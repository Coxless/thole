use crate::error::{check_interval, eval};
use crate::{Error, Options};

/// An integral computed by an adaptive method.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Integral {
    /// The estimate of the integral.
    pub value: f64,
    /// The estimate of its absolute error. It is not a bound.
    pub error: f64,
    /// The number of subintervals in the final partition of the interval.
    pub subintervals: usize,
    /// The number of evaluations of the function.
    pub evaluations: usize,
}

/// The nodes of the 15-point Kronrod rule on `[0, 1]`, largest first. The
/// odd-numbered ones (`XGK[1]`, `XGK[3]`, `XGK[5]`) and zero are the nodes of
/// the 7-point Gauss rule.
///
/// From QUADPACK (R. Piessens, E. de Doncker-Kapenga, C. W. Überhuber and
/// D. K. Kahaner, *QUADPACK: A Subroutine Package for Automatic Integration*,
/// Springer, 1983), routine `qk15`, rounded to the nearest `f64`.
// The digits are kept as QUADPACK publishes them.
#[allow(clippy::excessive_precision)]
const XGK: [f64; 8] = [
    0.991_455_371_120_812_639_206_854_697_526_329,
    0.949_107_912_342_758_524_526_189_684_047_851,
    0.864_864_423_359_769_072_789_712_788_640_926,
    0.741_531_185_599_394_439_863_864_773_280_788,
    0.586_087_235_467_691_130_294_144_845_693_013,
    0.405_845_151_377_397_166_906_606_412_076_961,
    0.207_784_955_007_898_467_600_689_403_773_245,
    0.0,
];

/// The weights of the 15-point Kronrod rule, for the nodes `±XGK[i]`.
// The digits are kept as QUADPACK publishes them.
#[allow(clippy::excessive_precision)]
const WGK: [f64; 8] = [
    0.022_935_322_010_529_224_963_732_008_058_970,
    0.063_092_092_629_978_553_290_700_663_189_204,
    0.104_790_010_322_250_183_839_876_322_541_518,
    0.140_653_259_715_525_918_745_189_590_510_238,
    0.169_004_726_639_267_902_826_583_426_598_550,
    0.190_350_578_064_785_409_913_256_402_421_014,
    0.204_432_940_075_298_892_414_161_999_234_649,
    0.209_482_141_084_727_828_012_999_174_891_714,
];

/// The weights of the 7-point Gauss rule, for the nodes `±XGK[2i + 1]`.
// The digits are kept as QUADPACK publishes them.
#[allow(clippy::excessive_precision)]
const WG: [f64; 4] = [
    0.129_484_966_168_869_693_270_611_432_679_082,
    0.279_705_391_489_276_667_901_467_771_423_780,
    0.381_830_050_505_118_944_950_369_775_488_975,
    0.417_959_183_673_469_387_755_102_040_816_327,
];

/// The nodes and weights of the 7-point Gauss and 15-point Kronrod rules
/// used by [`gauss_kronrod`], on `[-1, 1]`: `(nodes, kronrod_weights,
/// gauss_weights)`, the nodes in increasing order. The Gauss weight of a node
/// that belongs to the Kronrod rule only is zero.
///
/// The constants are those of QUADPACK's `qk15` rounded to `f64`. The oracle
/// (`oracle/` in the repository) checks that the Kronrod rule integrates
/// every polynomial of degree at most 22 and the Gauss rule every polynomial
/// of degree at most 13, up to the rounding of the constants.
pub fn gauss_kronrod_rule() -> ([f64; 15], [f64; 15], [f64; 15]) {
    let mut nodes = [0.0; 15];
    let mut kronrod = [0.0; 15];
    let mut gauss = [0.0; 15];
    for j in 0..8 {
        let g = if j % 2 == 1 { WG[j / 2] } else { 0.0 };
        for i in [j, 14 - j] {
            nodes[i] = if i < 7 { -XGK[j] } else { XGK[j] };
            kronrod[i] = WGK[j];
            gauss[i] = g;
        }
    }
    (nodes, kronrod, gauss)
}

/// A subinterval with the estimates of the integral over it.
///
/// `GkSegment` in the Lean file.
#[derive(Debug, Clone, Copy)]
struct Segment {
    a: f64,
    b: f64,
    value: f64,
    error: f64,
}

/// `gkSegment` in the Lean file: the 15-point Kronrod estimate of the
/// integral over `[a, b]`, with the difference from the 7-point Gauss
/// estimate as the error estimate.
fn segment(f: &mut impl FnMut(f64) -> f64, a: f64, b: f64) -> Result<Segment, Error> {
    let c = f64::midpoint(a, b);
    let h = b / 2.0 - a / 2.0;
    let fc = eval(f, c)?;
    let mut kronrod = WGK[7] * fc;
    let mut gauss = WG[3] * fc;
    for j in 0..7 {
        let dx = h * XGK[j];
        let sum = eval(f, c - dx)? + eval(f, c + dx)?;
        kronrod += WGK[j] * sum;
        if j % 2 == 1 {
            gauss += WG[j / 2] * sum;
        }
    }
    Ok(Segment {
        a,
        b,
        value: h * kronrod,
        error: (h * (kronrod - gauss)).abs(),
    })
}

/// Approximates `∫_a^b f(x) dx` by adaptive Gauss-Kronrod quadrature.
///
/// # Algorithm
///
/// Globally adaptive subdivision, as in QUADPACK's `qag` with the 15-point
/// rule, without its extrapolation and its heuristics for rounding errors.
///
/// On each subinterval the integral is estimated by the 15-point Kronrod
/// rule, and its error by the difference from the 7-point Gauss rule, whose
/// nodes are among those of the Kronrod rule. The estimates of the integral
/// and of the error over `[a, b]` are the sums over the subintervals, which
/// always partition `[a, b]`. While the error estimate exceeds
/// `options.tol.bound(value)`, the subinterval with the largest error
/// estimate (the first of them, from `a`, if there are several) is halved.
///
/// Each halving costs 30 evaluations of `f`, and the first estimate 15. The
/// sums are recomputed over all subintervals after each halving, in order
/// from `a`, so the cost of the bookkeeping grows with the square of the
/// number of subintervals. That is negligible for any sensible limit.
///
/// `a > b` is allowed and gives the negative of the integral over `[b, a]`.
///
/// # Guarantee
///
/// The 15-point Kronrod rule is exact, up to rounding, for polynomials of
/// degree at most 22, and the 7-point Gauss rule for degree at most 13. For
/// a smooth `f` the difference between the two is a pessimistic estimate of
/// the error of the Kronrod rule, but it is an estimate, not a bound: it can
/// be wrong for a function that the 15 nodes do not resolve, such as a narrow
/// peak between them.
///
/// On success, the returned error estimate is at most
/// `options.tol.bound(value)`.
///
/// # Errors
///
/// - [`Error::InvalidInterval`] if `a` or `b` is not finite.
/// - [`Error::InvalidTolerance`] if a tolerance is negative or NaN.
/// - [`Error::InvalidLimit`] if `options.max_subintervals` is zero.
/// - [`Error::NonFiniteValue`] if `f` returns NaN or an infinity.
/// - [`Error::MaxSubintervals`] if the tolerance is not reached with
///   `options.max_subintervals` subintervals. The error carries the last
///   estimates.
///
/// # Proofs
///
/// `lean/Thole/Quad/GaussKronrod/Defs.lean` defines the same iteration over
/// any ordered field (`gkSegment`, `gkStep`, `gk`, `gkDone`), and
/// `lean/Thole/Quad/GaussKronrod.lean` proves, over the real numbers:
///
/// - `gk_partition`: the subintervals always partition `[a, b]`, in order.
/// - `gk_error_le`: the error of the returned estimate is at most the sum of
///   the errors over the subintervals. So if the error estimate of every
///   subinterval bounds its error, the returned error estimate bounds the
///   error of the returned value.
///
/// That the error estimate of a subinterval bounds its error is not proved,
/// because it is not true in general. The exactness of the rules for
/// polynomials is tested, not proved: the constants are rational
/// approximations of irrational numbers. The oracle (`oracle/` in the
/// repository) checks it, and requires this function to return what the
/// operations below give in a model of `f64` arithmetic, bit for bit, on
/// polynomials drawn at random.
///
/// # Examples
///
/// ```
/// use thole_quad::{Options, gauss_kronrod};
///
/// let integral = gauss_kronrod(f64::exp, 0.0, 1.0, &Options::default())?;
/// assert!((integral.value - (1.0_f64.exp() - 1.0)).abs() < 1e-14);
/// assert_eq!(integral.evaluations, 15);
/// # Ok::<(), thole_quad::Error>(())
/// ```
pub fn gauss_kronrod(
    mut f: impl FnMut(f64) -> f64,
    a: f64,
    b: f64,
    options: &Options,
) -> Result<Integral, Error> {
    check_interval(a, b)?;
    let tol = options.tol;
    if !tol.is_valid() {
        return Err(Error::InvalidTolerance {
            abs: tol.abs,
            rel: tol.rel,
        });
    }
    if options.max_subintervals == 0 {
        return Err(Error::InvalidLimit {
            max_subintervals: 0,
        });
    }

    let mut segments = vec![segment(&mut f, a, b)?];
    loop {
        // `gkValue` and `gkError` in the Lean file.
        let mut value = 0.0;
        let mut error = 0.0;
        for s in &segments {
            value += s.value;
            error += s.error;
        }
        // `gkDone`.
        if error <= tol.bound(value) {
            return Ok(Integral {
                value,
                error,
                subintervals: segments.len(),
                evaluations: 15 * (2 * segments.len() - 1),
            });
        }
        if segments.len() >= options.max_subintervals {
            return Err(Error::MaxSubintervals {
                max_subintervals: options.max_subintervals,
                value,
                error,
            });
        }

        // `gkStep`: halve the first subinterval with the largest error.
        let mut worst = 0;
        for (i, s) in segments.iter().enumerate() {
            if s.error > segments[worst].error {
                worst = i;
            }
        }
        let Segment { a, b, .. } = segments[worst];
        let mid = f64::midpoint(a, b);
        let left = segment(&mut f, a, mid)?;
        let right = segment(&mut f, mid, b)?;
        segments[worst] = left;
        segments.insert(worst + 1, right);
    }
}
