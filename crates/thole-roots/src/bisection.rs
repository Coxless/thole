use crate::{Error, Options};

/// A root located by a bracketing method.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Root {
    /// The approximation of the root: the midpoint of the final bracket.
    pub x: f64,
    /// Lower end of the final bracket.
    pub lo: f64,
    /// Upper end of the final bracket.
    pub hi: f64,
    /// Number of bisection steps taken.
    pub iterations: usize,
}

/// Finds a root of `f` in `[a, b]` by bisection.
///
/// # Algorithm
///
/// The bracket starts as `[a, b]`. Each step evaluates `f` at the midpoint
/// and keeps the half over which `f` still changes sign, so the width halves
/// every step. The iteration stops when half the width of the bracket is at
/// most `options.tol.bound(midpoint)`, and returns the midpoint.
///
/// `f` is evaluated once at `a`, once at `b`, and once per step.
///
/// # Preconditions
///
/// - `a` and `b` are finite and `a <= b`.
/// - `f(a)` and `f(b)` do not have the same strict sign. Either may be zero.
/// - `f` is continuous on `[a, b]`. This cannot be checked. Without it the
///   result can be a point where `f` jumps across zero instead of a root
///   (for example the pole of `1 / x`).
///
/// # Guarantee
///
/// On success, some root `r` of `f` in `[a, b]` satisfies
/// `|x - r| <= options.tol.bound(x)`, up to the rounding error of evaluating
/// the midpoint. If `f` has several roots in `[a, b]`, which one is found is
/// unspecified.
///
/// # Errors
///
/// - [`Error::InvalidBracket`] if `a` or `b` is not finite, or `a > b`.
/// - [`Error::InvalidTolerance`] if a tolerance is negative or NaN.
/// - [`Error::NoSignChange`] if `f(a)` and `f(b)` have the same strict sign.
/// - [`Error::NanValue`] if `f` returns NaN.
/// - [`Error::MaxIterations`] if the tolerance is not reached within
///   `options.max_iter` steps. This always happens for a tolerance that is
///   smaller than the spacing of floating-point numbers around the root.
///
/// # Proofs
///
/// `lean/Thole/Roots/Bisection/Defs.lean` defines the same iteration over
/// any ordered field (`bisectStep`, `bisect`, `bisectMid`, `bisectDone`), and
/// `lean/Thole/Roots/Bisection.lean` proves, over the real numbers:
///
/// - `bisect_exists_root`: every bracket contains a root.
/// - `bisectMid_error_of_done`: the guarantee above.
/// - `bisectMid_error`: after `n` steps the error is at most
///   `(b - a) / 2 ^ (n + 1)`, which bounds the number of steps needed.
///
/// The proofs are about the Lean definitions, and do not cover
/// floating-point rounding. That this function follows the definitions is
/// tested: the oracle (`oracle/` in the repository) runs them with exact
/// rational arithmetic and checks the results of this function against them,
/// on polynomials drawn at random.
///
/// # Examples
///
/// ```
/// use thole_roots::{Options, bisect};
///
/// let root = bisect(|x| x * x - 2.0, 0.0, 2.0, &Options::default())?;
/// assert!((root.x - 2.0_f64.sqrt()).abs() < 1e-11);
/// # Ok::<(), thole_roots::Error>(())
/// ```
pub fn bisect(
    mut f: impl FnMut(f64) -> f64,
    a: f64,
    b: f64,
    options: &Options,
) -> Result<Root, Error> {
    if !(a.is_finite() && b.is_finite() && a <= b) {
        return Err(Error::InvalidBracket { a, b });
    }
    let tol = options.tol;
    if !tol.is_valid() {
        return Err(Error::InvalidTolerance {
            abs: tol.abs,
            rel: tol.rel,
        });
    }

    let mut eval = |x: f64| {
        let fx = f(x);
        if fx.is_nan() {
            Err(Error::NanValue { x })
        } else {
            Ok(fx)
        }
    };

    let (mut lo, mut hi) = (a, b);
    let mut f_lo = eval(lo)?;
    let f_hi = eval(hi)?;
    if !sign_change(f_lo, f_hi) {
        return Err(Error::NoSignChange { fa: f_lo, fb: f_hi });
    }

    let mut iterations = 0;
    loop {
        // `f64::midpoint` does not overflow, unlike `(lo + hi) / 2.0`.
        let mid = f64::midpoint(lo, hi);
        if (hi - lo) / 2.0 <= tol.bound(mid) {
            return Ok(Root {
                x: mid,
                lo,
                hi,
                iterations,
            });
        }
        if iterations == options.max_iter {
            return Err(Error::MaxIterations {
                max_iter: options.max_iter,
                lo,
                hi,
            });
        }

        // `bisectStep` in the Lean file.
        let f_mid = eval(mid)?;
        if sign_change(f_lo, f_mid) {
            hi = mid;
        } else {
            lo = mid;
            f_lo = f_mid;
        }
        iterations += 1;
    }
}

/// Whether `u` and `v` have opposite signs or one of them is zero.
///
/// Over the real numbers this is `u * v <= 0`, the form used in the Lean
/// definition `SignChange`, which the oracle evaluates exactly. The product is avoided here because it can
/// underflow to zero for two small values of the same sign.
fn sign_change(u: f64, v: f64) -> bool {
    u == 0.0 || v == 0.0 || (u < 0.0) != (v < 0.0)
}

#[cfg(test)]
mod tests {
    use super::sign_change;

    #[test]
    fn sign_change_matches_the_sign_of_the_product() {
        let values = [-2.0, -1e-300, -0.0, 0.0, 1e-300, 2.0, f64::INFINITY];
        for u in values {
            for v in values {
                let expected = match (u == 0.0, v == 0.0) {
                    (false, false) => (u < 0.0) != (v < 0.0),
                    _ => true,
                };
                assert_eq!(sign_change(u, v), expected, "u = {u}, v = {v}");
            }
        }
    }

    #[test]
    fn sign_change_does_not_underflow() {
        // The product of these underflows to 0, which would look like a sign change.
        assert_eq!(1e-200 * 1e-200, 0.0);
        assert!(!sign_change(1e-200, 1e-200));
    }
}
