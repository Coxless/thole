use std::f64::consts::PI;

use crate::Error;
use crate::error::{check_interval, eval};
use crate::interval::center_and_half;

/// The `n`-point Gauss-Legendre rule: its nodes and weights on `[-1, 1]`.
///
/// The rule approximates `∫_{-1}^{1} f(x) dx` by `Σ w_i f(x_i)`, and is
/// exact for polynomials of degree at most `2n - 1`. On `[a, b]` it is
/// applied through the affine map from `[-1, 1]` (see [`integrate`]).
///
/// The nodes are the roots of the Legendre polynomial `P_n`, and the weights
/// are `w_i = 2 / ((1 - x_i^2) P_n'(x_i)^2)`. Both are computed here, not
/// read from a table.
///
/// [`integrate`]: GaussLegendre::integrate
#[derive(Debug, Clone, PartialEq)]
pub struct GaussLegendre {
    nodes: Vec<f64>,
    weights: Vec<f64>,
}

/// The largest number of Newton steps taken for one node. Two to five are
/// enough from the initial guesses below; this only bounds the loop.
const MAX_NEWTON_STEPS: usize = 100;

/// A Newton step at most this long ends the iteration for a node. The error
/// of the node is then of the order of the square of this, far below the
/// spacing of floating-point numbers.
const NEWTON_TOL: f64 = 1e-14;

impl GaussLegendre {
    /// Computes the `n`-point rule.
    ///
    /// # Algorithm
    ///
    /// The positive roots of `P_n` are found one by one by Newton's method,
    /// from the initial guesses `cos(π (i + 3/4) / (n + 1/2))` (Abramowitz
    /// and Stegun 22.16.6). `P_n` and its derivative are evaluated by the
    /// three-term recurrence `(k + 1) P_{k+1} = (2k + 1) x P_k - k P_{k-1}`
    /// and `P_n' = n (x P_n - P_{n-1}) / (x^2 - 1)`. The iteration for a
    /// node stops after a step of at most `1e-14`. The negative roots follow
    /// by symmetry, and zero is a root when `n` is odd.
    ///
    /// The cosine of the initial guesses is a Taylor polynomial evaluated
    /// with `+`, `-`, `*` and `/` only, so that every operation here is
    /// correctly rounded and the oracle can repeat them exactly.
    ///
    /// The cost is of the order of `n^2` operations.
    ///
    /// # Errors
    ///
    /// [`Error::InvalidOrder`] if `n` is zero.
    ///
    /// # Proofs
    ///
    /// `lean/Thole/Quad/GaussLegendre/Defs.lean` defines the recurrence
    /// (`legendre`), the weight (`gaussWeight`) and the rule (`rule`) over
    /// any ordered field, and `lean/Thole/Quad/GaussLegendre.lean` proves,
    /// over the real numbers:
    ///
    /// - `gauss_exact`: a rule whose nodes are the roots of a polynomial of
    ///   degree `n` orthogonal to all polynomials of lower degree, and which
    ///   is exact for degree below `n`, is exact for degree below `2n`.
    /// - `rule_exact_of_exact`: a rule exact on `[-1, 1]` is exact on any
    ///   interval through the affine map.
    /// - `legendre_one` and `legendre_neg`: `P_n(1) = 1` and
    ///   `P_n(-x) = (-1)^n P_n(x)`, the symmetry used for the negative nodes.
    ///
    /// That the Legendre polynomials are orthogonal, and that these weights
    /// make the rule exact for degree below `n`, are classical and not
    /// proved; the Lean file says why. That the computed nodes are within a
    /// few units in the last place of the roots of `P_n` is tested: the
    /// oracle (`oracle/` in the repository) evaluates `P_n` exactly and
    /// requires a sign change around every node. It also requires this
    /// function to return the nodes and weights that the operations below
    /// give in a model of `f64` arithmetic, bit for bit.
    ///
    /// # Examples
    ///
    /// ```
    /// use thole_quad::GaussLegendre;
    ///
    /// let rule = GaussLegendre::new(2)?;
    /// let node = 1.0 / 3.0_f64.sqrt();
    /// assert!((rule.nodes()[1] - node).abs() < 1e-15);
    /// assert!(rule.weights().iter().all(|w| (w - 1.0).abs() < 1e-15));
    /// # Ok::<(), thole_quad::Error>(())
    /// ```
    pub fn new(n: usize) -> Result<Self, Error> {
        if n == 0 {
            return Err(Error::InvalidOrder { n });
        }
        let mut nodes = vec![0.0; n];
        let mut weights = vec![0.0; n];
        let nf = n as f64;
        for i in 0..n / 2 {
            // The `i`-th largest root.
            let mut x = cos(PI * (i as f64 + 0.75) / (nf + 0.5));
            for _ in 0..MAX_NEWTON_STEPS {
                let (p, dp) = legendre(n, x);
                let dx = p / dp;
                x -= dx;
                if dx.abs() <= NEWTON_TOL {
                    break;
                }
            }
            let w = weight(n, x);
            nodes[i] = -x;
            nodes[n - 1 - i] = x;
            weights[i] = w;
            weights[n - 1 - i] = w;
        }
        if n % 2 == 1 {
            nodes[n / 2] = 0.0;
            weights[n / 2] = weight(n, 0.0);
        }
        Ok(Self { nodes, weights })
    }

    /// The number of nodes.
    pub fn order(&self) -> usize {
        self.nodes.len()
    }

    /// The nodes on `[-1, 1]`, in increasing order.
    pub fn nodes(&self) -> &[f64] {
        &self.nodes
    }

    /// The weights, in the order of the nodes.
    pub fn weights(&self) -> &[f64] {
        &self.weights
    }

    /// Approximates `∫_a^b f(x) dx` by the rule.
    ///
    /// With `c` the midpoint of `[a, b]` and `h = (b - a) / 2`, this is
    /// `h Σ w_i f(c + h x_i)`, summed in the order of the nodes. `a > b` is
    /// allowed and gives the negative of the integral over `[b, a]`.
    ///
    /// # Guarantee
    ///
    /// Exact, up to rounding, when `f` is a polynomial of degree at most
    /// `2n - 1`. Otherwise there is no error estimate: compare with a rule
    /// of higher order, or use [`gauss_kronrod`](crate::gauss_kronrod).
    ///
    /// # Errors
    ///
    /// - [`Error::InvalidInterval`] if `a` or `b` is not finite.
    /// - [`Error::NonFiniteValue`] if `f` returns NaN or an infinity.
    pub fn integrate(&self, mut f: impl FnMut(f64) -> f64, a: f64, b: f64) -> Result<f64, Error> {
        check_interval(a, b)?;
        let (c, h) = center_and_half(a, b);
        let mut sum = 0.0;
        for (&x, &w) in self.nodes.iter().zip(&self.weights) {
            sum += w * eval(&mut f, c + h * x)?;
        }
        Ok(h * sum)
    }
}

/// Approximates `∫_a^b f(x) dx` by the `n`-point Gauss-Legendre rule.
///
/// The same as `GaussLegendre::new(n)?.integrate(f, a, b)`; see
/// [`GaussLegendre`]. To integrate several functions with the same `n`,
/// compute the rule once instead.
///
/// # Errors
///
/// - [`Error::InvalidOrder`] if `n` is zero.
/// - [`Error::InvalidInterval`] if `a` or `b` is not finite.
/// - [`Error::NonFiniteValue`] if `f` returns NaN or an infinity.
///
/// # Examples
///
/// ```
/// use thole_quad::gauss_legendre;
///
/// // Exact for a polynomial of degree 2n - 1 = 5.
/// let integral = gauss_legendre(|x| x.powi(5) + x * x, 0.0, 1.0, 3)?;
/// assert!((integral - (1.0 / 6.0 + 1.0 / 3.0)).abs() < 1e-15);
/// # Ok::<(), thole_quad::Error>(())
/// ```
pub fn gauss_legendre(f: impl FnMut(f64) -> f64, a: f64, b: f64, n: usize) -> Result<f64, Error> {
    GaussLegendre::new(n)?.integrate(f, a, b)
}

/// `legendre` in the Lean file: `(P_n(x), P_n'(x))` for `n >= 1` and
/// `|x| != 1`, by the three-term recurrence.
fn legendre(n: usize, x: f64) -> (f64, f64) {
    let (mut p0, mut p1) = (1.0, x);
    for k in 1..n {
        let k = k as f64;
        let p2 = ((2.0 * k + 1.0) * x * p1 - k * p0) / (k + 1.0);
        p0 = p1;
        p1 = p2;
    }
    (p1, n as f64 * (x * p1 - p0) / (x * x - 1.0))
}

/// `gaussWeight` in the Lean file: `2 / ((1 - x^2) P_n'(x)^2)`.
fn weight(n: usize, x: f64) -> f64 {
    let (_, dp) = legendre(n, x);
    2.0 / ((1.0 - x * x) * dp * dp)
}

/// `cos t` for `0 <= t <= π / 2`, by its Taylor polynomial of degree 24.
///
/// The first omitted term is below `(π / 2)^26 / 26! < 1e-21`. The value
/// is only an initial guess for Newton's method, so it need not be correctly
/// rounded; what matters is that it is computed by operations that the
/// oracle can repeat.
fn cos(t: f64) -> f64 {
    let t2 = t * t;
    let mut term = 1.0;
    let mut sum = 1.0;
    for k in 1..=12 {
        let k = k as f64;
        term = -term * t2 / ((2.0 * k - 1.0) * (2.0 * k));
        sum += term;
    }
    sum
}

#[cfg(test)]
mod tests {
    use super::{cos, legendre};

    #[test]
    fn cos_is_accurate_on_the_first_quadrant() {
        for i in 0..=100 {
            let t = std::f64::consts::FRAC_PI_2 * f64::from(i) / 100.0;
            assert!((cos(t) - t.cos()).abs() <= 4.0 * f64::EPSILON, "t = {t}");
        }
    }

    #[test]
    fn legendre_matches_closed_forms() {
        let x: f64 = 0.3;
        let (p, dp) = legendre(2, x);
        assert!((p - (3.0 * x * x - 1.0) / 2.0).abs() < 1e-15);
        assert!((dp - 3.0 * x).abs() < 1e-15);
        let (p, dp) = legendre(3, x);
        assert!((p - (5.0 * x.powi(3) - 3.0 * x) / 2.0).abs() < 1e-15);
        assert!((dp - (15.0 * x * x - 3.0) / 2.0).abs() < 1e-15);
        assert_eq!(legendre(1, x), (x, 1.0));
    }
}
