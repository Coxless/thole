use crate::{Error, Options};

/// A root located by Newton's method.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct NewtonRoot {
    /// The approximation of the root.
    pub x: f64,
    /// The last step taken: `x` is the previous approximation minus `step`.
    /// Zero if no step was taken.
    pub step: f64,
    /// Number of steps taken.
    pub iterations: usize,
}

/// Finds a root of `f` near `x0` by Newton's method, given the derivative
/// `df` of `f`.
///
/// # Algorithm
///
/// Starting from `x0`, each step replaces the approximation `x` by
/// `x - f(x) / df(x)`: the root of the tangent to `f` at `x`. The iteration
/// stops when `f` is zero at the approximation, or when the step that led to
/// it is at most `options.tol.bound(x)` long. It returns the approximation
/// as [`NewtonRoot::x`].
///
/// `f` and `df` are each evaluated once per step, and `f` once more at `x0`.
/// After a step that passes the stopping test, neither is evaluated again.
///
/// Near a simple root of a smooth function the number of correct digits
/// roughly doubles with every step. Far from a root, or at a multiple root,
/// nothing of the sort holds: the iteration can converge slowly, cycle, or
/// run away. Use [`brent`](crate::brent) when a bracket is known.
///
/// # Preconditions
///
/// - `x0` is finite.
/// - `df` is the derivative of `f`. This cannot be checked. With a wrong
///   derivative the iteration may still converge, to a root, but slowly.
///
/// # Guarantee
///
/// Newton's method has no unconditional guarantee: a short step does not by
/// itself mean that a root is near. When a short step is taken close enough
/// to a simple root, it does. On success, if `df` is Lipschitz continuous
/// with constant `L` and at least `m > 0` in absolute value on the interval
/// of half-width `|step|` around `x`, and `L * |step| <= m`, then some root
/// `r` of `f` in that interval satisfies
/// `|x - r| <= L * step^2 / m <= options.tol.bound(x)`, up to the rounding
/// error of evaluating `f` and `df`.
///
/// # Errors
///
/// - [`Error::InvalidStart`] if `x0` is not finite.
/// - [`Error::InvalidTolerance`] if a tolerance is negative or NaN.
/// - [`Error::NanValue`] if `f` returns NaN, [`Error::NanDerivative`] if
///   `df` does.
/// - [`Error::ZeroDerivative`] if `df` is zero at an approximation at which
///   `f` is not.
/// - [`Error::NonFiniteStep`] if `df` is infinite at an approximation, or
///   the next approximation is not finite (because `f` is infinite, or `df`
///   is tiny).
/// - [`Error::NotConverged`] if the tolerance is not reached within
///   `options.max_iter` steps.
///
/// # Proofs
///
/// `lean/Thole/Roots/Newton/Defs.lean` defines the same iteration over any
/// ordered field (`newtonStep`, `newton`, `newtonDone`), and
/// `lean/Thole/Roots/Newton.lean` proves, over the real numbers, for a
/// function with a Lipschitz continuous derivative:
///
/// - `newtonStep_error`: one step squares the error, up to the factor
///   `L / |df(x)|` (quadratic convergence).
/// - `newton_error`: from a starting point close enough to a simple root,
///   the error after `n` steps is at most `|x0 - r| / 2^n`.
/// - `newtonStep_exists_root` and `newton_error_of_done`: the guarantee
///   above.
///
/// The proofs are about the Lean definitions, and do not cover
/// floating-point rounding. That this function follows the definitions is
/// tested: the oracle (`oracle/` in the repository) runs them in a model of
/// `f64` arithmetic and requires the results of this function to be the
/// same, bit for bit, on polynomials drawn at random. The order of the
/// operations below is therefore part of what is tested.
///
/// # Examples
///
/// ```
/// use thole_roots::{Options, newton};
///
/// let root = newton(|x| x * x - 2.0, |x| 2.0 * x, 1.0, &Options::default())?;
/// assert!((root.x - 2.0_f64.sqrt()).abs() < 1e-11);
/// # Ok::<(), thole_roots::Error>(())
/// ```
pub fn newton(
    mut f: impl FnMut(f64) -> f64,
    mut df: impl FnMut(f64) -> f64,
    x0: f64,
    options: &Options,
) -> Result<NewtonRoot, Error> {
    if !x0.is_finite() {
        return Err(Error::InvalidStart { x0 });
    }
    let tol = options.tol;
    if !tol.is_valid() {
        return Err(Error::InvalidTolerance {
            abs: tol.abs,
            rel: tol.rel,
        });
    }

    let mut x = x0;
    let mut step = 0.0;
    let mut iterations = 0;
    loop {
        let fx = f(x);
        if fx.is_nan() {
            return Err(Error::NanValue { x });
        }
        // `newtonDone`, first half: `x` is a root.
        if fx == 0.0 {
            return Ok(NewtonRoot {
                x,
                step,
                iterations,
            });
        }
        if iterations == options.max_iter {
            return Err(Error::NotConverged {
                max_iter: options.max_iter,
                x,
            });
        }

        // `newtonStep` in the Lean file.
        let dfx = df(x);
        if dfx.is_nan() {
            return Err(Error::NanDerivative { x });
        }
        if dfx == 0.0 {
            return Err(Error::ZeroDerivative { x });
        }
        step = fx / dfx;
        let next = x - step;
        // An infinite derivative gives a zero step, which would pass the
        // stopping test without saying anything about a root.
        if dfx.is_infinite() || !next.is_finite() {
            return Err(Error::NonFiniteStep { x });
        }
        x = next;
        iterations += 1;

        // `newtonDone`, second half: the step was short enough.
        if step.abs() <= tol.bound(x) {
            return Ok(NewtonRoot {
                x,
                step,
                iterations,
            });
        }
    }
}
