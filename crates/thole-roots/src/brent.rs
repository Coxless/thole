use crate::bracket::{check_arguments, eval, sign_change};
use crate::{Error, Options, Root};

/// Finds a root of `f` in `[a, b]` by Brent's method.
///
/// # Algorithm
///
/// The procedure `zero` of R. P. Brent, *Algorithms for Minimization without
/// Derivatives* (Prentice-Hall, 1973), chapter 4.
///
/// Three points are kept: the best approximation so far, a point where `f`
/// has the opposite sign, so that a root lies between the two, and the
/// previous approximation. Each step proposes a new approximation by
/// interpolation: the secant through two of the points, or inverse quadratic
/// interpolation through all three when they are distinct. The proposal is
/// taken only if it falls inside the bracket and is less than half as long as
/// the step before last. Otherwise the step is a bisection. Every step moves
/// the approximation by at least half the tolerance.
///
/// The iteration stops when `f` is zero at the approximation, or when half
/// the distance to the point of opposite sign is at most
/// `options.tol.bound(x) / 2`. It returns the approximation as [`Root::x`];
/// the final bracket has `x` at one end.
///
/// `f` is evaluated once at `a`, once at `b`, and once per step.
///
/// For a smooth function with a simple root this takes far fewer steps than
/// [`bisect`](crate::bisect). In the worst case it takes more, but never more
/// than about the square of the number of bisection steps (Brent, section 3
/// of chapter 4).
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
/// `|x - r| <= options.tol.bound(x)`, up to the rounding error of the
/// subtraction in the stopping test. If `f` has several roots in `[a, b]`,
/// which one is found is unspecified.
///
/// # Errors
///
/// - [`Error::InvalidBracket`] if `a` or `b` is not finite, or `a > b`.
/// - [`Error::InvalidTolerance`] if a tolerance is negative or NaN.
/// - [`Error::NoSignChange`] if `f(a)` and `f(b)` have the same strict sign.
/// - [`Error::NanValue`] if `f` returns NaN.
/// - [`Error::MaxIterations`] if the tolerance is not reached within
///   `options.max_iter` steps. This always happens for a tolerance that is
///   smaller than the spacing of floating-point numbers around the root,
///   unless `f` is exactly zero at an approximation.
///
/// # Proofs
///
/// `lean/Thole/Roots/Brent/Defs.lean` defines the same iteration over any
/// ordered field (`brentStep`, `brent`, `brentDone` and the definitions they
/// are built from), and `lean/Thole/Roots/Brent.lean` proves, over the real
/// numbers:
///
/// - `brent_exists_root`: a root always lies between the approximation and
///   the point of opposite sign.
/// - `brent_error_of_done`: the guarantee above.
/// - `brent_done_of_le`: with a tolerance of at least `t` everywhere, the
///   iteration stops after at most `2 * (b - a) / t` steps.
///
/// Brent's bound on the number of steps and the superlinear convergence for
/// smooth `f` are not proved; the Lean file says why.
///
/// The proofs are about the Lean definitions, and do not cover
/// floating-point rounding.
///
/// # Examples
///
/// ```
/// use thole_roots::{Options, brent};
///
/// let root = brent(|x| x * x - 2.0, 0.0, 2.0, &Options::default())?;
/// assert!((root.x - 2.0_f64.sqrt()).abs() < 1e-11);
/// # Ok::<(), thole_roots::Error>(())
/// ```
pub fn brent(
    mut f: impl FnMut(f64) -> f64,
    a: f64,
    b: f64,
    options: &Options,
) -> Result<Root, Error> {
    check_arguments(a, b, options)?;
    let mut eval = |x: f64| eval(&mut f, x);

    let fa = eval(a)?;
    let fb = eval(b)?;
    if !sign_change(fa, fb) {
        return Err(Error::NoSignChange { fa, fb });
    }

    // `brentInit` in the Lean file.
    let mut s = State {
        prev: a,
        f_prev: fa,
        cur: b,
        f_cur: fb,
        contra: a,
        f_contra: fa,
        d: b - a,
        e: b - a,
    };
    s.order();

    let mut iterations = 0;
    loop {
        // The tolerance `tol s.cur` of the Lean file: half the tolerance of
        // the caller, so that the error is at most the tolerance itself.
        let tol = options.tol.bound(s.cur) / 2.0;
        let half = s.half();

        // `brentDone`.
        if s.f_cur == 0.0 || half.abs() <= tol {
            return Ok(Root {
                x: s.cur,
                lo: s.cur.min(s.contra),
                hi: s.cur.max(s.contra),
                iterations,
            });
        }
        if iterations == options.max_iter {
            return Err(Error::MaxIterations {
                max_iter: options.max_iter,
                lo: s.cur.min(s.contra),
                hi: s.cur.max(s.contra),
            });
        }

        // `brentStep`.
        let (d, e) = s.trial(tol, half);
        let next = s.cur + shift(tol, half, d);
        let f_next = eval(next)?;
        s = if sign_change(f_next, s.f_contra) {
            State {
                prev: s.cur,
                f_prev: s.f_cur,
                cur: next,
                f_cur: f_next,
                d,
                e,
                ..s
            }
        } else {
            let step = next - s.cur;
            State {
                prev: s.cur,
                f_prev: s.f_cur,
                cur: next,
                f_cur: f_next,
                contra: s.cur,
                f_contra: s.f_cur,
                d: step,
                e: step,
            }
        };
        s.order();
        iterations += 1;
    }
}

/// `BrentState` in the Lean file, with the value of `f` at each point.
#[derive(Clone, Copy)]
struct State {
    /// The previous value of `cur`.
    prev: f64,
    f_prev: f64,
    /// The best approximation of the root so far.
    cur: f64,
    f_cur: f64,
    /// A point where `f` has the opposite sign to `f_cur`.
    contra: f64,
    f_contra: f64,
    /// The last step proposed.
    d: f64,
    /// The step proposed before `d`.
    e: f64,
}

impl State {
    /// `BrentState.half`: the bisection step.
    ///
    /// Each point is halved before the subtraction, because
    /// `(contra - cur) / 2.0` overflows for a bracket wider than `f64::MAX`.
    fn half(&self) -> f64 {
        self.contra / 2.0 - self.cur / 2.0
    }

    /// `brentOrder`: makes `cur` the end of the bracket with the smaller `|f|`.
    fn order(&mut self) {
        if self.f_contra.abs() < self.f_cur.abs() {
            (self.prev, self.f_prev) = (self.cur, self.f_cur);
            (self.cur, self.f_cur) = (self.contra, self.f_contra);
            (self.contra, self.f_contra) = (self.prev, self.f_prev);
        }
    }

    /// `brentInterp`: `p` and `q` of the interpolation step, which is
    /// `-p / q`. The secant through `prev` and `cur` when `prev == contra`,
    /// inverse quadratic interpolation through the three points otherwise.
    fn interp(&self, half: f64) -> (f64, f64) {
        let s = self.f_cur / self.f_prev;
        if self.prev == self.contra {
            (2.0 * half * s, 1.0 - s)
        } else {
            let q = self.f_prev / self.f_contra;
            let r = self.f_cur / self.f_contra;
            (
                s * (2.0 * half * q * (q - r) - (self.cur - self.prev) * (r - 1.0)),
                (q - 1.0) * (r - 1.0) * (s - 1.0),
            )
        }
    }

    /// `brentTrial`: the new values of `d` and `e`, for the tolerance `tol`
    /// and the bisection step `half`.
    fn trial(&self, tol: f64, half: f64) -> (f64, f64) {
        if self.e.abs() < tol || self.f_prev.abs() <= self.f_cur.abs() {
            return (half, half);
        }
        let (p, q) = self.interp(half);
        // `brentP` and `brentQ`.
        let q = if p > 0.0 { -q } else { q };
        let p = p.abs();
        // Every comparison is false for a NaN, which infinite values of `f`
        // can produce, so the step is then a bisection. The same happens
        // while the bracket is wider than `f64::MAX`, where `2.0 * half`
        // overflows. A step that is taken is therefore shorter than
        // `0.75 * f64::MAX`, and the quotient does not overflow.
        if 2.0 * p < 3.0 * half * q - (tol * q).abs() && p < (self.e * q / 2.0).abs() {
            (p / q, self.d)
        } else {
            (half, half)
        }
    }
}

/// `brentShift`: the step actually taken for a proposed step `d`. `d` itself
/// if it is longer than the tolerance `tol`, otherwise `tol` in the direction
/// `half` of `contra`.
fn shift(tol: f64, half: f64, d: f64) -> f64 {
    if tol < d.abs() {
        d
    } else if half > 0.0 {
        tol
    } else {
        -tol
    }
}

#[cfg(test)]
mod tests {
    use super::shift;

    #[test]
    fn shift_is_at_least_the_tolerance_long() {
        // (tol, half, d, expected)
        let cases = [
            (0.5, 1.0, 2.0, 2.0),
            (0.5, 1.0, -2.0, -2.0),
            (0.5, 1.0, 0.25, 0.5),
            (0.5, -1.0, 0.25, -0.5),
            // Equal to the tolerance: not longer, so the direction is that of `half`.
            (0.5, -1.0, 0.5, -0.5),
            (0.0, 1.0, 0.0, 0.0),
        ];
        for (tol, half, d, expected) in cases {
            assert_eq!(shift(tol, half, d), expected, "({tol}, {half}, {d})");
        }
    }
}
