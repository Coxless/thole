/-
Brent's method for root finding: the executable specification.

Rust counterpart: `thole_roots::brent` in `../../../../src/brent.rs`.

The algorithm is the procedure `zero` of R. P. Brent, "Algorithms for
Minimization without Derivatives" (Prentice-Hall, 1973), chapter 4. It keeps
three points: `cur`, the best approximation so far; `contra`, a point where
`f` has the opposite sign, so that a root lies between the two; and `prev`,
the previous value of `cur`. Each step moves `cur` by an interpolation step
when that step is acceptable and by a bisection step otherwise.

| Lean           | Rust                                                       |
|----------------|------------------------------------------------------------|
| `BrentState`   | the variables of the loop in `brent`                       |
| `brentOrder`   | the swap that makes `cur` the point with the smaller `|f|` |
| `brentDone`    | the stopping test                                          |
| `brentInterp`  | `p` and `q` of the secant / inverse quadratic step         |
| `brentP/Q`     | `p` and `q` after the sign normalization                   |
| `brentTrial`   | the choice between interpolation and bisection (`d`, `e`)  |
| `brentShift`   | the step actually taken, at least `tol` long               |
| `brentStep`    | the body of the loop in `brent`                            |
| `brent`        | the state after `iterations` steps                         |

`tol` is the tolerance as a function of `cur`. The Rust code passes half the
tolerance of the caller, so that `brent_error_of_done` gives an error of at
most the tolerance itself.

Like bisection (`../Bisection/Defs.lean`), the definitions are written over
any linearly ordered field: `../Brent.lean` proves their properties over `ℝ`,
and they run with exact arithmetic over `ℚ`.
-/
import Thole.Roots.Bisection.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs

namespace Thole.Roots

/-- The variables of Brent's method. -/
structure BrentState (α : Type*) where
  /-- The previous value of `cur`. -/
  prev : α
  /-- The best approximation of the root so far. -/
  cur : α
  /-- A point where `f` has the opposite sign to `f cur`. -/
  contra : α
  /-- The last step proposed. -/
  d : α
  /-- The step proposed before `d`. -/
  e : α

variable {α : Type*} [Field α] [LinearOrder α]

/-- Half the signed distance from `cur` to `contra`: the bisection step. -/
def BrentState.half (s : BrentState α) : α :=
  (s.contra - s.cur) / 2

/-- Makes `cur` the end of the bracket with the smaller `|f|`. -/
def brentOrder (f : α → α) (s : BrentState α) : BrentState α :=
  if |f s.contra| < |f s.cur| then
    { s with prev := s.cur, cur := s.contra, contra := s.cur }
  else s

/-- The state before the first step, for the bracket `[a, b]`. -/
def brentInit (f : α → α) (a b : α) : BrentState α :=
  brentOrder f ⟨a, b, a, b - a, b - a⟩

/-- The stopping test: `cur` is a root, or the bracket is short enough. -/
def brentDone (f : α → α) (tol : α → α) (s : BrentState α) : Prop :=
  f s.cur = 0 ∨ |s.half| ≤ tol s.cur

instance (f : α → α) (tol : α → α) (s : BrentState α) :
    Decidable (brentDone f tol s) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- Numerator and denominator of the interpolation step, before the sign
normalization: the secant through `prev` and `cur` when `prev = contra`,
inverse quadratic interpolation through the three points otherwise. The
proposed step from `cur` is `-p / q`. -/
def brentInterp (f : α → α) (s : BrentState α) : α × α :=
  if s.prev = s.contra then
    (2 * s.half * (f s.cur / f s.prev), 1 - f s.cur / f s.prev)
  else
    (f s.cur / f s.prev *
        (2 * s.half * (f s.prev / f s.contra) *
            (f s.prev / f s.contra - f s.cur / f s.contra) -
          (s.cur - s.prev) * (f s.cur / f s.contra - 1)),
      (f s.prev / f s.contra - 1) * (f s.cur / f s.contra - 1) * (f s.cur / f s.prev - 1))

/-- The numerator of the interpolation step, made non-negative. -/
def brentP (f : α → α) (s : BrentState α) : α :=
  |(brentInterp f s).1|

/-- The denominator of the interpolation step, with the sign that makes
`brentP / brentQ` the proposed step. -/
def brentQ (f : α → α) (s : BrentState α) : α :=
  if 0 < (brentInterp f s).1 then -(brentInterp f s).2 else (brentInterp f s).2

/-- The new values of `d` and `e`. The interpolation step is taken when it
ends inside the bracket, not too close to `contra`, and is less than half as
long as the step before last. Otherwise the step is a bisection. -/
def brentTrial (f : α → α) (tol : α → α) (s : BrentState α) : α × α :=
  if |s.e| < tol s.cur ∨ |f s.prev| ≤ |f s.cur| then (s.half, s.half)
  else if 2 * brentP f s < 3 * s.half * brentQ f s - |tol s.cur * brentQ f s| ∧
      brentP f s < |s.e * brentQ f s / 2| then
    (brentP f s / brentQ f s, s.d)
  else (s.half, s.half)

/-- The step actually taken for a proposed step `d`: `d` itself if it is
longer than the tolerance `τ`, otherwise `τ` in the direction `m` of `contra`. -/
def brentShift (τ m d : α) : α :=
  if τ < |d| then d else if 0 < m then τ else -τ

/-- The next value of `cur`, before the reordering. -/
def brentNext (f : α → α) (tol : α → α) (s : BrentState α) : α :=
  s.cur + brentShift (tol s.cur) s.half (brentTrial f tol s).1

/-- One step of Brent's method. A state that passes the stopping test is left
unchanged. Otherwise `cur` moves to `brentNext`, and `contra` is kept if `f`
still changes sign between the two, or replaced by the old `cur` if not. -/
def brentStep (f : α → α) (tol : α → α) (s : BrentState α) : BrentState α :=
  if brentDone f tol s then s
  else
    brentOrder f
      (if f (brentNext f tol s) * f s.contra ≤ 0 then
        ⟨s.cur, brentNext f tol s, s.contra, (brentTrial f tol s).1, (brentTrial f tol s).2⟩
      else
        ⟨s.cur, brentNext f tol s, s.cur, brentNext f tol s - s.cur, brentNext f tol s - s.cur⟩)

/-- The state after `n` steps starting from the bracket `[a, b]`. -/
def brent (f : α → α) (tol : α → α) (a b : α) (n : ℕ) : BrentState α :=
  (brentStep f tol)^[n] (brentInit f a b)

end Thole.Roots
