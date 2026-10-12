/-
The bisection method for root finding: the executable specification.

Rust counterpart: `thole_roots::bisect` in `../../../../src/bisection.rs`.

| Lean          | Rust                                             |
|---------------|--------------------------------------------------|
| `SignChange`  | `sign_change` (sign comparison, not a product)   |
| `bisectStep`  | the body of the loop in `bisect`                 |
| `bisect`      | the bracket `(lo, hi)` after `iterations` steps  |
| `bisectMid`   | the returned `Root::x`                           |
| `bisectDone`  | the stopping test                                |

The definitions are written once, over any linearly ordered field `α`, and
used twice:

- over `ℝ`, where `../Bisection.lean` proves their properties;
- over `ℚ`, where they run with exact arithmetic. The oracle
  (`oracle/lean/Thole/Oracle/Roots.lean`) compares the results of the Rust code
  with them.

This file imports only what the definitions need, because everything it
imports is linked into the oracle executable.
-/
import Mathlib.Algebra.Field.Defs
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Logic.Function.Iterate

namespace Thole.Roots

variable {α : Type*} [Field α] [LinearOrder α]

/-- `f` takes values of opposite (weak) sign at `a` and `b`.

This is the precondition of bisection. It allows `f a = 0` or `f b = 0`. -/
def SignChange (f : α → α) (a b : α) : Prop :=
  f a * f b ≤ 0

instance (f : α → α) (a b : α) : Decidable (SignChange f a b) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- One bisection step on the bracket `p = (lo, hi)`: evaluate `f` at the
midpoint and keep the half on which the sign change is known to persist. -/
def bisectStep (f : α → α) (p : α × α) : α × α :=
  if f p.1 * f ((p.1 + p.2) / 2) ≤ 0 then (p.1, (p.1 + p.2) / 2) else ((p.1 + p.2) / 2, p.2)

/-- The bracket after `n` bisection steps starting from `(a, b)`. -/
def bisect (f : α → α) (a b : α) (n : ℕ) : α × α :=
  (bisectStep f)^[n] (a, b)

/-- The approximation returned after `n` steps: the midpoint of the bracket. -/
def bisectMid (f : α → α) (a b : α) (n : ℕ) : α :=
  ((bisect f a b n).1 + (bisect f a b n).2) / 2

/-- The stopping test after `n` steps: half the width of the bracket is at
most the tolerance at the midpoint. `tol` is the tolerance as a function of
the approximation. -/
def bisectDone (f : α → α) (tol : α → α) (a b : α) (n : ℕ) : Prop :=
  ((bisect f a b n).2 - (bisect f a b n).1) / 2 ≤ tol (bisectMid f a b n)

instance (f : α → α) (tol : α → α) (a b : α) (n : ℕ) : Decidable (bisectDone f tol a b n) :=
  inferInstanceAs (Decidable (_ ≤ _))

end Thole.Roots
