/-
Newton's method for root finding: the executable specification.

Rust counterpart: `thole_roots::newton` in `../../../../src/newton.rs`.

| Lean          | Rust                                                  |
|---------------|-------------------------------------------------------|
| `newtonStep`  | the step `x - f(x) / df(x)` in the loop of `newton`   |
| `newton`      | the approximation after `iterations` steps            |
| `newtonDone`  | the two stopping tests                                |

`df` is the derivative that the caller passes. The definitions do not require
it to be the derivative of `f`; the theorems in `../Newton.lean` do.

Where the derivative is zero, the Rust code stops with an error. Division by
zero is zero in a field, so `newtonStep` leaves the approximation where it is.
The theorems assume a derivative that is not zero.

Like bisection (`../Bisection/Defs.lean`), the definitions are written over
any linearly ordered field: `../Newton.lean` proves their properties over `ℝ`,
and the oracle runs them in a model of `f64` arithmetic
(`oracle/lean/Thole/Oracle/Newton.lean`).
-/
import Mathlib.Algebra.Field.Defs
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Logic.Function.Iterate

namespace Thole.Roots

variable {α : Type*} [Field α] [LinearOrder α]

/-- One Newton step from `x`: the root of the tangent to `f` at `x`, with
`df x` as its slope. -/
def newtonStep (f df : α → α) (x : α) : α :=
  x - f x / df x

/-- The approximation after `n` Newton steps from `x0`. -/
def newton (f df : α → α) (x0 : α) (n : ℕ) : α :=
  (newtonStep f df)^[n] x0

/-- The stopping test after `n` steps: `f` is zero at the approximation, or
the step that led to it is at most the tolerance at the approximation long.
`tol` is the tolerance as a function of the approximation. -/
def newtonDone (f df : α → α) (tol : α → α) (x0 : α) : ℕ → Prop
  | 0 => f x0 = 0
  | n + 1 => f (newton f df x0 (n + 1)) = 0 ∨
      |newton f df x0 (n + 1) - newton f df x0 n| ≤ tol (newton f df x0 (n + 1))

end Thole.Roots
