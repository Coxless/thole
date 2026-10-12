/-
Newton's method as a sequence of operations, over any arithmetic.

Rust counterpart: `thole_roots::newton` in `crates/thole-roots/src/newton.rs`.

Like `Brent.lean`, each definition follows the Rust code operation by
operation. `NewtonProofs.lean` proves that with exact arithmetic the steps are
those of `Thole/Roots/Newton/Defs.lean`, and that the loop stops where
`newtonDone` holds. With `f64` arithmetic they are what the Rust code
computes, and `checkNewtonSpec` in `Roots.lean` requires the Rust code to
return exactly that.

| Here              | `Newton/Defs.lean` | Rust                              |
|-------------------|--------------------|-----------------------------------|
| `newtonStepG`     | `newtonStep`       | `step = fx / dfx; x - step`       |
| `newtonG`         | `newton`           | `x` after `iterations` steps      |
| `runNewtonG`      | `newtonDone`       | the loop, with its error exits    |
| `NewtonOutcome`   |                    | `Result<NewtonRoot, Error>`       |

The error exits have no counterpart in the definitions: they are where the
real numbers have nothing to say (NaN, infinities), or where a field divides
by zero without complaint.
-/
import Thole.Oracle.Arith
import Thole.Roots.Newton.Defs

namespace Thole.Oracle

/-- How the loop of `thole_roots::newton` ends. -/
inductive NewtonOutcome (α : Type) where
  /-- `Ok(NewtonRoot { x, step, iterations })`. -/
  | root (x step : α) (iterations : ℕ)
  /-- `Err(Error::NotConverged { x, .. })`. -/
  | notConverged (x : α)
  /-- `Err(Error::ZeroDerivative { x })`. -/
  | zeroDerivative (x : α)
  /-- `Err(Error::NonFiniteStep { x })`. -/
  | nonFiniteStep (x : α)
  /-- `Err(Error::NanValue { x })`. -/
  | nanValue (x : α)
  /-- `Err(Error::NanDerivative { x })`. -/
  | nanDerivative (x : α)

variable {α : Type} (A : Arith α)

/-- The step and the next approximation: `step = fx / dfx`, then
`x - step`. -/
def newtonStepG (f df : α → α) (x : α) : α × α :=
  (A.div (f x) (df x), A.sub x (A.div (f x) (df x)))

/-- The approximation after `n` steps from `x0`. -/
def newtonG (f df : α → α) (x0 : α) (n : ℕ) : α :=
  (fun x => (newtonStepG A f df x).2)^[n] x0

/-- `x.is_nan()`: a NaN is the only value not equal to itself. -/
def isNaNG (x : α) : Bool :=
  !A.eq x x

/-- The loop of the Rust code from the approximation `x`, reached after
`steps` steps by the step `step`, with `fuel` steps left before the iteration
limit. -/
def runNewtonG (f df tol : α → α) : ℕ → ℕ → α → α → NewtonOutcome α
  | fuel, steps, x, step =>
    if isNaNG A (f x) then .nanValue x
    else if A.eq (f x) A.zero then .root x step steps
    else
      match fuel with
      | 0 => .notConverged x
      | fuel + 1 =>
        if isNaNG A (df x) then .nanDerivative x
        else if A.eq (df x) A.zero then .zeroDerivative x
        else if !A.finite (df x) || !A.finite (newtonStepG A f df x).2 then .nonFiniteStep x
        else if A.le (A.abs (newtonStepG A f df x).1) (tol (newtonStepG A f df x).2) then
          .root (newtonStepG A f df x).2 (newtonStepG A f df x).1 (steps + 1)
        else runNewtonG f df tol fuel (steps + 1) (newtonStepG A f df x).2
          (newtonStepG A f df x).1

/-- The whole call: the loop from `x0`, with `maxIter` steps allowed. -/
def newtonCallG (f df tol : α → α) (x0 : α) (maxIter : ℕ) : NewtonOutcome α :=
  runNewtonG A f df tol maxIter 0 x0 A.zero

end Thole.Oracle
