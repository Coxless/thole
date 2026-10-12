/-
Polynomials: the functions the oracle can evaluate exactly.

A Rust closure cannot be sent to the oracle, so the two sides agree on a
family of functions instead. A polynomial is given by its coefficients, lowest
degree first, and both sides evaluate it with Horner's rule: the Rust side in
`f64`, this side in `ℚ`.

Rust counterpart: `Poly` in `oracle/src/poly.rs`.
-/
import Thole.Oracle.Basic

namespace Thole.Oracle

/-- The polynomial with the given coefficients, lowest degree first, at `x`,
by Horner's rule. -/
def horner {α : Type*} [Field α] (coeffs : List α) (x : α) : α :=
  coeffs.foldr (fun c acc => acc * x + c) 0

/-- A bound on `|y - horner coeffs x|`, where `y` is what `Poly::eval`
computes in `f64` for the same coefficients and the same `x`, provided nothing
overflows.

This is not proved in Lean. It is the standard bound for Horner's rule in
floating-point arithmetic (N. J. Higham, "Accuracy and Stability of Numerical
Algorithms", 2nd edition, section 5.1): with `n` the degree and `u` the unit
roundoff, the error is at most `γ * p̃(|x|)`, where `γ = 2nu / (1 - 2nu)` and
`p̃` is the polynomial with the absolute values of the coefficients. The
second term covers multiplications that underflow, which the textbook bound
excludes: each of the `n` products is then off by at most half of
`minPositive`, and the later steps scale that by a power of `|x|`. -/
def hornerError (coeffs : List ℚ) (x : ℚ) : ℚ :=
  let n := coeffs.length - 1
  let k : ℚ := 2 * n * unitRoundoff
  k / (1 - k) * horner (coeffs.map (|·|)) |x| + minPositive * horner (List.replicate n 1) |x|

/-- Whether `f64` evaluation is certain to give the sign of the polynomial at
`x`: the exact value is further from zero than the rounding error can be. -/
def signCertain (coeffs : List ℚ) (x : ℚ) : Bool :=
  hornerError coeffs x < |horner coeffs x|

end Thole.Oracle
