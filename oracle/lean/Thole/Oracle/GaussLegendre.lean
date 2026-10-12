/-
The Gauss-Legendre rule as a sequence of operations, over any arithmetic.

Rust counterpart: `thole_quad::GaussLegendre` in
`crates/thole-quad/src/gauss_legendre.rs`.

Like `Brent.lean`, each definition follows the Rust code operation by
operation. `QuadProofs.lean` proves that with exact arithmetic they are the
definitions of `Thole/Quad/GaussLegendre/Defs.lean`. With `f64` arithmetic
they are what the Rust code computes, and `checkGaussRuleSpec` and
`checkGaussSpec` in `Quad.lean` require the Rust code to return exactly that.

| Here               | `GaussLegendre/Defs.lean` | Rust                         |
|--------------------|---------------------------|------------------------------|
| `legendreStepG`    | `legendreStep`            | the body of the loop         |
| `legendrePairG`    | `legendrePair`            | `(p0, p1)` in `legendre`     |
| `legendreDerivG`   | `legendreDeriv`           | the derivative in `legendre` |
| `weightG`          | `gaussWeight`             | `weight`                     |
| `nodeStepG`        | `gaussNodeStep`           | one Newton step              |
| `cosG`             |                           | `cos`                        |
| `nodeG`            |                           | one node in `new`            |
| `gaussRuleG`       |                           | `GaussLegendre::new`         |
| `integrateG`       | `rule`                    | `GaussLegendre::integrate`   |
-/
import Thole.Oracle.Arith
import Thole.Quad.GaussLegendre.Defs

namespace Thole.Oracle

variable {α : Type} (A : Arith α)

/-- `n as f64` for a natural number `n`. -/
def natG (n : ℕ) : α :=
  A.ofRat n

/-- One step of the recurrence: `((2k + 1) x p1 - k p0) / (k + 1)`. -/
def legendreStepG (x : α) (k : ℕ) (p : α × α) : α × α :=
  (p.2, A.div (A.sub (A.mul (A.mul (A.add (A.mul A.two (natG A k)) A.one) x) p.2)
      (A.mul (natG A k) p.1)) (A.add (natG A k) A.one))

/-- `(p0, p1)` at the end of `legendre`: the loop for `k` from 1 to `n - 1`,
from `(1, x)`. -/
def legendrePairG (n : ℕ) (x : α) : α × α :=
  (List.range' 1 (n - 1)).foldl (fun p k => legendreStepG A x k p) (A.one, x)

/-- `n * (x * p1 - p0) / (x * x - 1)`. -/
def legendreDerivG (n : ℕ) (x : α) : α :=
  A.div (A.mul (natG A n) (A.sub (A.mul x (legendrePairG A n x).2) (legendrePairG A n x).1))
    (A.sub (A.mul x x) A.one)

/-- `2 / ((1 - x * x) * dp * dp)`. -/
def weightG (n : ℕ) (x : α) : α :=
  A.div A.two (A.mul (A.mul (A.sub A.one (A.mul x x)) (legendreDerivG A n x))
    (legendreDerivG A n x))

/-- The step `dx = p / dp` and the next approximation `x - dx`. -/
def nodeStepG (n : ℕ) (x : α) : α × α :=
  (A.div (legendrePairG A n x).2 (legendreDerivG A n x),
    A.sub x (A.div (legendrePairG A n x).2 (legendreDerivG A n x)))

/-- `cos`: the Taylor polynomial, term by term, for `k` from 1 to 12. -/
def cosG (t : α) : α :=
  let t2 := A.mul t t
  let step := fun (ts : α × α) (k : ℕ) =>
    let term := A.div (A.mul (A.neg ts.1) t2)
      (A.mul (A.sub (A.mul A.two (natG A k)) A.one) (A.mul A.two (natG A k)))
    (term, A.add ts.2 term)
  ((List.range' 1 12).foldl step (A.one, A.one)).2

/-- `std::f64::consts::PI`: the `f64` nearest to `π`. -/
def piF64 : ℚ := mkRat 884279719003555 281474976710656

/-- `1e-14` as Rust reads the literal. -/
def newtonTol : ℚ := mkRat 1 (10 ^ 14)

/-- The Newton loop for one node, with `fuel` steps left. -/
def nodeLoopG (n : ℕ) : ℕ → α → α
  | 0, x => x
  | fuel + 1, x =>
    if A.le (A.abs (nodeStepG A n x).1) (A.ofRat newtonTol) then (nodeStepG A n x).2
    else nodeLoopG n fuel (nodeStepG A n x).2

/-- The `i`-th largest node: Newton's method from
`cos(PI * (i + 0.75) / (n + 0.5))`, for at most 100 steps. -/
def nodeG (n i : ℕ) : α :=
  nodeLoopG A n 100
    (cosG A (A.div (A.mul (A.ofRat piF64) (A.add (natG A i) (A.ofRat (3 / 4))))
      (A.add (natG A n) (A.ofRat (1 / 2)))))

/-- `GaussLegendre::new(n)`: the nodes in increasing order and their
weights. The `i`-th largest positive node `x_i` is the `i`-th node from the
right, and `-x_i` the `i`-th from the left. -/
def gaussRuleG (n : ℕ) : List α × List α :=
  let xs := (List.range (n / 2)).map (nodeG A n)
  let ws := xs.map (weightG A n)
  let middle := if n % 2 = 1 then [A.zero] else []
  let middleW := if n % 2 = 1 then [weightG A n A.zero] else []
  (xs.map A.neg ++ middle ++ xs.reverse, ws ++ middleW ++ ws.reverse)

/-- `GaussLegendre::integrate`: the value, or the first point at which `f` is
not finite. -/
def integrateG (xs ws : List α) (f : α → α) (a b : α) : Except α α :=
  let c := A.add (A.div a A.two) (A.div b A.two)
  let h := A.sub (A.div b A.two) (A.div a A.two)
  let sum := (xs.zip ws).foldlM (fun acc p =>
    let y := A.add c (A.mul h p.1)
    if A.finite (f y) then .ok (A.add acc (A.mul p.2 (f y))) else .error y) A.zero
  sum.map (A.mul h)

end Thole.Oracle
