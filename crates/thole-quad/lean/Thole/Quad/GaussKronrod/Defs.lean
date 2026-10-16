/-
Adaptive Gauss-Kronrod quadrature: the executable specification.

Rust counterpart: `thole_quad::gauss_kronrod` in
`../../../../src/gauss_kronrod.rs`.

| Lean              | Rust                                                     |
|-------------------|----------------------------------------------------------|
| `Segment`         | `Segment`                                                |
| `kronrodEstimate` | `segment`: the 15-point estimate and the error estimate  |
| `mkSegment`       | `segment`, for an estimate given as a function           |
| `totalValue`      | the sum of the values in the loop of `gauss_kronrod`     |
| `totalError`      | the sum of the error estimates                           |
| `worstIndex`      | `worst`: the first subinterval with the largest estimate |
| `split`           | the halving of that subinterval                          |
| `gkStep`          | one pass of the loop                                     |
| `gk`              | the subintervals after `n` halvings                      |
| `gkDone`          | the stopping test                                        |

The iteration is written for any estimate `est a b = (value, error)` over a
subinterval `[a, b]`; `kronrodEstimate` is the one the Rust code uses. The
theorems of `../GaussKronrod.lean` hold for any estimate.

The constants of the rules are parameters: `xgk` and `wgk`, the 8 nodes and
weights of the Kronrod rule on `[0, 1]` from the largest node, and `wg`, the 4
weights of the Gauss rule, whose nodes are `xgk[1]`, `xgk[3]`, `xgk[5]` and
`xgk[7] = 0`.

Like the other definitions, these are written over any linearly ordered
field.
-/
import Mathlib.Algebra.Field.Defs
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Logic.Function.Iterate

namespace Thole.Quad

variable {α : Type*} [Field α] [LinearOrder α]

/-- A subinterval `[a, b]` with an estimate of the integral over it and an
estimate of the error of that. -/
structure Segment (α : Type*) where
  a : α
  b : α
  value : α
  error : α

/-- The 15-point Kronrod estimate of the integral of `f` over `[a, b]`, and
the absolute difference from the 7-point Gauss estimate. The sums are formed
as the Rust code forms them: the midpoint first, then the nodes in pairs
`c ∓ h x_j`. -/
def kronrodEstimate (xgk wgk wg : List α) (f : α → α) (a b : α) : α × α :=
  let c := a / 2 + b / 2
  let h := b / 2 - a / 2
  let kg := (List.range 7).foldl
    (fun (kg : α × α) j =>
      let sum := f (c - h * xgk.getD j 0) + f (c + h * xgk.getD j 0)
      (kg.1 + wgk.getD j 0 * sum, if j % 2 = 1 then kg.2 + wg.getD (j / 2) 0 * sum else kg.2))
    (wgk.getD 7 0 * f c, wg.getD 3 0 * f c)
  (h * kg.1, |h * (kg.1 - kg.2)|)

/-- The subinterval `[a, b]` with the estimates `est a b`. -/
def mkSegment (est : α → α → α × α) (a b : α) : Segment α :=
  ⟨a, b, (est a b).1, (est a b).2⟩

/-- The estimate of the integral: the sum of the values, from the first
subinterval. -/
def totalValue (ss : List (Segment α)) : α :=
  ss.foldl (fun acc s => acc + s.value) 0

/-- The estimate of the error: the sum of the error estimates. -/
def totalError (ss : List (Segment α)) : α :=
  ss.foldl (fun acc s => acc + s.error) 0

/-- The index of the first subinterval with the largest error estimate,
scanning from index `i`, with `best` the best index so far and `e` its error
estimate. -/
def worstFrom : List (Segment α) → ℕ → ℕ → α → ℕ
  | [], _, best, _ => best
  | s :: ss, i, best, e => if e < s.error then worstFrom ss (i + 1) i s.error
      else worstFrom ss (i + 1) best e

/-- The index of the first subinterval with the largest error estimate. -/
def worstIndex : List (Segment α) → ℕ
  | [] => 0
  | s :: ss => worstFrom ss 1 0 s.error

/-- Replaces the subinterval at index `i` by its two halves. -/
def split (est : α → α → α × α) (ss : List (Segment α)) (i : ℕ) : List (Segment α) :=
  match ss[i]? with
  | none => ss
  | some s =>
    ss.take i ++ [mkSegment est s.a (s.a / 2 + s.b / 2), mkSegment est (s.a / 2 + s.b / 2) s.b] ++
      ss.drop (i + 1)

/-- One pass of the loop: halve the first subinterval with the largest error
estimate. -/
def gkStep (est : α → α → α × α) (ss : List (Segment α)) : List (Segment α) :=
  split est ss (worstIndex ss)

/-- The subintervals after `n` halvings, starting from `[a, b]`. -/
def gk (est : α → α → α × α) (a b : α) (n : ℕ) : List (Segment α) :=
  (gkStep est)^[n] [mkSegment est a b]

/-- The stopping test: the error estimate is at most the tolerance at the
estimate of the integral. -/
def gkDone (tol : α → α) (ss : List (Segment α)) : Prop :=
  totalError ss ≤ tol (totalValue ss)

instance (tol : α → α) (ss : List (Segment α)) : Decidable (gkDone tol ss) :=
  inferInstanceAs (Decidable (_ ≤ _))

end Thole.Quad
