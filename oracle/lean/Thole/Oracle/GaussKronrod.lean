/-
Adaptive Gauss-Kronrod quadrature as a sequence of operations, over any
arithmetic.

Rust counterpart: `thole_quad::gauss_kronrod` in
`crates/thole-quad/src/gauss_kronrod.rs`.

Like `Brent.lean`, each definition follows the Rust code operation by
operation. `QuadProofs.lean` proves that with exact arithmetic they are the
definitions of `Thole/Quad/GaussKronrod/Defs.lean`. With `f64` arithmetic they
are what the Rust code computes, and `checkKronrodSpec` in `Quad.lean`
requires the Rust code to return exactly that.

| Here          | `GaussKronrod/Defs.lean`  | Rust                            |
|---------------|---------------------------|---------------------------------|
| `segmentG`    | `mkSegment`, `kronrodEstimate` | `segment`                  |
| `totalsG`     | `totalValue`, `totalError`| the sums in the loop            |
| `worstG`      | `worstIndex`              | `worst`                         |
| `splitG`      | `split`                   | the halving                     |
| `runGkG`      | `gk`, `gkDone`            | the loop, with its error exits  |
| `gkCallG`     |                           | `gauss_kronrod`                 |

A value of `f` that is not finite ends the call with an error that names the
point. The real numbers have no such values, so the definitions have no such
exit.
-/
import Thole.Oracle.Arith
import Thole.Quad.GaussKronrod.Defs

namespace Thole.Oracle

open Thole.Quad

/-! ### The constants

QUADPACK's `qk15`, as the Rust code writes them. Rust rounds each literal to
the nearest `f64`, and so does `Arith.ofRat` in `f64` arithmetic. -/

/-- `XGK`. -/
def xgkQ : List ℚ :=
  [0.991455371120812639206854697526329, 0.949107912342758524526189684047851,
   0.864864423359769072789712788640926, 0.741531185599394439863864773280788,
   0.586087235467691130294144845693013, 0.405845151377397166906606412076961,
   0.207784955007898467600689403773245, 0]

/-- `WGK`. -/
def wgkQ : List ℚ :=
  [0.022935322010529224963732008058970, 0.063092092629978553290700663189204,
   0.104790010322250183839876322541518, 0.140653259715525918745189590510238,
   0.169004726639267902826583426598550, 0.190350578064785409913256402421014,
   0.204432940075298892414161999234649, 0.209482141084727828012999174891714]

/-- `WG`. -/
def wgQ : List ℚ :=
  [0.129484966168869693270611432679082, 0.279705391489276667901467771423780,
   0.381830050505118944950369775488975, 0.417959183673469387755102040816327]

variable {α : Type} (A : Arith α)

/-- `f (x)`, or the error naming `x` if the value is not finite. -/
def evalG (f : α → α) (x : α) : Except α α :=
  if A.finite (f x) then .ok (f x) else .error x

/-- `segment`: the Kronrod estimate over `[a, b]` and the absolute difference
from the Gauss estimate, with the constants `xgk`, `wgk` and `wg`. -/
def segmentG (xgk wgk wg : List α) (f : α → α) (a b : α) : Except α (Segment α) := do
  let c := A.add (A.div a A.two) (A.div b A.two)
  let h := A.sub (A.div b A.two) (A.div a A.two)
  let fc ← evalG A f c
  let kg ← (List.range 7).foldlM
    (fun (kg : α × α) j => do
      let dx := A.mul h (xgk.getD j A.zero)
      let f₁ ← evalG A f (A.sub c dx)
      let f₂ ← evalG A f (A.add c dx)
      let sum := A.add f₁ f₂
      pure (A.add kg.1 (A.mul (wgk.getD j A.zero) sum),
        if j % 2 = 1 then A.add kg.2 (A.mul (wg.getD (j / 2) A.zero) sum) else kg.2))
    (A.mul (wgk.getD 7 A.zero) fc, A.mul (wg.getD 3 A.zero) fc)
  pure ⟨a, b, A.mul h kg.1, A.abs (A.mul h (A.sub kg.1 kg.2))⟩

/-- The sums of the values and of the error estimates, from the first
subinterval. -/
def totalsG (ss : List (Segment α)) : α × α :=
  ss.foldl (fun acc s => (A.add acc.1 s.value, A.add acc.2 s.error)) (A.zero, A.zero)

/-- `worstFrom`, with the comparison of `A`. -/
def worstFromG : List (Segment α) → ℕ → ℕ → α → ℕ
  | [], _, best, _ => best
  | s :: ss, i, best, e => if A.lt e s.error then worstFromG ss (i + 1) i s.error
      else worstFromG ss (i + 1) best e

/-- `worst`: the index of the first subinterval with the largest error
estimate. -/
def worstG : List (Segment α) → ℕ
  | [] => 0
  | s :: ss => worstFromG A ss 1 0 s.error

/-- The halving of the subinterval at index `i`: the left half is estimated
first. -/
def splitG (xgk wgk wg : List α) (f : α → α) (ss : List (Segment α)) (i : ℕ) :
    Except α (List (Segment α)) :=
  match ss[i]? with
  | none => pure ss
  | some s => do
    let mid := A.add (A.div s.a A.two) (A.div s.b A.two)
    let left ← segmentG A xgk wgk wg f s.a mid
    let right ← segmentG A xgk wgk wg f mid s.b
    pure (ss.take i ++ [left, right] ++ ss.drop (i + 1))

/-- How `thole_quad::gauss_kronrod` ends. -/
inductive GkOutcome (α : Type) where
  /-- `Ok(Integral { value, error, subintervals, .. })`. -/
  | integral (value error : α) (subintervals : ℕ)
  /-- `Err(Error::MaxSubintervals { value, error, .. })`. -/
  | maxSubintervals (value error : α)
  /-- `Err(Error::NonFiniteValue { x, .. })`. -/
  | nonFinite (x : α)

/-- The loop of the Rust code from the subintervals `ss`, with `fuel`
halvings left. -/
def runGkG (xgk wgk wg : List α) (f tol : α → α) (maxSub : ℕ) :
    ℕ → List (Segment α) → GkOutcome α
  | fuel, ss =>
    if A.le (totalsG A ss).2 (tol (totalsG A ss).1) then
      .integral (totalsG A ss).1 (totalsG A ss).2 ss.length
    else if maxSub ≤ ss.length then .maxSubintervals (totalsG A ss).1 (totalsG A ss).2
    else
      match fuel with
      | 0 => .maxSubintervals (totalsG A ss).1 (totalsG A ss).2
      | fuel + 1 =>
        match splitG A xgk wgk wg f ss (worstG A ss) with
        | .error x => .nonFinite x
        | .ok ss' => runGkG xgk wgk wg f tol maxSub fuel ss'

/-- The whole call, after its arguments have been checked: the estimate over
`[a, b]`, then the loop. Each halving adds one subinterval, so `maxSub`
halvings are enough to reach the limit. -/
def gkCallG (xgk wgk wg : List α) (f tol : α → α) (a b : α) (maxSub : ℕ) : GkOutcome α :=
  match segmentG A xgk wgk wg f a b with
  | .error x => .nonFinite x
  | .ok s => runGkG A xgk wgk wg f tol maxSub maxSub [s]

end Thole.Oracle
