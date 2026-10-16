/-
The oracle for `thole-quad`.

Rust counterpart: `oracle/tests/quad.rs`.

The functions integrated are polynomials, given by their coefficients as in
`Roots.lean`. The integral of a polynomial over `[a, b]` is a rational number,
which `integral` computes exactly.

There are four checks of `thole_quad::GaussLegendre`.

- `checkGaussRuleSpec`: the nodes and weights are exactly those that the
  program of `GaussLegendre.lean` computes in the model of `f64` arithmetic.
- `checkGaussRuleBound`: the nodes are the roots of `P_n` up to `2^-50`: they
  are sorted, symmetric, inside `(-1, 1)`, and `Thole.Quad.legendre`,
  evaluated exactly, changes sign around each of them. So the `n` nodes are
  close to `n` distinct roots of `P_n`, which has no others. The weights are
  `gaussWeight` at the nodes, up to a relative `2^-40`.
- `checkGaussSpec`: the integral of a polynomial is exactly what the program
  computes in the model of `f64` arithmetic.
- `checkGaussBound`: the integral of a polynomial of degree at most `2n - 1`
  is its exact integral, up to `ruleBudget`. That is the exactness that
  `gauss_exact` and `rule_exact_of_exact` give.

There are three checks of `thole_quad::gauss_kronrod`.

- `checkKronrodRule`: the constants of the Rust code are QUADPACK's, rounded
  to `f64`, and they integrate the monomials of degree at most 22 (Kronrod)
  and 13 (Gauss) exactly up to the rounding of the constants.
- `checkKronrodSpec`: the result is exactly what the program of
  `GaussKronrod.lean` computes in the model of `f64` arithmetic. That program
  is the specification (`Thole.Quad.gk` and `gkDone`) when its arithmetic is
  exact, which `QuadProofs.lean` proves.
- `checkKronrodBound`: the result has the properties that the definitions and
  theorems give: the stopping test holds, the number of evaluations matches
  the number of subintervals (`gk_length`), and for a polynomial of degree at
  most 22 the value is the exact integral up to rounding, since the Kronrod
  rule is then exact on every subinterval of the partition (`gk_partition`,
  `integral_eq_sum`).

The rounding allowances (`ruleBudget`) are first-order bounds derived in the
docstrings below, with a factor of 2 to spare. They are not proved.
-/
import Thole.Oracle.Roots
import Thole.Oracle.GaussLegendre
import Thole.Oracle.GaussKronrod
import Thole.Quad.GaussLegendre.Defs

namespace Thole.Oracle

open Thole.Quad

/-! ### Exact integrals -/

/-- `∫_a^b p(x) dx` for the polynomial with the given coefficients, lowest
degree first. -/
def integral (coeffs : List ℚ) (a b : ℚ) : ℚ :=
  ((List.range coeffs.length).zip coeffs).foldl
    (fun acc p => acc + p.2 * (b ^ (p.1 + 1) - a ^ (p.1 + 1)) / (p.1 + 1)) 0

/-- The degree of a polynomial, as the length of its coefficients minus one. -/
def degree (coeffs : List ℚ) : ℕ :=
  coeffs.length - 1

/-- A bound on the rounding error of a rule with `m` nodes, applied in `f64`
to a polynomial of degree at most `deg` on an interval of half-length `h`
inside `[-R, R]`, when the rule with exact nodes and weights would be exact.

With `u` the unit roundoff, `W` the sum of the weights, `P = p̃(R)` the
polynomial with the absolute values of the coefficients at `R` and `E` the
rounding error of evaluating the polynomial (`hornerError` at `R`):

- each node is off by at most `nodeErr` and each weight by a relative
  `wRel`, so each term is off by at most `w (wRel P + deg P (nodeErr + 4u))`:
  the derivative of the polynomial is at most `deg P / R`, and the point
  `c + h x` is off by at most `h nodeErr + 4u R`;
- each value of the polynomial is off by at most `E`;
- the sum of `m` terms, the products and the final product by `h` add at most
  `(m + 3) u` relative to `W (P + E)`.

The sum, times `h` and doubled, is the budget. -/
def ruleBudget (m : ℕ) (coeffs : List ℚ) (wRel nodeErr W h R : ℚ) : ℚ :=
  let u := unitRoundoff
  let P := horner (coeffs.map (|·|)) R
  let E := hornerError coeffs R
  let deg : ℚ := degree coeffs
  2 * h * W * (wRel * P + deg * P * (nodeErr + 4 * u) + E + (m + 3) * u * (P + E) * 2)

/-- `max(|a|, |b|)`, widened by `2^-40` so that the rounded points of a rule
are inside `[-R, R]`. -/
def radius (a b : ℚ) : ℚ :=
  max |a| |b| * (1 + mkRat 1 (2 ^ 40))

/-! ### Gauss-Legendre: the rule -/

/-- Checks that the nodes and weights are exactly those of the program of
`GaussLegendre.lean` in `f64` arithmetic. -/
def checkGaussRuleSpec (n : ℕ) (xs ws : List ℚ) : Verdict :=
  let (xs', ws') := gaussRuleG Arith.f64 n
  match xs'.mapM F64.toRat, ws'.mapM F64.toRat with
  | some xs', some ws' =>
    require (xs == xs') s!"the model has the nodes {xs'}" <|
    require (ws == ws') s!"the model has the weights {ws'}" .ok
  | _, _ => .skip "the model leaves the finite numbers"

/-- How far a node may be from a root of `P_n`. -/
def nodeTol : ℚ := mkRat 1 (2 ^ 50)

/-- How far a weight may be from `gaussWeight` at its node, relative to it. -/
def weightTol : ℚ := mkRat 1 (2 ^ 40)

/-- Checks that the nodes are the roots of `P_n` and the weights the Gauss
weights, up to `nodeTol` and `weightTol`. -/
def checkGaussRuleBound (n : ℕ) (xs ws : List ℚ) : Verdict :=
  let pairs := xs.zip ws
  require (xs.length == n && ws.length == n) s!"not {n} nodes and weights" <|
  require (xs.zip (xs.drop 1) |>.all fun p => p.1 < p.2) "the nodes are not increasing" <|
  require (xs == xs.reverse.map (- ·) && ws == ws.reverse) "the rule is not symmetric" <|
  require (xs.all fun x => -1 < x ∧ x < 1) "a node is outside (-1, 1)" <|
  require (pairs.all fun p =>
      let lo := legendre n (p.1 - nodeTol)
      let hi := legendre n (p.1 + nodeTol)
      legendre n p.1 == 0 || lo * hi ≤ 0)
    "P_n does not change sign around a node" <|
  require (pairs.all fun p =>
      let w := gaussWeight n p.1
      0 < p.2 ∧ |p.2 - w| ≤ weightTol * w)
    "a weight is not the Gauss weight of its node" .ok

/-! ### Gauss-Legendre: integrals -/

/-- What an integration returned: `Ok(value)`, or
`Err(Error::NonFiniteValue { x, .. })`. -/
inductive QuadResult where
  | value (v : ℚ)
  | nonFinite (x : ℚ)
  deriving DecidableEq

/-- Checks that the integral is exactly what the program computes in `f64`
arithmetic. -/
def checkGaussSpec (n : ℕ) (a b : ℚ) (coeffs : List ℚ) (r : QuadResult) : Verdict :=
  let A := Arith.f64
  let (xs, ws) := gaussRuleG A n
  match integrateG A xs ws (hornerG A (coeffs.map .fin)) (.fin a) (.fin b) with
  | .ok (.fin v) => require (r == .value v) s!"the model returns {v}" .ok
  | .error (.fin x) => require (r == .nonFinite x) s!"the model stops at {x}" .ok
  | _ => .skip "the model leaves the finite numbers"

/-- Checks that the integral of a polynomial of degree at most `2n - 1` is the
exact integral, up to `ruleBudget`. The nodes and weights are taken to be
within `nodeTol` and `weightTol` of the exact ones, which
`checkGaussRuleBound` checks. -/
def checkGaussBound (n : ℕ) (a b : ℚ) (coeffs : List ℚ) (r : QuadResult) : Verdict :=
  if 2 * n ≤ degree coeffs then .skip "the degree is above 2n - 1"
  else
    match r with
    | .value v =>
      let exact := integral coeffs a b
      let budget := ruleBudget n coeffs weightTol nodeTol (2 * (1 + weightTol)) (|b - a| / 2)
        (radius a b)
      require (|v - exact| ≤ budget) s!"the exact integral is {exact}" .ok
    | .nonFinite x =>
      require (min a b ≤ x ∧ x ≤ max a b) "the point is outside the interval" .ok

/-! ### Gauss-Kronrod: the constants -/

/-- The constants as `gauss_kronrod_rule` lists them: the 15 nodes in
increasing order, the Kronrod weights, and the Gauss weights with zero for the
nodes that are not Gauss nodes. -/
def kronrodRuleQ (round : ℚ → ℚ) : List ℚ × List ℚ × List ℚ :=
  let xgk := xgkQ.map round
  let wgk := wgkQ.map round
  let wg := (List.range 8).map fun j => if j % 2 = 1 then round (wgQ.getD (j / 2) 0) else 0
  ((xgk.take 7).map (- ·) ++ [0] ++ (xgk.take 7).reverse,
    wgk.take 7 ++ [wgk.getD 7 0] ++ (wgk.take 7).reverse,
    wg.take 7 ++ [round (wgQ.getD 3 0)] ++ (wg.take 7).reverse)

/-- The rounding of the constants allowed in the integral of `x^k`: each node
is within `2^-54` of the exact one and each weight within `2^-55`, plus the
error of the 33 published digits. The bound is `(16 + 2k) 2^-53`. -/
def kronrodTol (k : ℕ) : ℚ :=
  (16 + 2 * k) * mkRat 1 (2 ^ 53)

/-- `Σ w_i x_i^k`, exactly. -/
def momentQ (xs ws : List ℚ) (k : ℕ) : ℚ :=
  ((xs.zip ws).map fun p => p.2 * p.1 ^ k).sum

/-- `∫_{-1}^{1} x^k dx`. -/
def monomialIntegral (k : ℕ) : ℚ :=
  if k % 2 = 0 then 2 / (k + 1) else 0

/-- Checks the constants of `gauss_kronrod_rule`. -/
def checkKronrodRule (xs wk wg : List ℚ) : Verdict :=
  let f64 := fun q => (F64.round q).toRat.getD 0
  let (xs', wk', wg') := kronrodRuleQ f64
  require (xs == xs' && wk == wk' && wg == wg') "the constants are not QUADPACK's" <|
  require ((List.range 23).all fun k => |momentQ xs wk k - monomialIntegral k| ≤ kronrodTol k)
    "the Kronrod rule is not exact up to degree 22" <|
  require ((List.range 14).all fun k => |momentQ xs wg k - monomialIntegral k| ≤ kronrodTol k)
    "the Gauss rule is not exact up to degree 13" .ok

/-! ### Gauss-Kronrod: integrals -/

/-- A call of `thole_quad::gauss_kronrod` on a polynomial. -/
structure KronrodCall where
  coeffs : List ℚ
  a : ℚ
  b : ℚ
  abs : ℚ
  rel : ℚ
  maxSub : ℕ

/-- What the call returned. -/
inductive KronrodResult where
  | integral (value error : ℚ) (subintervals evaluations : ℕ)
  | maxSubintervals (value error : ℚ)
  | nonFinite (x : ℚ)
  deriving DecidableEq

/-- `Tolerance::bound`. -/
def KronrodCall.tol (c : KronrodCall) (x : ℚ) : ℚ :=
  c.abs + c.rel * |x|

/-- The constants as the program uses them. -/
def kronrodConstants {α : Type} (A : Arith α) : List α × List α × List α :=
  (xgkQ.map A.ofRat, wgkQ.map A.ofRat, wgQ.map A.ofRat)

/-- Checks that the result is exactly what the program of `GaussKronrod.lean`
computes in `f64` arithmetic. -/
def checkKronrodSpec (c : KronrodCall) (r : KronrodResult) : Verdict :=
  if ¬(0 ≤ c.abs ∧ 0 ≤ c.rel ∧ 0 < c.maxSub) then .skip "the arguments are not valid"
  else
    let A := Arith.f64
    let (xgk, wgk, wg) := kronrodConstants A
    let f := hornerG A (c.coeffs.map .fin)
    let tol := fun x => A.add (.fin c.abs) (A.mul (.fin c.rel) (A.abs x))
    match gkCallG A xgk wgk wg f tol (.fin c.a) (.fin c.b) c.maxSub with
    | .integral (.fin v) (.fin e) k =>
      match r with
      | .integral v' e' k' evaluations =>
        require (k' == k) s!"the model ends with {k} subintervals" <|
        require (v' == v && e' == e) s!"the model returns {v} with the error estimate {e}" <|
        require (evaluations == 15 * (2 * k - 1)) "wrong number of evaluations" .ok
      | _ => .fail s!"the model returns {v} with the error estimate {e}"
    | .maxSubintervals (.fin v) (.fin e) =>
      require (r == .maxSubintervals v e) s!"the model hits the limit at {v}, {e}" .ok
    | .nonFinite (.fin x) => require (r == .nonFinite x) s!"the model stops at {x}" .ok
    | _ => .skip "the model leaves the finite numbers"

/-- Checks the properties of the result. -/
def checkKronrodBound (c : KronrodCall) (r : KronrodResult) : Verdict :=
  if ¬(0 ≤ c.abs ∧ 0 ≤ c.rel ∧ 0 < c.maxSub) then .skip "the arguments are not valid"
  else
    match r with
    | .integral v e k evaluations =>
      require (1 ≤ k ∧ k ≤ c.maxSub) "the number of subintervals is not within the limit" <|
      require (evaluations == 15 * (2 * k - 1)) "wrong number of evaluations" <|
      require (0 ≤ e ∧ e ≤ c.tol v * slack + minPositive) "the stopping test does not hold" <|
      if 22 < degree c.coeffs then .ok
      else
        let exact := integral c.coeffs c.a c.b
        let W : ℚ := 2 * (1 + mkRat 1 (2 ^ 50))
        let h := |c.b - c.a| / 2
        let R := radius c.a c.b
        let P := horner (c.coeffs.map (|·|)) R
        let budget := ruleBudget 15 c.coeffs (mkRat 1 (2 ^ 52)) (mkRat 1 (2 ^ 53)) W h R +
          2 * k * unitRoundoff * h * W * (P + hornerError c.coeffs R) * 2
        require (|v - exact| ≤ budget) s!"the exact integral is {exact}" .ok
    | .maxSubintervals v e =>
      require (c.tol v ≤ e * slack + minPositive) "the stopping test holds" .ok
    | .nonFinite x =>
      require (min c.a c.b ≤ x ∧ x ≤ max c.a c.b) "the point is outside the interval" .ok

/-! ### Requests -/

/-- Reads `count` numbers from the front of `args`. -/
def takeF64 (count : ℕ) (args : List String) : Except String (List ℚ × List String) := do
  if args.length < count then throw "too few arguments"
  pure (← (args.take count).mapM parseF64, args.drop count)

/-- Reads `n x_0 ... x_(n-1) w_0 ... w_(n-1)`. -/
def parseGaussRule (args : List String) : Except String (ℕ × List ℚ × List ℚ) := do
  let n :: rest := args | throw "too few arguments"
  let n ← parseNat n
  let (xs, rest) ← takeF64 n rest
  let (ws, rest) ← takeF64 n rest
  if !rest.isEmpty then throw "too many arguments"
  pure (n, xs, ws)

/-- Reads `n a b k c_0 ... c_(k-1)`, then `value v` or `non-finite x`. -/
def parseGauss (args : List String) : Except String (ℕ × ℚ × ℚ × List ℚ × QuadResult) := do
  let n :: a :: b :: k :: rest := args | throw "too few arguments"
  let (coeffs, rest) ← takeF64 (← parseNat k) rest
  let result ← match rest with
    | ["value", v] => pure (.value (← parseF64 v))
    | ["non-finite", x] => pure (.nonFinite (← parseF64 x))
    | _ => throw "unknown result"
  pure (← parseNat n, ← parseF64 a, ← parseF64 b, coeffs, result)

/-- Reads `a b abs rel max_subintervals k c_0 ... c_(k-1)`, then
`integral value error subintervals evaluations`,
`max-subintervals value error` or `non-finite x`. -/
def parseKronrod (args : List String) : Except String (KronrodCall × KronrodResult) := do
  let a :: b :: abs :: rel :: maxSub :: k :: rest := args | throw "too few arguments"
  let (coeffs, rest) ← takeF64 (← parseNat k) rest
  let call : KronrodCall := {
    coeffs, a := ← parseF64 a, b := ← parseF64 b, abs := ← parseF64 abs,
    rel := ← parseF64 rel, maxSub := ← parseNat maxSub }
  let result ← match rest with
    | ["integral", v, e, k, evaluations] =>
      pure (.integral (← parseF64 v) (← parseF64 e) (← parseNat k) (← parseNat evaluations))
    | ["max-subintervals", v, e] => pure (.maxSubintervals (← parseF64 v) (← parseF64 e))
    | ["non-finite", x] => pure (.nonFinite (← parseF64 x))
    | _ => throw "unknown result"
  pure (call, result)

/-- The requests of this area, by name. -/
def quadRequests : List (String × (List String → Except String Verdict)) :=
  [("quad.gauss.rule.spec", fun args => do
      let (n, xs, ws) ← parseGaussRule args
      pure (checkGaussRuleSpec n xs ws)),
   ("quad.gauss.rule.bound", fun args => do
      let (n, xs, ws) ← parseGaussRule args
      pure (checkGaussRuleBound n xs ws)),
   ("quad.gauss.spec", fun args => do
      let (n, a, b, coeffs, result) ← parseGauss args
      pure (checkGaussSpec n a b coeffs result)),
   ("quad.gauss.bound", fun args => do
      let (n, a, b, coeffs, result) ← parseGauss args
      pure (checkGaussBound n a b coeffs result)),
   ("quad.kronrod.rule", fun args => do
      let (xs, rest) ← takeF64 15 args
      let (wk, rest) ← takeF64 15 rest
      let (wg, rest) ← takeF64 15 rest
      if !rest.isEmpty then throw "too many arguments"
      pure (checkKronrodRule xs wk wg)),
   ("quad.kronrod.spec", fun args => do
      let (call, result) ← parseKronrod args
      pure (checkKronrodSpec call result)),
   ("quad.kronrod.bound", fun args => do
      let (call, result) ← parseKronrod args
      pure (checkKronrodBound call result))]

end Thole.Oracle
