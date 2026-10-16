/-
The oracle for `thole-roots`.

Rust counterpart: `oracle/tests/roots.rs`.

Every check takes a polynomial, the arguments of the call, and what the call
returned. The bracketing methods take the same arguments and return the same
results, so they share `BracketCall` and `BracketResult`.

There are two checks of `thole_roots::bisect`.

- `checkBisectSpec`: the result is exactly what the specification
  (`Thole.Roots.bisect` and the definitions around it) computes over `ℚ`. This
  can only be decided where `f64` arithmetic makes the same decisions as exact
  arithmetic, so the check answers `skip` everywhere else.
- `checkBisectBound`: the result has the properties that the theorems in
  `Thole/Roots/Bisection.lean` give, up to stated rounding errors. This works
  for any finite input.

There are two checks of `thole_roots::brent`.

- `checkBrentSpec`: the result is exactly what the program of `Brent.lean`
  computes in the model of `f64` arithmetic of `Arith.lean`. That program is
  the specification (`Thole.Roots.brent` and the definitions around it) when
  its arithmetic is exact, which `BrentProofs.lean` proves. An interpolation
  step divides, so `f64` arithmetic is exact almost nowhere and the comparison
  that bisection has would skip every call that takes a step.
- `checkBrentBound`: the result has the properties that the theorems in
  `Thole/Roots/Brent.lean` give, up to stated rounding errors.

There are two checks of `thole_roots::newton`, which takes a starting point
and a second polynomial for the derivative instead of a bracket.

- `checkNewtonSpec`: the result is exactly what the program of `Newton.lean`
  computes in the model of `f64` arithmetic, as for Brent's method.
  `NewtonProofs.lean` proves that the program is the specification
  (`Thole.Roots.newton` and `newtonDone`) when its arithmetic is exact.
- `checkNewtonBound`: the result has the properties that the theorems in
  `Thole/Roots/Newton.lean` give, up to stated rounding errors. The guarantee
  of a short step holds only under hypotheses on the derivative near the
  result; the check answers `skip` where it cannot establish them.
-/
import Thole.Oracle.Poly
import Thole.Oracle.Brent
import Thole.Oracle.Newton
import Thole.Roots.Bisection.Defs

namespace Thole.Oracle

open Thole.Roots

/-- A call of a bracketing method (`thole_roots::bisect`, `thole_roots::brent`)
on a polynomial. -/
structure BracketCall where
  /-- The coefficients of the polynomial, lowest degree first. -/
  coeffs : List ℚ
  /-- Lower end of the bracket. -/
  a : ℚ
  /-- Upper end of the bracket. -/
  b : ℚ
  /-- `Options::tol.abs`. -/
  abs : ℚ
  /-- `Options::tol.rel`. -/
  rel : ℚ
  /-- `Options::max_iter`. -/
  maxIter : ℕ

/-- What the call returned. -/
inductive BracketResult where
  /-- `Ok(Root { x, lo, hi, iterations })`. -/
  | root (x lo hi : ℚ) (iterations : ℕ)
  /-- `Err(Error::NoSignChange { .. })`. -/
  | noSignChange
  /-- `Err(Error::MaxIterations { lo, hi, .. })`. -/
  | maxIterations (lo hi : ℚ)

/-- The function whose root is sought. -/
def BracketCall.f (c : BracketCall) : ℚ → ℚ :=
  horner c.coeffs

/-- `Tolerance::bound`. -/
def BracketCall.tol (c : BracketCall) (x : ℚ) : ℚ :=
  c.abs + c.rel * |x|

/-! ### Bisection: agreement with the specification -/

/-- The number of steps after which the specification stops: the first `n`
for which `bisectDone` holds, if there is one within the iteration limit. -/
def BracketCall.stop (c : BracketCall) : Option ℕ :=
  (List.range (c.maxIter + 1)).find? fun n => bisectDone c.f c.tol c.a c.b n

/-- Whether the Rust code is certain to take the same decisions as the
specification on the first `steps` steps, so that the two must agree exactly.
This needs three things:

- the tolerance is absolute, so that `Tolerance::bound` involves no rounding;
- the width of the bracket and every midpoint are `f64` values, so that the
  Rust code computes them without rounding;
- at both ends of the bracket and at every midpoint, `f64` evaluation gives
  the sign of the polynomial. -/
def BracketCall.exact (c : BracketCall) (steps : ℕ) : Bool :=
  let mids := (List.range (steps + 1)).map (bisectMid c.f c.a c.b)
  c.rel == 0 && fitsF64 (c.b - c.a) && mids.all fitsF64 &&
    (c.a :: c.b :: mids.take steps).all (signCertain c.coeffs)

/-- Checks that the result is exactly what the specification computes.

The specification is run over `ℚ`: `SignChange` decides whether there is a
bracket, `bisectDone` when to stop, `bisect` and `bisectMid` what to return. -/
def checkBisectSpec (c : BracketCall) (r : BracketResult) : Verdict :=
  if ¬(c.a ≤ c.b ∧ 0 ≤ c.abs ∧ 0 ≤ c.rel) then .skip "the arguments are not valid"
  else if ¬SignChange c.f c.a c.b then
    if !(c.rel == 0 && signCertain c.coeffs c.a && signCertain c.coeffs c.b) then
      .skip "rounding can change a decision"
    else
      match r with
      | .noSignChange => .ok
      | _ => .fail "the specification has no sign change over the bracket"
  else
    let steps := c.stop.getD c.maxIter
    let (lo', hi') := bisect c.f c.a c.b steps
    if !c.exact steps then .skip "rounding can change a decision"
    else
      match c.stop, r with
      | some n, .root x lo hi iterations =>
        require (iterations == n) s!"the specification stops after {n} steps" <|
        require (lo == lo' && hi == hi') s!"the specification ends with the bracket [{lo'}, {hi'}]" <|
        require (x == bisectMid c.f c.a c.b n) "x is not the midpoint of the bracket" .ok
      | none, .maxIterations lo hi =>
        require (lo == lo' && hi == hi') s!"the specification ends with the bracket [{lo'}, {hi'}]" .ok
      | some n, _ => .fail s!"the specification stops after {n} steps"
      | none, _ => .fail "the specification does not stop within the iteration limit"

/-! ### Bisection: the guarantees, up to rounding -/

/-- The relative slack given to the comparisons that the Rust code makes in
`f64`: `1 + 2 ^ -48`, or 32 units roundoff. Each of those comparisons is
between two quantities computed with at most three operations. -/
def slack : ℚ := 1 + mkRat 1 (2 ^ 48)

/-- `f` changes sign between `lo` and `hi`, as far as `f64` evaluation can
tell: either it does, or its value at one of the two is within the rounding
error of zero. -/
def BracketCall.signChange (c : BracketCall) (lo hi : ℚ) : Bool :=
  decide (SignChange c.f lo hi) || !signCertain c.coeffs lo || !signCertain c.coeffs hi

/-- Checks the properties that the theorems give for the result.

For a root: the final bracket lies in the initial one and contains `x`
(`bisect_nested`), `f` changes sign over it (`bisect_signChange`), `x` is its
midpoint, and the stopping test holds (`bisectDone`). When `f` changes sign
exactly, `exists_root_of_signChange` then puts a root within the tolerance of
`x`, which is the statement of `bisectMid_error_of_done`. -/
def checkBisectBound (c : BracketCall) (r : BracketResult) : Verdict :=
  if ¬(c.a ≤ c.b ∧ 0 ≤ c.abs ∧ 0 ≤ c.rel) then .skip "the arguments are not valid"
  else
    match r with
    | .noSignChange =>
      require (!(decide (SignChange c.f c.a c.b) && signCertain c.coeffs c.a && signCertain c.coeffs c.b))
        "f changes sign over the bracket" .ok
    | .root x lo hi iterations =>
      let mid := (lo + hi) / 2
      require (iterations ≤ c.maxIter) "more steps than the iteration limit" <|
      require (c.a ≤ lo && lo ≤ x && x ≤ hi && hi ≤ c.b) "the brackets are not nested" <|
      require (c.signChange lo hi) "f does not change sign over the final bracket" <|
      require (|x - mid| ≤ 2 * unitRoundoff * |mid| + minPositive)
        "x is not the midpoint of the bracket" <|
      require ((hi - lo) / 2 ≤ c.tol x * slack + minPositive) "the stopping test does not hold" .ok
    | .maxIterations lo hi =>
      require (c.a ≤ lo && lo ≤ hi && hi ≤ c.b) "the brackets are not nested" <|
      require (c.signChange lo hi) "f does not change sign over the final bracket" <|
      require (c.tol ((lo + hi) / 2) ≤ (hi - lo) / 2 * slack + minPositive)
        "the stopping test holds" .ok

/-! ### Brent's method: agreement with the specification -/

/-- Checks that the result is exactly what the program of `Brent.lean`
computes in `f64` arithmetic.

The polynomial is evaluated as `Poly::eval` does (`hornerG`), the tolerance is
computed as the Rust code does (`brentTolG`), and `runG` takes the steps of
`brentG` until the stopping test holds or the iteration limit is reached. The
call must have ended in the same way, after the same number of steps, with the
same approximation and the same bracket. -/
def checkBrentSpec (c : BracketCall) (r : BracketResult) : Verdict :=
  if ¬(c.a ≤ c.b ∧ 0 ≤ c.abs ∧ 0 ≤ c.rel) then .skip "the arguments are not valid"
  else
    let A := Arith.f64
    let f := hornerG A (c.coeffs.map .fin)
    let tol := brentTolG A (.fin c.abs) (.fin c.rel)
    if !signChangeG A (f (.fin c.a)) (f (.fin c.b)) then
      match r with
      | .noSignChange => .ok
      | _ => .fail "the model has no sign change over the bracket"
    else
      let (done, steps, s) := runG A f tol c.maxIter 0 (initG A f (.fin c.a) (.fin c.b))
      match s.cur, s.contra with
      | .fin cur, .fin contra =>
        let lo' := min cur contra
        let hi' := max cur contra
        match done, r with
        | true, .root x lo hi iterations =>
          require (iterations == steps) s!"the model stops after {steps} steps" <|
          require (x == cur) s!"the model returns {cur}" <|
          require (lo == lo' && hi == hi') s!"the model ends with the bracket [{lo'}, {hi'}]" .ok
        | false, .maxIterations lo hi =>
          require (lo == lo' && hi == hi') s!"the model ends with the bracket [{lo'}, {hi'}]" .ok
        | true, _ => .fail s!"the model stops after {steps} steps"
        | false, _ => .fail "the model does not stop within the iteration limit"
      | _, _ => .skip "the model leaves the finite numbers"

/-! ### Brent's method: the guarantees, up to rounding -/

/-- The tolerance that `thole_roots::brent` passes to the definitions: half
of `Tolerance::bound`, as the header of `Thole/Roots/Brent/Defs.lean` says. -/
def BracketCall.brentTol (c : BracketCall) (x : ℚ) : ℚ :=
  c.tol x / 2

/-- Checks the properties that the theorems give for the result of
`thole_roots::brent`.

For a root: the final bracket lies in the initial one (`brent_mem`), `x` is
one of its ends, `f` changes sign over it (`brent_signChange`), and the
stopping test holds (`brentDone`): the value of `f` at `x` is within the
rounding error of zero, or half the length of the bracket is at most the
tolerance. When `f` changes sign exactly, `exists_root_of_signChange_uIcc`
then puts a root within `Tolerance::bound` of `x`, which is the statement of
`brent_error_of_done`.

The stopping test is made in `f64` on two quantities computed with at most
three operations each, which `slack` covers. A halving that underflows is
off by at most half of `minPositive`.

`brent_done_of_le` is not checked. Its bound on the number of steps is
`2 * (b - a) / abs`, which is beyond any iteration limit unless the tolerance
is coarse. -/
def checkBrentBound (c : BracketCall) (r : BracketResult) : Verdict :=
  if ¬(c.a ≤ c.b ∧ 0 ≤ c.abs ∧ 0 ≤ c.rel) then .skip "the arguments are not valid"
  else
    match r with
    | .noSignChange =>
      require (!(decide (SignChange c.f c.a c.b) && signCertain c.coeffs c.a && signCertain c.coeffs c.b))
        "f changes sign over the bracket" .ok
    | .root x lo hi iterations =>
      require (iterations ≤ c.maxIter) "more steps than the iteration limit" <|
      require (c.a ≤ lo && lo ≤ hi && hi ≤ c.b) "the brackets are not nested" <|
      require (x == lo || x == hi) "x is not an end of the final bracket" <|
      require (c.signChange lo hi) "f does not change sign over the final bracket" <|
      require (!signCertain c.coeffs x || (hi - lo) / 2 ≤ c.brentTol x * slack + 2 * minPositive)
        "the stopping test does not hold" .ok
    | .maxIterations lo hi =>
      require (c.a ≤ lo && lo ≤ hi && hi ≤ c.b) "the brackets are not nested" <|
      require (c.signChange lo hi) "f does not change sign over the final bracket" <|
      -- The approximation is one of the two ends, and the result does not say which.
      require (min (c.brentTol lo) (c.brentTol hi) ≤ (hi - lo) / 2 * slack + 2 * minPositive)
        "the stopping test holds" .ok

/-! ### Newton's method -/

/-- A call of `thole_roots::newton` on a polynomial and a second polynomial
for its derivative. -/
structure NewtonCall where
  /-- The coefficients of `f`, lowest degree first. -/
  coeffs : List ℚ
  /-- The coefficients of the derivative that is passed, lowest degree
  first. -/
  dcoeffs : List ℚ
  /-- The starting point. -/
  x0 : ℚ
  /-- `Options::tol.abs`. -/
  abs : ℚ
  /-- `Options::tol.rel`. -/
  rel : ℚ
  /-- `Options::max_iter`. -/
  maxIter : ℕ

/-- `Tolerance::bound`. -/
def NewtonCall.tol (c : NewtonCall) (x : ℚ) : ℚ :=
  c.abs + c.rel * |x|

deriving instance DecidableEq for NewtonOutcome

/-- How a result is written in a reason. -/
def NewtonOutcome.describe : NewtonOutcome ℚ → String
  | .root x step iterations => s!"the root {x} after {iterations} steps, the last of {step}"
  | .notConverged x => s!"no convergence, ending at {x}"
  | .zeroDerivative x => s!"a zero derivative at {x}"
  | .nonFiniteStep x => s!"a step that is not finite from {x}"
  | .nanValue x => s!"NaN from f at {x}"
  | .nanDerivative x => s!"NaN from the derivative at {x}"

/-- The outcome of the model with its values as rational numbers, or `none`
if one of them is not finite. -/
def NewtonOutcome.toExact : NewtonOutcome F64 → Option (NewtonOutcome ℚ)
  | .root (.fin x) (.fin step) n => some (.root x step n)
  | .notConverged (.fin x) => some (.notConverged x)
  | .zeroDerivative (.fin x) => some (.zeroDerivative x)
  | .nonFiniteStep (.fin x) => some (.nonFiniteStep x)
  | .nanValue (.fin x) => some (.nanValue x)
  | .nanDerivative (.fin x) => some (.nanDerivative x)
  | _ => none

/-- Checks that the result is exactly what the program of `Newton.lean`
computes in `f64` arithmetic: the polynomials are evaluated as `Poly::eval`
does (`hornerG`), and the tolerance as `Tolerance::bound` does. -/
def checkNewtonSpec (c : NewtonCall) (r : NewtonOutcome ℚ) : Verdict :=
  if ¬(0 ≤ c.abs ∧ 0 ≤ c.rel) then .skip "the arguments are not valid"
  else
    let A := Arith.f64
    let f := hornerG A (c.coeffs.map .fin)
    let df := hornerG A (c.dcoeffs.map .fin)
    let tol := fun x => A.add (.fin c.abs) (A.mul (.fin c.rel) (A.abs x))
    match (newtonCallG A f df tol (.fin c.x0) c.maxIter).toExact with
    | some expected => require (r == expected) s!"the model ends with {expected.describe}" .ok
    | none => .skip "the model leaves the finite numbers"

/-- The coefficients of the derivative of a polynomial, from the term of
degree `k` on. -/
def derivFrom : ℕ → List ℚ → List ℚ
  | _, [] => []
  | k, c :: cs => k * c :: derivFrom (k + 1) cs

/-- The coefficients of the derivative of the polynomial with the given
coefficients. -/
def derivCoeffs (coeffs : List ℚ) : List ℚ :=
  derivFrom 1 (coeffs.drop 1)

/-- Checks the properties that the theorems give for the result of
`thole_roots::newton`.

The theorems are about a derivative that is the derivative of `f`, so the
check answers `skip` unless the second polynomial is exactly that.

For a root, the iteration limit is respected and one of the two stopping
tests holds: the value of `f` at `x` is within the rounding error of zero, or
the last step is at most the tolerance long. In the second case the check
then looks for the hypotheses of `newtonStep_exists_root` around `x`, and
if they hold, requires `f` to change sign within the bound that the theorem
gives, widened by the rounding of the last step. It
answers `skip` when the hypotheses cannot be established, for example near a
multiple root.

The interval and the rounding allowance are first-order bounds derived here,
not proved. With `u` the unit roundoff, `s` the last step and `E_f`, `E_df`
the rounding errors of evaluating `f` and the derivative near `x`
(`hornerError`): the step that `f64` arithmetic takes differs from the exact
Newton step from the same point by at most
`e = 4u(|x| + |s|) + 8(E_f + (2|s| + minPositive) E_df) / |f'(x)|`, provided
that the derivative stays above `|f'(x)| / 2` on the interval of half-width
`w = 4(|s| + e)` around `x`, and that `E_df` is at most an eighth of
`|f'(x)|`. With `L` a bound on `|f''|` there, `newtonStep_exists_root` then
applies to the exact step with `m = |f'(x)| / 2`, and puts a root within
`(|s| + e) / 2 + e` of `x`.

Errors other than a root are not about anything the theorems say, apart from
a zero derivative, which must be zero up to rounding. -/
def checkNewtonBound (c : NewtonCall) (r : NewtonOutcome ℚ) : Verdict :=
  if ¬(0 ≤ c.abs ∧ 0 ≤ c.rel) then .skip "the arguments are not valid"
  else if c.dcoeffs != derivCoeffs c.coeffs then .skip "df is not the derivative of f"
  else
    match r with
    | .root x s 0 =>
      require (x == c.x0 && s == 0) "no step was taken, but the result is not x0" <|
      require (!signCertain c.coeffs x) "f is not zero at x0" .ok
    | .root x s k =>
      let zero := !signCertain c.coeffs x
      let short := |s| ≤ c.tol x * slack + minPositive
      require (k ≤ c.maxIter) "more steps than the iteration limit" <|
      require (zero || short) "neither stopping test holds" <|
      if !short then .ok
      else
        let u := unitRoundoff
        let R := |x| + 1
        let D := |horner c.dcoeffs x|
        let L := horner ((derivCoeffs c.dcoeffs).map (|·|)) R
        let EF := hornerError c.coeffs R
        let ED := hornerError c.dcoeffs R
        if !(0 < D && 8 * ED ≤ D) then .skip "the derivative is too close to zero at x"
        else
          let e := 4 * u * (|x| + |s|) + 8 * (EF + (2 * |s| + minPositive) * ED) / D
          let w := 4 * (|s| + e)
          if !(w ≤ 1 && L * w ≤ D / 2) then
            .skip "the hypotheses of newtonStep_exists_root cannot be established"
          else
            let τ := (|s| + e) / 2 + e
            let f := horner c.coeffs
            require (decide (SignChange f (x - τ) (x + τ)) || !signCertain c.coeffs (x - τ) ||
                !signCertain c.coeffs (x + τ))
              s!"no root within {τ} of x" .ok
    | .zeroDerivative x =>
      require (!signCertain c.dcoeffs x) "the derivative is not zero at x" .ok
    | _ => .ok

/-! ### Requests -/

/-- Reads the arguments shared by the checks:
`a b abs rel max_iter n c_0 ... c_(n-1)`, then the result as `root x lo hi
iterations`, `no-sign-change` or `max-iterations lo hi`. -/
def parseBracket (args : List String) : Except String (BracketCall × BracketResult) := do
  let a :: b :: abs :: rel :: maxIter :: n :: rest := args | throw "too few arguments"
  let n ← parseNat n
  if rest.length < n then throw "too few coefficients"
  let call : BracketCall := {
    coeffs := ← (rest.take n).mapM parseF64
    a := ← parseF64 a
    b := ← parseF64 b
    abs := ← parseF64 abs
    rel := ← parseF64 rel
    maxIter := ← parseNat maxIter }
  let result ← match rest.drop n with
    | ["root", x, lo, hi, iterations] =>
      pure (.root (← parseF64 x) (← parseF64 lo) (← parseF64 hi) (← parseNat iterations))
    | ["no-sign-change"] => pure .noSignChange
    | ["max-iterations", lo, hi] => pure (.maxIterations (← parseF64 lo) (← parseF64 hi))
    | _ => throw "unknown result"
  pure (call, result)

/-- Reads the arguments of a call of `thole_roots::newton`:
`x0 abs rel max_iter n c_0 ... c_(n-1) m d_0 ... d_(m-1)`, then the result as
`root x step iterations`, `not-converged x`, `zero-derivative x`,
`non-finite-step x`, `nan-value x` or `nan-derivative x`. -/
def parseNewton (args : List String) : Except String (NewtonCall × NewtonOutcome ℚ) := do
  let x0 :: abs :: rel :: maxIter :: n :: rest := args | throw "too few arguments"
  let n ← parseNat n
  if rest.length < n then throw "too few coefficients"
  let m :: rest' := rest.drop n | throw "too few arguments"
  let m ← parseNat m
  if rest'.length < m then throw "too few coefficients"
  let call : NewtonCall := {
    coeffs := ← (rest.take n).mapM parseF64
    dcoeffs := ← (rest'.take m).mapM parseF64
    x0 := ← parseF64 x0
    abs := ← parseF64 abs
    rel := ← parseF64 rel
    maxIter := ← parseNat maxIter }
  let result ← match rest'.drop m with
    | ["root", x, step, iterations] =>
      pure (.root (← parseF64 x) (← parseF64 step) (← parseNat iterations))
    | ["not-converged", x] => pure (.notConverged (← parseF64 x))
    | ["zero-derivative", x] => pure (.zeroDerivative (← parseF64 x))
    | ["non-finite-step", x] => pure (.nonFiniteStep (← parseF64 x))
    | ["nan-value", x] => pure (.nanValue (← parseF64 x))
    | ["nan-derivative", x] => pure (.nanDerivative (← parseF64 x))
    | _ => throw "unknown result"
  pure (call, result)

/-- The requests of this area, by name. -/
def rootsRequests : List (String × (List String → Except String Verdict)) :=
  [("roots.bisect.spec", fun args => do
      let (call, result) ← parseBracket args
      pure (checkBisectSpec call result)),
   ("roots.bisect.bound", fun args => do
      let (call, result) ← parseBracket args
      pure (checkBisectBound call result)),
   ("roots.brent.spec", fun args => do
      let (call, result) ← parseBracket args
      pure (checkBrentSpec call result)),
   ("roots.brent.bound", fun args => do
      let (call, result) ← parseBracket args
      pure (checkBrentBound call result)),
   ("roots.newton.spec", fun args => do
      let (call, result) ← parseNewton args
      pure (checkNewtonSpec call result)),
   ("roots.newton.bound", fun args => do
      let (call, result) ← parseNewton args
      pure (checkNewtonBound call result))]

end Thole.Oracle
