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
-/
import Thole.Oracle.Poly
import Thole.Oracle.Brent
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
      pure (checkBrentBound call result))]

end Thole.Oracle
