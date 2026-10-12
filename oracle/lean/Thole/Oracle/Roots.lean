/-
The oracle for `thole-roots`.

Rust counterpart: `oracle/tests/roots.rs`.

There are two checks of `thole_roots::bisect`. Both take a polynomial, the
arguments of the call, and what the call returned.

- `checkBisectSpec`: the result is exactly what the specification
  (`Thole.Roots.bisect` and the definitions around it) computes over `ℚ`. This
  can only be decided where `f64` arithmetic makes the same decisions as exact
  arithmetic, so the check answers `skip` everywhere else.
- `checkBisectBound`: the result has the properties that the theorems in
  `Thole/Roots/Bisection.lean` give, up to stated rounding errors. This works
  for any finite input.
-/
import Thole.Oracle.Poly
import Thole.Roots.Bisection.Defs

namespace Thole.Oracle

open Thole.Roots

/-- A call of `thole_roots::bisect` on a polynomial. -/
structure BisectCall where
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
inductive BisectResult where
  /-- `Ok(Root { x, lo, hi, iterations })`. -/
  | root (x lo hi : ℚ) (iterations : ℕ)
  /-- `Err(Error::NoSignChange { .. })`. -/
  | noSignChange
  /-- `Err(Error::MaxIterations { lo, hi, .. })`. -/
  | maxIterations (lo hi : ℚ)

/-- The function whose root is sought. -/
def BisectCall.f (c : BisectCall) : ℚ → ℚ :=
  horner c.coeffs

/-- `Tolerance::bound`. -/
def BisectCall.tol (c : BisectCall) (x : ℚ) : ℚ :=
  c.abs + c.rel * |x|

/-! ### Agreement with the specification -/

/-- The number of steps after which the specification stops: the first `n`
for which `bisectDone` holds, if there is one within the iteration limit. -/
def BisectCall.stop (c : BisectCall) : Option ℕ :=
  (List.range (c.maxIter + 1)).find? fun n => bisectDone c.f c.tol c.a c.b n

/-- Whether the Rust code is certain to take the same decisions as the
specification on the first `steps` steps, so that the two must agree exactly.
This needs three things:

- the tolerance is absolute, so that `Tolerance::bound` involves no rounding;
- the width of the bracket and every midpoint are `f64` values, so that the
  Rust code computes them without rounding;
- at both ends of the bracket and at every midpoint, `f64` evaluation gives
  the sign of the polynomial. -/
def BisectCall.exact (c : BisectCall) (steps : ℕ) : Bool :=
  let mids := (List.range (steps + 1)).map (bisectMid c.f c.a c.b)
  c.rel == 0 && fitsF64 (c.b - c.a) && mids.all fitsF64 &&
    (c.a :: c.b :: mids.take steps).all (signCertain c.coeffs)

/-- Checks that the result is exactly what the specification computes.

The specification is run over `ℚ`: `SignChange` decides whether there is a
bracket, `bisectDone` when to stop, `bisect` and `bisectMid` what to return. -/
def checkBisectSpec (c : BisectCall) (r : BisectResult) : Verdict :=
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

/-! ### The guarantees, up to rounding -/

/-- The relative slack given to the comparisons that the Rust code makes in
`f64`: `1 + 2 ^ -48`, or 32 units roundoff. Each of those comparisons is
between two quantities computed with at most three operations. -/
def slack : ℚ := 1 + mkRat 1 (2 ^ 48)

/-- `f` changes sign between `lo` and `hi`, as far as `f64` evaluation can
tell: either it does, or its value at one of the two is within the rounding
error of zero. -/
def BisectCall.signChange (c : BisectCall) (lo hi : ℚ) : Bool :=
  decide (SignChange c.f lo hi) || !signCertain c.coeffs lo || !signCertain c.coeffs hi

/-- Checks the properties that the theorems give for the result.

For a root: the final bracket lies in the initial one and contains `x`
(`bisect_nested`), `f` changes sign over it (`bisect_signChange`), `x` is its
midpoint, and the stopping test holds (`bisectDone`). When `f` changes sign
exactly, `exists_root_of_signChange` then puts a root within the tolerance of
`x`, which is the statement of `bisectMid_error_of_done`. -/
def checkBisectBound (c : BisectCall) (r : BisectResult) : Verdict :=
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

/-! ### Requests -/

/-- Reads the arguments shared by the two checks:
`a b abs rel max_iter n c_0 ... c_(n-1)`, then the result as `root x lo hi
iterations`, `no-sign-change` or `max-iterations lo hi`. -/
def parseBisect (args : List String) : Except String (BisectCall × BisectResult) := do
  let a :: b :: abs :: rel :: maxIter :: n :: rest := args | throw "too few arguments"
  let n ← parseNat n
  if rest.length < n then throw "too few coefficients"
  let call : BisectCall := {
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
      let (call, result) ← parseBisect args
      pure (checkBisectSpec call result)),
   ("roots.bisect.bound", fun args => do
      let (call, result) ← parseBisect args
      pure (checkBisectBound call result))]

end Thole.Oracle
