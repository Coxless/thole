/-
The parts shared by every area of the oracle: verdicts, and reading `f64`
values as exact rational numbers.

The oracle is the executable `thole-oracle` (`../../Main.lean`). The Rust tests
in `oracle/tests/` send it one request per line: a problem, and what the Rust
code returned for it. It answers with a verdict, computed with exact rational
arithmetic from the definitions that the theorems are about.

Rust counterpart: `oracle/src/lib.rs`.
-/
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import Mathlib.Algebra.Order.Group.Unbundled.Abs

namespace Thole.Oracle

/-- The answer to a request. -/
inductive Verdict where
  /-- The result of the Rust code is what the specification allows. -/
  | ok
  /-- The request is outside what this check can decide. Nothing is claimed
  about the result. -/
  | skip (reason : String)
  /-- The result of the Rust code contradicts the specification. -/
  | fail (reason : String)

/-- The line sent back to the Rust side. -/
def Verdict.toLine : Verdict → String
  | .ok => "ok"
  | .skip reason => s!"skip {reason}"
  | .fail reason => s!"fail {reason}"

/-- `Verdict.fail` unless the condition holds. Used to chain checks: the first
one that does not hold gives the verdict. -/
def require (condition : Bool) (reason : String) (next : Verdict) : Verdict :=
  if condition then next else .fail reason

/-! ### `f64` values

A finite `f64` is a rational number. It is sent as the 16 hexadecimal digits
of its bit pattern, which loses nothing. -/

/-- The unit roundoff of `f64` arithmetic, `2 ^ -53`: the result of one
operation rounded to nearest is within this relative error of the exact one,
unless it underflows. -/
def unitRoundoff : ℚ := mkRat 1 (2 ^ 53)

/-- The smallest positive `f64`, `2 ^ -1074`. A result that underflows is
within half of this of the exact one. -/
def minPositive : ℚ := mkRat 1 (2 ^ 1074)

/-- The value of the `f64` with the given bit pattern, or `none` if it is an
infinity or a NaN. -/
def ofBits (bits : ℕ) : Option ℚ :=
  let exponent := bits / 2 ^ 52 % 2 ^ 11
  let fraction := bits % 2 ^ 52
  if exponent = 2047 then none
  else
    -- The value is `m * 2 ^ (e - 1075)`. Subnormal numbers (exponent field 0)
    -- have no implicit leading bit and the exponent of the field value 1.
    let (m, e) := if exponent = 0 then (fraction, 1) else (2 ^ 52 + fraction, exponent)
    let magnitude := mkRat (m * 2 ^ e : ℕ) (2 ^ 1075)
    some (if bits / 2 ^ 63 % 2 = 1 then -magnitude else magnitude)

/-- A sufficient condition for `q` to be an `f64`: it is `m / 2 ^ k` with
`|m| < 2 ^ 53` and `k ≤ 1022`. Some `f64` values (the large ones, and the
subnormal ones) do not pass. -/
def fitsF64 (q : ℚ) : Bool :=
  q.den == 2 ^ q.den.log2 && q.den ≤ 2 ^ 1022 && q.num.natAbs < 2 ^ 53

/-! ### Reading requests -/

/-- The value of a hexadecimal digit. -/
def hexDigit (c : Char) : Option ℕ :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

/-- Reads a finite `f64` from the 16 hexadecimal digits of its bit pattern. -/
def parseF64 (token : String) : Except String ℚ := do
  if token.length ≠ 16 then throw s!"not 16 hexadecimal digits: {token}"
  let digits ← token.toList.mapM fun c =>
    match hexDigit c with
    | some d => pure d
    | none => throw s!"not a hexadecimal digit in {token}"
  match ofBits (digits.foldl (fun n d => 16 * n + d) 0) with
  | some q => pure q
  | none => throw s!"not a finite number: {token}"

/-- Reads a natural number in decimal. -/
def parseNat (token : String) : Except String ℕ :=
  match token.toNat? with
  | some n => pure n
  | none => throw s!"not a natural number: {token}"

end Thole.Oracle
