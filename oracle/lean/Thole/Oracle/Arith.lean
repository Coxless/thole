/-
Two arithmetics for one program: exact, and `f64`.

A check against the specification needs the Rust code and the Lean
definitions to take the same decisions. For bisection that can be decided
where `f64` arithmetic is exact. For an algorithm that divides it is exact
almost nowhere, so the comparison is made the other way round: the oracle runs
the sequence of operations of the Rust code in a model of `f64` arithmetic,
and the result of the Rust code must be that of the model, bit for bit.

The sequence of operations is written once, over an `Arith`: a set of
operations on some type. With the operations of `ℚ` (`Arith.exact`) it is
proved to be the definition the theorems are about. With the operations of
`F64` (`Arith.f64`) it is what the Rust code computes.

`F64` models IEEE 754 binary64 arithmetic with rounding to nearest, ties to
even: finite values are rational numbers, and overflow gives an infinity. This
is not proved to be what a processor does. It is tested: `oracle/tests/wire.rs`
compares each operation with the `f64` arithmetic of Rust on operands drawn at
random.

Two things are not modelled, and neither can be observed by the programs
here. Zero has no sign. And a non-zero number divided by zero is a NaN, where
`f64` gives an infinity with the sign that the model does not have.

Rust counterpart: `f64`.
-/
import Thole.Oracle.Basic

namespace Thole.Oracle

/-- The operations a program may use, on values of type `α`. -/
structure Arith (α : Type) where
  add : α → α → α
  sub : α → α → α
  mul : α → α → α
  div : α → α → α
  neg : α → α
  abs : α → α
  lt : α → α → Bool
  le : α → α → Bool
  eq : α → α → Bool
  zero : α
  one : α
  two : α
  three : α

/-- Exact arithmetic on the rational numbers. -/
def Arith.exact : Arith ℚ where
  add x y := x + y
  sub x y := x - y
  mul x y := x * y
  div x y := x / y
  neg x := -x
  abs x := |x|
  lt x y := decide (x < y)
  le x y := decide (x ≤ y)
  eq x y := decide (x = y)
  zero := 0
  one := 1
  two := 2
  three := 3

/-! ### The model of `f64` -/

/-- An `f64` value. -/
inductive F64 where
  /-- A finite value. Only the values that `F64.round` returns occur. -/
  | fin (q : ℚ)
  /-- An infinity. -/
  | inf (negative : Bool)
  /-- A NaN. -/
  | nan

/-- `2 ^ e` for an integer `e`. -/
def pow2 (e : ℤ) : ℚ :=
  if 0 ≤ e then ((2 ^ e.toNat : ℕ) : ℚ) else mkRat 1 (2 ^ (-e).toNat)

/-- The integer nearest to `q ≥ 0`, the even one of the two if `q` is half way
between them. -/
def roundEven (q : ℚ) : ℕ :=
  let floor := q.num.natAbs / q.den
  let rest := q - floor
  if rest < 1 / 2 then floor
  else if 1 / 2 < rest then floor + 1
  else if floor % 2 = 0 then floor
  else floor + 1

/-- The `f64` nearest to `q`: what an operation with the exact result `q`
returns.

A number of magnitude in `[2 ^ e, 2 ^ (e + 1))` is rounded to a multiple of
`2 ^ (e - 52)`, which leaves 53 significant bits. Below `2 ^ -1022` the
spacing stays `2 ^ -1074` (subnormal numbers), and a result of `2 ^ 1024` or
more is an infinity. -/
def F64.round (q : ℚ) : F64 :=
  if q = 0 then .fin 0
  else
    let a := |q|
    -- `2 ^ (e₀ - 1) < a < 2 ^ (e₀ + 1)`.
    let e₀ : ℤ := (a.num.natAbs.log2 : ℤ) - (a.den.log2 : ℤ)
    let e := if a < pow2 e₀ then e₀ - 1 else e₀
    let spacing := pow2 (max e (-1022) - 52)
    let r := roundEven (a / spacing) * spacing
    if pow2 1024 ≤ r then .inf (decide (q < 0))
    else .fin (if q < 0 then -r else r)

def F64.neg : F64 → F64
  | .fin x => .fin (-x)
  | .inf n => .inf (!n)
  | .nan => .nan

def F64.abs : F64 → F64
  | .fin x => .fin |x|
  | .inf _ => .inf false
  | .nan => .nan

def F64.add : F64 → F64 → F64
  | .fin x, .fin y => .round (x + y)
  | .inf n, .inf m => if n == m then .inf n else .nan
  | .inf n, .fin _ => .inf n
  | .fin _, .inf n => .inf n
  | _, _ => .nan

def F64.sub (x y : F64) : F64 :=
  x.add y.neg

def F64.mul : F64 → F64 → F64
  | .fin x, .fin y => .round (x * y)
  | .inf n, .inf m => .inf (n != m)
  | .inf n, .fin y => if y = 0 then .nan else .inf (n != decide (y < 0))
  | .fin x, .inf n => if x = 0 then .nan else .inf (n != decide (x < 0))
  | _, _ => .nan

def F64.div : F64 → F64 → F64
  -- Not modelled: `x / 0` for `x ≠ 0` is an infinity in `f64`.
  | .fin x, .fin y => if y = 0 then .nan else .round (x / y)
  | .fin _, .inf _ => .fin 0
  | .inf n, .fin y => .inf (n != decide (y < 0))
  | _, _ => .nan

/-- `x < y`. False if either is a NaN. -/
def F64.lt : F64 → F64 → Bool
  | .fin x, .fin y => decide (x < y)
  | .fin _, .inf n => !n
  | .inf n, .fin _ => n
  | .inf n, .inf m => n && !m
  | _, _ => false

/-- `x ≤ y`. False if either is a NaN. -/
def F64.le : F64 → F64 → Bool
  | .fin x, .fin y => decide (x ≤ y)
  | .fin _, .inf n => !n
  | .inf n, .fin _ => n
  | .inf n, .inf m => n || !m
  | _, _ => false

/-- `x == y`. False if either is a NaN. -/
def F64.eq : F64 → F64 → Bool
  | .fin x, .fin y => decide (x = y)
  | .inf n, .inf m => n == m
  | _, _ => false

/-- `f64` arithmetic. -/
def Arith.f64 : Arith F64 where
  add := F64.add
  sub := F64.sub
  mul := F64.mul
  div := F64.div
  neg := F64.neg
  abs := F64.abs
  lt := F64.lt
  le := F64.le
  eq := F64.eq
  zero := .fin 0
  one := .fin 1
  two := .fin 2
  three := .fin 3

/-- How a value is written in an answer: a fraction, `inf`, `-inf` or `nan`. -/
def F64.toLine : F64 → String
  | .fin q => s!"{q.num}/{q.den}"
  | .inf false => "inf"
  | .inf true => "-inf"
  | .nan => "nan"

/-- The operations that can be asked for by name, to compare them with those
of Rust. -/
def f64Operations : List (String × (F64 → F64 → F64)) :=
  [("f64.add", F64.add), ("f64.sub", F64.sub), ("f64.mul", F64.mul), ("f64.div", F64.div)]

end Thole.Oracle
