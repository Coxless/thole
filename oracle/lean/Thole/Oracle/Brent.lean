/-
Brent's method as a sequence of operations, over any arithmetic.

Rust counterpart: `thole_roots::brent` in `crates/thole-roots/src/brent.rs`.

Each definition here follows the Rust code operation by operation, in the
order in which Rust evaluates them, because rounding depends on that order.
`BrentProofs.lean` proves that with exact arithmetic they are the definitions
of `Thole/Roots/Brent/Defs.lean`, the ones the theorems are about. With `f64`
arithmetic they are what the Rust code computes, and `checkBrentSpec` in
`Roots.lean` requires the Rust code to return exactly that.

| Here            | `Brent/Defs.lean`   | Rust                    |
|-----------------|---------------------|-------------------------|
| `halfG`         | `BrentState.half`   | `State::half`           |
| `orderG`        | `brentOrder`        | `State::order`          |
| `initG`         | `brentInit`         | the state before `loop` |
| `doneG`         | `brentDone`         | the stopping test       |
| `interpG`       | `brentInterp`       | `State::interp`         |
| `trialG`        | `brentTrial`        | `State::trial`          |
| `shiftG`        | `brentShift`        | `shift`                 |
| `nextG`         | `brentNext`         | `next`                  |
| `signChangeG`   | `SignChange`        | `sign_change`           |
| `stepG`         | `brentStep`         | the body of `loop`      |
| `brentG`        | `brent`             | the state after `n` steps |
| `hornerG`       | `horner`            | `Poly::eval`            |
| `brentTolG`     | `tol`               | `tol.bound(cur) / 2.0`  |

Where the Rust code deviates from `Brent/Defs.lean` for floating-point
reasons, so do these: `halfG` halves before it subtracts, and `signChangeG`
compares signs.
-/
import Thole.Oracle.Arith
import Thole.Roots.Brent.Defs

namespace Thole.Oracle

open Thole.Roots

variable {α : Type} (A : Arith α)

/-- `Poly::eval`: Horner's rule, from the highest degree. -/
def hornerG (coeffs : List α) (x : α) : α :=
  coeffs.foldr (fun c acc => A.add (A.mul acc x) c) A.zero

/-- The tolerance the Rust code passes to the iteration:
`(abs + rel * |x|) / 2`. -/
def brentTolG (abs rel x : α) : α :=
  A.div (A.add abs (A.mul rel (A.abs x))) A.two

/-- `contra / 2 - cur / 2`. -/
def halfG (s : BrentState α) : α :=
  A.sub (A.div s.contra A.two) (A.div s.cur A.two)

def orderG (f : α → α) (s : BrentState α) : BrentState α :=
  if A.lt (A.abs (f s.contra)) (A.abs (f s.cur)) then
    { s with prev := s.cur, cur := s.contra, contra := s.cur }
  else s

def initG (f : α → α) (a b : α) : BrentState α :=
  orderG A f ⟨a, b, a, A.sub b a, A.sub b a⟩

def doneG (f : α → α) (tol : α → α) (s : BrentState α) : Bool :=
  A.eq (f s.cur) A.zero || A.le (A.abs (halfG A s)) (tol s.cur)

def interpG (f : α → α) (s : BrentState α) : α × α :=
  if A.eq s.prev s.contra then
    (A.mul (A.mul A.two (halfG A s)) (A.div (f s.cur) (f s.prev)),
      A.sub A.one (A.div (f s.cur) (f s.prev)))
  else
    (A.mul (A.div (f s.cur) (f s.prev))
        (A.sub
          (A.mul (A.mul (A.mul A.two (halfG A s)) (A.div (f s.prev) (f s.contra)))
            (A.sub (A.div (f s.prev) (f s.contra)) (A.div (f s.cur) (f s.contra))))
          (A.mul (A.sub s.cur s.prev) (A.sub (A.div (f s.cur) (f s.contra)) A.one))),
      A.mul
        (A.mul (A.sub (A.div (f s.prev) (f s.contra)) A.one)
          (A.sub (A.div (f s.cur) (f s.contra)) A.one))
        (A.sub (A.div (f s.cur) (f s.prev)) A.one))

/-- `p` of the interpolation step after the sign normalization. -/
def pG (f : α → α) (s : BrentState α) : α :=
  A.abs (interpG A f s).1

/-- `q` of the interpolation step after the sign normalization. -/
def qG (f : α → α) (s : BrentState α) : α :=
  if A.lt A.zero (interpG A f s).1 then A.neg (interpG A f s).2 else (interpG A f s).2

def trialG (f : α → α) (tol : α → α) (s : BrentState α) : α × α :=
  if A.lt (A.abs s.e) (tol s.cur) || A.le (A.abs (f s.prev)) (A.abs (f s.cur)) then
    (halfG A s, halfG A s)
  else if
      A.lt (A.mul A.two (pG A f s))
          (A.sub (A.mul (A.mul A.three (halfG A s)) (qG A f s))
            (A.abs (A.mul (tol s.cur) (qG A f s)))) &&
        A.lt (pG A f s) (A.abs (A.div (A.mul s.e (qG A f s)) A.two)) then
    (A.div (pG A f s) (qG A f s), s.d)
  else (halfG A s, halfG A s)

def shiftG (τ m d : α) : α :=
  if A.lt τ (A.abs d) then d else if A.lt A.zero m then τ else A.neg τ

def nextG (f : α → α) (tol : α → α) (s : BrentState α) : α :=
  A.add s.cur (shiftG A (tol s.cur) (halfG A s) (trialG A f tol s).1)

/-- `sign_change`: opposite signs, or a zero. -/
def signChangeG (u v : α) : Bool :=
  A.eq u A.zero || A.eq v A.zero || (A.lt u A.zero != A.lt v A.zero)

def stepG (f : α → α) (tol : α → α) (s : BrentState α) : BrentState α :=
  if doneG A f tol s then s
  else
    orderG A f
      (if signChangeG A (f (nextG A f tol s)) (f s.contra) then
        ⟨s.cur, nextG A f tol s, s.contra, (trialG A f tol s).1, (trialG A f tol s).2⟩
      else
        ⟨s.cur, nextG A f tol s, s.cur, A.sub (nextG A f tol s) s.cur,
          A.sub (nextG A f tol s) s.cur⟩)

def brentG (f : α → α) (tol : α → α) (a b : α) (n : ℕ) : BrentState α :=
  (stepG A f tol)^[n] (initG A f a b)

/-- Runs the loop of the Rust code from the state `s`, reached after `steps`
steps, with `fuel` steps left before the iteration limit. Returns whether the
stopping test held, the number of steps taken and the last state, which is
`brentG` of that number. -/
def runG (f : α → α) (tol : α → α) : ℕ → ℕ → BrentState α → Bool × ℕ × BrentState α
  | 0, steps, s => (doneG A f tol s, steps, s)
  | fuel + 1, steps, s =>
    if doneG A f tol s then (true, steps, s) else runG f tol fuel (steps + 1) (stepG A f tol s)

end Thole.Oracle
