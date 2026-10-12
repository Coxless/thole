/-
With exact arithmetic, the program of `Brent.lean` is the specification.

`Brent.lean` writes Brent's method as the sequence of operations of the Rust
code, over any arithmetic. This file proves that over `ℚ`, with exact
operations, each of its definitions is the definition of the same name in
`Thole/Roots/Brent/Defs.lean`. The theorems of `Thole/Roots/Brent.lean` are
about those, stated over `ℝ`; the definitions themselves are the same over any
ordered field.

So the program that the oracle runs in `f64` arithmetic, and that the Rust
code must agree with bit for bit, differs from the proved specification in
nothing but the rounding of each operation.

Nothing here is linked into the oracle executable.
-/
import Thole.Oracle.Brent
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace Thole.Oracle

open Thole.Roots

variable (f tol : ℚ → ℚ) (s : BrentState ℚ)

theorem halfG_exact : halfG .exact s = s.half := by
  simp only [halfG, Arith.exact, BrentState.half]
  ring

theorem orderG_exact : orderG .exact f s = brentOrder f s := by
  simp only [orderG, brentOrder, Arith.exact, decide_eq_true_eq]

theorem initG_exact (a b : ℚ) : initG .exact f a b = brentInit f a b := by
  simp only [initG, orderG_exact]
  simp only [brentInit, Arith.exact]

theorem doneG_exact : doneG .exact f tol s = decide (brentDone f tol s) := by
  simp only [doneG, halfG_exact]
  simp only [Arith.exact]
  rw [Bool.eq_iff_iff, Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq]
  exact decide_eq_true_iff.symm

theorem interpG_exact : interpG .exact f s = brentInterp f s := by
  simp only [interpG, halfG_exact]
  simp only [brentInterp, Arith.exact, decide_eq_true_eq]

theorem pG_exact : pG .exact f s = brentP f s := by
  simp only [pG, interpG_exact]
  simp only [brentP, Arith.exact]

theorem qG_exact : qG .exact f s = brentQ f s := by
  simp only [qG, interpG_exact]
  simp only [brentQ, Arith.exact, decide_eq_true_eq]

theorem trialG_exact : trialG .exact f tol s = brentTrial f tol s := by
  simp only [trialG, halfG_exact, pG_exact, qG_exact]
  simp only [brentTrial, Arith.exact, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]

theorem shiftG_exact (τ m d : ℚ) : shiftG .exact τ m d = brentShift τ m d := by
  simp only [shiftG, brentShift, Arith.exact, decide_eq_true_eq]

theorem nextG_exact : nextG .exact f tol s = brentNext f tol s := by
  simp only [nextG, shiftG_exact, halfG_exact, trialG_exact]
  simp only [brentNext, Arith.exact]

/-- Comparing signs is the same as testing the sign of the product. -/
theorem mul_nonpos_iff_sign (u v : ℚ) : u * v ≤ 0 ↔ u = 0 ∨ v = 0 ∨ ¬(u < 0 ↔ v < 0) := by
  rcases lt_trichotomy u 0 with hu | hu | hu
  · rcases lt_trichotomy v 0 with hv | hv | hv
    · have := mul_pos_of_neg_of_neg hu hv
      simp [hu, hv, hu.ne, hv.ne, not_le.mpr this]
    · simp [hv]
    · have := mul_neg_of_neg_of_pos hu hv
      simp [hu, hv.ne', not_lt.mpr hv.le, this.le]
  · simp [hu]
  · rcases lt_trichotomy v 0 with hv | hv | hv
    · have := mul_neg_of_pos_of_neg hu hv
      simp [hv, not_lt.mpr hu.le, this.le]
    · simp [hv]
    · have := mul_pos hu hv
      simp [hu.ne', hv.ne', not_lt.mpr hu.le, not_lt.mpr hv.le, not_le.mpr this]

theorem signChangeG_exact (u v : ℚ) : signChangeG .exact u v = decide (u * v ≤ 0) := by
  rw [Bool.eq_iff_iff]
  simp [signChangeG, Arith.exact, mul_nonpos_iff_sign, or_assoc]

theorem stepG_exact : stepG .exact f tol s = brentStep f tol s := by
  simp only [stepG, doneG_exact, orderG_exact, signChangeG_exact, nextG_exact, trialG_exact]
  simp only [brentStep, Arith.exact, decide_eq_true_eq]

/-- **The program is the specification.** After any number of steps, the
program of `Brent.lean` with exact arithmetic is in the state that
`Thole.Roots.brent` defines. -/
theorem brentG_exact (a b : ℚ) (n : ℕ) : brentG .exact f tol a b n = brent f tol a b n := by
  have h : stepG .exact f tol = brentStep f tol := funext (stepG_exact f tol)
  simp only [brentG, brent, initG_exact, h]

/-- The loop of the Rust code, as `runG` writes it, takes the steps of
`brentG`: started from the state after `steps` steps, it ends in the state
after the number of steps that it reports, and it reports whether the
stopping test holds there. -/
theorem runG_eq {α : Type} (A : Arith α) (f tol : α → α) (a b : α) (fuel steps : ℕ) :
    (runG A f tol fuel steps (brentG A f tol a b steps)).2.2 =
        brentG A f tol a b (runG A f tol fuel steps (brentG A f tol a b steps)).2.1 ∧
      (runG A f tol fuel steps (brentG A f tol a b steps)).1 =
        doneG A f tol (runG A f tol fuel steps (brentG A f tol a b steps)).2.2 := by
  induction fuel generalizing steps with
  | zero => simp [runG]
  | succ fuel ih =>
    have hstep : stepG A f tol (brentG A f tol a b steps) = brentG A f tol a b (steps + 1) := by
      simp only [brentG, Function.iterate_succ_apply']
    by_cases hd : doneG A f tol (brentG A f tol a b steps)
    · simp [runG, hd]
    · simp only [runG, hd, Bool.false_eq_true, ↓reduceIte, hstep]
      exact ih (steps + 1)

end Thole.Oracle
