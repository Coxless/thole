/-
With exact arithmetic, the program of `Newton.lean` is the specification.

`Newton.lean` writes Newton's method as the sequence of operations of the
Rust code, over any arithmetic. This file proves that over `ℚ`, with exact
operations, its steps are `newtonStep` of `Thole/Roots/Newton/Defs.lean`, and
that when the loop returns a root it returns the approximation `newton` after
the number of steps that it reports, at which `newtonDone` holds. The
theorems of `Thole/Roots/Newton.lean` are about those definitions.

Nothing here is linked into the oracle executable.
-/
import Thole.Oracle.Newton
import Mathlib.Tactic.Ring

namespace Thole.Oracle

open Thole.Roots

variable (f df tol : ℚ → ℚ)

theorem newtonStepG_exact (x : ℚ) :
    newtonStepG .exact f df x = (f x / df x, newtonStep f df x) := by
  simp only [newtonStepG, Arith.exact, newtonStep]

theorem newtonG_exact (x0 : ℚ) (n : ℕ) : newtonG .exact f df x0 n = newton f df x0 n := by
  have h : (fun x => (newtonStepG .exact f df x).2) = newtonStep f df := by
    funext x
    rw [newtonStepG_exact]
  simp only [newtonG, newton, h]

/-- The loop with exact arithmetic and no fuel left. -/
theorem runNewtonG_exact_zero (steps : ℕ) (x step : ℚ) :
    runNewtonG .exact f df tol 0 steps x step =
      if f x = 0 then .root x step steps else .notConverged x := by
  simp [runNewtonG, isNaNG, Arith.exact]

/-- The loop with exact arithmetic: no NaN, no infinity, and the steps of
`newtonStep`. -/
theorem runNewtonG_exact_succ (fuel steps : ℕ) (x step : ℚ) :
    runNewtonG .exact f df tol (fuel + 1) steps x step =
      if f x = 0 then .root x step steps
      else if df x = 0 then .zeroDerivative x
      else if |f x / df x| ≤ tol (newtonStep f df x) then
        .root (newtonStep f df x) (f x / df x) (steps + 1)
      else runNewtonG .exact f df tol fuel (steps + 1) (newtonStep f df x) (f x / df x) := by
  rw [runNewtonG]
  simp only [newtonStepG_exact]
  simp [isNaNG, Arith.exact]

theorem newtonDone_of_zero {x0 : ℚ} {n : ℕ} (h : f (newton f df x0 n) = 0) :
    newtonDone f df tol x0 n := by
  cases n with
  | zero => exact h
  | succ n => exact Or.inl h

/-- **The loop is the specification.** With exact arithmetic, when the loop
started at the approximation after `steps` steps returns a root, the root is
the approximation after the number of steps that it reports, and the stopping
test `newtonDone` holds there. -/
theorem runNewtonG_exact {x0 : ℚ} (fuel steps : ℕ) (step : ℚ) {x s : ℚ} {k : ℕ}
    (h : runNewtonG .exact f df tol fuel steps (newton f df x0 steps) step = .root x s k) :
    x = newton f df x0 k ∧ newtonDone f df tol x0 k := by
  induction fuel generalizing steps step with
  | zero =>
    rw [runNewtonG_exact_zero] at h
    split_ifs at h with h₀
    cases h
    exact ⟨rfl, newtonDone_of_zero f df tol h₀⟩
  | succ fuel ih =>
    rw [runNewtonG_exact_succ] at h
    have hn : newtonStep f df (newton f df x0 steps) = newton f df x0 (steps + 1) :=
      (Function.iterate_succ_apply' _ _ _).symm
    split_ifs at h with h₀ h₁ h₂
    · cases h
      exact ⟨rfl, newtonDone_of_zero f df tol h₀⟩
    · cases h
      refine ⟨hn, Or.inr ?_⟩
      rw [← hn]
      have : newtonStep f df (newton f df x0 steps) - newton f df x0 steps =
          -(f (newton f df x0 steps) / df (newton f df x0 steps)) := by
        unfold newtonStep; ring
      rw [this, abs_neg]
      exact h₂
    · rw [hn] at h
      exact ih (steps + 1) _ h

/-- The call as the Rust code makes it, from `x0` with `maxIter` steps
allowed: a root that it returns satisfies `runNewtonG_exact`. -/
theorem newtonCallG_exact {x0 : ℚ} (maxIter : ℕ) {x s : ℚ} {k : ℕ}
    (h : newtonCallG .exact f df tol x0 maxIter = .root x s k) :
    x = newton f df x0 k ∧ newtonDone f df tol x0 k :=
  runNewtonG_exact f df tol maxIter 0 _ h

end Thole.Oracle
