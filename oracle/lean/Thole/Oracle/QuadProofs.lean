/-
With exact arithmetic, the programs of `GaussLegendre.lean` and
`GaussKronrod.lean` are the specification.

This file proves that over `ℚ`, with exact operations:

- the recurrence, the derivative, the weight, the Newton step for a node and
  the rule of `GaussLegendre.lean` are those of
  `Thole/Quad/GaussLegendre/Defs.lean`;
- the estimate over a subinterval, the sums, the choice of the subinterval to
  halve and the halving of `GaussKronrod.lean` are those of
  `Thole/Quad/GaussKronrod/Defs.lean`, and when the loop returns an integral
  it returns the estimates of `Thole.Quad.gk` after some number of halvings,
  at which `gkDone` holds.

The initial guesses of the nodes (`cosG`) have no counterpart: they decide
where Newton's method starts, not what a node is.

Nothing here is linked into the oracle executable.
-/
import Thole.Oracle.GaussLegendre
import Thole.Oracle.GaussKronrod
import Mathlib.Tactic.Ring

namespace Thole.Oracle

open Thole.Quad

/-! ### Gauss-Legendre -/

theorem legendreStepG_exact (x : ℚ) (k : ℕ) (p : ℚ × ℚ) :
    legendreStepG .exact x k p = legendreStep x k p := by
  simp only [legendreStepG, legendreStep, natG, Arith.exact]

theorem legendrePair_foldl (x : ℚ) (m s : ℕ) :
    (List.range' s m).foldl (fun p k => legendreStep x k p) (legendrePair x s) =
      legendrePair x (s + m) := by
  induction m generalizing s with
  | zero => rfl
  | succ m ih =>
    rw [List.range'_succ, List.foldl_cons]
    have : legendreStep x s (legendrePair x s) = legendrePair x (s + 1) := rfl
    rw [this, ih (s + 1)]
    congr 1
    omega

theorem legendrePair_one (x : ℚ) : legendrePair x 1 = (1, x) := by
  simp [legendrePair, legendreStep]

theorem legendrePairG_exact (n : ℕ) (hn : 1 ≤ n) (x : ℚ) :
    legendrePairG .exact n x = legendrePair x n := by
  have h : (fun p k => legendreStepG .exact x k p) = fun p k => legendreStep x k p := by
    funext p k
    exact legendreStepG_exact x k p
  have hstart : ((Arith.exact).one, x) = legendrePair x 1 := by
    rw [legendrePair_one]
    rfl
  rw [legendrePairG, h, hstart, legendrePair_foldl]
  congr 1
  omega

theorem legendreDerivG_exact (n : ℕ) (hn : 1 ≤ n) (x : ℚ) :
    legendreDerivG .exact n x = legendreDeriv n x := by
  simp only [legendreDerivG, legendrePairG_exact n hn, legendreDeriv, natG, Arith.exact]

theorem weightG_exact (n : ℕ) (hn : 1 ≤ n) (x : ℚ) : weightG .exact n x = gaussWeight n x := by
  simp only [weightG, legendreDerivG_exact n hn, gaussWeight, Arith.exact]

/-- A Newton step for a node is `gaussNodeStep`, which is
`Thole.Roots.newtonStep` on `legendre` and `legendreDeriv`. -/
theorem nodeStepG_exact (n : ℕ) (hn : 1 ≤ n) (x : ℚ) :
    (nodeStepG .exact n x).2 = gaussNodeStep n x := by
  simp only [nodeStepG, legendrePairG_exact n hn, legendreDerivG_exact n hn, gaussNodeStep,
    Thole.Roots.newtonStep, legendre, Arith.exact]

theorem foldlM_ok {β γ ε : Type} (g : β → γ → Except ε β) (h : β → γ → β)
    (hg : ∀ b c, g b c = .ok (h b c)) (l : List γ) (init : β) :
    l.foldlM g init = .ok (l.foldl h init) := by
  induction l generalizing init with
  | nil => rfl
  | cons c l ih =>
    rw [List.foldlM_cons, hg, List.foldl_cons]
    exact ih _

/-- `GaussLegendre::integrate` is `rule`. -/
theorem integrateG_exact (xs ws : List ℚ) (f : ℚ → ℚ) (a b : ℚ) :
    integrateG .exact xs ws f a b = .ok (rule xs ws f a b) := by
  simp only [integrateG, Arith.exact, if_true]
  rw [foldlM_ok _ (fun acc (p : ℚ × ℚ) => acc + p.2 * f (a / 2 + b / 2 + (b / 2 - a / 2) * p.1))
    (fun _ _ => rfl)]
  rfl

/-! ### Gauss-Kronrod -/

variable (xgk wgk wg : List ℚ) (f tol : ℚ → ℚ)

theorem segmentG_exact (a b : ℚ) :
    segmentG .exact xgk wgk wg f a b = .ok (mkSegment (kronrodEstimate xgk wgk wg f) a b) := by
  simp only [segmentG, evalG, Arith.exact, if_true]
  rw [foldlM_ok _ (fun (kg : ℚ × ℚ) j =>
      (kg.1 + wgk.getD j 0 * (f (a / 2 + b / 2 - (b / 2 - a / 2) * xgk.getD j 0) +
          f (a / 2 + b / 2 + (b / 2 - a / 2) * xgk.getD j 0)),
        if j % 2 = 1 then kg.2 + wg.getD (j / 2) 0 * (f (a / 2 + b / 2 - (b / 2 - a / 2) *
          xgk.getD j 0) + f (a / 2 + b / 2 + (b / 2 - a / 2) * xgk.getD j 0)) else kg.2))
    (fun _ _ => rfl)]
  rfl

theorem totalsG_foldl (ss : List (Segment ℚ)) (v e : ℚ) :
    ss.foldl (fun acc s => ((Arith.exact).add acc.1 s.value, (Arith.exact).add acc.2 s.error))
        (v, e) =
      (ss.foldl (fun acc s => acc + s.value) v, ss.foldl (fun acc s => acc + s.error) e) := by
  induction ss generalizing v e with
  | nil => rfl
  | cons s ss ih => exact ih _ _

theorem totalsG_exact (ss : List (Segment ℚ)) :
    totalsG .exact ss = (totalValue ss, totalError ss) :=
  totalsG_foldl ss 0 0

theorem worstFromG_exact (ss : List (Segment ℚ)) (i best : ℕ) (e : ℚ) :
    worstFromG .exact ss i best e = worstFrom ss i best e := by
  induction ss generalizing i best e with
  | nil => rfl
  | cons s ss ih =>
    simp only [worstFromG, worstFrom, Arith.exact, decide_eq_true_eq]
    split <;> exact ih _ _ _

theorem worstG_exact (ss : List (Segment ℚ)) : worstG .exact ss = worstIndex ss := by
  cases ss with
  | nil => rfl
  | cons s ss => exact worstFromG_exact ss 1 0 s.error

theorem splitG_exact (ss : List (Segment ℚ)) (i : ℕ) :
    splitG .exact xgk wgk wg f ss i = .ok (split (kronrodEstimate xgk wgk wg f) ss i) := by
  unfold splitG split
  split
  · rfl
  · simp only [Arith.exact, segmentG_exact]
    rfl

/-- **The loop is the specification.** With exact arithmetic, when the loop
started from the subintervals after `m` halvings returns an integral, it
returns the estimates after some number `n` of halvings, the number of
subintervals there, and the stopping test `gkDone` holds there. -/
theorem runGkG_exact (a b : ℚ) (maxSub fuel m : ℕ) {v e : ℚ} {k : ℕ}
    (h : runGkG .exact xgk wgk wg f tol maxSub fuel
      (gk (kronrodEstimate xgk wgk wg f) a b m) = .integral v e k) :
    ∃ n, v = totalValue (gk (kronrodEstimate xgk wgk wg f) a b n) ∧
      e = totalError (gk (kronrodEstimate xgk wgk wg f) a b n) ∧
      k = (gk (kronrodEstimate xgk wgk wg f) a b n).length ∧
      gkDone tol (gk (kronrodEstimate xgk wgk wg f) a b n) := by
  induction fuel generalizing m with
  | zero =>
    unfold runGkG at h
    simp only [totalsG_exact, Arith.exact, decide_eq_true_eq] at h
    split_ifs at h with h₁
    · injection h with hv he hk
      exact ⟨m, hv.symm, he.symm, hk.symm, h₁⟩
  | succ fuel ih =>
    unfold runGkG at h
    simp only [totalsG_exact, Arith.exact, decide_eq_true_eq] at h
    split_ifs at h with h₁ h₂
    · injection h with hv he hk
      exact ⟨m, hv.symm, he.symm, hk.symm, h₁⟩
    · have hs := splitG_exact xgk wgk wg f (gk (kronrodEstimate xgk wgk wg f) a b m)
        (worstG .exact (gk (kronrodEstimate xgk wgk wg f) a b m))
      simp only [Arith.exact] at hs
      rw [hs, worstG_exact] at h
      have hstep : split (kronrodEstimate xgk wgk wg f) (gk (kronrodEstimate xgk wgk wg f) a b m)
          (worstIndex (gk (kronrodEstimate xgk wgk wg f) a b m)) =
          gk (kronrodEstimate xgk wgk wg f) a b (m + 1) := by
        simp only [gk, Function.iterate_succ_apply', gkStep]
      rw [hstep] at h
      exact ih (m + 1) h

/-- The whole call: an integral that it returns satisfies `runGkG_exact`. -/
theorem gkCallG_exact (a b : ℚ) (maxSub : ℕ) {v e : ℚ} {k : ℕ}
    (h : gkCallG .exact xgk wgk wg f tol a b maxSub =
      .integral v e k) :
    ∃ n, v = totalValue (gk (kronrodEstimate xgk wgk wg f) a b n) ∧
      e = totalError (gk (kronrodEstimate xgk wgk wg f) a b n) ∧
      k = (gk (kronrodEstimate xgk wgk wg f) a b n).length ∧
      gkDone tol (gk (kronrodEstimate xgk wgk wg f) a b n) := by
  unfold gkCallG at h
  rw [segmentG_exact] at h
  exact runGkG_exact xgk wgk wg f tol a b maxSub maxSub 0 h

end Thole.Oracle
