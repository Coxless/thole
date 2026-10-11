/-
The bisection method for root finding.

Rust counterpart: `thole_roots::bisect` in `../../../src/` (not implemented yet).
-/
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace Thole.Roots

/-- `f` takes values of opposite (weak) sign at `a` and `b`.

This is the precondition of bisection. It allows `f a = 0` or `f b = 0`. -/
def SignChange (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  f a * f b ≤ 0

/-- One bisection step on the bracket `p = (lo, hi)`: evaluate `f` at the
midpoint and keep the half on which the sign change is known to persist. -/
noncomputable def bisectStep (f : ℝ → ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  if f p.1 * f ((p.1 + p.2) / 2) ≤ 0 then (p.1, (p.1 + p.2) / 2) else ((p.1 + p.2) / 2, p.2)

/-- The bracket after `n` bisection steps starting from `(a, b)`. -/
noncomputable def bisect (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) : ℝ × ℝ :=
  (bisectStep f)^[n] (a, b)

/-- The approximation returned after `n` steps: the midpoint of the bracket. -/
noncomputable def bisectMid (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) : ℝ :=
  ((bisect f a b n).1 + (bisect f a b n).2) / 2

variable {f : ℝ → ℝ} {a b : ℝ}

@[simp]
theorem bisect_zero (f : ℝ → ℝ) (a b : ℝ) : bisect f a b 0 = (a, b) :=
  rfl

theorem bisect_succ (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) :
    bisect f a b (n + 1) = bisectStep f (bisect f a b n) :=
  Function.iterate_succ_apply' _ _ _

/-! ### A single step -/

/-- A step halves the width of the bracket. -/
theorem bisectStep_width (f : ℝ → ℝ) (p : ℝ × ℝ) :
    (bisectStep f p).2 - (bisectStep f p).1 = (p.2 - p.1) / 2 := by
  unfold bisectStep
  split_ifs <;> simp only <;> ring

/-- A step stays inside the bracket it was given. -/
theorem bisectStep_nested (f : ℝ → ℝ) {p : ℝ × ℝ} (h : p.1 ≤ p.2) :
    p.1 ≤ (bisectStep f p).1 ∧ (bisectStep f p).1 ≤ (bisectStep f p).2 ∧
      (bisectStep f p).2 ≤ p.2 := by
  unfold bisectStep
  split_ifs <;> simp only <;> refine ⟨?_, ?_, ?_⟩ <;> linarith

/-- A step preserves the sign change. -/
theorem bisectStep_signChange {p : ℝ × ℝ} (h : SignChange f p.1 p.2) :
    SignChange f (bisectStep f p).1 (bisectStep f p).2 := by
  unfold SignChange at *
  unfold bisectStep
  split_ifs with hm
  · exact hm
  · -- `f lo` and `f mid` have the same strict sign, so `f mid` and `f hi` do not.
    simp only
    have hm : 0 < f p.1 * f ((p.1 + p.2) / 2) := not_le.mp hm
    by_contra hc
    have hc : 0 < f ((p.1 + p.2) / 2) * f p.2 := not_le.mp hc
    have hsq : 0 ≤ f ((p.1 + p.2) / 2) ^ 2 := sq_nonneg _
    nlinarith [mul_pos hm hc, mul_nonneg_iff.mpr (Or.inr ⟨h, neg_nonpos.mpr hsq⟩)]

/-! ### `n` steps -/

/-- After `n` steps the bracket has width `(b - a) / 2 ^ n`. -/
theorem bisect_width (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) :
    (bisect f a b n).2 - (bisect f a b n).1 = (b - a) / 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [bisect_succ, bisectStep_width, ih, pow_succ]; ring

/-- Every bracket is a well-formed interval inside the initial one. -/
theorem bisect_nested (f : ℝ → ℝ) (hab : a ≤ b) (n : ℕ) :
    a ≤ (bisect f a b n).1 ∧ (bisect f a b n).1 ≤ (bisect f a b n).2 ∧
      (bisect f a b n).2 ≤ b := by
  induction n with
  | zero => simp [hab]
  | succ n ih =>
    obtain ⟨h₁, h₂, h₃⟩ := ih
    obtain ⟨k₁, k₂, k₃⟩ := bisectStep_nested f h₂
    rw [bisect_succ]
    exact ⟨h₁.trans k₁, k₂, k₃.trans h₃⟩

/-- Every bracket has the sign change. -/
theorem bisect_signChange (h : SignChange f a b) (n : ℕ) :
    SignChange f (bisect f a b n).1 (bisect f a b n).2 := by
  induction n with
  | zero => exact h
  | succ n ih => rw [bisect_succ]; exact bisectStep_signChange ih

/-! ### Roots -/

/-- A continuous function with a sign change on `[a, b]` has a root there.
This is the intermediate value theorem in the form bisection needs. -/
theorem exists_root_of_signChange (hab : a ≤ b) (hf : ContinuousOn f (Set.Icc a b))
    (h : SignChange f a b) : ∃ x ∈ Set.Icc a b, f x = 0 := by
  unfold SignChange at h
  rcases le_total (f a) 0 with ha | ha
  · rcases le_total 0 (f b) with hb | hb
    · exact intermediate_value_Icc hab hf ⟨ha, hb⟩
    · -- both values are `≤ 0` and their product is `≤ 0`, so one of them is `0`
      rcases mul_eq_zero.mp (le_antisymm h (mul_nonneg_of_nonpos_of_nonpos ha hb)) with h0 | h0
      · exact ⟨a, Set.left_mem_Icc.mpr hab, h0⟩
      · exact ⟨b, Set.right_mem_Icc.mpr hab, h0⟩
  · rcases le_total (f b) 0 with hb | hb
    · exact intermediate_value_Icc' hab hf ⟨hb, ha⟩
    · rcases mul_eq_zero.mp (le_antisymm h (mul_nonneg ha hb)) with h0 | h0
      · exact ⟨a, Set.left_mem_Icc.mpr hab, h0⟩
      · exact ⟨b, Set.right_mem_Icc.mpr hab, h0⟩

/-- **Bracketing.** Under the preconditions of bisection, the bracket after
any number of steps contains a root of `f`. -/
theorem bisect_exists_root (hab : a ≤ b) (hf : ContinuousOn f (Set.Icc a b))
    (h : SignChange f a b) (n : ℕ) :
    ∃ x ∈ Set.Icc (bisect f a b n).1 (bisect f a b n).2, f x = 0 := by
  obtain ⟨h₁, h₂, h₃⟩ := bisect_nested f hab n
  exact exists_root_of_signChange h₂ (hf.mono (Set.Icc_subset_Icc h₁ h₃)) (bisect_signChange h n)

/-- **Error bound.** Under the preconditions of bisection, the midpoint after
`n` steps is within `(b - a) / 2 ^ (n + 1)` of a root of `f` in `[a, b]`. -/
theorem bisectMid_error (hab : a ≤ b) (hf : ContinuousOn f (Set.Icc a b))
    (h : SignChange f a b) (n : ℕ) :
    ∃ x ∈ Set.Icc a b, f x = 0 ∧ |bisectMid f a b n - x| ≤ (b - a) / 2 ^ (n + 1) := by
  obtain ⟨x, ⟨hx₁, hx₂⟩, hx⟩ := bisect_exists_root hab hf h n
  obtain ⟨h₁, -, h₃⟩ := bisect_nested f hab n
  refine ⟨x, ⟨h₁.trans hx₁, hx₂.trans h₃⟩, hx, ?_⟩
  have hw := bisect_width f a b n
  have : (b - a) / 2 ^ (n + 1) = ((bisect f a b n).2 - (bisect f a b n).1) / 2 := by
    rw [hw, pow_succ]; ring
  rw [this, bisectMid, abs_le]
  constructor <;> linarith

/-- **Convergence.** Any accuracy `ε > 0` is reached after finitely many
steps: from some step on, the midpoint is within `ε` of a root. -/
theorem bisectMid_converges (hab : a ≤ b) (hf : ContinuousOn f (Set.Icc a b))
    (h : SignChange f a b) {ε : ℝ} (hε : 0 < ε) :
    ∃ N, ∀ n ≥ N, ∃ x ∈ Set.Icc a b, f x = 0 ∧ |bisectMid f a b n - x| < ε := by
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos hε (by linarith : (0:ℝ) < b - a + 1))
    (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨x, hx, hfx, hb⟩ := bisectMid_error hab hf h n
  refine ⟨x, hx, hfx, hb.trans_lt ?_⟩
  have hpos : (0 : ℝ) < b - a + 1 := by linarith
  have h2 : (1 / 2 : ℝ) ^ (n + 1) ≤ (1 / 2) ^ N :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have h3 : (1 / 2 : ℝ) ^ (n + 1) < ε / (b - a + 1) := h2.trans_lt hN
  have h4 : (1 / 2 : ℝ) ^ (n + 1) * (b - a + 1) < ε := (lt_div_iff₀ hpos).mp h3
  have h5 : (b - a) / 2 ^ (n + 1) = (1 / 2 : ℝ) ^ (n + 1) * (b - a) := by
    rw [one_div, inv_pow]; ring
  have h6 : (0 : ℝ) < (1 / 2) ^ (n + 1) := by positivity
  rw [h5]
  nlinarith
