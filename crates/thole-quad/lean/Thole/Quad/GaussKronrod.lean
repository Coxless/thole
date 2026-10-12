/-
Adaptive Gauss-Kronrod quadrature: the proofs.

Rust counterpart: `thole_quad::gauss_kronrod` in `../../../src/gauss_kronrod.rs`.

The definitions are in `GaussKronrod/Defs.lean`, with the table that maps them
to the Rust code. This file proves, over the real numbers and for any
estimate of the subintegrals:

- `gk_partition`: after any number of halvings the subintervals partition
  `[a, b]`, in order: the first starts at `a`, each one starts where the
  previous one ends, and the last ends at `b`.
- `gk_length`: after `n` halvings there are `n + 1` subintervals, which is how
  the Rust code counts them against the limit.
- `integral_eq_sum`: the integral over `[a, b]` is the sum of the integrals
  over the subintervals of a partition.
- `gk_error_le`: the error of the estimate of the integral is at most the sum
  of the errors over the subintervals.
- `gk_error_le_of_local`: so if the error estimate of every subinterval bounds
  its error, the estimate of the error bounds the error of the estimate.

Not proved, because it is not true in general: that the difference between the
Kronrod and the Gauss estimates bounds the error of the Kronrod estimate. Not
proved either: that the rules are exact for polynomials of degree 22 and 13.
Their constants are rational approximations of irrational numbers, so the
rules with these constants are exact for no degree above 1. The oracle checks
that they are exact up to the rounding of the constants
(`oracle/lean/Thole/Oracle/Quad.lean`).
-/
import Thole.Quad.GaussKronrod.Defs
import Thole.Quad.GaussLegendre
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace Thole.Quad

variable {est : ℝ → ℝ → ℝ × ℝ}

/-- The subintervals `ss` partition `[a, b]` in order. -/
def Partition : List (Segment ℝ) → ℝ → ℝ → Prop
  | [], a, b => a = b
  | s :: ss, a, b => s.a = a ∧ Partition ss s.b b

theorem partition_append (l₁ l₂ : List (Segment ℝ)) (a b : ℝ) :
    Partition (l₁ ++ l₂) a b ↔ ∃ m, Partition l₁ a m ∧ Partition l₂ m b := by
  induction l₁ generalizing a with
  | nil => simp [Partition]
  | cons s l₁ ih =>
    simp only [List.cons_append, Partition, ih]
    constructor
    · rintro ⟨h, m, h₁, h₂⟩; exact ⟨m, ⟨h, h₁⟩, h₂⟩
    · rintro ⟨m, ⟨h, h₁⟩, h₂⟩; exact ⟨h, m, h₁, h₂⟩

/-- Halving a subinterval keeps a partition. -/
theorem partition_split (ss : List (Segment ℝ)) (i : ℕ) {a b : ℝ} (h : Partition ss a b) :
    Partition (split est ss i) a b := by
  unfold split
  split
  · exact h
  · rename_i s hs
    have hi : i < ss.length := (List.getElem?_eq_some_iff.mp hs).1
    have hss : ss = ss.take i ++ [s] ++ ss.drop (i + 1) := by
      rw [List.append_assoc, List.singleton_append, ← (List.getElem?_eq_some_iff.mp hs).2,
        ← List.drop_eq_getElem_cons hi, List.take_append_drop]
    rw [hss, partition_append, partition_append] at h
    obtain ⟨m', ⟨m, h₁, hm⟩, h₃⟩ := h
    simp only [Partition] at hm
    obtain ⟨hsa, rfl⟩ := hm
    rw [partition_append, partition_append]
    refine ⟨s.b, ⟨m, h₁, ?_⟩, h₃⟩
    simp [Partition, mkSegment, hsa]

/-- **Partition.** After any number of halvings, the subintervals partition
`[a, b]` in order. -/
theorem gk_partition (est : ℝ → ℝ → ℝ × ℝ) (a b : ℝ) (n : ℕ) : Partition (gk est a b n) a b := by
  induction n with
  | zero => simp [gk, Partition, mkSegment]
  | succ n ih =>
    rw [gk, Function.iterate_succ_apply']
    exact partition_split _ _ ih

theorem worstFrom_lt (ss : List (Segment ℝ)) (i best : ℕ) (e : ℝ) (hb : best < i) :
    worstFrom ss i best e < i + ss.length := by
  induction ss generalizing i best e with
  | nil => simpa [worstFrom] using hb
  | cons s ss ih =>
    simp only [worstFrom, List.length_cons]
    split
    · have := ih (i + 1) i s.error (by omega); omega
    · have := ih (i + 1) best e (by omega); omega

theorem worstIndex_lt (ss : List (Segment ℝ)) (h : ss ≠ []) : worstIndex ss < ss.length := by
  cases ss with
  | nil => exact absurd rfl h
  | cons s ss =>
    have := worstFrom_lt ss 1 0 s.error (by omega)
    simp only [worstIndex, List.length_cons]
    omega

/-- **Count.** After `n` halvings there are `n + 1` subintervals. -/
theorem gk_length (est : ℝ → ℝ → ℝ × ℝ) (a b : ℝ) (n : ℕ) : (gk est a b n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [gk, Function.iterate_succ_apply']
    rw [gk] at ih
    set ss := (gkStep est)^[n] [mkSegment est a b]
    have hne : ss ≠ [] := by
      intro h; rw [h] at ih; simp at ih
    have hi := worstIndex_lt ss hne
    unfold gkStep split
    rw [List.getElem?_eq_getElem hi]
    simp only [List.length_append, List.length_take, List.length_drop, List.length_cons,
      List.length_nil]
    omega

/-! ### Integrals over a partition -/

variable {f : ℝ → ℝ}

/-- `Σ_s ∫_{s.a}^{s.b} f`. -/
noncomputable def sumIntegrals (f : ℝ → ℝ) (ss : List (Segment ℝ)) : ℝ :=
  (ss.map fun s => ∫ x in s.a..s.b, f x).sum

/-- The integral over `[a, b]` is the sum of the integrals over the
subintervals of a partition. -/
theorem integral_eq_sum (hf : ∀ x y, IntervalIntegrable f MeasureTheory.volume x y) :
    ∀ (ss : List (Segment ℝ)) (a b : ℝ), Partition ss a b →
      ∫ x in a..b, f x = sumIntegrals f ss
  | [], a, b, h => by simp [Partition] at h; simp [h, sumIntegrals]
  | s :: ss, a, b, h => by
    obtain ⟨rfl, h⟩ := h
    rw [sumIntegrals, List.map_cons, List.sum_cons, ← sumIntegrals,
      ← integral_eq_sum hf ss s.b b h,
      intervalIntegral.integral_add_adjacent_intervals (hf _ _) (hf _ _)]

theorem foldl_value (ss : List (Segment ℝ)) (init : ℝ) :
    ss.foldl (fun acc s => acc + s.value) init = init + (ss.map (·.value)).sum := by
  induction ss generalizing init with
  | nil => simp
  | cons s ss ih => rw [List.foldl_cons, ih, List.map_cons, List.sum_cons]; ring

theorem foldl_error (ss : List (Segment ℝ)) (init : ℝ) :
    ss.foldl (fun acc s => acc + s.error) init = init + (ss.map (·.error)).sum := by
  induction ss generalizing init with
  | nil => simp
  | cons s ss ih => rw [List.foldl_cons, ih, List.map_cons, List.sum_cons]; ring

theorem abs_sumIntegrals_sub_le (f : ℝ → ℝ) :
    ∀ ss : List (Segment ℝ), |sumIntegrals f ss - (ss.map (·.value)).sum| ≤
      (ss.map fun s => |(∫ x in s.a..s.b, f x) - s.value|).sum
  | [] => by simp [sumIntegrals]
  | s :: ss => by
    have ih := abs_sumIntegrals_sub_le f ss
    simp only [sumIntegrals, List.map_cons, List.sum_cons] at ih ⊢
    calc |(∫ x in s.a..s.b, f x) + (ss.map fun s => ∫ x in s.a..s.b, f x).sum -
          (s.value + (ss.map (·.value)).sum)|
        = |((∫ x in s.a..s.b, f x) - s.value) +
            ((ss.map fun s => ∫ x in s.a..s.b, f x).sum - (ss.map (·.value)).sum)| := by
          congr 1; ring
      _ ≤ |(∫ x in s.a..s.b, f x) - s.value| +
            |(ss.map fun s => ∫ x in s.a..s.b, f x).sum - (ss.map (·.value)).sum| :=
          abs_add_le _ _
      _ ≤ _ := by gcongr

/-- **Error.** After any number of halvings, the error of the estimate of the
integral is at most the sum of the errors over the subintervals. -/
theorem gk_error_le (hf : ∀ x y, IntervalIntegrable f MeasureTheory.volume x y)
    (est : ℝ → ℝ → ℝ × ℝ) (a b : ℝ) (n : ℕ) :
    |(∫ x in a..b, f x) - totalValue (gk est a b n)| ≤
      ((gk est a b n).map fun s => |(∫ x in s.a..s.b, f x) - s.value|).sum := by
  rw [integral_eq_sum hf _ a b (gk_partition est a b n), totalValue, foldl_value, zero_add]
  exact abs_sumIntegrals_sub_le f _

/-- **Error estimate.** If the error estimate of every subinterval bounds its
error, the estimate of the error bounds the error of the estimate of the
integral. -/
theorem gk_error_le_of_local (hf : ∀ x y, IntervalIntegrable f MeasureTheory.volume x y)
    (est : ℝ → ℝ → ℝ × ℝ) (a b : ℝ) (n : ℕ)
    (hlocal : ∀ s ∈ gk est a b n, |(∫ x in s.a..s.b, f x) - s.value| ≤ s.error) :
    |(∫ x in a..b, f x) - totalValue (gk est a b n)| ≤ totalError (gk est a b n) := by
  refine (gk_error_le hf est a b n).trans ?_
  rw [totalError, foldl_error, zero_add]
  exact List.sum_le_sum hlocal

end Thole.Quad
