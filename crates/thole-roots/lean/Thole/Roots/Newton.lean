/-
Newton's method for root finding: the proofs.

Rust counterpart: `thole_roots::newton` in `../../../src/newton.rs`.

The iteration is defined in `Newton/Defs.lean`, over any linearly ordered
field; the table that maps the definitions to the Rust code is there. This
file proves their properties over the real numbers, for a function `f` whose
derivative `df` is Lipschitz continuous with constant `L` and at least `m > 0`
in absolute value, on an interval that the theorems name.

- `newtonStep_error`: one step squares the error, up to the factor
  `L / |df x|`. This is the quadratic convergence of Newton's method.
- `newton_error`: from a starting point within `δ` of a root, where
  `2 * L * δ ≤ m`, the error after `n` steps is at most `|x0 - r| / 2 ^ n`.
- `newtonStep_exists_root`: after a step of length `s`, if `L * s ≤ m` on the
  interval of half-width `s` around the new approximation, a root lies within
  `L * s ^ 2 / m ≤ s` of it. Unlike the other two, this needs no root to be
  known in advance, so it is a guarantee that the stopping test can give.
- `newton_error_of_done`: that guarantee for the stopping test of the Rust
  code (`newtonDone`).

Not proved: Kantorovich's theorem, which gives convergence from conditions at
the starting point alone. It needs the same bounds on a larger interval and a
longer argument, and the Rust code does not rely on it.

The proofs are about the definitions; that the Rust code follows them, and
the effect of floating-point rounding, are what the oracle tests.
-/
import Thole.Roots.Newton.Defs
import Thole.Roots.Bisection
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr

namespace Thole.Roots

variable {f df : ℝ → ℝ} {L m : ℝ}

theorem newton_zero (f df : ℝ → ℝ) (x0 : ℝ) : newton f df x0 0 = x0 :=
  rfl

theorem newton_succ (f df : ℝ → ℝ) (x0 : ℝ) (n : ℕ) :
    newton f df x0 (n + 1) = newtonStep f df (newton f df x0 n) :=
  Function.iterate_succ_apply' _ _ _

/-! ### The linearization error -/

/-- A function that is Lipschitz continuous on a set is continuous there. -/
theorem continuousOn_of_lipschitz {g : ℝ → ℝ} {s : Set ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ y ∈ s, ∀ z ∈ s, |g y - g z| ≤ L * |y - z|) : ContinuousOn g s := by
  rw [Metric.continuousOn_iff]
  intro b hb ε hε
  refine ⟨ε / (L + 1), by positivity, fun a ha hab => ?_⟩
  rw [Real.dist_eq] at hab ⊢
  calc |g a - g b| ≤ L * |a - b| := hL a ha b hb
    _ ≤ L * (ε / (L + 1)) := by gcongr
    _ < ε := by
      rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
      nlinarith

/-- **Linearization.** If the derivative is Lipschitz continuous with
constant `L` on a convex set, the tangent at `x` is within `L * (y - x) ^ 2`
of `f` at any `y` of the set. -/
theorem abs_sub_tangent_le {s : Set ℝ} (hs : Convex ℝ s)
    (hf : ∀ y ∈ s, HasDerivAt f (df y) y) (hL0 : 0 ≤ L)
    (hL : ∀ y ∈ s, ∀ z ∈ s, |df y - df z| ≤ L * |y - z|) {x y : ℝ} (hx : x ∈ s)
    (hy : y ∈ s) : |f y - f x - df x * (y - x)| ≤ L * (y - x) ^ 2 := by
  have hsub : Set.uIcc x y ⊆ s := by
    rw [← segment_eq_uIcc]
    exact hs.segment_subset hx hy
  let g : ℝ → ℝ := fun t => f t - df x * t
  have hg : ∀ t ∈ Set.uIcc x y, HasDerivWithinAt g (df t - df x) (Set.uIcc x y) t := by
    intro t ht
    have := (hf t (hsub ht)).sub ((hasDerivAt_id t).const_mul (df x))
    simpa using this.hasDerivWithinAt
  have hb : ∀ t ∈ Set.uIcc x y, ‖df t - df x‖ ≤ L * |y - x| := by
    intro t ht
    rw [Real.norm_eq_abs]
    calc |df t - df x| ≤ L * |t - x| := hL t (hsub ht) x hx
      _ ≤ L * |y - x| := by
        gcongr
        exact Set.abs_sub_left_of_mem_uIcc ht
  have := (convex_uIcc x y).norm_image_sub_le_of_norm_hasDerivWithin_le hg hb
    Set.left_mem_uIcc Set.right_mem_uIcc
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at this
  have hgxy : g y - g x = f y - f x - df x * (y - x) := by simp only [g]; ring
  rw [hgxy] at this
  calc |f y - f x - df x * (y - x)| ≤ L * |y - x| * |y - x| := this
    _ = L * (y - x) ^ 2 := by rw [mul_assoc, abs_mul_abs_self, sq]

/-! ### One step -/

/-- **Quadratic convergence.** Under the hypotheses of `abs_sub_tangent_le`,
one step from `x` towards a root `r` leaves an error of at most
`L * (x - r) ^ 2 / |df x|`. -/
theorem newtonStep_error {s : Set ℝ} (hs : Convex ℝ s)
    (hf : ∀ y ∈ s, HasDerivAt f (df y) y) (hL0 : 0 ≤ L)
    (hL : ∀ y ∈ s, ∀ z ∈ s, |df y - df z| ≤ L * |y - z|) {x r : ℝ} (hx : x ∈ s)
    (hr : r ∈ s) (hfr : f r = 0) (hdx : df x ≠ 0) :
    |newtonStep f df x - r| ≤ L * (x - r) ^ 2 / |df x| := by
  have key : newtonStep f df x - r = -(f r - f x - df x * (r - x)) / df x := by
    unfold newtonStep
    rw [hfr]
    field_simp
    ring
  rw [key, abs_div, abs_neg]
  have h := abs_sub_tangent_le hs hf hL0 hL hx hr
  have hsq : (r - x) ^ 2 = (x - r) ^ 2 := by ring
  rw [hsq] at h
  gcongr

/-! ### Convergence -/

/-- **Convergence.** If the hypotheses hold within `δ` of a root `r`, with
`2 * L * δ ≤ m`, then from any starting point within `δ` of `r` every step at
least halves the error: after `n` steps it is at most `|x0 - r| / 2 ^ n`. -/
theorem newton_error {r δ x0 : ℝ} (hf : ∀ y ∈ Set.Icc (r - δ) (r + δ), HasDerivAt f (df y) y)
    (hL0 : 0 ≤ L)
    (hL : ∀ y ∈ Set.Icc (r - δ) (r + δ), ∀ z ∈ Set.Icc (r - δ) (r + δ),
      |df y - df z| ≤ L * |y - z|)
    (hm : 0 < m) (hdm : ∀ y ∈ Set.Icc (r - δ) (r + δ), m ≤ |df y|) (hδ : 2 * L * δ ≤ m)
    (hfr : f r = 0) (hx0 : |x0 - r| ≤ δ) (n : ℕ) :
    |newton f df x0 n - r| ≤ |x0 - r| / 2 ^ n := by
  have mem : ∀ y, |y - r| ≤ δ → y ∈ Set.Icc (r - δ) (r + δ) := by
    intro y hy
    rw [abs_le] at hy
    constructor <;> linarith
  have hr : r ∈ Set.Icc (r - δ) (r + δ) := mem r (by simpa using hx0.trans' (abs_nonneg _))
  -- One step from within `δ` of `r` at least halves the error.
  have halve : ∀ y, |y - r| ≤ δ → |newtonStep f df y - r| ≤ |y - r| / 2 := by
    intro y hy
    have hdy : m ≤ |df y| := hdm y (mem y hy)
    have hdy0 : df y ≠ 0 := abs_pos.mp (hm.trans_le hdy)
    have h := newtonStep_error (convex_Icc _ _) hf hL0 hL (mem y hy) hr hfr hdy0
    calc |newtonStep f df y - r| ≤ L * (y - r) ^ 2 / |df y| := h
      _ ≤ L * (y - r) ^ 2 / m := by gcongr
      _ ≤ |y - r| / 2 := by
        rw [div_le_iff₀ hm, ← sq_abs]
        have ha := abs_nonneg (y - r)
        nlinarith [mul_le_mul_of_nonneg_left hy (mul_nonneg hL0 ha)]
  induction n with
  | zero => simp [newton_zero]
  | succ n ih =>
    have hn : |newton f df x0 n - r| ≤ δ := by
      refine ih.trans ?_
      calc |x0 - r| / 2 ^ n ≤ |x0 - r| := div_le_self (abs_nonneg _) (one_le_pow₀ (by norm_num))
        _ ≤ δ := hx0
    rw [newton_succ]
    calc |newtonStep f df (newton f df x0 n) - r| ≤ |newton f df x0 n - r| / 2 := halve _ hn
      _ ≤ |x0 - r| / 2 ^ n / 2 := by gcongr
      _ = |x0 - r| / 2 ^ (n + 1) := by rw [pow_succ, div_div]

/-! ### The guarantee of a short step -/

/-- **A posteriori error bound.** Let `x'` be the Newton step from `x`, and
`s = |x' - x|` the length of the step. If, on the interval of half-width `s`
around `x'`, the derivative is Lipschitz continuous with constant `L` and at
least `m > 0` in absolute value, and `L * s ≤ m`, then `f` has a root in that
interval within `L * s ^ 2 / m` of `x'`.

No root needs to be known: the hypotheses are about the step that was taken. -/
theorem newtonStep_exists_root {x : ℝ}
    (hf : ∀ y ∈ Set.Icc (newtonStep f df x - |newtonStep f df x - x|)
      (newtonStep f df x + |newtonStep f df x - x|), HasDerivAt f (df y) y)
    (hL0 : 0 ≤ L)
    (hL : ∀ y ∈ Set.Icc (newtonStep f df x - |newtonStep f df x - x|)
        (newtonStep f df x + |newtonStep f df x - x|),
      ∀ z ∈ Set.Icc (newtonStep f df x - |newtonStep f df x - x|)
        (newtonStep f df x + |newtonStep f df x - x|), |df y - df z| ≤ L * |y - z|)
    (hm : 0 < m)
    (hdm : ∀ y ∈ Set.Icc (newtonStep f df x - |newtonStep f df x - x|)
      (newtonStep f df x + |newtonStep f df x - x|), m ≤ |df y|)
    (hLs : L * |newtonStep f df x - x| ≤ m) :
    ∃ r ∈ Set.Icc (newtonStep f df x - |newtonStep f df x - x|)
        (newtonStep f df x + |newtonStep f df x - x|),
      f r = 0 ∧ |newtonStep f df x - r| ≤ L * |newtonStep f df x - x| ^ 2 / m := by
  set x' := newtonStep f df x with hx'
  set s := |x' - x| with hs
  set I := Set.Icc (x' - s) (x' + s) with hI
  have hs0 : 0 ≤ s := abs_nonneg _
  have mem : ∀ y, |y - x'| ≤ s → y ∈ I := by
    intro y hy
    rw [abs_le] at hy
    constructor <;> linarith
  have hxI : x ∈ I := mem x (by rw [abs_sub_comm])
  have hx'I : x' ∈ I := mem x' (by simpa using hs0)
  have hdx : df x ≠ 0 := abs_pos.mp (hm.trans_le (hdm x hxI))
  -- The value at `x'` is small: the tangent at `x` is zero there.
  have hfx' : |f x'| ≤ L * s ^ 2 := by
    have h := abs_sub_tangent_le (convex_Icc _ _) hf hL0 hL hxI hx'I
    have ht : f x' - f x - df x * (x' - x) = f x' := by
      rw [hx']
      unfold newtonStep
      field_simp
      ring
    rw [ht] at h
    calc |f x'| ≤ L * (x' - x) ^ 2 := h
      _ = L * s ^ 2 := by rw [hs, sq_abs]
  -- So `f` must reach zero within `ρ = |f x'| / m` of `x'`.
  set ρ := |f x'| / m with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hρL : ρ ≤ L * s ^ 2 / m := by gcongr
  have hρs : ρ ≤ s := by
    refine hρL.trans ?_
    rw [div_le_iff₀ hm]
    nlinarith [mul_le_mul_of_nonneg_left hLs hs0]
  have hfc : ContinuousOn f I := fun y hy => (hf y hy).continuousAt.continuousWithinAt
  have hdfc : ContinuousOn df I := continuousOn_of_lipschitz hL0 hL
  have haI : x' - ρ ∈ I := mem _ (by rw [show x' - ρ - x' = -ρ by ring, abs_neg, abs_of_nonneg hρ0]; exact hρs)
  have hbI : x' + ρ ∈ I := mem _ (by rw [show x' + ρ - x' = ρ by ring, abs_of_nonneg hρ0]; exact hρs)
  have hsubI : Set.Icc (x' - ρ) (x' + ρ) ⊆ I := Set.Icc_subset_Icc haI.1 hbI.2
  rcases hρ0.eq_or_lt with h0 | hpos
  · -- `f x' = 0`.
    refine ⟨x', hx'I, ?_, by simpa using div_nonneg (mul_nonneg hL0 (sq_nonneg s)) hm.le⟩
    have : |f x'| = 0 := by
      have := (div_eq_zero_iff.mp h0.symm)
      rcases this with h | h
      · exact h
      · exact absurd h hm.ne'
    exact abs_eq_zero.mp this
  -- The mean value theorem on each side of `x'`.
  obtain ⟨c₁, hc₁, hd₁⟩ := exists_hasDerivAt_eq_slope f df (by linarith : x' < x' + ρ)
    (hfc.mono (Set.Icc_subset_Icc hx'I.1 hbI.2))
    (fun y hy => hf y ⟨hx'I.1.trans hy.1.le, hy.2.le.trans hbI.2⟩)
  obtain ⟨c₂, hc₂, hd₂⟩ := exists_hasDerivAt_eq_slope f df (by linarith : x' - ρ < x')
    (hfc.mono (Set.Icc_subset_Icc haI.1 hx'I.2))
    (fun y hy => hf y ⟨haI.1.trans hy.1.le, hy.2.le.trans hx'I.2⟩)
  have hc₁I : c₁ ∈ I := ⟨hx'I.1.trans hc₁.1.le, hc₁.2.le.trans hbI.2⟩
  have hc₂I : c₂ ∈ I := ⟨haI.1.trans hc₂.1.le, hc₂.2.le.trans hx'I.2⟩
  rw [show x' + ρ - x' = ρ by ring, eq_div_iff hpos.ne'] at hd₁
  rw [show x' - (x' - ρ) = ρ by ring, eq_div_iff hpos.ne'] at hd₂
  -- The derivative does not change sign on `I`: it would have to pass zero.
  have hsign : (m ≤ df c₁ ∧ m ≤ df c₂) ∨ (df c₁ ≤ -m ∧ df c₂ ≤ -m) := by
    have h₁ := hdm c₁ hc₁I
    have h₂ := hdm c₂ hc₂I
    rw [le_abs'] at h₁ h₂
    have huI : Set.uIcc c₁ c₂ ⊆ I := by
      rw [← segment_eq_uIcc]
      exact (convex_Icc _ _).segment_subset hc₁I hc₂I
    have hnz : ∀ c ∈ Set.uIcc c₁ c₂, df c ≠ 0 := fun c hc h =>
      by have := hdm c (huI hc); rw [h, abs_zero] at this; linarith
    have hivt := intermediate_value_uIcc (hdfc.mono huI)
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
    · exact Or.inr ⟨by linarith, by linarith⟩
    · exfalso
      obtain ⟨c, hc, hc0⟩ := hivt (Set.mem_uIcc.mpr (Or.inl ⟨by linarith, by linarith⟩))
      exact hnz c hc hc0
    · exfalso
      obtain ⟨c, hc, hc0⟩ := hivt (Set.mem_uIcc.mpr (Or.inr ⟨by linarith, by linarith⟩))
      exact hnz c hc hc0
    · exact Or.inl ⟨h₁, h₂⟩
  have hmρ : m * ρ = |f x'| := by rw [hρ]; field_simp
  have hsc : SignChange f (x' - ρ) (x' + ρ) := by
    unfold SignChange
    have hab := abs_le.mp (le_refl |f x'|)
    rcases hsign with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · have hb : 0 ≤ f (x' + ρ) := by nlinarith [mul_le_mul_of_nonneg_right h₁ hpos.le]
      have ha : f (x' - ρ) ≤ 0 := by nlinarith [mul_le_mul_of_nonneg_right h₂ hpos.le]
      exact mul_nonpos_of_nonpos_of_nonneg ha hb
    · have hb : f (x' + ρ) ≤ 0 := by nlinarith [mul_le_mul_of_nonneg_right h₁ hpos.le]
      have ha : 0 ≤ f (x' - ρ) := by nlinarith [mul_le_mul_of_nonneg_right h₂ hpos.le]
      exact mul_nonpos_of_nonneg_of_nonpos ha hb
  obtain ⟨r, hr, hfr⟩ := exists_root_of_signChange (by linarith) (hfc.mono hsubI) hsc
  refine ⟨r, hsubI hr, hfr, ?_⟩
  refine le_trans ?_ hρL
  rw [abs_le]
  constructor <;> linarith [hr.1, hr.2]

/-- **Stopping criterion.** When the stopping test `newtonDone` holds after
`n + 1` steps, and the hypotheses of `newtonStep_exists_root` hold for the
last step, the approximation is within the tolerance of a root. -/
theorem newton_error_of_done {tol : ℝ → ℝ} {x0 : ℝ} {n : ℕ}
    (hd : newtonDone f df tol x0 (n + 1)) (htol : 0 ≤ tol (newton f df x0 (n + 1)))
    (hf : ∀ y ∈ Set.Icc (newton f df x0 (n + 1) - |newton f df x0 (n + 1) - newton f df x0 n|)
      (newton f df x0 (n + 1) + |newton f df x0 (n + 1) - newton f df x0 n|),
      HasDerivAt f (df y) y)
    (hL0 : 0 ≤ L)
    (hL : ∀ y ∈ Set.Icc (newton f df x0 (n + 1) - |newton f df x0 (n + 1) - newton f df x0 n|)
        (newton f df x0 (n + 1) + |newton f df x0 (n + 1) - newton f df x0 n|),
      ∀ z ∈ Set.Icc (newton f df x0 (n + 1) - |newton f df x0 (n + 1) - newton f df x0 n|)
        (newton f df x0 (n + 1) + |newton f df x0 (n + 1) - newton f df x0 n|),
        |df y - df z| ≤ L * |y - z|)
    (hm : 0 < m)
    (hdm : ∀ y ∈ Set.Icc (newton f df x0 (n + 1) - |newton f df x0 (n + 1) - newton f df x0 n|)
      (newton f df x0 (n + 1) + |newton f df x0 (n + 1) - newton f df x0 n|), m ≤ |df y|)
    (hLs : L * |newton f df x0 (n + 1) - newton f df x0 n| ≤ m) :
    ∃ r, f r = 0 ∧ |newton f df x0 (n + 1) - r| ≤ tol (newton f df x0 (n + 1)) := by
  rcases hd with h0 | hstep
  · exact ⟨_, h0, by simpa using htol⟩
  rw [newton_succ] at hf hL hdm hLs hstep ⊢
  obtain ⟨r, -, hfr, hr⟩ := newtonStep_exists_root hf hL0 hL hm hdm hLs
  refine ⟨r, hfr, hr.trans (le_trans ?_ hstep)⟩
  rw [div_le_iff₀ hm, sq]
  nlinarith [mul_le_mul_of_nonneg_left hLs (abs_nonneg (newtonStep f df (newton f df x0 n) -
    newton f df x0 n))]

end Thole.Roots
