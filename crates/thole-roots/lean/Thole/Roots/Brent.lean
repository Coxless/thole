/-
Brent's method for root finding: the proofs.

Rust counterpart: `thole_roots::brent` in `../../../src/brent.rs`.

The algorithm is the procedure `zero` of R. P. Brent, "Algorithms for
Minimization without Derivatives" (Prentice-Hall, 1973), chapter 4. It keeps
three points: `cur`, the best approximation so far; `contra`, a point where
`f` has the opposite sign, so that a root lies between the two; and `prev`,
the previous value of `cur`. Each step moves `cur` by an interpolation step
when that step is acceptable and by a bisection step otherwise.

The iteration is defined in `Brent/Defs.lean`, over any linearly ordered
field; the table that maps the definitions to the Rust code is there. This
file proves their properties over the real numbers.

What is proved: the root stays bracketed, the stopping test guarantees the
error, and the iteration stops. These hold whatever `brentInterp` proposes,
because a proposal is only accepted when it falls inside the bracket.

What is not proved:

- Brent's bound on the number of steps (about the square of the number of
  bisection steps). `brent_done_of_le` only gives the bound that follows from
  every step being at least `tol` long, which is linear in `(b - a) / tol`.
- That the inverse quadratic step is the root of the interpolating
  polynomial, and the superlinear convergence for smooth `f`. Only the secant
  case is checked here (`brentInterp_secant`).
-/
import Thole.Roots.Brent.Defs
import Thole.Roots.Bisection
import Mathlib.Order.Interval.Set.UnorderedInterval
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.FieldSimp

namespace Thole.Roots

variable {f : ℝ → ℝ} {tol : ℝ → ℝ} {a b : ℝ} {s : BrentState ℝ}

@[simp]
theorem brent_zero (f : ℝ → ℝ) (tol : ℝ → ℝ) (a b : ℝ) : brent f tol a b 0 = brentInit f a b :=
  rfl

theorem brent_succ (f : ℝ → ℝ) (tol : ℝ → ℝ) (a b : ℝ) (n : ℕ) :
    brent f tol a b (n + 1) = brentStep f tol (brent f tol a b n) :=
  Function.iterate_succ_apply' _ _ _

/-! ### The interpolation step -/

/-- The sign normalization does not change the proposed step. -/
theorem brentP_div_brentQ (f : ℝ → ℝ) (s : BrentState ℝ) :
    brentP f s / brentQ f s = -((brentInterp f s).1 / (brentInterp f s).2) := by
  unfold brentP brentQ
  split_ifs with h
  · rw [abs_of_pos h, div_neg]
  · rw [abs_of_nonpos (not_lt.mp h), neg_div]

/-- With two distinct points the proposed step is the secant step: it leads
to the root of the line through `(prev, f prev)` and `(cur, f cur)`. -/
theorem brentInterp_secant (h : s.prev = s.contra) (hp : f s.prev ≠ 0)
    (hne : f s.cur ≠ f s.prev) :
    s.cur + brentP f s / brentQ f s =
      s.cur - f s.cur * (s.cur - s.prev) / (f s.cur - f s.prev) := by
  have h1 : f s.prev - f s.cur ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have h2 : f s.cur - f s.prev ≠ 0 := sub_ne_zero.mpr hne
  rw [brentP_div_brentQ]
  unfold brentInterp BrentState.half
  split_ifs
  rw [← h]
  field_simp
  ring

/-- The step proposed by `brentTrial` is the bisection step, or a quotient
that passed the acceptance test. -/
theorem brentTrial_spec (f : ℝ → ℝ) (tol : ℝ → ℝ) (s : BrentState ℝ) :
    (brentTrial f tol s).1 = s.half ∨
      ∃ p q, (brentTrial f tol s).1 = p / q ∧ 0 ≤ p ∧
        2 * p < 3 * s.half * q - |tol s.cur * q| := by
  unfold brentTrial
  split_ifs with h₁ h₂
  · exact Or.inl rfl
  · exact Or.inr ⟨_, _, rfl, abs_nonneg _, h₂.1⟩
  · exact Or.inl rfl

/-- The step taken is at least `τ` long, points towards `contra`, and stops
at least `τ` short of it. -/
theorem brentShift_bounds {τ m d : ℝ} (hτ : 0 ≤ τ) (hm : τ < |m|)
    (hd : d = m ∨ ∃ p q, d = p / q ∧ 0 ≤ p ∧ 2 * p < 3 * m * q - |τ * q|) :
    (0 < m → τ ≤ brentShift τ m d ∧ brentShift τ m d ≤ 2 * m - τ) ∧
      (m < 0 → 2 * m + τ ≤ brentShift τ m d ∧ brentShift τ m d ≤ -τ) := by
  constructor
  · intro hm0
    rw [abs_of_pos hm0] at hm
    have hd' : 0 ≤ d ∧ d ≤ 2 * m - τ := by
      rcases hd with rfl | ⟨p, q, rfl, hp, hpq⟩
      · constructor <;> linarith
      · have hq : 0 < q := by
          by_contra hq
          have hq : q ≤ 0 := not_lt.mp hq
          nlinarith [mul_nonneg hm0.le (neg_nonneg.mpr hq), abs_nonneg (τ * q)]
        refine ⟨div_nonneg hp hq.le, ?_⟩
        rw [div_le_iff₀ hq]
        nlinarith [le_abs_self (τ * q), mul_nonneg (sub_nonneg.mpr hm.le) hq.le]
    unfold brentShift
    split_ifs with h
    · rw [abs_of_nonneg hd'.1] at h
      exact ⟨h.le, hd'.2⟩
    · constructor <;> linarith
  · intro hm0
    rw [abs_of_neg hm0] at hm
    have hd' : 2 * m + τ ≤ d ∧ d ≤ 0 := by
      rcases hd with rfl | ⟨p, q, rfl, hp, hpq⟩
      · constructor <;> linarith
      · have hq : q < 0 := by
          by_contra hq
          have hq : 0 ≤ q := not_lt.mp hq
          nlinarith [mul_nonneg (neg_nonneg.mpr hm0.le) hq, abs_nonneg (τ * q)]
        refine ⟨?_, div_nonpos_of_nonneg_of_nonpos hp hq.le⟩
        rw [le_div_iff_of_neg hq]
        have hmτ : m + τ ≤ 0 := by linarith
        nlinarith [neg_le_abs (τ * q), mul_nonneg_of_nonpos_of_nonpos hmτ hq.le]
    unfold brentShift
    split_ifs with h
    · rw [abs_of_nonpos hd'.2] at h
      exact ⟨hd'.1, by linarith⟩
    all_goals constructor <;> linarith

/-! ### A single step -/

/-- Reordering keeps the two ends of the bracket, possibly exchanged. -/
theorem brentOrder_pair (f : ℝ → ℝ) (s : BrentState ℝ) :
    ((brentOrder f s).cur = s.cur ∧ (brentOrder f s).contra = s.contra) ∨
      ((brentOrder f s).cur = s.contra ∧ (brentOrder f s).contra = s.cur) := by
  unfold brentOrder
  split_ifs
  · exact Or.inr ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩

theorem brentStep_of_done (h : brentDone f tol s) : brentStep f tol s = s := by
  simp only [brentStep, h, ↓reduceIte]

/-- Before the iteration stops the bracket is not a single point. -/
theorem cur_ne_contra_of_not_done (hτ : 0 ≤ tol s.cur) (h : ¬brentDone f tol s) :
    s.cur ≠ s.contra := by
  intro hc
  have h0 : s.half = 0 := by unfold BrentState.half; rw [hc]; simp
  exact h (Or.inr (by rw [h0, abs_zero]; exact hτ))

/-- The new `cur` lies in the bracket, at least `tol` away from both ends. -/
theorem brentNext_bounds (hτ : 0 ≤ tol s.cur) (h : ¬brentDone f tol s) :
    (s.cur < s.contra →
        s.cur + tol s.cur ≤ brentNext f tol s ∧ brentNext f tol s ≤ s.contra - tol s.cur) ∧
      (s.contra < s.cur →
        s.contra + tol s.cur ≤ brentNext f tol s ∧ brentNext f tol s ≤ s.cur - tol s.cur) := by
  have hm : tol s.cur < |s.half| := not_le.mp (not_or.mp h).2
  obtain ⟨hpos, hneg⟩ := brentShift_bounds hτ hm (brentTrial_spec f tol s)
  have hh : 2 * s.half = s.contra - s.cur := by unfold BrentState.half; ring
  unfold brentNext
  constructor
  · intro hlt
    obtain ⟨h₁, h₂⟩ := hpos (by linarith)
    constructor <;> linarith
  · intro hlt
    obtain ⟨h₁, h₂⟩ := hneg (by linarith)
    constructor <;> linarith

/-- The ends of the bracket after a step that is not stopped: the new `cur`
together with whichever of the old ends has the opposite sign. -/
theorem brentStep_cases (h : ¬brentDone f tol s) :
    ∃ y, ((y = s.contra ∧ f (brentNext f tol s) * f y ≤ 0) ∨
        (y = s.cur ∧ 0 < f (brentNext f tol s) * f s.contra)) ∧
      (((brentStep f tol s).cur = brentNext f tol s ∧ (brentStep f tol s).contra = y) ∨
        ((brentStep f tol s).cur = y ∧ (brentStep f tol s).contra = brentNext f tol s)) := by
  simp only [brentStep, h, ↓reduceIte]
  by_cases hx : f (brentNext f tol s) * f s.contra ≤ 0
  · simp only [hx, ↓reduceIte]
    exact ⟨s.contra, Or.inl ⟨rfl, hx⟩, brentOrder_pair f _⟩
  · simp only [hx, ↓reduceIte]
    exact ⟨s.cur, Or.inr ⟨rfl, not_le.mp hx⟩, brentOrder_pair f _⟩

private theorem signChange_of_same_sign {u v w : ℝ} (h : u * w ≤ 0) (hv : 0 < v * w) :
    v * u ≤ 0 := by
  by_contra hc
  have hc : 0 < v * u := not_le.mp hc
  nlinarith [mul_pos hc hv, mul_nonneg (neg_nonneg.mpr h) (sq_nonneg v)]

/-- A step preserves the sign change between `cur` and `contra`. -/
theorem brentStep_signChange (h : SignChange f s.cur s.contra) :
    SignChange f (brentStep f tol s).cur (brentStep f tol s).contra := by
  by_cases hd : brentDone f tol s
  · rwa [brentStep_of_done hd]
  · unfold SignChange at *
    obtain ⟨y, hy, hpair⟩ := brentStep_cases hd
    have hxy : f (brentNext f tol s) * f y ≤ 0 := by
      rcases hy with ⟨rfl, hy⟩ | ⟨rfl, hy⟩
      · exact hy
      · exact signChange_of_same_sign h hy
    rcases hpair with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · rwa [h₁, h₂]
    · rwa [h₁, h₂, mul_comm]

/-- A step stays inside the bracket it was given. -/
theorem brentStep_mem (hτ : 0 ≤ tol s.cur) :
    (brentStep f tol s).cur ∈ Set.uIcc s.cur s.contra ∧
      (brentStep f tol s).contra ∈ Set.uIcc s.cur s.contra := by
  by_cases hd : brentDone f tol s
  · rw [brentStep_of_done hd]
    exact ⟨Set.left_mem_uIcc, Set.right_mem_uIcc⟩
  · obtain ⟨hlt, hgt⟩ := brentNext_bounds hτ hd
    have hx : brentNext f tol s ∈ Set.uIcc s.cur s.contra := by
      rw [Set.mem_uIcc]
      rcases lt_or_gt_of_ne (cur_ne_contra_of_not_done hτ hd) with hc | hc
      · obtain ⟨h₁, h₂⟩ := hlt hc
        exact Or.inl ⟨by linarith, by linarith⟩
      · obtain ⟨h₁, h₂⟩ := hgt hc
        exact Or.inr ⟨by linarith, by linarith⟩
    obtain ⟨y, hy, hpair⟩ := brentStep_cases hd
    have hy : y ∈ Set.uIcc s.cur s.contra := by
      rcases hy with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact Set.right_mem_uIcc
      · exact Set.left_mem_uIcc
    rcases hpair with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rw [h₁, h₂]
    · exact ⟨hx, hy⟩
    · exact ⟨hy, hx⟩

/-- A step that is not stopped shortens the bracket by at least `tol`. -/
theorem brentStep_width (hτ : 0 ≤ tol s.cur) (hd : ¬brentDone f tol s) :
    |(brentStep f tol s).contra - (brentStep f tol s).cur| ≤
      |s.contra - s.cur| - tol s.cur := by
  obtain ⟨hlt, hgt⟩ := brentNext_bounds hτ hd
  obtain ⟨y, hy, hpair⟩ := brentStep_cases hd
  have key : |y - brentNext f tol s| ≤ |s.contra - s.cur| - tol s.cur := by
    rcases lt_or_gt_of_ne (cur_ne_contra_of_not_done hτ hd) with hc | hc
    · obtain ⟨h₁, h₂⟩ := hlt hc
      rw [abs_of_pos (sub_pos.mpr hc), abs_le]
      rcases hy with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> constructor <;> linarith
    · obtain ⟨h₁, h₂⟩ := hgt hc
      rw [abs_of_neg (sub_neg.mpr hc), abs_le]
      rcases hy with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> constructor <;> linarith
  rcases hpair with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rw [h₁, h₂]
  · exact key
  · rwa [abs_sub_comm]

/-! ### `n` steps -/

/-- `cur` and `contra` always have the sign change. -/
theorem brent_signChange (tol : ℝ → ℝ) (h : SignChange f a b) (n : ℕ) :
    SignChange f (brent f tol a b n).cur (brent f tol a b n).contra := by
  induction n with
  | zero =>
    unfold SignChange at *
    rcases brentOrder_pair f ⟨a, b, a, b - a, b - a⟩ with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · rw [brent_zero, brentInit, h₁, h₂, mul_comm]; exact h
    · rw [brent_zero, brentInit, h₁, h₂]; exact h
  | succ n ih => rw [brent_succ]; exact brentStep_signChange ih

/-- `cur` and `contra` never leave the initial bracket. -/
theorem brent_mem (f : ℝ → ℝ) (htol : ∀ x, 0 ≤ tol x) (hab : a ≤ b) (n : ℕ) :
    (brent f tol a b n).cur ∈ Set.Icc a b ∧ (brent f tol a b n).contra ∈ Set.Icc a b := by
  induction n with
  | zero =>
    have ha : a ∈ Set.Icc a b := Set.left_mem_Icc.mpr hab
    have hb : b ∈ Set.Icc a b := Set.right_mem_Icc.mpr hab
    rcases brentOrder_pair f ⟨a, b, a, b - a, b - a⟩ with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · rw [brent_zero, brentInit, h₁, h₂]; exact ⟨hb, ha⟩
    · rw [brent_zero, brentInit, h₁, h₂]; exact ⟨ha, hb⟩
  | succ n ih =>
    have hsub := Set.uIcc_subset_Icc ih.1 ih.2
    obtain ⟨h₁, h₂⟩ := brentStep_mem (f := f) (htol (brent f tol a b n).cur)
    rw [brent_succ]
    exact ⟨hsub h₁, hsub h₂⟩

/-! ### Roots -/

/-- `exists_root_of_signChange` for two points in either order. -/
theorem exists_root_of_signChange_uIcc {u v : ℝ} (hf : ContinuousOn f (Set.uIcc u v))
    (h : SignChange f u v) : ∃ x ∈ Set.uIcc u v, f x = 0 := by
  rcases le_total u v with huv | huv
  · rw [Set.uIcc_of_le huv] at hf ⊢
    exact exists_root_of_signChange huv hf h
  · rw [Set.uIcc_of_ge huv] at hf ⊢
    exact exists_root_of_signChange huv hf (by unfold SignChange at *; rwa [mul_comm])

/-- **Bracketing.** Under the preconditions of Brent's method, a root of `f`
lies between `cur` and `contra` after any number of steps. -/
theorem brent_exists_root (htol : ∀ x, 0 ≤ tol x) (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) (h : SignChange f a b) (n : ℕ) :
    ∃ x ∈ Set.uIcc (brent f tol a b n).cur (brent f tol a b n).contra, f x = 0 := by
  obtain ⟨h₁, h₂⟩ := brent_mem f htol hab n
  exact exists_root_of_signChange_uIcc (hf.mono (Set.uIcc_subset_Icc h₁ h₂))
    (brent_signChange tol h n)

/-- **Error bound.** `cur` is within the length of the bracket of a root of
`f` in `[a, b]`. -/
theorem brent_error (htol : ∀ x, 0 ≤ tol x) (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) (h : SignChange f a b) (n : ℕ) :
    ∃ x ∈ Set.Icc a b, f x = 0 ∧
      |(brent f tol a b n).cur - x| ≤ |(brent f tol a b n).contra - (brent f tol a b n).cur| := by
  obtain ⟨x, hx, hfx⟩ := brent_exists_root htol hab hf h n
  obtain ⟨h₁, h₂⟩ := brent_mem f htol hab n
  refine ⟨x, Set.uIcc_subset_Icc h₁ h₂ hx, hfx, ?_⟩
  rw [abs_sub_comm]
  exact Set.abs_sub_left_of_mem_uIcc hx

/-- **Stopping criterion.** When the stopping test holds, `cur` is within
`2 * tol cur` of a root of `f` in `[a, b]`. -/
theorem brent_error_of_done (htol : ∀ x, 0 ≤ tol x) (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) (h : SignChange f a b) (n : ℕ)
    (hd : brentDone f tol (brent f tol a b n)) :
    ∃ x ∈ Set.Icc a b, f x = 0 ∧
      |(brent f tol a b n).cur - x| ≤ 2 * tol (brent f tol a b n).cur := by
  rcases hd with hd | hd
  · refine ⟨_, (brent_mem f htol hab n).1, hd, ?_⟩
    rw [sub_self, abs_zero]
    linarith [htol (brent f tol a b n).cur]
  · obtain ⟨x, hx, hfx, hb⟩ := brent_error htol hab hf h n
    refine ⟨x, hx, hfx, hb.trans ?_⟩
    have hw : |(brent f tol a b n).contra - (brent f tol a b n).cur| =
        2 * |(brent f tol a b n).half| := by
      unfold BrentState.half
      rw [abs_div, abs_two]
      ring
    linarith

/-! ### Termination -/

/-- While the iteration has not stopped, each of the `n` steps taken has
shortened the bracket by at least `δ`. -/
theorem brent_width_le {δ : ℝ} (hδ : 0 ≤ δ) (htol : ∀ x, δ ≤ tol x) (hab : a ≤ b) (n : ℕ)
    (hd : ¬brentDone f tol (brent f tol a b n)) :
    |(brent f tol a b n).contra - (brent f tol a b n).cur| ≤ b - a - n * δ := by
  induction n with
  | zero =>
    have hw : |a - b| = b - a := by rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hab)]
    rcases brentOrder_pair f ⟨a, b, a, b - a, b - a⟩ with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · rw [brent_zero, brentInit, h₁, h₂]; simp [hw]
    · rw [brent_zero, brentInit, h₁, h₂]; simp [abs_of_nonneg (sub_nonneg.mpr hab)]
  | succ n ih =>
    have hd' : ¬brentDone f tol (brent f tol a b n) := by
      intro hn
      rw [brent_succ, brentStep_of_done hn] at hd
      exact hd hn
    have hw := brentStep_width (hδ.trans (htol _)) hd'
    have hcast : ((n + 1 : ℕ) : ℝ) * δ = n * δ + δ := by push_cast; ring
    rw [brent_succ, hcast]
    linarith [ih hd', htol (brent f tol a b n).cur]

/-- **Termination.** If the tolerance is at least `δ > 0` everywhere, the
stopping test holds after `n` steps as soon as `(n + 2) * δ ≥ b - a`. -/
theorem brent_done_of_le {δ : ℝ} (hδ : 0 < δ) (htol : ∀ x, δ ≤ tol x) (hab : a ≤ b) {n : ℕ}
    (hn : b - a ≤ (n + 2) * δ) : brentDone f tol (brent f tol a b n) := by
  by_contra hd
  have hw := brent_width_le hδ.le htol hab n hd
  have hm : tol (brent f tol a b n).cur < |(brent f tol a b n).half| := not_le.mp (not_or.mp hd).2
  have hh : |(brent f tol a b n).contra - (brent f tol a b n).cur| =
      2 * |(brent f tol a b n).half| := by
    unfold BrentState.half
    rw [abs_div, abs_two]
    ring
  nlinarith [htol (brent f tol a b n).cur]

/-- **Convergence.** If the tolerance is at least `δ > 0` everywhere, the
iteration stops: from some step on the stopping test holds, and then
`brent_error_of_done` bounds the error. -/
theorem brent_eventually_done {δ : ℝ} (hδ : 0 < δ) (htol : ∀ x, δ ≤ tol x) (hab : a ≤ b) :
    ∃ N, ∀ n ≥ N, brentDone f tol (brent f tol a b n) := by
  obtain ⟨N, hN⟩ := exists_nat_ge ((b - a) / δ)
  refine ⟨N, fun n hn => brent_done_of_le hδ htol hab ?_⟩
  have h₁ : b - a ≤ N * δ := (div_le_iff₀ hδ).mp hN
  have h₂ : (N : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith

end Thole.Roots
