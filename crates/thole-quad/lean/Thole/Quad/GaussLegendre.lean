/-
Gauss-Legendre quadrature: the proofs.

Rust counterpart: `thole_quad::GaussLegendre` in `../../../src/gauss_legendre.rs`.

The definitions are in `GaussLegendre/Defs.lean`, with the table that maps
them to the Rust code. This file proves, over the real numbers:

- `legendre_one`, `legendre_neg`: `P_n(1) = 1` and `P_n(-x) = (-1)^n P_n(x)`.
  The second is why the Rust code computes only the positive nodes.
- `ruleSum_eq_sum`: the sum that the Rust code forms in order is the sum of
  `w_i f(x_i)`.
- `gauss_exact`: a rule with `n` nodes that is exact for polynomials of degree
  below `n`, and whose nodes are roots of a monic polynomial of degree `n`
  orthogonal on `[-1, 1]` to every polynomial of degree below `n`, is exact for
  polynomials of degree below `2n`. This is why Gauss rules have twice the
  degree of exactness of other rules with as many nodes.
- `rule_exact_of_exact`: a rule exact on `[-1, 1]` for polynomials of degree at
  most `d` is exact on any `[a, b]` through the affine map, for the same
  degrees.

Not proved: that the Legendre polynomials of the recurrence are orthogonal on
`[-1, 1]`, that `gaussWeight` gives the weights that make the rule exact for
degree below `n`, and that `P_n` has `n` simple roots in `(-1, 1)`. These are
classical (G. Szegő, "Orthogonal Polynomials", chapters 3 and 4); proving them
needs the Rodrigues formula or the Christoffel-Darboux identity, which Mathlib
does not have for this recurrence. With them, `gauss_exact` and
`rule_exact_of_exact` give the exactness of `GaussLegendre::integrate` for
degree at most `2n - 1`. The oracle tests the parts that are not proved: it
requires `P_n` to change sign around every computed node, and the rule to
integrate polynomials of degree `2n - 1` up to rounding.
-/
import Thole.Quad.GaussLegendre.Defs
import Mathlib.Algebra.Polynomial.Div
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace Thole.Quad

open Polynomial

/-! ### The Legendre recurrence -/

theorem legendrePair_one_pos (n : ℕ) (hn : 1 ≤ n) : legendrePair (1 : ℝ) n = (1, 1) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      simp [legendrePair, legendreStep]
    · rw [legendrePair, ih h, legendreStep]
      ext <;> simp only
      field_simp
      ring

/-- `P_n(1) = 1`. -/
theorem legendre_one (n : ℕ) : legendre n (1 : ℝ) = 1 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; rfl
  · simp [legendre, legendrePair_one_pos n h]

theorem legendrePair_neg (x : ℝ) (n : ℕ) :
    legendrePair (-x) n = (-(-1) ^ n * (legendrePair x n).1, (-1) ^ n * (legendrePair x n).2) := by
  induction n with
  | zero => simp [legendrePair]
  | succ n ih =>
    rw [legendrePair, legendrePair, ih]
    simp only [legendreStep, pow_succ]
    ext <;> simp only <;> ring

/-- **Symmetry.** `P_n(-x) = (-1)^n P_n(x)`: the roots of `P_n` are symmetric
about zero. -/
theorem legendre_neg (n : ℕ) (x : ℝ) : legendre n (-x) = (-1) ^ n * legendre n x := by
  simp [legendre, legendrePair_neg]

/-! ### Rules -/

theorem foldl_add_eq {β : Type*} (g : β → ℝ) (l : List β) (init : ℝ) :
    l.foldl (fun acc p => acc + g p) init = init + (l.map g).sum := by
  induction l generalizing init with
  | nil => simp
  | cons p l ih => rw [List.foldl_cons, ih, List.map_cons, List.sum_cons]; ring

/-- The sum that the Rust code forms in order is the sum of `w_i f(x_i)`. -/
theorem ruleSum_eq_sum (xs ws : List ℝ) (f : ℝ → ℝ) :
    ruleSum xs ws f = ((xs.zip ws).map fun p => p.2 * f p.1).sum := by
  rw [ruleSum, foldl_add_eq, zero_add]

/-- A rule only looks at the values at its nodes. -/
theorem ruleSum_congr {xs ws : List ℝ} {f g : ℝ → ℝ} (h : ∀ x ∈ xs, f x = g x) :
    ruleSum xs ws f = ruleSum xs ws g := by
  rw [ruleSum_eq_sum, ruleSum_eq_sum]
  congr 1
  apply List.map_congr_left
  intro p hp
  rw [h p.1 (List.of_mem_zip hp).1]

theorem ruleSum_add (xs ws : List ℝ) (f g : ℝ → ℝ) :
    ruleSum xs ws (fun x => f x + g x) = ruleSum xs ws f + ruleSum xs ws g := by
  simp only [ruleSum_eq_sum, mul_add, ← List.sum_map_add]

/-- **Gauss quadrature.** Let `P` be a monic polynomial of degree `n` that is
orthogonal on `[-1, 1]` to every polynomial of degree below `n`, and let a rule
have roots of `P` as its nodes and be exact for polynomials of degree below
`n`. Then the rule is exact for polynomials of degree below `2n`. -/
theorem gauss_exact {n : ℕ} {xs ws : List ℝ} {P : ℝ[X]} (hP : P.Monic) (hdeg : P.natDegree = n)
    (hroot : ∀ x ∈ xs, P.eval x = 0)
    (horth : ∀ q : ℝ[X], q.natDegree < n → ∫ t in (-1 : ℝ)..1, (P * q).eval t = 0)
    (hexact : ∀ q : ℝ[X], q.natDegree < n →
      ruleSum xs ws (fun t => q.eval t) = ∫ t in (-1 : ℝ)..1, q.eval t)
    (q : ℝ[X]) (hq : q.natDegree < 2 * n) :
    ruleSum xs ws (fun t => q.eval t) = ∫ t in (-1 : ℝ)..1, q.eval t := by
  have hn : 0 < n := by omega
  have hP1 : P ≠ 1 := by
    rintro rfl
    simp at hdeg
    omega
  -- `q = P * s + r` with `s` and `r` of degree below `n`.
  set s := q /ₘ P
  set r := q %ₘ P
  have hqsr : q = P * s + r := (modByMonic_add_div q hP).symm.trans (add_comm _ _)
  have hr : r.natDegree < n := hdeg ▸ natDegree_modByMonic_lt q hP hP1
  have hs : s.natDegree < n := by
    rw [natDegree_divByMonic, hdeg]
    omega
  have hint : ∀ p : ℝ[X], IntervalIntegrable (fun t => p.eval t) MeasureTheory.volume (-1) 1 :=
    fun p => p.continuous.intervalIntegrable _ _
  calc ruleSum xs ws (fun t => q.eval t)
      = ruleSum xs ws (fun t => (P * s).eval t + r.eval t) := by
        rw [hqsr]; simp only [eval_add]
    _ = ruleSum xs ws (fun t => r.eval t) := by
        rw [ruleSum_add]
        have h0 : ruleSum xs ws (fun t => (P * s).eval t) = ruleSum xs ws (fun _ => 0) :=
          ruleSum_congr fun x hx => by rw [eval_mul, hroot x hx, zero_mul]
        rw [h0]
        simp [ruleSum_eq_sum]
    _ = ∫ t in (-1 : ℝ)..1, r.eval t := hexact r hr
    _ = ∫ t in (-1 : ℝ)..1, (P * s).eval t + r.eval t := by
        rw [intervalIntegral.integral_add (hint _) (hint _), horth s hs, zero_add]
    _ = ∫ t in (-1 : ℝ)..1, q.eval t := by
        rw [hqsr]; simp only [eval_add]

/-- **Change of interval.** A rule exact on `[-1, 1]` for the polynomials of
degree at most `d` is exact on `[a, b]` for the same polynomials, through the
affine map of `rule`. -/
theorem rule_exact_of_exact {d : ℕ} {xs ws : List ℝ}
    (hexact : ∀ q : ℝ[X], q.natDegree ≤ d →
      ruleSum xs ws (fun t => q.eval t) = ∫ t in (-1 : ℝ)..1, q.eval t)
    (q : ℝ[X]) (hq : q.natDegree ≤ d) (a b : ℝ) :
    rule xs ws (fun t => q.eval t) a b = ∫ t in a..b, q.eval t := by
  set c := a / 2 + b / 2
  set h := b / 2 - a / 2
  -- The polynomial `q (c + h t)` has degree at most that of `q`.
  set q' := q.comp (C c + C h * X)
  have hdeg : q'.natDegree ≤ d := by
    refine (natDegree_comp_le).trans ?_
    have : (C c + C h * X).natDegree ≤ 1 := by
      refine (natDegree_add_le _ _).trans (max_le (by simp) ?_)
      exact (natDegree_C_mul_le _ _).trans (by simp)
    calc q.natDegree * (C c + C h * X).natDegree ≤ q.natDegree * 1 := Nat.mul_le_mul_left _ this
      _ = q.natDegree := mul_one _
      _ ≤ d := hq
  have heval : ∀ t, q'.eval t = q.eval (c + h * t) := by
    intro t; simp [q']
  have hrule : rule xs ws (fun t => q.eval t) a b = h * ∫ t in (-1 : ℝ)..1, q'.eval t := by
    rw [rule, ← hexact q' hdeg]
    congr 1
    exact ruleSum_congr fun t _ => (heval t).symm
  rw [hrule]
  simp only [heval]
  rcases eq_or_ne h 0 with h0 | h0
  · have hab : a = b := by linarith [show b / 2 - a / 2 = 0 from h0]
    rw [h0, zero_mul, hab, intervalIntegral.integral_same]
  · have := intervalIntegral.integral_comp_mul_add (fun t => q.eval t) h0 c (a := -1) (b := 1)
    simp only at this
    have hl : h * -1 + c = a := by simp only [h, c]; ring
    have hu : h * 1 + c = b := by simp only [h, c]; ring
    rw [hl, hu] at this
    have hcomm : (fun t => q.eval (c + h * t)) = fun t => q.eval (h * t + c) := by
      funext t; rw [add_comm]
    rw [hcomm, this, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ h0, one_mul]

end Thole.Quad
