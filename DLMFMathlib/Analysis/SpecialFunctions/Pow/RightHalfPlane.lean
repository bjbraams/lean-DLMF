/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.MeanValue
public import DLMFMathlib.Analysis.SpecialFunctions.Pow.ComplexReal

/-!
# Complex powers at vertical displacements

For `Re a > 0` and a real displacement `x`, the powers of `a ± ix` can be expressed using
`a² + x²` and the principal arctangent of `x/a`. The right half-plane hypotheses control the
logarithms of the product and quotient, so these identities also apply to complex `a`.
-/

@[expose] public noncomputable section

open Set
open scoped Real

namespace Complex

/-- The sum and difference of the logarithms of `a ± ix` on the right half-plane. -/
theorem log_add_mul_I_add_log_sub_mul_I {a : ℂ} (ha : 0 < a.re) (x : ℝ) :
    log (a + x * I) + log (a - x * I) = log (a ^ 2 + (x : ℂ) ^ 2) ∧
      log (a + x * I) - log (a - x * I) = 2 * I * arctan (x / a) := by
  have hp : 0 < (a + x * I).re := by simpa using ha
  have hm : 0 < (a - x * I).re := by simpa using ha
  have hp0 : a + x * I ≠ 0 := fun h => by simp [h] at hp
  have hm0 : a - x * I ≠ 0 := fun h => by simp [h] at hm
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha
  have hpa := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hp))
  have hma := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hm))
  have hmpi : arg (a - x * I) ≠ Real.pi := by linarith [Real.pi_pos]
  have hprod : (a + x * I) * (a - x * I) = a ^ 2 + (x : ℂ) ^ 2 := by
    linear_combination (-(x : ℂ) ^ 2) * I_sq
  have hsum := log_mul hp0 hm0 (show arg (a + x * I) + arg (a - x * I) ∈
      Ioc (-Real.pi) Real.pi from ⟨by linarith, by linarith⟩)
  have hquot := log_mul hp0 (inv_ne_zero hm0)
    (show arg (a + x * I) + arg (a - x * I)⁻¹ ∈ Ioc (-Real.pi) Real.pi from by
      rw [arg_inv, ite_eq_right hmpi]
      constructor <;> linarith)
  rw [log_inv _ hmpi, ← sub_eq_add_neg, ← div_eq_mul_inv] at hquot
  have hratio : (1 + (x : ℂ) / a * I) / (1 - (x : ℂ) / a * I) =
      (a + x * I) / (a - x * I) := by
    field_simp
  refine ⟨by simpa only [hprod] using hsum.symm, ?_⟩
  rw [arctan, hratio, hquot]
  linear_combination (log (a + x * I) - log (a - x * I)) * I_sq

/-- The sine of a complex multiple of the principal arctangent as a difference of powers. -/
theorem sin_mul_arctan_div_cpow {a : ℂ} (ha : 0 < a.re) (x : ℝ) (s : ℂ) :
    sin (s * arctan (x / a)) / (a ^ 2 + (x : ℂ) ^ 2) ^ (s / 2) =
      ((a - x * I) ^ (-s) - (a + x * I) ^ (-s)) / (2 * I) := by
  have hp0 : a + x * I ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hm0 : a - x * I ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hprod : (a + x * I) * (a - x * I) = a ^ 2 + (x : ℂ) ^ 2 := by
    linear_combination (-(x : ℂ) ^ 2) * I_sq
  have hprod0 : a ^ 2 + (x : ℂ) ^ 2 ≠ 0 := by rw [← hprod]; exact mul_ne_zero hp0 hm0
  obtain ⟨hsum, hdiff⟩ := log_add_mul_I_add_log_sub_mul_I ha x
  have hm : log (a - x * I) = log (a ^ 2 + (x : ℂ) ^ 2) / 2 - I * arctan (x / a) := by
    linear_combination (hsum - hdiff) / 2
  have hp : log (a + x * I) = log (a ^ 2 + (x : ℂ) ^ 2) / 2 + I * arctan (x / a) := by
    linear_combination (hsum + hdiff) / 2
  rw [sin, cpow_def_of_ne_zero hp0, cpow_def_of_ne_zero hm0,
    cpow_def_of_ne_zero hprod0, hm, hp]
  have he₁ : (log (a ^ 2 + (x : ℂ) ^ 2) / 2 - I * arctan (x / a)) * -s =
      -(log (a ^ 2 + (x : ℂ) ^ 2) * (s / 2)) + s * arctan (x / a) * I := by ring
  have he₂ : (log (a ^ 2 + (x : ℂ) ^ 2) / 2 + I * arctan (x / a)) * -s =
      -(log (a ^ 2 + (x : ℂ) ^ 2) * (s / 2)) + -(s * arctan (x / a) * I) := by ring
  rw [he₁, he₂, exp_add, exp_add]
  simp only [neg_mul, exp_neg]
  field_simp
  simp only [I_sq]
  ring

/-- The cosine of a complex multiple of the principal arctangent as a sum of powers. -/
theorem cos_mul_arctan_div_cpow {a : ℂ} (ha : 0 < a.re) (x : ℝ) (s : ℂ) :
    cos (s * arctan (x / a)) / (a ^ 2 + (x : ℂ) ^ 2) ^ (s / 2) =
      ((a - x * I) ^ (-s) + (a + x * I) ^ (-s)) / 2 := by
  have hp0 : a + x * I ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hm0 : a - x * I ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hprod : (a + x * I) * (a - x * I) = a ^ 2 + (x : ℂ) ^ 2 := by
    linear_combination (-(x : ℂ) ^ 2) * I_sq
  have hprod0 : a ^ 2 + (x : ℂ) ^ 2 ≠ 0 := by rw [← hprod]; exact mul_ne_zero hp0 hm0
  obtain ⟨hsum, hdiff⟩ := log_add_mul_I_add_log_sub_mul_I ha x
  have hm : log (a - x * I) = log (a ^ 2 + (x : ℂ) ^ 2) / 2 - I * arctan (x / a) := by
    linear_combination (hsum - hdiff) / 2
  have hp : log (a + x * I) = log (a ^ 2 + (x : ℂ) ^ 2) / 2 + I * arctan (x / a) := by
    linear_combination (hsum + hdiff) / 2
  rw [cos, cpow_def_of_ne_zero hp0, cpow_def_of_ne_zero hm0,
    cpow_def_of_ne_zero hprod0, hm, hp]
  have he₁ : (log (a ^ 2 + (x : ℂ) ^ 2) / 2 - I * arctan (x / a)) * -s =
      -(log (a ^ 2 + (x : ℂ) ^ 2) * (s / 2)) + s * arctan (x / a) * I := by ring
  have he₂ : (log (a ^ 2 + (x : ℂ) ^ 2) / 2 + I * arctan (x / a)) * -s =
      -(log (a ^ 2 + (x : ℂ) ^ 2) * (s / 2)) + -(s * arctan (x / a) * I) := by ring
  rw [he₁, he₂, exp_add, exp_add]
  simp only [neg_mul, exp_neg]
  field_simp

/-- Principal powers on a vertical line in the right half-plane grow at most polynomially,
uniformly for exponents in a fixed ball. -/
theorem exists_bound_cpow_add_mul_I {a : ℂ} (ha : 0 < a.re) {M : ℝ} (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ s : ℂ, ‖s‖ ≤ M → ∀ x : ℝ,
      ‖(a + x * I) ^ s‖ ≤ C * (1 + |x|) ^ N := by
  obtain ⟨C, hC, N, hb⟩ := exists_bound_cpow_of_norm_bounds ha (norm_nonneg a) hM
  refine ⟨C, hC, N, fun s hs x => hb s hs (a + x * I) |x| (abs_nonneg x) ?_ ?_⟩
  · simpa using (re_le_norm (a + x * I))
  · simpa only [norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs] using
      norm_add_le a ((x : ℂ) * I)

/-- Differentiation of a principal power along a vertical line in the right half-plane. -/
theorem hasDerivAt_cpow_add_mul_I {a : ℂ} (ha : 0 < a.re) (s : ℂ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => (a + y * I) ^ s)
      (s * (a + x * I) ^ (s - 1) * I) x := by
  have hz : a + x * I ∈ slitPlane := by
    apply mem_slitPlane_iff.mpr
    left
    simpa using ha
  have hd := (((hasDerivAt_id (x : ℂ)).mul_const I).const_add a).cpow_const (c := s) hz
  convert! hd.comp_ofReal using 1; simp only [id_eq, one_mul]

/-- The sine-power kernel vanishes to first order at zero, with a polynomial bound at infinity,
uniformly for the exponent in a fixed ball. -/
theorem exists_bound_sin_mul_arctan_div_cpow {a : ℂ} (ha : 0 < a.re) {M : ℝ} (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ s : ℂ, ‖s‖ ≤ M → ∀ x : ℝ, 0 ≤ x →
      ‖sin (s * arctan (x / a)) / (a ^ 2 + (x : ℂ) ^ 2) ^ (s / 2)‖ ≤
        C * x * (1 + x) ^ N := by
  obtain ⟨C, hC, N, hbound⟩ := exists_bound_cpow_add_mul_I ha
    (M := M + 1) (by linarith)
  refine ⟨M * C, by positivity, N, ?_⟩
  intro s hs x hx
  have hs' : ‖-s - 1‖ ≤ M + 1 := by
    calc ‖-s - 1‖ ≤ ‖-s‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
         _ ≤ M + 1 := by simpa using add_le_add_right hs 1
  have hD (t : ℝ) (ht : t ∈ Icc (-x) x) :
      ‖(-s) * (a + t * I) ^ (-s - 1) * I‖ ≤ (M * C) * (1 + x) ^ N := by
    have ht' : |t| ≤ x := abs_le.mpr ht
    have hb := hbound (-s - 1) hs' t
    rw [norm_mul, norm_mul, norm_I, mul_one, norm_neg]
    calc
      ‖s‖ * ‖(a + t * I) ^ (-s - 1)‖ ≤ M * (C * (1 + |t|) ^ N) :=
        mul_le_mul hs hb (norm_nonneg _) hM
      _ ≤ M * (C * (1 + x) ^ N) := by gcongr
      _ = _ := by ring
  have hdiff := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t (_ : t ∈ Icc (-x) x) => (hasDerivAt_cpow_add_mul_I ha (-s) t).hasDerivWithinAt)
    hD (convex_Icc (-x) x) (show -x ∈ Icc (-x) x from ⟨le_rfl, by linarith⟩)
    (show x ∈ Icc (-x) x from ⟨by linarith, le_rfl⟩)
  rw [sin_mul_arctan_div_cpow ha, norm_div, norm_mul, norm_ofNat, norm_I, mul_one]
  have hn : ‖(a - x * I) ^ (-s) - (a + x * I) ^ (-s)‖ =
      ‖(a + x * I) ^ (-s) - (a + (-x : ℝ) * I) ^ (-s)‖ := by
    rw [norm_sub_rev]
    congr 2
    push_cast
    ring
  rw [hn, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  rw [Real.norm_eq_abs, show x - -x = 2 * x by ring, abs_of_nonneg (by positivity)] at hdiff
  nlinarith

/-- A polynomial bound for the cosine-arctangent kernel, uniform in bounded order. -/
theorem exists_bound_cos_mul_arctan_div_cpow {a : ℂ} (ha : 0 < a.re) {M : ℝ} (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ s : ℂ, ‖s‖ ≤ M → ∀ x : ℝ, 0 ≤ x →
      ‖cos (s * arctan (x / a)) / (a ^ 2 + (x : ℂ) ^ 2) ^ (s / 2)‖ ≤
        C * (1 + x) ^ N := by
  obtain ⟨C, hC, N, hb⟩ := exists_bound_cpow_add_mul_I ha hM
  refine ⟨C, hC, N, fun s hs x hx => ?_⟩
  rw [cos_mul_arctan_div_cpow ha, norm_div, norm_ofNat]
  have hp := hb (-s) (by simpa using hs) x
  have hm := hb (-s) (by simpa using hs) (-x)
  simp only [abs_of_nonneg hx] at hp
  simp only [ofReal_neg, neg_mul, ← sub_eq_add_neg, abs_neg, abs_of_nonneg hx] at hm
  have htri := norm_add_le ((a - x * I) ^ (-s)) ((a + x * I) ^ (-s))
  linarith

end Complex
