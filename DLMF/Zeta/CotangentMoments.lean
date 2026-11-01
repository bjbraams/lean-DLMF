/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Zeta.IntegerArguments

/-!
# A cotangent moment for the zeta summation formula 25.8.10

A quadratic moment of `cot(πx)` over a half interval, needed for the summation formula
DLMF 25.8.10. Reflection and duplication reduce it to the Bernoulli-cotangent integral
for `ζ(3)`.

## Main results

* `integral_quadratic_mul_cot_pi`: the quadratic cotangent moment occurring after twice
  integrating the even-zeta series.
-/

@[expose] public noncomputable section

open Complex Filter Topology MeasureTheory Set Finset
open scoped Real Nat

namespace DLMF.Zeta

/-- The quadratic cotangent moment occurring after twice integrating the even-zeta series. -/
theorem integral_quadratic_mul_cot_pi
    (hbound : ∀ x ∈ Set.Icc (0 : ℝ) (1 / 2), |π * x * Real.cot (π * x)| ≤ 1) :
    IntervalIntegrable (fun x : ℝ => (x / 2 - x ^ 2) * Real.cot (π * x)) volume 0 (1 / 2) ∧
      (∫ x in (0 : ℝ)..(1 / 2), ((x / 2 - x ^ 2) * Real.cot (π * x) : ℝ) : ℂ) =
        7 * riemannZeta 3 / (8 * π ^ 3) := by
  let P : ℝ → ℝ := fun x => x ^ 3 - 3 / 2 * x ^ 2 + x / 2
  have hP : ∀ x : ℝ, bernoulliFun 3 x = P x := by
    intro x
    norm_num [bernoulliFun, Polynomial.bernoulli_def, sum_range_succ, P,
      bernoulli_eq_bernoulli'_of_ne_one, bernoulli'_zero, bernoulli'_two, bernoulli'_three]
    ring
  have hW : IntervalIntegrable (fun x : ℝ => π * x * Real.cot (π * x)) volume 0 (1 / 2) := by
    refine (intervalIntegrable_const (c := (1 : ℝ))).mono_fun' ?_ ?_
    · simp only [Real.cot_eq_cos_div_sin]
      exact (by fun_prop : Measurable fun x : ℝ =>
        π * x * (Real.cos (π * x) / Real.sin (π * x))).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_uIoc] with x hx
      rw [Set.uIoc_of_le (by norm_num)] at hx
      exact hbound x ⟨hx.1.le, hx.2⟩
  have hi (r : ℕ) : IntervalIntegrable (fun x : ℝ => x ^ (r + 1) * Real.cot (π * x))
      volume 0 (1 / 2) := by
    have h := (hW.continuousOn_mul (by fun_prop : ContinuousOn (fun x : ℝ => x ^ r)
      (uIcc (0 : ℝ) (1 / 2)))).const_mul π⁻¹
    convert h using 1
    funext x
    field_simp
    ring
  have hi1 := hi 0
  simp only [zero_add, pow_one] at hi1
  have hi2 := hi 1
  have hi3 := hi 2
  have hPf : IntervalIntegrable (fun x : ℝ => P x * Real.cot (π * x)) volume 0 (1 / 2) := by
    convert (hi3.sub (hi2.const_mul (3 / 2))).add (hi1.div_const 2) using 1
    funext x; dsimp [P]; ring
  have hP2 : IntervalIntegrable (fun x : ℝ => P (2 * x) * Real.cot (π * x)) volume 0 (1 / 2) := by
    convert ((hi3.const_mul 8).sub (hi2.const_mul 6)).add hi1 using 1
    funext x; dsimp [P]; ring
  have hζ := riemannZeta_two_mul_add_one_eq_integral (k := 1) (by norm_num)
  norm_num only [Nat.mul_one, Nat.reduceAdd, Nat.factorial, Nat.reducePow,
    Nat.cast_ofNat, one_add_one_eq_two] at hζ
  simp only [hP] at hζ
  let H : ℝ := ∫ x in (0 : ℝ)..1, P x * Real.cot (π * x)
  have hreflect (x : ℝ) : P (1 - x) * Real.cot (π * (1 - x)) = P x * Real.cot (π * x) := by
    rw [show π * (1 - x) = π - π * x by ring, Real.cot_eq_cos_div_sin,
      Real.cos_pi_sub, Real.sin_pi_sub, Real.cot_eq_cos_div_sin]
    dsimp [P]; ring
  have hR : (∫ x in (1 / 2 : ℝ)..1, P x * Real.cot (π * x)) =
      ∫ x in (0 : ℝ)..(1 / 2), P x * Real.cot (π * x) := by
    have h := intervalIntegral.integral_comp_sub_left (fun x : ℝ => P x * Real.cot (π * x))
      1 (a := 1 / 2) (b := 1)
    simp only [hreflect] at h
    norm_num at h
    exact h
  have hH : H = 2 * ∫ x in (0 : ℝ)..(1 / 2), P x * Real.cot (π * x) := by
    have hr : IntervalIntegrable (fun x : ℝ => P x * Real.cot (π * x)) volume (1 / 2) 1 :=
      hζ.1.mono_set (by
        norm_num only [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1),
          Set.uIcc_of_le zero_le_one]
        exact Set.Icc_subset_Icc (by norm_num) le_rfl)
    have h := intervalIntegral.integral_add_adjacent_intervals hPf hr
    change _ = H at h
    rw [hR] at h
    linarith
  have hdup {x : ℝ} (hx : 0 < x) (hx1 : x < 1 / 2) :
      2 * (P (2 * x) * Real.cot (π * (2 * x))) =
        P (2 * x) * Real.cot (π * x) +
          P (2 * (1 / 2 - x)) * Real.cot (π * (1 / 2 - x)) := by
    have hs : Real.sin (π * x) ≠ 0 :=
      (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])).ne'
    have hc : Real.cos (π * x) ≠ 0 :=
      (Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩).ne'
    rw [show π * (2 * x) = 2 * (π * x) by ring,
      show π * (1 / 2 - x) = π / 2 - π * x by ring]
    simp only [Real.cot_eq_cos_div_sin, Real.sin_two_mul, Real.cos_two_mul,
      Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]
    dsimp [P]
    have hs' : Real.sin (x * π) ≠ 0 := by simpa [mul_comm] using hs
    have hc' : Real.cos (x * π) ≠ 0 := by simpa [mul_comm] using hc
    field_simp [hs, hc, hs', hc']
    linear_combination (2 * ((2 * x) ^ 3 - 3 / 2 * (2 * x) ^ 2 + (2 * x) / 2)) *
      Real.sin_sq_add_cos_sq (x * π)
  have hD : H = 2 * ∫ x in (0 : ℝ)..(1 / 2), P (2 * x) * Real.cot (π * x) := by
    have heq : (∫ x in (0 : ℝ)..(1 / 2), 2 * (P (2 * x) * Real.cot (π * (2 * x)))) =
        ∫ x in (0 : ℝ)..(1 / 2), P (2 * x) * Real.cot (π * x) +
          P (2 * (1 / 2 - x)) * Real.cot (π * (1 / 2 - x)) := by
      refine intervalIntegral.integral_congr_ae ?_
      have hne : ∀ᵐ x : ℝ ∂volume, x ≠ 1 / 2 := by rw [ae_iff]; simp
      filter_upwards [hne] with x hx hxmem
      rw [Set.uIoc_of_le (by norm_num)] at hxmem
      exact hdup hxmem.1 (lt_of_le_of_ne hxmem.2 hx)
    have hcomp := intervalIntegral.integral_comp_mul_left
      (fun x : ℝ => P x * Real.cot (π * x)) (by norm_num : (2 : ℝ) ≠ 0)
      (a := 0) (b := 1 / 2)
    have href := intervalIntegral.integral_comp_sub_left
      (fun x : ℝ => P (2 * x) * Real.cot (π * x)) (1 / 2) (a := 0) (b := 1 / 2)
    norm_num at hcomp href
    rw [intervalIntegral.integral_const_mul, hcomp] at heq
    have hr : IntervalIntegrable (fun x : ℝ => P (2 * (1 / 2 - x)) *
        Real.cot (π * (1 / 2 - x))) volume 0 (1 / 2) := by
      simpa using (hP2.comp_sub_left (1 / 2)).symm
    rw [intervalIntegral.integral_add hP2 hr, href] at heq
    change 2 * ((1 / 2 : ℝ) * H) = _ at heq
    linarith
  have hJ : (∫ x in (0 : ℝ)..(1 / 2), (x / 2 - x ^ 2) * Real.cot (π * x)) = 7 * H / 12 := by
    have heP : (fun x : ℝ => P x * Real.cot (π * x)) = fun x =>
        (x ^ 3 * Real.cot (π * x) - 3 / 2 * (x ^ 2 * Real.cot (π * x))) +
          (x * Real.cot (π * x)) / 2 := by funext x; dsimp [P]; ring
    have heP2 : (fun x : ℝ => P (2 * x) * Real.cot (π * x)) = fun x =>
        (8 * (x ^ 3 * Real.cot (π * x)) - 6 * (x ^ 2 * Real.cot (π * x))) +
          (x * Real.cot (π * x)) := by funext x; dsimp [P]; ring
    rw [heP, intervalIntegral.integral_add (hi3.sub (hi2.const_mul (3 / 2))) (hi1.div_const 2),
      intervalIntegral.integral_sub hi3 (hi2.const_mul (3 / 2)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_div] at hH
    rw [heP2, intervalIntegral.integral_add ((hi3.const_mul 8).sub (hi2.const_mul 6)) hi1,
      intervalIntegral.integral_sub (hi3.const_mul 8) (hi2.const_mul 6),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hD
    have he : (fun x : ℝ => (x / 2 - x ^ 2) * Real.cot (π * x)) =
        fun x => x * Real.cot (π * x) / 2 - x ^ 2 * Real.cot (π * x) := by funext x; ring
    rw [he, intervalIntegral.integral_sub (hi1.div_const 2) hi2,
      intervalIntegral.integral_div]
    linear_combination (hD - 8 * hH) / 12
  refine ⟨?_, ?_⟩
  · convert (hi1.div_const 2).sub hi2 using 1
    funext x; ring
  · rw [intervalIntegral.integral_ofReal, hJ]
    have hv := hζ.2
    change riemannZeta 3 = ((_ : ℝ) : ℂ) at hv
    push_cast at hv ⊢
    have hp : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp
    linear_combination -12 * hv

end DLMF.Zeta
