/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.KummerProperties

/-!
# Confluence of Gauss's function with a shifted large parameter

This file proves the confluence limit `₂F₁(a, d + t; c; z/t) → M(a,c,z)` as the real parameter
`t` tends to infinity, with a fixed complex shift `d` of the large upper parameter.

## Main results

* `tendsto_ordinaryHypergeometric_add_div_atTop`: Gauss confluence with a fixed complex shift
  of the large real upper parameter.
* `norm_pochhammer_add_div_pow_le`: a fixed positive shifted Pochhammer symbol majorizes the
  normalized coefficients for all sufficiently large parameters.

## Implementation notes

Mathlib's dominated convergence theorem for series passes the coefficient limit through the
sum, using a fixed positive Gauss majorant.
-/

@[expose] public section

open Complex Filter
open scoped Real Topology
open DLMF.Hypergeometric

noncomputable section

namespace DLMF.Confluent

/-- Normalize Gauss coefficients by an independent scaling parameter. -/
private lemma gaussHypergeometricCoeff_mul_scaled_pow (a b c z t : ℂ) (n : ℕ) :
    gaussHypergeometricCoeff a b c n * (z / t) ^ n =
      (kummerMCoeff a c n * z ^ n) * (pochhammer b n / t ^ n) := by
  simp only [gaussHypergeometricCoeff, kummerMCoeff, div_eq_mul_inv, mul_inv_rev]
  ring

/-- A fixed positive shifted Pochhammer majorizes every sufficiently large parameter. -/
theorem norm_pochhammer_add_div_pow_le (d : ℂ) {T t : ℝ} (hT : 0 < T) (ht : T ≤ t) (n : ℕ) :
    ‖pochhammer (d + t) n / (t : ℂ) ^ n‖ ≤
      ‖pochhammer ((T + ‖d‖ : ℝ) : ℂ) n / (T : ℂ) ^ n‖ := by
  have ht0 : 0 < t := hT.trans_le ht
  have hnorm (n : ℕ) : ‖1 + ((‖d‖ : ℂ) + n) / (T : ℂ)‖ =
      1 + (‖d‖ + n) / T := by
    rw [show (1 : ℂ) + ((‖d‖ : ℂ) + n) / (T : ℂ) =
      ((1 + (‖d‖ + n) / T : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  induction n with
  | zero => simp [pochhammer_zero]
  | succ n ih =>
    have hrec (c : ℂ) (x : ℝ) (hx : 0 < x) :
        pochhammer (c + x) (n + 1) / (x : ℂ) ^ (n + 1) =
          pochhammer (c + x) n / (x : ℂ) ^ n * (1 + (c + n) / (x : ℂ)) := by
      rw [pochhammer_succ, pow_succ]
      field_simp [ofReal_ne_zero.mpr hx.ne']
      ring
    rw [show ((T + ‖d‖ : ℝ) : ℂ) = (‖d‖ : ℂ) + T by push_cast; ring] at ih
    rw [hrec d t ht0, show ((T + ‖d‖ : ℝ) : ℂ) = (‖d‖ : ℂ) + T by push_cast; ring,
      hrec (‖d‖ : ℂ) T hT, norm_mul, norm_mul, hnorm]
    apply mul_le_mul ih _ (by positivity) (norm_nonneg _)
    calc
      _ ≤ 1 + ‖(d + n) / (t : ℂ)‖ := by
        simpa only [norm_one] using norm_add_le (1 : ℂ) ((d + n) / (t : ℂ))
      _ ≤ 1 + (‖d‖ + n) / t := by
        rw [norm_div, Complex.norm_real, Real.norm_of_nonneg ht0.le]
        gcongr
        simpa using norm_add_le d (n : ℂ)
      _ ≤ _ := by gcongr

/-- Gauss confluence with a fixed complex shift of the large real upper parameter. -/
theorem tendsto_ordinaryHypergeometric_add_div_atTop (a c d z : ℂ) :
    Tendsto (fun t : ℝ => ₂F₁ a (d + t) c (z / t)) atTop (𝓝 (kummerM a c z)) := by
  let T : ℝ := ‖z‖ + 1
  have hT : 0 < T := by dsimp [T]; positivity
  have harg : ‖z / (T : ℂ)‖ < 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hT.le, div_lt_one hT]
    dsimp [T]
    linarith
  let F (t : ℝ) (n : ℕ) := gaussHypergeometricCoeff a (d + t) c n * (z / t) ^ n
  let G (n : ℕ) := ‖gaussHypergeometricCoeff a ((T + ‖d‖ : ℝ) : ℂ) c n * (z / T) ^ n‖
  have hG : Summable G := ((hasFPowerSeriesOnBall_ordinaryHypergeometric a
    ((T + ‖d‖ : ℝ) : ℂ) c).hasSum_mul_pow
      (mem_eball_one_of_norm_lt_one harg)).summable.norm
  have hlim (n : ℕ) : Tendsto (fun t => F t n) atTop
      (𝓝 (kummerMCoeff a c n * z ^ n)) := by
    simpa only [F, gaussHypergeometricCoeff_mul_scaled_pow, mul_one] using
      (tendsto_pochhammer_add_div_pow d n).const_mul (kummerMCoeff a c n * z ^ n)
  have hbound : ∀ᶠ t : ℝ in atTop, ∀ n, ‖F t n‖ ≤ G n := by
    filter_upwards [eventually_ge_atTop T] with t ht n
    dsimp only [F, G]
    simp only [gaussHypergeometricCoeff_mul_scaled_pow, norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_pochhammer_add_div_pow_le d hT ht n) (by positivity)
  have he (t : ℝ) : ₂F₁ a (d + t) c (z / t) = ∑' n, F t n := by
    rw [ordinaryHypergeometric_eq_tsum]
    apply tsum_congr
    intro n
    simp only [F, gaussHypergeometricCoeff, pochhammer, smul_eq_mul, div_eq_mul_inv, mul_inv_rev]
    ring
  simpa only [← he, kummerM, kummerMCoeff] using
    tendsto_tsum_of_dominated_convergence hG hlim hbound

end DLMF.Confluent
