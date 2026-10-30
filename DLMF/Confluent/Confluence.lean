/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.KummerProperties

/-!
# Confluence with a shifted large parameter

The Gauss upper parameter may have a fixed complex shift while its real part tends
to infinity. Mathlib's dominated convergence theorem for series passes the
coefficient limit through the sum, using a fixed positive Gauss majorant.
-/

@[expose] public section

open Complex Filter
open scoped Real Topology
open DLMF.Hypergeometric

noncomputable section

namespace DLMF.Confluent

/-- Normalize Gauss coefficients by an independent scaling parameter. -/
private lemma gaussHGCoeff_mul_scaled_pow (a b c z t : ℂ) (n : ℕ) :
    gaussHGCoeff a b c n * (z / t) ^ n =
      (kummerMCoeff a c n * z ^ n) * (poch b n / t ^ n) := by
  simp only [gaussHGCoeff, kummerMCoeff, div_eq_mul_inv, mul_inv_rev]
  ring

/-- A fixed positive shifted Pochhammer majorizes every sufficiently large parameter. -/
theorem norm_poch_add_div_pow_le (d : ℂ) {T t : ℝ} (hT : 0 < T) (ht : T ≤ t) (n : ℕ) :
    ‖poch (d + t) n / (t : ℂ) ^ n‖ ≤
      ‖poch ((T + ‖d‖ : ℝ) : ℂ) n / (T : ℂ) ^ n‖ := by
  have ht0 : 0 < t := hT.trans_le ht
  have hnorm (n : ℕ) : ‖1 + ((‖d‖ : ℂ) + n) / (T : ℂ)‖ =
      1 + (‖d‖ + n) / T := by
    rw [show (1 : ℂ) + ((‖d‖ : ℂ) + n) / (T : ℂ) =
      ((1 + (‖d‖ + n) / T : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  induction n with
  | zero => simp [poch_zero]
  | succ n ih =>
    have hrec (c : ℂ) (x : ℝ) (hx : 0 < x) :
        poch (c + x) (n + 1) / (x : ℂ) ^ (n + 1) =
          poch (c + x) n / (x : ℂ) ^ n * (1 + (c + n) / (x : ℂ)) := by
      rw [poch_succ, pow_succ]
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
  let F (t : ℝ) (n : ℕ) := gaussHGCoeff a (d + t) c n * (z / t) ^ n
  let G (n : ℕ) := ‖gaussHGCoeff a ((T + ‖d‖ : ℝ) : ℂ) c n * (z / T) ^ n‖
  have hG : Summable G := ((hasFPowerSeriesOnBall_ordinaryHypergeometric a
    ((T + ‖d‖ : ℝ) : ℂ) c).hasSum_mul_pow
      (mem_eball_one_of_norm_lt_one harg)).summable.norm
  have hlim (n : ℕ) : Tendsto (fun t => F t n) atTop
      (𝓝 (kummerMCoeff a c n * z ^ n)) := by
    simpa only [F, gaussHGCoeff_mul_scaled_pow, mul_one] using
      (tendsto_poch_add_div_pow d n).const_mul (kummerMCoeff a c n * z ^ n)
  have hbound : ∀ᶠ t : ℝ in atTop, ∀ n, ‖F t n‖ ≤ G n := by
    filter_upwards [eventually_ge_atTop T] with t ht n
    dsimp only [F, G]
    simp only [gaussHGCoeff_mul_scaled_pow, norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_poch_add_div_pow_le d hT ht n) (by positivity)
  have he (t : ℝ) : ₂F₁ a (d + t) c (z / t) = ∑' n, F t n := by
    rw [ordinaryHypergeometric_eq_tsum]
    apply tsum_congr
    intro n
    simp only [F, gaussHGCoeff, poch, smul_eq_mul, div_eq_mul_inv, mul_inv_rev]
    ring
  simpa only [← he, kummerM, kummerMCoeff] using
    tendsto_tsum_of_dominated_convergence hG hlim hbound

end DLMF.Confluent
