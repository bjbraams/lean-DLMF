/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.GeneralizedCalculus

/-!
# The Euler–Pochhammer integral for `ₚFq` (Duverney Thm 3.18; DLMF 16.5.2)

For `0 < Re a₀ < Re b₀` and `z` inside the disc of convergence of `𝐅(a; b)`,
`𝐅(a₀, a; b₀, b; z) = (Γ(a₀) Γ(b₀-a₀))⁻¹ ∫₀¹ t^{a₀-1} (1-t)^{b₀-a₀-1} 𝐅(a; b; zt) dt`,
by termwise integration (dominated convergence) and the Beta integral.
-/

@[expose] public section

open Complex Filter FormalMultilinearSeries MeasureTheory Set
open scoped Topology Nat

noncomputable section

namespace DLMF.Hypergeometric

/-- Adding a numerator `a₀` and a denominator `b₀` multiplies the coefficients by
`(a₀)ₙ/Γ(b₀+n)`. -/
theorem regularizedHGFunCoeff_cons (a₀ b₀ : ℂ) (a b : Multiset ℂ) (n : ℕ) :
    regularizedHGFunCoeff (a₀ ::ₘ a) (b₀ ::ₘ b) n =
      poch a₀ n / Gamma (b₀ + n) * regularizedHGFunCoeff a b n := by
  simp only [regularizedHGFunCoeff, Multiset.map_cons, Multiset.prod_cons, poch]
  rw [div_mul_div_comm]
  ring_nf

/-- **The Euler–Pochhammer integral** (Duverney Thm 3.18; DLMF 16.5.2): for
`0 < Re a₀ < Re b₀` and `z` inside the disc of convergence of `𝐅(a; b)`,
`𝐅(a₀, a; b₀, b; z) = (Γ(a₀) Γ(b₀-a₀))⁻¹ ∫₀¹ t^{a₀-1} (1-t)^{b₀-a₀-1} 𝐅(a; b; zt) dt`. -/
@[dlmf 16.5.E2]
theorem regularizedHGFun_cons_eq_integral {a₀ b₀ : ℂ} (ha : 0 < a₀.re) (hab : 0 < (b₀ - a₀).re)
    (a b : Multiset ℂ) {z : ℂ}
    (hz : (‖z‖₊ : ENNReal) < (regularizedHGFunSeries a b).radius) :
    regularizedHGFun (a₀ ::ₘ a) (b₀ ::ₘ b) z =
      (Gamma a₀ * Gamma (b₀ - a₀))⁻¹ * ∫ t : ℝ in (0 : ℝ)..1,
        (t : ℂ) ^ (a₀ - 1) * (1 - (t : ℂ)) ^ (b₀ - a₀ - 1) * regularizedHGFun a b (z * t) := by
  set S := regularizedHGFunCoeff a b
  set w : ℝ → ℂ := fun t => (t : ℂ) ^ (a₀ - 1) * (1 - (t : ℂ)) ^ (b₀ - a₀ - 1)
  have hw : IntervalIntegrable w volume 0 1 := betaIntegral_convergent ha hab
  have hr : 0 < (regularizedHGFunSeries a b).radius := lt_of_le_of_lt zero_le hz
  have hP : HasFPowerSeriesOnBall (regularizedHGFun a b) (ofScalars ℂ S) 0
      (regularizedHGFunSeries a b).radius :=
    (regularizedHGFunSeries a b).hasFPowerSeriesOnBall hr
  have hsum : Summable fun n : ℕ => ‖S n‖ * ‖z‖ ^ n := by
    have := (regularizedHGFunSeries a b).summable_norm_mul_pow hz
    simpa [regularizedHGFunSeries, ofScalars_norm] using this
  have hmem (t : ℝ) (ht : t ∈ uIoc (0 : ℝ) 1) :
      z * t ∈ Metric.eball (0 : ℂ) (regularizedHGFunSeries a b).radius := by
    rw [uIoc_of_le zero_le_one] at ht
    rw [Metric.mem_eball, edist_zero_right]
    refine lt_of_le_of_lt ?_ hz
    rw [enorm_eq_nnnorm, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm,
      norm_mul, norm_real, Real.norm_of_nonneg ht.1.le]
    nlinarith [norm_nonneg z, ht.2]
  have hint := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := volume) (a := 0) (b := 1)
    (F := fun (n : ℕ) (t : ℝ) => w t * (S n * (z * t) ^ n))
    (f := fun t : ℝ => w t * regularizedHGFun a b (z * t))
    (fun n t => ‖S n‖ * ‖z‖ ^ n * ‖w t‖)
    (fun n => by
      rw [uIoc_of_le zero_le_one]
      exact hw.1.aestronglyMeasurable.mul (by fun_prop : Continuous fun t : ℝ =>
        S n * (z * (t : ℂ)) ^ n).aestronglyMeasurable)
    (fun n => (Eventually.of_forall fun t ht => by
      rw [uIoc_of_le zero_le_one] at ht
      show ‖w t * (S n * (z * t) ^ n)‖ ≤ ‖S n‖ * ‖z‖ ^ n * ‖w t‖
      have hS : ‖S n * (z * t) ^ n‖ ≤ ‖S n‖ * ‖z‖ ^ n := by
        rw [norm_mul, norm_pow, norm_mul, norm_real, Real.norm_of_nonneg ht.1.le]
        have h0 : 0 ≤ ‖z‖ * t := mul_nonneg (norm_nonneg z) ht.1.le
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0
          (by nlinarith [norm_nonneg z, ht.2]) n) (norm_nonneg _)
      calc ‖w t * (S n * (z * t) ^ n)‖ = ‖w t‖ * ‖S n * (z * t) ^ n‖ := norm_mul _ _
        _ ≤ ‖w t‖ * (‖S n‖ * ‖z‖ ^ n) := by gcongr
        _ = ‖S n‖ * ‖z‖ ^ n * ‖w t‖ := by ring))
    (Eventually.of_forall fun t _ => hsum.mul_right _)
    (by
      simp_rw [tsum_mul_right]
      exact (hw.norm).const_mul _)
    (Eventually.of_forall fun t ht => (hP.hasSum_mul_pow (hmem t ht)).mul_left (w t))
  have hΓa : Gamma a₀ ≠ 0 := Gamma_ne_zero_of_re_pos ha
  have hΓb : Gamma (b₀ - a₀) ≠ 0 := Gamma_ne_zero_of_re_pos hab
  have hterm (n : ℕ) : (Gamma a₀ * Gamma (b₀ - a₀))⁻¹ *
      ∫ t : ℝ in (0 : ℝ)..1, w t * (S n * (z * t) ^ n) =
        regularizedHGFunCoeff (a₀ ::ₘ a) (b₀ ::ₘ b) n * z ^ n := by
    have hn : 0 < (a₀ + n).re := by simp; linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]
    have hbn : 0 < (b₀ + n).re := by
      have : 0 < b₀.re := by have := hab; simp at this; linarith
      simp; linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]
    have hcongr : ∫ t : ℝ in (0 : ℝ)..1, w t * (S n * (z * t) ^ n) =
        S n * z ^ n * betaIntegral (a₀ + n) (b₀ - a₀) := by
      rw [betaIntegral, ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun t ht => ?_)
      rw [uIoc_of_le zero_le_one] at ht
      have h0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.1.ne'
      simp only [w]
      rw [show a₀ + n - 1 = (a₀ - 1) + (n : ℂ) by ring, cpow_add _ _ h0, cpow_natCast]
      ring
    have hB := Gamma_mul_Gamma_eq_betaIntegral hn hab
    rw [show a₀ + n + (b₀ - a₀) = b₀ + n by ring] at hB
    have hΓbn : Gamma (b₀ + n) ≠ 0 := Gamma_ne_zero_of_re_pos hbn
    have hpoch : Gamma (a₀ + n) = poch a₀ n * Gamma a₀ := by
      rw [poch, ← Complex.Gamma_add_nat_div_Gamma_eq a₀ (fun k hk => by
        have := congrArg re hk; simp at this; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)])]
      field_simp
    rw [hcongr, regularizedHGFunCoeff_cons,
      show betaIntegral (a₀ + n) (b₀ - a₀) = Gamma (a₀ + n) * Gamma (b₀ - a₀) / Gamma (b₀ + n) by
        rw [hB]; field_simp, hpoch]
    field_simp
    simp only [S]; ring
  have hfin := hint.mul_left (Gamma a₀ * Gamma (b₀ - a₀))⁻¹
  simp_rw [hterm] at hfin
  rw [regularizedHGFun_eq_tsum', hfin.tsum_eq]

end DLMF.Hypergeometric

end
