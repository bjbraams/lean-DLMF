/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.IntegralRepresentations
public import DLMF.Hypergeometric.Boundary

/-!
# Fractional integrals at the Gauss boundary

When the inner regularized Gauss series converges absolutely at one, its fractional
integral on the unit interval can be evaluated termwise by beta moments and Gauss summation.
This is the boundary form of DLMF 15.6.8 under `Re d > 0`, `Re(c-d) > 0`,
`Re(d-a-b) > 0`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory
open scoped Real Topology Nat

namespace DLMF.Hypergeometric

/-- The fractional integral at `z = 1`, when the inner Gauss series is absolutely convergent. -/
theorem fractional_integral_one {a b c d : ℂ} (hd : 0 < d.re)
    (hcd : 0 < (c - d).re) (hgap : 0 < (d - a - b).re) :
    (1 / Gamma (c - d)) * (∫ t : ℝ in (0 : ℝ)..1,
      regularizedGaussHGFun a b d t * (t : ℂ) ^ (d - 1) *
        (1 - (t : ℂ)) ^ (c - d - 1)) =
      Gamma (c - a - b) / (Gamma (c - a) * Gamma (c - b)) := by
  let w : ℝ → ℂ := fun t => (t : ℂ) ^ (d - 1) * (1 - (t : ℂ)) ^ (c - d - 1)
  let e : ℕ → ℂ := fun n => (ascPochhammer ℂ n).eval a * (ascPochhammer ℂ n).eval b /
    n.factorial * (Gamma (d + n))⁻¹
  let F : ℕ → ℝ → ℂ := fun n t => w t * (e n * (t : ℂ) ^ n)
  have hw : IntervalIntegrable w MeasureTheory.volume 0 1 := betaIntegral_convergent hd hcd
  have he : Summable (fun n => ‖e n‖) :=
      (hasSum_regularizedGauss_one hgap).summable.norm.congr (fun n => by
        simp only [e, pochhammer, div_eq_mul_inv, norm_mul, norm_inv]
        ring)
  have hFi (n : ℕ) : IntervalIntegrable (F n) MeasureTheory.volume 0 1 :=
    hw.mul_continuousOn (by fun_prop)
  have hs := intervalIntegral.hasSum_integral_of_dominated_convergence
    (a := (0 : ℝ)) (b := 1) (μ := MeasureTheory.volume)
    (F := F) (f := fun t => regularizedGaussHGFun a b d t * (t : ℂ) ^ (d - 1) *
      (1 - (t : ℂ)) ^ (c - d - 1))
    (fun n t => ‖e n‖ * ‖w t‖) (fun n => (hFi n).def'.aestronglyMeasurable)
    (fun n => Filter.Eventually.of_forall fun t ht => ?_)
    (Filter.Eventually.of_forall fun t _ => he.mul_right ‖w t‖)
    (by
      simp_rw [tsum_mul_right]
      exact hw.norm.const_mul _)
    (Filter.Eventually.of_forall fun t ht => ?_)
  · have hc0 : 0 < c.re := by
      have : c.re = d.re + (c - d).re := by simp
      linarith
    have hterm (n : ℕ) : ∫ t : ℝ in (0 : ℝ)..1, F n t = e n * betaIntegral (d + n) (c - d) := by
      rw [betaIntegral, ← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      intro t ht
      have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht.1)
      have hp : (t : ℂ) ^ (d + n - 1) = (t : ℂ) ^ (d - 1) * (t : ℂ) ^ n := by
        rw [show d + n - 1 = (d - 1) + n by ring, cpow_add _ _ ht0, cpow_natCast]
      simp only [F, w, e]
      rw [hp]
      ring
    have hdn (n : ℕ) : 0 < (d + n).re := by
      have : (d + n).re = d.re + n := by simp
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hscaled (n : ℕ) : 1 / Gamma (c - d) * (∫ t : ℝ in (0 : ℝ)..1, F n t) =
        (ascPochhammer ℂ n).eval a * (ascPochhammer ℂ n).eval b / n.factorial *
          (Gamma (c + n))⁻¹ := by
      have hB := Gamma_mul_Gamma_eq_betaIntegral (hdn n) hcd
      rw [show d + n + (c - d) = c + n by ring] at hB
      have hcn : Gamma (c + n) ≠ 0 := Gamma_ne_zero_of_re_pos (by
        have : (c + n).re = c.re + n := by simp
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith)
      have hdn0 : Gamma (d + n) ≠ 0 := Gamma_ne_zero_of_re_pos (hdn n)
      have hcd0 : Gamma (c - d) ≠ 0 := Gamma_ne_zero_of_re_pos hcd
      have hBeq : betaIntegral (d + n) (c - d) = Gamma (d + n) * Gamma (c - d) / Gamma (c + n) := by
        rw [eq_div_iff hcn, mul_comm]; exact hB.symm
      rw [hterm, hBeq]
      simp only [e]
      field_simp
    have hs' := hs.mul_left (1 / Gamma (c - d))
    simp_rw [hscaled] at hs'
    have hgapc : 0 < (c - a - b).re := by
      have he : (c - a - b).re = (c - d).re + (d - a - b).re := by simp; ring
      rw [he]; linarith
    exact hs'.unique (by
      convert hasSum_regularizedGauss_one hgapc using 1
      funext n
      simp only [pochhammer]
      ring)
  · rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    have ht1 : ‖(t : ℂ)‖ ≤ 1 := by
      simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1] using ht.2
    calc
      ‖F n t‖ = ‖w t‖ * (‖e n‖ * ‖(t : ℂ)‖ ^ n) := by
        simp only [F, norm_mul, norm_pow]
      _ ≤ ‖w t‖ * (‖e n‖ * 1) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) ht1) (norm_nonneg _))
          (norm_nonneg _)
      _ = _ := by ring
  · rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    have ht1 : ‖(t : ℂ)‖ ≤ 1 := by
      simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1] using ht.2
    have hsum : Summable (fun n : ℕ => e n * (t : ℂ)^n) := by
      apply Summable.of_norm
      apply he.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      rw [norm_mul, norm_pow]
      exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) ht1)
    have h' := hsum.hasSum.mul_left (w t)
    rw [regularizedGaussHypergeometricFun_eq_tsum]
    convert h' using 1
    have hseq : (∑' n : ℕ, (ascPochhammer ℂ n).eval a * (ascPochhammer ℂ n).eval b *
        (t : ℂ)^n / n.factorial * (Gamma (d+n))⁻¹) = ∑' n : ℕ, e n*(t : ℂ)^n := by
      apply tsum_congr
      intro n
      dsimp [e]
      ring
    rw [hseq]
    dsimp [w]
    ring


end DLMF.Hypergeometric
