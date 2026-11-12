/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Gamma.Asymptotics.Stirling
public import DLMF.Gamma.Basic.ScaledGamma

/-!
# First correction for ratios of scaled Gamma functions

Binet’s integral and its proved Watson expansion give the first correction for
`Γ*(x/ν)/Γ*(x)` along positive real rays. Mathlib’s exponential remainder estimate
controls exponentiation without changing the principal-power normalization.
-/

@[expose] public noncomputable section
open Complex Filter Asymptotics
open scoped Real Topology

namespace DLMF.Gamma

/-- The scaled Gamma function on the positive ray is the exponential of Binet’s integral. -/
lemma scaledGamma_ofReal_eq_exp_binetIntegral {x : ℝ} (hx : 0 < x) :
    scaledGamma x = Complex.exp (binetIntegral x) := by
  let L := (x - 1 / 2) * Real.log x - x + 1 / 2 * Real.log (2 * π)
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hq : (2 * π / (x : ℂ)) ≠ 0 := by
    exact div_ne_zero (by exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)) hx0
  have hden : Complex.exp (-(x : ℂ)) * (x : ℂ) ^ (x : ℂ) * (2 * π / (x : ℂ)) ^ (1 / 2 : ℂ) =
      Complex.exp (L : ℂ) := by
    rw [cpow_def_of_ne_zero hx0, cpow_def_of_ne_zero hq,
      ← ofReal_log hx.le,
      show (2 * π / (x : ℂ)) = ((2 * π / x : ℝ) : ℂ) by push_cast; rfl,
      ← ofReal_log (by positivity : (0 : ℝ)≤2 * π / x), Real.log_div (by positivity) hx.ne',
      ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    dsimp [L]
    push_cast
    ring
  have hnum : Complex.Gamma (x : ℂ) = Complex.exp (L : ℂ) * Complex.exp (binetIntegral x) := by
    rw [Complex.Gamma_ofReal, ← Complex.exp_add, ← ofReal_add, ← ofReal_exp]
    rw [← log_Gamma_eq_add_binetIntegral hx, Real.exp_log (Real.Gamma_pos_of_pos hx)]
  rw [scaledGamma, hden, hnum, mul_div_cancel_left₀ _ (Complex.exp_ne_zero _)]

/-- Binet’s integral has leading term `1/(12x)` with error `O(x⁻²)`. -/
lemma isBigO_binetIntegral_sub_inv :
    (fun x : ℝ => binetIntegral x - 1 / (12 * x)) =O[atTop] (fun x : ℝ => x⁻¹ ^ 2) := by
  have h := hasAsymptoticExpansion_binetIntegral 1
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, smul_eq_mul,
    Nat.cast_zero, zero_add, zero_mul, zero_sub, bernoulli_two, Real.rpow_neg_one] at h
  have he : ∀ᶠ x : ℝ in atTop, x ^ (-2 : ℝ) = x⁻¹ ^ 2 := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [show (-2 : ℝ)=-(2 : ℝ) by norm_num, Real.rpow_neg hx.le, Real.rpow_two]
    ring
  exact (h.congr' (Eventually.of_forall fun x => by ring) he)

/-- Binet’s integral is `O(1/x)` on the positive ray. -/
lemma isBigO_binetIntegral_inv : binetIntegral =O[atTop] (fun x : ℝ => x⁻¹) := by
  have h := hasAsymptoticExpansion_binetIntegral 0
  simpa only [Finset.sum_range_zero, sub_zero, Nat.cast_zero, zero_add, neg_one_mul,
    Real.rpow_neg_one] using h

/-- The difference of Binet integrals at proportional arguments is `O(1/x)`. -/
lemma isBigO_binetIntegral_div_sub {ν : ℝ} (hν : 0 < ν) :
    (fun x : ℝ => binetIntegral (x / ν) - binetIntegral x) =O[atTop] (fun x : ℝ => x⁻¹) := by
  have hs := isBigO_binetIntegral_inv.comp_tendsto (tendsto_id.atTop_div_const hν)
  have ht := hs.trans (isBigO_const_mul_self ν (fun x : ℝ => x⁻¹) atTop |>.congr_left
    (fun x => by simp [div_eq_mul_inv]))
  exact ht.sub isBigO_binetIntegral_inv

/-- First correction for Binet’s integral at two proportional arguments. -/
lemma isBigO_binetIntegral_div_sub_main {ν : ℝ} (hν : 0 < ν) :
    (fun x : ℝ => binetIntegral (x / ν) - binetIntegral x - (ν - 1) / (12 * x)) =O[atTop]
      (fun x : ℝ => x⁻¹ ^ 2) := by
  have hs := isBigO_binetIntegral_sub_inv.comp_tendsto (tendsto_id.atTop_div_const hν)
  have ht := hs.trans (isBigO_const_mul_self (ν ^ 2) (fun x : ℝ => x⁻¹ ^ 2) atTop |>.congr_left
    (fun x => by simp [div_eq_mul_inv, mul_pow]))
  exact (ht.sub isBigO_binetIntegral_sub_inv).congr_left fun x => by
    dsimp only [Function.comp_def, Pi.sub_apply, _root_.id]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, mul_comm x ν⁻¹]
    ring

/-- Exponentiation retains the first proportional-argument Binet correction. -/
lemma isBigO_exp_binetIntegral_div_sub_main {ν : ℝ} (hν : 0 < ν) :
    (fun x : ℝ => Real.exp (binetIntegral (x / ν) - binetIntegral x) - 1 -
      (ν - 1) / (12 * x)) =O[atTop]
      (fun x : ℝ => x⁻¹ ^ 2) := by
  have hB := isBigO_binetIntegral_div_sub hν
  have hT := hB.trans_tendsto tendsto_inv_atTop_zero
  have hE : (fun x : ℝ => Real.exp (binetIntegral (x / ν) - binetIntegral x) - 1-
      (binetIntegral (x / ν) - binetIntegral x)) =O[atTop]
        (fun x : ℝ => (binetIntegral (x / ν) - binetIntegral x) ^ 2) := by
    apply IsBigO.of_bound 1
    filter_upwards [hT.eventually (Metric.ball_mem_nhds 0 (by norm_num : (0 : ℝ) < 1))] with x hx
    have hsmall : ‖((binetIntegral (x / ν) - binetIntegral x) : ℝ)‖ ≤ 1 := by
      simpa only [Metric.mem_ball, dist_zero_right] using hx.le
    rw [one_mul, norm_pow]
    exact Real.norm_exp_sub_one_sub_id_le hsmall
  exact ((hE.trans (hB.pow 2)).add (isBigO_binetIntegral_div_sub_main hν)).congr_left fun x => by
    ring

/-- The ratio `Γ*(x/ν)/Γ*(x)` is `1 + (ν-1)/(12x) + O(x⁻²)` for `ν > 0`. -/
lemma isBigO_scaledGamma_div_sub_main {ν : ℝ} (hν : 0 < ν) :
    (fun x : ℝ => scaledGamma ((x / ν : ℝ) : ℂ) / scaledGamma (x : ℂ) - 1-
      ((ν : ℂ) - 1) / (12 * x)) =O[atTop] (fun x : ℝ => (x : ℂ)⁻¹ ^ 2) := by
  have h := Complex.isBigO_ofReal_right.mpr
    (Complex.isBigO_ofReal_left.mpr (isBigO_exp_binetIntegral_div_sub_main hν))
  apply h.congr'
  · filter_upwards [eventually_gt_atTop 0] with x hx
    rw [scaledGamma_ofReal_eq_exp_binetIntegral (div_pos hx hν),
      scaledGamma_ofReal_eq_exp_binetIntegral hx, ← Complex.exp_sub]
    push_cast
    rfl
  · exact Eventually.of_forall fun x => by push_cast; rfl

end DLMF.Gamma
