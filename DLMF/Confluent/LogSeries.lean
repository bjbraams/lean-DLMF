/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module
public import DLMF.Confluent.ParameterDerivatives

/-!
# The analytic part of the integer-parameter Tricomi expansion

At a positive integer second parameter the logarithmic expansion of Tricomi's `U` separates
into `log z` times a regularized Kummer function and an ordinary power series. This file defines
that power series and proves its convergence and analyticity at zero, which supply the
small-argument remainder estimates.

## Main definitions

* `tricomiLogSeriesCoeff`, `tricomiLogSeries`: the analytic part accompanying `log z`.
* `tricomiLogSeriesRecipGammaCoeff`, `tricomiLogSeriesRecipGamma`: the same multiplied by
  `1/Γ(a-n)`, with `ψ(a+k)/Γ(a-n)` written through the derivative of `1/Γ`.

## Main results

* `summable_tricomiLogSeries`, `analyticAt_tricomiLogSeries`: convergence and analyticity at
  zero.
* `tricomi_log_series_split`: separation of the logarithm from the convergent series.
* `summable_tricomiLogSeriesRecipGamma`, `analyticAt_tricomiLogSeriesRecipGamma`: the same for
  the reciprocal-Gamma form, for all `a`.
* `tricomiLogSeriesRecipGamma_eq`: away from the poles of `Γ(a-n)` the two forms agree up to
  the factor `1/Γ(a-n)`.
* `tricomi_log_series_split_recipGamma`: the splitting in reciprocal-Gamma form, valid for
  all `a`.

## Implementation notes

Convergence is proved by differentiating Kummer's series in its parameters.
-/

@[expose] public section
open Complex Filter Set FormalMultilinearSeries DLMF.Hypergeometric
open scoped Real Nat Topology ENNReal
noncomputable section
set_option autoImplicit false
namespace DLMF.Confluent

open DLMF.Gamma

/-- Coefficients of the analytic part of the integer-parameter logarithmic expansion. -/
def tricomiLogSeriesCoeff (a : ℂ) (n k : ℕ) : ℂ :=
  poch a k / k.factorial * (Gamma ((n : ℂ) + 1 + k))⁻¹ *
    (digamma (a + k) - digamma (k + 1) - digamma ((n : ℂ) + 1 + k))

/-- The analytic part that accompanies `log z` in the integer-parameter U expansion. -/
def tricomiLogSeries (a : ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  ∑' k : ℕ, tricomiLogSeriesCoeff a n k * z ^ k

/-- Parameter differentiation gives absolute convergence of the analytic logarithmic part. -/
theorem summable_tricomiLogSeries (a : ℂ) (n : ℕ) {z : ℂ} (hz : z ≠ 0)
    (ha : ∀ k : ℕ, a - n ≠ -(k : ℂ)) :
    Summable (fun k : ℕ => tricomiLogSeriesCoeff a n k * z ^ k) := by
  have h := (tricomi_numerator_nat_series a n hz ha).1.sub
    ((summable_regularizedConfluent_term a ((n : ℂ) + 1) z).mul_right (log z))
  refine h.congr fun k => ?_
  dsimp only [tricomiLogSeriesCoeff]
  ring

/-- The ordinary power series part is analytic at zero. -/
theorem analyticAt_tricomiLogSeries (a : ℂ) (n : ℕ)
    (ha : ∀ k : ℕ, a - n ≠ -(k : ℂ)) :
    AnalyticAt ℂ (tricomiLogSeries a n) 0 := by
  let p := ofScalars ℂ (tricomiLogSeriesCoeff a n)
  have hs := (summable_tricomiLogSeries a n (z := 2) (by norm_num) ha).norm
  have hr : (2 : ENNReal) ≤ p.radius := by
    apply p.le_radius_of_summable_norm (r := 2)
    simpa only [p, ofScalars_norm, norm_mul, norm_pow, Complex.norm_ofNat,
      NNReal.coe_ofNat] using hs
  have hp := p.hasFPowerSeriesOnBall (lt_of_lt_of_le (by norm_num : (0 : ENNReal) < 2) hr)
  have heq : p.sum = tricomiLogSeries a n := by
    funext z
    simp only [p, FormalMultilinearSeries.sum, ofScalars_apply_eq, smul_eq_mul, tricomiLogSeries]
  rw [heq] at hp
  exact hp.analyticAt

/-- Constant term of the analytic logarithmic part. -/
theorem tricomiLogSeries_zero (a : ℂ) (n : ℕ) :
    tricomiLogSeries a n 0 = (Gamma ((n : ℂ) + 1))⁻¹ *
      (digamma a - digamma 1 - digamma ((n : ℂ) + 1)) := by
  unfold tricomiLogSeries
  rw [tsum_eq_single 0]
  · simp [tricomiLogSeriesCoeff, poch_zero]
  · intro k hk
    simp [zero_pow hk]

/-- Separation of the logarithm from the convergent integer-parameter series. -/
theorem tricomi_log_series_split (a : ℂ) (n : ℕ) {z : ℂ} (hz : z ≠ 0)
    (ha : ∀ k : ℕ, a - n ≠ -(k : ℂ)) :
    (∑' k : ℕ, (poch a k * z ^ k / k.factorial * (Gamma ((n : ℂ) + 1 + k))⁻¹) *
      (log z + digamma (a + k) - digamma (k + 1) - digamma ((n : ℂ) + 1 + k))) =
      log z * regularizedHGFun {a} {(n : ℂ) + 1} z + tricomiLogSeries a n z := by
  have hM := (summable_regularizedConfluent_term a ((n : ℂ) + 1) z).mul_left (log z)
  have hT := summable_tricomiLogSeries a n hz ha
  rw [regularizedConfluent_eq_tsum, tricomiLogSeries, ← tsum_mul_left, ← hM.tsum_add hT]
  refine tsum_congr fun k => ?_
  dsimp only [tricomiLogSeriesCoeff]
  ring

/-- Coefficients of the analytic logarithmic part multiplied by `1/Γ(a-n)`, with
`ψ(a+k)/Γ(a-n)` written as `-(a-n)_{n+k} (1/Γ)'(a+k)`; meaningful for all `a`. -/
def tricomiLogSeriesRecipGammaCoeff (a : ℂ) (n k : ℕ) : ℂ :=
  poch a k / k.factorial * (Gamma ((n : ℂ) + 1 + k))⁻¹ *
    (-((Gamma (a - n))⁻¹ * (digamma (k + 1) + digamma ((n : ℂ) + 1 + k))) -
      poch (a - n) (n + k) * recipGammaDeriv 1 (a + k))

/-- The analytic part accompanying `log z` in the integer-parameter U expansion, multiplied by
`1/Γ(a-n)`; it equals `tricomiLogSeries a n z / Γ(a-n)` when `a - n` is not a pole. -/
def tricomiLogSeriesRecipGamma (a : ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  ∑' k : ℕ, tricomiLogSeriesRecipGammaCoeff a n k * z ^ k

/-- Absolute convergence of `tricomiLogSeriesRecipGamma`, for all `a`. -/
theorem summable_tricomiLogSeriesRecipGamma (a : ℂ) (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    Summable (fun k : ℕ => tricomiLogSeriesRecipGammaCoeff a n k * z ^ k) := by
  have h := (tricomi_numerator_nat_series_recipGamma a n hz).1.sub
    ((summable_regularizedConfluent_term a ((n : ℂ) + 1) z).mul_right
      ((Gamma (a - n))⁻¹ * log z))
  refine h.congr fun k => ?_
  dsimp only [tricomiLogSeriesRecipGammaCoeff]
  ring

/-- `tricomiLogSeriesRecipGamma` is analytic at zero, for all `a`. -/
theorem analyticAt_tricomiLogSeriesRecipGamma (a : ℂ) (n : ℕ) :
    AnalyticAt ℂ (tricomiLogSeriesRecipGamma a n) 0 := by
  let p := ofScalars ℂ (tricomiLogSeriesRecipGammaCoeff a n)
  have hs := (summable_tricomiLogSeriesRecipGamma a n (z := 2) (by norm_num)).norm
  have hr : (2 : ENNReal) ≤ p.radius := by
    apply p.le_radius_of_summable_norm (r := 2)
    simpa only [p, ofScalars_norm, norm_mul, norm_pow, Complex.norm_ofNat,
      NNReal.coe_ofNat] using hs
  have hp := p.hasFPowerSeriesOnBall (lt_of_lt_of_le (by norm_num : (0 : ENNReal) < 2) hr)
  have heq : p.sum = tricomiLogSeriesRecipGamma a n := by
    funext z
    simp only [p, FormalMultilinearSeries.sum, ofScalars_apply_eq, smul_eq_mul,
      tricomiLogSeriesRecipGamma]
  rw [heq] at hp
  exact hp.analyticAt

/-- Constant term of `tricomiLogSeriesRecipGamma`. -/
theorem tricomiLogSeriesRecipGamma_zero (a : ℂ) (n : ℕ) :
    tricomiLogSeriesRecipGamma a n 0 = (Gamma ((n : ℂ) + 1))⁻¹ *
      (-((Gamma (a - n))⁻¹ * (digamma 1 + digamma ((n : ℂ) + 1))) -
        poch (a - n) n * recipGammaDeriv 1 a) := by
  unfold tricomiLogSeriesRecipGamma
  rw [tsum_eq_single 0]
  · simp [tricomiLogSeriesRecipGammaCoeff, poch_zero]
  · intro k hk
    simp [zero_pow hk]

/-- Away from the poles of `Γ(a-n)`, `tricomiLogSeriesRecipGamma` is `tricomiLogSeries / Γ(a-n)`. -/
theorem tricomiLogSeriesRecipGamma_eq (a : ℂ) (n : ℕ) (z : ℂ)
    (ha : ∀ k : ℕ, a - n ≠ -(k : ℂ)) :
    tricomiLogSeriesRecipGamma a n z = (Gamma (a - n))⁻¹ * tricomiLogSeries a n z := by
  rw [tricomiLogSeriesRecipGamma, tricomiLogSeries, ← tsum_mul_left]
  refine tsum_congr fun k => ?_
  have h := recip_Gamma_mul_digamma_add_nat (x := a - n) (n + k) (not_neg_nat_add_nat ha (n + k))
  rw [show a - n + ((n + k : ℕ) : ℂ) = a + k by push_cast; ring] at h
  dsimp only [tricomiLogSeriesRecipGammaCoeff, tricomiLogSeriesCoeff]
  linear_combination (-(poch a k / k.factorial * (Gamma ((n : ℂ) + 1 + k))⁻¹ * z ^ k)) * h

/-- Separation of the logarithm from the convergent integer-parameter series, in the form with
`(1/Γ)'`. Stronger than `tricomi_log_series_split`: valid for all `a`. -/
theorem tricomi_log_series_split_recipGamma (a : ℂ) (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    (∑' k : ℕ, (poch a k * z ^ k / k.factorial * (Gamma ((n : ℂ) + 1 + k))⁻¹) *
      ((Gamma (a - n))⁻¹ * (log z - digamma (k + 1) - digamma ((n : ℂ) + 1 + k)) -
        poch (a - n) (n + k) * recipGammaDeriv 1 (a + k))) =
      (Gamma (a - n))⁻¹ * log z * regularizedHGFun {a} {(n : ℂ) + 1} z +
        tricomiLogSeriesRecipGamma a n z := by
  have hM := (summable_regularizedConfluent_term a ((n : ℂ) + 1) z).mul_left
    ((Gamma (a - n))⁻¹ * log z)
  have hT := summable_tricomiLogSeriesRecipGamma a n hz
  rw [regularizedConfluent_eq_tsum, tricomiLogSeriesRecipGamma, ← tsum_mul_left,
    ← hM.tsum_add hT]
  refine tsum_congr fun k => ?_
  dsimp only [tricomiLogSeriesRecipGammaCoeff]
  ring

end DLMF.Confluent
