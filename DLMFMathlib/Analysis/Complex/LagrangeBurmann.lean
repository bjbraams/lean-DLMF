/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Analytic.OfScalars

/-!
# The Lagrange–Bürmann formula at the coefficient level

Let `F` and `Φ` be holomorphic on a closed disc `|t| ≤ r`. For small `z` the equation
`t = z Φ(t)` has a simple root `w` in the disc, and the Lagrange–Bürmann formula reads
`F(w) / (1 - z Φ'(w)) = ∑ₙ zⁿ [tⁿ] (F Φⁿ)`.
We prove it in the following form, which avoids the argument principle: assume a
factorization `t - z Φ(t) = (t - w) g(t)` on the circle `|t| = r` with `|w| < r` and with `g`
holomorphic and zero-free on the closed disc (then `g(w) = 1 - z Φ'(w)`).
Writing `[tⁿ](F Φⁿ)` as a Cauchy integral, summing the geometric series
`∑ (z Φ(t)/t)ⁿ = t / (t - z Φ(t))` under the integral (it converges uniformly when
`|z Φ| ≤ ρ < r` on the circle) and applying Cauchy's integral formula to `F/g` gives

* `Complex.lagB_hasSum_iteratedDeriv`:
  `∑ₙ zⁿ (F Φⁿ)⁽ⁿ⁾(0)/n! = F(w)/g(w)`.

We also record the tool for extending a power-series identity from a small disc to the disc of
holomorphy of its sum:

* `Complex.lagB_hasSum_of_differentiableOn`: if `f` is holomorphic on `|z| < R` and
  `f(z) = ∑ cₙ zⁿ` for `|z| < δ`, then the identity holds for `|z| < R`.

The proofs use Mathlib's Cauchy integral formula (`DiffContOnCl.circleIntegral_sub_inv_smul`,
`DiffContOnCl.circleIntegral_one_div_sub_center_pow_smul`), dominated convergence for interval
integrals, and uniqueness of power series (`HasFPowerSeriesOnBall.exchange_radius`).
-/

@[expose] public noncomputable section

open Complex Metric Set Filter MeasureTheory
open scoped Real Topology Nat NNReal ENNReal

namespace Complex

/-- **Lagrange–Bürmann formula, coefficient form.** If `F`, `Φ`, `g` are holomorphic on the
closed disc `|t| ≤ r`, `g` has no zeros there, `|z Φ(t)| ≤ ρ < r` on the circle `|t| = r`, and
`t - z Φ(t) = (t - w) g(t)` on that circle with `|w| < r`, then
`∑ₙ zⁿ [tⁿ](F Φⁿ) = F(w) / g(w)`, the coefficients being `(F Φⁿ)⁽ⁿ⁾(0) / n!`. -/
theorem lagB_hasSum_iteratedDeriv {F Φ g : ℂ → ℂ} {r ρ : ℝ} {z w : ℂ}
    (hr : 0 < r) (hF : DifferentiableOn ℂ F (closedBall 0 r))
    (hΦ : DifferentiableOn ℂ Φ (closedBall 0 r))
    (hg : DifferentiableOn ℂ g (closedBall 0 r)) (hg0 : ∀ t ∈ closedBall (0 : ℂ) r, g t ≠ 0)
    (hρ : ρ < r) (hzΦ : ∀ t ∈ sphere (0 : ℂ) r, ‖z * Φ t‖ ≤ ρ)
    (hw : ‖w‖ < r) (hfac : ∀ t ∈ sphere (0 : ℂ) r, t - z * Φ t = (t - w) * g t) :
    HasSum (fun n : ℕ => z ^ n * (iteratedDeriv n (fun t => F t * Φ t ^ n) 0 / n !))
      (F w / g w) := by
  have hrne : r ≠ 0 := hr.ne'
  have hρ0 : 0 ≤ ρ := by
    have hmem : (r : ℂ) ∈ sphere (0 : ℂ) r := by
      simp [abs_of_pos hr]
    exact (norm_nonneg _).trans (hzΦ _ hmem)
  have hq0 : 0 ≤ ρ / r := div_nonneg hρ0 hr.le
  have hq1 : ρ / r < 1 := (div_lt_one hr).2 hρ
  -- the Cauchy formula for the coefficients
  have hcoef : ∀ n : ℕ, (∮ t in C(0, r), (1 / (t - 0) ^ (n + 1)) • (F t * Φ t ^ n)) =
      (2 * π * I / n !) • iteratedDeriv n (fun t => F t * Φ t ^ n) 0 := by
    intro n
    have hd : DifferentiableOn ℂ (fun t => F t * Φ t ^ n) (closedBall 0 r) :=
      hF.mul (hΦ.pow n)
    exact DiffContOnCl.circleIntegral_one_div_sub_center_pow_smul hr n
      ((hd.mono (closure_ball_subset_closedBall)).diffContOnCl)
  -- the integrands
  set G : ℕ → ℂ → ℂ := fun n t => (z * Φ t * t⁻¹) ^ n * (t⁻¹ * F t) with hG
  have hGeq : ∀ n t, G n t = z ^ n * ((1 / (t - 0) ^ (n + 1)) • (F t * Φ t ^ n)) := by
    intro n t
    simp only [hG, sub_zero, smul_eq_mul, one_div]
    rw [mul_pow, mul_pow, inv_pow, pow_succ, mul_inv]
    ring
  have hFc : ContinuousOn F (closedBall 0 r) := hF.continuousOn
  have hΦc : ContinuousOn Φ (closedBall 0 r) := hΦ.continuousOn
  have hcm : ∀ θ : ℝ, circleMap 0 r θ ∈ closedBall (0 : ℂ) r :=
    fun θ => sphere_subset_closedBall (circleMap_mem_sphere 0 hr.le θ)
  have hcmne : ∀ θ : ℝ, circleMap 0 r θ ≠ 0 := fun θ => circleMap_ne_center hrne
  have hFθ : Continuous fun θ => F (circleMap 0 r θ) :=
    hFc.comp_continuous (continuous_circleMap 0 r) hcm
  have hΦθ : Continuous fun θ => Φ (circleMap 0 r θ) :=
    hΦc.comp_continuous (continuous_circleMap 0 r) hcm
  have hinvθ : Continuous fun θ => (circleMap 0 r θ)⁻¹ :=
    (continuous_circleMap 0 r).inv₀ hcmne
  -- the geometric series under the integral
  have hsum : HasSum (fun n => ∮ t in C(0, r), G n t)
      (∮ t in C(0, r), (t - w)⁻¹ • (F t / g t)) := by
    unfold circleIntegral
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun n θ => ‖F (circleMap 0 r θ)‖ * (ρ / r) ^ n) (fun n => ?_) (fun n => ?_) ?_ ?_ ?_
    · simp only [deriv_circleMap, hG]
      exact (((continuous_circleMap 0 r).mul continuous_const).smul
        (((continuous_const.mul hΦθ).mul hinvθ).pow n |>.mul (hinvθ.mul hFθ))).aestronglyMeasurable
    · refine Eventually.of_forall fun θ _ => ?_
      have ht : ‖circleMap 0 r θ‖ = r := by simp [abs_of_pos hr]
      have hb := hzΦ _ (circleMap_mem_sphere 0 hr.le θ)
      simp only [deriv_circleMap, hG, smul_eq_mul, norm_mul, norm_pow, norm_inv, ht, norm_I,
        mul_one]
      have h1 : ‖z‖ * ‖Φ (circleMap 0 r θ)‖ * r⁻¹ ≤ ρ / r := by
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right (by simpa [norm_mul] using hb) (inv_nonneg.2 hr.le)
      have h2 : (‖z‖ * ‖Φ (circleMap 0 r θ)‖ * r⁻¹) ^ n ≤ (ρ / r) ^ n :=
        pow_le_pow_left₀ (by positivity) h1 n
      calc r * ((‖z‖ * ‖Φ (circleMap 0 r θ)‖ * r⁻¹) ^ n * (r⁻¹ * ‖F (circleMap 0 r θ)‖))
          = (‖z‖ * ‖Φ (circleMap 0 r θ)‖ * r⁻¹) ^ n * ‖F (circleMap 0 r θ)‖ := by
            field_simp
        _ ≤ (ρ / r) ^ n * ‖F (circleMap 0 r θ)‖ :=
            mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
        _ = ‖F (circleMap 0 r θ)‖ * (ρ / r) ^ n := mul_comm _ _
    · exact Eventually.of_forall fun θ _ =>
        (summable_geometric_of_lt_one hq0 hq1).mul_left _
    · simp only [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
      exact (hFθ.norm.mul continuous_const).intervalIntegrable _ _
    · refine Eventually.of_forall fun θ _ => ?_
      set t := circleMap 0 r θ with ht_def
      have htS : t ∈ sphere (0 : ℂ) r := circleMap_mem_sphere 0 hr.le θ
      have ht : ‖t‖ = r := by simpa using htS
      have ht0 : t ≠ 0 := hcmne θ
      have hq : ‖z * Φ t * t⁻¹‖ < 1 := by
        rw [norm_mul, norm_inv, ht, ← div_eq_mul_inv]
        exact (div_lt_one hr).2 ((hzΦ t htS).trans_lt hρ)
      have hne : t - z * Φ t ≠ 0 := by
        intro h
        have : ‖z * Φ t‖ = r := by rw [← ht]; exact congrArg norm (sub_eq_zero.1 h).symm
        linarith [hzΦ t htS]
      have hgt : g t ≠ 0 := hg0 t (sphere_subset_closedBall htS)
      have htw : t - w ≠ 0 := by
        intro h
        rw [sub_eq_zero] at h
        rw [h] at ht
        linarith
      refine HasSum.const_smul _ ?_
      simp only [hG]
      convert (hasSum_geometric_of_norm_lt_one hq).mul_right (t⁻¹ * F t) using 1
      rw [smul_eq_mul]
      have hfac' := hfac t htS
      have h1 : (1 - z * Φ t * t⁻¹) = (t - w) * g t / t := by
        rw [← hfac']; field_simp
      rw [h1]
      field_simp
  -- Cauchy's integral formula for `F / g`
  have hHd : DifferentiableOn ℂ (fun t => F t / g t) (closedBall 0 r) :=
    hF.div hg hg0
  have hcauchy : (∮ t in C(0, r), (t - w)⁻¹ • (F t / g t)) = (2 * π * I) • (F w / g w) :=
    hHd.circleIntegral_sub_inv_smul (by simpa using hw)
  rw [hcauchy] at hsum
  have hsum' : HasSum (fun n => (2 * π * I) * (z ^ n * (iteratedDeriv n
      (fun t => F t * Φ t ^ n) 0 / n !))) ((2 * π * I) * (F w / g w)) := by
    refine hsum.congr_fun fun n => ?_
    rw [show (fun t => G n t) = fun t => z ^ n * ((1 / (t - 0) ^ (n + 1)) • (F t * Φ t ^ n))
      from funext (hGeq n), circleIntegral.integral_const_mul, hcoef n, smul_eq_mul]
    ring
  have h2pi : (2 * π * I : ℂ) ≠ 0 := two_pi_I_ne_zero
  have := hsum'.mul_left (2 * π * I)⁻¹
  simpa only [← mul_assoc, inv_mul_cancel₀ h2pi, one_mul] using this

/-- **Extension of a power-series identity.** If `f` is holomorphic on the disc `|z| < R` and
`f(z) = ∑ cₙ zⁿ` for `|z| < δ` (`δ > 0`), then `f(z) = ∑ cₙ zⁿ` for all `|z| < R`. -/
theorem lagB_hasSum_of_differentiableOn {f : ℂ → ℂ} {c : ℕ → ℂ} {δ R : ℝ} (hδ : 0 < δ)
    (hf : DifferentiableOn ℂ f (ball 0 R))
    (hsmall : ∀ z ∈ ball (0 : ℂ) δ, HasSum (fun n => c n * z ^ n) (f z))
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) : HasSum (fun n => c n * z ^ n) (f z) := by
  have hzR : ‖z‖ < R := by simpa using hz
  obtain ⟨r, hr0, hzr, hrR⟩ : ∃ r : ℝ≥0, (0 : ℝ) < r ∧ ‖z‖ < r ∧ (r : ℝ) < R := by
    have h0 : 0 ≤ (‖z‖ + R) / 2 := by linarith [norm_nonneg z]
    refine ⟨((‖z‖ + R) / 2).toNNReal, ?_, ?_, ?_⟩ <;>
      rw [Real.coe_toNNReal _ h0] <;> linarith [norm_nonneg z]
  -- the Cauchy power series on the disc of radius `r`
  have hq : HasFPowerSeriesOnBall f (cauchyPowerSeries f 0 r) 0 r :=
    (hf.mono (closedBall_subset_ball hrR)).hasFPowerSeriesOnBall (by exact_mod_cast hr0)
  -- the given power series on the small disc
  lift δ to ℝ≥0 using hδ.le
  have hp : HasFPowerSeriesOnBall f (FormalMultilinearSeries.ofScalars ℂ c) 0 δ := by
    refine ⟨?_, by exact_mod_cast hδ, fun {y} hy => ?_⟩
    · refine ENNReal.le_of_forall_pos_nnreal_lt fun s _ hs => ?_
      have hs' : (s : ℝ) < δ := by exact_mod_cast hs
      have hmem : ((s : ℝ) : ℂ) ∈ ball (0 : ℂ) δ := by
        simpa [abs_of_nonneg s.2] using hs'
      have hS := (hsmall _ hmem).summable
      refine FormalMultilinearSeries.le_radius_of_tendsto _ (l := 0) ?_
      have h0 := hS.norm.tendsto_atTop_zero
      refine h0.congr fun n => ?_
      rw [FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow, Complex.norm_real,
        Real.norm_eq_abs, NNReal.abs_eq]
    · have hy' : y ∈ ball (0 : ℂ) δ := by
        rw [Metric.mem_ball, dist_zero_right]
        have := hy
        rw [Metric.eball, Set.mem_ofPred_eq, edist_zero_right] at this
        exact_mod_cast this
      simpa [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, mul_comm] using
        hsmall y hy'
  have h := hp.exchange_radius hq
  have hz' : z ∈ Metric.eball (0 : ℂ) r := by
    rw [Metric.eball, Set.mem_ofPred_eq, edist_zero_right]
    exact_mod_cast hzr
  simpa [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, mul_comm] using h.hasSum hz'

end Complex
