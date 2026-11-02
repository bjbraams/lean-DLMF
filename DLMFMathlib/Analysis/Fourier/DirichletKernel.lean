/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import TauCeti.Analysis.Contour.WorkedExamples.HalfDisc.SineIntegral

/-!
# Pointwise convergence of Fourier integrals (Dirichlet's theorem)

For `g` integrable on `ℝ` and differentiable at `t`, the Dirichlet-kernel integrals
`∫ g(u) sin(η(t - u))/(π(t - u)) du` tend to `g(t)` as `η → ∞`. This is the pointwise
Fourier inversion theorem with symmetric partial integrals, under the Dini-type condition given by
differentiability. The proof splits off the Dirichlet integral `∫_{-δ}^{δ} sin(ηv)/(πv) dv → 1`
(from Tau Ceti's `TauCeti.Contour.tendsto_integral_sin_div_atTop`) and applies the
Riemann–Lebesgue lemma (`Real.tendsto_integral_exp_smul_cocompact`) to the remainder.

## Main results

* `Real.tendsto_integral_mul_sin_atTop`: `∫ k(v) sin(ηv) dv → 0` for integrable `k`.
* `Real.tendsto_integral_sin_mul_div_Icc`: `∫_{-δ}^{δ} sin(ηv)/(πv) dv → 1`.
* `Real.tendsto_integral_mul_sin_div_of_differentiableAt`: Dirichlet's theorem.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set Asymptotics
open scoped Topology Real

namespace Real

/-- Riemann–Lebesgue for `sin`: `∫ k(v) sin(ηv) dv → 0` as `η → ∞`. -/
theorem tendsto_integral_mul_sin_atTop {k : ℝ → ℂ} (hk : Integrable k) :
    Tendsto (fun η : ℝ => ∫ v, k v * (Real.sin (η * v) : ℂ)) atTop (𝓝 0) := by
  have hRL := Real.tendsto_integral_exp_smul_cocompact k
  have h1 := hRL.comp ((tendsto_id.atTop_div_const (by positivity : 0 < 2 * π)).mono_right
    atTop_le_cocompact)
  have h2 := hRL.comp ((tendsto_neg_atTop_atBot.atBot_div_const
    (by positivity : 0 < 2 * π)).mono_right atBot_le_cocompact)
  have h := (h2.sub h1).const_mul (1 / (2 * Complex.I))
  rw [sub_zero, mul_zero] at h
  refine h.congr fun η => ?_
  simp only [Function.comp_apply, id]
  have hexp : ∀ s : ℝ, Integrable fun v => Real.fourierChar (-(v * s)) • k v := fun s =>
    hk.bdd_smul 1 (by fun_prop) (Eventually.of_forall fun v => by simp)
  rw [← integral_sub (hexp _) (hexp _), ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
  rw [Complex.ofReal_sin, Complex.sin]
  push_cast
  have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have e1 : 2 * (π : ℂ) * -(v * (-η / (2 * π))) * Complex.I = η * v * Complex.I := by
    field_simp
  have e2 : 2 * (π : ℂ) * -(v * (η / (2 * π))) * Complex.I = -(η * v * Complex.I) := by
    field_simp
  rw [e1, e2]
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- `∫_{-δ}^{δ} sin(ηv)/(πv) dv → 1` as `η → ∞` (Dirichlet's integral), `δ > 0`. -/
theorem tendsto_integral_sin_mul_div_Icc {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun η : ℝ => ∫ v in Icc (-δ) δ, Real.sin (η * v) / (π * v)) atTop (𝓝 1) := by
  have hS := TauCeti.Contour.tendsto_integral_sin_div_atTop.comp
    (tendsto_id.atTop_mul_const hδ)
  have h := hS.const_mul (2 / π)
  rw [show 2 / π * (π / 2) = (1 : ℝ) by field_simp] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with η hη
  simp only [Function.comp_apply, id]
  set K : ℝ → ℝ := fun v => Real.sin (η * v) / (π * v) with hK
  have hKe : ∀ v, K (-v) = K v := fun v => by
    simp only [hK, mul_neg, Real.sin_neg, neg_div_neg_eq]
  have hKi : ∀ a b : ℝ, IntervalIntegrable K volume a b := by
    intro a b
    refine (intervalIntegrable_const (c := η / π)).mono_fun' ?_ (Eventually.of_forall fun v => ?_)
    · exact (by fun_prop : Measurable K).aestronglyMeasurable
    · dsimp only
      rw [Real.norm_eq_abs, hK, abs_div]
      by_cases hv : v = 0
      · simp [hv]; positivity
      rw [div_le_div_iff₀ (abs_pos.2 (by positivity)) Real.pi_pos, abs_mul,
        abs_of_pos Real.pi_pos]
      have := Real.abs_sin_le_abs (x := η * v)
      rw [abs_mul, abs_of_pos hη] at this
      nlinarith [abs_nonneg v, Real.pi_pos]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
    ← intervalIntegral.integral_add_adjacent_intervals (hKi _ 0) (hKi 0 _)]
  have hneg : ∫ v in (-δ)..0, K v = ∫ v in (0 : ℝ)..δ, K v := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := δ) K
    simp only [hKe, neg_zero] at this
    exact this.symm
  rw [hneg, ← two_mul]
  have hsub : ∫ v in (0 : ℝ)..δ, K v = π⁻¹ * ∫ x in (0 : ℝ)..η * δ, Real.sin x / x := by
    have h1 := intervalIntegral.integral_comp_mul_left (a := 0) (b := δ)
      (fun x => Real.sin x / x) hη.ne'
    simp only [mul_zero, smul_eq_mul] at h1
    have h2 : ∫ x in (0 : ℝ)..η * δ, Real.sin x / x =
        η * ∫ x in (0 : ℝ)..δ, Real.sin (η * x) / (η * x) := by
      rw [h1]; field_simp
    rw [h2, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun v _ => ?_
    simp only [hK]
    by_cases hv : v = 0
    · simp [hv]
    field_simp
  rw [hsub]
  field_simp

/-- **Dirichlet's pointwise convergence theorem** for Fourier integrals: if `g` is integrable on
`ℝ` and differentiable at `t`, then
`∫ g(u) sin(η(t - u))/(π(t - u)) du → g(t)` as `η → ∞`. -/
theorem tendsto_integral_mul_sin_div_of_differentiableAt {g : ℝ → ℂ} (hg : Integrable g)
    {t : ℝ} (hd : DifferentiableAt ℝ g t) :
    Tendsto (fun η : ℝ => ∫ u, g u * ((Real.sin (η * (t - u)) / (π * (t - u)) : ℝ) : ℂ))
      atTop (𝓝 (g t)) := by
  -- a Lipschitz bound at `t`
  obtain ⟨c, hc0, hc⟩ := hd.isBigO_sub.exists_pos
  obtain ⟨ε, hε, hεb⟩ := Metric.eventually_nhds_iff.1 hc.bound
  set δ : ℝ := ε / 2 with hδdef
  have hδ : 0 < δ := by positivity
  have hloc : ∀ v : ℝ, |v| ≤ δ → ‖g (t - v) - g t‖ ≤ c * |v| := by
    intro v hv
    have := hεb (y := t - v) (by
      rw [Real.dist_eq, show t - v - t = -v by ring, abs_neg]; linarith)
    simpa [Real.norm_eq_abs, abs_neg] using this
  have hgs : Integrable fun v => g (t - v) := hg.comp_sub_left t
  -- the regular part
  set k : ℝ → ℂ := fun v => (g (t - v) - (Icc (-δ) δ).indicator (fun _ => g t) v) *
    (((π * v)⁻¹ : ℝ) : ℂ) with hk
  have hkm : AEStronglyMeasurable k volume := by
    refine (hgs.aestronglyMeasurable.sub
      (aestronglyMeasurable_const.indicator measurableSet_Icc)).mul ?_
    exact (by fun_prop : Measurable fun v : ℝ => (((π * v)⁻¹ : ℝ) : ℂ)).aestronglyMeasurable
  have hki : Integrable k := by
    have hB : Integrable fun v => (Icc (-δ) δ).indicator (fun _ => c / π) v +
        ‖g (t - v)‖ / (π * δ) :=
      ((integrableOn_const (by simp)).integrable_indicator measurableSet_Icc).add
        (hgs.norm.div_const _)
    refine hB.mono' hkm (Eventually.of_forall fun v => ?_)
    simp only [hk, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_mul,
      abs_of_pos Real.pi_pos]
    by_cases hv : v = 0
    · simp only [hv, mul_zero, abs_zero, inv_zero, mul_zero]
      exact add_nonneg (indicator_nonneg (fun _ _ => by positivity) _) (by positivity)
    have hv' : 0 < |v| := abs_pos.2 hv
    by_cases hvδ : v ∈ Icc (-δ) δ
    · rw [indicator_of_mem hvδ, indicator_of_mem hvδ]
      have hb := hloc v (abs_le.2 hvδ)
      calc ‖g (t - v) - g t‖ * (π * |v|)⁻¹ ≤ c * |v| * (π * |v|)⁻¹ := by gcongr
        _ = c / π := by field_simp
        _ ≤ c / π + ‖g (t - v)‖ / (π * δ) := le_add_of_nonneg_right (by positivity)
    · rw [indicator_of_notMem hvδ, indicator_of_notMem hvδ, sub_zero, zero_add]
      have hvd : δ < |v| := by
        by_contra h; exact hvδ (abs_le.1 (not_lt.1 h))
      rw [← div_eq_mul_inv]
      gcongr
  -- the decomposition
  have hdec : ∀ η : ℝ, ∫ u, g u * ((Real.sin (η * (t - u)) / (π * (t - u)) : ℝ) : ℂ) =
      (∫ v, k v * (Real.sin (η * v) : ℂ)) +
        g t * ((∫ v in Icc (-δ) δ, Real.sin (η * v) / (π * v) : ℝ) : ℂ) := by
    intro η
    have hsub := integral_sub_left_eq_self
      (fun v => g (t - v) * ((Real.sin (η * v) / (π * v) : ℝ) : ℂ)) volume t
    simp only [sub_sub_cancel] at hsub
    rw [hsub]
    have hK : Integrable fun v => (Icc (-δ) δ).indicator
        (fun v => g t * ((Real.sin (η * v) / (π * v) : ℝ) : ℂ)) v := by
      refine (((integrableOn_const (s := Icc (-δ) δ) (C := ‖g t‖ * (|η| / π))
        (by simp)).integrable_indicator measurableSet_Icc)).mono' ?_
        (Eventually.of_forall fun v => ?_)
      · exact (aestronglyMeasurable_const.mul (by fun_prop : Measurable fun v : ℝ =>
          ((Real.sin (η * v) / (π * v) : ℝ) : ℂ)).aestronglyMeasurable).indicator
          measurableSet_Icc
      · by_cases hvδ : v ∈ Icc (-δ) δ
        · rw [indicator_of_mem hvδ, indicator_of_mem hvδ, norm_mul, Complex.norm_real,
            Real.norm_eq_abs]
          gcongr
          rw [abs_div, abs_mul, abs_of_pos Real.pi_pos]
          by_cases hv : v = 0
          · simp [hv]; positivity
          rw [div_le_div_iff₀ (by positivity) Real.pi_pos]
          have := Real.abs_sin_le_abs (x := η * v)
          rw [abs_mul] at this
          nlinarith [abs_nonneg v, Real.pi_pos, abs_nonneg η]
        · simp [indicator_of_notMem hvδ]
    have hkS : Integrable fun v => k v * (Real.sin (η * v) : ℂ) :=
      hki.mul_bdd (c := 1) (Complex.continuous_ofReal.comp (Real.continuous_sin.comp
        (continuous_const.mul continuous_id))).aestronglyMeasurable
        (Eventually.of_forall fun v => by
          rw [Complex.norm_real, Real.norm_eq_abs]; exact Real.abs_sin_le_one _)
    rw [← integral_complex_ofReal, ← integral_const_mul, ← integral_indicator measurableSet_Icc,
      ← integral_add hkS hK]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp only [hk]
    by_cases hvδ : v ∈ Icc (-δ) δ
    · rw [indicator_of_mem hvδ, indicator_of_mem hvδ]
      push_cast
      by_cases hv : v = 0
      · simp [hv]
      have : (π : ℂ) * v ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.2 Real.pi_ne_zero)
        (Complex.ofReal_ne_zero.2 hv)
      field_simp
      ring
    · rw [indicator_of_notMem hvδ, indicator_of_notMem hvδ]
      push_cast
      by_cases hv : v = 0
      · simp [hv]
      have : (π : ℂ) * v ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.2 Real.pi_ne_zero)
        (Complex.ofReal_ne_zero.2 hv)
      field_simp
      ring
  have h := (tendsto_integral_mul_sin_atTop hki).add
    (((Complex.continuous_ofReal.tendsto 1).comp (tendsto_integral_sin_mul_div_Icc hδ)).const_mul
      (g t))
  rw [zero_add, Complex.ofReal_one, mul_one] at h
  exact h.congr fun η => (hdec η).symm

end Real
