/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.MeasureTheory.Integral.PeakFunction
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# The Poisson kernel of the upper half-plane on the real line

The Poisson kernel `P_ε(t) = ε/(π((t - σ)² + ε²))` is an approximate identity as `ε → 0+`. At a
point `σ` where an integrable `g` has one-sided limits, `∫ P_ε(t) g(t) dt → (g(σ+) + g(σ-))/2`.
The proof splits off a step function with the same one-sided limits, whose integral against
`P_ε` is explicit (an arctangent), and applies Mathlib's peak-function theorem
`tendsto_integral_comp_smul_smul_of_integrable'` with the Cauchy density to the remainder.

## Main results

* `Real.poissonKernelLine`: the kernel `ε/(π((t - σ)² + ε²))`.
* `Real.tendsto_integral_poissonKernelLine_mul`: the limit at a jump.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set Topology Complex
open scoped Real

namespace Real

/-- The Poisson kernel `ε/(π((t - σ)² + ε²))` of the half-plane at height `ε`. -/
def poissonKernelLine (σ ε t : ℝ) : ℝ :=
  ε / (π * ((t - σ) ^ 2 + ε ^ 2))

/-- The Poisson kernel is nonnegative. -/
theorem poissonKernelLine_nonneg (σ : ℝ) {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    0 ≤ poissonKernelLine σ ε t := by
  unfold poissonKernelLine; have := Real.pi_pos; positivity

/-- The Poisson kernel at height `ε` is bounded by `1/(πε)`. -/
theorem poissonKernelLine_le (σ : ℝ) {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    poissonKernelLine σ ε t ≤ 1 / (π * ε) := by
  unfold poissonKernelLine
  have := Real.pi_pos
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg (t - σ), mul_pos this hε]

/-- The Poisson kernel is continuous in `t`. -/
theorem continuous_poissonKernelLine (σ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Continuous (poissonKernelLine σ ε) := by
  unfold poissonKernelLine
  refine continuous_const.div (by fun_prop) fun t => ?_
  have := Real.pi_pos; positivity

/-- `∫_σ^{σ+1} P_ε = ∫_{σ-1}^σ P_ε = arctan(1/ε)/π`. -/
private lemma integral_poissonKernelLine (σ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    (∫ t in σ..σ + 1, poissonKernelLine σ ε t) = Real.arctan ε⁻¹ / π ∧
      (∫ t in σ - 1..σ, poissonKernelLine σ ε t) = Real.arctan ε⁻¹ / π := by
  have hd : ∀ t, HasDerivAt (fun t => Real.arctan ((t - σ) / ε) / π)
      (poissonKernelLine σ ε t) t := by
    intro t
    have h := ((((hasDerivAt_id t).sub_const σ).div_const ε).arctan).div_const π
    simp only [id] at h
    convert h using 1
    unfold poissonKernelLine
    have := Real.pi_pos
    field_simp
    ring
  have hi : ∀ a b, IntervalIntegrable (poissonKernelLine σ ε) volume a b := fun a b =>
    (continuous_poissonKernelLine σ hε).intervalIntegrable a b
  constructor
  · rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) (hi _ _)]
    simp [one_div]
  · rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) (hi _ _)]
    simp [one_div, neg_div, Real.arctan_neg]

/-- The Cauchy density `1/(π(1 + x²))`. -/
private lemma cauchyDensity_props :
    (∀ x : ℝ, 0 ≤ (π * (1 + x ^ 2))⁻¹) ∧ (∫ x : ℝ, (π * (1 + x ^ 2))⁻¹) = 1 ∧
      Tendsto (fun x : ℝ => ‖x‖ ^ Module.finrank ℝ ℝ * (π * (1 + x ^ 2))⁻¹)
        (Bornology.cobounded ℝ) (𝓝 0) := by
  refine ⟨fun x => by have := Real.pi_pos; positivity, ?_, ?_⟩
  · simp_rw [mul_inv]
    rw [integral_const_mul, integral_univ_inv_one_add_sq, inv_mul_cancel₀ Real.pi_ne_zero]
  · rw [Metric.cobounded_eq_cocompact, cocompact_eq_atBot_atTop, ← comap_abs_atTop]
    have key : Tendsto (fun r : ℝ => r * (π * (1 + r ^ 2))⁻¹) atTop (𝓝 0) := by
      have h1 : Tendsto (fun r : ℝ => (π * r)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp (tendsto_id.const_mul_atTop Real.pi_pos)
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h1 ?_ ?_
      · filter_upwards [eventually_ge_atTop 0] with r hr
        have := Real.pi_pos; positivity
      · filter_upwards [eventually_gt_atTop 0] with r hr
        have := Real.pi_pos
        rw [← div_eq_mul_inv, div_le_iff₀ (by positivity), inv_mul_eq_div,
          le_div_iff₀ (by positivity)]
        nlinarith
    have : (fun x : ℝ => ‖x‖ ^ Module.finrank ℝ ℝ * (π * (1 + x ^ 2))⁻¹) =
        (fun r : ℝ => r * (π * (1 + r ^ 2))⁻¹) ∘ abs := by
      ext x; simp [Real.norm_eq_abs, sq_abs]
    rw [this]
    exact key.comp tendsto_comap


/-- Poisson-kernel limit at a jump: for integrable `g` with one-sided limits at `σ`,
`∫ P_ε(t) g(t) dt → (g(σ+) + g(σ-))/2` as `ε → 0+`. -/
theorem tendsto_integral_poissonKernelLine_mul {g : ℝ → ℂ} (hg : Integrable g)
    {σ : ℝ} {gp gm : ℂ} (hp : Tendsto g (𝓝[>] σ) (𝓝 gp)) (hm : Tendsto g (𝓝[<] σ) (𝓝 gm)) :
    Tendsto (fun ε : ℝ => ∫ t, (poissonKernelLine σ ε t : ℂ) * g t) (𝓝[>] 0)
      (𝓝 ((gp + gm) / 2)) := by
  set J : ℝ → ℂ := (Ioo σ (σ + 1)).indicator (fun _ => gp) +
    (Ioo (σ - 1) σ).indicator (fun _ => gm) with hJ
  set ψ : ℝ → ℂ := fun t => if t = σ then 0 else g t - J t with hψ
  have hJ1 : Integrable ((Ioo σ (σ + 1)).indicator (fun _ : ℝ => gp)) :=
    (integrable_indicator_iff measurableSet_Ioo).2 (integrableOn_const measure_Ioo_lt_top.ne)
  have hJ2 : Integrable ((Ioo (σ - 1) σ).indicator (fun _ : ℝ => gm)) :=
    (integrable_indicator_iff measurableSet_Ioo).2 (integrableOn_const measure_Ioo_lt_top.ne)
  have hJi : Integrable J := hJ1.add hJ2
  have hae : g =ᵐ[volume] fun t => ψ t + J t := by
    filter_upwards [Measure.ae_ne volume σ] with t ht
    simp [hψ, ht]
  have hψi : Integrable ψ := by
    refine (hg.sub hJi).congr ?_
    filter_upwards [Measure.ae_ne volume σ] with t ht
    simp [hψ, ht]
  have hψc : ContinuousAt ψ σ := by
    rw [continuousAt_iff_continuous_left'_right']
    constructor
    · have hJl : Tendsto J (𝓝[<] σ) (𝓝 gm) := tendsto_const_nhds.congr' (by
        filter_upwards [Ioo_mem_nhdsLT (show σ - 1 < σ by linarith)] with t ht
        have h1 : t ∉ Ioo σ (σ + 1) := fun h => by linarith [h.1, ht.2]
        simp [hJ, h1, ht])
      have h := hm.sub hJl
      rw [sub_self] at h
      simp only [ContinuousWithinAt, hψ, ↓reduceIte]
      refine h.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t (ht : t < σ)
      simp [ht.ne]
    · have hJr : Tendsto J (𝓝[>] σ) (𝓝 gp) := tendsto_const_nhds.congr' (by
        filter_upwards [Ioo_mem_nhdsGT (show σ < σ + 1 by linarith)] with t ht
        have h1 : t ∉ Ioo (σ - 1) σ := fun h => by linarith [h.2, ht.1]
        simp [hJ, h1, ht])
      have h := hp.sub hJr
      rw [sub_self] at h
      simp only [ContinuousWithinAt, hψ, ↓reduceIte]
      refine h.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t (ht : σ < t)
      simp [ht.ne']
  -- the continuous part
  obtain ⟨hφ0, hφ1, hφ2⟩ := cauchyDensity_props
  have hpeak := (tendsto_integral_comp_smul_smul_of_integrable' (μ := volume) hφ0 hφ1 hφ2 hψi
    hψc).comp tendsto_inv_nhdsGT_zero
  simp only [hψ, ↓reduceIte] at hpeak
  have hA : Tendsto (fun ε : ℝ => ∫ t, (poissonKernelLine σ ε t : ℂ) * ψ t) (𝓝[>] 0)
      (𝓝 0) := by
    refine hpeak.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    simp only [Function.comp_apply, Module.finrank_self, pow_one]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [Complex.real_smul, smul_eq_mul]
    congr 2
    unfold poissonKernelLine
    have := Real.pi_pos
    field_simp
    ring
  -- the jump part
  have hB : ∀ ε : ℝ, 0 < ε → ∫ t, (poissonKernelLine σ ε t : ℂ) * J t =
      (gp + gm) * ((Real.arctan ε⁻¹ / π : ℝ) : ℂ) := by
    intro ε hε
    obtain ⟨h1, h2⟩ := integral_poissonKernelLine σ hε
    have hK : ∀ s : Set ℝ, ∀ c : ℂ, MeasurableSet s →
        ∫ t, (poissonKernelLine σ ε t : ℂ) * s.indicator (fun _ => c) t =
          c * ∫ t in s, (poissonKernelLine σ ε t : ℂ) := by
      intro s c hs
      rw [← integral_const_mul, ← integral_indicator hs]
      congr 1; funext t
      by_cases ht : t ∈ s <;> simp [ht, mul_comm]
    have hb : ∀ c : ℂ, ∀ s : Set ℝ, Integrable (s.indicator fun _ : ℝ => c) →
        Integrable fun t => (poissonKernelLine σ ε t : ℂ) * s.indicator (fun _ => c) t :=
      fun c s hi => hi.bdd_mul (c := 1 / (π * ε))
        (Complex.continuous_ofReal.comp
          (continuous_poissonKernelLine σ hε)).aestronglyMeasurable
        (Eventually.of_forall fun t => by
          rw [Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (poissonKernelLine_nonneg σ hε t)]
          exact poissonKernelLine_le σ hε t)
    simp only [hJ, Pi.add_apply, mul_add]
    rw [integral_add (hb _ _ hJ1) (hb _ _ hJ2), hK _ _ measurableSet_Ioo,
      hK _ _ measurableSet_Ioo, integral_Ioc_eq_integral_Ioo.symm,
      integral_Ioc_eq_integral_Ioo.symm, ← intervalIntegral.integral_of_le (by linarith),
      ← intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_ofReal,
      intervalIntegral.integral_ofReal, h1, h2]
    ring
  have hat : Tendsto (fun ε : ℝ => ((Real.arctan ε⁻¹ / π : ℝ) : ℂ)) (𝓝[>] 0)
      (𝓝 ((1 / 2 : ℝ) : ℂ)) := by
    refine (Complex.continuous_ofReal.tendsto _).comp ?_
    have h := (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp
      tendsto_inv_nhdsGT_zero
    have := h.div_const π
    rwa [show π / 2 / π = 1 / 2 by field_simp] at this
  have hlim := hA.add (hat.const_mul (gp + gm))
  rw [zero_add, show (gp + gm) * ((1 / 2 : ℝ) : ℂ) = (gp + gm) / 2 by push_cast; ring] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  have hbdd : ∀ u : ℝ → ℂ, Integrable u →
      Integrable fun t => (poissonKernelLine σ ε t : ℂ) * u t :=
    fun u hu => hu.bdd_mul (c := 1 / (π * ε))
      (Complex.continuous_ofReal.comp (continuous_poissonKernelLine σ hε)).aestronglyMeasurable
      (Eventually.of_forall fun t => by
        rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (poissonKernelLine_nonneg σ hε t)]
        exact poissonKernelLine_le σ hε t)
  rw [← hB ε hε, ← integral_add (hbdd ψ hψi) (hbdd J hJi)]
  refine integral_congr_ae ?_
  filter_upwards [hae] with t ht
  rw [ht, mul_add]

end Real
