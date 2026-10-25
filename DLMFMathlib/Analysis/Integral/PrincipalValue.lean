/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Cauchy principal values by symmetric excision

For a function `F` on `[a, b]` with a simple singularity at an interior point `c`, the Cauchy
principal value is the limit as `ε → 0⁺` of `∫_a^{c-ε} F + ∫_{c+ε}^b F`. If `F t - A/(t - c)`
is integrable on `[a, b]` for some constant `A` (the "residue" of `F` at `c`), the excised
integrals of `A/(t - c)` cancel exactly, and the principal value exists and equals

`∫_a^b (F t - A/(t - c)) dt + A log ((b - c)/(c - a))`.

This is the subtraction form of the principal value of `PV ∫ f(t)/(t - c) dt`, with `A = f c`.
The hypothesis holds whenever `F t = f t / (t - c)` with `f` integrable on `[a, b]` and
differentiable at `c`.

## Main results

* `MeasureTheory.pv_tendsto_of_integrableOn_sub`: existence and value of the principal value
  under the subtraction hypothesis.
* `MeasureTheory.pv_integrableOn_sub_of_differentiableAt`: the subtraction hypothesis for
  `f t / (t - c)` with `f` integrable and differentiable at `c`.
* `MeasureTheory.pv_tendsto_div_sub`: the principal value of `∫_a^b f(t)/(t - c) dt`.
* `MeasureTheory.pv_tendsto_intervalIntegral_atTop_of_le`: moving the lower endpoint of a
  convergent improper integral `lim_{R→∞} ∫_b^R F`, used to attach infinite tails.
-/

@[expose] public section

noncomputable section

open Filter Set MeasureTheory intervalIntegral

open scoped Topology

namespace MeasureTheory

/-- The excised integrals of `(t - c)⁻¹` on `[a, c - ε]` and `[c + ε, b]` add up to
`log ((b - c)/(c - a))`, independently of `ε`. -/
theorem pv_integral_recip_sub_add {a b c ε : ℝ} (hε : 0 < ε) (hεa : ε < c - a) (hεb : ε < b - c) :
    (∫ t in a..c - ε, (t - c)⁻¹) + (∫ t in c + ε..b, (t - c)⁻¹) =
      Real.log ((b - c) / (c - a)) := by
  rw [intervalIntegral.integral_comp_sub_right (fun t => t⁻¹),
    intervalIntegral.integral_comp_sub_right (fun t => t⁻¹),
    integral_inv_of_neg (by linarith) (by linarith),
    integral_inv_of_pos (by linarith) (by linarith),
    ← Real.log_mul (by apply div_ne_zero <;> linarith) (by apply div_ne_zero <;> linarith)]
  congr 1
  rw [show c - ε - c = -ε by ring, show c + ε - c = ε by ring]
  have h1 : a - c ≠ 0 := by linarith
  have h2 : c - a ≠ 0 := by linarith
  have h3 : ε ≠ 0 := hε.ne'
  rw [div_mul_div_comm, div_eq_div_iff (mul_ne_zero h1 h3) h2]
  ring

/-- **Principal value by subtraction of the singular part.** If `F t - A/(t - c)` is integrable
on `[a, b]`, `a < c < b`, then `∫_a^{c-ε} F + ∫_{c+ε}^b F` tends, as `ε → 0⁺`, to
`∫_a^b (F t - A/(t - c)) dt + A log ((b - c)/(c - a))`. -/
theorem pv_tendsto_of_integrableOn_sub {F : ℝ → ℂ} {a b c : ℝ} (A : ℂ) (hac : a < c)
    (hcb : c < b) (hF : IntegrableOn (fun t => F t - A / (t - c)) (Icc a b)) :
    Tendsto (fun ε : ℝ => (∫ t in a..c - ε, F t) + ∫ t in c + ε..b, F t) (𝓝[>] 0)
      (𝓝 ((∫ t in a..b, (F t - A / (t - c))) + A * Real.log ((b - c) / (c - a)))) := by
  set G : ℝ → ℂ := fun t => F t - A / (t - c) with hG
  have hab : a ≤ b := by linarith
  have hGi : ∀ u v : ℝ, u ∈ Icc a b → v ∈ Icc a b → IntervalIntegrable G volume u v :=
    fun u v hu hv => (hF.mono_set (uIcc_subset_Icc hu hv)).intervalIntegrable
  -- the singular part is continuous away from `c`
  have hSi : ∀ u v : ℝ, c ∉ uIcc u v →
      IntervalIntegrable (fun t : ℝ => A / ((t : ℂ) - c)) volume u v := by
    intro u v huv
    refine ContinuousOn.intervalIntegrable ?_
    refine continuousOn_const.div (by fun_prop) fun t ht h => huv ?_
    have : t = c := by exact_mod_cast sub_eq_zero.mp h
    rw [← this]; exact ht
  have hsing : ∀ u v : ℝ, c ∉ uIcc u v →
      (∫ t in u..v, A / ((t : ℂ) - c)) = A * ((∫ t in u..v, (t - c)⁻¹ : ℝ) : ℂ) := by
    intro u v _
    rw [← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_const_mul]
    congr 1; funext t; push_cast; ring
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (∫ t in a..c - ε, F t) + (∫ t in c + ε..b, F t) =
        ((∫ t in a..c - ε, G t) + ∫ t in c + ε..b, G t) +
          A * Real.log ((b - c) / (c - a)) := by
    filter_upwards [Ioo_mem_nhdsGT (lt_min (sub_pos.mpr hac) (sub_pos.mpr hcb))] with ε hε
    have hε0 := hε.1
    have hεa : ε < c - a := lt_of_lt_of_le hε.2 (min_le_left _ _)
    have hεb : ε < b - c := lt_of_lt_of_le hε.2 (min_le_right _ _)
    have hc1 : c ∉ uIcc a (c - ε) := by
      rw [uIcc_of_le (by linarith)]; intro h; linarith [h.2]
    have hc2 : c ∉ uIcc (c + ε) b := by
      rw [uIcc_of_le (by linarith)]; intro h; linarith [h.1]
    have hF1 : (∫ t in a..c - ε, F t) = (∫ t in a..c - ε, G t) +
        ∫ t in a..c - ε, A / ((t : ℂ) - c) := by
      rw [← intervalIntegral.integral_add (hGi _ _ ⟨le_rfl, hab⟩ ⟨by linarith, by linarith⟩)
        (hSi _ _ hc1)]
      simp [G]
    have hF2 : (∫ t in c + ε..b, F t) = (∫ t in c + ε..b, G t) +
        ∫ t in c + ε..b, A / ((t : ℂ) - c) := by
      rw [← intervalIntegral.integral_add (hGi _ _ ⟨by linarith, by linarith⟩ ⟨hab, le_rfl⟩)
        (hSi _ _ hc2)]
      simp [G]
    rw [hF1, hF2, hsing _ _ hc1, hsing _ _ hc2, ← pv_integral_recip_sub_add hε0 hεa hεb]
    push_cast
    ring
  refine Tendsto.congr' (EventuallyEq.symm hev) (Tendsto.add_const _ ?_)
  -- continuity of the primitive of `G`
  have hcont : ContinuousOn (fun x => ∫ t in a..x, G t) (uIcc a b) :=
    intervalIntegral.continuousOn_primitive_interval (by rwa [uIcc_of_le hab])
  have hcIn : c ∈ uIcc a b := by rw [uIcc_of_le hab]; exact ⟨hac.le, hcb.le⟩
  have hlim : ∀ σ : ℝ, Tendsto (fun ε : ℝ => ∫ t in a..c + σ * ε, G t) (𝓝[>] 0)
      (𝓝 (∫ t in a..c, G t)) := by
    intro σ
    have hmap : Tendsto (fun ε : ℝ => c + σ * ε) (𝓝[>] 0) (𝓝[uIcc a b] c) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have : Tendsto (fun ε : ℝ => c + σ * ε) (𝓝 0) (𝓝 (c + σ * 0)) :=
          (continuous_const.add (continuous_const.mul continuous_id)).tendsto 0
        simpa using this.mono_left nhdsWithin_le_nhds
      · have hδ : ∀ᶠ ε in 𝓝[>] (0 : ℝ), |σ * ε| < min (c - a) (b - c) := by
          have : Tendsto (fun ε : ℝ => |σ * ε|) (𝓝 0) (𝓝 (|σ * 0|)) :=
            ((continuous_const.mul continuous_id).abs).tendsto 0
          rw [mul_zero, abs_zero] at this
          exact (this.mono_left nhdsWithin_le_nhds).eventually
            (gt_mem_nhds (lt_min (sub_pos.mpr hac) (sub_pos.mpr hcb)))
        filter_upwards [hδ] with ε hε
        rw [uIcc_of_le hab]
        have h1 := lt_of_lt_of_le hε (min_le_left _ _)
        have h2 := lt_of_lt_of_le hε (min_le_right _ _)
        constructor <;> linarith [abs_lt.mp h1, abs_lt.mp h2]
    exact (hcont c hcIn).tendsto.comp hmap
  have h1 := hlim (-1)
  have h2 := hlim 1
  have hsplit : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (∫ t in a..c - ε, G t) + (∫ t in c + ε..b, G t) =
        (∫ t in a..c + (-1) * ε, G t) + ((∫ t in a..b, G t) - ∫ t in a..c + 1 * ε, G t) := by
    filter_upwards [Ioo_mem_nhdsGT (sub_pos.mpr hcb)] with ε hε
    rw [← intervalIntegral.integral_interval_sub_left (hGi _ _ ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩)
      (hGi _ _ ⟨le_rfl, hab⟩ ⟨by linarith [hε.1], by linarith [hε.2]⟩)]
    simp only [neg_one_mul, one_mul, ← sub_eq_add_neg]
  refine Tendsto.congr' (EventuallyEq.symm hsplit) ?_
  convert h1.add (tendsto_const_nhds.sub h2) using 2
  ring

/-- If `f` is integrable on `[a, b]` and differentiable at `c`, then
`f t / (t - c) - f c / (t - c)` is integrable on `[a, b]`. -/
theorem pv_integrableOn_sub_of_differentiableAt {f : ℝ → ℂ} {a b c : ℝ}
    (hf : IntegrableOn f (Icc a b)) (hd : DifferentiableAt ℝ f c) :
    IntegrableOn (fun t => f t / (t - c) - f c / (t - c)) (Icc a b) := by
  -- a bound for the difference quotient near `c`
  have hs := hd.hasDerivAt.tendsto_slope
  obtain ⟨δ, hδ, hbd⟩ : ∃ δ > 0, ∀ t : ℝ, t ≠ c → |t - c| < δ →
      ‖(f t - f c) / ((t : ℂ) - c)‖ ≤ ‖deriv f c‖ + 1 := by
    have hev := hs.norm.eventually (eventually_le_nhds (lt_add_one ‖deriv f c‖))
    obtain ⟨U, hUo, hcU, hUs⟩ := mem_nhdsWithin.mp hev
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hUo c hcU
    refine ⟨δ, hδ, fun t htc ht => ?_⟩
    have := hUs ⟨hball (by rwa [Metric.mem_ball, Real.dist_eq]), htc⟩
    simp only [mem_ofPred_eq, slope_def_module] at this
    rw [div_eq_inv_mul]
    rwa [← Complex.coe_smul, Complex.ofReal_inv, Complex.ofReal_sub, smul_eq_mul] at this
  set M := ‖deriv f c‖ + 1
  have hmeas : AEStronglyMeasurable (fun t => f t / (t - c) - f c / (t - c))
      (volume.restrict (Icc a b)) := by
    have h1 : AEStronglyMeasurable (fun t : ℝ => ((t : ℂ) - c)⁻¹) (volume.restrict (Icc a b)) :=
      (Measurable.inv (by fun_prop)).aestronglyMeasurable
    simp only [div_eq_mul_inv]
    exact (hf.aestronglyMeasurable.mul h1).sub (aestronglyMeasurable_const.mul h1)
  refine Integrable.mono' (g := fun t => M + δ⁻¹ * (‖f t‖ + ‖f c‖)) ?_ hmeas ?_
  · exact (integrable_const M).add ((hf.norm.add (integrable_const _)).const_mul _)
  · refine ae_of_all _ fun t => ?_
    have hpos : 0 ≤ M + δ⁻¹ * (‖f t‖ + ‖f c‖) := by positivity
    rw [← sub_div]
    by_cases htc : t = c
    · subst htc; simpa using hpos
    by_cases hnear : |t - c| < δ
    · exact (hbd t htc hnear).trans (le_add_of_nonneg_right (by positivity))
    · push Not at hnear
      have hne : (t : ℂ) - c ≠ 0 := by
        intro h; exact htc (by exact_mod_cast sub_eq_zero.mp h)
      rw [norm_div]
      have hn : ‖(t : ℂ) - c‖ = |t - c| := by
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      rw [hn, div_eq_mul_inv]
      have h1 : ‖f t - f c‖ ≤ ‖f t‖ + ‖f c‖ := norm_sub_le _ _
      have h2 : |t - c|⁻¹ ≤ δ⁻¹ := inv_anti₀ hδ hnear
      have h3 : ‖f t - f c‖ * |t - c|⁻¹ ≤ (‖f t‖ + ‖f c‖) * δ⁻¹ :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
      have hM : 0 ≤ M := by positivity
      linarith

/-- **Principal value of `∫_a^b f(t)/(t - c) dt`** for `f` integrable on `[a, b]` and
differentiable at the interior point `c`. -/
theorem pv_tendsto_div_sub {f : ℝ → ℂ} {a b c : ℝ} (hac : a < c) (hcb : c < b)
    (hf : IntegrableOn f (Icc a b)) (hd : DifferentiableAt ℝ f c) :
    Tendsto (fun ε : ℝ => (∫ t in a..c - ε, f t / (t - c)) + ∫ t in c + ε..b, f t / (t - c))
      (𝓝[>] 0) (𝓝 ((∫ t in a..b, (f t - f c) / (t - c)) +
        f c * Real.log ((b - c) / (c - a)))) := by
  have h := pv_tendsto_of_integrableOn_sub (F := fun t => f t / (t - c)) (f c) hac hcb
    (pv_integrableOn_sub_of_differentiableAt hf hd)
  simpa only [sub_div] using h

/-- Moving the lower endpoint of a convergent improper integral: if `∫_b^R F → L` as `R → ∞`
and `F` is interval integrable on `[d, b]`, then `∫_d^R F → ∫_d^b F + L`. -/
theorem pv_tendsto_intervalIntegral_atTop_of_le {F : ℝ → ℂ} {b d : ℝ} {L : ℂ}
    (hL : Tendsto (fun R => ∫ t in b..R, F t) atTop (𝓝 L))
    (hFi : IntervalIntegrable F volume d b)
    (hloc : ∀ R, b ≤ R → IntervalIntegrable F volume b R) :
    Tendsto (fun R => ∫ t in d..R, F t) atTop (𝓝 ((∫ t in d..b, F t) + L)) := by
  refine (tendsto_const_nhds.add hL).congr' ?_
  filter_upwards [eventually_ge_atTop b] with R hR
  exact intervalIntegral.integral_add_adjacent_intervals hFi (hloc R hR)

end MeasureTheory
