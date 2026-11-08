/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Complex.CircleSingularities
public import DLMFMathlib.MeasureTheory.Integral.CompactParameterDomination
public import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Radial limits with finitely many integrable boundary singularities

Algebraic singularities of order strictly below one give uniform angular majorants on
inner concentric circles. Setting the trace to zero at singular angles preserves all
integrals and makes the majorant pointwise away from the fixed exceptional set.
This supplies the uniform-convergence step in Olver, *Asymptotics and Special Functions*,
Chapter 8, §9.3.
-/

@[expose] public noncomputable section

open Complex MeasureTheory Set Filter Metric Asymptotics
open scoped Real Topology

namespace Complex.CircleSingularities

/-- The polar circle parametrization with real radius. -/
def circle (s t : ℝ) : ℂ := (s : ℂ) * exp ((t : ℂ) * I)

/-- The circle parametrization is jointly continuous. -/
theorem continuous_circle : Continuous (fun p : ℝ × ℝ => circle p.1 p.2) := by
  unfold circle
  fun_prop

/-- The norm of a positively parametrized circle is its radius. -/
theorem norm_circle {s : ℝ} (hs : 0 ≤ s) (t : ℝ) : ‖circle s t‖ = s := by
  simp only [circle, norm_mul, norm_exp_ofReal_mul_I, mul_one, norm_real,
    Real.norm_eq_abs, abs_of_nonneg hs]

/-- Approaching a positive radius from below stays within the punctured open disk. -/
theorem tendsto_circle_nhdsWithin_disk {r v : ℝ} (hr : 0 < r) :
    Tendsto (fun p : ℝ × ℝ => circle p.1 p.2) (𝓝[<] r ×ˢ 𝓝 v)
      (𝓝[{z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < r}] (circle r v)) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨(continuous_circle.tendsto (r, v)).mono_left
    (by rw [nhds_prod_eq]; exact Filter.prod_mono nhdsWithin_le_nhds le_rfl), ?_⟩
  apply eventually_prod_iff.mpr
  refine ⟨fun s : ℝ => 0 < s ∧ s < r, Ioo_mem_nhdsLT hr, fun _ : ℝ => True,
    Eventually.of_forall fun _ => trivial, ?_⟩
  intro s hs t _
  simpa only [mem_ofPred_eq, norm_circle hs.1.le] using hs

/-- Every fiber of a nonzero-radius circle parametrization is countable. -/
theorem countable_fiber_circle {r : ℝ} (hr : r ≠ 0) (w : ℂ) :
    {t : ℝ | circle r t = w}.Countable := by
  by_cases hv : ∃ v : ℝ, circle r v = w
  · obtain ⟨v, hv⟩ := hv
    apply (countable_range (fun n : ℤ => v + (n : ℝ) * (2 * π))).mono
    intro t ht
    have he : exp ((t : ℂ) * I) = exp ((v : ℂ) * I) := by
      apply mul_left_cancel₀ (ofReal_ne_zero.mpr hr)
      exact ht.trans hv.symm
    obtain ⟨n, hn⟩ := exp_eq_exp_iff_exists_int.mp he
    have H := congrArg im hn
    norm_num at H
    exact ⟨n, by linarith⟩
  · have he : {t : ℝ | circle r t = w} = ∅ := by
      ext t
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      exact fun ht => hv ⟨t, ht⟩
    rw [he]
    exact countable_empty

/-- A finite set of boundary singularities has a null angular preimage. -/
theorem ae_circle_notMem {r : ℝ} (hr : r ≠ 0) (Z : Finset ℂ) :
    ∀ᵐ t : ℝ, circle r t ∉ Z := by
  have H : (⋃ w ∈ (Z : Set ℂ), {t : ℝ | circle r t = w}).Countable :=
    Z.finite_toSet.countable.biUnion fun w _ => countable_fiber_circle hr w
  have he : {t : ℝ | circle r t ∈ Z} = ⋃ w ∈ (Z : Set ℂ), {t : ℝ | circle r t = w} := by
    ext t
    simp
  have hzero : volume {t : ℝ | circle r t ∈ Z} = 0 := by rw [he]; exact H.measure_zero volume
  exact ae_iff.mpr (by simpa only [not_not] using hzero)

/-- The fixed exceptional boundary angles are assigned zero at every radial parameter. -/
def trace (h : ℂ → ℂ) (Z : Finset ℂ) (r s t : ℝ) : ℂ :=
  if circle r t ∈ Z then 0 else h (circle s t)

/-- Replacing the exceptional angular values does not change the radial function almost
anywhere. -/
theorem trace_ae_eq (h : ℂ → ℂ) (Z : Finset ℂ) {r : ℝ} (hr : r ≠ 0) (s : ℝ) :
    trace h Z r s =ᵐ[volume] fun t => h (circle s t) := by
  filter_upwards [ae_circle_notMem hr Z] with t ht
  simp only [trace, ite_eq_right ht]

/-- A locally valid angular profile gives a globally integrable majorant after restriction
of its support to a finite angular neighborhood. -/
theorem exists_integrable_bound_of_eventually {h : ℂ → ℂ} {Z : Finset ℂ} {r v : ℝ}
    {B : ℝ → ℝ} (hB0 : ∀ t, 0 ≤ B t)
    (hBi : IntervalIntegrable B volume (v - 1) (v + 1))
    (hb : ∀ᶠ p : ℝ × ℝ in 𝓝[<] r ×ˢ 𝓝 v, ‖trace h Z r p.1 p.2‖ ≤ B p.2) :
    ∃ U ∈ 𝓝 v, ∃ g : ℝ → ℝ, Integrable g ∧ (∀ t, 0 ≤ g t) ∧
      ∀ᶠ s in 𝓝[<] r, ∀ t ∈ U, ‖trace h Z r s t‖ ≤ g t := by
  obtain ⟨V, hV, W, hW, hVW⟩ := mem_prod_iff.mp hb
  let J := Icc (v - 1) (v + 1)
  let g := J.indicator B
  refine ⟨W ∩ Ioo (v - 1) (v + 1), inter_mem hW
    (Ioo_mem_nhds (by linarith) (by linarith)), g, ?_, ?_, ?_⟩
  · have HI := (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).mp hBi
    exact HI.integrable_indicator measurableSet_Icc
  · intro t
    exact indicator_nonneg (fun t _ => hB0 t) t
  · filter_upwards [hV] with s hs t ht
    rw [show g t = B t by exact indicator_of_mem (s := J) ⟨ht.2.1.le, ht.2.2.le⟩ B]
    exact hVW (show (s, t) ∈ V ×ˢ W from ⟨hs, ht.1⟩)

/-- The open punctured disk avoids every prescribed boundary singularity. -/
theorem disk_subset_closed_disk_diff {r : ℝ} {Z : Finset ℂ}
    (hZ : ∀ w ∈ Z, ‖w‖ = r) :
    {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < r} ⊆ {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ ≤ r} \ Z := by
  intro z hz
  refine ⟨⟨hz.1, hz.2.le⟩, ?_⟩
  intro hzZ
  exact hz.2.ne (hZ z hzZ)

/-- At a regular boundary angle, continuity supplies a local uniform radial majorant. -/
theorem exists_integrable_bound_of_continuous {h : ℂ → ℂ} {Z : Finset ℂ} {r v : ℝ}
    (hr : 0 < r) (hZ : ∀ w ∈ Z, ‖w‖ = r)
    (hh : ContinuousOn h ({z : ℂ | 0 < ‖z‖ ∧ ‖z‖ ≤ r} \ Z))
    (hv : circle r v ∉ Z) :
    ∃ U ∈ 𝓝 v, ∃ g : ℝ → ℝ, Integrable g ∧ (∀ t, 0 ≤ g t) ∧
      ∀ᶠ s in 𝓝[<] r, ∀ t ∈ U, ‖trace h Z r s t‖ ≤ g t := by
  have hmem : circle r v ∈ {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ ≤ r} \ Z :=
    ⟨by simpa only [mem_ofPred_eq, norm_circle hr.le] using And.intro hr le_rfl, hv⟩
  have ht := (hh _ hmem).tendsto.comp
    ((tendsto_circle_nhdsWithin_disk (v := v) hr).mono_right
      (nhdsWithin_mono _ (disk_subset_closed_disk_diff hZ)))
  have hb := ht.norm.eventually (eventually_le_nhds (lt_add_one ‖h (circle r v)‖))
  apply exists_integrable_bound_of_eventually
    (B := fun _ => ‖h (circle r v)‖ + 1) (fun _ => by positivity) intervalIntegrable_const
  filter_upwards [hb] with p hp
  by_cases hpZ : circle r p.2 ∈ Z
  · simp only [trace, ite_eq_left hpZ, norm_zero]
    positivity
  · simpa only [trace, ite_eq_right hpZ, Function.comp_apply] using hp

/-- At a weak algebraic boundary singularity, the circular distance power gives a uniform
integrable majorant for every nearby inner radius. -/
theorem exists_integrable_bound_of_singular {h : ℂ → ℂ} {Z : Finset ℂ} {r v σ : ℝ}
    (hr : 0 < r) (hσ : 0 < σ) (hv : circle r v ∈ Z)
    (hsing : h =O[𝓝[{z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < r}] (circle r v)]
      fun z => ‖z - circle r v‖ ^ (σ - 1)) :
    ∃ U ∈ 𝓝 v, ∃ g : ℝ → ℝ, Integrable g ∧ (∀ t, 0 ≤ g t) ∧
      ∀ᶠ s in 𝓝[<] r, ∀ t ∈ U, ‖trace h Z r s t‖ ≤ g t := by
  let p : ℝ := min (σ - 1) 0
  have hp : -1 < p := lt_min (by linarith) (by norm_num)
  have hp0 : p ≤ 0 := min_le_right _ _
  have hpσ : p ≤ σ - 1 := min_le_left _ _
  obtain ⟨C, hC, hCb⟩ := hsing.exists_pos
  let B : ℝ → ℝ := fun t => C * (2 : ℝ) ^ (-p) * ‖circle r t - circle r v‖ ^ p
  have hBi : IntervalIntegrable B volume (v - 1) (v + 1) := by
    have HI := Complex.intervalIntegrable_norm_circle_sub_rpow hr hp hp0 (circle r v)
      (v - 1) (v + 1)
    exact HI.const_mul (C * (2 : ℝ) ^ (-p))
  apply exists_integrable_bound_of_eventually (B := B) (fun t => by dsimp [B]; positivity) hBi
  have ht := tendsto_circle_nhdsWithin_disk (v := v) hr
  have hb := ht.eventually hCb.bound
  have hdist := ((ht.mono_right nhdsWithin_le_nhds).sub_const (circle r v)).norm
  simp only [sub_self, norm_zero] at hdist
  have hn := hdist.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))
  have hradEv : ∀ᶠ s : ℝ in 𝓝[<] r, 0 < s ∧ s < r := Ioo_mem_nhdsLT hr
  filter_upwards [hb, hn, hradEv.prod_inl (𝓝 v)] with u hu hnear hrad
  by_cases huZ : circle r u.2 ∈ Z
  · simp only [trace, ite_eq_left huZ, norm_zero]
    dsimp only [B]
    positivity
  · simp only [trace, ite_eq_right huZ]
    have hchord : 0 < ‖circle r u.2 - circle r v‖ := by
      apply norm_pos_iff.mpr
      apply sub_ne_zero.mpr
      intro he
      exact huZ (he ▸ hv)
    have hrad0 : 0 < ‖circle u.1 u.2 - circle r v‖ := by
      apply norm_pos_iff.mpr
      apply sub_ne_zero.mpr
      intro he
      have H := congrArg norm he
      rw [norm_circle hrad.1.le, norm_circle hr.le] at H
      linarith [hrad.2]
    have hsep : ‖circle r u.2 - circle r v‖ / 2 ≤
        ‖circle u.1 u.2 - circle r v‖ := by
      have H := Complex.norm_circle_sub_le_two_mul_norm_radial_sub hrad.1.le hrad.2.le
        (Complex.norm_exp_ofReal_mul_I u.2) (norm_circle hr.le v)
      change ‖circle r u.2 - circle r v‖ ≤ 2 * ‖circle u.1 u.2 - circle r v‖ at H
      linarith
    have hpow := Real.rpow_le_rpow_of_nonpos (div_pos hchord (by norm_num)) hsep hp0
    have hpow' : ‖circle u.1 u.2 - circle r v‖ ^ p ≤
        (2 : ℝ) ^ (-p) * ‖circle r u.2 - circle r v‖ ^ p := by
      rw [Real.div_rpow hchord.le (by norm_num)] at hpow
      rw [Real.rpow_neg (by norm_num)]
      simpa only [div_eq_mul_inv, mul_comm] using hpow
    have horder := Real.rpow_le_rpow_of_exponent_ge hrad0 hnear hpσ
    have hbase : ‖h (circle u.1 u.2)‖ ≤ C * ‖circle u.1 u.2 - circle r v‖ ^ (σ - 1) := by
      simpa only [Function.comp_apply, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)] using hu
    calc _ ≤ C * ‖circle u.1 u.2 - circle r v‖ ^ p :=
        hbase.trans (mul_le_mul_of_nonneg_left horder hC.le)
      _ ≤ C * ((2 : ℝ) ^ (-p) * ‖circle r u.2 - circle r v‖ ^ p) :=
        mul_le_mul_of_nonneg_left hpow' hC.le
      _ = B u.2 := by dsimp only [B]; ring

/-- Finitely many integrable algebraic singularities admit one common radial majorant
on each compact angular interval. -/
theorem exists_integrable_bound_trace {h : ℂ → ℂ} {Z : Finset ℂ} {r : ℝ}
    (hr : 0 < r) (hZ : ∀ w ∈ Z, ‖w‖ = r)
    (hh : ContinuousOn h ({z : ℂ | 0 < ‖z‖ ∧ ‖z‖ ≤ r} \ Z))
    (σ : ℂ → ℝ) (hσ : ∀ w ∈ Z, 0 < σ w)
    (hsing : ∀ w ∈ Z, h =O[𝓝[{z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < r}] w]
      fun z => ‖z - w‖ ^ (σ w - 1)) (a b : ℝ) :
    ∃ g : ℝ → ℝ, Integrable g ∧ (∀ t, 0 ≤ g t) ∧
      ∀ᶠ s in 𝓝[<] r, ∀ t ∈ Icc a b, ‖trace h Z r s t‖ ≤ g t := by
  apply isCompact_Icc.exists_integrable_bound_of_locally
  intro v _
  by_cases hv : circle r v ∈ Z
  · exact exists_integrable_bound_of_singular hr (hσ _ hv) hv (hsing _ hv)
  · exact exists_integrable_bound_of_continuous hr hZ hh hv

/-- The zeroed trace converges pointwise along inner radial circles. -/
theorem tendsto_trace {h : ℂ → ℂ} {Z : Finset ℂ} {r : ℝ}
    (hr : 0 < r) (hZ : ∀ w ∈ Z, ‖w‖ = r)
    (hh : ContinuousOn h ({z : ℂ | 0 < ‖z‖ ∧ ‖z‖ ≤ r} \ Z)) (t : ℝ) :
    Tendsto (fun s => trace h Z r s t) (𝓝[<] r) (𝓝 (trace h Z r r t)) := by
  by_cases ht : circle r t ∈ Z
  · simpa only [trace, ite_eq_left ht] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℂ)) (𝓝[<] r) (𝓝 0))
  · have hmem : circle r t ∈ {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ ≤ r} \ Z :=
      ⟨by simpa only [mem_ofPred_eq, norm_circle hr.le] using And.intro hr le_rfl, ht⟩
    have hrad := (tendsto_circle_nhdsWithin_disk (v := t) hr).comp
      (tendsto_id.prodMk tendsto_const_nhds)
    have H := (hh _ hmem).tendsto.comp (hrad.mono_right
      (nhdsWithin_mono _ (disk_subset_closed_disk_diff hZ)))
    simpa only [trace, ite_eq_right ht, Function.comp_def, id_eq] using H

/-- Inner radial traces are measurable after removing the fixed exceptional angles. -/
theorem measurable_trace {h : ℂ → ℂ} {Z : Finset ℂ} {r s : ℝ}
    (hZ : ∀ w ∈ Z, ‖w‖ = r)
    (hh : ContinuousOn h ({z : ℂ | 0 < ‖z‖ ∧ ‖z‖ ≤ r} \ Z))
    (hs : 0 < s) (hsr : s < r) : Measurable (trace h Z r s) := by
  have hc : Continuous (fun t : ℝ => h (circle s t)) := by
    apply hh.comp_continuous (by unfold circle; fun_prop)
    intro t
    exact disk_subset_closed_disk_diff hZ (by
      simpa only [mem_ofPred_eq, norm_circle hs.le] using And.intro hs hsr)
  have hE : MeasurableSet {t : ℝ | circle r t ∈ Z} :=
    (Z.finite_toSet.isClosed.preimage (by unfold circle; fun_prop)).measurableSet
  exact measurable_const.ite hE hc.measurable

/-- A Fourier multiplier on a real angular line has norm one. -/
theorem norm_fourierMultiplier (n : ℤ) (t : ℝ) : ‖exp (-((n : ℂ) * t * I))‖ = 1 := by
  simp [Complex.norm_exp, mul_re, mul_im]

/-- Finite integrable algebraic singularities permit expansion of a Fourier contour to the
boundary circle, with the exceptional boundary angles omitted. -/
theorem tendsto_integral_circle_mul_exp {h : ℂ → ℂ} {Z : Finset ℂ} {r : ℝ}
    (hr : 0 < r) (hZ : ∀ w ∈ Z, ‖w‖ = r)
    (hh : ContinuousOn h ({z : ℂ | 0 < ‖z‖ ∧ ‖z‖ ≤ r} \ Z))
    (σ : ℂ → ℝ) (hσ : ∀ w ∈ Z, 0 < σ w)
    (hsing : ∀ w ∈ Z, h =O[𝓝[{z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < r}] w]
      fun z => ‖z - w‖ ^ (σ w - 1)) (n : ℤ) {a b : ℝ} (hab : a ≤ b) :
    Tendsto (fun s => ∫ t in a..b, h (circle s t) * exp (-((n : ℂ) * t * I))) (𝓝[<] r)
      (𝓝 (∫ t in a..b, trace h Z r r t * exp (-((n : ℂ) * t * I)))) := by
  obtain ⟨g, hg, _, hb⟩ := exists_integrable_bound_trace hr hZ hh σ hσ hsing a b
  let μ : Measure ℝ := volume.restrict (Ioc a b)
  have hradEv : ∀ᶠ s : ℝ in 𝓝[<] r, 0 < s ∧ s < r := Ioo_mem_nhdsLT hr
  have hF : ∀ᶠ s in 𝓝[<] r, AEStronglyMeasurable
      (fun t => trace h Z r s t * exp (-((n : ℂ) * t * I))) μ := by
    filter_upwards [hradEv] with s hs
    have HM := (measurable_trace hZ hh hs.1 hs.2).mul
      (by fun_prop : Measurable (fun t : ℝ => exp (-((n : ℂ) * t * I))))
    exact HM.aestronglyMeasurable.restrict
  have hbound : ∀ᶠ s in 𝓝[<] r, ∀ᵐ t ∂μ,
      ‖trace h Z r s t * exp (-((n : ℂ) * t * I))‖ ≤ g t := by
    filter_upwards [hb] with s hs
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [norm_mul, norm_fourierMultiplier, mul_one]
    exact hs t ⟨ht.1.le, ht.2⟩
  have hlim : ∀ᵐ t ∂μ, Tendsto
      (fun s => trace h Z r s t * exp (-((n : ℂ) * t * I))) (𝓝[<] r)
      (𝓝 (trace h Z r r t * exp (-((n : ℂ) * t * I)))) :=
    Eventually.of_forall fun t => (tendsto_trace hr hZ hh t).mul_const _
  have H := tendsto_integral_filter_of_dominated_convergence g hF hbound hg.restrict hlim
  simp only [μ, ← intervalIntegral.integral_of_le hab] at H
  apply H.congr' (Eventually.of_forall fun s => ?_)
  apply intervalIntegral.integral_congr_ae
  filter_upwards [trace_ae_eq h Z hr.ne' s] with t ht _
  rw [ht]

end Complex.CircleSingularities
