/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Fourier.DirichletKernel
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.MeanValue
public import Mathlib.Topology.EMetricSpace.VariationOnFromTo

/-!
# The Dirichlet–Jordan theorem for Fourier integrals

If `g` is integrable on `ℝ` and of bounded variation near `t`, with one-sided limits
`g(t±)`, then the Dirichlet-kernel integrals `∫ g(u) sin(η(t - u))/(π(t - u)) du` tend to
`(g(t+) + g(t-))/2` as `η → ∞`. This is the pointwise Fourier inversion theorem at points of
bounded variation.

The proof writes the real and imaginary parts of `g` near `t` as differences of monotone
functions (`LocallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn`). For a monotone function
the contribution near `t` is controlled by the second mean value theorem
(`exists_le_const_mul_norm_intervalIntegral_of_nonneg_of_monotoneOn`) and the boundedness of the
sine integral; the remainder tends to `0` by the Riemann–Lebesgue lemma.

## Main results

* `Real.tendsto_integral_mul_sin_div_of_boundedVariationOn`: the Dirichlet–Jordan theorem.
* `Real.boundedVariationOn_exp_neg_mul`: `u ↦ e^{-σu}` has bounded variation on compact
  intervals (a weight that occurs when the theorem is applied to Laplace and Mellin transforms).
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set Asymptotics
open scoped Topology Real

namespace Real

/-- `sin x / x` is bounded by `1`. -/
private lemma abs_sin_div_le_one (x : ℝ) : |Real.sin x / x| ≤ 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rw [abs_div, div_le_one (abs_pos.2 hx)]
  exact Real.abs_sin_le_abs

private lemma intervalIntegrable_sin_div (a b : ℝ) :
    IntervalIntegrable (fun x => Real.sin x / x) volume a b := by
  refine (intervalIntegrable_const (c := (1 : ℝ))).mono_fun' ?_
    (Eventually.of_forall fun x => ?_)
  · exact (by fun_prop : Measurable fun x : ℝ => Real.sin x / x).aestronglyMeasurable
  · simp only [Real.norm_eq_abs]; exact abs_sin_div_le_one x

/-- The sine integral `∫₀ˢ sin x / x dx` is bounded. -/
private lemma exists_bound_integral_sin_div :
    ∃ C, ∀ s : ℝ, |∫ x in (0 : ℝ)..s, Real.sin x / x| ≤ C := by
  set F : ℝ → ℝ := fun s => ∫ x in (0 : ℝ)..s, Real.sin x / x with hF
  have hcont : Continuous F := by
    have : F = fun s => ∫ x in (0 : ℝ)..s, Real.sinc x := by
      funext s
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [Measure.ae_ne volume (0 : ℝ)] with x hx _
      rw [Real.sinc_of_ne_zero hx]
    rw [this]
    exact intervalIntegral.continuous_primitive
      (fun a b => Real.continuous_sinc.intervalIntegrable a b) 0
  have hodd : ∀ s, F (-s) = -F s := by
    intro s
    simp only [hF]
    have h := intervalIntegral.integral_comp_neg (a := 0) (b := s) (fun x => Real.sin x / x)
    simp only [Real.sin_neg, neg_div_neg_eq, neg_zero] at h
    have h2 := intervalIntegral.integral_symm (μ := volume) (f := fun x => Real.sin x / x) 0 (-s)
    linarith [h, h2]
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((TauCeti.Contour.tendsto_integral_sin_div_atTop.sub_const
    (π / 2)).abs.eventually (gt_mem_nhds (show |(π / 2 - π / 2 : ℝ)| < 1 by simp)))
  obtain ⟨C₀, hC₀⟩ := (isCompact_Icc (a := 0) (b := max N 0)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max C₀ (π / 2 + 1), fun s => ?_⟩
  have key : ∀ s, 0 ≤ s → |F s| ≤ max C₀ (π / 2 + 1) := by
    intro s hs
    by_cases hsN : s ≤ max N 0
    · have h0 : |F s| ≤ C₀ := by simpa [Real.norm_eq_abs] using hC₀ s ⟨hs, hsN⟩
      exact h0.trans (le_max_left _ _)
    · have h1 := hN s ((le_max_left _ _).trans (not_le.1 hsN).le)
      refine le_trans ?_ (le_max_right _ _)
      have h2 := abs_sub_abs_le_abs_sub (F s) (π / 2)
      rw [abs_of_pos (by positivity : 0 < π / 2)] at h2
      linarith
  rcases le_total 0 s with hs | hs
  · exact key s hs
  · have := key (-s) (by linarith)
    rwa [hodd, abs_neg] at this

/-- Scaling: `∫ₐᵇ sin(ηv)/v dv = ∫_{ηa}^{ηb} sin x / x dx` for `η > 0`. -/
private lemma integral_sin_mul_div_eq {η : ℝ} (hη : 0 < η) (a b : ℝ) :
    ∫ v in a..b, Real.sin (η * v) / v = ∫ x in η * a..η * b, Real.sin x / x := by
  have h := intervalIntegral.integral_comp_mul_left (a := a) (b := b)
    (fun x => Real.sin x / x) hη.ne'
  simp only [smul_eq_mul] at h
  rw [← mul_right_inj' (inv_ne_zero hη.ne'), ← h, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun v _ => ?_
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  field_simp

/-- A uniform bound for the truncated Dirichlet integrals `∫ₐᵇ sin(ηv)/v dv`, `η > 0`. -/
private lemma exists_bound_integral_sin_mul_div :
    ∃ C, ∀ η : ℝ, 0 < η → ∀ a b : ℝ, |∫ v in a..b, Real.sin (η * v) / v| ≤ C := by
  obtain ⟨C, hC⟩ := exists_bound_integral_sin_div
  refine ⟨2 * C, fun η hη a b => ?_⟩
  rw [integral_sin_mul_div_eq hη,
    ← intervalIntegral.integral_interval_sub_left (intervalIntegrable_sin_div 0 _)
    (intervalIntegrable_sin_div 0 _)]
  calc _ ≤ |∫ x in (0 : ℝ)..η * b, Real.sin x / x| + |∫ x in (0 : ℝ)..η * a, Real.sin x / x| :=
        abs_sub _ _
    _ ≤ 2 * C := by linarith [hC (η * a), hC (η * b)]


/-- The kernel `sin(ηv)/(πv)` is bounded by `|η|/π`. -/
private lemma abs_sin_mul_div_le (η v : ℝ) : |Real.sin (η * v) / (π * v)| ≤ |η| / π := by
  rw [abs_div, abs_mul, abs_of_pos Real.pi_pos]
  rcases eq_or_ne v 0 with rfl | hv
  · simp only [abs_zero, mul_zero, div_zero]; positivity
  rw [div_le_div_iff₀ (by positivity) Real.pi_pos]
  have := Real.abs_sin_le_abs (x := η * v)
  rw [abs_mul] at this
  nlinarith [Real.pi_pos, abs_nonneg v, abs_nonneg η]

/-- Interval integrability of `u(v) sin(ηv)/(πv)` for interval integrable `u`. -/
private lemma intervalIntegrable_mul_sin_div {u : ℝ → ℝ} {a b : ℝ}
    (hu : IntervalIntegrable u volume a b) (η : ℝ) :
    IntervalIntegrable (fun v => u v * (Real.sin (η * v) / (π * v))) volume a b := by
  rw [intervalIntegrable_iff] at hu ⊢
  exact hu.mul_bdd (c := |η| / π) (by fun_prop : Measurable fun v : ℝ =>
    Real.sin (η * v) / (π * v)).aestronglyMeasurable
    (Eventually.of_forall fun v => by rw [Real.norm_eq_abs]; exact abs_sin_mul_div_le η v)

/-- `∫₀^δ sin(ηv)/(πv) dv → 1/2` as `η → ∞`. -/
private lemma tendsto_integral_sin_mul_div_pi {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun η : ℝ => ∫ v in (0 : ℝ)..δ, Real.sin (η * v) / (π * v)) atTop
      (𝓝 (1 / 2)) := by
  have hS := TauCeti.Contour.tendsto_integral_sin_div_atTop.comp
    (tendsto_id.atTop_mul_const hδ)
  have h := hS.const_mul π⁻¹
  rw [show π⁻¹ * (π / 2) = (1 / 2 : ℝ) by field_simp] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with η hη
  simp only [Function.comp_apply, id]
  have h1 := integral_sin_mul_div_eq hη 0 δ
  rw [mul_zero] at h1
  rw [← h1, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun v _ => ?_
  ring

/-- Dirichlet–Jordan for a monotone function on one side: if `p` is monotone on `[0, δ]` with
`p(0+) = L`, then `∫₀^δ p(v) sin(ηv)/(πv) dv → L/2`. -/
private lemma tendsto_integral_monotoneOn_mul_sin_div {p : ℝ → ℝ} {δ L : ℝ} (hδ : 0 < δ)
    (hp : MonotoneOn p (Icc 0 δ)) (hL : Tendsto p (𝓝[>] 0) (𝓝 L)) :
    Tendsto (fun η : ℝ => ∫ v in (0 : ℝ)..δ, p v * (Real.sin (η * v) / (π * v))) atTop
      (𝓝 (L / 2)) := by
  obtain ⟨C, hC⟩ := exists_bound_integral_sin_mul_div
  have hLle : ∀ v ∈ Ioc 0 δ, L ≤ p v := by
    intro v hv
    refine le_of_tendsto hL ?_
    filter_upwards [Ioo_mem_nhdsGT hv.1] with w hw
    exact hp ⟨hw.1.le, hw.2.le.trans hv.2⟩ ⟨hv.1.le, hv.2⟩ hw.2.le
  set f : ℝ → ℝ := fun v => max (p v - L) 0 with hf
  have hfm : MonotoneOn f (Icc 0 δ) := fun x hx y hy hxy =>
    max_le_max (by linarith [hp hx hy hxy]) le_rfl
  have hpi : IntervalIntegrable p volume 0 δ := by
    refine MonotoneOn.intervalIntegrable ?_
    rwa [uIcc_of_le hδ.le]
  have hfi : IntervalIntegrable f volume 0 δ := by
    refine MonotoneOn.intervalIntegrable ?_
    rwa [uIcc_of_le hδ.le]
  have hf0 : Tendsto f (𝓝[>] 0) (𝓝 0) := by
    have := (hL.sub_const L).max (tendsto_const_nhds (x := (0 : ℝ)))
    simpa using this
  have hdec : ∀ η : ℝ, ∫ v in (0 : ℝ)..δ, p v * (Real.sin (η * v) / (π * v)) =
      (∫ v in (0 : ℝ)..δ, f v * (Real.sin (η * v) / (π * v))) +
        L * ∫ v in (0 : ℝ)..δ, Real.sin (η * v) / (π * v) := by
    intro η
    have hKi : IntervalIntegrable (fun v => Real.sin (η * v) / (π * v)) volume 0 δ := by
      simpa using intervalIntegrable_mul_sin_div
        (intervalIntegrable_const (c := (1 : ℝ)) (a := 0) (b := δ)) η
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add
      (intervalIntegrable_mul_sin_div hfi η) (hKi.const_mul L),
      intervalIntegral.integral_of_le hδ.le, intervalIntegral.integral_of_le hδ.le]
    refine setIntegral_congr_fun measurableSet_Ioc fun v hv => ?_
    simp only [hf]
    rw [max_eq_left (by linarith [hLle v hv])]
    ring
  have hmain : Tendsto (fun η : ℝ => ∫ v in (0 : ℝ)..δ, f v * (Real.sin (η * v) / (π * v)))
      atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    set ε' : ℝ := ε / (2 * (|C| / π + 1)) with hε'
    have hε'0 : 0 < ε' := by positivity
    have hI : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Ioo 0 δ := Ioo_mem_nhdsGT hδ
    obtain ⟨ρ, hρf, hρδ⟩ := ((hf0.eventually (gt_mem_nhds hε'0)).and hI).exists
    have hρ0 : 0 < ρ := hρδ.1
    -- the tail, by Riemann–Lebesgue
    set k : ℝ → ℂ := fun v => (((Ioc ρ δ).indicator (fun v => f v / (π * v)) v : ℝ) : ℂ)
      with hk
    have hk_int : Integrable k := by
      have hfρ : IntegrableOn f (Ioc ρ δ) := by
        have hsub : uIcc ρ δ ⊆ uIcc 0 δ := by
          rw [uIcc_of_le hδ.le, uIcc_of_le hρδ.2.le]
          exact Icc_subset_Icc_left hρ0.le
        have : IntervalIntegrable f volume ρ δ := hfi.mono_set hsub
        exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hρδ.2.le).1 this
      have h2 : IntegrableOn (fun v => f v * (π * v)⁻¹) (Ioc ρ δ) := by
        refine hfρ.mul_bdd (c := (π * ρ)⁻¹) (by fun_prop : Measurable fun v : ℝ =>
          (π * v)⁻¹).aestronglyMeasurable ?_
        refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun v hv => ?_)
        rw [Real.norm_eq_abs, abs_inv, abs_of_pos (by have := hρ0.trans hv.1; positivity)]
        exact inv_anti₀ (by positivity) (by gcongr; exact hv.1.le)
      have h1 : IntegrableOn (fun v => f v / (π * v)) (Ioc ρ δ) :=
        h2.congr_fun (fun v _ => by simp only [div_eq_mul_inv]) measurableSet_Ioc
      exact ((h1.integrable_indicator measurableSet_Ioc).ofReal)
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (tendsto_integral_mul_sin_atTop hk_int) (ε / 2)
      (half_pos hε)
    refine ⟨max N 1, fun η hη => ?_⟩
    have hη0 : 0 < η := lt_of_lt_of_le one_pos (le_of_max_le_right hη)
    have hRL := hN η (le_of_max_le_left hη)
    have htail : ∫ v, k v * (Real.sin (η * v) : ℂ) =
        ((∫ v in ρ..δ, f v * (Real.sin (η * v) / (π * v)) : ℝ) : ℂ) := by
      rw [intervalIntegral.integral_of_le hρδ.2.le, ← integral_indicator measurableSet_Ioc,
        ← integral_complex_ofReal]
      refine integral_congr_ae (Eventually.of_forall fun v => ?_)
      simp only [hk]
      by_cases hv : v ∈ Ioc ρ δ
      · rw [indicator_of_mem hv, indicator_of_mem hv]
        push_cast
        ring
      · rw [indicator_of_notMem hv, indicator_of_notMem hv]
        simp
    rw [htail, dist_zero_right, Complex.norm_real, Real.norm_eq_abs] at hRL
    -- the head, by the second mean value theorem
    have hKρ : IntervalIntegrable (fun v => Real.sin (η * v) / (π * v)) volume 0 ρ := by
      simpa using intervalIntegrable_mul_sin_div
        (intervalIntegrable_const (c := (1 : ℝ)) (a := 0) (b := ρ)) η
    obtain ⟨ξ, -, hξ⟩ := exists_le_const_mul_norm_intervalIntegral_of_nonneg_of_monotoneOn
      hρ0.le (show 0 ≤ f 0 from le_max_right _ _) (hfm.mono (Icc_subset_Icc_right hρδ.2.le)) hKρ
    simp only [smul_eq_mul, Real.norm_eq_abs] at hξ
    have hKξ : |∫ x in ξ..ρ, Real.sin (η * x) / (π * x)| ≤ |C| / π := by
      have : ∫ x in ξ..ρ, Real.sin (η * x) / (π * x) =
          π⁻¹ * ∫ x in ξ..ρ, Real.sin (η * x) / x := by
        rw [← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_congr fun v _ => ?_
        ring
      rw [this, abs_mul, abs_inv, abs_of_pos Real.pi_pos, inv_mul_eq_div]
      exact div_le_div_of_nonneg_right ((hC η hη0 ξ ρ).trans (le_abs_self C)) Real.pi_pos.le
    have hfρ0 : 0 ≤ f ρ := le_max_right _ _
    have hhead : |∫ v in (0 : ℝ)..ρ, f v * (Real.sin (η * v) / (π * v))| ≤ ε' * (|C| / π) :=
      hξ.trans (mul_le_mul hρf.le hKξ (abs_nonneg _) hε'0.le)
    have hs1 : uIcc 0 ρ ⊆ uIcc 0 δ := by
      rw [uIcc_of_le hδ.le, uIcc_of_le hρ0.le]; exact Icc_subset_Icc_right hρδ.2.le
    have hs2 : uIcc ρ δ ⊆ uIcc 0 δ := by
      rw [uIcc_of_le hδ.le, uIcc_of_le hρδ.2.le]; exact Icc_subset_Icc_left hρ0.le
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      ((intervalIntegrable_mul_sin_div hfi η).mono_set hs1)
      ((intervalIntegrable_mul_sin_div hfi η).mono_set hs2)
    rw [dist_zero_right, Real.norm_eq_abs, ← hsplit]
    have hε'C : ε' * (|C| / π) < ε / 2 := by
      rw [hε', div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) two_pos]
      have : 0 ≤ |C| / π := by positivity
      nlinarith
    calc _ ≤ |∫ v in (0 : ℝ)..ρ, f v * (Real.sin (η * v) / (π * v))| +
          |∫ v in ρ..δ, f v * (Real.sin (η * v) / (π * v))| := abs_add_le _ _
      _ < ε / 2 + ε / 2 := by linarith
      _ = ε := add_halves ε
  have h := hmain.add ((tendsto_integral_sin_mul_div_pi hδ).const_mul L)
  rw [zero_add, show L * (1 / 2) = L / 2 by ring] at h
  exact h.congr fun η => (hdec η).symm


private lemma intervalIntegrable_ofReal {u : ℝ → ℝ} {a b : ℝ}
    (h : IntervalIntegrable u volume a b) :
    IntervalIntegrable (fun v => (u v : ℂ)) volume a b :=
  ⟨h.1.ofReal, h.2.ofReal⟩

/-- One-sided Dirichlet–Jordan for a real function of bounded variation on `[0, δ]`. -/
private lemma tendsto_integral_boundedVariationOn_real {φ : ℝ → ℝ} {δ L : ℝ} (hδ : 0 < δ)
    (hφ : BoundedVariationOn φ (Icc 0 δ)) (hL : Tendsto φ (𝓝[>] 0) (𝓝 L)) :
    IntervalIntegrable φ volume 0 δ ∧
      Tendsto (fun η : ℝ => ∫ v in (0 : ℝ)..δ, φ v * (Real.sin (η * v) / (π * v))) atTop
        (𝓝 (L / 2)) := by
  obtain ⟨p, q, hp, hq, rfl⟩ := hφ.locallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn
  have hne : (Ioo (0 : ℝ) δ).Nonempty := ⟨δ / 2, by constructor <;> linarith⟩
  have hbdd : ∀ r : ℝ → ℝ, MonotoneOn r (Icc 0 δ) → BddBelow (r '' Ioo 0 δ) := by
    intro r hr
    exact ⟨r 0, by
      rintro _ ⟨w, hw, rfl⟩
      exact hr ⟨le_rfl, hδ.le⟩ ⟨hw.1.le, hw.2.le⟩ hw.1.le⟩
  have hpL := (hp.mono Ioo_subset_Icc_self).tendsto_nhdsWithin_Ioo_right hne (hbdd p hp)
  have hqL := (hq.mono Ioo_subset_Icc_self).tendsto_nhdsWithin_Ioo_right hne (hbdd q hq)
  have hLeq := tendsto_nhds_unique hL (hpL.sub hqL)
  have hint : ∀ r : ℝ → ℝ, MonotoneOn r (Icc 0 δ) → IntervalIntegrable r volume 0 δ := by
    intro r hr
    refine MonotoneOn.intervalIntegrable ?_
    rwa [uIcc_of_le hδ.le]
  refine ⟨(hint p hp).sub (hint q hq), ?_⟩
  have h := (tendsto_integral_monotoneOn_mul_sin_div hδ hp hpL).sub
    (tendsto_integral_monotoneOn_mul_sin_div hδ hq hqL)
  rw [← sub_div, ← hLeq] at h
  refine h.congr fun η => ?_
  rw [← intervalIntegral.integral_sub (intervalIntegrable_mul_sin_div (hint p hp) η)
    (intervalIntegrable_mul_sin_div (hint q hq) η)]
  refine intervalIntegral.integral_congr fun v _ => ?_
  simp only [Pi.sub_apply]
  ring

/-- One-sided Dirichlet–Jordan for a complex function of bounded variation on `[0, δ]`: if
`g(0+) = L`, then `∫₀^δ g(v) sin(ηv)/(πv) dv → L/2`. -/
lemma tendsto_intervalIntegral_mul_sin_div_of_boundedVariationOn {g : ℝ → ℂ} {δ : ℝ} {L : ℂ}
    (hδ : 0 < δ) (hg : BoundedVariationOn g (Icc 0 δ)) (hL : Tendsto g (𝓝[>] 0) (𝓝 L)) :
    IntervalIntegrable g volume 0 δ ∧
      Tendsto (fun η : ℝ => ∫ v in (0 : ℝ)..δ,
        g v * ((Real.sin (η * v) / (π * v) : ℝ) : ℂ)) atTop (𝓝 (L / 2)) := by
  obtain ⟨hire, hre⟩ := tendsto_integral_boundedVariationOn_real hδ
    (Complex.reCLM.lipschitzWith.comp_boundedVariationOn hg)
    ((Complex.reCLM.continuous.tendsto L).comp hL)
  obtain ⟨hiim, him⟩ := tendsto_integral_boundedVariationOn_real hδ
    (Complex.imCLM.lipschitzWith.comp_boundedVariationOn hg)
    ((Complex.imCLM.continuous.tendsto L).comp hL)
  simp only [Function.comp_def, Complex.reCLM_apply, Complex.imCLM_apply] at hire hre hiim him
  have hgi : IntervalIntegrable g volume 0 δ := by
    have := (intervalIntegrable_ofReal hire).add
      ((intervalIntegrable_ofReal hiim).mul_const Complex.I)
    refine this.congr fun v _ => ?_
    simp [Complex.re_add_im]
  refine ⟨hgi, ?_⟩
  have h := ((Complex.continuous_ofReal.tendsto _).comp hre).add
    (((Complex.continuous_ofReal.tendsto _).comp him).mul_const Complex.I)
  have hL2 : (((L.re / 2 : ℝ) : ℂ) + ((L.im / 2 : ℝ) : ℂ) * Complex.I) = L / 2 := by
    apply Complex.ext <;> simp
  rw [hL2] at h
  refine h.congr fun η => ?_
  simp only [Function.comp_apply]
  rw [← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_ofReal,
    ← intervalIntegral.integral_mul_const, ← intervalIntegral.integral_add]
  · refine intervalIntegral.integral_congr fun v _ => ?_
    apply Complex.ext <;> simp [sub_eq_add_neg]
  · exact intervalIntegrable_ofReal (intervalIntegrable_mul_sin_div hire η)
  · exact (intervalIntegrable_ofReal (intervalIntegrable_mul_sin_div hiim η)).mul_const _


/-- `u ↦ e^{-σu}` has bounded variation on every compact interval. -/
theorem boundedVariationOn_exp_neg_mul (σ a b : ℝ) :
    BoundedVariationOn (fun u : ℝ => Real.exp (-σ * u)) (Icc a b) := by
  rcases le_or_gt σ 0 with hσ | hσ
  · have hm : MonotoneOn (fun u : ℝ => Real.exp (-σ * u)) (Icc a b) := fun x _ y _ hxy => by
      dsimp only
      gcongr
      nlinarith
    rcases le_or_gt a b with hab | hab
    · simpa using hm.locallyBoundedVariationOn a b ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩
    · simp [Icc_eq_empty_of_lt hab]
  · have hm : MonotoneOn (fun w : ℝ => Real.exp (σ * w)) (Icc (-b) (-a)) := fun x _ y _ hxy => by
      dsimp only
      gcongr
    have hle := eVariationOn.comp_le_of_antitoneOn (fun w : ℝ => Real.exp (σ * w))
      (s := Icc (-b) (-a)) (t := Icc a b) (fun u => -u) (fun x _ y _ hxy => by simpa using hxy)
      (fun u hu => ⟨by linarith [hu.2], by linarith [hu.1]⟩)
    refine ne_top_of_le_ne_top ?_ (le_of_eq_of_le ?_ hle)
    · rcases le_or_gt a b with hab | hab
      · have := hm.locallyBoundedVariationOn (-b) (-a) ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩
        simp only [inter_self] at this
        exact this
      · rw [Icc_eq_empty_of_lt (by linarith : -a < -b)]
        simp
    · congr 1
      funext u
      simp only [Function.comp_apply]
      ring_nf

/-- **Dirichlet–Jordan theorem** for Fourier integrals: if `g` is integrable on `ℝ` and of
bounded variation on `[t - δ, t + δ]`, with one-sided limits `g(t+) = gp` and `g(t-) = gm`, then
`∫ g(u) sin(η(t - u))/(π(t - u)) du → (gp + gm)/2` as `η → ∞`. -/
theorem tendsto_integral_mul_sin_div_of_boundedVariationOn {g : ℝ → ℂ} (hg : Integrable g)
    {t δ : ℝ} (hδ : 0 < δ) (hbv : BoundedVariationOn g (Icc (t - δ) (t + δ))) {gp gm : ℂ}
    (hp : Tendsto g (𝓝[>] t) (𝓝 gp)) (hm : Tendsto g (𝓝[<] t) (𝓝 gm)) :
    Tendsto (fun η : ℝ => ∫ u, g u * ((Real.sin (η * (t - u)) / (π * (t - u)) : ℝ) : ℂ))
      atTop (𝓝 ((gp + gm) / 2)) := by
  -- the two one-sided pieces
  have hbv₁ : BoundedVariationOn (fun v => g (t - v)) (Icc 0 δ) := by
    refine ne_top_of_le_ne_top hbv (eVariationOn.comp_le_of_antitoneOn g (fun v => t - v)
      (fun x _ y _ hxy => by linarith) fun v hv => ?_)
    constructor <;> linarith [hv.1, hv.2]
  have hbv₂ : BoundedVariationOn (fun v => g (t + v)) (Icc 0 δ) := by
    refine ne_top_of_le_ne_top hbv (eVariationOn.comp_le_of_monotoneOn g (fun v => t + v)
      (fun x _ y _ hxy => by linarith) fun v hv => ?_)
    constructor <;> linarith [hv.1, hv.2]
  have hlim₁ : Tendsto (fun v => g (t - v)) (𝓝[>] 0) (𝓝 gm) := by
    refine hm.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_)
    · have : Tendsto (fun v : ℝ => t - v) (𝓝 0) (𝓝 (t - 0)) :=
        tendsto_const_nhds.sub tendsto_id
      rw [sub_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with v hv
      exact sub_lt_self t hv
  have hlim₂ : Tendsto (fun v => g (t + v)) (𝓝[>] 0) (𝓝 gp) := by
    refine hp.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_)
    · have : Tendsto (fun v : ℝ => t + v) (𝓝 0) (𝓝 (t + 0)) :=
        tendsto_const_nhds.add tendsto_id
      rw [add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with v hv
      exact lt_add_of_pos_right t hv
  obtain ⟨hi₁, h₁⟩ := tendsto_intervalIntegral_mul_sin_div_of_boundedVariationOn hδ hbv₁ hlim₁
  obtain ⟨hi₂, h₂⟩ := tendsto_intervalIntegral_mul_sin_div_of_boundedVariationOn hδ hbv₂ hlim₂
  -- the regular part
  have hgs : Integrable fun v => g (t - v) := hg.comp_sub_left t
  set k : ℝ → ℂ := fun v => (Icc (-δ) δ)ᶜ.indicator (fun v => g (t - v) *
    (((π * v)⁻¹ : ℝ) : ℂ)) v with hk
  have hkm : AEStronglyMeasurable k volume :=
    (hgs.aestronglyMeasurable.mul (by fun_prop : Measurable fun v : ℝ =>
      (((π * v)⁻¹ : ℝ) : ℂ)).aestronglyMeasurable).indicator measurableSet_Icc.compl
  have hki : Integrable k := by
    refine (hgs.norm.div_const (π * δ)).mono' hkm (Eventually.of_forall fun v => ?_)
    simp only [hk]
    by_cases hv : v ∈ (Icc (-δ) δ)ᶜ
    · rw [indicator_of_mem hv, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_mul,
        abs_of_pos Real.pi_pos, ← div_eq_mul_inv]
      have hvd : δ < |v| := by
        by_contra h
        exact hv (abs_le.1 (not_lt.1 h))
      gcongr
    · rw [indicator_of_notMem hv, norm_zero]
      positivity
  have hKi : ∀ η : ℝ, Integrable fun v => g (t - v) * ((Real.sin (η * v) / (π * v) : ℝ) : ℂ) :=
    fun η => hgs.mul_bdd (c := |η| / π) (by fun_prop : Measurable fun v : ℝ =>
      ((Real.sin (η * v) / (π * v) : ℝ) : ℂ)).aestronglyMeasurable
      (Eventually.of_forall fun v => by
        rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_sin_mul_div_le η v)
  have hdec : ∀ η : ℝ, ∫ u, g u * ((Real.sin (η * (t - u)) / (π * (t - u)) : ℝ) : ℂ) =
      (∫ v, k v * (Real.sin (η * v) : ℂ)) +
        ((∫ v in (0 : ℝ)..δ, g (t - v) * ((Real.sin (η * v) / (π * v) : ℝ) : ℂ)) +
          ∫ v in (0 : ℝ)..δ, g (t + v) * ((Real.sin (η * v) / (π * v) : ℝ) : ℂ)) := by
    intro η
    have hsub := integral_sub_left_eq_self
      (fun v => g (t - v) * ((Real.sin (η * v) / (π * v) : ℝ) : ℂ)) volume t
    simp only [sub_sub_cancel] at hsub
    rw [hsub]
    have hkS : Integrable fun v => k v * (Real.sin (η * v) : ℂ) :=
      hki.mul_bdd (c := 1) (by fun_prop : Measurable fun v : ℝ =>
        (Real.sin (η * v) : ℂ)).aestronglyMeasurable
        (Eventually.of_forall fun v => by
          rw [Complex.norm_real, Real.norm_eq_abs]; exact Real.abs_sin_le_one _)
    have hI := (hKi η).indicator (measurableSet_Icc (a := -δ) (b := δ))
    have hpt : (fun v => g (t - v) * ((Real.sin (η * v) / (π * v) : ℝ) : ℂ)) =
        fun v => k v * (Real.sin (η * v) : ℂ) + (Icc (-δ) δ).indicator
          (fun v => g (t - v) * ((Real.sin (η * v) / (π * v) : ℝ) : ℂ)) v := by
      funext v
      simp only [hk]
      by_cases hv : v ∈ Icc (-δ) δ
      · rw [indicator_of_notMem (not_not.2 hv), indicator_of_mem hv, zero_mul, zero_add]
      · rw [indicator_of_mem hv, indicator_of_notMem hv, add_zero]
        push_cast
        rcases eq_or_ne v 0 with rfl | hv0
        · simp
        have : (π : ℂ) * v ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.2 Real.pi_ne_zero)
          (Complex.ofReal_ne_zero.2 hv0)
        field_simp
    conv_lhs => rw [hpt]
    rw [integral_add hkS hI, integral_indicator measurableSet_Icc,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
      ← intervalIntegral.integral_add_adjacent_intervals (b := 0)
        (hKi η).intervalIntegrable (hKi η).intervalIntegrable, add_comm
        (∫ v in (-δ)..0, _)]
    congr 2
    have h := intervalIntegral.integral_comp_neg (a := 0) (b := δ)
      (fun v => g (t - v) * ((Real.sin (η * v) / (π * v) : ℝ) : ℂ))
    simp only [neg_zero, sub_neg_eq_add, mul_neg, Real.sin_neg, neg_div_neg_eq] at h
    exact h.symm
  have h := (tendsto_integral_mul_sin_atTop hki).add (h₁.add h₂)
  rw [zero_add, ← add_div, add_comm gm] at h
  exact h.congr fun η => (hdec η).symm

end Real
