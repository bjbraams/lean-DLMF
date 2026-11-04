/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AlgebraicAnalytic.Summability.Basic
public import DLMFMathlib.Analysis.Complex.ParametricHolomorphy
public import DLMFMathlib.Analysis.SpecialFunctions.Trigonometric.OneSubCosIntegral
public import TauCeti.Analysis.Fourier.ExpNegAbs
public import DLMFMathlib.MeasureTheory.Integral.ApproximateIdentity

/-!
# Summability of integrals and of Fourier integrals (DLMF §1.15(iv)–(v))

The Abel and Cesàro summability of integrals over `(-∞, ∞)` (`HasAbelIntegral`,
`HasCesaroIntegral`, 1.15.29–1.15.32), and the Poisson and Fejér kernels of Fourier integrals
(1.15.33–1.15.46) with DLMF's Fourier transform 1.14.1.

## Main results

* `hasAbelIntegral_of_integrable`, `hasCesaroIntegral_of_integrable`,
  `hasAbelIntegral_of_tendsto`, `hasCesaroIntegral_of_tendsto`: regularity of Abel and Cesàro
  summation of integrals (§1.15(iv)).
* `integral_halfPlanePoissonKernel`, `tendsto_integral_halfPlanePoissonKernel_tail`: the
  half-plane Poisson kernel (DLMF 1.15.34–1.15.35).
* `fourierAbelMean_eq_poisson`, `tendsto_integral_norm_fourierAbelMean_sub`: Abel means of
  Fourier integrals (DLMF 1.15.37–1.15.38).
* `re_poissonCauchyIntegral`, `im_poissonCauchyIntegral`,
  `differentiableOn_poissonCauchyIntegral`, `tendsto_im_poissonCauchyIntegral`: the Cauchy
  integral `Φ` (§1.15(v), 1.15.40).
* `integral_fejerKernelLine`, `tendsto_integral_fejerKernelLine_tail`: the Fejér kernel on the
  line (DLMF 1.15.42–1.15.43).
* `fourierCesaroMeanIntegral_eq`, `tendsto_integral_norm_fourierCesaroMeanIntegral_sub`: Cesàro
  means of Fourier integrals (DLMF 1.15.45–1.15.46).

## Implementation notes

**Correction (§1.15(v), after 1.15.40).** DLMF says that `lim_{y→0+} ℑΦ(x + iy)` "is the Hilbert
transform of `f(x)` (§1.14(v))". With DLMF's own normalization 1.14.41 (denominator `t - x`) the
limit is `-ℋ(f)(x)`: by 1.15.40 and 1.14.42 the kernels are `(x - t)/((x - t)² + y²)` and
`(t - x)/((t - x)² + y²)`. Numerically, for `f(t) = 1/(1 + t²)` and `x = 0.6`,
`ℑΦ(x + 0.001i) = 0.4405` while `ℋf(x) = -x/(1 + x²) = -0.4412` (1.14.43).
`tendsto_im_poissonCauchyIntegral` states the corrected form.
-/

@[expose] public noncomputable section

open MeasureTheory Complex Set Filter Topology

namespace DLMF.AlgebraicAnalytic

/-! ### Summability of integrals (§1.15(iv)) -/

/-- DLMF §1.15(iv): if `∫_{-∞}^{∞} f(t) dt` converges absolutely and equals `L`, then the integral
is Abel summable to `L`. Proved by dominated convergence. -/
@[dlmf 1.15.iv]
theorem hasAbelIntegral_of_integrable {f : ℝ → ℂ} (hf : Integrable f) :
    HasAbelIntegral f (∫ t, f t) := by
  have hmeas : ∀ ε : ℝ, AEStronglyMeasurable (fun t => (Real.exp (-ε * |t|) : ℂ) * f t) :=
    fun ε => (by fun_prop : Continuous fun t : ℝ => (Real.exp (-ε * |t|) : ℂ))
      |>.aestronglyMeasurable.mul hf.aestronglyMeasurable
  have hbound : ∀ ε : ℝ, 0 ≤ ε → ∀ t, ‖(Real.exp (-ε * |t|) : ℂ) * f t‖ ≤ ‖f t‖ := by
    intro ε hε t
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have : Real.exp (-ε * |t|) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg t])
    exact mul_le_of_le_one_left (norm_nonneg _) this
  refine ⟨fun ε hε => hf.norm.mono' (hmeas ε)
    (Eventually.of_forall (hbound ε hε.le)), ?_⟩
  have h := tendsto_integral_filter_of_dominated_convergence (l := 𝓝[>] (0 : ℝ))
    (F := fun ε t => (Real.exp (-ε * |t|) : ℂ) * f t) (f := f) (fun t => ‖f t‖)
    (Eventually.of_forall hmeas)
    (eventually_nhdsWithin_of_forall fun ε hε => Eventually.of_forall (hbound ε (le_of_lt hε)))
    hf.norm ?_
  · exact h
  · refine Eventually.of_forall fun t => ?_
    have hc : Tendsto (fun ε : ℝ => (Real.exp (-ε * |t|) : ℂ) * f t) (𝓝 0)
        (𝓝 ((Real.exp (-0 * |t|) : ℂ) * f t)) :=
      ((by fun_prop : Continuous fun ε : ℝ => (Real.exp (-ε * |t|) : ℂ) * f t).tendsto 0)
    simp only [neg_zero, zero_mul, Real.exp_zero, ofReal_one, one_mul] at hc
    exact hc.mono_left nhdsWithin_le_nhds

/-- DLMF §1.15(iv): if `∫_{-∞}^{∞} f(t) dt` converges absolutely and equals `L`, then the integral
is (C,1) summable to `L`. -/
@[dlmf 1.15.iv]
theorem hasCesaroIntegral_of_integrable {f : ℝ → ℂ} (hf : Integrable f) :
    HasCesaroIntegral f (∫ t, f t) := by
  set G : ℝ → ℝ → ℂ := fun R t =>
    (Ioc (-R) R).indicator (fun t => ((1 - |t| / R : ℝ) : ℂ) * f t) t
  have hEq : ∀ᶠ R in atTop, ∫ t in -R..R, ((1 - |t| / R : ℝ) : ℂ) * f t = ∫ t, G R t := by
    filter_upwards [eventually_gt_atTop 0] with R hR
    rw [intervalIntegral.integral_of_le (by linarith), integral_indicator measurableSet_Ioc]
  have hmeas : ∀ R, AEStronglyMeasurable (G R) := fun R =>
    (((by fun_prop : Continuous fun t : ℝ => ((1 - |t| / R : ℝ) : ℂ)).aestronglyMeasurable.mul
      hf.aestronglyMeasurable)).indicator measurableSet_Ioc
  have hbound : ∀ᶠ R in atTop, ∀ᵐ t, ‖G R t‖ ≤ ‖f t‖ := by
    filter_upwards [eventually_gt_atTop 0] with R hR
    refine Eventually.of_forall fun t => ?_
    simp only [G, indicator]
    split_ifs with ht
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have h1 : |t| ≤ R := abs_le.mpr ⟨ht.1.le, ht.2⟩
      have h2 : 0 ≤ |t| / R := div_nonneg (abs_nonneg t) hR.le
      have h3 : |t| / R ≤ 1 := (div_le_one hR).mpr h1
      rw [abs_of_nonneg (by linarith)]
      exact mul_le_of_le_one_left (norm_nonneg _) (by linarith)
    · simp
  have hlim : ∀ᵐ t, Tendsto (fun R => G R t) atTop (𝓝 (f t)) := by
    refine Eventually.of_forall fun t => ?_
    have h1 : Tendsto (fun R : ℝ => ((1 - |t| / R : ℝ) : ℂ) * f t) atTop
        (𝓝 (((1 - 0 : ℝ) : ℂ) * f t)) := by
      refine (Complex.continuous_ofReal.tendsto _ |>.comp ?_).mul_const _
      exact tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop tendsto_id)
    simp only [sub_zero, ofReal_one, one_mul] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop |t|] with R hR
    have : t ∈ Ioc (-R) R := ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
    simp only [G, indicator_of_mem this]
  exact (tendsto_integral_filter_of_dominated_convergence (fun t => ‖f t‖)
    (Eventually.of_forall hmeas) hbound hf.norm hlim).congr' (hEq.mono fun R h => h.symm)

/-- `u ↦ ∫_{-u}^u f` is continuous for locally integrable `f`. -/
private lemma continuous_integral_neg_self {f : ℝ → ℂ} (hf : LocallyIntegrable f) :
    Continuous fun u : ℝ => ∫ t in -u..u, f t := by
  have hii : ∀ a b : ℝ, IntervalIntegrable f volume a b := fun a b =>
    (intervalIntegrable_iff.mpr
      ((hf.integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc))
  have h1 := intervalIntegral.continuous_primitive hii 0
  have h2 : (fun u : ℝ => ∫ t in -u..u, f t) =
      fun u => (∫ t in (0 : ℝ)..u, f t) - ∫ t in (0 : ℝ)..(-u), f t := by
    ext u
    rw [intervalIntegral.integral_interval_sub_left (hii 0 u) (hii 0 (-u))]
  rw [h2]
  exact h1.sub (h1.comp continuous_neg)

/-- Fubini for the Fejér weight: `∫_{-R}^R (1 - |t|/R) f = R⁻¹ ∫_0^R ∫_{-u}^u f`. -/
private lemma integral_fejer_weight_eq {f : ℝ → ℂ} (hf : LocallyIntegrable f) {R : ℝ}
    (hR : 0 < R) :
    ∫ t in -R..R, ((1 - |t| / R : ℝ) : ℂ) * f t =
      (R : ℂ)⁻¹ * ∫ u in (0 : ℝ)..R, ∫ t in -u..u, f t := by
  set μ := volume.restrict (Ioc (-R) R)
  set ν := volume.restrict (Ioc (0 : ℝ) R)
  set g : ℝ → ℝ → ℂ := fun t u => (Ioi |t|).indicator (fun _ => f t) u with hg
  have hfi : Integrable f μ :=
    (hf.integrableOn_isCompact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hint : Integrable (Function.uncurry g) (μ.prod ν) := by
    refine Integrable.mono' ((hfi.norm).comp_fst ν) ?_ ?_
    · have hm : MeasurableSet {p : ℝ × ℝ | |p.1| < p.2} :=
        measurableSet_lt (measurable_fst.norm) measurable_snd
      have : Function.uncurry g = {p : ℝ × ℝ | |p.1| < p.2}.indicator (fun p => f p.1) := by
        ext ⟨t, u⟩
        simp [hg, Set.indicator]
      rw [this]
      exact (hfi.aestronglyMeasurable.comp_fst).indicator hm
    · refine Eventually.of_forall fun ⟨t, u⟩ => ?_
      simp only [Function.uncurry_apply_pair, hg]
      by_cases h : u ∈ Ioi |t|
      · simp [indicator_of_mem h]
      · simp [indicator_of_notMem h]
  have hswap := integral_integral_swap hint
  -- inner integrals
  have hin1 : ∀ t ∈ Ioc (-R) R, ∫ u, g t u ∂ν = ((R - |t| : ℝ) : ℂ) * f t := by
    intro t ht
    have hta : |t| ≤ R := abs_le.mpr ⟨ht.1.le, ht.2⟩
    simp only [hg, ν]
    rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
      setIntegral_const, Set.inter_comm, Ioc_inter_Ioi, max_eq_right (abs_nonneg t),
      Real.volume_real_Ioc, max_eq_left (by linarith),
      Complex.real_smul]
  have hin2 : ∀ u ∈ Ioc (0 : ℝ) R, ∫ t, g t u ∂μ = ∫ t in -u..u, f t := by
    intro u hu
    have hset : ∀ t, g t u = (Ioo (-u) u).indicator f t := by
      intro t
      simp only [hg, Set.indicator, mem_Ioi, mem_Ioo, abs_lt]
    simp only [hset, μ]
    rw [integral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo,
      Set.inter_eq_left.mpr (Ioo_subset_Ioc_self.trans (Ioc_subset_Ioc (by linarith [hu.2])
        hu.2)), intervalIntegral.integral_of_le (by linarith [hu.1]), integral_Ioc_eq_integral_Ioo]
  rw [intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_of_le hR.le]
  have e1 : ∫ t in Ioc (-R) R, ((1 - |t| / R : ℝ) : ℂ) * f t =
      (R : ℂ)⁻¹ * ∫ t, ∫ u, g t u ∂ν ∂μ := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    rw [hin1 t ht]
    have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
    push_cast
    field_simp
  have e2 : ∫ u, ∫ t, g t u ∂μ ∂ν = ∫ u in Ioc (0 : ℝ) R, ∫ t in -u..u, f t :=
    setIntegral_congr_fun measurableSet_Ioc fun u hu => hin2 u hu
  rw [e1, hswap, e2]

/-- Cesàro means of a continuous function with a limit: `R⁻¹ ∫_0^R F → L`. -/
private lemma tendsto_inv_mul_integral_of_tendsto {F : ℝ → ℂ} (hF : Continuous F) {L : ℂ}
    (h : Tendsto F atTop (𝓝 L)) :
    Tendsto (fun R : ℝ => (R : ℂ)⁻¹ * ∫ u in (0 : ℝ)..R, F u) atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨U₀, hU₀⟩ := Metric.tendsto_atTop.mp h (ε / 2) (half_pos hε)
  set U := max U₀ 0
  set C := ‖∫ u in (0 : ℝ)..U, (F u - L)‖
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun u => F u - L) volume a b := fun a b =>
    (hF.sub continuous_const).intervalIntegrable a b
  refine ⟨max (U + 1) (2 * C / ε + 1), fun R hR => ?_⟩
  have hRU : U + 1 ≤ R := le_trans (le_max_left _ _) hR
  have hRC : 2 * C / ε + 1 ≤ R := le_trans (le_max_right _ _) hR
  have hU0 : 0 ≤ U := le_max_right _ _
  have hR0 : 0 < R := by linarith
  have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hR0.ne'
  have hsplit : ((R : ℂ)⁻¹ * ∫ u in (0 : ℝ)..R, F u) - L =
      (R : ℂ)⁻¹ * ((∫ u in (0 : ℝ)..U, (F u - L)) + ∫ u in U..R, (F u - L)) := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hint 0 U) (hint U R),
      intervalIntegral.integral_sub (hF.intervalIntegrable 0 R) intervalIntegrable_const,
      intervalIntegral.integral_const, sub_zero, Complex.real_smul]
    field_simp
  have htail : ‖∫ u in U..R, (F u - L)‖ ≤ ε / 2 * (R - U) := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := U) (b := R)
      (C := ε / 2) (f := fun u => F u - L) (fun u hu => by
        rw [uIoc_of_le (by linarith)] at hu
        have := hU₀ u (le_trans (le_max_left _ _) hu.1.le)
        rw [dist_eq_norm] at this
        exact this.le)
    rwa [abs_of_nonneg (by linarith)] at this
  rw [dist_eq_norm, hsplit, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hR0.le]
  calc R⁻¹ * ‖(∫ u in (0 : ℝ)..U, (F u - L)) + ∫ u in U..R, (F u - L)‖
      ≤ R⁻¹ * (C + ε / 2 * (R - U)) := by
        gcongr
        exact (norm_add_le _ _).trans (add_le_add le_rfl htail)
    _ = C / R + ε / 2 * ((R - U) / R) := by field_simp
    _ ≤ C / R + ε / 2 * 1 := by
        gcongr
        rw [div_le_one hR0]; linarith
    _ < ε / 2 + ε / 2 := by
        have hCR : C / R < ε / 2 := by
          rw [div_lt_iff₀ hR0]
          have : 2 * C / ε < R := by linarith
          rw [div_lt_iff₀ hε] at this
          linarith
        linarith
    _ = ε := by ring

/-- DLMF §1.15(iv), improper case: if `f` is locally integrable and the improper integral
`lim_{a→-∞, b→∞} ∫_a^b f` equals `L`, then `∫ f = L (C,1)`. -/
@[dlmf 1.15.iv]
theorem hasCesaroIntegral_of_tendsto {f : ℝ → ℂ} (hf : LocallyIntegrable f) {L : ℂ}
    (h : Tendsto (fun p : ℝ × ℝ => ∫ t in p.1..p.2, f t) (atBot ×ˢ atTop) (𝓝 L)) :
    HasCesaroIntegral f L := by
  have hFc := continuous_integral_neg_self hf
  have hF : Tendsto (fun u : ℝ => ∫ t in -u..u, f t) atTop (𝓝 L) :=
    h.comp (tendsto_neg_atTop_atBot.prodMk tendsto_id)
  refine (tendsto_inv_mul_integral_of_tendsto hFc hF).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with R hR
  exact (integral_fejer_weight_eq hf hR).symm

/-- Fubini for the Abel weight: `∫ e^{-ε|t|} f = ε ∫_0^∞ e^{-εu} ∫_{-u}^u f`. -/
private lemma integral_exp_neg_abs_mul_eq {f : ℝ → ℂ} (hf : LocallyIntegrable f)
    (hint : ∀ ε : ℝ, 0 < ε → Integrable fun t => (Real.exp (-ε * |t|) : ℂ) * f t)
    {ε : ℝ} (hε : 0 < ε) :
    ∫ t, (Real.exp (-ε * |t|) : ℂ) * f t =
      (ε : ℂ) * ∫ u in Ioi (0 : ℝ), (Real.exp (-ε * u) : ℂ) * ∫ t in -u..u, f t := by
  set ν := volume.restrict (Ioi (0 : ℝ))
  set g : ℝ → ℝ → ℂ := fun t u => (Ioi |t|).indicator (fun u => (Real.exp (-ε * u) : ℂ) * f t) u
    with hg
  have hε2 : 0 < ε / 2 := half_pos hε
  have hintg : Integrable (Function.uncurry g) (volume.prod ν) := by
    have hdom := Integrable.mul_prod (hint (ε / 2) hε2).norm
      (integrableOn_exp_mul_Ioi (a := -(ε / 2)) (by linarith) 0)
    refine Integrable.mono' hdom ?_ ?_
    · have hm : MeasurableSet {p : ℝ × ℝ | |p.1| < p.2} :=
        measurableSet_lt (measurable_fst.norm) measurable_snd
      have : Function.uncurry g = {p : ℝ × ℝ | |p.1| < p.2}.indicator
          (fun p => (Real.exp (-ε * p.2) : ℂ) * f p.1) := by
        ext ⟨t, u⟩
        simp [hg, Set.indicator]
      rw [this]
      refine AEStronglyMeasurable.indicator ?_ hm
      exact ((Complex.continuous_ofReal.comp (Real.continuous_exp.comp
        (continuous_const.mul continuous_snd))).aestronglyMeasurable).mul
        hf.aestronglyMeasurable.comp_fst
    · refine Eventually.of_forall fun ⟨t, u⟩ => ?_
      simp only [Function.uncurry_apply_pair, hg]
      by_cases h : u ∈ Ioi |t|
      · rw [indicator_of_mem h, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg (Real.exp_pos _).le]
        have hu : |t| < u := h
        have : Real.exp (-ε * u) ≤ Real.exp (-(ε / 2) * |t|) * Real.exp (-(ε / 2) * u) := by
          rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith)
        calc Real.exp (-ε * u) * ‖f t‖
            ≤ Real.exp (-(ε / 2) * |t|) * Real.exp (-(ε / 2) * u) * ‖f t‖ :=
              mul_le_mul_of_nonneg_right this (norm_nonneg _)
          _ = _ := by ring
      · rw [indicator_of_notMem h, norm_zero]
        positivity
  have hswap := integral_integral_swap hintg
  have hin1 : ∀ t, ∫ u, g t u ∂ν = ((Real.exp (-ε * |t|) / ε : ℝ) : ℂ) * f t := by
    intro t
    simp only [hg, ν]
    rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
      Ioi_inter_Ioi, max_eq_left (abs_nonneg t), integral_mul_const, integral_complex_ofReal,
      integral_exp_mul_Ioi (by linarith)]
    congr 2
    field_simp
  have hin2 : ∀ u ∈ Ioi (0 : ℝ), ∫ t, g t u = (Real.exp (-ε * u) : ℂ) * ∫ t in -u..u, f t := by
    intro u hu
    have hset : ∀ t, g t u = (Ioo (-u) u).indicator
        (fun t => (Real.exp (-ε * u) : ℂ) * f t) t := by
      intro t
      simp only [hg, Set.indicator, mem_Ioi, mem_Ioo, abs_lt]
    simp only [hset]
    rw [integral_indicator measurableSet_Ioo, integral_const_mul,
      intervalIntegral.integral_of_le (by linarith [show (0 : ℝ) < u from hu]),
      integral_Ioc_eq_integral_Ioo]
  have e1 : ∫ t, (Real.exp (-ε * |t|) : ℂ) * f t = (ε : ℂ) * ∫ t, ∫ u, g t u ∂ν := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [hin1]
    have hε' : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
    push_cast
    field_simp
  have e2 : ∫ u, ∫ t, g t u ∂volume ∂ν =
      ∫ u in Ioi (0 : ℝ), (Real.exp (-ε * u) : ℂ) * ∫ t in -u..u, f t :=
    setIntegral_congr_fun measurableSet_Ioi fun u hu => hin2 u hu
  rw [e1, hswap, e2]

/-- Abel means of a continuous function with a limit: `ε ∫_0^∞ e^{-εu} F(u) du → L`
as `ε → 0⁺`. -/
private lemma tendsto_mul_integral_exp_neg_of_tendsto {F : ℝ → ℂ} (hF : Continuous F) {L : ℂ}
    (h : Tendsto F atTop (𝓝 L)) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * ∫ u in Ioi (0 : ℝ), (Real.exp (-ε * u) : ℂ) * F u)
      (𝓝[>] 0) (𝓝 L) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro η hη
  obtain ⟨U₀, hU₀⟩ := Metric.tendsto_atTop.mp h (η / 2) (half_pos hη)
  set U := max U₀ 0
  have hU0 : 0 ≤ U := le_max_right _ _
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((hF.sub continuous_const).continuousOn (s := Icc 0 U))
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 ⟨le_rfl, hU0⟩)
  have hbd : ∀ u, 0 ≤ u → ‖F u - L‖ ≤ max B (η / 2) := by
    intro u hu
    rcases le_or_gt u U with h | h
    · exact (hB u ⟨hu, h⟩).trans (le_max_left _ _)
    · have := hU₀ u (le_trans (le_max_left _ _) h.le)
      rw [dist_eq_norm] at this
      exact this.le.trans (le_max_right _ _)
  refine ⟨η / (2 * (B * U + 1)), by positivity, fun ε hε hεδ => ?_⟩
  have hε0 : 0 < ε := hε
  rw [dist_zero_right, Real.norm_of_nonneg hε0.le] at hεδ
  have hexp_int : IntegrableOn (fun u : ℝ => Real.exp (-ε * u)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (by linarith) 0
  have hint : IntegrableOn (fun u : ℝ => (Real.exp (-ε * u) : ℂ) * (F u - L)) (Ioi 0) := by
    refine Integrable.mono' (hexp_int.mul_const (max B (η / 2))) ?_ ?_
    · exact ((Complex.continuous_ofReal.comp (Real.continuous_exp.comp
        (continuous_const.mul continuous_id))).mul
        (hF.sub continuous_const)).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
      exact mul_le_mul_of_nonneg_left (hbd u (le_of_lt hu)) (Real.exp_pos _).le
  have hone : (ε : ℂ) * ∫ u in Ioi (0 : ℝ), (Real.exp (-ε * u) : ℂ) = 1 := by
    rw [integral_complex_ofReal, integral_exp_mul_Ioi (by linarith), mul_zero, Real.exp_zero]
    have hε' : (ε : ℂ) ≠ 0 := by exact_mod_cast hε0.ne'
    push_cast
    field_simp
  have hFint : IntegrableOn (fun u : ℝ => (Real.exp (-ε * u) : ℂ) * F u) (Ioi 0) := by
    have h2 : IntegrableOn (fun u : ℝ => (Real.exp (-ε * u) : ℂ) * L) (Ioi 0) :=
      (hexp_int.ofReal).mul_const L
    refine (hint.add h2).congr_fun (fun u _ => by simp only [Pi.add_apply]; ring)
      measurableSet_Ioi
  have hdiff : (ε : ℂ) * (∫ u in Ioi (0 : ℝ), (Real.exp (-ε * u) : ℂ) * F u) - L =
      (ε : ℂ) * ∫ u in Ioi (0 : ℝ), (Real.exp (-ε * u) : ℂ) * (F u - L) := by
    have h2 : ∫ u in Ioi (0 : ℝ), (Real.exp (-ε * u) : ℂ) * (F u - L) =
        (∫ u in Ioi (0 : ℝ), (Real.exp (-ε * u) : ℂ) * F u) -
          (∫ u in Ioi (0 : ℝ), (Real.exp (-ε * u) : ℂ)) * L := by
      have hL : IntegrableOn (fun u : ℝ => (Real.exp (-ε * u) : ℂ) * L) (Ioi 0) :=
        (hexp_int.ofReal).mul_const L
      calc ∫ u in Ioi (0 : ℝ), (Real.exp (-ε * u) : ℂ) * (F u - L)
          = ∫ u in Ioi (0 : ℝ), ((Real.exp (-ε * u) : ℂ) * F u - (Real.exp (-ε * u) : ℂ) * L) :=
            setIntegral_congr_fun measurableSet_Ioi fun u _ => by ring
        _ = _ := integral_sub hFint hL
        _ = _ := by rw [integral_mul_const]
    rw [h2, mul_sub, ← mul_assoc, hone, one_mul]
  -- split the integral at `U`
  have hsplit : ∫ u in Ioi (0 : ℝ), (Real.exp (-ε * u) : ℂ) * (F u - L) =
      (∫ u in Ioc 0 U, (Real.exp (-ε * u) : ℂ) * (F u - L)) +
        ∫ u in Ioi U, (Real.exp (-ε * u) : ℂ) * (F u - L) := by
    rw [← setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi hU0)),
      Ioc_union_Ioi_eq_Ioi hU0]
  have h1 : ‖∫ u in Ioc 0 U, (Real.exp (-ε * u) : ℂ) * (F u - L)‖ ≤ B * U := by
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc 0 U) (C := B)
      (f := fun u => (Real.exp (-ε * u) : ℂ) * (F u - L)) measure_Ioc_lt_top (fun u hu => by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
        calc Real.exp (-ε * u) * ‖F u - L‖ ≤ 1 * B := by
              refine mul_le_mul ?_ (hB u ⟨hu.1.le, hu.2⟩) (norm_nonneg _) zero_le_one
              rw [Real.exp_le_one_iff]; nlinarith [hu.1]
          _ = B := one_mul B)
    rwa [Real.volume_real_Ioc, sub_zero, max_eq_left hU0] at this
  have h2 : ‖∫ u in Ioi U, (Real.exp (-ε * u) : ℂ) * (F u - L)‖ ≤ η / 2 / ε := by
    have hle := norm_integral_le_of_norm_le
      (f := fun u => (Real.exp (-ε * u) : ℂ) * (F u - L))
      ((integrableOn_exp_mul_Ioi (a := -ε) (by linarith) U).mul_const (η / 2))
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
        have := hU₀ u (le_trans (le_max_left _ _) (le_of_lt hu))
        rw [dist_eq_norm] at this
        exact mul_le_mul_of_nonneg_left this.le (Real.exp_pos _).le))
    rw [integral_mul_const, integral_exp_mul_Ioi (by linarith)] at hle
    refine hle.trans ?_
    rw [neg_div_neg_eq, div_mul_eq_mul_div, mul_comm, div_le_div_iff_of_pos_right hε0]
    have : Real.exp (-ε * U) ≤ 1 := by rw [Real.exp_le_one_iff]; nlinarith
    nlinarith
  rw [dist_eq_norm, hdiff, hsplit, norm_mul, Complex.norm_real, Real.norm_of_nonneg hε0.le]
  have hBU : ε * (B * U) < η / 2 := by
    have hpos : 0 < 2 * (B * U + 1) := by positivity
    rw [lt_div_iff₀ hpos] at hεδ
    nlinarith [mul_nonneg hB0 hU0]
  calc ε * ‖(∫ u in Ioc 0 U, (Real.exp (-ε * u) : ℂ) * (F u - L)) +
        ∫ u in Ioi U, (Real.exp (-ε * u) : ℂ) * (F u - L)‖
      ≤ ε * (B * U + η / 2 / ε) := by
        gcongr
        exact (norm_add_le _ _).trans (add_le_add h1 h2)
    _ = ε * (B * U) + η / 2 := by field_simp
    _ < η := by linarith

/-- DLMF §1.15(iv), improper case: if `f` is locally integrable, the improper integral
`lim_{a→-∞, b→∞} ∫_a^b f` equals `L`, and `e^{-ε|t|} f(t)` is absolutely integrable for each
`ε > 0`, then `∫ f = L (A)`. -/
@[dlmf 1.15.iv]
theorem hasAbelIntegral_of_tendsto {f : ℝ → ℂ} (hf : LocallyIntegrable f) {L : ℂ}
    (h : Tendsto (fun p : ℝ × ℝ => ∫ t in p.1..p.2, f t) (atBot ×ˢ atTop) (𝓝 L))
    (hint : ∀ ε : ℝ, 0 < ε → Integrable fun t => (Real.exp (-ε * |t|) : ℂ) * f t) :
    HasAbelIntegral f L := by
  have hFc := continuous_integral_neg_self hf
  have hF : Tendsto (fun u : ℝ => ∫ t in -u..u, f t) atTop (𝓝 L) :=
    h.comp (tendsto_neg_atTop_atBot.prodMk tendsto_id)
  refine ⟨hint, (tendsto_mul_integral_exp_neg_of_tendsto hFc hF).congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (integral_exp_neg_abs_mul_eq hf hint hε).symm

/-! ### Poisson kernel of the half-plane (§1.15(v)) -/

/-- DLMF 1.15.34: `(1/2π) ∫ P(x, y) dx = 1` for `y > 0`. Proved from Mathlib's
`integral_univ_inv_one_add_sq`. -/
@[dlmf 1.15.E34]
theorem integral_halfPlanePoissonKernel {y : ℝ} (hy : 0 < y) :
    1 / (2 * Real.pi) * ∫ x, halfPlanePoissonKernel x y = 1 := by
  have h1 : (fun x => halfPlanePoissonKernel x y) =
      fun x => (2 / y) * (1 + (x / y) ^ 2)⁻¹ := by
    funext x
    unfold halfPlanePoissonKernel
    have : y ≠ 0 := hy.ne'
    field_simp
    ring
  rw [h1, integral_const_mul, Measure.integral_comp_div (fun u => (1 + u ^ 2)⁻¹) y,
    integral_univ_inv_one_add_sq, abs_of_pos hy, smul_eq_mul]
  have : y ≠ 0 := hy.ne'
  field_simp

/-- DLMF 1.15.35: `∫_{|x| ≥ δ} P(x, y) dx → 0` as `y → 0+`, for `δ > 0`. -/
@[dlmf 1.15.E35]
theorem tendsto_integral_halfPlanePoissonKernel_tail {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun y => ∫ x in {x : ℝ | δ ≤ |x|}, halfPlanePoissonKernel x y) (𝓝[>] 0) (𝓝 0) := by
  let S : Set ℝ := {x : ℝ | δ ≤ |x|}
  let C : ℝ := (1 + δ ^ 2) / δ ^ 2
  have hC : 0 < C := by dsimp [C]; positivity
  have hrec (x : ℝ) (hx : x ∈ S) :
      1 / x ^ 2 ≤ C * (1 + x ^ 2)⁻¹ := by
    have hxδ : δ ^ 2 ≤ x ^ 2 := by
      have hh : δ ≤ |x| := hx
      nlinarith [sq_abs x]
    have hxpos : 0 < x ^ 2 := lt_of_lt_of_le (sq_pos_of_pos hδ) hxδ
    rw [← div_eq_mul_inv, div_le_div_iff₀ hxpos (by positivity)]
    dsimp [C]
    rw [div_mul_eq_mul_div, le_div_iff₀ (sq_pos_of_pos hδ)]
    nlinarith
  have hg : Integrable (fun x : ℝ => (1 + x ^ 2)⁻¹) (volume.restrict S) :=
    integrable_inv_one_add_sq.integrableOn
  have hbound (y : ℝ) (hy : 0 < y) :
      ‖∫ x in S, halfPlanePoissonKernel x y‖ ≤
        (2 * y * C) * ∫ x in S, (1 + x ^ 2)⁻¹ := by
    rw [← integral_const_mul]
    refine norm_integral_le_of_norm_le (hg.const_mul _) ?_
    filter_upwards [ae_restrict_mem (by dsimp [S]; measurability)] with x hx
    have hxpos : 0 < x ^ 2 := by
      have hh : δ ≤ |x| := hx
      have : 0 < |x| := hδ.trans_le hh
      nlinarith [sq_abs x]
    have hden : 0 < x ^ 2 + y ^ 2 := by positivity
    rw [halfPlanePoissonKernel, Real.norm_eq_abs, abs_of_pos (by positivity)]
    calc
      2 * y / (x ^ 2 + y ^ 2) ≤ 2 * y / x ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) hxpos (by nlinarith [sq_nonneg y])
      _ ≤ 2 * y * (C * (1 + x ^ 2)⁻¹) := by
        simpa only [div_eq_mul_inv, one_div, one_mul] using
          mul_le_mul_of_nonneg_left (hrec x hx) (by positivity : 0 ≤ 2 * y)
      _ = 2 * y * C * (1 + x ^ 2)⁻¹ := by ring
  have hlim : Tendsto (fun y : ℝ => (2 * y * C) * ∫ x in S, (1 + x ^ 2)⁻¹)
      (𝓝[>] 0) (𝓝 0) := by
    have ht : ContinuousAt (fun y : ℝ => (2 * y * C) * ∫ x in S, (1 + x ^ 2)⁻¹) 0 := by fun_prop
    simpa using ht.tendsto.mono_left nhdsWithin_le_nhds
  exact squeeze_zero_norm'
      (by filter_upwards [self_mem_nhdsWithin] with y hy using hbound y hy) hlim

/-- DLMF 1.15.37: for `f` absolutely integrable and `y > 0`, the Abel mean 1.15.36 of the
Fourier integral is the Poisson integral `h(x, y) = (1/2π) ∫ f(t) P(x - t, y) dt`. -/
@[dlmf 1.15.E37]
theorem fourierAbelMean_eq_poisson {f : ℝ → ℂ} (hf : Integrable f) (x : ℝ) {y : ℝ}
    (hy : 0 < y) :
    fourierAbelMean f x y =
      ((2 * Real.pi : ℝ)⁻¹ : ℂ) * ∫ t, f t * (halfPlanePoissonKernel (x - t) y : ℂ) := by
  have he : Integrable fun t : ℝ => (Real.exp (-(y * |t|)) : ℂ) :=
    (TauCeti.integrable_exp_neg_mul_abs hy).ofReal
  set F : ℝ → ℝ → ℂ := fun t s =>
    cexp (-(I * x * t)) * cexp (I * t * s) * ((Real.exp (-(y * |t|)) : ℂ) * f s) with hF
  have hFi : Integrable (Function.uncurry F) (volume.prod volume) := by
    have hp := he.mul_prod hf
    refine (hp.bdd_mul (c := 1) (f := fun p : ℝ × ℝ =>
        cexp (-(I * x * p.1)) * cexp (I * p.1 * p.2)) ?_ ?_).congr
        (Eventually.of_forall fun p => ?_)
    · exact (by fun_prop : Continuous fun p : ℝ × ℝ =>
        cexp (-(I * x * p.1)) * cexp (I * p.1 * p.2)).aestronglyMeasurable
    · refine Eventually.of_forall fun p => ?_
      rw [norm_mul, Complex.norm_exp, Complex.norm_exp]
      simp
    · simp [hF, Function.uncurry]
  have hsq : ((Real.sqrt (2 * Real.pi))⁻¹ : ℂ) * ((Real.sqrt (2 * Real.pi))⁻¹ : ℂ) =
      ((2 * Real.pi : ℝ)⁻¹ : ℂ) := by
    rw [← mul_inv, ← ofReal_mul, Real.mul_self_sqrt (by positivity)]
  unfold fourierAbelMean fourierTransform
  have hin : ∀ t : ℝ, (Real.exp (-y * |t|) : ℂ) * cexp (-(I * x * t)) *
      (((Real.sqrt (2 * Real.pi))⁻¹ : ℂ) * ∫ s : ℝ, f s * cexp (I * t * s)) =
      ((Real.sqrt (2 * Real.pi))⁻¹ : ℂ) * ∫ s, F t s := by
    intro t
    conv_lhs => rw [← integral_const_mul, ← integral_const_mul]
    conv_rhs => rw [← integral_const_mul]
    congr 1; funext s
    simp only [hF, neg_mul]
    ring
  simp_rw [hin]
  rw [integral_const_mul, ← mul_assoc, hsq, integral_integral_swap hFi]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  simp only [hF]
  have h := TauCeti.integral_exp_mul_I_mul_exp_neg_mul_abs hy (s - x)
  calc ∫ t : ℝ, cexp (-(I * x * t)) * cexp (I * t * s) * ((Real.exp (-(y * |t|)) : ℂ) * f s)
      = (∫ t : ℝ, cexp (((s - x : ℝ) : ℂ) * t * I) * (Real.exp (-(y * |t|)) : ℂ)) * f s := by
        rw [← integral_mul_const]
        congr 1; funext t
        rw [show ((s - x : ℝ) : ℂ) * t * I = -(I * x * t) + I * t * s by push_cast; ring,
          Complex.exp_add]
        ring
    _ = f s * (halfPlanePoissonKernel (x - s) y : ℂ) := by
        rw [h, halfPlanePoissonKernel, mul_comm]
        congr 2
        ring


/-- Rescaling a convolution integral: `∫ f(t) K(x - t) dt = ∫ (εK(εu)) f(x - εu) du`. -/
private lemma integral_mul_kernel_eq_scaled {f : ℝ → ℂ} (K : ℝ → ℝ) (x : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    ∫ t, f t * (K (x - t) : ℂ) = ∫ u, (ε * K (ε * u)) • f (x - ε * u) := by
  have h1 : ∫ t, f t * (K (x - t) : ℂ) = ∫ s, f (x - s) * (K s : ℂ) := by
    rw [← integral_sub_left_eq_self (fun t => f t * (K (x - t) : ℂ)) volume x]
    simp
  have h2 := Measure.integral_comp_mul_left (fun s => f (x - s) * (K s : ℂ)) ε
  rw [abs_inv, abs_of_pos hε] at h2
  have h3 : ∫ u, (ε * K (ε * u)) • f (x - ε * u) =
      ε • ∫ u, f (x - ε * u) * (K (ε * u) : ℂ) := by
    rw [← integral_smul]
    congr 1; funext u
    rw [Complex.real_smul, Complex.real_smul]
    push_cast
    ring
  rw [h1, h3, h2, smul_smul, mul_inv_cancel₀ hε.ne', one_smul]

/-- The Cauchy density `1/(π(1 + u²))`. -/
private lemma halfPlanePoissonKernel_scaled {y : ℝ} (hy : 0 < y) (u : ℝ) :
    y * ((2 * Real.pi)⁻¹ * halfPlanePoissonKernel (y * u) y) = (Real.pi * (1 + u ^ 2))⁻¹ := by
  unfold halfPlanePoissonKernel
  have := Real.pi_pos
  field_simp
  ring

/-- DLMF 1.15.38: for `f` absolutely integrable, `∫ |h(x, y) - f(x)| dx → 0` as `y → 0+`. -/
@[dlmf 1.15.E38]
theorem tendsto_integral_norm_fourierAbelMean_sub {f : ℝ → ℂ} (hf : Integrable f) :
    Tendsto (fun y => ∫ x, ‖fourierAbelMean f x y - f x‖) (𝓝[>] 0) (𝓝 0) := by
  have hk : Integrable fun u : ℝ => (Real.pi * (1 + u ^ 2))⁻¹ := by
    refine (integrable_inv_one_add_sq.const_mul Real.pi⁻¹).congr
      (Eventually.of_forall fun u => ?_)
    simp only [mul_inv]
  have hk1 : ∫ u : ℝ, (Real.pi * (1 + u ^ 2))⁻¹ = 1 := by
    simp_rw [mul_inv]
    rw [integral_const_mul, integral_univ_inv_one_add_sq]
    exact inv_mul_cancel₀ Real.pi_ne_zero
  have h := (hf.tendsto_integral_norm_integral_smul_comp_sub_mul_sub hk
    (fun u => by positivity) hk1).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  rw [fourierAbelMean_eq_poisson hf x hy, ← integral_const_mul]
  have := integral_mul_kernel_eq_scaled (f := f)
    (fun s => (2 * Real.pi)⁻¹ * halfPlanePoissonKernel s y) x hy
  simp_rw [halfPlanePoissonKernel_scaled hy] at this
  rw [← this]
  congr 2
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  push_cast
  ring

/-- The integrand of 1.15.39 is integrable for integrable `f` and `y > 0`. -/
private lemma integrable_poissonCauchy_integrand {f : ℝ → ℝ} (hf : Integrable f)
    (x y : ℝ) (hy : 0 < y) :
    Integrable fun t : ℝ => (f t : ℂ) / ((x - t : ℝ) + I * y) := by
  have hne : ∀ t : ℝ, ((x - t : ℝ) : ℂ) + I * y ≠ 0 := by
    intro t h
    have := congrArg Complex.im h
    simp at this
    exact hy.ne' this
  have hb : ∀ t : ℝ, ‖(f t : ℂ) / ((x - t : ℝ) + I * y)‖ ≤ y⁻¹ * ‖f t‖ := by
    intro t
    rw [norm_div, Complex.norm_real, div_eq_inv_mul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rw [inv_le_inv₀ (norm_pos_iff.mpr (hne t)) hy]
    have : |(((x - t : ℝ) : ℂ) + I * y).im| ≤ ‖((x - t : ℝ) : ℂ) + I * y‖ := abs_im_le_norm _
    simpa [abs_of_pos hy] using this
  refine (hf.norm.const_mul y⁻¹).mono' ?_ (Eventually.of_forall hb)
  simp_rw [div_eq_mul_inv]
  refine (Complex.continuous_ofReal.comp_aestronglyMeasurable hf.aestronglyMeasurable).mul ?_
  have hc : Continuous fun t : ℝ => ((x - t : ℝ) : ℂ) + I * y := by fun_prop
  exact (hc.inv₀ hne).aestronglyMeasurable

/-- Pointwise splitting of the integrand of 1.15.39 into real and imaginary parts. -/
private lemma poissonCauchy_integrand_split (F u y : ℝ) (hy : 0 < y) :
    I / Real.pi * ((F : ℂ) / ((u : ℂ) + I * y)) =
      ((F * y / (Real.pi * (u ^ 2 + y ^ 2)) : ℝ) : ℂ) +
        I * ((F * u / (Real.pi * (u ^ 2 + y ^ 2)) : ℝ) : ℂ) := by
  have hD : 0 < u ^ 2 + y ^ 2 := by positivity
  have hpi := Real.pi_pos
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.div_re, Complex.div_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_apply, Complex.add_im,
      Complex.mul_im]
    field_simp
    ring
  · simp only [Complex.add_re, Complex.mul_re, Complex.div_re, Complex.div_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_apply, Complex.add_im,
      Complex.mul_im]
    field_simp
    ring

/-- The integral in 1.15.39 at `x + iy`, rewritten with a real-coordinate integrand. -/
private lemma poissonCauchyIntegral_ofReal_eq {f : ℝ → ℝ} (x y : ℝ) :
    poissonCauchyIntegral (fun t => (f t : ℂ)) (x + y * I) =
      ∫ t : ℝ, I / Real.pi * ((f t : ℂ) / ((x - t : ℝ) + I * y)) := by
  unfold poissonCauchyIntegral
  rw [integral_const_mul]
  simp

/-- DLMF §1.15(v), after 1.15.39: for real absolutely integrable `f` and `y > 0`, the real part
of `Φ(x + iy)` is the Poisson integral `h(x, y) = (1/2π) ∫ f(t) P(x - t, y) dt`. -/
@[dlmf 1.15.v]
theorem re_poissonCauchyIntegral {f : ℝ → ℝ} (hf : Integrable f) (x : ℝ) {y : ℝ} (hy : 0 < y) :
    (poissonCauchyIntegral (fun t => (f t : ℂ)) (x + y * I)).re =
      (2 * Real.pi)⁻¹ * ∫ t, f t * halfPlanePoissonKernel (x - t) y := by
  have hI := (integrable_poissonCauchy_integrand hf x y hy).const_mul (I / Real.pi)
  rw [poissonCauchyIntegral_ofReal_eq, ← RCLike.re_to_complex, ← integral_re hI,
      ← integral_const_mul]
  congr 1
  funext t
  rw [RCLike.re_to_complex, poissonCauchy_integrand_split _ _ _ hy]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im]
  unfold halfPlanePoissonKernel
  have hD : 0 < (x - t) ^ 2 + y ^ 2 := by positivity
  have hpi := Real.pi_pos
  field_simp
  ring

/-- DLMF 1.15.40: for real absolutely integrable `f` and `y > 0`,
`ℑΦ(x + iy) = (1/π) ∫ f(t) (x - t)/((x - t)² + y²) dt`, the conjugate Poisson integral. -/
@[dlmf 1.15.E40]
theorem im_poissonCauchyIntegral {f : ℝ → ℝ} (hf : Integrable f) (x : ℝ) {y : ℝ} (hy : 0 < y) :
    (poissonCauchyIntegral (fun t => (f t : ℂ)) (x + y * I)).im =
      Real.pi⁻¹ * ∫ t, f t * ((x - t) / ((x - t) ^ 2 + y ^ 2)) := by
  have hI := (integrable_poissonCauchy_integrand hf x y hy).const_mul (I / Real.pi)
  rw [poissonCauchyIntegral_ofReal_eq, ← RCLike.im_to_complex, ← integral_im hI,
      ← integral_const_mul]
  congr 1
  funext t
  rw [RCLike.im_to_complex, poissonCauchy_integrand_split _ _ _ hy]
  simp only [Complex.add_im, Complex.ofReal_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_im]
  have hD : 0 < (x - t) ^ 2 + y ^ 2 := by positivity
  have hpi := Real.pi_pos
  field_simp
  ring

/-- DLMF §1.15(v), after 1.15.39: for real absolutely integrable `f`, `Φ` (1.15.39) is analytic in
the upper half-plane. -/
@[dlmf 1.15.v]
theorem differentiableOn_poissonCauchyIntegral {f : ℝ → ℝ} (hf : Integrable f) :
    DifferentiableOn ℂ (poissonCauchyIntegral fun t => (f t : ℂ)) {z : ℂ | 0 < z.im} := by
  have hne (z : ℂ) (hz : 0 < z.im) (t : ℝ) : z - t ≠ 0 := by
    intro he
    have hi := congrArg Complex.im he
    simp at hi
    exact hz.ne' hi
  have hI : DifferentiableOn ℂ (fun z : ℂ => ∫ t : ℝ, (f t : ℂ) / (z - t))
      {z : ℂ | 0 < z.im} := by
    apply Complex.differentiableOn_integral_of_locally_dominated
      (isOpen_lt continuous_const Complex.continuous_im)
    · intro z hz
      simp_rw [div_eq_mul_inv]
      exact (Complex.continuous_ofReal.comp_aestronglyMeasurable hf.aestronglyMeasurable).mul
        ((by fun_prop : Continuous (fun t : ℝ => z - (t : ℂ))).inv₀ (hne z hz)).aestronglyMeasurable
    · filter_upwards [] with t z hz
      exact (differentiableAt_const (f t : ℂ)).div
        (differentiableAt_id.sub_const (t : ℂ)) (hne z hz t) |>.differentiableWithinAt
    · intro z hz
      refine ⟨{w : ℂ | z.im / 2 < w.im},
        (isOpen_lt continuous_const Complex.continuous_im).mem_nhds
            (by simpa using half_lt_self hz),
        fun t => (z.im / 2)⁻¹ * ‖f t‖, hf.norm.const_mul _, ?_⟩
      filter_upwards [] with t w hw
      have hw0 : 0 < w.im := lt_trans (half_pos hz) hw
      have hn : z.im / 2 ≤ ‖w - (t : ℂ)‖ := by
        have hb := Complex.abs_im_le_norm (w - (t : ℂ))
        simp only [Complex.sub_im, Complex.ofReal_im, sub_zero, abs_of_pos hw0] at hb
        exact hw.le.trans hb
      rw [norm_div, Complex.norm_real, div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_right
        ((inv_le_inv₀ (norm_pos_iff.mpr (hne w hw0 t)) (half_pos hz)).mpr hn)
        (norm_nonneg _)
  have heq : poissonCauchyIntegral (fun t => (f t : ℂ)) =
      fun z => (I / Real.pi) * ∫ t : ℝ, (f t : ℂ) / (z - t) := by
    funext z
    unfold poissonCauchyIntegral
    congr 1
    apply integral_congr_ae
    filter_upwards [] with t
    congr 1
    push_cast
    linear_combination Complex.re_add_im z
  rw [heq]
  exact hI.const_mul _

/-- DLMF §1.15(v), after 1.15.40, **corrected sign**: for real absolutely integrable `f`, for
almost every `x`, `ℑΦ(x + iy) → -ℋ(f)(x)` as `y → 0+`, with DLMF's Hilbert transform 1.14.41.
DLMF says the limit "is the Hilbert transform"; the sign is opposite (module docstring). -/
@[dlmf 1.15.v]
theorem tendsto_im_poissonCauchyIntegral {f : ℝ → ℝ} (hf : Integrable f) :
    ∀ᵐ x : ℝ, Tendsto (fun y : ℝ => (poissonCauchyIntegral (fun t => (f t : ℂ)) (x + y * I)).im)
      (𝓝[>] 0) (𝓝 (-(hilbertTransform (fun t => (f t : ℂ)) x).re)) := by
  sorry

/-! ### Fejér kernel of Fourier integrals (§1.15(v)) -/

/-- `K_R(s) = (R/π) (1 - cos(Rs))/(Rs)²`. -/
private theorem fejerKernelLine_eq {R : ℝ} (s : ℝ) :
    fejerKernelLine R s = R / Real.pi * ((1 - Real.cos (R * s)) / (R * s) ^ 2) := by
  unfold fejerKernelLine
  rcases eq_or_ne R 0 with rfl | hR
  · simp
  rcases eq_or_ne s 0 with rfl | hs
  · simp
  field_simp

/-- `K_R ≥ 0` for `R ≥ 0`. -/
private theorem fejerKernelLine_nonneg {R : ℝ} (hR : 0 ≤ R) (s : ℝ) : 0 ≤ fejerKernelLine R s := by
  unfold fejerKernelLine
  exact mul_nonneg (by positivity) (div_nonneg (by linarith [Real.cos_le_one (R * s)])
    (sq_nonneg s))

/-- `K_R(s) ≤ 2/(πRs²)`. -/
private theorem fejerKernelLine_le {R s : ℝ} (hR : 0 < R) (hs : s ≠ 0) :
    fejerKernelLine R s ≤ 2 / (Real.pi * R * s ^ 2) := by
  unfold fejerKernelLine
  rw [div_mul_div_comm, one_mul]
  exact div_le_div_of_nonneg_right (by linarith [Real.neg_one_le_cos (R * s)]) (by positivity)

/-- DLMF 1.15.42: `∫ K_R(s) ds = 1` for `R > 0`. -/
@[dlmf 1.15.E42]
theorem integral_fejerKernelLine {R : ℝ} (hR : 0 < R) : ∫ s, fejerKernelLine R s = 1 := by
  simp_rw [fejerKernelLine_eq]
  rw [integral_const_mul, Measure.integral_comp_mul_left (fun u => (1 - Real.cos u) / u ^ 2) R,
    Real.integral_one_sub_cos_div_sq, smul_eq_mul, abs_inv, abs_of_pos hR]
  field_simp

/-- DLMF 1.15.43: `∫_{|s| ≥ δ} K_R(s) ds → 0` as `R → ∞`, for `δ > 0`. -/
@[dlmf 1.15.E43]
theorem tendsto_integral_fejerKernelLine_tail {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun R => ∫ s in {s : ℝ | δ ≤ |s|}, fejerKernelLine R s) atTop (𝓝 0) := by
  set S : Set ℝ := {s : ℝ | δ ≤ |s|} with hSdef
  have hS : MeasurableSet S := measurableSet_le measurable_const continuous_abs.measurable
  simp_rw [← integral_indicator hS]
  set D : ℝ → ℝ := fun s => 2 * (1 + δ⁻¹ ^ 2) / Real.pi * (1 + s ^ 2)⁻¹ with hDdef
  have hD : Integrable D := integrable_inv_one_add_sq.const_mul _
  have hS0 : ∀ s ∈ S, s ≠ 0 := fun s hs h => by
    have hs' : δ ≤ |s| := hs
    rw [h, abs_zero] at hs'; linarith
  have hmeas : ∀ R, Measurable (fejerKernelLine R) := fun R => by
    unfold fejerKernelLine; fun_prop
  suffices h : Tendsto (fun R => ∫ s, S.indicator (fejerKernelLine R) s) atTop
      (𝓝 (∫ _ : ℝ, (0 : ℝ))) by simpa using h
  refine tendsto_integral_filter_of_dominated_convergence D ?_ ?_ hD ?_
  · exact Eventually.of_forall fun R => ((hmeas R).indicator hS).aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop 1] with R hR
    refine Eventually.of_forall fun s => ?_
    by_cases hs : s ∈ S
    · rw [indicator_of_mem hs, Real.norm_of_nonneg (fejerKernelLine_nonneg (by linarith) s)]
      have hs' : δ ≤ |s| := hs
      have hs0 := hS0 s hs
      have hsq : δ ^ 2 ≤ s ^ 2 := by rw [← sq_abs s]; gcongr
      have hs2 : 0 < s ^ 2 := by positivity
      refine (fejerKernelLine_le (by linarith) hs0).trans ?_
      have h2 : 2 / (Real.pi * R * s ^ 2) ≤ 2 / (Real.pi * s ^ 2) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity)
          (by nlinarith [mul_pos Real.pi_pos hs2])
      refine h2.trans (le_of_eq_of_le (by ring : 2 / (Real.pi * s ^ 2) =
        2 / Real.pi * (s ^ 2)⁻¹) ?_)
      simp only [hDdef, mul_div_right_comm 2 (1 + δ⁻¹ ^ 2), mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
      calc (s ^ 2)⁻¹ * (1 + s ^ 2) = (s ^ 2)⁻¹ + 1 := by field_simp
        _ ≤ (δ ^ 2)⁻¹ + 1 := by gcongr
        _ = 1 + (δ ^ 2)⁻¹ := by ring
    · rw [indicator_of_notMem hs, norm_zero]; positivity
  · refine Eventually.of_forall fun s => ?_
    by_cases hs : s ∈ S
    · simp only [indicator_of_mem hs]
      have hs0 := hS0 s hs
      have hlim : Tendsto (fun R : ℝ => 2 / (Real.pi * R * s ^ 2)) atTop (𝓝 0) := by
        refine tendsto_const_nhds.div_atTop ?_
        exact (tendsto_id.const_mul_atTop Real.pi_pos).atTop_mul_const (by positivity)
      refine squeeze_zero' ?_ ?_ hlim
      · filter_upwards [eventually_ge_atTop 0] with R hR using fejerKernelLine_nonneg hR s
      · filter_upwards [eventually_gt_atTop 0] with R hR using fejerKernelLine_le hR hs0
    · simp only [indicator_of_notMem hs]; exact tendsto_const_nhds

/-- The real antiderivative used for the Fejér integral. -/
private lemma integral_triangle_cos {R u : ℝ} (hR : 0 < R) (hu : u ≠ 0) :
    ∫ t in (0 : ℝ)..R, 2 * (1 - t / R) * Real.cos (u * t) =
      2 * (1 - Real.cos (R * u)) / (R * u ^ 2) := by
  have hd : ∀ t ∈ uIcc (0 : ℝ) R, HasDerivAt
      (fun t => 2 * (1 - t / R) * Real.sin (u * t) / u - 2 * Real.cos (u * t) / (R * u ^ 2))
      (2 * (1 - t / R) * Real.cos (u * t)) t := by
    intro t _
    have h1 := ((((hasDerivAt_id' t).div_const R).const_sub 1).const_mul 2).mul
      (((hasDerivAt_id' t).const_mul u).sin) |>.div_const u
    have h2 := ((((hasDerivAt_id' t).const_mul u).cos).const_mul 2).div_const (R * u ^ 2)
    refine (h1.sub h2).congr_deriv ?_
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (by
    apply Continuous.intervalIntegrable; fun_prop)]
  simp only [div_self hR.ne', sub_self, mul_zero, zero_mul, zero_div, Real.cos_zero,
    sub_zero, mul_one, Real.sin_zero]
  rw [mul_comm u R]
  field_simp
  ring

/-- `∫_{-R}^{R} (1 - |t|/R) e^{itu} dt = 2(1 - cos Ru)/(Ru²)` for `u ≠ 0`. -/
private lemma integral_triangle_cexp {R u : ℝ} (hR : 0 < R) (hu : u ≠ 0) :
    ∫ t in -R..R, ((1 - |t| / R : ℝ) : ℂ) * cexp (I * t * u) =
      ((2 * (1 - Real.cos (R * u)) / (R * u ^ 2) : ℝ) : ℂ) := by
  have hc : Continuous fun t : ℝ => ((1 - |t| / R : ℝ) : ℂ) * cexp (I * t * u) := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := R)
    (fun t : ℝ => ((1 - |t| / R : ℝ) : ℂ) * cexp (I * t * u))
  simp only [neg_zero, abs_neg, ofReal_neg, mul_neg, neg_mul] at h
  rw [← h, ← intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
    (hc.intervalIntegrable _ _), ← integral_triangle_cos hR hu, ← intervalIntegral.integral_ofReal]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le hR.le] at ht
  simp only [abs_of_nonneg ht.1]
  rw [← mul_add, show I * t * u = (u * t : ℝ) * I by push_cast; ring,
    show -((u * t : ℝ) * I) = -(u * t : ℝ) * I by ring, add_comm, ← Complex.two_cos]
  push_cast
  ring

/-- DLMF 1.15.45: for `f` absolutely integrable and `R > 0`, the Cesàro mean 1.15.44 of the
Fourier integral is `σ_R(θ) = ∫ f(t) K_R(θ - t) dt`. -/
@[dlmf 1.15.E45]
theorem fourierCesaroMeanIntegral_eq {f : ℝ → ℂ} (hf : Integrable f) {R : ℝ} (hR : 0 < R)
    (θ : ℝ) :
    fourierCesaroMeanIntegral f R θ = ∫ t, f t * (fejerKernelLine R (θ - t) : ℂ) := by
  set μ : Measure ℝ := volume.restrict (Ioc (-R) R) with hμ
  have he : Integrable (fun t : ℝ => ((1 - |t| / R : ℝ) : ℂ)) μ :=
    ((by fun_prop : Continuous fun t : ℝ => ((1 - |t| / R : ℝ) : ℂ)).integrableOn_Icc
      (a := -R) (b := R)).mono_set Ioc_subset_Icc_self
  set F : ℝ → ℝ → ℂ := fun t s =>
    cexp (-(I * θ * t)) * cexp (I * t * s) * (((1 - |t| / R : ℝ) : ℂ) * f s) with hF
  have hFi : Integrable (Function.uncurry F) (μ.prod volume) := by
    have hp := he.mul_prod hf
    refine (hp.bdd_mul (c := 1) (f := fun p : ℝ × ℝ =>
        cexp (-(I * θ * p.1)) * cexp (I * p.1 * p.2)) ?_ ?_).congr
        (Eventually.of_forall fun p => ?_)
    · exact (by fun_prop : Continuous fun p : ℝ × ℝ =>
        cexp (-(I * θ * p.1)) * cexp (I * p.1 * p.2)).aestronglyMeasurable
    · refine Eventually.of_forall fun p => ?_
      rw [norm_mul, Complex.norm_exp, Complex.norm_exp]
      simp
    · simp [hF, Function.uncurry]
  have hsq : ((Real.sqrt (2 * Real.pi))⁻¹ : ℂ) * ((Real.sqrt (2 * Real.pi))⁻¹ : ℂ) =
      ((2 * Real.pi : ℝ)⁻¹ : ℂ) := by
    rw [← mul_inv, ← ofReal_mul, Real.mul_self_sqrt (by positivity)]
  unfold fourierCesaroMeanIntegral fourierTransform
  rw [intervalIntegral.integral_of_le (by linarith)]
  have hin : ∀ t : ℝ, ((1 - |t| / R : ℝ) : ℂ) * cexp (-(I * θ * t)) *
      (((Real.sqrt (2 * Real.pi))⁻¹ : ℂ) * ∫ s : ℝ, f s * cexp (I * t * s)) =
      ((Real.sqrt (2 * Real.pi))⁻¹ : ℂ) * ∫ s, F t s := by
    intro t
    conv_lhs => rw [← integral_const_mul, ← integral_const_mul]
    conv_rhs => rw [← integral_const_mul]
    congr 1; funext s
    simp only [hF]
    ring
  simp_rw [hin]
  rw [integral_const_mul, ← mul_assoc, hsq, integral_integral_swap hFi, ← integral_const_mul]
  refine integral_congr_ae ?_
  have hθ : ∀ᵐ s : ℝ, s ∉ ({θ} : Set ℝ) :=
    measure_eq_zero_iff_ae_notMem.1 (measure_singleton θ)
  filter_upwards [hθ] with s hs
  simp only [hF]
  have hu : s - θ ≠ 0 := sub_ne_zero.mpr fun h => hs (mem_singleton_iff.mpr h)
  have h := integral_triangle_cexp hR hu
  rw [intervalIntegral.integral_of_le (by linarith)] at h
  calc ((2 * Real.pi : ℝ)⁻¹ : ℂ) * ∫ t in Ioc (-R) R,
        cexp (-(I * θ * t)) * cexp (I * t * s) * (((1 - |t| / R : ℝ) : ℂ) * f s)
      = ((2 * Real.pi : ℝ)⁻¹ : ℂ) * ((∫ t in Ioc (-R) R,
          ((1 - |t| / R : ℝ) : ℂ) * cexp (I * t * (s - θ : ℝ))) * f s) := by
        rw [← integral_mul_const]
        congr 2; funext t
        rw [show I * t * (s - θ : ℝ) = -(I * θ * t) + I * t * s by push_cast; ring,
          Complex.exp_add]
        ring
    _ = f s * (fejerKernelLine R (θ - s) : ℂ) := by
        rw [h, fejerKernelLine]
        have hu2 : (θ - s) ^ 2 = (s - θ) ^ 2 := by ring
        have hcos : Real.cos (R * (θ - s)) = Real.cos (R * (s - θ)) := by
          rw [← Real.cos_neg]; ring_nf
        rw [hu2, hcos]
        have hpi := Real.pi_pos
        push_cast
        field_simp

/-- The Fejér density `(1 - cos u)/(πu²)`. -/
private lemma fejerKernelLine_scaled {R : ℝ} (hR : 0 < R) (u : ℝ) :
    R⁻¹ * fejerKernelLine R (R⁻¹ * u) = Real.pi⁻¹ * ((1 - Real.cos u) / u ^ 2) := by
  unfold fejerKernelLine
  have := Real.pi_pos
  rw [mul_inv_cancel_left₀ hR.ne']
  field_simp

/-- DLMF 1.15.46: for `f` absolutely integrable, `∫ |σ_R(θ) - f(θ)| dθ → 0` as `R → ∞`. -/
@[dlmf 1.15.E46]
theorem tendsto_integral_norm_fourierCesaroMeanIntegral_sub {f : ℝ → ℂ} (hf : Integrable f) :
    Tendsto (fun R => ∫ θ, ‖fourierCesaroMeanIntegral f R θ - f θ‖) atTop (𝓝 0) := by
  have hk : Integrable fun u : ℝ => Real.pi⁻¹ * ((1 - Real.cos u) / u ^ 2) :=
    Real.integrable_one_sub_cos_div_sq.const_mul _
  have hk1 : ∫ u : ℝ, Real.pi⁻¹ * ((1 - Real.cos u) / u ^ 2) = 1 := by
    rw [integral_const_mul, Real.integral_one_sub_cos_div_sq]
    exact inv_mul_cancel₀ Real.pi_ne_zero
  have h := (hf.tendsto_integral_norm_integral_smul_comp_sub_mul_sub hk
    (fun u => mul_nonneg (inv_nonneg.mpr Real.pi_pos.le) (Real.one_sub_cos_div_sq_nonneg u))
    hk1).comp tendsto_inv_atTop_zero
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with R hR
  refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
  dsimp only
  rw [fourierCesaroMeanIntegral_eq hf hR,
    integral_mul_kernel_eq_scaled (fejerKernelLine R) θ (inv_pos.mpr hR)]
  simp_rw [fejerKernelLine_scaled hR]

end DLMF.AlgebraicAnalytic
