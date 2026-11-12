/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.IntegralRepresentations.EulerAndBessel
public import DLMFMathlib.Analysis.Asymptotics.WatsonGaussian
public import DLMFMathlib.Analysis.Calculus.DoubleZeroSqrt
public import DLMFMathlib.Analysis.SpecialFunctions.Gamma.BetaHalfLine

/-!
# Quadratic saddle estimates for the diagonal Tricomi integral

The phase `t-log(1+t)` has a double zero at the origin. Its signed square-root coordinate
has an analytic local inverse. The transformed amplitude has value one and derivative
`-2(a+1)/3`, giving the two terms in DLMF 13.8.7 for `Re a > 0`. The remaining integral
has an exponentially small tail.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics
open scoped Real Topology

namespace DLMF.Confluent.KummerTransition

/-- The Laplace phase `t - log(1+t)` of the diagonal Tricomi integral. -/
def phase (t : ℝ) : ℝ := t - Real.log (1+t)
/-- The analytic factor of the double zero of the Tricomi phase. -/
def quadraticFactor (t : ℝ) : ℝ := ∫ τ : ℝ in 0..1, τ/(1+t*τ)
/-- The signed quadratic saddle coordinate at zero. -/
def coordinate (t : ℝ) : ℝ := DoubleZeroSqrt.signedSqrt quadraticFactor 0 t

/-- The quadratic phase factor is analytic at zero. -/
lemma analyticAt_quadraticFactor : AnalyticAt ℝ quadraticFactor 0 := by
  have h : AnalyticAt ℝ (fun t : ℝ => (1+t)⁻¹) 0 :=
    (analyticAt_const.add analyticAt_id).inv (by norm_num)
  have hi : IntervalIntegrable (fun τ : ℝ => τ) volume 0 1 := continuous_id.intervalIntegrable _ _
  simpa only [quadraticFactor,smul_eq_mul,div_eq_mul_inv] using! h.dblZero_integral_smul_comp_mul hi

/-- The quadratic phase factor at zero is one half. -/
lemma quadraticFactor_zero : quadraticFactor 0 = 1/2 := by
  norm_num [quadraticFactor,integral_id]

/-- The first derivative of the quadratic phase factor at zero. -/
lemma hasDerivAt_quadraticFactor_zero : HasDerivAt quadraticFactor (-1/3) 0 := by
  have hden {u τ : ℝ} (hu : u ∈ Metric.ball (0:ℝ) (1/2)) (hτ : τ ∈ Ioc (0:ℝ) 1) :
      1/2 < 1+u*τ := by
    have hu' : |u| < 1/2 := by simpa [Metric.mem_ball,Real.dist_eq] using hu
    have hp := mul_pos (by linarith [abs_lt.mp hu'] : 0 < u+1/2) hτ.1
    nlinarith [hτ.2]
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioc (0:ℝ) 1))
    (F := fun u τ : ℝ => τ/(1+u*τ))
    (F' := fun u τ : ℝ => -τ^2/(1+u*τ)^2)
    (bound := fun _ : ℝ => (4:ℝ))
    (Metric.ball_mem_nhds (0:ℝ) (by norm_num : (0:ℝ)<1/2))
    (Eventually.of_forall fun _ => Measurable.aestronglyMeasurable (by fun_prop))
    (by simpa only [zero_mul,add_zero,div_one,_root_.id] using!
      (continuous_id.integrableOn_Icc.mono_set Ioc_subset_Icc_self :
        IntegrableOn (fun τ : ℝ => τ) (Ioc 0 1)))
    (Measurable.aestronglyMeasurable (by fun_prop)) ?_
    (continuous_const.integrableOn_Icc.mono_set Ioc_subset_Icc_self) ?_
  · have he : (∫ τ : ℝ in Ioc (0:ℝ) 1, -τ^2/(1+0*τ)^2) = -1/3 := by
      simp only [zero_mul,add_zero,one_pow,div_one]
      rw [←intervalIntegral.integral_of_le zero_le_one,intervalIntegral.integral_neg]
      norm_num [integral_pow]
    rw [he] at h
    convert h.2 using 1
    funext u
    exact intervalIntegral.integral_of_le zero_le_one
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with τ hτ u hu
    have hd := hden hu hτ
    rw [Real.norm_eq_abs,abs_div,abs_neg,abs_pow,abs_of_pos hτ.1,
      abs_pow,abs_of_pos (by linarith : 0 < 1+u*τ)]
    rw [div_le_iff₀ (sq_pos_of_pos (by linarith : 0 < 1+u*τ))]
    have hsq : τ^2 ≤ 1 := by nlinarith [hτ.1,hτ.2]
    nlinarith [sq_nonneg (1+u*τ-1/2)]
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with τ hτ u hu
    have hn : 1+u*τ ≠ 0 := ne_of_gt (lt_trans (by norm_num : (0:ℝ)<1/2) (hden hu hτ))
    have hd := (hasDerivAt_const u τ).div (((hasDerivAt_id u).mul_const τ).const_add 1) hn
    exact hd.congr_deriv (by dsimp only [_root_.id]; ring)

/-- The signed saddle coordinate is analytic at zero. -/
lemma analyticAt_coordinate : AnalyticAt ℝ coordinate 0 :=
  DoubleZeroSqrt.analyticAt_signedSqrt analyticAt_quadraticFactor
    (by rw [quadraticFactor_zero]; norm_num)

/-- The signed saddle coordinate has unit derivative at zero. -/
lemma hasDerivAt_coordinate_zero : HasDerivAt coordinate 1 0 := by
  simpa only [coordinate,quadraticFactor_zero,show 2*(1/2:ℝ)=1 by ring,Real.sqrt_one] using!
    DoubleZeroSqrt.hasDerivAt_signedSqrt analyticAt_quadraticFactor
      (by rw [quadraticFactor_zero]; norm_num)

/-- The positive Tricomi phase factors through its quadratic zero. -/
lemma phase_eq_sq_mul {t : ℝ} (ht : 0 < t) : phase t = t^2*quadraticFactor t := by
  have hs := DoubleZeroSqrt.integral_rpow_mul_right (fun u : ℝ => (1+u)⁻¹) 1 ht
  norm_num only [sub_zero,zero_add,Real.rpow_one,show (1+1:ℝ)=2 by ring,Real.rpow_two] at hs
  have hp : (∫ u : ℝ in 0..t, u*(1+u)⁻¹) = phase t := by
    have hd (u : ℝ) (hu : u ∈ uIcc 0 t) : HasDerivAt phase (u*(1+u)⁻¹) u := by
      have hu0 : 0 ≤ u := (uIcc_of_le ht.le ▸ hu).1
      have hn : 1+u ≠ 0 := by positivity
      have hlog : HasDerivAt (fun u : ℝ => Real.log (1+u)) ((1+u)⁻¹) u := by
        simpa using ((hasDerivAt_id u).const_add 1).log hn
      exact ((hasDerivAt_id u).sub hlog).congr_deriv (by field_simp;ring)
    have hc : ContinuousOn (fun u : ℝ => u*(1+u)⁻¹) (uIcc 0 t) := by
      apply continuousOn_id.mul
      apply ContinuousOn.inv₀
      · fun_prop
      · intro u hu
        have hu0 : 0 ≤ u := (uIcc_of_le ht.le ▸ hu).1
        positivity
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable
    simpa [phase] using he
  rw [←hp,hs]
  congr 1

/-- The saddle coordinate has an analytic local inverse with unit derivative. -/
lemma exists_inverse : ∃ T : ℝ → ℝ, AnalyticAt ℝ T 0 ∧ HasDerivAt T 1 0 ∧ T 0=0 ∧
    (∀ᶠ t in 𝓝 (0:ℝ), T (coordinate t)=t) ∧
    (∀ᶠ s in 𝓝 (0:ℝ), coordinate (T s)=s) := by
  have hc0 : coordinate 0=0 := by simp [coordinate,DoubleZeroSqrt.signedSqrt]
  simpa only [hc0,inv_one] using DoubleZeroSqrt.exists_analytic_inverse
    analyticAt_coordinate hasDerivAt_coordinate_zero one_ne_zero

/-- The divided slope of the saddle inverse has derivative one third. -/
lemma inverse_dslope_derivative {T : ℝ → ℝ} (hT : AnalyticAt ℝ T 0)
    (hdT : HasDerivAt T 1 0) (hT0 : T 0=0)
    (hr : ∀ᶠ s in 𝓝 (0:ℝ), coordinate (T s)=s) :
    HasDerivAt (dslope T 0) (1/3) 0 := by
  let P : ℝ → ℝ := dslope T 0
  have hPa : AnalyticAt ℝ P 0 := hT.dslope 0
  have hP0 : P 0=1 := by simp only [P,dslope_same,hdT.deriv]
  have hprod (s : ℝ) : T s=s*P s := by
    have h := sub_smul_dslope_of_zero hT0 s
    simpa only [sub_zero,smul_eq_mul] using h.symm
  have he : (fun s => P s^2*quadraticFactor (T s)) =ᶠ[𝓝 (0:ℝ)] fun _ => 1/2 := by
    have hQ : ∀ᶠ s in 𝓝 (0:ℝ), 0 < quadraticFactor (T s) := by
      have hh := (analyticAt_quadraticFactor.continuousAt.eventually
        (lt_mem_nhds (show 0 < quadraticFactor 0 by rw [quadraticFactor_zero];norm_num)))
      have ht : Tendsto T (𝓝 (0:ℝ)) (𝓝 (0:ℝ)) := by
        simpa only [hT0] using hdT.continuousAt.tendsto
      exact ht.eventually hh
    filter_upwards [hr,hQ] with s hs hQs
    by_cases hs0 : s=0
    · simp [hs0,hP0,hT0,quadraticFactor_zero]
    · have hs' : T s*Real.sqrt (2*quadraticFactor (T s))=s := by
        simpa only [coordinate,DoubleZeroSqrt.signedSqrt,sub_zero] using hs
      have hh := congrArg (fun x : ℝ => x^2) hs'
      rw [mul_pow,Real.sq_sqrt (by positivity)] at hh
      nth_rw 1 [hprod] at hh
      have hs2 : s^2 ≠ 0 := pow_ne_zero 2 hs0
      apply (mul_left_cancel₀ hs2)
      nlinarith [hh]
  have hD := (hPa.differentiableAt.hasDerivAt.fun_pow 2).mul
    (hasDerivAt_quadraticFactor_zero.comp_of_eq 0 hdT hT0.symm)
  have hzero := hD.congr_of_eventuallyEq he.symm
  have hval := hzero.unique (hasDerivAt_const (0:ℝ) (1/2:ℝ))
  norm_num only [hP0,Function.comp_def,hT0,quadraticFactor_zero,Nat.cast_ofNat,
    Nat.reduceSub,pow_one,one_pow,one_mul,mul_one] at hval
  exact hPa.differentiableAt.hasDerivAt.congr_deriv (by linarith)

/-- The second derivative of the saddle inverse at zero is two thirds. -/
lemma inverse_second_derivative {T : ℝ → ℝ} (hT : AnalyticAt ℝ T 0)
    (hdT : HasDerivAt T 1 0) (hT0 : T 0=0)
    (hr : ∀ᶠ s in 𝓝 (0:ℝ), coordinate (T s)=s) :
    HasDerivAt (deriv T) (2/3) 0 := by
  let P : ℝ → ℝ := dslope T 0
  have hPa : AnalyticAt ℝ P 0 := hT.dslope 0
  have hPd : HasDerivAt P (1/3) 0 := inverse_dslope_derivative hT hdT hT0 hr
  have hprod (s : ℝ) : T s=s*P s := by
    have h := sub_smul_dslope_of_zero hT0 s
    simpa only [sub_zero,smul_eq_mul] using h.symm
  have hfun : deriv T =ᶠ[𝓝 (0:ℝ)] fun s => P s+s*deriv P s := by
    filter_upwards [hPa.eventually_analyticAt] with s hs
    have h := (hasDerivAt_id s).mul hs.differentiableAt.hasDerivAt
    have hh := h.congr_of_eventuallyEq (Eventually.of_forall hprod)
    simpa only [_root_.id,one_mul] using hh.deriv
  have h := hPd.add ((hasDerivAt_id (0:ℝ)).mul hPa.deriv.differentiableAt.hasDerivAt)
  have hh := h.congr_of_eventuallyEq hfun
  exact hh.congr_deriv (by simp only [_root_.id,zero_mul,add_zero,one_mul,hPd.deriv];ring)

/-- The transformed Tricomi amplitude after the quadratic saddle substitution. -/
def amplitude (T : ℝ → ℝ) (a : ℂ) (s : ℝ) : ℂ :=
  ((dslope T 0 s : ℝ) : ℂ)^(a-1)*((1+T s:ℝ):ℂ)^(-a-1)*((deriv T s:ℝ):ℂ)

/-- The transformed amplitude is analytic with its first two explicit coefficients. -/
lemma amplitude_data {T : ℝ → ℝ} (hT : AnalyticAt ℝ T 0)
    (hdT : HasDerivAt T 1 0) (hT0 : T 0=0)
    (hr : ∀ᶠ s in 𝓝 (0:ℝ), coordinate (T s)=s) (a : ℂ) :
    AnalyticAt ℝ (amplitude T a) 0 ∧ amplitude T a 0=1 ∧
      HasDerivAt (amplitude T a) (-2*(a+1)/3) 0 := by
  have hPa : AnalyticAt ℝ (dslope T 0) 0 := hT.dslope 0
  have hP0 : dslope T 0 0=1 := by simp only [dslope_same,hdT.deriv]
  have hPd := inverse_dslope_derivative hT hdT hT0 hr
  have hD2 := inverse_second_derivative hT hdT hT0 hr
  have hD0 : deriv T 0=1 := hdT.deriv
  have hAa : AnalyticAt ℝ (fun s => ((dslope T 0 s:ℝ):ℂ)^(a-1)) 0 :=
    hPa.ofReal_cpow (by rw [hP0];norm_num) (a-1)
  have hBa : AnalyticAt ℝ (fun s => ((1+T s:ℝ):ℂ)^(-a-1)) 0 :=
    (analyticAt_const.add hT).ofReal_cpow
      (by simp only [Pi.add_apply,hT0,add_zero];norm_num) (-a-1)
  have hCa : AnalyticAt ℝ (fun s => ((deriv T s:ℝ):ℂ)) 0 :=
    (Complex.ofRealCLM.analyticAt (deriv T 0)).comp hT.deriv
  have hA : HasDerivAt (fun s => ((dslope T 0 s:ℝ):ℂ)^(a-1)) ((a-1)/3) 0 := by
    have hg := (Complex.hasStrictDerivAt_cpow_const (x := (1:ℂ)) (c := a-1)
      one_mem_slitPlane).hasDerivAt
    have hh := hg.comp_of_eq 0 hPd.ofReal_comp (by rw [hP0];rfl)
    simpa using! hh
  have hB : HasDerivAt (fun s => ((1+T s:ℝ):ℂ)^(-a-1)) (-a-1) 0 := by
    have hg := (Complex.hasStrictDerivAt_cpow_const (x := (1:ℂ)) (c := -a-1)
      one_mem_slitPlane).hasDerivAt
    have hh := hg.comp_of_eq 0 (hdT.const_add 1).ofReal_comp (by rw [hT0];norm_num)
    simpa using! hh
  have h := (hA.mul hB).mul hD2.ofReal_comp
  refine ⟨hAa.mul hBa |>.mul hCa,?_,?_⟩
  · simp [amplitude,hP0,hT0,hD0]
  · apply h.congr_deriv
    simp only [Pi.mul_apply,hP0,hT0,hD0,add_zero,ofReal_one,one_cpow,mul_one,one_mul]
    push_cast
    ring

/-- The local Tricomi integral becomes a Gaussian integral in saddle coordinates. -/
lemma integral_substitution {T : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hT0 : T 0=0) (hD : ∀ s ∈ Icc (0:ℝ) δ, HasDerivAt T (deriv T s) s)
    (hDpos : ∀ s ∈ Icc (0:ℝ) δ, 0 < deriv T s)
    (hmono : StrictMonoOn T (Icc (0:ℝ) δ))
    (hP : ∀ s ∈ Icc (0:ℝ) δ, 0 < dslope T 0 s)
    (hQ : ∀ s ∈ Icc (0:ℝ) δ, 0 < quadraticFactor (T s))
    (hr : ∀ s ∈ Icc (0:ℝ) δ, coordinate (T s)=s) (a : ℂ) (b : ℝ) :
    (∫ t in Ioc (0:ℝ) (T δ), (Real.exp (-b*phase t):ℂ)*
      (t:ℂ)^(a-1)*((1+t:ℝ):ℂ)^(-a-1)) =
    ∫ s in Ioc (0:ℝ) δ, (Real.exp (-b*s^2/2):ℂ)*(s:ℂ)^(a-1)*amplitude T a s := by
  have hc : ContinuousOn T (Icc (0:ℝ) δ) := fun s hs => (hD s hs).continuousAt.continuousWithinAt
  have himage := hc.image_Ioc_of_strictMonoOn hδ.le hmono
  rw [hT0] at himage
  rw [←himage, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioc
    (fun s hs => (hD s (Ioc_subset_Icc_self hs)).hasDerivWithinAt)
    (hmono.injOn.mono Ioc_subset_Icc_self)]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro s hs
  dsimp only
  have hs' := Ioc_subset_Icc_self hs
  have hTs : 0 < T s := by
    have h := hmono (show (0:ℝ) ∈ Icc (0:ℝ) δ from ⟨le_rfl,hδ.le⟩) hs' hs.1
    simpa only [hT0] using h
  have hPs := hP s hs'
  have hprod : T s=s*dslope T 0 s := by
    simpa only [sub_zero,smul_eq_mul] using (sub_smul_dslope_of_zero hT0 s).symm
  have hphase : phase (T s)=s^2/2 := by
    have he := congrArg (fun x : ℝ => x^2) (hr s hs')
    simp only [coordinate,DoubleZeroSqrt.signedSqrt,sub_zero,mul_pow,
      Real.sq_sqrt (show 0 ≤ 2*quadraticFactor (T s) by linarith [hQ s hs'])] at he
    rw [phase_eq_sq_mul hTs]
    nlinarith
  have hpow : (T s:ℂ)^(a-1) = (s:ℂ)^(a-1)*((dslope T 0 s:ℝ):ℂ)^(a-1) := by
    rw [hprod]
    simpa only [Complex.ofReal_mul] using! Complex.mul_cpow_ofReal_nonneg hs.1.le hPs.le (a-1)
  rw [Complex.real_smul,abs_of_pos (hDpos s hs'),hphase,hpow]
  dsimp [amplitude]
  have hexp : -b*(s^2/2) = -b*s^2/2 := by ring
  rw [hexp]
  ring

/-- The saddle inverse and transformed amplitude satisfy the substitution hypotheses
on a positive compact interval. -/
lemma exists_interval {T : ℝ → ℝ} (hT : AnalyticAt ℝ T 0)
    (hdT : HasDerivAt T 1 0) (hT0 : T 0=0)
    (hr : ∀ᶠ s in 𝓝 (0:ℝ), coordinate (T s)=s) (a : ℂ) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ s ∈ Icc (0:ℝ) δ, HasDerivAt T (deriv T s) s) ∧
      (∀ s ∈ Icc (0:ℝ) δ, 0 < deriv T s) ∧
      StrictMonoOn T (Icc (0:ℝ) δ) ∧
      (∀ s ∈ Icc (0:ℝ) δ, 0 < dslope T 0 s) ∧
      (∀ s ∈ Icc (0:ℝ) δ, 0 < quadraticFactor (T s)) ∧
      (∀ s ∈ Icc (0:ℝ) δ, coordinate (T s)=s) ∧
      ContinuousOn (amplitude T a) (Icc (0:ℝ) δ) := by
  have hPa : AnalyticAt ℝ (dslope T 0) 0 := hT.dslope 0
  have hP0 : dslope T 0 0=1 := by simp only [dslope_same,hdT.deriv]
  have hAa := (amplitude_data hT hdT hT0 hr a).1
  have hQ : AnalyticAt ℝ (fun s => quadraticFactor (T s)) 0 :=
    analyticAt_quadraticFactor.comp_of_eq hT hT0
  have hdpos : 0 < deriv T 0 := by rw [hdT.deriv];norm_num
  have hppos : 0 < dslope T 0 0 := by rw [hP0];norm_num
  have hqpos : 0 < quadraticFactor (T 0) := by rw [hT0,quadraticFactor_zero];norm_num
  have he := hT.eventually_analyticAt.and
    ((hT.deriv.continuousAt.eventually (lt_mem_nhds hdpos)).and
    ((hPa.continuousAt.eventually (lt_mem_nhds hppos)).and
    ((hQ.continuousAt.eventually (lt_mem_nhds hqpos)).and (hr.and hAa.eventually_analyticAt))))
  obtain ⟨r,hrpos,hrall⟩ := Metric.eventually_nhds_iff.mp he
  let δ : ℝ := r/2
  have hδ : 0 < δ := by dsimp [δ];positivity
  have hall (s : ℝ) (hs : s ∈ Icc (0:ℝ) δ) :
      AnalyticAt ℝ T s ∧ 0 < deriv T s ∧ 0 < dslope T 0 s ∧
      0 < quadraticFactor (T s) ∧ coordinate (T s)=s ∧ AnalyticAt ℝ (amplitude T a) s := by
    apply hrall
    rw [Real.dist_eq,sub_zero,abs_of_nonneg hs.1]
    dsimp [δ] at hs
    linarith [hs.2]
  have hc : ContinuousOn T (Icc (0:ℝ) δ) :=
    fun s hs => (hall s hs).1.continuousAt.continuousWithinAt
  refine ⟨δ,hδ,fun s hs => (hall s hs).1.differentiableAt.hasDerivAt,
    fun s hs => (hall s hs).2.1,?_,fun s hs => (hall s hs).2.2.1,
    fun s hs => (hall s hs).2.2.2.1,fun s hs => (hall s hs).2.2.2.2.1,
    fun s hs => (hall s hs).2.2.2.2.2.continuousAt.continuousWithinAt⟩
  exact strictMonoOn_of_deriv_pos (convex_Icc _ _) hc
    (fun s hs => (hall s (interior_subset hs)).2.1)

/-- The Tricomi phase has derivative `t/(1+t)` on the nonnegative half-line. -/
lemma hasDerivAt_phase {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt phase (t / (1+t)) t := by
  have hn : 1+t ≠ 0 := by positivity
  have hlog := ((hasDerivAt_id t).const_add 1).log hn
  exact ((hasDerivAt_id t).sub hlog).congr_deriv (by dsimp only [_root_.id]; field_simp; ring)

/-- The Tricomi phase is strictly increasing on the nonnegative half-line. -/
lemma strictMonoOn_phase : StrictMonoOn phase (Ici 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici 0) ?_ ?_
  · intro t ht
    exact (hasDerivAt_phase ht).continuousAt.continuousWithinAt
  · intro t ht
    have ht0 : 0 < t := by simpa using ht
    rw [(hasDerivAt_phase ht0.le).deriv]
    positivity

/-- The Tricomi phase is positive at every positive argument. -/
lemma phase_pos {t : ℝ} (ht : 0 < t) : 0 < phase t := by
  have h := strictMonoOn_phase (show (0:ℝ) ∈ Set.Ici 0 by simp) ht.le ht
  simpa [phase] using h

/-- The parameter-independent Tricomi amplitude is integrable for `Re a > 0`. -/
lemma integrableOn_weight {a : ℂ} (ha : 0 < a.re) :
    IntegrableOn (fun t : ℝ => (t:ℂ)^(a-1)*((1+t:ℝ):ℂ)^(-a-1)) (Ioi 0) := by
  refine (integrableOn_cpow_div_one_add_cpow ha (by simp : 0 < (1:ℂ).re)).congr_fun
    (fun t ht => ?_) measurableSet_Ioi
  rw [show -a-1=-(a+1) by ring,cpow_neg]
  push_cast
  rfl

/-- Every fixed positive Tricomi tail is exponentially small as the parameter grows. -/
lemma isBigO_tail {a : ℂ} (ha : 0 < a.re) {r : ℝ} (hr : 0 < r) :
    (fun b : ℝ => ∫ t in Ioi r, (Real.exp (-b*phase t):ℂ)*
      (t:ℂ)^(a-1)*((1+t:ℝ):ℂ)^(-a-1)) =O[atTop]
      (fun b : ℝ => Real.exp (-b*phase r)) := by
  let w : ℝ → ℂ := fun t => (t:ℂ)^(a-1)*((1+t:ℝ):ℂ)^(-a-1)
  have hi := (integrableOn_weight ha).mono_set (Ioi_subset_Ioi hr.le)
  refine IsBigO.of_bound (∫ t in Ioi r, ‖w t‖) ?_
  filter_upwards [eventually_ge_atTop 0] with b hb
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  calc
    ‖∫ t in Ioi r, (Real.exp (-b*phase t):ℂ)*(t:ℂ)^(a-1)*
        ((1+t:ℝ):ℂ)^(-a-1)‖ ≤
        ∫ t in Ioi r, ‖(Real.exp (-b*phase t):ℂ)*(t:ℂ)^(a-1)*
          ((1+t:ℝ):ℂ)^(-a-1)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi r, Real.exp (-b*phase r)*‖w t‖ := by
      apply integral_mono_of_nonneg
      · exact Eventually.of_forall fun t => norm_nonneg _
      · exact hi.norm.const_mul _
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        rw [mul_assoc,norm_mul,norm_real,Real.norm_of_nonneg (Real.exp_pos _).le]
        exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by
          have hp := strictMonoOn_phase.monotoneOn hr.le (hr.trans ht).le ht.le
          nlinarith)) (norm_nonneg _)
    _ = _ := by rw [integral_const_mul]; ring

/-- The positive Tricomi tail is bounded by every prescribed complex power. -/
lemma isBigO_tail_cpow {a : ℂ} (ha : 0 < a.re) {r : ℝ} (hr : 0 < r) (v : ℂ) :
    (fun b : ℝ => ∫ t in Ioi r, (Real.exp (-b*phase t):ℂ)*
      (t:ℂ)^(a-1)*((1+t:ℝ):ℂ)^(-a-1)) =O[atTop]
      (fun b : ℝ => (b:ℂ)^v) := by
  refine (isBigO_tail ha hr).trans ?_
  have h : (fun b : ℝ => Real.exp (-b*phase r)) =O[atTop]
      (fun b : ℝ => b^v.re) := by
    simpa only [mul_neg,neg_mul,mul_comm] using
      (isLittleO_exp_neg_mul_rpow_atTop (phase_pos hr) v.re).isBigO
  refine h.trans (IsBigO.of_bound 1 ?_)
  filter_upwards [eventually_gt_atTop 0] with b hb
  rw [one_mul,Real.norm_of_nonneg (Real.rpow_nonneg hb.le _),
    norm_cpow_eq_rpow_re_of_pos hb]

/-- The local Gaussian integral has the first two saddle coefficients with a
second-order remainder. -/
lemma isBigO_local {T : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hT : AnalyticAt ℝ T 0) (hdT : HasDerivAt T 1 0) (hT0 : T 0=0)
    (hr : ∀ᶠ s in 𝓝 (0:ℝ), coordinate (T s)=s)
    {a : ℂ} (hAc : ContinuousOn (amplitude T a) (Icc 0 δ)) (ha : 0 < a.re) :
    (fun b : ℝ => (∫ s in Ioc (0:ℝ) δ,
      (Real.exp (-b*s^2/2):ℂ)*(s:ℂ)^(a-1)*amplitude T a s) -
        ((b:ℂ)^(-a/2)*(Gamma (a/2)*(1/2:ℂ)^(-(a/2))/2) +
          (b:ℂ)^(-(a+1)/2)*(Gamma ((a+1)/2)*(1/2:ℂ)^(-((a+1)/2))/2)*
            (-2*(a+1)/3))) =O[atTop] (fun b : ℝ => (b:ℂ)^(-(a+2)/2)) := by
  obtain ⟨hAa,hA0,hAd⟩ := amplitude_data hT hdT hT0 hr a
  obtain ⟨p,hp⟩ := hAa
  have hp0 : p.coeff 0 = 1 := (hp.coeff_zero _).trans hA0
  have hp1 : p.coeff 1 = -2*(a+1)/3 := hp.hasDerivAt.unique hAd
  have hW := (Asymptotics.hasAsymptoticExpansion_gaussian_cpow hp hδ hAc ha) 2
  have h := hW.comp_tendsto Real.tendsto_sqrt_atTop
  refine h.congr' ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with b hb
    simp only [Function.comp_apply,Finset.sum_range_succ,Finset.range_zero,
      Finset.sum_empty,zero_add,add_zero,Nat.cast_zero,Nat.cast_one,smul_eq_mul,hp0,hp1,mul_one,
      Complex.QuadraticLaplace.mellin_exp_neg_half_sq ha,
      Complex.QuadraticLaplace.mellin_exp_neg_half_sq (show 0 < (a+1).re by simp;linarith)]
    simp_rw [Complex.ofReal_sqrt_cpow hb]
    congr 1
    · apply setIntegral_congr_fun measurableSet_Ioc
      intro s hs
      dsimp only
      congr 3
      rw [mul_pow,Real.sq_sqrt hb.le]
      ring
    · ring
  · filter_upwards [eventually_gt_atTop 0] with b hb
    simp only [Function.comp_apply,Nat.cast_ofNat]
    rw [Complex.ofReal_sqrt_cpow hb]

/-- The diagonal Tricomi kernel separates into its Laplace phase and fixed amplitude. -/
lemma kernel_eq (a : ℂ) (b : ℝ) {t : ℝ} (ht : 0 < t) :
    (Real.exp (-b*phase t):ℂ)*(t:ℂ)^(a-1)*((1+t:ℝ):ℂ)^(-a-1) =
      exp (-(b:ℂ)*t)*(t:ℂ)^(a-1)*(1+(t:ℂ))^((b:ℂ)-a-1) := by
  have hn : (1+(t:ℂ)) ≠ 0 := by
    have : 0 < (1+t:ℝ) := by positivity
    exact_mod_cast this.ne'
  have he : ((1+t:ℝ):ℂ)=1+(t:ℂ) := by push_cast;rfl
  rw [he,cpow_def_of_ne_zero hn,cpow_def_of_ne_zero hn,ofReal_exp]
  calc
    _ = (t:ℂ)^(a-1)*exp (((-b*phase t:ℝ):ℂ)+log (1+(t:ℂ))*(-a-1)) := by
      rw [exp_add];ring
    _ = (t:ℂ)^(a-1)*exp (-(b:ℂ)*t+log (1+(t:ℂ))*((b:ℂ)-a-1)) := by
      congr 2
      rw [←he,←ofReal_log (by positivity)]
      dsimp only [phase]
      push_cast
      ring
    _ = _ := by rw [exp_add];ring

/-- The first two Gaussian moments give the diagonal Tricomi expansion for `Re a > 0`. -/
lemma isBigO_integral_of_re_pos {a : ℂ} (ha : 0 < a.re) :
    (fun b : ℝ => kummerU a b b - 1/Gamma a *
      ((b:ℂ)^(-a/2)*(Gamma (a/2)*(1/2:ℂ)^(-(a/2))/2) +
        (b:ℂ)^(-(a+1)/2)*(Gamma ((a+1)/2)*(1/2:ℂ)^(-((a+1)/2))/2)*
          (-2*(a+1)/3))) =O[atTop] (fun b : ℝ => (b:ℂ)^(-(a+2)/2)) := by
  obtain ⟨T,hT,hdT,hT0,hl,hr⟩ := exists_inverse
  obtain ⟨δ,hδ,hD,hDp,hmono,hP,hQ,hrI,hAc⟩ := exists_interval hT hdT hT0 hr a
  have hTδ : 0 < T δ := by
    have h := hmono (show (0:ℝ) ∈ Icc (0:ℝ) δ from ⟨le_rfl,hδ.le⟩)
      (show δ ∈ Icc (0:ℝ) δ from ⟨hδ.le,le_rfl⟩) hδ
    simpa only [hT0] using h
  have hlocal := isBigO_local hδ hT hdT hT0 hr hAc ha
  have htail := isBigO_tail_cpow ha hTδ (-(a+2)/2)
  have h := (hlocal.add htail).const_mul_left (1/Gamma a)
  refine h.congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop 0] with b hb
  rw [kummerU_laplace ha (by simpa using hb)]
  have hi := kummerU_laplace_integrable (a := a) (b := (b:ℂ)) (z := (b:ℂ)) ha (by simpa using hb)
  have hker : (fun t : ℝ => exp (-(b:ℂ)*t)*(t:ℂ)^(a-1)*
      (1+(t:ℂ))^((b:ℂ)-a-1)) =ᶠ[ae (volume.restrict (Ioi 0))]
      (fun t : ℝ => (Real.exp (-b*phase t):ℂ)*(t:ℂ)^(a-1)*((1+t:ℝ):ℂ)^(-a-1)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (kernel_eq a b ht).symm
  rw [integral_congr_ae hker]
  have hi' : IntegrableOn (fun t : ℝ => (Real.exp (-b*phase t):ℂ)*(t:ℂ)^(a-1)*
      ((1+t:ℝ):ℂ)^(-a-1)) (Ioi 0) := hi.congr hker
  rw [←integral_substitution hδ hT0 hD hDp hmono hP hQ hrI a b]
  have hiu : Set.Ioc (0:ℝ) (T δ) ∪ Set.Ioi (T δ) = Set.Ioi 0 := Ioc_union_Ioi_eq_Ioi hTδ.le
  rw [←hiu,setIntegral_union Ioc_disjoint_Ioi_same
    measurableSet_Ioi (hi'.mono_set (by intro t ht;exact ht.1))
    (hi'.mono_set (Ioi_subset_Ioi hTδ.le))]
  ring

end DLMF.Confluent.KummerTransition
