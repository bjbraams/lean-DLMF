/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.Asymptotics.Transition

/-!
# The reflected quadratic saddle in the diagonal Euler integral

Reflection of the signed Tricomi saddle coordinate transforms the Euler integral for
`M(a,b,b)` into a Gaussian integral with the opposite first correction. The singular
endpoint is controlled by a fixed integrable Euler kernel and an exponential tail bound.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics
open scoped Real Topology

namespace DLMF.Confluent.KummerTransition

/-- The quadratic factorization of the Tricomi phase holds on a full neighborhood
of the origin. -/
lemma phase_eq_sq_mul_near :
    (fun t => phase t) =ᶠ[𝓝 (0:ℝ)] (fun t => t^2*quadraticFactor t) := by
  have h1 : AnalyticAt ℝ phase 0 := by
    apply AnalyticAt.sub analyticAt_id
    apply AnalyticAt.log (analyticAt_const.add analyticAt_id)
    norm_num
  have h2 : AnalyticAt ℝ (fun t : ℝ => t^2*quadraticFactor t) 0 :=
    (analyticAt_id.pow 2).mul analyticAt_quadraticFactor
  apply (h1.frequently_eq_iff_eventually_eq h2).mp
  have hf : ∀ᶠ t : ℝ in 𝓝[>] 0, phase t=t^2*quadraticFactor t := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact phase_eq_sq_mul ht
  exact hf.frequently.filter_mono (nhdsWithin_mono _ (fun t ht => ne_of_gt ht))

/-- The Euler-integral phase `-t-log(1-t)` for the diagonal Kummer function. -/
def eulerPhase (t : ℝ) : ℝ := phase (-t)
/-- Reflection of the signed saddle inverse to the Euler interval. -/
def reflectedInverse (T : ℝ → ℝ) (s : ℝ) : ℝ := -T (-s)

/-- The reflected saddle inverse and amplitude satisfy the substitution
hypotheses on a positive compact interval. -/
lemma exists_euler_interval {T : ℝ → ℝ} (hT : AnalyticAt ℝ T 0)
    (hdT : HasDerivAt T 1 0) (hT0 : T 0=0)
    (hr : ∀ᶠ s in 𝓝 (0:ℝ), coordinate (T s)=s) (a : ℂ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc (0:ℝ) δ,
      AnalyticAt ℝ T (-s) ∧ 0 < deriv T (-s) ∧ 0 < dslope T 0 (-s) ∧
      0 < quadraticFactor (T (-s)) ∧ coordinate (T (-s)) = -s ∧
      phase (T (-s)) = (T (-s))^2*quadraticFactor (T (-s)) ∧
      -1 < T (-s) ∧ AnalyticAt ℝ (amplitude T a) (-s) := by
  have hPa : AnalyticAt ℝ (dslope T 0) 0 := hT.dslope 0
  have hP0 : dslope T 0 0=1 := by simp only [dslope_same,hdT.deriv]
  have hAa := (amplitude_data hT hdT hT0 hr a).1
  have hQ : AnalyticAt ℝ (fun s => quadraticFactor (T s)) 0 :=
    analyticAt_quadraticFactor.comp_of_eq hT hT0
  have hdpos : 0 < deriv T 0 := by rw [hdT.deriv];norm_num
  have hppos : 0 < dslope T 0 0 := by rw [hP0];norm_num
  have hqpos : 0 < quadraticFactor (T 0) := by rw [hT0,quadraticFactor_zero];norm_num
  have hph : ∀ᶠ s in 𝓝 (0:ℝ), phase (T s)=(T s)^2*quadraticFactor (T s) := by
    have hcont : Tendsto T (𝓝 (0:ℝ)) (𝓝 (0:ℝ)) := by
      simpa only [hT0] using hT.continuousAt.tendsto
    exact hcont.eventually phase_eq_sq_mul_near
  have hneg : ∀ᶠ s in 𝓝 (0:ℝ), -1 < T s :=
    hT.continuousAt.eventually (lt_mem_nhds (by rw [hT0];norm_num))
  have he := hT.eventually_analyticAt.and
    ((hT.deriv.continuousAt.eventually (lt_mem_nhds hdpos)).and
    ((hPa.continuousAt.eventually (lt_mem_nhds hppos)).and
    ((hQ.continuousAt.eventually (lt_mem_nhds hqpos)).and
      (hr.and (hph.and (hneg.and hAa.eventually_analyticAt))))))
  obtain ⟨r,hrpos,hrall⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨r/2,by positivity,?_⟩
  intro s hs
  apply hrall
  rw [Real.dist_eq,sub_zero,abs_neg,abs_of_nonneg hs.1]
  linarith [hs.2]

/-- The local Euler integral becomes a Gaussian integral under the reflected
saddle substitution. -/
lemma euler_integral_substitution {T : ℝ → ℝ} {δ : ℝ} {a : ℂ} (hδ : 0 < δ)
    (hT0 : T 0=0)
    (hdata : ∀ s ∈ Icc (0:ℝ) δ,
      AnalyticAt ℝ T (-s) ∧ 0 < deriv T (-s) ∧ 0 < dslope T 0 (-s) ∧
      0 < quadraticFactor (T (-s)) ∧ coordinate (T (-s)) = -s ∧
      phase (T (-s)) = (T (-s))^2*quadraticFactor (T (-s)) ∧
      -1 < T (-s) ∧ AnalyticAt ℝ (amplitude T a) (-s))
    (b : ℝ) :
    (∫ t in Ioc (0:ℝ) (reflectedInverse T δ), (Real.exp (-b*eulerPhase t):ℂ)*
      (t:ℂ)^(a-1)*((1-t:ℝ):ℂ)^(-a-1)) =
    ∫ s in Ioc (0:ℝ) δ, (Real.exp (-b*s^2/2):ℂ)*(s:ℂ)^(a-1)*amplitude T a (-s) := by
  have hD (s : ℝ) (hs : s ∈ Icc (0:ℝ) δ) :
      HasDerivAt (reflectedInverse T) (deriv T (-s)) s := by
    simpa only [reflectedInverse,Function.comp_def,Pi.neg_apply,neg_neg,mul_neg,one_mul,mul_one]
      using!
      (((hdata s hs).1.differentiableAt.hasDerivAt.comp s (hasDerivAt_neg s)).neg)
  have hc : ContinuousOn (reflectedInverse T) (Icc (0:ℝ) δ) :=
    fun s hs => (hD s hs).continuousAt.continuousWithinAt
  have hmono : StrictMonoOn (reflectedInverse T) (Icc (0:ℝ) δ) :=
    strictMonoOn_of_deriv_pos (convex_Icc _ _) hc
      (fun s hs => by
        rw [(hD s (interior_subset hs)).deriv]
        exact (hdata s (interior_subset hs)).2.1)
  have hS0 : reflectedInverse T 0=0 := by simp [reflectedInverse,hT0]
  have himage := hc.image_Ioc_of_strictMonoOn hδ.le hmono
  rw [hS0] at himage
  rw [←himage,integral_image_eq_integral_abs_deriv_smul measurableSet_Ioc
    (fun s hs => (hD s (Ioc_subset_Icc_self hs)).hasDerivWithinAt)
    (hmono.injOn.mono Ioc_subset_Icc_self)]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro s hs
  dsimp only
  have hs' := Ioc_subset_Icc_self hs
  have hSs : 0 < reflectedInverse T s := by
    have h := hmono (show (0:ℝ) ∈ Icc (0:ℝ) δ from ⟨le_rfl,hδ.le⟩) hs' hs.1
    simpa only [hS0] using h
  have hPs := (hdata s hs').2.2.1
  have hprod : reflectedInverse T s=s*dslope T 0 (-s) := by
    have hp := sub_smul_dslope_of_zero hT0 (-s)
    dsimp only [reflectedInverse]
    simp only [sub_zero,smul_eq_mul] at hp
    linear_combination hp
  have hphase : eulerPhase (reflectedInverse T s)=s^2/2 := by
    have he := congrArg (fun x : ℝ => x^2) (hdata s hs').2.2.2.2.1
    simp only [coordinate,DoubleZeroSqrt.signedSqrt,sub_zero,mul_pow,neg_sq,
      Real.sq_sqrt (show 0 ≤ 2*quadraticFactor (T (-s)) by
        linarith [(hdata s hs').2.2.2.1])] at he
    simp only [eulerPhase,reflectedInverse,neg_neg]
    rw [(hdata s hs').2.2.2.2.2.1]
    nlinarith
  have hpow : (reflectedInverse T s:ℂ)^(a-1) =
      (s:ℂ)^(a-1)*((dslope T 0 (-s):ℝ):ℂ)^(a-1) := by
    rw [hprod]
    simpa only [ofReal_mul] using! mul_cpow_ofReal_nonneg hs.1.le hPs.le (a-1)
  rw [Complex.real_smul,abs_of_pos (hdata s hs').2.1,hphase,hpow]
  dsimp only [amplitude,reflectedInverse]
  have hexp : -b*(s^2/2) = -b*s^2/2 := by ring
  rw [hexp]
  simp only [sub_neg_eq_add]
  ring

/-- The diagonal Euler kernel separates into its phase and fixed amplitude. -/
lemma euler_kernel_eq (a : ℂ) (b : ℝ) {t : ℝ} (ht : t < 1) :
    (Real.exp (-b*eulerPhase t):ℂ)*(t:ℂ)^(a-1)*((1-t:ℝ):ℂ)^(-a-1) =
      (t:ℂ)^(a-1)*(1-(t:ℂ))^((b:ℂ)-a-1)*exp ((b:ℂ)*t) := by
  have hn : (1-(t:ℂ)) ≠ 0 := by
    have : 0 < (1-t:ℝ) := by linarith
    exact_mod_cast this.ne'
  have he : ((1-t:ℝ):ℂ)=1-(t:ℂ) := by push_cast;rfl
  rw [he,cpow_def_of_ne_zero hn,cpow_def_of_ne_zero hn,ofReal_exp]
  calc
    _ = (t:ℂ)^(a-1)*exp (((-b*eulerPhase t:ℝ):ℂ)+log (1-(t:ℂ))*(-a-1)) := by
      rw [exp_add];ring
    _ = (t:ℂ)^(a-1)*exp ((b:ℂ)*t+log (1-(t:ℂ))*((b:ℂ)-a-1)) := by
      congr 2
      rw [←he,←ofReal_log (by linarith)]
      dsimp only [eulerPhase,phase]
      push_cast
      ring
    _ = _ := by rw [exp_add];ring

/-- The diagonal Euler kernel is integrable for `0 < Re a < b`. -/
lemma integrableOn_euler_kernel {a : ℂ} (ha : 0 < a.re) {b : ℝ} (hb : a.re < b) :
    IntegrableOn (fun t : ℝ => (Real.exp (-b*eulerPhase t):ℂ)*
      (t:ℂ)^(a-1)*((1-t:ℝ):ℂ)^(-a-1)) (Ioo 0 1) := by
  have hB : 0 < ((b:ℂ)-a).re := by simp;linarith
  have hi := (betaIntegral_convergent ha hB).mul_continuousOn
    (g := fun t : ℝ => exp ((b:ℂ)*t)) (by fun_prop)
  have hi' : IntegrableOn (fun t : ℝ =>
      ((t:ℂ)^(a-1)*(1-(t:ℂ))^((b:ℂ)-a-1))*exp ((b:ℂ)*t)) (Ioo 0 1) :=
    hi.1.mono_set (by intro t ht;exact ⟨ht.1,ht.2.le⟩)
  exact hi'.congr_fun (fun t ht => (euler_kernel_eq a b ht.2).symm) measurableSet_Ioo

/-- The Euler phase has derivative `t/(1-t)` below its singular endpoint. -/
lemma hasDerivAt_eulerPhase {t : ℝ} (ht : t < 1) :
    HasDerivAt eulerPhase (t/(1-t)) t := by
  have hn : 1-t ≠ 0 := by linarith
  have hlog := ((hasDerivAt_id t).const_sub 1).log hn
  have h := (hasDerivAt_neg t).sub hlog
  exact h.congr_deriv (by dsimp only [_root_.id];field_simp;ring)

/-- The Euler phase is strictly increasing between zero and one. -/
lemma strictMonoOn_eulerPhase : StrictMonoOn eulerPhase (Ico (0:ℝ) 1) := by
  refine strictMonoOn_of_deriv_pos (convex_Ico 0 1) ?_ ?_
  · intro t ht
    exact (hasDerivAt_eulerPhase ht.2).continuousAt.continuousWithinAt
  · intro t ht
    have ht' : t ∈ Ioo (0:ℝ) 1 := by simpa using ht
    rw [(hasDerivAt_eulerPhase ht'.2).deriv]
    exact div_pos ht'.1 (by linarith [ht'.2])

/-- The Euler phase is positive on the open unit interval. -/
lemma eulerPhase_pos {r : ℝ} (hr : 0 < r) (hr1 : r < 1) : 0 < eulerPhase r := by
  have h := strictMonoOn_eulerPhase (show (0:ℝ) ∈ Ico (0:ℝ) 1 by norm_num)
    ⟨hr.le,hr1⟩ hr
  simpa [eulerPhase,phase] using h

/-- The Euler integral past any fixed positive point is exponentially small. -/
lemma isBigO_euler_tail {a : ℂ} (ha : 0 < a.re) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    (fun b : ℝ => ∫ t in Ioo r 1, (Real.exp (-b*eulerPhase t):ℂ)*
      (t:ℂ)^(a-1)*((1-t:ℝ):ℂ)^(-a-1)) =O[atTop]
      (fun b : ℝ => Real.exp (-b*eulerPhase r)) := by
  let B : ℝ := a.re+1
  let w : ℝ → ℂ := fun t => (t:ℂ)^(a-1)*((1-t:ℝ):ℂ)^(-a-1)
  let G : ℝ → ℂ := fun t => (Real.exp (-B*eulerPhase t):ℂ)*w t
  have hi : IntegrableOn G (Ioo r 1) := by
    simpa only [G,w,mul_assoc] using
      (integrableOn_euler_kernel ha (b := B) (by dsimp [B];linarith)).mono_set
      (Ioo_subset_Ioo hr.le le_rfl)
  refine IsBigO.of_bound ((∫ t in Ioo r 1, ‖G t‖)*Real.exp (B*eulerPhase r)) ?_
  filter_upwards [eventually_ge_atTop B] with b hb
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  have hker (t : ℝ) : (Real.exp (-b*eulerPhase t):ℂ)*
      (t:ℂ)^(a-1)*((1-t:ℝ):ℂ)^(-a-1) =
        (Real.exp (-(b-B)*eulerPhase t):ℂ)*G t := by
    have he : (Real.exp (-b*eulerPhase t):ℂ) =
        (Real.exp (-(b-B)*eulerPhase t):ℂ)*(Real.exp (-B*eulerPhase t):ℂ) := by
      rw [←ofReal_mul,←Real.exp_add]
      congr 2
      ring
    dsimp only [G,w]
    rw [he]
    ring
  simp_rw [hker]
  calc
    ‖∫ t in Ioo r 1, (Real.exp (-(b-B)*eulerPhase t):ℂ)*G t‖ ≤
        ∫ t in Ioo r 1, ‖(Real.exp (-(b-B)*eulerPhase t):ℂ)*G t‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioo r 1, Real.exp (-(b-B)*eulerPhase r)*‖G t‖ := by
      apply integral_mono_of_nonneg
      · exact Eventually.of_forall fun t => norm_nonneg _
      · exact hi.norm.const_mul _
      · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        rw [norm_mul,norm_real,Real.norm_of_nonneg (Real.exp_pos _).le]
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        apply Real.exp_le_exp.mpr
        have hp := strictMonoOn_eulerPhase.monotoneOn ⟨hr.le,hr1⟩
          ⟨(hr.trans ht.1).le,ht.2⟩ ht.1.le
        nlinarith
    _ = _ := by
      rw [integral_const_mul]
      have he : -(b-B)*eulerPhase r=B*eulerPhase r+(-b*eulerPhase r) := by ring
      rw [he,Real.exp_add]
      ring

/-- The reflected analytic amplitude gives the first two normalized Gaussian
moments of the Euler integral. -/
lemma isBigO_euler_local {T : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hT : AnalyticAt ℝ T 0) (hdT : HasDerivAt T 1 0) (hT0 : T 0=0)
    (hr : ∀ᶠ s in 𝓝 (0:ℝ), coordinate (T s)=s)
    {a : ℂ} (hAc : ContinuousOn (fun s => amplitude T a (-s)) (Icc 0 δ))
    (ha : 0 < a.re) :
    (fun b : ℝ => 1/Gamma a*(∫ s in Ioc (0:ℝ) δ,
      (Real.exp (-b*s^2/2):ℂ)*(s:ℂ)^(a-1)*amplitude T a (-s)) -
        (leadingCoefficient a*(b:ℂ)^(-a/2)-
          firstCorrection a*(b:ℂ)^(-(a+1)/2))) =O[atTop]
      (fun b : ℝ => (b:ℂ)^(-a/2-1)) := by
  obtain ⟨hAa,hA0,hAd⟩ := amplitude_data hT hdT hT0 hr a
  have hAref : AnalyticAt ℝ (fun s => amplitude T a (-s)) 0 :=
    hAa.comp_of_eq analyticAt_id.neg (by simp)
  have hArefd : HasDerivAt (fun s => amplitude T a (-s)) (2*(a+1)/3) 0 := by
    have hh := hAd.scomp_of_eq (0:ℝ) (hasDerivAt_neg 0) (by simp)
    simpa only [Function.comp_def,Complex.real_smul,ofReal_neg,ofReal_one,
      neg_mul,one_mul,neg_div,neg_neg] using! hh
  obtain ⟨p,hp⟩ := hAref
  have hp0 : p.coeff 0 = 1 := (hp.coeff_zero _).trans (by simpa using hA0)
  have hp1 : p.coeff 1 = 2*(a+1)/3 := hp.hasDerivAt.unique hArefd
  have hW := (Asymptotics.hasAsymptoticExpansion_gaussian_cpow hp hδ hAc ha) 2
  have h := (hW.comp_tendsto Real.tendsto_sqrt_atTop).const_mul_left (1/Gamma a)
  refine h.congr' ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with b hb
    simp only [Function.comp_apply,Finset.sum_range_succ,Finset.range_zero,
      Finset.sum_empty,zero_add,add_zero,Nat.cast_zero,Nat.cast_one,smul_eq_mul,hp0,hp1,mul_one,
      Complex.QuadraticLaplace.mellin_exp_neg_half_sq ha,
      Complex.QuadraticLaplace.mellin_exp_neg_half_sq (show 0 < (a+1).re by simp;linarith)]
    simp_rw [Complex.ofReal_sqrt_cpow hb]
    have hi : (∫ s in Ioc (0:ℝ) δ,
        (Real.exp (-(Real.sqrt b*s)^2/2):ℂ)*(s:ℂ)^(a-1)*amplitude T a (-s)) =
        ∫ s in Ioc (0:ℝ) δ,
          (Real.exp (-b*s^2/2):ℂ)*(s:ℂ)^(a-1)*amplitude T a (-s) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro s hs
      dsimp only
      rw [mul_pow,Real.sq_sqrt hb.le]
      congr 3
      ring
    rw [hi]
    linear_combination -(b:ℂ)^(-a/2)*integralCoefficient_leading ha+
      (b:ℂ)^(-(a+1)/2)*integralCoefficient_correction ha
  · filter_upwards [eventually_gt_atTop 0] with b hb
    simp only [Function.comp_apply,Nat.cast_ofNat]
    rw [Complex.ofReal_sqrt_cpow hb]
    congr 1
    ring

/-- The full normalized Euler integral has the two-term quadratic-saddle
expansion for `Re a > 0`. -/
lemma isBigO_euler_integral_of_re_pos {a : ℂ} (ha : 0 < a.re) :
    (fun b : ℝ => 1/Gamma a*(∫ t in Ioo (0:ℝ) 1,
      (Real.exp (-b*eulerPhase t):ℂ)*(t:ℂ)^(a-1)*((1-t:ℝ):ℂ)^(-a-1))-
        (leadingCoefficient a*(b:ℂ)^(-a/2)-
          firstCorrection a*(b:ℂ)^(-(a+1)/2))) =O[atTop]
      (fun b : ℝ => (b:ℂ)^(-a/2-1)) := by
  obtain ⟨T,hT,hdT,hT0,hl,hr⟩ := exists_inverse
  obtain ⟨δ,hδ,hdata⟩ := exists_euler_interval hT hdT hT0 hr a
  have hD (s : ℝ) (hs : s ∈ Icc (0:ℝ) δ) :
      HasDerivAt (reflectedInverse T) (deriv T (-s)) s := by
    simpa only [reflectedInverse,Function.comp_def,Pi.neg_apply,neg_neg,mul_neg,one_mul,mul_one]
      using! (((hdata s hs).1.differentiableAt.hasDerivAt.comp s (hasDerivAt_neg s)).neg)
  have hc : ContinuousOn (reflectedInverse T) (Icc (0:ℝ) δ) :=
    fun s hs => (hD s hs).continuousAt.continuousWithinAt
  have hmono : StrictMonoOn (reflectedInverse T) (Icc (0:ℝ) δ) :=
    strictMonoOn_of_deriv_pos (convex_Icc _ _) hc
      (fun s hs => by
        rw [(hD s (interior_subset hs)).deriv]
        exact (hdata s (interior_subset hs)).2.1)
  have hS0 : reflectedInverse T 0=0 := by simp [reflectedInverse,hT0]
  have hr0 : 0 < reflectedInverse T δ := by
    have hh := hmono (show (0:ℝ) ∈ Icc (0:ℝ) δ from ⟨le_rfl,hδ.le⟩)
      (show δ ∈ Icc (0:ℝ) δ from ⟨hδ.le,le_rfl⟩) hδ
    simpa only [hS0] using hh
  have hr1 : reflectedInverse T δ < 1 := by
    have hh := (hdata δ ⟨hδ.le,le_rfl⟩).2.2.2.2.2.2.1
    dsimp only [reflectedInverse]
    linarith
  have hAc : ContinuousOn (fun s => amplitude T a (-s)) (Icc (0:ℝ) δ) := by
    intro s hs
    exact ((hdata s hs).2.2.2.2.2.2.2.comp analyticAt_id.neg).continuousAt.continuousWithinAt
  have hlocal := isBigO_euler_local hδ hT hdT hT0 hr hAc ha
  have hexp : (fun b : ℝ => Real.exp (-b*eulerPhase (reflectedInverse T δ))) =O[atTop]
      (fun b : ℝ => b^(-a/2-1).re) := by
    simpa only [mul_neg,neg_mul,mul_comm] using
      (isLittleO_exp_neg_mul_rpow_atTop (eulerPhase_pos hr0 hr1) (-a/2-1).re).isBigO
  have ht := (isBigO_euler_tail ha hr0 hr1).trans hexp
  have hreal : (fun b : ℝ => b^(-a/2-1).re) =O[atTop]
      (fun b : ℝ => (b:ℂ)^(-a/2-1)) := by
    apply IsBigO.of_bound 1
    filter_upwards [eventually_gt_atTop 0] with b hb
    rw [one_mul,Real.norm_of_nonneg (Real.rpow_nonneg hb.le _),
      norm_cpow_eq_rpow_re_of_pos hb]
  have htail := (ht.trans hreal).const_mul_left (1/Gamma a)
  refine (hlocal.add htail).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop a.re] with b hb
  rw [←euler_integral_substitution hδ hT0 hdata b]
  have hi := integrableOn_euler_kernel ha hb
  have hu : Ioc (0:ℝ) (reflectedInverse T δ) ∪ Ioo (reflectedInverse T δ) 1=Ioo 0 1 := by
    ext t
    simp only [mem_union,mem_Ioc,mem_Ioo]
    constructor
    · rintro (⟨ht0,htr⟩|⟨htr,ht1⟩) <;> exact ⟨by linarith,by linarith⟩
    · intro ht
      by_cases htr : t ≤ reflectedInverse T δ
      · exact Or.inl ⟨ht.1,htr⟩
      · exact Or.inr ⟨lt_of_not_ge htr,ht.2⟩
  have hdis : Disjoint (Ioc (0:ℝ) (reflectedInverse T δ)) (Ioo (reflectedInverse T δ) 1) :=
    Set.disjoint_left.mpr fun t ht ht' => not_lt_of_ge ht.2 ht'.1
  rw [←hu,setIntegral_union hdis
    measurableSet_Ioo (hi.mono_set (by intro t ht;exact ⟨ht.1,ht.2.trans_lt hr1⟩))
    (hi.mono_set (Ioo_subset_Ioo hr0.le le_rfl))]
  ring

end DLMF.Confluent.KummerTransition
