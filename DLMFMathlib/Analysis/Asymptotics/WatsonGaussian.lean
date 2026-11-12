/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Asymptotics.WatsonComplexKernel
public import DLMFMathlib.Analysis.Asymptotics.WatsonSector
public import DLMFMathlib.Analysis.SpecialFunctions.ImproperIntegralsExtra
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Gaussian Watson expansions with a complex endpoint exponent

Quadratic exponential moments are Gamma integrals. Watson's lemma then expands a finite
Gaussian integral with analytic amplitude and a factor `t^(a-1)` for `Re a > 0`.
The proofs use the general-kernel Watson lemma and Mathlib's positive-power substitution.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics Finset
open scoped Real Topology

namespace Complex.QuadraticLaplace

/-- The quadratic Laplace moment for `Re s > -1` and `Re a > 0`. -/
theorem integral_cpow_mul_exp_neg_mul_sq {s a : ℂ} (hs : -1 < s.re) (ha : 0 < a.re) :
    (∫ t : ℝ in Ioi 0, (t : ℂ) ^ s * exp (-(a * (t : ℂ) ^ 2))) =
      Gamma ((s + 1) / 2) * a ^ (-((s + 1) / 2)) / 2 := by
  have hG := integral_cpow_mul_cexp_neg_mul_Ioi (s := (s + 1) / 2)
    (z := a) (by simp only [div_ofNat_re, add_re, one_re]; linarith) ha
  have hp := integral_comp_rpow_Ioi_of_pos
    (g := fun u : ℝ => (u : ℂ) ^ ((s + 1) / 2 - 1) * exp (-(a * u)))
    (p := (2 : ℝ)) (by norm_num)
  have hpoint : ∀ t ∈ Ioi (0 : ℝ),
      ((2 : ℝ) * t ^ ((2 : ℝ) - 1)) •
        (((t ^ (2 : ℝ) : ℝ) : ℂ) ^ ((s + 1) / 2 - 1) *
          exp (-(a * ((t ^ (2 : ℝ) : ℝ) : ℂ)))) =
      2 * ((t : ℂ) ^ s * exp (-(a * (t : ℂ) ^ 2))) := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
    have hc : ((t ^ (2 : ℝ) : ℝ) : ℂ) = (t : ℂ) ^ (2 : ℂ) := by
      exact ofReal_cpow ht.le 2
    have hc2 : ((t ^ ((2 : ℝ) - 1) : ℝ) : ℂ) = (t : ℂ) ^ (1 : ℂ) := by
      norm_num
    have hi : (log (t : ℂ) * (2 : ℂ)).im = 0 := by
      simp [mul_im, log_im, arg_ofReal_of_nonneg ht.le]
    simp only [Complex.real_smul, ofReal_mul, ofReal_ofNat, hc, hc2]
    rw [← cpow_mul _ (by rw [hi]; exact neg_lt_zero.mpr Real.pi_pos)
      (by rw [hi]; exact Real.pi_pos.le)]
    have he : (2 : ℂ) * ((s + 1) / 2 - 1) = s - 1 := by ring
    rw [he]
    rw [← cpow_natCast]
    calc _ = 2 * (((t : ℂ) ^ (1 : ℂ) * (t : ℂ) ^ (s - 1)) *
        exp (-(a * (t : ℂ) ^ (2 : ℂ)))) := by ring
      _ = _ := by
        rw [← cpow_add _ _ ht0, show (1 : ℂ) + (s - 1) = s by ring]
        norm_num
  rw [setIntegral_congr_fun measurableSet_Ioi hpoint, integral_const_mul, hG] at hp
  linear_combination (1 / 2 : ℂ) * hp



/-- The Mellin transform of the standard half-Gaussian for `Re v > 0`. -/
theorem mellin_exp_neg_half_sq {v : ℂ} (hv : 0 < v.re) :
    mellin (fun t : ℝ => (Real.exp (-t^2/2):ℂ)) v =
      Gamma (v/2)*(1/2:ℂ)^(-(v/2))/2 := by
  have he (t : ℝ) : (Real.exp (-t^2/2):ℂ) = exp (-((1/2:ℂ)*(t:ℂ)^2)) := by
    rw [ofReal_exp]
    congr 1
    push_cast
    ring
  simp_rw [he]
  rw [mellin]
  simp only [smul_eq_mul]
  rw [Complex.QuadraticLaplace.integral_cpow_mul_exp_neg_mul_sq
    (by simp only [sub_re,one_re];linarith) (by norm_num),sub_add_cancel]


end Complex.QuadraticLaplace

namespace Complex

/-- A complex power of a positive square root is a half-power of the original argument. -/
theorem ofReal_sqrt_cpow {b : ℝ} (hb : 0 < b) (v : ℂ) :
    (Real.sqrt b:ℂ)^v = (b:ℂ)^(v/2) := by
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hb).ne'),
    cpow_def_of_ne_zero (ofReal_ne_zero.mpr hb.ne'),
    ←ofReal_log (Real.sqrt_nonneg b),←ofReal_log hb.le,Real.log_sqrt hb.le]
  congr 1
  push_cast
  ring

/-- Inverting the positive base two negates a complex exponent. -/
theorem one_div_two_cpow_neg (a : ℂ) : (1/2:ℂ)^(-a)=(2:ℂ)^a := by
  rw [show (1/2:ℂ)=(2:ℂ)⁻¹ by norm_num,
    inv_cpow _ _ (by norm_num [arg_ofReal_of_nonneg]; exact ne_of_lt Real.pi_pos),cpow_neg,inv_inv]

end Complex

/-- Positive real analytic functions have real analytic complex powers. -/
theorem AnalyticAt.ofReal_cpow {f : ℝ → ℝ} {x : ℝ} (hf : AnalyticAt ℝ f x)
    (hf0 : 0 < f x) (a : ℂ) : AnalyticAt ℝ (fun s => (f s:ℂ)^a) x := by
  have hg : AnalyticAt ℂ (fun z : ℂ => z^a) (f x:ℂ) :=
    analyticAt_id.cpow analyticAt_const (Or.inl (by simpa using hf0))
  have hg' : AnalyticAt ℝ (fun z : ℂ => z^a) (f x:ℂ) := hg.restrictScalars
  have hf' : AnalyticAt ℝ (fun s : ℝ => (f s:ℂ)) x := by
    simpa only [Function.comp_def] using! (Complex.ofRealCLM.analyticAt (f x)).comp hf
  exact hg'.comp_of_eq hf' rfl

namespace Asymptotics

/-- A finite Gaussian integral with analytic amplitude has a complex-power expansion. -/
theorem hasAsymptoticExpansion_gaussian_cpow {H : ℝ → ℂ} {p : FormalMultilinearSeries ℝ ℝ ℂ}
    (hp : HasFPowerSeriesAt H p 0) {δ : ℝ} (hδ : 0 < δ)
    (hH : ContinuousOn H (Icc 0 δ)) {a : ℂ} (ha : 0 < a.re) :
    HasAsymptoticExpansion atTop (fun (n : ℕ) (x : ℝ) => (x:ℂ)^(-(a+n)))
      (fun n => mellin (fun t : ℝ => (Real.exp (-t^2/2):ℂ)) (a+n)*p.coeff n)
      (fun x : ℝ => ∫ t in Ioc (0:ℝ) δ,
        (Real.exp (-(x*t)^2/2):ℂ)*(t:ℂ)^(a-1)*H t) := by
  let q : ℝ → ℂ := indicator (Ioc 0 δ) (fun t => (t:ℂ)^(a-1)*H t)
  have hqi : Integrable q := by
    obtain ⟨M,hM⟩ := (isCompact_Icc (a := (0:ℝ)) (b := δ)).exists_bound_of_continuousOn hH
    have hm : IntegrableOn (fun t : ℝ => M*t^(a.re-1)) (Ioc 0 δ) :=
      ((intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < a.re-1)).1).const_mul M
    change Integrable (indicator (Ioc (0:ℝ) δ) (fun t => (t:ℂ)^(a-1)*H t))
    rw [integrable_indicator_iff measurableSet_Ioc]
    apply hm.mono'
    · have hc : ContinuousOn (fun t : ℝ => (t:ℂ)^(a-1)*H t) (Ioc 0 δ) := by
        apply ContinuousOn.mul _ (hH.mono Ioc_subset_Icc_self)
        intro t ht
        exact (continuousAt_ofReal_cpow_const _ _ (Or.inr ht.1.ne')).continuousWithinAt
      exact hc.aestronglyMeasurable measurableSet_Ioc
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [norm_mul,norm_cpow_eq_rpow_re_of_pos ht.1]
      simp only [sub_re,one_re]
      have htH := hM t (Ioc_subset_Icc_self ht)
      nlinarith [Real.rpow_nonneg ht.1.le (a.re-1)]
  have hqtop : q =O[atTop] (fun t : ℝ => Real.exp (1*t^(2:ℝ))) := by
    apply IsBigO.of_bound 0
    filter_upwards [eventually_gt_atTop δ] with t ht
    simp [q,indicator_of_notMem (show t ∉ Ioc (0:ℝ) δ by exact fun h => not_le_of_gt ht h.2)]
  have hqt (N : ℕ) : (fun t => q t-∑ n∈range N, (t:ℂ)^(a+n-1)*p.coeff n)
      =O[𝓝[>] 0] (fun t : ℝ => t^((a+N).re-1)) := by
    have hP : (fun t : ℝ => (t:ℂ)^(a-1)) =O[𝓝[>] 0]
        (fun t : ℝ => t^(a.re-1)) := by
      apply IsBigO.of_bound 1
      filter_upwards [self_mem_nhdsWithin] with t ht
      rw [norm_cpow_eq_rpow_re_of_pos ht]
      simp only [sub_re,one_re]
      rw [Real.norm_of_nonneg (Real.rpow_nonneg ht.le _),one_mul]
    have hT : (fun t : ℝ => H (0+t)-p.partialSum N t) =O[𝓝[>] 0]
        (fun t : ℝ => ‖t‖^N) :=
      (hp.isBigO_sub_partialSum_pow N).mono nhdsWithin_le_nhds
    have h := hP.mul hT
    apply h.congr'
    · filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Iio_mem_nhds hδ)] with t ht htδ
      have ht0 : (t:ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
      simp only [q,indicator_of_mem (show t ∈ Ioc (0:ℝ) δ from ⟨ht,htδ.le⟩),
        zero_add,FormalMultilinearSeries.partialSum,
        FormalMultilinearSeries.apply_eq_pow_smul_coeff,smul_eq_mul,mul_sub,Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro n hn
      rw [show a+(n:ℂ)-1=(a-1)+(n:ℂ) by ring,cpow_add _ _ ht0,cpow_natCast]
      simp [mul_assoc,Complex.real_smul]
    · filter_upwards [self_mem_nhdsWithin] with t ht
      rw [Real.norm_of_nonneg ht.le]
      rw [show (a+(N:ℂ)).re-1=(a.re-1)+(N:ℝ) by simp;ring,
        Real.rpow_add ht,Real.rpow_natCast]
  have h := hasAsymptoticExpansion_integral_kernel_mul_cpow_seq
    (f := fun t : ℝ => (Real.exp (-t^2/2):ℂ))
    (q := q) (d := fun n => p.coeff n) (e := fun n => a+n)
    (A := 1) (a := 1/2) (b := 1) (κ := 2)
    (fun n => by simp; positivity) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Measurable.aestronglyMeasurable (by fun_prop))
    (fun t ht => by
      rw [norm_real,Real.norm_of_nonneg (Real.exp_pos _).le,one_mul,Real.rpow_two]
      apply Real.exp_le_exp.mpr
      nlinarith)
    (hqi.locallyIntegrable.locallyIntegrableOn (Ioi 0)) hqtop hqt
  apply h.congr'
  exact Eventually.of_forall fun x => by
    have he (t : ℝ) : (Real.exp (-(x*t)^2/2):ℂ)*q t =
        indicator (Ioc (0:ℝ) δ) (fun t =>
          (Real.exp (-(x*t)^2/2):ℂ)*(t:ℂ)^(a-1)*H t) t := by
      by_cases ht : t ∈ Ioc (0:ℝ) δ <;> simp [q,indicator,ht,mul_assoc]
    simp_rw [he]
    rw [setIntegral_indicator measurableSet_Ioc,Set.inter_eq_right.mpr Set.Ioc_subset_Ioi_self]


/-- A smaller real part gives a smaller complex power on the positive real axis. -/
theorem isBigO_ofReal_cpow_of_re_le {u v : ℂ} (h : u.re ≤ v.re) :
    (fun b : ℝ => (b:ℂ)^u) =O[atTop] (fun b : ℝ => (b:ℂ)^v) := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop 1] with b hb
  have hb0 : 0 < b := by linarith
  rw [one_mul,norm_cpow_eq_rpow_re_of_pos hb0,norm_cpow_eq_rpow_re_of_pos hb0]
  exact Real.rpow_le_rpow_of_exponent_le hb h

end Asymptotics
