/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Zeta.Lerch.LogarithmicKernel

/-!
# Continuation of the regularized Lerch expansion

The horizontal incomplete-Gamma integral identifies the regularized Hermite expression
on negative real logarithmic arguments. Analytic continuation then identifies it throughout
the logarithmic disk away from its principal branch cut.
-/

@[expose] public noncomputable section

open Complex Set Filter MeasureTheory DLMF.Confluent DLMF.Core
open scoped Real Topology Nat

namespace DLMF.Zeta.LerchLogarithmic

/-- Rescaling the horizontal incomplete-Gamma integral identifies the weighted Lerch ray. -/
theorem exp_mul_integral_rayKernel_eq_upperIncompleteGamma {a : ℂ} (ha : 0 < a.re)
    (s : ℂ) {r : ℝ} (hr : r < 0) :
    exp (a * r) * (∫ x in Ioi (0 : ℝ), LerchHermite.rayKernel s a r x) =
      (-r : ℂ) ^ (s - 1) * upperIncompleteGamma (1 - s) ((-r : ℂ) * a) := by
  let c : ℝ := -r
  have hc : 0 < c := neg_pos.mpr hr
  have hc0 : (c : ℂ) ≠ 0 := ofReal_ne_zero.mpr hc.ne'
  have hz : (c : ℂ) * a ∈ slitPlane := Or.inl (by simp; exact mul_pos hc ha)
  let k : ℝ → ℂ := fun t => ((c : ℂ) * a + t) ^ (-s) * exp (-((c : ℂ) * a + t))
  have hcomp (x : ℝ) (hx : x ∈ Ioi (0 : ℝ)) :
      k (c * x) = (c : ℂ) ^ (-s) * exp (a * r) * LerchHermite.rayKernel s a r x := by
    have hx0 : 0 < x := hx
    have ha0 : a + x ≠ 0 := by intro h; have := congrArg re h; simp at this; linarith
    dsimp only [k, LerchHermite.rayKernel]
    rw [show (c : ℂ) * a + (c * x : ℝ) = (c : ℂ) * (a + x) by push_cast; ring,
      ofReal_mul_cpow_of_pos hc ha0, show -((c : ℂ) * (a + x)) =
        a * (r : ℂ) + (r : ℂ) * x by dsimp [c]; push_cast; ring, exp_add]
    ring
  have hki : IntegrableOn (fun x => k (c * x)) (Ioi 0) := by
    apply IntegrableOn.congr_fun
      ((LerchHermite.integrableOn_rayKernel_of_re_neg (w := (r : ℂ)) ha
        (by simpa using hr) s).const_mul ((c : ℂ) ^ (-s) * exp (a * r)))
      (fun x hx => (hcomp x hx).symm) measurableSet_Ioi
  have hk : IntegrableOn k (Ioi 0) := by
    simpa only [mul_zero] using (integrableOn_Ioi_comp_mul_left_iff k 0 hc).mp hki
  have hU : (∫ t in Ioi (0 : ℝ), k t) = upperIncompleteGamma (1 - s) ((c : ℂ) * a) := by
    have ht := upperIncompleteGamma_horizontal_integral (1 - s) hz
    change Tendsto (fun R : ℝ => ∫ t in (0 : ℝ)..R,
      ((c : ℂ) * a + t) ^ ((1 - s) - 1) * exp (-((c : ℂ) * a + t)))
      atTop (𝓝 (upperIncompleteGamma (1 - s) ((c : ℂ) * a))) at ht
    simp only [show (1 - s) - 1 = -s by ring] at ht
    exact tendsto_nhds_unique (intervalIntegral_tendsto_integral_Ioi 0 hk tendsto_id) ht
  have hscale := integral_comp_mul_left_Ioi' k 0 hc
  rw [setIntegral_congr_fun measurableSet_Ioi hcomp, integral_const_mul] at hscale
  simp only [mul_zero, Complex.real_smul] at hscale
  rw [hU] at hscale
  have hcprod : (c : ℂ) ^ (s - 1) * c * (c : ℂ) ^ (-s) = 1 := by
    calc
      _ = (c : ℂ) ^ (s - 1) * (c : ℂ) ^ (1 : ℂ) * (c : ℂ) ^ (-s) := by
        rw [cpow_one]
      _ = (c : ℂ) ^ ((s - 1) + 1 + -s) := by
        rw [← cpow_add _ _ hc0, ← cpow_add _ _ hc0]
      _ = 1 := by rw [show (s - 1) + 1 + -s = 0 by ring, cpow_zero]
  simp only [← ofReal_neg]
  change exp (a * r) * _ = (c : ℂ) ^ (s - 1) * _
  rw [← hscale]
  calc
    _ = ((c : ℂ) ^ (s - 1) * c * (c : ℂ) ^ (-s)) *
        (exp (a * r) * ∫ x in Ioi (0 : ℝ), LerchHermite.rayKernel s a r x) := by
      rw [hcprod]
      ring
    _ = _ := by ring

/-- The lower incomplete-Gamma endpoint cancels the singular ray term. -/
theorem exp_mul_integral_rayKernel_eq_sub_endpoint {a s : ℂ} (ha : 0 < a.re)
    (hs : ∀ n : ℕ, s ≠ (n : ℂ) + 1) {r : ℝ} (hr : r < 0) :
    exp (a * r) * (∫ x in Ioi (0 : ℝ), LerchHermite.rayKernel s a r x) =
      Gamma (1 - s) * (-r : ℂ) ^ (s - 1) - endpoint s a r := by
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  have hc : 0 < -r := neg_pos.mpr hr
  have hc0 : (-r : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hs' : ∀ n : ℕ, 1 - s ≠ -(n : ℂ) := by
    intro n h
    apply hs n
    linear_combination -h
  have hG := lowerIncompleteGamma_add_upperIncompleteGamma hs' (mul_ne_zero hc0 ha0)
  have he : (-r : ℂ) ^ (s - 1) * lowerIncompleteGamma (1 - s) ((-r : ℂ) * a) =
      endpoint s a r := by
    rw [lowerIncompleteGamma_eq_regularized hs']
    have hpow : ((-r : ℂ) * a) ^ (1 - s) = (-r : ℂ) ^ (1 - s) * a ^ (1 - s) := by
      simpa only [ofReal_neg] using ofReal_mul_cpow_of_pos hc ha0 (1 - s)
    rw [hpow]
    have hcp : (-r : ℂ) ^ (s - 1) * (-r : ℂ) ^ (1 - s) = 1 := by
      rw [← cpow_add _ _ hc0, show (s - 1) + (1 - s) = 0 by ring, cpow_zero]
    have hz : -((-r : ℂ) * a) = a * (r : ℂ) := by ring
    rw [hz, show 1 - s + 1 = 2 - s by ring, endpoint]
    linear_combination Gamma (1 - s) * a ^ (1 - s) *
      regularizedHGFun {1 - s} {2 - s} (a * r) * hcp
  rw [exp_mul_integral_rayKernel_eq_upperIncompleteGamma ha s hr]
  linear_combination (-r : ℂ) ^ (s - 1) * hG - he

/-- The holomorphic regularization agrees with Lerch's function for negative real logarithms. -/
theorem regularized_eq_of_real {a s : ℂ} (ha : 0 < a.re)
    (hs : ∀ n : ℕ, s ≠ (n : ℂ) + 1) {r : ℝ} (hr : r < 0) :
    regularized s a r = exp (a * r) * lerchPhi (exp (r : ℂ)) s a -
      Gamma (1 - s) * (-r : ℂ) ^ (s - 1) := by
  rw [LerchHermite.lerchPhi_exp_eq_of_real ha hr s, regularized]
  linear_combination -(exp_mul_integral_rayKernel_eq_sub_endpoint ha hs hr)

/-- Within one full period, exponentiation takes the logarithmic slit into the Lerch cut plane. -/
theorem exp_mem_slitOne {w : ℂ} (hw : |w.im| < 2 * π) (hw' : -w ∈ slitPlane) :
    exp w ∈ slitOne := by
  by_contra h
  simp only [slitOne, mem_ofPred_eq, not_or, not_not, not_lt] at h
  have hp : 0 < (exp w).re := lt_of_lt_of_le zero_lt_one h.2
  have he : exp w = exp ((Real.log (exp w).re : ℝ) : ℂ) := by
    rw [← ofReal_exp, Real.exp_log hp]
    exact Complex.ext (by simp) (by simpa using h.1)
  obtain ⟨n, hn⟩ := exp_eq_exp_iff_exists_int.mp he
  have hnIm := congrArg im hn
  norm_num at hnIm
  have hn0 : n = 0 := by
    have habs := abs_lt.mp hw
    have hπ : 0 < 2 * π := by positivity
    have hlo : (-1 : ℝ) < (n : ℝ) := (mul_lt_mul_iff_of_pos_right hπ).mp (by nlinarith)
    have hhi : (n : ℝ) < 1 := (mul_lt_mul_iff_of_pos_right hπ).mp (by nlinarith)
    have hlo' : (-1 : ℤ) < n := by exact_mod_cast hlo
    have hhi' : n < (1 : ℤ) := by exact_mod_cast hhi
    omega
  simp only [hn0, Int.cast_zero, zero_mul, add_zero] at hn
  rw [hn] at hw'
  have hnlog : 0 ≤ Real.log (exp w).re := Real.log_nonneg h.2
  rcases hw' with hR | hI
  · simp only [neg_re, ofReal_re] at hR
    linarith
  · simp at hI

/-- The regularization agrees with the principal Lerch function on the logarithmic slit strip. -/
theorem regularized_eq {a s w : ℂ} (ha : 0 < a.re)
    (hs : ∀ n : ℕ, s ≠ (n : ℂ) + 1) (hw : |w.im| < 2 * π) (hw' : -w ∈ slitPlane) :
    regularized s a w = exp (a * w) * lerchPhi (exp w) s a -
      Gamma (1 - s) * (-w) ^ (s - 1) := by
  let S : Set ℂ := {v : ℂ | -(2 * π) < v.im ∧ v.im < 2 * π}
  let U : Set ℂ := S ∩ (-slitPlane)
  have hS : IsOpen S :=
    (isOpen_lt continuous_const continuous_im).inter (isOpen_lt continuous_im continuous_const)
  have hU : IsOpen U := hS.inter isOpen_slitPlane.neg
  have hSc : Convex ℝ S :=
    (convex_halfSpace_im_gt (-(2 * π))).inter (convex_halfSpace_im_lt (2 * π))
  have hm : (-1 : ℂ) ∈ S := by
    change -(2 * π) < (-1 : ℂ).im ∧ (-1 : ℂ).im < 2 * π
    simp only [neg_im, one_im, neg_zero]
    constructor <;> nlinarith [Real.pi_pos]
  have hmU : (-1 : ℂ) ∈ U := ⟨hm, by simp⟩
  have hstar : StarConvex ℝ (-1 : ℂ) U :=
    (hSc.starConvex hm).inter starConvex_one_slitPlane.neg
  have hf : DifferentiableOn ℂ (regularized s a) U := by
    intro v hv
    exact (hasDerivAt_regularized ha (by simpa using hs 0)
      (abs_lt.mpr hv.1)).differentiableAt.differentiableWithinAt
  have hg : DifferentiableOn ℂ (fun v => exp (a * v) * lerchPhi (exp v) s a -
      Gamma (1 - s) * (-v) ^ (s - 1)) U := by
    intro v hv
    have hv' : -v ∈ slitPlane := by simpa using hv.2
    have hPhi := (analyticOnNhd_lerchPhi (lerchParamAdmissible_of_re_pos ha s) _
      (exp_mem_slitOne (abs_lt.mpr hv.1) hv')).differentiableAt
    have hP := ((hasDerivAt_id v).neg.cpow_const (c := s - 1) hv').differentiableAt
    exact (((by fun_prop : DifferentiableAt ℂ (fun t : ℂ => exp (a * t)) v).mul
      (hPhi.comp v differentiableAt_id.cexp)).sub
        (hP.const_mul _)).differentiableWithinAt
  refine (hf.analyticOnNhd hU).eqOn_of_preconnected_of_frequently_eq (hg.analyticOnNhd hU)
    (hstar.isPathConnected hmU).isConnected.isPreconnected hmU ?_ ⟨abs_lt.mp hw, by simpa⟩
  have hev : ∀ᶠ r : ℝ in 𝓝[≠] (-1),
      regularized s a r = exp (a * r) * lerchPhi (exp (r : ℂ)) s a -
        Gamma (1 - s) * (-(r : ℂ)) ^ (s - 1) := by
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (-1 : ℝ) < 0))] with r hr
    exact regularized_eq_of_real ha hs hr
  have ht : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[≠] (-1)) (𝓝[≠] ((-1 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin
      (fun r hr => Complex.ofReal_injective.ne hr)
  simpa only [ofReal_neg, ofReal_one] using
    (ht.frequently (p := fun v : ℂ => regularized s a v =
      exp (a * v) * lerchPhi (exp v) s a - Gamma (1 - s) * (-v) ^ (s - 1)) hev.frequently)

/-- The logarithmic series of Lerch's transcendent for right-half-plane parameters. -/
theorem hasSum_lerchPhi_log_of_re_pos {a s z : ℂ} (ha : 0 < a.re)
    (hs : ∀ n : ℕ, s ≠ (n : ℂ) + 1) (hz : z ∈ slitOne) (hz0 : z ≠ 0)
    (hlog : ‖log z‖ < 2 * π) :
    HasSum (fun n : ℕ => hurwitzZetaComplex (s - n) a * log z ^ n / n !)
      (z ^ a * lerchPhi z s a - Gamma (1 - s) * (-log z) ^ (s - 1)) := by
  have hw : -log z ∈ slitPlane := by
    by_cases hI : (log z).im = 0
    · have harg : arg z = 0 := by simpa only [log_im] using hI
      have hp := arg_eq_zero_iff.mp harg
      have hR : z.re < 1 := hz.resolve_left (by simpa using hp.2)
      have heq : z = (z.re : ℂ) := Complex.ext (by simp) (by simpa using hp.2)
      have hn : ‖z‖ < 1 := by
        rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp.1]
        exact hR
      exact Or.inl (by
        rw [neg_re, log_re]
        exact neg_pos.mpr (Real.log_neg (norm_pos_iff.mpr hz0) hn))
    · exact Or.inr (by simpa only [neg_im, neg_ne_zero] using hI)
  have h := hasSum_regularized ha hs hlog
  rw [regularized_eq ha hs ((abs_im_le_norm (log z)).trans_lt hlog) hw,
    exp_log hz0] at h
  simpa only [cpow_def_of_ne_zero hz0, mul_comm a (log z)] using h

end DLMF.Zeta.LerchLogarithmic
