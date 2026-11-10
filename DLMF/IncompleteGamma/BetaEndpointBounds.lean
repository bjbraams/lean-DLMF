/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.IncompleteGamma.BetaEndpointData
public import DLMFMathlib.Analysis.Complex.IteratedDeriv
public import DLMFMathlib.Analysis.Complex.Sector
public import DLMFMathlib.Analysis.SpecialFunctions.Pow.Decay
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Calculus.Taylor
public import DLMFMathlib.Analysis.SpecialFunctions.ImproperIntegralsExtra

/-!
# Uniform endpoint estimates for the incomplete Beta expansion

Estimates for the endpoint Laplace moments and for positive-order derivatives of the
analytic generating kernel in DLMF 8.18.3–8.18.6.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics
open scoped Real Topology Nat ContDiff
namespace DLMF.Confluent.IncompleteBetaUniform

open DLMF.Statistical

/-- The endpoint moment after translating the lower endpoint to zero. -/
def shiftedMoment (k : ℕ) (a b ξ : ℝ) : ℝ :=
  ∫ u : ℝ in Ioi 0, u^k*(ξ+u)^(b-1)*Real.exp (-a*u)

/-- Translation of the endpoint integrand to the positive half-line. -/
theorem translated_integrand (k : ℕ) (a b ξ u : ℝ) :
    (Ioi ξ).indicator (fun t : ℝ => (t-ξ)^k*t^(b-1)*Real.exp (-a*t)) (u+ξ) =
      Real.exp (-a*ξ) * (Ioi (0:ℝ)).indicator
        (fun t : ℝ => t^k*(ξ+t)^(b-1)*Real.exp (-a*t)) u := by
  by_cases hu : 0 < u
  · simp only [indicator_of_mem (show u+ξ ∈ Ioi ξ by change ξ < u+ξ; linarith),
      indicator_of_mem (show u ∈ Ioi (0:ℝ) from hu), add_sub_cancel_right]
    rw [show u+ξ = ξ+u by ring, show -a*(ξ+u) = -a*ξ + -a*u by ring, Real.exp_add]
    ring
  · simp only [indicator_of_notMem (show u+ξ ∉ Ioi ξ by change ¬ξ < u+ξ; linarith),
      indicator_of_notMem (show u ∉ Ioi (0:ℝ) from hu), mul_zero]

/-- The shifted moment integrand is integrable for positive shape and rate. -/
theorem integrable_shiftedMoment (k : ℕ) {a b ξ : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hξ : 0 ≤ ξ) : IntegrableOn
      (fun u : ℝ => u^k*(ξ+u)^(b-1)*Real.exp (-a*u)) (Ioi 0) := by
  have hi := (integrableOn_betaAux_integrand k ha hb hξ).integrable_indicator measurableSet_Ioi
  have hs := hi.comp_add_right ξ
  simp_rw [translated_integrand] at hs
  rw [← integrable_indicator_iff measurableSet_Ioi]
  exact (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (Real.exp_ne_zero _)) _).mp hs

/-- Translation identifies the endpoint auxiliary functions with the shifted moments. -/
theorem betaAuxF_eq_shiftedMoment (k : ℕ) (a b ξ : ℝ) :
    betaAuxF k a b ξ = ((Real.exp (-a*ξ)*shiftedMoment k a b ξ : ℝ) : ℂ)/Gamma b := by
  have hs : (∫ u : ℝ, (Ioi ξ).indicator
      (fun t : ℝ => (t-ξ)^k*t^(b-1)*Real.exp (-a*t)) (u+ξ)) =
      ∫ u : ℝ, (Ioi ξ).indicator
        (fun t : ℝ => (t-ξ)^k*t^(b-1)*Real.exp (-a*t)) u :=
    integral_add_right_eq_self _ ξ
  simp_rw [translated_integrand] at hs
  rw [integral_const_mul, integral_indicator measurableSet_Ioi] at hs
  rw [integral_indicator measurableSet_Ioi] at hs
  rw [betaAuxF, ← hs]
  rfl

/-- Endpoint moments are nonnegative. -/
theorem nonneg_shiftedMoment (k : ℕ) {a b ξ : ℝ} (hξ : 0 ≤ ξ) :
    0 ≤ shiftedMoment k a b ξ :=
  setIntegral_nonneg measurableSet_Ioi fun u hu => by
    have : 0 ≤ u := hu.le
    positivity

/-- A rate halving estimate for the translated zeroth moment. -/
theorem shiftedMoment_half_rate {a b ξ : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hξ : 0 ≤ ξ) : shiftedMoment 0 (a/2) b ξ ≤
      2*2^(max (b-1) 0) * shiftedMoment 0 a b ξ := by
  let f : ℝ → ℝ := fun u => (ξ+u)^(b-1)*Real.exp (-(a/2)*u)
  have hs := integral_comp_mul_left_Ioi f 0 (by norm_num : (0:ℝ) < 2)
  have hs' : shiftedMoment 0 (a/2) b ξ =
      2 * ∫ u in Ioi (0:ℝ), (ξ+2*u)^(b-1)*Real.exp (-a*u) := by
    simp only [mul_zero, smul_eq_mul] at hs
    simp only [shiftedMoment, pow_zero, one_mul]
    have he : (fun u : ℝ => f (2*u)) =
        fun u : ℝ => (ξ+2*u)^(b-1)*Real.exp (-a*u) := by
      funext u
      dsimp [f]
      congr 1
      congr 1
      ring
    rw [he] at hs
    linarith
  rw [hs', shiftedMoment]
  simp only [pow_zero, one_mul]
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
  rw [← integral_const_mul]
  have hbase := integrable_shiftedMoment 0 ha hb hξ
  simp only [pow_zero, one_mul] at hbase
  have hdom := hbase.const_mul (2^(max (b-1) 0))
  have hscaled : IntegrableOn
      (fun u : ℝ => (ξ+2*u)^(b-1)*Real.exp (-a*u)) (Ioi 0) := by
    refine hdom.mono' (ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi) ?_
    · intro u hu
      have hu0 : 0 < u := hu
      have hp : ContinuousAt (fun v : ℝ => (ξ+2*v)^(b-1)) u :=
        (by fun_prop : ContinuousAt (fun v : ℝ => ξ+2*v) u).rpow_const
          (Or.inl (by linarith : 0 < ξ+2*u).ne')
      exact (hp.mul (by fun_prop)).continuousWithinAt
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hu0 : 0 < u := hu
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_right (Real.rpow_add_two_mul_le (r := b-1) hξ hu) (Real.exp_pos _).le
  exact setIntegral_mono_on hscaled hdom measurableSet_Ioi fun u hu => by
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_right (Real.rpow_add_two_mul_le (r := b-1) hξ hu) (Real.exp_pos _).le

/-- Every translated endpoint moment is bounded by the zeroth moment times a power of the
inverse rate, uniformly in the endpoint. -/
theorem shiftedMoment_le (k : ℕ) {a b ξ : ℝ} (ha : 0 < a) (hb : 0 < b) (hξ : 0 ≤ ξ) :
    shiftedMoment k a b ξ ≤
      ((k.factorial:ℝ)*(2/a)^k) * (2*2^(max (b-1) 0)) * shiftedMoment 0 a b ξ := by
  have hk := integrable_shiftedMoment k ha hb hξ
  have hhalf := integrable_shiftedMoment 0 (half_pos ha) hb hξ
  simp only [pow_zero, one_mul] at hhalf
  have hK : 0 ≤ (k.factorial:ℝ)*(2/a)^k := by positivity
  have hle : shiftedMoment k a b ξ ≤
      ((k.factorial:ℝ)*(2/a)^k) * shiftedMoment 0 (a/2) b ξ := by
    rw [shiftedMoment, shiftedMoment]
    simp only [pow_zero, one_mul]
    rw [← integral_const_mul]
    refine setIntegral_mono_on hk (hhalf.const_mul _) measurableSet_Ioi fun u hu => ?_
    have hu0 : 0 < u := hu
    have hw : 0 ≤ (ξ+u)^(b-1) := Real.rpow_nonneg (by positivity) _
    have he := mul_le_mul_of_nonneg_left (Real.pow_mul_exp_neg_le_mul_exp_neg_half k ha hu0.le) hw
    convert he using 1 <;> ring
  calc shiftedMoment k a b ξ ≤
      ((k.factorial:ℝ)*(2/a)^k) * shiftedMoment 0 (a/2) b ξ := hle
    _ ≤ ((k.factorial:ℝ)*(2/a)^k) *
        ((2*2^(max (b-1) 0)) * shiftedMoment 0 a b ξ) :=
      mul_le_mul_of_nonneg_left (shiftedMoment_half_rate ha hb hξ) hK
    _ = _ := by ring

/-- Absolute values of the auxiliary functions are the positive normalized endpoint moments. -/
theorem norm_betaAuxF (k : ℕ) {a b ξ : ℝ} (hb : 0 < b) (hξ : 0 ≤ ξ) :
    ‖betaAuxF k a b ξ‖ =
      Real.exp (-a*ξ)*shiftedMoment k a b ξ / Real.Gamma b := by
  rw [betaAuxF_eq_shiftedMoment, Complex.Gamma_ofReal, ← ofReal_div, norm_real,
    Real.norm_eq_abs, abs_of_nonneg]
  exact div_nonneg (mul_nonneg (Real.exp_pos _).le (nonneg_shiftedMoment k hξ))
    (Real.Gamma_pos_of_pos hb).le

/-- The endpoint auxiliary moments satisfy a uniform inverse-rate bound. -/
theorem norm_betaAuxF_le (k : ℕ) {a b ξ : ℝ} (ha : 0 < a) (hb : 0 < b) (hξ : 0 ≤ ξ) :
    ‖betaAuxF k a b ξ‖ ≤
      ((k.factorial:ℝ)*(2/a)^k) * (2*2^(max (b-1) 0)) * ‖betaAuxF 0 a b ξ‖ := by
  rw [norm_betaAuxF k hb hξ, norm_betaAuxF 0 hb hξ]
  have h := mul_le_mul_of_nonneg_left (shiftedMoment_le k ha hb hξ)
    (Real.exp_pos (-a*ξ)).le
  have hd := div_le_div_of_nonneg_right h (Real.Gamma_pos_of_pos hb).le
  convert hd using 1 <;> ring

/-- A holomorphic extension of the generating kernel to the right half-plane. -/
def complexGeneratingKernel (b : ℝ) (z : ℂ) : ℂ :=
  z^((1-b:ℝ):ℂ) * (1-exp (-z))^((b-1:ℝ):ℂ)

/-- Holomorphy of the generating kernel on the open right half-plane. -/
theorem differentiableOn_complexGeneratingKernel (b : ℝ) :
    DifferentiableOn ℂ (complexGeneratingKernel b) {z : ℂ | 0 < z.re} := by
  intro z hz
  have h1 := differentiableAt_id.cpow_const (c := ((1-b:ℝ):ℂ)) (Or.inl hz)
  have hpos : 0 < (1-exp (-z)).re := by
    have he : ‖exp (-z)‖ < 1 := by
      rw [norm_exp, neg_re]
      exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos hz)
    have h := re_le_norm (exp (-z))
    simp only [sub_re, one_re]
    linarith
  have h2 := (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => 1-exp (-w)) z).cpow_const
    (c := ((b-1:ℝ):ℂ)) (Or.inl hpos)
  exact (h1.mul h2).differentiableWithinAt

/-- The complex extension agrees with the real endpoint generating kernel at positive arguments. -/
theorem complexGeneratingKernel_ofReal (b : ℝ) {x : ℝ} (hx : 0 < x) :
    complexGeneratingKernel b x = (Real.betaGeneratingKernel b x : ℂ) := by
  have he : 0 < 1-Real.exp (-x) := by
    have h := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hx)
    linarith
  rw [complexGeneratingKernel, ← ofReal_cpow hx.le, ← ofReal_neg, ← ofReal_exp,
    ← ofReal_one, ← ofReal_sub, ← ofReal_cpow he.le, ← ofReal_mul]
  congr 1
  rw [Real.betaGeneratingKernel, if_neg hx.ne', Real.div_rpow he.le hx.le,
    show 1-b = -(b-1) by ring, Real.rpow_neg hx.le]
  ring

/-- A dyadic-ball bound for the holomorphic extension at a large positive center. -/
theorem norm_complexGeneratingKernel_le (b : ℝ) {x : ℝ} (hx : 2 ≤ x) {z : ℂ}
    (hz : ‖z-(x:ℂ)‖ ≤ x/2) :
    ‖complexGeneratingKernel b z‖ ≤ 2^(2*|b-1|) * x^(1-b) := by
  have hx0 : 0 < x := by linarith
  have hr := abs_re_le_norm (z-(x:ℂ))
  simp only [sub_re, ofReal_re] at hr
  have hzre : x/2 ≤ z.re := by linarith [neg_abs_le (z.re-x)]
  have hnlo : x/2 ≤ ‖z‖ := hzre.trans (re_le_norm z)
  have hnhi : ‖z‖ ≤ 2*x := by
    have h := norm_add_le (z-(x:ℂ)) (x:ℂ)
    rw [sub_add_cancel, norm_real, Real.norm_of_nonneg hx0.le] at h
    linarith
  have he : ‖exp (-z)‖ ≤ 1/2 := by
    rw [norm_exp, neg_re]
    have h1 : 2 ≤ Real.exp z.re := by linarith [Real.add_one_le_exp z.re]
    have h2 : Real.exp z.re * Real.exp (-z.re) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (-z.re)]
  have helo : (1:ℝ)/2 ≤ ‖1-exp (-z)‖ := by
    have h := norm_sub_norm_le (1:ℂ) (exp (-z))
    rw [norm_one] at h
    linarith
  have hehi : ‖1-exp (-z)‖ ≤ 2 := by
    have h := norm_sub_le (1:ℂ) (exp (-z))
    rw [norm_one] at h
    linarith
  have h1 := Real.rpow_le_two_rpow_abs_mul (p := 1-b) hx0 hnlo hnhi
  have h2 := Real.rpow_le_two_rpow_abs_mul (x := 1) (p := b-1) one_pos helo
    (by simpa using hehi)
  simp only [Real.one_rpow, mul_one] at h2
  rw [complexGeneratingKernel, norm_mul, norm_cpow_real, norm_cpow_real]
  calc ‖z‖^(1-b)*‖1-exp (-z)‖^(b-1) ≤
      (2^|1-b| *x^(1-b))*2^|b-1| :=
        mul_le_mul h1 h2 (Real.rpow_nonneg (norm_nonneg _) _)
          (by positivity)
    _ = _ := by
      rw [show 1-b = -(b-1) by ring, abs_neg]
      rw [show 2^|b-1| *x^(-(b-1))*2^|b-1| =
        (2^|b-1| *2^|b-1|)*x^(-(b-1)) by ring, ← Real.rpow_add (by norm_num)]
      congr 1
      ring

/-- Positive-order derivatives of the complex generating kernel are bounded on the large
positive real axis by Cauchy's estimate. -/
theorem norm_iteratedDeriv_complexGeneratingKernel_le {b : ℝ} (hb : 0 < b)
    {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 2 ≤ x) :
    ‖iteratedDeriv n (complexGeneratingKernel b) (x:ℂ)‖ ≤
      (n.factorial:ℝ)*2^(2*|b-1|)*2^n := by
  have hx0 : 0 < x := by linarith
  have hR : 0 < x/2 := half_pos hx0
  have hsub : Metric.closedBall (x:ℂ) (x/2) ⊆ {z : ℂ | 0 < z.re} := by
    intro z hz
    have hr := abs_re_le_norm (z-(x:ℂ))
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    simp only [sub_re, ofReal_re] at hr
    have := neg_abs_le (z.re-x)
    change 0 < z.re
    linarith
  have hd := differentiableOn_complexGeneratingKernel b
  have hc : DiffContOnCl ℂ (complexGeneratingKernel b) (Metric.ball (x:ℂ) (x/2)) := by
    refine ⟨hd.mono (Metric.ball_subset_closedBall.trans hsub), ?_⟩
    rw [closure_ball _ hR.ne']
    exact hd.continuousOn.mono hsub
  have h := norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hR hc
    (fun z hz => norm_complexGeneratingKernel_le b hx
      (by rw [Metric.mem_sphere, dist_eq_norm] at hz; exact hz.le))
  have hp : x^(1-b) ≤ x^n := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ x)
    have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hr : x^(1-b)/(x/2)^n ≤ 2^n := by
    rw [div_pow, div_div_eq_mul_div]
    exact (div_le_iff₀ (pow_pos hx0 n)).mpr (by nlinarith [pow_pos (by norm_num : (0:ℝ)<2) n])
  calc ‖iteratedDeriv n (complexGeneratingKernel b) (x:ℂ)‖ ≤
      (n.factorial:ℝ)*(2^(2*|b-1|)*x^(1-b))/(x/2)^n := h
    _ = ((n.factorial:ℝ)*2^(2*|b-1|)) * (x^(1-b)/(x/2)^n) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hr (by positivity)

/-- Every derivative of positive order of the endpoint generating kernel is bounded on the
nonnegative real axis. -/
theorem exists_norm_iteratedDeriv_betaGeneratingKernel_le {b : ℝ} (hb : 0 < b)
    {n : ℕ} (hn : 1 ≤ n) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 ≤ x →
      ‖iteratedDeriv n (Real.betaGeneratingKernel b) x‖ ≤ C := by
  have hcd : ContDiff ℝ ∞ (Real.betaGeneratingKernel b) :=
    contDiff_iff_contDiffAt.mpr fun x => (analyticAt_betaGeneratingKernel b x).contDiffAt
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hcd.continuous_iteratedDeriv n (by simp)).continuousOn
  let K : ℝ := (n.factorial:ℝ)*2^(2*|b-1|)*2^n
  refine ⟨max M K, (by dsimp [K]; positivity), fun x hx => ?_⟩
  rcases le_or_gt x 2 with hx2 | hx2
  · exact (hM x ⟨hx, hx2⟩).trans (le_max_left _ _)
  · have hx0 : 0 < x := by linarith
    have he : Real.betaGeneratingKernel b =ᶠ[𝓝 x]
        fun y : ℝ => (complexGeneratingKernel b y).re := by
      filter_upwards [eventually_gt_nhds hx0] with y hy
      rw [complexGeneratingKernel_ofReal b hy, ofReal_re]
    have hd := differentiableOn_complexGeneratingKernel b
    have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
    rw [he.iteratedDeriv_eq n,
      Complex.iteratedDeriv_re_comp_ofReal_of_differentiableOn hU hd n hx0,
      Real.norm_eq_abs]
    exact ((abs_re_le_norm _).trans
      (norm_iteratedDeriv_complexGeneratingKernel_le hb hn hx2.le)).trans (le_max_right _ _)

/-- The substitution `u = exp(-t)` changes a Beta endpoint integral into a Laplace tail. -/
theorem integral_beta_exp_substitution (a b ξ : ℝ) :
    (∫ t : ℝ in Ioo 0 (Real.exp (-ξ)), t^(a-1)*(1-t)^(b-1)) =
      ∫ t : ℝ in Ioi ξ, Real.exp (-a*t)*(1-Real.exp (-t))^(b-1) := by
  rw [← integral_comp_exp_neg_Ioi (fun t : ℝ => t^(a-1)*(1-t)^(b-1)) ξ]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [smul_eq_mul, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp,
    ← mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- Multiplying the generating kernel by the Gamma weight cancels the real power of `t`. -/
theorem betaGeneratingKernel_weight_eq {a b t : ℝ} (ht : 0 < t) :
    t^(b-1)*Real.exp (-a*t)*Real.betaGeneratingKernel b t =
      Real.exp (-a*t)*(1-Real.exp (-t))^(b-1) := by
  have hq : 0 ≤ 1-Real.exp (-t) := by
    have := Real.exp_le_one_iff.mpr (by linarith : -t ≤ 0)
    linarith
  rw [Real.betaGeneratingKernel, ite_eq_right ht.ne', Real.div_rpow hq ht.le]
  have hp : t^(b-1) ≠ 0 := (Real.rpow_pos_of_pos ht _).ne'
  field_simp

/-- The Gamma-normalized incomplete Beta function is its defining real integral divided by
`Γ(b)` for positive real parameters and an argument in the unit interval. -/
theorem normalizedIncompleteBeta_eq_integral {a b x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hx : x ∈ Icc (0:ℝ) 1) :
    Gamma a/Gamma (a+b)*regularizedIncompleteBeta a b x =
      (((∫ t in (0:ℝ)..x, t^(a-1)*(1-t)^(b-1))/Real.Gamma b:ℝ):ℂ) := by
  rw [regularizedIncompleteBeta_ofReal (by simpa using ha) (by simpa using hb) hx,
    Real.regularizedIncompleteBeta_ofReal ha hb hx,
    TauCeti.regularizedIncompleteBeta_def_of_mem_Icc ha hb hx, ProbabilityTheory.beta]
  have hG : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  have hG' : Real.Gamma (a+b) ≠ 0 := (Real.Gamma_pos_of_pos (add_pos ha hb)).ne'
  have hH : Real.Gamma b ≠ 0 := (Real.Gamma_pos_of_pos hb).ne'
  rw [Complex.Gamma_ofReal, ← Complex.ofReal_add, Complex.Gamma_ofReal]
  push_cast
  have hid {u v w z : ℂ} (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0) :
      u/v*(z/(u*w/v))=z/w := by field_simp
  exact hid (Complex.ofReal_ne_zero.mpr hG) (Complex.ofReal_ne_zero.mpr hG')
    (Complex.ofReal_ne_zero.mpr hH)

/-- The Gamma-normalized incomplete Beta function is an endpoint Laplace integral. -/
theorem normalizedIncompleteBeta_eq_laplace_integral {a b x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hx : 0 < x) (hx1 : x ≤ 1) :
    Gamma a/Gamma (a+b)*regularizedIncompleteBeta a b x =
      ((∫ t : ℝ in Ioi (Real.betaXi x),
        t^(b-1)*Real.exp (-a*t)*Real.betaGeneratingKernel b t : ℝ) : ℂ)/Gamma b := by
  have hξ : 0 ≤ Real.betaXi x := neg_nonneg.mpr (Real.log_nonpos hx.le hx1)
  rw [normalizedIncompleteBeta_eq_integral ha hb ⟨hx.le,hx1⟩,
    intervalIntegral.integral_of_le hx.le, integral_Ioc_eq_integral_Ioo]
  have hex : Real.exp (-Real.betaXi x) = x := by simp [Real.betaXi, Real.exp_log hx]
  have hsub := integral_beta_exp_substitution a b (Real.betaXi x)
  rw [hex] at hsub
  rw [hsub, Complex.Gamma_ofReal, ← Complex.ofReal_div]
  have he : (∫ t : ℝ in Ioi (Real.betaXi x),
      Real.exp (-a*t)*(1-Real.exp (-t))^(b-1)) =
      ∫ t : ℝ in Ioi (Real.betaXi x),
        t^(b-1)*Real.exp (-a*t)*Real.betaGeneratingKernel b t := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    exact (betaGeneratingKernel_weight_eq (a := a) (b := b) (hξ.trans_lt ht)).symm
  rw [he]

/-- The Taylor remainder of positive order of the endpoint generating kernel has a bound
uniform in both nonnegative endpoints. -/
theorem exists_betaGeneratingKernel_taylor_bound {b : ℝ} (hb : 0 < b)
    {N : ℕ} (hN : 1 ≤ N) : ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ t : ℝ, 0 ≤ ξ → ξ ≤ t →
      |Real.betaGeneratingKernel b t - ∑ k ∈ Finset.range N,
        Real.betaGeneratingCoeff b ξ k*(t-ξ)^k| ≤ C*(t-ξ)^N := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  obtain ⟨C, hC, hbound⟩ := exists_norm_iteratedDeriv_betaGeneratingKernel_le hb
    (by omega : 1 ≤ n+1)
  refine ⟨C/(n.factorial:ℝ), by positivity, fun ξ t hξ hξt => ?_⟩
  have hcd : ContDiff ℝ (n+1) (Real.betaGeneratingKernel b) :=
    contDiff_iff_contDiffAt.mpr fun x => (analyticAt_betaGeneratingKernel b x).contDiffAt
  have hlt : ξ < t+1 := by linarith
  have huniq := uniqueDiffOn_Icc hlt
  have hp : taylorWithinEval (Real.betaGeneratingKernel b) n (Icc ξ (t+1)) ξ t =
      ∑ k ∈ Finset.range (n+1), Real.betaGeneratingCoeff b ξ k*(t-ξ)^k := by
    rw [taylor_within_apply]
    apply Finset.sum_congr rfl
    intro k hk
    rw [iteratedDerivWithin_eq_iteratedDeriv huniq
      (analyticAt_betaGeneratingKernel b ξ).contDiffAt ⟨le_rfl, hlt.le⟩]
    simp only [Real.betaGeneratingCoeff, smul_eq_mul]
    ring
  have h := taylor_mean_remainder_bound (f := Real.betaGeneratingKernel b)
    (a := ξ) (b := t+1) (x := t) (n := n) (C := C) hlt.le hcd.contDiffOn
    ⟨hξt, by linarith⟩ (fun y hy => by
      rw [iteratedDerivWithin_eq_iteratedDeriv huniq
        (analyticAt_betaGeneratingKernel b y).contDiffAt hy]
      exact hbound y (hξ.trans hy.1))
  rw [hp, Real.norm_eq_abs] at h
  convert h using 1
  simp only [Nat.succ_eq_add_one]
  ring

/-- Integrating a uniform Taylor remainder against the endpoint Gamma weight gives the
corresponding auxiliary moment as an error bound. -/
theorem norm_integral_generatingKernel_sub_sum_le {a b ξ C : ℝ} {N : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hξ : 0 ≤ ξ) (_hC : 0 ≤ C)
    (hTaylor : ∀ t : ℝ, ξ ≤ t →
      |Real.betaGeneratingKernel b t - ∑ k ∈ Finset.range N,
        Real.betaGeneratingCoeff b ξ k*(t-ξ)^k| ≤ C*(t-ξ)^N) :
    ‖(((∫ t : ℝ in Ioi ξ, t^(b-1)*Real.exp (-a*t)*Real.betaGeneratingKernel b t : ℝ):ℂ) /
        Gamma b - ∑ k ∈ Finset.range N, Real.betaGeneratingCoeff b ξ k * betaAuxF k a b ξ)‖ ≤
      C*‖betaAuxF N a b ξ‖ := by
  let w : ℝ → ℝ := fun t => t^(b-1)*Real.exp (-a*t)
  let P : ℝ → ℝ := fun t => ∑ k ∈ Finset.range N, Real.betaGeneratingCoeff b ξ k*(t-ξ)^k
  let R : ℝ → ℝ := fun t => w t*(Real.betaGeneratingKernel b t-P t)
  have hdom := (integrableOn_betaAux_integrand N ha hb hξ).const_mul C
  have hnorm : ∀ t ∈ Ioi ξ, ‖R t‖ ≤ C*((t-ξ)^N*t^(b-1)*Real.exp (-a*t)) := by
    intro t ht
    have ht0 : 0 < t := hξ.trans_lt ht
    have hw : 0 ≤ w t := by dsimp [w]; positivity
    dsimp only [R]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw]
    have h := mul_le_mul_of_nonneg_left (hTaylor t ht.le) hw
    convert h using 1 <;> dsimp [w, P] <;> ring
  have hR : IntegrableOn R (Ioi ξ) := by
    refine hdom.mono' (ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi) ?_
    · intro t ht
      have ht0 : 0 < t := hξ.trans_lt ht
      have hw : ContinuousAt w t := by
        dsimp [w]
        exact (Real.continuousAt_rpow_const _ _ (Or.inl ht0.ne')).mul (by fun_prop)
      have hf := (analyticAt_betaGeneratingKernel b t).continuousAt
      exact (hw.mul (hf.sub (by dsimp [P]; fun_prop))).continuousWithinAt
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hnorm t ht
  have hPsum : IntegrableOn
      (fun t : ℝ => ∑ k ∈ Finset.range N, Real.betaGeneratingCoeff b ξ k*
        ((t-ξ)^k*t^(b-1)*Real.exp (-a*t))) (Ioi ξ) :=
    integrable_finsetSum _ fun k hk =>
      (integrableOn_betaAux_integrand k ha hb hξ).const_mul _
  have hP : IntegrableOn (fun t => w t*P t) (Ioi ξ) := by
    refine hPsum.congr_fun (fun t ht => ?_) measurableSet_Ioi
    dsimp [w, P]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hF : IntegrableOn (fun t => w t*Real.betaGeneratingKernel b t) (Ioi ξ) := by
    refine (hR.add hP).congr_fun (fun t ht => ?_) measurableSet_Ioi
    dsimp [R]
    ring
  have hpoly : (∫ t in Ioi ξ, w t*P t) = ∑ k ∈ Finset.range N,
      Real.betaGeneratingCoeff b ξ k*
        ∫ t in Ioi ξ, (t-ξ)^k*t^(b-1)*Real.exp (-a*t) := by
    have he : (fun t => w t*P t) = fun t => ∑ k ∈ Finset.range N,
        Real.betaGeneratingCoeff b ξ k*((t-ξ)^k*t^(b-1)*Real.exp (-a*t)) := by
      funext t
      dsimp [w, P]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    rw [he, integral_finsetSum _ (fun k hk =>
      (integrableOn_betaAux_integrand k ha hb hξ).const_mul _)]
    simp_rw [integral_const_mul]
  have he : (((∫ t in Ioi ξ, w t*Real.betaGeneratingKernel b t : ℝ):ℂ)/Gamma b -
      ∑ k ∈ Finset.range N, Real.betaGeneratingCoeff b ξ k*betaAuxF k a b ξ) =
      ((∫ t in Ioi ξ, R t : ℝ):ℂ)/Gamma b := by
    have hRe : R = fun t => w t*Real.betaGeneratingKernel b t-w t*P t := by
      funext t
      dsimp [R]
      ring
    rw [hRe, integral_sub hF hP, hpoly, ofReal_sub, ofReal_sum, sub_div]
    congr 1
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k hk
    rw [betaAuxF, ofReal_mul]
    ring
  change ‖(((∫ t in Ioi ξ, w t*Real.betaGeneratingKernel b t : ℝ):ℂ)/Gamma b -
    ∑ k ∈ Finset.range N, Real.betaGeneratingCoeff b ξ k*betaAuxF k a b ξ)‖ ≤ _
  rw [he, betaAuxF, norm_div, norm_div, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs]
  have hI : 0 ≤ ∫ t in Ioi ξ, (t-ξ)^N*t^(b-1)*Real.exp (-a*t) :=
    setIntegral_nonneg measurableSet_Ioi fun t ht => by
      have ht0 : 0 < t := hξ.trans_lt ht
      have hdt : 0 ≤ t-ξ := by linarith [mem_Ioi.mp ht]
      positivity
  rw [abs_of_nonneg hI]
  have hle : |∫ t in Ioi ξ, R t| ≤ C*∫ t in Ioi ξ,
      (t-ξ)^N*t^(b-1)*Real.exp (-a*t) := by
    calc |∫ t in Ioi ξ, R t| = ‖∫ t in Ioi ξ, R t‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ t in Ioi ξ, ‖R t‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t in Ioi ξ, C*((t-ξ)^N*t^(b-1)*Real.exp (-a*t)) :=
        integral_mono_ae hR.norm hdom
          ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ hnorm))
      _ = _ := integral_const_mul _ _
  calc |∫ t in Ioi ξ, R t| / ‖Gamma (b:ℂ)‖ ≤
      (C*∫ t in Ioi ξ, (t-ξ)^N*t^(b-1)*Real.exp (-a*t)) / ‖Gamma (b:ℂ)‖ :=
        div_le_div_of_nonneg_right hle (norm_nonneg _)
    _ = _ := by ring

end DLMF.Confluent.IncompleteBetaUniform

namespace DLMF.Confluent

open DLMF.Statistical IncompleteBetaUniform

/-- The incomplete-Beta endpoint expansion has an error `O(a^(-N) F₀)`, uniformly for
`0 < x ≤ 1`, for every positive truncation order `N` and fixed `b > 0`. -/
@[dlmf 8.18.E3]
theorem incompleteBeta_large_a_uniform_of_pos_order {b : ℝ} (hb : 0 < b) {N : ℕ}
    (hN : 1 ≤ N) :
    IsBigO (comap Prod.fst atTop ⊓ 𝓟 {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.2 ≤ 1})
      (fun p => Gamma p.1/Gamma (p.1+b)*regularizedIncompleteBeta p.1 b p.2-
        ∑ k ∈ Finset.range N, Real.betaGeneratingCoeff b (Real.betaXi p.2) k*
          betaAuxF k p.1 b (Real.betaXi p.2))
      (fun p => (p.1:ℂ)^(-(N:ℤ))*betaAuxF 0 p.1 b (Real.betaXi p.2)) := by
  obtain ⟨C, hC, hTaylor⟩ := exists_betaGeneratingKernel_taylor_bound hb hN
  let A : ℝ := (N.factorial:ℝ)*2^N*(2*2^(max (b-1) 0))
  refine IsBigO.of_bound (C*A) ?_
  have hs : ∀ᶠ p : ℝ × ℝ in
      comap Prod.fst atTop ⊓ 𝓟 {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.2 ≤ 1},
      0 < p.1 ∧ 0 < p.2 ∧ p.2 ≤ 1 :=
    eventually_inf_principal.mpr (Eventually.of_forall fun p hp => hp)
  filter_upwards [hs] with p hp
  obtain ⟨ha, hx, hx1⟩ := hp
  have hξ : 0 ≤ Real.betaXi p.2 := neg_nonneg.mpr (Real.log_nonpos hx.le hx1)
  have h1 := norm_integral_generatingKernel_sub_sum_le ha hb hξ hC
    (fun t ht => hTaylor (Real.betaXi p.2) t hξ ht)
  rw [← normalizedIncompleteBeta_eq_laplace_integral ha hb hx hx1] at h1
  have hm := norm_betaAuxF_le N ha hb hξ
  have hd : ‖(p.1:ℂ)^(-(N:ℤ))*betaAuxF 0 p.1 b (Real.betaXi p.2)‖ =
      (p.1^N)⁻¹*‖betaAuxF 0 p.1 b (Real.betaXi p.2)‖ := by
    rw [norm_mul, norm_zpow, Complex.norm_real, Real.norm_of_nonneg ha.le,
      zpow_neg, zpow_natCast]
  rw [hd]
  calc ‖Gamma (p.1:ℂ)/Gamma (p.1+b)*regularizedIncompleteBeta p.1 b p.2-
        ∑ k ∈ Finset.range N, Real.betaGeneratingCoeff b (Real.betaXi p.2) k*
          betaAuxF k p.1 b (Real.betaXi p.2)‖ ≤
      C*‖betaAuxF N p.1 b (Real.betaXi p.2)‖ := h1
    _ ≤ C*(((N.factorial:ℝ)*(2/p.1)^N)*(2*2^(max (b-1) 0))*
        ‖betaAuxF 0 p.1 b (Real.betaXi p.2)‖) :=
      mul_le_mul_of_nonneg_left hm hC
    _ = _ := by
      dsimp [A]
      rw [div_pow, div_eq_mul_inv]
      ring

end DLMF.Confluent
