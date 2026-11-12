/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.Associated.ConjugationAndValues
public import DLMFMathlib.Analysis.Integral.HyperbolicComparison

/-!
# The hyperbolic associated Legendre equation

The substitution `x = coth u` transforms the associated Legendre equation into
`y'' = (μ² + ν(ν+1)/sinh² u)y`. For negative order `-μ`, with `μ > 0`, the solution
`P^{-μ}_ν(coth u)` has exponential normalization `1/Γ(1+μ)` at infinity, and both
it and its first derivative tend to zero. These facts supply the recessive boundary
condition in DLMF 14.15.2.
-/

open Complex Filter Set DLMF.Hypergeometric
open scoped Real Topology
@[expose] public noncomputable section

namespace DLMF.Legendre.HyperbolicAssociatedP
/-- The associated Legendre solution pulled back by `x = coth u`, for positive `u`. -/
noncomputable def value (ν : ℂ) (μ u : ℝ) : ℂ :=
  associatedP ν (-(μ : ℂ)) (Real.cosh u / Real.sinh u)
/-- The derivative of the associated Legendre solution in the hyperbolic coordinate. -/
noncomputable def firstDerivative (ν : ℂ) (μ u : ℝ) : ℂ :=
  (1 - (Real.cosh u / Real.sinh u : ℂ)^2) *
    deriv (associatedP ν (-(μ : ℂ))) (Real.cosh u / Real.sinh u)
/-- The first derivative of the pulled-back associated Legendre solution. -/
lemma hasDerivAt_value (ν : ℂ) (μ : ℝ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (value ν μ) (firstDerivative ν μ u) u := by
  have hf := (associatedP_analytic ν (-(μ : ℂ)) _
    (Complex.cosh_div_sinh_sub_one_mem_slitPlane hu)).differentiableAt.hasDerivAt
  have hc := (Real.hasDerivAt_cosh_div_sinh hu).ofReal_comp
  simp only [ofReal_div, ofReal_sub, ofReal_one, ofReal_pow] at hc
  convert hf.comp u hc using 1
  · rfl
  · simp only [firstDerivative]
    ring
/-- The pulled-back solution satisfies the hyperbolic normal form of Legendre's equation. -/
lemma hasDerivAt_firstDerivative (ν : ℂ) (μ : ℝ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (firstDerivative ν μ)
      (((μ : ℂ)^2 + ν*(ν+1)/(Real.sinh u : ℂ)^2) * value ν μ u) u := by
  have hz := Complex.cosh_div_sinh_sub_one_mem_slitPlane hu
  have ha := associatedP_analytic ν (-(μ : ℂ))
  have hdd := (ha.deriv _ hz).differentiableAt.hasDerivAt
  have hc := (Real.hasDerivAt_cosh_div_sinh hu).ofReal_comp
  simp only [ofReal_div, ofReal_sub, ofReal_one, ofReal_pow] at hc
  have hd := ((hc.pow 2).const_sub 1).mul (hdd.comp u hc)
  convert hd using 1
  · rfl
  · have he := associatedP_ode ν (-(μ : ℂ)) hz
    have hs : (Real.sinh u : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sinh_pos_iff.mpr hu).ne'
    have hq : 1-(Real.cosh u / Real.sinh u : ℂ)^2 = -1/(Real.sinh u : ℂ)^2 := by
      have hh : (Real.cosh u : ℂ)^2 - (Real.sinh u : ℂ)^2 = 1 := by
        exact_mod_cast Real.cosh_sq_sub_sinh_sq u
      field_simp
      linear_combination -hh
    have hq0 : 1-(Real.cosh u / Real.sinh u : ℂ)^2 ≠ 0 := by
      rw [hq]; exact div_ne_zero (by norm_num) (pow_ne_zero _ hs)
    simp only [iteratedDeriv_succ, iteratedDeriv_zero] at he
    simp only [Pi.pow_apply, Function.comp_apply, Nat.cast_ofNat, value]
    rw [hq] at he ⊢
    simp only [neg_sq] at he
    field_simp [hs] at he ⊢
    linear_combination (norm := (ring_nf; field_simp [hs]; ring)) he
/-- The hyperbolic pullback factors into an exponential and a regularized Gauss function. -/
lemma value_eq_exp_mul (ν : ℂ) (μ : ℝ) {u : ℝ} (hu : 0 < u) :
    value ν μ u = exp (-(μ : ℂ)*u) *
      regularizedGaussHypergeometric (ν+1) (-ν) (1+μ)
        ((1-(Real.cosh u / Real.sinh u : ℂ))/2) := by
  unfold value associatedP
  rw [Complex.exp_mul_log_cosh_div_sinh_ratio (-(μ : ℂ)) hu]
  simp only [sub_neg_eq_add]
/-- The exponentially normalized derivative in terms of two Gauss functions. -/
lemma exp_mul_firstDerivative (ν : ℂ) (μ : ℝ) {u : ℝ} (hu : 0 < u) :
    exp ((μ : ℂ)*u) * firstDerivative ν μ u =
      -(μ : ℂ) * regularizedGaussHypergeometric (ν+1) (-ν) (1+μ)
        ((1-(Real.cosh u / Real.sinh u : ℂ))/2) -
      (ν+1)*(-ν)/2 * (1-(Real.cosh u / Real.sinh u : ℂ)^2) *
        regularizedGaussHypergeometric (ν+2) (-ν+1) (2+μ)
          ((1-(Real.cosh u / Real.sinh u : ℂ))/2) := by
  have hh := (hasDerivAt_associatedP_aux (ν+1) (-ν) (1-(-(μ : ℂ))) (-(μ : ℂ))
    (Complex.cosh_div_sinh_sub_one_mem_slitPlane hu)).deriv
  change deriv (associatedP ν (-(μ : ℂ))) (Real.cosh u/Real.sinh u) = _ at hh
  simp only [sub_neg_eq_add] at hh
  unfold firstDerivative
  rw [hh, Complex.exp_mul_log_cosh_div_sinh_ratio (-(μ : ℂ)) hu]
  have hc : 1-(Real.cosh u / Real.sinh u : ℂ)^2 ≠ 0 := by
    have hh : 1-(Real.cosh u/Real.sinh u)^2 < 0 := by
      nlinarith [Real.one_lt_cosh_div_sinh hu]
    simpa only [ofReal_sub, ofReal_one, ofReal_pow, ofReal_div] using
      (ofReal_ne_zero.mpr (ne_of_lt hh))
  have hex : exp ((μ : ℂ)*u) * exp (-(μ : ℂ)*u) = 1 := by
    rw [← exp_add]; simp [neg_mul]
  have hp1 : ν+1+1 = ν+2 := by ring
  have hp2 : (1+(μ : ℂ))+1 = 2+μ := by ring
  rw [hp1, hp2]
  generalize ht : (Real.cosh u : ℂ)/(Real.sinh u : ℂ) = t at *
  simp only [neg_mul] at hex ⊢
  linear_combination (norm := (field_simp [hc]; ring))
    (-(μ : ℂ)*regularizedGaussHypergeometric (ν+1) (-ν) (1+μ)
      ((1-t)/2) - (ν+1)*(-ν)/2 * (1-t^2) *
        regularizedGaussHypergeometric (ν+2) (-ν+1) (2+μ)
          ((1-t)/2)) * hex
/-- The normalized Legendre solution tends to the reciprocal Gamma factor. -/
lemma tendsto_exp_mul_value (ν : ℂ) {μ : ℝ} (hμ : 0 < μ) :
    Tendsto (fun u : ℝ => exp ((μ : ℂ)*u) * value ν μ u) atTop
      (𝓝 (1 / Gamma (1+μ))) := by
  have hw : Tendsto (fun u : ℝ => (1-(Real.cosh u / Real.sinh u : ℂ))/2)
      atTop (𝓝 0) := by

    have hc := continuous_ofReal.tendsto 1 |>.comp Real.tendsto_cosh_div_sinh_atTop
    have h := (tendsto_const_nhds (x := (1 : ℂ)) (f := (atTop : Filter ℝ))).sub hc
    simpa using h.div_const (2 : ℂ)
  have hr : ∀ k : ℕ, (1+(μ : ℂ)) ≠ -(k : ℂ) := by
    intro k hk
    have he := congrArg re hk
    simp only [add_re, one_re, ofReal_re, neg_re, natCast_re] at he
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have ht := (analyticAt_regularizedGaussHypergeometric
    (ν+1) (-ν) (1+μ) zero_mem_cutPlane).continuousAt.tendsto
      |>.comp hw
  rw [regularizedGaussHypergeometric_zero_of_regular hr] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
  rw [value_eq_exp_mul ν μ hu, ← mul_assoc, ← exp_add]
  simp [neg_mul]
/-- The normalized first derivative tends to its reciprocal-Gamma coefficient. -/
lemma tendsto_exp_mul_firstDerivative (ν : ℂ) {μ : ℝ} (hμ : 0 < μ) :
    Tendsto (fun u : ℝ => exp ((μ : ℂ)*u) * firstDerivative ν μ u) atTop
      (𝓝 (-(μ : ℂ) / Gamma (1+μ))) := by
  have hw : Tendsto (fun u : ℝ => (1-(Real.cosh u / Real.sinh u : ℂ))/2)
      atTop (𝓝 0) := by

    have hc := continuous_ofReal.tendsto 1 |>.comp Real.tendsto_cosh_div_sinh_atTop
    have h := (tendsto_const_nhds (x := (1 : ℂ)) (f := (atTop : Filter ℝ))).sub hc
    simpa using h.div_const (2 : ℂ)
  have hr : ∀ k : ℕ, (1+(μ : ℂ)) ≠ -(k : ℂ) := by
    intro k hk
    have he := congrArg re hk
    simp only [add_re, one_re, ofReal_re, neg_re, natCast_re] at he
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hF := (analyticAt_regularizedGaussHypergeometric
    (ν+1) (-ν) (1+μ) zero_mem_cutPlane).continuousAt.tendsto
      |>.comp hw
  rw [regularizedGaussHypergeometric_zero_of_regular hr] at hF
  have hG := (analyticAt_regularizedGaussHypergeometric
    (ν+2) (-ν+1) (2+μ) zero_mem_cutPlane).continuousAt.tendsto
      |>.comp hw
  have hc := continuous_ofReal.tendsto 1 |>.comp Real.tendsto_cosh_div_sinh_atTop
  have hq := (tendsto_const_nhds (x := (1 : ℂ)) (f := (atTop : Filter ℝ))).sub (hc.pow 2)
  have ht := hF.const_mul (-(μ : ℂ)) |>.sub
    ((hq.const_mul ((ν+1)*(-ν)/2)).mul hG)
  simp only [ofReal_one, one_pow, sub_self, mul_zero, zero_mul, sub_zero, mul_one_div] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
  simpa only [Function.comp_apply, ofReal_div] using (exp_mul_firstDerivative ν μ hu).symm
/-- The pulled-back Legendre solution decays for positive order magnitude. -/
lemma tendsto_value_zero (ν : ℂ) {μ : ℝ} (hμ : 0 < μ) :
    Tendsto (value ν μ) atTop (𝓝 0) := by
  have hE : Tendsto (fun u : ℝ => exp (-(μ : ℂ)*u)) atTop (𝓝 0) := by

    have ht := continuous_ofReal.tendsto 0 |>.comp
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hμ))
    simpa only [Function.comp_def, id_eq, ofReal_exp, ofReal_neg, ofReal_mul, neg_mul,
      ofReal_zero] using ht
  have ht := hE.mul (tendsto_exp_mul_value ν hμ)
  simp only [zero_mul] at ht
  convert ht using 1
  funext u
  rw [← mul_assoc, ← exp_add]
  simp [neg_mul]
/-- The first derivative of the pulled-back Legendre solution decays. -/
lemma tendsto_firstDerivative_zero (ν : ℂ) {μ : ℝ} (hμ : 0 < μ) :
    Tendsto (firstDerivative ν μ) atTop (𝓝 0) := by
  have hE : Tendsto (fun u : ℝ => exp (-(μ : ℂ)*u)) atTop (𝓝 0) := by

    have ht := continuous_ofReal.tendsto 0 |>.comp
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hμ))
    simpa only [Function.comp_def, id_eq, ofReal_exp, ofReal_neg, ofReal_mul, neg_mul,
      ofReal_zero] using ht
  have ht := hE.mul (tendsto_exp_mul_firstDerivative ν hμ)
  simp only [zero_mul] at ht
  convert ht using 1
  funext u
  rw [← mul_assoc, ← exp_add]
  simp [neg_mul]
end DLMF.Legendre.HyperbolicAssociatedP
