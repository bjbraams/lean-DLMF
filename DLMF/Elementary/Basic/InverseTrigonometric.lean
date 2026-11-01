/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Elementary.Basic.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Principal inverse trigonometric functions

This file defines the principal inverse trigonometric functions of a complex variable and their
open cut planes (DLMF §4.23(ii)), and proves their analyticity, their agreement with the real
inverse functions on `[-1, 1]`, and the symmetry and complement relations of DLMF §4.23(iii).

## Main definitions

* `arcsinPrincipal`, `arccosPrincipal`, `arccscPrincipal`, `arcsecPrincipal`, `arccotPrincipal`:
  principal inverse functions (DLMF 4.23.7–4.23.9, 4.23.16, 4.23.19).
* `arcsinCutPlane`, `arctanCutPlane`, `arccscCutPlane`, `arccotCutPlane`: the open cut planes.

## Main results

* `trig_hasDerivAt_arcsin`, `trig_hasDerivAt_arctan`: derivatives on the cut planes.
* `analytic_arcsin_principal`, `analytic_arccos_principal`, `analytic_arctan_principal`,
  `analytic_arccsc_principal`, `analytic_arcsec_principal`, `analytic_arccot_principal`:
  analyticity (DLMF §4.23(ii)).
* `inverse_principal_real`: agreement with `Real.arcsin` and `Real.arccos` on `[-1, 1]`.
* `arcsinPrincipal_zero`, `arccosPrincipal_zero`: values at `0`.
* `arcsin_principal_neg`, `arccos_principal_neg`, `arctan_principal_neg`,
  `arccsc_principal_neg`, `arcsec_principal_neg`, `arccot_principal_neg`: DLMF 4.23.10–4.23.15.
* `arcsec_principal_complement`, `arccot_principal_complement`: DLMF 4.23.17–4.23.18.

## Implementation notes

The principal arctangent is Mathlib's `Complex.arctan`. Complex inverse functions use principal
logarithms and square roots off their cuts. The multivalued inverses, path integrals, cut values
and logarithmic forms are in `DLMF.Elementary.Trigonometric.InverseBranches`.
-/

@[expose] public noncomputable section

open Complex Filter Set

open scoped Real Topology

namespace DLMF.Elementary

/-- Principal complex arcsine off its cuts; its assigned cut values select one bank only. -/
@[dlmf 4.23.E19]
def arcsinPrincipal (z : ℂ) : ℂ := -I*Complex.log (Complex.sqrt (1-z^2)+I*z)

/-- Principal complex arccosine off its cuts. -/
@[dlmf 4.23.E16]
def arccosPrincipal (z : ℂ) : ℂ := π/2-arcsinPrincipal z

/-- Principal inverse cosecant, used on its cut domain with z nonzero. -/
@[dlmf 4.23.E7]
def arccscPrincipal (z : ℂ) : ℂ := arcsinPrincipal z⁻¹

/-- Principal inverse secant, used on its cut domain with z nonzero. -/
@[dlmf 4.23.E8]
def arcsecPrincipal (z : ℂ) : ℂ := arccosPrincipal z⁻¹

/-- Principal inverse cotangent off its central imaginary cut; its totalized value at zero is not a
bank value. -/
@[dlmf 4.23.E9]
def arccotPrincipal (z : ℂ) : ℂ := Complex.arctan z⁻¹

/-- The open arcsine/arccosine cut plane, excluding the two branch points. -/
def arcsinCutPlane : Set ℂ := {z | z.im≠0 ∨ |z.re|<1}

/-- The open arctangent cut plane, excluding ±i. -/
def arctanCutPlane : Set ℂ := {z | z.re≠0 ∨ |z.im|<1}

/-- The reciprocal cut plane for inverse secant and cosecant. -/
def arccscCutPlane : Set ℂ := {z | z≠0 ∧ z⁻¹∈arcsinCutPlane}

/-- The central imaginary cut is deleted for inverse cotangent. -/
def arccotCutPlane : Set ℂ := {z | z≠0 ∧ z⁻¹∈arctanCutPlane}

/-- Formula under the stated hypotheses: `(1+z*I)/(1-z*I)∈Complex.slitPlane`. -/
lemma trig_arctan_quotient_slit {z:ℂ} (hz:z∈arctanCutPlane) :
    (1+z*I)/(1-z*I)∈Complex.slitPlane := by
  have hre : ((1+z*I)/(1-z*I)).re=(1-z.im^2-z.re^2)/((1+z.im)^2+z.re^2) := by
    simp [Complex.div_re,Complex.normSq]
    ring
  have him : ((1+z*I)/(1-z*I)).im=(2*z.re)/((1+z.im)^2+z.re^2) := by
    simp [Complex.div_im,Complex.normSq]
    ring
  rw [Complex.mem_slitPlane_iff]
  by_cases hr:z.re≠0
  · right
    rw [him]
    have hD:0<(1+z.im)^2+z.re^2 := add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hr)
    exact div_ne_zero (mul_ne_zero two_ne_zero hr) hD.ne'
  · left
    have hr0:z.re=0 := not_ne_iff.mp hr
    have hi:|z.im|<1 := hz.resolve_left hr
    rw [hre,hr0]
    have hip:0<1+z.im := by linarith [(abs_lt.mp hi).1]
    apply div_pos
    · nlinarith [(abs_lt.mp hi).1,(abs_lt.mp hi).2]
    · positivity

/-- Nonvanishing under the stated hypotheses: `1+z*I≠0 ∧ 1-z*I≠0`. -/
private lemma trig_arctan_linear_ne {z:ℂ} (hz:z∈arctanCutPlane) :
    1+z*I≠0 ∧ 1-z*I≠0 := by
  have hgood: ¬(z.re=0 ∧ (z.im=1 ∨ z.im= -1)) := by
    rintro ⟨hr,hi⟩
    have h:|z.im|<1 := hz.resolve_left (not_ne_iff.mpr hr)
    rcases hi with hi|hi <;> simp [hi] at h
  constructor
  · intro h
    have hr:=congrArg Complex.re h
    have hi:=congrArg Complex.im h
    simp at hr hi
    exact hgood ⟨by linarith,Or.inl (by linarith)⟩
  · intro h
    have hr:=congrArg Complex.re h
    have hi:=congrArg Complex.im h
    simp at hr hi
    exact hgood ⟨by linarith,Or.inr (by linarith)⟩

/-- At `z`, the function `Complex.arctan` has derivative `((1+z^2)⁻¹)`. -/
lemma trig_hasDerivAt_arctan {z:ℂ} (hz:z∈arctanCutPlane) :
    HasDerivAt Complex.arctan ((1+z^2)⁻¹) z := by
  obtain ⟨hp,hm⟩:=trig_arctan_linear_ne hz
  have hd0 := (((hasDerivAt_id z).mul_const I).const_add 1).div
    (((hasDerivAt_id z).mul_const I).const_sub 1) hm
  have hd1 := (Complex.hasDerivAt_log (trig_arctan_quotient_slit hz)).comp z hd0
  have hd:=hd1.const_mul (-I/2)
  convert hd using 1
  · rfl
  · dsimp only [id]
    have hfac:(1+z*I)*(1-z*I)=1+z^2 := by
      linear_combination -z^2*Complex.I_sq
    rw [← hfac]
    field_simp [hp,hm]
    linear_combination 2*Complex.I_sq

/-- Formula under the stated hypotheses: `1+z^2∈Complex.slitPlane`. -/
lemma trig_one_add_sq_slit {z:ℂ} (hz:z∈arctanCutPlane) :
    1+z^2∈Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_cases hr:z.re=0
  · left
    have hi:|z.im|<1 := hz.resolve_left (not_ne_iff.mpr hr)
    simp [Complex.add_re,pow_two,Complex.mul_re,hr]
    nlinarith [(abs_lt.mp hi).1,(abs_lt.mp hi).2]
  · by_cases hi:z.im=0
    · left
      simp [Complex.add_re,pow_two,Complex.mul_re,hi]
      nlinarith [sq_nonneg z.re]
    · right
      simp [Complex.add_im,pow_two,Complex.mul_im]
      convert mul_ne_zero (mul_ne_zero two_ne_zero hr) hi using 1 <;> ring

/-- Identity under the stated parameter and domain assumptions: `(Complex.sqrt
(1-z^2)+I*z)*(Complex.sqrt (1-z^2)-I*z)=1`. -/
lemma trig_arcsin_product (z:ℂ) :
    (Complex.sqrt (1-z^2)+I*z)*(Complex.sqrt (1-z^2)-I*z)=1 := by
  linear_combination trig_sqrt_sq (1-z^2) - z^2*Complex.I_sq

/-- Nonvanishing under the stated hypotheses: `Complex.sqrt (1-z^2)+I*z≠0`. -/
lemma trig_arcsin_log_arg_ne (z:ℂ) : Complex.sqrt (1-z^2)+I*z≠0 := by
  intro h
  have hp:=trig_arcsin_product z
  rw [h,zero_mul] at hp
  exact zero_ne_one hp

/-- Formula under the stated hypotheses: `Complex.sqrt (1-z^2)+I*z∈Complex.slitPlane`. -/
private lemma trig_arcsin_log_slit (z:ℂ) : Complex.sqrt (1-z^2)+I*z∈Complex.slitPlane := by
  let r:=Complex.sqrt (1-z^2)
  change r+I*z∈Complex.slitPlane
  rw [Complex.mem_slitPlane_iff]
  by_cases hi:(r+I*z).im≠0
  · exact Or.inr hi
  · left
    have hi0:(r+I*z).im=0 := not_ne_iff.mp hi
    have hr:0≤r.re := by
      dsimp [r]
      rw [Complex.sqrt,Complex.cpow_inv_two_re]
      positivity
    have him:r.im= -z.re := by
      simp only [Complex.add_im,Complex.I_mul_im] at hi0
      linarith
    have hp:=congrArg Complex.re (trig_arcsin_product z)
    change ((r+I*z)*(r-I*z)).re=1 at hp
    simp only [Complex.mul_re,Complex.add_re,Complex.sub_re,Complex.add_im,Complex.sub_im,
      Complex.I_mul_re,Complex.I_mul_im,him] at hp
    norm_num only [Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_sub] at hp
    simp only [Complex.add_re,Complex.I_mul_re]
    nlinarith

/-- Formula under the stated hypotheses: `1-z^2∈Complex.slitPlane`. -/
lemma trig_one_sub_sq_slit {z:ℂ} (hz:z∈arcsinCutPlane) : 1-z^2∈Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_cases hi:z.im=0
  · left
    have hr:|z.re|<1 := hz.resolve_left (not_ne_iff.mpr hi)
    simp [pow_two,Complex.mul_re,hi]
    nlinarith [(abs_lt.mp hr).1,(abs_lt.mp hr).2]
  · by_cases hr:z.re=0
    · left
      simp [pow_two,Complex.mul_re,hr]
      nlinarith [sq_nonneg z.im]
    · right
      simp [pow_two,Complex.mul_im]
      convert neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero two_ne_zero hr) hi) using 1 <;> ring

/-- At `q`, the function `Complex.sqrt` has derivative `((Complex.sqrt q)⁻¹/2)`. -/
lemma trig_hasDerivAt_sqrt {q:ℂ} (hq:q∈Complex.slitPlane) :
    HasDerivAt Complex.sqrt ((Complex.sqrt q)⁻¹/2) q := by
  simpa only [Complex.sqrt,show (-1/2:ℂ)= -(2⁻¹:ℂ) by norm_num,Complex.cpow_neg] using
    Complex.hasDerivAt_sqrt hq

/-- At `z`, the function `arcsinPrincipal` has derivative `(Complex.sqrt (1-z^2))⁻¹`. -/
lemma trig_hasDerivAt_arcsin {z:ℂ} (hz:z∈arcsinCutPlane) :
    HasDerivAt arcsinPrincipal (Complex.sqrt (1-z^2))⁻¹ z := by
  have hq:=trig_one_sub_sq_slit hz
  have hr:Complex.sqrt (1-z^2)≠0 := by
    intro h
    have hs:=trig_sqrt_sq (1-z^2)
    rw [h,zero_pow two_ne_zero] at hs
    exact (Complex.mem_slitPlane_iff_arg.mp hq).2 hs.symm
  have hd0:=(trig_hasDerivAt_sqrt hq).comp z (((hasDerivAt_id z).pow 2).const_sub 1)
  have hd1:=hd0.add ((hasDerivAt_id z).const_mul I)
  have hd2:=(Complex.hasDerivAt_log (trig_arcsin_log_slit z)).comp z hd1
  have hd:=hd2.const_mul (-I)
  convert hd using 1
  · rfl
  · dsimp only [id,Pi.pow_apply,Pi.add_apply]
    norm_num only [Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one,one_mul]
    generalize heq : Complex.sqrt (1-z^2)=r at hr ⊢
    have hw:r+I*z≠0 := by rw [← heq]; exact trig_arcsin_log_arg_ne z
    field_simp [hr,hw]
    linear_combination r*Complex.I_sq

/-- DLMF 4.23.ii: analytic arcsin principal. -/
@[dlmf 4.23.ii]
theorem analytic_arcsin_principal : AnalyticOnNhd ℂ arcsinPrincipal arcsinCutPlane := by
  have hU:IsOpen arcsinCutPlane := by
    change IsOpen ({z:ℂ | z.im≠0}∪{z:ℂ | |z.re|<1})
    exact (isOpen_ne.preimage Complex.continuous_im).union
      (isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const)
  exact (show DifferentiableOn ℂ arcsinPrincipal arcsinCutPlane from fun z hz=>
    (trig_hasDerivAt_arcsin hz).differentiableAt.differentiableWithinAt).analyticOnNhd hU

/-- The principal arcsine is continuous at every point of its closed unit disk,
including the two branch points. -/
lemma continuousAt_arcsin_principal_of_norm_le_one {z : ℂ} (hz : ‖z‖≤1) :
    ContinuousAt arcsinPrincipal z := by
  have hre : 0 ≤ (1-z^2).re := by
    have hnorm := Complex.sq_norm z
    rw [Complex.normSq_apply] at hnorm
    simp only [Complex.sub_re, Complex.one_re, pow_two, Complex.mul_re]
    nlinarith [sq_nonneg z.im, norm_nonneg z]
  have hroot : ContinuousAt Complex.sqrt (1-z^2) := Complex.continuousAt_sqrt (Or.inl hre)
  have hpoly : ContinuousAt (fun w : ℂ => 1-w^2) z := by fun_prop
  have hsqrt : ContinuousAt (fun w : ℂ => Complex.sqrt (1-w^2)) z :=
    hroot.comp (f := fun w : ℂ => 1-w^2) hpoly
  have hs : ContinuousAt (fun w : ℂ => Complex.sqrt (1-w^2)+I*w) z :=
    hsqrt.add (by fun_prop)
  exact (continuousAt_clog (trig_arcsin_log_slit z)).comp
    (f := fun w : ℂ => Complex.sqrt (1-w^2)+I*w) hs |>.const_mul (-I)

/-- DLMF 4.23.ii: analytic arccos principal. -/
@[dlmf 4.23.ii]
theorem analytic_arccos_principal : AnalyticOnNhd ℂ arccosPrincipal arcsinCutPlane := by
  intro z hz
  change AnalyticAt ℂ (fun w=>(π:ℂ)/2-arcsinPrincipal w) z
  exact analyticAt_const.sub (analytic_arcsin_principal z hz)

/-- DLMF 4.23.ii: analytic arctan principal. -/
@[dlmf 4.23.ii]
theorem analytic_arctan_principal : AnalyticOnNhd ℂ Complex.arctan arctanCutPlane := by
  have hU:IsOpen arctanCutPlane := by
    change IsOpen ({z:ℂ|z.re≠0}∪{z:ℂ | |z.im|<1})
    exact (isOpen_ne.preimage Complex.continuous_re).union
      (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const)
  exact (show DifferentiableOn ℂ Complex.arctan arctanCutPlane from fun z hz=>
    (trig_hasDerivAt_arctan hz).differentiableAt.differentiableWithinAt).analyticOnNhd hU

/-- DLMF 4.23.ii: analytic arccsc principal. -/
@[dlmf 4.23.ii]
theorem analytic_arccsc_principal : AnalyticOnNhd ℂ arccscPrincipal arccscCutPlane := by
  intro z hz
  exact (analytic_arcsin_principal _ hz.2).comp (analyticAt_id.inv hz.1)

/-- DLMF 4.23.ii: analytic arcsec principal. -/
@[dlmf 4.23.ii]
theorem analytic_arcsec_principal : AnalyticOnNhd ℂ arcsecPrincipal arccscCutPlane := by
  intro z hz
  exact (analytic_arccos_principal _ hz.2).comp (analyticAt_id.inv hz.1)

/-- DLMF 4.23.ii: analytic arccot principal. -/
@[dlmf 4.23.ii]
theorem analytic_arccot_principal : AnalyticOnNhd ℂ arccotPrincipal arccotCutPlane := by
  intro z hz
  exact (analytic_arctan_principal _ hz.2).comp (analyticAt_id.inv hz.1)

open scoped ComplexOrder in
/-- DLMF 4.23.ii: inverse principal real. -/
@[dlmf 4.23.ii]
theorem inverse_principal_real {x : ℝ} (hx : x∈Icc (-1) 1) :
    arcsinPrincipal x=(Real.arcsin x:ℂ) ∧ arccosPrincipal x=(Real.arccos x:ℂ) := by
  have hs : arcsinPrincipal x=(Real.arcsin x:ℂ) := by
    have h1 : (1:ℂ) - (x:ℂ)^2 = ((1 - x^2 : ℝ) : ℂ) := by push_cast; ring
    have hnn : (0:ℂ) ≤ ((1 - x^2 : ℝ) : ℂ) := by
      rw [Complex.zero_le_real]; nlinarith [hx.1, hx.2]
    have hsq : Complex.sqrt (1 - (x:ℂ)^2) = (Real.cos (Real.arcsin x) : ℂ) := by
      rw [h1, Complex.sqrt_of_nonneg hnn, Complex.ofReal_re, Real.cos_arcsin]
    have he : Complex.sqrt (1 - (x:ℂ)^2) + I*x = Complex.exp ((Real.arcsin x:ℂ) * I) := by
      rw [hsq, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
        Real.sin_arcsin hx.1 hx.2]
      ring
    rw [arcsinPrincipal, he, Complex.log_exp]
    · linear_combination (-(Real.arcsin x:ℂ))*Complex.I_sq
    · simp; linarith [Real.neg_pi_div_two_le_arcsin x, Real.pi_pos]
    · simp; linarith [Real.arcsin_le_pi_div_two x, Real.pi_pos]
  refine ⟨hs, ?_⟩
  rw [arccosPrincipal, hs, Real.arccos_eq_pi_div_two_sub_arcsin]
  push_cast; ring

/-- DLMF 4.23.E10: arcsin principal neg. -/
@[dlmf 4.23.E10]
theorem arcsin_principal_neg {z : ℂ} : arcsinPrincipal (-z)= -arcsinPrincipal z := by
  have hn:Complex.sqrt (1-(-z)^2)+I*(-z)=(Complex.sqrt (1-z^2)+I*z)⁻¹ := by
    apply (mul_left_cancel₀ (trig_arcsin_log_arg_ne z))
    rw [mul_inv_cancel₀ (trig_arcsin_log_arg_ne z)]
    convert trig_arcsin_product z using 1 <;> ring
  unfold arcsinPrincipal
  rw [hn,Complex.log_inv _ (Complex.mem_slitPlane_iff_arg.mp (trig_arcsin_log_slit z)).1]
  ring

/-- DLMF 4.23.E11: arccos principal neg. -/
@[dlmf 4.23.E11]
theorem arccos_principal_neg {z : ℂ} : arccosPrincipal (-z)=π-arccosPrincipal z := by
  unfold arccosPrincipal
  rw [arcsin_principal_neg]
  ring

/-- DLMF 4.23.E12: arctan principal neg. -/
@[dlmf 4.23.E12]
theorem arctan_principal_neg {z : ℂ} (hz : z∈arctanCutPlane) :
    Complex.arctan (-z)= -Complex.arctan z := by
  have hq: (1+(-z)*I)/(1-(-z)*I)=((1+z*I)/(1-z*I))⁻¹ := by
    simp only [neg_mul,sub_neg_eq_add,sub_eq_add_neg,inv_div,neg_neg]
  rw [Complex.arctan,Complex.arctan,hq,Complex.log_inv _
    (Complex.mem_slitPlane_iff_arg.mp (trig_arctan_quotient_slit hz)).1]
  ring

/-- DLMF 4.23.E13: arccsc principal neg. -/
@[dlmf 4.23.E13]
theorem arccsc_principal_neg {z : ℂ} : arccscPrincipal (-z)= -arccscPrincipal z := by
  unfold arccscPrincipal
  rw [inv_neg]
  exact arcsin_principal_neg

/-- DLMF 4.23.E14: arcsec principal neg. -/
@[dlmf 4.23.E14]
theorem arcsec_principal_neg {z : ℂ} : arcsecPrincipal (-z)=π-arcsecPrincipal z := by
  unfold arcsecPrincipal
  rw [inv_neg]
  exact arccos_principal_neg

/-- DLMF 4.23.E15: arccot principal neg. -/
@[dlmf 4.23.E15]
theorem arccot_principal_neg {z : ℂ} (hz : z∈arccotCutPlane) :
    arccotPrincipal (-z)= -arccotPrincipal z := by
  unfold arccotPrincipal
  rw [inv_neg]
  exact arctan_principal_neg hz.2

/-- DLMF 4.23.E17: arcsec principal complement. -/
@[dlmf 4.23.E17]
theorem arcsec_principal_complement (z : ℂ) : arcsecPrincipal z=π/2-arccscPrincipal z := by
  rfl

/-- DLMF 4.23.E18: arccot principal complement. -/
@[dlmf 4.23.E18]
theorem arccot_principal_complement {z : ℂ} (hz : z.re≠0) :
    arccotPrincipal z=(if 0<z.re then π/2 else -π/2)-Complex.arctan z := by
  set w := (1+z*I)/(1-z*I) with hw
  have hD : 0<(1+z.im)^2+z.re^2 := add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hz)
  have him : w.im=(2*z.re)/((1+z.im)^2+z.re^2) := by
    simp [hw, Complex.div_im,Complex.normSq]
    ring
  have hm : 1 - z*I ≠ 0 := by
    intro h; have h2 := congrArg Complex.im h; simp at h2; exact hz h2
  have hzI : z - I ≠ 0 := by
    intro h; have h2 := congrArg Complex.re h; simp at h2; exact hz h2
  have h1 : (1+z⁻¹*I)/(1-z⁻¹*I) = -w⁻¹ := by
    have hz0 : z ≠ 0 := by rintro rfl; simp at hz
    have hp : 1 + z*I ≠ 0 := by
      intro h; have h2 := congrArg Complex.im h; simp at h2; exact hz h2
    have e1 : (1+z⁻¹*I)/(1-z⁻¹*I) = (z+I)/(z-I) := by
      rw [← mul_div_mul_left (1+z⁻¹*I) (1-z⁻¹*I) hz0]
      congr 1 <;> field_simp
    rw [e1, hw, inv_div, ← neg_div, div_eq_div_iff hzI hp]
    linear_combination (2*z)*Complex.I_sq
  have hl : ∀ s : ℝ, (Complex.arg (-w⁻¹) = -Complex.arg w + s) →
      Complex.log (-w⁻¹) = -Complex.log w + s * I := by
    intro s hs
    apply Complex.ext
    · simp [Complex.log_re, norm_inv, Real.log_inv]
    · simp [Complex.log_im, hs]
  rw [arccotPrincipal, Complex.arctan, Complex.arctan, h1, ← hw]
  have hinv : (w⁻¹).im = -w.im / Complex.normSq w := Complex.inv_im w
  split_ifs with hpos
  · have hwi : 0 < w.im := by rw [him]; positivity
    have hwi' : (w⁻¹).im < 0 := by
      rw [hinv, neg_div]; exact neg_neg_of_pos (div_pos hwi (Complex.normSq_pos.mpr (by
        intro h; rw [h] at hwi; simp at hwi)))
    have ha : Complex.arg w ≠ π := by
      intro h; have := Complex.arg_eq_pi_iff.mp h; linarith [this.2]
    rw [hl π (by rw [Complex.arg_neg_eq_arg_add_pi_of_im_neg hwi', Complex.arg_inv,
        ite_cond_eq_false _ _ (eq_false ha)])]
    push_cast
    linear_combination (-(π:ℂ)/2)*Complex.I_sq
  · have hneg : z.re < 0 := lt_of_le_of_ne (not_lt.mp hpos) hz
    have hwi : w.im < 0 := by rw [him]; exact div_neg_of_neg_of_pos (by linarith) hD
    have hwi' : 0 < (w⁻¹).im := by
      rw [hinv, neg_div]; exact neg_pos.mpr (div_neg_of_neg_of_pos hwi (Complex.normSq_pos.mpr (by
        intro h; rw [h] at hwi; simp at hwi)))
    have ha : Complex.arg w ≠ π := by
      intro h; have := Complex.arg_eq_pi_iff.mp h; linarith [this.2]
    rw [hl (-π) (by rw [Complex.arg_neg_eq_arg_sub_pi_of_im_pos hwi', Complex.arg_inv,
        ite_cond_eq_false _ _ (eq_false ha)]; ring)]
    push_cast
    linear_combination ((π:ℂ)/2)*Complex.I_sq

/-- `arcsin 0 = 0` for the principal branch. -/
@[simp]
theorem arcsinPrincipal_zero : arcsinPrincipal 0 = 0 := by
  simpa using (inverse_principal_real (x := 0) (by norm_num)).1

/-- `arccos 0 = π/2` for the principal branch. -/
@[simp]
theorem arccosPrincipal_zero : arccosPrincipal 0 = π / 2 := by
  simp [arccosPrincipal]

end DLMF.Elementary
