/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Elementary.Trigonometric.DirectIdentities

/-!
# Principal and general inverse trigonometric branches

Inverse domains, analytic branches, cut limits and the principal sine and cosine inverse
formulas.

Source references and common attribution are retained in
`DLMF.Elementary.Trigonometric`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Polynomial

open scoped Real Topology Nat

namespace DLMF.Elementary

/-! ## Principal and general inverse functions, including cut banks -/

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

/-- Principal inverse cotangent off its central imaginary cut; its totalized value at zero is not a bank value. -/
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

/-- The sign of the upper bank, or of the right bank for vertical cuts. -/
def trigBankSign (upper : Bool) : ℂ := if upper then 1 else -1

/-- General arcsine values, retaining every inverse image. -/
def arcsinGeneral (z : ℂ) : Set ℂ := {w | Complex.sin w=z}

/-- General arccosine values, retaining every inverse image. -/
def arccosGeneral (z : ℂ) : Set ℂ := {w | Complex.cos w=z}

/-- General arctangent values; totalized tangent poles are excluded. -/
def arctanGeneral (z : ℂ) : Set ℂ := {w | Complex.cos w≠0 ∧ Complex.tan w=z}

/-- General inverse cosecant values, excluding poles of cosecant. -/
def arccscGeneral (z : ℂ) : Set ℂ := {w | Complex.sin w≠0 ∧ csc w=z}

/-- General inverse secant values, excluding poles of secant. -/
def arcsecGeneral (z : ℂ) : Set ℂ := {w | Complex.cos w≠0 ∧ sec w=z}

/-- General inverse cotangent values, excluding poles of cotangent. -/
def arccotGeneral (z : ℂ) : Set ℂ := {w | Complex.sin w≠0 ∧ Complex.cot w=z}

/-- A path together with a continuously continued square root starting at +1. -/
def ArcsinLift (γ r : ℝ→ℂ) (z : ℂ) : Prop :=
  ContDiffOn ℝ 1 γ (Icc 0 1) ∧ γ 0=0 ∧ γ 1=z ∧ ContinuousOn r (Icc 0 1) ∧ r 0=1 ∧
    ∀ t∈Icc 0 1,r t≠0 ∧ (r t)^2=1-(γ t)^2

/-- DLMF 4.23.E1: arcsin general integral. -/
@[dlmf 4.23.E1]
theorem arcsin_general_integral {z w : ℂ} (hzp : z≠1) (hzm : z≠ -1) :
    w∈arcsinGeneral z ↔ ∃ γ r : ℝ→ℂ,ArcsinLift γ r z ∧
      (∫ t in (0:ℝ)..1,deriv γ t/r t)=w := by
  sorry

/-- The integral from z to 1, normalized by the principal segment from zero to one. -/
@[dlmf 4.23.E2]
theorem arccos_general_integral {z w : ℂ} (hzp : z≠1) (hzm : z≠ -1) :
    w∈arccosGeneral z ↔ ∃ γ r : ℝ→ℂ,ArcsinLift γ r z ∧
      π/2-(∫ t in (0:ℝ)..1,deriv γ t/r t)=w := by
  sorry

/-- DLMF 4.23.E3: arctan general integral. -/
@[dlmf 4.23.E3]
theorem arctan_general_integral {z w : ℂ} (hzp : z≠I) (hzm : z≠ -I) :
    w∈arctanGeneral z ↔ ∃ γ : ℝ→ℂ,
      ContDiffOn ℝ 1 γ (Icc 0 1) ∧ γ 0=0 ∧ γ 1=z ∧
      (∀ t∈Icc 0 1,γ t≠I ∧ γ t≠ -I) ∧
      (∫ t in (0:ℝ)..1,deriv γ t/(1+(γ t)^2))=w := by
  sorry

/-- Formula under the stated hypotheses: `(1+z*I)/(1-z*I)∈Complex.slitPlane`. -/
private lemma trig_arctan_quotient_slit {z:ℂ} (hz:z∈arctanCutPlane) :
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

/-- DLMF 4.23.E4: arccsc general reciprocal. -/
@[dlmf 4.23.E4]
theorem arccsc_general_reciprocal {z : ℂ} (hz : z≠0) : arccscGeneral z=arcsinGeneral z⁻¹ := by
  ext w
  change (Complex.sin w≠0 ∧ (Complex.sin w)⁻¹=z) ↔ Complex.sin w=z⁻¹
  constructor
  · intro h
    have := congrArg Inv.inv h.2
    simpa using this
  · intro h
    exact ⟨by simpa [h] using inv_ne_zero hz,by simp [h]⟩

/-- DLMF 4.23.E5: arcsec general reciprocal. -/
@[dlmf 4.23.E5]
theorem arcsec_general_reciprocal {z : ℂ} (hz : z≠0) : arcsecGeneral z=arccosGeneral z⁻¹ := by
  ext w
  change (Complex.cos w≠0 ∧ (Complex.cos w)⁻¹=z) ↔ Complex.cos w=z⁻¹
  constructor
  · intro h
    have := congrArg Inv.inv h.2
    simpa using this
  · intro h
    exact ⟨by simpa [h] using inv_ne_zero hz,by simp [h]⟩

/-- DLMF 4.23.E6: arccot general reciprocal. -/
@[dlmf 4.23.E6]
theorem arccot_general_reciprocal {z : ℂ} (hz : z≠0) : arccotGeneral z=arctanGeneral z⁻¹ := by
  ext w
  change (Complex.sin w≠0 ∧ Complex.cot w=z) ↔ Complex.cos w≠0 ∧ Complex.tan w=z⁻¹
  rw [cot_eq_inv_tan]
  constructor
  · rintro ⟨hs,ht⟩
    have ht0 : Complex.tan w≠0 := by
      intro h
      apply hz
      simpa [h] using ht.symm
    refine ⟨?_,?_⟩
    · intro h; exact ht0 (by simp [Complex.tan,h])
    · simpa using congrArg Inv.inv ht
  · rintro ⟨hc,ht⟩
    refine ⟨?_,by simp [ht]⟩
    intro h
    have : (z⁻¹:ℂ)=0 := by simpa [Complex.tan,h] using ht.symm
    exact inv_ne_zero hz this

/-- Identity under the stated parameter and domain assumptions: `(Complex.sqrt
(1-z^2)+I*z)*(Complex.sqrt (1-z^2)-I*z)=1`. -/
private lemma trig_arcsin_product (z:ℂ) :
    (Complex.sqrt (1-z^2)+I*z)*(Complex.sqrt (1-z^2)-I*z)=1 := by
  linear_combination trig_sqrt_sq (1-z^2) - z^2*Complex.I_sq

/-- Nonvanishing under the stated hypotheses: `Complex.sqrt (1-z^2)+I*z≠0`. -/
private lemma trig_arcsin_log_arg_ne (z:ℂ) : Complex.sqrt (1-z^2)+I*z≠0 := by
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
theorem arcsin_principal_neg {z : ℂ} (hz : z∈arcsinCutPlane) : arcsinPrincipal (-z)= -arcsinPrincipal z := by
  have hn:Complex.sqrt (1-(-z)^2)+I*(-z)=(Complex.sqrt (1-z^2)+I*z)⁻¹ := by
    apply (mul_left_cancel₀ (trig_arcsin_log_arg_ne z))
    rw [mul_inv_cancel₀ (trig_arcsin_log_arg_ne z)]
    convert trig_arcsin_product z using 1 <;> ring
  unfold arcsinPrincipal
  rw [hn,Complex.log_inv _ (Complex.mem_slitPlane_iff_arg.mp (trig_arcsin_log_slit z)).1]
  ring

/-- DLMF 4.23.E11: arccos principal neg. -/
@[dlmf 4.23.E11]
theorem arccos_principal_neg {z : ℂ} (hz : z∈arcsinCutPlane) : arccosPrincipal (-z)=π-arccosPrincipal z := by
  unfold arccosPrincipal
  rw [arcsin_principal_neg hz]
  ring

/-- DLMF 4.23.E12: arctan principal neg. -/
@[dlmf 4.23.E12]
theorem arctan_principal_neg {z : ℂ} (hz : z∈arctanCutPlane) : Complex.arctan (-z)= -Complex.arctan z := by
  have hq: (1+(-z)*I)/(1-(-z)*I)=((1+z*I)/(1-z*I))⁻¹ := by
    simp only [neg_mul,sub_neg_eq_add,sub_eq_add_neg,inv_div,neg_neg]
  rw [Complex.arctan,Complex.arctan,hq,Complex.log_inv _
    (Complex.mem_slitPlane_iff_arg.mp (trig_arctan_quotient_slit hz)).1]
  ring

/-- DLMF 4.23.E13: arccsc principal neg. -/
@[dlmf 4.23.E13]
theorem arccsc_principal_neg {z : ℂ} (hz : z∈arccscCutPlane) : arccscPrincipal (-z)= -arccscPrincipal z := by
  unfold arccscPrincipal
  rw [inv_neg]
  exact arcsin_principal_neg hz.2

/-- DLMF 4.23.E14: arcsec principal neg. -/
@[dlmf 4.23.E14]
theorem arcsec_principal_neg {z : ℂ} (hz : z∈arccscCutPlane) : arcsecPrincipal (-z)=π-arcsecPrincipal z := by
  unfold arcsecPrincipal
  rw [inv_neg]
  exact arccos_principal_neg hz.2

/-- DLMF 4.23.E15: arccot principal neg. -/
@[dlmf 4.23.E15]
theorem arccot_principal_neg {z : ℂ} (hz : z∈arccotCutPlane) : arccotPrincipal (-z)= -arccotPrincipal z := by
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
    rw [hl π (by rw [Complex.arg_neg_eq_arg_add_pi_of_im_neg hwi', Complex.arg_inv, ite_cond_eq_false _ _ (eq_false ha)])]
    push_cast
    linear_combination (-(π:ℂ)/2)*Complex.I_sq
  · have hneg : z.re < 0 := lt_of_le_of_ne (not_lt.mp hpos) hz
    have hwi : w.im < 0 := by rw [him]; exact div_neg_of_neg_of_pos (by linarith) hD
    have hwi' : 0 < (w⁻¹).im := by
      rw [hinv, neg_div]; exact neg_pos.mpr (div_neg_of_neg_of_pos hwi (Complex.normSq_pos.mpr (by
        intro h; rw [h] at hwi; simp at hwi)))
    have ha : Complex.arg w ≠ π := by
      intro h; have := Complex.arg_eq_pi_iff.mp h; linarith [this.2]
    rw [hl (-π) (by rw [Complex.arg_neg_eq_arg_sub_pi_of_im_pos hwi', Complex.arg_inv, ite_cond_eq_false _ _ (eq_false ha)]; ring)]
    push_cast
    linear_combination ((π:ℂ)/2)*Complex.I_sq

/-- Arcsine on either bank of the positive real cut. -/
@[dlmf 4.23.E20]
def arcsinRightBank (upper : Bool) (x : ℝ) : ℂ :=
  π/2+trigBankSign upper*I*(Real.log (Real.sqrt (x^2-1)+x):ℂ)

/-- Arcsine on either bank of the negative real cut. -/
@[dlmf 4.23.E21]
def arcsinLeftBank (upper : Bool) (x : ℝ) : ℂ :=
  -π/2+trigBankSign upper*I*(Real.log (Real.sqrt (x^2-1)-x):ℂ)

/-- The principal square root formula valid on the lower half-plane, extended continuously. -/
def trigR4_sqrtLow (w : ℂ) : ℂ := (Real.sqrt ((‖w‖ + w.re)/2) : ℂ) - I * Real.sqrt ((‖w‖ - w.re)/2)

/-- The principal square root formula valid on the closed upper half-plane. -/
def trigR4_sqrtUp (w : ℂ) : ℂ := (Real.sqrt ((‖w‖ + w.re)/2) : ℂ) + I * Real.sqrt ((‖w‖ - w.re)/2)

/-- On the lower half-plane the principal root is `trigR4_sqrtLow`. -/
lemma trigR4_sqrt_eq_low {w : ℂ} (h : w.im < 0) : Complex.sqrt w = trigR4_sqrtLow w := by
  rw [Complex.sqrt_eq_real_add_ite, trigR4_sqrtLow, ite_eq_right_of_eq_false _ _ (eq_false (not_le.mpr h))]; ring

/-- On the closed upper half-plane the principal root is `trigR4_sqrtUp`. -/
lemma trigR4_sqrt_eq_up {w : ℂ} (h : 0 ≤ w.im) : Complex.sqrt w = trigR4_sqrtUp w := by
  rw [Complex.sqrt_eq_real_add_ite, trigR4_sqrtUp, ite_eq_left_of_eq_true _ _ (eq_true h)]; ring

/-- The lower-bank root formula is continuous. -/
lemma trigR4_continuous_sqrtLow : Continuous trigR4_sqrtLow := by
  unfold trigR4_sqrtLow; fun_prop

/-- The upper-bank root formula is continuous. -/
lemma trigR4_continuous_sqrtUp : Continuous trigR4_sqrtUp := by
  unfold trigR4_sqrtUp; fun_prop

/-- Lower-bank root of a nonpositive real. -/
lemma trigR4_sqrtLow_neg {t : ℝ} (ht : 0 ≤ t) : trigR4_sqrtLow (-(t:ℂ)) = -I * Real.sqrt t := by
  simp [trigR4_sqrtLow, abs_of_nonneg ht]

/-- Upper-bank root of a nonpositive real. -/
lemma trigR4_sqrtUp_neg {t : ℝ} (ht : 0 ≤ t) : trigR4_sqrtUp (-(t:ℂ)) = I * Real.sqrt t := by
  simp [trigR4_sqrtUp, abs_of_nonneg ht]

/-- Logarithm of a point on the positive imaginary axis. -/
lemma trigR4_log_I_mul_pos {s : ℝ} (hs : 0 < s) :
    Complex.log (I * s) = Real.log s + π/2 * I := by
  apply Complex.ext
  · simp [Complex.log_re, abs_of_pos hs]
  · simp [Complex.log_im, mul_comm I, Complex.arg_real_mul _ hs]

/-- Logarithm of a point on the negative imaginary axis. -/
lemma trigR4_log_I_mul_neg {s : ℝ} (hs : s < 0) :
    Complex.log (I * s) = Real.log (-s) - π/2 * I := by
  have he : I * (s:ℂ) = ((-s:ℝ):ℂ) * (-I) := by push_cast; ring
  apply Complex.ext
  · simp [Complex.log_re, abs_of_neg hs]
  · rw [he, Complex.log_im, Complex.arg_real_mul _ (by linarith), Complex.arg_neg_I]; simp

/-- Arcsine limits along a bank where the square root follows a continuous formula. -/
lemma trigR4_arcsin_bank {x : ℝ} {T : Set ℂ} {G : ℂ → ℂ} (hG : Continuous G)
    (hev : ∀ᶠ z in 𝓝[T] (x:ℂ), Complex.sqrt (1 - z^2) = G (1 - z^2))
    (hP : G (1 - (x:ℂ)^2) + I*x ∈ Complex.slitPlane) :
    Tendsto arcsinPrincipal (𝓝[T] (x:ℂ)) (𝓝 (-I * Complex.log (G (1 - (x:ℂ)^2) + I*x))) := by
  have hc : ContinuousAt (fun z : ℂ => -I * Complex.log (G (1 - z^2) + I*z)) (x:ℂ) := by
    apply ContinuousAt.mul continuousAt_const
    exact (((hG.comp (by fun_prop : Continuous fun z : ℂ => 1 - z^2)).add
      (by fun_prop : Continuous fun z : ℂ => I*z)).continuousAt).clog hP
  refine (hc.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [hev] with z hz
  simp only [arcsinPrincipal, hz]

/-- Imaginary part of `1 - z^2`. -/
lemma trigR4_im_one_sub_sq (z : ℂ) : (1 - z^2).im = -(2 * z.re * z.im) := by
  simp [pow_two, Complex.mul_im]; ring

/-- `1 - x^2` as the negative of a real number. -/
lemma trigR4_one_sub_sq_real (x : ℝ) : (1:ℂ) - (x:ℂ)^2 = -((x^2 - 1 : ℝ) : ℂ) := by
  push_cast; ring

/-- DLMF 4.23.E20: arcsin right cut limit. -/
@[dlmf 4.23.E20]
theorem arcsin_right_cut_limit {x : ℝ} (hx : 1≤x) (upper : Bool) :
    Tendsto arcsinPrincipal (𝓝[{z : ℂ | if upper then 0<z.im else z.im<0}] (x:ℂ))
      (𝓝 (arcsinRightBank upper x)) := by
  have hx0 : 0 < x := by linarith
  have hr0 : 0 ≤ x^2 - 1 := by nlinarith
  set r := Real.sqrt (x^2 - 1) with hr
  have hrx : r < x + 1 := by
    rw [hr, Real.sqrt_lt' (by linarith)]; nlinarith
  have hrr : r * r = x^2 - 1 := Real.mul_self_sqrt hr0
  have hxr : 0 < x - r := by
    rw [hr, sub_pos, Real.sqrt_lt' hx0]; linarith
  have hxr' : 0 < x + r := by positivity
  have hprod : (x - r) * (x + r) = 1 := by nlinarith
  have hlog : Real.log (x - r) = -Real.log (r + x) := by
    have : x - r = (r + x)⁻¹ := by
      exact eq_inv_of_mul_eq_one_left (by linarith [hprod])
    rw [this, Real.log_inv]
  have hre : ∀ᶠ z in 𝓝 (x:ℂ), 0 < z.re :=
    (Complex.continuous_re.tendsto (x:ℂ)).eventually (lt_mem_nhds (by simpa using hx0))
  cases upper
  · -- lower bank: im z < 0, so im (1 - z^2) > 0
    have hev : ∀ᶠ z in 𝓝[{z : ℂ | if false = true then 0<z.im else z.im<0}] (x:ℂ),
        Complex.sqrt (1 - z^2) = trigR4_sqrtUp (1 - z^2) := by
      filter_upwards [nhdsWithin_le_nhds hre, self_mem_nhdsWithin] with z hz hzT
      simp only [Bool.false_eq_true, ite_false] at hzT
      apply trigR4_sqrt_eq_up
      rw [trigR4_im_one_sub_sq]; nlinarith
    have hP : trigR4_sqrtUp (1 - (x:ℂ)^2) + I*x = I * ((x + r : ℝ):ℂ) := by
      rw [trigR4_one_sub_sq_real, trigR4_sqrtUp_neg hr0]; push_cast; ring
    have h := trigR4_arcsin_bank trigR4_continuous_sqrtUp hev
      (by rw [hP]; exact Or.inr (by simp; linarith))
    rw [hP, trigR4_log_I_mul_pos hxr'] at h
    convert h using 2
    simp only [arcsinRightBank, trigBankSign, Bool.false_eq_true, ite_false]
    rw [add_comm r x]
    linear_combination ((π:ℂ)/2)*Complex.I_sq
  · have hev : ∀ᶠ z in 𝓝[{z : ℂ | if true = true then 0<z.im else z.im<0}] (x:ℂ),
        Complex.sqrt (1 - z^2) = trigR4_sqrtLow (1 - z^2) := by
      filter_upwards [nhdsWithin_le_nhds hre, self_mem_nhdsWithin] with z hz hzT
      simp only [ite_true] at hzT
      apply trigR4_sqrt_eq_low
      rw [trigR4_im_one_sub_sq]; nlinarith
    have hP : trigR4_sqrtLow (1 - (x:ℂ)^2) + I*x = I * ((x - r : ℝ):ℂ) := by
      rw [trigR4_one_sub_sq_real, trigR4_sqrtLow_neg hr0]; push_cast; ring
    have h := trigR4_arcsin_bank trigR4_continuous_sqrtLow hev
      (by rw [hP]; exact Or.inr (by simp; linarith))
    rw [hP, trigR4_log_I_mul_pos hxr, hlog] at h
    convert h using 2
    simp only [arcsinRightBank, trigBankSign, ite_true]
    push_cast
    linear_combination ((π:ℂ)/2)*Complex.I_sq

/-- DLMF 4.23.E21: arcsin left cut limit. -/
@[dlmf 4.23.E21]
theorem arcsin_left_cut_limit {x : ℝ} (hx : x≤ -1) (upper : Bool) :
    Tendsto arcsinPrincipal (𝓝[{z : ℂ | if upper then 0<z.im else z.im<0}] (x:ℂ))
      (𝓝 (arcsinLeftBank upper x)) := by
  have hx0 : x < 0 := by linarith
  have hr0 : 0 ≤ x^2 - 1 := by nlinarith
  set r := Real.sqrt (x^2 - 1) with hr
  have hrr : r * r = x^2 - 1 := Real.mul_self_sqrt hr0
  have hrn : 0 ≤ r := Real.sqrt_nonneg _
  have hxr : x + r < 0 := by
    have : r < -x := by rw [hr, Real.sqrt_lt' (by linarith)]; nlinarith
    linarith
  have hxr' : x - r < 0 := by linarith
  have hlog : Real.log (-(x + r)) = -Real.log (r - x) := by
    have : -(x + r) = (r - x)⁻¹ := eq_inv_of_mul_eq_one_left (by nlinarith [hrr])
    rw [this, Real.log_inv]
  have hre : ∀ᶠ z in 𝓝 (x:ℂ), z.re < 0 :=
    (Complex.continuous_re.tendsto (x:ℂ)).eventually (gt_mem_nhds (by simpa using hx0))
  cases upper
  · have hev : ∀ᶠ z in 𝓝[{z : ℂ | if false = true then 0<z.im else z.im<0}] (x:ℂ),
        Complex.sqrt (1 - z^2) = trigR4_sqrtLow (1 - z^2) := by
      filter_upwards [nhdsWithin_le_nhds hre, self_mem_nhdsWithin] with z hz hzT
      simp only [Bool.false_eq_true, ite_false] at hzT
      apply trigR4_sqrt_eq_low
      rw [trigR4_im_one_sub_sq]; nlinarith
    have hP : trigR4_sqrtLow (1 - (x:ℂ)^2) + I*x = I * ((x - r : ℝ):ℂ) := by
      rw [trigR4_one_sub_sq_real, trigR4_sqrtLow_neg hr0]; push_cast; ring
    have h := trigR4_arcsin_bank trigR4_continuous_sqrtLow hev
      (by rw [hP]; exact Or.inr (by simp; linarith))
    rw [hP, trigR4_log_I_mul_neg hxr', show -(x - r) = r - x by ring] at h
    convert h using 2
    simp only [arcsinLeftBank, trigBankSign, Bool.false_eq_true, ite_false]
    linear_combination (-(π:ℂ)/2)*Complex.I_sq
  · have hev : ∀ᶠ z in 𝓝[{z : ℂ | if true = true then 0<z.im else z.im<0}] (x:ℂ),
        Complex.sqrt (1 - z^2) = trigR4_sqrtUp (1 - z^2) := by
      filter_upwards [nhdsWithin_le_nhds hre, self_mem_nhdsWithin] with z hz hzT
      simp only [ite_true] at hzT
      apply trigR4_sqrt_eq_up
      rw [trigR4_im_one_sub_sq]; nlinarith
    have hP : trigR4_sqrtUp (1 - (x:ℂ)^2) + I*x = I * ((x + r : ℝ):ℂ) := by
      rw [trigR4_one_sub_sq_real, trigR4_sqrtUp_neg hr0]; push_cast; ring
    have h := trigR4_arcsin_bank trigR4_continuous_sqrtUp hev
      (by rw [hP]; exact Or.inr (by simp; linarith))
    rw [hP, trigR4_log_I_mul_neg hxr, hlog] at h
    convert h using 2
    simp only [arcsinLeftBank, trigBankSign, ite_true]
    push_cast
    linear_combination (-(π:ℂ)/2)*Complex.I_sq

/-- DLMF 4.23.E22: arccos principal log. -/
@[dlmf 4.23.E22]
theorem arccos_principal_log (z : ℂ) :
    arccosPrincipal z=π/2+I*Complex.log (Complex.sqrt (1-z^2)+I*z) := by
  unfold arccosPrincipal arcsinPrincipal; ring

/-- DLMF 4.23.E24: arccos right cut limit. -/
@[dlmf 4.23.E24]
theorem arccos_right_cut_limit {x : ℝ} (hx : 1≤x) (upper : Bool) :
    Tendsto arccosPrincipal (𝓝[{z : ℂ | if upper then 0<z.im else z.im<0}] (x:ℂ))
      (𝓝 (π/2-arcsinRightBank upper x)) := by
  exact (arcsin_right_cut_limit hx upper).const_sub ((π:ℂ)/2)

/-- DLMF 4.23.E25: arccos left cut limit. -/
@[dlmf 4.23.E25]
theorem arccos_left_cut_limit {x : ℝ} (hx : x≤ -1) (upper : Bool) :
    Tendsto arccosPrincipal (𝓝[{z : ℂ | if upper then 0<z.im else z.im<0}] (x:ℂ))
      (𝓝 (π/2-arcsinLeftBank upper x)) := by
  exact (arcsin_left_cut_limit hx upper).const_sub ((π:ℂ)/2)

/-- DLMF 4.23.E26: arctan principal log. -/
@[dlmf 4.23.E26]
theorem arctan_principal_log {z : ℂ} (hz : z∈arctanCutPlane) :
    Complex.arctan z=I/2*Complex.log ((I+z)/(I-z)) := by
  have hs := trig_arctan_quotient_slit hz
  have hv : (I+z)/(I-z) = ((1+z*I)/(1-z*I))⁻¹ := by
    rw [inv_div, show (1-z*I) = (-I)*(I+z) by linear_combination Complex.I_sq,
      show (1+z*I) = (-I)*(I-z) by linear_combination Complex.I_sq,
      mul_div_mul_left _ _ (neg_ne_zero.mpr Complex.I_ne_zero)]
  rw [hv, Complex.log_inv _ (Complex.slitPlane_arg_ne_pi hs), Complex.arctan]
  ring

/-- Arctangent bank values on the two exterior imaginary cuts. -/
@[dlmf 4.23.E27]
def arctanCutBank (right : Bool) (y : ℝ) : ℂ :=
  trigBankSign right*π/2+I/2*(Real.log ((y+1)/(y-1)):ℂ)

/-- Imaginary part of the arctangent logarithm argument. -/
lemma trigR4_arctan_quot_im (z : ℂ) :
    ((1+z*I)/(1-z*I)).im=(2*z.re)/((1+z.im)^2+z.re^2) := by
  simp [Complex.div_im,Complex.normSq]
  ring

/-- DLMF 4.23.E27: arctan cut limit. -/
@[dlmf 4.23.E27]
theorem arctan_cut_limit {y : ℝ} (hy : 1< |y|) (right : Bool) :
    Tendsto Complex.arctan (𝓝[{z : ℂ | if right then 0<z.re else z.re<0}] ((y:ℂ)*I))
      (𝓝 (arctanCutBank right y)) := by
  have hy1 : y + 1 ≠ 0 := by
    intro h; rw [show y = -1 by linarith] at hy; norm_num at hy
  have hym : y - 1 ≠ 0 := by
    intro h; rw [show y = 1 by linarith] at hy; norm_num at hy
  have hden : (1:ℂ) - (y:ℂ)*I*I ≠ 0 := by
    rw [mul_assoc, Complex.I_mul_I]
    exact_mod_cast (show (1:ℝ) - y * -1 ≠ 0 by intro h; apply hy1; linarith)
  set w0 : ℂ := (1+(y:ℂ)*I*I)/(1-(y:ℂ)*I*I) with hw0
  have hw0r : w0 = (((1 - y)/(1 + y) : ℝ) : ℂ) := by
    rw [hw0, mul_assoc, Complex.I_mul_I]; push_cast; ring_nf
  have hneg : (1 - y)/(1 + y) < 0 := by
    rcases lt_or_gt_of_ne (show y ≠ 0 by rintro rfl; norm_num at hy) with h | h
    · have : y < -1 := by rw [abs_of_neg h] at hy; linarith
      exact div_neg_of_pos_of_neg (by linarith) (by linarith)
    · have : 1 < y := by rw [abs_of_pos h] at hy; linarith
      exact div_neg_of_neg_of_pos (by linarith) (by linarith)
  have hw0re : w0.re < 0 := by rw [hw0r, Complex.ofReal_re]; exact hneg
  have hw0im : w0.im = 0 := by rw [hw0r, Complex.ofReal_im]
  have hnorm : Real.log ‖w0‖ = -Real.log ((y+1)/(y-1)) := by
    rw [hw0r, Complex.norm_real, Real.norm_eq_abs, abs_of_neg hneg, ← Real.log_inv, inv_div,
      ← neg_div, neg_sub, add_comm 1 y]
  have hcont : ContinuousAt (fun z : ℂ => (1+z*I)/(1-z*I)) ((y:ℂ)*I) :=
    ((by fun_prop : Continuous fun z : ℂ => 1+z*I).continuousAt).div
      ((by fun_prop : Continuous fun z : ℂ => 1-z*I).continuousAt) hden
  have hD : ∀ z : ℂ, z.re ≠ 0 → 0 < (1+z.im)^2+z.re^2 := fun z hz =>
    add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hz)
  cases right
  · have hw : Tendsto (fun z : ℂ => (1+z*I)/(1-z*I))
        (𝓝[{z : ℂ | if false = true then 0<z.re else z.re<0}] ((y:ℂ)*I))
        (𝓝[{z : ℂ | z.im < 0}] w0) := by
      apply tendsto_nhdsWithin_iff.mpr ⟨hcont.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with z hz
      have hz' : z.re < 0 := by simpa using hz
      show ((1+z*I)/(1-z*I)).im < 0
      rw [trigR4_arctan_quot_im]
      exact div_neg_of_neg_of_pos (by linarith) (hD z hz'.ne)
    have h := ((Complex.tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero hw0re hw0im).comp
      hw).const_mul (-I/2)
    have h' : Tendsto Complex.arctan _ (𝓝 (-I/2 * (Real.log ‖w0‖ - π * I))) := h
    convert h' using 2
    simp only [arctanCutBank, trigBankSign, Bool.false_eq_true, ite_false, hnorm]
    push_cast
    linear_combination (-(π:ℂ)/2)*Complex.I_sq
  · have hw : Tendsto (fun z : ℂ => (1+z*I)/(1-z*I))
        (𝓝[{z : ℂ | if true = true then 0<z.re else z.re<0}] ((y:ℂ)*I))
        (𝓝[{z : ℂ | 0 ≤ z.im}] w0) := by
      apply tendsto_nhdsWithin_iff.mpr ⟨hcont.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with z hz
      have hz' : 0 < z.re := by simpa using hz
      show 0 ≤ ((1+z*I)/(1-z*I)).im
      rw [trigR4_arctan_quot_im]
      exact (div_pos (by linarith) (hD z hz'.ne')).le
    have h := ((Complex.tendsto_log_nhdsWithin_im_nonneg_of_re_neg_of_im_zero hw0re hw0im).comp
      hw).const_mul (-I/2)
    have h' : Tendsto Complex.arctan _ (𝓝 (-I/2 * (Real.log ‖w0‖ + π * I))) := h
    convert h' using 2
    simp only [arctanCutBank, trigBankSign, ite_true, hnorm]
    push_cast
    linear_combination ((π:ℂ)/2)*Complex.I_sq

/-- DLMF 4.23.iv: reciprocal reverses real cut bank. -/
@[dlmf 4.23.iv]
theorem reciprocal_reverses_real_cut_bank {x : ℝ} (hx : x≠0) :
    Tendsto (fun y : ℝ => ((x:ℂ)+I*y)⁻¹) (𝓝[>] 0) (𝓝 ((x:ℂ)⁻¹)) ∧
    ∀ y : ℝ,0<y→(((x:ℂ)+I*y)⁻¹).im<0 := by
  constructor
  · have hc : ContinuousAt (fun y : ℝ => ((x:ℂ)+I*y)⁻¹) 0 := by
      apply ContinuousAt.inv₀ (by fun_prop)
      simpa using hx
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  · intro y hy
    rw [Complex.inv_im]
    have : 0 < Complex.normSq ((x:ℂ)+I*y) := by
      rw [Complex.normSq_pos]; intro h; have := congrArg Complex.re h; simp at this; exact hx this
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re]
    have h2 : (0:ℝ) < (0 * y + 1 * y) := by linarith
    rw [neg_div]
    simpa [zero_add] using div_pos (by linarith : (0:ℝ) < 0 + (0 * 0 + 1 * y)) this

/-- DLMF 4.23.E28: sin arcsin principal. -/
@[dlmf 4.23.E28]
theorem sin_arcsin_principal (z : ℂ) : Complex.sin (arcsinPrincipal z)=z := by
  let w:=Complex.sqrt (1-z^2)+I*z
  have hw:w≠0 := trig_arcsin_log_arg_ne z
  have hp:w*(Complex.sqrt (1-z^2)-I*z)=1 := trig_arcsin_product z
  have hi:w⁻¹=Complex.sqrt (1-z^2)-I*z := by
    apply (mul_left_cancel₀ hw)
    rw [mul_inv_cancel₀ hw,hp]
  have he:Complex.exp (arcsinPrincipal z*I)=w := by
    rw [arcsinPrincipal,show -I*Complex.log w*I=Complex.log w by linear_combination -Complex.log w*Complex.I_sq]
    exact Complex.exp_log hw
  have hn:Complex.exp (-(arcsinPrincipal z)*I)=w⁻¹ := by
    rw [neg_mul,Complex.exp_neg,he]
  rw [Complex.sin,he,hn,hi]
  dsimp [w]
  linear_combination -z*Complex.I_sq

/-- DLMF 4.23.E29: cos arccos principal. -/
@[dlmf 4.23.E29]
theorem cos_arccos_principal (z : ℂ) : Complex.cos (arccosPrincipal z)=z := by
  rw [arccosPrincipal,Complex.cos_pi_div_two_sub,sin_arcsin_principal]

/-- Mathlib gives the two sine fibers separately; this combines them using integer parity. -/
private lemma trig_sine_fiber_forms (A w : ℂ) :
    (∃ k : ℤ,w=2*k*π+A ∨ w=(2*k+1)*π-A) ↔
      ∃ k : ℤ,w=(-1:ℂ)^k*A+k*π := by
  constructor
  · rintro ⟨k,hk|hk⟩
    · have he:Even (2*k:ℤ) := ⟨k,by ring⟩
      refine ⟨2*k,?_⟩
      rw [he.neg_one_zpow]
      push_cast
      linear_combination hk
    · have ho:Odd (2*k+1:ℤ) := ⟨k,by ring⟩
      refine ⟨2*k+1,?_⟩
      rw [ho.neg_one_zpow]
      push_cast
      linear_combination hk
  · rintro ⟨n,hn⟩
    obtain ⟨k,hk|hk⟩:=Int.even_or_odd' n
    · have he:Even (2*k:ℤ) := ⟨k,by ring⟩
      rw [hk,he.neg_one_zpow] at hn
      refine ⟨k,Or.inl ?_⟩
      push_cast at hn
      linear_combination hn
    · have ho:Odd (2*k+1:ℤ) := ⟨k,by ring⟩
      rw [hk,ho.neg_one_zpow] at hn
      refine ⟨k,Or.inr ?_⟩
      push_cast at hn
      linear_combination hn

/-- DLMF 4.23.E31: arcsin general values. -/
@[dlmf 4.23.E31]
theorem arcsin_general_values (z w : ℂ) :
    w∈arcsinGeneral z ↔ ∃ k : ℤ,w=(-1:ℂ)^k*arcsinPrincipal z+k*π := by
  change Complex.sin w=z ↔ _
  have hb:=sin_arcsin_principal z
  constructor
  · intro h
    exact (trig_sine_fiber_forms _ _).mp (Complex.sin_eq_sin_iff.mp (hb.trans h.symm))
  · intro h
    exact (Complex.sin_eq_sin_iff.mpr ((trig_sine_fiber_forms _ _).mpr h)).symm.trans hb

end DLMF.Elementary
end
