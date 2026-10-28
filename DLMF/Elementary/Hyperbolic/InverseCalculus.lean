/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Elementary.Hyperbolic.Products

/-!
# Principal inverse hyperbolic functions

Path domains, analyticity, derivatives and real restrictions of principal inverse hyperbolic
functions.

Source references and common attribution are retained in
`DLMF.Elementary.Hyperbolic`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory

open scoped Real Topology

namespace DLMF.Elementary

/-- A path integral with the square root continued from its value 1 at the origin. -/
def IsArcsinhPathValue (z w : ℂ) : Prop := ∃ γ r : ℝ → ℂ,
  ContDiffOn ℝ 1 γ (Icc 0 1) ∧ γ 0=0 ∧ γ 1=z ∧ ContinuousOn r (Icc 0 1) ∧ r 0=1 ∧
  (∀ s ∈ Icc (0:ℝ) 1, γ s≠I ∧ γ s≠ -I ∧ r s^2=1+γ s^2) ∧
  IntervalIntegrable (fun s => deriv γ s/r s) volume 0 1 ∧
  (∫ s : ℝ in 0..1, deriv γ s/r s)=w
/-- A path integral with the square root selected on an initial positive-real segment. -/
def IsArccoshPathValue (z w : ℂ) : Prop := ∃ γ r : ℝ → ℂ,
  ContDiffOn ℝ 1 γ (Icc 0 1) ∧ γ 0=1 ∧ γ 1=z ∧ ContinuousOn r (Icc 0 1) ∧ r 0=0 ∧
  (∀ s ∈ Ioc (0:ℝ) 1, γ s≠1 ∧ γ s≠ -1 ∧ r s^2=γ s^2-1) ∧
  (∃ ε ∈ Ioc (0:ℝ) 1, ∀ s ∈ Ioo (0:ℝ) ε,
    (γ s).im=0 ∧ 1<(γ s).re ∧ r s=Complex.sqrt (γ s^2-1)) ∧
  IntervalIntegrable (fun s => deriv γ s/r s) volume 0 1 ∧
  (∫ s : ℝ in 0..1, deriv γ s/r s)=w
/-- The inverse-tanh path integral, avoiding the two logarithmic branch points. -/
def IsArctanhPathValue (z w : ℂ) : Prop := ∃ γ : ℝ → ℂ,
  ContDiffOn ℝ 1 γ (Icc 0 1) ∧ γ 0=0 ∧ γ 1=z ∧
  (∀ s ∈ Icc (0:ℝ) 1, γ s≠1 ∧ γ s≠ -1) ∧
  IntervalIntegrable (fun s => deriv γ s/(1-γ s^2)) volume 0 1 ∧
  (∫ s : ℝ in 0..1, deriv γ s/(1-γ s^2))=w
/-- The multivalued inverse defined by all admissible continued-branch path integrals. -/
@[dlmf 4.37.E1]
theorem arcsinh_path_values {z : ℂ} (hz : z≠I ∧ z≠ -I) : {w | IsArcsinhPathValue z w}=arcsinhValues z := by
  sorry

/-- The multivalued inverse defined by all admissible continued-branch path integrals. -/
@[dlmf 4.37.E2]
theorem arccosh_path_values {z : ℂ} (hz : z≠1 ∧ z≠ -1) : {w | IsArccoshPathValue z w}=arccoshValues z := by
  sorry

/-- The multivalued inverse defined by all admissible continued-branch path integrals. -/
@[dlmf 4.37.E3]
theorem arctanh_path_values {z : ℂ} (hz : z≠1 ∧ z≠ -1) : {w | IsArctanhPathValue z w}=arctanhValues z := by
  sorry

/-- Identity under the stated parameter and domain assumptions: `arccschValues z=arcsinhValues
z⁻¹`. -/
@[dlmf 4.37.E4]
theorem arccsch_values_inv {z : ℂ} (hz : z≠0) : arccschValues z=arcsinhValues z⁻¹ := by
  ext w
  change (Complex.sinh w≠0 ∧ (Complex.sinh w)⁻¹=z) ↔ Complex.sinh w=z⁻¹
  constructor
  · intro h
    simpa only [inv_inv] using congrArg Inv.inv h.2
  · intro h
    exact ⟨by simpa only [h] using inv_ne_zero hz,by simp only [h,inv_inv]⟩

/-- Identity under the stated parameter and domain assumptions: `arcsechValues z=arccoshValues
z⁻¹`. -/
@[dlmf 4.37.E5]
theorem arcsech_values_inv {z : ℂ} (hz : z≠0) : arcsechValues z=arccoshValues z⁻¹ := by
  ext w
  change (Complex.cosh w≠0 ∧ (Complex.cosh w)⁻¹=z) ↔ Complex.cosh w=z⁻¹
  constructor
  · intro h
    simpa only [inv_inv] using congrArg Inv.inv h.2
  · intro h
    exact ⟨by simpa only [h] using inv_ne_zero hz,by simp only [h,inv_inv]⟩

/-- Identity under the stated parameter and domain assumptions: `arccothValues z=arctanhValues
z⁻¹`. -/
@[dlmf 4.37.E6]
theorem arccoth_values_inv {z : ℂ} (hz : z≠0) : arccothValues z=arctanhValues z⁻¹ := by
  ext w
  change (Complex.sinh w≠0 ∧ coth w=z) ↔ Complex.cosh w≠0 ∧ Complex.tanh w=z⁻¹
  rw [coth_eq_inv_tanh]
  constructor
  · rintro ⟨hs,ht⟩
    have ht0:Complex.tanh w≠0 := by
      intro h
      apply hz
      simpa [h] using ht.symm
    refine ⟨?_,?_⟩
    · intro h; exact ht0 (by simp [Complex.tanh,h])
    · simpa only [inv_inv] using congrArg Inv.inv ht
  · rintro ⟨hc,ht⟩
    refine ⟨?_,by simp only [ht,inv_inv]⟩
    intro h
    have hh:(z⁻¹:ℂ)=0 := by simpa [Complex.tanh,h] using ht.symm
    exact inv_ne_zero hz hh

/-- Identity under the stated parameter and domain assumptions: `arccoth z=arctanh z⁻¹`. -/
@[dlmf 4.37.E9]
theorem arccoth_eq_inv {z : ℂ} (hz : z≠0) : arccoth z=arctanh z⁻¹ := by
  simp [arccoth,hz]

/-- A chosen hyperbolic cosine value lifts a sine value to a compatible logarithm branch.
This uses Mathlib's principal logarithm and hyperbolic exponential definitions. -/
lemma hyper_sinh_cosh_log_lift (u s : ℂ) (hs : s^2=1+u^2) :
    Complex.sinh (Complex.log (s+u))=u ∧ Complex.cosh (Complex.log (s+u))=s := by
  have hprod:(s+u)*(s-u)=1 := by linear_combination hs
  have hne:s+u≠0 := by
    intro h
    rw [h,zero_mul] at hprod
    exact zero_ne_one hprod
  have hinv:(s+u)⁻¹=s-u := by
    apply mul_left_cancel₀ hne
    rw [mul_inv_cancel₀ hne,hprod]
  rw [Complex.sinh,Complex.cosh,Complex.exp_log hne,Complex.exp_neg,Complex.exp_log hne,hinv]
  constructor <;> ring

/-- The factored principal square root in inverse cosh has its prescribed square. -/
private lemma hyper_arccosh_root_sq (z : ℂ) :
    (Complex.sqrt (z-1)*Complex.sqrt (z+1))^2=z^2-1 := by
  rw [mul_pow,trig_sqrt_sq,trig_sqrt_sq]
  ring

/-- The logarithmic inverse-cosh definition is a right inverse even at its cut values. -/
lemma hyper_cosh_arccosh (z : ℂ) : Complex.cosh (arccosh z)=z := by
  have hs:z^2=1+(Complex.sqrt (z-1)*Complex.sqrt (z+1))^2 := by
    rw [hyper_arccosh_root_sq]
    ring
  exact (hyper_sinh_cosh_log_lift _ z hs).2

/-- Compatible inverse-sinh/cosh branches are characterized by their two shared roots. -/
lemma hyper_mixed_inverse_fiber (u v σ : ℂ) (hσ : σ=1 ∨ σ= -1) :
    Set.image2 (fun a b : ℂ=>a+σ*b) (arcsinhValues u) (arccoshValues v)=
      {w | ∃ r s : ℂ,r^2=1+u^2 ∧ s^2=v^2-1 ∧
        Complex.sinh w=u*v+σ*(r*s) ∧ Complex.cosh w=v*r+σ*(u*s)} := by
  ext w
  constructor
  · rintro ⟨a,ha,b,hb,rfl⟩
    change Complex.sinh a=u at ha
    change Complex.cosh b=v at hb
    refine ⟨Complex.cosh a,Complex.sinh b,?_,?_,?_,?_⟩
    · rw [Complex.cosh_sq,ha] <;> ring
    · rw [Complex.sinh_sq,hb]
    · rcases hσ with rfl|rfl <;>
        simp [Complex.sinh_add,Complex.sinh_neg,Complex.cosh_neg,ha,hb] <;> ring
    · rcases hσ with rfl|rfl <;>
        simp [Complex.cosh_add,Complex.sinh_neg,Complex.cosh_neg,ha,hb] <;> ring
  · rintro ⟨r,s,hr,hs,hw,hc⟩
    have ha:=hyper_sinh_cosh_log_lift u r hr
    let a:=Complex.log (r+u)
    refine ⟨a,ha.1,σ*(w-a),?_,?_⟩
    · change Complex.cosh (σ*(w-a))=v
      rcases hσ with rfl|rfl <;> simp only [one_mul,neg_one_mul,Complex.cosh_neg] <;>
        rw [Complex.cosh_sub,ha.1,ha.2,hw,hc] <;> linear_combination v*hr
    · rcases hσ with rfl|rfl <;> ring

/-- The logarithmic inverse sinh is a right inverse also at the cut and branch points. -/
lemma hyper_sinh_arcsinh (z:ℂ) : Complex.sinh (arcsinh z)=z := by
  exact (hyper_sinh_cosh_log_lift z (Complex.sqrt (z^2+1))
    (by rw [trig_sqrt_sq];ring)).1

/-- Rotation of Mathlib's two sine fibers preserves the integer branch parity. -/
lemma hyper_sinh_fiber_forms (A w:ℂ) :
    Complex.sinh w=Complex.sinh A ↔
      ∃ k:ℤ,w=(-1:ℂ)^k*A+(k:ℂ)*π*I := by
  have hrot : Complex.sinh w=Complex.sinh A ↔
      Complex.sin (A*I)=Complex.sin (w*I) := by
    rw [Complex.sin_mul_I,Complex.sin_mul_I]
    constructor
    · intro h;rw [h]
    · intro h
      exact (mul_right_cancel₀ Complex.I_ne_zero h).symm
  rw [hrot,Complex.sin_eq_sin_iff]
  constructor
  · rintro ⟨k,hk|hk⟩
    · have he:Even (-2*k:ℤ) := ⟨-k,by ring⟩
      refine ⟨-2*k,?_⟩
      rw [he.neg_one_zpow]
      push_cast
      linear_combination -I*hk+(w-A)*Complex.I_sq
    · have ho:Odd (-(2*k+1):ℤ) := ⟨-k-1,by ring⟩
      refine ⟨-(2*k+1),?_⟩
      rw [ho.neg_one_zpow]
      push_cast
      linear_combination -I*hk+(w+A)*Complex.I_sq
  · rintro ⟨n,hn⟩
    obtain ⟨k,hk|hk⟩:=Int.even_or_odd' n
    · have he:Even (2*k:ℤ) := ⟨k,by ring⟩
      rw [hk,he.neg_one_zpow] at hn
      refine ⟨-k,Or.inl ?_⟩
      push_cast at hn ⊢
      linear_combination I*hn+(2*k*π)*Complex.I_sq
    · have ho:Odd (2*k+1:ℤ) := ⟨k,by ring⟩
      rw [hk,ho.neg_one_zpow] at hn
      refine ⟨-k-1,Or.inr ?_⟩
      push_cast at hn ⊢
      linear_combination I*hn+((2*k+1)*π)*Complex.I_sq

/-- Rotation identifies the chosen logarithm/square-root inverse with the trigonometric one. -/
private lemma hyper_arcsinh_rotation (z:ℂ) : arcsinh z=I*arcsinPrincipal (-I*z) := by
  have hq:1-(-I*z)^2=z^2+1 := by linear_combination -z^2*Complex.I_sq
  have hi:I*(-I*z)=z := by linear_combination -z*Complex.I_sq
  unfold arcsinh arcsinPrincipal
  rw [hq,hi]
  linear_combination Complex.log (Complex.sqrt (z^2+1)+z)*Complex.I_sq

/-- Rotation maps the inverse-sinh cut plane to the inverse-sine cut plane. -/
private lemma hyper_asinh_coord {z:ℂ} (hz:z∈arcsinhDomain) : -I*z∈arcsinCutPlane := by
  simpa [arcsinhDomain,arcsinCutPlane,Complex.mul_re,Complex.mul_im] using hz

/-- The inverse-sinh derivative follows from the proved rotated inverse-sine derivative. -/
lemma hyper_hasDerivAt_arcsinh {z:ℂ} (hz:z∈arcsinhDomain) :
    HasDerivAt arcsinh (Complex.sqrt (1+z^2))⁻¹ z := by
  have hd:=((hasDerivAt_arcsin_principal (hyper_asinh_coord hz)).comp z
    ((hasDerivAt_id z).const_mul (-I))).const_mul I
  convert hd using 1
  · ext w
    exact hyper_arcsinh_rotation w
  · have hq:1-(-I*z)^2=1+z^2 := by linear_combination -z^2*Complex.I_sq
    rw [hq]
    linear_combination (Complex.sqrt (1+z^2))⁻¹*Complex.I_sq

/-- The two logarithm factors multiply to one, including the square-root cut. -/
private lemma hyper_asinh_product (z:ℂ) :
    (Complex.sqrt (z^2+1)+z)*(Complex.sqrt (z^2+1)-z)=1 := by
  linear_combination trig_sqrt_sq (z^2+1)

/-- The inverse-sinh logarithm argument is nonzero. -/
private lemma hyper_asinh_log_ne (z:ℂ) : Complex.sqrt (z^2+1)+z≠0 := by
  intro h
  have hp:=hyper_asinh_product z
  rw [h,zero_mul] at hp
  exact zero_ne_one hp

/-- The inverse-sinh logarithm argument avoids the negative real axis. -/
private lemma hyper_asinh_log_slit (z:ℂ) : Complex.sqrt (z^2+1)+z∈Complex.slitPlane := by
  let r:=Complex.sqrt (z^2+1)
  change r+z∈Complex.slitPlane
  rw [Complex.mem_slitPlane_iff]
  by_cases hi:(r+z).im≠0
  · exact Or.inr hi
  · left
    have him:r.im= -z.im := by
      have hi0:(r+z).im=0 := not_ne_iff.mp hi
      simp only [Complex.add_im] at hi0
      linarith
    have hr:0≤r.re := by
      dsimp [r]
      rw [Complex.sqrt,Complex.cpow_inv_two_re]
      positivity
    have hp:=congrArg Complex.re (hyper_asinh_product z)
    change ((r+z)*(r-z)).re=1 at hp
    simp only [Complex.mul_re,Complex.add_re,Complex.sub_re,Complex.add_im,Complex.sub_im,him] at hp
    simp only [Complex.add_re]
    nlinarith

/-- The inverse-tanh Möbius argument lies in the principal logarithm cut plane. -/
private lemma hyper_atanh_slit {z:ℂ} (hz:z∈arctanhDomain) : (1+z)/(1-z)∈Complex.slitPlane := by
  have hre:((1+z)/(1-z)).re=(1-z.re^2-z.im^2)/((1-z.re)^2+z.im^2) := by
    simp [Complex.div_re,Complex.normSq]
    ring
  have him:((1+z)/(1-z)).im=(2*z.im)/((1-z.re)^2+z.im^2) := by
    simp [Complex.div_im,Complex.normSq]
    ring
  rw [Complex.mem_slitPlane_iff]
  by_cases hi:z.im≠0
  · right
    rw [him]
    have hD:0<(1-z.re)^2+z.im^2 := add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hi)
    exact div_ne_zero (mul_ne_zero two_ne_zero hi) hD.ne'
  · left
    have hi0:z.im=0 := not_ne_iff.mp hi
    have hx:|z.re|<1 := hz.resolve_left hi
    rw [hre,hi0]
    have hp:0<1-z.re := by linarith [(abs_lt.mp hx).2]
    apply div_pos
    · nlinarith [(abs_lt.mp hx).1,(abs_lt.mp hx).2]
    · positivity

/-- Neither linear factor vanishes on the inverse-tanh cut plane. -/
private lemma hyper_atanh_nonzero {z:ℂ} (hz:z∈arctanhDomain) : 1+z≠0 ∧ 1-z≠0 := by
  constructor
  · intro h
    have he:z= -1 := by linear_combination h
    rw [he] at hz
    norm_num [arctanhDomain] at hz
  · intro h
    have he:z=1 := by linear_combination -h
    rw [he] at hz
    norm_num [arctanhDomain] at hz

/-- Differentiate the principal inverse-tanh logarithm on its full cut plane. -/
lemma hyper_hasDerivAt_arctanh {z:ℂ} (hz:z∈arctanhDomain) :
    HasDerivAt arctanh (1/(1-z^2)) z := by
  obtain ⟨hp,hm⟩:=hyper_atanh_nonzero hz
  have hd0:=((hasDerivAt_id z).const_add 1).div ((hasDerivAt_id z).const_sub 1) hm
  have hd:=((Complex.hasDerivAt_log (hyper_atanh_slit hz)).comp z hd0).div_const 2
  convert hd using 1
  · rfl
  · dsimp only [id]
    have hfac:(1+z)*(1-z)=1-z^2 := by ring
    rw [← hfac]
    field_simp [hp,hm]
    ring

/-- Inversion maps the inverse-coth cut plane into the inverse-tanh cut plane. -/
lemma hyper_acoth_inv_mem {z:ℂ} (hz:z∈arccothDomain) : z≠0 ∧ z⁻¹∈arctanhDomain := by
  have hz0:z≠0 := by intro h;rw [h] at hz;norm_num [arccothDomain] at hz
  refine ⟨hz0,?_⟩
  by_cases hi:z.im≠0
  · left
    rw [Complex.inv_im]
    have hn:Complex.normSq z≠0 := by
      rw [Complex.normSq_eq_norm_sq]
      exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hz0)
    exact div_ne_zero (neg_ne_zero.mpr hi) hn
  · right
    have hi0:z.im=0 := not_ne_iff.mp hi
    have hx:1 < |z.re| := hz.resolve_left hi
    have he:z=(z.re:ℂ) := by apply Complex.ext <;> simp [hi0]
    rw [he,← Complex.ofReal_inv,Complex.ofReal_re,abs_inv]
    exact inv_lt_one_of_one_lt₀ hx

/-- The principal complex square root agrees with the nonnegative real square root. -/
lemma hyper_sqrt_ofReal (x:ℝ) (hx:0≤x) : Complex.sqrt (x:ℂ)=(Real.sqrt x:ℂ) := by
  exact Complex.sqrt_of_nonneg (by exact_mod_cast hx)

/-- Analyticity of the principal inverse on precisely its open cut domain. -/
theorem arcsinh_analytic  : AnalyticOnNhd ℂ arcsinh arcsinhDomain := by
  have hU:IsOpen arcsinhDomain := by
    change IsOpen ({z:ℂ | z.re≠0}∪{z:ℂ | |z.im|<1})
    exact (isOpen_ne.preimage Complex.continuous_re).union
      (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const)
  exact (show DifferentiableOn ℂ arcsinh arcsinhDomain from fun z hz=>
    (hyper_hasDerivAt_arcsinh hz).differentiableAt.differentiableWithinAt).analyticOnNhd hU

/-- Both linear factors of the factored inverse-cosh root lie in the principal slit plane. -/
lemma hypR4_acosh_slit {z : ℂ} (hz : z ∈ arccoshDomain) :
    z-1 ∈ Complex.slitPlane ∧ z+1 ∈ Complex.slitPlane := by
  rcases hz with hi | hr
  · exact ⟨Or.inr (by simpa using hi), Or.inr (by simpa using hi)⟩
  · exact ⟨Or.inl (by simp; linarith), Or.inl (by simp; linarith)⟩

/-- The factored inverse-cosh root does not vanish on the open domain. -/
lemma hypR4_acosh_root_ne {z : ℂ} (hz : z ∈ arccoshDomain) :
    Complex.sqrt (z-1)*Complex.sqrt (z+1) ≠ 0 := by
  intro h
  have hs := hyper_arccosh_root_sq z
  rw [h, zero_pow two_ne_zero] at hs
  have h1 : (z-1)*(z+1) = 0 := by linear_combination -hs
  rcases mul_eq_zero.mp h1 with h1 | h1
  · have : z = 1 := by linear_combination h1
    subst this; rcases hz with h | h <;> simp at h
  · have : z = -1 := by linear_combination h1
    subst this; rcases hz with h | h <;> norm_num at h

/-- The inverse-cosh logarithm argument lies in the principal slit plane on the open domain. -/
private lemma hypR4_acosh_log_slit {z : ℂ} (hz : z ∈ arccoshDomain) :
    z+Complex.sqrt (z-1)*Complex.sqrt (z+1) ∈ Complex.slitPlane := by
  set s := Complex.sqrt (z-1)*Complex.sqrt (z+1)
  have hprod : (z+s)*(z-s) = 1 := by
    have := hyper_arccosh_root_sq z; linear_combination -this
  rw [Complex.mem_slitPlane_iff]
  by_contra hcon
  push Not at hcon
  obtain ⟨hre, him⟩ := hcon
  have hre' := congrArg Complex.re hprod
  have him' := congrArg Complex.im hprod
  simp only [Complex.mul_re, Complex.mul_im, him, Complex.one_re, Complex.one_im] at hre' him'
  simp only [sub_zero, zero_mul, add_zero] at hre' him'
  have hg0 : (z+s).re ≠ 0 := by intro h; rw [h, zero_mul] at hre'; exact zero_ne_one hre'
  have hh_im : (z-s).im = 0 := by
    rcases mul_eq_zero.mp him' with h | h
    · exact absurd h hg0
    · exact h
  have hgneg : (z+s).re < 0 := lt_of_le_of_ne hre hg0
  have hh_re : (z-s).re < 0 := by
    by_contra hc; push Not at hc; nlinarith
  have hzre : z.re = ((z+s).re + (z-s).re)/2 := by simp
  have hzim : z.im = ((z+s).im + (z-s).im)/2 := by simp
  rcases hz with hi | hr
  · apply hi; rw [hzim, him, hh_im]; ring
  · linarith

/-- The derivative of the principal inverse cosh on its open domain. -/
lemma hypR4_hasDerivAt_arccosh {z : ℂ} (hz : z ∈ arccoshDomain) :
    HasDerivAt arccosh ((Complex.sqrt (z-1)*Complex.sqrt (z+1))⁻¹) z := by
  obtain ⟨h1, h2⟩ := hypR4_acosh_slit hz
  have hs := hypR4_acosh_root_ne hz
  have hg := hypR4_acosh_log_slit hz
  have hA : Complex.sqrt (z-1) ≠ 0 := fun h => hs (by rw [h, zero_mul])
  have hB : Complex.sqrt (z+1) ≠ 0 := fun h => hs (by rw [h, mul_zero])
  have dA : HasDerivAt (fun w => Complex.sqrt (w-1)) ((Complex.sqrt (z-1))⁻¹/2) z := by
    have := (Complex.hasDerivAt_sqrt h1).comp z ((hasDerivAt_id z).sub_const 1)
    simpa only [Complex.sqrt, show (-1/2:ℂ) = -(2⁻¹:ℂ) by norm_num, Complex.cpow_neg, mul_one,
      Function.comp_def, id] using this
  have dB : HasDerivAt (fun w => Complex.sqrt (w+1)) ((Complex.sqrt (z+1))⁻¹/2) z := by
    have := (Complex.hasDerivAt_sqrt h2).comp z ((hasDerivAt_id z).add_const 1)
    simpa only [Complex.sqrt, show (-1/2:ℂ) = -(2⁻¹:ℂ) by norm_num, Complex.cpow_neg, mul_one,
      Function.comp_def, id] using this
  have hd := (Complex.hasDerivAt_log hg).comp z ((hasDerivAt_id z).add (dA.mul dB))
  have hg0 : z+Complex.sqrt (z-1)*Complex.sqrt (z+1) ≠ 0 := Complex.slitPlane_ne_zero hg
  have key : (z+Complex.sqrt (z-1)*Complex.sqrt (z+1))⁻¹ *
      (1 + ((Complex.sqrt (z-1))⁻¹/2*Complex.sqrt (z+1) + Complex.sqrt (z-1)*((Complex.sqrt (z+1))⁻¹/2)))
      = (Complex.sqrt (z-1)*Complex.sqrt (z+1))⁻¹ := by
    have eA := trig_sqrt_sq (z-1)
    have eB := trig_sqrt_sq (z+1)
    generalize Complex.sqrt (z-1) = A at *
    generalize Complex.sqrt (z+1) = B at *
    field_simp
    linear_combination eA + eB
  rw [← key]
  exact hd

/-- Analyticity of the principal inverse on precisely its open cut domain. -/
theorem arccosh_analytic  : AnalyticOnNhd ℂ arccosh arccoshDomain := by
  have hU : IsOpen arccoshDomain := by
    change IsOpen ({z:ℂ | z.im≠0}∪{z:ℂ | 1<z.re})
    exact (isOpen_ne.preimage Complex.continuous_im).union
      (isOpen_lt continuous_const Complex.continuous_re)
  exact (show DifferentiableOn ℂ arccosh arccoshDomain from fun z hz =>
    (hypR4_hasDerivAt_arccosh hz).differentiableAt.differentiableWithinAt).analyticOnNhd hU

/-- Analyticity of the principal inverse on precisely its open cut domain. -/
theorem arctanh_analytic  : AnalyticOnNhd ℂ arctanh arctanhDomain := by
  have hU:IsOpen arctanhDomain := by
    change IsOpen ({z:ℂ | z.im≠0}∪{z:ℂ | |z.re|<1})
    exact (isOpen_ne.preimage Complex.continuous_im).union
      (isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const)
  exact (show DifferentiableOn ℂ arctanh arctanhDomain from fun z hz=>
    (hyper_hasDerivAt_arctanh hz).differentiableAt.differentiableWithinAt).analyticOnNhd hU

/-- Analyticity of the principal inverse on precisely its open cut domain. -/
theorem arccsch_analytic  : AnalyticOnNhd ℂ arccsch arccschDomain := by
  intro z hz
  exact (arcsinh_analytic _ hz.2).comp (analyticAt_id.inv hz.1)

/-- Analyticity of the principal inverse on precisely its open cut domain. -/
theorem arcsech_analytic  : AnalyticOnNhd ℂ arcsech arcsechDomain := by
  intro z hz
  exact (arccosh_analytic _ hz.2).comp (analyticAt_id.inv hz.1)

/-- Analyticity of the principal inverse on precisely its open cut domain. -/
theorem arccoth_analytic  : AnalyticOnNhd ℂ arccoth arccothDomain := by
  intro z hz
  obtain ⟨hz0,hi⟩:=hyper_acoth_inv_mem hz
  have hh:AnalyticAt ℂ (fun w=>arctanh w⁻¹) z :=
    (arctanh_analytic _ hi).comp (analyticAt_id.inv hz0)
  apply hh.congr
  filter_upwards [eventually_ne_nhds hz0] with w hw
  exact (arccoth_eq_inv hw).symm

/-- A right inverse `g (f z) = z` of an entire `g` cannot be analytic at a point where `g'` vanishes. -/
private lemma hypR4_not_analytic_of_right_inv {f g g' : ℂ → ℂ} {p : ℂ}
    (hinv : ∀ z, g (f z) = z) (hg : ∀ w, HasDerivAt g (g' w) w) (h0 : g' (f p) = 0) :
    ¬AnalyticAt ℂ f p := by
  intro ha
  have hd := (hg (f p)).comp p ha.differentiableAt.hasDerivAt
  have hid : HasDerivAt (g ∘ f) 1 p := by
    have : g ∘ f = id := funext hinv
    rw [this]; exact hasDerivAt_id p
  have := hd.unique hid
  rw [h0, zero_mul] at this
  exact zero_ne_one this

/-- The principal inverse tanh is not continuous at `±1`, where `exp (2 arctanh z)` has a pole
or a zero. -/
lemma hypR4_arctanh_exp (z : ℂ) (h1 : z ≠ 1) (h2 : z ≠ -1) :
    Complex.exp (2*arctanh z)*(1-z) = 1+z := by
  have hm : 1-z ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have hp : 1+z ≠ 0 := by intro h; apply h2; linear_combination h
  rw [arctanh, show 2*(Complex.log ((1+z)/(1-z))/2) = Complex.log ((1+z)/(1-z)) by ring,
    Complex.exp_log (div_ne_zero hp hm)]
  field_simp

/-- The two inverse branch points stated in the definition prose. -/
theorem arcsinh_branch_points  : ¬AnalyticAt ℂ arcsinh I ∧ ¬AnalyticAt ℂ arcsinh (-I) := by
  have hc : ∀ w, Complex.cosh (arcsinh w)^2 = 1+w^2 := fun w => by
    rw [Complex.cosh_sq, hyper_sinh_arcsinh]; ring
  constructor
  · refine hypR4_not_analytic_of_right_inv hyper_sinh_arcsinh Complex.hasDerivAt_sinh ?_
    have := hc I; rw [Complex.I_sq] at this
    exact pow_eq_zero_iff two_ne_zero |>.mp (by rw [this]; ring)
  · refine hypR4_not_analytic_of_right_inv hyper_sinh_arcsinh Complex.hasDerivAt_sinh ?_
    have := hc (-I); rw [neg_sq, Complex.I_sq] at this
    exact pow_eq_zero_iff two_ne_zero |>.mp (by rw [this]; ring)

/-- The two inverse branch points stated in the definition prose. -/
theorem arccosh_branch_points  : ¬AnalyticAt ℂ arccosh (1:ℂ) ∧ ¬AnalyticAt ℂ arccosh (-(1:ℂ)) := by
  have hc : ∀ w, Complex.sinh (arccosh w)^2 = w^2-1 := fun w => by
    rw [Complex.sinh_sq, hyper_cosh_arccosh]
  constructor
  · refine hypR4_not_analytic_of_right_inv hyper_cosh_arccosh Complex.hasDerivAt_cosh ?_
    exact pow_eq_zero_iff two_ne_zero |>.mp (by rw [hc]; ring)
  · refine hypR4_not_analytic_of_right_inv hyper_cosh_arccosh Complex.hasDerivAt_cosh ?_
    exact pow_eq_zero_iff two_ne_zero |>.mp (by rw [hc]; ring)

/-- The two inverse branch points stated in the definition prose. -/
theorem arctanh_branch_points  : ¬AnalyticAt ℂ arctanh (1:ℂ) ∧ ¬AnalyticAt ℂ arctanh (-(1:ℂ)) := by
  constructor
  · intro ha
    have hcont : ContinuousAt (fun z => Complex.exp (2*arctanh z)*(1-z)) 1 :=
      ((ha.continuousAt.const_mul 2).cexp).mul (continuousAt_const.sub continuousAt_id)
    have hlim : Tendsto (fun z => Complex.exp (2*arctanh z)*(1-z)) (𝓝[≠] 1) (𝓝 0) := by
      have := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := {(1:ℂ)}ᶜ))
      simpa using this
    have hlim2 : Tendsto (fun z => Complex.exp (2*arctanh z)*(1-z)) (𝓝[≠] 1) (𝓝 2) := by
      have h : Tendsto (fun z : ℂ => 1+z) (𝓝[≠] 1) (𝓝 2) := by
        have : Tendsto (fun z:ℂ => 1+z) (𝓝 1) (𝓝 (1+1)) := tendsto_const_nhds.add tendsto_id
        norm_num at this
        exact this.mono_left nhdsWithin_le_nhds
      refine h.congr' ?_
      have hne : ∀ᶠ z in 𝓝[≠] (1:ℂ), z ≠ -1 := by
        apply eventually_nhdsWithin_of_eventually_nhds
        exact eventually_ne_nhds (by norm_num)
      filter_upwards [self_mem_nhdsWithin, hne] with z hz hz'
      exact (hypR4_arctanh_exp z hz hz').symm
    have := tendsto_nhds_unique hlim hlim2
    norm_num at this
  · intro ha
    have hcont : ContinuousAt (fun z => Complex.exp (-(2*arctanh z))*(1+z)) (-1) :=
      ((ha.continuousAt.const_mul 2).neg.cexp).mul (continuousAt_const.add continuousAt_id)
    have hlim : Tendsto (fun z => Complex.exp (-(2*arctanh z))*(1+z)) (𝓝[≠] (-1)) (𝓝 0) := by
      have := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := {(-1:ℂ)}ᶜ))
      simpa using this
    have hlim2 : Tendsto (fun z => Complex.exp (-(2*arctanh z))*(1+z)) (𝓝[≠] (-1)) (𝓝 2) := by
      have h : Tendsto (fun z : ℂ => 1-z) (𝓝[≠] (-1)) (𝓝 2) := by
        have : Tendsto (fun z:ℂ => 1-z) (𝓝 (-1)) (𝓝 (1-(-1))) := tendsto_const_nhds.sub tendsto_id
        norm_num at this
        exact this.mono_left nhdsWithin_le_nhds
      refine h.congr' ?_
      have hne : ∀ᶠ z in 𝓝[≠] (-1:ℂ), z ≠ 1 := by
        apply eventually_nhdsWithin_of_eventually_nhds
        exact eventually_ne_nhds (by norm_num)
      filter_upwards [self_mem_nhdsWithin, hne] with z hz hz'
      have e := hypR4_arctanh_exp z hz' hz
      have hm : 1-z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz')
      rw [Complex.exp_neg]
      have hE : Complex.exp (2*arctanh z) ≠ 0 := Complex.exp_ne_zero _
      field_simp
      linear_combination e
    have := tendsto_nhds_unique hlim hlim2
    norm_num at this

/-- The two inverse branch points stated in the definition prose. -/
theorem arccsch_branch_points  : ¬AnalyticAt ℂ arccsch I ∧ ¬AnalyticAt ℂ arccsch (-I) := by
  have hrel : ∀ w : ℂ, arcsinh w = arccsch w⁻¹ := fun w => by simp [arccsch]
  have key : ∀ p : ℂ, p ≠ 0 → AnalyticAt ℂ arccsch p⁻¹ → AnalyticAt ℂ arcsinh p := by
    intro p hp ha
    have := ha.comp (analyticAt_id.inv hp)
    simpa [Function.comp_def, ← hrel] using this
  constructor
  · intro ha
    exact arcsinh_branch_points.2 (key (-I) (by simp) (by simpa using ha))
  · intro ha
    exact arcsinh_branch_points.1 (key I Complex.I_ne_zero (by simpa using ha))

/-- The two inverse branch points stated in the definition prose. -/
theorem arcsech_branch_points  : ¬AnalyticAt ℂ arcsech (1:ℂ) ∧ ¬AnalyticAt ℂ arcsech (-(1:ℂ)) := by
  have hrel : ∀ w : ℂ, arccosh w = arcsech w⁻¹ := fun w => by simp [arcsech]
  have key : ∀ p : ℂ, p ≠ 0 → AnalyticAt ℂ arcsech p⁻¹ → AnalyticAt ℂ arccosh p := by
    intro p hp ha
    have := ha.comp (analyticAt_id.inv hp)
    simpa [Function.comp_def, ← hrel] using this
  constructor
  · intro ha
    exact arccosh_branch_points.1 (key 1 one_ne_zero (by simpa using ha))
  · intro ha
    exact arccosh_branch_points.2 (key (-1) (by norm_num) (by simpa using ha))

/-- The two inverse branch points stated in the definition prose. -/
theorem arccoth_branch_points  : ¬AnalyticAt ℂ arccoth (1:ℂ) ∧ ¬AnalyticAt ℂ arccoth (-(1:ℂ)) := by
  have key : ∀ p : ℂ, p ≠ 0 → AnalyticAt ℂ arccoth p⁻¹ → AnalyticAt ℂ arctanh p := by
    intro p hp ha
    have h := ha.comp (analyticAt_id.inv hp)
    apply h.congr
    filter_upwards [eventually_ne_nhds hp] with w hw
    simp [arccoth_eq_inv (inv_ne_zero hw)]
  constructor
  · intro ha
    exact arctanh_branch_points.1 (key 1 one_ne_zero (by simpa using ha))
  · intro ha
    exact arctanh_branch_points.2 (key (-1) (by norm_num) (by simpa using ha))

/-- Reality and agreement with the existing real inverse on the uncut real interval. -/
theorem arcsinh_ofReal (x : ℝ)  : arcsinh x=(Real.arsinh x:ℂ) := by
  have hq:Complex.sqrt ((x:ℂ)^2+1)=(Real.sqrt (1+x^2):ℂ) := by
    rw [show (x:ℂ)^2+1=((1+x^2:ℝ):ℂ) by push_cast;ring]
    exact hyper_sqrt_ofReal _ (by positivity)
  have hp:0≤x+Real.sqrt (1+x^2) := by
    apply le_of_lt
    rw [← neg_lt_iff_pos_add']
    apply Real.lt_sqrt_of_sq_lt
    nlinarith
  rw [arcsinh,hq,Real.arsinh]
  rw [← Complex.ofReal_add,add_comm (Real.sqrt (1+x^2)) x,← Complex.ofReal_log hp]

/-- Reality and agreement with the existing real inverse on the uncut real interval. -/
theorem arccosh_ofReal (x : ℝ) (hx : 1≤x) : arccosh x=(Real.arcosh x:ℂ) := by
  have h1 : Complex.sqrt ((x:ℂ)-1) = (Real.sqrt (x-1):ℂ) := by
    rw [show (x:ℂ)-1 = ((x-1:ℝ):ℂ) by push_cast; ring]; exact hyper_sqrt_ofReal _ (by linarith)
  have h2 : Complex.sqrt ((x:ℂ)+1) = (Real.sqrt (x+1):ℂ) := by
    rw [show (x:ℂ)+1 = ((x+1:ℝ):ℂ) by push_cast; ring]; exact hyper_sqrt_ofReal _ (by linarith)
  rw [arccosh, h1, h2, ← Complex.ofReal_mul, ← Real.sqrt_mul (by linarith),
    show (x-1)*(x+1) = x^2-1 by ring, ← Complex.ofReal_add,
    ← Complex.ofReal_log (by positivity), Real.arcosh]

/-- Reality and agreement with the existing real inverse on the uncut real interval. -/
theorem arctanh_ofReal (x : ℝ) (hx : |x|<1) : arctanh x=(Real.artanh x:ℂ) := by
  have hxp:0<1+x := by linarith [(abs_lt.mp hx).1]
  have hxm:0<1-x := by linarith [(abs_lt.mp hx).2]
  have hp:0≤(1+x)/(1-x) := (div_pos hxp hxm).le
  have harg:(1+(x:ℂ))/(1-(x:ℂ))=(((1+x)/(1-x):ℝ):ℂ) := by push_cast;rfl
  rw [arctanh,harg,← Complex.ofReal_log hp,Real.artanh_eq_half_log (mem_Icc_of_Ioo (abs_lt.mp hx))]
  push_cast
  ring

/-- Oddness on the open cut plane; cut-side values are given separately. -/
@[dlmf 4.37.E10]
theorem arcsinh_neg (z : ℂ) : arcsinh (-z)= -arcsinh z := by
  have hn:Complex.sqrt ((-z)^2+1)+(-z)=(Complex.sqrt (z^2+1)+z)⁻¹ := by
    apply mul_left_cancel₀ (hyper_asinh_log_ne z)
    rw [mul_inv_cancel₀ (hyper_asinh_log_ne z)]
    convert hyper_asinh_product z using 1 <;> ring
  unfold arcsinh
  rw [hn,Complex.log_inv _ (Complex.mem_slitPlane_iff_arg.mp (hyper_asinh_log_slit z)).1]

/-- Oddness on the open cut plane; cut-side values are given separately. -/
@[dlmf 4.37.E12]
theorem arctanh_neg {z : ℂ} (hz : z ∈ arctanhDomain) : arctanh (-z)= -arctanh z := by
  have hn:(1+(-z))/(1-(-z))=((1+z)/(1-z))⁻¹ := by
    simp only [sub_eq_add_neg,inv_div,neg_neg]
  unfold arctanh
  rw [hn,Complex.log_inv _ (Complex.mem_slitPlane_iff_arg.mp (hyper_atanh_slit hz)).1]
  ring

/-- Oddness on the open cut plane; cut-side values are given separately. -/
@[dlmf 4.37.E13]
theorem arccsch_neg (z : ℂ) : arccsch (-z)= -arccsch z := by
  unfold arccsch
  rw [inv_neg,arcsinh_neg]

/-- Oddness on the open cut plane; cut-side values are given separately. -/
@[dlmf 4.37.E15]
theorem arccoth_neg {z : ℂ} (hz : z ∈ arccothDomain) : arccoth (-z)= -arccoth z := by
  obtain ⟨hz0,hi⟩:=hyper_acoth_inv_mem hz
  rw [arccoth_eq_inv (neg_ne_zero.mpr hz0),arccoth_eq_inv hz0,inv_neg,arctanh_neg hi]

end DLMF.Elementary
end
