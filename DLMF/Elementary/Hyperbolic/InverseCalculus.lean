/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Elementary.Basic.InverseHyperbolic
public import DLMF.Elementary.Hyperbolic.Products
public import DLMF.Elementary.PathLifts

/-!
# Inverse hyperbolic functions: path integrals

This file characterizes the multivalued inverse hyperbolic functions by path integrals
(DLMF 4.37.1–4.37.3) and relates the reciprocal inverses to the direct ones.

## Main definitions

* `IsArcsinhPathValue`, `IsArccoshPathValue`, `IsArctanhPathValue`: path-integral values with
  continued square-root or logarithm branches.

## Main results

* `arcsinh_path_values`, `arccosh_path_values`, `arctanh_path_values`: the multivalued inverses
  as sets of path-integral values (DLMF 4.37.1–4.37.3).
* `arccsch_values_inv`, `arcsech_values_inv`, `arccoth_values_inv`: DLMF 4.37.4–4.37.6.

## Implementation notes

The analyticity, branch points, reality on the real axis and oddness of the principal inverses
are in `DLMF.Elementary.Basic.InverseHyperbolic`.
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
theorem arcsinh_path_values {z : ℂ} (hz : z≠I ∧ z≠ -I) :
    {w | IsArcsinhPathValue z w}=arcsinhValues z := by
  ext w
  simp only [mem_ofPred_eq, arcsinhValues]
  constructor
  · rintro ⟨γ, r, hγ, h0, h1, hr, hr0, hh, -, hint⟩
    have hrr : ∀ t ∈ Icc (0 : ℝ) 1, r t ≠ 0 ∧ r t ^ 2 = 1 - (I * γ t) ^ 2 := by
      intro t ht
      obtain ⟨hp, hm, hs⟩ := hh t ht
      refine ⟨fun h0 => ?_, by rw [hs]; linear_combination (γ t ^ 2) * I_sq⟩
      rw [h0] at hs
      have : (γ t - I) * (γ t + I) = 0 := by linear_combination -hs - I_sq
      rcases mul_eq_zero.mp this with h | h
      · exact hp (sub_eq_zero.mp h)
      · exact hm (eq_neg_of_add_eq_zero_left h)
    have hs := (sin_of_arcsin_lift (z := I * z) (contDiffOn_const.mul hγ) (by simp [h0])
      (by simp [h1]) hr hr0 hrr).2
    simp only [deriv_const_mul_field', mul_div_assoc, intervalIntegral.integral_const_mul,
      hint] at hs
    rw [mul_comm, Complex.sin_mul_I] at hs
    exact mul_right_cancel₀ I_ne_zero (hs.trans (mul_comm _ _))
  · intro hw
    have hzI : z * I ≠ 1 := fun h => hz.2 (by linear_combination (-I) * h + z * I_sq)
    have hzI' : z * I ≠ -1 := fun h => hz.1 (by linear_combination (-I) * h + z * I_sq)
    have hsw : Complex.sin (w * I) = z * I := by rw [Complex.sin_mul_I, hw]
    obtain ⟨hcd, hc, hint⟩ := arcsin_lift_exists hzI hzI' hsw
    set D := pathDetour (w * I) (pathDetourSign (w * I))
    have hrr : ∀ t ∈ Icc (0 : ℝ) 1, Complex.cos (D t) ≠ 0 ∧
        Complex.cos (D t) ^ 2 = 1 - Complex.sin (D t) ^ 2 :=
      fun t ht => ⟨hc t ht, Complex.cos_sq' _⟩
    have hcr : ContinuousOn (fun t => Complex.cos (D t)) (Icc 0 1) :=
      (Complex.continuous_cos.comp (contDiff_pathDetour _ _).continuous).continuousOn
    have hi := (sin_of_arcsin_lift (z := z * I) hcd (by simp [D]) (by simp [D, hsw]) hcr
      (by simp [D]) hrr).1
    have hder : deriv (fun t => -I * Complex.sin (D t)) =
        fun t => -I * deriv (fun t => Complex.sin (D t)) t := deriv_const_mul_field' _
    refine ⟨fun t => -I * Complex.sin (D t), fun t => Complex.cos (D t),
      contDiffOn_const.mul hcd, by simp [D], ?_, hcr, by simp [D], fun t ht => ?_, ?_, ?_⟩
    · simp only [D, pathDetour_one, hsw]; linear_combination (-z) * I_sq
    · have hsq : Complex.cos (D t) ^ 2 = 1 + (-I * Complex.sin (D t)) ^ 2 := by
        rw [Complex.cos_sq']; linear_combination (-Complex.sin (D t) ^ 2) * I_sq
      refine ⟨fun h => hc t ht ?_, fun h => hc t ht ?_, hsq⟩ <;>
      · beta_reduce at h
        rw [h] at hsq
        have : Complex.cos (D t) ^ 2 = 0 := by linear_combination hsq + I_sq
        exact pow_eq_zero_iff two_ne_zero |>.mp this
    · rw [hder]
      simpa only [mul_div_assoc] using hi.const_mul (-I)
    · rw [hder]
      simp only [mul_div_assoc, intervalIntegral.integral_const_mul, hint]
      linear_combination (-w) * I_sq

/-- The multivalued inverse defined by all admissible continued-branch path integrals. -/
@[dlmf 4.37.E2]
theorem arccosh_path_values {z : ℂ} (hz : z≠1 ∧ z≠ -1) :
    {w | IsArccoshPathValue z w}=arccoshValues z := by
  sorry

/-- The multivalued inverse defined by all admissible continued-branch path integrals.
Stronger than DLMF, which assumes `z ≠ ±1`. -/
@[dlmf 4.37.E3]
theorem arctanh_path_values' {z : ℂ} :
    {w | IsArctanhPathValue z w}=arctanhValues z := by
  ext w
  simp only [mem_ofPred_eq, arctanhValues]
  constructor
  · rintro ⟨γ, hγ, h0, h1, hh, -, hint⟩
    have hI : ∀ t ∈ Icc (0 : ℝ) 1, I * γ t ≠ I ∧ I * γ t ≠ -I := by
      intro t ht
      refine ⟨fun h => (hh t ht).1 ?_, fun h => (hh t ht).2 ?_⟩
      · exact mul_left_cancel₀ I_ne_zero (h.trans (mul_one I).symm)
      · exact mul_left_cancel₀ I_ne_zero (h.trans (by ring))
    obtain ⟨-, hc, ht⟩ := tan_of_arctan_lift (z := I * z) (contDiffOn_const.mul hγ) (by simp [h0])
      (by simp [h1]) hI
    have he : ∀ t, deriv (fun t => I * γ t) t / (1 + (I * γ t) ^ 2) =
        I * (deriv γ t / (1 - γ t ^ 2)) := by
      intro t
      rw [deriv_const_mul_field, mul_div_assoc, mul_pow, I_sq]; ring_nf
    simp only [he, intervalIntegral.integral_const_mul, hint] at hc ht
    rw [mul_comm, Complex.cos_mul_I] at hc
    rw [mul_comm, Complex.tan_mul_I] at ht
    exact ⟨hc, mul_right_cancel₀ I_ne_zero (ht.trans (mul_comm _ _))⟩
  · rintro ⟨hc, ht⟩
    have hcw : Complex.cos (w * I) ≠ 0 := by rwa [Complex.cos_mul_I]
    have htw : Complex.tan (w * I) = z * I := by rw [Complex.tan_mul_I, ht]
    obtain ⟨hcd, hI, hint⟩ := arctan_lift_exists hcw
    set D := pathDetour (w * I) (pathDetourSign (w * I))
    have hi := (tan_of_arctan_lift (z := z * I) hcd (by simp [D]) (by simp [D, htw]) hI).1
    have he : ∀ t, deriv (fun t => -I * Complex.tan (D t)) t /
        (1 - (-I * Complex.tan (D t)) ^ 2) =
        -I * (deriv (fun t => Complex.tan (D t)) t / (1 + Complex.tan (D t) ^ 2)) := by
      intro t
      rw [deriv_const_mul_field, mul_div_assoc, mul_pow, neg_sq, I_sq]; ring_nf
    refine ⟨fun t => -I * Complex.tan (D t), contDiffOn_const.mul hcd, by simp [D], ?_,
      fun t ht => ?_, ?_, ?_⟩
    · simp only [D, pathDetour_one, htw]; linear_combination (-z) * I_sq
    · refine ⟨fun h => (hI t ht).1 ?_, fun h => (hI t ht).2 ?_⟩
      · linear_combination I * h + Complex.tan (D t) * I_sq
      · linear_combination I * h + Complex.tan (D t) * I_sq
    · simp only [he]
      exact hi.const_mul (-I)
    · simp only [he, intervalIntegral.integral_const_mul, hint]
      linear_combination (-w) * I_sq

/-- The multivalued inverse defined by all admissible continued-branch path integrals. -/
@[dlmf 4.37.E3]
theorem arctanh_path_values {z : ℂ} (_hz : z≠1 ∧ z≠ -1) :
    {w | IsArctanhPathValue z w}=arctanhValues z :=
  arctanh_path_values'

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

end DLMF.Elementary
end
