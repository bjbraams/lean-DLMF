/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Elementary.Basic.InverseHyperbolic
public import DLMF.Elementary.Hyperbolic.Products

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
