/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Arcosh
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Analysis.SpecialFunctions.Artanh
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The Gudermannian function

This file defines the Gudermannian function and its inverse by their integrals
(DLMF 4.23.39, 4.23.41) and proves their elementary closed forms and that they are mutually
inverse (DLMF §4.23(viii)).

## Main definitions

* `gudermannian`: the Gudermannian `gd x = ∫₀ˣ sech t dt` (DLMF 4.23.39).
* `inverseGudermannian`: its inverse `∫₀ˣ sec t dt` on `(-π/2, π/2)` (DLMF 4.23.41).

## Main results

* `gudermannian_elementary`, `gudermannian_reciprocal`, `gudermannian_nonneg_cosine`:
  DLMF 4.23.40.
* `inverse_gudermannian_elementary`, `inverse_gudermannian_reciprocal`,
  `inverse_gudermannian_nonneg_cosh`: DLMF 4.23.42.
* `gudermannian_inverse`: the two functions are mutually inverse (DLMF §4.23(viii)).
* `gudermannian_zero`, `gudermannian_neg`: `gd 0 = 0` and oddness.

## Implementation notes

The principal arccosine and secant forms of the Gudermannian, and the arccosh and arcsech forms
of its inverse, require a nonnegative argument; these sign conditions correct the displayed
formulas.
-/

@[expose] public noncomputable section

open Set

open scoped Real

namespace DLMF.Elementary

/-- The Gudermannian, real and odd on the full real line. -/
@[dlmf 4.23.E39]
def gudermannian (x : ℝ) : ℝ := ∫ t in (0:ℝ)..x,(Real.cosh t)⁻¹

/-- The inverse Gudermannian on the open strip (-pi/2,pi/2). -/
@[dlmf 4.23.E41]
def inverseGudermannian (x : ℝ) : ℝ := ∫ t in (0:ℝ)..x,(Real.cos t)⁻¹

/-- Identity under the stated parameter and domain assumptions: `gudermannian x=f x`. -/
private lemma Trigonometric.gudermannian_integral {f:ℝ→ℝ}
    (hf:∀x,HasDerivAt f (Real.cosh x)⁻¹ x) (h0:f 0=0) (x:ℝ) : gudermannian x=f x := by
  have hc:Continuous (fun t:ℝ=>(Real.cosh t)⁻¹) :=
    Real.continuous_cosh.inv₀ (fun t=>(Real.cosh_pos t).ne')
  rw [gudermannian,intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _=>hf t)
      (hc.intervalIntegrable 0 x),h0,sub_zero]

/-- Identity under the stated parameter and domain assumptions: `Real.sqrt (1-(Real.tanh
x)^2)=(Real.cosh x)⁻¹`. -/
private lemma Trigonometric.sqrt_one_sub_tanh (x:ℝ) :
    Real.sqrt (1-(Real.tanh x)^2)=(Real.cosh x)⁻¹ := by
  have hc:0<Real.cosh x := Real.cosh_pos x
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (inv_nonneg.mpr hc.le)).mp
  rw [Real.sq_sqrt (by linarith [Real.tanh_sq_lt_one x]),Real.tanh_eq_sinh_div_cosh]
  field_simp
  linear_combination Real.cosh_sq_sub_sinh_sq x

/-- Identity under the stated parameter and domain assumptions: `Real.sqrt (1+(Real.tan
x)^2)=(Real.cos x)⁻¹`. -/
private lemma Trigonometric.sqrt_one_add_tan {x:ℝ} (hx:|x|<π/2) :
    Real.sqrt (1+(Real.tan x)^2)=(Real.cos x)⁻¹ := by
  simpa only [inv_inv] using congrArg Inv.inv
    (Real.inv_sqrt_one_add_tan_sq (Real.cos_pos_of_mem_Ioo (abs_lt.mp hx)))

/-- Identity under the stated parameter and domain assumptions: `inverseGudermannian x=f x`. -/
private lemma Trigonometric.inverse_gudermannian_integral {f:ℝ→ℝ}
    (hf:∀t,|t|<π/2→HasDerivAt f (Real.cos t)⁻¹ t) (h0:f 0=0)
    {x:ℝ} (hx:|x|<π/2) : inverseGudermannian x=f x := by
  have hmem:∀t∈uIcc (0:ℝ) x,|t|<π/2 := by
    intro t ht
    apply abs_lt.mpr
    rcases le_total 0 x with h|h
    · rw [uIcc_of_le h] at ht
      exact ⟨by linarith [ht.1,Real.pi_pos],by linarith [ht.2,(abs_lt.mp hx).2]⟩
    · rw [uIcc_of_ge h] at ht
      exact ⟨by linarith [ht.1,(abs_lt.mp hx).1],by linarith [ht.2,Real.pi_pos]⟩
  have hcos:∀t∈uIcc (0:ℝ) x,Real.cos t≠0 := fun t ht=>
    (Real.cos_pos_of_mem_Ioo (abs_lt.mp (hmem t ht))).ne'
  have hc:ContinuousOn (fun t:ℝ=>(Real.cos t)⁻¹) (uIcc 0 x) :=
    Real.continuous_cos.continuousOn.inv₀ hcos
  rw [inverseGudermannian,intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht=>hf t (hmem t ht)) hc.intervalIntegrable,h0,sub_zero]

/-- Identity under the stated parameter and domain assumptions: `inverseGudermannian x=Real.arsinh
(Real.tan x)`. -/
private lemma Trigonometric.inverse_gudermannian_arsinh {x:ℝ} (hx:|x|<π/2) :
    inverseGudermannian x=Real.arsinh (Real.tan x) := by
  refine Trigonometric.inverse_gudermannian_integral (f:=fun t=>Real.arsinh (Real.tan t)) ?_ ?_ hx
  · intro t ht
    have hc:Real.cos t≠0 := (Real.cos_pos_of_mem_Ioo (abs_lt.mp ht)).ne'
    have hd:=(Real.hasDerivAt_tan hc).arsinh
    convert hd using 1
    rw [smul_eq_mul,Trigonometric.sqrt_one_add_tan ht]
    field_simp
  · simp

/-- DLMF 4.23.E40: gudermannian elementary. -/
@[dlmf 4.23.E40]
theorem gudermannian_elementary (x : ℝ) :
    gudermannian x=2*Real.arctan (Real.exp x)-π/2 ∧
    gudermannian x=Real.arcsin (Real.tanh x) ∧
    gudermannian x=Real.arctan (Real.sinh x) := by
  have he: gudermannian x=2*Real.arctan (Real.exp x)-π/2 := by
    apply Trigonometric.gudermannian_integral
    · intro t
      have hd:=((Real.hasDerivAt_exp t).arctan.const_mul 2).sub_const (π/2)
      convert hd using 1
      rw [Real.cosh_eq,Real.exp_neg]
      field_simp
      ring
    · norm_num
      ring
  have hs: gudermannian x=Real.arctan (Real.sinh x) := by
    apply Trigonometric.gudermannian_integral
    · intro t
      have hd:=(Real.hasDerivAt_sinh t).arctan
      convert hd using 1
      have hc:Real.cosh t≠0 := (Real.cosh_pos t).ne'
      have hp:1+(Real.sinh t)^2≠0 := by positivity
      field_simp
      linear_combination -Real.cosh_sq_sub_sinh_sq t
    · simp
  refine ⟨he,?_,hs⟩
  rw [Real.arcsin_eq_arctan ⟨Real.neg_one_lt_tanh x, Real.tanh_lt_one x⟩,
      Trigonometric.sqrt_one_sub_tanh]
  convert hs using 2
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp

/-- DLMF 4.23.E40: gudermannian reciprocal. -/
@[dlmf 4.23.E40]
theorem gudermannian_reciprocal {x : ℝ} :
    gudermannian x=Real.arcsin ((Real.cosh x/Real.sinh x)⁻¹) ∧
    gudermannian x=Real.arctan (((Real.sinh x)⁻¹)⁻¹) := by
  constructor
  · simpa only [inv_div,Real.tanh_eq_sinh_div_cosh] using (gudermannian_elementary x).2.1
  · simpa only [inv_inv] using (gudermannian_elementary x).2.2

/-- The principal arccosine/secant forms require x nonnegative. -/
@[dlmf 4.23.E40]
theorem gudermannian_nonneg_cosine {x : ℝ} (hx : 0≤x) :
    gudermannian x=Real.arccos ((Real.cosh x)⁻¹) := by
  have hcos:Real.cos (Real.arctan (Real.sinh x))=(Real.cosh x)⁻¹ := by
    rw [Real.cos_arctan,← Real.cosh_sq',Real.sqrt_sq (Real.cosh_pos x).le,one_div]
  rw [← hcos,Real.arccos_cos]
  · exact (gudermannian_elementary x).2.2
  · exact Real.arctan_nonneg.mpr (Real.sinh_nonneg_iff.mpr hx)
  · exact (Real.arctan_lt_pi_div_two _).le.trans (by linarith [Real.pi_pos])

/-- DLMF 4.23.E42: inverse gudermannian elementary. -/
@[dlmf 4.23.E42]
theorem inverse_gudermannian_elementary {x : ℝ} (hx : |x|<π/2) :
    inverseGudermannian x=Real.log (Real.tan (x/2+π/4)) ∧
    inverseGudermannian x=Real.log ((Real.cos x)⁻¹+Real.tan x) ∧
    inverseGudermannian x=Real.arsinh (Real.tan x) ∧
    inverseGudermannian x=Real.artanh (Real.sin x) := by
  have ha:=Trigonometric.inverse_gudermannian_arsinh hx
  have hc:0<Real.cos x := Real.cos_pos_of_mem_Ioo (abs_lt.mp hx)
  have hinv:gudermannian (inverseGudermannian x)=x := by
    rw [(gudermannian_elementary _).2.2,ha,Real.sinh_arsinh]
    exact Real.arctan_tan (abs_lt.mp hx).1 (abs_lt.mp hx).2
  have he:Real.exp (inverseGudermannian x)=Real.tan (x/2+π/4) := by
    rw [← Real.tan_arctan (Real.exp (inverseGudermannian x))]
    congr 1
    linarith [(gudermannian_elementary (inverseGudermannian x)).1]
  refine ⟨?_,?_,ha,?_⟩
  · rw [← he,Real.log_exp]
  · rw [ha,Real.arsinh,Trigonometric.sqrt_one_add_tan hx]
    congr 1
    ring
  · have hs:Real.sin x∈Ioo (-1:ℝ) 1 := by
      have hcircle:=Real.sin_sq_add_cos_sq x
      have hp:=sq_pos_of_pos hc
      constructor <;> nlinarith
    have hsqrt:Real.sqrt (1-(Real.sin x)^2)=Real.cos x := by
      rw [show 1-(Real.sin x)^2=(Real.cos x)^2 by nlinarith [Real.sin_sq_add_cos_sq x],
        Real.sqrt_sq hc.le]
    rw [ha]
    apply Real.sinh_injective
    rw [Real.sinh_arsinh,Real.sinh_artanh hs,hsqrt,Real.tan_eq_sin_div_cos]

/-- DLMF 4.23.E42: inverse gudermannian reciprocal. -/
@[dlmf 4.23.E42]
theorem inverse_gudermannian_reciprocal {x : ℝ} (hx : |x|<π/2) :
    inverseGudermannian x=Real.arsinh (Real.cot x)⁻¹ ∧
    inverseGudermannian x=Real.artanh (((Real.sin x)⁻¹)⁻¹) := by
  refine ⟨?_,?_⟩
  · simpa only [Real.cot_eq_cos_div_sin,inv_div,Real.tan_eq_sin_div_cos] using
      (inverse_gudermannian_elementary hx).2.2.1
  · simpa only [inv_inv] using (inverse_gudermannian_elementary hx).2.2.2

/-- The principal arccosh/arcsech forms require x nonnegative. -/
@[dlmf 4.23.E42]
theorem inverse_gudermannian_nonneg_cosh {x : ℝ} (hx : 0≤x) (hπ : x<π/2) :
    inverseGudermannian x=Real.arcosh ((Real.cos x)⁻¹) := by
  have hbound:|x|<π/2 := by rwa [abs_of_nonneg hx]
  have hc:0<Real.cos x := Real.cos_pos_of_mem_Ioo (abs_lt.mp hbound)
  have ht:0≤Real.tan x := by
    rw [Real.tan_eq_sin_div_cos]
    exact div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hx (by linarith [Real.pi_pos])) hc.le
  have hcosh:Real.cosh (Real.arsinh (Real.tan x))=(Real.cos x)⁻¹ := by
    rw [Real.cosh_arsinh,Trigonometric.sqrt_one_add_tan hbound]
  rw [← hcosh,Real.arcosh_cosh (Real.arsinh_nonneg_iff.mpr ht)]
  exact (inverse_gudermannian_elementary hbound).2.2.1

/-- DLMF 4.23.viii: gudermannian inverse. -/
@[dlmf 4.23.viii]
theorem gudermannian_inverse {x : ℝ} (hx : |x|<π/2) (y : ℝ) :
    gudermannian (inverseGudermannian x)=x ∧ inverseGudermannian (gudermannian y)=y := by
  constructor
  · rw [(gudermannian_elementary _).2.2,(inverse_gudermannian_elementary hx).2.2.1,Real.sinh_arsinh]
    exact Real.arctan_tan (abs_lt.mp hx).1 (abs_lt.mp hx).2
  · have hy:|gudermannian y|<π/2 := by
      rw [(gudermannian_elementary y).2.2]
      exact abs_lt.mpr ⟨Real.neg_pi_div_two_lt_arctan _,Real.arctan_lt_pi_div_two _⟩
    rw [(inverse_gudermannian_elementary hy).2.2.1,(gudermannian_elementary y).2.2,
      Real.tan_arctan,Real.arsinh_sinh]

/-- `gd 0 = 0`. -/
@[simp]
theorem gudermannian_zero : gudermannian 0 = 0 := by
  simp [gudermannian]

/-- The Gudermannian is odd. -/
theorem gudermannian_neg (x : ℝ) : gudermannian (-x) = -gudermannian x := by
  rw [(gudermannian_elementary _).2.2, (gudermannian_elementary x).2.2, Real.sinh_neg,
    Real.arctan_neg]

end DLMF.Elementary
