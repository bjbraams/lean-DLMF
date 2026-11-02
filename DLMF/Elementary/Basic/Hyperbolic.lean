/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Elementary.Basic.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Reciprocal and inverse hyperbolic functions

This file defines the reciprocal hyperbolic functions of DLMF §4.28 and the principal inverse
hyperbolic functions of DLMF §4.37, and proves the relations to the trigonometric functions,
the zeros of `sinh` and `cosh` and the derivatives of DLMF §4.34.

## Main definitions

* `csch`, `sech`, `coth`: the reciprocal hyperbolic functions (DLMF 4.28.5–4.28.7).
* `arcsinh`, `arccosh`, `arctanh`, `arccsch`, `arcsech`, `arccoth`: the principal inverse
  hyperbolic functions (DLMF §4.37).
* `arcsinhDomain`, `arccoshDomain`, `arctanhDomain`, `arccschDomain`, `arcsechDomain`,
  `arccothDomain`: their open principal domains.

## Main results

* `coth_eq_inv_tanh`: DLMF 4.28.7.
* `csc_mul_I`, `sec_mul_I`, `cot_mul_I`: relations to trigonometric functions
  (DLMF 4.28.11–4.28.13).
* `sinh_zeros`, `cosh_zeros`: the zeros of `sinh` and `cosh`.
* `csch_neg`, `sech_neg`, `coth_neg`, `csch_zero`, `sech_zero`, `coth_zero`, `arctanh_zero`:
  parity and values at `0`.
* `hasDerivAt_tanh`, `hasDerivAt_csch`, `hasDerivAt_sech`, `hasDerivAt_coth`: derivatives
  (DLMF 4.34.3–4.34.6).

## Implementation notes

Reciprocals have Lean's totalized values at poles. The principal inverse functions choose one
value on each cut. The multivalued inverses, interrelations, special values, inequalities,
series and differential equations are in `DLMF.Elementary.Hyperbolic.IdentitiesAndSeries`;
the analytic properties of the inverse functions are in the other modules of
`DLMF.Elementary.Hyperbolic`.
-/

@[expose] public noncomputable section

open Complex Filter Set

open scoped Real Topology

namespace DLMF.Elementary

/-- The hyperbolic cosecant, totalized at its poles. -/
@[dlmf 4.28.E5]
def csch (z : ℂ) : ℂ := (Complex.sinh z)⁻¹

/-- The hyperbolic secant, totalized at its poles. -/
@[dlmf 4.28.E6]
def sech (z : ℂ) : ℂ := (Complex.cosh z)⁻¹

/-- The hyperbolic cotangent, totalized at its poles. -/
@[dlmf 4.28.E7]
def coth (z : ℂ) : ℂ := Complex.cosh z/Complex.sinh z

/-- The open principal domain of arcsinh (the imaginary rays beyond ±i are cut); it equals
`arctanCutPlane` (`arcsinhDomain_eq_arctanCutPlane`). -/
def arcsinhDomain : Set ℂ := {z | z.re ≠ 0 ∨ |z.im| < 1}

/-- The open principal domain of arccosh, with the real ray up to 1 removed. -/
def arccoshDomain : Set ℂ := {z | z.im ≠ 0 ∨ 1 < z.re}

/-- The open principal domain of arctanh (the real rays beyond ±1 are cut). -/
def arctanhDomain : Set ℂ := {z | z.im ≠ 0 ∨ |z.re| < 1}

/-- The open principal domain of arccsch, obtained by inversion of the arcsinh domain. -/
def arccschDomain : Set ℂ := {z | z ≠ 0 ∧ z⁻¹ ∈ arcsinhDomain}

/-- The open principal domain of arcsech, obtained by inversion of the arccosh domain. -/
def arcsechDomain : Set ℂ := {z | z ≠ 0 ∧ z⁻¹ ∈ arccoshDomain}

/-- The open principal domain of arccoth, with the segment [-1,1] removed. -/
def arccothDomain : Set ℂ := {z | z.im ≠ 0 ∨ 1 < |z.re|}

/-- Principal inverse sinh; cut-side statements below remove the tie at the square-root cut. -/
@[dlmf 4.37.E16]
def arcsinh (z : ℂ) : ℂ := Complex.log (Complex.sqrt (z^2+1)+z)

/-- Principal inverse cosh, with the square roots factored to preserve the negative half-plane. -/
def arccosh (z : ℂ) : ℂ := Complex.log (z+Complex.sqrt (z-1)*Complex.sqrt (z+1))

/-- Principal inverse tanh off its poles, with the principal logarithm's cut convention. -/
@[dlmf 4.37.E24]
def arctanh (z : ℂ) : ℂ := Complex.log ((1+z)/(1-z))/2

/-- Principal inverse hyperbolic cosecant. -/
@[dlmf 4.37.E7]
def arccsch (z : ℂ) : ℂ := arcsinh z⁻¹

/-- Principal inverse hyperbolic secant. -/
@[dlmf 4.37.E8]
def arcsech (z : ℂ) : ℂ := arccosh z⁻¹

/-- Principal inverse hyperbolic cotangent; the value at zero is a cut-side value. -/
def arccoth (z : ℂ) : ℂ := if z=0 then π*I/2 else arctanh z⁻¹

/-- Identity under the stated parameter and domain assumptions: `coth z=(Complex.tanh z)⁻¹`. -/
@[dlmf 4.28.E7]
theorem coth_eq_inv_tanh (z : ℂ) : coth z=(Complex.tanh z)⁻¹ := by
  simp [coth, Complex.tanh_eq_sinh_div_cosh, inv_div]

/-- Identity under the stated parameter and domain assumptions: `(Complex.sin (I*z))⁻¹= -I*csch
z`. -/
@[dlmf 4.28.E11]
theorem csc_mul_I (z : ℂ) : (Complex.sin (I*z))⁻¹= -I*csch z := by
  simp [mul_comm I z, Complex.sin_mul_I, csch, mul_inv_rev, Complex.inv_I, mul_comm]

/-- Identity under the stated parameter and domain assumptions: `(Complex.cos (I*z))⁻¹=sech z`. -/
@[dlmf 4.28.E12]
theorem sec_mul_I (z : ℂ) : (Complex.cos (I*z))⁻¹=sech z := by
  rw [mul_comm I z, Complex.cos_mul_I]; rfl

/-- Identity under the stated parameter and domain assumptions: `(Complex.tan (I*z))⁻¹= -I*coth
z`. -/
@[dlmf 4.28.E13]
theorem cot_mul_I (z : ℂ) : (Complex.tan (I*z))⁻¹= -I*coth z := by
  simp [mul_comm I z, Complex.tan_mul_I, coth_eq_inv_tanh, mul_inv_rev, Complex.inv_I, mul_comm]

/-- Identity under the stated parameter and domain assumptions: `Complex.sinh z=0 ↔ ∃ k : ℤ,
z=(k:ℂ)*π*I`. -/
theorem sinh_zeros (z : ℂ) : Complex.sinh z=0 ↔ ∃ k : ℤ, z=(k:ℂ)*π*I := by
  constructor
  · intro h
    have hs:Complex.sin (z*I)=0 := by rw [Complex.sin_mul_I,h,zero_mul]
    obtain ⟨k,hk⟩:=Complex.sin_eq_zero_iff.mp hs
    refine ⟨-k,?_⟩
    have hh:=congrArg (fun w:ℂ=>w*(-I)) hk
    simp [mul_assoc] at hh
    convert hh using 1 <;> push_cast <;> ring
  · rintro ⟨k,rfl⟩
    have hs:Complex.sin (((k:ℂ)*π*I)*I)=0 := by
      rw [mul_assoc,Complex.I_mul_I,mul_neg_one]
      exact Complex.sin_eq_zero_iff.mpr ⟨-k,by push_cast;ring⟩
    rw [Complex.sin_mul_I] at hs
    exact (mul_eq_zero.mp hs).resolve_right Complex.I_ne_zero

/-- Identity under the stated parameter and domain assumptions: `Complex.cosh z=0 ↔ ∃ k : ℤ,
z=((k:ℂ)+1/2)*π*I`. -/
theorem cosh_zeros (z : ℂ) : Complex.cosh z=0 ↔ ∃ k : ℤ, z=((k:ℂ)+1/2)*π*I := by
  constructor
  · intro h
    have hs:Complex.cos (z*I)=0 := by rwa [Complex.cos_mul_I]
    obtain ⟨k,hk⟩:=Complex.cos_eq_zero_iff.mp hs
    refine ⟨-k-1,?_⟩
    have hh:=congrArg (fun w:ℂ=>w*(-I)) hk
    simp [mul_assoc] at hh
    convert hh using 1 <;> push_cast <;> ring
  · rintro ⟨k,rfl⟩
    rw [← Complex.cos_mul_I]
    apply Complex.cos_eq_zero_iff.mpr
    refine ⟨-k-1,?_⟩
    simp [mul_assoc]
    push_cast
    ring

/-- At `z`, the function `Complex.tanh` has derivative `(sech z^2)`. -/
@[dlmf 4.34.E3]
theorem hasDerivAt_tanh {z : ℂ} (hz : Complex.cosh z≠0) : HasDerivAt Complex.tanh (sech z^2) z := by
  convert (Complex.hasDerivAt_sinh z).div (Complex.hasDerivAt_cosh z) hz using 1
  · ext w; exact Complex.tanh_eq_sinh_div_cosh w
  · simp only [sech]
    field_simp
    linear_combination -(Complex.cosh_sq_sub_sinh_sq z)

/-- At `z`, the function `csch` has derivative `(-csch z*coth z)`. -/
@[dlmf 4.34.E4]
theorem hasDerivAt_csch {z : ℂ} (hz : Complex.sinh z≠0) : HasDerivAt csch (-csch z*coth z) z := by
  convert (Complex.hasDerivAt_sinh z).inv hz using 1
  · rfl
  · simp only [csch, coth]
    field_simp <;> ring

/-- At `z`, the function `sech` has derivative `(-sech z*Complex.tanh z)`. -/
@[dlmf 4.34.E5]
theorem hasDerivAt_sech {z : ℂ} (hz : Complex.cosh z≠0) :
    HasDerivAt sech (-sech z*Complex.tanh z) z := by
  convert (Complex.hasDerivAt_cosh z).inv hz using 1
  · rfl
  · simp only [sech, Complex.tanh_eq_sinh_div_cosh]
    field_simp <;> ring

/-- At `z`, the function `coth` has derivative `(-csch z^2)`. -/
@[dlmf 4.34.E6]
theorem hasDerivAt_coth {z : ℂ} (hz : Complex.sinh z≠0) : HasDerivAt coth (-csch z^2) z := by
  convert (Complex.hasDerivAt_cosh z).div (Complex.hasDerivAt_sinh z) hz using 1
  · rfl
  · simp only [coth, csch]
    field_simp
    linear_combination (Complex.cosh_sq_sub_sinh_sq z)

/-- The hyperbolic cosecant is odd. -/
theorem csch_neg (z : ℂ) : csch (-z) = -csch z := by
  simp [csch, Complex.sinh_neg, inv_neg]

/-- The hyperbolic secant is even. -/
@[simp]
theorem sech_neg (z : ℂ) : sech (-z) = sech z := by
  simp [sech]

/-- The hyperbolic cotangent is odd. -/
theorem coth_neg (z : ℂ) : coth (-z) = -coth z := by
  simp [coth, Complex.sinh_neg, div_neg]

/-- The totalized value of the hyperbolic cosecant at its pole `0`. -/
@[simp]
theorem csch_zero : csch 0 = 0 := by
  simp [csch]

/-- `sech 0 = 1`. -/
@[simp]
theorem sech_zero : sech 0 = 1 := by
  simp [sech]

/-- The totalized value of the hyperbolic cotangent at its pole `0`. -/
@[simp]
theorem coth_zero : coth 0 = 0 := by
  simp [coth]

/-- `arctanh 0 = 0`. -/
@[simp]
theorem arctanh_zero : arctanh 0 = 0 := by
  simp [arctanh]

end DLMF.Elementary
