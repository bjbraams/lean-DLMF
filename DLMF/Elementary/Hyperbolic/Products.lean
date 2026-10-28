/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Elementary.Hyperbolic.IdentitiesAndSeries

/-!
# Hyperbolic addition formulas and products

Addition and multiplication identities, Cartesian forms, infinite products and partial
fractions.

Source references and common attribution are retained in
`DLMF.Elementary.Hyperbolic`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory

open scoped Real Topology

namespace DLMF.Elementary

/-- Identity under the stated parameter and domain assumptions: `Complex.tanh (u+v)=(Complex.tanh
u+Complex.tanh v)/(1+Complex.tanh u*Complex.tanh v)`. -/
@[dlmf 4.35.E3]
theorem tanh_add {u v : ℂ} (hu : Complex.cosh u≠0) (hv : Complex.cosh v≠0) : Complex.tanh (u+v)=(Complex.tanh u+Complex.tanh v)/(1+Complex.tanh u*Complex.tanh v) := by
  unfold Complex.tanh
  rw [Complex.sinh_add,Complex.cosh_add]
  field_simp <;> ring

/-- Identity under the stated parameter and domain assumptions: `Complex.tanh (u-v)=(Complex.tanh
u-Complex.tanh v)/(1-Complex.tanh u*Complex.tanh v)`. -/
@[dlmf 4.35.E3]
theorem tanh_sub {u v : ℂ} (hu : Complex.cosh u≠0) (hv : Complex.cosh v≠0) : Complex.tanh (u-v)=(Complex.tanh u-Complex.tanh v)/(1-Complex.tanh u*Complex.tanh v) := by
  simpa [sub_eq_add_neg,Complex.tanh_neg] using tanh_add hu (show Complex.cosh (-v)≠0 by simpa using hv)

/-- Identity under the stated parameter and domain assumptions: `coth (u+v)=(coth u*coth
v+1)/(coth u+coth v)`. -/
@[dlmf 4.35.E4]
theorem coth_add {u v : ℂ} (hu : Complex.sinh u≠0) (hv : Complex.sinh v≠0) : coth (u+v)=(coth u*coth v+1)/(coth u+coth v) := by
  unfold coth
  rw [Complex.sinh_add,Complex.cosh_add]
  field_simp <;> ring

/-- Identity under the stated parameter and domain assumptions: `coth (u-v)=(-coth u*coth
v+1)/(coth u-coth v)`. -/
@[dlmf 4.35.E4]
theorem coth_sub {u v : ℂ} (hu : Complex.sinh u≠0) (hv : Complex.sinh v≠0) : coth (u-v)=(-coth u*coth v+1)/(coth u-coth v) := by
  have hn:Complex.sinh (-v)≠0 := by simpa using hv
  have hh:=coth_add hu hn
  simpa [coth,sub_eq_add_neg,Complex.sinh_neg,Complex.cosh_neg,div_neg] using hh

/-- Identity under the stated parameter and domain assumptions: `Complex.sinh u+Complex.sinh
v=2*Complex.sinh ((u+v)/2)*Complex.cosh ((u-v)/2)`. -/
@[dlmf 4.35.E5]
theorem sinh_add_sinh (u v : ℂ) : Complex.sinh u+Complex.sinh v=2*Complex.sinh ((u+v)/2)*Complex.cosh ((u-v)/2) := by
  have h1 := Complex.sinh_add ((u+v)/2) ((u-v)/2)
  have h2 := Complex.sinh_sub ((u+v)/2) ((u-v)/2)
  rw [show (u+v)/2+(u-v)/2=u by ring] at h1
  rw [show (u+v)/2-(u-v)/2=v by ring] at h2
  linear_combination h1+h2

/-- Identity under the stated parameter and domain assumptions: `Complex.sinh u-Complex.sinh
v=2*Complex.cosh ((u+v)/2)*Complex.sinh ((u-v)/2)`. -/
@[dlmf 4.35.E6]
theorem sinh_sub_sinh (u v : ℂ) : Complex.sinh u-Complex.sinh v=2*Complex.cosh ((u+v)/2)*Complex.sinh ((u-v)/2) := by
  have h1 := Complex.sinh_add ((u+v)/2) ((u-v)/2)
  have h2 := Complex.sinh_sub ((u+v)/2) ((u-v)/2)
  rw [show (u+v)/2+(u-v)/2=u by ring] at h1
  rw [show (u+v)/2-(u-v)/2=v by ring] at h2
  linear_combination h1-h2

/-- Identity under the stated parameter and domain assumptions: `Complex.cosh u+Complex.cosh
v=2*Complex.cosh ((u+v)/2)*Complex.cosh ((u-v)/2)`. -/
@[dlmf 4.35.E7]
theorem cosh_add_cosh (u v : ℂ) : Complex.cosh u+Complex.cosh v=2*Complex.cosh ((u+v)/2)*Complex.cosh ((u-v)/2) := by
  have h1 := Complex.cosh_add ((u+v)/2) ((u-v)/2)
  have h2 := Complex.cosh_sub ((u+v)/2) ((u-v)/2)
  rw [show (u+v)/2+(u-v)/2=u by ring] at h1
  rw [show (u+v)/2-(u-v)/2=v by ring] at h2
  linear_combination h1+h2

/-- Identity under the stated parameter and domain assumptions: `Complex.cosh u-Complex.cosh
v=2*Complex.sinh ((u+v)/2)*Complex.sinh ((u-v)/2)`. -/
@[dlmf 4.35.E8]
theorem cosh_sub_cosh (u v : ℂ) : Complex.cosh u-Complex.cosh v=2*Complex.sinh ((u+v)/2)*Complex.sinh ((u-v)/2) := by
  have h1 := Complex.cosh_add ((u+v)/2) ((u-v)/2)
  have h2 := Complex.cosh_sub ((u+v)/2) ((u-v)/2)
  rw [show (u+v)/2+(u-v)/2=u by ring] at h1
  rw [show (u+v)/2-(u-v)/2=v by ring] at h2
  linear_combination h1-h2

/-- Identity under the stated parameter and domain assumptions: `Complex.tanh u+Complex.tanh
v=Complex.sinh (u+v)/(Complex.cosh u*Complex.cosh v)`. -/
@[dlmf 4.35.E9]
theorem tanh_add_tanh {u v : ℂ} (hu : Complex.cosh u≠0) (hv : Complex.cosh v≠0) : Complex.tanh u+Complex.tanh v=Complex.sinh (u+v)/(Complex.cosh u*Complex.cosh v) := by
  simp only [Complex.tanh_eq_sinh_div_cosh, Complex.sinh_add]
  field_simp <;> ring

/-- Identity under the stated parameter and domain assumptions: `Complex.tanh u-Complex.tanh
v=Complex.sinh (u-v)/(Complex.cosh u*Complex.cosh v)`. -/
@[dlmf 4.35.E9]
theorem tanh_sub_tanh {u v : ℂ} (hu : Complex.cosh u≠0) (hv : Complex.cosh v≠0) : Complex.tanh u-Complex.tanh v=Complex.sinh (u-v)/(Complex.cosh u*Complex.cosh v) := by
  simp only [Complex.tanh_eq_sinh_div_cosh, Complex.sinh_sub]
  field_simp <;> ring

/-- Identity under the stated parameter and domain assumptions: `coth u+coth v=Complex.sinh
(v+u)/(Complex.sinh u*Complex.sinh v)`. -/
@[dlmf 4.35.E10]
theorem coth_add_coth {u v : ℂ} (hu : Complex.sinh u≠0) (hv : Complex.sinh v≠0) : coth u+coth v=Complex.sinh (v+u)/(Complex.sinh u*Complex.sinh v) := by
  simp only [coth, Complex.sinh_add]
  field_simp <;> ring

/-- Identity under the stated parameter and domain assumptions: `coth u-coth v=Complex.sinh
(v-u)/(Complex.sinh u*Complex.sinh v)`. -/
@[dlmf 4.35.E10]
theorem coth_sub_coth {u v : ℂ} (hu : Complex.sinh u≠0) (hv : Complex.sinh v≠0) : coth u-coth v=Complex.sinh (v-u)/(Complex.sinh u*Complex.sinh v) := by
  simp only [coth, Complex.sinh_sub]
  field_simp <;> ring

/-- Identity under the stated parameter and domain assumptions: `sech z^2=1-Complex.tanh z^2`. -/
@[dlmf 4.35.E12]
theorem sech_sq {z : ℂ} (hz : Complex.cosh z≠0) : sech z^2=1-Complex.tanh z^2 := by
  simp only [sech, Complex.tanh_eq_sinh_div_cosh]
  field_simp
  linear_combination -(Complex.cosh_sq_sub_sinh_sq z)

/-- Identity under the stated parameter and domain assumptions: `csch z^2=coth z^2-1`. -/
@[dlmf 4.35.E13]
theorem csch_sq {z : ℂ} (hz : Complex.sinh z≠0) : csch z^2=coth z^2-1 := by
  simp only [csch, coth]
  field_simp
  linear_combination -(Complex.cosh_sq_sub_sinh_sq z)

/-- Identity under the stated parameter and domain assumptions: `2*Complex.sinh u*Complex.sinh
v=Complex.cosh (u+v)-Complex.cosh (u-v)`. -/
@[dlmf 4.35.E14]
theorem two_sinh_mul_sinh (u v : ℂ) : 2*Complex.sinh u*Complex.sinh v=Complex.cosh (u+v)-Complex.cosh (u-v) := by
  rw [Complex.cosh_add, Complex.cosh_sub]
  ring

/-- Identity under the stated parameter and domain assumptions: `2*Complex.cosh u*Complex.cosh
v=Complex.cosh (u+v)+Complex.cosh (u-v)`. -/
@[dlmf 4.35.E15]
theorem two_cosh_mul_cosh (u v : ℂ) : 2*Complex.cosh u*Complex.cosh v=Complex.cosh (u+v)+Complex.cosh (u-v) := by
  rw [Complex.cosh_add, Complex.cosh_sub]
  ring

/-- Identity under the stated parameter and domain assumptions: `2*Complex.sinh u*Complex.cosh
v=Complex.sinh (u+v)+Complex.sinh (u-v)`. -/
@[dlmf 4.35.E16]
theorem two_sinh_mul_cosh (u v : ℂ) : 2*Complex.sinh u*Complex.cosh v=Complex.sinh (u+v)+Complex.sinh (u-v) := by
  rw [Complex.sinh_add, Complex.sinh_sub]
  ring

/-- Identity under the stated parameter and domain assumptions: `Complex.sinh u^2-Complex.sinh
v^2=Complex.sinh (u+v)*Complex.sinh (u-v)`. -/
@[dlmf 4.35.E17]
theorem sinh_sq_sub_sinh_sq (u v : ℂ) : Complex.sinh u^2-Complex.sinh v^2=Complex.sinh (u+v)*Complex.sinh (u-v) := by
  rw [Complex.sinh_add, Complex.sinh_sub]
  linear_combination -(Complex.sinh u)^2*(Complex.cosh_sq_sub_sinh_sq v) +
    (Complex.sinh v)^2*(Complex.cosh_sq_sub_sinh_sq u)

/-- Identity under the stated parameter and domain assumptions: `Complex.cosh u^2-Complex.cosh
v^2=Complex.sinh (u+v)*Complex.sinh (u-v)`. -/
@[dlmf 4.35.E18]
theorem cosh_sq_sub_cosh_sq (u v : ℂ) : Complex.cosh u^2-Complex.cosh v^2=Complex.sinh (u+v)*Complex.sinh (u-v) := by
  linear_combination (Complex.cosh_sq_sub_sinh_sq u) -
    (Complex.cosh_sq_sub_sinh_sq v) + (sinh_sq_sub_sinh_sq u v)

/-- Identity under the stated parameter and domain assumptions: `Complex.sinh u^2+Complex.cosh
v^2=Complex.cosh (u+v)*Complex.cosh (u-v)`. -/
@[dlmf 4.35.E19]
theorem sinh_sq_add_cosh_sq (u v : ℂ) : Complex.sinh u^2+Complex.cosh v^2=Complex.cosh (u+v)*Complex.cosh (u-v) := by
  rw [Complex.cosh_add, Complex.cosh_sub]
  linear_combination -(Complex.cosh v)^2*(Complex.cosh_sq_sub_sinh_sq u) -
    (Complex.sinh u)^2*(Complex.cosh_sq_sub_sinh_sq v)

/-- Identity under the stated parameter and domain assumptions: `Complex.sinh
(z/2)^2=(Complex.cosh z-1)/2`. -/
@[dlmf 4.35.E20]
theorem sinh_half_sq (z : ℂ) : Complex.sinh (z/2)^2=(Complex.cosh z-1)/2 := by
  have h := Complex.cosh_two_mul (z/2)
  rw [show 2*(z/2)=z by ring] at h
  linear_combination -h/2-(Complex.cosh_sq_sub_sinh_sq (z/2))/2

/-- Identity under the stated parameter and domain assumptions: `Complex.cosh
(z/2)^2=(Complex.cosh z+1)/2`. -/
@[dlmf 4.35.E21]
theorem cosh_half_sq (z : ℂ) : Complex.cosh (z/2)^2=(Complex.cosh z+1)/2 := by
  have h := Complex.cosh_two_mul (z/2)
  rw [show 2*(z/2)=z by ring] at h
  linear_combination -h/2+(Complex.cosh_sq_sub_sinh_sq (z/2))/2

/-- Identity under the stated parameter and domain assumptions: `Complex.tanh
(z/2)^2=(Complex.cosh z-1)/(Complex.cosh z+1)`. -/
@[dlmf 4.35.E22]
theorem tanh_half_sq {z : ℂ} (hz : Complex.cosh (z/2)≠0) : Complex.tanh (z/2)^2=(Complex.cosh z-1)/(Complex.cosh z+1) := by
  have hs:Complex.cosh z-1=2*Complex.sinh (z/2)^2 := by linear_combination -2*sinh_half_sq z
  have hc:Complex.cosh z+1=2*Complex.cosh (z/2)^2 := by linear_combination -2*cosh_half_sq z
  rw [hs,hc,Complex.tanh,div_pow]
  field_simp

/-- Identity under the stated parameter and domain assumptions: `Complex.tanh (z/2)=(Complex.cosh
z-1)/Complex.sinh z ∧ Complex.tanh (z/2)=Complex.sinh z/(Complex.cosh z+1)`. -/
@[dlmf 4.35.E22]
theorem tanh_half_ratios {z : ℂ} (hz : Complex.sinh z≠0) : Complex.tanh (z/2)=(Complex.cosh z-1)/Complex.sinh z ∧ Complex.tanh (z/2)=Complex.sinh z/(Complex.cosh z+1) := by
  have h2 : Complex.sinh z = 2*Complex.sinh (z/2)*Complex.cosh (z/2) := by
    rw [← Complex.sinh_two_mul]; ring_nf
  have hc : Complex.cosh z - 1 = 2*Complex.sinh (z/2)^2 := by linear_combination -2*sinh_half_sq z
  have hc' : Complex.cosh z + 1 = 2*Complex.cosh (z/2)^2 := by linear_combination -2*cosh_half_sq z
  have hch : Complex.cosh (z/2) ≠ 0 := by intro h; apply hz; rw [h2,h]; ring
  have hsh : Complex.sinh (z/2) ≠ 0 := by intro h; apply hz; rw [h2,h]; ring
  rw [Complex.tanh_eq_sinh_div_cosh, hc, hc', h2]
  constructor <;> field_simp <;> ring

/-- Identity under the stated parameter and domain assumptions: `Complex.sinh (2*z)=2*Complex.tanh
z/(1-Complex.tanh z^2)`. -/
@[dlmf 4.35.E26]
theorem sinh_two_mul_tanh {z : ℂ} (hz : Complex.cosh z≠0) : Complex.sinh (2*z)=2*Complex.tanh z/(1-Complex.tanh z^2) := by
  rw [Complex.tanh,Complex.sinh_two_mul]
  field_simp
  rw [Complex.cosh_sq]
  ring

/-- Identity under the stated parameter and domain assumptions: `Complex.cosh (2*z)=2*Complex.cosh
z^2-1 ∧ Complex.cosh (2*z)=2*Complex.sinh z^2+1`. -/
@[dlmf 4.35.E27]
theorem cosh_two_mul_forms (z : ℂ) : Complex.cosh (2*z)=2*Complex.cosh z^2-1 ∧ Complex.cosh (2*z)=2*Complex.sinh z^2+1 := by
  rw [Complex.cosh_two_mul]
  constructor
  · linear_combination -(Complex.cosh_sq_sub_sinh_sq z)
  · linear_combination (Complex.cosh_sq_sub_sinh_sq z)

/-- Identity under the stated parameter and domain assumptions: `Complex.tanh (2*z)=2*Complex.tanh
z/(1+Complex.tanh z^2)`. -/
@[dlmf 4.35.E28]
theorem tanh_two_mul {z : ℂ} (hz : Complex.cosh z≠0) : Complex.tanh (2*z)=2*Complex.tanh z/(1+Complex.tanh z^2) := by
  have hh:=tanh_add hz hz
  simpa only [← two_mul,pow_two] using hh

/-- Identity under the stated parameter and domain assumptions: `Complex.sinh (4*z)=4*Complex.sinh
z^3*Complex.cosh z+4*Complex.cosh z^3*Complex.sinh z`. -/
@[dlmf 4.35.E31]
theorem sinh_four_mul (z : ℂ) : Complex.sinh (4*z)=4*Complex.sinh z^3*Complex.cosh z+4*Complex.cosh z^3*Complex.sinh z := by
  rw [show 4*z=2*(2*z) by ring, Complex.sinh_two_mul,
    Complex.sinh_two_mul, Complex.cosh_two_mul]
  ring

/-- Identity under the stated parameter and domain assumptions: `Complex.cosh (4*z)=Complex.cosh
z^4+6*Complex.sinh z^2*Complex.cosh z^2+Complex.sinh z^4`. -/
@[dlmf 4.35.E32]
theorem cosh_four_mul (z : ℂ) : Complex.cosh (4*z)=Complex.cosh z^4+6*Complex.sinh z^2*Complex.cosh z^2+Complex.sinh z^4 := by
  rw [show 4*z=2*(2*z) by ring, Complex.cosh_two_mul,
    Complex.cosh_two_mul, Complex.sinh_two_mul]
  ring

/-- Identity under the stated parameter and domain assumptions: `Complex.cosh
((n:ℂ)*z)+Complex.sinh ((n:ℂ)*z)=(Complex.cosh z+Complex.sinh z)^n ∧ Complex.cosh
((n:ℂ)*z)-Complex.sinh ((n:ℂ)*z)=(Complex.cosh z-Complex.sinh z)^n`. -/
@[dlmf 4.35.E33]
theorem cosh_add_sinh_int_mul (n : ℤ) (z : ℂ) : Complex.cosh ((n:ℂ)*z)+Complex.sinh ((n:ℂ)*z)=(Complex.cosh z+Complex.sinh z)^n ∧ Complex.cosh ((n:ℂ)*z)-Complex.sinh ((n:ℂ)*z)=(Complex.cosh z-Complex.sinh z)^n := by
  constructor
  · rw [Complex.cosh_add_sinh, Complex.cosh_add_sinh, Complex.exp_int_mul]
  · rw [Complex.cosh_sub_sinh, Complex.cosh_sub_sinh, show -((n:ℂ)*z)=(n:ℂ)*(-z) by ring, Complex.exp_int_mul]

/-- Identity under the stated parameter and domain assumptions: `Complex.sinh z=Real.sinh
z.re*Real.cos z.im+I*(Real.cosh z.re*Real.sin z.im)`. -/
@[dlmf 4.35.E34]
theorem sinh_cartesian (z : ℂ) : Complex.sinh z=Real.sinh z.re*Real.cos z.im+I*(Real.cosh z.re*Real.sin z.im) := by
  conv_lhs => rw [← Complex.re_add_im z,Complex.sinh_add,Complex.sinh_mul_I,Complex.cosh_mul_I]
  simp only [← Complex.ofReal_sinh,← Complex.ofReal_cosh,← Complex.ofReal_sin,← Complex.ofReal_cos]
  push_cast
  ring

/-- Identity under the stated parameter and domain assumptions: `Complex.cosh z=Real.cosh
z.re*Real.cos z.im+I*(Real.sinh z.re*Real.sin z.im)`. -/
@[dlmf 4.35.E35]
theorem cosh_cartesian (z : ℂ) : Complex.cosh z=Real.cosh z.re*Real.cos z.im+I*(Real.sinh z.re*Real.sin z.im) := by
  conv_lhs => rw [← Complex.re_add_im z,Complex.cosh_add,Complex.sinh_mul_I,Complex.cosh_mul_I]
  simp only [← Complex.ofReal_sinh,← Complex.ofReal_cosh,← Complex.ofReal_sin,← Complex.ofReal_cos]
  push_cast
  ring

/-- Identity under the stated parameter and domain assumptions: `Complex.tanh z=((Real.sinh
(2*z.re):ℂ)+I*Real.sin (2*z.im))/(Real.cosh (2*z.re)+Real.cos (2*z.im))`. -/
@[dlmf 4.35.E36]
theorem tanh_cartesian (z : ℂ) : Complex.tanh z=((Real.sinh (2*z.re):ℂ)+I*Real.sin (2*z.im))/(Real.cosh (2*z.re)+Real.cos (2*z.im)) := by
  have hDr : Real.cosh (2*z.re)+Real.cos (2*z.im) = 2*((Real.sinh z.re)^2+(Real.cos z.im)^2) := by
    rw [Real.cosh_two_mul, Real.cos_two_mul]
    nlinarith [Real.cosh_sq z.re]
  have hq : 0 ≤ (Real.sinh z.re)^2+(Real.cos z.im)^2 := by positivity
  rw [Complex.tanh_eq_sinh_div_cosh]
  by_cases h0 : (Real.sinh z.re)^2+(Real.cos z.im)^2 = 0
  · have hc : Complex.cosh z = 0 := by
      have hs : Real.sinh z.re = 0 := by nlinarith [sq_nonneg (Real.sinh z.re), sq_nonneg (Real.cos z.im)]
      have hc0 : Real.cos z.im = 0 := by nlinarith [sq_nonneg (Real.sinh z.re), sq_nonneg (Real.cos z.im)]
      rw [cosh_cartesian, hs, hc0]; simp
    have : ((Real.cosh (2*z.re):ℂ)+Real.cos (2*z.im)) = 0 := by
      rw [← Complex.ofReal_add, hDr, h0]; simp
    rw [this, hc]; simp
  · have hD0 : ((Real.cosh (2*z.re):ℂ)+Real.cos (2*z.im)) ≠ 0 := by
      rw [← Complex.ofReal_add, hDr]
      exact_mod_cast mul_ne_zero two_ne_zero h0
    have hC0 : Complex.cosh z ≠ 0 := by
      intro h
      rw [cosh_cartesian] at h
      have h1 := congrArg Complex.re h
      have h2 := congrArg Complex.im h
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, Complex.add_im, Complex.mul_im, Complex.zero_re, Complex.zero_im] at h1 h2
      ring_nf at h1 h2
      have hcy : Real.cos z.im = 0 := by
        rcases mul_eq_zero.mp h1 with h|h
        · exact absurd h (Real.cosh_pos _).ne'
        · exact h
      have hsy : Real.sin z.im ≠ 0 := by
        intro h; have := Real.sin_sq_add_cos_sq z.im; rw [h, hcy] at this; norm_num at this
      have hsx : Real.sinh z.re = 0 := (mul_eq_zero.mp h2).resolve_right hsy
      apply h0; rw [hsx, hcy]; ring
    rw [div_eq_div_iff hC0 hD0, sinh_cartesian, cosh_cartesian]
    rw [Real.cosh_two_mul, Real.cos_two_mul, Real.sinh_two_mul, Real.sin_two_mul]
    have e1 := Real.cosh_sq z.re
    have e2 := Real.sin_sq_add_cos_sq z.im
    simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_sub,
      Complex.ofReal_ofNat, Complex.ofReal_one]
    have e1' : ((Real.cosh z.re:ℂ))^2 = (Real.sinh z.re:ℂ)^2+1 := by exact_mod_cast e1
    have e2' : ((Real.sin z.im:ℂ))^2 + (Real.cos z.im:ℂ)^2 = 1 := by exact_mod_cast e2
    generalize (Real.sinh z.re:ℂ) = a at *
    generalize (Real.cosh z.re:ℂ) = b at *
    generalize (Real.cos z.im:ℂ) = c at *
    generalize (Real.sin z.im:ℂ) = s at *
    linear_combination (I*b*s - a*c)*e1' + (-2*I^2*a*c)*e2' + (2*a*c^3 - 2*a*c)*Complex.I_sq

/-- Identity under the stated parameter and domain assumptions: `coth z=((Real.sinh
(2*z.re):ℂ)-I*Real.sin (2*z.im))/(Real.cosh (2*z.re)-Real.cos (2*z.im))`. -/
@[dlmf 4.35.E37]
theorem coth_cartesian (z : ℂ) : coth z=((Real.sinh (2*z.re):ℂ)-I*Real.sin (2*z.im))/(Real.cosh (2*z.re)-Real.cos (2*z.im)) := by
  have hDr : Real.cosh (2*z.re)-Real.cos (2*z.im) = 2*((Real.sinh z.re)^2+(Real.sin z.im)^2) := by
    rw [Real.cosh_two_mul, Real.cos_two_mul]
    nlinarith [Real.cosh_sq z.re, Real.sin_sq_add_cos_sq z.im]
  have hq : 0 ≤ (Real.sinh z.re)^2+(Real.sin z.im)^2 := by positivity
  rw [coth]
  by_cases h0 : (Real.sinh z.re)^2+(Real.sin z.im)^2 = 0
  · have hc : Complex.sinh z = 0 := by
      have hs : Real.sinh z.re = 0 := by nlinarith [sq_nonneg (Real.sinh z.re), sq_nonneg (Real.sin z.im)]
      have hc0 : Real.sin z.im = 0 := by nlinarith [sq_nonneg (Real.sinh z.re), sq_nonneg (Real.sin z.im)]
      rw [sinh_cartesian, hs, hc0]; simp
    have : ((Real.cosh (2*z.re):ℂ)-Real.cos (2*z.im)) = 0 := by
      rw [← Complex.ofReal_sub, hDr, h0]; simp
    rw [this, hc]; simp
  · have hD0 : ((Real.cosh (2*z.re):ℂ)-Real.cos (2*z.im)) ≠ 0 := by
      rw [← Complex.ofReal_sub, hDr]
      exact_mod_cast mul_ne_zero two_ne_zero h0
    have hC0 : Complex.sinh z ≠ 0 := by
      intro h
      rw [sinh_cartesian] at h
      have h1 := congrArg Complex.re h
      have h2 := congrArg Complex.im h
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, Complex.add_im, Complex.mul_im, Complex.zero_re, Complex.zero_im] at h1 h2
      ring_nf at h1 h2
      have hsy : Real.sin z.im = 0 := by
        rcases mul_eq_zero.mp h2 with h|h
        · exact absurd h (Real.cosh_pos _).ne'
        · exact h
      have hcy : Real.cos z.im ≠ 0 := by
        intro h; have := Real.sin_sq_add_cos_sq z.im; rw [h, hsy] at this; norm_num at this
      have hsx : Real.sinh z.re = 0 := (mul_eq_zero.mp h1).resolve_right hcy
      apply h0; rw [hsx, hsy]; ring
    rw [div_eq_div_iff hC0 hD0, sinh_cartesian, cosh_cartesian]
    rw [Real.cosh_two_mul, Real.cos_two_mul, Real.sinh_two_mul, Real.sin_two_mul]
    have e1 := Real.cosh_sq z.re
    have e2 := Real.sin_sq_add_cos_sq z.im
    simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_sub,
      Complex.ofReal_ofNat, Complex.ofReal_one]
    have e1' : ((Real.cosh z.re:ℂ))^2 = (Real.sinh z.re:ℂ)^2+1 := by exact_mod_cast e1
    have e2' : ((Real.sin z.im:ℂ))^2 + (Real.cos z.im:ℂ)^2 = 1 := by exact_mod_cast e2
    generalize (Real.sinh z.re:ℂ) = a at *
    generalize (Real.cosh z.re:ℂ) = b at *
    generalize (Real.cos z.im:ℂ) = c at *
    generalize (Real.sin z.im:ℂ) = s at *
    linear_combination (-I*a*s + b*c)*e1' + (2*I^2*b*c)*e2' + (-2*b*c^3 + 2*b*c)*Complex.I_sq

/-- Identity under the stated parameter and domain assumptions: `‖Complex.sinh z‖=Real.sqrt
(Real.sinh z.re^2+Real.sin z.im^2) ∧ ‖Complex.sinh z‖=Real.sqrt ((Real.cosh (2*z.re)-Real.cos
(2*z.im))/2)`. -/
@[dlmf 4.35.E38]
theorem norm_sinh_cartesian (z : ℂ) : ‖Complex.sinh z‖=Real.sqrt (Real.sinh z.re^2+Real.sin z.im^2) ∧ ‖Complex.sinh z‖=Real.sqrt ((Real.cosh (2*z.re)-Real.cos (2*z.im))/2) := by
  have hn:‖Complex.sin (I*z)‖=‖Complex.sinh z‖ := by
    rw [mul_comm I z,Complex.sin_mul_I,norm_mul,Complex.norm_I,mul_one]
  simpa [hn,Complex.I_mul_re,Complex.I_mul_im,Real.sin_neg,Real.cos_neg,add_comm] using norm_sin_explicit (I*z)

/-- Identity under the stated parameter and domain assumptions: `‖Complex.cosh z‖=Real.sqrt
(Real.sinh z.re^2+Real.cos z.im^2) ∧ ‖Complex.cosh z‖=Real.sqrt ((Real.cosh (2*z.re)+Real.cos
(2*z.im))/2)`. -/
@[dlmf 4.35.E39]
theorem norm_cosh_cartesian (z : ℂ) : ‖Complex.cosh z‖=Real.sqrt (Real.sinh z.re^2+Real.cos z.im^2) ∧ ‖Complex.cosh z‖=Real.sqrt ((Real.cosh (2*z.re)+Real.cos (2*z.im))/2) := by
  have hn:Complex.cos (I*z)=Complex.cosh z := by rw [mul_comm I z,Complex.cos_mul_I]
  simpa [hn,Complex.I_mul_re,Complex.I_mul_im,Real.cos_neg,add_comm] using norm_cos_explicit (I*z)

/-- Identity under the stated parameter and domain assumptions: `‖Complex.tanh z‖=Real.sqrt
((Real.cosh (2*z.re)-Real.cos (2*z.im))/(Real.cosh (2*z.re)+Real.cos (2*z.im)))`. -/
@[dlmf 4.35.E40]
theorem norm_tanh_cartesian (z : ℂ) : ‖Complex.tanh z‖=Real.sqrt ((Real.cosh (2*z.re)-Real.cos (2*z.im))/(Real.cosh (2*z.re)+Real.cos (2*z.im))) := by
  have hp:0≤(Real.cosh (2*z.re)-Real.cos (2*z.im))/2 := by
    rw [Real.cosh_two_mul,Real.cos_two_mul]
    nlinarith [Real.cosh_sq_sub_sinh_sq z.re,Real.sin_sq_add_cos_sq z.im,
      sq_nonneg (Real.sin z.im),sq_nonneg (Real.sinh z.re)]
  rw [Complex.tanh_eq_sinh_div_cosh,norm_div,(norm_sinh_cartesian z).2,(norm_cosh_cartesian z).2,← Real.sqrt_div hp]
  congr 1
  exact div_div_div_cancel_right₀ (two_ne_zero : (2:ℝ)≠0) _ _

/-- Two analytic functions on a preconnected open set with equal squares agree everywhere once
they agree at one point where they do not vanish. -/
lemma hypR4_sq_eq_continuation {U : Set ℂ} (hU : IsOpen U) (hc : IsPreconnected U)
    {r s : ℂ → ℂ} (hr : AnalyticOnNhd ℂ r U) (hs : AnalyticOnNhd ℂ s U)
    (hsq : ∀ z ∈ U, r z^2 = s z^2) {x : ℂ} (hx : x ∈ U) (hrx : r x = s x) (hsx : s x ≠ 0) :
    ∀ z ∈ U, r z = s z := by
  have hev : r =ᶠ[𝓝 x] s := by
    have hcont : ContinuousAt (fun z => r z + s z) x := ((hr x hx).add (hs x hx)).continuousAt
    have hne : ∀ᶠ z in 𝓝 x, r z + s z ≠ 0 :=
      hcont.eventually_ne (by rw [hrx, ← two_mul]; exact mul_ne_zero two_ne_zero hsx)
    filter_upwards [hne, hU.mem_nhds hx] with z hz hzU
    have h : (r z - s z)*(r z + s z) = 0 := by linear_combination hsq z hzU
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hz)
  exact fun z hz => hr.eqOn_of_preconnected_of_eventuallyEq hs hc hx hev hz

/-- The half-angle square root selected on the positive real axis and continued analytically. -/
@[dlmf 4.35.E20]
theorem sinh_half_continued_root {U : Set ℂ} (hU : IsOpen U) (hc : IsConnected U) {r : ℂ → ℂ}
    (hr : AnalyticOnNhd ℂ r U) (hsq : ∀ z ∈ U, r z^2=(Complex.cosh z-1)/2)
    {x : ℝ} (hx : 0<x) (hxU : (x:ℂ) ∈ U) (hanchor : r x=Complex.sinh ((x:ℂ)/2))
     :
    ∀ z ∈ U, r z=Complex.sinh (z/2) := by
  have hs : AnalyticOnNhd ℂ (fun z => Complex.sinh (z/2)) U := fun z _ =>
    (Complex.differentiable_sinh.comp (differentiable_id.div_const 2)).analyticAt z
  refine hypR4_sq_eq_continuation hU hc.isPreconnected hr hs
    (fun z hz => by rw [hsq z hz, sinh_half_sq]) hxU hanchor ?_
  rw [show (x:ℂ)/2 = ((x/2:ℝ):ℂ) by push_cast; ring, ← Complex.ofReal_sinh]
  exact_mod_cast (Real.sinh_pos_iff.mpr (by linarith)).ne'

/-- The half-angle square root selected on the positive real axis and continued analytically. -/
@[dlmf 4.35.E21]
theorem cosh_half_continued_root {U : Set ℂ} (hU : IsOpen U) (hc : IsConnected U) {r : ℂ → ℂ}
    (hr : AnalyticOnNhd ℂ r U) (hsq : ∀ z ∈ U, r z^2=(Complex.cosh z+1)/2)
    {x : ℝ} (hx : 0<x) (hxU : (x:ℂ) ∈ U) (hanchor : r x=Complex.cosh ((x:ℂ)/2))
     :
    ∀ z ∈ U, r z=Complex.cosh (z/2) := by
  have hs : AnalyticOnNhd ℂ (fun z => Complex.cosh (z/2)) U := fun z _ =>
    (Complex.differentiable_cosh.comp (differentiable_id.div_const 2)).analyticAt z
  refine hypR4_sq_eq_continuation hU hc.isPreconnected hr hs
    (fun z hz => by rw [hsq z hz, cosh_half_sq]) hxU hanchor ?_
  rw [show (x:ℂ)/2 = ((x/2:ℝ):ℂ) by push_cast; ring, ← Complex.ofReal_cosh]
  exact_mod_cast (Real.cosh_pos _).ne'

/-- The half-angle square root selected on the positive real axis and continued analytically. -/
@[dlmf 4.35.E22]
theorem tanh_half_continued_root {U : Set ℂ} (hU : IsOpen U) (hc : IsConnected U) {r : ℂ → ℂ}
    (hr : AnalyticOnNhd ℂ r U) (hsq : ∀ z ∈ U, r z^2=(Complex.cosh z-1)/(Complex.cosh z+1))
    {x : ℝ} (hx : 0<x) (hxU : (x:ℂ) ∈ U) (hanchor : r x=Complex.tanh ((x:ℂ)/2))
    (hpole : ∀ z ∈ U, Complex.cosh (z/2)≠0) :
    ∀ z ∈ U, r z=Complex.tanh (z/2) := by
  have hs : AnalyticOnNhd ℂ (fun z => Complex.tanh (z/2)) U := by
    intro z hz
    have h1 := (Complex.differentiable_sinh.comp (differentiable_id.div_const 2)).analyticAt z
    have h2 := (Complex.differentiable_cosh.comp (differentiable_id.div_const 2)).analyticAt z
    have hf : (fun z => Complex.tanh (z/2)) =
        (fun z => Complex.sinh (z/2)) / (fun z => Complex.cosh (z/2)) := by
      funext w; simp [Complex.tanh_eq_sinh_div_cosh]
    rw [hf]
    exact h1.div h2 (hpole z hz)
  refine hypR4_sq_eq_continuation hU hc.isPreconnected hr hs
    (fun z hz => by rw [hsq z hz, tanh_half_sq (hpole z hz)]) hxU hanchor ?_
  rw [show (x:ℂ)/2 = ((x/2:ℝ):ℂ) by push_cast; ring, ← Complex.ofReal_tanh]
  have : 0 < Real.tanh (x/2) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr (by linarith)) (Real.cosh_pos _)
  exact_mod_cast this.ne'

/-- Identity under the stated parameter and domain assumptions: `HasProd (fun n : ℕ =>
1+z^2/(((n+1:ℂ)^2)*π^2)) (sinhc z)`. -/
@[dlmf 4.36.E1]
theorem hasProd_sinh (z : ℂ) : HasProd (fun n : ℕ => 1+z^2/(((n+1:ℂ)^2)*π^2)) (sinhc z) := by
  have hπ : (π:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  by_cases hz0 : z = 0
  · subst hz0; simp [sinhc]
  have hx0 : I*z/π ≠ 0 := by simp [hz0, hπ, Complex.I_ne_zero]
  have hf : (fun n : ℕ => 1+z^2/(((n+1:ℂ)^2)*π^2)) = fun n => 1 + sineTerm (I*z/π) n := by
    funext n; simp only [sineTerm]; congr 1
    have : ((n:ℂ)+1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    field_simp
    linear_combination Complex.I_sq
  rw [hf, (multipliable_sineTerm _).hasProd_iff_tendsto_nat]
  convert tendsto_euler_sin_prod' hx0 using 2
  rw [show (π:ℂ)*(I*z/π) = z*I by field_simp, Complex.sin_mul_I]
  simp only [sinhc, hz0, ↓reduceIte]
  field_simp

/-- Identity under the stated parameter and domain assumptions: `HasProd (fun n : ℕ =>
1+4*z^2/(((2*n+1:ℂ)^2)*π^2)) (Complex.cosh z)`. -/
@[dlmf 4.36.E2]
theorem hasProd_cosh (z : ℂ) : HasProd (fun n : ℕ => 1+4*z^2/(((2*n+1:ℂ)^2)*π^2)) (Complex.cosh z) := by
  have hπ : (π:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  set R : ℝ := ‖z‖+1 with hR
  have hR0 : 0 ≤ R := by positivity
  set K : Set ℂ := Metric.closedBall (0:ℂ) R with hK
  have hzK : z ∈ Metric.ball (0:ℂ) R := by simp [hR]
  have hu : Summable (fun n : ℕ => 4*R^2/(((2*n+1:ℝ))^2*π^2)) := by
    have hs : Summable (fun n : ℕ => 1/((n:ℝ)+1)^2) := by
      have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
      simpa using this
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      (hs.mul_left (4*R^2/π^2))
    have h1 : ((n:ℝ)+1)^2 ≤ (2*n+1)^2 := by nlinarith [(n.cast_nonneg : (0:ℝ) ≤ n)]
    have hp : 0 < π^2 := by positivity
    rw [div_mul_div_comm, mul_one, mul_comm (π^2)]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_right h1 hp.le
  have hb : ∀ᶠ n : ℕ in atTop, ∀ x ∈ K,
      ‖4*x^2/(((2*n+1:ℂ)^2)*π^2)‖ ≤ 4*R^2/(((2*n+1:ℝ))^2*π^2) := by
    refine Filter.Eventually.of_forall fun (n : ℕ) (x : ℂ) hx => ?_
    have hx' : ‖x‖ ≤ R := by simpa [hK] using hx
    have e : ‖4*x^2/(((2*n+1:ℂ)^2)*π^2)‖ = 4*‖x‖^2/(((2*n+1:ℝ))^2*π^2) := by
      rw [norm_div, norm_mul, norm_mul, norm_pow, norm_pow, norm_pow]
      have h1 : ‖(2*n+1:ℂ)‖ = 2*n+1 := by
        rw [show (2*n+1:ℂ) = ((2*n+1:ℝ):ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_of_nonneg (by positivity)]
      rw [h1, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
      norm_num
    rw [e]
    gcongr
  have hcts : ∀ n : ℕ, ContinuousOn (fun x : ℂ => 4*x^2/(((2*n+1:ℂ)^2)*π^2)) K :=
    fun n => (by fun_prop : Continuous (fun x : ℂ => 4*x^2/(((2*n+1:ℂ)^2)*π^2))).continuousOn
  have H := Summable.hasProdUniformlyOn_nat_one_add (isCompact_closedBall (0:ℂ) R) hu hb hcts
  set F : ℂ → ℂ := fun x => ∏' i : ℕ, (1+4*x^2/(((2*i+1:ℂ)^2)*π^2)) with hF
  have hFc : ContinuousOn F K := by
    refine H.tendstoUniformlyOn_finsetRange.continuousOn (Filter.Frequently.of_forall fun n => ?_)
    exact continuousOn_finsetProd _ fun i _ => continuousOn_const.add (hcts i)
  have hsinhc2 : ∀ x : ℂ, sinhc (2*x) = sinhc x * Complex.cosh x := by
    intro x
    by_cases hx : x = 0
    · simp [sinhc, hx]
    · have h2 : 2*x ≠ 0 := mul_ne_zero two_ne_zero hx
      simp only [sinhc, hx, h2, ↓reduceIte, Complex.sinh_two_mul]
      field_simp
  have hgood : ∀ x ∈ K, sinhc x ≠ 0 → F x = Complex.cosh x := by
    intro x hx hs
    have h1 := H.hasProd hx
    have h2 := hasProd_sinh x
    have h3 := hasProd_sinh (2*x)
    have h4 : HasProd (fun k : ℕ => 1+(2*x)^2/(((k+1:ℂ)^2)*π^2)) (F x * sinhc x) := by
      refine HasProd.even_mul_odd ?_ ?_
      · convert h1 using 2 with k
        push_cast; ring
      · convert h2 using 2 with k
        have : (k:ℂ)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
        rw [show (((2*k+1:ℕ):ℂ)+1) = 2*((k:ℂ)+1) by push_cast; ring]
        field_simp
    have := h4.unique h3
    rw [hsinhc2, mul_comm] at this
    exact mul_left_cancel₀ hs this
  have hFz : F z = Complex.cosh z := by
    by_cases hs : sinhc z ≠ 0
    · exact hgood z (Metric.ball_subset_closedBall hzK) hs
    push Not at hs
    have hz0 : z ≠ 0 := by intro h; simp [sinhc, h] at hs
    have hsh : Complex.sinh z = 0 := by
      simp only [sinhc, hz0, ↓reduceIte] at hs
      exact (div_eq_zero_iff.mp hs).resolve_right hz0
    have hch : Complex.cosh z ≠ 0 := by
      intro h
      have := Complex.cosh_sq_sub_sinh_sq z
      rw [h, hsh] at this; norm_num at this
    have hlim : Tendsto (fun t : ℝ => z+t) (𝓝[≠] 0) (𝓝 z) := by
      have : Tendsto (fun t : ℝ => z+t) (𝓝 0) (𝓝 (z+((0:ℝ):ℂ))) :=
        (continuous_const.add Complex.continuous_ofReal).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    have hK : K ∈ 𝓝 z := Metric.closedBall_mem_nhds_of_mem hzK
    have hA := ((hFc.continuousAt hK).tendsto).comp hlim
    have hB := ((Complex.continuous_cosh.continuousAt (x := z)).tendsto).comp hlim
    have hev : ∀ᶠ t : ℝ in 𝓝[≠] 0, F (z+t) = Complex.cosh (z+t) := by
      have hin : ∀ᶠ t : ℝ in 𝓝[≠] 0, z+(t:ℂ) ∈ K := hlim.eventually (Filter.mem_of_superset hK
        (fun w hw => hw)) |>.mono fun t ht => ht
      filter_upwards [hin, self_mem_nhdsWithin] with t ht ht0
      apply hgood _ ht
      have hsh' : Complex.sinh (z+t) ≠ 0 := by
        rw [Complex.sinh_add, hsh, zero_mul, zero_add]
        refine mul_ne_zero hch ?_
        rw [← Complex.ofReal_sinh]
        exact_mod_cast fun h => ht0 (Real.sinh_eq_zero.mp h)
      by_cases h0 : z+(t:ℂ) = 0
      · simp [sinhc, h0]
      · simp only [sinhc, h0, ↓reduceIte]
        exact div_ne_zero hsh' h0
    exact tendsto_nhds_unique (hA.congr' (hev.mono fun t ht => by simp [Function.comp, ht])) hB
  have := H.hasProd (Metric.ball_subset_closedBall hzK)
  rw [hFz] at this
  exact this

/-- Off the imaginary lattice `πiℤ`, the rotated point `iz/π` avoids the integers. -/
private lemma hypR4_rot_mem {z : ℂ} (hz : ∀ n : ℤ, z≠(n:ℂ)*π*I) :
    I*z/π ∈ Complex.integerComplement := by
  have hπ : (π:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rintro ⟨n, hn⟩
  apply hz (-n)
  have h : I*z = (n:ℂ)*π := by rw [hn]; field_simp
  push_cast
  linear_combination (-I)*h + z*Complex.I_sq

/-- The Mittag-Leffler cotangent term at the rotated point `iz/π`. -/
private lemma hypR4_cotTerm_rot {z : ℂ} (hz : ∀ n : ℤ, z≠(n:ℂ)*π*I) (n : ℕ) :
    cotTerm (I*z/π) n = (-2*I*z*π)*(1/(z^2+(n+1:ℂ)^2*π^2)) := by
  have hπ : (π:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h1 : I*z - (n+1)*π ≠ 0 := by
    intro h; apply hz (-(n+1:ℤ)); push_cast
    linear_combination (-I)*h + z*Complex.I_sq
  have h2 : I*z + (n+1)*π ≠ 0 := by
    intro h; apply hz ((n+1:ℤ)); push_cast
    linear_combination (-I)*h + z*Complex.I_sq
  have h3 : z^2+(n+1:ℂ)^2*π^2 ≠ 0 := by
    intro h; apply mul_ne_zero h1 h2
    linear_combination -h + z^2*Complex.I_sq
  have e1 : I*z/π - (n+1) = (I*z - (n+1)*π)/π := by field_simp
  have e2 : I*z/π + (n+1) = (I*z + (n+1)*π)/π := by field_simp
  simp only [cotTerm]
  rw [e1, e2]
  field_simp
  linear_combination 2*I*z^3 * Complex.I_sq

/-- hasSum coth. -/
@[dlmf 4.36.E3]
theorem hasSum_coth_partialFractions {z : ℂ} (hz : ∀ n : ℤ, z≠(n:ℂ)*π*I) : HasSum (fun n : ℕ => 1/(z^2+(n+1:ℂ)^2*π^2)) ((coth z-z⁻¹)/(2*z)) := by
  have hπ : (π:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hz0 : z ≠ 0 := by simpa using hz 0
  have hs : Complex.sinh z ≠ 0 := fun h => by
    obtain ⟨k, hk⟩ := (sinh_zeros z).mp h; exact hz k hk
  have hc := (Complex.hasSum_cotTerm (hypR4_rot_mem hz)).div_const (-2*I*z*π)
  have hk : (-2*I*z*π) ≠ 0 := by simp [hz0, hπ, Complex.I_ne_zero]
  convert hc using 1
  · funext n; rw [hypR4_cotTerm_rot hz n]; field_simp
  · rw [show (π:ℂ)*(I*z/π) = z*I by field_simp, Complex.cot, Complex.cos_mul_I,
      Complex.sin_mul_I, coth]
    field_simp
    linear_combination (Complex.cosh z*z - Complex.sinh z) * Complex.I_sq

/-- The series with terms `(fun n : ℤ => 1/(z-(n:ℂ)*π*I)^2)` converges to `(csch z^2)`. -/
@[dlmf 4.36.E4]
theorem hasSum_csch_sq {z : ℂ} (hz : ∀ n : ℤ, z≠(n:ℂ)*π*I) : HasSum (fun n : ℤ => 1/(z-(n:ℂ)*π*I)^2) (csch z^2) := by
  sorry

/-- hasSum csch. -/
@[dlmf 4.36.E5]
theorem hasSum_csch_partialFractions {z : ℂ} (hz : ∀ n : ℤ, z≠(n:ℂ)*π*I) : HasSum (fun n : ℕ => (-1:ℂ)^(n+1)/(z^2+(n+1:ℂ)^2*π^2)) ((csch z-z⁻¹)/(2*z)) := by
  have hπ : (π:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hz0 : z ≠ 0 := by simpa using hz 0
  have hs : Complex.sinh z ≠ 0 := fun h => by
    obtain ⟨k, hk⟩ := (sinh_zeros z).mp h; exact hz k hk
  have hc := (Complex.hasSum_csc_partial_fraction (hypR4_rot_mem hz)).div_const (-2*I*z*π)
  have hk : (-2*I*z*π) ≠ 0 := by simp [hz0, hπ, Complex.I_ne_zero]
  convert hc using 1
  · funext n; rw [hypR4_cotTerm_rot hz n]; field_simp
  · rw [show (π:ℂ)*(I*z/π) = z*I by field_simp, Complex.sin_mul_I, csch]
    field_simp
    linear_combination (z - Complex.sinh z) * Complex.I_sq

end DLMF.Elementary
end
