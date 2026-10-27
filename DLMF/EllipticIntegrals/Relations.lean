/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.EllipticIntegrals.Symmetric
public import DLMF.Elementary.Trigonometric
public import Carlson.TwoVariable.R.ElementaryValues
public import Carlson.TwoVariable.Reduction

/-!
# Relations of elliptic integrals to other functions (DLMF §19.10)

DLMF §19.10(i) refers to §§20.9(i), 22.15(ii) and 23.6(iv) for the relations of Legendre's
integrals to theta, Jacobian and Weierstrass functions; those statements are acquired in the
chapters concerned (19.10.i.p1 is a cross-reference).

§19.10(ii) expresses the elementary inverse functions through `R_C` (19.10.1) and the
Gudermannian function through `R_C` (19.10.2). DLMF assumes `y > 0`; the formulas are real
formulas, with `R_C` evaluated at positive (or, for the endpoint cases, zero) real arguments.
DLMF does not state the ranges of `x` explicitly; we use the natural ones on which both sides
are defined and agree: `x > 0` for the logarithm, all real `x` for `arctan` and `arcsinh`,
`|x| < y` for `arctanh`, `|x| ≤ y` for `arcsin`, `0 ≤ x ≤ y` for `arccos` and `x ≥ y` for
`arccosh`. (For `x < 0` the `arccos` formula is false: its right side is even in `x`; for
example `arccos (-1/2) = 2π/3` while the right side is `π/3`.)

`R_C` is DLMF's `DLMF.EllipticIntegrals.symEllIntRC` (19.2.17). On positive arguments it is
`Carlson.TwoVariable.carlsonRC` of the companion library `lean-codes`, whose elementary values
(Carlson 1977, Exercise 6.9-16, formulas (6.9-15), (6.9-16)) are reused through homogeneity.

## References

* NIST DLMF §19.10.
* B. C. Carlson, *Special Functions of Applied Mathematics*, 1977, §6.9 (formalized in
  `lean-codes`, `Carlson.TwoVariable.R.ElementaryValues`).
-/

@[expose] public noncomputable section

open Complex Set
open scoped Real

namespace DLMF.EllipticIntegrals

open Carlson.TwoVariable (carlsonRC)

/-- Positive reals lie in the slit plane. -/
lemma ei19b_ofReal_mem_slitPlane {a : ℝ} (ha : 0 < a) : ((a : ℝ) : ℂ) ∈ slitPlane :=
  ofReal_mem_slitPlane.mpr ha

/-- `(y²)^{-1/2} = 1/y` for `y > 0`, as a complex power of a positive real. -/
lemma ei19b_sq_cpow_neg_half {y : ℝ} (hy : 0 < y) :
    (((y ^ 2 : ℝ) : ℂ)) ^ (-1 / 2 : ℂ) = (y : ℂ)⁻¹ := by
  rw [show (-1 / 2 : ℂ) = ((-1 / 2 : ℝ) : ℂ) by push_cast; ring,
    ← ofReal_cpow (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hy.le]
  norm_num
  rw [Real.rpow_neg_one]
  push_cast
  ring

/-- Homogeneity of DLMF's `R_C` for positive real arguments, in the form used below:
`R_C(y² a, y² b) = y⁻¹ R_C(a, b)` (Carlson's `R_C`), `y, a, b > 0`. -/
theorem ei19b_symEllIntRC_scale {y a b : ℝ} (hy : 0 < y) (ha : 0 < a) (hb : 0 < b) :
    symEllIntRC ((y ^ 2 * a : ℝ) : ℂ) ((y ^ 2 * b : ℝ) : ℂ) = (y : ℂ)⁻¹ * carlsonRC a b := by
  rw [symEllIntRC_eq_carlsonRC (ei19b_ofReal_mem_slitPlane (by positivity))
    (ei19b_ofReal_mem_slitPlane (by positivity))]
  have h := Carlson.TwoVariable.carlsonRC_mul_of_pos (l := y ^ 2) (by positivity)
    (ei19b_ofReal_mem_slitPlane ha) (ei19b_ofReal_mem_slitPlane hb)
  push_cast at h ⊢
  rw [h, ← ei19b_sq_cpow_neg_half hy]
  push_cast
  rfl

/-- `R_C(y², y² b) = y⁻¹ R_C(1, b)`, `y, b > 0`. -/
lemma ei19b_symEllIntRC_scale_one_left {y b : ℝ} (hy : 0 < y) (hb : 0 < b) :
    symEllIntRC ((y ^ 2 : ℝ) : ℂ) ((y ^ 2 * b : ℝ) : ℂ) = (y : ℂ)⁻¹ * carlsonRC 1 b := by
  have h := ei19b_symEllIntRC_scale hy one_pos hb
  rw [mul_one] at h
  rw [h, ofReal_one]

/-- `R_C(y² a, y²) = y⁻¹ R_C(a, 1)`, `y, a > 0`. -/
lemma ei19b_symEllIntRC_scale_one_right {y a : ℝ} (hy : 0 < y) (ha : 0 < a) :
    symEllIntRC ((y ^ 2 * a : ℝ) : ℂ) ((y ^ 2 : ℝ) : ℂ) = (y : ℂ)⁻¹ * carlsonRC a 1 := by
  have h := ei19b_symEllIntRC_scale hy ha one_pos
  rw [mul_one] at h
  rw [h, ofReal_one]

/-- Oddness of `artanh` on `(-1, 1)`. -/
lemma ei19b_artanh_neg {x : ℝ} (hx : |x| < 1) : Real.artanh (-x) = -Real.artanh x := by
  rw [abs_lt] at hx
  rw [Real.artanh_eq_half_log ⟨by linarith, by linarith⟩,
    Real.artanh_eq_half_log ⟨by linarith, by linarith⟩,
    show (1 + -x) / (1 - -x) = ((1 + x) / (1 - x))⁻¹ by
      rw [inv_div]; ring_nf, Real.log_inv]
  ring

/-- `log u = (u - 1) R_C(((u + 1)/2)², u)` for every `u > 0` (Carlson's `R_C`); Carlson's
(6.9-16) gives `u > 1`, and `u < 1` follows by homogeneity from `1/u`. -/
lemma ei19b_log_eq_mul_carlsonRC {u : ℝ} (hu : 0 < u) :
    (Real.log u : ℂ) = (u - 1) * carlsonRC (((u + 1) / 2) ^ 2 : ℝ) u := by
  rcases lt_trichotomy u 1 with h | rfl | h
  · have hv : 1 < u⁻¹ := (one_lt_inv₀ hu).mpr h
    have hl := Carlson.TwoVariable.log_eq_mul_carlsonRC hv
    have hs := Carlson.TwoVariable.carlsonRC_mul_of_pos (l := u ^ 2) (by positivity)
      (ei19b_ofReal_mem_slitPlane (a := ((u⁻¹ + 1) / 2) ^ 2) (by positivity))
      (ei19b_ofReal_mem_slitPlane (inv_pos.mpr hu))
    have hu0 : (u : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
    have e1 : ((u ^ 2 : ℝ) : ℂ) * (((((u⁻¹ + 1) / 2) ^ 2 : ℝ)) : ℂ) =
        ((((u + 1) / 2) ^ 2 : ℝ) : ℂ) := by
      push_cast; field_simp; ring
    have e2 : ((u ^ 2 : ℝ) : ℂ) * ((u⁻¹ : ℝ) : ℂ) = ((u : ℝ) : ℂ) := by
      push_cast; field_simp
    rw [e1, e2, ei19b_sq_cpow_neg_half hu] at hs
    rw [hs, Real.log_inv] at *
    push_cast at hl ⊢
    rw [show (Real.log u : ℂ) = -(-(Real.log u : ℂ)) by ring, hl]
    field_simp
    ring
  · simp
  · exact Carlson.TwoVariable.log_eq_mul_carlsonRC h

/-- DLMF 19.10.1 (first line): `ln(x/y) = (x - y) R_C(¼(x + y)², xy)` for `x, y > 0`. -/
@[dlmf 19.10.E1]
theorem log_div_eq_mul_symEllIntRC {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (Real.log (x / y) : ℂ) =
      (x - y) * symEllIntRC (((x + y) ^ 2 / 4 : ℝ) : ℂ) ((x * y : ℝ) : ℂ) := by
  set u := x / y with hu
  have hu0 : 0 < u := div_pos hx hy
  have hxu : x = y * u := by rw [hu]; field_simp
  have e1 : (x + y) ^ 2 / 4 = y ^ 2 * (((u + 1) / 2) ^ 2) := by rw [hxu]; ring
  have e2 : x * y = y ^ 2 * u := by rw [hxu]; ring
  rw [e1, e2, ei19b_symEllIntRC_scale hy (by positivity) hu0, ei19b_log_eq_mul_carlsonRC hu0, hxu]
  have : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  push_cast
  field_simp

/-- DLMF 19.10.1 (second line): `arctan(x/y) = x R_C(y², y² + x²)` for real `x` and `y > 0`. -/
@[dlmf 19.10.E1]
theorem arctan_div_eq_mul_symEllIntRC (x : ℝ) {y : ℝ} (hy : 0 < y) :
    (Real.arctan (x / y) : ℂ) = x * symEllIntRC ((y ^ 2 : ℝ) : ℂ) ((y ^ 2 + x ^ 2 : ℝ) : ℂ) := by
  set u := x / y with hu
  have hxu : x = y * u := by rw [hu]; field_simp
  have e2 : y ^ 2 + x ^ 2 = y ^ 2 * (1 + u ^ 2) := by rw [hxu]; ring
  rw [e2, ei19b_symEllIntRC_scale_one_left hy (by positivity),
    Carlson.TwoVariable.arctan_eq_mul_carlsonRC u, hxu]
  have : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  push_cast
  field_simp

/-- `artanh u = u R_C(1, 1 - u²)` for `|u| < 1` (Carlson's `R_C`; odd extension of Carlson's
`0 < u < 1`). -/
lemma ei19b_artanh_eq_mul_carlsonRC {u : ℝ} (hu : |u| < 1) :
    (Real.artanh u : ℂ) = u * carlsonRC 1 (1 - u ^ 2 : ℝ) := by
  rcases lt_trichotomy u 0 with h | rfl | h
  · have h' := Carlson.TwoVariable.artanh_eq_mul_carlsonRC (x := -u) (by linarith)
      (by rw [abs_lt] at hu; linarith)
    rw [ei19b_artanh_neg (by rw [abs_lt] at hu ⊢; constructor <;> linarith), neg_sq] at h'
    push_cast at h' ⊢
    linear_combination -h'
  · simp
  · exact Carlson.TwoVariable.artanh_eq_mul_carlsonRC h (by rw [abs_lt] at hu; linarith)

/-- DLMF 19.10.1 (third line): `arctanh(x/y) = x R_C(y², y² - x²)` for `|x| < y`. -/
@[dlmf 19.10.E1]
theorem artanh_div_eq_mul_symEllIntRC {x y : ℝ} (hxy : |x| < y) :
    (Real.artanh (x / y) : ℂ) = x * symEllIntRC ((y ^ 2 : ℝ) : ℂ) ((y ^ 2 - x ^ 2 : ℝ) : ℂ) := by
  have hy : 0 < y := lt_of_le_of_lt (abs_nonneg x) hxy
  set u := x / y with hu
  have hxu : x = y * u := by rw [hu]; field_simp
  have hu1 : |u| < 1 := by
    rw [hu, abs_div, abs_of_pos hy, div_lt_one hy]; exact hxy
  have hu2 : 0 < 1 - u ^ 2 := by
    have := sq_lt_one_iff_abs_lt_one u |>.mpr hu1; linarith
  have e2 : y ^ 2 - x ^ 2 = y ^ 2 * (1 - u ^ 2) := by rw [hxu]; ring
  rw [e2, ei19b_symEllIntRC_scale_one_left hy hu2, ei19b_artanh_eq_mul_carlsonRC hu1, hxu]
  have : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  push_cast
  field_simp

/-- `R_C(0, y²) = π/(2y)` for `y > 0` (a case of DLMF 19.6.15), from `R_C(0, y²) = R_F(0, y², y²)`
(19.16.6), (19.16.20) and `R_{-1/2}(½, ½; y², y²) = (y²)^{-1/2}` (19.16.11). -/
theorem ei19b_symEllIntRC_zero_sq {y : ℝ} (hy : 0 < y) :
    symEllIntRC 0 ((y ^ 2 : ℝ) : ℂ) = ((π / (2 * y) : ℝ) : ℂ) := by
  have hs : ((y ^ 2 : ℝ) : ℂ) ∈ slitPlane := ei19b_ofReal_mem_slitPlane (by positivity)
  rw [symEllIntRC_eq_symEllIntRF 0 (ei19c_not_isNegReal_of_mem_slitPlane hs),
    symEllIntRF_zero_left hs hs]
  have hv : (![((y ^ 2 : ℝ) : ℂ), ((y ^ 2 : ℝ) : ℂ)] : Fin 2 → ℂ) = fun _ => ((y ^ 2 : ℝ) : ℂ) := by
    funext i; fin_cases i <;> rfl
  rw [hv, symEllIntR_const _ _ hs (by simp [Fin.sum_univ_two]; norm_num),
    show (-(1 / 2 : ℂ)) = (-1 / 2 : ℂ) by ring, ei19b_sq_cpow_neg_half hy]
  have : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  push_cast
  field_simp

/-- DLMF 19.10.1 (fourth line): `arcsin(x/y) = x R_C(y² - x², y²)` for `|x| ≤ y`. -/
@[dlmf 19.10.E1]
theorem arcsin_div_eq_mul_symEllIntRC {x y : ℝ} (hxy : |x| ≤ y) (hy : 0 < y) :
    (Real.arcsin (x / y) : ℂ) = x * symEllIntRC ((y ^ 2 - x ^ 2 : ℝ) : ℂ) ((y ^ 2 : ℝ) : ℂ) := by
  have hyc : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  rcases hxy.lt_or_eq with h | h
  · set u := x / y with hu
    have hxu : x = y * u := by rw [hu]; field_simp
    have hu1 : |u| < 1 := by
      rw [hu, abs_div, abs_of_pos hy, div_lt_one hy]; exact h
    have hu2 : 0 < 1 - u ^ 2 := by
      have := sq_lt_one_iff_abs_lt_one u |>.mpr hu1; linarith
    have e2 : y ^ 2 - x ^ 2 = y ^ 2 * (1 - u ^ 2) := by rw [hxu]; ring
    have hodd : (Real.arcsin u : ℂ) = u * carlsonRC (1 - u ^ 2 : ℝ) 1 := by
      rw [abs_lt] at hu1
      rcases lt_trichotomy u 0 with h' | h' | h'
      · have := Carlson.TwoVariable.arcsin_eq_mul_carlsonRC (x := -u) (by linarith) (by linarith)
        rw [Real.arcsin_neg, neg_sq] at this
        push_cast at this ⊢
        linear_combination -this
      · simp [h']
      · exact Carlson.TwoVariable.arcsin_eq_mul_carlsonRC h' hu1.2
    rw [e2, ei19b_symEllIntRC_scale_one_right hy hu2, hodd, hxu]
    push_cast
    field_simp
  · have hx2 : x ^ 2 = y ^ 2 := by rw [← sq_abs, h]
    rw [hx2, sub_self, ofReal_zero, ei19b_symEllIntRC_zero_sq hy]
    rcases abs_eq hy.le |>.mp h with h' | h'
    · rw [h', div_self hy.ne', Real.arcsin_one]
      push_cast; field_simp
    · rw [h', neg_div, div_self hy.ne', Real.arcsin_neg, Real.arcsin_one]
      push_cast; field_simp

/-- DLMF 19.10.1 (sixth line): `arccos(x/y) = (y² - x²)^{1/2} R_C(x², y²)` for `0 ≤ x ≤ y`
(the formula is false for `x < 0`, where its right side is even in `x`). -/
@[dlmf 19.10.E1]
theorem arccos_div_eq_mul_symEllIntRC {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : 0 < y) :
    (Real.arccos (x / y) : ℂ) =
      (Real.sqrt (y ^ 2 - x ^ 2) : ℂ) * symEllIntRC ((x ^ 2 : ℝ) : ℂ) ((y ^ 2 : ℝ) : ℂ) := by
  have hyc : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  rcases hx.lt_or_eq with hx0 | rfl
  · rcases hxy.lt_or_eq with h | rfl
    · set u := x / y with hu
      have hxu : x = y * u := by rw [hu]; field_simp
      have hu0 : 0 < u := div_pos hx0 hy
      have hu1 : u < 1 := by rw [hu, div_lt_one hy]; exact h
      have e2 : x ^ 2 = y ^ 2 * u ^ 2 := by rw [hxu]; ring
      have e3 : Real.sqrt (y ^ 2 - x ^ 2) = y * Real.sqrt (1 - u ^ 2) := by
        rw [hxu, show y ^ 2 - (y * u) ^ 2 = y ^ 2 * (1 - u ^ 2) by ring,
          Real.sqrt_mul (by positivity), Real.sqrt_sq hy.le]
      rw [e3, e2, ei19b_symEllIntRC_scale_one_right hy (by positivity),
        Carlson.TwoVariable.arccos_eq_mul_carlsonRC hu0 hu1]
      push_cast
      field_simp
    · rw [div_self hy.ne', Real.arccos_one, sub_self, Real.sqrt_zero]
      simp
  · rw [zero_div, Real.arccos_zero, show ((0 : ℝ) ^ 2 : ℝ) = 0 by norm_num, ofReal_zero,
      ei19b_symEllIntRC_zero_sq hy, sub_zero, Real.sqrt_sq hy.le]
    push_cast
    field_simp

/-- DLMF 19.10.1 (fifth line): `arcsinh(x/y) = x R_C(y² + x², y²)` for real `x` and `y > 0`. -/
@[dlmf 19.10.E1]
theorem arsinh_div_eq_mul_symEllIntRC (x : ℝ) {y : ℝ} (hy : 0 < y) :
    (Real.arsinh (x / y) : ℂ) = x * symEllIntRC ((y ^ 2 + x ^ 2 : ℝ) : ℂ) ((y ^ 2 : ℝ) : ℂ) := by
  set u := x / y with hu
  have hxu : x = y * u := by rw [hu]; field_simp
  have e2 : y ^ 2 + x ^ 2 = y ^ 2 * (1 + u ^ 2) := by rw [hxu]; ring
  rw [e2, ei19b_symEllIntRC_scale_one_right hy (by positivity),
    Carlson.TwoVariable.arsinh_eq_mul_carlsonRC u, hxu]
  have : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  push_cast
  field_simp

/-- DLMF 19.10.1 (seventh line): `arccosh(x/y) = (x² - y²)^{1/2} R_C(x², y²)` for
`x ≥ y > 0`. -/
@[dlmf 19.10.E1]
theorem arcosh_div_eq_mul_symEllIntRC {x y : ℝ} (hy : 0 < y) (hxy : y ≤ x) :
    (Real.arcosh (x / y) : ℂ) =
      (Real.sqrt (x ^ 2 - y ^ 2) : ℂ) * symEllIntRC ((x ^ 2 : ℝ) : ℂ) ((y ^ 2 : ℝ) : ℂ) := by
  rcases hxy.lt_or_eq with h | rfl
  · set u := x / y with hu
    have hxu : x = y * u := by rw [hu]; field_simp
    have hu1 : 1 < u := by rw [hu, one_lt_div hy]; exact h
    have e2 : x ^ 2 = y ^ 2 * u ^ 2 := by rw [hxu]; ring
    have e3 : Real.sqrt (x ^ 2 - y ^ 2) = y * Real.sqrt (u ^ 2 - 1) := by
      rw [hxu, show (y * u) ^ 2 - y ^ 2 = y ^ 2 * (u ^ 2 - 1) by ring,
        Real.sqrt_mul (by positivity), Real.sqrt_sq hy.le]
    rw [e3, e2, ei19b_symEllIntRC_scale_one_right hy (by positivity),
      Carlson.TwoVariable.arcosh_eq_mul_carlsonRC hu1]
    have : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    push_cast
    field_simp
  · rw [div_self hy.ne', sub_self, Real.sqrt_zero]
    simp [Real.arcosh]

/-- DLMF 19.10.2: `(sinh φ) R_C(1, cosh² φ) = gd φ` for real `φ`, with the Gudermannian
`gd` of DLMF 4.23.39 (`DLMF.Elementary.gudermannian`). -/
@[dlmf 19.10.E2]
theorem sinh_mul_symEllIntRC_eq_gudermannian (φ : ℝ) :
    (Real.sinh φ : ℂ) * symEllIntRC 1 ((Real.cosh φ ^ 2 : ℝ) : ℂ) =
      (DLMF.Elementary.gudermannian φ : ℂ) := by
  rw [(DLMF.Elementary.gudermannian_elementary φ).2.2,
    Carlson.TwoVariable.arctan_eq_mul_carlsonRC, ← Real.cosh_sq', ← ofReal_one,
    symEllIntRC_eq_carlsonRC (ei19b_ofReal_mem_slitPlane one_pos)
      (ei19b_ofReal_mem_slitPlane (by positivity))]

end DLMF.EllipticIntegrals
