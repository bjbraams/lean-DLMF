/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ExpIntegrals.Basic.Functions
public import DLMF.Confluent.Basic.ExponentialIntegralSeries
public import DLMFMathlib.Analysis.Complex.FactorialSeries
public import DLMFMathlib.Analysis.Complex.SegmentPrimitive
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Exponential, sine and cosine integrals: basic properties (DLMF §6.2)

Power series, entireness, symmetries, the segment-integral definitions of DLMF §6.2 and the
derivatives of the functions defined in `DLMF.ExpIntegrals.Basic.Functions`.

## Main results

* `hasSum_Ein_complex`, `hasSum_Si_complex`, `hasSum_Cin_complex`: the power series
  (DLMF 6.6.4, 6.6.5).
* `expIntEin_entire`, `sinInt_entire`, `cosIntCin_entire`, `sinhInt_entire`: these functions
  are entire.
* `expIntEin_ofReal`, `sinInt_ofReal`, `cosIntCin_ofReal`, `cosInt_ofReal`: agreement with the
  real-variable definitions.
* `sinInt_odd`, `cosIntCin_even`, `expIntEin_mul_I`, `sinInt_mul_I`, `cosIntCin_mul_I`: parity
  and rotation by `i`.
* `expIntEin_segment_integral`, `sinInt_segment_integral`, `cosIntCin_segment_integral`,
  `sinhInt_segment_integral`, `coshInt_segment_integral`: the integral definitions
  (DLMF 6.2.3, 6.2.9, 6.2.12, 6.2.15, 6.2.16).
* `hasDerivAt_expIntEin_complex`, `hasDerivAt_sinInt_complex`, `hasDerivAt_cosIntCin_complex`,
  `hasDerivAt_cosInt_complex`: the derivatives.
* `sinInt_eq_aux`, `cosInt_eq_aux`, `hasDerivAt_expIntAuxF`, `hasDerivAt_expIntAuxG`: the
  auxiliary functions `f`, `g` (DLMF 6.2.19–6.2.21).

## Implementation notes

The relations to `E₁`, `Ei` and `li` (DLMF 6.2.1, 6.2.2, 6.2.4–6.2.8) and the limits at infinity
are in `DLMF.ExpIntegrals.AnalyticProperties`.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
open DLMF.Core

namespace DLMF.Confluent

/-- The series with terms `(fun k : ℕ => (-1 : ℂ)^k*z^(k+1)/((k+1).factorial*(k+1 : ℂ)))`
converges to `(expIntEin z)`. -/
@[dlmf 6.6.E4]
theorem hasSum_Ein_complex (z : ℂ) :
    HasSum (fun k : ℕ => (-1 : ℂ)^k*z^(k+1)/((k+1).factorial*(k+1 : ℂ))) (expIntEin z) := by
  simpa only [expIntEin, sinInt, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] using
    (summable_factorial_div_nat (c := fun k => (-1:ℂ)^k)
    (d := fun k => k+1) (by intro k; simp)
    (by intro i j hij; dsimp at hij; omega) (by intro k; omega) z).hasSum

/-- The series with terms `(fun k : ℕ => (-1 : ℂ)^k*z^(2*k+1)/((2*k+1).factorial*(2*k+1 : ℂ)))`
converges to `(sinInt z)`. -/
@[dlmf 6.6.E5]
theorem hasSum_Si_complex (z : ℂ) :
    HasSum (fun k : ℕ => (-1 : ℂ)^k*z^(2*k+1)/((2*k+1).factorial*(2*k+1 : ℂ))) (sinInt z) := by
  simpa only [expIntEin, sinInt, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] using
    (summable_factorial_div_nat (c := fun k => (-1:ℂ)^k)
    (d := fun k => 2*k+1) (by intro k; simp)
    (by intro i j hij; dsimp at hij; omega) (by intro k; omega) z).hasSum

/-- Entire differentiability from the defining convergent series. -/
theorem expIntEin_entire  :
    Differentiable ℂ expIntEin := by
  unfold expIntEin
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] using
    differentiable_tsum_factorial_div_nat (c := fun k => (-1 : ℂ)^k)
    (d := fun k => k+1) (by intro k; simp)
    (by intro i j hij; dsimp at hij; omega) (by intro k; omega)

/-- Entire differentiability from the defining convergent series. -/
theorem sinInt_entire  :
    Differentiable ℂ sinInt := by
  unfold sinInt
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] using
    differentiable_tsum_factorial_div_nat (c := fun k => (-1 : ℂ)^k)
    (d := fun k => 2*k+1) (by intro k; simp)
    (by intro i j hij; dsimp at hij; omega) (by intro k; omega)

/-- Entire differentiability from the defining convergent series. -/
theorem cosIntCin_entire  :
    Differentiable ℂ cosIntCin := by
  unfold cosIntCin
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] using
    differentiable_tsum_factorial_div_nat (c := fun k => (-1 : ℂ)^k)
    (d := fun k => 2*k+2) (by intro k; simp)
    (by intro i j hij; dsimp at hij; omega) (by intro k; omega)

/-- Entire differentiability from the defining convergent series. -/
theorem sinhInt_entire  :
    Differentiable ℂ sinhInt := by
  unfold sinhInt
  simpa only [one_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
    (differentiable_tsum_factorial_div_nat (c := fun _ => (1 : ℂ))
      (d := fun k => 2*k+1) (by intro k; simp)
      (by intro i j hij; dsimp at hij; omega) (by intro k; omega))

/-- Agreement with the existing real-variable definition. -/
theorem expIntEin_ofReal (x : ℝ) :
    expIntEin x = (Real.expIntEin x : ℂ) := by
  rw [← (Complex.hasSum_ofReal.mpr (Real.hasSum_expIntEin x)).tsum_eq]
  unfold expIntEin
  apply tsum_congr
  intro k
  push_cast
  ring

/-- Agreement with the existing real-variable definition. -/
theorem sinInt_ofReal (x : ℝ) :
    sinInt x = (Real.sinInt x : ℂ) := by
  rw [← (Complex.hasSum_ofReal.mpr (Real.hasSum_sinInt x)).tsum_eq]
  unfold sinInt
  apply tsum_congr
  intro k
  push_cast
  ring

/-- Agreement with the existing real-variable definition. -/
theorem cosIntCin_ofReal (x : ℝ) :
    cosIntCin x = (Real.cosIntCin x : ℂ) := by
  rw [← (Complex.hasSum_ofReal.mpr (Real.hasSum_cosIntCin x)).tsum_eq]
  unfold cosIntCin
  apply tsum_congr
  intro k
  push_cast
  ring

/-- Identity under the stated parameter and domain assumptions: `cosInt x = (Real.cosInt x : ℂ)`. -/
theorem cosInt_ofReal {x : ℝ} (hx : 0 < x) :
    cosInt x = (Real.cosInt x : ℂ) := by
  rw [cosInt, cosIntCin_ofReal, ← Complex.ofReal_log hx.le, Real.cosInt]
  push_cast
  ring

/-- Identity under the stated parameter and domain assumptions: `sinInt (-z) = -sinInt z`. -/
theorem sinInt_odd (z : ℂ) :
    sinInt (-z) = -sinInt z := by
  unfold sinInt
  rw [← tsum_neg]
  apply tsum_congr
  intro k
  rw [neg_pow z, show (-1:ℂ)^(2*k+1) = -1 by simp [pow_add, pow_mul]]
  ring

/-- Identity under the stated parameter and domain assumptions: `cosIntCin (-z) = cosIntCin z`. -/
theorem cosIntCin_even (z : ℂ) :
    cosIntCin (-z) = cosIntCin z := by
  unfold cosIntCin
  apply tsum_congr
  intro k
  rw [neg_pow z, show (-1:ℂ)^(2*k+2) = 1 by simp [pow_add, pow_mul], one_mul]

/-- The Cin series converges absolutely at every complex argument. -/
theorem hasSum_Cin_complex (z : ℂ) :
    HasSum (fun k : ℕ => (-1:ℂ)^k*z^(2*k+2)/((2*k+2).factorial*(2*k+2:ℂ))) (cosIntCin z) := by
  simpa only [cosIntCin, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
    (summable_factorial_div_nat (c := fun k => (-1:ℂ)^k) (d := fun k => 2*k+2)
      (by intro k; simp) (by intro i j hij; dsimp at hij; omega) (by intro k; omega) z).hasSum

/-- Separating even and odd terms of Ein at a rotated argument gives Cin and Si. -/
theorem expIntEin_mul_I (z : ℂ) : expIntEin (I*z)=cosIntCin z+I*sinInt z := by
  let F : ℕ → ℂ := fun k => (-1:ℂ)^k*(I*z)^(k+1)/((k+1).factorial*(k+1:ℂ))
  have he : HasSum (fun k => F (2*k)) (I*sinInt z) := by
    refine ((hasSum_Si_complex z).mul_left I).congr_fun fun k => ?_
    dsimp [F]
    rw [mul_pow, pow_add I, show I^(2*k)=(-1:ℂ)^k by rw [pow_mul, I_sq]]
    simp only [pow_one, pow_mul, neg_one_sq, one_pow, one_mul]
    push_cast
    ring
  have ho : HasSum (fun k => F (2*k+1)) (cosIntCin z) := by
    refine (hasSum_Cin_complex z).congr_fun fun k => ?_
    dsimp [F]
    rw [show 2*k+1+1=2*k+2 by omega, mul_pow,
      show I^(2*k+2)=(-1:ℂ)^(k+1) by rw [show 2*k+2=2*(k+1) by ring, pow_mul, I_sq],
      pow_succ (-1:ℂ)]
    simp only [pow_add, pow_mul, neg_one_sq, one_pow, one_mul, pow_one]
    push_cast
    ring
  have hs := (hasSum_Ein_complex (I*z)).unique (he.even_add_odd ho)
  simpa only [add_comm] using hs

/-- Rotation of the sine integral into the entire hyperbolic sine integral. -/
theorem sinInt_mul_I (z : ℂ) : sinInt (I*z)=I*sinhInt z := by
  unfold sinInt sinhInt
  rw [← tsum_mul_left]
  apply tsum_congr
  intro k
  rw [mul_pow,show I^(2*k+1)=(-1:ℂ)^k*I by rw [pow_add,pow_mul,I_sq,pow_one]]
  have hs : (-1:ℂ)^k*(-1:ℂ)^k=1 := by rw [← mul_pow,neg_one_mul,neg_neg,one_pow]
  calc
    _ = ((-1:ℂ)^k*(-1:ℂ)^k)*(I*z^(2*k+1)/((2*k+1).factorial*(2*k+1:ℂ))) := by ring
    _ = _ := by rw [hs]; ring

/-- Rotation of Cin expresses the nonlogarithmic part of the hyperbolic cosine integral. -/
theorem cosIntCin_mul_I (z : ℂ) :
    cosIntCin (I*z)= -(∑' k : ℕ, z^(2*k+2)/((2*k+2).factorial*(2*k+2:ℂ))) := by
  unfold cosIntCin
  rw [← tsum_neg]
  apply tsum_congr
  intro k
  rw [mul_pow,show I^(2*k+2)= -(-1:ℂ)^k by
    rw [show 2*k+2=2*(k+1) by ring,pow_mul,I_sq,pow_succ]; ring]
  have hs : (-1:ℂ)^k*(-1:ℂ)^k=1 := by rw [← mul_pow,neg_one_mul,neg_neg,one_pow]
  calc
    _ = ((-1:ℂ)^k*(-1:ℂ)^k)*(-z^(2*k+2)/((2*k+2).factorial*(2*k+2:ℂ))) := by ring
    _ = _ := by rw [hs]; ring

/-- Identity under the stated parameter and domain assumptions: `expIntEin z = primitive (fun t =>
(1-exp (-t))/t) z`. -/
@[dlmf 6.2.E3]
theorem expIntEin_segment_integral (z : ℂ) :
    expIntEin z = primitive (fun t => (1-exp (-t))/t) z := by
  let F : ℂ → ℂ := fun t : ℂ=>1-exp (-t)
  have hF : Differentiable ℂ F := by dsimp [F]; fun_prop
  have hF0 : F 0=0 := by simp [F]
  have hd := differentiable_dslope_entire hF 0
  have he : expIntEin=primitive (dslope F 0) := by
    apply eq_of_differentiable_of_eqOn_pos_reals expIntEin_entire (differentiable_primitive hd)
    intro x hx
    rw [expIntEin_ofReal,primitive_dslope_zero hF0,primitive_ofReal,Real.expIntEin,
      ← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun t ht=>?_)
    rw [uIoc_of_le hx.le] at ht
    dsimp [F]
    simp
  rw [he,primitive_dslope_zero hF0]

/-- Identity under the stated parameter and domain assumptions: `sinInt z = primitive (fun t =>
sin t/t) z`. -/
@[dlmf 6.2.E9]
theorem sinInt_segment_integral (z : ℂ) :
    sinInt z = primitive (fun t => sin t/t) z := by
  let F : ℂ → ℂ := Complex.sin
  have hF : Differentiable ℂ F := by dsimp [F]; fun_prop
  have hF0 : F 0=0 := by simp [F]
  have hd := differentiable_dslope_entire hF 0
  have he : sinInt=primitive (dslope F 0) := by
    apply eq_of_differentiable_of_eqOn_pos_reals sinInt_entire (differentiable_primitive hd)
    intro x hx
    rw [sinInt_ofReal,primitive_dslope_zero hF0,primitive_ofReal,Real.sinInt,
      ← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun t ht=>?_)
    rw [uIoc_of_le hx.le] at ht
    dsimp [F]
    rw [Real.sinc_of_ne_zero (ne_of_gt ht.1)]; push_cast; rfl
  rw [he,primitive_dslope_zero hF0]

/-- Identity under the stated parameter and domain assumptions: `cosIntCin z = primitive (fun t =>
(1-cos t)/t) z`. -/
@[dlmf 6.2.E12]
theorem cosIntCin_segment_integral (z : ℂ) :
    cosIntCin z = primitive (fun t => (1-cos t)/t) z := by
  let F : ℂ → ℂ := fun t : ℂ=>1-cos t
  have hF : Differentiable ℂ F := by dsimp [F]; fun_prop
  have hF0 : F 0=0 := by simp [F]
  have hd := differentiable_dslope_entire hF 0
  have he : cosIntCin=primitive (dslope F 0) := by
    apply eq_of_differentiable_of_eqOn_pos_reals cosIntCin_entire (differentiable_primitive hd)
    intro x hx
    rw [cosIntCin_ofReal,primitive_dslope_zero hF0,primitive_ofReal,Real.cosIntCin,
      ← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun t ht=>?_)
    rw [uIoc_of_le hx.le] at ht
    dsimp [F]
    simp
  rw [he,primitive_dslope_zero hF0]

/-- Identity under the stated parameter and domain assumptions: `sinhInt z = primitive (fun t =>
sinh t/t) z`. -/
@[dlmf 6.2.E15]
theorem sinhInt_segment_integral (z : ℂ) :
    sinhInt z = primitive (fun t => sinh t/t) z := by
  have h := sinInt_mul_I z
  rw [sinInt_segment_integral] at h
  have he : primitive (fun t => sin t/t) (I*z)=I*primitive (fun t=>sinh t/t) z := by
    simp only [primitive,segmentIntegral,sub_zero,zero_add]
    have hf : (fun t : ℝ => sin ((t:ℂ)*(I*z))/((t:ℂ)*(I*z)))=
        (fun t : ℝ => sinh ((t:ℂ)*z)/((t:ℂ)*z)) := by
      funext t
      rw [show (t:ℂ)*(I*z)=((t:ℂ)*z)*I by ring,Complex.sin_mul_I]
      field_simp
    rw [hf]
    ring
  rw [he] at h
  exact (mul_left_cancel₀ I_ne_zero h).symm

/-- Identity under the stated parameter and domain assumptions: `coshInt z =
Real.eulerMascheroniConstant + log z + primitive (fun t => (cosh t-1)/t) z`. -/
@[dlmf 6.2.E16]
theorem coshInt_segment_integral {z : ℂ} :
    coshInt z = Real.eulerMascheroniConstant + log z + primitive (fun t => (cosh t-1)/t) z := by
  have h := cosIntCin_mul_I z
  rw [cosIntCin_segment_integral] at h
  have he : primitive (fun t => (1-cos t)/t) (I*z)= -primitive (fun t=>(cosh t-1)/t) z := by
    simp only [primitive,segmentIntegral,sub_zero,zero_add]
    have hf : (fun t : ℝ => (1-cos ((t:ℂ)*(I*z)))/((t:ℂ)*(I*z)))=
        (fun t : ℝ => I*((cosh ((t:ℂ)*z)-1)/((t:ℂ)*z))) := by
      funext t
      rw [show (t:ℂ)*(I*z)=((t:ℂ)*z)*I by ring,Complex.cos_mul_I]
      field_simp
      ring_nf
      simp [I_sq]
    rw [hf,intervalIntegral.integral_const_mul,←mul_assoc,show I*z*I= -z by ring_nf; simp [I_sq]]
    ring
  rw [he] at h
  unfold coshInt
  linear_combination h

/-- A segment primitive of `F t / t`, with `F` entire and `F 0 = 0`, differentiates to
`F z / z` away from the origin. -/
theorem hasDerivAt_primitive_div_self {F : ℂ → ℂ} (hF : Differentiable ℂ F) (hF0 : F 0 = 0)
    {z : ℂ} (hz : z ≠ 0) :
    HasDerivAt (primitive (fun t => F t/t)) (F z/z) z := by
  have he : primitive (fun t => F t/t) = primitive (dslope F 0) :=
    funext fun w => (primitive_dslope_zero hF0 w).symm
  rw [he]
  have h := hasDerivAt_primitive (differentiable_dslope_entire hF 0) z
  rwa [dslope_of_ne _ hz, slope_def_field, hF0, sub_zero, sub_zero] at h

/-- The entire sine integral differentiates to `sin z / z` away from the origin. -/
theorem hasDerivAt_sinInt_complex {z : ℂ} (hz : z ≠ 0) :
    HasDerivAt sinInt (sin z/z) z := by
  rw [funext sinInt_segment_integral]
  exact hasDerivAt_primitive_div_self Complex.differentiable_sin (by simp) hz

/-- The entire complementary cosine integral differentiates to `(1 - cos z)/z` away from the
origin. -/
theorem hasDerivAt_cosIntCin_complex {z : ℂ} (hz : z ≠ 0) :
    HasDerivAt cosIntCin ((1-cos z)/z) z := by
  rw [funext cosIntCin_segment_integral]
  exact hasDerivAt_primitive_div_self (F := fun t => 1-cos t) (by fun_prop) (by simp) hz

/-- The principal cosine integral differentiates to `cos z / z` on the slit plane. -/
theorem hasDerivAt_cosInt_complex {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt cosInt (cos z/z) z := by
  have hz0 := slitPlane_ne_zero hz
  have h := ((hasDerivAt_cosIntCin_complex hz0).neg.add (Complex.hasDerivAt_log hz)).add_const
    (Real.eulerMascheroniConstant : ℂ)
  have he : cosInt = fun w => -cosIntCin w + log w + Real.eulerMascheroniConstant := rfl
  rw [he]
  convert h using 1
  field_simp
  ring

/-- The complementary exponential integral differentiates to `(1 - e^{-z})/z` off the origin. -/
theorem hasDerivAt_expIntEin_complex {z : ℂ} (hz : z ≠ 0) :
    HasDerivAt expIntEin ((1-exp (-z))/z) z := by
  rw [funext expIntEin_segment_integral]
  exact hasDerivAt_primitive_div_self (F := fun t => 1-exp (-t)) (by fun_prop) (by simp) hz

/-- Identity under the stated parameter and domain assumptions: `sinInt z = π/2 - expIntAuxF z *
cos z - expIntAuxG z * sin z`. -/
@[dlmf 6.2.E19]
theorem sinInt_eq_aux (z : ℂ) :
    sinInt z = π/2 - expIntAuxF z * cos z - expIntAuxG z * sin z := by
  have h := Complex.sin_sq_add_cos_sq z
  unfold expIntAuxF expIntAuxG sinIntTail
  linear_combination -(sinInt z-π/2)*h

/-- Identity under the stated parameter and domain assumptions: `cosInt z = expIntAuxF z * sin z -
expIntAuxG z * cos z`. -/
@[dlmf 6.2.E20]
theorem cosInt_eq_aux (z : ℂ) :
    cosInt z = expIntAuxF z * sin z - expIntAuxG z * cos z := by
  have h := Complex.sin_sq_add_cos_sq z
  unfold expIntAuxF expIntAuxG
  linear_combination -(cosInt z)*h

/-- At `z`, the function `expIntAuxF` has derivative `(-expIntAuxG z)`. -/
@[dlmf 6.2.E21]
theorem hasDerivAt_expIntAuxF {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt expIntAuxF (-expIntAuxG z) z := by
  have hz0 := slitPlane_ne_zero hz
  have hC := hasDerivAt_cosInt_complex hz
  have hS : HasDerivAt sinIntTail (sin z/z) z := (hasDerivAt_sinInt_complex hz0).sub_const _
  have h := (hC.mul (Complex.hasDerivAt_sin z)).sub (hS.mul (Complex.hasDerivAt_cos z))
  have he : expIntAuxF = fun w => cosInt w * sin w - sinIntTail w * cos w := rfl
  rw [he]
  convert h using 1
  unfold expIntAuxG
  field_simp
  ring

/-- At `z`, the function `expIntAuxG` has derivative `(expIntAuxF z - 1/z)`. -/
@[dlmf 6.2.E21]
theorem hasDerivAt_expIntAuxG {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt expIntAuxG (expIntAuxF z - 1/z) z := by
  have hz0 := slitPlane_ne_zero hz
  have hC := hasDerivAt_cosInt_complex hz
  have hS : HasDerivAt sinIntTail (sin z/z) z := (hasDerivAt_sinInt_complex hz0).sub_const _
  have h := (hC.neg.mul (Complex.hasDerivAt_cos z)).sub (hS.mul (Complex.hasDerivAt_sin z))
  have he : expIntAuxG = fun w => -cosInt w * cos w - sinIntTail w * sin w := rfl
  rw [he]
  convert h using 1
  have h1 := Complex.sin_sq_add_cos_sq z
  unfold expIntAuxF
  simp only [Pi.neg_apply]
  field_simp
  linear_combination h1

end DLMF.Confluent
