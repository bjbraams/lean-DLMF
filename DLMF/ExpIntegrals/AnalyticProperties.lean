/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ExpIntegrals.Basic

public import DLMF.Core.Framework
public import DLMFMathlib.Analysis.Complex.FactorialSeries
public import DLMF.Confluent.Integrals
public import DLMF.Confluent.ExpIntegral

/-!
# Entire and principal exponential, trigonometric and hyperbolic integrals

Canonical definitions are in `DLMF.ExpIntegrals.Basic`; this module develops their properties.

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
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
    rw [expIntEin_ofReal,primitive_dslope_zero hF0,primitive_ofReal,Real.expIntEin,← intervalIntegral.integral_ofReal]
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
    rw [sinInt_ofReal,primitive_dslope_zero hF0,primitive_ofReal,Real.sinInt,← intervalIntegral.integral_ofReal]
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
    rw [cosIntCin_ofReal,primitive_dslope_zero hF0,primitive_ofReal,Real.cosIntCin,← intervalIntegral.integral_ofReal]
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
theorem coshInt_segment_integral {z : ℂ} (hz : z ∈ slitPlane) :
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

/-- Identity under the stated parameter and domain assumptions: `genExpIntE 1 z = exp (-z) * ∫ t :
ℝ in Ioi 0, exp (-t : ℂ)/(t+z)`. -/
@[dlmf 6.2.E2]
theorem expIntE1_stieltjes {z : ℂ} (hz : z ∈ slitPlane) :
    genExpIntE 1 z = exp (-z) * ∫ t : ℝ in Ioi 0, exp (-t : ℂ)/(t+z) := by
  -- Tricomi's Stieltjes representation 13.4.5 at `a = b = 1`.
  have h := kummerU_stieltjes (a := 1) (b := 1) hz (by simp) (by simp)
  rw [genExpIntE_eq_cpow_mul_kummerU, h]
  simp only [sub_self, cpow_zero, add_sub_cancel_right, Gamma_one, kummerU_zero]
  have hi : (∫ t : ℝ in Ioi 0, (1 : ℂ) * exp (-(t : ℂ)) * 1 / ((t : ℂ) + z)) =
      ∫ t : ℝ in Ioi 0, exp (-t : ℂ)/(t+z) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp
  rw [hi]; ring

/-- Zero upper parameter in the regularized Kummer function, including Gamma zeros. -/
theorem regularizedConfluent_zero_upper (b z : ℂ) :
    regularizedHGFun {0} {b} z=(Gamma b)⁻¹ := by
  rw [regularizedHGFun_eq_tsum]
  rw [tsum_eq_single 0]
  · simp [regularizedHGFunCoeff_singleton, poch_zero]
  · intro n hn
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    simp [regularizedHGFunCoeff_singleton, poch_succ_left]

/-- The parameter derivative of the regularized lower-Gamma Kummer series identifies Ein. -/
theorem hasDerivAt_regularizedConfluent_Ein (z : ℂ) :
    HasDerivAt (fun a : ℂ => regularizedHGFun {a} {a+1} (-z))
      (Real.eulerMascheroniConstant-expIntEin z) 0 := by
  have hG : HasDerivAt (fun w : ℂ => (Gamma (w+1))⁻¹) (Real.eulerMascheroniConstant:ℂ) 0 := by
    have h := Complex.hasDerivAt_Gamma_one.inv (by simp)
    have h' : HasDerivAt (fun w : ℂ => (Gamma w)⁻¹) _ 1 :=
      h.congr_of_eventuallyEq (Eventually.of_forall fun w => rfl)
    have hh := h'.comp_of_eq 0 ((hasDerivAt_id (0:ℂ)).add_const 1) (by simp)
    exact (hh.congr_of_eventuallyEq (Eventually.of_forall fun w => rfl)).congr_deriv (by simp)
  have hc (k : ℕ) : deriv (fun w : ℂ => poch w (k+1)*(-z)^(k+1)/(k+1).factorial*
        (Gamma (w+1+(k+1:ℕ)))⁻¹) 0 = (-z)^(k+1)/((k+1).factorial*(k+1:ℂ)) := by
    have hp : HasDerivAt (fun w : ℂ => poch w (k+1)) (k.factorial:ℂ) 0 := by
      have hd : Differentiable ℂ (fun w : ℂ => poch (w+1) k) :=
        (Polynomial.differentiable (ascPochhammer ℂ k)).comp (differentiable_id.add_const 1)
      have h := (hasDerivAt_id (0:ℂ)).mul hd.differentiableAt.hasDerivAt
      have he : (fun w : ℂ => poch w (k+1))=(fun w => w*poch (w+1) k) :=
        funext fun w => poch_succ_left w k
      rw [he]
      have h' : HasDerivAt (fun w : ℂ => w*poch (w+1) k) _ 0 :=
        h.congr_of_eventuallyEq (Eventually.of_forall fun w => rfl)
      simpa only [id_eq, zero_add, zero_mul, add_zero, one_mul, poch_nat_one] using h'
    have hi : Differentiable ℂ (fun w : ℂ => (Gamma (w+1+(k+1:ℕ)))⁻¹) :=
      differentiable_one_div_Gamma.comp (by fun_prop)
    have h := ((hp.mul_const ((-z)^(k+1))).div_const ((k+1).factorial:ℂ)).mul
      hi.differentiableAt.hasDerivAt
    have he : (1:ℂ)+(k+1:ℕ)=(k+1:ℕ)+1 := by push_cast; ring
    have h' : HasDerivAt (fun w : ℂ => poch w (k+1)*(-z)^(k+1)/(k+1).factorial*
        (Gamma (w+1+(k+1:ℕ)))⁻¹) _ 0 := h.congr_of_eventuallyEq (Eventually.of_forall fun w => rfl)
    rw [h'.deriv]
    simp only [show poch (0:ℂ) (k+1)=0 by simp [poch_succ_left], zero_add,
      zero_mul, zero_div, add_zero, he, Gamma_nat_eq_factorial]
    field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k),
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (k+1))]
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    ring
  have hs := hasSum_deriv_regularizedConfluent_comp differentiable_id (differentiable_id.add_const 1) (-z) 0
  simp only [id_eq] at hs
  have hh : deriv (fun w : ℂ => poch w 0*(-z)^0/((0:ℕ).factorial:ℂ)*(Gamma (w+1+(0:ℕ)))⁻¹) 0=
      (Real.eulerMascheroniConstant:ℂ) := by
    simpa only [poch_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, one_mul,
      div_one, Nat.cast_zero, add_zero] using hG.deriv
  have ht := (hasSum_nat_add_iff' 1).mpr hs
  simp only [Finset.sum_range_one, hh] at ht
  have hEin : HasSum (fun k : ℕ => (-1:ℂ)^k*z^(k+1)/((k+1).factorial*(k+1:ℂ))) (expIntEin z) := by
    simpa only [expIntEin, Nat.cast_add, Nat.cast_one] using
      (summable_factorial_div_nat (c := fun k => (-1:ℂ)^k) (d := fun k => k+1)
        (by intro k; simp) (by intro i j hij; dsimp at hij; omega) (by intro k; omega) z).hasSum
  have ht' : HasSum (fun k : ℕ => deriv (fun w : ℂ => poch w (k+1)*(-z)^(k+1)/(k+1).factorial*
      (Gamma (w+1+(k+1:ℕ)))⁻¹) 0) (-expIntEin z) :=
    hEin.neg.congr_fun (fun k => by rw [hc, neg_pow z, pow_succ]; ring)
  have heq := ht.unique ht'
  have hd : HasDerivAt (fun a : ℂ => regularizedHGFun {a} {a+1} (-z))
      (deriv (fun a : ℂ => regularizedHGFun {a} {a+1} (-z)) 0) 0 :=
    (differentiable_regularizedConfluent_comp differentiable_id
      (differentiable_id.add_const 1) (-z) 0).hasDerivAt
  refine hd.congr_deriv ?_
  linear_combination heq

/-- Identity under the stated parameter and domain assumptions: `genExpIntE 1 z = expIntEin z -
log z - Real.eulerMascheroniConstant`. -/
@[dlmf 6.2.E4]
theorem expIntE1_eq_Ein_complex {z : ℂ} (hz : z ≠ 0) :
    genExpIntE 1 z = expIntEin z - log z - Real.eulerMascheroniConstant := by
  have hR := (hasDerivAt_regularizedConfluent_Ein z).comp_of_eq 1
    ((hasDerivAt_id (1:ℂ)).sub_const 1) (by simp)
  have hP := ((hasDerivAt_id (1:ℂ)).const_sub 1).const_cpow (c := z) (Or.inl hz)
  have hG : Differentiable ℂ (fun c : ℂ => (Gamma (2-c))⁻¹) :=
    differentiable_one_div_Gamma.comp (by fun_prop)
  have heq (c : ℂ) : tricomiD 1 c z=exp z*
      (regularizedHGFun {c-1} {(c-1)+1} (-z)-z^(1-c))*(Gamma (2-c))⁻¹ := by
    rw [tricomiD, regularizedConfluent_kummer_transform 1 c z,
      regularizedConfluent_kummer_transform (1-c+1) (2-c) z]
    rw [show (2:ℂ)-c-(1-c+1)=0 by ring, regularizedConfluent_zero_upper]
    simp only [Gamma_one, inv_one, mul_one]
    rw [show (c-1)+1=c by ring, show (1:ℂ)-c+1=2-c by ring]
    ring
  have hd := (((hR.sub hP).const_mul (exp z)).mul hG.differentiableAt.hasDerivAt)
  have hd' : HasDerivAt (fun c : ℂ => tricomiD 1 c z)
      (exp z*(Real.eulerMascheroniConstant-expIntEin z+log z)) 1 := by
    refine (hd.congr_of_eventuallyEq (Eventually.of_forall heq)).congr_deriv ?_
    simp only [Function.comp_apply, Pi.sub_apply, id_eq, sub_self, zero_add, mul_one, cpow_zero, one_mul, neg_one_mul,
      regularizedConfluent_zero_upper, show (2:ℂ)-1=1 by norm_num, Gamma_one, inv_one, sub_zero, mul_zero, add_zero]
    ring
  rw [genExpIntE_eq_exp_mul_kummerU 1 hz]
  norm_num
  have hU := kummerU_nat_eq_deriv 1 1 hz
  norm_num at hU
  rw [hU, hd'.deriv]
  have he : exp (-z)*exp z=1 := by rw [← Complex.exp_add]; simp
  linear_combination -(Real.eulerMascheroniConstant-expIntEin z+log z)*he

/-- The complementary exponential integral differentiates to `(1 - e^{-z})/z` off the origin. -/
theorem hasDerivAt_expIntEin_complex {z : ℂ} (hz : z ≠ 0) :
    HasDerivAt expIntEin ((1-exp (-z))/z) z := by
  rw [funext expIntEin_segment_integral]
  exact hasDerivAt_primitive_div_self (F := fun t => 1-exp (-t)) (by fun_prop) (by simp) hz

/-- The `E₁` tail integral converges on every right half-line with positive endpoint. -/
theorem hasIntegralAtTop_exp_neg_div {ε : ℝ} (hε : 0 < ε) :
    HasIntegralAtTop (fun t : ℝ => exp (-t : ℂ)/(t : ℂ)) ε (genExpIntE 1 ε) := by
  have hint : IntegrableOn (fun t : ℝ => Real.exp (-t)/t) (Ioi ε) := by
    refine Integrable.mono' ((exp_neg_integrableOn_Ioi ε one_pos).div_const ε) ?_ ?_
    · exact (ContinuousOn.div (by fun_prop) continuousOn_id
        fun t ht => (lt_trans hε ht).ne').aestronglyMeasurable measurableSet_Ioi
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => ?_)
      have ht0 : 0 < t := lt_trans hε ht
      rw [Real.norm_eq_abs, abs_of_pos (div_pos (Real.exp_pos _) ht0), neg_one_mul]
      exact div_le_div_of_nonneg_left (Real.exp_pos _).le hε (le_of_lt ht)
  have hc : IntegrableOn (fun t : ℝ => exp (-t : ℂ)/(t : ℂ)) (Ioi ε) := by
    refine (hint.ofReal).congr_fun (fun t _ => ?_) measurableSet_Ioi
    change ((Real.exp (-t)/t : ℝ) : ℂ) = _
    rw [Complex.ofReal_div, Complex.ofReal_exp, Complex.ofReal_neg]
  have h := intervalIntegral_tendsto_integral_Ioi ε hc tendsto_id
  have he : (∫ t in Ioi ε, ((Real.exp (-t)/t : ℝ) : ℂ)) = ∫ t in Ioi ε, exp (-t : ℂ)/(t : ℂ) :=
    setIntegral_congr_fun measurableSet_Ioi fun t _ => by
      rw [Complex.ofReal_div, Complex.ofReal_exp, Complex.ofReal_neg]
  rw [genExpIntE_one_eq_integral hε, ← integral_complex_ofReal, he]
  exact h

/-- Identity under the stated parameter and domain assumptions: `HasPrincipalValueIoi (fun t : ℝ
=> exp (-t : ℂ)/(t : ℂ)) (-x) 0 (-Real.expIntEi x)`. -/
@[dlmf 6.2.E5]
theorem Real.expIntEi_principalValue {x : ℝ} (hx : 0 < x) :
    HasPrincipalValueIoi (fun t : ℝ => exp (-t : ℂ)/(t : ℂ)) (-x) 0 (-Real.expIntEi x) := by
  have himp (ε : ℝ) (hε : 0 < ε) :
      improperAtTop (fun t : ℝ => exp (-t : ℂ)/(t : ℂ)) ε = genExpIntE 1 ε :=
    (hasIntegralAtTop_exp_neg_div hε).limUnder_eq
  refine ⟨by linarith, fun ε hε => ?_, ?_⟩
  · rw [zero_add] at *
    rw [himp ε hε]
    exact hasIntegralAtTop_exp_neg_div hε
  -- closed form of the regularized integral for 0 < ε < x
  have hG (t : ℝ) (ht : t < 0) : HasDerivAt (fun t : ℝ => (Real.log (-t) : ℂ) - DLMF.Confluent.expIntEin t)
      (exp (-t : ℂ)/(t : ℂ)) t := by
    have ht0 : (t:ℂ) ≠ 0 := by exact_mod_cast ht.ne
    have hl : HasDerivAt (fun t : ℝ => Real.log (-t)) (t⁻¹) t := by
      have := ((hasDerivAt_neg t).log (by linarith : -t ≠ 0))
      convert this using 1; field_simp
    have h := (hl.ofReal_comp).sub ((hasDerivAt_expIntEin_complex ht0).comp_ofReal)
    convert h using 1
    push_cast
    field_simp
    ring_nf
  have hclosed : ∀ᶠ ε in 𝓝[>] (0:ℝ),
      (∫ t in -x..(0:ℝ)-ε, exp (-t : ℂ)/(t : ℂ)) + improperAtTop (fun t : ℝ => exp (-t : ℂ)/(t : ℂ)) (0+ε)
        = DLMF.Confluent.expIntEin (-x) - Real.log x - Real.eulerMascheroniConstant
          - DLMF.Confluent.expIntEin (-(ε:ℂ)) + DLMF.Confluent.expIntEin ε := by
    filter_upwards [Ioo_mem_nhdsGT hx] with ε hε
    rw [zero_add, zero_sub, himp ε hε.1, genExpIntE_one_eq_Ein hε.1]
    push_cast
    rw [← expIntEin_ofReal]
    have hle : -x ≤ -ε := by linarith [hε.2]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hG t (by
        rw [uIcc_of_le hle] at ht; linarith [ht.2, hε.1]))
      (ContinuousOn.intervalIntegrable (ContinuousOn.div (Continuous.continuousOn (by fun_prop))
        (Continuous.continuousOn (by fun_prop)) fun t ht => by
          rw [uIcc_of_le hle] at ht
          exact_mod_cast (show t ≠ 0 by linarith [ht.2, hε.1])))]
    push_cast
    ring_nf
  refine Tendsto.congr' (EventuallyEq.symm hclosed) ?_
  have hc : Continuous DLMF.Confluent.expIntEin := expIntEin_entire.continuous
  have h0 : Tendsto (fun ε : ℝ => DLMF.Confluent.expIntEin (ε:ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have := (hc.comp Complex.continuous_ofReal).tendsto 0
    simpa [DLMF.Confluent.expIntEin, Function.comp_def] using this.mono_left nhdsWithin_le_nhds
  have h0' : Tendsto (fun ε : ℝ => DLMF.Confluent.expIntEin (-(ε:ℂ))) (𝓝[>] 0) (𝓝 0) := by
    have := (hc.comp (Complex.continuous_ofReal.neg)).tendsto 0
    simpa [DLMF.Confluent.expIntEin, Function.comp_def] using this.mono_left nhdsWithin_le_nhds
  have h := ((tendsto_const_nhds (x := DLMF.Confluent.expIntEin (-x) - Real.log x - Real.eulerMascheroniConstant)).sub
    h0').add h0
  convert h using 2
  rw [Real.expIntEi, abs_of_pos hx, show -(x:ℂ) = ((-x:ℝ):ℂ) by push_cast; ring, expIntEin_ofReal]
  push_cast
  simp only [Complex.ofReal_re]
  ring

/-- Identity under the stated parameter and domain assumptions: `(Real.expIntEi (-x) : ℂ) =
-genExpIntE 1 x`. -/
@[dlmf 6.2.E6]
theorem Real.expIntEi_negative {x : ℝ} (hx : 0 < x) :
    (Real.expIntEi (-x) : ℂ) = -genExpIntE 1 x := by
  rw [Real.expIntEi]
  simp only [Complex.ofReal_neg, neg_neg]
  rw [DLMF.Confluent.expIntEin_ofReal, Complex.ofReal_re,
    genExpIntE_one_eq_Ein hx, abs_neg, abs_of_pos hx]
  push_cast
  ring

/-- Identity under the stated parameter and domain assumptions: `(Real.expIntEi (ε*x) : ℂ) =
-expIntEin (-ε*x) + Real.log x + Real.eulerMascheroniConstant`. -/
@[dlmf 6.2.E7]
theorem Real.expIntEi_Ein {x : ℝ} (hx : 0 < x) {ε : ℝ} (hε : ε=1 ∨ ε = -1) :
    (Real.expIntEi (ε*x) : ℂ) = -expIntEin (-ε*x) + Real.log x + Real.eulerMascheroniConstant := by
  rw [Real.expIntEi]
  have he : -((ε*x:ℝ):ℂ)=-(ε:ℂ)*x := by push_cast; ring
  have hEin : DLMF.Confluent.expIntEin (-(ε:ℂ)*x)=(Real.expIntEin (-ε*x):ℂ) := by
    convert DLMF.Confluent.expIntEin_ofReal (-ε*x) using 1 <;> push_cast <;> ring
  rw [he, hEin]
  have habs : |ε*x|=x := by rcases hε with rfl | rfl <;> simp [abs_of_pos hx]
  rw [habs]
  simp only [Complex.ofReal_re]
  push_cast
  ring

/-- `|Ei(-u)| ≤ e^{-u}/u` for `u > 0`. -/
theorem liPV_abs_expIntEi_neg_le {u : ℝ} (hu : 0 < u) :
    |Real.expIntEi (-u)| ≤ Real.exp (-u) / u := by
  have h := Real.expIntEi_negative hu
  rw [genExpIntE_one_eq_integral hu] at h
  have h' : Real.expIntEi (-u) = -∫ t in Ioi u, Real.exp (-t) / t := by exact_mod_cast h
  have hnn : 0 ≤ ∫ t in Ioi u, Real.exp (-t) / t :=
    setIntegral_nonneg measurableSet_Ioi fun t ht => by
      have : 0 < t := lt_trans hu ht
      positivity
  have hle : (∫ t in Ioi u, Real.exp (-t) / t) ≤ ∫ t in Ioi u, Real.exp (-t) / u := by
    refine integral_mono_of_nonneg ?_ ?_ ?_
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => ?_)
      have : 0 < t := lt_trans hu ht
      simp only [Pi.zero_apply]; positivity
    · exact (integrableOn_exp_neg_Ioi u).div_const u
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => ?_)
      exact div_le_div_of_nonneg_left (Real.exp_pos _).le hu (le_of_lt ht)
  rw [integral_div, integral_exp_neg_Ioi] at hle
  rw [h', abs_neg, abs_of_nonneg hnn]
  exact hle

/-- `li(δ) → 0` as `δ → 0⁺`. -/
theorem liPV_tendsto_logIntLi_zero :
    Tendsto Real.logIntLi (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hlog : Tendsto (fun δ : ℝ => -Real.log δ) (𝓝[>] 0) atTop :=
    tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  have hb : Tendsto (fun u : ℝ => Real.exp (-u) / u) atTop (𝓝 0) := by
    have := Real.tendsto_exp_neg_atTop_nhds_zero.mul (tendsto_inv_atTop_zero (𝕜 := ℝ))
    simpa [div_eq_mul_inv] using this
  refine squeeze_zero_norm' ?_ (hb.comp hlog)
  filter_upwards [hlog.eventually_gt_atTop 0, self_mem_nhdsWithin] with δ hδ hδ0
  rw [Real.norm_eq_abs, Real.logIntLi, show Real.log δ = -(-Real.log δ) by ring]
  exact liPV_abs_expIntEi_neg_le hδ

/-- `li(t) = γ + log|log t| - Ein(-log t)`. -/
theorem liPV_logIntLi_eq (t : ℝ) : Real.logIntLi t =
    Real.eulerMascheroniConstant + Real.log (Real.log t) - Real.expIntEin (-Real.log t) := by
  rw [Real.logIntLi, Real.expIntEi, Real.log_abs,
    show -((Real.log t : ℝ) : ℂ) = ((-Real.log t : ℝ) : ℂ) by push_cast; ring,
    expIntEin_ofReal, ofReal_re]

/-- The real `Ein` differentiates to `(1 - e^{-t})/t` off the origin. -/
theorem liPV_hasDerivAt_ein {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt Real.expIntEin ((1 - Real.exp (-t)) / t) t := by
  have h := (hasDerivAt_expIntEin_complex (z := (t : ℂ)) (by exact_mod_cast ht)).real_of_complex
  have hf : (fun y : ℝ => (expIntEin (y : ℂ)).re) = Real.expIntEin := by
    funext y; rw [expIntEin_ofReal, ofReal_re]
  rw [hf] at h
  convert h using 1
  rw [← ofReal_neg, ← ofReal_exp, ← ofReal_one, ← ofReal_sub, ← ofReal_div, ofReal_re]

/-- `li' = 1/log` on `(0, ∞) \ {1}`. -/
theorem liPV_hasDerivAt {t : ℝ} (ht : 0 < t) (ht1 : t ≠ 1) :
    HasDerivAt Real.logIntLi (1 / Real.log t) t := by
  have hl : Real.log t ≠ 0 := by
    intro h; rcases Real.log_eq_zero.mp h with h | h | h <;> [linarith; exact ht1 h; linarith]
  rw [funext liPV_logIntLi_eq]
  have h1 := ((Real.hasDerivAt_log ht.ne').log hl).const_add Real.eulerMascheroniConstant
  have h2 := (liPV_hasDerivAt_ein (neg_ne_zero.mpr hl)).comp t (Real.hasDerivAt_log ht.ne').neg
  refine (h1.sub h2).congr_deriv ?_
  rw [neg_neg, Real.exp_log ht]
  field_simp
  ring

/-- The integrand `1/log t` is continuous on `[0, b]` for `b < 1` (with `1/log 0 = 0`). -/
theorem liPV_continuousOn_left {b : ℝ} (hb : b < 1) :
    ContinuousOn (fun t : ℝ => 1 / Real.log t) (Icc 0 b) := by
  intro t ht
  rcases eq_or_lt_of_le ht.1 with h | h
  · subst h
    refine ContinuousAt.continuousWithinAt ?_
    rw [← continuousWithinAt_compl_self, ContinuousWithinAt]
    simp only [Real.log_zero, div_zero, one_div]
    exact Real.tendsto_log_nhdsNE_zero.inv_tendsto_atBot
  · refine ContinuousAt.continuousWithinAt (continuousAt_const.div
      (Real.continuousAt_log h.ne') ?_)
    exact (Real.log_neg h (by linarith [ht.2])).ne

/-- `li(1-ε) - li(1+ε) → 0`. -/
theorem liPV_tendsto_sub :
    Tendsto (fun ε : ℝ => Real.logIntLi (1 - ε) - Real.logIntLi (1 + ε)) (𝓝[>] 0) (𝓝 0) := by
  have hs := (Real.hasDerivAt_log one_ne_zero).tendsto_slope_zero
  simp only [Real.log_one, sub_zero, inv_one, smul_eq_mul] at hs
  have hp : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝[≠] 0) :=
    tendsto_nhdsWithin_mono_left (fun x hx => ne_of_gt hx) tendsto_id
  have hn : Tendsto (fun ε : ℝ => -ε) (𝓝[>] 0) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa using (continuous_neg.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact neg_ne_zero.mpr (ne_of_gt hε)
  have hr : Tendsto (fun ε : ℝ => |(-ε)⁻¹ * Real.log (1 + -ε)| / |ε⁻¹ * Real.log (1 + ε)|)
      (𝓝[>] 0) (𝓝 (|1| / |1|)) :=
    ((hs.comp hn).abs).div ((hs.comp hp).abs) (by norm_num)
  have hL : Tendsto (fun ε : ℝ => Real.log (|(-ε)⁻¹ * Real.log (1 + -ε)| /
      |ε⁻¹ * Real.log (1 + ε)|)) (𝓝[>] 0) (𝓝 0) := by
    have := ((Real.continuousAt_log (by norm_num : (|1| / |1| : ℝ) ≠ 0)).tendsto).comp hr
    simp only [abs_one, div_one, Real.log_one] at this
    exact this
  have hE : Tendsto (fun ε : ℝ => Real.expIntEin (-Real.log (1 - ε)) -
      Real.expIntEin (-Real.log (1 + ε))) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous Real.expIntEin := by
      have : Real.expIntEin = fun y : ℝ => (expIntEin (y : ℂ)).re := by
        funext y; rw [expIntEin_ofReal, ofReal_re]
      rw [this]; exact Complex.continuous_re.comp (expIntEin_entire.continuous.comp
        continuous_ofReal)
    have hg : ∀ σ : ℝ, Tendsto (fun ε : ℝ => Real.expIntEin (-Real.log (1 + σ * ε))) (𝓝[>] 0)
        (𝓝 (Real.expIntEin (-Real.log (1 + σ * 0)))) := by
      intro σ
      have h0 : ContinuousAt (fun ε : ℝ => 1 + σ * ε) 0 := by fun_prop
      have hcont : ContinuousAt (fun ε : ℝ => Real.expIntEin (-Real.log (1 + σ * ε))) 0 :=
        hc.continuousAt.comp (h0.log (by simp)).neg
      exact hcont.tendsto.mono_left nhdsWithin_le_nhds
    have := (hg (-1)).sub (hg 1)
    simp only [mul_zero, add_zero, sub_self, neg_one_mul, one_mul, ← sub_eq_add_neg] at this
    exact this
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), Real.logIntLi (1 - ε) - Real.logIntLi (1 + ε) =
      Real.log (|(-ε)⁻¹ * Real.log (1 + -ε)| / |ε⁻¹ * Real.log (1 + ε)|) -
      (Real.expIntEin (-Real.log (1 - ε)) - Real.expIntEin (-Real.log (1 + ε))) := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ) < 1)] with ε hε
    have h1 : Real.log (1 - ε) ≠ 0 := (Real.log_neg (by linarith [hε.2]) (by linarith [hε.1])).ne
    have h2 : Real.log (1 + ε) ≠ 0 := (Real.log_pos (by linarith [hε.1])).ne'
    have hε0 : ε ≠ 0 := hε.1.ne'
    rw [liPV_logIntLi_eq, liPV_logIntLi_eq, abs_mul, abs_mul, ← sub_eq_add_neg, abs_inv, abs_inv,
      abs_neg, mul_div_mul_left _ _ (inv_ne_zero (abs_ne_zero.mpr hε0)),
      Real.log_div (abs_ne_zero.mpr h1) (abs_ne_zero.mpr h2), Real.log_abs, Real.log_abs]
    ring
  refine Tendsto.congr' (EventuallyEq.symm hev) ?_
  simpa using hL.sub hE

/-- The map `(fun ε : ℝ => (∫ t in (0 : ℝ)..(1-ε), 1/Real.log t) + ∫ t in (1+ε)..x, 1/Real.log t)`
tends to `(𝓝 (Real.logIntLi x))` along `(𝓝[>] (0 : ℝ))`. -/
@[dlmf 6.2.E8, dlmf 4.10.E7]
theorem Real.logIntLi_principalValue {x : ℝ} (hx : 1 < x) :
    Tendsto (fun ε : ℝ => (∫ t in (0 : ℝ)..(1-ε), 1/Real.log t) + ∫ t in (1+ε)..x, 1/Real.log t) (𝓝[>] (0 : ℝ)) (𝓝 (Real.logIntLi x)) := by
  have hleft : ∀ ε : ℝ, 0 < ε → ε < 1 →
      (∫ t in (0 : ℝ)..(1-ε), 1/Real.log t) = Real.logIntLi (1 - ε) := by
    intro ε hε hε1
    set G : ℝ → ℝ := fun t => if t = 0 then 0 else Real.logIntLi t with hG
    have hGe : ∀ t : ℝ, t ≠ 0 → G =ᶠ[𝓝 t] Real.logIntLi := fun t ht => by
      filter_upwards [isOpen_ne.mem_nhds ht] with s hs
      simp [G, hs]
    have hGc : ContinuousOn G (Icc 0 (1 - ε)) := by
      intro t ht
      rcases eq_or_lt_of_le ht.1 with h | h
      · subst h
        have h0 : ContinuousWithinAt G (Ioi 0) 0 := by
          have : G 0 = 0 := by simp [G]
          rw [ContinuousWithinAt, this]
          refine liPV_tendsto_logIntLi_zero.congr' ?_
          filter_upwards [self_mem_nhdsWithin] with s hs
          simp [G, ne_of_gt (show (0:ℝ) < s from hs)]
        exact (continuousWithinAt_Ioi_iff_Ici.mp h0).mono Icc_subset_Ici_self
      · have hd := liPV_hasDerivAt h (by linarith [ht.2])
        exact (hd.continuousAt.congr (hGe t h.ne').symm).continuousWithinAt
    have hGd : ∀ t ∈ Ioo 0 (1 - ε), HasDerivAt G (1 / Real.log t) t := fun t ht =>
      (liPV_hasDerivAt ht.1 (by linarith [ht.2])).congr_of_eventuallyEq (hGe t ht.1.ne')
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by linarith) hGc hGd
      ((liPV_continuousOn_left (by linarith)).intervalIntegrable_of_Icc (by linarith))]
    simp [G, show (1 : ℝ) - ε ≠ 0 by linarith]
  have hright : ∀ ε : ℝ, 0 < ε → 1 + ε < x →
      (∫ t in (1+ε)..x, 1/Real.log t) = Real.logIntLi x - Real.logIntLi (1 + ε) := by
    intro ε hε hεx
    have hpos : ∀ t ∈ uIcc (1 + ε) x, 1 < t := fun t ht => by
      rw [uIcc_of_le hεx.le] at ht; linarith [ht.1]
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht =>
      liPV_hasDerivAt (by linarith [hpos t ht]) (ne_of_gt (hpos t ht))) ?_
    refine ContinuousOn.intervalIntegrable fun t ht => ?_
    have h1 := hpos t ht
    exact (continuousAt_const.div (Real.continuousAt_log (by linarith))
      (Real.log_pos h1).ne').continuousWithinAt
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (∫ t in (0 : ℝ)..(1-ε), 1/Real.log t) + (∫ t in (1+ε)..x, 1/Real.log t) =
        Real.logIntLi x + (Real.logIntLi (1 - ε) - Real.logIntLi (1 + ε)) := by
    filter_upwards [Ioo_mem_nhdsGT (lt_min one_pos (sub_pos.mpr hx))] with ε hε
    have h1 : ε < 1 := lt_of_lt_of_le hε.2 (min_le_left _ _)
    have h2 : ε < x - 1 := lt_of_lt_of_le hε.2 (min_le_right _ _)
    rw [hleft ε hε.1 h1, hright ε hε.1 (by linarith)]
    ring
  refine Tendsto.congr' (EventuallyEq.symm hev) ?_
  simpa using (tendsto_const_nhds (x := Real.logIntLi x)).add liPV_tendsto_sub

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

/-- The principal logarithms of the two quarter-turns in the right half-plane. -/
theorem log_quarter_turn {z : ℂ} (hz : 0 < z.re) :
    log (I*z)=log z+π*I/2 ∧ log (-I*z)=log z-π*I/2 := by
  have hz0 : z≠0 := by intro h; simp [h] at hz
  have ha := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz))
  constructor
  · rw [Complex.log_mul I_ne_zero hz0 (by simp only [arg_I, Set.mem_Ioc]; constructor <;> linarith [Real.pi_pos]), log_I]
    ring
  · rw [Complex.log_mul (neg_ne_zero.mpr I_ne_zero) hz0 (by simp only [arg_neg_I, Set.mem_Ioc]; constructor <;> linarith [Real.pi_pos]), log_neg_I]
    ring

/-- Identity under the stated parameter and domain assumptions: `sinInt z = I/2*(genExpIntE 1
(-I*z)-genExpIntE 1 (I*z))+π/2`. -/
@[dlmf 6.5.E5]
theorem sinInt_eq_E1 {z : ℂ} (hz : 0 < z.re) :
    sinInt z = I/2*(genExpIntE 1 (-I*z)-genExpIntE 1 (I*z))+π/2 := by
  have hz0 : z≠0 := by intro h; simp [h] at hz
  have hlog := log_quarter_turn hz
  have hp := expIntE1_eq_Ein_complex (mul_ne_zero I_ne_zero hz0)
  have hm := expIntE1_eq_Ein_complex (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hz0)
  rw [expIntEin_mul_I, hlog.1] at hp
  rw [show -I*z=I*(-z) by ring, expIntEin_mul_I, sinInt_odd, cosIntCin_even] at hm
  rw [show I*(-z)=-I*z by ring, hlog.2] at hm
  linear_combination (norm := ring_nf) -I/2*(hm-hp) <;> simp [I_sq] <;> ring

/-- Identity under the stated parameter and domain assumptions: `cosInt z = -(genExpIntE 1
(I*z)+genExpIntE 1 (-I*z))/2`. -/
@[dlmf 6.5.E6]
theorem cosInt_eq_E1 {z : ℂ} (hz : 0 < z.re) :
    cosInt z = -(genExpIntE 1 (I*z)+genExpIntE 1 (-I*z))/2 := by
  have hz0 : z≠0 := by intro h; simp [h] at hz
  have hlog := log_quarter_turn hz
  have hp := expIntE1_eq_Ein_complex (mul_ne_zero I_ne_zero hz0)
  have hm := expIntE1_eq_Ein_complex (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hz0)
  rw [expIntEin_mul_I, hlog.1] at hp
  rw [show -I*z=I*(-z) by ring, expIntEin_mul_I, sinInt_odd, cosIntCin_even] at hm
  rw [show I*(-z)=-I*z by ring, hlog.2] at hm
  unfold cosInt
  linear_combination (hp+hm)/2

/-- Identity under the stated parameter and domain assumptions: `expIntAuxG z + ε*I*expIntAuxF z =
genExpIntE 1 (-ε*I*z)*exp (-ε*I*z)`. -/
@[dlmf 6.5.E7]
theorem expIntAux_eq_E1 {z : ℂ} (hz : 0 < z.re) {ε : ℝ} (hε : ε=1 ∨ ε = -1) :
    expIntAuxG z + ε*I*expIntAuxF z = genExpIntE 1 (-ε*I*z)*exp (-ε*I*z) := by
  have hs := sinInt_eq_E1 hz
  have hc := cosInt_eq_E1 hz
  have ht := Complex.sin_sq_add_cos_sq z
  have hp : exp (-I*z)=cos z-I*sin z := by
    rw [show -I*z=(-z)*I by ring, Complex.exp_mul_I]; simp [mul_comm, sub_eq_add_neg]
  have hm : exp (I*z)=cos z+I*sin z := by
    rw [show I*z=z*I by ring, Complex.exp_mul_I]; simp [mul_comm, sub_eq_add_neg]
  rcases hε with rfl | rfl
  · simp only [Complex.ofReal_one, one_mul, neg_mul, neg_neg]
    rw [show -(I*z)=-I*z by ring, hp]
    unfold expIntAuxF expIntAuxG sinIntTail
    rw [hs,hc]
    ring_nf
    simp [I_sq]
    ring
  · simp only [Complex.ofReal_neg, Complex.ofReal_one, neg_one_mul, neg_neg, one_mul]
    rw [hm]
    unfold expIntAuxF expIntAuxG sinIntTail
    rw [hs,hc]
    ring_nf
    simp [I_sq]
    ring

/-- An improper integral on a half-line from an antiderivative with a limit at infinity. -/
theorem hasIntegralAtTop_of_hasDerivAt_of_tendsto {f F : ℝ → ℂ} {a : ℝ} {L : ℂ}
    (hd : ∀ t, a ≤ t → HasDerivAt F (f t) t) (hc : ContinuousOn f (Ici a))
    (hl : Tendsto F atTop (𝓝 L)) : HasIntegralAtTop f a (L - F a) := by
  unfold HasIntegralAtTop
  refine (hl.sub_const (F a)).congr' ?_
  filter_upwards [eventually_ge_atTop a] with R hR
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hd x (by rw [uIcc_of_le hR] at hx; exact hx.1))
    ((hc.mono Icc_subset_Ici_self).intervalIntegrable_of_Icc hR)]

/-- Improper integrals add when both integrands are integrable on bounded intervals. -/
theorem _root_.DLMF.HasIntegralAtTop.add {f g : ℝ → ℂ} {a : ℝ} {u v : ℂ} (hf : HasIntegralAtTop f a u)
    (hg : HasIntegralAtTop g a v) (hfi : ∀ R, a ≤ R → IntervalIntegrable f volume a R)
    (hgi : ∀ R, a ≤ R → IntervalIntegrable g volume a R) :
    HasIntegralAtTop (fun t => f t+g t) a (u+v) := by
  unfold HasIntegralAtTop at *
  refine (hf.add hg).congr' ?_
  filter_upwards [eventually_ge_atTop a] with R hR
  rw [intervalIntegral.integral_add (hfi R hR) (hgi R hR)]

/-- Improper integrals scale by constants. -/
theorem _root_.DLMF.HasIntegralAtTop.const_mul {f : ℝ → ℂ} {a : ℝ} {u : ℂ} (hf : HasIntegralAtTop f a u)
    (c : ℂ) : HasIntegralAtTop (fun t => c*f t) a (c*u) := by
  unfold HasIntegralAtTop at *
  refine (hf.const_mul c).congr' (Eventually.of_forall fun R => ?_)
  exact (intervalIntegral.integral_const_mul c f).symm

/-- Changing the integrand off the half-line does not change the improper integral. -/
theorem _root_.DLMF.HasIntegralAtTop.congr {f g : ℝ → ℂ} {a : ℝ} {u : ℂ} (hf : HasIntegralAtTop f a u)
    (h : ∀ t, a ≤ t → f t = g t) : HasIntegralAtTop g a u := by
  unfold HasIntegralAtTop at *
  refine hf.congr' ?_
  filter_upwards [eventually_ge_atTop a] with R hR
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le hR] at ht
  exact h t ht.1

/-- A ray `(w + t) c` with `‖c‖ = 1` and `δ < re c` eventually enters the sector filter. -/
theorem tendsto_ray_sectorAtTop (w c : ℂ) (hc : ‖c‖ = 1) {δ : ℝ} (hδ : 0 ≤ δ) (hδc : δ < c.re) :
    Tendsto (fun t : ℝ => (w+t)*c) atTop (sectorAtTop δ) := by
  have hn (t : ℝ) : ‖(w+t)*c‖ = ‖w+t‖ := by rw [norm_mul, hc, mul_one]
  have hlow (t : ℝ) : t - ‖w‖ ≤ ‖w+t‖ := by
    have h := norm_sub_norm_le (t:ℂ) (-w)
    rw [sub_neg_eq_add, add_comm, Complex.norm_real, norm_neg, Real.norm_eq_abs] at h
    linarith [le_abs_self t]
  rw [sectorAtTop, tendsto_inf, tendsto_principal, tendsto_comap_iff]
  constructor
  · refine tendsto_atTop_mono (fun t => (hn t).symm ▸ hlow t) ?_
    exact tendsto_atTop_add_const_right _ _ tendsto_id
  · have hpos : 0 < c.re - δ := by linarith
    filter_upwards [eventually_ge_atTop ((1+δ)*‖w‖/(c.re-δ))] with t ht
    simp only [hn]
    have hup : ‖w+t‖ ≤ ‖w‖ + t := by
      have := norm_add_le w (t:ℂ)
      have ht0 : 0 ≤ t := le_trans (by positivity) ht
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0] at this
      exact this
    have hre : ((w+t)*c).re = (w*c).re + t*c.re := by simp [add_mul]
    have hwc : -‖w‖ ≤ (w*c).re := by
      have := neg_abs_le (w*c).re
      have h2 := abs_re_le_norm (w*c)
      rw [norm_mul, hc, mul_one] at h2
      linarith
    have ht' : (1+δ)*‖w‖ ≤ t*(c.re-δ) := by
      rwa [div_le_iff₀ hpos] at ht
    rw [hre]
    nlinarith

/-- The rotated sector filter is the sector filter after rotation. -/
theorem tendsto_rotSectorAtTop_of_mul {α : Type*} {l : Filter α} {f : α → ℂ} (δ β : ℝ)
    (h : Tendsto (fun x => f x * exp (β*I)) l (sectorAtTop δ)) :
    Tendsto f l (rotSectorAtTop δ β) := tendsto_comap_iff.mpr h

/-- `ζ ^ (-a) → 0` along the rotated sector when `re a > 0`. -/
theorem tendsto_cpow_neg_rotSectorAtTop {a : ℂ} (ha : 0 < a.re) (δ β : ℝ) :
    Tendsto (fun z : ℂ => z^(-a)) (rotSectorAtTop δ β) (𝓝 0) := by
  have hn : Tendsto (fun z : ℂ => ‖z‖) (rotSectorAtTop δ β) atTop := by
    have := (tendsto_norm_sectorAtTop δ).comp (tendsto_rotSectorAtTop δ β)
    refine this.congr fun z => ?_
    simp [norm_exp_ofReal_mul_I]
  have hr : Tendsto (fun r : ℝ => r^(-a.re)*Real.exp (π*|(-a).im|)) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop ha).mul_const (Real.exp (π*|(-a).im|))
  refine squeeze_zero_norm' ?_ (hr.comp hn)
  filter_upwards with z
  have := norm_cpow_le_exp z (-a)
  simpa using this

/-- Tricomi `U(a,b,ζ) → 0` along a rotated sector when `re a > 0`. -/
theorem tendsto_kummerU_rotSectorAtTop {a : ℂ} (b : ℂ) (ha : 0 < a.re) {δ β : ℝ} (hδ : 0 < δ)
    (hβ : |β| < π/2) :
    Tendsto (fun z => kummerU a b z) (rotSectorAtTop δ β) (𝓝 0) := by
  have h := hasAsymptoticExpansion_kummerU_rotSector a b hδ hβ 0
  simp only [Finset.range_zero, Finset.sum_empty, sub_zero, CharP.cast_eq_zero, zero_add] at h
  exact h.trans_tendsto (tendsto_cpow_neg_rotSectorAtTop ha δ β)

/-- `e^{-ζ} U(a,b,ζ) → 0` along a sector, for all parameters. -/
theorem tendsto_exp_neg_mul_kummerU_sectorAtTop (a b : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun z => exp (-z)*kummerU a b z) (sectorAtTop δ) (𝓝 0) := by
  have h := hasAsymptoticExpansion_kummerU_sector a b hδ 0
  simp only [Finset.range_zero, Finset.sum_empty, sub_zero, CharP.cast_eq_zero, zero_add] at h
  refine ((isBigO_refl (fun z : ℂ => exp (-z)) _).mul h).trans_tendsto ?_
  have hr : Tendsto (fun r : ℝ => r^(-a.re)*Real.exp (-δ*r)*Real.exp (π*|(-a).im|)) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (-a.re) δ hδ).mul_const
      (Real.exp (π*|(-a).im|))
  refine squeeze_zero_norm' ?_ (hr.comp (tendsto_norm_sectorAtTop δ))
  rw [sectorAtTop, eventually_inf_principal]
  filter_upwards with z hz
  rw [norm_mul, Complex.norm_exp, Function.comp_apply]
  have h1 := norm_cpow_le_exp z (-a)
  have h2 : Real.exp (-z).re ≤ Real.exp (-δ*‖z‖) := by
    rw [Real.exp_le_exp, neg_re]; linarith
  calc Real.exp (-z).re*‖z^(-a)‖ ≤ Real.exp (-δ*‖z‖)*(‖z‖^(-a).re*Real.exp (π*|(-a).im|)) :=
        mul_le_mul h2 h1 (norm_nonneg _) (Real.exp_pos _).le
    _ = _ := by simp; ring

/-- The horizontal ray `z + t` enters the sector `|ζ|/2 ≤ re ζ`. -/
theorem tendsto_add_ofReal_sectorAtTop (z : ℂ) :
    Tendsto (fun t : ℝ => z+t) atTop (sectorAtTop (1/2)) := by
  simpa using tendsto_ray_sectorAtTop z 1 (by simp) (by norm_num) (by norm_num)

/-- The rotated horizontal ray `ε i (z + t)` enters a rotated sector. -/
theorem tendsto_mul_I_add_ofReal_rotSectorAtTop (z : ℂ) {ε : ℝ} (hε : ε=1 ∨ ε = -1) :
    Tendsto (fun t : ℝ => ε*I*(z+t)) atTop (rotSectorAtTop (1/2) (-ε*(π/4))) := by
  apply tendsto_rotSectorAtTop_of_mul
  have hs : (1/2:ℝ) < Real.sqrt 2/2 := by
    have : (1:ℝ) < Real.sqrt 2 := by
      rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    linarith
  have hc : ‖ε*I*exp ((-ε*(π/4):ℝ)*I)‖ = 1 := by
    rw [norm_mul, norm_mul, norm_exp_ofReal_mul_I]; rcases hε with rfl | rfl <;> simp
  have hre : (ε*I*exp ((-ε*(π/4):ℝ)*I)).re = Real.sqrt 2/2 := by
    rw [show ((-ε*(π/4):ℝ):ℂ)*I = ((-ε*(π/4):ℝ):ℂ)*I from rfl, Complex.exp_mul_I]
    rw [← ofReal_cos, ← ofReal_sin]
    rcases hε with rfl | rfl
    · simp [Real.cos_neg, Real.sin_neg, Real.cos_pi_div_four, Real.sin_pi_div_four]
    · simp [Real.cos_pi_div_four, Real.sin_pi_div_four]
  have h := tendsto_ray_sectorAtTop (δ := 1/2) z (ε*I*exp ((-ε*(π/4):ℝ)*I)) hc (by norm_num) (by rw [hre]; exact hs)
  refine h.congr fun t => ?_
  ring

/-- `E₁(ζ) → 0` along the rotated horizontal rays `ε i (z+t)`. -/
theorem tendsto_expIntE1_mul_I_add_ofReal (z : ℂ) {ε : ℝ} (hε : ε=1 ∨ ε = -1) :
    Tendsto (fun t : ℝ => genExpIntE 1 (ε*I*(z+t))) atTop (𝓝 0) := by
  have hβ : |-ε*(π/4)| < π/2 := by
    rcases hε with rfl | rfl <;> simp [abs_of_pos (by positivity : (0:ℝ) < π/4)] <;> linarith [Real.pi_pos]
  have hr := tendsto_mul_I_add_ofReal_rotSectorAtTop z hε
  have hU := (tendsto_kummerU_rotSectorAtTop (a := 1) 1 (by norm_num) (by norm_num) hβ).comp hr
  have hU' := hU.norm.mul_const (Real.exp (ε*z.im))
  rw [norm_zero, zero_mul] at hU'
  refine squeeze_zero_norm' ?_ hU'
  have hn : ∀ᶠ t : ℝ in atTop, ε*I*(z+t) ≠ 0 := by
    have := (tendsto_norm_sectorAtTop (1/2)).comp ((tendsto_rotSectorAtTop _ _).comp hr)
    filter_upwards [this.eventually_gt_atTop 0] with t ht h0
    simp [h0] at ht
  filter_upwards [hn] with t ht
  rw [genExpIntE_eq_exp_mul_kummerU 1 ht, show (2:ℂ)-1=1 by norm_num, norm_mul, Complex.norm_exp,
    Function.comp_apply, mul_comm]
  apply le_of_eq
  congr 2
  rcases hε with rfl | rfl <;> simp

/-- `E₁(z+t) → 0` along horizontal rays. -/
theorem tendsto_expIntE1_add_ofReal (z : ℂ) :
    Tendsto (fun t : ℝ => genExpIntE 1 (z+t)) atTop (𝓝 0) := by
  have h := (tendsto_exp_neg_mul_kummerU_sectorAtTop 1 1 (by norm_num : (0:ℝ) < 1/2)).comp
    (tendsto_add_ofReal_sectorAtTop z)
  refine h.congr' ?_
  have := (tendsto_norm_sectorAtTop (1/2)).comp (tendsto_add_ofReal_sectorAtTop z)
  filter_upwards [this.eventually_gt_atTop 0] with t ht
  have ht0 : z+t ≠ 0 := by intro h0; simp [h0] at ht
  simp [genExpIntE_eq_exp_mul_kummerU 1 ht0]
  norm_num

/-- `Γ(a,z+t) → 0` along horizontal rays. -/
theorem tendsto_upperIncGamma_add_ofReal (a z : ℂ) :
    Tendsto (fun t : ℝ => upperIncGamma a (z+t)) atTop (𝓝 0) :=
  (tendsto_exp_neg_mul_kummerU_sectorAtTop (1-a) (1-a) (by norm_num : (0:ℝ) < 1/2)).comp
    (tendsto_add_ofReal_sectorAtTop z)

/-- Eventually a horizontal ray lies in the right half-plane. -/
theorem eventually_re_add_ofReal_pos (z : ℂ) : ∀ᶠ t : ℝ in atTop, 0 < (z+t).re := by
  filter_upwards [eventually_gt_atTop (-z.re)] with t ht
  simp; linarith

/-- `si(z+t) → 0` along horizontal rays. -/
theorem tendsto_sinIntTail_add_ofReal (z : ℂ) :
    Tendsto (fun t : ℝ => sinIntTail (z+t)) atTop (𝓝 0) := by
  have h1 := tendsto_expIntE1_mul_I_add_ofReal z (ε := -1) (Or.inr rfl)
  have h2 := tendsto_expIntE1_mul_I_add_ofReal z (ε := 1) (Or.inl rfl)
  have h := (h1.sub h2).const_mul (I/2)
  rw [sub_zero, mul_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_re_add_ofReal_pos z] with t ht
  rw [sinIntTail, sinInt_eq_E1 ht]
  push_cast
  ring_nf

/-- `Ci(z+t) → 0` along horizontal rays. -/
theorem tendsto_cosInt_add_ofReal (z : ℂ) :
    Tendsto (fun t : ℝ => cosInt (z+t)) atTop (𝓝 0) := by
  have h1 := tendsto_expIntE1_mul_I_add_ofReal z (ε := -1) (Or.inr rfl)
  have h2 := tendsto_expIntE1_mul_I_add_ofReal z (ε := 1) (Or.inl rfl)
  have h := (h2.add h1).neg.div_const 2
  rw [add_zero, neg_zero, zero_div] at h
  refine h.congr' ?_
  filter_upwards [eventually_re_add_ofReal_pos z] with t ht
  rw [cosInt_eq_E1 ht]
  push_cast
  ring_nf

/-- Points `z+t`, `t ≥ 0`, of a horizontal ray from the slit plane stay in it. -/
theorem add_ofReal_mem_slitPlane {z : ℂ} (hz : z ∈ slitPlane) {t : ℝ} (ht : 0 ≤ t) :
    z+t ∈ slitPlane := by
  rcases hz with h | h
  · left; simp; linarith
  · right; simpa using h

/-- Differentiating along a horizontal ray. -/
theorem hasDerivAt_comp_add_ofReal {g : ℂ → ℂ} {g' z : ℂ} {t : ℝ} (h : HasDerivAt g g' (z+t)) :
    HasDerivAt (fun s : ℝ => g (z+s)) g' t := by
  have := h.comp (t:ℂ) ((hasDerivAt_id (t:ℂ)).const_add z)
  simpa using this.comp_ofReal

/-- `E₀(z) = e^{-z}/z`. -/
theorem genExpIntE_zero_eq (z : ℂ) : genExpIntE 0 z = exp (-z)/z := by
  rw [genExpIntE, sub_zero, upperIncGamma_one, zero_sub, cpow_neg_one]; ring

/-- Horizontal-ray integral representation: `HasIntegralAtTop (fun t : ℝ => exp (-(z+t))/(z+t)) 0
(genExpIntE 1 z)`. -/
@[dlmf 6.2.E1]
theorem expIntE1_horizontal_integral {z : ℂ} (hz : z ∈ slitPlane) :
    HasIntegralAtTop (fun t : ℝ => exp (-(z+t))/(z+t)) 0 (genExpIntE 1 z) := by
  have hd : ∀ t : ℝ, 0 ≤ t → HasDerivAt (fun t : ℝ => -genExpIntE 1 (z+t)) (exp (-(z+t))/(z+t)) t := by
    intro t ht
    refine (hasDerivAt_comp_add_ofReal (g := fun w => -genExpIntE 1 w)
      (hasDerivAt_genExpIntE 1 (add_ofReal_mem_slitPlane hz ht)).neg).congr_deriv ?_
    simp [genExpIntE_zero_eq]
  have hc : ContinuousOn (fun t : ℝ => exp (-(z+t))/(z+t)) (Ici 0) := by
    refine ContinuousOn.div (by fun_prop) (by fun_prop) fun t ht => slitPlane_ne_zero (add_ofReal_mem_slitPlane hz ht)
  have h := hasIntegralAtTop_of_hasDerivAt_of_tendsto hd hc (tendsto_expIntE1_add_ofReal z).neg
  simpa using h

/-- Horizontal-ray integral representation: `HasIntegralAtTop (fun t : ℝ => sin (z+t)/(z+t)) 0
(-sinIntTail z)`. -/
@[dlmf 6.2.E10]
theorem sinIntTail_horizontal_integral {z : ℂ} (hz : z ∈ slitPlane) :
    HasIntegralAtTop (fun t : ℝ => sin (z+t)/(z+t)) 0 (-sinIntTail z) := by
  have hd : ∀ t : ℝ, 0 ≤ t → HasDerivAt (fun t : ℝ => sinIntTail (z+t)) (sin (z+t)/(z+t)) t := fun t ht =>
    hasDerivAt_comp_add_ofReal (g := sinIntTail)
      ((hasDerivAt_sinInt_complex (slitPlane_ne_zero (add_ofReal_mem_slitPlane hz ht))).sub_const _)
  have hc : ContinuousOn (fun t : ℝ => sin (z+t)/(z+t)) (Ici 0) := by
    refine ContinuousOn.div (by fun_prop) (by fun_prop) fun t ht => slitPlane_ne_zero (add_ofReal_mem_slitPlane hz ht)
  have h := hasIntegralAtTop_of_hasDerivAt_of_tendsto hd hc (tendsto_sinIntTail_add_ofReal z)
  simpa using h

/-- Horizontal-ray integral representation: `HasIntegralAtTop (fun t : ℝ => cos (z+t)/(z+t)) 0
(-cosInt z)`. -/
@[dlmf 6.2.E11]
theorem cosInt_horizontal_integral {z : ℂ} (hz : z ∈ slitPlane) :
    HasIntegralAtTop (fun t : ℝ => cos (z+t)/(z+t)) 0 (-cosInt z) := by
  have hd : ∀ t : ℝ, 0 ≤ t → HasDerivAt (fun t : ℝ => cosInt (z+t)) (cos (z+t)/(z+t)) t := fun t ht =>
    hasDerivAt_comp_add_ofReal (g := cosInt) (hasDerivAt_cosInt_complex (add_ofReal_mem_slitPlane hz ht))
  have hc : ContinuousOn (fun t : ℝ => cos (z+t)/(z+t)) (Ici 0) := by
    refine ContinuousOn.div (by fun_prop) (by fun_prop) fun t ht => slitPlane_ne_zero (add_ofReal_mem_slitPlane hz ht)
  have h := hasIntegralAtTop_of_hasDerivAt_of_tendsto hd hc (tendsto_cosInt_add_ofReal z)
  simpa using h

/-- The map `(fun x : ℝ => cosInt x)` tends to `(𝓝 0)` along `atTop`. -/
@[dlmf 6.2.E14]
theorem cosInt_tendsto_atTop  :
    Tendsto (fun x : ℝ => cosInt x) atTop (𝓝 0) := by
  simpa using tendsto_cosInt_add_ofReal 0

end DLMF.Confluent
