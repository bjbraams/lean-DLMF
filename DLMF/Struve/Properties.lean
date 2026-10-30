/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Struve.SeriesAndEquations
public import DLMF.Struve.Poisson
public import DLMF.Bessel.NeumannSeries

/-!
# Struve half-integer orders, recurrences and Bessel expansions

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.

The proved calculus uses the regularized quadratic gauge from `Basic`; integral
orders extend across the origin by entire-function uniqueness. Half-integer
formulas reuse the proved Bessel derivative ladders and elementary values.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Struve

open DLMF.Bessel

/-- Identity under the stated parameter and domain assumptions: `struveH (-n-1/2) z =
(-1)^n*besselJ (n+1/2) z`. -/
@[dlmf 11.4.E3]
theorem struveH_neg_nat_sub_half (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    struveH (-n-1/2) z = (-1)^n*besselJ (n+1/2) z := by
  induction n generalizing z with
  | zero =>
    simp only [Nat.cast_zero,neg_zero,zero_sub,pow_zero,one_mul]
    rw [struveH,struveHCore_eq_regularized,besselJ_eq_regularized]
    norm_num only
    rw [regularized1F2_one_one]
    congr 2; ring
  | succ n ih =>
    have hd := hasDerivAt_struveQuadratic (-(n:ℂ)-1/2) (-1) hz
    rw [funext (struveQuadratic_H (-(n:ℂ)-1/2))] at hd
    simp only [struveQuadratic_H] at hd
    have hev : struveH (-(n:ℂ)-1/2)=ᶠ[𝓝 z] (fun w => (-1:ℂ)^n*besselJ (n+1/2) w) := by
      filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
      exact ih hw
    have he := hd.deriv
    rw [hev.deriv_eq,deriv_const_mul_field,(hasDerivAt_besselJ (ν:=(n:ℂ)+1/2) hz).deriv,ih hz] at he
    push_cast
    rw [show -((n:ℂ)+1)-1/2=(-(n:ℂ)-1/2)-1 by ring,
      show (n:ℂ)+1+1/2=(n:ℂ)+1/2+1 by ring]
    rw [pow_succ]
    linear_combination -he

/-- Identity under the stated parameter and domain assumptions: `struveL (-n-1/2) z = besselI
(n+1/2) z`. -/
@[dlmf 11.4.E4]
theorem struveL_neg_nat_sub_half (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    struveL (-n-1/2) z = besselI (n+1/2) z := by
  induction n generalizing z with
  | zero =>
    simp only [Nat.cast_zero,neg_zero,zero_sub,pow_zero,one_mul]
    rw [struveL,struveLCore_eq_regularized,besselI]
    norm_num only
    rw [regularized1F2_one_one]
  | succ n ih =>
    have hd := hasDerivAt_struveQuadratic (-(n:ℂ)-1/2) 1 hz
    rw [funext (struveQuadratic_L (-(n:ℂ)-1/2))] at hd
    simp only [struveQuadratic_L] at hd
    have hev : struveL (-(n:ℂ)-1/2)=ᶠ[𝓝 z] (fun w => besselI (n+1/2) w) := by
      filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
      exact ih hw
    have he := hd.deriv
    rw [hev.deriv_eq,(hasDerivAt_besselI (ν:=(n:ℂ)+1/2) hz).deriv,ih hz] at he
    push_cast
    rw [show -((n:ℂ)+1)-1/2=(-(n:ℂ)-1/2)-1 by ring,
      show (n:ℂ)+1+1/2=(n:ℂ)+1/2+1 by ring]
    linear_combination -he

/-- The reciprocal half-power forcing has the standard Bessel normalization. -/
theorem struve_half_prefactor {z : ℂ} (hz : z∈slitPlane) :
    (z/2)^(-(1/2):ℂ)/(Real.sqrt π:ℂ)=(2/(π*z))^(1/2:ℂ) := by
  have hp : (π:ℂ)^(1/2:ℂ)=(Real.sqrt π:ℂ) :=
    Complex.Gamma_one_half_eq.symm.trans DLMF.Confluent.Gamma_one_half_eq_sqrt
  rw [cpow_half_recip_div_two hz,cpow_half_two_div_pi_z hz,cpow_half_div_pi,hp]
  ring

/-- The other elementary half-power shares the inherited slit-plane branch. -/
theorem struve_positive_half_prefactor {z : ℂ} (hz : z∈slitPlane) :
    (z/(2*π))^(1/2:ℂ)=(z/2)^(1/2:ℂ)/(Real.sqrt π:ℂ) ∧
      (z/2)^(1/2:ℂ)/(Real.sqrt π:ℂ)=(2/(π*z))^(1/2:ℂ)*z/2 := by
  have hz0 := slitPlane_ne_zero hz
  have hp : (π:ℂ)^(1/2:ℂ)=(Real.sqrt π:ℂ) :=
    Complex.Gamma_one_half_eq.symm.trans DLMF.Confluent.Gamma_one_half_eq_sqrt
  constructor
  · rw [show z/(2*π)=(((π:ℝ)⁻¹:ℝ):ℂ)*(z/2) by push_cast; ring,
      DLMF.Confluent.ofReal_mul_cpow_of_pos (by positivity) (div_ne_zero hz0 (by norm_num)) (1/2:ℂ),
      Complex.ofReal_inv,inv_cpow_ofReal_nonneg Real.pi_pos.le,hp]
    ring
  · have he : (z/2)^(1/2:ℂ)=(z/2)^(-(1/2):ℂ)*(z/2) := by
      calc
        (z/2)^(1/2:ℂ)=(z/2)^(-(1/2)+1:ℂ) := by congr 1; ring
        _ = _ := by rw [cpow_add _ _ (div_ne_zero hz0 (by norm_num)),cpow_one]
    rw [he]
    linear_combination (z/2)*(struve_half_prefactor hz)

/-- Rotating the entire 0F1 series gives the modified half-integer Bessel values. -/
theorem besselI_elementary_halves {z : ℂ} (hz : z∈slitPlane) :
    besselI (1/2) z=(2/(π*z))^(1/2:ℂ)*sinh z ∧
      besselI (-(1/2)) z=(2/(π*z))^(1/2:ℂ)*cosh z := by
  have hz0 := slitPlane_ne_zero hz
  have hs := regularized0F1_three_halves_eq_sinc (mul_ne_zero I_ne_zero hz0 : I*z≠0)
  have hc := regularized0F1_half_eq_cos (z:=I*z)
  have ha : -((I*z)^2/4)=z^2/4 := by simp [mul_pow,I_sq]; ring
  have hsin : sin (I*z)=I*sinh z := by rw [mul_comm I,sin_mul_I]; ring
  have hcos : cos (I*z)=cosh z := by rw [mul_comm I,cos_mul_I]
  rw [ha,hsin] at hs
  rw [ha,hcos] at hc
  have hs' : regularizedHGFun ∅ {3/2} (z^2/4)=2*sinh z/(z*Gamma (1/2)) := by
    rw [hs]
    field_simp
  constructor
  · rw [besselI,show (1/2:ℂ)+1=3/2 by ring,hs',← bessel_half_prefactor hz]
    field_simp
  · rw [besselI,show -(1/2:ℂ)+1=1/2 by ring,hc,DLMF.Confluent.Gamma_one_half_eq_sqrt]
    linear_combination cosh z*(struve_half_prefactor hz)

/-- Identity under the stated parameter and domain assumptions: `struveH (-1/2) z =
(2/(π*z))^(1/2:ℂ)*sin z`. -/
@[dlmf 11.4.E6]
theorem struve_special_6 {z : ℂ} (hz : z ∈ slitPlane) :
    struveH (-1/2) z = (2/(π*z))^(1/2:ℂ)*sin z := by
  rw [show (-1:ℂ)/2= -(1/2) by ring]
  have h : struveH (-(1/2)) z=besselJ (1/2) z := by
    simpa only [Nat.cast_zero,neg_zero,zero_sub,pow_zero,one_mul,zero_add] using struveH_neg_nat_sub_half 0 hz
  exact h.trans (besselJ_half z hz)

/-- Identity under the stated parameter and domain assumptions: `struveH (-3/2) z =
(2/(π*z))^(1/2:ℂ)*(cos z-sin z/z)`. -/
@[dlmf 11.4.E10]
theorem struve_special_10 {z : ℂ} (hz : z ∈ slitPlane) :
    struveH (-3/2) z = (2/(π*z))^(1/2:ℂ)*(cos z-sin z/z) := by
  have hs := struveH_neg_nat_sub_half 1 hz
  have hr := besselJ_add_sub (ν:=(1/2:ℂ)) (slitPlane_ne_zero hz)
  norm_num only [Nat.cast_one,pow_one] at hs
  rw [show (-3:ℂ)/2= -(3/2) by ring,hs]
  rw [show (1/2:ℂ)-1= -(1/2) by ring,show (1/2:ℂ)+1=3/2 by ring,
    besselJ_half z hz,besselJ_neg_half z hz] at hr
  linear_combination hr

/-- Identity under the stated parameter and domain assumptions: `struveH (1/2) z =
(2/(π*z))^(1/2:ℂ)*(1-cos z)`. -/
@[dlmf 11.4.E5]
theorem struve_special_5 {z : ℂ} (hz : z ∈ slitPlane) :
    struveH (1/2) z = (2/(π*z))^(1/2:ℂ)*(1-cos z) := by
  have hr := struveQuadratic_recurrence (-(1/2)) (-1) hz
  simp only [struveQuadratic_H,neg_one_mul,sub_neg_eq_add,one_mul] at hr
  rw [show -(1/2:ℂ)-1= -3/2 by ring,show -(1/2:ℂ)+1=1/2 by ring,
    show -(1/2:ℂ)+3/2=1 by ring,Gamma_one,mul_one,
    show -(1/2:ℂ)=(-1:ℂ)/2 by ring,struve_special_10 hz,struve_special_6 hz] at hr
  rw [show (-1:ℂ)/2= -(1/2) by ring,struve_half_prefactor hz] at hr
  linear_combination (norm := (field_simp [slitPlane_ne_zero hz]; ring)) hr

/-- Identity under the stated parameter and domain assumptions: `struveL (-1/2) z =
(2/(π*z))^(1/2:ℂ)*sinh z`. -/
@[dlmf 11.4.E8]
theorem struve_special_8 {z : ℂ} (hz : z ∈ slitPlane) :
    struveL (-1/2) z = (2/(π*z))^(1/2:ℂ)*sinh z := by
  have he : struveL (-(1/2)) z=besselI (1/2) z := by
    simpa only [Nat.cast_zero,neg_zero,zero_sub,zero_add] using struveL_neg_nat_sub_half 0 hz
  rw [show (-1:ℂ)/2= -(1/2) by ring]
  exact he.trans (besselI_elementary_halves hz).1

/-- Identity under the stated parameter and domain assumptions: `struveL (-3/2) z =
(2/(π*z))^(1/2:ℂ)*(cosh z-sinh z/z)`. -/
@[dlmf 11.4.E12]
theorem struve_special_12 {z : ℂ} (hz : z ∈ slitPlane) :
    struveL (-3/2) z = (2/(π*z))^(1/2:ℂ)*(cosh z-sinh z/z) := by
  have hs := struveL_neg_nat_sub_half 1 hz
  have hr := besselI_sub_add (ν:=(1/2:ℂ)) (slitPlane_ne_zero hz)
  norm_num only [Nat.cast_one] at hs
  rw [show (-3:ℂ)/2= -(3/2) by ring,hs]
  rw [show (1/2:ℂ)-1= -(1/2) by ring,show (1/2:ℂ)+1=3/2 by ring,
    (besselI_elementary_halves hz).1,(besselI_elementary_halves hz).2] at hr
  linear_combination hr

/-- Identity under the stated parameter and domain assumptions: `struveL (1/2) z =
(2/(π*z))^(1/2:ℂ)*(cosh z-1)`. -/
@[dlmf 11.4.E7]
theorem struve_special_7 {z : ℂ} (hz : z ∈ slitPlane) :
    struveL (1/2) z = (2/(π*z))^(1/2:ℂ)*(cosh z-1) := by
  have hr := struveQuadratic_recurrence (-(1/2)) 1 hz
  simp only [struveQuadratic_L,neg_one_mul,sub_neg_eq_add,one_mul] at hr
  rw [show -(1/2:ℂ)-1= -3/2 by ring,show -(1/2:ℂ)+1=1/2 by ring,
    show -(1/2:ℂ)+3/2=1 by ring,Gamma_one,mul_one,
    show -(1/2:ℂ)=(-1:ℂ)/2 by ring,struve_special_12 hz,struve_special_8 hz] at hr
  rw [show (-1:ℂ)/2= -(1/2) by ring,struve_half_prefactor hz] at hr
  linear_combination (norm := (field_simp [slitPlane_ne_zero hz]; ring)) -hr

/-- Identity under the stated parameter and domain assumptions: `struveH (3/2) z =
(z/(2*π))^(1/2:ℂ)*(1+2/z^2)-(2/(π*z))^(1/2:ℂ)*(sin z+cos z/z)`. -/
@[dlmf 11.4.E9]
theorem struve_special_9 {z : ℂ} (hz : z ∈ slitPlane) :
    struveH (3/2) z = (z/(2*π))^(1/2:ℂ)*(1+2/z^2)-(2/(π*z))^(1/2:ℂ)*(sin z+cos z/z) := by
  have hr := struveQuadratic_recurrence (1/2) (-1) hz
  simp only [struveQuadratic_H,neg_one_mul,sub_neg_eq_add,one_mul] at hr
  rw [show (1/2:ℂ)-1= -1/2 by ring,show (1/2:ℂ)+1=3/2 by ring,
    show (1/2:ℂ)+3/2=2 by ring,show Gamma (2:ℂ)=1 by simpa using Gamma_nat_eq_factorial 1,
    mul_one,struve_special_6 hz,struve_special_5 hz] at hr
  rw [(struve_positive_half_prefactor hz).1,(struve_positive_half_prefactor hz).2]
  rw [(struve_positive_half_prefactor hz).2] at hr
  linear_combination (norm := (field_simp [slitPlane_ne_zero hz]; ring)) hr

/-- Identity under the stated parameter and domain assumptions: `struveL (3/2) z =
-(z/(2*π))^(1/2:ℂ)*(1-2/z^2)+(2/(π*z))^(1/2:ℂ)*(sinh z-cosh z/z)`. -/
@[dlmf 11.4.E11]
theorem struve_special_11 {z : ℂ} (hz : z ∈ slitPlane) :
    struveL (3/2) z = -(z/(2*π))^(1/2:ℂ)*(1-2/z^2)+(2/(π*z))^(1/2:ℂ)*(sinh z-cosh z/z) := by
  have hr := struveQuadratic_recurrence (1/2) 1 hz
  simp only [struveQuadratic_L,neg_one_mul,sub_neg_eq_add,one_mul] at hr
  rw [show (1/2:ℂ)-1= -1/2 by ring,show (1/2:ℂ)+1=3/2 by ring,
    show (1/2:ℂ)+3/2=2 by ring,show Gamma (2:ℂ)=1 by simpa using Gamma_nat_eq_factorial 1,
    mul_one,struve_special_8 hz,struve_special_7 hz] at hr
  rw [(struve_positive_half_prefactor hz).1,(struve_positive_half_prefactor hz).2]
  rw [(struve_positive_half_prefactor hz).2] at hr
  linear_combination (norm := (field_simp [slitPlane_ne_zero hz]; ring)) -hr

/-- Factorial coefficient of a half-integer Struve Laurent polynomial. -/
def struveHalfCoeff (n m : ℕ) : ℂ :=
  ((2*m).factorial:ℂ)*2^(-(2*m:ℤ))/((m.factorial:ℂ)*(n-m).factorial)

/-- The signed finite Laurent polynomial occurring at positive half-integer orders. -/
def struveHalfPoly (σ : ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  ∑ m∈Finset.range (n+1), σ^m*struveHalfCoeff n m*(z/2)^((n:ℤ)-2*m)

/-- Shifting the summation index multiplies its coefficient by the next odd factor. -/
theorem struveHalfCoeff_succ (n m : ℕ) :
    struveHalfCoeff (n+1) (m+1)=struveHalfCoeff n m*(2*m+1)/2 := by
  unfold struveHalfCoeff
  rw [show 2*(m+1)=(2*m+1)+1 by omega,Nat.factorial_succ,Nat.factorial_succ,Nat.factorial_succ,
    Nat.add_sub_add_right]
  push_cast
  rw [show -(2*((m:ℤ)+1))= -(2*m)-2 by ring,zpow_sub₀ (by norm_num)]
  norm_num only [zpow_ofNat]
  field_simp
  ring

/-- The finite polynomial ladder includes its new leading monomial. -/
theorem struveHalfPoly_succ (σ : ℂ) (n : ℕ) {z : ℂ} (hz : z≠0) :
    struveHalfPoly σ (n+1) z=(z/2)^(n+1)/(n+1).factorial+
      σ/z*∑ m∈Finset.range (n+1), (2*m+1)*σ^m*struveHalfCoeff n m*(z/2)^((n:ℤ)-2*m) := by
  rw [struveHalfPoly,Finset.sum_range_succ']
  simp only [pow_zero,struveHalfCoeff,Nat.mul_zero,Nat.factorial_zero,Int.natCast_zero,
    mul_zero,neg_zero,zpow_zero,one_mul,mul_one,Nat.sub_zero,sub_zero,zpow_natCast]
  rw [add_comm]
  congr 1
  · norm_num
    ring
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    change σ^(m+1)*struveHalfCoeff (n+1) (m+1)*(z/2)^(((n+1:ℕ):ℤ)-2*(m+1))=_
    rw [struveHalfCoeff_succ,pow_succ]
    have he : ((n+1:ℕ):ℤ)-2*(m+1)=(n:ℤ)-2*m-1 := by push_cast; ring
    rw [he,zpow_sub₀ (div_ne_zero hz (by norm_num)),zpow_one]
    unfold struveHalfCoeff
    field_simp
/-- Differentiating the Laurent polynomial multiplies each monomial by its integer exponent. -/
theorem hasDerivAt_struveHalfPoly (σ : ℂ) (n : ℕ) {z : ℂ} (hz : z≠0) :
    HasDerivAt (struveHalfPoly σ n)
      (∑ m∈Finset.range (n+1), ((n:ℂ)-2*m)/z*σ^m*struveHalfCoeff n m*(z/2)^((n:ℤ)-2*m)) z := by
  apply HasDerivAt.fun_sum
  intro m hm
  have hd := ((hasDerivAt_zpow ((n:ℤ)-2*m) (z/2) (Or.inl (div_ne_zero hz (by norm_num)))).comp z
    ((hasDerivAt_id z).div_const 2)).const_mul (σ^m*struveHalfCoeff n m)
  have hd' : HasDerivAt (fun w=>σ^m*struveHalfCoeff n m*(w/2)^((n:ℤ)-2*m)) _ z :=
    hd.congr_of_eventuallyEq (Eventually.of_forall fun w=>rfl)
  refine hd'.congr_deriv ?_
  rw [zpow_sub₀ (div_ne_zero hz (by norm_num)),zpow_one]
  push_cast
  field_simp

/-- The elementary half-power times the Laurent polynomial obeys the signed order ladder. -/
theorem hasDerivAt_struveHalf_finite (σ : ℂ) (hσ : σ^2=1) (n : ℕ) {z : ℂ} (hz : z∈slitPlane) :
    HasDerivAt (fun w=>(2/(π*w))^(1/2:ℂ)*struveHalfPoly σ n w)
      (((n:ℂ)+1/2)/z*((2/(π*z))^(1/2:ℂ)*struveHalfPoly σ n z)-
        σ*((2/(π*z))^(1/2:ℂ)*struveHalfPoly σ (n+1) z)+
        σ*(2/(π*z))^(1/2:ℂ)*(z/2)^(n+1)/(n+1).factorial) z := by
  have hp := (hasDerivAt_besselPrefactor (-(1/2):ℂ) hz).div_const (Real.sqrt π:ℂ)
  have hev : (fun w=>(w/2)^(-(1/2):ℂ)/(Real.sqrt π:ℂ))=ᶠ[𝓝 z]
      (fun w=>(2/(π*w))^(1/2:ℂ)) := by
    filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
    exact struve_half_prefactor hw
  have hp' := hp.congr_of_eventuallyEq hev.symm
  have hd := hp'.mul (hasDerivAt_struveHalfPoly σ n (slitPlane_ne_zero hz))
  have hd' : HasDerivAt (fun w=>(2/(π*w))^(1/2:ℂ)*struveHalfPoly σ n w) _ z :=
    hd.congr_of_eventuallyEq (Eventually.of_forall fun w=>rfl)
  have hsum : (2/(π*z))^(1/2:ℂ)*(-(1/2)/z)*struveHalfPoly σ n z+
      (2/(π*z))^(1/2:ℂ)*(∑ m∈Finset.range (n+1),
        ((n:ℂ)-2*m)/z*σ^m*struveHalfCoeff n m*(z/2)^((n:ℤ)-2*m))=
      ((n:ℂ)+1/2)/z*((2/(π*z))^(1/2:ℂ)*struveHalfPoly σ n z)-
        (2/(π*z))^(1/2:ℂ)/z*(∑ m∈Finset.range (n+1),
          (2*m+1)*σ^m*struveHalfCoeff n m*(z/2)^((n:ℤ)-2*m)) := by
    rw [struveHalfPoly]
    simp only [Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    ring
  refine hd'.congr_deriv ?_
  rw [show (z/2)^(-(1/2):ℂ)*(-(1/2)/z)/(Real.sqrt π:ℂ)=
      ((z/2)^(-(1/2):ℂ)/(Real.sqrt π:ℂ))*(-(1/2)/z) by ring,struve_half_prefactor hz,
    hsum,struveHalfPoly_succ σ n (slitPlane_ne_zero hz)]
  ring_nf
  rw [hσ]
  ring

/-- The Struve forcing at a positive half-integer order is the leading finite monomial. -/
theorem struveHalf_forcing (n : ℕ) {z : ℂ} (hz : z∈slitPlane) :
    (z/2)^((n:ℂ)+1/2)/((Real.sqrt π:ℂ)*Gamma ((n:ℂ)+1/2+3/2))=
      (2/(π*z))^(1/2:ℂ)*(z/2)^(n+1)/(n+1).factorial := by
  rw [show (n:ℂ)+1/2+3/2=((n+1:ℕ):ℂ)+1 by push_cast; ring,Gamma_nat_eq_factorial]
  rw [← struve_half_prefactor hz]
  have he : (z/2)^((n:ℂ)+1/2)=(z/2)^(-(1/2):ℂ)*(z/2)^(n+1) := by
    rw [← cpow_natCast,← cpow_add _ _ (div_ne_zero (slitPlane_ne_zero hz) (by norm_num))]
    congr 1
    push_cast
    ring
  rw [he]
  ring

/-- The Struve derivative in raising-order form, with its forcing term. -/
theorem hasDerivAt_struve_raise (ν σ : ℂ) {z : ℂ} (hz : z∈slitPlane) :
    HasDerivAt (struveQuadratic ν σ)
      (ν/z*struveQuadratic ν σ z+σ*struveQuadratic (ν+1) σ z+
        (z/2)^ν/(Real.sqrt π*Gamma (ν+3/2))) z := by
  refine (hasDerivAt_struveQuadratic ν σ hz).congr_deriv ?_
  linear_combination struveQuadratic_recurrence ν σ hz

/-- Formula under the stated hypotheses: `struveK (n+1/2) z = (2/(π*z))^(1/2:ℂ) * ∑ m ∈
Finset.range (n+1), ((2*m).factorial :
ℂ)*2^(-(2*m:ℤ))/((m.factorial:ℂ)*(n-m).factorial)*(z/2)^((n:ℤ)-2*m)`. -/
@[dlmf 11.4.E1]
theorem struveK_nat_add_half (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    struveK (n+1/2) z = (2/(π*z))^(1/2:ℂ) * ∑ m ∈ Finset.range (n+1), ((2*m).factorial : ℂ)*2^(-(2*m:ℤ))/((m.factorial:ℂ)*(n-m).factorial)*(z/2)^((n:ℤ)-2*m) := by
  suffices h : struveK (n+1/2) z=(2/(π*z))^(1/2:ℂ)*struveHalfPoly 1 n z by
    simpa only [struveHalfPoly,struveHalfCoeff,one_pow,one_mul,mul_div_assoc,mul_assoc] using h
  induction n generalizing z with
  | zero =>
    simp only [Nat.cast_zero,zero_add,struveHalfPoly,Finset.sum_range_one,struveHalfCoeff,
      pow_zero,zpow_zero,Nat.factorial_zero,Int.natCast_zero,Nat.mul_zero,mul_zero,neg_zero,
      Nat.sub_zero,div_one,mul_one,one_mul,sub_zero]
    rw [struveK,struve_special_5 hz,besselY_half hz]
    ring
  | succ n ih =>
    have hdH := hasDerivAt_struve_raise ((n:ℂ)+1/2) (-1) hz
    rw [funext (struveQuadratic_H ((n:ℂ)+1/2))] at hdH
    simp only [struveQuadratic_H] at hdH
    have hd := hdH.sub (hasDerivAt_besselY ((n:ℂ)+1/2) hz)
    have hd' : HasDerivAt (struveK ((n:ℂ)+1/2)) _ z := hd
    have hev : struveK ((n:ℂ)+1/2)=ᶠ[𝓝 z]
        (fun w=>(2/(π*w))^(1/2:ℂ)*struveHalfPoly 1 n w) := by
      filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
      exact ih hw
    have he := hd'.deriv
    rw [hev.deriv_eq,(hasDerivAt_struveHalf_finite 1 (by norm_num) n hz).deriv,
      struveHalf_forcing n hz] at he
    simp only [struveK] at ih ⊢
    have hi := ih hz
    push_cast
    rw [show (n:ℂ)+1+1/2=(n:ℂ)+1/2+1 by ring]
    linear_combination he+((n:ℂ)+1/2)/z*hi

/-- Formula under the stated hypotheses: `struveL (n+1/2) z = besselI (-n-1/2) z -
(2/(π*z))^(1/2:ℂ) * ∑ m ∈ Finset.range (n+1), (-1)^m*((2*m).factorial :
ℂ)*2^(-(2*m:ℤ))/((m.factorial:ℂ)*(n-m).factorial)*(z/2)^((n:ℤ)-2*m)`. -/
@[dlmf 11.4.E2]
theorem struveL_nat_add_half (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    struveL (n+1/2) z = besselI (-n-1/2) z - (2/(π*z))^(1/2:ℂ) * ∑ m ∈ Finset.range (n+1), (-1)^m*((2*m).factorial : ℂ)*2^(-(2*m:ℤ))/((m.factorial:ℂ)*(n-m).factorial)*(z/2)^((n:ℤ)-2*m) := by
  suffices h : struveL (n+1/2) z=besselI (-n-1/2) z-(2/(π*z))^(1/2:ℂ)*struveHalfPoly (-1) n z by
    simpa only [struveHalfPoly,struveHalfCoeff,mul_div_assoc,mul_assoc] using h
  induction n generalizing z with
  | zero =>
    simp only [Nat.cast_zero,zero_add,neg_zero,zero_sub,struveHalfPoly,Finset.sum_range_one,struveHalfCoeff,
      pow_zero,zpow_zero,Nat.factorial_zero,Int.natCast_zero,Nat.mul_zero,mul_zero,
      Nat.sub_zero,div_one,mul_one,one_mul,sub_zero]
    rw [struve_special_7 hz,(besselI_elementary_halves hz).2]
    ring
  | succ n ih =>
    have hdL := hasDerivAt_struve_raise ((n:ℂ)+1/2) 1 hz
    rw [funext (struveQuadratic_L ((n:ℂ)+1/2))] at hdL
    simp only [struveQuadratic_L] at hdL
    have hd := (hasDerivAt_besselI' (ν:= -(n:ℂ)-1/2) hz).sub hdL
    have hev : (fun w=>besselI (-(n:ℂ)-1/2) w-struveL ((n:ℂ)+1/2) w)=ᶠ[𝓝 z]
        (fun w=>(2/(π*w))^(1/2:ℂ)*struveHalfPoly (-1) n w) := by
      filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
      linear_combination -ih hw
    have hd' : HasDerivAt (fun w=>besselI (-(n:ℂ)-1/2) w-struveL ((n:ℂ)+1/2) w) _ z := hd
    have he := hd'.deriv
    rw [hev.deriv_eq,(hasDerivAt_struveHalf_finite (-1) (by norm_num) n hz).deriv,
      struveHalf_forcing n hz] at he
    have hi := ih hz
    push_cast
    rw [show (n:ℂ)+1+1/2=(n:ℂ)+1/2+1 by ring,
      show -((n:ℂ)+1)-1/2=(-(n:ℂ)-1/2)-1 by ring]
    linear_combination he-((n:ℂ)+1/2)/z*hi

/-- For `p ≥ 0` and `x > 0`, `∫₀¹ (1-t²)^p sin(xt) dt ≥ 0` (one integration by parts). -/
theorem integral_rpow_mul_sin_nonneg {p x : ℝ} (hp : 0 ≤ p) (hx : 0 < x) :
    0 ≤ ∫ t : ℝ in 0..1, (1-t^2)^p * Real.sin (x*t) := by
  set u : ℝ → ℝ := fun t => (1-t^2)^p
  set u' : ℝ → ℝ := fun t => (-(2*t)) * p * (1-t^2)^(p-1)
  set v : ℝ → ℝ := fun t => (1 - Real.cos (x*t))/x
  have hu : ContinuousOn u (uIcc 0 1) :=
    ((continuous_const.sub (continuous_pow 2)).rpow_const (fun _ => Or.inr hp)).continuousOn
  have hv : ContinuousOn v (uIcc 0 1) := by fun_prop
  have huu' : ∀ t ∈ Ioo (min 0 1) (max 0 1), HasDerivAt u (u' t) t := by
    intro t ht
    simp only [zero_le_one, min_eq_left, max_eq_right] at ht
    have hb : (1:ℝ)-t^2 ≠ 0 := by nlinarith [ht.1, ht.2]
    have := ((hasDerivAt_pow 2 t).const_sub 1).rpow_const (p := p) (Or.inl hb)
    convert this using 1
    simp only [u']; push_cast; ring
  have hvv' : ∀ t ∈ Ioo (min 0 1) (max 0 1), HasDerivAt v (Real.sin (x*t)) t := by
    intro t _
    have := (((Real.hasDerivAt_cos (x*t)).comp t ((hasDerivAt_id t).const_mul x)).const_sub 1
      ).div_const x
    convert this using 1
    · funext s; simp [v]
    · field_simp
  have hu' : IntervalIntegrable u' volume 0 1 := by
    have h := intervalIntegral.intervalIntegrable_deriv_of_nonneg (g := fun t => -u t)
      (g' := fun t => -u' t) hu.neg (fun t ht => (huu' t ht).neg) (fun t ht => by
        simp only [zero_le_one, min_eq_left, max_eq_right] at ht
        simp only [u']
        have : 0 ≤ (1-t^2)^(p-1) := Real.rpow_nonneg (by nlinarith [ht.1, ht.2]) _
        have := mul_nonneg (mul_nonneg (by linarith [ht.1] : (0:ℝ) ≤ 2*t) hp) this
        linarith)
    have := h.neg
    refine this.congr (fun t _ => ?_)
    simp
  have hv' : IntervalIntegrable (fun t => Real.sin (x*t)) volume 0 1 :=
    (by fun_prop : Continuous fun t : ℝ => Real.sin (x*t)).intervalIntegrable _ _
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt hu hv huu' hvv'
    hu' hv'
  change 0 ≤ ∫ t : ℝ in 0..1, u t * Real.sin (x*t)
  rw [hibp]
  have h1 : 0 ≤ u 1 * v 1 := mul_nonneg (Real.rpow_nonneg (by norm_num) _)
    (div_nonneg (by linarith [Real.cos_le_one (x*1)]) hx.le)
  have h0 : u 0 * v 0 = 0 := by simp [v]
  have h2 : (∫ t : ℝ in 0..1, u' t * v t) ≤ 0 := by
    rw [← neg_nonneg, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_nonneg zero_le_one fun t ht => ?_
    simp only [u', v]
    have : 0 ≤ (1-t^2)^(p-1) := Real.rpow_nonneg (by nlinarith [ht.1, ht.2]) _
    have hc : 0 ≤ (1 - Real.cos (x*t))/x := div_nonneg (by linarith [Real.cos_le_one (x*t)]) hx.le
    have := mul_nonneg (mul_nonneg (mul_nonneg (by linarith [ht.1] : (0:ℝ) ≤ 2*t) hp) this) hc
    linarith
  linarith

/-- struveH nonneg, from Poisson's integral and one integration by parts. -/
@[dlmf 11.4.E13]
theorem struveH_nonneg {ν x : ℝ} (hν : 1/2 ≤ ν) (hx : 0 < x) :
    0 ≤ (struveH ν x).re ∧ (struveH ν x).im = 0 := by
  have hν' : -1/2 < (ν:ℂ).re := by simp; linarith
  have hP := struveH_eq_poisson hν' (z := x) (ofReal_ne_zero.2 hx.ne')
  have hint : (∫ t : ℝ in 0..1, (1-(t:ℂ)^2)^((ν:ℂ)-1/2)*sin ((x:ℂ)*t)) =
      ((∫ t : ℝ in 0..1, (1-t^2)^(ν-1/2) * Real.sin (x*t) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le zero_le_one] at ht
    rw [ofReal_mul, ofReal_cpow (by nlinarith [ht.1, ht.2])]
    push_cast; ring_nf
  have hpre : 2*((x:ℂ)/2)^(ν:ℂ)/(Real.sqrt π*Gamma ((ν:ℂ)+1/2)) =
      ((2*(x/2)^ν/(Real.sqrt π*Real.Gamma (ν+1/2)) : ℝ) : ℂ) := by
    rw [show ((x:ℂ)/2) = ((x/2:ℝ):ℂ) by push_cast; ring, ← ofReal_cpow (by positivity),
      show (ν:ℂ)+1/2 = ((ν+1/2:ℝ):ℂ) by push_cast; ring, Complex.Gamma_ofReal]
    push_cast; ring
  rw [hint, hpre, ← ofReal_mul] at hP
  rw [hP, ofReal_re, ofReal_im]
  refine ⟨mul_nonneg (div_nonneg (by positivity) (mul_nonneg (Real.sqrt_nonneg _)
    (Real.Gamma_pos_of_pos (by linarith)).le)) ?_, rfl⟩
  exact integral_rpow_mul_sin_nonneg (by linarith) hx

/-- Relative-error bound, with minimum distance to reciprocal-gamma zeros explicit.
DLMF 11.4.15 prints `2/3 * exp(|z|^2/(4|ν₀+3/2|) - 1)`, which is false: at `ν = 1000`,
`z = i*y` with `y^2/4 = |ν+3/2|` the error exceeds `0.93 > 2/3`. The bound proved by the
termwise estimate `(3/2)_n ≥ (3/2) n!` is `2/3 * (exp(|z|^2/(4|ν₀+3/2|)) - 1)`, stated here
(corrected 2026-10-20). -/
@[dlmf 11.4.E14, dlmf 11.4.E15]
theorem struveH_relative_bound {ν z : ℂ} (hν : ∀ n : ℕ, ν+3/2 ≠ -n) (hz : z ≠ 0) (d : ℝ) (hd : 0 < d) (hmin : ∀ n : ℕ, d ≤ ‖ν+3/2+n‖) (hatt : ∃ n : ℕ, d = ‖ν+3/2+n‖) :
    ∃ θ : ℂ, struveH ν z = 2*(z/2)^(ν+1)/(Real.sqrt π*Gamma (ν+3/2))*(1+θ) ∧ ‖θ‖ < 2/3*(Real.exp (‖z‖^2/(4*d))-1) := by
  sorry

/-- struveH bessel series 18. The hypothesis `hν'` excludes `ν + 1/2 ∈ -ℕ`, where DLMF's
term with `2k+2ν+1 = 0` is a removable quotient but the totalized Lean term is `0`
(added 2026-10-20; at `ν = -1/2` the unrestricted statement claims `H_{-1/2} = 0`). -/
@[dlmf 11.4.E18]
theorem struveH_bessel_series_18 (ν : ℂ) (hν : ∀ n : ℕ, ν ≠ -(n+1))
    (hν' : ∀ n : ℕ, ν + 1/2 ≠ -n) {z : ℂ} (hz : z ∈ slitPlane) :
    HasSum (fun k : ℕ => (4/(Real.sqrt π*Gamma (ν+1/2))) * ((2*k+ν+1)*Gamma (k+ν+1)/((k.factorial:ℂ)*(2*k+1)*(2*k+2*ν+1))*besselJ (2*k+ν+1) z)) (struveH ν z) := by
  have hz0 := slitPlane_ne_zero hz
  have hl : ∀ n : ℕ, ν + 1 ≠ -n := fun n h => hν n (by linear_combination h)
  have hx : ∀ i : ℕ, (1 / 2 : ℂ) + i ≠ 0 := fun i h => by
    have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg i : (0:ℝ) ≤ i)]
  have hy : ∀ i : ℕ, (ν + 1 / 2 : ℂ) + i ≠ 0 := fun i h => hν' i (by linear_combination h)
  have ha : ∀ n : ℕ, (n : ℂ) + 1 / 2 ≠ 0 := fun n => by rw [add_comm]; exact hx n
  have hb : ∀ n : ℕ, (n : ℂ) + (ν + 1 / 2) ≠ 0 := fun n => by rw [add_comm]; exact hy n
  have hπ : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hG0 : Gamma (ν + 1 / 2) ≠ 0 :=
    Complex.Gamma_ne_zero fun m h => hν' m (by linear_combination h)
  have hhalf : Gamma (1 / 2) = (Real.sqrt π : ℂ) := by
    rw [Gamma_one_half_eq, show ((1 / 2 : ℂ)) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_cpow Real.pi_pos.le, ← Real.sqrt_eq_rpow]
  have h := (hasSum_besselJ_neumann_lommel (l := ν + 1) (a := 1 / 2) (b := ν + 1 / 2)
    (by ring) hl ha hb hz0).mul_left (1 / ((Real.sqrt π : ℂ) * Gamma (ν + 1 / 2)))
  convert h using 1
  · funext k
    have h1 := ha k
    have h2 := hb k
    have h3 : (2 * k + 1 : ℂ) ≠ 0 := by
      intro h; apply h1; linear_combination h / 2
    have h4 : (2 * k + 2 * ν + 1 : ℂ) ≠ 0 := by
      intro h; apply h2; linear_combination h / 2
    have hf : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    rw [powerNeumannCoeff, show (2 * k + ν + 1 : ℂ) = ν + 1 + 2 * k by ring,
      show (k + ν + 1 : ℂ) = ν + 1 + k by ring]
    field_simp
    ring
  · rw [struveH, struveHCore, mul_left_comm, ← tsum_mul_left (α := ℂ)
      (a := 1 / ((Real.sqrt π : ℂ) * Gamma (ν + 1 / 2)))]
    congr 1
    refine tsum_congr fun j => ?_
    have hP := Gamma_add_nat_succ_eq_prod hx j
    have hQ := Gamma_add_nat_succ_eq_prod hy j
    rw [struveCoeff, show (j : ℂ) + 3 / 2 = 1 / 2 + j + 1 by ring, hP,
      show (j : ℂ) + ν + 3 / 2 = ν + 1 / 2 + j + 1 by ring, hQ, hhalf, Finset.prod_mul_distrib, pow_mul]
    have hp1 : ∏ i ∈ Finset.range (j + 1), ((i : ℂ) + 1 / 2) = ∏ i ∈ Finset.range (j + 1), (1 / 2 + (i : ℂ)) :=
      Finset.prod_congr rfl fun i _ => add_comm _ _
    have hp2 : ∏ i ∈ Finset.range (j + 1), ((i : ℂ) + (ν + 1 / 2)) =
        ∏ i ∈ Finset.range (j + 1), (ν + 1 / 2 + (i : ℂ)) := Finset.prod_congr rfl fun i _ => add_comm _ _
    have hq1 : ∏ i ∈ Finset.range (j + 1), (1 / 2 + (i : ℂ)) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hx i
    have hq2 : ∏ i ∈ Finset.range (j + 1), (ν + 1 / 2 + (i : ℂ)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ => hy i
    rw [hp1, hp2]
    field_simp

/-- The series with terms `(fun k : ℕ => (z/(2*π))^(1/2:ℂ) *
((z/2)^k/((k.factorial:ℂ)*(k+1/2))*besselJ (k+ν+1/2) z))` converges to `(struveH ν z)`. -/
@[dlmf 11.4.E19]
theorem struveH_bessel_series_19 (ν : ℂ)  {z : ℂ} (hz : z ∈ slitPlane) :
    HasSum (fun k : ℕ => (z/(2*π))^(1/2:ℂ) * ((z/2)^k/((k.factorial:ℂ)*(k+1/2))*besselJ (k+ν+1/2) z)) (struveH ν z) := by
  have hz0 := slitPlane_ne_zero hz
  have hw0 : z / 2 ≠ 0 := div_ne_zero hz0 two_ne_zero
  set a : ℕ → ℂ := fun k => 1 / ((k ! : ℂ) * (k + 1 / 2)) with ha_def
  obtain ⟨B, hB0, hB⟩ := exists_norm_recip_nat_add_le (1 / 2 : ℂ)
  have ha : ∀ k, ‖a k‖ ≤ B * 1 ^ k := fun k => by
    have hf : (1 : ℝ) ≤ k ! := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero k)
    show ‖1 / ((k ! : ℂ) * (k + 1 / 2))‖ ≤ B * 1 ^ k
    rw [one_pow, mul_one, one_div, mul_inv, norm_mul, norm_inv, Complex.norm_natCast]
    calc (k ! : ℝ)⁻¹ * ‖((k : ℂ) + 1 / 2)⁻¹‖ ≤ 1 * B := by
          gcongr
          · exact inv_le_one_of_one_le₀ hf
          · exact hB k
      _ = B := one_mul B
  have hx : ∀ i : ℕ, (1 / 2 : ℂ) + i ≠ 0 := fun i h => by
    have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg i : (0:ℝ) ≤ i)]
  have hcoeff : ∀ j, neumannCoeff (ν + 1 / 2) (-1) a (fun k => k) j =
      (-1) ^ j / (Gamma (ν + 1 / 2 + j + 1) * ∏ i ∈ Finset.range (j + 1), (1 / 2 + (i : ℂ))) := by
    intro j
    rw [div_mul_eq_div_div_swap, ← sum_antidiagonal_neg_one_pow_div_add j hx, Finset.sum_div]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_antidiagonal] at hp
    rw [regularizedHGFunCoeff_empty, ha_def]
    have hj : (j : ℂ) = p.1 + p.2 := by exact_mod_cast hp.symm
    rw [hj, show ν + 1 / 2 + ((p.1 : ℕ) : ℂ) + 1 + ((p.2 : ℕ) : ℂ) = ν + 1 / 2 + (p.1 + p.2) + 1 by
      ring]
    simp only [div_eq_mul_inv, one_mul, mul_inv]
    ring
  have h := hasSum_besselJ_neumann_of_coeff hz0 (ν + 1 / 2) a (fun k => k) (fun k => k)
    (fun k => by ring)
    (summable_neumann_of_norm_le zero_le_one ha _ (fun k => ⟨le_rfl, by omega⟩) _) _ hcoeff
  have h2 := h.mul_left ((z / (2 * π)) ^ (1 / 2 : ℂ))
  convert h2 using 1
  · funext k
    simp only [ha_def]
    rw [show (k : ℂ) + ν + 1 / 2 = ν + 1 / 2 + k by ring]
    ring
  · have hπ : (0 : ℝ) < π := Real.pi_pos
    have hkey : (z / (2 * π)) ^ (1 / 2 : ℂ) * (z / 2) ^ (ν + 1 / 2) =
        (z / 2) ^ (ν + 1) / Gamma (1 / 2) := by
      rw [Complex.Gamma_one_half_eq, show z / (2 * π) = (z / 2) / (π : ℂ) by ring,
        div_ofReal_cpow hπ hw0, div_mul_eq_mul_div, ← cpow_add _ _ hw0]
      ring_nf
    rw [← mul_assoc, hkey, struveH, struveHCore,
      show ∀ X Y : ℂ, X / Gamma (1 / 2) * Y = X * ((Gamma (1 / 2))⁻¹ * Y) from fun X Y => by ring,
      ← tsum_mul_left (α := ℂ) (a := (Gamma (1 / 2))⁻¹)]
    congr 1
    refine tsum_congr fun j => ?_
    have hG := Gamma_add_nat_succ_eq_prod hx j
    rw [struveCoeff, show (j : ℂ) + 3 / 2 = 1 / 2 + j + 1 by ring, hG,
      show (j : ℂ) + ν + 3 / 2 = ν + 1 / 2 + j + 1 by ring, pow_mul]
    have hG0 : Gamma (1 / 2) ≠ 0 := by
      rw [Complex.Gamma_one_half_eq]; exact (cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num)).mpr
        (ofReal_ne_zero.mpr hπ.ne')
    field_simp

/-- The series with terms `(fun k : ℕ => (z/2)^(ν+1/2)/Gamma (ν+1/2) *
((z/2)^k/((k.factorial:ℂ)*(k+ν+1/2))*besselJ (k+1/2) z))` converges to `(struveH ν z)`. -/
@[dlmf 11.4.E20]
theorem struveH_bessel_series_20 (ν : ℂ) (hν : ∀ n : ℕ, ν+1/2 ≠ -n) {z : ℂ} (hz : z ∈ slitPlane) :
    HasSum (fun k : ℕ => (z/2)^(ν+1/2)/Gamma (ν+1/2) * ((z/2)^k/((k.factorial:ℂ)*(k+ν+1/2))*besselJ (k+1/2) z)) (struveH ν z) := by
  have hz0 := slitPlane_ne_zero hz
  have hw0 : z / 2 ≠ 0 := div_ne_zero hz0 two_ne_zero
  set a : ℕ → ℂ := fun k => 1 / ((k ! : ℂ) * (k + ν + 1 / 2)) with ha_def
  obtain ⟨B, hB0, hB⟩ := exists_norm_recip_nat_add_le (ν + 1 / 2 : ℂ)
  have ha : ∀ k, ‖a k‖ ≤ B * 1 ^ k := fun k => by
    have hf : (1 : ℝ) ≤ k ! := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero k)
    show ‖1 / ((k ! : ℂ) * (k + ν + 1 / 2))‖ ≤ B * 1 ^ k
    rw [one_pow, mul_one, one_div, mul_inv, norm_mul, norm_inv, Complex.norm_natCast,
      show (k : ℂ) + ν + 1 / 2 = k + (ν + 1 / 2) by ring]
    calc (k ! : ℝ)⁻¹ * ‖((k : ℂ) + (ν + 1 / 2))⁻¹‖ ≤ 1 * B := by
          gcongr
          · exact inv_le_one_of_one_le₀ hf
          · exact hB k
      _ = B := one_mul B
  have hx : ∀ i : ℕ, (ν + 1 / 2 : ℂ) + i ≠ 0 := fun i h => hν i (by linear_combination h)
  have hcoeff : ∀ j, neumannCoeff (1 / 2) (-1) a (fun k => k) j =
      (-1) ^ j / (Gamma (1 / 2 + j + 1) * ∏ i ∈ Finset.range (j + 1), (ν + 1 / 2 + (i : ℂ))) := by
    intro j
    rw [div_mul_eq_div_div_swap, ← sum_antidiagonal_neg_one_pow_div_add j hx, Finset.sum_div]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_antidiagonal] at hp
    rw [regularizedHGFunCoeff_empty, ha_def]
    dsimp only
    have hj : (j : ℂ) = p.1 + p.2 := by exact_mod_cast hp.symm
    rw [hj, show 1 / 2 + ((p.1 : ℕ) : ℂ) + 1 + ((p.2 : ℕ) : ℂ) = 1 / 2 + (p.1 + p.2) + 1 by
      ring, show (p.1 : ℂ) + ν + 1 / 2 = ν + 1 / 2 + p.1 by ring]
    simp only [div_eq_mul_inv, one_mul, mul_inv]
    ring
  have h := hasSum_besselJ_neumann_of_coeff hz0 (1 / 2) a (fun k => k) (fun k => k)
    (fun k => by ring)
    (summable_neumann_of_norm_le zero_le_one ha _ (fun k => ⟨le_rfl, by omega⟩) _) _ hcoeff
  have h2 := h.mul_left ((z / 2) ^ (ν + 1 / 2) / Gamma (ν + 1 / 2))
  convert h2 using 1
  · funext k
    simp only [ha_def]
    rw [show (k : ℂ) + 1 / 2 = 1 / 2 + k by ring]
    ring
  · have hkey : (z / 2) ^ (ν + 1 / 2) / Gamma (ν + 1 / 2) * (z / 2) ^ (1 / 2 : ℂ) =
        (z / 2) ^ (ν + 1) / Gamma (ν + 1 / 2) := by
      rw [div_mul_eq_mul_div, ← cpow_add _ _ hw0]
      ring_nf
    rw [← mul_assoc, hkey, struveH, struveHCore,
      show ∀ X Y : ℂ, X / Gamma (ν + 1 / 2) * Y = X * ((Gamma (ν + 1 / 2))⁻¹ * Y) from
        fun X Y => by ring,
      ← tsum_mul_left (α := ℂ) (a := (Gamma (ν + 1 / 2))⁻¹)]
    congr 1
    refine tsum_congr fun j => ?_
    have hG := Gamma_add_nat_succ_eq_prod hx j
    have hG0 : Gamma (ν + 1 / 2) ≠ 0 :=
      Complex.Gamma_ne_zero fun m h => hν m (by linear_combination h)
    rw [struveCoeff, show (j : ℂ) + ν + 3 / 2 = ν + 1 / 2 + j + 1 by ring, hG,
      show (j : ℂ) + 3 / 2 = 1 / 2 + j + 1 by ring, pow_mul]
    field_simp

/-- The series with terms `(fun k : ℕ => 4/π*besselJ (2*k+1) z/(2*k+1))` converges to `(struveH 0
z)`. -/
@[dlmf 11.4.E21]
theorem struveH_zero_odd {z : ℂ} (hz : z ∈ slitPlane) :
    HasSum (fun k : ℕ => 4/π*besselJ (2*k+1) z/(2*k+1)) (struveH 0 z) := by
  have h := struveH_bessel_series_18 0 (fun n h => by have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)])
    (fun n h => by have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]) hz
  have hhalf : Gamma (1 / 2) = (Real.sqrt π : ℂ) := by
    rw [Gamma_one_half_eq, show ((1 / 2 : ℂ)) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_cpow Real.pi_pos.le, ← Real.sqrt_eq_rpow]
  have hpi : (Real.sqrt π : ℂ) * Real.sqrt π = π := by
    rw [← ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
  have hπ : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  convert h using 1
  funext k
  have h3 : (2 * k + 1 : ℂ) ≠ 0 := by
    intro h; have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  have hf : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  simp only [zero_add, mul_zero, add_zero]
  rw [hhalf, show (k : ℂ) + 1 = k + 1 by rfl, Complex.Gamma_nat_eq_factorial, ← hpi]
  field_simp

/-- The series with terms `(fun k : ℕ => 2*(-1)^k*(besselJ (k+1/2) (z/2))^2)` converges to
`(struveH 0 z)`. -/
@[dlmf 11.4.E21]
theorem struveH_zero_products {z : ℂ} (hz : z ∈ slitPlane) :
    HasSum (fun k : ℕ => 2*(-1)^k*(besselJ (k+1/2) (z/2))^2) (struveH 0 z) := by
  have hx := div_two_mem_slitPlane hz
  set u : ℂ := z / 4 with hu
  set f : ℕ × ℕ → ℂ := fun p => 2 * (-1) ^ p.1 * u ^ (2 * p.1 + 1) *
    (poch (2 * p.1 + p.2 + 2 : ℂ) p.2 * (-(u ^ 2)) ^ p.2 / p.2 ! *
      ((Gamma (p.1 + p.2 + 3 / 2))⁻¹) ^ 2) with hf
  obtain ⟨C, hC0, hC⟩ := exists_norm_recip_Gamma_add_nat_le (3 / 2 : ℂ)
  -- absolute summability
  have hsum : Summable fun p => ‖f p‖ := by
    have hg := Real.summable_pow_div_factorial (16 * ‖u‖ ^ 2)
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_)
      ((hg.mul_of_nonneg hg (fun _ => by positivity) (fun _ => by positivity)).mul_left
        (4 * C ^ 2 * ‖u‖))
    obtain ⟨k, m⟩ := p
    simp only [hf]
    rw [mul_div_right_comm, poch_div_factorial_eq_choose]
    simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, mul_one,
      Complex.norm_natCast, Complex.norm_ofNat]
    have hch : ((2 * k + 2 * m + 1).choose m : ℝ) ≤ 2 * 4 ^ (k + m) := by
      have := Nat.choose_le_two_pow (2 * k + 2 * m + 1) m
      have h' : (2 : ℕ) ^ (2 * k + 2 * m + 1) = 2 * 4 ^ (k + m) := by
        rw [pow_succ, show 2 * k + 2 * m = 2 * (k + m) by ring, pow_mul]; norm_num; ring
      exact_mod_cast h' ▸ this
    have hG := hC (k + m)
    rw [show (3 / 2 : ℂ) + ((k + m : ℕ) : ℂ) = k + m + 3 / 2 by push_cast; ring] at hG
    have hfac : ((k ! : ℝ) * m !) ≤ ((k + m)! : ℝ) ^ 2 := by
      have h1 : ((k ! : ℝ) * m !) ≤ (k + m)! := by
        exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos _)
          (Nat.factorial_mul_factorial_dvd_factorial_add k m)
      have h2 : (1 : ℝ) ≤ (k + m)! := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
      nlinarith
    have hk0 : (0 : ℝ) < k ! := by exact_mod_cast Nat.factorial_pos k
    have hm0 : (0 : ℝ) < m ! := by exact_mod_cast Nat.factorial_pos m
    calc 2 * ‖u‖ ^ (2 * k + 1) * (((2 * k + 2 * m + 1).choose m : ℝ) * (‖u‖ ^ 2) ^ m *
          ‖(Gamma (k + m + 3 / 2))⁻¹‖ ^ 2)
        ≤ 2 * ‖u‖ ^ (2 * k + 1) * ((2 * 4 ^ (k + m)) * (‖u‖ ^ 2) ^ m *
          (C * (2 ^ (k + m) / (k + m)!)) ^ 2) := by gcongr
      _ = 4 * C ^ 2 * ‖u‖ * ((16 * ‖u‖ ^ 2) ^ k * (16 * ‖u‖ ^ 2) ^ m / ((k + m)! : ℝ) ^ 2) := by
          have e1 : (4 : ℝ) ^ (k + m) = (2 ^ (k + m)) ^ 2 := by
            rw [← pow_mul, mul_comm, pow_mul]; norm_num
          have e2 : (16 * ‖u‖ ^ 2) ^ k * (16 * ‖u‖ ^ 2) ^ m =
              (2 ^ (k + m)) ^ 4 * (‖u‖ ^ (2 * k) * (‖u‖ ^ 2) ^ m) := by
            rw [mul_pow, mul_pow, show (16 : ℝ) ^ k = (2 ^ k) ^ 4 by
                rw [← pow_mul, mul_comm, pow_mul]; norm_num,
              show (16 : ℝ) ^ m = (2 ^ m) ^ 4 by rw [← pow_mul, mul_comm, pow_mul]; norm_num,
              pow_add, mul_pow, ← pow_mul]
            ring
          rw [e1, e2, pow_succ]
          generalize (2 : ℝ) ^ (k + m) = X
          field_simp
          ring
      _ ≤ 4 * C ^ 2 * ‖u‖ * ((16 * ‖u‖ ^ 2) ^ k * (16 * ‖u‖ ^ 2) ^ m / ((k ! : ℝ) * m !)) := by
          gcongr
      _ = _ := by field_simp
  have hs := hsum.of_norm
  -- inner sums
  have hinner : ∀ k : ℕ, HasSum (fun m => f (k, m)) (2 * (-1) ^ k * (besselJ (k + 1 / 2) (z / 2)) ^ 2) := by
    intro k
    rw [pow_two, besselJ_mul_besselJ _ _ hx]
    rw [show (k : ℂ) + 1 / 2 + (k + 1 / 2) = ((2 * k + 1 : ℕ) : ℂ) by push_cast; ring, cpow_natCast,
      show z / 2 / 2 = u by rw [hu]; ring]
    convert (hs.prod_factor k).hasSum using 1
    rw [← tsum_mul_left, ← tsum_mul_left]
    refine tsum_congr fun m => ?_
    simp only [hf]
    rw [show (((2 * k + 1 : ℕ) : ℂ) + m + 1) = 2 * k + m + 2 by push_cast; ring,
      show (k : ℂ) + 1 / 2 + m + 1 = k + m + 3 / 2 by ring,
      show -((z / 2) ^ 2 / 4) = -(u ^ 2) by rw [hu]; ring]
    ring
  have h1 := hs.hasSum.prod_fiberwise hinner
  -- Finset.antidiagonal sums
  have hs2 := hs.hasSum
  rw [← (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd).hasSum_iff] at hs2
  have h2 := hs2.sigma fun j => hasSum_fintype _
  have hcoef : ∀ j : ℕ, ∑ b : Finset.antidiagonal j,
      (f ∘ Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd) ⟨j, b⟩ =
      z / 2 * ((-1) ^ j * (z / 2) ^ (2 * j) * struveCoeff 0 j) := by
    intro j
    simp only [Function.comp_apply, Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd_apply]
    rw [Finset.sum_coe_sort (Finset.antidiagonal j) f]
    have hterm : ∀ p ∈ Finset.antidiagonal j, f p = 2 * (-1) ^ j * u ^ (2 * j + 1) *
        ((Gamma (j + 3 / 2))⁻¹) ^ 2 * ((2 * j + 1).choose p.2 : ℕ) := by
      intro p hp
      rw [Finset.mem_antidiagonal] at hp
      obtain ⟨k, m⟩ := p
      simp only at hp
      subst hp
      simp only [hf]
      rw [mul_div_right_comm, poch_div_factorial_eq_choose,
        show 2 * (k + m) + 1 = 2 * k + 2 * m + 1 by ring, neg_pow (u ^ 2) m, ← pow_mul]
      push_cast
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    have hsw := Finset.Nat.sum_antidiagonal_swap (n := j)
      (f := fun p : ℕ × ℕ => (((2 * j + 1).choose p.2 : ℕ) : ℂ))
    simp only [Prod.snd_swap] at hsw
    rw [← hsw, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a _ =>
      (((2 * j + 1).choose a : ℕ) : ℂ)) j]
    rw [show ∑ k ∈ Finset.range j.succ, (((2 * j + 1).choose k : ℕ) : ℂ) = ((4 ^ j : ℕ) : ℂ) by
      rw [← Nat.sum_range_choose_halfway j]; push_cast; rfl]
    rw [struveCoeff, hu]
    push_cast
    rw [show (j : ℂ) + 0 + 3 / 2 = j + 3 / 2 by ring]
    have h4 : (4 : ℂ) = 2 ^ 2 := by norm_num
    rw [h4, div_pow, div_pow]
    simp only [← pow_mul]
    field_simp
    ring
  simp_rw [hcoef] at h2
  have h3 := (hasSum_struveHCore 0 z).mul_left (z / 2)
  have heq := h2.unique h3
  rw [struveH, show ((0 : ℂ) + 1) = ((1 : ℕ) : ℂ) by simp, cpow_natCast, pow_one, ← heq]
  exact h1

/-- The series with terms `(fun k : ℕ => 4/π*besselJ (2*(k+1)) z/(4*(k+1:ℂ)^2-1))` converges to
`(struveH 1 z-2/π*(1-besselJ 0 z))`. -/
@[dlmf 11.4.E22]
theorem struveH_one_even {z : ℂ} (hz : z ∈ slitPlane) :
    HasSum (fun k : ℕ => 4/π*besselJ (2*(k+1)) z/(4*(k+1:ℂ)^2-1)) (struveH 1 z-2/π*(1-besselJ 0 z)) := by
  have h := struveH_bessel_series_18 1 (fun n h => by have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)])
    (fun n h => by have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]) hz
  have hJ := (hasSum_besselJ_cos z 0).mul_left (2 / (π : ℂ))
  simp only [Complex.ofReal_zero, mul_zero, Complex.cos_zero, mul_one, Complex.sin_zero] at hJ
  have hd := h.sub hJ
  have hΓ : Gamma (1 + 1 / 2) = (Real.sqrt π : ℂ) / 2 := by
    rw [show (1 + 1 / 2 : ℂ) = 1 / 2 + 1 by ring, Gamma_add_one _ (by norm_num), Gamma_one_half_eq,
      show ((1 / 2 : ℂ)) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_cpow Real.pi_pos.le, ← Real.sqrt_eq_rpow]
    push_cast; ring
  have hpi : (Real.sqrt π : ℂ) * Real.sqrt π = π := by
    rw [← ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
  have hπ : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hπ' : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_pos.ne'
  convert hd using 1
  · funext k
    have h3 : (2 * k + 1 : ℂ) ≠ 0 := by
      intro h; have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
    have h4 : (2 * k + 2 * 1 + 1 : ℂ) ≠ 0 := by
      intro h; have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
    have h5 : (4 * (k + 1 : ℂ) ^ 2 - 1) ≠ 0 := by
      rw [show (4 * (k + 1 : ℂ) ^ 2 - 1) = (2 * k + 1) * (2 * k + 2 * 1 + 1) by ring]
      exact mul_ne_zero h3 h4
    have hf : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    rw [hΓ, show (k : ℂ) + 1 + 1 = ((k + 1 : ℕ) : ℂ) + 1 by push_cast; ring,
      Complex.Gamma_nat_eq_factorial, show (2 * k + 1 + 1 : ℂ) = ((2 * k + 2 : ℕ) : ℂ) by
        push_cast; ring, show (2 * ((k : ℂ) + 1)) = ((2 * k + 2 : ℕ) : ℂ) by push_cast; ring,
      Nat.factorial_succ]
    generalize besselJ ((2 * k + 2 : ℕ) : ℂ) z = J
    rw [← hpi]
    push_cast
    rw [show (4 * ((k : ℂ) + 1) ^ 2 - 1) = (2 * k + 1) * (2 * k + 3) by ring,
      show (2 * (k : ℂ) + 2 * 1 + 1) = 2 * k + 3 by ring]
    have h4' : (2 * k + 3 : ℂ) ≠ 0 := by
      intro h; have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
    field_simp
    ring

/-- `(n+1)_m / m! = C(n+m, m)` for natural `n`. -/
theorem poch_natCast_add_one_div_factorial (n m : ℕ) :
    poch ((n : ℂ) + 1) m / m ! = ((n + m).choose m : ℕ) := by
  have h1 := poch_natCast_add_one_mul_factorial n m
  have h2 := Nat.choose_mul_factorial_mul_factorial (show m ≤ n + m by omega)
  rw [show n + m - m = n by omega] at h2
  rw [← h2] at h1
  have hf1 : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hf2 : (m ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  push_cast at h1 ⊢
  rw [div_eq_iff hf2]
  apply mul_right_cancel₀ hf1
  rw [h1]

/-- Parity-restricted binomial sums: `∑_{b ≤ j, j - b even} C(n+1, b) = ∑_{b ≤ j} C(n, b)`. -/
theorem sum_range_even_choose_succ (n j : ℕ) :
    ∑ b ∈ Finset.range (j + 1), (if Even (j - b) then (n + 1).choose b else 0) =
      ∑ b ∈ Finset.range (j + 1), n.choose b := by
  induction j using Nat.twoStepInduction with
  | zero => simp
  | one => simp [Finset.sum_range_succ]; omega
  | more j ih _ =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ (fun b => n.choose b),
      Finset.sum_range_succ (fun b => n.choose b), ← ih]
    have : ∀ b ∈ Finset.range (j + 1), (if Even (j + 2 - b) then (n + 1).choose b else 0) =
        (if Even (j - b) then (n + 1).choose b else 0) := by
      intro b hb
      rw [Finset.mem_range] at hb
      rw [show j + 2 - b = (j - b) + 2 by omega]
      simp [Nat.even_add]
    rw [Finset.sum_congr rfl this]
    simp [show j + 2 - (j + 1) = 1 by omega, Nat.choose_succ_succ]
    ring

/-- `∑_{a ≤ j, a even} C(2j+2, j-a) = 4^j`. -/
theorem sum_range_even_choose_eq_four_pow (j : ℕ) : ∑ a ∈ Finset.range (j + 1), (if Even a then (2 * j + 2).choose (j - a) else 0)
    = 4 ^ j := by
  rw [← Finset.sum_range_reflect, ← Nat.sum_range_choose_halfway j]
  rw [← sum_range_even_choose_succ]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [Finset.mem_range] at hb
  rw [show j + 1 - 1 - b = j - b by omega, show j - (j - b) = b by omega]

/-- The series with terms `(fun k : ℕ => 4*besselJ (2*k+1/2) (z/2)*besselJ (2*k+3/2) (z/2))`
converges to `(struveH 1 z)`. -/
@[dlmf 11.4.E22]
theorem struveH_one_products {z : ℂ} (hz : z ∈ slitPlane) :
    HasSum (fun k : ℕ => 4*besselJ (2*k+1/2) (z/2)*besselJ (2*k+3/2) (z/2)) (struveH 1 z) := by
  have hx := div_two_mem_slitPlane hz
  set u : ℂ := z / 4 with hu
  set f : ℕ × ℕ → ℂ := fun p => 4 * u ^ (4 * p.1 + 2) *
    (poch (4 * p.1 + p.2 + 3 : ℂ) p.2 * (-(u ^ 2)) ^ p.2 / p.2 ! *
      ((Gamma (2 * p.1 + p.2 + 3 / 2))⁻¹ * (Gamma (2 * p.1 + p.2 + 5 / 2))⁻¹)) with hf
  have hpoch : ∀ k m : ℕ, poch (4 * k + m + 3 : ℂ) m / m ! = ((4 * k + 2 * m + 2).choose m : ℕ) := by
    intro k m
    rw [show (4 * k + m + 3 : ℂ) = ((4 * k + m + 2 : ℕ) : ℂ) + 1 by push_cast; ring,
      poch_natCast_add_one_div_factorial, show 4 * k + m + 2 + m = 4 * k + 2 * m + 2 by ring]
  obtain ⟨C, hC0, hC⟩ := exists_norm_recip_Gamma_add_nat_le (3 / 2 : ℂ)
  obtain ⟨C', hC0', hC'⟩ := exists_norm_recip_Gamma_add_nat_le (5 / 2 : ℂ)
  -- absolute summability
  have hsum : Summable fun p => ‖f p‖ := by
    have hA := Real.summable_pow_div_factorial (256 * ‖u‖ ^ 4)
    have hB := Real.summable_pow_div_factorial (16 * ‖u‖ ^ 2)
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_)
      ((hA.mul_of_nonneg hB (fun _ => by positivity) (fun _ => by positivity)).mul_left
        (16 * C * C' * ‖u‖ ^ 2))
    obtain ⟨k, m⟩ := p
    simp only [hf]
    rw [mul_div_right_comm, hpoch]
    simp only [norm_mul, norm_pow, norm_neg, Complex.norm_natCast, Complex.norm_ofNat]
    have hch : ((4 * k + 2 * m + 2).choose m : ℝ) ≤ 4 * 16 ^ k * 4 ^ m := by
      have := Nat.choose_le_two_pow (4 * k + 2 * m + 2) m
      have h' : (2 : ℕ) ^ (4 * k + 2 * m + 2) = 4 * 16 ^ k * 4 ^ m := by
        rw [pow_add, pow_add, pow_mul, pow_mul]; norm_num; ring
      exact_mod_cast h' ▸ this
    have hG := hC (2 * k + m)
    have hG' := hC' (2 * k + m)
    rw [show (3 / 2 : ℂ) + ((2 * k + m : ℕ) : ℂ) = 2 * k + m + 3 / 2 by push_cast; ring] at hG
    rw [show (5 / 2 : ℂ) + ((2 * k + m : ℕ) : ℂ) = 2 * k + m + 5 / 2 by push_cast; ring] at hG'
    have hfac : ((k ! : ℝ) * m !) ≤ ((2 * k + m)! : ℝ) ^ 2 := by
      have h1 : ((k ! : ℝ) * m !) ≤ (2 * k + m)! := by
        have h0 : k ! * m ! ≤ (k + m)! := Nat.le_of_dvd (Nat.factorial_pos _)
          (Nat.factorial_mul_factorial_dvd_factorial_add k m)
        exact_mod_cast h0.trans (Nat.factorial_le (by omega))
      have h2 : (1 : ℝ) ≤ (2 * k + m)! := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
      nlinarith
    have hk0 : (0 : ℝ) < k ! := by exact_mod_cast Nat.factorial_pos k
    have hm0 : (0 : ℝ) < m ! := by exact_mod_cast Nat.factorial_pos m
    have hn0 : (0 : ℝ) < (2 * k + m)! := by exact_mod_cast Nat.factorial_pos _
    calc 4 * ‖u‖ ^ (4 * k + 2) * (((4 * k + 2 * m + 2).choose m : ℝ) * (‖u‖ ^ 2) ^ m *
          (‖(Gamma (2 * k + m + 3 / 2))⁻¹‖ * ‖(Gamma (2 * k + m + 5 / 2))⁻¹‖))
        ≤ 4 * ‖u‖ ^ (4 * k + 2) * ((4 * 16 ^ k * 4 ^ m) * (‖u‖ ^ 2) ^ m *
          ((C * (2 ^ (2 * k + m) / (2 * k + m)!)) * (C' * (2 ^ (2 * k + m) / (2 * k + m)!)))) := by
          gcongr
      _ = 16 * C * C' * ‖u‖ ^ 2 * ((256 * ‖u‖ ^ 4) ^ k * (16 * ‖u‖ ^ 2) ^ m /
            ((2 * k + m)! : ℝ) ^ 2) := by
          field_simp
          rw [mul_pow (‖u‖ ^ 4), mul_pow (‖u‖ ^ 2),
            show (256 : ℝ) ^ k = 16 ^ k * 16 ^ k by rw [← mul_pow]; norm_num,
            show (16 : ℝ) ^ m = 4 ^ m * 4 ^ m by rw [← mul_pow]; norm_num,
            show ((2 : ℝ) ^ (2 * k + m)) ^ 2 = 16 ^ k * 4 ^ m by
              rw [← pow_mul, show (2 * k + m) * 2 = 2 * (2 * k) + 2 * m by ring, pow_add, pow_mul,
                pow_mul, ← pow_mul]; norm_num; rw [pow_mul, pow_mul]; norm_num]
          ring
      _ ≤ 16 * C * C' * ‖u‖ ^ 2 * ((256 * ‖u‖ ^ 4) ^ k * (16 * ‖u‖ ^ 2) ^ m /
            ((k ! : ℝ) * m !)) := by
          gcongr
      _ = _ := by field_simp
  have hs := hsum.of_norm
  -- inner sums
  have hinner : ∀ k : ℕ, HasSum (fun m => f (k, m))
      (4 * besselJ (2 * k + 1 / 2) (z / 2) * besselJ (2 * k + 3 / 2) (z / 2)) := by
    intro k
    rw [mul_assoc, besselJ_mul_besselJ _ _ hx]
    rw [show (2 * k : ℂ) + 1 / 2 + (2 * k + 3 / 2) = ((4 * k + 2 : ℕ) : ℂ) by push_cast; ring,
      cpow_natCast, show z / 2 / 2 = u by rw [hu]; ring]
    convert (hs.prod_factor k).hasSum using 1
    rw [← tsum_mul_left, ← tsum_mul_left]
    refine tsum_congr fun m => ?_
    simp only [hf]
    rw [show (((4 * k + 2 : ℕ) : ℂ) + m + 1) = 4 * k + m + 3 by push_cast; ring,
      show (2 * k : ℂ) + 1 / 2 + m + 1 = 2 * k + m + 3 / 2 by ring,
      show (2 * k : ℂ) + 3 / 2 + m + 1 = 2 * k + m + 5 / 2 by ring,
      show -((z / 2) ^ 2 / 4) = -(u ^ 2) by rw [hu]; ring]
    ring
  have h1 := hs.hasSum.prod_fiberwise hinner
  -- spread the first index over even integers
  set h : ℕ × ℕ → ℂ := fun p => if Even p.1 then f (p.1 / 2, p.2) else 0 with hh
  set g : ℕ × ℕ → ℕ × ℕ := fun p => (2 * p.1, p.2) with hg
  have hginj : Function.Injective g := by
    intro p q hpq
    simp only [hg, Prod.mk.injEq] at hpq
    exact Prod.ext (by omega) hpq.2
  have hhg : h ∘ g = f := by
    funext p
    simp [hh, hg, Nat.mul_div_cancel_left _ two_pos]
  have hzero : ∀ x ∉ Set.range g, h x = 0 := by
    intro x hx'
    simp only [hh]
    split_ifs with he
    · exfalso; apply hx'
      obtain ⟨r, hr⟩ := he
      exact ⟨(r, x.2), Prod.ext (by simp only [hg]; omega) rfl⟩
    · rfl
  have hhs : HasSum h (∑' p, f p) := by
    rw [← hginj.hasSum_iff hzero, hhg]; exact hs.hasSum
  have hs2 := hhs
  rw [← (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd).hasSum_iff] at hs2
  have h2 := hs2.sigma fun j => hasSum_fintype _
  have hcoef : ∀ j : ℕ, ∑ b : Finset.antidiagonal j,
      (h ∘ Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd) ⟨j, b⟩ =
      (z / 2) ^ 2 * ((-1) ^ j * (z / 2) ^ (2 * j) * struveCoeff 1 j) := by
    intro j
    simp only [Function.comp_apply, Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd_apply]
    rw [Finset.sum_coe_sort (Finset.antidiagonal j) h]
    have hterm : ∀ p ∈ Finset.antidiagonal j, h p = 4 * (-1) ^ j * u ^ (2 * j + 2) *
        ((Gamma (j + 3 / 2))⁻¹ * (Gamma (j + 5 / 2))⁻¹) *
        (if Even p.1 then (((2 * j + 2).choose (j - p.1) : ℕ) : ℂ) else 0) := by
      intro p hp
      rw [Finset.mem_antidiagonal] at hp
      obtain ⟨a, b⟩ := p
      simp only at hp
      subst hp
      simp only [hh]
      split_ifs with he
      · obtain ⟨k, rfl⟩ := he
        simp only [hf]
        rw [show (k + k) / 2 = k by omega, mul_div_right_comm, hpoch,
          show 4 * k + 2 * b + 2 = 2 * (k + k + b) + 2 by ring,
          show k + k + b - (k + k) = b by omega, neg_pow (u ^ 2) b, ← pow_mul]
        rw [show (-1 : ℂ) ^ (k + k + b) = (-1) ^ b by
          rw [pow_add, ← two_mul, pow_mul]; norm_num]
        push_cast
        rw [show (2 * (k : ℂ) + b + 3 / 2) = k + k + b + 3 / 2 by ring,
          show (2 * (k : ℂ) + b + 5 / 2) = k + k + b + 5 / 2 by ring]
        ring
      · simp
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a _ =>
      (if Even a then (((2 * j + 2).choose (j - a) : ℕ) : ℂ) else 0)) j]
    have h4 : ∑ a ∈ Finset.range j.succ,
        (if Even a then (((2 * j + 2).choose (j - a) : ℕ) : ℂ) else 0) = ((4 ^ j : ℕ) : ℂ) := by
      rw [← sum_range_even_choose_eq_four_pow j]
      push_cast
      refine Finset.sum_congr rfl fun a _ => ?_
      split_ifs <;> simp
    rw [h4, struveCoeff, hu]
    push_cast
    rw [show (j : ℂ) + 1 + 3 / 2 = j + 5 / 2 by ring]
    have h4' : (4 : ℂ) = 2 ^ 2 := by norm_num
    rw [h4', div_pow, div_pow]
    simp only [← pow_mul]
    field_simp
    congr 1
    rw [div_pow]
    field_simp
    ring
  simp_rw [hcoef] at h2
  have h3 := (hasSum_struveHCore 1 z).mul_left ((z / 2) ^ 2)
  have heq := h2.unique h3
  rw [struveH, show ((1 : ℂ) + 1) = ((2 : ℕ) : ℂ) by norm_num, cpow_natCast, ← heq]
  exact h1

/-- Identity under the stated parameter and domain assumptions: `struveH (ν-1) z + struveH (ν+1) z
= 2*ν/z*struveH ν z+(z/2)^ν/(Real.sqrt π*Gamma (ν+3/2))`. -/
@[dlmf 11.4.E23]
theorem struveH_recurrence (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    struveH (ν-1) z + struveH (ν+1) z = 2*ν/z*struveH ν z+(z/2)^ν/(Real.sqrt π*Gamma (ν+3/2)) := by
  have h := struveQuadratic_recurrence ν (-1) hz
  simpa only [struveQuadratic_H, neg_one_mul, sub_neg_eq_add, one_mul] using h

/-- At `z`, the function `(struveH ν)` has derivative `((struveH (ν-1) z - struveH (ν+1)
z+(z/2)^ν/(Real.sqrt π*Gamma (ν+3/2)))/2)`. -/
@[dlmf 11.4.E24]
theorem struveH_derivative (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (struveH ν) ((struveH (ν-1) z - struveH (ν+1) z+(z/2)^ν/(Real.sqrt π*Gamma (ν+3/2)))/2) z := by
  have hd := hasDerivAt_struveQuadratic ν (-1) hz
  rw [funext (struveQuadratic_H ν)] at hd
  simp only [struveQuadratic_H] at hd
  refine hd.congr_deriv ?_
  have hr := struveH_recurrence ν hz
  linear_combination hr/2

/-- At `z`, the function `(fun z : ℂ => z^(1*ν)*struveH ν z)` has derivative `(z^ν*struveH (ν-1)
z)`. -/
@[dlmf 11.4.E27, dlmf 11.7.E1]
theorem struveH_weighted_deriv_27 (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (fun z : ℂ => z^(1*ν)*struveH ν z) (z^ν*struveH (ν-1) z) z := by
  have hd := hasDerivAt_weighted_struveQuadratic ν (-1) hz
  simpa only [struveQuadratic_H, one_mul, neg_one_mul, neg_mul, ← sub_eq_add_neg] using hd

/-- At `z`, the function `(fun z : ℂ => z^(-1*ν)*struveH ν z)` has derivative `(2^(-ν)/(Real.sqrt
π*Gamma (ν+3/2)) - z^(-ν)*struveH (ν+1) z)`. -/
@[dlmf 11.4.E28, dlmf 11.7.E2]
theorem struveH_weighted_deriv_28 (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (fun z : ℂ => z^(-1*ν)*struveH ν z) (2^(-ν)/(Real.sqrt π*Gamma (ν+3/2)) - z^(-ν)*struveH (ν+1) z) z := by
  have hd := hasDerivAt_reciprocal_weighted_struveQuadratic ν (-1) hz
  simpa only [struveQuadratic_H, one_mul, neg_one_mul, neg_mul, ← sub_eq_add_neg] using hd

/-- Identity under the stated parameter and domain assumptions: `((fun f : ℂ → ℂ => fun z => deriv
f z/z)^[m]) (fun z => z^ν*struveH ν z) z = z^(ν-m)*struveH (ν-m) z`. -/
@[dlmf 11.4.E31]
theorem struveH_iterated_weighted_deriv (ν : ℂ) (m : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    ((fun f : ℂ → ℂ => fun z => deriv f z/z)^[m]) (fun z => z^ν*struveH ν z) z = z^(ν-m)*struveH (ν-m) z := by
  have he := iterated_weighted_struveQuadratic ν (-1) m hz
  simpa only [struveQuadratic_H] using he

/-- At `z`, the function `(struveH 0)` has derivative `(2/π - struveH 1 z)`. -/
@[dlmf 11.4.E32]
theorem struveH_zero_deriv (z : ℂ) :
    HasDerivAt (struveH 0) (2/π - struveH 1 z) z := by
  have hf : Differentiable ℂ (struveH 0) := by simpa using struveH_nat_entire 0
  have hg : Differentiable ℂ (struveH 1) := by simpa using struveH_nat_entire 1
  have he : deriv (struveH 0)=(fun z => 2/(π:ℂ)-struveH 1 z) := by
    apply Complex.eq_of_differentiable_of_eqOn_pos_reals
    · exact fun z => ((hf.differentiableOn.analyticOnNhd isOpen_univ) z (mem_univ z)).deriv.differentiableAt
    · fun_prop
    · intro x hx
      have hz : (x:ℂ)∈slitPlane := Or.inl (by simpa using hx)
      have hd := struveH_weighted_deriv_28 0 hz
      norm_num only [mul_zero,neg_zero,cpow_zero,one_mul,zero_add] at hd
      rw [hd.deriv]
      have hG := Gamma_oddProduct 0
      norm_num [oddProduct] at hG
      have hp : (Real.sqrt π:ℂ)^2=(π:ℂ) := by exact_mod_cast Real.sq_sqrt Real.pi_pos.le
      have hc : (Real.sqrt π:ℂ)*Gamma (3/2)=π/2 := by rw [hG]; linear_combination hp/2
      rw [hc]
      congr 1
      field_simp
  exact (hf z).hasDerivAt.congr_deriv (congrFun he z)

/-- At `z`, the function `(fun z => z*struveH 1 z)` has derivative `(z*struveH 0 z)`. -/
@[dlmf 11.4.E32]
theorem struveH_one_weighted_deriv (z : ℂ) :
    HasDerivAt (fun z => z*struveH 1 z) (z*struveH 0 z) z := by
  have h0 : Differentiable ℂ (struveH 0) := by simpa using struveH_nat_entire 0
  have h1 : Differentiable ℂ (struveH 1) := by simpa using struveH_nat_entire 1
  have hf : Differentiable ℂ (fun z => z*struveH 1 z) := by fun_prop
  have he : deriv (fun z => z*struveH 1 z)=(fun z => z*struveH 0 z) := by
    apply Complex.eq_of_differentiable_of_eqOn_pos_reals
    · exact fun z => ((hf.differentiableOn.analyticOnNhd isOpen_univ) z (mem_univ z)).deriv.differentiableAt
    · fun_prop
    · intro x hx
      have hz : (x:ℂ)∈slitPlane := Or.inl (by simpa using hx)
      simpa using (struveH_weighted_deriv_27 1 hz).deriv
  exact (hf z).hasDerivAt.congr_deriv (congrFun he z)

/-- Identity under the stated parameter and domain assumptions: `struveL (ν-1) z - struveL (ν+1) z
= 2*ν/z*struveL ν z+(z/2)^ν/(Real.sqrt π*Gamma (ν+3/2))`. -/
@[dlmf 11.4.E25]
theorem struveL_recurrence (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    struveL (ν-1) z - struveL (ν+1) z = 2*ν/z*struveL ν z+(z/2)^ν/(Real.sqrt π*Gamma (ν+3/2)) := by
  have h := struveQuadratic_recurrence ν (1) hz
  simpa only [struveQuadratic_L, neg_one_mul, sub_neg_eq_add, one_mul] using h

/-- At `z`, the function `(struveL ν)` has derivative `((struveL (ν-1) z + struveL (ν+1)
z+(z/2)^ν/(Real.sqrt π*Gamma (ν+3/2)))/2)`. -/
@[dlmf 11.4.E26]
theorem struveL_derivative (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (struveL ν) ((struveL (ν-1) z + struveL (ν+1) z+(z/2)^ν/(Real.sqrt π*Gamma (ν+3/2)))/2) z := by
  have hd := hasDerivAt_struveQuadratic ν (1) hz
  rw [funext (struveQuadratic_L ν)] at hd
  simp only [struveQuadratic_L] at hd
  refine hd.congr_deriv ?_
  have hr := struveL_recurrence ν hz
  linear_combination hr/2

/-- At `z`, the function `(fun z : ℂ => z^(1*ν)*struveL ν z)` has derivative `(z^ν*struveL (ν-1)
z)`. -/
@[dlmf 11.4.E29, dlmf 11.7.E3]
theorem struveL_weighted_deriv_29 (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (fun z : ℂ => z^(1*ν)*struveL ν z) (z^ν*struveL (ν-1) z) z := by
  have hd := hasDerivAt_weighted_struveQuadratic ν (1) hz
  simpa only [struveQuadratic_L, one_mul, neg_one_mul, neg_mul, ← sub_eq_add_neg] using hd

/-- At `z`, the function `(fun z : ℂ => z^(-1*ν)*struveL ν z)` has derivative `(2^(-ν)/(Real.sqrt
π*Gamma (ν+3/2)) + z^(-ν)*struveL (ν+1) z)`. -/
@[dlmf 11.4.E30, dlmf 11.7.E4]
theorem struveL_weighted_deriv_30 (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (fun z : ℂ => z^(-1*ν)*struveL ν z) (2^(-ν)/(Real.sqrt π*Gamma (ν+3/2)) + z^(-ν)*struveL (ν+1) z) z := by
  have hd := hasDerivAt_reciprocal_weighted_struveQuadratic ν (1) hz
  simpa only [struveQuadratic_L, one_mul, neg_one_mul, neg_mul, ← sub_eq_add_neg] using hd

/-- Identity under the stated parameter and domain assumptions: `((fun f : ℂ → ℂ => fun z => deriv
f z/z)^[m]) (fun z => z^ν*struveL ν z) z = z^(ν-m)*struveL (ν-m) z`. -/
@[dlmf 11.4.E31]
theorem struveL_iterated_weighted_deriv (ν : ℂ) (m : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    ((fun f : ℂ → ℂ => fun z => deriv f z/z)^[m]) (fun z => z^ν*struveL ν z) z = z^(ν-m)*struveL (ν-m) z := by
  have he := iterated_weighted_struveQuadratic ν (1) m hz
  simpa only [struveQuadratic_L] using he

/-- At `z`, the function `(struveL 0)` has derivative `(2/π + struveL 1 z)`. -/
@[dlmf 11.4.E33]
theorem struveL_zero_deriv (z : ℂ) :
    HasDerivAt (struveL 0) (2/π + struveL 1 z) z := by
  have hf : Differentiable ℂ (struveL 0) := by simpa using struveL_nat_entire 0
  have hg : Differentiable ℂ (struveL 1) := by simpa using struveL_nat_entire 1
  have he : deriv (struveL 0)=(fun z => 2/(π:ℂ)+struveL 1 z) := by
    apply Complex.eq_of_differentiable_of_eqOn_pos_reals
    · exact fun z => ((hf.differentiableOn.analyticOnNhd isOpen_univ) z (mem_univ z)).deriv.differentiableAt
    · fun_prop
    · intro x hx
      have hz : (x:ℂ)∈slitPlane := Or.inl (by simpa using hx)
      have hd := struveL_weighted_deriv_30 0 hz
      norm_num only [mul_zero,neg_zero,cpow_zero,one_mul,zero_add] at hd
      rw [hd.deriv]
      have hG := Gamma_oddProduct 0
      norm_num [oddProduct] at hG
      have hp : (Real.sqrt π:ℂ)^2=(π:ℂ) := by exact_mod_cast Real.sq_sqrt Real.pi_pos.le
      have hc : (Real.sqrt π:ℂ)*Gamma (3/2)=π/2 := by rw [hG]; linear_combination hp/2
      rw [hc]
      congr 1
      field_simp
  exact (hf z).hasDerivAt.congr_deriv (congrFun he z)

/-- At `z`, the function `(fun z => z*struveL 1 z)` has derivative `(z*struveL 0 z)`. -/
@[dlmf 11.4.E33]
theorem struveL_one_weighted_deriv (z : ℂ) :
    HasDerivAt (fun z => z*struveL 1 z) (z*struveL 0 z) z := by
  have h0 : Differentiable ℂ (struveL 0) := by simpa using struveL_nat_entire 0
  have h1 : Differentiable ℂ (struveL 1) := by simpa using struveL_nat_entire 1
  have hf : Differentiable ℂ (fun z => z*struveL 1 z) := by fun_prop
  have he : deriv (fun z => z*struveL 1 z)=(fun z => z*struveL 0 z) := by
    apply Complex.eq_of_differentiable_of_eqOn_pos_reals
    · exact fun z => ((hf.differentiableOn.analyticOnNhd isOpen_univ) z (mem_univ z)).deriv.differentiableAt
    · fun_prop
    · intro x hx
      have hz : (x:ℂ)∈slitPlane := Or.inl (by simpa using hx)
      simpa using (struveL_weighted_deriv_29 1 hz).deriv
  exact (hf z).hasDerivAt.congr_deriv (congrFun he z)

end DLMF.Struve
