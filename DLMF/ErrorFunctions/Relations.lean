/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.ExpIntegral
public import DLMF.ErrorFunctions.AnalyticProperties
public import DLMF.Hypergeometric.Basic.GeneralizedCalculus

/-!
# Symmetries, derivatives and interrelations of error functions (DLMF §§7.4–7.5, 7.10–7.11)

Symmetry relations (§7.4), interrelations between the error, Dawson, Faddeeva and Fresnel
functions (§7.5), derivatives (§7.10), and relations to incomplete Gamma, confluent and
generalized hypergeometric functions (§7.11).

## Main definitions

* `fresnelZetaComplex`: the signed Fresnel-to-Gaussian change of variable (DLMF 7.5.7).

## Main results

* `erf_negative`, `erfc_negative`, `faddeevaW_negative`, `dawsonF_negative`, `fresnel_negative`,
  `fresnel_mul_I`, `FresnelAuxiliary.mul_I`, `FresnelAuxiliary.negative`: DLMF 7.4.1–7.4.8.
* `dawsonF_faddeeva`, `fresnel_sum_tail`, `fresnelC_aux`, `fresnelS_aux`,
  `fresnelTail_aux`, `fresnel_signed_tail`: DLMF 7.5.1–7.5.6.
* `fresnel_signed_erf`, `fresnel_signed_faddeeva`, `FresnelAuxiliary.signed_erfc`: the Fresnel
  integrals through `erf`, `w` and `erfc` (DLMF 7.5.8–7.5.10).
* `fresnelTail_norm_sq_nonneg`, `fresnelTail_norm_sq_nonpos`: DLMF 7.5.11, 7.5.12.
* `iteratedDeriv_erf_hermite`, `hasDerivAt_faddeevaW`, `iteratedDeriv_faddeevaW_recurrence`,
  `hasDerivAt_fresnelAux`: derivatives (DLMF 7.10.1–7.10.4).
* `erf_lowerIncompleteGamma`, `erfc_upperIncompleteGamma`, `erfc_expIntegralE`: DLMF 7.11.1–7.11.3.
* `erf_kummerM_pair`, `erfc_kummerU_pair`, `fresnel_kummerM_pair`: confluent hypergeometric
  representations (DLMF 7.11.4–7.11.6).
* `fresnelC_hypergeometric`, `fresnelS_hypergeometric`: `₁F₂` representations of
  `C(z)` and `S(z)` (DLMF 7.11.7, 7.11.8).

## Implementation notes

The Faddeeva ladder (7.10.3) follows by differentiating the first-order equation (7.10.2). The
Fresnel representations use Mathlib's regularized hypergeometric coefficients and the
termwise-integrated sine and cosine series.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
open DLMF.Core

namespace DLMF.Confluent

/-- Identity under the stated parameter and domain assumptions: `erf (-z)=-erf z`. -/
@[dlmf 7.4.E1]
theorem erf_negative (z : ℂ) :
    erf (-z)=-erf z := by
  simp [erf]

/-- Identity under the stated parameter and domain assumptions: `erfc (-z)=2-erfc z`. -/
@[dlmf 7.4.E2]
theorem erfc_negative (z : ℂ) :
    erfc (-z)=2-erfc z := by
  simp [erfc, erf_negative]
  ring

/-- Identity under the stated parameter and domain assumptions: `faddeevaW (-z)=2*exp
(-z^2)-faddeevaW z`. -/
@[dlmf 7.4.E3]
theorem faddeevaW_negative (z : ℂ) :
    faddeevaW (-z)=2*exp (-z^2)-faddeevaW z := by
  simp only [faddeevaW, neg_sq, mul_neg, erfc_negative]
  ring

/-- Identity under the stated parameter and domain assumptions: `dawsonF (-z)=-dawsonF z`. -/
@[dlmf 7.4.E4]
theorem dawsonF_negative (z : ℂ) :
    dawsonF (-z)=-dawsonF z := by
  simp [dawsonF, primitive, segmentIntegral, mul_pow]

/-- Identity under the stated parameter and domain assumptions: `fresnelC (-z) =
-fresnelC z ∧ fresnelS (-z) = -fresnelS z`. -/
@[dlmf 7.4.E5]
theorem fresnel_negative (z : ℂ) :
    fresnelC (-z) = -fresnelC z ∧ fresnelS (-z) = -fresnelS z := by
  constructor <;> simp [fresnelC, fresnelS, primitive, segmentIntegral, mul_pow]

/-- Identity under the stated parameter and domain assumptions: `fresnelC (I*z) =
I*fresnelC z ∧ fresnelS (I*z) = -I*fresnelS z`. -/
@[dlmf 7.4.E6]
theorem fresnel_mul_I (z : ℂ) :
    fresnelC (I*z) = I*fresnelC z ∧ fresnelS (I*z) = -I*fresnelS z := by
  constructor
  · have he : (fun t : ℝ => cos (π*((t:ℂ)*(I*z))^2/2)) =
        (fun t : ℝ => cos (π*((t:ℂ)*z)^2/2)) := by
      funext t
      rw [show π*((t:ℂ)*(I*z))^2/2=-(π*((t:ℂ)*z)^2/2) by simp [mul_pow, I_sq]; ring,
                                                           Complex.cos_neg]
    simp only [fresnelC, primitive, segmentIntegral, sub_zero, zero_add]
    rw [he]
    ring
  · have he : (fun t : ℝ => sin (π*((t:ℂ)*(I*z))^2/2)) =
        (fun t : ℝ => -sin (π*((t:ℂ)*z)^2/2)) := by
      funext t
      rw [show π*((t:ℂ)*(I*z))^2/2=-(π*((t:ℂ)*z)^2/2) by simp [mul_pow, I_sq]; ring,
                                                           Complex.sin_neg]
    simp only [fresnelS, primitive, segmentIntegral, sub_zero, zero_add]
    rw [he, intervalIntegral.integral_neg]
    ring

/-- Identity under the stated parameter and domain assumptions: `fresnelAuxiliaryFComplex (I*z)=exp
(π*I/4-π*I*z^2/2)/Real.sqrt 2-I*fresnelAuxiliaryFComplex z ∧ fresnelAuxiliaryGComplex (I*z)=exp
(-π*I/4-π*I*z^2/2)/Real.sqrt 2+I*fresnelAuxiliaryGComplex z`. -/
@[dlmf 7.4.E7]
theorem FresnelAuxiliary.mul_I (z : ℂ) :
    fresnelAuxiliaryFComplex (I*z)=exp (π*I/4-π*I*z^2/2)/Real.sqrt 2-I*fresnelAuxiliaryFComplex z ∧
        fresnelAuxiliaryGComplex (I*z)=exp (-π*I/4-π*I*z^2/2)/Real.sqrt
            2+I*fresnelAuxiliaryGComplex z := by
  have hc : cos ((π:ℂ)/4)=(Real.sqrt 2:ℂ)/2 := by exact_mod_cast Real.cos_pi_div_four
  have hs : sin ((π:ℂ)/4)=(Real.sqrt 2:ℂ)/2 := by exact_mod_cast Real.sin_pi_div_four
  have hsq : (Real.sqrt 2:ℂ)^2=2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hs0 : (Real.sqrt 2:ℂ)≠0 := by exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne'
  have hp := fresnel_mul_I z
  have hE : exp (π*I/4-π*I*z^2/2)=(Real.sqrt 2:ℂ)/2*(1+I)*(cos (π*z^2/2)-I*sin (π*z^2/2)) := by
    rw [show (π:ℂ)*I/4-π*I*z^2/2=((π:ℂ)/4)*I+(-(π*z^2/2))*I by ring,
      Complex.exp_add,Complex.exp_mul_I,Complex.exp_mul_I,hc,hs,Complex.cos_neg,Complex.sin_neg]
    ring
  have hE' : exp (-π*I/4-π*I*z^2/2)=(Real.sqrt 2:ℂ)/2*(1-I)*(cos (π*z^2/2)-I*sin (π*z^2/2)) := by
    rw [show -(π:ℂ)*I/4-π*I*z^2/2=(-((π:ℂ)/4))*I+(-(π*z^2/2))*I by ring,
      Complex.exp_add,Complex.exp_mul_I,Complex.exp_mul_I,Complex.cos_neg,Complex.sin_neg,hc,hs]
    simp only [Complex.sin_neg,Complex.cos_neg]
    ring
  constructor <;> simp only [fresnelAuxiliaryFComplex,fresnelAuxiliaryGComplex]
  · rw [hp.1, hp.2, hE, show π*(I*z)^2/2= -(π*z^2/2) by simp [mul_pow, I_sq]; ring, Complex.cos_neg,
                                                          Complex.sin_neg]
    field_simp [hs0]
    ring_nf
    simp [I_sq]
    ring
  · rw [hp.1, hp.2, hE', show π*(I*z)^2/2= -(π*z^2/2) by simp [mul_pow, I_sq]; ring,
                                                           Complex.cos_neg, Complex.sin_neg]
    field_simp [hs0]
    ring_nf
    simp [I_sq]
    ring

/-- Identity under the stated parameter and domain assumptions:
`fresnelAuxiliaryFComplex (-z)=Real.sqrt 2*cos (π/4+π*z^2/2)-fresnelAuxiliaryFComplex z ∧
fresnelAuxiliaryGComplex (-z)=Real.sqrt 2*sin (π/4+π*z^2/2)-fresnelAuxiliaryGComplex z`. -/
@[dlmf 7.4.E8]
theorem FresnelAuxiliary.negative (z : ℂ) :
    fresnelAuxiliaryFComplex (-z)=Real.sqrt 2*cos (π/4+π*z^2/2)-fresnelAuxiliaryFComplex z ∧
        fresnelAuxiliaryGComplex (-z)=Real.sqrt 2*sin (π/4+π*z^2/2)-fresnelAuxiliaryGComplex z := by
  have hc : cos ((π:ℂ)/4)=(Real.sqrt 2:ℂ)/2 := by exact_mod_cast Real.cos_pi_div_four
  have hs : sin ((π:ℂ)/4)=(Real.sqrt 2:ℂ)/2 := by exact_mod_cast Real.sin_pi_div_four
  have hsq : (Real.sqrt 2:ℂ)^2=2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hp := fresnel_negative z
  constructor <;> simp only [fresnelAuxiliaryFComplex,fresnelAuxiliaryGComplex]
  · rw [hp.1,hp.2,neg_sq,Complex.cos_add,hc,hs]
    ring_nf
    simp [hsq]
    ring
  · rw [hp.1,hp.2,neg_sq,Complex.sin_add,hc,hs]
    ring_nf
    simp [hsq]
    ring

/-- Identity under the stated parameter and domain assumptions: `dawsonF z = I*Real.sqrt π/2*(exp
(-z^2)-faddeevaW z) ∧ dawsonF z = -I*Real.sqrt π/2*exp (-z^2)*erf (I*z)`. -/
@[dlmf 7.5.E1]
theorem dawsonF_faddeeva (z : ℂ) :
    dawsonF z = I*Real.sqrt π/2*(exp (-z^2)-faddeevaW z) ∧ dawsonF z =
        -I*Real.sqrt π/2*exp (-z^2)*erf (I*z) := by
  have he : erf (I*z)=2/Real.sqrt π*I*primitive (fun t => exp (t^2)) z := by
    rw [erf_complex_segment_integral]
    simp only [primitive, segmentIntegral, sub_zero, zero_add]
    have harg (t : ℝ) : -((t:ℂ)*(I*z))^2=((t:ℂ)*z)^2 := by simp [mul_pow, I_sq]
    simp_rw [harg]
    ring
  have hπ : (Real.sqrt π:ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hD : dawsonF z = -I*Real.sqrt π/2*exp (-z^2)*erf (I*z) := by
    rw [he, dawsonF]
    field_simp
    simp [I_sq]
  refine ⟨?_,hD⟩
  rw [hD, faddeevaW, erfc]
  have hn : -I*z=-(I*z) := by ring
  rw [hn, erf_negative]
  ring

/-- Identity under the stated parameter and domain assumptions: `fresnelC z+I*fresnelS
z=(1+I)/2-fresnelTail z`. -/
@[dlmf 7.5.E2]
theorem fresnel_sum_tail (z : ℂ) :
    fresnelC z+I*fresnelS z=(1+I)/2-fresnelTail z := by
  unfold fresnelTail
  ring

/-- Identity under the stated parameter and domain assumptions: `fresnelC
z=1/2+fresnelAuxiliaryFComplex z*sin (π*z^2/2)-fresnelAuxiliaryGComplex z*cos (π*z^2/2)`. -/
@[dlmf 7.5.E3]
theorem fresnelC_aux (z : ℂ) :
    fresnelC z=1/2+fresnelAuxiliaryFComplex z*sin (π*z^2/2)-fresnelAuxiliaryGComplex z*cos
        (π*z^2/2) := by
  have h := Complex.sin_sq_add_cos_sq (π*z^2/2)
  unfold fresnelAuxiliaryFComplex fresnelAuxiliaryGComplex
  linear_combination -(fresnelC z-1/2)*h

/-- Identity under the stated parameter and domain assumptions: `fresnelS
z=1/2-fresnelAuxiliaryFComplex z*cos (π*z^2/2)-fresnelAuxiliaryGComplex z*sin (π*z^2/2)`. -/
@[dlmf 7.5.E4]
theorem fresnelS_aux (z : ℂ) :
    fresnelS z=1/2-fresnelAuxiliaryFComplex z*cos (π*z^2/2)-fresnelAuxiliaryGComplex z*sin
        (π*z^2/2) := by
  have h := Complex.sin_sq_add_cos_sq (π*z^2/2)
  unfold fresnelAuxiliaryFComplex fresnelAuxiliaryGComplex
  linear_combination -(fresnelS z-1/2)*h

/-- Identity under the stated parameter and domain assumptions: `exp
(ε*π*I*z^2/2)*(fresnelAuxiliaryGComplex z+ε*I*fresnelAuxiliaryFComplex z)=(1+ε*I)/2-(fresnelC
z+ε*I*fresnelS z)`. -/
@[dlmf 7.5.E6]
theorem fresnel_signed_tail (z : ℂ) {ε : ℝ} (hε : ε=1 ∨ ε = -1) :
    exp (ε*π*I*z^2/2)*(fresnelAuxiliaryGComplex z+ε*I*fresnelAuxiliaryFComplex
        z)=(1+ε*I)/2-(fresnelC
        z+ε*I*fresnelS z) := by
  have he : exp (ε*π*I*z^2/2)=cos (π*z^2/2)+ε*I*sin (π*z^2/2) := by
    rw [show (ε:ℂ)*π*I*z^2/2=(ε*(π*z^2/2))*I by ring, Complex.exp_mul_I]
    rcases hε with rfl | rfl <;> simp [mul_comm]
  have ht := Complex.sin_sq_add_cos_sq (π*z^2/2)
  rw [he]
  unfold fresnelAuxiliaryFComplex fresnelAuxiliaryGComplex
  rcases hε with rfl | rfl <;> norm_num
  · linear_combination (norm := ring_nf) (-(fresnelC z-1/2)-I*(fresnelS z-1/2))*ht
        <;> simp [I_sq]
  · linear_combination (norm := ring_nf) (-(fresnelC z-1/2)+I*(fresnelS z-1/2))*ht
        <;> simp [I_sq]

/-- Identity under the stated parameter and domain assumptions: `exp (-π*I*z^2/2)*fresnelTail
z=fresnelAuxiliaryGComplex z+I*fresnelAuxiliaryFComplex z`. -/
@[dlmf 7.5.E5]
theorem fresnelTail_aux (z : ℂ) :
    exp (-π*I*z^2/2)*fresnelTail z=fresnelAuxiliaryGComplex z+I*fresnelAuxiliaryFComplex z := by
  have h := fresnel_signed_tail z (ε:=1) (Or.inl rfl)
  simp only [Complex.ofReal_one, one_mul] at h
  rw [show -π*I*z^2/2=-(π*I*z^2/2) by ring, Complex.exp_neg, fresnelTail]
  have he : exp (-(π*I*z^2/2))*exp (π*I*z^2/2)=1 := by rw [← Complex.exp_add]; simp
  rw [← Complex.exp_neg]
  linear_combination -exp (-(π*I*z^2/2))*h +
      (fresnelAuxiliaryGComplex z+I*fresnelAuxiliaryFComplex z)*he

/-- Signed Fresnel-to-Gaussian change of variable. -/
@[dlmf 7.5.E7]
def fresnelZetaComplex (ε : ℝ) (z : ℂ) : ℂ :=
  Real.sqrt π/2*(1-ε*I)*z

/-- Identity under the stated parameter and domain assumptions: `fresnelC z+ε*I*fresnelS
z=(1+ε*I)/2*erf (fresnelZetaComplex ε z)`. -/
@[dlmf 7.5.E8]
theorem fresnel_signed_erf (z : ℂ) {ε : ℝ} (hε : ε=1 ∨ ε = -1) :
    fresnelC z+ε*I*fresnelS z=(1+ε*I)/2*erf (fresnelZetaComplex ε z) := by
  have hε2 : (ε:ℂ)^2=1 := by rcases hε with rfl | rfl <;> norm_num
  have hπ : (Real.sqrt π:ℂ)^2=π := by exact_mod_cast Real.sq_sqrt Real.pi_pos.le
  have hπ0 : (Real.sqrt π:ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  let α : ℂ := Real.sqrt π/2*(1-ε*I)
  let β : ℂ := (1+ε*I)/2
  have hα : ∀ w : ℂ, -(α*w)^2=ε*π*I*w^2/2 := by
    intro w
    dsimp [α]
    simp only [mul_pow, div_pow, sub_sq, I_sq]
    rw [hπ, hε2]
    ring
  have hβα : β*(2/Real.sqrt π)*α=1 := by
    dsimp [α,β]
    field_simp
    ring_nf
    rw [I_sq, hε2]
    norm_num
  have hE (w : ℂ) : cos (π*w^2/2)+ε*I*sin (π*w^2/2)=exp (ε*π*I*w^2/2) := by
    rcases hε with rfl | rfl
    · convert Complex.cos_add_sin_I (π*w^2/2) using 1 <;> push_cast <;> ring
    · have h := Complex.cos_add_sin_I (-(π*w^2/2))
      simp only [Complex.cos_neg, Complex.sin_neg] at h
      convert h using 1 <;> push_cast <;> ring
  have hd (w : ℂ) : HasDerivAt
      (fun w => fresnelC w+ε*I*fresnelS w-β*erf (α*w)) 0 w := by
    have hf := (hasDerivAt_fresnelC_complex w).add
      ((hasDerivAt_fresnelS_complex w).const_mul ((ε:ℂ)*I))
    have hg := ((hasDerivAt_erf_complex (α*w)).comp w
      ((hasDerivAt_id w).const_mul α)).const_mul β
    refine ((hf.sub hg).congr_of_eventuallyEq (Eventually.of_forall fun w => rfl)).congr_deriv ?_
    rw [hα, hE]
    linear_combination -exp (ε*π*I*w^2/2)*hβα
  have he := is_const_of_deriv_eq_zero (fun w => (hd w).differentiableAt)
      (fun w => (hd w).deriv) z 0
  have he' : fresnelC z+ε*I*fresnelS z-β*erf (α*z)=0 := by
    simpa [fresnelC,fresnelS,erf_zero,primitive_zero] using he
  change fresnelC z+ε*I*fresnelS z=β*erf (α*z)
  linear_combination he'

/-- Identity under the stated parameter and domain assumptions: `fresnelC z+ε*I*fresnelS
z=(1+ε*I)/2*(1-exp (ε*π*I*z^2/2)*faddeevaW (I*fresnelZetaComplex ε z))`. -/
@[dlmf 7.5.E9]
theorem fresnel_signed_faddeeva (z : ℂ) {ε : ℝ} (hε : ε=1 ∨ ε = -1) :
    fresnelC z+ε*I*fresnelS
        z=(1+ε*I)/2*(1-exp (ε*π*I*z^2/2)*faddeevaW (I*fresnelZetaComplex ε z)) := by
  rw [fresnel_signed_erf z hε]
  have hz : (fresnelZetaComplex ε z)^2 = -ε*π*I*z^2/2 := by
    unfold fresnelZetaComplex
    rw [mul_pow, mul_pow, div_pow,
        show (Real.sqrt π:ℂ)^2=π by exact_mod_cast Real.sq_sqrt Real.pi_pos.le]
    simp only [sub_sq, mul_pow, I_sq]
    rcases hε with rfl | rfl <;> norm_num <;> ring
  unfold faddeevaW
  rw [show -I*(I*fresnelZetaComplex ε z)=fresnelZetaComplex ε z by ring_nf; simp,
    mul_pow, I_sq, hz]
  have he : exp (ε*π*I*z^2/2)*exp (-(-1*(-ε*π*I*z^2/2)))=1 := by
    rw [← Complex.exp_add]; convert Complex.exp_zero using 1 <;> ring
  unfold erfc
  rw [← mul_assoc, he, one_mul]
  ring

/-- Identity under the stated parameter and domain assumptions: `fresnelAuxiliaryGComplex
z+ε*I*fresnelAuxiliaryFComplex z=(1+ε*I)/2*exp ((fresnelZetaComplex ε z)^2)*erfc (fresnelZetaComplex
ε z)`. -/
@[dlmf 7.5.E10]
theorem FresnelAuxiliary.signed_erfc (z : ℂ) {ε : ℝ} (hε : ε=1 ∨ ε = -1) :
    fresnelAuxiliaryGComplex z+ε*I*fresnelAuxiliaryFComplex z=(1+ε*I)/2*exp
        ((fresnelZetaComplex ε z)^2)*erfc
        (fresnelZetaComplex ε z) := by
  have h := fresnel_signed_tail z hε
  rw [fresnel_signed_erf z hε] at h
  have hz : (fresnelZetaComplex ε z)^2 = -(ε*π*I*z^2/2) := by
    unfold fresnelZetaComplex
    rw [mul_pow, mul_pow, div_pow,
        show (Real.sqrt π:ℂ)^2=π by exact_mod_cast Real.sq_sqrt Real.pi_pos.le]
    simp only [sub_sq, mul_pow, I_sq]
    rcases hε with rfl | rfl <;> norm_num <;> ring
  rw [hz, Complex.exp_neg]
  unfold erfc
  have hE := Complex.exp_ne_zero (ε*π*I*z^2/2)
  generalize exp (ε*π*I*z^2/2)=E at h hE ⊢
  field_simp [hE]
  linear_combination 2*h

/-- Rotation of the Fresnel tail preserves its squared norm on the whole real axis. -/
theorem fresnelTail_norm_sq_real (x : ℝ) :
    ‖fresnelTail x‖^2=fresnelAuxiliaryF x^2+fresnelAuxiliaryG x^2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [fresnelTail, fresnelC_ofReal, fresnelS_ofReal]
  simp only [sub_re, sub_im, div_ofNat_re, div_ofNat_im, add_re, add_im,
    one_re, one_im, I_re, I_im, ofReal_re, ofReal_im, mul_re, mul_im]
  unfold fresnelAuxiliaryF fresnelAuxiliaryG
  have h := Real.sin_sq_add_cos_sq (π*x^2/2)
  linear_combination -((1/2-Real.fresnelS x)^2+(1/2-Real.fresnelC x)^2)*h

/-- Identity under the stated parameter and domain assumptions:
`‖fresnelTail x‖^2 = fresnelAuxiliaryF x^2+fresnelAuxiliaryG x^2`. -/
@[dlmf 7.5.E11]
theorem fresnelTail_norm_sq_nonneg {x : ℝ} :
    ‖fresnelTail x‖^2 = fresnelAuxiliaryF x^2+fresnelAuxiliaryG x^2 := by
  exact fresnelTail_norm_sq_real x

/-- Identity under the stated parameter and domain assumptions:
`‖fresnelTail x‖^2 = 2+fresnelAuxiliaryF (-x)^2+fresnelAuxiliaryG (-x)^2-2*Real.sqrt 2*Real.cos
(π/4+π*x^2/2)*fresnelAuxiliaryF (-x)-2*Real.sqrt 2*Real.cos (π/4-π*x^2/2)*fresnelAuxiliaryG
(-x)`. -/
@[dlmf 7.5.E12]
theorem fresnelTail_norm_sq_nonpos {x : ℝ} :
    ‖fresnelTail x‖^2 = 2+fresnelAuxiliaryF (-x)^2+fresnelAuxiliaryG (-x)^2-2*Real.sqrt 2*Real.cos
        (π/4+π*x^2/2)*fresnelAuxiliaryF (-x)-2*Real.sqrt 2*Real.cos
            (π/4-π*x^2/2)*fresnelAuxiliaryG (-x) := by
  have h := FresnelAuxiliary.negative ((-x:ℝ):ℂ)
  rw [fresnelAuxiliaryFComplex_ofReal (-x), fresnelAuxiliaryGComplex_ofReal (-x)] at h
  have hF : fresnelAuxiliaryF x=Real.sqrt 2*Real.cos (π/4+π*x^2/2)-fresnelAuxiliaryF (-x) := by
    apply Complex.ofReal_injective
    push_cast
    simpa only [← ofReal_neg, fresnelAuxiliaryFComplex_ofReal, neg_neg, ofReal_neg,
      neg_sq, ← ofReal_pow, ← ofReal_div, ← ofReal_mul, ← ofReal_add,
      Complex.ofReal_cos, Complex.ofReal_ofNat] using h.1
  have hG : fresnelAuxiliaryG x=Real.sqrt 2*Real.sin (π/4+π*x^2/2)-fresnelAuxiliaryG (-x) := by
    apply Complex.ofReal_injective
    push_cast
    simpa only [← ofReal_neg, fresnelAuxiliaryGComplex_ofReal, neg_neg, ofReal_neg,
      neg_sq, ← ofReal_pow, ← ofReal_div, ← ofReal_mul, ← ofReal_add,
      Complex.ofReal_sin, Complex.ofReal_ofNat] using h.2
  rw [fresnelTail_norm_sq_real, hF, hG]
  have hs : Real.sin (π/4+π*x^2/2)=Real.cos (π/4-π*x^2/2) := by
    rw [Real.sin_add, Real.cos_sub, Real.sin_pi_div_four, Real.cos_pi_div_four]
  rw [← hs]
  have ht := Real.sin_sq_add_cos_sq (π/4+π*x^2/2)
  have htwo := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  nlinarith [ht]

/- The relation `goodwinStatonG_dawson` (DLMF 7.5.13) is proved in
`DLMF.ErrorFunctions.Integrals`, alongside the Gaussian Cauchy integral it uses. -/

/-- Identity under the stated parameter and domain assumptions: `iteratedDeriv (n+1) erf z = (-1 :
ℂ)^n*2/Real.sqrt π*hermitePolynomialHEval n z*exp (-z^2)`. -/
@[dlmf 7.10.E1]
theorem iteratedDeriv_erf_hermite (n : ℕ) (z : ℂ) :
    iteratedDeriv (n+1) erf z = (-1 : ℂ)^n*2/Real.sqrt π*hermitePolynomialHEval n z*exp (-z^2) := by
  have hd : deriv erf=(fun t : ℂ => (2/(Real.sqrt π:ℂ))*exp (-t^2)) :=
    funext fun t => (hasDerivAt_erf_complex t).deriv
  rw [iteratedDeriv_succ',hd,iteratedDeriv_const_mul_field,
    DLMF.OrthogonalPolynomials.iteratedDeriv_cexp_neg_sq,hermitePolynomialHEval_eq_aeval]
  ring

/-- At `z`, the function `faddeevaW` has derivative `(-2*z*faddeevaW z+2*I/Real.sqrt π)`. -/
@[dlmf 7.10.E2]
theorem hasDerivAt_faddeevaW (z : ℂ) :
    HasDerivAt faddeevaW (-2*z*faddeevaW z+2*I/Real.sqrt π) z := by
  have hE : HasDerivAt erfc (-(2/Real.sqrt π*exp (-(-I*z)^2))) (-I*z) := by
    change HasDerivAt (fun w => 1-erf w) _ _
    exact (hasDerivAt_erf_complex (-I*z)).const_sub 1
  have hC := hE.comp z ((hasDerivAt_id z).const_mul (-I))
  have h := (((hasDerivAt_pow 2 z).neg).cexp).mul hC
  change HasDerivAt (fun w => exp (-w^2)*erfc (-I*w)) _ z
  refine h.congr_deriv ?_
  simp only [Pi.neg_apply, Function.comp_apply, id_eq, faddeevaW]
  have he : exp (-z^2)*exp (-(-I*z)^2)=1 := by
    rw [← Complex.exp_add]
    congr 1
    simp [mul_pow, I_sq]
  have harg : -(-I*z)^2=z^2 := by simp [mul_pow, I_sq]
  rw [harg] at he ⊢
  field_simp
  linear_combination 2*I*he

/-- Identity under the stated parameter and domain assumptions: `iteratedDeriv (n+2) faddeevaW
z+2*z*iteratedDeriv (n+1) faddeevaW z+2*(n+1)*iteratedDeriv n faddeevaW z=0`. -/
@[dlmf 7.10.E3]
theorem iteratedDeriv_faddeevaW_recurrence (n : ℕ) (z : ℂ) :
    iteratedDeriv (n+2) faddeevaW z+2*z*iteratedDeriv (n+1) faddeevaW z+2*(n+1)*iteratedDeriv n
        faddeevaW z=0 := by
  have hcd : ContDiff ℂ ⊤ faddeevaW :=
    contDiffOn_univ.mp (faddeevaW_entire.differentiableOn.contDiffOn isOpen_univ)
  have hd (k : ℕ) (w : ℂ) : HasDerivAt (iteratedDeriv k faddeevaW)
      (iteratedDeriv (k+1) faddeevaW w) w := by
    rw [iteratedDeriv_succ]
    exact (hcd.differentiable_iteratedDeriv k (by simp) w).hasDerivAt
  have hbase (w : ℂ) : iteratedDeriv 2 faddeevaW w+
      2*w*iteratedDeriv 1 faddeevaW w+2*faddeevaW w=0 := by
    have he : deriv faddeevaW=(fun t => -2*t*faddeevaW t+2*I/Real.sqrt π) :=
      funext fun t => (hasDerivAt_faddeevaW t).deriv
    have h := (((hasDerivAt_id w).const_mul (-2)).mul (hd 0 w)).add_const (2*I/Real.sqrt π)
    have h' : HasDerivAt (fun t => -2*t*faddeevaW t+2*I/Real.sqrt π) _ w :=
      h.congr_of_eventuallyEq (Eventually.of_forall fun t => rfl)
    rw [iteratedDeriv_succ,iteratedDeriv_one,he,h'.deriv]
    simp only [id_eq,mul_one,iteratedDeriv_zero]
    rw [iteratedDeriv_one,he]
    ring
  induction n generalizing z with
  | zero => simpa using hbase z
  | succ n ih =>
    have h := ((hd (n+2) z).add
      (((hasDerivAt_id z).const_mul 2).mul (hd (n+1) z))).add ((hd n z).const_mul (2*(n+1:ℂ)))
    have h' : HasDerivAt (fun w => iteratedDeriv (n+2) faddeevaW w+
        2*w*iteratedDeriv (n+1) faddeevaW w+2*(n+1:ℂ)*iteratedDeriv n faddeevaW w) _ z :=
      h.congr_of_eventuallyEq (Eventually.of_forall fun t => rfl)
    have he : (fun w => iteratedDeriv (n+2) faddeevaW w+
        2*w*iteratedDeriv (n+1) faddeevaW w+2*(n+1:ℂ)*iteratedDeriv n faddeevaW w)=(fun _ => 0) :=
      funext ih
    rw [he] at h'
    have hh := h'.unique (hasDerivAt_const z (0:ℂ))
    push_cast
    simp only [id_eq,mul_one] at hh
    linear_combination hh

/-- Derivative formula at the specified argument: `HasDerivAt fresnelAuxiliaryFComplex
(-π*z*fresnelAuxiliaryGComplex z) z ∧ HasDerivAt fresnelAuxiliaryGComplex
(π*z*fresnelAuxiliaryFComplex z-1) z`. -/
@[dlmf 7.10.E4]
theorem hasDerivAt_fresnelAux (z : ℂ) :
    HasDerivAt fresnelAuxiliaryFComplex (-π*z*fresnelAuxiliaryGComplex z) z ∧
        HasDerivAt fresnelAuxiliaryGComplex (π*z*fresnelAuxiliaryFComplex z-1) z := by
  have hC := hasDerivAt_fresnelC_complex z
  have hS := hasDerivAt_fresnelS_complex z
  have ht : HasDerivAt (fun w : ℂ => π*w^2/2) (π*z) z := by
    convert ((hasDerivAt_pow 2 z).const_mul (π:ℂ)).div_const 2 using 1 <;> ring
  have hc := ht.ccos
  have hs := ht.csin
  have hid := Complex.sin_sq_add_cos_sq (π*z^2/2)
  constructor
  · change HasDerivAt (fun w => (1/2-fresnelS w)*cos (π*w^2/2)-
        (1/2-fresnelC w)*sin (π*w^2/2)) _ z
    convert (((hS.const_sub (1/2)).mul hc).sub ((hC.const_sub (1/2)).mul hs)) using 1
    simp only [fresnelAuxiliaryGComplex]
    ring
  · change HasDerivAt (fun w => (1/2-fresnelC w)*cos (π*w^2/2)+
        (1/2-fresnelS w)*sin (π*w^2/2)) _ z
    convert (((hC.const_sub (1/2)).mul hc).add ((hS.const_sub (1/2)).mul hs)) using 1
    simp only [fresnelAuxiliaryFComplex]
    linear_combination hid

/-- Identity under the stated parameter and domain assumptions: `erfc z=exp (-z^2)/Real.sqrt
π*kummerU (1/2) (1/2) (z^2) ∧ erfc z=z/Real.sqrt π*exp (-z^2)*kummerU 1 (3/2) (z^2)`. -/
@[dlmf 7.11.E5]
theorem erfc_kummerU_pair {z : ℂ} (hz : 0 < z.re) :
    erfc z=exp (-z^2)/Real.sqrt π*kummerU (1/2) (1/2) (z^2) ∧
        erfc z=z/Real.sqrt π*exp (-z^2)*kummerU 1 (3/2) (z^2) := by
  have hs : z∈slitPlane := Or.inl hz
  have hz0 := slitPlane_ne_zero hs
  have hp0 : (Real.sqrt π:ℂ)≠0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hu := kummerU_erfc hs hz
  constructor
  · rw [hu, ← mul_assoc, ← mul_assoc, show exp (-z^2)/Real.sqrt π*(Real.sqrt π:ℂ)*exp (z^2)=1 by
      field_simp; rw [← Complex.exp_add]; simp]
    simp
  · rw [kummerU_kummer_transform_all 1 (3/2) (pow_ne_zero 2 hz0)]
    norm_num
    rw [sq_cpow_of_re_pos hz, show (2:ℂ)*(-(1/2)) = -1 by ring, cpow_neg_one, hu]
    have he : exp (-z^2)*exp (z^2)=1 := by rw [← Complex.exp_add]; simp
    field_simp
    linear_combination -erfc z*he

/-- Identity under the stated parameter and domain assumptions: `erfc z=upperIncompleteGamma (1/2)
(z^2)/Real.sqrt π`. -/
@[dlmf 7.11.E2]
theorem erfc_upperIncompleteGamma {z : ℂ} (hz : 0 < z.re) :
    erfc z=upperIncompleteGamma (1/2) (z^2)/Real.sqrt π := by
  have h := (erfc_kummerU_pair hz).1
  rw [upperIncompleteGamma,show (1:ℂ)-1/2=1/2 by norm_num]
  linear_combination h

/-- Identity under the stated parameter and domain assumptions: `erf z=lowerIncompleteGamma (1/2)
(z^2)/Real.sqrt π`. -/
@[dlmf 7.11.E1]
theorem erf_lowerIncompleteGamma {z : ℂ} (hz : 0 < z.re) :
    erf z=lowerIncompleteGamma (1/2) (z^2)/Real.sqrt π := by
  have hz0 : z≠0 := ne_zero_of_re_pos hz
  have h := lowerIncompleteGamma_add_upperIncompleteGamma (a:=1/2)
      Complex.one_div_two_ne_neg_natCast
      (pow_ne_zero 2 hz0)
  rw [Complex.Gamma_one_half_eq_sqrt] at h
  have hu := erfc_upperIncompleteGamma hz
  unfold erfc at hu
  have hp0 : (Real.sqrt π:ℂ)≠0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  field_simp [hp0] at hu ⊢
  linear_combination -h-hu

/-- Identity under the stated parameter and domain assumptions: `erfc z=z/Real.sqrt π*expIntegralE
(1/2) (z^2)`. -/
@[dlmf 7.11.E3]
theorem erfc_expIntegralE {z : ℂ} (hz : 0 < z.re) :
    erfc z=z/Real.sqrt π*expIntegralE (1/2) (z^2) := by
  rw [erfc_upperIncompleteGamma hz,expIntegralE]
  norm_num only [show (1/2:ℂ)-1= -1/2 by ring,show (1:ℂ)-1/2=1/2 by ring]
  rw [sq_cpow_of_re_pos hz,show (2:ℂ)*(-(1/2))= -1 by ring,cpow_neg_one]
  field_simp [ne_zero_of_re_pos hz]

/-- Identity under the stated parameter and domain assumptions: `erf z=2*z/Real.sqrt π*kummerM
(1/2) (3/2) (-z^2) ∧ erf z=2*z/Real.sqrt π*exp (-z^2)*kummerM 1 (3/2) (z^2)`. -/
@[dlmf 7.11.E4]
theorem erf_kummerM_pair (z : ℂ) :
    erf z=2*z/Real.sqrt π*kummerM (1/2) (3/2) (-z^2) ∧
        erf z=2*z/Real.sqrt π*exp (-z^2)*kummerM 1 (3/2) (z^2) := by
  constructor
  · unfold erf
    ring
  · rw [erf, kummerM_kummer_transform Complex.three_div_two_ne_neg_natCast]
    norm_num
    ring

/-- Identity under the stated parameter and domain assumptions: `fresnelC z+I*fresnelS
z=z*kummerM (1/2) (3/2) (π*I*z^2/2) ∧ fresnelC z+I*fresnelS z=z*exp
(π*I*z^2/2)*kummerM 1 (3/2) (-π*I*z^2/2)`. -/
@[dlmf 7.11.E6]
theorem fresnel_kummerM_pair (z : ℂ) :
    fresnelC z+I*fresnelS z=z*kummerM (1/2) (3/2) (π*I*z^2/2) ∧
        fresnelC z+I*fresnelS z=z*exp (π*I*z^2/2)*kummerM 1 (3/2) (-π*I*z^2/2) := by
  have h := fresnel_signed_erf z (ε:=1) (Or.inl rfl)
  simp only [Complex.ofReal_one,one_mul] at h
  have hzeta : -(fresnelZetaComplex 1 z)^2=π*I*z^2/2 := by
    unfold fresnelZetaComplex
    simp only [Complex.ofReal_one,one_mul,mul_pow,div_pow,sub_sq,I_sq]
    rw [show (Real.sqrt π:ℂ)^2=π by exact_mod_cast Real.sq_sqrt Real.pi_pos.le]
    ring
  have hcoef : (1+I)/2*(2*fresnelZetaComplex 1 z/(Real.sqrt π:ℂ))=z := by
    unfold fresnelZetaComplex
    simp only [Complex.ofReal_one,one_mul]
    have hp0 : (Real.sqrt π:ℂ)≠0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
    field_simp
    ring_nf
    simp [I_sq]
    ring
  rw [(erf_kummerM_pair _).1,hzeta,←mul_assoc,hcoef] at h
  refine ⟨h,?_⟩
  rw [h,kummerM_kummer_transform Complex.three_div_two_ne_neg_natCast]
  norm_num
  ring

/-- The adjacent upper/lower Gamma ratio in a 1F2 coefficient, on the positive parameter
half-planes. -/
lemma regularized1F2_gamma_coeff {a c : ℂ} (ha : 0<a.re) (hc : 0<c.re) (n : ℕ) :
    Gamma (a+1)*Gamma c*regularizedHGFunCoeff {a} {a+1,c} n=
      a*Gamma c/((a+n)*(n.factorial:ℂ)*Gamma (c+n)) := by
  have hna : ∀ k : ℕ, a≠-k := by
    intro k he; have h := congrArg Complex.re he; simp at h
    linarith [show (0:ℝ)≤k by positivity]
  have han : 0<(a+n).re := by simp; linarith [show (0:ℝ)≤n by positivity]
  have hcn : 0<(c+n).re := by simp; linarith [show (0:ℝ)≤n by positivity]
  have han0 : a+n≠0 := by intro h; rw [h] at han; simpa using han
  have ha0 : a≠0 := by intro h; rw [h] at ha; simpa using ha
  simp only [regularizedHGFunCoeff,Multiset.map_singleton,Multiset.prod_singleton,
    Multiset.insert_eq_cons,Multiset.map_cons,Multiset.prod_cons]
  rw [← pochhammer,pochhammer,← Gamma_add_nat_div_Gamma_eq a hna,
    show a+1+n=(a+n)+1 by ring,Gamma_add_one _ han0,Gamma_add_one _ ha0]
  field_simp [Gamma_ne_zero_of_re_pos ha,Gamma_ne_zero_of_re_pos han,
    Gamma_ne_zero_of_re_pos hcn]

/-- The two elementary Gamma coefficient reductions for the Fresnel 1F2 series. -/
theorem fresnel_gamma_coeff (n : ℕ) :
    Gamma (5/4)*Gamma (1/2)*regularizedHGFunCoeff {1/4} {5/4,1/2} n=
      (4:ℂ)^n/((4*n+1)*(2*n).factorial) ∧
    Gamma (7/4)*Gamma (3/2)*regularizedHGFunCoeff {3/4} {7/4,3/2} n=
      3*(4:ℂ)^n/((4*n+3)*(2*n+1).factorial) := by
  have hG : Gamma (1/2:ℂ)≠0 := Gamma_ne_zero_of_re_pos (by norm_num)
  have hn : (n.factorial:ℂ)≠0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have h2n : ((2*n).factorial:ℂ)≠0 := Nat.cast_ne_zero.mpr (2*n).factorial_ne_zero
  have h2n1 : ((2*n+1).factorial:ℂ)≠0 := Nat.cast_ne_zero.mpr (2*n+1).factorial_ne_zero
  constructor
  · rw [show (5/4:ℂ)=1/4+1 by ring,regularized1F2_gamma_coeff (by norm_num) (by norm_num),
      DLMF.Bessel.Gamma_nat_add_half]
    field_simp [hG,hn,h2n]
    ring
  · rw [show (7/4:ℂ)=3/4+1 by ring,regularized1F2_gamma_coeff (by norm_num) (by norm_num),
      DLMF.Bessel.Gamma_nat_add_three_halves,DLMF.Bessel.Gamma_three_halves]
    field_simp [hG,hn,h2n1]
    ring

/-- Identity under the stated parameter and domain assumptions: `fresnelC z=z*Gamma
(5/4)*Gamma (1/2)*regularizedHGFun {1/4} {5/4,1/2} (-π^2*z^4/16)`. -/
@[dlmf 7.11.E7]
theorem fresnelC_hypergeometric (z : ℂ) :
    fresnelC z=z*Gamma (5/4)*Gamma (1/2)*regularizedHGFun {1/4} {5/4,1/2} (-π^2*z^4/16) := by
  apply (fresnelC_hasSum z).unique
  have hs := (hasSum_regularized1F2 (1/4) (5/4) (1/2) (-π^2*z^4/16)).mul_left
    (z*Gamma (5/4)*Gamma (1/2))
  refine hs.congr_fun fun n=>?_
  symm
  calc
    (z*Gamma (5/4)*Gamma (1/2))*
        (regularizedHGFunCoeff {1/4} {5/4,1/2} n*(-π^2*z^4/16)^n) =
      z*(Gamma (5/4)*Gamma (1/2)*
        regularizedHGFunCoeff {1/4} {5/4,1/2} n)*(-π^2*z^4/16)^n := by ring
    _ = _ := by
      rw [(fresnel_gamma_coeff n).1]
      have hscale : (4:ℂ)^n*(-π^2*z^4/16)^n=
          (-1)^n*(π/2)^(2*n)*z^(4*n) := by
        rw [← mul_pow,show (4:ℂ)*(-π^2*z^4/16)= -((π/2)*z^2)^2 by ring,
          neg_pow,← pow_mul,mul_pow,← pow_mul]
        ring
      simp only [Nat.add_zero]
      linear_combination (norm := (simp only [div_eq_mul_inv, mul_inv_rev]; ring))
          (z/((4*n+1)*(2*n).factorial))*hscale

/-- Identity under the stated parameter and domain assumptions: `fresnelS z=π*z^3/6*Gamma
(7/4)*Gamma (3/2)*regularizedHGFun {3/4} {7/4,3/2} (-π^2*z^4/16)`. -/
@[dlmf 7.11.E8]
theorem fresnelS_hypergeometric (z : ℂ) :
    fresnelS z=π*z^3/6*Gamma (7/4)*Gamma (3/2)*regularizedHGFun {3/4} {7/4, 3/2}
        (-π^2*z^4/16) := by
  apply (fresnelS_hasSum z).unique
  have hs := (hasSum_regularized1F2 (3/4) (7/4) (3/2) (-π^2*z^4/16)).mul_left
    (π*z^3/6*Gamma (7/4)*Gamma (3/2))
  refine hs.congr_fun fun n=>?_
  symm
  calc
    (π*z^3/6*Gamma (7/4)*Gamma (3/2))*
        (regularizedHGFunCoeff {3/4} {7/4,3/2} n*(-π^2*z^4/16)^n) =
      π*z^3/6*(Gamma (7/4)*Gamma (3/2)*
        regularizedHGFunCoeff {3/4} {7/4,3/2} n)*(-π^2*z^4/16)^n := by ring
    _ = _ := by
      rw [(fresnel_gamma_coeff n).2]
      have hscale : (4:ℂ)^n*(-π^2*z^4/16)^n=
          (-1)^n*(π/2)^(2*n)*z^(4*n) := by
        rw [← mul_pow,show (4:ℂ)*(-π^2*z^4/16)= -((π/2)*z^2)^2 by ring,
          neg_pow,← pow_mul,mul_pow,← pow_mul]
        ring
      linear_combination (norm := (simp only [div_eq_mul_inv, mul_inv_rev]; ring))
          (π*z^3/(2*((4*n+3)*(2*n+1).factorial)))*hscale

end DLMF.Confluent
