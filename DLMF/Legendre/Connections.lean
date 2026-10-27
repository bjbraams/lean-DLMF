/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.Associated
public import DLMF.Legendre.Laplace

/-!
# Ferrers and associated Legendre connection formulas

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Legendre

/-- ferrers connection 1. -/
@[dlmf 14.9.E1]
theorem ferrers_connection_1 (ν μ : ℂ) (hplus : LegendreQRegular ν μ) (hminus : LegendreQRegular ν (-μ)) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    π*sin (μ*π)/(2*Gamma (ν-μ+1))*ferrersP ν (-μ) x=-ferrersQ ν μ x/Gamma (ν+μ+1)+cos (μ*π)/Gamma (ν-μ+1)*ferrersQ ν (-μ) x := by
  obtain ⟨hg1, hg2⟩ := legendre_Gamma_half_ne_zero hplus
  obtain ⟨hh1, hh2⟩ := legendre_Gamma_half_ne_zero_neg hminus
  have pyth := sin_sq_add_cos_sq ((ν+μ)*π/2)
  have pytha := sin_sq_add_cos_sq ((ν-μ)*π/2)
  have hs : (Real.sqrt π:ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hT : (2:ℂ)^μ ≠ 0 := by simp
  have hN : (2:ℂ)^ν ≠ 0 := by simp
  have hP : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [ferrersP_neg_regular hminus hx, ferrersQ_even_odd, ferrersQ_neg_even_odd ν μ hx,
    legendre_Gamma_plus, legendre_Gamma_minus, cpow_neg]
  have hμπ : μ*π = (ν+μ)*π/2 - (ν-μ)*π/2 := by ring
  rw [hμπ, sin_sub, cos_sub]
  generalize ferrersEven ν μ x = E
  generalize ferrersOdd ν μ x = O
  generalize Gamma ((ν+μ+1)/2) = g1 at hg1
  generalize Gamma ((ν+μ+2)/2) = g2 at hg2
  generalize Gamma ((ν-μ+1)/2) = h1 at hh1
  generalize Gamma ((ν-μ+2)/2) = h2 at hh2
  generalize (2:ℂ)^μ = T at hT
  generalize (2:ℂ)^ν = N at hN
  generalize sin ((ν+μ)*π/2) = sb at pyth
  generalize cos ((ν+μ)*π/2) = cb at pyth
  generalize sin ((ν-μ)*π/2) = sa at pytha
  generalize cos ((ν-μ)*π/2) = ca at pytha
  generalize (Real.sqrt π:ℂ) = S at hs
  generalize (π:ℂ) = P at hP
  field_simp
  linear_combination (sb*h1*E*g1-cb*h2*g2*O)*pytha

/-- ferrers connection 2. -/
@[dlmf 14.9.E2]
theorem ferrers_connection_2 (ν μ : ℂ) (hplus : LegendreQRegular ν μ) (hminus : LegendreQRegular ν (-μ)) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    2*sin (μ*π)/(π*Gamma (ν-μ+1))*ferrersQ ν (-μ) x=ferrersP ν μ x/Gamma (ν+μ+1)-cos (μ*π)/Gamma (ν-μ+1)*ferrersP ν (-μ) x := by
  obtain ⟨hg1, hg2⟩ := legendre_Gamma_half_ne_zero hplus
  obtain ⟨hh1, hh2⟩ := legendre_Gamma_half_ne_zero_neg hminus
  have pyth := sin_sq_add_cos_sq ((ν+μ)*π/2)
  have pytha := sin_sq_add_cos_sq ((ν-μ)*π/2)
  have hs : (Real.sqrt π:ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hT : (2:ℂ)^μ ≠ 0 := by simp
  have hN : (2:ℂ)^ν ≠ 0 := by simp
  have hP : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [ferrersP_neg_regular hminus hx, ferrersP_regular hplus hx, ferrersQ_neg_even_odd ν μ hx,
    legendre_Gamma_plus, legendre_Gamma_minus, cpow_neg]
  rw [show μ*π = (ν+μ)*π/2 - (ν-μ)*π/2 by ring, sin_sub, cos_sub]
  generalize ferrersEven ν μ x = E
  generalize ferrersOdd ν μ x = O
  generalize Gamma ((ν+μ+1)/2) = g1 at hg1
  generalize Gamma ((ν+μ+2)/2) = g2 at hg2
  generalize Gamma ((ν-μ+1)/2) = h1 at hh1
  generalize Gamma ((ν-μ+2)/2) = h2 at hh2
  generalize (2:ℂ)^μ = T at hT
  generalize (2:ℂ)^ν = N at hN
  generalize sin ((ν+μ)*π/2) = sb at pyth
  generalize cos ((ν+μ)*π/2) = cb at pyth
  generalize sin ((ν-μ)*π/2) = sa at pytha
  generalize cos ((ν-μ)*π/2) = ca at pytha
  generalize (Real.sqrt π:ℂ) = S at hs
  generalize (π:ℂ) = P at hP
  field_simp
  linear_combination (sb*h2*g2*O + cb*h1*E*g1)*pytha

/-- ferrers connection 5. -/
@[dlmf 14.9.E5]
theorem ferrers_connection_5 (ν μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersP (-ν-1) μ x=ferrersP ν μ x := by
  have hp : 1+(x:ℂ) ∈ slitPlane := Or.inl (by simp; linarith [hx.1])
  unfold ferrersP
  rw [show -(-ν-1)=ν+1 by ring, show -ν-1+1 = -ν by ring,
    regularizedGaussHG_symm _ _ _ (mem_cutPlane_of_one_add hp)]

/-- ferrers connection 6. -/
@[dlmf 14.9.E6]
theorem ferrers_connection_6 (ν μ : ℂ) (hplus : LegendreQRegular ν μ) (hminus : LegendreQRegular ν (-μ)) (hother : LegendreQRegular (-ν-1) μ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    π*cos (ν*π)*cos (μ*π)*ferrersP ν μ x=sin ((ν+μ)*π)*ferrersQ ν μ x-sin ((ν-μ)*π)*ferrersQ (-ν-1) μ x := by
  obtain ⟨hg1, hg2⟩ := legendre_Gamma_half_ne_zero hplus
  obtain ⟨hh1, hh2⟩ := legendre_Gamma_half_ne_zero_neg hminus
  obtain ⟨hk1, hk2⟩ := legendre_Gamma_half_ne_zero hother
  rw [show (-ν-1+μ+1)/2 = (μ-ν)/2 by ring] at hk1
  rw [show (-ν-1+μ+2)/2 = (1-ν+μ)/2 by ring] at hk2
  obtain ⟨hA, hB⟩ := legendre_reflection_recip hplus
  obtain ⟨-, -, e2, o2⟩ := legendre_reflections ν μ
  have pyth := sin_sq_add_cos_sq ((ν+μ)*π/2)
  have pytha := sin_sq_add_cos_sq ((ν-μ)*π/2)
  have hT : (2:ℂ)^μ ≠ 0 := by simp
  have hP : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [ferrersP_regular hplus hx, ferrersQ_even_odd, ferrersQ_neg_degree_even_odd ν μ hx, hA, hB]
  rw [show μ*π = (ν+μ)*π/2 - (ν-μ)*π/2 by ring, show ν*π = (ν+μ)*π/2 + (ν-μ)*π/2 by ring,
    cos_sub, cos_add, legendre_sin_two_mul_half, legendre_sin_two_mul_half]
  generalize sin ((ν+μ)*π/2) = sb at pyth
  generalize cos ((ν+μ)*π/2) = cb at pyth
  generalize sin ((ν-μ)*π/2) = sa at pytha o2
  generalize cos ((ν-μ)*π/2) = ca at pytha e2
  generalize ferrersEven ν μ x = E
  generalize ferrersOdd ν μ x = O
  generalize Gamma ((ν+μ+1)/2) = g1 at hg1
  generalize Gamma ((ν+μ+2)/2) = g2 at hg2
  generalize Gamma ((ν-μ+1)/2) = h1 at hh1 e2
  generalize Gamma ((ν-μ+2)/2) = h2 at hh2 o2
  generalize Gamma ((μ-ν)/2) = k1 at hk1 o2
  generalize Gamma ((1-ν+μ)/2) = k2 at hk2 e2
  generalize (2:ℂ)^μ = T at hT
  generalize (π:ℂ) = P at hP e2 o2
  have e2' : P = ca*k2*h1 := by field_simp at e2; linear_combination e2
  have o2' : P = -sa*k1*h2 := by field_simp at o2; linear_combination o2
  field_simp
  linear_combination (cb*ca^2*g1*E*h1)*o2' - (sb*sa^2*h2*g2*O)*e2' +
    P*g1*E*h1*cb*(ca^2*pyth - sb^2*pytha) + P*h2*g2*O*sb*(cb^2*pytha - sa^2*pyth)

/-- ferrers connection 7. -/
@[dlmf 14.9.E7]
theorem ferrers_connection_7 (ν μ : ℂ) (hplus : LegendreQRegular ν μ) (hminus : LegendreQRegular ν (-μ)) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    sin ((ν-μ)*π)/Gamma (ν+μ+1)*ferrersP ν μ x=sin (ν*π)/Gamma (ν-μ+1)*ferrersP ν (-μ) x-sin (μ*π)/Gamma (ν-μ+1)*ferrersP ν (-μ) (-x) := by
  obtain ⟨hg1, hg2⟩ := legendre_Gamma_half_ne_zero hplus
  obtain ⟨hh1, hh2⟩ := legendre_Gamma_half_ne_zero_neg hminus
  have pyth := sin_sq_add_cos_sq ((ν+μ)*π/2)
  have pytha := sin_sq_add_cos_sq ((ν-μ)*π/2)
  have hs : (Real.sqrt π:ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hT : (2:ℂ)^μ ≠ 0 := by simp
  have hN : (2:ℂ)^ν ≠ 0 := by simp
  have hP : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [ferrersP_neg_regular hminus hx, ferrersP_neg_regular hminus (ferrers_neg_mem_Ioo hx), ferrersEven_neg,
    ferrersOdd_neg, ferrersP_regular hplus hx, legendre_Gamma_plus, legendre_Gamma_minus, cpow_neg]
  rw [show μ*π = (ν+μ)*π/2 - (ν-μ)*π/2 by ring, show ν*π = (ν+μ)*π/2 + (ν-μ)*π/2 by ring,
    sin_sub, sin_add, legendre_sin_two_mul_half]
  generalize ferrersEven ν μ x = E
  generalize ferrersOdd ν μ x = O
  generalize Gamma ((ν+μ+1)/2) = g1 at hg1
  generalize Gamma ((ν+μ+2)/2) = g2 at hg2
  generalize Gamma ((ν-μ+1)/2) = h1 at hh1
  generalize Gamma ((ν-μ+2)/2) = h2 at hh2
  generalize (2:ℂ)^μ = T at hT
  generalize (2:ℂ)^ν = N at hN
  generalize sin ((ν+μ)*π/2) = sb at pyth
  generalize cos ((ν+μ)*π/2) = cb at pyth
  generalize sin ((ν-μ)*π/2) = sa at pytha
  generalize cos ((ν-μ)*π/2) = ca at pytha
  generalize (Real.sqrt π:ℂ) = S at hs
  generalize (π:ℂ) = P at hP
  field_simp
  linear_combination (0:ℂ)*pyth

/-- ferrers connection 8. -/
@[dlmf 14.9.E8]
theorem ferrers_connection_8 (ν μ : ℂ) (hplus : LegendreQRegular ν μ) (hminus : LegendreQRegular ν (-μ)) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    π/2*sin ((ν-μ)*π)*ferrersP ν (-μ) x=-cos ((ν-μ)*π)*ferrersQ ν (-μ) x-ferrersQ ν (-μ) (-x) := by
  obtain ⟨hh1, hh2⟩ := legendre_Gamma_half_ne_zero_neg hminus
  obtain ⟨hg1, hg2⟩ := legendre_Gamma_half_ne_zero hplus
  have pytha := sin_sq_add_cos_sq ((ν-μ)*π/2)
  have hT : (2:ℂ)^μ ≠ 0 := by simp
  have hP : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [ferrersP_neg_regular hminus hx, ferrersQ_neg_even_odd ν μ hx, ferrersQ_neg_even_odd ν μ (ferrers_neg_mem_Ioo hx),
    ferrersEven_neg, ferrersOdd_neg, cpow_neg]
  rw [legendre_sin_two_mul_half, legendre_cos_two_mul_half]
  generalize ferrersEven ν μ x = E
  generalize ferrersOdd ν μ x = O
  generalize Gamma ((ν+μ+1)/2) = g1 at hg1
  generalize Gamma ((ν+μ+2)/2) = g2 at hg2
  generalize Gamma ((ν-μ+1)/2) = h1 at hh1
  generalize Gamma ((ν-μ+2)/2) = h2 at hh2
  generalize (2:ℂ)^μ = T at hT
  generalize sin ((ν-μ)*π/2) = sa at pytha
  generalize cos ((ν-μ)*π/2) = ca at pytha
  generalize (π:ℂ) = P at hP
  field_simp
  linear_combination (2*ca*g2*h2*O)*pytha

/-- ferrers connection 9. -/
@[dlmf 14.9.E9]
theorem ferrers_connection_9 (ν μ : ℂ) (hplus : LegendreQRegular ν μ) (hminus : LegendreQRegular ν (-μ)) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    2/(Gamma (ν+μ+1)*Gamma (μ-ν))*ferrersQ ν μ x=-cos (ν*π)*ferrersP ν (-μ) x+cos (μ*π)*ferrersP ν (-μ) (-x) := by
  obtain ⟨hg1, hg2⟩ := legendre_Gamma_half_ne_zero hplus
  obtain ⟨hh1, hh2⟩ := legendre_Gamma_half_ne_zero_neg hminus
  obtain ⟨hA, hB⟩ := legendre_reflection_recip_neg hminus
  have pyth := sin_sq_add_cos_sq ((ν+μ)*π/2)
  have pytha := sin_sq_add_cos_sq ((ν-μ)*π/2)
  have hs : (Real.sqrt π:ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hs2 : (Real.sqrt π:ℂ)^2 = π := by rw [← ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
  have hT : (2:ℂ)^μ ≠ 0 := by simp
  have hN : (2:ℂ)^ν ≠ 0 := by simp
  have hP : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [ferrersP_neg_regular hminus hx, ferrersP_neg_regular hminus (ferrers_neg_mem_Ioo hx), ferrersEven_neg,
    ferrersOdd_neg, ferrersQ_even_odd, div_eq_mul_inv, mul_inv, legendre_recip_Gamma_sub, hA, hB,
    legendre_Gamma_plus, cpow_neg]
  rw [show μ*π = (ν+μ)*π/2 - (ν-μ)*π/2 by ring, show ν*π = (ν+μ)*π/2 + (ν-μ)*π/2 by ring,
    cos_sub, cos_add]
  generalize sin ((ν+μ)*π/2) = sb at pyth
  generalize cos ((ν+μ)*π/2) = cb at pyth
  generalize sin ((ν-μ)*π/2) = sa at pytha
  generalize cos ((ν-μ)*π/2) = ca at pytha
  rw [← hs2]
  generalize ferrersEven ν μ x = E
  generalize ferrersOdd ν μ x = O
  generalize Gamma ((ν+μ+1)/2) = g1 at hg1
  generalize Gamma ((ν+μ+2)/2) = g2 at hg2
  generalize Gamma ((ν-μ+1)/2) = h1 at hh1
  generalize Gamma ((ν-μ+2)/2) = h2 at hh2
  generalize (2:ℂ)^μ = T at hT
  generalize (2:ℂ)^ν = N at hN
  generalize (Real.sqrt π:ℂ) = S at hs
  field_simp
  linear_combination (0:ℂ)*pyth

/-- ferrers connection 10. -/
@[dlmf 14.9.E10]
theorem ferrers_connection_10 (ν μ : ℂ) (hplus : LegendreQRegular ν μ) (hminus : LegendreQRegular ν (-μ)) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    2/π*sin ((ν-μ)*π)*ferrersQ ν (-μ) x=cos ((ν-μ)*π)*ferrersP ν (-μ) x-ferrersP ν (-μ) (-x) := by
  obtain ⟨hh1, hh2⟩ := legendre_Gamma_half_ne_zero_neg hminus
  obtain ⟨hg1, hg2⟩ := legendre_Gamma_half_ne_zero hplus
  have pytha := sin_sq_add_cos_sq ((ν-μ)*π/2)
  have hT : (2:ℂ)^μ ≠ 0 := by simp
  have hP : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [ferrersP_neg_regular hminus hx, ferrersP_neg_regular hminus (ferrers_neg_mem_Ioo hx), ferrersQ_neg_even_odd ν μ hx,
    ferrersEven_neg, ferrersOdd_neg, cpow_neg]
  rw [legendre_sin_two_mul_half, legendre_cos_two_mul_half]
  generalize ferrersEven ν μ x = E
  generalize ferrersOdd ν μ x = O
  generalize Gamma ((ν+μ+1)/2) = g1 at hg1
  generalize Gamma ((ν+μ+2)/2) = g2 at hg2
  generalize Gamma ((ν-μ+1)/2) = h1 at hh1
  generalize Gamma ((ν-μ+2)/2) = h2 at hh2
  generalize (2:ℂ)^μ = T at hT
  generalize sin ((ν-μ)*π/2) = sa at pytha
  generalize cos ((ν-μ)*π/2) = ca at pytha
  generalize (π:ℂ) = P at hP
  field_simp
  linear_combination (-(2*ca*h1*E*g1))*pytha

/-- ferrersP negative integer order. -/
@[dlmf 14.9.E3]
theorem ferrersP_negative_integer_order (ν : ℂ) (m : ℕ) (h : ∀ n : ℕ, ν-m+1 ≠ -n) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersP ν (-m) x=(-1)^m*Gamma (ν-m+1)/Gamma (ν+m+1)*ferrersP ν m x := by
  have hG := Gamma_add_nat_ne_zero ν m h
  rcases m with _ | k
  · simp only [Nat.cast_zero, neg_zero, sub_zero, add_zero, pow_zero, one_mul] at hG ⊢
    rw [div_self hG, one_mul]
  have hw := mem_cutPlane_of_one_add (show 1+(x:ℂ) ∈ slitPlane from Or.inl (by simp; linarith [hx.1]))
  have hp := poch_mul_poch_neg_mul_Gamma ν (k+1) h
  have hg := ferrers_gauge_neg_nat (k+1) hx
  unfold ferrersP
  rw [show 1-(-((k+1:ℕ):ℂ)) = ((k+1:ℕ):ℂ)+1 by ring, regularizedGaussHG_legendre_neg_nat ν k hw]
  have hm1 : (-1:ℂ)^(k+1) = poch (ν+1) (k+1) * poch (-ν) (k+1) * Gamma (ν-((k+1:ℕ):ℂ)+1) /
      Gamma (ν+((k+1:ℕ):ℂ)+1) := by rw [hp]; field_simp
  have hsq : (-1:ℂ)^(k+1)*(-1)^(k+1) = 1 := by rw [← mul_pow]; norm_num
  rw [← hg]
  set A := (((1+x)/(1-x):ℝ):ℂ)^(((k+1:ℕ):ℂ)/2) * ((1-(x:ℂ))/2)^(k+1) *
    ((1-(1-(x:ℂ))/2)^(k+1))⁻¹ * regularizedGaussHG (ν+1) (-ν) ((k+1:ℕ)+1) ((1-x)/2) with hA
  linear_combination (-A) * hsq + (-1:ℂ)^(k+1) * A * hm1

/-- ferrersQ negative integer order. -/
@[dlmf 14.9.E4]
theorem ferrersQ_negative_integer_order (ν : ℂ) (m : ℕ) (h : ∀ n : ℕ, ν-m+1 ≠ -n) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersQ ν (-m) x=(-1)^m*Gamma (ν-m+1)/Gamma (ν+m+1)*ferrersQ ν m x := by
  have hm : LegendreQRegular ν (-(m:ℂ)) := fun n hn => h n (by linear_combination hn)
  have hp : LegendreQRegular ν (m:ℂ) := fun n hn => h (n+2*m) (by push_cast; linear_combination hn)
  obtain ⟨hg1, hg2⟩ := legendre_Gamma_half_ne_zero hp
  obtain ⟨hh1, hh2⟩ := legendre_Gamma_half_ne_zero_neg hm
  have hs : (Real.sqrt π:ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hT : (2:ℂ)^(m:ℂ) ≠ 0 := by simp
  have hN : (2:ℂ)^ν ≠ 0 := by simp
  have hσ : ((-1:ℂ)^m)^2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [ferrersQ_neg_even_odd ν m hx, ferrersQ_even_odd, legendre_Gamma_plus, legendre_Gamma_minus, cpow_neg,
    show (ν-m)*π/2 = (ν+m)*π/2 - m*π by ring, legendre_sin_sub_nat_mul_pi, legendre_cos_sub_nat_mul_pi]
  generalize ferrersEven ν m x = E
  generalize ferrersOdd ν m x = O
  generalize Gamma ((ν+m+1)/2) = g1 at hg1
  generalize Gamma ((ν+m+2)/2) = g2 at hg2
  generalize Gamma ((ν-m+1)/2) = h1 at hh1
  generalize Gamma ((ν-m+2)/2) = h2 at hh2
  generalize (2:ℂ)^(m:ℂ) = T at hT
  generalize (2:ℂ)^ν = N at hN
  generalize (-1:ℂ)^m = σ at hσ
  generalize (Real.sqrt π:ℂ) = S at hs
  field_simp

/-- associated connection 11. -/
@[dlmf 14.9.E11]
theorem associated_connection_11 (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    associatedP (-ν-1) μ z=associatedP ν μ z := by
  unfold associatedP
  rw [show -(-ν-1)=ν+1 by ring, show -ν-1+1 = -ν by ring,
    regularizedGaussHG_symm _ _ _ (mem_cutPlane_of_one_add (one_add_mem_slitPlane_of_sub_one hz))]

/-- associated connection 14. -/
@[dlmf 14.9.E14]
theorem associated_connection_14 (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    olverQ ν (-μ) z=olverQ ν μ z := by
  refine legendre_eq_of_continuous_nonint (f := fun μ => olverQ ν (-μ) z) (g := fun μ => olverQ ν μ z)
    ((olverQ_entire_order ν z hz).continuous.comp continuous_neg) (olverQ_entire_order ν z hz).continuous
    (fun μ hμ => ?_) μ
  have hμ' : ∀ n : ℤ, -μ ≠ n := fun n hn => hμ (-n) (by push_cast; linear_combination -hn)
  have h1 := olverQ_connection ν μ hz
  have h2 := olverQ_connection ν (-μ) hz
  rw [neg_neg, show ν+-μ+1 = ν-μ+1 by ring, show ν- -μ+1 = ν+μ+1 by ring, neg_mul, sin_neg] at h2
  have hs := legendre_sin_ne_zero hμ
  have hs' : sin (π*μ) ≠ 0 := by rwa [mul_comm]
  have hpi : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have : 2*sin (μ*π)/π*(olverQ ν μ z - olverQ ν (-μ) z) = 0 := by linear_combination h1 + h2
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h (div_ne_zero (mul_ne_zero two_ne_zero hs) hpi)
  · linear_combination -h

/-- associated connection 12. -/
@[dlmf 14.9.E12]
theorem associated_connection_12 (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    cos (ν*π)*associatedP ν (-μ) z=-olverQ ν μ z/Gamma (μ-ν)+olverQ (-ν-1) μ z/Gamma (ν+μ+1) := by
  refine legendre_eq_of_continuous_nonint
    (f := fun μ => cos (ν*π)*associatedP ν (-μ) z)
    (g := fun μ => -olverQ ν μ z*(Gamma (μ-ν))⁻¹+olverQ (-ν-1) μ z*(Gamma (ν+μ+1))⁻¹)
    (continuous_const.mul (continuous_associatedP_neg_order ν hz))
    ((((olverQ_entire_order ν z hz).continuous.neg.mul (continuous_recip_Gamma.comp (by fun_prop)))).add
      ((olverQ_entire_order (-ν-1) z hz).continuous.mul (continuous_recip_Gamma.comp (by fun_prop))))
    (fun μ hμ => ?_) μ |>.trans (by simp only [div_eq_mul_inv])
  rw [(olverQ_eventuallyEq_nonint ν μ hμ hz).eq_of_nhds, (olverQ_reflect_eventuallyEq_nonint ν μ hμ hz).eq_of_nhds]
  have r1 := legendre_recip_Gamma_reflection (ν+μ+1)
  have r2 := legendre_recip_Gamma_reflection (ν-μ+1)
  rw [show 1-(ν+μ+1) = -ν-1-μ+1 by ring] at r1
  rw [show 1-(ν-μ+1) = μ-ν by ring] at r2
  rw [show -ν-1+μ+1 = μ-ν by ring]
  have t1 : sin (π*(ν+μ+1)) = -(sin (ν*π)*cos (μ*π)+cos (ν*π)*sin (μ*π)) := by
    rw [show (π:ℂ)*(ν+μ+1) = ν*π+μ*π+π by ring, sin_add_pi, sin_add]
  have t2 : sin (π*(ν-μ+1)) = -(sin (ν*π)*cos (μ*π)-cos (ν*π)*sin (μ*π)) := by
    rw [show (π:ℂ)*(ν-μ+1) = ν*π-μ*π+π by ring, sin_add_pi, sin_sub]
  generalize (Gamma (ν+μ+1))⁻¹ = g1 at r1 ⊢
  generalize (Gamma (ν-μ+1))⁻¹ = g2 at r2 ⊢
  generalize (Gamma (μ-ν))⁻¹ = h1 at r2 ⊢
  generalize (Gamma (-ν-1-μ+1))⁻¹ = h2 at r1 ⊢
  have hs := legendre_sin_ne_zero hμ
  have hs' : sin (π*μ) ≠ 0 := by rwa [mul_comm]
  have hpi : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hE : g1*h2-g2*h1 = -2*cos (ν*π)*sin (μ*π)/π := by
    rw [eq_div_iff hpi]; linear_combination r1 - r2 + t1 - t2
  linear_combination (norm := skip) (π/(2*sin (μ*π))*associatedP ν (-μ) z)*hE
  field_simp
  ring



/-- associated connection 15. -/
@[dlmf 14.9.E15]
theorem associated_connection_15 (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    2*sin (μ*π)/π*olverQ ν μ z=associatedP ν μ z/Gamma (ν+μ+1)-associatedP ν (-μ) z/Gamma (ν-μ+1) := by
  exact olverQ_connection ν μ hz

/-- Euler-transformed hypergeometric form of `P^{-μ}_ν` (DLMF 14.3.15), available before
the hypergeometric-representation module for the Whipple formulas. -/
theorem associatedP_neg_euler (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    associatedP ν (-μ) z=2^(-μ)*legendreBranchPower μ z*regularizedGaussHG (μ-ν) (ν+μ+1) (μ+1) ((1-z)/2) := by
  have hw := mem_cutPlane_of_one_add (one_add_mem_slitPlane_of_sub_one hz)
  have h1 : z+1 ≠ 0 := by
    simpa [add_comm] using slitPlane_ne_zero (one_add_mem_slitPlane_of_sub_one hz)
  have hl2 : log (2:ℂ) = (Real.log 2:ℂ) := by
    rw [show (2:ℂ) = ((2:ℝ):ℂ) by norm_num, ofReal_log (by norm_num)]
  have hp : (1-(1-z)/2)^μ = exp ((log (z+1) - Real.log 2)*μ) := by
    rw [show 1-(1-z)/2 = (z+1)*((1/2:ℝ):ℂ) by push_cast; ring,
      cpow_def_of_ne_zero (mul_ne_zero h1 (by norm_num)), log_mul_ofReal _ (by norm_num) _ h1,
      one_div, Real.log_inv]
    push_cast; ring_nf
  have h2 : (2:ℂ)^(-μ) = exp (Real.log 2 * (-μ)) := by
    rw [cpow_def_of_ne_zero (by norm_num), hl2]
  unfold associatedP legendreBranchPower
  rw [show 1-(-μ) = μ+1 by ring, regularizedGaussHG_euler _ _ _ hw, show μ+1-(ν+1)-(-ν) = μ by ring,
    show μ+1-(ν+1) = μ-ν by ring, show μ+1-(-ν) = ν+μ+1 by ring, hp, h2]
  have he : exp (-μ/2*(log (z+1)-log (z-1))) * exp ((log (z+1) - Real.log 2)*μ) =
      exp (Real.log 2 * (-μ)) * exp (μ/2*(log (z-1)+log (z+1))) := by
    rw [← exp_add, ← exp_add]; congr 1; ring
  linear_combination regularizedGaussHG (μ-ν) (ν+μ+1) (μ+1) ((1-z)/2) * he

/-- The regularized quadratic transformation 15.8.17 near the origin, for all parameters. -/
theorem regularizedGaussHG_quadratic_half_sum (a b : ℂ) {x : ℂ} (hx : ‖x‖ < 1) (hr : x.re < 1/2)
    (hw : ‖4*x*(x-1)/(1-2*x)^2‖ < 1) :
    regularizedGaussHG a b ((a+b+1)/2) x =
      (1-2*x)^(-a) * regularizedGaussHG (a/2) ((a+1)/2) ((a+b+1)/2) (4*x*(x-1)/(1-2*x)^2) := by
  have key : ∀ b : ℂ, (∀ k : ℕ, (a+b+1)/2 ≠ -(k:ℂ)) →
      regularizedGaussHG a b ((a+b+1)/2) x =
        (1-2*x)^(-a) * regularizedGaussHG (a/2) ((a+1)/2) ((a+b+1)/2) (4*x*(x-1)/(1-2*x)^2) := by
    intro b hc
    have hG : Gamma ((a+b+1)/2) ≠ 0 := Gamma_ne_zero hc
    have h := quadratic_half_sum hc hx hr hw
    rw [ordinaryHypergeometric_eq_Gamma_mul_regularizedGaussHG hc hx,
      ordinaryHypergeometric_eq_Gamma_mul_regularizedGaussHG hc hw] at h
    apply mul_left_cancel₀ hG
    linear_combination h
  have hxc : x ∈ cutPlane := mem_cutPlane_of_norm_lt_one hx
  have hwc : 4*x*(x-1)/(1-2*x)^2 ∈ cutPlane := mem_cutPlane_of_norm_lt_one hw
  have hF : AnalyticOnNhd ℂ (fun b => regularizedGaussHG a b ((a+b+1)/2) x) univ :=
    analyticOnNhd_regularizedGaussHG_comp (A := fun _ => a) (B := fun b => b)
      (C := fun b => (a+b+1)/2) (by fun_prop) (by fun_prop) (by fun_prop) hxc
  have hG : AnalyticOnNhd ℂ (fun b => (1-2*x)^(-a) *
      regularizedGaussHG (a/2) ((a+1)/2) ((a+b+1)/2) (4*x*(x-1)/(1-2*x)^2)) univ := by
    intro b hb
    exact analyticAt_const.mul (analyticOnNhd_regularizedGaussHG_comp (A := fun _ => a/2)
      (B := fun _ => (a+1)/2) (C := fun b => (a+b+1)/2) (by fun_prop) (by fun_prop)
      (by fun_prop) hwc b hb)
  have hev : (fun b => regularizedGaussHG a b ((a+b+1)/2) x) =ᶠ[𝓝 (3-a)] (fun b => (1-2*x)^(-a) *
      regularizedGaussHG (a/2) ((a+1)/2) ((a+b+1)/2) (4*x*(x-1)/(1-2*x)^2)) := by
    have ho : IsOpen {b : ℂ | 0 < ((a+b+1)/2).re} :=
      isOpen_lt continuous_const (by fun_prop)
    filter_upwards [ho.mem_nhds (by simp; norm_num)] with b hb
    refine key b fun k hk => ?_
    rw [hk] at hb
    simp at hb
    linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  exact hF.eqOn_of_preconnected_of_eventuallyEq hG isPreconnected_univ (mem_univ _) hev (mem_univ b)

/-- The right half of the cut domain of `P^μ_ν` is star-shaped about `2`. -/
theorem starConvex_re_pos_sub_one_slitPlane :
    StarConvex ℝ (2:ℂ) {z : ℂ | 0 < z.re ∧ z-1 ∈ slitPlane} := by
  intro y ⟨hy1, hy2⟩ a b ha hb hab
  rw [mem_slitPlane_iff] at hy2
  have hre : (a • (2:ℂ) + b • y).re = 2*a + b*y.re := by simp; ring
  have him : (a • (2:ℂ) + b • y - 1).im = b*y.im := by simp
  refine ⟨?_, ?_⟩
  · rw [hre]
    rcases eq_or_lt_of_le ha with h | h
    · subst h; simp at hab; subst hab; linarith
    · nlinarith
  · rw [mem_slitPlane_iff]
    rcases eq_or_lt_of_le hb with h | h
    · subst h; left; simp at hab; subst hab; simp
    · rcases hy2 with h2 | h2
      · left
        have : (a • (2:ℂ) + b • y - 1).re = a + b*(y.re-1) := by
          simp; linear_combination hab
        simp at h2
        rw [this]; nlinarith
      · right; rw [him]; exact mul_ne_zero h.ne' (by simpa using h2)

/-- DLMF 14.3.18 for `Re z > 0`, proved before 14.3.16 because the latter is derived from it:
the quadratic transformation 15.8.17 on the real segment `(1,2)`, then analytic continuation. -/
theorem associatedP_neg_eq_quadratic (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) (hre : 0 < z.re) :
    associatedP ν (-μ) z=2^(-μ)*z^(ν-μ)*legendreBranchPower μ z*regularizedGaussHG ((μ-ν)/2) ((μ-ν+1)/2) (μ+1) (1-1/z^2) := by
  set D : Set ℂ := {z : ℂ | 0 < z.re ∧ z-1 ∈ slitPlane} with hD
  have hDo : IsOpen D := (isOpen_lt continuous_const continuous_re).inter
    (isOpen_slitPlane.preimage (continuous_sub_right 1))
  have hmem : ∀ w ∈ D, w + 1 ∈ slitPlane ∧ w - 1 ∈ slitPlane ∧ w ∈ slitPlane ∧
      (1-w)/2 ∈ cutPlane ∧ 1-1/w^2 ∈ cutPlane := by
    intro w ⟨h1, h2⟩
    refine ⟨Or.inl (by simp; linarith), h2, Or.inl h1,
      mem_cutPlane_of_one_add (Or.inl (by simp; linarith)), ?_⟩
    show 1 - (1 - 1/w^2) ∈ slitPlane
    rw [sub_sub_cancel, one_div]
    exact recip_mem_slitPlane' (sq_mem_slitPlane h1)
  have hf : AnalyticOnNhd ℂ (associatedP ν (-μ)) D := by
    refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) hDo
    obtain ⟨h1, h2, -, h4, -⟩ := hmem w hw
    unfold associatedP
    apply DifferentiableAt.differentiableWithinAt
    fun_prop (disch := assumption)
  have hg : AnalyticOnNhd ℂ (fun z => 2^(-μ)*z^(ν-μ)*legendreBranchPower μ z*
      regularizedGaussHG ((μ-ν)/2) ((μ-ν+1)/2) (μ+1) (1-1/z^2)) D := by
    refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) hDo
    obtain ⟨h1, h2, h3, -, h5⟩ := hmem w hw
    have h0 : w ^ 2 ≠ 0 := pow_ne_zero 2 (slitPlane_ne_zero h3)
    unfold legendreBranchPower
    apply DifferentiableAt.differentiableWithinAt
    fun_prop (disch := assumption)
  have hreal : ∀ t : ℝ, t ∈ Ioo (1:ℝ) 2 → associatedP ν (-μ) t = 2^(-μ)*(t:ℂ)^(ν-μ)*
      legendreBranchPower μ t*regularizedGaussHG ((μ-ν)/2) ((μ-ν+1)/2) (μ+1) (1-1/(t:ℂ)^2) := by
    intro t ht
    have ht0 : (t:ℂ) ≠ 0 := by exact_mod_cast (by linarith [ht.1] : t ≠ 0)
    have hz1 : (t:ℂ) - 1 ∈ slitPlane := Or.inl (by simp; linarith [ht.1])
    rw [associatedP_neg_euler ν μ hz1]
    set x : ℂ := (1-(t:ℂ))/2 with hx
    have hxn : ‖x‖ < 1 := by
      rw [show x = (((1-t)/2:ℝ):ℂ) by push_cast; ring, norm_real, Real.norm_eq_abs, abs_lt]
      constructor <;> linarith [ht.1, ht.2]
    have hxr : x.re < 1/2 := by simp [hx]; linarith [ht.1]
    have hv : 4*x*(x-1)/(1-2*x)^2 = 1-1/(t:ℂ)^2 := by
      rw [hx, show 1-2*((1-(t:ℂ))/2) = t by ring]; field_simp; ring
    have hvn : ‖4*x*(x-1)/(1-2*x)^2‖ < 1 := by
      rw [hv, show (1-1/(t:ℂ)^2) = ((1-1/t^2:ℝ):ℂ) by push_cast; ring, norm_real,
        Real.norm_eq_abs, abs_lt]
      have h1 : 1 < t^2 := by nlinarith [ht.1]
      have h2 : 0 < 1/t^2 := by positivity
      have h3 : 1/t^2 < 1 := by rw [div_lt_one (by positivity)]; exact h1
      constructor <;> linarith
    have hq := regularizedGaussHG_quadratic_half_sum (μ-ν) (ν+μ+1) hxn hxr hvn
    rw [show (μ-ν+(ν+μ+1)+1)/2 = μ+1 by ring, hv, show 1-2*x = (t:ℂ) by rw [hx]; ring,
      show -(μ-ν) = ν-μ by ring] at hq
    rw [hq]; ring
  have hfreq : ∃ᶠ w in 𝓝[≠] ((3/2:ℝ):ℂ), associatedP ν (-μ) w = 2^(-μ)*w^(ν-μ)*
      legendreBranchPower μ w*regularizedGaussHG ((μ-ν)/2) ((μ-ν+1)/2) (μ+1) (1-1/w^2) := by
    have hT : Tendsto (fun t : ℝ => (t:ℂ)) (𝓝[≠] (3/2:ℝ)) (𝓝[≠] ((3/2:ℝ):ℂ)) :=
      (continuous_ofReal.tendsto _).inf (tendsto_principal_principal.mpr fun t ht =>
        fun h => ht (ofReal_injective h))
    apply hT.frequently
    have hev : ∀ᶠ t : ℝ in 𝓝[≠] (3/2:ℝ), associatedP ν (-μ) t = 2^(-μ)*(t:ℂ)^(ν-μ)*
        legendreBranchPower μ t*regularizedGaussHG ((μ-ν)/2) ((μ-ν+1)/2) (μ+1) (1-1/(t:ℂ)^2) := by
      apply eventually_nhdsWithin_of_eventually_nhds
      filter_upwards [Ioo_mem_nhds (by norm_num : (1:ℝ) < 3/2) (by norm_num : (3/2:ℝ) < 2)]
        with t ht using hreal t ht
    exact hev.frequently
  have h32 : ((3/2:ℝ):ℂ) ∈ D := ⟨by simp, Or.inl (by simp; norm_num)⟩
  exact hf.eqOn_of_preconnected_of_frequently_eq hg
    (StarConvex.isPathConnected starConvex_re_pos_sub_one_slitPlane
      ⟨by simp, Or.inl (by simp)⟩).isConnected.isPreconnected h32 hfreq ⟨hre, hz⟩

/-- Off `(-∞,1]`, `1 - 1/z²` lies in the slit plane. -/
theorem one_sub_recip_sq_mem_slitPlane_of_sub_one {z : ℂ} (hz : z-1 ∈ slitPlane) : 1-1/z^2 ∈ slitPlane := by
  have hz0 : z ≠ 0 := by
    rintro rfl; rw [mem_slitPlane_iff] at hz; norm_num at hz
  rw [mem_slitPlane_iff_not_le_zero]
  intro hle
  rw [Complex.le_def] at hle
  obtain ⟨hre, him⟩ := hle
  simp only [zero_re, zero_im] at hre him
  set r := (1-1/z^2).re
  have hr : 1-1/z^2 = (r:ℂ) := Complex.ext rfl (by simpa using him.symm)
  have h1r : (0:ℝ) < 1 - r := by linarith
  have hzsq : z^2 = ((1/(1-r):ℝ):ℂ) := by
    have h2 : 1/z^2 = ((1-r:ℝ):ℂ) := by push_cast; linear_combination -hr
    have h2' : ((1-r:ℝ):ℂ) ≠ 0 := ofReal_ne_zero.mpr h1r.ne'
    rw [ofReal_div, ofReal_one, ← h2]; field_simp
  have him2 := congrArg Complex.im hzsq
  have hre2 := congrArg Complex.re hzsq
  simp only [pow_two, mul_im, mul_re, ofReal_im, ofReal_re] at him2 hre2
  have hpos : 0 < 1/(1-r) := by positivity
  have hle1 : 1/(1-r) ≤ 1 := by rw [div_le_one h1r]; linarith
  have hb : z.im = 0 := by
    rcases mul_eq_zero.mp (show z.re * z.im * 2 = 0 by linarith) with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · rw [h'] at hre2; nlinarith [sq_nonneg z.im]
      · exact h'
    · norm_num at h
  rw [hb] at hre2
  have : z.re ≤ 1 := by nlinarith
  rw [mem_slitPlane_iff] at hz
  rcases hz with h | h
  · simp at h; linarith
  · simp [hb] at h

/-- The square of the inherited square root `exp((log(z-1)+log(z+1))/2)` is `(z-1)(z+1)`. -/
theorem whipple_sqrt_sq {z : ℂ} (h1 : z - 1 ≠ 0) (h2 : z + 1 ≠ 0) :
    exp ((log (z-1)+log (z+1))/2)^2 = (z-1)*(z+1) := by
  rw [← exp_nat_mul, show ((2:ℕ):ℂ)*((log (z-1)+log (z+1))/2) = log (z-1)+log (z+1) by push_cast; ring,
    exp_add, exp_log h1, exp_log h2]

/-- On the right half of the cut domain, the Whipple point `z/√(z²-1)` avoids `(-∞,1]`. -/
theorem whipple_point_sub_one_mem {z : ℂ} (hz : z-1 ∈ slitPlane) (hre : 0 < z.re) :
    z/exp ((log (z-1)+log (z+1))/2) - 1 ∈ slitPlane := by
  have h1 : z - 1 ≠ 0 := slitPlane_ne_zero hz
  have h2 : z + 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  set w := exp ((log (z-1)+log (z+1))/2) with hw
  have hw0 : w ≠ 0 := exp_ne_zero _
  have hw2 := whipple_sqrt_sq h1 h2
  rw [← hw] at hw2
  rw [mem_slitPlane_iff_not_le_zero]
  intro hle
  rw [Complex.le_def] at hle
  obtain ⟨hr, hi⟩ := hle
  simp only [zero_re, zero_im] at hr hi
  set r := (z/w).re with hrdef
  have hζ : z/w = (r:ℂ) := Complex.ext rfl (by simpa using hi)
  have hzr : z = r*w := by rw [← hζ]; field_simp
  -- w² (r²-1) = 1
  have hr2 : w^2*((r:ℂ)^2-1) = 1 := by
    have : z^2 = (r:ℂ)^2*w^2 := by rw [hzr]; ring
    linear_combination -this - hw2
  have hr1 : (r:ℂ)^2 - 1 ≠ 0 := by
    intro h; rw [h, mul_zero] at hr2; exact zero_ne_one hr2
  have hzsq : z^2 = (((r^2/(r^2-1)):ℝ):ℂ) := by
    have hw2' : w^2 = 1/((r:ℂ)^2-1) := by field_simp; linear_combination hr2
    rw [hzr, mul_pow, hw2']; push_cast; field_simp
  have him := congrArg Complex.im hzsq
  simp only [pow_two, mul_im, ofReal_im] at him
  have hzi : z.im = 0 := by
    have : z.re * z.im = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact h
  -- z is a real number a > 1
  have ha : 1 < z.re := by
    rw [mem_slitPlane_iff] at hz
    rcases hz with h | h
    · simp at h; linarith
    · simp [hzi] at h
  have hzc : z = (z.re:ℂ) := Complex.ext rfl (by simp [hzi])
  set a := z.re
  have hl1 : log (z-1) = (Real.log (a-1):ℂ) := by
    rw [hzc, ← ofReal_one, ← ofReal_sub, ofReal_log (by linarith)]
  have hl2 : log (z+1) = (Real.log (a+1):ℂ) := by
    rw [hzc, ← ofReal_one, ← ofReal_add, ofReal_log (by linarith)]
  set W := Real.exp ((Real.log (a-1)+Real.log (a+1))/2)
  have hwW : w = (W:ℂ) := by rw [hw, hl1, hl2]; simp only [W, ofReal_exp]; push_cast; ring_nf
  have hW0 : 0 < W := Real.exp_pos _
  have hW2 : W^2 = (a-1)*(a+1) := by
    have := hw2; rw [hwW, hzc] at this; exact_mod_cast this
  have hrW : r = a/W := by
    have := hζ; rw [hzc, hwW, ← ofReal_div] at this; exact (ofReal_injective this).symm
  have : W < a := by nlinarith
  have : 1 < r := by rw [hrW, lt_div_iff₀ hW0]; linarith
  have : r ≤ 1 := by simp only [sub_re, one_re] at hr; linarith
  linarith

/-- The Whipple point of a real `t > 1` is the real number `t/√(t²-1) > 1`, with its logarithms. -/
theorem whipple_point_real {t : ℝ} (ht : 1 < t) :
    ∃ ζ : ℝ, 1 < ζ ∧ (t:ℂ)/exp ((log ((t:ℂ)-1)+log ((t:ℂ)+1))/2) = ζ ∧
      Real.log (ζ-1) + Real.log (ζ+1) = -(Real.log (t-1) + Real.log (t+1)) ∧
      Real.log ζ = Real.log t - (Real.log (t-1) + Real.log (t+1))/2 ∧
      1/(ζ:ℂ)^2 = 1 - 1/(t:ℂ)^2 := by
  set l := Real.log (t-1) + Real.log (t+1) with hl
  set W := Real.exp (l/2) with hW
  have hW0 : 0 < W := Real.exp_pos _
  have hW2 : W^2 = (t-1)*(t+1) := by
    rw [hW, ← Real.exp_nat_mul, show ((2:ℕ):ℝ)*(l/2) = l by push_cast; ring, hl, Real.exp_add,
      Real.exp_log (by linarith), Real.exp_log (by linarith)]
  have ht0 : 0 < t := by linarith
  have hWt : W < t := by nlinarith
  refine ⟨t/W, by rw [lt_div_iff₀ hW0]; linarith, ?_, ?_, ?_, ?_⟩
  · rw [show (t:ℂ)-1 = ((t-1:ℝ):ℂ) by push_cast; ring, show (t:ℂ)+1 = ((t+1:ℝ):ℂ) by push_cast; ring,
      ← ofReal_log (by linarith), ← ofReal_log (by linarith), ← ofReal_add,
      show ((Real.log (t-1) + Real.log (t+1) : ℝ):ℂ)/2 = ((l/2:ℝ):ℂ) by rw [hl]; push_cast; ring,
      ← ofReal_exp, ← ofReal_div]
  · have hz1 : 0 < t/W - 1 := by rw [sub_pos, lt_div_iff₀ hW0]; linarith
    have hz2 : 0 < t/W + 1 := by positivity
    rw [← Real.log_mul hz1.ne' hz2.ne', show (t/W-1)*(t/W+1) = (W^2)⁻¹ by
      field_simp; nlinarith [hW2], Real.log_inv, Real.log_pow, hW, Real.log_exp]
    push_cast; ring
  · rw [Real.log_div ht0.ne' hW0.ne', hW, Real.log_exp]
  · have hW2c : (W:ℂ)^2 = ((t:ℂ)-1)*((t:ℂ)+1) := by exact_mod_cast hW2
    have ht0c : (t:ℂ) ≠ 0 := ofReal_ne_zero.mpr ht0.ne'
    have hW0c : (W:ℂ) ≠ 0 := ofReal_ne_zero.mpr hW0.ne'
    push_cast
    field_simp
    linear_combination hW2c

/-- Whipple's formula 14.9.16 on the real ray `t > 1`. -/
theorem olverQ_whipple_real (ν μ : ℂ) (t : ℝ) (ht : 1 < t) :
    olverQ ν μ t=(π/2:ℂ)^(1/2:ℂ)*legendreBranchPower (-1/2) t*associatedP (-μ-1/2) (-ν-1/2) (t/exp ((log ((t:ℂ)-1)+log ((t:ℂ)+1))/2)) := by
  obtain ⟨ζ, hζ1, hζe, hlog, hlogζ, hinv⟩ := whipple_point_real ht
  have ht0 : 0 < t := by linarith
  rw [hζe, show -ν-1/2 = -(ν+1/2) by ring,
    associatedP_neg_eq_quadratic (-μ-1/2) (ν+1/2) (Or.inl (by simp; linarith)) (by simp; linarith),
    show (ν+1/2-(-μ-1/2))/2 = (ν+μ+1)/2 by ring, show (ν+1/2-(-μ-1/2)+1)/2 = (ν+μ+2)/2 by ring,
    show ν+1/2+1 = ν+3/2 by ring, show 1-1/(ζ:ℂ)^2 = 1/(t:ℂ)^2 by rw [hinv]; ring]
  have hcut : 1/(t:ℂ)^2 ∈ cutPlane := by
    apply mem_cutPlane_of_norm_lt_one
    rw [show 1/(t:ℂ)^2 = ((1/t^2:ℝ):ℂ) by push_cast; ring, norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity), div_lt_one (by positivity)]
    nlinarith
  rw [regularizedGaussHG_symm _ _ _ hcut]
  unfold olverQ legendreBranchPower
  have hl1 : log ((t:ℂ)-1) = (Real.log (t-1):ℂ) := by
    rw [show (t:ℂ)-1 = ((t-1:ℝ):ℂ) by push_cast; ring, ofReal_log (by linarith)]
  have hl2 : log ((t:ℂ)+1) = (Real.log (t+1):ℂ) := by
    rw [show (t:ℂ)+1 = ((t+1:ℝ):ℂ) by push_cast; ring, ofReal_log (by linarith)]
  have hk1 : log ((ζ:ℂ)-1) = (Real.log (ζ-1):ℂ) := by
    rw [show (ζ:ℂ)-1 = ((ζ-1:ℝ):ℂ) by push_cast; ring, ofReal_log (by linarith)]
  have hk2 : log ((ζ:ℂ)+1) = (Real.log (ζ+1):ℂ) := by
    rw [show (ζ:ℂ)+1 = ((ζ+1:ℝ):ℂ) by push_cast; ring, ofReal_log (by linarith)]
  have hc2 : ∀ s : ℂ, (2:ℂ)^s = exp ((Real.log 2:ℂ)*s) := fun s => by
    rw [cpow_def_of_ne_zero two_ne_zero, show (2:ℂ) = ((2:ℝ):ℂ) by norm_num, ofReal_log (by norm_num)]
  have hct : ∀ s : ℂ, (t:ℂ)^s = exp ((Real.log t:ℂ)*s) := fun s => by
    rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr ht0.ne'), ofReal_log ht0.le]
  have hcz : ∀ s : ℂ, (ζ:ℂ)^s = exp ((Real.log ζ:ℂ)*s) := fun s => by
    rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr (by linarith)), ofReal_log (by linarith)]
  have hpi2 : (π/2:ℂ)^(1/2:ℂ) = exp (((Real.log π - Real.log 2:ℝ):ℂ)*(1/2)) := by
    rw [cpow_def_of_ne_zero (div_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero) two_ne_zero),
      show (π/2:ℂ) = ((π/2:ℝ):ℂ) by push_cast; ring, ← ofReal_log (by positivity),
      Real.log_div Real.pi_ne_zero two_ne_zero]
  have hsq : ((Real.sqrt π:ℝ):ℂ) = exp ((Real.log π:ℂ)/2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos Real.pi_pos, ofReal_exp]; push_cast; ring_nf
  rw [hl1, hl2, hk1, hk2, ← ofReal_add (Real.log (ζ-1)), hlog, hc2, hc2, hct, hcz, hpi2, hsq, hlogζ]
  simp only [div_eq_mul_inv, ← exp_neg, ← mul_assoc, ← exp_add]
  congr 2
  push_cast
  ring

/-- Whipple's formula 14.9.17 on the real ray `t > 1`. -/
theorem associatedP_whipple_real (ν μ : ℂ) (t : ℝ) (ht : 1 < t) :
    associatedP ν μ t=(2/π:ℂ)^(1/2:ℂ)*legendreBranchPower (-1/2) t*olverQ (-μ-1/2) (ν+1/2) (t/exp ((log ((t:ℂ)-1)+log ((t:ℂ)+1))/2)) := by
  obtain ⟨ζ, hζ1, hζe, hlog, hlogζ, hinv⟩ := whipple_point_real ht
  have ht0 : 0 < t := by linarith
  have hz1 : (t:ℂ) - 1 ∈ slitPlane := Or.inl (by simp; linarith)
  have hw : 1-1/(t:ℂ)^2 ∈ cutPlane := by
    apply mem_cutPlane_of_norm_lt_one
    rw [show 1-1/(t:ℂ)^2 = ((1-1/t^2:ℝ):ℂ) by push_cast; ring, norm_real, Real.norm_eq_abs, abs_lt]
    have h1 : 0 < 1/t^2 := by positivity
    have h2 : 1/t^2 < 1 := by rw [div_lt_one (by positivity)]; nlinarith
    constructor <;> linarith
  have hL := associatedP_neg_eq_quadratic ν (-μ) hz1 (by simp; linarith)
  rw [neg_neg, show -μ-ν = -ν-μ by ring] at hL
  rw [hL, hζe]
  unfold olverQ
  rw [hinv, show -μ-1/2+(ν+1/2)+2 = ν-μ+2 by ring, show -μ-1/2+(ν+1/2)+1 = ν-μ+1 by ring,
    show -μ-1/2+3/2 = -μ+1 by ring, regularizedGaussHG_euler _ _ _ hw, sub_sub_cancel,
    show -μ+1-(-ν-μ)/2-(-ν-μ+1)/2 = ν+1/2 by ring,
    show -μ+1-(-ν-μ)/2 = (ν-μ+2)/2 by ring, show -μ+1-(-ν-μ+1)/2 = (ν-μ+1)/2 by ring]
  unfold legendreBranchPower
  have hl1 : log ((t:ℂ)-1) = (Real.log (t-1):ℂ) := by
    rw [show (t:ℂ)-1 = ((t-1:ℝ):ℂ) by push_cast; ring, ofReal_log (by linarith)]
  have hl2 : log ((t:ℂ)+1) = (Real.log (t+1):ℂ) := by
    rw [show (t:ℂ)+1 = ((t+1:ℝ):ℂ) by push_cast; ring, ofReal_log (by linarith)]
  have hk1 : log ((ζ:ℂ)-1) = (Real.log (ζ-1):ℂ) := by
    rw [show (ζ:ℂ)-1 = ((ζ-1:ℝ):ℂ) by push_cast; ring, ofReal_log (by linarith)]
  have hk2 : log ((ζ:ℂ)+1) = (Real.log (ζ+1):ℂ) := by
    rw [show (ζ:ℂ)+1 = ((ζ+1:ℝ):ℂ) by push_cast; ring, ofReal_log (by linarith)]
  have hc2 : ∀ s : ℂ, (2:ℂ)^s = exp ((Real.log 2:ℂ)*s) := fun s => by
    rw [cpow_def_of_ne_zero two_ne_zero, show (2:ℂ) = ((2:ℝ):ℂ) by norm_num, ofReal_log (by norm_num)]
  have hct : ∀ s : ℂ, (t:ℂ)^s = exp ((Real.log t:ℂ)*s) := fun s => by
    rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr ht0.ne'), ofReal_log ht0.le]
  have hcz : ∀ s : ℂ, (ζ:ℂ)^s = exp ((Real.log ζ:ℂ)*s) := fun s => by
    rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr (by linarith)), ofReal_log (by linarith)]
  have hct2 : ∀ s : ℂ, (1/(t:ℂ)^2)^s = exp ((-2*Real.log t:ℝ)*s) := fun s => by
    rw [cpow_def_of_ne_zero (by simp; exact ht0.ne'), show 1/(t:ℂ)^2 = ((1/t^2:ℝ):ℂ) by push_cast; ring,
      ← ofReal_log (by positivity), Real.log_div one_ne_zero (by positivity), Real.log_one,
      Real.log_pow]
    push_cast; ring_nf
  have hpi2 : (2/π:ℂ)^(1/2:ℂ) = exp (((Real.log 2 - Real.log π:ℝ):ℂ)*(1/2)) := by
    rw [cpow_def_of_ne_zero (div_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)),
      show (2/π:ℂ) = ((2/π:ℝ):ℂ) by push_cast; ring, ← ofReal_log (by positivity),
      Real.log_div two_ne_zero Real.pi_ne_zero]
  have hsq : ((Real.sqrt π:ℝ):ℂ) = exp ((Real.log π:ℂ)/2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos Real.pi_pos, ofReal_exp]; push_cast; ring_nf
  rw [hl1, hl2, hk1, hk2, ← ofReal_add (Real.log (ζ-1)), hlog, hc2, hc2, hct, hcz, hct2, hpi2, hsq,
    hlogζ]
  simp only [div_eq_mul_inv, ← exp_neg, ← mul_assoc, ← exp_add]
  congr 2
  push_cast
  ring

/-- Identity principle on the right half of the cut domain: functions analytic there that agree
on the real segment `(1,2)` agree everywhere on it. -/
theorem eq_of_eqOn_Ioo_re_pos {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f {z : ℂ | 0 < z.re ∧ z-1 ∈ slitPlane})
    (hg : AnalyticOnNhd ℂ g {z : ℂ | 0 < z.re ∧ z-1 ∈ slitPlane})
    (h : ∀ t : ℝ, t ∈ Ioo (1:ℝ) 2 → f t = g t) {z : ℂ} (hz : z-1 ∈ slitPlane) (hre : 0 < z.re) :
    f z = g z := by
  have hfreq : ∃ᶠ w in 𝓝[≠] ((3/2:ℝ):ℂ), f w = g w := by
    have hT : Tendsto (fun t : ℝ => (t:ℂ)) (𝓝[≠] (3/2:ℝ)) (𝓝[≠] ((3/2:ℝ):ℂ)) :=
      (continuous_ofReal.tendsto _).inf (tendsto_principal_principal.mpr fun t ht =>
        fun h => ht (ofReal_injective h))
    apply hT.frequently
    have hev : ∀ᶠ t : ℝ in 𝓝[≠] (3/2:ℝ), f t = g t := by
      apply eventually_nhdsWithin_of_eventually_nhds
      filter_upwards [Ioo_mem_nhds (by norm_num : (1:ℝ) < 3/2) (by norm_num : (3/2:ℝ) < 2)]
        with t ht using h t ht
    exact hev.frequently
  have h32 : ((3/2:ℝ):ℂ) ∈ {z : ℂ | 0 < z.re ∧ z-1 ∈ slitPlane} :=
    ⟨by simp, Or.inl (by simp; norm_num)⟩
  exact hf.eqOn_of_preconnected_of_frequently_eq hg
    (StarConvex.isPathConnected starConvex_re_pos_sub_one_slitPlane
      ⟨by simp, Or.inl (by simp)⟩).isConnected.isPreconnected h32 hfreq ⟨hre, hz⟩

/-- Domain facts for the Whipple formulas on the right half of the cut domain. -/
theorem whipple_domain {w : ℂ} (hw : w ∈ {z : ℂ | 0 < z.re ∧ z-1 ∈ slitPlane}) :
    w + 1 ∈ slitPlane ∧ w - 1 ∈ slitPlane ∧ w ∈ slitPlane ∧ 1/w^2 ∈ cutPlane ∧
    w/exp ((log (w-1)+log (w+1))/2) - 1 ∈ slitPlane ∧
    w/exp ((log (w-1)+log (w+1))/2) + 1 ∈ slitPlane ∧
    w/exp ((log (w-1)+log (w+1))/2) ∈ slitPlane ∧
    (1 - w/exp ((log (w-1)+log (w+1))/2))/2 ∈ cutPlane ∧
    1/(w/exp ((log (w-1)+log (w+1))/2))^2 ∈ cutPlane := by
  obtain ⟨hre, h2⟩ := hw
  have hm := whipple_point_sub_one_mem h2 hre
  have hsl : ∀ u : ℂ, u - 1 ∈ slitPlane → u ∈ slitPlane := fun u hu => by
    rw [mem_slitPlane_iff] at hu ⊢
    rcases hu with h | h
    · left; simp at h; linarith
    · right; simpa using h
  have hp : ∀ u : ℂ, u - 1 ∈ slitPlane → u + 1 ∈ slitPlane := fun u hu => by
    have := one_add_mem_slitPlane_of_sub_one hu; rwa [add_comm] at this
  exact ⟨hp w h2, h2, hsl w h2, one_sub_recip_sq_mem_slitPlane_of_sub_one h2, hm, hp _ hm, hsl _ hm,
    mem_cutPlane_of_one_add (one_add_mem_slitPlane_of_sub_one hm),
    one_sub_recip_sq_mem_slitPlane_of_sub_one hm⟩

/-- Principal-sheet formula; Whipple transformation is stated in the right half-plane to fix its inherited branch. -/
@[dlmf 14.9.E16]
theorem associated_connection_16 (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) (hre : 0 < z.re) :
    olverQ ν μ z=(π/2:ℂ)^(1/2:ℂ)*legendreBranchPower (-1/2) z*associatedP (-μ-1/2) (-ν-1/2) (z/exp ((log (z-1)+log (z+1))/2)) := by
  refine eq_of_eqOn_Ioo_re_pos (f := olverQ ν μ)
    (g := fun z => (π/2:ℂ)^(1/2:ℂ)*legendreBranchPower (-1/2) z*associatedP (-μ-1/2) (-ν-1/2) (z/exp ((log (z-1)+log (z+1))/2))) ?_ ?_ (fun t ht => olverQ_whipple_real ν μ t ht.1) hz hre
  · refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) ((isOpen_lt continuous_const continuous_re).inter
      (isOpen_slitPlane.preimage (continuous_sub_right 1)))
    obtain ⟨h1, h2, h3, h4, -⟩ := whipple_domain hw
    have h0 : w ^ 2 ≠ 0 := pow_ne_zero 2 (slitPlane_ne_zero h3)
    have h6 : w ^ (ν+μ+1) ≠ 0 := by rw [cpow_def_of_ne_zero (slitPlane_ne_zero h3)]; exact exp_ne_zero _
    unfold olverQ legendreBranchPower
    simp only [div_eq_mul_inv, mul_inv]
    apply DifferentiableAt.differentiableWithinAt
    fun_prop (disch := first | assumption | simpa [div_eq_mul_inv] using h4)
  · refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) ((isOpen_lt continuous_const continuous_re).inter
      (isOpen_slitPlane.preimage (continuous_sub_right 1)))
    obtain ⟨h1, h2, h3, -, h5, h6, h7, h8, -⟩ := whipple_domain hw
    have hE : exp ((log (w-1)+log (w+1))/2) ≠ 0 := exp_ne_zero _
    unfold associatedP legendreBranchPower
    apply DifferentiableAt.differentiableWithinAt
    fun_prop (disch := assumption)

/-- Principal-sheet formula; Whipple transformation is stated in the right half-plane to fix its inherited branch. -/
@[dlmf 14.9.E17]
theorem associated_connection_17 (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) (hre : 0 < z.re) :
    associatedP ν μ z=(2/π:ℂ)^(1/2:ℂ)*legendreBranchPower (-1/2) z*olverQ (-μ-1/2) (ν+1/2) (z/exp ((log (z-1)+log (z+1))/2)) := by
  refine eq_of_eqOn_Ioo_re_pos (f := associatedP ν μ)
    (g := fun z => (2/π:ℂ)^(1/2:ℂ)*legendreBranchPower (-1/2) z*olverQ (-μ-1/2) (ν+1/2) (z/exp ((log (z-1)+log (z+1))/2))) ?_ ?_ (fun t ht => associatedP_whipple_real ν μ t ht.1) hz hre
  · refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) ((isOpen_lt continuous_const continuous_re).inter
      (isOpen_slitPlane.preimage (continuous_sub_right 1)))
    obtain ⟨h1, h2, -, -, -⟩ := whipple_domain hw
    have h4 : (1-w)/2 ∈ cutPlane := mem_cutPlane_of_one_add (one_add_mem_slitPlane_of_sub_one h2)
    unfold associatedP
    apply DifferentiableAt.differentiableWithinAt
    fun_prop (disch := assumption)
  · refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) ((isOpen_lt continuous_const continuous_re).inter
      (isOpen_slitPlane.preimage (continuous_sub_right 1)))
    obtain ⟨h1, h2, h3, -, h5, h6, h7, -, h9⟩ := whipple_domain hw
    have hE : exp ((log (w-1)+log (w+1))/2) ≠ 0 := exp_ne_zero _
    have h0 : (w/exp ((log (w-1)+log (w+1))/2)) ^ 2 ≠ 0 := pow_ne_zero 2 (slitPlane_ne_zero h7)
    have h10 : (w/exp ((log (w-1)+log (w+1))/2)) ^ (-μ-1/2+(ν+1/2)+1) ≠ 0 := by
      rw [cpow_def_of_ne_zero (slitPlane_ne_zero h7)]; exact exp_ne_zero _
    unfold olverQ legendreBranchPower
    simp only [div_eq_mul_inv, mul_inv]
    apply DifferentiableAt.differentiableWithinAt
    fun_prop (disch := first | assumption | simpa [div_eq_mul_inv] using h9)

/-- associatedP negative integer order. -/
@[dlmf 14.9.E13]
theorem associatedP_negative_integer_order (ν : ℂ) (m : ℕ) (h : ∀ n : ℕ, ν-m+1 ≠ -n) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    associatedP ν (-m) z=Gamma (ν-m+1)/Gamma (ν+m+1)*associatedP ν m z := by
  have hG := Gamma_add_nat_ne_zero ν m h
  rcases m with _ | k
  · simp only [Nat.cast_zero, neg_zero, sub_zero, add_zero] at hG ⊢
    rw [div_self hG, one_mul]
  have hw := mem_cutPlane_of_one_add (one_add_mem_slitPlane_of_sub_one hz)
  have hp := poch_mul_poch_neg_mul_Gamma ν (k+1) h
  have hg := associated_gauge_neg_nat (k+1) hz
  unfold associatedP
  rw [show 1-(-((k+1:ℕ):ℂ)) = ((k+1:ℕ):ℂ)+1 by ring, regularizedGaussHG_legendre_neg_nat ν k hw]
  calc _ = ((-1)^(k+1)*(-1)^(k+1)) * exp (-((k+1:ℕ):ℂ)/2*(log (z+1)-log (z-1))) *
        regularizedGaussHG (ν+1) (-ν) ((k+1:ℕ)+1) ((1-z)/2) := by
          rw [← mul_pow, show (-1:ℂ)*(-1) = 1 by ring, one_pow, one_mul]
    _ = _ := by
      have hm1 : (-1:ℂ)^(k+1) = poch (ν+1) (k+1) * poch (-ν) (k+1) * Gamma (ν-((k+1:ℕ):ℂ)+1) /
          Gamma (ν+((k+1:ℕ):ℂ)+1) := by rw [hp]; field_simp
      rw [mul_assoc ((-1:ℂ)^(k+1)), ← hg, hm1]
      ring

end DLMF.Legendre
