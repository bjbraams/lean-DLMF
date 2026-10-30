/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ParabolicCylinder.Basic.Functions

public import DLMF.Confluent.ParabolicCylinder.EquationAndIntegrals

/-!
# Wronskians and connections of parabolic cylinder functions

Wronskians of rotated Weber solutions, connection formulas and the second cylinder solution V.

Source references and common attribution are retained in
`DLMF.Confluent.ParabolicCylinder`.
-/

@[expose] public section

open Complex Filter MeasureTheory Asymptotics Set

open scoped Real Topology Nat

open DLMF.Hypergeometric

noncomputable section

namespace DLMF.Confluent

/-! ### Wronskians (DLMF 12.2) -/

/-- The derivative of `w ↦ U(a,-w)` is `-U'(a,-z)`. -/
theorem hasDerivAt_pcfU_neg (a z : ℂ) :
    HasDerivAt (fun w => pcfU a (-w)) (-pcfUDeriv a (-z)) z := by
  have h := (hasDerivAt_pcfU a (-z)).comp z (hasDerivAt_neg z)
  exact h.congr_deriv (by ring)

/-- The derivative of `w ↦ U(b, iw)` is `i U'(b, iz)`. -/
theorem hasDerivAt_pcfU_mul_I (b z : ℂ) :
    HasDerivAt (fun w => pcfU b (I * w)) (I * pcfUDeriv b (I * z)) z := by
  have h := (hasDerivAt_pcfU b (I * z)).comp z ((hasDerivAt_id z).const_mul I)
  exact h.congr_deriv (by ring)

/-- The derivative of `w ↦ U(b, -iw)` is `-i U'(b, -iz)`. -/
theorem hasDerivAt_pcfU_mul_neg_I (b z : ℂ) :
    HasDerivAt (fun w => pcfU b (-I * w)) (-I * pcfUDeriv b (-I * z)) z := by
  have h := (hasDerivAt_pcfU b (-I * z)).comp z ((hasDerivAt_id z).const_mul (-I))
  exact h.congr_deriv (by ring)

/-- `U(a,-z)` solves Weber's equation `w'' = (z²/4 + a) w`. -/
theorem isWeberSol_pcfU_neg (a : ℂ) :
    IsWeberSol a (fun w => pcfU a (-w)) (fun w => -pcfUDeriv a (-w)) := fun z => by
  refine ⟨hasDerivAt_pcfU_neg a z, ?_⟩
  have h := ((hasDerivAt_pcfUDeriv a (-z)).comp z (hasDerivAt_neg z)).neg
  exact h.congr_deriv (by ring)

/-- `U(-a, iz)` solves Weber's equation `w'' = (z²/4 + a) w`. -/
theorem isWeberSol_pcfU_mul_I (a : ℂ) :
    IsWeberSol a (fun w => pcfU (-a) (I * w)) (fun w => I * pcfUDeriv (-a) (I * w)) :=
  fun z => by
  refine ⟨hasDerivAt_pcfU_mul_I (-a) z, ?_⟩
  have h := ((hasDerivAt_pcfUDeriv (-a) (I * z)).comp z
    ((hasDerivAt_id z).const_mul I)).const_mul I
  have hI4 : I ^ 4 = 1 := by
    rw [show 4 = 2 * 2 from rfl, pow_mul, Complex.I_sq]; norm_num
  refine h.congr_deriv ?_
  ring_nf
  simp only [hI4, Complex.I_sq]
  ring

/-- `U(-a, -iz)` solves Weber's equation `w'' = (z²/4 + a) w`. -/
theorem isWeberSol_pcfU_mul_neg_I (a : ℂ) :
    IsWeberSol a (fun w => pcfU (-a) (-I * w)) (fun w => -I * pcfUDeriv (-a) (-I * w)) :=
  fun z => by
  refine ⟨hasDerivAt_pcfU_mul_neg_I (-a) z, ?_⟩
  have h := ((hasDerivAt_pcfUDeriv (-a) (-I * z)).comp z
    ((hasDerivAt_id z).const_mul (-I))).const_mul (-I)
  have hI4 : I ^ 4 = 1 := by
    rw [show 4 = 2 * 2 from rfl, pow_mul, Complex.I_sq]; norm_num
  refine h.congr_deriv ?_
  ring_nf
  simp only [hI4, Complex.I_sq]
  ring

/-- **Wronskian** (DLMF 12.2.11): `𝒲{U(a,z), U(a,-z)} = √(2π)/Γ(1/2 + a)`. -/
@[dlmf 12.2.E11]
theorem pcfU_wronskian_neg (a z : ℂ) :
    pcfU a z * deriv (fun w => pcfU a (-w)) z - deriv (pcfU a) z * pcfU a (-z) =
      (Real.sqrt (2 * π) : ℂ) / Gamma (1 / 2 + a) := by
  rw [(hasDerivAt_pcfU_neg a z).deriv, deriv_pcfU]
  have hW := (isWeberSol_pcfU a).wronskian_eq (isWeberSol_pcfU_neg a) z
  simp only [neg_zero] at hW
  rw [hW, pcfU_zero', pcfUDeriv_zero']
  have hd := Complex.Gamma_mul_Gamma_add_half (1 / 4 + a / 2)
  rw [show 1 / 4 + a / 2 + 1 / 2 = 3 / 4 + a / 2 by ring,
    show 2 * (1 / 4 + a / 2) = 1 / 2 + a by ring,
    show 1 - (1 / 2 + a) = 1 / 2 - a by ring] at hd
  have hinv : (Gamma (3 / 4 + a / 2))⁻¹ * (Gamma (1 / 4 + a / 2))⁻¹ =
      (Gamma (1 / 2 + a))⁻¹ * ((2 : ℂ) ^ (1 / 2 - a))⁻¹ * (Real.sqrt π : ℂ)⁻¹ := by
    rw [← mul_inv, mul_comm, hd, mul_inv, mul_inv]
  have hP : (2 : ℂ) ^ (-(a / 2 + 1 / 4)) * 2 ^ (-(a / 2 - 1 / 4)) * (Real.sqrt 2 : ℂ) =
      2 ^ (1 / 2 - a) := by
    rw [← two_cpow_half, ← Complex.cpow_add _ _ two_ne_zero,
      ← Complex.cpow_add _ _ two_ne_zero]
    ring_nf
  have hπ : (Real.sqrt π : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hT : (2 : ℂ) ^ (1 / 2 - a) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl two_ne_zero)
  have h2π : (Real.sqrt (2 * π) : ℂ) = (Real.sqrt 2 : ℂ) * (Real.sqrt π : ℂ) := by
    rw [Real.sqrt_mul (by norm_num), Complex.ofReal_mul]
  have hππ : (Real.sqrt π : ℂ) * (Real.sqrt π : ℂ) = π := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
  have h22 : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  have e : (Real.sqrt π : ℂ) * 2 ^ (-(a / 2 + 1 / 4)) * (Gamma (3 / 4 + a / 2))⁻¹ *
        -(-((Real.sqrt π : ℂ) * 2 ^ (-(a / 2 - 1 / 4)) * (Gamma (1 / 4 + a / 2))⁻¹)) -
      -((Real.sqrt π : ℂ) * 2 ^ (-(a / 2 - 1 / 4)) * (Gamma (1 / 4 + a / 2))⁻¹) *
        ((Real.sqrt π : ℂ) * 2 ^ (-(a / 2 + 1 / 4)) * (Gamma (3 / 4 + a / 2))⁻¹) =
      2 * ((Real.sqrt π : ℂ) * (Real.sqrt π : ℂ)) *
        ((2 : ℂ) ^ (-(a / 2 + 1 / 4)) * 2 ^ (-(a / 2 - 1 / 4))) *
        ((Gamma (3 / 4 + a / 2))⁻¹ * (Gamma (1 / 4 + a / 2))⁻¹) := by ring
  rw [e, hinv, h2π, div_eq_mul_inv ((Real.sqrt 2 : ℂ) * (Real.sqrt π : ℂ))]
  generalize (Gamma (1 / 2 + a))⁻¹ = A
  generalize hQ : (2 : ℂ) ^ (-(a / 2 + 1 / 4)) * 2 ^ (-(a / 2 - 1 / 4)) = Q at hP
  generalize (2 : ℂ) ^ (1 / 2 - a) = T at hP hT
  rw [← hP]
  have hs2 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    intro h; rw [h, zero_mul] at h22; norm_num at h22
  have hQ0 : Q ≠ 0 := by rintro rfl; rw [zero_mul] at hP; exact hT hP.symm
  field_simp
  linear_combination (-A) * h22

/-- Euler's reflection formula for reciprocals, valid for every complex `s`. -/
theorem pi_mul_recip_Gamma_mul_recip_Gamma (s : ℂ) :
    (π : ℂ) * ((Gamma s)⁻¹ * (Gamma (1 - s))⁻¹) = Complex.sin (π * s) := by
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [← mul_inv, Complex.Gamma_mul_Gamma_one_sub, inv_div]
  field_simp

/-- **Wronskians** (DLMF 12.2.12, upper signs):
`𝒲{U(a,z), U(-a,iz)} = -i e^{iπ(a/2 + 1/4)}`, as printed in the DLMF. -/
@[dlmf 12.2.E12]
theorem pcfU_wronskian_mul_I (a z : ℂ) :
    pcfU a z * deriv (fun w => pcfU (-a) (I * w)) z - deriv (pcfU a) z * pcfU (-a) (I * z) =
      -I * exp (I * π * (a / 2 + 1 / 4)) := by
  rw [(hasDerivAt_pcfU_mul_I (-a) z).deriv, deriv_pcfU]
  have hW := (isWeberSol_pcfU a).wronskian_eq (isWeberSol_pcfU_mul_I a) z
  simp only [mul_zero] at hW
  rw [hW, pcfU_zero' a, pcfUDeriv_zero' (-a), pcfUDeriv_zero' a, pcfU_zero' (-a),
    show (1 / 4 + -a / 2 : ℂ) = 1 / 4 - a / 2 by ring,
    show (3 / 4 + -a / 2 : ℂ) = 3 / 4 - a / 2 by ring]
  have q1 := pi_mul_recip_Gamma_mul_recip_Gamma (1 / 4 - a / 2)
  rw [show 1 - (1 / 4 - a / 2) = 3 / 4 + a / 2 by ring] at q1
  have q2 := pi_mul_recip_Gamma_mul_recip_Gamma (1 / 4 + a / 2)
  rw [show 1 - (1 / 4 + a / 2) = 3 / 4 - a / 2 by ring,
    show (π : ℂ) * (1 / 4 + a / 2) = π * (a / 2 + 1 / 4) by ring] at q2
  have hc : Complex.sin (π * (1 / 4 - a / 2)) = Complex.cos (π * (a / 2 + 1 / 4)) := by
    rw [← Complex.sin_pi_div_two_sub]; ring_nf
  have hexp : exp (I * π * (a / 2 + 1 / 4)) =
      Complex.cos (π * (a / 2 + 1 / 4)) + Complex.sin (π * (a / 2 + 1 / 4)) * I := by
    rw [← Complex.exp_mul_I]; ring_nf
  have p1 : (2 : ℂ) ^ (-(a / 2 + 1 / 4)) * 2 ^ (-(-a / 2 - 1 / 4)) = 1 := by
    rw [← Complex.cpow_add _ _ two_ne_zero, show -(a / 2 + 1 / 4) + -(-a / 2 - 1 / 4) = 0 by ring,
      Complex.cpow_zero]
  have p2 : (2 : ℂ) ^ (-(a / 2 - 1 / 4)) * 2 ^ (-(-a / 2 + 1 / 4)) = 1 := by
    rw [← Complex.cpow_add _ _ two_ne_zero, show -(a / 2 - 1 / 4) + -(-a / 2 + 1 / 4) = 0 by ring,
      Complex.cpow_zero]
  have hππ : (Real.sqrt π : ℂ) * (Real.sqrt π : ℂ) = π := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
  rw [hexp]
  set X1 := (2 : ℂ) ^ (-(a / 2 + 1 / 4)) * 2 ^ (-(-a / 2 - 1 / 4))
  set X2 := (2 : ℂ) ^ (-(a / 2 - 1 / 4)) * 2 ^ (-(-a / 2 + 1 / 4))
  set Y1 := (Gamma (1 / 4 - a / 2))⁻¹ * (Gamma (3 / 4 + a / 2))⁻¹
  set Y2 := (Gamma (1 / 4 + a / 2))⁻¹ * (Gamma (3 / 4 - a / 2))⁻¹
  linear_combination (-I * X1 * Y1 + X2 * Y2) * hππ - I * π * Y1 * p1 - I * q1 - I * hc +
    π * Y2 * p2 + q2 + Complex.sin (π * (a / 2 + 1 / 4)) * Complex.I_sq

/-- **Wronskians** (DLMF 12.2.12, lower signs):
`𝒲{U(a,z), U(-a,-iz)} = i e^{-iπ(a/2 + 1/4)}`. -/
@[dlmf 12.2.E12]
theorem pcfU_wronskian_mul_neg_I (a z : ℂ) :
    pcfU a z * deriv (fun w => pcfU (-a) (-I * w)) z - deriv (pcfU a) z * pcfU (-a) (-I * z) =
      I * exp (-I * π * (a / 2 + 1 / 4)) := by
  rw [(hasDerivAt_pcfU_mul_neg_I (-a) z).deriv, deriv_pcfU]
  have hW := (isWeberSol_pcfU a).wronskian_eq (isWeberSol_pcfU_mul_neg_I a) z
  simp only [mul_zero] at hW
  rw [hW, pcfU_zero' a, pcfUDeriv_zero' (-a), pcfUDeriv_zero' a, pcfU_zero' (-a),
    show (1 / 4 + -a / 2 : ℂ) = 1 / 4 - a / 2 by ring,
    show (3 / 4 + -a / 2 : ℂ) = 3 / 4 - a / 2 by ring]
  have q1 := pi_mul_recip_Gamma_mul_recip_Gamma (1 / 4 - a / 2)
  rw [show 1 - (1 / 4 - a / 2) = 3 / 4 + a / 2 by ring] at q1
  have q2 := pi_mul_recip_Gamma_mul_recip_Gamma (1 / 4 + a / 2)
  rw [show 1 - (1 / 4 + a / 2) = 3 / 4 - a / 2 by ring,
    show (π : ℂ) * (1 / 4 + a / 2) = π * (a / 2 + 1 / 4) by ring] at q2
  have hc : Complex.sin (π * (1 / 4 - a / 2)) = Complex.cos (π * (a / 2 + 1 / 4)) := by
    rw [← Complex.sin_pi_div_two_sub]; ring_nf
  have hexp : exp (-I * π * (a / 2 + 1 / 4)) =
      Complex.cos (π * (a / 2 + 1 / 4)) - Complex.sin (π * (a / 2 + 1 / 4)) * I := by
    rw [show -I * π * (a / 2 + 1 / 4) = (-(π * (a / 2 + 1 / 4))) * I by ring,
      Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
    ring
  have p1 : (2 : ℂ) ^ (-(a / 2 + 1 / 4)) * 2 ^ (-(-a / 2 - 1 / 4)) = 1 := by
    rw [← Complex.cpow_add _ _ two_ne_zero, show -(a / 2 + 1 / 4) + -(-a / 2 - 1 / 4) = 0 by ring,
      Complex.cpow_zero]
  have p2 : (2 : ℂ) ^ (-(a / 2 - 1 / 4)) * 2 ^ (-(-a / 2 + 1 / 4)) = 1 := by
    rw [← Complex.cpow_add _ _ two_ne_zero, show -(a / 2 - 1 / 4) + -(-a / 2 + 1 / 4) = 0 by ring,
      Complex.cpow_zero]
  have hππ : (Real.sqrt π : ℂ) * (Real.sqrt π : ℂ) = π := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
  rw [hexp]
  set X1 := (2 : ℂ) ^ (-(a / 2 + 1 / 4)) * 2 ^ (-(-a / 2 - 1 / 4))
  set X2 := (2 : ℂ) ^ (-(a / 2 - 1 / 4)) * 2 ^ (-(-a / 2 + 1 / 4))
  set Y1 := (Gamma (1 / 4 - a / 2))⁻¹ * (Gamma (3 / 4 + a / 2))⁻¹
  set Y2 := (Gamma (1 / 4 + a / 2))⁻¹ * (Gamma (3 / 4 - a / 2))⁻¹
  linear_combination (I * X1 * Y1 + X2 * Y2) * hππ + I * π * Y1 * p1 + I * q1 + I * hc +
    π * Y2 * p2 + q2 + Complex.sin (π * (a / 2 + 1 / 4)) * Complex.I_sq

/-! ### Connection formula 12.2.17 -/

/-- Linear combinations of solutions of Weber's equation are solutions. -/
theorem IsWeberSol.lincomb {a : ℂ} {f f' g g' : ℂ → ℂ} (hf : IsWeberSol a f f')
    (hg : IsWeberSol a g g') (c₁ c₂ : ℂ) :
    IsWeberSol a (fun w => c₁ * f w + c₂ * g w) (fun w => c₁ * f' w + c₂ * g' w) := fun z =>
  ⟨((hf z).1.const_mul c₁).add ((hg z).1.const_mul c₂),
    (((hf z).2.const_mul c₁).add ((hg z).2.const_mul c₂)).congr_deriv (by ring)⟩

/-- **Connection formula** (DLMF 12.2.17, upper signs):
`√(2π) U(-a, iz) = Γ(1/2 + a) (e^{-iπ(a/2 - 1/4)} U(a,z) + e^{iπ(a/2 - 1/4)} U(a,-z))`.
At the poles of `Γ(1/2 + a)` the bracket vanishes and the right side is a limit `∞ · 0`,
so those parameters are excluded. -/
@[dlmf 12.2.E17]
theorem pcfU_connection_mul_I {a : ℂ} (ha : ∀ n : ℕ, 1 / 2 + a ≠ -n) (z : ℂ) :
    (Real.sqrt (2 * π) : ℂ) * pcfU (-a) (I * z) = Gamma (1 / 2 + a) *
      (exp (-I * π * (a / 2 - 1 / 4)) * pcfU a z +
        exp (I * π * (a / 2 - 1 / 4)) * pcfU a (-z)) := by
  set A := Gamma (1 / 2 + a) with hA
  set e₁ := exp (-I * π * (a / 2 - 1 / 4)) with he₁d
  set e₂ := exp (I * π * (a / 2 - 1 / 4)) with he₂d
  have hf := (isWeberSol_pcfU_mul_I a).lincomb (isWeberSol_pcfU_mul_I a)
    (Real.sqrt (2 * π) : ℂ) 0
  have hg := ((isWeberSol_pcfU a).lincomb (isWeberSol_pcfU_neg a) (A * e₁) (A * e₂))
  have hd := Complex.Gamma_mul_Gamma_add_half (1 / 4 + a / 2)
  rw [show 1 / 4 + a / 2 + 1 / 2 = 3 / 4 + a / 2 by ring,
    show 2 * (1 / 4 + a / 2) = 1 / 2 + a by ring,
    show 1 - (1 / 2 + a) = 1 / 2 - a by ring, ← hA] at hd
  have hπ : (Real.sqrt π : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hT : (2 : ℂ) ^ (1 / 2 - a) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl two_ne_zero)
  have hA0 : A ≠ 0 := Complex.Gamma_ne_zero ha
  have hprod : Gamma (1 / 4 + a / 2) * Gamma (3 / 4 + a / 2) ≠ 0 := by
    rw [hd]; exact mul_ne_zero (mul_ne_zero hA0 hT) hπ
  have hΓ1 : Gamma (1 / 4 + a / 2) ≠ 0 := left_ne_zero_of_mul hprod
  have hΓ3 : Gamma (3 / 4 + a / 2) ≠ 0 := right_ne_zero_of_mul hprod
  have hAe : A = Gamma (1 / 4 + a / 2) * Gamma (3 / 4 + a / 2) /
      ((2 : ℂ) ^ (1 / 2 - a) * (Real.sqrt π : ℂ)) := by
    rw [hd]; field_simp
  have q1 := pi_mul_recip_Gamma_mul_recip_Gamma (1 / 4 - a / 2)
  rw [show 1 - (1 / 4 - a / 2) = 3 / 4 + a / 2 by ring] at q1
  have q2 := pi_mul_recip_Gamma_mul_recip_Gamma (1 / 4 + a / 2)
  rw [show 1 - (1 / 4 + a / 2) = 3 / 4 - a / 2 by ring] at q2
  have hcos : Complex.cos (π * (a / 2 - 1 / 4)) = Complex.sin (π * (1 / 4 + a / 2)) := by
    rw [← Complex.sin_add_pi_div_two]; ring_nf
  have hsin : Complex.sin (π * (a / 2 - 1 / 4)) = -Complex.sin (π * (1 / 4 - a / 2)) := by
    rw [← Complex.sin_neg]; ring_nf
  have he₁ : e₁ = Complex.cos (π * (a / 2 - 1 / 4)) - Complex.sin (π * (a / 2 - 1 / 4)) * I := by
    rw [he₁d, show -I * π * (a / 2 - 1 / 4) = (-(π * (a / 2 - 1 / 4))) * I by ring,
      Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
    ring
  have he₂ : e₂ = Complex.cos (π * (a / 2 - 1 / 4)) + Complex.sin (π * (a / 2 - 1 / 4)) * I := by
    rw [he₂d, show I * π * (a / 2 - 1 / 4) = (π * (a / 2 - 1 / 4)) * I by ring,
      Complex.exp_mul_I]
  rw [hcos, ← q2] at he₁ he₂
  rw [hsin, ← q1] at he₁ he₂
  have hππ : (Real.sqrt π : ℂ) * (Real.sqrt π : ℂ) = π := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
  have h2π : (Real.sqrt (2 * π) : ℂ) = (Real.sqrt 2 : ℂ) * (Real.sqrt π : ℂ) := by
    rw [Real.sqrt_mul (by norm_num), Complex.ofReal_mul]
  have hpow (x y : ℂ) (hxy : 1 / 2 + x + (1 / 2 - a) = 1 + y) :
      (Real.sqrt 2 : ℂ) * 2 ^ x * 2 ^ (1 / 2 - a) = 2 * 2 ^ y := by
    rw [← two_cpow_half, ← Complex.cpow_add _ _ two_ne_zero, ← Complex.cpow_add _ _ two_ne_zero,
      hxy, Complex.cpow_add _ _ two_ne_zero, Complex.cpow_one]
  have key := hf.eq_of_initial hg ?_ ?_ z
  · simp only [zero_mul, add_zero] at key
    rw [key]; ring
  · simp only [mul_zero, neg_zero, zero_mul, add_zero]
    rw [pcfU_zero' (-a), pcfU_zero' a, he₁, he₂, hAe, h2π,
      show (3 / 4 + -a / 2 : ℂ) = 3 / 4 - a / 2 by ring]
    have r := hpow (-(-a / 2 + 1 / 4)) (-(a / 2 + 1 / 4)) (by ring)
    generalize (Gamma (3 / 4 - a / 2))⁻¹ = m3
    generalize (Gamma (1 / 4 - a / 2))⁻¹ = m1
    generalize (2 : ℂ) ^ (1 / 2 - a) = T at hT r
    generalize Gamma (1 / 4 + a / 2) = B at hΓ1
    generalize Gamma (3 / 4 + a / 2) = C at hΓ3
    generalize (2 : ℂ) ^ (-(a / 2 + 1 / 4)) = P at r
    generalize (2 : ℂ) ^ (-(-a / 2 + 1 / 4)) = P' at r
    field_simp
    have hππ2 : (Real.sqrt π : ℂ) ^ 2 = π := by rw [sq, hππ]
    linear_combination ((Real.sqrt π : ℂ) ^ 2 * m3 * C) * r + (2 * P * m3 * C) * hππ2
  · simp only [mul_zero, neg_zero, zero_mul, add_zero]
    rw [pcfUDeriv_zero' (-a), pcfUDeriv_zero' a, he₁, he₂, hAe, h2π,
      show (1 / 4 + -a / 2 : ℂ) = 1 / 4 - a / 2 by ring]
    have r := hpow (-(-a / 2 - 1 / 4)) (-(a / 2 - 1 / 4)) (by ring)
    generalize (Gamma (3 / 4 - a / 2))⁻¹ = m3
    generalize (Gamma (1 / 4 - a / 2))⁻¹ = m1
    generalize (2 : ℂ) ^ (1 / 2 - a) = T at hT r
    generalize Gamma (1 / 4 + a / 2) = B at hΓ1
    generalize Gamma (3 / 4 + a / 2) = C at hΓ3
    generalize (2 : ℂ) ^ (-(a / 2 - 1 / 4)) = P at r
    generalize (2 : ℂ) ^ (-(-a / 2 - 1 / 4)) = P' at r
    field_simp
    have hππ2 : (Real.sqrt π : ℂ) ^ 2 = π := by rw [sq, hππ]
    linear_combination (-(Real.sqrt π : ℂ) ^ 2 * I * m1 * B) * r + (-2 * I * P * m1 * B) * hππ2

/-- **Connection formula** (DLMF 12.2.17, lower signs):
`√(2π) U(-a, -iz) = Γ(1/2 + a) (e^{-iπ(a/2 - 1/4)} U(a,-z) + e^{iπ(a/2 - 1/4)} U(a,z))`. -/
@[dlmf 12.2.E17]
theorem pcfU_connection_mul_neg_I {a : ℂ} (ha : ∀ n : ℕ, 1 / 2 + a ≠ -n) (z : ℂ) :
    (Real.sqrt (2 * π) : ℂ) * pcfU (-a) (-I * z) = Gamma (1 / 2 + a) *
      (exp (-I * π * (a / 2 - 1 / 4)) * pcfU a (-z) +
        exp (I * π * (a / 2 - 1 / 4)) * pcfU a z) := by
  have h := pcfU_connection_mul_I ha (-z)
  rwa [neg_neg, show I * -z = -I * z by ring] at h

/-! ### The second solution `V(a,z)` (DLMF 12.2, 12.4.2, 12.8) -/

/-- `V(a,·)` has derivative `pcfVDeriv a`. -/
theorem hasDerivAt_pcfV (a z : ℂ) : HasDerivAt (pcfV a) (pcfVDeriv a z) z :=
  ((hasDerivAt_pcfEven a z).const_mul _).add ((hasDerivAt_pcfOdd a z).const_mul _)

/-- Weber's equation (DLMF 12.2.2) for `V`. -/
@[dlmf 12.2.E2]
theorem hasDerivAt_pcfVDeriv (a z : ℂ) :
    HasDerivAt (pcfVDeriv a) ((z ^ 2 / 4 + a) * pcfV a z) z := by
  refine (((hasDerivAt_pcfEvenDeriv a z).const_mul _).add
    ((hasDerivAt_pcfOddDeriv a z).const_mul _)).congr_deriv ?_
  rw [pcfV]
  ring

/-- `V(a,z)` solves Weber's equation, with derivative `pcfVDeriv a`. -/
theorem isWeberSol_pcfV (a : ℂ) : IsWeberSol a (pcfV a) (pcfVDeriv a) :=
  fun z => ⟨hasDerivAt_pcfV a z, hasDerivAt_pcfVDeriv a z⟩

/-- `deriv (V(a,·)) = pcfVDeriv a`. -/
theorem deriv_pcfV (a : ℂ) : deriv (pcfV a) = pcfVDeriv a :=
  funext fun z => (hasDerivAt_pcfV a z).deriv

/-- The value `V(a,0)` is `pcfVZero a` (DLMF 12.2.8). -/
theorem pcfV_zero' (a : ℂ) : pcfV a 0 = pcfVZero a := by
  simp [pcfV, pcfEven_zero, pcfOdd_zero]

/-- The value `V'(a,0)` is `pcfVDerivZero a` (DLMF 12.2.9). -/
theorem pcfVDeriv_zero' (a : ℂ) : pcfVDeriv a 0 = pcfVDerivZero a := by
  simp [pcfVDeriv, pcfEvenDeriv_zero, pcfOddDeriv_zero]

/-- `V(a,0)` (DLMF 12.2.8). -/
@[dlmf 12.2.E8]
theorem pcfV_zero (a : ℂ) :
    pcfV a 0 = π * (2 : ℂ) ^ (a / 2 + 1 / 4) /
      (Gamma (3 / 4 - a / 2) ^ 2 * Gamma (1 / 4 + a / 2)) := by
  rw [pcfV_zero', pcfVZero]
  simp only [div_eq_mul_inv, mul_inv, inv_pow]
  ring

/-- `V'(a,0)` (DLMF 12.2.9). -/
@[dlmf 12.2.E9]
theorem pcfVDeriv_zero (a : ℂ) :
    pcfVDeriv a 0 = π * (2 : ℂ) ^ (a / 2 + 3 / 4) /
      (Gamma (1 / 4 - a / 2) ^ 2 * Gamma (3 / 4 + a / 2)) := by
  rw [pcfVDeriv_zero', pcfVDerivZero]
  simp only [div_eq_mul_inv, mul_inv, inv_pow]
  ring

/-- The derivative of `w ↦ V(a,-w)` is `-V'(a,-z)`. -/
theorem hasDerivAt_pcfV_neg (a z : ℂ) :
    HasDerivAt (fun w => pcfV a (-w)) (-pcfVDeriv a (-z)) z := by
  have h := (hasDerivAt_pcfV a (-z)).comp z (hasDerivAt_neg z)
  exact h.congr_deriv (by ring)

/-- `V(a,-z)` solves Weber's equation. -/
theorem isWeberSol_pcfV_neg (a : ℂ) :
    IsWeberSol a (fun w => pcfV a (-w)) (fun w => -pcfVDeriv a (-w)) := fun z => by
  refine ⟨hasDerivAt_pcfV_neg a z, ?_⟩
  have h := ((hasDerivAt_pcfVDeriv a (-z)).comp z (hasDerivAt_neg z)).neg
  exact h.congr_deriv (by ring)

/-- Legendre duplication for reciprocals, valid for every `a`:
`1/Γ(1/2 + a) = 2^{1/2-a} √π / (Γ(1/4 + a/2) Γ(3/4 + a/2))`. -/
theorem recip_Gamma_half_add (a : ℂ) :
    (Gamma (1 / 2 + a))⁻¹ = (Gamma (1 / 4 + a / 2))⁻¹ * (Gamma (3 / 4 + a / 2))⁻¹ *
      (2 : ℂ) ^ (1 / 2 - a) * (Real.sqrt π : ℂ) := by
  have hd := Complex.Gamma_mul_Gamma_add_half (1 / 4 + a / 2)
  rw [show 1 / 4 + a / 2 + 1 / 2 = 3 / 4 + a / 2 by ring,
    show 2 * (1 / 4 + a / 2) = 1 / 2 + a by ring,
    show 1 - (1 / 2 + a) = 1 / 2 - a by ring] at hd
  have hπ : (Real.sqrt π : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hT : (2 : ℂ) ^ (1 / 2 - a) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl two_ne_zero)
  rw [← mul_inv, hd, mul_inv, mul_inv]
  field_simp

/-- `sin(π(1/4 - a/2)) = cos(π(1/4 + a/2))`. -/
theorem sin_pi_quarter_sub (a : ℂ) :
    Complex.sin (π * (1 / 4 - a / 2)) = Complex.cos (π * (1 / 4 + a / 2)) := by
  rw [← Complex.sin_pi_div_two_sub]; ring_nf

/-- `sin(πa) = sin²(π(1/4 + a/2)) - cos²(π(1/4 + a/2))`. -/
theorem sin_pi_mul_eq_sq (a : ℂ) :
    Complex.sin (π * a) =
      Complex.sin (π * (1 / 4 + a / 2)) ^ 2 - Complex.cos (π * (1 / 4 + a / 2)) ^ 2 := by
  rw [show (π : ℂ) * a = 2 * (π * (1 / 4 + a / 2)) - π / 2 by ring,
    Complex.sin_sub_pi_div_two, Complex.cos_two_mul]
  linear_combination (-1 : ℂ) * Complex.sin_sq_add_cos_sq (π * (1 / 4 + a / 2))

/-- `cos(πa) = 2 sin(π(1/4 + a/2)) cos(π(1/4 + a/2))`. -/
theorem cos_pi_mul_eq_mul (a : ℂ) :
    Complex.cos (π * a) =
      2 * Complex.sin (π * (1 / 4 + a / 2)) * Complex.cos (π * (1 / 4 + a / 2)) := by
  rw [show (π : ℂ) * a = 2 * (π * (1 / 4 + a / 2)) - π / 2 by ring,
    Complex.cos_sub_pi_div_two, Complex.sin_two_mul]

/-- **Wronskian** (DLMF 12.2.10): `𝒲{U(a,z), V(a,z)} = √(2/π)`. -/
@[dlmf 12.2.E10]
theorem pcfV_wronskian (a z : ℂ) :
    pcfU a z * deriv (pcfV a) z - deriv (pcfU a) z * pcfV a z = (Real.sqrt (2 / π) : ℂ) := by
  rw [deriv_pcfV, deriv_pcfU]
  have hW := (isWeberSol_pcfU a).wronskian_eq (isWeberSol_pcfV a) z
  rw [hW, pcfU_zero', pcfUDeriv_zero', pcfV_zero', pcfVDeriv_zero', pcfVZero, pcfVDerivZero]
  have q1 := pi_mul_recip_Gamma_mul_recip_Gamma (1 / 4 - a / 2)
  rw [show 1 - (1 / 4 - a / 2) = 3 / 4 + a / 2 by ring, sin_pi_quarter_sub] at q1
  have q2 := pi_mul_recip_Gamma_mul_recip_Gamma (1 / 4 + a / 2)
  rw [show 1 - (1 / 4 + a / 2) = 3 / 4 - a / 2 by ring] at q2
  have htr := Complex.sin_sq_add_cos_sq (π * (1 / 4 + a / 2))
  have p1 : (2 : ℂ) ^ (-(a / 2 + 1 / 4)) * 2 ^ (a / 2 + 3 / 4) = (Real.sqrt 2 : ℂ) := by
    rw [← two_cpow_half, ← Complex.cpow_add _ _ two_ne_zero]; ring_nf
  have p2 : (2 : ℂ) ^ (-(a / 2 - 1 / 4)) * 2 ^ (a / 2 + 1 / 4) = (Real.sqrt 2 : ℂ) := by
    rw [← two_cpow_half, ← Complex.cpow_add _ _ two_ne_zero]; ring_nf
  have hππ : (Real.sqrt π : ℂ) * (Real.sqrt π : ℂ) = π := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
  have hR : (Real.sqrt (2 / π) : ℂ) * (Real.sqrt π : ℂ) = (Real.sqrt 2 : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.sqrt_mul (div_nonneg (by norm_num) Real.pi_pos.le),
      div_mul_cancel₀ _ Real.pi_ne_zero]
  have hπ0 : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  refine mul_left_cancel₀ hπ0 ?_
  set g1m := (Gamma (1 / 4 - a / 2))⁻¹
  set g3m := (Gamma (3 / 4 - a / 2))⁻¹
  set g1p := (Gamma (1 / 4 + a / 2))⁻¹
  set g3p := (Gamma (3 / 4 + a / 2))⁻¹
  set c := Complex.cos (π * (1 / 4 + a / 2))
  set s := Complex.sin (π * (1 / 4 + a / 2))
  set r := (Real.sqrt π : ℂ)
  set R := (Real.sqrt (2 / π) : ℂ)
  set t := (Real.sqrt 2 : ℂ)
  linear_combination (π ^ 2 * r * g3p ^ 2 * g1m ^ 2) * p1 + (π ^ 2 * r * g1p ^ 2 * g3m ^ 2) * p2
    + (r * t * (π * (g1m * g3p) + c)) * q1 + (r * t * (π * (g1p * g3m) + s)) * q2
    + (r * t) * htr + R * hππ - r * hR

/-- Duplication formula: `1/Γ(1/2 - a) = 2^{1/2+a} √π / (Γ(1/4 - a/2) Γ(3/4 - a/2))`. -/
theorem recip_Gamma_half_sub (a : ℂ) :
    (Gamma (1 / 2 - a))⁻¹ = (Gamma (1 / 4 - a / 2))⁻¹ * (Gamma (3 / 4 - a / 2))⁻¹ *
      (2 : ℂ) ^ (1 / 2 + a) * (Real.sqrt π : ℂ) := by
  have h := recip_Gamma_half_add (-a)
  rwa [show (1 / 2 + -a : ℂ) = 1 / 2 - a by ring, show (1 / 4 + -a / 2 : ℂ) = 1 / 4 - a / 2 by ring,
    show (3 / 4 + -a / 2 : ℂ) = 3 / 4 - a / 2 by ring,
    show (1 / 2 - -a : ℂ) = 1 / 2 + a by ring] at h

/-- `2^x 2^y = 2^z` when `x + y = z`. -/
theorem two_cpow_mul_two_cpow (x y z : ℂ) (h : x + y = z) :
    (2 : ℂ) ^ x * 2 ^ y = 2 ^ z := by
  rw [← Complex.cpow_add _ _ two_ne_zero, h]

/-- **Connection formula** (DLMF 12.2.15), valid for every `a`:
`U(a,-z) = -sin(πa) U(a,z) + π/Γ(1/2 + a) V(a,z)`. -/
@[dlmf 12.2.E15]
theorem pcfU_neg_eq (a z : ℂ) :
    pcfU a (-z) = -Complex.sin (π * a) * pcfU a z + π / Gamma (1 / 2 + a) * pcfV a z := by
  have hg := (isWeberSol_pcfU a).lincomb (isWeberSol_pcfV a) (-Complex.sin (π * a))
    (π / Gamma (1 / 2 + a))
  refine (isWeberSol_pcfU_neg a).eq_of_initial hg ?_ ?_ z
  · simp only [neg_zero]
    rw [pcfU_zero', pcfV_zero', pcfVZero, div_eq_mul_inv (π : ℂ) (Gamma (1 / 2 + a)),
      recip_Gamma_half_add, sin_pi_mul_eq_sq]
    have q2 := pi_mul_recip_Gamma_mul_recip_Gamma (1 / 4 + a / 2)
    rw [show 1 - (1 / 4 + a / 2) = 3 / 4 - a / 2 by ring] at q2
    have htr := Complex.sin_sq_add_cos_sq (π * (1 / 4 + a / 2))
    have pw : (2 : ℂ) ^ (1 / 2 - a) * 2 ^ (a / 2 + 1 / 4) = 2 * 2 ^ (-(a / 2 + 1 / 4)) := by
      rw [two_cpow_mul_two_cpow _ _ (-(a / 2 + 1 / 4) + 1) (by ring),
        Complex.cpow_add _ _ two_ne_zero, Complex.cpow_one]; ring
    set g3m := (Gamma (3 / 4 - a / 2))⁻¹
    set g1p := (Gamma (1 / 4 + a / 2))⁻¹
    set g3p := (Gamma (3 / 4 + a / 2))⁻¹
    set c := Complex.cos (π * (1 / 4 + a / 2))
    set s := Complex.sin (π * (1 / 4 + a / 2))
    set r := (Real.sqrt π : ℂ)
    set A := (2 : ℂ) ^ (-(a / 2 + 1 / 4))
    set B := (2 : ℂ) ^ (a / 2 + 1 / 4)
    set T := (2 : ℂ) ^ (1 / 2 - a)
    linear_combination (-(r * g3p * T * B) * (π * (g1p * g3m) + s)) * q2 +
      (-(r * g3p * s ^ 2)) * pw + (-(r * A * g3p)) * htr
  · simp only [neg_zero]
    rw [pcfUDeriv_zero', pcfVDeriv_zero', pcfVDerivZero,
      div_eq_mul_inv (π : ℂ) (Gamma (1 / 2 + a)), recip_Gamma_half_add, sin_pi_mul_eq_sq]
    have q1 := pi_mul_recip_Gamma_mul_recip_Gamma (1 / 4 - a / 2)
    rw [show 1 - (1 / 4 - a / 2) = 3 / 4 + a / 2 by ring, sin_pi_quarter_sub] at q1
    have htr := Complex.sin_sq_add_cos_sq (π * (1 / 4 + a / 2))
    have pw : (2 : ℂ) ^ (1 / 2 - a) * 2 ^ (a / 2 + 3 / 4) = 2 * 2 ^ (-(a / 2 - 1 / 4)) := by
      rw [two_cpow_mul_two_cpow _ _ (-(a / 2 - 1 / 4) + 1) (by ring),
        Complex.cpow_add _ _ two_ne_zero, Complex.cpow_one]; ring
    set g1m := (Gamma (1 / 4 - a / 2))⁻¹
    set g1p := (Gamma (1 / 4 + a / 2))⁻¹
    set g3p := (Gamma (3 / 4 + a / 2))⁻¹
    set c := Complex.cos (π * (1 / 4 + a / 2))
    set s := Complex.sin (π * (1 / 4 + a / 2))
    set r := (Real.sqrt π : ℂ)
    set A := (2 : ℂ) ^ (-(a / 2 - 1 / 4))
    set B := (2 : ℂ) ^ (a / 2 + 3 / 4)
    set T := (2 : ℂ) ^ (1 / 2 - a)
    linear_combination (-(r * g1p * T * B) * (π * (g1m * g3p) + c)) * q1 +
      (-(r * g1p * c ^ 2)) * pw + (-(r * A * g1p)) * htr

/-- **Connection formula** (DLMF 12.2.16), valid for every `a`:
`V(a,-z) = cos(πa)/Γ(1/2 - a) U(a,z) + sin(πa) V(a,z)`. -/
@[dlmf 12.2.E16]
theorem pcfV_neg_eq (a z : ℂ) :
    pcfV a (-z) = Complex.cos (π * a) / Gamma (1 / 2 - a) * pcfU a z +
      Complex.sin (π * a) * pcfV a z := by
  have hg := (isWeberSol_pcfU a).lincomb (isWeberSol_pcfV a)
    (Complex.cos (π * a) / Gamma (1 / 2 - a)) (Complex.sin (π * a))
  have q1 := pi_mul_recip_Gamma_mul_recip_Gamma (1 / 4 - a / 2)
  rw [show 1 - (1 / 4 - a / 2) = 3 / 4 + a / 2 by ring, sin_pi_quarter_sub] at q1
  have q2 := pi_mul_recip_Gamma_mul_recip_Gamma (1 / 4 + a / 2)
  rw [show 1 - (1 / 4 + a / 2) = 3 / 4 - a / 2 by ring] at q2
  have htr := Complex.sin_sq_add_cos_sq (π * (1 / 4 + a / 2))
  have hππ : (Real.sqrt π : ℂ) * (Real.sqrt π : ℂ) = π := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
  refine (isWeberSol_pcfV_neg a).eq_of_initial hg ?_ ?_ z
  · simp only [neg_zero]
    rw [pcfU_zero', pcfV_zero', pcfVZero, div_eq_mul_inv _ (Gamma (1 / 2 - a)),
      recip_Gamma_half_sub, sin_pi_mul_eq_sq, cos_pi_mul_eq_mul]
    have pw : (2 : ℂ) ^ (1 / 2 + a) * 2 ^ (-(a / 2 + 1 / 4)) = 2 ^ (a / 2 + 1 / 4) :=
      two_cpow_mul_two_cpow _ _ _ (by ring)
    set g1m := (Gamma (1 / 4 - a / 2))⁻¹
    set g3m := (Gamma (3 / 4 - a / 2))⁻¹
    set g1p := (Gamma (1 / 4 + a / 2))⁻¹
    set g3p := (Gamma (3 / 4 + a / 2))⁻¹
    set c := Complex.cos (π * (1 / 4 + a / 2))
    set s := Complex.sin (π * (1 / 4 + a / 2))
    set r := (Real.sqrt π : ℂ)
    set A := (2 : ℂ) ^ (-(a / 2 + 1 / 4))
    set B := (2 : ℂ) ^ (a / 2 + 1 / 4)
    set T := (2 : ℂ) ^ (1 / 2 + a)
    linear_combination (-2 * s * c * g1m * g3m * g3p * T * A) * hππ +
      (-2 * s * c * π * g1m * g3m * g3p) * pw + (-2 * s * c * B * g3m) * q1 +
      (B * g3m * (1 - s ^ 2 + c ^ 2)) * q2 + (-s * B * g3m) * htr
  · simp only [neg_zero]
    rw [pcfUDeriv_zero', pcfVDeriv_zero', pcfVDerivZero, div_eq_mul_inv _ (Gamma (1 / 2 - a)),
      recip_Gamma_half_sub, sin_pi_mul_eq_sq, cos_pi_mul_eq_mul]
    have pw : (2 : ℂ) ^ (1 / 2 + a) * 2 ^ (-(a / 2 - 1 / 4)) = 2 ^ (a / 2 + 3 / 4) :=
      two_cpow_mul_two_cpow _ _ _ (by ring)
    set g1m := (Gamma (1 / 4 - a / 2))⁻¹
    set g3m := (Gamma (3 / 4 - a / 2))⁻¹
    set g1p := (Gamma (1 / 4 + a / 2))⁻¹
    set g3p := (Gamma (3 / 4 + a / 2))⁻¹
    set c := Complex.cos (π * (1 / 4 + a / 2))
    set s := Complex.sin (π * (1 / 4 + a / 2))
    set r := (Real.sqrt π : ℂ)
    set A := (2 : ℂ) ^ (-(a / 2 - 1 / 4))
    set B := (2 : ℂ) ^ (a / 2 + 3 / 4)
    set T := (2 : ℂ) ^ (1 / 2 + a)
    linear_combination (2 * s * c * g1m * g3m * g1p * T * A) * hππ +
      (2 * s * c * π * g1m * g3m * g1p) * pw + (2 * s * c * B * g1m) * q2 +
      (-(B * g1m * (1 + s ^ 2 - c ^ 2))) * q1 + (c * B * g1m) * htr

/-- `cos(nπ) = (-1)^n` for natural `n`. -/
theorem cos_nat_mul_pi' (n : ℕ) : Complex.cos (n * π) = (-1) ^ n := by
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul, ← Complex.ofReal_cos,
    Real.cos_nat_mul_pi]
  push_cast; ring

/-- Parity of `U` at the Hermite parameters (DLMF 12.2.13):
`U(-n - 1/2, -z) = (-1)ⁿ U(-n - 1/2, z)`. -/
@[dlmf 12.2.E13]
theorem pcfU_neg_nat_sub_half_neg (n : ℕ) (z : ℂ) :
    pcfU (-n - 1 / 2) (-z) = (-1) ^ n * pcfU (-n - 1 / 2) z := by
  rw [pcfU_neg_eq, show (1 / 2 + (-(n : ℂ) - 1 / 2)) = -(n : ℂ) by ring,
    Complex.Gamma_neg_nat_eq_zero, div_zero, zero_mul, add_zero,
    show (π : ℂ) * (-(n : ℂ) - 1 / 2) = -(n * π) - π / 2 by ring, Complex.sin_sub_pi_div_two,
    Complex.cos_neg, cos_nat_mul_pi']
  ring

/-- Parity of `V` at the parameters `n + 1/2` (DLMF 12.2.14):
`V(n + 1/2, -z) = (-1)ⁿ V(n + 1/2, z)`. -/
@[dlmf 12.2.E14]
theorem pcfV_nat_add_half_neg (n : ℕ) (z : ℂ) :
    pcfV (n + 1 / 2) (-z) = (-1) ^ n * pcfV (n + 1 / 2) z := by
  rw [pcfV_neg_eq, show (1 / 2 - ((n : ℂ) + 1 / 2)) = -(n : ℂ) by ring,
    Complex.Gamma_neg_nat_eq_zero, div_zero, zero_mul, zero_add,
    show (π : ℂ) * ((n : ℂ) + 1 / 2) = n * π + π / 2 by ring, Complex.sin_add_pi_div_two,
    cos_nat_mul_pi']

/-- The classical form of `V` (DLMF 12.2.15 solved for `V`):
`V(a,z) = Γ(1/2 + a)/π (sin(πa) U(a,z) + U(a,-z))`, away from the poles of `Γ(1/2 + a)`. -/
theorem pcfV_eq {a : ℂ} (ha : ∀ n : ℕ, 1 / 2 + a ≠ -n) (z : ℂ) :
    pcfV a z = Gamma (1 / 2 + a) / π * (Complex.sin (π * a) * pcfU a z + pcfU a (-z)) := by
  have hΓ := Complex.Gamma_ne_zero ha
  have hπ0 : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [pcfU_neg_eq, show Complex.sin (π * a) * pcfU a z +
      (-Complex.sin (π * a) * pcfU a z + π / Gamma (1 / 2 + a) * pcfV a z) =
      π / Gamma (1 / 2 + a) * pcfV a z by ring, ← mul_assoc, div_mul_div_comm,
    mul_comm (Gamma (1 / 2 + a)) (π : ℂ), div_self (mul_ne_zero hπ0 hΓ), one_mul]

/-- `exp(-iπ(a/2 - 1/4)) = sin(π(1/4 + a/2)) + i cos(π(1/4 + a/2))`. -/
theorem exp_neg_I_pi_quarter (a : ℂ) :
    exp (-I * π * (a / 2 - 1 / 4)) =
      Complex.sin (π * (1 / 4 + a / 2)) + Complex.cos (π * (1 / 4 + a / 2)) * I := by
  rw [show -I * π * (a / 2 - 1 / 4) = (-(π * (1 / 4 + a / 2) - π / 2)) * I by ring,
    Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg, Complex.cos_sub_pi_div_two,
    Complex.sin_sub_pi_div_two]
  ring

/-- `exp(iπ(a/2 - 1/4)) = sin(π(1/4 + a/2)) - i cos(π(1/4 + a/2))`. -/
theorem exp_I_pi_quarter (a : ℂ) :
    exp (I * π * (a / 2 - 1 / 4)) =
      Complex.sin (π * (1 / 4 + a / 2)) - Complex.cos (π * (1 / 4 + a / 2)) * I := by
  rw [show I * π * (a / 2 - 1 / 4) = (π * (1 / 4 + a / 2) - π / 2) * I by ring,
    Complex.exp_mul_I, Complex.cos_sub_pi_div_two, Complex.sin_sub_pi_div_two]
  ring

/-- **Connection formula** (DLMF 12.2.20, upper signs), valid for every `a`:
`V(a,z) = -i/Γ(1/2 - a) U(a,z) + √(2/π) e^{-iπ(a/2 - 1/4)} U(-a, iz)`. -/
@[dlmf 12.2.E20]
theorem pcfV_eq_mul_I (a z : ℂ) :
    pcfV a z = -I / Gamma (1 / 2 - a) * pcfU a z +
      (Real.sqrt (2 / π) : ℂ) * exp (-I * π * (a / 2 - 1 / 4)) * pcfU (-a) (I * z) := by
  have hg := (isWeberSol_pcfU a).lincomb (isWeberSol_pcfU_mul_I a) (-I / Gamma (1 / 2 - a))
    ((Real.sqrt (2 / π) : ℂ) * exp (-I * π * (a / 2 - 1 / 4)))
  have q1 := pi_mul_recip_Gamma_mul_recip_Gamma (1 / 4 - a / 2)
  rw [show 1 - (1 / 4 - a / 2) = 3 / 4 + a / 2 by ring, sin_pi_quarter_sub] at q1
  have q2 := pi_mul_recip_Gamma_mul_recip_Gamma (1 / 4 + a / 2)
  rw [show 1 - (1 / 4 + a / 2) = 3 / 4 - a / 2 by ring] at q2
  have hππ : (Real.sqrt π : ℂ) * (Real.sqrt π : ℂ) = π := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
  have hR : (Real.sqrt (2 / π) : ℂ) * (Real.sqrt π : ℂ) = (Real.sqrt 2 : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.sqrt_mul (div_nonneg (by norm_num) Real.pi_pos.le),
      div_mul_cancel₀ _ Real.pi_ne_zero]
  refine (isWeberSol_pcfV a).eq_of_initial hg ?_ ?_ z
  · simp only [mul_zero]
    rw [pcfV_zero', pcfVZero, pcfU_zero' a, pcfU_zero' (-a), div_eq_mul_inv _ (Gamma (1 / 2 - a)),
      recip_Gamma_half_sub, exp_neg_I_pi_quarter, show (3 / 4 + -a / 2 : ℂ) = 3 / 4 - a / 2 by ring]
    have pwA : (2 : ℂ) ^ (1 / 2 + a) * 2 ^ (-(a / 2 + 1 / 4)) = 2 ^ (a / 2 + 1 / 4) :=
      two_cpow_mul_two_cpow _ _ _ (by ring)
    have pwB : (Real.sqrt 2 : ℂ) * 2 ^ (-(-a / 2 + 1 / 4)) = 2 ^ (a / 2 + 1 / 4) := by
      rw [← two_cpow_half]; exact two_cpow_mul_two_cpow _ _ _ (by ring)
    set g1m := (Gamma (1 / 4 - a / 2))⁻¹
    set g3m := (Gamma (3 / 4 - a / 2))⁻¹
    set g1p := (Gamma (1 / 4 + a / 2))⁻¹
    set g3p := (Gamma (3 / 4 + a / 2))⁻¹
    set c := Complex.cos (π * (1 / 4 + a / 2))
    set s := Complex.sin (π * (1 / 4 + a / 2))
    set r := (Real.sqrt π : ℂ)
    set A := (2 : ℂ) ^ (-(a / 2 + 1 / 4))
    set A2 := (2 : ℂ) ^ (-(-a / 2 + 1 / 4))
    set B := (2 : ℂ) ^ (a / 2 + 1 / 4)
    set T := (2 : ℂ) ^ (1 / 2 + a)
    linear_combination (I * g1m * g3m * T * A * g3p) * hππ + (I * g1m * g3m * g3p * π) * pwA +
      (I * g3m * B) * q1 + (-(s + c * I) * A2 * g3m) * hR + (-(s + c * I) * g3m) * pwB +
      (B * g3m) * q2
  · simp only [mul_zero]
    rw [pcfVDeriv_zero', pcfVDerivZero, pcfUDeriv_zero' a, pcfUDeriv_zero' (-a),
      div_eq_mul_inv _ (Gamma (1 / 2 - a)), recip_Gamma_half_sub, exp_neg_I_pi_quarter,
      show (1 / 4 + -a / 2 : ℂ) = 1 / 4 - a / 2 by ring]
    have pwA : (2 : ℂ) ^ (1 / 2 + a) * 2 ^ (-(a / 2 - 1 / 4)) = 2 ^ (a / 2 + 3 / 4) :=
      two_cpow_mul_two_cpow _ _ _ (by ring)
    have pwB : (Real.sqrt 2 : ℂ) * 2 ^ (-(-a / 2 - 1 / 4)) = 2 ^ (a / 2 + 3 / 4) := by
      rw [← two_cpow_half]; exact two_cpow_mul_two_cpow _ _ _ (by ring)
    set g1m := (Gamma (1 / 4 - a / 2))⁻¹
    set g3m := (Gamma (3 / 4 - a / 2))⁻¹
    set g1p := (Gamma (1 / 4 + a / 2))⁻¹
    set g3p := (Gamma (3 / 4 + a / 2))⁻¹
    set c := Complex.cos (π * (1 / 4 + a / 2))
    set s := Complex.sin (π * (1 / 4 + a / 2))
    set r := (Real.sqrt π : ℂ)
    set A := (2 : ℂ) ^ (-(a / 2 - 1 / 4))
    set A2 := (2 : ℂ) ^ (-(-a / 2 - 1 / 4))
    set B := (2 : ℂ) ^ (a / 2 + 3 / 4)
    set T := (2 : ℂ) ^ (1 / 2 + a)
    linear_combination (-I * g1m * g3m * T * A * g1p) * hππ + (-I * g1m * g3m * g1p * π) * pwA +
      (-I * g1m * B) * q2 + ((s + c * I) * I * A2 * g1m) * hR + ((s + c * I) * I * g1m) * pwB +
      (c * B * g1m) * Complex.I_sq + (B * g1m) * q1

/-- **Connection formula** (DLMF 12.2.20, lower signs), valid for every `a`:
`V(a,z) = i/Γ(1/2 - a) U(a,z) + √(2/π) e^{iπ(a/2 - 1/4)} U(-a, -iz)`. -/
@[dlmf 12.2.E20]
theorem pcfV_eq_mul_neg_I (a z : ℂ) :
    pcfV a z = I / Gamma (1 / 2 - a) * pcfU a z +
      (Real.sqrt (2 / π) : ℂ) * exp (I * π * (a / 2 - 1 / 4)) * pcfU (-a) (-I * z) := by
  have hg := (isWeberSol_pcfU a).lincomb (isWeberSol_pcfU_mul_neg_I a) (I / Gamma (1 / 2 - a))
    ((Real.sqrt (2 / π) : ℂ) * exp (I * π * (a / 2 - 1 / 4)))
  have q1 := pi_mul_recip_Gamma_mul_recip_Gamma (1 / 4 - a / 2)
  rw [show 1 - (1 / 4 - a / 2) = 3 / 4 + a / 2 by ring, sin_pi_quarter_sub] at q1
  have q2 := pi_mul_recip_Gamma_mul_recip_Gamma (1 / 4 + a / 2)
  rw [show 1 - (1 / 4 + a / 2) = 3 / 4 - a / 2 by ring] at q2
  have hππ : (Real.sqrt π : ℂ) * (Real.sqrt π : ℂ) = π := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
  have hR : (Real.sqrt (2 / π) : ℂ) * (Real.sqrt π : ℂ) = (Real.sqrt 2 : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.sqrt_mul (div_nonneg (by norm_num) Real.pi_pos.le),
      div_mul_cancel₀ _ Real.pi_ne_zero]
  refine (isWeberSol_pcfV a).eq_of_initial hg ?_ ?_ z
  · simp only [mul_zero]
    rw [pcfV_zero', pcfVZero, pcfU_zero' a, pcfU_zero' (-a), div_eq_mul_inv _ (Gamma (1 / 2 - a)),
      recip_Gamma_half_sub, exp_I_pi_quarter, show (3 / 4 + -a / 2 : ℂ) = 3 / 4 - a / 2 by ring]
    have pwA : (2 : ℂ) ^ (1 / 2 + a) * 2 ^ (-(a / 2 + 1 / 4)) = 2 ^ (a / 2 + 1 / 4) :=
      two_cpow_mul_two_cpow _ _ _ (by ring)
    have pwB : (Real.sqrt 2 : ℂ) * 2 ^ (-(-a / 2 + 1 / 4)) = 2 ^ (a / 2 + 1 / 4) := by
      rw [← two_cpow_half]; exact two_cpow_mul_two_cpow _ _ _ (by ring)
    set g1m := (Gamma (1 / 4 - a / 2))⁻¹
    set g3m := (Gamma (3 / 4 - a / 2))⁻¹
    set g1p := (Gamma (1 / 4 + a / 2))⁻¹
    set g3p := (Gamma (3 / 4 + a / 2))⁻¹
    set c := Complex.cos (π * (1 / 4 + a / 2))
    set s := Complex.sin (π * (1 / 4 + a / 2))
    set r := (Real.sqrt π : ℂ)
    set A := (2 : ℂ) ^ (-(a / 2 + 1 / 4))
    set A2 := (2 : ℂ) ^ (-(-a / 2 + 1 / 4))
    set B := (2 : ℂ) ^ (a / 2 + 1 / 4)
    set T := (2 : ℂ) ^ (1 / 2 + a)
    linear_combination (-I * g1m * g3m * T * A * g3p) * hππ + (-I * g1m * g3m * g3p * π) * pwA +
      (-I * g3m * B) * q1 + (-(s - c * I) * A2 * g3m) * hR + (-(s - c * I) * g3m) * pwB +
      (B * g3m) * q2
  · simp only [mul_zero]
    rw [pcfVDeriv_zero', pcfVDerivZero, pcfUDeriv_zero' a, pcfUDeriv_zero' (-a),
      div_eq_mul_inv _ (Gamma (1 / 2 - a)), recip_Gamma_half_sub, exp_I_pi_quarter,
      show (1 / 4 + -a / 2 : ℂ) = 1 / 4 - a / 2 by ring]
    have pwA : (2 : ℂ) ^ (1 / 2 + a) * 2 ^ (-(a / 2 - 1 / 4)) = 2 ^ (a / 2 + 3 / 4) :=
      two_cpow_mul_two_cpow _ _ _ (by ring)
    have pwB : (Real.sqrt 2 : ℂ) * 2 ^ (-(-a / 2 - 1 / 4)) = 2 ^ (a / 2 + 3 / 4) := by
      rw [← two_cpow_half]; exact two_cpow_mul_two_cpow _ _ _ (by ring)
    set g1m := (Gamma (1 / 4 - a / 2))⁻¹
    set g3m := (Gamma (3 / 4 - a / 2))⁻¹
    set g1p := (Gamma (1 / 4 + a / 2))⁻¹
    set g3p := (Gamma (3 / 4 + a / 2))⁻¹
    set c := Complex.cos (π * (1 / 4 + a / 2))
    set s := Complex.sin (π * (1 / 4 + a / 2))
    set r := (Real.sqrt π : ℂ)
    set A := (2 : ℂ) ^ (-(a / 2 - 1 / 4))
    set A2 := (2 : ℂ) ^ (-(-a / 2 - 1 / 4))
    set B := (2 : ℂ) ^ (a / 2 + 3 / 4)
    set T := (2 : ℂ) ^ (1 / 2 + a)
    linear_combination (I * g1m * g3m * T * A * g1p) * hππ + (I * g1m * g3m * g1p * π) * pwA +
      (I * g1m * B) * q2 + (-(s - c * I) * I * A2 * g1m) * hR + (-(s - c * I) * I * g1m) * pwB +
      (c * B * g1m) * Complex.I_sq + (B * g1m) * q1

/-- DLMF 12.8.7: `V'(a,z) + (z/2) V(a,z) - V(a+1,z) = 0`. -/
@[dlmf 12.8.E7]
theorem pcfV_recurrence_add (a z : ℂ) :
    deriv (pcfV a) z + z / 2 * pcfV a z - pcfV (a + 1) z = 0 := by
  rw [deriv_pcfV]
  have hs : IsWeberSol (a + 1) (fun w => pcfVDeriv a w + w / 2 * pcfV a w - pcfV (a + 1) w)
      (fun w => (w ^ 2 / 4 + a) * pcfV a w + 1 / 2 * pcfV a w + w / 2 * pcfVDeriv a w -
        pcfVDeriv (a + 1) w) := fun w => by
    have hU := hasDerivAt_pcfV a w
    have hU' := hasDerivAt_pcfVDeriv a w
    have hV := hasDerivAt_pcfV (a + 1) w
    have hV' := hasDerivAt_pcfVDeriv (a + 1) w
    refine ⟨(hU'.add (((hasDerivAt_id w).div_const 2).mul hU)).sub hV |>.congr_deriv ?_, ?_⟩
    · simp only [id]; ring
    · refine ((((((hasDerivAt_pow 2 w).div_const 4).add_const a).mul hU).add
        (hU.const_mul (1 / 2))).add (((hasDerivAt_id w).div_const 2).mul hU')).sub hV'
        |>.congr_deriv ?_
      simp only [id]; push_cast; ring
  have h0 : pcfVDeriv a 0 + 0 / 2 * pcfV a 0 - pcfV (a + 1) 0 = 0 := by
    simp only [pcfVDeriv_zero', pcfV_zero', pcfVZero, pcfVDerivZero]
    rw [show 3 / 4 - (a + 1) / 2 = 1 / 4 - a / 2 by ring,
      show 1 / 4 + (a + 1) / 2 = 3 / 4 + a / 2 by ring,
      show (a + 1) / 2 + 1 / 4 = a / 2 + 3 / 4 by ring]
    ring
  have h1 : ((0 : ℂ) ^ 2 / 4 + a) * pcfV a 0 + 1 / 2 * pcfV a 0 + 0 / 2 * pcfVDeriv a 0 -
      pcfVDeriv (a + 1) 0 = 0 := by
    have hgA := mul_recip_Gamma_add_one' (-1 / 4 - a / 2)
    rw [show -1 / 4 - a / 2 + 1 = 3 / 4 - a / 2 by ring] at hgA
    have hgB := mul_recip_Gamma_add_one' (1 / 4 + a / 2)
    rw [show 1 / 4 + a / 2 + 1 = 5 / 4 + a / 2 by ring] at hgB
    have pw : (2 : ℂ) ^ (a / 2 + 5 / 4) = 2 * 2 ^ (a / 2 + 1 / 4) := by
      rw [show a / 2 + 5 / 4 = (a / 2 + 1 / 4) + 1 by ring, Complex.cpow_add _ _ two_ne_zero,
        Complex.cpow_one]; ring
    simp only [pcfVDeriv_zero', pcfV_zero', pcfVZero, pcfVDerivZero]
    rw [show 1 / 4 - (a + 1) / 2 = -1 / 4 - a / 2 by ring,
      show 3 / 4 + (a + 1) / 2 = 5 / 4 + a / 2 by ring,
      show (a + 1) / 2 + 3 / 4 = a / 2 + 5 / 4 by ring, ← hgA, ← hgB, pw]
    ring
  exact hs.eq_zero h0 h1 z

/-- DLMF 12.8.6: `V'(a,z) - (z/2) V(a,z) - (a - 1/2) V(a-1,z) = 0`. -/
@[dlmf 12.8.E6]
theorem pcfV_recurrence_sub (a z : ℂ) :
    deriv (pcfV a) z - z / 2 * pcfV a z - (a - 1 / 2) * pcfV (a - 1) z = 0 := by
  rw [deriv_pcfV]
  have hs : IsWeberSol (a - 1)
      (fun w => pcfVDeriv a w - w / 2 * pcfV a w - (a - 1 / 2) * pcfV (a - 1) w)
      (fun w => (w ^ 2 / 4 + a) * pcfV a w - 1 / 2 * pcfV a w - w / 2 * pcfVDeriv a w -
        (a - 1 / 2) * pcfVDeriv (a - 1) w) := fun w => by
    have hU := hasDerivAt_pcfV a w
    have hU' := hasDerivAt_pcfVDeriv a w
    have hV := hasDerivAt_pcfV (a - 1) w
    have hV' := hasDerivAt_pcfVDeriv (a - 1) w
    refine ⟨(hU'.sub (((hasDerivAt_id w).div_const 2).mul hU)).sub (hV.const_mul (a - 1 / 2))
      |>.congr_deriv ?_, ?_⟩
    · simp only [id]; ring
    · refine ((((((hasDerivAt_pow 2 w).div_const 4).add_const a).mul hU).sub
        (hU.const_mul (1 / 2))).sub (((hasDerivAt_id w).div_const 2).mul hU')).sub
        (hV'.const_mul (a - 1 / 2)) |>.congr_deriv ?_
      simp only [id]; push_cast; ring
  have h0 : pcfVDeriv a 0 - 0 / 2 * pcfV a 0 - (a - 1 / 2) * pcfV (a - 1) 0 = 0 := by
    have hgA := mul_recip_Gamma_add_one' (1 / 4 - a / 2)
    rw [show 1 / 4 - a / 2 + 1 = 5 / 4 - a / 2 by ring] at hgA
    have hgB := mul_recip_Gamma_add_one' (a / 2 - 1 / 4)
    rw [show a / 2 - 1 / 4 + 1 = 3 / 4 + a / 2 by ring] at hgB
    have pw : (2 : ℂ) ^ (a / 2 + 3 / 4) = 2 * 2 ^ (a / 2 - 1 / 4) := by
      rw [show a / 2 + 3 / 4 = (a / 2 - 1 / 4) + 1 by ring, Complex.cpow_add _ _ two_ne_zero,
        Complex.cpow_one]; ring
    simp only [pcfVDeriv_zero', pcfV_zero', pcfVZero, pcfVDerivZero]
    rw [show 3 / 4 - (a - 1) / 2 = 5 / 4 - a / 2 by ring,
      show 1 / 4 + (a - 1) / 2 = a / 2 - 1 / 4 by ring,
      show (a - 1) / 2 + 1 / 4 = a / 2 - 1 / 4 by ring, ← hgA, ← hgB, pw]
    ring
  have h1 : ((0 : ℂ) ^ 2 / 4 + a) * pcfV a 0 - 1 / 2 * pcfV a 0 - 0 / 2 * pcfVDeriv a 0 -
      (a - 1 / 2) * pcfVDeriv (a - 1) 0 = 0 := by
    simp only [pcfVDeriv_zero', pcfV_zero', pcfVZero, pcfVDerivZero]
    rw [show 1 / 4 - (a - 1) / 2 = 3 / 4 - a / 2 by ring,
      show 3 / 4 + (a - 1) / 2 = 1 / 4 + a / 2 by ring,
      show (a - 1) / 2 + 3 / 4 = a / 2 + 1 / 4 by ring]
    ring
  exact hs.eq_zero h0 h1 z

/-- DLMF 12.8.5: `z V(a,z) - V(a+1,z) + (a - 1/2) V(a-1,z) = 0`. -/
@[dlmf 12.8.E5]
theorem pcfV_three_term (a z : ℂ) :
    z * pcfV a z - pcfV (a + 1) z + (a - 1 / 2) * pcfV (a - 1) z = 0 := by
  linear_combination pcfV_recurrence_add a z - pcfV_recurrence_sub a z

/-- DLMF 12.8.8: `2 V'(a,z) - V(a+1,z) - (a - 1/2) V(a-1,z) = 0`. -/
@[dlmf 12.8.E8]
theorem pcfV_deriv_recurrence (a z : ℂ) :
    2 * deriv (pcfV a) z - pcfV (a + 1) z - (a - 1 / 2) * pcfV (a - 1) z = 0 := by
  linear_combination pcfV_recurrence_add a z + pcfV_recurrence_sub a z

end DLMF.Confluent

end
end
