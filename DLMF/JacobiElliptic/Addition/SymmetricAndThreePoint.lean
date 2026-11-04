/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
  -/
module

public import DLMF.JacobiElliptic.Addition.ThetaAndQuotients

/-!
# Symmetric and three-point Jacobi addition formulas

Alternative symmetric addition formulas for the Jacobian elliptic functions (DLMF
22.8.13–22.8.18), the four-point determinant and product identities (DLMF 22.8.19–22.8.23),
and the constant three-point and four-point expressions (DLMF 22.8.24–22.8.27).

## Main definitions

* `jacobiDnThreePointExpr`: the expression of DLMF 22.8.25 at `z₁`, with `z₂ = z₁ - 2K/3`,
  `z₃ = z₂ - 2K/3`.

## Main results

* `jacobiSn_add_alt`, `jacobiSn_add_alt₂`, `jacobiCn_add_alt`, `jacobiCn_add_alt₂`,
  `jacobiDn_add_alt`, `jacobiDn_add_alt₂`: the addition theorems DLMF 22.8.13–22.8.18, at
  points where the functions involved are finite.
* `jacobiSnCnDnk_add_sub`: the addition formulas at `u + v` and `u - v` with the common
  denominator.
* `jacobi_det_sum_zero`, `jacobi_prod_sum_zero`: the four-point identities DLMF 22.8.19–22.8.21
  for `z₁ + z₂ + z₃ + z₄ = 0`.
* `jacobi_det_sum_two_K`, `jacobi_det_sum_two_K'`: corrected forms of DLMF 22.8.22–22.8.23.
* `jacobiSnCnDnk_two_mul_completeEllipticK_div_three`: the values at `2K/3` and `4K/3`.
* `jacobiDnThreePointExpr_const`: DLMF 22.8.24–22.8.25, proved from the values at `2K/3` and
  the addition theorem.
* `jacobiDn_four_point`: DLMF 22.8.26–22.8.27, from Table 22.4.3.

## Implementation notes

**Correction.** DLMF 22.8.23 as printed (columns `sn cn, cn dn, cn, dn` with
`z₁ + z₂ + z₃ + z₄ = 2K`) fails numerically (e.g. `k = 0.6`, determinant `≈ -0.107 + 0.033i`).
Replacing the third column by `sn`, or the second by `sn dn`, gives true identities; both are
stated (`jacobi_det_sum_two_K`, `jacobi_det_sum_two_K'`).
  -/

@[expose] public section

open Complex DLMF.Elliptic

open scoped Real

noncomputable section

namespace DLMF.JacobiElliptic

open DLMF.EllipticIntegrals (completeEllipticK completeEllipticKPrime)

local notation "θ₁" => jacobiThetaOneTau

local notation "θ₂" => jacobiThetaTwoTau

local notation "θ₃" => jacobiThetaThreeTau

local notation "θ₄" => jacobiThetaFourTau

/-- DLMF 22.8.13: an addition theorem for `sn`, at points `u`, `v` where the functions
`·n` are finite (`IsJacobiRegular .n`) and the printed denominator is nonzero. -/
@[dlmf 22.8.E13]
theorem jacobiSn_add_alt {k : ℂ} (hk : k ∈ jacobiModulusDomain) {u v : ℂ}
    (hu : IsJacobiRegular .n u k) (hv : IsJacobiRegular .n v k)
    (hden : jacobiSn u k * jacobiCn v k * jacobiDn v k -
      jacobiSn v k * jacobiCn u k * jacobiDn u k ≠ 0) :
    jacobiSn (u + v) k =
      (jacobiSn u k ^ 2 - jacobiSn v k ^ 2) / (jacobiSn u k * jacobiCn v k * jacobiDn v k -
        jacobiSn v k * jacobiCn u k * jacobiDn u k) := by
  have hτ := jacobiTau_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  have hu' : θ₄ (jacobiThetaArgument u k) (jacobiTau k) ≠ 0 := by
    intro h'; apply hu; simp [jacobiLetterTheta, h']
  have hv' : θ₄ (jacobiThetaArgument v k) (jacobiTau k) ≠ 0 := by
    intro h'; apply hv; simp [jacobiLetterTheta, h']
  rw [eq_div_iff hden]
  simp only [jacobiSn, jacobiCn, jacobiDn, jacobiPQ, jacobiGlaisher, jacobiLetterTheta,
    reduceCtorEq, ↓reduceIte] at hden ⊢
  rw [jacobiThetaArgument_add]
  rw [jacobiModulusOfTau] at hmod
  generalize jacobiThetaArgument u k = x at hu' hden ⊢
  generalize jacobiThetaArgument v k = y at hv' hden ⊢
  generalize jacobiTau k = τ at hτ hu' hv' hden hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := jacobiThetaTau_zero_ne_zero_and_pow_four τ hτ
  have hD : (θ₄ (x + y) τ * θ₁ (x - y) τ) ≠ 0 := by
    intro h0; apply hden
    field_simp
    linear_combination θ₄ 0 τ ^ 2 *
        (-jacobiThetaFourTau_add_mul_jacobiThetaOneTau_sub x y τ hτ + θ₂ 0 τ * θ₃ 0 τ * h0)
  have hp := left_ne_zero_of_mul hD
  field_simp
  linear_combination (-(θ₄ 0 τ ^ 2 * θ₁ (x + y) τ)) *
      jacobiThetaFourTau_add_mul_jacobiThetaOneTau_sub x y τ hτ +
    (θ₃ 0 τ * θ₂ 0 τ * θ₄ (x + y) τ) * jacobiThetaOneTau_add_mul_jacobiThetaOneTau_sub_four x y τ hτ

/-- DLMF 22.8.14: an addition theorem for `sn`, at points `u`, `v` where the functions
`·n` are finite (`IsJacobiRegular .n`) and the printed denominator is nonzero. -/
@[dlmf 22.8.E14]
theorem jacobiSn_add_alt₂ {k : ℂ} (hk : k ∈ jacobiModulusDomain) {u v : ℂ}
    (hu : IsJacobiRegular .n u k) (hv : IsJacobiRegular .n v k)
    (hden : jacobiCn u k * jacobiCn v k +
      jacobiSn u k * jacobiDn u k * jacobiSn v k * jacobiDn v k ≠ 0) :
    jacobiSn (u + v) k =
      (jacobiSn u k * jacobiCn u k * jacobiDn v k + jacobiSn v k * jacobiCn v k *
        jacobiDn u k) / (jacobiCn u k * jacobiCn v k + jacobiSn u k * jacobiDn u k *
          jacobiSn v k * jacobiDn v k) := by
  have hτ := jacobiTau_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  have hu' : θ₄ (jacobiThetaArgument u k) (jacobiTau k) ≠ 0 := by
    intro h'; apply hu; simp [jacobiLetterTheta, h']
  have hv' : θ₄ (jacobiThetaArgument v k) (jacobiTau k) ≠ 0 := by
    intro h'; apply hv; simp [jacobiLetterTheta, h']
  rw [eq_div_iff hden]
  simp only [jacobiSn, jacobiCn, jacobiDn, jacobiPQ, jacobiGlaisher, jacobiLetterTheta,
    reduceCtorEq, ↓reduceIte] at hden ⊢
  rw [jacobiThetaArgument_add]
  rw [jacobiModulusOfTau] at hmod
  generalize jacobiThetaArgument u k = x at hu' hden ⊢
  generalize jacobiThetaArgument v k = y at hv' hden ⊢
  generalize jacobiTau k = τ at hτ hu' hv' hden hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := jacobiThetaTau_zero_ne_zero_and_pow_four τ hτ
  have hD : (θ₄ (x + y) τ * θ₂ (x - y) τ) ≠ 0 := by
    intro h0; apply hden
    field_simp
    linear_combination θ₄ 0 τ ^ 2 *
        (-jacobiThetaFourTau_add_mul_jacobiThetaTwoTau_sub x y τ hτ + θ₂ 0 τ * θ₄ 0 τ * h0)
  have hp := left_ne_zero_of_mul hD
  field_simp
  linear_combination (-(θ₃ 0 τ * θ₁ (x + y) τ)) *
      jacobiThetaFourTau_add_mul_jacobiThetaTwoTau_sub x y τ hτ +
    (θ₂ 0 τ * θ₄ (x + y) τ) * jacobiThetaOneTau_add_mul_jacobiThetaTwoTau_sub x y τ hτ

/-- DLMF 22.8.15: an addition theorem for `cn`, at points `u`, `v` where the functions
`·n` are finite (`IsJacobiRegular .n`) and the printed denominator is nonzero. -/
@[dlmf 22.8.E15]
theorem jacobiCn_add_alt {k : ℂ} (hk : k ∈ jacobiModulusDomain) {u v : ℂ}
    (hu : IsJacobiRegular .n u k) (hv : IsJacobiRegular .n v k)
    (hden : jacobiSn u k * jacobiCn v k * jacobiDn v k -
      jacobiSn v k * jacobiCn u k * jacobiDn u k ≠ 0) :
    jacobiCn (u + v) k =
      (jacobiSn u k * jacobiCn u k * jacobiDn v k - jacobiSn v k * jacobiCn v k *
        jacobiDn u k) / (jacobiSn u k * jacobiCn v k * jacobiDn v k - jacobiSn v k *
          jacobiCn u k * jacobiDn u k) := by
  have hτ := jacobiTau_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  have hu' : θ₄ (jacobiThetaArgument u k) (jacobiTau k) ≠ 0 := by
    intro h'; apply hu; simp [jacobiLetterTheta, h']
  have hv' : θ₄ (jacobiThetaArgument v k) (jacobiTau k) ≠ 0 := by
    intro h'; apply hv; simp [jacobiLetterTheta, h']
  rw [eq_div_iff hden]
  simp only [jacobiSn, jacobiCn, jacobiDn, jacobiPQ, jacobiGlaisher, jacobiLetterTheta,
    reduceCtorEq, ↓reduceIte] at hden ⊢
  rw [jacobiThetaArgument_add]
  rw [jacobiModulusOfTau] at hmod
  generalize jacobiThetaArgument u k = x at hu' hden ⊢
  generalize jacobiThetaArgument v k = y at hv' hden ⊢
  generalize jacobiTau k = τ at hτ hu' hv' hden hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := jacobiThetaTau_zero_ne_zero_and_pow_four τ hτ
  have hD : (θ₄ (x + y) τ * θ₁ (x - y) τ) ≠ 0 := by
    intro h0; apply hden
    field_simp
    linear_combination θ₄ 0 τ ^ 2 *
        (-jacobiThetaFourTau_add_mul_jacobiThetaOneTau_sub x y τ hτ + θ₂ 0 τ * θ₃ 0 τ * h0)
  have hp := left_ne_zero_of_mul hD
  field_simp
  linear_combination (-(θ₄ 0 τ * θ₂ (x + y) τ)) *
      jacobiThetaFourTau_add_mul_jacobiThetaOneTau_sub x y τ hτ +
    (θ₂ 0 τ * θ₄ (x + y) τ) * jacobiThetaTwoTau_add_mul_jacobiThetaOneTau_sub x y τ hτ

/-- DLMF 22.8.16: an addition theorem for `cn`, at points `u`, `v` where the functions
`·n` are finite (`IsJacobiRegular .n`) and the printed denominator is nonzero. -/
@[dlmf 22.8.E16]
theorem jacobiCn_add_alt₂ {k : ℂ} (hk : k ∈ jacobiModulusDomain) {u v : ℂ}
    (hu : IsJacobiRegular .n u k) (hv : IsJacobiRegular .n v k)
    (hden : jacobiCn u k * jacobiCn v k +
      jacobiSn u k * jacobiDn u k * jacobiSn v k * jacobiDn v k ≠ 0) :
    jacobiCn (u + v) k =
      (1 - jacobiSn u k ^ 2 - jacobiSn v k ^ 2 + k ^ 2 * jacobiSn u k ^ 2 * jacobiSn v k ^ 2) /
        (jacobiCn u k * jacobiCn v k + jacobiSn u k * jacobiDn u k * jacobiSn v k *
          jacobiDn v k) := by
  have hτ := jacobiTau_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  have hu' : θ₄ (jacobiThetaArgument u k) (jacobiTau k) ≠ 0 := by
    intro h'; apply hu; simp [jacobiLetterTheta, h']
  have hv' : θ₄ (jacobiThetaArgument v k) (jacobiTau k) ≠ 0 := by
    intro h'; apply hv; simp [jacobiLetterTheta, h']
  rw [eq_div_iff hden]
  simp only [jacobiSn, jacobiCn, jacobiDn, jacobiPQ, jacobiGlaisher, jacobiLetterTheta,
    reduceCtorEq, ↓reduceIte] at hden ⊢
  rw [jacobiThetaArgument_add]
  rw [jacobiModulusOfTau] at hmod
  generalize jacobiThetaArgument u k = x at hu' hden ⊢
  generalize jacobiThetaArgument v k = y at hv' hden ⊢
  generalize jacobiTau k = τ at hτ hu' hv' hden hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := jacobiThetaTau_zero_ne_zero_and_pow_four τ hτ
  have hD : (θ₄ (x + y) τ * θ₂ (x - y) τ) ≠ 0 := by
    intro h0; apply hden
    field_simp
    linear_combination θ₄ 0 τ ^ 2 *
        (-jacobiThetaFourTau_add_mul_jacobiThetaTwoTau_sub x y τ hτ + θ₂ 0 τ * θ₄ 0 τ * h0)
  have hp := left_ne_zero_of_mul hD
  field_simp
  linear_combination (-(θ₄ 0 τ ^ 3 * θ₂ (x + y) τ)) *
      jacobiThetaFourTau_add_mul_jacobiThetaTwoTau_sub x y τ hτ +
    (θ₂ 0 τ * θ₄ (x + y) τ) * jacobiThetaTwoTau_add_mul_jacobiThetaTwoTau_sub_four x y τ hτ

/-- DLMF 22.8.17: an addition theorem for `dn`, at points `u`, `v` where the functions
`·n` are finite (`IsJacobiRegular .n`) and the printed denominator is nonzero. -/
@[dlmf 22.8.E17]
theorem jacobiDn_add_alt {k : ℂ} (hk : k ∈ jacobiModulusDomain) {u v : ℂ}
    (hu : IsJacobiRegular .n u k) (hv : IsJacobiRegular .n v k)
    (hden : jacobiSn u k * jacobiCn v k * jacobiDn v k -
      jacobiSn v k * jacobiCn u k * jacobiDn u k ≠ 0) :
    jacobiDn (u + v) k =
      (jacobiSn u k * jacobiCn v k * jacobiDn u k - jacobiSn v k * jacobiCn u k *
        jacobiDn v k) / (jacobiSn u k * jacobiCn v k * jacobiDn v k - jacobiSn v k *
          jacobiCn u k * jacobiDn u k) := by
  have hτ := jacobiTau_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  have hu' : θ₄ (jacobiThetaArgument u k) (jacobiTau k) ≠ 0 := by
    intro h'; apply hu; simp [jacobiLetterTheta, h']
  have hv' : θ₄ (jacobiThetaArgument v k) (jacobiTau k) ≠ 0 := by
    intro h'; apply hv; simp [jacobiLetterTheta, h']
  rw [eq_div_iff hden]
  simp only [jacobiSn, jacobiCn, jacobiDn, jacobiPQ, jacobiGlaisher, jacobiLetterTheta,
    reduceCtorEq, ↓reduceIte] at hden ⊢
  rw [jacobiThetaArgument_add]
  rw [jacobiModulusOfTau] at hmod
  generalize jacobiThetaArgument u k = x at hu' hden ⊢
  generalize jacobiThetaArgument v k = y at hv' hden ⊢
  generalize jacobiTau k = τ at hτ hu' hv' hden hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := jacobiThetaTau_zero_ne_zero_and_pow_four τ hτ
  have hD : (θ₄ (x + y) τ * θ₁ (x - y) τ) ≠ 0 := by
    intro h0; apply hden
    field_simp
    linear_combination θ₄ 0 τ ^ 2 *
        (-jacobiThetaFourTau_add_mul_jacobiThetaOneTau_sub x y τ hτ + θ₂ 0 τ * θ₃ 0 τ * h0)
  have hp := left_ne_zero_of_mul hD
  field_simp
  linear_combination (-(θ₄ 0 τ * θ₃ (x + y) τ)) *
      jacobiThetaFourTau_add_mul_jacobiThetaOneTau_sub x y τ hτ +
    (θ₃ 0 τ * θ₄ (x + y) τ) * jacobiThetaThreeTau_add_mul_jacobiThetaOneTau_sub x y τ hτ

/-- DLMF 22.8.18: an addition theorem for `dn`, at points `u`, `v` where the functions
`·n` are finite (`IsJacobiRegular .n`) and the printed denominator is nonzero. -/
@[dlmf 22.8.E18]
theorem jacobiDn_add_alt₂ {k : ℂ} (hk : k ∈ jacobiModulusDomain) {u v : ℂ}
    (hu : IsJacobiRegular .n u k) (hv : IsJacobiRegular .n v k)
    (hden : jacobiCn u k * jacobiCn v k +
      jacobiSn u k * jacobiDn u k * jacobiSn v k * jacobiDn v k ≠ 0) :
    jacobiDn (u + v) k =
      (jacobiCn u k * jacobiDn u k * jacobiCn v k * jacobiDn v k + jacobiComodulus k ^ 2 *
        jacobiSn u k * jacobiSn v k) / (jacobiCn u k * jacobiCn v k + jacobiSn u k *
          jacobiDn u k * jacobiSn v k * jacobiDn v k) := by
  have hτ := jacobiTau_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  have hu' : θ₄ (jacobiThetaArgument u k) (jacobiTau k) ≠ 0 := by
    intro h'; apply hu; simp [jacobiLetterTheta, h']
  have hv' : θ₄ (jacobiThetaArgument v k) (jacobiTau k) ≠ 0 := by
    intro h'; apply hv; simp [jacobiLetterTheta, h']
  rw [eq_div_iff hden]
  rw [← (jacobi_inversion_k hk).2.1] at ⊢
  simp only [jacobiSn, jacobiCn, jacobiDn, jacobiPQ, jacobiGlaisher, jacobiLetterTheta,
    jacobiComodulusOfTau, reduceCtorEq, ↓reduceIte] at hden ⊢
  rw [jacobiThetaArgument_add]
  rw [jacobiModulusOfTau] at hmod
  generalize jacobiThetaArgument u k = x at hu' hden ⊢
  generalize jacobiThetaArgument v k = y at hv' hden ⊢
  generalize jacobiTau k = τ at hτ hu' hv' hden hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := jacobiThetaTau_zero_ne_zero_and_pow_four τ hτ
  have hD : (θ₄ (x + y) τ * θ₂ (x - y) τ) ≠ 0 := by
    intro h0; apply hden
    field_simp
    linear_combination θ₄ 0 τ ^ 2 *
        (-jacobiThetaFourTau_add_mul_jacobiThetaTwoTau_sub x y τ hτ + θ₂ 0 τ * θ₄ 0 τ * h0)
  have hp := left_ne_zero_of_mul hD
  field_simp
  linear_combination (-(θ₃ (x + y) τ * θ₃ 0 τ)) *
      jacobiThetaFourTau_add_mul_jacobiThetaTwoTau_sub x y τ hτ +
    (θ₄ (x + y) τ * θ₄ 0 τ) * jacobiThetaThreeTau_add_mul_jacobiThetaTwoTau_sub x y τ hτ

/-- `1 - k² sn²u sn²v ≠ 0` where `sn` is finite at `u`, `v`, `u + v`, `u - v`. -/
private lemma one_sub_sq_mul_jacobiSn_sq_mul_jacobiSn_sq_ne_zero {k : ℂ}
    (hk : k ∈ jacobiModulusDomain) {u v : ℂ}
    (hu : IsJacobiRegular .n u k) (hv : IsJacobiRegular .n v k)
    (hp : IsJacobiRegular .n (u + v) k) (hm : IsJacobiRegular .n (u - v) k) :
    1 - k ^ 2 * jacobiSn u k ^ 2 * jacobiSn v k ^ 2 ≠ 0 := by
  have hτ := jacobiTau_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  have hu' := jacobiThetaFourTau_jacobiThetaArgument_ne_zero hu
  have hv' := jacobiThetaFourTau_jacobiThetaArgument_ne_zero hv
  have hp' := jacobiThetaFourTau_jacobiThetaArgument_ne_zero hp
  have hm' := jacobiThetaFourTau_jacobiThetaArgument_ne_zero hm
  rw [jacobiThetaArgument_add] at hp'
  rw [sub_eq_add_neg, jacobiThetaArgument_add, jacobiThetaArgument_neg, ← sub_eq_add_neg] at hm'
  simp only [jacobiSn, jacobiPQ, jacobiGlaisher, jacobiLetterTheta, reduceCtorEq, ↓reduceIte]
  rw [jacobiModulusOfTau] at hmod
  generalize jacobiThetaArgument u k = x at hu' hp' hm' ⊢
  generalize jacobiThetaArgument v k = y at hv' hp' hm' ⊢
  generalize jacobiTau k = τ at hτ hu' hv' hp' hm' hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := jacobiThetaTau_zero_ne_zero_and_pow_four τ hτ
  have N4 := jacobiThetaFourTau_add_mul_jacobiThetaFourTau_sub x y τ hτ
  intro h0
  field_simp at h0
  have : jacobiThetaFourTau 0 τ ^ 2 *
      (jacobiThetaFourTau (x + y) τ * jacobiThetaFourTau (x - y) τ) = 0 := by
    linear_combination N4 + h0
  rcases mul_eq_zero.mp this with h | h
  · exact h4 (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h)
  · rcases mul_eq_zero.mp h with h | h
    · exact hp' h
    · exact hm' h

/-- The stated relation follows from the given hypotheses: `IsJacobiRegular .n (-v) k`. -/
private lemma isJacobiRegular_n_neg {k : ℂ} {v : ℂ} (hv : IsJacobiRegular .n v k) : IsJacobiRegular
    .n (-v) k := by
  unfold IsJacobiRegular at *
  rw [jacobiThetaArgument_neg, jacobiLetterTheta_neg]; simpa using hv

/-- Addition formulas at `u + v` and `u - v` with the common denominator. -/
theorem jacobiSnCnDnk_add_sub {k : ℂ} (hk : k ∈ jacobiModulusDomain) {u v : ℂ}
    (hu : IsJacobiRegular .n u k) (hv : IsJacobiRegular .n v k)
    (hp : IsJacobiRegular .n (u + v) k) (hm : IsJacobiRegular .n (u - v) k) :
    let su := jacobiSn u k; let cu := jacobiCn u k; let du := jacobiDn u k
    let sv := jacobiSn v k; let cv := jacobiCn v k; let dv := jacobiDn v k
    let D := 1 - k ^ 2 * su ^ 2 * sv ^ 2
    D ≠ 0 ∧
    jacobiSn (u + v) k = (su * cv * dv + sv * cu * du) / D ∧
    jacobiCn (u + v) k = (cu * cv - su * du * sv * dv) / D ∧
    jacobiDn (u + v) k = (du * dv - k ^ 2 * su * cu * sv * cv) / D ∧
    jacobiSn (u - v) k = (su * cv * dv - sv * cu * du) / D ∧
    jacobiCn (u - v) k = (cu * cv + su * du * sv * dv) / D ∧
    jacobiDn (u - v) k = (du * dv + k ^ 2 * su * cu * sv * cv) / D := by
  intro su cu du sv cv dv D
  have hD : D ≠ 0 := one_sub_sq_mul_jacobiSn_sq_mul_jacobiSn_sq_ne_zero hk hu hv hp hm
  have hD' : 1 - k ^ 2 * jacobiSn u k ^ 2 * jacobiSn (-v) k ^ 2 ≠ 0 := by
    have : jacobiSn (-v) k = -jacobiSn v k := by simp [jacobiSn, jacobiPQ_neg]
    rw [this, neg_sq]; exact hD
  have ns : jacobiSn (-v) k = -sv := by simp [sv, jacobiSn, jacobiPQ_neg]
  have nc : jacobiCn (-v) k = cv := by simp [cv, jacobiCn, jacobiPQ_neg]
  have nd : jacobiDn (-v) k = dv := by simp [dv, jacobiDn, jacobiPQ_neg]
  have hv' := isJacobiRegular_n_neg hv
  have a1 := jacobiSn_add hk hu hv' hD'
  have a2 := jacobiCn_add hk hu hv' hD'
  have a3 := jacobiDn_add hk hu hv' hD'
  rw [← sub_eq_add_neg, ns, nc, nd, neg_sq] at a1 a2 a3
  refine ⟨hD, jacobiSn_add hk hu hv hD, jacobiCn_add hk hu hv hD, jacobiDn_add hk hu hv hD,
    ?_, ?_, ?_⟩
  · rw [a1]; ring
  · rw [a2]; ring
  · rw [a3]; ring

/-- Nonvanishing under the stated hypotheses: `jacobiPQ p q z k ≠ 0`. -/
private lemma jacobiPQ_ne_zero_of_regular {p q : JacobiLetter} (hpq : p ≠ q) {z k : ℂ}
    (hp : IsJacobiRegular p z k) (hq : IsJacobiRegular q z k) : jacobiPQ p q z k ≠ 0 := by
  unfold jacobiPQ jacobiGlaisher
  simp only [hpq, ↓reduceIte]
  exact div_ne_zero hp hq

/-- The stated relation follows from the given hypotheses:
`IsJacobiRegular r (z + completeEllipticK k) k ↔ IsJacobiRegular r.swapK z k`. -/
theorem isJacobiRegular_add_completeEllipticK_iff {k : ℂ} (hk : k ∈ jacobiModulusDomain)
    (r : JacobiLetter) (z : ℂ) :
    IsJacobiRegular r (z + completeEllipticK k) k ↔ IsJacobiRegular r.swapK z k := by
  have hK := completeEllipticK_ne_zero hk
  have hτ := jacobiTau_im_pos hk
  have hz : jacobiThetaArgument (z + completeEllipticK k) k = jacobiThetaArgument z k + π / 2 := by
    rw [jacobiThetaArgument, jacobiThetaArgument]; field_simp
  unfold IsJacobiRegular
  rw [hz, jacobiLetterTheta_add_pi_div_two hτ]
  exact ⟨fun h => right_ne_zero_of_mul h,
    fun h => mul_ne_zero (jacobiLetterMultiplierK_ne_zero hτ r) h⟩

/-- The stated relation follows from the given hypotheses: `IsJacobiRegular .n (z + 2 *
completeEllipticK k) k ↔ IsJacobiRegular .n z k`. -/
theorem isJacobiRegular_n_add_two_mul_completeEllipticK_iff {k : ℂ}
    (hk : k ∈ jacobiModulusDomain) (z : ℂ) :
    IsJacobiRegular .n (z + 2 * completeEllipticK k) k ↔ IsJacobiRegular .n z k := by
  rw [show z + 2 * completeEllipticK k = z + completeEllipticK k + completeEllipticK k by ring,
    isJacobiRegular_add_completeEllipticK_iff hk, isJacobiRegular_add_completeEllipticK_iff hk]
  rfl

/-- Theta functions at real multiples of `π`. -/
theorem jacobiThetaTau_real_mul_pi_ne_zero {τ : ℂ} (hτ : 0 < τ.im) (r : ℝ) :
    jacobiThetaFourTau (r * π) τ ≠ 0 ∧ jacobiThetaThreeTau (r * π) τ ≠ 0 ∧
      ((∀ m : ℤ, r ≠ m) → jacobiThetaOneTau (r * π) τ ≠ 0) := by
  obtain ⟨h1, -, h3, h4⟩ := DLMF.Theta.jacobiThetaTau_eq_zero_iff hτ (r * π)
  have key : ∀ (y x : ℝ), (r : ℂ) * π = (y + x * τ) * π → x = 0 ∧ r = y := by
    intro y x h
    have h' : ((r - y : ℝ) : ℂ) + (-x : ℝ) * τ = 0 := by
      have := mul_right_cancel₀ (ofReal_ne_zero.mpr Real.pi_ne_zero) h
      push_cast; linear_combination this
    have := DLMF.Theta.eq_zero_of_lattice_point_eq_zero hτ (a := r - y) (b := -x)
        (by rw [h', zero_mul])
    constructor <;> linarith [this.1, this.2]
  refine ⟨?_, ?_, ?_⟩
  · rw [Ne, h4]; rintro ⟨m, n, h⟩
    have := (key m (n + 1 / 2) (by rw [h]; push_cast; ring)).1
    have h2 : (2 * n + 1 : ℝ) = 0 := by linarith
    have h3 : (2 * n + 1 : ℤ) = 0 := by exact_mod_cast h2
    omega
  · rw [Ne, h3]; rintro ⟨m, n, h⟩
    have := (key (m + 1 / 2) (n + 1 / 2) (by rw [h]; push_cast; ring)).1
    have h2 : (2 * n + 1 : ℝ) = 0 := by linarith
    have h3 : (2 * n + 1 : ℤ) = 0 := by exact_mod_cast h2
    omega
  · intro hr; rw [Ne, h1]; rintro ⟨m, n, h⟩
    exact hr m (key m n (by rw [h]; push_cast; ring)).2

/-- Identity under the stated parameter and domain assumptions:
`jacobiThetaArgument (c * completeEllipticK k) k = ((c / 2 : ℝ) : ℂ) * π`. -/
private lemma jacobiThetaArgument_real_mul_completeEllipticK {k : ℂ}
    (hk : k ∈ jacobiModulusDomain) (c : ℝ) :
    jacobiThetaArgument (c * completeEllipticK k) k = ((c / 2 : ℝ) : ℂ) * π := by
  have hK := completeEllipticK_ne_zero hk
  rw [jacobiThetaArgument]; push_cast; field_simp

/-- Nonvanishing under the stated hypotheses: `IsJacobiRegular .n (c * completeEllipticK k) k ∧
IsJacobiRegular .d (c * completeEllipticK k) k ∧ ((∀ m : ℤ, c / 2 ≠ m) → IsJacobiRegular .s (c *
completeEllipticK k) k)`. -/
private lemma isJacobiRegular_real_mul_completeEllipticK {k : ℂ}
    (hk : k ∈ jacobiModulusDomain) (c : ℝ) :
    IsJacobiRegular .n (c * completeEllipticK k) k ∧
        IsJacobiRegular .d (c * completeEllipticK k) k ∧
      ((∀ m : ℤ, c / 2 ≠ m) → IsJacobiRegular .s (c * completeEllipticK k) k) := by
  have hτ := jacobiTau_im_pos hk
  obtain ⟨h4, h3, h1⟩ := jacobiThetaTau_real_mul_pi_ne_zero hτ (c / 2)
  obtain ⟨n2, n3, n4, -⟩ := jacobiThetaTau_zero_ne_zero_and_pow_four _ hτ
  simp only [IsJacobiRegular, jacobiLetterTheta, jacobiThetaArgument_real_mul_completeEllipticK hk]
  exact ⟨div_ne_zero h4 n4, div_ne_zero h3 n3,
    fun h => mul_ne_zero (div_ne_zero n3 (mul_ne_zero n2 n4)) (h1 h)⟩

/-- Values at `2K/3` and `4K/3`. -/
theorem jacobiSnCnDnk_two_mul_completeEllipticK_div_three {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    let a := 2 * completeEllipticK k / 3
    let b := 4 * completeEllipticK k / 3
    IsJacobiRegular .n a k ∧ IsJacobiRegular .n b k ∧ jacobiSn a k ≠ 0 ∧
      jacobiSn b k = jacobiSn a k ∧ jacobiCn b k = -jacobiCn a k ∧
      jacobiDn b k = jacobiDn a k ∧ 1 - k ^ 2 * jacobiSn a k ^ 4 ≠ 0 ∧
      1 - k ^ 2 * jacobiSn a k ^ 4 = 2 * jacobiCn a k * jacobiDn a k ∧
      jacobiCn a k ^ 2 - jacobiSn a k ^ 2 * jacobiDn a k ^ 2 =
        -2 * jacobiCn a k ^ 2 * jacobiDn a k := by
  intro a b
  have ea : a = ((2 / 3 : ℝ) : ℂ) * completeEllipticK k := by simp only [a]; push_cast; ring
  have eb : b = ((4 / 3 : ℝ) : ℂ) * completeEllipticK k := by simp only [b]; push_cast; ring
  obtain ⟨hna, -, hsa⟩ := isJacobiRegular_real_mul_completeEllipticK hk (2 / 3)
  obtain ⟨hnb, -, -⟩ := isJacobiRegular_real_mul_completeEllipticK hk (4 / 3)
  rw [← ea] at hna hsa; rw [← eb] at hnb
  have hsa' : jacobiSn a k ≠ 0 := by
    refine jacobiPQ_ne_zero_of_regular (by decide) (hsa ?_) hna
    intro m hm
    have h3 : (3 * m : ℝ) = 1 := by linarith
    have h3' : (3 * m : ℤ) = 1 := by exact_mod_cast h3
    omega
  have e2 : b = -a + 2 * completeEllipticK k := by simp only [a, b]; ring
  have vs : jacobiSn b k = jacobiSn a k := by
    rw [e2, (jacobiSn_shift hk _).2.2.2.1]
    simp [jacobiSn, jacobiPQ_neg]
  have vc : jacobiCn b k = -jacobiCn a k := by
    rw [e2, (jacobiCn_shift hk _).2.2.2.1]
    simp [jacobiCn, jacobiPQ_neg]
  have vd : jacobiDn b k = jacobiDn a k := by
    rw [e2, (jacobiDn_shift hk _).2.2.2.1]
    simp [jacobiDn, jacobiPQ_neg]
  have e2a : 2 * a = b := by simp only [a, b]; ring
  have hn0 : IsJacobiRegular .n (a - a) k := by
    rw [sub_self]; simpa using (isJacobiRegular_real_mul_completeEllipticK hk 0).1
  have hnaa : IsJacobiRegular .n (a + a) k := by rw [← two_mul, e2a]; exact hnb
  have hD4 := one_sub_sq_mul_jacobiSn_sq_mul_jacobiSn_sq_ne_zero hk hna hna hnaa hn0
  have hD : 1 - k ^ 2 * jacobiSn a k ^ 4 ≠ 0 := by convert hD4 using 2; ring
  have d1 := jacobiSn_add hk hna hna hD4
  have d2 := jacobiCn_add hk hna hna hD4
  rw [← two_mul, e2a, vs] at d1; rw [← two_mul, e2a, vc] at d2
  rw [eq_div_iff hD4] at d1 d2
  have E1 : 1 - k ^ 2 * jacobiSn a k ^ 4 = 2 * jacobiCn a k * jacobiDn a k := by
    apply mul_left_cancel₀ hsa'; linear_combination d1
  refine ⟨hna, hnb, hsa', vs, vc, vd, hD, E1, ?_⟩
  linear_combination -d2 - jacobiCn a k * E1

/-- Nonvanishing under the stated hypotheses: `k ≠ 0`. -/
theorem ne_zero_of_mem_jacobiModulusDomain {k : ℂ} (hk : k ∈ jacobiModulusDomain) : k ≠ 0 := by
  rintro rfl; simp [jacobiModulusDomain] at hk

/-- Nonvanishing under the stated hypotheses: `jacobiDn (2 * completeEllipticK k / 3) k ≠ 0`. -/
theorem jacobiDn_two_mul_completeEllipticK_div_three_ne_zero {k : ℂ}
    (hk : k ∈ jacobiModulusDomain) :
    jacobiDn (2 * completeEllipticK k / 3) k ≠ 0 := by
  obtain ⟨hn, hd, -⟩ := isJacobiRegular_real_mul_completeEllipticK hk (2 / 3)
  have ea : 2 * completeEllipticK k / 3 = ((2 / 3 : ℝ) : ℂ) * completeEllipticK k := by
      push_cast; ring
  rw [ea]; exact jacobiPQ_ne_zero_of_regular (by decide) hd hn

/-- `sn² + cn² = 1`, `k² sn² + dn² = 1` (copy of 22.6.1 for use in this file). -/
private lemma jacobiSn_sq_add_jacobiCn_sq_and_of_regular {k : ℂ}
    (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hn : IsJacobiRegular .n z k) :
    jacobiSn z k ^ 2 + jacobiCn z k ^ 2 = 1 ∧ k ^ 2 * jacobiSn z k ^ 2 + jacobiDn z k ^ 2 = 1 :=
        by
  have hτ := jacobiTau_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  have hn' : jacobiThetaFourTau (jacobiThetaArgument z k) (jacobiTau k) ≠ 0 := by
    intro h; apply hn; simp [jacobiLetterTheta, h]
  simp only [jacobiSn, jacobiCn, jacobiDn, jacobiPQ, jacobiGlaisher, jacobiLetterTheta,
    reduceCtorEq, ↓reduceIte]
  rw [jacobiModulusOfTau] at hmod
  generalize jacobiThetaArgument z k = ζ at hn' ⊢
  generalize jacobiTau k = τ at hτ hn' hmod ⊢
  subst hmod
  have h2 := jacobiThetaTwoTau_zero_ne_zero hτ
  have h3 := jacobiThetaThreeTau_zero_ne_zero hτ
  have h4 := jacobiThetaFourTau_zero_ne_zero hτ
  have e3 := DLMF.Theta.jacobiTheta_sq_two_four ζ τ hτ
  have e2 := DLMF.Theta.jacobiTheta_sq_three_four ζ τ hτ
  simp only [DLMF.Theta.jacobiThetaTwoNullTau, DLMF.Theta.jacobiThetaThreeNullTau,
    DLMF.Theta.jacobiThetaFourNullTau] at e2 e3
  constructor
  · field_simp
    linear_combination -e3
  · field_simp
    linear_combination -e2

/-- **Admitted.** DLMF 22.8.19–22.8.20: if `z₁ + z₂ + z₃ + z₄ = 0` then
`det [sn zⱼ, cn zⱼ, dn zⱼ, 1] = 0` (at points where `sn, cn, dn` are finite). -/
@[dlmf 22.8.E19, dlmf 22.8.E20]
theorem jacobi_det_sum_zero {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : Fin 4 → ℂ)
    (hz : z 0 + z 1 + z 2 + z 3 = 0) (hreg : ∀ j, IsJacobiRegular .n (z j) k) :
    Matrix.det (Matrix.of fun i : Fin 4 =>
      ![jacobiSn (z i) k, jacobiCn (z i) k, jacobiDn (z i) k, 1]) = 0 := by
  sorry

/-- **Admitted.** DLMF 22.8.21: if `z₁ + z₂ + z₃ + z₄ = 0` then
`k'² - k'²k² ∏ sn zⱼ + k² ∏ cn zⱼ - ∏ dn zⱼ = 0`. -/
@[dlmf 22.8.E19, dlmf 22.8.E21]
theorem jacobi_prod_sum_zero {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : Fin 4 → ℂ)
    (hz : z 0 + z 1 + z 2 + z 3 = 0) (hreg : ∀ j, IsJacobiRegular .n (z j) k) :
    jacobiComodulus k ^ 2 - jacobiComodulus k ^ 2 * k ^ 2 * ∏ j, jacobiSn (z j) k +
      k ^ 2 * ∏ j, jacobiCn (z j) k - ∏ j, jacobiDn (z j) k = 0 := by
  sorry

/-- **Admitted, corrected.** DLMF 22.8.22–22.8.23 with the third column corrected to `sn`: if
`z₁ + z₂ + z₃ + z₄ = 2K` then `det [sn zⱼ cn zⱼ, cn zⱼ dn zⱼ, sn zⱼ, dn zⱼ] = 0`.
Corrected from the printed DLMF formula: with the printed third column `cn zⱼ` the determinant
is nonzero (≈ -0.107 + 0.033i at `k = 0.6`); with `sn zⱼ` it vanishes. -/
@[dlmf 22.8.E22,
  dlmf 22.8.E23 "corrected: printed third column cn z_j replaced by sn z_j"]
theorem jacobi_det_sum_two_K {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : Fin 4 → ℂ)
    (hz : z 0 + z 1 + z 2 + z 3 = 2 * completeEllipticK k)
        (hreg : ∀ j, IsJacobiRegular .n (z j) k) :
    Matrix.det (Matrix.of fun i : Fin 4 =>
      ![jacobiSn (z i) k * jacobiCn (z i) k, jacobiCn (z i) k * jacobiDn (z i) k,
        jacobiSn (z i) k, jacobiDn (z i) k]) = 0 := by
  sorry

/-- **Admitted, corrected.** DLMF 22.8.22–22.8.23 with the second column corrected to
`sn zⱼ dn zⱼ`: if `z₁ + z₂ + z₃ + z₄ = 2K` then
`det [sn zⱼ cn zⱼ, sn zⱼ dn zⱼ, cn zⱼ, dn zⱼ] = 0`.
Corrected from the printed DLMF formula: the printed determinant (second column `cn zⱼ dn zⱼ`)
is nonzero numerically; with second column `sn zⱼ dn zⱼ` it vanishes (an alternative to
`jacobi_det_sum_two_K`). -/
@[dlmf 22.8.E22,
  dlmf 22.8.E23 "corrected: printed second column cn z_j dn z_j replaced by sn z_j dn z_j"]
theorem jacobi_det_sum_two_K' {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : Fin 4 → ℂ)
    (hz : z 0 + z 1 + z 2 + z 3 = 2 * completeEllipticK k)
        (hreg : ∀ j, IsJacobiRegular .n (z j) k) :
    Matrix.det (Matrix.of fun i : Fin 4 =>
      ![jacobiSn (z i) k * jacobiCn (z i) k, jacobiSn (z i) k * jacobiDn (z i) k,
        jacobiCn (z i) k, jacobiDn (z i) k]) = 0 := by
  sorry

/-- The expression of DLMF 22.8.25 at `z₁`, with `z₂ = z₁ - 2K/3`, `z₃ = z₂ - 2K/3`. -/
def jacobiDnThreePointExpr (z k : ℂ) : ℂ :=
  let d₁ := jacobiDn z k
  let d₂ := jacobiDn (z - 2 * completeEllipticK k / 3) k
  let d₃ := jacobiDn (z - 4 * completeEllipticK k / 3) k
  (d₂ + d₃) * (d₃ + d₁) * (d₁ + d₂) / (d₁ + d₂ + d₃)

/-- DLMF 22.8.24–22.8.25: if `z₁ - z₂ = z₂ - z₃ = 2K/3` then
`(dn z₂ + dn z₃)(dn z₃ + dn z₁)(dn z₁ + dn z₂)/(dn z₁ + dn z₂ + dn z₃)` is independent of the
`zⱼ` (at points where the `dn zⱼ` are finite and the denominator is nonzero). -/
@[dlmf 22.8.E24, dlmf 22.8.E25]
theorem jacobiDnThreePointExpr_const {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    ∃ c : ℂ, ∀ z : ℂ, (∀ j : ℕ, IsJacobiRegular .n (z - 2 * j * completeEllipticK k / 3) k) →
      jacobiDn z k + jacobiDn (z - 2 * completeEllipticK k / 3) k +
        jacobiDn (z - 4 * completeEllipticK k / 3) k ≠ 0 →
      jacobiDnThreePointExpr z k = c := by
  have W := jacobiSnCnDnk_two_mul_completeEllipticK_div_three hk
  simp only at W
  obtain ⟨hna, -, hsa, -, -, -, -, E1, E2⟩ := W
  obtain ⟨ha1, ha2⟩ := jacobiSn_sq_add_jacobiCn_sq_and_of_regular hk hna
  have hκ := jacobiDn_two_mul_completeEllipticK_div_three_ne_zero hk
  have hk0 : k ≠ 0 := ne_zero_of_mem_jacobiModulusDomain hk
  have hF2 : 1 + 2 * jacobiDn (2 * completeEllipticK k / 3) k ≠ 0 := by
    intro h
    have hY := mul_inv_cancel₀ hsa
    generalize (jacobiSn (2 * completeEllipticK k / 3) k)⁻¹ = Y at hY
    have : (1 : ℂ) = 0 := by
      linear_combination (-4 * Y ^ 2) * E2 +
          (-jacobiSn (2 * completeEllipticK k / 3) k * Y - 1) * hY +
        (-2 * jacobiSn (2 * completeEllipticK k / 3) k ^ 2 *
            jacobiDn (2 * completeEllipticK k / 3) k * Y ^ 2 +
          jacobiSn (2 * completeEllipticK k / 3) k ^ 2 * Y ^ 2 +
          4 * jacobiCn (2 * completeEllipticK k / 3) k ^ 2 * Y ^ 2) * h
    exact one_ne_zero this
  refine ⟨2 * jacobiDn (2 * completeEllipticK k / 3) k *
      (1 + jacobiDn (2 * completeEllipticK k / 3) k) ^ 2 /
    (1 + 2 * jacobiDn (2 * completeEllipticK k / 3) k), fun z hreg hden => ?_⟩
  have hn := hreg 0
  have hm := hreg 1
  have hb := hreg 2
  rw [show z - 2 * ((0 : ℕ) : ℂ) * completeEllipticK k / 3 = z by push_cast; ring] at hn
  rw [show z - 2 * ((1 : ℕ) : ℂ) * completeEllipticK k / 3 = z - 2 * completeEllipticK k / 3 by
    push_cast; ring] at hm
  have eb : z - 2 * ((2 : ℕ) : ℂ) * completeEllipticK k / 3 + 2 * completeEllipticK k =
      z + 2 * completeEllipticK k / 3 := by push_cast; ring
  have hp : IsJacobiRegular .n (z + 2 * completeEllipticK k / 3) k := by
    rw [← eb, isJacobiRegular_n_add_two_mul_completeEllipticK_iff hk]; exact hb
  have d3 : jacobiDn (z - 4 * completeEllipticK k / 3) k =
      jacobiDn (z + 2 * completeEllipticK k / 3) k := by
    rw [← (jacobiDn_shift hk _).2.2.2.1]; congr 1; ring
  obtain ⟨hD, -, -, e3, -, -, e6⟩ := jacobiSnCnDnk_add_sub hk hn hna hp hm
  obtain ⟨h1, h2⟩ := jacobiSn_sq_add_jacobiCn_sq_and_of_regular hk hn
  unfold jacobiDnThreePointExpr
  simp only
  rw [d3] at hden ⊢
  rw [e3, e6] at hden ⊢
  generalize jacobiSn z k = s at *
  generalize jacobiCn z k = c at *
  generalize jacobiDn z k = d at *
  generalize jacobiSn (2 * completeEllipticK k / 3) k = sa at *
  generalize jacobiCn (2 * completeEllipticK k / 3) k = ca at *
  generalize jacobiDn (2 * completeEllipticK k / 3) k = κ at *
  generalize hDdef : 1 - k ^ 2 * s ^ 2 * sa ^ 2 = D at hD hden ⊢
  have hden' : d * D + (d * κ + k ^ 2 * s * c * sa * ca) +
      (d * κ - k ^ 2 * s * c * sa * ca) ≠ 0 := by
    intro h; apply hden; field_simp; linear_combination h
  have hX := mul_inv_cancel₀ hκ
  generalize κ⁻¹ = X at hX
  rw [div_eq_div_iff hden hF2]
  field_simp
  linear_combination (-4*d^3*ca^4*κ^2*k^2-2*d^3*ca^4*κ*k^2+4*d^3*ca^2*κ^2*k^2+4*d*ca^4*κ^2*k^2
    -2*d*ca^2*k^4*D*X+2*d^3*ca^2*κ*k^2+2*d*ca^4*κ*k^2-2*d*ca^2*k^4*X-4*d*ca^2*κ^2*k^2
    +2*d*k^4*D*X-2*d*ca^2*κ*k^2+2*d*k^4*X+2*d*κ*k^2*D-2*d*k^2*D*X+2*d*κ*k^2-2*d*k^2*X) * h1 +
      (-d^3*ca^6*κ^2+4*c^2*d*ca^4*κ^2*k^2-d^3*ca^6*κ*X-2*d^3*ca^6*κ+2*c^2*d*ca^4*κ*k^2+d^3*ca^5*κ
        +5*d^3*ca^4*κ^2-4*c^2*d*ca^2*κ^2*k^2+d^3*ca^4*κ*X+d^3*ca^5+7*d^3*ca^4*κ-2*c^2*d*ca^2*κ*k^2
        -2*d*ca^2*κ^3*D^2-2*d*ca^2*κ^2*D^2*X+3*d^3*ca^4+2*d^3*ca^3*κ-4*d*ca^5*κ-7*d^3*ca^2*κ^2
        -4*d*ca^4*κ^2+4*d*ca^2*κ^3*D+8*d*ca^2*κ*k^2*D-4*d*ca^2*κ^2*D^2-2*d*ca^5*X
        -3*d^3*ca^2*κ*X+4*d*ca^2*κ^2*D*X+8*d*ca^2*k^2*D*X+2*d^3*ca^3-6*d*ca^5-8*d^3*ca^2*κ
        -10*d*ca^4*κ+12*d*ca^2*κ^3+8*d*ca^2*κ*k^2-2*d*ca^3*κ*D+8*d*ca^2*κ^2*D
        +16*d*ca^2*k^2*D+2*d*κ^3*D^2-6*d*ca^4*X+12*d*ca^2*κ^2*X+8*d*ca^2*k^2*X
        +2*d*κ^2*D^2*X-14*d*ca^4-3*d^3*ca*κ-2*d*ca^3*κ+3*d^3*κ^2+20*d*ca^2*κ^2
        +16*d*ca^2*k^2-2*d*ca^3*D-10*d*ca^2*κ*D-4*d*κ^3*D-8*d*κ*k^2*D+4*d*κ^2*D^2
        -8*d*ca^3*X+3*d^3*κ*X-8*d*ca^2*κ*X-6*d*ca^2*D*X-4*d*κ^2*D*X-8*d*k^2*D*X
        -3*d^3*ca-10*d*ca^3+3*d^3*κ+2*d*ca^2*κ-12*d*κ^3-8*d*κ*k^2-16*d*ca^2*D
        +2*d*ca*κ*D-8*d*κ^2*D-16*d*k^2*D-12*d*κ^2*X-8*d*k^2*X-3*d^3+16*d*ca^2
        +6*d*ca*κ-16*d*κ^2-16*d*k^2+2*d*ca*D+8*d*κ*D+10*d*ca*X+8*d*κ*X
        +8*d*D*X+16*d*ca+6*d*κ+16*d*D+8*d*X-2*d) * h2 +
      (2*d^3*sa^2*ca^3*κ^2*k^4*X+2*d^5*sa^2*ca^3*κ*k^2*X+d^3*sa^2*ca^3*κ*k^4*X
        +2*d^3*sa^2*ca^2*κ^2*k^4*X+2*d^5*sa^2*ca^3*κ*k^2+s^2*d^3*ca^4*κ^2*k^2
        -4*s^2*c^2*d*ca^2*κ^2*k^4+d^5*ca^4*κ^3*X+1/2*d^5*sa^2*ca^3*k^2*X+2*d^5*sa^2*ca^2*κ*k^2*X
        +s^2*d^3*ca^4*κ*k^2*X+2*d^3*ca^3*κ^4*k^2*X-d^3*sa^2*ca^2*κ*k^4*X
        -2*d*sa^2*ca^3*κ^2*k^4*X-1/2*d^3*sa^2*ca^3*κ*k^2*D*X+d^3*sa^2*ca^2*k^4*X^2
        +2*d^5*sa^2*ca^2*κ*k^2+2*s^2*d^3*ca^4*κ*k^2-2*s^2*c^2*d*ca^2*κ*k^4
        -1/2*d^3*sa^2*ca^3*κ*k^2*D-2*d^5*ca^3*κ^3*X-1/2*d^5*sa^2*ca^2*k^2*X
        -7/2*d^3*sa^2*ca^3*κ*k^2*X-3*d^3*ca^3*κ^3*k^2*X+2*d^3*ca^2*κ^4*k^2*X
        +d^3*sa^2*ca^2*k^4*X-4*d^3*sa^2*ca*κ*k^4*X-d*sa^2*ca^3*κ*k^4*X
        -2*d*sa^2*ca^2*κ^2*k^4*X-1/2*d^3*sa^2*ca^3*k^2*D*X
        -1/2*d^3*sa^2*ca^2*κ*k^2*D*X+3*d^3*sa^2*ca*k^4*X^2+2*d^5*ca^3*κ^3
        -2*d^5*sa^2*ca^2*k^2-s^2*d^3*ca^3*κ*k^2-7/2*d^3*sa^2*ca^3*κ*k^2
        -1/2*d^3*sa^2*ca^3*k^2*D-1/2*d^3*sa^2*ca^2*κ*k^2*D
        -1/2*d^5*ca^3*κ^2*X-2*d^5*ca^2*κ^3*X-d^3*ca^4*κ^3*X
        -3/2*d^5*sa^2*ca*k^2*X-5/2*d^3*sa^2*ca^2*κ*k^2*X
        -2*d^3*ca^3*κ^2*k^2*X-5*d^3*ca^2*κ^3*k^2*X-2*d*ca^3*κ^4*k^2*X
        +4*d^3*sa^2*ca*k^4*X-4*d^3*sa^2*κ*k^4*X+d*sa^2*ca^2*κ*k^4*X
        +1/2*d^3*ca^3*κ^3*D*X+1/2*d^3*sa^2*ca^2*k^2*D*X
        -1/2*d^3*sa^2*ca*κ*k^2*D*X-d^3*ca^2*κ^2*k^2*X^2
        +5*d^3*sa^2*k^4*X^2-d*sa^2*ca^2*k^4*X^2+2*d^5*ca^2*κ^3
        -3*d^5*sa^2*ca*k^2-s^2*d^3*ca^3*k^2
        +3/2*d^3*sa^2*ca^3*k^2-3*s^2*d^3*ca^2*κ*k^2
        -5/2*d^3*sa^2*ca^2*κ*k^2-1/2*d^3*ca^3*κ^3*D
        +1/2*d^3*sa^2*ca^2*k^2*D
        -1/2*d^3*sa^2*ca*κ*k^2*D+2*s^2*d*κ^3*k^2*D^2
        +1/2*d^5*ca^2*κ^2*X+7/2*d^3*ca^3*κ^3*X
        -3/2*d^5*sa^2*k^2*X
        +2*d^3*sa^2*ca^2*k^2*X
        +9/2*d^3*sa^2*ca*κ*k^2*X
        +2*d^3*ca^3*κ*k^2*X
        +2*d*sa^2*ca^3*κ*k^2*X
        +3*d^3*ca^2*κ^2*k^2*X
        -4*d^3*ca*κ^3*k^2*X
        +3*d*ca^3*κ^3*k^2*X
        -2*d*ca^2*κ^4*k^2*X
        +8*d^3*sa^2*k^4*X
        -d*sa^2*ca^2*k^4*X
        +4*d*sa^2*ca*κ*k^4*X+1/2*d^3*ca^3*κ^2*D*X+1/2*d^3*ca^2*κ^3*D*X+3/2*d^3*sa^2*ca*k^2*D*X
        -1/2*d^3*sa^2*κ*k^2*D*X+2*d^3*κ^4*D^2*X+2*s^2*d*κ^2*k^2*D^2*X-3*d^3*ca*κ^2*k^2*X^2
        -3*d*sa^2*ca*k^4*X^2-d*sa^2*ca^2*k^2*D*X^2-2*d^5*ca^2*κ^2-7/2*d^3*ca^3*κ^3-3*d^5*sa^2*k^2
        -3*s^2*d^3*ca^2*k^2+9/2*d^3*sa^2*ca^2*k^2-3*s^2*d^3*ca*κ*k^2+9/2*d^3*sa^2*ca*κ*k^2
        +4*s^2*d*ca^3*κ*k^2+4*d^3*ca^3*κ*k^2+2*d*sa^2*ca^3*κ*k^2+3*s^2*d^3*κ^2*k^2
        -1/2*d^3*ca^3*κ^2*D-1/2*d^3*ca^2*κ^3*D+5/2*d^3*sa^2*ca*k^2*D-1/2*d^3*sa^2*κ*k^2*D
        -4*s^2*d*κ^3*k^2*D-8*s^2*d*κ*k^4*D+4*s^2*d*κ^2*k^2*D^2+3/2*d^5*ca*κ^2*X+2*d^3*ca^3*κ^2*X
        +3*d^5*κ^3*X+5/2*d^3*ca^2*κ^3*X+4*d^3*sa^2*ca*k^2*X+2*s^2*d*ca^3*k^2*X-2*d^3*ca^3*k^2*X
        +3*s^2*d^3*κ*k^2*X+19/2*d^3*sa^2*κ*k^2*X+6*d^3*ca^2*κ*k^2*X+d*sa^2*ca^2*κ*k^2*X
        +12*d^3*ca*κ^2*k^2*X+2*d*ca^3*κ^2*k^2*X+5*d*ca^2*κ^3*k^2*X-4*d*sa^2*ca*k^4*X
        +4*d*sa^2*κ*k^4*X-1/2*d^3*ca^2*κ^2*D*X+1/2*d^3*ca*κ^3*D*X-4*d^3*κ^4*D*X
        +5/2*d^3*sa^2*k^2*D*X-3*d*sa^2*ca^2*k^2*D*X-4*s^2*d*κ^2*k^2*D*X-6*s^2*d*k^4*D*X
        +2*c^2*d*k^4*D*X-4*d*κ^3*k^2*D^2*X+d*sa^2*ca^2*k^2*X^2-5*d^3*κ^2*k^2*X^2+d*ca^2*κ^2*k^2*X^2
        -5*d*sa^2*k^4*X^2-3*d*sa^2*ca*k^2*D*X^2-3*d^5*ca*κ^2+3/2*d^3*ca^3*κ^2-5/2*d^3*ca^2*κ^3
        -3*s^2*d^3*ca*k^2+7/2*d^3*sa^2*ca*k^2+6*s^2*d*ca^3*k^2-4*d^3*ca^3*k^2-d*sa^2*ca^3*k^2
        +3*s^2*d^3*κ*k^2+19/2*d^3*sa^2*κ*k^2+8*s^2*d*ca^2*κ*k^2+4*d^3*ca^2*κ*k^2+d*sa^2*ca^2*κ*k^2
        -12*s^2*d*κ^3*k^2-8*s^2*d*κ*k^4+1/2*d^3*ca^2*κ^2*D-1/2*d^3*ca*κ^3*D+9/2*d^3*sa^2*k^2*D
        -2*d*sa^2*ca^2*k^2*D+2*s^2*d*ca*κ*k^2*D-8*s^2*d*κ^2*k^2*D-16*s^2*d*k^4*D+3/2*d^5*κ^2*X
        +4*d^3*ca^2*κ^2*X-9/2*d^3*ca*κ^3*X-2*d*ca^3*κ^3*X-12*d^3*κ^4*X+3*d^3*sa^2*k^2*X
        +6*s^2*d*ca^2*k^2*X-6*d^3*ca^2*k^2*X+d*sa^2*ca^2*k^2*X+14*d^3*ca*κ*k^2*X
        -4*d*sa^2*ca*κ*k^2*X-2*d*ca^3*κ*k^2*X-12*s^2*d*κ^2*k^2*X+2*d^3*κ^2*k^2*X-3*d*ca^2*κ^2*k^2*X
        +4*d*ca*κ^3*k^2*X-6*s^2*d*k^4*X+2*c^2*d*k^4*X-8*d*sa^2*k^4*X-3/2*d^3*ca*κ^2*D*X
        +1/2*d^3*κ^3*D*X-8*d*sa^2*ca*k^2*D*X-2*d*κ^4*D^2*X-d*sa^2*k^2*D^2*X-6*d*κ^2*k^2*D^2*X
        +3*d*sa^2*ca*k^2*X^2+3*d*ca*κ^2*k^2*X^2+d*ca^2*κ^2*D*X^2-5*d*sa^2*k^2*D*X^2-3*d^5*κ^2
        +9/2*d^3*ca^2*κ^2+9/2*d^3*ca*κ^3+2*d*ca^3*κ^3-3*s^2*d^3*k^2-5/2*d^3*sa^2*k^2
        +14*s^2*d*ca^2*k^2-12*d^3*ca^2*k^2-d*sa^2*ca^2*k^2+6*s^2*d*ca*κ*k^2-4*d*sa^2*ca*κ*k^2
        -4*d*ca^3*κ*k^2-16*s^2*d*κ^2*k^2-4*d^3*κ^2*k^2-16*s^2*d*k^4+5/2*d^3*ca*κ^2*D-1/2*d^3*κ^3*D
        +2*s^2*d*ca*k^2*D-6*d*sa^2*ca*k^2*D+10*s^2*d*κ*k^2*D-8*d^3*κ*k^2*D-d*sa^2*k^2*D^2
        +4*d*κ^2*k^2*D^2+6*d^3*ca*κ^2*X-2*d*ca^3*κ^2*X-9/2*d^3*κ^3*X-d*ca^2*κ^3*X+10*s^2*d*ca*k^2*X
        -10*d^3*ca*k^2*X+4*d*sa^2*ca*k^2*X+2*d*ca^3*k^2*X+8*s^2*d*κ*k^2*X+14*d^3*κ*k^2*X
        -9*d*sa^2*κ*k^2*X-8*d*ca^2*κ*k^2*X-12*d*ca*κ^2*k^2*X+4*d*κ^3*k^2*X+7/2*d^3*κ^2*D*X
        +d*ca^2*κ^2*D*X+4*d*κ^4*D*X+6*s^2*d*k^2*D*X-8*d^3*k^2*D*X-11*d*sa^2*k^2*D*X-2*d*k^4*D*X
        +4*d*κ*k^2*D^2*X-d*ca^2*κ^2*X^2+5*d*sa^2*k^2*X^2+5*d*κ^2*k^2*X^2+3*d*ca*κ^2*D*X^2
        +7/2*d^3*ca*κ^2-d*ca^3*κ^2+19/2*d^3*κ^3+d*ca^2*κ^3+16*s^2*d*ca*k^2-24*d^3*ca*k^2
        +3*d*sa^2*ca*k^2+4*d*ca^3*k^2+8*s^2*d*κ*k^2-2*d^3*κ*k^2-9*d*sa^2*κ*k^2-4*d*ca^2*κ*k^2
        +9/2*d^3*κ^2*D-2*d*ca^2*κ^2*D+16*s^2*d*k^2*D-16*d^3*k^2*D-8*d*sa^2*k^2*D+14*d*κ*k^2*D^2
        +3*d^3*κ^2*X-5*d*ca^2*κ^2*X+4*d*ca*κ^3*X+12*d*κ^4*X+6*s^2*d*k^2*X-8*d^3*k^2*X
        +8*d*sa^2*k^2*X+6*d*ca^2*k^2*X-14*d*ca*κ*k^2*X+4*d*κ^2*k^2*X-2*d*k^4*X+2*d*ca*κ^2*D*X
        +d*κ^2*D^2*X+6*d*k^2*D^2*X-3*d*ca*κ^2*X^2+5*d*κ^2*D*X^2-5/2*d^3*κ^2-d*ca^2*κ^2-4*d*ca*κ^3
        -2*s^2*d*k^2-20*d^3*k^2+10*d*sa^2*k^2+14*d*ca^2*k^2-6*d*ca*κ^2*D+8*d*κ*k^2*D-d*κ^2*D^2
        +12*d*k^2*D^2-8*d*ca*κ^2*X+d*κ^3*X+10*d*ca*k^2*X-18*d*κ*k^2*X-5*d*κ^2*D*X+8*d*k^2*D*X
        -5*d*κ^2*X^2+3*d*ca*κ^2-9*d*κ^3+24*d*ca*k^2-12*d*κ*k^2-8*d*κ^2*D+16*d*k^2*D-4*d*κ^2*X
        +2*d*k^2*X+10*d*κ^2+8*d*k^2) * ha1 +
      (-2*d^3*ca^5*κ^2*k^2*X-2*d^5*ca^5*κ*X-d^3*ca^5*κ*k^2*X-2*d^3*ca^4*κ^2*k^2*X-2*d^5*ca^5*κ
        -1/2*d^5*ca^5*X-2*d^5*ca^4*κ*X+d^3*ca^4*κ*k^2*X+2*d^3*ca^3*κ^2*k^2*X+2*d*ca^5*κ^2*k^2*X
        +1/2*d^3*ca^5*κ*D*X-d^3*ca^4*k^2*X^2-2*d^5*ca^4*κ+1/2*d^3*ca^5*κ*D+1/2*d^5*ca^4*X
        +2*d^5*ca^3*κ*X+7/2*d^3*ca^5*κ*X-d^3*ca^4*k^2*X+5*d^3*ca^3*κ*k^2*X+d*ca^5*κ*k^2*X
        +2*d^3*ca^2*κ^2*k^2*X+2*d*ca^4*κ^2*k^2*X+1/2*d^3*ca^5*D*X+1/2*d^3*ca^4*κ*D*X
        -3*d^3*ca^3*k^2*X^2+2*d^5*ca^4+2*d^5*ca^3*κ+7/2*d^3*ca^5*κ+1/2*d^3*ca^5*D
        +1/2*d^3*ca^4*κ*D+2*d^5*ca^3*X+2*d^5*ca^2*κ*X+5/2*d^3*ca^4*κ*X+4*d^3*ca^3*κ^2*X
        -4*d^3*ca^3*k^2*X+3*d^3*ca^2*κ*k^2*X-d*ca^4*κ*k^2*X-2*d*ca^3*κ^2*k^2*X
        -1/2*d^3*ca^4*D*X-4*d^3*ca^2*k^2*X^2+d*ca^4*k^2*X^2+3*d^5*ca^3-3/2*d^3*ca^5
        +2*d^5*ca^2*κ+5/2*d^3*ca^4*κ-1/2*d^3*ca^4*D+d^5*ca^2*X-2*d^3*ca^4*X
        -10*d^3*ca^3*κ*X-2*d*ca^5*κ*X+4*d^3*ca^2*κ^2*X-7*d^3*ca^2*k^2*X
        +d*ca^4*k^2*X-4*d^3*ca*κ*k^2*X-5*d*ca^3*κ*k^2*X-2*d*ca^2*κ^2*k^2*X
        -2*d^3*ca^3*D*X+3*d^3*ca*k^2*X^2+3*d*ca^3*k^2*X^2+d*ca^4*D*X^2
        +d^5*ca^2-9/2*d^3*ca^4-12*d^3*ca^3*κ-2*d*ca^5*κ-3*d^3*ca^3*D
        -3/2*d^5*ca*X-2*d^3*ca^3*X-18*d^3*ca^2*κ*X-d*ca^4*κ*X
        -4*d*ca^3*κ^2*X+4*d^3*ca*k^2*X+4*d*ca^3*k^2*X-4*d^3*κ*k^2*X
        -3*d*ca^2*κ*k^2*X-2*d^3*ca^2*D*X+3*d*ca^4*D*X
        -1/2*d^3*ca*κ*D*X-2*c^2*d*k^2*D*X-d*ca^4*X^2+5*d^3*k^2*X^2
        +4*d*ca^2*k^2*X^2+3*d*ca^3*D*X^2-3*d^5*ca+2*d^3*ca^3
        +d*ca^5-16*d^3*ca^2*κ-d*ca^4*κ-4*d^3*ca^2*D+2*d*ca^4*D
        -1/2*d^3*ca*κ*D-3/2*d^5*X+5*d^3*ca^2*X-d*ca^4*X
        -19/2*d^3*ca*κ*X+8*d*ca^3*κ*X-4*d*ca^2*κ^2*X
        -2*c^2*d*k^2*X+8*d^3*k^2*X+7*d*ca^2*k^2*X
        +4*d*ca*κ*k^2*X+3/2*d^3*ca*D*X+8*d*ca^3*D*X
        -1/2*d^3*κ*D*X+d*ca^2*D^2*X-3*d*ca^3*X^2
        -3*d*ca*k^2*X^2+4*d*ca^2*D*X^2-3*d^5
        +19*d^3*ca^2+d*ca^4+9/2*d^3*ca*κ
        +10*d*ca^3*κ+4*d^3*κ^2+5/2*d^3*ca*D
        +6*d*ca^3*D+15/2*d^3*κ*D+d*ca^2*D^2
        -4*d*κ^2*D^2+14*d^3*ca*X
        -6*d*ca^3*X-9/2*d^3*κ*X
        +18*d*ca^2*κ*X-4*d*ca*k^2*X
        +4*d*κ*k^2*X+21/2*d^3*D*X
        +8*d*ca^2*D*X+2*d*k^2*D*X
        -4*d*κ*D^2*X
        -4*d*ca^2*X^2
        -5*d*k^2*X^2
        -3*d*ca*D*X^2
        +55/2*d^3*ca
        -8*d*ca^3+23/2*d^3*κ+14*d*ca^2*κ+41/2*d^3*D+6*d*ca^2*D-14*d*κ*D^2+11*d^3*X-13*d*ca^2*X
        +10*d*ca*κ*X-6*d*k^2*X-8*d*ca*D*X-7*d*D^2*X+3*d*ca*X^2-5*d*D*X^2+35/2*d^3-25*d*ca^2
        -4*d*ca*κ-6*d*ca*D-8*d*κ*D-13*d*D^2-6*d*ca*X+9*d*κ*X-19*d*D*X+5*d*X^2-21*d*ca+3*d*κ-24*d*D
        +6*d*X+2*d) * ha2 +
      (2*d^3*ca^3*κ^2*k^2*X+2*d^5*ca^3*κ*X+d^3*ca^3*κ*k^2*X+2*d^3*ca^2*κ^2*k^2*X+2*d^5*ca^3*κ
        +1/2*d^5*ca^3*X+2*d^5*ca^2*κ*X-d^3*ca^2*κ*k^2*X-2*d*ca^3*κ^2*k^2*X-1/2*d^3*ca^3*κ*D*X
        +d^3*ca^2*k^2*X^2+2*d^5*ca^2*κ-1/2*d^3*ca^3*κ*D-1/2*d^5*ca^2*X-7/2*d^3*ca^3*κ*X
        +d^3*ca^2*k^2*X-4*d^3*ca*κ*k^2*X-d*ca^3*κ*k^2*X-2*d*ca^2*κ^2*k^2*X-1/2*d^3*ca^3*D*X
        -1/2*d^3*ca^2*κ*D*X+3*d^3*ca*k^2*X^2-2*d^5*ca^2-7/2*d^3*ca^3*κ-1/2*d^3*ca^3*D
        -1/2*d^3*ca^2*κ*D-3/2*d^5*ca*X-5/2*d^3*ca^2*κ*X+4*d^3*ca*k^2*X-4*d^3*κ*k^2*X
        +d*ca^2*κ*k^2*X+1/2*d^3*ca^2*D*X-1/2*d^3*ca*κ*D*X+5*d^3*k^2*X^2-d*ca^2*k^2*X^2
        -3*d^5*ca+3/2*d^3*ca^3-5/2*d^3*ca^2*κ+1/2*d^3*ca^2*D-1/2*d^3*ca*κ*D-3/2*d^5*X
        +2*d^3*ca^2*X+9/2*d^3*ca*κ*X+2*d*ca^3*κ*X+8*d^3*k^2*X-d*ca^2*k^2*X
        +4*d*ca*κ*k^2*X+3/2*d^3*ca*D*X-1/2*d^3*κ*D*X-3*d*ca*k^2*X^2-d*ca^2*D*X^2
        -3*d^5+9/2*d^3*ca^2+9/2*d^3*ca*κ+2*d*ca^3*κ+5/2*d^3*ca*D-1/2*d^3*κ*D
        +4*d^3*ca*X+19/2*d^3*κ*X+d*ca^2*κ*X-4*d*ca*k^2*X+4*d*κ*k^2*X
        +5/2*d^3*D*X-3*d*ca^2*D*X+d*ca^2*X^2-5*d*k^2*X^2-3*d*ca*D*X^2
        +7/2*d^3*ca-d*ca^3+19/2*d^3*κ+d*ca^2*κ+9/2*d^3*D-2*d*ca^2*D
        +3*d^3*X+d*ca^2*X-4*d*ca*κ*X-8*d*k^2*X-8*d*ca*D*X-d*D^2*X
        +3*d*ca*X^2-5*d*D*X^2-5/2*d^3-d*ca^2-4*d*ca*κ-6*d*ca*D-d*D^2
        +4*d*ca*X-9*d*κ*X-11*d*D*X+5*d*X^2+3*d*ca-9*d*κ-8*d*D+8*d*X
        +10*d) * E1 +
      (d^5*ca^4*κ*X+2*d^3*ca^3*κ^2*k^2*X-2*d^5*ca^3*κ*X-3*d^3*ca^3*κ*k^2*X+2*d^3*ca^2*κ^2*k^2*X
        +2*d^5*ca^3*κ-1/2*d^5*ca^3*X-2*d^5*ca^2*κ*X-d^3*ca^4*κ*X+2*d^3*ca^3*k^2*X
        -5*d^3*ca^2*κ*k^2*X-2*d*ca^3*κ^2*k^2*X+1/2*d^3*ca^3*κ*D*X-d^3*ca^2*k^2*X^2+2*d^5*ca^2*κ
        -1/2*d^3*ca^3*κ*D+1/2*d^5*ca^2*X+7/2*d^3*ca^3*κ*X+7*d^3*ca^2*k^2*X-4*d^3*ca*κ*k^2*X
        +3*d*ca^3*κ*k^2*X-2*d*ca^2*κ^2*k^2*X+1/2*d^3*ca^3*D*X+1/2*d^3*ca^2*κ*D*X
        +2*d^3*κ^2*D^2*X-3*d^3*ca*k^2*X^2-2*d^5*ca^2-7/2*d^3*ca^3*κ-1/2*d^3*ca^3*D
        -1/2*d^3*ca^2*κ*D+3/2*d^5*ca*X+2*d^3*ca^3*X+3*d^5*κ*X+5/2*d^3*ca^2*κ*X
        +12*d^3*ca*k^2*X-2*d*ca^3*k^2*X+5*d*ca^2*κ*k^2*X-1/2*d^3*ca^2*D*X
        +1/2*d^3*ca*κ*D*X-4*d^3*κ^2*D*X-4*d*κ*k^2*D^2*X-5*d^3*k^2*X^2+d*ca^2*k^2*X^2
        -3*d^5*ca+3/2*d^3*ca^3-5/2*d^3*ca^2*κ+1/2*d^3*ca^2*D-1/2*d^3*ca*κ*D
        +3/2*d^5*X+4*d^3*ca^2*X-9/2*d^3*ca*κ*X-2*d*ca^3*κ*X-12*d^3*κ^2*X
        +2*d^3*k^2*X-7*d*ca^2*k^2*X+4*d*ca*κ*k^2*X-3/2*d^3*ca*D*X
        +1/2*d^3*κ*D*X-2*d*κ^2*D^2*X-6*d*k^2*D^2*X+3*d*ca*k^2*X^2
        +d*ca^2*D*X^2-3*d^5+9/2*d^3*ca^2+9/2*d^3*ca*κ+2*d*ca^3*κ
        +5/2*d^3*ca*D-1/2*d^3*κ*D+6*d^3*ca*X-2*d*ca^3*X-9/2*d^3*κ*X
        -d*ca^2*κ*X-12*d*ca*k^2*X+4*d*κ*k^2*X+7/2*d^3*D*X+d*ca^2*D*X
        +4*d*κ^2*D*X-d*ca^2*X^2+5*d*k^2*X^2+3*d*ca*D*X^2+7/2*d^3*ca
        -d*ca^3+19/2*d^3*κ+d*ca^2*κ+9/2*d^3*D-2*d*ca^2*D+3*d^3*X
        -5*d*ca^2*X+4*d*ca*κ*X+12*d*κ^2*X+4*d*k^2*X+2*d*ca*D*X
        +d*D^2*X-3*d*ca*X^2+5*d*D*X^2-5/2*d^3-d*ca^2-4*d*ca*κ
        -6*d*ca*D-d*D^2-8*d*ca*X+d*κ*X-5*d*D*X-5*d*X^2
        +3*d*ca-9*d*κ-8*d*D-4*d*X+10*d) * E2 +
      (d^3*ca^4*κ^2+d^3*ca^4*κ*X+2*d^3*ca^4*κ-d^3*ca^3*κ-d^3*ca^3-3*d^3*ca^2*κ+2*d*κ^3*D^2
        +2*d*κ^2*D^2*X-3*d^3*ca^2-3*d^3*ca*κ+4*d*ca^3*κ+3*d^3*κ^2-4*d*κ^3*D-8*d*κ*k^2*D
        +4*d*κ^2*D^2+2*d*ca^3*X+3*d^3*κ*X-4*d*κ^2*D*X-6*d*k^2*D*X-3*d^3*ca+6*d*ca^3+3*d^3*κ
        +8*d*ca^2*κ-12*d*κ^3-8*d*κ*k^2+2*d*ca*κ*D-8*d*κ^2*D-16*d*k^2*D+6*d*ca^2*X-12*d*κ^2*X
        -6*d*k^2*X-3*d^3+14*d*ca^2+6*d*ca*κ-16*d*κ^2-16*d*k^2+2*d*ca*D+10*d*κ*D+10*d*ca*X
        +8*d*κ*X+6*d*D*X+16*d*ca+8*d*κ+16*d*D+6*d*X-2*d) * hDdef +
      (-d^5*ca^6*κ^2-2*d^5*ca^6*κ+4*d^5*ca^5*κ^2+5*d^5*ca^5*κ+5*d^5*ca^4*κ^2+d^3*ca^6*κ^2
        +4*d^3*ca^5*κ*k^2+4*d^3*ca^4*κ^2*k^2-d^3*ca^5*κ^2*D+2*d^3*ca^4*κ*k^2*X+d^5*ca^5
        +7*d^5*ca^4*κ+2*d^3*ca^6*κ-4*d^5*ca^3*κ^2-7*d^3*ca^5*κ^2-4*d^3*ca^5*k^2+6*d^3*ca^4*κ*k^2
        -2*d^3*ca^5*κ*D-d^3*ca^4*κ^2*D-2*d^3*ca^2*κ^3*D^2+2*d^3*ca^4*k^2*X+6*d^3*ca^3*κ*k^2*X
        -d^5*ca^4-9*d^3*ca^5*κ-7*d^5*ca^2*κ^2-6*d^3*ca^4*κ^2-4*d^3*ca^3*κ^3-12*d^3*ca^4*k^2
        -4*d^3*ca^3*κ*k^2-4*d*ca^5*κ*k^2-8*d^3*ca^2*κ^2*k^2-4*d*ca^4*κ^2*k^2-d^3*ca^5*D
        -d^3*ca^4*κ*D+4*d^3*ca^2*κ^3*D-4*d^3*ca^2*κ^2*D^2+4*d*ca^2*κ^2*k^2*D^2
        +8*d^3*ca^3*k^2*X+8*d^3*ca^2*κ*k^2*X-2*d*ca^4*κ*k^2*X-4*d^5*ca^3-4*d^3*ca^5
        -8*d^5*ca^2*κ-14*d^3*ca^4*κ+18*d^3*ca^3*κ^2+4*d*ca^5*κ^2+8*d^3*ca^2*κ^3
        -20*d^3*ca^3*k^2+4*d*ca^5*k^2-6*d*ca^4*κ*k^2+d^3*ca^4*D+2*d^3*ca^3*κ*D
        +8*d^3*ca^2*κ^2*D+2*d^3*κ^3*D^2+2*d*ca^2*κ^3*D^2+14*d*ca^2*κ*k^2*D^2
        +16*d^3*ca^2*k^2*X-2*d*ca^4*k^2*X-6*d^3*ca*κ*k^2*X-6*d*ca^3*κ*k^2*X
        -2*d*ca^4*κ*D*X-6*d^5*ca^2-8*d^3*ca^4+3*d^5*ca*κ+6*d^3*ca^3*κ
        +6*d*ca^5*κ+3*d^5*κ^2+49*d^3*ca^2*κ^2+2*d*ca^4*κ^2+4*d*ca^3*κ^3
        +8*d^3*ca^2*k^2+14*d*ca^4*k^2+4*d*ca^3*κ*k^2+4*d^3*κ^2*k^2
        +4*d*ca^2*κ^2*k^2+4*d^3*ca^3*D-4*d^3*ca^2*κ*D-4*d*ca^4*κ*D
        +d^3*ca*κ^2*D-4*d^3*κ^3*D-4*d*ca^2*κ^3*D+2*c^2*d*κ*k^2*D
        +4*d*ca^2*κ^2*D^2+12*d*ca^2*k^2*D^2-4*d*κ^2*k^2*D^2
        +2*d*ca^4*κ*X+10*d^3*ca*k^2*X-8*d*ca^3*k^2*X
        -10*d^3*κ*k^2*X-8*d*ca^2*κ*k^2*X-2*d*ca^4*D*X
        -6*d*ca^3*κ*D*X-3*d^5*ca-10*d^3*ca^3+4*d*ca^5
        +3*d^5*κ+18*d^3*ca^2*κ+12*d*ca^4*κ+5*d^3*ca*κ^2
        -14*d*ca^3*κ^2-12*d^3*κ^3-8*d*ca^2*κ^3
        +24*d^3*ca*k^2+20*d*ca^3*k^2+2*c^2*d*κ*k^2
        -6*d^3*κ*k^2-14*d*ca^2*κ*k^2-4*d^3*ca^2*D
        -4*d*ca^4*D-4*d^3*ca*κ*D-10*d*ca^3*κ*D
        +d^3*κ^2*D-8*d*ca^2*κ^2*D-2*d^3*κ*D^2
        -2*d*ca^2*κ*D^2-2*d*κ^3*D^2
        -6*d*κ*k^2*D^2+2*d*ca^4*X
        +6*d*ca^3*κ*X-16*d*ca^2*k^2*X
        +6*d*ca*κ*k^2*X-8*d*ca^3*D*X
        -8*d*ca^2*κ*D*X-3*d^5
        -4*d^3*ca^2+12*d*ca^4
        +11*d^3*ca*κ+2*d*ca^3*κ
        -44*d*ca^2*κ^2+4*d^3*k^2
        -22*d*ca^2*k^2
        +5*d^3*ca*D
        -16*d*ca^3*D
        -3*d^3*κ*D-2*d*ca^2*κ*D+4*d*κ^3*D-2*d*κ*k^2*D-2*d*ca^2*D^2+4*d*κ^2*D^2+4*d*k^2*D^2
        +2*d*κ*D^3+8*d*ca^3*X+8*d*ca^2*κ*X-10*d*ca*k^2*X+10*d*κ*k^2*X-16*d*ca^2*D*X+6*d*ca*κ*D*X
        -8*d^3*ca+26*d*ca^3+4*d^3*κ-2*d*ca^2*κ-6*d*ca*κ^2+12*d*κ^3-24*d*ca*k^2+10*d*κ*k^2+3*d^3*D
        -14*d*ca^2*D+10*d*ca*κ*D-2*d*ca*D^2+4*d*κ*D^2+16*d*ca^2*X-6*d*ca*κ*X-10*d*ca*D*X+10*d*κ*D*X
        -22*d^3+32*d*ca^2-20*d*ca*κ-8*d*κ^2-8*d*k^2-16*d*ca*D+2*d*κ*D-4*d*D^2+10*d*ca*X-10*d*κ*X
        +24*d*ca-10*d*κ+18*d*D+8*d) * hX

/-- `dn(z + K) dn z = k'` where both are finite and `dn z ≠ 0` (from Table 22.4.3). -/
theorem jacobiDn_add_K_mul {k : ℂ} (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hn : IsJacobiRegular .n z k) (hd : IsJacobiRegular .d z k) :
    jacobiDn (z + completeEllipticK k) k * jacobiDn z k = jacobiComodulus k := by
  rw [(jacobiDn_shift hk z).1, mul_assoc]
  have hdn : jacobiDn z k ≠ 0 := by
    unfold jacobiDn jacobiPQ jacobiGlaisher
    simp only [reduceCtorEq, ↓reduceIte]
    exact div_ne_zero hd hn
  rw [jacobiNd, jacobiPQ_eq_one_div, ← jacobiDn, one_div_mul_cancel hdn, mul_one]

/-- DLMF 22.8.26–22.8.27: if `z₁ - z₂ = z₂ - z₃ = z₃ - z₄ = K/2` then
`dn z₁ dn z₃ = dn z₂ dn z₄ = k'` (at points `z₃`, `z₄` where `dn` is finite and nonzero). -/
@[dlmf 22.8.E26, dlmf 22.8.E27]
theorem jacobiDn_four_point {k : ℂ} (hk : k ∈ jacobiModulusDomain) {z₁ z₂ z₃ z₄ : ℂ}
    (h₁ : z₁ - z₂ = completeEllipticK k / 2) (h₂ : z₂ - z₃ = completeEllipticK k / 2)
    (h₃ : z₃ - z₄ = completeEllipticK k / 2)
    (hn₃ : IsJacobiRegular .n z₃ k) (hd₃ : IsJacobiRegular .d z₃ k)
    (hn₄ : IsJacobiRegular .n z₄ k) (hd₄ : IsJacobiRegular .d z₄ k) :
    jacobiDn z₁ k * jacobiDn z₃ k = jacobiComodulus k ∧
      jacobiDn z₂ k * jacobiDn z₄ k = jacobiComodulus k := by
  have e₁ : z₁ = z₃ + completeEllipticK k := by linear_combination h₁ + h₂
  have e₂ : z₂ = z₄ + completeEllipticK k := by linear_combination h₂ + h₃
  exact ⟨e₁ ▸ jacobiDn_add_K_mul hk hn₃ hd₃, e₂ ▸ jacobiDn_add_K_mul hk hn₄ hd₄⟩

end DLMF.JacobiElliptic

end
end
