/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.JacobiElliptic.PeriodsPolesZeros

/-!
# Jacobian elliptic functions: addition theorems (DLMF §22.8)

The addition theorems 22.8.1–22.8.18 are stated pointwise for complex `u`, `v` where the
functions involved are finite (`jacobiRegulark`) and the printed denominator is nonzero. They
are proved from the theta-function product identities of §20.7: each formula reduces, after
`k = θ₂²(0)/θ₃²(0)`, `k' = θ₄²(0)/θ₃²(0)` (22.2.2) and clearing denominators, to one identity
`θ_p(0)θ_q(0) θ_p(u+v)θ_q(u-v) = …` (derived from Watson's formulas 20.7.13 and the
Landen-type products) and one identity of the form 20.7.6–20.7.9. The four-point identities
22.8.19–22.8.23 are admitted; 22.8.24–22.8.25 are proved from the values at `2K/3` and the
addition theorem, and 22.8.27 follows from Table 22.4.3.

**Correction.** DLMF 22.8.23 as printed (columns `sn cn, cn dn, cn, dn` with
`z₁ + z₂ + z₃ + z₄ = 2K`) fails numerically (e.g. `k = 0.6`, determinant `≈ -0.107 + 0.033i`).
Replacing the third column by `sn`, or the second by `sn dn`, gives true identities; both are
acquired (`jacobi_det_sum_two_K`, `jacobi_det_sum_two_K'`).
-/

@[expose] public section

open Complex DLMF.Elliptic
open scoped Real

noncomputable section

namespace DLMF.JacobiElliptic

/-! ### Mixed theta products (helpers) -/

lemma p22R1_one_sub_half (x τ : ℂ) :
    jacobiThetaOneTau (x - π / 2) τ = -jacobiThetaTwoTau x τ := by
  rw [jacobiThetaOneTau, sub_add_cancel]

lemma p22R1_three_sub_half (x τ : ℂ) :
    jacobiThetaThreeTau (x - π / 2) τ = jacobiThetaFourTau x τ := by
  rw [jacobiThetaFourTau, show x + π / 2 = (x - π / 2) + π by ring, jacobiThetaThreeTau_add_pi]

lemma p22R1_two_sub_half (x τ : ℂ) :
    jacobiThetaTwoTau (x - π / 2) τ = jacobiThetaOneTau x τ := by
  rw [jacobiThetaOneTau, show x + π / 2 = (x - π / 2) + π by ring, jacobiThetaTwoTau_add_pi,
    neg_neg]

/-- Mixed addition identity (pairs `{1,4}`, `{2,3}`):
`θ₂(0)θ₃(0) θ₁(u+v)θ₄(u-v) = θ₁θ₄(u) θ₂θ₃(v) + θ₂θ₃(u) θ₁θ₄(v)`. -/
theorem p22R1_mixed14 (u v τ : ℂ) (hτ : 0 < τ.im) :
    jacobiThetaTwoTau 0 τ * jacobiThetaThreeTau 0 τ *
        (jacobiThetaOneTau (u + v) τ * jacobiThetaFourTau (u - v) τ) =
      jacobiThetaOneTau u τ * jacobiThetaFourTau u τ *
          (jacobiThetaTwoTau v τ * jacobiThetaThreeTau v τ) +
        jacobiThetaTwoTau u τ * jacobiThetaThreeTau u τ *
          (jacobiThetaOneTau v τ * jacobiThetaFourTau v τ) := by
  have h := DLMF.Theta.p3t_mixed14 u v τ hτ
  simp only [DLMF.Theta.jacobiThetaTwoNullTau, DLMF.Theta.jacobiThetaThreeNullTau] at h
  exact h

lemma p22R1_three_mul_four (z w τ : ℂ) (hτ : 0 < τ.im) :
    jacobiThetaThreeTau z τ * jacobiThetaFourTau w τ =
      jacobiThetaFourTau (z + w) (2 * τ) * jacobiThetaFourTau (z - w) (2 * τ) -
        jacobiThetaOneTau (z + w) (2 * τ) * jacobiThetaOneTau (z - w) (2 * τ) := by
  have h := DLMF.Theta.p20R1_W3 z (w + π / 2) τ hτ
  rw [je22a_thetaThree_add_half_pi, show z + (w + π / 2) = (z + w) + π / 2 by ring,
    show z - (w + π / 2) = (z - w) - π / 2 by ring, je22a_thetaThree_add_half_pi,
    p22R1_three_sub_half, je22a_thetaTwo_add_half_pi, p22R1_two_sub_half] at h
  linear_combination h

/-- Mixed addition identity (pairs `{3,4}`, `{1,2}`). -/
theorem p22R1_mixed34 (u v τ : ℂ) (hτ : 0 < τ.im) :
    jacobiThetaThreeTau 0 τ * jacobiThetaFourTau 0 τ *
        (jacobiThetaThreeTau (u + v) τ * jacobiThetaFourTau (u - v) τ) =
      jacobiThetaThreeTau u τ * jacobiThetaFourTau u τ *
          (jacobiThetaThreeTau v τ * jacobiThetaFourTau v τ) -
        jacobiThetaOneTau u τ * jacobiThetaTwoTau u τ *
          (jacobiThetaOneTau v τ * jacobiThetaTwoTau v τ) := by
  have F := p22R1_three_mul_four (u + v) (u - v) τ hτ
  rw [show u + v + (u - v) = 2 * u by ring, show u + v - (u - v) = 2 * v by ring] at F
  have l0 := DLMF.Theta.p20R1_L40 τ hτ
  have l4u := DLMF.Theta.p20R1_L4 u τ hτ
  have l4v := DLMF.Theta.p20R1_L4 v τ hτ
  have l1u := DLMF.Theta.p20R1_L1 u τ hτ
  have l1v := DLMF.Theta.p20R1_L1 v τ hτ
  simp only [DLMF.Theta.jacobiThetaThreeNullTau,
    DLMF.Theta.jacobiThetaFourNullTau] at l0 l4u l4v l1u l1v
  rw [l0, l4u, l4v, l1u, l1v, F]; ring

/-- Mixed addition identity (pairs `{2,4}`, `{1,3}`). -/
theorem p22R1_mixed24 (u v τ : ℂ) (hτ : 0 < τ.im) :
    jacobiThetaTwoTau 0 τ * jacobiThetaFourTau 0 τ *
        (jacobiThetaTwoTau (u + v) τ * jacobiThetaFourTau (u - v) τ) =
      jacobiThetaTwoTau u τ * jacobiThetaFourTau u τ *
          (jacobiThetaTwoTau v τ * jacobiThetaFourTau v τ) -
        jacobiThetaOneTau u τ * jacobiThetaThreeTau u τ *
          (jacobiThetaOneTau v τ * jacobiThetaThreeTau v τ) := by
  have h := DLMF.Theta.p3t_mixed24 u v τ hτ
  simp only [DLMF.Theta.jacobiThetaTwoNullTau, DLMF.Theta.jacobiThetaFourNullTau] at h
  exact h

/-- `θ₄(0)² θ₄(u+v) θ₄(u-v) = θ₄(u)² θ₄(v)² - θ₁(u)² θ₁(v)²` (alternative form of 20.7.9). -/
theorem p22R1_four_add_mul_sub (u v τ : ℂ) (hτ : 0 < τ.im) :
    jacobiThetaFourTau 0 τ ^ 2 * (jacobiThetaFourTau (u + v) τ * jacobiThetaFourTau (u - v) τ) =
      jacobiThetaFourTau u τ ^ 2 * jacobiThetaFourTau v τ ^ 2 -
        jacobiThetaOneTau u τ ^ 2 * jacobiThetaOneTau v τ ^ 2 := by
  have h9 := DLMF.Theta.jacobiThetaFourTau_add_mul_sub u v τ hτ
  have a2u := DLMF.Theta.jacobiTheta_sq_three_four u τ hτ
  have a2v := DLMF.Theta.jacobiTheta_sq_three_four v τ hτ
  have a3u := DLMF.Theta.jacobiTheta_sq_two_four u τ hτ
  have a3v := DLMF.Theta.jacobiTheta_sq_two_four v τ hτ
  have j := DLMF.Theta.jacobiThetaNull_fourth_power τ hτ
  simp only [DLMF.Theta.jacobiThetaTwoNullTau, DLMF.Theta.jacobiThetaThreeNullTau,
    DLMF.Theta.jacobiThetaFourNullTau] at h9 a2u a2v a3u a3v j
  have h4 := je22a_thetaFour_zero_ne_zero hτ
  have hc : jacobiThetaFourTau 0 τ ^ 4 ≠ 0 := pow_ne_zero _ h4
  apply mul_left_cancel₀ hc
  set a := jacobiThetaTwoTau 0 τ
  set b := jacobiThetaThreeTau 0 τ
  set c := jacobiThetaFourTau 0 τ
  linear_combination c ^ 4 * h9 -
    (b ^ 2 * jacobiThetaFourTau v τ ^ 2 - a ^ 2 * jacobiThetaOneTau v τ ^ 2) * a2u
    - c ^ 2 * jacobiThetaThreeTau u τ ^ 2 * a2v
    + (a ^ 2 * jacobiThetaFourTau v τ ^ 2 - b ^ 2 * jacobiThetaOneTau v τ ^ 2) * a3u
    + c ^ 2 * jacobiThetaTwoTau u τ ^ 2 * a3v
    + (jacobiThetaFourTau u τ ^ 2 * jacobiThetaFourTau v τ ^ 2 -
      jacobiThetaOneTau u τ ^ 2 * jacobiThetaOneTau v τ ^ 2) * j

lemma p22R1_zetak_add (u v k : ℂ) : jacobiZetak (u + v) k = jacobiZetak u k + jacobiZetak v k := by
  simp only [jacobiZetak]; ring

lemma p22R1_four_ne {z k : ℂ} (h : jacobiRegulark .n z k) :
    jacobiThetaFourTau (jacobiZetak z k) (jacobiTauk k) ≠ 0 := by
  intro h'; apply h; simp [jacobiLetterTheta, h']

local notation "θ₁" => jacobiThetaOneTau
local notation "θ₂" => jacobiThetaTwoTau
local notation "θ₃" => jacobiThetaThreeTau
local notation "θ₄" => jacobiThetaFourTau

lemma p22R1_four_sub_half (x τ : ℂ) : θ₄ (x - π / 2) τ = θ₃ x τ := by
  rw [jacobiThetaFourTau, sub_add_cancel]

theorem p22R1_P23 (x y τ : ℂ) (hτ : 0 < τ.im) :
    θ₂ 0 τ * θ₃ 0 τ * (θ₂ (x + y) τ * θ₃ (x - y) τ) =
      θ₂ x τ * θ₃ x τ * (θ₂ y τ * θ₃ y τ) - θ₁ x τ * θ₄ x τ * (θ₁ y τ * θ₄ y τ) := by
  have h := p22R1_mixed14 x (y + π / 2) τ hτ
  rw [show x + (y + π / 2) = (x + y) + π / 2 by ring,
    show x - (y + π / 2) = (x - y) - π / 2 by ring,
    je22a_thetaOne_add_half_pi, p22R1_four_sub_half, je22a_thetaOne_add_half_pi,
    je22a_thetaTwo_add_half_pi, je22a_thetaThree_add_half_pi, je22a_thetaFour_add_half_pi] at h
  linear_combination h

lemma p22R1_P32 (x y τ : ℂ) (hτ : 0 < τ.im) :
    θ₂ 0 τ * θ₃ 0 τ * (θ₃ (x + y) τ * θ₂ (x - y) τ) =
      θ₂ x τ * θ₃ x τ * (θ₂ y τ * θ₃ y τ) + θ₁ x τ * θ₄ x τ * (θ₁ y τ * θ₄ y τ) := by
  have h := p22R1_P23 x (-y) τ hτ
  rw [← sub_eq_add_neg, sub_neg_eq_add, jacobiThetaOneTau_neg, jacobiThetaTwoTau_neg,
    jacobiThetaThreeTau_neg, jacobiThetaFourTau_neg] at h
  linear_combination h

lemma p22R1_P41 (x y τ : ℂ) (hτ : 0 < τ.im) :
    θ₂ 0 τ * θ₃ 0 τ * (θ₄ (x + y) τ * θ₁ (x - y) τ) =
      θ₁ x τ * θ₄ x τ * (θ₂ y τ * θ₃ y τ) - θ₂ x τ * θ₃ x τ * (θ₁ y τ * θ₄ y τ) := by
  have h := p22R1_mixed14 x (-y) τ hτ
  rw [← sub_eq_add_neg, sub_neg_eq_add, jacobiThetaOneTau_neg, jacobiThetaTwoTau_neg,
    jacobiThetaThreeTau_neg, jacobiThetaFourTau_neg] at h
  linear_combination h

lemma p22R1_P42 (x y τ : ℂ) (hτ : 0 < τ.im) :
    θ₂ 0 τ * θ₄ 0 τ * (θ₄ (x + y) τ * θ₂ (x - y) τ) =
      θ₂ x τ * θ₄ x τ * (θ₂ y τ * θ₄ y τ) + θ₁ x τ * θ₃ x τ * (θ₁ y τ * θ₃ y τ) := by
  have h := p22R1_mixed24 x (-y) τ hτ
  rw [← sub_eq_add_neg, sub_neg_eq_add, jacobiThetaOneTau_neg, jacobiThetaTwoTau_neg,
    jacobiThetaThreeTau_neg, jacobiThetaFourTau_neg] at h
  linear_combination h

theorem p22R1_P13 (x y τ : ℂ) (hτ : 0 < τ.im) :
    θ₂ 0 τ * θ₄ 0 τ * (θ₁ (x + y) τ * θ₃ (x - y) τ) =
      θ₂ x τ * θ₄ x τ * (θ₁ y τ * θ₃ y τ) + θ₁ x τ * θ₃ x τ * (θ₂ y τ * θ₄ y τ) := by
  have h := p22R1_mixed24 x (y + π / 2) τ hτ
  rw [show x + (y + π / 2) = (x + y) + π / 2 by ring,
    show x - (y + π / 2) = (x - y) - π / 2 by ring,
    je22a_thetaTwo_add_half_pi, p22R1_four_sub_half, je22a_thetaOne_add_half_pi,
    je22a_thetaTwo_add_half_pi, je22a_thetaThree_add_half_pi, je22a_thetaFour_add_half_pi] at h
  linear_combination -h

lemma p22R1_P31 (x y τ : ℂ) (hτ : 0 < τ.im) :
    θ₂ 0 τ * θ₄ 0 τ * (θ₃ (x + y) τ * θ₁ (x - y) τ) =
      θ₁ x τ * θ₃ x τ * (θ₂ y τ * θ₄ y τ) - θ₂ x τ * θ₄ x τ * (θ₁ y τ * θ₃ y τ) := by
  have h := p22R1_P13 x (-y) τ hτ
  rw [← sub_eq_add_neg, sub_neg_eq_add, jacobiThetaOneTau_neg, jacobiThetaTwoTau_neg,
    jacobiThetaThreeTau_neg, jacobiThetaFourTau_neg] at h
  linear_combination h

lemma p22R1_P43 (x y τ : ℂ) (hτ : 0 < τ.im) :
    θ₃ 0 τ * θ₄ 0 τ * (θ₄ (x + y) τ * θ₃ (x - y) τ) =
      θ₃ x τ * θ₄ x τ * (θ₃ y τ * θ₄ y τ) + θ₁ x τ * θ₂ x τ * (θ₁ y τ * θ₂ y τ) := by
  have h := p22R1_mixed34 x (-y) τ hτ
  rw [← sub_eq_add_neg, sub_neg_eq_add, jacobiThetaOneTau_neg, jacobiThetaTwoTau_neg,
    jacobiThetaThreeTau_neg, jacobiThetaFourTau_neg] at h
  linear_combination h

lemma p22R1_shiftFactor_mul (x y τ : ℂ) :
    je22a_shiftFactor (x + y) τ * je22a_shiftFactor (x - y) τ = je22a_shiftFactor x τ ^ 2 := by
  simp only [je22a_shiftFactor, sq, ← exp_add]; congr 1; ring

lemma p22R1_P21 (x y τ : ℂ) (hτ : 0 < τ.im) :
    θ₃ 0 τ * θ₄ 0 τ * (θ₂ (x + y) τ * θ₁ (x - y) τ) =
      θ₁ x τ * θ₂ x τ * (θ₃ y τ * θ₄ y τ) - θ₃ x τ * θ₄ x τ * (θ₁ y τ * θ₂ y τ) := by
  have h := p22R1_mixed34 (x + π * τ / 2) y τ hτ
  rw [show x + π * τ / 2 + y = (x + y) + π * τ / 2 by ring,
    show x + π * τ / 2 - y = (x - y) + π * τ / 2 by ring, je22a_thetaThree_add_half_tau,
    je22a_thetaFour_add_half_tau, je22a_thetaThree_add_half_tau, je22a_thetaFour_add_half_tau,
    je22a_thetaOne_add_half_tau, je22a_thetaTwo_add_half_tau] at h
  have hm := p22R1_shiftFactor_mul x y τ
  have hS : I * je22a_shiftFactor x τ ^ 2 ≠ 0 :=
    mul_ne_zero I_ne_zero (pow_ne_zero _ (exp_ne_zero _))
  apply mul_left_cancel₀ hS
  linear_combination h - I * θ₃ 0 τ * θ₄ 0 τ * (θ₂ (x + y) τ * θ₁ (x - y) τ) * hm

theorem p22R1_P12 (x y τ : ℂ) (hτ : 0 < τ.im) :
    θ₃ 0 τ * θ₄ 0 τ * (θ₁ (x + y) τ * θ₂ (x - y) τ) =
      θ₁ x τ * θ₂ x τ * (θ₃ y τ * θ₄ y τ) + θ₃ x τ * θ₄ x τ * (θ₁ y τ * θ₂ y τ) := by
  have h := p22R1_P21 x (-y) τ hτ
  rw [← sub_eq_add_neg, sub_neg_eq_add, jacobiThetaOneTau_neg, jacobiThetaTwoTau_neg,
    jacobiThetaThreeTau_neg, jacobiThetaFourTau_neg] at h
  linear_combination h

section
variable (x y τ : ℂ) (hτ : 0 < τ.im)
include hτ

theorem p22R1_nulls :
    θ₂ 0 τ ≠ 0 ∧ θ₃ 0 τ ≠ 0 ∧ θ₄ 0 τ ≠ 0 ∧ θ₃ 0 τ ^ 4 = θ₂ 0 τ ^ 4 + θ₄ 0 τ ^ 4 := by
  have j := DLMF.Theta.jacobiThetaNull_fourth_power τ hτ
  simp only [DLMF.Theta.jacobiThetaTwoNullTau, DLMF.Theta.jacobiThetaThreeNullTau,
    DLMF.Theta.jacobiThetaFourNullTau] at j
  exact ⟨je22a_thetaTwo_zero_ne_zero hτ, je22a_thetaThree_zero_ne_zero hτ,
    je22a_thetaFour_zero_ne_zero hτ, j⟩

theorem p22R1_S3 : θ₃ 0 τ ^ 2 * (θ₃ (x + y) τ * θ₃ (x - y) τ) =
    θ₃ x τ ^ 2 * θ₃ y τ ^ 2 + θ₁ x τ ^ 2 * θ₁ y τ ^ 2 := by
  have h := DLMF.Theta.jacobiThetaThreeTau_add_mul_sub x y τ hτ
  have ex := DLMF.Theta.jacobiTheta_sq_three_four x τ hτ
  have ey := DLMF.Theta.jacobiTheta_sq_two_three y τ hτ
  simp only [DLMF.Theta.jacobiThetaTwoNullTau, DLMF.Theta.jacobiThetaThreeNullTau,
    DLMF.Theta.jacobiThetaFourNullTau] at h ex ey
  obtain ⟨-, -, h4, -⟩ := p22R1_nulls τ hτ
  apply mul_left_cancel₀ (pow_ne_zero 2 h4)
  linear_combination θ₃ 0 τ ^ 2 * h + θ₃ y τ ^ 2 * ex + θ₁ x τ ^ 2 * ey

theorem p22R1_S2 : θ₂ 0 τ ^ 2 * (θ₂ (x + y) τ * θ₂ (x - y) τ) =
    θ₂ x τ ^ 2 * θ₂ y τ ^ 2 - θ₁ x τ ^ 2 * θ₁ y τ ^ 2 := by
  have h := DLMF.Theta.jacobiThetaTwoTau_add_mul_sub x y τ hτ
  have ex := DLMF.Theta.jacobiTheta_sq_two_four x τ hτ
  have ey := DLMF.Theta.jacobiTheta_sq_two_three y τ hτ
  simp only [DLMF.Theta.jacobiThetaTwoNullTau, DLMF.Theta.jacobiThetaThreeNullTau,
    DLMF.Theta.jacobiThetaFourNullTau] at h ex ey
  obtain ⟨-, -, h4, -⟩ := p22R1_nulls τ hτ
  apply mul_left_cancel₀ (pow_ne_zero 2 h4)
  linear_combination θ₂ 0 τ ^ 2 * h + θ₂ y τ ^ 2 * ex - θ₁ x τ ^ 2 * ey

lemma p22R1_S1 : θ₂ 0 τ ^ 2 * (θ₁ (x + y) τ * θ₁ (x - y) τ) =
    θ₁ x τ ^ 2 * θ₂ y τ ^ 2 - θ₂ x τ ^ 2 * θ₁ y τ ^ 2 := by
  have h := DLMF.Theta.jacobiThetaOneTau_add_mul_sub x y τ hτ
  have ex := DLMF.Theta.jacobiTheta_sq_two_three x τ hτ
  have ey := DLMF.Theta.jacobiTheta_sq_two_three y τ hτ
  simp only [DLMF.Theta.jacobiThetaTwoNullTau, DLMF.Theta.jacobiThetaThreeNullTau,
    DLMF.Theta.jacobiThetaFourNullTau] at h ex ey
  obtain ⟨-, -, h4, -⟩ := p22R1_nulls τ hτ
  apply mul_left_cancel₀ (pow_ne_zero 2 h4)
  linear_combination θ₂ 0 τ ^ 2 * h + θ₂ y τ ^ 2 * ex - θ₂ x τ ^ 2 * ey

lemma p22R1_S1' : θ₄ 0 τ ^ 2 * (θ₁ (x + y) τ * θ₁ (x - y) τ) =
    θ₁ x τ ^ 2 * θ₄ y τ ^ 2 - θ₄ x τ ^ 2 * θ₁ y τ ^ 2 := by
  have h := p22R1_S1 x y τ hτ
  have ex := DLMF.Theta.jacobiTheta_sq_two_four x τ hτ
  have ey := DLMF.Theta.jacobiTheta_sq_two_four y τ hτ
  simp only [DLMF.Theta.jacobiThetaTwoNullTau, DLMF.Theta.jacobiThetaThreeNullTau,
    DLMF.Theta.jacobiThetaFourNullTau] at ex ey
  obtain ⟨h2, -, -, -⟩ := p22R1_nulls τ hτ
  apply mul_left_cancel₀ (pow_ne_zero 2 h2)
  linear_combination θ₄ 0 τ ^ 2 * h - θ₁ x τ ^ 2 * ey + θ₁ y τ ^ 2 * ex

lemma p22R1_S2' : θ₄ 0 τ ^ 4 * (θ₂ (x + y) τ * θ₂ (x - y) τ) =
    θ₂ 0 τ ^ 2 * (θ₄ x τ ^ 2 * θ₄ y τ ^ 2) -
      θ₃ 0 τ ^ 2 * (θ₁ x τ ^ 2 * θ₄ y τ ^ 2 + θ₄ x τ ^ 2 * θ₁ y τ ^ 2) +
      θ₂ 0 τ ^ 2 * (θ₁ x τ ^ 2 * θ₁ y τ ^ 2) := by
  have h := p22R1_S2 x y τ hτ
  have ex := DLMF.Theta.jacobiTheta_sq_two_four x τ hτ
  have ey := DLMF.Theta.jacobiTheta_sq_two_four y τ hτ
  simp only [DLMF.Theta.jacobiThetaTwoNullTau, DLMF.Theta.jacobiThetaThreeNullTau,
    DLMF.Theta.jacobiThetaFourNullTau] at ex ey
  obtain ⟨h2, -, -, j⟩ := p22R1_nulls τ hτ
  apply mul_left_cancel₀ (pow_ne_zero 2 h2)
  linear_combination θ₄ 0 τ ^ 4 * h + θ₁ x τ ^ 2 * θ₁ y τ ^ 2 * j -
    (θ₂ 0 τ ^ 2 * θ₄ y τ ^ 2 - θ₃ 0 τ ^ 2 * θ₁ y τ ^ 2) * ex - θ₄ 0 τ ^ 2 * θ₂ x τ ^ 2 * ey

end

/-- DLMF 22.8.1: an addition theorem for `sn`, at points `u`, `v` where the functions
`·n` are finite (`jacobiRegulark .n`) and the printed denominator is nonzero. -/
@[dlmf 22.8.E1]
theorem jacobiSnk_add {k : ℂ} (hk : k ∈ jacobiModulusDomain) {u v : ℂ}
    (hu : jacobiRegulark .n u k) (hv : jacobiRegulark .n v k)
    (hden : (1 - k ^ 2 * jacobiSnk u k ^ 2 * jacobiSnk v k ^ 2) ≠ 0) :
    jacobiSnk (u + v) k =
      (jacobiSnk u k * jacobiCnk v k * jacobiDnk v k + jacobiSnk v k * jacobiCnk u k *
        jacobiDnk u k) / (1 - k ^ 2 * jacobiSnk u k ^ 2 * jacobiSnk v k ^ 2) := by
  have hτ := jacobiTauk_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  have hu' := p22R1_four_ne hu
  have hv' := p22R1_four_ne hv
  rw [eq_div_iff hden]
  simp only [jacobiSnk, jacobiCnk, jacobiDnk, jacobiPQk, jacobiGlaisher, jacobiLetterTheta,
    reduceCtorEq, ↓reduceIte] at hden ⊢
  rw [p22R1_zetak_add]
  rw [jacobiModulusTau] at hmod
  generalize jacobiZetak u k = x at hu' hden ⊢
  generalize jacobiZetak v k = y at hv' hden ⊢
  generalize jacobiTauk k = τ at hτ hu' hv' hden hmod ⊢
  subst hmod
  have h2 := je22a_thetaTwo_zero_ne_zero hτ
  have h3 := je22a_thetaThree_zero_ne_zero hτ
  have h4 := je22a_thetaFour_zero_ne_zero hτ
  have M := p22R1_mixed14 x y τ hτ
  have N := p22R1_four_add_mul_sub x y τ hτ
  have hD : jacobiThetaFourTau (x + y) τ * jacobiThetaFourTau (x - y) τ ≠ 0 := by
    intro h0; apply hden
    field_simp
    linear_combination (-(1 : ℂ)) * N + jacobiThetaFourTau 0 τ ^ 2 * h0
  have hp : jacobiThetaFourTau (x + y) τ ≠ 0 := left_ne_zero_of_mul hD
  field_simp
  linear_combination (-(jacobiThetaTwoTau 0 τ * jacobiThetaThreeTau 0 τ *
    jacobiThetaOneTau (x + y) τ)) * N +
    jacobiThetaFourTau 0 τ ^ 2 * jacobiThetaFourTau (x + y) τ * M

/-- DLMF 22.8.2: an addition theorem for `cn`, at points `u`, `v` where the functions
`·n` are finite (`jacobiRegulark .n`) and the printed denominator is nonzero. -/
@[dlmf 22.8.E2]
theorem jacobiCnk_add {k : ℂ} (hk : k ∈ jacobiModulusDomain) {u v : ℂ}
    (hu : jacobiRegulark .n u k) (hv : jacobiRegulark .n v k)
    (hden : (1 - k ^ 2 * jacobiSnk u k ^ 2 * jacobiSnk v k ^ 2) ≠ 0) :
    jacobiCnk (u + v) k =
      (jacobiCnk u k * jacobiCnk v k - jacobiSnk u k * jacobiDnk u k * jacobiSnk v k *
        jacobiDnk v k) / (1 - k ^ 2 * jacobiSnk u k ^ 2 * jacobiSnk v k ^ 2) := by
  have hτ := jacobiTauk_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  have hu' := p22R1_four_ne hu
  have hv' := p22R1_four_ne hv
  rw [eq_div_iff hden]
  simp only [jacobiSnk, jacobiCnk, jacobiDnk, jacobiPQk, jacobiGlaisher, jacobiLetterTheta,
    reduceCtorEq, ↓reduceIte] at hden ⊢
  rw [p22R1_zetak_add]
  rw [jacobiModulusTau] at hmod
  generalize jacobiZetak u k = x at hu' hden ⊢
  generalize jacobiZetak v k = y at hv' hden ⊢
  generalize jacobiTauk k = τ at hτ hu' hv' hden hmod ⊢
  subst hmod
  have h2 := je22a_thetaTwo_zero_ne_zero hτ
  have h3 := je22a_thetaThree_zero_ne_zero hτ
  have h4 := je22a_thetaFour_zero_ne_zero hτ
  have M := p22R1_mixed24 x y τ hτ
  have N := p22R1_four_add_mul_sub x y τ hτ
  have hD : jacobiThetaFourTau (x + y) τ * jacobiThetaFourTau (x - y) τ ≠ 0 := by
    intro h0; apply hden
    field_simp
    linear_combination (-(1 : ℂ)) * N + jacobiThetaFourTau 0 τ ^ 2 * h0
  have hp : jacobiThetaFourTau (x + y) τ ≠ 0 := left_ne_zero_of_mul hD
  field_simp
  linear_combination (-(jacobiThetaTwoTau 0 τ * jacobiThetaTwoTau (x + y) τ)) * N +
    jacobiThetaFourTau 0 τ * jacobiThetaFourTau (x + y) τ * M

/-- DLMF 22.8.3: an addition theorem for `dn`, at points `u`, `v` where the functions
`·n` are finite (`jacobiRegulark .n`) and the printed denominator is nonzero. -/
@[dlmf 22.8.E3]
theorem jacobiDnk_add {k : ℂ} (hk : k ∈ jacobiModulusDomain) {u v : ℂ}
    (hu : jacobiRegulark .n u k) (hv : jacobiRegulark .n v k)
    (hden : (1 - k ^ 2 * jacobiSnk u k ^ 2 * jacobiSnk v k ^ 2) ≠ 0) :
    jacobiDnk (u + v) k =
      (jacobiDnk u k * jacobiDnk v k - k ^ 2 * jacobiSnk u k * jacobiCnk u k * jacobiSnk v k *
        jacobiCnk v k) / (1 - k ^ 2 * jacobiSnk u k ^ 2 * jacobiSnk v k ^ 2) := by
  have hτ := jacobiTauk_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  have hu' := p22R1_four_ne hu
  have hv' := p22R1_four_ne hv
  rw [eq_div_iff hden]
  simp only [jacobiSnk, jacobiCnk, jacobiDnk, jacobiPQk, jacobiGlaisher, jacobiLetterTheta,
    reduceCtorEq, ↓reduceIte] at hden ⊢
  rw [p22R1_zetak_add]
  rw [jacobiModulusTau] at hmod
  generalize jacobiZetak u k = x at hu' hden ⊢
  generalize jacobiZetak v k = y at hv' hden ⊢
  generalize jacobiTauk k = τ at hτ hu' hv' hden hmod ⊢
  subst hmod
  have h2 := je22a_thetaTwo_zero_ne_zero hτ
  have h3 := je22a_thetaThree_zero_ne_zero hτ
  have h4 := je22a_thetaFour_zero_ne_zero hτ
  have M := p22R1_mixed34 x y τ hτ
  have N := p22R1_four_add_mul_sub x y τ hτ
  have hD : jacobiThetaFourTau (x + y) τ * jacobiThetaFourTau (x - y) τ ≠ 0 := by
    intro h0; apply hden
    field_simp
    linear_combination (-(1 : ℂ)) * N + jacobiThetaFourTau 0 τ ^ 2 * h0
  have hp : jacobiThetaFourTau (x + y) τ ≠ 0 := left_ne_zero_of_mul hD
  field_simp
  linear_combination (-(jacobiThetaThreeTau 0 τ * jacobiThetaThreeTau (x + y) τ)) * N +
    jacobiThetaFourTau 0 τ * jacobiThetaFourTau (x + y) τ * M

/-- DLMF 22.8.4: an addition theorem for `cd`, at points `u`, `v` where the functions
`·d` are finite (`jacobiRegulark .d`) and the printed denominator is nonzero. -/
@[dlmf 22.8.E4]
theorem jacobiCdk_add {k : ℂ} (hk : k ∈ jacobiModulusDomain) {u v : ℂ}
    (hu : jacobiRegulark .d u k) (hv : jacobiRegulark .d v k)
    (hden : (1 + k ^ 2 * jacobiComodulusk k ^ 2 * jacobiSdk u k ^ 2 * jacobiSdk v k ^ 2) ≠ 0) :
    jacobiCdk (u + v) k =
      (jacobiCdk u k * jacobiCdk v k - jacobiComodulusk k ^ 2 * jacobiSdk u k * jacobiNdk u k *
        jacobiSdk v k * jacobiNdk v k) / (1 + k ^ 2 * jacobiComodulusk k ^ 2 * jacobiSdk u k ^ 2 *
          jacobiSdk v k ^ 2) := by
  have hτ := jacobiTauk_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  have hu' : θ₃ (jacobiZetak u k) (jacobiTauk k) ≠ 0 := by
    intro h'; apply hu; simp [jacobiLetterTheta, h']
  have hv' : θ₃ (jacobiZetak v k) (jacobiTauk k) ≠ 0 := by
    intro h'; apply hv; simp [jacobiLetterTheta, h']
  rw [eq_div_iff hden]
  rw [← (jacobi_inversion_k hk).2.1] at hden ⊢
  simp only [jacobiCdk, jacobiSdk, jacobiNdk, jacobiPQk, jacobiGlaisher, jacobiLetterTheta,
    jacobiComodulusTau, reduceCtorEq, ↓reduceIte] at hden ⊢
  rw [p22R1_zetak_add]
  rw [jacobiModulusTau] at hmod
  generalize jacobiZetak u k = x at hu' hden ⊢
  generalize jacobiZetak v k = y at hv' hden ⊢
  generalize jacobiTauk k = τ at hτ hu' hv' hden hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := p22R1_nulls τ hτ
  have hD : (θ₃ (x + y) τ * θ₃ (x - y) τ) ≠ 0 := by
    intro h0; apply hden
    field_simp
    linear_combination -p22R1_S3 x y τ hτ + θ₃ 0 τ ^ 2 * h0
  have hp := left_ne_zero_of_mul hD
  field_simp
  linear_combination (-(θ₂ (x + y) τ * θ₂ 0 τ)) * p22R1_S3 x y τ hτ +
    (θ₃ (x + y) τ * θ₃ 0 τ) * p22R1_P23 x y τ hτ

/-- DLMF 22.8.5: an addition theorem for `sd`, at points `u`, `v` where the functions
`·d` are finite (`jacobiRegulark .d`) and the printed denominator is nonzero. -/
@[dlmf 22.8.E5]
theorem jacobiSdk_add {k : ℂ} (hk : k ∈ jacobiModulusDomain) {u v : ℂ}
    (hu : jacobiRegulark .d u k) (hv : jacobiRegulark .d v k)
    (hden : (1 + k ^ 2 * jacobiComodulusk k ^ 2 * jacobiSdk u k ^ 2 * jacobiSdk v k ^ 2) ≠ 0) :
    jacobiSdk (u + v) k =
      (jacobiSdk u k * jacobiCdk v k * jacobiNdk v k + jacobiSdk v k * jacobiCdk u k *
        jacobiNdk u k) / (1 + k ^ 2 * jacobiComodulusk k ^ 2 * jacobiSdk u k ^ 2 *
          jacobiSdk v k ^ 2) := by
  have hτ := jacobiTauk_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  have hu' : θ₃ (jacobiZetak u k) (jacobiTauk k) ≠ 0 := by
    intro h'; apply hu; simp [jacobiLetterTheta, h']
  have hv' : θ₃ (jacobiZetak v k) (jacobiTauk k) ≠ 0 := by
    intro h'; apply hv; simp [jacobiLetterTheta, h']
  rw [eq_div_iff hden]
  rw [← (jacobi_inversion_k hk).2.1] at hden ⊢
  simp only [jacobiCdk, jacobiSdk, jacobiNdk, jacobiPQk, jacobiGlaisher, jacobiLetterTheta,
    jacobiComodulusTau, reduceCtorEq, ↓reduceIte] at hden ⊢
  rw [p22R1_zetak_add]
  rw [jacobiModulusTau] at hmod
  generalize jacobiZetak u k = x at hu' hden ⊢
  generalize jacobiZetak v k = y at hv' hden ⊢
  generalize jacobiTauk k = τ at hτ hu' hv' hden hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := p22R1_nulls τ hτ
  have hD : (θ₃ (x + y) τ * θ₃ (x - y) τ) ≠ 0 := by
    intro h0; apply hden
    field_simp
    linear_combination -p22R1_S3 x y τ hτ + θ₃ 0 τ ^ 2 * h0
  have hp := left_ne_zero_of_mul hD
  field_simp
  linear_combination (-(θ₂ 0 τ * θ₄ 0 τ * θ₁ (x + y) τ)) * p22R1_S3 x y τ hτ +
    (θ₃ 0 τ ^ 2 * θ₃ (x + y) τ) * p22R1_P13 x y τ hτ

/-- DLMF 22.8.6: an addition theorem for `nd`, at points `u`, `v` where the functions
`·d` are finite (`jacobiRegulark .d`) and the printed denominator is nonzero. -/
@[dlmf 22.8.E6]
theorem jacobiNdk_add {k : ℂ} (hk : k ∈ jacobiModulusDomain) {u v : ℂ}
    (hu : jacobiRegulark .d u k) (hv : jacobiRegulark .d v k)
    (hden : (1 + k ^ 2 * jacobiComodulusk k ^ 2 * jacobiSdk u k ^ 2 * jacobiSdk v k ^ 2) ≠ 0) :
    jacobiNdk (u + v) k =
      (jacobiNdk u k * jacobiNdk v k + k ^ 2 * jacobiSdk u k * jacobiCdk u k * jacobiSdk v k *
        jacobiCdk v k) / (1 + k ^ 2 * jacobiComodulusk k ^ 2 * jacobiSdk u k ^ 2 *
          jacobiSdk v k ^ 2) := by
  have hτ := jacobiTauk_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  have hu' : θ₃ (jacobiZetak u k) (jacobiTauk k) ≠ 0 := by
    intro h'; apply hu; simp [jacobiLetterTheta, h']
  have hv' : θ₃ (jacobiZetak v k) (jacobiTauk k) ≠ 0 := by
    intro h'; apply hv; simp [jacobiLetterTheta, h']
  rw [eq_div_iff hden]
  rw [← (jacobi_inversion_k hk).2.1] at hden ⊢
  simp only [jacobiCdk, jacobiSdk, jacobiNdk, jacobiPQk, jacobiGlaisher, jacobiLetterTheta,
    jacobiComodulusTau, reduceCtorEq, ↓reduceIte] at hden ⊢
  rw [p22R1_zetak_add]
  rw [jacobiModulusTau] at hmod
  generalize jacobiZetak u k = x at hu' hden ⊢
  generalize jacobiZetak v k = y at hv' hden ⊢
  generalize jacobiTauk k = τ at hτ hu' hv' hden hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := p22R1_nulls τ hτ
  have hD : (θ₃ (x + y) τ * θ₃ (x - y) τ) ≠ 0 := by
    intro h0; apply hden
    field_simp
    linear_combination -p22R1_S3 x y τ hτ + θ₃ 0 τ ^ 2 * h0
  have hp := left_ne_zero_of_mul hD
  field_simp
  linear_combination (-(θ₄ (x + y) τ * θ₄ 0 τ)) * p22R1_S3 x y τ hτ +
    (θ₃ (x + y) τ * θ₃ 0 τ) * p22R1_P43 x y τ hτ

/-- DLMF 22.8.7: an addition theorem for `dc`, at points `u`, `v` where the functions
`·c` are finite (`jacobiRegulark .c`) and the printed denominator is nonzero. -/
@[dlmf 22.8.E7]
theorem jacobiDck_add {k : ℂ} (hk : k ∈ jacobiModulusDomain) {u v : ℂ}
    (hu : jacobiRegulark .c u k) (hv : jacobiRegulark .c v k)
    (hden : (1 - jacobiComodulusk k ^ 2 * jacobiSck u k ^ 2 * jacobiSck v k ^ 2) ≠ 0) :
    jacobiDck (u + v) k =
      (jacobiDck u k * jacobiDck v k + jacobiComodulusk k ^ 2 * jacobiSck u k * jacobiNck u k *
        jacobiSck v k * jacobiNck v k) / (1 - jacobiComodulusk k ^ 2 * jacobiSck u k ^ 2 *
          jacobiSck v k ^ 2) := by
  have hτ := jacobiTauk_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  have hu' : θ₂ (jacobiZetak u k) (jacobiTauk k) ≠ 0 := by
    intro h'; apply hu; simp [jacobiLetterTheta, h']
  have hv' : θ₂ (jacobiZetak v k) (jacobiTauk k) ≠ 0 := by
    intro h'; apply hv; simp [jacobiLetterTheta, h']
  rw [eq_div_iff hden]
  rw [← (jacobi_inversion_k hk).2.1] at hden ⊢
  simp only [jacobiDck, jacobiNck, jacobiSck, jacobiPQk, jacobiGlaisher, jacobiLetterTheta,
    jacobiComodulusTau, reduceCtorEq, ↓reduceIte] at hden ⊢
  rw [p22R1_zetak_add]
  rw [jacobiModulusTau] at hmod
  generalize jacobiZetak u k = x at hu' hden ⊢
  generalize jacobiZetak v k = y at hv' hden ⊢
  generalize jacobiTauk k = τ at hτ hu' hv' hden hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := p22R1_nulls τ hτ
  have hD : (θ₂ (x + y) τ * θ₂ (x - y) τ) ≠ 0 := by
    intro h0; apply hden
    field_simp
    linear_combination -p22R1_S2 x y τ hτ + θ₂ 0 τ ^ 2 * h0
  have hp := left_ne_zero_of_mul hD
  field_simp
  linear_combination (-(θ₃ (x + y) τ * θ₃ 0 τ)) * p22R1_S2 x y τ hτ +
    (θ₂ (x + y) τ * θ₂ 0 τ) * p22R1_P32 x y τ hτ

/-- DLMF 22.8.8: an addition theorem for `nc`, at points `u`, `v` where the functions
`·c` are finite (`jacobiRegulark .c`) and the printed denominator is nonzero. -/
@[dlmf 22.8.E8]
theorem jacobiNck_add {k : ℂ} (hk : k ∈ jacobiModulusDomain) {u v : ℂ}
    (hu : jacobiRegulark .c u k) (hv : jacobiRegulark .c v k)
    (hden : (1 - jacobiComodulusk k ^ 2 * jacobiSck u k ^ 2 * jacobiSck v k ^ 2) ≠ 0) :
    jacobiNck (u + v) k =
      (jacobiNck u k * jacobiNck v k + jacobiSck u k * jacobiDck u k * jacobiSck v k *
        jacobiDck v k) / (1 - jacobiComodulusk k ^ 2 * jacobiSck u k ^ 2 * jacobiSck v k ^ 2) := by
  have hτ := jacobiTauk_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  have hu' : θ₂ (jacobiZetak u k) (jacobiTauk k) ≠ 0 := by
    intro h'; apply hu; simp [jacobiLetterTheta, h']
  have hv' : θ₂ (jacobiZetak v k) (jacobiTauk k) ≠ 0 := by
    intro h'; apply hv; simp [jacobiLetterTheta, h']
  rw [eq_div_iff hden]
  rw [← (jacobi_inversion_k hk).2.1] at hden ⊢
  simp only [jacobiDck, jacobiNck, jacobiSck, jacobiPQk, jacobiGlaisher, jacobiLetterTheta,
    jacobiComodulusTau, reduceCtorEq, ↓reduceIte] at hden ⊢
  rw [p22R1_zetak_add]
  rw [jacobiModulusTau] at hmod
  generalize jacobiZetak u k = x at hu' hden ⊢
  generalize jacobiZetak v k = y at hv' hden ⊢
  generalize jacobiTauk k = τ at hτ hu' hv' hden hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := p22R1_nulls τ hτ
  have hD : (θ₂ (x + y) τ * θ₂ (x - y) τ) ≠ 0 := by
    intro h0; apply hden
    field_simp
    linear_combination -p22R1_S2 x y τ hτ + θ₂ 0 τ ^ 2 * h0
  have hp := left_ne_zero_of_mul hD
  field_simp
  linear_combination (-(θ₄ (x + y) τ * θ₄ 0 τ)) * p22R1_S2 x y τ hτ +
    (θ₂ (x + y) τ * θ₂ 0 τ) * p22R1_P42 x y τ hτ

/-- DLMF 22.8.9: an addition theorem for `sc`, at points `u`, `v` where the functions
`·c` are finite (`jacobiRegulark .c`) and the printed denominator is nonzero. -/
@[dlmf 22.8.E9]
theorem jacobiSck_add {k : ℂ} (hk : k ∈ jacobiModulusDomain) {u v : ℂ}
    (hu : jacobiRegulark .c u k) (hv : jacobiRegulark .c v k)
    (hden : (1 - jacobiComodulusk k ^ 2 * jacobiSck u k ^ 2 * jacobiSck v k ^ 2) ≠ 0) :
    jacobiSck (u + v) k =
      (jacobiSck u k * jacobiDck v k * jacobiNck v k + jacobiSck v k * jacobiDck u k *
        jacobiNck u k) / (1 - jacobiComodulusk k ^ 2 * jacobiSck u k ^ 2 * jacobiSck v k ^ 2) := by
  have hτ := jacobiTauk_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  have hu' : θ₂ (jacobiZetak u k) (jacobiTauk k) ≠ 0 := by
    intro h'; apply hu; simp [jacobiLetterTheta, h']
  have hv' : θ₂ (jacobiZetak v k) (jacobiTauk k) ≠ 0 := by
    intro h'; apply hv; simp [jacobiLetterTheta, h']
  rw [eq_div_iff hden]
  rw [← (jacobi_inversion_k hk).2.1] at hden ⊢
  simp only [jacobiDck, jacobiNck, jacobiSck, jacobiPQk, jacobiGlaisher, jacobiLetterTheta,
    jacobiComodulusTau, reduceCtorEq, ↓reduceIte] at hden ⊢
  rw [p22R1_zetak_add]
  rw [jacobiModulusTau] at hmod
  generalize jacobiZetak u k = x at hu' hden ⊢
  generalize jacobiZetak v k = y at hv' hden ⊢
  generalize jacobiTauk k = τ at hτ hu' hv' hden hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := p22R1_nulls τ hτ
  have hD : (θ₂ (x + y) τ * θ₂ (x - y) τ) ≠ 0 := by
    intro h0; apply hden
    field_simp
    linear_combination -p22R1_S2 x y τ hτ + θ₂ 0 τ ^ 2 * h0
  have hp := left_ne_zero_of_mul hD
  field_simp
  linear_combination (-(θ₃ 0 τ * θ₄ 0 τ * θ₁ (x + y) τ)) * p22R1_S2 x y τ hτ +
    (θ₂ 0 τ ^ 2 * θ₂ (x + y) τ) * p22R1_P12 x y τ hτ

/-- DLMF 22.8.10: an addition theorem for `ns`, at points `u`, `v` where the functions
`·s` are finite (`jacobiRegulark .s`) and the printed denominator is nonzero. -/
@[dlmf 22.8.E10]
theorem jacobiNsk_add {k : ℂ} (hk : k ∈ jacobiModulusDomain) {u v : ℂ}
    (hu : jacobiRegulark .s u k) (hv : jacobiRegulark .s v k)
    (hden : (jacobiCsk v k ^ 2 - jacobiCsk u k ^ 2) ≠ 0) :
    jacobiNsk (u + v) k =
      (jacobiNsk u k * jacobiDsk v k * jacobiCsk v k - jacobiNsk v k * jacobiDsk u k *
        jacobiCsk u k) / (jacobiCsk v k ^ 2 - jacobiCsk u k ^ 2) := by
  have hτ := jacobiTauk_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  have hu' : θ₁ (jacobiZetak u k) (jacobiTauk k) ≠ 0 := by
    intro h'; apply hu; simp [jacobiLetterTheta, h']
  have hv' : θ₁ (jacobiZetak v k) (jacobiTauk k) ≠ 0 := by
    intro h'; apply hv; simp [jacobiLetterTheta, h']
  rw [eq_div_iff hden]
  simp only [jacobiNsk, jacobiDsk, jacobiCsk, jacobiPQk, jacobiGlaisher, jacobiLetterTheta,
    reduceCtorEq, ↓reduceIte] at hden ⊢
  rw [p22R1_zetak_add]
  rw [jacobiModulusTau] at hmod
  generalize jacobiZetak u k = x at hu' hden ⊢
  generalize jacobiZetak v k = y at hv' hden ⊢
  generalize jacobiTauk k = τ at hτ hu' hv' hden hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := p22R1_nulls τ hτ
  have hD : (θ₁ (x + y) τ * θ₁ (x - y) τ) ≠ 0 := by
    intro h0; apply hden
    field_simp
    linear_combination θ₄ 0 τ ^ 2 * (-p22R1_S1 x y τ hτ + θ₂ 0 τ ^ 2 * h0)
  have hp := left_ne_zero_of_mul hD
  field_simp
  linear_combination (-(θ₄ (x + y) τ * θ₃ 0 τ)) * p22R1_S1 x y τ hτ +
    (θ₂ 0 τ * θ₁ (x + y) τ) * p22R1_P41 x y τ hτ

/-- DLMF 22.8.11: an addition theorem for `ds`, at points `u`, `v` where the functions
`·s` are finite (`jacobiRegulark .s`) and the printed denominator is nonzero. -/
@[dlmf 22.8.E11]
theorem jacobiDsk_add {k : ℂ} (hk : k ∈ jacobiModulusDomain) {u v : ℂ}
    (hu : jacobiRegulark .s u k) (hv : jacobiRegulark .s v k)
    (hden : (jacobiCsk v k ^ 2 - jacobiCsk u k ^ 2) ≠ 0) :
    jacobiDsk (u + v) k =
      (jacobiDsk u k * jacobiCsk v k * jacobiNsk v k - jacobiDsk v k * jacobiCsk u k *
        jacobiNsk u k) / (jacobiCsk v k ^ 2 - jacobiCsk u k ^ 2) := by
  have hτ := jacobiTauk_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  have hu' : θ₁ (jacobiZetak u k) (jacobiTauk k) ≠ 0 := by
    intro h'; apply hu; simp [jacobiLetterTheta, h']
  have hv' : θ₁ (jacobiZetak v k) (jacobiTauk k) ≠ 0 := by
    intro h'; apply hv; simp [jacobiLetterTheta, h']
  rw [eq_div_iff hden]
  simp only [jacobiNsk, jacobiDsk, jacobiCsk, jacobiPQk, jacobiGlaisher, jacobiLetterTheta,
    reduceCtorEq, ↓reduceIte] at hden ⊢
  rw [p22R1_zetak_add]
  rw [jacobiModulusTau] at hmod
  generalize jacobiZetak u k = x at hu' hden ⊢
  generalize jacobiZetak v k = y at hv' hden ⊢
  generalize jacobiTauk k = τ at hτ hu' hv' hden hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := p22R1_nulls τ hτ
  have hD : (θ₁ (x + y) τ * θ₁ (x - y) τ) ≠ 0 := by
    intro h0; apply hden
    field_simp
    linear_combination θ₄ 0 τ ^ 2 * (-p22R1_S1 x y τ hτ + θ₂ 0 τ ^ 2 * h0)
  have hp := left_ne_zero_of_mul hD
  field_simp
  linear_combination (-(θ₃ (x + y) τ * θ₄ 0 τ)) * p22R1_S1 x y τ hτ +
    (θ₂ 0 τ * θ₁ (x + y) τ) * p22R1_P31 x y τ hτ

/-- DLMF 22.8.12: an addition theorem for `cs`, at points `u`, `v` where the functions
`·s` are finite (`jacobiRegulark .s`) and the printed denominator is nonzero. -/
@[dlmf 22.8.E12]
theorem jacobiCsk_add {k : ℂ} (hk : k ∈ jacobiModulusDomain) {u v : ℂ}
    (hu : jacobiRegulark .s u k) (hv : jacobiRegulark .s v k)
    (hden : (jacobiCsk v k ^ 2 - jacobiCsk u k ^ 2) ≠ 0) :
    jacobiCsk (u + v) k =
      (jacobiCsk u k * jacobiDsk v k * jacobiNsk v k - jacobiCsk v k * jacobiDsk u k *
        jacobiNsk u k) / (jacobiCsk v k ^ 2 - jacobiCsk u k ^ 2) := by
  have hτ := jacobiTauk_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  have hu' : θ₁ (jacobiZetak u k) (jacobiTauk k) ≠ 0 := by
    intro h'; apply hu; simp [jacobiLetterTheta, h']
  have hv' : θ₁ (jacobiZetak v k) (jacobiTauk k) ≠ 0 := by
    intro h'; apply hv; simp [jacobiLetterTheta, h']
  rw [eq_div_iff hden]
  simp only [jacobiNsk, jacobiDsk, jacobiCsk, jacobiPQk, jacobiGlaisher, jacobiLetterTheta,
    reduceCtorEq, ↓reduceIte] at hden ⊢
  rw [p22R1_zetak_add]
  rw [jacobiModulusTau] at hmod
  generalize jacobiZetak u k = x at hu' hden ⊢
  generalize jacobiZetak v k = y at hv' hden ⊢
  generalize jacobiTauk k = τ at hτ hu' hv' hden hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := p22R1_nulls τ hτ
  have hD : (θ₁ (x + y) τ * θ₁ (x - y) τ) ≠ 0 := by
    intro h0; apply hden
    field_simp
    linear_combination θ₄ 0 τ ^ 2 * (-p22R1_S1 x y τ hτ + θ₂ 0 τ ^ 2 * h0)
  have hp := left_ne_zero_of_mul hD
  field_simp
  linear_combination (-(θ₂ (x + y) τ * θ₃ 0 τ * θ₄ 0 τ)) * p22R1_S1 x y τ hτ +
    (θ₂ 0 τ ^ 2 * θ₁ (x + y) τ) * p22R1_P21 x y τ hτ

/-- DLMF 22.8.13: an addition theorem for `sn`, at points `u`, `v` where the functions
`·n` are finite (`jacobiRegulark .n`) and the printed denominator is nonzero. -/
@[dlmf 22.8.E13]
theorem jacobiSnk_add_alt {k : ℂ} (hk : k ∈ jacobiModulusDomain) {u v : ℂ}
    (hu : jacobiRegulark .n u k) (hv : jacobiRegulark .n v k)
    (hden : jacobiSnk u k * jacobiCnk v k * jacobiDnk v k -
      jacobiSnk v k * jacobiCnk u k * jacobiDnk u k ≠ 0) :
    jacobiSnk (u + v) k =
      (jacobiSnk u k ^ 2 - jacobiSnk v k ^ 2) / (jacobiSnk u k * jacobiCnk v k * jacobiDnk v k -
        jacobiSnk v k * jacobiCnk u k * jacobiDnk u k) := by
  have hτ := jacobiTauk_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  have hu' : θ₄ (jacobiZetak u k) (jacobiTauk k) ≠ 0 := by
    intro h'; apply hu; simp [jacobiLetterTheta, h']
  have hv' : θ₄ (jacobiZetak v k) (jacobiTauk k) ≠ 0 := by
    intro h'; apply hv; simp [jacobiLetterTheta, h']
  rw [eq_div_iff hden]
  simp only [jacobiSnk, jacobiCnk, jacobiDnk, jacobiPQk, jacobiGlaisher, jacobiLetterTheta,
    reduceCtorEq, ↓reduceIte] at hden ⊢
  rw [p22R1_zetak_add]
  rw [jacobiModulusTau] at hmod
  generalize jacobiZetak u k = x at hu' hden ⊢
  generalize jacobiZetak v k = y at hv' hden ⊢
  generalize jacobiTauk k = τ at hτ hu' hv' hden hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := p22R1_nulls τ hτ
  have hD : (θ₄ (x + y) τ * θ₁ (x - y) τ) ≠ 0 := by
    intro h0; apply hden
    field_simp
    linear_combination θ₄ 0 τ ^ 2 * (-p22R1_P41 x y τ hτ + θ₂ 0 τ * θ₃ 0 τ * h0)
  have hp := left_ne_zero_of_mul hD
  field_simp
  linear_combination (-(θ₄ 0 τ ^ 2 * θ₁ (x + y) τ)) * p22R1_P41 x y τ hτ +
    (θ₃ 0 τ * θ₂ 0 τ * θ₄ (x + y) τ) * p22R1_S1' x y τ hτ

/-- DLMF 22.8.14: an addition theorem for `sn`, at points `u`, `v` where the functions
`·n` are finite (`jacobiRegulark .n`) and the printed denominator is nonzero. -/
@[dlmf 22.8.E14]
theorem jacobiSnk_add_alt₂ {k : ℂ} (hk : k ∈ jacobiModulusDomain) {u v : ℂ}
    (hu : jacobiRegulark .n u k) (hv : jacobiRegulark .n v k)
    (hden : jacobiCnk u k * jacobiCnk v k +
      jacobiSnk u k * jacobiDnk u k * jacobiSnk v k * jacobiDnk v k ≠ 0) :
    jacobiSnk (u + v) k =
      (jacobiSnk u k * jacobiCnk u k * jacobiDnk v k + jacobiSnk v k * jacobiCnk v k *
        jacobiDnk u k) / (jacobiCnk u k * jacobiCnk v k + jacobiSnk u k * jacobiDnk u k *
          jacobiSnk v k * jacobiDnk v k) := by
  have hτ := jacobiTauk_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  have hu' : θ₄ (jacobiZetak u k) (jacobiTauk k) ≠ 0 := by
    intro h'; apply hu; simp [jacobiLetterTheta, h']
  have hv' : θ₄ (jacobiZetak v k) (jacobiTauk k) ≠ 0 := by
    intro h'; apply hv; simp [jacobiLetterTheta, h']
  rw [eq_div_iff hden]
  simp only [jacobiSnk, jacobiCnk, jacobiDnk, jacobiPQk, jacobiGlaisher, jacobiLetterTheta,
    reduceCtorEq, ↓reduceIte] at hden ⊢
  rw [p22R1_zetak_add]
  rw [jacobiModulusTau] at hmod
  generalize jacobiZetak u k = x at hu' hden ⊢
  generalize jacobiZetak v k = y at hv' hden ⊢
  generalize jacobiTauk k = τ at hτ hu' hv' hden hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := p22R1_nulls τ hτ
  have hD : (θ₄ (x + y) τ * θ₂ (x - y) τ) ≠ 0 := by
    intro h0; apply hden
    field_simp
    linear_combination θ₄ 0 τ ^ 2 * (-p22R1_P42 x y τ hτ + θ₂ 0 τ * θ₄ 0 τ * h0)
  have hp := left_ne_zero_of_mul hD
  field_simp
  linear_combination (-(θ₃ 0 τ * θ₁ (x + y) τ)) * p22R1_P42 x y τ hτ +
    (θ₂ 0 τ * θ₄ (x + y) τ) * p22R1_P12 x y τ hτ

/-- DLMF 22.8.15: an addition theorem for `cn`, at points `u`, `v` where the functions
`·n` are finite (`jacobiRegulark .n`) and the printed denominator is nonzero. -/
@[dlmf 22.8.E15]
theorem jacobiCnk_add_alt {k : ℂ} (hk : k ∈ jacobiModulusDomain) {u v : ℂ}
    (hu : jacobiRegulark .n u k) (hv : jacobiRegulark .n v k)
    (hden : jacobiSnk u k * jacobiCnk v k * jacobiDnk v k -
      jacobiSnk v k * jacobiCnk u k * jacobiDnk u k ≠ 0) :
    jacobiCnk (u + v) k =
      (jacobiSnk u k * jacobiCnk u k * jacobiDnk v k - jacobiSnk v k * jacobiCnk v k *
        jacobiDnk u k) / (jacobiSnk u k * jacobiCnk v k * jacobiDnk v k - jacobiSnk v k *
          jacobiCnk u k * jacobiDnk u k) := by
  have hτ := jacobiTauk_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  have hu' : θ₄ (jacobiZetak u k) (jacobiTauk k) ≠ 0 := by
    intro h'; apply hu; simp [jacobiLetterTheta, h']
  have hv' : θ₄ (jacobiZetak v k) (jacobiTauk k) ≠ 0 := by
    intro h'; apply hv; simp [jacobiLetterTheta, h']
  rw [eq_div_iff hden]
  simp only [jacobiSnk, jacobiCnk, jacobiDnk, jacobiPQk, jacobiGlaisher, jacobiLetterTheta,
    reduceCtorEq, ↓reduceIte] at hden ⊢
  rw [p22R1_zetak_add]
  rw [jacobiModulusTau] at hmod
  generalize jacobiZetak u k = x at hu' hden ⊢
  generalize jacobiZetak v k = y at hv' hden ⊢
  generalize jacobiTauk k = τ at hτ hu' hv' hden hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := p22R1_nulls τ hτ
  have hD : (θ₄ (x + y) τ * θ₁ (x - y) τ) ≠ 0 := by
    intro h0; apply hden
    field_simp
    linear_combination θ₄ 0 τ ^ 2 * (-p22R1_P41 x y τ hτ + θ₂ 0 τ * θ₃ 0 τ * h0)
  have hp := left_ne_zero_of_mul hD
  field_simp
  linear_combination (-(θ₄ 0 τ * θ₂ (x + y) τ)) * p22R1_P41 x y τ hτ +
    (θ₂ 0 τ * θ₄ (x + y) τ) * p22R1_P21 x y τ hτ

/-- DLMF 22.8.16: an addition theorem for `cn`, at points `u`, `v` where the functions
`·n` are finite (`jacobiRegulark .n`) and the printed denominator is nonzero. -/
@[dlmf 22.8.E16]
theorem jacobiCnk_add_alt₂ {k : ℂ} (hk : k ∈ jacobiModulusDomain) {u v : ℂ}
    (hu : jacobiRegulark .n u k) (hv : jacobiRegulark .n v k)
    (hden : jacobiCnk u k * jacobiCnk v k +
      jacobiSnk u k * jacobiDnk u k * jacobiSnk v k * jacobiDnk v k ≠ 0) :
    jacobiCnk (u + v) k =
      (1 - jacobiSnk u k ^ 2 - jacobiSnk v k ^ 2 + k ^ 2 * jacobiSnk u k ^ 2 * jacobiSnk v k ^ 2) /
        (jacobiCnk u k * jacobiCnk v k + jacobiSnk u k * jacobiDnk u k * jacobiSnk v k *
          jacobiDnk v k) := by
  have hτ := jacobiTauk_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  have hu' : θ₄ (jacobiZetak u k) (jacobiTauk k) ≠ 0 := by
    intro h'; apply hu; simp [jacobiLetterTheta, h']
  have hv' : θ₄ (jacobiZetak v k) (jacobiTauk k) ≠ 0 := by
    intro h'; apply hv; simp [jacobiLetterTheta, h']
  rw [eq_div_iff hden]
  simp only [jacobiSnk, jacobiCnk, jacobiDnk, jacobiPQk, jacobiGlaisher, jacobiLetterTheta,
    reduceCtorEq, ↓reduceIte] at hden ⊢
  rw [p22R1_zetak_add]
  rw [jacobiModulusTau] at hmod
  generalize jacobiZetak u k = x at hu' hden ⊢
  generalize jacobiZetak v k = y at hv' hden ⊢
  generalize jacobiTauk k = τ at hτ hu' hv' hden hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := p22R1_nulls τ hτ
  have hD : (θ₄ (x + y) τ * θ₂ (x - y) τ) ≠ 0 := by
    intro h0; apply hden
    field_simp
    linear_combination θ₄ 0 τ ^ 2 * (-p22R1_P42 x y τ hτ + θ₂ 0 τ * θ₄ 0 τ * h0)
  have hp := left_ne_zero_of_mul hD
  field_simp
  linear_combination (-(θ₄ 0 τ ^ 3 * θ₂ (x + y) τ)) * p22R1_P42 x y τ hτ +
    (θ₂ 0 τ * θ₄ (x + y) τ) * p22R1_S2' x y τ hτ

/-- DLMF 22.8.17: an addition theorem for `dn`, at points `u`, `v` where the functions
`·n` are finite (`jacobiRegulark .n`) and the printed denominator is nonzero. -/
@[dlmf 22.8.E17]
theorem jacobiDnk_add_alt {k : ℂ} (hk : k ∈ jacobiModulusDomain) {u v : ℂ}
    (hu : jacobiRegulark .n u k) (hv : jacobiRegulark .n v k)
    (hden : jacobiSnk u k * jacobiCnk v k * jacobiDnk v k -
      jacobiSnk v k * jacobiCnk u k * jacobiDnk u k ≠ 0) :
    jacobiDnk (u + v) k =
      (jacobiSnk u k * jacobiCnk v k * jacobiDnk u k - jacobiSnk v k * jacobiCnk u k *
        jacobiDnk v k) / (jacobiSnk u k * jacobiCnk v k * jacobiDnk v k - jacobiSnk v k *
          jacobiCnk u k * jacobiDnk u k) := by
  have hτ := jacobiTauk_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  have hu' : θ₄ (jacobiZetak u k) (jacobiTauk k) ≠ 0 := by
    intro h'; apply hu; simp [jacobiLetterTheta, h']
  have hv' : θ₄ (jacobiZetak v k) (jacobiTauk k) ≠ 0 := by
    intro h'; apply hv; simp [jacobiLetterTheta, h']
  rw [eq_div_iff hden]
  simp only [jacobiSnk, jacobiCnk, jacobiDnk, jacobiPQk, jacobiGlaisher, jacobiLetterTheta,
    reduceCtorEq, ↓reduceIte] at hden ⊢
  rw [p22R1_zetak_add]
  rw [jacobiModulusTau] at hmod
  generalize jacobiZetak u k = x at hu' hden ⊢
  generalize jacobiZetak v k = y at hv' hden ⊢
  generalize jacobiTauk k = τ at hτ hu' hv' hden hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := p22R1_nulls τ hτ
  have hD : (θ₄ (x + y) τ * θ₁ (x - y) τ) ≠ 0 := by
    intro h0; apply hden
    field_simp
    linear_combination θ₄ 0 τ ^ 2 * (-p22R1_P41 x y τ hτ + θ₂ 0 τ * θ₃ 0 τ * h0)
  have hp := left_ne_zero_of_mul hD
  field_simp
  linear_combination (-(θ₄ 0 τ * θ₃ (x + y) τ)) * p22R1_P41 x y τ hτ +
    (θ₃ 0 τ * θ₄ (x + y) τ) * p22R1_P31 x y τ hτ

/-- DLMF 22.8.18: an addition theorem for `dn`, at points `u`, `v` where the functions
`·n` are finite (`jacobiRegulark .n`) and the printed denominator is nonzero. -/
@[dlmf 22.8.E18]
theorem jacobiDnk_add_alt₂ {k : ℂ} (hk : k ∈ jacobiModulusDomain) {u v : ℂ}
    (hu : jacobiRegulark .n u k) (hv : jacobiRegulark .n v k)
    (hden : jacobiCnk u k * jacobiCnk v k +
      jacobiSnk u k * jacobiDnk u k * jacobiSnk v k * jacobiDnk v k ≠ 0) :
    jacobiDnk (u + v) k =
      (jacobiCnk u k * jacobiDnk u k * jacobiCnk v k * jacobiDnk v k + jacobiComodulusk k ^ 2 *
        jacobiSnk u k * jacobiSnk v k) / (jacobiCnk u k * jacobiCnk v k + jacobiSnk u k *
          jacobiDnk u k * jacobiSnk v k * jacobiDnk v k) := by
  have hτ := jacobiTauk_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  have hu' : θ₄ (jacobiZetak u k) (jacobiTauk k) ≠ 0 := by
    intro h'; apply hu; simp [jacobiLetterTheta, h']
  have hv' : θ₄ (jacobiZetak v k) (jacobiTauk k) ≠ 0 := by
    intro h'; apply hv; simp [jacobiLetterTheta, h']
  rw [eq_div_iff hden]
  rw [← (jacobi_inversion_k hk).2.1] at ⊢
  simp only [jacobiSnk, jacobiCnk, jacobiDnk, jacobiPQk, jacobiGlaisher, jacobiLetterTheta,
    jacobiComodulusTau, reduceCtorEq, ↓reduceIte] at hden ⊢
  rw [p22R1_zetak_add]
  rw [jacobiModulusTau] at hmod
  generalize jacobiZetak u k = x at hu' hden ⊢
  generalize jacobiZetak v k = y at hv' hden ⊢
  generalize jacobiTauk k = τ at hτ hu' hv' hden hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := p22R1_nulls τ hτ
  have hD : (θ₄ (x + y) τ * θ₂ (x - y) τ) ≠ 0 := by
    intro h0; apply hden
    field_simp
    linear_combination θ₄ 0 τ ^ 2 * (-p22R1_P42 x y τ hτ + θ₂ 0 τ * θ₄ 0 τ * h0)
  have hp := left_ne_zero_of_mul hD
  field_simp
  linear_combination (-(θ₃ (x + y) τ * θ₃ 0 τ)) * p22R1_P42 x y τ hτ +
    (θ₄ (x + y) τ * θ₄ 0 τ) * p22R1_P32 x y τ hτ


/-- `1 - k² sn²u sn²v ≠ 0` where `sn` is finite at `u`, `v`, `u + v`, `u - v`. -/
lemma p22R1_den_add_sub {k : ℂ} (hk : k ∈ jacobiModulusDomain) {u v : ℂ}
    (hu : jacobiRegulark .n u k) (hv : jacobiRegulark .n v k)
    (hp : jacobiRegulark .n (u + v) k) (hm : jacobiRegulark .n (u - v) k) :
    1 - k ^ 2 * jacobiSnk u k ^ 2 * jacobiSnk v k ^ 2 ≠ 0 := by
  have hτ := jacobiTauk_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  have hu' := p22R1_four_ne hu
  have hv' := p22R1_four_ne hv
  have hp' := p22R1_four_ne hp
  have hm' := p22R1_four_ne hm
  rw [p22R1_zetak_add] at hp'
  rw [sub_eq_add_neg, p22R1_zetak_add, jacobiZetak_neg, ← sub_eq_add_neg] at hm'
  simp only [jacobiSnk, jacobiPQk, jacobiGlaisher, jacobiLetterTheta, reduceCtorEq, ↓reduceIte]
  rw [jacobiModulusTau] at hmod
  generalize jacobiZetak u k = x at hu' hp' hm' ⊢
  generalize jacobiZetak v k = y at hv' hp' hm' ⊢
  generalize jacobiTauk k = τ at hτ hu' hv' hp' hm' hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := p22R1_nulls τ hτ
  have N4 := p22R1_four_add_mul_sub x y τ hτ
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

lemma p22R1_reg_neg {k : ℂ} {v : ℂ} (hv : jacobiRegulark .n v k) : jacobiRegulark .n (-v) k := by
  unfold jacobiRegulark at *
  rw [jacobiZetak_neg, jacobiLetterTheta_neg]; simpa using hv

/-- Addition formulas at `u + v` and `u - v` with the common denominator. -/
theorem p22R1_add_sub_vals {k : ℂ} (hk : k ∈ jacobiModulusDomain) {u v : ℂ}
    (hu : jacobiRegulark .n u k) (hv : jacobiRegulark .n v k)
    (hp : jacobiRegulark .n (u + v) k) (hm : jacobiRegulark .n (u - v) k) :
    let su := jacobiSnk u k; let cu := jacobiCnk u k; let du := jacobiDnk u k
    let sv := jacobiSnk v k; let cv := jacobiCnk v k; let dv := jacobiDnk v k
    let D := 1 - k ^ 2 * su ^ 2 * sv ^ 2
    D ≠ 0 ∧
    jacobiSnk (u + v) k = (su * cv * dv + sv * cu * du) / D ∧
    jacobiCnk (u + v) k = (cu * cv - su * du * sv * dv) / D ∧
    jacobiDnk (u + v) k = (du * dv - k ^ 2 * su * cu * sv * cv) / D ∧
    jacobiSnk (u - v) k = (su * cv * dv - sv * cu * du) / D ∧
    jacobiCnk (u - v) k = (cu * cv + su * du * sv * dv) / D ∧
    jacobiDnk (u - v) k = (du * dv + k ^ 2 * su * cu * sv * cv) / D := by
  intro su cu du sv cv dv D
  have hD : D ≠ 0 := p22R1_den_add_sub hk hu hv hp hm
  have hD' : 1 - k ^ 2 * jacobiSnk u k ^ 2 * jacobiSnk (-v) k ^ 2 ≠ 0 := by
    have : jacobiSnk (-v) k = -jacobiSnk v k := by simp [jacobiSnk, jacobiPQk_neg]
    rw [this, neg_sq]; exact hD
  have ns : jacobiSnk (-v) k = -sv := by simp [sv, jacobiSnk, jacobiPQk_neg]
  have nc : jacobiCnk (-v) k = cv := by simp [cv, jacobiCnk, jacobiPQk_neg]
  have nd : jacobiDnk (-v) k = dv := by simp [dv, jacobiDnk, jacobiPQk_neg]
  have hv' := p22R1_reg_neg hv
  have a1 := jacobiSnk_add hk hu hv' hD'
  have a2 := jacobiCnk_add hk hu hv' hD'
  have a3 := jacobiDnk_add hk hu hv' hD'
  rw [← sub_eq_add_neg, ns, nc, nd, neg_sq] at a1 a2 a3
  refine ⟨hD, jacobiSnk_add hk hu hv hD, jacobiCnk_add hk hu hv hD, jacobiDnk_add hk hu hv hD,
    ?_, ?_, ?_⟩
  · rw [a1]; ring
  · rw [a2]; ring
  · rw [a3]; ring

lemma p22R1_pq_ne {p q : JacobiLetter} (hpq : p ≠ q) {z k : ℂ}
    (hp : jacobiRegulark p z k) (hq : jacobiRegulark q z k) : jacobiPQk p q z k ≠ 0 := by
  unfold jacobiPQk jacobiGlaisher
  simp only [hpq, ↓reduceIte]
  exact div_ne_zero hp hq

theorem p22R1_reg_add_K {k : ℂ} (hk : k ∈ jacobiModulusDomain) (r : JacobiLetter) (z : ℂ) :
    jacobiRegulark r (z + compEllIntKk k) k ↔ jacobiRegulark r.swapK z k := by
  have hK := compEllIntKk_ne_zero hk
  have hτ := jacobiTauk_im_pos hk
  have hz : jacobiZetak (z + compEllIntKk k) k = jacobiZetak z k + π / 2 := by
    rw [jacobiZetak, jacobiZetak]; field_simp
  unfold jacobiRegulark
  rw [hz, je22a_letterTheta_add_half_pi hτ]
  exact ⟨fun h => right_ne_zero_of_mul h,
    fun h => mul_ne_zero (je22a_betaK_ne_zero hτ r) h⟩

theorem p22R1_reg_add_two_K {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ) :
    jacobiRegulark .n (z + 2 * compEllIntKk k) k ↔ jacobiRegulark .n z k := by
  rw [show z + 2 * compEllIntKk k = z + compEllIntKk k + compEllIntKk k by ring,
    p22R1_reg_add_K hk, p22R1_reg_add_K hk]
  rfl

/-- Theta functions at real multiples of `π`. -/
theorem p22R1_theta_real_ne {τ : ℂ} (hτ : 0 < τ.im) (r : ℝ) :
    jacobiThetaFourTau (r * π) τ ≠ 0 ∧ jacobiThetaThreeTau (r * π) τ ≠ 0 ∧
      ((∀ m : ℤ, r ≠ m) → jacobiThetaOneTau (r * π) τ ≠ 0) := by
  obtain ⟨h1, -, h3, h4⟩ := DLMF.Theta.jacobiThetaTau_eq_zero_iff hτ (r * π)
  have key : ∀ (y x : ℝ), (r : ℂ) * π = (y + x * τ) * π → x = 0 ∧ r = y := by
    intro y x h
    have h' : ((r - y : ℝ) : ℂ) + (-x : ℝ) * τ = 0 := by
      have := mul_right_cancel₀ (ofReal_ne_zero.mpr Real.pi_ne_zero) h
      push_cast; linear_combination this
    have := DLMF.Theta.th20_lattice_eq_zero hτ (a := r - y) (b := -x) (by rw [h', zero_mul])
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

lemma p22R1_zetak_mul_K {k : ℂ} (hk : k ∈ jacobiModulusDomain) (c : ℝ) :
    jacobiZetak (c * compEllIntKk k) k = ((c / 2 : ℝ) : ℂ) * π := by
  have hK := compEllIntKk_ne_zero hk
  rw [jacobiZetak]; push_cast; field_simp

lemma p22R1_reg_mul_K {k : ℂ} (hk : k ∈ jacobiModulusDomain) (c : ℝ) :
    jacobiRegulark .n (c * compEllIntKk k) k ∧ jacobiRegulark .d (c * compEllIntKk k) k ∧
      ((∀ m : ℤ, c / 2 ≠ m) → jacobiRegulark .s (c * compEllIntKk k) k) := by
  have hτ := jacobiTauk_im_pos hk
  obtain ⟨h4, h3, h1⟩ := p22R1_theta_real_ne hτ (c / 2)
  obtain ⟨n2, n3, n4, -⟩ := p22R1_nulls _ hτ
  simp only [jacobiRegulark, jacobiLetterTheta, p22R1_zetak_mul_K hk]
  exact ⟨div_ne_zero h4 n4, div_ne_zero h3 n3,
    fun h => mul_ne_zero (div_ne_zero n3 (mul_ne_zero n2 n4)) (h1 h)⟩

/-- Values at `2K/3` and `4K/3`. -/
theorem p22R1_third_vals {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    let a := 2 * compEllIntKk k / 3
    let b := 4 * compEllIntKk k / 3
    jacobiRegulark .n a k ∧ jacobiRegulark .n b k ∧ jacobiSnk a k ≠ 0 ∧
      jacobiSnk b k = jacobiSnk a k ∧ jacobiCnk b k = -jacobiCnk a k ∧
      jacobiDnk b k = jacobiDnk a k ∧ 1 - k ^ 2 * jacobiSnk a k ^ 4 ≠ 0 ∧
      1 - k ^ 2 * jacobiSnk a k ^ 4 = 2 * jacobiCnk a k * jacobiDnk a k ∧
      jacobiCnk a k ^ 2 - jacobiSnk a k ^ 2 * jacobiDnk a k ^ 2 =
        -2 * jacobiCnk a k ^ 2 * jacobiDnk a k := by
  intro a b
  have ea : a = ((2 / 3 : ℝ) : ℂ) * compEllIntKk k := by simp only [a]; push_cast; ring
  have eb : b = ((4 / 3 : ℝ) : ℂ) * compEllIntKk k := by simp only [b]; push_cast; ring
  obtain ⟨hna, -, hsa⟩ := p22R1_reg_mul_K hk (2 / 3)
  obtain ⟨hnb, -, -⟩ := p22R1_reg_mul_K hk (4 / 3)
  rw [← ea] at hna hsa; rw [← eb] at hnb
  have hsa' : jacobiSnk a k ≠ 0 := by
    refine p22R1_pq_ne (by decide) (hsa ?_) hna
    intro m hm
    have h3 : (3 * m : ℝ) = 1 := by linarith
    have h3' : (3 * m : ℤ) = 1 := by exact_mod_cast h3
    omega
  have e2 : b = -a + 2 * compEllIntKk k := by simp only [a, b]; ring
  have vs : jacobiSnk b k = jacobiSnk a k := by
    rw [e2, (jacobiSnk_shift hk _).2.2.2.1]
    simp [jacobiSnk, jacobiPQk_neg]
  have vc : jacobiCnk b k = -jacobiCnk a k := by
    rw [e2, (jacobiCnk_shift hk _).2.2.2.1]
    simp [jacobiCnk, jacobiPQk_neg]
  have vd : jacobiDnk b k = jacobiDnk a k := by
    rw [e2, (jacobiDnk_shift hk _).2.2.2.1]
    simp [jacobiDnk, jacobiPQk_neg]
  have e2a : 2 * a = b := by simp only [a, b]; ring
  have hn0 : jacobiRegulark .n (a - a) k := by
    rw [sub_self]; simpa using (p22R1_reg_mul_K hk 0).1
  have hnaa : jacobiRegulark .n (a + a) k := by rw [← two_mul, e2a]; exact hnb
  have hD4 := p22R1_den_add_sub hk hna hna hnaa hn0
  have hD : 1 - k ^ 2 * jacobiSnk a k ^ 4 ≠ 0 := by convert hD4 using 2; ring
  have d1 := jacobiSnk_add hk hna hna hD4
  have d2 := jacobiCnk_add hk hna hna hD4
  rw [← two_mul, e2a, vs] at d1; rw [← two_mul, e2a, vc] at d2
  rw [eq_div_iff hD4] at d1 d2
  have E1 : 1 - k ^ 2 * jacobiSnk a k ^ 4 = 2 * jacobiCnk a k * jacobiDnk a k := by
    apply mul_left_cancel₀ hsa'; linear_combination d1
  refine ⟨hna, hnb, hsa', vs, vc, vd, hD, E1, ?_⟩
  linear_combination -d2 - jacobiCnk a k * E1

theorem p22R1_k_ne {k : ℂ} (hk : k ∈ jacobiModulusDomain) : k ≠ 0 := by
  rintro rfl; simp [jacobiModulusDomain] at hk

theorem p22R1_kappa_ne {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    jacobiDnk (2 * compEllIntKk k / 3) k ≠ 0 := by
  obtain ⟨hn, hd, -⟩ := p22R1_reg_mul_K hk (2 / 3)
  have ea : 2 * compEllIntKk k / 3 = ((2 / 3 : ℝ) : ℂ) * compEllIntKk k := by push_cast; ring
  rw [ea]; exact p22R1_pq_ne (by decide) hd hn

/-- `sn² + cn² = 1`, `k² sn² + dn² = 1` (copy of 22.6.1 for use in this file). -/
lemma p22R1_sq_sum {k : ℂ} (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hn : jacobiRegulark .n z k) :
    jacobiSnk z k ^ 2 + jacobiCnk z k ^ 2 = 1 ∧ k ^ 2 * jacobiSnk z k ^ 2 + jacobiDnk z k ^ 2 = 1 :=
        by
  have hτ := jacobiTauk_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  have hn' : jacobiThetaFourTau (jacobiZetak z k) (jacobiTauk k) ≠ 0 := by
    intro h; apply hn; simp [jacobiLetterTheta, h]
  simp only [jacobiSnk, jacobiCnk, jacobiDnk, jacobiPQk, jacobiGlaisher, jacobiLetterTheta,
    reduceCtorEq, ↓reduceIte]
  rw [jacobiModulusTau] at hmod
  generalize jacobiZetak z k = ζ at hn' ⊢
  generalize jacobiTauk k = τ at hτ hn' hmod ⊢
  subst hmod
  have h2 := je22a_thetaTwo_zero_ne_zero hτ
  have h3 := je22a_thetaThree_zero_ne_zero hτ
  have h4 := je22a_thetaFour_zero_ne_zero hτ
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
    (hz : z 0 + z 1 + z 2 + z 3 = 0) (hreg : ∀ j, jacobiRegulark .n (z j) k) :
    Matrix.det (Matrix.of fun i : Fin 4 =>
      ![jacobiSnk (z i) k, jacobiCnk (z i) k, jacobiDnk (z i) k, 1]) = 0 := by
  sorry

/-- **Admitted.** DLMF 22.8.21: if `z₁ + z₂ + z₃ + z₄ = 0` then
`k'² - k'²k² ∏ sn zⱼ + k² ∏ cn zⱼ - ∏ dn zⱼ = 0`. -/
@[dlmf 22.8.E19, dlmf 22.8.E21]
theorem jacobi_prod_sum_zero {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : Fin 4 → ℂ)
    (hz : z 0 + z 1 + z 2 + z 3 = 0) (hreg : ∀ j, jacobiRegulark .n (z j) k) :
    jacobiComodulusk k ^ 2 - jacobiComodulusk k ^ 2 * k ^ 2 * ∏ j, jacobiSnk (z j) k +
      k ^ 2 * ∏ j, jacobiCnk (z j) k - ∏ j, jacobiDnk (z j) k = 0 := by
  sorry

/-- **Admitted, corrected.** DLMF 22.8.22–22.8.23 with the third column corrected to `sn`: if
`z₁ + z₂ + z₃ + z₄ = 2K` then `det [sn zⱼ cn zⱼ, cn zⱼ dn zⱼ, sn zⱼ, dn zⱼ] = 0`.
Corrected from the printed DLMF formula: with the printed third column `cn zⱼ` the determinant
is nonzero (≈ -0.107 + 0.033i at `k = 0.6`); with `sn zⱼ` it vanishes. -/
@[dlmf 22.8.E22,
  dlmf 22.8.E23 "corrected: printed third column cn z_j replaced by sn z_j"]
theorem jacobi_det_sum_two_K {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : Fin 4 → ℂ)
    (hz : z 0 + z 1 + z 2 + z 3 = 2 * compEllIntKk k) (hreg : ∀ j, jacobiRegulark .n (z j) k) :
    Matrix.det (Matrix.of fun i : Fin 4 =>
      ![jacobiSnk (z i) k * jacobiCnk (z i) k, jacobiCnk (z i) k * jacobiDnk (z i) k,
        jacobiSnk (z i) k, jacobiDnk (z i) k]) = 0 := by
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
    (hz : z 0 + z 1 + z 2 + z 3 = 2 * compEllIntKk k) (hreg : ∀ j, jacobiRegulark .n (z j) k) :
    Matrix.det (Matrix.of fun i : Fin 4 =>
      ![jacobiSnk (z i) k * jacobiCnk (z i) k, jacobiSnk (z i) k * jacobiDnk (z i) k,
        jacobiCnk (z i) k, jacobiDnk (z i) k]) = 0 := by
  sorry

/-- The expression of DLMF 22.8.25 at `z₁`, with `z₂ = z₁ - 2K/3`, `z₃ = z₂ - 2K/3`. -/
def jacobiDnThreePointExpr (z k : ℂ) : ℂ :=
  let d₁ := jacobiDnk z k
  let d₂ := jacobiDnk (z - 2 * compEllIntKk k / 3) k
  let d₃ := jacobiDnk (z - 4 * compEllIntKk k / 3) k
  (d₂ + d₃) * (d₃ + d₁) * (d₁ + d₂) / (d₁ + d₂ + d₃)

/-- DLMF 22.8.24–22.8.25: if `z₁ - z₂ = z₂ - z₃ = 2K/3` then
`(dn z₂ + dn z₃)(dn z₃ + dn z₁)(dn z₁ + dn z₂)/(dn z₁ + dn z₂ + dn z₃)` is independent of the
`zⱼ` (at points where the `dn zⱼ` are finite and the denominator is nonzero). -/
@[dlmf 22.8.E24, dlmf 22.8.E25]
theorem jacobiDnThreePointExpr_const {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    ∃ c : ℂ, ∀ z : ℂ, (∀ j : ℕ, jacobiRegulark .n (z - 2 * j * compEllIntKk k / 3) k) →
      jacobiDnk z k + jacobiDnk (z - 2 * compEllIntKk k / 3) k +
        jacobiDnk (z - 4 * compEllIntKk k / 3) k ≠ 0 →
      jacobiDnThreePointExpr z k = c := by
  have W := p22R1_third_vals hk
  simp only at W
  obtain ⟨hna, -, hsa, -, -, -, -, E1, E2⟩ := W
  obtain ⟨ha1, ha2⟩ := p22R1_sq_sum hk hna
  have hκ := p22R1_kappa_ne hk
  have hk0 : k ≠ 0 := p22R1_k_ne hk
  have hF2 : 1 + 2 * jacobiDnk (2 * compEllIntKk k / 3) k ≠ 0 := by
    intro h
    have hY := mul_inv_cancel₀ hsa
    generalize (jacobiSnk (2 * compEllIntKk k / 3) k)⁻¹ = Y at hY
    have : (1 : ℂ) = 0 := by
      linear_combination (-4 * Y ^ 2) * E2 + (-jacobiSnk (2 * compEllIntKk k / 3) k * Y - 1) * hY +
        (-2 * jacobiSnk (2 * compEllIntKk k / 3) k ^ 2 * jacobiDnk (2 * compEllIntKk k / 3) k * Y ^ 2 +
          jacobiSnk (2 * compEllIntKk k / 3) k ^ 2 * Y ^ 2 +
          4 * jacobiCnk (2 * compEllIntKk k / 3) k ^ 2 * Y ^ 2) * h
    exact one_ne_zero this
  refine ⟨2 * jacobiDnk (2 * compEllIntKk k / 3) k * (1 + jacobiDnk (2 * compEllIntKk k / 3) k) ^ 2 /
    (1 + 2 * jacobiDnk (2 * compEllIntKk k / 3) k), fun z hreg hden => ?_⟩
  have hn := hreg 0
  have hm := hreg 1
  have hb := hreg 2
  rw [show z - 2 * ((0 : ℕ) : ℂ) * compEllIntKk k / 3 = z by push_cast; ring] at hn
  rw [show z - 2 * ((1 : ℕ) : ℂ) * compEllIntKk k / 3 = z - 2 * compEllIntKk k / 3 by
    push_cast; ring] at hm
  have eb : z - 2 * ((2 : ℕ) : ℂ) * compEllIntKk k / 3 + 2 * compEllIntKk k =
      z + 2 * compEllIntKk k / 3 := by push_cast; ring
  have hp : jacobiRegulark .n (z + 2 * compEllIntKk k / 3) k := by
    rw [← eb, p22R1_reg_add_two_K hk]; exact hb
  have d3 : jacobiDnk (z - 4 * compEllIntKk k / 3) k = jacobiDnk (z + 2 * compEllIntKk k / 3) k := by
    rw [← (jacobiDnk_shift hk _).2.2.2.1]; congr 1; ring
  obtain ⟨hD, -, -, e3, -, -, e6⟩ := p22R1_add_sub_vals hk hn hna hp hm
  obtain ⟨h1, h2⟩ := p22R1_sq_sum hk hn
  unfold jacobiDnThreePointExpr
  simp only
  rw [d3] at hden ⊢
  rw [e3, e6] at hden ⊢
  generalize jacobiSnk z k = s at *
  generalize jacobiCnk z k = c at *
  generalize jacobiDnk z k = d at *
  generalize jacobiSnk (2 * compEllIntKk k / 3) k = sa at *
  generalize jacobiCnk (2 * compEllIntKk k / 3) k = ca at *
  generalize jacobiDnk (2 * compEllIntKk k / 3) k = κ at *
  generalize hDdef : 1 - k ^ 2 * s ^ 2 * sa ^ 2 = D at hD hden ⊢
  have hden' : d * D + (d * κ + k ^ 2 * s * c * sa * ca) + (d * κ - k ^ 2 * s * c * sa * ca) ≠ 0 := by
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
                                                                                +4*d*sa^2*ca*κ*k^4*X+1/2*d^3*ca^3*κ^2*D*X+1/2*d^3*ca^2*κ^3*D*X+3/2*d^3*sa^2*ca*k^2*D*X-1/2*d^3*sa^2*κ*k^2*D*X+2*d^3*κ^4*D^2*X+2*s^2*d*κ^2*k^2*D^2*X-3*d^3*ca*κ^2*k^2*X^2-3*d*sa^2*ca*k^4*X^2-d*sa^2*ca^2*k^2*D*X^2-2*d^5*ca^2*κ^2-7/2*d^3*ca^3*κ^3-3*d^5*sa^2*k^2-3*s^2*d^3*ca^2*k^2+9/2*d^3*sa^2*ca^2*k^2-3*s^2*d^3*ca*κ*k^2+9/2*d^3*sa^2*ca*κ*k^2+4*s^2*d*ca^3*κ*k^2+4*d^3*ca^3*κ*k^2+2*d*sa^2*ca^3*κ*k^2+3*s^2*d^3*κ^2*k^2-1/2*d^3*ca^3*κ^2*D-1/2*d^3*ca^2*κ^3*D+5/2*d^3*sa^2*ca*k^2*D-1/2*d^3*sa^2*κ*k^2*D-4*s^2*d*κ^3*k^2*D-8*s^2*d*κ*k^4*D+4*s^2*d*κ^2*k^2*D^2+3/2*d^5*ca*κ^2*X+2*d^3*ca^3*κ^2*X+3*d^5*κ^3*X+5/2*d^3*ca^2*κ^3*X+4*d^3*sa^2*ca*k^2*X+2*s^2*d*ca^3*k^2*X-2*d^3*ca^3*k^2*X+3*s^2*d^3*κ*k^2*X+19/2*d^3*sa^2*κ*k^2*X+6*d^3*ca^2*κ*k^2*X+d*sa^2*ca^2*κ*k^2*X+12*d^3*ca*κ^2*k^2*X+2*d*ca^3*κ^2*k^2*X+5*d*ca^2*κ^3*k^2*X-4*d*sa^2*ca*k^4*X+4*d*sa^2*κ*k^4*X-1/2*d^3*ca^2*κ^2*D*X+1/2*d^3*ca*κ^3*D*X-4*d^3*κ^4*D*X+5/2*d^3*sa^2*k^2*D*X-3*d*sa^2*ca^2*k^2*D*X-4*s^2*d*κ^2*k^2*D*X-6*s^2*d*k^4*D*X+2*c^2*d*k^4*D*X-4*d*κ^3*k^2*D^2*X+d*sa^2*ca^2*k^2*X^2-5*d^3*κ^2*k^2*X^2+d*ca^2*κ^2*k^2*X^2-5*d*sa^2*k^4*X^2-3*d*sa^2*ca*k^2*D*X^2-3*d^5*ca*κ^2+3/2*d^3*ca^3*κ^2-5/2*d^3*ca^2*κ^3-3*s^2*d^3*ca*k^2+7/2*d^3*sa^2*ca*k^2+6*s^2*d*ca^3*k^2-4*d^3*ca^3*k^2-d*sa^2*ca^3*k^2+3*s^2*d^3*κ*k^2+19/2*d^3*sa^2*κ*k^2+8*s^2*d*ca^2*κ*k^2+4*d^3*ca^2*κ*k^2+d*sa^2*ca^2*κ*k^2-12*s^2*d*κ^3*k^2-8*s^2*d*κ*k^4+1/2*d^3*ca^2*κ^2*D-1/2*d^3*ca*κ^3*D+9/2*d^3*sa^2*k^2*D-2*d*sa^2*ca^2*k^2*D+2*s^2*d*ca*κ*k^2*D-8*s^2*d*κ^2*k^2*D-16*s^2*d*k^4*D+3/2*d^5*κ^2*X+4*d^3*ca^2*κ^2*X-9/2*d^3*ca*κ^3*X-2*d*ca^3*κ^3*X-12*d^3*κ^4*X+3*d^3*sa^2*k^2*X+6*s^2*d*ca^2*k^2*X-6*d^3*ca^2*k^2*X+d*sa^2*ca^2*k^2*X+14*d^3*ca*κ*k^2*X-4*d*sa^2*ca*κ*k^2*X-2*d*ca^3*κ*k^2*X-12*s^2*d*κ^2*k^2*X+2*d^3*κ^2*k^2*X-3*d*ca^2*κ^2*k^2*X+4*d*ca*κ^3*k^2*X-6*s^2*d*k^4*X+2*c^2*d*k^4*X-8*d*sa^2*k^4*X-3/2*d^3*ca*κ^2*D*X+1/2*d^3*κ^3*D*X-8*d*sa^2*ca*k^2*D*X-2*d*κ^4*D^2*X-d*sa^2*k^2*D^2*X-6*d*κ^2*k^2*D^2*X+3*d*sa^2*ca*k^2*X^2+3*d*ca*κ^2*k^2*X^2+d*ca^2*κ^2*D*X^2-5*d*sa^2*k^2*D*X^2-3*d^5*κ^2+9/2*d^3*ca^2*κ^2+9/2*d^3*ca*κ^3+2*d*ca^3*κ^3-3*s^2*d^3*k^2-5/2*d^3*sa^2*k^2+14*s^2*d*ca^2*k^2-12*d^3*ca^2*k^2-d*sa^2*ca^2*k^2+6*s^2*d*ca*κ*k^2-4*d*sa^2*ca*κ*k^2-4*d*ca^3*κ*k^2-16*s^2*d*κ^2*k^2-4*d^3*κ^2*k^2-16*s^2*d*k^4+5/2*d^3*ca*κ^2*D-1/2*d^3*κ^3*D+2*s^2*d*ca*k^2*D-6*d*sa^2*ca*k^2*D+10*s^2*d*κ*k^2*D-8*d^3*κ*k^2*D-d*sa^2*k^2*D^2+4*d*κ^2*k^2*D^2+6*d^3*ca*κ^2*X-2*d*ca^3*κ^2*X-9/2*d^3*κ^3*X-d*ca^2*κ^3*X+10*s^2*d*ca*k^2*X-10*d^3*ca*k^2*X+4*d*sa^2*ca*k^2*X+2*d*ca^3*k^2*X+8*s^2*d*κ*k^2*X+14*d^3*κ*k^2*X-9*d*sa^2*κ*k^2*X-8*d*ca^2*κ*k^2*X-12*d*ca*κ^2*k^2*X+4*d*κ^3*k^2*X+7/2*d^3*κ^2*D*X+d*ca^2*κ^2*D*X+4*d*κ^4*D*X+6*s^2*d*k^2*D*X-8*d^3*k^2*D*X-11*d*sa^2*k^2*D*X-2*d*k^4*D*X+4*d*κ*k^2*D^2*X-d*ca^2*κ^2*X^2+5*d*sa^2*k^2*X^2+5*d*κ^2*k^2*X^2+3*d*ca*κ^2*D*X^2+7/2*d^3*ca*κ^2-d*ca^3*κ^2+19/2*d^3*κ^3+d*ca^2*κ^3+16*s^2*d*ca*k^2-24*d^3*ca*k^2+3*d*sa^2*ca*k^2+4*d*ca^3*k^2+8*s^2*d*κ*k^2-2*d^3*κ*k^2-9*d*sa^2*κ*k^2-4*d*ca^2*κ*k^2+9/2*d^3*κ^2*D-2*d*ca^2*κ^2*D+16*s^2*d*k^2*D-16*d^3*k^2*D-8*d*sa^2*k^2*D+14*d*κ*k^2*D^2+3*d^3*κ^2*X-5*d*ca^2*κ^2*X+4*d*ca*κ^3*X+12*d*κ^4*X+6*s^2*d*k^2*X-8*d^3*k^2*X+8*d*sa^2*k^2*X+6*d*ca^2*k^2*X-14*d*ca*κ*k^2*X+4*d*κ^2*k^2*X-2*d*k^4*X+2*d*ca*κ^2*D*X+d*κ^2*D^2*X+6*d*k^2*D^2*X-3*d*ca*κ^2*X^2+5*d*κ^2*D*X^2-5/2*d^3*κ^2-d*ca^2*κ^2-4*d*ca*κ^3-2*s^2*d*k^2-20*d^3*k^2+10*d*sa^2*k^2+14*d*ca^2*k^2-6*d*ca*κ^2*D+8*d*κ*k^2*D-d*κ^2*D^2+12*d*k^2*D^2-8*d*ca*κ^2*X+d*κ^3*X+10*d*ca*k^2*X-18*d*κ*k^2*X-5*d*κ^2*D*X+8*d*k^2*D*X-5*d*κ^2*X^2+3*d*ca*κ^2-9*d*κ^3+24*d*ca*k^2-12*d*κ*k^2-8*d*κ^2*D+16*d*k^2*D-4*d*κ^2*X+2*d*k^2*X+10*d*κ^2+8*d*k^2) * ha1 +
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
                                                                                    -8*d*ca^3+23/2*d^3*κ+14*d*ca^2*κ+41/2*d^3*D+6*d*ca^2*D-14*d*κ*D^2+11*d^3*X-13*d*ca^2*X+10*d*ca*κ*X-6*d*k^2*X-8*d*ca*D*X-7*d*D^2*X+3*d*ca*X^2-5*d*D*X^2+35/2*d^3-25*d*ca^2-4*d*ca*κ-6*d*ca*D-8*d*κ*D-13*d*D^2-6*d*ca*X+9*d*κ*X-19*d*D*X+5*d*X^2-21*d*ca+3*d*κ-24*d*D+6*d*X+2*d) * ha2 +
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
                                                                                  -3*d^3*κ*D-2*d*ca^2*κ*D+4*d*κ^3*D-2*d*κ*k^2*D-2*d*ca^2*D^2+4*d*κ^2*D^2+4*d*k^2*D^2+2*d*κ*D^3+8*d*ca^3*X+8*d*ca^2*κ*X-10*d*ca*k^2*X+10*d*κ*k^2*X-16*d*ca^2*D*X+6*d*ca*κ*D*X-8*d^3*ca+26*d*ca^3+4*d^3*κ-2*d*ca^2*κ-6*d*ca*κ^2+12*d*κ^3-24*d*ca*k^2+10*d*κ*k^2+3*d^3*D-14*d*ca^2*D+10*d*ca*κ*D-2*d*ca*D^2+4*d*κ*D^2+16*d*ca^2*X-6*d*ca*κ*X-10*d*ca*D*X+10*d*κ*D*X-22*d^3+32*d*ca^2-20*d*ca*κ-8*d*κ^2-8*d*k^2-16*d*ca*D+2*d*κ*D-4*d*D^2+10*d*ca*X-10*d*κ*X+24*d*ca-10*d*κ+18*d*D+8*d) * hX

/-- `dn(z + K) dn z = k'` where both are finite and `dn z ≠ 0` (from Table 22.4.3). -/
theorem jacobiDnk_add_K_mul {k : ℂ} (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hn : jacobiRegulark .n z k) (hd : jacobiRegulark .d z k) :
    jacobiDnk (z + compEllIntKk k) k * jacobiDnk z k = jacobiComodulusk k := by
  rw [(jacobiDnk_shift hk z).1, mul_assoc]
  have hdn : jacobiDnk z k ≠ 0 := by
    unfold jacobiDnk jacobiPQk jacobiGlaisher
    simp only [reduceCtorEq, ↓reduceIte]
    exact div_ne_zero hd hn
  rw [jacobiNdk, jacobiPQk_eq_one_div, ← jacobiDnk, one_div_mul_cancel hdn, mul_one]

/-- DLMF 22.8.26–22.8.27: if `z₁ - z₂ = z₂ - z₃ = z₃ - z₄ = K/2` then
`dn z₁ dn z₃ = dn z₂ dn z₄ = k'` (at points `z₃`, `z₄` where `dn` is finite and nonzero). -/
@[dlmf 22.8.E26, dlmf 22.8.E27]
theorem jacobiDn_four_point {k : ℂ} (hk : k ∈ jacobiModulusDomain) {z₁ z₂ z₃ z₄ : ℂ}
    (h₁ : z₁ - z₂ = compEllIntKk k / 2) (h₂ : z₂ - z₃ = compEllIntKk k / 2)
    (h₃ : z₃ - z₄ = compEllIntKk k / 2)
    (hn₃ : jacobiRegulark .n z₃ k) (hd₃ : jacobiRegulark .d z₃ k)
    (hn₄ : jacobiRegulark .n z₄ k) (hd₄ : jacobiRegulark .d z₄ k) :
    jacobiDnk z₁ k * jacobiDnk z₃ k = jacobiComodulusk k ∧
      jacobiDnk z₂ k * jacobiDnk z₄ k = jacobiComodulusk k := by
  have e₁ : z₁ = z₃ + compEllIntKk k := by linear_combination h₁ + h₂
  have e₂ : z₂ = z₄ + compEllIntKk k := by linear_combination h₂ + h₃
  exact ⟨e₁ ▸ jacobiDnk_add_K_mul hk hn₃ hd₃, e₂ ▸ jacobiDnk_add_K_mul hk hn₄ hd₄⟩

end DLMF.JacobiElliptic
