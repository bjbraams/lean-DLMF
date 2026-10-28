/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.JacobiElliptic.PeriodsPolesZeros

/-!
# Theta products and Jacobi addition formulas

Mixed theta products give addition formulas for the twelve Jacobian elliptic quotients.

Source references and common attribution are retained in
`DLMF.JacobiElliptic.Addition`.
-/

@[expose] public section

open Complex DLMF.Elliptic

open scoped Real

noncomputable section

namespace DLMF.JacobiElliptic

/-- Identity under the stated parameter and domain assumptions: `jacobiThetaOneTau (x - π / 2) τ =
-jacobiThetaTwoTau x τ`. -/
lemma p22R1_one_sub_half (x τ : ℂ) :
    jacobiThetaOneTau (x - π / 2) τ = -jacobiThetaTwoTau x τ := by
  rw [jacobiThetaOneTau, sub_add_cancel]

/-- Identity under the stated parameter and domain assumptions: `jacobiThetaThreeTau (x - π / 2) τ
= jacobiThetaFourTau x τ`. -/
lemma p22R1_three_sub_half (x τ : ℂ) :
    jacobiThetaThreeTau (x - π / 2) τ = jacobiThetaFourTau x τ := by
  rw [jacobiThetaFourTau, show x + π / 2 = (x - π / 2) + π by ring, jacobiThetaThreeTau_add_pi]

/-- Identity under the stated parameter and domain assumptions: `jacobiThetaTwoTau (x - π / 2) τ =
jacobiThetaOneTau x τ`. -/
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

/-- Identity under the stated parameter and domain assumptions: `jacobiThetaThreeTau z τ *
jacobiThetaFourTau w τ = jacobiThetaFourTau (z + w) (2 * τ) * jacobiThetaFourTau (z - w) (2 *
τ) - jacobiThetaOneTau (z + w) (2 * τ) * jacobiThetaOneTau (z - w) (2 * τ)`. -/
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

/-- Identity under the stated parameter and domain assumptions: `jacobiZetak (u + v) k =
jacobiZetak u k + jacobiZetak v k`. -/
lemma p22R1_zetak_add (u v k : ℂ) : jacobiZetak (u + v) k = jacobiZetak u k + jacobiZetak v k := by
  simp only [jacobiZetak]; ring

/-- Nonvanishing under the stated hypotheses: `jacobiThetaFourTau (jacobiZetak z k) (jacobiTauk k)
≠ 0`. -/
lemma p22R1_four_ne {z k : ℂ} (h : jacobiRegulark .n z k) :
    jacobiThetaFourTau (jacobiZetak z k) (jacobiTauk k) ≠ 0 := by
  intro h'; apply h; simp [jacobiLetterTheta, h']

local notation "θ₁" => jacobiThetaOneTau
local notation "θ₂" => jacobiThetaTwoTau
local notation "θ₃" => jacobiThetaThreeTau
local notation "θ₄" => jacobiThetaFourTau

/-- Identity under the stated parameter and domain assumptions: `θ₄ (x - π / 2) τ = θ₃ x τ`. -/
lemma p22R1_four_sub_half (x τ : ℂ) : θ₄ (x - π / 2) τ = θ₃ x τ := by
  rw [jacobiThetaFourTau, sub_add_cancel]

/-- Identity under the stated parameter and domain assumptions: `θ₂ 0 τ * θ₃ 0 τ * (θ₂ (x + y) τ *
θ₃ (x - y) τ) = θ₂ x τ * θ₃ x τ * (θ₂ y τ * θ₃ y τ) - θ₁ x τ * θ₄ x τ * (θ₁ y τ * θ₄ y τ)`. -/
theorem p22R1_P23 (x y τ : ℂ) (hτ : 0 < τ.im) :
    θ₂ 0 τ * θ₃ 0 τ * (θ₂ (x + y) τ * θ₃ (x - y) τ) =
      θ₂ x τ * θ₃ x τ * (θ₂ y τ * θ₃ y τ) - θ₁ x τ * θ₄ x τ * (θ₁ y τ * θ₄ y τ) := by
  have h := p22R1_mixed14 x (y + π / 2) τ hτ
  rw [show x + (y + π / 2) = (x + y) + π / 2 by ring,
    show x - (y + π / 2) = (x - y) - π / 2 by ring,
    je22a_thetaOne_add_half_pi, p22R1_four_sub_half, je22a_thetaOne_add_half_pi,
    je22a_thetaTwo_add_half_pi, je22a_thetaThree_add_half_pi, je22a_thetaFour_add_half_pi] at h
  linear_combination h

/-- Identity under the stated parameter and domain assumptions: `θ₂ 0 τ * θ₃ 0 τ * (θ₃ (x + y) τ *
θ₂ (x - y) τ) = θ₂ x τ * θ₃ x τ * (θ₂ y τ * θ₃ y τ) + θ₁ x τ * θ₄ x τ * (θ₁ y τ * θ₄ y τ)`. -/
lemma p22R1_P32 (x y τ : ℂ) (hτ : 0 < τ.im) :
    θ₂ 0 τ * θ₃ 0 τ * (θ₃ (x + y) τ * θ₂ (x - y) τ) =
      θ₂ x τ * θ₃ x τ * (θ₂ y τ * θ₃ y τ) + θ₁ x τ * θ₄ x τ * (θ₁ y τ * θ₄ y τ) := by
  have h := p22R1_P23 x (-y) τ hτ
  rw [← sub_eq_add_neg, sub_neg_eq_add, jacobiThetaOneTau_neg, jacobiThetaTwoTau_neg,
    jacobiThetaThreeTau_neg, jacobiThetaFourTau_neg] at h
  linear_combination h

/-- Identity under the stated parameter and domain assumptions: `θ₂ 0 τ * θ₃ 0 τ * (θ₄ (x + y) τ *
θ₁ (x - y) τ) = θ₁ x τ * θ₄ x τ * (θ₂ y τ * θ₃ y τ) - θ₂ x τ * θ₃ x τ * (θ₁ y τ * θ₄ y τ)`. -/
lemma p22R1_P41 (x y τ : ℂ) (hτ : 0 < τ.im) :
    θ₂ 0 τ * θ₃ 0 τ * (θ₄ (x + y) τ * θ₁ (x - y) τ) =
      θ₁ x τ * θ₄ x τ * (θ₂ y τ * θ₃ y τ) - θ₂ x τ * θ₃ x τ * (θ₁ y τ * θ₄ y τ) := by
  have h := p22R1_mixed14 x (-y) τ hτ
  rw [← sub_eq_add_neg, sub_neg_eq_add, jacobiThetaOneTau_neg, jacobiThetaTwoTau_neg,
    jacobiThetaThreeTau_neg, jacobiThetaFourTau_neg] at h
  linear_combination h

/-- Identity under the stated parameter and domain assumptions: `θ₂ 0 τ * θ₄ 0 τ * (θ₄ (x + y) τ *
θ₂ (x - y) τ) = θ₂ x τ * θ₄ x τ * (θ₂ y τ * θ₄ y τ) + θ₁ x τ * θ₃ x τ * (θ₁ y τ * θ₃ y τ)`. -/
lemma p22R1_P42 (x y τ : ℂ) (hτ : 0 < τ.im) :
    θ₂ 0 τ * θ₄ 0 τ * (θ₄ (x + y) τ * θ₂ (x - y) τ) =
      θ₂ x τ * θ₄ x τ * (θ₂ y τ * θ₄ y τ) + θ₁ x τ * θ₃ x τ * (θ₁ y τ * θ₃ y τ) := by
  have h := p22R1_mixed24 x (-y) τ hτ
  rw [← sub_eq_add_neg, sub_neg_eq_add, jacobiThetaOneTau_neg, jacobiThetaTwoTau_neg,
    jacobiThetaThreeTau_neg, jacobiThetaFourTau_neg] at h
  linear_combination h

/-- Identity under the stated parameter and domain assumptions: `θ₂ 0 τ * θ₄ 0 τ * (θ₁ (x + y) τ *
θ₃ (x - y) τ) = θ₂ x τ * θ₄ x τ * (θ₁ y τ * θ₃ y τ) + θ₁ x τ * θ₃ x τ * (θ₂ y τ * θ₄ y τ)`. -/
theorem p22R1_P13 (x y τ : ℂ) (hτ : 0 < τ.im) :
    θ₂ 0 τ * θ₄ 0 τ * (θ₁ (x + y) τ * θ₃ (x - y) τ) =
      θ₂ x τ * θ₄ x τ * (θ₁ y τ * θ₃ y τ) + θ₁ x τ * θ₃ x τ * (θ₂ y τ * θ₄ y τ) := by
  have h := p22R1_mixed24 x (y + π / 2) τ hτ
  rw [show x + (y + π / 2) = (x + y) + π / 2 by ring,
    show x - (y + π / 2) = (x - y) - π / 2 by ring,
    je22a_thetaTwo_add_half_pi, p22R1_four_sub_half, je22a_thetaOne_add_half_pi,
    je22a_thetaTwo_add_half_pi, je22a_thetaThree_add_half_pi, je22a_thetaFour_add_half_pi] at h
  linear_combination -h

/-- Identity under the stated parameter and domain assumptions: `θ₂ 0 τ * θ₄ 0 τ * (θ₃ (x + y) τ *
θ₁ (x - y) τ) = θ₁ x τ * θ₃ x τ * (θ₂ y τ * θ₄ y τ) - θ₂ x τ * θ₄ x τ * (θ₁ y τ * θ₃ y τ)`. -/
lemma p22R1_P31 (x y τ : ℂ) (hτ : 0 < τ.im) :
    θ₂ 0 τ * θ₄ 0 τ * (θ₃ (x + y) τ * θ₁ (x - y) τ) =
      θ₁ x τ * θ₃ x τ * (θ₂ y τ * θ₄ y τ) - θ₂ x τ * θ₄ x τ * (θ₁ y τ * θ₃ y τ) := by
  have h := p22R1_P13 x (-y) τ hτ
  rw [← sub_eq_add_neg, sub_neg_eq_add, jacobiThetaOneTau_neg, jacobiThetaTwoTau_neg,
    jacobiThetaThreeTau_neg, jacobiThetaFourTau_neg] at h
  linear_combination h

/-- Identity under the stated parameter and domain assumptions: `θ₃ 0 τ * θ₄ 0 τ * (θ₄ (x + y) τ *
θ₃ (x - y) τ) = θ₃ x τ * θ₄ x τ * (θ₃ y τ * θ₄ y τ) + θ₁ x τ * θ₂ x τ * (θ₁ y τ * θ₂ y τ)`. -/
lemma p22R1_P43 (x y τ : ℂ) (hτ : 0 < τ.im) :
    θ₃ 0 τ * θ₄ 0 τ * (θ₄ (x + y) τ * θ₃ (x - y) τ) =
      θ₃ x τ * θ₄ x τ * (θ₃ y τ * θ₄ y τ) + θ₁ x τ * θ₂ x τ * (θ₁ y τ * θ₂ y τ) := by
  have h := p22R1_mixed34 x (-y) τ hτ
  rw [← sub_eq_add_neg, sub_neg_eq_add, jacobiThetaOneTau_neg, jacobiThetaTwoTau_neg,
    jacobiThetaThreeTau_neg, jacobiThetaFourTau_neg] at h
  linear_combination h

/-- Identity under the stated parameter and domain assumptions: `je22a_shiftFactor (x + y) τ *
je22a_shiftFactor (x - y) τ = je22a_shiftFactor x τ ^ 2`. -/
lemma p22R1_shiftFactor_mul (x y τ : ℂ) :
    je22a_shiftFactor (x + y) τ * je22a_shiftFactor (x - y) τ = je22a_shiftFactor x τ ^ 2 := by
  simp only [je22a_shiftFactor, sq, ← exp_add]; congr 1; ring

/-- Identity under the stated parameter and domain assumptions: `θ₃ 0 τ * θ₄ 0 τ * (θ₂ (x + y) τ *
θ₁ (x - y) τ) = θ₁ x τ * θ₂ x τ * (θ₃ y τ * θ₄ y τ) - θ₃ x τ * θ₄ x τ * (θ₁ y τ * θ₂ y τ)`. -/
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

/-- Identity under the stated parameter and domain assumptions: `θ₃ 0 τ * θ₄ 0 τ * (θ₁ (x + y) τ *
θ₂ (x - y) τ) = θ₁ x τ * θ₂ x τ * (θ₃ y τ * θ₄ y τ) + θ₃ x τ * θ₄ x τ * (θ₁ y τ * θ₂ y τ)`. -/
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

/-- Identity under the stated parameter and domain assumptions: `θ₂ 0 τ ≠ 0 ∧ θ₃ 0 τ ≠ 0 ∧ θ₄ 0 τ
≠ 0 ∧ θ₃ 0 τ ^ 4 = θ₂ 0 τ ^ 4 + θ₄ 0 τ ^ 4`. -/
theorem p22R1_nulls :
    θ₂ 0 τ ≠ 0 ∧ θ₃ 0 τ ≠ 0 ∧ θ₄ 0 τ ≠ 0 ∧ θ₃ 0 τ ^ 4 = θ₂ 0 τ ^ 4 + θ₄ 0 τ ^ 4 := by
  have j := DLMF.Theta.jacobiThetaNull_fourth_power τ hτ
  simp only [DLMF.Theta.jacobiThetaTwoNullTau, DLMF.Theta.jacobiThetaThreeNullTau,
    DLMF.Theta.jacobiThetaFourNullTau] at j
  exact ⟨je22a_thetaTwo_zero_ne_zero hτ, je22a_thetaThree_zero_ne_zero hτ,
    je22a_thetaFour_zero_ne_zero hτ, j⟩

/-- Identity under the stated parameter and domain assumptions: `θ₃ 0 τ ^ 2 * (θ₃ (x + y) τ * θ₃
(x - y) τ) = θ₃ x τ ^ 2 * θ₃ y τ ^ 2 + θ₁ x τ ^ 2 * θ₁ y τ ^ 2`. -/
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

/-- Identity under the stated parameter and domain assumptions: `θ₂ 0 τ ^ 2 * (θ₂ (x + y) τ * θ₂
(x - y) τ) = θ₂ x τ ^ 2 * θ₂ y τ ^ 2 - θ₁ x τ ^ 2 * θ₁ y τ ^ 2`. -/
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

/-- Identity under the stated parameter and domain assumptions: `θ₂ 0 τ ^ 2 * (θ₁ (x + y) τ * θ₁
(x - y) τ) = θ₁ x τ ^ 2 * θ₂ y τ ^ 2 - θ₂ x τ ^ 2 * θ₁ y τ ^ 2`. -/
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

/-- Identity under the stated parameter and domain assumptions: `θ₄ 0 τ ^ 2 * (θ₁ (x + y) τ * θ₁
(x - y) τ) = θ₁ x τ ^ 2 * θ₄ y τ ^ 2 - θ₄ x τ ^ 2 * θ₁ y τ ^ 2`. -/
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

/-- Identity under the stated parameter and domain assumptions: `θ₄ 0 τ ^ 4 * (θ₂ (x + y) τ * θ₂
(x - y) τ) = θ₂ 0 τ ^ 2 * (θ₄ x τ ^ 2 * θ₄ y τ ^ 2) - θ₃ 0 τ ^ 2 * (θ₁ x τ ^ 2 * θ₄ y τ ^ 2 +
θ₄ x τ ^ 2 * θ₁ y τ ^ 2) + θ₂ 0 τ ^ 2 * (θ₁ x τ ^ 2 * θ₁ y τ ^ 2)`. -/
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

end DLMF.JacobiElliptic
end
end
