/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Theta.Basic.Series

/-!
# Theta functions: lattice quasi-periodicity and half-period translations (DLMF §20.2(ii)–(iii))

The behaviour of the four theta functions under translation of `z` by lattice points
`(m + nτ)π` and by the half-periods `π/2`, `πτ/2`, `π/2 + πτ/2`.

## Main results

* `jacobiThetaOneTau_add_lattice`, …, `jacobiThetaFourTau_add_lattice`: DLMF 20.2.6–20.2.9.
* `jacobiThetaTau_add_two_pi`: all four theta functions have period `2π` (DLMF §20.2(ii)).
* `jacobiThetaOneTau_half_periods`, …, `jacobiThetaFourTau_half_periods`:
  DLMF 20.2.11–20.2.14.

## Implementation notes

Results with `q²`, `iq`, … are stated with `2τ`, `τ + 1/2`, … accordingly.
-/

@[expose] public section

open Complex
open scoped Real

noncomputable section

namespace DLMF.Theta

open DLMF.Elliptic Filter Topology

/-! ### §20.2(ii) Periodicity and quasi-periodicity -/

/-- Lattice quasi-periodicity of `θ₃` in exponential form. -/
private lemma jacobiThetaThreeTau_add_lattice_exp (z τ : ℂ) (m n : ℤ) :
    jacobiThetaThreeTau (z + (m + n * τ) * π) τ =
      cexp (-(π * I * τ * n ^ 2)) * cexp (-2 * I * n * z) * jacobiThetaThreeTau z τ := by
  rw [jacobiThetaThreeTau_eq_tsum, jacobiThetaThreeTau_eq_tsum, ← tsum_mul_left,
    ← (Equiv.subRight n).tsum_eq]
  refine tsum_congr fun k => ?_
  simp only [Equiv.subRight_apply, ← exp_add]
  rw [exp_eq_exp_iff_exists_int]
  exact ⟨k * m - n * m, by push_cast; ring⟩

/-- DLMF 20.2.8: `θ₃(z + (m + nτ)π|τ) = q^{-n²} e^{-2inz} θ₃(z|τ)`. -/
@[dlmf 20.2.E8]
theorem jacobiThetaThreeTau_add_lattice (z τ : ℂ) (m n : ℤ) :
    jacobiThetaThreeTau (z + (m + n * τ) * π) τ =
      cexp (-(π * I * τ * n ^ 2)) * cexp (-2 * I * n * z) * jacobiThetaThreeTau z τ :=
  jacobiThetaThreeTau_add_lattice_exp z τ m n

/-- DLMF 20.2.9: `θ₄(z + (m + nτ)π|τ) = (-1)ⁿ q^{-n²} e^{-2inz} θ₄(z|τ)`. -/
@[dlmf 20.2.E9]
theorem jacobiThetaFourTau_add_lattice (z τ : ℂ) (m n : ℤ) :
    jacobiThetaFourTau (z + (m + n * τ) * π) τ =
      (-1 : ℂ) ^ n * cexp (-(π * I * τ * n ^ 2)) * cexp (-2 * I * n * z) *
        jacobiThetaFourTau z τ := by
  rw [jacobiThetaFourTau, jacobiThetaFourTau, show z + (m + n * τ) * π + π / 2 =
    (z + π / 2) + (m + n * τ) * π by ring, jacobiThetaThreeTau_add_lattice_exp, neg_one_zpow_eq_exp]
  simp only [← exp_add]
  congr 1
  rw [exp_eq_exp_iff_exists_int]
  exact ⟨-n, by push_cast; ring⟩

/-- DLMF 20.2.7: `θ₂(z + (m + nτ)π|τ) = (-1)^m q^{-n²} e^{-2inz} θ₂(z|τ)`. -/
@[dlmf 20.2.E7]
theorem jacobiThetaTwoTau_add_lattice (z τ : ℂ) (m n : ℤ) :
    jacobiThetaTwoTau (z + (m + n * τ) * π) τ =
      (-1 : ℂ) ^ m * cexp (-(π * I * τ * n ^ 2)) * cexp (-2 * I * n * z) *
        jacobiThetaTwoTau z τ := by
  rw [jacobiThetaTwoTau, jacobiThetaTwoTau, show z + (m + n * τ) * π + π * τ / 2 =
    (z + π * τ / 2) + (m + n * τ) * π by ring, jacobiThetaThreeTau_add_lattice_exp,
        neg_one_zpow_eq_exp]
  simp only [← mul_assoc, ← exp_add]
  congr 2
  ring

/-- DLMF 20.2.6: `θ₁(z + (m + nτ)π|τ) = (-1)^{m+n} q^{-n²} e^{-2inz} θ₁(z|τ)`. -/
@[dlmf 20.2.E6]
theorem jacobiThetaOneTau_add_lattice (z τ : ℂ) (m n : ℤ) :
    jacobiThetaOneTau (z + (m + n * τ) * π) τ =
      (-1 : ℂ) ^ (m + n) * cexp (-(π * I * τ * n ^ 2)) * cexp (-2 * I * n * z) *
        jacobiThetaOneTau z τ := by
  rw [jacobiThetaOneTau, jacobiThetaOneTau, show z + (m + n * τ) * π + π / 2 =
    (z + π / 2) + (m + n * τ) * π by ring, jacobiThetaTwoTau_add_lattice, neg_one_zpow_eq_exp,
    neg_one_zpow_eq_exp]
  have : cexp (-2 * I * n * (z + π / 2)) = cexp (π * I * n) * cexp (-2 * I * n * z) := by
    rw [← exp_add, exp_eq_exp_iff_exists_int]; exact ⟨-n, by push_cast; ring⟩
  rw [this]
  have e : cexp (π * I * m) * cexp (-(π * I * τ * n ^ 2)) * (cexp (π * I * n) *
      cexp (-2 * I * n * z)) = cexp (π * I * (m + n : ℤ)) * cexp (-(π * I * τ * n ^ 2)) *
      cexp (-2 * I * n * z) := by
    simp only [← exp_add]; congr 1; push_cast; ring
  rw [← e]; ring

/-- DLMF §20.2(ii): `θ₁` and `θ₂` have period `2π` in `z` (`θ₃`, `θ₄` even have period `π`). -/
@[dlmf 20.2.ii]
theorem jacobiThetaTau_add_two_pi (j : ℕ) (z τ : ℂ) :
    jacobiThetaTau j (z + 2 * π) τ = jacobiThetaTau j z τ := by
  rcases j with _ | _ | _ | _ | _ | j
  · rfl
  · simp only [jacobiThetaTau]
    rw [show z + 2 * π = z + π + π by ring, jacobiThetaOneTau_add_pi, jacobiThetaOneTau_add_pi,
      neg_neg]
  · simp only [jacobiThetaTau]
    rw [show z + 2 * π = z + π + π by ring, jacobiThetaTwoTau_add_pi, jacobiThetaTwoTau_add_pi,
      neg_neg]
  · simp only [jacobiThetaTau]
    rw [show z + 2 * π = z + π + π by ring, jacobiThetaThreeTau_add_pi,
      jacobiThetaThreeTau_add_pi]
  · simp only [jacobiThetaTau]
    rw [show z + 2 * π = z + π + π by ring, jacobiThetaFourTau_add_pi, jacobiThetaFourTau_add_pi]
  · rfl

/-! ### §20.2(iii) Translation of the argument by half-periods -/

/-- DLMF 20.2.11: `θ₁(z|τ) = -θ₂(z + π/2|τ) = -iMθ₄(z + πτ/2|τ) = -iMθ₃(z + π/2 + πτ/2|τ)`. -/
@[dlmf 20.2.E11]
theorem jacobiThetaOneTau_half_periods (z τ : ℂ) :
    jacobiThetaOneTau z τ = -jacobiThetaTwoTau (z + π / 2) τ ∧
    jacobiThetaOneTau z τ = -I * thetaMultiplierM z τ * jacobiThetaFourTau (z + π * τ / 2) τ ∧
    jacobiThetaOneTau z τ =
      -I * thetaMultiplierM z τ * jacobiThetaThreeTau (z + π / 2 + π * τ / 2) τ := by
  have h3 : jacobiThetaOneTau z τ =
      -I * thetaMultiplierM z τ * jacobiThetaThreeTau (z + π / 2 + π * τ / 2) τ := by
    rw [jacobiThetaOneTau, jacobiThetaTwoTau, thetaMultiplierM,
      show z + π / 2 + π * τ / 2 = z + π * τ / 2 + π / 2 by ring]
    have : cexp (π * I * τ / 4 + I * (z + π / 2)) = I * cexp (I * z + π * I * τ / 4) := by
      rw [show π * I * τ / 4 + I * (z + π / 2) = (I * z + π * I * τ / 4) + π / 2 * I by ring,
        exp_add, show (π / 2 : ℂ) * I = (π / 2 : ℂ) * I from rfl, exp_mul_I]
      simp [cos_pi_div_two, sin_pi_div_two]; ring
    rw [this]
    ring_nf
  refine ⟨rfl, ?_, h3⟩
  rw [h3, jacobiThetaFourTau, show z + π * τ / 2 + π / 2 = z + π / 2 + π * τ / 2 by ring]

/-- DLMF 20.2.12: `θ₂(z|τ) = θ₁(z + π/2|τ) = Mθ₃(z + πτ/2|τ) = Mθ₄(z + π/2 + πτ/2|τ)`. -/
@[dlmf 20.2.E12]
theorem jacobiThetaTwoTau_half_periods (z τ : ℂ) :
    jacobiThetaTwoTau z τ = jacobiThetaOneTau (z + π / 2) τ ∧
    jacobiThetaTwoTau z τ = thetaMultiplierM z τ * jacobiThetaThreeTau (z + π * τ / 2) τ ∧
    jacobiThetaTwoTau z τ =
      thetaMultiplierM z τ * jacobiThetaFourTau (z + π / 2 + π * τ / 2) τ := by
  have h2 : jacobiThetaTwoTau z τ =
      thetaMultiplierM z τ * jacobiThetaThreeTau (z + π * τ / 2) τ := by
    rw [jacobiThetaTwoTau, thetaMultiplierM]; congr 2; ring
  refine ⟨?_, h2, ?_⟩
  · rw [jacobiThetaOneTau, show z + π / 2 + π / 2 = z + π by ring, jacobiThetaTwoTau_add_pi,
      neg_neg]
  · rw [h2, jacobiThetaFourTau, show z + π / 2 + π * τ / 2 + π / 2 = z + π * τ / 2 + π by ring,
      jacobiThetaThreeTau_add_pi]

/-- DLMF 20.2.13: `θ₃(z|τ) = θ₄(z + π/2|τ) = Mθ₂(z + πτ/2|τ) = Mθ₁(z + π/2 + πτ/2|τ)`. -/
@[dlmf 20.2.E13]
theorem jacobiThetaThreeTau_half_periods (z τ : ℂ) :
    jacobiThetaThreeTau z τ = jacobiThetaFourTau (z + π / 2) τ ∧
    jacobiThetaThreeTau z τ = thetaMultiplierM z τ * jacobiThetaTwoTau (z + π * τ / 2) τ ∧
    jacobiThetaThreeTau z τ =
      thetaMultiplierM z τ * jacobiThetaOneTau (z + π / 2 + π * τ / 2) τ := by
  have h2 : jacobiThetaThreeTau z τ =
      thetaMultiplierM z τ * jacobiThetaTwoTau (z + π * τ / 2) τ := by
    rw [jacobiThetaTwoTau, thetaMultiplierM, show z + π * τ / 2 + π * τ / 2 =
      z + (((0 : ℤ) : ℂ) + ((1 : ℤ) : ℂ) * τ) * π by
      push_cast; ring, jacobiThetaThreeTau_add_lattice_exp]
    have e : cexp (I * z + π * I * τ / 4) * cexp (π * I * τ / 4 + I * (z + π * τ / 2)) *
        cexp (-(π * I * τ * ((1 : ℤ) : ℂ) ^ 2)) * cexp (-2 * I * ((1 : ℤ) : ℂ) * z) = 1 := by
      simp only [← exp_add]; rw [← exp_zero]; congr 1; push_cast; ring
    linear_combination (-jacobiThetaThreeTau z τ) * e
  refine ⟨?_, h2, ?_⟩
  · rw [jacobiThetaFourTau, show z + π / 2 + π / 2 = z + π by ring, jacobiThetaThreeTau_add_pi]
  · rw [h2, jacobiThetaOneTau, show z + π / 2 + π * τ / 2 + π / 2 = z + π * τ / 2 + π by ring,
      jacobiThetaTwoTau_add_pi, neg_neg]

/-- DLMF 20.2.14: `θ₄(z|τ) = θ₃(z + π/2|τ) = -iMθ₁(z + πτ/2|τ) = iMθ₂(z + π/2 + πτ/2|τ)`. -/
@[dlmf 20.2.E14]
theorem jacobiThetaFourTau_half_periods (z τ : ℂ) :
    jacobiThetaFourTau z τ = jacobiThetaThreeTau (z + π / 2) τ ∧
    jacobiThetaFourTau z τ = -I * thetaMultiplierM z τ * jacobiThetaOneTau (z + π * τ / 2) τ ∧
    jacobiThetaFourTau z τ =
      I * thetaMultiplierM z τ * jacobiThetaTwoTau (z + π / 2 + π * τ / 2) τ := by
  have h2 : jacobiThetaFourTau z τ =
      I * thetaMultiplierM z τ * jacobiThetaTwoTau (z + π / 2 + π * τ / 2) τ := by
    have h := (jacobiThetaThreeTau_half_periods (z + π / 2) τ).2.1
    rw [jacobiThetaFourTau, h, thetaMultiplierM, thetaMultiplierM,
      show z + π / 2 + π * τ / 2 = z + π * τ / 2 + π / 2 by ring]
    have : cexp (I * (z + π / 2) + π * I * τ / 4) = I * cexp (I * z + π * I * τ / 4) := by
      rw [show I * (z + π / 2) + π * I * τ / 4 = (I * z + π * I * τ / 4) + π / 2 * I by ring,
        exp_add, exp_mul_I]
      simp [cos_pi_div_two, sin_pi_div_two]; ring
    rw [this]
  refine ⟨rfl, ?_, h2⟩
  rw [h2, jacobiThetaOneTau, show z + π * τ / 2 + π / 2 = z + π / 2 + π * τ / 2 by ring]
  ring_nf

end DLMF.Theta

end
