/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Elliptic.Basic.Theta

/-!
# Jacobi's theta functions in DLMF normalization (Temme §12.3.2, DLMF §20.2)

Mathlib's `jacobiTheta₂ z τ = ∑ₙ exp(2πinz + πin²τ)` is `θ₃(πz|τ)`. We define `θ₁, …, θ₄` with
the DLMF argument convention (`q = e^{iπτ}`, period `π` in `z`) and derive their series,
periodicity, parity and the quasi-periodicity of `θ₃`, together with Jacobi's imaginary
transformation of `θ₃(0|τ)`, from Mathlib's results for `jacobiTheta₂`.
-/

@[expose] public section

open Complex
open scoped Real

noncomputable section

namespace DLMF.Elliptic

/-- The series for `θ₄` (DLMF 20.2.4). -/
@[dlmf 20.2.E4]
theorem jacobiThetaFourTau_eq_tsum (z τ : ℂ) :
    jacobiThetaFourTau z τ = ∑' n : ℤ, (-1 : ℂ) ^ n * cexp (π * I * n ^ 2 * τ + 2 * I * n * z) := by
  rw [jacobiThetaFourTau, jacobiThetaThreeTau_eq_tsum]
  refine tsum_congr fun n => ?_
  rw [← exp_pi_mul_I, ← exp_int_mul, ← exp_add]
  congr 1
  ring

/-- `θ₃(z + π|τ) = θ₃(z|τ)`. -/
@[dlmf 20.2.E8 "special case m = 1, n = 0"]
theorem jacobiThetaThreeTau_add_pi (z τ : ℂ) :
    jacobiThetaThreeTau (z + π) τ = jacobiThetaThreeTau z τ := by
  rw [jacobiThetaThreeTau, jacobiThetaThreeTau, add_div, div_self pi_ne_zero',
      jacobiTheta₂_add_left]

/-- `θ₃` is even. -/
@[dlmf 20.2.ii]
theorem jacobiThetaThreeTau_neg (z τ : ℂ) :
    jacobiThetaThreeTau (-z) τ = jacobiThetaThreeTau z τ := by
  rw [jacobiThetaThreeTau, jacobiThetaThreeTau, neg_div, jacobiTheta₂_neg_left]

/-- Quasi-periodicity `θ₃(z + πτ|τ) = q⁻¹ e^{-2iz} θ₃(z|τ)` (Temme §12.3.2). -/
@[dlmf 20.2.E8 "special case m = 0, n = 1"]
theorem jacobiThetaThreeTau_add_pi_mul (z τ : ℂ) :
    jacobiThetaThreeTau (z + π * τ) τ =
      cexp (-(π * I * τ) - 2 * I * z) * jacobiThetaThreeTau z τ := by
  rw [jacobiThetaThreeTau, jacobiThetaThreeTau, add_div, mul_div_cancel_left₀ _ pi_ne_zero',
    jacobiTheta₂_add_left']
  congr 2
  field_simp [pi_ne_zero']
  ring

/-- `θ₃(z - πτ|τ) = q⁻¹ e^{2iz} θ₃(z|τ)`. -/
theorem jacobiThetaThreeTau_sub_pi_mul (z τ : ℂ) :
    jacobiThetaThreeTau (z - π * τ) τ =
      cexp (-(π * I * τ) + 2 * I * z) * jacobiThetaThreeTau z τ := by
  have h := jacobiThetaThreeTau_add_pi_mul (z - π * τ) τ
  rw [sub_add_cancel] at h
  rw [h, ← mul_assoc, ← exp_add]
  ring_nf
  rw [exp_zero, one_mul]

/-- `θ₄(z + π|τ) = θ₄(z|τ)`. -/
theorem jacobiThetaFourTau_add_pi (z τ : ℂ) :
    jacobiThetaFourTau (z + π) τ = jacobiThetaFourTau z τ := by
  rw [jacobiThetaFourTau, jacobiThetaFourTau, show z + π + π / 2 = z + π / 2 + π by ring,
      jacobiThetaThreeTau_add_pi]

/-- `θ₄` is even. -/
@[dlmf 20.2.ii]
theorem jacobiThetaFourTau_neg (z τ : ℂ) : jacobiThetaFourTau (-z) τ = jacobiThetaFourTau z τ := by
  rw [jacobiThetaFourTau, jacobiThetaFourTau, ← jacobiThetaThreeTau_neg,
    show -(-z + π / 2) = z - π / 2 by ring, ← jacobiThetaThreeTau_add_pi (z - π / 2)]
  ring_nf

/-- `θ₂(z + π|τ) = -θ₂(z|τ)`. -/
theorem jacobiThetaTwoTau_add_pi (z τ : ℂ) :
    jacobiThetaTwoTau (z + π) τ = -jacobiThetaTwoTau z τ := by
  rw [jacobiThetaTwoTau, jacobiThetaTwoTau, show z + π + π * τ / 2 = z + π * τ / 2 + π by ring,
      jacobiThetaThreeTau_add_pi,
    show π * I * τ / 4 + I * (z + π) = (π * I * τ / 4 + I * z) + π * I by ring, exp_add,
    exp_pi_mul_I]
  ring

/-- `θ₂` is even. -/
@[dlmf 20.2.ii]
theorem jacobiThetaTwoTau_neg (z τ : ℂ) : jacobiThetaTwoTau (-z) τ = jacobiThetaTwoTau z τ := by
  rw [jacobiThetaTwoTau, jacobiThetaTwoTau, ← jacobiThetaThreeTau_neg (-z + π * τ / 2),
    show -(-z + π * τ / 2) = (z + π * τ / 2) - π * τ by ring, jacobiThetaThreeTau_sub_pi_mul,
    ← mul_assoc, ← exp_add]
  congr 2
  ring

/-- `θ₁(z + π|τ) = -θ₁(z|τ)`. -/
theorem jacobiThetaOneTau_add_pi (z τ : ℂ) :
    jacobiThetaOneTau (z + π) τ = -jacobiThetaOneTau z τ := by
  rw [jacobiThetaOneTau, jacobiThetaOneTau, show z + π + π / 2 = z + π / 2 + π by ring,
      jacobiThetaTwoTau_add_pi]

/-- `θ₁` is odd. -/
@[dlmf 20.2.ii]
theorem jacobiThetaOneTau_neg (z τ : ℂ) : jacobiThetaOneTau (-z) τ = -jacobiThetaOneTau z τ := by
  rw [jacobiThetaOneTau, jacobiThetaOneTau, ← jacobiThetaTwoTau_neg,
    show -(-z + π / 2) = (z - π / 2) by ring, show z + π / 2 = (z - π / 2) + π by ring,
    jacobiThetaTwoTau_add_pi, neg_neg]

/-- Jacobi's imaginary transformation at `z = 0`: `θ₃(0|-1/τ) = (-iτ)^{1/2} θ₃(0|τ)`. -/
@[dlmf 20.7.E32 "special case z = 0"]
theorem jacobiThetaThreeTau_zero_neg_recip {τ : ℂ} (hτ : τ ≠ 0) :
    jacobiThetaThreeTau 0 (-1 / τ) = (-I * τ) ^ (1 / 2 : ℂ) * jacobiThetaThreeTau 0 τ := by
  have h := jacobiTheta₂_functional_equation 0 τ
  simp only [zero_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    exp_zero, mul_one] at h
  have hne : (-I * τ) ^ (1 / 2 : ℂ) ≠ 0 :=
    cpow_ne_zero_iff.mpr (Or.inl (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hτ))
  rw [jacobiThetaThreeTau, jacobiThetaThreeTau, zero_div, h]
  field_simp

end DLMF.Elliptic
