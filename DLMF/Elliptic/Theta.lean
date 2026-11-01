/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Elliptic.Basic.ThetaPeriodicity

/-!
# Jacobi's imaginary transformation of `θ₃(0|τ)`

Jacobi's imaginary transformation of the theta constant `θ₃(0|τ)`, from Mathlib's functional
equation for `jacobiTheta₂` (Temme §12.3.2, DLMF §20.7(viii)). The series, periodicity and
parity of `θ₁, …, θ₄` are in `DLMF.Elliptic.Basic.ThetaPeriodicity`.

## Main results

* `jacobiThetaThreeTau_zero_neg_recip`: `θ₃(0|-1/τ) = (-iτ)^{1/2} θ₃(0|τ)` (DLMF 20.7.32 at
  `z = 0`).
-/

@[expose] public section

open Complex
open scoped Real

noncomputable section

namespace DLMF.Elliptic

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
