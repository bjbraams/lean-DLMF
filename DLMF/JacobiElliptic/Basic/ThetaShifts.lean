/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.JacobiElliptic.Basic.Definitions
public import DLMF.Elliptic.Basic.ThetaPeriodicity

/-!
# Theta functions under quarter-period shifts; the nome (DLMF §§20.2, 22.2)

The behaviour of the theta functions `θⱼ(ζ|τ)` under the shifts `ζ ↦ ζ + π/2` and
`ζ ↦ ζ + πτ/2` of the theta argument, which correspond to the quarter periods `K` and `iK'` of
the Jacobian elliptic functions, and the nome `q = e^{iπτ}` of the modulus `k`.

## Main definitions

* `jacobiThetaShiftFactor`: the multiplier `e^{-iπτ/4 - iζ}` of the shift `ζ ↦ ζ + πτ/2`.

## Main results

* `jacobiThetaOneTau_add_pi_div_two`, …, `jacobiThetaFourTau_add_pi_div_two`: the shift
  `ζ ↦ ζ + π/2`.
* `jacobiThetaOneTau_add_pi_mul_div_two`, …, `jacobiThetaFourTau_add_pi_mul_div_two`: the shift
  `ζ ↦ ζ + πτ/2`.
* `jacobiNome_eq_exp_tau`: `q = e^{iπτ}` with `τ = iK'/K` (DLMF 22.2.1, 22.2.12).
-/

@[expose] public section

open Complex DLMF.Elliptic

open scoped Real

noncomputable section

namespace DLMF.JacobiElliptic

/-- `θ₁(ζ + π/2) = θ₂(ζ)`. -/
theorem jacobiThetaOneTau_add_pi_div_two (ζ τ : ℂ) :
    jacobiThetaOneTau (ζ + π / 2) τ = jacobiThetaTwoTau ζ τ := by
  rw [jacobiThetaOneTau, show ζ + π / 2 + π / 2 = ζ + π by ring, jacobiThetaTwoTau_add_pi, neg_neg]

/-- `θ₂(ζ + π/2) = -θ₁(ζ)`. -/
theorem jacobiThetaTwoTau_add_pi_div_two (ζ τ : ℂ) :
    jacobiThetaTwoTau (ζ + π / 2) τ = -jacobiThetaOneTau ζ τ := by
  rw [jacobiThetaOneTau, neg_neg]

/-- `θ₃(ζ + π/2) = θ₄(ζ)`. -/
theorem jacobiThetaThreeTau_add_pi_div_two (ζ τ : ℂ) :
    jacobiThetaThreeTau (ζ + π / 2) τ = jacobiThetaFourTau ζ τ := rfl

/-- `θ₄(ζ + π/2) = θ₃(ζ)`. -/
theorem jacobiThetaFourTau_add_pi_div_two (ζ τ : ℂ) :
    jacobiThetaFourTau (ζ + π / 2) τ = jacobiThetaThreeTau ζ τ := by
  rw [jacobiThetaFourTau, show ζ + π / 2 + π / 2 = ζ + π by ring, jacobiThetaThreeTau_add_pi]

/-- The multiplier `e^{-iπτ/4 - iζ}` of the half-period shift `ζ ↦ ζ + πτ/2`. -/
def jacobiThetaShiftFactor (ζ τ : ℂ) : ℂ := cexp (-(π * I * τ / 4 + I * ζ))

/-- Nonvanishing under the stated hypotheses: `jacobiThetaShiftFactor ζ τ ≠ 0`. -/
theorem jacobiThetaShiftFactor_ne_zero (ζ τ : ℂ) : jacobiThetaShiftFactor ζ τ ≠ 0 :=
    Complex.exp_ne_zero _

/-- `θ₃(ζ + πτ/2) = e^{-iπτ/4-iζ} θ₂(ζ)`. -/
theorem jacobiThetaThreeTau_add_pi_mul_div_two (ζ τ : ℂ) :
    jacobiThetaThreeTau (ζ + π * τ / 2) τ = jacobiThetaShiftFactor ζ τ * jacobiThetaTwoTau ζ τ := by
  rw [jacobiThetaTwoTau, jacobiThetaShiftFactor, ← mul_assoc, ← exp_add, neg_add_cancel, exp_zero,
    one_mul]

/-- `θ₂(ζ + πτ/2) = e^{-iπτ/4-iζ} θ₃(ζ)`. -/
theorem jacobiThetaTwoTau_add_pi_mul_div_two (ζ τ : ℂ) :
    jacobiThetaTwoTau (ζ + π * τ / 2) τ = jacobiThetaShiftFactor ζ τ * jacobiThetaThreeTau ζ τ := by
  rw [jacobiThetaTwoTau, show ζ + π * τ / 2 + π * τ / 2 = ζ + π * τ by ring,
    jacobiThetaThreeTau_add_pi_mul, jacobiThetaShiftFactor, ← mul_assoc, ← exp_add]
  congr 2
  ring

/-- Identity under the stated parameter and domain assumptions: `cexp (-(π / 2 * I)) = -I`. -/
private lemma exp_neg_pi_div_two_mul_I_eq_neg_I : cexp (-(π / 2 * I)) = -I := by
  rw [Complex.exp_neg, Complex.exp_pi_div_two_mul_I, inv_I]

/-- `θ₁(ζ + πτ/2) = i e^{-iπτ/4-iζ} θ₄(ζ)`. -/
theorem jacobiThetaOneTau_add_pi_mul_div_two (ζ τ : ℂ) :
    jacobiThetaOneTau (ζ + π * τ / 2) τ =
      I * jacobiThetaShiftFactor ζ τ * jacobiThetaFourTau ζ τ := by
  rw [jacobiThetaOneTau, jacobiThetaTwoTau, show ζ + π * τ / 2 + π / 2 + π * τ / 2 =
    (ζ + π / 2) + π * τ by ring, jacobiThetaThreeTau_add_pi_mul, jacobiThetaShiftFactor,
    ← jacobiThetaFourTau, ← mul_assoc, ← exp_add]
  have h : π * I * τ / 4 + I * (ζ + π * τ / 2 + π / 2) + (-(π * I * τ) - 2 * I * (ζ + π / 2)) =
      -(π * I * τ / 4 + I * ζ) + (-(π / 2 * I)) := by ring
  rw [h, exp_add, exp_neg_pi_div_two_mul_I_eq_neg_I]
  ring

/-- `θ₄(ζ + πτ/2) = i e^{-iπτ/4-iζ} θ₁(ζ)`. -/
theorem jacobiThetaFourTau_add_pi_mul_div_two (ζ τ : ℂ) :
    jacobiThetaFourTau (ζ + π * τ / 2) τ =
      I * jacobiThetaShiftFactor ζ τ * jacobiThetaOneTau ζ τ := by
  rw [jacobiThetaFourTau, show ζ + π * τ / 2 + π / 2 = (ζ + π / 2) + π * τ / 2 by ring,
    jacobiThetaThreeTau_add_pi_mul_div_two, jacobiThetaTwoTau_add_pi_div_two,
        jacobiThetaShiftFactor,
    jacobiThetaShiftFactor, show -(π * I * τ / 4 + I * (ζ + π / 2)) =
      -(π * I * τ / 4 + I * ζ) + (-(π / 2 * I)) by ring, exp_add, exp_neg_pi_div_two_mul_I_eq_neg_I]
  ring

/-- The nome is `q = e^{iπτ}` with `τ = iK'/K` (DLMF 22.2.1 and 22.2.12). -/
@[dlmf 22.2.E1]
theorem jacobiNome_eq_exp_tau (k : ℂ) : jacobiNome k = cexp (π * I * jacobiTau k) := by
  rw [jacobiNome, jacobiTau]
  congr 1
  rw [mul_div_assoc', ← mul_assoc, mul_assoc (π : ℂ) I I, I_mul_I]
  ring

end DLMF.JacobiElliptic

end
end
