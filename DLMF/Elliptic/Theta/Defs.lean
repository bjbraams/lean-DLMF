/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable

/-!
# Jacobi theta functions in the DLMF argument convention

The four theta functions are defined using Mathlib's two-variable theta series, with
period `π` in the argument and nome `q = exp (π * I * τ)`.
-/

@[expose] public section

open Complex
open scoped Real

noncomputable section

namespace DLMF.Elliptic

/-- `θ₃(z|τ) = ∑ₙ q^{n²} e^{2inz}`, `q = e^{iπτ}` (DLMF 20.2.3), via Mathlib's `jacobiTheta₂`. -/
def jacobiThetaThreeTau (z τ : ℂ) : ℂ := jacobiTheta₂ (z / π) τ

/-- `θ₄(z|τ) = θ₃(z + π/2|τ) = ∑ₙ (-1)ⁿ q^{n²} e^{2inz}` (DLMF 20.2.4). -/
@[dlmf 20.2.E14 "first equality, used as the definition of θ₄"]
def jacobiThetaFourTau (z τ : ℂ) : ℂ := jacobiThetaThreeTau (z + π / 2) τ

/-- `θ₂(z|τ) = q^{1/4} e^{iz} θ₃(z + πτ/2|τ) = ∑ₙ q^{(n+1/2)²} e^{(2n+1)iz}` (DLMF 20.2.2). -/
@[dlmf 20.2.E12 "second equality M θ₃(z + πτ/2|τ), used as the definition of θ₂"]
def jacobiThetaTwoTau (z τ : ℂ) : ℂ := cexp (π * I * τ / 4 + I * z) *
    jacobiThetaThreeTau (z + π * τ / 2) τ

/-- `θ₁(z|τ) = -θ₂(z + π/2|τ)` (DLMF §20.2). -/
@[dlmf 20.2.E11 "first equality, used as the definition of θ₁"]
def jacobiThetaOneTau (z τ : ℂ) : ℂ := -jacobiThetaTwoTau (z + π / 2) τ

/-- `(π : ℂ) ≠ 0`. -/
theorem pi_ne_zero' : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero

/-- The series for `θ₃` (DLMF 20.2.3). -/
@[dlmf 20.2.E3]
theorem jacobiThetaThreeTau_eq_tsum (z τ : ℂ) :
    jacobiThetaThreeTau z τ = ∑' n : ℤ, cexp (π * I * n ^ 2 * τ + 2 * I * n * z) := by
  rw [jacobiThetaThreeTau, jacobiTheta₂]
  refine tsum_congr fun n => ?_
  rw [jacobiTheta₂_term]
  congr 1
  field_simp [pi_ne_zero']
  ring

end DLMF.Elliptic
