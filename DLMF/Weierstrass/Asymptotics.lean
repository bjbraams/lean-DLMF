/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Weierstrass.Basic
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.NumberTheory.ModularForms.Basic

/-!
# Asymptotic approximations as `q → 0` (DLMF §23.12)

DLMF lets `q = e^{πiω₃/ω₁} → 0` with `ω₁` and `z` fixed. Here `ω₃ = ω₁τ` and `τ` tends to
`i∞` in the upper half-plane (`UpperHalfPlane.atImInfty`), which is the same as `q → 0`.
The condition `z ∉ 𝕃` of DLMF is, eventually as `ℑτ → ∞`, the condition `z ∉ 2ω₁ℤ`.
§23.13 (zeros of `℘`) only refers to Eichler and Zagier (1982) and contains no formula.
-/

@[expose] public section

open Complex PeriodPair Asymptotics UpperHalfPlane
open scoped Real

noncomputable section

namespace DLMF.Weierstrass

namespace HalfPeriods

/-- DLMF 23.12.1: as `q → 0` with `ω₁` and `z ∉ 2ω₁ℤ` fixed,
`℘(z) = (π²/(4ω₁²))(-1/3 + csc²(πz/(2ω₁)) + 8(1 - cos(πz/ω₁))q² + O(q⁴))`. -/
@[dlmf 23.12.E1]
theorem weierstrassP_isBigO_nome (ω : ℂ) (hω : ω ≠ 0) {z : ℂ} (hz : ∀ m : ℤ, z ≠ 2 * m * ω) :
    (fun τ : ℍ ↦ (ofTau ω hω τ).weierstrassP z - π ^ 2 / (4 * ω ^ 2) *
        (-1 / 3 + 1 / Complex.sin (π * z / (2 * ω)) ^ 2 +
          8 * (1 - Complex.cos (π * z / ω)) * (ofTau ω hω τ).nome ^ 2)) =O[atImInfty]
      fun τ ↦ (ofTau ω hω τ).nome ^ 4 := by
  sorry

/-- DLMF 23.12.2: as `q → 0` with `ω₁` and `z ∉ 2ω₁ℤ` fixed,
`ζ(z) = (π²/(4ω₁²))(z/3 + (2ω₁/π)cot(πz/(2ω₁)) - 8(z - (ω₁/π)sin(πz/ω₁))q² + O(q⁴))`. -/
@[dlmf 23.12.E2]
theorem weierstrassZeta_isBigO_nome (ω : ℂ) (hω : ω ≠ 0) {z : ℂ} (hz : ∀ m : ℤ, z ≠ 2 * m * ω) :
    (fun τ : ℍ ↦ (ofTau ω hω τ).weierstrassZeta z - π ^ 2 / (4 * ω ^ 2) *
        (z / 3 + 2 * ω / π * Complex.cot (π * z / (2 * ω)) -
          8 * (z - ω / π * Complex.sin (π * z / ω)) * (ofTau ω hω τ).nome ^ 2)) =O[atImInfty]
      fun τ ↦ (ofTau ω hω τ).nome ^ 4 := by
  sorry

/-- DLMF 23.12.3: as `q → 0` with `ω₁` and `z` fixed,
`σ(z) = (2ω₁/π)exp(π²z²/(24ω₁²))sin(πz/(2ω₁))(1 - (π²z²/ω₁² - 4sin²(πz/(2ω₁)))q² + O(q⁴))`. -/
@[dlmf 23.12.E3]
theorem weierstrassSigma_isBigO_nome (ω : ℂ) (hω : ω ≠ 0) (z : ℂ) :
    (fun τ : ℍ ↦ (ofTau ω hω τ).weierstrassSigma z - 2 * ω / π *
        cexp (π ^ 2 * z ^ 2 / (24 * ω ^ 2)) * Complex.sin (π * z / (2 * ω)) *
        (1 - (π ^ 2 * z ^ 2 / ω ^ 2 - 4 * Complex.sin (π * z / (2 * ω)) ^ 2) *
          (ofTau ω hω τ).nome ^ 2)) =O[atImInfty]
      fun τ ↦ (ofTau ω hω τ).nome ^ 4 := by
  sorry

/-- DLMF 23.12.4: as `q → 0` with `ω₁` fixed, `η₁ = (π²/(4ω₁))(1/3 - 8q² + O(q⁴))`. -/
@[dlmf 23.12.E4]
theorem eta_one_isBigO_nome (ω : ℂ) (hω : ω ≠ 0) :
    (fun τ : ℍ ↦ (ofTau ω hω τ).eta 1 - π ^ 2 / (4 * ω) * (1 / 3 - 8 * (ofTau ω hω τ).nome ^ 2))
      =O[atImInfty] fun τ ↦ (ofTau ω hω τ).nome ^ 4 := by
  sorry

end HalfPeriods

end DLMF.Weierstrass
