/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# Mellin transform methods: definitions (DLMF §2.5)

The Mellin transform 2.5.1 is Mathlib's `mellin f s = ∫₀^∞ t^{s-1} f(t) dt` and its inverse
2.5.2 is `mellinInv`. This file defines

* `mellinTruncLow f`, `mellinTruncHigh f` (2.5.21–2.5.24): the truncations `f₁ = f` on
  `(0, 1]`, `0` on `(1, ∞)`, and `f₂ = f - f₁`;
* `besselSqMellinKernel ν z`, `besselSqMellinA ν n`, `besselSqMellinB ν n` (2.5.10–2.5.13): the
  meromorphic factor `2^{z-1}Γ(ν + z/2)/(Γ²(1 - z/2) Γ(1 + ν - z/2) Γ(z))` of the Mellin
  transform of `J_ν²`, and `aₙ = A(n)`, `bₙ = -A'(n)` of the example 2.5.8. Reciprocals of
  `Γ` use Mathlib's `Complex.Gamma`, which is `0` at the poles, so that `(Γ w)⁻¹` is the entire
  function `1/Γ(w)` everywhere.
-/

@[expose] public noncomputable section

open Set Complex

namespace DLMF.AsymptoticApproximations

/-- DLMF 2.5.21, 2.5.23: the truncation `f₁(t) = f(t)` for `0 < t ≤ 1`, `f₁(t) = 0` for
`1 < t < ∞` (values for `t ≤ 0` are irrelevant to Mellin transforms). -/
@[dlmf 2.5.E21, dlmf 2.5.E23]
def mellinTruncLow (f : ℝ → ℂ) : ℝ → ℂ :=
  (Iic (1 : ℝ)).indicator f

/-- DLMF 2.5.22, 2.5.24: `f₂(t) = f(t) - f₁(t)`. -/
@[dlmf 2.5.E22, dlmf 2.5.E24]
def mellinTruncHigh (f : ℝ → ℂ) : ℝ → ℂ :=
  f - mellinTruncLow f

/-- The factor `A(z) = 2^{z-1} Γ(ν + z/2) / (Γ²(1 - z/2) Γ(1 + ν - z/2) Γ(z))` in DLMF 2.5.10,
`𝓜h(z) = A(z) π/sin(πz)` for `h(t) = J_ν²(t)`; reciprocal Gamma functions are entire. -/
def besselSqMellinKernel (ν : ℝ) (z : ℂ) : ℂ :=
  (2 : ℂ) ^ (z - 1) * Gamma (ν + z / 2) * (Gamma (1 - z / 2))⁻¹ ^ 2 *
    (Gamma (1 + ν - z / 2))⁻¹ * (Gamma z)⁻¹

/-- DLMF 2.5.12: `aₙ = 2^{n-1} Γ(ν + n/2) / (Γ²(1 - n/2) Γ(1 + ν - n/2) Γ(n))`. -/
@[dlmf 2.5.E12]
def besselSqMellinA (ν : ℝ) (n : ℕ) : ℂ :=
  besselSqMellinKernel ν n

/-- DLMF 2.5.13: `bₙ = -A'(n)`, where `A = besselSqMellinKernel ν`, so that the residue 2.5.11 of
`x^{-z} A(z) π²/sin²(πz)` at `z = n` is `-(aₙ ln x + bₙ) x^{-n}` (see `BesselExample`). Where all
Gamma functions in `A(n)` are finite and nonzero, `-A'(n)` is DLMF's
`-aₙ(ln 2 + ½ψ(ν + n/2) + ψ(1 - n/2) + ½ψ(1 + ν - n/2) - ψ(n))`
(`besselSqMellinB_eq_digamma`); the derivative form also covers the cases where `aₙ = 0`
because a reciprocal Gamma function vanishes and DLMF's product is of the form `0 · ∞`. -/
@[dlmf 2.5.E13]
def besselSqMellinB (ν : ℝ) (n : ℕ) : ℂ :=
  -deriv (besselSqMellinKernel ν) n

end DLMF.AsymptoticApproximations
