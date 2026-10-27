/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.WignerSymbols.Basic

/-!
# Approximations for large parameters: DLMF §34.8

DLMF 34.8.1 is stated for `j₁, j₂, j₃ ≫ l₃ ≫ 1` with an `o(1)` remainder "as the parameters
tend to infinity". It is acquired as an iterated limit: first the `jᵣ` tend to infinity with
`l₃` fixed, then `l₃` tends to infinity, uniformly for `θ` (34.8.2, `largeParameterAngle`)
bounded away from `0` and `π` (`sin θ ≥ δ`; near `θ = 0, π` the prefactor `(sin θ)^{-1/2}`
is singular and the approximation is not uniform). The statement is checked numerically
with exact `6j` values up to `j ≈ 1600` (see the ledger).
-/

@[expose] public noncomputable section

open scoped Real

namespace DLMF.WignerSymbols

/-- DLMF 34.8.1–34.8.2: for `j₁, j₂, j₃ ≫ l₃ ≫ 1`,
`{j₁ j₂ j₃; j₂ j₁ l₃} = (-1)^{j₁+j₂+j₃+l₃} (4 / (π(2j₁+1)(2j₂+1)(2l₃+1) sin θ))^{1/2}`
`× (cos((l₃ + 1/2)θ - π/4) + o(1))`, with `θ` of 34.8.2. -/
@[dlmf 34.8.E1, dlmf 34.8.E2]
theorem wigner6j_large_parameters {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ L₀ : ℕ, ∀ l₃ : ℕ, L₀ ≤ l₃ → ∃ K : ℝ, ∀ j₁ j₂ j₃ : ℚ, IsTriad j₁ j₂ j₃ →
      K ≤ j₁ → K ≤ j₂ → K ≤ j₃ →
      δ ≤ Real.sin (largeParameterAngle j₁ j₂ j₃) →
      |wigner6j j₁ j₂ j₃ j₂ j₁ l₃ /
          (signPow (j₁ + j₂ + j₃ + l₃) *
            Real.sqrt (4 / (π * (2 * (j₁ : ℝ) + 1) * (2 * j₂ + 1) * (2 * l₃ + 1) *
              Real.sin (largeParameterAngle j₁ j₂ j₃)))) -
        Real.cos ((l₃ + 1 / 2) * largeParameterAngle j₁ j₂ j₃ - π / 4)| ≤ ε := by
  sorry

end DLMF.WignerSymbols
