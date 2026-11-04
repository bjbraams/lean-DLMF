/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The complete elliptic integral of the first kind (DLMF 19.2.8–19.2.9)

Legendre's complete elliptic integral of the first kind `K(k)` and its complementary integral
`K'(k)` for complex modulus, as integrals over `[0, π/2]` with the principal power.

## Main definitions

* `completeEllipticK`: `K(k) = ∫₀^{π/2} (1 - k² sin²θ)^{-1/2} dθ` (DLMF 19.2.8).
* `completeEllipticKPrime`: `K'(k) = ∫₀^{π/2} (1 - (1 - k²) sin²θ)^{-1/2} dθ` (DLMF 19.2.9).

## Implementation notes

The other complete integrals `E(k)`, `D(k)` and `Π(α², k)` are complete values of the
incomplete integrals in `DLMF.EllipticIntegrals.Basic.Legendre`, where `K(k) = F(π/2, k)` is
proved. `K` and `K'` are kept in this small file because the modulus form of the Jacobian
elliptic functions (`DLMF.JacobiElliptic.Basic.Definitions`) is built on them.
-/

@[expose] public section

open Complex

open scoped Real

noncomputable section

namespace DLMF.EllipticIntegrals

/-- Legendre's complete elliptic integral of the first kind for complex modulus,
`K(k) = ∫₀^{π/2} (1 - k² sin²θ)^{-1/2} dθ` with the principal power (DLMF 19.2.8); it is the
principal branch for `k² ∈ ℂ \ [1, ∞)`. -/
@[dlmf 19.2.E8]
def completeEllipticK (k : ℂ) : ℂ :=
  ∫ θ in (0 : ℝ)..(π / 2), (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))

/-- The complementary integral `K'(k) = K(k') = ∫₀^{π/2} (1 - (1 - k²) sin²θ)^{-1/2} dθ`
(DLMF 19.2.9), principal for `k² ∈ ℂ \ (-∞, 0]`. -/
@[dlmf 19.2.E9]
def completeEllipticKPrime (k : ℂ) : ℂ :=
  ∫ θ in (0 : ℝ)..(π / 2), (1 - (1 - k ^ 2) * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))

end DLMF.EllipticIntegrals
