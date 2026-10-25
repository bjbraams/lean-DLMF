/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Weierstrass.Relations
public import DLMF.Weierstrass.SpecialLattices

/-!
# Quarter periods (DLMF §23.7)

DLMF gives `℘(ω_j/2)` in two forms, a square-root form and a Jacobian form, with `k, k'` and
the square roots real and positive for rectangular lattices and "determined by continuity"
otherwise. Here the branch is made precise as follows.

* The Jacobian forms hold for every pair of generators with the lattice quantities
  `K = (π/2)θ₃²(0|τ)`, `k = θ₂²(0|τ)/θ₃²(0|τ)`, `k' = θ₄²(0|τ)/θ₃²(0|τ)` (these are the
  analytic continuations in `τ` of the rectangular values; checked numerically for several
  generator pairs of one lattice, including `τ` outside `-1 < ℜτ ≤ 1`).
* The squares of the square-root forms hold for every lattice, branch-free.
* For rectangular lattices the square-root forms hold with principal (positive) roots.
-/

@[expose] public section

open Complex PeriodPair DLMF.Elliptic DLMF.JacobiElliptic
open scoped Real

noncomputable section

namespace DLMF.Weierstrass

namespace HalfPeriods

variable (H : HalfPeriods)

/-- DLMF 23.7.1 (Jacobian form): `℘(ω₁/2) = e₁ + ω₁⁻²K²k'`. -/
@[dlmf 23.7.E1]
theorem weierstrassP_half_ω₁ :
    H.weierstrassP (H.ω₁ / 2) = H.e 1 + H.quarterK ^ 2 * H.comodulus / H.ω₁ ^ 2 := by
  sorry

/-- DLMF 23.7.2 (Jacobian form): `℘(ω₂/2) = e₂ - iω₁⁻²K²kk'`. -/
@[dlmf 23.7.E2]
theorem weierstrassP_half_ω₂ :
    H.weierstrassP (H.ω₂ / 2) =
      H.e 2 - I * H.quarterK ^ 2 * H.modulus * H.comodulus / H.ω₁ ^ 2 := by
  sorry

/-- DLMF 23.7.3 (Jacobian form): `℘(ω₃/2) = e₃ - ω₁⁻²K²k`. -/
@[dlmf 23.7.E3]
theorem weierstrassP_half_ω₃ :
    H.weierstrassP (H.ω₃ / 2) = H.e 3 - H.quarterK ^ 2 * H.modulus / H.ω₁ ^ 2 := by
  sorry

/-- DLMF 23.7.1–23.7.3 (square-root forms, squared; every lattice):
`(℘(ω₁/2) - e₁)² = (e₁ - e₃)(e₁ - e₂)`, `(℘(ω₂/2) - e₂)² = -(e₁ - e₂)(e₂ - e₃)`,
`(℘(ω₃/2) - e₃)² = (e₁ - e₃)(e₂ - e₃)`. -/
@[dlmf 23.7.E1, dlmf 23.7.E2, dlmf 23.7.E3]
theorem weierstrassP_half_sq :
    (H.weierstrassP (H.ω₁ / 2) - H.e 1) ^ 2 = (H.e 1 - H.e 3) * (H.e 1 - H.e 2) ∧
      (H.weierstrassP (H.ω₂ / 2) - H.e 2) ^ 2 = -((H.e 1 - H.e 2) * (H.e 2 - H.e 3)) ∧
      (H.weierstrassP (H.ω₃ / 2) - H.e 3) ^ 2 = (H.e 1 - H.e 3) * (H.e 2 - H.e 3) := by
  sorry

/-- DLMF 23.7.1–23.7.3 (square-root forms, rectangular lattice, positive roots):
`℘(ω₁/2) = e₁ + √((e₁ - e₃)(e₁ - e₂))`, `℘(ω₂/2) = e₂ - i√((e₁ - e₂)(e₂ - e₃))`,
`℘(ω₃/2) = e₃ - √((e₁ - e₃)(e₂ - e₃))`. -/
@[dlmf 23.7.E1, dlmf 23.7.E2, dlmf 23.7.E3]
theorem IsRectangular.weierstrassP_half {H : HalfPeriods} (h : H.IsRectangular) :
    H.weierstrassP (H.ω₁ / 2) =
        H.e 1 + (Real.sqrt (((H.e 1 - H.e 3) * (H.e 1 - H.e 2)).re) : ℂ) ∧
      H.weierstrassP (H.ω₂ / 2) =
        H.e 2 - I * (Real.sqrt (((H.e 1 - H.e 2) * (H.e 2 - H.e 3)).re) : ℂ) ∧
      H.weierstrassP (H.ω₃ / 2) =
        H.e 3 - (Real.sqrt (((H.e 1 - H.e 3) * (H.e 2 - H.e 3)).re) : ℂ) := by
  sorry

end HalfPeriods

end DLMF.Weierstrass
