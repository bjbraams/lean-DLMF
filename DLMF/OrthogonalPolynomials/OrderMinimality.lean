/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Basic.PolynomialContinuation
public import DLMF.OrthogonalPolynomials.JacobiContinuation

/-!
# Jacobi second-kind sequences and degree minimality

Temme, *Special Functions* (1996), §13.3, Example 9, p. 342.
The second kind uses the book's Cauchy-transform normalization.
-/

@[expose] public noncomputable section
open Filter MeasureTheory Set Complex
open scoped Topology
namespace DLMF.OrthogonalPolynomials

/-- The Jacobi second-kind Cauchy transform for real parameters greater than minus one,
with principal powers and complex argument outside `[-1,1]`.
Temme §13.3, Example 9, synopsis TEM-13-08. -/
def jacobiSecondKind (α β : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  (z - 1) ^ (-(α : ℂ)) * (z + 1) ^ (-(β : ℂ)) / 2 *
    ∫ t : ℝ in (-1 : ℝ)..1, ((1 - t : ℝ) ^ α * (1 + t : ℝ) ^ β : ℝ) *
      jacobiExtended α β n t / (z - t)

/-- The defining integral and normalization of the Jacobi second kind,
Temme §13.3, Example 9, synopsis TEM-13-08. -/
theorem jacobiSecondKind_def (α β : ℝ) (n : ℕ) (z : ℂ) :
    jacobiSecondKind α β n z =
      (z - 1) ^ (-(α : ℂ)) * (z + 1) ^ (-(β : ℂ)) / 2 *
        ∫ t : ℝ in (-1 : ℝ)..1, ((1 - t : ℝ) ^ α * (1 + t : ℝ) ^ β : ℝ) *
          jacobiExtended α β n t / (z - t) := rfl

/-- Integrability of the defining second-kind transform off the orthogonality interval,
Temme §13.3, Example 9, synopsis TEM-13-08. -/
theorem intervalIntegrable_jacobiSecondKind_integrand {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (n : ℕ) {z : ℂ}
    (hz : ∀ t ∈ Icc (-1 : ℝ) 1, z ≠ t) :
    IntervalIntegrable (fun t : ℝ => ((1 - t : ℝ) ^ α * (1 + t : ℝ) ^ β : ℝ) *
      jacobiExtended α β n t / (z - t)) volume (-1) 1 := by
  sorry

/-- The dominant Jacobi degree ratio on the exterior Joukowski sheet,
Temme §13.3, Example 9, synopsis TEM-13-08. -/
theorem tendsto_jacobiExtended_degree_ratio {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β) {z w : ℂ}
    (hw : 1 < ‖w‖) (hzw : w + w⁻¹ = 2 * z) :
    Tendsto (fun n : ℕ => jacobiExtended α β (n + 1) z / jacobiExtended α β n z)
      atTop (𝓝 w) := by
  sorry

/-- The minimal second-kind Jacobi degree ratio, Temme §13.3, Example 9,
synopsis TEM-13-08. -/
theorem tendsto_jacobiSecondKind_degree_ratio {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β) {z w : ℂ}
    (hw : 1 < ‖w‖) (hzw : w + w⁻¹ = 2 * z) :
    Tendsto (fun n : ℕ => jacobiSecondKind α β (n + 1) z / jacobiSecondKind α β n z)
      atTop (𝓝 w⁻¹) := by
  sorry

/-- The Jacobi second kind is minimal outside the orthogonality interval,
Temme §13.3, Example 9, synopsis TEM-13-08. -/
theorem tendsto_jacobiSecondKind_div_jacobiExtended {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β) {z w : ℂ}
    (hw : 1 < ‖w‖) (hzw : w + w⁻¹ = 2 * z) :
    Tendsto (fun n : ℕ => jacobiSecondKind α β n z / jacobiExtended α β n z)
      atTop (𝓝 0) := by
  sorry

end DLMF.OrthogonalPolynomials
