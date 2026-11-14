/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Basic.CutPlane

/-!
# Principal Gauss connection formulas and resonant limits

The regularized normalization permits all lower parameters. Clearing the sine
factor gives an entire-parameter identity; the quotient has the prescribed
removable limit when exponent differences are integers. Full common principal
cut domains are used, rather than just the intersection of two power-series discs.
Source: Kristensson, *Second Order Differential Equations*, Chapter 5,
Theorem 5.5, pp. 84–86, and §5.6.1, pp. 89–90; DLMF 15.8.2, 15.8.4.
-/

@[expose] public noncomputable section

open Complex Filter
open scoped Real Topology

namespace DLMF.Hypergeometric.GaussConnection

/-- The principal connection expression at infinity, before taking removable
integer-exponent-difference limits. Kristensson, Theorem 5.5, pp. 84–86. -/
def atInfinity (a b c z : ℂ) : ℂ :=
  Real.pi / sin (Real.pi * (b - a)) *
    ((-z) ^ (-a) * regularizedGaussHypergeometric a (1 + a - c) (1 + a - b) z⁻¹ /
      (Gamma b * Gamma (c - a)) -
      (-z) ^ (-b) * regularizedGaussHypergeometric b (1 + b - c) (1 + b - a) z⁻¹ /
        (Gamma a * Gamma (c - b)))

/-- The explicit two terms of the infinity connection expression. -/
theorem atInfinity_def (a b c z : ℂ) : atInfinity a b c z =
    Real.pi / sin (Real.pi * (b - a)) *
      ((-z) ^ (-a) * regularizedGaussHypergeometric a (1 + a - c) (1 + a - b) z⁻¹ /
        (Gamma b * Gamma (c - a)) -
        (-z) ^ (-b) * regularizedGaussHypergeometric b (1 + b - c) (1 + b - a) z⁻¹ /
          (Gamma a * Gamma (c - b))) := rfl

/-- The principal connection expression at one. Kristensson, Chapter 5,
§5.6.1, pp. 89–90. Integer exponent differences require its parameter limit. -/
def atOne (a b c z : ℂ) : ℂ :=
  Real.pi / sin (Real.pi * (c - a - b)) *
    (regularizedGaussHypergeometric a b (1 + a + b - c) (1 - z) /
      (Gamma (c - a) * Gamma (c - b)) -
      (1 - z) ^ (c - a - b) *
        regularizedGaussHypergeometric (c - a) (c - b) (1 + c - a - b) (1 - z) /
          (Gamma a * Gamma b))

/-- The explicit two terms of the connection expression at one. -/
theorem atOne_def (a b c z : ℂ) : atOne a b c z =
    Real.pi / sin (Real.pi * (c - a - b)) *
      (regularizedGaussHypergeometric a b (1 + a + b - c) (1 - z) /
        (Gamma (c - a) * Gamma (c - b)) -
        (1 - z) ^ (c - a - b) *
          regularizedGaussHypergeometric (c - a) (c - b) (1 + c - a - b) (1 - z) /
            (Gamma a * Gamma b)) := rfl

end DLMF.Hypergeometric.GaussConnection

namespace DLMF.Hypergeometric

/-- The full principal infinity connection formula with its sine factor cleared.
All parameters are allowed; at resonances both sides vanish before the removable
quotient is taken. Kristensson, Theorem 5.5, pp. 84–86; DLMF 15.8.2. -/
theorem regularizedGaussHypergeometric_connection_inv (a b c : ℂ) {z : ℂ}
    (hz : -z ∈ slitPlane) :
    sin (Real.pi * (b - a)) / Real.pi * regularizedGaussHypergeometric a b c z =
      (-z) ^ (-a) * regularizedGaussHypergeometric a (1 + a - c) (1 + a - b) z⁻¹ /
        (Gamma b * Gamma (c - a)) -
        (-z) ^ (-b) * regularizedGaussHypergeometric b (1 + b - c) (1 + b - a) z⁻¹ /
          (Gamma a * Gamma (c - b)) := by
  sorry

/-- The infinity connection quotient is exactly the principal continued Gauss
function at noninteger upper-parameter difference, on the whole stated cut.
Kristensson, Theorem 5.5, pp. 84–86. -/
theorem regularizedGaussHypergeometric_eq_connection_inv (a b c : ℂ)
    (hab : ∀ k : ℤ, b - a ≠ (k : ℂ)) {z : ℂ} (hz : -z ∈ slitPlane) :
    regularizedGaussHypergeometric a b c z = GaussConnection.atInfinity a b c z := by
  sorry

/-- The whole infinity connection expression has the correct removable parameter
limit, including all integer upper-parameter differences and denominator Gamma
poles. The two summands are combined before taking the limit. Kristensson,
Chapter 5, §5.5, pp. 84–88. -/
theorem tendsto_connection_inv (a b c : ℂ) {z : ℂ} (hz : -z ∈ slitPlane) :
    Tendsto (fun v : ℂ => GaussConnection.atInfinity a v c z) (𝓝[≠] b)
      (𝓝 (regularizedGaussHypergeometric a b c z)) := by
  sorry

/-- The full principal zero-to-one connection formula with its sine factor
cleared. Both principal arguments remain in their cut planes. Kristensson,
Chapter 5, §5.6.1, pp. 89–90; DLMF 15.8.4. -/
theorem regularizedGaussHypergeometric_connection_one_sub (a b c : ℂ) {z : ℂ}
    (hz : z ∈ cutPlane) (h₁z : 1 - z ∈ cutPlane) :
    sin (Real.pi * (c - a - b)) / Real.pi * regularizedGaussHypergeometric a b c z =
      regularizedGaussHypergeometric a b (1 + a + b - c) (1 - z) /
        (Gamma (c - a) * Gamma (c - b)) -
        (1 - z) ^ (c - a - b) *
          regularizedGaussHypergeometric (c - a) (c - b) (1 + c - a - b) (1 - z) /
            (Gamma a * Gamma b) := by
  sorry

/-- The nonresonant connection quotient at one on the complete common principal
cut domain. Kristensson, Chapter 5, §5.6.1, pp. 89–90. -/
theorem regularizedGaussHypergeometric_eq_connection_one_sub (a b c : ℂ)
    (habc : ∀ k : ℤ, c - a - b ≠ (k : ℂ)) {z : ℂ}
    (hz : z ∈ cutPlane) (h₁z : 1 - z ∈ cutPlane) :
    regularizedGaussHypergeometric a b c z = GaussConnection.atOne a b c z := by
  sorry

/-- The complete connection expression at one has the prescribed removable
limit at every parameter, including integer exponent differences. This avoids
assigning separate finite values to two divergent Gamma terms. Kristensson,
Chapter 5, §5.6.1, pp. 89–90. -/
theorem tendsto_connection_one_sub (a b c : ℂ) {z : ℂ}
    (hz : z ∈ cutPlane) (h₁z : 1 - z ∈ cutPlane) :
    Tendsto (fun v : ℂ => GaussConnection.atOne a v c z) (𝓝[≠] b)
      (𝓝 (regularizedGaussHypergeometric a b c z)) := by
  sorry

end DLMF.Hypergeometric
