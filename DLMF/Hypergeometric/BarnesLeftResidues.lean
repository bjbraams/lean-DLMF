/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.BarnesContours
public import DLMF.Hypergeometric.PrincipalConnections
public import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Left Barnes residues and logarithmic coalescence

Olver, *Asymptotics and Special Functions*, Chapter 8, §6,
pp. 299–302, synopsis O-8.08. The residue series converges outside the
unit circle. At integral upper differences the two families must be combined
before a parameter limit; differentiating the cleared expression generates logs.
-/

@[expose] public noncomputable section
open Complex Filter
open scoped Topology
namespace DLMF.Hypergeometric.GaussBarnes

/-- The normalized coefficient from the pole s=-a-j. Olver, Chapter 8,
§6, pp. 299–302. The other family interchanges a and b. -/
def leftResidueCoefficient (a b c z : ℂ) (j : ℕ) : ℂ :=
  (-1 : ℂ) ^ j * Gamma (b - a - j) * pochhammer a j * (-z) ^ (-a - j) /
    (j.factorial * Gamma (c - a - j) * Gamma b)

/-- The defining explicit left-pole coefficient. -/
theorem leftResidueCoefficient_def (a b c z : ℂ) (j : ℕ) :
    leftResidueCoefficient a b c z j =
      (-1 : ℂ) ^ j * Gamma (b - a - j) * pochhammer a j * (-z) ^ (-a - j) /
        (j.factorial * Gamma (c - a - j) * Gamma b) := rfl

/-- A sufficiently small positively oriented circle isolates the normalized
Barnes left residue, including possible zeros of reciprocal Gamma.
Olver, Chapter 8, §6, pp. 299–302. -/
theorem circleIntegral_barnesIntegrand_left {a b c z : ℂ}
    (ha : ∀ n : ℕ, a ≠ -(n : ℂ)) (hb : ∀ n : ℕ, b ≠ -(n : ℂ))
    (hab : ∀ k : ℤ, a - b ≠ (k : ℂ)) (hz : -z ∈ slitPlane) (j : ℕ) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r ∈ Set.Ioo 0 r₀,
      (∮ s in C(-a - j, r), barnesIntegrand a b c z s) /
        (2 * Real.pi * I * Gamma a * Gamma b) = leftResidueCoefficient a b c z j := by
  sorry

/-- Closing the Barnes contour to the left gives both full convergent residue
families. Olver, Chapter 8, §6, pp. 299–302. -/
theorem hasSum_leftResidueCoefficient {a b c z : ℂ}
    (ha : ∀ n : ℕ, a ≠ -(n : ℂ)) (hb : ∀ n : ℕ, b ≠ -(n : ℂ))
    (hab : ∀ k : ℤ, a - b ≠ (k : ℂ)) (hz : -z ∈ slitPlane) (hz₁ : 1 < ‖z‖) :
    HasSum (fun j : ℕ => leftResidueCoefficient a b c z j +
      leftResidueCoefficient b a c z j) (regularizedGaussHypergeometric a b c z) := by
  sorry

/-- Both left-pole series converge normally on compact subsets of their
exterior principal-cut domain. Olver, Chapter 8, §6, pp. 299–302. -/
theorem tendstoLocallyUniformlyOn_sum_leftResidueCoefficient {a b c : ℂ}
    (ha : ∀ n : ℕ, a ≠ -(n : ℂ)) (hb : ∀ n : ℕ, b ≠ -(n : ℂ))
    (hab : ∀ k : ℤ, a - b ≠ (k : ℂ)) :
    TendstoLocallyUniformlyOn
      (fun N : ℕ => fun z : ℂ => ∑ j ∈ Finset.range N,
        (leftResidueCoefficient a b c z j + leftResidueCoefficient b a c z j))
      (regularizedGaussHypergeometric a b c) atTop {z | -z ∈ slitPlane ∧ 1 < ‖z‖} := by
  sorry

/-- The sine-cleared connection numerator at infinity. Its derivative in b
contains the logarithm -log(-z) from the moving power (-z)^(-b).
Olver, Chapter 8, §6, pp. 299–302. -/
def connectionNumerator (a b c z : ℂ) : ℂ :=
  (-z) ^ (-a) * regularizedGaussHypergeometric a (1 + a - c) (1 + a - b) z⁻¹ /
    (Gamma b * Gamma (c - a)) -
      (-z) ^ (-b) * regularizedGaussHypergeometric b (1 + b - c) (1 + b - a) z⁻¹ /
        (Gamma a * Gamma (c - b))

/-- The explicit sine-cleared numerator. -/
theorem connectionNumerator_def (a b c z : ℂ) : connectionNumerator a b c z =
    (-z) ^ (-a) * regularizedGaussHypergeometric a (1 + a - c) (1 + a - b) z⁻¹ /
      (Gamma b * Gamma (c - a)) -
        (-z) ^ (-b) * regularizedGaussHypergeometric b (1 + b - c) (1 + b - a) z⁻¹ /
          (Gamma a * Gamma (c - b)) := rfl

/-- At every integral upper difference, the combined derivative gives the
logarithmic continuation value without separately totalizing either singular
residue family. Olver, Chapter 8, §6, pp. 299–302. -/
theorem regularizedGaussHypergeometric_eq_connectionNumerator_deriv
    (a c : ℂ) (m : ℤ) {z : ℂ} (hz : -z ∈ slitPlane) :
    regularizedGaussHypergeometric a (a + m) c z =
      (-1 : ℂ) ^ m * deriv (fun b : ℂ => connectionNumerator a b c z) (a + m) := by
  sorry

end DLMF.Hypergeometric.GaussBarnes
