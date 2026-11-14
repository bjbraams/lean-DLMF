/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bessel.OrderAndZeroProperties
public import Mathlib.Topology.Order.Basic

/-!
# Adaptive complex Bessel weights

The supremum ranges over the actual intersection of a vertical strip and a disc.
It is not a real-axis modulus envelope. The nonzero closed right half-plane is
the domain of the modulus statements; the order-zero modulus is unbounded at
the origin, so no finite continuous extension there is claimed.
Source: Olver, *Asymptotics and Special Functions*, Chapter 12,
§8, (8.01)–(8.14), pp. 453–457.
-/

@[expose] public noncomputable section

open Complex Set
open scoped Real

namespace DLMF.AsymptoticApproximations.BesselComplexEnvelope

/-- The comparison set `0<=Re(t)<=Re(z), abs(t)<=abs(z)`.
Olver, Chapter 12, (8.04), p. 454. -/
def comparisonRegion (z : ℂ) : Set ℂ :=
  {t | 0 ≤ t.re ∧ t.re ≤ z.re ∧ ‖t‖ ≤ ‖z‖}

/-- Membership in the defining strip-disc intersection. -/
theorem mem_comparisonRegion_iff (z t : ℂ) : t ∈ comparisonRegion z ↔
    0 ≤ t.re ∧ t.re ≤ z.re ∧ ‖t‖ ≤ ‖z‖ := Iff.rfl

/-- The square of the adaptive weight, using the limiting ratio zero at `t=0`.
Olver, Chapter 12, (8.03)–(8.04), p. 454. -/
def weightSquared (ν : ℝ) (z : ℂ) : ℝ :=
  sSup ((fun t : ℂ => if t = 0 then 0 else
    ‖DLMF.Bessel.besselI ν t / DLMF.Bessel.besselK ν t‖) '' comparisonRegion z)

/-- The actual supremum defining the squared adaptive weight. -/
theorem weightSquared_def (ν : ℝ) (z : ℂ) : weightSquared ν z =
    sSup ((fun t : ℂ => if t = 0 then 0 else
      ‖DLMF.Bessel.besselI ν t / DLMF.Bessel.besselK ν t‖) '' comparisonRegion z) := rfl

/-- The nonnegative adaptive complex weight. Olver, Chapter 12, §8, p. 454. -/
def weight (ν : ℝ) (z : ℂ) : ℝ := Real.sqrt (weightSquared ν z)

/-- The defining nonnegative square root. -/
theorem weight_def (ν : ℝ) (z : ℂ) : weight ν z = Real.sqrt (weightSquared ν z) := rfl

/-- The complex modulus on the nonzero right half-plane. Olver,
Chapter 12, (8.11), p. 456. Its value at zero is a totalization only. -/
def modulus (ν : ℝ) (z : ℂ) : ℝ :=
  Real.sqrt ((‖DLMF.Bessel.besselI ν z‖ / weight ν z) ^ 2 +
    (weight ν z * ‖DLMF.Bessel.besselK ν z‖) ^ 2)

/-- The defining weighted sum of squares. -/
theorem modulus_def (ν : ℝ) (z : ℂ) : modulus ν z =
    Real.sqrt ((‖DLMF.Bessel.besselI ν z‖ / weight ν z) ^ 2 +
      (weight ν z * ‖DLMF.Bessel.besselK ν z‖) ^ 2) := rfl

/-- The supremum is finite; the weight is positive away from zero, jointly
continuous, and bounds the Bessel ratio throughout its comparison region.
Olver, Chapter 12, §8, pp. 454–456. -/
theorem weight_properties :
    ContinuousOn (fun p : ℝ × ℂ => weight p.1 p.2) {p | 0 ≤ p.1 ∧ 0 ≤ p.2.re} ∧
      ∀ ν : ℝ, 0 ≤ ν → weight ν 0 = 0 ∧
        ∀ z : ℂ, 0 ≤ z.re →
          BddAbove ((fun t : ℂ => if t = 0 then 0 else
            ‖DLMF.Bessel.besselI ν t / DLMF.Bessel.besselK ν t‖) '' comparisonRegion z) ∧
          weight ν z ^ 2 = weightSquared ν z ∧
          weightSquared ν z ≤ 2 / Real.pi * Real.exp (2 * z.re) ∧
          (z ≠ 0 → 0 < weight ν z) ∧
          ∀ t ∈ comparisonRegion z, t ≠ 0 →
            ‖DLMF.Bessel.besselI ν t / DLMF.Bessel.besselK ν t‖ ≤ weightSquared ν z := by
  sorry

/-- The modulus is positive and continuous on its nonzero domain, and the
weight gives simultaneous majorants for `I` and `K`.
Olver, Chapter 12, (8.11)–(8.12), pp. 456–457. -/
theorem modulus_properties :
    ContinuousOn (fun p : ℝ × ℂ => modulus p.1 p.2)
      {p | 0 ≤ p.1 ∧ 0 ≤ p.2.re ∧ p.2 ≠ 0} ∧
      ∀ (ν : ℝ) (z : ℂ), 0 ≤ ν → 0 ≤ z.re → z ≠ 0 →
        0 < modulus ν z ∧
          ‖DLMF.Bessel.besselI ν z‖ ≤ weight ν z * modulus ν z ∧
          ‖DLMF.Bessel.besselK ν z‖ ≤ modulus ν z / weight ν z := by
  sorry

/-- The proper-sector equivalent is uniform in every bounded interval of
nonnegative orders. Olver, Chapter 12, (8.08), p. 455. -/
theorem exists_uniform_sector_weight_equivalent {N ε δ : ℝ}
    (hN : 0 ≤ N) (hε : 0 < ε) (hεpi : ε < Real.pi / 2) (hδ : 0 < δ) :
    ∃ R : ℝ, 0 < R ∧ ∀ (ν : ℝ) (z : ℂ), 0 ≤ ν → ν ≤ N → R ≤ ‖z‖ →
      |arg z| ≤ Real.pi / 2 - ε →
        |weightSquared ν z * Real.exp (-2 * z.re) - 1 / Real.pi| ≤ δ := by
  sorry

/-- Both directions of the modulus estimate hold on the entire closed right
half-plane, locally uniformly in order. Olver, Chapter 12, (8.13)–(8.14), p. 457. -/
theorem exists_uniform_halfPlane_modulus_bounds {N : ℝ} (hN : 0 ≤ N) :
    ∃ R C : ℝ, 0 < R ∧ 0 < C ∧ ∀ (ν : ℝ) (z : ℂ),
      0 ≤ ν → ν ≤ N → 0 ≤ z.re → R ≤ ‖z‖ →
        modulus ν z ≤ C / Real.sqrt ‖z‖ ∧ (modulus ν z)⁻¹ ≤ C * Real.sqrt ‖z‖ := by
  sorry

end DLMF.AsymptoticApproximations.BesselComplexEnvelope
