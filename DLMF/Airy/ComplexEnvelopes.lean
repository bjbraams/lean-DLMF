/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Airy.Basic

/-!
# Complex Airy envelopes

The three weights select their principal fractional power after rotating the
argument into their own sector. These real weights are continuous across their
opposite rays; their branch choices are separate from logarithmic continuation
of analytic solutions. The two error constants are actual finite suprema.
Source: Olver, *Asymptotics and Special Functions*, Chapter 11,
§8.3, (8.07)–(8.12), pp. 415–416, used in Theorem 9.1, pp. 417–418.
-/

@[expose] public noncomputable section

open Complex Set
open scoped Real

namespace DLMF.Airy.ComplexEnvelope

/-- The cubic rotation taking sector `j` to the positive sector. The index is
periodic modulo three. Olver, Chapter 11, §8.1, pp. 413–414. -/
def rotation (j : ℤ) : ℂ := exp (-2 * Real.pi * I * j / 3)

/-- The defining cubic root of unity. -/
theorem rotation_def (j : ℤ) : rotation j = exp (-2 * Real.pi * I * j / 3) := rfl

/-- The canonical recessive Airy solution in sector `j`. Olver, Chapter 11,
§8.1, pp. 413–414. -/
def solution (j : ℤ) (z : ℂ) : ℂ := airyAi (rotation j * z)

/-- The defining rotated Airy solution. -/
theorem solution_def (j : ℤ) (z : ℂ) : solution j z = airyAi (rotation j * z) := rfl

/-- The derivative with respect to the physical argument, including its rotation
factor. Olver, Chapter 11, §8.3, (8.09), p. 415. -/
def derivative (j : ℤ) (z : ℂ) : ℂ := rotation j * airyAiDeriv (rotation j * z)

/-- The defining physical derivative. -/
theorem derivative_def (j : ℤ) (z : ℂ) :
    derivative j z = rotation j * airyAiDeriv (rotation j * z) := rfl

/-- The closed recessive sector `S_j`, with opening `2pi/3`.
Olver, Chapter 11, §8.1, p. 413. -/
def sector (j : ℤ) : Set ℂ := {z | |arg (rotation j * z)| ≤ Real.pi / 3}

/-- Membership in the closed canonical Airy sector. -/
theorem mem_sector (j : ℤ) (z : ℂ) : z ∈ sector j ↔
    |arg (rotation j * z)| ≤ Real.pi / 3 := Iff.rfl

/-- The weight `E_j`, at least one in `S_j` and at most one in the adjacent
sectors. The rotated principal power fixes the branch in each sector separately.
Olver, Chapter 11, §8.3, (8.07), p. 415. -/
def weight (j : ℤ) (z : ℂ) : ℝ :=
  Real.exp (((2 / 3 : ℂ) * (rotation j * z) ^ (3 / 2 : ℂ)).re)

/-- The defining real exponential weight. -/
theorem weight_def (j : ℤ) (z : ℂ) : weight j z =
    Real.exp (((2 / 3 : ℂ) * (rotation j * z) ^ (3 / 2 : ℂ)).re) := rfl

/-- Every complex Airy weight is positive. -/
theorem weight_pos (j : ℤ) (z : ℂ) : 0 < weight j z := Real.exp_pos _

/-- The complex Airy modulus `M_j`. Olver, Chapter 11, (8.08), p. 415. -/
def modulus (j : ℤ) (z : ℂ) : ℝ := Real.sqrt
  ((weight (j + 1) z * ‖solution (j + 1) z‖) ^ 2 +
    (weight (j - 1) z * ‖solution (j - 1) z‖) ^ 2)

/-- The defining weighted adjacent-solution modulus. -/
theorem modulus_def (j : ℤ) (z : ℂ) : modulus j z = Real.sqrt
    ((weight (j + 1) z * ‖solution (j + 1) z‖) ^ 2 +
      (weight (j - 1) z * ‖solution (j - 1) z‖) ^ 2) := rfl

/-- The complex derivative modulus `N_j`. Olver, Chapter 11, (8.09), p. 415. -/
def derivativeModulus (j : ℤ) (z : ℂ) : ℝ := Real.sqrt
  ((weight (j + 1) z * ‖derivative (j + 1) z‖) ^ 2 +
    (weight (j - 1) z * ‖derivative (j - 1) z‖) ^ 2)

/-- The defining weighted derivative modulus. -/
theorem derivativeModulus_def (j : ℤ) (z : ℂ) : derivativeModulus j z = Real.sqrt
    ((weight (j + 1) z * ‖derivative (j + 1) z‖) ^ 2 +
      (weight (j - 1) z * ‖derivative (j - 1) z‖) ^ 2) := rfl

/-- The source constant `upsilon_1`, using index zero; all three indices give
this same supremum. Olver, Chapter 11, (8.11), pp. 415–416. -/
def firstErrorConstant : ℝ := sSup
  ((fun z : ℂ => Real.pi * Real.sqrt ‖z‖ * modulus 0 z ^ 2) '' (sector (-1) ∪ sector 1))

/-- The defining supremum of the first constant. -/
theorem firstErrorConstant_def : firstErrorConstant = sSup
    ((fun z : ℂ => Real.pi * Real.sqrt ‖z‖ * modulus 0 z ^ 2) ''
      (sector (-1) ∪ sector 1)) := rfl

/-- The source constant `upsilon_2`, with the equivalent adjacent choice supplied
by the reflection/rotation symmetries. Olver, Chapter 11, (8.12), pp. 415–416. -/
def secondErrorConstant : ℝ := sSup
  ((fun z : ℂ => Real.pi * weight (-1) z * modulus 0 z * Real.sqrt ‖z‖ * ‖solution (-1) z‖) ''
    (sector (-1) ∪ sector 1))

/-- The defining supremum of the second constant. -/
theorem secondErrorConstant_def : secondErrorConstant = sSup
    ((fun z : ℂ => Real.pi * weight (-1) z * modulus 0 z * Real.sqrt ‖z‖ * ‖solution (-1) z‖) ''
      (sector (-1) ∪ sector 1)) := rfl

/-- The defined derivative and function form an entire Airy solution.
Olver, Chapter 11, §8.1, pp. 413–414. -/
theorem isAirySolution_solution (j : ℤ) : IsAirySolution (solution j) (derivative j) := by
  sorry

/-- Adjacent canonical Airy solutions have Wronskian modulus `1/(2pi)`.
Olver, Chapter 11, Exercise 8.1, p. 416. -/
theorem norm_wronskian_solution_adjacent (j : ℤ) (z : ℂ) :
    ‖solution j z * derivative (j + 1) z - derivative j z * solution (j + 1) z‖ =
      1 / (2 * Real.pi) := by
  sorry

/-- The weights and both moduli are continuous and positive on the whole plane.
Olver, Chapter 11, §8.3, (8.07)–(8.10), pp. 415–416. -/
theorem envelope_properties (j : ℤ) : Continuous (weight j) ∧ Continuous (modulus j) ∧
    Continuous (derivativeModulus j) ∧ ∀ z, 0 < modulus j z ∧ 0 < derivativeModulus j z := by
  sorry

/-- The source sector signs of the exponential weights.
Olver, Chapter 11, §8.3, (8.07), p. 415. -/
theorem weight_sector_bounds (j : ℤ) (z : ℂ) :
    (z ∈ sector j → 1 ≤ weight j z) ∧
      (z ∈ sector (j - 1) ∪ sector (j + 1) → weight j z ≤ 1) := by
  sorry

/-- Rotation and conjugation preserve the canonical envelope normalizations.
Olver, Chapter 11, (8.07), (8.10), pp. 415–416. -/
theorem rotation_conjugation (j : ℤ) (z : ℂ) :
    weight j (rotation (-1) * z) = weight (j - 1) z ∧
    modulus j (rotation (-1) * z) = modulus (j - 1) z ∧
    derivativeModulus j (rotation (-1) * z) = derivativeModulus (j - 1) z ∧
    weight j (star z) = weight (-j) z ∧ modulus j (star z) = modulus (-j) z ∧
    derivativeModulus j (star z) = derivativeModulus (-j) z := by
  sorry

/-- The two defining ranges are bounded, their suprema are independent of the
index and the adjacent sign, and both source constants are positive.
Olver, Chapter 11, (8.11)–(8.12), pp. 415–416. -/
theorem errorConstant_bounds : 0 < firstErrorConstant ∧ 0 < secondErrorConstant ∧
    ∀ j : ℤ,
      BddAbove ((fun z : ℂ => Real.pi * Real.sqrt ‖z‖ * modulus j z ^ 2) ''
        (sector (j - 1) ∪ sector (j + 1))) ∧
      sSup ((fun z : ℂ => Real.pi * Real.sqrt ‖z‖ * modulus j z ^ 2) ''
        (sector (j - 1) ∪ sector (j + 1))) = firstErrorConstant ∧
      ∀ σ : ℤ, (σ = 1 ∨ σ = -1) →
        BddAbove ((fun z : ℂ => Real.pi * weight (j + σ) z * modulus j z *
          Real.sqrt ‖z‖ * ‖solution (j + σ) z‖) '' (sector (j - 1) ∪ sector (j + 1))) ∧
        sSup ((fun z : ℂ => Real.pi * weight (j + σ) z * modulus j z *
          Real.sqrt ‖z‖ * ‖solution (j + σ) z‖) '' (sector (j - 1) ∪ sector (j + 1))) =
          secondErrorConstant := by
  sorry

end DLMF.Airy.ComplexEnvelope
