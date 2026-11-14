/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ParabolicCylinder.UniformLG2.PositiveParameterEstimates
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Computable positive-parameter parabolic-cylinder error

Olver, *Asymptotics and Special Functions*, Chapter 6, §6, pp. 206–208,
synopsis O-6.08. The normalization is `U(u/2,√(2u)t)` and the existing
positive phase `pcfXiBar`. The full real line is retained in the parameter bound.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory Asymptotics
open scoped Topology

namespace DLMF.Confluent.PositiveCylinderError

/-- The exact leading factor in Olver's scaled positive-parameter cylinder formula. -/
def leadingFactor (u t : ℝ) : ℝ :=
  2 ^ ((u - 1) / 4) * u ^ (-(u + 1) / 4) * Real.exp (u / 4) *
    CylinderUniformExpansion.posAmplitude t * Real.exp (-u * pcfXiBar t)

/-- The defining source normalization. -/
theorem leadingFactor_def (u t : ℝ) :
    leadingFactor u t = 2 ^ ((u - 1) / 4) * u ^ (-(u + 1) / 4) * Real.exp (u / 4) *
      CylinderUniformExpansion.posAmplitude t * Real.exp (-u * pcfXiBar t) := rfl

/-- The actual relative error of the canonical entire cylinder function. -/
def error (u t : ℝ) : ℂ :=
  parabolicCylinderU (u / 2) (Real.sqrt (2 * u) * t) / leadingFactor u t - 1

/-- The defining relative error. -/
theorem error_def (u t : ℝ) :
    error u t = parabolicCylinderU (u / 2) (Real.sqrt (2 * u) * t) /
      leadingFactor u t - 1 := rfl

/-- The explicit real error-control density for `f(t)=1+t²` and `g=0`. -/
def density (t : ℝ) : ℝ := (3 * t ^ 2 - 2) / (4 * (1 + t ^ 2) ^ ((5 : ℝ) / 2))

/-- The defining density formula. -/
theorem density_def (t : ℝ) :
    density t = (3 * t ^ 2 - 2) / (4 * (1 + t ^ 2) ^ ((5 : ℝ) / 2)) := rfl

/-- The actual variation from a finite real point to positive infinity. -/
def tailVariation (t : ℝ) : ℝ := ∫ s : ℝ in Ici t, |density s|

/-- The defining tail-variation integral. -/
theorem tailVariation_def (t : ℝ) :
    tailVariation t = ∫ s : ℝ in Ici t, |density s| := rfl

/-- Substitution of the fourth-root amplitude gives the displayed density.
Olver, Chapter 6, §6, synopsis O-6.08. -/
theorem amplitude_mul_secondDeriv (t : ℝ) :
    CylinderUniformExpansion.posAmplitude t *
      iteratedDeriv 2 CylinderUniformExpansion.posAmplitude t = density t := by
  sorry

/-- The variation is exactly computable on the full line and has a quadratic tail bound.
Olver, Chapter 6, §6, synopsis O-6.08. -/
theorem integrable_density_and_variation :
    Integrable density ∧
      (∫ t : ℝ, |density t|) = 4 / 3 * Real.sqrt (2 / 5) - 1 / 6 ∧
      (∀ t ≥ 1, tailVariation t ≤ 3 / (8 * t ^ 2)) := by
  sorry

/-- Both canonical relative-error components satisfy the explicit finite-variation bound
at every real point. Olver, Chapter 6, §6, synopsis O-6.08. -/
theorem norm_error_le {u : ℝ} (hu : 0 < u) (t : ℝ) :
    ‖error u t‖ ≤ Real.exp (tailVariation t / (2 * u)) - 1 ∧
      ‖deriv (error u) t‖ / (2 * u * Real.sqrt (1 + t ^ 2)) ≤
        Real.exp (tailVariation t / (2 * u)) - 1 := by
  sorry

/-- The error is uniformly `O(1/u)` on the entire real line and is `O(t⁻²)` at fixed
positive parameter. Olver, Chapter 6, §6, synopsis O-6.08. -/
theorem error_uniform_parameter_and_tail :
    (∃ C > 0, ∀ u ≥ 1, ∀ t : ℝ, ‖error u t‖ ≤ C / u) ∧
      (∀ u > 0, (error u) =O[atTop] fun t : ℝ => t ^ (-(2 : ℤ))) := by
  sorry

end DLMF.Confluent.PositiveCylinderError
