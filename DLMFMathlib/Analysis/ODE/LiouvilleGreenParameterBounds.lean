/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.ODE.ParameterDependence
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Parameter derivatives and Dirichlet eigenvalues in Liouville coordinates

Olver, *Asymptotics and Special Functions*, Chapter 6, Theorem 9.1 and
§9, pp. 214–217, synopsis O-6.12–O-6.13. All interval-end derivatives
are within the closed interval. The explicit uniqueness threshold includes the
arcsine derivative factor, rather than suppressing it in an unspecified threshold.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory Asymptotics Complex
open scoped Topology Real

namespace LiouvilleGreen.CompactInterval

/-- The real positive-weight compact-interval data of Olver's parameter theorem. -/
structure Data (a b : ℝ) where
  lower_lt_upper : a < b
  coefficient : ℝ → ℝ
  perturbation : ℝ → ℝ
  coefficient_pos : ∀ x ∈ Icc a b, 0 < coefficient x
  contDiffOn_coefficient : ContDiffOn ℝ 2 coefficient (Icc a b)
  continuousOn_perturbation : ContinuousOn perturbation (Icc a b)

namespace Data

variable {a b : ℝ}

/-- The positive fourth-root amplitude. -/
def amplitude (D : Data a b) (x : ℝ) : ℝ := D.coefficient x ^ (-(1 : ℝ) / 4)

/-- The defining amplitude. -/
theorem amplitude_def (D : Data a b) (x : ℝ) :
    D.amplitude x = D.coefficient x ^ (-(1 : ℝ) / 4) := rfl

/-- The Liouville phase with value zero at the left endpoint. -/
def phase (D : Data a b) (x : ℝ) : ℝ := ∫ t : ℝ in a..x, Real.sqrt (D.coefficient t)

/-- The defining action integral. -/
theorem phase_def (D : Data a b) (x : ℝ) :
    D.phase x = ∫ t : ℝ in a..x, Real.sqrt (D.coefficient t) := rfl

/-- The real error density with the source's one-sided endpoint derivative convention. -/
def density (D : Data a b) (x : ℝ) : ℝ :=
  D.amplitude x * iteratedDerivWithin 2 D.amplitude (Icc a b) x -
    D.perturbation x / Real.sqrt (D.coefficient x)

/-- The defining error density. -/
theorem density_def (D : Data a b) (x : ℝ) :
    D.density x = D.amplitude x * iteratedDerivWithin 2 D.amplitude (Icc a b) x -
      D.perturbation x / Real.sqrt (D.coefficient x) := rfl

/-- Variation of the error primitive from the finite left endpoint. -/
def variation (D : Data a b) (x : ℝ) : ℝ := ∫ t : ℝ in a..x, |D.density t|

/-- The defining variation integral on an increasing segment. -/
theorem variation_def (D : Data a b) (x : ℝ) :
    D.variation x = ∫ t : ℝ in a..x, |D.density t| := rfl

/-- The increasing primitive called `I` in Olver's Theorem 9.1. -/
def integratedVariation (D : Data a b) (x : ℝ) : ℝ :=
  ∫ t : ℝ in a..x, Real.sqrt (D.coefficient t) * D.variation t

/-- The defining weighted variation primitive. -/
theorem integratedVariation_def (D : Data a b) (x : ℝ) :
    D.integratedVariation x =
      ∫ t : ℝ in a..x, Real.sqrt (D.coefficient t) * D.variation t := rfl

/-- The fully explicit parameter-derivative majorant of Theorem 9.1. -/
def parameterBound (D : Data a b) (u x : ℝ) : ℝ :=
  (D.integratedVariation x / u +
    (1 + D.integratedVariation x) * D.variation x / u ^ 2) * Real.exp (D.variation x / u)

/-- The defining parameter majorant. -/
theorem parameterBound_def (D : Data a b) (u x : ℝ) :
    D.parameterBound u x = (D.integratedVariation x / u +
      (1 + D.integratedVariation x) * D.variation x / u ^ 2) *
        Real.exp (D.variation x / u) := rfl

/-- The actual oscillatory initial-value family has a jointly continuously differentiable
relative error and the explicit parameter derivative estimate. The minus family is its
complex conjugate because all coefficients are real.
Olver, Chapter 6, Theorem 9.1, synopsis O-6.12. -/
theorem exists_oscillatory_parameter_family (D : Data a b) :
    ∃ W ε : ℝ → ℝ → ℂ,
      ContDiffOn ℝ 1 (Function.uncurry ε) (Ioi 0 ×ˢ Icc a b) ∧
      (∀ u > 0,
        ContDiffOn ℝ 2 (W u) (Icc a b) ∧
        (∀ x ∈ Icc a b,
          iteratedDerivWithin 2 (W u) (Icc a b) x =
            ((-(u ^ 2 * D.coefficient x) + D.perturbation x : ℝ) : ℂ) * W u x ∧
          W u x = (D.amplitude x : ℂ) * exp (I * u * D.phase x) * (1 + ε u x) ∧
          ‖ε u x‖ ≤ Real.exp (D.variation x / u) - 1 ∧
          ‖derivWithin (ε u) (Icc a b) x‖ / (u * Real.sqrt (D.coefficient x)) ≤
            Real.exp (D.variation x / u) - 1 ∧
          ‖deriv (fun v => ε v x) u‖ ≤ D.parameterBound u x) ∧
        ε u a = 0 ∧ derivWithin (ε u) (Icc a b) a = 0) := by
  sorry

/-- Large Dirichlet frequencies retain the phase integer, have simple characteristic
zeros, and give a uniform sine approximation to their normalized eigenfunctions.
The index begins at a finite threshold; no unsupported claim about low eigenvalues is made.
Olver, Chapter 6, §9, synopsis O-6.13. -/
theorem exists_dirichlet_frequency_sequence (D : Data a b) :
    ∃ (y : ℝ → ℝ → ℝ) (frequency : ℕ → ℝ) (N : ℕ) (C : ℝ),
      0 < C ∧
      (∀ u > 0, ContDiffOn ℝ 2 (y u) (Icc a b) ∧ y u a = 0 ∧
        derivWithin (y u) (Icc a b) a = u * D.coefficient a ^ ((1 : ℝ) / 4) ∧
        ∀ x ∈ Icc a b, iteratedDerivWithin 2 (y u) (Icc a b) x =
          (-(u ^ 2 * D.coefficient x) + D.perturbation x) * y u x) ∧
      (∀ n, N ≤ n → 0 < frequency n ∧ y (frequency n) b = 0 ∧
        deriv (fun u => y u b) (frequency n) ≠ 0 ∧
        |frequency n - (n : ℝ) * π / D.phase b| ≤ C / (n : ℝ) ∧
        (∀ x ∈ Icc a b,
          |y (frequency n) x / D.amplitude x -
            Real.sin (frequency n * D.phase x)| ≤ C / frequency n)) ∧
      (∀ u, ((N : ℝ) + 1) * π / D.phase b ≤ u → y u b = 0 →
        ∃ n, N ≤ n ∧ u = frequency n) := by
  sorry

/-- The finite computable threshold for exactly one Dirichlet frequency in a prescribed
phase cell. The two majorants are the value error and the parameter error, with the
additional differentiated exponential factor retained.
Olver, Chapter 6, §9 and Theorem 9.1, synopsis O-6.12–O-6.13. -/
theorem existsUnique_dirichlet_frequency_of_threshold (D : Data a b)
    {y : ℝ → ℝ → ℝ}
    (hy : ∀ u > 0, ContDiffOn ℝ 2 (y u) (Icc a b) ∧ y u a = 0 ∧
      derivWithin (y u) (Icc a b) a = u * D.coefficient a ^ ((1 : ℝ) / 4) ∧
      ∀ x ∈ Icc a b, iteratedDerivWithin 2 (y u) (Icc a b) x =
        (-(u ^ 2 * D.coefficient x) + D.perturbation x) * y u x)
    (n : ℕ) (hn : 1 ≤ n)
    (hthreshold : ∀ u ∈
        Icc (((n : ℝ) - 1 / 2) * π / D.phase b)
          (((n : ℝ) + 1 / 2) * π / D.phase b),
      let A := Real.exp (D.variation b / u) - 1
      A < 1 ∧ (D.phase b * A + D.parameterBound u b) / Real.sqrt (1 - A ^ 2) < D.phase b) :
    ∃! u : ℝ, u ∈ Ioo (((n : ℝ) - 1 / 2) * π / D.phase b)
      (((n : ℝ) + 1 / 2) * π / D.phase b) ∧ y u b = 0 := by
  sorry

end Data
end LiouvilleGreen.CompactInterval
