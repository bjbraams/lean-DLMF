/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Quantitative zeros of a sine with a controlled additive error

Olver, *Asymptotics and Special Functions*, Chapter 6, §8, pp. 211–214,
synopsis O-6.10. The independent variable is the phase coordinate. Thus the
same statements apply to a nonlinear Liouville phase and to `u` times that phase.
-/

@[expose] public noncomputable section

open Set Filter Asymptotics
open scoped Topology Real

namespace Real

/-- A continuous sine perturbation has a zero within the exact arcsine phase bracket.
The result includes zero error and the resulting singleton bracket.
Olver, Chapter 6, §8, synopsis O-6.10. -/
theorem exists_zero_sin_add_error {ε : ℝ → ℝ} {η δ : ℝ} (n : ℤ)
    (hη : 0 ≤ η) (hη' : η < 1)
    (hε : ContinuousOn ε (Icc (n * π - δ - arcsin η) (n * π - δ + arcsin η)))
    (hbound : ∀ t ∈ Icc (n * π - δ - arcsin η) (n * π - δ + arcsin η),
      |ε t| ≤ η) :
    ∃ t ∈ Icc (n * π - δ - arcsin η) (n * π - δ + arcsin η),
      sin (t + δ) + ε t = 0 ∧ |t - (n * π - δ)| ≤ π * η / 2 := by
  sorry

/-- The phase derivative error less than `1/√2` makes the arcsine-bracket zero unique.
Olver, Chapter 6, §8, synopsis O-6.10. -/
theorem existsUnique_zero_sin_add_error {ε : ℝ → ℝ} {η δ : ℝ} (n : ℤ)
    (hη : 0 ≤ η) (hη' : η < 1 / sqrt 2)
    (hε : ContDiffOn ℝ 1 ε (Icc (n * π - δ - arcsin η) (n * π - δ + arcsin η)))
    (hbound : ∀ t ∈ Icc (n * π - δ - arcsin η) (n * π - δ + arcsin η),
      |ε t| ≤ η ∧ |derivWithin ε
        (Icc (n * π - δ - arcsin η) (n * π - δ + arcsin η)) t| ≤ η) :
    ∃! t : ℝ, t ∈ Icc (n * π - δ - arcsin η) (n * π - δ + arcsin η) ∧
      sin (t + δ) + ε t = 0 := by
  sorry

/-- A vanishing sine error and its vanishing phase derivative give exactly one zero in
every sufficiently late half-period cell, and retain the phase integer in its asymptotic
location. This specifies all sufficiently large zeros, not an arbitrary subsequence.
Olver, Chapter 6, §8, synopsis O-6.10. -/
theorem exists_sin_error_zero_sequence {ε : ℝ → ℝ} {T δ : ℝ}
    (hε : ContDiffOn ℝ 1 ε (Ici T)) (hlim : Tendsto ε atTop (𝓝 0))
    (hdlim : Tendsto (deriv ε) atTop (𝓝 0)) :
    ∃ (N : ℕ) (z : ℕ → ℝ),
      (∀ n, N ≤ n →
        z n ∈ Ioo ((n : ℝ) * π - δ - π / 2) ((n : ℝ) * π - δ + π / 2) ∧
        sin (z n + δ) + ε (z n) = 0 ∧
        (∀ t ∈ Ioo ((n : ℝ) * π - δ - π / 2) ((n : ℝ) * π - δ + π / 2),
          sin (t + δ) + ε t = 0 → t = z n)) ∧
      Tendsto (fun n => z n - ((n : ℝ) * π - δ)) atTop (𝓝 0) ∧
      (∀ t, ((N : ℝ) + 1) * π - δ ≤ t → sin (t + δ) + ε t = 0 →
        ∃ n, N ≤ n ∧ t = z n) := by
  sorry

end Real
