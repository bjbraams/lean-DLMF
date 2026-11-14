/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bessel.TurningPointExpansion
public import DLMF.Bessel.FourierBessel
public import DLMF.Airy.Zeros.RealAndAi
public import Mathlib.Analysis.Asymptotics.Defs

/-!
# Large-order Bessel zeros and Airy inversion

Complete increasing zero enumerations retain the first-zero indexing. The
coordinate expansions are uniform in the zero index; inversion back to the
original variable retains the derivative of that inverse. Derivative-zero
corrections are not declared analytic at zero: they have an additional reciprocal
Airy-zero term. Source: Olver, *Asymptotics and Special Functions*, Chapter 11,
§6, pp. 405–408, and §10, pp. 424–426.
-/

@[expose] public noncomputable section

open Complex Set Filter ODE
open scoped Real Topology Asymptotics

namespace DLMF.Bessel

/-- The fixed-index first three terms of a positive `J_nu` zero, including the
source's exact powers of two and the complete enumeration convention.
Olver, Chapter 11, §6, pp. 407–408. -/
theorem Real.isBigO_besselJ_fixed_zero_turningPoint
    (j : ℝ → ℕ → ℝ) (hj : ∀ ν : ℝ, 0 < ν → IsPositiveBesselZeroSequence ν (j ν)) (n : ℕ) :
    (fun ν : ℝ => j ν n - ν + DLMF.Airy.airyAiZero (n + 1) * (ν / 2) ^ (1 / 3 : ℝ) -
      (3 * DLMF.Airy.airyAiZero (n + 1) ^ 2 / 20) * (ν / 2) ^ (-1 / 3 : ℝ)) =O[atTop]
      (fun ν : ℝ => ν⁻¹) := by
  sorry

/-- All positive `J` and `Y` zeros admit the same implicit turning-point
inversion coefficients, uniformly in the zero index. The first coefficient is
exactly `-B_0`. The statement stays in the action coordinate, so it does not
assert a uniform bound for an unbounded derivative of its inverse at infinity.
Olver, Chapter 11, §10, pp. 424–426. -/
theorem TurningPoint.exists_uniform_zero_coordinate_coefficients
    {A B : ℕ → ℂ → ℂ}
    (hcoeff : IsTurningPointCoefficientSequence TurningPoint.perturbation A B
      (TurningPoint.coordinate '' slitPlane))
    (hnormal : ∀ s : ℕ, 0 < s → Tendsto (fun x : ℝ => A s x) atBot (𝓝 0))
    (j : Fin 2 → ℝ → ℕ → ℝ)
    (hpos : ∀ k ν n, 0 < ν → 0 < j k ν n)
    (hmono : ∀ k ν, 0 < ν → StrictMono (j k ν))
    (hunbounded : ∀ k ν, 0 < ν → Tendsto (j k ν) atTop atTop)
    (hzeros : ∀ (k : Fin 2) (ν x : ℝ), 0 < ν → 0 < x →
      ((if k = 0 then besselJ ν x else besselY ν x) = 0 ↔ ∃ n, j k ν n = x)) :
    ∃ Z : ℕ → ℝ → ℝ,
      (∀ s, AnalyticOnNhd ℝ (Z s) (Iic 0)) ∧
      (∀ x : ℝ, x ≤ 0 → Z 0 x = x ∧ Z 1 x = -(B 0 x).re) ∧
      ∀ N : ℕ, 0 < N → ∃ C R : ℝ, 0 < C ∧ 0 < R ∧
        ∀ (ν : ℝ) (k : Fin 2) (n : ℕ), R ≤ ν →
          let a := if k = 0 then DLMF.Airy.airyAiZero (n + 1)
            else DLMF.Airy.airyBiZero (n + 1)
          let α := a / ν ^ (2 / 3 : ℝ)
          ‖TurningPoint.coordinate (j k ν n / ν) -
            ((∑ s ∈ Finset.range N, Z s α / ν ^ (2 * s)) : ℝ)‖ ≤ C / ν ^ (2 * N) := by
  sorry

end DLMF.Bessel
