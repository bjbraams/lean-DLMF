/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AsymptoticApproximations.ODE.Singularities
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Literal rank-one normalization, differentiated expansions and analytic parameters

Olver, *Asymptotics and Special Functions*, Chapter 7, Theorems 2.1–3.1,
pp. 232–237, synopsis O-7.02–O-7.04. The source normalizer is `exp(λz)z^μ`,
with the actual unwrapped logarithm of `z`. The argument used to orient the sectors
is not inserted into that power normalizer.
-/

@[expose] public noncomputable section

open Set Filter Complex Asymptotics
open scoped Topology Real BigOperators

namespace DLMF.AsymptoticApproximations.RankOne

/-- The source's enlarged canonical sector, with the second solution centered one
half-turn later on the same logarithmic cover. -/
def canonicalSector (lam₁ lam₂ : ℂ) (first : Bool) (δ : ℝ) : Filter ℂ :=
  if first then logSectorFilter (-(3 * π / 2) + δ) (3 * π / 2 - δ) (log (lam₂ - lam₁))
  else logSectorFilter (-(π / 2) + δ) (5 * π / 2 - δ) (log (lam₂ - lam₁))

/-- The actual unwrapped canonical-sector filters. -/
theorem canonicalSector_def (lam₁ lam₂ : ℂ) (first : Bool) (δ : ℝ) :
    canonicalSector lam₁ lam₂ first δ =
      if first then logSectorFilter (-(3 * π / 2) + δ) (3 * π / 2 - δ) (log (lam₂ - lam₁))
      else logSectorFilter (-(π / 2) + δ) (5 * π / 2 - δ) (log (lam₂ - lam₁)) := rfl

/-- The canonical solutions in the literal source normalization, their first two
termwise differentiated expansions, and uniqueness on the full widened sectors.
The factor `exp(j*w)` converts logarithmic-coordinate derivatives into ordinary
argument derivative orders without discarding the case `λ=0`.
Olver, Theorems 2.1–2.2, synopsis O-7.02–O-7.03. -/
theorem exists_unique_differentiated_solutions {p q : ℂ → ℂ} {pc qc : ℕ → ℂ}
    {R : ℝ} {lam₁ lam₂ : ℂ} (h : IsRankOneAtInfinity p q pc qc R lam₁ lam₂) :
    ∃ W : Bool → ℂ → ℂ,
      (∀ first, IsLogPlaneSolutionOn p q (W first) (logExterior R)) ∧
      (∀ first δ, 0 < δ → δ < π →
        let lam := if first then lam₁ else lam₂
        let μ := rankOneExponent pc qc lam
        HasAsymptoticExpansion (canonicalSector lam₁ lam₂ first δ)
          (rankOneScale lam μ 0) (rankOneCoeff pc qc lam) (W first) ∧
        (∀ (N j : ℕ), j ≤ 2 →
          (fun w => iteratedDeriv j (fun v => W first v -
            ∑ n ∈ Finset.range N, rankOneCoeff pc qc lam n * rankOneScale lam μ 0 n v) w)
            =O[canonicalSector lam₁ lam₂ first δ]
              (fun w => rankOneScale lam μ 0 N w * exp ((j : ℂ) * w))) ∧
        (∀ V, IsLogPlaneSolutionOn p q V (logExterior R) →
          HasAsymptoticExpansion (canonicalSector lam₁ lam₂ first δ)
            (rankOneScale lam μ 0) (rankOneCoeff pc qc lam) V →
          EqOn V (W first) (logExterior R))) := by
  sorry

/-- Holomorphic Laurent coefficient families with fixed distinct characteristic roots
and actual common convergent majorants on every compact parameter set.
Olver, Theorem 3.1, synopsis O-7.04. -/
structure ParameterData (U : Set ℂ) where
  isOpen : IsOpen U
  coefficient : ℂ → ℂ → ℂ
  perturbation : ℂ → ℂ → ℂ
  coefficientSeries : ℂ → ℕ → ℂ
  perturbationSeries : ℂ → ℕ → ℂ
  firstRoot : ℂ
  secondRoot : ℂ
  constantCoefficient : ℂ
  constantPerturbation : ℂ
  roots_ne : firstRoot ≠ secondRoot
  roots_sum : firstRoot + secondRoot = -constantCoefficient
  roots_mul : firstRoot * secondRoot = constantPerturbation
  leading_coefficient : ∀ u ∈ U, coefficientSeries u 0 = constantCoefficient
  leading_perturbation : ∀ u ∈ U, perturbationSeries u 0 = constantPerturbation
  analyticOnNhd_coefficientSeries : ∀ n, AnalyticOnNhd ℂ (fun u => coefficientSeries u n) U
  analyticOnNhd_perturbationSeries : ∀ n,
    AnalyticOnNhd ℂ (fun u => perturbationSeries u n) U
  compact_majorant : ∀ K : Set ℂ, IsCompact K → K ⊆ U →
    ∃ R M : ℝ, 0 < R ∧ 0 < M ∧ ∀ u ∈ K,
      (∀ n, ‖coefficientSeries u n‖ ≤ M * R ^ n ∧
        ‖perturbationSeries u n‖ ≤ M * R ^ n) ∧
      (∀ z : ℂ, R < ‖z‖ →
        HasSum (fun n => coefficientSeries u n / z ^ n) (coefficient u z) ∧
        HasSum (fun n => perturbationSeries u n / z ^ n) (perturbation u z))

/-- All exponents and recursive coefficients depend holomorphically on the parameter.
Olver, Chapter 7, Theorem 3.1, synopsis O-7.04. -/
theorem ParameterData.analyticOnNhd_exponent_coeff {U : Set ℂ} (D : ParameterData U) :
    ∀ first : Bool,
      let lam := if first then D.firstRoot else D.secondRoot
      AnalyticOnNhd ℂ (fun u => rankOneExponent
        (D.coefficientSeries u) (D.perturbationSeries u) lam) U ∧
      ∀ n, AnalyticOnNhd ℂ (fun u => rankOneCoeff
        (D.coefficientSeries u) (D.perturbationSeries u) lam n) U := by
  sorry

/-- Canonical-at-infinity solutions are jointly analytic locally in the parameter and
on the entire lifted exterior. Every differentiated remainder is locally uniform in
the parameter with the actual varying exponent and multiplier.
Olver, Chapter 7, Theorem 3.1, synopsis O-7.04. -/
theorem ParameterData.exists_analytic_canonical_family {U : Set ℂ} (D : ParameterData U)
    {multiplier : ℂ → ℂ} (hm : AnalyticOnNhd ℂ multiplier U) {u₀ : ℂ} (hu₀ : u₀ ∈ U) :
    ∃ (V : Set ℂ) (R : ℝ) (W : Bool → ℂ → ℂ → ℂ),
      IsOpen V ∧ u₀ ∈ V ∧ V ⊆ U ∧ 0 < R ∧
      (∀ first, AnalyticOnNhd ℂ (Function.uncurry (W first)) (V ×ˢ logExterior R)) ∧
      (∀ first u, u ∈ V →
        IsLogPlaneSolutionOn (D.coefficient u) (D.perturbation u) (W first u)
          (logExterior R)) ∧
      (∀ first j w, j ≤ 2 → w ∈ logExterior R →
        AnalyticOnNhd ℂ (fun u => iteratedDeriv j (W first u) w) V) ∧
      (∀ first (K : Set ℂ), IsCompact K → K ⊆ V → ∀ δ, 0 < δ → δ < π →
        let lam := if first then D.firstRoot else D.secondRoot
        let μ := fun u => rankOneExponent (D.coefficientSeries u) (D.perturbationSeries u) lam
        ∀ (N j : ℕ), j ≤ 2 →
          (fun uw : ℂ × ℂ => iteratedDeriv j (fun v => W first uw.1 v -
            ∑ n ∈ Finset.range N,
              multiplier uw.1 * rankOneCoeff (D.coefficientSeries uw.1)
                (D.perturbationSeries uw.1) lam n * rankOneScale lam (μ uw.1) 0 n v) uw.2)
            =O[𝓟 K ×ˢ canonicalSector D.firstRoot D.secondRoot first δ]
              (fun uw : ℂ × ℂ => rankOneScale lam (μ uw.1) 0 N uw.2 * exp ((j : ℂ) * uw.2))) := by
  sorry

end DLMF.AsymptoticApproximations.RankOne
