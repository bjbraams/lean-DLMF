/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.ODE.ThreeReferenceLiouvilleGreen
public import DLMFMathlib.Analysis.Complex.AmplitudePhaseError
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Real connection formulas extracted from the canonical complex network

Olver, *Asymptotics and Special Functions*, Chapter 13, §§14.1–14.3,
pp. 510–513, synopsis O-13.11. The actual canonical solutions and their
source endpoint vanishing conditions are retained. Schwarz symmetry is used
only with the explicit branch and reference normalizations. Amplitude and phase
bounds reuse `Complex.exists_amplitude_phase_error`.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory ComplexConjugate
open scoped Topology Real

namespace Complex.ThreeReferenceLiouvilleGreen

/-- The actual real-symmetric geometry and the source's canonical quarter-root phases.
These are coefficient/branch normalizations, not assumptions on connection errors. -/
structure IsRealGeometry {u : ℝ} (D : Data (u : ℂ)) : Prop where
  turningPoint_eq_zero : D.turningPoint = 0
  real_mem : ∀ x : ℝ, (x : ℂ) ∈ D.domain
  conj_mem : ∀ z ∈ D.domain, conj z ∈ D.domain
  coefficient_conj : ∀ z ∈ D.domain, D.coefficient (conj z) = conj (D.coefficient z)
  perturbation_conj : ∀ z ∈ D.domain, D.perturbation (conj z) = conj (D.perturbation z)
  coefficient_sign : ∀ x : ℝ, x ≠ 0 → 0 < x * (D.coefficient x).re
  positive_mem : ∀ x : ℝ, 0 < x → (x : ℂ) ∈ D.principalDomain 0
  negative_mem : ∀ x : ℝ, x < 0 → (x : ℂ) ∈ D.branchDomain 1 ∩ D.branchDomain 2
  reference_real : ∀ t ≥ 1, (D.reference 0 t).im = 0 ∧ 0 < (D.reference 0 t).re
  reference_conj : ∀ t ≥ 1, D.reference 2 t = conj (D.reference 1 t)
  first_branch_conj : ∀ z ∈ D.branchDomain 0, conj z ∈ D.branchDomain 0 ∧
    D.sourceAmplitude 0 (conj z) = conj (D.sourceAmplitude 0 z) ∧
    D.phase 0 (conj z) = conj (D.phase 0 z)
  other_branches_conj : ∀ z ∈ D.branchDomain 1, conj z ∈ D.branchDomain 2 ∧
    D.sourceAmplitude 2 (conj z) = conj (D.sourceAmplitude 1 z) ∧
    D.phase 2 (conj z) = conj (D.phase 1 z)
  positive_amplitude : ∀ x : ℝ, 0 < x →
    D.sourceAmplitude 0 x = ((D.coefficient x).re ^ (-(1 : ℝ) / 4) : ℝ)
  positive_phase : ∀ x : ℝ, 0 < x →
    D.phase 0 x = (∫ t : ℝ in 0..x, Real.sqrt (D.coefficient t).re : ℝ)
  negative_amplitude : ∀ x : ℝ, x < 0 →
    D.sourceAmplitude 1 x = exp (-π * I / 12) * (|(D.coefficient x).re| ^ (-(1 : ℝ) / 4) : ℝ)
  negative_phase : ∀ x : ℝ, x < 0 →
    D.phase 1 x = I * (∫ t : ℝ in x..0, Real.sqrt |(D.coefficient t).re| : ℝ)

/-- The complex three-solution relation gives the exact real amplitude-two connection,
its endpoint constant, and the source sharp amplitude/phase inequalities. The vanishing
hypotheses are actual relative errors of the canonical family, as in §14.1.
Olver, Chapter 13, (14.02)–(14.10), synopsis O-13.11. -/
theorem real_connection_of_canonical_family {u : ℝ} (hu : 0 < u)
    {D : Data (u : ℂ)} (hreal : IsRealGeometry D) {W : Fin 3 → ℂ → ℂ}
    (hW : D.IsCanonicalFamily W)
    (hvanish : Tendsto (D.relativeError W 1 ∘ D.reference 2) atTop (𝓝 0))
    (hnegative : ∀ j ∈ ({1, 2} : Set (Fin 3)),
      Tendsto (fun x : ℝ => D.relativeError W j x) atBot (𝓝 0)) :
    ∃ d : ℂ,
      Tendsto (D.relativeError W 1 ∘ D.reference 0) atTop (𝓝 d) ∧
      ‖d‖ ≤ (Real.exp (D.joinVariation 1 0 / u) - 1) / 2 ∧
      (∀ x : ℝ, (W 0 x).im = 0 ∧ W 2 x = conj (W 1 x)) ∧
      (∀ x : ℝ, x < 0 →
        W 0 x = ((2 * |(D.coefficient x).re| ^ (-(1 : ℝ) / 4) : ℝ) : ℂ) *
          ((exp (I * π / 4 - I * u *
            (∫ t : ℝ in x..0, Real.sqrt |(D.coefficient t).re| : ℝ)) *
              (1 + conj d) * (1 + D.relativeError W 1 x)).re : ℝ)) ∧
      Tendsto (fun x : ℝ =>
        (W 0 x).re * |(D.coefficient x).re| ^ ((1 : ℝ) / 4) -
          2 * (exp (I * π / 4 - I * u *
            (∫ t : ℝ in x..0, Real.sqrt |(D.coefficient t).re| : ℝ)) * (1 + conj d)).re)
              atBot (𝓝 0) ∧
      (‖d‖ ≤ 1 → ∃ α δ : ℝ, 0 ≤ 1 + α ∧ |α| ≤ ‖d‖ ∧
        |δ| ≤ Real.arcsin ‖d‖ ∧ Real.arcsin ‖d‖ ≤ π * ‖d‖ / 2 ∧
        ∀ x : ℝ, x < 0 → ‖D.relativeError W 1 x‖ ≤ 1 →
          ∃ p q : ℝ, 0 ≤ 1 + p ∧ |p| ≤ ‖D.relativeError W 1 x‖ ∧
            |q| ≤ Real.arcsin ‖D.relativeError W 1 x‖ ∧
            Real.arcsin ‖D.relativeError W 1 x‖ ≤ π * ‖D.relativeError W 1 x‖ / 2 ∧
            W 0 x = ((2 * (1 + α) * (1 + p) *
              |(D.coefficient x).re| ^ (-(1 : ℝ) / 4) *
              Real.sin (u * (∫ t : ℝ in x..0, Real.sqrt |(D.coefficient t).re|) +
                π / 4 + δ + q) : ℝ) : ℂ)) := by
  sorry

/-- The selected real cosine solution has the exact growing-side relative error and
negative-side cosine phase. Its growing asymptotic alone would permit adding a recessive
solution; the definition here fixes that choice using the canonical complex solution.
Olver, Chapter 13, (14.11)–(14.13), synopsis O-13.11. -/
theorem cosine_connection_of_canonical_family {u : ℝ} (hu : 0 < u)
    {D : Data (u : ℂ)} (hreal : IsRealGeometry D) {W : Fin 3 → ℂ → ℂ}
    (hW : D.IsCanonicalFamily W)
    (hnegative : Tendsto (fun x : ℝ => D.relativeError W 1 x) atBot (𝓝 0)) :
    let C := fun x : ℝ => (exp (-π * I / 6) * W 1 x).re
    (∀ x : ℝ, 0 < x → C x = (D.coefficient x).re ^ (-(1 : ℝ) / 4) *
      Real.exp (u * (∫ t : ℝ in 0..x, Real.sqrt (D.coefficient t).re)) *
        (1 + (D.relativeError W 1 x).re)) ∧
    (∀ x : ℝ, x < 0 → ‖D.relativeError W 1 x‖ ≤ 1 → ∃ p q : ℝ,
      |p| ≤ ‖D.relativeError W 1 x‖ ∧ |q| ≤ Real.arcsin ‖D.relativeError W 1 x‖ ∧
      C x = (1 + p) * |(D.coefficient x).re| ^ (-(1 : ℝ) / 4) *
        Real.cos (u * (∫ t : ℝ in x..0, Real.sqrt |(D.coefficient t).re|) + π / 4 + q)) ∧
    Tendsto (fun x : ℝ => C x * |(D.coefficient x).re| ^ ((1 : ℝ) / 4) -
      Real.cos (u * (∫ t : ℝ in x..0, Real.sqrt |(D.coefficient t).re|) + π / 4))
        atBot (𝓝 0) := by
  sorry

end Complex.ThreeReferenceLiouvilleGreen
