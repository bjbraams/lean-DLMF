/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.ODE.ComplexLiouvilleGreen
public import DLMFMathlib.Analysis.ODE.LiouvilleGreenSingularCoefficients
public import DLMFMathlib.Analysis.ODE.LinearODEContinuation

/-!
# The actual three-reference Liouville–Green connection network

Olver, *Asymptotics and Special Functions*, Chapter 13, §§11.2–11.4
and Exercise 11.1, pp. 504–506, synopsis O-13.08–O-13.09. Inputs are
analytic coefficient branches and actual progressive paths with common prescribed
tails. Canonical solutions, endpoint error limits, symmetry and the three-solution
identity are conclusions. No connection coefficient is postulated as input data.
-/

@[expose] public noncomputable section

open Set Filter Asymptotics
open scoped Topology Real BigOperators

namespace Complex.ThreeReferenceLiouvilleGreen

/-- Analytic three-branch geometry, actual reference infinities and progressive joins.
The quarter-root amplitudes are separately normalized by their explicit nonzero constants.
Olver, Chapter 13, §§11.1–11.3, synopsis O-13.08. -/
structure Data (u : ℂ) where
  parameter_ne_zero : u ≠ 0
  domain : Set ℂ
  isOpen_domain : IsOpen domain
  simplyConnected_domain : IsSimplyConnected domain
  coefficient : ℂ → ℂ
  perturbation : ℂ → ℂ
  analyticOnNhd_coefficient : AnalyticOnNhd ℂ coefficient domain
  analyticOnNhd_perturbation : AnalyticOnNhd ℂ perturbation domain
  turningPoint : ℂ
  turningPoint_mem : turningPoint ∈ domain
  coefficient_zero : coefficient turningPoint = 0
  coefficient_deriv_ne_zero : deriv coefficient turningPoint ≠ 0
  coefficient_ne_zero : ∀ z ∈ domain, z ≠ turningPoint → coefficient z ≠ 0
  branchDomain : Fin 3 → Set ℂ
  principalDomain : Fin 3 → Set ℂ
  isOpen_branchDomain : ∀ j, IsOpen (branchDomain j)
  simplyConnected_branchDomain : ∀ j, IsSimplyConnected (branchDomain j)
  branchDomain_subset : ∀ j, branchDomain j ⊆ domain \ {turningPoint}
  principalDomain_subset : ∀ j k, principalDomain j ⊆ branchDomain k
  amplitude : Fin 3 → ℂ → ℂ
  phase : Fin 3 → ℂ → ℂ
  control : Fin 3 → ℂ → ℂ
  multiplier : Fin 3 → ℂ
  multiplier_ne_zero : ∀ j, multiplier j ≠ 0
  branchData : ∀ j, IsComplexLiouvilleGreenData coefficient perturbation
    (amplitude j) (phase j) (control j) (branchDomain j)
  positive_phase : ∀ j z, z ∈ principalDomain j → 0 < (u * phase j z).re
  cyclic_phase : ∀ j z, z ∈ principalDomain j →
    phase (j + 1) z = -phase j z ∧ phase (j + 2) z = -phase j z
  cyclic_amplitude : ∀ j z, z ∈ principalDomain j →
    multiplier (j + 1) * amplitude (j + 1) z =
      exp (π * I / 6) * (multiplier j * amplitude j z) ∧
    multiplier (j + 2) * amplitude (j + 2) z =
      exp (-π * I / 6) * (multiplier j * amplitude j z)
  reference : Fin 3 → ℝ → ℂ
  continuousOn_reference : ∀ j, ContinuousOn (reference j) (Ici 1)
  regular_reference : ∀ j R, 1 < R → TauCeti.IsPiecewiseC1On (reference j) 1 R
  reference_mem : ∀ j t, 1 ≤ t → reference j t ∈ principalDomain j
  progressive_reference : ∀ j,
    MonotoneOn (fun t => (u * phase j (reference j t)).re) (Ici 1)
  reference_phase : ∀ j, Tendsto (fun t => (u * phase j (reference j t)).re) atTop atTop
  reference_variation : ∀ j, BoundedVariationOn (control j ∘ reference j) (Ici 1)
  join : Fin 3 → Fin 3 → ℝ → ℂ
  continuous_join : ∀ j k, j ≠ k → Continuous (join j k)
  regular_join : ∀ j k R, j ≠ k → 0 < R → TauCeti.IsPiecewiseC1On (join j k) (-R) R
  join_mem : ∀ j k t, j ≠ k → join j k t ∈ branchDomain j ∩ branchDomain k
  initial_tail : ∀ j k t, j ≠ k → t ≤ -1 → join j k t = reference j (-t)
  terminal_tail : ∀ j k t, j ≠ k → 1 ≤ t → join j k t = reference k t
  opposite_phase_join : ∀ j k t, j ≠ k → phase j (join j k t) = -phase k (join j k t)
  progressive_join : ∀ j k, j ≠ k → Monotone (fun t => -(u * phase j (join j k t)).re)
  join_variation : ∀ j k, j ≠ k → BoundedVariationOn (control j ∘ join j k) univ

namespace Data

variable {u : ℂ}

/-- The actually normalized source amplitude on the jth principal branch. -/
def sourceAmplitude (D : Data u) (j : Fin 3) (z : ℂ) : ℂ :=
  D.multiplier j * D.amplitude j z

/-- The defining nonzero constant normalization of the quarter-root branch. -/
theorem sourceAmplitude_def (D : Data u) (j : Fin 3) (z : ℂ) :
    D.sourceAmplitude j z = D.multiplier j * D.amplitude j z := rfl

/-- Actual total control variation on the prescribed pairwise progressive join. -/
def joinVariation (D : Data u) (j k : Fin 3) : ℝ :=
  (eVariationOn (D.control j ∘ D.join j k) univ).toReal

/-- The defining finite control-variation cost. -/
theorem joinVariation_def (D : Data u) (j k : Fin 3) :
    D.joinVariation j k = (eVariationOn (D.control j ∘ D.join j k) univ).toReal := rfl

/-- The actual relative error of a supplied global solution on a source branch. -/
def relativeError (D : Data u) (W : Fin 3 → ℂ → ℂ) (j : Fin 3) (z : ℂ) : ℂ :=
  W j z / (D.sourceAmplitude j z * exp (-u * D.phase j z)) - 1

/-- The defining source-relative solution error. -/
theorem relativeError_def (D : Data u) (W : Fin 3 → ℂ → ℂ) (j : Fin 3) (z : ℂ) :
    D.relativeError W j z = W j z / (D.sourceAmplitude j z * exp (-u * D.phase j z)) - 1 := rfl

/-- A supplied family is canonical when it solves the actual equation globally and its
value and normalized derivative errors vanish at the three prescribed references. -/
def IsCanonicalFamily (D : Data u) (W : Fin 3 → ℂ → ℂ) : Prop :=
  ∀ j, AnalyticOnNhd ℂ (W j) D.domain ∧
    (∀ z ∈ D.domain, deriv (deriv (W j)) z =
      (u ^ 2 * D.coefficient z + D.perturbation z) * W j z) ∧
    Tendsto (D.relativeError W j ∘ D.reference j) atTop (𝓝 0) ∧
    Tendsto (fun t => D.amplitude j (D.reference j t) ^ 2 *
      deriv (D.relativeError W j) (D.reference j t) / u) atTop (𝓝 0)

/-- The defining actual equation and endpoint normalizations. -/
theorem isCanonicalFamily_iff (D : Data u) (W : Fin 3 → ℂ → ℂ) :
    D.IsCanonicalFamily W ↔ ∀ j, AnalyticOnNhd ℂ (W j) D.domain ∧
      (∀ z ∈ D.domain, deriv (deriv (W j)) z =
        (u ^ 2 * D.coefficient z + D.perturbation z) * W j z) ∧
      Tendsto (D.relativeError W j ∘ D.reference j) atTop (𝓝 0) ∧
      Tendsto (fun t => D.amplitude j (D.reference j t) ^ 2 *
        deriv (D.relativeError W j) (D.reference j t) / u) atTop (𝓝 0) := Iff.rfl

/-- The three global analytic solutions are selected at their actual reference infinities.
All opposite endpoint limits, their symmetry, their sharp bounds and the cyclic exact
connection identity are derived together from that normalization.
Olver, Chapter 13, (11.07)–(11.15), synopsis O-13.08–O-13.09. -/
theorem exists_canonical_network (D : Data u) :
    ∃ (W ε : Fin 3 → ℂ → ℂ) (δ : Fin 3 → Fin 3 → ℂ),
      (∀ j, AnalyticOnNhd ℂ (W j) D.domain ∧
        (∀ z ∈ D.domain, deriv (deriv (W j)) z =
          (u ^ 2 * D.coefficient z + D.perturbation z) * W j z) ∧
        AnalyticOnNhd ℂ (ε j) (D.branchDomain j) ∧
        (∀ z ∈ D.branchDomain j,
          W j z = D.sourceAmplitude j z * exp (-u * D.phase j z) * (1 + ε j z)) ∧
        Tendsto (ε j ∘ D.reference j) atTop (𝓝 0) ∧
        Tendsto (fun t => D.amplitude j (D.reference j t) ^ 2 *
          deriv (ε j) (D.reference j t) / u) atTop (𝓝 0)) ∧
      (∀ j k, δ j k = δ k j ∧ δ j j = 0 ∧
        Tendsto (ε j ∘ D.reference k) atTop (𝓝 (δ j k)) ∧
        Tendsto (fun t => D.amplitude j (D.reference k t) ^ 2 *
          deriv (ε j) (D.reference k t) / u) atTop (𝓝 0) ∧
        (j ≠ k → ‖δ j k‖ ≤ (Real.exp (D.joinVariation j k / ‖u‖) - 1) / 2)) ∧
      (∀ z ∈ D.domain,
        (1 + δ 1 2) * W 0 z + exp (-2 * π * I / 3) * (1 + δ 2 0) * W 1 z +
          exp (2 * π * I / 3) * (1 + δ 0 1) * W 2 z = 0) ∧
      (∀ j (path : ℝ → ℂ), ContinuousOn path (Ioc 0 1) →
        (∀ t ∈ Ioo (0 : ℝ) 1, TauCeti.IsPiecewiseC1On path t 1) →
        (∀ t ∈ Ioc (0 : ℝ) 1, path t ∈ D.branchDomain j) →
        (∀ᶠ t : ℝ in 𝓝[>] 0, path t = D.reference j t⁻¹) →
        MonotoneOn (fun t => -(u * D.phase j (path t)).re) (Ioc 0 1) →
        BoundedVariationOn (D.control j ∘ path) (Ioc 0 1) →
        ‖ε j (path 1)‖ ≤
          Real.exp ((eVariationOn (D.control j ∘ path) (Ioc 0 1)).toReal / ‖u‖) - 1 ∧
        ‖D.amplitude j (path 1) ^ 2 * deriv (ε j) (path 1) / u‖ ≤
          Real.exp ((eVariationOn (D.control j ∘ path) (Ioc 0 1)).toReal / ‖u‖) - 1) := by
  sorry

/-- Endpoint-normalized original-variable coefficient sequences have symmetric actual
opposite-end coefficients. These are the higher normalized connection coefficients,
not unspecified constants inserted into an asymptotic formula.
Olver, Chapter 13, Exercise 11.1, p. 506, synopsis O-13.09. -/
theorem normalized_coefficient_endpoint_symmetry (D : Data u)
    {A : Fin 3 → ℕ → ℂ → ℂ}
    (hA : ∀ j, IsOriginalVariableLiouvilleGreenCoefficientSequence
      (fun z => -(D.amplitude j z ^ 2)) D.perturbation (A j) (D.branchDomain j))
    (hnorm : ∀ j n, 0 < n → Tendsto (A j n ∘ D.reference j) atTop (𝓝 0))
    (hvar : ∀ j k n, j ≠ k → BoundedVariationOn (A j n ∘ D.join j k) univ) :
    ∃ c : ℕ → Fin 3 → Fin 3 → ℂ,
      (∀ j k n, Tendsto (A j n ∘ D.reference k) atTop (𝓝 (c n j k)) ∧
        c n j k = c n k j) ∧
      (∀ j k, c 0 j k = 1) ∧ (∀ j n, 0 < n → c n j j = 0) := by
  sorry

/-- Fixed progressive geometry gives uniform large-positive-parameter connection errors
and the complete higher-order endpoint coefficient expansions. The endpoint coefficients
are actual limits of the normalized original-variable recursion and inherit pair symmetry.
Olver, Chapter 13, §11.4 and Exercise 11.1, p. 506, synopsis O-13.09. -/
theorem exists_positive_parameter_connection_expansions (D : Data 1)
    {A : Fin 3 → ℕ → ℂ → ℂ}
    (hA : ∀ j, IsOriginalVariableLiouvilleGreenCoefficientSequence
      (fun z => -(D.amplitude j z ^ 2)) D.perturbation (A j) (D.branchDomain j))
    (hnorm : ∀ j n, 0 < n → Tendsto (A j n ∘ D.reference j) atTop (𝓝 0))
    (hvar : ∀ j k n, j ≠ k → BoundedVariationOn (A j n ∘ D.join j k) univ) :
    ∃ (W : ℝ → Fin 3 → ℂ → ℂ) (δ : ℝ → Fin 3 → Fin 3 → ℂ)
        (c : ℕ → Fin 3 → Fin 3 → ℂ),
      (∀ j k n, Tendsto (A j n ∘ D.reference k) atTop (𝓝 (c n j k)) ∧
        c n j k = c n k j) ∧
      (∀ v > 0, ∀ j,
        AnalyticOnNhd ℂ (W v j) D.domain ∧
        (∀ z ∈ D.domain, deriv (deriv (W v j)) z =
          (((v : ℂ) ^ 2) * D.coefficient z + D.perturbation z) * W v j z) ∧
        (∀ k, Tendsto (fun t => W v j (D.reference k t) /
          (D.sourceAmplitude j (D.reference k t) *
            exp (-(v : ℂ) * D.phase j (D.reference k t))) - 1)
              atTop (𝓝 (δ v j k))) ∧ δ v j j = 0) ∧
      (∀ v > 0, ∀ j k, δ v j k = δ v k j ∧
        (j ≠ k → ‖δ v j k‖ ≤ (Real.exp (D.joinVariation j k / v) - 1) / 2)) ∧
      (∀ v > 0, ∀ z ∈ D.domain,
        (1 + δ v 1 2) * W v 0 z + exp (-2 * π * I / 3) * (1 + δ v 2 0) * W v 1 z +
          exp (2 * π * I / 3) * (1 + δ v 0 1) * W v 2 z = 0) ∧
      (∀ j k N, (fun v : ℝ => 1 + δ v j k -
        ∑ n ∈ Finset.range N, c n j k / (v : ℂ) ^ n)
          =O[atTop] (fun v : ℝ => v ^ (-(N : ℤ)))) := by
  sorry

/-- Any actual canonically normalized family has the same symmetric endpoint limits
and cyclic connection coefficients. This interface takes only the differential equation
and its boundary normalizations as hypotheses, never the desired delta outcomes.
Olver, Chapter 13, §11, synopsis O-13.08–O-13.09. -/
theorem IsCanonicalFamily.connection_limits {D : Data u} {W : Fin 3 → ℂ → ℂ}
    (hW : D.IsCanonicalFamily W) :
    ∃ δ : Fin 3 → Fin 3 → ℂ,
      (∀ j k, δ j k = δ k j ∧ δ j j = 0 ∧
        Tendsto (D.relativeError W j ∘ D.reference k) atTop (𝓝 (δ j k)) ∧
        (j ≠ k → ‖δ j k‖ ≤ (Real.exp (D.joinVariation j k / ‖u‖) - 1) / 2)) ∧
      ∀ z ∈ D.domain,
        (1 + δ 1 2) * W 0 z + exp (-2 * π * I / 3) * (1 + δ 2 0) * W 1 z +
          exp (2 * π * I / 3) * (1 + δ 0 1) * W 2 z = 0 := by
  sorry

end Data
end Complex.ThreeReferenceLiouvilleGreen
