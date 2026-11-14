/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.ODE.GeneralWeightedVolterra
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Liouville–Green estimates with minimal real regularity

Olver, *Asymptotics and Special Functions*, Chapter 6, Theorems 2.1–3.1
and §5, pp. 193–206, synopsis O-6.02–O-6.07. Endpoints are extended real,
the positive coefficient is only twice continuously differentiable, and the
perturbation may be complex. The control primitive is fixed by its actual density.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory Complex Asymptotics ComplexConjugate
open scoped Topology

namespace LiouvilleGreen.RealInterval

/-- Positive real phase data and a continuous complex perturbation on an arbitrary
finite or improper interval. Olver, Chapter 6, §2.1, synopsis O-6.02. -/
structure Data (a b : EReal) where
  lower_lt_upper : a < b
  coefficient : ℝ → ℝ
  perturbation : ℝ → ℂ
  phase : ℝ → ℝ
  coefficient_pos : ∀ x ∈ ODE.WeightedVolterra.interval a b, 0 < coefficient x
  contDiffOn_coefficient : ContDiffOn ℝ 2 coefficient (ODE.WeightedVolterra.interval a b)
  continuousOn_perturbation : ContinuousOn perturbation (ODE.WeightedVolterra.interval a b)
  hasDerivAt_phase : ∀ x ∈ ODE.WeightedVolterra.interval a b,
    HasDerivAt phase (Real.sqrt (coefficient x)) x

namespace Data

variable {a b : EReal}

/-- The positive fourth-root amplitude. -/
def amplitude (D : Data a b) (x : ℝ) : ℝ := D.coefficient x ^ (-(1 : ℝ) / 4)

/-- The defining amplitude normalization. -/
theorem amplitude_def (D : Data a b) (x : ℝ) :
    D.amplitude x = D.coefficient x ^ (-(1 : ℝ) / 4) := rfl

/-- The derivative of the source's error-control primitive, with the complex perturbation.
Olver, (2.01), synopsis O-6.02. -/
def density (D : Data a b) (x : ℝ) : ℂ :=
  (D.amplitude x * iteratedDeriv 2 D.amplitude x : ℝ) -
    D.perturbation x / Real.sqrt (D.coefficient x)

/-- The defining error density. -/
theorem density_def (D : Data a b) (x : ℝ) :
    D.density x = (D.amplitude x * iteratedDeriv 2 D.amplitude x : ℝ) -
      D.perturbation x / Real.sqrt (D.coefficient x) := rfl

/-- The finite part of the unoriented segment from an extended reference to `x`. -/
def referenceSegment (_D : Data a b) (c : EReal) (x : ℝ) : Set ℝ :=
  {t | t ∈ ODE.WeightedVolterra.interval a b ∧
    min c (x : EReal) ≤ (t : EReal) ∧ (t : EReal) ≤ max c (x : EReal)}

/-- Membership in an endpoint-to-point integration segment. -/
theorem mem_referenceSegment_iff (D : Data a b) (c : EReal) (x t : ℝ) :
    t ∈ D.referenceSegment c x ↔ t ∈ ODE.WeightedVolterra.interval a b ∧
      min c (x : EReal) ≤ (t : EReal) ∧ (t : EReal) ≤ max c (x : EReal) := Iff.rfl

/-- The actual total variation from the selected reference. -/
def variation (D : Data a b) (c : EReal) (x : ℝ) : ℝ :=
  ∫ t : ℝ in D.referenceSegment c x, ‖D.density t‖

/-- The defining absolute-density integral. -/
theorem variation_def (D : Data a b) (c : EReal) (x : ℝ) :
    D.variation c x = ∫ t : ℝ in D.referenceSegment c x, ‖D.density t‖ := rfl

/-- The actual one-sided approach to an endpoint, or the two-sided approach to an
interior reference. -/
def approach (_D : Data a b) (c : EReal) : Filter ℝ :=
  comap (fun x : ℝ => (x : EReal)) (𝓝 c) ⊓ 𝓟 (ODE.WeightedVolterra.interval a b)

/-- The defining reference approach filter. -/
theorem approach_def (D : Data a b) (c : EReal) :
    D.approach c = comap (fun x : ℝ => (x : EReal)) (𝓝 c) ⊓
      𝓟 (ODE.WeightedVolterra.interval a b) := rfl

/-- The exponential solution normalized at the endpoint from which its phase increases.
Both error components have their source constants and tend to zero at that endpoint.
Olver, Theorem 2.1 and §5, synopsis O-6.03 and O-6.07. -/
theorem exists_exponential (D : Data a b) {u : ℝ} (hu : 0 < u) (left : Bool)
    (hF : ∀ x ∈ ODE.WeightedVolterra.interval a b,
      IntegrableOn D.density (D.referenceSegment (if left then a else b) x)) :
    ∃ w ε : ℝ → ℂ,
      ContDiffOn ℝ 2 w (ODE.WeightedVolterra.interval a b) ∧
      ContDiffOn ℝ 2 ε (ODE.WeightedVolterra.interval a b) ∧
      (∀ x ∈ ODE.WeightedVolterra.interval a b,
        iteratedDeriv 2 w x = ((u ^ 2 * D.coefficient x : ℝ) + D.perturbation x) * w x ∧
        w x = (D.amplitude x : ℂ) *
          exp ((if left then (1 : ℂ) else -1) * u * D.phase x) * (1 + ε x) ∧
        ‖ε x‖ ≤ Real.exp (D.variation (if left then a else b) x / (2 * u)) - 1 ∧
        ‖deriv ε x‖ / (2 * u * Real.sqrt (D.coefficient x)) ≤
          Real.exp (D.variation (if left then a else b) x / (2 * u)) - 1) ∧
      Tendsto ε (D.approach (if left then a else b)) (𝓝 0) ∧
      Tendsto (fun x => deriv ε x / Real.sqrt (D.coefficient x))
        (D.approach (if left then a else b)) (𝓝 0) ∧
      ((∀ x ∈ ODE.WeightedVolterra.interval a b, (D.perturbation x).im = 0) →
        ∀ x ∈ ODE.WeightedVolterra.interval a b, (w x).im = 0) := by
  sorry

/-- The two oscillatory solutions from any finite or improper reference, with conjugate
choices when the perturbation is real. Olver, Theorem 2.2, synopsis O-6.04 and O-6.07. -/
theorem exists_oscillatory_pair (D : Data a b) {u : ℝ} (hu : 0 < u)
    {c : EReal} (hc : c ∈ Icc a b)
    (hF : ∀ x ∈ ODE.WeightedVolterra.interval a b,
      IntegrableOn D.density (D.referenceSegment c x)) :
    ∃ w ε : Bool → ℝ → ℂ,
      (∀ sign, ContDiffOn ℝ 2 (w sign) (ODE.WeightedVolterra.interval a b) ∧
        ContDiffOn ℝ 2 (ε sign) (ODE.WeightedVolterra.interval a b) ∧
        (∀ x ∈ ODE.WeightedVolterra.interval a b,
          iteratedDeriv 2 (w sign) x =
            ((-(u ^ 2 * D.coefficient x) : ℝ) + D.perturbation x) * w sign x ∧
          w sign x = (D.amplitude x : ℂ) *
            exp ((if sign then I else -I) * u * D.phase x) * (1 + ε sign x) ∧
          ‖ε sign x‖ ≤ Real.exp (D.variation c x / u) - 1 ∧
          ‖deriv (ε sign) x‖ / (u * Real.sqrt (D.coefficient x)) ≤
            Real.exp (D.variation c x / u) - 1) ∧
        Tendsto (ε sign) (D.approach c) (𝓝 0) ∧
        Tendsto (fun x => deriv (ε sign) x / Real.sqrt (D.coefficient x))
          (D.approach c) (𝓝 0)) ∧
      ((∀ x ∈ ODE.WeightedVolterra.interval a b, (D.perturbation x).im = 0) →
        ∀ x ∈ ODE.WeightedVolterra.interval a b,
          w false x = conj (w true x) ∧ ε false x = conj (ε true x)) := by
  sorry

/-- Finite total error variation gives the opposite-end dominant error limit and the
vanishing normalized derivative. The solution need only satisfy the displayed exact
normal form and its original endpoint normalization.
Olver, Theorem 3.1, synopsis O-6.05. -/
theorem tendsto_exponential_error_opposite (D : Data a b) {u : ℝ} (hu : 0 < u)
    (left : Bool) (hF : IntegrableOn D.density (ODE.WeightedVolterra.interval a b))
    (hphase : Tendsto (fun x => if left then D.phase x else -D.phase x)
      (D.approach (if left then b else a)) atTop)
    {w ε : ℝ → ℂ} (hw : ContDiffOn ℝ 2 w (ODE.WeightedVolterra.interval a b))
    (hε : ContDiffOn ℝ 2 ε (ODE.WeightedVolterra.interval a b))
    (hode : ∀ x ∈ ODE.WeightedVolterra.interval a b,
      iteratedDeriv 2 w x = ((u ^ 2 * D.coefficient x : ℝ) + D.perturbation x) * w x)
    (hnorm : ∀ x ∈ ODE.WeightedVolterra.interval a b,
      w x = (D.amplitude x : ℂ) *
        exp ((if left then (1 : ℂ) else -1) * u * D.phase x) * (1 + ε x)) :
    ∃ L : ℂ, Tendsto ε (D.approach (if left then b else a)) (𝓝 L) ∧
      Tendsto (fun x => deriv ε x / Real.sqrt (D.coefficient x))
        (D.approach (if left then b else a)) (𝓝 0) := by
  sorry

end Data
end LiouvilleGreen.RealInterval
