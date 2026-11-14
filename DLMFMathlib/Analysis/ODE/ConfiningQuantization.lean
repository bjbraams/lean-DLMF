/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.ODE.TurningPointCoordinates
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Confining bound states and differentiated power-tail potentials

Olver, *Asymptotics and Special Functions*, Chapter 13, §9,
(9.02)–(9.04) and §9.4, pp. 497–501, synopsis O-13.06. The source proves
an additive O(1/u) action error. For a varying potential this is not automatically
O(1/n); the latter synopsis strengthening is kept for separate review.
-/

@[expose] public noncomputable section
open Filter Set MeasureTheory Asymptotics
open scoped Topology
namespace ODE.ConfiningPotential

/-- The four differentiated power-tail conditions at each infinity.
Olver, Chapter 13, (9.03)–(9.04), pp. 497–498. -/
structure HasDifferentiatedPowerTails (q : ℝ → ℝ) (k₁ α₁ k₂ α₂ : ℝ) : Prop where
  contDiff : ContDiff ℝ 3 q
  positive_constants : 0 < k₁ ∧ 0 < α₁ ∧ 0 < k₂ ∧ 0 < α₂
  positive_value : q ~[atTop] (fun x : ℝ => k₁ * x ^ α₁)
  positive_derivative : deriv q ~[atTop] (fun x : ℝ => α₁ * k₁ * x ^ (α₁ - 1))
  positive_second : iteratedDeriv 2 q =O[atTop] (fun x : ℝ => x ^ (α₁ - 2))
  positive_third : iteratedDeriv 3 q =O[atTop] (fun x : ℝ => x ^ (α₁ - 3))
  negative_value : q ~[atBot] (fun x : ℝ => k₂ * (-x) ^ α₂)
  negative_derivative : deriv q ~[atBot] (fun x : ℝ => -α₂ * k₂ * (-x) ^ (α₂ - 1))
  negative_second : iteratedDeriv 2 q =O[atBot] (fun x : ℝ => (-x) ^ (α₂ - 2))
  negative_third : iteratedDeriv 3 q =O[atBot] (fun x : ℝ => (-x) ^ (α₂ - 3))

/-- A nontrivial classical solution vanishes at both real infinities.
Olver, Chapter 13, (9.02), p. 497. -/
def IsBoundState (q : ℝ → ℝ) (u : ℝ) : Prop :=
  ∃ w : ℝ → ℝ, ContDiff ℝ 2 w ∧ w ≠ 0 ∧
    (∀ x : ℝ, iteratedDeriv 2 w x = (q x - u ^ 2) * w x) ∧
      Tendsto w atTop (𝓝 0) ∧ Tendsto w atBot (𝓝 0)

/-- The leftmost real turning root, used only at energies with two roots. -/
def leftTurningRoot (q : ℝ → ℝ) (u : ℝ) : ℝ := sInf {x | q x = u ^ 2}

/-- The rightmost real turning root, used only at energies with two roots. -/
def rightTurningRoot (q : ℝ → ℝ) (u : ℝ) : ℝ := sSup {x | q x = u ^ 2}

/-- The classical action between both turning roots. Olver, Chapter 13, §9.4. -/
def action (q : ℝ → ℝ) (u : ℝ) : ℝ :=
  ∫ x in leftTurningRoot q u..rightTurningRoot q u, Real.sqrt (u ^ 2 - q x)

/-- The removable first divided difference q(x)-q(r) over x-r. -/
def turningFactor (q : ℝ → ℝ) (r x : ℝ) : ℝ :=
  ∫ t : ℝ in 0..1, deriv q (r + t * (x - r))

/-- The actual Airy control density in the original variable, on the half-line
containing a positively oriented turning root. Olver, Chapter 13, §9.3. -/
def controlDensity (q : ℝ → ℝ) (r x : ℝ) : ℝ :=
  ‖ODE.RealTurningPoint.perturbation (turningFactor q r) (fun _ => 0) r x‖ /
    Real.sqrt |ODE.RealTurningPoint.coordinate (turningFactor q r) r x| *
      Real.sqrt (ODE.RealTurningPoint.scale (turningFactor q r) r x)

/-- The sum of the two computed half-line control variations. -/
def controlVariation (q : ℝ → ℝ) (u : ℝ) : ℝ :=
  ∫ x in Ioi (0 : ℝ), controlDensity q (rightTurningRoot q u) x +
    controlDensity (fun t => q (-t)) (-leftTurningRoot q u) x

/-- The bound-state equation and its two vanishing boundary conditions. -/
theorem isBoundState_iff (q : ℝ → ℝ) (u : ℝ) : IsBoundState q u ↔
    ∃ w : ℝ → ℝ, ContDiff ℝ 2 w ∧ w ≠ 0 ∧
      (∀ x : ℝ, iteratedDeriv 2 w x = (q x - u ^ 2) * w x) ∧
        Tendsto w atTop (𝓝 0) ∧ Tendsto w atBot (𝓝 0) := Iff.rfl

/-- The defining least turning root. -/
theorem leftTurningRoot_def (q : ℝ → ℝ) (u : ℝ) :
    leftTurningRoot q u = sInf {x | q x = u ^ 2} := rfl

/-- The defining greatest turning root. -/
theorem rightTurningRoot_def (q : ℝ → ℝ) (u : ℝ) :
    rightTurningRoot q u = sSup {x | q x = u ^ 2} := rfl

/-- The defining action integral. -/
theorem action_def (q : ℝ → ℝ) (u : ℝ) : action q u =
    ∫ x in leftTurningRoot q u..rightTurningRoot q u, Real.sqrt (u ^ 2 - q x) := rfl

/-- The defining nonsingular divided difference. -/
theorem turningFactor_def (q : ℝ → ℝ) (r x : ℝ) : turningFactor q r x =
    ∫ t : ℝ in 0..1, deriv q (r + t * (x - r)) := rfl

/-- The defining computed control density. -/
theorem controlDensity_def (q : ℝ → ℝ) (r x : ℝ) : controlDensity q r x =
    ‖ODE.RealTurningPoint.perturbation (turningFactor q r) (fun _ => 0) r x‖ /
      Real.sqrt |ODE.RealTurningPoint.coordinate (turningFactor q r) r x| *
        Real.sqrt (ODE.RealTurningPoint.scale (turningFactor q r) r x) := rfl

/-- The defining total half-line variation. -/
theorem controlVariation_def (q : ℝ → ℝ) (u : ℝ) : controlVariation q u =
    ∫ x in Ioi (0 : ℝ), controlDensity q (rightTurningRoot q u) x +
      controlDensity (fun t => q (-t)) (-leftTurningRoot q u) x := rfl

/-- Exactly two real turning roots exist at every sufficiently large energy.
Olver, Chapter 13, §9.2, pp. 497–498. -/
theorem exists_large_turning_root_spec {q : ℝ → ℝ} {k₁ α₁ k₂ α₂ : ℝ}
    (hq : HasDifferentiatedPowerTails q k₁ α₁ k₂ α₂) :
    ∃ U : ℝ, 0 < U ∧ ∀ u : ℝ, U ≤ u →
      leftTurningRoot q u < 0 ∧ 0 < rightTurningRoot q u ∧
      (∀ x : ℝ, q x = u ^ 2 ↔ x = leftTurningRoot q u ∨ x = rightTurningRoot q u) ∧
      (∀ x ∈ Ioo (leftTurningRoot q u) (rightTurningRoot q u), q x < u ^ 2) := by
  sorry

/-- Both turning-root leading equivalents. Olver, Chapter 13, §9.2, p. 498. -/
theorem turning_roots_isEquivalent {q : ℝ → ℝ} {k₁ α₁ k₂ α₂ : ℝ}
    (hq : HasDifferentiatedPowerTails q k₁ α₁ k₂ α₂) :
    leftTurningRoot q ~[atTop] (fun u : ℝ => -((u ^ 2 / k₂) ^ (1 / α₂))) ∧
      rightTurningRoot q ~[atTop] (fun u : ℝ => (u ^ 2 / k₁) ^ (1 / α₁)) := by
  sorry

/-- The source's differentiated tail assumptions make both Airy controls
integrable with total size O(1/u). Olver, Chapter 13, §9.3, pp. 498–500. -/
theorem exists_controlVariation_le {q : ℝ → ℝ} {k₁ α₁ k₂ α₂ : ℝ}
    (hq : HasDifferentiatedPowerTails q k₁ α₁ k₂ α₂) :
    ∃ C U : ℝ, 0 < C ∧ 0 < U ∧ ∀ u : ℝ, U ≤ u →
      IntegrableOn (controlDensity q (rightTurningRoot q u)) (Ioi 0) ∧
      IntegrableOn (controlDensity (fun t => q (-t)) (-leftTurningRoot q u)) (Ioi 0) ∧
      controlVariation q u ≤ C / u := by
  sorry

/-- Classical two-end decay and the L2 bound-state condition agree.
Olver, Chapter 13, §9, pp. 497–501. -/
theorem isBoundState_iff_exists_memLp {q : ℝ → ℝ} {k₁ α₁ k₂ α₂ : ℝ}
    (hq : HasDifferentiatedPowerTails q k₁ α₁ k₂ α₂) (u : ℝ) :
    IsBoundState q u ↔ ∃ w : ℝ → ℝ, ContDiff ℝ 2 w ∧ w ≠ 0 ∧
      (∀ x : ℝ, iteratedDeriv 2 w x = (q x - u ^ 2) * w x) ∧ MemLp w 2 volume := by
  sorry

/-- The large positive bound-state parameters form a simple unbounded sequence.
No assertion about the first global spectral index is built into the enumeration.
Olver, Chapter 13, §9, pp. 497–501. -/
theorem exists_boundState_enumeration {q : ℝ → ℝ} {k₁ α₁ k₂ α₂ : ℝ}
    (hq : HasDifferentiatedPowerTails q k₁ α₁ k₂ α₂) :
    ∃ U : ℝ, 0 < U ∧ ∃ u : ℕ → ℝ, StrictMono u ∧ Tendsto u atTop atTop ∧
      (∀ n : ℕ, U < u n) ∧
      ∀ v : ℝ, U < v → (IsBoundState q v ↔ ∃ n : ℕ, u n = v) := by
  sorry

/-- The source's action quantization error is O(1/u).
Olver, Chapter 13, §9.4, p. 500. The index labels the large phase sequence;
it is not assigned to the first global eigenvalue. -/
theorem exists_action_quantization_bound {q : ℝ → ℝ} {k₁ α₁ k₂ α₂ : ℝ}
    (hq : HasDifferentiatedPowerTails q k₁ α₁ k₂ α₂) :
    ∃ C U : ℝ, 0 < C ∧ 0 < U ∧ ∀ u : ℝ, U ≤ u → IsBoundState q u →
      ∃ n : ℕ, 1 ≤ n ∧ |action q u - ((n : ℝ) + 1 / 2) * Real.pi| ≤ C / u := by
  sorry

end ODE.ConfiningPotential
