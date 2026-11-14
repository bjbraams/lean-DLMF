/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.ODE.TurningPointCoordinates
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Two-turning-point bound states and transmission

Olver, *Asymptotics and Special Functions*, Chapter 13, §§8 and 10,
pp. 494–497 and 501–503, synopsis O-13.05 and O-13.07.
The hypotheses concern actual coefficients, action integrals and Airy control
variations. Scattering coefficients are characterized by value and derivative
limits, rather than assuming a connection formula.
-/

@[expose] public noncomputable section
open Filter Set MeasureTheory Asymptotics
open scoped Topology
namespace ODE.TwoTurningPoints

/-- The signed two-turning-point potential. Olver, Chapter 13, §8. -/
def potential (F : ℝ → ℝ) (a b x : ℝ) : ℝ := (x - a) * (x - b) * F x

/-- The positive action measured from the right turning point. -/
def rightAction (F : ℝ → ℝ) (a b x : ℝ) : ℝ :=
  ∫ t in b..x, Real.sqrt (potential F a b t)

/-- The positive action measured to the left turning point. -/
def leftAction (F : ℝ → ℝ) (a b x : ℝ) : ℝ :=
  ∫ t in x..a, Real.sqrt (potential F a b t)

/-- The positive barrier action between the two turning points. -/
def barrierAction (F : ℝ → ℝ) (a b : ℝ) : ℝ :=
  ∫ t in a..b, Real.sqrt (-potential F a b t)

/-- The computed control density for a positively oriented simple turning root. -/
def controlDensity (H : ℝ → ℝ) (g : ℝ → ℂ) (r x : ℝ) : ℝ :=
  ‖ODE.RealTurningPoint.perturbation H g r x‖ /
    Real.sqrt |ODE.RealTurningPoint.coordinate H r x| *
      Real.sqrt (ODE.RealTurningPoint.scale H r x)

/-- The coefficient, endpoint and control-variation hypotheses for two simple
turning points. Olver, Chapter 13, §§8 and 10. The left half-line is reflected
so that both controls use the positive orientation at their turning root. -/
structure IsProblem (F : ℝ → ℝ) (g : ℝ → ℂ) (a b : ℝ) : Prop where
  ordered : a < b
  factor_regular : ContDiff ℝ 2 F
  factor_positive : ∀ x : ℝ, 0 < F x
  perturbation_continuous : Continuous g
  right_action : Tendsto (rightAction F a b) atTop atTop
  left_action : Tendsto (leftAction F a b) atBot atTop
  right_control : IntegrableOn
    (controlDensity (fun x => (x - a) * F x) g b) (Ioi ((a + b) / 2))
  left_control : IntegrableOn
    (controlDensity (fun x => (x + b) * F (-x)) (fun x => g (-x)) (-a))
      (Ioi (-(a + b) / 2))

/-- A nonzero solution recessive relative to the growing comparison at both ends.
This definition remains meaningful when the recessive solution does not tend to
zero as a function. Olver, Chapter 13, §8. -/
def IsTwoEndRecessive (F : ℝ → ℝ) (g : ℝ → ℂ) (a b u : ℝ) : Prop :=
  ∃ w : ℝ → ℂ, ContDiff ℝ 2 w ∧ w ≠ 0 ∧
    (∀ x : ℝ, deriv (deriv w) x = (u ^ 2 * potential F a b x + g x) * w x) ∧
    w =o[atTop] (fun x : ℝ =>
      ((potential F a b x ^ (-1 / 4 : ℝ)) * Real.exp (u * rightAction F a b x) : ℝ)) ∧
    w =o[atBot] (fun x : ℝ =>
      ((potential F a b x ^ (-1 / 4 : ℝ)) * Real.exp (u * leftAction F a b x) : ℝ))

/-- The incoming, reflected and transmitted asymptotic data of an actual
classical solution, with unit outgoing amplitude on the right. Derivatives are
taken after removing the Liouville amplitude. Olver, Chapter 13, §10. -/
def IsScatteringState (F : ℝ → ℝ) (g : ℝ → ℂ) (a b u : ℝ)
    (y : ℝ → ℂ) (A B : ℂ) : Prop :=
  ContDiff ℝ 2 y ∧
    (∀ x : ℝ, deriv (deriv y) x = (-u ^ 2 * potential F a b x + g x) * y x) ∧
    Tendsto (fun x : ℝ => ((potential F a b x ^ (1 / 4 : ℝ) : ℝ) : ℂ) * y x -
      Complex.exp (Complex.I * u * rightAction F a b x)) atTop (𝓝 0) ∧
    Tendsto (fun x : ℝ =>
      deriv (fun t => ((potential F a b t ^ (1 / 4 : ℝ) : ℝ) : ℂ) * y t) x /
        Real.sqrt (potential F a b x) -
          Complex.I * u * Complex.exp (Complex.I * u * rightAction F a b x))
      atTop (𝓝 0) ∧
    Tendsto (fun x : ℝ => ((potential F a b x ^ (1 / 4 : ℝ) : ℝ) : ℂ) * y x -
      (A * Complex.exp (-Complex.I * u * leftAction F a b x) +
        B * Complex.exp (Complex.I * u * leftAction F a b x))) atBot (𝓝 0) ∧
    Tendsto (fun x : ℝ =>
      deriv (fun t => ((potential F a b t ^ (1 / 4 : ℝ) : ℝ) : ℂ) * y t) x /
        Real.sqrt (potential F a b x) - Complex.I * u *
          (A * Complex.exp (-Complex.I * u * leftAction F a b x) -
            B * Complex.exp (Complex.I * u * leftAction F a b x))) atBot (𝓝 0)

/-- The defining signed potential. -/
theorem potential_def (F : ℝ → ℝ) (a b x : ℝ) :
    potential F a b x = (x - a) * (x - b) * F x := rfl

/-- The defining right action. -/
theorem rightAction_def (F : ℝ → ℝ) (a b x : ℝ) : rightAction F a b x =
    ∫ t in b..x, Real.sqrt (potential F a b t) := rfl

/-- The defining left action. -/
theorem leftAction_def (F : ℝ → ℝ) (a b x : ℝ) : leftAction F a b x =
    ∫ t in x..a, Real.sqrt (potential F a b t) := rfl

/-- The defining barrier integral. -/
theorem barrierAction_def (F : ℝ → ℝ) (a b : ℝ) : barrierAction F a b =
    ∫ t in a..b, Real.sqrt (-potential F a b t) := rfl

/-- The defining Airy control density. -/
theorem controlDensity_def (H : ℝ → ℝ) (g : ℝ → ℂ) (r x : ℝ) :
    controlDensity H g r x =
      ‖ODE.RealTurningPoint.perturbation H g r x‖ /
        Real.sqrt |ODE.RealTurningPoint.coordinate H r x| *
          Real.sqrt (ODE.RealTurningPoint.scale H r x) := rfl

/-- The barrier action is strictly positive. Olver, Chapter 13, §8. -/
theorem barrierAction_pos {F : ℝ → ℝ} {g : ℝ → ℂ} {a b : ℝ}
    (h : IsProblem F g a b) : 0 < barrierAction F a b := by
  sorry

/-- Each real positive parameter has two canonically normalized recessive
solutions. Their midpoint Wronskian vanishes exactly when one solution is
recessive at both ends. Olver, Chapter 13, §8. -/
theorem exists_recessive_pair {F : ℝ → ℝ} {g : ℝ → ℂ} {a b : ℝ}
    (h : IsProblem F g a b) {u : ℝ} (hu : 0 < u) :
    ∃ R S : ℝ → ℂ, ContDiff ℝ 2 R ∧ ContDiff ℝ 2 S ∧
      (∀ x : ℝ, deriv (deriv R) x =
        (u ^ 2 * potential F a b x + g x) * R x) ∧
      (∀ x : ℝ, deriv (deriv S) x =
        (u ^ 2 * potential F a b x + g x) * S x) ∧
      Tendsto (fun x : ℝ => R x /
        (potential F a b x ^ (-1 / 4 : ℝ) *
          Real.exp (-u * rightAction F a b x) : ℝ)) atTop (𝓝 1) ∧
      Tendsto (fun x : ℝ => S x /
        (potential F a b x ^ (-1 / 4 : ℝ) *
          Real.exp (-u * leftAction F a b x) : ℝ)) atBot (𝓝 1) ∧
      (IsTwoEndRecessive F g a b u ↔
        R ((a + b) / 2) * deriv S ((a + b) / 2) -
          deriv R ((a + b) / 2) * S ((a + b) / 2) = 0) := by
  sorry

/-- The necessary quantization law for the actual two-end recessive boundary
problem, with fixed potential and O(1/n) phase error.
Olver, Chapter 13, §8, (8.05), pp. 494–497. -/
theorem exists_quantization_bound {F : ℝ → ℝ} {g : ℝ → ℂ} {a b : ℝ}
    (h : IsProblem F g a b) :
    ∃ C U : ℝ, 0 < C ∧ 0 < U ∧ ∀ u : ℝ, U ≤ u →
      IsTwoEndRecessive F g a b u → ∃ n : ℕ, 1 ≤ n ∧
        |u * barrierAction F a b - ((n : ℝ) + 1 / 2) * Real.pi| ≤ C / n := by
  sorry

/-- The physical scattering coefficients have the barrier transmission and
reflection estimates. The theorem constructs the scattering states themselves.
Olver, Chapter 13, §10, (10.05)–(10.06), pp. 501–503. -/
theorem exists_scattering_family {F : ℝ → ℝ} {g : ℝ → ℂ} {a b : ℝ}
    (h : IsProblem F g a b) :
    ∃ y : ℝ → ℝ → ℂ, ∃ A B : ℝ → ℂ, ∃ U : ℝ, 0 < U ∧
      (∀ u : ℝ, U ≤ u → IsScatteringState F g a b u (y u) (A u) (B u) ∧ A u ≠ 0) ∧
      (fun u : ℝ => Real.exp (2 * u * barrierAction F a b) / ‖A u‖ ^ 2 - 1)
        =O[atTop] (fun u : ℝ => u⁻¹) ∧
      (fun u : ℝ => ‖B u‖ ^ 2 / ‖A u‖ ^ 2 - 1)
        =O[atTop] (fun u : ℝ => u⁻¹) := by
  sorry

/-- A real perturbation conserves the exact unit flux, before taking any
large-parameter approximation. In particular T+R=1. Olver, Chapter 13,
§10.2, p. 503. -/
theorem flux_identity {F : ℝ → ℝ} {g : ℝ → ℂ} {a b u : ℝ}
    (h : IsProblem F g a b) (hg : ∀ x : ℝ, (g x).im = 0) (hu : 0 < u)
    {y : ℝ → ℂ} {A B : ℂ} (hy : IsScatteringState F g a b u y A B) :
    ‖A‖ ^ 2 - ‖B‖ ^ 2 = 1 ∧ A ≠ 0 ∧
      ‖A‖⁻¹ ^ 2 + ‖B‖ ^ 2 / ‖A‖ ^ 2 = 1 := by
  sorry

end ODE.TwoTurningPoints
