/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ParabolicCylinder.Basic
public import DLMFMathlib.Analysis.ODE.ConfiningQuantization
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Exact Weber scattering and two-end bound states

Olver, *Asymptotics and Special Functions*, Chapter 13, §15,
pp. 513–516, synopsis O-13.12. Scattering coefficients are Wronskians of
actual unit-flux solutions of the modified Weber equation; their values are not
defined to be the desired logistic formulas.
-/

@[expose] public noncomputable section
open Complex Filter
open scoped Topology
namespace DLMF.Confluent.WeberScattering

/-- The unit-flux outgoing-right solution of w''=(a²-x²)w.
Olver, Chapter 13, §15, pp. 513–516. Its asymptotic phase is
x²/2-(a²/2)*log(sqrt(2)*x). -/
def outgoingRight (a x : ℝ) : ℂ :=
  ((2 : ℝ) ^ (1 / 4 : ℝ) : ℝ) * exp (Real.pi * a ^ 2 / 8 - I * Real.pi / 8) *
    parabolicCylinderU (I * a ^ 2 / 2)
      ((Real.sqrt 2 : ℂ) * exp (-I * Real.pi / 4) * x)

/-- The reflected outgoing-left solution. -/
def outgoingLeft (a x : ℝ) : ℂ := outgoingRight a (-x)

/-- The unit incoming-left solution, by conjugation of the outgoing-left one. -/
def incomingLeft (a x : ℝ) : ℂ := starRingEnd ℂ (outgoingLeft a x)

/-- The actual real-variable Wronskian. -/
def wronskian (f g : ℝ → ℂ) (x : ℝ) : ℂ := f x * deriv g x - deriv f x * g x

/-- Incoming coefficient of the actual unit outgoing solution. -/
def incomingCoefficient (a : ℝ) : ℂ :=
  wronskian (outgoingRight a) (outgoingLeft a) 0 /
    wronskian (incomingLeft a) (outgoingLeft a) 0

/-- Reflected coefficient of the actual unit outgoing solution. -/
def reflectedCoefficient (a : ℝ) : ℂ :=
  wronskian (incomingLeft a) (outgoingRight a) 0 /
    wronskian (incomingLeft a) (outgoingLeft a) 0

/-- The transmission probability from unit incoming flux. -/
def transmission (a : ℝ) : ℝ := (‖incomingCoefficient a‖ ^ 2)⁻¹

/-- The reflected probability from unit incoming flux. -/
def reflection (a : ℝ) : ℝ :=
  ‖reflectedCoefficient a‖ ^ 2 / ‖incomingCoefficient a‖ ^ 2

/-- The defining canonical outgoing solution. -/
theorem outgoingRight_def (a x : ℝ) : outgoingRight a x =
    ((2 : ℝ) ^ (1 / 4 : ℝ) : ℝ) * exp (Real.pi * a ^ 2 / 8 - I * Real.pi / 8) *
      parabolicCylinderU (I * a ^ 2 / 2)
        ((Real.sqrt 2 : ℂ) * exp (-I * Real.pi / 4) * x) := rfl

/-- The defining reflected outgoing solution. -/
theorem outgoingLeft_def (a x : ℝ) : outgoingLeft a x = outgoingRight a (-x) := rfl

/-- The defining incoming conjugate. -/
theorem incomingLeft_def (a x : ℝ) :
    incomingLeft a x = starRingEnd ℂ (outgoingLeft a x) := rfl

/-- The defining real-variable Wronskian. -/
theorem wronskian_def (f g : ℝ → ℂ) (x : ℝ) :
    wronskian f g x = f x * deriv g x - deriv f x * g x := rfl

/-- The defining incoming Wronskian quotient. -/
theorem incomingCoefficient_def (a : ℝ) : incomingCoefficient a =
    wronskian (outgoingRight a) (outgoingLeft a) 0 /
      wronskian (incomingLeft a) (outgoingLeft a) 0 := rfl

/-- The defining reflected Wronskian quotient. -/
theorem reflectedCoefficient_def (a : ℝ) : reflectedCoefficient a =
    wronskian (incomingLeft a) (outgoingRight a) 0 /
      wronskian (incomingLeft a) (outgoingLeft a) 0 := rfl

/-- The defining unit-flux transmission probability. -/
theorem transmission_def (a : ℝ) : transmission a = (‖incomingCoefficient a‖ ^ 2)⁻¹ := rfl

/-- The defining reflected probability. -/
theorem reflection_def (a : ℝ) :
    reflection a = ‖reflectedCoefficient a‖ ^ 2 / ‖incomingCoefficient a‖ ^ 2 := rfl

/-- The outgoing mode solves the actual modified Weber equation.
Olver, Chapter 13, §15, pp. 513–516. -/
theorem outgoingRight_differential_equation (a x : ℝ) :
    iteratedDeriv 2 (outgoingRight a) x = (a ^ 2 - x ^ 2 : ℝ) * outgoingRight a x := by
  sorry

/-- The outgoing mode has exactly one unit of rightward flux.
Olver, Chapter 13, §15, pp. 513–516. -/
theorem outgoingRight_flux (a x : ℝ) :
    (starRingEnd ℂ (outgoingRight a x) * deriv (outgoingRight a) x).im = 1 := by
  sorry

/-- The left basis and incoming coefficient have nonzero physical denominators.
Olver, Chapter 13, §15, pp. 513–516. -/
theorem denominators_ne_zero (a : ℝ) :
    wronskian (incomingLeft a) (outgoingLeft a) 0 ≠ 0 ∧ incomingCoefficient a ≠ 0 := by
  sorry

/-- The Wronskian coefficients give the exact global solution identity.
Olver, Chapter 13, §15, pp. 513–516. -/
theorem outgoingRight_eq_incoming_add_reflected (a x : ℝ) :
    outgoingRight a x = incomingCoefficient a * incomingLeft a x +
      reflectedCoefficient a * outgoingLeft a x := by
  sorry

/-- The modified Weber probabilities have the exact logistic values.
Olver, Chapter 13, §15, pp. 513–516. -/
theorem transmission_and_reflection {a : ℝ} (ha : 0 < a) :
    transmission a = 1 / (1 + Real.exp (Real.pi * a ^ 2)) ∧
      reflection a = 1 / (1 + Real.exp (-Real.pi * a ^ 2)) ∧
        transmission a + reflection a = 1 := by
  sorry

/-- A real Weber bound state exists precisely at an odd positive square energy.
Olver, Chapter 13, §15, pp. 513–516. -/
theorem isBoundState_iff_odd_square {a : ℝ} (ha : 0 < a) :
    ODE.ConfiningPotential.IsBoundState (fun x : ℝ => x ^ 2) a ↔
      ∃ n : ℕ, a ^ 2 = 2 * n + 1 := by
  sorry

end DLMF.Confluent.WeberScattering
