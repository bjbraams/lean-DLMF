/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.ODE.LinearODEContinuation
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Circuit monodromy of a scalar second-order differential equation

Olver, *Asymptotics and Special Functions*, Chapter 13, §2,
pp. 480–482, synopsis O-13.01. The logarithmic universal cover makes an
actual positive circuit the translation w -> w+2*pi*i. Single-valued analytic
coefficients on the punctured disc are essential hypotheses.
-/

@[expose] public noncomputable section
open Set Matrix Polynomial
namespace Complex.CircuitMonodromy

/-- The universal cover of a punctured disc of radius R. -/
def logDomain (R : ℝ) : Set ℂ := {w | Real.exp w.re < R}

/-- The lifted differential equation for y(w)=Y(exp(w)).
Olver, Chapter 13, §2, pp. 480–482. -/
def IsLiftedSolution (p q : ℂ → ℂ) (R : ℝ) (y : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ y (logDomain R) ∧ ∀ w ∈ logDomain R,
    iteratedDeriv 2 y w + (exp w * p (exp w) - 1) * deriv y w +
      exp (2 * w) * q (exp w) * y w = 0

/-- The fundamental matrix has solution columns and logarithmic derivatives. -/
def fundamentalMatrix (F : Fin 2 → ℂ → ℂ) (w : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![F 0 w, F 1 w; deriv (F 0) w, deriv (F 1) w]

/-- The actual one-circuit change matrix in the basis at w0.
Olver, Chapter 13, §2. Applications require a nonzero fundamental determinant. -/
def circuitMatrix (F : Fin 2 → ℂ → ℂ) (w₀ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (fundamentalMatrix F w₀)⁻¹ * fundamentalMatrix F (w₀ + 2 * Real.pi * I)

/-- Membership in the logarithmic covering domain. -/
theorem mem_logDomain_iff (R : ℝ) (w : ℂ) : w ∈ logDomain R ↔ Real.exp w.re < R := Iff.rfl

/-- The defining lifted equation and analyticity condition. -/
theorem isLiftedSolution_iff (p q : ℂ → ℂ) (R : ℝ) (y : ℂ → ℂ) :
    IsLiftedSolution p q R y ↔ AnalyticOnNhd ℂ y (logDomain R) ∧
      ∀ w ∈ logDomain R, iteratedDeriv 2 y w +
        (exp w * p (exp w) - 1) * deriv y w + exp (2 * w) * q (exp w) * y w = 0 := Iff.rfl

/-- The defining solution-jet matrix. -/
theorem fundamentalMatrix_def (F : Fin 2 → ℂ → ℂ) (w : ℂ) :
    fundamentalMatrix F w = !![F 0 w, F 1 w; deriv (F 0) w, deriv (F 1) w] := rfl

/-- The defining positive-circuit change matrix. -/
theorem circuitMatrix_def (F : Fin 2 → ℂ → ℂ) (w₀ : ℂ) : circuitMatrix F w₀ =
    (fundamentalMatrix F w₀)⁻¹ * fundamentalMatrix F (w₀ + 2 * Real.pi * I) := rfl

/-- Every ordinary solution germ on a punctured disc has a normalized
fundamental continuation to its logarithmic cover. Olver, Chapter 13, §2. -/
theorem exists_normalized_lifted_basis {R : ℝ} (hR : 0 < R) {p q : ℂ → ℂ}
    (hp : AnalyticOnNhd ℂ p (Metric.ball 0 R \ {0}))
    (hq : AnalyticOnNhd ℂ q (Metric.ball 0 R \ {0}))
    {w₀ : ℂ} (hw₀ : w₀ ∈ logDomain R) :
    ∃ F : Fin 2 → ℂ → ℂ, (∀ j, IsLiftedSolution p q R (F j)) ∧
      fundamentalMatrix F w₀ = 1 ∧
      ∀ w ∈ logDomain R, (fundamentalMatrix F w).det ≠ 0 := by
  sorry

/-- The actual circuit matrix is invertible and represents every integer
continuation. The domain Multiplicative Z records addition of circuit numbers.
Olver, Chapter 13, §2, pp. 480–482. -/
theorem exists_circuit_representation {R : ℝ} (hR : 0 < R) {p q : ℂ → ℂ}
    (hp : AnalyticOnNhd ℂ p (Metric.ball 0 R \ {0}))
    (hq : AnalyticOnNhd ℂ q (Metric.ball 0 R \ {0}))
    {F : Fin 2 → ℂ → ℂ} (hF : ∀ j, IsLiftedSolution p q R (F j))
    {w₀ : ℂ} (hw₀ : w₀ ∈ logDomain R) (hdet : (fundamentalMatrix F w₀).det ≠ 0) :
    ∃ ρ : Multiplicative ℤ →* GeneralLinearGroup (Fin 2) ℂ,
      (ρ (Multiplicative.ofAdd 1) : Matrix (Fin 2) (Fin 2) ℂ) = circuitMatrix F w₀ ∧
      ∀ m : ℤ, ∀ w ∈ logDomain R,
        fundamentalMatrix F (w + 2 * Real.pi * I * m) =
          fundamentalMatrix F w * (ρ (Multiplicative.ofAdd m) : Matrix (Fin 2) (Fin 2) ℂ) := by
  sorry

/-- Changing the actual solution basis conjugates its circuit matrix.
Olver, Chapter 13, §2, pp. 480–482. -/
theorem circuitMatrix_change_basis {F G : Fin 2 → ℂ → ℂ} {A : Matrix (Fin 2) (Fin 2) ℂ}
    (hG : ∀ w, fundamentalMatrix G w = fundamentalMatrix F w * A) (w₀ : ℂ) :
    circuitMatrix G w₀ = A⁻¹ * circuitMatrix F w₀ * A := by
  simp only [circuitMatrix, hG, Matrix.mul_inv_rev, Matrix.mul_assoc]

/-- Cayley–Hamilton applied to actual continuation gives the second-circuit
identity for every solution, not merely for the two basis vectors.
Olver, Chapter 13, §2, pp. 480–482. -/
theorem liftedSolution_second_circuit {R : ℝ} (hR : 0 < R) {p q : ℂ → ℂ}
    (hp : AnalyticOnNhd ℂ p (Metric.ball 0 R \ {0}))
    (hq : AnalyticOnNhd ℂ q (Metric.ball 0 R \ {0}))
    {F : Fin 2 → ℂ → ℂ} (hF : ∀ j, IsLiftedSolution p q R (F j))
    {w₀ : ℂ} (hw₀ : w₀ ∈ logDomain R) (hdet : (fundamentalMatrix F w₀).det ≠ 0)
    {y : ℂ → ℂ} (hy : IsLiftedSolution p q R y) {w : ℂ} (hw : w ∈ logDomain R) :
    y (w + 4 * Real.pi * I) - (circuitMatrix F w₀).trace * y (w + 2 * Real.pi * I) +
      (circuitMatrix F w₀).det * y w = 0 := by
  sorry

/-- Regular-singular nonresonant circuit eigenvalues are the exponentials of
the indicial roots. Olver, Chapter 13, §2, pp. 480–482. -/
theorem exists_regularSingular_diagonalization {R : ℝ} (hR : 0 < R) {P Q : ℂ → ℂ}
    (hP : AnalyticOnNhd ℂ P (Metric.ball 0 R))
    (hQ : AnalyticOnNhd ℂ Q (Metric.ball 0 R))
    {α β : ℂ} (hα : α * (α - 1) + P 0 * α + Q 0 = 0)
    (hβ : β * (β - 1) + P 0 * β + Q 0 = 0)
    (hres : ∀ m : ℤ, α - β ≠ (m : ℂ))
    {F : Fin 2 → ℂ → ℂ}
    (hF : ∀ j, IsLiftedSolution (fun z => P z / z) (fun z => Q z / z ^ 2) R (F j))
    {w₀ : ℂ} (hw₀ : w₀ ∈ logDomain R) (hdet : (fundamentalMatrix F w₀).det ≠ 0) :
    ∃ B : Matrix (Fin 2) (Fin 2) ℂ, B.det ≠ 0 ∧ circuitMatrix F w₀ =
      B * diagonal ![exp (2 * Real.pi * I * α), exp (2 * Real.pi * I * β)] * B⁻¹ := by
  sorry

/-- At resonance the logarithmic Frobenius contribution gives a triangular
circuit block. Olver, Chapter 13, §2, pp. 480–482. -/
theorem exists_regularSingular_resonant_triangularization {R : ℝ} (hR : 0 < R)
    {P Q : ℂ → ℂ} (hP : AnalyticOnNhd ℂ P (Metric.ball 0 R))
    (hQ : AnalyticOnNhd ℂ Q (Metric.ball 0 R))
    {α β : ℂ} (hα : α * (α - 1) + P 0 * α + Q 0 = 0)
    (hβ : β * (β - 1) + P 0 * β + Q 0 = 0)
    (hroots : α + β = 1 - P 0) (hres : ∃ m : ℤ, α - β = m)
    {F : Fin 2 → ℂ → ℂ}
    (hF : ∀ j, IsLiftedSolution (fun z => P z / z) (fun z => Q z / z ^ 2) R (F j))
    {w₀ : ℂ} (hw₀ : w₀ ∈ logDomain R) (hdet : (fundamentalMatrix F w₀).det ≠ 0) :
    ∃ B : Matrix (Fin 2) (Fin 2) ℂ, ∃ κ : ℂ, B.det ≠ 0 ∧ circuitMatrix F w₀ =
      B * !![exp (2 * Real.pi * I * α), κ; 0, exp (2 * Real.pi * I * α)] * B⁻¹ := by
  sorry

end Complex.CircuitMonodromy
