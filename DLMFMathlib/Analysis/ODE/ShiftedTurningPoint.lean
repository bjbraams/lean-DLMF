/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.ODE.TurningPointCoefficients
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Formal Airy expansions with a displaced argument

The two formal residuals are explicit power series in `h=1/u`, with coefficients
analytic functions of the turning-point variable. Their vanishing is the triangular
coefficient algorithm after using the Airy equation. This formal construction does
not assert a uniform asymptotic remainder theorem.
Source: Olver, *Asymptotics and Special Functions*, Chapter 11,
§11, (11.01)–(11.08), pp. 426–429.
-/

@[expose] public noncomputable section

open Set

namespace ODE

/-- The removable displacement `Phi=(1/2)*integral_0^1 t^(-1/2)*phi(t*z) dt`.
Olver, Chapter 11, (11.03), p. 427. -/
def turningPointDisplacement (φ : ℂ → ℂ) (z : ℂ) : ℂ :=
  MeasureTheory.weightedRayPrimitive (-1 / 2) φ z / 2

/-- The defining weighted integral of the displacement. -/
theorem turningPointDisplacement_def (φ : ℂ → ℂ) (z : ℂ) :
    turningPointDisplacement φ z = MeasureTheory.weightedRayPrimitive (-1 / 2) φ z / 2 := rfl

/-- The displacement is analytic, including zero, and solves the exact linear
normalizing equation. Olver, Chapter 11, (11.03), p. 427. -/
theorem analytic_turningPointDisplacement {D : Set ℂ} (hD : IsOpen D)
    (hstar : StarConvex ℝ 0 D) (hzero : 0 ∈ D) {φ : ℂ → ℂ}
    (hφ : AnalyticOnNhd ℂ φ D) :
    AnalyticOnNhd ℂ (turningPointDisplacement φ) D ∧
      ∀ z ∈ D, turningPointDisplacement φ z + 2 * z * deriv (turningPointDisplacement φ) z =
        φ z := by
  sorry

/-- Differentiation of each analytic-function coefficient of a formal series.
No differentiation of the formal parameter is involved. -/
def coefficientDerivative (S : PowerSeries (ℂ → ℂ)) : PowerSeries (ℂ → ℂ) :=
  PowerSeries.mk fun n => deriv (PowerSeries.coeff n S)

/-- Coefficient extraction commutes with coefficient differentiation. -/
@[simp] theorem coeff_coefficientDerivative (S : PowerSeries (ℂ → ℂ)) (n : ℕ) :
    PowerSeries.coeff n (coefficientDerivative S) = deriv (PowerSeries.coeff n S) := by
  simp [coefficientDerivative]

/-- The two formal residuals after substituting
`C(u^(2/3)*(z+Phi/u))*A + u^(-4/3)*C'(...)*B` and eliminating `C''`.
The second residual is divided by its harmless factor `u^(8/3)`.
Here `h=1/u`, `S=z+h*Phi`, `T=1+h*Phi'`, and
`Delta=2*Phi*Phi'+z*Phi'^2+h*Phi*Phi'^2-psi`.
Olver, Chapter 11, §11, pp. 427–429. -/
def shiftedTurningPointResiduals (Φ : ℂ → ℂ) (ψ A B : PowerSeries (ℂ → ℂ)) :
    PowerSeries (ℂ → ℂ) × PowerSeries (ℂ → ℂ) :=
  let S := PowerSeries.C id + PowerSeries.X * PowerSeries.C Φ
  let T := 1 + PowerSeries.X * PowerSeries.C (deriv Φ)
  let Δ := PowerSeries.C (fun z => 2 * Φ z * deriv Φ z + z * deriv Φ z ^ 2) +
    PowerSeries.X * PowerSeries.C (fun z => Φ z * deriv Φ z ^ 2) - ψ
  (coefficientDerivative (coefficientDerivative A) + Δ * A +
    (T ^ 2 + PowerSeries.X * S * PowerSeries.C (deriv (deriv Φ))) * B +
    2 * S * T * coefficientDerivative B,
    2 * T * coefficientDerivative A + PowerSeries.X * PowerSeries.C (deriv (deriv Φ)) * A +
      PowerSeries.X ^ 2 * (coefficientDerivative (coefficientDerivative B) + Δ * B))

/-- The formal residuals are the explicitly specified polynomial differential
expressions in the displacement and coefficient series. -/
theorem shiftedTurningPointResiduals_def (Φ : ℂ → ℂ)
    (ψ A B : PowerSeries (ℂ → ℂ)) : shiftedTurningPointResiduals Φ ψ A B =
    let S := PowerSeries.C id + PowerSeries.X * PowerSeries.C Φ
    let T := 1 + PowerSeries.X * PowerSeries.C (deriv Φ)
    let Δ := PowerSeries.C (fun z => 2 * Φ z * deriv Φ z + z * deriv Φ z ^ 2) +
      PowerSeries.X * PowerSeries.C (fun z => Φ z * deriv Φ z ^ 2) - ψ
    (coefficientDerivative (coefficientDerivative A) + Δ * A +
      (T ^ 2 + PowerSeries.X * S * PowerSeries.C (deriv (deriv Φ))) * B +
      2 * S * T * coefficientDerivative B,
      2 * T * coefficientDerivative A + PowerSeries.X * PowerSeries.C (deriv (deriv Φ)) * A +
        PowerSeries.X ^ 2 * (coefficientDerivative (coefficientDerivative B) + Δ * B)) := rfl

/-- Every prescribed sequence of integration constants is realized by analytic
formal coefficients. At each order the first residual determines `B_s` through
`2*z*B_s'+B_s`, and the second determines `A_(s+1)'`; the removable weighted
primitive fixes the former uniquely. The equations are asserted coefficientwise
on the analytic domain, so the totalization outside it is irrelevant.
Olver, Chapter 11, §11, pp. 427–429. -/
theorem exists_shiftedTurningPoint_formal_coefficients {D : Set ℂ}
    (hD : IsOpen D) (hsc : IsSimplyConnected D) (hzero : 0 ∈ D)
    {φ Φ : ℂ → ℂ} {ψ : ℕ → ℂ → ℂ}
    (hφ : AnalyticOnNhd ℂ φ D) (hΦ : AnalyticOnNhd ℂ Φ D)
    (hdisplacement : ∀ z ∈ D, Φ z + 2 * z * deriv Φ z = φ z)
    (hψ : ∀ n, AnalyticOnNhd ℂ (ψ n) D) (c : ℕ → ℂ) (hc : c 0 = 1) :
    ∃ A B : ℕ → ℂ → ℂ,
      (∀ n, AnalyticOnNhd ℂ (A n) D ∧ AnalyticOnNhd ℂ (B n) D) ∧
      (∀ z ∈ D, A 0 z = 1) ∧ (∀ n, A n 0 = c n) ∧
      ∀ n z, z ∈ D →
        PowerSeries.coeff n (shiftedTurningPointResiduals Φ
          (PowerSeries.mk ψ) (PowerSeries.mk A) (PowerSeries.mk B)).1 z = 0 ∧
        PowerSeries.coeff n (shiftedTurningPointResiduals Φ
          (PowerSeries.mk ψ) (PowerSeries.mk A) (PowerSeries.mk B)).2 z = 0 := by
  sorry

end ODE
