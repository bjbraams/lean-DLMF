/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Statistical.MarcumFixedOrder
public import DLMFMathlib.Analysis.Analytic.QuadraticInverse
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# The variable-order Marcum transition

Temme, *Special Functions* (1996), Chapter 11, equations (11.81)–(11.83), pages 303–305.
The saddle inverse is the analytic germ with the prescribed imaginary derivative, and the
pole-subtracted amplitude is filled by its removable limit. Thus the coefficients are actual
Taylor derivatives, including on the transition `y=x+μ`.
-/

@[expose] public noncomputable section

open Complex Filter MeasureTheory Set Finset
open scoped Real Topology

namespace DLMF.Statistical

/-- The principal phase `(t+t⁻¹)/2-βLog t`, Temme (11.81), TEM-11-19. -/
def marcumSaddlePhase (β : ℝ) (t : ℂ) : ℂ := (t + t⁻¹) / 2 - β * log t

/-- The normalized analytic inverse at the positive saddle.
Temme (11.81)–(11.82), synopsis TEM-11-19. -/
def marcumSaddleInverse (β : ℝ) : ℂ → ℂ :=
  let γ := _root_.Real.arsinh β
  quadraticInverse (marcumSaddlePhase β) (_root_.Real.exp γ)
    (I * _root_.Real.exp γ / _root_.Real.sqrt (_root_.Real.cosh γ))

/-- The signed image of the Marcum pole under the quadratic saddle coordinate.
Temme (11.82), synopsis TEM-11-19. -/
def Real.marcumPoleCoordinate (β ρ : ℝ) : ℝ :=
  let γ := _root_.Real.arsinh β
  let θ := _root_.Real.log ρ
  SignType.sign (γ - θ) * _root_.Real.sqrt
    (2 * (_root_.Real.cosh θ - _root_.Real.cosh γ + (γ - θ) * _root_.Real.sinh γ))

/-- The pole-subtracted analytic amplitude; the apparent pole is filled by a punctured limit.
Temme (11.82)–(11.83), synopsis TEM-11-19. -/
def marcumSaddleAmplitude (β ρ : ℝ) (u : ℂ) : ℂ :=
  let raw := fun v : ℂ => deriv (marcumSaddleInverse β) v / (ρ - marcumSaddleInverse β v) +
    (v - I * Real.marcumPoleCoordinate β ρ)⁻¹
  if u = I * Real.marcumPoleCoordinate β ρ then limUnder (𝓝[≠] u) raw else raw u

/-- The Taylor coefficient `c_n=f⁽ⁿ⁾(0)/(i n!)` of the explicit analytic amplitude.
Temme (11.83), synopsis TEM-11-19. -/
def marcumSaddleCoefficient (n : ℕ) (β ρ : ℝ) : ℂ :=
  iteratedDeriv n (marcumSaddleAmplitude β ρ) 0 / (I * n.factorial)

/-- The order-zero Marcum value is its one-sided order limit, not the totalized
Poisson-mixture formula at an exceptional central shape.
Temme following (11.83), synopsis TEM-11-19. -/
def Real.marcumQZeroOrder (x y : ℝ) : ℝ :=
  marcumQ 1 x y - _root_.Real.exp (-x - y) *
    (DLMF.Bessel.besselI 0 (2 * _root_.Real.sqrt (x * y))).re

/-- The defining principal phase. -/
theorem marcumSaddlePhase_def (β : ℝ) (t : ℂ) :
    marcumSaddlePhase β t = (t + t⁻¹) / 2 - β * log t := rfl

/-- The defining branch of the inverse saddle germ. -/
theorem marcumSaddleInverse_def (β : ℝ) :
    marcumSaddleInverse β =
      quadraticInverse (marcumSaddlePhase β) (_root_.Real.exp (_root_.Real.arsinh β))
        (I * _root_.Real.exp (_root_.Real.arsinh β) /
          _root_.Real.sqrt (_root_.Real.cosh (_root_.Real.arsinh β))) := rfl

/-- The defining signed pole coordinate. -/
theorem Real.marcumPoleCoordinate_def (β ρ : ℝ) :
    Real.marcumPoleCoordinate β ρ =
      SignType.sign (_root_.Real.arsinh β - _root_.Real.log ρ) * _root_.Real.sqrt
        (2 * (_root_.Real.cosh (_root_.Real.log ρ) -
          _root_.Real.cosh (_root_.Real.arsinh β) +
          (_root_.Real.arsinh β - _root_.Real.log ρ) *
            _root_.Real.sinh (_root_.Real.arsinh β))) := rfl

/-- The defining pole subtraction with its removable value. -/
theorem marcumSaddleAmplitude_def (β ρ : ℝ) (u : ℂ) :
    marcumSaddleAmplitude β ρ u =
      let raw := fun v : ℂ =>
        deriv (marcumSaddleInverse β) v / (ρ - marcumSaddleInverse β v) +
          (v - I * Real.marcumPoleCoordinate β ρ)⁻¹
      if u = I * Real.marcumPoleCoordinate β ρ then limUnder (𝓝[≠] u) raw else raw u := rfl

/-- The defining Taylor coefficient of the explicit saddle amplitude. -/
theorem marcumSaddleCoefficient_def (n : ℕ) (β ρ : ℝ) :
    marcumSaddleCoefficient n β ρ =
      iteratedDeriv n (marcumSaddleAmplitude β ρ) 0 / (I * n.factorial) := rfl

/-- The defining order-zero value. -/
theorem Real.marcumQZeroOrder_def (x y : ℝ) :
    Real.marcumQZeroOrder x y = marcumQ 1 x y - _root_.Real.exp (-x - y) *
      (DLMF.Bessel.besselI 0 (2 * _root_.Real.sqrt (x * y))).re := rfl

/-- The saddle inverse satisfies the actual phase equation and prescribed branch.
Temme (11.81)–(11.82), synopsis TEM-11-19. -/
theorem marcumSaddleInverse_spec {β : ℝ} (hβ : 0 ≤ β) :
    IsAnalyticSaddleMap (marcumSaddlePhase β) (fun u => -u ^ 2 / 2) 0
      (_root_.Real.exp (_root_.Real.arsinh β))
      (I * _root_.Real.exp (_root_.Real.arsinh β) /
        _root_.Real.sqrt (_root_.Real.cosh (_root_.Real.arsinh β)))
      (marcumSaddleInverse β) := by
  sorry

/-- The pole coordinate satisfies its defining squared equation.
Temme (11.82), synopsis TEM-11-19. -/
theorem Real.marcumPoleCoordinate_sq {β ρ : ℝ} (hβ : 0 ≤ β) (hρ : 0 < ρ) :
    Real.marcumPoleCoordinate β ρ ^ 2 / 2 =
      _root_.Real.cosh (_root_.Real.log ρ) - _root_.Real.cosh (_root_.Real.arsinh β) +
        (_root_.Real.arsinh β - _root_.Real.log ρ) * β := by
  sorry

/-- Pole subtraction is analytic, including at the transition.
Temme (11.82)–(11.83), synopsis TEM-11-19. -/
theorem analyticAt_marcumSaddleAmplitude {β ρ : ℝ} (hβ : 0 ≤ β) (hρ : 0 < ρ) :
    AnalyticAt ℂ (marcumSaddleAmplitude β ρ) 0 := by
  sorry

/-- The even Taylor coefficients in the real Marcum expansion are real.
Temme (11.83), synopsis TEM-11-19. -/
theorem im_marcumSaddleCoefficient_even (n : ℕ) {β ρ : ℝ}
    (hβ : 0 ≤ β) (hρ : 0 < ρ) : (marcumSaddleCoefficient (2 * n) β ρ).im = 0 := by
  sorry

/-- The order-zero endpoint is the one-sided continuous order limit.
Temme following (11.83), synopsis TEM-11-19. -/
theorem Real.tendsto_marcumQ_zero_order {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Tendsto (fun μ : ℝ => marcumQ μ x y) (𝓝[>] 0) (𝓝 (Real.marcumQZeroOrder x y)) := by
  sorry

/-- The transition is exactly `y=x+μ`, Temme (11.82), synopsis TEM-11-19. -/
theorem Real.marcumPoleCoordinate_eq_zero_iff {μ x y : ℝ}
    (hμ : 0 ≤ μ) (hx : 0 < x) (hy : 0 < y) :
    Real.marcumPoleCoordinate (μ / Real.marcumXi x y) (Real.marcumRho x y) = 0 ↔
      y = x + μ := by
  sorry

/-- The complete Marcum expansion is uniform in nonnegative order and on compact positive
ratio intervals. The zero-order value is the one-sided order limit.
Temme (11.83), pages 303–305, synopsis TEM-11-19. -/
theorem exists_marcumQ_variable_order_uniform_remainder (N : ℕ) {B : ℝ} (hB : 0 < B) :
    ∃ C R : ℝ, 0 < C ∧ 0 < R ∧ ∀ ξ μ ρ : ℝ,
      R ≤ ξ → 0 ≤ μ → 0 < ρ → |(_root_.Real.log ρ)| ≤ B →
      let x := ξ / (2 * ρ)
      let y := ξ * ρ / 2
      let β := μ / ξ
      let u₀ := Real.marcumPoleCoordinate β ρ
      ‖((if μ = 0 then Real.marcumQZeroOrder x y else marcumQ μ x y : ℝ) : ℂ) -
        DLMF.Confluent.erfc (-u₀ * _root_.Real.sqrt (ξ / 2)) / 2 -
        (_root_.Real.exp (-ξ * u₀ ^ 2 / 2) /
          _root_.Real.sqrt (2 * π * ξ) : ℝ) *
          ∑ n ∈ range N, ((2 * n - 1).doubleFactorial : ℂ) *
            marcumSaddleCoefficient (2 * n) β ρ / (ξ : ℂ) ^ n‖ ≤
        C * _root_.Real.exp (-ξ * u₀ ^ 2 / 2) * ξ ^ (-(N : ℝ) - 1 / 2) := by
  sorry

end DLMF.Statistical
