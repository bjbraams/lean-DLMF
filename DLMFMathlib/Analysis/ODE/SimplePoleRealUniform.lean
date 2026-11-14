/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.ODE.SimplePoleCoefficients
public import Mathlib.Analysis.BoundedVariation
public import Mathlib.Analysis.Asymptotics.Defs

/-!
# Real simple-pole coefficient dependence and convergent tails

Continuous order dependence gives local uniformity on compact order intervals.
Differentiated decay at either real infinity gives the finite coefficient limits
and weighted variations needed by the endpoint error theorem.
Source: Olver, *Asymptotics and Special Functions*, Chapter 12,
§5, pp. 447–448, together with the differentiated-tail criterion of Chapter11 §7.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology Asymptotics

namespace ODE

/-- The first derivative-series coefficient after removing the known Frobenius
power: `C_0=A_0`, `C_(s+1)=A_(s+1)+2*z*B_s'-2*nu*B_s`.
Olver, Chapter 12, §5, p. 448, by differentiation of (2.09). -/
def simplePoleDerivativeCoefficient (ν : ℂ) (A B : ℕ → ℝ → ℂ) : ℕ → ℝ → ℂ
  | 0 => A 0
  | n + 1 => fun x => A (n + 1) x + 2 * x * deriv (B n) x - 2 * ν * B n x

/-- The defining two cases of the derivative-series coefficient. -/
theorem simplePoleDerivativeCoefficient_def (ν : ℂ) (A B : ℕ → ℝ → ℂ) (n : ℕ) (x : ℝ) :
    simplePoleDerivativeCoefficient ν A B n x = match n with
    | 0 => A 0 x
    | s + 1 => A (s + 1) x + 2 * x * deriv (B s) x - 2 * ν * B s x := by
  cases n <;> rfl

/-- The other derivative coefficient is `2*A_s'+B_s`.
Olver, Chapter 12, §5, p. 448, by differentiation of (2.09). -/
def simplePoleDerivativeCompanion (A B : ℕ → ℝ → ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  2 * deriv (A n) x + B n x

/-- The defining derivative companion. -/
theorem simplePoleDerivativeCompanion_def (A B : ℕ → ℝ → ℂ) (n : ℕ) (x : ℝ) :
    simplePoleDerivativeCompanion A B n x = 2 * deriv (A n) x + B n x := rfl

/-- The coefficient construction is continuous in the real order, jointly with
the variable and with each variable derivative. Its constants are fixed by
`A_0(0)=1,A_s(0)=0` for positive `s`. Olver, Chapter 12, §5.2, p. 448. -/
theorem exists_jointly_continuous_simplePole_coefficients {D : Set ℝ}
    (hD : IsOpen D) (hstar : StarConvex ℝ 0 D) (hzero : 0 ∈ D)
    {ψ : ℝ → ℂ} (hψ : ContDiffOn ℝ ⊤ ψ D) :
    ∃ A B : ℝ → ℕ → ℝ → ℂ,
      (∀ ν : ℝ, IsSimplePoleCoefficientSequence ψ ν (A ν) (B ν) D ∧
        ∀ n, A ν n 0 = if n = 0 then 1 else 0) ∧
      ∀ n s : ℕ,
        ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv s (A p.1 n) p.2) (univ ×ˢ D) ∧
        ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv s (B p.1 n) p.2) (univ ×ˢ D) := by
  sorry

/-- The differentiated tail condition yields limits of both function and
actual derivative-series coefficients, as well as finite weighted B variation.
Both real infinities are covered by the sign. Olver, Chapter 12,
§5, pp. 447–448, and Chapter11 §7, pp. 411–412. -/
theorem exists_simplePole_coefficient_tail_limits
    {D : Set ℝ} (hD : IsOpen D) (hstar : StarConvex ℝ 0 D) (hzero : 0 ∈ D)
    {ψ : ℝ → ℂ} {A B : ℕ → ℝ → ℂ} {ν : ℂ}
    (hcoeff : IsSimplePoleCoefficientSequence ψ ν A B D)
    {δ σ : ℝ} (hδ : 0 < δ) (hσ : σ = 1 ∨ σ = -1)
    (hDtail : ∀ᶠ x : ℝ in comap (fun x : ℝ => σ * x) atTop, x ∈ D)
    (hdecay : ∀ s : ℕ, iteratedDeriv s ψ =O[comap (fun x : ℝ => σ * x) atTop]
      (fun x : ℝ => |x| ^ (-(s : ℝ) - 1 / 2 - δ))) (n : ℕ) :
    ∃ R : ℝ, 1 ≤ R ∧ {x : ℝ | R ≤ σ * x} ⊆ D ∧
      BoundedVariationOn (fun x : ℝ => (Real.sqrt |x| : ℂ) * B n x)
        {x : ℝ | R ≤ σ * x} ∧
      ∃ a b : ℂ,
        Tendsto (A n) (comap (fun x : ℝ => σ * x) atTop) (𝓝 a) ∧
        Tendsto (simplePoleDerivativeCoefficient ν A B n)
          (comap (fun x : ℝ => σ * x) atTop) (𝓝 a) ∧
        Tendsto (fun x : ℝ => (Real.sqrt |x| : ℂ) * B n x)
          (comap (fun x : ℝ => σ * x) atTop) (𝓝 b) ∧
        Tendsto (fun x : ℝ => (Real.sqrt |x| : ℂ) * simplePoleDerivativeCompanion A B n x)
          (comap (fun x : ℝ => σ * x) atTop) (𝓝 b) := by
  sorry

end ODE
