/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# Inhomogeneous large-parameter coefficient expansions

The recursion and finite sums are genuine functions. The exact residual and
two-reference primitive error retain the signs and powers of the parameter.
Source: Olver, *Asymptotics and Special Functions*, Chapter 10, §10,
pp. 386–388. Convergence of endpoint primitives is supplied by applications.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace Complex

/-- Coefficients for `W''-(u^2+psi)W=omega`, with initial coefficient `-omega`.
Olver, Chapter 10, §10, pp. 386–387. -/
def inhomogeneousExpansionCoefficient (ψ ω : ℂ → ℂ) : ℕ → ℂ → ℂ
  | 0 => fun z => -ω z
  | n + 1 => fun z => deriv (deriv (inhomogeneousExpansionCoefficient ψ ω n)) z -
      ψ z * inhomogeneousExpansionCoefficient ψ ω n z

/-- The initial inhomogeneous coefficient. -/
@[simp] theorem inhomogeneousExpansionCoefficient_zero (ψ ω : ℂ → ℂ) (z : ℂ) :
    inhomogeneousExpansionCoefficient ψ ω 0 z = -ω z := rfl

/-- The defining second-derivative recursion. -/
theorem inhomogeneousExpansionCoefficient_succ (ψ ω : ℂ → ℂ) (n : ℕ) (z : ℂ) :
    inhomogeneousExpansionCoefficient ψ ω (n + 1) z =
      deriv (deriv (inhomogeneousExpansionCoefficient ψ ω n)) z -
        ψ z * inhomogeneousExpansionCoefficient ψ ω n z := rfl

/-- The finite inverse-even-power inhomogeneous expansion.
Olver, Chapter 10, §10, pp. 386–387. -/
def inhomogeneousExpansionPartialSum (ψ ω : ℂ → ℂ) (u : ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  ∑ n ∈ Finset.range N, inhomogeneousExpansionCoefficient ψ ω n z / u ^ (2 * n + 2)

/-- The defining finite coefficient sum. -/
theorem inhomogeneousExpansionPartialSum_def (ψ ω : ℂ → ℂ) (u : ℂ) (N : ℕ) (z : ℂ) :
    inhomogeneousExpansionPartialSum ψ ω u N z =
      ∑ n ∈ Finset.range N, inhomogeneousExpansionCoefficient ψ ω n z / u ^ (2 * n + 2) := rfl

/-- The zero-term partial sum vanishes. -/
@[simp] theorem inhomogeneousExpansionPartialSum_zero (ψ ω : ℂ → ℂ) (u z : ℂ) :
    inhomogeneousExpansionPartialSum ψ ω u 0 z = 0 := by
  simp [inhomogeneousExpansionPartialSum]

/-- Analytic coefficients remain analytic through every step of the recursion.
Olver, Chapter 10, §10, p. 386. -/
theorem analyticOnNhd_inhomogeneousExpansionCoefficient {ψ ω : ℂ → ℂ} {U : Set ℂ}
    (hψ : AnalyticOnNhd ℂ ψ U) (hω : AnalyticOnNhd ℂ ω U) (n : ℕ) :
    AnalyticOnNhd ℂ (inhomogeneousExpansionCoefficient ψ ω n) U := by
  induction n with
  | zero => exact hω.neg
  | succ n ih => exact ih.deriv.deriv.sub (hψ.mul ih)

/-- The exact truncation residual is the next coefficient divided by `u^(2N)`.
In particular no additional sign or forcing term is hidden in the remainder.
Olver, Chapter 10, §10, p. 386. -/
theorem inhomogeneousExpansionPartialSum_residual {ψ ω : ℂ → ℂ} {U : Set ℂ}
    (hψ : AnalyticOnNhd ℂ ψ U) (hω : AnalyticOnNhd ℂ ω U)
    {u : ℂ} (hu : u ≠ 0) (N : ℕ) {z : ℂ} (hz : z ∈ U) :
    deriv (deriv (inhomogeneousExpansionPartialSum ψ ω u N)) z -
      (u ^ 2 + ψ z) * inhomogeneousExpansionPartialSum ψ ω u N z - ω z =
        inhomogeneousExpansionCoefficient ψ ω N z / u ^ (2 * N) := by
  sorry

/-- Exact two-reference error construction from complementary homogeneous
solutions and separately chosen primitives. Their constants may come from
opposite finite or convergent infinite endpoints. The displayed sign is the one
needed to cancel the truncation residual. Olver, Chapter 10, §10, pp. 386–388. -/
theorem inhomogeneousExpansionError_equation {ψ ω W₁ W₂ F₁ F₂ : ℂ → ℂ}
    {U : Set ℂ} (hU : IsOpen U) {u W : ℂ} (hu : u ≠ 0) (hW : W ≠ 0)
    (hψ : AnalyticOnNhd ℂ ψ U) (hω : AnalyticOnNhd ℂ ω U)
    (hW₁ : AnalyticOnNhd ℂ W₁ U) (hW₂ : AnalyticOnNhd ℂ W₂ U)
    (hF₁ : AnalyticOnNhd ℂ F₁ U) (hF₂ : AnalyticOnNhd ℂ F₂ U) (N : ℕ)
    (hode₁ : ∀ z ∈ U, deriv (deriv W₁) z = (u ^ 2 + ψ z) * W₁ z)
    (hode₂ : ∀ z ∈ U, deriv (deriv W₂) z = (u ^ 2 + ψ z) * W₂ z)
    (hwronskian : ∀ z ∈ U, W₁ z * deriv W₂ z - deriv W₁ z * W₂ z = W)
    (hprimitive₁ : ∀ z ∈ U,
      deriv F₁ z = W₁ z * inhomogeneousExpansionCoefficient ψ ω N z / W)
    (hprimitive₂ : ∀ z ∈ U,
      deriv F₂ z = W₂ z * inhomogeneousExpansionCoefficient ψ ω N z / W) :
    let E := fun z => (W₁ z * F₂ z - W₂ z * F₁ z) / u ^ (2 * N)
    ∀ z ∈ U, deriv (deriv E) z - (u ^ 2 + ψ z) * E z =
      -inhomogeneousExpansionCoefficient ψ ω N z / u ^ (2 * N) := by
  sorry

end Complex
