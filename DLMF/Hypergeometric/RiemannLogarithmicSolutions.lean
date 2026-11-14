/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Riemann
public import DLMF.Hypergeometric.ArgumentContinuation

/-!
# Papperitz solutions with specified local logarithms

Rao–Lakshminarayanan, *Generalized Hypergeometric Functions* (2018), Chapter 3,
(3.14)–(3.18), pp. 3-6–3-7, synopsis RL-3.04. Both prefactor logarithms are
specified as analytic functions. The Gauss factor is its principal continuation
on the full cut plane, rather than a divergent totalized series.
-/

@[expose] public noncomputable section

open Complex Set

namespace DLMF.Hypergeometric

/-- The local Papperitz solution with arbitrary specified analytic logarithms of its
two prefactor ratios, on the full principal domain of the Gauss argument.
Rao–Lakshminarayanan (3.14)–(3.18), pp. 3-6–3-7, synopsis RL-3.04. -/
theorem riemann_hypergeometric_solution_exp_log
    {α β γ a₁ a₂ b₁ b₂ c₁ c₂ : ℂ}
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hβγ : β ≠ γ)
    (hfuchs : a₁ + a₂ + b₁ + b₂ + c₁ + c₂ = 1)
    (hc : ∀ k : ℕ, 1 + a₁ - a₂ ≠ -(k : ℂ))
    {U : Set ℂ} (hU : IsOpen U) {Lα Lβ : ℂ → ℂ}
    (hLα : AnalyticOnNhd ℂ Lα U) (hLβ : AnalyticOnNhd ℂ Lβ U)
    (hreg : ∀ z ∈ U, z ≠ α ∧ z ≠ β ∧ z ≠ γ)
    (hαlog : ∀ z ∈ U, exp (Lα z) = (z - α) / (z - γ))
    (hβlog : ∀ z ∈ U, exp (Lβ z) = (z - β) / (z - γ))
    (hT : ∀ z ∈ U, (z - α) * (β - γ) / ((z - γ) * (β - α)) ∈ cutPlane) :
    let y := fun z => exp (a₁ * Lα z + b₁ * Lβ z) * Gamma (1 + a₁ - a₂) *
      regularizedGaussHypergeometric (a₁ + b₁ + c₁) (a₁ + b₁ + c₂)
        (1 + a₁ - a₂) ((z - α) * (β - γ) / ((z - γ) * (β - α)))
    AnalyticOnNhd ℂ y U ∧ ∀ z ∈ U,
      riemannOperator α β γ a₁ a₂ b₁ b₂ c₁ c₂ y z = 0 := by
  sorry

end DLMF.Hypergeometric
