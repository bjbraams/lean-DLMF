/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Analytic inverses in nested exterior sectors

Olver, *Asymptotics and Special Functions*, Chapter 1, Theorem 6.1,
pp. 14–16, synopsis O-1.08. Strictly nested arguments keep all sectors on one sheet.
-/

@[expose] public noncomputable section

open Filter Set Asymptotics
open scoped Topology

namespace Complex

/-- A uniformly near-identity holomorphic function has an analytic inverse sufficiently far
out on each properly interior sector. The root is unique in a common intermediate sector.
Olver, Chapter 1, Theorem 6.1, synopsis O-1.08. -/
theorem exists_analytic_inverse_of_isEquivalent_sector {f : ℂ → ℂ}
    {R θ ω ω₁ ω₂ : ℝ} (hω : ω < Real.pi) (hω₂ : 0 < ω₂)
    (h₂₁ : ω₂ < ω₁) (h₁ : ω₁ < ω)
    (hf : AnalyticOnNhd ℂ f {z | R < ‖z‖ ∧ |(z * exp (-I * θ)).arg| ≤ ω})
    (he : f ~[comap norm atTop ⊓ 𝓟 {z | |(z * exp (-I * θ)).arg| ≤ ω}] id) :
    ∃ R₁ M : ℝ, R < R₁ ∧ 0 < R₁ ∧ R₁ < M ∧ ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g {u | M < ‖u‖ ∧ |(u * exp (-I * θ)).arg| ≤ ω₂} ∧
      (∀ u, M < ‖u‖ → |(u * exp (-I * θ)).arg| ≤ ω₂ →
        R₁ < ‖g u‖ ∧ |(g u * exp (-I * θ)).arg| ≤ ω₁ ∧ f (g u) = u ∧
          ∀ z, R₁ < ‖z‖ → |(z * exp (-I * θ)).arg| ≤ ω₁ → f z = u → z = g u) ∧
      g ~[comap norm atTop ⊓ 𝓟 {u | |(u * exp (-I * θ)).arg| ≤ ω₂}] id := by
  sorry

end Complex
