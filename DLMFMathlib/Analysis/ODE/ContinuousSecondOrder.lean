/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.ODE.FundamentalPair
public import DLMFMathlib.Analysis.ODE.LinearInterval
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
# Continuous second-order equations on arbitrary open real intervals

Olver, *Asymptotics and Special Functions*, Chapter 5, Theorems 1.1–1.2,
pp. 139–142, synopsis O-5.01–O-5.02. Intervals can be unbounded. The forcing,
coefficients and solutions may be complex; no analytic time regularity is imposed.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace ODE

/-- Picard iterates for `y''+p*y'+q*y=r`, including both components of the solution jet.
Olver, Chapter 5, Theorem 1.1, pp. 139–141, synopsis O-5.01. -/
def secondOrderPicardIterate (p q r : ℝ → ℂ) (t₀ : ℝ) (y₀ y₁ : ℂ) :
    ℕ → ℝ → ℂ × ℂ
  | 0, _ => (y₀, y₁)
  | n + 1, t => (y₀, y₁) + ∫ s in t₀..t,
      ((secondOrderPicardIterate p q r t₀ y₀ y₁ n s).2,
        r s - p s * (secondOrderPicardIterate p q r t₀ y₀ y₁ n s).2 -
          q s * (secondOrderPicardIterate p q r t₀ y₀ y₁ n s).1)

/-- Initial Picard iterate. -/
theorem secondOrderPicardIterate_zero (p q r : ℝ → ℂ) (t₀ : ℝ) (y₀ y₁ : ℂ) (t : ℝ) :
    secondOrderPicardIterate p q r t₀ y₀ y₁ 0 t = (y₀, y₁) := rfl

/-- The actual Picard integral recurrence. -/
theorem secondOrderPicardIterate_succ (p q r : ℝ → ℂ) (t₀ : ℝ) (y₀ y₁ : ℂ)
    (n : ℕ) (t : ℝ) :
    secondOrderPicardIterate p q r t₀ y₀ y₁ (n + 1) t = (y₀, y₁) +
      ∫ s in t₀..t, ((secondOrderPicardIterate p q r t₀ y₀ y₁ n s).2,
        r s - p s * (secondOrderPicardIterate p q r t₀ y₀ y₁ n s).2 -
          q s * (secondOrderPicardIterate p q r t₀ y₀ y₁ n s).1) := rfl

/-- Continuous coefficients and forcing give the unique complete-interval solution and
compact-uniform convergence of its explicit Picard iterates.
Olver, Chapter 5, Theorem 1.1, pp. 139–141, synopsis O-5.01. -/
theorem existsUnique_secondOrder_continuous_interval {U : Set ℝ}
    (hU : IsOpen U) (hconnected : U.OrdConnected) {t₀ : ℝ} (ht₀ : t₀ ∈ U)
    {p q r : ℝ → ℂ} (hp : ContinuousOn p U) (hq : ContinuousOn q U)
    (hr : ContinuousOn r U) (y₀ y₁ : ℂ) :
    ∃ y v : ℝ → ℂ, y t₀ = y₀ ∧ v t₀ = y₁ ∧ ContDiffOn ℝ 2 y U ∧
      (∀ t ∈ U, HasDerivAt y (v t) t ∧
        HasDerivAt v (r t - p t * v t - q t * y t) t) ∧
      (∀ a b : ℝ, Icc a b ⊆ U → t₀ ∈ Icc a b →
        TendstoUniformlyOn (secondOrderPicardIterate p q r t₀ y₀ y₁)
          (fun t => (y t, v t)) atTop (Icc a b)) ∧
      ∀ z z' : ℝ → ℂ, z t₀ = y₀ → z' t₀ = y₁ →
        (∀ t ∈ U, HasDerivAt z (z' t) t ∧
          HasDerivAt z' (r t - p t * z' t - q t * z t) t) →
        EqOn z y U ∧ EqOn z' v U := by
  sorry

/-- Abel's formula with minimal continuous real-time coefficients and complex solutions.
Olver, Chapter 5, Theorem 1.2, pp. 141–142, synopsis O-5.02. -/
theorem wronskian_eq_exp_integral_continuous {U : Set ℝ}
    (hU : IsOpen U) (hconnected : U.OrdConnected) {p q f g : ℝ → ℂ}
    (hp : ContinuousOn p U) (hq : ContinuousOn q U)
    (hf : ContDiffOn ℝ 2 f U) (hg : ContDiffOn ℝ 2 g U)
    (hfeq : ∀ t ∈ U, iteratedDeriv 2 f t + p t * deriv f t + q t * f t = 0)
    (hgeq : ∀ t ∈ U, iteratedDeriv 2 g t + p t * deriv g t + q t * g t = 0)
    {t₀ t : ℝ} (ht₀ : t₀ ∈ U) (ht : t ∈ U) :
    wronskian f g t = wronskian f g t₀ * Complex.exp (-(∫ s in t₀..t, p s)) := by
  sorry

/-- The spanning, linear-independence and Wronskian tests are equivalent for continuous
ordinary real-time equations. Olver, Chapter 5, Theorem 1.2, synopsis O-5.02. -/
theorem fundamentalPair_iff_linearIndependent_iff_wronskian {U : Set ℝ}
    (hU : IsOpen U) (hconnected : U.OrdConnected) (hne : U.Nonempty)
    {p q f g : ℝ → ℂ} (hp : ContinuousOn p U) (hq : ContinuousOn q U)
    (hf : ContDiffOn ℝ 2 f U) (hg : ContDiffOn ℝ 2 g U)
    (hfeq : ∀ t ∈ U, iteratedDeriv 2 f t + p t * deriv f t + q t * f t = 0)
    (hgeq : ∀ t ∈ U, iteratedDeriv 2 g t + p t * deriv g t + q t * g t = 0) :
    ((∀ y : ℝ → ℂ, ContDiffOn ℝ 2 y U →
      (∀ t ∈ U, iteratedDeriv 2 y t + p t * deriv y t + q t * y t = 0) →
      ∃ A B : ℂ, ∀ t ∈ U, y t = A * f t + B * g t) ↔
        LinearIndependent ℂ ![(fun t : U => f t), (fun t : U => g t)]) ∧
    (LinearIndependent ℂ ![(fun t : U => f t), (fun t : U => g t)] ↔
      ∃ t ∈ U, wronskian f g t ≠ 0) := by
  sorry

/-- Reduction of order on a real ordinary interval requires only continuous complex
coefficients. Both nested integrals are the actual normalized primitives, and the
Wronskian is the nowhere-zero Abel factor.
Olver, Chapter 5, Theorem 1.2, pp. 141–142, synopsis O-5.02. -/
theorem reduction_of_order_continuous {U : Set ℝ} (hU : IsOpen U)
    (hconn : OrdConnected U) {p q w : ℝ → ℂ}
    (hp : ContinuousOn p U) (hq : ContinuousOn q U) (hw : ContDiffOn ℝ 2 w U)
    (hne : ∀ x ∈ U, w x ≠ 0)
    (hode : ∀ x ∈ U, iteratedDeriv 2 w x + p x * deriv w x + q x * w x = 0)
    {a : ℝ} (ha : a ∈ U) :
    let E := fun x => Complex.exp (-(∫ t : ℝ in a..x, p t))
    let v := fun x => w x * ∫ t : ℝ in a..x, E t / w t ^ 2
    ContDiffOn ℝ 2 v U ∧ v a = 0 ∧ deriv v a = (w a)⁻¹ ∧
      ∀ x ∈ U, iteratedDeriv 2 v x + p x * deriv v x + q x * v x = 0 ∧
        wronskian w v x = E x ∧ E x ≠ 0 := by
  sorry

end ODE
