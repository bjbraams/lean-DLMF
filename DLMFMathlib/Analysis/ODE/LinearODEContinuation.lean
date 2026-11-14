/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Analysis.Complex.Conformal.Continuation.Basic

/-!
# Continuation of linear ODE solution germs along paths

Olver, *Asymptotics and Special Functions*, Chapter 5, Theorems 3.1–3.2,
pp. 145–147, synopsis O-5.05–O-5.06. A continuation is an actual compatible
family of local solution germs along the supplied path. This retains path choices
on multiply connected domains instead of assuming single-valuedness there.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology

namespace Complex

/-- Compatible analytic solution germs of `y''+py'+qy=0` along `γ`.
The local representatives agree near neighboring path points.
Olver, Chapter 5, Theorems 3.1–3.2, synopsis O-5.05/O-5.06. -/
def IsLinearSecondOrderContinuation (p q : ℂ → ℂ) (D : Set ℂ)
    (path : ℝ → ℂ) (F : ℝ → ℂ → ℂ) : Prop :=
  (∀ t ∈ Icc (0 : ℝ) 1, path t ∈ D ∧ AnalyticAt ℂ (F t) (path t) ∧
    ∀ᶠ z in 𝓝 (path t), z ∈ D ∧
      iteratedDeriv 2 (F t) z + p z * deriv (F t) z + q z * F t z = 0) ∧
  ∀ t ∈ Icc (0 : ℝ) 1, ∀ᶠ s in 𝓝[Icc (0 : ℝ) 1] t,
    F s =ᶠ[𝓝 (path s)] F t

/-- The local solution and neighboring-germ compatibility conditions. -/
theorem isLinearSecondOrderContinuation_iff (p q : ℂ → ℂ) (D : Set ℂ)
    (path : ℝ → ℂ) (F : ℝ → ℂ → ℂ) :
    IsLinearSecondOrderContinuation p q D path F ↔
      ((∀ t ∈ Icc (0 : ℝ) 1, path t ∈ D ∧ AnalyticAt ℂ (F t) (path t) ∧
        ∀ᶠ z in 𝓝 (path t), z ∈ D ∧
          iteratedDeriv 2 (F t) z + p z * deriv (F t) z + q z * F t z = 0) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ᶠ s in 𝓝[Icc (0 : ℝ) 1] t,
        F s =ᶠ[𝓝 (path s)] F t) := Iff.rfl

/-- A carried ODE solution jet is the canonical TauCeti analytic continuation of its
value germ. Olver, Chapter 5, Theorems 3.1–3.2, synopsis O-5.05/O-5.06. -/
theorem IsLinearSecondOrderContinuation.isAnalyticContinuationAlong
    {p q : ℂ → ℂ} {D : Set ℂ} {path : ℝ → ℂ} {F : ℝ → ℂ → ℂ}
    (hF : IsLinearSecondOrderContinuation p q D path F)
    (hpath : ContinuousOn path (Icc (0 : ℝ) 1)) :
    TauCeti.IsAnalyticContinuationAlong F path (Icc (0 : ℝ) 1) where
  continuousOn := hpath
  analyticAt t ht := (hF.1 t ht).2.1
  locallyEq := hF.2

/-- Every continuous path in the ordinary domain carries a unique continuation of the
specified initial solution germ. No simply-connectedness assumption is made.
Olver, Chapter 5, Theorem 3.1, pp. 145–146, synopsis O-5.05. -/
theorem existsUnique_linearSecondOrderContinuation {D : Set ℂ} (hD : IsOpen D)
    {p q : ℂ → ℂ} (hp : AnalyticOnNhd ℂ p D) (hq : AnalyticOnNhd ℂ q D)
    {path : ℝ → ℂ} (hpath : ContinuousOn path (Icc (0 : ℝ) 1))
    (himage : ∀ t ∈ Icc (0 : ℝ) 1, path t ∈ D) (a b : ℂ) :
    ∃ F : ℝ → ℂ → ℂ, IsLinearSecondOrderContinuation p q D path F ∧
      F 0 (path 0) = a ∧ deriv (F 0) (path 0) = b ∧
      ∀ G : ℝ → ℂ → ℂ, IsLinearSecondOrderContinuation p q D path G →
        G 0 (path 0) = a → deriv (G 0) (path 0) = b →
        ∀ t ∈ Icc (0 : ℝ) 1, F t =ᶠ[𝓝 (path t)] G t := by
  sorry

/-- Fixed-path continuation preserves holomorphic dependence of the value and its first
 two argument derivatives on a holomorphic parameter.
Olver, Chapter 5, Theorem 3.2, pp. 146–147, synopsis O-5.06. -/
theorem exists_linearSecondOrderContinuation_param_analytic {U D : Set ℂ}
    (hU : IsOpen U) (hD : IsOpen D) {p q : ℂ → ℂ → ℂ}
    (hp : ContinuousOn (Function.uncurry p) (U ×ˢ D))
    (hq : ContinuousOn (Function.uncurry q) (U ×ˢ D))
    (hpu : ∀ z ∈ D, AnalyticOnNhd ℂ (fun u => p u z) U)
    (hqu : ∀ z ∈ D, AnalyticOnNhd ℂ (fun u => q u z) U)
    (hpz : ∀ u ∈ U, AnalyticOnNhd ℂ (p u) D)
    (hqz : ∀ u ∈ U, AnalyticOnNhd ℂ (q u) D)
    {a b : ℂ → ℂ} (ha : AnalyticOnNhd ℂ a U) (hb : AnalyticOnNhd ℂ b U)
    {path : ℝ → ℂ} (hpath : ContinuousOn path (Icc (0 : ℝ) 1))
    (himage : ∀ t ∈ Icc (0 : ℝ) 1, path t ∈ D) :
    ∃ F : ℂ → ℝ → ℂ → ℂ,
      (∀ u ∈ U, IsLinearSecondOrderContinuation (p u) (q u) D path (F u) ∧
        F u 0 (path 0) = a u ∧ deriv (F u 0) (path 0) = b u) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ j ≤ 2,
        AnalyticOnNhd ℂ (fun u => iteratedDeriv j (F u t) (path t)) U := by
  sorry

end Complex
