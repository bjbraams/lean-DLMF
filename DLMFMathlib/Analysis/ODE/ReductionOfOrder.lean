/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Reduction of order for analytic second-order equations

Kristensson, *Second Order Differential Equations*, §2.3.1, pp. 10–11, and
Olver, *Asymptotics and Special Functions*, Chapter 5, §1. The two primitives
are normalized at an interior point, making the Wronskian normalization explicit.
-/

@[expose] public section

open Set

noncomputable section

namespace Complex

/-- Kristensson, §2.3.1: if `F′=p` and `G′=exp(-F)/u²`, then `uG` is a
second solution with Wronskian `exp(-F)`, provided `u` is a nonvanishing solution.
The explicit primitive assumptions also apply on an arbitrary branch domain. -/
theorem reduction_of_order_of_primitives {D : Set ℂ} {p q u F G : ℂ → ℂ}
    (hD : IsOpen D)
    (hu : AnalyticOnNhd ℂ u D) (hF : AnalyticOnNhd ℂ F D) (hG : AnalyticOnNhd ℂ G D)
    (hne : ∀ z ∈ D, u z ≠ 0)
    (hode : ∀ z ∈ D, deriv (deriv u) z + p z * deriv u z + q z * u z = 0)
    (hFp : ∀ z ∈ D, deriv F z = p z)
    (hGp : ∀ z ∈ D, deriv G z = exp (-F z) / (u z) ^ 2) :
    ∀ z ∈ D,
      deriv (deriv (fun t => u t * G t)) z +
        p z * deriv (fun t => u t * G t) z + q z * (u z * G z) = 0 ∧
      u z * deriv (fun t => u t * G t) z - deriv u z * (u z * G z) = exp (-F z) := by
  sorry

/-- Kristensson, §2.3.1, and Olver, Chapter 5, §1: on a simply connected
nonvanishing-solution domain the two normalized analytic primitives exist and give
a second solution with nowhere-zero Wronskian. -/
theorem exists_reduction_of_order {D : Set ℂ} {p q u : ℂ → ℂ} {b : ℂ}
    (hD : IsOpen D) (hsc : IsSimplyConnected D) (hb : b ∈ D)
    (hp : AnalyticOnNhd ℂ p D)
    (hu : AnalyticOnNhd ℂ u D) (hne : ∀ z ∈ D, u z ≠ 0)
    (hode : ∀ z ∈ D, deriv (deriv u) z + p z * deriv u z + q z * u z = 0) :
    ∃ F G : ℂ → ℂ, AnalyticOnNhd ℂ F D ∧ AnalyticOnNhd ℂ G D ∧ F b = 0 ∧ G b = 0 ∧
      ∀ z ∈ D, deriv F z = p z ∧ deriv G z = exp (-F z) / (u z) ^ 2 ∧
        deriv (deriv (fun t => u t * G t)) z +
          p z * deriv (fun t => u t * G t) z + q z * (u z * G z) = 0 ∧
        u z * deriv (fun t => u t * G t) z - deriv u z * (u z * G z) = exp (-F z) ∧
        exp (-F z) ≠ 0 := by
  sorry

end Complex
