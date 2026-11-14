/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Asymptotics.AsymptoticExpansion
public import DLMFMathlib.Analysis.Asymptotics.ExponentialGrowth
public import Mathlib.Analysis.Analytic.Constructions

/-!
# Exact converging factors and limits of finite-argument inference

Olver, *Asymptotics and Special Functions*, Chapter 14, §§1–2,
pp. 519–522, synopsis O-14.01. Least-term choice is a predicate about
terms alone; it does not assert anything about the actual remainder.
-/

@[expose] public noncomputable section
open Filter Set
open scoped Topology
namespace Asymptotics

/-- The exact quotient of a remainder by its next term; applications require
that next term to be nonzero. Olver, Chapter 14, §§1–2, pp. 519–522. -/
def convergingFactor {α K : Type*} [Field K] (f : α → K) (u : ℕ → α → K)
    (n : ℕ) (x : α) : K := (f x - ∑ j ∈ Finset.range n, u j x) / u n x

/-- The exact defining remainder quotient. -/
theorem convergingFactor_def {α K : Type*} [Field K] (f : α → K)
    (u : ℕ → α → K) (n : ℕ) (x : α) : convergingFactor f u n x =
      (f x - ∑ j ∈ Finset.range n, u j x) / u n x := rfl

/-- Recovering the exact remainder requires the omitted term to be nonzero.
Olver, Chapter 14, §§1–2. -/
theorem convergingFactor_mul {α K : Type*} [Field K] (f : α → K)
    (u : ℕ → α → K) (n : ℕ) (x : α) (hu : u n x ≠ 0) :
    convergingFactor f u n x * u n x = f x - ∑ j ∈ Finset.range n, u j x := by
  rw [convergingFactor, div_mul_cancel₀ _ hu]

/-- An index minimizes term size, with no assertion about the error of its
associated truncation. Olver, Chapter 14, §§1–2. -/
def IsLeastTermIndex {E : Type*} [NormedAddCommGroup E] (u : ℕ → E) (n : ℕ) : Prop :=
  ∀ j : ℕ, ‖u n‖ ≤ ‖u j‖

/-- The defining minimum-size property of a least-term index. -/
theorem isLeastTermIndex_iff {E : Type*} [NormedAddCommGroup E] (u : ℕ → E) (n : ℕ) :
    IsLeastTermIndex u n ↔ ∀ j : ℕ, ‖u n‖ ≤ ‖u j‖ := Iff.rfl

/-- An explicit flat function with any prescribed finite-point value.
Olver, Chapter 14, §§1–2, pp. 519–522. -/
def flatExample (x₀ M x : ℝ) : ℝ := M * Real.exp (x₀ - x)

/-- The defining flat exponential. -/
theorem flatExample_def (x₀ M x : ℝ) : flatExample x₀ M x = M * Real.exp (x₀ - x) := rfl

/-- Every value at an assigned finite argument is possible for a flat function. -/
theorem flatExample_self (x₀ M : ℝ) : flatExample x₀ M x₀ = M := by
  simp [flatExample]

/-- The prescribed finite value is invisible to every inverse-power order.
Olver, Chapter 14, §§1–2, pp. 519–522. -/
theorem isLittleO_flatExample (x₀ M r : ℝ) :
    flatExample x₀ M =o[atTop] (fun x : ℝ => x ^ r) := by
  have h := (isLittleO_exp_neg_mul_rpow_atTop (by norm_num : (0 : ℝ) < 1) r).const_mul_left
    (M * Real.exp x₀)
  refine h.congr' (Eventually.of_forall fun x => ?_) .rfl
  simp only [flatExample, neg_mul, one_mul, Real.exp_sub, Real.exp_neg]
  ring

/-- Even an everywhere-decreasing nonzero term sequence and a full analytic
asymptotic expansion give no prescribed next-term bound at a fixed finite point.
Olver, Chapter 14, §§1–2, pp. 519–522. -/
theorem exists_analytic_expansion_error_gt_of_decreasing_terms {x₀ : ℝ}
    (hx₀ : 1 < x₀) (N : ℕ) (B : ℝ) :
    ∃ f : ℝ → ℝ, AnalyticOnNhd ℝ f (Ioi 1) ∧
      HasAsymptoticExpansion atTop (fun (j : ℕ) (x : ℝ) => (x ^ (j + 1))⁻¹)
        (fun _ => (1 : ℝ)) f ∧
      (∀ j : ℕ, 0 < (x₀ ^ (j + 2))⁻¹ ∧
        (x₀ ^ (j + 2))⁻¹ < (x₀ ^ (j + 1))⁻¹) ∧
      |f x₀ - ∑ j ∈ Finset.range N, (x₀ ^ (j + 1))⁻¹| > B / x₀ ^ (N + 1) := by
  sorry

end Asymptotics
