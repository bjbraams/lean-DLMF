/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Differential

/-!
# The formal Laguerre generating series

`laguerreSeries α x = ∑ L_n^{(α)}(x) tⁿ` (with `laguerreExtended`) is the unique formal
solution with constant term one of the generating-function equation
`(1 - t)² f' = ((α + 1)(1 - t) - x) f` (`LaguerreODE`). The equation is equivalent to the
three-term recurrence. Products of solutions solve the equation with parameters
`α + β + 1` and `x + y`, which gives the Laguerre addition theorem for `Re α, Re β > -1`.
Both sides of that theorem are entire in `α` and `β`, so the identity theorem removes the
restriction.
-/

@[expose] public section

open Complex
open scoped Nat
open DLMF.Hypergeometric

noncomputable section

namespace DLMF.OrthogonalPolynomials

open PowerSeries

/-- The formal Laguerre generating series `∑ L_n^{(α)}(x) tⁿ`. -/
def laguerreSeries (α x : ℂ) : PowerSeries ℂ := mk fun n => laguerreExtended α n x

/-- The Laguerre generating differential equation `(1 - t)² f' = ((α + 1)(1 - t) - x) f`. -/
def LaguerreODE (α x : ℂ) (F : PowerSeries ℂ) : Prop :=
  (1 - X) ^ 2 * d⁄dX F = (C (α + 1) * (1 - X) - C x) * F

/-- `L_0^{(α)} = 1`. -/
theorem laguerreExtended_zero (α x : ℂ) : laguerreExtended α 0 x = 1 := by
  simp [laguerreExtended, poch_zero]

/-- `L_1^{(α)}(x) = α + 1 - x`. -/
theorem laguerreExtended_one (α x : ℂ) : laguerreExtended α 1 x = α + 1 - x := by
  simp [laguerreExtended, Finset.sum_range_succ, poch_succ, poch_zero]
  ring

/-- The Laguerre equation with the products expanded. -/
theorem laguerreODE_iff (α x : ℂ) (F : PowerSeries ℂ) :
    LaguerreODE α x F ↔ d⁄dX F - C 2 * (X * d⁄dX F) + X * (X * d⁄dX F) =
      C (α + 1 - x) * F - C (α + 1) * (X * F) := by
  unfold LaguerreODE
  have e1 : (1 - X) ^ 2 * d⁄dX F = d⁄dX F - C 2 * (X * d⁄dX F) + X * (X * d⁄dX F) := by
    rw [map_ofNat]; ring
  have e2 : (C (α + 1) * (1 - X) - C x) * F = C (α + 1 - x) * F - C (α + 1) * (X * F) := by
    rw [map_sub (C) (α + 1) x]; ring
  rw [e1, e2]

/-- The linear coefficient of a solution of the Laguerre equation. -/
theorem coeff_one_of_laguerreODE {α x : ℂ} {F : PowerSeries ℂ} (h : LaguerreODE α x F) :
    coeff 1 F = (α + 1 - x) * coeff 0 F := by
  have h0 := congrArg (coeff 0) ((laguerreODE_iff α x F).mp h)
  rw [LinearMap.map_add, LinearMap.map_sub, LinearMap.map_sub, coeff_C_mul, coeff_C_mul,
    coeff_C_mul, coeff_zero_X_mul, coeff_zero_X_mul, coeff_zero_X_mul, coeff_derivative] at h0
  simpa using h0

/-- Solutions of the Laguerre equation satisfy the three-term recurrence. -/
theorem coeff_add_two_of_laguerreODE {α x : ℂ} {F : PowerSeries ℂ} (h : LaguerreODE α x F)
    (n : ℕ) : (n + 2 : ℂ) * coeff (n + 2) F =
      (2 * n + α + 3 - x) * coeff (n + 1) F - (n + α + 1) * coeff n F := by
  have h1 := congrArg (coeff (n + 1)) ((laguerreODE_iff α x F).mp h)
  rw [LinearMap.map_add, LinearMap.map_sub, LinearMap.map_sub, coeff_C_mul, coeff_C_mul,
    coeff_C_mul, coeff_succ_X_mul, coeff_succ_X_mul, coeff_succ_X_mul, coeff_derivative,
    coeff_derivative] at h1
  rcases n with _ | n
  · rw [coeff_zero_X_mul] at h1
    push_cast at h1 ⊢
    linear_combination h1
  · rw [coeff_succ_X_mul, coeff_derivative] at h1
    push_cast at h1 ⊢
    linear_combination h1

/-- The three-term recurrence implies the Laguerre equation. -/
theorem laguerreODE_of_coeff {α x : ℂ} {F : PowerSeries ℂ}
    (h1 : coeff 1 F = (α + 1 - x) * coeff 0 F)
    (h2 : ∀ n : ℕ, (n + 2 : ℂ) * coeff (n + 2) F =
      (2 * n + α + 3 - x) * coeff (n + 1) F - (n + α + 1) * coeff n F) :
    LaguerreODE α x F := by
  rw [laguerreODE_iff]
  ext n
  rw [LinearMap.map_add, LinearMap.map_sub, LinearMap.map_sub, coeff_C_mul, coeff_C_mul,
    coeff_C_mul]
  rcases n with _ | n
  · rw [coeff_zero_X_mul, coeff_zero_X_mul, coeff_zero_X_mul, coeff_derivative]
    push_cast
    linear_combination h1
  · rw [coeff_succ_X_mul, coeff_succ_X_mul, coeff_succ_X_mul, coeff_derivative, coeff_derivative]
    rcases n with _ | n
    · rw [coeff_zero_X_mul]
      have := h2 0
      push_cast at this ⊢
      linear_combination this
    · rw [coeff_succ_X_mul, coeff_derivative]
      have := h2 (n + 1)
      push_cast at this ⊢
      linear_combination this

/-- A solution of the Laguerre equation is determined by its constant coefficient. -/
theorem eq_of_laguerreODE {α x : ℂ} {F G : PowerSeries ℂ} (hF : LaguerreODE α x F)
    (hG : LaguerreODE α x G) (h0 : coeff 0 F = coeff 0 G) : F = G := by
  ext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · exact h0
    · rw [coeff_one_of_laguerreODE hF, coeff_one_of_laguerreODE hG, h0]
    · have hF2 := coeff_add_two_of_laguerreODE hF n
      have hG2 := coeff_add_two_of_laguerreODE hG n
      rw [ih n (by omega), ih (n + 1) (by omega)] at hF2
      have hn : (n + 2 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n + 1)
      exact mul_left_cancel₀ hn (hF2.trans hG2.symm)

/-- The product of solutions solves the equation with parameters added. -/
theorem laguerreODE_mul {α β x y : ℂ} {F G : PowerSeries ℂ} (hF : LaguerreODE α x F)
    (hG : LaguerreODE β y G) : LaguerreODE (α + β + 1) (x + y) (F * G) := by
  unfold LaguerreODE at *
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  simp only [map_add, map_one] at *
  linear_combination F * hG + G * hF


/-- The Laguerre series solves the Laguerre equation for `Re α > -1`. -/
theorem laguerreODE_laguerreSeries {α : ℂ} (hα : -1 < α.re) (x : ℂ) :
    LaguerreODE α x (laguerreSeries α x) := by
  have hc : ∀ k : ℕ, α + 1 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by
    simp only [Complex.add_re, Complex.one_re]
    linarith)
  apply laguerreODE_of_coeff
  · simp only [laguerreSeries, coeff_mk, laguerreExtended_zero, laguerreExtended_one, mul_one]
  · intro n
    simp only [laguerreSeries, coeff_mk, laguerreExtended_eq hc]
    exact laguerrePolyL_recurrence hα n x

/-- The Laguerre addition theorem for `Re α, Re β > -1`. -/
theorem laguerrePolyL_addition_of_re {α β : ℂ} (hα : -1 < α.re) (hβ : -1 < β.re) (x y : ℂ) (n : ℕ) :
    laguerreExtended (α + β + 1) n (x + y) =
      ∑ k ∈ Finset.range (n + 1), laguerreExtended α k x * laguerreExtended β (n - k) y := by
  have hγ : -1 < (α + β + 1).re := by
    simp only [Complex.add_re, Complex.one_re]; linarith
  have h := eq_of_laguerreODE (laguerreODE_mul (laguerreODE_laguerreSeries hα x)
    (laguerreODE_laguerreSeries hβ y)) (laguerreODE_laguerreSeries hγ (x + y))
    (by simp [laguerreSeries, laguerreExtended_zero])
  have hn := congrArg (coeff n) h
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hn
  simpa [laguerreSeries] using hn.symm


/-- `laguerreExtended` is entire in the parameter. -/
theorem differentiable_laguerreExtended (n : ℕ) (x : ℂ) :
    Differentiable ℂ fun α : ℂ => laguerreExtended α n x := by
  unfold laguerreExtended
  refine Differentiable.fun_sum fun k _ => ?_
  refine Differentiable.mul (Differentiable.div_const ?_ _) (differentiable_const _)
  exact (ascPochhammer ℂ (n - k)).differentiable.comp
    ((differentiable_id.add_const _).add_const _)

/-- Two entire functions agreeing on `-1 < Re a` agree everywhere. -/
theorem eq_of_differentiable_of_re_gt {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (h : ∀ a : ℂ, -1 < a.re → f a = g a) (a : ℂ) : f a = g a := by
  have hU : IsOpen {a : ℂ | -1 < a.re} := isOpen_lt continuous_const Complex.continuous_re
  refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (z₀ := 0)
    (fun z _ => hf.analyticAt z) (fun z _ => hg.analyticAt z) isPreconnected_univ
    (Set.mem_univ _) ?_ (Set.mem_univ a)
  filter_upwards [hU.mem_nhds (by simp : (0 : ℂ) ∈ {a : ℂ | -1 < a.re})] with z hz
  exact h z hz

end DLMF.OrthogonalPolynomials
