/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Basic.NormsAndKernels
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Jacobi matrices and moment generating fractions

Andrews, Askey and Roy, *Special Functions*, §5.8 identifies moments with finite
Jacobi-matrix entries and hence with weighted walks. The continued-fraction statement
below is coefficientwise and has no analytic convergence assumption.
-/

@[expose] public section

open Polynomial MeasureTheory

noncomputable section

namespace DLMF.OrthogonalPolynomials

/-- The finite Jacobi matrix, with diagonal `α` and off-diagonal `√β`.
Andrews–Askey–Roy, *Special Functions*, §5.8, Lemma 5.8.1
(synopsis AAR-5.8.1–5.8.2). -/
def jacobiTruncation (α β : ℕ → ℝ) (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  fun i j => if i = j then α i else if i.val + 1 = j.val then Real.sqrt (β j)
    else if j.val + 1 = i.val then Real.sqrt (β i) else 0

/-- Entries of the finite Jacobi matrix. -/
theorem jacobiTruncation_apply (α β : ℕ → ℝ) (N : ℕ) (i j : Fin (N + 1)) :
    jacobiTruncation α β N i j =
      if i = j then α i else if i.val + 1 = j.val then Real.sqrt (β j)
      else if j.val + 1 = i.val then Real.sqrt (β i) else 0 := rfl

/-- A moment of a probability measure is the `(0,0)` entry of a Jacobi-matrix power.
Andrews–Askey–Roy, *Special Functions*, Lemma 5.8.1, p. 267
(synopsis AAR-5.8.1–5.8.2). Truncation at `k` retains every length-`k` walk from zero. -/
theorem moment_eq_jacobiTruncation_pow {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {p : ℕ → ℝ[X]} (h : IsOrthogonalPolynomials μ p)
    (hmonic : ∀ n, (p n).Monic) {α β : ℕ → ℝ}
    (hβ : ∀ n, 0 < β (n + 1))
    (hfirst : p 1 = X - C (α 0))
    (hrec : ∀ n, p (n + 2) = (X - C (α (n + 1))) * p (n + 1) -
      C (β (n + 1)) * p n) (k : ℕ) :
    moment μ k = (jacobiTruncation α β k ^ k) 0 0 := by
  sorry

/-- Finite Jacobi continued fractions as formal power series. The last tail is one.
Andrews–Askey–Roy, *Special Functions*, §5.8, Theorem 5.8.2
(synopsis AAR-5.8.1–5.8.2). -/
def jacobiMomentFraction (α β : ℕ → ℝ) : ℕ → ℕ → PowerSeries ℝ
  | 0, _ => 1
  | depth + 1, n => (1 - PowerSeries.C (α n) * PowerSeries.X -
      PowerSeries.C (β (n + 1)) * PowerSeries.X ^ 2 *
        jacobiMomentFraction α β depth (n + 1))⁻¹

/-- The zero-depth Jacobi fraction. -/
@[simp] theorem jacobiMomentFraction_zero (α β : ℕ → ℝ) (n : ℕ) :
    jacobiMomentFraction α β 0 n = 1 := rfl

/-- The formal Jacobi fraction recursion. -/
theorem jacobiMomentFraction_succ (α β : ℕ → ℝ) (depth n : ℕ) :
    jacobiMomentFraction α β (depth + 1) n =
      (1 - PowerSeries.C (α n) * PowerSeries.X -
        PowerSeries.C (β (n + 1)) * PowerSeries.X ^ 2 *
          jacobiMomentFraction α β depth (n + 1))⁻¹ := rfl

/-- Each coefficient of the formal moment fraction stabilizes to the corresponding moment.
Andrews–Askey–Roy, *Special Functions*, Theorem 5.8.2, p. 269
(synopsis AAR-5.8.1–5.8.2). -/
theorem coeff_jacobiMomentFraction_eq_moment {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {p : ℕ → ℝ[X]} (h : IsOrthogonalPolynomials μ p)
    (hmonic : ∀ n, (p n).Monic) {α β : ℕ → ℝ}
    (hβ : ∀ n, 0 < β (n + 1))
    (hfirst : p 1 = X - C (α 0))
    (hrec : ∀ n, p (n + 2) = (X - C (α (n + 1))) * p (n + 1) -
      C (β (n + 1)) * p n) (k depth : ℕ) (hdepth : k ≤ depth) :
    PowerSeries.coeff k (jacobiMomentFraction α β depth 0) = moment μ k := by
  sorry

end DLMF.OrthogonalPolynomials
