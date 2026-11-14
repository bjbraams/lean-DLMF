/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.UniformSpace.UniformConvergence
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Picard series for a complex second-order normal equation

Kristensson, *Second Order Differential Equations*, Chapter 2, Theorem 2.2 and
Lemmas 2.3–2.6, pp. 7–9. The kernel is integrated along the straight segment
from the initial point to the argument. This file records the construction and
its quantitative majorants, not merely abstract ordinary-point existence.
-/

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology BigOperators

noncomputable section

namespace Complex.PicardSeries

/-- Kristensson, §2.2, pp. 7–9: the successive Picard terms for `u″+q u=0`,
with `u₀(z)=a₀+a₁(z-b)` and `u_{n+1}(z)=∫_[b,z](ζ-z)q(ζ)u_n(ζ)dζ`.
The displayed real integral parametrizes that complex segment. -/
def term (q : ℂ → ℂ) (b a₀ a₁ : ℂ) : ℕ → ℂ → ℂ
  | 0 => fun z => a₀ + a₁ * (z - b)
  | n + 1 => fun z => (z - b) ^ 2 * ∫ s : ℝ in 0..1,
      ((s : ℂ) - 1) * q (b + s * (z - b)) * term q b a₀ a₁ n (b + s * (z - b))

/-- The initial affine Picard term, Kristensson, §2.2. -/
@[simp] theorem term_zero (q : ℂ → ℂ) (b a₀ a₁ z : ℂ) :
    term q b a₀ a₁ 0 z = a₀ + a₁ * (z - b) := rfl

/-- The segment-integral recursion for the Picard terms, Kristensson, §2.2. -/
theorem term_add_one (q : ℂ → ℂ) (b a₀ a₁ : ℂ) (n : ℕ) (z : ℂ) :
    term q b a₀ a₁ (n + 1) z = (z - b) ^ 2 * ∫ s : ℝ in 0..1,
      ((s : ℂ) - 1) * q (b + s * (z - b)) * term q b a₀ a₁ n (b + s * (z - b)) := rfl

/-- Every positive-order Picard term vanishes at the initial point,
Kristensson, Lemmas 2.3–2.4. -/
@[simp] theorem term_add_one_initial (q : ℂ → ℂ) (b a₀ a₁ : ℂ) (n : ℕ) :
    term q b a₀ a₁ (n + 1) b = 0 := by simp [term]

/-- Kristensson, Lemmas 2.3–2.4, pp. 7–8: the factorial Picard majorant on
a closed disc. Both majorant constants are nonnegative. -/
theorem norm_term_le {q : ℂ → ℂ} {b a₀ a₁ : ℂ} {r M μ : ℝ}
    (hr : 0 < r) (hM : 0 ≤ M) (hμ : 0 ≤ μ)
    (hq : AnalyticOnNhd ℂ q (Metric.closedBall b r))
    (hbound : ∀ z ∈ Metric.closedBall b r, ‖q z‖ ≤ M)
    (hinit : ∀ z ∈ Metric.closedBall b r, ‖a₀ + a₁ * (z - b)‖ ≤ μ)
    (n : ℕ) {z : ℂ} (hz : z ∈ Metric.closedBall b r) :
    ‖term q b a₀ a₁ n z‖ ≤ μ * M ^ n * ‖z - b‖ ^ (2 * n) / n.factorial := by
  sorry

/-- Kristensson, Lemmas 2.3–2.5, pp. 7–9: each Picard term is analytic inside
the disc where its coefficient is analytic. -/
theorem analyticOnNhd_term {q : ℂ → ℂ} {b : ℂ} {r : ℝ}
    (hq : AnalyticOnNhd ℂ q (Metric.ball b r)) (a₀ a₁ : ℂ) (n : ℕ) :
    AnalyticOnNhd ℂ (term q b a₀ a₁ n) (Metric.ball b r) := by
  sorry

/-- Kristensson, Lemma 2.5, p. 8: differentiating a Picard term removes the
linear kernel, with the prescribed negative sign. -/
theorem deriv_term_add_one {q : ℂ → ℂ} {b a₀ a₁ z : ℂ} {r : ℝ}
    (hq : AnalyticOnNhd ℂ q (Metric.ball b r)) (hz : z ∈ Metric.ball b r) (n : ℕ) :
    deriv (term q b a₀ a₁ (n + 1)) z =
      -(z - b) * ∫ s : ℝ in 0..1,
        q (b + s * (z - b)) * term q b a₀ a₁ n (b + s * (z - b)) := by
  sorry

/-- Kristensson, Lemma 2.5, p. 8: the second derivative of the next Picard
term is minus the coefficient times the current term. -/
theorem deriv_deriv_term_add_one {q : ℂ → ℂ} {b a₀ a₁ z : ℂ} {r : ℝ}
    (hq : AnalyticOnNhd ℂ q (Metric.ball b r)) (hz : z ∈ Metric.ball b r) (n : ℕ) :
    deriv (deriv (term q b a₀ a₁ (n + 1))) z = -q z * term q b a₀ a₁ n z := by
  sorry

/-- Kristensson, Theorem 2.2: the Picard series defining the analytic solution.
Its convergence and differential equation are asserted separately. -/
def solution (q : ℂ → ℂ) (b a₀ a₁ z : ℂ) : ℂ := ∑' n, term q b a₀ a₁ n z

/-- The series formula for the Picard solution, Kristensson, Theorem 2.2. -/
theorem solution_def (q : ℂ → ℂ) (b a₀ a₁ z : ℂ) :
    solution q b a₀ a₁ z = ∑' n, term q b a₀ a₁ n z := rfl

/-- Kristensson, Lemma 2.6 and Theorem 2.2, p. 9: uniform convergence of the
Picard series on a closed disc contained in the analytic coefficient domain. -/
theorem tendstoUniformlyOn_sum_range_term {q : ℂ → ℂ} {b : ℂ} {r : ℝ}
    (hr : 0 < r) (hq : AnalyticOnNhd ℂ q (Metric.closedBall b r)) (a₀ a₁ : ℂ) :
    TendstoUniformlyOn (fun N z => ∑ n ∈ Finset.range N, term q b a₀ a₁ n z)
      (solution q b a₀ a₁) atTop (Metric.closedBall b r) := by
  sorry

/-- Kristensson, Theorem 2.2, p. 9: the summed Picard series is analytic and
satisfies the normal differential equation with the prescribed initial data. -/
theorem solution_properties {q : ℂ → ℂ} {b : ℂ} {r : ℝ}
    (hr : 0 < r) (hq : AnalyticOnNhd ℂ q (Metric.closedBall b r)) (a₀ a₁ : ℂ) :
    AnalyticOnNhd ℂ (solution q b a₀ a₁) (Metric.ball b r) ∧
      solution q b a₀ a₁ b = a₀ ∧ deriv (solution q b a₀ a₁) b = a₁ ∧
      ∀ z ∈ Metric.ball b r,
        deriv (deriv (solution q b a₀ a₁)) z + q z * solution q b a₀ a₁ z = 0 := by
  sorry

end Complex.PicardSeries
