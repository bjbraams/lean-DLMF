/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.BigOperators.Fin

/-!
# A zero-free parabola for a three-term recurrence

Andrews, Askey and Roy, *Special Functions*, Theorem 4.16.1, pp. 231–233
(synopsis AAR-4.14.1–4.16.4). This is the general recurrence theorem,
rather than just its power-series partial-sum specialization.
-/

@[expose] public noncomputable section
namespace Complex

/-- Saff–Varga's zero-free parabola for all retained recurrence polynomials.
Andrews–Askey–Roy, Theorem 4.16.1. A positive lower bound for the printed minimum
is equivalent and avoids a special convention when the index set is empty. -/
theorem recurrence_ne_zero_of_mem_parabolicRegion {p : ℤ → ℂ → ℂ}
    {b c : ℕ → ℝ} {N : ℕ} {alpha : ℝ}
    (hneg : ∀ z, p (-1) z = 0) (hzero : ∃ a : ℂ, a ≠ 0 ∧ ∀ z, p 0 z = a)
    (hbzero : b 0 = 0) (hpositive : ∀ k ∈ Finset.Icc 1 N, 0 < b k ∧ 0 < c k)
    (hrec : ∀ k ∈ Finset.Icc 1 N, ∀ z,
      p (k : ℤ) z = (1 + z / b k) * p ((k : ℤ) - 1) z -
        (z / c k) * p ((k : ℤ) - 2) z)
    (halpha : 0 < alpha)
    (hbound : ∀ k ∈ Finset.Icc 1 N, alpha ≤ b k * (1 - b (k - 1) / c k))
    {z : ℂ} (hz : z.im ^ 2 < 4 * alpha * (z.re + alpha)) :
    ∀ k ≤ N, p (k : ℤ) z ≠ 0 := by
  sorry

end Complex
