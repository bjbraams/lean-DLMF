/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.BernoulliEuler.Basic

/-!
# Elementary Bernoulli and Euler bounds

Temme, *Special Functions*, Chapter 1, (1.15), p. 6, and p. 16.
The Euler bound retains the absolute value required by the alternating signs
of the Euler numbers and includes the entire closed interval.
-/

@[expose] public section

namespace DLMF.BernoulliEuler

/-- Elementary strict upper and lower bounds for the even Bernoulli numbers.
Temme, *Special Functions*, Chapter 1, (1.15), p. 6, synopsis TEM-01-04. -/
theorem bernoulli_two_mul_elementary_bounds {n : ℕ} (hn : 1 ≤ n) :
    2 / (2 * Real.pi) ^ (2 * n) < |(bernoulli (2 * n) : ℝ)| / (2 * n).factorial ∧
      |(bernoulli (2 * n) : ℝ)| / (2 * n).factorial < 4 / (2 * Real.pi) ^ (2 * n) := by
  sorry

/-- The absolute Euler-polynomial bound on the full closed unit interval.
Temme, *Special Functions*, Chapter 1, p. 16, synopsis TEM-01-12.
The absolute value of the Euler number corrects the printed sign error. -/
theorem abs_eulerFun_two_mul_le (n : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |eulerFun (2 * n) x| ≤ (4 : ℝ)⁻¹ ^ n * |(eulerNumber (2 * n) : ℝ)| := by
  sorry

end DLMF.BernoulliEuler
