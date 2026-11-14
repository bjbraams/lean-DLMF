/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.BernoulliEuler.Basic.ComplexOrder

/-!
# Generating functions for complex-order Bernoulli and Euler polynomials

Temme, *Special Functions* (1996), §§1.1 and 1.3, (1.1)–(1.3), (1.24).
Analytic logarithms are normalized at zero on the full disk of convergence.
-/

@[expose] public noncomputable section
open Complex Polynomial
open scoped Nat Real
namespace DLMF.BernoulliEuler.ComplexOrder

/-- Natural orders agree with the existing Bernoulli polynomials of higher order,
Temme §1.1, synopsis TEM-01-01. -/
theorem bernoulliPolynomial_natCast (ell n : ℕ) :
    bernoulliPolynomial ell n = (bernoulliOrder ell n).map (algebraMap ℚ ℂ) := by
  sorry

/-- Natural orders agree with the existing Euler polynomials of higher order,
Temme §1.3, synopsis TEM-01-11. -/
theorem eulerPolynomial_natCast (ell n : ℕ) :
    eulerPolynomial ell n = (eulerOrder ell n).map (algebraMap ℚ ℂ) := by
  sorry

/-- The full-disk complex-order Bernoulli generating function with its normalized
analytic logarithm, Temme (1.1)–(1.3), synopsis TEM-01-01. -/
theorem exists_bernoulli_generating_log :
    ∃ L : ℂ → ℂ, AnalyticOnNhd ℂ L (Metric.ball 0 (2 * Real.pi)) ∧ L 0 = 0 ∧
      (∀ t ∈ Metric.ball 0 (2 * Real.pi),
        exp (L t) = if t = 0 then 1 else t / (exp t - 1)) ∧
      ∀ σ x : ℂ, ∀ t ∈ Metric.ball 0 (2 * Real.pi),
        HasSum (fun n : ℕ => (bernoulliPolynomial σ n).eval x * t ^ n / n.factorial)
          (exp (x * t + σ * L t)) := by
  sorry

/-- The full-disk complex-order Euler generating function with its normalized
analytic logarithm, Temme (1.24), synopsis TEM-01-11. -/
theorem exists_euler_generating_log :
    ∃ L : ℂ → ℂ, AnalyticOnNhd ℂ L (Metric.ball 0 Real.pi) ∧ L 0 = 0 ∧
      (∀ t ∈ Metric.ball 0 Real.pi, exp (L t) = 2 / (exp t + 1)) ∧
      ∀ σ x : ℂ, ∀ t ∈ Metric.ball 0 Real.pi,
        HasSum (fun n : ℕ => (eulerPolynomial σ n).eval x * t ^ n / n.factorial)
          (exp (x * t + σ * L t)) := by
  sorry

end DLMF.BernoulliEuler.ComplexOrder
