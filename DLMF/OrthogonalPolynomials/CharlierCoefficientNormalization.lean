/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Hahn.CharlierAndConnections
public import DLMFMathlib.RingTheory.Binomial

/-!
# Charlier polynomials in coefficient normalization

Duverney, *An Introduction to Hypergeometric Functions*, Exercise 9.14,
uses the coefficient of `tⁿ` in `exp(-μt)(1+t)^x`, rather than the DLMF
normalization. The factor is `(-μ)ⁿ/n!`; the canonical Charlier function is reused.
-/

@[expose] public noncomputable section

open Complex Finset

namespace DLMF.OrthogonalPolynomials

/-- The finite coefficient formula is the scaled canonical Charlier polynomial.
Duverney Exercise 9.14, synopsis DU-9.19. -/
theorem charlier_coefficient_eq_sum {μ : ℝ} (hμ : 0 < μ) (n : ℕ) (x : ℝ) :
    ((-μ : ℂ) ^ n / n.factorial) * charlier μ n x =
      ∑ k ∈ range (n + 1), (Ring.choose x k : ℂ) * (-μ : ℂ) ^ (n - k) /
        (n - k).factorial := by
  sorry

/-- The Charlier generating function for arbitrary real arguments in coefficient
normalization. Duverney Exercise 9.14, synopsis DU-9.19. -/
theorem hasSum_charlier_coefficient {μ : ℝ} (hμ : 0 < μ) (x : ℝ) {t : ℝ}
    (ht : |t| < 1) :
    HasSum (fun n : ℕ => ((-μ : ℂ) ^ n / n.factorial) * charlier μ n x * (t : ℂ) ^ n)
      ((Real.exp (-μ * t) * (1 + t) ^ x : ℝ) : ℂ) := by
  sorry

end DLMF.OrthogonalPolynomials
