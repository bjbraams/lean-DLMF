/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.BernoulliEuler.Basic.HigherOrder

/-!
# Bernoulli and Euler polynomials of complex order

Temme, *Special Functions* (1996), §§1.1 and 1.3, synopsis TEM-01-01 and
TEM-01-11. Finite polynomial formulas extend the natural-order definitions
without identifying an arbitrary principal logarithm with the normalized local branch.
-/

@[expose] public noncomputable section
open Polynomial Finset
open scoped Nat
namespace DLMF.BernoulliEuler.ComplexOrder

/-- The Bernoulli polynomial `B_n^(σ)(x)` for complex order `σ`, Temme §1.1,
(1.1)–(1.3), synopsis TEM-01-01. The order coefficients reuse the canonical
Nörlund polynomials. -/
def bernoulliPolynomial (σ : ℂ) (n : ℕ) : Polynomial ℂ :=
  ∑ k ∈ range (n + 1), C ((n.choose k : ℂ) *
    (norlundPolynomial k).eval₂ (algebraMap ℚ ℂ) σ) * X ^ (n - k)

/-- The Euler polynomial `E_n^(σ)(x)` for complex order `σ`, Temme §1.3,
(1.24), synopsis TEM-01-11. The coefficients come from the finite binomial
expansion of the formal series `2/(exp t+1)`. -/
def eulerPolynomial (σ : ℂ) (n : ℕ) : Polynomial ℂ :=
  ∑ k ∈ range (n + 1), C ((n.choose k : ℂ) * k.factorial *
    (binomialSeriesCoeff (eulerPowerSeries - 1) k).eval₂ (algebraMap ℚ ℂ) σ) * X ^ (n - k)

/-- The finite coefficient formula defining complex-order Bernoulli polynomials,
Temme (1.1)–(1.3). -/
theorem bernoulliPolynomial_def (σ : ℂ) (n : ℕ) : bernoulliPolynomial σ n =
    ∑ k ∈ range (n + 1), C ((n.choose k : ℂ) *
      (norlundPolynomial k).eval₂ (algebraMap ℚ ℂ) σ) * X ^ (n - k) := rfl

/-- The finite coefficient formula defining complex-order Euler polynomials,
Temme (1.24). -/
theorem eulerPolynomial_def (σ : ℂ) (n : ℕ) : eulerPolynomial σ n =
    ∑ k ∈ range (n + 1), C ((n.choose k : ℂ) * k.factorial *
      (binomialSeriesCoeff (eulerPowerSeries - 1) k).eval₂ (algebraMap ℚ ℂ) σ) * X ^ (n - k) := rfl

end DLMF.BernoulliEuler.ComplexOrder
