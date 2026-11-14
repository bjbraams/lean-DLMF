/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.BernoulliEuler.Basic.ComplexOrder
public import Mathlib.Algebra.Polynomial.Monic

/-!
# Polynomial parameters and degree of complex-order Bernoulli and Euler families

Temme, *Special Functions*, Chapter 1, (1.1)–(1.3), (1.24), pp. 3–4, 15–16.
The order parameter varies over all complex values, including exceptional integer orders.
-/

@[expose] public section

namespace DLMF.BernoulliEuler.ComplexOrder

/-- Generalized Bernoulli polynomials remain monic of degree `n` at every complex order.
Temme, *Special Functions*, Chapter 1, (1.1)–(1.3), synopsis TEM-01-01. -/
theorem monic_bernoulliPolynomial (σ : ℂ) (n : ℕ) :
    (bernoulliPolynomial σ n).Monic ∧ (bernoulliPolynomial σ n).natDegree = n := by
  sorry

/-- Every coefficient is a polynomial in the complex order, of the expected maximum degree.
Temme, *Special Functions*, Chapter 1, (1.1)–(1.3), synopsis TEM-01-01.
Thus the defining family is polynomial jointly in its argument and order. -/
theorem exists_polynomial_coeff_bernoulliPolynomial (n j : ℕ) :
    ∃ P : Polynomial ℂ, P.natDegree ≤ n - j ∧
      ∀ σ : ℂ, (bernoulliPolynomial σ n).coeff j = P.eval σ := by
  sorry

/-- Generalized Euler polynomials are monic of degree `n` at every complex order.
Temme, *Special Functions*, Chapter 1, (1.24), synopsis TEM-01-11. -/
theorem monic_eulerPolynomial (σ : ℂ) (n : ℕ) :
    (eulerPolynomial σ n).Monic ∧ (eulerPolynomial σ n).natDegree = n := by
  sorry

/-- Every generalized Euler coefficient is polynomial in its complex order.
Temme, *Special Functions*, Chapter 1, (1.24), synopsis TEM-01-11. -/
theorem exists_polynomial_coeff_eulerPolynomial (n j : ℕ) :
    ∃ P : Polynomial ℂ, P.natDegree ≤ n - j ∧
      ∀ σ : ℂ, (eulerPolynomial σ n).coeff j = P.eval σ := by
  sorry

end DLMF.BernoulliEuler.ComplexOrder
