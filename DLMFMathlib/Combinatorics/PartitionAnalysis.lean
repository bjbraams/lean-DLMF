/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.RingTheory.MvPowerSeries.Inverse

/-!
# MacMahon's Omega extraction and rational elimination

Andrews, Askey and Roy, *Special Functions*, §§11.2–11.3. Every coefficient in
the ordinary size variables is a Laurent polynomial in the auxiliary variable,
so extraction involves a finite sum. `invOfUnit` uses the known unit constant
coefficient of the displayed rational denominators.
-/

@[expose] public section

open Finset
open scoped Classical

noncomputable section

namespace LaurentPolynomial

/-- Retain nonnegative Laurent exponents and evaluate the auxiliary variable at one.
Andrews–Askey–Roy, *Special Functions*, §11.2 (synopsis AAR-11.1.1–11.3.1). -/
def nonnegativeCoefficientSum {R : Type*} [Semiring R] (f : LaurentPolynomial R) : R :=
  f.coeff.sum fun k a => if 0 ≤ k then a else 0

/-- The finite nonnegative-exponent extraction formula. -/
theorem nonnegativeCoefficientSum_def {R : Type*} [Semiring R]
    (f : LaurentPolynomial R) :
    nonnegativeCoefficientSum f = f.coeff.sum (fun k a => if 0 ≤ k then a else 0) := rfl

end LaurentPolynomial

namespace MvPowerSeries

/-- Omega extraction in one auxiliary Laurent variable, coefficientwise in all size
variables. Andrews–Askey–Roy, *Special Functions*, §11.2
(synopsis AAR-11.1.1–11.3.1). Iteration handles several auxiliary variables. -/
def omegaNonnegative {σ R : Type*} [Semiring R]
    (f : MvPowerSeries σ (LaurentPolynomial R)) : MvPowerSeries σ R :=
  fun n => LaurentPolynomial.nonnegativeCoefficientSum (coeff n f)

/-- Omega extraction acts on each size coefficient by the finite Laurent sum. -/
theorem coeff_omegaNonnegative {σ R : Type*} [Semiring R]
    (f : MvPowerSeries σ (LaurentPolynomial R)) (n : σ →₀ ℕ) :
    coeff n (omegaNonnegative f) = LaurentPolynomial.nonnegativeCoefficientSum (coeff n f) :=
  rfl

/-- The elementary two-factor Omega elimination. Andrews–Askey–Roy,
*Special Functions*, Lemma 11.2.1 (synopsis AAR-11.1.1–11.3.1). -/
theorem omegaNonnegative_geometric_two {R : Type*} [CommRing R] :
    omegaNonnegative
      (invOfUnit ((1 - C (LaurentPolynomial.T 1) * X (0 : Fin 2)) *
        (1 - C (LaurentPolynomial.T (-1)) * X (1 : Fin 2))) 1) =
      invOfUnit ((1 - X (0 : Fin 2)) * (1 - X (0 : Fin 2) * X (1 : Fin 2)) :
        MvPowerSeries (Fin 2) R) 1 := by
  sorry

/-- Omega extraction after a nonnegative negative Laurent shift.
Andrews–Askey–Roy, *Special Functions*, Lemmas 11.2.1–11.2.3
(synopsis AAR-11.1.1–11.3.1). -/
theorem omegaNonnegative_geometric_two_shift {R : Type*} [CommRing R] (a : ℕ) :
    omegaNonnegative
      (C (LaurentPolynomial.T (-(a : ℤ))) *
        invOfUnit ((1 - C (LaurentPolynomial.T 1) * X (0 : Fin 2)) *
          (1 - C (LaurentPolynomial.T (-1)) * X (1 : Fin 2))) 1) =
      X (0 : Fin 2) ^ a *
        invOfUnit ((1 - X (0 : Fin 2)) * (1 - X (0 : Fin 2) * X (1 : Fin 2)) :
          MvPowerSeries (Fin 2) R) 1 := by
  sorry

/-- One positive geometric factor and arbitrarily many negative geometric factors.
Andrews–Askey–Roy, *Special Functions*, Proposition 11.3.1
(synopsis AAR-11.1.1–11.3.1). -/
theorem omegaNonnegative_geometric_many {R : Type*} [CommRing R] (r : ℕ) :
    omegaNonnegative
      (invOfUnit ((1 - C (LaurentPolynomial.T 1) * X (0 : Fin (r + 1))) *
        ∏ j : Fin r, (1 - C (LaurentPolynomial.T (-1)) * X j.succ)) 1) =
      invOfUnit ((1 - X (0 : Fin (r + 1))) *
        ∏ j : Fin r, (1 - X (0 : Fin (r + 1)) * X j.succ) :
          MvPowerSeries (Fin (r + 1)) R) 1 := by
  sorry

/-- The three-factor Omega elimination with two positive auxiliary powers.
Andrews–Askey–Roy, *Special Functions*, Proposition 11.3.1
(synopsis AAR-11.1.1–11.3.1). -/
theorem omegaNonnegative_geometric_three {R : Type*} [CommRing R] :
    omegaNonnegative
      (invOfUnit ((1 - C (LaurentPolynomial.T 1) * X (0 : Fin 3)) *
        (1 - C (LaurentPolynomial.T 1) * X (1 : Fin 3)) *
        (1 - C (LaurentPolynomial.T (-1)) * X (2 : Fin 3))) 1) =
      (1 - X (0 : Fin 3) * X (1 : Fin 3) * X (2 : Fin 3)) *
        invOfUnit ((1 - X (0 : Fin 3)) * (1 - X (1 : Fin 3)) *
          (1 - X (0 : Fin 3) * X (2 : Fin 3)) *
          (1 - X (1 : Fin 3) * X (2 : Fin 3)) : MvPowerSeries (Fin 3) R) 1 := by
  sorry

/-- The quadratic-negative-power Omega elimination. Andrews–Askey–Roy,
*Special Functions*, Proposition 11.3.1 (synopsis AAR-11.1.1–11.3.1). -/
theorem omegaNonnegative_geometric_three_square {R : Type*} [CommRing R] :
    omegaNonnegative
      (invOfUnit ((1 - C (LaurentPolynomial.T 1) * X (0 : Fin 3)) *
        (1 - C (LaurentPolynomial.T 1) * X (1 : Fin 3)) *
        (1 - C (LaurentPolynomial.T (-2)) * X (2 : Fin 3))) 1) =
      (1 + X (0 : Fin 3) * X (1 : Fin 3) * X (2 : Fin 3) -
        X (0 : Fin 3) ^ 2 * X (1 : Fin 3) * X (2 : Fin 3) -
        X (0 : Fin 3) * X (1 : Fin 3) ^ 2 * X (2 : Fin 3)) *
        invOfUnit ((1 - X (0 : Fin 3)) * (1 - X (1 : Fin 3)) *
          (1 - X (0 : Fin 3) ^ 2 * X (2 : Fin 3)) *
          (1 - X (1 : Fin 3) ^ 2 * X (2 : Fin 3)) : MvPowerSeries (Fin 3) R) 1 := by
  sorry

end MvPowerSeries
