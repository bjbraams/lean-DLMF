/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Gamma.RationalSeries
public import DLMF.Gamma.Basic.RealDigamma

/-!
# Rational-function series from polynomial residues

Duverney, *An Introduction to Hypergeometric Functions*, Chapter 2,
equations (2.30)–(2.35). The denominator is factored into distinct real roots,
none of them a natural number. The degree gap removes the non-summable `1/n` term.
-/

@[expose] public noncomputable section

open Polynomial Finset

namespace DLMF.Gamma

/-- A rational series with distinct real poles is evaluated by digamma values at the
negated poles. Duverney (2.30)–(2.35), synopsis DU-2.10.
The polynomial factorization explicitly records all denominator roots with multiplicity one. -/
theorem hasSum_polynomial_div_of_distinct_real_roots (P Q : ℝ[X]) (hQ : Q ≠ 0)
    {m : ℕ} (a : Fin m → ℝ) (ha : Function.Injective a)
    (hfactor : Q = C Q.leadingCoeff * ∏ i : Fin m, (X - C (a i)))
    (hdegree : P.degree + 2 ≤ Q.degree)
    (hnat : ∀ i : Fin m, ∀ n : ℕ, a i ≠ (n : ℝ)) :
    (∑ i : Fin m, P.eval (a i) / Q.derivative.eval (a i)) = 0 ∧
      HasSum (fun n : ℕ => P.eval (n : ℝ) / Q.eval (n : ℝ))
        (-(∑ i : Fin m, P.eval (a i) / Q.derivative.eval (a i) *
          Real.digamma (-a i))) := by
  sorry

end DLMF.Gamma
