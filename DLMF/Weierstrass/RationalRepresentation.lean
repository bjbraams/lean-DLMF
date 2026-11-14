/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Weierstrass.Basic
public import DLMFMathlib.Analysis.Complex.EllipticDivisors
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Rational representation of elliptic functions

Temme, *Special Functions* (1996), Exercise 12.6, p. 331,
synopsis TEM-12-10. A common polynomial denominator expresses the
meromorphic identity without evaluating independently singular factors.
-/

@[expose] public noncomputable section
open Complex PeriodPair
namespace DLMF.Weierstrass

/-- Every elliptic function is rational in `℘` and `℘'`,
Temme Exercise 12.6, synopsis TEM-12-10. The common regular locus is stated
explicitly because a meromorphic function's assigned values at its poles are arbitrary. -/
theorem exists_polynomial_weierstrass_representation (L : PeriodPair) (f : ℂ → ℂ)
    (hf : Meromorphic f) (hper : ∀ w ∈ L.lattice, Function.Periodic f w) :
    ∃ A B C : Polynomial ℂ, C ≠ 0 ∧
      (∃ z, z ∉ L.lattice ∧ AnalyticAt ℂ f z ∧ C.eval (℘[L] z) ≠ 0) ∧
      ∀ z, z ∉ L.lattice → AnalyticAt ℂ f z → C.eval (℘[L] z) ≠ 0 →
        f z = (A.eval (℘[L] z) + deriv (fun w => ℘[L] w) z * B.eval (℘[L] z)) /
          C.eval (℘[L] z) := by
  sorry

end DLMF.Weierstrass
