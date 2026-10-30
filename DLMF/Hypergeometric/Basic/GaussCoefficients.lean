/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Basic.Pochhammer
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.Analysis.SpecialFunctions.Complex.Arctan

/-!
# Coefficients of the ordinary Gauss series
-/

@[expose] public noncomputable section

open Complex Filter Set Polynomial
open scoped Real Nat Topology ENNReal Interval

namespace DLMF.Hypergeometric

/-- The coefficient of `z^n` in `₂F₁(a,b;c;z)`. -/
def gaussHGCoeff (a b c : ℂ) (n : ℕ) : ℂ :=
  poch a n * poch b n / (poch c n * n !)
/-- Mathlib's `ordinaryHypergeometricCoefficient` agrees with the project coefficient
  `gaussHGCoeff`. -/
theorem ordinaryHypergeometricCoefficient_eq (a b c : ℂ) (n : ℕ) :
    ordinaryHypergeometricCoefficient a b c n = gaussHGCoeff a b c n := by
  simp [ordinaryHypergeometricCoefficient, gaussHGCoeff, poch, div_eq_mul_inv, mul_assoc,
    mul_left_comm, mul_comm]

end DLMF.Hypergeometric
