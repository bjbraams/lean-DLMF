/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.GeneralizedHypergeometric.Basic.PrincipalContinuation

/-!
# Bilateral series and logarithmic Barnes integrals
-/

@[expose] public noncomputable section

open Complex Filter Set Polynomial
open scoped Real Nat Topology ENNReal Interval

namespace DLMF.Hypergeometric

/-- Rising factorial at an integer index; negative indices use the reciprocal continuation.
At singular parameters this expression is totalized, so analytic formulas state exclusions. -/
def genIntPoch (a : ℂ) (n : ℤ) : ℂ :=
  if 0 ≤ n then poch a n.toNat else (poch (a + n) (-n).toNat)⁻¹

/-- Formal bilateral hypergeometric coefficient, with no factorial factor (16.4.16). -/
@[dlmf 16.4.E16]
def genBilateralCoeff (a b : Multiset ℂ) (n : ℤ) : ℂ :=
  (a.map fun x => genIntPoch x n).prod / (b.map fun x => genIntPoch x n).prod

/-- Totalized bilateral series. Outside an explicitly proved convergence regime this is
only a formal-series interface, not an analytically continued function (16.4.16). -/
@[dlmf 16.4.E16]
def genBilateralHG (a b : Multiset ℂ) (z : ℂ) : ℂ :=
  ∑' n : ℤ, genBilateralCoeff a b n * z ^ n

/-- Mellin–Barnes kernel on the logarithm sheet `w=Log(-z)`. -/
def genBarnesKernelLog (a b : Multiset ℂ) (w s : ℂ) : ℂ :=
  genGamma (genShift a s) / genGamma (genShift b s) * Gamma (-s) * Complex.exp (s * w)

/-- A convergent contour-defined ordinary pFq value, separate from the divergent formal
series. Both contour tails converge separately; the log sheet of `-z` is explicit. -/
def genHasBarnesValueLog (a b : Multiset ℂ) (L : ℝ → ℂ) (w v : ℂ) : Prop :=
  DLMF.HasIntegralWholeLine (fun t => deriv L t * genBarnesKernelLog a b w (L t))
    (2 * Real.pi * I * genGamma a / genGamma b * v)

/-- Totalized value of a Barnes contour. Every mathematical use asserts its separate
convergence with `genHasBarnesValueLog` and excludes poles in the parameter prefactor. -/
def genBarnesHGLog (a b : Multiset ℂ) (L : ℝ → ℂ) (w : ℂ) : ℂ :=
  genGamma b / (2 * Real.pi * I * genGamma a) *
    limUnder atTop (fun T : ℝ =>
      ∫ t in (-T)..T, deriv L t * genBarnesKernelLog a b w (L t))

end DLMF.Hypergeometric
