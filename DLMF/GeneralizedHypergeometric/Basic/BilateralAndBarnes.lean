/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.GeneralizedHypergeometric.Basic.PrincipalContinuation

/-!
# Bilateral series and logarithmic Barnes integrals

## Main definitions

* `pochhammerOfInt`: the rising factorial at an integer index.
* `bilateralHypergeometricCoeff`, `bilateralHypergeometric`: the bilateral series, DLMF 16.4.16,
  totalized outside its convergence regime.
* `barnesKernelLog`: the Mellin–Barnes kernel on the logarithm sheet `w = Log(-z)`.
* `HasBarnesValueLog`, `barnesHypergeometricLog`: convergence of a Barnes contour integral and its
  (totalized) value.

## Implementation notes

Every use of `barnesHypergeometricLog` asserts convergence separately with `HasBarnesValueLog`.
-/

@[expose] public noncomputable section

open Complex Filter Set Polynomial
open scoped Real Nat Topology ENNReal Interval

namespace DLMF.Hypergeometric

/-- Rising factorial at an integer index; negative indices use the reciprocal continuation.
At singular parameters this expression is totalized, so analytic formulas state exclusions. -/
def pochhammerOfInt (a : ℂ) (n : ℤ) : ℂ :=
  if 0 ≤ n then pochhammer a n.toNat else (pochhammer (a + n) (-n).toNat)⁻¹

/-- Formal bilateral hypergeometric coefficient, with no factorial factor (16.4.16). -/
@[dlmf 16.4.E16]
def bilateralHypergeometricCoeff (a b : Multiset ℂ) (n : ℤ) : ℂ :=
  (a.map fun x => pochhammerOfInt x n).prod / (b.map fun x => pochhammerOfInt x n).prod

/-- Totalized bilateral series. Outside an explicitly proved convergence regime this is
only a formal-series interface, not an analytically continued function (16.4.16). -/
@[dlmf 16.4.E16]
def bilateralHypergeometric (a b : Multiset ℂ) (z : ℂ) : ℂ :=
  ∑' n : ℤ, bilateralHypergeometricCoeff a b n * z ^ n

/-- Mellin–Barnes kernel on the logarithm sheet `w=Log(-z)`. -/
def barnesKernelLog (a b : Multiset ℂ) (w s : ℂ) : ℂ :=
  gammaProduct (shiftParameters a s) / gammaProduct (shiftParameters b s) * Gamma (-s) *
      Complex.exp (s * w)

/-- A convergent contour-defined ordinary pFq value, separate from the divergent formal
series. Both contour tails converge separately; the log sheet of `-z` is explicit. -/
def HasBarnesValueLog (a b : Multiset ℂ) (L : ℝ → ℂ) (w v : ℂ) : Prop :=
  DLMF.Core.HasIntegralWholeLine (fun t => deriv L t * barnesKernelLog a b w (L t))
    (2 * Real.pi * I * gammaProduct a / gammaProduct b * v)

/-- Totalized value of a Barnes contour. Every mathematical use asserts its separate
convergence with `HasBarnesValueLog` and excludes poles in the parameter prefactor. -/
def barnesHypergeometricLog (a b : Multiset ℂ) (L : ℝ → ℂ) (w : ℂ) : ℂ :=
  gammaProduct b / (2 * Real.pi * I * gammaProduct a) *
    limUnder atTop (fun T : ℝ =>
      ∫ t in (-T)..T, deriv L t * barnesKernelLog a b w (L t))

end DLMF.Hypergeometric
