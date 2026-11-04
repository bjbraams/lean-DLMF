/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.GeneralizedHypergeometric.Basic.ParametersAndSeries
public import DLMF.Hypergeometric.Basic.PrincipalBranch

/-!
# Normalized principal continuation of generalized hypergeometric functions

## Main definitions

* `PrincipalContinuation`: a normalized regularized continuation for `p = q + 1`.
* `regularizedGeneralizedHypergeometric`: the regularized principal function, DLMF 16.2.5; for
  `p > q + 1` it is only the totalized series, and Barnes values should be used instead.
* `generalizedHypergeometric`: the ordinary principal function, valid for regular lower parameters.
* `generalizedHypergeometricLower`: values on the lower side of the cut.
-/

@[expose] public noncomputable section

open Complex Filter Set Polynomial
open scoped Real Nat Topology ENNReal Interval

namespace DLMF.Hypergeometric

/-- A normalized regularized continuation for `p=q+1`; its existence is acquired explicitly. -/
structure PrincipalContinuation (a b : Multiset ℂ) where
  /-- Principal values, with an upper-side cut convention. -/
  value : ℂ → ℂ
  /-- Analytic continuation on the plane cut from one to positive infinity. -/
  analytic : AnalyticOnNhd ℂ value cutPlane
  /-- The original germ on the open unit disk. -/
  germ : ∀ z, ‖z‖ < 1 → value z = Complex.regularizedHGFun a b z
  /-- Upper cut values away from the singular endpoint. -/
  upper_boundary : ∀ x : ℝ, 1 < x →
    Tendsto value (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 (value x))
  /-- At the endpoint only the totalized series value is retained; convergence is separate. -/
  one : value 1 = Complex.regularizedHGFun a b 1

/-- Regularized principal generalized hypergeometric function.
For `p>q+1` this expression retains only the totalized series; use Barnes values instead.
The guarded choice keeps local series facts independent of the separate existence admission. -/
@[dlmf 16.2.E5]
def regularizedGeneralizedHypergeometric (a b : Multiset ℂ) (z : ℂ) : ℂ := by
  classical
  exact if a.card = b.card + 1 then
    if hF : Nonempty (PrincipalContinuation a b) then (Classical.choice hF).value z
    else Complex.regularizedHGFun a b z
  else Complex.regularizedHGFun a b z

/-- Ordinary principal generalized hypergeometric values, valid for regular lower parameters. -/
def generalizedHypergeometric (a b : Multiset ℂ) (z : ℂ) : ℂ := gammaProduct b *
    regularizedGeneralizedHypergeometric a b z

/-- Lower-side principal cut values; conjugate the parameters as well as the variable. -/
def generalizedHypergeometricLower (a b : Multiset ℂ) (z : ℂ) : ℂ :=
  star (generalizedHypergeometric (a.map star) (b.map star) (star z))

end DLMF.Hypergeometric
