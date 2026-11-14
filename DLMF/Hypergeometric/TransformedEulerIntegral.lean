/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Basic.CutPlane

/-!
# Euler's integral on the ray from one to infinity

The substitution `t = 1/u` gives the transformed Euler representation on the
entire principal cut plane. Both endpoint conditions are retained, and absolute
integrability is stated separately. Source: Kristensson, *Second Order
Differential Equations*, Chapter 5, Corollary 5.2, p. 79.
-/

@[expose] public noncomputable section

open Complex MeasureTheory Set
open scoped Real

namespace DLMF.Hypergeometric

/-- Absolute integrability of the Euler kernel after the substitution `t=1/u`.
The lower endpoint has exponent `c-b-1`, while the tail has exponent `-b-1`.
Kristensson, Chapter 5, Corollary 5.2, p. 79. -/
theorem integrableOn_transformedEulerKernel {a b c z : ℂ}
    (hb : 0 < b.re) (hcb : 0 < (c - b).re) (hz : z ∈ cutPlane) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (a - c) *
      ((t : ℂ) - 1) ^ (c - b - 1) * ((t : ℂ) - z) ^ (-a)) (Ioi 1) := by
  sorry

/-- The transformed Euler integral for the principal regularized Gauss function.
Multiplying by `Gamma(c)` gives the ordinary book normalization. All powers use
the principal logarithm; the cut-plane hypothesis keeps `t-z` off its cut for
`t>1`. Kristensson, Chapter 5, Corollary 5.2, p. 79. -/
theorem regularizedGaussHypergeometric_eq_integral_Ioi_one {a b c z : ℂ}
    (hb : 0 < b.re) (hcb : 0 < (c - b).re) (hz : z ∈ cutPlane) :
    regularizedGaussHypergeometric a b c z =
      (∫ t : ℝ in Ioi 1, (t : ℂ) ^ (a - c) *
        ((t : ℂ) - 1) ^ (c - b - 1) * ((t : ℂ) - z) ^ (-a)) /
          (Gamma b * Gamma (c - b)) := by
  sorry

end DLMF.Hypergeometric
