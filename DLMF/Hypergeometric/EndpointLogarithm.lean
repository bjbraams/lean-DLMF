/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.ArgumentContinuation
public import DLMF.Hypergeometric.LogConnectionsRecipGamma

/-!
# The zero-excess logarithmic limit at one

Duverney, *An Introduction to Hypergeometric Functions*, Chapter 4, Theorem 4.11,
equation (4.61). Reciprocal gamma factors retain the limit also at exceptional upper
parameters; the source's ordinary statement follows by multiplication by `Γ(a+b)`.
-/

@[expose] public noncomputable section

open Complex Filter
open scoped Topology

namespace DLMF.Hypergeometric

/-- The zero-excess regularized Gauss function has logarithmic coefficient
`-1/(Γ(a)Γ(b))` at one. Duverney Theorem 4.11, (4.61), synopsis DU-4.15.
The reciprocal-gamma formulation includes exceptional upper parameters. -/
theorem tendsto_regularizedGaussHypergeometric_div_log_left_one (a b : ℂ) :
    Tendsto (fun x : ℝ => regularizedGaussHypergeometric a b (a + b) x /
      (Real.log (1 - x) : ℂ)) (𝓝[<] 1) (𝓝 (-(Gamma a * Gamma b)⁻¹)) := by
  sorry

end DLMF.Hypergeometric
