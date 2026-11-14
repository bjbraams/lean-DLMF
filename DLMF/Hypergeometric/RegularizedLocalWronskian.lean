/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Basic.GaussEquation
public import DLMF.Hypergeometric.Basic.CutPlane
public import DLMFMathlib.Analysis.ODE.Wronskian

/-!
# The regularized Gauss local-pair Wronskian for every lower parameter

Olver, *Asymptotics and Special Functions*, Chapter 5, §10,
pp. 163–168, synopsis O-5.15. The ordinary-pair Wronskian must be divided
by both Gamma normalizations. Its sine coefficient then extends to every
integer lower parameter without independent evaluation of Gamma poles.
-/

@[expose] public noncomputable section

open Complex
open scoped Real

namespace DLMF.Hypergeometric

/-- The regularized zero-basis Wronskian on its full common principal branch domain.
All parameters are retained, including the vanishing Wronskian at integer `c`.
Olver, Chapter 5, §10, pp. 163–168, synopsis O-5.15. -/
theorem wronskian_regularizedGauss_zero_pair (a b c : ℂ) {z : ℂ}
    (hz : z ∈ slitPlane) (h₁z : 1 - z ∈ slitPlane) :
    ODE.wronskian (regularizedGaussHypergeometric a b c)
      (fun w => w ^ (1 - c) *
        regularizedGaussHypergeometric (a - c + 1) (b - c + 1) (2 - c) w) z =
      sin (π * c) / π * z ^ (-c) * (1 - z) ^ (c - a - b - 1) := by
  sorry

end DLMF.Hypergeometric
