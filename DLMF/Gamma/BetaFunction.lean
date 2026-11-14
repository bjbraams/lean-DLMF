/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Gamma.BetaFunction.ComplexTrigonometric

public import DLMF.Gamma.BetaFunction.ParameterIntegrals
public import DLMF.Gamma.BetaFunction.Cosine
public import DLMF.Gamma.BetaFunction.Vertical

/-!
# Beta function (DLMF §5.12)

This umbrella collects the trigonometric, half-line, shifted, cosine, hyperbolic and vertical
Beta integrals of DLMF 5.12.2–5.12.8. The Euler integral and the identity
`B(a,b) = Γ(a)Γ(b)/Γ(a+b)` (5.12.1) are Mathlib's `betaIntegral` and
`Gamma_mul_Gamma_eq_betaIntegral`, and also `selberg_integral_one` in
`DLMF.Selberg.ContinuationAndAomoto`. The contour integrals 5.12.9–5.12.12 are not formalized.
-/
