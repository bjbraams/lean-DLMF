/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Gamma.BetaFunction.ParameterIntegrals
public import DLMF.Gamma.BetaFunction.Cosine
public import DLMF.Gamma.BetaFunction.Vertical

/-!
# Beta function (DLMF §5.12)

The Euler integral and the identity `B(a,b) = Γ(a)Γ(b)/Γ(a+b)` are Mathlib
`betaIntegral` and `Gamma_mul_Gamma_eq_betaIntegral`, and are also
`selberg_integral_one` in `DLMF.Selberg.Basic`. The trigonometric integrals 5.12.5–5.12.6 use
Mathlib's binomial series (`Complex.one_add_cpow_hasFPowerSeriesOnBall_zero`). Contour
formulae 5.12.9–5.12.12 are deferred. The real Euler integral uses the Tau Ceti contributors’
`TauCeti.integral_rpow_mul_one_sub_rpow`, built on Mathlib’s beta theory.
-/
