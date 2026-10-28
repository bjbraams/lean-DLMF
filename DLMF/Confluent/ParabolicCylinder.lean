/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Confluent.ParabolicCylinder.EquationAndIntegrals
public import DLMF.Confluent.ParabolicCylinder.WronskiansAndConnections

/-!
# Parabolic cylinder functions (Temme §7.3.3; DLMF Chapter 12)

Weber's function `U(a,z)` is the solution of `w'' = (z²/4 + a) w` that is recessive as
`z → +∞`. We define it, following DLMF 12.4.1, through the even and odd Kummer solutions
`u₁(a,z) = e^{-z²/4} M(a/2 + 1/4, 1/2, z²/2)` and `u₂(a,z) = z e^{-z²/4} M(a/2 + 3/4, 3/2, z²/2)`
with the initial values 12.2.6 and 12.2.7. This makes `U(a, ·)` entire for every `a`.

## Main results

* `hasDerivAt_pcfU`, `hasDerivAt_pcfUDeriv`, `deriv_deriv_pcfU`: Weber's equation 12.2.2.
* `pcfU_zero`, `pcfUDeriv_zero`: the initial values.
* `pcfU_neg_half`: `U(-1/2, z) = e^{-z²/4}`.
* `pcfU_eq_kummerU`: `U(a,z) = 2^{-1/4-a/2} e^{-z²/4} U(a/2 + 1/4, 1/2, z²/2)` for `re z > 0`.
* `hasAsymptoticExpansion_pcfU`: `U(a,x) ~ e^{-x²/4} x^{-a-1/2} ∑ (-1)^s (a + 1/2)_{2s}/(s! (2x²)^s)`.
* `IsWeberSol.eq_of_initial`: solutions of Weber's equation are determined by `w(0), w'(0)`
  (via constancy of Wronskians against `u₁, u₂`).
* `pcfU_three_term`, `pcfU_recurrence_add`, `pcfU_recurrence_sub`, `pcfU_deriv_recurrence`:
  the recurrences 12.8.1–12.8.4.
* `pcfD_nat`: `D_n(z) = e^{-z²/4} He_n(z)` (12.7.2).
* `pcfU_eq_integral`: `U(a,z) = e^{-z²/4}/Γ(1/2+a) ∫₀^∞ t^{a-1/2} e^{-t²/2-zt} dt` (12.5.1).
* `pcfU_wronskian_neg`, `pcfU_wronskian_mul_I`, `pcfU_wronskian_mul_neg_I`: the Wronskians
  12.2.11–12.2.12.
* `pcfU_connection_mul_I`, `pcfU_connection_mul_neg_I`: the connection formula 12.2.17.
* `pcfV`: the second solution `V(a,z) = V(a,0) u₁ + V'(a,0) u₂` (12.4.2), entire in `a` and `z`,
  with `pcfV_zero`, `pcfVDeriv_zero` (12.2.8–12.2.9) and Weber's equation.
* `pcfV_wronskian`: `𝒲{U, V} = √(2/π)` (12.2.10).
* `pcfU_neg_eq`, `pcfV_neg_eq`: the connection formulas 12.2.15–12.2.16 for every `a`, with the
  parity cases `pcfU_neg_nat_sub_half_neg`, `pcfV_nat_add_half_neg` (12.2.13–12.2.14) and the
  classical form `pcfV_eq` of `V` in terms of `U(a, ±z)`.
* `pcfV_eq_mul_I`, `pcfV_eq_mul_neg_I`: the connection formula 12.2.20 for every `a`.
* `pcfV_three_term`, `pcfV_recurrence_sub`, `pcfV_recurrence_add`, `pcfV_deriv_recurrence`:
  the recurrences 12.8.5–12.8.8.

Whittaker's `D_ν(z) = U(-ν - 1/2, z)` is `pcfD`.
-/
