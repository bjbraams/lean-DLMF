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

* `hasDerivAt_parabolicCylinderU`, `hasDerivAt_parabolicCylinderUDeriv`,
  `deriv_deriv_parabolicCylinderU`: Weber's equation 12.2.2.
* `parabolicCylinderU_zero`, `parabolicCylinderUDeriv_zero`: the initial values.
* `parabolicCylinderU_neg_half`: `U(-1/2, z) = e^{-z²/4}`.
* `parabolicCylinderU_eq_kummerU`: `U(a,z) = 2^{-1/4-a/2} e^{-z²/4} U(a/2 + 1/4, 1/2, z²/2)` for
  `re z > 0`.
* `hasAsymptoticExpansion_parabolicCylinderU`:
  `U(a,x) ~ e^{-x²/4} x^{-a-1/2} ∑ (-1)^s (a + 1/2)_{2s}/(s! (2x²)^s)`.
* `IsWeberSolution.eq_of_initial`: solutions of Weber's equation are determined by `w(0), w'(0)`
  (via constancy of Wronskians against `u₁, u₂`).
* `parabolicCylinderU_three_term`, `parabolicCylinderU_recurrence_add`,
  `parabolicCylinderU_recurrence_sub`, `parabolicCylinderU_deriv_recurrence`: the recurrences
  12.8.1–12.8.4.
* `parabolicCylinderD_nat`: `D_n(z) = e^{-z²/4} He_n(z)` (12.7.2).
* `parabolicCylinderU_eq_integral`: `U(a,z) = e^{-z²/4}/Γ(1/2+a) ∫₀^∞ t^{a-1/2} e^{-t²/2-zt} dt`
  (12.5.1).
* `parabolicCylinderU_wronskian_neg`, `parabolicCylinderU_wronskian_mul_I`,
  `parabolicCylinderU_wronskian_mul_neg_I`: the Wronskians 12.2.11–12.2.12.
* `parabolicCylinderU_connection_mul_I`, `parabolicCylinderU_connection_mul_neg_I`: the connection
  formula 12.2.17.
* `parabolicCylinderV`: the second solution `V(a,z) = V(a,0) u₁ + V'(a,0) u₂` (12.4.2), entire in
  `a` and `z`, with `parabolicCylinderV_zero`, `parabolicCylinderVDeriv_zero` (12.2.8–12.2.9) and
  Weber's equation.
* `parabolicCylinderV_wronskian`: `𝒲{U, V} = √(2/π)` (12.2.10).
* `parabolicCylinderU_neg_eq`, `parabolicCylinderV_neg_eq`: the connection formulas 12.2.15–12.2.16
  for every `a`, with the parity cases `parabolicCylinderU_neg_nat_sub_half_neg`,
  `parabolicCylinderV_nat_add_half_neg` (12.2.13–12.2.14) and the classical form
  `parabolicCylinderV_eq` of `V` in terms of `U(a, ±z)`.
* `parabolicCylinderV_eq_mul_I`, `parabolicCylinderV_eq_mul_neg_I`: the connection formula 12.2.20
  for every `a`.
* `parabolicCylinderV_three_term`, `parabolicCylinderV_recurrence_sub`,
  `parabolicCylinderV_recurrence_add`, `parabolicCylinderV_deriv_recurrence`: the recurrences
  12.8.5–12.8.8.

Whittaker's `D_ν(z) = U(-ν - 1/2, z)` is `parabolicCylinderD`.
-/
