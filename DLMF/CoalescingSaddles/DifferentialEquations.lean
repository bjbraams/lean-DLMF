/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.CoalescingSaddles.DifferentialEquations.Cuspoid
public import DLMF.CoalescingSaddles.DifferentialEquations.HyperbolicUmbilic
public import DLMF.CoalescingSaddles.DifferentialEquations.EllipticUmbilic

/-!
# Differential equations for the canonical integrals: DLMF §36.10

The canonical integrals are defined (`DLMF.CoalescingSaddles.Basic`) as absolutely convergent
integrals over rotated contours, on which the integrand and all its polynomial moments have
Gaussian decay. This file proves

* differentiation under the integral sign: `∂Ψ_K/∂x_m` is `i` times the moment of order `m`
  (`hasDerivAt_cuspoidMoment_update`, `iteratedDeriv_cuspoidIntegral_update`), so that
  `∂ⁿΨ_K/∂x_mⁿ = iⁿ ∫ t^{mn} exp(iΦ_K) dt`;
* integration by parts along the contour: `∫ (∂Φ_K/∂t) exp(iΦ_K) dt = 0`
  (`cuspoidMoment_ibp`), since the integrand is `-i d/dt exp(iΦ_K)` and `exp(iΦ_K)` vanishes at
  both ends of the contour.

From these, the operator equation 36.10.1, the ordinary differential equation 36.10.2 in `x₁`,
its special cases 36.10.3–36.10.5, and the relations 36.10.6–36.10.10 between partial derivatives
are proved. Of the umbilic equations 36.10.11–36.10.18, those for `Ψ^{(H)}` (36.10.15, 36.10.16,
36.10.18) are proved in the same way on the product of two cubic contours
(`hasDerivAt_hyperbolicUmbilicMoment_x`, Fubini and integration by parts in each variable); those
for `Ψ^{(E)}` (36.10.13, 36.10.14, 36.10.17) are proved on the 2-cycle of
`ellipticUmbilicIntegral` in the coordinates `a = s + it`, `b = s - it`, with weighted moments
`q2t_EM` and integration by parts along each ray (the boundary terms cancel over the cycle).

Partial derivatives are written with `Function.update`: `∂ⁿΨ_K/∂x_mⁿ` at `x` is
`iteratedDeriv n (fun s => cuspoidIntegral K (Function.update x m s)) (x m)`, where (as in
`DLMF.CoalescingSaddles.Basic`) the Lean index `m : Fin K` is DLMF's `x_{m+1}`. All
differentiability used in these statements is proved here (the canonical integrals are smooth
in each variable), so the Lean convention `deriv f = 0` at non-differentiable points never
enters.

The integrability lemmas for the rotated contour (`norm_cuspoidContour`, `cuspoidContour_pow`,
`s36a_norm_integrand_le`, …) are those of `DLMF.CoalescingSaddles.CanonicalIntegrals`.
-/
