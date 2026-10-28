/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Zeta.IntegralReps.ElementaryKernels
public import DLMF.Zeta.IntegralReps.PolygammaAndContours

/-!
# Integral representations of the Riemann zeta function (DLMF §25.5)

Conventions.
* Integrals over `(0, ∞)` are Bochner integrals `∫ x in Ioi 0`, stated together with the
  integrability of the integrand, so that Lean's convention `∫ = 0` for non-integrable functions
  plays no role. Powers `x^{s-1}`, `(1+x²)^{s/2}`, `2^s`, `π^{s/2}` are principal complex powers
  of positive reals.
* 25.5.5 converges only conditionally at `∞` (for `-1 < Re s < 0`); it is stated as the limit of
  `∫₀^R` as `R → ∞`.
* Where DLMF divides by `1 - 2^{1-s}` (25.5.3, 25.5.4, 25.5.10, 25.5.21), which vanishes at
  `s = 1 + 2πik/ln 2`, the multiplied form is stated. It is equivalent to the printed form where
  the factor is nonzero and also holds at its zeros (stronger than DLMF).
* `1/Γ(s)` is kept as printed; Lean's `1 / Γ(s) = 0` at the poles of `Γ` agrees with the
  reciprocal Gamma function, so 25.5.6 and 25.5.7 hold also at `s = 0, -1, -2, …`.
* 25.5.13 has a removable singularity at `s = 0`, which is excluded.
* `ψ = Complex.digamma` and `ψ^{(m)} = DLMF.Gamma.polygamma m` (iterated derivatives of `ψ`).
* The loop integrals 25.5.20–25.5.21 are taken over the keyhole contours `keyholeLoopIntegral`
  (the two edges of the cut `(-∞, -δ]` and the circle `|z| = δ`), for every admissible radius
  `δ`; DLMF allows any loop of the stated kind, and the independence of the loop (Cauchy's
  theorem) is not formalized.
-/
