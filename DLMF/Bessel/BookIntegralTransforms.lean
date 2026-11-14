/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bessel.Basic
public import DLMF.Hypergeometric.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Sonine, Laplace and Mellin product integrals

Andrews, Askey and Roy, *Special Functions*, §4.11, pp. 216–222.
Complex powers use the principal slit branch. The angular product is written
with the entire normalized Bessel series to avoid introducing a square-root branch.
Every half-line formula includes absolute integrability of its full integrand.
-/

@[expose] public section

open Complex MeasureTheory

namespace DLMF.Bessel

/-- Sonine's first angular integral. Andrews–Askey–Roy, *Special Functions*,
Theorem 4.11.1, pp. 216–217 (synopsis AAR-4.11.1–4.11.8).
Positive real arguments are included in the full principal slit branch. -/
theorem besselJ_sonine_angular {μ ν z : ℂ} (hμ : -1 < μ.re) (hν : -1 < ν.re)
    (hz : z ∈ slitPlane) :
    IntervalIntegrable (fun t : ℝ => besselJ μ (z * Real.sin t) *
      (Real.sin t : ℂ) ^ (μ + 1) * (Real.cos t : ℂ) ^ (2 * ν + 1)) volume
        0 (Real.pi / 2) ∧
    (∫ t : ℝ in 0..Real.pi / 2, besselJ μ (z * Real.sin t) *
      (Real.sin t : ℂ) ^ (μ + 1) * (Real.cos t : ℂ) ^ (2 * ν + 1)) =
      (2 : ℂ) ^ ν * Gamma (ν + 1) * z ^ (-ν - 1) * besselJ (μ + ν + 1) z := by
  sorry

/-- Sonine's two-Bessel angular integral with its normalized entire endpoint value.
Andrews–Askey–Roy, *Special Functions*, Theorem 4.11.1, pp. 216–217
(synopsis AAR-4.11.1–4.11.8). The normalized Bessel function on the right is
`J_(μ+ν+1)(sqrt(x²+y²))/(sqrt(x²+y²))^(μ+ν+1)`. -/
theorem besselJ_mul_besselJ_sonine_angular {μ ν x y : ℂ}
    (hμ : -1 < μ.re) (hν : -1 < ν.re) (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) :
    IntervalIntegrable (fun t : ℝ => besselJ μ (x * Real.sin t) *
      besselJ ν (y * Real.cos t) * (Real.sin t : ℂ) ^ (μ + 1) *
        (Real.cos t : ℂ) ^ (ν + 1)) volume 0 (Real.pi / 2) ∧
    (∫ t : ℝ in 0..Real.pi / 2, besselJ μ (x * Real.sin t) *
      besselJ ν (y * Real.cos t) * (Real.sin t : ℂ) ^ (μ + 1) *
        (Real.cos t : ℂ) ^ (ν + 1)) =
      x ^ μ * y ^ ν / (2 : ℂ) ^ (μ + ν + 1) *
        regularizedHGFun ∅ {μ + ν + 2} (-(x ^ 2 + y ^ 2) / 4) := by
  sorry

/-- The Laplace–Bessel transform for complex frequency with its two growth inequalities.
Andrews–Askey–Roy, *Special Functions*, Theorem 4.11.3, pp. 217–219
(synopsis AAR-4.11.1–4.11.8). The regularized Gauss function includes exceptional
orders without evaluating a singular gamma quotient separately. -/
theorem besselJ_complex_laplace_integral {μ ν s w : ℂ}
    (hμν : 0 < (μ + ν).re) (hplus : 0 < (s + I * w).re)
    (hminus : 0 < (s - I * w).re) (hw : w ∈ slitPlane) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (μ - 1) * exp (-s * t) * besselJ ν (w * t))
      (Set.Ioi 0) ∧
    (∫ t : ℝ in Set.Ioi 0, (t : ℂ) ^ (μ - 1) * exp (-s * t) * besselJ ν (w * t)) =
      (w / 2) ^ ν * Gamma (μ + ν) * s ^ (-(μ + ν)) *
        DLMF.Hypergeometric.regularizedGaussHypergeometric
          ((μ + ν) / 2) ((μ + ν + 1) / 2) (ν + 1) (-w ^ 2 / s ^ 2) := by
  sorry

/-- The elementary reciprocal-variable Laplace transform.
Andrews–Askey–Roy, *Special Functions*, Corollary 4.11.5, pp. 218–219
(synopsis AAR-4.11.1–4.11.8). -/
theorem integral_exp_mul_besselJ_div {ν : ℂ} (hν : 0 < ν.re)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    IntegrableOn (fun t : ℝ => exp (-(x : ℂ) * t) * besselJ ν (y * t) / t) (Set.Ioi 0) ∧
    (∫ t : ℝ in Set.Ioi 0, exp (-(x : ℂ) * t) * besselJ ν (y * t) / t) =
      ((Real.sqrt (x ^ 2 + y ^ 2) - x : ℝ) : ℂ) ^ ν / (ν * (y : ℂ) ^ ν) := by
  sorry

/-- The Mellin product of two Bessel functions at the same positive argument.
Andrews–Askey–Roy, *Special Functions*, §4.11, pp. 220–222
(synopsis AAR-4.11.1–4.11.8). Positive real part of `λ` ensures absolute
convergence at infinity; the other inequality ensures convergence at zero. -/
theorem integral_besselJ_mul_besselJ_cpow {μ ν lam : ℂ}
    (hlam : 0 < lam.re) (hzero : lam.re < (μ + ν + 1).re) :
    IntegrableOn (fun t : ℝ => besselJ μ t * besselJ ν t * (t : ℂ) ^ (-lam)) (Set.Ioi 0) ∧
    (∫ t : ℝ in Set.Ioi 0, besselJ μ t * besselJ ν t * (t : ℂ) ^ (-lam)) =
      Gamma lam * Gamma ((μ + ν - lam + 1) / 2) /
        ((2 : ℂ) ^ lam * Gamma ((-μ + ν + lam + 1) / 2) *
          Gamma ((μ + ν + lam + 1) / 2) * Gamma ((μ - ν + lam + 1) / 2)) := by
  sorry

end DLMF.Bessel
