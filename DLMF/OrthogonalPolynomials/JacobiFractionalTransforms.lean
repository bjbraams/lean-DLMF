/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Basic.PolynomialContinuation
public import DLMF.OrthogonalPolynomials.Basic.Classical
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Fractional Jacobi transforms with a rational weight

Andrews, Askey and Roy, *Special Functions*, Theorem 6.7.2(c)–(d), pp. 314–315
(synopsis AAR-6.7.1–6.7.4). The polynomial continuation is used throughout;
normalization is at the endpoint from which the fractional integral is taken.
Positive real-part conditions are the precise local endpoint conditions.
-/

@[expose] public section

open Complex MeasureTheory
open scoped Classical

namespace DLMF.OrthogonalPolynomials

/-- The right-endpoint fractional transform with the rational Jacobi weight.
Andrews–Askey–Roy, *Special Functions*, Theorem 6.7.2(c), pp. 314–315
(synopsis AAR-6.7.1–6.7.4). This complex-parameter form uses principal powers
of positive real bases, and includes the book's real-parameter statement. -/
theorem jacobiExtended_fractional_integral_weighted {α β μ : ℂ}
    (hα : -1 < α.re) (hμ : 0 < μ.re) (n : ℕ) {x : ℝ}
    (hx : x ∈ Set.Ioo (-1) 1) :
    let R := fun a b z : ℂ => jacobiExtended a b n z /
      jacobiExtended a b n 1
    IntervalIntegrable (fun t : ℝ =>
      (1 - t : ℂ) ^ α * R α β t /
        (1 + t : ℂ) ^ (n + α + β + μ + 1) * (t - x : ℂ) ^ (μ - 1)) volume x 1 ∧
    (1 - x : ℂ) ^ (α + μ) / (1 + x : ℂ) ^ (n + α + β + 1) * R (α + μ) β x =
      (2 : ℂ) ^ μ * Gamma (α + μ + 1) / (Gamma (α + 1) * Gamma μ) *
        ∫ t : ℝ in x..1, (1 - t : ℂ) ^ α * R α β t /
          (1 + t : ℂ) ^ (n + α + β + μ + 1) * (t - x : ℂ) ^ (μ - 1) := by
  sorry

/-- Reflection gives the corresponding left-endpoint rational-weight transform.
Andrews–Askey–Roy, *Special Functions*, Theorem 6.7.2(d), pp. 314–315
(synopsis AAR-6.7.1–6.7.4). The quotient is normalized at `-1`, so reflection
introduces no additional parity factor. -/
theorem jacobiExtended_fractional_integral_weighted_left {α β μ : ℂ}
    (hβ : -1 < β.re) (hμ : 0 < μ.re) (n : ℕ) {x : ℝ}
    (hx : x ∈ Set.Ioo (-1) 1) :
    let R := fun a b z : ℂ => jacobiExtended a b n z /
      jacobiExtended a b n (-1)
    IntervalIntegrable (fun t : ℝ =>
      (1 + t : ℂ) ^ β * R α β t /
        (1 - t : ℂ) ^ (n + α + β + μ + 1) * (x - t : ℂ) ^ (μ - 1)) volume (-1) x ∧
    (1 + x : ℂ) ^ (β + μ) / (1 - x : ℂ) ^ (n + α + β + 1) * R α (β + μ) x =
      (2 : ℂ) ^ μ * Gamma (β + μ + 1) / (Gamma (β + 1) * Gamma μ) *
        ∫ t : ℝ in (-1 : ℝ)..x, (1 + t : ℂ) ^ β * R α β t /
          (1 - t : ℂ) ^ (n + α + β + μ + 1) * (x - t : ℂ) ^ (μ - 1) := by
  sorry


/-- The Gegenbauer angular fractional transform, including the Chebyshev removable case.
Andrews–Askey–Roy, *Special Functions*, Corollary 6.7.3, pp. 315–316
(synopsis AAR-6.7.1–6.7.4). Both parameters may pass through zero: the normalized
zero-parameter family is the Chebyshev polynomial. The weight has its full
integrability range `ν > λ > -1/2`. -/
theorem ultrasphericalPolynomial_normalized_fractional_angular {lam ν : ℝ}
    (hlam : -1 / 2 < lam) (hν : lam < ν) (n : ℕ) {θ : ℝ}
    (hθ : θ ∈ Set.Icc 0 Real.pi) :
    let R := fun (a : ℝ) (z : ℂ) =>
      if a = 0 then (Polynomial.Chebyshev.T ℂ n).eval z
      else ultrasphericalPolynomial a n z / ultrasphericalPolynomial a n 1
    let F := fun φ : ℝ =>
      let D : ℝ := 1 - Real.sin θ ^ 2 * Real.cos φ ^ 2
      (Real.sin φ : ℂ) ^ (2 * lam : ℂ) *
        (Real.cos φ : ℂ) ^ (2 * ν - 2 * lam - 1 : ℂ) *
        (D : ℂ) ^ ((n : ℂ) / 2) * R lam (Real.cos θ / Real.sqrt D)
    IntervalIntegrable F volume 0 (Real.pi / 2) ∧
      R ν (Real.cos θ) =
        2 * Gamma (ν + 1 / 2 : ℂ) / (Gamma (lam + 1 / 2 : ℂ) * Gamma (ν - lam : ℂ)) *
          ∫ φ : ℝ in (0 : ℝ)..Real.pi / 2, F φ := by
  sorry

end DLMF.OrthogonalPolynomials
