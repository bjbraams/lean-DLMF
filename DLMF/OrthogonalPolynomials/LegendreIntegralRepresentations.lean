/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Complex Laplace and complementary Mehler integrals for Legendre polynomials

Temme, *Special Functions*, (6.49)–(6.53), pp. 156–158, and Andrews, Askey and
Roy, *Special Functions*, Theorem 6.7.1. The Laplace integral retains either
square root, so it does not prescribe an artificial branch for polynomial data.
-/

@[expose] public section

namespace DLMF.OrthogonalPolynomials

/-- Laplace's integral for every complex argument and either root of z²−1.
Temme, *Special Functions*, (6.49)–(6.50), pp. 156–157 (synopsis TEM-06-12). -/
theorem legendrePolynomialP_eq_integral_pow (n : ℕ) {z s : ℂ}
    (hs : s ^ 2 = z ^ 2 - 1) :
    legendrePolynomialP n z = (Real.pi : ℂ)⁻¹ *
      ∫ φ : ℝ in (0 : ℝ)..Real.pi, (z + s * Real.cos φ) ^ n := by
  sorry

/-- The complementary Dirichlet–Mehler integral, integrated from θ to π.
Temme, *Special Functions*, (6.51)–(6.53), pp. 157–158 (synopsis TEM-06-12);
Andrews–Askey–Roy, Theorem 6.7.1 (synopsis AAR-6.7.1–6.7.4). -/
theorem legendrePolynomialP_eq_complementary_mehler (n : ℕ) {θ : ℝ}
    (hθ : 0 < θ) (hθπ : θ < Real.pi) :
    legendrePolynomialP n (Real.cos θ) =
      ((Real.sqrt 2 / Real.pi * ∫ φ : ℝ in θ..Real.pi,
        Real.sin ((n + 1 / 2) * φ) /
          Real.sqrt (Real.cos θ - Real.cos φ) : ℝ) : ℂ) := by
  sorry

end DLMF.OrthogonalPolynomials
