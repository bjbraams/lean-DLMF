/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Complex Laplace integral and growth bound for Legendre polynomials

Olver, *Asymptotics and Special Functions*, Chapter 2, (7.19) and
Exercise 7.9, pp. 51–52, synopsis O-2.18. Either square root is allowed.
-/

@[expose] public noncomputable section

open Complex MeasureTheory

namespace DLMF.OrthogonalPolynomials

/-- The complex angular representation depends only on the square of the chosen root.
Olver, Chapter 2, (7.19), synopsis O-2.18. -/
theorem legendrePolynomialP_eq_laplace_integral_complex (n : ℕ) (z s : ℂ)
    (hs : s ^ 2 = z ^ 2 - 1) :
    legendrePolynomialP n z = (Real.pi : ℂ)⁻¹ *
      ∫ θ in (0 : ℝ)..Real.pi, (z + s * Real.cos θ) ^ n := by
  sorry

/-- The hyperbolic-cosine growth bound for complex Legendre polynomials.
Olver, Chapter 2, Exercise 7.9, synopsis O-2.18. -/
theorem norm_legendrePolynomialP_cosh_le (n : ℕ) (α β : ℝ) :
    ‖legendrePolynomialP n (Complex.cosh (α + Complex.I * β))‖ ≤
      Real.exp ((n : ℝ) * |α|) := by
  sorry

/-- The Rodrigues–Cauchy contour formula on any positively oriented circle about `z`.
Olver, Chapter 2, (7.19), synopsis O-2.18. -/
theorem legendrePolynomialP_eq_circleIntegral (n : ℕ) (z : ℂ) {R : ℝ} (hR : 0 < R) :
    legendrePolynomialP n z = (2 : ℂ)⁻¹ ^ n / (2 * Real.pi * I) *
      circleIntegral (fun t => (t ^ 2 - 1) ^ n / (t - z) ^ (n + 1)) z R := by
  sorry

end DLMF.OrthogonalPolynomials
