/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Basic.AskeyScheme
public import DLMFMathlib.Analysis.Complex.BarnesContour
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Complex Wilson orthogonality on deformed Barnes contours

Andrews, Askey and Roy, *Special Functions*, Theorems 3.6.2 and 3.8.2,
pp. 151 and 159–160 (synopsis AAR-3.6.1–3.8.2). The contour separates the
opposing Gamma pole families. Its existence retains the full admissible
complex parameter range, even when a straight separating line does not exist.
-/

@[expose] public section

open Complex DLMF.Hypergeometric

namespace DLMF.OrthogonalPolynomials

/-- The Wilson Gamma weight times two Wilson polynomials in the contour coordinate.
Andrews–Askey–Roy, *Special Functions*, Theorem 3.8.2, pp. 159–160
(synopsis AAR-3.6.1–3.8.2). The polynomial argument is `-s²`. -/
noncomputable def wilsonBarnesIntegrand (a b c d : ℂ) (m n : ℕ) (s : ℂ) : ℂ :=
  Gamma (a + s) * Gamma (a - s) * Gamma (b + s) * Gamma (b - s) *
    Gamma (c + s) * Gamma (c - s) * Gamma (d + s) * Gamma (d - s) /
      (Gamma (2 * s) * Gamma (-2 * s)) *
        wilson a b c d m (-s ^ 2) * wilson a b c d n (-s ^ 2)

/-- The complete Gamma-and-polynomial integrand formula. -/
theorem wilsonBarnesIntegrand_def (a b c d : ℂ) (m n : ℕ) (s : ℂ) :
    wilsonBarnesIntegrand a b c d m n s =
      Gamma (a + s) * Gamma (a - s) * Gamma (b + s) * Gamma (b - s) *
        Gamma (c + s) * Gamma (c - s) * Gamma (d + s) * Gamma (d - s) /
          (Gamma (2 * s) * Gamma (-2 * s)) *
            wilson a b c d m (-s ^ 2) * wilson a b c d n (-s ^ 2) := rfl

/-- Wilson's full complex contour norm, including the degree-zero Wilson integral.
Andrews–Askey–Roy, *Special Functions*, Theorems 3.6.2 and 3.8.2,
pp. 151 and 159–160 (synopsis AAR-3.6.1–3.8.2). The actual finite-deformation
contour geometry enforces separation and avoidance of all numerator poles. -/
theorem wilson_integral_mul_contour (a b c d : ℂ)
    (C : BarnesContour ![a, b, c, d] ![a, b, c, d]) (m n : ℕ) :
    C.IsIntegrable (wilsonBarnesIntegrand a b c d m n) ∧
      C.integral (wilsonBarnesIntegrand a b c d m n) / (2 * Real.pi * I) =
        if m = n then
          2 * n.factorial * pochhammer (n + a + b + c + d - 1) n *
            Gamma (n + a + b) * Gamma (n + a + c) * Gamma (n + a + d) *
            Gamma (n + b + c) * Gamma (n + b + d) * Gamma (n + c + d) /
            Gamma (a + b + c + d + 2 * n)
        else 0 := by
  sorry

end DLMF.OrthogonalPolynomials
