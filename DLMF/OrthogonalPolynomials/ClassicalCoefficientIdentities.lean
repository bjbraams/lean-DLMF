/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.PolynomialContinuation
public import DLMF.Hypergeometric.Basic.GaussSeries
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Classical polynomial normalization and positive connection coefficients

Andrews, Askey and Roy, *Special Functions*, §3.1, Theorem 6.4.3 and
Theorems 7.1.4–7.1.4′ (synopses AAR-3.1.1–3.1.3, AAR-6.3.1–6.4.3,
AAR-7.1.1–7.1.4′). Removable Jacobi factors are canceled before specialization.
-/

@[expose] public noncomputable section
open Polynomial MeasureTheory
namespace DLMF.OrthogonalPolynomials

/-- The even Jacobi quadratic identity at all polynomially continued parameters.
Andrews–Askey–Roy, §3.1, equation following (3.1.3). The ratio
`(α+1)₂ₙ/(α+1)ₙ` is canceled to `(α+n+1)ₙ`. -/
theorem jacobiExtended_quadratic_even (alpha : ℂ) (n : ℕ) (z : ℂ) :
    jacobiExtended alpha alpha (2 * n) z =
      ((n.factorial : ℂ) * DLMF.Hypergeometric.pochhammer (alpha + n + 1) n /
        (2 * n).factorial) * jacobiExtended alpha (-1 / 2) n (2 * z ^ 2 - 1) := by
  sorry

/-- Orthogonality to lower powers and the value at one determine the Jacobi polynomial.
Andrews–Askey–Roy, Theorem 6.4.3. Degree at most n suffices. -/
theorem eq_jacobiExtended_of_orthogonal_and_endpoint {alpha beta : ℝ}
    (halpha : -1 < alpha) (hbeta : -1 < beta) (n : ℕ) (p : ℝ[X])
    (hdegree : p.degree ≤ n)
    (horthogonal : ∀ k < n,
      (∫ x : ℝ in Set.Ioo (-1) 1,
        p.eval x * x ^ k * (1 - x) ^ alpha * (1 + x) ^ beta) = 0)
    (hendpoint : ((p.eval (1 : ℝ) : ℝ) : ℂ) =
      DLMF.Hypergeometric.pochhammer ((alpha : ℂ) + 1) n / n.factorial) :
    ∀ x : ℂ, p.aeval x = jacobiExtended alpha beta n x := by
  sorry

/-- Every Gegenbauer connection coefficient is nonnegative when the numerator parameter
is at least the positive basis parameter. Andrews–Askey–Roy, Theorems 7.1.4–7.1.4′.
This is the real scalar form of `ultrasphericalPolynomial_connection`. -/
theorem gegenbauer_connectionCoefficient_nonneg {lam mu : ℝ}
    (hmu : 0 < mu) (hlam : mu ≤ lam) {n k : ℕ} (hk : 2 * k ≤ n) :
    0 ≤ (mu + n - 2 * k) / mu * (ascPochhammer ℝ (n - k)).eval lam /
      (ascPochhammer ℝ (n - k)).eval (mu + 1) *
        ((ascPochhammer ℝ k).eval (lam - mu) / k.factorial) := by
  have hnum : 0 ≤ mu + (n : ℝ) - 2 * k := by
    have hk' : (2 : ℝ) * k ≤ n := by exact_mod_cast hk
    linarith
  exact mul_nonneg
    (div_nonneg (mul_nonneg (div_nonneg hnum hmu.le)
      (DLMF.Hypergeometric.pochhammer_eval_nonneg (hmu.le.trans hlam) _))
      (DLMF.Hypergeometric.pochhammer_eval_nonneg (by linarith) _))
    (div_nonneg (DLMF.Hypergeometric.pochhammer_eval_nonneg (sub_nonneg.mpr hlam) _)
      (Nat.cast_nonneg _))

end DLMF.OrthogonalPolynomials
