/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
public import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Global bounds for complex sine and logarithmic differences

Kristensson, *Second Order Differential Equations*, Appendix A, Lemmas A.1–A.2
and Corollary A.1. Principal logarithms use the upper-bank value on the negative
real axis; real parts of their shifted difference stay bounded across the cuts.
-/

@[expose] public section

namespace Complex

/-- Kristensson, Appendix A, Lemma A.1, pp. 166–168: away from fixed-radius
discs about the integers, the magnitude of `sin (πz)` is comparable to `exp(π|Im z|)`. -/
theorem exists_norm_sin_pi_mul_bounds_of_dist_int {ε : ℝ}
    (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ z : ℂ,
      (∀ n : ℤ, ε < ‖z - n‖) →
      c * Real.exp (Real.pi * |z.im|) ≤ ‖sin (Real.pi * z)‖ ∧
        ‖sin (Real.pi * z)‖ ≤ C * Real.exp (Real.pi * |z.im|) := by
  sorry

/-- Kristensson, Appendix A, Corollary A.1, p. 168: translating the sine estimate
changes its constants, while retaining the exponential in the original imaginary part. -/
theorem exists_norm_sin_pi_mul_add_bounds_of_dist_int (α : ℂ) {ε : ℝ}
    (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ z : ℂ,
      (∀ n : ℤ, ε < ‖z + α - n‖) →
      c * Real.exp (Real.pi * |z.im|) ≤ ‖sin (Real.pi * (z + α))‖ ∧
        ‖sin (Real.pi * (z + α))‖ ≤ C * Real.exp (Real.pi * |z.im|) := by
  sorry

/-- Kristensson, Appendix A, Lemma A.2, pp. 169–170: the real part of a shifted
logarithm difference is globally bounded when both arguments stay away from zero.
No bound on its imaginary part is asserted across a principal-logarithm cut. -/
theorem exists_abs_re_mul_log_sub_log_le (α γ : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, ε ≤ ‖z‖ → ε ≤ ‖z + α‖ →
      |((z + γ) * (log (z + α) - log z)).re| ≤ C := by
  sorry

end Complex
