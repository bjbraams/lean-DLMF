/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Entire functions with integer interpolation data

The Hardy–Pólya, Gelfond and Selberg exponential-type criteria recalled in Andrews,
Askey and Roy, *Special Functions*, §8.3, p. 410 (synopsis AAR-8.4.1–8.4.4).
The output is an actual polynomial representing the entire function.
-/

@[expose] public section

namespace Complex

/-- Hardy–Pólya: an entire function of exponential type less than `log 2` whose values
at nonnegative integers are integers is a polynomial. Andrews–Askey–Roy,
*Special Functions*, §8.3, p. 410 (synopsis AAR-8.4.1–8.4.4). -/
theorem exists_polynomial_of_integer_values_of_type_lt_log_two {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {C τ : ℝ} (hC : 0 < C) (hτ : τ < Real.log 2)
    (hbound : ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp (τ * ‖z‖))
    (hinteger : ∀ n : ℕ, ∃ k : ℤ, f n = k) :
    ∃ P : Polynomial ℂ, ∀ z : ℂ, f z = P.eval z := by
  sorry

/-- Gelfond's exponential-type criterion for integer values of successive derivatives.
Andrews–Askey–Roy, *Special Functions*, §8.3, p. 410
(synopsis AAR-8.4.1–8.4.4). -/
theorem exists_polynomial_of_integer_derivatives_of_type_lt_gelfond {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {p : ℕ} (hp : 0 < p) {C τ : ℝ} (hC : 0 < C)
    (hτ : τ < p * Real.log (1 + Real.exp ((1 - (p : ℝ)) / p)))
    (hbound : ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp (τ * ‖z‖))
    (hinteger : ∀ j < p, ∀ n : ℕ, ∃ k : ℤ, iteratedDeriv j f n = k) :
    ∃ P : Polynomial ℂ, ∀ z : ℂ, f z = P.eval z := by
  sorry

/-- Selberg's constrained-minimum refinement of the integer-derivative type bound.
Andrews–Askey–Roy, *Special Functions*, §8.3, p. 410
(synopsis AAR-8.4.1–8.4.4). `y` is an actual minimizing positive configuration. -/
theorem exists_polynomial_of_integer_derivatives_of_type_lt_selberg {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {p : ℕ} (hp : 0 < p) (y : Fin p → ℝ)
    (hy : ∀ i, 0 < y i) (hprod : (∏ i, y i) = Real.exp (1 - (p : ℝ)))
    (hdisc : |∏ i, ∏ j, if i < j then (y i)⁻¹ - (y j)⁻¹ else 1| = 1)
    (hmin : ∀ x : Fin p → ℝ, (∀ i, 0 < x i) →
      (∏ i, x i) = Real.exp (1 - (p : ℝ)) →
      |∏ i, ∏ j, if i < j then (x i)⁻¹ - (x j)⁻¹ else 1| = 1 →
      (∏ i, (1 + y i)) ≤ ∏ i, (1 + x i))
    {C τ : ℝ} (hC : 0 < C) (hτ : τ < Real.log (∏ i, (1 + y i)))
    (hbound : ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp (τ * ‖z‖))
    (hinteger : ∀ j < p, ∀ n : ℕ, ∃ k : ℤ, iteratedDeriv j f n = k) :
    ∃ P : Polynomial ℂ, ∀ z : ℂ, f z = P.eval z := by
  sorry

end Complex
