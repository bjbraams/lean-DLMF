/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import DLMFMathlib.Analysis.Fourier.HyperbolicSecant
import TauCeti.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith

/-!
# Polynomial moments of a hyperbolic secant

Every real or complex polynomial is absolutely integrable against `1 / cosh (r t)` for
`r > 0`. The proof extends the positive half-line bound to the real line using TauCeti's
`TauCeti.MeasureTheory.integrable_comp_abs` and bounds the polynomial powers term by term.

* `RCLike.integrable_pow_div_cosh`: integrability of each power moment.
* `RCLike.integrable_eval_polynomial_div_cosh`: integrability of a polynomial moment.
-/

public noncomputable section

open MeasureTheory Set Polynomial Filter
open scoped Real

namespace RCLike

/-- Every polynomial power divided by `cosh (r t)` is integrable when `r > 0`,
over a real or complex scalar field. -/
lemma integrable_pow_div_cosh {K : Type*} [RCLike K] {r : ℝ} (hr : 0 < r) (n : ℕ) :
    Integrable (fun t : ℝ => (t : K) ^ n / (Real.cosh (r * t) : K)) := by
  have hb : Integrable (fun t : ℝ => (1 + |t|) ^ n / Real.cosh (r * |t|)) :=
    TauCeti.MeasureTheory.integrable_comp_abs (Real.integrableOn_one_add_pow_div_cosh hr n)
  have hc : Continuous (fun t : ℝ => (t : K) ^ n / (Real.cosh (r * t) : K)) :=
    (RCLike.continuous_ofReal.pow n).div
      (RCLike.continuous_ofReal.comp
        (Real.continuous_cosh.comp (continuous_const.mul continuous_id)))
      (fun t => RCLike.ofReal_ne_zero.mpr (Real.cosh_pos _).ne')
  refine hb.mono' hc.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  rw [norm_div, norm_pow, RCLike.norm_ofReal, RCLike.norm_ofReal,
    abs_of_pos (Real.cosh_pos _)]
  have hd : Real.cosh (r * |t|) = Real.cosh (r * t) := by
    rw [show r * |t| = |r * t| by rw [abs_mul, abs_of_pos hr], Real.cosh_abs]
  rw [hd]
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (by linarith) n)
    (Real.cosh_pos _).le

/-- Every polynomial evaluated on the real line is integrable against a hyperbolic secant
with positive scale. -/
lemma integrable_eval_polynomial_div_cosh {K : Type*} [RCLike K] {r : ℝ} (hr : 0 < r)
    (P : K[X]) : Integrable (fun t : ℝ => P.eval (t : K) / (Real.cosh (r * t) : K)) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    refine (hP.add hQ).congr (Eventually.of_forall fun t => ?_)
    simp only [Pi.add_apply, eval_add, add_div]
  | monomial n a =>
    simpa only [eval_monomial, mul_div_assoc] using (integrable_pow_div_cosh hr n).const_mul a

end RCLike
