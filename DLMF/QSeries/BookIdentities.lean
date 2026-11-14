/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QSeries.QCalculus
public import DLMF.QSeries.Logarithm
public import DLMF.QHypergeometric.Calculus.QDerivative
public import Mathlib.NumberTheory.Real.Irrational

/-!
# Additional q-calculus and Lambert identities

Duverney, *An Introduction to Hypergeometric Functions*, Chapter 10, Theorems
10.2 and 10.4, equations (10.10)–(10.25), and Exercises 10.10 and 10.13.
The constants theorem retains the indispensable finite limit at the origin.
-/

@[expose] public noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology Real

namespace DLMF.QSeries

/-- Jackson derivative of a real power on the positive ray.
Duverney (10.11), synopsis DU-10.03. -/
theorem qDeriv_cpow_real {q x : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hx : 0 < x) (a : ℝ) :
    qDeriv q (fun z : ℂ => z ^ (a : ℂ)) x =
      (((1 - q ^ a) / (1 - q) * x ^ (a - 1) : ℝ) : ℂ) := by
  sorry

/-- The real-parameter Jackson difference quotient tends to a real derivative; complex
analyticity of the extension is unnecessary. Duverney (10.12), synopsis DU-10.03. -/
theorem tendsto_qDeriv_of_hasDerivAt_real {f : ℂ → ℂ} {x : ℝ} {f' : ℂ}
    (hf : HasDerivAt (fun t : ℝ => f t) f' x) (hx : x ≠ 0) :
    Tendsto (fun q : ℝ => qDeriv q f x) (𝓝[<] 1) (𝓝 f') := by
  sorry

/-- A logarithmically periodic sine has zero Jackson derivative on the positive ray.
Duverney's counterexample following Theorem 10.2, synopsis DU-10.04. -/
theorem qDeriv_sin_log_eq_zero {q x : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hx : 0 < x) :
    qDeriv q (fun z : ℂ => (Real.sin (2 * Real.pi * Real.log z.re / Real.log q) : ℂ)) x =
      0 := by
  sorry

/-- The logarithmically periodic zero-Jackson-derivative example is nonconstant.
Its value at one is zero, while this theorem supplies a positive point with nonzero value.
Duverney following Theorem 10.2, synopsis DU-10.04. -/
theorem exists_pos_sin_log_ne_zero {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    ∃ x : ℝ, 0 < x ∧ Real.sin (2 * Real.pi * Real.log x / Real.log q) ≠ 0 := by
  sorry

/-- Constants are characterized by their zero Jackson derivative if a finite right limit
exists. Duverney Theorem 10.2, synopsis DU-10.04. -/
theorem qDeriv_eq_zero_iff_eq_limit {q upper : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hupper : 0 < upper) {f : ℂ → ℂ} {L : ℂ}
    (hf : Tendsto (fun t : ℝ => f t) (𝓝[>] 0) (𝓝 L)) :
    (∀ x ∈ Ioo (0 : ℝ) upper, qDeriv q f x = 0) ↔
      ∀ x ∈ Ioo (0 : ℝ) upper, f x = L := by
  sorry

/-- Finite right limits suffice for absolute convergence of the Jackson series.
Duverney Theorem 10.4, synopsis DU-10.05. -/
theorem summable_jackson_of_tendsto {q x : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hx : 0 < x) {f : ℂ → ℂ} {L : ℂ}
    (hf : Tendsto (fun t : ℝ => f t) (𝓝[>] 0) (𝓝 L)) :
    Summable (fun k : ℕ => f (x * q ^ k) * (q : ℂ) ^ k) := by
  sorry

/-- The Jackson primitive tends to zero at its lower endpoint.
Duverney Theorem 10.4, synopsis DU-10.05. -/
theorem tendsto_jacksonIntegral_zero {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    {f : ℂ → ℂ} {L : ℂ} (hf : Tendsto (fun t : ℝ => f t) (𝓝[>] 0) (𝓝 L)) :
    Tendsto (fun x : ℝ => jacksonIntegral q x f) (𝓝[>] 0) (𝓝 0) := by
  sorry

/-- Uniqueness of the Jackson primitive with zero right limit.
Duverney Theorem 10.4, synopsis DU-10.05. -/
theorem eq_jacksonIntegral_of_qDeriv_eq {q upper : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hupper : 0 < upper) {f F : ℂ → ℂ} {L : ℂ}
    (hf : Tendsto (fun t : ℝ => f t) (𝓝[>] 0) (𝓝 L))
    (hF : Tendsto (fun t : ℝ => F t) (𝓝[>] 0) (𝓝 0))
    (hd : ∀ x ∈ Ioo (0 : ℝ) upper, qDeriv q F x = f x) :
    ∀ x ∈ Ioo (0 : ℝ) upper, F x = jacksonIntegral q x f := by
  sorry

/-- Termwise Jackson differentiation of a convergent power series away from zero.
Duverney (10.21), synopsis DU-10.06. -/
theorem hasSum_qDeriv_powerSeries {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    {a : ℕ → ℂ} {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : ∀ z : ℂ, ‖z‖ < R → HasSum (fun k : ℕ => a k * z ^ k) (f z))
    {z : ℂ} (hz : ‖z‖ < R) (hz0 : z ≠ 0) :
    HasSum (fun k : ℕ => a (k + 1) * (1 - (q : ℂ) ^ (k + 1)) /
      (1 - q) * z ^ k) (qDeriv q f z) := by
  sorry

/-- Termwise Jackson integration of a convergent power series.
Duverney (10.22), synopsis DU-10.06. -/
theorem hasSum_jacksonIntegral_powerSeries {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    {a : ℕ → ℂ} {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : ∀ z : ℂ, ‖z‖ < R → HasSum (fun k : ℕ => a k * z ^ k) (f z))
    {z : ℂ} (hz : ‖z‖ < R) :
    HasSum (fun k : ℕ => a k * (1 - q) * z ^ (k + 1) /
      (1 - (q : ℂ) ^ (k + 1))) (jacksonIntegral q z f) := by
  sorry

/-- The Jackson differential equation for the unscaled little q-exponential, throughout
its product-continuation domain away from the origin.
Duverney (10.27), synopsis DU-10.07. -/
theorem qDeriv_inv_qPochhammerInf {q z : ℂ} (hq : ‖q‖ < 1) (hz0 : z ≠ 0)
    (hz : ∀ n : ℕ, 1 - z * q ^ n ≠ 0) :
    (1 - q) * qDeriv q (fun w => (qPochhammerInf w q)⁻¹) z =
      (qPochhammerInf z q)⁻¹ := by
  sorry

/-- The divisor Lambert identity. Duverney Exercise 10.10, synopsis DU-10.18. -/
theorem tsum_pow_div_one_sub_pow_sq {q : ℂ} (hq : ‖q‖ < 1) :
    (∑' k : ℕ, q ^ (k + 1) / (1 - q ^ (k + 1)) ^ 2) =
      ∑' k : ℕ, (k + 1) * q ^ (k + 1) / (1 - q ^ (k + 1)) := by
  sorry

namespace Real

/-- The Erdős–Borwein constant, defined by its absolutely convergent dyadic Lambert series.
Duverney Exercise 10.13, synopsis DU-10.18. -/
def erdosBorweinConstant : ℝ := ∑' n : ℕ, ((2 : ℝ) ^ (n + 1) - 1)⁻¹

/-- Defining series of the Erdős–Borwein constant. Duverney Exercise 10.13, DU-10.18. -/
theorem erdosBorweinConstant_def :
    erdosBorweinConstant = ∑' n : ℕ, ((2 : ℝ) ^ (n + 1) - 1)⁻¹ := rfl

/-- Absolute convergence of the Erdős–Borwein series.
Duverney Exercise 10.13, synopsis DU-10.18. -/
theorem summable_erdosBorweinConstant :
    Summable (fun n : ℕ => ((2 : ℝ) ^ (n + 1) - 1)⁻¹) := by
  sorry

/-- The quadratically convergent Erdős–Borwein series.
Duverney Exercise 10.13, synopsis DU-10.18. -/
theorem hasSum_erdosBorweinConstant_accelerated :
    HasSum (fun n : ℕ => ((2 : ℝ) ^ (n + 1) + 1) /
      ((2 : ℝ) ^ ((n + 1) ^ 2) * ((2 : ℝ) ^ (n + 1) - 1)))
      erdosBorweinConstant := by
  sorry

/-- Irrationality of the Erdős–Borwein constant.
Duverney Exercise 10.13, synopsis DU-10.18. -/
theorem irrational_erdosBorweinConstant : Irrational erdosBorweinConstant := by
  sorry

end Real
end DLMF.QSeries
