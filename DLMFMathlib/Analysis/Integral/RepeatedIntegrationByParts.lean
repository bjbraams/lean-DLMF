/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Repeated integration by parts against a complex exponential

A finite sequence of continuous successive derivatives gives an exact boundary
sum and an integral remainder. One-sided derivatives at interval endpoints suffice.
-/

@[expose] public noncomputable section

open MeasureTheory Set Complex Finset
open scoped Topology

namespace intervalIntegral

/-- One integration by parts against `exp(z t)`, allowing one-sided endpoint derivatives. -/
theorem integral_cexp_mul_eq_boundary_sub {a b : ℝ} (hab : a ≤ b) {z : ℂ} (hz : z ≠ 0)
    {q q' : ℝ → ℂ} (hq : ContinuousOn q (Icc a b)) (hq' : ContinuousOn q' (Icc a b))
    (hd : ∀ t ∈ Icc a b, HasDerivWithinAt q (q' t) (Icc a b) t) :
    (∫ t in a..b, exp (z * t) * q t) =
      (exp (z * b) * q b - exp (z * a) * q a) / z -
        (∫ t in a..b, exp (z * t) * q' t) / z := by
  have he (t : ℝ) : HasDerivAt (fun u : ℝ => exp (z * u) / z) (exp (z * t)) t := by
    have h := (((hasDerivAt_id (t : ℂ)).const_mul z).cexp.div_const z).comp_ofReal
    convert h using 1 <;> simp [hz]
  have hi := integral_deriv_mul_eq_sub_of_hasDerivWithinAt
    (fun t ht => (he t).hasDerivWithinAt (s := uIcc a b))
    (fun t ht => by rw [uIcc_of_le hab] at ht ⊢; exact hd t ht)
    (by apply Continuous.intervalIntegrable; fun_prop)
    (hq'.intervalIntegrable_of_Icc hab)
  have h0 : IntervalIntegrable (fun t : ℝ => exp (z * t) * q t) volume a b :=
    ((show ContinuousOn (fun t : ℝ => exp (z * t)) (Icc a b) by
      fun_prop).mul hq).intervalIntegrable_of_Icc hab
  have h1 : IntervalIntegrable (fun t : ℝ => exp (z * t) * q' t / z) volume a b :=
    (((show ContinuousOn (fun t : ℝ => exp (z * t)) (Icc a b) by
      fun_prop).mul hq').div_const z).intervalIntegrable_of_Icc hab
  simp only [show ∀ t : ℝ, exp (z * t) / z * q' t = exp (z * t) * q' t / z by intro t; ring,
    integral_add h0 h1, integral_div] at hi
  linear_combination hi

/-- Repeated integration by parts gives an exact finite boundary sum and remainder
for a complex exponential kernel and a sequence of successive derivatives. -/
theorem integral_cexp_mul_eq_sum_add {a b : ℝ} (hab : a ≤ b) {z : ℂ} (hz : z ≠ 0)
    (D : ℕ → ℝ → ℂ) (n : ℕ)
    (hD : ∀ k ≤ n, ContinuousOn (D k) (Icc a b))
    (hd : ∀ k < n, ∀ t ∈ Icc a b, HasDerivWithinAt (D k) (D (k + 1) t) (Icc a b) t) :
    (∫ t in a..b, exp (z * t) * D 0 t) =
      ∑ k ∈ range n, (-z⁻¹) ^ k / z * (exp (z * b) * D k b - exp (z * a) * D k a) +
        (-z⁻¹) ^ n * ∫ t in a..b, exp (z * t) * D n t := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := ih (fun k hk => hD k (by omega)) (fun k hk => hd k (by omega))
    have hn := integral_cexp_mul_eq_boundary_sub hab hz (hD n (by omega)) (hD (n + 1) le_rfl)
      (hd n (by omega))
    rw [h, hn, sum_range_succ, pow_succ]
    ring

end intervalIntegral
