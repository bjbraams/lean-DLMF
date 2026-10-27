/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Basic

/-!
# Scalar power series for hypergeometric differential equations

These lemmas specialize Mathlib's analytic differentiation machinery to complex scalar
coefficients. They also keep track of multiplication by the independent variable.
-/

@[expose] public section

open Complex FormalMultilinearSeries
open scoped Topology ENNReal

noncomputable section

namespace DLMF.Hypergeometric

/-- Adding a natural number preserves exclusion of the nonpositive integers. -/
theorem not_neg_nat_add_nat {a : ℂ} (ha : ∀ k : ℕ, a ≠ -k) (m : ℕ) :
    ∀ k : ℕ, a + m ≠ -k := by
  intro k h
  apply ha (k + m)
  push_cast
  linear_combination h

/-- Mathlib's left Pochhammer recurrence in the project's notation. -/
theorem poch_succ_left (a : ℂ) (n : ℕ) : poch a (n + 1) = a * poch (a + 1) n := by
  simp [poch, ascPochhammer_succ_left, Polynomial.eval_comp]

/-- Termwise differentiation, as a direct scalar specialization of Mathlib's
`HasFPowerSeriesOnBall.fderiv`. -/
theorem _root_.HasFPowerSeriesOnBall.deriv_ofScalars {f : ℂ → ℂ} {c : ℕ → ℂ} {r : ℝ≥0∞}
    (h : HasFPowerSeriesOnBall f (ofScalars ℂ c) 0 r) :
    HasFPowerSeriesOnBall (deriv f) (ofScalars ℂ (fun n => (n + 1) * c (n + 1))) 0 r := by
  have hd := (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).comp_hasFPowerSeriesOnBall h.fderiv
  have heq : (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).compFormalMultilinearSeries
      (ofScalars ℂ c).derivSeries = ofScalars ℂ (fun n => (n + 1) * c (n + 1)) := by
    ext n
    simp only [ContinuousLinearMap.compFormalMultilinearSeries_apply,
      ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply]
    rw [apply_eq_prod_smul_coeff]
    simp [derivSeries_coeff_one, coeff_ofScalars, ofScalars, mul_comm]
  simpa only [heq, Function.comp_def, ContinuousLinearMap.apply_apply,
    fderiv_eq_deriv_mul, mul_one] using hd

/-- Scalar coefficients give the usual series sum on the ball. -/
theorem _root_.HasFPowerSeriesOnBall.hasSum_mul_pow {f : ℂ → ℂ} {c : ℕ → ℂ} {r : ℝ≥0∞}
    (h : HasFPowerSeriesOnBall f (ofScalars ℂ c) 0 r) {z : ℂ}
    (hz : z ∈ Metric.eball (0 : ℂ) r) : HasSum (fun n => c n * z ^ n) (f z) := by
  simpa only [ofScalars_apply_eq, smul_eq_mul, zero_add] using h.hasSum hz

/-- Shifting a power series after multiplication by its variable. -/
theorem _root_.HasSum.mul_pow_shift {c : ℕ → ℂ} {s z : ℂ}
    (h : HasSum (fun n => c (n + 1) * z ^ n) s) (h0 : c 0 = 0) :
    HasSum (fun n => c n * z ^ n) (z * s) := by
  rw [← hasSum_nat_add_iff' 1]
  simpa [Finset.sum_range_one, h0, pow_succ, mul_comm, mul_left_comm, mul_assoc] using
    h.mul_left z

/-- Multiplying the differentiated series by `z` restores its original indexing. -/
theorem _root_.HasFPowerSeriesOnBall.hasSum_z_mul_deriv {f : ℂ → ℂ} {c : ℕ → ℂ} {r : ℝ≥0∞}
    (h : HasFPowerSeriesOnBall f (ofScalars ℂ c) 0 r) {z : ℂ}
    (hz : z ∈ Metric.eball (0 : ℂ) r) :
    HasSum (fun n : ℕ => (n : ℂ) * c n * z ^ n) (z * deriv f z) := by
  apply HasSum.mul_pow_shift (c := fun n => (n : ℂ) * c n) ?_ (by simp)
  simpa only [Nat.cast_add, Nat.cast_one] using h.deriv_ofScalars.hasSum_mul_pow hz

/-- A quadratic coefficient recurrence gives a second-order differential equation.
This applies to both the Gauss and confluent hypergeometric series. -/
theorem _root_.HasFPowerSeriesOnBall.ode_of_recurrence {f : ℂ → ℂ} {c : ℕ → ℂ} {r : ℝ≥0∞}
    (h : HasFPowerSeriesOnBall f (ofScalars ℂ c) 0 r) {A B C D : ℂ}
    (hrec : ∀ n : ℕ, (n + 1 : ℂ) * (D + n) * c (n + 1) =
      (A * n * (n - 1) + B * n + C) * c n) {z : ℂ}
    (hz : z ∈ Metric.eball (0 : ℂ) r) :
    z * (1 - A * z) * deriv (deriv f) z + (D - B * z) * deriv f z - C * f z = 0 := by
  have h0 := h.hasSum_mul_pow hz
  have h1 := h.deriv_ofScalars.hasSum_mul_pow hz
  have hz1 := h.hasSum_z_mul_deriv hz
  have hz2 := h.deriv_ofScalars.hasSum_z_mul_deriv hz
  have hzz2 : HasSum (fun n : ℕ => (n : ℂ) * (n - 1) * c n * z ^ n)
      (z ^ 2 * deriv (deriv f) z) := by
    have hs : HasSum (fun n : ℕ =>
        (n + 1 : ℂ) * ((n + 1 : ℂ) - 1) * c (n + 1) * z ^ n)
        (z * deriv (deriv f) z) := by
      convert hz2 using 1
      funext n
      ring
    have ht := HasSum.mul_pow_shift (c := fun n => (n : ℂ) * (n - 1) * c n)
      (by simpa only [Nat.cast_add, Nat.cast_one] using hs) (by simp)
    convert ht using 1
    ring
  have hleft := hz2.add (h1.mul_left D)
  have hright := ((hzz2.mul_left A).add (hz1.mul_left B)).add (h0.mul_left C)
  have heq : (fun n : ℕ => (n : ℂ) * ((n + 1) * c (n + 1)) * z ^ n +
        D * ((n + 1) * c (n + 1) * z ^ n)) =
      (fun n : ℕ => (A * ((n : ℂ) * (n - 1) * c n * z ^ n) +
        B * ((n : ℂ) * c n * z ^ n)) + C * (c n * z ^ n)) := by
    funext n
    calc
      _ = ((n + 1 : ℂ) * (D + n) * c (n + 1)) * z ^ n := by ring
      _ = _ := by rw [hrec]; ring
  rw [heq] at hleft
  have he := hleft.unique hright
  linear_combination he

/-- The Gauss series has radius at least one, including terminating numerator parameters. -/
theorem ordinaryHypergeometricSeries_radius_ge_one (a b c : ℂ) :
    1 ≤ (ordinaryHypergeometricSeries ℂ a b c).radius := by
  by_cases ha : ∃ k : ℕ, a = -k
  · obtain ⟨k, rfl⟩ := ha
    rw [ordinaryHypergeometric_radius_top_of_neg_nat₁]
    exact le_top
  by_cases hb : ∃ k : ℕ, b = -k
  · obtain ⟨k, rfl⟩ := hb
    rw [ordinaryHypergeometric_radius_top_of_neg_nat₂]
    exact le_top
  by_cases hc : ∃ k : ℕ, c = -k
  · obtain ⟨k, rfl⟩ := hc
    rw [ordinaryHypergeometric_radius_top_of_neg_nat₃]
    exact le_top
  rw [ordinaryHypergeometricSeries_radius_eq_one ℂ a b c]
  · intro k
    exact ⟨fun h => ha ⟨k, by linear_combination h⟩,
      fun h => hb ⟨k, by linear_combination h⟩,
      fun h => hc ⟨k, by linear_combination h⟩⟩

/-- The Gauss series represents `₂F₁` throughout the open unit disk. -/
theorem hasFPowerSeriesOnBall_ordinaryHypergeometric (a b c : ℂ) :
    HasFPowerSeriesOnBall (₂F₁ a b c) (ofScalars ℂ (gaussHGCoeff a b c)) 0 1 := by
  have hr := ordinaryHypergeometricSeries_radius_ge_one a b c
  have h := ((ordinaryHypergeometricSeries ℂ a b c).hasFPowerSeriesOnBall
    (lt_of_lt_of_le (by simp) hr)).mono (by simp) hr
  change HasFPowerSeriesOnBall (₂F₁ a b c) (ordinaryHypergeometricSeries ℂ a b c) 0 1 at h
  have heq : ordinaryHypergeometricCoefficient a b c = gaussHGCoeff a b c :=
    funext (ordinaryHypergeometricCoefficient_eq a b c)
  simpa only [ordinaryHypergeometricSeries, heq] using h

/-- Absolute summability of the Gauss series inside the unit disk. -/
theorem summable_norm_gaussHGCoeff_mul_pow (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable fun n : ℕ => ‖gaussHGCoeff a b c n * z ^ n‖ := by
  have h := hasFPowerSeriesOnBall_ordinaryHypergeometric a b c
  have hr : (‖z‖₊ : ENNReal) < (ofScalars ℂ (gaussHGCoeff a b c)).radius := by
    refine lt_of_lt_of_le ?_ h.r_le
    rw [← ENNReal.coe_one, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_one]
    exact hz
  refine ((ofScalars ℂ (gaussHGCoeff a b c)).summable_norm_mul_pow hr).congr
    fun n => ?_
  rw [ofScalars_norm, norm_mul, norm_pow, coe_nnnorm]

/-- Helper lemma for binomial expansions of `(1-z)^{-β}`. -/
theorem gaussHGCoeff_self_right (β : ℂ) (n : ℕ) :
    gaussHGCoeff β 1 1 n = poch β n / n.factorial := by
  have h1 : poch (1 : ℂ) n = n.factorial := poch_nat_one n
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  simp [gaussHGCoeff, h1]
  field [hf]

/-- Helper lemma for binomial expansions of `(1-z)^{-β}`. -/
theorem one_not_neg_nat : ∀ k : ℕ, (1 : ℂ) ≠ -k := by
  intro k h
  have : (1 : ℝ) = -k := by simpa using congrArg Complex.re h
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

/-- The binomial series `∑ (β)_n / n! z^n = (1-z)^{-β}` for `|z| < 1`. -/
theorem hasSum_poch_div_factorial {β z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => poch β n / n.factorial * z ^ n) ((1 - z) ^ (-β)) := by
  have hc : ∀ k : ℕ, (k : ℂ) ≠ -(1 : ℂ) := fun k hk =>
    one_not_neg_nat k (neg_eq_iff_eq_neg.mp hk.symm)
  have hval := ordinaryHypergeometric_eq_one_sub_neg_cpow (a := β) (c := 1) hc hz
  have hs := (hasFPowerSeriesOnBall_ordinaryHypergeometric β 1 1).hasSum_mul_pow
    (mem_eball_one_of_norm_lt_one hz)
  have hfun : (fun n : ℕ => gaussHGCoeff β 1 1 n * z ^ n) =
      fun n => poch β n / n.factorial * z ^ n := by
    funext n
    rw [gaussHGCoeff_self_right]
  rwa [hfun, hval] at hs

/-- Helper lemma for generating-function estimates. -/
theorem poch_eval_nonneg {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    0 ≤ (ascPochhammer ℝ n).eval x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ascPochhammer_succ_eval]
    exact mul_nonneg ih (add_nonneg hx (Nat.cast_nonneg n))

/-- Helper lemma for generating-function estimates. -/
theorem norm_poch_le (z : ℂ) (n : ℕ) :
    ‖poch z n‖ ≤ (ascPochhammer ℝ n).eval ‖z‖ := by
  induction n with
  | zero => simp [poch_zero]
  | succ n ih =>
    rw [poch_succ, norm_mul, ascPochhammer_succ_eval]
    have hle : ‖z + n‖ ≤ ‖z‖ + n := by
      calc
        ‖z + (n : ℂ)‖ ≤ ‖z‖ + ‖(n : ℂ)‖ := norm_add_le _ _
        _ = ‖z‖ + n := by simp
    have hnn : 0 ≤ (ascPochhammer ℝ n).eval ‖z‖ := poch_eval_nonneg (norm_nonneg z) n
    exact mul_le_mul ih hle (norm_nonneg _) hnn

/-- Helper lemma for generating-function estimates. -/
theorem poch_eval_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (n : ℕ) :
    (ascPochhammer ℝ n).eval x ≤ (ascPochhammer ℝ n).eval y := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval]
    exact mul_le_mul ih (add_le_add hxy le_rfl)
      (add_nonneg hx (Nat.cast_nonneg n)) (poch_eval_nonneg (le_trans hx hxy) n)

/-- Helper lemma for generating-function estimates. -/
theorem poch_ofReal (x : ℝ) (n : ℕ) :
    poch (x : ℂ) n = ↑((ascPochhammer ℝ n).eval x) := by
  induction n with
  | zero => simp [poch_zero]
  | succ n ih =>
    rw [poch_succ, ascPochhammer_succ_eval, ih]
    push_cast
    ring

end DLMF.Hypergeometric
