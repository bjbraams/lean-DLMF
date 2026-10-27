/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# BBP-type formulas and Gauss's Machin formula (Duverney §8.4)

Writing `1/(mk+j) = ∫₀¹ y^{mk+j-1} dy` and summing the geometric series under the integral sign
gives `∑ aᵏ/(mk+j) = ∫₀¹ y^{j-1}/(1 - a yᵐ) dy` for `0 ≤ a < 1` (`hasSum_pow_div_mul_add`,
Duverney (8.92)–(8.93)). A linear combination of such sums is then the integral of a rational
function, which is evaluated by an explicit primitive. This gives:
* the Bailey–Borwein–Plouffe formula
  `π = ∑ 16^{-k} (4/(8k+1) - 2/(8k+4) - 1/(8k+5) - 1/(8k+6))` (8.90);
* `ln 3 = ∑ 4^{-k}/(2k+1)` and `(3/2) ln 2 = ∑ 9^{-k}/(2k+1)` (8.81)–(8.82);
* `4 ln 5 = ∑ 16^{-k}(4/(4k+1) + 4/(4k+2) + 1/(4k+3))` (8.83);
* `(8/3) ln 3 = ∑ 64^{-k}(4/(6k+2) + 2/(6k+3) + 1/(6k+4))` (Exercise 8.15).

Gauss's Machin-like formula `12 arctan(1/18) + 8 arctan(1/57) - 5 arctan(1/239) = π/4` (8.88)
follows from Mathlib's arctangent addition formula, beside Mathlib's other Machin formulas.
-/

@[expose] public section

open Real Filter MeasureTheory intervalIntegral Set

noncomputable section

namespace DLMF.Constants

/-- `∑ aᵏ/(mk+j) = ∫₀¹ y^{j-1}/(1 - a yᵐ) dy` for `0 ≤ a < 1`. -/
theorem hasSum_pow_div_mul_add (a : ℝ) (ha0 : 0 ≤ a) (ha : a < 1) (m j : ℕ) (hj : 1 ≤ j) :
    HasSum (fun k : ℕ => a ^ k / (m * k + j))
      (∫ y in (0 : ℝ)..1, y ^ (j - 1) / (1 - a * y ^ m)) := by
  have hint (k : ℕ) : a ^ k / (m * k + j) = ∫ y in (0 : ℝ)..1, a ^ k * y ^ (m * k + j - 1) := by
    rw [intervalIntegral.integral_const_mul, integral_pow]
    have : ((m * k + j - 1 : ℕ) : ℝ) + 1 = m * k + j := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [this, show m * k + j - 1 + 1 = m * k + j by omega, zero_pow (by omega)]
    simp [div_eq_mul_inv]
  simp_rw [hint]
  refine intervalIntegral.hasSum_integral_of_dominated_convergence (fun k _ => a ^ k)
    (fun k => (by fun_prop : Continuous fun y : ℝ => a ^ k * y ^ (m * k + j - 1))
      |>.aestronglyMeasurable)
    (fun k => Eventually.of_forall fun y hy => ?_)
    (Eventually.of_forall fun _ _ => summable_geometric_of_lt_one ha0 ha)
    intervalIntegrable_const (Eventually.of_forall fun y hy => ?_)
  · rw [uIoc_of_le zero_le_one] at hy
    rw [norm_mul, Real.norm_of_nonneg (pow_nonneg ha0 _),
      Real.norm_of_nonneg (pow_nonneg hy.1.le _)]
    exact mul_le_of_le_one_right (pow_nonneg ha0 _) (pow_le_one₀ hy.1.le hy.2)
  · rw [uIoc_of_le zero_le_one] at hy
    have h0 : 0 ≤ a * y ^ m := mul_nonneg ha0 (pow_nonneg hy.1.le _)
    have h1 : a * y ^ m < 1 := by
      calc a * y ^ m ≤ a * 1 := by gcongr; exact pow_le_one₀ hy.1.le hy.2
        _ < 1 := by linarith
    have hg := (hasSum_geometric_of_lt_one h0 h1).mul_left (y ^ (j - 1))
    refine hg.congr_fun fun k => ?_
    rw [show m * k + j - 1 = m * k + (j - 1) by omega, pow_add, mul_pow, pow_mul]
    ring

/-- The BBP integrands are integrable on `[0, 1]`. -/
theorem intervalIntegrable_bbp (a : ℝ) (ha0 : 0 ≤ a) (ha : a < 1) (m n : ℕ) :
    IntervalIntegrable (fun y : ℝ => y ^ n / (1 - a * y ^ m)) volume 0 1 := by
  refine ContinuousOn.intervalIntegrable fun y hy => ?_
  rw [uIcc_of_le zero_le_one] at hy
  have : a * y ^ m < 1 := by
    calc a * y ^ m ≤ a * 1 := by gcongr; exact pow_le_one₀ hy.1 hy.2
      _ < 1 := by linarith
  exact ((continuous_pow n).continuousAt.div (by fun_prop) (by linarith)).continuousWithinAt

/-- **The Bailey–Borwein–Plouffe formula** (Duverney (8.90)):
`π = ∑ 16^{-k} (4/(8k+1) - 2/(8k+4) - 1/(8k+5) - 1/(8k+6))`. -/
theorem hasSum_bbp_pi :
    HasSum (fun k : ℕ => (1 / 16 : ℝ) ^ k *
      (4 / (8 * k + 1) - 2 / (8 * k + 4) - 1 / (8 * k + 5) - 1 / (8 * k + 6))) π := by
  have ha0 : (0 : ℝ) ≤ 1 / 16 := by norm_num
  have ha : (1 / 16 : ℝ) < 1 := by norm_num
  have h := ((((hasSum_pow_div_mul_add _ ha0 ha 8 1 le_rfl).mul_left 4).sub
    ((hasSum_pow_div_mul_add _ ha0 ha 8 4 (by norm_num)).mul_left 2)).sub
    (hasSum_pow_div_mul_add _ ha0 ha 8 5 (by norm_num))).sub
    (hasSum_pow_div_mul_add _ ha0 ha 8 6 (by norm_num))
  convert h using 1
  · funext k; push_cast; ring
  have hI (n : ℕ) := intervalIntegrable_bbp (1 / 16) ha0 ha 8 n
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub ((hI _).const_mul _) ((hI _).const_mul _),
    ← intervalIntegral.integral_sub (((hI _).const_mul _).sub ((hI _).const_mul _)) (hI _),
    ← intervalIntegral.integral_sub ((((hI _).const_mul _).sub ((hI _).const_mul _)).sub (hI _))
      (hI _)]
  set F : ℝ → ℝ := fun y => 2 * log (2 - y ^ 2) - 2 * log (y ^ 2 - 2 * y + 2) +
    4 * arctan (y - 1)
  have hF : ∀ y ∈ uIcc (0 : ℝ) 1, HasDerivAt F
      (4 * (y ^ (1 - 1) / (1 - 1 / 16 * y ^ 8)) - 2 * (y ^ (4 - 1) / (1 - 1 / 16 * y ^ 8)) -
        y ^ (5 - 1) / (1 - 1 / 16 * y ^ 8) - y ^ (6 - 1) / (1 - 1 / 16 * y ^ 8)) y := by
    intro y hy
    rw [uIcc_of_le zero_le_one] at hy
    have h1 : 0 < 2 - y ^ 2 := by nlinarith [hy.1, hy.2]
    have h2 : 0 < y ^ 2 - 2 * y + 2 := by nlinarith
    have h3 : (1 - 1 / 16 * y ^ 8) ≠ 0 := by
      have : y ^ 8 ≤ 1 := pow_le_one₀ hy.1 hy.2
      linarith
    have d := ((((hasDerivAt_id y).pow 2).const_sub 2).log h1.ne').const_mul 2 |>.sub
      (((((hasDerivAt_id y).pow 2).sub ((hasDerivAt_id y).const_mul 2)).add_const 2).log
        h2.ne' |>.const_mul 2) |>.add (((hasDerivAt_id y).sub_const 1).arctan.const_mul 4)
    refine d.congr_deriv ?_
    have h4 : 1 + (y - 1) ^ 2 ≠ 0 := by positivity
    simp only [id, Pi.pow_apply, Pi.sub_apply]
    norm_num
    have h2' : y * (y - 2) + 2 ≠ 0 := by nlinarith
    have h5 : 16 - y ^ 8 ≠ 0 := by
      have : y ^ 8 ≤ 1 := pow_le_one₀ hy.1 hy.2
      linarith
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF (by
    exact ((((hI _).const_mul _).sub ((hI _).const_mul _)).sub (hI _)).sub (hI _))]
  simp only [F]
  norm_num
  ring

/-- `ln 3 = ∑ 4^{-k}/(2k+1)` (Duverney (8.81)). -/
theorem hasSum_log_three :
    HasSum (fun k : ℕ => (1 / 4 : ℝ) ^ k / (2 * k + 1)) (log 3) := by
  have h := hasSum_pow_div_mul_add (1 / 4) (by norm_num) (by norm_num) 2 1 le_rfl
  convert h using 1
  · funext k; push_cast; ring
  set F : ℝ → ℝ := fun y => log (2 + y) - log (2 - y)
  have hF : ∀ y ∈ uIcc (0 : ℝ) 1, HasDerivAt F (y ^ (1 - 1) / (1 - 1 / 4 * y ^ 2)) y := by
    intro y hy
    rw [uIcc_of_le zero_le_one] at hy
    have h1 : 0 < 2 + y := by linarith [hy.1]
    have h2 : 0 < 2 - y := by linarith [hy.2]
    refine ((((hasDerivAt_id y).const_add 2).log h1.ne').sub
      (((hasDerivAt_id y).const_sub 2).log h2.ne')).congr_deriv ?_
    have h3 : 4 - y ^ 2 ≠ 0 := by nlinarith [hy.1, hy.2]
    simp only [id_eq]; norm_num
    field_simp; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    (intervalIntegrable_bbp _ (by norm_num) (by norm_num) 2 _)]
  simp only [F]; norm_num

/-- `ln 2 = (2/3) ∑ 9^{-k}/(2k+1)` (Duverney (8.82)). -/
theorem hasSum_log_two :
    HasSum (fun k : ℕ => (1 / 9 : ℝ) ^ k / (2 * k + 1)) (3 / 2 * log 2) := by
  have h := hasSum_pow_div_mul_add (1 / 9) (by norm_num) (by norm_num) 2 1 le_rfl
  convert h using 1
  · funext k; push_cast; ring
  set F : ℝ → ℝ := fun y => 3 / 2 * (log (3 + y) - log (3 - y))
  have hF : ∀ y ∈ uIcc (0 : ℝ) 1, HasDerivAt F (y ^ (1 - 1) / (1 - 1 / 9 * y ^ 2)) y := by
    intro y hy
    rw [uIcc_of_le zero_le_one] at hy
    have h1 : 0 < 3 + y := by linarith [hy.1]
    have h2 : 0 < 3 - y := by linarith [hy.2]
    refine (((((hasDerivAt_id y).const_add 3).log h1.ne').sub
      (((hasDerivAt_id y).const_sub 3).log h2.ne')).const_mul (3 / 2)).congr_deriv ?_
    have h3 : 9 - y ^ 2 ≠ 0 := by nlinarith [hy.1, hy.2]
    simp only [id_eq]; norm_num
    field_simp; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    (intervalIntegrable_bbp _ (by norm_num) (by norm_num) 2 _)]
  simp only [F]; norm_num
  rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul two_ne_zero two_ne_zero]
  ring

/-- A BBP-type formula for `ln 5` (Duverney (8.83)):
`4 ln 5 = ∑ 16^{-k} (4/(4k+1) + 4/(4k+2) + 1/(4k+3))`. -/
theorem hasSum_bbp_log_five :
    HasSum (fun k : ℕ => (1 / 16 : ℝ) ^ k *
      (4 / (4 * k + 1) + 4 / (4 * k + 2) + 1 / (4 * k + 3))) (4 * log 5) := by
  have ha0 : (0 : ℝ) ≤ 1 / 16 := by norm_num
  have ha : (1 / 16 : ℝ) < 1 := by norm_num
  have h := (((hasSum_pow_div_mul_add _ ha0 ha 4 1 le_rfl).mul_left 4).add
    ((hasSum_pow_div_mul_add _ ha0 ha 4 2 (by norm_num)).mul_left 4)).add
    (hasSum_pow_div_mul_add _ ha0 ha 4 3 (by norm_num))
  convert h using 1
  · funext k; push_cast; ring
  have hI (n : ℕ) := intervalIntegrable_bbp (1 / 16) ha0 ha 4 n
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add ((hI _).const_mul _) ((hI _).const_mul _),
    ← intervalIntegral.integral_add (((hI _).const_mul _).add ((hI _).const_mul _)) (hI _)]
  set F : ℝ → ℝ := fun y => 4 * (log (y ^ 2 + 4) - 2 * log (2 - y))
  have hF : ∀ y ∈ uIcc (0 : ℝ) 1, HasDerivAt F
      (4 * (y ^ (1 - 1) / (1 - 1 / 16 * y ^ 4)) + 4 * (y ^ (2 - 1) / (1 - 1 / 16 * y ^ 4)) +
        y ^ (3 - 1) / (1 - 1 / 16 * y ^ 4)) y := by
    intro y hy
    rw [uIcc_of_le zero_le_one] at hy
    have h1 : 0 < y ^ 2 + 4 := by positivity
    have h2 : 0 < 2 - y := by linarith [hy.2]
    refine (((((hasDerivAt_id y).pow 2).add_const 4).log h1.ne').sub
      ((((hasDerivAt_id y).const_sub 2).log h2.ne').const_mul 2)).const_mul 4 |>.congr_deriv ?_
    have h5 : 16 - y ^ 4 ≠ 0 := by
      have : y ^ 4 ≤ 1 := pow_le_one₀ hy.1 hy.2
      linarith
    simp only [id, Pi.pow_apply]; norm_num
    field_simp; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    ((((hI _).const_mul _).add ((hI _).const_mul _)).add (hI _))]
  simp only [F]; norm_num
  rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul two_ne_zero two_ne_zero]
  ring

/-- A base-64 BBP-type formula for `ln 3` (Duverney, Exercise 8.15):
`(8/3) ln 3 = ∑ 64^{-k} (4/(6k+2) + 2/(6k+3) + 1/(6k+4))`. -/
theorem hasSum_bbp_log_three :
    HasSum (fun k : ℕ => (1 / 64 : ℝ) ^ k *
      (4 / (6 * k + 2) + 2 / (6 * k + 3) + 1 / (6 * k + 4))) (8 / 3 * log 3) := by
  have ha0 : (0 : ℝ) ≤ 1 / 64 := by norm_num
  have ha : (1 / 64 : ℝ) < 1 := by norm_num
  have h := (((hasSum_pow_div_mul_add _ ha0 ha 6 2 (by norm_num)).mul_left 4).add
    ((hasSum_pow_div_mul_add _ ha0 ha 6 3 (by norm_num)).mul_left 2)).add
    (hasSum_pow_div_mul_add _ ha0 ha 6 4 (by norm_num))
  convert h using 1
  · funext k; push_cast; ring
  have hI (n : ℕ) := intervalIntegrable_bbp (1 / 64) ha0 ha 6 n
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add ((hI _).const_mul _) ((hI _).const_mul _),
    ← intervalIntegral.integral_add (((hI _).const_mul _).add ((hI _).const_mul _)) (hI _)]
  set F : ℝ → ℝ := fun y => 8 / 3 *
    (2 * log (y ^ 2 - 2 * y + 4) - 3 * log (2 - y) - log (y + 2))
  have hF : ∀ y ∈ uIcc (0 : ℝ) 1, HasDerivAt F
      (4 * (y ^ (2 - 1) / (1 - 1 / 64 * y ^ 6)) + 2 * (y ^ (3 - 1) / (1 - 1 / 64 * y ^ 6)) +
        y ^ (4 - 1) / (1 - 1 / 64 * y ^ 6)) y := by
    intro y hy
    rw [uIcc_of_le zero_le_one] at hy
    have h1 : 0 < y ^ 2 - 2 * y + 4 := by nlinarith
    have h2 : 0 < 2 - y := by linarith [hy.2]
    have h3 : 0 < y + 2 := by linarith [hy.1]
    have dA := ((((hasDerivAt_id y).pow 2).sub ((hasDerivAt_id y).const_mul 2)).add_const 4).log
      h1.ne'
    have dB := ((hasDerivAt_id y).const_sub 2).log h2.ne'
    have dC := ((hasDerivAt_id y).add_const 2).log h3.ne'
    refine (((dA.const_mul 2).sub (dB.const_mul 3)).sub dC).const_mul (8 / 3) |>.congr_deriv ?_
    have h5 : 64 - y ^ 6 ≠ 0 := by
      have : y ^ 6 ≤ 1 := pow_le_one₀ hy.1 hy.2
      linarith
    have h1' : y * (y - 2) + 4 ≠ 0 := by nlinarith
    simp only [id, Pi.pow_apply, Pi.sub_apply]; norm_num
    field_simp; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    ((((hI _).const_mul _).add ((hI _).const_mul _)).add (hI _))]
  simp only [F]; norm_num
  rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul two_ne_zero two_ne_zero]
  ring

/-- **Gauss's Machin-like formula** (Duverney (8.88)):
`12 arctan(1/18) + 8 arctan(1/57) - 5 arctan(1/239) = π/4`. -/
theorem gauss_machin :
    12 * arctan 18⁻¹ + 8 * arctan 57⁻¹ - 5 * arctan 239⁻¹ = π / 4 := by
  have a2 : 2 * arctan 18⁻¹ = arctan (36 / 323) := by rw [two_mul_arctan] <;> norm_num
  have a4 : 2 * arctan (36 / 323) = arctan (23256 / 103033) := by
    rw [two_mul_arctan] <;> norm_num
  have a8 : 2 * arctan (23256 / 103033) = arctan (4792270896 / 10074957553) := by
    rw [two_mul_arctan] <;> norm_num
  have a12 : arctan (4792270896 / 10074957553) + arctan (23256 / 103033) =
      arctan (728065260080136 / 926604049600873) := by rw [arctan_add] <;> norm_num
  have b2 : 2 * arctan 57⁻¹ = arctan (57 / 1624) := by rw [two_mul_arctan] <;> norm_num
  have b4 : 2 * arctan (57 / 1624) = arctan (185136 / 2634127) := by
    rw [two_mul_arctan] <;> norm_num
  have b8 : 2 * arctan (185136 / 2634127) = arctan (975343472544 / 6904349713633) := by
    rw [two_mul_arctan] <;> norm_num
  have c2 : 2 * arctan 239⁻¹ = arctan (239 / 28560) := by rw [two_mul_arctan] <;> norm_num
  have c4 : 2 * arctan (239 / 28560) = arctan (13651680 / 815616479) := by
    rw [two_mul_arctan] <;> norm_num
  have c5 : arctan (13651680 / 815616479) + arctan 239⁻¹ =
      arctan (4078367999 / 194918686801) := by rw [arctan_add] <;> norm_num
  have s : arctan (728065260080136 / 926604049600873) +
      arctan (975343472544 / 6904349713633) = arctan (99498527400 / 95420159401) := by
    rw [arctan_add] <;> norm_num
  have t : arctan (99498527400 / 95420159401) + arctan (-(4078367999 / 194918686801)) =
      arctan 1 := by
    rw [arctan_add] <;> norm_num
  rw [arctan_neg, arctan_one] at t
  linarith

end DLMF.Constants

end
