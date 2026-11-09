/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Asymptotics.AsymptoticExpansion
public import DLMFMathlib.Analysis.Integral.LaplaceMoments
public import Mathlib.Algebra.Ring.GeomSum

/-!
# Elementary asymptotic power series

The finite geometric identity gives the reciprocal-linear expansions at zero and
infinity. The negative-axis exponential Taylor bound gives its complete asymptotic
power series at zero, including the order-zero bound.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Finset Asymptotics Complex
open scoped Topology

/-- The exact finite geometric remainder for the reciprocal-linear function. -/
theorem inv_one_add_sub_sum_neg_pow {𝕜 : Type*} [Field 𝕜] {z : 𝕜}
    (hz : 1 + z ≠ 0) (N : ℕ) :
    (1 + z)⁻¹ - ∑ k ∈ range N, (-z) ^ k = (-z) ^ N / (1 + z) := by
  apply (eq_div_iff hz).mpr
  have h := geom_sum_mul_neg (-z) N
  simp only [sub_neg_eq_add] at h
  rw [sub_mul, inv_mul_cancel₀ hz, h]
  ring

/-- The exact reciprocal-linear remainder in inverse powers. -/
theorem inv_one_add_sub_sum_inv_pow {𝕜 : Type*} [Field 𝕜] {z : 𝕜}
    (hz : z ≠ 0) (h1z : 1 + z ≠ 0) (N : ℕ) :
    (1 + z)⁻¹ - ∑ k ∈ range N, (-1 : 𝕜) ^ k * z⁻¹ ^ (k + 1) =
      (-1 : 𝕜) ^ N * z⁻¹ ^ N / (1 + z) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [sum_range_succ, sub_add_eq_sub_sub, ih, pow_succ, pow_succ]
      field_simp
      ring

namespace Asymptotics

/-- The negative real exponential has its Taylor expansion at zero in complex form. -/
theorem hasAsymptoticExpansion_exp_neg_ofReal :
    HasAsymptoticExpansion (𝓝[>] 0) (fun (n : ℕ) (t : ℝ) => (t : ℂ) ^ (n : ℂ))
      (fun n => (-1 : ℂ) ^ n / (n.factorial : ℂ)) (fun t : ℝ => Complex.exp (-(t : ℂ))) := by
  intro N
  refine IsBigO.of_bound (((N - 1).factorial : ℝ)⁻¹) ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hsum : ∑ n ∈ range N, (t : ℂ) ^ (n : ℂ) * ((-1 : ℂ) ^ n / (n.factorial : ℂ)) =
      ∑ n ∈ range N, (-(t : ℂ)) ^ n / (n.factorial : ℂ) := by
    apply sum_congr rfl
    intro n _
    rw [cpow_natCast, neg_pow]
    ring
  simp only [smul_eq_mul]
  rw [hsum, cpow_natCast, norm_pow, norm_real, Real.norm_of_nonneg ht.le]
  exact (Complex.norm_exp_neg_ofReal_sub_sum_le ht.le N).trans_eq (by ring)

/-- The reciprocal-linear Taylor expansion at zero has alternating unit coefficients. -/
theorem hasAsymptoticExpansion_inv_one_add_atZero :
    HasAsymptoticExpansion (𝓝[>] 0) (fun (n : ℕ) (t : ℝ) => (t : ℂ) ^ (n : ℂ))
      (fun n => (-1 : ℂ) ^ n) (fun t : ℝ => (1 + (t : ℂ))⁻¹) := by
  intro N
  refine IsBigO.of_bound 1 ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hden : 1 + (t : ℂ) ≠ 0 := by
    have hre : 0 < (1 + (t : ℂ)).re := by
      simp only [add_re, one_re, ofReal_re]
      linarith [show 0 < t from ht]
    exact ne_zero_of_re_pos hre
  have hsum : ∑ n ∈ range N, (t : ℂ) ^ (n : ℂ) * (-1 : ℂ) ^ n =
      ∑ n ∈ range N, (-(t : ℂ)) ^ n := by
    apply sum_congr rfl
    intro n _
    rw [cpow_natCast, neg_pow]
    ring
  simp only [smul_eq_mul, one_mul]
  have hd : ‖1 + (t : ℂ)‖ = 1 + t := by
    rw [← ofReal_one, ← ofReal_add, norm_real, Real.norm_of_nonneg (by
      linarith [show 0 < t from ht] : 0 ≤ 1 + t)]
  rw [hsum, inv_one_add_sub_sum_neg_pow hden, norm_div, norm_pow, norm_neg,
    cpow_natCast, norm_pow, hd, norm_real, Real.norm_of_nonneg ht.le]
  exact div_le_self (pow_nonneg ht.le N) (by linarith [show 0 < t from ht])

/-- The reciprocal-linear expansion at positive infinity has alternating inverse powers. -/
theorem hasAsymptoticExpansion_inv_one_add_atTop :
    HasAsymptoticExpansion atTop
      (fun (n : ℕ) (t : ℝ) => (t : ℂ) ^ (-((n : ℂ) + 1)))
      (fun n => (-1 : ℂ) ^ n) (fun t : ℝ => (1 + (t : ℂ))⁻¹) := by
  intro N
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  have hden : 1 + (t : ℂ) ≠ 0 := by
    apply ne_zero_of_re_pos
    simp
    linarith
  have hp (n : ℕ) : (t : ℂ) ^ (-((n : ℂ) + 1)) = (t : ℂ)⁻¹ ^ (n + 1) := by
    rw [← Nat.cast_add_one, cpow_neg, cpow_natCast, inv_pow]
  simp only [smul_eq_mul, hp, one_mul]
  rw [show (∑ n ∈ range N, (t : ℂ)⁻¹ ^ (n + 1) * (-1 : ℂ) ^ n) =
      ∑ n ∈ range N, (-1 : ℂ) ^ n * (t : ℂ)⁻¹ ^ (n + 1) by
        apply sum_congr rfl; intro n _; ring,
    inv_one_add_sub_sum_inv_pow ht0 hden, norm_div, norm_mul, norm_pow,
    norm_neg, norm_one, one_pow, one_mul]
  have hd : ‖1 + (t : ℂ)‖ = 1 + t := by
    rw [← ofReal_one, ← ofReal_add, norm_real,
      Real.norm_of_nonneg (by linarith : 0 ≤ 1 + t)]
  simp only [norm_pow, norm_inv, hd, norm_real, Real.norm_of_nonneg ht.le]
  calc t⁻¹ ^ N / (1 + t) ≤ t⁻¹ ^ N / t :=
      div_le_div_of_nonneg_left (pow_nonneg (inv_nonneg.mpr ht.le) N) ht (by linarith)
    _ = _ := by rw [pow_succ, div_eq_mul_inv]

end Asymptotics
