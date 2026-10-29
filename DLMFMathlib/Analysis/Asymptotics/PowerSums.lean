/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Bounds for partial sums of real powers

Integral comparison bounds the partial sums of `j^p`, with the logarithmic
case stated separately. These estimates do not require an asymptotic expansion.
-/

@[expose] public noncomputable section

open Filter Finset Set Asymptotics MeasureTheory
open scoped Topology

namespace Real

/-- A decreasing real power has partial sums bounded by one plus its integral. -/
theorem sum_Ico_rpow_le_one_add_integral {p : ℝ} (hp : p ≤ 0) {n : ℕ} (hn : 1 ≤ n) :
    ∑ j ∈ Finset.Ico 1 n, (j : ℝ) ^ p ≤ 1 + ∫ x in (1 : ℝ)..n, x ^ p := by
  have hanti : AntitoneOn (fun x : ℝ => x ^ p) (Icc (1 : ℝ) n) :=
    fun x hx y hy hxy => rpow_le_rpow_of_nonpos (zero_lt_one.trans_le hx.1) hxy hp
  have hb := AntitoneOn.sum_le_integral_Ico (f := fun x : ℝ => x ^ p) hn
    (by simpa only [Nat.cast_one] using hanti)
  simp only [Nat.cast_one] at hb
  have ht := Finset.sum_Ico_sub (fun j : ℕ => (j : ℝ) ^ p) hn
  rw [Finset.sum_sub_distrib] at ht
  simp only [Nat.cast_one, one_rpow] at ht
  linarith [rpow_nonneg (Nat.cast_nonneg n) p]

/-- Partial sums of a summable real power are bounded. -/
theorem sum_Ico_rpow_isBigO_one {p : ℝ} (hp : p < -1) :
    (fun n : ℕ => ∑ j ∈ Finset.Ico 1 n, (j : ℝ) ^ p) =O[atTop] fun _ => (1 : ℝ) := by
  have hs := summable_nat_rpow.mpr hp
  refine IsBigO.of_bound (∑' j : ℕ, (j : ℝ) ^ p) (Eventually.of_forall fun n => ?_)
  rw [norm_one, mul_one,
    Real.norm_of_nonneg (sum_nonneg fun j _ => rpow_nonneg (Nat.cast_nonneg _) _)]
  exact hs.sum_le_tsum _ (fun j _ => rpow_nonneg (Nat.cast_nonneg j) p)

/-- The harmonic partial sums are bounded by a constant times the logarithm. -/
theorem sum_Ico_rpow_neg_one_isBigO_log :
    (fun n : ℕ => ∑ j ∈ Finset.Ico 1 n, (j : ℝ) ^ (-1 : ℝ)) =O[atTop]
      fun n => Real.log n := by
  have ht := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  refine IsBigO.of_bound 2 ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ), ht.eventually (eventually_ge_atTop 1)] with n hn hlog
  dsimp only [Function.comp_def] at hlog
  have hb := sum_Ico_rpow_le_one_add_integral (by norm_num : (-1 : ℝ) ≤ 0) hn
  rw [show (fun x : ℝ => x ^ (-1 : ℝ)) = fun x => x⁻¹ by ext; exact rpow_neg_one _] at hb
  rw [integral_inv (by simp [uIcc_of_le (show (1 : ℝ) ≤ n by exact_mod_cast hn)]),
    div_one] at hb
  rw [Real.norm_of_nonneg (sum_nonneg fun j _ => rpow_nonneg (Nat.cast_nonneg _) _),
    Real.norm_of_nonneg (by linarith : 0 ≤ Real.log n)]
  linarith

/-- For exponent greater than `-1`, the partial power sum is `O(n^(p+1))`. -/
theorem sum_Ico_rpow_isBigO {p : ℝ} (hp : -1 < p) :
    (fun n : ℕ => ∑ j ∈ Finset.Ico 1 n, (j : ℝ) ^ p) =O[atTop]
      fun n => (n : ℝ) ^ (p + 1) := by
  rcases le_total 0 p with hp0 | hp0
  · refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
    rw [one_mul, Real.norm_of_nonneg (sum_nonneg fun j _ => rpow_nonneg (Nat.cast_nonneg _) _),
      Real.norm_of_nonneg (rpow_nonneg (Nat.cast_nonneg n) _)]
    calc ∑ j ∈ Finset.Ico 1 n, (j : ℝ) ^ p ≤
          ∑ _j ∈ Finset.Ico 1 n, (n : ℝ) ^ p := sum_le_sum fun j hj =>
            rpow_le_rpow (Nat.cast_nonneg j) (by exact_mod_cast (mem_Ico.mp hj).2.le) hp0
      _ ≤ (n : ℝ) * (n : ℝ) ^ p := by
        simp only [sum_const, Nat.card_Ico, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le n 1)
          (rpow_nonneg (Nat.cast_nonneg n) p)
      _ = (n : ℝ) ^ (p + 1) := by rw [rpow_add hn0, rpow_one, mul_comm]
  · refine IsBigO.of_bound (1 + 1 / (p + 1)) ?_
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn
    have hpow : 1 ≤ (n : ℝ) ^ (p + 1) := one_le_rpow hn1 (by linarith)
    have hb := sum_Ico_rpow_le_one_add_integral hp0 hn
    rw [integral_rpow (Or.inr ⟨by linarith, by
      rw [uIcc_of_le hn1]; simp only [Set.mem_Icc, not_and_or]; exact Or.inl (by norm_num)⟩),
      one_rpow] at hb
    rw [Real.norm_of_nonneg (sum_nonneg fun j _ => rpow_nonneg (Nat.cast_nonneg _) _),
      Real.norm_of_nonneg (rpow_nonneg (Nat.cast_nonneg n) _)]
    have hden : 0 < p + 1 := by linarith
    have hdiv : ((n : ℝ) ^ (p + 1) - 1) / (p + 1) ≤ (n : ℝ) ^ (p + 1) / (p + 1) :=
      div_le_div_of_nonneg_right (by linarith) hden.le
    calc _ ≤ 1 + (n : ℝ) ^ (p + 1) / (p + 1) := hb.trans (add_le_add le_rfl hdiv)
      _ ≤ (n : ℝ) ^ (p + 1) + (n : ℝ) ^ (p + 1) / (p + 1) := add_le_add hpow le_rfl
      _ = (1 + 1 / (p + 1)) * (n : ℝ) ^ (p + 1) := by ring

/-- Away from exponent `-1`, a bound valid on both sides of the summability threshold. -/
theorem sum_Ico_rpow_isBigO_add_one {p : ℝ} (hp : p ≠ -1) :
    (fun n : ℕ => ∑ j ∈ Finset.Ico 1 n, (j : ℝ) ^ p) =O[atTop]
      fun n => (n : ℝ) ^ (p + 1) + 1 := by
  rcases lt_or_gt_of_ne hp with hp | hp
  · exact (sum_Ico_rpow_isBigO_one hp).trans (IsBigO.of_norm_le fun n => by
      rw [norm_one]
      linarith [rpow_nonneg (Nat.cast_nonneg n) (p + 1)])
  · exact (sum_Ico_rpow_isBigO hp).trans (IsBigO.of_norm_le fun n => by
      rw [Real.norm_of_nonneg (rpow_nonneg (Nat.cast_nonneg n) _)]; linarith)

end Real
