/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Gamma.SeriesExpansions
public import DLMFMathlib.Algebra.BigOperators
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Ordered alternating digamma sums

Temme, *Special Functions* (1996), Chapter 3, (3.10)–(3.14), pp. 53–56,
synopsis TEM-03-06. Adjacent pairs are absolutely summable, while the original
alternating series is expressed by natural finite partial sums.
-/

@[expose] public noncomputable section

open Complex Filter Finset
open scoped Topology

namespace DLMF.Gamma

/-- The natural ordered alternating reciprocal series is half a digamma difference.
Temme, Chapter 3, (3.10)–(3.14), pp. 53–56, synopsis TEM-03-06. -/
theorem tendsto_sum_alternating_reciprocal {z : ℂ} (hz : 0 < z.re) :
    Tendsto (fun N : ℕ => ∑ n ∈ range N, (-1 : ℂ) ^ n / ((n : ℂ) + z))
      atTop (𝓝 ((digamma ((z + 1) / 2) - digamma (z / 2)) / 2)) := by
  have hzreg : ∀ n : ℕ, z ≠ -(n : ℂ) := by
    intro n hn
    have := congrArg Complex.re hn
    simp only [neg_re, natCast_re] at this
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have h₁ : (z + 1) / 2 ∈ notNegNat := by
    intro n hn
    exact hzreg (2 * n + 1) (by push_cast; linear_combination 2 * hn)
  have h₂ : z / 2 ∈ notNegNat := by
    intro n hn
    exact hzreg (2 * n) (by push_cast; linear_combination 2 * hn)
  have hpair : Summable (fun k : ℕ =>
      1 / (2 * k + z) - 1 / (2 * k + 1 + z)) := by
    have h := ((summable_cDigammaTerm h₁).sub (summable_cDigammaTerm h₂)).mul_left
      (1 / 2 : ℂ)
    apply h.congr
    intro k
    unfold cDigammaTerm
    rw [show z / 2 + (k : ℂ) = (2 * k + z) / 2 by ring,
      show (z + 1) / 2 + (k : ℂ) = (2 * k + 1 + z) / 2 by ring]
    simp only [one_div_div]
    ring
  have hval : (∑' k : ℕ, (1 / (2 * k + z) - 1 / (2 * k + 1 + z))) =
      (digamma ((z + 1) / 2) - digamma (z / 2)) / 2 := by
    rw [digamma_half_diff z hzreg]
    ring
  have heven : Tendsto
      (fun N : ℕ => ∑ n ∈ range (2 * N), (-1 : ℂ) ^ n / ((n : ℂ) + z))
      atTop (𝓝 ((digamma ((z + 1) / 2) - digamma (z / 2)) / 2)) := by
    have h := hpair.hasSum.tendsto_sum_nat
    rw [hval] at h
    convert h using 1
    ext N
    rw [Finset.sum_range_two_mul]
    apply Finset.sum_congr rfl
    intro k _
    simp only [pow_add, pow_mul, neg_one_sq, one_pow, pow_one]
    push_cast
    ring
  have hi : Tendsto (fun N : ℕ => (N : ℂ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_nhds_zero_nat
  have hterm : Tendsto (fun N : ℕ => (-1 : ℂ) ^ (2 * N) / ((2 * N : ℕ) + z))
      atTop (𝓝 0) := by
    have h := hi.div (tendsto_const_nhds.add (hi.const_mul z)) (by norm_num :
      (2 : ℂ) + z * 0 ≠ 0)
    simp only [zero_div] at h
    apply h.congr'
    filter_upwards [eventually_ne_atTop (0 : ℕ)] with N hN
    have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
    simp only [pow_mul, neg_one_sq, one_pow, Pi.div_apply]
    push_cast
    field_simp
  have hodd : Tendsto
      (fun N : ℕ => ∑ n ∈ range (2 * N + 1), (-1 : ℂ) ^ n / ((n : ℂ) + z))
      atTop (𝓝 ((digamma ((z + 1) / 2) - digamma (z / 2)) / 2)) := by
    simpa [sum_range_succ] using heven.add hterm
  rw [Metric.tendsto_atTop] at heven hodd ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := heven ε hε
  obtain ⟨M, hM⟩ := hodd ε hε
  refine ⟨2 * max N M, fun n hn => ?_⟩
  have hd : max N M ≤ n / 2 := by omega
  by_cases he : n % 2 = 0
  · simpa only [show 2 * (n / 2) = n by omega] using
      hN (n / 2) ((le_max_left N M).trans hd)
  · simpa only [show 2 * (n / 2) + 1 = n by omega] using
      hM (n / 2) ((le_max_right N M).trans hd)

end DLMF.Gamma
