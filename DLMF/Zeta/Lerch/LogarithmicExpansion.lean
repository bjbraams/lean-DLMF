/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Zeta.Lerch.LogarithmicContinuation

/-!
# Lerch's logarithmic expansion on the principal cut plane

The right-half-plane expansion extends to all admissible parameters by the finite
parameter-shift recurrence. The corresponding Hurwitz shift and the exponential series
supply the finite correction, preserving the principal powers of each shifted parameter.
This proves DLMF 25.14.3_1.
-/

@[expose] public noncomputable section

open Complex Set Filter MeasureTheory
open scoped Real Topology Nat

namespace DLMF.Zeta.LerchLogarithmic

/-- Each finite parameter-shift correction has its exponential Taylor series. -/
theorem hasSum_exponential_correction {a z : ℂ} (ha : a ≠ 0) (hz : z ≠ 0) (s : ℂ) :
    HasSum (fun n : ℕ => 1 / a ^ (s - n) * log z ^ n / n !)
      (z ^ a / a ^ s) := by
  have h : HasSum (fun n : ℕ => (a * log z) ^ n / n !) (exp (a * log z)) := by
    rw [Complex.exp_eq_exp_ℂ]
    exact NormedSpace.expSeries_div_hasSum_exp _
  convert h.mul_left (1 / a ^ s) using 1
  · funext n
    rw [cpow_sub _ _ ha, cpow_natCast, one_div_div, mul_pow]
    ring
  · rw [cpow_def_of_ne_zero hz, mul_comm (log z) a]
    ring

/-- The regular logarithmic expansion for all admissible Lerch parameters. -/
theorem hasSum_lerchPhi_log {z s a : ℂ} (hs : ∀ n : ℕ, s ≠ (n : ℂ) + 1)
    (ha : LerchParamAdmissible s a) (ha' : ∀ m : ℕ, a ≠ -(m : ℂ)) (hz : z ∈ slitOne)
    (hz0 : z ≠ 0) (hlog : ‖log z‖ < 2 * π) :
    HasSum (fun n : ℕ => hurwitzZetaComplex (s - n) a * log z ^ n / n !)
      (z ^ a * lerchPhi z s a - Gamma (1 - s) * (-log z) ^ (s - 1)) := by
  obtain ⟨m, hm⟩ := exists_nat_gt (-a.re)
  have ham : 0 < (a + (m : ℂ)).re := by simp only [add_re, natCast_re]; linarith
  have hS := hasSum_lerchPhi_log_of_re_pos ham hs hz hz0 hlog
  have hA : ∀ k : ℕ, a + k ≠ 0 := by
    intro k h
    exact ha' k (by linear_combination h)
  have hF := hasSum_sum (s := Finset.range m) (fun k _ =>
    hasSum_exponential_correction (hA k) hz0 s)
  convert hS.add hF using 1
  · funext n
    have hn : s - (n : ℂ) ≠ 1 := by
      intro h
      apply hs n
      linear_combination h
    rw [hurwitzZetaComplex_eq_add_nat hn ha' m, add_mul, add_div]
    congr 1
    simp only [Finset.sum_mul, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k _
    rw [add_comm (k : ℂ) a]
  · rw [lerchPhi_eq_add_nat_of_mem_slitOne ha hz m, mul_add, Finset.mul_sum]
    simp_rw [cpow_add _ _ hz0, cpow_natCast]
    rw [Finset.sum_congr rfl (fun k _ => by ring :
      ∀ k ∈ Finset.range m, z ^ a * (z ^ k / (a + k) ^ s) =
        z ^ a * z ^ k / (a + k) ^ s)]
    ring

end DLMF.Zeta.LerchLogarithmic
