/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Zeta.Lerch.LogarithmicExpansion

/-!
# Parameter shifts of Lerch's integer logarithmic expansion

The finite shift in the Lerch parameter extends the integer-order logarithmic expansion
from the right half-plane. Omitting its exceptional Taylor coefficient in each exponential
correction produces the reciprocal sum in the finite digamma shift.
-/

@[expose] public noncomputable section

open Complex Set Filter MeasureTheory
open scoped Real Topology Nat

namespace DLMF.Zeta.LerchLogarithmic

/-- Removing the exceptional Taylor coefficient from an exponential shift correction subtracts
its reciprocal-parameter contribution. -/
theorem hasSum_exponential_correction_omit {m : ℕ} (hm : 1 ≤ m) {a z : ℂ}
    (ha : a ≠ 0) (hz : z ≠ 0) :
    HasSum (fun n : ℕ => if n = m - 1 then 0 else
      1 / a ^ ((m : ℂ) - n) * log z ^ n / n !)
      (z ^ a / a ^ (m : ℂ) - (log z ^ (m - 1) / (m - 1)!) / a) := by
  have hEq : ((m - 1 : ℕ) : ℂ) + 1 = (m : ℂ) := by
    exact_mod_cast Nat.sub_add_cancel hm
  have horder : (m : ℂ) - ((m - 1 : ℕ) : ℂ) = 1 := by linear_combination -hEq
  have H := (hasSum_exponential_correction ha hz (m : ℂ)).update (m - 1) 0
  convert H using 1
  · funext n
    by_cases hn : n = m - 1 <;> simp [hn]
  · simp only [horder, cpow_one, zero_sub]
    ring

/-- A right-half-plane integer logarithmic expansion extends to every admissible Lerch
parameter by finite shifts. The coefficient at the Hurwitz pole is omitted throughout. -/
theorem hasSum_lerchPhi_log_nat_of_right {m : ℕ} (hm : 2 ≤ m) {z a : ℂ}
    (hz : z ∈ slitOne) (hz0 : z ≠ 0) (_hlog : ‖log z‖ < 2 * π)
    (ha : ∀ k : ℕ, a ≠ -(k : ℂ))
    (hRight : ∀ A : ℂ, 0 < A.re →
      HasSum (fun n : ℕ => if n = m - 1 then 0 else
        hurwitzZetaComplex ((m : ℂ) - n) A * log z ^ n / n !)
        (z ^ A * lerchPhi z m A - log z ^ (m - 1) / (m - 1)! *
          (digamma m - digamma A - log (-log z)))) :
    HasSum (fun n : ℕ => if n = m - 1 then 0 else
      hurwitzZetaComplex ((m : ℂ) - n) a * log z ^ n / n !)
      (z ^ a * lerchPhi z m a - log z ^ (m - 1) / (m - 1)! *
        (digamma m - digamma a - log (-log z))) := by
  obtain ⟨M, hM⟩ := exists_nat_gt (-a.re)
  have hAM : 0 < (a + (M : ℂ)).re := by simp only [add_re, natCast_re]; linarith
  have hS := hRight (a + M) hAM
  have hA : ∀ k : ℕ, a + k ≠ 0 := by
    intro k h
    exact ha k (by linear_combination h)
  have hF := hasSum_sum (s := Finset.range M) (fun k _ =>
    hasSum_exponential_correction_omit (m := m) (by omega) (hA k) hz0)
  have hp : LerchParamAdmissible (m : ℂ) a := by
    constructor
    · intro hNonInt
      exact False.elim (hNonInt (m : ℤ) (by simp))
    · intro _
      exact ha
  have hPsi := digamma_apply_add_nat ha M
  let C : ℂ := log z ^ (m - 1) / (m - 1)!
  have hFinite : (∑ k ∈ Finset.range M, (z ^ (a + k) / (a + k) ^ (m : ℂ) - C / (a + k))) =
      z ^ a * (∑ k ∈ Finset.range M, z ^ k / (a + k) ^ (m : ℂ)) -
        C * ∑ k ∈ Finset.range M, (a + k)⁻¹ := by
    rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro k _
      rw [cpow_add _ _ hz0, cpow_natCast]
      ring
  convert hS.add hF using 1
  · funext n
    by_cases hn : n = m - 1
    · simp only [ite_eq_left hn, Finset.sum_const_zero, add_zero]
    · simp only [ite_eq_right hn]
      have hs : (m : ℂ) - (n : ℂ) ≠ 1 := by
        intro he
        have he' : (m : ℂ) = (n : ℂ) + 1 := by linear_combination he
        have he'' : m = n + 1 := by exact_mod_cast he'
        exact hn (by omega)
      rw [hurwitzZetaComplex_eq_add_nat hs ha M, add_mul, add_div]
      congr 1
      simp only [Finset.sum_mul, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k _
      rw [add_comm (k : ℂ) a]
  · change _ = _ + ∑ k ∈ Finset.range M, (z ^ (a + k) / (a + k) ^ (m : ℂ) - C / (a + k))
    rw [hFinite, lerchPhi_eq_add_nat_of_mem_slitOne hp hz M, hPsi]
    simp only [cpow_add _ _ hz0, cpow_natCast, C]
    ring

end DLMF.Zeta.LerchLogarithmic
