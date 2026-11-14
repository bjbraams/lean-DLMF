/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.BernoulliEuler.Properties
public import DLMFMathlib.Algebra.Polynomial.CentralFactorial
import DLMFMathlib.Algebra.BigOperators

/-!
# Bernoulli numbers from central factorials

DLMF 24.6.3 follows by applying Bernoulli umbral substitution to the central-factorial
expansion of an even monomial. The defining Bernoulli difference equation evaluates each
basis element through the derivative of its discrete antiderivative at zero.
The expansion and antiderivative use Mathlib's polynomial and forward-difference APIs.
-/

public noncomputable section

open Finset
open Polynomial hiding bernoulli
open scoped Nat

namespace DLMF.BernoulliEuler

/-- Bernoulli umbral substitution of an even central factorial. -/
lemma umbralBernoulli_evenCentralFactorial_succ (k : ℕ) :
    umbralBernoulli 0 (evenCentralFactorial ℂ (k + 1)) =
      (-1 : ℂ) ^ (k + 2) * (k ! : ℂ) * ((k + 1)! : ℂ) / (2 * (2 * k + 3)) := by
  obtain ⟨Q, hQ, hQd⟩ := exists_evenCentralFactorial_discreteAntiderivative (K := ℂ) k
  have he : evenCentralFactorial ℂ (k + 1) = Q.comp (X + 1) - Q := by
    apply Polynomial.funext
    intro x
    simpa only [eval_sub, eval_comp, eval_add, eval_X, eval_one] using (hQ x).symm
  rw [he, umbralBernoulli_sub, umbralBernoulli_comp_add_one_sub, hQd]

/-- **DLMF 24.6.3**: `B₂ₙ = ∑_{k=1}^{n} ((k-1)! k!/(2k+1)!) ∑_{j=1}^{k} (-1)^{j-1} (2k choose k+j)
j^{2n}`, `n ≥ 1`. -/
@[dlmf 24.6.E3]
theorem bernoulli_two_mul_eq_explicit₃ {n : ℕ} (hn : 1 ≤ n) :
    bernoulli (2 * n) = ∑ k ∈ Icc 1 n, ((k - 1)! * k ! / (2 * k + 1)! : ℚ) *
      ∑ j ∈ Icc 1 k, (-1 : ℚ) ^ (j - 1) * ((2 * k).choose (k + j) : ℚ) * (j : ℚ) ^ (2 * n) := by
  apply Rat.cast_injective (α := ℂ)
  push_cast
  have hexp := congrArg (umbralBernoulli 0)
    (X_pow_two_mul_eq_sum_evenCentralFactorial (K := ℂ) n)
  have hleft : umbralBernoulli 0 ((X : ℂ[X]) ^ (2 * n)) = (bernoulli (2 * n) : ℂ) := by
    have h := umbralBernoulli_X_add_C_pow (2 * n) 0 0
    simpa only [map_zero, add_zero, bernoulliPolyB_zero_arg] using h.symm
  rw [hleft, umbralBernoulli_sum, sum_range_succ'] at hexp
  have hn0 : 2 * n ≠ 0 := by omega
  have hz : umbralBernoulli 0 (C (((fwdDiff 1)^[2 * 0]
      (fun x : ℂ => x ^ (2 * n)) (-((0 : ℕ) : ℂ))) / ((2 * 0)! : ℂ)) *
        evenCentralFactorial ℂ 0) = 0 := by
    simp [hn0, umbralBernoulli, umbralFunctional]
  rw [hz, add_zero] at hexp
  rw [hexp, sum_Icc_one_eq_sum_range_add_one]
  apply sum_congr rfl
  intro k _
  rw [umbralBernoulli_C_mul, umbralBernoulli_evenCentralFactorial_succ]
  rw [fwdDiff_iter_eq_sum_shift]
  have he : (∑ i ∈ range (2 * (k + 1) + 1),
      ((-1 : ℤ) ^ (2 * (k + 1) - i) * ((2 * (k + 1)).choose i : ℤ)) •
        ((-((k + 1 : ℕ) : ℂ) + i • (1 : ℂ)) ^ (2 * n))) =
      ∑ i ∈ range (2 * (k + 1) + 1), (-1 : ℂ) ^ (2 * (k + 1) - i) *
        ((2 * (k + 1)).choose i : ℂ) * ((i : ℂ) - ((k + 1 : ℕ) : ℂ)) ^ (2 * n) := by
    apply sum_congr rfl
    intro i _
    rw [zsmul_eq_mul, nsmul_eq_mul, mul_one]
    push_cast
    ring
  rw [he, Finset.sum_neg_one_pow_mul_choose_mul_sub_pow_even n (k + 1) hn]
  have hfact : ((2 * (k + 1) + 1)! : ℂ) = ((2 * (k + 1) : ℕ) + 1) * ((2 * (k + 1))! : ℂ) := by
    rw [Nat.factorial_succ]
    push_cast
    rfl
  rw [hfact, Nat.add_sub_cancel]
  have hsum : ∑ j ∈ Icc 1 (k + 1), (-1 : ℂ) ^ (j - 1) *
      ((2 * (k + 1)).choose (k + 1 + j) : ℂ) * (j : ℂ) ^ (2 * n) =
      -∑ j ∈ Icc 1 (k + 1), (-1 : ℂ) ^ j *
        ((2 * (k + 1)).choose (k + 1 - j) : ℂ) * (j : ℂ) ^ (2 * n) := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro j hj
    have hj1 : 1 ≤ j := (mem_Icc.mp hj).1
    have hjk : j ≤ k + 1 := (mem_Icc.mp hj).2
    rw [show (2 * (k + 1)).choose (k + 1 + j) = (2 * (k + 1)).choose (k + 1 - j) by
      rw [← Nat.choose_symm (by omega : k + 1 - j ≤ 2 * (k + 1))]
      congr 1
      omega]
    have hpow : (-1 : ℂ)^j = -(-1)^(j - 1) := by
      calc (-1 : ℂ)^j = (-1)^((j - 1) + 1) := by congr 1; omega
        _ = -(-1)^(j - 1) := by rw [pow_succ]; ring

    rw [hpow]
    ring
  rw [hsum]
  have hs : (-1 : ℂ) ^ (k + 1) * (-1 : ℂ) ^ (k + 2) = -1 := by
    rw [← pow_add, show k + 1 + (k + 2) = 2 * (k + 1) + 1 by omega, pow_add, pow_mul]
    norm_num
  have hf : (((2 * (k + 1))! : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hk : (2 * (k : ℂ) + 3) ≠ 0 := by exact_mod_cast (by omega : 2 * k + 3 ≠ 0)
  have hk' : (2 * ((k : ℂ) + 1) + 1) ≠ 0 := by
    convert hk using 1
    ring
  have hs' : (-1 : ℂ) ^ (k + 1) * (-1 : ℂ) ^ (k + 1 + 1) = -1 := by exact hs
  push_cast
  field_simp [hf, hk, hk']
  linear_combination ((2 * (k : ℂ) + 3) * (k ! : ℂ) * ((k + 1)! : ℂ) *
    (∑ j ∈ Icc 1 (k + 1), (-1 : ℂ)^j * ((2 * (k + 1)).choose (k + 1 - j) : ℂ) *
      (j : ℂ)^(2 * n))) * hs'

end DLMF.BernoulliEuler
