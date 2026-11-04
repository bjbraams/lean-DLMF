/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Airy.Basic.Properties
public import DLMF.Hypergeometric.Basic.Pochhammer
public import DLMFMathlib.Analysis.SpecialFunctions.Gamma.Values

/-!
# Maclaurin series of the Airy functions (DLMF §9.4)

## Main results

* `factorial_three_mul`, `factorial_three_mul_add_one`, `factorial_three_mul_add_two`:
  triplication formulas for factorials.
* `Gamma_four_thirds`, `Gamma_five_thirds`: `Γ(4/3) = Γ(1/3)/3`, `Γ(5/3) = 2Γ(2/3)/3`.
* `hasSum_airyAi_maclaurin`, `hasSum_airyAiDeriv_maclaurin`, `hasSum_airyBi_maclaurin`,
  `hasSum_airyBiDeriv_maclaurin`: DLMF 9.4.1–9.4.4.
-/

@[expose] public noncomputable section

open Complex DLMF.Hypergeometric
open scoped Real Nat

namespace DLMF.Airy

/-- `Γ(4/3) = Γ(1/3)/3`. -/
theorem Gamma_four_thirds : Gamma (4 / 3) = 1 / 3 * Gamma (1 / 3) := by
  rw [show (4 / 3 : ℂ) = 1 / 3 + 1 by norm_num, Complex.Gamma_add_one _ (by norm_num)]

/-- `Γ(5/3) = (2/3)Γ(2/3)`. -/
theorem Gamma_five_thirds : Gamma (5 / 3) = 2 / 3 * Gamma (2 / 3) := by
  rw [show (5 / 3 : ℂ) = 2 / 3 + 1 by norm_num, Complex.Gamma_add_one _ (by norm_num)]

/-- Triplication: `(3k)! = 27^k k! (1/3)_k (2/3)_k`. -/
theorem factorial_three_mul (k : ℕ) :
    (((3 * k) ! : ℕ) : ℂ) = 27 ^ k * k ! * pochhammer (1 / 3) k * pochhammer (2 / 3) k := by
  induction k with
  | zero => simp [pochhammer]
  | succ k ih =>
    rw [show 3 * (k + 1) = 3 * k + 2 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ,
      Nat.factorial_succ]
    push_cast
    rw [ih]
    simp only [pochhammer, ascPochhammer_succ_eval, Nat.factorial_succ]
    push_cast
    ring

/-- `(3k+1)! = 27^k k! (2/3)_k (4/3)_k`. -/
theorem factorial_three_mul_add_one (k : ℕ) :
    (((3 * k + 1) ! : ℕ) : ℂ) = 27 ^ k * k ! * pochhammer (2 / 3) k * pochhammer (4 / 3) k := by
  induction k with
  | zero => simp [pochhammer]
  | succ k ih =>
    rw [show 3 * (k + 1) + 1 = 3 * k + 1 + 2 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ,
      Nat.factorial_succ]
    push_cast
    rw [ih]
    simp only [pochhammer, ascPochhammer_succ_eval, Nat.factorial_succ]
    push_cast
    ring

/-- `(3k+2)! = 2 · 27^k k! (4/3)_k (5/3)_k`. -/
theorem factorial_three_mul_add_two (k : ℕ) :
    (((3 * k + 2) ! : ℕ) : ℂ) = 2 * 27 ^ k * k ! * pochhammer (4 / 3) k * pochhammer (5 / 3) k := by
  induction k with
  | zero => simp [pochhammer]
  | succ k ih =>
    rw [show 3 * (k + 1) + 2 = 3 * k + 2 + 2 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ,
      Nat.factorial_succ]
    push_cast
    rw [ih]
    simp only [pochhammer, ascPochhammer_succ_eval, Nat.factorial_succ]
    push_cast
    ring

/-- Maclaurin series of `airyF`. -/
theorem hasSum_airyF_maclaurin (z : ℂ) :
    HasSum (fun k : ℕ => (Gamma (2 / 3))⁻¹ * (3 : ℂ) ^ k * pochhammer (1 / 3) k / (3 * k)! *
      z ^ (3 * k)) (airyF z) := by
  refine (Complex.hasSum_regularizedHGFun_empty_singleton (2 / 3) (z ^ 3 / 9)).congr_fun fun k => ?_
  rw [factorial_three_mul, Gamma_add_nat_eq_pochhammer_mul_Gamma (by norm_num)]
  have h1 := pochhammer_ne_zero_of_re_pos (z := 1 / 3) (by norm_num) k
  have h2 := pochhammer_ne_zero_of_re_pos (z := 2 / 3) (by norm_num) k
  have h3 : Gamma (2 / 3) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  have hk : (k ! : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  rw [pow_mul, show (27 : ℂ) = 3 * 9 by norm_num, mul_pow, div_pow]
  field_simp

/-- Maclaurin series of `airyG`. -/
theorem hasSum_airyG_maclaurin (z : ℂ) :
    HasSum (fun k : ℕ => (Gamma (4 / 3))⁻¹ * (3 : ℂ) ^ k * pochhammer (2 / 3) k / (3 * k + 1)! *
      z ^ (3 * k + 1)) (airyG z) := by
  refine ((Complex.hasSum_regularizedHGFun_empty_singleton (4 / 3) (z ^ 3 / 9)).mul_left
      z).congr_fun fun k => ?_
  rw [factorial_three_mul_add_one, Gamma_add_nat_eq_pochhammer_mul_Gamma (by norm_num)]
  have h1 := pochhammer_ne_zero_of_re_pos (z := 4 / 3) (by norm_num) k
  have h2 := pochhammer_ne_zero_of_re_pos (z := 2 / 3) (by norm_num) k
  have h3 : Gamma (4 / 3) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  have hk : (k ! : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  rw [pow_succ, pow_mul, show (27 : ℂ) = 3 * 9 by norm_num, mul_pow, div_pow]
  field_simp

/-- Maclaurin series of `airyFDeriv`. -/
theorem hasSum_airyFDeriv_maclaurin (z : ℂ) :
    HasSum (fun k : ℕ => (Gamma (2 / 3))⁻¹ * (3 : ℂ) ^ k * pochhammer (4 / 3) k / (3 * k + 2)! *
      z ^ (3 * k + 2)) (airyFDeriv z) := by
  refine ((Complex.hasSum_regularizedHGFun_empty_singleton (5 / 3) (z ^ 3 / 9)).mul_left (z ^ 2 /
      3)).congr_fun fun k => ?_
  rw [factorial_three_mul_add_two, Gamma_add_nat_eq_pochhammer_mul_Gamma (by norm_num),
    Gamma_five_thirds]
  have h1 := pochhammer_ne_zero_of_re_pos (z := 4 / 3) (by norm_num) k
  have h2 := pochhammer_ne_zero_of_re_pos (z := 5 / 3) (by norm_num) k
  have h3 : Gamma (2 / 3) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  have hk : (k ! : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  rw [pow_add, pow_mul, show (27 : ℂ) = 3 * 9 by norm_num, mul_pow, div_pow]
  field_simp

/-- `G′(z) = 3 ₀F̃₁(;1/3;z³/9)`. -/
theorem airyGDeriv_eq (z : ℂ) :
    airyGDeriv z = 3 * regularizedHGFun (∅ : Multiset ℂ) {1 / 3} (z ^ 3 / 9) := by
  rw [airyGDeriv, reg0F1_contiguous_of_eq (c := 1 / 3) (c₁ := 4 / 3) (c₂ := 7 / 3) (by norm_num)
    (by norm_num)]
  ring

/-- Maclaurin series of `airyGDeriv`. -/
theorem hasSum_airyGDeriv_maclaurin (z : ℂ) :
    HasSum (fun k : ℕ => (Gamma (4 / 3))⁻¹ * (3 : ℂ) ^ k * pochhammer (2 / 3) k / (3 * k)! *
      z ^ (3 * k)) (airyGDeriv z) := by
  rw [airyGDeriv_eq]
  refine ((Complex.hasSum_regularizedHGFun_empty_singleton (1 / 3) (z ^ 3 / 9)).mul_left
      3).congr_fun fun k => ?_
  rw [factorial_three_mul, Gamma_add_nat_eq_pochhammer_mul_Gamma (by norm_num),
    Gamma_four_thirds]
  have h1 := pochhammer_ne_zero_of_re_pos (z := 1 / 3) (by norm_num) k
  have h2 := pochhammer_ne_zero_of_re_pos (z := 2 / 3) (by norm_num) k
  have h3 : Gamma (1 / 3) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  have hk : (k ! : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  rw [pow_mul, show (27 : ℂ) = 3 * 9 by norm_num, mul_pow, div_pow]
  field_simp

/-- `G′(0) = 1/Γ(4/3)`. -/
theorem airyGDeriv_zero' : airyGDeriv 0 = (Gamma (4 / 3))⁻¹ := by
  rw [airyGDeriv_zero, Gamma_four_thirds]
  have h3 : Gamma (1 / 3) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  field_simp

/-- The Maclaurin series `Ai(z) = Ai(0) Σ 3^k (1/3)_k z^{3k}/(3k)! + Ai'(0) Σ 3^k (2/3)_k
z^{3k+1}/(3k+1)!` (DLMF 9.4.1). -/
@[dlmf 9.4.E1]
theorem hasSum_airyAi_maclaurin (z : ℂ) :
    HasSum (fun k : ℕ => airyAi 0 * (3 : ℂ) ^ k * pochhammer (1 / 3) k /
        (3 * k).factorial * z ^ (3 * k) +
      airyAiDeriv 0 * (3 : ℂ) ^ k * pochhammer (2 / 3) k / (3 * k + 1).factorial * z ^ (3 * k + 1))
      (airyAi z) := by
  convert ((hasSum_airyF_maclaurin z).mul_left (((3 : ℝ) ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)).add
    ((hasSum_airyG_maclaurin z).mul_left (-(((3 : ℝ) ^ (-(4 / 3 : ℝ)) : ℝ) : ℂ))) using 1
  · funext k
    simp only [airyAi, airyAiDeriv, airyF_zero, airyG_zero, airyFDeriv_zero, airyGDeriv_zero']
    ring
  · simp only [airyAi]; ring

/-- The Maclaurin series `Ai'(z) = Ai'(0) Σ 3^k (2/3)_k z^{3k}/(3k)! + Ai(0) Σ 3^k (4/3)_k
z^{3k+2}/(3k+2)!` (DLMF 9.4.2). -/
@[dlmf 9.4.E2]
theorem hasSum_airyAiDeriv_maclaurin (z : ℂ) :
    HasSum (fun k : ℕ => airyAiDeriv 0 * (3 : ℂ) ^ k * pochhammer (2 / 3) k / (3 * k).factorial *
        z ^ (3 * k) +
      airyAi 0 * (3 : ℂ) ^ k * pochhammer (4 / 3) k / (3 * k + 2).factorial * z ^ (3 * k + 2))
      (airyAiDeriv z) := by
  convert ((hasSum_airyGDeriv_maclaurin z).mul_left (-(((3 : ℝ) ^ (-(4 / 3 : ℝ)) : ℝ) : ℂ))).add
    ((hasSum_airyFDeriv_maclaurin z).mul_left (((3 : ℝ) ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)) using 1
  · funext k
    simp only [airyAi, airyAiDeriv, airyF_zero, airyG_zero, airyFDeriv_zero, airyGDeriv_zero']
    ring
  · simp only [airyAiDeriv]; ring

/-- The Maclaurin series of `Bi`, the same as 9.4.1 with `Bi(0)`, `Bi'(0)` in place of
`Ai(0)`, `Ai'(0)` (DLMF 9.4.3). -/
@[dlmf 9.4.E3]
theorem hasSum_airyBi_maclaurin (z : ℂ) :
    HasSum (fun k : ℕ => airyBi 0 * (3 : ℂ) ^ k * pochhammer (1 / 3) k /
        (3 * k).factorial * z ^ (3 * k) +
      airyBiDeriv 0 * (3 : ℂ) ^ k * pochhammer (2 / 3) k / (3 * k + 1).factorial * z ^ (3 * k + 1))
      (airyBi z) := by
  convert ((hasSum_airyF_maclaurin z).mul_left
      ((Real.sqrt 3 : ℂ) * (((3 : ℝ) ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ))).add
    ((hasSum_airyG_maclaurin z).mul_left
      ((Real.sqrt 3 : ℂ) * (((3 : ℝ) ^ (-(4 / 3 : ℝ)) : ℝ) : ℂ))) using 1
  · funext k
    simp only [airyBi, airyBiDeriv, airyF_zero, airyG_zero, airyFDeriv_zero, airyGDeriv_zero']
    ring
  · simp only [airyBi]; ring

/-- The Maclaurin series of `Bi'`, the same as 9.4.2 with `Bi(0)`, `Bi'(0)` in place of
`Ai(0)`, `Ai'(0)` (DLMF 9.4.4). -/
@[dlmf 9.4.E4]
theorem hasSum_airyBiDeriv_maclaurin (z : ℂ) :
    HasSum (fun k : ℕ => airyBiDeriv 0 * (3 : ℂ) ^ k * pochhammer (2 / 3) k / (3 * k).factorial *
        z ^ (3 * k) +
      airyBi 0 * (3 : ℂ) ^ k * pochhammer (4 / 3) k / (3 * k + 2).factorial * z ^ (3 * k + 2))
      (airyBiDeriv z) := by
  convert ((hasSum_airyGDeriv_maclaurin z).mul_left
      ((Real.sqrt 3 : ℂ) * (((3 : ℝ) ^ (-(4 / 3 : ℝ)) : ℝ) : ℂ))).add
    ((hasSum_airyFDeriv_maclaurin z).mul_left
      ((Real.sqrt 3 : ℂ) * (((3 : ℝ) ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ))) using 1
  · funext k
    simp only [airyBi, airyBiDeriv, airyF_zero, airyG_zero, airyFDeriv_zero, airyGDeriv_zero']
    ring
  · simp only [airyBiDeriv]; ring

end DLMF.Airy
