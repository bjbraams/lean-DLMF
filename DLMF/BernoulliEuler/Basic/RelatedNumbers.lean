/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.BernoulliEuler.Basic.Polynomials
public import DLMFMathlib.NumberTheory.BernoulliTaylor

/-!
# Genocchi and tangent numbers

The Genocchi numbers and the tangent numbers of DLMF §24.15(i)–(ii), with their generating
functions and the entries of Table 24.15.1.

## Main definitions

* `genocchiNumber`: the Genocchi numbers `Gₙ = 2(1 - 2ⁿ) Bₙ` (DLMF 24.15.2).
* `tangentNumber`: the tangent numbers `Tₙ`, by the closed forms DLMF 24.15.4, 24.15.5.

## Main results

* `hasSum_genocchiNumber`: `2t/(eᵗ + 1) = ∑ Gₙ tⁿ/n!` for `‖t‖ < π` (DLMF 24.15.1).
* `hasSum_tangentNumber`, `tangentNumber_odd`, `tangentNumber_even`: `tan t = ∑ Tₙ tⁿ/n!` for
  `‖t‖ < π/2` and the closed forms (DLMF 24.15.3–24.15.5).
* `genocchiNumber_table`, `tangentNumber_table`: Table 24.15.1 (exact integers).

## Implementation notes

DLMF defines `Gₙ` and `Tₙ` by the generating functions 24.15.1 and 24.15.3; here the closed
forms are the definitions and the generating functions are theorems, proved from the series of
`t/(eᵗ - 1)` and `π z tan(π z)` in `DLMFMathlib.NumberTheory.BernoulliTaylor`. The relations with
Stirling, Fibonacci and Lucas numbers (§24.15(iii)–(iv)) are in
`DLMF.BernoulliEuler.RelatedNumbers`.
-/

@[expose] public noncomputable section

open Finset Filter
open scoped Nat Real

namespace DLMF.BernoulliEuler

/-! ### §24.15(i) Genocchi numbers -/

/-- DLMF 24.15.2: the Genocchi numbers `Gₙ = 2(1 - 2ⁿ) Bₙ`. (DLMF defines `Gₙ` by the
generating function 24.15.1, proved as `hasSum_genocchiNumber`.) -/
@[dlmf 24.15.E2]
def genocchiNumber (n : ℕ) : ℚ := 2 * (1 - 2 ^ n) * bernoulli n

/-- DLMF 24.15.2: `Gₙ = 2(1 - 2ⁿ) Bₙ`. -/
@[dlmf 24.15.E2]
theorem genocchiNumber_eq (n : ℕ) : genocchiNumber n = 2 * (1 - 2 ^ n) * bernoulli n := rfl

/-- Nonvanishing under the stated hypotheses: `Complex.exp w ≠ 1`. -/
private lemma bernBasic_exp_ne_one_of_norm_lt {w : ℂ} (hw : ‖w‖ < 2 * π) (hw0 : w ≠ 0) :
    Complex.exp w ≠ 1 := by
  intro h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn; exact hw0 hn
  have : ‖w‖ = |(n : ℝ)| * (2 * π) := by
    rw [hn, norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_intCast, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]; ring
  have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hn0
  nlinarith [Real.pi_pos]

/-- DLMF 24.15.1: `2t/(eᵗ + 1) = ∑ₙ Gₙ tⁿ/n!` for complex `‖t‖ < π` (DLMF's sum starts at
`n = 1`; `G₀ = 0`). -/
@[dlmf 24.15.E1]
theorem hasSum_genocchiNumber {t : ℂ} (ht : ‖t‖ < π) :
    HasSum (fun n : ℕ => (genocchiNumber n : ℂ) * t ^ n / n !) (2 * t / (Complex.exp t + 1)) := by
  rcases eq_or_ne t 0 with rfl | ht0
  · convert hasSum_single (f := fun n : ℕ => (genocchiNumber n : ℂ) * 0 ^ n / n !) 0 ?_ using 1
    · simp [genocchiNumber]
    · intro b hb; simp [hb]
  have h2t : ‖2 * t‖ < 2 * π := by rw [norm_mul, Complex.norm_ofNat]; linarith
  have h2t0 : 2 * t ≠ 0 := mul_ne_zero two_ne_zero ht0
  have hpi := Real.pi_pos
  have h1 := Complex.hasSum_bernoulli_mul_pow_div (z := t) (by linarith) ht0
  have h2 := Complex.hasSum_bernoulli_mul_pow_div h2t h2t0
  have he1 : Complex.exp t - 1 ≠ 0 :=
    sub_ne_zero.mpr (bernBasic_exp_ne_one_of_norm_lt (by linarith) ht0)
  have he2 : Complex.exp (2 * t) - 1 ≠ 0 :=
    sub_ne_zero.mpr (bernBasic_exp_ne_one_of_norm_lt h2t h2t0)
  have he3 : Complex.exp t + 1 ≠ 0 := by
    intro h; apply he2
    rw [show 2 * t = t + t by ring, Complex.exp_add,
      show Complex.exp t = -1 by linear_combination h]; ring
  convert (h1.mul_left 2).sub (h2.mul_left 2) using 1
  · funext n; simp only [genocchiNumber]; push_cast; ring
  · rw [show 2 * t = t + t by ring, Complex.exp_add,
      show Complex.exp t * Complex.exp t - 1 = (Complex.exp t - 1) * (Complex.exp t + 1) by ring]
    field_simp
    ring

/-! ### §24.15(ii) Tangent numbers -/

/-- DLMF 24.15.4, 24.15.5: the tangent numbers, `T₂ₙ₋₁ = (-1)ⁿ⁻¹ 2²ⁿ(2²ⁿ - 1)/(2n) · B₂ₙ`
(`n ≥ 1`) and `T₂ₙ = 0`. (DLMF defines `Tₙ` by the generating function 24.15.3, proved as
`hasSum_tangentNumber`.) -/
@[dlmf 24.15.E4]
def tangentNumber (n : ℕ) : ℚ :=
  if Even n then 0
  else (-1) ^ ((n + 1) / 2 - 1) * (2 ^ (n + 1) * (2 ^ (n + 1) - 1) / (n + 1)) * bernoulli (n + 1)

/-- DLMF 24.15.4: `T₂ₙ₋₁ = (-1)ⁿ⁻¹ 2²ⁿ(2²ⁿ - 1)/(2n) · B₂ₙ` for `n ≥ 1`. -/
@[dlmf 24.15.E4]
theorem tangentNumber_odd {n : ℕ} (hn : 1 ≤ n) :
    tangentNumber (2 * n - 1) =
      (-1) ^ (n - 1) * (2 ^ (2 * n) * (2 ^ (2 * n) - 1) / (2 * n)) * bernoulli (2 * n) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have h1 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
  have h2 : (2 * k + 1 + 1) / 2 - 1 = k := by omega
  have hne : ¬ Even (2 * k + 1) := Nat.not_even_iff_odd.mpr (odd_two_mul_add_one k)
  rw [h1, tangentNumber]
  simp only [hne, ↓reduceIte]
  rw [h2, show 2 * k + 1 + 1 = 2 * (k + 1) by ring, Nat.add_sub_cancel]
  push_cast; ring

/-- DLMF 24.15.5: `T₂ₙ = 0`. -/
@[dlmf 24.15.E5]
theorem tangentNumber_even (n : ℕ) : tangentNumber (2 * n) = 0 := by
  simp [tangentNumber]

/-- DLMF 24.15.3: `tan t = ∑ₙ Tₙ tⁿ/n!` for complex `‖t‖ < π/2`. -/
@[dlmf 24.15.E3]
theorem hasSum_tangentNumber {t : ℂ} (ht : ‖t‖ < π / 2) :
    HasSum (fun n : ℕ => (tangentNumber n : ℂ) * t ^ n / n !) (Complex.tan t) := by
  rcases eq_or_ne t 0 with rfl | ht0
  · convert hasSum_single (f := fun n : ℕ => (tangentNumber n : ℂ) * 0 ^ n / n !) 0 ?_ using 1
    · simp [tangentNumber]
    · intro b hb; simp [hb]
  have hpi := Real.pi_pos
  have hpi' : (π : ℂ) ≠ 0 := by exact_mod_cast hpi.ne'
  set w : ℂ := t / π with hw
  have hwt : (π : ℂ) * w = t := by rw [hw]; field_simp
  have hwn : ‖w‖ < 1 / 2 := by
    rw [hw, norm_div, Complex.norm_real, Real.norm_of_nonneg hpi.le, div_lt_iff₀ hpi]
    linarith
  have hw0 : w ≠ 0 := div_ne_zero ht0 hpi'
  have h := Complex.hasSum_pi_mul_tan_bernoulli hwn hw0
  rw [mul_assoc, hwt] at h
  have h' := (hasSum_nat_add_iff' 1).mpr (h.div_const t)
  simp only [Finset.sum_range_one, pow_zero, mul_zero, sub_self, mul_one, zero_div,
    sub_zero] at h'
  rw [mul_div_cancel_left₀ _ ht0] at h'
  have he : HasSum (fun k : ℕ => (tangentNumber (2 * k) : ℂ) * t ^ (2 * k) / (2 * k)!) 0 := by
    simp only [tangentNumber_even, Rat.cast_zero, zero_mul, zero_div]; exact hasSum_zero
  rw [← zero_add (Complex.tan t)]
  refine HasSum.even_add_odd (f := fun n : ℕ => (tangentNumber n : ℂ) * t ^ n / n !) he
    (h'.congr_fun fun k => ?_)
  · have hT := tangentNumber_odd (n := k + 1) (by omega)
    rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega, Nat.add_sub_cancel] at hT
    rw [hT, show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Nat.factorial_succ (2 * k + 1)]
    have hf : ((2 * k + 1)! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hk : (2 * (k : ℂ) + 1) + 1 ≠ 0 := by norm_cast
    have hk2 : (k : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero k
    push_cast
    rw [show (4 : ℂ) ^ (k + 1) = 2 ^ (2 * k + 1 + 1) by
      rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring, pow_mul]; norm_num]
    field_simp
    ring

/-! ### Table 24.15.1 -/

/-- Identity under the stated parameter and domain assumptions: `bernoulli 0 = 1 ∧ bernoulli 1 =
-1 / 2 ∧ bernoulli 2 = 1 / 6 ∧ bernoulli 3 = 0 ∧ bernoulli 4 = -1 / 30 ∧ bernoulli 5 = 0 ∧
bernoulli 6 = 1 / 42 ∧ bernoulli 7 = 0 ∧ bernoulli 8 = -1 / 30 ∧ bernoulli 9 = 0`. -/
private lemma bernBasic_bernoulli_values_zero_to_nine :
    bernoulli 0 = 1 ∧ bernoulli 1 = -1 / 2 ∧ bernoulli 2 = 1 / 6 ∧ bernoulli 3 = 0 ∧
      bernoulli 4 = -1 / 30 ∧ bernoulli 5 = 0 ∧ bernoulli 6 = 1 / 42 ∧ bernoulli 7 = 0 ∧
      bernoulli 8 = -1 / 30 ∧ bernoulli 9 = 0 := by
  have h3 : bernoulli' 3 = 0 := bernoulli'_three
  have h5 : bernoulli' 5 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by norm_num)
  have h7 : bernoulli' 7 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by norm_num)
  have h9 : bernoulli' 9 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by norm_num)
  have h6 : bernoulli' 6 = 1 / 42 := by
    rw [bernoulli'_def]
    norm_num [sum_range_succ, bernoulli'_zero, bernoulli'_one, bernoulli'_two, h3,
      bernoulli'_four, h5, Nat.choose]
  have h8 : bernoulli' 8 = -1 / 30 := by
    rw [bernoulli'_def]
    norm_num [sum_range_succ, bernoulli'_zero, bernoulli'_one, bernoulli'_two, h3,
      bernoulli'_four, h5, h6, h7, Nat.choose]
  refine ⟨bernoulli_zero, bernoulli_one, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num)]
  · rw [bernoulli'_two]
  · exact h3
  · exact bernoulli'_four
  · exact h5
  · exact h6
  · exact h7
  · exact h8
  · exact h9

/-- DLMF Table 24.15.1: `G₀, …, G₈ = 0, 1, -1, 0, 1, 0, -3, 0, 17`. -/
@[dlmf 24.15.T1]
theorem genocchiNumber_table :
    genocchiNumber 0 = 0 ∧ genocchiNumber 1 = 1 ∧ genocchiNumber 2 = -1 ∧
      genocchiNumber 3 = 0 ∧ genocchiNumber 4 = 1 ∧ genocchiNumber 5 = 0 ∧
      genocchiNumber 6 = -3 ∧ genocchiNumber 7 = 0 ∧ genocchiNumber 8 = 17 := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, -⟩ := bernBasic_bernoulli_values_zero_to_nine
  simp only [genocchiNumber, b0, b1, b2, b3, b4, b5, b6, b7, b8]
  norm_num

/-- DLMF Table 24.15.1: `T₀, …, T₈ = 0, 1, 0, 2, 0, 16, 0, 272, 0`. -/
@[dlmf 24.15.T1]
theorem tangentNumber_table :
    tangentNumber 0 = 0 ∧ tangentNumber 1 = 1 ∧ tangentNumber 2 = 0 ∧
      tangentNumber 3 = 2 ∧ tangentNumber 4 = 0 ∧ tangentNumber 5 = 16 ∧
      tangentNumber 6 = 0 ∧ tangentNumber 7 = 272 ∧ tangentNumber 8 = 0 := by
  obtain ⟨-, -, b2, -, b4, -, b6, -, b8, -⟩ := bernBasic_bernoulli_values_zero_to_nine
  simp only [tangentNumber]
  norm_num [b2, b4, b6, b8, Nat.even_iff]

end DLMF.BernoulliEuler
