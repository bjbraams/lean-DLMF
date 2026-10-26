/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.BernoulliEuler.GeneratingFunctions
public import DLMF.Combinatorics.Stirling
public import DLMFMathlib.NumberTheory.BernoulliTaylor
public import DLMFMathlib.NumberTheory.EulerNumbers
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.NumberTheory.Padics.PadicNorm
public import Mathlib.Tactic.CrossRefAttribute
public import Pochhammer.PochhammerTransform

/-!
# Sequences of numbers related to Bernoulli and Euler numbers (DLMF §24.15)

* §24.15(i): the Genocchi numbers `Gₙ = 2(1 - 2ⁿ) Bₙ` (`genocchiNumber`; DLMF defines them by
  the generating function 24.15.1, which is proved here for `‖t‖ < π`, the closed form 24.15.2
  being the definition).
* §24.15(ii): the tangent numbers `Tₙ` (`tangentNumber`), defined by the closed forms 24.15.4,
  24.15.5; the generating function `tan t = ∑ Tₙ tⁿ/n!` (24.15.3) is proved for `‖t‖ < π/2`.
* Table 24.15.1 (`G₀ … G₈`, `T₀ … T₈`, exact integers) is proved.
* §24.15(iii): Stirling numbers. DLMF's `S(n, m)` (§26.8) is Mathlib's `Nat.stirlingSecond`;
  DLMF's signed `s(n, m) = (-1)^{n-m} |s(n, m)|` is written with Mathlib's unsigned
  `Nat.stirlingFirst`. The congruences 24.15.9, 24.15.10 between rationals are stated with the
  `p`-adic norm: `a ≡ b (mod pᵏ)` means `padicNorm p (a - b) ≤ p^{-k}`, i.e. `a - b ∈ pᵏ ℤ_(p)`.
* §24.15(iv): Fibonacci numbers `uₙ` are Mathlib's `Nat.fib`; the Lucas numbers `vₙ` are
  `lucasNumber`. In 24.15.11 the term `(n/6) v_{n-1}` has the factor `n`, so the value of
  `v_{n-1}` at `n = 0` is immaterial (natural subtraction); `1/2^{n-1}` in 24.15.12 is `2/2ⁿ`.

24.15.6 and 24.15.8 are proved with the umbral functional `Xⁿ ↦ Bₙ` applied to the expansion of
`Xⁿ` in falling factorials (Stirling numbers of the second kind, `DLMF.Combinatorics.Stirling`)
and to the coefficients of the rising factorial (`coeff_ascPochhammer` from lean-codes'
`Pochhammer.PochhammerTransform`). 24.15.11 and 24.15.12 are proved from the Binet formulas and
the shift relations of the polynomials. 24.15.7 is proved with formal power series: by
`[tᵐ] (eᵗ - 1)ᵏ = k! S(m, k)/m!` its right side is `n! [tⁿ] ∑ₖ (n+1 choose k+1) (-E)ᵏ` with
`E = (eᵗ - 1)/t`, and `E ∑ₖ (n+1 choose k+1)(-E)ᵏ = 1 - (1 - E)ⁿ⁺¹ = 1 + O(tⁿ⁺¹)`. 24.15.9 and
24.15.10 remain admitted.

## References

* NIST DLMF §24.15; Horata (1991).
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

theorem b24b_exp_ne_one {w : ℂ} (hw : ‖w‖ < 2 * π) (hw0 : w ≠ 0) : Complex.exp w ≠ 1 := by
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
  have he1 : Complex.exp t - 1 ≠ 0 := sub_ne_zero.mpr (b24b_exp_ne_one (by linarith) ht0)
  have he2 : Complex.exp (2 * t) - 1 ≠ 0 := sub_ne_zero.mpr (b24b_exp_ne_one h2t h2t0)
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

theorem b24b_bernoulli_values :
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
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, -⟩ := b24b_bernoulli_values
  simp only [genocchiNumber, b0, b1, b2, b3, b4, b5, b6, b7, b8]
  norm_num

/-- DLMF Table 24.15.1: `T₀, …, T₈ = 0, 1, 0, 2, 0, 16, 0, 272, 0`. -/
@[dlmf 24.15.T1]
theorem tangentNumber_table :
    tangentNumber 0 = 0 ∧ tangentNumber 1 = 1 ∧ tangentNumber 2 = 0 ∧
      tangentNumber 3 = 2 ∧ tangentNumber 4 = 0 ∧ tangentNumber 5 = 16 ∧
      tangentNumber 6 = 0 ∧ tangentNumber 7 = 272 ∧ tangentNumber 8 = 0 := by
  obtain ⟨-, -, b2, -, b4, -, b6, -, b8, -⟩ := b24b_bernoulli_values
  simp only [tangentNumber]
  norm_num [b2, b4, b6, b8, Nat.even_iff]

/-! ### The umbral functional `Xⁿ ↦ Bₙ` (helpers for §24.15(iii)) -/

section Umbral

open Polynomial

/-- The umbral functional `L(Xⁿ) = Bₙ` on `ℚ[X]`. -/
def q24b_L : ℚ[X] →ₗ[ℚ] ℚ := Polynomial.lsum fun i => (_root_.bernoulli i) • LinearMap.id

/-- `L` on monomials. -/
theorem q24b_L_monomial (n : ℕ) (a : ℚ) : q24b_L (monomial n a) = a * _root_.bernoulli n := by
  simp [q24b_L]; ring

/-- `L(p(X+1)) - L(p) = p'(0)`. -/
theorem q24b_L_shift (p : ℚ[X]) :
    q24b_L (p.comp (X + 1)) - q24b_L p = (derivative p).eval 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [add_comp, map_add, map_add, derivative_add, eval_add, ← hp, ← hq]; ring
  | monomial n a =>
    have h1 : (monomial n a).comp (X + 1) =
        ∑ k ∈ range (n + 1), monomial k (a * n.choose k) := by
      rw [← C_mul_X_pow_eq_monomial, mul_comp, C_comp, pow_comp, X_comp, add_pow, mul_sum]
      refine sum_congr rfl fun k _ => ?_
      rw [one_pow, mul_one, ← C_mul_X_pow_eq_monomial, map_mul, ← C_eq_natCast]; ring
    rw [h1, map_sum, sum_range_succ]
    simp only [q24b_L_monomial, Nat.choose_self, Nat.cast_one, mul_one, add_sub_cancel_right]
    have h2 := _root_.sum_bernoulli n
    rw [show ∑ k ∈ range n, a * (n.choose k : ℚ) * _root_.bernoulli k =
      a * ∑ k ∈ range n, (n.choose k : ℚ) * _root_.bernoulli k by rw [mul_sum]; ring_nf, h2]
    rw [derivative_monomial, eval_monomial]
    rcases n with _ | _ | n <;> simp

/-- `(-1)(-2)⋯(-k) = (-1)ᵏ k!`. -/
theorem q24b_descPochhammer_eval_neg_one (k : ℕ) :
    (descPochhammer ℚ k).eval (-1) = (-1) ^ k * k ! := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [descPochhammer_succ_right, eval_mul, ih, eval_sub, eval_X, eval_natCast, Nat.factorial_succ]
    push_cast; ring

/-- `L(x(x-1)⋯(x-k+1)) = (-1)ᵏ k!/(k+1)`. -/
theorem q24b_L_descPochhammer (k : ℕ) :
    q24b_L (descPochhammer ℚ k) = (-1) ^ k * k ! / (k + 1) := by
  have h := descPochhammer_succ_comp_X_sub_one (R := ℚ) k
  have hcomp : ((X : ℚ[X]) - 1).comp (X + 1) = X := by simp
  have h' := congrArg (fun p => p.comp (X + 1)) h
  simp only [smul_eq_mul, sub_comp, mul_comp, comp_assoc, hcomp, comp_X, add_comp,
    natCast_comp, one_comp] at h'
  have hs := q24b_L_shift (descPochhammer ℚ (k + 1))
  have hD : (descPochhammer ℚ (k + 1)).comp (X + 1) - descPochhammer ℚ (k + 1) =
      C ((k : ℚ) + 1) * descPochhammer ℚ k := by
    rw [C_add, C_1, map_natCast]; linear_combination -h'
  rw [← map_sub, hD, ← smul_eq_C_mul, map_smul, smul_eq_mul, descPochhammer_succ_left,
    derivative_mul, derivative_X, eval_add, eval_mul, eval_mul, eval_X, zero_mul, add_zero,
    eval_one, one_mul, eval_comp, eval_sub, eval_X, eval_one, zero_sub,
    q24b_descPochhammer_eval_neg_one] at hs
  have hk : (k : ℚ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero k
  rw [eq_div_iff hk, mul_comm, hs]

/-- DLMF 24.15.6 (helper form). -/
theorem q24b_bernoulli_eq_sum_stirlingSecond (n : ℕ) :
    _root_.bernoulli n = ∑ k ∈ range (n + 1),
      (-1) ^ k * (k ! * Nat.stirlingSecond n k : ℚ) / (k + 1) := by
  have h := congrArg q24b_L (DLMF.Combinatorics.X_pow_eq_sum_stirlingSecond_mul_descPochhammer ℚ n)
  rw [← monomial_one_right_eq_X_pow, q24b_L_monomial, one_mul, map_sum] at h
  rw [h]
  refine sum_congr rfl fun k _ => ?_
  rw [← smul_eq_C_mul, map_smul, q24b_L_descPochhammer, smul_eq_mul]
  ring

/-- DLMF 24.15.8 (helper form). -/
theorem q24b_sum_stirlingFirst_mul_bernoulli (n : ℕ) :
    ∑ k ∈ range (n + 1), (-1) ^ (n + k) *
        ((-1) ^ (n - k) * (Nat.stirlingFirst (n + 1) (k + 1) : ℚ)) * _root_.bernoulli k =
      n ! / (n + 1) := by
  set r := (ascPochhammer ℚ n).comp (X + 1)
  have hA : ascPochhammer ℚ (n + 1) = X * r := ascPochhammer_succ_left ℚ n
  have hcoeff : ∀ k, r.coeff k = Nat.stirlingFirst (n + 1) (k + 1) := by
    intro k
    rw [← coeff_X_mul, ← hA, coeff_ascPochhammer]
  have hdeg : r.natDegree < n + 1 := by
    rw [Nat.lt_succ_iff, natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [hcoeff, Nat.stirlingFirst_eq_zero_of_lt (by omega), Nat.cast_zero]
  have h1 : q24b_L r =
      ∑ k ∈ range (n + 1), (Nat.stirlingFirst (n + 1) (k + 1) : ℚ) * _root_.bernoulli k := by
    conv_lhs => rw [as_sum_range' r (n + 1) hdeg]
    rw [map_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [q24b_L_monomial, hcoeff]
  have h2 : q24b_L r = n ! / (n + 1) := by
    have hs := q24b_L_shift (ascPochhammer ℚ (n + 1))
    rw [ascPochhammer_succ_comp_X_add_one, map_add, add_sub_cancel_left, map_nsmul, nsmul_eq_mul,
      hA, derivative_mul, derivative_X, eval_add, eval_mul, eval_mul, eval_X, zero_mul, add_zero,
      eval_one, one_mul] at hs
    have hr0 : r.eval 0 = n ! := by
      simp only [r, eval_comp, eval_add, eval_X, eval_one, zero_add, ascPochhammer_eval_one]
    rw [hr0] at hs
    have hn : (n : ℚ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero n
    rw [eq_div_iff hn, mul_comm, ← hs]; push_cast; ring
  rw [← h2, h1]
  refine sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  rw [← mul_assoc, ← pow_add, show n + k + (n - k) = 2 * n by omega, pow_mul]
  norm_num

end Umbral

/-! ### §24.15(iii) Stirling numbers -/

/-- DLMF 24.15.6: `Bₙ = ∑ₖ (-1)ᵏ k! S(n, k)/(k+1)`. -/
@[dlmf 24.15.E6]
theorem bernoulli_eq_sum_stirlingSecond (n : ℕ) :
    bernoulli n = ∑ k ∈ range (n + 1),
      (-1) ^ k * (k ! * Nat.stirlingSecond n k : ℚ) / (k + 1) :=
  q24b_bernoulli_eq_sum_stirlingSecond n

/-- `[tᵐ] (eᵗ - 1)ᵏ = k! S(m, k)/m!`. -/
theorem r24b_coeff_exp_sub_one_pow (m k : ℕ) :
    PowerSeries.coeff m ((PowerSeries.exp ℚ - 1) ^ k) =
      (k ! * Nat.stirlingSecond m k : ℚ) / m ! := by
  induction m generalizing k with
  | zero =>
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, map_sub,
      PowerSeries.constantCoeff_exp, map_one, sub_self]
    rcases k with _ | k <;> simp
  | succ m ih =>
    rcases k with _ | k
    · simp [pow_zero, PowerSeries.coeff_one]
    have hd : PowerSeries.derivative ((PowerSeries.exp ℚ - 1) ^ (k + 1)) =
        ((k + 1 : ℕ) : PowerSeries ℚ) * ((PowerSeries.exp ℚ - 1) ^ (k + 1) +
          (PowerSeries.exp ℚ - 1) ^ k) := by
      rw [PowerSeries.derivative_pow, map_sub, PowerSeries.derivative_exp,
        PowerSeries.derivative_one, sub_zero, Nat.add_sub_cancel]
      ring
    have hc := congrArg (PowerSeries.coeff m) hd
    rw [PowerSeries.coeff_derivative, ← map_natCast (PowerSeries.C (R := ℚ)),
      PowerSeries.coeff_C_mul, map_add, ih, ih] at hc
    have h1 : ((m + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    have h2 : (m ! : ℚ) ≠ 0 := by positivity
    rw [Nat.stirlingSecond_succ_succ, Nat.factorial_succ m, Nat.factorial_succ k]
    rw [← eq_div_iff (by positivity)] at hc
    rw [hc]
    simp only [Nat.factorial_succ]
    push_cast
    field_simp

/-- DLMF 24.15.7: `Bₙ = ∑ₖ (-1)ᵏ (n+1 choose k+1) S(n+k, k)/(n+k choose k)`. -/
@[dlmf 24.15.E7]
theorem bernoulli_eq_sum_stirlingSecond_choose (n : ℕ) :
    bernoulli n = ∑ k ∈ range (n + 1),
      (-1) ^ k * ((n + 1).choose (k + 1) * Nat.stirlingSecond (n + k) k : ℚ) /
        (n + k).choose k := by
  set E : PowerSeries ℚ := PowerSeries.mk fun j => 1 / ((j + 1)! : ℚ)
  set B := bernoulliPowerSeries ℚ
  have hXE : PowerSeries.X * E = PowerSeries.exp ℚ - 1 := by
    ext j
    rcases j with _ | j
    · simp [E]
    · rw [PowerSeries.coeff_succ_X_mul]; simp [E, PowerSeries.coeff_exp, PowerSeries.coeff_one]
  have hBE : B * E = 1 := by
    have h := bernoulliPowerSeries_mul_exp_sub_one ℚ
    rw [← hXE] at h
    have hX : (PowerSeries.X : PowerSeries ℚ) ≠ 0 := PowerSeries.X_ne_zero
    apply mul_left_cancel₀ hX
    linear_combination h
  have hEk : ∀ k, PowerSeries.coeff n (E ^ k) = k ! * Nat.stirlingSecond (n + k) k / (n + k)! := by
    intro k
    rw [← r24b_coeff_exp_sub_one_pow, ← hXE, mul_pow, add_comm n k, PowerSeries.coeff_X_pow_mul']
    simp
  have hterm : ∀ k ∈ range (n + 1), (-1) ^ k * ((n + 1).choose (k + 1) *
      Nat.stirlingSecond (n + k) k : ℚ) / (n + k).choose k =
      n ! * PowerSeries.coeff n (PowerSeries.C ((n + 1).choose (k + 1) : ℚ) * (-E) ^ k) := by
    intro k _
    rw [PowerSeries.coeff_C_mul, neg_pow E k,
      show ((-1 : PowerSeries ℚ)) ^ k = PowerSeries.C ((-1 : ℚ) ^ k) by simp,
      PowerSeries.coeff_C_mul, hEk,
      Nat.cast_choose ℚ (show k ≤ n + k by omega), Nat.add_sub_cancel]
    have h1 : (n ! : ℚ) ≠ 0 := by positivity
    have h2 : (k ! : ℚ) ≠ 0 := by positivity
    have h3 : ((n + k)! : ℚ) ≠ 0 := by positivity
    field_simp
  rw [sum_congr rfl hterm, ← mul_sum, ← map_sum]
  have hS : (∑ k ∈ range (n + 1), PowerSeries.C ((n + 1).choose (k + 1) : ℚ) * (-E) ^ k) =
      B - B * (1 - E) ^ (n + 1) := by
    have hb : (1 - E) ^ (n + 1) = ∑ j ∈ range (n + 1 + 1), (-E) ^ j * 1 ^ (n + 1 - j) *
        ((n + 1).choose j : PowerSeries ℚ) := by rw [← add_pow]; ring
    rw [sum_range_succ'] at hb
    simp only [pow_zero, one_pow, mul_one, Nat.choose_zero_right, Nat.cast_one] at hb
    have : (∑ k ∈ range (n + 1), PowerSeries.C ((n + 1).choose (k + 1) : ℚ) * (-E) ^ k) * (-E) =
        (1 - E) ^ (n + 1) - 1 := by
      rw [hb, sum_mul, add_sub_cancel_right]
      refine sum_congr rfl fun k _ => ?_
      rw [map_natCast]; ring
    linear_combination (-B) * this - (∑ k ∈ range (n + 1),
      PowerSeries.C ((n + 1).choose (k + 1) : ℚ) * (-E) ^ k) * hBE
  rw [hS, map_sub]
  have hE0 : PowerSeries.constantCoeff (1 - E) = 0 := by simp [E]
  obtain ⟨Q, hQ⟩ := PowerSeries.X_dvd_iff.mpr hE0
  rw [hQ, mul_pow, mul_left_comm, PowerSeries.coeff_X_pow_mul']
  simp only [show ¬ n + 1 ≤ n by omega, ↓reduceIte, sub_zero]
  simp [B, bernoulliPowerSeries]
  field_simp

/-- DLMF 24.15.8: `∑ₖ (-1)^{n+k} s(n+1, k+1) Bₖ = n!/(n+1)`, with the signed Stirling number
`s(n+1, k+1) = (-1)^{n-k} |s(n+1, k+1)|` written through Mathlib's unsigned
`Nat.stirlingFirst`. -/
@[dlmf 24.15.E8]
theorem sum_stirlingFirst_mul_bernoulli (n : ℕ) :
    ∑ k ∈ range (n + 1), (-1) ^ (n + k) *
        ((-1) ^ (n - k) * (Nat.stirlingFirst (n + 1) (k + 1) : ℚ)) * bernoulli k =
      n ! / (n + 1) :=
  q24b_sum_stirlingFirst_mul_bernoulli n

/-- DLMF 24.15.9: for a prime `p` and `1 ≤ n ≤ p - 2`,
`p Bₙ/n ≡ S(p - 1 + n, p - 1) (mod p²)`. -/
@[dlmf 24.15.E9]
theorem padicNorm_bernoulli_sub_stirlingSecond {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n)
    (hnp : n ≤ p - 2) :
    padicNorm p (p * bernoulli n / n - Nat.stirlingSecond (p - 1 + n) (p - 1)) ≤
      (p : ℚ) ^ (-2 : ℤ) := by
  sorry

/-- DLMF 24.15.10: for a prime `p` and `2 ≤ 2n ≤ p - 3`,
`(2n - 1)/(4n) · p² B₂ₙ ≡ S(p + 2n, p - 1) (mod p³)`. -/
@[dlmf 24.15.E10]
theorem padicNorm_bernoulli_sub_stirlingSecond_cube {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n)
    (hnp : 2 * n ≤ p - 3) :
    padicNorm p ((2 * n - 1) / (4 * n) * p ^ 2 * bernoulli (2 * n) -
      Nat.stirlingSecond (p + 2 * n) (p - 1)) ≤ (p : ℚ) ^ (-3 : ℤ) := by
  sorry

/-! ### §24.15(iv) Fibonacci and Lucas numbers -/

/-- DLMF §24.15(iv): the Lucas numbers `v₀ = 2`, `v₁ = 1`, `vₙ₊₁ = vₙ + vₙ₋₁`. (The Fibonacci
numbers `uₙ` are Mathlib's `Nat.fib`.) -/
@[dlmf 24.15.iv]
def lucasNumber : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | n + 2 => lucasNumber (n + 1) + lucasNumber n

/-- DLMF §24.15(iv): the Lucas recurrence `vₙ₊₂ = vₙ₊₁ + vₙ`. -/
@[dlmf 24.15.iv]
theorem lucasNumber_add_two (n : ℕ) :
    lucasNumber (n + 2) = lucasNumber (n + 1) + lucasNumber n := rfl

/-- DLMF §24.15(iv): `vₙ₊₁ = uₙ + uₙ₊₂` (the Lucas numbers through the Fibonacci numbers). -/
@[dlmf 24.15.iv]
theorem lucasNumber_succ (n : ℕ) : lucasNumber (n + 1) = Nat.fib n + Nat.fib (n + 2) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rfl
    | 1 => rfl
    | n + 2 =>
      rw [lucasNumber_add_two, ih (n + 1) (by omega), ih n (by omega)]
      simp only [Nat.fib_add_two]
      ring

/-! ### Binet formulas and shifted sums (helpers for §24.15(iv)) -/

/-- A sum over `j ≤ n` whose odd terms vanish is the sum of its even terms. -/
theorem q24b_sum_range_even {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → M)
    (hf : ∀ j, Odd j → f j = 0) :
    ∑ k ∈ range (n / 2 + 1), f (2 * k) = ∑ j ∈ range (n + 1), f j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ _ (n + 1), ← ih]
    rcases Nat.even_or_odd (n + 1) with he | ho
    · obtain ⟨m, hm⟩ := he
      rw [show (n + 1) / 2 = n / 2 + 1 by omega, sum_range_succ,
        show 2 * (n / 2 + 1) = n + 1 by omega]
    · rw [hf _ ho, add_zero, show (n + 1) / 2 = n / 2 by obtain ⟨m, hm⟩ := ho; omega]

/-- The complex number `√5`. -/
noncomputable def q24b_s : ℂ := ((Real.sqrt 5 : ℝ) : ℂ)

/-- `(√5)² = 5`. -/
theorem q24b_s_sq : q24b_s ^ 2 = 5 := by
  rw [q24b_s, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num

/-- `√5 ≠ 0`. -/
theorem q24b_s_ne_zero : q24b_s ≠ 0 := by
  intro h; have := q24b_s_sq; rw [h] at this; norm_num at this

/-- Binet's formula for the Lucas numbers, in `ℂ`. -/
theorem q24b_lucas_eq (m : ℕ) :
    (lucasNumber m : ℂ) = ((1 + q24b_s) / 2) ^ m + ((1 - q24b_s) / 2) ^ m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m with
    | 0 => norm_num [lucasNumber]
    | 1 => simp [lucasNumber]; ring
    | m + 2 =>
      rw [lucasNumber_add_two, Nat.cast_add, ih (m + 1) (by omega), ih m (by omega)]
      have h := q24b_s_sq
      linear_combination (-(((1 + q24b_s) / 2) ^ m + ((1 - q24b_s) / 2) ^ m) / 4) * h

/-- Binet's formula for the Fibonacci numbers, in `ℂ`. -/
theorem q24b_fib_eq (m : ℕ) :
    (Nat.fib m : ℂ) = (((1 + q24b_s) / 2) ^ m - ((1 - q24b_s) / 2) ^ m) / q24b_s := by
  rw [eq_div_iff q24b_s_ne_zero]
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m with
    | 0 => simp
    | 1 => simp; ring
    | m + 2 =>
      rw [Nat.fib_add_two, Nat.cast_add, add_mul, ih (m + 1) (by omega), ih m (by omega)]
      have h := q24b_s_sq
      linear_combination (-(((1 + q24b_s) / 2) ^ m - ((1 - q24b_s) / 2) ^ m) / 4) * h

/-- `Eₙ(x+1) + Eₙ(x) = 2xⁿ` for complex `x`. -/
theorem q24b_eulerPolyE_add_one_add (n : ℕ) (x : ℂ) :
    eulerPolyE n (x + 1) + eulerPolyE n x = 2 * x ^ n := by
  have h := congrArg (Polynomial.aeval x) (Polynomial.euler_comp_X_add_one_add n)
  simp only [map_add, Polynomial.aeval_comp, Polynomial.aeval_X, map_one, map_mul, map_pow,
    map_ofNat] at h
  exact h

/-- `∑ⱼ (n choose j) (s/2)ʲ Eⱼ y^{n-j} = sⁿ Eₙ(1/2 + y/s)`. -/
theorem q24b_sum_euler_shift (n : ℕ) (y : ℂ) :
    ∑ j ∈ range (n + 1), (n.choose j : ℂ) * (q24b_s / 2) ^ j * eulerNumber j * y ^ (n - j) =
      q24b_s ^ n * eulerPolyE n (1 / 2 + y / q24b_s) := by
  rw [eulerPolyE_add, mul_sum]
  refine sum_congr rfl fun j hj => ?_
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hj)
  rw [eulerPolyE_half, show q24b_s ^ n = q24b_s ^ j * q24b_s ^ (n - j) by
    rw [← pow_add, Nat.add_sub_cancel' hjn], div_pow, div_pow]
  have := q24b_s_ne_zero
  field_simp


/-- `Bₙ(x+1) = Bₙ(x) + n x^{n-1}` for complex `x`. -/
theorem q24b_bernoulliPolyB_add_one (n : ℕ) (x : ℂ) :
    bernoulliPolyB n (x + 1) = bernoulliPolyB n x + n * x ^ (n - 1) := by
  have h := congrArg (Polynomial.aeval x) (Polynomial.bernoulli_comp_one_add_X n)
  simp only [Polynomial.aeval_comp, map_add, map_one, Polynomial.aeval_X, nsmul_eq_mul, map_mul,
    map_natCast, map_pow] at h
  rw [bernoulliPolyB, add_comm x, h, bernoulliPolyB]

/-- `∑ⱼ (n choose j) aʲ Bⱼ y^{n-j} = aⁿ Bₙ(y/a)`. -/
theorem q24b_sum_bernoulli_shift (n : ℕ) {a : ℂ} (ha : a ≠ 0) (y : ℂ) :
    ∑ j ∈ range (n + 1), (n.choose j : ℂ) * a ^ j * bernoulli j * y ^ (n - j) =
      a ^ n * bernoulliPolyB n (y / a) := by
  rw [bernoulliPolyB_eq_sum, mul_sum]
  refine sum_congr rfl fun j hj => ?_
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hj)
  rw [show a ^ n = a ^ j * a ^ (n - j) by rw [← pow_add, Nat.add_sub_cancel' hjn], div_pow]
  field_simp

/-- DLMF 24.15.11:
`∑_{k=0}^{⌊n/2⌋} (n choose 2k) (5/9)ᵏ B₂ₖ u_{n-2k} = (n/6) v_{n-1} + (n/3ⁿ) v_{2n-2}`. -/
@[dlmf 24.15.E11]
theorem sum_choose_bernoulli_fib (n : ℕ) :
    ∑ k ∈ range (n / 2 + 1), (n.choose (2 * k) : ℚ) * (5 / 9) ^ k * bernoulli (2 * k) *
        Nat.fib (n - 2 * k) =
      n / 6 * lucasNumber (n - 1) + n / 3 ^ n * lucasNumber (2 * n - 2) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  apply Rat.cast_injective (α := ℂ)
  push_cast
  have hs := q24b_s_sq
  have hs0 := q24b_s_ne_zero
  have hl1 := q24b_lucas_eq (m + 1 - 1)
  have hl2 := q24b_lucas_eq (2 * (m + 1) - 2)
  rw [show m + 1 - 1 = m by omega] at hl1
  rw [show 2 * (m + 1) - 2 = 2 * m by omega] at hl2
  rw [show 2 * (m + 1) - 2 = 2 * m by omega, hl2]
  rw [hl1]
  have hfib : ∀ k, (Nat.fib (m + 1 - 2 * k) : ℂ) = _ := fun k => q24b_fib_eq (m + 1 - 2 * k)
  simp_rw [hfib]
  generalize hP : (1 + q24b_s) / 2 = P
  generalize hQ : (1 - q24b_s) / 2 = Q
  generalize q24b_s = s at hs hs0 hP hQ
  set a := s / 3 with ha
  have ha0 : a ≠ 0 := by rw [ha]; exact div_ne_zero hs0 (by norm_num)
  set g : ℕ → ℂ := fun j => (((m + 1).choose j : ℕ) : ℂ) * a ^ j * (bernoulli j : ℂ) *
    ((P ^ (m + 1 - j) - Q ^ (m + 1 - j)) / s) with hg
  have hL : ∀ k, (((m + 1).choose (2 * k) : ℕ) : ℂ) * (5 / 9) ^ k * (bernoulli (2 * k) : ℂ) *
      ((P ^ (m + 1 - 2 * k) - Q ^ (m + 1 - 2 * k)) / s) = g (2 * k) := by
    intro k
    simp only [hg, pow_mul, ha, div_pow, hs]; norm_num
  simp_rw [hL]
  have key := q24b_sum_range_even (m + 1) (fun j => if j = 1 then 0 else g j) (fun j hj => by
    by_cases h1 : j = 1
    · simp [h1]
    · simp only [h1, ite_false, hg]
      rw [bernoulli_eq_zero_of_odd hj (by obtain ⟨r, hr⟩ := hj; omega)]; simp)
  have hk : ∀ k, (if 2 * k = 1 then (0 : ℂ) else g (2 * k)) = g (2 * k) := fun k => by
    simp only [show 2 * k ≠ 1 by omega, ite_false]
  simp only [hk] at key
  rw [key]
  have hsplit : ∑ j ∈ range (m + 1 + 1), (if j = 1 then (0 : ℂ) else g j) =
      ∑ j ∈ range (m + 1 + 1), g j - g 1 := by
    have hmem : 1 ∈ range (m + 1 + 1) := by simp
    have h1 := Finset.add_sum_erase (range (m + 1 + 1)) g hmem
    have h2 := Finset.add_sum_erase (range (m + 1 + 1))
      (fun j => if j = 1 then (0 : ℂ) else g j) hmem
    have h3 : ∑ j ∈ (range (m + 1 + 1)).erase 1, (if j = 1 then (0 : ℂ) else g j) =
        ∑ j ∈ (range (m + 1 + 1)).erase 1, g j :=
      sum_congr rfl fun j hj => by simp [Finset.ne_of_mem_erase hj]
    simp only [ite_true] at h2
    rw [← h2, h3, ← h1]; ring
  rw [hsplit]
  have hsum : ∑ j ∈ range (m + 1 + 1), g j = (a ^ (m + 1) * (bernoulliPolyB (m + 1) (P / a) -
      bernoulliPolyB (m + 1) (Q / a))) / s := by
    rw [mul_sub, ← q24b_sum_bernoulli_shift _ ha0, ← q24b_sum_bernoulli_shift _ ha0,
      ← sum_sub_distrib, sum_div]
    refine sum_congr rfl fun j _ => ?_
    simp only [hg]; ring
  have hPQ : P / a = Q / a + 1 + 1 + 1 := by
    rw [ha, ← hP, ← hQ]; field_simp; ring
  rw [hsum, hPQ, q24b_bernoulliPolyB_add_one, q24b_bernoulliPolyB_add_one,
    q24b_bernoulliPolyB_add_one, Nat.add_sub_cancel]
  have hg1 : g 1 = -((m + 1 : ℂ) * (P ^ m - Q ^ m) / 6) := by
    simp only [hg, Nat.choose_one_right, pow_one, bernoulli_one, Nat.add_sub_cancel, ha]
    push_cast; field_simp; ring
  rw [hg1]
  have e1 : a * (Q / a + 1) = Q ^ 2 / 3 := by
    rw [ha, ← hQ]; field_simp; linear_combination (-1 : ℂ) * hs
  have e2 : a * (Q / a + 1 + 1) = P ^ 2 / 3 := by
    rw [ha, ← hP, ← hQ]; field_simp; linear_combination (-1 : ℂ) * hs
  have e0 : a * (Q / a) = Q := by field_simp
  have hexp : a ^ (m + 1) * (↑(m + 1) * (Q / a) ^ m + ↑(m + 1) * (Q / a + 1) ^ m +
      ↑(m + 1) * (Q / a + 1 + 1) ^ m) =
        a * (m + 1) * ((P ^ 2 / 3) ^ m + (Q ^ 2 / 3) ^ m + Q ^ m) := by
    rw [show a ^ (m + 1) * (↑(m + 1) * (Q / a) ^ m + ↑(m + 1) * (Q / a + 1) ^ m +
      ↑(m + 1) * (Q / a + 1 + 1) ^ m) = a * ↑(m + 1) * ((a * (Q / a + 1 + 1)) ^ m +
        (a * (Q / a + 1)) ^ m + (a * (Q / a)) ^ m) by simp only [mul_pow]; ring, e1, e2, e0]
    push_cast; ring
  have hfinal : ∀ X : ℂ, a ^ (m + 1) * (X + ↑(m + 1) * (Q / a) ^ m +
      ↑(m + 1) * (Q / a + 1) ^ m + ↑(m + 1) * (Q / a + 1 + 1) ^ m - X) =
      a * (m + 1) * ((P ^ 2 / 3) ^ m + (Q ^ 2 / 3) ^ m + Q ^ m) := by
    intro X; rw [← hexp]; ring
  rw [hfinal, div_pow, div_pow, ← pow_mul, ← pow_mul, ha]
  field_simp
  ring

/-- DLMF 24.15.12: `∑_{k=0}^{⌊n/2⌋} (n choose 2k) (5/4)ᵏ E₂ₖ v_{n-2k} = 1/2^{n-1}`. -/
@[dlmf 24.15.E12]
theorem sum_choose_eulerNumber_lucas (n : ℕ) :
    ∑ k ∈ range (n / 2 + 1), (n.choose (2 * k) : ℚ) * (5 / 4) ^ k * eulerNumber (2 * k) *
        lucasNumber (n - 2 * k) = 2 / 2 ^ n := by
  apply Rat.cast_injective (α := ℂ)
  push_cast
  have hs := q24b_s_sq
  have hs0 := q24b_s_ne_zero
  have key := q24b_sum_range_even n (fun j => (n.choose j : ℂ) * (q24b_s / 2) ^ j *
    eulerNumber j * (((1 + q24b_s) / 2) ^ (n - j) + ((1 - q24b_s) / 2) ^ (n - j))) (fun j hj => by
      simp [eulerNumber_eq_zero_of_odd hj])
  have hL : ∀ k, (n.choose (2 * k) : ℂ) * (5 / 4) ^ k * (eulerNumber (2 * k) : ℂ) *
      (lucasNumber (n - 2 * k) : ℂ) = (n.choose (2 * k) : ℂ) * (q24b_s / 2) ^ (2 * k) *
      eulerNumber (2 * k) *
        (((1 + q24b_s) / 2) ^ (n - 2 * k) + ((1 - q24b_s) / 2) ^ (n - 2 * k)) := by
    intro k
    rw [q24b_lucas_eq, pow_mul, show (q24b_s / 2) ^ 2 = 5 / 4 by rw [div_pow, hs]; norm_num]
  simp_rw [hL]
  rw [key]
  simp_rw [mul_add, sum_add_distrib]
  rw [q24b_sum_euler_shift, q24b_sum_euler_shift]
  have h1 : 1 / 2 + (1 + q24b_s) / 2 / q24b_s = 1 / (2 * q24b_s) + 1 := by field_simp; ring
  have h2 : 1 / 2 + (1 - q24b_s) / 2 / q24b_s = 1 / (2 * q24b_s) := by field_simp; ring
  rw [h1, h2, ← mul_add, q24b_eulerPolyE_add_one_add, div_pow, one_pow, mul_pow]
  field_simp

end DLMF.BernoulliEuler
