/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.BernoulliEuler.Basic.RelatedNumbers
public import DLMF.BernoulliEuler.GeneratingFunctions
public import DLMF.Combinatorics.Stirling
public import Pochhammer.PochhammerTransform
import DLMFMathlib.NumberTheory.StirlingCongruences
import DLMFMathlib.NumberTheory.BernoulliCongruences

/-!
# Sequences of numbers related to Bernoulli and Euler numbers

This file covers DLMF §24.15(iii)–(iv): relations with Stirling numbers, and identities with
Fibonacci and Lucas numbers. The Genocchi and tangent numbers of §24.15(i)–(ii) and Table 24.15.1
are in `DLMF.BernoulliEuler.Basic.RelatedNumbers`.

## Main definitions

* `lucasNumber`: the Lucas numbers `vₙ` (DLMF §24.15(iv)).

## Main results

* `bernoulli_eq_sum_stirlingSecond`, `bernoulli_eq_sum_stirlingSecond_choose`,
  `sum_stirlingFirst_mul_bernoulli`: DLMF 24.15.6–24.15.8.
* `padicNorm_bernoulli_sub_stirlingSecond`, `padicNorm_bernoulli_sub_stirlingSecond_cube`:
  the congruences DLMF 24.15.9, 24.15.10.
* `sum_choose_bernoulli_fib`, `sum_choose_eulerNumber_lucas`: DLMF 24.15.11, 24.15.12.

## Implementation notes

DLMF's `S(n, m)` (§26.8) is Mathlib's `Nat.stirlingSecond`; DLMF's signed
`s(n, m) = (-1)^{n-m} |s(n, m)|` is written with Mathlib's unsigned `Nat.stirlingFirst`. The
congruences 24.15.9, 24.15.10 between rationals are stated with the `p`-adic norm: `a ≡ b (mod pᵏ)`
means `padicNorm p (a - b) ≤ p^{-k}`, i.e. `a - b ∈ pᵏ ℤ_(p)`. Fibonacci numbers `uₙ` are Mathlib's
`Nat.fib`. In 24.15.11 the term `(n/6) v_{n-1}` has the factor `n`, so the value of `v_{n-1}` at
`n = 0` is immaterial (natural subtraction); `1/2^{n-1}` in 24.15.12 is `2/2ⁿ`.

24.15.6 and 24.15.8 are proved with the umbral functional `Xⁿ ↦ Bₙ` (`umbralBernoulliRat`)
applied to the expansion of `Xⁿ` in falling factorials (Stirling numbers of the second kind,
`DLMF.Combinatorics.Stirling`) and to the coefficients of the rising factorial
(`coeff_ascPochhammer` from lean-codes' `Pochhammer.PochhammerTransform`). 24.15.11 and
24.15.12 follow from the Binet formulas and the shift relations of the polynomials. 24.15.7 is
proved with formal power series: by `[tᵐ] (eᵗ - 1)ᵏ = k! S(m, k)/m!` its right side is
`n! [tⁿ] ∑ₖ (n+1 choose k+1) (-E)ᵏ` with `E = (eᵗ - 1)/t`, and
`E ∑ₖ (n+1 choose k+1)(-E)ᵏ = 1 - (1 - E)ⁿ⁺¹ = 1 + O(tⁿ⁺¹)`.

## References

* NIST DLMF §24.15; Horata (1991).
-/

@[expose] public noncomputable section

open Finset Filter
open scoped Nat Real

namespace DLMF.BernoulliEuler

/-! ### The umbral functional `Xⁿ ↦ Bₙ` (helpers for §24.15(iii)) -/

section Umbral

open Polynomial

/-- The umbral functional `L(Xⁿ) = Bₙ` on `ℚ[X]`. -/
def umbralBernoulliRat : ℚ[X] →ₗ[ℚ] ℚ := Polynomial.lsum fun i =>
    (_root_.bernoulli i) • LinearMap.id

/-- `L` on monomials. -/
private lemma umbralBernoulliRat_monomial (n : ℕ) (a : ℚ) : umbralBernoulliRat (monomial n a) = a *
    _root_.bernoulli n := by
  simp [umbralBernoulliRat]; ring

/-- `L(p(X+1)) - L(p) = p'(0)`. -/
private lemma umbralBernoulliRat_comp_add_one_sub (p : ℚ[X]) :
    umbralBernoulliRat (p.comp (X + 1)) - umbralBernoulliRat p = (derivative p).eval 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [add_comp, map_add, map_add, derivative_add, eval_add, ← hp, ← hq]; ring
  | monomial n a =>
    have h1 : (monomial n a).comp (X + 1) =
        ∑ k ∈ range (n + 1), monomial k (a * n.choose k) := by
      rw [← C_mul_X_pow_eq_monomial, mul_comp, C_comp, pow_comp, X_comp, add_pow, mul_sum]
      refine sum_congr rfl fun k _ => ?_
      rw [one_pow, mul_one, ← C_mul_X_pow_eq_monomial, map_mul, ← C_eq_natCast]; ring
    rw [h1, map_sum, sum_range_succ]
    simp only [umbralBernoulliRat_monomial, Nat.choose_self, Nat.cast_one, mul_one,
        add_sub_cancel_right]
    have h2 := _root_.sum_bernoulli n
    rw [show ∑ k ∈ range n, a * (n.choose k : ℚ) * _root_.bernoulli k =
      a * ∑ k ∈ range n, (n.choose k : ℚ) * _root_.bernoulli k by rw [mul_sum]; ring_nf, h2]
    rw [derivative_monomial, eval_monomial]
    rcases n with _ | _ | n <;> simp

/-- `(-1)(-2)⋯(-k) = (-1)ᵏ k!`. -/
private lemma descPochhammer_eval_neg_one (k : ℕ) :
    (descPochhammer ℚ k).eval (-1) = (-1) ^ k * k ! := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [descPochhammer_succ_right, eval_mul, ih, eval_sub, eval_X, eval_natCast, Nat.factorial_succ]
    push_cast; ring

/-- `L(x(x-1)⋯(x-k+1)) = (-1)ᵏ k!/(k+1)`. -/
private lemma umbralBernoulliRat_descPochhammer (k : ℕ) :
    umbralBernoulliRat (descPochhammer ℚ k) = (-1) ^ k * k ! / (k + 1) := by
  have h := descPochhammer_succ_comp_X_sub_one (R := ℚ) k
  have hcomp : ((X : ℚ[X]) - 1).comp (X + 1) = X := by simp
  have h' := congrArg (fun p => p.comp (X + 1)) h
  simp only [smul_eq_mul, sub_comp, mul_comp, comp_assoc, hcomp, comp_X, add_comp,
    natCast_comp, one_comp] at h'
  have hs := umbralBernoulliRat_comp_add_one_sub (descPochhammer ℚ (k + 1))
  have hD : (descPochhammer ℚ (k + 1)).comp (X + 1) - descPochhammer ℚ (k + 1) =
      C ((k : ℚ) + 1) * descPochhammer ℚ k := by
    rw [C_add, C_1, map_natCast]; linear_combination -h'
  rw [← map_sub, hD, ← smul_eq_C_mul, map_smul, smul_eq_mul, descPochhammer_succ_left,
    derivative_mul, derivative_X, eval_add, eval_mul, eval_mul, eval_X, zero_mul, add_zero,
    eval_one, one_mul, eval_comp, eval_sub, eval_X, eval_one, zero_sub,
    descPochhammer_eval_neg_one] at hs
  have hk : (k : ℚ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero k
  rw [eq_div_iff hk, mul_comm, hs]

/-- DLMF 24.15.6 (helper form). -/
private lemma bernoulli_eq_sum_factorial_stirlingSecond (n : ℕ) :
    _root_.bernoulli n = ∑ k ∈ range (n + 1),
      (-1) ^ k * (k ! * Nat.stirlingSecond n k : ℚ) / (k + 1) := by
  have h := congrArg umbralBernoulliRat
      (DLMF.Combinatorics.X_pow_eq_sum_stirlingSecond_mul_descPochhammer ℚ n)
  rw [← monomial_one_right_eq_X_pow, umbralBernoulliRat_monomial, one_mul, map_sum] at h
  rw [h]
  refine sum_congr rfl fun k _ => ?_
  rw [← smul_eq_C_mul, map_smul, umbralBernoulliRat_descPochhammer, smul_eq_mul]
  ring

/-- DLMF 24.15.8 (helper form). -/
private lemma sum_neg_one_pow_stirlingFirst_mul_bernoulli (n : ℕ) :
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
  have h1 : umbralBernoulliRat r =
      ∑ k ∈ range (n + 1), (Nat.stirlingFirst (n + 1) (k + 1) : ℚ) * _root_.bernoulli k := by
    conv_lhs => rw [as_sum_range' r (n + 1) hdeg]
    rw [map_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [umbralBernoulliRat_monomial, hcoeff]
  have h2 : umbralBernoulliRat r = n ! / (n + 1) := by
    have hs := umbralBernoulliRat_comp_add_one_sub (ascPochhammer ℚ (n + 1))
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
  bernoulli_eq_sum_factorial_stirlingSecond n

/-- `[tᵐ] (eᵗ - 1)ᵏ = k! S(m, k)/m!`. -/
private lemma coeff_exp_sub_one_pow (m k : ℕ) :
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
    rw [← coeff_exp_sub_one_pow, ← hXE, mul_pow, add_comm n k, PowerSeries.coeff_X_pow_mul']
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
  sum_neg_one_pow_stirlingFirst_mul_bernoulli n

/-- DLMF 24.15.9: for a prime `p` and `1 ≤ n ≤ p - 2`,
`p Bₙ/n ≡ S(p - 1 + n, p - 1) (mod p²)`. -/
@[dlmf 24.15.E9]
theorem padicNorm_bernoulli_sub_stirlingSecond {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n)
    (hnp : n ≤ p - 2) :
    padicNorm p (p * bernoulli n / n - Nat.stirlingSecond (p - 1 + n) (p - 1)) ≤
      (p : ℚ) ^ (-2 : ℤ) := by
  let _ : Fact p.Prime := ⟨hp⟩
  have h := padicNorm.stirlingSecond_sub_prime_mul_bernoulli_div_le (p := p) hn hnp
  rw [← padicNorm.neg] at h
  simpa only [neg_sub] using h

/-- DLMF 24.15.10: for a prime `p` and `2 ≤ 2n ≤ p - 3`,
`(2n - 1)/(4n) · p² B₂ₙ ≡ S(p + 2n, p - 1) (mod p³)`. -/
@[dlmf 24.15.E10]
theorem padicNorm_bernoulli_sub_stirlingSecond_cube {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n)
    (hnp : 2 * n ≤ p - 3) :
    padicNorm p ((2 * n - 1) / (4 * n) * p ^ 2 * bernoulli (2 * n) -
      Nat.stirlingSecond (p + 2 * n) (p - 1)) ≤ (p : ℚ) ^ (-3 : ℤ) := by
  let _ : Fact p.Prime := ⟨hp⟩
  have h := padicNorm.stirlingSecond_sub_prime_sq_mul_bernoulli_le_of_odd (p := p) (d := 2 * n + 1)
    (by omega) (by have := hp.two_le; omega) (by exact ⟨n, by omega⟩)
  have he : p - 1 + (2 * n + 1) = p + 2 * n := by have := hp.one_le; omega
  rw [he, Nat.add_sub_cancel] at h
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at h
  have hc : ((2 * (n : ℚ) + 1 - 2) / (2 * (2 * n + 1 - 1))) =
      (2 * (n : ℚ) - 1) / (4 * n) := by ring
  rw [hc] at h
  rw [← padicNorm.neg] at h
  simpa only [neg_sub] using h

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
private lemma sum_range_half_eq_of_odd_eq_zero {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → M)
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
noncomputable def sqrtFive : ℂ := ((Real.sqrt 5 : ℝ) : ℂ)

/-- `(√5)² = 5`. -/
private lemma sqrtFive_sq : sqrtFive ^ 2 = 5 := by
  rw [sqrtFive, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num

/-- `√5 ≠ 0`. -/
private lemma sqrtFive_ne_zero : sqrtFive ≠ 0 := by
  intro h; have := sqrtFive_sq; rw [h] at this; norm_num at this

/-- Binet's formula for the Lucas numbers, in `ℂ`. -/
private lemma lucasNumber_eq_binet (m : ℕ) :
    (lucasNumber m : ℂ) = ((1 + sqrtFive) / 2) ^ m + ((1 - sqrtFive) / 2) ^ m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m with
    | 0 => norm_num [lucasNumber]
    | 1 => simp [lucasNumber]; ring
    | m + 2 =>
      rw [lucasNumber_add_two, Nat.cast_add, ih (m + 1) (by omega), ih m (by omega)]
      have h := sqrtFive_sq
      linear_combination (-(((1 + sqrtFive) / 2) ^ m + ((1 - sqrtFive) / 2) ^ m) / 4) * h

/-- Binet's formula for the Fibonacci numbers, in `ℂ`. -/
private lemma fib_eq_binet (m : ℕ) :
    (Nat.fib m : ℂ) = (((1 + sqrtFive) / 2) ^ m - ((1 - sqrtFive) / 2) ^ m) / sqrtFive := by
  rw [eq_div_iff sqrtFive_ne_zero]
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m with
    | 0 => simp
    | 1 => simp; ring
    | m + 2 =>
      rw [Nat.fib_add_two, Nat.cast_add, add_mul, ih (m + 1) (by omega), ih m (by omega)]
      have h := sqrtFive_sq
      linear_combination (-(((1 + sqrtFive) / 2) ^ m - ((1 - sqrtFive) / 2) ^ m) / 4) * h

/-- `Eₙ(x+1) + Eₙ(x) = 2xⁿ` for complex `x`. -/
private lemma eulerPolyE_add_one_add' (n : ℕ) (x : ℂ) :
    eulerPolyE n (x + 1) + eulerPolyE n x = 2 * x ^ n := by
  have h := congrArg (Polynomial.aeval x) (Polynomial.euler_comp_X_add_one_add n)
  simp only [map_add, Polynomial.aeval_comp, Polynomial.aeval_X, map_one, map_mul, map_pow,
    map_ofNat] at h
  exact h

/-- `∑ⱼ (n choose j) (s/2)ʲ Eⱼ y^{n-j} = sⁿ Eₙ(1/2 + y/s)`. -/
private lemma sum_choose_sqrtFive_pow_eulerNumber (n : ℕ) (y : ℂ) :
    ∑ j ∈ range (n + 1), (n.choose j : ℂ) * (sqrtFive / 2) ^ j * eulerNumber j * y ^ (n - j) =
      sqrtFive ^ n * eulerPolyE n (1 / 2 + y / sqrtFive) := by
  rw [eulerPolyE_add, mul_sum]
  refine sum_congr rfl fun j hj => ?_
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hj)
  rw [eulerPolyE_half, show sqrtFive ^ n = sqrtFive ^ j * sqrtFive ^ (n - j) by
    rw [← pow_add, Nat.add_sub_cancel' hjn], div_pow, div_pow]
  have := sqrtFive_ne_zero
  field_simp

/-- `Bₙ(x+1) = Bₙ(x) + n x^{n-1}` for complex `x`. -/
private lemma bernoulliPolyB_add_one (n : ℕ) (x : ℂ) :
    bernoulliPolyB n (x + 1) = bernoulliPolyB n x + n * x ^ (n - 1) := by
  have h := congrArg (Polynomial.aeval x) (Polynomial.bernoulli_comp_one_add_X n)
  simp only [Polynomial.aeval_comp, map_add, map_one, Polynomial.aeval_X, nsmul_eq_mul, map_mul,
    map_natCast, map_pow] at h
  rw [bernoulliPolyB, add_comm x, h, bernoulliPolyB]

/-- `∑ⱼ (n choose j) aʲ Bⱼ y^{n-j} = aⁿ Bₙ(y/a)`. -/
private lemma sum_choose_pow_mul_bernoulli_eq_bernoulliPolyB (n : ℕ) {a : ℂ} (ha : a ≠ 0) (y : ℂ) :
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
  have hs := sqrtFive_sq
  have hs0 := sqrtFive_ne_zero
  have hl1 := lucasNumber_eq_binet (m + 1 - 1)
  have hl2 := lucasNumber_eq_binet (2 * (m + 1) - 2)
  rw [show m + 1 - 1 = m by omega] at hl1
  rw [show 2 * (m + 1) - 2 = 2 * m by omega] at hl2
  rw [show 2 * (m + 1) - 2 = 2 * m by omega, hl2]
  rw [hl1]
  have hfib : ∀ k, (Nat.fib (m + 1 - 2 * k) : ℂ) = _ := fun k => fib_eq_binet (m + 1 - 2 * k)
  simp_rw [hfib]
  generalize hP : (1 + sqrtFive) / 2 = P
  generalize hQ : (1 - sqrtFive) / 2 = Q
  generalize sqrtFive = s at hs hs0 hP hQ
  set a := s / 3 with ha
  have ha0 : a ≠ 0 := by rw [ha]; exact div_ne_zero hs0 (by norm_num)
  set g : ℕ → ℂ := fun j => (((m + 1).choose j : ℕ) : ℂ) * a ^ j * (bernoulli j : ℂ) *
    ((P ^ (m + 1 - j) - Q ^ (m + 1 - j)) / s) with hg
  have hL : ∀ k, (((m + 1).choose (2 * k) : ℕ) : ℂ) * (5 / 9) ^ k * (bernoulli (2 * k) : ℂ) *
      ((P ^ (m + 1 - 2 * k) - Q ^ (m + 1 - 2 * k)) / s) = g (2 * k) := by
    intro k
    simp only [hg, pow_mul, ha, div_pow, hs]; norm_num
  simp_rw [hL]
  have key := sum_range_half_eq_of_odd_eq_zero (m + 1) (fun j => if j = 1 then 0 else g j)
      (fun j hj => by
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
    rw [mul_sub, ← sum_choose_pow_mul_bernoulli_eq_bernoulliPolyB _ ha0,
        ← sum_choose_pow_mul_bernoulli_eq_bernoulliPolyB _ ha0,
      ← sum_sub_distrib, sum_div]
    refine sum_congr rfl fun j _ => ?_
    simp only [hg]; ring
  have hPQ : P / a = Q / a + 1 + 1 + 1 := by
    rw [ha, ← hP, ← hQ]; field_simp; ring
  rw [hsum, hPQ, bernoulliPolyB_add_one, bernoulliPolyB_add_one,
    bernoulliPolyB_add_one, Nat.add_sub_cancel]
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
  have hs := sqrtFive_sq
  have hs0 := sqrtFive_ne_zero
  have key := sum_range_half_eq_of_odd_eq_zero n (fun j => (n.choose j : ℂ) * (sqrtFive / 2) ^ j *
    eulerNumber j * (((1 + sqrtFive) / 2) ^ (n - j) + ((1 - sqrtFive) / 2) ^ (n - j)))
        (fun j hj => by
      simp [eulerNumber_eq_zero_of_odd hj])
  have hL : ∀ k, (n.choose (2 * k) : ℂ) * (5 / 4) ^ k * (eulerNumber (2 * k) : ℂ) *
      (lucasNumber (n - 2 * k) : ℂ) = (n.choose (2 * k) : ℂ) * (sqrtFive / 2) ^ (2 * k) *
      eulerNumber (2 * k) *
        (((1 + sqrtFive) / 2) ^ (n - 2 * k) + ((1 - sqrtFive) / 2) ^ (n - 2 * k)) := by
    intro k
    rw [lucasNumber_eq_binet, pow_mul, show (sqrtFive / 2) ^ 2 = 5 /
        4 by rw [div_pow, hs]; norm_num]
  simp_rw [hL]
  rw [key]
  simp_rw [mul_add, sum_add_distrib]
  rw [sum_choose_sqrtFive_pow_eulerNumber, sum_choose_sqrtFive_pow_eulerNumber]
  have h1 : 1 / 2 + (1 + sqrtFive) / 2 / sqrtFive = 1 / (2 * sqrtFive) + 1 := by field_simp; ring
  have h2 : 1 / 2 + (1 - sqrtFive) / 2 / sqrtFive = 1 / (2 * sqrtFive) := by field_simp; ring
  rw [h1, h2, ← mul_add, eulerPolyE_add_one_add', div_pow, one_pow, mul_pow]
  field_simp

end DLMF.BernoulliEuler
