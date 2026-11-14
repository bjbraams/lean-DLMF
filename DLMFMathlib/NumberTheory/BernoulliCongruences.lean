/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.Padics.PadicNorm
public import Mathlib.Topology.Instances.Rat
import DLMFMathlib.NumberTheory.PadicNorm
import DLMFMathlib.NumberTheory.PowerSums
import Mathlib.Tactic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.FieldTheory.Finite.Basic
import DLMFMathlib.NumberTheory.BernoulliMoments
import DLMFMathlib.NumberTheory.PadicPolynomial

/-!
# p-adic estimates for Bernoulli numbers

The von Staudt–Clausen theorem bounds `|Bₙ|ₚ` by `p`. Isolating the final term of
Faulhaber's formula and estimating the remaining denominators then gives
`|p B_N - ∑_{k < p} k^N|ₚ ≤ |N|ₚ / p` for even `N ≥ 4`.

* `Bernoulli.padicNorm_bernoulli_le`: the uniform bound.
* `Bernoulli.padicNorm_prime_mul_bernoulli_sub_sum_pow_le`: the power sum approximation.
* `Bernoulli.padicNorm_bernoulli_le_of_prime_pow_dvd`: divisibility from the index.
* `Bernoulli.tendsto_padicNorm_sum_range_pow_div_sub`: the normalized power sum limit.
* `Bernoulli.padicNorm_one_sub_pow_mul_bernoulli_div_le`: bounded regularized quotients.
* `Bernoulli.padicNorm_den_mul_faulhaber_sub_le`: the denominator-cleared power sum error.
* `Bernoulli.padicNorm_bernoulli_div_le_of_not_dvd`: integral Bernoulli quotients.
* `Bernoulli.padicNorm_sum_range_pow_sub_prime_mul_bernoulli_le`: a small-index approximation.
* `Bernoulli.padicNorm_sum_range_pow_sub_two_terms_le`: the next power sum term modulo `p³`.
* `Bernoulli.sum_bernoulli_mul_bernoulli_div_of_odd`: the odd-index convolution.

The proof uses Mathlib's `Bernoulli.vonStaudt_clausen`, `sum_range_pow`, and prime
p-adic norm APIs. The consecutive integer denominator estimate is in
`DLMFMathlib.NumberTheory.PadicNorm`.
-/

public noncomputable section

open Finset Filter
open scoped Nat Topology Polynomial

namespace Bernoulli

/-- The p-adic norm of every Bernoulli number is at most `p`. -/
lemma padicNorm_bernoulli_le (p n : ℕ) [Fact p.Prime] : padicNorm p (bernoulli n) ≤ p := by
  have hp : p.Prime := Fact.out
  have hpone : (1 : ℚ) ≤ p := by exact_mod_cast hp.one_le
  rcases Nat.even_or_odd n with hn | hn
  · obtain ⟨k, rfl⟩ := hn
    obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen k
    have hb : bernoulli (k + k) = (z : ℚ) - ∑ q ∈ range (2 * k + 2) with
        q.Prime ∧ (q - 1) ∣ 2 * k, (1 : ℚ) / q := by
      rw [← two_mul]
      linarith [hz]
    rw [hb, sub_eq_add_neg]
    refine padicNorm.nonarchimedean.trans (max_le ((padicNorm.of_int z).trans hpone) ?_)
    rw [padicNorm.neg]
    apply padicNorm.sum_le' _ (by positivity)
    intro q hq
    have hqprime : q.Prime := (mem_filter.mp hq).2.1
    let _ : Fact q.Prime := ⟨hqprime⟩
    by_cases hpq : p = q
    · subst q
      have ht : padicNorm p (p : ℚ) = (p : ℚ)⁻¹ := padicNorm.padicNorm_p_of_prime
      rw [padicNorm.div, padicNorm.one, ht, one_div, inv_inv]
    · have ht : padicNorm p (q : ℚ) = 1 := padicNorm.padicNorm_of_prime_of_ne hpq
      simpa only [padicNorm.div, padicNorm.one, ht, div_one] using hpone
  · by_cases hn1 : n = 1
    · subst n
      rw [bernoulli_one, neg_div, padicNorm.neg, padicNorm.div, padicNorm.one]
      by_cases hp2 : p = 2
      · subst p
        have ht : padicNorm 2 (2 : ℚ) = (2 : ℚ)⁻¹ := padicNorm.padicNorm_p_of_prime
        rw [ht]
        norm_num
      · let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        have ht : padicNorm p (2 : ℚ) = 1 := padicNorm.padicNorm_of_prime_of_ne hp2
        simpa only [ht, div_one] using hpone
    · rw [bernoulli_eq_zero_of_odd hn (by have := hn.pos; omega), padicNorm.zero]
      positivity

/-- For even `N ≥ 4`, the sum of the `N`th powers modulo `p` approximates `p B_N`
with p-adic error at most `|N|ₚ / p`. -/
lemma padicNorm_prime_mul_bernoulli_sub_sum_pow_le {p N : ℕ} [Fact p.Prime]
    (hN : 4 ≤ N) (heven : Even N) :
    padicNorm p ((p : ℚ) * bernoulli N - ∑ k ∈ range p, (k : ℚ) ^ N) ≤
      padicNorm p (N : ℚ) / p := by
  have h := sum_range_pow p N
  rw [sum_range_succ] at h
  have hlast : bernoulli N * ((N + 1).choose N : ℚ) * (p : ℚ) ^ (N + 1 - N) /
      (N + 1) = p * bernoulli N := by
    rw [Nat.choose_succ_self_right, show N + 1 - N = 1 by omega, pow_one]
    have hNZ : (N + 1 : ℚ) ≠ 0 := by positivity
    push_cast
    field_simp
  rw [hlast] at h
  have he : (p : ℚ) * bernoulli N - ∑ k ∈ range p, (k : ℚ) ^ N =
      - ∑ j ∈ range N, bernoulli j * ((N + 1).choose j) *
        (p : ℚ) ^ (N + 1 - j) / (N + 1) := by linarith [h]
  rw [he, padicNorm.neg]
  apply padicNorm.sum_le' _ (div_nonneg (padicNorm.nonneg _) (by positivity))
  intro j hj
  have hjN : j < N := mem_range.mp hj
  by_cases hjtop : j = N - 1
  · subst j
    have hodd : Odd (N - 1) := by
      obtain ⟨r, hr⟩ := heven
      exact ⟨r - 1, by omega⟩
    rw [bernoulli_eq_zero_of_odd hodd (by omega), zero_mul, zero_mul, zero_div, padicNorm.zero]
    exact div_nonneg (padicNorm.nonneg _) (by positivity)
  · have hd : 2 ≤ N - j := by omega
    have hcoeff : ((N + 1).choose j : ℚ) / (N + 1) =
        (N : ℚ) * ((N - 1).choose j : ℚ) / ((N - j) * (N - j + 1) : ℕ) := by
      rw [Nat.cast_choose ℚ (by omega : j ≤ N + 1), Nat.cast_choose ℚ (by omega : j ≤ N - 1)]
      have hfac : (N + 1) ! = (N + 1) * N * (N - 1) ! := by
        rw [Nat.factorial_succ, ← Nat.mul_factorial_pred (by omega : N ≠ 0)]
        ring
      have hdiff : (N + 1 - j) ! = (N - j + 1) * (N - j) * (N - 1 - j) ! := by
        rw [show N + 1 - j = (N - j) + 1 by omega, Nat.factorial_succ,
          ← Nat.mul_factorial_pred (by omega : N - j ≠ 0),
          show N - j - 1 = N - 1 - j by omega]
        ring
      rw [hfac, hdiff]
      simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      have hz₁ : (N + 1 : ℚ) ≠ 0 := by positivity
      have hz₂ : (j ! : ℚ) ≠ 0 := by positivity
      have hz₃ : ((N - 1 - j) ! : ℚ) ≠ 0 := by positivity
      have hz₄ : ((N - j : ℕ) : ℚ) ≠ 0 := by positivity
      have hz₅ : (((N - j : ℕ) : ℚ) + 1) ≠ 0 := by positivity
      field_simp
    have hterm : bernoulli j * ((N + 1).choose j : ℚ) *
        (p : ℚ) ^ (N + 1 - j) / (N + 1) =
      (N : ℚ) * ((N - 1).choose j : ℚ) * bernoulli j *
        ((p : ℚ) ^ (N - j + 1) / ((N - j : ℕ) * (N - j + 1) : ℕ)) := by
      rw [show N + 1 - j = N - j + 1 by omega]
      calc
        _ = bernoulli j * (p : ℚ) ^ (N - j + 1) *
            (((N + 1).choose j : ℚ) / (N + 1)) := by ring
        _ = _ := by rw [hcoeff]; ring
    rw [hterm, padicNorm.mul, padicNorm.mul, padicNorm.mul]
    have hc := padicNorm.of_nat (p := p) ((N - 1).choose j)
    have hb := padicNorm_bernoulli_le p j
    have hd := padicNorm.pow_div_mul_succ_le_neg_two (p := p) hd
    have hd' : padicNorm p ((p : ℚ) ^ (N - j + 1) /
        (((N - j) * (N - j + 1) : ℕ) : ℚ)) ≤ (p : ℚ) ^ (-2 : ℤ) := by
      simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using hd
    calc
      _ ≤ padicNorm p (N : ℚ) * 1 * p * (p : ℚ) ^ (-2 : ℤ) := by
        have h₁ := mul_le_mul_of_nonneg_left hc (padicNorm.nonneg (p := p) (N : ℚ))
        have h₂ := mul_le_mul h₁ hb (padicNorm.nonneg (p := p) (bernoulli j))
          (mul_nonneg (padicNorm.nonneg (p := p) (N : ℚ)) (by norm_num : (0 : ℚ) ≤ 1))
        exact mul_le_mul h₂ hd' (padicNorm.nonneg _) (mul_nonneg
          (mul_nonneg (padicNorm.nonneg _) (by norm_num)) (by positivity))
      _ = _ := by
        have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
        rw [mul_one]
        simp only [zpow_neg, zpow_ofNat]
        field_simp

/-- For even `N ≥ 4` with `p - 1 ∤ N`, a prime power dividing the index gives the
same p-adic divisibility of the Bernoulli number. -/
lemma padicNorm_bernoulli_le_of_prime_pow_dvd {p N ℓ : ℕ} (hp : p.Prime) (hN4 : 4 ≤ N)
    (hNeven : Even N) (hN : p ^ ℓ ∣ N) (hNd : ¬ (p - 1) ∣ N) :
    padicNorm p (bernoulli N) ≤ (p : ℚ) ^ (-(ℓ : ℤ)) := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hsum := Int.prime_pow_dvd_sum_range_pow hp hN hNd
  have hsnorm : padicNorm p (∑ j ∈ range p, (j : ℚ) ^ N) ≤
      (p : ℚ) ^ (-((ℓ + 1 : ℕ) : ℤ)) := by
    have h := (padicNorm.dvd_iff_norm_le (p := p) (n := ℓ + 1)
      (z := ∑ j ∈ range p, (j : ℤ) ^ N)).mp (by
        simpa only [Nat.cast_pow] using hsum)
    simpa only [Int.cast_sum, Int.cast_pow, Int.cast_natCast] using h
  have hindex : padicNorm p (N : ℚ) ≤ (p : ℚ) ^ (-(ℓ : ℤ)) := by
    have hdz : ((p ^ ℓ : ℕ) : ℤ) ∣ N := by exact_mod_cast hN
    exact_mod_cast padicNorm.dvd_iff_norm_le.mp hdz
  have hrest := Bernoulli.padicNorm_prime_mul_bernoulli_sub_sum_pow_le
    (p := p) hN4 hNeven
  have hrest' : padicNorm p ((p : ℚ) * bernoulli N - ∑ j ∈ range p, (j : ℚ) ^ N) ≤
      (p : ℚ) ^ (-((ℓ + 1 : ℕ) : ℤ)) := by
    calc
      _ ≤ padicNorm p (N : ℚ) / p := hrest
      _ ≤ (p : ℚ) ^ (-(ℓ : ℤ)) / p := div_le_div_of_nonneg_right hindex (by positivity)
      _ = _ := by
        have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
        rw [show -((ℓ + 1 : ℕ) : ℤ) = -(ℓ : ℤ) - 1 by omega, zpow_sub₀ hp0, zpow_one]
  have hpB : padicNorm p ((p : ℚ) * bernoulli N) ≤
      (p : ℚ) ^ (-((ℓ + 1 : ℕ) : ℤ)) := by
    have he : (p : ℚ) * bernoulli N =
        ((p : ℚ) * bernoulli N - ∑ j ∈ range p, (j : ℚ) ^ N) +
          (∑ j ∈ range p, (j : ℚ) ^ N) := by ring
    rw [he]
    exact padicNorm.nonarchimedean.trans (max_le hrest' hsnorm)
  rw [padicNorm.mul, padicNorm.padicNorm_p_of_prime] at hpB
  have hpQ : (0 : ℚ) < p := by exact_mod_cast hp.pos
  have hm := mul_le_mul_of_nonneg_left hpB hpQ.le
  have he₁ : (p : ℚ) * ((p : ℚ)⁻¹ * padicNorm p (bernoulli N)) =
      padicNorm p (bernoulli N) := by field_simp
  have he₂ : (p : ℚ) * (p : ℚ) ^ (-((ℓ + 1 : ℕ) : ℤ)) =
      (p : ℚ) ^ (-(ℓ : ℤ)) := by
    rw [show -((ℓ + 1 : ℕ) : ℤ) = -(ℓ : ℤ) - 1 by omega,
      zpow_sub₀ hpQ.ne', zpow_one]
    field_simp
  rwa [he₁, he₂] at hm

/-- Normalized power sums over `p^R` converge p-adically to the Bernoulli number. -/
lemma tendsto_padicNorm_sum_range_pow_div_sub {p : ℕ} [Fact p.Prime] (N : ℕ) :
    Tendsto (fun R : ℕ => padicNorm p
      ((∑ j ∈ range (p ^ R), (j : ℚ) ^ N) / (p ^ R : ℚ) - _root_.bernoulli N))
      atTop (𝓝 0) := by
  have hp : p.Prime := Fact.out
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (1 : ℚ) < p := by exact_mod_cast hp.one_lt
  have hgeo : Tendsto (fun R : ℕ => ((p : ℚ)⁻¹) ^ R) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hp1)
  let c : ℕ → ℚ := fun j => _root_.bernoulli j * ((N + 1).choose j : ℚ) / (N + 1)
  have he (R : ℕ) :
      (∑ j ∈ range (p ^ R), (j : ℚ) ^ N) / (p ^ R : ℚ) - _root_.bernoulli N =
        ∑ j ∈ range N, c j * (p ^ R : ℚ) ^ (N - j) := by
    rw [sum_range_pow, sum_range_succ, add_div, sum_div]
    push_cast
    have hlast : _root_.bernoulli N * ((N + 1).choose N : ℚ) *
        (p ^ R : ℚ) ^ (N + 1 - N) / (N + 1) / (p ^ R) = _root_.bernoulli N := by
      rw [Nat.choose_succ_self_right, show N + 1 - N = 1 by omega, pow_one]
      have hNZ : (N + 1 : ℚ) ≠ 0 := by positivity
      push_cast
      field_simp
    rw [hlast, add_sub_cancel_right]
    apply sum_congr rfl
    intro j hj
    dsimp only [c]
    have hjN := mem_range.mp hj
    rw [show N + 1 - j = (N - j) + 1 by omega, pow_succ]
    field_simp
  have hnorm (R : ℕ) : padicNorm p (p ^ R : ℚ) = ((p : ℚ)⁻¹) ^ R := by
    rw [IsAbsoluteValue.abv_pow (padicNorm p)]
    exact congrArg (fun q : ℚ => q ^ R) (padicNorm.padicNorm_p_of_prime)
  have hbound (R : ℕ) : padicNorm p
      ((∑ j ∈ range (p ^ R), (j : ℚ) ^ N) / (p ^ R : ℚ) - _root_.bernoulli N) ≤
        ∑ j ∈ range N, padicNorm p (c j) * (((p : ℚ)⁻¹) ^ R) ^ (N - j) := by
    rw [he]
    apply padicNorm.sum_le' _
      (Finset.sum_nonneg (fun j _ => mul_nonneg (padicNorm.nonneg _) (by positivity)))
    intro j hj
    rw [padicNorm.mul, IsAbsoluteValue.abv_pow (padicNorm p), hnorm]
    exact Finset.single_le_sum
      (fun k _ => mul_nonneg (padicNorm.nonneg (p := p) (c k)) (by positivity)) hj
  have hu : Tendsto (fun R : ℕ =>
      ∑ j ∈ range N, padicNorm p (c j) * (((p : ℚ)⁻¹) ^ R) ^ (N - j)) atTop (𝓝 0) := by
    have ht (j : ℕ) (hj : j ∈ range N) : Tendsto
        (fun R : ℕ => padicNorm p (c j) * (((p : ℚ)⁻¹) ^ R) ^ (N - j)) atTop (𝓝 0) := by
      have hjN : j < N := mem_range.mp hj
      simpa only [zero_pow (by omega : N - j ≠ 0), mul_zero] using
        tendsto_const_nhds.mul (hgeo.pow (N - j))
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum (range N) ht
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
    (fun R => padicNorm.nonneg (p := p)
    ((∑ j ∈ range (p ^ R), (j : ℚ) ^ N) / (p ^ R : ℚ) - _root_.bernoulli N)) hbound

/-- For `p ∤ a`, the regularized Bernoulli quotient `(1 - a^N) B_N / N` is
a p-adic integer when `N ≥ 1`. -/
lemma padicNorm_one_sub_pow_mul_bernoulli_div_le {p a N : ℕ} [Fact p.Prime] (hN : 1 ≤ N)
    (ha : ¬ p ∣ a) : padicNorm p (((1 - (a : ℚ) ^ N) * _root_.bernoulli N) / N) ≤ 1 := by
  obtain ⟨L, hLX, hLav⟩ := Polynomial.exists_linearMap_pow_eq_regularized_bernoulli (K := ℚ) a
  have hbase (k : ℕ) : padicNorm p (L (Ring.choose (Polynomial.X : ℚ[X]) k)) ≤ 1 := by
    simpa only [Nat.cast_zero, map_zero, add_zero, Polynomial.comp_X] using
      LinearMap.padicNorm_apply_choose_X_comp_natCast ha L hLav k 0
  have h := LinearMap.padicNorm_apply_le_of_choose_X L hbase (by norm_num : (0 : ℚ) ≤ 1)
    ((Polynomial.X : ℚ[X]) ^ (N - 1)) (fun j => by
      simp only [Polynomial.eval_pow, Polynomial.eval_X]
      exact_mod_cast padicNorm.of_nat (p := p) (j ^ (N - 1)))
  rw [hLX, Nat.sub_add_cancel hN] at h
  have hc : (((N - 1 : ℕ) : ℚ) + 1) = (N : ℚ) := by exact_mod_cast Nat.sub_add_cancel hN
  simpa only [hc, Rat.cast_id] using h

/-- Multiplying the even Bernoulli power sum error by the Bernoulli denominator
gives a p-adic error at most `|M|ₚ²` for every prime divisor `p` of `M`. -/
lemma padicNorm_den_mul_faulhaber_sub_le {p M n : ℕ} [Fact p.Prime] (hn : 1 ≤ n)
    (hM : 1 ≤ M) (hpM : p ∣ M) :
    padicNorm p (((_root_.bernoulli (2 * n)).den : ℚ) *
      ((M : ℚ) * _root_.bernoulli (2 * n) - ∑ k ∈ range M, (k : ℚ) ^ (2 * n))) ≤
        (padicNorm p (M : ℚ)) ^ 2 := by
  have hp : p.Prime := Fact.out
  have hpQ : (0 : ℚ) < p := by exact_mod_cast hp.pos
  by_cases hn1 : n = 1
  · subst n
    norm_num only [Nat.mul_one, bernoulli_two]
    have he : (6 : ℚ) * ((M : ℚ) * (1 / 6) - ∑ k ∈ range M, (k : ℚ) ^ 2) =
        (M : ℚ) ^ 2 * (3 - 2 * M) := by
      rw [sum_range_pow]
      norm_num [sum_range_succ]
      ring
    rw [he, padicNorm.mul, IsAbsoluteValue.abv_pow (padicNorm p)]
    have hi : padicNorm p (3 - 2 * (M : ℚ)) ≤ 1 := by
      simpa only [Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast] using
        padicNorm.of_int (p := p) (3 - 2 * (M : ℤ))
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hi (sq_nonneg _)
  have hn2 : 2 ≤ n := by omega
  let N := 2 * n
  let D : ℕ := (_root_.bernoulli N).den
  let r : ℕ := if p ≤ 3 then 0 else 1
  have hD : padicNorm p (D : ℚ) ≤ 1 := padicNorm.of_nat D
  have hDB (j : ℕ) : padicNorm p (D : ℚ) * padicNorm p (_root_.bernoulli j) ≤ (p : ℚ) ^ r := by
    by_cases hp3 : p ≤ 3
    · have hd : p ∣ D := by
        dsimp only [D, N]
        apply Bernoulli.dvd_den_bernoulli (by omega)
        have hp2 := hp.two_le
        rcases (show p = 2 ∨ p = 3 by omega) with rfl | rfl
        · simp
        · exact even_iff_two_dvd.mp (even_two_mul n)
      have hDn : padicNorm p (D : ℚ) ≤ (p : ℚ) ^ (-1 : ℤ) := by
        have hdz : ((p ^ 1 : ℕ) : ℤ) ∣ D := by
          simpa only [pow_one] using (Int.natCast_dvd_natCast.mpr hd)
        simpa only [Int.cast_natCast, Nat.cast_one] using padicNorm.dvd_iff_norm_le.mp hdz
      simp only [r, hp3, ↓reduceIte, pow_zero]
      calc
        _ ≤ padicNorm p (D : ℚ) * p := mul_le_mul_of_nonneg_left
          (Bernoulli.padicNorm_bernoulli_le p j) (padicNorm.nonneg _)
        _ ≤ (p : ℚ) ^ (-1 : ℤ) * p := mul_le_mul_of_nonneg_right hDn hpQ.le
        _ = 1 := by simp only [zpow_neg_one]; field_simp
    · simp only [r, hp3, ↓reduceIte, pow_one]
      calc
        _ ≤ (1 : ℚ) * p := mul_le_mul hD (Bernoulli.padicNorm_bernoulli_le p j)
          (padicNorm.nonneg _) (by norm_num)
        _ = _ := one_mul _
  have hv (d : ℕ) (hd : 2 ≤ d) : multiplicity p (d + 1) + r ≤ d - 1 := by
    by_cases hp3 : p ≤ 3
    · simp only [r, hp3, ↓reduceIte, add_zero]
      have h := Nat.multiplicity_mul_succ_le_sub_one hp hd
      rw [Nat.multiplicity_mul (by omega : d ≠ 0) (by omega : d + 1 ≠ 0)] at h
      omega
    · have hp4 : p ≠ 4 := by rintro rfl; norm_num at hp
      have hp5 : 5 ≤ p := by omega
      have h := Nat.multiplicity_succ_le_sub_two hp5 hd
      simp only [r, hp3, ↓reduceIte]
      omega
  have hs := sum_range_pow M N
  rw [sum_range_succ] at hs
  have hlast : _root_.bernoulli N * ((N + 1).choose N : ℚ) *
      (M : ℚ) ^ (N + 1 - N) / (N + 1) = M * _root_.bernoulli N := by
    rw [Nat.choose_succ_self_right, show N + 1 - N = 1 by omega, pow_one]
    have hz : (N + 1 : ℚ) ≠ 0 := by positivity
    push_cast
    field_simp
  rw [hlast] at hs
  have herr : (D : ℚ) * ((M : ℚ) * _root_.bernoulli N - ∑ k ∈ range M, (k : ℚ) ^ N) =
      - ∑ j ∈ range N, (D : ℚ) * _root_.bernoulli j * ((N + 1).choose j : ℚ) *
        (M : ℚ) ^ (N + 1 - j) / (N + 1) := by
    have he : (M : ℚ) * _root_.bernoulli N - ∑ k ∈ range M, (k : ℚ) ^ N =
      -∑ j ∈ range N, _root_.bernoulli j * ((N + 1).choose j : ℚ) *
        (M : ℚ) ^ (N + 1 - j) / (N + 1) := by linarith [hs]
    rw [he, mul_neg, mul_sum]
    congr 1
    apply sum_congr rfl
    intro j _
    ring
  rw [herr, padicNorm.neg]
  apply padicNorm.sum_le' _ (sq_nonneg _)
  intro j hj
  have hjN : j < N := mem_range.mp hj
  by_cases hjtop : j = N - 1
  · subst j
    have ho : Odd (N - 1) := by exact ⟨n - 1, by dsimp only [N]; omega⟩
    rw [bernoulli_eq_zero_of_odd ho (by dsimp only [N]; omega), mul_zero, zero_mul,
      zero_mul, zero_div, padicNorm.zero]
    exact sq_nonneg _
  have hd : 2 ≤ N - j := by omega
  have hC : ((N + 1).choose j : ℚ) / (N + 1) =
      (N.choose j : ℚ) / (((N + 1 - j : ℕ) : ℚ)) := by
    have hz1 : (N + 1 : ℚ) ≠ 0 := by positivity
    have hz2 : ((N + 1 - j : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [div_eq_div_iff hz1 hz2]
    exact_mod_cast (Nat.choose_mul_succ_eq N j).symm
  have he : (D : ℚ) * _root_.bernoulli j * ((N + 1).choose j : ℚ) *
      (M : ℚ) ^ (N + 1 - j) / (N + 1) =
        (D : ℚ) * _root_.bernoulli j * (N.choose j : ℚ) *
          ((M : ℚ) ^ (N - j + 1) / (((N - j : ℕ) : ℚ) + 1)) := by
    calc
      _ = (D : ℚ) * _root_.bernoulli j * (M : ℚ) ^ (N + 1 - j) *
          (((N + 1).choose j : ℚ) / (N + 1)) := by ring
      _ = _ := by
        rw [hC, show N + 1 - j = (N - j) + 1 by omega, Nat.cast_add, Nat.cast_one]
        ring
  rw [he, padicNorm.mul, padicNorm.mul, padicNorm.mul]
  have hb := hDB j
  have hc := padicNorm.of_nat (p := p) (N.choose j)
  have hdB := padicNorm.pow_div_succ_le_of_multiplicity hM hpM hd (hv (N - j) hd)
  calc
    _ ≤ (p : ℚ) ^ r * 1 * ((padicNorm p (M : ℚ)) ^ 2 / (p : ℚ) ^ r) := by
      have hh := mul_le_mul hb hc (padicNorm.nonneg _) (by positivity : (0 : ℚ) ≤ (p : ℚ) ^ r)
      exact mul_le_mul hh hdB (padicNorm.nonneg _) (by positivity)
    _ = _ := by field_simp

/-- If `p - 1 ∤ N`, the Bernoulli quotient `B_N/N` is a p-adic integer. -/
lemma padicNorm_bernoulli_div_le_of_not_dvd {p N : ℕ} [Fact p.Prime] (hN : ¬ (p - 1) ∣ N) :
    padicNorm p (_root_.bernoulli N / N) ≤ 1 := by
  have hN1 : 1 ≤ N := by
    by_contra h
    have hz : N = 0 := by omega
    exact hN (by simp only [hz, dvd_zero])
  have hn : ¬ ∀ u : (ZMod p)ˣ, u ^ N = 1 := by
    intro hu
    exact hN (by simpa only [ZMod.card] using (FiniteField.forall_pow_eq_one_iff (ZMod p) N).mp hu)
  push Not at hn
  obtain ⟨u, hu⟩ := hn
  let a := (u : ZMod p).val
  have ha : (a : ZMod p) = u := ZMod.natCast_zmod_val _
  have hap : ¬ p ∣ a := by
    intro hd
    have hz : (a : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hd
    rw [ha] at hz
    exact u.ne_zero hz
  have hf : padicNorm p (1 - (a : ℚ) ^ N) = 1 := by
    have hnot : ¬ (p : ℤ) ∣ (1 - (a : ℤ) ^ N) := by
      intro hd
      have hz : ((1 - (a : ℤ) ^ N : ℤ) : ZMod p) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hd
      push_cast at hz
      have he : (a : ZMod p) ^ N = 1 := by linear_combination -hz
      rw [ha] at he
      exact hu (Units.ext he)
    have h := (padicNorm.int_eq_one_iff (p := p) (1 - (a : ℤ) ^ N)).mpr hnot
    simpa only [Int.cast_sub, Int.cast_one, Int.cast_pow, Int.cast_natCast] using h
  have h := Bernoulli.padicNorm_one_sub_pow_mul_bernoulli_div_le (p := p) hN1 hap
  rwa [mul_div_assoc, padicNorm.mul, hf, one_mul] at h

/-- Bernoulli numbers at indices below `p-1` are p-adic integers. -/
lemma padicNorm_bernoulli_le_one_of_lt {p j : ℕ} [Fact p.Prime] (hj : j < p - 1) :
    padicNorm p (_root_.bernoulli j) ≤ 1 := by
  rcases j with _ | j
  · simp
  have hj0 : (j + 1 : ℚ) ≠ 0 := by positivity
  have hn := padicNorm_bernoulli_div_le_of_not_dvd (p := p) (Nat.not_dvd_of_pos_of_lt (by omega) hj)
  norm_num only [Nat.cast_add, Nat.cast_one] at hn
  have he : _root_.bernoulli (j + 1) = (_root_.bernoulli (j + 1) / (j + 1)) * (j + 1) := by
    field_simp
  rw [he, padicNorm.mul]
  have hnat : padicNorm p (j + 1 : ℚ) ≤ 1 := by exact_mod_cast padicNorm.of_nat (p := p) (j + 1)
  calc
    _ ≤ 1 * 1 := mul_le_mul hn hnat (padicNorm.nonneg _) (by norm_num)
    _ = _ := one_mul _

/-- For `1 ≤ N ≤ p-2`, the power sum over the residues differs from `p B_N`
by a rational of p-adic norm at most `p⁻²`. -/
lemma padicNorm_sum_range_pow_sub_prime_mul_bernoulli_le {p N : ℕ} [Fact p.Prime]
    (hN : 1 ≤ N) (hNp : N ≤ p - 2) :
    padicNorm p ((∑ j ∈ range p, (j : ℚ) ^ N) - p * _root_.bernoulli N) ≤ (p : ℚ) ^ (-2 : ℤ) := by
  have hp : p.Prime := Fact.out
  have hpQ : (1 : ℚ) < p := by exact_mod_cast hp.one_lt
  have hsum := sum_range_pow p N
  rw [sum_range_succ] at hsum
  have hlast : _root_.bernoulli N * ((N + 1).choose N : ℚ) * (p : ℚ) ^ (N + 1 - N) /
      (N + 1) = p * _root_.bernoulli N := by
    rw [Nat.choose_succ_self_right, show N + 1 - N = 1 by omega, pow_one]
    have hz : (N + 1 : ℚ) ≠ 0 := by positivity
    push_cast
    field_simp
  rw [hlast] at hsum
  have he : (∑ j ∈ range p, (j : ℚ) ^ N) - p * _root_.bernoulli N =
      ∑ j ∈ range N, _root_.bernoulli j * ((N + 1).choose j : ℚ) *
        (p : ℚ) ^ (N + 1 - j) / (N + 1) := by linarith [hsum]
  rw [he]
  apply padicNorm.sum_le' _ (by positivity)
  intro j hj
  have hjN : j < N := mem_range.mp hj
  have hdlo : 2 ≤ N + 1 - j := by omega
  have hdhi : N + 1 - j < p := by omega
  have hC : ((N + 1).choose j : ℚ) / (N + 1) =
      (N.choose j : ℚ) / (((N + 1 - j : ℕ) : ℚ)) := by
    have hz1 : (N + 1 : ℚ) ≠ 0 := by positivity
    have hz2 : ((N + 1 - j : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [div_eq_div_iff hz1 hz2]
    exact_mod_cast (Nat.choose_mul_succ_eq N j).symm
  have hterm : _root_.bernoulli j * ((N + 1).choose j : ℚ) *
      (p : ℚ) ^ (N + 1 - j) / (N + 1) =
        _root_.bernoulli j * (N.choose j : ℚ) *
          (p : ℚ) ^ (N + 1 - j) / (((N + 1 - j : ℕ) : ℚ)) := by
    calc
      _ = _root_.bernoulli j * (p : ℚ) ^ (N + 1 - j) *
          (((N + 1).choose j : ℚ) / (N + 1)) := by ring
      _ = _ := by rw [hC]; ring
  rw [hterm, padicNorm.div, padicNorm.mul, padicNorm.mul,
    (padicNorm.nat_eq_one_iff (N + 1 - j)).mpr (Nat.not_dvd_of_pos_of_lt (by omega) hdhi), div_one]
  have hb := padicNorm_bernoulli_le_one_of_lt (p := p) (by omega : j < p - 1)
  have hc := padicNorm.of_nat (p := p) (N.choose j)
  have hpow : padicNorm p ((p : ℚ) ^ (N + 1 - j)) ≤ (p : ℚ) ^ (-2 : ℤ) := by
    rw [IsAbsoluteValue.abv_pow (padicNorm p)]
    have ht : padicNorm p (p : ℚ) = (p : ℚ)⁻¹ := padicNorm.padicNorm_p_of_prime
    rw [ht, inv_pow, ← zpow_natCast, ← zpow_neg]
    apply zpow_le_zpow_right₀ hpQ.le
    omega
  have hbc := mul_le_mul hb hc (padicNorm.nonneg _) (by norm_num : (0 : ℚ) ≤ 1)
  calc
    _ ≤ (1 : ℚ) * (p : ℚ) ^ (-2 : ℤ) :=
      mul_le_mul (by simpa only [one_mul] using hbc) hpow (padicNorm.nonneg _) (by norm_num)
    _ = _ := one_mul _

/-- The two leading terms of Faulhaber's formula approximate the power sum modulo `p³`
for `2 ≤ N ≤ p-2`. -/
lemma padicNorm_sum_range_pow_sub_two_terms_le {p N : ℕ} [Fact p.Prime]
    (hN : 2 ≤ N) (hNp : N ≤ p - 2) :
    padicNorm p ((∑ j ∈ range p, (j : ℚ) ^ N) - p * _root_.bernoulli N -
      N * (p : ℚ) ^ 2 / 2 * _root_.bernoulli (N - 1)) ≤ (p : ℚ) ^ (-3 : ℤ) := by
  have hp : p.Prime := Fact.out
  have hpQ : (1 : ℚ) < p := by exact_mod_cast hp.one_lt
  have hsum := sum_range_pow p N
  rw [sum_range_succ] at hsum
  have hlast : _root_.bernoulli N * ((N + 1).choose N : ℚ) * (p : ℚ) ^ (N + 1 - N) /
      (N + 1) = p * _root_.bernoulli N := by
    rw [Nat.choose_succ_self_right, show N + 1 - N = 1 by omega, pow_one]
    have hz : (N + 1 : ℚ) ≠ 0 := by positivity
    push_cast
    field_simp
  rw [hlast] at hsum
  have hsplit := sum_range_succ
    (fun j => _root_.bernoulli j * ((N + 1).choose j : ℚ) *
      (p : ℚ) ^ (N + 1 - j) / (N + 1)) (N - 1)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ N)] at hsplit
  have hnext : _root_.bernoulli (N - 1) * ((N + 1).choose (N - 1) : ℚ) *
      (p : ℚ) ^ (N + 1 - (N - 1)) / (N + 1) =
        N * (p : ℚ) ^ 2 / 2 * _root_.bernoulli (N - 1) := by
    have hc : (N + 1).choose (N - 1) * 2 = (N + 1) * N := by
      have h := Nat.choose_mul_succ_eq N (N - 1)
      rw [← Nat.choose_symm (by omega : N - 1 ≤ N),
        show N - (N - 1) = 1 by omega, Nat.choose_one_right,
        show N + 1 - (N - 1) = 2 by omega] at h
      simpa only [mul_comm] using h.symm
    have hcQ : ((N + 1).choose (N - 1) : ℚ) * 2 = (N + 1) * N := by exact_mod_cast hc
    rw [show N + 1 - (N - 1) = 2 by omega]
    have hz : (N + 1 : ℚ) ≠ 0 := by positivity
    field_simp
    linear_combination _root_.bernoulli (N - 1) * hcQ
  rw [hnext] at hsplit
  have he : (∑ j ∈ range p, (j : ℚ) ^ N) - p * _root_.bernoulli N -
      N * (p : ℚ) ^ 2 / 2 * _root_.bernoulli (N - 1) =
        ∑ j ∈ range (N - 1), _root_.bernoulli j * ((N + 1).choose j : ℚ) *
          (p : ℚ) ^ (N + 1 - j) / (N + 1) := by linarith [hsum, hsplit]
  rw [he]
  apply padicNorm.sum_le' _ (by positivity)
  intro j hj
  have hjN : j < N - 1 := mem_range.mp hj
  have hdlo : 3 ≤ N + 1 - j := by omega
  have hdhi : N + 1 - j < p := by omega
  have hC : ((N + 1).choose j : ℚ) / (N + 1) =
      (N.choose j : ℚ) / (((N + 1 - j : ℕ) : ℚ)) := by
    have hz1 : (N + 1 : ℚ) ≠ 0 := by positivity
    have hz2 : ((N + 1 - j : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [div_eq_div_iff hz1 hz2]
    exact_mod_cast (Nat.choose_mul_succ_eq N j).symm
  have hterm : _root_.bernoulli j * ((N + 1).choose j : ℚ) *
      (p : ℚ) ^ (N + 1 - j) / (N + 1) =
        _root_.bernoulli j * (N.choose j : ℚ) *
          (p : ℚ) ^ (N + 1 - j) / (((N + 1 - j : ℕ) : ℚ)) := by
    calc
      _ = _root_.bernoulli j * (p : ℚ) ^ (N + 1 - j) *
          (((N + 1).choose j : ℚ) / (N + 1)) := by ring
      _ = _ := by rw [hC]; ring
  rw [hterm, padicNorm.div, padicNorm.mul, padicNorm.mul,
    (padicNorm.nat_eq_one_iff (N + 1 - j)).mpr (Nat.not_dvd_of_pos_of_lt (by omega) hdhi), div_one]
  have hb := padicNorm_bernoulli_le_one_of_lt (p := p) (by omega : j < p - 1)
  have hc := padicNorm.of_nat (p := p) (N.choose j)
  have hpow : padicNorm p ((p : ℚ) ^ (N + 1 - j)) ≤ (p : ℚ) ^ (-3 : ℤ) := by
    rw [IsAbsoluteValue.abv_pow (padicNorm p)]
    have ht : padicNorm p (p : ℚ) = (p : ℚ)⁻¹ := padicNorm.padicNorm_p_of_prime
    rw [ht, inv_pow, ← zpow_natCast, ← zpow_neg]
    apply zpow_le_zpow_right₀ hpQ.le
    omega
  have hbc := mul_le_mul hb hc (padicNorm.nonneg _) (by norm_num : (0 : ℚ) ≤ 1)
  calc
    _ ≤ (1 : ℚ) * (p : ℚ) ^ (-3 : ℤ) :=
      mul_le_mul (by simpa only [one_mul] using hbc) hpow (padicNorm.nonneg _) (by norm_num)
    _ = _ := one_mul _

/-- The Bernoulli convolution at an odd index `d ≥ 3` has only its two endpoint terms. -/
lemma sum_bernoulli_mul_bernoulli_div_of_odd {d : ℕ} (hd : 3 ≤ d) (hodd : Odd d) :
    (∑ i ∈ range (d - 1), _root_.bernoulli (i + 1) *
      _root_.bernoulli (d - 1 - i) / (((d - 1 - i : ℕ) : ℚ))) =
        -(d : ℚ) / (2 * (d - 1)) * _root_.bernoulli (d - 1) := by
  have hsum : (∑ i ∈ ({0, d - 2} : Finset ℕ), _root_.bernoulli (i + 1) *
      _root_.bernoulli (d - 1 - i) / (((d - 1 - i : ℕ) : ℚ))) =
      ∑ i ∈ range (d - 1), _root_.bernoulli (i + 1) *
        _root_.bernoulli (d - 1 - i) / (((d - 1 - i : ℕ) : ℚ)) := Finset.sum_subset
    (by intro i hi; simp only [mem_insert, mem_singleton] at hi; rcases hi with rfl | rfl <;>
          exact mem_range.mpr (by omega))
    (by
      intro i hi hnot
      have hi' : i < d - 1 := mem_range.mp hi
      have hne : i ≠ 0 ∧ i ≠ d - 2 := by simpa only [mem_insert, mem_singleton, not_or] using hnot
      have hodd' : Odd (i + 1) ∨ Odd (d - 1 - i) := by
        have hdmod := Nat.odd_iff.mp hodd
        rw [Nat.odd_iff, Nat.odd_iff]
        omega
      rcases hodd' with ha | hb
      · rw [bernoulli_eq_zero_of_odd ha (by omega), zero_mul, zero_div]
      · rw [bernoulli_eq_zero_of_odd hb (by omega), mul_zero, zero_div])
  rw [← hsum, sum_pair (by omega : (0 : ℕ) ≠ d - 2)]
  simp only [zero_add, Nat.sub_zero, bernoulli_one,
    show d - 2 + 1 = d - 1 by omega, show d - 1 - (d - 2) = 1 by omega, Nat.cast_one, div_one]
  have hcast : ((d - 1 : ℕ) : ℚ) = d - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  rw [hcast]
  have hz : (d : ℚ) - 1 ≠ 0 := by
    have hdc : (3 : ℚ) ≤ d := by exact_mod_cast hd
    linarith
  field_simp
  ring

end Bernoulli
