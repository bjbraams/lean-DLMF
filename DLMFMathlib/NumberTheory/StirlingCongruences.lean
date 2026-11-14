/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.NumberTheory.Padics.PadicNorm
public import Mathlib.NumberTheory.Bernoulli
import DLMFMathlib.NumberTheory.BernoulliCongruences
import DLMFMathlib.Combinatorics.StirlingPowerSums
import DLMFMathlib.NumberTheory.PowerSums
import Mathlib.Tactic

/-!
# Prime congruences for Stirling numbers

The Newton identity and Fermat power sum divisibility show that `S(p-1+d,p-1)`
is divisible by `p` for `1 ≤ d ≤ p-2`. A second application identifies `d` times
this number modulo `p²` with the `d`th power sum of the residues.

* `Nat.prime_dvd_stirlingSecond_add`: divisibility by `p`.
* `padicNorm.mul_stirlingSecond_sub_sum_pow_le`: the power sum congruence modulo `p²`.
* `padicNorm.stirlingSecond_sub_prime_mul_bernoulli_div_le`: Bernoulli congruence modulo `p²`.
* `padicNorm.stirlingSecond_sub_prime_sq_mul_bernoulli_le_of_odd`: odd-index congruence
  modulo `p³`.

The proof uses Mathlib's prime divisibility and p-adic norm APIs, with the formal Newton
identity in `DLMFMathlib.Combinatorics.StirlingPowerSums`.
-/

public noncomputable section

open Finset
open scoped Nat

namespace Nat

/-- The number `S(p-1+d,p-1)` is divisible by the prime `p` when `1 ≤ d ≤ p-2`. -/
lemma prime_dvd_stirlingSecond_add {p d : ℕ} (hp : p.Prime) (hd : 1 ≤ d) (hdp : d ≤ p - 2) :
    p ∣ Nat.stirlingSecond (p - 1 + d) (p - 1) := by
  let _ : Fact p.Prime := ⟨hp⟩
  have h := congrArg (fun t : ℕ => (t : ℚ))
    (Nat.mul_stirlingSecond_add_eq_sum_pow (p - 1) (d - 1))
  push_cast at h
  rw [Nat.sub_add_cancel hd, Nat.sub_add_cancel hp.one_le] at h
  have hdq : (((d - 1 : ℕ) : ℚ) + 1) = (d : ℚ) := by exact_mod_cast Nat.sub_add_cancel hd
  rw [hdq] at h
  have hZ : (d : ℤ) * (Nat.stirlingSecond (p - 1 + d) (p - 1) : ℤ) =
      ∑ i ∈ Finset.range d, (∑ j ∈ Finset.range p, (j : ℤ) ^ (i + 1)) *
        (Nat.stirlingSecond (p - 1 + (d - 1 - i)) (p - 1) : ℤ) := by exact_mod_cast h
  have hdiv : (p : ℤ) ∣ (d : ℤ) * (Nat.stirlingSecond (p - 1 + d) (p - 1) : ℤ) := by
    rw [hZ]
    apply Finset.dvd_sum
    intro i hi
    have hi' : i < d := Finset.mem_range.mp hi
    have hs := Int.prime_pow_dvd_sum_range_pow (p := p) (N := i + 1) (ℓ := 0)
      hp (by simp) (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
    exact dvd_mul_of_dvd_left (by simpa only [zero_add, pow_one] using hs) _
  have hpz : _root_.Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  rcases hpz.dvd_or_dvd hdiv with hpd | hps
  · have : p ∣ d := by exact_mod_cast hpd
    exact False.elim ((Nat.not_dvd_of_pos_of_lt (by omega) (by omega)) this)
  · exact_mod_cast hps

end Nat

namespace padicNorm

/-- The difference between `d S(p-1+d,p-1)` and the `d`th power sum of the residues
has p-adic norm at most `p⁻²` for `1 ≤ d ≤ p-2`. -/
lemma mul_stirlingSecond_sub_sum_pow_le {p d : ℕ} (hp : p.Prime)
    (hd : 1 ≤ d) (hdp : d ≤ p - 2) :
    padicNorm p ((d : ℚ) * Nat.stirlingSecond (p - 1 + d) (p - 1) -
      (∑ j ∈ Finset.range p, (j : ℚ) ^ d)) ≤ (p : ℚ) ^ (-2 : ℤ) := by
  let _ : Fact p.Prime := ⟨hp⟩
  have h := congrArg (fun t : ℕ => (t : ℚ))
    (Nat.mul_stirlingSecond_add_eq_sum_pow (p - 1) (d - 1))
  push_cast at h
  rw [Nat.sub_add_cancel hd, Nat.sub_add_cancel hp.one_le] at h
  have hdq : (((d - 1 : ℕ) : ℚ) + 1) = (d : ℚ) := by exact_mod_cast Nat.sub_add_cancel hd
  rw [hdq] at h
  have hsplit := Finset.sum_range_succ
    (fun i => (∑ j ∈ Finset.range p, (j : ℚ) ^ (i + 1)) *
      (Nat.stirlingSecond (p - 1 + (d - 1 - i)) (p - 1) : ℚ)) (d - 1)
  rw [Nat.sub_add_cancel hd] at hsplit
  simp only [Nat.sub_self, Nat.add_zero, Nat.stirlingSecond_self, Nat.cast_one, mul_one] at hsplit
  rw [hsplit] at h
  have hZ : (d : ℤ) * (Nat.stirlingSecond (p - 1 + d) (p - 1) : ℤ) -
      (∑ j ∈ Finset.range p, (j : ℤ) ^ d) =
      ∑ i ∈ Finset.range (d - 1), (∑ j ∈ Finset.range p, (j : ℤ) ^ (i + 1)) *
        (Nat.stirlingSecond (p - 1 + (d - 1 - i)) (p - 1) : ℤ) := by
    have hz : (d : ℤ) * (Nat.stirlingSecond (p - 1 + d) (p - 1) : ℤ) =
      (∑ i ∈ Finset.range (d - 1), (∑ j ∈ Finset.range p, (j : ℤ) ^ (i + 1)) *
        (Nat.stirlingSecond (p - 1 + (d - 1 - i)) (p - 1) : ℤ)) +
          (∑ j ∈ Finset.range p, (j : ℤ) ^ d) := by exact_mod_cast h
    linarith
  have hdiv : (p : ℤ) ^ 2 ∣ (d : ℤ) *
      (Nat.stirlingSecond (p - 1 + d) (p - 1) : ℤ) - (∑ j ∈ Finset.range p, (j : ℤ) ^ d) := by
    rw [hZ]
    apply Finset.dvd_sum
    intro i hi
    have hi' : i < d - 1 := Finset.mem_range.mp hi
    have hs : (p : ℤ) ∣ (∑ j ∈ Finset.range p, (j : ℤ) ^ (i + 1)) := by
      have h := Int.prime_pow_dvd_sum_range_pow (p := p) (N := i + 1) (ℓ := 0)
        hp (by simp) (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
      simpa only [zero_add, pow_one] using h
    have ht : (p : ℤ) ∣ (Nat.stirlingSecond (p - 1 + (d - 1 - i)) (p - 1) : ℤ) := by
      exact_mod_cast Nat.prime_dvd_stirlingSecond_add hp (by omega : 1 ≤ d - 1 - i) (by omega)
    simpa only [pow_two] using mul_dvd_mul hs ht
  have hn := (padicNorm.dvd_iff_norm_le (p := p) (n := 2)
    (z := (d : ℤ) * (Nat.stirlingSecond (p - 1 + d) (p - 1) : ℤ) -
      (∑ j ∈ Finset.range p, (j : ℤ) ^ d))).mp (by simpa only [Nat.cast_pow] using hdiv)
  simpa only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_sum, Int.cast_pow,
    Nat.cast_ofNat] using hn

/-- The Stirling number `S(p-1+n,p-1)` equals `p B_n/n` modulo `p²` for `1 ≤ n ≤ p-2`. -/
lemma stirlingSecond_sub_prime_mul_bernoulli_div_le {p n : ℕ} [Fact p.Prime]
    (hn : 1 ≤ n) (hnp : n ≤ p - 2) :
    padicNorm p ((Nat.stirlingSecond (p - 1 + n) (p - 1) : ℚ) -
      p * _root_.bernoulli n / n) ≤ (p : ℚ) ^ (-2 : ℤ) := by
  have hp : p.Prime := Fact.out
  have hnunit : padicNorm p (n : ℚ) = 1 :=
    (padicNorm.nat_eq_one_iff n).mpr (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
  have h₁ := padicNorm.mul_stirlingSecond_sub_sum_pow_le hp hn hnp
  have h₂ := Bernoulli.padicNorm_sum_range_pow_sub_prime_mul_bernoulli_le (p := p) hn hnp
  have h : padicNorm p ((n : ℚ) * Nat.stirlingSecond (p - 1 + n) (p - 1) -
      p * _root_.bernoulli n) ≤ (p : ℚ) ^ (-2 : ℤ) := by
    have he : ((n : ℚ) * Nat.stirlingSecond (p - 1 + n) (p - 1) - p * _root_.bernoulli n) =
        ((n : ℚ) * Nat.stirlingSecond (p - 1 + n) (p - 1) - ∑ j ∈ range p, (j : ℚ) ^ n) +
          ((∑ j ∈ range p, (j : ℚ) ^ n) - p * _root_.bernoulli n) := by ring
    rw [he]
    exact padicNorm.nonarchimedean.trans (max_le h₁ h₂)
  have hn0 : (n : ℚ) ≠ 0 := by positivity
  have he : (Nat.stirlingSecond (p - 1 + n) (p - 1) : ℚ) - p * _root_.bernoulli n / n =
      (((n : ℚ) * Nat.stirlingSecond (p - 1 + n) (p - 1) - p * _root_.bernoulli n) / n) := by
    field_simp
  rw [he, padicNorm.div, hnunit, div_one]
  exact h

/-- The Stirling number `S(p-1+d,p-1)` has norm at most `p⁻¹` for `1 ≤ d ≤ p-2`. -/
lemma stirlingSecond_le_inv {p d : ℕ} [Fact p.Prime] (hd : 1 ≤ d) (hdp : d ≤ p - 2) :
    padicNorm p (Nat.stirlingSecond (p - 1 + d) (p - 1) : ℚ) ≤ (p : ℚ)⁻¹ := by
  have h := Nat.prime_dvd_stirlingSecond_add (Fact.out : p.Prime) hd hdp
  have hZ : ((p ^ 1 : ℕ) : ℤ) ∣ (Nat.stirlingSecond (p - 1 + d) (p - 1) : ℤ) := by
    simpa only [pow_one] using Int.natCast_dvd_natCast.mpr h
  simpa only [Int.cast_natCast, Nat.cast_one, zpow_neg_one] using padicNorm.dvd_iff_norm_le.mp hZ

/-- A product of a residue power sum and a Stirling number equals the corresponding
Bernoulli product modulo `p³`. -/
lemma sum_pow_mul_stirlingSecond_sub_prime_sq_mul_bernoulli_le {p a b : ℕ} [Fact p.Prime]
    (ha : 1 ≤ a) (hap : a ≤ p - 2) (hb : 1 ≤ b) (hbp : b ≤ p - 2) :
    padicNorm p ((∑ j ∈ range p, (j : ℚ) ^ a) *
      (Nat.stirlingSecond (p - 1 + b) (p - 1) : ℚ) -
      (p : ℚ) ^ 2 * _root_.bernoulli a * _root_.bernoulli b / b) ≤ (p : ℚ) ^ (-3 : ℤ) := by
  have h₁ := Bernoulli.padicNorm_sum_range_pow_sub_prime_mul_bernoulli_le (p := p) ha hap
  have h₂ := stirlingSecond_sub_prime_mul_bernoulli_div_le (p := p) hb hbp
  have hS := stirlingSecond_le_inv (p := p) hb hbp
  have hB : padicNorm p ((p : ℚ) * _root_.bernoulli a) ≤ (p : ℚ)⁻¹ := by
    rw [padicNorm.mul, padicNorm.padicNorm_p_of_prime]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (Bernoulli.padicNorm_bernoulli_le_one_of_lt (p := p) (by omega : a < p - 1))
      (by positivity : (0 : ℚ) ≤ (p : ℚ)⁻¹)
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have he : (∑ j ∈ range p, (j : ℚ) ^ a) *
      (Nat.stirlingSecond (p - 1 + b) (p - 1) : ℚ) -
      (p : ℚ) ^ 2 * _root_.bernoulli a * _root_.bernoulli b / b =
      ((∑ j ∈ range p, (j : ℚ) ^ a) - p * _root_.bernoulli a) *
        (Nat.stirlingSecond (p - 1 + b) (p - 1) : ℚ) +
      ((p : ℚ) * _root_.bernoulli a) *
        ((Nat.stirlingSecond (p - 1 + b) (p - 1) : ℚ) -
          p * _root_.bernoulli b / b) := by ring
  rw [he]
  apply padicNorm.nonarchimedean.trans
  apply max_le
  · rw [padicNorm.mul]
    calc
      _ ≤ (p : ℚ) ^ (-2 : ℤ) * (p : ℚ)⁻¹ :=
        mul_le_mul h₁ hS (padicNorm.nonneg _) (by positivity)
      _ = _ := by rw [← zpow_neg_one, ← zpow_add₀ hp0]; norm_num
  · rw [padicNorm.mul]
    calc
      _ ≤ (p : ℚ)⁻¹ * (p : ℚ) ^ (-2 : ℤ) :=
        mul_le_mul hB h₂ (padicNorm.nonneg _) (by positivity)
      _ = _ := by rw [← zpow_neg_one, ← zpow_add₀ hp0]; norm_num

/-- At an odd index `3 ≤ d ≤ p-2`, the Stirling number `S(p-1+d,p-1)` has an explicit
Bernoulli approximation modulo `p³`. -/
lemma stirlingSecond_sub_prime_sq_mul_bernoulli_le_of_odd {p d : ℕ} [Fact p.Prime]
    (hd : 3 ≤ d) (hdp : d ≤ p - 2)
    (hodd : Odd d) :
    padicNorm p ((Nat.stirlingSecond (p - 1 + d) (p - 1) : ℚ) -
      ((d : ℚ) - 2) / (2 * (d - 1)) * p ^ 2 * _root_.bernoulli (d - 1)) ≤
        (p : ℚ) ^ (-3 : ℤ) := by
  have hp : p.Prime := Fact.out
  have h := congrArg (fun t : ℕ => (t : ℚ))
    (Nat.mul_stirlingSecond_add_eq_sum_pow (p - 1) (d - 1))
  push_cast at h
  rw [Nat.sub_add_cancel (by omega : 1 ≤ d), Nat.sub_add_cancel hp.one_le] at h
  have hdq : (((d - 1 : ℕ) : ℚ) + 1) = (d : ℚ) := by
    exact_mod_cast Nat.sub_add_cancel (by omega : 1 ≤ d)
  rw [hdq] at h
  have hsplit := Finset.sum_range_succ
    (fun i => (∑ j ∈ range p, (j : ℚ) ^ (i + 1)) *
      (Nat.stirlingSecond (p - 1 + (d - 1 - i)) (p - 1) : ℚ)) (d - 1)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ d)] at hsplit
  simp only [Nat.sub_self, Nat.add_zero, Nat.stirlingSecond_self, Nat.cast_one, mul_one] at hsplit
  rw [hsplit] at h
  have hpower := Bernoulli.padicNorm_sum_range_pow_sub_two_terms_le (p := p) (by omega : 2 ≤ d) hdp
  rw [bernoulli_eq_zero_of_odd hodd (by omega), mul_zero, sub_zero] at hpower
  have herr : padicNorm p (∑ i ∈ range (d - 1),
      ((∑ j ∈ range p, (j : ℚ) ^ (i + 1)) *
        (Nat.stirlingSecond (p - 1 + (d - 1 - i)) (p - 1) : ℚ) -
        (p : ℚ) ^ 2 * _root_.bernoulli (i + 1) *
          _root_.bernoulli (d - 1 - i) / (((d - 1 - i : ℕ) : ℚ)))) ≤ (p : ℚ) ^ (-3 : ℤ) := by
    apply padicNorm.sum_le' _ (by positivity)
    intro i hi
    have hi' : i < d - 1 := mem_range.mp hi
    exact sum_pow_mul_stirlingSecond_sub_prime_sq_mul_bernoulli_le (p := p)
      (by omega) (by omega) (by omega) (by omega)
  have hsum : (∑ i ∈ range (d - 1), (p : ℚ) ^ 2 * _root_.bernoulli (i + 1) *
      _root_.bernoulli (d - 1 - i) / (((d - 1 - i : ℕ) : ℚ))) =
        (p : ℚ) ^ 2 * (-(d : ℚ) / (2 * (d - 1)) * _root_.bernoulli (d - 1)) := by
    rw [← Bernoulli.sum_bernoulli_mul_bernoulli_div_of_odd hd hodd, mul_sum]
    apply sum_congr rfl
    intro i _
    ring
  rw [sum_sub_distrib, hsum] at herr
  have he : (d : ℚ) * ((Nat.stirlingSecond (p - 1 + d) (p - 1) : ℚ) -
      ((d : ℚ) - 2) / (2 * (d - 1)) * p ^ 2 * _root_.bernoulli (d - 1)) =
      ((∑ j ∈ range p, (j : ℚ) ^ d) - d * (p : ℚ) ^ 2 / 2 * _root_.bernoulli (d - 1)) +
      ((∑ i ∈ range (d - 1), (∑ j ∈ range p, (j : ℚ) ^ (i + 1)) *
        (Nat.stirlingSecond (p - 1 + (d - 1 - i)) (p - 1) : ℚ)) -
        (p : ℚ) ^ 2 * (-(d : ℚ) / (2 * (d - 1)) * _root_.bernoulli (d - 1))) := by
    have hd0 : (d : ℚ) - 1 ≠ 0 := by
      have hdc : (3 : ℚ) ≤ d := by exact_mod_cast hd
      linarith
    rw [mul_sub, h]
    field_simp
    ring
  have hnorm : padicNorm p ((d : ℚ) *
      ((Nat.stirlingSecond (p - 1 + d) (p - 1) : ℚ) -
        ((d : ℚ) - 2) / (2 * (d - 1)) * p ^ 2 * _root_.bernoulli (d - 1))) ≤
          (p : ℚ) ^ (-3 : ℤ) := by
    rw [he]
    exact padicNorm.nonarchimedean.trans (max_le hpower herr)
  rw [padicNorm.mul,
    (padicNorm.nat_eq_one_iff d).mpr
      (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)), one_mul] at hnorm
  exact hnorm

end padicNorm
