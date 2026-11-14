/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.NumberTheory.Padics.PadicNorm
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Rational p-adic norm bounds

* `padicNorm.pow_div_factorial_le_one`: `pᵏ / (k + 1)!` is a p-adic integer.
* `padicNorm.pow_div_mul_succ_le_neg_two`: a bound with a consecutive integer denominator.
* `padicNorm.sum_range_pow_sub_le_of_totient_dvd`: the Fermat–Euler power sum bound.
* `Nat.multiplicity_mul_succ_le_sub_one`: the valuation bound for consecutive integers.
* `Nat.multiplicity_succ_le_sub_two`: the sharper bound for bases at least five.
* `padicNorm.pow_div_succ_le_of_multiplicity`: the higher power denominator estimate.
* `Rat.prime_pow_dvd_num_of_padicNorm_le`: a rational norm bound gives numerator divisibility.

The factorial estimate uses Mathlib's strict Legendre bound
`multiplicity_factorial_lt_of_ne_zero`.
-/

public section

open Finset
open scoped Nat

namespace Nat

/-- For `d ≥ 2`, a prime occurs in the product `d(d+1)` at most `d-1` times. -/
lemma multiplicity_mul_succ_le_sub_one {p d : ℕ} (hp : p.Prime) (hd : 2 ≤ d) :
    multiplicity p (d * (d + 1)) ≤ d - 1 := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hgrowth : d + 1 < 2 ^ d := by
    induction d, hd using Nat.le_induction with
    | base => norm_num
    | succ d _ ih =>
      rw [pow_succ]
      omega
  have hbound (x : ℕ) (hx : 0 < x) (hxd : x ≤ d + 1) : multiplicity p x ≤ d - 1 := by
    have hf : FiniteMultiplicity p x := Nat.finiteMultiplicity_iff.mpr ⟨hp.ne_one, hx⟩
    have hnot : ¬ p ^ d ∣ x := by
      intro hdiv
      have hle := Nat.le_of_dvd hx hdiv
      have hpow : 2 ^ d ≤ p ^ d := Nat.pow_le_pow_left hp.two_le d
      omega
    have := hf.multiplicity_lt_iff_not_dvd.mpr hnot
    omega
  have hf₁ : d ≠ 0 := by omega
  have hf₂ : d + 1 ≠ 0 := by omega
  rw [Nat.multiplicity_mul hf₁ hf₂]
  by_cases hpd : p ∣ d
  · have hpn : ¬ p ∣ d + 1 := by
      intro hdiv
      have : p ∣ 1 := by simpa using Nat.dvd_sub hdiv hpd
      exact hp.not_dvd_one this
    rw [multiplicity_eq_zero_of_not_dvd hpn, add_zero]
    exact hbound d (by omega) (by omega)
  · rw [multiplicity_eq_zero_of_not_dvd hpd, zero_add]
    exact hbound (d + 1) (by omega) le_rfl

/-- For `p ≥ 5` and `d ≥ 2`, the multiplicity of `p` in `d+1` is at most `d-2`. -/
lemma multiplicity_succ_le_sub_two {p d : ℕ} (hp : 5 ≤ p) (hd : 2 ≤ d) :
    multiplicity p (d + 1) ≤ d - 2 := by
  have hgrowth : d + 1 < p ^ (d - 1) := by
    induction d, hd using Nat.le_induction with
    | base => simpa using (show 3 < p by omega)
    | succ d hd ih =>
      rw [show d + 1 - 1 = (d - 1) + 1 by omega, pow_succ]
      nlinarith [Nat.one_le_pow (d - 1) p (by omega : 0 < p)]
  by_contra h
  have hdiv : p ^ (d - 1) ∣ d + 1 := pow_dvd_of_le_multiplicity (by omega)
  have hle := Nat.le_of_dvd (by omega : 0 < d + 1) hdiv
  omega

end Nat

namespace padicNorm

/-- For a prime `p`, the rational `pᵏ / (k + 1)!` is a p-adic integer. -/
lemma pow_div_factorial_le_one {p : ℕ} [Fact p.Prime] (k : ℕ) :
    padicNorm p ((p : ℚ) ^ k / ((k + 1) ! : ℚ)) ≤ 1 := by
  have hv : multiplicity p ((k + 1) !) ≤ k :=
    Nat.le_of_lt_succ (multiplicity_factorial_lt_of_ne_zero p (by omega))
  rw [padicNorm.div, padicNorm.eq_zpow_of_ne_zero (by positivity : ((k + 1) ! : ℚ) ≠ 0),
    padicValRat.of_nat]
  have hpow : padicNorm p ((p : ℚ) ^ k) = (p : ℚ) ^ (-(k : ℤ)) := by
    have ht : padicNorm p (p : ℚ) = (p : ℚ)⁻¹ := padicNorm.padicNorm_p_of_prime
    rw [IsAbsoluteValue.abv_pow (padicNorm p), ht, inv_pow, zpow_neg, zpow_natCast]
  rw [hpow, ← zpow_sub₀ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)]
  exact zpow_le_one_of_nonpos₀ (by exact_mod_cast (Fact.out : p.Prime).one_le) (by omega)

/-- For a prime `p` and `d ≥ 2`, the rational `p^(d+1) / (d(d+1))` has
p-adic norm at most `p⁻²`. -/
lemma pow_div_mul_succ_le_neg_two {p d : ℕ} [Fact p.Prime] (hd : 2 ≤ d) :
    padicNorm p ((p : ℚ) ^ (d + 1) / ((d : ℚ) * (d + 1))) ≤ (p : ℚ) ^ (-2 : ℤ) := by
  have hp : p.Prime := Fact.out
  have hv := Nat.multiplicity_mul_succ_le_sub_one hp hd
  have hden : (((d * (d + 1) : ℕ) : ℚ)) ≠ 0 := by positivity
  rw [show (d : ℚ) * (d + 1) = ((d * (d + 1) : ℕ) : ℚ) by push_cast; rfl,
    padicNorm.div, padicNorm.eq_zpow_of_ne_zero hden, padicValRat.of_nat]
  have hpow : padicNorm p ((p : ℚ) ^ (d + 1)) = (p : ℚ) ^ (-((d + 1 : ℕ) : ℤ)) := by
    rw [IsAbsoluteValue.abv_pow (padicNorm p), padicNorm.padicNorm_p_of_prime, inv_pow, zpow_neg,
      zpow_natCast]
  rw [hpow, ← zpow_sub₀ (by exact_mod_cast hp.ne_zero)]
  apply zpow_le_zpow_right₀ (by exact_mod_cast hp.one_le)
  omega

/-- If a positive exponent is divisible by `(p - 1)p^ℓ`, the sum of its powers
over the residues modulo `p` is congruent to `p - 1` modulo `p^(ℓ+1)`. -/
lemma sum_range_pow_sub_le_of_totient_dvd {p N ℓ : ℕ} [Fact p.Prime] (hN : 1 ≤ N)
    (hdvd : (p - 1) * p ^ ℓ ∣ N) :
    padicNorm p ((∑ k ∈ range p, (k : ℚ) ^ N) - (p - 1 : ℚ)) ≤
      (p : ℚ) ^ (-((ℓ + 1 : ℕ) : ℤ)) := by
  have hp : p.Prime := Fact.out
  have hp2 := hp.two_le
  let M := p ^ (ℓ + 1)
  have hpow (j : ℕ) (hj : 1 ≤ j) (hjp : j < p) : (j : ZMod M) ^ N = 1 := by
    have hc : j.Coprime M := ((hp.coprime_iff_not_dvd).mpr
      (Nat.not_dvd_of_pos_of_lt (by omega) hjp)).symm.pow_right (ℓ + 1)
    obtain ⟨a, ha⟩ := hdvd
    have hN : N = M.totient * a := by
      dsimp only [M]
      rw [Nat.totient_prime_pow hp (by omega), show ℓ + 1 - 1 = ℓ by omega,
        mul_comm (p ^ ℓ)]
      exact ha
    have ht := (Nat.ModEq.pow_totient hc).pow a
    rw [← pow_mul, ← hN, one_pow] at ht
    simpa only [Nat.cast_pow, Nat.cast_one] using (ZMod.natCast_eq_natCast_iff _ _ _).mpr ht
  have hsum : (∑ j ∈ range p, (j : ZMod M) ^ N) = (p : ZMod M) - 1 := by
    rw [show p = (p - 1) + 1 by omega, sum_range_succ']
    simp only [Nat.cast_zero, zero_pow (by omega : N ≠ 0), add_zero]
    have he : ∀ j ∈ range (p - 1), ((j + 1 : ℕ) : ZMod M) ^ N = 1 :=
      fun j hj => hpow (j + 1) (by omega) (by have := mem_range.mp hj; omega)
    rw [sum_congr rfl he, sum_const, card_range, nsmul_eq_mul, mul_one,
      Nat.cast_sub hp.one_le, Nat.cast_one]
    rw [Nat.sub_add_cancel hp.one_le]
  have hdiv : ((p : ℤ) ^ (ℓ + 1)) ∣ (∑ j ∈ range p, (j : ℤ) ^ N) - (p - 1 : ℤ) := by
    have hz : (((∑ j ∈ range p, (j : ℤ) ^ N) - (p - 1 : ℤ) : ℤ) : ZMod M) = 0 := by
      push_cast
      exact sub_eq_zero.mpr hsum
    have hdiv := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
    simpa only [M, Nat.cast_pow] using hdiv
  have hnorm := (padicNorm.dvd_iff_norm_le (p := p) (n := ℓ + 1)
    (z := (∑ j ∈ range p, (j : ℤ) ^ N) - (p - 1 : ℤ))).mp (by
      simpa only [Nat.cast_pow] using hdiv)
  simpa only [Int.cast_sub, Int.cast_sum, Int.cast_pow, Int.cast_natCast, Int.cast_one] using hnorm

/-- A multiplicity bound on `d+1` controls the p-adic norm of
`M^(d+1)/(d+1)` when `p ∣ M`. -/
lemma pow_div_succ_le_of_multiplicity {p M d r : ℕ} [Fact p.Prime] (hM : 1 ≤ M) (hpM : p ∣ M)
    (hd : 2 ≤ d) (hv : multiplicity p (d + 1) + r ≤ d - 1) :
    padicNorm p ((M : ℚ) ^ (d + 1) / (d + 1)) ≤
      (padicNorm p (M : ℚ)) ^ 2 / (p : ℚ) ^ r := by
  have hp : p.Prime := Fact.out
  have hM0 : (M : ℚ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  have hd0 : (d + 1 : ℚ) ≠ 0 := by positivity
  have he : 1 ≤ multiplicity p M := by
    have hf : FiniteMultiplicity p M := Nat.finiteMultiplicity_iff.mpr ⟨hp.ne_one, by omega⟩
    exact hf.le_multiplicity_of_pow_dvd (by simpa only [pow_one] using hpM)
  rw [padicNorm.div, IsAbsoluteValue.abv_pow (padicNorm p),
    padicNorm.eq_zpow_of_ne_zero hM0, padicValRat.of_nat,
    padicNorm.eq_zpow_of_ne_zero hd0]
  have hvd : padicValRat p (d + 1 : ℚ) = multiplicity p (d + 1) := by
    norm_cast
  rw [hvd, ← zpow_natCast, ← zpow_mul, ← zpow_natCast, ← zpow_mul, ← zpow_natCast,
    ← zpow_sub₀ (by exact_mod_cast hp.ne_zero), ← zpow_sub₀ (by exact_mod_cast hp.ne_zero)]
  apply zpow_le_zpow_right₀ (by exact_mod_cast hp.one_le)
  have hpos : (1 : ℤ) ≤ multiplicity p M := by exact_mod_cast he
  have hval : (multiplicity p (d + 1) : ℤ) + r ≤ d - 1 := by omega
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
  nlinarith

end padicNorm

namespace Rat

/-- A rational with p-adic norm at most `p⁻ℓ` has numerator divisible by `p^ℓ`. -/
lemma prime_pow_dvd_num_of_padicNorm_le {p : ℕ} [Fact p.Prime] {q : ℚ} {ℓ : ℕ}
    (hq : padicNorm p q ≤ (p : ℚ) ^ (-(ℓ : ℤ))) : (p : ℤ) ^ ℓ ∣ q.num := by
  have hn : padicNorm p (q.num : ℚ) ≤ (p : ℚ) ^ (-(ℓ : ℤ)) := by
    rw [← Rat.mul_den_eq_num, padicNorm.mul]
    calc
      _ ≤ padicNorm p q * 1 :=
        mul_le_mul_of_nonneg_left (padicNorm.of_nat q.den) (padicNorm.nonneg _)
      _ ≤ _ := by simpa only [mul_one] using hq
  simpa only [Nat.cast_pow] using (padicNorm.dvd_iff_norm_le.mpr hn)

end Rat
