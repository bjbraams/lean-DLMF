/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.BernoulliEuler.Explicit
import DLMFMathlib.NumberTheory.EulerCongruences
import DLMFMathlib.NumberTheory.BernoulliCongruences
import DLMFMathlib.NumberTheory.BernoulliRegularization
import DLMFMathlib.NumberTheory.BernoulliMoments
import DLMFMathlib.NumberTheory.PadicPolynomial
import Mathlib.FieldTheory.Finite.Basic
import DLMFMathlib.NumberTheory.PadicNorm
import DLMFMathlib.NumberTheory.PowerSums
import DLMFMathlib.Algebra.BigOperators
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Bernoulli and Euler numbers: arithmetic properties

This file covers DLMF §24.10: congruences for the Bernoulli and Euler numbers. DLMF §24.10(i)
calls two rational numbers congruent if the modulus divides the numerator of their difference;
this is `RatModEq M a b`.

## Main definitions

* `RatModEq`: congruence of rational numbers (DLMF §24.10(i)).

## Main results

* `bernoulli_two_mul_den_eq_prod`: the denominator of `B₂ₙ` is the product of the primes `p`
  with `p - 1 ∣ 2n` (second assertion of DLMF 24.10.1).
* `prime_mul_bernoulli_two_mul_modEq`: DLMF 24.10.2.
* `kummer_congruence`, `kummer_congruence_pow`: Kummer's congruences (DLMF 24.10.3, 24.10.4).
* `eulerNumber_modEq_add_prime_sub_one`, `eulerNumber_two_mul_modEq_two_pow`:
  DLMF 24.10.5, 24.10.6.
* `voronoi_congruence`: Voronoi's congruence (DLMF 24.10.7).
* `prime_pow_dvd_bernoulli_num`, `eulerNumber_two_mul_modEq_prime_pow`: DLMF 24.10.8, 24.10.9.

## Implementation notes

The von Staudt–Clausen theorem (first assertion of 24.10.1) is Mathlib's
`Bernoulli.vonStaudt_clausen` (pointer in `DLMF.BernoulliEuler.MathlibCoverage`).

Corrections to DLMF:

* Kummer's congruence 24.10.3 fails if `m = 1` or `n = 1` (e.g. `p = 3`, `m = 1`, `n = 3`:
  `B₁/1 = -1/2 ≢ 0 = B₃/3 (mod 3)`); it is stated for `m, n ≥ 2`. 24.10.4 needs no such
  condition (its factor `1 - p⁰` vanishes for `m = 1`).
* 24.10.5 also holds for `n = 1` (`E₁ = Eₚ = 0`), but not for `n = 0`; it is stated as printed
  (`n ≥ 2`).

The proof of 24.10.9 uses Mathlib’s Euler polynomial addition formula and Fermat–Euler
theorem `Nat.ModEq.pow_totient`.

All congruences were checked in exact arithmetic for primes `p ≤ 13` and the index ranges
`m, n < 60` (24.10.3–24.10.4), `n < 200` (24.10.2), `n < 150` (24.10.8–24.10.9), `M < 12`,
`|b| ≤ 7` (24.10.7).
-/

@[expose] public section

noncomputable section

open Finset Filter
open scoped Nat Polynomial Topology

namespace DLMF.BernoulliEuler

/-- Congruence of rational numbers in DLMF §24.10: `a ≡ b (mod M)` when `M` divides the
numerator of `a - b`. -/
@[dlmf 24.10.i]
def RatModEq (M : ℤ) (a b : ℚ) : Prop := M ∣ (a - b).num

/-! ### §24.10(i) Von Staudt–Clausen theorem -/

/-- The denominator of `∑_{p ∈ s} 1/p` divides `∏_{p ∈ s} p`. -/
private lemma den_sum_one_div_dvd_prod (s : Finset ℕ) :
    (∑ p ∈ s, (1 : ℚ) / p).den ∣ ∏ p ∈ s, p := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [sum_insert ha, prod_insert ha]
    refine (Rat.add_den_dvd _ _).trans (Nat.mul_dvd_mul ?_ ih)
    rcases Nat.eq_zero_or_pos a with rfl | h
    · simp
    · rw [one_div, Rat.inv_natCast_den]; simp [h.ne']

/-- **DLMF 24.10.1** (second assertion): for `n ≥ 1` the denominator of `B₂ₙ` is the product of
the primes `p` with `p - 1 ∣ 2n` (all such primes are `≤ 2n + 1`). -/
@[dlmf 24.10.E1]
theorem bernoulli_two_mul_den_eq_prod {n : ℕ} (hn : 1 ≤ n) :
    (bernoulli (2 * n)).den = ∏ p ∈ range (2 * n + 2) with p.Prime ∧ (p - 1) ∣ 2 * n, p := by
  obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen n
  set T := (range (2 * n + 2)).filter (fun p => p.Prime ∧ (p - 1) ∣ 2 * n)
  have hB : bernoulli (2 * n) = (z : ℚ) + -∑ p ∈ T, (1 : ℚ) / p := by linarith
  refine Nat.dvd_antisymm ?_ ?_
  · rw [hB, Rat.intCast_add_den, Rat.den_neg_eq_den]
    exact den_sum_one_div_dvd_prod T
  · refine Finset.prod_primes_dvd _ (fun p hp => (mem_filter.mp hp).2.1.prime) fun p hp => ?_
    have hp' := (mem_filter.mp hp).2
    have : Fact p.Prime := ⟨hp'.1⟩
    exact Bernoulli.dvd_den_bernoulli (by omega) hp'.2

/-- The congruence `p B₂ₙ ≡ p - 1 (mod p^(ℓ+1))` also holds for `ℓ = 0`;
stronger than DLMF, which assumes `ℓ ≥ 1`. -/
@[dlmf 24.10.E2 "stronger than DLMF: includes ℓ = 0"]
theorem prime_mul_bernoulli_two_mul_modEq' {p : ℕ} (hp : p.Prime) {n ℓ : ℕ} (hn : 2 ≤ n)
    (hdvd : (p - 1) * p ^ ℓ ∣ 2 * n) :
    RatModEq ((p : ℤ) ^ (ℓ + 1))
      (p * bernoulli (2 * n)) (p - 1) := by
  let _ : Fact p.Prime := ⟨hp⟩
  apply Rat.prime_pow_dvd_num_of_padicNorm_le
  have hsum := padicNorm.sum_range_pow_sub_le_of_totient_dvd (p := p) (N := 2 * n) (by omega) hdvd
  have hrest := Bernoulli.padicNorm_prime_mul_bernoulli_sub_sum_pow_le (p := p) (N := 2 * n)
    (by omega) (even_two_mul n)
  have hindex : padicNorm p ((2 * n : ℕ) : ℚ) ≤ (p : ℚ) ^ (-(ℓ : ℤ)) := by
    have hd : p ^ ℓ ∣ 2 * n := dvd_trans (dvd_mul_left _ _) hdvd
    have hdz : ((p ^ ℓ : ℕ) : ℤ) ∣ (2 * n : ℕ) := by exact_mod_cast hd
    exact_mod_cast padicNorm.dvd_iff_norm_le.mp hdz
  have hrest' : padicNorm p ((p : ℚ) * bernoulli (2 * n) -
      ∑ k ∈ range p, (k : ℚ) ^ (2 * n)) ≤ (p : ℚ) ^ (-((ℓ + 1 : ℕ) : ℤ)) := by
    calc
      _ ≤ padicNorm p ((2 * n : ℕ) : ℚ) / p := hrest
      _ ≤ (p : ℚ) ^ (-(ℓ : ℤ)) / p := div_le_div_of_nonneg_right hindex (by positivity)
      _ = _ := by
        have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
        rw [show -((ℓ + 1 : ℕ) : ℤ) = -(ℓ : ℤ) - 1 by omega, zpow_sub₀ hp0, zpow_one]
  have he : (p : ℚ) * bernoulli (2 * n) - (p - 1) =
      ((p : ℚ) * bernoulli (2 * n) - ∑ k ∈ range p, (k : ℚ) ^ (2 * n)) +
        ((∑ k ∈ range p, (k : ℚ) ^ (2 * n)) - (p - 1)) := by ring
  rw [he]
  exact padicNorm.nonarchimedean.trans (max_le hrest' hsum)

/-- **DLMF 24.10.2**: `p B₂ₙ ≡ p - 1 (mod p^{ℓ+1})` for `n ≥ 2`, `ℓ ≥ 1`, `(p-1)p^ℓ ∣ 2n`. -/
@[dlmf 24.10.E2]
theorem prime_mul_bernoulli_two_mul_modEq {p : ℕ} (hp : p.Prime) {n ℓ : ℕ} (hn : 2 ≤ n)
    (hℓ : 1 ≤ ℓ) (hdvd : (p - 1) * p ^ ℓ ∣ 2 * n) :
    RatModEq ((p : ℤ) ^ (ℓ + 1)) (p * bernoulli (2 * n)) (p - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hℓ
  exact prime_mul_bernoulli_two_mul_modEq' hp hn hdvd

/-! ### §24.10(ii) Kummer congruences -/

/-- **Kummer's congruence, DLMF 24.10.3** (corrected: `m, n ≥ 2`):
`Bₘ/m ≡ Bₙ/n (mod p)` for `m ≡ n ≢ 0 (mod p - 1)`. -/
@[dlmf 24.10.E3]
theorem kummer_congruence {p : ℕ} (hp : p.Prime) {m n : ℕ} (hm : 2 ≤ m) (hn2 : 2 ≤ n)
    (hmn : m ≡ n [MOD p - 1]) (hn : ¬ (p - 1) ∣ n) :
    RatModEq p (bernoulli m / m) (bernoulli n / n) := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hnot : ¬ ∀ u : (ZMod p)ˣ, u ^ n = 1 := by
    intro hu
    have h := (FiniteField.forall_pow_eq_one_iff (ZMod p) n).mp hu
    exact hn (by simpa only [ZMod.card] using h)
  push Not at hnot
  obtain ⟨u, hu⟩ := hnot
  let a : ℕ := (u : ZMod p).val
  have ha : (a : ZMod p) = u := ZMod.natCast_zmod_val _
  have hap : ¬ p ∣ a := by
    intro hd
    have hz : (a : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hd
    rw [ha] at hz
    exact u.ne_zero hz
  have hepow : (a : ZMod p) ^ m = (a : ZMod p) ^ n :=
    pow_eq_pow_of_modEq hmn (ZMod.pow_card_sub_one_eq_one (by rw [ha]; exact u.ne_zero))
  have hunit (r : ℕ) (hr : r = m ∨ r = n) : padicNorm p (1 - (a : ℚ) ^ r) = 1 := by
    have hnot : ¬ (p : ℤ) ∣ (1 - (a : ℤ) ^ r) := by
      intro hd
      have hz : ((1 - (a : ℤ) ^ r : ℤ) : ZMod p) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hd
      have he : (a : ZMod p) ^ r = 1 := by
        push_cast at hz
        linear_combination -hz
      rcases hr with rfl | rfl
      · rw [hepow, ha] at he
        exact hu (Units.ext he)
      · rw [ha] at he
        exact hu (Units.ext he)
    have h := (padicNorm.int_eq_one_iff (p := p) (1 - (a : ℤ) ^ r)).mpr hnot
    simpa only [Int.cast_sub, Int.cast_one, Int.cast_pow, Int.cast_natCast] using h
  obtain ⟨L, hLX, hLav⟩ := Polynomial.exists_linearMap_pow_eq_regularized_bernoulli (K := ℚ) a
  have hbase (k : ℕ) : padicNorm p (L (Ring.choose (Polynomial.X : ℚ[X]) k)) ≤ 1 := by
    simpa only [Nat.cast_zero, map_zero, add_zero, Polynomial.comp_X] using
      LinearMap.padicNorm_apply_choose_X_comp_natCast hap L hLav k 0
  have hxm : L ((Polynomial.X : ℚ[X]) ^ (m - 1)) =
      (1 - (a : ℚ) ^ m) * (_root_.bernoulli m / m) := by
    rw [hLX, Nat.sub_add_cancel (by omega : 1 ≤ m)]
    have hc : (((m - 1 : ℕ) : ℚ) + 1) = (m : ℚ) := by
      exact_mod_cast Nat.sub_add_cancel (by omega : 1 ≤ m)
    rw [hc]
    simp only [Rat.cast_id]
    ring
  have hxn : L ((Polynomial.X : ℚ[X]) ^ (n - 1)) =
      (1 - (a : ℚ) ^ n) * (_root_.bernoulli n / n) := by
    rw [hLX, Nat.sub_add_cancel (by omega : 1 ≤ n)]
    have hc : (((n - 1 : ℕ) : ℚ) + 1) = (n : ℚ) := by
      exact_mod_cast Nat.sub_add_cancel (by omega : 1 ≤ n)
    rw [hc]
    simp only [Rat.cast_id]
    ring
  have hqn : padicNorm p (_root_.bernoulli n / n) ≤ 1 := by
    have h := LinearMap.padicNorm_apply_le_of_choose_X L hbase (by norm_num : (0 : ℚ) ≤ 1)
      ((Polynomial.X : ℚ[X]) ^ (n - 1)) (fun j => by
        simp only [Polynomial.eval_pow, Polynomial.eval_X]
        exact_mod_cast padicNorm.of_nat (p := p) (j ^ (n - 1)))
    rwa [hxn, padicNorm.mul, hunit n (Or.inr rfl), one_mul] at h
  have hpoly : padicNorm p
      (L ((Polynomial.X : ℚ[X]) ^ (m - 1) - Polynomial.X ^ (n - 1))) ≤ (p : ℚ) ^ (-1 : ℤ) := by
    apply LinearMap.padicNorm_apply_le_of_choose_X L hbase (by positivity)
    intro j
    have he : (j : ZMod p) ^ (m - 1) = (j : ZMod p) ^ (n - 1) := by
      by_cases hj : (j : ZMod p) = 0
      · simp only [hj, zero_pow (by omega : m - 1 ≠ 0), zero_pow (by omega : n - 1 ≠ 0)]
      · apply mul_right_cancel₀ hj
        rw [← pow_succ, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ m),
          Nat.sub_add_cancel (by omega : 1 ≤ n)]
        exact pow_eq_pow_of_modEq hmn (ZMod.pow_card_sub_one_eq_one hj)
    have hd : (p : ℤ) ∣ (j : ℤ) ^ (m - 1) - (j : ℤ) ^ (n - 1) := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      push_cast
      exact sub_eq_zero.mpr he
    have hnorm := (padicNorm.dvd_iff_norm_le (p := p) (n := 1)
      (z := (j : ℤ) ^ (m - 1) - (j : ℤ) ^ (n - 1))).mp (by simpa only [pow_one] using hd)
    simpa only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Int.cast_sub, Int.cast_pow,
      Int.cast_natCast, Nat.cast_one] using hnorm
  have hdiff : padicNorm p ((1 - (a : ℚ) ^ n) - (1 - (a : ℚ) ^ m)) ≤ (p : ℚ) ^ (-1 : ℤ) := by
    have hd : (p : ℤ) ∣ (a : ℤ) ^ m - (a : ℤ) ^ n := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      push_cast
      exact sub_eq_zero.mpr hepow
    have hnorm := (padicNorm.dvd_iff_norm_le (p := p) (n := 1)
      (z := (a : ℤ) ^ m - (a : ℤ) ^ n)).mp (by simpa only [pow_one] using hd)
    have he : (1 - (a : ℚ) ^ n) - (1 - (a : ℚ) ^ m) = (a : ℚ) ^ m - (a : ℚ) ^ n := by ring
    rw [he]
    simpa only [Int.cast_sub, Int.cast_pow, Int.cast_natCast, Nat.cast_one] using hnorm
  have hcorr : padicNorm p (((1 - (a : ℚ) ^ n) - (1 - (a : ℚ) ^ m)) *
      (_root_.bernoulli n / n)) ≤ (p : ℚ) ^ (-1 : ℤ) := by
    rw [padicNorm.mul]
    calc
      _ ≤ padicNorm p ((1 - (a : ℚ) ^ n) - (1 - (a : ℚ) ^ m)) * 1 :=
        mul_le_mul_of_nonneg_left hqn (padicNorm.nonneg _)
      _ ≤ _ := by simpa only [mul_one] using hdiff
  have he : (1 - (a : ℚ) ^ m) * (_root_.bernoulli m / m - _root_.bernoulli n / n) =
      L ((Polynomial.X : ℚ[X]) ^ (m - 1) - Polynomial.X ^ (n - 1)) +
        ((1 - (a : ℚ) ^ n) - (1 - (a : ℚ) ^ m)) * (_root_.bernoulli n / n) := by
    rw [map_sub, hxm, hxn]
    ring
  have hbound : padicNorm p (_root_.bernoulli m / m - _root_.bernoulli n / n) ≤
      (p : ℚ) ^ (-1 : ℤ) := by
    rw [← one_mul (padicNorm p (_root_.bernoulli m / m - _root_.bernoulli n / n)),
      ← hunit m (Or.inl rfl), ← padicNorm.mul, he]
    exact padicNorm.nonarchimedean.trans (max_le hpoly hcorr)
  dsimp only [DLMF.BernoulliEuler.RatModEq]
  simpa only [pow_one, Nat.cast_one] using
    Rat.prime_pow_dvd_num_of_padicNorm_le (ℓ := 1) hbound

/-- **DLMF 24.10.4**: `(1 - p^{m-1}) Bₘ/m ≡ (1 - p^{n-1}) Bₙ/n (mod p^{ℓ+1})` for
`m ≡ n (mod (p-1)p^ℓ)` and `n ≢ 0 (mod p - 1)`, `ℓ ≥ 0`. -/
@[dlmf 24.10.E4]
theorem kummer_congruence_pow {p : ℕ} (hp : p.Prime) {m n ℓ : ℕ}
    (hmn : m ≡ n [MOD (p - 1) * p ^ ℓ]) (hn : ¬ (p - 1) ∣ n) :
    RatModEq ((p : ℤ) ^ (ℓ + 1)) ((1 - (p : ℚ) ^ (m - 1)) * bernoulli m / m)
      ((1 - (p : ℚ) ^ (n - 1)) * bernoulli n / n) := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hmodp : m ≡ n [MOD p - 1] := hmn.of_dvd (dvd_mul_right _ _)
  have hn0 : n ≠ 0 := by intro h; subst n; exact hn (dvd_zero _)
  have hm0 : m ≠ 0 := by
    intro h
    subst m
    exact hn (Nat.modEq_zero_iff_dvd.mp hmodp.symm)
  have hm1 : 1 ≤ m := by omega
  have hn1 : 1 ≤ n := by omega
  have hnot : ¬ ∀ u : (ZMod p)ˣ, u ^ n = 1 := by
    intro hu
    exact hn (by simpa only [ZMod.card] using (FiniteField.forall_pow_eq_one_iff (ZMod p) n).mp hu)
  push Not at hnot
  obtain ⟨u, hu⟩ := hnot
  let a : ℕ := (u : ZMod p).val
  have ha : (a : ZMod p) = u := ZMod.natCast_zmod_val _
  have hap : ¬ p ∣ a := by
    intro hd
    have hz : (a : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hd
    rw [ha] at hz
    exact u.ne_zero hz
  have hepow : (a : ZMod p) ^ m = (a : ZMod p) ^ n :=
    pow_eq_pow_of_modEq hmodp (ZMod.pow_card_sub_one_eq_one (by rw [ha]; exact u.ne_zero))
  let f (r : ℕ) : ℚ := (a : ℚ) ^ r - 1
  let q (r : ℕ) : ℚ := (1 - (p : ℚ) ^ (r - 1)) * _root_.bernoulli r / r
  let U (r R : ℕ) : ℚ := Bernoulli.Regularization.powerSum a (p ^ (R + 1)) r -
    (p : ℚ) ^ (r - 1) * Bernoulli.Regularization.powerSum a (p ^ R) r
  let T : ℚ := (p : ℚ) ^ (-((ℓ + 1 : ℕ) : ℤ))
  have hpQ : (0 : ℚ) < p := by exact_mod_cast hp.pos
  have hT : 0 < T := by dsimp only [T]; positivity
  have hunit (r : ℕ) (hr : r = m ∨ r = n) : padicNorm p (f r) = 1 := by
    have hnot : ¬ (p : ℤ) ∣ (a : ℤ) ^ r - 1 := by
      intro hd
      have hz : (((a : ℤ) ^ r - 1 : ℤ) : ZMod p) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hd
      have he : (a : ZMod p) ^ r = 1 := by
        push_cast at hz
        exact sub_eq_zero.mp hz
      rcases hr with rfl | rfl
      · rw [hepow, ha] at he
        exact hu (Units.ext he)
      · rw [ha] at he
        exact hu (Units.ext he)
    have h := (padicNorm.int_eq_one_iff (p := p) ((a : ℤ) ^ r - 1)).mpr hnot
    simpa only [f, Int.cast_sub, Int.cast_pow, Int.cast_natCast, Int.cast_one] using h
  have hqn : padicNorm p (q n) ≤ 1 := by
    have hreg := Bernoulli.padicNorm_one_sub_pow_mul_bernoulli_div_le (p := p) hn1 hap
    have hf : padicNorm p (1 - (a : ℚ) ^ n) = 1 := by
      rw [show 1 - (a : ℚ) ^ n = -((a : ℚ) ^ n - 1) by ring, padicNorm.neg]
      exact hunit n (Or.inr rfl)
    rw [mul_div_assoc, padicNorm.mul, hf, one_mul] at hreg
    have hpint : padicNorm p (1 - (p : ℚ) ^ (n - 1)) ≤ 1 := by
      simpa only [Int.cast_sub, Int.cast_one, Int.cast_pow, Int.cast_natCast] using
        padicNorm.of_int (p := p) (1 - (p : ℤ) ^ (n - 1))
    dsimp only [q]
    rw [mul_div_assoc, padicNorm.mul]
    calc
      _ ≤ padicNorm p (1 - (p : ℚ) ^ (n - 1)) * 1 :=
        mul_le_mul_of_nonneg_left hreg (padicNorm.nonneg _)
      _ ≤ 1 := by simpa only [mul_one] using hpint
  have hlim (r : ℕ) (hr : 1 ≤ r) :
      Tendsto (fun R => padicNorm p (f r * q r - U r R)) atTop (𝓝 0) := by
    have h := Bernoulli.Regularization.tendsto_padicNorm_sub_powerSum_sub_scaled (p := p) hr hap
    convert h using 1
    funext R
    congr 1
    dsimp only [f, q, U]
    ring
  have hem := (hlim m hm1).eventually (gt_mem_nhds hT)
  have hen := (hlim n hn1).eventually (gt_mem_nhds hT)
  obtain ⟨R, hRm, hRn⟩ := (hem.and hen).exists
  have hU : padicNorm p (U m R - U n R) ≤ T :=
    Bernoulli.Regularization.padicNorm_powerSum_sub_scaled_sub_le (p := p) (R := R) hap hm1 hn1 hmn
  have hprod : padicNorm p (f m * q m - f n * q n) ≤ T := by
    have he : f m * q m - f n * q n =
        ((f m * q m - U m R) + (U m R - U n R)) + -(f n * q n - U n R) := by ring
    rw [he]
    refine padicNorm.nonarchimedean.trans (max_le ?_ ?_)
    · exact padicNorm.nonarchimedean.trans (max_le hRm.le hU)
    · simpa only [padicNorm.neg] using hRn.le
  have hdiff : padicNorm p (f n - f m) ≤ T := by
    let M := p ^ (ℓ + 1)
    have hc : a.Coprime M := ((hp.coprime_iff_not_dvd).mpr hap).symm.pow_right (ℓ + 1)
    have ht := Nat.ModEq.pow_totient hc
    have hphi : M.totient = (p - 1) * p ^ ℓ := by
      dsimp only [M]
      rw [Nat.totient_prime_pow hp (by omega), show ℓ + 1 - 1 = ℓ by omega, mul_comm]
    have ht' : (a : ZMod M) ^ ((p - 1) * p ^ ℓ) = 1 := by
      rw [← hphi]
      simpa only [Nat.cast_pow, Nat.cast_one] using (ZMod.natCast_eq_natCast_iff _ _ _).mpr ht
    have he := pow_eq_pow_of_modEq hmn ht'
    have hd : (p : ℤ) ^ (ℓ + 1) ∣ (a : ℤ) ^ n - (a : ℤ) ^ m := by
      have hz : (((a : ℤ) ^ n - (a : ℤ) ^ m : ℤ) : ZMod M) = 0 := by
        push_cast
        exact sub_eq_zero.mpr he.symm
      simpa only [M, Nat.cast_pow] using (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
    have h := (padicNorm.dvd_iff_norm_le (p := p) (n := ℓ + 1)
      (z := (a : ℤ) ^ n - (a : ℤ) ^ m)).mp (by simpa only [Nat.cast_pow] using hd)
    have heq : f n - f m = (a : ℚ) ^ n - (a : ℚ) ^ m := by dsimp only [f]; ring
    rw [heq]
    simpa only [Int.cast_sub, Int.cast_pow, Int.cast_natCast] using h
  have hcorr : padicNorm p ((f n - f m) * q n) ≤ T := by
    rw [padicNorm.mul]
    calc
      _ ≤ padicNorm p (f n - f m) * 1 := mul_le_mul_of_nonneg_left hqn (padicNorm.nonneg _)
      _ ≤ _ := by simpa only [mul_one] using hdiff
  have heq : f m * (q m - q n) = (f m * q m - f n * q n) + (f n - f m) * q n := by ring
  have hb : padicNorm p (q m - q n) ≤ T := by
    rw [← one_mul (padicNorm p (q m - q n)), ← hunit m (Or.inl rfl), ← padicNorm.mul, heq]
    exact padicNorm.nonarchimedean.trans (max_le hprod hcorr)
  exact Rat.prime_pow_dvd_num_of_padicNorm_le hb

/-- Euler numbers as a Newton series with any number `K ≥ m` of terms:
`Eₘ = ∑_{k=0}^{K} 2⁻ᵏ ∑_{j=0}^{k} (-1)ʲ (k choose j) (2j+1)ᵐ`. -/
private lemma eulerNumber_eq_newton_series {m K : ℕ} (hmK : m ≤ K) :
    (eulerNumber m : ℚ) = ∑ k ∈ range (K + 1), 1 / (2 : ℚ) ^ k *
      ∑ j ∈ range (k + 1), (-1 : ℚ) ^ j * (k.choose j : ℚ) * (2 * (j : ℚ) + 1) ^ m := by
  have h := eulerPolyE_eq_newton_series m (1 / 2)
  rw [eulerPolyE_half] at h
  rw [sum_subset (range_subset_range.mpr (show m + 1 ≤ K + 1 by omega)) (fun k hk hk' => by
    have : m < k := by simp only [mem_range] at hk hk'; omega
    rw [sum_alt_choose_mul_add_pow_eq_zero _ this, mul_zero])] at h
  have h2 : (2 : ℂ) ^ m ≠ 0 := pow_ne_zero _ (by norm_num)
  have : ((eulerNumber m : ℚ) : ℂ) = ((∑ k ∈ range (K + 1), 1 / (2 : ℚ) ^ k *
      ∑ j ∈ range (k + 1), (-1 : ℚ) ^ j * (k.choose j : ℚ) * (2 * (j : ℚ) + 1) ^ m : ℚ) : ℂ) := by
    push_cast
    rw [div_eq_iff h2] at h
    rw [h, sum_mul]
    refine sum_congr rfl fun k _ => ?_
    rw [mul_assoc, sum_mul]
    congr 1
    refine sum_congr rfl fun j _ => ?_
    rw [show (1 / 2 : ℂ) + j = (2 * j + 1) / 2 by ring, div_pow]
    field_simp
  exact_mod_cast this

/-- A rational `p a / 2ᴷ` with `a ∈ ℤ` and `p` an odd prime has numerator divisible by `p`. -/
private lemma prime_dvd_num_of_eq_mul_div_two_pow {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {q : ℚ}
    {a : ℤ} (K : ℕ)
    (hq : q = p * a / 2 ^ K) : (p : ℤ) ∣ q.num := by
  have h1 : (q.num : ℚ) * 2 ^ K = p * a * q.den := by
    rw [← Rat.mul_den_eq_num, hq]; field_simp
  have h2 : q.num * 2 ^ K = p * a * q.den := by exact_mod_cast h1
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hd : (p : ℤ) ∣ q.num * 2 ^ K := ⟨a * q.den, by rw [h2]; ring⟩
  rcases hpz.dvd_or_dvd hd with h | h
  · exact h
  · exfalso
    have h' := hpz.dvd_of_dvd_pow h
    have : (p : ℤ) ≤ 2 := Int.le_of_dvd (by norm_num) h'
    have : 2 ≤ (p : ℤ) := by exact_mod_cast hp.two_le
    have : p = 2 := by omega
    exact hp2 this

/-- **DLMF 24.10.5**: `Eₙ ≡ Eₙ₊ₚ₋₁ (mod p)` for primes `p > 2` and `n ≥ 2`. -/
@[dlmf 24.10.E5]
theorem eulerNumber_modEq_add_prime_sub_one {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) {n : ℕ}
    (hn : 2 ≤ n) :
    RatModEq p (eulerNumber n) (eulerNumber (n + p - 1)) := by
  have := Fact.mk hp
  set K := n + p - 1
  have hF : ∀ a : ℤ, (p : ℤ) ∣ a ^ K - a ^ n := by
    intro a
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [show K = (n - 1) + p by omega, pow_add, ZMod.pow_card, ← pow_succ,
      Nat.sub_add_cancel (by omega), sub_self]
  choose e he using hF
  have hE := eulerNumber_eq_newton_series (m := n) (K := K) (by omega)
  have hE' := eulerNumber_eq_newton_series (m := K) (K := K) le_rfl
  unfold RatModEq
  refine prime_dvd_num_of_eq_mul_div_two_pow hp (by omega) K
      (a := -∑ k ∈ range (K + 1), 2 ^ (K - k) *
    ∑ j ∈ range (k + 1), (-1) ^ j * (k.choose j : ℤ) * e (2 * j + 1)) ?_
  rw [hE, hE', ← sum_sub_distrib]
  push_cast
  simp only [mul_neg, neg_div, mul_sum, sum_div, ← sum_neg_distrib, ← sum_sub_distrib]
  refine sum_congr rfl fun k hk => ?_
  have hk' : k ≤ K := Nat.lt_succ_iff.mp (mem_range.mp hk)
  refine sum_congr rfl fun j _ => ?_
  have hej : ((2 * (j : ℚ) + 1) ^ K - (2 * (j : ℚ) + 1) ^ n) = p * e (2 * j + 1) := by
    have := he (2 * j + 1); exact_mod_cast this
  have : (-1 : ℚ) ^ j * (k.choose j : ℚ) * (2 * (j : ℚ) + 1) ^ n -
      (-1 : ℚ) ^ j * (k.choose j : ℚ) * (2 * (j : ℚ) + 1) ^ K =
      -((-1 : ℚ) ^ j * (k.choose j : ℚ) * (p * e (2 * j + 1))) := by rw [← hej]; ring
  rw [← mul_sub, this,
    show (2 : ℚ) ^ K = 2 ^ k * 2 ^ (K - k) by rw [← pow_add, Nat.add_sub_cancel' hk']]
  field_simp

/-- Euler numbers at indices congruent modulo `2^ℓ` are congruent modulo `2^ℓ`;
stronger than DLMF, which assumes the first index is even and the second is obtained
by adding a nonnegative multiple of `2^ℓ`. -/
@[dlmf 24.10.E6 "stronger than DLMF: arbitrary indices congruent modulo 2^ℓ"]
theorem eulerNumber_two_mul_modEq_two_pow' (m n ℓ : ℕ) (hmn : m ≡ n [MOD 2 ^ ℓ]) :
    RatModEq ((2 : ℤ) ^ ℓ) (eulerNumber m) (eulerNumber n) := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact Rat.prime_pow_dvd_num_of_padicNorm_le (padicNorm_eulerNumber_sub_le_of_modEq m n ℓ hmn)

/-- **DLMF 24.10.6**: `E₂ₙ ≡ E₂ₙ₊w (mod 2^ℓ)` for `ℓ ≥ 0`, `n ≥ 0`, `w ≥ 0` with `2^ℓ ∣ w`. -/
@[dlmf 24.10.E6]
theorem eulerNumber_two_mul_modEq_two_pow (n ℓ w : ℕ) (hw : 2 ^ ℓ ∣ w) :
    RatModEq ((2 : ℤ) ^ ℓ) (eulerNumber (2 * n)) (eulerNumber (2 * n + w)) := by
  apply eulerNumber_two_mul_modEq_two_pow'
  exact (Nat.modEq_iff_dvd' (by omega : 2 * n ≤ 2 * n + w)).mpr (by simpa using hw)

/-! ### §24.10(iii) Voronoi's congruence -/

/-- **Voronoi's congruence, DLMF 24.10.7**: with `B₂ₙ = N₂ₙ/D₂ₙ` in lowest terms (`D₂ₙ > 0`),
`(b^{2n} - 1) N₂ₙ ≡ 2n b^{2n-1} D₂ₙ ∑_{k=1}^{M-1} k^{2n-1} ⌊kb/M⌋ (mod M)` for integers `M ≥ 2`
and `b` prime to `M`, `n ≥ 1`. -/
@[dlmf 24.10.E7]
theorem voronoi_congruence {n : ℕ} (hn : 1 ≤ n) {M : ℕ} (hM : 2 ≤ M) {b : ℤ}
    (hb : IsCoprime b M) :
    (b ^ (2 * n) - 1) * (bernoulli (2 * n)).num ≡
      2 * n * b ^ (2 * n - 1) * (bernoulli (2 * n)).den *
        ∑ k ∈ Icc 1 (M - 1), (k : ℤ) ^ (2 * n - 1) * ⌊((k * b : ℤ) : ℚ) / M⌋ [ZMOD M] := by
  let N := 2 * n
  let D : ℕ := (_root_.bernoulli N).den
  let A : ℤ := (_root_.bernoulli N).num
  let S : ℤ := ∑ j ∈ range M, (j : ℤ) ^ N
  let V : ℤ := ∑ j ∈ range M, (j : ℤ) ^ (N - 1) * ((b * j) / M)
  let H : ℤ := (b ^ N - 1) * S - N * M * b ^ (N - 1) * V
  let G : ℤ := (b ^ N - 1) * A - N * b ^ (N - 1) * D * V
  have hH : (M : ℤ) ^ 2 ∣ H := Int.sq_dvd_mul_sum_range_pow_sub_mul_sum_ediv (by omega) hb
  have hBD : (_root_.bernoulli N) * (D : ℚ) = (A : ℚ) := Rat.mul_den_eq_num _
  have hMG : (M : ℚ) * (G : ℚ) =
      ((b : ℚ) ^ N - 1) * ((D : ℚ) * ((M : ℚ) * _root_.bernoulli N - (S : ℚ))) +
        (D : ℚ) * (H : ℚ) := by
    dsimp only [G, H]
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_natCast, Int.cast_one]
    rw [← hBD]
    ring
  have hG : (M : ℤ) ∣ G := by
    apply Int.natCast_dvd.mpr
    apply (Nat.dvd_iff_prime_pow_dvd_dvd G.natAbs M).mpr
    intro p ℓ hp hdvd
    rcases ℓ with _ | ℓ
    · simp
    let _ : Fact p.Prime := ⟨hp⟩
    have hpM : p ∣ M := (dvd_pow_self p (by omega : ℓ + 1 ≠ 0)).trans hdvd
    have hM0 : (M : ℚ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
    have hMnorm : 0 < padicNorm p (M : ℚ) :=
      lt_of_le_of_ne (padicNorm.nonneg _) (Ne.symm (padicNorm.ne_zero hM0))
    have hfirst : padicNorm p (((b : ℚ) ^ N - 1) *
        ((D : ℚ) * ((M : ℚ) * _root_.bernoulli N - (S : ℚ)))) ≤
          (padicNorm p (M : ℚ)) ^ 2 := by
      rw [padicNorm.mul]
      have hi : padicNorm p ((b : ℚ) ^ N - 1) ≤ 1 := by
        simpa only [Int.cast_sub, Int.cast_pow, Int.cast_one] using
          padicNorm.of_int (p := p) (b ^ N - 1)
      have he : padicNorm p ((D : ℚ) * ((M : ℚ) * _root_.bernoulli N - (S : ℚ))) ≤
          (padicNorm p (M : ℚ)) ^ 2 := by
        simpa only [N, D, S, Int.cast_sum, Int.cast_pow, Int.cast_natCast] using
          Bernoulli.padicNorm_den_mul_faulhaber_sub_le hn (by omega : 1 ≤ M) hpM
      calc
        _ ≤ 1 * padicNorm p ((D : ℚ) * ((M : ℚ) * _root_.bernoulli N - (S : ℚ))) :=
          mul_le_mul_of_nonneg_right hi (padicNorm.nonneg _)
        _ ≤ _ := by simpa only [one_mul] using he
    have hsecond : padicNorm p ((D : ℚ) * (H : ℚ)) ≤ (padicNorm p (M : ℚ)) ^ 2 := by
      have hdH : (M : ℤ) ^ 2 ∣ (D : ℤ) * H := dvd_mul_of_dvd_right hH _
      obtain ⟨z, hz⟩ := hdH
      have hzQ : (D : ℚ) * (H : ℚ) = (M : ℚ) ^ 2 * z := by exact_mod_cast hz
      rw [hzQ, padicNorm.mul, IsAbsoluteValue.abv_pow (padicNorm p)]
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (padicNorm.of_int (p := p) z) (sq_nonneg _)
    have hmul : padicNorm p (M : ℚ) * padicNorm p (G : ℚ) ≤ (padicNorm p (M : ℚ)) ^ 2 := by
      rw [← padicNorm.mul, hMG]
      exact padicNorm.nonarchimedean.trans (max_le hfirst hsecond)
    have hnormG : padicNorm p (G : ℚ) ≤ padicNorm p (M : ℚ) := by
      rw [pow_two] at hmul
      exact (mul_le_mul_iff_right₀ hMnorm).mp hmul
    have hnormM : padicNorm p (M : ℚ) ≤ (p : ℚ) ^ (-((ℓ + 1 : ℕ) : ℤ)) := by
      have hdz : ((p ^ (ℓ + 1) : ℕ) : ℤ) ∣ M := by exact_mod_cast hdvd
      simpa only [Int.cast_natCast] using padicNorm.dvd_iff_norm_le.mp hdz
    have hdG : ((p ^ (ℓ + 1) : ℕ) : ℤ) ∣ G :=
      padicNorm.dvd_iff_norm_le.mpr (hnormG.trans hnormM)
    exact Int.natCast_dvd.mp hdG
  have hV : V = ∑ k ∈ Icc 1 (M - 1), (k : ℤ) ^ (N - 1) * ⌊((k * b : ℤ) : ℚ) / M⌋ := by
    dsimp only [V]
    have hs := Finset.sum_range_succ_eq_sum_Icc_of_zero (M - 1)
      (f := fun k : ℕ => (k : ℤ) ^ (N - 1) * ((b * k) / M)) (by simp)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ M)] at hs
    rw [hs]
    apply sum_congr rfl
    intro k _
    rw [Rat.floor_intCast_div_natCast, mul_comm (k : ℤ) b]
  have hMod : (b ^ N - 1) * A ≡ (N : ℤ) * b ^ (N - 1) * D * V [ZMOD M] := by
    apply Int.modEq_iff_dvd.mpr
    convert hG.neg_right using 1
    dsimp only [G]
    ring
  rw [hV] at hMod
  simpa only [N, D, A, Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using hMod

/-! ### §24.10(iv) Factors -/

/-- **DLMF 24.10.8**: `N₂ₙ ≡ 0 (mod p^ℓ)` for `ℓ ≥ 1`, `n ≥ 1`, `2n ≢ 0 (mod p - 1)` and
`p^ℓ ∣ 2n`. -/
@[dlmf 24.10.E8]
theorem prime_pow_dvd_bernoulli_num {p : ℕ} (hp : p.Prime) {n ℓ : ℕ} (hn : 1 ≤ n) (hℓ : 1 ≤ ℓ)
    (hp1 : ¬ (p - 1) ∣ 2 * n) (hdvd : p ^ ℓ ∣ 2 * n) :
    (p : ℤ) ^ ℓ ∣ (bernoulli (2 * n)).num := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by intro h; subst p; exact hp1 (by simp)
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hpd : p ∣ 2 * n := (dvd_pow_self p (by omega : ℓ ≠ 0)).trans hdvd
  have hN : 4 ≤ 2 * n := by
    have hle := Nat.le_of_dvd (by omega : 0 < 2 * n) hpd
    omega
  apply Rat.prime_pow_dvd_num_of_padicNorm_le
  exact Bernoulli.padicNorm_bernoulli_le_of_prime_pow_dvd hp hN (even_two_mul n) hdvd hp1

open Polynomial

/-- Expanding `2ᵐ Eₘ(x + 1/2)` in powers of `2x` and Euler numbers. -/
private lemma two_pow_mul_euler_eval_add_half_eq_sum (m : ℕ) (x : ℚ) :
    2 ^ m * (euler m).eval (x + 1 / 2) =
      ∑ k ∈ range (m + 1), (m.choose k : ℚ) * (2 * x) ^ (m - k) * eulerNumber k := by
  rw [add_comm x, euler_eval_add, mul_sum]
  refine sum_congr rfl fun k hk => ?_
  have hkm : k ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hk)
  rw [eulerNumber, mul_pow,
    show (2 : ℚ) ^ m = 2 ^ (m - k) * 2 ^ k by rw [← pow_add, Nat.sub_add_cancel hkm]]
  ring

/-- Alternating odd powers as a difference of scaled Euler polynomial values. -/
private lemma sum_range_neg_one_pow_mul_odd_pow (m N : ℕ) :
    2 * ∑ j ∈ range N, (-1 : ℚ) ^ j * (2 * (j : ℚ) + 1) ^ m =
      eulerNumber m - (-1) ^ N * 2 ^ m * (euler m).eval ((N : ℚ) + 1 / 2) := by
  induction N with
  | zero => simp [eulerNumber]
  | succ N ih =>
    rw [sum_range_succ, mul_add, ih, pow_succ]
    have h := euler_eval_add_one_add m ((N : ℚ) + 1 / 2)
    have harg : (N : ℚ) + 1 / 2 + 1 = (N + 1 : ℕ) + 1 / 2 := by push_cast; ring
    rw [harg] at h
    have hpow : (2 * (N : ℚ) + 1) ^ m = 2 ^ m * ((N : ℚ) + 1 / 2) ^ m := by
      rw [← mul_pow]; congr 1; ring
    rw [hpow]
    linear_combination -((-1 : ℚ) ^ N * 2 ^ m) * h

/-- For odd `N`, the difference between `Eₘ` and the alternating sum of odd powers is
an integer multiple of `N`. -/
private lemma eulerNumber_sub_sum_odd_pow_eq (m N : ℕ) (hN : Odd N) :
    ∃ z : ℤ, eulerNumber m -
      ∑ j ∈ range N, (-1 : ℚ) ^ j * (2 * (j : ℚ) + 1) ^ m = N * z := by
  choose E hE using fun k => (eulerNumber_eq_two_pow_mul_and_integer k).2
  refine ⟨-∑ k ∈ range m,
    (m.choose k : ℤ) * (2 * N : ℤ) ^ (m - k - 1) * E k, ?_⟩
  have hs := sum_range_neg_one_pow_mul_odd_pow m N
  rw [hN.neg_one_pow, neg_one_mul, neg_mul, sub_neg_eq_add,
    two_pow_mul_euler_eval_add_half_eq_sum, sum_range_succ] at hs
  simp only [Nat.choose_self, Nat.sub_self, pow_zero, Nat.cast_one, one_mul] at hs
  have ht : (∑ k ∈ range m,
      (m.choose k : ℚ) * (2 * (N : ℚ)) ^ (m - k) * eulerNumber k) =
      2 * N * (∑ k ∈ range m,
        (m.choose k : ℤ) * (2 * N : ℤ) ^ (m - k - 1) * E k : ℤ) := by
    push_cast
    rw [mul_sum]
    refine sum_congr rfl fun k hk => ?_
    have hkm : k < m := mem_range.mp hk
    rw [hE]
    conv_lhs => rw [show m - k = (m - k - 1) + 1 by omega, pow_succ]
    ring
  rw [ht] at hs
  push_cast at hs ⊢
  linarith

/-- Euler numbers modulo an odd prime power when their index is at least the exponent
and divisible by the totient. -/
private lemma eulerNumber_modEq_prime_pow_of_totient_dvd {p m ℓ : ℕ} (hp : p.Prime)
    (hpodd : Odd p) (hℓ : 1 ≤ ℓ) (hℓm : ℓ ≤ m)
    (hdvd : (p - 1) * p ^ (ℓ - 1) ∣ m) :
    RatModEq ((p : ℤ) ^ ℓ) (eulerNumber m) (1 - (-1) ^ ((p - 1) / 2)) := by
  let N := p ^ ℓ
  have hpow : ∀ j : ℕ, ((2 * j + 1 : ℕ) : ZMod N) ^ m =
      if p ∣ 2 * j + 1 then 0 else 1 := by
    intro j
    split_ifs with hj
    · have hd : N ∣ (2 * j + 1) ^ m :=
        (Nat.pow_dvd_pow p hℓm).trans (pow_dvd_pow_of_dvd hj m)
      simpa only [Nat.cast_pow] using (ZMod.natCast_eq_zero_iff _ _).mpr hd
    · have hc := ((hp.coprime_iff_not_dvd).mpr hj).symm.pow_right ℓ
      obtain ⟨a, ha⟩ := hdvd
      have hm : m = N.totient * a := by
        rw [Nat.totient_prime_pow hp (by omega), mul_comm (p ^ (ℓ - 1))]
        exact ha
      have ht := (Nat.ModEq.pow_totient hc).pow a
      rw [← pow_mul, ← hm, one_pow] at ht
      simpa only [Nat.cast_pow, Nat.cast_one] using (ZMod.natCast_eq_natCast_iff _ _ _).mpr ht
  have hsum : ∑ j ∈ range N, (-1 : ZMod N) ^ j *
      (((2 * j + 1 : ℕ) : ZMod N) ^ m) = 1 - (-1) ^ ((p - 1) / 2) := by
    have hoddSum : ∀ T : ℕ, Odd T → ∑ j ∈ range T, (-1 : ZMod N) ^ j = 1 := by
      intro T hT
      rw [← Fin.sum_univ_eq_sum_range]
      simpa only [Nat.not_even_iff_odd.mpr hT, ↓reduceIte] using Fin.sum_neg_one_pow (ZMod N) T
    let Q := p ^ (ℓ - 1)
    have hNQ : N = Q * p := by
      simpa only [N, Q, pow_one] using (Nat.pow_sub_mul_pow p hℓ).symm
    have hsplit : ∀ f : ℕ → ZMod N, ∑ j ∈ range N, f j =
        ∑ t ∈ range Q, ∑ a ∈ range p, f (a + p * t) := by
      intro f
      calc ∑ j ∈ range N, f j = ∑ j ∈ range (Q * p), f j :=
          congrArg (fun T => ∑ j ∈ range T, f j) hNQ
        _ = _ := by
          rw [← Fin.sum_univ_eq_sum_range]
          rw [← Equiv.sum_comp (finProdFinEquiv : Fin Q × Fin p ≃ Fin (Q * p)),
            Fintype.sum_prod_type]
          simp only [finProdFinEquiv, Equiv.coe_fn_mk]
          rw [Fin.sum_univ_eq_sum_range (fun t => ∑ a : Fin p, f (a + p * t)) Q]
          exact sum_congr rfl fun t _ =>
            Fin.sum_univ_eq_sum_range (fun a => f (a + p * t)) p
    have hres : ∀ a ∈ range p, p ∣ 2 * a + 1 ↔ a = (p - 1) / 2 := by
      intro a ha
      have hap : a < p := mem_range.mp ha
      obtain ⟨v, hv⟩ := hpodd
      have hpv : p = 2 * v + 1 := by omega
      rw [hpv]
      constructor
      · rintro ⟨q, hq⟩
        have hqpos : 0 < q := by nlinarith
        have hqle : q < 2 := by nlinarith
        have hq1 : q = 1 := by omega
        simp only [hq1, mul_one] at hq
        omega
      · intro ha
        have hav : a = v := by omega
        exact ⟨1, by rw [hav]; omega⟩
    have hzero : ∑ j ∈ range N,
        (if p ∣ 2 * j + 1 then (-1 : ZMod N) ^ j else 0) = (-1) ^ ((p - 1) / 2) := by
      rw [hsplit]
      have hblock : ∀ t ∈ range Q, ∑ a ∈ range p,
          (if p ∣ 2 * (a + p * t) + 1 then (-1 : ZMod N) ^ (a + p * t) else 0) =
          (-1) ^ t * (-1) ^ ((p - 1) / 2) := by
        intro t _
        have hterm : ∀ a ∈ range p,
            (if p ∣ 2 * (a + p * t) + 1 then (-1 : ZMod N) ^ (a + p * t) else 0) =
            if a = (p - 1) / 2 then (-1) ^ t * (-1) ^ ((p - 1) / 2) else 0 := by
          intro a ha
          have hd : p ∣ 2 * (a + p * t) + 1 ↔ p ∣ 2 * a + 1 := by
            rw [show 2 * (a + p * t) + 1 = (2 * a + 1) + p * (2 * t) by ring,
              ← Nat.dvd_add_iff_left (dvd_mul_right p (2 * t))]
          simp only [hd, hres a ha]
          split_ifs with ha'
          · rw [ha', pow_add, pow_mul, hpodd.neg_one_pow]
            ring
          · rfl
        rw [sum_congr rfl hterm, sum_ite_eq']
        have hh : (p - 1) / 2 < p := by
          have := hp.two_le
          omega
        simp only [mem_range, hh, ↓reduceIte]
      rw [sum_congr rfl hblock, ← sum_mul, hoddSum Q hpodd.pow, one_mul]
    calc ∑ j ∈ range N, (-1 : ZMod N) ^ j * (((2 * j + 1 : ℕ) : ZMod N) ^ m)
        = (∑ j ∈ range N, (-1 : ZMod N) ^ j) -
            ∑ j ∈ range N, (if p ∣ 2 * j + 1 then (-1 : ZMod N) ^ j else 0) := by
          rw [← sum_sub_distrib]
          refine sum_congr rfl fun j _ => ?_
          rw [hpow]
          split_ifs <;> simp
      _ = 1 - (-1) ^ ((p - 1) / 2) := by rw [hoddSum N hpodd.pow, hzero]
  obtain ⟨E, hE⟩ := (eulerNumber_eq_two_pow_mul_and_integer m).2
  obtain ⟨z, hz⟩ := eulerNumber_sub_sum_odd_pow_eq m N hpodd.pow
  rw [hE] at hz
  have hz' : E - ∑ j ∈ range N, (-1 : ℤ) ^ j * (2 * (j : ℤ) + 1) ^ m = N * z := by
    exact_mod_cast hz
  have he : (E : ZMod N) = ∑ j ∈ range N, (-1 : ZMod N) ^ j *
      (((2 * j + 1 : ℕ) : ZMod N) ^ m) := by
    have h := congrArg (Int.cast : ℤ → ZMod N) hz'
    push_cast at h ⊢
    simpa only [ZMod.natCast_self, zero_mul, sub_eq_zero] using h
  unfold RatModEq
  rw [hE]
  have hc : (1 : ℚ) - (-1) ^ ((p - 1) / 2) = ((1 - (-1) ^ ((p - 1) / 2) : ℤ) : ℚ) := by
    push_cast; rfl
  rw [hc, ← Int.cast_sub, Rat.num_intCast]
  have hzero : ((E - (1 - (-1) ^ ((p - 1) / 2)) : ℤ) : ZMod N) = 0 := by
    push_cast
    rw [he, hsum, sub_self]
  simpa [N] using (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp hzero

/-- **DLMF 24.10.9**: for `ℓ ≥ 1`, `n ≥ 1` with `(p - 1)p^{ℓ-1} ∣ 2n`, `E₂ₙ ≡ 0 (mod p^ℓ)` if
`p ≡ 1 (mod 4)` and `E₂ₙ ≡ 2 (mod p^ℓ)` if `p ≡ 3 (mod 4)`. -/
@[dlmf 24.10.E9]
theorem eulerNumber_two_mul_modEq_prime_pow {p : ℕ} (hp : p.Prime) {n ℓ : ℕ} (hn : 1 ≤ n)
    (hℓ : 1 ≤ ℓ) (hdvd : (p - 1) * p ^ (ℓ - 1) ∣ 2 * n) :
    (p % 4 = 1 → RatModEq ((p : ℤ) ^ ℓ) (eulerNumber (2 * n)) 0) ∧
      (p % 4 = 3 → RatModEq ((p : ℤ) ^ ℓ) (eulerNumber (2 * n)) 2) := by
  have hℓn : ℓ ≤ 2 * n := by
    have hpow : ℓ ≤ p ^ (ℓ - 1) := by
      have := Nat.lt_pow_self (n := ℓ - 1) hp.one_lt
      omega
    have hmul : p ^ (ℓ - 1) ≤ (p - 1) * p ^ (ℓ - 1) :=
      Nat.le_mul_of_pos_left _ (by have := hp.two_le; omega)
    exact (hpow.trans hmul).trans (Nat.le_of_dvd (by omega) hdvd)
  constructor
  · intro hp4
    have hpodd := hp.odd_of_ne_two (by omega)
    have heven : Even ((p - 1) / 2) := ⟨p / 4, by omega⟩
    simpa only [heven.neg_one_pow, sub_self] using
      eulerNumber_modEq_prime_pow_of_totient_dvd hp hpodd hℓ hℓn hdvd
  · intro hp4
    have hpodd := hp.odd_of_ne_two (by omega)
    have hodd : Odd ((p - 1) / 2) := ⟨p / 4, by omega⟩
    simpa only [hodd.neg_one_pow, sub_neg_eq_add, one_add_one_eq_two] using
      eulerNumber_modEq_prime_pow_of_totient_dvd hp hpodd hℓ hℓn hdvd


end DLMF.BernoulliEuler
