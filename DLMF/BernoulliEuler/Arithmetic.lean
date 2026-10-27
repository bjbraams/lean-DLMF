/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.BernoulliEuler.Explicit

/-!
# Bernoulli and Euler numbers: arithmetic properties (DLMF §24.10)

DLMF §24.10(i): "two rational numbers are congruent if the modulus divides the numerator of
their difference"; this is `RatModEq M a b`. The von Staudt–Clausen theorem 24.10.1 is Mathlib's
`Bernoulli.vonStaudt_clausen` (pointer in `DLMF.BernoulliEuler.MathlibCoverage`); the second
assertion of 24.10.1 (the denominator of `B₂ₙ` is the product of the primes `p` with
`p - 1 ∣ 2n`) is `bernoulli_two_mul_den_eq_prod`.

## Corrections

* Kummer's congruence 24.10.3 fails if `m = 1` or `n = 1` (e.g. `p = 3`, `m = 1`, `n = 3`:
  `B₁/1 = -1/2 ≢ 0 = B₃/3 (mod 3)`); acquired for `m, n ≥ 2`. 24.10.4 needs no such condition
  (its factor `1 - p⁰` vanishes for `m = 1`).
* 24.10.5 also holds for `n = 1` (`E₁ = Eₚ = 0`), but not for `n = 0`; acquired as printed
  (`n ≥ 2`).

All congruences were checked in exact arithmetic for primes `p ≤ 13` and the index ranges
`m, n < 60` (24.10.3–24.10.4), `n < 200` (24.10.2), `n < 150` (24.10.8–24.10.9), `M < 12`,
`|b| ≤ 7` (24.10.7).
-/

@[expose] public section

noncomputable section

open Finset
open scoped Nat

namespace DLMF.BernoulliEuler

/-- Congruence of rational numbers in DLMF §24.10: `a ≡ b (mod M)` when `M` divides the
numerator of `a - b`. -/
@[dlmf 24.10.i]
def RatModEq (M : ℤ) (a b : ℚ) : Prop := M ∣ (a - b).num

/-! ### §24.10(i) Von Staudt–Clausen theorem -/

/-- The denominator of `∑_{p ∈ s} 1/p` divides `∏_{p ∈ s} p`. -/
lemma q24a_den_sum_inv_dvd (s : Finset ℕ) :
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
    exact q24a_den_sum_inv_dvd T
  · refine Finset.prod_primes_dvd _ (fun p hp => (mem_filter.mp hp).2.1.prime) fun p hp => ?_
    have hp' := (mem_filter.mp hp).2
    have : Fact p.Prime := ⟨hp'.1⟩
    exact Bernoulli.dvd_den_bernoulli (by omega) hp'.2

/-- **DLMF 24.10.2**: `p B₂ₙ ≡ p - 1 (mod p^{ℓ+1})` for `n ≥ 2`, `ℓ ≥ 1`, `(p-1)p^ℓ ∣ 2n`. -/
@[dlmf 24.10.E2]
theorem prime_mul_bernoulli_two_mul_modEq {p : ℕ} (hp : p.Prime) {n ℓ : ℕ} (hn : 2 ≤ n)
    (hℓ : 1 ≤ ℓ) (hdvd : (p - 1) * p ^ ℓ ∣ 2 * n) :
    RatModEq ((p : ℤ) ^ (ℓ + 1)) (p * bernoulli (2 * n)) (p - 1) := by
  sorry

/-! ### §24.10(ii) Kummer congruences -/

/-- **Kummer's congruence, DLMF 24.10.3** (corrected: `m, n ≥ 2`):
`Bₘ/m ≡ Bₙ/n (mod p)` for `m ≡ n ≢ 0 (mod p - 1)`. -/
@[dlmf 24.10.E3]
theorem kummer_congruence {p : ℕ} (hp : p.Prime) {m n : ℕ} (hm : 2 ≤ m) (hn2 : 2 ≤ n)
    (hmn : m ≡ n [MOD p - 1]) (hn : ¬ (p - 1) ∣ n) :
    RatModEq p (bernoulli m / m) (bernoulli n / n) := by
  sorry

/-- **DLMF 24.10.4**: `(1 - p^{m-1}) Bₘ/m ≡ (1 - p^{n-1}) Bₙ/n (mod p^{ℓ+1})` for
`m ≡ n (mod (p-1)p^ℓ)` and `n ≢ 0 (mod p - 1)`, `ℓ ≥ 0`. -/
@[dlmf 24.10.E4]
theorem kummer_congruence_pow {p : ℕ} (hp : p.Prime) {m n ℓ : ℕ}
    (hmn : m ≡ n [MOD (p - 1) * p ^ ℓ]) (hn : ¬ (p - 1) ∣ n) :
    RatModEq ((p : ℤ) ^ (ℓ + 1)) ((1 - (p : ℚ) ^ (m - 1)) * bernoulli m / m)
      ((1 - (p : ℚ) ^ (n - 1)) * bernoulli n / n) := by
  sorry

/-- Euler numbers as a Newton series with any number `K ≥ m` of terms:
`Eₘ = ∑_{k=0}^{K} 2⁻ᵏ ∑_{j=0}^{k} (-1)ʲ (k choose j) (2j+1)ᵐ`. -/
lemma r24a_eulerNumber_newton {m K : ℕ} (hmK : m ≤ K) :
    (eulerNumber m : ℚ) = ∑ k ∈ range (K + 1), 1 / (2 : ℚ) ^ k *
      ∑ j ∈ range (k + 1), (-1 : ℚ) ^ j * (k.choose j : ℚ) * (2 * (j : ℚ) + 1) ^ m := by
  have h := q24a_eulerPolyE_newton m (1 / 2)
  rw [eulerPolyE_half] at h
  rw [sum_subset (range_subset_range.mpr (show m + 1 ≤ K + 1 by omega)) (fun k hk hk' => by
    have : m < k := by simp only [mem_range] at hk hk'; omega
    rw [q24a_alt_sum_pow_eq_zero _ this, mul_zero])] at h
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
lemma r24a_dvd_num_of_eq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {q : ℚ} {a : ℤ} (K : ℕ)
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
  have hE := r24a_eulerNumber_newton (m := n) (K := K) (by omega)
  have hE' := r24a_eulerNumber_newton (m := K) (K := K) le_rfl
  unfold RatModEq
  refine r24a_dvd_num_of_eq hp (by omega) K (a := -∑ k ∈ range (K + 1), 2 ^ (K - k) *
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

/-- **DLMF 24.10.6**: `E₂ₙ ≡ E₂ₙ₊w (mod 2^ℓ)` for `ℓ ≥ 0`, `n ≥ 0`, `w ≥ 0` with `2^ℓ ∣ w`. -/
@[dlmf 24.10.E6]
theorem eulerNumber_two_mul_modEq_two_pow (n ℓ w : ℕ) (hw : 2 ^ ℓ ∣ w) :
    RatModEq ((2 : ℤ) ^ ℓ) (eulerNumber (2 * n)) (eulerNumber (2 * n + w)) := by
  sorry

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
  sorry

/-! ### §24.10(iv) Factors -/

/-- **DLMF 24.10.8**: `N₂ₙ ≡ 0 (mod p^ℓ)` for `ℓ ≥ 1`, `n ≥ 1`, `2n ≢ 0 (mod p - 1)` and
`p^ℓ ∣ 2n`. -/
@[dlmf 24.10.E8]
theorem prime_pow_dvd_bernoulli_num {p : ℕ} (hp : p.Prime) {n ℓ : ℕ} (hn : 1 ≤ n) (hℓ : 1 ≤ ℓ)
    (hp1 : ¬ (p - 1) ∣ 2 * n) (hdvd : p ^ ℓ ∣ 2 * n) :
    (p : ℤ) ^ ℓ ∣ (bernoulli (2 * n)).num := by
  sorry

/-- **DLMF 24.10.9**: for `ℓ ≥ 1`, `n ≥ 1` with `(p - 1)p^{ℓ-1} ∣ 2n`, `E₂ₙ ≡ 0 (mod p^ℓ)` if
`p ≡ 1 (mod 4)` and `E₂ₙ ≡ 2 (mod p^ℓ)` if `p ≡ 3 (mod 4)`. -/
@[dlmf 24.10.E9]
theorem eulerNumber_two_mul_modEq_prime_pow {p : ℕ} (hp : p.Prime) {n ℓ : ℕ} (hn : 1 ≤ n)
    (hℓ : 1 ≤ ℓ) (hdvd : (p - 1) * p ^ (ℓ - 1) ∣ 2 * n) :
    (p % 4 = 1 → RatModEq ((p : ℤ) ^ ℓ) (eulerNumber (2 * n)) 0) ∧
      (p % 4 = 3 → RatModEq ((p : ℤ) ^ ℓ) (eulerNumber (2 * n)) 2) := by
  sorry

end DLMF.BernoulliEuler
