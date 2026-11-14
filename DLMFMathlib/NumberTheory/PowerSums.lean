/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Int.Basic
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.RingTheory.Coprime.Basic
import Mathlib.NumberTheory.Multiplicity
import Mathlib.RingTheory.Coprime.Lemmas
import DLMFMathlib.Data.ZMod.BigOperators
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

/-!
# Prime-power divisibility of power sums

If `p^ℓ` divides `N` and `p - 1` does not, then `∑_{j < p} j^N` is divisible by
`p^(ℓ+1)`. Multiplication by a finite-field unit whose `N`th power is not one
permutes the residues. Lifting the exponent identifies the lifted powers modulo
`p^(ℓ+1)`, and the resulting unit factor can be cancelled.

* `Int.prime_pow_dvd_pow_sub_pow`: the lifting-the-exponent divisibility consequence.
* `Int.prime_pow_dvd_sum_range_pow`: the power sum divisibility theorem.
* `Int.sq_dvd_mul_sum_range_pow_sub_mul_sum_ediv`: the finite integer Voronoi congruence.
* `Int.sq_dvd_mul_sum_range_pow_sub_mul_sum_div`: its natural multiplier form.

The proof uses Mathlib's `Int.emultiplicity_pow_sub_pow`,
`FiniteField.forall_pow_eq_one_iff`, and finite sum reindexing APIs.
-/

public noncomputable section

open Finset
open scoped Nat

namespace Int

/-- If `x ≡ y (mod p)`, `p ∤ x`, `p` is odd prime, and `p^ℓ ∣ N`, then
`x^N ≡ y^N (mod p^(ℓ+1))`. -/
lemma prime_pow_dvd_pow_sub_pow {p N ℓ : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hN : p ^ ℓ ∣ N) {x y : ℤ} (hxy : (p : ℤ) ∣ x - y) (hx : ¬ (p : ℤ) ∣ x) :
    (p : ℤ) ^ (ℓ + 1) ∣ x ^ N - y ^ N := by
  rw [pow_dvd_iff_le_emultiplicity, Int.emultiplicity_pow_sub_pow hp hodd hxy hx]
  have h₁ : (1 : ℕ∞) ≤ emultiplicity (p : ℤ) (x - y) := by
    exact le_emultiplicity_of_pow_dvd (by simpa only [pow_one] using hxy : (p : ℤ) ^ 1 ∣ x - y)
  have h₂ : (ℓ : ℕ∞) ≤ emultiplicity p N := le_emultiplicity_of_pow_dvd hN
  simpa only [Nat.cast_add, Nat.cast_one, add_comm] using add_le_add h₁ h₂

/-- If `p^ℓ ∣ N` and `p - 1 ∤ N`, the sum of the `N`th powers of the residues
modulo the prime `p` is divisible by `p^(ℓ+1)`. -/
lemma prime_pow_dvd_sum_range_pow {p N ℓ : ℕ} (hp : p.Prime) (hN : p ^ ℓ ∣ N)
    (hNd : ¬ (p - 1) ∣ N) :
    (p : ℤ) ^ (ℓ + 1) ∣ ∑ j ∈ Finset.range p, (j : ℤ) ^ N := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by intro h; subst p; exact hNd (by simp)
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hN0 : 1 ≤ N := by
    by_contra h
    have : N = 0 := by omega
    exact hNd (by simp only [this, dvd_zero])
  have hn : ¬ ∀ u : (ZMod p)ˣ, u ^ N = 1 := by
    intro hu
    have h := (FiniteField.forall_pow_eq_one_iff (ZMod p) N).mp hu
    exact hNd (by simpa only [ZMod.card] using h)
  push Not at hn
  obtain ⟨u, hu⟩ := hn
  let a : ℕ := (u : ZMod p).val
  have ha : (a : ZMod p) = u := ZMod.natCast_zmod_val _
  have hap : ¬ p ∣ a := by
    intro hd
    have hz : (a : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hd
    rw [ha] at hz
    exact u.ne_zero hz
  have han : ¬ (p : ℤ) ∣ (a : ℤ) ^ N - 1 := by
    intro hd
    have hz : (((a : ℤ) ^ N - 1 : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hd
    have hz' : ((u : ZMod p) ^ N) = 1 := by
      simpa only [Int.cast_sub, Int.cast_pow, Int.cast_natCast, Int.cast_one, ha,
        sub_eq_zero] using hz
    exact hu (Units.ext hz')
  let M := p ^ (ℓ + 1)
  have hpow (x : ZMod p) :
      ((((u : ZMod p) * x).val : ℕ) : ZMod M) ^ N =
        (a : ZMod M) ^ N * (x.val : ZMod M) ^ N := by
    by_cases hx : x = 0
    · subst x
      simp only [mul_zero, ZMod.val_zero, Nat.cast_zero, zero_pow (by omega : N ≠ 0)]
    · have hxunit : ¬ (p : ℤ) ∣ (a : ℤ) * x.val := by
        intro hd
        have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
        rcases hpz.dvd_or_dvd hd with hd | hd
        · exact hap (by exact_mod_cast hd)
        · have hz : ((x.val : ℕ) : ZMod p) = 0 :=
            (ZMod.natCast_eq_zero_iff _ _).mpr (by exact_mod_cast hd)
          exact hx (by simpa only [ZMod.natCast_zmod_val] using hz)
      have hxy : (p : ℤ) ∣ (a : ℤ) * x.val - (((u : ZMod p) * x).val : ℕ) := by
        apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
        simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, ha, ZMod.natCast_zmod_val,
          sub_self]
      have hd := prime_pow_dvd_pow_sub_pow hp hodd hN hxy hxunit
      have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd
        (((a : ℤ) * x.val) ^ N - ((((u : ZMod p) * x).val : ℕ) : ℤ) ^ N) M).mpr
          (by simpa only [M, Nat.cast_pow] using hd)
      push_cast at hz
      rw [mul_pow] at hz
      exact (sub_eq_zero.mp hz).symm
  let S : ZMod M := ∑ x : ZMod p, (x.val : ZMod M) ^ N
  have hmul : (a : ZMod M) ^ N * S = S := by
    simp only [S, mul_sum]
    rw [show (fun x : ZMod p => (a : ZMod M) ^ N * (x.val : ZMod M) ^ N) =
        fun x => ((((u : ZMod p) * x).val : ℕ) : ZMod M) ^ N by
          funext x; exact (hpow x).symm]
    convert Equiv.sum_comp (Equiv.mulLeft₀ (u : ZMod p) u.ne_zero)
      (fun x : ZMod p => (x.val : ZMod M) ^ N) using 1
    simp only [Equiv.mulLeft₀_apply]
  have hScast : S = ((∑ j ∈ Finset.range p, (j : ℤ) ^ N : ℤ) : ZMod M) := by
    dsimp only [S]
    rw [ZMod.sum_univ_val p (fun j => (j : ZMod M) ^ N)]
    push_cast
    rfl
  push_cast at hScast
  have hd : (p : ℤ) ^ (ℓ + 1) ∣ ((a : ℤ) ^ N - 1) *
      (∑ j ∈ Finset.range p, (j : ℤ) ^ N) := by
    have hzero :
        (((((a : ℤ) ^ N - 1) * (∑ j ∈ Finset.range p, (j : ℤ) ^ N)) : ℤ) : ZMod M) = 0 := by
      push_cast
      rw [← hScast, sub_mul, one_mul, hmul, sub_self]
    simpa only [M, Nat.cast_pow] using (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzero
  have hc : IsCoprime ((p : ℤ) ^ (ℓ + 1)) ((a : ℤ) ^ N - 1) := by
    exact ((Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd.mpr han).pow_left
  exact hc.dvd_of_dvd_mul_left hd

/-- Multiplication by an integer prime to `M` gives the first-order Voronoi
power sum congruence modulo `M²`; the multiplier may be negative. -/
lemma sq_dvd_mul_sum_range_pow_sub_mul_sum_ediv {M N : ℕ} (hM : 1 ≤ M) {b : ℤ}
    (hb : IsCoprime b M) :
    (M : ℤ) ^ 2 ∣ (b ^ N - 1) * (∑ j ∈ Finset.range M, (j : ℤ) ^ N) -
      N * M * b ^ (N - 1) * ∑ j ∈ Finset.range M, (j : ℤ) ^ (N - 1) * ((b * j) / M) := by
  let _ : NeZero M := ⟨by omega⟩
  have hunit : IsUnit (b : ZMod M) := by
    apply isCoprime_zero_right.mp
    have h := hb.map (Int.castRingHom (ZMod M))
    simpa only [Int.coe_castRingHom, Int.cast_natCast, ZMod.natCast_self] using h
  obtain ⟨u, hu⟩ := hunit
  have hperm : (∑ j ∈ Finset.range M, ((b * j) % M) ^ N) = ∑ j ∈ Finset.range M, (j : ℤ) ^ N := by
    rw [← ZMod.sum_univ_val M (fun j => ((b * j) % M) ^ N),
      ← ZMod.sum_univ_val M (fun j => (j : ℤ) ^ N)]
    have he (x : ZMod M) : ((b * x.val) % M) ^ N = (((u * x : ZMod M).val : ℕ) : ℤ) ^ N := by
      have hr : (u * x : ZMod M) = ((b * (x.val : ℤ) : ℤ) : ZMod M) := by
        rw [hu]
        push_cast
        rw [ZMod.natCast_zmod_val]
      rw [hr, ZMod.val_intCast]
    rw [sum_congr rfl (fun x _ => he x)]
    exact Equiv.sum_comp u.mulLeft (fun x : ZMod M => (x.val : ℤ) ^ N)
  have hterm (j : ℕ) : (M : ℤ) ^ 2 ∣ (b * j) ^ N - ((b * j) % M) ^ N -
      N * M * (b * j) ^ (N - 1) * ((b * j) / M) := by
    have h := sq_dvd_add_pow_sub_sub (-(M : ℤ) * ((b * j) / M)) (b * j) N
    have hd : (M : ℤ) ^ 2 ∣ (-(M : ℤ) * ((b * j) / M)) ^ 2 := by
      rw [mul_pow, neg_sq]
      exact dvd_mul_right _ _
    have hr : b * j + -(M : ℤ) * ((b * j) / M) = (b * j) % M := by
      linarith [Int.emod_add_mul_ediv (b * j) M]
    have he : ((b * j) % M) ^ N - (b * j) ^ (N - 1) * (-(M : ℤ) * ((b * j) / M)) * N -
        (b * j) ^ N =
      -((b * j) ^ N - ((b * j) % M) ^ N - N * M * (b * j) ^ (N - 1) * ((b * j) / M)) := by ring
    rw [hr, he] at h
    simpa only [neg_neg] using (hd.trans h).neg_right
  have hs := Finset.dvd_sum (fun j (_ : j ∈ Finset.range M) => hterm j)
  have he : (∑ j ∈ Finset.range M, ((b * j) ^ N - ((b * j) % M) ^ N -
        N * M * (b * j) ^ (N - 1) * ((b * j) / M))) =
      (b ^ N - 1) * (∑ j ∈ Finset.range M, (j : ℤ) ^ N) -
      N * M * b ^ (N - 1) * ∑ j ∈ Finset.range M, (j : ℤ) ^ (N - 1) * ((b * j) / M) := by
    simp only [sum_sub_distrib, mul_pow, mul_assoc, ← mul_sum]
    rw [hperm]
    ring
  rwa [he] at hs

/-- Multiplication of residues prime to `M` gives the first-order power sum
congruence modulo `M²`, with the Euclidean quotient as its weight. -/
lemma sq_dvd_mul_sum_range_pow_sub_mul_sum_div {M a N : ℕ} (hM : 1 ≤ M) (ha : a.Coprime M) :
    (M : ℤ) ^ 2 ∣ ((a : ℤ) ^ N - 1) * (∑ j ∈ Finset.range M, (j : ℤ) ^ N) -
      N * M * (a : ℤ) ^ (N - 1) * ∑ j ∈ Finset.range M, (j : ℤ) ^ (N - 1) * ((a * j) / M : ℕ) := by
  have h := sq_dvd_mul_sum_range_pow_sub_mul_sum_ediv (N := N) hM ha.isCoprime
  simpa only [Nat.cast_mul, Int.natCast_ediv] using h

end Int
