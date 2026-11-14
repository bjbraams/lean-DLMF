/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.NumberTheory.BernoulliCongruences
import DLMFMathlib.NumberTheory.PowerSums
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Finite approximations to regularized Bernoulli moments

The first-order Voronoi congruence and Faulhaber's formula show that finite weighted
power sums over `p^R` approximate `(a^N - 1) B_N / N`. Removing the preceding scaled
sum restricts the residues to units, where Fermat–Euler supplies the prime-power
congruences at congruent indices.

* `Bernoulli.Regularization.powerSum`: the finite Voronoi weighted power sum.
* `Bernoulli.Regularization.tendsto_padicNorm_sub_powerSum`: the p-adic approximation.
* `Bernoulli.Regularization.powerSum_sub_scaled_eq_sum_not_dvd`: restriction to units.
* `Bernoulli.Regularization.tendsto_padicNorm_sub_powerSum_sub_scaled`: regularized moments.
* `Bernoulli.Regularization.padicNorm_powerSum_sub_scaled_sub_le`: the unit power congruence.

The proof uses Mathlib's p-adic norm, rational geometric limits, and Fermat–Euler theorem,
with the finite integer Voronoi congruence in `DLMFMathlib.NumberTheory.PowerSums`.
-/

public noncomputable section

open Finset Filter
open scoped Nat Topology

namespace Bernoulli.Regularization

/-- The finite Voronoi weighted power sum for nonnegative integers `a`, `M`, `N`.
The exponent is `N - 1` in `ℕ`; the approximation theorems assume `N ≥ 1`. -/
@[expose] def powerSum (a M N : ℕ) : ℚ :=
  (a : ℚ) ^ (N - 1) * ∑ j ∈ range M, (j : ℚ) ^ (N - 1) * ((a * j) / M : ℕ)

/-- The defining finite sum of the Voronoi power sum. -/
lemma powerSum_def (a M N : ℕ) : powerSum a M N =
    (a : ℚ) ^ (N - 1) * ∑ j ∈ range M, (j : ℚ) ^ (N - 1) * ((a * j) / M : ℕ) := rfl

/-- The finite Voronoi power sums over `p^R` converge p-adically to
`(a^N - 1) B_N / N` when `p ∤ a` and `N ≥ 1`. -/
lemma tendsto_padicNorm_sub_powerSum {p a N : ℕ} [Fact p.Prime] (hN : 1 ≤ N)
    (ha : ¬ p ∣ a) :
    Tendsto (fun R : ℕ => padicNorm p
      (((a : ℚ) ^ N - 1) * _root_.bernoulli N / N - powerSum a (p ^ R) N)) atTop (𝓝 0) := by
  have hp : p.Prime := Fact.out
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (1 : ℚ) < p := by exact_mod_cast hp.one_lt
  have hN0 : (N : ℚ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hgeo : Tendsto (fun R : ℕ => ((p : ℚ)⁻¹) ^ R) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hp1)
  let A (R : ℕ) : ℚ := ((a : ℚ) ^ N - 1) *
    (∑ j ∈ range (p ^ R), (j : ℚ) ^ N) / ((p ^ R : ℚ) * N)
  have herr (R : ℕ) : padicNorm p (A R - powerSum a (p ^ R) N) ≤
      ((p : ℚ)⁻¹) ^ R / padicNorm p (N : ℚ) := by
    have hcop : a.Coprime (p ^ R) := ((hp.coprime_iff_not_dvd).mpr ha).symm.pow_right R
    obtain ⟨z, hz⟩ := Int.sq_dvd_mul_sum_range_pow_sub_mul_sum_div
      (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero R hp.ne_zero)) hcop
    have hzQ : (((a : ℚ) ^ N - 1) * (∑ j ∈ range (p ^ R), (j : ℚ) ^ N) -
        N * (p ^ R : ℚ) * powerSum a (p ^ R) N) = (p ^ R : ℚ) ^ 2 * z := by
      have hz' := congrArg (fun r : ℤ => (r : ℚ)) hz
      simp only [Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_natCast, Int.cast_one,
        Int.cast_sum] at hz'
      dsimp only [powerSum]
      push_cast at hz'
      convert hz' using 1; ring
    have he : A R - powerSum a (p ^ R) N = (p ^ R : ℚ) * z / N := by
      dsimp only [A]
      have hM0 : (p ^ R : ℚ) ≠ 0 := pow_ne_zero R hp0
      field_simp
      linear_combination hzQ
    rw [he, padicNorm.div, padicNorm.mul, IsAbsoluteValue.abv_pow (padicNorm p)]
    have hpn : padicNorm p (p : ℚ) = (p : ℚ)⁻¹ := padicNorm.padicNorm_p_of_prime
    rw [hpn]
    apply div_le_div_of_nonneg_right _ (padicNorm.nonneg _)
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (padicNorm.of_int (p := p) z)
        (by positivity : (0 : ℚ) ≤ ((p : ℚ)⁻¹) ^ R)
  let c : ℚ := padicNorm p (((a : ℚ) ^ N - 1) / N)
  have hmain : Tendsto (fun R : ℕ => c * padicNorm p
      ((∑ j ∈ range (p ^ R), (j : ℚ) ^ N) / (p ^ R : ℚ) - _root_.bernoulli N)) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul
      (Bernoulli.tendsto_padicNorm_sum_range_pow_div_sub (p := p) N)
  have hden : Tendsto (fun R : ℕ => ((p : ℚ)⁻¹) ^ R / padicNorm p (N : ℚ)) atTop (𝓝 0) := by
    simpa only [zero_div] using hgeo.div_const (padicNorm p (N : ℚ))
  have hbound (R : ℕ) : padicNorm p
      (((a : ℚ) ^ N - 1) * _root_.bernoulli N / N - powerSum a (p ^ R) N) ≤
        c * padicNorm p ((∑ j ∈ range (p ^ R), (j : ℚ) ^ N) / (p ^ R : ℚ) - _root_.bernoulli N) +
          ((p : ℚ)⁻¹) ^ R / padicNorm p (N : ℚ) := by
    have he : (((a : ℚ) ^ N - 1) * _root_.bernoulli N / N - powerSum a (p ^ R) N) =
        -(((a : ℚ) ^ N - 1) / N *
          ((∑ j ∈ range (p ^ R), (j : ℚ) ^ N) / (p ^ R : ℚ) - _root_.bernoulli N)) +
            (A R - powerSum a (p ^ R) N) := by dsimp only [A]; ring
    rw [he]
    have ht := padicNorm.triangle_ineq (p := p)
      (-(((a : ℚ) ^ N - 1) / N *
          ((∑ j ∈ range (p ^ R), (j : ℚ) ^ N) / (p ^ R : ℚ) - _root_.bernoulli N)))
      (A R - powerSum a (p ^ R) N)
    simp only [padicNorm.neg, padicNorm.mul] at ht
    dsimp only [c]
    calc
      _ ≤ padicNorm p (((a : ℚ) ^ N - 1) / N) *
          padicNorm p ((∑ j ∈ range (p ^ R), (j : ℚ) ^ N) / (p ^ R : ℚ) - _root_.bernoulli N) +
            padicNorm p (A R - powerSum a (p ^ R) N) := ht
      _ ≤ _ := add_le_add le_rfl (herr R)
  have hupper := hmain.add hden
  simp only [zero_add] at hupper
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun R => padicNorm.nonneg _) hbound

/-- Removing the scaled preceding power sum retains precisely the residues prime to `p`. -/
lemma powerSum_sub_scaled_eq_sum_not_dvd {p a N R : ℕ} (hp : 1 ≤ p) :
    powerSum a (p ^ (R + 1)) N - (p : ℚ) ^ (N - 1) * powerSum a (p ^ R) N =
      (a : ℚ) ^ (N - 1) * ∑ j ∈ range (p ^ (R + 1)) with ¬ p ∣ j,
        (j : ℚ) ^ (N - 1) * ((a * j) / (p ^ (R + 1)) : ℕ) := by
  have hsplit (f : ℕ → ℚ) : (∑ j ∈ range (p ^ (R + 1)) with p ∣ j, f j) =
      ∑ k ∈ range (p ^ R), f (p * k) := by
    symm
    refine Finset.sum_bij (fun k _ => p * k) ?_ ?_ ?_ ?_
    · intro k hk
      simp only [mem_filter, mem_range]
      refine ⟨?_, dvd_mul_right _ _⟩
      have hk' : k < p ^ R := mem_range.mp hk
      rw [pow_succ, mul_comm (p ^ R)]
      exact Nat.mul_lt_mul_of_pos_left hk' (by omega)
    · intro k₁ _ k₂ _ he
      exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < p) he
    · intro j hj
      have hj' := mem_filter.mp hj
      obtain ⟨k, hk⟩ := hj'.2
      refine ⟨k, ?_, hk.symm⟩
      rw [mem_range]
      have hlt : j < p ^ (R + 1) := mem_range.mp hj'.1
      rw [hk, pow_succ, mul_comm (p ^ R)] at hlt
      exact Nat.lt_of_mul_lt_mul_left hlt
    · intro k _
      rfl
  have hdiv : (∑ j ∈ range (p ^ (R + 1)) with p ∣ j,
      (j : ℚ) ^ (N - 1) * ((a * j) / (p ^ (R + 1)) : ℕ)) =
      (p : ℚ) ^ (N - 1) * ∑ j ∈ range (p ^ R),
        (j : ℚ) ^ (N - 1) * ((a * j) / (p ^ R) : ℕ) := by
    rw [hsplit, mul_sum]
    apply sum_congr rfl
    intro k _
    rw [Nat.cast_mul, mul_pow]
    have he : (a * (p * k)) / (p ^ (R + 1)) = (a * k) / (p ^ R) := by
      rw [show a * (p * k) = p * (a * k) by ring, pow_succ, mul_comm (p ^ R)]
      exact Nat.mul_div_mul_left _ _ (by omega : 0 < p)
    rw [he]
    ring
  have hs := Finset.sum_filter_add_sum_filter_not (s := range (p ^ (R + 1)))
    (f := fun j => (j : ℚ) ^ (N - 1) * ((a * j) / (p ^ (R + 1)) : ℕ)) (fun j => p ∣ j)
  dsimp only [powerSum]
  rw [← hs, hdiv]
  ring

/-- The power sums restricted to units approximate
`(1 - p^(N-1))(a^N - 1) B_N / N` p-adically. -/
lemma tendsto_padicNorm_sub_powerSum_sub_scaled {p a N : ℕ} [Fact p.Prime] (hN : 1 ≤ N)
    (ha : ¬ p ∣ a) :
    Tendsto (fun R : ℕ => padicNorm p
      ((1 - (p : ℚ) ^ (N - 1)) * (((a : ℚ) ^ N - 1) * _root_.bernoulli N / N) -
        (powerSum a (p ^ (R + 1)) N - (p : ℚ) ^ (N - 1) * powerSum a (p ^ R) N)))
      atTop (𝓝 0) := by
  let q : ℚ := ((a : ℚ) ^ N - 1) * _root_.bernoulli N / N
  have hlim := tendsto_padicNorm_sub_powerSum (p := p) hN ha
  have hlim' := hlim.comp (tendsto_add_atTop_nat 1)
  have hupper := hlim'.add ((tendsto_const_nhds : Tendsto
    (fun _ : ℕ => padicNorm p ((p : ℚ) ^ (N - 1))) atTop
      (𝓝 (padicNorm p ((p : ℚ) ^ (N - 1))))).mul hlim)
  simp only [mul_zero, add_zero] at hupper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun R => padicNorm.nonneg _) (fun R => ?_)
  have he : (1 - (p : ℚ) ^ (N - 1)) * q -
      (powerSum a (p ^ (R + 1)) N - (p : ℚ) ^ (N - 1) * powerSum a (p ^ R) N) =
        (q - powerSum a (p ^ (R + 1)) N) +
          -((p : ℚ) ^ (N - 1) * (q - powerSum a (p ^ R) N)) := by ring
  rw [he]
  simpa only [padicNorm.neg, padicNorm.mul, Function.comp_def, q] using
    padicNorm.triangle_ineq (p := p)
    (q - powerSum a (p ^ (R + 1)) N) (-((p : ℚ) ^ (N - 1) * (q - powerSum a (p ^ R) N)))

/-- Unit-restricted power sums at congruent positive indices differ by a rational
with p-adic norm at most `p^(-ℓ-1)`. -/
lemma padicNorm_powerSum_sub_scaled_sub_le {p a m n ℓ R : ℕ} [Fact p.Prime] (ha : ¬ p ∣ a)
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hmn : m ≡ n [MOD (p - 1) * p ^ ℓ]) :
    padicNorm p ((powerSum a (p ^ (R + 1)) m - (p : ℚ) ^ (m - 1) * powerSum a (p ^ R) m) -
      (powerSum a (p ^ (R + 1)) n - (p : ℚ) ^ (n - 1) * powerSum a (p ^ R) n)) ≤
        (p : ℚ) ^ (-((ℓ + 1 : ℕ) : ℤ)) := by
  have hp : p.Prime := Fact.out
  rw [powerSum_sub_scaled_eq_sum_not_dvd hp.one_le, powerSum_sub_scaled_eq_sum_not_dvd hp.one_le]
  let M := p ^ (ℓ + 1)
  have hmod := Nat.ModEq.sub_right hm hn hmn
  have hpow (j : ℕ) (hj : ¬ p ∣ j) : (p : ℤ) ^ (ℓ + 1) ∣
      (a * j : ℤ) ^ (m - 1) - (a * j : ℤ) ^ (n - 1) := by
    have hnot : ¬ p ∣ a * j := fun h => (hp.dvd_mul.mp h).elim ha hj
    have hc : (a * j).Coprime M := ((hp.coprime_iff_not_dvd).mpr hnot).symm.pow_right (ℓ + 1)
    have ht := Nat.ModEq.pow_totient hc
    have hphi : M.totient = (p - 1) * p ^ ℓ := by
      dsimp only [M]
      rw [Nat.totient_prime_pow hp (by omega), show ℓ + 1 - 1 = ℓ by omega, mul_comm]
    have hunit : ((a * j : ℕ) : ZMod M) ^ ((p - 1) * p ^ ℓ) = 1 := by
      rw [← hphi]
      simpa only [Nat.cast_pow, Nat.cast_one] using (ZMod.natCast_eq_natCast_iff _ _ _).mpr ht
    have he := pow_eq_pow_of_modEq hmod hunit
    have hz : (((a * j : ℤ) ^ (m - 1) - (a * j : ℤ) ^ (n - 1) : ℤ) : ZMod M) = 0 := by
      push_cast
      exact sub_eq_zero.mpr (by simpa only [Nat.cast_mul] using he)
    simpa only [M, Nat.cast_pow] using (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
  let I : ℤ := ∑ j ∈ range (p ^ (R + 1)) with ¬ p ∣ j,
    ((a * j : ℤ) ^ (m - 1) - (a * j : ℤ) ^ (n - 1)) * ((a * j) / (p ^ (R + 1)) : ℕ)
  have hI : (p : ℤ) ^ (ℓ + 1) ∣ I := by
    apply Finset.dvd_sum
    intro j hj
    exact dvd_mul_of_dvd_left (hpow j (mem_filter.mp hj).2) _
  have hnorm := (padicNorm.dvd_iff_norm_le (p := p) (n := ℓ + 1) (z := I)).mp
    (by simpa only [Nat.cast_pow] using hI)
  have he : (a : ℚ) ^ (m - 1) * (∑ j ∈ range (p ^ (R + 1)) with ¬ p ∣ j,
      (j : ℚ) ^ (m - 1) * ((a * j) / (p ^ (R + 1)) : ℕ)) -
      (a : ℚ) ^ (n - 1) * (∑ j ∈ range (p ^ (R + 1)) with ¬ p ∣ j,
        (j : ℚ) ^ (n - 1) * ((a * j) / (p ^ (R + 1)) : ℕ)) = (I : ℚ) := by
    dsimp only [I]
    simp only [Int.cast_sum, Int.cast_mul, Int.cast_sub, Int.cast_pow, Int.cast_natCast]
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro j _
    rw [mul_pow, mul_pow]
    ring
  rw [he]
  exact hnorm

end Bernoulli.Regularization
