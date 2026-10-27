/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Combinatorics.Permutations

/-!
# Counting techniques (DLMF §26.18)

The inclusion–exclusion principle (26.18.1) is Mathlib's
`Finset.inclusion_exclusion_card_inf_compl` (pointer in `MathlibCoverageB`; the `t = ∅` term of
Mathlib's sum is DLMF's `|S|`). This file states the three examples.

Correction: in (26.18.4) the sum must run to `t = k`, not `t = n`. As printed it fails whenever
`n ≤ k - 2` (for instance `n = 1`, `k = 3`: `3 - 3·2 = -3`, while there are no onto maps); the
printed upper limit is harmless only for `k ≤ n + 1`. The corrected sum is acquired.

## References

* NIST DLMF §26.18.
-/

@[expose] public section

noncomputable section

open Finset

namespace DLMF.Combinatorics

/-- Counting a filter of the subtype `Icc 1 N` as a filter of `Icc 1 N`. -/
private lemma q26b_card_subtype (N : ℕ) (Q : ℕ → Prop) [DecidablePred Q] :
    #{m : {m // m ∈ (Finset.Icc 1 N : Finset ℕ)} | Q m.1} = #{m ∈ Icc 1 N | Q m} := by
  refine Finset.card_bij (fun a _ => a.1) ?_ ?_ ?_
  · intro a ha; simp only [mem_filter, mem_univ, true_and] at ha ⊢; exact ⟨a.2, ha⟩
  · intro a _ b _ h; exact Subtype.ext h
  · intro b hb
    simp only [mem_filter] at hb
    exact ⟨⟨b, hb.1⟩, by simp [hb.2], rfl⟩

/-- (26.18.2): the number of positive integers `≤ N` not divisible by any of the distinct primes
`p_1, …, p_n` is `N + ∑_{t=1}^n (-1)^t ∑_{j_1 < ⋯ < j_t} ⌊N/(p_{j_1} ⋯ p_{j_t})⌋`. -/
@[dlmf 26.18.E2]
theorem card_not_dvd_primes {n : ℕ} (p : Fin n → ℕ) (hp : ∀ j, (p j).Prime)
    (hinj : Function.Injective p) (N : ℕ) :
    (#{m ∈ Icc 1 N | ∀ j, ¬ p j ∣ m} : ℤ) =
      N + ∑ t ∈ (univ : Finset (Fin n)).powerset with t.Nonempty,
        (-1 : ℤ) ^ #t * (N / ∏ j ∈ t, p j : ℕ) := by
  classical
  let S : Fin n → Finset {m // m ∈ (Finset.Icc 1 N : Finset ℕ)} := fun j =>
    univ.filter fun m => p j ∣ m.1
  have hL : #{m ∈ Icc 1 N | ∀ j, ¬ p j ∣ m} = #((univ : Finset (Fin n)).inf fun j => (S j)ᶜ) := by
    rw [← q26b_card_subtype]
    congr 1
    ext m
    rw [q26b_mem_inf]
    simp [S]
  have hdvd : ∀ (t : Finset (Fin n)) (m : ℕ), (∀ j ∈ t, p j ∣ m) ↔ ∏ j ∈ t, p j ∣ m := by
    intro t m
    constructor
    · intro h
      rw [show ∏ j ∈ t, p j = ∏ x ∈ t.image p, x from
        (Finset.prod_image (f := id) (fun a _ b _ h => hinj h)).symm]
      refine Finset.prod_primes_dvd m ?_ ?_
      · intro a ha; obtain ⟨j, -, rfl⟩ := mem_image.mp ha; exact (hp j).prime
      · intro a ha; obtain ⟨j, hj, rfl⟩ := mem_image.mp ha; exact h j hj
    · intro h j hj; exact (Finset.dvd_prod_of_mem p hj).trans h
  have hR : ∀ t : Finset (Fin n), #(t.inf S) = N / ∏ j ∈ t, p j := by
    intro t
    have : t.inf S =
        univ.filter fun m : {m // m ∈ (Finset.Icc 1 N : Finset ℕ)} => ∏ j ∈ t, p j ∣ m.1 := by
      ext m
      rw [q26b_mem_inf]
      simp [S, ← hdvd]
    rw [this, q26b_card_subtype]
    rw [show Icc 1 N = Ioc 0 N from Finset.Icc_add_one_left_eq_Ioc 0 N,
      Nat.Ioc_filter_dvd_card_eq_div]
  rw [hL, inclusion_exclusion_card_inf_compl]
  simp_rw [hR]
  rw [← Finset.add_sum_erase _ _ (empty_mem_powerset _)]
  have hset : (univ : Finset (Fin n)).powerset.erase ∅ =
      (univ : Finset (Fin n)).powerset.filter (·.Nonempty) := by
    ext t; simp [nonempty_iff_ne_empty]
  rw [hset]
  simp

/-- No rooks: `r_0(B) = 1`. -/
lemma c26b_rookNumber_zero {n : ℕ} (B : Finset (Fin n × Fin n)) : rookNumber B 0 = 1 := by
  unfold rookNumber
  rw [Finset.card_eq_one]
  refine ⟨∅, ?_⟩
  ext C
  simp only [mem_filter, mem_powerset, card_eq_zero, mem_singleton]
  constructor
  · rintro ⟨_, h, _⟩; exact h
  · rintro rfl; exact ⟨empty_subset _, rfl, by simp [IsNonattacking]⟩

/-- (26.18.3): the number of placements of `n` nonattacking rooks on an `n × n` board avoiding
the squares of `B` (the permutations avoiding `B`, `N_0(B)` of §26.15) is
`n! + ∑_{t=1}^n (-1)^t r_t(B) (n-t)!`. -/
@[dlmf 26.18.E3]
theorem hitNumber_zero_eq_inclusion_exclusion {n : ℕ} (B : Finset (Fin n × Fin n)) :
    (hitNumber B 0 : ℤ) =
      n.factorial + ∑ t ∈ Icc 1 n, (-1 : ℤ) ^ t * rookNumber B t * (n - t).factorial := by
  rw [(hitNumber_zero_eq B).2, Finset.sum_range_succ', c26b_rookNumber_zero]
  have hI : Icc 1 n = (range n).image (· + 1) := by
    ext t; simp only [mem_Icc, mem_image, mem_range]
    constructor
    · intro h; exact ⟨t - 1, by omega, by omega⟩
    · rintro ⟨a, ha, rfl⟩; omega
  rw [hI, Finset.sum_image (fun a _ b _ h => by simpa using h)]
  simp only [pow_zero, Nat.cast_one, one_mul, Nat.sub_zero]
  ring

/-- (26.18.4), corrected: the number of ways of placing `n` labeled objects into `k` labeled
boxes with no box empty (the onto maps `Fin n → Fin k`) is `∑_{t=0}^k (-1)^t C(k, t) (k-t)ⁿ`
(DLMF prints the upper limit `n`; see the module docstring). -/
@[dlmf 26.18.E4 "corrected: upper limit k (printed n); fails as printed for n ≤ k - 2"]
theorem card_surjective_eq_sum (n k : ℕ) :
    (#{f : Fin n → Fin k | Function.Surjective f} : ℤ) =
      ∑ t ∈ range (k + 1), (-1 : ℤ) ^ t * k.choose t * ((k - t : ℕ) : ℤ) ^ n :=
  q26b_card_surjective_eq_alternating_sum n k

end DLMF.Combinatorics
