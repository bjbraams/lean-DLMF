/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Combinatorics.RestrictedPartitions
public import DLMF.Bessel.Modified
public import Mathlib.Combinatorics.Enumerative.Partition.Glaisher
public import Mathlib.Combinatorics.Enumerative.Pentagonal.Basic
public import DLMF.QSeries.QExponential
public import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries
public import Mathlib.RingTheory.PowerSeries.Expand
public import DLMF.Combinatorics.S26aStaircase
public import DLMF.Bailey
public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Analytic.Uniqueness

/-!
# Integer partitions: other restrictions (DLMF §26.10)

Restricted partition counts of DLMF §26.10(i), on Mathlib's `Nat.Partition`:

* `p(𝒟, n)` (`partitionCountDistinct`) is `#(Nat.Partition.distincts n)`; `p(𝒪, n)`
  (`partitionCountOdd`) is `#(Nat.Partition.odds n)`;
* `p_m(𝒟, n)` (`partitionCountAtMostDistinct`): at most `m` distinct parts;
  `p_m(≤ k, 𝒟, n)` (`partitionCountAtMostDistinctBoxed`): moreover every part at most `k`;
* `p(𝒟k, n)` (`partitionCountDiff`): any two parts differ by at least `k`
  (`PartsDifferAtLeast`; for `k = 0` all partitions, for `k = 1` distinct parts);
* `p(𝒟'3, n)` (`partitionCountSchur`): parts differ by at least 3 and multiples of 3 by at
  least 6;
* `p(∈ S, n)` (`partitionCountIn`): parts taken from `S`; `A_{j,k}` is `residueSetPM j k`
  and `T = {2, 3, …}` is `setGeTwo`. Combined restrictions are conjunctions.

Euler's identity (26.10.12) is Mathlib's `Nat.Partition.card_odds_eq_card_distincts` (pointer in
`MathlibCoverageB`).

Corrections (all verified by brute force in Python, `n < 40`):

* (26.10.9) as printed, `p_m(𝒟, n) = p_m(𝒟, n - m) + p_{m-1}(𝒟, n)`, is false for the stated
  definition (`m = n = 2`: `1 ≠ 2`). Removing one from each of `m` distinct parts leaves `m` or
  `m - 1` distinct parts, so the correct analogue of (26.9.8) is
  `p_m(𝒟, n) = p_{m-1}(𝒟, n) + p_m(𝒟, n - m) - p_{m-2}(𝒟, n - m)` (equivalently, for exactly
  `m` distinct parts, `q_m(n) = q_m(n - m) + q_{m-1}(n - m)`); this is acquired.
* §26.10(iv): `p(𝒟'3, n) < p(𝒟3, n)` holds for `n = 9` and `n ≥ 15`, not for all `n ≥ 9`:
  `p(𝒟'3, n) = p(𝒟3, n)` for `10 ≤ n ≤ 14` (for instance both are 4 at `n = 10`). The
  corrected range is acquired.
* (26.10.18): the sum over `1 < h ≤ k` would make `A_1(n) = 0` and the leading term of
  (26.10.17) vanish; with `1 ≤ h ≤ k` the series reproduces `p(𝒟, n)` (mpmath, `n ≤ 20`). The
  corrected range is acquired.
* (26.10.7), (26.10.8): the printed sums over `k ≥ 0` with both signs `±` (the `k = 0` term once)
  are sums over `k ∈ ℤ` of the pentagonal numbers `k(3k-1)/2` (Mathlib's `pentagonal`).

## References

* NIST DLMF §26.10.
-/

@[expose] public section

noncomputable section

open Finset Filter Asymptotics
open DLMF.QSeries DLMF.Partitions

namespace DLMF.Combinatorics

/-- `p(𝒟, n)`: partitions of `n` into distinct parts (DLMF §26.10(i)). -/
@[dlmf 26.10.i]
def partitionCountDistinct (n : ℕ) : ℕ := #(Nat.Partition.distincts n)

/-- `p(𝒪, n)`: partitions of `n` into odd parts (DLMF §26.10(i)). -/
@[dlmf 26.10.i]
def partitionCountOdd (n : ℕ) : ℕ := #(Nat.Partition.odds n)

/-- `p_m(𝒟, n)`: partitions of `n` into at most `m` distinct parts (DLMF §26.10(i)). -/
@[dlmf 26.10.i]
def partitionCountAtMostDistinct (m n : ℕ) : ℕ :=
  #{p ∈ Nat.Partition.distincts n | p.parts.card ≤ m}

/-- `p_m(≤ k, 𝒟, n)`: partitions of `n` into at most `m` distinct parts, each at most `k`
(DLMF (26.10.3)). -/
@[dlmf 26.10.E3]
def partitionCountAtMostDistinctBoxed (m k n : ℕ) : ℕ :=
  #{p ∈ Nat.Partition.distincts n | p.parts.card ≤ m ∧ ∀ i ∈ p.parts, i ≤ k}

/-- Any two parts of `p` (two different occurrences) differ by at least `k`. -/
def PartsDifferAtLeast {n : ℕ} (k : ℕ) (p : n.Partition) : Prop :=
  ∀ a ∈ p.parts, ∀ b ∈ p.parts.erase a, a + k ≤ b ∨ b + k ≤ a

instance {n : ℕ} (k : ℕ) (p : n.Partition) : Decidable (PartsDifferAtLeast k p) := by
  unfold PartsDifferAtLeast; infer_instance

/-- `p(𝒟k, n)`: partitions of `n` into parts with difference at least `k` (DLMF §26.10(i)). -/
@[dlmf 26.10.i]
def partitionCountDiff (k n : ℕ) : ℕ := #{p : n.Partition | PartsDifferAtLeast k p}

/-- Schur's condition: parts differ by at least 3, and multiples of 3 by at least 6. -/
def SchurCondition {n : ℕ} (p : n.Partition) : Prop :=
  PartsDifferAtLeast 3 p ∧
    ∀ a ∈ p.parts, ∀ b ∈ p.parts.erase a, 3 ∣ a → 3 ∣ b → a + 6 ≤ b ∨ b + 6 ≤ a

instance {n : ℕ} (p : n.Partition) : Decidable (SchurCondition p) := by
  unfold SchurCondition; infer_instance

/-- `p(𝒟'3, n)`: partitions of `n` into parts with difference at least 3, except that
multiples of 3 must differ by at least 6 (DLMF §26.10(i)). -/
@[dlmf 26.10.i]
def partitionCountSchur (n : ℕ) : ℕ := #{p : n.Partition | SchurCondition p}

/-- `p(∈ S, n)`: partitions of `n` into parts taken from `S` (DLMF §26.10(i)). -/
@[dlmf 26.10.i]
def partitionCountIn (S : Set ℕ) [DecidablePred (· ∈ S)] (n : ℕ) : ℕ :=
  #(Nat.Partition.restricted n (· ∈ S))

/-- `A_{j,k} = {n ≥ 1 | n ≡ ±j (mod k)}` (DLMF §26.10(i)). -/
@[dlmf 26.10.i]
def residueSetPM (j k : ℕ) : Set ℕ :=
  {n | 1 ≤ n ∧ ((n : ℤ) ≡ j [ZMOD k] ∨ (n : ℤ) ≡ -j [ZMOD k])}

instance (j k : ℕ) : DecidablePred (· ∈ residueSetPM j k) := fun n => by
  unfold residueSetPM; simp only [Set.mem_ofPred_eq]; infer_instance

/-- `T = {2, 3, 4, …}` (DLMF §26.10(i)). -/
@[dlmf 26.10.i]
def setGeTwo : Set ℕ := {n | 2 ≤ n}

instance : DecidablePred (· ∈ setGeTwo) := fun n => by
  unfold setGeTwo; simp only [Set.mem_ofPred_eq]; infer_instance

/-- `p(𝒟2, ∈ T, n)`: difference at least 2 and no part 1. -/
@[dlmf 26.10.i]
def partitionCountDiffTwoNoOne (n : ℕ) : ℕ :=
  #{p : n.Partition | PartsDifferAtLeast 2 p ∧ ∀ i ∈ p.parts, i ∈ setGeTwo}

/-- The partitions of `0`: there is exactly one. -/
lemma c26b_partition_zero_eq (p : (0 : ℕ).Partition) : p.parts = 0 := by
  refine Multiset.eq_zero_of_forall_notMem fun i hi => ?_
  have := p.parts_pos hi
  have := Nat.Partition.le_of_mem_parts hi
  omega

lemma c26b_card_filter_partition_zero (P : (0 : ℕ).Partition → Prop) [DecidablePred P]
    (h : ∀ p, p.parts = 0 → P p) : #{p : (0 : ℕ).Partition | P p} = 1 := by
  rw [Finset.filter_true_of_mem fun p _ => h p (c26b_partition_zero_eq p), card_univ]
  exact partitionFunction_zero

/-- (26.10.1): `p(𝒟, 0) = p(𝒟k, 0) = p(∈ S, 0) = 1`. -/
@[dlmf 26.10.E1]
theorem partitionCount_zero (k : ℕ) (S : Set ℕ) [DecidablePred (· ∈ S)] :
    partitionCountDistinct 0 = 1 ∧ partitionCountDiff k 0 = 1 ∧ partitionCountIn S 0 = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold partitionCountDistinct Nat.Partition.distincts
    exact c26b_card_filter_partition_zero _ fun p hp => by rw [hp]; simp
  · unfold partitionCountDiff
    exact c26b_card_filter_partition_zero _ fun p hp => by
      unfold PartsDifferAtLeast; rw [hp]; simp
  · unfold partitionCountIn Nat.Partition.restricted
    exact c26b_card_filter_partition_zero _ fun p hp => by rw [hp]; simp

/-- `(w; q)_∞` as an unconditional product. -/
lemma r26a_hasProd_one_sub {w q : ℂ} (hq : ‖q‖ < 1) :
    HasProd (fun k : ℕ => 1 - w * q ^ k) (qPochhammerInf w q) :=
  (multipliable_one_sub_mul_pow hq).hasProd

/-- `∏_{j ≥ 1} (1 + q^j) = (-q; q)_∞`. -/
lemma r26a_tprod_one_add_eq {q : ℂ} :
    ∏' j : ℕ, (1 + q ^ (j + 1)) = qPochhammerInf (-q) q := by
  unfold qPochhammerInf
  congr 1; ext j; ring

/-- `∏_{j ≥ 1} (1 + q^j)` converges unconditionally for `|q| < 1`. -/
lemma r26a_hasProd_one_add {q : ℂ} (hq : ‖q‖ < 1) :
    HasProd (fun j : ℕ => 1 + q ^ (j + 1)) (∏' j : ℕ, (1 + q ^ (j + 1))) := by
  rw [r26a_tprod_one_add_eq]
  convert r26a_hasProd_one_sub (w := -q) hq using 2 with j
  ring

/-- Removing `k` copies of an allowed part `a`, keeping track of the remaining multiplicity. -/
lemma r26a_card_restricted_count_ge' (P : ℕ → Prop) [DecidablePred P] {a : ℕ} (ha1 : 1 ≤ a)
    (hP : P a) (Q : ℕ → Prop) [DecidablePred Q] : ∀ k n : ℕ, k * a ≤ n →
      #{p ∈ Nat.Partition.restricted n P | k ≤ p.parts.count a ∧ Q (p.parts.count a - k)} =
        #{q ∈ Nat.Partition.restricted (n - k * a) P | Q (q.parts.count a)} := by
  intro k
  induction k with
  | zero =>
    intro n _
    rw [zero_mul, Nat.sub_zero]
    congr 1
  | succ k ih =>
    intro n hn
    have ha : a ≤ n := by nlinarith
    rw [show n - (k + 1) * a = n - a - k * a by rw [add_mul, one_mul]; omega,
      ← ih (n - a) (by rw [add_mul, one_mul] at hn; omega)]
    let e := Nat.Partition.partitionWithPartEquiv ha1 ha
    refine card_bij (fun p hp => e ⟨p, ?_⟩) ?_ ?_ ?_
    · simp only [mem_filter] at hp
      exact Multiset.count_pos.mp (by omega)
    · intro p hp
      simp only [mem_filter, Nat.Partition.restricted, mem_univ, true_and] at hp ⊢
      rw [Nat.Partition.partitionWithPartEquiv_apply_parts]
      refine ⟨fun i hi => hp.1 i (Multiset.mem_of_mem_erase hi), ?_⟩
      rw [Multiset.count_erase_self]
      refine ⟨Nat.le_sub_of_add_le hp.2.1, ?_⟩
      have := hp.2.2
      rwa [show Multiset.count a p.parts - 1 - k = Multiset.count a p.parts - (k + 1) by omega]
    · intro p _ p' _ h
      exact congrArg Subtype.val (e.injective h)
    · intro q hq
      simp only [mem_filter, Nat.Partition.restricted, mem_univ, true_and] at hq
      refine ⟨(e.symm q).1, ?_, by simp⟩
      simp only [mem_filter, Nat.Partition.restricted, mem_univ, true_and,
        Nat.Partition.partitionWithPartEquiv_symm_apply_parts, e]
      refine ⟨fun i hi => ?_, ?_⟩
      · rcases Multiset.mem_cons.mp hi with rfl | hi
        · exact hP
        · exact hq.1 i hi
      · obtain ⟨-, hq1, hq2⟩ := hq
        rw [Multiset.count_cons_self]
        refine ⟨by omega, ?_⟩
        rwa [show Multiset.count a q.parts + 1 - (k + 1) = Multiset.count a q.parts - k by omega]

/-- Adjoining an allowed part `a ∉ P`: `p(P ∪ {a}, n) = ∑_{m a ≤ n} p(P, n - m a)`. -/
lemma r26a_card_restricted_insert (P : ℕ → Prop) [DecidablePred P] {a : ℕ} (ha1 : 1 ≤ a)
    (hPa : ¬ P a) (n : ℕ) :
    #(Nat.Partition.restricted n (fun i => i = a ∨ P i)) =
      ∑ m ∈ range (n + 1) with m * a ≤ n, #(Nat.Partition.restricted (n - m * a) P) := by
  set P' : ℕ → Prop := fun i => i = a ∨ P i
  have hcount : ∀ p : n.Partition, p.parts.count a ∈ range (n + 1) := by
    intro p
    have := Multiset.count_le_card a p.parts
    have h2 := Multiset.card_nsmul_le_sum (s := p.parts) (a := 1) fun i hi => p.parts_pos hi
    rw [smul_eq_mul, mul_one, p.parts_sum] at h2
    exact mem_range.mpr (by omega)
  rw [card_eq_sum_card_fiberwise (f := fun p : n.Partition => p.parts.count a)
    (t := range (n + 1)) fun p _ => hcount p, ← sum_filter_add_sum_filter_not (range (n + 1))
    (fun m => m * a ≤ n), sum_eq_zero (s := (range (n + 1)).filter fun m => ¬ m * a ≤ n), add_zero]
  · refine sum_congr rfl fun m hm => ?_
    simp only [mem_filter] at hm
    have h := r26a_card_restricted_count_ge' P' ha1 (Or.inl rfl) (· = 0) m n hm.2
    have e1 : ({p ∈ Nat.Partition.restricted n P' | p.parts.count a = m} : Finset _) =
        {p ∈ Nat.Partition.restricted n P' | m ≤ p.parts.count a ∧ p.parts.count a - m = 0} :=
      filter_congr fun p _ => by omega
    have e2 : ({q ∈ Nat.Partition.restricted (n - m * a) P' | q.parts.count a = 0} : Finset _) =
        Nat.Partition.restricted (n - m * a) P := by
      unfold Nat.Partition.restricted
      rw [filter_filter]
      refine filter_congr fun q _ =>
        ⟨fun ⟨h1, h2⟩ i hi => ?_, fun h1 => ⟨fun i hi => Or.inr (h1 i hi), ?_⟩⟩
      · rcases h1 i hi with rfl | h
        · exact absurd (Multiset.count_pos.mpr hi) (by omega)
        · exact h
      · exact Multiset.count_eq_zero.mpr fun ha => hPa (h1 a ha)
    rw [e1, h, e2]
  · intro m hm
    simp only [mem_filter, not_le] at hm
    rw [card_eq_zero, filter_eq_empty_iff]
    intro p _ hp
    have : p.parts.count a * a ≤ n := by
      obtain ⟨u, hu⟩ := Multiset.le_iff_exists_add.mp
        (Multiset.le_count_iff_replicate_le.mp (le_refl (p.parts.count a)))
      calc p.parts.count a * a = (Multiset.replicate (p.parts.count a) a).sum := by simp
        _ ≤ (Multiset.replicate (p.parts.count a) a).sum + u.sum := Nat.le_add_right _ _
        _ = p.parts.sum := by rw [← Multiset.sum_add, ← hu]
        _ = n := p.parts_sum
    rw [hp] at this
    omega


/-- Partitions with all parts in `∅`: only the empty partition of `0`. -/
lemma r26a_card_restricted_false (n : ℕ) :
    #(Nat.Partition.restricted n (· ∈ (∅ : Finset ℕ))) = if n = 0 then 1 else 0 := by
  split_ifs with hn
  · subst hn
    rw [card_eq_one]
    refine ⟨default, eq_singleton_iff_unique_mem.mpr ⟨?_, fun p _ => Subsingleton.elim _ _⟩⟩
    simp [Nat.Partition.restricted]
  · rw [card_eq_zero, Nat.Partition.restricted, filter_eq_empty_iff]
    intro p _ hp
    obtain ⟨x, hx⟩ : ∃ x, x ∈ p.parts := by
      by_contra h0
      push Not at h0
      have := p.parts_sum
      rw [Multiset.eq_zero_of_forall_notMem h0, Multiset.sum_zero] at this
      omega
    simpa using hp x hx

/-- The geometric series `∑_m q^{a m}` as a series in `n` supported on multiples of `a`. -/
lemma r26a_hasSum_dvd {a : ℕ} (ha : 1 ≤ a) {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ => (if a ∣ n then (1 : ℂ) else 0) * q ^ n) (1 - q ^ a)⁻¹ := by
  have hqa : ‖q ^ a‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq (by omega)
  have h := hasSum_geometric_of_norm_lt_one hqa
  rw [← (mul_right_injective₀ (by omega : a ≠ 0)).hasSum_iff]
  · convert h using 1
    ext m
    simp [pow_mul]
  · intro n hn
    have : ¬ a ∣ n := by rintro ⟨m, rfl⟩; exact hn ⟨m, rfl⟩
    simp [this]

/-- (26.10.5) for a finite set of allowed parts. -/
lemma r26a_hasSum_restricted_finset (T : Finset ℕ) (hT : 0 ∉ T) : ∀ q : ℂ, ‖q‖ < 1 →
    HasSum (fun n => (#(Nat.Partition.restricted n (· ∈ T)) : ℂ) * q ^ n)
      (∏ j ∈ T, (1 - q ^ j)⁻¹) := by
  induction T using Finset.induction_on with
  | empty =>
    intro q _
    simp_rw [r26a_card_restricted_false, prod_empty]
    convert hasSum_ite_eq 0 (1 : ℂ) using 1
    ext n
    split_ifs <;> simp_all
  | insert a T haT ih =>
    intro q hq
    have ha : 1 ≤ a := Nat.pos_of_ne_zero fun h => hT (h ▸ mem_insert_self a T)
    have hT0 : 0 ∉ T := fun h => hT (mem_insert_of_mem h)
    have hc : ∀ n, #(Nat.Partition.restricted n (· ∈ insert a T)) =
        ∑ m ∈ range (n + 1) with m * a ≤ n, #(Nat.Partition.restricted (n - m * a) (· ∈ T)) := by
      intro n
      rw [← r26a_card_restricted_insert (· ∈ T) ha haT n]
      congr 1
      exact filter_congr fun p _ => by simp [mem_insert]
    set c : ℕ → ℕ := fun n => #(Nat.Partition.restricted n (· ∈ T))
    have hf := ih hT0 q hq
    have hfn : Summable fun n => ‖(c n : ℂ) * q ^ n‖ := by
      have h := (ih hT0 (‖q‖ : ℂ) (by simpa using hq)).summable
      have h2 : Summable fun n => ((c n * ‖q‖ ^ n : ℝ) : ℂ) := by
        convert h using 2 with n; push_cast; rfl
      convert Complex.summable_ofReal.mp h2 using 2 with n
      rw [norm_mul, norm_pow, Complex.norm_natCast]
    have hg := r26a_hasSum_dvd ha hq
    have hgn : Summable fun n : ℕ => ‖(if a ∣ n then (1 : ℂ) else 0) * q ^ n‖ := by
      refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
        (summable_geometric_of_lt_one (norm_nonneg q) hq)
      rw [norm_mul, norm_pow]
      split_ifs <;> simp
    have hprod := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hfn hgn
    have hsum := (summable_norm_sum_mul_antidiagonal_of_summable_norm hfn hgn).of_norm
    rw [hf.tsum_eq, hg.tsum_eq] at hprod
    rw [prod_insert haT, mul_comm, hprod]
    convert hsum.hasSum using 2 with n
    rw [hc, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Nat.cast_sum, sum_mul]
    have hterm : ∀ k ∈ range (n + 1),
        (c k : ℂ) * q ^ k * ((if a ∣ n - k then 1 else 0) * q ^ (n - k))
        = if a ∣ n - k then (c k : ℂ) * q ^ n else 0 := by
      intro k hk
      have : k + (n - k) = n := by simp at hk; omega
      split_ifs
      · rw [one_mul, mul_assoc, ← pow_add, this]
      · simp
    rw [sum_congr rfl hterm, ← sum_filter]
    symm
    refine sum_nbij' (fun k => (n - k) / a) (fun m => n - m * a) ?_ ?_ ?_ ?_ ?_
    · intro k hk
      simp only [mem_filter, mem_range] at hk ⊢
      obtain ⟨hk1, j, hj⟩ := hk
      rw [hj, Nat.mul_div_cancel_left _ (by omega)]
      have h1 : a * j ≤ n := by omega
      exact ⟨by nlinarith, by rw [mul_comm]; exact h1⟩
    · intro m hm
      simp only [mem_filter, mem_range] at hm ⊢
      exact ⟨by omega, ⟨m, by rw [show n - (n - m * a) = m * a by omega, mul_comm]⟩⟩
    · intro k hk
      simp only [mem_filter, mem_range] at hk
      obtain ⟨hk1, j, hj⟩ := hk
      rw [hj, Nat.mul_div_cancel_left _ (by omega), mul_comm]
      omega
    · intro m hm
      simp only [mem_filter, mem_range] at hm
      rw [show n - (n - m * a) = m * a by omega, Nat.mul_div_cancel _ (by omega)]
    · intro k hk
      simp only [mem_filter, mem_range] at hk
      obtain ⟨hk1, j, hj⟩ := hk
      rw [hj, Nat.mul_div_cancel_left _ (by omega), mul_comm, show n - j * a = k by
        rw [mul_comm]; omega]
      exact mul_comm _ _


/-- `∏_{j ∈ T} (1 - r^j)⁻¹ ≤ exp(1/(1-r)²)` for `0 ≤ r < 1` and `0 ∉ T`. -/
lemma r26a_prod_inv_le {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) (T : Finset ℕ) (hT : 0 ∉ T) :
    ∏ j ∈ T, (1 - r ^ j)⁻¹ ≤ Real.exp (1 / (1 - r) ^ 2) := by
  have h1r : 0 < 1 - r := by linarith
  have hfac : ∀ j ∈ T, (1 - r ^ j)⁻¹ ≤ Real.exp (r ^ j / (1 - r)) := by
    intro j hj
    have hj1 : 1 ≤ j := Nat.pos_of_ne_zero fun h => hT (h ▸ hj)
    have hrj : r ^ j ≤ r := pow_le_of_le_one hr0 hr.le (by omega)
    have hpos : 0 < 1 - r ^ j := by linarith
    calc (1 - r ^ j)⁻¹ = 1 + r ^ j / (1 - r ^ j) := by field_simp; ring
      _ ≤ 1 + r ^ j / (1 - r) := by gcongr
      _ ≤ _ := by linarith [Real.add_one_le_exp (r ^ j / (1 - r))]
  calc ∏ j ∈ T, (1 - r ^ j)⁻¹ ≤ ∏ j ∈ T, Real.exp (r ^ j / (1 - r)) :=
        Finset.prod_le_prod₀ (fun j hj => by
          have hj1 : 1 ≤ j := Nat.pos_of_ne_zero fun h => hT (h ▸ hj)
          have : r ^ j < 1 := pow_lt_one₀ hr0 hr (by omega)
          exact inv_nonneg.mpr (by linarith)) hfac
    _ = Real.exp (∑ j ∈ T, r ^ j / (1 - r)) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (1 / (1 - r) ^ 2) := by
        rw [Real.exp_le_exp, ← sum_div, div_le_div_iff₀ h1r (by positivity)]
        have hs : ∑ j ∈ T, r ^ j ≤ 1 / (1 - r) := by
          rw [one_div, ← tsum_geometric_of_lt_one hr0 hr]
          exact (summable_geometric_of_lt_one hr0 hr).sum_le_tsum _ (fun _ _ => by positivity)
        rw [le_div_iff₀ h1r] at hs
        nlinarith

/-- (26.10.5) for an arbitrary set of allowed positive parts (`0 ∉ S` is irrelevant: parts are
positive). -/
lemma r26a_hasSum_partitionCountIn {q : ℂ} (hq : ‖q‖ < 1) (S : Set ℕ) [DecidablePred (· ∈ S)] :
    HasSum (fun n => (partitionCountIn S n : ℂ) * q ^ n)
        (∏' j : ℕ, if j + 1 ∈ S then (1 - q ^ (j + 1))⁻¹ else 1) ∧
      HasProd (fun j : ℕ => if j + 1 ∈ S then (1 - q ^ (j + 1))⁻¹ else 1)
        (∏' j : ℕ, if j + 1 ∈ S then (1 - q ^ (j + 1))⁻¹ else 1) := by
  set f : ℂ → ℕ → ℂ := fun x j => if j + 1 ∈ S then (1 - x ^ (j + 1))⁻¹ else 1
  -- multipliability
  have hmult : ∀ x : ℂ, ‖x‖ < 1 → Multipliable (f x) := by
    intro x hx
    have h1x : 0 < 1 - ‖x‖ := by linarith
    have hu : ∀ j, f x j = 1 + (if j + 1 ∈ S then x ^ (j + 1) / (1 - x ^ (j + 1)) else 0) := by
      intro j
      show (if j + 1 ∈ S then (1 - x ^ (j + 1))⁻¹ else 1) = _
      split_ifs
      · have : 1 - x ^ (j + 1) ≠ 0 := by
          intro h
          have h2 : ‖x ^ (j + 1)‖ = 1 := by rw [← sub_eq_zero.mp h, norm_one]
          rw [norm_pow] at h2
          exact absurd h2 (pow_lt_one₀ (norm_nonneg _) hx (by omega)).ne
        field_simp; ring
      · simp
    rw [funext hu]
    refine multipliable_one_add_of_summable ?_
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => ?_)
      ((summable_geometric_of_lt_one (norm_nonneg x) hx).mul_left (1 / (1 - ‖x‖)))
    split_ifs
    · rw [norm_div, norm_pow]
      have hxj : ‖x‖ ^ (j + 1) ≤ ‖x‖ ^ j := pow_le_pow_of_le_one (norm_nonneg _) hx.le (by omega)
      have hden : 1 - ‖x‖ ≤ ‖1 - x ^ (j + 1)‖ := by
        have := norm_sub_norm_le (1 : ℂ) (x ^ (j + 1))
        rw [norm_one, norm_pow] at this
        have : ‖x‖ ^ (j + 1) ≤ ‖x‖ := pow_le_of_le_one (norm_nonneg _) hx.le (by omega)
        linarith
      calc ‖x‖ ^ (j + 1) / ‖1 - x ^ (j + 1)‖ ≤ ‖x‖ ^ j / (1 - ‖x‖) :=
            div_le_div₀ (by positivity) hxj h1x hden
        _ = 1 / (1 - ‖x‖) * ‖x‖ ^ j := by ring
    · simp only [norm_zero]; positivity
  refine ⟨?_, (hmult q hq).hasProd⟩
  -- truncations
  set T : ℕ → Finset ℕ := fun N => ((range N).filter fun j => j + 1 ∈ S).map (addRightEmbedding 1)
  have hT0 : ∀ N, 0 ∉ T N := by intro N h; simp [T] at h
  have hTS : ∀ N, ∀ i ∈ T N, i ∈ S := by
    intro N i hi; simp only [T, Finset.mem_map, mem_filter, addRightEmbedding_apply] at hi
    obtain ⟨j, ⟨_, hj⟩, rfl⟩ := hi; exact hj
  have hprodT : ∀ (x : ℂ) N, ∏ j ∈ T N, (1 - x ^ j)⁻¹ = ∏ j ∈ range N, f x j := by
    intro x N
    simp only [T, prod_map, addRightEmbedding_apply, f, prod_ite, prod_const_one, mul_one]
  set c : ℕ → ℕ := fun n => partitionCountIn S n
  set cN : ℕ → ℕ → ℕ := fun N n => #(Nat.Partition.restricted n (· ∈ T N))
  have hcle : ∀ N n, cN N n ≤ c n := by
    intro N n
    exact card_le_card fun p hp => by
      simp only [Nat.Partition.restricted, mem_filter, mem_univ, true_and] at hp ⊢
      exact fun i hi => hTS N i (hp i hi)
  have hceq : ∀ N n, n ≤ N → cN N n = c n := by
    intro N n hn
    simp only [cN, c, partitionCountIn]
    congr 1
    refine filter_congr fun p _ => ⟨fun h i hi => hTS N i (h i hi), fun h i hi => ?_⟩
    have h1 := p.parts_pos hi
    have h2 := Nat.Partition.le_of_mem_parts hi
    simp only [T, Finset.mem_map, mem_filter, mem_range, addRightEmbedding_apply]
    exact ⟨i - 1, ⟨by omega, by rw [Nat.sub_add_cancel h1]; exact h i hi⟩, Nat.sub_add_cancel h1⟩
  -- real bound at `r = ‖q‖`
  set r := ‖q‖
  have hr0 : 0 ≤ r := norm_nonneg q
  have hreal : ∀ N, HasSum (fun n => (cN N n : ℝ) * r ^ n) (∏ j ∈ T N, (1 - r ^ j)⁻¹) := by
    intro N
    have h := r26a_hasSum_restricted_finset (T N) (hT0 N) (r : ℂ) (by simpa [r] using hq)
    rw [← Complex.hasSum_ofReal]
    push_cast
    exact h
  have hsumc : Summable fun n => (c n : ℝ) * r ^ n := by
    refine summable_of_sum_range_le (c := Real.exp (1 / (1 - r) ^ 2))
      (fun n => by positivity) fun M => ?_
    calc ∑ n ∈ range M, (c n : ℝ) * r ^ n = ∑ n ∈ range M, (cN M n : ℝ) * r ^ n :=
          sum_congr rfl fun n hn => by rw [hceq M n (by simp at hn; omega)]
      _ ≤ ∏ j ∈ T M, (1 - r ^ j)⁻¹ :=
          sum_le_hasSum _ (fun n _ => by positivity) (hreal M)
      _ ≤ _ := r26a_prod_inv_le hr0 hq (T M) (hT0 M)
  have hsumq : Summable fun n => (c n : ℂ) * q ^ n :=
    Summable.of_norm_bounded hsumc fun n => by rw [norm_mul, norm_pow, Complex.norm_natCast]
  -- Tannery
  have hT := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun N n => (cN N n : ℂ) * q ^ n)
    (g := fun n => (c n : ℂ) * q ^ n) hsumc
    (fun n => tendsto_atTop_of_eventually_const (i₀ := n) fun N hN => by
      rw [hceq N n hN])
    (Eventually.of_forall fun N n => by
      rw [norm_mul, norm_pow, Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcle N n) (by positivity))
  have hT' : Tendsto (fun N => ∏ j ∈ range N, f q j) atTop
      (nhds (∑' n, (c n : ℂ) * q ^ n)) := by
    refine hT.congr fun N => ?_
    rw [(r26a_hasSum_restricted_finset (T N) (hT0 N) q hq).tsum_eq, hprodT]
  have := tendsto_nhds_unique hT' (hmult q hq).tendsto_prod_tprod_nat
  rw [← this]
  exact hsumq.hasSum

/-- (26.10.2), second equality: `∏_{j ≥ 1} (1 + q^j) = ∏_{j ≥ 1} (1 - q^{2j-1})⁻¹`. -/
@[dlmf 26.10.E2]
theorem hasProd_one_sub_odd_pow_inv {q : ℂ} (hq : ‖q‖ < 1) :
    HasProd (fun j : ℕ => (1 - q ^ (2 * j + 1))⁻¹) (∏' j : ℕ, (1 + q ^ (j + 1))) := by
  have hq2 : ‖q ^ 2‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq (by norm_num)
  set O := qPochhammerInf q (q ^ 2)
  set E := qPochhammerInf (q ^ 2) (q ^ 2)
  have hO : HasProd (fun j : ℕ => 1 - q ^ (2 * j + 1)) O := by
    convert r26a_hasProd_one_sub (w := q) hq2 using 2 with j; ring
  have hE : HasProd (fun j : ℕ => 1 - q ^ (2 * j + 2)) E := by
    convert r26a_hasProd_one_sub (w := q ^ 2) hq2 using 2 with j; ring
  have hO0 : O ≠ 0 :=
    qPochhammerInf_ne_zero_of_norm_lt_one (by simpa using hq.trans_le' (le_refl _)) hq2
  have hE0 : E ≠ 0 := qPochhammerInf_ne_zero_of_norm_lt_one hq2 hq2
  have hB : HasProd (fun j : ℕ => 1 - q ^ (j + 1)) (O * E) := by
    refine HasProd.even_mul_odd ?_ ?_
    · convert hO using 2 with k
    · convert hE using 2 with k
  have hA := r26a_hasProd_one_add hq
  have hAB := hA.mul hB
  have hAB' : HasProd (fun j : ℕ => 1 - q ^ (2 * j + 2))
      ((∏' j : ℕ, (1 + q ^ (j + 1))) * (O * E)) := by
    convert hAB using 2 with j; ring
  have heq := hAB'.unique hE
  have : ∏' j : ℕ, (1 + q ^ (j + 1)) = O⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    apply mul_right_cancel₀ hE0
    rw [one_mul, mul_assoc]; exact heq
  rw [this]
  exact hO.inv₀ hO0

/-- (26.10.2), first equality: `∑ p(𝒟, n) qⁿ = ∏_{j ≥ 1} (1 + q^j)` for `|q| < 1`. -/
@[dlmf 26.10.E2]
theorem hasSum_partitionCountDistinct {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n => (partitionCountDistinct n : ℂ) * q ^ n) (∏' j : ℕ, (1 + q ^ (j + 1))) ∧
      HasProd (fun j : ℕ => 1 + q ^ (j + 1)) (∏' j : ℕ, (1 + q ^ (j + 1))) := by
  have hodd := hasProd_one_sub_odd_pow_inv hq
  refine ⟨?_, r26a_hasProd_one_add hq⟩
  have hS := r26a_hasSum_partitionCountIn hq {j | Odd j}
  have hd : ∀ n, partitionCountDistinct n = partitionCountIn {j | Odd j} n := by
    intro n
    rw [partitionCountDistinct, ← Nat.Partition.card_odds_eq_card_distincts, partitionCountIn]
    congr 1
    exact filter_congr fun p _ => by simp [Nat.not_even_iff_odd]
  have hF : HasProd (fun j : ℕ => if j + 1 ∈ {j | Odd j} then (1 - q ^ (j + 1))⁻¹ else 1)
      (∏' j : ℕ, (1 + q ^ (j + 1))) := by
    rw [← (mul_right_injective₀ (two_ne_zero : (2 : ℕ) ≠ 0)).hasProd_iff]
    · convert hodd using 2 with j
      simp
    · intro j hj
      have : ¬ Odd (j + 1) := by
        rintro ⟨k, hk⟩
        exact hj ⟨k, by simp only; omega⟩
      simp [this]
  rw [← hS.2.unique hF]
  simp_rw [hd]
  exact hS.1

/-- (26.10.2), third equality: `∏_{j ≥ 1} (1 + q^j) = 1 + ∑_{m ≥ 1} q^{m(m+1)/2}/(q;q)_m`
(the `m = 0` term is `1`). -/
@[dlmf 26.10.E2]
theorem hasSum_pow_triangle_div_qPochhammer {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun m : ℕ => q ^ (m * (m + 1) / 2) / qPochhammer q q m)
      (∏' j : ℕ, (1 + q ^ (j + 1))) := by
  have he : ∀ m : ℕ, q ^ (m * (m + 1) / 2) / qPochhammer q q m =
      q ^ m.choose 2 * q ^ m / qPochhammer q q m := by
    intro m
    rw [← pow_add]; congr 2
    rw [Nat.choose_two_right]
    rcases m with _ | m
    · rfl
    · rw [show (m + 1) * (m + 1 + 1) = (m + 1) * m + 2 * (m + 1) by ring, Nat.add_sub_cancel,
        Nat.add_mul_div_left _ _ two_pos]
  obtain ⟨D, hD⟩ := exists_norm_recip_qPochhammer_le hq
  have hs : Summable fun m : ℕ => q ^ (m * (m + 1) / 2) / qPochhammer q q m := by
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one (norm_nonneg q) hq).mul_left D)
      fun m => ?_
    rw [he, div_eq_mul_inv, norm_mul, norm_mul, norm_pow, norm_pow]
    have h1 : ‖q‖ ^ m.choose 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) hq.le
    have := hD m
    have h0 : 0 ≤ ‖(qPochhammer q q m)⁻¹‖ := norm_nonneg _
    calc ‖q‖ ^ m.choose 2 * ‖q‖ ^ m * ‖(qPochhammer q q m)⁻¹‖ ≤ 1 * ‖q‖ ^ m * D := by
          gcongr
      _ = D * ‖q‖ ^ m := by ring
  convert hs.hasSum using 1
  rw [r26a_tprod_one_add_eq, ← tsum_qExp hq q]
  exact tsum_congr fun m => (he m).symm

/-- (26.10.2), fourth equality: `∏_{j ≥ 1} (1 + q^j) = 1 + ∑_{m ≥ 1} q^m (1+q)⋯(1+q^{m-1})`
(the `m = 0` term is `1`). The `m`-th term is the generating function of the partitions into
distinct parts with largest part `m` (`hasSum_distinct_largest`). -/
@[dlmf 26.10.E2]
theorem hasSum_pow_mul_prod_one_add {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun m : ℕ => q ^ m * ∏ i ∈ Ico 1 m, (1 + q ^ i)) (∏' j : ℕ, (1 + q ^ (j + 1))) := by
  -- partial sums telescope to `∏_{i=1}^{N} (1 + q^i)`
  have htel : ∀ N : ℕ, ∑ m ∈ range (N + 1), q ^ m * ∏ i ∈ Ico 1 m, (1 + q ^ i) =
      ∏ j ∈ range N, (1 + q ^ (j + 1)) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [sum_range_succ, ih, prod_range_succ]
      have : ∏ i ∈ Ico 1 (N + 1), (1 + q ^ i) = ∏ j ∈ range N, (1 + q ^ (j + 1)) := by
        rw [prod_Ico_eq_prod_range]; simp [add_comm]
      rw [this]; ring
  have hA := (r26a_hasProd_one_add hq).tendsto_prod_nat
  -- bound the terms
  set B := ∏' j : ℕ, (1 + ‖q‖ ^ (j + 1))
  have hbd : ∀ m, ‖∏ i ∈ Ico 1 m, (1 + q ^ i)‖ ≤ Real.exp (1 / (1 - ‖q‖)) := by
    intro m
    rw [norm_prod]
    calc ∏ i ∈ Ico 1 m, ‖1 + q ^ i‖ ≤ ∏ i ∈ Ico 1 m, Real.exp (‖q‖ ^ i) := by
          refine prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ => ?_
          calc ‖1 + q ^ i‖ ≤ 1 + ‖q‖ ^ i := by
                refine (norm_add_le _ _).trans ?_; rw [norm_one, norm_pow]
            _ ≤ _ := by linarith [Real.add_one_le_exp (‖q‖ ^ i)]
      _ = Real.exp (∑ i ∈ Ico 1 m, ‖q‖ ^ i) := (Real.exp_sum _ _).symm
      _ ≤ Real.exp (1 / (1 - ‖q‖)) := by
          rw [Real.exp_le_exp, one_div, ← tsum_geometric_of_lt_one (norm_nonneg q) hq]
          exact (summable_geometric_of_lt_one (norm_nonneg q) hq).sum_le_tsum _
            (fun _ _ => by positivity)
  have hs : Summable fun m : ℕ => q ^ m * ∏ i ∈ Ico 1 m, (1 + q ^ i) := by
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one (norm_nonneg q) hq).mul_left
      (Real.exp (1 / (1 - ‖q‖)))) fun m => ?_
    rw [norm_mul, norm_pow, mul_comm]
    exact mul_le_mul_of_nonneg_right (hbd m) (by positivity)
  refine (hs.hasSum_iff_tendsto_nat).mpr ?_
  rw [← tendsto_add_atTop_iff_nat 1]
  simpa only [htel] using hA

/-- Distinct partitions of `n` with largest part `m ≥ 1` against subsets `T ⊆ [1, m)` with
`m + ∑ T = n`. -/
lemma r26a_card_distinct_sup {m : ℕ} (hm : 1 ≤ m) (n : ℕ) :
    #{p ∈ Nat.Partition.distincts n | p.parts.sup = m} =
      #{T ∈ (Ico 1 m).powerset | m + ∑ i ∈ T, i = n} := by
  symm
  refine card_bij (fun T hT => ⟨(insert m T).val, ?_, ?_⟩) ?_ ?_ ?_
  · intro i hi
    simp only [mem_filter, mem_powerset] at hT
    rcases mem_insert.mp hi with rfl | hi
    · omega
    · exact (mem_Ico.mp (hT.1 hi)).1
  · simp only [mem_filter, mem_powerset] at hT
    have hmT : m ∉ T := fun h => by have := mem_Ico.mp (hT.1 h); omega
    rw [show (insert m T).val.sum = ∑ i ∈ insert m T, i by
      rw [Finset.sum_eq_multiset_sum, Multiset.map_id'], sum_insert hmT]; exact hT.2
  · intro T hT
    simp only [mem_filter, mem_powerset] at hT
    simp only [mem_filter, Nat.Partition.distincts, mem_univ, true_and]
    refine ⟨(insert m T).nodup, ?_⟩
    rw [show (insert m T).val.sup = (insert m T).sup id by rw [Finset.sup_def, Multiset.map_id]]
    apply le_antisymm
    · refine Finset.sup_le fun i hi => ?_
      rcases mem_insert.mp hi with rfl | hi
      · exact le_rfl
      · exact (mem_Ico.mp (hT.1 hi)).2.le
    · exact Finset.le_sup (f := id) (mem_insert_self m T)
  · intro T hT T' hT' h
    simp only [mem_filter, mem_powerset] at hT hT'
    have h1 := congrArg Nat.Partition.parts h
    simp only at h1
    have h2 : insert m T = insert m T' := Finset.val_injective h1
    have hmT : m ∉ T := fun h => by have := mem_Ico.mp (hT.1 h); omega
    have hmT' : m ∉ T' := fun h => by have := mem_Ico.mp (hT'.1 h); omega
    rw [← erase_insert hmT, h2, erase_insert hmT']
  · intro p hp
    simp only [mem_filter, Nat.Partition.distincts, mem_univ, true_and] at hp
    have hle : ∀ i ∈ p.parts, i ≤ m := fun i hi => hp.2 ▸ Multiset.le_sup hi
    have hval : p.parts.toFinset.val = p.parts := by
      rw [Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hp.1]
    have hmem : m ∈ p.parts := by
      rcases Multiset.empty_or_exists_mem p.parts with h0 | ⟨x, hx⟩
      · rw [h0, Multiset.sup_zero] at hp; simp at hp; omega
      · obtain ⟨y, hy, hy'⟩ := Finset.exists_mem_eq_sup p.parts.toFinset
          ⟨x, Multiset.mem_toFinset.mpr hx⟩ id
        rw [Finset.sup_def, hval, Multiset.map_id, hp.2] at hy'
        rw [hy']; exact Multiset.mem_toFinset.mp hy
    refine ⟨p.parts.toFinset.erase m, ?_, ?_⟩
    · simp only [mem_filter, mem_powerset]
      refine ⟨fun i hi => ?_, ?_⟩
      · rw [mem_erase, Multiset.mem_toFinset] at hi
        exact mem_Ico.mpr ⟨p.parts_pos hi.2, lt_of_le_of_ne (hle i hi.2) hi.1⟩
      · rw [Finset.add_sum_erase _ (fun i => i) (Multiset.mem_toFinset.mpr hmem),
          Finset.sum_eq_multiset_sum, Multiset.map_id', hval, p.parts_sum]
    · apply Nat.Partition.ext
      simp only
      rw [insert_erase (Multiset.mem_toFinset.mpr hmem), Multiset.toFinset_val,
        Multiset.dedup_eq_self.mpr hp.1]


/-- §26.10(ii), after (26.10.2): `q^m (1+q)⋯(1+q^{m-1})` is the generating function of the
partitions into distinct parts with largest part equal to `m` (a polynomial identity, every
`q`). -/
@[dlmf 26.10.E2]
theorem hasSum_distinct_largest (q : ℂ) (m : ℕ) :
    HasSum (fun n => (#{p ∈ Nat.Partition.distincts n | p.parts.sup = m} : ℂ) * q ^ n)
      (q ^ m * ∏ i ∈ Ico 1 m, (1 + q ^ i)) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have h : ∀ n, (#{p ∈ Nat.Partition.distincts n | p.parts.sup = 0} : ℂ) * q ^ n =
        if n = 0 then 1 else 0 := by
      intro n
      split_ifs with hn
      · subst hn
        rw [card_eq_one.mpr ⟨default, eq_singleton_iff_unique_mem.mpr ⟨?_,
          fun p _ => Subsingleton.elim _ _⟩⟩]
        · simp
        simp [Nat.Partition.distincts]
      · rw [card_eq_zero.mpr, Nat.cast_zero, zero_mul]
        rw [filter_eq_empty_iff]
        intro p _ hp
        obtain ⟨x, hx⟩ : ∃ x, x ∈ p.parts := by
          by_contra h0
          push Not at h0
          have := p.parts_sum
          rw [Multiset.eq_zero_of_forall_notMem h0, Multiset.sum_zero] at this
          omega
        have h1 := Multiset.le_sup hx
        rw [hp] at h1
        have := p.parts_pos hx
        simp at h1; omega
    simp_rw [h]
    simpa using hasSum_ite_eq 0 (1 : ℂ)
  -- `m ≥ 1`: expand the product over subsets of `[1, m)`
  simp_rw [r26a_card_distinct_sup hm]
  set g : Finset ℕ → ℕ := fun T => m + ∑ i ∈ T, i
  have hval : q ^ m * ∏ i ∈ Ico 1 m, (1 + q ^ i) = ∑ T ∈ (Ico 1 m).powerset, q ^ g T := by
    rw [prod_one_add, mul_sum]
    refine sum_congr rfl fun T _ => ?_
    rw [prod_pow_eq_pow_sum, ← pow_add]
  have hbound : ∀ T ∈ (Ico 1 m).powerset, g T ∈ range (g (Ico 1 m) + 1) := by
    intro T hT
    rw [mem_range, Nat.lt_succ_iff]
    exact Nat.add_le_add_left (sum_le_sum_of_subset (mem_powerset.mp hT)) m
  rw [hval]
  have hfin : ∀ n ∉ range (g (Ico 1 m) + 1),
      (#{T ∈ (Ico 1 m).powerset | g T = n} : ℂ) * q ^ n = 0 := by
    intro n hn
    rw [card_eq_zero.mpr, Nat.cast_zero, zero_mul]
    rw [filter_eq_empty_iff]
    intro T hT hTn
    exact hn (hTn ▸ hbound T hT)
  have hs := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ) hfin
  convert hs using 1
  rw [← sum_fiberwise_of_maps_to' hbound]
  refine sum_congr rfl fun n _ => ?_
  rw [sum_const, nsmul_eq_mul]

/-- Distinct partitions with parts at most `k` against subsets of `[1, k]`. -/
lemma r26a_card_boxed_eq (m k n : ℕ) :
    partitionCountAtMostDistinctBoxed m k n =
      #{T ∈ (Icc 1 k).powerset | T.card ≤ m ∧ ∑ i ∈ T, i = n} := by
  unfold partitionCountAtMostDistinctBoxed
  symm
  refine card_bij (fun T hT => ⟨T.val, ?_, ?_⟩) ?_ ?_ ?_
  · intro i hi
    simp only [mem_filter, mem_powerset] at hT
    exact (mem_Icc.mp (hT.1 hi)).1
  · simp only [mem_filter, mem_powerset] at hT
    rw [← hT.2.2, Finset.sum_eq_multiset_sum, Multiset.map_id']
  · intro T hT
    simp only [mem_filter, mem_powerset] at hT
    simp only [mem_filter, Nat.Partition.distincts, mem_univ, true_and]
    exact ⟨T.nodup, hT.2.1, fun i hi => (mem_Icc.mp (hT.1 hi)).2⟩
  · intro T _ T' _ h
    exact Finset.val_injective (congrArg Nat.Partition.parts h)
  · intro p hp
    simp only [mem_filter, Nat.Partition.distincts, mem_univ, true_and] at hp
    have hval : p.parts.toFinset.val = p.parts := by
      rw [Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hp.1]
    refine ⟨p.parts.toFinset, ?_, Nat.Partition.ext (by simpa using hval)⟩
    simp only [mem_filter, mem_powerset]
    refine ⟨fun i hi => ?_, ?_, ?_⟩
    · rw [Multiset.mem_toFinset] at hi
      exact mem_Icc.mpr ⟨p.parts_pos hi, hp.2.2 i hi⟩
    · rw [← Multiset.toFinset_card_of_nodup hp.1] at hp; exact hp.2.1
    · rw [Finset.sum_eq_multiset_sum, Multiset.map_id', hval, p.parts_sum]

/-- (26.10.3): `(1 - x) ∑_{m,n} p_m(≤ k, 𝒟, n) x^m qⁿ = ∏_{j=1}^k (1 + x q^j)` for `|x| < 1`;
the `n`-sums are finite, so `q` is arbitrary (stronger than DLMF's `|q| < 1`). -/
@[dlmf 26.10.E3]
theorem hasSum_partitionCountAtMostDistinctBoxed (q : ℂ) {x : ℂ} (hx : ‖x‖ < 1) (k : ℕ) :
    HasSum (fun mn : ℕ × ℕ =>
        (1 - x) * ((partitionCountAtMostDistinctBoxed mn.1 k mn.2 : ℂ) * x ^ mn.1 * q ^ mn.2))
      (∏ j ∈ Icc 1 k, (1 + x * q ^ j)) := by
  set U := (Icc 1 k).powerset
  -- one subset at a time
  have hT : ∀ T ∈ U, HasSum (fun mn : ℕ × ℕ =>
      if T.card ≤ mn.1 ∧ ∑ i ∈ T, i = mn.2 then (1 - x) * (x ^ mn.1 * q ^ mn.2) else 0)
      (x ^ T.card * q ^ ∑ i ∈ T, i) := by
    intro T _
    set t := T.card
    set s := ∑ i ∈ T, i
    have hinj : Function.Injective fun m : ℕ => (m + t, s) := fun a b h => by
      simp only [Prod.mk.injEq] at h; omega
    rw [← hinj.hasSum_iff]
    · have hg := (hasSum_geometric_of_norm_lt_one hx).mul_left ((1 - x) * x ^ t * q ^ s)
      have hx1 : (1 : ℂ) - x ≠ 0 := by
        intro h; rw [sub_eq_zero] at h; rw [← h, norm_one] at hx; exact lt_irrefl _ hx
      convert hg using 1
      · ext m
        simp only [Function.comp, le_add_iff_nonneg_left, zero_le, true_and, ↓reduceIte]
        ring
      · field_simp
    · rintro ⟨m, n⟩ hmn
      rw [ite_eq_right_iff]
      rintro ⟨h1, h2⟩
      exact (hmn ⟨m - t, by simp only [Prod.mk.injEq]; omega⟩).elim
  have hsum := hasSum_sum hT
  convert hsum using 1
  · ext ⟨m, n⟩
    rw [r26a_card_boxed_eq, card_filter, Nat.cast_sum, sum_mul, sum_mul, mul_sum]
    refine sum_congr rfl fun T _ => ?_
    split_ifs <;> simp
  · rw [prod_one_add]
    refine sum_congr rfl fun T _ => ?_
    rw [prod_mul_distrib, prod_const, prod_pow_eq_pow_sum]

/-- (26.10.3), middle member: `∑_{m=0}^k [k m]_q q^{m(m+1)/2} x^m = ∏_{j=1}^k (1 + x q^j)`
(Cauchy's finite `q`-binomial theorem; every `x, q`). -/
@[dlmf 26.10.E3]
theorem sum_qBinom_triangle_eq_prod (q x : ℂ) (k : ℕ) :
    ∑ m ∈ range (k + 1), qBinom q k m * q ^ (m * (m + 1) / 2) * x ^ m =
      ∏ j ∈ Icc 1 k, (1 + x * q ^ j) := by
  have h := qPochhammer_eq_sum_qBinom (-(x * q)) q k
  have hprod : qPochhammer (-(x * q)) q k = ∏ j ∈ Icc 1 k, (1 + x * q ^ j) := by
    rw [qPochhammer_eq_prod]
    clear h
    induction k with
    | zero => simp
    | succ k ih => rw [prod_range_succ, ih, Finset.prod_Icc_succ_top (by omega)]; ring
  rw [← hprod, h]
  refine sum_congr rfl fun m _ => ?_
  have hm : m * (m + 1) / 2 = m.choose 2 + m := by
    rw [Nat.choose_two_right, show m * (m + 1) = m * (m - 1) + 2 * m by
      rcases m with _ | m
      · rfl
      · rw [Nat.add_sub_cancel]; ring, Nat.add_mul_div_left _ _ two_pos]
  rw [hm, pow_add, neg_pow (x * q), mul_pow]
  have h1 : ((-1 : ℂ) ^ m * (-1) ^ m) = 1 := by rw [← mul_pow]; norm_num
  linear_combination -(qBinom q k m * q ^ m.choose 2 * x ^ m * q ^ m) * h1

/-! ### Staircase generating functions (agent p26a) -/

/-- DLMF (26.10.10) (helper): the staircase count with minimal part `1`. -/
theorem s26a_partitionCountDiff_eq_sum (k n : ℕ) :
    partitionCountDiff k n =
      ∑ m ∈ range (n + 1) with k * m.choose 2 + m ≤ n,
        partitionCountAtMostParts m (n - (k * m.choose 2 + m)) := by
  have h := s26a_card_diff_min_eq_sum k 1 n le_rfl
  simp only [one_mul] at h
  rw [← h, partitionCountDiff]
  congr 1
  refine filter_congr fun p _ => ?_
  exact ⟨fun hp => ⟨hp, fun i hi => p.parts_pos hi⟩, fun hp => hp.1⟩


/-- `(q;q)_m = ∏_{j=1}^m (1 - q^j)`. -/
lemma s26a_qPochhammer_eq_prod (q : ℂ) (m : ℕ) :
    qPochhammer q q m = ∏ j ∈ Icc 1 m, (1 - q ^ j) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [qPochhammer_succ, ih, Finset.prod_Icc_succ_top (by omega), pow_succ' q m]

/-- Generating function of `c n = ∑_{m, e m ≤ n} p_m(n - e m)` for `e m ≥ m`. -/
theorem s26a_hasSum_staircase {q : ℂ} (hq : ‖q‖ < 1) (e : ℕ → ℕ) (he : ∀ m, m ≤ e m)
    (c : ℕ → ℕ) (hc : ∀ n, c n = ∑ m ∈ range (n + 1) with e m ≤ n,
      partitionCountAtMostParts m (n - e m)) :
    HasSum (fun n => (c n : ℂ) * q ^ n) (∑' m : ℕ, q ^ e m * ∏ j ∈ Icc 1 m, (1 - q ^ j)⁻¹) ∧
      Summable fun m : ℕ => q ^ e m * ∏ j ∈ Icc 1 m, (1 - q ^ j)⁻¹ := by
  set r := ‖q‖
  have hr0 : 0 ≤ r := norm_nonneg q
  set F : ℕ × ℕ → ℂ := fun p => (partitionCountAtMostParts p.1 p.2 : ℂ) * q ^ (p.2 + e p.1)
    with hF
  have hrow : ∀ m, HasSum (fun N => F (m, N)) (q ^ e m * ∏ j ∈ Icc 1 m, (1 - q ^ j)⁻¹) := by
    intro m
    convert (hasSum_partitionCountAtMostParts hq m).mul_left (q ^ e m) using 1
    ext N; simp only [hF, pow_add]; ring
  have hrowa : ∀ m, HasSum (fun N => ‖F (m, N)‖) (r ^ e m * ∏ j ∈ Icc 1 m, (1 - r ^ j)⁻¹) := by
    intro m
    have h := (hasSum_partitionCountAtMostParts (q := (r : ℂ)) (by simpa [r] using hq) m).mul_left
      ((r : ℂ) ^ e m)
    have h2 : HasSum (fun N => ((‖F (m, N)‖ : ℝ) : ℂ))
        (((r ^ e m * ∏ j ∈ Icc 1 m, (1 - r ^ j)⁻¹ : ℝ)) : ℂ) := by
      convert h using 1
      · ext N; simp only [hF, norm_mul, norm_pow, Complex.norm_natCast, r, pow_add]
        push_cast; ring
      · push_cast; rfl
    exact Complex.hasSum_ofReal.mp h2
  have hbound : ∀ m, r ^ e m * ∏ j ∈ Icc 1 m, (1 - r ^ j)⁻¹ ≤
      Real.exp (1 / (1 - r) ^ 2) * r ^ m := by
    intro m
    rw [mul_comm]
    exact mul_le_mul (r26a_prod_inv_le hr0 hq _ (by simp))
      (pow_le_pow_of_le_one hr0 hq.le (he m)) (by positivity) (by positivity)
  have hsumF : Summable F := by
    refine Summable.of_norm ?_
    refine (summable_prod_of_nonneg fun _ => norm_nonneg _).mpr
      ⟨fun m => (hrowa m).summable, ?_⟩
    simp_rw [fun m => (hrowa m).tsum_eq]
    refine Summable.of_nonneg_of_le (fun m => by
      have := (hrowa m).nonneg (fun _ => norm_nonneg _); exact this) hbound ?_
    exact (summable_geometric_of_lt_one hr0 hq).mul_left _
  have h1 := hsumF.hasSum.prod_fiberwise hrow
  refine ⟨?_, h1.summable⟩
  rw [h1.tsum_eq]
  -- reindex by `n = N + e m`
  set G : ℕ × ℕ → ℂ := fun p => if e p.2 ≤ p.1 then
    (partitionCountAtMostParts p.2 (p.1 - e p.2) : ℂ) * q ^ p.1 else 0 with hG
  set ι : ℕ × ℕ → ℕ × ℕ := fun p => (p.2 + e p.1, p.1) with hι
  have hιinj : Function.Injective ι := by
    rintro ⟨m, N⟩ ⟨m', N'⟩ h
    simp only [hι, Prod.mk.injEq] at h
    obtain ⟨h1, rfl⟩ := h
    simp only [Prod.mk.injEq, true_and]; omega
  have hGι : G ∘ ι = F := by
    ext ⟨m, N⟩
    simp only [Function.comp, hG, hι, hF, Nat.le_add_left, ite_true, Nat.add_sub_cancel]
  have hGsum : HasSum G (∑' p, F p) := by
    rw [← (hιinj.hasSum_iff ?_), hGι]
    · exact hsumF.hasSum
    · rintro ⟨n, m⟩ hnm
      simp only [hG]
      by_cases h : e m ≤ n
      · exact absurd ⟨(m, n - e m), by simp [hι]; omega⟩ hnm
      · simp [h]
  refine hGsum.prod_fiberwise fun n => ?_
  rw [hc n, Nat.cast_sum, sum_mul, sum_filter]
  refine hasSum_sum_of_ne_finset_zero fun m hm => ?_
  simp only [mem_range, not_lt] at hm
  simp only [hG]
  rw [ite_eq_right (by have := he m; omega)]

/-- (26.10.4): `∑ p(𝒟k, n) qⁿ = 1 + ∑_{m ≥ 1} q^{(km² + (2-k)m)/2}/(q;q)_m` for `|q| < 1`;
the exponent is written `k·m(m-1)/2 + m` (the `m = 0` term is `1`). -/
@[dlmf 26.10.E4]
theorem hasSum_partitionCountDiff {q : ℂ} (hq : ‖q‖ < 1) (k : ℕ) :
    HasSum (fun n => (partitionCountDiff k n : ℂ) * q ^ n)
        (∑' m : ℕ, q ^ (k * m.choose 2 + m) / qPochhammer q q m) ∧
      Summable fun m : ℕ => q ^ (k * m.choose 2 + m) / qPochhammer q q m := by
  have h := s26a_hasSum_staircase hq (fun m => k * m.choose 2 + m) (fun m => by omega)
    (partitionCountDiff k) (s26a_partitionCountDiff_eq_sum k)
  have he : (fun m : ℕ => q ^ (k * m.choose 2 + m) / qPochhammer q q m) =
      fun m => q ^ (k * m.choose 2 + m) * ∏ j ∈ Icc 1 m, (1 - q ^ j)⁻¹ := by
    ext m; rw [s26a_qPochhammer_eq_prod, div_eq_mul_inv, prod_inv_distrib]
  rw [he]
  exact h

/-- (26.10.5): `∑ p(∈ S, n) qⁿ = ∏_{j ∈ S} (1 - q^j)⁻¹` for `|q| < 1` and any set `S` of
positive integers (`0 ∉ S`; the product over `j ∉ S` contributes `1`). -/
@[dlmf 26.10.E5]
theorem hasSum_partitionCountIn {q : ℂ} (hq : ‖q‖ < 1) (S : Set ℕ) [DecidablePred (· ∈ S)] :
    HasSum (fun n => (partitionCountIn S n : ℂ) * q ^ n)
        (∏' j : ℕ, if j + 1 ∈ S then (1 - q ^ (j + 1))⁻¹ else 1) ∧
      HasProd (fun j : ℕ => if j + 1 ∈ S then (1 - q ^ (j + 1))⁻¹ else 1)
        (∏' j : ℕ, if j + 1 ∈ S then (1 - q ^ (j + 1))⁻¹ else 1) :=
  r26a_hasSum_partitionCountIn hq S

/-- Removing `k` copies of an allowed part `a`: partitions of `n` with parts in `P` and at least `k`
copies of `a` correspond to partitions of `n - k a` with parts in `P`. -/
lemma r26a_card_restricted_count_ge (P : ℕ → Prop) [DecidablePred P] {a : ℕ} (ha1 : 1 ≤ a)
    (hP : P a) : ∀ k n : ℕ, k * a ≤ n →
      #{p ∈ Nat.Partition.restricted n P | k ≤ p.parts.count a} =
        #(Nat.Partition.restricted (n - k * a) P) := by
  intro k
  induction k with
  | zero =>
    intro n _
    rw [zero_mul, Nat.sub_zero]
    congr 1
    exact filter_true_of_mem fun _ _ => Nat.zero_le _
  | succ k ih =>
    intro n hn
    have ha : a ≤ n := by nlinarith
    rw [show n - (k + 1) * a = n - a - k * a by rw [add_mul, one_mul]; omega,
      ← ih (n - a) (by rw [add_mul, one_mul] at hn; omega)]
    let e := Nat.Partition.partitionWithPartEquiv ha1 ha
    refine card_bij (fun p hp => e ⟨p, ?_⟩) ?_ ?_ ?_
    · simp only [mem_filter] at hp
      exact Multiset.count_pos.mp (by omega)
    · intro p hp
      simp only [mem_filter, Nat.Partition.restricted, mem_univ, true_and] at hp ⊢
      rw [Nat.Partition.partitionWithPartEquiv_apply_parts]
      refine ⟨fun i hi => hp.1 i (Multiset.mem_of_mem_erase hi), ?_⟩
      rw [Multiset.count_erase_self]; exact Nat.le_sub_of_add_le hp.2
    · intro p _ p' _ h
      exact congrArg Subtype.val (e.injective h)
    · intro q hq
      simp only [mem_filter, Nat.Partition.restricted, mem_univ, true_and] at hq
      refine ⟨(e.symm q).1, ?_, by simp⟩
      simp only [mem_filter, Nat.Partition.restricted, mem_univ, true_and,
        Nat.Partition.partitionWithPartEquiv_symm_apply_parts, e]
      refine ⟨fun i hi => ?_, ?_⟩
      · rcases Multiset.mem_cons.mp hi with rfl | hi
        · exact hP
        · exact hq.1 i hi
      · rw [Multiset.count_cons_self]; omega

/-- (26.10.11) for a predicate: `n p(P, n) = ∑_{t=1}^n p(P, n - t) ∑_{j ∣ t, P j} j`. -/
theorem r26a_card_restricted_recurrence (P : ℕ → Prop) [DecidablePred P] (n : ℕ) :
    n * #(Nat.Partition.restricted n P) =
      ∑ t ∈ Icc 1 n, #(Nat.Partition.restricted (n - t) P) * ∑ j ∈ t.divisors with P j, j := by
  set R := Nat.Partition.restricted n P
  -- left side: sum over partitions of the sum of the parts
  have hL : n * #R = ∑ j ∈ (Icc 1 n).filter P, j * ∑ p ∈ R, p.parts.count j := by
    have h1 : ∀ p ∈ R, n = ∑ j ∈ (Icc 1 n).filter P, j * p.parts.count j := by
      intro p hp
      simp only [R, Nat.Partition.restricted, mem_filter, mem_univ, true_and] at hp
      conv_lhs => rw [← p.parts_sum, Finset.sum_multiset_count]
      simp_rw [smul_eq_mul, mul_comm (Multiset.count _ _)]
      apply sum_subset
      · intro j hj
        rw [Multiset.mem_toFinset] at hj
        simp only [mem_filter, mem_Icc]
        exact ⟨⟨p.parts_pos hj, Nat.Partition.le_of_mem_parts hj⟩, hp j hj⟩
      · intro j _ hj; rw [Multiset.mem_toFinset] at hj; simp [Multiset.count_eq_zero_of_notMem hj]
    rw [mul_comm, ← smul_eq_mul, ← sum_const, sum_congr rfl h1, sum_comm]
    simp_rw [mul_sum]
  -- the multiplicity of `j` as a sum of indicator counts
  have hC : ∀ j ∈ (Icc 1 n).filter P, ∑ p ∈ R, p.parts.count j =
      ∑ t ∈ (Icc 1 n).filter (j ∣ ·), #(Nat.Partition.restricted (n - t) P) := by
    intro j hj
    simp only [mem_filter, mem_Icc] at hj
    have hcount : ∀ p ∈ R,
        p.parts.count j = ∑ k ∈ Icc 1 n, if k ≤ p.parts.count j then 1 else 0 := by
      intro p _
      rw [sum_boole, Nat.cast_id]
      have hle : p.parts.count j ≤ n := by
        have := Multiset.count_le_card j p.parts
        have h2 : Multiset.card p.parts ≤ n := by
          have := Multiset.card_nsmul_le_sum (s := p.parts) (a := 1) fun i hi => p.parts_pos hi
          rw [smul_eq_mul, mul_one, p.parts_sum] at this
          exact this
        omega
      rw [show (Icc 1 n).filter (fun k => k ≤ p.parts.count j) = Icc 1 (p.parts.count j) by
        ext k; simp only [mem_filter, mem_Icc]; omega]
      simp
    rw [sum_congr rfl hcount, sum_comm]
    simp_rw [← card_filter]
    -- reindex `t = k j`
    have hk : ∀ k ∈ Icc 1 n, #{p ∈ R | k ≤ p.parts.count j} =
        if k * j ≤ n then #(Nat.Partition.restricted (n - k * j) P) else 0 := by
      intro k _
      split_ifs with hkj
      · exact r26a_card_restricted_count_ge P hj.1.1 hj.2 k n hkj
      · rw [card_eq_zero, filter_eq_empty_iff]
        intro p _ hp
        apply hkj
        have : p.parts.count j * j ≤ n := by
          obtain ⟨u, hu⟩ := Multiset.le_iff_exists_add.mp
            (Multiset.le_count_iff_replicate_le.mp (le_refl (p.parts.count j)))
          calc p.parts.count j * j = (Multiset.replicate (p.parts.count j) j).sum := by simp
            _ ≤ (Multiset.replicate (p.parts.count j) j).sum + u.sum := Nat.le_add_right _ _
            _ = p.parts.sum := by rw [← Multiset.sum_add, ← hu]
            _ = n := p.parts_sum
        calc k * j ≤ p.parts.count j * j := Nat.mul_le_mul_right _ hp
          _ ≤ n := this
    rw [sum_congr rfl hk, ← sum_filter]
    have hmap : (Icc 1 n).filter (j ∣ ·) =
        ((Icc 1 n).filter (· * j ≤ n)).map ⟨(· * j), mul_left_injective₀ (by omega)⟩ := by
      ext t
      simp only [mem_filter, mem_Icc, Finset.mem_map, Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨⟨h1, h2⟩, k, rfl⟩
        refine ⟨k, ⟨⟨?_, ?_⟩, by rw [mul_comm]; omega⟩, mul_comm _ _⟩
        · rcases k with _ | k
          · simp at h1
          · omega
        · nlinarith
      · rintro ⟨k, ⟨⟨h1, h2⟩, h3⟩, rfl⟩
        exact ⟨⟨by nlinarith, h3⟩, Dvd.intro_left k rfl⟩
    rw [hmap, sum_map]
    rfl
  rw [hL, sum_congr rfl fun j hj => by rw [hC j hj]]
  simp_rw [mul_sum]
  rw [sum_comm' (t' := Icc 1 n) (s' := fun t => t.divisors.filter P)]
  · refine sum_congr rfl fun t _ => sum_congr rfl fun j _ => mul_comm _ _
  · intro j t
    simp only [mem_filter, mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, hPj⟩, ⟨h3, h4⟩, hjt⟩
      exact ⟨⟨⟨hjt, by omega⟩, hPj⟩, h3, h4⟩
    · rintro ⟨⟨⟨hjt, ht0⟩, hPj⟩, h3, h4⟩
      have := Nat.le_of_dvd (by omega) hjt
      have : 0 < j := Nat.pos_of_dvd_of_pos hjt (by omega)
      exact ⟨⟨⟨by omega, by omega⟩, hPj⟩, ⟨h3, h4⟩, hjt⟩

/-- (26.10.6): `n p(𝒟, n) = ∑_{t=1}^n p(𝒟, n - t) ∑_{j ∣ t, j odd} j` (stated multiplied by
`n`). -/
@[dlmf 26.10.E6]
theorem partitionCountDistinct_recurrence (n : ℕ) :
    n * partitionCountDistinct n =
      ∑ t ∈ Icc 1 n, partitionCountDistinct (n - t) * ∑ j ∈ t.divisors with Odd j, j := by
  -- Euler: `p(𝒟, m) = p(𝒪, m)`, then (26.10.11) for odd parts
  have h : ∀ m, partitionCountDistinct m = #(Nat.Partition.restricted m (¬ Even ·)) := fun m => by
    rw [partitionCountDistinct, ← Nat.Partition.card_odds_eq_card_distincts]; rfl
  simp_rw [h]
  rw [r26a_card_restricted_recurrence]
  refine sum_congr rfl fun t _ => ?_
  congr 1
  refine sum_congr (filter_congr fun j _ => Nat.not_even_iff_odd) fun _ _ => rfl

open PowerSeries PowerSeries.WithPiTopology in
/-- Coefficients of the partial products `∏_{i ∈ s} (1 + X^{i+1})` are eventually the distinct
partition counts. -/
lemma r26a_coeff_prod_one_add_eventually (n : ℕ) :
    ∀ᶠ s in atTop, coeff n (∏ i ∈ s, (1 + X ^ (i + 1) : ℤ⟦X⟧)) = partitionCountDistinct n := by
  have h := Nat.Partition.hasProd_powerSeriesMk_card_countRestricted ℤ (m := 2) two_pos
  rw [HasProd, tendsto_iff_coeff_tendsto] at h
  have h2 := h n
  rw [coeff_mk, nhds_discrete, tendsto_pure] at h2
  filter_upwards [h2] with s hs
  rw [partitionCountDistinct, ← Nat.Partition.countRestricted_two, ← hs]
  congr 1
  exact prod_congr rfl fun i _ => by simp [sum_range_succ]

open PowerSeries PowerSeries.WithPiTopology in
/-- `(q;q)_∞ ∏ (1 + q^j) = (q²;q²)_∞`, coefficientwise:
`∑_{i ≤ n} [q^i](q;q)_∞ · p(𝒟, n - i) = [q^n](q²;q²)_∞`. -/
lemma r26a_sum_pentagonal_mul_distinct (n : ℕ) :
    ∑ i ∈ range (n + 1), coeff i (pentagonalSeries ℤ) * partitionCountDistinct (n - i) =
      if 2 ∣ n then coeff (n / 2) (pentagonalSeries ℤ) else 0 := by
  have e1 : ∀ᶠ s in atTop, ∀ j ∈ range (n + 1),
      coeff j (∏ i ∈ s, (1 - X ^ (i + 1) : ℤ⟦X⟧)) = coeff j (pentagonalSeries ℤ) :=
    (eventually_all_finset _).2 fun j _ => coeff_prod_one_sub_X_pow_eventually_eq ℤ j
  have e2 : ∀ᶠ s in atTop, ∀ j ∈ range (n + 1),
      coeff j (∏ i ∈ s, (1 + X ^ (i + 1) : ℤ⟦X⟧)) = partitionCountDistinct j :=
    (eventually_all_finset _).2 fun j _ => r26a_coeff_prod_one_add_eventually j
  obtain ⟨s, h1, h2, h3⟩ :=
    (e1.and (e2.and (coeff_prod_one_sub_X_pow_eventually_eq ℤ (n / 2)))).exists
  have hprod : (∏ i ∈ s, (1 - X ^ (i + 1) : ℤ⟦X⟧)) * ∏ i ∈ s, (1 + X ^ (i + 1) : ℤ⟦X⟧) =
      expand 2 two_ne_zero (∏ i ∈ s, (1 - X ^ (i + 1) : ℤ⟦X⟧)) := by
    rw [← prod_mul_distrib, map_prod]
    refine prod_congr rfl fun i _ => ?_
    rw [map_sub, map_one, map_pow, expand_X]
    ring
  have hc := congrArg (coeff n) hprod
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, coeff_expand] at hc
  rw [← h3]
  convert hc using 1
  refine sum_congr rfl fun i hi => ?_
  simp only
  rw [h1 i hi, h2 (n - i) (by simp)]

open PowerSeries PowerSeries.WithPiTopology in
/-- `(-1)^k = (-1)^{|k|}` for the `negOnePow` sign. -/
lemma r26a_coe_negOnePow (k : ℤ) : ((k.negOnePow : ℤˣ) : ℤ) = (-1) ^ k.natAbs := by
  rw [← Int.negOnePow_abs, ← Int.natCast_natAbs, Int.coe_negOnePow_natCast]

open PowerSeries PowerSeries.WithPiTopology in
/-- `|k| ≤ k(3k-1)/2`. -/
lemma r26a_natAbs_le_pentagonal (k : ℤ) : k.natAbs ≤ pentagonal k := by
  have h := two_mul_natCast_pentagonal k
  have : (k.natAbs : ℤ) ≤ pentagonal k := by
    rcases le_or_gt 0 k with hk | hk
    · rw [Int.natAbs_of_nonneg hk]; nlinarith
    · rw [Int.ofNat_natAbs_of_nonpos hk.le]; nlinarith
  exact_mod_cast this

open PowerSeries PowerSeries.WithPiTopology in
/-- (26.10.7), proved via `(q;q)_∞ (-q;q)_∞ = (q²;q²)_∞` and the pentagonal number theorem. -/
theorem r26a_pentagonal_distinct (n : ℕ) :
    ∑ k ∈ Icc (-(n : ℤ)) n with pentagonal k ≤ n,
        (-1 : ℤ) ^ k.natAbs * partitionCountDistinct (n - pentagonal k) =
      ∑ r ∈ Icc (-(n : ℤ)) n, if (n : ℤ) = r * (3 * r - 1) then (-1 : ℤ) ^ r.natAbs else 0 := by
  set K := (Icc (-(n : ℤ)) n).filter (pentagonal · ≤ n)
  have hL : ∑ k ∈ K, (-1 : ℤ) ^ k.natAbs * partitionCountDistinct (n - pentagonal k) =
      ∑ i ∈ range (n + 1), coeff i (pentagonalSeries ℤ) * partitionCountDistinct (n - i) := by
    simp_rw [coeff_pentagonalSeries_mul_eq_extend ℤ _
      (fun i => (partitionCountDistinct (n - i) : ℤ))]
    rw [← sum_subset (s₁ := K.image pentagonal)]
    · rw [sum_image (fun x _ y _ h => pentagonal_injective h)]
      refine sum_congr rfl fun k _ => ?_
      rw [pentagonal_injective.extend_apply, r26a_coe_negOnePow, Int.cast_id]
    · intro i hi
      obtain ⟨k, hk, rfl⟩ := mem_image.mp hi
      simp only [K, mem_filter] at hk
      exact mem_range.mpr (Nat.lt_succ_of_le hk.2)
    · intro i hi hiK
      by_cases hr : ∃ k, pentagonal k = i
      · obtain ⟨k, rfl⟩ := hr
        exfalso; apply hiK
        refine mem_image_of_mem _ ?_
        have h1 := r26a_natAbs_le_pentagonal k
        have h2 : pentagonal k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
        simp only [K, mem_filter, mem_Icc]
        refine ⟨⟨?_, ?_⟩, h2⟩ <;> omega
      · rw [Function.extend_apply' _ _ _ (by simpa using hr)]; rfl
  rw [hL, r26a_sum_pentagonal_mul_distinct]
  have hcond : ∀ r : ℤ, ((n : ℤ) = r * (3 * r - 1) ↔ 2 * pentagonal r = n) := by
    intro r
    rw [← two_mul_natCast_pentagonal]; constructor <;> intro h <;> omega
  by_cases hex : ∃ r : ℤ, 2 * pentagonal r = n
  · obtain ⟨r, hr⟩ := hex
    have hr1 := r26a_natAbs_le_pentagonal r
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨_, hr.symm⟩), show n / 2 = pentagonal r by omega,
      coeff_pentagonalSeries_pentagonal, r26a_coe_negOnePow, Int.cast_id]
    rw [sum_eq_single r]
    · rw [ite_eq_left_of_eq_true _ _ (eq_true ((hcond r).2 hr))]
    · intro b _ hb
      refine ite_eq_right_of_eq_false _ _ (eq_false fun h => ?_)
      exact hb (pentagonal_injective (by have := (hcond b).1 h; omega))
    · intro h; exfalso; apply h; simp only [mem_Icc]; constructor <;> omega
  · push Not at hex
    rw [sum_eq_zero fun r _ =>
      ite_eq_right_of_eq_false _ _ (eq_false fun h => hex r ((hcond r).1 h))]
    split_ifs with h2
    · apply coeff_pentagonalSeries_eq_zero
      rintro ⟨k, hk⟩
      exact hex k (by omega)
    · rfl

/-- (26.10.7): `∑_{k ∈ ℤ} (-1)^k p(𝒟, n - k(3k-1)/2) = (-1)^r` if `n = r(3r ± 1)` and `0`
otherwise. The printed sum over `k ≥ 0` with both signs (the `k = 0` term once) is the sum over
`k ∈ ℤ` with the pentagonal numbers `pentagonal k = k(3k-1)/2`; all relevant `k` lie in
`[-n, n]`, and the right side is written as a sum over the (at most one) `r ∈ ℤ` with
`n = r(3r - 1)`. -/
@[dlmf 26.10.E7]
theorem sum_neg_one_pow_partitionCountDistinct_pentagonal (n : ℕ) :
    ∑ k ∈ Icc (-(n : ℤ)) n with pentagonal k ≤ n,
        (-1 : ℤ) ^ k.natAbs * partitionCountDistinct (n - pentagonal k) =
      ∑ r ∈ Icc (-(n : ℤ)) n, if (n : ℤ) = r * (3 * r - 1) then (-1 : ℤ) ^ r.natAbs else 0 :=
  r26a_pentagonal_distinct n

/-- (26.10.8): `∑_{k ∈ ℤ} (-1)^k p(𝒟, n - k(3k-1)) = 1` if `n = r(r ± 1)/2` (a triangular
number) and `0` otherwise (same reading of the `±` sum as in (26.10.7)); the right side is a sum
over the (at most one) `r ≥ 0` with `n = r(r+1)/2`. -/
@[dlmf 26.10.E8]
theorem sum_neg_one_pow_partitionCountDistinct_two_pentagonal (n : ℕ) :
    ∑ k ∈ Icc (-(n : ℤ)) n with 2 * pentagonal k ≤ n,
        (-1 : ℤ) ^ k.natAbs * partitionCountDistinct (n - 2 * pentagonal k) =
      ∑ r ∈ range (n + 1), if n = r * (r + 1) / 2 then (1 : ℤ) else 0 := by
  sorry

/-- Helper for (26.10.9) (agent p26a). -/
lemma r26a_sum_map_succ (s : Multiset ℕ) : (s.map (· + 1)).sum = s.sum + Multiset.card s := by
  rw [Multiset.sum_map_add, Multiset.map_id', Multiset.map_const', Multiset.sum_replicate,
    smul_eq_mul, mul_one]

/-- Helper for (26.10.9) (agent p26a). -/
lemma r26a_map_pred_succ {s : Multiset ℕ} (hs : ∀ i ∈ s, 0 < i) :
    (s.map (· - 1)).map (· + 1) = s := by
  rw [Multiset.map_map]
  conv_rhs => rw [← Multiset.map_id s]
  exact Multiset.map_congr rfl fun i hi => by simp only [Function.comp, id]; have := hs i hi; omega

/-- Adding `1` to each part of a partition of `N` into `m` parts. -/
def r26a_shift {N : ℕ} (q : N.Partition) (n : ℕ) (h : N + Multiset.card q.parts = n) :
    n.Partition where
  parts := q.parts.map (· + 1)
  parts_pos := by intro i hi; obtain ⟨j, -, rfl⟩ := Multiset.mem_map.mp hi; omega
  parts_sum := by rw [r26a_sum_map_succ, q.parts_sum, h]

/-- Adding `1` to each part of a partition of `N` into `m - 1` parts and adjoining a part `1`. -/
def r26a_shiftCons {N : ℕ} (q : N.Partition) (n : ℕ) (h : N + Multiset.card q.parts + 1 = n) :
    n.Partition where
  parts := 1 ::ₘ q.parts.map (· + 1)
  parts_pos := by
    intro i hi
    rcases Multiset.mem_cons.mp hi with rfl | hi
    · exact one_pos
    · obtain ⟨j, -, rfl⟩ := Multiset.mem_map.mp hi; omega
  parts_sum := by rw [Multiset.sum_cons, r26a_sum_map_succ, q.parts_sum, ← h]; ring

/-- Subtracting `1` from each part. -/
def r26a_unshift {n : ℕ} (p : n.Partition) (N : ℕ) (h : N + Multiset.card p.parts = n)
    (h1 : 1 ∉ p.parts) : N.Partition where
  parts := p.parts.map (· - 1)
  parts_pos := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Multiset.mem_map.mp hi
    have := p.parts_pos hj
    have : j ≠ 1 := fun e => h1 (e ▸ hj)
    omega
  parts_sum := by
    have := r26a_sum_map_succ (p.parts.map (· - 1))
    rw [r26a_map_pred_succ (fun i hi => p.parts_pos hi), Multiset.card_map, p.parts_sum] at this
    omega

/-- Helper for (26.10.9) (agent p26a). -/
lemma r26a_parts_shift {N : ℕ} (q : N.Partition) (n : ℕ) (h : N + Multiset.card q.parts = n) :
    (r26a_shift q n h).parts = q.parts.map (· + 1) := rfl

/-- Helper for (26.10.9) (agent p26a). -/
lemma r26a_parts_shiftCons {N : ℕ} (q : N.Partition) (n : ℕ)
    (h : N + Multiset.card q.parts + 1 = n) :
    (r26a_shiftCons q n h).parts = 1 ::ₘ q.parts.map (· + 1) := rfl

/-- Helper for (26.10.9) (agent p26a). -/
lemma r26a_parts_unshift {n : ℕ} (p : n.Partition) (N : ℕ) (h : N + Multiset.card p.parts = n)
    (h1 : 1 ∉ p.parts) : (r26a_unshift p N h h1).parts = p.parts.map (· - 1) := rfl

/-- Helper for (26.10.9) (agent p26a). -/
lemma r26a_nodup_map_pred {s : Multiset ℕ} (hs : ∀ i ∈ s, 0 < i) (hn : s.Nodup) :
    (s.map (· - 1)).Nodup :=
  hn.map_on fun x hx y hy hxy => by have := hs x hx; have := hs y hy; omega

/-- Helper for (26.10.9) (agent p26a). -/
lemma r26a_card_distinct_no_one {m n : ℕ} (hmn : m ≤ n) :
    #{p ∈ Nat.Partition.distincts n | p.parts.card = m ∧ 1 ∉ p.parts} =
      #{p ∈ Nat.Partition.distincts (n - m) | p.parts.card = m} := by
  symm
  refine card_bij (fun q hq => r26a_shift q n (by
    simp only [mem_filter] at hq; rw [hq.2]; omega)) ?_ ?_ ?_
  · intro q hq
    simp only [mem_filter, Nat.Partition.distincts, mem_univ, true_and] at hq ⊢
    rw [r26a_parts_shift]
    refine ⟨hq.1.map (add_left_injective 1), by rw [Multiset.card_map, hq.2], fun h => ?_⟩
    obtain ⟨j, hj, hj1⟩ := Multiset.mem_map.mp h
    have := q.parts_pos hj
    omega
  · intro q _ q' _ h
    have := congrArg Nat.Partition.parts h
    rw [r26a_parts_shift, r26a_parts_shift] at this
    exact Nat.Partition.ext (Multiset.map_injective (add_left_injective 1) this)
  · intro p hp
    simp only [mem_filter, Nat.Partition.distincts, mem_univ, true_and] at hp
    have hN : n - m + Multiset.card p.parts = n := by rw [hp.2.1]; omega
    refine ⟨r26a_unshift p (n - m) hN hp.2.2, ?_, ?_⟩
    · simp only [mem_filter, Nat.Partition.distincts, mem_univ, true_and]
      rw [r26a_parts_unshift, Multiset.card_map]
      exact ⟨r26a_nodup_map_pred (fun i hi => p.parts_pos hi) hp.1, hp.2.1⟩
    · apply Nat.Partition.ext
      rw [r26a_parts_shift, r26a_parts_unshift, r26a_map_pred_succ (fun i hi => p.parts_pos hi)]

/-- Helper for (26.10.9) (agent p26a). -/
lemma r26a_card_distinct_one {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    #{p ∈ Nat.Partition.distincts n | p.parts.card = m ∧ 1 ∈ p.parts} =
      #{p ∈ Nat.Partition.distincts (n - m) | p.parts.card = m - 1} := by
  symm
  refine card_bij (fun q hq => r26a_shiftCons q n (by
    simp only [mem_filter] at hq; rw [hq.2]; omega)) ?_ ?_ ?_
  · intro q hq
    simp only [mem_filter, Nat.Partition.distincts, mem_univ, true_and] at hq ⊢
    rw [r26a_parts_shiftCons]
    refine ⟨Multiset.nodup_cons.mpr ⟨fun h => ?_, hq.1.map (add_left_injective 1)⟩,
      by rw [Multiset.card_cons, Multiset.card_map, hq.2]; omega, Multiset.mem_cons_self _ _⟩
    obtain ⟨j, hj, hj1⟩ := Multiset.mem_map.mp h
    have := q.parts_pos hj
    omega
  · intro q _ q' _ h
    have := congrArg Nat.Partition.parts h
    rw [r26a_parts_shiftCons, r26a_parts_shiftCons, Multiset.cons_inj_right] at this
    exact Nat.Partition.ext (Multiset.map_injective (add_left_injective 1) this)
  · intro p hp
    simp only [mem_filter, Nat.Partition.distincts, mem_univ, true_and] at hp
    have hn1 : 1 ≤ n := by omega
    let p' := Nat.Partition.partitionWithPartEquiv le_rfl hn1 ⟨p, hp.2.2⟩
    have hp' : p'.parts = p.parts.erase 1 := by
      simp [p', Nat.Partition.partitionWithPartEquiv_apply_parts]
    have hcard : Multiset.card p'.parts = m - 1 := by
      rw [hp', Multiset.card_erase_of_mem hp.2.2, hp.2.1]; rfl
    have h1 : 1 ∉ p'.parts := by
      rw [hp']; exact (Multiset.nodup_iff_count_le_one.mp hp.1 1 |> fun h =>
        fun hm1 => by
          have := Multiset.count_erase_self 1 p.parts
          have h2 := Multiset.count_pos.mpr hm1
          omega)
    have hN : n - m + Multiset.card p'.parts = n - 1 := by rw [hcard]; omega
    refine ⟨r26a_unshift p' (n - m) hN h1, ?_, ?_⟩
    · simp only [mem_filter, Nat.Partition.distincts, mem_univ, true_and]
      rw [r26a_parts_unshift, Multiset.card_map, hcard]
      refine ⟨r26a_nodup_map_pred (fun i hi => p'.parts_pos hi) ?_, rfl⟩
      rw [hp']; exact hp.1.erase 1
    · apply Nat.Partition.ext
      rw [r26a_parts_shiftCons, r26a_parts_unshift,
        r26a_map_pred_succ (fun i hi => p'.parts_pos hi), hp']
      exact Multiset.cons_erase hp.2.2

/-- Helper for (26.10.9) (agent p26a). -/
lemma r26a_atMost_succ (m N : ℕ) :
    partitionCountAtMostDistinct (m + 1) N = partitionCountAtMostDistinct m N +
      #{p ∈ Nat.Partition.distincts N | p.parts.card = m + 1} := by
  unfold partitionCountAtMostDistinct
  rw [← card_filter_add_card_filter_not (fun p : N.Partition => p.parts.card ≤ m), filter_filter,
    filter_filter]
  congr 2
  · exact filter_congr fun p _ => by omega
  · exact filter_congr fun p _ => by omega

/-- Helper for (26.10.9) (agent p26a). -/
lemma r26a_atMost_zero (N : ℕ) :
    partitionCountAtMostDistinct 0 N = #{p ∈ Nat.Partition.distincts N | p.parts.card = 0} := by
  unfold partitionCountAtMostDistinct
  congr 1
  exact filter_congr fun p _ => by omega

/-- (26.10.9), corrected, for exactly `m` distinct parts:
`q_m(n) = q_m(n - m) + q_{m-1}(n - m)` for `1 ≤ m ≤ n`, where
`q_m(n) = p_m(𝒟, n) - p_{m-1}(𝒟, n)`. -/
@[dlmf 26.10.E9 "corrected form for exactly m distinct parts"]
theorem card_distinct_card_eq_recurrence {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    #{p ∈ Nat.Partition.distincts n | p.parts.card = m} =
      #{p ∈ Nat.Partition.distincts (n - m) | p.parts.card = m} +
        #{p ∈ Nat.Partition.distincts (n - m) | p.parts.card = m - 1} := by
  rw [← card_filter_add_card_filter_not (fun p : n.Partition => 1 ∉ p.parts), filter_filter,
    filter_filter, add_comm]
  simp only [not_not]
  rw [← r26a_card_distinct_no_one hmn, ← r26a_card_distinct_one hm hmn, add_comm]

/-- (26.10.9), corrected: `p_m(𝒟, n) = p_{m-1}(𝒟, n) + p_m(𝒟, n - m) - p_{m-2}(𝒟, n - m)`
for `1 ≤ m ≤ n` (with `p_{-1} = 0`). DLMF prints `p_m(𝒟, n) = p_m(𝒟, n - m) + p_{m-1}(𝒟, n)`,
which fails already at `m = n = 2` (see the module docstring). -/
@[dlmf 26.10.E9
  "corrected: printed recurrence is false; removing 1 from m distinct parts leaves m or m-1 parts"]
theorem partitionCountAtMostDistinct_recurrence {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    (partitionCountAtMostDistinct m n : ℤ) =
      partitionCountAtMostDistinct (m - 1) n + partitionCountAtMostDistinct m (n - m) -
        if 2 ≤ m then (partitionCountAtMostDistinct (m - 2) (n - m) : ℤ) else 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have h1 := r26a_atMost_succ k n
  have h2 := r26a_atMost_succ k (n - (k + 1))
  have h3 := card_distinct_card_eq_recurrence hm hmn
  simp only [Nat.add_sub_cancel] at h3 ⊢
  rcases k with _ | k
  · have h4 := r26a_atMost_zero (n - 1)
    simp only [zero_add] at h1 h2 h3 h4 ⊢
    norm_num
    push_cast [h1, h2, h3, h4]
    ring
  · have h4 := r26a_atMost_succ k (n - (k + 1 + 1))
    have h2le : 2 ≤ k + 1 + 1 := by omega
    simp only [h2le, ↓reduceIte, show k + 1 + 1 - 2 = k by omega]
    push_cast [h1, h2, h3, h4]
    ring

/-- (26.10.10): `p(𝒟k, n) = ∑_m p_m(n - km²/2 - m + km/2)` over the `m ≥ 0` with nonnegative
argument; the argument is `n - k·m(m-1)/2 - m`. -/
@[dlmf 26.10.E10]
theorem partitionCountDiff_eq_sum (k n : ℕ) :
    partitionCountDiff k n =
      ∑ m ∈ range (n + 1) with k * m.choose 2 + m ≤ n,
        partitionCountAtMostParts m (n - (k * m.choose 2 + m)) :=
  s26a_partitionCountDiff_eq_sum k n

/-- (26.10.11): `n p(∈ S, n) = ∑_{t=1}^n p(∈ S, n - t) ∑_{j ∣ t, j ∈ S} j` (stated multiplied
by `n`). -/
@[dlmf 26.10.E11]
theorem partitionCountIn_recurrence (S : Set ℕ) [DecidablePred (· ∈ S)] (n : ℕ) :
    n * partitionCountIn S n =
      ∑ t ∈ Icc 1 n, partitionCountIn S (n - t) * ∑ j ∈ t.divisors with j ∈ S, j :=
  r26a_card_restricted_recurrence (· ∈ S) n

/-! ### Rogers–Ramanujan (agent p26a) -/

/-- Coefficients of two natural-number power series agreeing on the unit disk are equal. -/
theorem s26a_coeff_unique_nat {a b : ℕ → ℕ} {F : ℂ → ℂ}
    (ha : ∀ q : ℂ, ‖q‖ < 1 → HasSum (fun n => (a n : ℂ) * q ^ n) (F q))
    (hb : ∀ q : ℂ, ‖q‖ < 1 → HasSum (fun n => (b n : ℂ) * q ^ n) (F q)) : a = b := by
  have hser : ∀ c : ℕ → ℕ, (∀ q : ℂ, ‖q‖ < 1 → HasSum (fun n => (c n : ℂ) * q ^ n) (F q)) →
      HasFPowerSeriesAt (FormalMultilinearSeries.ofScalars ℂ fun n => (c n : ℂ)).sum
        (FormalMultilinearSeries.ofScalars ℂ fun n => (c n : ℂ)) 0 ∧
      ∀ q : ℂ, ‖q‖ < 1 →
        (FormalMultilinearSeries.ofScalars ℂ fun n => (c n : ℂ)).sum q = F q := by
    intro c hc
    set P := FormalMultilinearSeries.ofScalars ℂ fun n => (c n : ℂ)
    have hsumP : ∀ q : ℂ, P.sum q = ∑' n, (c n : ℂ) * q ^ n := fun q => by
      change FormalMultilinearSeries.ofScalarsSum _ q = _
      rw [FormalMultilinearSeries.ofScalars_sum_eq]; simp [smul_eq_mul]
    have hrad : 1 ≤ P.radius := by
      refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
      refine P.le_radius_of_summable_norm ?_
      have hr1 : (r : ℝ) < 1 := by exact_mod_cast hr
      have h := (hc (r : ℂ) (by simpa using hr1)).summable
      have h' : Summable fun n => (c n : ℝ) * (r : ℝ) ^ n := by
        rw [← Complex.summable_ofReal]; simpa using h
      simpa [P, FormalMultilinearSeries.ofScalars_norm] using h'
    refine ⟨(P.hasFPowerSeriesOnBall (lt_of_lt_of_le zero_lt_one hrad)).hasFPowerSeriesAt,
      fun q hq => by rw [hsumP]; exact (hc q hq).tsum_eq⟩
  obtain ⟨h1, e1⟩ := hser a ha
  obtain ⟨h2, e2⟩ := hser b hb
  have hev : ∀ᶠ z in nhds (0 : ℂ),
      (FormalMultilinearSeries.ofScalars ℂ fun n => (a n : ℂ)).sum z =
        (FormalMultilinearSeries.ofScalars ℂ fun n => (b n : ℂ)).sum z := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) one_pos] with z hz
    have : ‖z‖ < 1 := by simpa using hz
    rw [e1 z this, e2 z this]
  have := FormalMultilinearSeries.ofScalars_series_injective ℂ ℂ
    (h1.eq_formalMultilinearSeries_of_eventually h2 hev)
  ext n
  exact_mod_cast congrFun this n

/-- A product over two residue classes mod 5. -/
theorem s26a_hasProd_two_progressions {q : ℂ} (hq : ‖q‖ < 1) {a b : ℕ} (ha : 1 ≤ a)
    (hab : a < b) (hb : b < 5) (S : Set ℕ) [DecidablePred (· ∈ S)]
    (hS : ∀ n, n ∈ S ↔ 1 ≤ n ∧ (n % 5 = a ∨ n % 5 = b)) :
    HasProd (fun j : ℕ => if j + 1 ∈ S then (1 - q ^ (j + 1))⁻¹ else 1)
      ((qPochhammerInf (q ^ a) (q ^ 5))⁻¹ * (qPochhammerInf (q ^ b) (q ^ 5))⁻¹) := by
  have hpos : ∀ r : ℕ, 0 < r → ‖q ^ r‖ < 1 := fun r hr => by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq hr.ne'
  set ι : ℕ ⊕ ℕ → ℕ := Sum.elim (fun i => 5 * i + (a - 1)) (fun i => 5 * i + (b - 1)) with hι
  have hιinj : Function.Injective ι := by
    rintro (i | i) (j | j) h <;> simp only [hι, Sum.elim_inl, Sum.elim_inr, Sum.inl.injEq,
      Sum.inr.injEq, reduceCtorEq] at h ⊢ <;> omega
  rw [← hιinj.hasProd_iff]
  · apply HasProd.sum
    · convert (r26a_hasProd_one_sub (w := q ^ a) (hpos 5 (by norm_num))).inv₀
        (qPochhammerInf_ne_zero_of_norm_lt_one (hpos a (by omega)) (hpos 5 (by norm_num)))
        using 1
      ext i
      simp only [Function.comp, hι, Sum.elim_inl]
      rw [ite_eq_left ((hS _).mpr ⟨by omega, Or.inl (by omega)⟩), ← pow_mul, ← pow_add,
        show 5 * i + (a - 1) + 1 = a + 5 * i by omega]
    · convert (r26a_hasProd_one_sub (w := q ^ b) (hpos 5 (by norm_num))).inv₀
        (qPochhammerInf_ne_zero_of_norm_lt_one (hpos b (by omega)) (hpos 5 (by norm_num)))
        using 1
      ext i
      simp only [Function.comp, hι, Sum.elim_inr]
      rw [ite_eq_left ((hS _).mpr ⟨by omega, Or.inr (by omega)⟩), ← pow_mul, ← pow_add,
        show 5 * i + (b - 1) + 1 = b + 5 * i by omega]
  · intro j hj
    refine ite_eq_right fun hS' => ?_
    obtain ⟨h1, h2⟩ := (hS _).mp hS'
    rcases h2 with h2 | h2
    · exact hj ⟨Sum.inl ((j + 1) / 5), by simp only [hι, Sum.elim_inl]; omega⟩
    · exact hj ⟨Sum.inr ((j + 1) / 5), by simp only [hι, Sum.elim_inr]; omega⟩

lemma s26a_mem_residueSetPM_five (j n : ℕ) (hj : j < 5) :
    n ∈ residueSetPM j 5 ↔ 1 ≤ n ∧ (n % 5 = j % 5 ∨ n % 5 = (5 - j) % 5) := by
  simp only [residueSetPM, Set.mem_ofPred_eq, Int.ModEq]
  omega

lemma s26a_two_choose_add (m : ℕ) : 2 * m.choose 2 + m = m * m := by
  rcases m with _ | m
  · simp
  · rw [Nat.choose_two_right, Nat.add_sub_cancel]
    obtain ⟨t, ht⟩ := Nat.even_mul_pred_self (m + 1)
    rw [Nat.add_sub_cancel] at ht
    rw [ht, show t + t = 2 * t by ring, Nat.mul_div_cancel_left t two_pos]
    nlinarith

/-- The generating function of `p(∈ S, n)` for `S` two residue classes mod 5. -/
lemma s26a_hasSum_partitionCountIn_five {q : ℂ} (hq : ‖q‖ < 1) {a b : ℕ} (ha : 1 ≤ a)
    (hab : a < b) (hb : b < 5) (S : Set ℕ) [DecidablePred (· ∈ S)]
    (hS : ∀ n, n ∈ S ↔ 1 ≤ n ∧ (n % 5 = a ∨ n % 5 = b)) :
    HasSum (fun n => (partitionCountIn S n : ℂ) * q ^ n)
      (1 / (qPochhammerInf (q ^ a) (q ^ 5) * qPochhammerInf (q ^ b) (q ^ 5))) := by
  obtain ⟨h1, h2⟩ := hasSum_partitionCountIn hq S
  rw [h2.unique (s26a_hasProd_two_progressions hq ha hab hb S hS), ← mul_inv, ← one_div] at h1
  exact h1

/-- (26.10.13), first Rogers–Ramanujan identity: `p(𝒟2, n) = p(∈ A_{1,5}, n)`. -/
@[dlmf 26.10.E13]
theorem partitionCountDiff_two_eq (n : ℕ) :
    partitionCountDiff 2 n = partitionCountIn (residueSetPM 1 5) n := by
  refine congrFun (s26a_coeff_unique_nat (F := fun q =>
    1 / (qPochhammerInf (q ^ 1) (q ^ 5) * qPochhammerInf (q ^ 4) (q ^ 5))) (fun q hq => ?_)
    (fun q hq => s26a_hasSum_partitionCountIn_five hq le_rfl (by norm_num) (by norm_num) _
      fun n => s26a_mem_residueSetPM_five 1 n (by norm_num))) n
  have h := (hasSum_partitionCountDiff hq 2).1
  simp_rw [s26a_two_choose_add] at h
  rw [DLMF.Bailey.rogers_ramanujan_first hq] at h
  simpa using h

/-- (26.10.14), second Rogers–Ramanujan identity: `p(𝒟2, ∈ T, n) = p(∈ A_{2,5}, n)`. -/
@[dlmf 26.10.E14]
theorem partitionCountDiffTwoNoOne_eq (n : ℕ) :
    partitionCountDiffTwoNoOne n = partitionCountIn (residueSetPM 2 5) n := by
  refine congrFun (s26a_coeff_unique_nat (F := fun q =>
    1 / (qPochhammerInf (q ^ 2) (q ^ 5) * qPochhammerInf (q ^ 3) (q ^ 5))) (fun q hq => ?_)
    (fun q hq => s26a_hasSum_partitionCountIn_five hq (by norm_num) (by norm_num) (by norm_num)
      _ fun n => s26a_mem_residueSetPM_five 2 n (by norm_num))) n
  have hc : ∀ n, partitionCountDiffTwoNoOne n = ∑ m ∈ range (n + 1) with m * (m + 1) ≤ n,
      partitionCountAtMostParts m (n - m * (m + 1)) := by
    intro n
    have h := s26a_card_diff_min_eq_sum 2 2 n (by norm_num)
    have he : ∀ m : ℕ, 2 * m.choose 2 + 2 * m = m * (m + 1) := fun m => by
      have := s26a_two_choose_add m; nlinarith
    simp only [he] at h
    rw [← h]
    rfl
  have h := (s26a_hasSum_staircase hq (fun m => m * (m + 1)) (fun m => by nlinarith)
    partitionCountDiffTwoNoOne hc).1
  have he : (∑' m : ℕ, q ^ (m * (m + 1)) * ∏ j ∈ Icc 1 m, (1 - q ^ j)⁻¹) =
      ∑' m : ℕ, q ^ (m * (m + 1) : ℕ) / qPochhammer q q m := by
    congr 1; ext m; rw [s26a_qPochhammer_eq_prod, div_eq_mul_inv, prod_inv_distrib]
  rw [he, DLMF.Bailey.rogers_ramanujan_second hq] at h
  exact h

/-- (26.10.15), Schur's theorem: `p(𝒟'3, n) = p(∈ A_{1,6}, n)`. -/
@[dlmf 26.10.E15]
theorem partitionCountSchur_eq (n : ℕ) :
    partitionCountSchur n = partitionCountIn (residueSetPM 1 6) n := by
  sorry

/-- §26.10(iv): `p(𝒟'3, n) ≤ p(𝒟3, n)`. -/
@[dlmf 26.10.iv]
theorem partitionCountSchur_le (n : ℕ) : partitionCountSchur n ≤ partitionCountDiff 3 n := by
  unfold partitionCountSchur partitionCountDiff
  exact Finset.card_le_card fun p => by simp only [mem_filter]; exact fun h => ⟨h.1, h.2.1⟩

/-- A partition of `n` from a multiset of positive parts. -/
def r26a_ofParts (n : ℕ) (s : Multiset ℕ) (hpos : ∀ i ∈ s, 0 < i) (hs : s.sum = n) :
    n.Partition := ⟨s, fun hi => hpos _ hi, hs⟩

/-- For distinct parts, `PartsDifferAtLeast` is a condition on pairs of different parts. -/
lemma r26a_partsDiffer_iff_of_nodup {n : ℕ} (k : ℕ) (p : n.Partition) (hp : p.parts.Nodup) :
    PartsDifferAtLeast k p ↔ ∀ x ∈ p.parts, ∀ y ∈ p.parts, x ≠ y → x + k ≤ y ∨ y + k ≤ x := by
  unfold PartsDifferAtLeast
  refine forall₂_congr fun x hx => ⟨fun h y hy hxy => h y ((hp.mem_erase_iff).2 ⟨Ne.symm hxy, hy⟩),
    fun h y hy => ?_⟩
  rw [hp.mem_erase_iff] at hy
  exact h y hy.2 (Ne.symm hy.1)

/-- A witness against Schur's condition: parts differ by at least `3`, two multiples of `3`
differ by `3`. -/
lemma r26a_exists_bad (n : ℕ) (hn : n = 9 ∨ 15 ≤ n) :
    ∃ p : n.Partition, PartsDifferAtLeast 3 p ∧ ¬ SchurCondition p := by
  -- the parts: two multiples of 3 at distance 3 and possibly a third part
  obtain ⟨a, c, ha, hcs, hsum⟩ : ∃ a c : ℕ, (a = 3 ∨ a = 6) ∧
      (c = 0 ∨ (c ≥ 1 ∧ (c + 3 ≤ a ∨ a + 6 ≤ c))) ∧ a + (a + 3) + c = n := by
    rcases hn with rfl | hn
    · exact ⟨3, 0, Or.inl rfl, Or.inl rfl, rfl⟩
    · by_cases h18 : 18 ≤ n
      · exact ⟨3, n - 9, Or.inl rfl, Or.inr ⟨by omega, Or.inr (by omega)⟩, by omega⟩
      · exact ⟨6, n - 15, Or.inr rfl, by omega, by omega⟩
  have h3a : 3 ∣ a := by rcases ha with rfl | rfl <;> norm_num
  -- common conclusion from the list of parts
  have key : ∀ (s : Multiset ℕ), s.Nodup → a ∈ s → a + 3 ∈ s → (∀ i ∈ s, 0 < i) → s.sum = n →
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y → x + 3 ≤ y ∨ y + 3 ≤ x) →
      ∃ p : n.Partition, PartsDifferAtLeast 3 p ∧ ¬ SchurCondition p := by
    intro s hnd has has3 hpos hs hd
    refine ⟨r26a_ofParts n s hpos hs, (r26a_partsDiffer_iff_of_nodup 3 _ hnd).2 hd, fun h => ?_⟩
    have := h.2 a has (a + 3) ((hnd.mem_erase_iff).2 ⟨by omega, has3⟩) h3a (by omega)
    omega
  rcases hcs with rfl | ⟨hc1, hc⟩
  · refine key {a, a + 3} ?_ (by simp) (by simp) ?_ (by simp; omega) ?_
    · simp
    · intro i hi; simp at hi; rcases ha with rfl | rfl <;> omega
    · intro x hx y hy hxy; simp at hx hy; omega
  · refine key {a, a + 3, c} ?_ (by simp) (by simp) ?_ (by simp; omega) ?_
    · simp; omega
    · intro i hi; simp at hi; rcases ha with rfl | rfl <;> omega
    · intro x hx y hy hxy; simp at hx hy; omega


/-- A partition with parts differing by at least `3` that violates Schur's condition has
`n = 9` or `n ≥ 15`. -/
lemma r26a_bad_imp {n : ℕ} (p : n.Partition) (hd : PartsDifferAtLeast 3 p)
    (hs : ¬ SchurCondition p) : n = 9 ∨ 15 ≤ n := by
  unfold SchurCondition at hs
  simp only [hd, true_and, not_forall] at hs
  obtain ⟨x, hx, y, hy, h3x, h3y, hxy⟩ := hs
  have hd' := hd x hx y hy
  have hyx : y ∈ p.parts := Multiset.mem_of_mem_erase hy
  -- `lo ∈ parts`, `lo + 3 ∈ parts.erase lo`
  obtain ⟨lo, hlo, hhi, h3lo⟩ : ∃ lo, lo ∈ p.parts ∧ lo + 3 ∈ p.parts.erase lo ∧ 3 ∣ lo := by
    rcases hd' with h | h
    · have : y = x + 3 := by omega
      exact ⟨x, hx, this ▸ hy, h3x⟩
    · have hxe : x = y + 3 := by omega
      refine ⟨y, hyx, ?_, h3y⟩
      rw [← hxe]; exact Multiset.mem_erase_of_ne (by omega) |>.2 hx
  have hlo0 := p.parts_pos hlo
  set rest := (p.parts.erase lo).erase (lo + 3)
  have e : p.parts = lo ::ₘ (lo + 3) ::ₘ rest := by
    rw [Multiset.cons_erase hhi, Multiset.cons_erase hlo]
  have hsum : lo + (lo + 3) + rest.sum = n := by
    have := p.parts_sum
    rw [e, Multiset.sum_cons, Multiset.sum_cons] at this
    omega
  rcases Nat.lt_or_ge lo 6 with hl6 | hl6
  · have hl3 : lo = 3 := by obtain ⟨t, rfl⟩ := h3lo; omega
    subst hl3
    rcases Multiset.empty_or_exists_mem rest with h0 | ⟨c, hc⟩
    · rw [h0, Multiset.sum_zero] at hsum; left; omega
    · right
      have hc1 : c ∈ p.parts.erase 3 := Multiset.mem_of_mem_erase hc
      have hc2 : c ∈ p.parts.erase (3 + 3) := by
        have : c ∈ (p.parts.erase (3 + 3)).erase 3 := by
          rw [Multiset.erase_comm]; exact hc
        exact Multiset.mem_of_mem_erase this
      have hc0 := p.parts_pos (Multiset.mem_of_mem_erase hc1)
      have d1 := hd 3 hlo c hc1
      have d2 := hd (3 + 3) (Multiset.mem_of_mem_erase hhi) c hc2
      have hcs : c ≤ rest.sum := Multiset.le_sum_of_mem hc
      omega
  · right; omega

/-- §26.10(iv), corrected: `p(𝒟'3, n) < p(𝒟3, n)` exactly for `n = 9` and `n ≥ 15`. DLMF
states strict inequality for `n ≥ 9`, but equality holds for `10 ≤ n ≤ 14`. -/
@[dlmf 26.10.iv "corrected: strict for n = 9 and n ≥ 15 (equality for 10 ≤ n ≤ 14)"]
theorem partitionCountSchur_lt_iff (n : ℕ) :
    partitionCountSchur n < partitionCountDiff 3 n ↔ n = 9 ∨ 15 ≤ n := by
  unfold partitionCountSchur partitionCountDiff
  have hsub : (univ.filter fun p : n.Partition => SchurCondition p) ⊆
      univ.filter fun p : n.Partition => PartsDifferAtLeast 3 p :=
    fun p => by simp only [mem_filter, mem_univ, true_and]; exact fun h => h.1
  constructor
  · intro h
    obtain ⟨p, hpB, hpA⟩ := exists_of_ssubset (ssubset_of_subset_of_ne hsub (fun e => by
      rw [e] at h; exact lt_irrefl _ h))
    simp only [mem_filter, mem_univ, true_and] at hpB hpA
    exact r26a_bad_imp p hpB hpA
  · intro hn
    obtain ⟨p, hd, hs⟩ := r26a_exists_bad n hn
    refine card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun e => ?_⟩)
    have : p ∈ univ.filter fun p : n.Partition => PartsDifferAtLeast 3 p := by simp [hd]
    rw [← e] at this
    simp only [mem_filter, mem_univ, true_and] at this
    exact hs this

/-- §26.10(iv), Alder's conjecture (Yee 2004; DLMF's statement): for `k > 3`,
`p(𝒟k, n) ≥ p(∈ A_{1,k+3}, n)`. -/
@[dlmf 26.10.iv]
theorem partitionCountIn_le_partitionCountDiff {k : ℕ} (hk : 3 < k) (n : ℕ) :
    partitionCountIn (residueSetPM 1 (k + 3)) n ≤ partitionCountDiff k n := by
  sorry

/-- §26.10(iv): the inequality is strict for all sufficiently large `n` when `k = 2^m - 1`,
`m = 3, 4, 5`, or `k ≥ 32` (Yee 2004). -/
@[dlmf 26.10.iv]
theorem eventually_partitionCountIn_lt_partitionCountDiff {k : ℕ}
    (hk : k = 7 ∨ k = 15 ∨ k = 31 ∨ 32 ≤ k) :
    ∀ᶠ n in atTop, partitionCountIn (residueSetPM 1 (k + 3)) n < partitionCountDiff k n := by
  sorry

/-- (26.10.16): `p(𝒟, n) ∼ e^{π √(n/3)}/(768 n³)^{1/4}` as `n → ∞`. -/
@[dlmf 26.10.E16]
theorem partitionCountDistinct_isEquivalent :
    (fun n : ℕ => (partitionCountDistinct n : ℝ)) ~[atTop]
      fun n : ℕ => Real.exp (Real.pi * Real.sqrt (n / 3)) / (768 * (n : ℝ) ^ 3) ^ (1 / 4 : ℝ) := by
  sorry

/-- (26.10.20): the sawtooth `[[x]] = x - ⌊x⌋ - 1/2` for `x ∉ ℤ`, `[[x]] = 0` for `x ∈ ℤ`. -/
@[dlmf 26.10.E20]
def sawtooth (x : ℝ) : ℝ := if Int.fract x = 0 then 0 else x - ⌊x⌋ - 1 / 2

/-- (26.10.19): `f(h, k) = ∑_{j=1}^k [[(2j-1)/(2k)]] [[h(2j-1)/k]]`. -/
@[dlmf 26.10.E19]
def distinctPartitionDedekindSum (h k : ℕ) : ℝ :=
  ∑ j ∈ Icc 1 k, sawtooth ((2 * j - 1 : ℝ) / (2 * k)) * sawtooth ((h : ℝ) * (2 * j - 1) / k)

/-- (26.10.18), corrected: `A_k(n) = ∑_{1 ≤ h ≤ k, (h,k) = 1} e^{π i f(h,k) - 2π i n h/k}`.
DLMF prints the range `1 < h ≤ k`, which gives `A_1(n) = 0` (see the module docstring). -/
@[dlmf 26.10.E18 "corrected: summation range 1 ≤ h ≤ k (printed 1 < h ≤ k)"]
def distinctPartitionKloosterman (k n : ℕ) : ℂ :=
  ∑ h ∈ Icc 1 k with Nat.Coprime h k,
    Complex.exp (Real.pi * Complex.I * distinctPartitionDedekindSum h k -
      2 * Real.pi * Complex.I * n * h / k)

/-- The sawtooth function has period `1`. -/
lemma r26a_sawtooth_add_int (x : ℝ) (m : ℤ) : sawtooth (x + m) = sawtooth x := by
  unfold sawtooth
  rw [Int.fract_add_intCast, Int.floor_add_intCast]
  push_cast; ring_nf

/-- The sawtooth function is odd. -/
lemma r26a_sawtooth_neg (x : ℝ) : sawtooth (-x) = -sawtooth x := by
  unfold sawtooth
  by_cases hx : Int.fract x = 0
  · have h0 : Int.fract (-x) = 0 := Int.fract_neg_eq_zero.mpr hx
    simp [hx, h0]
  · have h0 : Int.fract (-x) ≠ 0 := fun h => hx (Int.fract_neg_eq_zero.mp h)
    simp only [hx, h0, ↓reduceIte]
    have h1 := Int.fract_neg hx
    rw [← Int.self_sub_floor, ← Int.self_sub_floor] at h1
    linarith

/-- `f(k - h, k) = -f(h, k)`. -/
lemma r26a_dedekind_sub (h k : ℕ) (hhk : h ≤ k) (hk : 0 < k) :
    distinctPartitionDedekindSum (k - h) k = -distinctPartitionDedekindSum h k := by
  unfold distinctPartitionDedekindSum
  rw [← sum_neg_distrib]
  refine sum_congr rfl fun j _ => ?_
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have : ((k - h : ℕ) : ℝ) * (2 * j - 1) / k =
      -((h : ℝ) * (2 * j - 1) / k) + ((2 * j - 1 : ℤ) : ℝ) := by
    push_cast [Nat.cast_sub hhk]; field_simp; ring
  rw [this, r26a_sawtooth_add_int, r26a_sawtooth_neg]; ring

open Complex in
/-- §26.10(vi): the terms for `h` and `k - h` are complex conjugates. -/
lemma r26a_kloosterman_im (k n : ℕ) : (distinctPartitionKloosterman k n).im = 0 := by
  rcases Nat.lt_or_ge k 2 with hk | hk
  · interval_cases k
    · simp [distinctPartitionKloosterman]
    · have hf : distinctPartitionDedekindSum 1 1 = 0 := by
        simp [distinctPartitionDedekindSum, sawtooth]
      have hs : (Icc 1 1).filter (fun h => Nat.Coprime h 1) = {1} := by decide
      rw [distinctPartitionKloosterman, hs, sum_singleton, hf]
      have h1 : (Real.pi : ℂ) * I * ((0 : ℝ) : ℂ) -
            2 * Real.pi * I * n * ((1 : ℕ) : ℂ) / ((1 : ℕ) : ℂ) =
          0 - (n : ℂ) * (2 * Real.pi * I) := by push_cast; ring
      rw [h1, exp_sub, exp_nat_mul_two_pi_mul_I, div_one, exp_zero, one_im]
  rw [← conj_eq_iff_im]
  unfold distinctPartitionKloosterman
  rw [map_sum]
  refine sum_nbij' (fun h => k - h) (fun h => k - h) ?_ ?_ ?_ ?_ ?_
  · intro h hh
    simp only [mem_filter, mem_Icc] at hh ⊢
    have hne : h ≠ k := by
      rintro rfl
      have := hh.2; rw [Nat.coprime_self] at this; omega
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rw [Nat.coprime_self_sub_left hh.1.2]; exact hh.2
  · intro h hh
    simp only [mem_filter, mem_Icc] at hh ⊢
    have hne : h ≠ k := by
      rintro rfl
      have := hh.2; rw [Nat.coprime_self] at this; omega
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rw [Nat.coprime_self_sub_left hh.1.2]; exact hh.2
  · intro h hh; simp only [mem_filter, mem_Icc] at hh; omega
  · intro h hh; simp only [mem_filter, mem_Icc] at hh; omega
  · intro h hh
    simp only [mem_filter, mem_Icc] at hh
    have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    rw [← exp_conj, r26a_dedekind_sub h k hh.1.2 (by omega)]
    have e : (Real.pi : ℂ) * I * ((-distinctPartitionDedekindSum h k : ℝ) : ℂ) -
        2 * Real.pi * I * n * ((k - h : ℕ) : ℂ) / k =
        (starRingEnd ℂ) ((Real.pi : ℂ) * I * (distinctPartitionDedekindSum h k : ℂ) -
          2 * Real.pi * I * n * h / k) - (n : ℂ) * (2 * Real.pi * I) := by
      simp only [map_sub, map_mul, map_div₀, conj_ofReal, conj_I, map_natCast, map_ofNat]
      push_cast [Nat.cast_sub hh.1.2]
      field_simp
      ring
    rw [e, exp_sub, exp_nat_mul_two_pi_mul_I, div_one]
/-- §26.10(vi): `A_k(n)` is real-valued. -/
@[dlmf 26.10.vi]
theorem distinctPartitionKloosterman_im (k n : ℕ) : (distinctPartitionKloosterman k n).im = 0 :=
  r26a_kloosterman_im k n

/-- (26.10.17): `p(𝒟, n) = π ∑_{k ≥ 1} A_{2k-1}(n)/((2k-1)√(24n+1)) I₁(π/(2k-1) √((24n+1)/72))`
(with the corrected `A_k`, (26.10.18)); `I₁` is the project's `DLMF.Bessel.besselI 1`. -/
@[dlmf 26.10.E17]
theorem hasSum_partitionCountDistinct_bessel (n : ℕ) :
    HasSum (fun k : ℕ => (Real.pi : ℂ) * distinctPartitionKloosterman (2 * k + 1) n /
        ((2 * k + 1 : ℂ) * (Real.sqrt (24 * n + 1) : ℂ)) *
          DLMF.Bessel.besselI 1 ((Real.pi / (2 * k + 1) * Real.sqrt ((24 * n + 1) / 72) : ℝ)))
      (partitionCountDistinct n : ℂ) := by
  sorry

end DLMF.Combinatorics
