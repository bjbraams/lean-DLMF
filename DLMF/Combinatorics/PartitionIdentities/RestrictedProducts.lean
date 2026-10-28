/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Combinatorics.RestrictedPartitions
public import DLMF.Bessel.Modified
public import Mathlib.Combinatorics.Enumerative.Partition.Glaisher
public import DLMF.QSeries.QExponential
public import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries
public import Mathlib.RingTheory.PowerSeries.Expand
public import DLMF.Combinatorics.S26aStaircase
public import DLMF.Bailey

/-!
# Generating products for restricted partitions

Generating series and finite products for partitions with restrictions on their parts.

Source references and common attribution are retained in
`DLMF.Combinatorics.PartitionIdentities`.
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

/-- The minimum-gap condition on the finitely many parts of a partition is decidable. -/
instance {n : ℕ} (k : ℕ) (p : n.Partition) : Decidable (PartsDifferAtLeast k p) := by
  unfold PartsDifferAtLeast; infer_instance

/-- `p(𝒟k, n)`: partitions of `n` into parts with difference at least `k` (DLMF §26.10(i)). -/
@[dlmf 26.10.i]
def partitionCountDiff (k n : ℕ) : ℕ := #{p : n.Partition | PartsDifferAtLeast k p}

/-- Schur's condition: parts differ by at least 3, and multiples of 3 by at least 6. -/
def SchurCondition {n : ℕ} (p : n.Partition) : Prop :=
  PartsDifferAtLeast 3 p ∧
    ∀ a ∈ p.parts, ∀ b ∈ p.parts.erase a, 3 ∣ a → 3 ∣ b → a + 6 ≤ b ∨ b + 6 ≤ a

/-- Schur condition on the finitely many parts of a partition is decidable. -/
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

/-- Membership in the two prescribed residue classes is decidable. -/
instance (j k : ℕ) : DecidablePred (· ∈ residueSetPM j k) := fun n => by
  unfold residueSetPM; simp only [Set.mem_ofPred_eq]; infer_instance

/-- `T = {2, 3, 4, …}` (DLMF §26.10(i)). -/
@[dlmf 26.10.i]
def setGeTwo : Set ℕ := {n | 2 ≤ n}

/-- Membership in the set of natural parts at least two is decidable. -/
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

/-- Identity under the stated parameter and domain assumptions: `#{p : (0 : ℕ).Partition | P p} =
1`. -/
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

end DLMF.Combinatorics
end
end
