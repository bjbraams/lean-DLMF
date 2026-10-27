/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Combinatorics.Basic
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.Order.Partition.Finpartition
public import DLMFMathlib.Combinatorics.R26aFinpartition
public import DLMFMathlib.Combinatorics.Q26bSurjections

/-!
# Lattice paths: multinomial coefficients and set partitions (DLMF §26.4)

DLMF's multinomial coefficient `(n₁ + ⋯ + n_k; n₁, …, n_k)` is Mathlib's
`Nat.multinomial univ n` for `n : Fin k → ℕ` (more generally `Nat.multinomial s f`), defined as
`(∑ nᵢ)! / ∏ nᵢ!` (26.4.2, `Nat.multinomial_spec`); `Multiset.multinomial` is the same
coefficient for a multiset of parts. Mathlib also has the binomial case 26.4.1
(`Nat.binomial_eq_choose`) and the multinomial theorem 26.4.9
(`Finset.sum_pow_eq_sum_piAntidiag`); pointers are in `DLMF/Combinatorics/MathlibCoverage.lean`.

For the data of Table 26.4.1 the nonnegative integers `a₁, …, a_n` with `∑ j a_j = n`
(26.4.3) are the multiplicities `a_j = λ.parts.count j` of a partition `λ : Nat.Partition n`
(26.4.5); `m = ∑ a_j` (26.4.4) is the number of parts. `M₁` (26.4.6) is the multinomial
coefficient of the parts, `M₂` (26.4.7) counts permutations of `{1, …, n}` with cycle type `λ`
(fixed points included, `Equiv.Perm.partition`), and `M₃` (26.4.8) counts set partitions of
`{1, …, n}` with block sizes `λ`. Mathlib's `Equiv.Perm.card_of_cycleType` (cycle type without
fixed points) and `Multiset.bell` (whose defining formula is `M₃`, `Multiset.bell_mul_eq`) are
the closest upstream results.

**Source correction (implicit condition).** The recurrence 26.4.10 needs `m ≥ 1`: for `m = 0`
the left side is `1` and the sum is empty.
-/

@[expose] public section

open Finset

noncomputable section

namespace DLMF.Combinatorics

/-! ### Helpers (agent p26a) -/

/-- Reindexing a multinomial coefficient along an embedding. -/
lemma q26a_multinomial_map {α β : Type*} (s : Finset α) (g : α ↪ β) (f : β → ℕ) :
    Nat.multinomial (s.map g) f = Nat.multinomial s (f ∘ g) := by
  simp [Nat.multinomial, sum_map, prod_map]

/-- Counting the occurrences of `l` in `Fin.cons j g`. -/
lemma q26a_sum_consEquiv_eq {k N : ℕ} (j : Fin k) (g : Fin N → Fin k) (l : Fin k) :
    (∑ i : Fin (N + 1), if (Fin.consEquiv (fun _ => Fin k) (j, g)) i = l then 1 else 0) =
      #{i | g i = l} + if j = l then 1 else 0 := by
  rw [card_filter, Fin.sum_univ_succ]
  simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.cons_zero, Fin.cons_succ]
  ring

/-- The Pascal-type recurrence of multinomial coefficients:
`(n; n₁, …, n_k) = ∑_{j, n_j > 0} (n-1; n₁, …, n_j - 1, …, n_k)`. -/
lemma q26a_multinomial_rec {k N : ℕ} (n : Fin k → ℕ) (hN : ∑ i, n i = N + 1) :
    Nat.multinomial univ n =
      ∑ j ∈ univ.filter (fun j => 0 < n j),
        Nat.multinomial univ (Function.update n j (n j - 1)) := by
  have hspec := fun (m : Fin k → ℕ) => Nat.multinomial_spec univ m
  have hpos : ∀ m : Fin k → ℕ, (0 : ℚ) < ∏ i, ((m i).factorial : ℚ) :=
    fun m => prod_pos fun i _ => by exact_mod_cast (m i).factorial_pos
  have hq : ∀ m : Fin k → ℕ,
      (Nat.multinomial univ m : ℚ) = (∑ i, m i).factorial / ∏ i, ((m i).factorial : ℚ) := by
    intro m
    rw [eq_div_iff (hpos m).ne']
    have := hspec m
    exact_mod_cast (by rw [mul_comm] at this; exact this)
  have hupd : ∀ j, 0 < n j → (∑ i, Function.update n j (n j - 1) i = N) ∧
      (∏ i, ((Function.update n j (n j - 1) i).factorial : ℚ)) * n j =
        ∏ i, ((n i).factorial : ℚ) := by
    intro j hj
    constructor
    · rw [Finset.sum_update_of_mem (mem_univ j)]
      have := Finset.add_sum_erase univ n (mem_univ j)
      rw [← sdiff_singleton_eq_erase] at this
      omega
    · have e : ∀ i, ((Function.update n j (n j - 1) i).factorial : ℚ) =
          Function.update (fun i => ((n i).factorial : ℚ)) j ((n j - 1).factorial) i := by
        intro i; by_cases h : i = j
        · subst h; simp
        · simp [Function.update_of_ne h]
      simp_rw [e]
      rw [prod_update_of_mem (mem_univ j),
        ← prod_erase_mul univ (fun i => ((n i).factorial : ℚ)) (mem_univ j),
        ← sdiff_singleton_eq_erase]
      obtain ⟨a, ha⟩ : ∃ a, n j = a + 1 := ⟨n j - 1, by omega⟩
      rw [ha, Nat.add_sub_cancel, Nat.factorial_succ]; push_cast; ring
  have : (Nat.multinomial univ n : ℚ) = ∑ j ∈ univ.filter (fun j => 0 < n j),
      (Nat.multinomial univ (Function.update n j (n j - 1)) : ℚ) := by
    rw [hq]
    have h2 : ∀ j ∈ univ.filter (fun j => 0 < n j),
        (Nat.multinomial univ (Function.update n j (n j - 1)) : ℚ) =
          N.factorial * n j * (∏ i, ((n i).factorial : ℚ))⁻¹ := by
      intro j hj
      simp only [mem_filter, mem_univ, true_and] at hj
      obtain ⟨h1, h2⟩ := hupd j hj
      rw [hq, h1, ← h2]
      have : (n j : ℚ) ≠ 0 := by exact_mod_cast hj.ne'
      rw [mul_inv, show (N.factorial : ℚ) * n j *
          ((∏ i, ((Function.update n j (n j - 1) i).factorial : ℚ))⁻¹ * (n j : ℚ)⁻¹) =
        N.factorial * (∏ i, ((Function.update n j (n j - 1) i).factorial : ℚ))⁻¹ *
          ((n j : ℚ) * (n j : ℚ)⁻¹) by ring,
        mul_inv_cancel₀ this, mul_one, div_eq_mul_inv]
    rw [sum_congr rfl h2, ← sum_mul, ← mul_sum, ← div_eq_mul_inv]
    have h3 : ∑ j ∈ univ.filter (fun j => 0 < n j), (n j : ℚ) = N + 1 := by
      rw [sum_filter_of_ne
        (fun j _ h => by exact_mod_cast Nat.pos_of_ne_zero (by exact_mod_cast h))]
      exact_mod_cast hN
    rw [h3, hN, Nat.factorial_succ]; push_cast; ring
  exact_mod_cast this

/-- Placements of `N` labeled objects into `k` boxes with prescribed occupancies. -/
lemma q26a_card_boxPlacements (N : ℕ) : ∀ {k : ℕ} (n : Fin k → ℕ), ∑ i, n i = N →
    #{f : Fin N → Fin k | ∀ j, #{i | f i = j} = n j} = Nat.multinomial univ n := by
  induction N with
  | zero =>
    intro k n hn
    have hn0 : ∀ i, n i = 0 := fun i => by
      have := Finset.single_le_sum (fun j _ => Nat.zero_le (n j)) (mem_univ i); omega
    rw [Nat.multinomial, hn, show (∏ i, (n i).factorial) = 1 by simp [hn0]]
    simp only [Nat.factorial_zero, Nat.div_one]
    rw [card_eq_one]
    refine ⟨Fin.elim0, ?_⟩
    ext f
    simp only [mem_filter, mem_univ, true_and, mem_singleton, hn0]
    constructor
    · intro _; funext i; exact i.elim0
    · intro _ j; simp
  | succ N ih =>
    intro k n hn
    rw [q26a_multinomial_rec n hn]
    simp only [card_filter]
    rw [← (Fin.consEquiv fun _ => Fin k).sum_comp, Fintype.sum_prod_type]
    rw [← sum_filter_add_sum_filter_not univ (fun j => 0 < n j)]
    rw [sum_eq_zero (s := univ.filter fun j => ¬ 0 < n j) (fun j hj => ?_), add_zero]
    · refine sum_congr rfl fun j hj => ?_
      simp only [mem_filter, mem_univ, true_and] at hj
      have hsum : ∑ i, Function.update n j (n j - 1) i = N := by
        rw [Finset.sum_update_of_mem (mem_univ j)]
        have := Finset.add_sum_erase univ n (mem_univ j)
        rw [← sdiff_singleton_eq_erase] at this
        omega
      rw [← ih _ hsum, card_filter]
      refine sum_congr rfl fun g _ => ?_
      congr 1
      apply propext
      refine forall_congr' fun l => ?_
      rw [q26a_sum_consEquiv_eq]
      by_cases hl : l = j
      · subst hl
        simp only [Function.update_self, ite_true]
        omega
      · simp only [Function.update_of_ne hl, Ne.symm hl, ite_false, add_zero]
    · simp only [mem_filter, mem_univ, true_and, not_lt, Nat.le_zero] at hj
      refine sum_eq_zero fun g _ => ?_
      rw [if_neg]
      intro h
      have := h j
      rw [q26a_sum_consEquiv_eq] at this
      simp at this; omega

/-- The number of occurrences of `i` in `List.ofFn f`. -/
lemma q26a_count_ofFn {k : ℕ} : ∀ {N : ℕ} (f : Fin N → Fin k) (i : Fin k),
    (List.ofFn f).count i = #{x | f x = i} := by
  intro N
  induction N with
  | zero => intro f i; simp
  | succ N ih =>
    intro f i
    rw [List.ofFn_succ, List.count_cons, ih, card_filter, card_filter, Fin.sum_univ_succ]
    simp only [beq_iff_eq]
    ring

/-! ### Combinatorial interpretations (§26.4(i)) -/

/-- DLMF §26.4(i): `(n; n₁, …, n_k)` is the number of ways of placing `n = n₁ + ⋯ + n_k`
distinct objects into `k` labeled boxes with `n_j` objects in box `j`. -/
@[dlmf 26.4.i]
theorem card_boxPlacements_eq_multinomial {k : ℕ} (n : Fin k → ℕ) :
    #{f : Fin (∑ i, n i) → Fin k | ∀ j, #{i | f i = j} = n j} = Nat.multinomial univ n :=
  q26a_card_boxPlacements _ n rfl

/-- DLMF §26.4(i): `(n; n₁, …, n_k)` is the number of `k`-dimensional lattice paths from the
origin to `(n₁, …, n_k)`. -/
@[dlmf 26.4.i]
theorem card_latticePathsFin_eq_multinomial {k : ℕ} (n : Fin k → ℕ) :
    #(latticePathsFin n) = Nat.multinomial univ n := by
  rw [latticePathsFin, filter_image, card_image_of_injective _ List.ofFn_injective]
  simp only [q26a_count_ofFn]
  exact q26a_card_boxPlacements _ n rfl

/-- DLMF 26.4.2 (product form): `(n₁ + ⋯ + n_k; n₁, …, n_k) = ∏_{j=1}^{k-1}
C(n_j + n_{j+1} + ⋯ + n_k, n_j)` (the factor `j = k` is `C(n_k, n_k) = 1`). -/
@[dlmf 26.4.E2]
theorem multinomial_eq_prod_choose {k : ℕ} (n : Fin k → ℕ) :
    Nat.multinomial univ n = ∏ j : Fin k, (∑ i ∈ Ici j, n i).choose (n j) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.prod_univ_succ]
    conv_lhs => rw [Fin.univ_succ, Nat.multinomial_cons, q26a_multinomial_map, ih, sum_map]
    congr 1
    · congr 1
      rw [show Ici (0 : Fin (k + 1)) = univ by ext; simp, Fin.sum_univ_succ]
      rfl
    · refine prod_congr rfl fun j _ => ?_
      rw [← Fin.map_succEmb_Ici, sum_map]
      rfl

/-! ### Multiplicities of a partition (§26.4(i), Table 26.4.1) -/

/-- The parts of a partition of `n` are among `0, …, n`. -/
lemma c26a_toFinset_parts_subset {n : ℕ} (p : n.Partition) :
    p.parts.toFinset ⊆ range (n + 1) := by
  intro j hj
  rw [Multiset.mem_toFinset] at hj
  exact mem_range.mpr (Nat.lt_succ_of_le (Nat.Partition.le_of_mem_parts hj))

/-- DLMF 26.4.3: `n = a₁ + 2a₂ + ⋯ + n a_n`, `a_j` the multiplicity of `j` in `λ`. -/
@[dlmf 26.4.E3]
theorem sum_mul_count_parts {n : ℕ} (p : n.Partition) :
    ∑ j ∈ range (n + 1), j * p.parts.count j = n := by
  conv_rhs => rw [← p.parts_sum, Finset.sum_multiset_count]
  simp_rw [smul_eq_mul, mul_comm (Multiset.count _ _)]
  symm
  apply sum_subset (c26a_toFinset_parts_subset p)
  intro j _ hj; rw [Multiset.mem_toFinset] at hj; simp [Multiset.count_eq_zero_of_notMem hj]

/-- DLMF 26.4.4: `m = a₁ + a₂ + ⋯ + a_n` is the number of parts of `λ`. -/
@[dlmf 26.4.E4]
theorem sum_count_parts {n : ℕ} (p : n.Partition) :
    ∑ j ∈ range (n + 1), p.parts.count j = Multiset.card p.parts := by
  rw [← Multiset.toFinset_sum_count_eq]
  symm
  apply sum_subset (c26a_toFinset_parts_subset p)
  intro j _ hj; rw [Multiset.mem_toFinset] at hj; exact Multiset.count_eq_zero_of_notMem hj

/-- DLMF 26.4.5: `λ = 1^{a₁} 2^{a₂} ⋯ n^{a_n}`, i.e. the multiset of parts is the sum of
`a_j` copies of `j`. -/
@[dlmf 26.4.E5]
theorem parts_eq_sum_replicate {n : ℕ} (p : n.Partition) :
    p.parts = ∑ j ∈ range (n + 1), Multiset.replicate (p.parts.count j) j := by
  conv_lhs => rw [← Multiset.toFinset_sum_count_nsmul_eq p.parts]
  simp_rw [Multiset.nsmul_singleton]
  apply sum_subset (c26a_toFinset_parts_subset p)
  intro j _ hj; rw [Multiset.mem_toFinset] at hj; simp [Multiset.count_eq_zero_of_notMem hj]

/-- `m.multinomial · ∏_{x ∈ m} x! = (∑ m)!`. -/
lemma c26a_multinomial_mul_prod_factorial (m : Multiset ℕ) :
    m.multinomial * (m.map Nat.factorial).prod = m.sum.factorial := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons x m ih =>
    rw [Multiset.multinomial_cons, Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
    rw [show (x + m.sum).choose x * m.multinomial * (x.factorial * (m.map Nat.factorial).prod) =
      (x + m.sum).choose x * x.factorial * (m.multinomial * (m.map Nat.factorial).prod) by ring,
      ih, Nat.choose_symm_add, Nat.add_choose_mul_factorial_mul_factorial]

/-- DLMF 26.4.6: `M₁ = (n; 1, …, 1, …, n, …, n) = n! / ((1!)^{a₁} (2!)^{a₂} ⋯ (n!)^{a_n})`, the
multinomial coefficient of the parts of `λ` (`Multiset.multinomial`). -/
@[dlmf 26.4.E6]
theorem multinomial_parts_eq {n : ℕ} (p : n.Partition) :
    (p.parts.multinomial : ℚ) =
      n.factorial / ∏ j ∈ range (n + 1), ((j.factorial : ℚ) ^ p.parts.count j) := by
  have h := c26a_multinomial_mul_prod_factorial p.parts
  rw [p.parts_sum, Finset.prod_multiset_map_count] at h
  have e : ∏ j ∈ p.parts.toFinset, (j.factorial : ℚ) ^ p.parts.count j =
      ∏ j ∈ range (n + 1), (j.factorial : ℚ) ^ p.parts.count j := by
    apply prod_subset (c26a_toFinset_parts_subset p)
    intro j _ hj; rw [Multiset.mem_toFinset] at hj; simp [Multiset.count_eq_zero_of_notMem hj]
  rw [← e, eq_div_iff (by positivity)]
  exact_mod_cast h

/-- Transporting a partition along `a = b` keeps its parts. -/
lemma q26a_parts_cast {a b : ℕ} (h : a = b) (p : b.Partition) : (h ▸ p).parts = p.parts := by
  subst h; rfl

/-- The parts of size `1` of a partition. -/
lemma q26a_filter_lt_two_parts {n : ℕ} (p : n.Partition) :
    p.parts.filter (fun j => ¬ 2 ≤ j) = Multiset.replicate (p.parts.count 1) 1 := by
  rw [← Multiset.filter_eq']
  refine Multiset.filter_congr fun j hj => ?_
  have := p.parts_pos hj
  omega

/-- The parts `≥ 2` and the parts `= 1` of a partition of `n` add up to `n`. -/
lemma q26a_sum_filter_two_le {n : ℕ} (p : n.Partition) :
    (p.parts.filter (2 ≤ ·)).sum + p.parts.count 1 = n := by
  have h := Multiset.filter_add_not (2 ≤ ·) p.parts
  have := congrArg Multiset.sum h
  rw [Multiset.sum_add, q26a_filter_lt_two_parts, Multiset.sum_replicate, smul_eq_mul, mul_one,
    p.parts_sum] at this
  exact this

/-- DLMF 26.4.7: `M₂ = n! / (1^{a₁} a₁! 2^{a₂} a₂! ⋯ n^{a_n} a_n!)` is the number of
permutations of `{1, …, n}` with `a_j` cycles of length `j` (the cycle-type partition
`σ.partition`, fixed points included; for `n = 0` the empty permutation). -/
@[dlmf 26.4.E7]
theorem card_perm_partition_eq {n : ℕ} (p : n.Partition) :
    (#{σ : Equiv.Perm (Fin n) | σ.partition = (Fintype.card_fin n).symm ▸ p} : ℚ) =
      n.factorial / ∏ j ∈ range (n + 1),
        ((j : ℚ) ^ p.parts.count j * (p.parts.count j).factorial) := by
  set m := p.parts.filter (2 ≤ ·) with hm
  have hsum : m.sum + p.parts.count 1 = n := q26a_sum_filter_two_le p
  have hset :
      (univ.filter fun σ : Equiv.Perm (Fin n) => σ.partition = (Fintype.card_fin n).symm ▸ p) =
      univ.filter fun σ : Equiv.Perm (Fin n) => σ.cycleType = m := by
    ext σ
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · intro h
      rw [← Equiv.Perm.filter_parts_partition_eq_cycleType, h, q26a_parts_cast]
      exact Fintype.card_fin n
    · intro h
      apply Nat.Partition.ext
      rw [q26a_parts_cast, Equiv.Perm.parts_partition, h, Fintype.card_fin,
        ← Equiv.Perm.sum_cycleType, h, ← Multiset.filter_add_not (2 ≤ ·) p.parts,
        q26a_filter_lt_two_parts]
      · congr 2
        omega
      · exact Fintype.card_fin n
  rw [hset]
  have hmul := Equiv.Perm.card_of_cycleType_mul_eq (α := Fin n) m
  have hc : m.sum ≤ n ∧ ∀ a ∈ m, 2 ≤ a :=
    ⟨by omega, fun a ha => (Multiset.mem_filter.mp ha).2⟩
  rw [Fintype.card_fin, ite_cond_eq_true _ _ (eq_true hc)] at hmul
  have hD : (((n - m.sum).factorial * m.prod * ∏ x ∈ m.toFinset, (m.count x).factorial : ℕ) : ℚ) =
      ∏ j ∈ range (n + 1), ((j : ℚ) ^ p.parts.count j * (p.parts.count j).factorial) := by
    have hDn : (n - m.sum).factorial * m.prod * ∏ x ∈ m.toFinset, (m.count x).factorial =
        ∏ j ∈ range (n + 1), (j ^ p.parts.count j * (p.parts.count j).factorial) := by
      set F : ℕ → ℕ := fun j => j ^ p.parts.count j * (p.parts.count j).factorial with hF
      have ha0 : p.parts.count 0 = 0 :=
        Multiset.count_eq_zero.mpr fun h => (Nat.lt_irrefl 0) (p.parts_pos h)
      rw [← prod_filter_mul_prod_filter_not (range (n + 1)) (2 ≤ ·)]
      have h2 : ∏ j ∈ (range (n + 1)).filter (fun j => ¬ 2 ≤ j), F j =
          (p.parts.count 1).factorial := by
        rw [prod_subset (s₂ := {0, 1})]
        · rw [prod_pair (by norm_num)]
          simp [hF, ha0]
        · intro j hj; simp only [mem_filter, mem_range] at hj
          simp only [mem_insert, mem_singleton]; omega
        · intro j hj hj'
          simp only [mem_insert, mem_singleton] at hj
          simp only [mem_filter, mem_range, not_and, not_not] at hj'
          rcases hj with rfl | rfl
          · simp [hF, ha0]
          · have : n = 0 := by by_contra h; exact absurd (hj' (by omega)) (by omega)
            have : p.parts.count 1 = 0 := by omega
            simp [hF, this]
      have h1 : ∏ j ∈ (range (n + 1)).filter (2 ≤ ·), F j =
          ∏ x ∈ m.toFinset, x ^ m.count x * (m.count x).factorial := by
        calc ∏ j ∈ (range (n + 1)).filter (2 ≤ ·), F j
            = ∏ j ∈ (range (n + 1)).filter (2 ≤ ·), j ^ m.count j * (m.count j).factorial :=
              prod_congr rfl fun j hj => by
                simp only [mem_filter] at hj
                simp only [hF, hm, Multiset.count_filter_of_pos hj.2]
          _ = _ := by
            symm
            apply prod_subset
            · intro x hx
              rw [Multiset.mem_toFinset, hm, Multiset.mem_filter] at hx
              simp only [mem_filter, mem_range]
              exact ⟨Nat.lt_succ_of_le (Nat.Partition.le_of_mem_parts hx.1), hx.2⟩
            · intro x _ hx'
              rw [Multiset.mem_toFinset] at hx'
              rw [Multiset.count_eq_zero.mpr hx']; simp
      rw [h1, h2, prod_mul_distrib, ← Finset.prod_multiset_count,
        show n - m.sum = p.parts.count 1 by omega]
      ring
    exact_mod_cast hDn
  have hpos : (0 : ℚ) <
      ∏ j ∈ range (n + 1), ((j : ℚ) ^ p.parts.count j * (p.parts.count j).factorial) := by
    rw [← hD]
    have h0 : (n - m.sum).factorial * m.prod * ∏ x ∈ m.toFinset, (m.count x).factorial ≠ 0 :=
      fun h0 => by rw [h0, mul_zero] at hmul; exact Nat.factorial_ne_zero n hmul.symm
    exact_mod_cast Nat.pos_of_ne_zero h0
  rw [eq_div_iff hpos.ne', ← hD]
  exact_mod_cast hmul

/-- Value multisets of maps `Fin k → Fin (n + 1)` against value counts. -/
lemma r26a_map_val_eq_iff {n k : ℕ} (p : n.Partition) (s : Fin k → Fin (n + 1)) :
    univ.val.map (fun j => (s j : ℕ)) = p.parts ↔
      ∀ i : Fin (n + 1), #{j | s j = i} = p.parts.count (i : ℕ) := by
  have hc : ∀ a : ℕ, Multiset.count a (univ.val.map fun j => (s j : ℕ)) = #{j | (s j : ℕ) = a} :=
    fun a => q26b_count_map (fun j => (s j : ℕ)) a
  constructor
  · intro h i
    rw [← h, hc]
    congr 1
  · intro h
    ext a
    rw [hc]
    by_cases ha : a < n + 1
    · rw [show #{j | (s j : ℕ) = a} = #{j | s j = ⟨a, ha⟩} by
        congr 1, h]
    · rw [Multiset.count_eq_zero_of_notMem fun hm =>
        ha (Nat.lt_succ_of_le (Nat.Partition.le_of_mem_parts hm))]
      rw [card_eq_zero, filter_eq_empty_iff]
      intro j _ hj
      exact ha (hj ▸ (s j).2)

/-- DLMF 26.4.8: `M₃ = n! / ((1!)^{a₁} a₁! (2!)^{a₂} a₂! ⋯ (n!)^{a_n} a_n!)` is the number of
set partitions of `{1, …, n}` with `a_j` blocks of size `j`. -/
@[dlmf 26.4.E8]
theorem card_finpartition_blocks_eq {n : ℕ} (p : n.Partition) :
    (#{P : Finpartition (univ : Finset (Fin n)) | P.parts.val.map Finset.card = p.parts} : ℚ) =
      n.factorial / ∏ j ∈ range (n + 1),
        ((j.factorial : ℚ) ^ p.parts.count j * (p.parts.count j).factorial) := by
  -- `k! · #{P} = #{surjections with fibre sizes λ}`, classified by the fibre-size vector
  classical
  set k := Multiset.card p.parts with hk
  set c : Fin (n + 1) → ℕ := fun i => p.parts.count (i : ℕ) with hcdef
  set Pl : ℕ := (p.parts.map Nat.factorial).prod with hPl
  have hP : (0 : ℚ) < Pl := by
    exact_mod_cast Multiset.prod_pos fun x hx => by
      obtain ⟨y, -, rfl⟩ := Multiset.mem_map.mp hx; exact Nat.factorial_pos y
  -- step 1: finpartitions against surjections
  have h1 := r26a_card_surjective_filter (α := Fin n) k (· = p.parts)
  have hfilt : (univ.filter fun P : Finpartition (univ : Finset (Fin n)) => #P.parts = k ∧
      P.parts.val.map card = p.parts) =
      univ.filter fun P : Finpartition (univ : Finset (Fin n)) =>
        P.parts.val.map Finset.card = p.parts := by
    refine filter_congr fun P _ => ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
    rw [hk, ← h, Multiset.card_map]; rfl
  rw [hfilt] at h1
  -- step 2: classify the surjections by their fibre sizes
  let τ : (Fin n → Fin k) → (Fin k → Fin (n + 1)) := fun f j =>
    ⟨#{x | f x = j}, Nat.lt_succ_of_le ((card_le_univ _).trans (Fintype.card_fin n).le)⟩
  let T : Finset (Fin k → Fin (n + 1)) := {s | ∀ i, #{j | s j = i} = c i}
  have hA : (univ.filter fun f : Fin n → Fin k => Function.Surjective f ∧
      univ.val.map (fun j => #{x | f x = j}) = p.parts) = univ.filter fun f => τ f ∈ T := by
    refine filter_congr fun f _ => ?_
    have e : univ.val.map (fun j => #{x | f x = j}) = univ.val.map (fun j => ((τ f j : ℕ))) := rfl
    simp only [T, mem_filter, mem_univ, true_and]
    rw [e, r26a_map_val_eq_iff]
    refine ⟨fun h => h.2, fun h => ⟨fun j => ?_, h⟩⟩
    have hm : #{x | f x = j} ∈ p.parts := by
      rw [← (r26a_map_val_eq_iff p (τ f)).2 h]
      exact Multiset.mem_map_of_mem _ (mem_univ_val j)
    obtain ⟨x, hx⟩ := card_pos.mp (p.parts_pos hm)
    exact ⟨x, by simpa using hx⟩
  have hfib : ∀ s ∈ T, (#{f : Fin n → Fin k | τ f = s} : ℚ) =
      n.factorial / (Pl : ℚ) := by
    intro s hs
    have hsm : univ.val.map (fun j => (s j : ℕ)) = p.parts := by
      rw [r26a_map_val_eq_iff]; simpa [T] using hs
    have hsum : ∑ j, (s j : ℕ) = n := by
      rw [sum_eq_multiset_sum, hsm, p.parts_sum]
    have hprod : ∏ j, (s j : ℕ).factorial = Pl := by
      rw [prod_eq_multiset_prod, hPl, ← hsm, Multiset.map_map]; rfl
    have hb := q26a_card_boxPlacements n (fun j => (s j : ℕ)) hsum
    have hspec := Nat.multinomial_spec univ (fun j => (s j : ℕ))
    rw [hprod, hsum] at hspec
    have he : (univ.filter fun f : Fin n → Fin k => τ f = s) =
        univ.filter fun f : Fin n → Fin k => ∀ j, #{x | f x = j} = (s j : ℕ) := by
      refine filter_congr fun f _ => ?_
      simp only [τ, funext_iff, Fin.ext_iff]
    rw [he, hb, eq_div_iff (by positivity), mul_comm]
    exact_mod_cast hspec
  rw [hA, card_eq_sum_card_fiberwise (f := τ) (t := T) (fun f hf => by simpa using hf)] at h1
  have h2 :
      (∑ s ∈ T, #((univ.filter fun f : Fin n → Fin k => τ f ∈ T).filter fun f => τ f = s) : ℚ) =
      #T * (n.factorial / (Pl : ℚ)) := by
    rw [← nsmul_eq_mul, ← sum_const]
    refine sum_congr rfl fun s hs => ?_
    rw [← hfib s hs, filter_filter]
    congr 2
    refine filter_congr fun f _ => ⟨fun h => h.2, fun h => ⟨h ▸ hs, h⟩⟩
  -- step 3: count the fibre-size patterns
  have hcsum : ∑ i, c i = k := by
    rw [Fin.sum_univ_eq_sum_range (fun j => p.parts.count j), sum_count_parts]
  have hT := q26a_card_boxPlacements k c hcsum
  have hTspec := Nat.multinomial_spec univ c
  rw [hcsum, ← hT] at hTspec
  -- conclude
  have hD : ∏ j ∈ range (n + 1),
      ((j.factorial : ℚ) ^ p.parts.count j * (p.parts.count j).factorial) =
      Pl * ∏ i, ((c i).factorial : ℚ) := by
    rw [prod_mul_distrib, Fin.prod_univ_eq_prod_range (fun j => ((p.parts.count j).factorial : ℚ))]
    congr 1
    rw [hPl, Nat.cast_multiset_prod, Multiset.map_map, Finset.prod_multiset_map_count]
    symm
    apply prod_subset (c26a_toFinset_parts_subset p)
    intro j _ hj; rw [Multiset.mem_toFinset] at hj; simp [Multiset.count_eq_zero_of_notMem hj]
  have h1' : (k.factorial : ℚ) * #{P : Finpartition (univ : Finset (Fin n)) |
      P.parts.val.map Finset.card = p.parts} = #T * (n.factorial / (Pl : ℚ)) := by
    rw [← h2]; exact_mod_cast h1.symm
  have hTq : (∏ i, ((c i).factorial : ℚ)) * #T = k.factorial := by exact_mod_cast hTspec
  have hC : (0 : ℚ) < ∏ i, ((c i).factorial : ℚ) := prod_pos fun i _ => by positivity
  have hTpos : (0 : ℚ) < #T := by rw [hT]; exact_mod_cast Nat.multinomial_pos _ _
  rw [hD, eq_div_iff (by positivity)]
  rw [← hTq] at h1'
  have h3 := congrArg (· * (Pl : ℚ)) h1'
  rw [mul_assoc (#T : ℚ), div_mul_cancel₀ _ hP.ne'] at h3
  have h4 : (#T : ℚ) * (#{P : Finpartition (univ : Finset (Fin n)) |
      P.parts.val.map Finset.card = p.parts} * (Pl *
        ∏ i, ((c i).factorial : ℚ))) = #T * n.factorial := by
    rw [← h3]; ring
  exact mul_left_cancel₀ hTpos.ne' h4

/-! ### Recurrence relation (§26.4(iii)) -/

/-- DLMF 26.4.10: `(n₁ + ⋯ + n_m; n₁, …, n_m) = ∑_{k=1}^{m} (n₁ + ⋯ + n_m - 1; n₁, …,
n_k - 1, …, n_m)`, all `nᵢ ≥ 1`, `m ≥ 1` (implicit in DLMF; for `m = 0` it fails). -/
@[dlmf 26.4.E10]
theorem multinomial_eq_sum_update {m : ℕ} (hm : 1 ≤ m) (n : Fin m → ℕ) (hn : ∀ i, 1 ≤ n i) :
    Nat.multinomial univ n =
      ∑ k : Fin m, Nat.multinomial univ (Function.update n k (n k - 1)) := by
  set N := ∑ i, n i with hN
  set P := ∏ i, (n i).factorial with hPdef
  have hN1 : 1 ≤ N := le_trans (hn ⟨0, by omega⟩) (single_le_sum (by simp) (mem_univ _))
  have key : ∀ k : Fin m,
      P * Nat.multinomial univ (Function.update n k (n k - 1)) = (N - 1).factorial * n k := by
    intro k
    have hS : ∑ i, Function.update n k (n k - 1) i = N - 1 := by
      rw [Finset.sum_update_of_mem (mem_univ k), hN,
        Finset.sum_eq_add_sum_sdiff_singleton_of_mem (mem_univ k) n]
      have := hn k; omega
    have hP : (∏ i, (Function.update n k (n k - 1) i).factorial) * n k = P := by
      have e : ∀ i, (Function.update n k (n k - 1) i).factorial =
          Function.update (fun i => (n i).factorial) k (n k - 1).factorial i := fun i =>
        Function.apply_update (fun _ => Nat.factorial) n k (n k - 1) i
      simp_rw [e]
      rw [Finset.prod_update_of_mem (mem_univ k), hPdef,
        Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (mem_univ k) (fun i => (n i).factorial),
        ← Nat.mul_factorial_pred (by have := hn k; omega : n k ≠ 0)]
      ring
    have hspec := Nat.multinomial_spec (univ : Finset (Fin m)) (Function.update n k (n k - 1))
    rw [hS] at hspec
    rw [← hP, ← hspec]; ring
  have hsum : P * ∑ k : Fin m, Nat.multinomial univ (Function.update n k (n k - 1)) =
      N.factorial := by
    rw [mul_sum, sum_congr rfl fun k _ => key k, ← mul_sum, ← hN,
      mul_comm, Nat.mul_factorial_pred (by omega)]
  have hP0 : 0 < P := by positivity
  apply Nat.eq_of_mul_eq_mul_left hP0
  rw [hsum, hPdef, Nat.multinomial_spec]

end DLMF.Combinatorics
