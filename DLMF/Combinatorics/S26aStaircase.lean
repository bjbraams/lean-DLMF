/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Combinatorics.RestrictedPartitions

/-!
# The staircase bijection for partitions with parts differing by at least `k`

A partition of `n` into exactly `m` parts, any two of which differ by at least `k` and all of
which are at least `s ≥ 1`, is a decreasing list `λ₁ > ⋯ > λ_m`; subtracting the staircase
`k (m - i) + s` from `λ_i` gives a partition of `n - (k C(m,2) + s m)` into at most `m` parts,
and conversely (`s26a_card_staircase`). Summed over `m` (`s26a_card_diff_min_eq_sum`) this is
DLMF (26.10.10) (`s = 1`) and the counting behind the Rogers–Ramanujan identities.
-/

@[expose] public section

open Finset

namespace DLMF.Combinatorics

/-- Subtracting the staircase `k (len - 1 - i) + s` from a list. -/
def s26a_sub (k s : ℕ) : List ℕ → List ℕ
  | [] => []
  | a :: t => (a - (k * t.length + s)) :: s26a_sub k s t

/-- Adding the staircase `k (len - 1 - i) + s` to a list. -/
def s26a_add (k s : ℕ) : List ℕ → List ℕ
  | [] => []
  | a :: t => (a + (k * t.length + s)) :: s26a_add k s t

/-- Every entry dominates the staircase. -/
def S26aGood (k s : ℕ) : List ℕ → Prop
  | [] => True
  | a :: t => k * t.length + s ≤ a ∧ S26aGood k s t

/-- Identity under the stated parameter and domain assumptions: `(s26a_sub k s l).length =
l.length`. -/
@[simp] lemma s26a_length_sub (k s : ℕ) (l : List ℕ) : (s26a_sub k s l).length = l.length := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [s26a_sub, ih]

/-- Identity under the stated parameter and domain assumptions: `(s26a_add k s l).length =
l.length`. -/
@[simp] lemma s26a_length_add (k s : ℕ) (l : List ℕ) : (s26a_add k s l).length = l.length := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [s26a_add, ih]

/-- Identity under the stated parameter and domain assumptions: `s26a_sub k s (s26a_add k s l) =
l`. -/
lemma s26a_sub_add (k s : ℕ) (l : List ℕ) : s26a_sub k s (s26a_add k s l) = l := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [s26a_sub, s26a_add, ih]

/-- Identity under the stated parameter and domain assumptions: `s26a_add k s (s26a_sub k s l) =
l`. -/
lemma s26a_add_sub (k s : ℕ) {l : List ℕ} (h : S26aGood k s l) :
    s26a_add k s (s26a_sub k s l) = l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [S26aGood] at h
    simp only [s26a_sub, s26a_add, s26a_length_sub, ih h.2, List.cons.injEq, and_true]
    omega

/-- Identity under the stated parameter and domain assumptions: `(s26a_add k s l).sum = l.sum + (k
* l.length.choose 2 + s * l.length)`. -/
lemma s26a_sum_add (k s : ℕ) (l : List ℕ) :
    (s26a_add k s l).sum = l.sum + (k * l.length.choose 2 + s * l.length) := by
  induction l with
  | nil => simp [s26a_add]
  | cons a t ih =>
    simp only [s26a_add, List.sum_cons, ih, List.length_cons, Nat.choose_succ_succ',
      Nat.choose_one_right]
    ring

/-- Identity under the stated parameter and domain assumptions: `(s26a_sub k s l).sum + (k *
l.length.choose 2 + s * l.length) = l.sum`. -/
lemma s26a_sum_sub (k s : ℕ) {l : List ℕ} (h : S26aGood k s l) :
    (s26a_sub k s l).sum + (k * l.length.choose 2 + s * l.length) = l.sum := by
  have := s26a_sum_add k s (s26a_sub k s l)
  rw [s26a_add_sub k s h, s26a_length_sub] at this
  exact this.symm

/-- The stated relation follows from the given hypotheses: `S26aGood k s (s26a_add k s l)`. -/
lemma s26a_good_add (k s : ℕ) (l : List ℕ) : S26aGood k s (s26a_add k s l) := by
  induction l with
  | nil => trivial
  | cons a t ih => exact ⟨by simp, ih⟩

/-- The stated relation follows from the given hypotheses: `S26aGood k s l`. -/
lemma s26a_good_of_chain (k s : ℕ) {l : List ℕ} (hc : l.IsChain (fun a b => b + k ≤ a))
    (hs : ∀ x ∈ l, s ≤ x) : S26aGood k s l := by
  induction l with
  | nil => trivial
  | cons a t ih =>
    refine ⟨?_, ih hc.tail fun x hx => hs x (List.mem_cons_of_mem a hx)⟩
    rcases t with _ | ⟨b, t'⟩
    · simpa using hs a (by simp)
    · have h1 := (ih hc.tail fun x hx => hs x (List.mem_cons_of_mem a hx)).1
      have h2 : b + k ≤ a := (List.isChain_cons_cons.mp hc).1
      simp only [List.length_cons]
      nlinarith

/-- The selected subsets form a chain under reverse inclusion. -/
lemma s26a_chain_sub (k s : ℕ) {l : List ℕ} (hc : l.IsChain (fun a b => b + k ≤ a)) :
    (s26a_sub k s l).IsChain (fun a b => b ≤ a) := by
  induction l with
  | nil => exact List.IsChain.nil
  | cons a t ih =>
    rcases t with _ | ⟨b, t'⟩
    · simp [s26a_sub]
    · have h2 : b + k ≤ a := (List.isChain_cons_cons.mp hc).1
      simp only [s26a_sub, List.length_cons] at ih ⊢
      refine List.IsChain.cons_cons ?_ (ih hc.tail)
      have : k * (t'.length + 1) = k * t'.length + k := by ring
      omega

/-- Estimate under the stated parameter and domain assumptions: `(s26a_add k s l).IsChain (fun a b
=> b + k ≤ a)`. -/
lemma s26a_chain_add (k s : ℕ) {l : List ℕ} (hc : l.IsChain (fun a b => b ≤ a)) :
    (s26a_add k s l).IsChain (fun a b => b + k ≤ a) := by
  induction l with
  | nil => exact List.IsChain.nil
  | cons a t ih =>
    rcases t with _ | ⟨b, t'⟩
    · simp [s26a_add]
    · have h2 : b ≤ a := (List.isChain_cons_cons.mp hc).1
      simp only [s26a_add, List.length_cons] at ih ⊢
      refine List.IsChain.cons_cons ?_ (ih hc.tail)
      have : k * (t'.length + 1) = k * t'.length + k := by ring
      omega

/-- Estimate under the stated parameter and domain assumptions: `l.Pairwise (fun a b => b + k ≤
a)`. -/
lemma s26a_pairwise_of_pda (k : ℕ) {l : List ℕ} (hsort : l.Pairwise (· ≥ ·))
    (h : ∀ a ∈ l, ∀ b ∈ l.erase a, a + k ≤ b ∨ b + k ≤ a) :
    l.Pairwise (fun a b => b + k ≤ a) := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons c t ih =>
    rw [List.pairwise_cons] at hsort ⊢
    refine ⟨fun b hb => ?_, ih hsort.2 fun a ha b hb => ?_⟩
    · have h1 := h c (by simp) b (by simpa using hb)
      have h2 := hsort.1 b hb
      omega
    · exact h a (List.mem_cons_of_mem c ha) b
        (((List.sublist_cons_self c t).erase a).subset hb)

/-- Estimate under the stated parameter and domain assumptions: `∀ a ∈ l, ∀ b ∈ l.erase a, a + k ≤
b ∨ b + k ≤ a`. -/
lemma s26a_pda_of_pairwise (k : ℕ) {l : List ℕ} (h : l.Pairwise (fun a b => b + k ≤ a)) :
    ∀ a ∈ l, ∀ b ∈ l.erase a, a + k ≤ b ∨ b + k ≤ a := by
  induction l with
  | nil => simp
  | cons c t ih =>
    rw [List.pairwise_cons] at h
    intro a ha b hb
    by_cases hac : c = a
    · subst hac
      rw [List.erase_cons_head] at hb
      exact Or.inr (h.1 b hb)
    · rw [List.erase_cons_tail (by simpa using hac)] at hb
      have ha' : a ∈ t := by
        rcases List.mem_cons.mp ha with h' | h'
        · exact absurd h'.symm hac
        · exact h'
      rcases List.mem_cons.mp hb with rfl | hb
      · exact Or.inl (h.1 a ha')
      · exact ih h.2 a ha' b hb

/-- Estimate under the stated parameter and domain assumptions: `L.filter (fun x => 0 < x) ++
List.replicate (L.length - (L.filter (fun x => 0 < x)).length) 0 = L`. -/
lemma s26a_filter_pad {L : List ℕ} (hL : L.Pairwise (· ≥ ·)) :
    L.filter (fun x => 0 < x) ++
      List.replicate (L.length - (L.filter (fun x => 0 < x)).length) 0 = L := by
  induction L with
  | nil => simp
  | cons a t ih =>
    rw [List.pairwise_cons] at hL
    by_cases ha : 0 < a
    · rw [List.filter_cons_of_pos (by simpa using ha)]
      simp only [List.length_cons, Nat.add_sub_add_right, List.cons_append, ih hL.2]
    · have h0 : ∀ b ∈ a :: t, b = 0 := by
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · omega
        · have := hL.1 b hb; omega
      have hf : (a :: t).filter (fun x => 0 < x) = [] := by
        rw [List.filter_eq_nil_iff]; intro b hb; simp [h0 b hb]
      rw [hf, List.nil_append, List.length_nil, Nat.sub_zero]
      exact (List.eq_replicate_iff.mpr ⟨rfl, h0⟩).symm

/-- Estimate under the stated parameter and domain assumptions: `(L.filter (fun x => 0 < x)).sum =
L.sum`. -/
lemma s26a_sum_filter_pos (L : List ℕ) : (L.filter (fun x => 0 < x)).sum = L.sum := by
  induction L with
  | nil => rfl
  | cons a t ih =>
    by_cases ha : 0 < a
    · rw [List.filter_cons_of_pos (by simpa using ha)]; simp [ih]
    · rw [List.filter_cons_of_neg (by simpa using ha)]; simp [ih]; omega

/-- The list of parts of a partition in decreasing order. -/
def s26a_sortDesc {n : ℕ} (p : n.Partition) : List ℕ := p.parts.sort (· ≥ ·)

/-- The stated relation follows from the given hypotheses: `(s26a_sortDesc p).Pairwise (· ≥ ·)`. -/
lemma s26a_sortDesc_pairwise {n : ℕ} (p : n.Partition) : (s26a_sortDesc p).Pairwise (· ≥ ·) :=
  Multiset.pairwise_sort _ _

/-- Identity under the stated parameter and domain assumptions: `(↑(s26a_sortDesc p) : Multiset ℕ)
= p.parts`. -/
lemma s26a_sortDesc_coe {n : ℕ} (p : n.Partition) : (↑(s26a_sortDesc p) : Multiset ℕ) = p.parts :=
  Multiset.sort_eq _ _

/-- Identity under the stated parameter and domain assumptions: `(↑L : Multiset ℕ).sort (· ≥ ·) =
L`. -/
lemma s26a_sort_coe_of_pairwise {L : List ℕ} (hL : L.Pairwise (· ≥ ·)) :
    (↑L : Multiset ℕ).sort (· ≥ ·) = L := by
  rw [Multiset.coe_sort]; exact List.mergeSort_eq_self _ hL

/-- Estimate under the stated parameter and domain assumptions: `l.Pairwise (fun a b => b + k ≤
a)`. -/
lemma s26a_pairwise_of_chain_gap (k : ℕ) {l : List ℕ}
    (h : l.IsChain (fun a b => b + k ≤ a)) : l.Pairwise (fun a b => b + k ≤ a) := by
  have : Trans (fun a b : ℕ => b + k ≤ a) (fun a b : ℕ => b + k ≤ a)
      (fun a b : ℕ => b + k ≤ a) := ⟨fun h1 h2 => by omega⟩
  exact h.pairwise

/-- Estimate under the stated parameter and domain assumptions: `s ≤ x`. -/
lemma s26a_le_of_mem_add (k s : ℕ) {L : List ℕ} {x : ℕ} (hx : x ∈ s26a_add k s L) : s ≤ x := by
  induction L with
  | nil => simp [s26a_add] at hx
  | cons a t ih =>
    simp only [s26a_add, List.mem_cons] at hx
    rcases hx with rfl | hx
    · omega
    · exact ih hx

/-- The decreasing list of parts of a partition with parts differing by at least `k`, all
at least `s`, and `m` parts. -/
lemma s26a_src_facts (k s : ℕ) {m n : ℕ} (p : n.Partition)
    (hd : ∀ a ∈ p.parts, ∀ b ∈ p.parts.erase a, a + k ≤ b ∨ b + k ≤ a)
    (hmin : ∀ i ∈ p.parts, s ≤ i) (hc : p.parts.card = m) :
    S26aGood k s (s26a_sortDesc p) ∧ (s26a_sortDesc p).length = m ∧
      (s26a_sub k s (s26a_sortDesc p)).sum + (k * m.choose 2 + s * m) = n ∧
      (s26a_sub k s (s26a_sortDesc p)).Pairwise (· ≥ ·) := by
  set l := s26a_sortDesc p
  have hcoe := s26a_sortDesc_coe p
  have hP : l.Pairwise (fun a b => b + k ≤ a) := by
    refine s26a_pairwise_of_pda k (s26a_sortDesc_pairwise p) fun a ha b hb => ?_
    have ha' : a ∈ p.parts := by rw [← hcoe]; exact Multiset.mem_coe.mpr ha
    have hb' : b ∈ p.parts.erase a := by rw [← hcoe, Multiset.coe_erase]; exact hb
    exact hd a ha' b hb'
  have hG : S26aGood k s l := s26a_good_of_chain k s hP.isChain fun x hx => hmin x (by
    rw [← hcoe]; exact Multiset.mem_coe.mpr hx)
  have hlen : l.length = m := by rw [← hc, ← hcoe, Multiset.coe_card]
  have hsum := s26a_sum_sub k s hG
  have hps : l.sum = n := by
    rw [← p.parts_sum, ← hcoe, Multiset.sum_coe]
  refine ⟨hG, hlen, by rw [hlen] at hsum; omega, ?_⟩
  exact (s26a_chain_sub k s hP.isChain).pairwise

/-- The staircase bijection: partitions of `n` into exactly `m` parts, any two differing by at
least `k`, all parts at least `s ≥ 1`, correspond to partitions of `n - (k C(m,2) + s m)` into at
most `m` parts. -/
lemma s26a_card_staircase (k s m : ℕ) (hs : 1 ≤ s) {n N : ℕ}
    (hN : N + (k * m.choose 2 + s * m) = n) :
    #{p : n.Partition | (∀ a ∈ p.parts, ∀ b ∈ p.parts.erase a, a + k ≤ b ∨ b + k ≤ a) ∧
        (∀ i ∈ p.parts, s ≤ i) ∧ p.parts.card = m} =
      #{q : N.Partition | q.parts.card ≤ m} := by
  have hsrc : ∀ p : n.Partition, (∀ a ∈ p.parts, ∀ b ∈ p.parts.erase a, a + k ≤ b ∨ b + k ≤ a) →
      (∀ i ∈ p.parts, s ≤ i) → p.parts.card = m →
      S26aGood k s (s26a_sortDesc p) ∧ (s26a_sortDesc p).length = m ∧
        (s26a_sub k s (s26a_sortDesc p)).sum = N ∧
        (s26a_sub k s (s26a_sortDesc p)).Pairwise (· ≥ ·) := by
    intro p hd hmin hc
    obtain ⟨hG, hlen, hsum, hpw⟩ := s26a_src_facts k s p hd hmin hc
    exact ⟨hG, hlen, by omega, hpw⟩
  -- facts about the padded list of a target partition
  have htgt : ∀ q : N.Partition, q.parts.card ≤ m →
      (s26a_sortDesc q ++ List.replicate (m - q.parts.card) 0).length = m ∧
      (s26a_sortDesc q ++ List.replicate (m - q.parts.card) 0).sum = N ∧
      (s26a_sortDesc q ++ List.replicate (m - q.parts.card) 0).Pairwise (· ≥ ·) := by
    intro q hq
    have hcoe := s26a_sortDesc_coe q
    refine ⟨?_, ?_, ?_⟩
    · have hl : (s26a_sortDesc q).length = q.parts.card := by rw [← Multiset.coe_card, hcoe]
      rw [List.length_append, List.length_replicate, hl]; omega
    · rw [List.sum_append, List.sum_replicate, smul_zero, add_zero, ← Multiset.sum_coe, hcoe,
        q.parts_sum]
    · rw [List.pairwise_append]
      refine ⟨s26a_sortDesc_pairwise q, ?_, fun a _ b hb => ?_⟩
      · exact List.pairwise_replicate.mpr (Or.inr le_rfl)
      · rw [(List.mem_replicate.mp hb).2]; exact Nat.zero_le a
  have hpad_add : ∀ L : List ℕ, L.Pairwise (· ≥ ·) →
      (s26a_add k s L).Pairwise (fun a b => b + k ≤ a) := fun L hL =>
    s26a_pairwise_of_chain_gap k (s26a_chain_add k s hL.isChain)
  refine Finset.card_bij' (fun p hp => ⟨↑((s26a_sub k s (s26a_sortDesc p)).filter (0 < ·)),
      fun {i} hi => by simpa using (List.mem_filter.mp (Multiset.mem_coe.mp hi)).2, by
        simp only [mem_filter, mem_univ, true_and] at hp
        obtain ⟨-, -, hsum, -⟩ := hsrc p hp.1 hp.2.1 hp.2.2
        rw [Multiset.sum_coe, s26a_sum_filter_pos, hsum]⟩)
    (fun q hq => ⟨↑(s26a_add k s (s26a_sortDesc q ++ List.replicate (m - q.parts.card) 0)),
      fun {i} hi => by have := s26a_le_of_mem_add k s (Multiset.mem_coe.mp hi); omega, by
        simp only [mem_filter, mem_univ, true_and] at hq
        obtain ⟨hlen, hsum, -⟩ := htgt q hq
        rw [Multiset.sum_coe, s26a_sum_add, hlen, hsum, hN]⟩) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [mem_filter, mem_univ, true_and] at hp ⊢
    obtain ⟨-, hlen, -, -⟩ := hsrc p hp.1 hp.2.1 hp.2.2
    rw [Multiset.coe_card]
    exact (List.length_filter_le _ _).trans (by rw [s26a_length_sub, hlen])
  · intro q hq
    simp only [mem_filter, mem_univ, true_and] at hq ⊢
    obtain ⟨hlen, -, hpw⟩ := htgt q hq
    refine ⟨fun a ha b hb => ?_, fun i hi => s26a_le_of_mem_add k s (Multiset.mem_coe.mp hi), ?_⟩
    · rw [Multiset.coe_erase] at hb
      exact s26a_pda_of_pairwise k (hpad_add _ hpw) a (Multiset.mem_coe.mp ha) b
        (Multiset.mem_coe.mp hb)
    · rw [Multiset.coe_card, s26a_length_add, hlen]
  · intro p hp
    simp only [mem_filter, mem_univ, true_and] at hp
    obtain ⟨hG, hlen, -, hpw⟩ := hsrc p hp.1 hp.2.1 hp.2.2
    apply Nat.Partition.ext
    simp only
    rw [show s26a_sortDesc (⟨↑((s26a_sub k s (s26a_sortDesc p)).filter (0 < ·)), _, _⟩ :
        N.Partition) = (s26a_sub k s (s26a_sortDesc p)).filter (0 < ·) from
      s26a_sort_coe_of_pairwise (hpw.filter _), Multiset.coe_card]
    rw [show m = (s26a_sub k s (s26a_sortDesc p)).length by rw [s26a_length_sub, hlen]]
    rw [s26a_filter_pad hpw, s26a_add_sub k s hG, s26a_sortDesc_coe]
  · intro q hq
    simp only [mem_filter, mem_univ, true_and] at hq
    obtain ⟨-, -, hpw⟩ := htgt q hq
    apply Nat.Partition.ext
    simp only
    rw [show s26a_sortDesc (⟨↑(s26a_add k s (s26a_sortDesc q ++
        List.replicate (m - q.parts.card) 0)), _, _⟩ : n.Partition) =
        s26a_add k s (s26a_sortDesc q ++ List.replicate (m - q.parts.card) 0) from
      s26a_sort_coe_of_pairwise ((hpad_add _ hpw).imp fun h => by omega),
      s26a_sub_add, List.filter_append]
    rw [List.filter_eq_self.mpr fun a ha => by
        have := q.parts_pos (by rw [← s26a_sortDesc_coe q]; exact Multiset.mem_coe.mpr ha)
        simpa using this,
      List.filter_eq_nil_iff.mpr fun a ha => by simp [(List.mem_replicate.mp ha).2],
      List.append_nil, s26a_sortDesc_coe]

/-- If `n < k C(m,2) + s m` there is no such partition. -/
lemma s26a_card_staircase_zero (k s m : ℕ) {n : ℕ} (h : n < k * m.choose 2 + s * m) :
    #{p : n.Partition | (∀ a ∈ p.parts, ∀ b ∈ p.parts.erase a, a + k ≤ b ∨ b + k ≤ a) ∧
        (∀ i ∈ p.parts, s ≤ i) ∧ p.parts.card = m} = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro p - ⟨hd, hmin, hc⟩
  have := (s26a_src_facts k s p hd hmin hc).2.2.1
  omega

/-- Partitions of `n` with parts differing by at least `k`, all at least `s ≥ 1`:
`∑_m p_m(n - k C(m,2) - s m)`. -/
theorem s26a_card_diff_min_eq_sum (k s n : ℕ) (hs : 1 ≤ s) :
    #{p : n.Partition | (∀ a ∈ p.parts, ∀ b ∈ p.parts.erase a, a + k ≤ b ∨ b + k ≤ a) ∧
        (∀ i ∈ p.parts, s ≤ i)} =
      ∑ m ∈ range (n + 1) with k * m.choose 2 + s * m ≤ n,
        partitionCountAtMostParts m (n - (k * m.choose 2 + s * m)) := by
  rw [card_eq_sum_card_fiberwise (f := fun p : n.Partition => p.parts.card) (t := range (n + 1))
    (fun p _ => by simpa [Nat.lt_succ_iff] using c26b_card_parts_le p), sum_filter]
  refine sum_congr rfl fun m _ => ?_
  rw [filter_filter]
  split_ifs with h
  · simp only [and_assoc]
    rw [s26a_card_staircase k s m hs (N := n - (k * m.choose 2 + s * m)) (by omega)]
    rfl
  · simp only [and_assoc]
    exact s26a_card_staircase_zero k s m (by omega)

end DLMF.Combinatorics
