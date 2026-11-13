/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Combinatorics.MultisetPermutations.Inversions
import DLMF.QSeries.QBinomial

/-!
# The major-index enumerator for multiset permutations

Appending a boundary letter gives a refined major-index enumerator. Its last-letter
recurrence, multiplied by the q-factorials of the multiplicities, telescopes to a total
q-factorial shifted by the number of letters above the boundary. A boundary above the
alphabet then gives MacMahon's formula, DLMF 26.16.3. Cancellation away from the unit
circle and continuity cover every complex `q`, including roots of unity.

The proof reuses Mathlib's `Finset.prod_one_add_ordered`, finite-list APIs and reversal
permutation of `Fin`, together with the content and q-factorial bridges in
`MultisetWords`.

## Main results

* `MultisetWords.boundaryEnumerator_mul_factorialProduct`: the refined identity.
* `MultisetWords.majorIndexEnumerator_content`: MacMahon's formula for list words.
* `MultisetWords.sum_pow_wordMajorIndex`: the canonical indexed-word form.
-/

public noncomputable section

open Finset DLMF.QSeries

namespace DLMF.Combinatorics.MultisetWords

/-- The major index of a list, using the canonical indexed-word statistic. -/
@[expose] def listMajorIndex (l : List ℕ) : ℕ := wordMajorIndex l.get

/-- The empty list has major index zero. -/
lemma listMajorIndex_nil : listMajorIndex [] = 0 := by
  simp [listMajorIndex, wordMajorIndex, wordDescentSet]

/-- A singleton list has no descent. -/
lemma listMajorIndex_singleton (j : ℕ) : listMajorIndex [j] = 0 := by
  simp [listMajorIndex, wordMajorIndex, wordDescentSet]

/-- Appending a letter adds the new last position exactly when it is a descent. -/
lemma listMajorIndex_snoc_snoc (l : List ℕ) (i j : ℕ) :
    listMajorIndex (l ++ [i] ++ [j]) = listMajorIndex (l ++ [i]) +
      if j < i then l.length + 1 else 0 := by
  have hmem (a : List ℕ) (k : ℕ) : k ∈ wordDescentSet a.get ↔
      ∃ h : k + 1 < a.length, a[k + 1] < a[k] := by
    simp only [wordDescentSet, mem_filter, mem_range, List.get_eq_getElem]
    exact ⟨fun h => h.2, fun h => ⟨by obtain ⟨h, _⟩ := h; omega, h⟩⟩
  have hi : (l ++ [i] ++ [j])[l.length] = i := by simp
  have hj : (l ++ [i] ++ [j])[l.length + 1] = j := by simp
  have hset : wordDescentSet (l ++ [i] ++ [j]).get =
      wordDescentSet (l ++ [i]).get ∪ if j < i then {l.length} else ∅ := by
    ext k
    rw [mem_union, hmem, hmem]
    simp only [List.length_append, List.length_singleton]
    by_cases hji : j < i
    · rw [ite_eq_left hji, mem_singleton]
      constructor
      · rintro ⟨hk, hlt⟩
        by_cases hki : k < l.length
        · left
          refine ⟨by omega, ?_⟩
          simpa only [List.getElem_append_left (by simp; omega : k + 1 < (l ++ [i]).length),
            List.getElem_append_left (by simp; omega : k < (l ++ [i]).length)] using hlt
        · right
          omega
      · rintro (⟨hk, hlt⟩ | rfl)
        · refine ⟨by omega, ?_⟩
          simpa only [List.getElem_append_left (by simp; omega : k + 1 < (l ++ [i]).length),
            List.getElem_append_left (by simp; omega : k < (l ++ [i]).length)] using hlt
        · exact ⟨by omega, by rw [hi, hj]; exact hji⟩
    · rw [ite_eq_right hji]
      simp only [Finset.notMem_empty, or_false]
      constructor
      · rintro ⟨hk, hlt⟩
        have hki : k < l.length := by
          by_contra h
          have : k = l.length := by omega
          subst k
          rw [hi, hj] at hlt
          exact hji hlt
        refine ⟨by omega, ?_⟩
        simpa only [List.getElem_append_left (by simp; omega : k + 1 < (l ++ [i]).length),
          List.getElem_append_left (by simp; omega : k < (l ++ [i]).length)] using hlt
      · rintro ⟨hk, hlt⟩
        refine ⟨by omega, ?_⟩
        simpa only [List.getElem_append_left (by simp; omega : k + 1 < (l ++ [i]).length),
          List.getElem_append_left (by simp; omega : k < (l ++ [i]).length)] using hlt
  rw [listMajorIndex, wordMajorIndex, hset, sum_union]
  · split_ifs with h
    · simp [listMajorIndex, wordMajorIndex]
    · simp [listMajorIndex, wordMajorIndex]
  · rw [disjoint_iff_ne]
    intro a ha b hb hab
    have ha' := (mem_filter.mp ha).2
    split_ifs at hb with h
    · simp only [mem_singleton] at hb
      subst b
      subst a
      obtain ⟨h', _⟩ := ha'
      simp only [List.length_append, List.length_singleton] at h'
      omega
    · simp at hb

/-- Nonempty words split disjointly by their last letter. -/
lemma words_eq_snoc_biUnion {m : ℕ} {s : Multiset (Fin m)} (hs : s ≠ 0) :
    words s = s.toFinset.biUnion fun j =>
      (words (s.erase j)).map ⟨fun l => l ++ [j], List.append_left_injective [j]⟩ := by
  ext l
  simp only [mem_words, mem_biUnion, Multiset.mem_toFinset, mem_map,
    Function.Embedding.coeFn_mk]
  induction l using List.reverseRecOn with
  | nil => simp [Ne.symm hs]
  | append_singleton l j _ =>
    constructor
    · intro h
      have hj : j ∈ s := by rw [← h]; simp
      refine ⟨j, hj, l, ?_, rfl⟩
      rw [← h]
      have he : (l ++ [j] : Multiset (Fin m)) = j ::ₘ (l : Multiset (Fin m)) := by
        exact Quot.sound List.perm_append_comm
      rw [he, Multiset.erase_cons_head]
    · rintro ⟨j', hj, l', hl', he⟩
      have hlen := congrArg List.length he
      simp only [List.length_append, List.length_singleton] at hlen
      obtain ⟨rfl, hj'⟩ := List.append_inj he (by omega)
      have : j' = j := by simpa using hj'
      subst j'
      rw [← Multiset.coe_add, hl']
      rw [Multiset.add_comm, Multiset.coe_singleton, Multiset.singleton_add,
        Multiset.cons_erase hj]

/-- The number of letters strictly larger than a given natural-number boundary. -/
@[expose] def greaterCount {m : ℕ} (s : Multiset (Fin m)) (j : ℕ) : ℕ :=
  (s.filter fun i => j < i.val).card

/-- The larger-letter count is the sum of the corresponding multiplicities. -/
lemma greaterCount_eq_sum {m : ℕ} (s : Multiset (Fin m)) (j : ℕ) :
    greaterCount s j = ∑ i : Fin m with j < i.val, s.count i := by
  rw [greaterCount, ← Multiset.sum_count_eq_card (s := univ)
    (m := s.filter (fun i => j < i.val)) (fun _ _ => mem_univ _)]
  simp only [Multiset.count_filter, sum_filter]

/-- The descending geometric blocks telescope to the total geometric factor. -/
lemma sum_pow_greaterCount_mul_one_sub_pow_count {m : ℕ} (q : ℂ) (s : Multiset (Fin m)) :
    ∑ j ∈ s.toFinset, q ^ greaterCount s j.val * (1 - q ^ s.count j) = 1 - q ^ s.card := by
  have h := prod_one_add_ordered (univ : Finset (Fin m))
    (fun j => q ^ s.count j.rev - 1)
  have he (j : Fin m) : 1 + (q ^ s.count j.rev - 1) = q ^ s.count j.rev := by ring
  simp_rw [he, prod_pow_eq_pow_sum] at h
  have hcount : (∑ i : Fin m, s.count i.rev) = s.card := by
    have hrev := Equiv.sum_comp Fin.revPerm (fun i => s.count i)
    simp only [Fin.revPerm_apply] at hrev
    rw [hrev, Multiset.sum_count_eq_card (fun _ _ => mem_univ _)]
  rw [hcount] at h
  have hG (j : Fin m) : (∑ i : Fin m with i < j, s.count i.rev) =
      greaterCount s j.rev.val := by
    rw [greaterCount_eq_sum, sum_filter, sum_filter]
    apply Fintype.sum_equiv Fin.revPerm
    intro i
    simp only [Fin.revPerm_apply, Fin.rev_lt_rev, Fin.val_fin_lt]
  simp_rw [hG] at h
  have hrev : (∑ j : Fin m, (q ^ s.count j.rev - 1) * q ^ greaterCount s j.rev.val) =
      ∑ j : Fin m, (q ^ s.count j - 1) * q ^ greaterCount s j.val := by
    simpa only [Fin.revPerm_apply] using Equiv.sum_comp Fin.revPerm
      (fun j => (q ^ s.count j - 1) * q ^ greaterCount s j.val)
  rw [hrev] at h
  have hs : (∑ j ∈ s.toFinset, q ^ greaterCount s j.val * (1 - q ^ s.count j)) =
      ∑ j : Fin m, q ^ greaterCount s j.val * (1 - q ^ s.count j) := by
    apply sum_subset (subset_univ _)
    intro j _ hj
    have hc : s.count j = 0 := Multiset.count_eq_zero.mpr (by simpa using hj)
    rw [hc, pow_zero, sub_self, mul_zero]
  rw [hs]
  calc
    _ = -(∑ j : Fin m, (q ^ s.count j - 1) * q ^ greaterCount s j.val) := by
      rw [← sum_neg_distrib]
      apply sum_congr rfl
      intro j _
      ring
    _ = _ := by linear_combination h

/-- The geometric blocks above a boundary telescope to their total factor. -/
lemma sum_pow_greaterCount_filter_mul_one_sub_pow_count {m : ℕ} (q : ℂ)
    (s : Multiset (Fin m)) (j : ℕ) :
    ∑ i ∈ s.toFinset with j < i.val,
      q ^ greaterCount s i.val * (1 - q ^ s.count i) = 1 - q ^ greaterCount s j := by
  have h := sum_pow_greaterCount_mul_one_sub_pow_count q (s.filter fun i => j < i.val)
  rw [Multiset.toFinset_filter] at h
  convert h using 1
  · apply sum_congr rfl
    intro i hi
    obtain ⟨_, hji⟩ := mem_filter.mp hi
    have hG : greaterCount (s.filter fun i => j < i.val) i.val = greaterCount s i.val := by
      simp only [greaterCount, Multiset.filter_filter]
      congr 1
      apply Multiset.filter_congr
      intro a _
      omega
    rw [hG, Multiset.count_filter, ite_eq_left hji]
  · rfl

/-- The last-letter boundary weights shift the telescoping geometric factor. -/
lemma sum_pow_greaterCount_mul_boundary {m : ℕ} (q : ℂ)
    (s : Multiset (Fin m)) (j : ℕ) :
    ∑ i ∈ s.toFinset, q ^ (if j < i.val then s.card else 0) *
      (q ^ greaterCount s i.val * (1 - q ^ s.count i)) =
        q ^ greaterCount s j * (1 - q ^ s.card) := by
  have he : (∑ i ∈ s.toFinset, q ^ (if j < i.val then s.card else 0) *
      (q ^ greaterCount s i.val * (1 - q ^ s.count i))) =
        (∑ i ∈ s.toFinset, q ^ greaterCount s i.val * (1 - q ^ s.count i)) +
          (q ^ s.card - 1) * ∑ i ∈ s.toFinset with j < i.val,
            q ^ greaterCount s i.val * (1 - q ^ s.count i) := by
    rw [mul_sum, sum_filter, ← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    split_ifs <;> ring
  rw [he, sum_pow_greaterCount_mul_one_sub_pow_count,
    sum_pow_greaterCount_filter_mul_one_sub_pow_count]
  ring

/-- The major-index enumerator after appending a fixed boundary letter. -/
@[expose] def boundaryEnumerator {m : ℕ} (q : ℂ) (s : Multiset (Fin m)) (j : ℕ) : ℂ :=
  ∑ l ∈ words s, q ^ listMajorIndex (l.map Fin.val ++ [j])

/-- The empty content followed by one boundary letter contributes one. -/
lemma boundaryEnumerator_zero (q : ℂ) (m j : ℕ) :
    boundaryEnumerator q (0 : Multiset (Fin m)) j = 1 := by
  simp [boundaryEnumerator, words_zero, listMajorIndex_singleton]

/-- The last-letter recurrence for the major-index boundary enumerator. -/
lemma boundaryEnumerator_eq_sum {m : ℕ} (q : ℂ) {s : Multiset (Fin m)} (hs : s ≠ 0)
    (j : ℕ) : boundaryEnumerator q s j = ∑ i ∈ s.toFinset,
      q ^ (if j < i.val then s.card else 0) * boundaryEnumerator q (s.erase i) i.val := by
  rw [boundaryEnumerator, words_eq_snoc_biUnion hs, sum_biUnion]
  · apply sum_congr rfl
    intro i hi
    rw [sum_map, boundaryEnumerator, mul_sum]
    apply sum_congr rfl
    intro l hl
    dsimp only [Function.Embedding.coeFn_mk]
    rw [List.map_append, List.map_singleton, listMajorIndex_snoc_snoc]
    have hcard := congrArg Multiset.card (mem_words.mp hl)
    simp only [Multiset.coe_card, Multiset.card_erase_of_mem (Multiset.mem_toFinset.mp hi)] at hcard
    simp only [Nat.pred_eq_sub_one] at hcard
    have hlen : (l.map Fin.val).length + 1 = s.card := by
      simp only [List.length_map]
      have := Multiset.card_pos.mpr hs
      omega
    rw [hlen, pow_add, mul_comm]
  · intro a _ b _ hab
    simp only [Function.onFun]
    rw [disjoint_left]
    intro l hla hlb
    obtain ⟨la, _, he⟩ := mem_map.mp hla
    obtain ⟨lb, _, he'⟩ := mem_map.mp hlb
    dsimp only [Function.Embedding.coeFn_mk] at he he'
    have h := he.trans he'.symm
    have hlen := congrArg List.length h
    simp only [List.length_append, List.length_singleton] at hlen
    have hlast := (List.append_inj h (by omega)).2
    exact hab (by simpa using hlast)

/-- Erasing a letter preserves the count of letters strictly larger than it. -/
lemma greaterCount_erase_self {m : ℕ} {s : Multiset (Fin m)} {i : Fin m} (hi : i ∈ s) :
    greaterCount (s.erase i) i.val = greaterCount s i.val := by
  conv_rhs => rw [← Multiset.cons_erase hi]
  simp [greaterCount]

/-- The boundary enumerator times the content q-factorials is a shifted total q-factorial. -/
lemma boundaryEnumerator_mul_factorialProduct_of_card (q : ℂ) (m n : ℕ) :
    ∀ s : Multiset (Fin m), s.card = n → ∀ j : ℕ,
      boundaryEnumerator q s j * factorialProduct q s =
        q ^ greaterCount s j * qPochhammer q q n := by
  induction n with
  | zero =>
    intro s hs j
    obtain rfl := Multiset.card_eq_zero.mp hs
    simp [boundaryEnumerator_zero, factorialProduct, greaterCount]
  | succ n ih =>
    intro s hs j
    have hs0 : s ≠ 0 := by intro h; simp [h] at hs
    rw [boundaryEnumerator_eq_sum q hs0, sum_mul]
    calc
      _ = ∑ i ∈ s.toFinset, q ^ (if j < i.val then s.card else 0) *
          (q ^ greaterCount s i.val * (1 - q ^ s.count i)) * qPochhammer q q n := by
        apply sum_congr rfl
        intro i hi
        have hi' := Multiset.mem_toFinset.mp hi
        have hcard : (s.erase i).card = n := by
          simpa only [hs, Nat.pred_succ] using Multiset.card_erase_of_mem hi'
        rw [factorialProduct_erase q hi']
        calc
          _ = q ^ (if j < i.val then s.card else 0) * (1 - q ^ s.count i) *
              (boundaryEnumerator q (s.erase i) i.val * factorialProduct q (s.erase i)) := by ring
          _ = _ := by rw [ih _ hcard, greaterCount_erase_self hi']; ring
      _ = q ^ greaterCount s j * (1 - q ^ s.card) * qPochhammer q q n := by
        rw [← sum_mul, sum_pow_greaterCount_mul_boundary]
      _ = _ := by rw [hs, qPochhammer_succ, pow_succ]; ring

/-- The multiplicative boundary-enumerator formula, valid at every complex `q`. -/
lemma boundaryEnumerator_mul_factorialProduct {m : ℕ} (q : ℂ) (s : Multiset (Fin m)) (j : ℕ) :
    boundaryEnumerator q s j * factorialProduct q s =
      q ^ greaterCount s j * qPochhammer q q s.card :=
  boundaryEnumerator_mul_factorialProduct_of_card q m s.card s rfl j

/-- Appending a letter at least as large as all letters creates no new descent. -/
lemma listMajorIndex_append_of_forall_le (l : List ℕ) (j : ℕ) (hl : ∀ i ∈ l, i ≤ j) :
    listMajorIndex (l ++ [j]) = listMajorIndex l := by
  induction l using List.reverseRecOn with
  | nil => simp [listMajorIndex_nil, listMajorIndex_singleton]
  | append_singleton l i _ =>
    rw [listMajorIndex_snoc_snoc, ite_eq_right (not_lt.mpr (hl i (by simp))), add_zero]

/-- The major-index generating polynomial of words with fixed content. -/
@[expose] def majorIndexEnumerator {m : ℕ} (q : ℂ) (s : Multiset (Fin m)) : ℂ :=
  ∑ l ∈ words s, q ^ listMajorIndex (l.map Fin.val)

/-- A boundary above the alphabet preserves every major index. -/
lemma majorIndexEnumerator_eq_boundaryEnumerator {m : ℕ} (q : ℂ) (s : Multiset (Fin m)) :
    majorIndexEnumerator q s = boundaryEnumerator q s m := by
  rw [majorIndexEnumerator, boundaryEnumerator]
  apply sum_congr rfl
  intro l _
  rw [listMajorIndex_append_of_forall_le]
  intro i hi
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hi
  exact i.isLt.le

/-- No letter lies above the size of the alphabet. -/
lemma greaterCount_card_alphabet {m : ℕ} (s : Multiset (Fin m)) : greaterCount s m = 0 := by
  rw [greaterCount, Multiset.filter_eq_nil.mpr (fun i _ => not_lt.mpr i.isLt.le)]
  rfl

/-- The major-index enumerator times the content q-factorials is the total q-factorial. -/
lemma majorIndexEnumerator_mul_factorialProduct {m : ℕ} (q : ℂ) (s : Multiset (Fin m)) :
    majorIndexEnumerator q s * factorialProduct q s = qPochhammer q q s.card := by
  rw [majorIndexEnumerator_eq_boundaryEnumerator, boundaryEnumerator_mul_factorialProduct,
    greaterCount_card_alphabet, pow_zero, one_mul]

/-- The q-multinomial identity follows by cancellation away from the unit circle. -/
lemma majorIndexEnumerator_content_of_norm_ne_one {m : ℕ} {q : ℂ} (hq : ‖q‖ ≠ 1)
    (a : Fin m → ℕ) : majorIndexEnumerator q (content a) = qMultinomial q a := by
  apply mul_right_cancel₀ (factorialProduct_ne_zero hq (content a))
  rw [majorIndexEnumerator_mul_factorialProduct, card_content, factorialProduct_content,
    qMultinomial_mul_factorialProduct]

/-- The finite major-index enumerator is continuous in `q`. -/
lemma continuous_majorIndexEnumerator {m : ℕ} (s : Multiset (Fin m)) :
    Continuous (fun q : ℂ => majorIndexEnumerator q s) := by
  unfold majorIndexEnumerator
  fun_prop

/-- Continuity extends the major-index identity to every complex `q`. -/
lemma majorIndexEnumerator_content {m : ℕ} (q : ℂ) (a : Fin m → ℕ) :
    majorIndexEnumerator q (content a) = qMultinomial q a := by
  have hd : Dense (Metric.sphere (0 : ℂ) 1)ᶜ :=
    interior_eq_empty_iff_dense_compl.mp (interior_sphere (0 : ℂ) (by norm_num))
  have he : Set.EqOn (fun q : ℂ => majorIndexEnumerator q (content a))
      (fun q => qMultinomial q a) (Metric.sphere (0 : ℂ) 1)ᶜ := by
    intro z hz
    apply majorIndexEnumerator_content_of_norm_ne_one
    simpa only [Set.mem_compl_iff, Metric.mem_sphere, dist_zero_right] using hz
  exact he.closure (continuous_majorIndexEnumerator _)
    (continuous_qMultinomial _) (by rw [hd.closure_eq]; exact Set.mem_univ q)

/-- The list representation preserves the major index of an indexed word. -/
lemma listMajorIndex_map_ofFn {m n : ℕ} (w : Fin n → Fin m) :
    listMajorIndex ((List.ofFn w).map Fin.val) = wordMajorIndex (fun i => (w i : ℕ)) := by
  simp only [List.map_ofFn, listMajorIndex, wordMajorIndex, wordDescentSet, List.length_ofFn,
    List.get_eq_getElem, List.getElem_ofFn, Function.comp_def]

/-- MacMahon’s major-index generating function for multiset permutations, for every complex `q`. -/
lemma sum_pow_wordMajorIndex (q : ℂ) {m : ℕ} (a : Fin m → ℕ) :
    ∑ w ∈ multisetPermutations a, q ^ wordMajorIndex (fun i => (w i : ℕ)) = qMultinomial q a := by
  rw [← majorIndexEnumerator_content q a, majorIndexEnumerator]
  apply sum_bij (fun w _ => List.ofFn w)
  · intro w hw
    exact (mem_words_content_ofFn a w).mpr hw
  · intro a _ b _ h
    exact List.ofFn_injective h
  · intro l hl
    obtain ⟨w, hw, he⟩ := exists_ofFn_eq_of_mem_words_content a hl
    exact ⟨w, hw, he⟩
  · intro w _
    rw [listMajorIndex_map_ofFn]

/-- The list major index in indexed form. -/
lemma listMajorIndex_def (l : List ℕ) : listMajorIndex l = wordMajorIndex l.get := rfl

/-- The larger-letter count as the cardinality of a filtered content. -/
lemma greaterCount_def {m : ℕ} (s : Multiset (Fin m)) (j : ℕ) :
    greaterCount s j = (s.filter fun i => j < i.val).card := rfl

/-- The boundary enumerator as a finite sum over words. -/
lemma boundaryEnumerator_def {m : ℕ} (q : ℂ) (s : Multiset (Fin m)) (j : ℕ) :
    boundaryEnumerator q s j = ∑ l ∈ words s,
      q ^ listMajorIndex (l.map Fin.val ++ [j]) := rfl

/-- The major-index enumerator as a finite sum over words. -/
lemma majorIndexEnumerator_def {m : ℕ} (q : ℂ) (s : Multiset (Fin m)) :
    majorIndexEnumerator q s = ∑ l ∈ words s, q ^ listMajorIndex (l.map Fin.val) := rfl

end DLMF.Combinatorics.MultisetWords
