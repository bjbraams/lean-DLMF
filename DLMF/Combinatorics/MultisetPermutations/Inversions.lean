/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Combinatorics.Basic.Permutations
public import Mathlib.Analysis.Complex.Basic
import DLMF.QSeries.QBinomial
import Mathlib.Data.List.Permutation
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
# The inversion enumerator for multiset permutations

The first-letter decomposition of list words gives a finite recurrence for their inversion
polynomial. Multiplying by the q-factorials of the multiplicities and using a geometric
block telescoping identity gives the total q-factorial. The Gaussian-binomial product
has the same multiplicative identity. Cancellation proves equality away from the unit
circle, and continuity extends it to every complex `q`, including roots of unity.

The proof reuses Mathlib's `Finset.prod_one_add_ordered`, its finite-multiset and list
permutation APIs, and the project's proved `qBinom_mul_qPochhammer`. The indexed-word
bridge preserves the definition and normalization of DLMF 26.16.2.

## Main results

* `MultisetWords.enumerator_mul_factorialProduct`: the multiplicative q-factorial identity.
* `MultisetWords.enumerator_content`: the inversion enumerator for every complex `q`.
* `MultisetWords.sum_pow_wordInversions`: the indexed-word form of DLMF 26.16.2.
-/

public noncomputable section

open Finset DLMF.QSeries

namespace DLMF.Combinatorics.MultisetWords

/-- The finite set of list words with the given multiset of letters. -/
@[expose] def words {m : ℕ} (s : Multiset (Fin m)) : Finset (List (Fin m)) :=
  s.toList.permutations.toFinset

/-- A list word belongs to the enumerator precisely when its multiset of letters agrees. -/
lemma mem_words {m : ℕ} {s : Multiset (Fin m)} {l : List (Fin m)} :
    l ∈ words s ↔ (l : Multiset (Fin m)) = s := by
  simp only [words, List.mem_toFinset, List.mem_permutations, ← Multiset.coe_eq_coe,
    Multiset.coe_toList]

/-- The inversion number of a list word, using the canonical indexed-word statistic. -/
@[expose] def inversions {m : ℕ} (l : List (Fin m)) : ℕ :=
  wordInversions (fun i : Fin l.length => (l.get i : ℕ))

/-- The empty word has no inversions. -/
lemma inversions_nil {m : ℕ} : inversions ([] : List (Fin m)) = 0 := by
  simp [inversions, wordInversions]

/-- An initial letter contributes one inversion for each smaller letter in the tail. -/
lemma inversions_cons {m : ℕ} (j : Fin m) (l : List (Fin m)) :
    inversions (j :: l) = inversions l + l.countP (· < j) := by
  have countP_eq_sum_get (p : Fin m → Bool) (l : List (Fin m)) :
      l.countP p = ∑ i : Fin l.length, if p (l.get i) then 1 else 0 := by
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.countP_cons, List.length_cons, Fin.sum_univ_succ,
        List.get_cons_zero, List.get_cons_succ', ← ih]
      split_ifs <;> simp_all [Nat.add_comm]
  simp only [inversions, wordInversions, card_filter, Fintype.sum_prod_type]
  simp only [List.length_cons, Fin.sum_univ_succ, List.get_cons_zero, List.get_cons_succ',
    Fin.not_lt_zero, false_and, ite_false, Fin.succ_pos, Fin.succ_lt_succ_iff, true_and,
    zero_add, Fin.val_fin_lt]
  rw [countP_eq_sum_get]
  simp only [decide_eq_true_eq]
  omega

/-- The empty word is the only word with no letters. -/
lemma words_zero (m : ℕ) : words (0 : Multiset (Fin m)) = {[]} := by
  simp [words]

/-- Nonempty words split disjointly by their first letter. -/
lemma words_eq_biUnion {m : ℕ} {s : Multiset (Fin m)} (hs : s ≠ 0) :
    words s = s.toFinset.biUnion fun j =>
      (words (s.erase j)).map ⟨List.cons j, List.cons_injective⟩ := by
  ext l
  simp only [mem_words, mem_biUnion, Multiset.mem_toFinset, mem_map,
    Function.Embedding.coeFn_mk]
  cases l with
  | nil => simp [Ne.symm hs]
  | cons j l =>
    constructor
    · intro h
      have hj : j ∈ s := by rw [← h]; simp
      refine ⟨j, hj, l, ?_, rfl⟩
      rw [← h]
      simp
    · rintro ⟨j', hj, l', hl', he⟩
      obtain ⟨rfl, rfl⟩ := List.cons.inj he
      rw [← Multiset.cons_coe, hl', Multiset.cons_erase hj]

/-- The inversion-generating polynomial evaluated at `q` for words with fixed content. -/
@[expose] def enumerator {m : ℕ} (q : ℂ) (s : Multiset (Fin m)) : ℂ :=
  ∑ l ∈ words s, q ^ inversions l

/-- The number of letters strictly smaller than a given letter. -/
@[expose] def lowerCount {m : ℕ} (s : Multiset (Fin m)) (j : Fin m) : ℕ :=
  (s.filter (· < j)).card

/-- The smaller-letter count of the tail is determined by the full content. -/
lemma countP_lt_of_cons_eq {m : ℕ} {s : Multiset (Fin m)} {j : Fin m} {l : List (Fin m)}
    (h : (j :: l : Multiset (Fin m)) = s) : l.countP (· < j) = lowerCount s j := by
  rw [lowerCount, ← h, ← Multiset.cons_coe, Multiset.filter_cons]
  simp only [lt_self_iff_false, ↓reduceIte]
  rw [Multiset.filter_coe, zero_add, Multiset.coe_card, ← List.countP_eq_length_filter]

/-- The empty word contributes the constant one. -/
lemma enumerator_zero (q : ℂ) (m : ℕ) : enumerator q (0 : Multiset (Fin m)) = 1 := by
  rw [enumerator, words_zero, sum_singleton, inversions_nil, pow_zero]

/-- The first-letter recurrence for the inversion-generating polynomial. -/
lemma enumerator_eq_sum {m : ℕ} (q : ℂ) {s : Multiset (Fin m)} (hs : s ≠ 0) :
    enumerator q s = ∑ j ∈ s.toFinset, q ^ lowerCount s j * enumerator q (s.erase j) := by
  rw [enumerator, words_eq_biUnion hs, sum_biUnion]
  · apply sum_congr rfl
    intro j hj
    rw [sum_map, enumerator, mul_sum]
    apply sum_congr rfl
    intro l hl
    have he := mem_words.mp hl
    have hc : (j :: l : Multiset (Fin m)) = s := by
      rw [← Multiset.cons_coe, he, Multiset.cons_erase (Multiset.mem_toFinset.mp hj)]
    dsimp only [Function.Embedding.coeFn_mk]
    rw [inversions_cons, countP_lt_of_cons_eq hc, pow_add]
    exact mul_comm _ _
  · intro a _ b _ hab
    simp only [Function.onFun]
    rw [disjoint_left]
    intro l hla hlb
    obtain ⟨la, _, he⟩ := mem_map.mp hla
    obtain ⟨lb, _, he'⟩ := mem_map.mp hlb
    exact hab (List.cons.inj (he.trans he'.symm)).1

/-- The product of finite q-factorials of the letter multiplicities. -/
@[expose] def factorialProduct {m : ℕ} (q : ℂ) (s : Multiset (Fin m)) : ℂ :=
  ∏ j : Fin m, qPochhammer q q (s.count j)

/-- Erasing one occurrence removes the final factor of that letter's q-factorial. -/
lemma factorialProduct_erase {m : ℕ} (q : ℂ) {s : Multiset (Fin m)} {j : Fin m}
    (hj : j ∈ s) :
    factorialProduct q s = (1 - q ^ s.count j) * factorialProduct q (s.erase j) := by
  have he (i : Fin m) : qPochhammer q q (s.count i) =
      (if i = j then 1 - q ^ s.count j else 1) * qPochhammer q q ((s.erase j).count i) := by
    by_cases hi : i = j
    · subst i
      rw [ite_eq_left rfl, Multiset.count_erase_self]
      obtain ⟨k, hk⟩ : ∃ k, s.count j = k + 1 :=
        ⟨s.count j - 1, by have := Multiset.count_pos.mpr hj; omega⟩
      rw [hk, Nat.add_sub_cancel, qPochhammer_succ]
      simp only [pow_succ]
      ring
    · rw [ite_eq_right hi, one_mul, Multiset.count_erase_of_ne hi]
  rw [factorialProduct, prod_congr rfl (fun i _ => he i), prod_mul_distrib]
  simp only [prod_ite_eq' univ j, mem_univ, ite_true]
  rfl

/-- The number of smaller letters is the sum of their multiplicities. -/
lemma lowerCount_eq_sum {m : ℕ} (s : Multiset (Fin m)) (j : Fin m) :
    lowerCount s j = ∑ i : Fin m with i < j, s.count i := by
  rw [lowerCount, ← Multiset.sum_count_eq_card (s := univ) (m := s.filter (· < j))
    (fun _ _ => mem_univ _)]
  simp only [Multiset.count_filter, sum_filter]

/-- The consecutive letter blocks telescope to the total geometric factor. -/
lemma sum_pow_lowerCount_mul_one_sub_pow_count {m : ℕ} (q : ℂ) (s : Multiset (Fin m)) :
    ∑ j ∈ s.toFinset, q ^ lowerCount s j * (1 - q ^ s.count j) = 1 - q ^ s.card := by
  have h := prod_one_add_ordered (univ : Finset (Fin m)) (fun j => q ^ s.count j - 1)
  have he (j : Fin m) : 1 + (q ^ s.count j - 1) = q ^ s.count j := by ring
  simp_rw [he, prod_pow_eq_pow_sum] at h
  rw [Multiset.sum_count_eq_card (fun _ _ => mem_univ _)] at h
  simp_rw [← lowerCount_eq_sum] at h
  have hs : (∑ j ∈ s.toFinset, q ^ lowerCount s j * (1 - q ^ s.count j)) =
      ∑ j : Fin m, q ^ lowerCount s j * (1 - q ^ s.count j) := by
    apply sum_subset (subset_univ _)
    intro j _ hj
    have hc : s.count j = 0 := Multiset.count_eq_zero.mpr (by simpa using hj)
    rw [hc, pow_zero, sub_self, mul_zero]
  rw [hs]
  calc
    _ = -(∑ j : Fin m, (q ^ s.count j - 1) * q ^ lowerCount s j) := by
      rw [← sum_neg_distrib]
      apply sum_congr rfl
      intro j _
      ring
    _ = _ := by linear_combination h

/-- The inversion enumerator times the multiplicity factorials is the total q-factorial. -/
lemma enumerator_mul_factorialProduct_of_card (q : ℂ) (m n : ℕ) :
    ∀ s : Multiset (Fin m), s.card = n →
      enumerator q s * factorialProduct q s = qPochhammer q q n := by
  induction n with
  | zero =>
    intro s hs
    obtain rfl := Multiset.card_eq_zero.mp hs
    simp [enumerator_zero, factorialProduct]
  | succ n ih =>
    intro s hs
    have hs0 : s ≠ 0 := by intro h; simp [h] at hs
    rw [enumerator_eq_sum q hs0, sum_mul]
    calc
      _ = ∑ j ∈ s.toFinset,
          q ^ lowerCount s j * (1 - q ^ s.count j) * qPochhammer q q n := by
        apply sum_congr rfl
        intro j hj
        have hj' := Multiset.mem_toFinset.mp hj
        have hcard : (s.erase j).card = n := by
          simpa only [hs, Nat.pred_succ] using Multiset.card_erase_of_mem hj'
        rw [factorialProduct_erase q hj']
        calc
          _ = q ^ lowerCount s j * (1 - q ^ s.count j) *
              (enumerator q (s.erase j) * factorialProduct q (s.erase j)) := by ring
          _ = _ := by rw [ih _ hcard]
      _ = (1 - q ^ s.card) * qPochhammer q q n := by
        rw [← sum_mul, sum_pow_lowerCount_mul_one_sub_pow_count]
      _ = _ := by rw [hs, qPochhammer_succ, pow_succ]; ring

/-- The multiplicative q-multinomial formula, without excluding roots of unity. -/
lemma enumerator_mul_factorialProduct {m : ℕ} (q : ℂ) (s : Multiset (Fin m)) :
    enumerator q s * factorialProduct q s = qPochhammer q q s.card :=
  enumerator_mul_factorialProduct_of_card q m s.card s rfl

/-- Separate the first letter in the product defining the q-multinomial. -/
lemma qMultinomial_succ (q : ℂ) {m : ℕ} (a : Fin (m + 1) → ℕ) :
    qMultinomial q a =
      qBinom q (a 0 + ∑ i : Fin m, a i.succ) (a 0) *
        qMultinomial q (fun i : Fin m => a i.succ) := by
  simp only [qMultinomial, Fin.prod_univ_succ, sum_filter, Fin.sum_univ_succ,
    Fin.zero_le, ite_true, not_le.mpr (Fin.succ_pos _), ite_false, zero_add, Fin.succ_le_succ_iff]

/-- The Gaussian-binomial product gives the multiplicative q-factorial formula. -/
lemma qMultinomial_mul_factorialProduct (q : ℂ) {m : ℕ} (a : Fin m → ℕ) :
    qMultinomial q a * ∏ j : Fin m, qPochhammer q q (a j) =
      qPochhammer q q (∑ j : Fin m, a j) := by
  induction m with
  | zero => simp [qMultinomial]
  | succ m ih =>
    rw [qMultinomial_succ, Fin.prod_univ_succ, Fin.sum_univ_succ]
    calc
      _ = qBinom q (a 0 + ∑ i : Fin m, a i.succ) (a 0) * qPochhammer q q (a 0) *
          (qMultinomial q (fun i : Fin m => a i.succ) *
            ∏ i : Fin m, qPochhammer q q (a i.succ)) := by ring
      _ = _ := by rw [ih, qBinom_mul_qPochhammer]

/-- The multiset with the prescribed finite family of letter multiplicities. -/
@[expose] def content {m : ℕ} (a : Fin m → ℕ) : Multiset (Fin m) :=
  (Finsupp.equivFunOnFinite.symm a).toMultiset

/-- The content multiset has exactly the prescribed number of each letter. -/
lemma count_content {m : ℕ} (a : Fin m → ℕ) (j : Fin m) : (content a).count j = a j := by
  simp [content]

/-- The content size is the sum of all letter multiplicities. -/
lemma card_content {m : ℕ} (a : Fin m → ℕ) : (content a).card = ∑ j, a j := by
  rw [← Multiset.sum_count_eq_card (s := univ) (m := content a) (fun _ _ => mem_univ _)]
  simp only [count_content]

/-- The q-factorial product of a content multiset uses the prescribed multiplicities. -/
lemma factorialProduct_content {m : ℕ} (q : ℂ) (a : Fin m → ℕ) :
    factorialProduct q (content a) = ∏ j, qPochhammer q q (a j) := by
  simp only [factorialProduct, count_content]

/-- Away from the unit circle, all finite q-factorials are nonzero. -/
lemma factorialProduct_ne_zero {m : ℕ} {q : ℂ} (hq : ‖q‖ ≠ 1) (s : Multiset (Fin m)) :
    factorialProduct q s ≠ 0 := by
  have hp (n : ℕ) : qPochhammer q q n ≠ 0 := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [qPochhammer_succ]
      apply mul_ne_zero ih
      have hpow : q ^ (n + 1) ≠ 1 := fun h =>
        hq (Complex.norm_eq_one_of_pow_eq_one h (by omega))
      simpa only [pow_succ, mul_comm] using sub_ne_zero.mpr hpow.symm
  exact prod_ne_zero_iff.mpr (fun j _ => hp (s.count j))

/-- Cancellation gives the q-multinomial identity away from the unit circle. -/
lemma enumerator_content_of_norm_ne_one {m : ℕ} {q : ℂ} (hq : ‖q‖ ≠ 1) (a : Fin m → ℕ) :
    enumerator q (content a) = qMultinomial q a := by
  apply mul_right_cancel₀ (factorialProduct_ne_zero hq (content a))
  rw [enumerator_mul_factorialProduct, card_content, factorialProduct_content,
    qMultinomial_mul_factorialProduct]

/-- The finite inversion enumerator is continuous as a function of `q`. -/
lemma continuous_enumerator {m : ℕ} (s : Multiset (Fin m)) :
    Continuous (fun q : ℂ => enumerator q s) := by
  unfold enumerator
  fun_prop

/-- The polynomial Gaussian-binomial product is continuous in `q`. -/
lemma continuous_qMultinomial {m : ℕ} (a : Fin m → ℕ) :
    Continuous (fun q : ℂ => qMultinomial q a) := by
  unfold qMultinomial
  exact continuous_finsetProd _ (fun j _ => continuous_qBinom _ _)

/-- Continuity extends the q-multinomial identity to every complex `q`. -/
lemma enumerator_content {m : ℕ} (q : ℂ) (a : Fin m → ℕ) :
    enumerator q (content a) = qMultinomial q a := by
  have hd : Dense (Metric.sphere (0 : ℂ) 1)ᶜ :=
    interior_eq_empty_iff_dense_compl.mp (interior_sphere (0 : ℂ) (by norm_num))
  have he : Set.EqOn (fun q : ℂ => enumerator q (content a)) (fun q => qMultinomial q a)
      (Metric.sphere (0 : ℂ) 1)ᶜ := by
    intro z hz
    apply enumerator_content_of_norm_ne_one
    simpa only [Set.mem_compl_iff, Metric.mem_sphere, dist_zero_right] using hz
  exact he.closure (continuous_enumerator _)
    (continuous_qMultinomial _) (by rw [hd.closure_eq]; exact Set.mem_univ q)

/-- Lists and indexed words express the same prescribed multiplicities. -/
lemma mem_words_content_ofFn {m : ℕ} (a : Fin m → ℕ)
    (w : Fin (∑ i, a i) → Fin m) :
    List.ofFn w ∈ words (content a) ↔ w ∈ multisetPermutations a := by
  rw [mem_words, Multiset.ext]
  simp only [Multiset.coe_count, List.count_ofFn, count_content,
    multisetPermutations, mem_filter, mem_univ, true_and]

/-- Every word with prescribed content has the corresponding indexed representation. -/
lemma exists_ofFn_eq_of_mem_words_content {m : ℕ} (a : Fin m → ℕ) {l : List (Fin m)}
    (hl : l ∈ words (content a)) :
    ∃ w ∈ multisetPermutations a, List.ofFn w = l := by
  have he : l.length = ∑ i, a i := by
    have h := congrArg Multiset.card (mem_words.mp hl)
    simpa only [Multiset.coe_card, card_content] using h
  let w : Fin (∑ i, a i) → Fin m := fun i => l.get (Fin.cast he.symm i)
  have hw : List.ofFn w = l :=
    (List.ofFn_congr he l.get).symm.trans (List.ofFn_get l)
  refine ⟨w, (mem_words_content_ofFn a w).mp ?_, hw⟩
  rw [hw]
  exact hl

/-- Passing from an indexed word to its list preserves the inversion statistic. -/
lemma inversions_ofFn {m n : ℕ} (w : Fin n → Fin m) :
    inversions (List.ofFn w) = wordInversions (fun i => (w i : ℕ)) := by
  simp only [inversions, wordInversions, List.get_eq_getElem, List.getElem_ofFn]
  let e := Equiv.prodCongr (finCongr (List.length_ofFn (f := w)))
    (finCongr (List.length_ofFn (f := w)))
  apply Finset.card_equiv e
  intro p
  simp only [mem_filter, mem_univ, true_and, e, Equiv.prodCongr_apply, Fin.lt_def]
  rfl

/-- The inversion generating function of multiset permutations is the q-multinomial. -/
lemma sum_pow_wordInversions (q : ℂ) {m : ℕ} (a : Fin m → ℕ) :
    ∑ w ∈ multisetPermutations a, q ^ wordInversions (fun i => (w i : ℕ)) = qMultinomial q a := by
  rw [← enumerator_content q a, enumerator]
  apply sum_bij (fun w _ => List.ofFn w)
  · intro w hw
    exact (mem_words_content_ofFn a w).mpr hw
  · intro a _ b _ h
    exact List.ofFn_injective h
  · intro l hl
    obtain ⟨w, hw, he⟩ := exists_ofFn_eq_of_mem_words_content a hl
    exact ⟨w, hw, he⟩
  · intro w _
    rw [inversions_ofFn]

/-- The word inversion statistic in indexed form. -/
lemma inversions_def {m : ℕ} (l : List (Fin m)) :
    inversions l = wordInversions (fun i : Fin l.length => (l.get i : ℕ)) := rfl

/-- The finite sum defining the inversion enumerator. -/
lemma enumerator_def {m : ℕ} (q : ℂ) (s : Multiset (Fin m)) :
    enumerator q s = ∑ l ∈ words s, q ^ inversions l := rfl

/-- The filtered-multiset definition of the smaller-letter count. -/
lemma lowerCount_def {m : ℕ} (s : Multiset (Fin m)) (j : Fin m) :
    lowerCount s j = (s.filter (· < j)).card := rfl

/-- The finite product defining the multiplicity q-factorial. -/
lemma factorialProduct_def {m : ℕ} (q : ℂ) (s : Multiset (Fin m)) :
    factorialProduct q s = ∏ j : Fin m, qPochhammer q q (s.count j) := rfl

/-- Equality with the prescribed content is characterized by each letter's count. -/
lemma content_eq_iff {m : ℕ} (a : Fin m → ℕ) (s : Multiset (Fin m)) :
    content a = s ↔ ∀ j, s.count j = a j := by
  rw [Multiset.ext]
  simp only [count_content]
  exact ⟨fun h j => (h j).symm, fun h j => (h j).symm⟩

end DLMF.Combinatorics.MultisetWords
