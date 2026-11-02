/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Combinatorics.Enumerative.InclusionExclusion
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Fintype.Lattice

/-!
# Counting surjections

The number of surjections `Fin n → Fin k`, through Stirling numbers of the second kind and
by inclusion–exclusion, and the classification of maps up to permutations of the domain.

## Main results

* `Fintype.card_filter_surjective_congr`: the number of surjections `ι → α` depends only on
  `α` up to equivalence.
* `Fin.card_filter_surjective`: `#{f : Fin n → Fin k | f surjective} = k! S(n, k)`.
* `Fin.card_filter_surjective_eq_alternating_sum`: the inclusion–exclusion formula
  `#{surjections} = ∑_{t=0}^k (-1)^t C(k, t) (k-t)ⁿ`.
* `Nat.card_quot_eq_of_surjective`: classes of a relation counted by a complete invariant.
* `Multiset.map_univ_eq_map_univ_iff`: two maps have the same multiset of values iff they
  differ by a permutation of the domain.
* `Multiset.exists_map_univ_eq`, `Function.Injective.exists_perm_comp_eq`.

## Implementation notes

`Fin.card_filter_surjective` is proved by strong induction on `k` from the identity
`kⁿ = ∑_j C(k, j) · #{surjections Fin n → Fin j}` (classifying maps by their image) and
Mathlib's `Nat.pow_eq_sum_stirlingSecond_mul_descFactorial`.
-/

@[expose] public section

open Finset Equiv

/-- The number of surjections `ι → α` depends only on `α` up to equivalence. -/
theorem Fintype.card_filter_surjective_congr {ι α β : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (e : α ≃ β) :
    #{f : ι → α | Function.Surjective f} = #{f : ι → β | Function.Surjective f} := by
  refine Finset.card_bij (fun f _ => e ∘ f) ?_ ?_ ?_
  · intro f hf
    simp only [mem_filter, mem_univ, true_and] at hf ⊢
    exact e.surjective.comp hf
  · intro f _ g _ h
    funext i
    exact e.injective (congrFun h i)
  · intro g hg
    simp only [mem_filter, mem_univ, true_and] at hg
    refine ⟨e.symm ∘ g, ?_, ?_⟩
    · simp only [mem_filter, mem_univ, true_and]
      exact e.symm.surjective.comp hg
    · funext i; simp

/-- The maps `ι → β` with image exactly `T` are the surjections onto `T`. -/
private lemma Fintype.card_filter_image_univ_eq {ι β : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (T : Finset β) :
    #{f : ι → β | univ.image f = T} = #{g : ι → T | Function.Surjective g} := by
  symm
  refine Finset.card_bij (fun g _ => fun i => (g i : β)) ?_ ?_ ?_
  · intro g hg
    simp only [mem_filter, mem_univ, true_and] at hg ⊢
    ext b
    simp only [mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩; exact (g i).2
    · intro hb
      obtain ⟨i, hi⟩ := hg ⟨b, hb⟩
      exact ⟨i, by rw [hi]⟩
  · intro f _ g _ h
    funext i
    exact Subtype.ext (congrFun h i)
  · intro f hf
    simp only [mem_filter, mem_univ, true_and] at hf
    have hmem : ∀ i, f i ∈ T := fun i => hf ▸ mem_image_of_mem f (mem_univ i)
    refine ⟨fun i => ⟨f i, hmem i⟩, ?_, rfl⟩
    simp only [mem_filter, mem_univ, true_and]
    rintro ⟨b, hb⟩
    rw [← hf] at hb
    obtain ⟨i, -, hi⟩ := mem_image.mp hb
    exact ⟨i, Subtype.ext hi⟩

/-- `kⁿ = ∑_{j=0}^k C(k, j) · #{surjections Fin n → Fin j}`. -/
private lemma Fin.pow_eq_sum_choose_mul_card_filter_surjective (n k : ℕ) :
    k ^ n = ∑ j ∈ range (k + 1), k.choose j * #{f : Fin n → Fin j | Function.Surjective f} := by
  have h1 : k ^ n = #(univ : Finset (Fin n → Fin k)) := by simp [card_univ]
  rw [h1, Finset.card_eq_sum_card_fiberwise (f := fun f : Fin n → Fin k => univ.image f)
    (t := (univ : Finset (Fin k)).powerset) (fun f _ => mem_powerset.mpr (subset_univ _))]
  have h2 : ∀ T ∈ (univ : Finset (Fin k)).powerset,
      #{f ∈ (univ : Finset (Fin n → Fin k)) | univ.image f = T} =
        #{f : Fin n → Fin #T | Function.Surjective f} := by
    intro T _
    rw [Fintype.card_filter_image_univ_eq T]
    exact Fintype.card_filter_surjective_congr (T.equivFin.trans (finCongr rfl))
  rw [Finset.sum_congr rfl h2, Finset.sum_powerset_apply_card
    (fun m => #{f : Fin n → Fin m | Function.Surjective f})]
  simp [card_univ, Fintype.card_fin]

/-- The number of surjections `Fin n → Fin k` is `k! S(n, k)`. -/
theorem Fin.card_filter_surjective (n k : ℕ) :
    #{f : Fin n → Fin k | Function.Surjective f} = k.factorial * Nat.stirlingSecond n k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    have h1 := Fin.pow_eq_sum_choose_mul_card_filter_surjective n k
    have h2 := Nat.pow_eq_sum_stirlingSecond_mul_descFactorial k n
    rw [Finset.sum_range_succ, Nat.choose_self, one_mul] at h1
    have hS : ∑ j ∈ range (k + 1), Nat.stirlingSecond n j * k.descFactorial j =
        ∑ j ∈ range (k + 1), k.choose j * (j.factorial * Nat.stirlingSecond n j) := by
      refine sum_congr rfl fun j _ => ?_
      rw [Nat.descFactorial_eq_factorial_mul_choose]; ring
    have hS' : ∑ j ∈ range (n + 1), Nat.stirlingSecond n j * k.descFactorial j =
        ∑ j ∈ range (k + 1), Nat.stirlingSecond n j * k.descFactorial j := by
      rcases le_or_gt n k with h | h
      · rw [← Finset.sum_range_add_sum_Ico _ (by omega : n + 1 ≤ k + 1), left_eq_add]
        refine sum_eq_zero fun j hj => ?_
        rw [Nat.stirlingSecond_eq_zero_of_lt (by simp at hj; omega), zero_mul]
      · rw [← Finset.sum_range_add_sum_Ico _ (by omega : k + 1 ≤ n + 1), add_eq_left]
        refine sum_eq_zero fun j hj => ?_
        rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by simp at hj; omega), mul_zero]
    rw [hS', hS, Finset.sum_range_succ, Nat.choose_self, one_mul] at h2
    have h3 : ∑ j ∈ range k, k.choose j * #{f : Fin n → Fin j | Function.Surjective f} =
        ∑ j ∈ range k, k.choose j * (j.factorial * Nat.stirlingSecond n j) :=
      sum_congr rfl fun j hj => by rw [ih j (mem_range.mp hj)]
    omega

/-- Inclusion–exclusion: `#{surjections Fin n → Fin k} = ∑_{t=0}^k (-1)^t C(k, t) (k-t)ⁿ`. -/
theorem Fin.card_filter_surjective_eq_alternating_sum (n k : ℕ) :
    (#{f : Fin n → Fin k | Function.Surjective f} : ℤ) =
      ∑ t ∈ range (k + 1), (-1 : ℤ) ^ t * k.choose t * ((k - t : ℕ) : ℤ) ^ n := by
  classical
  let S : Fin k → Finset (Fin n → Fin k) := fun j => univ.filter fun f => ∀ i, f i ≠ j
  have hsurj : (univ.filter fun f : Fin n → Fin k => Function.Surjective f) =
      (univ : Finset (Fin k)).inf fun j => (S j)ᶜ := by
    ext f
    rw [mem_filter, Finset.mem_inf]
    simp [Function.Surjective, S]
  have hcard : ∀ t : Finset (Fin k), #(t.inf S) = (k - #t) ^ n := by
    intro t
    have : t.inf S = univ.filter fun f : Fin n → Fin k => ∀ i, f i ∈ tᶜ := by
      ext f
      simp only [Finset.mem_inf, mem_filter, mem_univ, true_and, S, mem_compl]
      exact ⟨fun h i hi => h _ hi i rfl, fun h j hj i hij => h i (hij ▸ hj)⟩
    rw [this, ← Fintype.card_subtype, Fintype.card_congr Equiv.subtypePiEquivPi,
      Fintype.card_fun, Fintype.card_fin, Fintype.card_coe, card_compl, Fintype.card_fin]
  rw [hsurj, inclusion_exclusion_card_inf_compl]
  simp_rw [hcard]
  rw [Finset.sum_powerset_apply_card (fun m => (-1 : ℤ) ^ m * (((k - m : ℕ) ^ n : ℕ) : ℤ))]
  simp only [card_univ, Fintype.card_fin, nsmul_eq_mul]
  refine sum_congr rfl fun t _ => ?_
  push_cast; ring

/-- Counting the classes of a relation through a complete invariant. -/
theorem Nat.card_quot_eq_of_surjective {α M : Type*} (r : α → α → Prop) (F : α → M)
    (hF : ∀ a b, r a b ↔ F a = F b) (hs : Function.Surjective F) :
    Nat.card (Quot r) = Nat.card M := by
  refine Nat.card_congr (Equiv.ofBijective (Quot.lift F fun a b h => (hF a b).1 h) ⟨?_, ?_⟩)
  · intro x y hxy
    induction x using Quot.ind
    induction y using Quot.ind
    exact Quot.sound ((hF _ _).2 hxy)
  · intro m
    obtain ⟨a, rfl⟩ := hs m
    exact ⟨Quot.mk _ a, rfl⟩

/-- Two maps with fibres of equal sizes differ by a permutation of the domain. -/
private lemma Equiv.Perm.exists_comp_eq_of_card_fiber_eq {α β : Type*} [Fintype α]
    [DecidableEq β] {f g : α → β}
    (h : ∀ c, #{a | f a = c} = #{a | g a = c}) : ∃ σ : Perm α, ∀ a, g (σ a) = f a := by
  classical
  have e : ∀ c, {a // f a = c} ≃ {a // g a = c} := fun c =>
    Fintype.equivOfCardEq (by rw [Fintype.card_subtype, Fintype.card_subtype]; convert h c)
  exact ⟨Equiv.ofFiberEquiv e, Equiv.ofFiberEquiv_map e⟩

/-- The multiset of values of `f`. -/
theorem Multiset.count_map_univ {α β : Type*} [Fintype α] [DecidableEq β] (f : α → β) (c : β) :
    Multiset.count c (univ.val.map f) = #{a | f a = c} := by
  rw [Multiset.count_map]
  simp only [Finset.card, Finset.filter_val]
  congr 1
  exact Multiset.filter_congr fun a _ => eq_comm

/-- Two maps have the same multiset of values iff they differ by a permutation of the domain. -/
theorem Multiset.map_univ_eq_map_univ_iff {α β : Type*} [Fintype α] [DecidableEq β] (f g : α → β) :
    univ.val.map f = univ.val.map g ↔ ∃ σ : Perm α, g = f ∘ σ := by
  constructor
  · intro h
    have hc : ∀ c, #{a | g a = c} = #{a | f a = c} := fun c => by
      rw [← Multiset.count_map_univ, ← Multiset.count_map_univ, h]
    obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_comp_eq_of_card_fiber_eq hc
    exact ⟨σ, funext fun a => (hσ a).symm⟩
  · rintro ⟨σ, rfl⟩
    rw [← Multiset.map_map]
    congr 1
    exact (Multiset.map_univ_val_equiv σ).symm

/-- Every multiset of cardinality `n` is the multiset of values of a map on `Fin n`. -/
theorem Multiset.exists_map_univ_eq {β : Type*} {n : ℕ} (s : Multiset β) (h : Multiset.card s = n) :
    ∃ f : Fin n → β, univ.val.map f = s := by
  obtain ⟨l, rfl⟩ := Quot.exists_rep s
  change Multiset.card (l : Multiset β) = n at h
  rw [Multiset.coe_card] at h
  subst h
  exact ⟨l.get, by rw [Fin.univ_val_map, List.ofFn_get]; rfl⟩

/-- Two injections into a finite type differ by a permutation of the target. -/
theorem Function.Injective.exists_perm_comp_eq {α β : Type*} [Fintype β] {a b : α → β}
    (ha : Function.Injective a) (hb : Function.Injective b) : ∃ τ : Perm β, b = τ ∘ a := by
  classical
  let e : {x // x ∈ Set.range a} ≃ {x // x ∈ Set.range b} :=
    (Equiv.ofInjective a ha).symm.trans (Equiv.ofInjective b hb)
  refine ⟨e.extendSubtype, funext fun i => ?_⟩
  simp only [Function.comp_apply]
  rw [Equiv.extendSubtype_apply_of_mem e (a i) ⟨i, rfl⟩]
  simp [e, Equiv.ofInjective_symm_apply]
