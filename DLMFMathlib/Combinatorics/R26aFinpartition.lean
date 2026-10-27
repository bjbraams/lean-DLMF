/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Data.Fintype.Pi

/-!
# Finpartitions from surjections

A surjection `f : α → Fin k` induces the finpartition `r26a_ofFun f` of `univ` into its fibres;
conversely a finpartition with `k` parts comes from exactly `k!` surjections (one for each
labelling of its parts). Hence (`r26a_card_surjective_filter`), for any condition `R` on the
multiset of block sizes,
`#{f : α → Fin k | f surjective, R (fibre sizes)} = k! · #{P | #P.parts = k, R (block sizes)}`.
This reduces the counting of set partitions (Stirling numbers of the second kind, Bell numbers,
set partitions of a given type) to counting maps.
-/

@[expose] public section

open Finset Function

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The fibre of `f` over `j`. -/
def r26a_fiber {k : ℕ} (f : α → Fin k) (j : Fin k) : Finset α := {x | f x = j}

/-- The finpartition of `univ` into the nonempty fibres of `f`. -/
def r26a_ofFun {k : ℕ} (f : α → Fin k) : Finpartition (univ : Finset α) :=
  Finpartition.ofExistsUnique (univ.image fun x => r26a_fiber f (f x)) (by simp)
    (fun a _ => ⟨r26a_fiber f (f a), ⟨mem_image_of_mem _ (mem_univ a), by simp [r26a_fiber]⟩,
      by
        rintro t ⟨ht, hat⟩
        obtain ⟨x, -, rfl⟩ := mem_image.mp ht
        simp only [r26a_fiber, mem_filter, mem_univ, true_and] at hat
        simp [r26a_fiber, hat]⟩)
    (by
      simp only [mem_image, mem_univ, true_and, not_exists]
      intro x hx
      have : x ∈ r26a_fiber f (f x) := by simp [r26a_fiber]
      rw [hx] at this; simp at this)

lemma r26a_ofFun_parts {k : ℕ} (f : α → Fin k) :
    (r26a_ofFun f).parts = univ.image fun x => r26a_fiber f (f x) := rfl

/-- `f` induces `P`: the part of `x` is the fibre of `f` through `x`. -/
lemma r26a_part_ofFun {k : ℕ} (f : α → Fin k) (x : α) :
    (r26a_ofFun f).part x = r26a_fiber f (f x) :=
  (r26a_ofFun f).part_eq_of_mem (by rw [r26a_ofFun_parts]; exact mem_image_of_mem _ (mem_univ x))
    (by simp [r26a_fiber])

lemma r26a_parts_eq_of_part_eq {P Q : Finpartition (univ : Finset α)}
    (h : ∀ x, P.part x = Q.part x) : P = Q := by
  ext t
  constructor
  · intro ht
    obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts ht
    rw [← P.part_eq_of_mem ht hx, h]; simp
  · intro ht
    obtain ⟨x, hx⟩ := Q.nonempty_of_mem_parts ht
    rw [← Q.part_eq_of_mem ht hx, ← h]; simp

lemma r26a_parts_ofFun {k : ℕ} {f : α → Fin k} (hf : Surjective f) :
    (r26a_ofFun f).parts = univ.image (r26a_fiber f) := by
  ext t
  simp only [r26a_ofFun_parts, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨x, rfl⟩; exact ⟨_, rfl⟩
  · rintro ⟨j, rfl⟩; obtain ⟨x, rfl⟩ := hf j; exact ⟨x, rfl⟩

omit [DecidableEq α] in
lemma r26a_fiber_injective {k : ℕ} {f : α → Fin k} (hf : Surjective f) :
    Injective (r26a_fiber f) := by
  intro i j hij
  obtain ⟨x, rfl⟩ := hf i
  have : x ∈ r26a_fiber f (f x) := by simp [r26a_fiber]
  rw [hij] at this
  simpa [r26a_fiber] using this

lemma r26a_card_parts_ofFun {k : ℕ} {f : α → Fin k} (hf : Surjective f) :
    #(r26a_ofFun f).parts = k := by
  rw [r26a_parts_ofFun hf, card_image_of_injective _ (r26a_fiber_injective hf), card_univ,
    Fintype.card_fin]

lemma r26a_map_card_parts_ofFun {k : ℕ} {f : α → Fin k} (hf : Surjective f) :
    (r26a_ofFun f).parts.val.map card = univ.val.map fun j => #(r26a_fiber f j) := by
  rw [r26a_parts_ofFun hf, image_val_of_injOn (r26a_fiber_injective hf).injOn, Multiset.map_map]
  rfl

/-- For a finpartition `P` with `k` parts, the surjections inducing `P` are counted by `k!`. -/
lemma r26a_card_ofFun_eq (k : ℕ) (P : Finpartition (univ : Finset α)) (hP : #P.parts = k) :
    #{f : α → Fin k | Surjective f ∧ r26a_ofFun f = P} = k.factorial := by
  classical
  have hcard : Fintype.card (P.parts ≃ Fin k) = k.factorial := by
    rw [Fintype.card_equiv (Fintype.equivFinOfCardEq (by simpa using hP))]; simp [hP]
  rw [← hcard, ← card_univ]
  symm
  refine card_bij (fun e _ => fun x => e ⟨P.part x, by simp⟩) ?_ ?_ ?_
  · intro e _
    simp only [mem_filter, mem_univ, true_and]
    have hsurj : Surjective fun x => e ⟨P.part x, by simp⟩ := by
      intro j
      obtain ⟨⟨t, ht⟩, rfl⟩ := e.surjective j
      obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts ht
      exact ⟨x, by simp [P.part_eq_of_mem ht hx]⟩
    refine ⟨hsurj, r26a_parts_eq_of_part_eq fun x => ?_⟩
    rw [r26a_part_ofFun]
    ext y
    simp only [r26a_fiber, mem_filter, mem_univ, true_and, e.apply_eq_iff_eq, Subtype.mk.injEq]
    rw [P.mem_part_iff_part_eq_part (mem_univ _) (mem_univ _)]
  · intro e _ e' _ h
    ext ⟨t, ht⟩ : 2
    obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts ht
    have := congrFun h x
    have h2 : (⟨P.part x, by simp⟩ : P.parts) = ⟨t, ht⟩ := Subtype.ext (P.part_eq_of_mem ht hx)
    rw [h2] at this
    rw [this]
  · intro f hf
    simp only [mem_filter, mem_univ, true_and] at hf
    obtain ⟨hs, rfl⟩ := hf
    have key : ∀ (t : (r26a_ofFun f).parts) x, x ∈ t.1 → t.1 = r26a_fiber f (f x) := by
      intro t x hx
      rw [← (r26a_ofFun f).part_eq_of_mem t.2 hx, r26a_part_ofFun]
    let g : (r26a_ofFun f).parts → Fin k := fun t =>
      f ((r26a_ofFun f).nonempty_of_mem_parts t.2).choose
    have hgx : ∀ (t : (r26a_ofFun f).parts) x, x ∈ t.1 → g t = f x := by
      intro t x hx
      obtain ⟨y, hy1, hy2⟩ : ∃ y, g t = f y ∧ y ∈ t.1 :=
        ⟨_, rfl, ((r26a_ofFun f).nonempty_of_mem_parts t.2).choose_spec⟩
      rw [key t x hx] at hy2
      rw [hy1]
      simpa [r26a_fiber] using hy2
    have hg : Bijective g := by
      constructor
      · intro t u htu
        apply Subtype.ext
        obtain ⟨x, hx⟩ := (r26a_ofFun f).nonempty_of_mem_parts t.2
        obtain ⟨y, hy⟩ := (r26a_ofFun f).nonempty_of_mem_parts u.2
        rw [key t x hx, key u y hy, ← hgx t x hx, ← hgx u y hy, htu]
      · intro j
        obtain ⟨x, rfl⟩ := hs j
        exact ⟨⟨(r26a_ofFun f).part x, by simp⟩, hgx _ x (by simp)⟩
    refine ⟨Equiv.ofBijective g hg, mem_univ _, funext fun x => ?_⟩
    exact hgx _ x (by simp)
/-- Surjections `α → Fin k` whose fibre sizes satisfy `R`, against finpartitions with `k` parts
whose block sizes satisfy `R`: each finpartition comes from `k!` surjections. -/
theorem r26a_card_surjective_filter (k : ℕ) (R : Multiset ℕ → Prop) [DecidablePred R] :
    #{f : α → Fin k | Surjective f ∧ R (univ.val.map fun j => #{x | f x = j})} =
      k.factorial * #{P : Finpartition (univ : Finset α) | #P.parts = k ∧
        R (P.parts.val.map card)} := by
  classical
  rw [card_eq_sum_card_fiberwise (f := r26a_ofFun) (t := {P : Finpartition (univ : Finset α) |
    #P.parts = k ∧ R (P.parts.val.map card)})]
  · rw [sum_const_nat (m := k.factorial) ?_, mul_comm]
    intro P hP
    simp only [mem_filter, mem_univ, true_and] at hP
    rw [← r26a_card_ofFun_eq k P hP.1, filter_filter]
    congr 1
    refine filter_congr fun f _ => ?_
    constructor
    · rintro ⟨⟨hs, -⟩, h⟩; exact ⟨hs, h⟩
    · rintro ⟨hs, rfl⟩
      refine ⟨⟨hs, ?_⟩, rfl⟩
      have := hP.2
      rwa [r26a_map_card_parts_ofFun hs] at this
  · intro f hf
    rw [mem_coe, mem_filter] at hf ⊢; refine ⟨mem_univ _, ?_⟩; replace hf := hf.2
    refine ⟨r26a_card_parts_ofFun hf.1, ?_⟩
    rw [r26a_map_card_parts_ofFun hf.1]
    exact hf.2
