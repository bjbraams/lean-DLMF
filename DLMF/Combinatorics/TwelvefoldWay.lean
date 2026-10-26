/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Combinatorics.RestrictedPartitions
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.Data.Sym.Card
public import Mathlib.Data.Fintype.Powerset
public import DLMFMathlib.Combinatorics.Q26bSurjections

/-!
# The twelvefold way (DLMF §26.17, Table 26.17.1)

Mappings `f : N → K` from a set `N` of `n` balls to a set `K` of `k` boxes are
`f : Fin n → Fin k`, restricted to all maps, injective maps or surjective maps
(`MapRestriction`). When the balls (resp. boxes) are unlabeled, maps are identified up to a
permutation of `N` (resp. of `K`): `f ∼ τ ∘ f ∘ σ` (`twelvefoldRel`). `twelvefoldCount balls
boxes r n k` is the number of equivalence classes, `Nat.card` of the quotient. The twelve
entries of Table 26.17.1 are the twelve theorems below, all tagged `26.17.T1`.

Conventions and qualifications:

* `(k-n+1)_n` (Pochhammer's symbol) is `(ascPochhammer ℤ n).eval (k - n + 1)`, which is `0` for
  `n > k`.
* `C(n-1, n-k)` (unlabeled balls, labeled boxes, onto) is stated for `1 ≤ k ≤ n`; for `k > n`
  there is no onto map, and `n = k = 0` gives `1`.
* `S(n,1) + ⋯ + S(n,k)` (labeled balls, unlabeled boxes, unrestricted) is stated for `n ≥ 1`: for
  `n = 0` there is one (empty) map while the sum is `0`; the sum from `j = 0` is correct for all
  `n`.
* `p_k(n) - p_{k-1}(n)` (unlabeled balls and boxes, onto) needs `k ≥ 1`.
* `S(n, k)` is Mathlib's `Nat.stirlingSecond`; `p_k(n)` is `partitionCountAtMostParts`.

## References

* NIST DLMF §26.17; R. P. Stanley, Enumerative Combinatorics I (1997), p. 33.
-/

@[expose] public section

noncomputable section

open Finset Equiv Polynomial

namespace DLMF.Combinatorics

/-- Whether the balls (elements of `N`) or the boxes (elements of `K`) are labeled. -/
inductive Labeling
  | labeled
  | unlabeled
  deriving DecidableEq

/-- The three columns of Table 26.17.1. -/
inductive MapRestriction
  | unrestricted
  | injective
  | surjective
  deriving DecidableEq

/-- The predicate on maps selected by a column of Table 26.17.1. -/
def MapRestriction.Holds {n k : ℕ} : MapRestriction → (Fin n → Fin k) → Prop
  | .unrestricted, _ => True
  | .injective, f => Function.Injective f
  | .surjective, f => Function.Surjective f

/-- Two maps are identified when they differ by a permutation of the unlabeled sides:
`g = τ ∘ f ∘ σ` with `σ = 1` if the balls are labeled and `τ = 1` if the boxes are labeled. -/
def twelvefoldRel {n k : ℕ} (balls boxes : Labeling) (f g : Fin n → Fin k) : Prop :=
  ∃ σ : Perm (Fin n), ∃ τ : Perm (Fin k), (balls = .labeled → σ = 1) ∧ (boxes = .labeled → τ = 1) ∧
    g = τ ∘ f ∘ σ

/-- The entry of Table 26.17.1: the number of classes of maps `Fin n → Fin k` satisfying the
restriction `r`, up to the permutations of the unlabeled sides (DLMF §26.17). -/
@[dlmf 26.17]
def twelvefoldCount (balls boxes : Labeling) (r : MapRestriction) (n k : ℕ) : ℕ :=
  Nat.card (Quot fun f g : {f : Fin n → Fin k // r.Holds f} => twelvefoldRel balls boxes f.1 g.1)

/-- With both sides labeled the relation is equality, so the quotient is the set of maps. -/
lemma c26b_twelvefoldCount_labeled (r : MapRestriction) (n k : ℕ) :
    twelvefoldCount .labeled .labeled r n k = Nat.card {f : Fin n → Fin k // r.Holds f} := by
  unfold twelvefoldCount
  refine Nat.card_congr (Equiv.ofBijective (Quot.mk _) ⟨fun a b h => ?_, Quot.mk_surjective⟩).symm
  have hr : ∀ a b : {f : Fin n → Fin k // r.Holds f},
      twelvefoldRel .labeled .labeled a.1 b.1 → a = b := by
    rintro a b ⟨σ, τ, hσ, hτ, h⟩
    rw [hσ rfl, hτ rfl] at h
    exact Subtype.ext (by simpa using h.symm)
  have key : ∀ x y, Relation.EqvGen
      (fun f g : {f : Fin n → Fin k // r.Holds f} => twelvefoldRel .labeled .labeled f.1 g.1) x y →
      x = y := by
    intro x y hxy
    induction hxy with
    | rel x y hxy => exact hr x y hxy
    | refl => rfl
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2
  exact key a b (Quot.eqvGen_exact h)

/-- The relation for unlabeled balls and labeled boxes. -/
lemma q26b_rel_UL {n k : ℕ} (f g : Fin n → Fin k) :
    twelvefoldRel .unlabeled .labeled f g ↔ ∃ σ : Perm (Fin n), g = f ∘ σ := by
  constructor
  · rintro ⟨σ, τ, -, hτ, h⟩
    rw [hτ rfl] at h
    exact ⟨σ, by simpa using h⟩
  · rintro ⟨σ, h⟩
    exact ⟨σ, 1, fun h => Labeling.noConfusion h, fun _ => rfl, by simpa using h⟩

/-- The number of classes is `1` if `n ≤ k` and `0` otherwise, for injections. -/
lemma q26b_natCard_quot_injective {n k : ℕ} (r : {f : Fin n → Fin k // Function.Injective f} →
    {f : Fin n → Fin k // Function.Injective f} → Prop) (hr : ∀ a b, r a b) :
    Nat.card (Quot r) = if n ≤ k then 1 else 0 := by
  split_ifs with h
  · rw [q26b_natCard_quot r (fun _ => ()) (fun a b => by simp [hr a b])
      (fun _ => ⟨⟨Fin.castLE h, Fin.castLE_injective h⟩, rfl⟩)]
    simp
  · rw [Nat.card_eq_zero]
    left
    refine ⟨fun q => ?_⟩
    obtain ⟨a, -⟩ := Quot.exists_rep q
    have := Fintype.card_le_of_injective _ a.2
    simp at this
    omega

/-- The kernel of `f` (the blocks of the set partition of the domain induced by `f`). -/
def q26b_ker {n : ℕ} {β : Type*} [DecidableEq β] (f : Fin n → β) : Fin n → Finset (Fin n) :=
  fun i => univ.filter fun i' => f i' = f i

/-- Two maps have the same kernel iff they identify the same pairs of points. -/
lemma q26b_ker_eq_iff {n : ℕ} {β γ : Type*} [DecidableEq β] [DecidableEq γ] (f : Fin n → β)
    (g : Fin n → γ) : q26b_ker f = q26b_ker g ↔ ∀ i i', (f i' = f i ↔ g i' = g i) := by
  constructor
  · intro h i i'
    have := congrArg (fun K => i' ∈ K i) h
    simpa [q26b_ker] using this
  · intro h
    funext i
    ext i'
    simp [q26b_ker, h i i']

/-- Postcomposition with an injective map preserves the kernel. -/
lemma q26b_ker_comp {n : ℕ} {β γ : Type*} [DecidableEq β] [DecidableEq γ] (f : Fin n → β)
    {e : β → γ} (he : Function.Injective e) : q26b_ker (e ∘ f) = q26b_ker f :=
  (q26b_ker_eq_iff _ _).2 fun _ _ => he.eq_iff

/-- Maps into `Fin k` with the same kernel differ by a permutation of `Fin k`. -/
lemma q26b_exists_perm_of_ker_eq {n k : ℕ} {f g : Fin n → Fin k} (h : q26b_ker f = q26b_ker g) :
    ∃ τ : Perm (Fin k), g = τ ∘ f := by
  classical
  rw [q26b_ker_eq_iff] at h
  let φ : Set.range f → Fin k := fun x => g x.2.choose
  have hφ : ∀ i, φ ⟨f i, i, rfl⟩ = g i := fun i =>
    ((h i (⟨f i, i, rfl⟩ : Set.range f).2.choose).1
      (⟨f i, i, rfl⟩ : Set.range f).2.choose_spec)
  have hinj : Function.Injective φ := by
    rintro ⟨x, i, rfl⟩ ⟨y, j, rfl⟩ hxy
    rw [hφ, hφ] at hxy
    exact Subtype.ext ((h i j).2 hxy.symm).symm
  obtain ⟨τ, hτ⟩ := q26b_exists_perm_comp_of_injective Subtype.val_injective hinj
  refine ⟨τ, funext fun i => ?_⟩
  rw [← hφ i, hτ]
  rfl

/-- The number of blocks of the kernel of `g` is the size of the image of `g`. -/
lemma q26b_card_image_ker {n : ℕ} {β : Type*} [DecidableEq β] (g : Fin n → β) :
    #(univ.image (q26b_ker g)) = #(univ.image g) := by
  classical
  have : univ.image (q26b_ker g) =
      (univ.image g).image fun c => univ.filter fun i' => g i' = c := by
    rw [Finset.image_image]; rfl
  rw [this, card_image_of_injOn]
  intro c hc c' _ hcc'
  obtain ⟨i, -, rfl⟩ := mem_image.mp hc
  have := congrArg (fun K : Finset (Fin n) => i ∈ K) hcc'
  simpa using this

/-- For labeled balls and unlabeled boxes, the classes are the kernels. -/
lemma q26b_rel_LU {n k : ℕ} (f g : Fin n → Fin k) :
    twelvefoldRel .labeled .unlabeled f g ↔ q26b_ker f = q26b_ker g := by
  constructor
  · rintro ⟨σ, τ, hσ, -, h⟩
    rw [hσ rfl] at h
    subst h
    exact (q26b_ker_comp f τ.injective).symm
  · intro h
    obtain ⟨τ, hτ⟩ := q26b_exists_perm_of_ker_eq h
    exact ⟨1, τ, fun _ => rfl, fun h => Labeling.noConfusion h, by simpa using hτ⟩

/-- Labeled balls, unlabeled boxes: the count is the number of kernels. -/
lemma q26b_twelvefoldCount_LU (r : MapRestriction) (n k : ℕ)
    [DecidablePred (r.Holds (n := n) (k := k))] :
    twelvefoldCount .labeled .unlabeled r n k =
      #((univ.filter (r.Holds (n := n) (k := k))).image q26b_ker) := by
  unfold twelvefoldCount
  rw [q26b_natCard_quot (M := {x // x ∈ (univ.filter (r.Holds (n := n) (k := k))).image q26b_ker}) _
    (fun f => ⟨q26b_ker f.1, mem_image_of_mem _ (by simpa using f.2)⟩)]
  · rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  · intro a b
    rw [q26b_rel_LU, Subtype.ext_iff]
  · rintro ⟨x, hx⟩
    obtain ⟨f, hf, rfl⟩ := mem_image.mp hx
    exact ⟨⟨f, by simpa using hf⟩, rfl⟩

/-- `twelvefoldRel` is an equivalence relation. -/
lemma q26b_twelvefoldRel_equivalence {n k : ℕ} (balls boxes : Labeling) :
    Equivalence (twelvefoldRel (n := n) (k := k) balls boxes) := by
  refine ⟨fun f => ⟨1, 1, fun _ => rfl, fun _ => rfl, rfl⟩, ?_, ?_⟩
  · rintro f g ⟨σ, τ, hσ, hτ, rfl⟩
    refine ⟨σ⁻¹, τ⁻¹, fun h => by rw [hσ h, inv_one], fun h => by rw [hτ h, inv_one], ?_⟩
    funext i; simp
  · rintro f g h ⟨σ, τ, hσ, hτ, rfl⟩ ⟨σ', τ', hσ', hτ', rfl⟩
    refine ⟨σ * σ', τ' * τ, fun h => by rw [hσ h, hσ' h, mul_one],
      fun h => by rw [hτ h, hτ' h, mul_one], ?_⟩
    funext i; simp

/-- `Quot.mk` of an equivalence relation. -/
lemma q26b_quot_mk_eq_iff {α : Type*} {r : α → α → Prop} (h : Equivalence r) (a b : α) :
    Quot.mk r a = Quot.mk r b ↔ r a b :=
  ⟨fun e => h.eqvGen_iff.mp (Quot.eqvGen_exact e), Quot.sound⟩

/-- Table 26.17.1, labeled balls, unlabeled boxes, onto (used for the unrestricted entry). -/
lemma q26b_LU_surj (n k : ℕ) :
    twelvefoldCount .labeled .unlabeled .surjective n k = Nat.stirlingSecond n k := by
  classical
  unfold twelvefoldCount
  set r := fun f g : {f : Fin n → Fin k // MapRestriction.surjective.Holds f} =>
    twelvefoldRel .labeled .unlabeled f.1 g.1 with hr
  have heq : Equivalence r := by
    have h := q26b_twelvefoldRel_equivalence (n := n) (k := k) .labeled .unlabeled
    exact ⟨fun a => h.refl _, fun hab => h.symm hab, fun hab hbc => h.trans hab hbc⟩
  let _ : Fintype (Quot r) := Fintype.ofFinite _
  have hfib : ∀ a : {f : Fin n → Fin k // MapRestriction.surjective.Holds f},
      #{b | Quot.mk r b = Quot.mk r a} = k.factorial := by
    intro a
    rw [show k.factorial = #(univ : Finset (Perm (Fin k))) by
      simp [card_univ, Fintype.card_perm]]
    symm
    refine Finset.card_bij (fun τ _ => (⟨τ ∘ a.1, τ.surjective.comp a.2⟩ :
      {f : Fin n → Fin k // MapRestriction.surjective.Holds f})) ?_ ?_ ?_
    · intro τ _
      simp only [mem_filter, mem_univ, true_and]
      rw [q26b_quot_mk_eq_iff heq]
      refine ⟨1, τ⁻¹, fun _ => rfl, fun h => Labeling.noConfusion h, ?_⟩
      funext i; simp
    · intro τ _ τ' _ h
      have h' : τ ∘ a.1 = τ' ∘ a.1 := congrArg Subtype.val h
      exact Equiv.ext (congrFun ((a.2 : Function.Surjective a.1).injective_comp_right h'))
    · intro b hb
      simp only [mem_filter, mem_univ, true_and] at hb
      rw [q26b_quot_mk_eq_iff heq] at hb
      obtain ⟨σ, τ, hσ, -, h⟩ := hb
      rw [hσ rfl] at h
      exact ⟨τ⁻¹, mem_univ _, Subtype.ext (by funext i; simp [h])⟩
  have htot : k.factorial * Nat.stirlingSecond n k =
      Fintype.card (Quot r) * k.factorial := by
    rw [← q26b_card_surjective_fin, ← Fintype.card_subtype]
    rw [show Fintype.card {x : Fin n → Fin k // Function.Surjective x} =
      #(univ : Finset {f : Fin n → Fin k // MapRestriction.surjective.Holds f}) by
        rw [card_univ]; exact Fintype.card_congr (Equiv.refl _)]
    rw [Finset.card_eq_sum_card_fiberwise (f := Quot.mk r) (t := univ)
        (fun _ _ => mem_univ _)]
    rw [Finset.sum_const_nat (m := k.factorial)]
    · rfl
    · intro q _
      obtain ⟨a, rfl⟩ := Quot.exists_rep q
      exact hfib a
  rw [Nat.card_eq_fintype_card]
  have := Nat.factorial_pos k
  rw [mul_comm] at htot
  exact (Nat.eq_of_mul_eq_mul_right this htot).symm


/-- The `Sym` of values of a map. -/
def q26b_sym {n k : ℕ} (f : Fin n → Fin k) : Sym (Fin k) n := ⟨univ.val.map f, by simp⟩

/-- The multiset of all multiplicities of `s` is its partition padded by zeros. -/
lemma q26b_map_count_eq {k n : ℕ} (s : Sym (Fin k) n) :
    univ.val.map (fun c => Multiset.count c s.1) =
      (Nat.Partition.ofSym s).parts +
        Multiset.replicate (k - Multiset.card (Nat.Partition.ofSym s).parts) 0 := by
  classical
  have hsplit := Multiset.filter_add_not (fun c => c ∈ s.1) (univ : Finset (Fin k)).val
  have h1 : Multiset.filter (fun c => c ∈ s.1) (univ : Finset (Fin k)).val = s.1.dedup := by
    rw [Multiset.Nodup.ext (Multiset.Nodup.filter _ univ.nodup) (Multiset.nodup_dedup _)]
    intro a; simp
  have hparts : (Nat.Partition.ofSym s).parts = s.1.dedup.map fun c => Multiset.count c s.1 := rfl
  have h2 : (Multiset.filter (fun c => c ∉ s.1) (univ : Finset (Fin k)).val).map
      (fun c => Multiset.count c s.1) =
      Multiset.replicate (k - Multiset.card (Nat.Partition.ofSym s).parts) 0 := by
    rw [Multiset.eq_replicate]
    constructor
    · rw [Multiset.card_map, hparts, Multiset.card_map]
      have := congrArg Multiset.card hsplit
      rw [Multiset.card_add, h1] at this
      simp only [Finset.card_val, card_univ, Fintype.card_fin] at this
      omega
    · intro b hb
      obtain ⟨c, hc, rfl⟩ := Multiset.mem_map.mp hb
      exact Multiset.count_eq_zero.mpr (Multiset.mem_filter.mp hc).2
  rw [← hsplit, Multiset.map_add, h1, h2, hparts]

/-- Two elements of `Sym (Fin k) n` with the same partition differ by a permutation. -/
lemma q26b_exists_perm_of_ofSym_eq {k n : ℕ} {s t : Sym (Fin k) n}
    (h : Nat.Partition.ofSym s = Nat.Partition.ofSym t) :
    ∃ τ : Perm (Fin k), t.1 = s.1.map τ := by
  classical
  have hc : univ.val.map (fun c => Multiset.count c s.1) =
      univ.val.map (fun c => Multiset.count c t.1) := by
    rw [q26b_map_count_eq, q26b_map_count_eq, h]
  obtain ⟨ρ, hρ⟩ := (q26b_map_eq_iff _ _).1 hc
  refine ⟨ρ⁻¹, Multiset.ext.2 fun c => ?_⟩
  have h1 := congrFun hρ c
  simp only [Function.comp_apply] at h1
  rw [h1, ← Multiset.count_map_eq_count' (⇑ρ⁻¹) s.1 (ρ⁻¹).injective (ρ c)]
  simp

/-- Every partition of `n` into at most `k` parts is the partition of some `s : Sym (Fin k) n`. -/
lemma q26b_exists_ofSym_eq {k n : ℕ} (p : n.Partition) (hp : Multiset.card p.parts ≤ k) :
    ∃ s : Sym (Fin k) n, Nat.Partition.ofSym s = p := by
  classical
  set l := p.parts.toList with hl
  have hlen : l.length ≤ k := by rw [hl, Multiset.length_toList]; exact hp
  let s0 : Multiset (Fin l.length) :=
    (univ : Finset (Fin l.length)).val.bind fun i => Multiset.replicate (l.get i) i
  have hcount : ∀ i, Multiset.count i s0 = l.get i := by
    intro i
    rw [Multiset.count_bind]
    rw [show (univ : Finset (Fin l.length)).val.map
        (fun b => Multiset.count i (Multiset.replicate (l.get b) b)) =
        (univ : Finset (Fin l.length)).val.map (fun b => if b = i then l.get i else 0) by
      refine Multiset.map_congr rfl fun b _ => ?_
      rw [Multiset.count_replicate]
      split_ifs <;> simp_all]
    rw [← Finset.sum_eq_multiset_sum, Finset.sum_ite_eq' univ i]
    simp
  have hpos : ∀ i, 0 < l.get i := fun i =>
    p.parts_pos (by rw [← Multiset.mem_toList, ← hl]; exact List.get_mem l i)
  have hded : s0.dedup = (univ : Finset (Fin l.length)).val := by
    rw [Multiset.Nodup.ext (Multiset.nodup_dedup _) univ.nodup]
    intro i
    simp only [Multiset.mem_dedup, Finset.mem_val, mem_univ, iff_true]
    rw [← Multiset.count_pos, hcount]; exact hpos i
  have hsum : Multiset.card s0 = n := by
    rw [Multiset.card_bind]
    simp only [Function.comp_def, Multiset.card_replicate]
    rw [Fin.univ_val_map, List.ofFn_get, Multiset.sum_coe, ← Multiset.sum_coe, hl,
      Multiset.coe_toList, p.parts_sum]
  refine ⟨⟨s0.map (Fin.castLE hlen), by rw [Multiset.card_map, hsum]⟩, ?_⟩
  ext1
  change (s0.map (Fin.castLE hlen)).dedup.map
    (fun c => Multiset.count c (s0.map (Fin.castLE hlen))) = _
  rw [Multiset.dedup_map_of_injective (Fin.castLE_injective hlen), Multiset.map_map]
  simp only [Function.comp_def, Multiset.count_map_eq_count' _ _ (Fin.castLE_injective hlen),
    hcount, hded]
  rw [Fin.univ_val_map, List.ofFn_get, hl, Multiset.coe_toList]

/-- For unlabeled balls and boxes, the classes are the partitions of fibre sizes. -/
lemma q26b_rel_UU {n k : ℕ} (f g : Fin n → Fin k) :
    twelvefoldRel .unlabeled .unlabeled f g ↔
      Nat.Partition.ofSym (q26b_sym f) = Nat.Partition.ofSym (q26b_sym g) := by
  constructor
  · rintro ⟨σ, τ, -, -, rfl⟩
    have : q26b_sym (τ ∘ f ∘ σ) = (q26b_sym f).map τ := by
      apply Sym.ext
      change univ.val.map (τ ∘ f ∘ σ) = (univ.val.map f).map τ
      rw [← Multiset.map_map, ← Multiset.map_map, Multiset.map_univ_val_equiv]
    rw [this, Nat.Partition.ofSym_map]
  · intro h
    obtain ⟨τ, hτ⟩ := q26b_exists_perm_of_ofSym_eq h
    have h2 : univ.val.map (τ ∘ f) = univ.val.map g := by
      rw [← Multiset.map_map]; exact hτ.symm
    obtain ⟨σ, hσ⟩ := (q26b_map_eq_iff _ _).1 h2
    exact ⟨σ, τ, fun h => Labeling.noConfusion h, fun h => Labeling.noConfusion h, hσ⟩

/-- The number of parts of the partition of fibre sizes is the size of the image. -/
lemma q26b_card_parts_ofSym {n k : ℕ} (f : Fin n → Fin k) :
    Multiset.card (Nat.Partition.ofSym (q26b_sym f)).parts = #(univ.image f) := by
  change Multiset.card ((univ.val.map f).dedup.map _) = _
  rw [Multiset.card_map]
  rfl

/-- Unlabeled balls and boxes: the count is the number of fibre-size partitions. -/
lemma q26b_twelvefoldCount_UU (r : MapRestriction) (n k : ℕ)
    [DecidablePred (r.Holds (n := n) (k := k))] :
    twelvefoldCount .unlabeled .unlabeled r n k =
      #((univ.filter (r.Holds (n := n) (k := k))).image
        fun f => Nat.Partition.ofSym (q26b_sym f)) := by
  unfold twelvefoldCount
  rw [q26b_natCard_quot (M := {x // x ∈ (univ.filter (r.Holds (n := n) (k := k))).image
    fun f => Nat.Partition.ofSym (q26b_sym f)}) _
    (fun f => ⟨Nat.Partition.ofSym (q26b_sym f.1), mem_image_of_mem _ (by simpa using f.2)⟩)]
  · rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  · intro a b
    rw [q26b_rel_UU, Subtype.ext_iff]
  · rintro ⟨x, hx⟩
    obtain ⟨f, hf, rfl⟩ := mem_image.mp hx
    exact ⟨⟨f, by simpa using hf⟩, rfl⟩

/-- A map into `Fin k` is onto iff its image has `k` elements. -/
lemma q26b_surjective_iff_card_image {n k : ℕ} (f : Fin n → Fin k) :
    Function.Surjective f ↔ #(univ.image f) = k := by
  constructor
  · intro h; rw [Finset.image_univ_of_surjective h]; simp
  · intro h c
    have h' : univ.image f = univ := Finset.eq_univ_of_card _ (by simpa using h)
    have : c ∈ univ.image f := h' ▸ mem_univ c
    obtain ⟨i, -, hi⟩ := mem_image.mp this
    exact ⟨i, hi⟩

/-- The fibre-size partitions of the maps with `P (image size)` are the partitions into at most
`k` parts with `P (number of parts)`. -/
lemma q26b_image_UU {n k : ℕ} (P : ℕ → Prop) [DecidablePred P] :
    ((univ : Finset (Fin n → Fin k)).filter (fun f => P #(univ.image f))).image
      (fun f => Nat.Partition.ofSym (q26b_sym f)) =
      univ.filter fun p : n.Partition => Multiset.card p.parts ≤ k ∧ P (Multiset.card p.parts) := by
  ext p
  simp only [mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨f, hf, rfl⟩
    rw [q26b_card_parts_ofSym]
    exact ⟨(card_le_univ _).trans (by simp), hf⟩
  · rintro ⟨hk, hP⟩
    obtain ⟨s, rfl⟩ := q26b_exists_ofSym_eq p hk
    obtain ⟨f, hf⟩ := q26b_exists_map_eq s.1 s.2
    have hs : q26b_sym f = s := Sym.ext hf
    refine ⟨f, ?_, by rw [hs]⟩
    rw [← q26b_card_parts_ofSym, hs]; exact hP

/-- Table 26.17.1, labeled balls, labeled boxes, `f` unrestricted: `kⁿ`. -/
@[dlmf 26.17.T1]
theorem twelvefoldCount_LL_unrestricted (n k : ℕ) :
    twelvefoldCount .labeled .labeled .unrestricted n k = k ^ n := by
  rw [c26b_twelvefoldCount_labeled]
  change Nat.card {f : Fin n → Fin k // True} = _
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial)]
  simp

/-- Table 26.17.1, labeled balls, labeled boxes, `f` one-to-one: `(k-n+1)_n`. -/
@[dlmf 26.17.T1]
theorem twelvefoldCount_LL_injective (n k : ℕ) :
    (twelvefoldCount .labeled .labeled .injective n k : ℤ) =
      (ascPochhammer ℤ n).eval ((k : ℤ) - n + 1) := by
  rw [c26b_twelvefoldCount_labeled]
  change (Nat.card {f : Fin n → Fin k // Function.Injective f} : ℤ) = _
  rw [Nat.card_congr (Equiv.subtypeInjectiveEquivEmbedding (Fin n) (Fin k)),
    Nat.card_eq_fintype_card, Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin]
  have h := descPochhammer_eval_eq_descFactorial ℤ k n
  rw [descPochhammer_eq_ascPochhammer, eval_comp] at h
  simp only [eval_sub, eval_add, eval_X, eval_natCast, eval_one] at h
  rw [← h]

/-- Table 26.17.1, labeled balls, labeled boxes, `f` onto: `k! S(n, k)`. -/
@[dlmf 26.17.T1]
theorem twelvefoldCount_LL_surjective (n k : ℕ) :
    twelvefoldCount .labeled .labeled .surjective n k = k.factorial * Nat.stirlingSecond n k := by
  rw [c26b_twelvefoldCount_labeled]
  change Nat.card {f : Fin n → Fin k // Function.Surjective f} = _
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact q26b_card_surjective_fin n k

/-- Table 26.17.1, unlabeled balls, labeled boxes, `f` unrestricted: `C(k+n-1, n)`. -/
@[dlmf 26.17.T1]
theorem twelvefoldCount_UL_unrestricted (n k : ℕ) :
    twelvefoldCount .unlabeled .labeled .unrestricted n k = (k + n - 1).choose n := by
  unfold twelvefoldCount
  rw [q26b_natCard_quot (M := Sym (Fin k) n) _
    (fun f : {f : Fin n → Fin k // MapRestriction.unrestricted.Holds f} =>
    (⟨univ.val.map f.1, by simp⟩ : Sym (Fin k) n))]
  · rw [Nat.card_eq_fintype_card, Sym.card_sym_eq_choose, Fintype.card_fin]
  · intro a b
    rw [q26b_rel_UL, ← q26b_map_eq_iff]
    exact ⟨fun h => Sym.ext h, fun h => congrArg Sym.toMultiset h⟩
  · intro s
    obtain ⟨f, hf⟩ := q26b_exists_map_eq s.1 s.2
    exact ⟨⟨f, trivial⟩, Sym.ext hf⟩

/-- Table 26.17.1, unlabeled balls, labeled boxes, `f` one-to-one: `C(k, n)`. -/
@[dlmf 26.17.T1]
theorem twelvefoldCount_UL_injective (n k : ℕ) :
    twelvefoldCount .unlabeled .labeled .injective n k = k.choose n := by
  unfold twelvefoldCount
  have himg : ∀ f : Fin n → Fin k, Function.Injective f → (univ.image f).val = univ.val.map f :=
    fun f hf => Finset.image_val_of_injOn (fun a _ b _ h => hf h)
  rw [q26b_natCard_quot _ (fun f : {f : Fin n → Fin k // MapRestriction.injective.Holds f} =>
    (⟨univ.image f.1, by rw [card_image_of_injective _ f.2, card_univ, Fintype.card_fin]⟩ :
      {T : Finset (Fin k) // #T = n}))]
  · rw [Nat.card_eq_fintype_card, Fintype.card_finset_len, Fintype.card_fin]
  · intro a b
    rw [q26b_rel_UL, ← q26b_map_eq_iff, Subtype.ext_iff, ← Finset.val_inj, himg _ a.2,
      himg _ b.2]
  · rintro ⟨T, hT⟩
    obtain ⟨f, hf⟩ := q26b_exists_map_eq T.val hT
    have hinj : Function.Injective f := by
      have hnd : (univ.val.map f).Nodup := hf ▸ T.nodup
      exact fun a b h => Multiset.inj_on_of_nodup_map hnd a (mem_univ a) b (mem_univ b) h
    refine ⟨⟨f, hinj⟩, Subtype.ext ?_⟩
    rw [← Finset.val_inj, himg _ hinj, hf]

/-- Table 26.17.1, unlabeled balls, labeled boxes, `f` onto: `C(n-1, n-k)`, for `1 ≤ k ≤ n`. -/
@[dlmf 26.17.T1]
theorem twelvefoldCount_UL_surjective {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    twelvefoldCount .unlabeled .labeled .surjective n k = (n - 1).choose (n - k) := by
  unfold twelvefoldCount
  have hle : ∀ f : Fin n → Fin k, Function.Surjective f →
      (univ : Finset (Fin k)).val ≤ univ.val.map f := by
    intro f hf
    rw [Multiset.le_iff_count]
    intro j
    rw [Multiset.count_eq_one_of_mem univ.nodup (mem_univ j), Nat.one_le_iff_ne_zero,
      Ne, Multiset.count_eq_zero, not_not]
    obtain ⟨i, rfl⟩ := hf j
    exact Multiset.mem_map_of_mem f (mem_univ i)
  rw [q26b_natCard_quot (M := Sym (Fin k) (n - k)) _
    (fun f : {f : Fin n → Fin k // MapRestriction.surjective.Holds f} =>
    (⟨univ.val.map f.1 - univ.val, by
      rw [Multiset.card_sub (hle f.1 f.2)]; simp⟩ : Sym (Fin k) (n - k)))]
  · rw [Nat.card_eq_fintype_card, Sym.card_sym_eq_choose, Fintype.card_fin]
    congr 1; omega
  · intro a b
    rw [q26b_rel_UL, ← q26b_map_eq_iff]
    constructor
    · intro h; exact Sym.ext (by simp only [h])
    · intro h
      have h' : univ.val.map a.1 - univ.val = univ.val.map b.1 - univ.val :=
        congrArg Sym.toMultiset h
      rw [← Multiset.sub_add_cancel (hle _ a.2), h', Multiset.sub_add_cancel (hle _ b.2)]
  · intro s
    obtain ⟨f, hf⟩ := q26b_exists_map_eq (n := n) (s.1 + (univ : Finset (Fin k)).val)
      (by rw [Multiset.card_add, s.2]; simp; omega)
    have hsurj : Function.Surjective f := by
      intro j
      have : j ∈ univ.val.map f := by rw [hf]; exact Multiset.mem_add.mpr (Or.inr (mem_univ j))
      obtain ⟨i, -, hi⟩ := Multiset.mem_map.mp this
      exact ⟨i, hi⟩
    exact ⟨⟨f, hsurj⟩, Sym.ext (by simp [hf])⟩

/-- Table 26.17.1, labeled balls, unlabeled boxes, `f` unrestricted:
`S(n,1) + S(n,2) + ⋯ + S(n,k)`, for `n ≥ 1` (see the module docstring for `n = 0`). -/
@[dlmf 26.17.T1]
theorem twelvefoldCount_LU_unrestricted {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    twelvefoldCount .labeled .unlabeled .unrestricted n k =
      ∑ j ∈ Icc 1 k, Nat.stirlingSecond n j := by
  classical
  have hS : ∀ j, #((univ.filter fun g : Fin n → Fin j => Function.Surjective g).image q26b_ker) =
      Nat.stirlingSecond n j := by
    intro j
    rw [← q26b_LU_surj, q26b_twelvefoldCount_LU]
    congr 2; ext g; simp [MapRestriction.Holds]
  have hall : (univ.filter (MapRestriction.unrestricted.Holds (n := n) (k := k))).image q26b_ker =
      (range (k + 1)).biUnion fun j =>
        (univ.filter fun g : Fin n → Fin j => Function.Surjective g).image q26b_ker := by
    ext K
    simp only [mem_image, mem_filter, mem_univ, true_and, mem_biUnion, mem_range]
    constructor
    · rintro ⟨f, -, rfl⟩
      let T := univ.image f
      have hT : ∀ i, f i ∈ T := fun i => mem_image_of_mem f (mem_univ i)
      let g : Fin n → Fin #T := fun i => T.equivFin ⟨f i, hT i⟩
      refine ⟨#T, Nat.lt_succ_of_le (card_le_univ T |>.trans (by simp)), g, ?_, ?_⟩
      · intro c
        obtain ⟨⟨x, hx⟩, rfl⟩ := T.equivFin.surjective c
        obtain ⟨i, -, rfl⟩ := mem_image.mp hx
        exact ⟨i, rfl⟩
      · rw [q26b_ker_eq_iff]
        intro i i'
        simp only [g, EmbeddingLike.apply_eq_iff_eq, Subtype.mk.injEq]
    · rintro ⟨j, hj, g, -, rfl⟩
      exact ⟨Fin.castLE (by omega) ∘ g, trivial, q26b_ker_comp g (Fin.castLE_injective _)⟩
  rw [q26b_twelvefoldCount_LU, hall, card_biUnion]
  · simp_rw [hS]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega),
      Nat.stirlingSecond_succ_zero, zero_add]
    rfl
  · intro j _ j' _ hjj'
    rw [Function.onFun, Finset.disjoint_left]
    intro K hK hK'
    obtain ⟨g, hg, rfl⟩ := mem_image.mp hK
    obtain ⟨g', hg', hgg'⟩ := mem_image.mp hK'
    simp only [mem_filter, mem_univ, true_and] at hg hg'
    have h1 := q26b_card_image_ker g
    have h2 := q26b_card_image_ker g'
    rw [hgg', Finset.image_univ_of_surjective hg', Finset.image_univ_of_surjective hg] at *
    simp at h1 h2
    omega

/-- Table 26.17.1, labeled balls, unlabeled boxes, `f` one-to-one: `1` if `n ≤ k`, else `0`. -/
@[dlmf 26.17.T1]
theorem twelvefoldCount_LU_injective (n k : ℕ) :
    twelvefoldCount .labeled .unlabeled .injective n k = if n ≤ k then 1 else 0 := by
  refine q26b_natCard_quot_injective _ fun a b => ?_
  obtain ⟨τ, hτ⟩ := q26b_exists_perm_comp_of_injective a.2 b.2
  exact ⟨1, τ, fun _ => rfl, fun h => Labeling.noConfusion h, by simpa using hτ⟩

/-- Table 26.17.1, labeled balls, unlabeled boxes, `f` onto: `S(n, k)`. -/
@[dlmf 26.17.T1]
theorem twelvefoldCount_LU_surjective (n k : ℕ) :
    twelvefoldCount .labeled .unlabeled .surjective n k = Nat.stirlingSecond n k := by
  exact q26b_LU_surj n k

/-- Table 26.17.1, unlabeled balls, unlabeled boxes, `f` unrestricted: `p_k(n)`. -/
@[dlmf 26.17.T1]
theorem twelvefoldCount_UU_unrestricted (n k : ℕ) :
    twelvefoldCount .unlabeled .unlabeled .unrestricted n k = partitionCountAtMostParts k n := by
  classical
  rw [q26b_twelvefoldCount_UU]
  have := q26b_image_UU (n := n) (k := k) (fun _ => True)
  simp only [and_true] at this
  rw [partitionCountAtMostParts, ← this]
  congr 2
  ext f; simp [MapRestriction.Holds]

/-- Table 26.17.1, unlabeled balls, unlabeled boxes, `f` one-to-one: `1` if `n ≤ k`, else `0`. -/
@[dlmf 26.17.T1]
theorem twelvefoldCount_UU_injective (n k : ℕ) :
    twelvefoldCount .unlabeled .unlabeled .injective n k = if n ≤ k then 1 else 0 := by
  refine q26b_natCard_quot_injective _ fun a b => ?_
  obtain ⟨τ, hτ⟩ := q26b_exists_perm_comp_of_injective a.2 b.2
  exact ⟨1, τ, fun h => Labeling.noConfusion h, fun h => Labeling.noConfusion h, by simpa using hτ⟩

/-- Table 26.17.1, unlabeled balls, unlabeled boxes, `f` onto: `p_k(n) - p_{k-1}(n)`, `k ≥ 1`. -/
@[dlmf 26.17.T1]
theorem twelvefoldCount_UU_surjective {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    (twelvefoldCount .unlabeled .unlabeled .surjective n k : ℤ) =
      partitionCountAtMostParts k n - partitionCountAtMostParts (k - 1) n := by
  classical
  rw [q26b_twelvefoldCount_UU]
  have := q26b_image_UU (n := n) (k := k) (fun m => m = k)
  rw [show (univ.filter (MapRestriction.surjective.Holds (n := n) (k := k))) =
    univ.filter (fun f => #(univ.image f) = k) by
      ext f; simp [MapRestriction.Holds, q26b_surjective_iff_card_image], this]
  have hsplit : (univ.filter fun p : n.Partition => Multiset.card p.parts ≤ k) =
      (univ.filter fun p : n.Partition => Multiset.card p.parts ≤ k - 1) ∪
        (univ.filter fun p : n.Partition =>
          Multiset.card p.parts ≤ k ∧ Multiset.card p.parts = k) := by
    ext p; simp only [mem_filter, mem_univ, true_and, mem_union]; omega
  have hdisj : Disjoint (univ.filter fun p : n.Partition => Multiset.card p.parts ≤ k - 1)
      (univ.filter fun p : n.Partition =>
        Multiset.card p.parts ≤ k ∧ Multiset.card p.parts = k) := by
    rw [Finset.disjoint_left]
    intro p h1 h2
    simp only [mem_filter, mem_univ, true_and] at h1 h2
    omega
  unfold partitionCountAtMostParts
  rw [hsplit, card_union_of_disjoint hdisj]
  push_cast
  ring

end DLMF.Combinatorics
