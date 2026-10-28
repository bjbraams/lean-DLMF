/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Combinatorics.Permutations.EulerianNumbers

/-!
# Rook polynomials and permutation matrices

Matrix interpretations of permutations and deletion and union identities for rook polynomials.

Source references and common attribution are retained in
`DLMF.Combinatorics.Permutations`.
-/

@[expose] public section

noncomputable section

open Finset Equiv

open Polynomial hiding bernoulli

namespace DLMF.Combinatorics

/-! ### §26.15 Matrix notation -/

/-- (26.15.1): the matrix of the example permutation `35247816`: a `1` in row `j`, column
`σ(j)`. -/
@[dlmf 26.15.E1]
theorem dlmfExamplePerm_permMatrix :
    dlmfExamplePerm.permMatrix ℤ = !![0, 0, 1, 0, 0, 0, 0, 0; 0, 0, 0, 0, 1, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 1, 0;
      0, 0, 0, 0, 0, 0, 0, 1; 1, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 1, 0, 0] := by
  decide +kernel

/-- (26.15.2): `inv(σ) = ∑ a_{gh} a_{kℓ}` over `1 ≤ g < k ≤ n`, `n ≥ h > ℓ ≥ 1`, where
`(a_{gh})` is the permutation matrix of `σ`. -/
@[dlmf 26.15.E2]
theorem inversionNumber_eq_sum_permMatrix {n : ℕ} (σ : Perm (Fin n)) :
    (inversionNumber σ : ℤ) = ∑ g : Fin n, ∑ k : Fin n, ∑ h : Fin n, ∑ l : Fin n,
      if g < k ∧ l < h then σ.permMatrix ℤ g h * σ.permMatrix ℤ k l else 0 := by
  have hP : ∀ i j, σ.permMatrix ℤ i j = if σ i = j then 1 else 0 := by
    intro i j
    simp [Perm.permMatrix, PEquiv.toMatrix_apply]
  simp_rw [hP]
  have : ∀ g k : Fin n, (∑ h : Fin n, ∑ l : Fin n,
      if g < k ∧ l < h then (if σ g = h then (1 : ℤ) else 0) * (if σ k = l then 1 else 0) else 0) =
      if g < k ∧ σ k < σ g then 1 else 0 := by
    intro g k
    rw [Finset.sum_eq_single (σ g)]
    · rw [Finset.sum_eq_single (σ k)]
      · simp
      · intro l _ hl; simp [Ne.symm hl]
      · simp
    · intro h _ hh
      refine sum_eq_zero fun l _ => ?_
      simp [Ne.symm hh]
    · simp
  simp_rw [this]
  rw [inversionNumber, wordInversions, Finset.card_filter, ← Finset.univ_product_univ,
    Finset.sum_product]
  push_cast
  simp only [Fin.val_fin_lt]

/-- A set of squares of the `n × n` board is nonattacking if no two share a row or a column. -/
def IsNonattacking {n : ℕ} (C : Finset (Fin n × Fin n)) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, x ≠ y → x.1 ≠ y.1 ∧ x.2 ≠ y.2

/-- The nonattacking condition on a finite rook placement is decidable. -/
instance {n : ℕ} (C : Finset (Fin n × Fin n)) : Decidable (IsNonattacking C) := by
  unfold IsNonattacking; infer_instance

/-- `r_j(B)`: the number of ways of placing `j` nonattacking rooks on the squares of `B`
(`r_0(B) = 1`) (DLMF §26.15). -/
@[dlmf 26.15]
def rookNumber {n : ℕ} (B : Finset (Fin n × Fin n)) (j : ℕ) : ℕ :=
  #{C ∈ B.powerset | C.card = j ∧ IsNonattacking C}

/-- (26.15.3): the rook polynomial `R(x, B) = ∑_{j=0}^n r_j(B) x^j`. -/
@[dlmf 26.15.E3]
def rookPolynomial {n : ℕ} (B : Finset (Fin n × Fin n)) : ℤ[X] :=
  ∑ j ∈ range (n + 1), C (rookNumber B j : ℤ) * X ^ j

/-- `N_k(B)`: the number of `σ ∈ 𝔖_n` for which exactly `k` of the pairs `(j, σ(j))` lie in
`B` (DLMF §26.15). -/
@[dlmf 26.15]
def hitNumber {n : ℕ} (B : Finset (Fin n × Fin n)) (k : ℕ) : ℕ :=
  #{σ : Perm (Fin n) | #{j : Fin n | (j, σ j) ∈ B} = k}

/-- (26.15.6): `N(x, B) = ∑_{k=0}^n N_k(B) x^k`. -/
@[dlmf 26.15.E6]
def hitPolynomial {n : ℕ} (B : Finset (Fin n × Fin n)) : ℤ[X] :=
  ∑ k ∈ range (n + 1), C (hitNumber B k : ℤ) * X ^ k

/-- The diagonal board `{(1,1), …, (n,n)}`. -/
def diagonalBoard (n : ℕ) : Finset (Fin n × Fin n) := univ.image fun i => (i, i)

/-- §26.15: the derangements are the permutations avoiding the diagonal board,
`N_0(diag) = d(n)`. -/
@[dlmf 26.15]
theorem hitNumber_diagonalBoard_zero (n : ℕ) :
    hitNumber (diagonalBoard n) 0 = numDerangements n := by
  have key : ∀ σ : Perm (Fin n),
      #{j : Fin n | (j, σ j) ∈ diagonalBoard n} = 0 ↔ σ ∈ derangements (Fin n) := by
    intro σ
    have hmem : ∀ x : Fin n, (x, σ x) ∈ diagonalBoard n ↔ σ x = x := by
      intro x
      simp only [diagonalBoard, mem_image, mem_univ, true_and, Prod.mk.injEq]
      constructor
      · rintro ⟨a, rfl, h⟩; exact h.symm
      · intro h; exact ⟨x, rfl, h.symm⟩
    change _ ↔ ∀ x, σ x ≠ x
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    simp only [mem_univ, true_implies, hmem]
  unfold hitNumber
  rw [← Fintype.card_fin n, ← card_derangements_eq_numDerangements (Fin n), Fintype.card_fin,
    Fintype.card_subtype]
  congr 1
  ext σ
  simp only [mem_filter, mem_univ, true_and]
  exact key σ

/-- §26.15: for the derangement board, `r_j(B) = C(n, j)`. -/
@[dlmf 26.15]
theorem rookNumber_diagonalBoard (n j : ℕ) : rookNumber (diagonalBoard n) j = n.choose j := by
  have hcard : (diagonalBoard n).card = n := by
    rw [diagonalBoard, Finset.card_image_of_injective _ (fun a b h => by simpa using h)]
    simp
  unfold rookNumber
  rw [show n.choose j = (diagonalBoard n).card.choose j by rw [hcard], ← Finset.card_powersetCard,
    Finset.powersetCard_eq_filter]
  congr 1
  refine Finset.filter_congr fun C hC => ?_
  rw [mem_powerset] at hC
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  intro x hx y hy hxy
  obtain ⟨a, -, rfl⟩ := mem_image.mp (hC hx)
  obtain ⟨b, -, rfl⟩ := mem_image.mp (hC hy)
  have hab : a ≠ b := fun h => hxy (h ▸ rfl)
  exact ⟨hab, hab⟩

/-- A nonattacking placement has at most `n` rooks. -/
lemma q26b_card_le_of_nonattacking {n : ℕ} {C : Finset (Fin n × Fin n)} (hC : IsNonattacking C) :
    #C ≤ n := by
  have : #(C.image Prod.fst) = #C := card_image_of_injOn fun x hx y hy h => by
    by_contra hne; exact (hC x hx y hy hne).1 h
  rw [← this]
  exact (card_le_univ _).trans (by simp)

/-- The rook polynomial as a sum over nonattacking placements. -/
lemma q26b_rookPolynomial_eq_sum {n : ℕ} (B : Finset (Fin n × Fin n)) :
    rookPolynomial B = ∑ D ∈ B.powerset.filter IsNonattacking, (X : ℤ[X]) ^ #D := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun D => #D) (t := range (n + 1))
    (fun D hD => by
      simp only [mem_filter] at hD
      rw [mem_range]; exact Nat.lt_succ_of_le (q26b_card_le_of_nonattacking hD.2))]
  refine sum_congr rfl fun k _ => ?_
  rw [Finset.sum_congr rfl (fun D hD => by rw [(mem_filter.mp hD).2]), sum_const, nsmul_eq_mul,
    rookNumber, Finset.filter_filter]
  simp only [map_natCast]
  congr 3
  exact Finset.filter_congr fun D _ => and_comm

/-- (26.15.4): if no square of `B₁` shares a row or column with a square of `B₂`, then
`R(x, B₁ ∪ B₂) = R(x, B₁) R(x, B₂)`. -/
@[dlmf 26.15.E4]
theorem rookPolynomial_union {n : ℕ} {B₁ B₂ : Finset (Fin n × Fin n)}
    (h : ∀ x ∈ B₁, ∀ y ∈ B₂, x.1 ≠ y.1 ∧ x.2 ≠ y.2) :
    rookPolynomial (B₁ ∪ B₂) = rookPolynomial B₁ * rookPolynomial B₂ := by
  classical
  have hdisj : Disjoint B₁ B₂ := by
    rw [Finset.disjoint_left]
    intro x hx hx2
    exact (h x hx x hx2).1 rfl
  simp only [q26b_rookPolynomial_eq_sum]
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  symm
  refine Finset.sum_bij (fun p _ => p.1 ∪ p.2) ?_ ?_ ?_ ?_
  · rintro ⟨C₁, C₂⟩ hp
    simp only [mem_product, mem_filter, mem_powerset] at hp ⊢
    refine ⟨union_subset_union hp.1.1 hp.2.1, ?_⟩
    intro x hx y hy hxy
    rcases mem_union.mp hx with hx | hx <;> rcases mem_union.mp hy with hy | hy
    · exact hp.1.2 x hx y hy hxy
    · exact h x (hp.1.1 hx) y (hp.2.1 hy)
    · have := h y (hp.1.1 hy) x (hp.2.1 hx); exact ⟨this.1.symm, this.2.symm⟩
    · exact hp.2.2 x hx y hy hxy
  · rintro ⟨C₁, C₂⟩ hp ⟨D₁, D₂⟩ hq hCD
    simp only [mem_product, mem_filter, mem_powerset] at hp hq
    simp only at hCD
    have key : ∀ (E₁ E₂ : Finset (Fin n × Fin n)), E₁ ⊆ B₁ → E₂ ⊆ B₂ →
        (E₁ ∪ E₂).filter (· ∈ B₁) = E₁ ∧ (E₁ ∪ E₂).filter (· ∈ B₂) = E₂ := by
      intro E₁ E₂ h1 h2
      constructor
      · ext x
        simp only [mem_filter, mem_union]
        constructor
        · rintro ⟨hx | hx, hb⟩
          · exact hx
          · exact absurd hb (Finset.disjoint_right.mp hdisj (h2 hx))
        · intro hx; exact ⟨Or.inl hx, h1 hx⟩
      · ext x
        simp only [mem_filter, mem_union]
        constructor
        · rintro ⟨hx | hx, hb⟩
          · exact absurd hb (Finset.disjoint_left.mp hdisj (h1 hx))
          · exact hx
        · intro hx; exact ⟨Or.inr hx, h2 hx⟩
    obtain ⟨h1, h2⟩ := key C₁ C₂ hp.1.1 hp.2.1
    obtain ⟨h3, h4⟩ := key D₁ D₂ hq.1.1 hq.2.1
    rw [hCD] at h1 h2
    exact Prod.ext (h1.symm.trans h3) (h2.symm.trans h4)
  · intro C hC
    simp only [mem_filter, mem_powerset] at hC
    refine ⟨(C.filter (· ∈ B₁), C.filter (· ∈ B₂)), ?_, ?_⟩
    · simp only [mem_product, mem_filter, mem_powerset]
      refine ⟨⟨fun x hx => (mem_filter.mp hx).2, fun x hx y hy => hC.2 x (mem_filter.mp hx).1 y
        (mem_filter.mp hy).1⟩, fun x hx => (mem_filter.mp hx).2, fun x hx y hy => hC.2 x
        (mem_filter.mp hx).1 y (mem_filter.mp hy).1⟩
    · ext x
      simp only [mem_union, mem_filter]
      constructor
      · rintro (⟨hx, -⟩ | ⟨hx, -⟩) <;> exact hx
      · intro hx
        rcases mem_union.mp (hC.1 hx) with hb | hb
        · exact Or.inl ⟨hx, hb⟩
        · exact Or.inr ⟨hx, hb⟩
  · rintro ⟨C₁, C₂⟩ hp
    simp only [mem_product, mem_filter, mem_powerset] at hp
    rw [card_union_of_disjoint (Finset.disjoint_of_subset_left hp.1.1
      (Finset.disjoint_of_subset_right hp.2.1 hdisj)), pow_add]

/-- (26.15.5): for `(j, k) ∈ B`, `R(x, B) = x R(x, B∖[j,k]) + R(x, B∖(j,k))`, where `B∖[j,k]`
removes row `j` and column `k` and `B∖(j,k)` removes the square `(j, k)`. -/
@[dlmf 26.15.E5]
theorem rookPolynomial_delete {n : ℕ} {B : Finset (Fin n × Fin n)} {j k : Fin n}
    (hjk : (j, k) ∈ B) :
    rookPolynomial B =
      X * rookPolynomial (B.filter fun x => x.1 ≠ j ∧ x.2 ≠ k) +
        rookPolynomial (B.erase (j, k)) := by
  classical
  simp only [q26b_rookPolynomial_eq_sum]
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun D => (j, k) ∈ D)]
  congr 1
  · rw [Finset.mul_sum]
    symm
    refine Finset.sum_bij (fun D _ => insert (j, k) D) ?_ ?_ ?_ ?_
    · intro D hD
      simp only [mem_filter, mem_powerset] at hD ⊢
      refine ⟨⟨insert_subset hjk (hD.1.trans (filter_subset _ _)), ?_⟩, mem_insert_self _ _⟩
      intro x hx y hy hxy
      have hrc : ∀ z ∈ D, z.1 ≠ j ∧ z.2 ≠ k := fun z hz => (mem_filter.mp (hD.1 hz)).2
      rcases mem_insert.mp hx with rfl | hx <;> rcases mem_insert.mp hy with rfl | hy
      · exact absurd rfl hxy
      · have := hrc y hy; exact ⟨this.1.symm, this.2.symm⟩
      · exact hrc x hx
      · exact hD.2 x hx y hy hxy
    · intro D hD D' hD' h
      simp only [mem_filter, mem_powerset] at hD hD'
      have hn : ∀ E : Finset (Fin n × Fin n), E ⊆ B.filter (fun x => x.1 ≠ j ∧ x.2 ≠ k) →
          (j, k) ∉ E := fun E hE hm => by simpa using (mem_filter.mp (hE hm)).2
      rw [← erase_insert (hn D hD.1), h, erase_insert (hn D' hD'.1)]
    · intro D hD
      simp only [mem_filter, mem_powerset] at hD
      refine ⟨D.erase (j, k), ?_, insert_erase hD.2⟩
      simp only [mem_filter, mem_powerset]
      refine ⟨fun x hx => ?_, fun x hx y hy hxy =>
        hD.1.2 x (mem_of_mem_erase hx) y (mem_of_mem_erase hy) hxy⟩
      rw [mem_filter]
      refine ⟨hD.1.1 (mem_of_mem_erase hx), ?_⟩
      have h1 := hD.1.2 x (mem_of_mem_erase hx) (j, k) hD.2 (ne_of_mem_erase hx)
      exact h1
    · intro D hD
      simp only [mem_filter, mem_powerset] at hD
      have : (j, k) ∉ D := fun hm => by simpa using (mem_filter.mp (hD.1 hm)).2
      rw [card_insert_of_notMem this, pow_succ, mul_comm]
  · rw [Finset.filter_filter]
    refine sum_congr ?_ fun _ _ => rfl
    ext D
    simp only [mem_filter, mem_powerset]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨fun x hx => mem_erase.mpr ⟨fun h => h3 (h ▸ hx), h1 hx⟩, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1.trans (erase_subset _ _), h2, fun h => (mem_erase.mp (h1 h)).1 rfl⟩

/-- The number of permutations of `Fin n` fixing every point of `R` is `(n - #R)!`. -/
lemma q26b_card_perm_fix {n : ℕ} (R : Finset (Fin n)) :
    #{τ : Perm (Fin n) | ∀ r ∈ R, τ r = r} = (n - #R).factorial := by
  classical
  rw [← Fintype.card_subtype]
  have e := Perm.subtypeEquivSubtypePerm (fun a : Fin n => a ∉ R)
  rw [← Fintype.card_congr (e.trans (Equiv.subtypeEquivRight fun τ => by simp))]
  rw [Fintype.card_perm, Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe]

/-- The number of permutations containing a nonattacking placement `C` is `(n - #C)!`. -/
lemma q26b_card_perm_extend {n : ℕ} {C : Finset (Fin n × Fin n)} (hC : IsNonattacking C) :
    #{σ : Perm (Fin n) | ∀ x ∈ C, σ x.1 = x.2} = (n - #C).factorial := by
  classical
  have hinj1 : Function.Injective fun x : C => x.1.1 := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ h
    by_contra hne
    exact (hC x hx y hy fun h' => hne (Subtype.ext h')).1 h
  have hinj2 : Function.Injective fun x : C => x.1.2 := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ h
    by_contra hne
    exact (hC x hx y hy fun h' => hne (Subtype.ext h')).2 h
  obtain ⟨σ0, hσ0⟩ := q26b_exists_perm_comp_of_injective hinj1 hinj2
  have hσ0' : ∀ x ∈ C, σ0 x.1 = x.2 := fun x hx => (congrFun hσ0 ⟨x, hx⟩).symm
  have hR : #(C.image Prod.fst) = #C := card_image_of_injOn fun x hx y hy h => by
    by_contra hne; exact (hC x hx y hy hne).1 h
  rw [← hR, ← q26b_card_perm_fix]
  refine Finset.card_bij (fun σ _ => σ0⁻¹ * σ) ?_ ?_ ?_
  · intro σ hσ
    simp only [mem_filter, mem_univ, true_and] at hσ ⊢
    intro r hr
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hr
    rw [Perm.mul_apply, hσ x hx, ← hσ0' x hx]; simp
  · intro σ _ τ _ h; exact mul_left_cancel h
  · intro τ hτ
    simp only [mem_filter, mem_univ, true_and] at hτ
    refine ⟨σ0 * τ, ?_, by rw [← mul_assoc, inv_mul_cancel, one_mul]⟩
    simp only [mem_filter, mem_univ, true_and]
    intro x hx
    rw [Perm.mul_apply, hτ x.1 (mem_image_of_mem _ hx), hσ0' x hx]

/-- (26.15.7): `N(x, B) = ∑_{k=0}^n r_k(B) (n-k)! (x-1)^k`. -/
@[dlmf 26.15.E7]
theorem hitPolynomial_eq {n : ℕ} (B : Finset (Fin n × Fin n)) :
    hitPolynomial B =
      ∑ k ∈ range (n + 1), C ((rookNumber B k * (n - k).factorial : ℕ) : ℤ) * (X - 1) ^ k := by
  classical
  set NA := B.powerset.filter IsNonattacking with hNA
  set J : Perm (Fin n) → Finset (Fin n) := fun σ => univ.filter fun j => (j, σ j) ∈ B
  -- Step 1
  have h1 : hitPolynomial B = ∑ σ : Perm (Fin n), (X : ℤ[X]) ^ #(J σ) := by
    rw [hitPolynomial, ← Finset.sum_fiberwise_of_maps_to (g := fun σ => #(J σ))
      (t := range (n + 1)) (s := univ) (fun σ _ => by
        rw [mem_range]; exact Nat.lt_succ_of_le ((card_le_univ _).trans (by simp)))]
    refine sum_congr rfl fun k _ => ?_
    rw [Finset.sum_congr rfl (fun σ hσ => by rw [(mem_filter.mp hσ).2]), sum_const,
      nsmul_eq_mul, hitNumber]
    simp only [map_natCast]
    rfl
  -- Step 2
  have h2 : ∀ σ : Perm (Fin n), (X : ℤ[X]) ^ #(J σ) =
      ∑ D ∈ NA.filter (fun D => ∀ x ∈ D, σ x.1 = x.2), (X - 1) ^ #D := by
    intro σ
    have hX : (X : ℤ[X]) ^ #(J σ) = ∏ _j ∈ J σ, ((X - 1) + 1) := by
      rw [prod_const, sub_add_cancel]
    rw [hX, prod_add_one]
    simp only [prod_const]
    refine Finset.sum_bij (fun T _ => T.image fun j => (j, σ j)) ?_ ?_ ?_ ?_
    · intro T hT
      rw [mem_powerset] at hT
      simp only [mem_filter, hNA, mem_powerset]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro x hx
        obtain ⟨j, hj, rfl⟩ := mem_image.mp hx
        exact (mem_filter.mp (hT hj)).2
      · intro x hx y hy hxy
        obtain ⟨i, -, rfl⟩ := mem_image.mp hx
        obtain ⟨j, -, rfl⟩ := mem_image.mp hy
        have hij : i ≠ j := fun h => hxy (h ▸ rfl)
        exact ⟨hij, fun h => hij (σ.injective h)⟩
      · intro x hx
        obtain ⟨j, -, rfl⟩ := mem_image.mp hx
        rfl
    · intro T _ T' _ h
      have := congrArg (Finset.image Prod.fst) h
      simpa [Finset.image_image, Function.comp_def] using this
    · intro D hD
      simp only [mem_filter, hNA, mem_powerset] at hD
      refine ⟨D.image Prod.fst, ?_, ?_⟩
      · rw [mem_powerset]
        intro j hj
        obtain ⟨x, hx, rfl⟩ := mem_image.mp hj
        simp only [J, mem_filter, mem_univ, true_and]
        rw [hD.2 x hx]
        exact hD.1.1 hx
      · ext x
        simp only [mem_image, Prod.exists, exists_and_right, exists_eq_right]
        constructor
        · rintro ⟨j, ⟨k, hjk⟩, rfl⟩
          rw [hD.2 _ hjk]; exact hjk
        · intro hx
          exact ⟨x.1, ⟨x.2, hx⟩, by rw [hD.2 x hx]⟩
    · intro T _
      rw [card_image_of_injective _ (fun i j h => by simpa using congrArg Prod.fst h)]
  -- Step 3
  have h3 : ∑ σ : Perm (Fin n), (X : ℤ[X]) ^ #(J σ) =
      ∑ D ∈ NA, C (((n - #D).factorial : ℕ) : ℤ) * (X - 1) ^ #D := by
    simp_rw [h2, Finset.sum_filter]
    rw [Finset.sum_comm]
    refine sum_congr rfl fun D hD => ?_
    rw [← Finset.sum_filter, sum_const, nsmul_eq_mul]
    simp only [mem_filter, hNA, mem_powerset] at hD
    rw [q26b_card_perm_extend hD.2]
    simp
  -- Step 4
  rw [h1, h3, ← Finset.sum_fiberwise_of_maps_to (g := fun D => #D) (t := range (n + 1))
    (fun D hD => by
      simp only [hNA, mem_filter] at hD
      rw [mem_range]; exact Nat.lt_succ_of_le (q26b_card_le_of_nonattacking hD.2))]
  refine sum_congr rfl fun k _ => ?_
  rw [Finset.sum_congr rfl (fun D hD => by rw [(mem_filter.mp hD).2]), sum_const, nsmul_eq_mul]
  have hr : #(NA.filter fun D => #D = k) = rookNumber B k := by
    rw [rookNumber, hNA, Finset.filter_filter]
    congr 1
    ext D; simp only [mem_filter]; tauto
  rw [hr]
  simp only [Nat.cast_mul, map_mul, map_natCast]
  ring

/-- (26.15.8): the number of permutations avoiding `B` is
`N_0(B) = N(0, B) = ∑_{k=0}^n (-1)^k r_k(B) (n-k)!`. -/
@[dlmf 26.15.E8]
theorem hitNumber_zero_eq {n : ℕ} (B : Finset (Fin n × Fin n)) :
    (hitNumber B 0 : ℤ) = (hitPolynomial B).eval 0 ∧
      (hitNumber B 0 : ℤ) =
        ∑ k ∈ range (n + 1), (-1 : ℤ) ^ k * rookNumber B k * (n - k).factorial := by
  have h0 : (hitPolynomial B).eval 0 = hitNumber B 0 := by
    simp only [hitPolynomial, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
    rw [Finset.sum_eq_single 0]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; simp at h
  refine ⟨h0.symm, ?_⟩
  rw [← h0, hitPolynomial_eq]
  simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_sub, eval_X, eval_one, zero_sub]
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast; ring

/-- The ménage board `{(j, j), (j, j+1) | 1 ≤ j < n} ∪ {(n, n), (n, 1)}` (indices mod `n`). -/
def menageBoard (n : ℕ) [NeZero n] : Finset (Fin n × Fin n) :=
  univ.image (fun i => (i, i)) ∪ univ.image (fun i => (i, i + 1))

end DLMF.Combinatorics
end
end
