/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Bialternant

/-!
# MacMahon box formula for plane partitions

Array encodings, counting bijections and the finite-box product formula for plane partitions.

Source references and common attribution are retained in
`DLMF.Combinatorics.PlanePartitions`.
-/

@[expose] public section

noncomputable section

open Finset Filter Asymptotics

namespace DLMF.Combinatorics

/-- (26.12.3): the box `B(r, s, t) = {(h, j, k) | 1 ≤ h ≤ r, 1 ≤ j ≤ s, 1 ≤ k ≤ t}`. -/
@[dlmf 26.12.E3]
def planeBox (r s t : ℕ) : Finset (ℕ × ℕ × ℕ) := Icc 1 r ×ˢ Icc 1 s ×ˢ Icc 1 t

/-- A plane partition (DLMF §26.12(i), second definition): a finite set of points of
`ℕ × ℕ × ℕ` with positive coordinates such that `(r, s, t) ∈ π` and
`(1, 1, 1) ≤ (h, j, k) ≤ (r, s, t)` imply `(h, j, k) ∈ π`. -/
@[dlmf 26.12.i]
def IsPlanePartition (π : Finset (ℕ × ℕ × ℕ)) : Prop :=
  ∀ x ∈ π, 1 ≤ x.1 ∧ 1 ≤ x.2.1 ∧ 1 ≤ x.2.2 ∧ planeBox x.1 x.2.1 x.2.2 ⊆ π

/-- The downward-closure condition defining a finite plane partition is decidable. -/
instance (π : Finset (ℕ × ℕ × ℕ)) : Decidable (IsPlanePartition π) := by
  unfold IsPlanePartition; infer_instance

/-- The plane partitions contained in the box `B(r, s, t)`. -/
def planePartitionsIn (r s t : ℕ) : Finset (Finset (ℕ × ℕ × ℕ)) :=
  (planeBox r s t).powerset.filter IsPlanePartition

/-! ### MacMahon's box formula

Proof of (26.12.4) and (26.12.21) via Jacobi's bialternant formula
`TauCeti.diagramSchurPoly_mul_alternant`: a plane partition in `B(r, s, t)` is a semistandard
tableau of the rectangular shape `r × t` in the alphabet `{0, …, r + s - 1}` (the column heights in
the `j` direction, shifted by the row index), and the Schur polynomial at `xₖ = Xᵏ` is a quotient
of two Vandermonde products. -/

section MacMahonBox

open Polynomial

/-- The rectangular Young diagram with `r` rows of length `t`. -/
def s26b_rect (r t : ℕ) : YoungDiagram where
  cells := range r ×ˢ range t
  isLowerSet := by
    intro a b hba ha
    simp only [coe_product, coe_range, Set.mem_prod, Set.mem_Iio] at ha ⊢
    exact ⟨lt_of_le_of_lt hba.1 ha.1, lt_of_le_of_lt hba.2 ha.2⟩

/-- Membership in the rectangle. -/
lemma s26b_mem_rect {r t i c : ℕ} : (i, c) ∈ s26b_rect r t ↔ i < r ∧ c < t := by
  change (i, c) ∈ range r ×ˢ range t ↔ _
  simp

/-- Membership in `planePartitionsIn`. -/
lemma s26b_mem_planePartitionsIn {r s t : ℕ} {π : Finset (ℕ × ℕ × ℕ)} :
    π ∈ planePartitionsIn r s t ↔ π ⊆ planeBox r s t ∧ IsPlanePartition π := by
  simp [planePartitionsIn]

/-- Membership in `planeBox`. -/
lemma s26b_mem_planeBox {r s t h j k : ℕ} :
    (h, j, k) ∈ planeBox r s t ↔ 1 ≤ h ∧ h ≤ r ∧ 1 ≤ j ∧ j ≤ s ∧ 1 ≤ k ∧ k ≤ t := by
  simp [planeBox, and_assoc]

/-- Down-closure of a plane partition. -/
lemma s26b_down {π : Finset (ℕ × ℕ × ℕ)} (hπ : IsPlanePartition π) {h j k h' j' k' : ℕ}
    (hx : (h, j, k) ∈ π) (h1 : 1 ≤ h') (h2 : h' ≤ h) (j1 : 1 ≤ j') (j2 : j' ≤ j) (k1 : 1 ≤ k')
    (k2 : k' ≤ k) : (h', j', k') ∈ π :=
  (hπ _ hx).2.2.2 (s26b_mem_planeBox.mpr ⟨h1, h2, j1, j2, k1, k2⟩)

/-- The column of heights over `(h, k)`. -/
def s26b_fiber (π : Finset (ℕ × ℕ × ℕ)) (s h k : ℕ) : Finset ℕ :=
  (Icc 1 s).filter fun j => (h, j, k) ∈ π

/-- The column over `(h, k)` of a plane partition is an initial segment `[1, m]`. -/
lemma s26b_mem_iff_le_card {π : Finset (ℕ × ℕ × ℕ)} (hπ : IsPlanePartition π) {s h j k : ℕ}
    (hj1 : 1 ≤ j) (hjs : j ≤ s) : (h, j, k) ∈ π ↔ j ≤ #(s26b_fiber π s h k) := by
  constructor
  · intro hx
    have : Icc 1 j ⊆ s26b_fiber π s h k := by
      intro j' hj'
      rw [mem_Icc] at hj'
      have := hπ _ hx
      simp only [s26b_fiber, mem_filter, mem_Icc]
      exact ⟨⟨hj'.1, hj'.2.trans hjs⟩,
        s26b_down hπ hx this.1 le_rfl hj'.1 hj'.2 this.2.2.1 le_rfl⟩
    simpa using card_le_card this
  · intro hle
    by_contra hx
    have : s26b_fiber π s h k ⊆ Icc 1 (j - 1) := by
      intro j' hj'
      simp only [s26b_fiber, mem_filter, mem_Icc] at hj' ⊢
      refine ⟨hj'.1.1, ?_⟩
      by_contra hlt
      exact hx (s26b_down hπ hj'.2 (hπ _ hj'.2).1 le_rfl hj1 (by omega) (hπ _ hj'.2).2.2.1
        le_rfl)
    have := card_le_card this
    simp at this; omega

/-- A column of a plane partition in `B(r, s, t)` has height at most `s`. -/
lemma s26b_card_fiber_le (π : Finset (ℕ × ℕ × ℕ)) (s h k : ℕ) :
    #(s26b_fiber π s h k) ≤ s := by
  simpa [s26b_fiber] using card_le_card (filter_subset (fun j => (h, j, k) ∈ π) (Icc 1 s))

/-- Column heights of a plane partition are antitone. -/
lemma s26b_fiber_mono {π : Finset (ℕ × ℕ × ℕ)} (hπ : IsPlanePartition π) {s h k h' k' : ℕ}
    (h1 : 1 ≤ h') (h2 : h' ≤ h) (k1 : 1 ≤ k') (k2 : k' ≤ k) :
    #(s26b_fiber π s h k) ≤ #(s26b_fiber π s h' k') := by
  refine card_le_card fun j hj => ?_
  simp only [s26b_fiber, mem_filter] at hj ⊢
  exact ⟨hj.1, s26b_down hπ hj.2 h1 h2 (mem_Icc.mp hj.1).1 le_rfl k1 k2⟩

/-- Entries of a semistandard tableau grow by at least one per row down a column. -/
lemma s26b_col_add {μ : YoungDiagram} (T : SemistandardYoungTableau μ) {i i' c : ℕ}
    (hii : i ≤ i') (hc : (i', c) ∈ μ) : T i c + (i' - i) ≤ T i' c := by
  induction i', hii using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    have hm' : (m, c) ∈ μ := μ.up_left_mem (Nat.le_succ m) le_rfl hc
    have := T.col_strict (i1 := m) (i2 := m + 1) (Nat.lt_succ_self m) hc
    have := ih hm'
    omega

/-- The tableau of a plane partition. -/
def s26b_toT (r s t : ℕ) (π : Finset (ℕ × ℕ × ℕ)) (hπ : IsPlanePartition π) :
    SemistandardYoungTableau (s26b_rect r t) where
  entry i c := if i < r ∧ c < t then #(s26b_fiber π s (r - i) (t - c)) + i else 0
  row_weak' := by
    intro i c1 c2 hc hcell
    rw [s26b_mem_rect] at hcell
    have e1 : i < r ∧ c1 < t := ⟨hcell.1, by omega⟩
    simp only [e1, hcell, and_self, ↓reduceIte]
    have := s26b_fiber_mono (s := s) hπ (h := r - i) (h' := r - i) (k := t - c1) (k' := t - c2)
      (by omega) le_rfl (by omega) (by omega)
    omega
  col_strict' := by
    intro i1 i2 c hi hcell
    rw [s26b_mem_rect] at hcell
    have e1 : i1 < r ∧ c < t := ⟨by omega, hcell.2⟩
    simp only [e1, hcell, and_self, ↓reduceIte]
    have := s26b_fiber_mono (s := s) hπ (h := r - i1) (h' := r - i2) (k := t - c) (k' := t - c)
      (by omega) (by omega) (by omega) le_rfl
    omega
  zeros' := by
    intro i c hc
    rw [s26b_mem_rect] at hc
    simp only [hc, ↓reduceIte]

/-- The entries of `s26b_toT`. -/
lemma s26b_toT_apply (r s t : ℕ) (π : Finset (ℕ × ℕ × ℕ)) (hπ : IsPlanePartition π) (i c : ℕ) :
    s26b_toT r s t π hπ i c = if i < r ∧ c < t then #(s26b_fiber π s (r - i) (t - c)) + i else 0 :=
  rfl

/-- The plane partition of a tableau. -/
def s26b_ofT (r s t : ℕ) (T : SemistandardYoungTableau (s26b_rect r t)) : Finset (ℕ × ℕ × ℕ) :=
  (planeBox r s t).filter fun x => x.2.1 + (r - x.1) ≤ T (r - x.1) (t - x.2.2)

/-- `s26b_ofT` produces a plane partition in the box. -/
lemma s26b_ofT_mem (r s t : ℕ) (T : SemistandardYoungTableau (s26b_rect r t)) :
    s26b_ofT r s t T ∈ planePartitionsIn r s t := by
  rw [s26b_mem_planePartitionsIn]
  refine ⟨filter_subset _ _, ?_⟩
  rintro ⟨h, j, k⟩ hx
  simp only [s26b_ofT, mem_filter, s26b_mem_planeBox] at hx
  obtain ⟨⟨h1, h2, j1, j2, k1, k2⟩, hle⟩ := hx
  refine ⟨h1, j1, k1, ?_⟩
  rintro ⟨h', j', k'⟩ hy
  simp only [s26b_mem_planeBox] at hy
  simp only [s26b_ofT, mem_filter, s26b_mem_planeBox]
  refine ⟨⟨hy.1, by omega, hy.2.2.1, by omega, hy.2.2.2.2.1, by omega⟩, ?_⟩
  have hrow := T.row_weak (i := r - h) (j1 := t - k) (j2 := t - k')
  have hcol := s26b_col_add T (i := r - h) (i' := r - h') (c := t - k') (by omega)
    (s26b_mem_rect.mpr ⟨by omega, by omega⟩)
  rcases Nat.lt_or_ge (t - k) (t - k') with hlt | hge
  · have := hrow hlt (s26b_mem_rect.mpr ⟨by omega, by omega⟩)
    omega
  · have : t - k = t - k' := by omega
    rw [this] at hle
    omega

/-- `s26b_ofT` inverts `s26b_toT`. -/
lemma s26b_ofT_toT {r s t : ℕ} {π : Finset (ℕ × ℕ × ℕ)} (hπ' : π ∈ planePartitionsIn r s t) :
    s26b_ofT r s t (s26b_toT r s t π (s26b_mem_planePartitionsIn.mp hπ').2) = π := by
  obtain ⟨hsub, hπ⟩ := s26b_mem_planePartitionsIn.mp hπ'
  ext ⟨h, j, k⟩
  rw [s26b_ofT, mem_filter]
  simp only [s26b_toT_apply]
  constructor
  · rintro ⟨hb, hle⟩
    rw [s26b_mem_planeBox] at hb
    have e1 : r - h < r ∧ t - k < t := ⟨by omega, by omega⟩
    simp only [e1, and_self, ↓reduceIte] at hle
    rw [show r - (r - h) = h by omega, show t - (t - k) = k by omega] at hle
    exact (s26b_mem_iff_le_card hπ (s := s) (by omega) (by omega)).mpr (by omega)
  · intro hx
    have hb := hsub hx
    refine ⟨hb, ?_⟩
    rw [s26b_mem_planeBox] at hb
    have e1 : r - h < r ∧ t - k < t := ⟨by omega, by omega⟩
    simp only [e1, and_self, ↓reduceIte]
    rw [show r - (r - h) = h by omega, show t - (t - k) = k by omega]
    have := (s26b_mem_iff_le_card hπ (s := s) (by omega) (by omega)).mp hx
    omega

/-- Entry bounds `i ≤ T i c ≤ i + s` for a tableau with entries below `r + s`. -/
lemma s26b_entry_le {r s t : ℕ} (T : SemistandardYoungTableau (s26b_rect r t))
    (hT : ∀ i c, (i, c) ∈ s26b_rect r t → T i c < r + s) {i c : ℕ}
    (hc : (i, c) ∈ s26b_rect r t) : i ≤ T i c ∧ T i c ≤ i + s := by
  have hc' := s26b_mem_rect.mp hc
  refine ⟨SemistandardYoungTableau.le_entry T hc, ?_⟩
  have h1 := s26b_col_add T (i := i) (i' := r - 1) (c := c) (by omega)
    (s26b_mem_rect.mpr ⟨by omega, hc'.2⟩)
  have h2 := hT (r - 1) c (s26b_mem_rect.mpr ⟨by omega, hc'.2⟩)
  omega

/-- `s26b_toT` inverts `s26b_ofT` on bounded tableaux. -/
lemma s26b_toT_ofT {r s t : ℕ} (T : SemistandardYoungTableau (s26b_rect r t))
    (hT : ∀ i c, (i, c) ∈ s26b_rect r t → T i c < r + s) :
    s26b_toT r s t (s26b_ofT r s t T)
      (s26b_mem_planePartitionsIn.mp (s26b_ofT_mem r s t T)).2 = T := by
  ext i c
  rw [s26b_toT_apply]
  split_ifs with hc
  · have hc' := s26b_mem_rect.mpr hc
    obtain ⟨hle1, hle2⟩ := s26b_entry_le T hT hc'
    have hf : s26b_fiber (s26b_ofT r s t T) s (r - i) (t - c) = Icc 1 (T i c - i) := by
      ext j
      simp only [s26b_fiber, s26b_ofT, mem_filter, mem_Icc, s26b_mem_planeBox]
      rw [show r - (r - i) = i by omega, show t - (t - c) = c by omega]
      constructor
      · rintro ⟨⟨hj1, _⟩, _, hj⟩; exact ⟨hj1, by omega⟩
      · rintro ⟨hj1, hj2⟩
        exact ⟨⟨hj1, by omega⟩, ⟨by omega, by omega, hj1, by omega, by omega, by omega⟩, by omega⟩
    rw [hf, Nat.card_Icc]
    omega
  · exact (T.zeros (fun h => hc (s26b_mem_rect.mp h))).symm

/-- The tableau of a plane partition in `B(r, s, t)` has entries below `r + s`. -/
lemma s26b_toT_lt {r s t : ℕ} {π : Finset (ℕ × ℕ × ℕ)} (hπ : IsPlanePartition π) :
    ∀ i c, (i, c) ∈ s26b_rect r t → s26b_toT r s t π hπ i c < r + s := by
  intro i c hc
  rw [s26b_mem_rect] at hc
  rw [s26b_toT_apply]
  simp only [hc, and_self, ↓reduceIte]
  have := s26b_card_fiber_le π s (r - i) (t - c)
  omega

/-- The entry sum of the tableau of a plane partition. -/
lemma s26b_sum_toT {r s t : ℕ} {π : Finset (ℕ × ℕ × ℕ)} (hπ' : π ∈ planePartitionsIn r s t) :
    ∑ x ∈ (s26b_rect r t).cells,
        s26b_toT r s t π (s26b_mem_planePartitionsIn.mp hπ').2 x.1 x.2 =
      #π + t * ∑ i ∈ range r, i := by
  obtain ⟨hsub, hπ⟩ := s26b_mem_planePartitionsIn.mp hπ'
  have hcells : (s26b_rect r t).cells = range r ×ˢ range t := rfl
  rw [hcells, sum_product]
  have h1 : ∀ i ∈ range r, ∑ c ∈ range t, s26b_toT r s t π hπ i c =
      ∑ c ∈ range t, #(s26b_fiber π s (r - i) (t - c)) + t * i := by
    intro i hi
    rw [mem_range] at hi
    rw [show t * i = ∑ c ∈ range t, i by simp, ← sum_add_distrib]
    refine sum_congr rfl fun c hc => ?_
    rw [mem_range] at hc
    rw [s26b_toT_apply]
    simp only [hi, hc, and_self, ↓reduceIte]
  rw [sum_congr rfl h1, sum_add_distrib, ← mul_sum]
  congr 1
  -- #π as a sum of fibers
  rw [card_eq_sum_card_fiberwise (f := fun x : ℕ × ℕ × ℕ => (x.1, x.2.2))
    (t := Icc 1 r ×ˢ Icc 1 t)]
  · rw [sum_product]
    refine sum_nbij' (fun i => r - i) (fun h => r - h) ?_ ?_ ?_ ?_ ?_
    · intro i hi; simp at hi ⊢; omega
    · intro h hh; simp at hh ⊢; omega
    · intro i hi; simp at hi; omega
    · intro h hh; simp at hh; omega
    · intro i hi
      simp only [mem_range] at hi
      refine sum_nbij' (fun c => t - c) (fun k => t - k) ?_ ?_ ?_ ?_ ?_
      · intro c hc; simp at hc ⊢; omega
      · intro k hk; simp at hk ⊢; omega
      · intro c hc; simp at hc; omega
      · intro k hk; simp at hk; omega
      · intro c hc
        simp only [mem_range] at hc
        refine card_nbij' (fun j => (r - i, j, t - c)) (fun x => x.2.1) ?_ ?_ ?_ ?_
        · intro j hj
          simp only [s26b_fiber, mem_coe, mem_filter] at hj
          simp [hj.2]
        · rintro ⟨h, j, k⟩ hx
          simp only [mem_coe, mem_filter, Prod.mk.injEq] at hx
          obtain ⟨hx, rfl, rfl⟩ := hx
          have := s26b_mem_planeBox.mp (hsub hx)
          simp only [s26b_fiber, mem_coe, mem_filter, mem_Icc]
          exact ⟨⟨this.2.2.1, this.2.2.2.1⟩, hx⟩
        · intro j _; rfl
        · rintro ⟨h, j, k⟩ hx
          simp only [mem_coe, mem_filter, Prod.mk.injEq] at hx
          obtain ⟨_, rfl, rfl⟩ := hx
          rfl
  · rintro ⟨h, j, k⟩ hx
    have := s26b_mem_planeBox.mp (hsub hx)
    simp only [mem_coe, mem_product, mem_Icc]
    omega

/-- A product over pairs `i < j` in `Fin N` as a double product over `range N`. -/
lemma s26b_prod_Ioi_fin {M : Type*} [CommMonoid M] (N : ℕ) (f : ℕ → ℕ → M) :
    ∏ i : Fin N, ∏ j ∈ Ioi i, f i j =
      ∏ i ∈ range N, ∏ j ∈ range N, if i < j then f i j else 1 := by
  rw [← Fin.prod_univ_eq_prod_range (fun i => ∏ j ∈ range N, if i < j then f i j else 1)]
  refine prod_congr rfl fun i _ => ?_
  rw [← Fin.prod_univ_eq_prod_range (fun j => if (i : ℕ) < j then f i j else 1), ← prod_filter]
  refine prod_congr ?_ fun _ _ => rfl
  ext j; simp

/-- A sum over pairs `i < j` in `Fin N` as a double sum over `range N`. -/
lemma s26b_sum_Ioi_fin (N : ℕ) (f : ℕ → ℕ → ℕ) :
    ∑ i : Fin N, ∑ j ∈ Ioi i, f i j =
      ∑ i ∈ range N, ∑ j ∈ range N, if i < j then f i j else 0 := by
  rw [← Fin.sum_univ_eq_sum_range (fun i => ∑ j ∈ range N, if i < j then f i j else 0)]
  refine sum_congr rfl fun i _ => ?_
  rw [← Fin.sum_univ_eq_sum_range (fun j => if (i : ℕ) < j then f i j else 0), ← sum_filter]
  refine sum_congr ?_ fun _ _ => rfl
  ext j; simp

/-- `1 - X ^ m ≠ 0` in `ℤ[X]` for `m > 0`. -/
lemma s26b_one_sub_X_pow_ne_zero {m : ℕ} (hm : 0 < m) : (1 - X ^ m : ℤ[X]) ≠ 0 := by
  have := X_pow_sub_C_ne_zero (R := ℤ) hm 1
  rw [map_one] at this
  intro h; apply this; rw [← neg_sub, h, neg_zero]

/-- Vandermonde product for a strictly decreasing exponent sequence. -/
lemma s26b_vand_decr (N : ℕ) (α : ℕ → ℕ) (hα : ∀ i j, i < j → j < N → α j < α i) :
    ∏ i : Fin N, ∏ j ∈ Ioi i, ((X : ℤ[X]) ^ α j - X ^ α i) =
      X ^ (∑ i : Fin N, ∑ j ∈ Ioi i, α j) *
        ∏ i ∈ range N, ∏ j ∈ range N, if i < j then (1 - X ^ (α i - α j)) else 1 := by
  rw [← s26b_prod_Ioi_fin N (fun i j => 1 - (X : ℤ[X]) ^ (α i - α j)), ← prod_pow_eq_pow_sum,
    ← prod_mul_distrib]
  refine prod_congr rfl fun i _ => ?_
  rw [← prod_pow_eq_pow_sum, ← prod_mul_distrib]
  refine prod_congr rfl fun j hj => ?_
  have hij : (i : ℕ) < j := by simpa using hj
  have := hα i j hij j.isLt
  rw [mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' this.le]

/-- Splitting the pairs `i < j` into the cross pairs `i < r ≤ j` and the rest. -/
lemma s26b_prod_split_cross {M : Type*} [CommMonoid M] (N r : ℕ) (hr : r ≤ N) (F : ℕ → ℕ → M) :
    ∏ i ∈ range N, ∏ j ∈ range N, (if i < j then F i j else 1) =
      (∏ i ∈ range N, ∏ j ∈ range N, if i < j ∧ ¬(i < r ∧ r ≤ j) then F i j else 1) *
        ∏ i ∈ range r, ∏ j ∈ Ico r N, F i j := by
  have hc : ∏ i ∈ range N, ∏ j ∈ range N, (if i < j ∧ (i < r ∧ r ≤ j) then F i j else 1) =
      ∏ i ∈ range r, ∏ j ∈ Ico r N, F i j := by
    have h1 : ∀ i ∈ range N, ∏ j ∈ range N, (if i < j ∧ (i < r ∧ r ≤ j) then F i j else 1) =
        if i < r then ∏ j ∈ Ico r N, F i j else 1 := by
      intro i _
      split_ifs with hi
      · rw [← prod_filter]
        refine prod_congr ?_ fun _ _ => rfl
        ext j; simp only [mem_filter, mem_range, mem_Ico]; omega
      · exact prod_eq_one fun j _ => by split_ifs with h; exacts [absurd h.2.1 hi, rfl]
    rw [prod_congr rfl h1, ← prod_filter]
    refine prod_congr ?_ fun _ _ => rfl
    ext j; simp only [mem_filter, mem_range]; omega
  rw [← hc, ← prod_mul_distrib]
  refine prod_congr rfl fun i _ => ?_
  rw [← prod_mul_distrib]
  refine prod_congr rfl fun j _ => ?_
  by_cases h : i < r ∧ r ≤ j
  · have : i < j := by omega
    simp [h, this]
  · simp [h]

/-- The Vandermonde algebra behind MacMahon's formula: the bialternant identity for the
rectangle `r × t` in `r + s` variables at `xₖ = Xᵏ`, reduced to the cross pairs. -/
lemma s26b_alg_main (r s t : ℕ) (G : ℤ[X])
    (h : X ^ (∑ i : Fin (r + s), ∑ j ∈ Ioi i, (if (j : ℕ) < r then t else 0)) * G *
        ∏ i : Fin (r + s), ∏ j ∈ Ioi i,
          ((X : ℤ[X]) ^ (r + s - 1 - (j : ℕ)) - X ^ (r + s - 1 - (i : ℕ))) =
      ∏ i : Fin (r + s), ∏ j ∈ Ioi i,
          ((X : ℤ[X]) ^ ((if (j : ℕ) < r then t else 0) + (r + s - 1 - (j : ℕ))) -
            X ^ ((if (i : ℕ) < r then t else 0) + (r + s - 1 - (i : ℕ))))) :
    G * ∏ i ∈ range r, ∏ j ∈ Ico r (r + s), (1 - (X : ℤ[X]) ^ (j - i)) =
      ∏ i ∈ range r, ∏ j ∈ Ico r (r + s), (1 - (X : ℤ[X]) ^ (t + j - i)) := by
  set N := r + s with hN
  set g : ℕ → ℕ := fun i => if i < r then t else 0 with hg
  set δ : ℕ → ℕ := fun i => N - 1 - i with hδ
  set β : ℕ → ℕ := fun i => g i + δ i with hβ
  have hδd : ∀ i j, i < j → j < N → δ j < δ i := fun i j hij hj => by simp only [hδ]; omega
  have hβd : ∀ i j, i < j → j < N → β j < β i := fun i j hij hj => by
    simp only [hβ, hδ, hg]; split_ifs <;> omega
  have h' := h
  change X ^ (∑ i : Fin N, ∑ j ∈ Ioi i, g j) * G *
      ∏ i : Fin N, ∏ j ∈ Ioi i, ((X : ℤ[X]) ^ δ j - X ^ δ i) =
    ∏ i : Fin N, ∏ j ∈ Ioi i, ((X : ℤ[X]) ^ β j - X ^ β i) at h'
  rw [s26b_vand_decr N δ hδd, s26b_vand_decr N β hβd] at h'
  have hE : ∑ i : Fin N, ∑ j ∈ Ioi i, β j =
      ∑ i : Fin N, ∑ j ∈ Ioi i, δ j + ∑ i : Fin N, ∑ j ∈ Ioi i, g j := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [← sum_add_distrib]
    exact sum_congr rfl fun j _ => by simp only [hβ]; ring
  have hr : r ≤ N := by omega
  rw [hE, s26b_prod_split_cross N r hr, s26b_prod_split_cross N r hr] at h'
  have hC : (∏ i ∈ range N, ∏ j ∈ range N,
        if i < j ∧ ¬(i < r ∧ r ≤ j) then (1 - (X : ℤ[X]) ^ (β i - β j)) else 1) =
      ∏ i ∈ range N, ∏ j ∈ range N,
        if i < j ∧ ¬(i < r ∧ r ≤ j) then (1 - (X : ℤ[X]) ^ (δ i - δ j)) else 1 := by
    refine prod_congr rfl fun i hi => prod_congr rfl fun j hj => ?_
    simp only [mem_range] at hi hj
    split_ifs with hc
    · congr 2; simp only [hβ, hg, hδ]; split_ifs <;> omega
    · rfl
  rw [hC] at h'
  set C := ∏ i ∈ range N, ∏ j ∈ range N,
        if i < j ∧ ¬(i < r ∧ r ≤ j) then (1 - (X : ℤ[X]) ^ (δ i - δ j)) else 1 with hCdef
  have hC0 : C ≠ 0 := by
    refine prod_ne_zero_iff.mpr fun i hi => prod_ne_zero_iff.mpr fun j hj => ?_
    simp only [mem_range] at hi hj
    split_ifs with hc
    · exact s26b_one_sub_X_pow_ne_zero (by simp only [hδ]; omega)
    · exact one_ne_zero
  have hX : (X : ℤ[X]) ^ (∑ i : Fin N, ∑ j ∈ Ioi i, δ j + ∑ i : Fin N, ∑ j ∈ Ioi i, g j) * C ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ X_ne_zero) hC0
  have key : (X : ℤ[X]) ^ (∑ i : Fin N, ∑ j ∈ Ioi i, δ j + ∑ i : Fin N, ∑ j ∈ Ioi i, g j) * C *
      (G * ∏ i ∈ range r, ∏ j ∈ Ico r N, (1 - (X : ℤ[X]) ^ (δ i - δ j))) =
      (X : ℤ[X]) ^ (∑ i : Fin N, ∑ j ∈ Ioi i, δ j + ∑ i : Fin N, ∑ j ∈ Ioi i, g j) * C *
      ∏ i ∈ range r, ∏ j ∈ Ico r N, (1 - (X : ℤ[X]) ^ (β i - β j)) := by
    linear_combination h'
  have key2 := mul_left_cancel₀ hX key
  convert key2 using 1
  · congr 1
    refine prod_congr rfl fun i hi => prod_congr rfl fun j hj => ?_
    simp only [mem_range, mem_Ico] at hi hj
    congr 2; simp only [hδ]; omega
  · refine prod_congr rfl fun i hi => prod_congr rfl fun j hj => ?_
    simp only [mem_range, mem_Ico] at hi hj
    congr 2; simp only [hβ, hδ, hg]; split_ifs <;> omega

/-- An alternant evaluated at the geometric progression `xₖ = Xᵏ` is a Vandermonde product. -/
lemma s26b_eval_alternant {N : ℕ} (α : Fin N → ℕ) :
    MvPolynomial.eval (fun k : Fin N => (X : ℤ[X]) ^ (k : ℕ))
        (TauCeti.alternant (Fin N) ℤ[X] α) =
      ∏ i : Fin N, ∏ j ∈ Ioi i, ((X : ℤ[X]) ^ α j - X ^ α i) := by
  rw [TauCeti.alternant_def, RingHom.map_det, ← Matrix.det_vandermonde, ← Matrix.det_transpose]
  congr 1
  ext i j
  simp [Matrix.vandermonde, ← pow_mul, mul_comm]

/-- The monomial of a tableau at a geometric progression. -/
lemma s26b_prod_weight {N : ℕ} {μ : YoungDiagram} (T : TauCeti.BoundedSSYT N μ) :
    ∏ k : Fin N, ((X : ℤ[X]) ^ (k : ℕ)) ^ TauCeti.BoundedSSYT.weight T k =
      X ^ (∑ x ∈ μ.cells, T.1 x.1 x.2) := by
  simp only [← pow_mul]
  rw [prod_pow_eq_pow_sum]
  congr 1
  simp only [TauCeti.BoundedSSYT.weight_apply, SemistandardYoungTableau.content_apply]
  rw [Fin.sum_univ_eq_sum_range (fun k => k * #(μ.cells.filter fun c => T.1 c.1 c.2 = k)) N,
    ← sum_fiberwise_of_maps_to (g := fun c : ℕ × ℕ => T.1 c.1 c.2) (t := range N)
      (fun c hc => mem_range.mpr
        (TauCeti.BoundedSSYT.entry_lt T ((YoungDiagram.mem_cells _).mp hc)))]
  refine sum_congr rfl fun k _ => ?_
  rw [sum_congr rfl (g := fun _ => k) (fun c hc => (mem_filter.mp hc).2), sum_const, smul_eq_mul,
    mul_comm]

/-- The exponent `∑_{i<j} λ_j` for the rectangle `r × t`. -/
lemma s26b_sum_g (r s t : ℕ) :
    ∑ i : Fin (r + s), ∑ j ∈ Ioi i, (if (j : ℕ) < r then t else 0) = t * ∑ i ∈ range r, i := by
  rw [s26b_sum_Ioi_fin (r + s) (fun _ j => if j < r then t else 0), sum_comm]
  have : ∀ j ∈ range (r + s), (∑ i ∈ range (r + s), if i < j then (if j < r then t else 0) else 0) =
      if j < r then t * j else 0 := by
    intro j hj
    rw [mem_range] at hj
    rw [← sum_filter, sum_const, smul_eq_mul]
    have : #((range (r + s)).filter (· < j)) = j := by
      rw [show (range (r + s)).filter (· < j) = range j by
        ext i; simp only [mem_filter, mem_range]; omega, card_range]
    rw [this]
    split_ifs <;> ring
  rw [sum_congr rfl this, ← sum_filter, mul_sum]
  refine sum_congr ?_ fun _ _ => rfl
  ext i; simp only [mem_filter, mem_range]; omega

/-- MacMahon's box formula as a polynomial identity (proof via Jacobi's bialternant formula). -/
lemma s26b_box_poly (r s t : ℕ) :
    (∑ π ∈ planePartitionsIn r s t, (X : ℤ[X]) ^ #π) *
        ∏ h ∈ Icc 1 r, ∏ k ∈ Icc 1 s, (1 - (X : ℤ[X]) ^ (h + k - 1)) =
      ∏ h ∈ Icc 1 r, ∏ k ∈ Icc 1 s, (1 - (X : ℤ[X]) ^ (h + k + t - 1)) := by
  set N := r + s with hN
  have hcol : (s26b_rect r t).colLen 0 ≤ N := by
    by_contra h
    push Not at h
    have := YoungDiagram.mem_iff_lt_colLen.mpr h
    rw [s26b_mem_rect] at this; omega
  have hrow : ∀ i, (s26b_rect r t).rowLen i = if i < r then t else 0 := by
    intro i
    apply le_antisymm
    · by_contra h
      push Not at h
      have := YoungDiagram.mem_iff_lt_rowLen.mpr h
      rw [s26b_mem_rect] at this
      split_ifs at this with hi <;> omega
    · split_ifs with hi
      · by_contra h
        push Not at h
        have := (s26b_mem_rect (r := r) (t := t) (i := i)
          (c := (s26b_rect r t).rowLen i)).mpr ⟨hi, h⟩
        exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp this) (lt_irrefl _)
      · exact Nat.zero_le _
  have hb := congrArg (MvPolynomial.eval (fun k : Fin N => (X : ℤ[X]) ^ (k : ℕ)))
    (TauCeti.diagramSchurPoly_mul_alternant (R := ℤ[X]) N (s26b_rect r t) hcol)
  rw [map_mul, s26b_eval_alternant, s26b_eval_alternant, TauCeti.eval_diagramSchurPoly] at hb
  simp only [YoungDiagram.betaNumber_def, hrow, s26b_prod_weight] at hb
  -- the tableau sum
  have hsum : ∑ T : TauCeti.BoundedSSYT N (s26b_rect r t),
      (X : ℤ[X]) ^ (∑ x ∈ (s26b_rect r t).cells, T.1 x.1 x.2) =
      X ^ (t * ∑ i ∈ range r, i) * ∑ π ∈ planePartitionsIn r s t, (X : ℤ[X]) ^ #π := by
    rw [mul_sum]
    symm
    refine sum_bij' (fun π hπ => ⟨s26b_toT r s t π (s26b_mem_planePartitionsIn.mp hπ).2,
        s26b_toT_lt _⟩) (fun T _ => s26b_ofT r s t T.1) (fun _ _ => mem_univ _)
      (fun T _ => s26b_ofT_mem r s t T.1) (fun π hπ => s26b_ofT_toT hπ)
      (fun T _ => Subtype.ext (s26b_toT_ofT T.1 T.2)) ?_
    intro π hπ
    rw [← pow_add]
    exact congrArg _ (by rw [s26b_sum_toT hπ]; ring)
  rw [hsum, ← s26b_sum_g r s t] at hb
  have key := s26b_alg_main r s t _ hb
  convert key using 1
  · congr 1
    refine prod_nbij' (fun h => r - h) (fun i => r - i) ?_ ?_ ?_ ?_ ?_
    · intro h hh; simp at hh ⊢; omega
    · intro i hi; simp at hi ⊢; omega
    · intro h hh; simp at hh; omega
    · intro i hi; simp at hi; omega
    · intro h hh
      simp only [mem_Icc] at hh
      refine prod_nbij' (fun k => k + r - 1) (fun j => j + 1 - r) ?_ ?_ ?_ ?_ ?_
      · intro k hk; simp at hk ⊢; omega
      · intro j hj; simp at hj ⊢; omega
      · intro k hk; simp at hk; omega
      · intro j hj; simp at hj; omega
      · intro k hk
        simp only [mem_Icc] at hk
        congr 2; omega
  · refine prod_nbij' (fun h => r - h) (fun i => r - i) ?_ ?_ ?_ ?_ ?_
    · intro h hh; simp at hh ⊢; omega
    · intro i hi; simp at hi ⊢; omega
    · intro h hh; simp at hh; omega
    · intro i hi; simp at hi; omega
    · intro h hh
      simp only [mem_Icc] at hh
      refine prod_nbij' (fun k => k + r - 1) (fun j => j + 1 - r) ?_ ?_ ?_ ?_ ?_
      · intro k hk; simp at hk ⊢; omega
      · intro j hj; simp at hj ⊢; omega
      · intro k hk; simp at hk; omega
      · intro j hj; simp at hj; omega
      · intro k hk
        simp only [mem_Icc] at hk
        congr 2; omega

/-- Telescoping product in a field. -/
lemma s26b_prod_Icc_div {K : Type*} [Field K] (f : ℕ → K) (t : ℕ) (hf : ∀ k ≤ t, f k ≠ 0) :
    ∏ k ∈ Icc 1 t, f k / f (k - 1) = f t / f 0 := by
  induction t with
  | zero => simp [div_self (hf 0 le_rfl)]
  | succ n ih =>
    have h0 : f 0 ≠ 0 := hf 0 (by omega)
    rw [prod_Icc_succ_top (by omega), ih fun k hk => hf k (by omega), Nat.add_sub_cancel]
    have hn : f n ≠ 0 := hf n (by omega)
    field_simp

/-- The counting form: `#PP(r,s,t) ∏ (h+k-1) = ∏ (h+k+t-1)`. -/
lemma s26b_box_count (r s t : ℕ) :
    ((planePartitionsIn r s t).card : ℚ) * ∏ h ∈ Icc 1 r, ∏ k ∈ Icc 1 s, ((h + k - 1 : ℕ) : ℚ) =
      ∏ h ∈ Icc 1 r, ∏ k ∈ Icc 1 s, ((h + k + t - 1 : ℕ) : ℚ) := by
  have hp := s26b_box_poly r s t
  simp only [← mul_neg_geom_sum (X : ℤ[X]), prod_mul_distrib, prod_const, Nat.card_Icc,
    Nat.add_sub_cancel] at hp
  have hne : ((1 - X : ℤ[X]) ^ s) ^ r ≠ 0 :=
    pow_ne_zero _ (pow_ne_zero _ (by simpa using s26b_one_sub_X_pow_ne_zero (m := 1) one_pos))
  have hp' : (∑ π ∈ planePartitionsIn r s t, (X : ℤ[X]) ^ #π) *
      ∏ h ∈ Icc 1 r, ∏ k ∈ Icc 1 s, ∑ i ∈ range (h + k - 1), (X : ℤ[X]) ^ i =
      ∏ h ∈ Icc 1 r, ∏ k ∈ Icc 1 s, ∑ i ∈ range (h + k + t - 1), (X : ℤ[X]) ^ i := by
    apply mul_left_cancel₀ hne
    linear_combination hp
  have := congrArg (Polynomial.aeval (1 : ℚ)) hp'
  simpa [map_prod, map_sum] using this

/-- Box product equals the double product (rational form). -/
lemma s26b_box_prod_rat (r s t : ℕ) :
    ∏ x ∈ planeBox r s t, ((x.1 + x.2.1 + x.2.2 - 1 : ℚ) / (x.1 + x.2.1 + x.2.2 - 2)) =
      ∏ h ∈ Icc 1 r, ∏ j ∈ Icc 1 s, ((h + j + t - 1 : ℚ) / (h + j - 1)) := by
  rw [planeBox, prod_product]
  refine prod_congr rfl fun h hh => ?_
  rw [prod_product]
  refine prod_congr rfl fun j hj => ?_
  simp only [mem_Icc] at hh hj
  have := s26b_prod_Icc_div (fun k : ℕ => (h + j + k - 1 : ℚ)) t (fun k _ => by
    have : (1 : ℚ) ≤ h := by exact_mod_cast hh.1
    have : (1 : ℚ) ≤ j := by exact_mod_cast hj.1
    have : (0 : ℚ) ≤ k := by positivity
    intro h0; linarith)
  simp only [Nat.cast_zero, add_zero] at this
  rw [← this]
  refine prod_congr rfl fun k hk => ?_
  simp only [mem_Icc] at hk
  rw [Nat.cast_sub hk.1]
  ring_nf

/-! The array description of §26.12(i). -/

/-- The array condition of §26.12(i). -/
def S26bIsPPArray (n : ℕ) (a : ℕ → ℕ → ℕ) : Prop :=
  (∀ i j, a (i + 1) j ≤ a i j) ∧ (∀ i j, a i (j + 1) ≤ a i j) ∧
    (Function.support (Function.uncurry a)).Finite ∧
    ∑ᶠ ij : ℕ × ℕ, Function.uncurry a ij = n

/-- Arrays are antitone in both indices. -/
lemma s26b_array_anti {a : ℕ → ℕ → ℕ} (h1 : ∀ i j, a (i + 1) j ≤ a i j)
    (h2 : ∀ i j, a i (j + 1) ≤ a i j) {i i' j j' : ℕ} (hi : i ≤ i') (hj : j ≤ j') :
    a i' j' ≤ a i j := by
  have hA : ∀ j, Antitone fun i => a i j := fun j => antitone_nat_of_succ_le fun i => h1 i j
  have hB : ∀ i, Antitone fun j => a i j := fun i => antitone_nat_of_succ_le fun j => h2 i j
  exact (hB i' hj).trans (hA j hi)

/-- Bounds for an array of sum `n`: nonzero entries lie in `[0, n)²` and are at most `n`. -/
lemma s26b_array_bound {n : ℕ} {a : ℕ → ℕ → ℕ} (ha : S26bIsPPArray n a) {i j : ℕ}
    (hij : a i j ≠ 0) : i < n ∧ j < n ∧ a i j ≤ n := by
  obtain ⟨h1, h2, hfin, hsum⟩ := ha
  rw [finsum_eq_sum_of_support_subset _ hfin.coe_toFinset.symm.subset] at hsum
  have key : ∀ s : Finset (ℕ × ℕ), ∑ x ∈ s, Function.uncurry a x ≤ n := fun s => by
    rw [← hsum]
    refine sum_le_sum_of_ne_zero fun x _ hx => ?_
    simpa using hx
  refine ⟨?_, ?_, ?_⟩
  · have := key ((range (i + 1)).image fun i' => (i', j))
    rw [sum_image (fun _ _ _ _ h => (Prod.mk.inj h).1)] at this
    simp only [Function.uncurry_apply_pair] at this
    have hge : ∑ i' ∈ range (i + 1), 1 ≤ ∑ i' ∈ range (i + 1), Function.uncurry a (i', j) :=
      sum_le_sum fun i' hi' => by
        have := s26b_array_anti h1 h2 (i := i') (i' := i) (j := j) (j' := j)
          (by simp at hi'; omega) le_rfl
        simp only [Function.uncurry_apply_pair]; omega
    simp only [Function.uncurry_apply_pair, sum_const, card_range, smul_eq_mul, mul_one] at hge
    omega
  · have := key ((range (j + 1)).image fun j' => (i, j'))
    rw [sum_image (fun _ _ _ _ h => (Prod.mk.inj h).2)] at this
    simp only [Function.uncurry_apply_pair] at this
    have hge : ∑ j' ∈ range (j + 1), 1 ≤ ∑ j' ∈ range (j + 1), Function.uncurry a (i, j') :=
      sum_le_sum fun j' hj' => by
        have := s26b_array_anti h1 h2 (i := i) (i' := i) (j := j') (j' := j) le_rfl
          (by simp at hj'; omega)
        simp only [Function.uncurry_apply_pair]; omega
    simp only [Function.uncurry_apply_pair, sum_const, card_range, smul_eq_mul, mul_one] at hge
    omega
  · simpa using key {(i, j)}

/-- The array of a plane partition. -/
def s26b_toArr (n : ℕ) (π : Finset (ℕ × ℕ × ℕ)) : ℕ → ℕ → ℕ :=
  fun i j => #(s26b_fiber π n (i + 1) (j + 1))

/-- The plane partition of an array. -/
def s26b_ofArr (n : ℕ) (a : ℕ → ℕ → ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (planeBox n n n).filter fun x => x.2.1 ≤ a (x.1 - 1) (x.2.2 - 1)

/-- `|π|` as the sum of its column heights. -/
lemma s26b_card_eq_sum_fiber {r s t : ℕ} {π : Finset (ℕ × ℕ × ℕ)} (hsub : π ⊆ planeBox r s t) :
    #π = ∑ h ∈ Icc 1 r, ∑ k ∈ Icc 1 t, #(s26b_fiber π s h k) := by
  rw [card_eq_sum_card_fiberwise (f := fun x : ℕ × ℕ × ℕ => (x.1, x.2.2))
    (t := Icc 1 r ×ˢ Icc 1 t), sum_product]
  · refine sum_congr rfl fun h _ => sum_congr rfl fun k _ => ?_
    refine card_nbij' (fun x => x.2.1) (fun j => (h, j, k)) ?_ ?_ ?_ ?_
    · rintro ⟨h', j, k'⟩ hx
      simp only [mem_coe, mem_filter, Prod.mk.injEq] at hx
      obtain ⟨hx, rfl, rfl⟩ := hx
      have := s26b_mem_planeBox.mp (hsub hx)
      simp only [s26b_fiber, mem_coe, mem_filter, mem_Icc]
      exact ⟨⟨this.2.2.1, this.2.2.2.1⟩, hx⟩
    · intro j hj
      simp only [s26b_fiber, mem_coe, mem_filter] at hj
      simp [hj.2]
    · rintro ⟨h', j, k'⟩ hx
      simp only [mem_coe, mem_filter, Prod.mk.injEq] at hx
      obtain ⟨_, rfl, rfl⟩ := hx
      rfl
    · intro j _; rfl
  · rintro ⟨h, j, k⟩ hx
    have := s26b_mem_planeBox.mp (hsub hx)
    simp only [mem_coe, mem_product, mem_Icc]
    omega

/-- The columns of `s26b_ofArr`. -/
lemma s26b_fiber_ofArr {n : ℕ} {a : ℕ → ℕ → ℕ} (ha : S26bIsPPArray n a) {h k : ℕ}
    (hh : 1 ≤ h ∧ h ≤ n) (hk : 1 ≤ k ∧ k ≤ n) :
    s26b_fiber (s26b_ofArr n a) n h k = Icc 1 (a (h - 1) (k - 1)) := by
  have hle : a (h - 1) (k - 1) ≤ n := by
    by_cases h0 : a (h - 1) (k - 1) = 0
    · omega
    · exact (s26b_array_bound ha h0).2.2
  ext j
  simp only [s26b_fiber, s26b_ofArr, mem_filter, mem_Icc, s26b_mem_planeBox]
  constructor
  · rintro ⟨⟨hj1, _⟩, _, hj⟩; exact ⟨hj1, hj⟩
  · rintro ⟨hj1, hj2⟩; exact ⟨⟨hj1, by omega⟩, ⟨hh.1, hh.2, hj1, by omega, hk.1, hk.2⟩, hj2⟩

/-- `s26b_ofArr` of an array is a plane partition of `n` in `B(n, n, n)`. -/
lemma s26b_ofArr_mem {n : ℕ} {a : ℕ → ℕ → ℕ} (ha : S26bIsPPArray n a) :
    s26b_ofArr n a ∈ {π ∈ (planeBox n n n).powerset | IsPlanePartition π ∧ π.card = n} := by
  simp only [mem_filter, mem_powerset]
  refine ⟨filter_subset _ _, ?_, ?_⟩
  · rintro ⟨h, j, k⟩ hx
    simp only [s26b_ofArr, mem_filter, s26b_mem_planeBox] at hx
    obtain ⟨⟨h1, h2, j1, j2, k1, k2⟩, hle⟩ := hx
    refine ⟨h1, j1, k1, ?_⟩
    rintro ⟨h', j', k'⟩ hy
    simp only [s26b_mem_planeBox] at hy
    simp only [s26b_ofArr, mem_filter, s26b_mem_planeBox]
    refine ⟨⟨hy.1, by omega, hy.2.2.1, by omega, hy.2.2.2.2.1, by omega⟩, ?_⟩
    have := s26b_array_anti ha.1 ha.2.1 (i := h' - 1) (i' := h - 1) (j := k' - 1) (j' := k - 1)
      (by omega) (by omega)
    omega
  · rw [s26b_card_eq_sum_fiber (π := s26b_ofArr n a) (r := n) (s := n) (t := n)
      (filter_subset _ _)]
    have hsupp : Function.support (Function.uncurry a) ⊆ ↑(range n ×ˢ range n) := by
      rintro ⟨i, j⟩ hx
      have := s26b_array_bound ha hx
      simp only [coe_product, coe_range, Set.mem_prod, Set.mem_Iio]
      omega
    have hs := ha.2.2.2
    rw [finsum_eq_sum_of_support_subset _ hsupp, sum_product] at hs
    refine Eq.trans ?_ hs
    refine sum_nbij' (· - 1) (· + 1) ?_ ?_ ?_ ?_ ?_
    · intro i hi; simp at hi ⊢; omega
    · intro i hi; simp at hi ⊢; omega
    · intro i hi; simp at hi; omega
    · intro i hi; simp
    · intro h hh
      simp only [mem_Icc] at hh
      refine sum_nbij' (· - 1) (· + 1) ?_ ?_ ?_ ?_ ?_
      · intro j hj; simp at hj ⊢; omega
      · intro j hj; simp at hj ⊢; omega
      · intro j hj; simp at hj; omega
      · intro j hj; simp
      · intro k hk
        simp only [mem_Icc] at hk
        rw [s26b_fiber_ofArr ha hh hk, Nat.card_Icc, Nat.add_sub_cancel]
        rfl

/-- The second form of (26.12.21) (helper used before its statement). -/
lemma s26b_sum_box_pow {q : ℂ} (hq : ∀ m : ℕ, 0 < m → q ^ m ≠ 1) (r s t : ℕ) :
    ∑ π ∈ planePartitionsIn r s t, q ^ π.card =
      ∏ h ∈ Icc 1 r, ∏ j ∈ Icc 1 s, (1 - q ^ (h + j + t - 1)) / (1 - q ^ (h + j - 1)) := by
  have hne : ∀ m : ℕ, 0 < m → (1 - q ^ m) ≠ 0 := fun m hm h => hq m hm (sub_eq_zero.mp h).symm
  have hp := congrArg (Polynomial.aeval q) (s26b_box_poly r s t)
  simp only [map_mul, map_sum, map_prod, map_sub, map_one, map_pow, Polynomial.aeval_X] at hp
  have hD : ∏ h ∈ Icc 1 r, ∏ k ∈ Icc 1 s, (1 - q ^ (h + k - 1)) ≠ 0 :=
    prod_ne_zero_iff.mpr fun h hh => prod_ne_zero_iff.mpr fun k hk => by
      simp only [mem_Icc] at hh hk; exact hne _ (by omega)
  rw [eq_div_of_mul_eq hD hp, ← prod_div_distrib]
  exact prod_congr rfl fun h _ => (prod_div_distrib _ _).symm

end MacMahonBox

/-- `pp(n)`: the number of plane partitions of `n` (DLMF §26.12(i)). A plane partition with `n`
points lies in `B(n, n, n)`. -/
@[dlmf 26.12.i]
def planePartitionCount (n : ℕ) : ℕ :=
  #{π ∈ (planeBox n n n).powerset | IsPlanePartition π ∧ π.card = n}

/-- §26.12(i): `pp(0) = 1`. -/
@[dlmf 26.12.i]
theorem planePartitionCount_zero : planePartitionCount 0 = 1 := by
  decide

/-- Table 26.12.1, the first entries: `pp(1) = 1`, `pp(2) = 3` (the rest of the table is not
acquired: finite table of exact values, see the ledger). -/
@[dlmf 26.12.T1]
theorem planePartitionCount_one_two : planePartitionCount 1 = 1 ∧ planePartitionCount 2 = 3 := by
  decide +kernel

/-- §26.12(i), the array definition: `pp(n)` is the number of arrays `(a_{ij})` of
nonnegative integers with finitely many nonzero entries, weakly decreasing across rows and down
columns, with sum `n`. -/
@[dlmf 26.12.i]
theorem planePartitionCount_eq_card_arrays (n : ℕ) :
    planePartitionCount n =
      Nat.card {a : ℕ → ℕ → ℕ // (∀ i j, a (i + 1) j ≤ a i j) ∧ (∀ i j, a i (j + 1) ≤ a i j) ∧
        (Function.support (Function.uncurry a)).Finite ∧
        ∑ᶠ ij : ℕ × ℕ, Function.uncurry a ij = n} := by
  change _ = Nat.card {a : ℕ → ℕ → ℕ // S26bIsPPArray n a}
  rw [planePartitionCount, ← Nat.card_eq_finsetCard]
  -- forward map facts
  have hfwd : ∀ π : Finset (ℕ × ℕ × ℕ), π ∈ {π ∈ (planeBox n n n).powerset |
      IsPlanePartition π ∧ π.card = n} → S26bIsPPArray n (s26b_toArr n π) := by
    intro π hπ
    simp only [mem_filter, mem_powerset] at hπ
    obtain ⟨hsub, hπ, hcard⟩ := hπ
    have hsupp : Function.support (Function.uncurry (s26b_toArr n π)) ⊆
        ↑(range n ×ˢ range n) := by
      rintro ⟨i, j⟩ hx
      simp only [Function.mem_support, Function.uncurry_apply_pair, s26b_toArr, ne_eq,
        card_eq_zero, ← nonempty_iff_ne_empty] at hx
      obtain ⟨j', hj'⟩ := hx
      simp only [s26b_fiber, mem_filter] at hj'
      have := s26b_mem_planeBox.mp (hsub hj'.2)
      simp only [coe_product, coe_range, Set.mem_prod, Set.mem_Iio]
      omega
    refine ⟨fun i j => s26b_fiber_mono hπ (by omega) (by omega) (by omega) le_rfl,
      fun i j => s26b_fiber_mono hπ (by omega) le_rfl (by omega) (by omega),
      (finite_toSet _).subset hsupp, ?_⟩
    rw [finsum_eq_sum_of_support_subset _ hsupp, sum_product]
    refine Eq.trans ?_ hcard
    rw [s26b_card_eq_sum_fiber hsub]
    refine sum_nbij' (· + 1) (· - 1) ?_ ?_ ?_ ?_ ?_
    · intro i hi; simp at hi ⊢; omega
    · intro i hi; simp at hi ⊢; omega
    · intro i hi; simp
    · intro i hi; simp at hi; omega
    · intro i _
      refine sum_nbij' (· + 1) (· - 1) ?_ ?_ ?_ ?_ ?_
      · intro j hj; simp at hj ⊢; omega
      · intro j hj; simp at hj ⊢; omega
      · intro j hj; simp
      · intro j hj; simp at hj; omega
      · intro j _; rfl
  refine Nat.card_congr
    { toFun := fun π => ⟨s26b_toArr n π, hfwd π π.2⟩
      invFun := fun a => ⟨s26b_ofArr n a, s26b_ofArr_mem a.2⟩
      left_inv := ?_
      right_inv := ?_ }
  · rintro ⟨π, hπ⟩
    refine Subtype.ext ?_
    simp only [mem_filter, mem_powerset] at hπ
    obtain ⟨hsub, hπ, -⟩ := hπ
    ext ⟨h, j, k⟩
    change (h, j, k) ∈ (planeBox n n n).filter _ ↔ _
    rw [mem_filter]
    simp only [s26b_toArr]
    constructor
    · rintro ⟨hb, hle⟩
      have hb' := s26b_mem_planeBox.mp hb
      rw [show h - 1 + 1 = h by omega, show k - 1 + 1 = k by omega] at hle
      exact (s26b_mem_iff_le_card hπ (by omega) (by omega)).mpr hle
    · intro hx
      have hb := hsub hx
      have hb' := s26b_mem_planeBox.mp hb
      refine ⟨hb, ?_⟩
      rw [show h - 1 + 1 = h by omega, show k - 1 + 1 = k by omega]
      exact (s26b_mem_iff_le_card hπ (by omega) (by omega)).mp hx
  · rintro ⟨a, ha⟩
    refine Subtype.ext ?_
    funext i j
    simp only [s26b_toArr]
    by_cases hij : i < n ∧ j < n
    · rw [s26b_fiber_ofArr ha (by omega) (by omega), Nat.card_Icc]
      simp
    · have h0 : a i j = 0 := by
        by_contra h0
        have := s26b_array_bound ha h0
        omega
      rw [h0, card_eq_zero]
      ext j'
      simp only [s26b_fiber, s26b_ofArr, mem_filter, s26b_mem_planeBox, notMem_empty,
        iff_false]
      omega

/-- (26.12.1): there are six plane partitions of 3. -/
@[dlmf 26.12.E1]
theorem planePartitionCount_three : planePartitionCount 3 = 6 := by
  have : planePartitionCount 3 =
      #((planeBox 3 3 3).powersetCard 3 |>.filter IsPlanePartition) := by
    unfold planePartitionCount
    rw [Finset.powersetCard_eq_filter, Finset.filter_filter]
    exact congrArg Finset.card (Finset.filter_congr fun π _ => and_comm)
  rw [this]
  decide +kernel

/-- The plane partition of 75 of (26.12.2), as the set of its blocks: the array
`6 5 5 4 3 3 / 6 4 3 3 1 / 6 4 3 1 1 / 4 2 2 1 / 3 1 1 / 1 1 1`. -/
def planePartitionExample : Finset (ℕ × ℕ × ℕ) :=
  ((planeBox 6 6 6).filter fun x =>
    x.2.2 ≤ ([[6, 5, 5, 4, 3, 3], [6, 4, 3, 3, 1], [6, 4, 3, 1, 1], [4, 2, 2, 1], [3, 1, 1],
      [1, 1, 1]].getD (x.1 - 1) []).getD (x.2.1 - 1) 0)

/-- (26.12.2) and Figure 26.12.1: the array (26.12.2) is a cyclically symmetric plane partition
of 75. -/
@[dlmf 26.12.E2]
theorem planePartitionExample_spec :
    IsPlanePartition planePartitionExample ∧ planePartitionExample.card = 75 ∧
      ∀ x ∈ planePartitionExample, (x.2.1, x.2.2, x.1) ∈ planePartitionExample := by
  decide +kernel

/-- (26.12.4): the number of plane partitions in `B(r, s, t)` is
`∏_{(h,j,k) ∈ B} (h+j+k-1)/(h+j+k-2) = ∏_{h=1}^r ∏_{j=1}^s (h+j+t-1)/(h+j-1)`. -/
@[dlmf 26.12.E4]
theorem card_planePartitionsIn (r s t : ℕ) :
    ((planePartitionsIn r s t).card : ℚ) =
        ∏ x ∈ planeBox r s t, ((x.1 + x.2.1 + x.2.2 - 1 : ℚ) / (x.1 + x.2.1 + x.2.2 - 2)) ∧
      ((planePartitionsIn r s t).card : ℚ) =
        ∏ h ∈ Icc 1 r, ∏ j ∈ Icc 1 s, ((h + j + t - 1 : ℚ) / (h + j - 1)) := by
  have h2 : ((planePartitionsIn r s t).card : ℚ) =
      ∏ h ∈ Icc 1 r, ∏ j ∈ Icc 1 s, ((h + j + t - 1 : ℚ) / (h + j - 1)) := by
    have hc := s26b_box_count r s t
    have hD : ∏ h ∈ Icc 1 r, ∏ k ∈ Icc 1 s, ((h + k - 1 : ℕ) : ℚ) ≠ 0 :=
      prod_ne_zero_iff.mpr fun h hh => prod_ne_zero_iff.mpr fun k hk => by
        simp only [mem_Icc] at hh hk; exact_mod_cast (by omega : h + k - 1 ≠ 0)
    rw [eq_div_of_mul_eq hD hc, ← prod_div_distrib]
    refine prod_congr rfl fun h hh => ?_
    rw [← prod_div_distrib]
    refine prod_congr rfl fun k hk => ?_
    simp only [mem_Icc] at hh hk
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast; ring
  exact ⟨h2.trans (s26b_box_prod_rat r s t).symm, h2⟩

/-- Symmetric plane partition: `(h, j, k) ∈ π` implies `(j, h, k) ∈ π`. -/
@[dlmf 26.12.i]
def IsSymmetricPP (π : Finset (ℕ × ℕ × ℕ)) : Prop := ∀ x ∈ π, (x.2.1, x.1, x.2.2) ∈ π

/-- Cyclically symmetric plane partition: `(h, j, k) ∈ π` implies `(j, k, h) ∈ π`. -/
@[dlmf 26.12.i]
def IsCyclicallySymmetricPP (π : Finset (ℕ × ℕ × ℕ)) : Prop := ∀ x ∈ π, (x.2.1, x.2.2, x.1) ∈ π

/-- Totally symmetric: symmetric and cyclically symmetric. -/
@[dlmf 26.12.i]
def IsTotallySymmetricPP (π : Finset (ℕ × ℕ × ℕ)) : Prop :=
  IsSymmetricPP π ∧ IsCyclicallySymmetricPP π

/-- The complement `π^c = {(h, j, k) | (r-h+1, s-j+1, t-k+1) ∉ π}` of `π ⊆ B(r, s, t)`. -/
@[dlmf 26.12.i]
def planeComplement (r s t : ℕ) (π : Finset (ℕ × ℕ × ℕ)) : Finset (ℕ × ℕ × ℕ) :=
  (planeBox r s t).filter fun x => (r + 1 - x.1, s + 1 - x.2.1, t + 1 - x.2.2) ∉ π

/-- The transpose `{(j, h, k) | (h, j, k) ∈ π}`. -/
def planeTranspose (π : Finset (ℕ × ℕ × ℕ)) : Finset (ℕ × ℕ × ℕ) :=
  π.map ⟨fun x => (x.2.1, x.1, x.2.2), fun x y h => by
    simp only [Prod.mk.injEq] at h; exact Prod.ext h.2.1 (Prod.ext h.1 h.2.2)⟩

/-- Symmetry of a finite plane partition under interchange of its first two coordinates is
decidable. -/
instance (π : Finset (ℕ × ℕ × ℕ)) : Decidable (IsSymmetricPP π) := by
  unfold IsSymmetricPP; infer_instance
/-- Cyclic symmetry of a finite plane partition is decidable. -/
instance (π : Finset (ℕ × ℕ × ℕ)) : Decidable (IsCyclicallySymmetricPP π) := by
  unfold IsCyclicallySymmetricPP; infer_instance
/-- Symmetry of a finite plane partition under all coordinate permutations is decidable. -/
instance (π : Finset (ℕ × ℕ × ℕ)) : Decidable (IsTotallySymmetricPP π) := by
  unfold IsTotallySymmetricPP; infer_instance

/-- (26.12.5): the number of symmetric plane partitions in `B(r, r, t)` is
`∏_{h=1}^r (2h+t-1)/(2h-1) ∏_{1≤h<j≤r} (h+j+t-1)/(h+j-1)`. -/
@[dlmf 26.12.E5]
theorem card_symmetric_planePartitionsIn (r t : ℕ) :
    ((planePartitionsIn r r t).filter IsSymmetricPP).card =
      (∏ h ∈ Icc 1 r, ((2 * h + t - 1 : ℚ) / (2 * h - 1))) *
        ∏ h ∈ Icc 1 r, ∏ j ∈ Ioc h r, ((h + j + t - 1 : ℚ) / (h + j - 1)) := by
  sorry

/-- (26.12.6): the number of cyclically symmetric plane partitions in `B(r, r, r)` is
`∏_{h=1}^r (3h-1)/(3h-2) ∏_{1≤h<j≤r} (h+2j-1)/(h+j-1)`. -/
@[dlmf 26.12.E6]
theorem card_cyclicallySymmetric_planePartitionsIn (r : ℕ) :
    ((planePartitionsIn r r r).filter IsCyclicallySymmetricPP).card =
      (∏ h ∈ Icc 1 r, ((3 * h - 1 : ℚ) / (3 * h - 2))) *
        ∏ h ∈ Icc 1 r, ∏ j ∈ Ioc h r, ((h + 2 * j - 1 : ℚ) / (h + j - 1)) := by
  sorry

/-- (26.12.7): the equivalent form `∏_{h=1}^r ((3h-1)/(3h-2) ∏_{j=h}^r (r+h+j-1)/(2h+j-1))`. -/
@[dlmf 26.12.E7]
theorem card_cyclicallySymmetric_planePartitionsIn' (r : ℕ) :
    ((planePartitionsIn r r r).filter IsCyclicallySymmetricPP).card =
      ∏ h ∈ Icc 1 r, (((3 * h - 1 : ℚ) / (3 * h - 2)) *
        ∏ j ∈ Icc h r, ((r + h + j - 1 : ℚ) / (2 * h + j - 1))) := by
  sorry

/-- (26.12.8): the number of totally symmetric plane partitions in `B(r, r, r)` is
`∏_{1≤h≤j≤r} (h+j+r-1)/(h+2j-2)`. -/
@[dlmf 26.12.E8]
theorem card_totallySymmetric_planePartitionsIn (r : ℕ) :
    ((planePartitionsIn r r r).filter IsTotallySymmetricPP).card =
      ∏ h ∈ Icc 1 r, ∏ j ∈ Icc h r, ((h + j + r - 1 : ℚ) / (h + 2 * j - 2)) := by
  sorry

/-- The box product `∏_{h=1}^r ∏_{j=1}^s (h+j+t-1)/(h+j-1)` of (26.12.4). -/
def planeBoxProduct (r s t : ℕ) : ℚ :=
  ∏ h ∈ Icc 1 r, ∏ j ∈ Icc 1 s, ((h + j + t - 1 : ℚ) / (h + j - 1))

/-- (26.12.9): the number of self-complementary plane partitions in `B(2r, 2s, 2t)` is
`(∏_{h=1}^r ∏_{j=1}^s (h+j+t-1)/(h+j-1))²`. -/
@[dlmf 26.12.E9]
theorem card_selfComplementary_even (r s t : ℕ) :
    ((planePartitionsIn (2 * r) (2 * s) (2 * t)).filter
        fun π => π = planeComplement (2 * r) (2 * s) (2 * t) π).card =
      planeBoxProduct r s t ^ 2 := by
  sorry

/-- (26.12.10): in `B(2r+1, 2s, 2t)` the number is
`(∏_{h=1}^r ∏_{j=1}^s …)(∏_{h=1}^{r+1} ∏_{j=1}^s …)`. -/
@[dlmf 26.12.E10]
theorem card_selfComplementary_odd_even (r s t : ℕ) :
    ((planePartitionsIn (2 * r + 1) (2 * s) (2 * t)).filter
        fun π => π = planeComplement (2 * r + 1) (2 * s) (2 * t) π).card =
      planeBoxProduct r s t * planeBoxProduct (r + 1) s t := by
  sorry

/-- (26.12.11): in `B(2r+1, 2s+1, 2t)` the number is
`(∏_{h=1}^{r+1} ∏_{j=1}^s …)(∏_{h=1}^r ∏_{j=1}^{s+1} …)`. -/
@[dlmf 26.12.E11]
theorem card_selfComplementary_odd_odd (r s t : ℕ) :
    ((planePartitionsIn (2 * r + 1) (2 * s + 1) (2 * t)).filter
        fun π => π = planeComplement (2 * r + 1) (2 * s + 1) (2 * t) π).card =
      planeBoxProduct (r + 1) s t * planeBoxProduct r (s + 1) t := by
  sorry

/-- (26.12.12): the number of transpose complement plane partitions in `B(r, r, 2t)` (complement
equal to the transpose; see the module docstring) is
`C(t+r-1, r-1) ∏_{1≤h≤j≤r-2} (h+j+2t+1)/(h+j+1)`, for `r ≥ 1`. -/
@[dlmf 26.12.E12 "clarified: transpose complement = complement equals transpose (h,j,k) ↦ (j,h,k)"]
theorem card_transposeComplement {r : ℕ} (hr : 1 ≤ r) (t : ℕ) :
    ((planePartitionsIn r r (2 * t)).filter
        fun π => planeComplement r r (2 * t) π = planeTranspose π).card =
      ((t + r - 1).choose (r - 1) : ℚ) *
        ∏ h ∈ Icc 1 (r - 2), ∏ j ∈ Icc h (r - 2), ((h + j + 2 * t + 1 : ℚ) / (h + j + 1)) := by
  sorry

/-- (26.12.13): the number of symmetric self-complementary plane partitions in `B(2r, 2r, 2t)`
is `∏_{h=1}^r ∏_{j=1}^r (h+j+t-1)/(h+j-1)`. -/
@[dlmf 26.12.E13]
theorem card_symmetric_selfComplementary_even (r t : ℕ) :
    ((planePartitionsIn (2 * r) (2 * r) (2 * t)).filter
        fun π => IsSymmetricPP π ∧ π = planeComplement (2 * r) (2 * r) (2 * t) π).card =
      planeBoxProduct r r t := by
  sorry

/-- (26.12.14): in `B(2r+1, 2r+1, 2t)` the number is `∏_{h=1}^r ∏_{j=1}^{r+1} …`. -/
@[dlmf 26.12.E14]
theorem card_symmetric_selfComplementary_odd (r t : ℕ) :
    ((planePartitionsIn (2 * r + 1) (2 * r + 1) (2 * t)).filter
        fun π => IsSymmetricPP π ∧ π = planeComplement (2 * r + 1) (2 * r + 1) (2 * t) π).card =
      planeBoxProduct r (r + 1) t := by
  sorry

/-- (26.12.15): the number of cyclically symmetric transpose complement plane partitions in
`B(2r, 2r, 2r)` is `∏_{h=0}^{r-1} (3h+1)(6h)!(2h)!/((4h+1)!(4h)!)`. -/
@[dlmf 26.12.E15]
theorem card_cyclicallySymmetric_transposeComplement (r : ℕ) :
    ((planePartitionsIn (2 * r) (2 * r) (2 * r)).filter fun π => IsCyclicallySymmetricPP π ∧
        planeComplement (2 * r) (2 * r) (2 * r) π = planeTranspose π).card =
      ∏ h ∈ range r, ((3 * h + 1) * (6 * h).factorial * (2 * h).factorial : ℚ) /
        ((4 * h + 1).factorial * (4 * h).factorial) := by
  sorry

/-- The product `∏_{h=0}^{r-1} (3h+1)!/(r+h)!` of (26.12.16), (26.12.17), (26.12.19). -/
def asmProduct (r : ℕ) : ℚ := ∏ h ∈ range r, ((3 * h + 1).factorial : ℚ) / (r + h).factorial

/-- (26.12.16): the number of cyclically symmetric self-complementary plane partitions in
`B(2r, 2r, 2r)` is `(∏_{h=0}^{r-1} (3h+1)!/(r+h)!)²`. -/
@[dlmf 26.12.E16]
theorem card_cyclicallySymmetric_selfComplementary (r : ℕ) :
    ((planePartitionsIn (2 * r) (2 * r) (2 * r)).filter fun π => IsCyclicallySymmetricPP π ∧
        π = planeComplement (2 * r) (2 * r) (2 * r) π).card = asmProduct r ^ 2 := by
  sorry

/-- (26.12.17): the number of totally symmetric self-complementary plane partitions in
`B(2r, 2r, 2r)` is `∏_{h=0}^{r-1} (3h+1)!/(r+h)!`. -/
@[dlmf 26.12.E17]
theorem card_totallySymmetric_selfComplementary (r : ℕ) :
    ((planePartitionsIn (2 * r) (2 * r) (2 * r)).filter fun π => IsTotallySymmetricPP π ∧
        π = planeComplement (2 * r) (2 * r) (2 * r) π).card = asmProduct r := by
  sorry

/-- A strict shifted plane partition (DLMF §26.12(i)): rows of positive integers, row `i`
indented `i` places, rows weakly decreasing, columns strictly decreasing; the row lengths are
strictly decreasing (each entry has an entry above it). Entry `p` of row `i+1` lies below entry
`p+1` of row `i`. -/
@[dlmf 26.12.i]
def IsStrictShiftedPP (d : List (List ℕ)) : Prop :=
  (∀ row ∈ d, row ≠ [] ∧ (∀ a ∈ row, 1 ≤ a) ∧ row.Pairwise (· ≥ ·)) ∧
    ∀ i (hi : i + 1 < d.length),
      (d[i + 1]).length < (d[i]).length ∧
        ∀ p (hp : p < (d[i + 1]).length), (d[i + 1])[p] < (d[i]).getD (p + 1) 0

/-- A descending plane partition (DLMF §26.12(i)): a strict shifted plane partition in which the
number of parts of each row is strictly less than the largest part of that row and at least the
largest part of the next row. -/
@[dlmf 26.12.i]
def IsDescendingPP (d : List (List ℕ)) : Prop :=
  IsStrictShiftedPP d ∧
    ∀ i (hi : i < d.length), (d[i]).length < (d[i]).headD 0 ∧
      ∀ hi' : i + 1 < d.length, (d[i + 1]).headD 0 ≤ (d[i]).length

/-- (26.12.18): the example `6 6 6 4 3 / 3 3 / 2` is a strict shifted (indeed descending) plane
partition. -/
@[dlmf 26.12.E18]
theorem isDescendingPP_example : IsDescendingPP [[6, 6, 6, 4, 3], [3, 3], [2]] := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro row hrow
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
    rcases hrow with rfl | rfl | rfl <;> refine ⟨by simp, by simp, by simp⟩
  · intro i hi
    have hi3 : i < 2 := by simp at hi; omega
    interval_cases i
    · refine ⟨by simp, fun p hp => ?_⟩
      have : p < 2 := by simpa using hp
      interval_cases p <;> simp
    · refine ⟨by simp, fun p hp => ?_⟩
      have : p = 0 := by simpa using hp
      subst this; simp
  · intro i hi
    have hi3 : i < 3 := by simp at hi; omega
    interval_cases i <;> simp

/-- The descending plane partitions with all parts at most `r` ("in `B(r, r, r)`"). -/
def DescendingPPIn (r : ℕ) : Type :=
  {d : List (List ℕ) // IsDescendingPP d ∧ ∀ row ∈ d, ∀ a ∈ row, a ≤ r}

/-- (26.12.19): the number of descending plane partitions in `B(r, r, r)` is
`∏_{h=0}^{r-1} (3h+1)!/(r+h)!`. -/
@[dlmf 26.12.E19]
theorem card_descendingPPIn (r : ℕ) : (Nat.card (DescendingPPIn r) : ℚ) = asmProduct r := by
  sorry

end DLMF.Combinatorics
end
end
