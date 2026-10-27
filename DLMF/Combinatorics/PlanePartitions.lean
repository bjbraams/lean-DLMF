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
# Plane partitions (DLMF §26.12)

A plane partition is, following DLMF §26.12(i), a finite set `π ⊆ ℕ × ℕ × ℕ` of points with
positive coordinates such that `(r, s, t) ∈ π` implies `B(r, s, t) ⊆ π` (`IsPlanePartition`),
where `B(r, s, t) = [1, r] × [1, s] × [1, t]` (`planeBox`, (26.12.3)); `|π|` is `π.card`. The
array description (weakly decreasing rows and columns) is the equivalent form of §26.12(i),
acquired as `planePartitionCount_eq_card_arrays`. `pp(n)` is `planePartitionCount n`.

Symmetry classes (all inside a box): symmetric (`(h, j, k) ∈ π → (j, h, k) ∈ π`), cyclically
symmetric (`(h, j, k) ∈ π → (j, k, h) ∈ π`), totally symmetric, the complement
`π^c = {(h, j, k) ∈ B | (r-h+1, s-j+1, t-k+1) ∉ π}` (`planeComplement`), self-complementary
(`π = π^c`) and transpose complement (`π^c` equals the transpose of `π`).

Strict shifted and descending plane partitions are lists of rows (`List (List ℕ)`), row `i`
indented by `i` places (`IsStrictShiftedPP`, `IsDescendingPP`). A descending plane partition
"in `B(r, r, r)`" is one with all parts at most `r`.

Counts in boxes are stated as rational numbers (`ℚ`), as DLMF's products are.

Corrections and clarifications (verified by brute force):

* §26.12(i), transpose complement: DLMF says "equal to the reflection through the `(x, y)`-plane
  of its complement". The count (26.12.12) is that of plane partitions whose complement is their
  transpose `(h, j, k) ↦ (j, h, k)` (reflection in the plane `x = y`); with the literal
  reflection `k ↦ t + 1 - k` the counts differ (`r = 1`, `t = 1`: none versus one). The
  transpose reading is acquired.
* (26.12.24): the product must run over `1 ≤ h ≤ j ≤ r`, not `1 ≤ h < j ≤ r`. As printed, for
  `r = 2` the right side is `(1 - q⁴)/(1 - q³)`, not a polynomial, whereas the descending plane
  partitions with parts at most 2 are `∅` and `(2)`, with generating function `1 + q²`; at
  `q = 1` the printed product does not reproduce (26.12.19). The corrected product matches for
  `r ≤ 5`.
* 26.12.27 (decimal values of `ζ(3)`, `ζ'(-1)`) and Table 26.12.1 are numerical and not acquired.

## References

* NIST DLMF §26.12.
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
def s26b_IsPPArray (n : ℕ) (a : ℕ → ℕ → ℕ) : Prop :=
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
lemma s26b_array_bound {n : ℕ} {a : ℕ → ℕ → ℕ} (ha : s26b_IsPPArray n a) {i j : ℕ}
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
lemma s26b_fiber_ofArr {n : ℕ} {a : ℕ → ℕ → ℕ} (ha : s26b_IsPPArray n a) {h k : ℕ}
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
lemma s26b_ofArr_mem {n : ℕ} {a : ℕ → ℕ → ℕ} (ha : s26b_IsPPArray n a) :
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
  change _ = Nat.card {a : ℕ → ℕ → ℕ // s26b_IsPPArray n a}
  rw [planePartitionCount, ← Nat.card_eq_finsetCard]
  -- forward map facts
  have hfwd : ∀ π : Finset (ℕ × ℕ × ℕ), π ∈ {π ∈ (planeBox n n n).powerset |
      IsPlanePartition π ∧ π.card = n} → s26b_IsPPArray n (s26b_toArr n π) := by
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

instance (π : Finset (ℕ × ℕ × ℕ)) : Decidable (IsSymmetricPP π) := by
  unfold IsSymmetricPP; infer_instance
instance (π : Finset (ℕ × ℕ × ℕ)) : Decidable (IsCyclicallySymmetricPP π) := by
  unfold IsCyclicallySymmetricPP; infer_instance
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

/-! ### The recurrence (26.12.25)

From the box formula for `B(n, n, n)` modulo `X^(n+1)`, `G · ∏_{m ≤ n} (1 - X^m)^m ≡ 1`, where
`G = ∑ X^{|π|}` has the coefficients `pp(k)`, `k ≤ n`; applying the Euler operator `θ = X d/dX`
gives `θ G ≡ G · ∑_{m ≤ n} m² ∑_{l ≤ n} X^{ml}`. -/

section Recurrence

open Polynomial

/-- Truncation ideal `(X^(N+1))` of `ℤ[X]`. -/
abbrev s26b_I (N : ℕ) : Ideal ℤ[X] := Ideal.span {(X : ℤ[X]) ^ (N + 1)}

/-- The quotient map modulo `X^(N+1)`. -/
abbrev s26b_mk (N : ℕ) : ℤ[X] →+* ℤ[X] ⧸ s26b_I N := Ideal.Quotient.mk (s26b_I N)

/-- `X^e` vanishes modulo `X^(N+1)` for `e ≥ N + 1`. -/
lemma s26b_mk_X_pow {N e : ℕ} (he : N + 1 ≤ e) : s26b_mk N ((X : ℤ[X]) ^ e) = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  exact pow_dvd_pow _ he

/-- Congruent polynomials modulo `X^(N+1)` share their coefficients up to `N`. -/
lemma s26b_coeff_eq_of_mk_eq {N : ℕ} {A B : ℤ[X]} (h : s26b_mk N A = s26b_mk N B) {n : ℕ}
    (hn : n ≤ N) : A.coeff n = B.coeff n := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at h
  obtain ⟨C, hC⟩ := h
  have := congrArg (fun p => p.coeff n) hC
  simp only [coeff_sub, coeff_X_pow_mul'] at this
  split_ifs at this with hh
  · omega
  · omega

/-- The Euler operator `θ = X d/dX`. -/
def s26b_θ (A : ℤ[X]) : ℤ[X] := X * derivative A

/-- `θ` is a derivation. -/
lemma s26b_θ_mul (A B : ℤ[X]) : s26b_θ (A * B) = s26b_θ A * B + A * s26b_θ B := by
  simp only [s26b_θ, derivative_mul]; ring

/-- `θ` preserves congruence modulo `X^(N+1)`. -/
lemma s26b_mk_θ {N : ℕ} {A B : ℤ[X]} (h : s26b_mk N A = s26b_mk N B) :
    s26b_mk N (s26b_θ A) = s26b_mk N (s26b_θ B) := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at h ⊢
  obtain ⟨C, hC⟩ := h
  refine ⟨(N + 1 : ℤ[X]) * C + X * derivative C, ?_⟩
  rw [s26b_θ, s26b_θ, ← mul_sub, ← derivative_sub, hC, derivative_mul, derivative_X_pow]
  simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, map_add, map_one, map_natCast]
  ring

/-- Logarithmic derivative of a product modulo `X^(N+1)`. -/
lemma s26b_mk_θ_prod {N : ℕ} {ι : Type*} (s : Finset ι) (g c : ι → ℤ[X])
    (h : ∀ i ∈ s, s26b_mk N (s26b_θ (g i)) = s26b_mk N (g i * c i)) :
    s26b_mk N (s26b_θ (∏ i ∈ s, g i)) = s26b_mk N ((∏ i ∈ s, g i) * ∑ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [s26b_θ]
  | insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha, s26b_θ_mul, map_add, map_mul, map_mul,
      h a (mem_insert_self a s), ih fun i hi => h i (mem_insert_of_mem hi)]
    simp only [map_mul, map_add]
    ring

/-- A plane partition lies in the cube of side `|π|`. -/
lemma s26b_subset_planeBox_card {π : Finset (ℕ × ℕ × ℕ)} (hπ : IsPlanePartition π) :
    π ⊆ planeBox #π #π #π := by
  rintro ⟨h, j, k⟩ hx
  obtain ⟨h1, j1, k1, -⟩ := hπ _ hx
  have c1 : (Icc 1 h).image (fun i => (i, 1, 1)) ⊆ π := by
    intro y hy
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hy
    rw [mem_Icc] at hi
    exact s26b_down hπ hx hi.1 hi.2 le_rfl j1 le_rfl k1
  have c2 : (Icc 1 j).image (fun i => (1, i, 1)) ⊆ π := by
    intro y hy
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hy
    rw [mem_Icc] at hi
    exact s26b_down hπ hx le_rfl h1 hi.1 hi.2 le_rfl k1
  have c3 : (Icc 1 k).image (fun i => (1, 1, i)) ⊆ π := by
    intro y hy
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hy
    rw [mem_Icc] at hi
    exact s26b_down hπ hx le_rfl h1 le_rfl j1 hi.1 hi.2
  have e1 := card_le_card c1
  have e2 := card_le_card c2
  have e3 := card_le_card c3
  rw [card_image_of_injective _ (fun a b hab => (Prod.mk.inj hab).1)] at e1
  rw [card_image_of_injective _ (fun a b hab => (Prod.mk.inj (Prod.mk.inj hab).2).1)] at e2
  rw [card_image_of_injective _ (fun a b hab => (Prod.mk.inj (Prod.mk.inj hab).2).2)] at e3
  simp only [Nat.card_Icc, Nat.add_sub_cancel] at e1 e2 e3
  exact s26b_mem_planeBox.mpr ⟨h1, e1, j1, e2, k1, e3⟩

/-- The box generating polynomial has `pp(n)` as its coefficients up to the side length. -/
lemma s26b_coeff_boxPoly {N n : ℕ} (hn : n ≤ N) :
    (∑ π ∈ planePartitionsIn N N N, (X : ℤ[X]) ^ #π).coeff n = planePartitionCount n := by
  simp only [finsetSum_coeff, coeff_X_pow]
  rw [sum_boole, planePartitionCount]
  congr 2
  ext π
  simp only [mem_filter, s26b_mem_planePartitionsIn, mem_powerset]
  constructor
  · rintro ⟨⟨_, hπ⟩, rfl⟩
    exact ⟨s26b_subset_planeBox_card hπ, hπ, rfl⟩
  · rintro ⟨hsub, hπ, rfl⟩
    refine ⟨⟨hsub.trans fun x hx => ?_, hπ⟩, rfl⟩
    rw [planeBox, mem_product, mem_product, mem_Icc, mem_Icc, mem_Icc] at hx ⊢
    omega

/-- Regrouping the box denominator modulo `X^(N+1)`. -/
lemma s26b_mk_denom (N : ℕ) :
    s26b_mk N (∏ h ∈ Icc 1 N, ∏ k ∈ Icc 1 N, (1 - (X : ℤ[X]) ^ (h + k - 1))) =
      s26b_mk N (∏ m ∈ Icc 1 N, (1 - (X : ℤ[X]) ^ m) ^ m) := by
  set f : ℕ → ℤ[X] ⧸ s26b_I N := fun m => s26b_mk N (1 - X ^ m) with hf
  have hf1 : ∀ m, N + 1 ≤ m → f m = 1 := fun m hm => by
    simp only [hf, map_sub, map_one, s26b_mk_X_pow hm, sub_zero]
  simp only [map_prod, map_pow]
  change ∏ h ∈ Icc 1 N, ∏ k ∈ Icc 1 N, f (h + k - 1) = ∏ m ∈ Icc 1 N, f m ^ m
  have hin : ∀ h ∈ Icc 1 N, ∏ k ∈ Icc 1 N, f (h + k - 1) = ∏ m ∈ Icc h N, f m := by
    intro h hh
    rw [mem_Icc] at hh
    have : ∏ k ∈ Icc 1 N, f (h + k - 1) = ∏ k ∈ Icc 1 (N + 1 - h), f (h + k - 1) := by
      symm
      refine prod_subset (fun k hk => by simp only [mem_Icc] at hk ⊢; omega) fun k hk hk' => ?_
      simp only [mem_Icc] at hk hk'
      exact hf1 _ (by omega)
    rw [this]
    refine prod_nbij' (fun k => h + k - 1) (fun m => m + 1 - h) ?_ ?_ ?_ ?_ fun _ _ => rfl
    · intro k hk; simp at hk ⊢; omega
    · intro m hm; simp at hm ⊢; omega
    · intro k hk; simp at hk; omega
    · intro m hm; simp at hm; omega
  rw [prod_congr rfl hin, prod_comm' (t' := Icc 1 N) (s' := fun m => Icc 1 m)]
  · refine prod_congr rfl fun m _ => ?_
    rw [prod_const, Nat.card_Icc, Nat.add_sub_cancel]
  · intro h m
    simp only [mem_Icc]
    omega

/-- The truncated divisor series `T_m = ∑_{l=1}^{N} X^{ml}`. -/
def s26b_T (N m : ℕ) : ℤ[X] := ∑ l ∈ range N, X ^ (m * (l + 1))

/-- `θ (1 - X^m)^m ≡ -(1 - X^m)^m m² T_m` modulo `X^(N+1)`. -/
lemma s26b_mk_θ_factor {N m : ℕ} (hm : 1 ≤ m) :
    s26b_mk N (s26b_θ ((1 - (X : ℤ[X]) ^ m) ^ m)) =
      s26b_mk N ((1 - (X : ℤ[X]) ^ m) ^ m * (-(C ((m : ℤ) ^ 2)) * s26b_T N m)) := by
  have htel : (1 - (X : ℤ[X]) ^ m) * s26b_T N m = X ^ m - X ^ (m * (N + 1)) := by
    rw [s26b_T, mul_sum]
    have := sum_range_sub (fun l => -(X : ℤ[X]) ^ (m * (l + 1))) N
    simp only [neg_sub_neg] at this
    rw [show ∑ l ∈ range N, (1 - (X : ℤ[X]) ^ m) * X ^ (m * (l + 1)) =
        ∑ l ∈ range N, ((X : ℤ[X]) ^ (m * (l + 1)) - X ^ (m * (l + 1 + 1))) from
      sum_congr rfl fun l _ => by ring, this]
    ring
  have hz : s26b_mk N ((X : ℤ[X]) ^ (m * (N + 1))) = 0 :=
    s26b_mk_X_pow (by nlinarith)
  have hθ : s26b_θ ((1 - (X : ℤ[X]) ^ m) ^ m) =
      -(C ((m : ℤ) ^ 2)) * (1 - X ^ m) ^ (m - 1) * X ^ m := by
    rw [s26b_θ, derivative_pow, derivative_sub, derivative_one, derivative_X_pow]
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp only [Nat.add_sub_cancel, map_pow, map_natCast]
    ring
  rw [hθ]
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [show (1 - (X : ℤ[X]) ^ (m' + 1)) ^ (m' + 1) * (-(C (((m' + 1 : ℕ) : ℤ) ^ 2)) *
      s26b_T N (m' + 1)) = -(C (((m' + 1 : ℕ) : ℤ) ^ 2)) * (1 - X ^ (m' + 1)) ^ m' *
      ((1 - X ^ (m' + 1)) * s26b_T N (m' + 1)) by ring, htel]
  simp only [Nat.add_sub_cancel, map_mul, map_sub, hz, sub_zero]

/-- Coefficients of `∑_{m ≤ N} m² T_m` are `σ₂`. -/
lemma s26b_coeff_S {N j : ℕ} (hj : 1 ≤ j) (hjN : j ≤ N) :
    (∑ m ∈ Icc 1 N, C ((m : ℤ) ^ 2) * s26b_T N m).coeff j = ArithmeticFunction.sigma 2 j := by
  simp only [finsetSum_coeff, coeff_C_mul, s26b_T, coeff_X_pow]
  rw [ArithmeticFunction.sigma_apply, Nat.cast_sum]
  have : ∀ m ∈ Icc 1 N, ((m : ℤ) ^ 2 * ∑ l ∈ range N, if j = m * (l + 1) then (1 : ℤ) else 0) =
      if m ∣ j then (m : ℤ) ^ 2 else 0 := by
    intro m hm
    rw [mem_Icc] at hm
    rw [sum_boole]
    split_ifs with hd
    · obtain ⟨c, rfl⟩ := hd
      have hc : 1 ≤ c := by rcases c with _ | c <;> simp_all
      have : (range N).filter (fun l => m * c = m * (l + 1)) = {c - 1} := by
        ext l
        simp only [mem_filter, mem_range, mem_singleton]
        constructor
        · rintro ⟨_, h⟩
          have := Nat.eq_of_mul_eq_mul_left (by omega) h
          omega
        · rintro rfl
          refine ⟨?_, by rw [Nat.sub_add_cancel hc]⟩
          have : c ≤ m * c := Nat.le_mul_of_pos_left c (by omega)
          omega
      rw [this, card_singleton]; simp
    · have : (range N).filter (fun l => j = m * (l + 1)) = ∅ := by
        ext l
        simp only [mem_filter, mem_range, notMem_empty, iff_false, not_and]
        intro _ h
        exact hd ⟨_, h⟩
      rw [this]; simp
  rw [sum_congr rfl this, ← sum_filter]
  push_cast
  refine sum_congr ?_ fun _ _ => rfl
  ext m
  simp only [mem_filter, mem_Icc, Nat.mem_divisors]
  constructor
  · rintro ⟨_, h⟩; exact ⟨h, by omega⟩
  · rintro ⟨h, _⟩
    have := Nat.le_of_dvd (by omega) h
    have : 0 < m := Nat.pos_of_dvd_of_pos h (by omega)
    omega

/-- The recurrence (26.12.25) (helper used before its statement). -/
lemma s26b_pp_recurrence (n : ℕ) :
    n * planePartitionCount n =
      ∑ j ∈ Icc 1 n, planePartitionCount (n - j) * ArithmeticFunction.sigma 2 j := by
  set G : ℤ[X] := ∑ π ∈ planePartitionsIn n n n, (X : ℤ[X]) ^ #π with hG
  set E : ℤ[X] := ∏ m ∈ Icc 1 n, (1 - (X : ℤ[X]) ^ m) ^ m with hE
  set S : ℤ[X] := ∑ m ∈ Icc 1 n, C ((m : ℤ) ^ 2) * s26b_T n m with hS
  -- `G E ≡ 1`
  have hGE : s26b_mk n (G * E) = s26b_mk n 1 := by
    have hb := congrArg (s26b_mk n) (s26b_box_poly n n n)
    rw [map_mul, s26b_mk_denom, ← map_mul] at hb
    rw [hb, map_prod, map_one]
    refine prod_eq_one fun h hh => ?_
    rw [map_prod]
    refine prod_eq_one fun k hk => ?_
    simp only [mem_Icc] at hh hk
    rw [map_sub, map_one, s26b_mk_X_pow (by omega), sub_zero]
  -- `θ E ≡ -E S`
  have hθE : s26b_mk n (s26b_θ E) = s26b_mk n (E * -S) := by
    rw [hE, s26b_mk_θ_prod _ _ (fun m : ℕ => -(C ((m : ℤ) ^ 2)) * s26b_T n m)
      (fun m hm => s26b_mk_θ_factor (mem_Icc.mp hm).1), hS, ← sum_neg_distrib]
    simp only [neg_mul]
  have hθ1 : s26b_mk n (s26b_θ (G * E)) = 0 := by
    rw [s26b_mk_θ hGE]; simp [s26b_θ]
  rw [s26b_θ_mul, map_add, map_mul, map_mul, hθE, map_mul, map_neg] at hθ1
  rw [map_mul, map_one] at hGE
  have key : s26b_mk n (s26b_θ G) = s26b_mk n (G * S) := by
    rw [map_mul]
    linear_combination (s26b_mk n G) * hθ1 +
      (s26b_mk n G * s26b_mk n S - s26b_mk n (s26b_θ G)) * hGE
  have hc := s26b_coeff_eq_of_mk_eq key (le_refl n)
  -- read off coefficient `n`
  have hl : (s26b_θ G).coeff n = n * planePartitionCount n := by
    rcases n with _ | m
    · simp [s26b_θ]
    · rw [s26b_θ, coeff_X_mul, coeff_derivative, s26b_coeff_boxPoly le_rfl]
      push_cast; ring
  have hr : (G * S).coeff n =
      ∑ j ∈ Icc 1 n, (planePartitionCount (n - j) * ArithmeticFunction.sigma 2 j : ℤ) := by
    have hS0 : S.coeff 0 = 0 := by
      rw [hS, finsetSum_coeff]
      refine sum_eq_zero fun m hm => ?_
      rw [coeff_C_mul, s26b_T, finsetSum_coeff, sum_eq_zero, mul_zero]
      intro l _
      simp only [mem_Icc] at hm
      have := Nat.mul_pos (by omega : 0 < m) (by omega : 0 < l + 1)
      rw [coeff_X_pow]
      split_ifs with h
      · omega
      · rfl
    rw [mul_comm, coeff_mul,
      Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => S.coeff i * G.coeff j), range_eq_Ico,
      sum_eq_sum_Ico_succ_bot (by omega), hS0, zero_mul, zero_add,
      show Ico (0 + 1) (n + 1) = Icc 1 n by ext; simp]
    refine sum_congr rfl fun j hj => ?_
    rw [mem_Icc] at hj
    rw [s26b_coeff_S hj.1 hj.2, s26b_coeff_boxPoly (by omega)]
    ring
  have := hl.symm.trans (hc.trans hr)
  exact_mod_cast this

end Recurrence

/-! ### MacMahon's generating function (26.12.20)

`pp(n) ρⁿ` is bounded by the recurrence, so `∑ pp(n) qⁿ` converges for `|q| < 1`; it is the limit
of the box sums `∑_{π ⊆ B(N,N,N)} q^{|π|}`, which by (26.12.21) are
`∏_{h,j ≤ N} (1 - q^{h+j+N-1})/(1 - q^{h+j-1})`, and these tend to MacMahon's product. -/

section GenFun

open Filter Topology

/-- `σ₂(j) ≤ j³`. -/
lemma s26b_sigma_two_le (j : ℕ) : ArithmeticFunction.sigma 2 j ≤ j ^ 3 := by
  rw [ArithmeticFunction.sigma_apply]
  calc ∑ d ∈ j.divisors, d ^ 2 ≤ ∑ _d ∈ j.divisors, j ^ 2 :=
        sum_le_sum fun d hd => Nat.pow_le_pow_left (Nat.divisor_le hd) 2
    _ = #j.divisors * j ^ 2 := by rw [sum_const, smul_eq_mul]
    _ ≤ j * j ^ 2 := Nat.mul_le_mul_right _ (Nat.card_divisors_le_self j)
    _ = j ^ 3 := by ring

/-- `pp(n) ρⁿ` is bounded for `0 < ρ < 1` (from the recurrence (26.12.25)). -/
lemma s26b_pp_bound {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n, (planePartitionCount n : ℝ) * ρ ^ n ≤ B := by
  have hsum : Summable fun j : ℕ => ((j : ℝ) ^ 3 * ρ ^ j) :=
    summable_pow_mul_geometric_of_norm_lt_one 3
      (by rw [Real.norm_eq_abs, abs_of_pos hρ0]; exact hρ1)
  set K := ∑' j : ℕ, ((j : ℝ) ^ 3 * ρ ^ j) with hK
  have hpart : ∀ n, ∑ j ∈ Icc 1 n, (ArithmeticFunction.sigma 2 j : ℝ) * ρ ^ j ≤ K := by
    intro n
    calc ∑ j ∈ Icc 1 n, (ArithmeticFunction.sigma 2 j : ℝ) * ρ ^ j
        ≤ ∑ j ∈ Icc 1 n, ((j : ℝ) ^ 3 * ρ ^ j) := sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_right (by exact_mod_cast s26b_sigma_two_le j) (by positivity)
      _ ≤ K := hsum.sum_le_tsum _ fun j _ => by positivity
  set K0 := ⌈K⌉₊
  set B := ∑ n ∈ range (K0 + 1), (planePartitionCount n : ℝ) * ρ ^ n
  have hB0 : 0 ≤ B := sum_nonneg fun n _ => by positivity
  refine ⟨B, hB0, fun n => ?_⟩
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n ≤ K0
    · exact single_le_sum (f := fun n => (planePartitionCount n : ℝ) * ρ ^ n)
        (fun n _ => by positivity) (mem_range.mpr (by omega))
    · push Not at hn
      have hrec := s26b_pp_recurrence n
      have hrecR : (n : ℝ) * ((planePartitionCount n : ℝ) * ρ ^ n) =
          ∑ j ∈ Icc 1 n, ((planePartitionCount (n - j) : ℝ) * ρ ^ (n - j)) *
            ((ArithmeticFunction.sigma 2 j : ℝ) * ρ ^ j) := by
        rw [← mul_assoc]
        have : ((n * planePartitionCount n : ℕ) : ℝ) =
            ((∑ j ∈ Icc 1 n, planePartitionCount (n - j) * ArithmeticFunction.sigma 2 j : ℕ) :
              ℝ) := by rw [hrec]
        push_cast at this
        rw [this, sum_mul]
        refine sum_congr rfl fun j hj => ?_
        rw [mem_Icc] at hj
        rw [show ρ ^ n = ρ ^ (n - j) * ρ ^ j by rw [← pow_add, Nat.sub_add_cancel hj.2]]
        ring
      have hle : (n : ℝ) * ((planePartitionCount n : ℝ) * ρ ^ n) ≤ B * n := by
        rw [hrecR]
        calc ∑ j ∈ Icc 1 n, ((planePartitionCount (n - j) : ℝ) * ρ ^ (n - j)) *
              ((ArithmeticFunction.sigma 2 j : ℝ) * ρ ^ j)
            ≤ ∑ j ∈ Icc 1 n, B * ((ArithmeticFunction.sigma 2 j : ℝ) * ρ ^ j) := by
              refine sum_le_sum fun j hj => ?_
              rw [mem_Icc] at hj
              exact mul_le_mul_of_nonneg_right (ih _ (by omega)) (by positivity)
          _ = B * ∑ j ∈ Icc 1 n, (ArithmeticFunction.sigma 2 j : ℝ) * ρ ^ j := by
              rw [mul_sum]
          _ ≤ B * K := mul_le_mul_of_nonneg_left (hpart n) hB0
          _ ≤ B * n := by
              refine mul_le_mul_of_nonneg_left ?_ hB0
              have := Nat.le_ceil K
              have : (K0 : ℝ) < n := by exact_mod_cast hn
              linarith
      have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      nlinarith

/-- Summability of `pp(n) qⁿ` for `|q| < 1`. -/
lemma s26b_summable_pp {q : ℂ} (hq : ‖q‖ < 1) :
    Summable fun n => ‖(planePartitionCount n : ℂ) * q ^ n‖ := by
  obtain ⟨ρ, hqρ, hρ1⟩ := exists_between hq
  have hρ0 : 0 < ρ := lt_of_le_of_lt (norm_nonneg q) hqρ
  obtain ⟨B, hB0, hB⟩ := s26b_pp_bound hρ0 hρ1
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    ((summable_geometric_of_lt_one (div_nonneg (norm_nonneg q) hρ0.le)
      ((div_lt_one hρ0).mpr hqρ)).mul_left B)
  rw [norm_mul, norm_pow, Complex.norm_natCast, div_pow]
  have := hB n
  have hρn : 0 < ρ ^ n := pow_pos hρ0 n
  rw [mul_div_assoc', le_div_iff₀ hρn]
  calc (planePartitionCount n : ℝ) * ‖q‖ ^ n * ρ ^ n
      = ((planePartitionCount n : ℝ) * ρ ^ n) * ‖q‖ ^ n := by ring
    _ ≤ B * ‖q‖ ^ n := mul_le_mul_of_nonneg_right this (by positivity)

/-- `1 - qᵐ ≠ 0` for `|q| < 1`, `m > 0`. -/
lemma s26b_one_sub_pow_ne_zero {q : ℂ} (hq : ‖q‖ < 1) {m : ℕ} (hm : 0 < m) : 1 - q ^ m ≠ 0 := by
  intro h
  have : ‖q ^ m‖ = 1 := by rw [← sub_eq_zero.mp h, norm_one]
  rw [norm_pow] at this
  have : ‖q‖ ^ m < 1 := pow_lt_one₀ (norm_nonneg q) hq hm.ne'
  linarith

/-- MacMahon's product `∏ (1 - q^{k+1})^{-(k+1)}` converges, as an exponential of a sum. -/
lemma s26b_hasProd_macMahon {q : ℂ} (hq : ‖q‖ < 1) :
    ∃ A : ℂ, HasProd (fun k : ℕ => ((1 - q ^ (k + 1)) ^ (k + 1))⁻¹) (Complex.exp A) := by
  set a : ℕ → ℂ := fun k => -(((k + 1 : ℕ) : ℂ) * Complex.log (1 - q ^ (k + 1))) with ha
  have h0 : Summable fun n : ℕ => (n : ℝ) ^ 1 * ‖q‖ ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one 1 (r := ‖q‖) (by rw [norm_norm]; exact hq)
  have h1 : Summable fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ 1 * ‖q‖ ^ (n + 1) :=
    (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ 1 * ‖q‖ ^ n) 1).mpr h0
  have hsg : Summable fun k : ℕ => (3 / 2 : ℝ) * (((k + 1 : ℕ) : ℝ) ^ 1 * ‖q‖ ^ (k + 1)) :=
    h1.mul_left _
  have hev : ∀ᶠ k : ℕ in atTop, ‖q‖ ^ (k + 1) ≤ 1 / 2 := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg q) hq).comp
      (tendsto_add_atTop_nat 1)
    exact (this.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
  have hs : Summable a := by
    refine Summable.of_norm_bounded_eventually_nat hsg ?_
    filter_upwards [hev] with k hk
    rw [ha, norm_neg, norm_mul, Complex.norm_natCast, sub_eq_add_neg]
    have := Complex.norm_log_one_add_half_le_self (z := -q ^ (k + 1)) (by rwa [norm_neg, norm_pow])
    rw [norm_neg, norm_pow] at this
    rw [pow_one]
    nlinarith [norm_nonneg (Complex.log (1 + -q ^ (k + 1)))]
  refine ⟨∑' k, a k, ?_⟩
  have := hs.hasSum.cexp
  convert this using 1
  funext k
  simp only [Function.comp, ha, Complex.exp_neg, Complex.exp_nat_mul,
    Complex.exp_log (s26b_one_sub_pow_ne_zero hq (Nat.succ_pos k))]

/-- Products `∏ (1 - wᵢ)` over finite families with `∑ ‖wᵢ‖ → 0` tend to `1`. -/
lemma s26b_tendsto_prod_one_sub {ι : Type*} (s : ℕ → Finset ι) (w : ℕ → ι → ℂ)
    (hw : ∀ᶠ N in atTop, ∀ x ∈ s N, ‖w N x‖ ≤ 1 / 2)
    (hsum : Tendsto (fun N => ∑ x ∈ s N, ‖w N x‖) atTop (𝓝 0)) :
    Tendsto (fun N => ∏ x ∈ s N, (1 - w N x)) atTop (𝓝 1) := by
  have hL : Tendsto (fun N => ∑ x ∈ s N, Complex.log (1 + -w N x)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) ?_
      (by simpa using hsum.const_mul (3 / 2 : ℝ))
    filter_upwards [hw] with N hN
    refine (norm_sum_le _ _).trans ?_
    rw [mul_sum]
    refine sum_le_sum fun x hx => ?_
    have := Complex.norm_log_one_add_half_le_self (z := -w N x) (by rw [norm_neg]; exact hN x hx)
    rwa [norm_neg] at this
  have hE := (Complex.continuous_exp.tendsto 0).comp hL
  rw [Complex.exp_zero] at hE
  refine hE.congr' ?_
  filter_upwards [hw] with N hN
  simp only [Function.comp, Complex.exp_sum]
  refine prod_congr rfl fun x hx => ?_
  rw [Complex.exp_log, sub_eq_add_neg]
  intro h
  have h1 : ‖w N x‖ = 1 := by
    rw [← norm_neg, show -w N x = 1 + -w N x - 1 by ring, h, zero_sub, norm_neg, norm_one]
  have := hN x hx
  linarith

/-- Regrouping `∏_{h,k ≤ N} f(h+k-1) = ∏_{m ≤ N} f(m)^m` when `f = 1` beyond `N`. -/
lemma s26b_prod_regroup {M : Type*} [CommMonoid M] (N : ℕ) (f : ℕ → M)
    (hf1 : ∀ m, N + 1 ≤ m → f m = 1) :
    ∏ h ∈ Icc 1 N, ∏ k ∈ Icc 1 N, f (h + k - 1) = ∏ m ∈ Icc 1 N, f m ^ m := by
  have hin : ∀ h ∈ Icc 1 N, ∏ k ∈ Icc 1 N, f (h + k - 1) = ∏ m ∈ Icc h N, f m := by
    intro h hh
    rw [mem_Icc] at hh
    have : ∏ k ∈ Icc 1 N, f (h + k - 1) = ∏ k ∈ Icc 1 (N + 1 - h), f (h + k - 1) := by
      symm
      refine prod_subset (fun k hk => by simp only [mem_Icc] at hk ⊢; omega) fun k hk hk' => ?_
      simp only [mem_Icc] at hk hk'
      exact hf1 _ (by omega)
    rw [this]
    refine prod_nbij' (fun k => h + k - 1) (fun m => m + 1 - h) ?_ ?_ ?_ ?_ fun _ _ => rfl
    · intro k hk; simp at hk ⊢; omega
    · intro m hm; simp at hm ⊢; omega
    · intro k hk; simp at hk; omega
    · intro m hm; simp at hm; omega
  rw [prod_congr rfl hin, prod_comm' (t' := Icc 1 N) (s' := fun m => Icc 1 m)]
  · refine prod_congr rfl fun m _ => ?_
    rw [prod_const, Nat.card_Icc, Nat.add_sub_cancel]
  · intro h m
    simp only [mem_Icc]
    omega

/-- The number of plane partitions of `n` in `B(N, N, N)`. -/
def s26b_c (N n : ℕ) : ℕ := #{π ∈ planePartitionsIn N N N | π.card = n}

/-- `c_N(n) ≤ pp(n)`. -/
lemma s26b_c_le (N n : ℕ) : s26b_c N n ≤ planePartitionCount n := by
  refine card_le_card fun π hπ => ?_
  simp only [mem_filter, s26b_mem_planePartitionsIn, mem_powerset] at hπ ⊢
  obtain ⟨⟨_, hπ⟩, rfl⟩ := hπ
  exact ⟨s26b_subset_planeBox_card hπ, hπ, rfl⟩

/-- `c_N(n) = pp(n)` for `n ≤ N`. -/
lemma s26b_c_eq {N n : ℕ} (hn : n ≤ N) : s26b_c N n = planePartitionCount n := by
  have := s26b_coeff_boxPoly (N := N) hn
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_X_pow, sum_boole] at this
  rw [s26b_c]
  exact_mod_cast (congrArg (fun F => #F) (filter_congr fun π _ => eq_comm)).trans
    (by exact_mod_cast this)

/-- `∑_{π ⊆ B(N,N,N)} q^{|π|} = ∑ₙ c_N(n) qⁿ`. -/
lemma s26b_hasSum_c {q : ℂ} (N : ℕ) :
    HasSum (fun n => (s26b_c N n : ℂ) * q ^ n) (∑ π ∈ planePartitionsIn N N N, q ^ π.card) := by
  have hmaps : ∀ π ∈ planePartitionsIn N N N, π.card ∈ range (N ^ 3 + 1) := by
    intro π hπ
    have := card_le_card (s26b_mem_planePartitionsIn.mp hπ).1
    simp only [planeBox, card_product, Nat.card_Icc, Nat.add_sub_cancel] at this
    rw [mem_range]; nlinarith
  rw [← sum_fiberwise_of_maps_to hmaps]
  have : ∀ n ∈ range (N ^ 3 + 1), ∑ π ∈ planePartitionsIn N N N with π.card = n, q ^ π.card =
      (s26b_c N n : ℂ) * q ^ n := by
    intro n _
    rw [sum_congr rfl fun π hπ => by rw [(mem_filter.mp hπ).2], sum_const, nsmul_eq_mul, s26b_c]
  rw [sum_congr rfl this]
  refine hasSum_sum_of_ne_finset_zero fun n hn => ?_
  rw [s26b_c, card_eq_zero.mpr, Nat.cast_zero, zero_mul]
  refine filter_eq_empty_iff.mpr fun π hπ hc => hn ?_
  rw [← hc]; exact hmaps π hπ

/-- Double products `∏_{h,j ≤ N} (1 - w)` with `‖w‖ ≤ ‖q‖^{N+1}` tend to `1`. -/
lemma s26b_tendsto_box_prod {q : ℂ} (hq : ‖q‖ < 1) (w : ℕ → ℕ × ℕ → ℂ)
    (hw : ∀ N, ∀ x ∈ Icc 1 N ×ˢ Icc 1 N, ‖w N x‖ ≤ ‖q‖ ^ (N + 1)) :
    Tendsto (fun N => ∏ h ∈ Icc 1 N, ∏ j ∈ Icc 1 N, (1 - w N (h, j))) atTop (𝓝 1) := by
  simp only [← prod_product']
  have hq0 := norm_nonneg q
  refine s26b_tendsto_prod_one_sub (fun N => Icc 1 N ×ˢ Icc 1 N) w ?_ ?_
  · have := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq).comp (tendsto_add_atTop_nat 1)
    filter_upwards [this.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with N hN x hx
    exact (hw N x hx).trans hN
  · have hlim : Tendsto (fun N : ℕ => ‖q‖ * ((N : ℝ) ^ 2 * ‖q‖ ^ N)) atTop (𝓝 0) := by
      simpa using (tendsto_pow_const_mul_const_pow_of_abs_lt_one 2
        (by rw [abs_of_nonneg hq0]; exact hq)).const_mul ‖q‖
    refine squeeze_zero (fun N => sum_nonneg fun x _ => norm_nonneg _) (fun N => ?_) hlim
    calc ∑ x ∈ Icc 1 N ×ˢ Icc 1 N, ‖w N x‖ ≤ ∑ _x ∈ Icc 1 N ×ˢ Icc 1 N, ‖q‖ ^ (N + 1) :=
          sum_le_sum (hw N)
      _ = ‖q‖ * ((N : ℝ) ^ 2 * ‖q‖ ^ N) := by
          rw [sum_const, card_product, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
          push_cast; ring

end GenFun

open Topology in
/-- (26.12.20), MacMahon: `∑_π q^{|π|} = ∑ₙ pp(n) qⁿ = ∏_{k ≥ 1} (1 - q^k)^{-k}` for `|q| < 1`. -/
@[dlmf 26.12.E20]
theorem hasSum_planePartitionCount {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n => (planePartitionCount n : ℂ) * q ^ n)
        (∏' k : ℕ, ((1 - q ^ (k + 1)) ^ (k + 1))⁻¹) ∧
      HasProd (fun k : ℕ => ((1 - q ^ (k + 1)) ^ (k + 1))⁻¹)
        (∏' k : ℕ, ((1 - q ^ (k + 1)) ^ (k + 1))⁻¹) := by
  obtain ⟨A, hA⟩ := s26b_hasProd_macMahon hq
  rw [hA.tprod_eq]
  refine ⟨?_, hA⟩
  set F := Complex.exp A
  have hF0 : F ≠ 0 := Complex.exp_ne_zero A
  have hq0 := norm_nonneg q
  have hsP : Summable fun n => (planePartitionCount n : ℂ) * q ^ n :=
    (s26b_summable_pp hq).of_norm
  set GN : ℕ → ℂ := fun N => ∑ π ∈ planePartitionsIn N N N, q ^ π.card with hGN
  -- `GN → P`
  set u : ℕ → ℝ := fun n => ‖(planePartitionCount n : ℂ) * q ^ n‖ with hu
  have T1 : Tendsto GN atTop (𝓝 (∑' n, (planePartitionCount n : ℂ) * q ^ n)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hlim := (tendsto_sum_nat_add u).comp (tendsto_add_atTop_nat 1)
    refine squeeze_zero (fun N => norm_nonneg _) (fun N => ?_) hlim
    set d : ℕ → ℂ := fun n =>
      ((planePartitionCount n : ℂ) - s26b_c N n) * q ^ n with hd
    have hdsum : HasSum d (∑' n, (planePartitionCount n : ℂ) * q ^ n - GN N) := by
      have := hsP.hasSum.sub (s26b_hasSum_c (q := q) N)
      convert this using 1
      funext n; simp only [hd]; ring
    have hd0 : ∀ n < N + 1, d n = 0 := fun n hn => by
      simp only [hd, s26b_c_eq (Nat.lt_succ_iff.mp hn), sub_self, zero_mul]
    have hdle : ∀ n, ‖d n‖ ≤ u n := fun n => by
      simp only [hd, hu, norm_mul]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      rw [show ((planePartitionCount n : ℂ) - s26b_c N n) =
        ((planePartitionCount n - s26b_c N n : ℕ) : ℂ) by
          rw [Nat.cast_sub (s26b_c_le N n)], Complex.norm_natCast, Complex.norm_natCast]
      exact_mod_cast Nat.sub_le _ _
    have hshift := (hasSum_nat_add_iff' (f := d) (N + 1)).mpr hdsum
    rw [sum_eq_zero fun n hn => hd0 n (mem_range.mp hn), sub_zero] at hshift
    rw [norm_sub_rev, ← hshift.tsum_eq]
    have hus : Summable fun k => u (k + (N + 1)) :=
      (summable_nat_add_iff (N + 1)).mpr (s26b_summable_pp hq)
    refine (norm_tsum_le_tsum_norm (hus.of_nonneg_of_le (fun _ => norm_nonneg _)
      fun k => hdle _)).trans ?_
    exact Summable.tsum_le_tsum (fun k => hdle _)
      (hus.of_nonneg_of_le (fun _ => norm_nonneg _) fun k => hdle _) hus
  -- `GN → F`
  have hq' : ∀ m : ℕ, 0 < m → q ^ m ≠ 1 := fun m hm h =>
    s26b_one_sub_pow_ne_zero hq hm (by rw [h, sub_self])
  set Num : ℕ → ℂ := fun N => ∏ h ∈ Icc 1 N, ∏ j ∈ Icc 1 N, (1 - q ^ (h + j + N - 1))
  set Xt : ℕ → ℂ := fun N => ∏ h ∈ Icc 1 N, ∏ j ∈ Icc 1 N,
    (1 - (if N < h + j - 1 then q ^ (h + j - 1) else 0))
  set E : ℕ → ℂ := fun N => ∏ m ∈ Icc 1 N, (1 - q ^ m) ^ m
  have hG : ∀ N, GN N = Num N / (E N * Xt N) := by
    intro N
    have hden : ∏ h ∈ Icc 1 N, ∏ j ∈ Icc 1 N, (1 - q ^ (h + j - 1)) = E N * Xt N := by
      have hsplit : ∀ m : ℕ, (1 - q ^ m) = (if m ≤ N then 1 - q ^ m else 1) *
          (1 - (if N < m then q ^ m else 0)) := fun m => by
        split_ifs with h1 h2 h2 <;> first | omega | ring
      rw [prod_congr rfl fun h _ => prod_congr rfl fun j _ => hsplit (h + j - 1)]
      simp only [prod_mul_distrib]
      congr 1
      rw [s26b_prod_regroup N (fun m => if m ≤ N then 1 - q ^ m else 1)
        (fun m hm => by simp only [show ¬m ≤ N by omega, ↓reduceIte])]
      exact prod_congr rfl fun m hm => by simp only [(mem_Icc.mp hm).2, ↓reduceIte]
    show ∑ π ∈ planePartitionsIn N N N, q ^ π.card = _
    rw [s26b_sum_box_pow hq' N N N, ← hden]
    simp only [prod_div_distrib]
    rfl
  have hNum : Tendsto Num atTop (𝓝 1) := by
    refine s26b_tendsto_box_prod hq (fun N x => q ^ (x.1 + x.2 + N - 1)) fun N x hx => ?_
    simp only [mem_product, mem_Icc] at hx
    rw [norm_pow]
    exact pow_le_pow_of_le_one hq0 hq.le (by omega)
  have hXt : Tendsto Xt atTop (𝓝 1) := by
    refine s26b_tendsto_box_prod hq
      (fun N x => if N < x.1 + x.2 - 1 then q ^ (x.1 + x.2 - 1) else 0) fun N x hx => ?_
    split_ifs with h
    · rw [norm_pow]; exact pow_le_pow_of_le_one hq0 hq.le (by omega)
    · rw [norm_zero]; positivity
  have hE : Tendsto E atTop (𝓝 F⁻¹) := by
    refine (hA.tendsto_prod_nat.inv₀ hF0).congr fun N => ?_
    rw [← prod_inv_distrib]
    simp only [inv_inv]
    refine prod_nbij' (· + 1) (· - 1) ?_ ?_ ?_ ?_ fun _ _ => rfl
    · intro k hk; simp at hk ⊢; omega
    · intro m hm; simp at hm ⊢; omega
    · intro k hk; simp
    · intro m hm; simp at hm; omega
  have T2 : Tendsto GN atTop (𝓝 F) := by
    have := hNum.div (hE.mul hXt) (by simpa using hF0)
    rw [mul_one, one_div, inv_inv] at this
    exact this.congr fun N => (hG N).symm
  have := tendsto_nhds_unique T1 T2
  rw [← this]
  exact hsP.hasSum

/-- (26.12.21): `∑_{π ⊆ B(r,s,t)} q^{|π|} = ∏_{(h,j,k) ∈ B} (1-q^{h+j+k-1})/(1-q^{h+j+k-2})
= ∏_{h=1}^r ∏_{j=1}^s (1-q^{h+j+t-1})/(1-q^{h+j-1})`, for `q` not a root of unity. -/
@[dlmf 26.12.E21]
theorem sum_planePartitionsIn_pow {q : ℂ} (hq : ∀ m : ℕ, 0 < m → q ^ m ≠ 1) (r s t : ℕ) :
    ∑ π ∈ planePartitionsIn r s t, q ^ π.card =
        ∏ x ∈ planeBox r s t, (1 - q ^ (x.1 + x.2.1 + x.2.2 - 1)) /
          (1 - q ^ (x.1 + x.2.1 + x.2.2 - 2)) ∧
      ∑ π ∈ planePartitionsIn r s t, q ^ π.card =
        ∏ h ∈ Icc 1 r, ∏ j ∈ Icc 1 s, (1 - q ^ (h + j + t - 1)) / (1 - q ^ (h + j - 1)) := by
  have hne : ∀ m : ℕ, 0 < m → (1 - q ^ m) ≠ 0 := fun m hm h => hq m hm (sub_eq_zero.mp h).symm
  have h2 : ∑ π ∈ planePartitionsIn r s t, q ^ π.card =
      ∏ h ∈ Icc 1 r, ∏ j ∈ Icc 1 s, (1 - q ^ (h + j + t - 1)) / (1 - q ^ (h + j - 1)) :=
    s26b_sum_box_pow hq r s t
  refine ⟨h2.trans ?_, h2⟩
  rw [planeBox, prod_product]
  refine prod_congr rfl fun h hh => ?_
  rw [prod_product]
  refine prod_congr rfl fun j hj => ?_
  simp only [mem_Icc] at hh hj
  have := s26b_prod_Icc_div (fun k : ℕ => 1 - q ^ (h + j + k - 1)) t
    (fun k _ => hne _ (by omega))
  simp only [add_zero] at this
  rw [← this]
  refine prod_congr rfl fun k hk => ?_
  simp only [mem_Icc] at hk
  show _ = (1 - q ^ (h + j + k - 1)) / (1 - q ^ (h + j + k - 2))
  rw [show h + j + (k - 1) - 1 = h + j + k - 2 by omega]

/-- (26.12.22): `∑_{π ⊆ B(r,r,t) symmetric} q^{|π|} = ∏_{h=1}^r (1-q^{2h+t-1})/(1-q^{2h-1})
∏_{1≤h<j≤r} (1-q^{2(h+j+t-1)})/(1-q^{2(h+j-1)})`, for `q` not a root of unity. -/
@[dlmf 26.12.E22]
theorem sum_symmetric_planePartitionsIn_pow {q : ℂ} (hq : ∀ m : ℕ, 0 < m → q ^ m ≠ 1) (r t : ℕ) :
    ∑ π ∈ (planePartitionsIn r r t).filter IsSymmetricPP, q ^ π.card =
      (∏ h ∈ Icc 1 r, (1 - q ^ (2 * h + t - 1)) / (1 - q ^ (2 * h - 1))) *
        ∏ h ∈ Icc 1 r, ∏ j ∈ Ioc h r,
          (1 - q ^ (2 * (h + j + t - 1))) / (1 - q ^ (2 * (h + j - 1))) := by
  sorry

/-- (26.12.23): `∑_{π ⊆ B(r,r,r) cyclically symmetric} q^{|π|}` equals
`∏_{h=1}^r (1-q^{3h-1})/(1-q^{3h-2}) ∏_{1≤h<j≤r} (1-q^{3(h+2j-1)})/(1-q^{3(h+j-1)})` and
`∏_{h=1}^r ((1-q^{3h-1})/(1-q^{3h-2}) ∏_{j=h}^r (1-q^{3(r+h+j-1)})/(1-q^{3(2h+j-1)}))`, for `q`
not a root of unity. -/
@[dlmf 26.12.E23]
theorem sum_cyclicallySymmetric_planePartitionsIn_pow {q : ℂ}
    (hq : ∀ m : ℕ, 0 < m → q ^ m ≠ 1) (r : ℕ) :
    ∑ π ∈ (planePartitionsIn r r r).filter IsCyclicallySymmetricPP, q ^ π.card =
        (∏ h ∈ Icc 1 r, (1 - q ^ (3 * h - 1)) / (1 - q ^ (3 * h - 2))) *
          ∏ h ∈ Icc 1 r, ∏ j ∈ Ioc h r,
            (1 - q ^ (3 * (h + 2 * j - 1))) / (1 - q ^ (3 * (h + j - 1))) ∧
      ∑ π ∈ (planePartitionsIn r r r).filter IsCyclicallySymmetricPP, q ^ π.card =
        ∏ h ∈ Icc 1 r, ((1 - q ^ (3 * h - 1)) / (1 - q ^ (3 * h - 2)) *
          ∏ j ∈ Icc h r, (1 - q ^ (3 * (r + h + j - 1))) / (1 - q ^ (3 * (2 * h + j - 1)))) := by
  sorry

/-- (26.12.24), corrected: `∑ q^{|π|}` over the descending plane partitions in `B(r, r, r)` is
`∏_{1≤h≤j≤r} (1-q^{r+h+j-1})/(1-q^{2h+j-1})` (DLMF prints `h < j`; see the module docstring),
for `q` not a root of unity. -/
@[dlmf 26.12.E24 "corrected: product over 1 ≤ h ≤ j ≤ r (printed h < j)"]
theorem sum_descendingPPIn_pow {q : ℂ} (hq : ∀ m : ℕ, 0 < m → q ^ m ≠ 1) (r : ℕ) :
    ∑ᶠ d : DescendingPPIn r, q ^ (d.1.map List.sum).sum =
      ∏ h ∈ Icc 1 r, ∏ j ∈ Icc h r, (1 - q ^ (r + h + j - 1)) / (1 - q ^ (2 * h + j - 1)) := by
  sorry

/-- (26.12.25): `n pp(n) = ∑_{j=1}^n pp(n-j) σ₂(j)`, `σ₂(j)` the sum of the squares of the
divisors of `j` (stated multiplied by `n`). -/
@[dlmf 26.12.E25]
theorem planePartitionCount_recurrence (n : ℕ) :
    n * planePartitionCount n =
      ∑ j ∈ Icc 1 n, planePartitionCount (n - j) * ArithmeticFunction.sigma 2 j := by
  exact s26b_pp_recurrence n

/-- (26.12.26): `pp(n) ∼ ζ(3)^{7/36}/(2^{11/36} (3π)^{1/2} n^{25/36})
exp(3 ζ(3)^{1/3} (n/2)^{2/3} + ζ'(-1))` as `n → ∞`. -/
@[dlmf 26.12.E26]
theorem planePartitionCount_isEquivalent :
    (fun n : ℕ => (planePartitionCount n : ℝ)) ~[atTop] fun n : ℕ =>
      (riemannZeta 3).re ^ (7 / 36 : ℝ) /
          ((2 : ℝ) ^ (11 / 36 : ℝ) * Real.sqrt (3 * Real.pi) * (n : ℝ) ^ (25 / 36 : ℝ)) *
        Real.exp (3 * (riemannZeta 3).re ^ (1 / 3 : ℝ) * ((n : ℝ) / 2) ^ (2 / 3 : ℝ) +
          (deriv riemannZeta (-1)).re) := by
  sorry

end DLMF.Combinatorics
