/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Data.Finset.Prod

/-!
# Plane partitions (DLMF §26.12(i))

Plane partitions as finite down-closed sets of lattice points with positive coordinates, their
count `pp(n)`, the symmetry classes, and strict shifted and descending plane partitions.

## Main definitions

* `planeBox`: the box `B(r, s, t)` (DLMF 26.12.3).
* `IsPlanePartition`, `planePartitionsIn`, `planePartitionCount`: plane partitions, those in a
  box, and `pp(n)`.
* `IsSymmetricPP`, `IsCyclicallySymmetricPP`, `IsTotallySymmetricPP`: the symmetry classes.
* `planeComplement`, `planeTranspose`: the complement `π^c` in a box and the transpose.
* `IsStrictShiftedPP`, `IsDescendingPlanePartition`, `DescendingPlanePartitionIn`: strict shifted
  and descending plane partitions, as lists of rows, row `i` indented by `i` places.

## Main results

* `mem_planePartitionsIn`, `mem_planeBox`, `mem_of_isPlanePartition_of_le`: membership and
  down-closure.
* `planePartitionCount_zero`, `planePartitionCount_one_two`: `pp(0) = 1`, `pp(1) = 1`,
  `pp(2) = 3`.

## Implementation notes

MacMahon's box formula, the symmetry-class counts and the generating functions are in
`DLMF.Combinatorics.PlanePartitions.BoxFormula` and
`DLMF.Combinatorics.PlanePartitions.GeneratingFunctions`.
-/

@[expose] public section

noncomputable section

open Finset

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

/-- Membership in `planePartitionsIn`. -/
lemma mem_planePartitionsIn {r s t : ℕ} {π : Finset (ℕ × ℕ × ℕ)} :
    π ∈ planePartitionsIn r s t ↔ π ⊆ planeBox r s t ∧ IsPlanePartition π := by
  simp [planePartitionsIn]

/-- Membership in `planeBox`. -/
lemma mem_planeBox {r s t h j k : ℕ} :
    (h, j, k) ∈ planeBox r s t ↔ 1 ≤ h ∧ h ≤ r ∧ 1 ≤ j ∧ j ≤ s ∧ 1 ≤ k ∧ k ≤ t := by
  simp [planeBox, and_assoc]

/-- Down-closure of a plane partition. -/
lemma mem_of_isPlanePartition_of_le {π : Finset (ℕ × ℕ × ℕ)} (hπ : IsPlanePartition π)
    {h j k h' j' k' : ℕ}
    (hx : (h, j, k) ∈ π) (h1 : 1 ≤ h') (h2 : h' ≤ h) (j1 : 1 ≤ j') (j2 : j' ≤ j) (k1 : 1 ≤ k')
    (k2 : k' ≤ k) : (h', j', k') ∈ π :=
  (hπ _ hx).2.2.2 (mem_planeBox.mpr ⟨h1, h2, j1, j2, k1, k2⟩)

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
def IsDescendingPlanePartition (d : List (List ℕ)) : Prop :=
  IsStrictShiftedPP d ∧
    ∀ i (hi : i < d.length), (d[i]).length < (d[i]).headD 0 ∧
      ∀ hi' : i + 1 < d.length, (d[i + 1]).headD 0 ≤ (d[i]).length

/-- The descending plane partitions with all parts at most `r` ("in `B(r, r, r)`"). -/
def DescendingPlanePartitionIn (r : ℕ) : Type :=
  {d : List (List ℕ) // IsDescendingPlanePartition d ∧ ∀ row ∈ d, ∀ a ∈ row, a ≤ r}

end DLMF.Combinatorics

end

end
