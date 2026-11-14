/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Combinatorics.RestrictedPartitions
public import DLMF.Combinatorics.PartitionIdentities
public import DLMF.QSeries.Basic

/-!
# Partition refinements and Ferrers-diagram identities

Andrews, Askey and Roy, *Special Functions*, Chapter 11. The existing Mathlib
partition type and local gap predicate are reused. The counts here refine these
by exact length, least part or bounded multiplicity.
-/

@[expose] public section

open Finset
open DLMF.QSeries
open scoped Classical PowerSeries.WithPiTopology

noncomputable section

namespace DLMF.Combinatorics

/-- Partitions with parts in a set and multiplicities at most a fixed bound.
Andrews–Askey–Roy, *Special Functions*, §11.1 (synopsis AAR-11.1.1–11.3.1). -/
def partitionCountMultiplicityIn (S : Set ℕ) (r n : ℕ) : ℕ :=
  #{p : n.Partition | ∀ a ∈ p.parts, a ∈ S ∧ p.parts.count a ≤ r}

/-- The finite bounded-multiplicity count. -/
theorem partitionCountMultiplicityIn_def (S : Set ℕ) (r n : ℕ) :
    partitionCountMultiplicityIn S r n =
      #{p : n.Partition | ∀ a ∈ p.parts, a ∈ S ∧ p.parts.count a ≤ r} := rfl

/-- Partitions of an exact length, a minimum gap, and a minimum part.
Andrews–Askey–Roy, *Special Functions*, Theorem 11.4.2
(synopsis AAR-11.4.1–11.4.6). -/
def partitionCountExactGap (k l m n : ℕ) : ℕ :=
  #{p : n.Partition | p.parts.card = m ∧ PartsDifferAtLeast k p ∧ ∀ a ∈ p.parts, l ≤ a}

/-- The exact-length, gap and least-part conditions defining the count. -/
theorem partitionCountExactGap_def (k l m n : ℕ) :
    partitionCountExactGap k l m n =
      #{p : n.Partition | p.parts.card = m ∧ PartsDifferAtLeast k p ∧
        ∀ a ∈ p.parts, l ≤ a} := rfl

/-- The generating product for restricted bounded multiplicities.
Andrews–Askey–Roy, *Special Functions*, §11.1 (synopsis AAR-11.1.1–11.3.1). -/
theorem hasProd_partitionCountMultiplicityIn (S : Set ℕ) (r : ℕ)
    {q : ℂ} (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ => (partitionCountMultiplicityIn S r n : ℂ) * q ^ n) ∧
      HasProd (fun j : ℕ => if j + 1 ∈ S then
        (1 - q ^ ((r + 1) * (j + 1))) / (1 - q ^ (j + 1)) else 1)
        (∑' n : ℕ, (partitionCountMultiplicityIn S r n : ℂ) * q ^ n) := by
  sorry

/-- The coefficientwise formal generating product for bounded multiplicities.
Andrews–Askey–Roy, *Special Functions*, §11.1 (synopsis AAR-11.1.1–11.3.1). -/
theorem hasProd_partitionCountMultiplicityIn_formal (S : Set ℕ) (r : ℕ) :
    HasProd (fun j : ℕ => if j + 1 ∈ S then
      ∑ k ∈ Finset.range (r + 1), (PowerSeries.X : PowerSeries ℤ) ^ ((j + 1) * k)
      else 1)
      (PowerSeries.mk (fun n : ℕ => (partitionCountMultiplicityIn S r n : ℤ))) := by
  sorry

/-- The formal staircase identity with its finite denominator multiplied through.
Andrews–Askey–Roy, *Special Functions*, Theorem 11.4.2
(synopsis AAR-11.4.1–11.4.6). -/
theorem partitionCountExactGap_formal (k m : ℕ) {l : ℕ} (hl : 1 ≤ l) :
    PowerSeries.mk (fun n : ℕ => (partitionCountExactGap k l m n : ℤ)) *
        (∏ j : Fin m, (1 - (PowerSeries.X : PowerSeries ℤ) ^ (j.val + 1))) =
      (PowerSeries.X : PowerSeries ℤ) ^ (l * m + k * m * (m - 1) / 2) := by
  sorry

/-- The staircase generating function for exact length and minimum gap.
Andrews–Askey–Roy, *Special Functions*, Theorems 11.4.1–11.4.2
(synopsis AAR-11.4.1–11.4.6). -/
theorem hasSum_partitionCountExactGap (k m : ℕ) {l : ℕ} (hl : 1 ≤ l)
    {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ => (partitionCountExactGap k l m n : ℂ) * q ^ n)
      (q ^ (l * m + k * m * (m - 1) / 2) / qPochhammer q q m) := by
  sorry

/-- The two-variable length generating function for unrestricted partitions.
Andrews–Askey–Roy, *Special Functions*, Theorem 11.4.6
(synopsis AAR-11.4.1–11.4.6). -/
theorem hasSum_partitionCountExactGap_zero_bivariate {q z : ℂ}
    (hq : ‖q‖ < 1) (hzq : ‖z * q‖ < 1) :
    HasSum (fun mn : ℕ × ℕ =>
      (partitionCountExactGap 0 1 mn.1 mn.2 : ℂ) * z ^ mn.1 * q ^ mn.2)
      ((qPochhammerInf (z * q) q)⁻¹) := by
  sorry

/-- The two-variable length generating function for distinct partitions.
Andrews–Askey–Roy, *Special Functions*, Theorem 11.4.6
(synopsis AAR-11.4.1–11.4.6). -/
theorem hasSum_partitionCountExactGap_one_bivariate {q : ℂ}
    (hq : ‖q‖ < 1) (z : ℂ) :
    HasSum (fun mn : ℕ × ℕ =>
      (partitionCountExactGap 1 1 mn.1 mn.2 : ℂ) * z ^ mn.1 * q ^ mn.2)
      (qPochhammerInf (-z * q) q) := by
  sorry

/-- The bivariate gap-two series before Rogers–Ramanujan specialization.
Andrews–Askey–Roy, *Special Functions*, Theorem 11.4.6
(synopsis AAR-11.4.1–11.4.6). -/
theorem hasSum_partitionCountExactGap_two_bivariate {q : ℂ}
    (hq : ‖q‖ < 1) {l : ℕ} (hl : 1 ≤ l) (z : ℂ) :
    HasSum (fun mn : ℕ × ℕ =>
      (partitionCountExactGap 2 l mn.1 mn.2 : ℂ) * z ^ mn.1 * q ^ mn.2)
      (∑' m : ℕ, z ^ m * q ^ (l * m + m * (m - 1)) / qPochhammer q q m) := by
  sorry

/-- The Durfee-square decomposition of the unrestricted partition product.
Andrews–Askey–Roy, *Special Functions*, §11.5
(synopsis AAR-11.5.1–11.7). -/
theorem hasSum_durfee_square {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun m : ℕ => q ^ (m ^ 2) / qPochhammer q q m ^ 2)
      ((qPochhammerInf q q)⁻¹) := by
  sorry

/-- Self-conjugate partitions and partitions into distinct odd parts are equinumerous.
Andrews–Askey–Roy, *Special Functions*, §11.5
(synopsis AAR-11.5.1–11.7). -/
theorem nonempty_equiv_selfConjugate_distinct_odd (n : ℕ) :
    Nonempty ({p : n.Partition // p.conjugate = p} ≃
      {p : n.Partition // p.parts.Nodup ∧ ∀ a ∈ p.parts, Odd a}) := by
  sorry

/-- The number of positive integer triangles with ordered side lengths and perimeter n.
Andrews–Askey–Roy, *Special Functions*, §11.2 (synopsis AAR-11.1.1–11.3.1). -/
def trianglePartitionCount (n : ℕ) : ℕ :=
  #{v : Fin 3 → Fin (n + 1) | (v 1).val ≤ (v 0).val ∧ (v 2).val ≤ (v 1).val ∧
    1 ≤ (v 2).val ∧ (v 0).val < (v 1).val + (v 2).val ∧ ∑ i, (v i).val = n}

/-- The finite ordered-side count. -/
theorem trianglePartitionCount_def (n : ℕ) :
    trianglePartitionCount n =
      #{v : Fin 3 → Fin (n + 1) | (v 1).val ≤ (v 0).val ∧ (v 2).val ≤ (v 1).val ∧
        1 ≤ (v 2).val ∧ (v 0).val < (v 1).val + (v 2).val ∧ ∑ i, (v i).val = n} := rfl

/-- The rational generating function for ordered integer triangles.
Andrews–Askey–Roy, *Special Functions*, §11.2 (synopsis AAR-11.1.1–11.3.1). -/
theorem hasSum_trianglePartitionCount {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ => (trianglePartitionCount n : ℂ) * q ^ n)
      (q ^ 3 / ((1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4))) := by
  sorry

end DLMF.Combinatorics
