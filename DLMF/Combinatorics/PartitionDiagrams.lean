/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Combinatorics.PartitionRefinements
public import Mathlib.Combinatorics.Enumerative.Partition.YoungDiagram
public import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Explicit diagonal hooks and formal Durfee decomposition

Andrews, Askey and Roy, *Special Functions*, §11.5, pp. 563–566,
synopsis AAR-11.5.1–11.7. The diagram is Mathlib's canonical Young diagram.
-/

@[expose] public noncomputable section

open scoped Classical PowerSeries.WithPiTopology

namespace DLMF.Combinatorics

/-- The multiset of hook lengths of diagonal cells in the partition's Young diagram.
Andrews–Askey–Roy, §11.5, synopsis AAR-11.5.1–11.7. Cells use zero-based row and column indices. -/
def diagonalHookLengths {n : ℕ} (p : Nat.Partition n) : Multiset ℕ :=
  ((Multiset.range n).filter (fun i => (i, i) ∈ YoungDiagram.ofPartition p)).map
    (fun i => (YoungDiagram.ofPartition p).rowLen i +
      (YoungDiagram.ofPartition p).colLen i - (2 * i + 1))

/-- The finite definition of the diagonal hook multiset. -/
theorem diagonalHookLengths_def {n : ℕ} (p : Nat.Partition n) :
    diagonalHookLengths p =
      ((Multiset.range n).filter (fun i => (i, i) ∈ YoungDiagram.ofPartition p)).map
        (fun i => (YoungDiagram.ofPartition p).rowLen i +
          (YoungDiagram.ofPartition p).colLen i - (2 * i + 1)) := rfl

/-- Membership in the hook multiset is witnessed by an actual diagonal cell. -/
theorem mem_diagonalHookLengths_iff {n a : ℕ} (p : Nat.Partition n) :
    a ∈ diagonalHookLengths p ↔ ∃ i, i < n ∧ (i, i) ∈ YoungDiagram.ofPartition p ∧
      (YoungDiagram.ofPartition p).rowLen i + (YoungDiagram.ofPartition p).colLen i -
        (2 * i + 1) = a := by
  simp [diagonalHookLengths, Multiset.mem_map, Multiset.mem_filter, and_assoc]

/-- The classical self-conjugate/distinct-odd bijection sends a partition to its actual diagonal
hook lengths, rather than merely asserting equinumerosity. Andrews–Askey–Roy,
§11.5, synopsis AAR-11.5.1–11.7. -/
theorem exists_equiv_selfConjugate_distinct_odd_diagonalHooks (n : ℕ) :
    ∃ e : {p : n.Partition // p.conjugate = p} ≃
      {p : n.Partition // p.parts.Nodup ∧ ∀ a ∈ p.parts, Odd a},
      ∀ p, (e p).val.parts = diagonalHookLengths p.val := by
  sorry

/-- The Durfee-square identity is a coefficientwise formal power-series identity.
Andrews–Askey–Roy, §11.5, synopsis AAR-11.5.1–11.7. Each coefficient receives only finitely
many summands, and every finite denominator has constant coefficient one. -/
theorem hasSum_durfee_square_formal :
    HasSum (fun m : ℕ => (PowerSeries.X : PowerSeries ℚ) ^ (m ^ 2) *
      (∏ j : Fin m, (1 - (PowerSeries.X : PowerSeries ℚ) ^ (j.val + 1)))⁻¹ ^ 2)
      ((PowerSeries.pentagonalSeries ℚ)⁻¹) := by
  sorry

end DLMF.Combinatorics
