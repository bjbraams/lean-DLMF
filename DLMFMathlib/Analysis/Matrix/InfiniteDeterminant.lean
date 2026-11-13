/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams, The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Minor
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
import TauCeti.Analysis.Matrix.FiniteCompression
import TauCeti.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Infinite determinants with absolutely summable entries

The principal minors of an absolutely summable matrix form a summable family. Consequently,
finite coordinate determinants of `1 + A` converge to the sum of all principal minors.
The proof bounds minors by products of row sums and bounds their total sum by an exponential.

The finite-compression coefficient formula and the absolute-value Hadamard inequality are
from TauCeti. The reversed-characteristic-polynomial evaluation proof adapts the argument of
TauCeti's `Matrix.eval_one_charpolyRev` from `TauCeti.LinearAlgebra.Matrix.Charpoly.Reverse`.

## Main results

* `Matrix.summable_principalMinor_of_summable_norm`: summability of principal minors.
* `Matrix.det_one_add_submatrix_eq_sum_principalMinor`: finite principal-minor expansion.
* `Matrix.tendsto_det_one_add_submatrix_of_summable_norm`: convergence of finite determinants.
-/

public section

open Finset Filter Topology
namespace Matrix

/-- Absolute summability of all entries implies summability of all principal minors. -/
lemma summable_principalMinor_of_summable_norm {ι R : Type*} [DecidableEq ι]
    [NormedField R] [CompleteSpace R] (A : Matrix ι ι R)
    (hA : Summable (fun ij : ι × ι => ‖A ij.1 ij.2‖)) :
    Summable (fun s : Finset ι => A.principalMinor s) := by
  let r : ι → ℝ := fun i => ∑' j, ‖A i j‖
  have hrpos (i : ι) : 0 ≤ r i := tsum_nonneg fun _ => norm_nonneg _
  obtain ⟨hrow, hr⟩ := (summable_prod_of_nonneg (fun ij => norm_nonneg (A ij.1 ij.2))).mp hA
  have hbound (s : Finset ι) : ‖A.principalMinor s‖ ≤ ∏ i ∈ s, r i := by
    rw [principalMinor_def]
    have h := Matrix.abv_det_le_prod_sum_abv
      (A.submatrix (Subtype.val : s → ι) Subtype.val)
      (IsAbsoluteValue.toAbsoluteValue (norm : R → ℝ))
    simp only [IsAbsoluteValue.toAbsoluteValue_apply, submatrix_apply] at h
    apply h.trans
    rw [← prod_coe_sort s r]
    apply Finset.prod_le_prod₀
    · intro i _
      exact sum_nonneg fun _ _ => norm_nonneg _
    · intro i _
      have hsum := (hrow i.val).sum_le_tsum s (fun _ _ => norm_nonneg _)
      calc
        _ = ∑ j ∈ s, ‖A i.val j‖ := sum_coe_sort s _
        _ ≤ r i.val := hsum
  have hprod : Summable (fun s : Finset ι => ∏ i ∈ s, r i) := by
    apply summable_of_sum_le (fun s => prod_nonneg fun i _ => hrpos i)
      (c := Real.exp (∑' i, r i))
    intro U
    let V : Finset ι := U.biUnion id
    calc
      _ ≤ ∑ s ∈ V.powerset, ∏ i ∈ s, r i := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro s hs
          rw [mem_powerset]
          intro i hi
          exact mem_biUnion.mpr ⟨s, hs, hi⟩
        · intro s _ _
          exact prod_nonneg fun i _ => hrpos i
      _ = ∏ i ∈ V, (1 + r i) := (prod_one_add V).symm
      _ ≤ ∏ i ∈ V, Real.exp (r i) := by
        apply Finset.prod_le_prod₀
        · intro i _; positivity
        · intro i _; linarith [Real.add_one_le_exp (r i)]
      _ = Real.exp (∑ i ∈ V, r i) := (Real.exp_sum V r).symm
      _ ≤ _ := Real.exp_le_exp.mpr (hr.sum_le_tsum V (fun _ _ => hrpos _))
  exact hprod.of_norm_bounded hbound

/-- A finite determinant of `1 + A` is the sum of its principal minors. -/
lemma det_one_add_submatrix_eq_sum_principalMinor {ι R : Type*} [DecidableEq ι]
    [CommRing R] (A : Matrix ι ι R) (S : Finset ι) :
    (1 + A.submatrix (Subtype.val : S → ι) Subtype.val).det =
      ∑ s ∈ S.powerset, A.principalMinor s := by
  let M : Matrix S S R := A.submatrix Subtype.val Subtype.val
  have hdeg : M.charpolyRev.natDegree < S.card + 1 :=
    (natDegree_charpolyRev_le M).trans_lt (by simp)
  calc
    _ = M.charpolyRev.eval (-1) := by
      -- Evaluate the determinant as in TauCeti's `Matrix.eval_one_charpolyRev`.
      rw [charpolyRev, ← Polynomial.coe_evalRingHom, RingHom.map_det]
      congr 1
      ext i j
      by_cases h : i = j <;> simp [h, M]
    _ = ∑ k ∈ range (S.card + 1), M.charpolyRev.coeff k * (-1 : R) ^ k :=
      Polynomial.eval_eq_sum_range' hdeg (-1)
    _ = ∑ k ∈ range (S.card + 1), ∑ s ∈ S.powersetCard k, A.principalMinor s := by
      apply sum_congr rfl
      intro k _
      dsimp only [M]
      rw [TauCeti.coeff_charpolyRev_finiteCompression]
      calc
        _ = ((-1 : R) ^ k * (-1) ^ k) * ∑ s ∈ S.powersetCard k, A.principalMinor s := by ring
        _ = _ := by rw [← mul_pow]; simp
    _ = _ := (Finset.sum_powerset S _).symm

/-- Finite coordinate determinants converge to the principal-minor series when the matrix
entries are absolutely summable. -/
lemma tendsto_det_one_add_submatrix_of_summable_norm {ι R : Type*} [DecidableEq ι]
    [NormedField R] [CompleteSpace R] (A : Matrix ι ι R)
    (hA : Summable (fun ij : ι × ι => ‖A ij.1 ij.2‖)) :
    Tendsto (fun S : Finset ι => (1 + A.submatrix (Subtype.val : S → ι) Subtype.val).det)
      atTop (𝓝 (∑' s : Finset ι, A.principalMinor s)) := by
  have h := (summable_principalMinor_of_summable_norm A hA).hasSum.comp
    tendsto_finset_powerset_atTop_atTop
  simpa only [Function.comp_def, det_one_add_submatrix_eq_sum_principalMinor] using h

end Matrix

