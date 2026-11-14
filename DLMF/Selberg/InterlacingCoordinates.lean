/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Interlacing roots and simplex residue coordinates

Andrews, Askey and Roy, *Special Functions*, Lemmas 8.4.1–8.4.3,
pp. 411–414. The residues are explicit rational products, and the last
simplex coordinate is omitted when taking the Jacobian determinant.
-/

@[expose] public noncomputable section

open Finset

namespace DLMF.Selberg

/-- The residue at `a_j` of the monic root quotient associated to interlacing roots.
Andrews–Askey–Roy, *Special Functions*, Lemmas 8.4.1–8.4.3, pp. 411–414
(synopsis AAR-8.4.1–8.4.4). -/
def interlacingResidue {n : ℕ} (a : Fin (n + 1) → ℝ) (t : Fin n → ℝ)
    (j : Fin (n + 1)) : ℝ :=
  (∏ i : Fin n, (a j - t i)) / ∏ k : Fin (n + 1) with k ≠ j, (a j - a k)

/-- The explicit product defining the interlacing residue. -/
theorem interlacingResidue_def {n : ℕ} (a : Fin (n + 1) → ℝ) (t : Fin n → ℝ)
    (j : Fin (n + 1)) :
    interlacingResidue a t j =
      (∏ i : Fin n, (a j - t i)) / ∏ k : Fin (n + 1) with k ≠ j, (a j - a k) := rfl

/-- Interlacing residues are positive and sum to one. Andrews–Askey–Roy,
*Special Functions*, Lemma 8.4.1, pp. 411–412 (synopsis AAR-8.4.1–8.4.4). -/
theorem interlacingResidue_pos_sum {n : ℕ} (a : Fin (n + 1) → ℝ)
    (ha : StrictAnti a) (t : Fin n → ℝ)
    (ht : ∀ i : Fin n, a i.succ < t i ∧ t i < a i.castSucc) :
    (∀ j, 0 < interlacingResidue a t j) ∧ (∑ j, interlacingResidue a t j) = 1 := by
  sorry

/-- Every point of the open probability simplex determines exactly one interlacing
root vector. Andrews–Askey–Roy, *Special Functions*, Lemmas 8.4.1–8.4.2,
pp. 411–413 (synopsis AAR-8.4.1–8.4.4). -/
theorem existsUnique_interlacing_roots_of_residues {n : ℕ} (a : Fin (n + 1) → ℝ)
    (ha : StrictAnti a) (u : Fin (n + 1) → ℝ) (hu : ∀ j, 0 < u j)
    (hsum : ∑ j, u j = 1) :
    ∃! t : Fin n → ℝ,
      (∀ i : Fin n, a i.succ < t i ∧ t i < a i.castSucc) ∧
        ∀ j, interlacingResidue a t j = u j := by
  sorry

/-- The derivative and absolute Jacobian determinant of the residue coordinates.
Andrews–Askey–Roy, *Special Functions*, Lemma 8.4.3, pp. 413–414
(synopsis AAR-8.4.1–8.4.4). The determinant uses the first `n` residues;
the omitted last coordinate is fixed by their sum being one. -/
theorem interlacingResidue_jacobian {n : ℕ} (a : Fin (n + 1) → ℝ)
    (ha : StrictAnti a) (t : Fin n → ℝ)
    (ht : ∀ i : Fin n, a i.succ < t i ∧ t i < a i.castSucc) :
    (∀ j : Fin n, HasFDerivAt (fun v : Fin n → ℝ => interlacingResidue a v j.castSucc)
      (∑ i : Fin n, (-interlacingResidue a t j.castSucc / (a j.castSucc - t i)) •
        (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)) t) ∧
    |Matrix.det (fun j i : Fin n => -interlacingResidue a t j.castSucc /
      (a j.castSucc - t i))| =
      (∏ i : Fin n, ∏ j : Fin n, if i < j then t i - t j else 1) /
        ∏ i : Fin (n + 1), ∏ j : Fin (n + 1), if i < j then a i - a j else 1 := by
  sorry

end DLMF.Selberg
