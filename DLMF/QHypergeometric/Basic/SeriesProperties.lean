/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.Basic.Series

/-!
# Basic properties of the general basic hypergeometric series

This file proves the value at the origin of the general unilateral series `rφs` and its
agreement with the phase-free series `DLMF.QSeries.basicHG` when `r = s + 1`.

## Main results

* `qPhi_zero`: `rφs(a; b; q, 0) = 1`.
* `qPhi_eq_basicHG`: `qPhi` agrees with `DLMF.QSeries.basicHG` when `r = s + 1`.

## Implementation notes

Convergence, termination, classical limits and analyticity are in
`DLMF.QHypergeometric.Convergence`.
-/

@[expose] public noncomputable section
namespace DLMF.QHypergeometric

/-- At zero, every unilateral basic hypergeometric series consists only of its constant term. -/
@[simp] theorem qPhi_zero (a b : List ℂ) (q : ℂ) : qPhi a b q 0 = 1 := by
  unfold qPhi
  rw [tsum_eq_single 0]
  · simp [qPhiTerm, qPochhammerList, DLMF.QSeries.TripleProduct.tri]
  · intro n hn
    simp [qPhiTerm, zero_pow hn]

/-- The general definition agrees with the existing phase-free basicHG when r=s+1. -/
theorem qPhi_eq_basicHG {a b : List ℂ} (h : a.length=b.length+1) (q z : ℂ) :
    qPhi a b q z=DLMF.QSeries.basicHG a b q z := by
  have he : qPhiExponent a b=0 := by simp only [qPhiExponent]; omega
  unfold qPhi DLMF.QSeries.basicHG
  apply tsum_congr
  intro n
  simp [qPhiTerm, qPochhammerList, he]

end DLMF.QHypergeometric
