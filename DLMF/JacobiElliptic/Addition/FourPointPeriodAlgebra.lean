/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.JacobiElliptic.Basic.Definitions
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Polynomial identities for Jacobi four-point determinants

The two corrected determinants of DLMF 22.8.22–22.8.23 vanish after the triple-addition
formulas are substituted and the last row is multiplied by the common denominator squared.
The calculation reduces powers of cn and dn using the two quadratic Jacobi relations.
Mathlib's determinant expansion and polynomial normalization check the resulting identities.
-/

open Complex Matrix
public section
namespace DLMF.JacobiElliptic.FourPointAddition

set_option maxRecDepth 100000

set_option maxHeartbeats 0 in
/-- The cleared Jacobi determinant with sn in its third column. -/
lemma det_two_K_sn_polynomial (m s0 c0 d0 s1 c1 d1 s2 c2 d2 : ℂ)
    (hc0 : c0 ^ 2 = 1 - s0 ^ 2) (hd0 : d0 ^ 2 = 1 - m * s0 ^ 2)
    (hc1 : c1 ^ 2 = 1 - s1 ^ 2) (hd1 : d1 ^ 2 = 1 - m * s1 ^ 2)
    (hc2 : c2 ^ 2 = 1 - s2 ^ 2) (hd2 : d2 ^ 2 = 1 - m * s2 ^ 2) :
    let D := 1 - m * s0 ^ 2 * s1 ^ 2
    let A := s0 * c1 * d1 + s1 * c0 * d0
    let B := c0 * c1 - s0 * s1 * d0 * d1
    let C := d0 * d1 - m * s0 * s1 * c0 * c1
    let E := D ^ 2 - m * A ^ 2 * s2 ^ 2
    let Ns := A * c2 * d2 * D + s2 * B * C
    let Nc := B * c2 * D - A * s2 * C * d2
    let Nd := C * d2 * D - m * A * s2 * B * c2
    Matrix.det !![s0 * c0, c0 * d0, s0, d0; s1 * c1, c1 * d1, s1, d1; s2 * c2, c2 * d2, s2, d2;
      -Ns * Nc, -Nc * Nd, Ns * E, Nd * E] = 0 := by
  dsimp only
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix_apply, Matrix.of_apply]
  norm_num [Fin.succAbove]
  have powers (x a : ℂ) (hx : x ^ 2 = a) :
      x ^ 3 = a * x ∧ x ^ 4 = a ^ 2 ∧ x ^ 5 = a ^ 2 * x := by
    have h4 : x ^ 4 = a ^ 2 := by
      calc x ^ 4 = (x ^ 2) ^ 2 := by ring
           _ = a ^ 2 := by rw [hx]
    refine ⟨?_, h4, ?_⟩
    · rw [pow_succ, hx]
    · rw [pow_succ, h4]
  obtain ⟨hc03, hc04, hc05⟩ := powers c0 (1 - s0 ^ 2) hc0
  obtain ⟨hd03, hd04, hd05⟩ := powers d0 (1 - m * s0 ^ 2) hd0
  obtain ⟨hc13, hc14, hc15⟩ := powers c1 (1 - s1 ^ 2) hc1
  obtain ⟨hd13, hd14, hd15⟩ := powers d1 (1 - m * s1 ^ 2) hd1
  obtain ⟨hc23, _, _⟩ := powers c2 (1 - s2 ^ 2) hc2
  obtain ⟨hd23, _, _⟩ := powers d2 (1 - m * s2 ^ 2) hd2
  ring_nf
  simp only [hc0, hd0, hc1, hd1, hc2, hd2, hc03, hc04, hc05, hd03, hd04, hd05,
    hc13, hc14, hc15, hd13, hd14, hd15, hc23, hd23]
  ring

set_option maxHeartbeats 0 in
/-- The cleared Jacobi determinant with cn in its third column. -/
lemma det_two_K_cn_polynomial (m s0 c0 d0 s1 c1 d1 s2 c2 d2 : ℂ)
    (hc0 : c0 ^ 2 = 1 - s0 ^ 2) (hd0 : d0 ^ 2 = 1 - m * s0 ^ 2)
    (hc1 : c1 ^ 2 = 1 - s1 ^ 2) (hd1 : d1 ^ 2 = 1 - m * s1 ^ 2)
    (hc2 : c2 ^ 2 = 1 - s2 ^ 2) (hd2 : d2 ^ 2 = 1 - m * s2 ^ 2) :
    let D := 1 - m * s0 ^ 2 * s1 ^ 2
    let A := s0 * c1 * d1 + s1 * c0 * d0
    let B := c0 * c1 - s0 * s1 * d0 * d1
    let C := d0 * d1 - m * s0 * s1 * c0 * c1
    let E := D ^ 2 - m * A ^ 2 * s2 ^ 2
    let Ns := A * c2 * d2 * D + s2 * B * C
    let Nc := B * c2 * D - A * s2 * C * d2
    let Nd := C * d2 * D - m * A * s2 * B * c2
    Matrix.det !![s0 * c0, s0 * d0, c0, d0; s1 * c1, s1 * d1, c1, d1; s2 * c2, s2 * d2, c2, d2;
      -Ns * Nc, Ns * Nd, -Nc * E, Nd * E] = 0 := by
  dsimp only
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix_apply, Matrix.of_apply]
  norm_num [Fin.succAbove]
  have powers (x a : ℂ) (hx : x ^ 2 = a) :
      x ^ 3 = a * x ∧ x ^ 4 = a ^ 2 ∧ x ^ 5 = a ^ 2 * x := by
    have h4 : x ^ 4 = a ^ 2 := by
      calc x ^ 4 = (x ^ 2) ^ 2 := by ring
           _ = a ^ 2 := by rw [hx]
    refine ⟨?_, h4, ?_⟩
    · rw [pow_succ, hx]
    · rw [pow_succ, h4]
  obtain ⟨hc03, hc04, hc05⟩ := powers c0 (1 - s0 ^ 2) hc0
  obtain ⟨hd03, hd04, hd05⟩ := powers d0 (1 - m * s0 ^ 2) hd0
  obtain ⟨hc13, hc14, hc15⟩ := powers c1 (1 - s1 ^ 2) hc1
  obtain ⟨hd13, hd14, hd15⟩ := powers d1 (1 - m * s1 ^ 2) hd1
  obtain ⟨hc23, _, _⟩ := powers c2 (1 - s2 ^ 2) hc2
  obtain ⟨hd23, _, _⟩ := powers d2 (1 - m * s2 ^ 2) hd2
  ring_nf
  simp only [hc0, hd0, hc1, hd1, hc2, hd2, hc03, hc04, hc05, hd03, hd04, hd05,
    hc13, hc14, hc15, hd13, hd14, hd15, hc23, hd23]
  ring

end DLMF.JacobiElliptic.FourPointAddition
