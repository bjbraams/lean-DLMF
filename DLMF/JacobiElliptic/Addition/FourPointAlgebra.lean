/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.JacobiElliptic.Basic.Definitions
import DLMF.JacobiElliptic.Addition.ThetaAndQuotients

/-!
# Algebraic four-point Jacobi identities

The addition laws and the two quadratic Jacobi relations imply the determinant and
product identities for four arguments summing to zero. This file establishes the
identities wherever the two intermediate addition denominators are nonzero.
The determinant calculation uses Mathlib's cofactor expansion.
-/

open Complex Filter Set DLMF.Elliptic
open scoped Real Topology
public section
namespace DLMF.JacobiElliptic.FourPointAddition


/-- The quadratic relations for Jacobi sn, cn and dn at a regular point. -/
lemma squares {k : ℂ}
    (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hn : IsJacobiRegular .n z k) :
    jacobiSn z k ^ 2 + jacobiCn z k ^ 2 = 1 ∧ k ^ 2 * jacobiSn z k ^ 2 + jacobiDn z k ^ 2 = 1 :=
        by
  have hτ := jacobiTau_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  have hn' : jacobiThetaFourTau (jacobiThetaArgument z k) (jacobiTau k) ≠ 0 := by
    intro h; apply hn; simp [jacobiLetterTheta, h]
  simp only [jacobiSn, jacobiCn, jacobiDn, jacobiPQ, jacobiGlaisher, jacobiLetterTheta,
    reduceCtorEq, ↓reduceIte]
  rw [jacobiModulusOfTau] at hmod
  generalize jacobiThetaArgument z k = ζ at hn' ⊢
  generalize jacobiTau k = τ at hτ hn' hmod ⊢
  subst hmod
  have h2 := jacobiThetaTwoTau_zero_ne_zero hτ
  have h3 := jacobiThetaThreeTau_zero_ne_zero hτ
  have h4 := jacobiThetaFourTau_zero_ne_zero hτ
  have e3 := DLMF.Theta.jacobiTheta_sq_two_four ζ τ hτ
  have e2 := DLMF.Theta.jacobiTheta_sq_three_four ζ τ hτ
  simp only [DLMF.Theta.jacobiThetaTwoNullTau, DLMF.Theta.jacobiThetaThreeNullTau,
    DLMF.Theta.jacobiThetaFourNullTau] at e2 e3
  constructor
  · field_simp
    linear_combination -e3
  · field_simp
    linear_combination -e2



/-- The four-point sum-zero identities where two addition denominators are nonzero. -/
lemma det_and_product_eq_zero_of_additionDenominators_ne_zero {k : ℂ} (hk : k ∈ jacobiModulusDomain)
    (z : Fin 4 → ℂ)
    (hz : z 0 + z 1 + z 2 + z 3 = 0) (hreg : ∀ i, IsJacobiRegular .n (z i) k)
    (hreg01 : IsJacobiRegular .n (z 0 + z 1) k)
    (h01 : 1 - k ^ 2 * jacobiSn (z 0) k ^ 2 * jacobiSn (z 1) k ^ 2 ≠ 0)
    (h012 : 1 - k ^ 2 * jacobiSn (z 0 + z 1) k ^ 2 * jacobiSn (z 2) k ^ 2 ≠ 0) :
    Matrix.det (Matrix.of fun i : Fin 4 =>
      ![jacobiSn (z i) k, jacobiCn (z i) k, jacobiDn (z i) k, 1]) = 0 ∧
    (1 - k ^ 2) - (1 - k ^ 2) * k ^ 2 * (∏ i, jacobiSn (z i) k) + k ^ 2 * (∏ i, jacobiCn (z i) k) -
      (∏ i, jacobiDn (z i) k) = 0 := by
  set m : ℂ := k ^ 2
  set s0 : ℂ := jacobiSn (z 0) k
  set c0 : ℂ := jacobiCn (z 0) k
  set d0 : ℂ := jacobiDn (z 0) k
  set s1 : ℂ := jacobiSn (z 1) k
  set c1 : ℂ := jacobiCn (z 1) k
  set d1 : ℂ := jacobiDn (z 1) k
  set s2 : ℂ := jacobiSn (z 2) k
  set c2 : ℂ := jacobiCn (z 2) k
  set d2 : ℂ := jacobiDn (z 2) k
  set s3 : ℂ := jacobiSn (z 3) k
  set c3 : ℂ := jacobiCn (z 3) k
  set d3 : ℂ := jacobiDn (z 3) k
  let D := 1 - m * s0 ^ 2 * s1 ^ 2
  let A := s0 * c1 * d1 + s1 * c0 * d0
  let B := c0 * c1 - s0 * s1 * d0 * d1
  let C := d0 * d1 - m * s0 * s1 * c0 * c1
  let E := D ^ 2 - m * A ^ 2 * s2 ^ 2
  let Ns := A * c2 * d2 * D + s2 * B * C
  let Nc := B * c2 * D - A * s2 * C * d2
  let Nd := C * d2 * D - m * A * s2 * B * c2
  have hs01 : jacobiSn (z 0 + z 1) k = A / D := jacobiSn_add hk (hreg 0) (hreg 1) h01
  have hc01 : jacobiCn (z 0 + z 1) k = B / D := by
    convert jacobiCn_add hk (hreg 0) (hreg 1) h01 using 1
    dsimp only [B, D]
    ring
  have hd01 : jacobiDn (z 0 + z 1) k = C / D := by
    convert jacobiDn_add hk (hreg 0) (hreg 1) h01 using 1
    dsimp only [C, D]
    ring
  have hD : D ≠ 0 := h01
  have hD2 : 1 - m * (A / D) ^ 2 * s2 ^ 2 ≠ 0 := by simpa only [hs01] using h012
  have hE : E ≠ 0 := by
    have he : E = D ^ 2 * (1 - m * (A / D) ^ 2 * s2 ^ 2) := by
      dsimp only [E]
      field_simp
    rw [he]
    exact mul_ne_zero (pow_ne_zero 2 hD) hD2
  have hz3 : z 3 = -((z 0 + z 1) + z 2) := by linear_combination hz
  have hs3 : s3 * E = -Ns := by
    dsimp only [s3]
    rw [hz3]
    rw [show jacobiSn (-((z 0 + z 1) + z 2)) k = -jacobiSn ((z 0 + z 1) + z 2) k by
      simp only [jacobiSn]; rw [jacobiPQ_neg]; simp]
    rw [jacobiSn_add hk hreg01 (hreg 2) h012, hs01, hc01, hd01]
    change -((A / D * c2 * d2 + s2 * (B / D) * (C / D)) / (1 - m * (A / D) ^ 2 * s2 ^ 2)) * E = -Ns
    dsimp only [E, Ns]
    have heN2 : D ^ 2 - A ^ 2 * s2 ^ 2 * m ≠ 0 := by
      convert hE using 1
      dsimp only [E]
      ring
    field_simp [heN2]
  have hc3 : c3 * E = Nc := by
    dsimp only [c3]
    rw [hz3]
    rw [show jacobiCn (-((z 0 + z 1) + z 2)) k = jacobiCn ((z 0 + z 1) + z 2) k by
      simp only [jacobiCn]; rw [jacobiPQ_neg]; simp]
    rw [jacobiCn_add hk hreg01 (hreg 2) h012, hs01, hc01, hd01]
    change (B / D * c2 - A / D * (C / D) * s2 * d2) / (1 - m * (A / D) ^ 2 * s2 ^ 2) * E = Nc
    dsimp only [E, Nc]
    have heN2 : D ^ 2 - A ^ 2 * s2 ^ 2 * m ≠ 0 := by
      convert hE using 1
      dsimp only [E]
      ring
    field_simp [heN2]
  have hd3 : d3 * E = Nd := by
    dsimp only [d3]
    rw [hz3]
    rw [show jacobiDn (-((z 0 + z 1) + z 2)) k = jacobiDn ((z 0 + z 1) + z 2) k by
      simp only [jacobiDn]; rw [jacobiPQ_neg]; simp]
    rw [jacobiDn_add hk hreg01 (hreg 2) h012, hs01, hc01, hd01]
    change (C / D * d2 - m * (A / D) * (B / D) * s2 * c2) / (1 - m * (A / D) ^ 2 * s2 ^ 2) * E = Nd
    dsimp only [E, Nd]
    have heN3 : D ^ 2 - m * A ^ 2 * s2 ^ 2 ≠ 0 := hE
    field_simp [heN3]
  have h0 : c0 ^ 2 + s0 ^ 2 - 1 = 0 := by linear_combination (squares hk (hreg 0)).1
  have h1 : d0 ^ 2 + m * s0 ^ 2 - 1 = 0 := by linear_combination (squares hk (hreg 0)).2
  have h2 : c1 ^ 2 + s1 ^ 2 - 1 = 0 := by linear_combination (squares hk (hreg 1)).1
  have h3 : d1 ^ 2 + m * s1 ^ 2 - 1 = 0 := by linear_combination (squares hk (hreg 1)).2
  have h4 : c2 ^ 2 + s2 ^ 2 - 1 = 0 := by linear_combination (squares hk (hreg 2)).1
  have h5 : d2 ^ 2 + m * s2 ^ 2 - 1 = 0 := by linear_combination (squares hk (hreg 2)).2
  have hmat : Matrix.of (fun i : Fin 4 =>
      ![jacobiSn (z i) k, jacobiCn (z i) k, jacobiDn (z i) k, 1]) =
      !![s0, c0, d0, 1;s1, c1, d1, 1;s2, c2, d2, 1;s3, c3, d3, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  constructor
  · rw [hmat]
    apply mul_left_cancel₀ hE
    rw [mul_zero]
    rw [Matrix.det_succ_row_zero]
    simp only [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix_apply, Matrix.of_apply]
    conv_lhs => norm_num [Fin.succAbove]
    dsimp only [E, Ns, Nc, Nd, A, B, C, D] at hs3 hc3 hd3 ⊢
    linear_combination
      (-c0 * c1 ^ 2 * d1 * m * s0 * s1 * s2 + c0 * c1 ^ 2 * d2 * m * s0 * s1 * s2 - c0 * c1 * c2 *
          d0 * m * s1 ^ 2 * s2 + c0 * c1 * c2 * d0 * m * s1 * s2 ^ 2 - c0 * d0 ^ 2 * d1 * m * s1 ^ 2
          * s2 ^ 3 + c0 * d0 ^ 2 * d2 * m * s1 ^ 3 * s2 ^ 2 + c1 ^ 3 * d0 * m * s0 * s1 * s2 - c1 ^
          3 * d2 * m * s0 * s1 * s2 - c1 ^ 2 * c2 * d0 * m * s1 * s2 ^ 2 + c1 ^ 2 * c2 * d1 * m * s0
          * s2 ^ 2 - c1 * c2 ^ 2 * d0 * m * s0 * s1 * s2 + c1 * c2 ^ 2 * d0 * m * s1 ^ 2 * s2 + c1 *
          d0 ^ 3 * m * s1 ^ 2 * s2 ^ 3 - c1 * d0 ^ 2 * d2 * m * s0 * s1 ^ 3 * s2 + c1 * d0 * d1 ^ 2
          * m * s0 ^ 2 * s1 ^ 2 * s2 - 2 * c1 * d0 * d1 ^ 2 * m * s0 * s1 * s2 ^ 3 + c1 * d0 * d1 ^
          2 * s2 + c1 * d0 * d1 * d2 * m * s0 * s1 ^ 2 * s2 ^ 2 - c1 * d0 * d1 * d2 * s2 - c1 * d0 *
          d2 ^ 2 * m * s0 ^ 2 * s1 ^ 2 * s2 + c1 * d0 * d2 ^ 2 * m * s0 * s1 ^ 3 * s2 + c1 * d2 * m
          ^ 2 * s0 ^ 3 * s1 ^ 4 - c1 * d2 * m ^ 2 * s0 ^ 3 * s1 ^ 3 * s2 - c1 * d2 * m * s0 * s1 ^ 2
          + c1 * d2 * m * s0 * s1 * s2 - c2 * d0 ^ 3 * m * s1 ^ 3 * s2 ^ 2 + c2 * d0 ^ 2 * d1 * m *
          s0 * s1 ^ 3 * s2 - c2 * d0 * d1 * d2 * m * s0 ^ 2 * s1 ^ 3 + c2 * d0 * d1 * d2 * s1 + c2 *
          d0 * d2 ^ 2 * m * s0 ^ 2 * s1 ^ 3 - c2 * d0 * d2 ^ 2 * s1) * h0 +
      (-c0 * c1 ^ 2 * d1 * m * s0 ^ 2 * s1 ^ 2 * s2 + 2 * c0 * c1 ^ 2 * d1 * m * s0 * s1 * s2 ^ 3 -
          c0 * c1 ^ 2 * d1 * s2 - c0 * c1 * c2 * d1 * m * s0 * s1 ^ 2 * s2 ^ 2 + c0 * c1 * c2 * d1 *
          s2 + c0 * c1 * c2 * d2 * m * s0 ^ 2 * s1 ^ 3 - c0 * c1 * c2 * d2 * s1 + c0 * c2 ^ 2 * d1 *
          m * s0 ^ 2 * s1 ^ 2 * s2 - c0 * c2 ^ 2 * d1 * m * s0 * s1 ^ 3 * s2 - c0 * c2 ^ 2 * d2 * m
          * s0 ^ 2 * s1 ^ 3 + c0 * c2 ^ 2 * d2 * s1 + c0 * d0 * d1 * d2 * s1 ^ 2 * s2 - c0 * d0 * d1
          * d2 * s1 * s2 ^ 2 - c0 * d1 ^ 3 * s0 * s1 * s2 + c0 * d1 ^ 2 * d2 * s1 * s2 ^ 2 + c0 * d1
          * d2 ^ 2 * s0 * s1 * s2 - c0 * d1 * d2 ^ 2 * s1 ^ 2 * s2 + c0 * d1 * m * s0 ^ 2 * s1 ^ 2 *
          s2 ^ 3 - c0 * d1 * m * s1 ^ 2 * s2 ^ 3 - c0 * d2 * m * s0 ^ 2 * s1 ^ 3 * s2 ^ 2 + c0 * d2
          * m * s1 ^ 3 * s2 ^ 2 + c1 * d0 * d1 ^ 2 * s0 * s1 * s2 - c1 * d0 * m * s0 ^ 2 * s1 ^ 2 *
          s2 ^ 3 + c1 * d0 * m * s1 ^ 2 * s2 ^ 3 - c1 * d1 ^ 2 * d2 * s0 * s2 ^ 2 + c1 * d2 * m * s0
          ^ 3 * s1 ^ 3 * s2 - c1 * d2 * m * s0 * s1 ^ 3 * s2 - c2 * d0 * d1 ^ 2 * s0 * s1 * s2 + c2
          * d0 * m * s0 ^ 2 * s1 ^ 3 * s2 ^ 2 - c2 * d0 * m * s1 ^ 3 * s2 ^ 2 + c2 * d1 ^ 3 * s0 *
          s1 * s2 - c2 * d1 * m * s0 ^ 3 * s1 ^ 4 + c2 * d1 * m * s0 * s1 ^ 3 * s2 + c2 * d1 * s0 *
          s1 ^ 2 - c2 * d1 * s0 * s1 * s2) * h1 +
      (c0 * c1 * c2 * d1 * m * s0 ^ 2 * s2 - c0 * c1 * c2 * d1 * m * s0 * s2 ^ 2 - c0 * c2 ^ 2 * d1
          * m * s0 ^ 2 * s2 + c0 * c2 ^ 2 * d1 * m * s0 * s1 * s2 - c0 * d0 * d1 * d2 * m * s0 ^ 2 *
          s1 * s2 ^ 2 + c0 * d0 * d1 * d2 * s2 - c0 * d1 ^ 3 * m * s0 ^ 2 * s2 ^ 3 + c0 * d1 ^ 2 *
          d2 * m * s0 ^ 3 * s1 * s2 - c0 * d1 * d2 ^ 2 * m * s0 ^ 3 * s1 * s2 + c0 * d1 * d2 ^ 2 * m
          * s0 ^ 2 * s1 ^ 2 * s2 + c0 * d1 * m ^ 2 * s0 ^ 4 * s1 ^ 2 * s2 - 2 * c0 * d1 * m ^ 2 * s0
          ^ 3 * s1 * s2 ^ 3 + c0 * d1 * m * s0 ^ 3 * s1 * s2 - c0 * d1 * m * s0 ^ 2 * s1 ^ 2 * s2 +
          c0 * d1 * m * s0 ^ 2 * s2 + 2 * c0 * d1 * m * s0 * s1 * s2 ^ 3 - c0 * d1 * m * s0 * s1 *
          s2 - c0 * d1 * s2 - c0 * d2 * m ^ 2 * s0 ^ 4 * s1 ^ 3 + c0 * d2 * m ^ 2 * s0 ^ 3 * s1 ^ 3
          * s2 - c0 * d2 * m * s0 ^ 3 * s1 * s2 + c0 * d2 * m * s0 ^ 2 * s1 + c1 * d0 * d1 ^ 2 * m *
          s0 ^ 2 * s2 ^ 3 - c1 * d0 * m * s0 ^ 3 * s1 * s2 + c1 * d0 * m * s0 * s1 * s2 - c1 * d1 ^
          2 * d2 * m * s0 ^ 3 * s2 ^ 2 + c1 * d2 * m * s0 ^ 3 * s1 * s2 - c1 * d2 * m * s0 * s1 * s2
          - c2 * d0 * d1 ^ 2 * m * s0 ^ 3 * s1 * s2 + c2 * d0 * d1 * d2 * m * s0 ^ 3 * s1 ^ 2 - c2 *
          d0 * d1 * d2 * s0 + c2 * d0 * m * s0 ^ 2 * s1 * s2 ^ 2 - c2 * d0 * m * s1 * s2 ^ 2 + c2 *
          d1 ^ 3 * m * s0 ^ 3 * s2 ^ 2 - c2 * d1 * d2 ^ 2 * m * s0 ^ 3 * s1 ^ 2 + c2 * d1 * d2 ^ 2 *
          s0 - c2 * d1 * m * s0 ^ 3 * s2 ^ 2 + c2 * d1 * m * s0 * s2 ^ 2) * h2 +
      (c0 * c1 * c2 * d0 * m * s0 ^ 2 * s1 * s2 ^ 2 - c0 * c1 * c2 * d0 * s2 - c0 * c1 * c2 * d2 * m
          * s0 ^ 3 * s1 ^ 2 + c0 * c1 * c2 * d2 * s0 + c0 * d1 * m * s0 ^ 3 * s1 * s2 + c0 * d1 * m
          * s0 ^ 2 * s1 ^ 2 * s2 ^ 3 - c0 * d1 * m * s0 ^ 2 * s2 ^ 3 - c0 * d1 * s0 * s1 * s2 - c0 *
          d2 * m * s0 ^ 3 * s1 ^ 3 * s2 + c0 * d2 * m * s0 ^ 3 * s1 * s2 - c0 * d2 * m * s0 ^ 2 * s1
          * s2 ^ 2 + c0 * d2 * s1 * s2 ^ 2 + c1 * c2 ^ 2 * d0 * m * s0 ^ 3 * s1 * s2 - c1 * c2 ^ 2 *
          d0 * m * s0 ^ 2 * s1 ^ 2 * s2 + c1 * c2 ^ 2 * d2 * m * s0 ^ 3 * s1 ^ 2 - c1 * c2 ^ 2 * d2
          * s0 - c1 * d0 * d1 * d2 * s0 ^ 2 * s2 + c1 * d0 * d1 * d2 * s0 * s2 ^ 2 + c1 * d0 * d2 ^
          2 * s0 ^ 2 * s2 - c1 * d0 * d2 ^ 2 * s0 * s1 * s2 - c1 * d0 * m * s0 ^ 4 * s1 ^ 2 * s2 + 2
          * c1 * d0 * m * s0 ^ 3 * s1 * s2 ^ 3 - c1 * d0 * m * s0 ^ 3 * s1 * s2 - c1 * d0 * m * s0 ^
          2 * s1 ^ 2 * s2 ^ 3 + c1 * d0 * m * s0 ^ 2 * s1 ^ 2 * s2 + c1 * d0 * m * s0 ^ 2 * s2 ^ 3 -
          2 * c1 * d0 * m * s0 * s1 * s2 ^ 3 - c1 * d0 * s0 ^ 2 * s2 + c1 * d0 * s0 * s1 * s2 + c1 *
          d0 * s2 + c1 * d2 * m * s0 ^ 3 * s1 ^ 2 * s2 ^ 2 - c1 * d2 * s0 * s2 ^ 2 + c2 * d0 * m *
          s0 ^ 4 * s1 ^ 3 - c2 * d0 * s0 ^ 2 * s1 - c2 * d1 * m * s0 ^ 3 * s1 ^ 2 * s2 ^ 2 - c2 * d1
          * m * s0 ^ 3 * s1 * s2 + c2 * d1 * m * s0 ^ 3 * s2 ^ 2 + c2 * d1 * s0 * s1 * s2) * h3 +
      (c0 * d0 * d1 * d2 * m * s0 ^ 2 * s1 ^ 3 - c0 * d0 * d1 * d2 * s1 - c0 * d1 * m ^ 2 * s0 ^ 4 *
          s1 ^ 2 * s2 + c0 * d1 * m ^ 2 * s0 ^ 3 * s1 ^ 3 * s2 + 2 * c0 * d1 * m * s0 ^ 2 * s1 ^ 2 *
          s2 - c0 * d1 * m * s0 ^ 2 * s2 - 2 * c0 * d1 * m * s0 * s1 ^ 3 * s2 + c0 * d1 * m * s0 *
          s1 * s2 + c0 * d2 * m ^ 2 * s0 ^ 4 * s1 ^ 3 - c0 * d2 * m * s0 ^ 2 * s1 ^ 3 - c0 * d2 * m
          * s0 ^ 2 * s1 + c0 * d2 * s1 - c1 * d0 * d1 * d2 * m * s0 ^ 3 * s1 ^ 2 + c1 * d0 * d1 * d2
          * s0 - c1 * d0 * m ^ 2 * s0 ^ 3 * s1 ^ 3 * s2 + c1 * d0 * m ^ 2 * s0 ^ 2 * s1 ^ 4 * s2 + 2
          * c1 * d0 * m * s0 ^ 3 * s1 * s2 - 2 * c1 * d0 * m * s0 ^ 2 * s1 ^ 2 * s2 - c1 * d0 * m *
          s0 * s1 * s2 + c1 * d0 * m * s1 ^ 2 * s2 - c1 * d2 * m ^ 2 * s0 ^ 3 * s1 ^ 4 + c1 * d2 * m
          * s0 ^ 3 * s1 ^ 2 + c1 * d2 * m * s0 * s1 ^ 2 - c1 * d2 * s0) * h4 +
      (-c0 * c1 * c2 * d0 * m * s0 ^ 2 * s1 ^ 3 + c0 * c1 * c2 * d0 * s1 + c0 * c1 * c2 * d1 * m *
          s0 ^ 3 * s1 ^ 2 - c0 * c1 * c2 * d1 * s0 + c0 * d1 * m * s0 ^ 3 * s1 ^ 3 * s2 - 2 * c0 *
          d1 * m * s0 ^ 3 * s1 * s2 - c0 * d1 * m * s0 ^ 2 * s1 ^ 4 * s2 + 2 * c0 * d1 * m * s0 ^ 2
          * s1 ^ 2 * s2 + c0 * d1 * s0 * s1 * s2 - c0 * d1 * s1 ^ 2 * s2 + c1 * d0 * m * s0 ^ 4 * s1
          ^ 2 * s2 - c1 * d0 * m * s0 ^ 3 * s1 ^ 3 * s2 - 2 * c1 * d0 * m * s0 ^ 2 * s1 ^ 2 * s2 + 2
          * c1 * d0 * m * s0 * s1 ^ 3 * s2 + c1 * d0 * s0 ^ 2 * s2 - c1 * d0 * s0 * s1 * s2 - c2 *
          d0 * m * s0 ^ 4 * s1 ^ 3 + c2 * d0 * m * s0 ^ 2 * s1 ^ 3 + c2 * d0 * s0 ^ 2 * s1 - c2 * d0
          * s1 + c2 * d1 * m * s0 ^ 3 * s1 ^ 4 - c2 * d1 * m * s0 ^ 3 * s1 ^ 2 - c2 * d1 * s0 * s1 ^
          2 + c2 * d1 * s0) * h5 +
      (-c0 * d1 + c0 * d2 + c1 * d0 - c1 * d2 - c2 * d0 + c2 * d1) * hs3 +
      (s0 * d1 - s0 * d2 - s1 * d0 + s1 * d2 + s2 * d0 - s2 * d1) * hc3 +
      (-s0 * c1 + s0 * c2 + s1 * c0 - s1 * c2 - s2 * c0 + s2 * c1) * hd3
  · simp only [Fin.prod_univ_succ]
    change (1 - m) - (1 - m) * m * (s0 * (s1 * (s2 * (s3 * 1)))) +
      m * (c0 * (c1 * (c2 * (c3 * 1)))) - (d0 * (d1 * (d2 * (d3 * 1)))) = 0
    apply mul_left_cancel₀ hE
    rw [mul_zero]
    dsimp only [E, Ns, Nc, Nd, A, B, C, D] at hs3 hc3 hd3 ⊢
    linear_combination
      (c0 * c1 ^ 2 * c2 * d0 * d2 * m ^ 2 * s0 * s1 ^ 2 * s2 + c1 ^ 3 * c2 * d1 * d2 * m ^ 2 * s0 ^
          2 * s1 * s2 - c1 ^ 2 * c2 ^ 2 * m ^ 2 * s0 ^ 2 * s1 ^ 2 + c1 ^ 2 * c2 ^ 2 * m + c1 ^ 2 * m
          ^ 3 * s0 ^ 2 * s1 ^ 2 * s2 ^ 2 - c1 ^ 2 * m ^ 2 * s0 ^ 2 * s1 ^ 2 * s2 ^ 2 + d0 ^ 2 * m ^
          2 * s1 ^ 2 * s2 ^ 2 - d0 ^ 2 * m * s1 ^ 2 * s2 ^ 2) * h0 +
      (-c0 * c2 * d0 * d1 ^ 2 * d2 * m * s0 * s1 ^ 2 * s2 - c1 * c2 * d1 ^ 3 * d2 * m * s0 ^ 2 * s1
          * s2 + d1 ^ 2 * d2 ^ 2 * m * s0 ^ 2 * s1 ^ 2 - d1 ^ 2 * d2 ^ 2 + d1 ^ 2 * m ^ 2 * s0 ^ 2 *
          s1 ^ 2 * s2 ^ 2 - d1 ^ 2 * m * s0 ^ 2 * s1 ^ 2 * s2 ^ 2 - m ^ 2 * s0 ^ 2 * s1 ^ 2 * s2 ^ 2
          + m ^ 2 * s1 ^ 2 * s2 ^ 2 + m * s0 ^ 2 * s1 ^ 2 * s2 ^ 2 - m * s1 ^ 2 * s2 ^ 2) * h1 +
      (-c0 * c2 * d0 * d2 * m ^ 2 * s0 ^ 3 * s1 ^ 2 * s2 + c0 * c2 * d0 * d2 * m ^ 2 * s0 * s1 ^ 2 *
          s2 - c1 * c2 * d1 * d2 * m ^ 2 * s0 ^ 4 * s1 * s2 + c1 * c2 * d1 * d2 * m ^ 2 * s0 ^ 2 *
          s1 * s2 + c2 ^ 2 * m ^ 2 * s0 ^ 4 * s1 ^ 2 - c2 ^ 2 * m ^ 2 * s0 ^ 2 * s1 ^ 2 - c2 ^ 2 * m
          * s0 ^ 2 + c2 ^ 2 * m + d1 ^ 2 * m ^ 2 * s0 ^ 2 * s2 ^ 2 - d1 ^ 2 * m * s0 ^ 2 * s2 ^ 2 -
          m ^ 3 * s0 ^ 4 * s1 ^ 2 * s2 ^ 2 + m ^ 3 * s0 ^ 2 * s1 ^ 2 * s2 ^ 2 + m ^ 2 * s0 ^ 4 * s1
          ^ 2 * s2 ^ 2 - m ^ 2 * s0 ^ 2 * s1 ^ 2 * s2 ^ 2) * h2 +
      (c0 * c2 * d0 * d2 * m ^ 2 * s0 ^ 3 * s1 ^ 2 * s2 - c0 * c2 * d0 * d2 * m * s0 * s1 ^ 2 * s2 +
          c1 * c2 * d1 * d2 * m ^ 2 * s0 ^ 4 * s1 * s2 - c1 * c2 * d1 * d2 * m * s0 ^ 2 * s1 * s2 -
          d2 ^ 2 * m ^ 2 * s0 ^ 4 * s1 ^ 2 + d2 ^ 2 * m * s0 ^ 2 * s1 ^ 2 + d2 ^ 2 * m * s0 ^ 2 - d2
          ^ 2 - m ^ 3 * s0 ^ 4 * s1 ^ 2 * s2 ^ 2 + m ^ 2 * s0 ^ 4 * s1 ^ 2 * s2 ^ 2 + m ^ 2 * s0 ^ 2
          * s2 ^ 2 - m * s0 ^ 2 * s2 ^ 2) * h3 +
      (c0 * c1 * d0 * d1 * m ^ 2 * s0 ^ 3 * s1 ^ 3 - c0 * c1 * d0 * d1 * m * s0 * s1 - m ^ 2 * s0 ^
          4 * s1 ^ 4 + m ^ 2 * s0 ^ 4 * s1 ^ 2 + m ^ 2 * s0 ^ 2 * s1 ^ 4 - m ^ 2 * s0 ^ 2 * s1 ^ 2 +
          m * s0 ^ 2 * s1 ^ 2 - m * s0 ^ 2 - m * s1 ^ 2 + m) * h4 +
      (-c0 * c1 * d0 * d1 * m ^ 2 * s0 ^ 3 * s1 ^ 3 + c0 * c1 * d0 * d1 * m * s0 * s1 + m ^ 3 * s0 ^
          4 * s1 ^ 4 - m ^ 2 * s0 ^ 4 * s1 ^ 2 - m ^ 2 * s0 ^ 2 * s1 ^ 4 - m ^ 2 * s0 ^ 2 * s1 ^ 2 +
          m * s0 ^ 2 * s1 ^ 2 + m * s0 ^ 2 + m * s1 ^ 2 - 1) * h5 +
      (-(1 - m) * m * s0 * s1 * s2) * hs3 + (m * c0 * c1 * c2) * hc3 - (d0 * d1 * d2) * hd3


end DLMF.JacobiElliptic.FourPointAddition
