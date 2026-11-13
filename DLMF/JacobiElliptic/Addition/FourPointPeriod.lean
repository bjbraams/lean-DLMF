/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.JacobiElliptic.Basic.Definitions
import DLMF.JacobiElliptic.Addition.FourPoint
import DLMF.JacobiElliptic.Addition.FourPointAlgebra
import DLMF.JacobiElliptic.Addition.ThetaAndQuotients
import DLMF.JacobiElliptic.Addition.FourPointPeriodAlgebra
import DLMF.JacobiElliptic.PeriodsPolesZeros

/-!
# Four-point Jacobi determinants at a real half-period

The corrected determinants of DLMF 22.8.22–22.8.23 vanish when the arguments sum to `2K`.
The triple-addition formulas and the real half-period reflection establish the polynomial
identities locally. Entire theta numerators extend them to every regular configuration.
The proof uses Mathlib's analytic identity theorem.
-/

open Complex Filter Set DLMF.Elliptic DLMF.EllipticIntegrals
open scoped Real Topology
public section
namespace DLMF.JacobiElliptic.FourPointAddition

/-- The two real-half-period determinants away from intermediate addition poles. -/
lemma det_two_K_of_additionDenominators_ne_zero {k : ℂ} (hk : k ∈ jacobiModulusDomain)
    (z : Fin 4 → ℂ)
    (hz : z 0 + z 1 + z 2 + z 3 = 2 * completeEllipticK k) (hreg : ∀ i, IsJacobiRegular .n (z i) k)
    (hreg01 : IsJacobiRegular .n (z 0 + z 1) k)
    (h01 : 1 - k ^ 2 * jacobiSn (z 0) k ^ 2 * jacobiSn (z 1) k ^ 2 ≠ 0)
    (h012 : 1 - k ^ 2 * jacobiSn (z 0 + z 1) k ^ 2 * jacobiSn (z 2) k ^ 2 ≠ 0) :
    Matrix.det (Matrix.of fun i : Fin 4 =>
      ![jacobiSn (z i) k * jacobiCn (z i) k, jacobiCn (z i) k * jacobiDn (z i) k,
        jacobiSn (z i) k, jacobiDn (z i) k]) = 0 ∧
    Matrix.det (Matrix.of fun i : Fin 4 =>
      ![jacobiSn (z i) k * jacobiCn (z i) k, jacobiSn (z i) k * jacobiDn (z i) k,
        jacobiCn (z i) k, jacobiDn (z i) k]) = 0 := by
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
      field_simp [hD]
    rw [he]
    exact mul_ne_zero (pow_ne_zero 2 hD) hD2
  have hz3 : z 3 = 2 * completeEllipticK k - ((z 0 + z 1) + z 2) := by
    linear_combination hz
  have hr :
      jacobiSn (2 * completeEllipticK k - ((z 0 + z 1) + z 2)) k =
        jacobiSn ((z 0 + z 1) + z 2) k ∧
      jacobiCn (2 * completeEllipticK k - ((z 0 + z 1) + z 2)) k =
        -jacobiCn ((z 0 + z 1) + z 2) k ∧
      jacobiDn (2 * completeEllipticK k - ((z 0 + z 1) + z 2)) k =
        jacobiDn ((z 0 + z 1) + z 2) k := by
    have reflection (u : ℂ) :
        jacobiSn (2 * completeEllipticK k - u) k = jacobiSn u k ∧
        jacobiCn (2 * completeEllipticK k - u) k = -jacobiCn u k ∧
        jacobiDn (2 * completeEllipticK k - u) k = jacobiDn u k := by
      have e : 2 * completeEllipticK k - u = -u + 2 * completeEllipticK k := by ring
      rw [e, (jacobiSn_shift hk (-u)).2.2.2.1, (jacobiCn_shift hk (-u)).2.2.2.1,
        (jacobiDn_shift hk (-u)).2.2.2.1]
      simp [jacobiSn, jacobiCn, jacobiDn, jacobiPQ_neg]
    exact reflection _
  have hs3 : s3 * E = Ns := by
    dsimp only [s3]
    rw [hz3, hr.1]
    rw [jacobiSn_add hk hreg01 (hreg 2) h012, hs01, hc01, hd01]
    -- Expose the named common denominator for clearing fractions.
    change ((A / D * c2 * d2 + s2 * (B / D) * (C / D)) / (1 - m * (A / D) ^ 2 * s2 ^ 2)) * E = Ns
    dsimp only [E, Ns]
    have heN2 : D ^ 2 - A ^ 2 * s2 ^ 2 * m ≠ 0 := by
      convert hE using 1
      dsimp only [E]
      ring
    field_simp [heN2]
  have hc3 : c3 * E = -Nc := by
    dsimp only [c3]
    rw [hz3, hr.2.1]
    rw [jacobiCn_add hk hreg01 (hreg 2) h012, hs01, hc01, hd01]
    -- Expose the named common denominator for clearing fractions.
    change -((B / D * c2 - A / D * (C / D) * s2 * d2) / (1 - m * (A / D) ^ 2 * s2 ^ 2)) * E = -Nc
    dsimp only [E, Nc]
    have heN2 : D ^ 2 - A ^ 2 * s2 ^ 2 * m ≠ 0 := by
      convert hE using 1
      dsimp only [E]
      ring
    field_simp [heN2]
  have hd3 : d3 * E = Nd := by
    dsimp only [d3]
    rw [hz3, hr.2.2]
    rw [jacobiDn_add hk hreg01 (hreg 2) h012, hs01, hc01, hd01]
    -- Expose the named common denominator for clearing fractions.
    change (C / D * d2 - m * (A / D) * (B / D) * s2 * c2) / (1 - m * (A / D) ^ 2 * s2 ^ 2) * E = Nd
    dsimp only [E, Nd]
    have heN3 : D ^ 2 - m * A ^ 2 * s2 ^ 2 ≠ 0 := hE
    field_simp [heN3]
  have hc0 : c0 ^ 2 = 1 - s0 ^ 2 := by linear_combination (squares hk (hreg 0)).1
  have hd0 : d0 ^ 2 = 1 - m * s0 ^ 2 := by linear_combination (squares hk (hreg 0)).2
  have hc1 : c1 ^ 2 = 1 - s1 ^ 2 := by linear_combination (squares hk (hreg 1)).1
  have hd1 : d1 ^ 2 = 1 - m * s1 ^ 2 := by linear_combination (squares hk (hreg 1)).2
  have hc2 : c2 ^ 2 = 1 - s2 ^ 2 := by linear_combination (squares hk (hreg 2)).1
  have hd2 : d2 ^ 2 = 1 - m * s2 ^ 2 := by linear_combination (squares hk (hreg 2)).2
  constructor
  · have hm : (Matrix.of fun i : Fin 4 =>
        ![jacobiSn (z i) k * jacobiCn (z i) k, jacobiCn (z i) k * jacobiDn (z i) k,
          jacobiSn (z i) k, jacobiDn (z i) k]) =
        !![s0 * c0, c0 * d0, s0, d0;
        s1 * c1, c1 * d1, s1, d1;
        s2 * c2, c2 * d2, s2, d2;
        s3 * c3, c3 * d3, s3, d3] := by
      ext i j; fin_cases i <;> fin_cases j <;> rfl
    rw [hm]
    let M := !![s0 * c0, c0 * d0, s0, d0;
          s1 * c1, c1 * d1, s1, d1;
          s2 * c2, c2 * d2, s2, d2;
          s3 * c3, c3 * d3, s3, d3]
    let v : Fin 4 → ℂ := ![1, 1, 1, E ^ 2]
    have hrow : E ^ 2 • ![s3 * c3, c3 * d3, s3, d3] = ![-Ns * Nc, -Nc * Nd, Ns * E, Nd * E] := by
      ext j; fin_cases j <;> simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero',
        Matrix.cons_val_succ', Matrix.cons_val_fin_one]
      · calc E ^ 2 * (s3 * c3) = (s3 * E) * (c3 * E) := by ring
             _ = -Ns * Nc := by simp only [hs3, hc3, mul_neg, neg_mul]
      · calc E ^ 2 * (c3 * d3) = (c3 * E) * (d3 * E) := by ring
             _ = -Nc * Nd := by rw [hc3, hd3]
      · calc E ^ 2 * s3 = (s3 * E) * E := by ring
             _ = Ns * E := by rw [hs3]
      · calc E ^ 2 * d3 = (d3 * E) * E := by ring
             _ = Nd * E := by rw [hd3]
    have heq : (Matrix.of fun i j => v i * M i j) = !![s0 * c0, c0 * d0, s0, d0;
          s1 * c1, c1 * d1, s1, d1;
          s2 * c2, c2 * d2, s2, d2;
         -Ns * Nc, -Nc * Nd, Ns * E, Nd * E] := by
      ext i j
      fin_cases i
      · simp [M, v]
      · simp [M, v]
      · simp [M, v]
      · simpa only [v, M, Matrix.cons_val_zero', Matrix.cons_val_succ',
          Matrix.cons_val_fin_one, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
        using congrFun hrow j
    have hp : Matrix.det !![s0 * c0, c0 * d0, s0, d0;
          s1 * c1, c1 * d1, s1, d1;
          s2 * c2, c2 * d2, s2, d2;
         -Ns * Nc, -Nc * Nd, Ns * E, Nd * E] = 0 :=
      det_two_K_sn_polynomial m s0 c0 d0 s1 c1 d1 s2 c2 d2 hc0 hd0 hc1 hd1 hc2 hd2
    have h := Matrix.det_mul_column v M
    rw [heq, hp] at h
    have hv : (∏ i, v i) = E ^ 2 := by norm_num [v, Fin.prod_univ_succ]
    rw [hv] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero 2 hE)
  · have hm : (Matrix.of fun i : Fin 4 =>
        ![jacobiSn (z i) k * jacobiCn (z i) k, jacobiSn (z i) k * jacobiDn (z i) k,
          jacobiCn (z i) k, jacobiDn (z i) k]) =
        !![s0 * c0, s0 * d0, c0, d0;
        s1 * c1, s1 * d1, c1, d1;
        s2 * c2, s2 * d2, c2, d2;
        s3 * c3, s3 * d3, c3, d3] := by
      ext i j; fin_cases i <;> fin_cases j <;> rfl
    rw [hm]
    let M := !![s0 * c0, s0 * d0, c0, d0;
          s1 * c1, s1 * d1, c1, d1;
          s2 * c2, s2 * d2, c2, d2;
          s3 * c3, s3 * d3, c3, d3]
    let v : Fin 4 → ℂ := ![1, 1, 1, E ^ 2]
    have hrow : E ^ 2 • ![s3 * c3, s3 * d3, c3, d3] = ![-Ns * Nc, Ns * Nd, -Nc * E, Nd * E] := by
      ext j; fin_cases j <;> simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero',
        Matrix.cons_val_succ', Matrix.cons_val_fin_one]
      · calc E ^ 2 * (s3 * c3) = (s3 * E) * (c3 * E) := by ring
             _ = -Ns * Nc := by simp only [hs3, hc3, mul_neg, neg_mul]
      · calc E ^ 2 * (s3 * d3) = (s3 * E) * (d3 * E) := by ring
             _ = Ns * Nd := by rw [hs3, hd3]
      · calc E ^ 2 * c3 = (c3 * E) * E := by ring
             _ = -Nc * E := by rw [hc3]
      · calc E ^ 2 * d3 = (d3 * E) * E := by ring
             _ = Nd * E := by rw [hd3]
    have heq : (Matrix.of fun i j => v i * M i j) = !![s0 * c0, s0 * d0, c0, d0;
          s1 * c1, s1 * d1, c1, d1;
          s2 * c2, s2 * d2, c2, d2;
         -Ns * Nc, Ns * Nd, -Nc * E, Nd * E] := by
      ext i j
      fin_cases i
      · simp [M, v]
      · simp [M, v]
      · simp [M, v]
      · simpa only [v, M, Matrix.cons_val_zero', Matrix.cons_val_succ',
          Matrix.cons_val_fin_one, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
        using congrFun hrow j
    have hp : Matrix.det !![s0 * c0, s0 * d0, c0, d0;
          s1 * c1, s1 * d1, c1, d1;
          s2 * c2, s2 * d2, c2, d2;
         -Ns * Nc, Ns * Nd, -Nc * E, Nd * E] = 0 :=
      det_two_K_cn_polynomial m s0 c0 d0 s1 c1 d1 s2 c2 d2 hc0 hd0 hc1 hd1 hc2 hd2
    have h := Matrix.det_mul_column v M
    rw [heq, hp] at h
    have hv : (∏ i, v i) = E ^ 2 := by norm_num [v, Fin.prod_univ_succ]
    rw [hv] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero 2 hE)

/-- Clearing the squared theta denominators in the two half-period determinants. -/
lemma det_two_K_thetaMatrix_eq_prod_mul_det (b : Bool) (k : ℂ) (z : Fin 4 → ℂ)
    (hreg : ∀ i, IsJacobiRegular .n (z i) k) :
    Matrix.det (Matrix.of fun i : Fin 4 => if b then
      ![jacobiLetterTheta .s (jacobiThetaArgument (z i) k) (jacobiTau k) *
          jacobiLetterTheta .c (jacobiThetaArgument (z i) k) (jacobiTau k),
        jacobiLetterTheta .c (jacobiThetaArgument (z i) k) (jacobiTau k) *
          jacobiLetterTheta .d (jacobiThetaArgument (z i) k) (jacobiTau k),
        jacobiLetterTheta .s (jacobiThetaArgument (z i) k) (jacobiTau k) *
          jacobiLetterTheta .n (jacobiThetaArgument (z i) k) (jacobiTau k),
        jacobiLetterTheta .d (jacobiThetaArgument (z i) k) (jacobiTau k) *
          jacobiLetterTheta .n (jacobiThetaArgument (z i) k) (jacobiTau k)] else
      ![jacobiLetterTheta .s (jacobiThetaArgument (z i) k) (jacobiTau k) *
          jacobiLetterTheta .c (jacobiThetaArgument (z i) k) (jacobiTau k),
        jacobiLetterTheta .s (jacobiThetaArgument (z i) k) (jacobiTau k) *
          jacobiLetterTheta .d (jacobiThetaArgument (z i) k) (jacobiTau k),
        jacobiLetterTheta .c (jacobiThetaArgument (z i) k) (jacobiTau k) *
          jacobiLetterTheta .n (jacobiThetaArgument (z i) k) (jacobiTau k),
        jacobiLetterTheta .d (jacobiThetaArgument (z i) k) (jacobiTau k) *
          jacobiLetterTheta .n (jacobiThetaArgument (z i) k) (jacobiTau k)]) =
    (∏ i, jacobiLetterTheta .n (jacobiThetaArgument (z i) k) (jacobiTau k) ^ 2) *
      Matrix.det (Matrix.of fun i : Fin 4 => if b then
        ![jacobiSn (z i) k * jacobiCn (z i) k, jacobiCn (z i) k * jacobiDn (z i) k,
          jacobiSn (z i) k, jacobiDn (z i) k] else
        ![jacobiSn (z i) k * jacobiCn (z i) k, jacobiSn (z i) k * jacobiDn (z i) k,
          jacobiCn (z i) k, jacobiDn (z i) k]) := by
  let n : Fin 4 → ℂ := fun i =>
    jacobiLetterTheta .n (jacobiThetaArgument (z i) k) (jacobiTau k)
  have hm : (Matrix.of fun i : Fin 4 => if b then
      ![jacobiLetterTheta .s (jacobiThetaArgument (z i) k) (jacobiTau k) *
          jacobiLetterTheta .c (jacobiThetaArgument (z i) k) (jacobiTau k),
        jacobiLetterTheta .c (jacobiThetaArgument (z i) k) (jacobiTau k) *
          jacobiLetterTheta .d (jacobiThetaArgument (z i) k) (jacobiTau k),
        jacobiLetterTheta .s (jacobiThetaArgument (z i) k) (jacobiTau k) * n i,
        jacobiLetterTheta .d (jacobiThetaArgument (z i) k) (jacobiTau k) * n i] else
      ![jacobiLetterTheta .s (jacobiThetaArgument (z i) k) (jacobiTau k) *
          jacobiLetterTheta .c (jacobiThetaArgument (z i) k) (jacobiTau k),
        jacobiLetterTheta .s (jacobiThetaArgument (z i) k) (jacobiTau k) *
          jacobiLetterTheta .d (jacobiThetaArgument (z i) k) (jacobiTau k),
        jacobiLetterTheta .c (jacobiThetaArgument (z i) k) (jacobiTau k) * n i,
        jacobiLetterTheta .d (jacobiThetaArgument (z i) k) (jacobiTau k) * n i]) =
      Matrix.diagonal (fun i => n i ^ 2) * Matrix.of (fun i : Fin 4 => if b then
        ![jacobiSn (z i) k * jacobiCn (z i) k, jacobiCn (z i) k * jacobiDn (z i) k,
          jacobiSn (z i) k, jacobiDn (z i) k] else
        ![jacobiSn (z i) k * jacobiCn (z i) k, jacobiSn (z i) k * jacobiDn (z i) k,
          jacobiCn (z i) k, jacobiDn (z i) k]) := by
    ext i j
    cases b <;> fin_cases j <;>
      simp only [Bool.false_eq_true, eq_self, ↓reduceIte, Matrix.diagonal_mul,
        Matrix.of_apply, Matrix.cons_val_fin_one, Matrix.cons_val_zero', Matrix.cons_val_succ',
        jacobiSn, jacobiCn, jacobiDn, jacobiPQ, jacobiGlaisher, reduceCtorEq, n]
    all_goals
      have hi : jacobiLetterTheta .n (jacobiThetaArgument (z i) k) (jacobiTau k) ≠ 0 := hreg i
      field_simp [hi]
  rw [hm, Matrix.det_mul, Matrix.det_diagonal]

/-- The two corrected Jacobi determinants at every regular configuration summing to `2K`. -/
lemma det_two_K_eq_zero {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : Fin 4 → ℂ)
    (hz : z 0 + z 1 + z 2 + z 3 = 2 * completeEllipticK k)
    (hreg : ∀ i, IsJacobiRegular .n (z i) k) :
    Matrix.det (Matrix.of fun i : Fin 4 =>
      ![jacobiSn (z i) k * jacobiCn (z i) k, jacobiCn (z i) k * jacobiDn (z i) k,
        jacobiSn (z i) k, jacobiDn (z i) k]) = 0 ∧
    Matrix.det (Matrix.of fun i : Fin 4 =>
      ![jacobiSn (z i) k * jacobiCn (z i) k, jacobiSn (z i) k * jacobiDn (z i) k,
        jacobiCn (z i) k, jacobiDn (z i) k]) = 0 := by
  let L : JacobiLetter → ℂ → ℂ := fun p w =>
    jacobiLetterTheta p (jacobiThetaArgument w k) (jacobiTau k)
  have hL (p : JacobiLetter) : Differentiable ℂ (L p) :=
    differentiable_jacobiLetterTheta_comp_jacobiThetaArgument hk p
  let w : ℂ → Fin 4 → ℂ := fun t =>
    ![t * z 0, t * z 1, t * z 2, 2 * completeEllipticK k - t * (z 0 + z 1 + z 2)]
  have hw (i : Fin 4) : Differentiable ℂ (fun t => w t i) := by
    fin_cases i <;> simp only [w, Matrix.cons_val_zero', Matrix.cons_val_succ',
      Matrix.cons_val_fin_one] <;> fun_prop
  have hw0 (t : ℂ) : w t 0 = t * z 0 := rfl
  have hwone (t : ℂ) : w t 1 = t * z 1 := rfl
  have hw2 (t : ℂ) : w t 2 = t * z 2 := rfl
  have hw3 (t : ℂ) : w t 3 = 2 * completeEllipticK k - t * (z 0 + z 1 + z 2) := rfl
  have hw1 : w 1 = z := by
    have hlast : 2 * completeEllipticK k - (z 0 + z 1 + z 2) = z 3 := by
      linear_combination -hz
    dsimp only [w]
    simp only [one_mul, hlast]
    ext i; fin_cases i <;> rfl
  have hn2 : IsJacobiRegular .n (2 * completeEllipticK k) k := by
    have harg : jacobiThetaArgument (2 * completeEllipticK k) k = π := by
      dsimp only [jacobiThetaArgument]
      field_simp [completeEllipticK_ne_zero hk]
    simp only [IsJacobiRegular, jacobiLetterTheta, harg]
    rw [← zero_add (π : ℂ), jacobiThetaFourTau_add_pi]
    exact div_ne_zero (jacobiThetaFourTau_zero_ne_zero (jacobiTau_im_pos hk))
      (jacobiThetaFourTau_zero_ne_zero (jacobiTau_im_pos hk))
  have hnearreg : ∀ᶠ t : ℂ in 𝓝 0, ∀ i, IsJacobiRegular .n (w t i) k := by
    apply eventually_all.mpr
    intro i
    fin_cases i
    · exact eventually_isJacobiRegular_mul hk (z 0)
    · exact eventually_isJacobiRegular_mul hk (z 1)
    · exact eventually_isJacobiRegular_mul hk (z 2)
    · have hc : Continuous (fun t : ℂ =>
          L .n (2 * completeEllipticK k - t * (z 0 + z 1 + z 2))) :=
        (hL .n).continuous.comp
          (continuous_const.sub (continuous_id.mul_const (z 0 + z 1 + z 2)))
      have hn0 : L .n (2 * completeEllipticK k - 0 * (z 0 + z 1 + z 2)) ≠ 0 := by
        simpa only [L, zero_mul, sub_zero, IsJacobiRegular] using hn2
      exact hc.continuousAt.eventually_ne hn0
  have hfinal (b : Bool) :
      Matrix.det (Matrix.of fun i : Fin 4 => if b then
        ![jacobiSn (z i) k * jacobiCn (z i) k, jacobiCn (z i) k * jacobiDn (z i) k,
          jacobiSn (z i) k, jacobiDn (z i) k] else
        ![jacobiSn (z i) k * jacobiCn (z i) k, jacobiSn (z i) k * jacobiDn (z i) k,
          jacobiCn (z i) k, jacobiDn (z i) k]) = 0 := by
    let M : ℂ → Matrix (Fin 4) (Fin 4) ℂ := fun t => Matrix.of fun i => if b then
      ![L .s (w t i) * L .c (w t i), L .c (w t i) * L .d (w t i),
        L .s (w t i) * L .n (w t i), L .d (w t i) * L .n (w t i)] else
      ![L .s (w t i) * L .c (w t i), L .s (w t i) * L .d (w t i),
        L .c (w t i) * L .n (w t i), L .d (w t i) * L .n (w t i)]
    let f : ℂ → ℂ := fun t => (M t).det
    have hentry (i j : Fin 4) : Differentiable ℂ (fun t => M t i j) := by
      cases b <;> fin_cases j <;> simp only [M, Bool.false_eq_true, eq_self,
        ↓reduceIte, Matrix.of_apply, Matrix.cons_val_zero', Matrix.cons_val_succ',
        Matrix.cons_val_fin_one]
      all_goals fun_prop
    have hf : Differentiable ℂ f := by
      simp only [f, Matrix.det_apply']
      apply Differentiable.fun_sum
      intro σ _
      apply Differentiable.const_mul
      exact Differentiable.fun_finsetProd fun i _ => hentry (σ i) i
    have hnear : ∀ᶠ t : ℂ in 𝓝 0, f t = 0 := by
      filter_upwards [hnearreg, eventually_isJacobiRegular_mul hk (z 0 + z 1),
        eventually_additionDenominator_ne_zero hk (z 0) (z 1),
        eventually_additionDenominator_ne_zero hk (z 0 + z 1) (z 2)] with t ht ht01 hd01 hd012
      have ht01' : IsJacobiRegular .n (w t 0 + w t 1) k := by
        rw [hw0, hwone, ← mul_add]
        exact ht01
      have hd01' : 1 - k ^ 2 * jacobiSn (w t 0) k ^ 2 * jacobiSn (w t 1) k ^ 2 ≠ 0 := hd01
      have hd012' : 1 - k ^ 2 * jacobiSn (w t 0 + w t 1) k ^ 2 *
          jacobiSn (w t 2) k ^ 2 ≠ 0 := by
        rw [hw0, hwone, hw2, ← mul_add]
        exact hd012
      have hsum : w t 0 + w t 1 + w t 2 + w t 3 = 2 * completeEllipticK k := by
        rw [hw0, hwone, hw2, hw3]
        ring
      have hdets := det_two_K_of_additionDenominators_ne_zero hk (w t) hsum ht ht01' hd01' hd012'
      have hb : Matrix.det (Matrix.of fun i : Fin 4 => if b then
          ![jacobiSn (w t i) k * jacobiCn (w t i) k, jacobiCn (w t i) k * jacobiDn (w t i) k,
            jacobiSn (w t i) k, jacobiDn (w t i) k] else
          ![jacobiSn (w t i) k * jacobiCn (w t i) k, jacobiSn (w t i) k * jacobiDn (w t i) k,
            jacobiCn (w t i) k, jacobiDn (w t i) k]) = 0 := by
        cases b
        · exact hdets.2
        · exact hdets.1
      dsimp only [f, M, L]
      rw [det_two_K_thetaMatrix_eq_prod_mul_det b k (w t) ht, hb, mul_zero]
    have haf : AnalyticOnNhd ℂ f univ := fun v _ => hf.analyticAt v
    have hf1 : f 1 = 0 := haf.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (mem_univ 0) hnear (mem_univ 1)
    have hn : (∏ i, jacobiLetterTheta .n (jacobiThetaArgument (z i) k) (jacobiTau k) ^ 2) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero 2 (hreg i)
    simp only [f, M, L, hw1] at hf1
    rw [det_two_K_thetaMatrix_eq_prod_mul_det b k z hreg] at hf1
    exact (mul_eq_zero.mp hf1).resolve_left hn
  exact ⟨hfinal true, hfinal false⟩

end DLMF.JacobiElliptic.FourPointAddition
