/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.JacobiElliptic.Basic.Definitions
import DLMF.JacobiElliptic.Addition.FourPointAlgebra
import DLMF.JacobiElliptic.Addition.ThetaAndQuotients

/-!
# Four-point sum-zero Jacobi identities

The four-point determinant and product identities (DLMF 22.8.19–22.8.21) hold at all
regular arguments whose sum is zero. Their theta numerators are entire along a common
complex scaling of the four arguments. The algebraic identities near zero therefore
extend to every scale by Mathlib's analytic identity principle, including configurations
where an intermediate addition denominator vanishes.
-/

open Complex Filter Set DLMF.Elliptic
open scoped Real Topology
public section
namespace DLMF.JacobiElliptic.FourPointAddition


/-- The common denominator of sn, cn and dn is nonzero at zero. -/
lemma isJacobiRegular_zero {k : ℂ} (hk : k ∈ jacobiModulusDomain) : IsJacobiRegular .n 0 k := by
  have h4 := jacobiThetaFourTau_zero_ne_zero (jacobiTau_im_pos hk)
  simp [IsJacobiRegular, jacobiThetaArgument, jacobiLetterTheta, h4]

/-- Jacobi sn is continuous at zero for a modulus in the principal domain. -/
lemma continuousAt_jacobiSn_zero {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    ContinuousAt (fun w => jacobiSn w k) 0 := by
  have hn := differentiable_jacobiLetterTheta_comp_jacobiThetaArgument hk .n
  have hs := differentiable_jacobiLetterTheta_comp_jacobiThetaArgument hk .s
  change ContinuousAt (fun w => jacobiLetterTheta .s (jacobiThetaArgument w k) (jacobiTau k) /
    jacobiLetterTheta .n (jacobiThetaArgument w k) (jacobiTau k)) 0
  exact hs.continuous.continuousAt.div hn.continuous.continuousAt (isJacobiRegular_zero hk)

/-- Every fixed direction is regular sufficiently close to zero. -/
lemma eventually_isJacobiRegular_mul {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ) :
    ∀ᶠ t : ℂ in 𝓝 0, IsJacobiRegular .n (t * z) k := by
  have hc := (differentiable_jacobiLetterTheta_comp_jacobiThetaArgument hk .n).continuous
  have hc' := (hc.comp (continuous_id.mul_const z)).continuousAt (x := (0 : ℂ))
  have hne : jacobiLetterTheta .n (jacobiThetaArgument (0 * z) k) (jacobiTau k) ≠ 0 := by
    simpa only [IsJacobiRegular, zero_mul] using (isJacobiRegular_zero hk :
      jacobiLetterTheta .n (jacobiThetaArgument 0 k) (jacobiTau k) ≠ 0)
  exact hc'.eventually_ne hne

/-- The addition denominator is nonzero when both arguments are sufficiently small. -/
lemma eventually_additionDenominator_ne_zero {k : ℂ} (hk : k ∈ jacobiModulusDomain) (u v : ℂ) :
    ∀ᶠ t : ℂ in 𝓝 0, 1 - k ^ 2 * jacobiSn (t * u) k ^ 2 * jacobiSn (t * v) k ^ 2 ≠ 0 := by
  have hu := (continuousAt_jacobiSn_zero hk).comp_of_eq (by fun_prop : ContinuousAt (fun t : ℂ => t
      * u) 0)
    (by simp)
  have hv := (continuousAt_jacobiSn_zero hk).comp_of_eq (by fun_prop : ContinuousAt (fun t : ℂ => t
      * v) 0)
    (by simp)
  have hc := ((hu.pow 2).const_mul (k ^ 2)).mul (hv.pow 2) |>.const_sub 1
  have hs0 : jacobiSn 0 k = 0 := by
    simp [jacobiSn, jacobiPQ, jacobiGlaisher, jacobiLetterTheta, jacobiThetaArgument,
      jacobiThetaOneTau_zero]
  have hne : 1 - k ^ 2 * jacobiSn (0 * u) k ^ 2 * jacobiSn (0 * v) k ^ 2 ≠ 0 := by
    simp only [zero_mul, hs0, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, sub_zero,
      ne_eq, one_ne_zero, not_false_eq_true]
  exact hc.eventually_ne hne

/-- Multiplying each row by its theta denominator clears the Jacobi determinant. -/
lemma det_thetaMatrix_eq_prod_mul_det (k : ℂ) (z : Fin 4 → ℂ) (hreg : ∀ i, IsJacobiRegular .n (z i)
    k) :
    Matrix.det (Matrix.of fun i : Fin 4 =>
      ![jacobiLetterTheta .s (jacobiThetaArgument (z i) k) (jacobiTau k),
        jacobiLetterTheta .c (jacobiThetaArgument (z i) k) (jacobiTau k),
        jacobiLetterTheta .d (jacobiThetaArgument (z i) k) (jacobiTau k),
        jacobiLetterTheta .n (jacobiThetaArgument (z i) k) (jacobiTau k)]) =
    (∏ i, jacobiLetterTheta .n (jacobiThetaArgument (z i) k) (jacobiTau k)) *
      Matrix.det (Matrix.of fun i : Fin 4 =>
        ![jacobiSn (z i) k, jacobiCn (z i) k, jacobiDn (z i) k, 1]) := by
  let n : Fin 4 → ℂ := fun i => jacobiLetterTheta .n (jacobiThetaArgument (z i) k) (jacobiTau k)
  have hm : (Matrix.of fun i : Fin 4 =>
      ![jacobiLetterTheta .s (jacobiThetaArgument (z i) k) (jacobiTau k),
        jacobiLetterTheta .c (jacobiThetaArgument (z i) k) (jacobiTau k),
        jacobiLetterTheta .d (jacobiThetaArgument (z i) k) (jacobiTau k), n i]) =
      Matrix.diagonal n * Matrix.of (fun i : Fin 4 =>
        ![jacobiSn (z i) k, jacobiCn (z i) k, jacobiDn (z i) k, 1]) := by
    ext i j
    fin_cases j <;>
      simp only [Matrix.diagonal_mul, Matrix.of_apply,
        Matrix.cons_val_fin_one, Matrix.cons_val_zero', Matrix.cons_val_succ', jacobiSn, jacobiCn,
            jacobiDn, jacobiPQ, jacobiGlaisher,
        reduceCtorEq, ↓reduceIte, n]
    all_goals
      have hi : jacobiLetterTheta .n (jacobiThetaArgument (z i) k) (jacobiTau k) ≠ 0 := hreg i
      field_simp [hi]
  rw [hm, Matrix.det_mul, Matrix.det_diagonal]

/-- The theta numerators clear the four-point Jacobi product relation. -/
lemma product_theta_eq_prod_mul_relation (k : ℂ) (z : Fin 4 → ℂ) (hreg : ∀ i, IsJacobiRegular .n (z
    i) k) :
    (1 - k ^ 2) * (∏ i, jacobiLetterTheta .n (jacobiThetaArgument (z i) k) (jacobiTau k)) -
      (1 - k ^ 2) * k ^ 2 * (∏ i, jacobiLetterTheta .s (jacobiThetaArgument (z i) k) (jacobiTau k))
          +
      k ^ 2 * (∏ i, jacobiLetterTheta .c (jacobiThetaArgument (z i) k) (jacobiTau k)) -
      (∏ i, jacobiLetterTheta .d (jacobiThetaArgument (z i) k) (jacobiTau k)) =
    (∏ i, jacobiLetterTheta .n (jacobiThetaArgument (z i) k) (jacobiTau k)) *
      ((1 - k ^ 2) - (1 - k ^ 2) * k ^ 2 * (∏ i, jacobiSn (z i) k) + k ^ 2 * (∏ i, jacobiCn (z i) k)
          -
        (∏ i, jacobiDn (z i) k)) := by
  have hn : (∏ i, jacobiLetterTheta .n (jacobiThetaArgument (z i) k) (jacobiTau k)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => hreg i)
  simp only [jacobiSn, jacobiCn, jacobiDn, jacobiPQ, jacobiGlaisher, reduceCtorEq, ↓reduceIte,
    Finset.prod_div_distrib]
  field_simp

/-- The determinant and product identities for four regular Jacobi arguments summing to zero. -/
lemma det_and_product_eq_zero {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : Fin 4 → ℂ)
    (hz : z 0 + z 1 + z 2 + z 3 = 0) (hreg : ∀ i, IsJacobiRegular .n (z i) k) :
    Matrix.det (Matrix.of fun i : Fin 4 =>
      ![jacobiSn (z i) k, jacobiCn (z i) k, jacobiDn (z i) k, 1]) = 0 ∧
    (1 - k ^ 2) - (1 - k ^ 2) * k ^ 2 * (∏ i, jacobiSn (z i) k) + k ^ 2 * (∏ i, jacobiCn (z i) k) -
      (∏ i, jacobiDn (z i) k) = 0 := by
  let L : JacobiLetter → ℂ → ℂ := fun p w =>
    jacobiLetterTheta p (jacobiThetaArgument w k) (jacobiTau k)
  have hL (p : JacobiLetter) : Differentiable ℂ (L p) :=
    differentiable_jacobiLetterTheta_comp_jacobiThetaArgument hk p
  let M : ℂ → Matrix (Fin 4) (Fin 4) ℂ := fun t => Matrix.of fun i =>
    ![L .s (t * z i), L .c (t * z i), L .d (t * z i), L .n (t * z i)]
  let f : ℂ → ℂ := fun t => (M t).det
  let g : ℂ → ℂ := fun t => (1 - k ^ 2) * (∏ i, L .n (t * z i)) -
    (1 - k ^ 2) * k ^ 2 * (∏ i, L .s (t * z i)) + k ^ 2 * (∏ i, L .c (t * z i)) - (∏ i, L .d (t * z
        i))
  have hentry (i j : Fin 4) : Differentiable ℂ (fun t => M t i j) := by
    fin_cases j <;> simp only [M, Matrix.of_apply, Matrix.cons_val_zero',
      Matrix.cons_val_succ', Matrix.cons_val_fin_one]
    · exact (hL .s).comp (differentiable_id.mul_const (z i))
    · exact (hL .c).comp (differentiable_id.mul_const (z i))
    · exact (hL .d).comp (differentiable_id.mul_const (z i))
    · exact (hL .n).comp (differentiable_id.mul_const (z i))
  have hf : Differentiable ℂ f := by
    simp only [f, Matrix.det_apply']
    apply Differentiable.fun_sum
    intro σ _
    apply Differentiable.const_mul
    exact Differentiable.fun_finsetProd fun i _ => hentry (σ i) i
  have hp (p : JacobiLetter) : Differentiable ℂ (fun t => ∏ i, L p (t * z i)) :=
    Differentiable.fun_finsetProd fun i _ => (hL p).comp (differentiable_id.mul_const (z i))
  have hg : Differentiable ℂ g :=
    (((hp .n).const_mul _).sub ((hp .s).const_mul _)).add ((hp .c).const_mul _)
      |>.sub (hp .d)
  have hnear : ∀ᶠ t : ℂ in 𝓝 0, f t = 0 ∧ g t = 0 := by
    have hr : ∀ᶠ t : ℂ in 𝓝 0, ∀ i : Fin 4, IsJacobiRegular .n (t * z i) k :=
      eventually_all.mpr fun i => eventually_isJacobiRegular_mul hk (z i)
    filter_upwards [hr, eventually_isJacobiRegular_mul hk (z 0 + z 1),
      eventually_additionDenominator_ne_zero hk (z 0) (z 1),
      eventually_additionDenominator_ne_zero hk (z 0 + z 1) (z 2)] with t ht ht01 hd01 hd012
    have ht01' : IsJacobiRegular .n (t * z 0 + t * z 1) k := by simpa only [mul_add] using ht01
    have hd012' : 1 - k ^ 2 * jacobiSn (t * z 0 + t * z 1) k ^ 2 * jacobiSn (t * z 2) k ^ 2 ≠ 0 :=
        by
      simpa only [mul_add] using hd012
    have hsum : t * z 0 + t * z 1 + t * z 2 + t * z 3 = 0 := by linear_combination t * hz
    obtain ⟨hdet, hprod⟩ := det_and_product_eq_zero_of_additionDenominators_ne_zero hk (fun i => t *
        z i) hsum ht ht01' hd01 hd012'
    constructor
    · change Matrix.det (Matrix.of fun i : Fin 4 =>
        ![L .s (t * z i), L .c (t * z i), L .d (t * z i), L .n (t * z i)]) = 0
      rw [det_thetaMatrix_eq_prod_mul_det k _ ht, hdet, mul_zero]
    · change (1 - k ^ 2) * (∏ i, L .n (t * z i)) - (1 - k ^ 2) * k ^ 2 * (∏ i, L .s (t * z i)) +
        k ^ 2 * (∏ i, L .c (t * z i)) - (∏ i, L .d (t * z i)) = 0
      rw [product_theta_eq_prod_mul_relation k _ ht, hprod, mul_zero]
  have haf : AnalyticOnNhd ℂ f univ := fun w _ => hf.analyticAt w
  have hag : AnalyticOnNhd ℂ g univ := fun w _ => hg.analyticAt w
  have hf1 : f 1 = 0 := haf.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (mem_univ 0)
      (hnear.mono fun _ h => h.1) (mem_univ 1)
  have hg1 : g 1 = 0 := hag.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (mem_univ 0)
      (hnear.mono fun _ h => h.2) (mem_univ 1)
  have hn : (∏ i, jacobiLetterTheta .n (jacobiThetaArgument (z i) k) (jacobiTau k)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => hreg i
  constructor
  · simp only [f, M, L, one_mul] at hf1
    rw [det_thetaMatrix_eq_prod_mul_det k z hreg] at hf1
    exact (mul_eq_zero.mp hf1).resolve_left hn
  · simp only [g, L, one_mul] at hg1
    rw [product_theta_eq_prod_mul_relation k z hreg] at hg1
    exact (mul_eq_zero.mp hg1).resolve_left hn

end DLMF.JacobiElliptic.FourPointAddition
