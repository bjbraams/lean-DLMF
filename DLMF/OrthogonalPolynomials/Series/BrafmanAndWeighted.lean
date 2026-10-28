/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Series.JacobiParameterSeries

/-!
# Brafman and weighted Jacobi generating functions

Brafman product formulas and weighted Jacobi generating series on their specified complex
branches.

Source references and common attribution are retained in
`DLMF.OrthogonalPolynomials.Series`.
-/

@[expose] public section

open Complex Polynomial MeasureTheory Filter

open scoped Real Nat Topology

open DLMF.Hypergeometric

open DLMF.Confluent

open DLMF.Bessel

noncomputable section

set_option autoImplicit false

namespace DLMF.OrthogonalPolynomials

section JacobiBrafman

open Metric Set
open scoped ComplexConjugate

/-- The square of `R conj(1 - w)`, `R² = 1 - 2xw + w²`, is never a nonpositive real for
`|w| < 1`, `|x| ≤ 1`. -/
theorem jacB_sq_not_nonpos {x : ℝ} (hx : |x| ≤ 1) {w : ℂ} (hw : ‖w‖ < 1) :
    ¬ (((1 - 2 * x * w + w ^ 2) * conj (1 - w) ^ 2).im = 0 ∧
      ((1 - 2 * x * w + w ^ 2) * conj (1 - w) ^ 2).re ≤ 0) := by
  rintro ⟨him, hre⟩
  have hw2 : w.re ^ 2 + w.im ^ 2 < 1 := by
    have := Complex.sq_norm w
    rw [Complex.normSq_apply] at this
    nlinarith [norm_nonneg w]
  have e1 : ((1 - 2 * x * w + w ^ 2) * conj (1 - w) ^ 2).im =
      2 * (1 - x) * w.im * (1 - w.re ^ 2 - w.im ^ 2) := by
    simp only [pow_two, mul_im, mul_re, sub_re, sub_im, add_re, add_im, one_re, one_im,
      conj_re, conj_im, ofReal_re, ofReal_im, re_ofNat, im_ofNat]
    ring
  have e2 : ((1 - 2 * x * w + w ^ 2) * conj (1 - w) ^ 2).re =
      ((1 - w.re) ^ 2 + w.im ^ 2) ^ 2 +
        2 * (1 - x) * (w.re * (1 + w.re ^ 2 + w.im ^ 2) - 2 * (w.re ^ 2 + w.im ^ 2)) := by
    simp only [pow_two, mul_im, mul_re, sub_re, sub_im, add_re, add_im, one_re, one_im,
      conj_re, conj_im, ofReal_re, ofReal_im, re_ofNat, im_ofNat]
    ring
  rw [e1] at him
  rw [e2] at hre
  have hp1 : w.re < 1 := by nlinarith [sq_nonneg w.im]
  have hpos : 0 < 1 - w.re ^ 2 - w.im ^ 2 := by linarith
  have hxq : (1 - x) * w.im = 0 := by
    have : 2 * ((1 - x) * w.im) * (1 - w.re ^ 2 - w.im ^ 2) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · linarith
  rcases mul_eq_zero.mp hxq with h | h
  · have hx1 : x = 1 := by linarith
    subst hx1
    nlinarith [sq_nonneg w.im, sq_pos_of_pos (sub_pos.mpr hp1)]
  · rw [h] at hre
    have hxp : x * w.re ≤ |w.re| := by
      calc x * w.re ≤ |x * w.re| := le_abs_self _
        _ = |x| * |w.re| := abs_mul _ _
        _ ≤ 1 * |w.re| := mul_le_mul_of_nonneg_right hx (abs_nonneg _)
        _ = |w.re| := one_mul _
    have hpa : |w.re| < 1 := by
      rw [h] at hw2
      have h3 := sq_lt_sq.mp (show w.re ^ 2 < 1 ^ 2 by linarith)
      simpa using h3
    have hq : 0 < 1 - 2 * x * w.re + w.re ^ 2 := by
      nlinarith [sq_abs w.re, sq_nonneg (1 - |w.re|)]
    have hfac : ((1 - w.re) ^ 2 + 0 ^ 2) ^ 2 +
        2 * (1 - x) * (w.re * (1 + w.re ^ 2 + 0 ^ 2) - 2 * (w.re ^ 2 + 0 ^ 2)) =
        (1 - w.re) ^ 2 * (1 - 2 * x * w.re + w.re ^ 2) := by ring
    rw [hfac] at hre
    have := mul_pos (sq_pos_of_pos (sub_pos.mpr hp1)) hq
    linarith

/-- `Re(R conj(1 - z)) > 0` on the unit disc, `R = (1 - 2xz + z²)^{1/2}` (principal branch). -/
theorem jacB_re_pos {x : ℝ} (hx : |x| ≤ 1) {z : ℂ} (hz : ‖z‖ < 1) :
    0 < ((1 - 2 * x * z + z ^ 2) ^ (1 / 2 : ℂ) * conj (1 - z)).re := by
  set g : ℂ → ℝ := fun w => ((1 - 2 * x * w + w ^ 2) ^ (1 / 2 : ℂ) * conj (1 - w)).re with hg
  have hne : ∀ w ∈ ball (0 : ℂ) 1, g w ≠ 0 := by
    intro w hw h0
    have hw1 : ‖w‖ < 1 := by simpa using hw
    have hR2 : ((1 - 2 * x * w + w ^ 2) ^ (1 / 2 : ℂ)) ^ 2 = 1 - 2 * x * w + w ^ 2 :=
      cpow_half_sq (slitPlane_ne_zero (jacGen_mem_slitPlane hx hw1))
    set s := (1 - 2 * x * w + w ^ 2) ^ (1 / 2 : ℂ) * conj (1 - w) with hs
    have hs2 : s ^ 2 = (1 - 2 * x * w + w ^ 2) * conj (1 - w) ^ 2 := by
      rw [hs, mul_pow, hR2]
    have hsre : s.re = 0 := h0
    have him : (s ^ 2).im = 0 := by rw [pow_two, mul_im, hsre]; ring
    have hre : (s ^ 2).re ≤ 0 := by
      rw [pow_two, mul_re, hsre]; nlinarith [sq_nonneg s.im]
    rw [hs2] at him hre
    exact jacB_sq_not_nonpos hx hw1 ⟨him, hre⟩
  have hcont : ContinuousOn g (ball 0 1) := by
    intro w hw
    have hw1 : ‖w‖ < 1 := by simpa using hw
    have hRd : DifferentiableAt ℂ (fun w : ℂ => (1 - 2 * x * w + w ^ 2) ^ (1 / 2 : ℂ)) w :=
      DifferentiableAt.cpow (f := fun w : ℂ => 1 - 2 * x * w + w ^ 2) (by fun_prop)
        (differentiableAt_const _) (jacGen_mem_slitPlane hx hw1)
    have : ContinuousAt (fun w : ℂ => (1 - 2 * x * w + w ^ 2) ^ (1 / 2 : ℂ) * conj (1 - w)) w :=
      hRd.continuousAt.mul ((Complex.continuous_conj.comp (by fun_prop)).continuousAt)
    exact (Complex.continuous_re.continuousAt.comp this).continuousWithinAt
  have hpc := (convex_ball (0 : ℂ) 1).isPreconnected.image g hcont
  have h0 : g 0 = 1 := by simp [hg]
  by_contra hle
  push Not at hle
  have hz' : z ∈ ball (0 : ℂ) 1 := by simpa using hz
  have h00 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := by simp
  have hsub := hpc.Icc_subset (mem_image_of_mem g hz') (mem_image_of_mem g h00)
  obtain ⟨w, hw, hw0⟩ := hsub ⟨hle, by rw [h0]; exact zero_le_one⟩
  exact hne w hw hw0

/-- `|(1 - R - z)/2|² ≤ |z|` on the unit disc (the two roots of `4U² - 4(1-z)U + 2(1-x)z`
have product `(x-1)z/2`, and the one with the minus sign is the smaller). -/
theorem jacB_norm_sq_le {x : ℝ} (hx : |x| ≤ 1) {z : ℂ} (hz : ‖z‖ < 1) :
    ‖(1 - (1 - 2 * x * z + z ^ 2) ^ (1 / 2 : ℂ) - z) / 2‖ ^ 2 ≤ ‖z‖ := by
  set R := (1 - 2 * x * z + z ^ 2) ^ (1 / 2 : ℂ) with hR
  have hR2 : R ^ 2 = 1 - 2 * x * z + z ^ 2 :=
    cpow_half_sq (slitPlane_ne_zero (jacGen_mem_slitPlane hx hz))
  have hre := jacB_re_pos hx hz
  rw [← hR] at hre
  set A := 1 - z with hA
  have hle : ‖A - R‖ ≤ ‖A + R‖ := by
    have h1 : ‖A - R‖ ^ 2 ≤ ‖A + R‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_sub, Complex.normSq_add]
      have : (A * conj R).re = (R * conj A).re := by
        rw [show A * conj R = conj (R * conj A) by simp [mul_comm], Complex.conj_re]
      linarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h1
  have hprod : (1 - R - z) / 2 * ((A + R) / 2) = (x - 1) / 2 * z := by
    rw [hA]; linear_combination (-1 / 4 : ℂ) * hR2
  have hx1 : ‖((x : ℂ) - 1) / 2‖ ≤ 1 := by
    rw [norm_div, show ((x : ℂ) - 1) = ((x - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs]
    norm_num
    have := abs_le.mp hx
    rw [div_le_one two_pos, abs_le]; constructor <;> linarith
  have hU : ‖(1 - R - z) / 2‖ ≤ ‖(A + R) / 2‖ := by
    rw [norm_div, norm_div, show 1 - R - z = A - R by rw [hA]; ring]
    gcongr
  calc ‖(1 - R - z) / 2‖ ^ 2 = ‖(1 - R - z) / 2‖ * ‖(1 - R - z) / 2‖ := pow_two _
    _ ≤ ‖(1 - R - z) / 2‖ * ‖(A + R) / 2‖ := mul_le_mul_of_nonneg_left hU (norm_nonneg _)
    _ = ‖((x : ℂ) - 1) / 2‖ * ‖z‖ := by rw [← norm_mul, hprod, norm_mul]
    _ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right hx1 (norm_nonneg _)
    _ = ‖z‖ := one_mul _

/-- The companion bound `|(1 - R + z)/2|² ≤ |z|`, by `(x, z) ↦ (-x, -z)`. -/
theorem jacB_norm_sq_le' {x : ℝ} (hx : |x| ≤ 1) {z : ℂ} (hz : ‖z‖ < 1) :
    ‖(1 - (1 - 2 * x * z + z ^ 2) ^ (1 / 2 : ℂ) + z) / 2‖ ^ 2 ≤ ‖z‖ := by
  have h := jacB_norm_sq_le (x := -x) (by rwa [abs_neg]) (z := -z) (by rwa [norm_neg])
  have e : (1 - 2 * ((-x : ℝ) : ℂ) * -z + (-z) ^ 2) = 1 - 2 * x * z + z ^ 2 := by
    push_cast; ring
  rw [e, norm_neg, sub_neg_eq_add] at h
  exact h

/-- The antidiagonal sums of Appell's `F₄` at `((x-1)/2, (x+1)/2)` are Jacobi polynomials
(by 18.5.8). -/
theorem jacB_coeff {α β : ℂ} (hα : -1 < α.re) (hβ : -1 < β.re) (γ x : ℂ) (N : ℕ) :
    ∑ p ∈ Finset.antidiagonal N, appF4Coeff γ (α + β + 1 - γ) (α + 1) (β + 1) p.1 p.2 *
        ((x - 1) / 2) ^ p.1 * ((x + 1) / 2) ^ p.2 =
      poch γ N * poch (α + β + 1 - γ) N / (poch (α + 1) N * poch (β + 1) N) *
        jacobiPolyP α β N x := by
  have hpa : ∀ j, poch (α + 1) j ≠ 0 := poch_ne_zero_of_not_neg_nat
    (not_neg_nat_of_re_pos (by simp only [add_re, one_re]; linarith))
  have hpb : ∀ j, poch (β + 1) j ≠ 0 := poch_ne_zero_of_not_neg_nat
    (not_neg_nat_of_re_pos (by simp only [add_re, one_re]; linarith))
  rw [jacobi_binomial_sum hα N x, ← mul_assoc, Finset.mul_sum,
    ← Finset.Nat.sum_antidiagonal_swap]
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun n m =>
      appF4Coeff γ (α + β + 1 - γ) (α + 1) (β + 1) m n * ((x - 1) / 2) ^ m * ((x + 1) / 2) ^ n)]
  refine Finset.sum_congr rfl fun k hk => ?_
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
  rw [Nat.add_sub_cancel_left]
  have e1 : α + ((k + m : ℕ) : ℂ) - k + 1 = α + 1 + m := by push_cast; ring
  rw [e1]
  unfold appF4Coeff
  rw [add_comm k m, poch_add (α + 1) m k,
    show poch (β + 1) (m + k) = poch (β + 1) k * poch (β + 1 + k) m by rw [add_comm m k, poch_add],
    show β + (k : ℂ) + 1 = β + 1 + k by ring, pow_add, div_pow, div_pow]
  have := hpa m; have := hpb k
  have := hpa k; have := hpb m
  have hpa' : poch (α + 1 + m) k ≠ 0 := fun h => hpa (m + k) (by rw [poch_add, h, mul_zero])
  have hpb' : poch (β + 1 + k) m ≠ 0 := fun h => hpb (k + m) (by rw [poch_add, h, mul_zero])
  field_simp

/-- Regrouping a summable double series along antidiagonals. -/
theorem jacB_hasSum_antidiagonal {A : ℕ × ℕ → ℂ} {S : ℂ} (h : HasSum A S) :
    HasSum (fun n => ∑ p ∈ Finset.antidiagonal n, A p) S := by
  have h' := (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.hasSum_iff (f := A)).mpr h
  refine h'.sigma fun n => ?_
  have := hasSum_fintype (fun p : Finset.antidiagonal n => A p)
  rwa [Finset.sum_coe_sort] at this

/-- Brafman's generating function for small `|z|`, from Bailey's product formula
`appF4_bailey`: with `U = (1 - R - z)/2`, `V = (1 - R + z)/2` one has `U(1 - V) = (x-1)z/2`
and `V(1 - U) = (x+1)z/2`. -/
theorem jacB_hasSum_small {α β : ℂ} (hα : -1 < α.re) (hβ : -1 < β.re) (γ : ℂ) {x : ℝ}
    (hx : |x| ≤ 1) : ∃ ε > 0, ∀ z ∈ ball (0 : ℂ) ε,
    HasSum (fun n : ℕ => poch γ n * poch (α + β + 1 - γ) n /
      (poch (α + 1) n * poch (β + 1) n) * jacobiPolyP α β n x * z ^ n)
      (₂F₁ γ (α + β + 1 - γ) (α + 1) ((1 - (1 - 2 * x * z + z ^ 2) ^ (1 / 2 : ℂ) - z) / 2) *
       ₂F₁ γ (α + β + 1 - γ) (β + 1) ((1 - (1 - 2 * x * z + z ^ 2) ^ (1 / 2 : ℂ) + z) / 2)) := by
  have hcc : (α + 1) + (β + 1) = γ + (α + β + 1 - γ) + 1 := by ring
  obtain ⟨δ, hδ, hB⟩ := appF4_bailey hcc (by simp only [add_re, one_re]; linarith)
    (by simp only [add_re, one_re]; linarith)
  refine ⟨min (δ ^ 2) 1, lt_min (by positivity) one_pos, fun z hz => ?_⟩
  have hz' : ‖z‖ < min (δ ^ 2) 1 := by simpa using hz
  have hz1 : ‖z‖ < 1 := lt_of_lt_of_le hz' (min_le_right _ _)
  have hzδ : ‖z‖ < δ ^ 2 := lt_of_lt_of_le hz' (min_le_left _ _)
  have hUs := jacB_norm_sq_le hx hz1
  have hVs := jacB_norm_sq_le' hx hz1
  set R := (1 - 2 * (x : ℂ) * z + z ^ 2) ^ (1 / 2 : ℂ) with hR
  have hR2 : R ^ 2 = 1 - 2 * x * z + z ^ 2 :=
    cpow_half_sq (slitPlane_ne_zero (jacGen_mem_slitPlane hx hz1))
  have hU : ‖(1 - R - z) / 2‖ < δ :=
    (pow_lt_pow_iff_left₀ (norm_nonneg _) hδ.le two_ne_zero).mp (by linarith)
  have hV : ‖(1 - R + z) / 2‖ < δ :=
    (pow_lt_pow_iff_left₀ (norm_nonneg _) hδ.le two_ne_zero).mp (by linarith)
  have h := hB _ _ hU hV
  have e1 : (1 - R - z) / 2 * (1 - (1 - R + z) / 2) = (x - 1) / 2 * z := by
    linear_combination (-1 / 4 : ℂ) * hR2
  have e2 : (1 - R + z) / 2 * (1 - (1 - R - z) / 2) = (x + 1) / 2 * z := by
    linear_combination (-1 / 4 : ℂ) * hR2
  rw [e1, e2] at h
  have h2 := jacB_hasSum_antidiagonal h
  refine h2.congr_fun fun N => ?_
  rw [← jacB_coeff hα hβ γ x N, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mem_antidiagonal] at hp
  rw [← hp, mul_pow, mul_pow, pow_add]
  ring

/-- The right side of Brafman's formula is holomorphic on the unit disc. -/
theorem jacB_differentiableOn (α β γ : ℂ) {x : ℝ} (hx : |x| ≤ 1) :
    DifferentiableOn ℂ (fun z : ℂ =>
      ₂F₁ γ (α + β + 1 - γ) (α + 1) ((1 - (1 - 2 * x * z + z ^ 2) ^ (1 / 2 : ℂ) - z) / 2) *
       ₂F₁ γ (α + β + 1 - γ) (β + 1) ((1 - (1 - 2 * x * z + z ^ 2) ^ (1 / 2 : ℂ) + z) / 2))
      (ball 0 1) := by
  intro w hw
  have hw1 : ‖w‖ < 1 := by simpa using hw
  have hRd : DifferentiableAt ℂ (fun w : ℂ => (1 - 2 * x * w + w ^ 2) ^ (1 / 2 : ℂ)) w :=
    DifferentiableAt.cpow (f := fun w : ℂ => 1 - 2 * x * w + w ^ 2) (by fun_prop)
      (differentiableAt_const _) (jacGen_mem_slitPlane hx hw1)
  have hU1 : ‖(1 - (1 - 2 * x * w + w ^ 2) ^ (1 / 2 : ℂ) - w) / 2‖ < 1 :=
    (pow_lt_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp
      (lt_of_le_of_lt (jacB_norm_sq_le hx hw1) hw1)
  have hV1 : ‖(1 - (1 - 2 * x * w + w ^ 2) ^ (1 / 2 : ℂ) + w) / 2‖ < 1 :=
    (pow_lt_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp
      (lt_of_le_of_lt (jacB_norm_sq_le' hx hw1) hw1)
  have hUd : DifferentiableAt ℂ
      (fun w : ℂ => (1 - (1 - 2 * x * w + w ^ 2) ^ (1 / 2 : ℂ) - w) / 2) w :=
    (((differentiableAt_const _).sub hRd).sub differentiableAt_id).div_const 2
  have hVd : DifferentiableAt ℂ
      (fun w : ℂ => (1 - (1 - 2 * x * w + w ^ 2) ^ (1 / 2 : ℂ) + w) / 2) w :=
    (((differentiableAt_const _).sub hRd).add differentiableAt_id).div_const 2
  exact (((analyticAt_ordinaryHypergeometric hU1).differentiableAt.comp w hUd).mul
    ((analyticAt_ordinaryHypergeometric hV1).differentiableAt.comp w hVd)).differentiableWithinAt

end JacobiBrafman

/-- The series with terms `(fun n : ℕ => poch γ n * poch (α + β + 1 - γ) n / (poch (α + 1) n *
poch (β + 1) n) * jacobiPolyP α β n x * z ^ n)` converges to `(₂F₁ γ (α + β + 1 - γ) (α + 1)
((1 - (1 - 2 * x * z + z ^ 2) ^ (1 / 2 : ℂ) - z) / 2) * ₂F₁ γ (α + β + 1 - γ) (β + 1) ((1 - (1
- 2 * x * z + z ^ 2) ^ (1 / 2 : ℂ) + z) / 2))`. -/
@[dlmf 18.12.E2_5]
theorem jacobi_brafman_generating_function {α β : ℂ} (hα : -1 < α.re)
    (hβ : -1 < β.re) (γ : ℂ) {x : ℝ} (hx : |x| ≤ 1) {z : ℂ} (hz : ‖z‖ < 1)
    (hu : ‖(1 - (1 - 2 * x * z + z ^ 2) ^ (1 / 2 : ℂ) - z) / 2‖ < 1)
    (hv : ‖(1 - (1 - 2 * x * z + z ^ 2) ^ (1 / 2 : ℂ) + z) / 2‖ < 1) :
    HasSum (fun n : ℕ => poch γ n * poch (α + β + 1 - γ) n /
      (poch (α + 1) n * poch (β + 1) n) * jacobiPolyP α β n x * z ^ n)
      (₂F₁ γ (α + β + 1 - γ) (α + 1) ((1 - (1 - 2 * x * z + z ^ 2) ^ (1 / 2 : ℂ) - z) / 2) *
       ₂F₁ γ (α + β + 1 - γ) (β + 1) ((1 - (1 - 2 * x * z + z ^ 2) ^ (1 / 2 : ℂ) + z) / 2)) := by
  -- `hu` and `hv` are redundant: they follow from `|z| < 1` (`jacB_norm_sq_le`).
  have _hu := hu
  have _hv := hv
  obtain ⟨ε, hε, hsmall⟩ := jacB_hasSum_small hα hβ γ hx
  exact Complex.lagB_hasSum_of_differentiableOn (c := fun n => poch γ n *
      poch (α + β + 1 - γ) n / (poch (α + 1) n * poch (β + 1) n) * jacobiPolyP α β n x)
    hε (jacB_differentiableOn α β γ hx) hsmall (by simpa using hz)

section JacobiWeighted

open Metric Set

/-- `k! ≤ (1 + 1/(Re β + 1))^k |(β+1)_k|` for `Re β > -1`. -/
theorem jacW_factorial_le_norm_poch {β : ℂ} (hβ : -1 < β.re) (k : ℕ) :
    (k ! : ℝ) ≤ (1 + 1 / (β.re + 1)) ^ k * ‖poch (β + 1) k‖ := by
  have hσ : 0 < β.re + 1 := by linarith
  induction k with
  | zero => simp [poch_zero]
  | succ k ih =>
    rw [poch_succ, norm_mul, Nat.factorial_succ, pow_succ]
    have h1 : (β.re + 1 + k) ≤ ‖β + 1 + k‖ := by
      have := Complex.re_le_norm (β + 1 + k)
      simpa using this
    have h2 : ((k : ℝ) + 1) ≤ (1 + 1 / (β.re + 1)) * ‖β + 1 + k‖ := by
      have h3 : ((k : ℝ) + 1) ≤ (1 + 1 / (β.re + 1)) * (β.re + 1 + k) := by
        rw [add_mul, one_div, inv_mul_eq_div, add_div, div_self hσ.ne']
        have : 0 ≤ (k : ℝ) / (β.re + 1) := by positivity
        linarith
      exact h3.trans (mul_le_mul_of_nonneg_left h1 (by positivity))
    push_cast
    calc ((k : ℝ) + 1) * k ! ≤ ((1 + 1 / (β.re + 1)) * ‖β + 1 + k‖) *
          ((1 + 1 / (β.re + 1)) ^ k * ‖poch (β + 1) k‖) :=
          mul_le_mul h2 ih (by positivity) (by positivity)
      _ = _ := by ring

/-- `(2k+m)! ≤ 2^{2k+m} 4^k k!² m!`. -/
theorem jacW_factorial_two_mul_add_le (k m : ℕ) :
    ((2 * k + m)! : ℝ) ≤ 2 ^ (2 * k + m) * 4 ^ k * (k ! * k ! * m !) := by
  have h1 : (2 * k + m)! = (2 * k + m).choose m * ((2 * k)! * m !) := by
    have := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left m (2 * k))
    rw [Nat.add_sub_cancel] at this
    rw [← this]; ring
  have h2 : (2 * k)! = (2 * k).choose k * (k ! * k !) := by
    have := Nat.choose_mul_factorial_mul_factorial (show k ≤ 2 * k by omega)
    rw [show 2 * k - k = k by omega] at this
    rw [← this]; ring
  have hc1 : ((2 * k + m).choose m : ℝ) ≤ 2 ^ (2 * k + m) := by
    exact_mod_cast Nat.choose_le_two_pow _ _
  have hc2 : ((2 * k).choose k : ℝ) ≤ 4 ^ k := by
    have := Nat.choose_le_two_pow (2 * k) k
    rw [pow_mul] at this
    exact_mod_cast this
  rw [h1, h2]
  push_cast
  calc ((2 * k + m).choose m : ℝ) * (((2 * k).choose k : ℝ) * (k ! * k !) * m !)
      ≤ 2 ^ (2 * k + m) * (4 ^ k * (k ! * k !) * m !) := by gcongr
    _ = _ := by ring

/-- The double-series term behind 18.12.3:
`(λ)_{2k+m} (-1)^m y^k z^{k+m} / ((β+1)_k k! m!)`. -/
noncomputable def jacWTerm (l β y z : ℂ) (p : ℕ × ℕ) : ℂ :=
  poch l (2 * p.1 + p.2) * (-1) ^ p.2 * y ^ p.1 * z ^ (p.1 + p.2) /
    (poch (β + 1) p.1 * p.1 ! * p.2 !)

/-- A geometric bound for `jacWTerm`. -/
theorem jacWTerm_norm_le (l : ℂ) {β : ℂ} (hβ : -1 < β.re) {y : ℂ} (hy : ‖y‖ ≤ 1) (z : ℂ)
    (p : ℕ × ℕ) : ‖jacWTerm l β y z p‖ ≤
      (16 * (1 + ‖l‖) ^ 2 * (1 + 1 / (β.re + 1)) * ‖z‖) ^ p.1 * (2 * (1 + ‖l‖) * ‖z‖) ^ p.2 := by
  obtain ⟨k, m⟩ := p
  simp only
  have hσ : 0 < β.re + 1 := by linarith
  have hP := jacW_factorial_le_norm_poch hβ k
  have hPpos : 0 < ‖poch (β + 1) k‖ := by
    by_contra h
    push Not at h
    have h0 : ‖poch (β + 1) k‖ = 0 := le_antisymm h (norm_nonneg _)
    rw [h0, mul_zero] at hP
    exact absurd hP (not_le.mpr (by exact_mod_cast k.factorial_pos))
  have hL := appF4_norm_poch_le l (2 * k + m)
  have hF := jacW_factorial_two_mul_add_le k m
  have hk : (0 : ℝ) < k ! := by exact_mod_cast k.factorial_pos
  have hm : (0 : ℝ) < m ! := by exact_mod_cast m.factorial_pos
  unfold jacWTerm
  rw [norm_div, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, norm_pow,
    norm_neg, norm_one, one_pow, mul_one, Complex.norm_natCast, Complex.norm_natCast,
    div_le_iff₀ (by positivity)]
  have hyk : ‖y‖ ^ k ≤ 1 := pow_le_one₀ (norm_nonneg _) hy
  have hz := norm_nonneg z
  have hl := norm_nonneg l
  calc ‖poch l (2 * k + m)‖ * ‖y‖ ^ k * ‖z‖ ^ (k + m)
      ≤ ((1 + ‖l‖) ^ (2 * k + m) * (2 * k + m)!) * 1 * ‖z‖ ^ (k + m) := by gcongr
    _ ≤ ((1 + ‖l‖) ^ (2 * k + m) * (2 ^ (2 * k + m) * 4 ^ k * (k ! * k ! * m !))) * 1 *
          ‖z‖ ^ (k + m) := by gcongr
    _ ≤ ((1 + ‖l‖) ^ (2 * k + m) * (2 ^ (2 * k + m) * 4 ^ k *
          (((1 + 1 / (β.re + 1)) ^ k * ‖poch (β + 1) k‖) * k ! * m !))) * 1 *
          ‖z‖ ^ (k + m) := by gcongr
    _ = _ := by
      simp only [mul_pow, ← pow_mul, pow_add]
      rw [show (16 : ℝ) = 2 ^ 2 * 4 by norm_num, mul_pow, ← pow_mul]
      ring

/-- Duplication for rising factorials: `(2a)_{2m} = 4^m (a)_m (a + 1/2)_m`. -/
theorem jacW_poch_two_mul (a : ℂ) (m : ℕ) :
    poch (2 * a) (2 * m) = 4 ^ m * poch a m * poch (a + 1 / 2) m := by
  exact poch_two_mul_two_mul a m

/-- The `m`-sums of `jacWTerm` are binomial series. -/
theorem jacWTerm_hasSum_fiber (l β y : ℂ) {z : ℂ} (hz : ‖z‖ < 1) (k : ℕ) :
    HasSum (fun m => jacWTerm l β y z (k, m))
      (poch l (2 * k) / (poch (β + 1) k * k !) * (y * z) ^ k * (1 + z) ^ (-(l + 2 * k))) := by
  have hz' : ‖-z‖ < 1 := by rwa [norm_neg]
  have h := (hasSum_poch_div_factorial (β := l + 2 * k) hz').mul_left
    (poch l (2 * k) / (poch (β + 1) k * k !) * (y * z) ^ k)
  rw [sub_neg_eq_add] at h
  refine h.congr_fun fun m => ?_
  unfold jacWTerm
  simp only
  rw [poch_add, show l + ((2 * k : ℕ) : ℂ) = l + 2 * k by push_cast; ring]
  have h1 : (m ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr m.factorial_ne_zero
  rw [neg_pow z, pow_add, mul_pow]
  by_cases hp : poch (β + 1) k = 0
  · simp [hp]
  have h2 : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  field_simp

/-- The `k`-sum of the fibre sums is `(1+z)^{-λ} ₂F₁(λ/2, λ/2 + 1/2; β+1; 4yz/(1+z)²)`. -/
theorem jacWTerm_hasSum_outer (l β y : ℂ) {z : ℂ} (hz : ‖z‖ < 1)
    (hv : ‖4 * y * z / (1 + z) ^ 2‖ < 1) :
    HasSum (fun k : ℕ => poch l (2 * k) / (poch (β + 1) k * k !) * (y * z) ^ k *
      (1 + z) ^ (-(l + 2 * k)))
      ((1 + z) ^ (-l) * ₂F₁ (l / 2) (l / 2 + 1 / 2) (β + 1) (4 * y * z / (1 + z) ^ 2)) := by
  have hz0 : 1 + z ≠ 0 := by
    intro h
    have : z = -1 := by linear_combination h
    rw [this] at hz; simp at hz
  have h := ((hasFPowerSeriesOnBall_ordinaryHypergeometric (l / 2) (l / 2 + 1 / 2)
    (β + 1)).hasSum_mul_pow (mem_eball_one_of_norm_lt_one hv)).mul_left ((1 + z) ^ (-l))
  refine h.congr_fun fun k => ?_
  have hpoch : poch l (2 * k) = 4 ^ k * poch (l / 2) k * poch (l / 2 + 1 / 2) k := by
    have := jacW_poch_two_mul (l / 2) k
    rwa [show 2 * (l / 2) = l by ring] at this
  have hcp : (1 + z) ^ (-(l + 2 * k)) = (1 + z) ^ (-l) * (((1 + z) ^ 2) ^ k)⁻¹ := by
    rw [neg_add, cpow_add _ _ hz0, cpow_neg (1 + z) (2 * k),
      show (2 : ℂ) * k = ((2 * k : ℕ) : ℂ) by push_cast; ring, cpow_natCast, pow_mul]
  rw [hcp, hpoch, gaussHGCoeff, div_pow, mul_pow, mul_pow, mul_pow]
  by_cases hp : poch (β + 1) k = 0
  · simp [hp]
  have h2 : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have h3 : ((1 + z) ^ 2) ^ k ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hz0)
  field_simp

/-- The Jacobi coefficient of 18.12.3 as an antidiagonal sum of `jacWTerm`. -/
theorem jacW_coeff_eq_sum_antidiagonal {α β : ℂ} (hα : -1 < α.re) (hβ : -1 < β.re) (x z : ℂ)
    (n : ℕ) :
    poch (α + β + 1) n / poch (β + 1) n * jacobiPolyP α β n x * z ^ n =
      ∑ p ∈ Finset.antidiagonal n, jacWTerm (α + β + 1) β ((x + 1) / 2) z p := by
  have hβ' : ∀ k : ℕ, β + 1 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by
    simp only [Complex.add_re, Complex.one_re]
    linarith)
  have hrefl := jacobi_reflection hα hβ n (-x)
  rw [neg_neg] at hrefl
  rw [hrefl, jacobi_finite_sum hβ n (-x),
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => jacWTerm (α + β + 1) β
      ((x + 1) / 2) z (i, j)), Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  obtain ⟨m, rfl⟩ : ∃ m, n = k + m := ⟨n - k, by omega⟩
  rw [Nat.add_sub_cancel_left]
  unfold jacWTerm
  simp only
  rw [show 2 * k + m = (k + m) + k by ring, poch_add (α + β + 1) (k + m) k,
    poch_add (β + 1) k m]
  have hpk := poch_ne_zero_of_not_neg_nat hβ' k
  have hpm : poch (β + 1 + k) m ≠ 0 := by
    have : ∀ j : ℕ, β + 1 + k ≠ -(j : ℂ) := not_neg_nat_of_re_pos (by
      simp only [Complex.add_re, Complex.one_re, Complex.natCast_re]
      linarith [(Nat.cast_nonneg (α := ℝ) k)])
    exact poch_ne_zero_of_not_neg_nat this m
  have h1 : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have h2 : (m ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr m.factorial_ne_zero
  rw [show ((k + m : ℕ) : ℂ) + β + α + 1 = α + β + 1 + ((k + m : ℕ) : ℂ) by ring,
    show β + k + 1 = β + 1 + k by ring, show (-x - 1) / 2 = -1 * ((x + 1) / 2) by ring,
    mul_pow]
  have hsq : (-1 : ℂ) ^ k * (-1) ^ k = 1 := by rw [← pow_add, ← two_mul, pow_mul]; simp
  calc _ = poch (α + β + 1) (k + m) * poch (α + β + 1 + ↑(k + m)) k * ((-1) ^ k * (-1) ^ k) *
        (-1) ^ m * ((x + 1) / 2) ^ k * z ^ (k + m) / (poch (β + 1) k * ↑k ! * ↑m !) := by
          field_simp
          rw [pow_add (-1 : ℂ) k m]
          ring
    _ = _ := by rw [hsq, mul_one]

/-- 18.12.3 for small `|z|`, by summing the double series in two ways. -/
theorem jacW_hasSum_small {α β : ℂ} (hα : -1 < α.re) (hβ : -1 < β.re) {x : ℝ} (hx : |x| ≤ 1)
    {z : ℂ} (hz : ‖z‖ < 1 / (32 * ((1 + ‖α + β + 1‖) ^ 2 * (1 + 1 / (β.re + 1))))) :
    HasSum (fun n : ℕ => poch (α + β + 1) n / poch (β + 1) n * jacobiPolyP α β n x * z ^ n)
      ((1 + z) ^ (-α - β - 1) * ₂F₁ ((α + β + 1) / 2) ((α + β + 2) / 2)
        (β + 1) (2 * (x + 1 : ℂ) * z / (1 + z) ^ 2)) := by
  set l := α + β + 1 with hl
  set y : ℂ := ((x : ℂ) + 1) / 2 with hy
  have hσ : 0 < β.re + 1 := by linarith
  set K := (1 + ‖l‖) ^ 2 * (1 + 1 / (β.re + 1)) with hK
  have hl0 := norm_nonneg l
  have hK1 : 1 ≤ K := by
    have h1 : 1 ≤ (1 + ‖l‖) ^ 2 := one_le_pow₀ (by linarith)
    have h2 : 1 ≤ 1 + 1 / (β.re + 1) := by have : 0 < 1 / (β.re + 1) := by positivity
                                           linarith
    nlinarith
  have hz0 := norm_nonneg z
  have hKz : K * ‖z‖ < 1 / 32 := by
    rw [lt_div_iff₀ (by positivity)] at hz
    nlinarith
  have hz32 : ‖z‖ < 1 / 32 := by nlinarith
  have hz1 : ‖z‖ < 1 := by linarith
  have hy1 : ‖y‖ ≤ 1 := by
    rw [hy, show ((x : ℂ) + 1) / 2 = (((x + 1) / 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [(abs_le.mp hx).1, (abs_le.mp hx).2]
  -- summability of the double series
  set P := 16 * (1 + ‖l‖) ^ 2 * (1 + 1 / (β.re + 1)) * ‖z‖ with hP
  set Q := 2 * (1 + ‖l‖) * ‖z‖ with hQ
  have hP0 : 0 ≤ P := by positivity
  have hQ0 : 0 ≤ Q := by positivity
  have hP1 : P < 1 := by
    have : P = 16 * (K * ‖z‖) := by rw [hP, hK]; ring
    rw [this]; linarith
  have hQ1 : Q < 1 := by
    have h1 : 2 * (1 + ‖l‖) ≤ 2 * K := by
      have : 1 + ‖l‖ ≤ (1 + ‖l‖) ^ 2 := by nlinarith
      have h3 : (1 + ‖l‖) ^ 2 ≤ K := by
        rw [hK]; have : 0 < 1 / (β.re + 1) := by positivity
        nlinarith
      linarith
    have : Q ≤ 2 * (K * ‖z‖) := by rw [hQ]; nlinarith
    linarith
  have hsum : Summable (jacWTerm l β y z) := by
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hP0 hP1).mul_of_nonneg
      (summable_geometric_of_lt_one hQ0 hQ1) (fun _ => by positivity) (fun _ => by positivity))
      (fun p => ?_)
    exact jacWTerm_norm_le l hβ hy1 z p
  -- the argument of `₂F₁`
  have hz1' : 31 / 32 ≤ ‖1 + z‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-z)
    rw [norm_one, norm_neg, sub_neg_eq_add] at this
    linarith
  have hv : ‖4 * y * z / (1 + z) ^ 2‖ < 1 := by
    rw [norm_div, norm_mul, norm_mul, norm_pow, Complex.norm_ofNat,
      div_lt_one (by positivity)]
    have : (31 / 32 : ℝ) ^ 2 ≤ ‖1 + z‖ ^ 2 := by gcongr
    nlinarith [norm_nonneg y]
  -- sum by fibres and by antidiagonals
  have hfib := hsum.hasSum.prod_fiberwise (fun k => jacWTerm_hasSum_fiber l β y hz1 k)
  have hval := (jacWTerm_hasSum_outer l β y hz1 hv).unique hfib
  have hanti := jacB_hasSum_antidiagonal hsum.hasSum
  rw [← hval] at hanti
  convert hanti using 1
  · funext n
    exact jacW_coeff_eq_sum_antidiagonal hα hβ (x : ℂ) z n
  · rw [show -α - β - 1 = -l by rw [hl]; ring, show (α + β + 1) / 2 = l / 2 by rw [hl],
      show (α + β + 2) / 2 = l / 2 + 1 / 2 by rw [hl]; ring,
      show 2 * ((x : ℂ) + 1) * z = 4 * y * z by rw [hy]; ring]

/-- The coefficients of 18.12.3 have radius of convergence at least `1`: for `0 ≤ r < 1`,
`|(α+β+1)_n/(β+1)_n P_n^{(α,β)}(x)| rⁿ → 0`, by 18.12.1 and the Gauss series. -/
theorem jacW_tendsto_coeff {α β : ℂ} (hα : -1 < α.re) (hβ : -1 < β.re) {x : ℝ} (hx : |x| ≤ 1)
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    Tendsto (fun n : ℕ => ‖poch (α + β + 1) n / poch (β + 1) n * jacobiPolyP α β n x‖ * r ^ n)
      atTop (𝓝 0) := by
  set s := Real.sqrt r with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg r
  have hs1 : s < 1 := by rw [hs, Real.sqrt_lt' one_pos]; simpa using hr
  have hss : s * s = r := Real.mul_self_sqrt hr0
  -- the Jacobi factor
  have hsn : ‖(s : ℂ)‖ < 1 := by rwa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0]
  have hJ := (jacobi_generating_function hα hβ hx hsn).summable.norm.tendsto_atTop_zero
  -- the Pochhammer factor
  have hrad := (hasFPowerSeriesOnBall_ordinaryHypergeometric (α + β + 1) 1 (β + 1)).r_le
  have hsr : ((s.toNNReal : NNReal) : ENNReal) <
      (FormalMultilinearSeries.ofScalars ℂ (gaussHGCoeff (α + β + 1) 1 (β + 1))).radius :=
    lt_of_lt_of_le (by rw [ENNReal.coe_lt_one_iff, Real.toNNReal_lt_one]; exact hs1) hrad
  have hG := ((FormalMultilinearSeries.ofScalars ℂ
    (gaussHGCoeff (α + β + 1) 1 (β + 1))).summable_norm_mul_pow hsr).tendsto_atTop_zero
  have := hG.mul hJ
  rw [zero_mul] at this
  refine this.congr fun n => ?_
  rw [FormalMultilinearSeries.ofScalars_norm, gaussHGCoeff, poch_nat_one, norm_mul, norm_mul,
    norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0, Real.coe_toNNReal _ hs0,
    ← hss, mul_pow]
  have hf : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  rw [mul_div_mul_right _ _ hf]
  ring

/-- Star-convexity of the domain of 18.12.3: shrinking `z` towards `0` decreases
`|z / (1 + z)²|` (`|1 + bz|² - b|1 + z|² = (1 - b)(1 - b|z|²)`). -/
theorem jacW_norm_div_sq_le {z : ℂ} (hz : ‖z‖ < 1) {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    ‖(b : ℂ) * z / (1 + (b : ℂ) * z) ^ 2‖ ≤ ‖z / (1 + z) ^ 2‖ := by
  have hz2 : z.re ^ 2 + z.im ^ 2 < 1 := by
    have := Complex.sq_norm z
    rw [Complex.normSq_apply] at this
    nlinarith [norm_nonneg z]
  have hne : ∀ c : ℂ, ‖c‖ < 1 → 1 + c ≠ 0 := fun c hc h => by
    have : c = -1 := by linear_combination h
    rw [this] at hc; simp at hc
  have hbz : ‖(b : ℂ) * z‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb0]
    nlinarith [norm_nonneg z]
  have h1 := hne z hz
  have h2 := hne _ hbz
  rw [norm_div, norm_div, norm_pow, norm_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hb0, div_le_div_iff₀ (by positivity) (by positivity)]
  have key : b * ‖1 + z‖ ^ 2 ≤ ‖1 + (b : ℂ) * z‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [add_re, one_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, add_im, one_im,
      mul_im, zero_add]
    nlinarith [mul_nonneg (sub_nonneg.2 hb1) (mul_nonneg hb0 (sub_nonneg.2 hz2.le))]
  have := mul_le_mul_of_nonneg_left key (norm_nonneg z)
  nlinarith [norm_nonneg z]

/-- The coefficient series of 18.12.3 has radius at least `1`. -/
theorem jacW_one_le_radius {α β : ℂ} (hα : -1 < α.re) (hβ : -1 < β.re) {x : ℝ} (hx : |x| ≤ 1) :
    1 ≤ (FormalMultilinearSeries.ofScalars ℂ
      (fun n : ℕ => poch (α + β + 1) n / poch (β + 1) n * jacobiPolyP α β n x)).radius := by
  refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
  have hr1 : (r : ℝ) < 1 := by exact_mod_cast hr
  refine FormalMultilinearSeries.le_radius_of_tendsto _ (l := 0) ?_
  refine (jacW_tendsto_coeff hα hβ hx r.2 hr1).congr fun n => ?_
  rw [FormalMultilinearSeries.ofScalars_norm]
  rfl

end JacobiWeighted

open Metric Set in
/-- The series with terms `(fun n : ℕ => poch (α + β + 1) n / poch (β + 1) n * jacobiPolyP α β n x
* z ^ n)` converges to `((1 + z) ^ (-α - β - 1) * ₂F₁ ((α + β + 1) / 2) ((α + β + 2) / 2) (β +
1) (2 * (x + 1 : ℂ) * z / (1 + z) ^ 2))`. -/
@[dlmf 18.12.E3]
theorem jacobi_weighted_generating_function {α β : ℂ} (hα : -1 < α.re)
    (hβ : -1 < β.re) {x : ℝ} (hx : |x| ≤ 1) {z : ℂ} (hz : ‖z‖ < 1)
    (hu : ‖2 * (x + 1 : ℂ) * z / (1 + z) ^ 2‖ < 1) :
    HasSum (fun n : ℕ => poch (α + β + 1) n / poch (β + 1) n * jacobiPolyP α β n x * z ^ n)
      ((1 + z) ^ (-α - β - 1) * ₂F₁ ((α + β + 1) / 2) ((α + β + 2) / 2)
        (β + 1) (2 * (x + 1 : ℂ) * z / (1 + z) ^ 2)) := by
  set c : ℕ → ℂ := fun n => poch (α + β + 1) n / poch (β + 1) n * jacobiPolyP α β n x with hc
  set p := FormalMultilinearSeries.ofScalars ℂ c with hp
  have hrad : 1 ≤ p.radius := jacW_one_le_radius hα hβ hx
  have hF : HasFPowerSeriesOnBall p.sum p 0 1 :=
    (p.hasFPowerSeriesOnBall (lt_of_lt_of_le one_pos hrad)).mono one_pos hrad
  have hFsum : ∀ w : ℂ, ‖w‖ < 1 → HasSum (fun n => c n * w ^ n) (p.sum w) := by
    intro w hw
    have := hF.hasSum (mem_eball_one_of_norm_lt_one hw)
    simpa [hp, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, mul_comm] using this
  -- the right side and its domain
  set v : ℂ → ℂ := fun w => 2 * (x + 1 : ℂ) * w / (1 + w) ^ 2 with hv
  set G : ℂ → ℂ := fun w => (1 + w) ^ (-α - β - 1) *
    ₂F₁ ((α + β + 1) / 2) ((α + β + 2) / 2) (β + 1) (v w) with hG
  have hne : ∀ w : ℂ, ‖w‖ < 1 → 1 + w ≠ 0 := fun w hw h => by
    have : w = -1 := by linear_combination h
    rw [this] at hw; simp at hw
  set D := ball (0 : ℂ) 1 ∩ v ⁻¹' ball 0 1 with hD
  have hD0 : (0 : ℂ) ∈ D := by simp [hD, hv]
  have hDs : StarConvex ℝ (0 : ℂ) D := by
    intro w hw a b ha hb hab
    obtain ⟨hw1, hw2⟩ := hw
    have hw1' : ‖w‖ < 1 := by simpa using hw1
    have hb1 : b ≤ 1 := by linarith
    simp only [smul_zero, zero_add, Complex.real_smul]
    refine ⟨?_, ?_⟩
    · rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb]
      nlinarith [norm_nonneg w]
    · have h2 : ‖v w‖ < 1 := by simpa using hw2
      rw [Set.mem_preimage, mem_ball_zero_iff]
      have hle := jacW_norm_div_sq_le hw1' hb hb1
      have e1 : v (b * w) = 2 * (x + 1 : ℂ) * ((b : ℂ) * w / (1 + (b : ℂ) * w) ^ 2) := by
        rw [hv]; ring
      have e2 : v w = 2 * (x + 1 : ℂ) * (w / (1 + w) ^ 2) := by rw [hv]; ring
      rw [e1, norm_mul]
      rw [e2, norm_mul] at h2
      calc _ ≤ ‖2 * ((x : ℂ) + 1)‖ * ‖w / (1 + w) ^ 2‖ :=
            mul_le_mul_of_nonneg_left hle (norm_nonneg _)
        _ < 1 := h2
  have hGa : AnalyticOnNhd ℂ G D := by
    intro w hw
    obtain ⟨hw1, hw2⟩ := hw
    have hw1' : ‖w‖ < 1 := by simpa using hw1
    have hw2' : ‖v w‖ < 1 := by simpa using hw2
    have hre : 0 < (1 + w).re := by
      have := Complex.abs_re_le_norm w
      simp only [add_re, one_re]; linarith [(abs_le.mp this).1]
    have hvA : AnalyticAt ℂ v w := by
      have := hne w hw1'
      exact AnalyticAt.div (f := fun w : ℂ => 2 * (x + 1 : ℂ) * w)
        (g := fun w : ℂ => (1 + w) ^ 2) (by fun_prop) (by fun_prop) (pow_ne_zero 2 this)
    have h1 : AnalyticAt ℂ (fun w : ℂ => (1 + w) ^ (-α - β - 1)) w :=
      AnalyticAt.cpow (by fun_prop) analyticAt_const (Or.inl hre)
    have h2 := (analyticAt_ordinaryHypergeometric (a := (α + β + 1) / 2) (b := (α + β + 2) / 2)
      (c := β + 1) hw2').comp hvA
    exact h1.mul h2
  have hFa : AnalyticOnNhd ℂ p.sum D := fun w hw =>
    hF.analyticAt_of_mem (mem_eball_one_of_norm_lt_one (by simpa using hw.1))
  -- agreement near `0`
  set δ := 1 / (32 * ((1 + ‖α + β + 1‖) ^ 2 * (1 + 1 / (β.re + 1)))) with hδ
  have hσ : 0 < β.re + 1 := by linarith
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hev : p.sum =ᶠ[𝓝 0] G := by
    filter_upwards [ball_mem_nhds (0 : ℂ) (lt_min hδ0 one_pos)] with w hw
    have hw' : ‖w‖ < min δ 1 := by simpa using hw
    exact (hFsum w (lt_of_lt_of_le hw' (min_le_right _ _))).unique
      (jacW_hasSum_small hα hβ hx (lt_of_lt_of_le hw' (min_le_left _ _)))
  have heq := hFa.eqOn_of_preconnected_of_eventuallyEq hGa
    (StarConvex.isPathConnected hDs hD0).isConnected.isPreconnected hD0 hev
  have hzD : z ∈ D := ⟨by simpa using hz, by simpa [hv] using hu⟩
  have := hFsum z hz
  rw [heq hzD] at this
  exact this

end DLMF.OrthogonalPolynomials
end
end
