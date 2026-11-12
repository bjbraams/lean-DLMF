/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.ContinuedFraction.Convergence
public import Mathlib.Analysis.Complex.Basic

/-!
# Value regions of Jacobi continued fractions

For real sequences `c_k` and positive `d_k`, the Jacobi fraction with partial numerators
`-c_k²` and denominators `d_k z` has no poles in either open half-plane. Its convergents
are bounded by `‖a₀‖/(d₀ |Im z|)`. Bounds outside the real interval follow from diagonal
dominance when `d_k ≥ c_k + c_{k+1}`.
-/

@[expose] public noncomputable section

open Filter Finset
open scoped Topology

namespace GenContFract

/-- Negating every partial denominator multiplies continuants by alternating signs. -/
theorem ofFun_continuants_neg_denominators (a b : ℕ → ℂ) (n : ℕ) :
    (ofFun 0 a (fun k => -b k)).dens n = (-1 : ℂ) ^ n * (ofFun 0 a b).dens n ∧
      (ofFun 0 a (fun k => -b k)).nums n = (-1 : ℂ) ^ (n + 1) * (ofFun 0 a b).nums n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    rcases n with _ | _ | n
    · simp only [ofFun_dens_zero, ofFun_nums_zero, pow_zero, one_mul, mul_zero]; trivial
    · simp [ofFun_dens_one, ofFun_nums_one]
    · obtain ⟨hd1, hn1⟩ := ih (n + 1) (by omega)
      obtain ⟨hd0, hn0⟩ := ih n (by omega)
      constructor
      · rw [ofFun_dens_add_two, hd1, hd0, ofFun_dens_add_two]
        simp only [pow_add, pow_one]
        ring
      · rw [ofFun_nums_add_two, hn1, hn0, ofFun_nums_add_two]
        simp only [pow_add, pow_one]
        ring

/-- Negating every partial denominator negates the convergent of a fraction with zero head. -/
theorem ofFun_convs_neg_denominators (a b : ℕ → ℂ) (n : ℕ) :
    (ofFun 0 a (fun k => -b k)).convs n = -(ofFun 0 a b).convs n := by
  obtain ⟨hd, hn⟩ := ofFun_continuants_neg_denominators a b n
  change _ / _ = -(_ / _)
  rw [hd, hn, pow_succ]
  have hpn : (-1 : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [show (-1 : ℂ) ^ n * -1 * (ofFun 0 a b).nums n =
    -((-1 : ℂ) ^ n * (ofFun 0 a b).nums n) by ring, neg_div,
    mul_div_mul_left _ _ hpn]

/-- A Jacobi fraction has no poles in the upper half-plane, with the Cauchy-transform bound. -/
theorem ofFun_jacobi_im_bound {a b : ℕ → ℂ} {c d : ℕ → ℝ} {z : ℂ}
    (hz : 0 < z.im) (hd : ∀ k, 0 < d k)
    (ha : ∀ k, 1 ≤ k → a k = -(c k : ℂ) ^ 2)
    (hb : ∀ k, b k = (d k : ℂ) * z) (n : ℕ) :
    (ofFun 0 a b).dens n ≠ 0 ∧
      ‖(ofFun 0 a b).convs n‖ ≤ ‖a 0‖ / (d 0 * z.im) := by
  rcases n with _ | N
  · simp only [ofFun_dens_zero, ne_eq, one_ne_zero, not_false_eq_true,
      GenContFract.convs, ofFun_nums_zero, zero_div, norm_zero, true_and]
    exact div_nonneg (norm_nonneg _) (mul_pos (hd 0) hz).le
  let w := backwardSolution a b N
  have hrec : ∀ k ≤ N, w k = b k * w (k + 1) + a (k + 1) * w (k + 2) :=
    backwardSolution_rec N
  have key : ∀ j ≤ N, w (N - j + 1) ≠ 0 ∧
      d (N - j) * z.im ≤ (w (N - j) / w (N - j + 1)).im := by
    intro j
    induction j with
    | zero =>
      intro _
      have he1 : w (N + 1) = 1 := backwardSolution_succ N
      have he0 : w N = (d N : ℂ) * z := by
        rw [hrec N le_rfl, he1, show w (N + 2) = 0 from backwardSolution_succ_succ N, hb]
        ring
      simp only [Nat.sub_zero, he1, he0, div_one, Complex.im_ofReal_mul]
      exact ⟨one_ne_zero, le_rfl⟩
    | succ j ih =>
      intro hj
      obtain ⟨h1, h2⟩ := ih (by omega)
      let k := N - (j + 1)
      have hk1 : N - j = k + 1 := by omega
      rw [hk1] at h1 h2
      have hρ : 0 < (w (k + 1) / w (k + 1 + 1)).im :=
        (mul_pos (hd _) hz).trans_le h2
      have hw1 : w (k + 1) ≠ 0 := by
        intro h0
        rw [h0, zero_div, Complex.zero_im] at hρ
        exact lt_irrefl _ hρ
      refine ⟨hw1, ?_⟩
      have he := hrec k (by omega)
      rw [hb, ha (k + 1) (by omega)] at he
      have heq : w k / w (k + 1) = (d k : ℂ) * z -
          (c (k + 1) : ℂ) ^ 2 * (w (k + 1) / w (k + 1 + 1))⁻¹ := by
        rw [he, inv_div]
        field_simp
        ring
      have hneg : ((c (k + 1) : ℂ) ^ 2 *
          (w (k + 1) / w (k + 1 + 1))⁻¹).im ≤ 0 := by
        rw [← Complex.ofReal_pow, Complex.im_ofReal_mul, Complex.inv_im]
        exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _)
          (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hρ.le) (Complex.normSq_nonneg _))
      change d k * z.im ≤ (w k / w (k + 1)).im
      rw [heq, Complex.sub_im, Complex.im_ofReal_mul]
      linarith
  obtain ⟨h1, h2⟩ := key N le_rfl
  simp only [Nat.sub_self, zero_add] at h1 h2
  have hρ : 0 < (w 0 / w 1).im := (mul_pos (hd 0) hz).trans_le h2
  have hw0 : w 0 ≠ 0 := by
    intro h0
    rw [h0, zero_div, Complex.zero_im] at hρ
    exact lt_irrefl _ hρ
  obtain ⟨hden, hnum⟩ := ofFun_continuants_of_backward (h := 0) N hrec
    (backwardSolution_succ N) (backwardSolution_succ_succ N)
  refine ⟨by rw [hden]; exact hw0, ?_⟩
  change ‖(ofFun 0 a b).nums (N + 1) / (ofFun 0 a b).dens (N + 1)‖ ≤ _
  rw [hden, hnum, zero_mul, add_zero]
  have heq : a 0 * w 1 / w 0 = a 0 / (w 0 / w 1) := by field_simp
  rw [heq, norm_div]
  exact div_le_div_of_nonneg_left (norm_nonneg _) (mul_pos (hd 0) hz)
    (h2.trans (Complex.im_le_norm _))

/-- Diagonal dominance gives a pole-free right half-plane and a uniform Jacobi-fraction bound. -/
theorem ofFun_jacobi_re_bound {a b : ℕ → ℂ} {c d : ℕ → ℝ} {z : ℂ}
    (hz : 1 < z.re) (hc : ∀ k, 0 ≤ c k) (hd : ∀ k, 0 < d k)
    (hdom : ∀ k, c k + c (k + 1) ≤ d k)
    (ha : ∀ k, 1 ≤ k → a k = -(c k : ℂ) ^ 2)
    (hb : ∀ k, b k = (d k : ℂ) * z) (n : ℕ) :
    (ofFun 0 a b).dens n ≠ 0 ∧
      ‖(ofFun 0 a b).convs n‖ ≤ ‖a 0‖ / (d 0 * (z.re - 1)) := by
  rcases n with _ | N
  · simp only [ofFun_dens_zero, ne_eq, one_ne_zero, not_false_eq_true,
      GenContFract.convs, ofFun_nums_zero, zero_div, norm_zero, true_and]
    exact div_nonneg (norm_nonneg _) (mul_pos (hd 0) (sub_pos.mpr hz)).le
  let w := backwardSolution a b N
  have hrec : ∀ k ≤ N, w k = b k * w (k + 1) + a (k + 1) * w (k + 2) :=
    backwardSolution_rec N
  have key : ∀ j ≤ N, w (N - j + 1) ≠ 0 ∧
      c (N - j) + d (N - j) * (z.re - 1) ≤
        (w (N - j) / w (N - j + 1)).re := by
    intro j
    induction j with
    | zero =>
      intro _
      have he1 : w (N + 1) = 1 := backwardSolution_succ N
      have he0 : w N = (d N : ℂ) * z := by
        rw [hrec N le_rfl, he1, show w (N + 2) = 0 from backwardSolution_succ_succ N, hb]
        ring
      simp only [Nat.sub_zero, he1, he0, div_one, Complex.re_ofReal_mul]
      refine ⟨one_ne_zero, ?_⟩
      linarith [hdom N, hc (N + 1)]
    | succ j ih =>
      intro hj
      obtain ⟨h1, h2⟩ := ih (by omega)
      let k := N - (j + 1)
      have hk1 : N - j = k + 1 := by omega
      rw [hk1] at h1 h2
      have hρ : 0 < (w (k + 1) / w (k + 1 + 1)).re := by
        have := mul_pos (hd (k + 1)) (sub_pos.mpr hz)
        linarith [hc (k + 1)]
      have hw1 : w (k + 1) ≠ 0 := by
        intro h0
        rw [h0, zero_div, Complex.zero_re] at hρ
        exact lt_irrefl _ hρ
      refine ⟨hw1, ?_⟩
      have he := hrec k (by omega)
      rw [hb, ha (k + 1) (by omega)] at he
      have heq : w k / w (k + 1) = (d k : ℂ) * z -
          (c (k + 1) : ℂ) ^ 2 * (w (k + 1) / w (k + 1 + 1))⁻¹ := by
        rw [he, inv_div]
        field_simp
        ring
      have hnorm : c (k + 1) ≤ ‖w (k + 1) / w (k + 1 + 1)‖ := by
        have := mul_pos (hd (k + 1)) (sub_pos.mpr hz)
        exact (by linarith : c (k + 1) ≤ (w (k + 1) / w (k + 1 + 1)).re).trans
          (Complex.re_le_norm _)
      have hnorm0 : 0 < ‖w (k + 1) / w (k + 1 + 1)‖ :=
        hρ.trans_le (Complex.re_le_norm _)
      have hbound : ‖(c (k + 1) : ℂ) ^ 2 *
          (w (k + 1) / w (k + 1 + 1))⁻¹‖ ≤ c (k + 1) := by
        rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hc _),
          norm_inv, ← div_eq_mul_inv, div_le_iff₀ hnorm0]
        nlinarith [hc (k + 1)]
      change c k + d k * (z.re - 1) ≤ (w k / w (k + 1)).re
      rw [heq, Complex.sub_re, Complex.re_ofReal_mul]
      have := (Complex.re_le_norm _).trans hbound
      linarith [hdom k]
  obtain ⟨h1, h2⟩ := key N le_rfl
  simp only [Nat.sub_self, zero_add] at h1 h2
  have hρ : 0 < (w 0 / w 1).re := by
    have := mul_pos (hd 0) (sub_pos.mpr hz)
    linarith [hc 0]
  have hw0 : w 0 ≠ 0 := by
    intro h0
    rw [h0, zero_div, Complex.zero_re] at hρ
    exact lt_irrefl _ hρ
  obtain ⟨hden, hnum⟩ := ofFun_continuants_of_backward (h := 0) N hrec
    (backwardSolution_succ N) (backwardSolution_succ_succ N)
  refine ⟨by rw [hden]; exact hw0, ?_⟩
  change ‖(ofFun 0 a b).nums (N + 1) / (ofFun 0 a b).dens (N + 1)‖ ≤ _
  rw [hden, hnum, zero_mul, add_zero]
  have heq : a 0 * w 1 / w 0 = a 0 / (w 0 / w 1) := by field_simp
  rw [heq, norm_div]
  apply div_le_div_of_nonneg_left (norm_nonneg _) (mul_pos (hd 0) (sub_pos.mpr hz))
  exact (by linarith [hc 0] : d 0 * (z.re - 1) ≤ (w 0 / w 1).re).trans
    (Complex.re_le_norm _)

/-- Jacobi fractions with diagonally dominant weights are locally bounded off the unit segment. -/
theorem ofFun_jacobi_bound {a b : ℕ → ℂ} {c d : ℕ → ℝ} {z : ℂ}
    (hz : 0 < max (|z.re| - 1) |z.im|) (hc : ∀ k, 0 ≤ c k) (hd : ∀ k, 0 < d k)
    (hdom : ∀ k, c k + c (k + 1) ≤ d k)
    (ha : ∀ k, 1 ≤ k → a k = -(c k : ℂ) ^ 2)
    (hb : ∀ k, b k = (d k : ℂ) * z) (n : ℕ) :
    (ofFun 0 a b).dens n ≠ 0 ∧
      ‖(ofFun 0 a b).convs n‖ ≤ ‖a 0‖ / (d 0 * max (|z.re| - 1) |z.im|) := by
  have hbneg (k : ℕ) : -b k = (d k : ℂ) * (-z) := by rw [hb]; ring
  have htransfer {B : ℝ}
      (h : (ofFun 0 a (fun k => -b k)).dens n ≠ 0 ∧
        ‖(ofFun 0 a (fun k => -b k)).convs n‖ ≤ B) :
      (ofFun 0 a b).dens n ≠ 0 ∧ ‖(ofFun 0 a b).convs n‖ ≤ B := by
    rw [(ofFun_continuants_neg_denominators a b n).1] at h
    refine ⟨(mul_ne_zero_iff.mp h.1).2, ?_⟩
    simpa only [ofFun_convs_neg_denominators, norm_neg] using h.2
  rcases le_total (|z.re| - 1) |z.im| with hm | hm
  · rw [max_eq_right hm] at hz ⊢
    have him : z.im ≠ 0 := abs_pos.mp hz
    rcases lt_or_gt_of_ne him with him | him
    · have h := ofFun_jacobi_im_bound (z := -z) (by simpa using neg_pos.mpr him)
        hd ha hbneg n
      apply htransfer
      simpa only [Complex.neg_im, abs_of_neg him] using h
    · simpa only [abs_of_pos him] using ofFun_jacobi_im_bound him hd ha hb n
  · rw [max_eq_left hm] at hz ⊢
    rcases le_or_gt z.re 0 with hre | hre
    · have hzr : 1 < (-z).re := by rw [Complex.neg_re]; rw [abs_of_nonpos hre] at hz; linarith
      have h := ofFun_jacobi_re_bound hzr hc hd hdom ha hbneg n
      apply htransfer
      simpa only [Complex.neg_re, abs_of_nonpos hre] using h
    · have hzr : 1 < z.re := by rw [abs_of_pos hre] at hz; linarith
      simpa only [abs_of_pos hre] using ofFun_jacobi_re_bound hzr hc hd hdom ha hb n

end GenContFract
