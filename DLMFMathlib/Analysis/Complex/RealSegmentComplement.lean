/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.Convex

/-!
# Complements of closed real segments in the complex plane

The complement of a real segment is an open connected complex domain. It is the union of
the upper and lower half-planes and the half-planes to the left and right of the segment.
-/

@[expose] public section

open Set

namespace Complex

/-- The complement of the closed real segment `[a,b]`; for `b<a` this is the whole plane. -/
def realSegmentComplement (a b : ℝ) : Set ℂ := {z | z.im ≠ 0 ∨ z.re < a ∨ b < z.re}

/-- A real-segment complement is the union of four open half-planes. -/
theorem realSegmentComplement_eq_union (a b : ℝ) :
    realSegmentComplement a b =
      (({z : ℂ | 0 < z.im} ∪ {z : ℂ | b < z.re}) ∪ {z : ℂ | z.im < 0}) ∪
        {z : ℂ | z.re < a} := by
  ext z
  simp only [realSegmentComplement, mem_ofPred_eq, mem_union]
  constructor
  · rintro (h | h | h)
    · rcases lt_or_gt_of_ne h with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inr h
    · exact Or.inl (Or.inl (Or.inr h))
  · rintro (((h | h) | h) | h)
    · exact Or.inl h.ne'
    · exact Or.inr (Or.inr h)
    · exact Or.inl h.ne
    · exact Or.inr (Or.inl h)

/-- Complements of real segments are open. -/
theorem isOpen_realSegmentComplement (a b : ℝ) : IsOpen (realSegmentComplement a b) := by
  rw [realSegmentComplement_eq_union]
  exact (((isOpen_lt continuous_const continuous_im).union
    (isOpen_lt continuous_const continuous_re)).union
    (isOpen_lt continuous_im continuous_const)).union
    (isOpen_lt continuous_re continuous_const)

/-- Complements of real segments are preconnected. -/
theorem isPreconnected_realSegmentComplement (a b : ℝ) :
    IsPreconnected (realSegmentComplement a b) := by
  rw [realSegmentComplement_eq_union]
  have h1 : IsPreconnected ({z : ℂ | 0 < z.im} ∪ {z : ℂ | b < z.re}) := by
    apply IsPreconnected.union' ?_ (convex_halfSpace_im_gt 0).isPreconnected
      (convex_halfSpace_re_gt b).isPreconnected
    exact ⟨((b + 1 : ℝ) : ℂ) + I, by simp, by simp⟩
  have h2 : IsPreconnected
      (({z : ℂ | 0 < z.im} ∪ {z : ℂ | b < z.re}) ∪ {z : ℂ | z.im < 0}) := by
    apply IsPreconnected.union' ?_ h1 (convex_halfSpace_im_lt 0).isPreconnected
    exact ⟨((b + 1 : ℝ) : ℂ) - I, Or.inr (by simp), by simp⟩
  apply IsPreconnected.union' ?_ h2 (convex_halfSpace_re_lt a).isPreconnected
  exact ⟨((a - 1 : ℝ) : ℂ) + I, Or.inl (Or.inl (by simp)), by simp⟩

/-- The fractional linear map `(z+1)/(z-1)` maps the complement of `[-1,1]` into the slit plane. -/
theorem add_one_div_sub_one_mem_slitPlane {z : ℂ}
    (hz : z ∈ realSegmentComplement (-1) 1) : (z + 1) / (z - 1) ∈ slitPlane := by
  have hz1 : z ≠ 1 := by
    intro he
    subst z
    norm_num [realSegmentComplement] at hz
  have hden : 0 < normSq (z - 1) := normSq_pos.mpr (sub_ne_zero.mpr hz1)
  rcases hz with him | hleft | hright
  · apply mem_slitPlane_iff.mpr
    right
    have he : ((z + 1) / (z - 1)).im = -2 * z.im / normSq (z - 1) := by
      rw [div_im]
      simp only [add_im, sub_im, add_re, sub_re, one_im, one_re, add_zero, sub_zero]
      ring
    rw [he]
    exact div_ne_zero (mul_ne_zero (by norm_num) him) hden.ne'
  · apply mem_slitPlane_iff.mpr
    left
    rw [div_re]
    simp only [add_im, sub_im, add_re, sub_re, one_im, one_re, add_zero, sub_zero]
    rw [← add_div]
    apply div_pos ?_ hden
    nlinarith [sq_nonneg z.im]
  · apply mem_slitPlane_iff.mpr
    left
    rw [div_re]
    simp only [add_im, sub_im, add_re, sub_re, one_im, one_re, add_zero, sub_zero]
    rw [← add_div]
    apply div_pos ?_ hden
    nlinarith [sq_nonneg z.im]

/-- The gap from the real unit segment is positive on its complement. -/
theorem max_abs_re_sub_one_abs_im_pos {z : ℂ}
    (hz : z ∈ realSegmentComplement (-1) 1) : 0 < max (|z.re| - 1) |z.im| := by
  rcases hz with him | hleft | hright
  · exact (abs_pos.mpr him).trans_le (le_max_right _ _)
  · have he : 0 < |z.re| - 1 := by linarith [neg_le_abs z.re]
    exact he.trans_le (le_max_left _ _)
  · have he : 0 < |z.re| - 1 := by linarith [le_abs_self z.re]
    exact he.trans_le (le_max_left _ _)

/-- Inversion takes the plane slit along the two exterior real rays into the complement
of the unit segment. -/
theorem inv_mem_realSegmentComplement {z : ℂ} (hz0 : z ≠ 0)
    (hz : z.im ≠ 0 ∨ |z.re| < 1) : z⁻¹ ∈ realSegmentComplement (-1) 1 := by
  by_cases him : z.im = 0
  · have he : z = (z.re : ℂ) := by apply Complex.ext <;> simp [him]
    have hr0 : z.re ≠ 0 := by
      intro hr
      exact hz0 (by rw [he, hr]; simp)
    have hr : |z.re| < 1 := hz.resolve_left (by simp [him])
    have habs : 1 < |(z⁻¹).re| := by
      rw [he, ← ofReal_inv, ofReal_re, abs_inv]
      exact (one_lt_inv₀ (abs_pos.mpr hr0)).mpr hr
    right
    by_contra! h
    exact (not_le_of_gt habs) (abs_le.mpr ⟨h.1, h.2⟩)
  · left
    rw [inv_im]
    exact div_ne_zero (neg_ne_zero.mpr him) (normSq_pos.mpr hz0).ne'

end Complex
