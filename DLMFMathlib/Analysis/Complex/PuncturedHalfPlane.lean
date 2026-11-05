/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.Convex

/-!
# Connected punctured half-planes

A right half-plane with the interior point `1` removed is preconnected.
-/

@[expose] public section

open Set

namespace Complex

/-- `{Re s > c} \ {1}` is preconnected for `c < 1`. -/
theorem isPreconnected_re_gt_sdiff_one {c : ℝ} (hc : c < 1) :
    IsPreconnected ({s : ℂ | c < s.re} \ {1}) := by
  set Q1 : Set ℂ := {s | c < s.re ∧ 0 < s.im}
  set Q2 : Set ℂ := {s | c < s.re ∧ s.im < 0}
  set Q3 : Set ℂ := {s | c < s.re ∧ s.re < 1}
  set Q4 : Set ℂ := {s | 1 < s.re}
  have c1 : Convex ℝ Q1 := (convex_halfSpace_re_gt c).inter (convex_halfSpace_im_gt 0)
  have c2 : Convex ℝ Q2 := (convex_halfSpace_re_gt c).inter (convex_halfSpace_im_lt 0)
  have c3 : Convex ℝ Q3 := (convex_halfSpace_re_gt c).inter (convex_halfSpace_re_lt 1)
  have c4 : Convex ℝ Q4 := convex_halfSpace_re_gt 1
  set m : ℝ := (c + 1) / 2
  have hm1 : c < m := by simp only [m]; linarith
  have hm2 : m < 1 := by simp only [m]; linarith
  have h13 := c1.isPreconnected.union ((m : ℂ) + I) (by simp [Q1, hm1])
    (by simp [Q3, hm1, hm2]) c3.isPreconnected
  have h132 := h13.union ((m : ℂ) - I) (by simp [Q3, hm1, hm2]) (by simp [Q2, hm1])
    c2.isPreconnected
  have h := h132.union (2 + I)
    (show (2 + I) ∈ Q1 ∪ Q3 ∪ Q2 from Or.inl (Or.inl ⟨by simp; linarith, by simp⟩))
    (by norm_num [Q4])
    c4.isPreconnected
  convert h using 1
  ext s
  simp only [Set.mem_sdiff, mem_ofPred_eq, Set.mem_singleton_iff, mem_union, Q1, Q2, Q3, Q4]
  constructor
  · rintro ⟨h0, h1⟩
    rcases lt_trichotomy s.im 0 with hi | hi | hi
    · exact Or.inl (Or.inr ⟨h0, hi⟩)
    · rcases lt_trichotomy s.re 1 with hr | hr | hr
      · exact Or.inl (Or.inl (Or.inr ⟨h0, hr⟩))
      · exact absurd (Complex.ext (by simpa using hr) (by simpa using hi)) h1
      · exact Or.inr hr
    · exact Or.inl (Or.inl (Or.inl ⟨h0, hi⟩))
  · rintro (((⟨h0, h1⟩ | ⟨h0, h1⟩) | ⟨h0, h1⟩) | h0)
    · exact ⟨h0, fun h => by subst h; simp at h1⟩
    · exact ⟨h0, fun h => by subst h; simp at h1⟩
    · exact ⟨h0, fun h => by subst h; simp at h1⟩
    · exact ⟨by linarith, fun h => by subst h; simp at h0⟩

end Complex
