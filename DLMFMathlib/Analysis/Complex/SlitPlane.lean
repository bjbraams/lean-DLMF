/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import TauCeti.Analysis.Complex.SectorBounds

/-!
# Nonnegative translations in the slit plane

A nonnegative real translation preserves the principal slit plane. On a closed sector
away from the negative real axis, the norm of `z+t` uniformly bounds `‖z‖+t` from below.
The translation estimate uses TauCeti’s `Complex.mul_norm_add_le_norm_add_ofReal`.
-/

@[expose] public section

open Set
open scoped Real

namespace Complex

/-- Nonnegative real translation preserves the principal slit plane. -/
lemma add_ofReal_mem_slitPlane_of_nonneg {z : ℂ} (hz : z ∈ slitPlane) {t : ℝ} (ht : 0 ≤ t) :
    z + t ∈ slitPlane := by
  rcases mem_slitPlane_iff.mp hz with hr | hi
  · exact mem_slitPlane_iff.mpr (Or.inl (by simpa using add_pos_of_pos_of_nonneg hr ht))
  · exact mem_slitPlane_iff.mpr (Or.inr (by simpa using hi))

/-- A lower bound for translations when the real part stays away from `-‖z‖`. -/
lemma mul_norm_add_le_norm_add_ofReal_of_le_re {z : ℂ} {d t : ℝ} (hd : 0 < d) (hd1 : d ≤ 1)
    (hz : (-1 + d) * ‖z‖ ≤ z.re) (ht : 0 ≤ t) :
    d / 2 * (‖z‖ + t) ≤ ‖z + t‖ := by
  apply Complex.mul_norm_add_le_norm_add_ofReal (c := d / 2)
  · positivity
  · linarith
  · exact ht
  · convert hz using 1 <;> ring

/-- Uniform translation bound on a sector separated from the negative real axis. -/
lemma sector_norm_add_ofReal_bound {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < π) :
    ∃ c : ℝ, 0 < c ∧ ∀ z : ℂ, |arg z| ≤ π - δ → ∀ t : ℝ, 0 ≤ t →
      c * (‖z‖ + t) ≤ ‖z + t‖ := by
  let d : ℝ := (1 + Real.cos (π - δ)) / 2
  have hcos : -1 < Real.cos (π - δ) := by
    have h := Real.strictAntiOn_cos
      (show π - δ ∈ Icc (0 : ℝ) π from ⟨by linarith, by linarith⟩)
      (show π ∈ Icc (0 : ℝ) π from ⟨Real.pi_pos.le, le_rfl⟩) (by linarith : π - δ < π)
    simpa only [Real.cos_pi] using h
  have hd : 0 < d := by dsimp [d]; linarith
  have hd1 : d ≤ 1 := by dsimp [d]; linarith [Real.cos_le_one (π - δ)]
  refine ⟨d / 2, by positivity, fun z hz t ht => ?_⟩
  apply mul_norm_add_le_norm_add_ofReal_of_le_re hd hd1 ?_ ht
  have h := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg (arg z))
    (by linarith : π - δ ≤ π) hz
  rw [Real.cos_abs] at h
  have hnorm := mul_le_mul_of_nonneg_left h (norm_nonneg z)
  rw [norm_mul_cos_arg] at hnorm
  have hbase := mul_nonneg (norm_nonneg z) (show 0 ≤ 1 + Real.cos (π - δ) by linarith)
  dsimp only [d]
  nlinarith

end Complex
