/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Symmetric equality criterion for Cauchy–Schwarz

Mathlib's `norm_inner_eq_norm_tfae` gives the equality criterion in terms of one
vector being zero or the other being a scalar multiple. The symmetric formulation
below includes both degenerate cases without selecting a distinguished vector.
-/

@[expose] public noncomputable section

open MeasureTheory

/-- Equality in the squared real Cauchy–Schwarz inequality holds precisely when a
nontrivial linear combination of the two vectors vanishes. -/
theorem real_inner_sq_eq_iff_smul_eq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (x y : E) :
    inner ℝ x y ^ 2 = inner ℝ x x * inner ℝ y y ↔
      ∃ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) ∧ a • x = b • y := by
  have hnorm : inner ℝ x y ^ 2 = inner ℝ x x * inner ℝ y y ↔
      ‖inner ℝ x y‖ = ‖x‖ * ‖y‖ := by
    rw [← sq_eq_sq₀ (norm_nonneg (inner ℝ x y))
      (mul_nonneg (norm_nonneg x) (norm_nonneg y))]
    simp [Real.norm_eq_abs, sq_abs, mul_pow]
  have hlin : ‖inner ℝ x y‖ = ‖x‖ * ‖y‖ ↔ x = 0 ∨ ∃ r : ℝ, y = r • x :=
    (norm_inner_eq_norm_tfae ℝ x y).out 1 3
  rw [hnorm, hlin]
  constructor
  · rintro (hx | ⟨r, hr⟩)
    · exact ⟨1, 0, Or.inl one_ne_zero, by simp [hx]⟩
    · exact ⟨r, 1, Or.inr one_ne_zero, by simp [hr]⟩
  · rintro ⟨a, b, hab, h⟩
    by_cases hb : b = 0
    · have ha : a ≠ 0 := hab.resolve_right (not_ne_iff.mpr hb)
      left
      have hz : a • x = 0 := by simpa only [hb, zero_smul] using h
      exact (smul_eq_zero.mp hz).resolve_left ha
    · right
      refine ⟨a / b, ?_⟩
      rw [div_eq_inv_mul, mul_smul, eq_comm, inv_smul_eq_iff₀ hb]
      exact h

/-- The real inner product of two `L²` representatives is the integral of their
pointwise product. -/
theorem MeasureTheory.MemLp.real_inner_toLp {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x * g x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
  simp [hfx, hgx, mul_comm]
