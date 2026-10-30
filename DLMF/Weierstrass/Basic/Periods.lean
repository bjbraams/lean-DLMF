/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic

/-!
# Half-periods, period pairs, lattice orientation and scaling
-/

@[expose] public noncomputable section

open Complex PeriodPair
open scoped Real

namespace DLMF.Weierstrass

/-- DLMF's lattice data (§23.2(i)): nonzero half-periods `ω₁, ω₃` with `ℑ(ω₃/ω₁) > 0`. The
lattice `𝕃` consists of the points `2mω₁ + 2nω₃`, `m, n ∈ ℤ`. -/
structure HalfPeriods where
  /-- The half-period `ω₁`. -/
  ω₁ : ℂ
  /-- The half-period `ω₃`. -/
  ω₃ : ℂ
  /-- The first half-period is nonzero. -/
  ω₁_ne_zero : ω₁ ≠ 0
  /-- The ratio of the half-periods has positive imaginary part, fixing the lattice orientation. -/
  im_div_pos : 0 < (ω₃ / ω₁).im

namespace HalfPeriods

variable (H : HalfPeriods)

/-- The third half-period `ω₂ = -ω₁ - ω₃` (DLMF 23.2.1). -/
@[dlmf 23.2.E1]
def ω₂ : ℂ := -H.ω₁ - H.ω₃

/-- DLMF 23.2.1: `ω₁ + ω₂ + ω₃ = 0`. -/
@[dlmf 23.2.E1]
theorem ω₁_add_ω₂_add_ω₃ : H.ω₁ + H.ω₂ + H.ω₃ = 0 := by
  simp only [ω₂]; ring

/-- The lattice parameter `τ = ω₃/ω₁` (DLMF 23.6.1), with `ℑτ > 0`. -/
@[dlmf 23.6.E1]
def tau : ℂ := H.ω₃ / H.ω₁

/-- The nome `q = e^{iπτ}` (DLMF 23.6.1, 23.8.i). -/
@[dlmf 23.6.E1]
def nome : ℂ := cexp (π * I * H.tau)

/-- Estimate under the stated parameter and domain assumptions: `0 < H.tau.im`. -/
theorem tau_im_pos : 0 < H.tau.im := H.im_div_pos

/-- Nonvanishing under the stated hypotheses: `H.ω₃ ≠ 0`. -/
theorem ω₃_ne_zero : H.ω₃ ≠ 0 := by
  intro h
  have := H.im_div_pos
  simp [h] at this

/-- `2ω₁` and `2ω₃` are `ℝ`-linearly independent. -/
theorem linearIndependent_two_mul :
    LinearIndependent ℝ ![2 * H.ω₁, 2 * H.ω₃] := by
  refine LinearIndependent.pair_iff.mpr fun s t hst => ?_
  have h1 := H.ω₁_ne_zero
  have key : (s : ℂ) + t * (H.ω₃ / H.ω₁) = 0 := by
    have : (2 * H.ω₁) * ((s : ℂ) + t * (H.ω₃ / H.ω₁)) = 0 := by
      rw [← hst]; simp only [Complex.real_smul]; field_simp
    simpa [h1] using this
  have hi := congrArg Complex.im key
  simp only [add_im, ofReal_im, mul_im, ofReal_re, zero_mul, add_zero, zero_add,
    Complex.zero_im] at hi
  have ht : t = 0 := by
    rcases mul_eq_zero.mp hi with h | h
    · exact h
    · exact absurd h (ne_of_gt H.im_div_pos)
  subst ht
  simpa using key

/-- Half-periods `ω₁ = ω`, `ω₃ = ωτ` for `τ` in the upper half-plane. With `ω = 1/2` the
lattice generators are `1, τ` (as in DLMF 23.19.3). -/
def ofTau (ω : ℂ) (hω : ω ≠ 0) (τ : UpperHalfPlane) : HalfPeriods :=
  ⟨ω, ω * τ, hω, by rw [mul_div_cancel_left₀ _ hω]; exact τ.im_pos⟩

/-- Identity under the stated parameter and domain assumptions: `(ofTau ω hω τ).ω₁ = ω`. -/
@[simp] theorem ofTau_ω₁ (ω : ℂ) (hω : ω ≠ 0) (τ : UpperHalfPlane) : (ofTau ω hω τ).ω₁ = ω := rfl
/-- Identity under the stated parameter and domain assumptions: `(ofTau ω hω τ).ω₃ = ω * τ`. -/
@[simp] theorem ofTau_ω₃ (ω : ℂ) (hω : ω ≠ 0) (τ : UpperHalfPlane) :
    (ofTau ω hω τ).ω₃ = ω * τ := rfl

/-- The bridge to Mathlib: the `PeriodPair` with full periods `2ω₁, 2ω₃`. -/
def periodPair : PeriodPair := ⟨2 * H.ω₁, 2 * H.ω₃, H.linearIndependent_two_mul⟩

/-- Identity under the stated parameter and domain assumptions: `H.periodPair.ω₁ = 2 * H.ω₁`. -/
@[simp] theorem periodPair_ω₁ : H.periodPair.ω₁ = 2 * H.ω₁ := rfl
/-- Identity under the stated parameter and domain assumptions: `H.periodPair.ω₂ = 2 * H.ω₃`. -/
@[simp] theorem periodPair_ω₂ : H.periodPair.ω₂ = 2 * H.ω₃ := rfl

/-- The lattice `𝕃` with generators `2ω₁, 2ω₃`. -/
abbrev lattice : Submodule ℤ ℂ := H.periodPair.lattice

end HalfPeriods

/-- Nonvanishing under the stated hypotheses: `L.ω₁ ≠ 0`. -/
lemma wp23_ω₁_ne_zero (L : PeriodPair) : L.ω₁ ≠ 0 := by
  simpa using L.indep.ne_zero 0

/-- Nonvanishing under the stated hypotheses: `(L.ω₂ / L.ω₁).im ≠ 0`. -/
lemma wp23_im_div_ne_zero (L : PeriodPair) : (L.ω₂ / L.ω₁).im ≠ 0 := by
  intro him
  have h1 := wp23_ω₁_ne_zero L
  have hq : L.ω₂ / L.ω₁ = ((L.ω₂ / L.ω₁).re : ℂ) := Complex.ext (by simp) (by simp [him])
  have h2 : L.ω₂ = ((L.ω₂ / L.ω₁).re : ℂ) * L.ω₁ := by
    rw [← hq]; field_simp
  have := LinearIndependent.pair_iff.mp L.indep ((L.ω₂ / L.ω₁).re) (-1)
    (by rw [Complex.real_smul, Complex.real_smul, ← h2]; simp)
  norm_num at this

/-- DLMF half-periods for an arbitrary Mathlib period pair: `ω₁ = L.ω₁/2` and
`ω₃ = ±L.ω₂/2`, the sign chosen so that `ℑ(ω₃/ω₁) > 0`. -/
def halfPeriodsOf (L : PeriodPair) : HalfPeriods :=
  if h : 0 < (L.ω₂ / L.ω₁).im then
    ⟨L.ω₁ / 2, L.ω₂ / 2, by simpa using wp23_ω₁_ne_zero L, by
      rwa [div_div_div_cancel_right₀ two_ne_zero]⟩
  else
    ⟨L.ω₁ / 2, -L.ω₂ / 2, by simpa using wp23_ω₁_ne_zero L, by
      rw [div_div_div_cancel_right₀ two_ne_zero, neg_div, neg_im]
      have := wp23_im_div_ne_zero L
      exact neg_pos.mpr (lt_of_le_of_ne (not_lt.mp h) this)⟩

/-- The period pair `c𝕃` with periods `cω₁, cω₂` (`c ≠ 0`). -/
def scalePeriodPair (c : ℂ) (hc : c ≠ 0) (L : PeriodPair) : PeriodPair :=
  ⟨c * L.ω₁, c * L.ω₂, by
    refine LinearIndependent.pair_iff.mpr fun s t h => ?_
    refine LinearIndependent.pair_iff.mp L.indep s t ?_
    have : c * (s • L.ω₁ + t • L.ω₂) = 0 := by
      rw [← h]; simp only [Complex.real_smul]; ring
    simpa [hc] using this⟩

/-- Formula under the stated hypotheses: `z ∈ (scalePeriodPair c hc L).lattice ↔ z / c ∈
L.lattice`. -/
theorem wp23_mem_scale_iff (c : ℂ) (hc : c ≠ 0) (L : PeriodPair) {z : ℂ} :
    z ∈ (scalePeriodPair c hc L).lattice ↔ z / c ∈ L.lattice := by
  simp only [PeriodPair.mem_lattice, scalePeriodPair]
  constructor
  · rintro ⟨m, n, rfl⟩; exact ⟨m, n, by field_simp⟩
  · rintro ⟨m, n, h⟩; exact ⟨m, n, by rw [← mul_div_cancel₀ z hc, ← h]; ring⟩

/-- Multiplication by `c` as a bijection `𝕃 ≃ c𝕃`. -/
def wp23_scaleEquiv (c : ℂ) (hc : c ≠ 0) (L : PeriodPair) :
    L.lattice ≃ (scalePeriodPair c hc L).lattice where
  toFun l := ⟨c * l, (wp23_mem_scale_iff c hc L).mpr (by simp [hc])⟩
  invFun l := ⟨l / c, (wp23_mem_scale_iff c hc L).mp l.2⟩
  left_inv l := by ext; simp [hc]
  right_inv l := by ext; simp [mul_div_cancel₀ _ hc]

/-- The square lattice with half-periods `1, i`, used to see that `PeriodPair` is nonempty. -/
def wp23_squareHalfPeriods : HalfPeriods := ⟨1, I, one_ne_zero, by simp⟩

/-- The square lattice supplies a complex period pair. -/
instance : Nonempty PeriodPair := ⟨wp23_squareHalfPeriods.periodPair⟩

end DLMF.Weierstrass
