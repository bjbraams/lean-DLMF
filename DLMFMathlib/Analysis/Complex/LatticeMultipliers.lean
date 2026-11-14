/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import TauCeti.Algebra.Ring.Subgroup
import Mathlib.Tactic

/-!
# Multipliers of a complex lattice

The complex numbers `α` with `αΛ ⊆ Λ` form a ring. For a lattice of rank two every
multiplier satisfies a monic quadratic equation over the integers; the real multipliers
are exactly the integers. A nonreal multiplier has negative quadratic discriminant.

The multiplier ring is TauCeti's `AddSubgroup.multiplierRing`, used directly on the
underlying additive group of the lattice. These are the elementary complex multiplication
results in Lang, *Elliptic Functions*,
Chapter 1, §5, pp. 19–20, and Koecher–Krieg, *Elliptic Functions and Modular Forms*,
Chapter I, §7. The lattice and basis APIs are Mathlib's `PeriodPair`.
-/

@[expose] public noncomputable section

namespace PeriodPair

/-- It suffices to check a multiplier on the two lattice generators. -/
theorem mem_multiplierRing_iff_periods (L : PeriodPair) (α : ℂ) :
    α ∈ L.lattice.toAddSubgroup.multiplierRing ↔
      α * L.ω₁ ∈ L.lattice ∧ α * L.ω₂ ∈ L.lattice := by
  simp only [AddSubgroup.mem_multiplierRing, Submodule.mem_toAddSubgroup]
  constructor
  · intro h
    exact ⟨h _ L.ω₁_mem_lattice, h _ L.ω₂_mem_lattice⟩
  · rintro ⟨h₁, h₂⟩ z hz
    obtain ⟨m, n, rfl⟩ := mem_lattice.mp hz
    have h := add_mem (L.lattice.smul_mem m h₁) (L.lattice.smul_mem n h₂)
    simpa only [zsmul_eq_mul, mul_add, mul_left_comm] using h

/-- Integer matrices describe the action of every multiplier on a lattice basis. -/
theorem exists_integer_matrix_of_mem_multiplierRing (L : PeriodPair) {α : ℂ}
    (hα : α ∈ L.lattice.toAddSubgroup.multiplierRing) :
    ∃ a b c d : ℤ, α * L.ω₁ = a * L.ω₁ + b * L.ω₂ ∧
      α * L.ω₂ = c * L.ω₁ + d * L.ω₂ := by
  obtain ⟨h₁, h₂⟩ := (L.mem_multiplierRing_iff_periods α).mp hα
  obtain ⟨a, b, hab⟩ := mem_lattice.mp h₁
  obtain ⟨c, d, hcd⟩ := mem_lattice.mp h₂
  exact ⟨a, b, c, d, hab.symm, hcd.symm⟩

/-- A lattice multiplier satisfies the characteristic equation of its integer matrix. -/
theorem exists_quadratic_of_mem_multiplierRing (L : PeriodPair) {α : ℂ}
    (hα : α ∈ L.lattice.toAddSubgroup.multiplierRing) :
    ∃ t n : ℤ, α ^ 2 - t * α + n = 0 := by
  obtain ⟨a, b, c, d, h₁, h₂⟩ := L.exists_integer_matrix_of_mem_multiplierRing hα
  refine ⟨a + d, a * d - b * c, ?_⟩
  have hω : L.ω₁ ≠ 0 := L.indep.ne_zero 0
  apply (mul_eq_zero.mp (show
    (α ^ 2 - ((a + d : ℤ) : ℂ) * α + ((a * d - b * c : ℤ) : ℂ)) * L.ω₁ = 0
      from ?_)).resolve_right hω
  push_cast
  linear_combination (α - d) * h₁ + b * h₂

/-- Every lattice multiplier is an algebraic integer. -/
theorem isIntegral_of_mem_multiplierRing (L : PeriodPair) {α : ℂ}
    (hα : α ∈ L.lattice.toAddSubgroup.multiplierRing) : IsIntegral ℤ α := by
  obtain ⟨t, n, h⟩ := L.exists_quadratic_of_mem_multiplierRing hα
  refine ⟨Polynomial.X ^ 2 - (Polynomial.C t * Polynomial.X - Polynomial.C n), ?_, ?_⟩
  · apply Polynomial.monic_X_pow_sub
    compute_degree!
  · simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_mul, Polynomial.eval₂_C]
    linear_combination h

/-- A real multiplier of a full lattice is an integer. -/
theorem ofReal_mem_multiplierRing_iff (L : PeriodPair) (r : ℝ) :
    (r : ℂ) ∈ L.lattice.toAddSubgroup.multiplierRing ↔ ∃ n : ℤ, r = n := by
  constructor
  · intro h
    obtain ⟨a, b, hab⟩ := mem_lattice.mp ((L.mem_multiplierRing_iff_periods r).mp h).1
    have hlin : (r - a) • L.ω₁ + (-(b : ℝ)) • L.ω₂ = 0 := by
      simp only [Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_intCast,
        Complex.ofReal_neg]
      linear_combination -hab
    exact ⟨a, sub_eq_zero.mp (LinearIndependent.pair_iff.mp L.indep _ _ hlin).1⟩
  · rintro ⟨n, rfl⟩
    apply AddSubgroup.mem_multiplierRing.mpr
    intro z hz
    simpa using L.lattice.smul_mem n hz

/-- A multiplier with zero imaginary part is an integer, and conversely. -/
theorem im_eq_zero_iff_of_mem_multiplierRing (L : PeriodPair) {α : ℂ}
    (hα : α ∈ L.lattice.toAddSubgroup.multiplierRing) : α.im = 0 ↔ ∃ n : ℤ, α = n := by
  constructor
  · intro hi
    have hr : (α.re : ℂ) = α := by apply Complex.ext <;> simp [hi]
    obtain ⟨n, hn⟩ := (L.ofReal_mem_multiplierRing_iff α.re).mp (hr.symm ▸ hα)
    exact ⟨n, by rw [← hr, hn]; simp⟩
  · rintro ⟨n, rfl⟩
    simp

/-- A noninteger multiplier is imaginary quadratic: its monic integer quadratic has
strictly negative discriminant. No choice of orientation for the lattice is required. -/
theorem exists_quadratic_negative_discriminant_of_mem_multiplierRing (L : PeriodPair)
    {α : ℂ} (hα : α ∈ L.lattice.toAddSubgroup.multiplierRing) (hnt : ¬ ∃ n : ℤ, α = n) :
    ∃ t n : ℤ, α ^ 2 - t * α + n = 0 ∧ t ^ 2 - 4 * n < 0 := by
  obtain ⟨t, n, h⟩ := L.exists_quadratic_of_mem_multiplierRing hα
  have hi : α.im ≠ 0 := (L.im_eq_zero_iff_of_mem_multiplierRing hα).not.mpr hnt
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp only [Complex.sub_im, Complex.add_im, Complex.sub_re, Complex.add_re,
    Complex.mul_im, Complex.mul_re, Complex.intCast_re, Complex.intCast_im,
    Complex.zero_im, Complex.zero_re, pow_two, zero_mul, sub_zero, add_zero] at him hre
  have ht : (t : ℝ) = 2 * α.re := by
    exact (sub_eq_zero.mp ((mul_eq_zero.mp (show (2 * α.re - t) * α.im = 0 by
      linear_combination him)).resolve_right hi)).symm
  have hneg : (t : ℝ) ^ 2 - 4 * n < 0 := by
    nlinarith [sq_pos_of_ne_zero hi]
  exact ⟨t, n, h, by exact_mod_cast hneg⟩

end PeriodPair
