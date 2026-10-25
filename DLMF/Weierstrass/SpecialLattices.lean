/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Weierstrass.Basic
public import DLMF.Elliptic.SpecialValues
public import DLMF.JacobiElliptic.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Real-valued Weierstrass functions and special lattices (DLMF §23.5)

Rectangular, lemniscatic, rhombic and equianharmonic lattices are described by predicates on
DLMF half-periods. Real numbers are complex numbers with vanishing imaginary part, and order
statements are made for real parts. The complete elliptic integral of 23.5.5 is the project's
real `DLMF.Elliptic.Real.compEllIntKm` with parameter `m = k² = 1/2`; the complex values in
23.5.9 use the principal complex integral `DLMF.JacobiElliptic.compEllIntKk` (modulus form) of the
Chapter 22 acquisition, and the modulus `k = e^{iπ/6}` with `k² = e^{iπ/3}`.
-/

@[expose] public section

open Complex PeriodPair
open scoped Real

noncomputable section

namespace DLMF.Weierstrass

/-- DLMF §23.5(i): the Weierstrass functions are real on the real axis iff the lattice is
invariant under complex conjugation, equivalently iff `g₂, g₃ ∈ ℝ`. Stated for `℘`. -/
@[dlmf 23.5.i]
theorem weierstrassP_real_iff (L : PeriodPair) :
    ((∀ x : ℝ, (x : ℂ) ∉ L.lattice → (℘[L] x).im = 0) ↔
        (starRingEnd ℂ) '' (L.lattice : Set ℂ) = L.lattice) ∧
      ((starRingEnd ℂ) '' (L.lattice : Set ℂ) = L.lattice ↔ L.g₂.im = 0 ∧ L.g₃.im = 0) := by
  sorry

namespace HalfPeriods

variable (H : HalfPeriods)

/-- A rectangular lattice (DLMF §23.5(ii)): `ω₁ > 0` and `ω₃/i > 0`. -/
def IsRectangular : Prop :=
  H.ω₁.im = 0 ∧ 0 < H.ω₁.re ∧ H.ω₃.re = 0 ∧ 0 < H.ω₃.im

/-- A lemniscatic lattice (DLMF §23.5(iii)): `ω₁ > 0` and `ω₃ = iω₁`. -/
def IsLemniscatic : Prop :=
  H.ω₁.im = 0 ∧ 0 < H.ω₁.re ∧ H.ω₃ = I * H.ω₁

/-- A rhombic lattice (DLMF §23.5(iv)): `ω₁ > 0`, `ℑω₃ > 0` and `ℜω₃ = ω₁/2`. (DLMF also lists
`Δ < 0`; this follows from the other conditions, see `IsRhombic.discriminant_neg`.) -/
def IsRhombic : Prop :=
  H.ω₁.im = 0 ∧ 0 < H.ω₁.re ∧ H.ω₃.re = H.ω₁.re / 2

/-- An equianharmonic lattice (DLMF §23.5(v)): `ω₁ > 0` and `ω₃ = e^{πi/3}ω₁`. -/
def IsEquianharmonic : Prop :=
  H.ω₁.im = 0 ∧ 0 < H.ω₁.re ∧ H.ω₃ = cexp (π * I / 3) * H.ω₁

/-- DLMF §23.5(ii): for a rectangular lattice `Δ > 0`. -/
@[dlmf 23.5.ii]
theorem IsRectangular.discriminant_pos {H : HalfPeriods} (h : H.IsRectangular) :
    (latticeDiscriminant H.periodPair).im = 0 ∧ 0 < (latticeDiscriminant H.periodPair).re := by
  sorry

/-- DLMF 23.5.1: for a rectangular lattice the roots are real with `e₁ > e₂ > e₃` and
`e₁ > 0 > e₃`. -/
@[dlmf 23.5.E1]
theorem IsRectangular.roots {H : HalfPeriods} (h : H.IsRectangular) :
    (H.e 1).im = 0 ∧ (H.e 2).im = 0 ∧ (H.e 3).im = 0 ∧
      (H.e 2).re < (H.e 1).re ∧ (H.e 3).re < (H.e 2).re ∧ 0 < (H.e 1).re ∧ (H.e 3).re < 0 := by
  sorry

/-- DLMF §23.5(ii): for a rectangular lattice `e₂` and `g₃` have opposite signs unless
`ω₃ = iω₁`, in which case both vanish. -/
@[dlmf 23.5.ii]
theorem IsRectangular.e_two_g₃ {H : HalfPeriods} (h : H.IsRectangular) :
    H.g₃.im = 0 ∧ (H.ω₃ = I * H.ω₁ → H.e 2 = 0 ∧ H.g₃ = 0) ∧
      (H.ω₃ ≠ I * H.ω₁ → (H.e 2).re * H.g₃.re < 0) := by
  sorry

/-- Rectangular half-periods `ω₁ = a`, `ω₃ = ib` with `a, b > 0`. -/
def rectangular (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : HalfPeriods :=
  ⟨a, b * I, by exact_mod_cast ha.ne', by
    rw [Complex.div_ofReal_im]; simpa using div_pos hb ha⟩

/-- DLMF §23.5(ii): with `ω₁` fixed, `e₁` and `e₂` are decreasing and `e₃` is increasing
functions of `ℑω₃`. -/
@[dlmf 23.5.ii]
theorem rectangular_roots_monotone (a b₁ b₂ : ℝ) (ha : 0 < a) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂)
    (hb : b₁ < b₂) :
    ((rectangular a b₂ ha hb₂).e 1).re < ((rectangular a b₁ ha hb₁).e 1).re ∧
      ((rectangular a b₂ ha hb₂).e 2).re < ((rectangular a b₁ ha hb₁).e 2).re ∧
      ((rectangular a b₁ ha hb₁).e 3).re < ((rectangular a b₂ ha hb₂).e 3).re := by
  sorry

/-- DLMF 23.5.2: for a lemniscatic lattice `η₁ = iη₃ = π/(4ω₁)`. -/
@[dlmf 23.5.E2]
theorem IsLemniscatic.eta {H : HalfPeriods} (h : H.IsLemniscatic) :
    H.eta 1 = I * H.eta 3 ∧ H.eta 1 = π / (4 * H.ω₁) := by
  sorry

/-- DLMF 23.5.3: for a lemniscatic lattice `e₁ = -e₃ = Γ(1/4)⁴/(32πω₁²)` and `e₂ = 0`. -/
@[dlmf 23.5.E3]
theorem IsLemniscatic.roots {H : HalfPeriods} (h : H.IsLemniscatic) :
    H.e 1 = -H.e 3 ∧ H.e 1 = (Real.Gamma (1 / 4) : ℂ) ^ 4 / (32 * π * H.ω₁ ^ 2) ∧ H.e 2 = 0 := by
  sorry

/-- DLMF 23.5.4: for a lemniscatic lattice `g₂ = Γ(1/4)⁸/(256π²ω₁⁴)` and `g₃ = 0`. -/
@[dlmf 23.5.E4]
theorem IsLemniscatic.invariants {H : HalfPeriods} (h : H.IsLemniscatic) :
    H.g₂ = (Real.Gamma (1 / 4) : ℂ) ^ 8 / (256 * π ^ 2 * H.ω₁ ^ 4) ∧ H.g₃ = 0 := by
  sorry

/-- DLMF §23.5(iii): for a lemniscatic lattice `τ = i`. -/
@[dlmf 23.5.iii]
theorem IsLemniscatic.tau {H : HalfPeriods} (h : H.IsLemniscatic) : H.tau = I := by
  rw [HalfPeriods.tau, h.2.2, mul_div_assoc, div_self H.ω₁_ne_zero, mul_one]

/-- DLMF 23.5.5: for a lemniscatic lattice the modulus defined by 23.6.16 satisfies
`k² = (e₂ - e₃)/(e₁ - e₃) = 1/2` (derived from 23.5.3). -/
@[dlmf 23.5.E5]
theorem IsLemniscatic.modulus_sq {H : HalfPeriods} (h : H.IsLemniscatic) :
    (H.e 2 - H.e 3) / (H.e 1 - H.e 3) = 1 / 2 := by
  obtain ⟨h13, h1, h2⟩ := h.roots
  have hne : H.e 1 ≠ 0 := by
    rw [h1]
    have hg : (Real.Gamma (1 / 4) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 4)).ne'
    have := H.ω₁_ne_zero
    have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hω := H.ω₁_ne_zero
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact div_ne_zero (pow_ne_zero 4 hg) (mul_ne_zero (mul_ne_zero (by norm_num) hπ)
      (pow_ne_zero 2 hω))
  have h3 : H.e 3 = -H.e 1 := by rw [h13]; ring
  rw [h2, h3]
  field_simp
  ring

/-- DLMF 23.5.5: `K(k) = K'(k) = Γ(1/4)²/(4√π)` for `k² = 1/2` (parameter form; this is the
project's `DLMF.Elliptic.Real.compEllIntKm_one_half`, and `K' = K(1 - k²) = K(1/2)`). -/
@[dlmf 23.5.E5]
theorem compEllIntKm_lemniscatic :
    DLMF.Elliptic.Real.compEllIntKm (1 / 2) = Real.Gamma (1 / 4) ^ 2 / (4 * Real.sqrt π) ∧
      DLMF.Elliptic.Real.compEllIntKm (1 - 1 / 2) = DLMF.Elliptic.Real.compEllIntKm (1 / 2) :=
  ⟨DLMF.Elliptic.Real.compEllIntKm_one_half, by norm_num⟩

/-- DLMF §23.5(iv): for a rhombic lattice `Δ < 0`. -/
@[dlmf 23.5.iv]
theorem IsRhombic.discriminant_neg {H : HalfPeriods} (h : H.IsRhombic) :
    (latticeDiscriminant H.periodPair).im = 0 ∧ (latticeDiscriminant H.periodPair).re < 0 := by
  sorry

/-- DLMF §23.5(iv): for a rhombic lattice `e₁` is real and `e₃ = conj e₂` with `ℑe₂ > 0`; `e₁`
and `g₃` have the same sign unless `2ω₃ = (1 + i)ω₁` (the pseudo-lemniscatic case), when both
vanish. -/
@[dlmf 23.5.iv]
theorem IsRhombic.roots {H : HalfPeriods} (h : H.IsRhombic) :
    (H.e 1).im = 0 ∧ H.e 3 = (starRingEnd ℂ) (H.e 2) ∧ 0 < (H.e 2).im ∧ H.g₃.im = 0 ∧
      (2 * H.ω₃ = (1 + I) * H.ω₁ → H.e 1 = 0 ∧ H.g₃ = 0) ∧
      (2 * H.ω₃ ≠ (1 + I) * H.ω₁ → 0 < (H.e 1).re * H.g₃.re) := by
  sorry

/-- Rhombic half-periods `ω₁ = a`, `ω₃ = a/2 + ib` with `a, b > 0`. -/
def rhombic (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : HalfPeriods :=
  ⟨a, a / 2 + b * I, by exact_mod_cast ha.ne', by
    rw [Complex.div_ofReal_im]; simpa using div_pos hb ha⟩

/-- DLMF §23.5(iv): for rhombic lattices with fixed `ω₁`, `e₁` is an increasing function of
`ℑe₃`. -/
@[dlmf 23.5.iv]
theorem rhombic_e_one_monotone (a b₁ b₂ : ℝ) (ha : 0 < a) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂)
    (h : ((rhombic a b₁ ha hb₁).e 3).im < ((rhombic a b₂ ha hb₂).e 3).im) :
    ((rhombic a b₁ ha hb₁).e 1).re < ((rhombic a b₂ ha hb₂).e 1).re := by
  sorry

/-- DLMF 23.5.6: for an equianharmonic lattice `η₁ = e^{πi/3}η₃ = π/(2√3 ω₁)`. -/
@[dlmf 23.5.E6]
theorem IsEquianharmonic.eta {H : HalfPeriods} (h : H.IsEquianharmonic) :
    H.eta 1 = cexp (π * I / 3) * H.eta 3 ∧ H.eta 1 = π / (2 * Real.sqrt 3 * H.ω₁) := by
  sorry

/-- DLMF 23.5.7: for an equianharmonic lattice
`e₁ = e^{2πi/3}e₃ = e^{-2πi/3}e₂ = Γ(1/3)⁶/(2^{14/3}π²ω₁²)`. -/
@[dlmf 23.5.E7]
theorem IsEquianharmonic.roots {H : HalfPeriods} (h : H.IsEquianharmonic) :
    H.e 1 = cexp (2 * π * I / 3) * H.e 3 ∧ H.e 1 = cexp (-(2 * π * I / 3)) * H.e 2 ∧
      H.e 1 = (Real.Gamma (1 / 3) : ℂ) ^ 6 / ((2 : ℂ) ^ (14 / 3 : ℂ) * π ^ 2 * H.ω₁ ^ 2) := by
  sorry

/-- DLMF 23.5.8: for an equianharmonic lattice `g₂ = 0` and `g₃ = Γ(1/3)¹⁸/(4πω₁)⁶`. -/
@[dlmf 23.5.E8]
theorem IsEquianharmonic.invariants {H : HalfPeriods} (h : H.IsEquianharmonic) :
    H.g₂ = 0 ∧ H.g₃ = (Real.Gamma (1 / 3) : ℂ) ^ 18 / (4 * π * H.ω₁) ^ 6 := by
  sorry

/-- DLMF §23.5(v): for an equianharmonic lattice `τ = e^{iπ/3}`. -/
@[dlmf 23.5.v]
theorem IsEquianharmonic.tau {H : HalfPeriods} (h : H.IsEquianharmonic) :
    H.tau = cexp (π * I / 3) := by
  rw [HalfPeriods.tau, h.2.2, mul_div_assoc, div_self H.ω₁_ne_zero, mul_one]

/-- DLMF 23.5.9: for an equianharmonic lattice the modulus of 23.6.16 satisfies
`k² = (e₂ - e₃)/(e₁ - e₃) = e^{iπ/3}`. -/
@[dlmf 23.5.E9]
theorem IsEquianharmonic.modulus_sq {H : HalfPeriods} (h : H.IsEquianharmonic) :
    (H.e 2 - H.e 3) / (H.e 1 - H.e 3) = cexp (π * I / 3) := by
  obtain ⟨h13, h12, hv⟩ := h.roots
  set x := cexp (π * I / 3) with hx
  have hx3 : x ^ 3 = -1 := by
    rw [hx, ← Complex.exp_nat_mul]; push_cast
    rw [show (3 : ℂ) * (π * I / 3) = π * I by ring, Complex.exp_pi_mul_I]
  have hxre : x.re = 1 / 2 := by
    rw [hx, show (π : ℂ) * I / 3 = ((π / 3 : ℝ) : ℂ) * I by push_cast; ring,
      Complex.exp_ofReal_mul_I_re, Real.cos_pi_div_three]
  have hx1 : 1 + x ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp [hxre] at this
    norm_num at this
  have hx0 : x ≠ 0 := Complex.exp_ne_zero _
  have hA : cexp (2 * π * I / 3) = x ^ 2 := by
    rw [hx, ← Complex.exp_nat_mul]; push_cast; ring_nf
  have hB : cexp (-(2 * π * I / 3)) = -x := by
    have : cexp (-(2 * π * I / 3)) * x ^ 2 = 1 := by
      rw [← hA, ← Complex.exp_add]; simp
    have h2 : x ^ 2 * (-x) = 1 := by linear_combination -hx3
    have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx0
    exact mul_right_cancel₀ hx2 (by rw [this]; linear_combination -h2)
  rw [hA] at h13
  rw [hB] at h12
  have he1 : H.e 1 ≠ 0 := by
    rw [hv]
    have hg : (Real.Gamma (1 / 3) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 3)).ne'
    have := H.ω₁_ne_zero
    have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have : (2 : ℂ) ^ (14 / 3 : ℂ) ≠ 0 := by simp
    have hω := H.ω₁_ne_zero
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have h2 : (2 : ℂ) ^ (14 / 3 : ℂ) ≠ 0 := by simp
    exact div_ne_zero (pow_ne_zero 6 hg) (mul_ne_zero (mul_ne_zero h2 (pow_ne_zero 2 hπ))
      (pow_ne_zero 2 hω))
  -- `e₂ = x² e₁` and `e₃ = -x e₁`.
  have he2 : H.e 2 = x ^ 2 * H.e 1 := by
    have : (-x) * (x ^ 2 * H.e 1) = H.e 1 := by linear_combination (-(H.e 1)) * hx3
    have hnx : -x ≠ 0 := neg_ne_zero.mpr hx0
    exact mul_left_cancel₀ hnx (by rw [this, ← h12])
  have he3 : H.e 3 = -x * H.e 1 := by
    have : x ^ 2 * (-x * H.e 1) = H.e 1 := by linear_combination (-(H.e 1)) * hx3
    exact mul_left_cancel₀ (pow_ne_zero 2 hx0) (by rw [this, ← h13])
  have hden : H.e 1 - -x * H.e 1 ≠ 0 := by
    rw [show H.e 1 - -x * H.e 1 = (1 + x) * H.e 1 by ring]
    exact mul_ne_zero hx1 he1
  rw [he2, he3, div_eq_iff hden]
  ring

/-- DLMF 23.5.9: for `k = e^{iπ/6}` (so `k² = e^{iπ/3}`),
`K(k) = e^{iπ/6}K'(k) = e^{iπ/12} 3^{1/4} Γ(1/3)³/(2^{7/3}π)`, with the principal complex
complete elliptic integrals. -/
@[dlmf 23.5.E9]
theorem compEllIntKk_equianharmonic :
    JacobiElliptic.compEllIntKk (cexp (π * I / 6)) =
        cexp (π * I / 6) * JacobiElliptic.compEllIntKpk (cexp (π * I / 6)) ∧
      JacobiElliptic.compEllIntKk (cexp (π * I / 6)) =
        cexp (π * I / 12) * (3 : ℂ) ^ (1 / 4 : ℂ) * (Real.Gamma (1 / 3) : ℂ) ^ 3 /
          ((2 : ℂ) ^ (7 / 3 : ℂ) * π) := by
  sorry

end HalfPeriods

end DLMF.Weierstrass
