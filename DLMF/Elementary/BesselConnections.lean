/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bessel.Theorems

/-!
# The elementary zero equation for `J₃/₂` (DLMF §4.46)

The numerical root tables mentioned in §4.46 are excluded, while the exact
identification of their positive roots with zeros of `J₃/₂` is retained.
The proof uses the project's half-order evaluations and three-term recurrence.
-/

@[expose] public noncomputable section

open Complex
open scoped Real

namespace DLMF.Elementary

/-- Elementary half-integer evaluation used in the root correspondence. -/
theorem besselJ_three_halves {z : ℂ} (hz : z ∈ slitPlane) :
    Complex.besselJ (3 / 2) z =
      (2 / (π * z)) ^ (1 / 2 : ℂ) * (sin z / z - cos z) := by
  have h := DLMF.Bessel.besselJ_add_sub (ν := 1 / 2) (slitPlane_ne_zero hz)
  rw [show (1 / 2 : ℂ) - 1 = -(1 / 2) by ring,
    show (1 / 2 : ℂ) + 1 = 3 / 2 by ring,
    DLMF.Bessel.besselJ_half z hz, DLMF.Bessel.besselJ_neg_half z hz] at h
  linear_combination -h

/-- The positive solutions of `tan x = x` are exactly the positive zeros of `J₃/₂`.
This is the mathematical parenthesis in the numerical-table section. -/
@[dlmf 4.46]
theorem tan_eq_self_iff_besselJ_zero {x : ℝ} (hx : 0 < x) :
    Real.tan x = x ↔ Complex.besselJ (3 / 2) x = 0 := by
  have hz : (x : ℂ) ∈ slitPlane := by simpa [ofReal_mem_slitPlane] using hx
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have ha : (2 / (π * (x : ℂ))) ^ (1 / 2 : ℂ) ≠ 0 := by
    exact cpow_ne_zero_iff.mpr (Or.inl (div_ne_zero (by norm_num) (mul_ne_zero hπ hx0)))
  rw [besselJ_three_halves hz, mul_eq_zero, or_iff_right ha]
  have heq : (sin (x : ℂ) / (x : ℂ) - cos (x : ℂ) = 0) ↔
      Real.sin x = x * Real.cos x := by
    rw [sub_eq_zero, div_eq_iff hx0]
    norm_cast
    rw [mul_comm]
  rw [heq]
  constructor
  · intro ht
    have hc : Real.cos x ≠ 0 := by
      intro hc
      simp only [Real.tan_eq_sin_div_cos, hc, div_zero] at ht
      exact hx.ne' ht.symm
    exact (div_eq_iff hc).mp (by simpa only [Real.tan_eq_sin_div_cos] using ht)
  · intro hs
    have hc : Real.cos x ≠ 0 := by
      intro hc
      have hzsin : Real.sin x = 0 := by simpa [hc] using hs
      have hp := Real.sin_sq_add_cos_sq x
      simp [hc, hzsin] at hp
    simpa only [Real.tan_eq_sin_div_cos] using (div_eq_iff hc).mpr hs

end DLMF.Elementary
