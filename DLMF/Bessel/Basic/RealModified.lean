/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bessel.Basic
public import TauCeti.Analysis.SpecialFunctions.BesselI

/-!
# The modified Bessel function `I_ν` on the real line

TauCeti defines the real modified Bessel function `Real.besselI ν x` as the real part of the
complex series formula. This file identifies it with the restriction of the complex function
`DLMF.Bessel.besselI` (DLMF 10.25.2).

## Main results

* `DLMF.Bessel.re_besselI_ofReal`: `Re I_ν(x) = Real.besselI ν x` for all real `ν`, `x`.
* `DLMF.Bessel.besselI_ofReal`: `I_ν(x) = Real.besselI ν x` for real `ν` and `x ≥ 0`.
-/

@[expose] public section

open Complex

namespace DLMF.Bessel

/-- The real part of `I_ν` on the real line is TauCeti's real modified Bessel function. -/
theorem re_besselI_ofReal (ν x : ℝ) : (besselI ν x).re = Real.besselI ν x := by
  rw [Real.besselI_def, besselI]
  congr 3
  ring

/-- For `x ≥ 0`, `I_ν(x)` is real and equals TauCeti's real modified Bessel function. -/
theorem besselI_ofReal (ν : ℝ) {x : ℝ} (hx : 0 ≤ x) : besselI ν x = Real.besselI ν x := by
  have hF := Complex.regularizedHGFun_zero_singleton_ofReal_im (ν + 1) ((x / 2) ^ 2)
  have hp : ((x : ℂ) / 2) ^ (ν : ℂ) = (((x / 2) ^ ν : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (by positivity)]
    push_cast
    rfl
  apply Complex.ext
  · exact re_besselI_ofReal ν x
  · rw [besselI, Complex.ofReal_im, show (x : ℂ) ^ 2 / 4 = (((x / 2) ^ 2 : ℝ) : ℂ) by
      push_cast; ring, hp, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      add_zero]
    push_cast at hF ⊢
    exact mul_eq_zero_of_right _ hF
