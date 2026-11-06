/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
import DLMF.Zeta.Basic.LerchProperties
open Complex DLMF.Zeta
open scoped Real Topology

/-!
# The positive-integer obstruction to a pointwise Lerch transformation

The series gives `Re Φ(1/2, 1, 1/2) ≥ 2`, while the factor `Γ(1-s)` vanishes at `s = 1`
under Lean's totalization. Thus the pointwise expression in DLMF 25.14.7 cannot hold at
this order, regardless of the value of the remaining bracket. This check imports only the
proved foundational layer.
-/

namespace DLMF.Zeta.LerchTransformationCheck

/-- The first positive series term is a lower bound for the value. -/
theorem two_le_re_lerchPhi_half : 2 ≤ (lerchPhi (1 / 2) 1 (1 / 2)).re := by
  have hparam : LerchParamAdmissible 1 (1 / 2) := by
    constructor
    · intro h; exact False.elim (h 1 (by norm_num))
    · intro _ m hm
      have := congrArg Complex.re hm
      simp at this
      linarith [Nat.cast_nonneg (α := ℝ) m]
  have hS := hasSum_lerchPhi (z := (1 / 2 : ℂ)) hparam (by norm_num)
  have hR : HasSum (fun n : ℕ => (1 / 2 : ℝ) ^ n / (1 / 2 + n))
      (lerchPhi (1 / 2) 1 (1 / 2)).re := by
    convert Complex.hasSum_re hS using 1
    funext n
    rw [cpow_one]
    have hcast : (((1 / 2 : ℝ) ^ n / (1 / 2 + n) : ℝ) : ℂ) =
        (1 / 2 : ℂ) ^ n / (1 / 2 + n) := by push_cast; rfl
    rw [← hcast, ofReal_re]
  have h := hR.summable.le_tsum 0 (fun n _ => by positivity)
  rw [hR.tsum_eq] at h
  simpa using h

/-- The pointwise right-hand side of Lerch's transformation vanishes at order one. -/
theorem pointwise_transformation_ne_at_one (B : ℂ) :
    lerchPhi (1 / 2) 1 (1 / 2) ≠
      I * (2 * π) ^ ((1 : ℂ) - 1) / (1 / 2 : ℂ) ^ (1 / 2 : ℂ) *
        Gamma (1 - (1 : ℂ)) * B := by
  have hn : lerchPhi (1 / 2) 1 (1 / 2) ≠ 0 := by
    intro h
    have hbound := two_le_re_lerchPhi_half
    rw [h, zero_re] at hbound
    norm_num at hbound
  simpa using hn

end DLMF.Zeta.LerchTransformationCheck

#print axioms DLMF.Zeta.LerchTransformationCheck.two_le_re_lerchPhi_half
#print axioms DLMF.Zeta.LerchTransformationCheck.pointwise_transformation_ne_at_one
