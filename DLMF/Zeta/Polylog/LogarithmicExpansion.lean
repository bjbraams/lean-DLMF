/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Zeta.Lerch.LogarithmicExpansion

/-!
# The regular logarithmic series of the principal polylogarithm

Specializing Lerch's expansion at parameter one gives the regular part of the
polylogarithm at `z = 1`. The singular term is expressed using `-log z`, which retains
the principal branch on the negative real axis.
-/

@[expose] public noncomputable section
open Complex Set
open scoped Real Topology Nat

namespace DLMF.Zeta.PolylogLogarithmic

/-- The Hurwitz coefficients at parameter one give the polylogarithm's regular Taylor series. -/
theorem hasSum_regularized {s z : ℂ} (hs : ∀ n : ℕ, s ≠ (n : ℂ) + 1)
    (hz : z ∈ slitOne) (hz0 : z ≠ 0) (hlog : ‖log z‖ < 2 * π) :
    HasSum (fun n : ℕ => riemannZeta (s - n) * log z ^ n / n !)
      (polylog s z - Gamma (1 - s) * (-log z) ^ (s - 1)) := by
  have h := LerchLogarithmic.hasSum_lerchPhi_log hs
    (lerchParamAdmissible_of_re_pos (a := 1) (by norm_num) s)
    (by intro m hm; have := congrArg re hm; simp at this; linarith [Nat.cast_nonneg (α := ℝ) m])
    hz hz0 hlog
  rw [cpow_one, ← polylog_eq_mul_lerchPhi_of_mem_slitOne s hz] at h
  refine h.congr_fun fun n => ?_
  rw [hurwitzZetaComplex_one]
  intro hn
  apply hs n
  linear_combination hn

end DLMF.Zeta.PolylogLogarithmic
