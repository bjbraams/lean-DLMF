/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.ParabolicCylinder

/-!
# A source discrepancy in DLMF 12.13.6

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Confluent

/-- At n=0 and z=0, DLMF 12.13.6 would incorrectly assert this value equals one. -/
theorem pcfU_half_zero_ne_one  :
    pcfU (1/2) 0 ≠ 1 := by
  intro h
  rw [pcfU_zero] at h
  norm_num at h
  have hp : (2:ℂ)^(1/2:ℂ)=(Real.sqrt 2:ℂ) := by
    have hh := (Complex.ofReal_cpow (by norm_num : 0 ≤ (2:ℝ)) (1/2:ℝ)).symm
    rw [← Real.sqrt_eq_rpow 2] at hh
    simpa using hh
  rw [hp] at h
  have hr : Real.sqrt π/Real.sqrt 2=1 := by exact_mod_cast h
  have he : Real.sqrt π=Real.sqrt 2 := (div_eq_one_iff_eq (by positivity)).mp hr
  have hsπ:=Real.sq_sqrt Real.pi_pos.le
  have hs2:=Real.sq_sqrt (by norm_num : 0 ≤ (2:ℝ))
  have hπ:=Real.pi_gt_three
  rw [← he] at hs2
  linarith

/-- Counterexample to the printed formula, using only the pre-existing cylinder and error-function theory. -/
theorem dlmf_12_13_6_counterexample  :
    pcfU (1/2) 0 ≠ exp (-(0:ℂ)^2/2)*erfc (0/Real.sqrt 2)*pcfU (-1/2) (I*0) := by
  simpa [erfc,erf_zero,pcfU_neg_half] using pcfU_half_zero_ne_one

end DLMF.Confluent
