/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AsymptoticApproximations.Integrals.Basic
public import DLMF.ParabolicCylinder.Basic

/-!
# Parabolic-cylinder evaluation of the Bleistein moments

Olver, *Asymptotics and Special Functions*, Chapter 9, §9,
pp. 344–346, synopsis O-9.11. This exact finite moment reduction is independent
of a remainder estimate for extending a finite endpoint integral to infinity.
-/

@[expose] public noncomputable section
open Complex
namespace DLMF.AsymptoticApproximations

/-- Every polynomial centered Gaussian moment is a finite combination of the
canonical Weber U function. Olver, Chapter 9, §9, pp. 344–346. -/
theorem bleisteinF_eq_sum_parabolicCylinderU {lam : ℝ} (hlam : 0 < lam)
    (s : ℕ) (y : ℝ) :
    (bleisteinF lam s y : ℂ) = exp ((y : ℂ) ^ 2 / 4) *
      ∑ k ∈ Finset.range (s + 1), (s.choose k : ℂ) * (-(y : ℂ)) ^ (s - k) *
        Gamma (lam + k) * DLMF.Confluent.parabolicCylinderU (lam + k - 1 / 2) (-y) := by
  sorry

end DLMF.AsymptoticApproximations
