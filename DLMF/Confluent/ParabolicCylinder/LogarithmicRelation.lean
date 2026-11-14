/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.ParabolicCylinder.EquationAndIntegrals
public import DLMF.Confluent.Asymptotics.LogarithmicSector

/-!
# Correlated parabolic-cylinder and Tricomi continuation

Olver, *Asymptotics and Special Functions*, Chapter 7, §§9–10,
pp. 257–262, synopsis O-7.17. The Tricomi logarithm is `2w-log(2)` when
`z=exp(w)`; it is not replaced by the principal logarithm of `z²/2` after
turning around the origin. The parabolic-cylinder function itself is entire.
-/

@[expose] public noncomputable section

open Complex
open scoped Real

namespace DLMF.Confluent

/-- The full logarithmic-plane cylinder/Tricomi identity, including negative real
arguments obtained by a correlated half-turn. Olver, Chapter 7, §§9–10,
pp. 257–262, synopsis O-7.17. -/
theorem parabolicCylinderU_eq_kummerUContinuedOnLog (a w : ℂ) :
    parabolicCylinderU a (exp w) =
      (2 : ℂ) ^ (-a / 2 - 1 / 4) * exp (-(exp w) ^ 2 / 4) *
        kummerUContinuedOnLog (a / 2 + 1 / 4) (1 / 2) (2 * w - Real.log 2) := by
  sorry

end DLMF.Confluent
