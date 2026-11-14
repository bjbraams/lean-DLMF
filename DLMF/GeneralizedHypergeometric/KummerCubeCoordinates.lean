/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.GeneralizedHypergeometric.FiniteTransformationGroups

/-!
# Six-coordinate cube parametrization of Kummer solutions

Rao–Lakshminarayanan, *Generalized Hypergeometric Functions* (2018),
§3.2, (3.8)–(3.11), synopsis RL-3.02. The cube rotations produce
only the six anharmonic argument transformations.
-/

@[expose] public noncomputable section
open Complex Finset
namespace DLMF.Hypergeometric.TransformationGroups

/-- The Gauss parameters and argument obtained from the six zero-sum coordinates,
Rao–Lakshminarayanan (3.8)–(3.11), synopsis RL-3.02. -/
def kummerCubeParameters (x : Fin 6 → ℂ) : Fin 4 → ℂ :=
  ![1 / 2 + x 0 + x 1 + x 2, 1 / 2 + x 0 + x 1 + x 3,
    1 + x 0 - x 5, -(x 0 + x 5) / (x 2 + x 3)]

/-- The six-coordinate parameter map, Rao–Lakshminarayanan (3.8)–(3.11). -/
theorem kummerCubeParameters_def (x : Fin 6 → ℂ) : kummerCubeParameters x =
    ![1 / 2 + x 0 + x 1 + x 2, 1 / 2 + x 0 + x 1 + x 3,
      1 + x 0 - x 5, -(x 0 + x 5) / (x 2 + x 3)] := rfl

/-- The opposite-face reflection interchanges the two upper parameters,
Rao–Lakshminarayanan (3.8)–(3.11), synopsis RL-3.02. -/
theorem kummerCubeParameters_mirror (x : Fin 6 → ℂ) :
    kummerCubeParameters (x ∘ Equiv.swap 2 3) =
      ![kummerCubeParameters x 1, kummerCubeParameters x 0,
        kummerCubeParameters x 2, kummerCubeParameters x 3] := by
  funext i
  fin_cases i <;> simp [kummerCubeParameters, Equiv.swap_apply_def, add_comm]

/-- The argument orbit is contained in the six anharmonic transforms,
Rao–Lakshminarayanan (3.8)–(3.11), synopsis RL-3.02. Both displayed
six-coordinate arguments are required to have a nonzero denominator. -/
theorem kummerCubeParameters_argument_mem (x : Fin 6 → ℂ) (hx : ∑ i, x i = 0)
    (hden : x 2 + x 3 ≠ 0) (g : cubeRotations)
    (hgden : x (g.val.symm 2) + x (g.val.symm 3) ≠ 0) :
    let z := kummerCubeParameters x 3
    kummerCubeParameters (x ∘ g.val.symm) 3 ∈
      ({z, 1 - z, 1 / z, 1 / (1 - z), z / (z - 1), (z - 1) / z} : Finset ℂ) := by
  sorry

end DLMF.Hypergeometric.TransformationGroups
