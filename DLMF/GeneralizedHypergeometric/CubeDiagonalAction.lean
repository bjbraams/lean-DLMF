/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.GeneralizedHypergeometric.FiniteTransformationGroups

/-!
# The actual body-diagonal action of the cube group

Rao–Lakshminarayanan, *Generalized Hypergeometric Functions* (2018), Chapter 3,
(3.6)–(3.7), p. 3-3, synopsis RL-3.01. Faces are numbered `0,…,5`, with
opposite pairs `(0,5)`, `(1,4)`, `(2,3)`. A vertex is its incident-face triple;
an unoriented body diagonal is the pair of its antipodal vertices.
-/

@[expose] public noncomputable section

open Equiv Finset

namespace DLMF.Hypergeometric.TransformationGroups

/-- Opposite faces in the book's six-face labelling.
Rao–Lakshminarayanan (3.6)–(3.7), synopsis RL-3.01. -/
def cubeOppositeFace : Perm (Fin 6) :=
  { toFun := fun i => ⟨5 - i.val, by omega⟩
    invFun := fun i => ⟨5 - i.val, by omega⟩
    left_inv := by decide
    right_inv := by decide }

/-- The four actual unoriented body diagonals, represented by antipodal incident-face
triples. Rao–Lakshminarayanan (3.6)–(3.7), synopsis RL-3.01. -/
def cubeBodyDiagonal (i : Fin 4) : Finset (Finset (Fin 6)) :=
  let v : Finset (Fin 6) :=
    {0, if i.val % 2 = 0 then 1 else 4, if i.val / 2 = 0 then 2 else 3}
  {v, v.image cubeOppositeFace}

/-- The explicit opposite-face permutation. -/
theorem cubeOppositeFace_apply (i : Fin 6) :
    cubeOppositeFace i = (⟨5 - i.val, by omega⟩ : Fin 6) := rfl

/-- The defining antipodal-vertex representation of each body diagonal. -/
theorem cubeBodyDiagonal_def (i : Fin 4) : cubeBodyDiagonal i =
    let v : Finset (Fin 6) :=
      {0, if i.val % 2 = 0 then 1 else 4, if i.val / 2 = 0 then 2 else 3}
    {v, v.image cubeOppositeFace} := rfl

/-- The isomorphism with `S₄` is induced by the actual action on the four unoriented
body diagonals, rather than merely an abstract isomorphism.
Rao–Lakshminarayanan (3.6)–(3.7), p. 3-3, synopsis RL-3.01. -/
theorem exists_cubeBodyDiagonal_mulEquiv :
    ∃ ρ : cubeRotations ≃* Perm (Fin 4), ∀ g i,
      cubeBodyDiagonal (ρ g i) =
        (cubeBodyDiagonal i).image (fun v => v.image g.val) := by
  sorry

end DLMF.Hypergeometric.TransformationGroups
