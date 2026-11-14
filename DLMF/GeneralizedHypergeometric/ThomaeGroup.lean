/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.GeneralizedHypergeometric.TransformationGroups
public import Mathlib.GroupTheory.Perm.Basic

/-!
# The actual linear group of Thomae parameter transformations

Rao–Lakshminarayanan, *Generalized Hypergeometric Functions* (2018),
(4.107)–(4.122), pp. 4-18–4-20, synopsis RL-4.12. The generators act on
`(a,b,c,d,e)` itself; their generated group is identified with the five-coordinate
permutation group of the normalized Thomae invariant.
-/

@[expose] public noncomputable section
namespace DLMF.Hypergeometric.ThomaeCoordinates

/-- The Thomae parameter permutation with its explicit linear inverse,
Rao–Lakshminarayanan (4.107)–(4.122), synopsis RL-4.12. -/
def thomaeEquiv : Equiv.Perm (Fin 5 → ℂ) where
  toFun v :=
    let s := v 3 + v 4 - v 0 - v 1 - v 2
    ![v 3 - v 0, v 4 - v 0, s, s + v 1, s + v 2]
  invFun v := ![v 3 + v 4 - v 0 - v 1 - v 2, v 3 - v 2, v 4 - v 2,
    v 3 + v 4 - v 1 - v 2, v 3 + v 4 - v 0 - v 2]
  left_inv v := by ext i; fin_cases i <;> norm_num <;> ring
  right_inv v := by ext i; fin_cases i <;> norm_num <;> ring

/-- The forward Thomae transformation. -/
theorem thomaeEquiv_apply (v : Fin 5 → ℂ) :
    thomaeEquiv v =
      let s := v 3 + v 4 - v 0 - v 1 - v 2
      ![v 3 - v 0, v 4 - v 0, s, s + v 1, s + v 2] := rfl

/-- The inverse linear Thomae parameter map. -/
theorem thomaeEquiv_symm_apply (v : Fin 5 → ℂ) :
    thomaeEquiv.symm v =
      ![v 3 + v 4 - v 0 - v 1 - v 2, v 3 - v 2, v 4 - v 2,
        v 3 + v 4 - v 1 - v 2, v 3 + v 4 - v 0 - v 2] := rfl

/-- The Thomae generator is a five-cycle in the invariant coordinates,
Rao–Lakshminarayanan (4.107)–(4.122), synopsis RL-4.12. -/
theorem thomaeEquiv_parameters (x : Fin 5 → ℂ) :
    thomaeEquiv (parameters x) = parameters ![x 3, x 4, x 0, x 1, x 2] := by
  ext i
  fin_cases i <;> norm_num [thomaeEquiv, parameters, Fin.sum_univ_succ] <;> ring

/-- The three upper/lower swaps and the Thomae map,
Rao–Lakshminarayanan (4.107)–(4.122), synopsis RL-4.12. -/
def linearGenerator : Fin 4 → Equiv.Perm (Fin 5 → ℂ) :=
  ![Equiv.arrowCongr (Equiv.swap 0 1) (Equiv.refl ℂ),
    Equiv.arrowCongr (Equiv.swap 1 2) (Equiv.refl ℂ),
    Equiv.arrowCongr (Equiv.swap 3 4) (Equiv.refl ℂ), thomaeEquiv]

/-- The defining four linear generators. -/
theorem linearGenerator_def : linearGenerator =
    ![Equiv.arrowCongr (Equiv.swap 0 1) (Equiv.refl ℂ),
      Equiv.arrowCongr (Equiv.swap 1 2) (Equiv.refl ℂ),
      Equiv.arrowCongr (Equiv.swap 3 4) (Equiv.refl ℂ), thomaeEquiv] := rfl

/-- The subgroup of actual parameter transformations,
Rao–Lakshminarayanan RL-4.12. -/
def linearGroup : Subgroup (Equiv.Perm (Fin 5 → ℂ)) :=
  Subgroup.closure (Set.range linearGenerator)

/-- The generating description of the Thomae linear group. -/
theorem linearGroup_def : linearGroup = Subgroup.closure (Set.range linearGenerator) := rfl

/-- Conjugating the parameter action by the affine coordinate map gives the full
five-coordinate permutation group, Rao–Lakshminarayanan RL-4.12. -/
theorem exists_linearGroup_mulEquiv_perm_five :
    ∃ e : linearGroup ≃* Equiv.Perm (Fin 5),
      ∀ g x, g.val (parameters x) = parameters (x ∘ (e g).symm) := by
  sorry

/-- The Thomae group has order 120, Rao–Lakshminarayanan RL-4.12. -/
theorem card_linearGroup : Nat.card linearGroup = 120 := by
  sorry

end DLMF.Hypergeometric.ThomaeCoordinates
