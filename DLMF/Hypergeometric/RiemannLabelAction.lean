/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.GeneralizedHypergeometric.CubeDiagonalAction
public import DLMF.Hypergeometric.Riemann

/-!
# The order-48 action on labelled Riemann exponent pairs

Rao–Lakshminarayanan, *Generalized Hypergeometric Functions* (2018), Chapter 3,
(3.14)–(3.18), pp. 3-6–3-7, synopsis RL-3.04. The existing full cube group
acts faithfully on six exponent labels, preserving their three unordered pairs.
The induced point permutation and within-pair swaps give the stated group of order 48.
-/

@[expose] public noncomputable section

open Equiv

namespace DLMF.Hypergeometric.TransformationGroups

/-- Identify the two exponents at each of three singular points with the opposite-face
pairs `(0,5)`, `(1,4)`, `(2,3)` of the canonical cube group.
Rao–Lakshminarayanan (3.14)–(3.18), synopsis RL-3.04. -/
def riemannFaceLabelEquiv : Fin 3 × Fin 2 ≃ Fin 6 where
  toFun p := ⟨if p.2 = 0 then p.1.val else 5 - p.1.val, by split_ifs <;> omega⟩
  invFun k := if h : k.val < 3 then (⟨k.val, h⟩, 0)
    else (⟨5 - k.val, by omega⟩, 1)
  left_inv := by decide
  right_inv := by decide

/-- The actual permutation of Riemann exponent labels induced by a cube symmetry.
Rao–Lakshminarayanan (3.14)–(3.18), synopsis RL-3.04. -/
def riemannLabelAction (g : cubeSymmetries) : Perm (Fin 3 × Fin 2) :=
  Equiv.permCongr riemannFaceLabelEquiv.symm g.val

/-- The induced singular-point permutation, read from either exponent of the pair.
Rao–Lakshminarayanan (3.14)–(3.18), synopsis RL-3.04. -/
def riemannPointAction (g : cubeSymmetries) (i : Fin 3) : Fin 3 :=
  (riemannLabelAction g (i, 0)).1

/-- The defining conjugate permutation on exponent labels. -/
theorem riemannLabelAction_def (g : cubeSymmetries) :
    riemannLabelAction g = Equiv.permCongr riemannFaceLabelEquiv.symm g.val := rfl

/-- The defining induced action on singular-point labels. -/
theorem riemannPointAction_def (g : cubeSymmetries) (i : Fin 3) :
    riemannPointAction g i = (riemannLabelAction g (i, 0)).1 := rfl

/-- The identity cube symmetry acts trivially on exponent labels. -/
@[simp] theorem riemannLabelAction_one : riemannLabelAction 1 = 1 := by
  apply Equiv.ext
  intro p
  simp [riemannLabelAction]

/-- Multiplication of cube symmetries is composition of their exponent-label actions. -/
theorem riemannLabelAction_mul (g h : cubeSymmetries) :
    riemannLabelAction (g * h) = riemannLabelAction g * riemannLabelAction h := by
  apply Equiv.ext
  intro p
  simp [riemannLabelAction]

/-- The action on all six exponent labels is faithful.
Rao–Lakshminarayanan (3.14)–(3.18), synopsis RL-3.04. -/
theorem injective_riemannLabelAction : Function.Injective riemannLabelAction := by
  intro g h hgh
  apply Subtype.ext
  exact (Equiv.permCongr riemannFaceLabelEquiv.symm).injective hgh

/-- The actual exponent-label action contains exactly 48 transformations.
Rao–Lakshminarayanan (3.14)–(3.18), synopsis RL-3.04. -/
theorem card_range_riemannLabelAction : Nat.card (Set.range riemannLabelAction) = 48 := by
  calc
    _ = Nat.card cubeSymmetries :=
      (Nat.card_congr (Equiv.ofInjective riemannLabelAction injective_riemannLabelAction)).symm
    _ = 48 := card_cubeSymmetries

/-- Exponents at a single singular point remain paired, and the induced point map is a
permutation. Rao–Lakshminarayanan (3.14)–(3.18), synopsis RL-3.04. -/
theorem exists_riemannPointAction_perm (g : cubeSymmetries) :
    ∃ σ : Perm (Fin 3), ∀ i j, (riemannLabelAction g (i, j)).1 = σ i := by
  sorry

/-- Relabelling the three singular points and independently swapping their exponent pairs
leaves the actual Papperitz differential operator unchanged.
Rao–Lakshminarayanan (3.14)–(3.18), synopsis RL-3.04. -/
theorem riemannOperator_labelAction (g : cubeSymmetries) (s : Fin 3 → ℂ)
    (e : Fin 3 × Fin 2 → ℂ) (f : ℂ → ℂ) (z : ℂ) :
    let s' := fun i => s (riemannPointAction g⁻¹ i)
    let e' := fun p => e (riemannLabelAction g⁻¹ p)
    riemannOperator (s' 0) (s' 1) (s' 2)
      (e' (0, 0)) (e' (0, 1)) (e' (1, 0)) (e' (1, 1)) (e' (2, 0)) (e' (2, 1)) f z =
      riemannOperator (s 0) (s 1) (s 2)
        (e (0, 0)) (e (0, 1)) (e (1, 0)) (e (1, 1)) (e (2, 0)) (e (2, 1)) f z := by
  sorry

end DLMF.Hypergeometric.TransformationGroups
