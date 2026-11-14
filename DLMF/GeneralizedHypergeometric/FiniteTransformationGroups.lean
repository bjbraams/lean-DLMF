/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.GroupTheory.Coset.Card

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.Group.ConjFinite
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Perm.List
public import Mathlib.RepresentationTheory.Character

/-!
# Finite groups of hypergeometric parameter transformations

Rao–Lakshminarayanan, *Generalized Hypergeometric Functions* (2018), Chapter 3
and §4.2. Cube symmetries act on six faces; the terminating `₃F₂` group is
realized by the book's signed permutations on six Whipple coordinates.
-/

@[expose] public noncomputable section
open Equiv
namespace DLMF.Hypergeometric.TransformationGroups

/-- The two face permutations generating cube rotations, Rao–Lakshminarayanan
(3.6)–(3.7), synopsis RL-3.01. Faces `1,…,6` are encoded by `0,…,5`. -/
def cubeGenerator (i : Fin 2) : Perm (Fin 6) :=
  if i = 0 then ([1, 3, 4, 2] : List (Fin 6)).formPerm
  else ([0, 1, 5, 4] : List (Fin 6)).formPerm

/-- The orientation-preserving cube group in RL-3.01. -/
def cubeRotations : Subgroup (Perm (Fin 6)) :=
  Subgroup.closure (Set.range cubeGenerator)

/-- The full cube group, adding reflection in the third coordinate, RL-3.01. -/
def cubeSymmetries : Subgroup (Perm (Fin 6)) :=
  Subgroup.closure (Set.range cubeGenerator ∪ {Equiv.swap 2 3})

/-- The face generator formula, Rao–Lakshminarayanan (3.6)–(3.7). -/
theorem cubeGenerator_def (i : Fin 2) : cubeGenerator i =
    if i = 0 then ([1, 3, 4, 2] : List (Fin 6)).formPerm
    else ([0, 1, 5, 4] : List (Fin 6)).formPerm := rfl

/-- The generating subgroup for cube rotations, Rao–Lakshminarayanan (3.6)–(3.7). -/
theorem cubeRotations_def : cubeRotations = Subgroup.closure (Set.range cubeGenerator) := rfl

/-- The generating subgroup for all cube symmetries, Rao–Lakshminarayanan (3.6)–(3.7). -/
theorem cubeSymmetries_def : cubeSymmetries =
    Subgroup.closure (Set.range cubeGenerator ∪ {Equiv.swap 2 3}) := rfl

/-- The cube rotation group has order 24, Rao–Lakshminarayanan (3.6)–(3.7), RL-3.01. -/
theorem card_cubeRotations : Nat.card cubeRotations = 24 := by
  sorry

/-- The diagonal action identifies cube rotations with `S₄`,
Rao–Lakshminarayanan (3.6)–(3.7), synopsis RL-3.01. -/
theorem nonempty_cubeRotations_mulEquiv_perm_four :
    Nonempty (cubeRotations ≃* Perm (Fin 4)) := by
  sorry

/-- Full cube symmetries have order 48, Rao–Lakshminarayanan (3.6)–(3.7), RL-3.01. -/
theorem card_cubeSymmetries : Nat.card cubeSymmetries = 48 := by
  sorry

/-- The three signed generators on Whipple's six coordinates,
Rao–Lakshminarayanan (4.57)–(4.69), synopsis RL-4.07. The second component
is the additive sign exponent modulo two, regarded multiplicatively. -/
def terminatingGenerator (i : Fin 3) : Perm (Fin 6) × Multiplicative (ZMod 2) :=
  if i = 0 then
    (Equiv.swap 0 5 * Equiv.swap 1 3 * Equiv.swap 2 4, Multiplicative.ofAdd 1)
  else if i = 1 then (Equiv.swap 1 2, 1) else (Equiv.swap 4 5, 1)

/-- The signed-permutation group of terminating `₃F₂` transformations,
Rao–Lakshminarayanan (4.57)–(4.69), synopsis RL-4.07. -/
def terminatingGroup : Subgroup (Perm (Fin 6) × Multiplicative (ZMod 2)) :=
  Subgroup.closure (Set.range terminatingGenerator)

/-- The explicit signed generators of RL-4.07. -/
theorem terminatingGenerator_def (i : Fin 3) : terminatingGenerator i =
    if i = 0 then
      (Equiv.swap 0 5 * Equiv.swap 1 3 * Equiv.swap 2 4, Multiplicative.ofAdd 1)
    else if i = 1 then (Equiv.swap 1 2, 1) else (Equiv.swap 4 5, 1) := rfl

/-- The generated subgroup in RL-4.07. -/
theorem terminatingGroup_def : terminatingGroup =
    Subgroup.closure (Set.range terminatingGenerator) := rfl

/-- Each terminating generator has square one, Rao–Lakshminarayanan
(4.57)–(4.69), synopsis RL-4.07. -/
theorem terminatingGenerator_sq (i : Fin 3) : terminatingGenerator i ^ 2 = 1 := by
  sorry

/-- Order 72 of the signed transformation group, Rao–Lakshminarayanan
(4.57)–(4.69), synopsis RL-4.07. -/
theorem card_terminatingGroup : Nat.card terminatingGroup = 72 := by
  sorry

/-- The nine printed conjugacy representatives, Rao–Lakshminarayanan p. 4-12,
synopsis RL-4.08. The signs are encoded by the second coordinate. -/
def terminatingClassRepresentative : Fin 9 → Perm (Fin 6) × Multiplicative (ZMod 2) :=
  ![(1, 1), (([3, 4, 5] : List (Fin 6)).formPerm, 1),
    (([0, 1, 2] : List (Fin 6)).formPerm * ([3, 4, 5] : List (Fin 6)).formPerm, 1),
    (Equiv.swap 0 5 * Equiv.swap 1 3 * Equiv.swap 2 4, Multiplicative.ofAdd 1),
    (Equiv.swap 1 2, 1), (Equiv.swap 1 2 * Equiv.swap 4 5, 1),
    (([0, 5, 1, 3, 2, 4] : List (Fin 6)).formPerm, Multiplicative.ofAdd 1),
    (([0, 2, 1] : List (Fin 6)).formPerm * Equiv.swap 3 4, 1),
    (Equiv.swap 0 5 * ([1, 4, 2, 3] : List (Fin 6)).formPerm, Multiplicative.ofAdd 1)]

/-- The nine class sizes, Rao–Lakshminarayanan p. 4-12, RL-4.08. -/
def terminatingClassSize : Fin 9 → ℕ := ![1, 4, 4, 6, 6, 9, 12, 12, 18]

/-- The element orders in the same class order, Rao–Lakshminarayanan p. 4-12, RL-4.08. -/
def terminatingClassOrder : Fin 9 → ℕ := ![1, 3, 3, 2, 2, 2, 6, 6, 4]

/-- The irreducible dimensions, Rao–Lakshminarayanan p. 4-12, RL-4.08. -/
def terminatingIrreducibleDimension : Fin 9 → ℕ := ![1, 1, 1, 1, 2, 4, 4, 4, 4]

/-- The full irreducible character table in the printed class order,
Rao–Lakshminarayanan p. 4-12, synopsis RL-4.08. -/
def terminatingCharacterTable : Fin 9 → Fin 9 → ℤ :=
  ![![1, 1, 1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, -1, 1, 1, -1, 1, -1],
    ![1, 1, 1, 1, -1, 1, 1, -1, -1], ![1, 1, 1, -1, -1, 1, -1, -1, 1],
    ![2, 2, 2, 0, 0, -2, 0, 0, 0], ![4, 1, -2, 0, 2, 0, 0, -1, 0],
    ![4, 1, -2, 0, -2, 0, 0, 1, 0], ![4, -2, 1, 2, 0, 0, -1, 0, 0],
    ![4, -2, 1, -2, 0, 0, 1, 0, 0]]

/-- The nine specified representatives exhaust conjugacy classes with the printed
sizes and orders, Rao–Lakshminarayanan p. 4-12, synopsis RL-4.08. -/
theorem exists_terminating_conjugacy_classes :
    ∃ r : Fin 9 → terminatingGroup,
      (∀ i, (r i).val = terminatingClassRepresentative i) ∧
      Function.Bijective (fun i => ConjClasses.mk (r i)) ∧
      (∀ i, Nat.card (ConjClasses.carrier (ConjClasses.mk (r i))) = terminatingClassSize i) ∧
      ∀ i, orderOf (r i) = terminatingClassOrder i := by
  sorry

/-- All nine character rows are realized by irreducible complex representations;
the four four-dimensional ones are faithful, Rao–Lakshminarayanan p. 4-12, RL-4.08. -/
theorem exists_terminating_irreducible_characters :
    ∃ r : Fin 9 → terminatingGroup,
      (∀ j, (r j).val = terminatingClassRepresentative j) ∧
      ∃ ρ : (i : Fin 9) → Representation ℂ terminatingGroup
          (Fin (terminatingIrreducibleDimension i) → ℂ),
        (∀ i, Representation.IsIrreducible (ρ i)) ∧
        (∀ i j, (ρ i).character (r j) = (terminatingCharacterTable i j : ℂ)) ∧
        ∀ i, 5 ≤ i.val → Function.Injective (ρ i) := by
  sorry

/-- The subgroup generated by the two independent upper/lower parameter swaps,
Rao–Lakshminarayanan (4.18)–(4.35), synopsis RL-4.03. -/
def terminatingParameterPermutations : Subgroup terminatingGroup :=
  Subgroup.closure {g | g.val = terminatingGenerator 1 ∨ g.val = terminatingGenerator 2}

/-- The defining two-swap subgroup, Rao–Lakshminarayanan RL-4.03. -/
theorem terminatingParameterPermutations_def : terminatingParameterPermutations =
    Subgroup.closure {g | g.val = terminatingGenerator 1 ∨ g.val = terminatingGenerator 2} := rfl

/-- The two independent parameter permutations form a subgroup of order four,
Rao–Lakshminarayanan (4.18)–(4.35), synopsis RL-4.03. -/
theorem card_terminatingParameterPermutations :
    Nat.card terminatingParameterPermutations = 4 := by
  sorry

/-- The eighteen transformation forms are the cosets modulo the two parameter swaps,
Rao–Lakshminarayanan (4.18)–(4.35), synopsis RL-4.03. The quotient is a coset type;
normality of the parameter-swap subgroup is not required. -/
theorem card_terminating_parameter_forms :
    Nat.card (terminatingGroup ⧸ terminatingParameterPermutations) = 18 := by
  sorry

/-- The five nontrivial proper normal subgroups as unions of the numbered classes,
Rao–Lakshminarayanan (4.72)–(4.89), RL-4.09. Class labels use zero-based indexing. -/
def terminatingNormalClasses : Fin 5 → Finset (Fin 9) :=
  ![{0, 1, 2}, {0, 1, 2, 5}, {0, 1, 2, 5, 8}, {0, 1, 2, 5, 3, 6}, {0, 1, 2, 5, 4, 7}]

/-- The explicit normal-subgroup class unions, Rao–Lakshminarayanan RL-4.09. -/
theorem terminatingNormalClasses_def : terminatingNormalClasses =
    ![{0, 1, 2}, {0, 1, 2, 5}, {0, 1, 2, 5, 8}, {0, 1, 2, 5, 3, 6}, {0, 1, 2, 5, 4, 7}] := rfl

/-- Exactly five proper nontrivial normal subgroups occur, with orders
`9,18,36,36,36`, Rao–Lakshminarayanan (4.72)–(4.89), synopsis RL-4.09. -/
theorem exists_terminating_normal_subgroups :
    ∃ H : Fin 5 → Subgroup terminatingGroup,
      Function.Injective H ∧
      (∀ i g, g ∈ H i ↔ ∃ j ∈ terminatingNormalClasses i,
        IsConj g.val (terminatingClassRepresentative j)) ∧
      (∀ i, (H i).Normal ∧ Nat.card (H i) = (![9, 18, 36, 36, 36] : Fin 5 → ℕ) i) ∧
      Nonempty (H 0 ≃* Multiplicative (ZMod 3 × ZMod 3)) ∧
      ∀ K : Subgroup terminatingGroup, K.Normal → K ≠ ⊥ → K ≠ ⊤ → ∃ i, K = H i := by
  sorry

/-- The explicit finite data for the terminating group,
Rao–Lakshminarayanan p. 4-12, synopsis RL-4.08. -/
theorem terminatingClassRepresentative_def : terminatingClassRepresentative =
  ![(1, 1), (([3, 4, 5] : List (Fin 6)).formPerm, 1),
    (([0, 1, 2] : List (Fin 6)).formPerm * ([3, 4, 5] : List (Fin 6)).formPerm, 1),
    (Equiv.swap 0 5 * Equiv.swap 1 3 * Equiv.swap 2 4, Multiplicative.ofAdd 1),
    (Equiv.swap 1 2, 1), (Equiv.swap 1 2 * Equiv.swap 4 5, 1),
    (([0, 5, 1, 3, 2, 4] : List (Fin 6)).formPerm, Multiplicative.ofAdd 1),
    (([0, 2, 1] : List (Fin 6)).formPerm * Equiv.swap 3 4, 1),
    (Equiv.swap 0 5 * ([1, 4, 2, 3] : List (Fin 6)).formPerm, Multiplicative.ofAdd 1)] := rfl

/-- The explicit finite data for the terminating group,
Rao–Lakshminarayanan p. 4-12, synopsis RL-4.08. -/
theorem terminatingClassSize_def : terminatingClassSize =
  ![1, 4, 4, 6, 6, 9, 12, 12, 18] := rfl

/-- The explicit finite data for the terminating group,
Rao–Lakshminarayanan p. 4-12, synopsis RL-4.08. -/
theorem terminatingClassOrder_def : terminatingClassOrder =
  ![1, 3, 3, 2, 2, 2, 6, 6, 4] := rfl

/-- The explicit finite data for the terminating group,
Rao–Lakshminarayanan p. 4-12, synopsis RL-4.08. -/
theorem terminatingIrreducibleDimension_def : terminatingIrreducibleDimension =
  ![1, 1, 1, 1, 2, 4, 4, 4, 4] := rfl

/-- The explicit finite data for the terminating group,
Rao–Lakshminarayanan p. 4-12, synopsis RL-4.08. -/
theorem terminatingCharacterTable_def : terminatingCharacterTable =
  ![![1, 1, 1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, -1, 1, 1, -1, 1, -1],
    ![1, 1, 1, 1, -1, 1, 1, -1, -1], ![1, 1, 1, -1, -1, 1, -1, -1, 1],
    ![2, 2, 2, 0, 0, -2, 0, 0, 0], ![4, 1, -2, 0, 2, 0, 0, -1, 0],
    ![4, 1, -2, 0, -2, 0, 0, 1, 0], ![4, -2, 1, 2, 0, 0, -1, 0, 0],
    ![4, -2, 1, -2, 0, 0, 1, 0, 0]] := rfl

end DLMF.Hypergeometric.TransformationGroups
