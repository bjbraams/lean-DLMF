/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.WignerSymbols.Basic
public import Mathlib.Algebra.Group.Subgroup.Basic
public import DLMF.GeneralizedHypergeometric.Basic
public import Mathlib.GroupTheory.Perm.Sign

/-!
# Balanced Regge arrays and their complete permutation action

Rao–Lakshminarayanan, *Generalized Hypergeometric Functions* (2018),
§5.2, (5.131)–(5.135), pp. 5-19–5-20, synopsis RL-5.08.
Nonnegative arrays with a common row and column sum reconstruct admissible spins.
Row permutations, column permutations and transposition act on nine positions.
-/

@[expose] public noncomputable section
open Finset
namespace DLMF.WignerSymbols.ReggeArrays

/-- The common-sum condition on a nonnegative Regge array, Rao–Lakshminarayanan
(5.131)–(5.135), synopsis RL-5.08. -/
def IsBalanced (R : Matrix (Fin 3) (Fin 3) ℕ) (J : ℕ) : Prop :=
  (∀ i, ∑ j, R i j = J) ∧ ∀ j, ∑ i, R i j = J

/-- The row-sum and column-sum definition of balance. -/
theorem isBalanced_iff (R : Matrix (Fin 3) (Fin 3) ℕ) (J : ℕ) :
    IsBalanced R J ↔ (∀ i, ∑ j, R i j = J) ∧ ∀ j, ∑ i, R i j = J := Iff.rfl

/-- The reconstructed spin in a column, Rao–Lakshminarayanan RL-5.08. -/
def spin (R : Matrix (Fin 3) (Fin 3) ℕ) (J : ℕ) (j : Fin 3) : ℚ :=
  ((J : ℚ) - R 0 j) / 2

/-- The reconstructed magnetic projection, Rao–Lakshminarayanan RL-5.08. -/
def projection (R : Matrix (Fin 3) (Fin 3) ℕ) (j : Fin 3) : ℚ :=
  ((R 2 j : ℚ) - R 1 j) / 2

/-- The symbol reconstructed from a balanced Regge array,
Rao–Lakshminarayanan RL-5.08. -/
def symbol (R : Matrix (Fin 3) (Fin 3) ℕ) (J : ℕ) : ℝ :=
  wigner3j (spin R J 0) (spin R J 1) (spin R J 2)
    (projection R 0) (projection R 1) (projection R 2)

/-- The spin reconstruction formula. -/
theorem spin_def (R : Matrix (Fin 3) (Fin 3) ℕ) (J : ℕ) (j : Fin 3) :
    spin R J j = ((J : ℚ) - R 0 j) / 2 := rfl

/-- The projection reconstruction formula. -/
theorem projection_def (R : Matrix (Fin 3) (Fin 3) ℕ) (j : Fin 3) :
    projection R j = ((R 2 j : ℚ) - R 1 j) / 2 := rfl

/-- The symbol reconstruction formula. -/
theorem symbol_def (R : Matrix (Fin 3) (Fin 3) ℕ) (J : ℕ) :
    symbol R J = wigner3j (spin R J 0) (spin R J 1) (spin R J 2)
      (projection R 0) (projection R 1) (projection R 2) := rfl

/-- A balanced nonnegative array reconstructs admissible spins and projections,
Rao–Lakshminarayanan (5.131)–(5.135), synopsis RL-5.08. -/
theorem isAdmissible3j_of_isBalanced {R : Matrix (Fin 3) (Fin 3) ℕ} {J : ℕ}
    (hR : IsBalanced R J) :
    IsAdmissible3j (spin R J 0) (spin R J 1) (spin R J 2)
      (projection R 0) (projection R 1) (projection R 2) := by
  sorry

/-- The complete row/column symmetry with its parity phase,
Rao–Lakshminarayanan (5.131)–(5.135), synopsis RL-5.08. -/
theorem symbol_row_column_perm {R : Matrix (Fin 3) (Fin 3) ℕ} {J : ℕ}
    (hR : IsBalanced R J) (p q : Equiv.Perm (Fin 3)) :
    symbol (fun i j => R (p i) (q j)) J =
      (if p.sign = 1 then 1 else (-1 : ℝ) ^ J) *
      (if q.sign = 1 then 1 else (-1 : ℝ) ^ J) * symbol R J := by
  sorry

/-- Transposition has positive phase, Rao–Lakshminarayanan (5.131)–(5.135),
synopsis RL-5.08. -/
theorem symbol_transpose {R : Matrix (Fin 3) (Fin 3) ℕ} {J : ℕ}
    (hR : IsBalanced R J) : symbol R.transpose J = symbol R J := by
  sorry

/-- All six finite factorial forms with their phases, indexed by a column permutation,
Rao–Lakshminarayanan (5.134)–(5.135), synopsis RL-5.09. The canonical finite
Racah sum uses reciprocal factorials, which vanish outside the admissible support. -/
theorem symbol_eq_symmetricRacahSum {R : Matrix (Fin 3) (Fin 3) ℕ} {J : ℕ}
    (hR : IsBalanced R J) (p : Equiv.Perm (Fin 3)) :
    symbol R J =
      signPow ((R 2 (p 0) : ℚ) - R 1 (p 1) +
        if p.sign = 1 then 0 else (J : ℚ)) *
      Real.sqrt ((∏ i : Fin 3, ∏ j : Fin 3, ((R i j).factorial : ℝ)) /
        (J + 1).factorial) *
      symmetricRacahSum (R 1 (p 0)) (R 2 (p 1)) (R 0 (p 2)) 0
        ((R 1 (p 0) : ℚ) - R 2 (p 2))
        ((R 2 (p 1) : ℚ) - R 1 (p 2)) := by
  sorry

/-- The six finite `₃F₂` forms on their ordinary regular locus,
Rao–Lakshminarayanan (5.136)–(5.141), synopsis RL-5.10. The inequalities
make the two lower parameters positive integers; other cases use the factorial
formula rather than a singular unnormalized series. -/
theorem symbol_eq_threeFTwo {R : Matrix (Fin 3) (Fin 3) ℕ} {J : ℕ}
    (hR : IsBalanced R J) (p : Equiv.Perm (Fin 3))
    (hD : R 1 (p 0) ≤ R 2 (p 2)) (hE : R 2 (p 1) ≤ R 1 (p 2)) :
    let N := min (min (R 1 (p 0)) (R 2 (p 1))) (R 0 (p 2))
    let D : ℂ := 1 + (R 2 (p 2) : ℂ) - R 1 (p 0)
    let E : ℂ := 1 + (R 1 (p 2) : ℂ) - R 2 (p 1)
    symbol R J =
      signPow ((R 2 (p 0) : ℚ) - R 1 (p 1) +
        if p.sign = 1 then 0 else (J : ℚ)) *
      Real.sqrt ((∏ i : Fin 3, ∏ j : Fin 3, ((R i j).factorial : ℝ)) /
        (J + 1).factorial) *
      (DLMF.Hypergeometric.generalizedHypergeometricTruncated N
        {-(R 1 (p 0) : ℂ), -(R 2 (p 1) : ℂ), -(R 0 (p 2) : ℂ)} {D, E} 1 /
        ((R 1 (p 0)).factorial * (R 2 (p 1)).factorial * (R 0 (p 2)).factorial *
          Complex.Gamma D * Complex.Gamma E)).re := by
  sorry

/-- The actual permutation group on the nine array positions, generated by independent
row/column permutations and transposition. Rao–Lakshminarayanan RL-5.08 and RL-7.06. -/
def arrayGroup : Subgroup (Equiv.Perm (Fin 3 × Fin 3)) :=
  Subgroup.closure
    (Set.range (fun p : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3) =>
      Equiv.prodCongr p.1 p.2) ∪ {Equiv.prodComm (Fin 3) (Fin 3)})

/-- The generating description of the array symmetry group. -/
theorem arrayGroup_def : arrayGroup = Subgroup.closure
    (Set.range (fun p : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3) =>
      Equiv.prodCongr p.1 p.2) ∪ {Equiv.prodComm (Fin 3) (Fin 3)}) := rfl

/-- The array action has order 72, Rao–Lakshminarayanan RL-5.08 and RL-7.06. -/
theorem card_arrayGroup : Nat.card arrayGroup = 72 := by
  sorry

end DLMF.WignerSymbols.ReggeArrays
