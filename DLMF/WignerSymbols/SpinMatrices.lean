/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.WignerSymbols.Basic.SpinMatrices
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Angular-momentum algebra and the finite-dimensional spin classification

Rao–Lakshminarayanan, *Generalized Hypergeometric Functions* (2018), §5.2,
(5.36)–(5.95), synopses RL-5.03–5.04. Matrix products act on column vectors.
-/

@[expose] public noncomputable section
open Complex Matrix
namespace DLMF.WignerSymbols

/-- The standard raising commutator, Rao–Lakshminarayanan (5.36)–(5.72), RL-5.03. -/
theorem spinZ_mul_spinRaising_sub (N : ℕ) :
    spinZ N * spinRaising N - spinRaising N * spinZ N = spinRaising N := by
  ext i j
  simp only [spinZ, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases h : i.val + 1 = j.val
  · have hj : (j.val : ℂ) = (i.val : ℂ) + 1 := by exact_mod_cast h.symm
    simp only [spinRaising, ite_eq_left h]
    rw [hj]
    ring
  · simp [spinRaising, h]

/-- The normalized ladder commutator, Rao–Lakshminarayanan (5.36)–(5.72), RL-5.03. -/
theorem spinRaising_mul_spinLowering_sub (N : ℕ) :
    spinRaising N * spinLowering N - spinLowering N * spinRaising N = (2 : ℂ) • spinZ N := by
  sorry

/-- The spin Casimir scalar, Rao–Lakshminarayanan (5.36)–(5.72), RL-5.03. -/
theorem sum_spinComponent_sq (N : ℕ) :
    (∑ k : Fin 3, spinComponent N k * spinComponent N k) =
      ((N : ℂ) / 2 * ((N : ℂ) / 2 + 1)) • (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) := by
  sorry

/-- Hermiticity of the Cartesian spin matrices, Rao–Lakshminarayanan §5.2, RL-5.03. -/
theorem isHermitian_spinComponent (N : ℕ) (k : Fin 3) :
    (spinComponent N k).IsHermitian := by
  sorry

/-- Spin one-half has the standard diagonal matrix, Rao–Lakshminarayanan
(5.77)–(5.95), synopsis RL-5.04. -/
theorem spinZ_one : spinZ 1 = !![(1 / 2 : ℂ), 0; 0, -1 / 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [spinZ, Matrix.diagonal]

/-- The spin one-half raising matrix, Rao–Lakshminarayanan (5.77)–(5.95), RL-5.04. -/
theorem spinRaising_one : spinRaising 1 = !![(0 : ℂ), 1; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [spinRaising]

/-- The spin-one raising matrix with its positive `√2` normalization,
Rao–Lakshminarayanan (5.77)–(5.95), synopsis RL-5.04. -/
theorem spinRaising_two : spinRaising 2 =
    !![(0 : ℂ), Real.sqrt 2, 0; 0, 0, Real.sqrt 2; 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [spinRaising]

/-- The Pauli product in cyclic order, Rao–Lakshminarayanan (5.77)–(5.95), RL-5.04. -/
theorem pauli_product_cyclic :
    ((2 : ℂ) • spinX 1) * ((2 : ℂ) • spinY 1) = I • ((2 : ℂ) • spinZ 1) ∧
    ((2 : ℂ) • spinY 1) * ((2 : ℂ) • spinZ 1) = I • ((2 : ℂ) • spinX 1) ∧
    ((2 : ℂ) • spinZ 1) * ((2 : ℂ) • spinX 1) = I • ((2 : ℂ) • spinY 1) := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [spinX, spinY, spinZ, spinLowering, spinRaising, Matrix.mul_apply,
        Fin.sum_univ_succ, Matrix.diagonal] <;> ring_nf
  · constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [spinX, spinY, spinZ, spinLowering, spinRaising, Matrix.mul_apply,
        Fin.sum_univ_succ, Matrix.diagonal] <;> ring_nf <;> norm_num

/-- The Pauli squares, Rao–Lakshminarayanan (5.77)–(5.95), synopsis RL-5.04. -/
theorem pauli_sq (k : Fin 3) : ((2 : ℂ) • spinComponent 1 k) ^ 2 = 1 := by
  fin_cases k <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [spinComponent, spinX, spinY, spinZ, spinLowering, spinRaising,
      pow_two, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.diagonal] <;> ring_nf <;> norm_num

/-- The canonical normalized spin representation is irreducible, completing the
converse classification in Rao–Lakshminarayanan (5.36)–(5.72), synopsis RL-5.03. -/
theorem eq_bot_or_eq_top_of_spinComponent_invariant (N : ℕ)
    (W : Submodule ℂ (Fin (N + 1) → ℂ))
    (hW : ∀ k, ∀ v ∈ W, (spinComponent N k).mulVec v ∈ W) : W = ⊥ ∨ W = ⊤ := by
  sorry

/-- An irreducible nonzero Hermitian angular-momentum triple is unitarily equivalent
to one of the spin matrices. Invariance is required for all three components,
Rao–Lakshminarayanan (5.36)–(5.72), synopsis RL-5.03. -/
theorem exists_unitary_spin_basis (d : ℕ) (hd : 0 < d)
    (A : Fin 3 → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ k, (A k).IsHermitian)
    (hcomm : A 0 * A 1 - A 1 * A 0 = I • A 2 ∧
      A 1 * A 2 - A 2 * A 1 = I • A 0 ∧ A 2 * A 0 - A 0 * A 2 = I • A 1)
    (hirr : ∀ W : Submodule ℂ (Fin d → ℂ),
      (∀ k, ∀ v ∈ W, (A k).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) :
    ∃ N : ℕ, ∃ e : Fin d ≃ Fin (N + 1), ∃ U : Matrix (Fin d) (Fin d) ℂ,
      U.conjTranspose * U = 1 ∧ ∀ k,
        Matrix.reindex e e (U.conjTranspose * A k * U) = spinComponent N k := by
  sorry

end DLMF.WignerSymbols
