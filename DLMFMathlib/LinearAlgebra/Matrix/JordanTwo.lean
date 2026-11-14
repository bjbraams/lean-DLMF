/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Jordan alternatives for an invertible matrix of order two

The linear-algebra classification used for circuit matrices in Olver,
*Asymptotics and Special Functions*, Chapter 13, §2, pp. 480–482.
Mathlib supplies generalized eigenspace decomposition and TauCeti supplies
nilpotent Jordan-chain bases; the statement below records the explicit
order-two matrix alternatives.
-/

@[expose] public section
namespace Matrix

/-- An invertible matrix of order two over an algebraically closed field is similar
either to a diagonal matrix with two nonzero eigenvalues, or to one nontrivial normalized Jordan
block. Olver, Chapter 13, §2, pp. 480–482. -/
theorem exists_jordan_two_of_det_ne_zero {K : Type*} [Field K] [IsAlgClosed K]
    {C : Matrix (Fin 2) (Fin 2) K}
    (hC : C.det ≠ 0) :
    ∃ B : Matrix (Fin 2) (Fin 2) K, ∃ eigenvalue₁ eigenvalue₂ κ : K,
      B.det ≠ 0 ∧ eigenvalue₁ ≠ 0 ∧ eigenvalue₂ ≠ 0 ∧
        (κ = 0 ∨ (eigenvalue₁ = eigenvalue₂ ∧ κ = 1)) ∧
        C = B * !![eigenvalue₁, κ; 0, eigenvalue₂] * B⁻¹ := by
  sorry

end Matrix
