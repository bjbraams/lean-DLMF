/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.WignerSymbols.Basic
public import DLMF.WignerSymbols.Basic.SpinMatrices
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.Data.Matrix.Block

/-!
# The Clebsch–Gordan change of basis for normalized spin matrices

Rao–Lakshminarayanan, *Generalized Hypergeometric Functions* (2018),
§5.4, (5.112)–(5.122), synopsis RL-5.06. The rectangular coefficient matrix
identifies the product magnetic basis with the direct sum of every allowed spin.
-/

@[expose] public noncomputable section
namespace DLMF.WignerSymbols.SpinCoupling

/-- Twice the coupled spin, with `k=0,…,min(N₁,N₂)`,
Rao–Lakshminarayanan (5.112)–(5.122), synopsis RL-5.06. -/
def degree (N₁ N₂ k : ℕ) : ℕ := N₁ + N₂ - 2 * k

/-- The allowed total-spin blocks and their magnetic coordinates,
Rao–Lakshminarayanan (5.112)–(5.122), synopsis RL-5.06. -/
abbrev CoupledIndex (N₁ N₂ : ℕ) :=
  Σ k : Fin (min N₁ N₂ + 1), Fin (degree N₁ N₂ k.val + 1)

/-- The explicit allowed doubled-spin degree, RL-5.06. -/
theorem degree_def (N₁ N₂ k : ℕ) : degree N₁ N₂ k = N₁ + N₂ - 2 * k := rfl

/-- The Clebsch–Gordan change-of-basis matrix in decreasing magnetic order,
Rao–Lakshminarayanan (5.112)–(5.122), synopsis RL-5.06. -/
def coefficientMatrix (N₁ N₂ : ℕ) :
    Matrix (Fin (N₁ + 1) × Fin (N₂ + 1)) (CoupledIndex N₁ N₂) ℂ :=
  fun p q => (clebschGordan ((N₁ : ℚ) / 2) ((N₁ : ℚ) / 2 - p.1.val)
    ((N₂ : ℚ) / 2) ((N₂ : ℚ) / 2 - p.2.val)
    ((degree N₁ N₂ q.1.val : ℚ) / 2)
    ((degree N₁ N₂ q.1.val : ℚ) / 2 - q.2.val) : ℂ)

/-- The explicit Clebsch–Gordan entries in the product magnetic basis, RL-5.06. -/
theorem coefficientMatrix_def (N₁ N₂ : ℕ)
    (p : Fin (N₁ + 1) × Fin (N₂ + 1)) (q : CoupledIndex N₁ N₂) :
    coefficientMatrix N₁ N₂ p q =
      (clebschGordan ((N₁ : ℚ) / 2) ((N₁ : ℚ) / 2 - p.1.val)
        ((N₂ : ℚ) / 2) ((N₂ : ℚ) / 2 - p.2.val)
        ((degree N₁ N₂ q.1.val : ℚ) / 2)
        ((degree N₁ N₂ q.1.val : ℚ) / 2 - q.2.val) : ℂ) := rfl

/-- The coupled spin blocks exhaust the dimension of the product,
Rao–Lakshminarayanan (5.112)–(5.122), synopsis RL-5.06. -/
theorem card_coupledIndex (N₁ N₂ : ℕ) :
    Fintype.card (CoupledIndex N₁ N₂) = (N₁ + 1) * (N₂ + 1) := by
  sorry

/-- Orthogonality and completeness of all Clebsch–Gordan coefficients,
Rao–Lakshminarayanan (5.112)–(5.122), synopsis RL-5.06. -/
theorem coefficientMatrix_unitary (N₁ N₂ : ℕ) :
    (coefficientMatrix N₁ N₂).conjTranspose * coefficientMatrix N₁ N₂ = 1 ∧
      coefficientMatrix N₁ N₂ * (coefficientMatrix N₁ N₂).conjTranspose = 1 := by
  sorry

/-- The coefficient matrix intertwines total product angular momentum with each coupled
spin block, Rao–Lakshminarayanan (5.112)–(5.122), synopsis RL-5.06.
Together with unitarity this is the normalized direct-sum decomposition. -/
theorem coefficientMatrix_intertwines_spinComponent (N₁ N₂ : ℕ) (a : Fin 3) :
    (Matrix.kronecker (spinComponent N₁ a) 1 +
      Matrix.kronecker 1 (spinComponent N₂ a)) * coefficientMatrix N₁ N₂ =
      coefficientMatrix N₁ N₂ *
        Matrix.blockDiagonal' (fun k : Fin (min N₁ N₂ + 1) =>
          spinComponent (degree N₁ N₂ k.val) a) := by
  sorry

end DLMF.WignerSymbols.SpinCoupling
