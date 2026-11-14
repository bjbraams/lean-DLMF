/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Spin matrices with the Condon–Shortley ladder normalization

Rao–Lakshminarayanan, *Generalized Hypergeometric Functions* (2018), §5.2,
(5.36)–(5.95), synopses RL-5.03–5.04. `N=2j` is natural and the basis is
ordered by decreasing magnetic number `m=j,j-1,…,-j`; the units have `ℏ=1`.
-/

@[expose] public noncomputable section
namespace DLMF.WignerSymbols

/-- The `z` component in spin `N/2`, Rao–Lakshminarayanan (5.36)–(5.72), RL-5.03. -/
def spinZ (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  Matrix.diagonal fun i => (N : ℂ) / 2 - i.val

/-- The normalized raising operator in spin `N/2`,
Rao–Lakshminarayanan (5.36)–(5.72), synopsis RL-5.03. -/
def spinRaising (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  fun i j => if i.val + 1 = j.val
    then (Real.sqrt ((j.val : ℝ) * (N + 1 - (j.val : ℝ))) : ℂ) else 0

/-- The lowering operator, the adjoint of raising in the normalized basis,
Rao–Lakshminarayanan (5.36)–(5.72), RL-5.03. -/
def spinLowering (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  (spinRaising N).conjTranspose

/-- The `x` component in spin `N/2`, Rao–Lakshminarayanan (5.77)–(5.95), RL-5.04. -/
def spinX (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  (2 : ℂ)⁻¹ • (spinRaising N + spinLowering N)

/-- The `y` component in spin `N/2`, Rao–Lakshminarayanan (5.77)–(5.95), RL-5.04. -/
def spinY (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  (-(Complex.I / 2)) • (spinRaising N - spinLowering N)

/-- The three Cartesian spin components, Rao–Lakshminarayanan §5.2, RL-5.03/04. -/
def spinComponent (N : ℕ) : Fin 3 → Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  ![spinX N, spinY N, spinZ N]

/-- The diagonal magnetic-number formula, Rao–Lakshminarayanan §5.2. -/
theorem spinZ_def (N : ℕ) : spinZ N =
    Matrix.diagonal (fun i => (N : ℂ) / 2 - i.val) := rfl

/-- The positive square-root raising formula, Rao–Lakshminarayanan §5.2. -/
theorem spinRaising_def (N : ℕ) (i j : Fin (N + 1)) : spinRaising N i j =
    if i.val + 1 = j.val
      then (Real.sqrt ((j.val : ℝ) * (N + 1 - (j.val : ℝ))) : ℂ) else 0 := rfl

/-- The adjoint lowering formula, Rao–Lakshminarayanan §5.2. -/
theorem spinLowering_def (N : ℕ) : spinLowering N = (spinRaising N).conjTranspose := rfl

/-- The Cartesian `x` formula, Rao–Lakshminarayanan §5.2. -/
theorem spinX_def (N : ℕ) : spinX N = (2 : ℂ)⁻¹ • (spinRaising N + spinLowering N) := rfl

/-- The Cartesian `y` formula, Rao–Lakshminarayanan §5.2. -/
theorem spinY_def (N : ℕ) : spinY N =
    (-(Complex.I / 2)) • (spinRaising N - spinLowering N) := rfl

/-- The Cartesian component vector, Rao–Lakshminarayanan §5.2. -/
theorem spinComponent_def (N : ℕ) : spinComponent N = ![spinX N, spinY N, spinZ N] := rfl

end DLMF.WignerSymbols
