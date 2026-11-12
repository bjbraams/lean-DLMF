/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Data.Complex.BigOperators
import Mathlib.Tactic.Ring

/-!
# Trace identities for complexified real matrices

The trace pairing on a complex affine line separates into its real and imaginary parts.
The proof uses Mathlib's matrix multiplication and finite-sum APIs.

* `Matrix.trace_map_ofReal_add_I_smul_mul_map_ofReal`: trace pairing on a complex affine line.
-/

public section
namespace Matrix

/-- The trace pairing on a complex affine line separates into its real and imaginary parts. -/
lemma trace_map_ofReal_add_I_smul_mul_map_ofReal
    {n : Type*} [Fintype n] (U V X : Matrix n n ℝ) :
    ((U.map Complex.ofReal + Complex.I • V.map Complex.ofReal) * X.map Complex.ofReal).trace =
      ((U*X).trace : ℂ) + Complex.I*((V*X).trace : ℂ) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul, Complex.ofReal_sum, Complex.ofReal_mul,
    Finset.sum_add_distrib, Finset.mul_sum, add_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intros
  ring

end Matrix
