/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.NumberTheory.JacobiSum.Basic

/-!
# Multiple Jacobi sums

The many-character Jacobi–Gauss identity of Andrews, Askey and Roy,
*Special Functions*, Theorem 1.10.11. The zero-extension convention is supplied
by Mathlib's `MulChar`, including for the trivial character.
-/

@[expose] public section

open Finset
open scoped Classical

noncomputable section

/-- The multiple Jacobi sum over vectors whose coordinates sum to one.
Andrews–Askey–Roy, *Special Functions*, Theorem 1.10.11
(synopsis AAR-1.10.1–1.10.11). -/
def multipleJacobiSum {F R : Type*} [Field F] [Fintype F] [CommRing R]
    {n : ℕ} (χ : Fin n → MulChar F R) : R :=
  ∑ x : Fin n → F, if ∑ i, x i = 1 then ∏ i, χ i (x i) else 0

/-- The defining constrained character sum. -/
theorem multipleJacobiSum_def {F R : Type*} [Field F] [Fintype F] [CommRing R]
    {n : ℕ} (χ : Fin n → MulChar F R) :
    multipleJacobiSum χ =
      ∑ x : Fin n → F, if ∑ i, x i = 1 then ∏ i, χ i (x i) else 0 := rfl

/-- A multiple Jacobi sum is a quotient of Gauss sums when the product character is
nontrivial. Andrews–Askey–Roy, *Special Functions*, Theorem 1.10.11
(synopsis AAR-1.10.1–1.10.11). The individual characters may be trivial. -/
theorem multipleJacobiSum_eq_prod_gaussSum_div {F K : Type*} [Field F] [Fintype F]
    [Field K] [CharZero K] {n : ℕ} (χ : Fin n → MulChar F K)
    (hχ : (∏ i, χ i) ≠ 1) (ψ : AddChar F K) (hψ : ψ.IsPrimitive) :
    multipleJacobiSum χ = (∏ i, gaussSum (χ i) ψ) / gaussSum (∏ i, χ i) ψ := by
  sorry
