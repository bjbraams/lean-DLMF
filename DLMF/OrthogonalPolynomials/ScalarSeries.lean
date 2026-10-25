/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Complex.ScalarSeries
public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Analysis.Analytic.OfScalars

/-!
# Scalar power series helpers

Mathlib's uniqueness of formal multilinear series identifies scalar coefficients
from their sums on a disk. Its shifted-series API supplies multiplication by monomials.
-/

@[expose] public section
open Complex Filter
open scoped Nat Topology
noncomputable section
namespace DLMF.OrthogonalPolynomials

/-- Recover a scalar power series from its sums on the unit disk. -/
lemma scalarSeries_unique {c d : ℕ → ℂ} {f : ℂ → ℂ}
    (hc : ∀ z : ℂ, ‖z‖ < 1 → HasSum (fun n => c n * z ^ n) (f z))
    (hd : ∀ z : ℂ, ‖z‖ < 1 → HasSum (fun n => d n * z ^ n) (f z)) : c = d := by
  exact Complex.powerSeries_coefficients_unique hc hd

/-- Multiplication of a power series by a monomial inserts a zero prefix. -/
lemma hasSum_scalar_shift {c : ℕ → ℂ} {z u : ℂ}
    (hc : HasSum (fun n => c n * z ^ n) u) (k : ℕ) :
    HasSum (fun n => (if k ≤ n then c (n - k) else 0) * z ^ n) (z ^ k * u) := by
  apply (hasSum_nat_add_iff' k).mp
  have hzero : ∑ n ∈ Finset.range k, (if k ≤ n then c (n - k) else 0) * z ^ n = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    simp [show ¬k ≤ n by have := Finset.mem_range.mp hn; omega]
  rw [hzero, sub_zero]
  convert hc.mul_left (z ^ k) using 1
  funext n
  simp only [Nat.le_add_left, ↓reduceIte, Nat.add_sub_cancel, pow_add]
  ring

end DLMF.OrthogonalPolynomials
