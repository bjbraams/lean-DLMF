/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Basic.NormsAndKernels
import Mathlib.Tactic.FieldSimp

/-!
# Positive diagonal kernels and products of squared-norm ratios

Andrews, Askey and Roy, *Special Functions*, Theorem 5.2.5 and Corollary 5.2.3
(synopsis AAR-5.2.2–5.2.6). Both statements follow directly from positive norms.
-/

@[expose] public noncomputable section
open Polynomial MeasureTheory
namespace DLMF.OrthogonalPolynomials

/-- The diagonal Christoffel–Darboux kernel is strictly positive, including degree zero.
Andrews–Askey–Roy, Theorem 5.2.5. -/
theorem christoffelDarbouxKernel_diag_pos {mu : Measure ℝ} {p : ℕ → ℝ[X]}
    (h : IsOrthogonalPolynomials mu p) (n : ℕ) (x : ℝ) :
    0 < christoffelDarbouxKernel mu p n x x := by
  unfold christoffelDarbouxKernel
  rw [Finset.sum_range_succ']
  refine add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun k _ =>
    div_nonneg (mul_self_nonneg _) (h.2.2.1 _).le) (div_pos ?_ (h.2.2.1 0))
  have hpzero : p 0 = C ((p 0).coeff 0) := eq_C_of_natDegree_eq_zero (h.1 0)
  have hc : (p 0).coeff 0 ≠ 0 := fun hc => h.ne_zero 0 (by rw [hpzero, hc, C_0])
  rw [hpzero, eval_C]
  exact mul_self_pos.2 hc

/-- Multiplication of successive squared-norm ratios telescopes to the norm.
Andrews–Askey–Roy, Corollary 5.2.3; together with `monic_squaredNorm_ratio`
this is the product of the monic recurrence coefficients. -/
theorem squaredNorm_eq_mul_prod_ratio {mu : Measure ℝ} {p : ℕ → ℝ[X]}
    (h : IsOrthogonalPolynomials mu p) (n : ℕ) :
    squaredNorm mu p n = squaredNorm mu p 0 *
      ∏ j ∈ Finset.range n, squaredNorm mu p (j + 1) / squaredNorm mu p j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ← mul_assoc, ← ih]
    exact (mul_div_cancel₀ _ (h.2.2.1 n).ne').symm

end DLMF.OrthogonalPolynomials
