/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Basic.Complex.Basic

/-!
# Normalized binary-polynomial matrix coefficients

Andrews, Askey and Roy, *Special Functions*, §§9.13–9.15. The basis monomial
`x₁^(N-j)x₂^j` has squared norm `(N-j)!j!`. The formula uses no square-root or
Euler-angle phase convention beyond the positive real factorial normalization.
-/

@[expose] public section

noncomputable section

namespace DLMF.SphericalHarmonics

/-- Matrix of substitution by `gᵀ` on homogeneous binary polynomials of degree `N`,
in the monomial basis normalized by `√((N-j)!j!)`. Andrews–Askey–Roy,
*Special Functions*, §9.14, pp. 472–475 (synopsis AAR-9.11–9.16). -/
def suTwoPolynomialMatrix (N : ℕ) (g : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ := fun j k =>
  (Real.sqrt (((N - j.val).factorial : ℝ) * j.val.factorial /
    ((N - k.val).factorial * k.val.factorial)) : ℂ) *
      ∑ r ∈ Finset.Icc (j.val - k.val) (min j.val (N - k.val)),
        ((N - k.val).choose r : ℂ) * (k.val.choose (j.val - r) : ℂ) *
          g 0 0 ^ (N - k.val - r) * g 1 0 ^ r *
          g 0 1 ^ (k.val + r - j.val) * g 1 1 ^ (j.val - r)

/-- Explicit normalized binary-polynomial matrix entries. -/
theorem suTwoPolynomialMatrix_apply (N : ℕ) (g : Matrix (Fin 2) (Fin 2) ℂ)
    (j k : Fin (N + 1)) :
    suTwoPolynomialMatrix N g j k =
      (Real.sqrt (((N - j.val).factorial : ℝ) * j.val.factorial /
        ((N - k.val).factorial * k.val.factorial)) : ℂ) *
          ∑ r ∈ Finset.Icc (j.val - k.val) (min j.val (N - k.val)),
            ((N - k.val).choose r : ℂ) * (k.val.choose (j.val - r) : ℂ) *
              g 0 0 ^ (N - k.val - r) * g 1 0 ^ r *
              g 0 1 ^ (k.val + r - j.val) * g 1 1 ^ (j.val - r) := rfl

end DLMF.SphericalHarmonics
