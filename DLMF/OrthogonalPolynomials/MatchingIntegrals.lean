/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Basic
public import DLMFMathlib.Combinatorics.SimpleGraph.MatchingPolynomial
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Gaussian Hermite-product integrals and multipartite matchings

Andrews, Askey and Roy, *Special Functions*, Theorem 6.9.4. Both the physicists'
and probabilists' normalizations are connected to the same labeled graph count.
-/

@[expose] public section

open Polynomial MeasureTheory
open scoped Real

noncomputable section

namespace DLMF.OrthogonalPolynomials

/-- A Gaussian product moment of probabilists' Hermite polynomials counts multipartite
perfect matchings. Andrews–Askey–Roy, *Special Functions*, Theorem 6.9.4
(synopsis AAR-6.8.1–6.9.9). -/
theorem integral_prod_hermite_eq_matchingCount {r : ℕ} (blocks : Fin r → ℕ) :
    (∫ x : ℝ, (∏ j, (Polynomial.hermite (blocks j)).eval₂ (Int.castRingHom ℝ) x) *
      Real.exp (-x ^ 2 / 2)) = Real.sqrt (2 * Real.pi) *
        SimpleGraph.completeMultipartitePerfectMatchingCount blocks := by
  sorry

/-- The physicists' normalization of the Gaussian matching integral.
Andrews–Askey–Roy, *Special Functions*, Theorem 6.9.4
(synopsis AAR-6.8.1–6.9.9). -/
theorem integral_prod_hermitePolynomialH_eq_matchingCount {r : ℕ}
    (blocks : Fin r → ℕ) :
    (∫ x : ℝ, (∏ j, (hermitePolynomialH (blocks j)).eval₂ (Int.castRingHom ℝ) x) *
      Real.exp (-x ^ 2)) = (2 : ℝ) ^ (((∑ j, blocks j : ℕ) : ℝ) / 2) *
        Real.sqrt Real.pi * SimpleGraph.completeMultipartitePerfectMatchingCount blocks := by
  sorry

end DLMF.OrthogonalPolynomials
