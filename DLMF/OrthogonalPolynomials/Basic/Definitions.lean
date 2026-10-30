/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Core.Framework
public import DLMF.Hypergeometric.Basic.GaussCoefficients
public import DLMF.Confluent.Basic.KummerM
public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.RingTheory.Polynomial.Chebyshev
public import Mathlib.RingTheory.Polynomial.Hermite.Basic
public import Mathlib.RingTheory.Polynomial.ShiftedLegendre
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.SpecialFunctions.Bernstein

/-!
# Canonical classical orthogonal polynomial families
-/

@[expose] public noncomputable section

open Complex Filter Set Polynomial
open scoped Real Nat Topology ENNReal Interval
open DLMF.Hypergeometric
open MeasureTheory intervalIntegral DLMF.Confluent

namespace DLMF.OrthogonalPolynomials

/-- Physicists' Hermite polynomials, AAR §6.1: `H_{n+1} = 2x H_n - H_n'`. -/
def hermitePolyH : ℕ → ℤ[X]
  | 0 => 1
  | n + 1 => 2 * X * hermitePolyH n - derivative (hermitePolyH n)

/-- Hypergeometric realization of generalized Laguerre polynomials, AAR §6.2,
for `α + 1` not a nonpositive integer:
`L_n^{(α)}(x) = (α+1)_n / n! · ₁F₁(-n; α+1; x)`. -/
@[dlmf 18.5.E12]
def laguerrePolyL (α : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  poch (α + 1) n / n ! * kummerM (-n : ℂ) (α + 1) x

/-- Hypergeometric realization of Jacobi polynomials, AAR §6.3,
for `α + 1` not a nonpositive integer:
`P_n^{(α,β)}(x) = (α+1)_n / n! · ₂F₁(-n, n+α+β+1; α+1; (1-x)/2)`. -/
@[dlmf 18.5.E7]
def jacobiPolyP (α β : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  poch (α + 1) n / n ! * ₂F₁ (-n : ℂ) (n + α + β + 1) (α + 1) ((1 - x) / 2)

/-- Legendre polynomials as Jacobi polynomials with `α = β = 0`. -/
@[dlmf 18.7.E9]
def legendrePolyP (n : ℕ) (x : ℂ) : ℂ :=
  jacobiPolyP 0 0 n x

/-- Hypergeometric realization of Gegenbauer polynomials, AAR §6.11,
for `λ + 1/2` not a nonpositive integer:
`C_n^{(λ)}(x) = (2λ)_n / n! · ₂F₁(-n, n+2λ; λ+1/2; (1-x)/2)`. -/
@[dlmf 18.5.E9]
def ultrasphPoly (lam : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  poch (2 * lam) n / n ! * ₂F₁ (-n : ℂ) (n + 2 * lam) (lam + 1 / 2) ((1 - x) / 2)

/-- Helper lemma for `eval_U_eq_ultrasphPoly`. Closed form of the coefficients of `C_n^{(1)}`. -/
def gegenbauerB (n k : ℕ) : ℂ :=
  if k ≤ n then
    (-1 : ℂ) ^ k * (4 : ℂ) ^ k * (n + k + 1).factorial /
      ((n - k).factorial * (2 * k + 1).factorial : ℂ)
  else 0

/-- The Jacobi weight measure on `(-1,1)`. -/
def jacobiMeasure (α β : ℝ) : Measure ℝ :=
  (volume.restrict (Set.Ioo (-1 : ℝ) 1)).withDensity
    (fun x => ENNReal.ofReal ((1 - x) ^ α * (1 + x) ^ β))

end DLMF.OrthogonalPolynomials

namespace DLMF.Confluent

open DLMF.OrthogonalPolynomials

/-- Physicists' Hermite polynomial evaluated in `ℂ`. -/
def hermitePolyHEval (n : ℕ) (z : ℂ) : ℂ :=
  eval z ((hermitePolyH n).map (Int.castRingHom ℂ))

end DLMF.Confluent
