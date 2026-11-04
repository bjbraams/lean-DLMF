/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Core.Basic
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

The canonical definitions of the classical orthogonal polynomial families that are not in
Mathlib, following AAR Chapter 6 and DLMF §18.5.

## Main definitions

* `hermitePolynomialH`: the physicists' Hermite polynomials, by `H_{n+1} = 2x H_n - H_n'` (AAR
  §6.1).
* `laguerrePolynomialL`: the generalized Laguerre polynomials `L_n^{(α)}` as a `₁F₁` (DLMF 18.5.12).
* `jacobiPolynomialP`: the Jacobi polynomials `P_n^{(α,β)}` as a `₂F₁` (DLMF 18.5.7).
* `legendrePolynomialP`: the Legendre polynomials, the Jacobi case `α = β = 0` (DLMF 18.7.9).
* `ultrasphericalPolynomial`: the Gegenbauer polynomials `C_n^{(λ)}` as a `₂F₁` (DLMF 18.5.9).
* `laguerreExtended`: the Laguerre polynomial as a polynomial in its parameter, including
  negative integer parameters (DLMF 18.5.12).
* `chebyshevV`, `chebyshevW`: the Chebyshev polynomials of the third and fourth kinds
  (DLMF 18.7.5–18.7.6).
* `jacobiMeasure`: the Jacobi weight measure on `(-1, 1)`.
* `hermitePolynomialHEval`: the physicists' Hermite polynomial evaluated in `ℂ`.

## Implementation notes

The hypergeometric realizations of `laguerrePolynomialL`, `jacobiPolynomialP` and
`ultrasphericalPolynomial` are intended for `α + 1` (resp. `λ + 1/2`) not a nonpositive integer. The
basic API of these families is in `DLMF.OrthogonalPolynomials.Basic.Classical`.
-/

@[expose] public noncomputable section

open Complex Filter Set Polynomial
open scoped Real Nat Topology ENNReal Interval
open DLMF.Hypergeometric
open MeasureTheory intervalIntegral DLMF.Confluent

namespace DLMF.OrthogonalPolynomials

/-- Physicists' Hermite polynomials, AAR §6.1: `H_{n+1} = 2x H_n - H_n'`. -/
def hermitePolynomialH : ℕ → ℤ[X]
  | 0 => 1
  | n + 1 => 2 * X * hermitePolynomialH n - derivative (hermitePolynomialH n)

/-- Hypergeometric realization of generalized Laguerre polynomials, AAR §6.2,
for `α + 1` not a nonpositive integer:
`L_n^{(α)}(x) = (α+1)_n / n! · ₁F₁(-n; α+1; x)`. -/
@[dlmf 18.5.E12]
def laguerrePolynomialL (α : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  pochhammer (α + 1) n / n ! * kummerM (-n : ℂ) (α + 1) x

/-- Hypergeometric realization of Jacobi polynomials, AAR §6.3,
for `α + 1` not a nonpositive integer:
`P_n^{(α,β)}(x) = (α+1)_n / n! · ₂F₁(-n, n+α+β+1; α+1; (1-x)/2)`. -/
@[dlmf 18.5.E7]
def jacobiPolynomialP (α β : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  pochhammer (α + 1) n / n ! * ₂F₁ (-n : ℂ) (n + α + β + 1) (α + 1) ((1 - x) / 2)

/-- Legendre polynomials as Jacobi polynomials with `α = β = 0`. -/
@[dlmf 18.7.E9]
def legendrePolynomialP (n : ℕ) (x : ℂ) : ℂ :=
  jacobiPolynomialP 0 0 n x

/-- Hypergeometric realization of Gegenbauer polynomials, AAR §6.11,
for `λ + 1/2` not a nonpositive integer:
`C_n^{(λ)}(x) = (2λ)_n / n! · ₂F₁(-n, n+2λ; λ+1/2; (1-x)/2)`. -/
@[dlmf 18.5.E9]
def ultrasphericalPolynomial (lam : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  pochhammer (2 * lam) n / n ! * ₂F₁ (-n : ℂ) (n + 2 * lam) (lam + 1 / 2) ((1 - x) / 2)

/-- Helper lemma for `eval_U_eq_ultrasphericalPolynomial`. Closed form of the coefficients of
`C_n^{(1)}`. -/
def gegenbauerB (n k : ℕ) : ℂ :=
  if k ≤ n then
    (-1 : ℂ) ^ k * (4 : ℂ) ^ k * (n + k + 1).factorial /
      ((n - k).factorial * (2 * k + 1).factorial : ℂ)
  else 0

/-- The Jacobi weight measure on `(-1,1)`. -/
def jacobiMeasure (α β : ℝ) : Measure ℝ :=
  (volume.restrict (Set.Ioo (-1 : ℝ) 1)).withDensity
    (fun x => ENNReal.ofReal ((1 - x) ^ α * (1 + x) ^ β))

/-- Polynomial continuation of Laguerre in its parameter, including negative
integers. The existing `laguerrePolynomialL` uses a totalized hypergeometric quotient and
agrees with this definition only at regular denominator parameters. -/
@[dlmf 18.5.E12]
def laguerreExtended (α : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), pochhammer (α + k + 1) (n - k) /
    ((k.factorial : ℂ) * (n - k).factorial) * (-x) ^ k

/-- Chebyshev polynomials of the third kind, in the DLMF normalization. -/
@[dlmf 18.7.E5]
def chebyshevV (n : ℕ) (x : ℂ) : ℂ :=
  jacobiPolynomialP (-1 / 2) (1 / 2) n x / jacobiPolynomialP (-1 / 2) (1 / 2) n 1

/-- Chebyshev polynomials of the fourth kind, in the DLMF normalization. -/
@[dlmf 18.7.E6]
def chebyshevW (n : ℕ) (x : ℂ) : ℂ :=
  (2 * n + 1) * jacobiPolynomialP (1 / 2) (-1 / 2) n x / jacobiPolynomialP (1 / 2) (-1 / 2) n 1

end DLMF.OrthogonalPolynomials

namespace DLMF.Confluent

open DLMF.OrthogonalPolynomials

/-- Physicists' Hermite polynomial evaluated in `ℂ`. -/
def hermitePolynomialHEval (n : ℕ) (z : ℂ) : ℂ :=
  eval z ((hermitePolynomialH n).map (Int.castRingHom ℂ))

end DLMF.Confluent
