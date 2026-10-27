/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# Remainder terms and the Stokes phenomenon: definitions (DLMF §2.11)

Definitions for DLMF §2.11 (namespace `DLMF.AsymptoticApproximations`).

* `cosRationalIntegral` (2.11.1) and `cosRationalCoeff` (the `q_s` of 2.11.2–2.11.3).
* `stokesC` (2.11.16): `c(θ) = (2(1 + e^{iθ} + i(θ - π)))^{1/2}`, the branch continuous on
  `(-π, 3π)` with `c(θ) ∼ π - θ` as `θ → π`.
* `stokesA2` (2.11.14) and `stokesH` (2.11.17): the coefficients of the re-expansions
  2.11.13 and 2.11.15.
* `whittakerTerm` (2.11.30) and `levinTransform` (2.11.32).

The terminant `F_{n+p}(z) = Γ(n+p)/(2π) E_{n+p}(z)/z^{n+p-1}` of 2.11.11 is written out in
the statements of `Remainders/Stokes`, since `E_p` (`DLMF.Confluent.genExpIntE`) lives in a
theorem file of the confluent area.
-/

@[expose] public noncomputable section

open Complex
open scoped Real Nat

namespace DLMF.AsymptoticApproximations

/-- DLMF 2.11.1: `I(m) = ∫_0^π cos(mt)/(t² + 1) dt`. -/
@[dlmf 2.11.E1]
def cosRationalIntegral (m : ℝ) : ℝ := ∫ t in (0 : ℝ)..π, Real.cos (m * t) / (t ^ 2 + 1)

/-- The coefficients `q_s(t) = (-1)^{s+1} h^{(2s-1)}(t)`, `h(t) = 1/(t² + 1)`, of the expansion
2.11.2 obtained by repeated integration by parts (DLMF 2.11.2–2.11.3). -/
@[dlmf 2.11.E2]
def cosRationalCoeff (s : ℕ) (t : ℝ) : ℝ :=
  (-1) ^ (s + 1) * iteratedDeriv (2 * s - 1) (fun t : ℝ => 1 / (t ^ 2 + 1)) t

/-- DLMF 2.11.16: `c(θ) = (2(1 + e^{iθ} + i(θ - π)))^{1/2}`, with the branch continuous for
`-π < θ < 3π` and `c(θ) ∼ π - θ` as `θ → π`; it is written as
`(π - θ) · (2(1 + e^{iθ} + i(θ - π))/(π - θ)²)^{1/2}` with the principal square root (the
quotient avoids `(-∞, 0]` for `θ ∈ (-π, 3π)`), and `c(π) = 0`. -/
@[dlmf 2.11.E16]
def stokesC (θ : ℝ) : ℂ :=
  ((π - θ : ℝ) : ℂ) *
    (2 * (1 + Complex.exp (I * θ) + I * (θ - π)) / ((π - θ : ℝ) : ℂ) ^ 2) ^ (1 / 2 : ℂ)

/-- DLMF 2.11.14:
`a₂(θ, α) = (6α² - 6α + 1)/12 - α/(1 + e^{iθ}) + 1/(1 + e^{iθ})²`. -/
@[dlmf 2.11.E14]
def stokesA2 (θ : ℝ) (α : ℂ) : ℂ :=
  (6 * α ^ 2 - 6 * α + 1) / 12 - α / (1 + Complex.exp (I * θ)) +
    1 / (1 + Complex.exp (I * θ)) ^ 2

/-- DLMF 2.11.17: given the coefficients `a_{2s}(θ, α)` of 2.11.13 (here `a s θ α`),
`h_{2s}(θ, α) = e^{iα(π-θ)}/(1 + e^{-iθ}) a_{2s}(θ, α)
  + (-1)^{s-1} i · 1·3·5⋯(2s-1)/c(θ)^{2s+1}`. -/
@[dlmf 2.11.E17]
def stokesH (a : ℕ → ℝ → ℂ → ℂ) (s : ℕ) (θ : ℝ) (α : ℂ) : ℂ :=
  Complex.exp (I * α * (π - θ)) / (1 + Complex.exp (-(I * θ))) * a s θ α +
    (-1) ^ (s + 1) * I * ((2 * s - 1)‼ : ℂ) / stokesC θ ^ (2 * s + 1)

/-- DLMF 2.11.30: the terms
`a_n = e^{-z/2}/(z^{n-κ} n!) (μ² - (κ - 1/2)²)(μ² - (κ - 3/2)²)⋯(μ² - (κ - n + 1/2)²)`
of the expansion 2.11.29 of `W_{κ,μ}(z)` (principal power). -/
@[dlmf 2.11.E30]
def whittakerTerm (κ μ z : ℂ) (n : ℕ) : ℂ :=
  Complex.exp (-z / 2) / (z ^ ((n : ℂ) - κ) * n.factorial) *
    ∏ k ∈ Finset.Icc 1 n, (μ ^ 2 - (κ - k + 1 / 2) ^ 2)

/-- DLMF 2.11.32 (a variant of Levin's transformation): for terms `a_j` with partial sums
`s_j = a_0 + ⋯ + a_j`,
`d_n = ∑_{j=0}^{n} (-1)^j (n choose j) (j+1)^{n-1} s_j/a_{j+1} /
  ∑_{j=0}^{n} (-1)^j (n choose j) (j+1)^{n-1}/a_{j+1}`. -/
@[dlmf 2.11.E32]
def levinTransform (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  (∑ j ∈ Finset.range (n + 1), (-1) ^ j * (n.choose j : ℂ) * ((j + 1 : ℂ) ^ ((n : ℤ) - 1)) *
      ((∑ k ∈ Finset.range (j + 1), a k) / a (j + 1))) /
    ∑ j ∈ Finset.range (n + 1), (-1) ^ j * (n.choose j : ℂ) * ((j + 1 : ℂ) ^ ((n : ℤ) - 1)) /
      a (j + 1)

end DLMF.AsymptoticApproximations
