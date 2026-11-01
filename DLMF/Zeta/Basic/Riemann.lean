/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Functions attached to the Riemann zeta function (DLMF Chapter 25)

The Riemann zeta function `ζ(s)` of DLMF Chapter 25 is Mathlib's `riemannZeta`. This file
defines the functions and constants that DLMF builds from it.

## Main definitions

* `stieltjesSeq`, `stieltjesConstant`: the Stieltjes constants `γₙ` (DLMF 25.2.5).
* `riemannXi`: Riemann's `ξ`-function (DLMF 25.4.4).
* `reflectionConst`: the constant `c = -ln(2π) - πi/2` (DLMF 25.4.6).
* `riemannChi`: the factor `χ(s)` of the functional equation `ζ(s) = χ(s) ζ(1-s)`
  (DLMF 25.9.2).
* `riemannSiegelTheta`, `riemannSiegelZ`: the Riemann–Siegel functions `θ` and `Z`
  (DLMF 25.10.1–25.10.2).

## Implementation notes

`riemannXi` is defined through Mathlib's entire function `completedRiemannZeta₀`, so that it is
entire with no removable singularities to fill in. `stieltjesConstant n` is a `limUnder`; the
existence of the limit is `tendsto_stieltjesSeq` in `DLMF.Zeta.Basic.RiemannProperties`.
`riemannSiegelTheta` uses the principal phase, as DLMF prescribes; `e^{iθ}` and hence `Z` do not
depend on that choice. The basic properties are in `DLMF.Zeta.Basic.RiemannProperties`.
-/

@[expose] public noncomputable section

open Complex Filter
open scoped Real

namespace DLMF.Zeta

/-- The sequence `∑_{k=1}^{m} (ln k)ⁿ/k - (ln m)^{n+1}/(n+1)` whose limit defines the Stieltjes
constant `γₙ` (DLMF 25.2.5). -/
@[dlmf 25.2.E5]
def stieltjesSeq (n m : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 m, Real.log k ^ n / k - Real.log m ^ (n + 1) / (n + 1)

/-- DLMF 25.2.5: the Stieltjes constants `γₙ = lim_{m→∞} (∑_{k=1}^{m} (ln k)ⁿ/k -
(ln m)^{n+1}/(n+1))`, as the `limUnder` of `stieltjesSeq n`; the limit exists by
`tendsto_stieltjesSeq`. -/
@[dlmf 25.2.E5]
def stieltjesConstant (n : ℕ) : ℝ :=
  limUnder atTop (stieltjesSeq n)

/-- DLMF 25.4.4: Riemann's `ξ`-function `ξ(s) = ½ s(s-1) Γ(s/2) π^{-s/2} ζ(s)`, defined as the
entire function `½ s(s-1) Λ₀(s) + ½`, where `Λ₀ = completedRiemannZeta₀` is Mathlib's entire
completion `Λ(s) + 1/s + 1/(1-s)` of `Λ(s) = π^{-s/2} Γ(s/2) ζ(s)`. The printed formula is
`riemannXi_eq`. -/
@[dlmf 25.4.E4]
def riemannXi (s : ℂ) : ℂ :=
  s * (s - 1) / 2 * completedRiemannZeta₀ s + 1 / 2

/-- DLMF 25.4.6: the constant `c = -ln(2π) - πi/2` of the derivative reflection formulas. -/
@[dlmf 25.4.E6]
def reflectionConst : ℂ :=
  -(Real.log (2 * π) : ℂ) - π * I / 2

/-- DLMF 25.9.2: `χ(s) = π^{s-½} Γ(½ - s/2) / Γ(s/2)`. -/
@[dlmf 25.9.E2]
def riemannChi (s : ℂ) : ℂ :=
  (π : ℂ) ^ (s - 1 / 2) * Gamma (1 / 2 - s / 2) / Gamma (s / 2)

/-- DLMF 25.10.2: the Riemann–Siegel theta function `θ(t) = ph Γ(¼ + ½it) - ½ t ln π`, with the
principal value of the phase (`Complex.arg`), as DLMF prescribes. -/
@[dlmf 25.10.E2]
def riemannSiegelTheta (t : ℝ) : ℝ :=
  arg (Gamma (1 / 4 + t / 2 * I)) - t / 2 * Real.log π

/-- DLMF 25.10.1: `Z(t) = e^{iθ(t)} ζ(½ + it)`. -/
@[dlmf 25.10.E1]
def riemannSiegelZ (t : ℝ) : ℂ :=
  cexp (I * riemannSiegelTheta t) * riemannZeta (1 / 2 + t * I)

end DLMF.Zeta
