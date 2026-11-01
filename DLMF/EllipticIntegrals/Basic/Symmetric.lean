/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Definitions of the symmetric elliptic integrals

Domain predicates and the literal principal-power integrals defining Carlson's symmetric
elliptic integrals, following DLMF §§19.2(iv), 19.15–19.16.

## Main definitions

* `SymEllIntArg`, `SymEllIntRFDomain`: admissible arguments and the domain of `R_F`
  (DLMF §19.16(i)).
* `IsNegReal`, `cauchyPVIoi`: negative real parameters and the Cauchy principal value of an
  integral over `(0, ∞)`.
* `symEllIntS`: the product `s(t)` of square roots (DLMF 19.16.4).
* `symEllIntRF`, `symEllIntRJ`, `symEllIntRG`, `symEllIntRD`: the integrals `R_F`, `R_J`,
  `R_G`, `R_D` (DLMF 19.16.1, 19.16.2, 19.16.2_5, 19.16.5).
* `symEllIntRC`: the integral `R_C(x, y)` (DLMF 19.2.17).

## Implementation notes

Negative real pole parameters use a Cauchy principal value. Divergent integrals and
nonexistent limits remain totalized; the theorem layer states convergence and branch
assumptions explicitly. The multivariate hypergeometric function `symEllIntR` (DLMF 19.16.8),
which is defined through Carlson's `R`-function in `lean-codes`, and the comparison theorems
with the Carlson functions are in `DLMF.EllipticIntegrals.Symmetric`.
-/

@[expose] public noncomputable section
open Complex Set Filter MeasureTheory
open scoped Real Topology
namespace DLMF.EllipticIntegrals

/-! ### Domains and the Cauchy principal value -/

/-- DLMF §19.16(i): an admissible argument of a symmetric integral, `x ∈ ℂ \ (-∞, 0]` or
`x = 0` (that is, `x` is not a negative real number). -/
@[dlmf 19.16.i]
def SymEllIntArg (x : ℂ) : Prop := x ∈ slitPlane ∨ x = 0

/-- DLMF §19.16(i): the domain of `R_F(x, y, z)` and of the first three arguments of `R_J`:
admissible arguments, at most one of them zero. -/
@[dlmf 19.16.i]
def SymEllIntRFDomain (x y z : ℂ) : Prop :=
  SymEllIntArg x ∧ SymEllIntArg y ∧ SymEllIntArg z ∧
    (x = 0 → y ≠ 0 ∧ z ≠ 0) ∧ (y = 0 → z ≠ 0)

/-- `p` is a negative real number (the case `p < 0` of DLMF, where principal values are
taken). -/
def IsNegReal (p : ℂ) : Prop := p.im = 0 ∧ p.re < 0

/-- The Cauchy principal value of `∫₀^∞ f` about an interior singular point `c > 0`:
`lim_{ε → 0+} ∫_{(0,∞) \ [c-ε, c+ε]} f`. Used for `R_J` with `p < 0` (DLMF §19.16(i)) and
`R_C` with `y < 0` (DLMF 19.2.17). If the limit does not exist the value is junk
(`limUnder`). -/
def cauchyPVIoi (f : ℝ → ℂ) (c : ℝ) : ℂ :=
  limUnder (𝓝[>] (0 : ℝ)) fun ε => ∫ t in Ioi (0 : ℝ) \ Icc (c - ε) (c + ε), f t

/-! ### The symmetric integrals -/

/-- DLMF 19.16.4: `s(t) = √(t + x) √(t + y) √(t + z)`, principal square roots. -/
@[dlmf 19.16.E4]
def symEllIntS (x y z : ℂ) (t : ℝ) : ℂ :=
  ((t : ℂ) + x) ^ (1 / 2 : ℂ) * ((t : ℂ) + y) ^ (1 / 2 : ℂ) * ((t : ℂ) + z) ^ (1 / 2 : ℂ)

/-- DLMF 19.16.1: Carlson's symmetric integral of the first kind
`R_F(x, y, z) = (1/2) ∫₀^∞ dt / s(t)`, for `x, y, z ∈ ℂ \ (-∞, 0]`, at most one of them `0`
(`SymEllIntRFDomain`). Off that domain the Lean integral is totalized. -/
@[dlmf 19.16.E1]
def symEllIntRF (x y z : ℂ) : ℂ :=
  (1 / 2) * ∫ t in Ioi (0 : ℝ), (symEllIntS x y z t)⁻¹

/-- DLMF 19.16.2: Carlson's symmetric integral of the third kind
`R_J(x, y, z, p) = (3/2) ∫₀^∞ dt / (s(t) (t + p))`, `p ≠ 0`, with `x, y, z` as for `R_F`.
**When `p` is real and negative the Cauchy principal value is taken** (about `t = -p`). -/
@[dlmf 19.16.E2]
def symEllIntRJ (x y z p : ℂ) : ℂ := by
  classical
  exact (3 / 2) *
    if IsNegReal p then
      cauchyPVIoi (fun t => (symEllIntS x y z t * ((t : ℂ) + p))⁻¹) (-p.re)
    else ∫ t in Ioi (0 : ℝ), (symEllIntS x y z t * ((t : ℂ) + p))⁻¹

/-- DLMF 19.16.2_5: Carlson's symmetric integral of the second kind
`R_G(x, y, z) = (1/4) ∫₀^∞ s(t)⁻¹ (x/(t+x) + y/(t+y) + z/(t+z)) t dt`, for admissible
`x, y, z` (any number of them may vanish). -/
@[dlmf 19.16.E2_5]
def symEllIntRG (x y z : ℂ) : ℂ :=
  (1 / 4) * ∫ t in Ioi (0 : ℝ),
    (symEllIntS x y z t)⁻¹ * (x / ((t : ℂ) + x) + y / ((t : ℂ) + y) + z / ((t : ℂ) + z)) * t

/-- DLMF 19.16.5: `R_D(x, y, z) = R_J(x, y, z, z)`, symmetric only in `x, y`; `z ≠ 0`. -/
@[dlmf 19.16.E5]
def symEllIntRD (x y z : ℂ) : ℂ := symEllIntRJ x y z z

/-- DLMF 19.2.17: `R_C(x, y) = (1/2) ∫₀^∞ dt / (√(t + x) (t + y))` for `x ∈ ℂ \ (-∞, 0)`,
`y ≠ 0`; **the Cauchy principal value is taken if `y < 0`**. -/
def symEllIntRC (x y : ℂ) : ℂ := by
  classical
  exact (1 / 2) *
    if IsNegReal y then
      cauchyPVIoi (fun t => (((t : ℂ) + x) ^ (1 / 2 : ℂ) * ((t : ℂ) + y))⁻¹) (-y.re)
    else ∫ t in Ioi (0 : ℝ), (((t : ℂ) + x) ^ (1 / 2 : ℂ) * ((t : ℂ) + y))⁻¹

end DLMF.EllipticIntegrals
