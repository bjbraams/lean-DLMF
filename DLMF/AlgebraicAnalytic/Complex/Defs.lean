/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import Mathlib.Topology.Compactification.OnePoint.Basic
public import TauCeti.Analysis.Contour.Winding.Number.Basic
public import TauCeti.Analysis.Contour.PiecewiseC1On
public import TauCeti.Topology.FilledHull

/-!
# Calculus and functions of a complex variable: definitions (DLMF §§1.9–1.10)

Definitions for DLMF §§1.9–1.10 (namespace `DLMF.AlgebraicAnalytic`) that are not in Mathlib or
Tau Ceti. Most notions of these sections are upstream: `Complex.re`, `Complex.im`, `Complex.arg`
(the principal phase, with values in `(-π, π]`, the single-valued convention of DLMF §1.9(i)),
`HasDerivAt`, `AnalyticAt`, `MeromorphicAt`, `analyticOrderAt`, `circleIntegral`, Tau Ceti's
`TauCeti.Contour.IsPiecewiseC1On` (contours), `TauCeti.Contour.windingNumber`,
`TauCeti.filledHull` and `TauCeti.Contour.residue` (residue at a pole). Defined here:

* `IsPhase z θ` (1.9.7): `θ` is a value of the multivalued phase `ph z`, `z = |z| e^{iθ}`.
* `extAdd`, `extMul`, `extDiv` (1.9.36–1.9.39): the arithmetic conventions of the extended
  plane `OnePoint ℂ` (`∞ ± z = ∞`, `∞ · z = ∞` for `z ≠ 0`, `z/∞ = 0`, `z/0 = ∞` for `z ≠ 0`).
* `AnalyticAtInfty f L`, `derivAtInfty f L` (§1.9(iv)): `f` is analytic at `∞` with value `L`
  there (`g(z) = f(1/z)`, `g(0) = L`, is analytic at `0`), and `f'(∞) = g'(0)`.
* `mobius a b c d` and its extension `mobiusExt a b c d` to `OnePoint ℂ` (1.9.40–1.9.41).
* `crossRatio` (1.9.45).
* `recipCoeff`, `logCoeff`, `powCoeff ν` (1.9.55–1.9.62): the coefficients of `1/f`, `ln f`
  and `f^ν` for a power series `f`, by the recurrences 1.9.56, 1.9.59, 1.9.62.
* `contourIntegral` (1.9.28), `IsSimpleClosedContour`, `contourInterior`, `contourExterior`,
  `IsPositivelyOriented`
  (§1.9(iii)): simple closed contours, their interior and exterior domains (via Tau Ceti's
  filled hull) and the positive (anticlockwise) sense.
* `laurentCoeff` (1.10.7) and `residueAt` (§1.10(iii)): Laurent coefficients as circle integrals
  and the residue `a_{-1}` at an isolated singularity (also essential ones).
* `ProdConvergesDLMF` (§1.10(ix)): DLMF's notion of convergence of `∏ (1 + a_n)` (partial
  products from some index on converge to a nonzero limit).
-/

@[expose] public noncomputable section

open Complex Filter Set
open scoped Topology OnePoint

namespace DLMF.AlgebraicAnalytic

/-! ## §1.9(i) Complex numbers -/

/-- DLMF 1.9.7: `θ` is a value of the (multivalued) phase `ph z`, that is `z = |z| e^{iθ}`.
For `z ≠ 0` the values are `θ = arg z + 2nπ`, `n ∈ ℤ` (`isPhase_iff` in
`DLMF.AlgebraicAnalytic.Complex.Calculus`); for `z = 0` every `θ` qualifies, and DLMF leaves
the phase undefined. -/
@[dlmf 1.9.E7]
def IsPhase (z : ℂ) (θ : ℝ) : Prop :=
  z = (‖z‖ : ℂ) * exp (θ * I)

/-! ## §1.9(iv) The extended complex plane -/

/-- DLMF 1.9.36: addition of a complex number to a point of the extended plane `ℂ ∪ {∞}`:
`∞ + z = ∞`, and ordinary addition on `ℂ`. -/
@[dlmf 1.9.E36]
def extAdd : OnePoint ℂ → ℂ → OnePoint ℂ
  | ∞, _ => ∞
  | (w : ℂ), z => ((w + z : ℂ) : OnePoint ℂ)

/-- DLMF 1.9.37: multiplication of a point of the extended plane by a complex number:
`∞ · z = ∞` (DLMF requires `z ≠ 0`; the value `∞ · 0 = ∞` is a junk value), and ordinary
multiplication on `ℂ`. -/
@[dlmf 1.9.E37]
def extMul : OnePoint ℂ → ℂ → OnePoint ℂ
  | ∞, _ => ∞
  | (w : ℂ), z => ((w * z : ℂ) : OnePoint ℂ)

/-- DLMF 1.9.38–1.9.39: division of a complex number by a point of the extended plane:
`z/∞ = 0`, `z/0 = ∞` (DLMF requires `z ≠ 0`; `0/0 = ∞` is a junk value), and ordinary division
by a nonzero complex number. -/
@[dlmf 1.9.E38]
def extDiv (z : ℂ) : OnePoint ℂ → OnePoint ℂ
  | ∞ => ((0 : ℂ) : OnePoint ℂ)
  | (w : ℂ) => if w = 0 then ∞ else ((z / w : ℂ) : OnePoint ℂ)

/-- DLMF §1.9(iv): `f` is analytic at `∞` with value `L` there: `g(z) = f(1/z)`, completed by
`g(0) = L`, is analytic at `z = 0`. (The value at `∞` is a parameter because `f : ℂ → ℂ` has no
value at `∞`; it is the limit of `f` at infinity.) -/
@[dlmf 1.9.iv]
def AnalyticAtInfty (f : ℂ → ℂ) (L : ℂ) : Prop :=
  AnalyticAt ℂ (Function.update (fun z => f z⁻¹) 0 L) 0

/-- DLMF §1.9(iv): `f'(∞) = g'(0)` for `g(z) = f(1/z)`, `g(0) = L`. -/
@[dlmf 1.9.iv]
def derivAtInfty (f : ℂ → ℂ) (L : ℂ) : ℂ :=
  deriv (Function.update (fun z => f z⁻¹) 0 L) 0

/-- DLMF 1.9.40: the bilinear (Möbius) transformation `f(z) = (az + b)/(cz + d)` on `ℂ`
(with `x/0 = 0` at `z = -d/c`; see `mobiusExt` for the extended plane). -/
@[dlmf 1.9.E40]
def mobius (a b c d : ℂ) (z : ℂ) : ℂ :=
  (a * z + b) / (c * z + d)

/-- DLMF 1.9.40–1.9.41: the bilinear transformation on the extended plane: `f(-d/c) = ∞`,
`f(∞) = a/c` (for `c ≠ 0`; for `c = 0`, `f(∞) = ∞`). -/
@[dlmf 1.9.E41]
def mobiusExt (a b c d : ℂ) : OnePoint ℂ → OnePoint ℂ
  | ∞ => if c = 0 then ∞ else ((a / c : ℂ) : OnePoint ℂ)
  | (z : ℂ) => if c * z + d = 0 then ∞ else ((mobius a b c d z : ℂ) : OnePoint ℂ)

/-- DLMF 1.9.45: the cross ratio `(z₁ - z₂)(z₃ - z₄) / ((z₁ - z₄)(z₃ - z₂))` of four complex
numbers (the limiting forms with a point at `∞` are not defined here). -/
@[dlmf 1.9.E45]
def crossRatio (z₁ z₂ z₃ z₄ : ℂ) : ℂ :=
  (z₁ - z₂) * (z₃ - z₄) / ((z₁ - z₄) * (z₃ - z₂))

/-! ## §1.9(vi) Operations on power series -/

/-- DLMF 1.9.55–1.9.56: the coefficients `b_n` of `1/f(z) = ∑ b_n zⁿ` for
`f(z) = ∑ a_n zⁿ`, `a_0 ≠ 0`: `b_0 = 1/a_0` and
`b_n = -(a_1 b_{n-1} + a_2 b_{n-2} + ⋯ + a_n b_0)/a_0` for `n ≥ 1`. -/
@[dlmf 1.9.E56]
def recipCoeff (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  if _h : n = 0 then 1 / a 0
  else -(∑ k : Fin n, a (k + 1) * recipCoeff a (n - 1 - k)) / a 0
decreasing_by omega

/-- DLMF 1.9.58–1.9.59: the coefficients `q_n` of `ln f(z) = ∑_{n ≥ 1} q_n zⁿ` for
`f(z) = 1 + a_1 z + a_2 z² + ⋯`: `q_n = (n a_n - (n-1) a_1 q_{n-1} - ⋯ - a_{n-1} q_1)/n`
(`q_0 = 0`; for `n = 1` the formula gives `q_1 = a_1`). -/
@[dlmf 1.9.E59]
def logCoeff (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  if _h : n = 0 then 0
  else (n * a n - ∑ k : Fin (n - 1), ((n : ℂ) - (k + 1)) * a (k + 1) *
    logCoeff a (n - 1 - k)) / n
decreasing_by omega

/-- DLMF 1.9.61–1.9.62: the coefficients `p_n` of `(f(z))^ν = ∑ p_n zⁿ` for
`f(z) = 1 + a_1 z + a_2 z² + ⋯`: `p_0 = 1` and
`p_n = ((ν - n + 1) a_1 p_{n-1} + (2ν - n + 2) a_2 p_{n-2} + ⋯ + n ν a_n p_0)/n`, that is
`n p_n = ∑_{k=1}^{n} ((ν + 1)k - n) a_k p_{n-k}`. -/
@[dlmf 1.9.E62]
def powCoeff (ν : ℂ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  if _h : n = 0 then 1
  else (∑ k : Fin n, ((ν + 1) * (k + 1) - n) * a (k + 1) * powCoeff ν a (n - 1 - k)) / n
decreasing_by omega

/-! ## §1.9(iii) Contours -/

/-- DLMF §1.9(iii): `γ : [a, b] → ℂ` is a simple closed contour: piecewise `C¹`
(`TauCeti.Contour.IsPiecewiseC1On`), closed (`γ a = γ b`) and without multiple points other than
the endpoints (`γ` injective on `[a, b)`), with `a < b`. -/
@[dlmf 1.9.iii]
def IsSimpleClosedContour (γ : ℝ → ℂ) (a b : ℝ) : Prop :=
  a < b ∧ TauCeti.Contour.IsPiecewiseC1On γ a b ∧ γ a = γ b ∧ InjOn γ (Ico a b)

/-- DLMF 1.9.28: the contour integral `∫_C f(z) dz = ∫_a^b f(z(t)) z'(t) dt` along
`z = γ(t)`, `a ≤ t ≤ b` (Tau Ceti's convention `∫ t in a..b, deriv γ t • f (γ t)`; for a
piecewise `C¹` contour the derivative is junk only at finitely many breakpoints). -/
@[dlmf 1.9.E28]
def contourIntegral (γ : ℝ → ℂ) (a b : ℝ) (f : ℂ → ℂ) : ℂ :=
  ∫ t in a..b, deriv γ t • f (γ t)

/-- DLMF §1.9(iii) (Jordan curve theorem): the interior domain of a closed contour `C`, the
points off `C` whose component of `ℂ \ C` is bounded (Tau Ceti's filled hull minus the curve). -/
@[dlmf 1.9.iii]
def contourInterior (γ : ℝ → ℂ) (a b : ℝ) : Set ℂ :=
  TauCeti.filledHull (γ '' Icc a b) \ γ '' Icc a b

/-- DLMF §1.9(iii) (Jordan curve theorem): the exterior domain of a closed contour, the union of
the unbounded components of its complement. -/
@[dlmf 1.9.iii]
def contourExterior (γ : ℝ → ℂ) (a b : ℝ) : Set ℂ :=
  (TauCeti.filledHull (γ '' Icc a b))ᶜ

/-- DLMF §1.9(iii): a closed contour is described in the positive rotational (anticlockwise)
sense when its winding number about every interior point is `1`. For a simple closed contour
the winding number is constant `±1` on the interior
(`IsSimpleClosedContour.windingNumber_eq_one_or_neg_one`), so exactly one of `γ` and its
reversal is positively oriented. -/
@[dlmf 1.9.iii]
def IsPositivelyOriented (γ : ℝ → ℂ) (a b : ℝ) : Prop :=
  ∀ z ∈ contourInterior γ a b, TauCeti.Contour.windingNumber γ a b z = 1

/-! ## §1.10(iii) Laurent series and residues -/

/-- DLMF 1.10.7: the Laurent coefficient
`a_n = (2πi)⁻¹ ∮_{|z - z₀| = r} f(z) (z - z₀)^{-n-1} dz`, `n ∈ ℤ`, the circle described once in
the positive sense. -/
@[dlmf 1.10.E7]
def laurentCoeff (f : ℂ → ℂ) (z₀ : ℂ) (r : ℝ) (n : ℤ) : ℂ :=
  (2 * Real.pi * I)⁻¹ * ∮ z in C(z₀, r), f z * (z - z₀) ^ (-n - 1)

/-- DLMF §1.10(iii): the residue of `f` at an isolated singularity `z₀`, the coefficient `a_{-1}`
of its Laurent series in a punctured disc, `(2πi)⁻¹ ∮_{|z - z₀| = r} f(z) dz` for small `r > 0`
(the value is independent of `r` when `f` is holomorphic in a punctured disc; for other `f` the
limit is a junk value). This covers essential singularities; at poles it agrees with Tau Ceti's
`TauCeti.Contour.residue` (`residueAt_eq_residue`). -/
@[dlmf 1.10.iii]
def residueAt (f : ℂ → ℂ) (z₀ : ℂ) : ℂ :=
  limUnder (𝓝[>] (0 : ℝ)) fun r => laurentCoeff f z₀ r (-1)

/-! ## §1.10(ix) Infinite products -/

/-- DLMF §1.10(ix): the infinite product `∏_{n ≥ 1} (1 + a_n)` converges in the sense of DLMF:
for some `k ≥ 1` the partial products `p_{k,m} = ∏_{n=k}^{m} (1 + a_n)` tend to a nonzero limit
as `m → ∞` (finitely many zero factors are allowed). The value `a 0` is not used. This differs
from Mathlib's `Multipliable`, which is unconditional and allows the limit `0`. -/
@[dlmf 1.10.ix]
def ProdConvergesDLMF (a : ℕ → ℂ) : Prop :=
  ∃ k ≥ 1, ∃ p : ℂ, p ≠ 0 ∧
    Tendsto (fun m : ℕ => ∏ n ∈ Finset.Icc k m, (1 + a n)) atTop (𝓝 p)

end DLMF.AlgebraicAnalytic
