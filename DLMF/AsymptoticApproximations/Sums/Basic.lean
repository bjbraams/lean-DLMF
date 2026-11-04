/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.EulerMaclaurin
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import Mathlib.RingTheory.Binomial
public import DLMF.AlgebraicAnalytic.Complex.Basic

/-!
# Sums and sequences: definitions

This file defines the sums, integrals and comparison functions used in DLMF §2.10 (sums and
sequences), in the namespace `DLMF.AsymptoticApproximations`.

## Main definitions

* `jLogJSum`, `jLogJRemainder`: the Euler–Maclaurin example `∑_{j=1}^{n} j ln j` and its
  remainder (DLMF 2.10.3, 2.10.5), using DLMFMathlib's `periodicBernoulli`
  (`B̃_n(x) = B_n(x - ⌊x⌋)`, §24.2).
* `partialSumFrom`: the partial sums `U_j = u_1 + ⋯ + u_j` (DLMF 2.10.10).
* `oscillatorySum`: `S(α, β, n) = ∑_{j=1}^{n-1} e^{ijβ} j^α` (DLMF 2.10.11).
* `hypergeometric0F2OneOne`: `₀F₂(-; 1, 1; x) = ∑ x^j/(j!)³` (DLMF 2.10.19).
* `arcPathIntegral`, `imagSegmentPathIntegral`, `contourIntegralC`, `contourIntegralC₁`,
  `contourIntegralC₂`: the contour `𝒞` of Figure 2.10.1 (two semicircles and two pieces of the
  imaginary axis) and its halves, as sums of parametrized path integrals (DLMF 2.10.20, 2.10.22).
* `laurentCoeff_zero_eq`: the Laurent coefficients of DLMF 2.10.26 are
  `AlgebraicAnalytic.laurentCoeff` about `0`.
* `legendreComparison`: Darboux's comparison function for `P_n(cos α)` (DLMF 2.10.34).
* `powSumCoeff`, `harmonicAsymptoticCoeff`: the coefficients of DLMF 2.10.7 and 2.10.8.
-/

@[expose] public noncomputable section

open MeasureTheory Set Real Complex

namespace DLMF.AsymptoticApproximations

/-- DLMF 2.10.3: `S(n) = ∑_{j=1}^{n} j ln j`. -/
@[dlmf 2.10.E3]
def jLogJSum (n : ℕ) : ℝ := ∑ j ∈ Finset.Icc 1 n, (j : ℝ) * Real.log j

/-- DLMF 2.10.5: the remainder
`R_m(n) = ∫_n^∞ (B̃_{2m}(x) - B_{2m})/(2m(2m-1) x^{2m-1}) dx` of the expansion 2.10.4
(an absolutely convergent integral for `m ≥ 2`). -/
@[dlmf 2.10.E5]
def jLogJRemainder (m n : ℕ) : ℝ :=
  ∫ x in Ioi (n : ℝ), (periodicBernoulli (2 * m) x - bernoulli (2 * m)) /
    (2 * m * (2 * m - 1) * x ^ (2 * m - 1))

/-- DLMF 2.10.10: the partial sums `U_j = u_1 + u_2 + ⋯ + u_j` (`U_0 = 0`). -/
@[dlmf 2.10.E10]
def partialSumFrom (u : ℕ → ℂ) (j : ℕ) : ℂ := ∑ i ∈ Finset.Icc 1 j, u i

/-- DLMF 2.10.11: `S(α, β, n) = ∑_{j=1}^{n-1} e^{ijβ} j^α` for real `α`, `β`. -/
@[dlmf 2.10.E11]
def oscillatorySum (α β : ℝ) (n : ℕ) : ℂ :=
  ∑ j ∈ Finset.Ico 1 n, Complex.exp (I * j * β) * ((j : ℝ) ^ α : ℝ)

/-- DLMF 2.10.19: `₀F₂(-; 1, 1; x) = ∑_{j ≥ 0} x^j/(j!)³` (an entire function). -/
@[dlmf 2.10.E19]
def hypergeometric0F2OneOne (x : ℂ) : ℂ := ∑' j : ℕ, x ^ j / (j.factorial : ℂ) ^ 3

/-- The path integral of `F` over the arc `θ ↦ c e^{iθ}`, `θ` from `θ₁` to `θ₂`. -/
def arcPathIntegral (F : ℂ → ℂ) (c : ℝ) (θ₁ θ₂ : ℝ) : ℂ :=
  ∫ θ in θ₁..θ₂, F (c * Complex.exp (I * θ)) * (I * c * Complex.exp (I * θ))

/-- The path integral of `F` over the segment `y ↦ i y` of the imaginary axis, `y` from `y₁`
to `y₂`. -/
def imagSegmentPathIntegral (F : ℂ → ℂ) (y₁ y₂ : ℝ) : ℂ := ∫ y in y₁..y₂, F (I * y) * I

/-- The contour integral `∫_𝒞 F(t) dt` over the contour `𝒞` of Figure 2.10.1 (DLMF 2.10.20),
for `n ≥ 1`: the right semicircle `|t| = n - ½` (from `-i(n-½)` to `i(n-½)`), the imaginary
axis from `i(n-½)` down to `i/2`, the left semicircle `|t| = ½` (from `i/2` through `-½` to
`-i/2`) and the imaginary axis from `-i/2` down to `-i(n-½)`. It encircles `0, 1, …, n - 1`
once in the positive sense. -/
def contourIntegralC (F : ℂ → ℂ) (n : ℕ) : ℂ :=
  arcPathIntegral F (n - 1 / 2) (-(π / 2)) (π / 2) + imagSegmentPathIntegral F (n - 1 / 2) (1 / 2) +
    arcPathIntegral F (1 / 2) (π / 2) (3 * π / 2) +
    imagSegmentPathIntegral F (-(1 / 2)) (-(n - 1 / 2))

/-- The upper half `𝒞₁` of the contour `𝒞` (DLMF 2.10.22): the quarter circle from `n - ½` to
`i(n-½)`, the imaginary axis down to `i/2`, and the quarter circle from `i/2` to `-½`. -/
def contourIntegralC₁ (F : ℂ → ℂ) (n : ℕ) : ℂ :=
  arcPathIntegral F (n - 1 / 2) 0 (π / 2) + imagSegmentPathIntegral F (n - 1 / 2) (1 / 2) +
    arcPathIntegral F (1 / 2) (π / 2) π

/-- The lower half `𝒞₂` of the contour `𝒞` (DLMF 2.10.22): the quarter circle from `-½` to
`-i/2`, the imaginary axis down to `-i(n-½)`, and the quarter circle from `-i(n-½)` to
`n - ½`. -/
def contourIntegralC₂ (F : ℂ → ℂ) (n : ℕ) : ℂ :=
  arcPathIntegral F (1 / 2) π (3 * π / 2) + imagSegmentPathIntegral F (-(1 / 2)) (-(n - 1 / 2)) +
    arcPathIntegral F (n - 1 / 2) (-(π / 2)) 0

/-- DLMF 2.10.26: the Laurent coefficient `f_n = (2πi)⁻¹ ∮_{|z|=ρ} f(z) z^{-n-1} dz`, `n ∈ ℤ`,
for `f` analytic on an annulus containing the circle `|z| = ρ`, is the coefficient
`AlgebraicAnalytic.laurentCoeff f 0 ρ n` of DLMF 1.10.7 about `z₀ = 0`. -/
@[dlmf 2.10.E26]
theorem laurentCoeff_zero_eq (f : ℂ → ℂ) (ρ : ℝ) (n : ℤ) :
    AlgebraicAnalytic.laurentCoeff f 0 ρ n = (2 * π * I)⁻¹ * ∮ z in C(0, ρ), f z *
        z ^ (-(n + 1)) := by
  simp only [AlgebraicAnalytic.laurentCoeff, sub_zero, neg_add']

/-- DLMF 2.10.34: the comparison function
`g(z) = e^{-πi/4}(2 sin α)^{-1/2}(e^{-iα} - z)^{-1/2} + e^{πi/4}(2 sin α)^{-1/2}(e^{iα} - z)^{-1/2}`
for `0 < α < π`. The branch of `(e^{∓iα} - z)^{-1/2}` is continuous in the plane cut along the
outward ray through `e^{∓iα}` and equals `e^{±iα/2}` at `z = 0`; it is written as
`e^{±iα/2} (1 - z e^{±iα})^{-1/2}` with the principal power. -/
@[dlmf 2.10.E34]
def legendreComparison (α : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-(π * I / 4)) * ((2 * Real.sin α) ^ (-(1 / 2 : ℝ)) : ℝ) *
      (Complex.exp (I * α / 2) * (1 - z * Complex.exp (I * α)) ^ (-(1 / 2 : ℂ))) +
    Complex.exp (π * I / 4) * ((2 * Real.sin α) ^ (-(1 / 2 : ℝ)) : ℝ) *
      (Complex.exp (-(I * α / 2)) * (1 - z * Complex.exp (-(I * α))) ^ (-(1 / 2 : ℂ)))

section

open Finset
open scoped Nat

/-- The terms `(-B_{2s})/(2s(2s-1)(2s-2)) n^{-(2s-2)}` of DLMF 2.10.4. -/
def sumMulLogTerm (s n : ℕ) : ℝ :=
  -(bernoulli (2 * s) : ℝ) / (2 * s * (2 * s - 1) * (2 * s - 2)) / (n : ℝ) ^ (2 * s - 2)

/-- The asymptotic scale `n ↦ n^{α+1-s}` of DLMF 2.10.7. -/
def powSumScale (α : ℝ) (s n : ℕ) : ℝ := (n : ℝ) ^ (α + 1 - s)

/-- The coefficients `(α+1 choose s) B_s/(α+1)` of DLMF 2.10.7. -/
def powSumCoeff (α : ℝ) (s : ℕ) : ℝ := Ring.choose (α + 1) s * bernoulli s / (α + 1)

/-- The scale `n ↦ n^{-s}` of DLMF 2.10.8. -/
def Real.invPowScale (s n : ℕ) : ℝ := ((n : ℝ) ^ s)⁻¹

/-- The coefficients of DLMF 2.10.8: `0`, `-1/2`, and `-B_s/s` for `s ≥ 2` (zero for odd `s`). -/
def harmonicAsymptoticCoeff (s : ℕ) : ℝ :=
  if s = 0 then 0 else if s = 1 then -1 / 2 else -(bernoulli s : ℝ) / s

end

section

open Complex

/-- The integrand `x^t/Γ(t+1)³` of DLMF 2.10.20–2.10.24 (principal power, `x > 0`). -/
def hypergeometric0F2OneOneIntegrand (x : ℝ) (t : ℂ) : ℂ := (x : ℂ) ^ t / Complex.Gamma (t + 1) ^ 3

/-- The punctured disc `0 < |z| < r`. -/
def puncturedDisc (r : ℝ) : Set ℂ := {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < r}

end

end DLMF.AsymptoticApproximations
