/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.WignerSymbols.Basic
public import DLMF.Legendre.Harmonics

/-!
# `3j` symbols, Legendre polynomials and spherical harmonics: DLMF §34.3(vii)

The Legendre polynomials `P_l` of §18.3 are `DLMF.OrthogonalPolynomials.legendrePolyP` and the
spherical harmonics `Y_{l,m}` of §14.30 are `DLMF.Legendre.sphericalHarmonic` (with
`Y_{l,m} = 0` for `|m| > l`). The sums over `l` run over `0, …, l₁ + l₂` and over
`m = -l, …, l`; the summands vanish outside the triangle conditions.
-/

@[expose] public noncomputable section

open Finset MeasureTheory intervalIntegral
open scoped Real

namespace DLMF.WignerSymbols

open DLMF.OrthogonalPolynomials DLMF.Legendre

/-- DLMF 34.3.19, for every complex argument (stronger than DLMF, which takes `x = cos θ`):
`P_{l₁}(x) P_{l₂}(x) = ∑_l (2l+1) (l₁ l₂ l; 0 0 0)² P_l(x)`. -/
@[dlmf 34.3.E19]
theorem legendrePolyP_mul_legendrePolyP (l₁ l₂ : ℕ) (x : ℂ) :
    legendrePolyP l₁ x * legendrePolyP l₂ x =
      ∑ l ∈ range (l₁ + l₂ + 1),
        ((2 * (l : ℝ) + 1) * wigner3j l₁ l₂ l 0 0 0 ^ 2 : ℝ) * legendrePolyP l x := by
  sorry

/-- DLMF 34.3.20: `Y_{l₁,m₁} Y_{l₂,m₂}`
`= ∑_{l,m} ((2l₁+1)(2l₂+1)(2l+1)/(4π))^{1/2} (l₁ l₂ l; m₁ m₂ m) conj(Y_{l,m}) (l₁ l₂ l; 0 0 0)`. -/
@[dlmf 34.3.E20]
theorem sphericalHarmonic_mul_sphericalHarmonic (l₁ l₂ : ℕ) (m₁ m₂ : ℤ) (θ φ : ℝ) :
    sphericalHarmonic l₁ m₁ θ φ * sphericalHarmonic l₂ m₂ θ φ =
      ∑ l ∈ range (l₁ + l₂ + 1), ∑ m ∈ Icc (-(l : ℤ)) l,
        ((Real.sqrt ((2 * (l₁ : ℝ) + 1) * (2 * l₂ + 1) * (2 * l + 1) / (4 * π)) *
            wigner3j l₁ l₂ l m₁ m₂ m * wigner3j l₁ l₂ l 0 0 0 : ℝ) : ℂ) *
          starRingEnd ℂ (sphericalHarmonic l m θ φ) := by
  sorry

/-- DLMF 34.3.21: `∫₀^π P_{l₁}(cos θ) P_{l₂}(cos θ) P_{l₃}(cos θ) sin θ dθ`
`= 2 (l₁ l₂ l₃; 0 0 0)²`. -/
@[dlmf 34.3.E21]
theorem integral_legendrePolyP_mul_mul (l₁ l₂ l₃ : ℕ) :
    ∫ θ in (0 : ℝ)..π, legendrePolyP l₁ (Real.cos θ) * legendrePolyP l₂ (Real.cos θ) *
        legendrePolyP l₃ (Real.cos θ) * (Real.sin θ : ℂ) =
      ((2 * wigner3j l₁ l₂ l₃ 0 0 0 ^ 2 : ℝ) : ℂ) := by
  sorry

/-- DLMF 34.3.22: Gaunt's integral
`∫₀^{2π} ∫₀^π Y_{l₁,m₁} Y_{l₂,m₂} Y_{l₃,m₃} sin θ dθ dφ`
`= ((2l₁+1)(2l₂+1)(2l₃+1)/(4π))^{1/2} (l₁ l₂ l₃; 0 0 0)(l₁ l₂ l₃; m₁ m₂ m₃)`. -/
@[dlmf 34.3.E22]
theorem integral_sphericalHarmonic_mul_mul (l₁ l₂ l₃ : ℕ) (m₁ m₂ m₃ : ℤ) :
    ∫ φ in (0 : ℝ)..2 * π, ∫ θ in (0 : ℝ)..π,
        sphericalHarmonic l₁ m₁ θ φ * sphericalHarmonic l₂ m₂ θ φ *
          sphericalHarmonic l₃ m₃ θ φ * (Real.sin θ : ℂ) =
      ((Real.sqrt ((2 * (l₁ : ℝ) + 1) * (2 * l₂ + 1) * (2 * l₃ + 1) / (4 * π)) *
          wigner3j l₁ l₂ l₃ 0 0 0 * wigner3j l₁ l₂ l₃ m₁ m₂ m₃ : ℝ) : ℂ) := by
  sorry

end DLMF.WignerSymbols
