/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Weierstrass.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Asymptotics.Defs

/-!
# Fourier series, series of cosecants, products and Laurent series (DLMF §§23.8–23.9)

Series are stated with `HasSum` (all of them converge absolutely). Sums from `n = 1` are
indexed by `n : ℕ` with the shift `n + 1`; the Eisenstein-bracketed cotangent series 23.8.4 is
stated as the absolutely convergent series of the bracketed pairs `n`, `-n`.

**Source correction.** The convergence condition of 23.8.1–23.8.2 is printed as
`ℑ(z/ω₁) < 2ℑ(ω₃/ω₁)`; the series diverge when `ℑ(z/ω₁) ≤ -2ℑ(ω₃/ω₁)` (the terms grow like
`e^{nπ(|ℑ(z/ω₁)| - 2ℑτ)}`; e.g. `ω₁ = 1.1 + 0.2i`, `ω₃ = 0.3 + 0.9i`,
`z/ω₁ = 0.3 - 2.5iℑτ` gives terms of size `10⁵, 10¹¹, 10²¹` at `n = 10, 20, 40`). The
acquired condition is `|ℑ(z/ω₁)| < 2ℑ(ω₃/ω₁)`.

The coefficients `a_{m,n}` of 23.9.7 are defined by the recursion 23.9.8 (`sigmaCoeff`), by
well-founded recursion on the weight `2m + 3n`.
-/

@[expose] public section

open Complex PeriodPair Asymptotics
open scoped Real

noncomputable section

namespace DLMF.Weierstrass

namespace HalfPeriods

variable (H : HalfPeriods)

/-! ### Fourier series (§23.8(i)) -/

/-- DLMF 23.8.1 (with the corrected condition `|ℑ(z/ω₁)| < 2ℑτ`), `q = e^{iπω₃/ω₁}`, `z ∉ 𝕃`:
`℘(z) + η₁/ω₁ - (π²/(4ω₁²))csc²(πz/(2ω₁)) = -(2π²/ω₁²) ∑_{n≥1} nq^{2n}/(1 - q^{2n}) cos(nπz/ω₁)`.
Corrected from the printed DLMF formula: the printed condition lacks the absolute value on
`ℑ(z/ω₁)`; for `ℑ(z/ω₁) ≤ -2ℑτ` the series diverges (terms `10⁵, 10¹¹, 10²¹` at
`n = 10, 20, 40`). -/
@[dlmf 23.8.E1]
theorem weierstrassP_fourier {z : ℂ} (hz : z ∉ H.lattice) (hzi : |(z / H.ω₁).im| < 2 * H.tau.im) :
    HasSum (fun n : ℕ ↦ -(2 * π ^ 2 / H.ω₁ ^ 2) *
        ((n + 1 : ℂ) * H.nome ^ (2 * (n + 1)) / (1 - H.nome ^ (2 * (n + 1))) *
          Complex.cos ((n + 1 : ℂ) * π * z / H.ω₁)))
      (H.weierstrassP z + H.eta 1 / H.ω₁ -
        π ^ 2 / (4 * H.ω₁ ^ 2) * (1 / Complex.sin (π * z / (2 * H.ω₁)) ^ 2)) := by
  sorry

/-- DLMF 23.8.2 (with the corrected condition `|ℑ(z/ω₁)| < 2ℑτ`), `z ∉ 𝕃`:
`ζ(z) - η₁z/ω₁ - (π/(2ω₁))cot(πz/(2ω₁)) = (2π/ω₁) ∑_{n≥1} q^{2n}/(1 - q^{2n}) sin(nπz/ω₁)`.
Corrected from the printed DLMF formula: the absolute value on `ℑ(z/ω₁)` is missing in the
printed condition, as in 23.8.1; without it the series diverges. -/
@[dlmf 23.8.E2]
theorem weierstrassZeta_fourier {z : ℂ} (hz : z ∉ H.lattice)
    (hzi : |(z / H.ω₁).im| < 2 * H.tau.im) :
    HasSum (fun n : ℕ ↦ 2 * π / H.ω₁ *
        (H.nome ^ (2 * (n + 1)) / (1 - H.nome ^ (2 * (n + 1))) *
          Complex.sin ((n + 1 : ℂ) * π * z / H.ω₁)))
      (H.weierstrassZeta z - H.eta 1 * z / H.ω₁ -
        π / (2 * H.ω₁) * Complex.cot (π * z / (2 * H.ω₁))) := by
  sorry

/-! ### Series of cosecants and cotangents (§23.8(ii)) -/

/-- DLMF 23.8.3: `℘(z) = -η₁/ω₁ + (π²/(4ω₁²)) ∑_{n ∈ ℤ} csc²(π(z + 2nω₃)/(2ω₁))`, `z ∉ 𝕃`. -/
@[dlmf 23.8.E3]
theorem weierstrassP_csc_series {z : ℂ} (hz : z ∉ H.lattice) :
    HasSum (fun n : ℤ ↦ π ^ 2 / (4 * H.ω₁ ^ 2) *
        (1 / Complex.sin (π * (z + 2 * n * H.ω₃) / (2 * H.ω₁)) ^ 2))
      (H.weierstrassP z + H.eta 1 / H.ω₁) := by
  sorry

/-- DLMF 23.8.4: `ζ(z) = η₁z/ω₁ + (π/(2ω₁)) ∑_{n ∈ ℤ} cot(π(z + 2nω₃)/(2ω₁))` with the terms
`n` and `-n` bracketed (Eisenstein summation), `z ∉ 𝕃`. -/
@[dlmf 23.8.E4]
theorem weierstrassZeta_cot_series {z : ℂ} (hz : z ∉ H.lattice) :
    HasSum (fun n : ℕ ↦ π / (2 * H.ω₁) *
        (Complex.cot (π * (z + 2 * (n + 1) * H.ω₃) / (2 * H.ω₁)) +
          Complex.cot (π * (z - 2 * (n + 1) * H.ω₃) / (2 * H.ω₁))))
      (H.weierstrassZeta z - H.eta 1 * z / H.ω₁ -
        π / (2 * H.ω₁) * Complex.cot (π * z / (2 * H.ω₁))) := by
  sorry

/-- DLMF 23.8.5: `η₁ = (π²/(2ω₁)) (1/6 + ∑_{n≥1} csc²(nπω₃/ω₁))`. -/
@[dlmf 23.8.E5]
theorem eta_one_csc_series :
    HasSum (fun n : ℕ ↦ π ^ 2 / (2 * H.ω₁) *
        (1 / Complex.sin ((n + 1 : ℂ) * π * H.ω₃ / H.ω₁) ^ 2))
      (H.eta 1 - π ^ 2 / (2 * H.ω₁) * (1 / 6)) := by
  sorry

/-! ### Infinite products (§23.8(iii)) -/

/-- DLMF 23.8.6: `σ(z) = (2ω₁/π) exp(η₁z²/(2ω₁)) sin(πz/(2ω₁))
∏_{n≥1} (1 - 2q^{2n}cos(πz/ω₁) + q^{4n})/(1 - q^{2n})²`, `z ∈ ℂ`. -/
@[dlmf 23.8.E6]
theorem weierstrassSigma_prod (z : ℂ) :
    HasProd (fun n : ℕ ↦ (1 - 2 * H.nome ^ (2 * (n + 1)) * Complex.cos (π * z / H.ω₁) +
        H.nome ^ (4 * (n + 1))) / (1 - H.nome ^ (2 * (n + 1))) ^ 2)
      (H.weierstrassSigma z /
        (2 * H.ω₁ / π * cexp (H.eta 1 * z ^ 2 / (2 * H.ω₁)) * Complex.sin (π * z / (2 * H.ω₁)))) ∧
    H.weierstrassSigma z = 2 * H.ω₁ / π * cexp (H.eta 1 * z ^ 2 / (2 * H.ω₁)) *
      Complex.sin (π * z / (2 * H.ω₁)) *
      ∏' n : ℕ, (1 - 2 * H.nome ^ (2 * (n + 1)) * Complex.cos (π * z / H.ω₁) +
        H.nome ^ (4 * (n + 1))) / (1 - H.nome ^ (2 * (n + 1))) ^ 2 := by
  sorry

/-- DLMF 23.8.7: `σ(z) = (2ω₁/π) exp(η₁z²/(2ω₁)) sin(πz/(2ω₁))
∏_{n≥1} sin(π(2nω₃ + z)/(2ω₁)) sin(π(2nω₃ - z)/(2ω₁))/sin²(πnω₃/ω₁)`, `z ∈ ℂ`. -/
@[dlmf 23.8.E7]
theorem weierstrassSigma_sin_prod (z : ℂ) :
    Multipliable (fun n : ℕ ↦ Complex.sin (π * (2 * (n + 1) * H.ω₃ + z) / (2 * H.ω₁)) *
        Complex.sin (π * (2 * (n + 1) * H.ω₃ - z) / (2 * H.ω₁)) /
          Complex.sin (π * (n + 1) * H.ω₃ / H.ω₁) ^ 2) ∧
    H.weierstrassSigma z = 2 * H.ω₁ / π * cexp (H.eta 1 * z ^ 2 / (2 * H.ω₁)) *
      Complex.sin (π * z / (2 * H.ω₁)) *
      ∏' n : ℕ, Complex.sin (π * (2 * (n + 1) * H.ω₃ + z) / (2 * H.ω₁)) *
        Complex.sin (π * (2 * (n + 1) * H.ω₃ - z) / (2 * H.ω₁)) /
          Complex.sin (π * (n + 1) * H.ω₃ / H.ω₁) ^ 2 := by
  sorry

end HalfPeriods

/-! ### Laurent series (§23.9) -/

/-- The Laurent coefficients `c_n = (2n - 1) ∑_{w ∈ 𝕃∖{0}} w^{-2n}` (DLMF 23.9.1), `n ≥ 2`
(Mathlib's `G (2n)` sums over `𝕃` with the `w = 0` term `0`). -/
@[dlmf 23.9.E1]
def laurentCoeff (L : PeriodPair) (n : ℕ) : ℂ := (2 * n - 1) * L.G (2 * n)

/-- DLMF 23.9.4: `c₂ = g₂/20`. -/
@[dlmf 23.9.E4]
theorem laurentCoeff_two (L : PeriodPair) : laurentCoeff L 2 = L.g₂ / 20 := by
  simp only [laurentCoeff, PeriodPair.g₂]; push_cast; ring

/-- DLMF 23.9.4: `c₃ = g₃/28`. -/
@[dlmf 23.9.E4]
theorem laurentCoeff_three (L : PeriodPair) : laurentCoeff L 3 = L.g₃ / 28 := by
  simp only [laurentCoeff, PeriodPair.g₃]; push_cast; ring

/-- DLMF 23.9.2: `℘(z) = 1/z² + ∑_{n≥2} c_n z^{2n-2}` for `0 < |z| < |z₀|`, `z₀` a nearest
nonzero lattice point. -/
@[dlmf 23.9.E2]
theorem weierstrassP_laurent (L : PeriodPair) {z : ℂ} (hz0 : z ≠ 0)
    (hz : ∀ w ∈ L.lattice, w ≠ 0 → ‖z‖ < ‖w‖) :
    HasSum (fun n : ℕ ↦ laurentCoeff L (n + 2) * z ^ (2 * (n + 2) - 2)) (℘[L] z - 1 / z ^ 2) := by
  sorry

/-- DLMF 23.9.3: `ζ(z) = 1/z - ∑_{n≥2} c_n z^{2n-1}/(2n - 1)` for `0 < |z| < |z₀|`. -/
@[dlmf 23.9.E3]
theorem weierstrassZeta_laurent (L : PeriodPair) {z : ℂ} (hz0 : z ≠ 0)
    (hz : ∀ w ∈ L.lattice, w ≠ 0 → ‖z‖ < ‖w‖) :
    HasSum (fun n : ℕ ↦ -(laurentCoeff L (n + 2) / (2 * (n + 2) - 1) * z ^ (2 * (n + 2) - 1)))
      (weierstrassZeta L z - 1 / z) := by
  sorry

/-- DLMF 23.9.5: `c_n = 3/((2n + 1)(n - 3)) ∑_{m=2}^{n-2} c_m c_{n-m}`, `n ≥ 4`. -/
@[dlmf 23.9.E5]
theorem laurentCoeff_recursion (L : PeriodPair) {n : ℕ} (hn : 4 ≤ n) :
    laurentCoeff L n = 3 / ((2 * n + 1) * (n - 3)) *
      ∑ m ∈ Finset.Icc 2 (n - 2), laurentCoeff L m * laurentCoeff L (n - m) := by
  sorry

namespace HalfPeriods

variable (H : HalfPeriods)

/-- DLMF 23.9.6: as `t → 0`, for `j = 1, 2, 3`,
`℘(ω_j + t) = e_j + (3e_j² - 5c₂)t² + (10c₂e_j + 21c₃)t⁴ + (7c₂e_j² + 21c₃e_j + 5c₂²)t⁶ + O(t⁸)`. -/
@[dlmf 23.9.E6]
theorem weierstrassP_halfPeriod_expansion {j : ℕ} (hj : j ∈ ({1, 2, 3} : Finset ℕ)) :
    (fun t : ℂ ↦ H.weierstrassP (H.halfPeriod j + t) -
      (H.e j + (3 * H.e j ^ 2 - 5 * laurentCoeff H.periodPair 2) * t ^ 2 +
        (10 * laurentCoeff H.periodPair 2 * H.e j + 21 * laurentCoeff H.periodPair 3) * t ^ 4 +
        (7 * laurentCoeff H.periodPair 2 * H.e j ^ 2 +
          21 * laurentCoeff H.periodPair 3 * H.e j +
          5 * laurentCoeff H.periodPair 2 ^ 2) * t ^ 6)) =O[nhds 0] fun t ↦ t ^ 8 := by
  sorry

end HalfPeriods

/-- The coefficients `a_{m,n}` of the power series of `σ` (DLMF 23.9.8): `a_{0,0} = 1`,
`a_{m,n} = 0` if `m < 0` or `n < 0`, and for `(m, n) ≠ (0, 0)`
`a_{m,n} = 3(m+1)a_{m+1,n-1} + (16/3)(n+1)a_{m-2,n+1} - (1/3)(2m+3n-1)(4m+6n-1)a_{m-1,n}`.
The recursion is well founded in the weight `2m + 3n`. -/
@[dlmf 23.9.E8]
def sigmaCoeff (m n : ℕ) : ℚ :=
  if m = 0 ∧ n = 0 then 1 else
    (if hn : 1 ≤ n then 3 * (m + 1) * sigmaCoeff (m + 1) (n - 1) else 0) +
    (if hm : 2 ≤ m then 16 / 3 * (n + 1) * sigmaCoeff (m - 2) (n + 1) else 0) -
    (if hm' : 1 ≤ m then 1 / 3 * (2 * m + 3 * n - 1) * (4 * m + 6 * n - 1) *
      sigmaCoeff (m - 1) n else 0)
termination_by 2 * m + 3 * n
decreasing_by all_goals omega

/-- DLMF 23.9.7: `σ(z) = ∑_{m,n≥0} a_{m,n} (10c₂)^m (56c₃)^n z^{4m+6n+1}/(4m+6n+1)!`, `z ∈ ℂ`. -/
@[dlmf 23.9.E7]
theorem weierstrassSigma_series (L : PeriodPair) (z : ℂ) :
    HasSum (fun p : ℕ × ℕ ↦ (sigmaCoeff p.1 p.2 : ℂ) * (10 * laurentCoeff L 2) ^ p.1 *
        (56 * laurentCoeff L 3) ^ p.2 * z ^ (4 * p.1 + 6 * p.2 + 1) /
          ((4 * p.1 + 6 * p.2 + 1).factorial : ℂ))
      (weierstrassSigma L z) := by
  sorry

end DLMF.Weierstrass
