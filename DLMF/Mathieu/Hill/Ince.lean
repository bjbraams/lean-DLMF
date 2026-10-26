/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.Hill.Defs
public import DLMF.Mathieu.Basic
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The equations of Whittaker–Hill and Ince (DLMF §28.31)

Statements of DLMF §28.31 for the definitions in `DLMF.Mathieu.Hill.Defs`: the reduction of
the Whittaker–Hill equation 28.31.1 to Ince's equation 28.31.3 (28.31.2), the Fourier-series
solutions and their coefficient recurrences (28.31.4–28.31.9), the Ince polynomials
`C_p^m`, `S_p^m` and their eigenvalues `a_p^m`, `b_p^m` (28.31.10–28.31.15), and the
paraboloidal wave functions `hc_p^m`, `hs_p^m` (28.31.16–28.31.24 and the asymptotic
behaviour). The limits 28.31.14–28.31.15 use the Mathieu functions `ce_m`, `se_m` and
eigenvalues `a_m`, `b_m` of `DLMF.Mathieu.Basic` (real `q`).

The admissible indices are `m ≤ p`, `m ≡ p (mod 2)` (and `m ≥ 1` for `S_p^m`, `hs_p^m`), as in
DLMF 28.31.10–28.31.11 (`m = 0, 1, …, n` with `p = 2n`, `2n + 1`, `2n + 2`).

**Correction (§28.31(iii), Asymptotic Behavior, second paragraph).** DLMF says that for
`ξ > 0` the functions `hc_p^m(z, -ξ)`, `hs_p^m(z, -ξ)` behave as multiples of
`exp(¼ξ cos 2z) (cos z)^{-p-2}` as `z → ½π ± i∞`, and all other periodic solutions as
multiples of `exp(-¼ξ cos 2z) (cos z)^p`. By the reflection formulas 28.31.19–28.31.20
(`z ↦ ½π - z`, under which `cos 2z ↦ -cos 2z` and `cos z ↦ sin z`) and the first paragraph,
the correct factors are `exp(¼ξ cos 2z) (sin z)^p` for `hc_p^m(z, -ξ)`, `hs_p^m(z, -ξ)`, and
`exp(-¼ξ cos 2z) (sin z)^{-p-2}` for the other periodic solutions. Numerically
(`ξ = 0.8`, `p = 2, 3, 4`, all `m`, `z = ½π + iy`, `y = 2, 3, 4`), the ratio
`hc_p^m(z, -ξ) / (exp(¼ξ cos 2z) (sin z)^p)` converges (e.g. `-0.416, -0.472, -0.480` for
`hc_2^0`) while the ratio with DLMF's factor `exp(¼ξ cos 2z) (cos z)^{-p-2}` grows like
`e^{(2p+2)y}`. The corrected form is acquired (`paraboloidal_asymptotic_neg`).

All other formulas of §28.31 were checked: 28.31.3 and the recurrences 28.31.6–28.31.9
symbolically (sympy), and 28.31.13 and the reflection formulas 28.31.19–28.31.20 numerically
(finite eigenproblems for `p ≤ 6`, `ξ = 0.8`).
-/

@[expose] public noncomputable section

open Complex Set Filter MeasureTheory intervalIntegral
open scoped Topology Classical

namespace DLMF.Mathieu

/-! ### §28.31(i)–(ii) Whittaker–Hill and Ince equations -/

/-- `cos 4z = 1 - 2 sin² 2z`. -/
theorem m28b_cos_four (z : ℂ) : Complex.cos (4 * z) = 1 - 2 * Complex.sin (2 * z) ^ 2 := by
  rw [show (4 : ℂ) * z = 2 * (2 * z) by ring, Complex.cos_two_mul]
  have := Complex.sin_sq_add_cos_sq (2 * z)
  linear_combination (2 : ℂ) * this

/-- The derivative of `-ξ cos(2z)/4`. -/
theorem m28b_hasDerivAt_g (ξ z : ℂ) :
    HasDerivAt (fun z => -(ξ * Complex.cos (2 * z)) / 4) (ξ * Complex.sin (2 * z) / 2) z := by
  have h2 : HasDerivAt (fun z : ℂ => 2 * z) 2 z := by
    simpa using (hasDerivAt_id z).const_mul (2 : ℂ)
  have := ((h2.ccos).const_mul ξ).neg.div_const 4
  convert this using 1; ring

/-- The derivative of `ξ sin(2z)/2`. -/
theorem m28b_hasDerivAt_g' (ξ z : ℂ) :
    HasDerivAt (fun z => ξ * Complex.sin (2 * z) / 2) (ξ * Complex.cos (2 * z)) z := by
  have h2 : HasDerivAt (fun z : ℂ => 2 * z) 2 z := by
    simpa using (hasDerivAt_id z).const_mul (2 : ℂ)
  have := ((h2.csin).const_mul ξ).div_const 2
  convert this using 1; ring

/-- **Reduction to Ince's equation** (DLMF 28.31.2–28.31.3): with `ξ² = -4k²c²`,
`A = η - ξ²/8`, `B = -(p+1)ξ` and `W(z) = w(z) exp(-¼ξ cos 2z)`, `W` solves the Whittaker–Hill
equation 28.31.1 iff `w` solves Ince's equation 28.31.3. (DLMF makes the substitution for
`k² < 0`; the algebra holds for all complex parameters.) Proved. -/
@[dlmf 28.31.E2]
theorem isWhittakerHillSolution_iff_isInceSolution {k c ξ η p : ℂ}
    (hξ : ξ ^ 2 = -4 * k ^ 2 * c ^ 2) {w : ℂ → ℂ} :
    IsWhittakerHillSolution (η - ξ ^ 2 / 8) (-(p + 1) * ξ) k c
        (fun z => w z * Complex.exp (-(ξ * Complex.cos (2 * z)) / 4)) ↔
      IsInceSolution ξ η p w := by
  set g : ℂ → ℂ := fun z => -(ξ * Complex.cos (2 * z)) / 4
  set g' : ℂ → ℂ := fun z => ξ * Complex.sin (2 * z) / 2
  set E : ℂ → ℂ := fun z => Complex.exp (g z)
  have hE : ∀ z, HasDerivAt E (E z * g' z) z := fun z => (m28b_hasDerivAt_g ξ z).cexp
  have hF : ∀ z, HasDerivAt (fun z => Complex.exp (-g z)) (Complex.exp (-g z) * -g' z) z :=
    fun z => (m28b_hasDerivAt_g ξ z).neg.cexp
  have hg' : ∀ z, HasDerivAt g' (ξ * Complex.cos (2 * z)) z := m28b_hasDerivAt_g' ξ
  have hEF : ∀ z, E z * Complex.exp (-g z) = 1 := fun z => by
    simp only [E]; rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  constructor
  · rintro ⟨hWd, hW⟩
    set W : ℂ → ℂ := fun z => w z * E z
    have hw : w = fun z => W z * Complex.exp (-g z) := by
      funext z; simp only [W]; rw [mul_assoc, hEF, mul_one]
    have hWd' : ∀ z, HasDerivAt W (deriv W z) z := fun z => (hWd z).hasDerivAt
    have hw' : ∀ z, HasDerivAt w ((deriv W z - g' z * W z) * Complex.exp (-g z)) z := by
      intro z; rw [hw]
      convert (hWd' z).mul (hF z) using 1; ring
    have hdw : deriv w = fun z => (deriv W z - g' z * W z) * Complex.exp (-g z) :=
      funext fun z => (hw' z).deriv
    refine ⟨fun z => (hw' z).differentiableAt, fun z => ?_⟩
    rw [hdw]
    have := (((hW z).sub ((hg' z).mul (hWd' z))).mul (hF z))
    convert this using 1
    have h4 := m28b_cos_four z
    have hwz : w z = W z * Complex.exp (-g z) := congrFun hw z
    rw [hwz]
    simp only [W, g', Pi.sub_apply, Pi.mul_apply]
    rw [h4]
    linear_combination
      (-1/8 * w z * E z * Complex.exp (-g z) * (1 - 2 * Complex.sin (2 * z) ^ 2)) * hξ
  · rintro ⟨hwd, hw⟩
    have hwd' : ∀ z, HasDerivAt w (deriv w z) z := fun z => (hwd z).hasDerivAt
    have hW' : ∀ z, HasDerivAt (fun z => w z * E z) ((deriv w z + w z * g' z) * E z) z := by
      intro z; convert (hwd' z).mul (hE z) using 1; ring
    have hdW : deriv (fun z => w z * E z) = fun z => (deriv w z + w z * g' z) * E z :=
      funext fun z => (hW' z).deriv
    refine ⟨fun z => (hW' z).differentiableAt, fun z => ?_⟩
    rw [hdW]
    have := (((hw z).add ((hwd' z).mul (hg' z))).mul (hE z))
    convert this using 1
    have h4 := m28b_cos_four z
    simp only [g', Pi.mul_apply, Pi.add_apply]
    rw [h4]
    linear_combination (1/8 * w z * E z * (1 - 2 * Complex.sin (2 * z) ^ 2)) * hξ


/-- **Even Fourier-series solutions, `s = 0`** (DLMF 28.31.4, 28.31.6):
`w(z) = ∑_ℓ A_{2ℓ} cos(2ℓz)` solves Ince's equation iff
`-2ηA₀ + (2+p)ξA₂ = 0`, `pξA₀ + (4-η)A₂ + (½p+2)ξA₄ = 0` and, for `ℓ ≥ 2`,
`(½p-ℓ+1)ξA_{2ℓ-2} + (4ℓ²-η)A_{2ℓ} + (½p+ℓ+1)ξA_{2ℓ+2} = 0`. -/
@[dlmf 28.31.E4, dlmf 28.31.E6]
theorem isInceSolution_cos_even_iff {ξ η p : ℂ} {A : ℕ → ℂ} (hA : IsEntireFourierCoeff A) :
    IsInceSolution ξ η p (fun z => ∑' ℓ : ℕ, A (2 * ℓ) * Complex.cos ((2 * ℓ : ℕ) * z)) ↔
      (-2 * η * A 0 + (2 + p) * ξ * A 2 = 0) ∧
      (p * ξ * A 0 + (4 - η) * A 2 + (p / 2 + 2) * ξ * A 4 = 0) ∧
      ∀ ℓ : ℕ, 2 ≤ ℓ → (p / 2 - ℓ + 1) * ξ * A (2 * ℓ - 2) + (4 * ℓ ^ 2 - η) * A (2 * ℓ) +
        (p / 2 + ℓ + 1) * ξ * A (2 * ℓ + 2) = 0 := by
  sorry

/-- **Even Fourier-series solutions, `s = 1`** (DLMF 28.31.4, 28.31.7):
`w(z) = ∑_ℓ A_{2ℓ+1} cos((2ℓ+1)z)` solves Ince's equation iff
`(1-η+(½p+½)ξ)A₁ + (½p+3/2)ξA₃ = 0` and, for `ℓ ≥ 1`,
`(½p-ℓ+½)ξA_{2ℓ-1} + ((2ℓ+1)²-η)A_{2ℓ+1} + (½p+ℓ+3/2)ξA_{2ℓ+3} = 0`. -/
@[dlmf 28.31.E4, dlmf 28.31.E7]
theorem isInceSolution_cos_odd_iff {ξ η p : ℂ} {A : ℕ → ℂ} (hA : IsEntireFourierCoeff A) :
    IsInceSolution ξ η p (fun z => ∑' ℓ : ℕ, A (2 * ℓ + 1) * Complex.cos ((2 * ℓ + 1 : ℕ) * z)) ↔
      ((1 - η + (p / 2 + 1 / 2) * ξ) * A 1 + (p / 2 + 3 / 2) * ξ * A 3 = 0) ∧
      ∀ ℓ : ℕ, 1 ≤ ℓ → (p / 2 - ℓ + 1 / 2) * ξ * A (2 * ℓ - 1) +
        ((2 * ℓ + 1) ^ 2 - η) * A (2 * ℓ + 1) + (p / 2 + ℓ + 3 / 2) * ξ * A (2 * ℓ + 3) = 0 := by
  sorry

/-- **Odd Fourier-series solutions, `s = 1`** (DLMF 28.31.5, 28.31.8):
`w(z) = ∑_ℓ B_{2ℓ+1} sin((2ℓ+1)z)` solves Ince's equation iff
`(1-η-(½p+½)ξ)B₁ + (½p+3/2)ξB₃ = 0` and, for `ℓ ≥ 1`,
`(½p-ℓ+½)ξB_{2ℓ-1} + ((2ℓ+1)²-η)B_{2ℓ+1} + (½p+ℓ+3/2)ξB_{2ℓ+3} = 0`. -/
@[dlmf 28.31.E5, dlmf 28.31.E8]
theorem isInceSolution_sin_odd_iff {ξ η p : ℂ} {B : ℕ → ℂ} (hB : IsEntireFourierCoeff B) :
    IsInceSolution ξ η p (fun z => ∑' ℓ : ℕ, B (2 * ℓ + 1) * Complex.sin ((2 * ℓ + 1 : ℕ) * z)) ↔
      ((1 - η - (p / 2 + 1 / 2) * ξ) * B 1 + (p / 2 + 3 / 2) * ξ * B 3 = 0) ∧
      ∀ ℓ : ℕ, 1 ≤ ℓ → (p / 2 - ℓ + 1 / 2) * ξ * B (2 * ℓ - 1) +
        ((2 * ℓ + 1) ^ 2 - η) * B (2 * ℓ + 1) + (p / 2 + ℓ + 3 / 2) * ξ * B (2 * ℓ + 3) = 0 := by
  sorry

/-- **Odd Fourier-series solutions, `s = 2`** (DLMF 28.31.5, 28.31.9):
`w(z) = ∑_ℓ B_{2ℓ+2} sin((2ℓ+2)z)` solves Ince's equation iff
`(4-η)B₂ + (½p+2)ξB₄ = 0` and, for `ℓ ≥ 2`,
`(½p-ℓ+1)ξB_{2ℓ-2} + (4ℓ²-η)B_{2ℓ} + (½p+ℓ+1)ξB_{2ℓ+2} = 0`. -/
@[dlmf 28.31.E5, dlmf 28.31.E9]
theorem isInceSolution_sin_even_iff {ξ η p : ℂ} {B : ℕ → ℂ} (hB : IsEntireFourierCoeff B) :
    IsInceSolution ξ η p (fun z => ∑' ℓ : ℕ, B (2 * ℓ + 2) * Complex.sin ((2 * ℓ + 2 : ℕ) * z)) ↔
      ((4 - η) * B 2 + (p / 2 + 2) * ξ * B 4 = 0) ∧
      ∀ ℓ : ℕ, 2 ≤ ℓ → (p / 2 - ℓ + 1) * ξ * B (2 * ℓ - 2) + (4 * ℓ ^ 2 - η) * B (2 * ℓ) +
        (p / 2 + ℓ + 1) * ξ * B (2 * ℓ + 2) = 0 := by
  sorry

/-! ### Ince polynomials (§28.31(ii)) -/

/-- **Ince polynomials `C_p^m` and eigenvalues `a_p^m`** (DLMF §28.31(ii), 28.31.10, 28.31.12):
for a nonnegative integer `p`, real `ξ` and `m ≤ p`, `m ≡ p (mod 2)`, `C_p^m(·, ξ)` is a cosine
Ince polynomial solving 28.31.3 with `η = a_p^m(ξ)`, with exactly `m` zeros in `[0, π)`, all
simple, normalized by 28.31.12 and positive at `0`; the `a_p^m(ξ)` are real and distinct; and
every (complex) `η` admitting a nontrivial cosine Ince polynomial solution is one of them. -/
@[dlmf 28.31.ii, dlmf 28.31.E10, dlmf 28.31.E12]
theorem inceC_spec {p m : ℕ} (hm : m ≤ p) (hpm : m % 2 = p % 2) (ξ : ℝ) :
    IsInceCosPoly p (fun z => inceC p m z ξ) ∧
      IsInceSolution ξ (inceA p m ξ) p (fun z => inceC p m z ξ) ∧
      zerosIco (fun z => inceC p m z ξ) = m ∧
      (∀ x : ℝ, x ∈ Ico 0 Real.pi → inceC p m x ξ = 0 → deriv (fun z => inceC p m z ξ) x ≠ 0) ∧
      (1 / Real.pi : ℂ) * ∫ x in (0 : ℝ)..2 * Real.pi, inceC p m x ξ ^ 2 = 1 ∧
      0 < (inceC p m 0 ξ).re ∧
      (∀ m' : ℕ, m' ≤ p → m' % 2 = p % 2 → m' ≠ m → inceA p m' ξ ≠ inceA p m ξ) ∧
      (∀ η : ℂ, (∃ f, IsInceCosPoly p f ∧ (∃ z, f z ≠ 0) ∧ IsInceSolution ξ η p f) →
        ∃ m' : ℕ, m' ≤ p ∧ m' % 2 = p % 2 ∧ η = inceA p m' ξ) := by
  sorry

/-- **Ince polynomials `S_p^m` and eigenvalues `b_p^m`** (DLMF §28.31(ii), 28.31.11,
28.31.12): for `1 ≤ m ≤ p`, `m ≡ p (mod 2)` and real `ξ`, `S_p^m(·, ξ)` is a sine Ince
polynomial solving 28.31.3 with `η = b_p^m(ξ)`, with exactly `m` zeros in `[0, π)` (including
`z = 0`), all simple, normalized by 28.31.12 with `S_p^m'(0, ξ) > 0`; the `b_p^m(ξ)` are real
and distinct; and every `η` admitting a nontrivial sine Ince polynomial solution is one of
them. -/
@[dlmf 28.31.ii, dlmf 28.31.E11, dlmf 28.31.E12]
theorem inceS_spec {p m : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ p) (hpm : m % 2 = p % 2) (ξ : ℝ) :
    IsInceSinPoly p (fun z => inceS p m z ξ) ∧
      IsInceSolution ξ (inceB p m ξ) p (fun z => inceS p m z ξ) ∧
      zerosIco (fun z => inceS p m z ξ) = m ∧
      (∀ x : ℝ, x ∈ Ico 0 Real.pi → inceS p m x ξ = 0 → deriv (fun z => inceS p m z ξ) x ≠ 0) ∧
      (1 / Real.pi : ℂ) * ∫ x in (0 : ℝ)..2 * Real.pi, inceS p m x ξ ^ 2 = 1 ∧
      0 < (deriv (fun z => inceS p m z ξ) 0).re ∧
      (∀ m' : ℕ, 1 ≤ m' → m' ≤ p → m' % 2 = p % 2 → m' ≠ m → inceB p m' ξ ≠ inceB p m ξ) ∧
      (∀ η : ℂ, (∃ f, IsInceSinPoly p f ∧ (∃ z, f z ≠ 0) ∧ IsInceSolution ξ η p f) →
        ∃ m' : ℕ, 1 ≤ m' ∧ m' ≤ p ∧ m' % 2 = p % 2 ∧ η = inceB p m' ξ) := by
  sorry

/-- **Limits as `ξ → 0`** (DLMF 28.31.13): `C_p^0(x, ξ) → 1/√2`, `C_p^m(x, ξ) → cos(mx)`,
`S_p^m(x, ξ) → sin(mx)` (`m ≠ 0`), and `a_p^m(ξ), b_p^m(ξ) → m²`, for fixed real `x` and
admissible `p, m`. -/
@[dlmf 28.31.E13]
theorem ince_tendsto_xi_zero {p m : ℕ} (hm : m ≤ p) (hpm : m % 2 = p % 2) (x : ℝ) :
    (m = 0 → Tendsto (fun ξ : ℝ => inceC p 0 x ξ) (𝓝 0) (𝓝 (1 / Real.sqrt 2 : ℝ))) ∧
      (m ≠ 0 → Tendsto (fun ξ : ℝ => inceC p m x ξ) (𝓝 0) (𝓝 (Complex.cos (m * x)))) ∧
      (m ≠ 0 → Tendsto (fun ξ : ℝ => inceS p m x ξ) (𝓝 0) (𝓝 (Complex.sin (m * x)))) ∧
      Tendsto (fun ξ : ℝ => inceA p m ξ) (𝓝 0) (𝓝 ((m : ℝ) ^ 2)) ∧
      (m ≠ 0 → Tendsto (fun ξ : ℝ => inceB p m ξ) (𝓝 0) (𝓝 ((m : ℝ) ^ 2))) := by
  sorry

/-- **Limit to Mathieu functions** (DLMF 28.31.14–28.31.15): if `p → ∞` (through integers
`≡ m mod 2`) and `ξ → 0` with `pξ → 2q` (real `q`), then `C_p^m(x, ξ) → ce_m(x, q)`,
`S_p^m(x, ξ) → se_m(x, q)` (`m ≥ 1`), `a_p^m(ξ) → a_m(q)` and `b_p^m(ξ) → b_m(q)` (`m ≥ 1`). -/
@[dlmf 28.31.E14, dlmf 28.31.E15]
theorem ince_tendsto_mathieu {m : ℕ} {q : ℝ} {P : ℕ → ℕ} {Ξ : ℕ → ℝ}
    (hP : Tendsto P atTop atTop) (hPm : ∀ j, P j % 2 = m % 2) (hΞ : Tendsto Ξ atTop (𝓝 0))
    (hPΞ : Tendsto (fun j => (P j : ℝ) * Ξ j) atTop (𝓝 (2 * q))) (x : ℝ) :
    Tendsto (fun j => inceC (P j) m x (Ξ j)) atTop (𝓝 (mathieuCe m x q)) ∧
      Tendsto (fun j => inceA (P j) m (Ξ j)) atTop (𝓝 (mathieuA m q)) ∧
      (1 ≤ m → Tendsto (fun j => inceS (P j) m x (Ξ j)) atTop (𝓝 (mathieuSe m x q))) ∧
      (1 ≤ m → Tendsto (fun j => inceB (P j) m (Ξ j)) atTop (𝓝 (mathieuB m q))) := by
  sorry

/-! ### §28.31(iii) Paraboloidal wave functions -/

/-- **Differential equation of the paraboloidal wave functions** (DLMF 28.31.18):
`w'' + (η - ⅛ξ² - (p+1)ξ cos 2z + ⅛ξ² cos 4z) w = 0` with `η = a_p^m(ξ)` for `hc_p^m` and
`η = b_p^m(ξ)` for `hs_p^m`; this is the Whittaker–Hill equation 28.31.1 with
`A = η - ξ²/8`, `B = -(p+1)ξ`, `k = iξ/2`, `c = 1`. Proved from 28.31.2 and the admitted
`inceC_spec`, `inceS_spec`. -/
@[dlmf 28.31.E18]
theorem paraboloidal_isWhittakerHillSolution {p m : ℕ} (hm : m ≤ p) (hpm : m % 2 = p % 2)
    (ξ : ℝ) :
    IsWhittakerHillSolution (inceA p m ξ - (ξ : ℂ) ^ 2 / 8) (-((p : ℂ) + 1) * ξ) (I * ξ / 2) 1
        (fun z => paraboloidalHc p m z ξ) ∧
      (1 ≤ m → IsWhittakerHillSolution (inceB p m ξ - (ξ : ℂ) ^ 2 / 8) (-((p : ℂ) + 1) * ξ)
        (I * ξ / 2) 1 (fun z => paraboloidalHs p m z ξ)) := by
  have hk : ((ξ : ℂ)) ^ 2 = -4 * (I * ξ / 2) ^ 2 * 1 ^ 2 := by
    ring_nf; rw [Complex.I_sq]; ring
  have hfun : ∀ (F : ℂ → ℂ), (fun z => F z * Complex.exp (-((ξ : ℂ) * Complex.cos (2 * z)) / 4)) =
      fun z => Complex.exp (-((ξ : ℂ) * Complex.cos (2 * z)) / 4) * F z :=
    fun F => funext fun z => mul_comm _ _
  refine ⟨?_, fun hm1 => ?_⟩
  · have := (isWhittakerHillSolution_iff_isInceSolution (η := (inceA p m ξ : ℂ)) (p := (p : ℂ))
      hk).mpr (inceC_spec hm hpm ξ).2.1
    rw [hfun] at this
    exact this
  · have := (isWhittakerHillSolution_iff_isInceSolution (η := (inceB p m ξ : ℂ)) (p := (p : ℂ))
      hk).mpr (inceS_spec hm1 hm hpm ξ).2.1
    rw [hfun] at this
    exact this

/-- **Change of sign of `ξ`** (DLMF 28.31.19):
`hc_{2n}^{2m}(z, -ξ) = (-1)^m hc_{2n}^{2m}(½π - z, ξ)` and
`hc_{2n+1}^{2m+1}(z, -ξ) = (-1)^m hs_{2n+1}^{2m+1}(½π - z, ξ)`, `m ≤ n`. -/
@[dlmf 28.31.E19]
theorem paraboloidalHc_neg_xi {n m : ℕ} (hm : m ≤ n) (z : ℂ) (ξ : ℝ) :
    paraboloidalHc (2 * n) (2 * m) z (-ξ) =
        (-1) ^ m * paraboloidalHc (2 * n) (2 * m) (Real.pi / 2 - z) ξ ∧
      paraboloidalHc (2 * n + 1) (2 * m + 1) z (-ξ) =
        (-1) ^ m * paraboloidalHs (2 * n + 1) (2 * m + 1) (Real.pi / 2 - z) ξ := by
  sorry

/-- **Change of sign of `ξ`** (DLMF 28.31.20):
`hs_{2n+1}^{2m+1}(z, -ξ) = (-1)^m hc_{2n+1}^{2m+1}(½π - z, ξ)` and
`hs_{2n+2}^{2m+2}(z, -ξ) = (-1)^m hs_{2n+2}^{2m+2}(½π - z, ξ)`, `m ≤ n`. -/
@[dlmf 28.31.E20]
theorem paraboloidalHs_neg_xi {n m : ℕ} (hm : m ≤ n) (z : ℂ) (ξ : ℝ) :
    paraboloidalHs (2 * n + 1) (2 * m + 1) z (-ξ) =
        (-1) ^ m * paraboloidalHc (2 * n + 1) (2 * m + 1) (Real.pi / 2 - z) ξ ∧
      paraboloidalHs (2 * n + 2) (2 * m + 2) z (-ξ) =
        (-1) ^ m * paraboloidalHs (2 * n + 2) (2 * m + 2) (Real.pi / 2 - z) ξ := by
  sorry

/-- **Orthogonality** (DLMF 28.31.21): for `m₁ ≠ m₂` (admissible for `p`),
`∫₀^{2π} hc_p^{m₁} hc_p^{m₂} dx = ∫₀^{2π} hs_p^{m₁} hs_p^{m₂} dx = 0`. -/
@[dlmf 28.31.E21]
theorem integral_paraboloidal_orthogonal {p m₁ m₂ : ℕ} (h₁ : m₁ ≤ p) (h₁' : m₁ % 2 = p % 2)
    (h₂ : m₂ ≤ p) (h₂' : m₂ % 2 = p % 2) (hne : m₁ ≠ m₂) (ξ : ℝ) :
    ∫ x in (0 : ℝ)..2 * Real.pi, paraboloidalHc p m₁ x ξ * paraboloidalHc p m₂ x ξ = 0 ∧
      (1 ≤ m₁ → 1 ≤ m₂ →
        ∫ x in (0 : ℝ)..2 * Real.pi, paraboloidalHs p m₁ x ξ * paraboloidalHs p m₂ x ξ = 0) := by
  sorry

/-- **Double orthogonality of `hc`** (DLMF 28.31.22): for real `ξ ≠ 0` and admissible
`(p₁, m₁) ≠ (p₂, m₂)`, with `u₀ = 0` (`ξ > 0`) or `u₀ = ½π` (`ξ < 0`),
`∫_{u₀}^{u₀+i∞} ∫₀^{2π} hc_{p₁}^{m₁}(u) hc_{p₁}^{m₁}(v) hc_{p₂}^{m₂}(u) hc_{p₂}^{m₂}(v)
(cos 2u - cos 2v) dv du = 0`; the `u`-integral is written as `∫₀^∞ ⋯ dt` with `u = u₀ + it`
(the factor `du = i dt` is dropped). -/
@[dlmf 28.31.E22]
theorem paraboloidalHc_double_orthogonal {ξ : ℝ} (hξ : ξ ≠ 0) {p₁ m₁ p₂ m₂ : ℕ}
    (h₁ : m₁ ≤ p₁ ∧ m₁ % 2 = p₁ % 2) (h₂ : m₂ ≤ p₂ ∧ m₂ % 2 = p₂ % 2)
    (hne : p₁ ≠ p₂ ∨ m₁ ≠ m₂) :
    let u₀ : ℂ := if 0 < ξ then 0 else (Real.pi / 2 : ℝ)
    ∫ t in Ioi (0 : ℝ), ∫ v in (0 : ℝ)..2 * Real.pi,
      paraboloidalHc p₁ m₁ (u₀ + I * t) ξ * paraboloidalHc p₁ m₁ v ξ *
        paraboloidalHc p₂ m₂ (u₀ + I * t) ξ * paraboloidalHc p₂ m₂ v ξ *
        (Complex.cos (2 * (u₀ + I * t)) - Complex.cos (2 * v)) = 0 := by
  sorry

/-- **Double orthogonality of `hs`** (DLMF 28.31.23), as 28.31.22 for `hs`
(`m₁, m₂ ≥ 1`). -/
@[dlmf 28.31.E23]
theorem paraboloidalHs_double_orthogonal {ξ : ℝ} (hξ : ξ ≠ 0) {p₁ m₁ p₂ m₂ : ℕ}
    (h₁ : 1 ≤ m₁ ∧ m₁ ≤ p₁ ∧ m₁ % 2 = p₁ % 2) (h₂ : 1 ≤ m₂ ∧ m₂ ≤ p₂ ∧ m₂ % 2 = p₂ % 2)
    (hne : p₁ ≠ p₂ ∨ m₁ ≠ m₂) :
    let u₀ : ℂ := if 0 < ξ then 0 else (Real.pi / 2 : ℝ)
    ∫ t in Ioi (0 : ℝ), ∫ v in (0 : ℝ)..2 * Real.pi,
      paraboloidalHs p₁ m₁ (u₀ + I * t) ξ * paraboloidalHs p₁ m₁ v ξ *
        paraboloidalHs p₂ m₂ (u₀ + I * t) ξ * paraboloidalHs p₂ m₂ v ξ *
        (Complex.cos (2 * (u₀ + I * t)) - Complex.cos (2 * v)) = 0 := by
  sorry

/-- **Double orthogonality of `hc` against `hs`** (DLMF 28.31.24), for all admissible
`p₁, m₁` (for `hc`) and `p₂, m₂` (for `hs`). -/
@[dlmf 28.31.E24]
theorem paraboloidalHc_Hs_double_orthogonal {ξ : ℝ} (hξ : ξ ≠ 0) {p₁ m₁ p₂ m₂ : ℕ}
    (h₁ : m₁ ≤ p₁ ∧ m₁ % 2 = p₁ % 2) (h₂ : 1 ≤ m₂ ∧ m₂ ≤ p₂ ∧ m₂ % 2 = p₂ % 2) :
    let u₀ : ℂ := if 0 < ξ then 0 else (Real.pi / 2 : ℝ)
    ∫ t in Ioi (0 : ℝ), ∫ v in (0 : ℝ)..2 * Real.pi,
      paraboloidalHc p₁ m₁ (u₀ + I * t) ξ * paraboloidalHc p₁ m₁ v ξ *
        paraboloidalHs p₂ m₂ (u₀ + I * t) ξ * paraboloidalHs p₂ m₂ v ξ *
        (Complex.cos (2 * (u₀ + I * t)) - Complex.cos (2 * v)) = 0 := by
  sorry

/-- **Asymptotic behaviour, `ξ > 0`** (DLMF §28.31(iii), Asymptotic Behavior, first
paragraph): as `z → ±i∞`, `hc_p^m(z, ξ)` and `hs_p^m(z, ξ)` behave as nonzero multiples of
`exp(-¼ξ cos 2z) (cos z)^p`; every other even or odd `2π`-periodic solution of 28.31.18 (with
any `η`) behaves as a nonzero multiple of `exp(¼ξ cos 2z) (cos z)^{-p-2}`. Here `z = iy`,
`y → ±∞`. -/
@[dlmf 28.31.iii]
theorem paraboloidal_asymptotic_pos {ξ : ℝ} (hξ : 0 < ξ) {p m : ℕ} (hm : m ≤ p)
    (hpm : m % 2 = p % 2) :
    (∀ F : ℂ → ℂ, (F = fun z => paraboloidalHc p m z ξ) ∨
        (1 ≤ m ∧ F = fun z => paraboloidalHs p m z ξ) →
      ∃ C₁ C₂ : ℂ, C₁ ≠ 0 ∧ C₂ ≠ 0 ∧
        Tendsto (fun y : ℝ => F (I * y) /
          (Complex.exp (-(ξ * Complex.cos (2 * (I * y))) / 4) * Complex.cos (I * y) ^ p))
          atTop (𝓝 C₁) ∧
        Tendsto (fun y : ℝ => F (I * y) /
          (Complex.exp (-(ξ * Complex.cos (2 * (I * y))) / 4) * Complex.cos (I * y) ^ p))
          atBot (𝓝 C₂)) ∧
    ∀ (η : ℂ) (W : ℂ → ℂ),
      IsWhittakerHillSolution (η - (ξ : ℂ) ^ 2 / 8) (-((p : ℂ) + 1) * ξ) (I * ξ / 2) 1 W →
      Function.Periodic W (2 * Real.pi) → (W ≠ 0) →
      ((∀ z, W (-z) = W z) ∨ (∀ z, W (-z) = -W z)) →
      (∀ (m' : ℕ) (c : ℂ), W ≠ fun z => c * paraboloidalHc p m' z ξ) →
      (∀ (m' : ℕ) (c : ℂ), W ≠ fun z => c * paraboloidalHs p m' z ξ) →
      ∃ C₁ C₂ : ℂ, C₁ ≠ 0 ∧ C₂ ≠ 0 ∧
        Tendsto (fun y : ℝ => W (I * y) /
          (Complex.exp (ξ * Complex.cos (2 * (I * y)) / 4) * Complex.cos (I * y) ^ (-(p : ℤ) - 2)))
          atTop (𝓝 C₁) ∧
        Tendsto (fun y : ℝ => W (I * y) /
          (Complex.exp (ξ * Complex.cos (2 * (I * y)) / 4) * Complex.cos (I * y) ^ (-(p : ℤ) - 2)))
          atBot (𝓝 C₂) := by
  sorry

/-- **Asymptotic behaviour, `-ξ < 0`** (DLMF §28.31(iii), Asymptotic Behavior, second
paragraph, **corrected**): for `ξ > 0`, as `z → ½π ± i∞`, `hc_p^m(z, -ξ)` and `hs_p^m(z, -ξ)`
behave as nonzero multiples of `exp(¼ξ cos 2z) (sin z)^p` (DLMF prints
`exp(¼ξ cos 2z) (cos z)^{-p-2}`, which is wrong; see the module docstring); the other even or
odd periodic solutions behave as nonzero multiples of `exp(-¼ξ cos 2z) (sin z)^{-p-2}` (DLMF
prints `exp(-¼ξ cos 2z) (cos z)^p`). Here `z = ½π + iy`, `y → ±∞`. -/
@[dlmf 28.31.iii]
theorem paraboloidal_asymptotic_neg {ξ : ℝ} (hξ : 0 < ξ) {p m : ℕ} (hm : m ≤ p)
    (hpm : m % 2 = p % 2) :
    (∀ F : ℂ → ℂ, (F = fun z => paraboloidalHc p m z (-ξ)) ∨
        (1 ≤ m ∧ F = fun z => paraboloidalHs p m z (-ξ)) →
      ∃ C₁ C₂ : ℂ, C₁ ≠ 0 ∧ C₂ ≠ 0 ∧
        Tendsto (fun y : ℝ => F (Real.pi / 2 + I * y) /
          (Complex.exp (ξ * Complex.cos (2 * (Real.pi / 2 + I * y)) / 4) *
            Complex.sin (Real.pi / 2 + I * y) ^ p)) atTop (𝓝 C₁) ∧
        Tendsto (fun y : ℝ => F (Real.pi / 2 + I * y) /
          (Complex.exp (ξ * Complex.cos (2 * (Real.pi / 2 + I * y)) / 4) *
            Complex.sin (Real.pi / 2 + I * y) ^ p)) atBot (𝓝 C₂)) ∧
    ∀ (η : ℂ) (W : ℂ → ℂ),
      IsWhittakerHillSolution (η - (ξ : ℂ) ^ 2 / 8) (((p : ℂ) + 1) * ξ) (I * ξ / 2) 1 W →
      Function.Periodic W (2 * Real.pi) → (W ≠ 0) →
      ((∀ z, W (-z) = W z) ∨ (∀ z, W (-z) = -W z)) →
      (∀ (m' : ℕ) (c : ℂ), W ≠ fun z => c * paraboloidalHc p m' z (-ξ)) →
      (∀ (m' : ℕ) (c : ℂ), W ≠ fun z => c * paraboloidalHs p m' z (-ξ)) →
      ∃ C₁ C₂ : ℂ, C₁ ≠ 0 ∧ C₂ ≠ 0 ∧
        Tendsto (fun y : ℝ => W (Real.pi / 2 + I * y) /
          (Complex.exp (-(ξ * Complex.cos (2 * (Real.pi / 2 + I * y))) / 4) *
            Complex.sin (Real.pi / 2 + I * y) ^ (-(p : ℤ) - 2))) atTop (𝓝 C₁) ∧
        Tendsto (fun y : ℝ => W (Real.pi / 2 + I * y) /
          (Complex.exp (-(ξ * Complex.cos (2 * (Real.pi / 2 + I * y))) / 4) *
            Complex.sin (Real.pi / 2 + I * y) ^ (-(p : ℤ) - 2))) atBot (𝓝 C₂) := by
  sorry

end DLMF.Mathieu
