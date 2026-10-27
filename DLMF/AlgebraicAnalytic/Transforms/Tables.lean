/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AlgebraicAnalytic.Transforms.Laplace
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
public import Mathlib.Analysis.MellinTransform

/-!
# Tables of integral transforms (DLMF §1.14(vii), Tables 1.14.1–1.14.5)

Each row of DLMF Tables 1.14.1 (Fourier transforms, 1.14.1), 1.14.2 (Fourier cosine transforms,
1.14.9), 1.14.3 (Fourier sine transforms, 1.14.10), 1.14.4 (Laplace transforms, 1.14.17) and
1.14.5 (Mellin transforms, 1.14.32) is a theorem here, tagged with the table ID. All rows were
checked numerically (mpmath) before acquisition.

Where the transform integral converges only conditionally (rows 1.14.1.10–11, 1.14.2.8–9,
1.14.3.2, 1.14.3.3, 1.14.3.5, 1.14.3.12, 1.14.3.14) the statement is the limit of the integrals
over `[-R, R]` or `[0, R]` as `R → ∞` (the Lebesgue integral would be Lean's junk value `0`).
Row 1.14.3.13 (`arctan(t/a)`) does not converge even conditionally; DLMF's entry is its Abel
value `lim_{ε→0+} ∫₀^∞ e^{-εt} …`, and it is stated so. Row 1.14.5.4 is a Cauchy principal value
at `x = 1`, as DLMF says.

Parameters are complex where DLMF writes `ℜa > 0` or `|ph a| < …`; principal branches throughout.

**Corrections and precisions.**
* 1.14.2.11: DLMF writes `ln((a² + t²)/(b² + t²))` with `ℜa, ℜb > 0`. With the principal logarithm
  of the quotient the entry is false for some complex `a`, `b` (e.g. `a = 1 + 10i`, `b = 1 - 10i`,
  `x = 0.7`: the integral is `-2.3288i`, the table value `2.3365i`); it holds for
  `ln(a² + t²) - ln(b² + t²)`, which is what is acquired (the two agree for real `a, b > 0`).
* 1.14.4.15: DLMF's condition `ℜ(s + a) > 0` is insufficient (`cosh(at)` is even in `a`; for
  `a = 1`, `s = ½` the integral diverges); the correct condition `ℜs > |ℜa|` is used.
* 1.14.4.16, 1.14.4.17: DLMF gives `ℜs > 0`, which suffices for real `a`; for complex `a` the
  condition is `ℜs > |ℑa|`, used here.
* 1.14.5.3: DLMF gives `ℜs > 1`; the integral converges and the formula holds for `ℜs > 0`
  (stated so, stronger than DLMF). 1.14.5.7 needs `s ≠ 0` in Lean (`π tan(0)/0` is junk `0`, the
  limit value is `π²/2`).

Proved: 1.14.1.9 (Gaussian, from Mathlib's `fourierIntegral_gaussian`), 1.14.4.2, 1.14.4.5,
1.14.4.6 (from 1.14.4.3 and the translation rule 1.14.21) and 1.14.4.7. The other rows are
admitted.
-/

@[expose] public noncomputable section

open MeasureTheory Complex Set Filter Topology
open scoped Nat

namespace DLMF.AlgebraicAnalytic

/-! ### Table 1.14.1: Fourier transforms `(2π)^{-1/2} ∫ f(t) e^{ixt} dt` -/

/-- DLMF Table 1.14.1, row 2: `f = 1` on `|t| < a`, `0` otherwise: `F(x) = √(2/π) sin(ax)/x`
(`a > 0`, `x ≠ 0`). -/
@[dlmf 1.14.T1]
theorem fourierTransform_indicator {a : ℝ} (ha : 0 < a) {x : ℝ} (hx : x ≠ 0) :
    fourierTransform (fun t => (Ioo (-a) a).indicator (fun _ => (1 : ℂ)) t) x =
      (Real.sqrt (2 / Real.pi) : ℂ) * Real.sin (a * x) / x := by
  sorry

/-- DLMF Table 1.14.1, row 3: `e^{-a|t|} ↦ √(2/π) a/(a² + x²)`, `a > 0`. -/
@[dlmf 1.14.T1]
theorem fourierTransform_exp_neg_abs {a : ℝ} (ha : 0 < a) (x : ℝ) :
    fourierTransform (fun t => (Real.exp (-a * |t|) : ℂ)) x =
      (Real.sqrt (2 / Real.pi) : ℂ) * (a / (a ^ 2 + x ^ 2) : ℝ) := by
  sorry

/-- DLMF Table 1.14.1, row 4: `t e^{-a|t|} ↦ √(2/π) 2iax/(a² + x²)²`, `a > 0`. -/
@[dlmf 1.14.T1]
theorem fourierTransform_mul_exp_neg_abs {a : ℝ} (ha : 0 < a) (x : ℝ) :
    fourierTransform (fun t => (t * Real.exp (-a * |t|) : ℂ)) x =
      (Real.sqrt (2 / Real.pi) : ℂ) * (2 * I * a * x / (a ^ 2 + x ^ 2) ^ 2) := by
  sorry

/-- DLMF Table 1.14.1, row 5: `|t| e^{-a|t|} ↦ √(2/π) (a² - x²)/(a² + x²)²`, `a > 0`. -/
@[dlmf 1.14.T1]
theorem fourierTransform_abs_mul_exp_neg_abs {a : ℝ} (ha : 0 < a) (x : ℝ) :
    fourierTransform (fun t => (|t| * Real.exp (-a * |t|) : ℂ)) x =
      (Real.sqrt (2 / Real.pi) : ℂ) * ((a ^ 2 - x ^ 2) / (a ^ 2 + x ^ 2) ^ 2 : ℝ) := by
  sorry

/-- DLMF Table 1.14.1, row 6: `e^{-a|t|}/|t|^{1/2} ↦ (a + (a² + x²)^{1/2})^{1/2}/(a² + x²)^{1/2}`,
`a > 0`. -/
@[dlmf 1.14.T1]
theorem fourierTransform_exp_neg_abs_div_sqrt {a : ℝ} (ha : 0 < a) (x : ℝ) :
    fourierTransform (fun t => (Real.exp (-a * |t|) / Real.sqrt |t| : ℂ)) x =
      (Real.sqrt (a + Real.sqrt (a ^ 2 + x ^ 2)) / Real.sqrt (a ^ 2 + x ^ 2) : ℝ) := by
  sorry

/-- DLMF Table 1.14.1, row 7: `sinh(at)/sinh(πt) ↦ (2π)^{-1/2} sin a/(cosh x + cos a)`,
`-π < a < π` (the Lean value at `t = 0` is `0/0 = 0`, a null set). -/
@[dlmf 1.14.T1]
theorem fourierTransform_sinh_div_sinh {a : ℝ} (ha1 : -Real.pi < a) (ha2 : a < Real.pi)
    (x : ℝ) :
    fourierTransform (fun t => (Real.sinh (a * t) / Real.sinh (Real.pi * t) : ℂ)) x =
      ((Real.sqrt (2 * Real.pi))⁻¹ : ℂ) * (Real.sin a / (Real.cosh x + Real.cos a) : ℝ) := by
  sorry

/-- DLMF Table 1.14.1, row 8:
`cosh(at)/cosh(πt) ↦ √(2/π) cos(½a) cosh(½x)/(cosh x + cos a)`, `-π < a < π`. -/
@[dlmf 1.14.T1]
theorem fourierTransform_cosh_div_cosh {a : ℝ} (ha1 : -Real.pi < a) (ha2 : a < Real.pi)
    (x : ℝ) :
    fourierTransform (fun t => (Real.cosh (a * t) / Real.cosh (Real.pi * t) : ℂ)) x =
      (Real.sqrt (2 / Real.pi) : ℂ) *
        (Real.cos (a / 2) * Real.cosh (x / 2) / (Real.cosh x + Real.cos a) : ℝ) := by
  sorry

/-- DLMF Table 1.14.1, row 9: `e^{-at²} ↦ (2a)^{-1/2} e^{-x²/(4a)}`, `a > 0`. Proved from
Mathlib's `fourierIntegral_gaussian`. -/
@[dlmf 1.14.T1]
theorem fourierTransform_gaussian {a : ℝ} (ha : 0 < a) (x : ℝ) :
    fourierTransform (fun t => cexp (-a * t ^ 2)) x =
      ((Real.sqrt (2 * a))⁻¹ : ℂ) * cexp (-x ^ 2 / (4 * a)) := by
  have hb : 0 < (a : ℂ).re := by simpa using ha
  unfold fourierTransform
  have h := fourierIntegral_gaussian hb (x : ℂ)
  simp_rw [mul_comm (cexp (-(a : ℂ) * _))] at *
  rw [h]
  have hpa : ((Real.pi : ℂ) / a) ^ (1 / 2 : ℂ) = (Real.sqrt (Real.pi / a) : ℂ) := by
    rw [Real.sqrt_eq_rpow, ofReal_cpow (by positivity)]
    push_cast
    ring_nf
  rw [hpa, ← mul_assoc]
  congr 1
  have h1 : Real.sqrt (Real.pi / a) = Real.sqrt Real.pi / Real.sqrt a :=
    Real.sqrt_div' _ ha.le
  have h2 : Real.sqrt (2 * Real.pi) = Real.sqrt 2 * Real.sqrt Real.pi :=
    Real.sqrt_mul (by norm_num) _
  have h3 : Real.sqrt (2 * a) = Real.sqrt 2 * Real.sqrt a := Real.sqrt_mul (by norm_num) _
  have hpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  rw [h1, h2, h3]
  push_cast
  have : (Real.sqrt Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr hpi.ne'
  have : (Real.sqrt a : ℂ) ≠ 0 := ofReal_ne_zero.mpr hsa.ne'
  have : (Real.sqrt 2 : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs2.ne'
  field_simp

/-- DLMF Table 1.14.1, row 10: `sin(at²) ↦ -(2a)^{-1/2} sin(x²/(4a) - π/4)`, `a > 0`, the
integral converging conditionally (limit of `∫_{-R}^{R}`). -/
@[dlmf 1.14.T1]
theorem tendsto_fourierTransform_sin_sq {a : ℝ} (ha : 0 < a) (x : ℝ) :
    Tendsto (fun R : ℝ => ((Real.sqrt (2 * Real.pi))⁻¹ : ℂ) *
        ∫ t in -R..R, (Real.sin (a * t ^ 2) : ℂ) * cexp (I * x * t)) atTop
      (𝓝 (-(Real.sqrt (2 * a))⁻¹ * Real.sin (x ^ 2 / (4 * a) - Real.pi / 4) : ℝ)) := by
  sorry

/-- DLMF Table 1.14.1, row 11: `cos(at²) ↦ (2a)^{-1/2} cos(x²/(4a) - π/4)`, `a > 0`
(conditionally convergent). -/
@[dlmf 1.14.T1]
theorem tendsto_fourierTransform_cos_sq {a : ℝ} (ha : 0 < a) (x : ℝ) :
    Tendsto (fun R : ℝ => ((Real.sqrt (2 * Real.pi))⁻¹ : ℂ) *
        ∫ t in -R..R, (Real.cos (a * t ^ 2) : ℂ) * cexp (I * x * t)) atTop
      (𝓝 ((Real.sqrt (2 * a))⁻¹ * Real.cos (x ^ 2 / (4 * a) - Real.pi / 4) : ℝ)) := by
  sorry

/-! ### Table 1.14.2: Fourier cosine transforms `√(2/π) ∫₀^∞ f(t) cos(xt) dt`, `x > 0` -/

/-- DLMF Table 1.14.2, row 2: `f = 1` on `0 < t ≤ a`, `0` otherwise: `√(2/π) sin(ax)/x`
(`a > 0`). -/
@[dlmf 1.14.T2]
theorem fourierCosTransform_indicator {a : ℝ} (ha : 0 < a) {x : ℝ} (hx : 0 < x) :
    fourierCosTransform (fun t => (Ioc 0 a).indicator (fun _ => (1 : ℂ)) t) x =
      (Real.sqrt (2 / Real.pi) : ℂ) * Real.sin (a * x) / x := by
  sorry

/-- DLMF Table 1.14.2, row 3: `1/(a² + t²) ↦ √(π/2) e^{-ax}/a`, `ℜa > 0`. -/
@[dlmf 1.14.T2]
theorem fourierCosTransform_inv_sq_add_sq {a : ℂ} (ha : 0 < a.re) {x : ℝ} (hx : 0 < x) :
    fourierCosTransform (fun t => 1 / (a ^ 2 + t ^ 2)) x =
      (Real.sqrt (Real.pi / 2) : ℂ) * cexp (-a * x) / a := by
  sorry

/-- DLMF Table 1.14.2, row 4: `1/(a² + t²)² ↦ √(π/2) (1 + ax) e^{-ax}/(2a³)`, `ℜa > 0`. -/
@[dlmf 1.14.T2]
theorem fourierCosTransform_inv_sq_add_sq_sq {a : ℂ} (ha : 0 < a.re) {x : ℝ} (hx : 0 < x) :
    fourierCosTransform (fun t => 1 / (a ^ 2 + t ^ 2) ^ 2) x =
      (Real.sqrt (Real.pi / 2) : ℂ) * (1 + a * x) * cexp (-a * x) / (2 * a ^ 3) := by
  sorry

/-- DLMF Table 1.14.2, row 5: `4a³/(4a⁴ + t⁴) ↦ √π e^{-ax} sin(ax + ¼π)`, `ℜa > 0`. -/
@[dlmf 1.14.T2]
theorem fourierCosTransform_quartic {a : ℂ} (ha : 0 < a.re) {x : ℝ} (hx : 0 < x) :
    fourierCosTransform (fun t => 4 * a ^ 3 / (4 * a ^ 4 + t ^ 4)) x =
      (Real.sqrt Real.pi : ℂ) * cexp (-a * x) * Complex.sin (a * x + Real.pi / 4) := by
  sorry

/-- DLMF Table 1.14.2, row 6: `e^{-at} ↦ √(2/π) a/(a² + x²)`, `ℜa > 0`. -/
@[dlmf 1.14.T2]
theorem fourierCosTransform_exp_neg {a : ℂ} (ha : 0 < a.re) {x : ℝ} (hx : 0 < x) :
    fourierCosTransform (fun t => cexp (-a * t)) x =
      (Real.sqrt (2 / Real.pi) : ℂ) * (a / (a ^ 2 + x ^ 2)) := by
  sorry

/-- DLMF Table 1.14.2, row 7: `e^{-at²} ↦ (2a)^{-1/2} e^{-x²/(4a)}`, `ℜa > 0`, principal power. -/
@[dlmf 1.14.T2]
theorem fourierCosTransform_gaussian {a : ℂ} (ha : 0 < a.re) {x : ℝ} (hx : 0 < x) :
    fourierCosTransform (fun t => cexp (-a * t ^ 2)) x =
      (2 * a) ^ (-(1 / 2 : ℂ)) * cexp (-x ^ 2 / (4 * a)) := by
  sorry

/-- DLMF Table 1.14.2, row 8: `sin(at²) ↦ -(2a)^{-1/2} sin(x²/(4a) - π/4)`, `a > 0`
(conditionally convergent: limit of `∫₀^R`). -/
@[dlmf 1.14.T2]
theorem tendsto_fourierCosTransform_sin_sq {a : ℝ} (ha : 0 < a) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun R : ℝ => (Real.sqrt (2 / Real.pi) : ℂ) *
        ∫ t in (0 : ℝ)..R, (Real.sin (a * t ^ 2) * Real.cos (x * t) : ℂ)) atTop
      (𝓝 (-(Real.sqrt (2 * a))⁻¹ * Real.sin (x ^ 2 / (4 * a) - Real.pi / 4) : ℝ)) := by
  sorry

/-- DLMF Table 1.14.2, row 9: `cos(at²) ↦ (2a)^{-1/2} cos(x²/(4a) - π/4)`, `a > 0`
(conditionally convergent). -/
@[dlmf 1.14.T2]
theorem tendsto_fourierCosTransform_cos_sq {a : ℝ} (ha : 0 < a) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun R : ℝ => (Real.sqrt (2 / Real.pi) : ℂ) *
        ∫ t in (0 : ℝ)..R, (Real.cos (a * t ^ 2) * Real.cos (x * t) : ℂ)) atTop
      (𝓝 ((Real.sqrt (2 * a))⁻¹ * Real.cos (x ^ 2 / (4 * a) - Real.pi / 4) : ℝ)) := by
  sorry

/-- DLMF Table 1.14.2, row 10: `ln(1 + a²/t²) ↦ √(2π) (1 - e^{-ax})/x`, `ℜa > 0`, principal
logarithm. -/
@[dlmf 1.14.T2]
theorem fourierCosTransform_log_one_add {a : ℂ} (ha : 0 < a.re) {x : ℝ} (hx : 0 < x) :
    fourierCosTransform (fun t => Complex.log (1 + a ^ 2 / t ^ 2)) x =
      (Real.sqrt (2 * Real.pi) : ℂ) * (1 - cexp (-a * x)) / x := by
  sorry

/-- DLMF Table 1.14.2, row 11, **corrected**: `ln(a² + t²) - ln(b² + t²) ↦
√(2π) (e^{-bx} - e^{-ax})/x`, `ℜa, ℜb > 0`. DLMF writes `ln((a² + t²)/(b² + t²))`; with the
principal logarithm of the quotient this fails for some complex `a`, `b` (module docstring). -/
@[dlmf 1.14.T2]
theorem fourierCosTransform_log_sub_log {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) {x : ℝ}
    (hx : 0 < x) :
    fourierCosTransform (fun t => Complex.log (a ^ 2 + t ^ 2) - Complex.log (b ^ 2 + t ^ 2)) x =
      (Real.sqrt (2 * Real.pi) : ℂ) * (cexp (-b * x) - cexp (-a * x)) / x := by
  sorry

/-! ### Table 1.14.3: Fourier sine transforms `√(2/π) ∫₀^∞ f(t) sin(xt) dt`, `x > 0` -/

/-- DLMF Table 1.14.3, row 2: `t⁻¹ ↦ √(π/2)` (conditionally convergent: limit of `∫₀^R`). -/
@[dlmf 1.14.T3]
theorem tendsto_fourierSinTransform_inv {x : ℝ} (hx : 0 < x) :
    Tendsto (fun R : ℝ => (Real.sqrt (2 / Real.pi) : ℂ) *
        ∫ t in (0 : ℝ)..R, (t⁻¹ * Real.sin (x * t) : ℂ)) atTop
      (𝓝 (Real.sqrt (Real.pi / 2) : ℂ)) := by
  sorry

/-- DLMF Table 1.14.3, row 3: `t^{-1/2} ↦ x^{-1/2}` (conditionally convergent). -/
@[dlmf 1.14.T3]
theorem tendsto_fourierSinTransform_inv_sqrt {x : ℝ} (hx : 0 < x) :
    Tendsto (fun R : ℝ => (Real.sqrt (2 / Real.pi) : ℂ) *
        ∫ t in (0 : ℝ)..R, ((Real.sqrt t)⁻¹ * Real.sin (x * t) : ℂ)) atTop
      (𝓝 ((Real.sqrt x)⁻¹ : ℂ)) := by
  sorry

/-- DLMF Table 1.14.3, row 4: `t^{-3/2} ↦ 2x^{1/2}`. -/
@[dlmf 1.14.T3]
theorem fourierSinTransform_rpow_neg_three_halves {x : ℝ} (hx : 0 < x) :
    fourierSinTransform (fun t => (t ^ (-(3 / 2 : ℝ)) : ℝ)) x = (2 * Real.sqrt x : ℝ) := by
  sorry

/-- DLMF Table 1.14.3, row 5: `t/(a² + t²) ↦ √(π/2) e^{-ax}`, `ℜa > 0` (conditionally
convergent). -/
@[dlmf 1.14.T3]
theorem tendsto_fourierSinTransform_div_sq_add_sq {a : ℂ} (ha : 0 < a.re) {x : ℝ}
    (hx : 0 < x) :
    Tendsto (fun R : ℝ => (Real.sqrt (2 / Real.pi) : ℂ) *
        ∫ t in (0 : ℝ)..R, t / (a ^ 2 + t ^ 2) * Real.sin (x * t)) atTop
      (𝓝 ((Real.sqrt (Real.pi / 2) : ℂ) * cexp (-a * x))) := by
  sorry

/-- DLMF Table 1.14.3, row 6: `t/(a² + t²)² ↦ √(π/8) (x/a) e^{-ax}`, `ℜa > 0`. -/
@[dlmf 1.14.T3]
theorem fourierSinTransform_div_sq_add_sq_sq {a : ℂ} (ha : 0 < a.re) {x : ℝ} (hx : 0 < x) :
    fourierSinTransform (fun t => t / (a ^ 2 + t ^ 2) ^ 2) x =
      (Real.sqrt (Real.pi / 8) : ℂ) * (x / a) * cexp (-a * x) := by
  sorry

/-- DLMF Table 1.14.3, row 7: `1/(t(a² + t²)) ↦ √(π/2) (1 - e^{-ax})/a²`, `ℜa > 0`. -/
@[dlmf 1.14.T3]
theorem fourierSinTransform_inv_mul_sq_add_sq {a : ℂ} (ha : 0 < a.re) {x : ℝ} (hx : 0 < x) :
    fourierSinTransform (fun t => 1 / (t * (a ^ 2 + t ^ 2))) x =
      (Real.sqrt (Real.pi / 2) : ℂ) * (1 - cexp (-a * x)) / a ^ 2 := by
  sorry

/-- DLMF Table 1.14.3, row 8: `e^{-at}/t ↦ √(2/π) arctan(x/a)`, `ℜa > 0`, principal branch. -/
@[dlmf 1.14.T3]
theorem fourierSinTransform_exp_neg_div {a : ℂ} (ha : 0 < a.re) {x : ℝ} (hx : 0 < x) :
    fourierSinTransform (fun t => cexp (-a * t) / t) x =
      (Real.sqrt (2 / Real.pi) : ℂ) * Complex.arctan (x / a) := by
  sorry

/-- DLMF Table 1.14.3, row 9: `e^{-at} ↦ √(2/π) x/(a² + x²)`, `ℜa > 0`. -/
@[dlmf 1.14.T3]
theorem fourierSinTransform_exp_neg {a : ℂ} (ha : 0 < a.re) {x : ℝ} (hx : 0 < x) :
    fourierSinTransform (fun t => cexp (-a * t)) x =
      (Real.sqrt (2 / Real.pi) : ℂ) * (x / (a ^ 2 + x ^ 2)) := by
  sorry

/-- DLMF Table 1.14.3, row 10: `t e^{-at} ↦ √(2/π) 2ax/(a² + x²)²`, `ℜa > 0`. -/
@[dlmf 1.14.T3]
theorem fourierSinTransform_mul_exp_neg {a : ℂ} (ha : 0 < a.re) {x : ℝ} (hx : 0 < x) :
    fourierSinTransform (fun t => t * cexp (-a * t)) x =
      (Real.sqrt (2 / Real.pi) : ℂ) * (2 * a * x / (a ^ 2 + x ^ 2) ^ 2) := by
  sorry

/-- DLMF Table 1.14.3, row 11: `t e^{-at²} ↦ (2a)^{-3/2} x e^{-x²/(4a)}`, `|ph a| < ½π`
(that is, `ℜa > 0`), principal power. -/
@[dlmf 1.14.T3]
theorem fourierSinTransform_mul_gaussian {a : ℂ} (ha : 0 < a.re) {x : ℝ} (hx : 0 < x) :
    fourierSinTransform (fun t => t * cexp (-a * t ^ 2)) x =
      (2 * a) ^ (-(3 / 2 : ℂ)) * x * cexp (-x ^ 2 / (4 * a)) := by
  sorry

/-- DLMF Table 1.14.3, row 12: `sin(at)/t ↦ (2π)^{-1/2} ln|(x + a)/(x - a)|`, `a > 0`
(conditionally convergent; `x ≠ a`). -/
@[dlmf 1.14.T3]
theorem tendsto_fourierSinTransform_sin_div {a : ℝ} (ha : 0 < a) {x : ℝ} (hx : 0 < x)
    (hxa : x ≠ a) :
    Tendsto (fun R : ℝ => (Real.sqrt (2 / Real.pi) : ℂ) *
        ∫ t in (0 : ℝ)..R, (Real.sin (a * t) / t * Real.sin (x * t) : ℂ)) atTop
      (𝓝 (((Real.sqrt (2 * Real.pi))⁻¹ * Real.log |(x + a) / (x - a)| : ℝ) : ℂ)) := by
  sorry

/-- DLMF Table 1.14.3, row 13: `arctan(t/a) ↦ √(π/2) e^{-ax}/x`, `a > 0`. The sine integral of
`arctan(t/a)` does not converge; DLMF's value is the Abel limit
`lim_{ε→0+} √(2/π) ∫₀^∞ e^{-εt} arctan(t/a) sin(xt) dt`, stated so. -/
@[dlmf 1.14.T3]
theorem tendsto_fourierSinTransform_arctan_abel {a : ℝ} (ha : 0 < a) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun ε : ℝ => Real.sqrt (2 / Real.pi) *
        ∫ t in Ioi (0 : ℝ), Real.exp (-ε * t) * Real.arctan (t / a) * Real.sin (x * t))
      (𝓝[>] 0) (𝓝 (Real.sqrt (Real.pi / 2) * Real.exp (-a * x) / x)) := by
  sorry

/-- DLMF Table 1.14.3, row 14: `ln|(t + a)/(t - a)| ↦ √(2π) sin(ax)/x`, `a > 0`
(conditionally convergent at infinity, integrable logarithmic singularity at `t = a`). -/
@[dlmf 1.14.T3]
theorem tendsto_fourierSinTransform_log_abs {a : ℝ} (ha : 0 < a) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun R : ℝ => Real.sqrt (2 / Real.pi) *
        ∫ t in (0 : ℝ)..R, Real.log |(t + a) / (t - a)| * Real.sin (x * t)) atTop
      (𝓝 (Real.sqrt (2 * Real.pi) * Real.sin (a * x) / x)) := by
  sorry

/-! ### Table 1.14.4: Laplace transforms `∫₀^∞ e^{-st} f(t) dt` -/

/-- DLMF Table 1.14.4, row 5: `e^{-at} ↦ 1/(s + a)`, `ℜ(s + a) > 0`. -/
@[dlmf 1.14.T4]
theorem laplaceTransform_exp_neg {a s : ℂ} (hs : 0 < (s + a).re) :
    laplaceTransform (fun t => cexp (-a * t)) s = 1 / (s + a) := by
  unfold laplaceTransform
  have h : (-(s + a)).re < 0 := by simp at hs ⊢; linarith
  have hne : s + a ≠ 0 := by
    intro h0; rw [h0] at hs; simp at hs
  calc (∫ t in Ioi (0 : ℝ), cexp (-s * t) * cexp (-a * t))
      = ∫ t in Ioi (0 : ℝ), cexp (-(s + a) * t) := by
        congr 1; funext t; rw [← Complex.exp_add]; congr 1; ring
    _ = 1 / (s + a) := by
        rw [integral_exp_mul_complex_Ioi h 0]
        simp only [ofReal_zero, mul_zero, Complex.exp_zero]
        field_simp

/-- DLMF Table 1.14.4, row 2: `1 ↦ 1/s`, `ℜs > 0`. -/
@[dlmf 1.14.T4]
theorem laplaceTransform_one {s : ℂ} (hs : 0 < s.re) :
    laplaceTransform (fun _ => 1) s = 1 / s := by
  have h := laplaceTransform_exp_neg (a := 0) (s := s) (by simpa using hs)
  simpa using h

/-- DLMF Table 1.14.4, row 3: `tⁿ/n! ↦ 1/s^{n+1}`, `ℜs > 0`. -/
@[dlmf 1.14.T4]
theorem laplaceTransform_pow_div_factorial (n : ℕ) {s : ℂ} (hs : 0 < s.re) :
    laplaceTransform (fun t => (t : ℂ) ^ n / n !) s = 1 / s ^ (n + 1) := by
  sorry

/-- DLMF Table 1.14.4, row 4: `1/√(πt) ↦ 1/√s`, `ℜs > 0`, principal square root. -/
@[dlmf 1.14.T4]
theorem laplaceTransform_inv_sqrt {s : ℂ} (hs : 0 < s.re) :
    laplaceTransform (fun t => ((Real.sqrt (Real.pi * t))⁻¹ : ℂ)) s = s ^ (-(1 / 2 : ℂ)) := by
  sorry

/-- DLMF Table 1.14.4, row 6: `tⁿ e^{-at}/n! ↦ 1/(s + a)^{n+1}`, `ℜ(s + a) > 0`. Proved from
row 3 and the translation rule 1.14.21. -/
@[dlmf 1.14.T4]
theorem laplaceTransform_pow_mul_exp_neg_div_factorial (n : ℕ) {a s : ℂ}
    (hs : 0 < (s + a).re) :
    laplaceTransform (fun t => (t : ℂ) ^ n * cexp (-a * t) / n !) s = 1 / (s + a) ^ (n + 1) := by
  have h := laplaceTransform_sub (fun t => (t : ℂ) ^ n / n !) s (-a)
  rw [sub_neg_eq_add, laplaceTransform_pow_div_factorial n (by simpa using hs)] at h
  rw [h]
  congr 1
  funext t
  ring

/-- DLMF Table 1.14.4, row 7: `(e^{-at} - e^{-bt})/(b - a) ↦ 1/((s + a)(s + b))`, `a ≠ b`,
`ℜs > -ℜa`, `ℜs > -ℜb`. Proved from row 5. -/
@[dlmf 1.14.T4]
theorem laplaceTransform_exp_neg_sub_exp_neg {a b s : ℂ} (hab : a ≠ b) (ha : -a.re < s.re)
    (hb : -b.re < s.re) :
    laplaceTransform (fun t => (cexp (-a * t) - cexp (-b * t)) / (b - a)) s =
      1 / ((s + a) * (s + b)) := by
  have ha' : 0 < (s + a).re := by simp; linarith
  have hb' : 0 < (s + b).re := by simp; linarith
  have hia : IntegrableOn (fun t : ℝ => cexp (-s * t) * cexp (-a * t)) (Ioi 0) := by
    have : IntegrableOn (fun t : ℝ => cexp (-(s + a) * t)) (Ioi 0) :=
      integrableOn_exp_mul_complex_Ioi (by simp at ha' ⊢; linarith) 0
    refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only; rw [← Complex.exp_add]; congr 1; ring
  have hib : IntegrableOn (fun t : ℝ => cexp (-s * t) * cexp (-b * t)) (Ioi 0) := by
    have : IntegrableOn (fun t : ℝ => cexp (-(s + b) * t)) (Ioi 0) :=
      integrableOn_exp_mul_complex_Ioi (by simp at hb' ⊢; linarith) 0
    refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only; rw [← Complex.exp_add]; congr 1; ring
  have ea := laplaceTransform_exp_neg ha'
  have eb := laplaceTransform_exp_neg hb'
  unfold laplaceTransform at *
  have : (fun t : ℝ => cexp (-s * t) * ((cexp (-a * t) - cexp (-b * t)) / (b - a))) =
      fun t : ℝ => (cexp (-s * t) * cexp (-a * t) - cexp (-s * t) * cexp (-b * t)) / (b - a) := by
    funext t; ring
  rw [this, integral_div, integral_sub hia hib, ea, eb]
  have h1 : s + a ≠ 0 := fun h => by rw [h] at ha'; simp at ha'
  have h2 : s + b ≠ 0 := fun h => by rw [h] at hb'; simp at hb'
  have h3 : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  field_simp
  ring

/-- DLMF Table 1.14.4, row 8: `sin(at) ↦ a/(s² + a²)`, `ℜs > |ℑa|`. -/
@[dlmf 1.14.T4]
theorem laplaceTransform_sin {a s : ℂ} (hs : |a.im| < s.re) :
    laplaceTransform (fun t => Complex.sin (a * t)) s = a / (s ^ 2 + a ^ 2) := by
  sorry

/-- DLMF Table 1.14.4, row 9: `cos(at) ↦ s/(s² + a²)`, `ℜs > |ℑa|`. -/
@[dlmf 1.14.T4]
theorem laplaceTransform_cos {a s : ℂ} (hs : |a.im| < s.re) :
    laplaceTransform (fun t => Complex.cos (a * t)) s = s / (s ^ 2 + a ^ 2) := by
  sorry

/-- DLMF Table 1.14.4, row 10: `sinh(at) ↦ a/(s² - a²)`, `ℜs > |ℜa|`. -/
@[dlmf 1.14.T4]
theorem laplaceTransform_sinh {a s : ℂ} (hs : |a.re| < s.re) :
    laplaceTransform (fun t => Complex.sinh (a * t)) s = a / (s ^ 2 - a ^ 2) := by
  sorry

/-- DLMF Table 1.14.4, row 11: `cosh(at) ↦ s/(s² - a²)`, `ℜs > |ℜa|`. -/
@[dlmf 1.14.T4]
theorem laplaceTransform_cosh {a s : ℂ} (hs : |a.re| < s.re) :
    laplaceTransform (fun t => Complex.cosh (a * t)) s = s / (s ^ 2 - a ^ 2) := by
  sorry

/-- DLMF Table 1.14.4, row 12: `t sin(at) ↦ 2as/(s² + a²)²`, `ℜs > |ℑa|`. -/
@[dlmf 1.14.T4]
theorem laplaceTransform_mul_sin {a s : ℂ} (hs : |a.im| < s.re) :
    laplaceTransform (fun t => t * Complex.sin (a * t)) s = 2 * a * s / (s ^ 2 + a ^ 2) ^ 2 := by
  sorry

/-- DLMF Table 1.14.4, row 13: `t cos(at) ↦ (s² - a²)/(s² + a²)²`, `ℜs > |ℑa|`. -/
@[dlmf 1.14.T4]
theorem laplaceTransform_mul_cos {a s : ℂ} (hs : |a.im| < s.re) :
    laplaceTransform (fun t => t * Complex.cos (a * t)) s =
      (s ^ 2 - a ^ 2) / (s ^ 2 + a ^ 2) ^ 2 := by
  sorry

/-- DLMF Table 1.14.4, row 14: `(e^{-bt} - e^{-at})/t ↦ ln((s + a)/(s + b))`, `ℜs > -ℜa`,
`ℜs > -ℜb`, principal logarithm. -/
@[dlmf 1.14.T4]
theorem laplaceTransform_exp_neg_sub_exp_neg_div {a b s : ℂ} (ha : -a.re < s.re)
    (hb : -b.re < s.re) :
    laplaceTransform (fun t => (cexp (-b * t) - cexp (-a * t)) / t) s =
      Complex.log ((s + a) / (s + b)) := by
  sorry

/-- DLMF Table 1.14.4, row 15: `2(1 - cosh(at))/t ↦ ln(1 - a²/s²)`, under the **corrected**
condition `ℜs > |ℜa|` (DLMF prints `ℜ(s + a) > 0`, insufficient since the left side is even in
`a`). -/
@[dlmf 1.14.T4]
theorem laplaceTransform_one_sub_cosh_div {a s : ℂ} (hs : |a.re| < s.re) :
    laplaceTransform (fun t => 2 * (1 - Complex.cosh (a * t)) / t) s =
      Complex.log (1 - a ^ 2 / s ^ 2) := by
  sorry

/-- DLMF Table 1.14.4, row 16: `2(1 - cos(at))/t ↦ ln(1 + a²/s²)`, `ℜs > |ℑa|` (DLMF:
`ℜs > 0`, for real `a`). -/
@[dlmf 1.14.T4]
theorem laplaceTransform_one_sub_cos_div {a s : ℂ} (hs : |a.im| < s.re) :
    laplaceTransform (fun t => 2 * (1 - Complex.cos (a * t)) / t) s =
      Complex.log (1 + a ^ 2 / s ^ 2) := by
  sorry

/-- DLMF Table 1.14.4, row 17: `sin(at)/t ↦ arctan(a/s)`, `ℜs > |ℑa|` (DLMF: `ℜs > 0`, for real
`a`), principal branch. -/
@[dlmf 1.14.T4]
theorem laplaceTransform_sin_div {a s : ℂ} (hs : |a.im| < s.re) :
    laplaceTransform (fun t => Complex.sin (a * t) / t) s = Complex.arctan (a / s) := by
  sorry

/-! ### Table 1.14.5: Mellin transforms `∫₀^∞ x^{s-1} f(x) dx` (Mathlib's `mellin`) -/

/-- DLMF Table 1.14.5, row 2: `f = 1` for `x < a`, `0` for `x ≥ a`: `a^s/s`, `a ≥ 0`, `ℜs > 0`. -/
@[dlmf 1.14.T5]
theorem mellin_indicator_lt {a : ℝ} (ha : 0 ≤ a) {s : ℂ} (hs : 0 < s.re) :
    mellin (fun x => (Iio a).indicator (fun _ => (1 : ℂ)) x) s = (a : ℂ) ^ s / s := by
  sorry

/-- DLMF Table 1.14.5, row 3: `ln(a/x)` for `x < a`, `0` for `x ≥ a`: `a^s/s²`, `a ≥ 0`;
valid for `ℜs > 0` (DLMF: `ℜs > 1`). -/
@[dlmf 1.14.T5]
theorem mellin_log_indicator_lt {a : ℝ} (ha : 0 ≤ a) {s : ℂ} (hs : 0 < s.re) :
    mellin (fun x => (Iio a).indicator (fun x => (Real.log (a / x) : ℂ)) x) s =
      (a : ℂ) ^ s / s ^ 2 := by
  sorry

/-- DLMF Table 1.14.5, row 4: `1/(1 - x) ↦ π cot(sπ)`, `0 < ℜs < 1`, Cauchy principal value at
`x = 1`. -/
@[dlmf 1.14.T5]
theorem tendsto_mellin_inv_one_sub_pv {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    Tendsto (fun ε : ℝ => ∫ x in {x : ℝ | 0 < x ∧ ε < |x - 1|},
        (x : ℂ) ^ (s - 1) * (1 / (1 - x))) (𝓝[>] 0)
      (𝓝 (Real.pi * Complex.cot (s * Real.pi))) := by
  sorry

/-- DLMF Table 1.14.5, row 5: `1/(1 + x) ↦ π csc(sπ)`, `0 < ℜs < 1`. -/
@[dlmf 1.14.T5]
theorem mellin_inv_one_add {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    mellin (fun x => 1 / (1 + (x : ℂ))) s = Real.pi / Complex.sin (s * Real.pi) := by
  sorry

/-- DLMF Table 1.14.5, row 6: `ln(1 + ax) ↦ π csc(sπ)/(s a^s)`, `|ph a| < π`, `-1 < ℜs < 0`. -/
@[dlmf 1.14.T5]
theorem mellin_log_one_add_mul {a : ℂ} (ha : a ∈ slitPlane) {s : ℂ} (hs0 : -1 < s.re)
    (hs1 : s.re < 0) :
    mellin (fun x => Complex.log (1 + a * x)) s =
      Real.pi / Complex.sin (s * Real.pi) / (s * a ^ s) := by
  sorry

/-- DLMF Table 1.14.5, row 7: `ln|(1 + x)/(1 - x)| ↦ π tan(½sπ)/s`, `-1 < ℜs < 1`, `s ≠ 0`. -/
@[dlmf 1.14.T5]
theorem mellin_log_abs_one_add_div_one_sub {s : ℂ} (hs0 : -1 < s.re) (hs1 : s.re < 1)
    (hs : s ≠ 0) :
    mellin (fun x => (Real.log |(1 + x) / (1 - x)| : ℂ)) s =
      Real.pi * Complex.tan (s * Real.pi / 2) / s := by
  sorry

/-- DLMF Table 1.14.5, row 8: `ln(1 + x)/x ↦ π csc(sπ)/(1 - s)`, `0 < ℜs < 1`. -/
@[dlmf 1.14.T5]
theorem mellin_log_one_add_div {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    mellin (fun x => (Real.log (1 + x) / x : ℂ)) s =
      Real.pi / Complex.sin (s * Real.pi) / (1 - s) := by
  sorry

/-- DLMF Table 1.14.5, row 9: `arctan x ↦ -π sec(½sπ)/(2s)`, `-1 < ℜs < 0`. -/
@[dlmf 1.14.T5]
theorem mellin_arctan {s : ℂ} (hs0 : -1 < s.re) (hs1 : s.re < 0) :
    mellin (fun x => (Real.arctan x : ℂ)) s =
      -(Real.pi / Complex.cos (s * Real.pi / 2)) / (2 * s) := by
  sorry

/-- DLMF Table 1.14.5, row 10: `arccot x = π/2 - arctan x ↦ π sec(½sπ)/(2s)`, `0 < ℜs < 1`. -/
@[dlmf 1.14.T5]
theorem mellin_arccot {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    mellin (fun x => ((Real.pi / 2 - Real.arctan x : ℝ) : ℂ)) s =
      Real.pi / Complex.cos (s * Real.pi / 2) / (2 * s) := by
  sorry

/-- DLMF Table 1.14.5, row 11: `(1 + x cos θ)/(1 + 2x cos θ + x²) ↦ π cos(sθ)/sin(sπ)`,
`-π < θ < π`, `0 < ℜs < 1`. -/
@[dlmf 1.14.T5]
theorem mellin_poisson_cos {θ : ℝ} (hθ1 : -Real.pi < θ) (hθ2 : θ < Real.pi) {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    mellin (fun x => (((1 + x * Real.cos θ) / (1 + 2 * x * Real.cos θ + x ^ 2) : ℝ) : ℂ)) s =
      Real.pi * Complex.cos (s * θ) / Complex.sin (s * Real.pi) := by
  sorry

/-- DLMF Table 1.14.5, row 12: `x sin θ/(1 + 2x cos θ + x²) ↦ π sin(sθ)/sin(sπ)`,
`-π < θ < π`, `0 < ℜs < 1`. -/
@[dlmf 1.14.T5]
theorem mellin_poisson_sin {θ : ℝ} (hθ1 : -Real.pi < θ) (hθ2 : θ < Real.pi) {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    mellin (fun x => ((x * Real.sin θ / (1 + 2 * x * Real.cos θ + x ^ 2) : ℝ) : ℂ)) s =
      Real.pi * Complex.sin (s * θ) / Complex.sin (s * Real.pi) := by
  sorry

end DLMF.AlgebraicAnalytic
