/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AlgebraicAnalytic.Transforms.Fourier
public import DLMF.AlgebraicAnalytic.Transforms.LaplaceTable
public import DLMF.Gamma.MellinBarnes
public import DLMFMathlib.Analysis.MellinConvolution
public import DLMFMathlib.Analysis.SpecialFunctions.Pow.ComplexReal
public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import TauCeti.Analysis.Contour.WorkedExamples.HalfDisc.SineIntegral
public import TauCeti.Analysis.Fourier.ExpNegAbs
public import TauCeti.MeasureTheory.Integral.Bochner.Basic

/-!
# Tables of integral transforms (DLMF §1.14(vii), Tables 1.14.1–1.14.5)

Each row of DLMF Tables 1.14.1 (Fourier transforms, 1.14.1), 1.14.2 (Fourier cosine transforms,
1.14.9), 1.14.3 (Fourier sine transforms, 1.14.10) and 1.14.5 (Mellin transforms, 1.14.32) is a
theorem here, tagged with the table ID. The Laplace entries of Table 1.14.4 (1.14.17) are in the
imported `DLMF.AlgebraicAnalytic.Transforms.LaplaceTable`.

## Main results

* `fourierTransform_indicator`, `fourierTransform_exp_neg_abs`, `fourierTransform_gaussian`,
  `tendsto_fourierTransform_sin_sq`, `tendsto_fourierTransform_cos_sq` and the other
  `fourierTransform_*` rows: Table 1.14.1.
* `fourierCosTransform_indicator`, `fourierCosTransform_inv_sq_add_sq`,
  `fourierCosTransform_gaussian`, `fourierCosTransform_log_sub_log` and the other
  `fourierCosTransform_*` rows: Table 1.14.2.
* `tendsto_fourierSinTransform_inv`, `fourierSinTransform_exp_neg`,
  `fourierSinTransform_mul_gaussian`, `tendsto_fourierSinTransform_arctan_abel` and the other
  `fourierSinTransform_*` rows: Table 1.14.3.
* `mellin_indicator_lt`, `mellin_inv_one_add`, `mellin_arctan`, `mellin_poisson_cos`,
  `mellin_poisson_sin` and the other `mellin_*` rows: Table 1.14.5.

## Implementation notes

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
  `ln(a² + t²) - ln(b² + t²)`, which is the form stated (the two agree for real `a, b > 0`).
* 1.14.4.15: DLMF's condition `ℜ(s + a) > 0` is insufficient (`cosh(at)` is even in `a`; for
  `a = 1`, `s = ½` the integral diverges); the correct condition `ℜs > |ℜa|` is used.
* 1.14.4.16, 1.14.4.17: DLMF gives `ℜs > 0`, which suffices for real `a`; for complex `a` the
  condition is `ℜs > |ℑa|`, used here.
* 1.14.5.3: DLMF gives `ℜs > 1`; the integral converges and the formula holds for `ℜs > 0`
  (stated so, stronger than DLMF). 1.14.5.7 needs `s ≠ 0` in Lean (`π tan(0)/0` is junk `0`, the
  limit value is `π²/2`).
-/

@[expose] public noncomputable section

open MeasureTheory Complex Set Filter Topology
open scoped Nat

namespace DLMF.AlgebraicAnalytic

/-- The first absolute moment of a two-sided exponential is integrable. -/
private theorem integrable_abs_mul_exp_neg_abs {a : ℝ} (ha : 0 < a) :
    Integrable (fun t : ℝ => |t| * Real.exp (-a * |t|)) := by
  simpa only [pow_one, neg_mul] using TauCeti.MeasureTheory.integrable_comp_abs
    (TauCeti.integrableOn_pow_mul_exp_neg_mul_Ioi 1 ha)

/-- Converting the Gaussian integral constant to the principal DLMF normalization. -/
private theorem gaussian_normalization {a : ℂ} (ha : 0 < a.re) :
    (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ * ((Real.pi : ℂ) / a) ^ (1 / 2 : ℂ) =
      (2 * a) ^ (-(1 / 2 : ℂ)) := by
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha
  have harg : a.arg ≠ Real.pi := (arg_lt_pi_iff.mpr (Or.inl ha.le)).ne
  rw [div_eq_mul_inv, mul_comm (Real.pi : ℂ) a⁻¹,
    mul_ofReal_cpow_of_ne_zero (inv_ne_zero ha0) Real.pi_pos,
    inv_cpow a _ harg, ← cpow_neg,
    show (2 : ℂ) * a = a * ((2 : ℝ) : ℂ) by norm_num; ring,
    mul_ofReal_cpow_of_ne_zero ha0 (by norm_num : (0 : ℝ) < 2)]
  have hp : (Real.pi : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt Real.pi : ℂ) := by
    rw [Real.sqrt_eq_rpow, ofReal_cpow Real.pi_pos.le]
    norm_num
  have hp2 : (2 : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt 2 : ℂ) := by
    rw [Real.sqrt_eq_rpow, ofReal_cpow (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have h2 : (2 : ℂ) ^ (-(1 / 2 : ℂ)) = (Real.sqrt 2 : ℂ)⁻¹ := by
    rw [cpow_neg, hp2]
  norm_num only [ofReal_ofNat]
  rw [hp, h2, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  push_cast
  have hpi : (Real.sqrt Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr
    (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hs2 : (Real.sqrt 2 : ℂ) ≠ 0 := ofReal_ne_zero.mpr
    (Real.sqrt_pos.mpr (by norm_num)).ne'
  field_simp

/-! ### Table 1.14.1: Fourier transforms `(2π)^{-1/2} ∫ f(t) e^{ixt} dt` -/

/-- DLMF Table 1.14.1, row 2: `f = 1` on `|t| < a`, `0` otherwise: `F(x) = √(2/π) sin(ax)/x`
(`a > 0`, `x ≠ 0`). -/
@[dlmf 1.14.T1]
theorem fourierTransform_indicator {a : ℝ} (ha : 0 < a) {x : ℝ} (hx : x ≠ 0) :
    fourierTransform (fun t => (Ioo (-a) a).indicator (fun _ => (1 : ℂ)) t) x =
      (Real.sqrt (2 / Real.pi) : ℂ) * Real.sin (a * x) / x := by
  have hI : (∫ t in -a..a, cexp (I * x * t)) = (2 * Real.sin (a * x) / x : ℝ) := by
    have he : (fun t : ℝ => cexp (I * x * t)) = fun t => cexp (((t * x : ℝ) : ℂ) * I) := by
      funext t
      congr 1
      push_cast
      ring
    rw [he, intervalIntegral.integral_comp_mul_right (fun t : ℝ => cexp (t * I)) hx,
      neg_mul, integral_exp_mul_I_eq_sin]
    simp only [Complex.real_smul]
    push_cast
    ring
  unfold fourierTransform
  have he : (fun t : ℝ => (Ioo (-a) a).indicator (fun _ => (1 : ℂ)) t * cexp (I * x * t)) =
      (Ioo (-a) a).indicator (fun t => cexp (I * x * t)) := by
    ext t
    by_cases ht : t ∈ Ioo (-a) a <;> simp [ht]
  rw [he, integral_indicator measurableSet_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith : -a ≤ a), hI]
  push_cast
  linear_combination (Complex.sin ((a : ℂ) * x) / x) * inv_sqrt_two_pi_mul_two

/-- DLMF Table 1.14.1, row 3: `e^{-a|t|} ↦ √(2/π) a/(a² + x²)`, `a > 0`. -/
@[dlmf 1.14.T1]
theorem fourierTransform_exp_neg_abs {a : ℝ} (ha : 0 < a) (x : ℝ) :
    fourierTransform (fun t => (Real.exp (-a * |t|) : ℂ)) x =
      (Real.sqrt (2 / Real.pi) : ℂ) * (a / (a ^ 2 + x ^ 2) : ℝ) := by
  unfold fourierTransform
  have hi : (∫ t : ℝ, (Real.exp (-a * |t|) : ℂ) * cexp (I * x * t)) =
      ((2 * a / (a ^ 2 + x ^ 2) : ℝ) : ℂ) := by
    convert TauCeti.integral_exp_mul_I_mul_exp_neg_mul_abs ha x using 1
    congr 1
    funext t
    rw [show I * (x : ℂ) * t = (x : ℂ) * t * I by ring, neg_mul]
    exact mul_comm _ _
  rw [hi]
  push_cast
  rw [show (2 : ℂ) * a / (a ^ 2 + x ^ 2) = 2 * ((a : ℂ) / (a ^ 2 + x ^ 2)) by ring,
    ← mul_assoc, inv_sqrt_two_pi_mul_two]

/-- DLMF Table 1.14.1, row 4: `t e^{-a|t|} ↦ √(2/π) 2iax/(a² + x²)²`, `a > 0`. -/
@[dlmf 1.14.T1]
theorem fourierTransform_mul_exp_neg_abs {a : ℝ} (ha : 0 < a) (x : ℝ) :
    fourierTransform (fun t => (t * Real.exp (-a * |t|) : ℂ)) x =
      (Real.sqrt (2 / Real.pi) : ℂ) * (2 * I * a * x / (a ^ 2 + x ^ 2) ^ 2) := by
  have hf : Integrable (fun t : ℝ => (t * Real.exp (-a * |t|) : ℂ)) := by
    refine (integrable_abs_mul_exp_neg_abs ha).mono' (by fun_prop) ?_
    exact Filter.Eventually.of_forall fun t => by
      simp [Real.norm_eq_abs, Complex.norm_exp]
  have hi := integral_eq_integral_Ioi_add_neg (integrable_mul_cexp_I_mul hf x)
  have he (t : ℝ) (ht : 0 < t) :
      ((t * Real.exp (-a * |t|) : ℂ) * cexp (I * x * t) +
        ((-t) * Real.exp (-a * |-t|) : ℂ) * cexp (I * x * (-t))) =
      2 * I * (cexp (-(a : ℂ) * t) * (t * Complex.sin (x * t))) := by
    rw [abs_neg, abs_of_pos ht]
    simp only [ofReal_mul, ofReal_neg, ofReal_exp, Complex.sin]
    rw [show I * (x : ℂ) * t = ↑x * t * I by ring,
      show I * (x : ℂ) * -t = -(↑x * t * I) by ring]
    ring_nf
    simp [I_sq]
    ring
  simp only [ofReal_neg] at hi
  rw [setIntegral_congr_fun measurableSet_Ioi he, integral_const_mul] at hi
  have hl := laplaceTransform_mul_sin (a := (x : ℂ)) (s := (a : ℂ)) (by simpa using ha)
  unfold laplaceTransform at hl
  rw [fourierTransform, hi, hl]
  rw [show (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ * (2 * I *
      (2 * ↑x * ↑a / ((↑a : ℂ) ^ 2 + ↑x ^ 2) ^ 2)) =
      ((Real.sqrt (2 * Real.pi) : ℂ)⁻¹ * 2) *
        (2 * I * ↑a * ↑x / ((↑a : ℂ) ^ 2 + ↑x ^ 2) ^ 2) by ring,
    inv_sqrt_two_pi_mul_two]

/-- DLMF Table 1.14.1, row 5: `|t| e^{-a|t|} ↦ √(2/π) (a² - x²)/(a² + x²)²`, `a > 0`. -/
@[dlmf 1.14.T1]
theorem fourierTransform_abs_mul_exp_neg_abs {a : ℝ} (ha : 0 < a) (x : ℝ) :
    fourierTransform (fun t => (|t| * Real.exp (-a * |t|) : ℂ)) x =
      (Real.sqrt (2 / Real.pi) : ℂ) * ((a ^ 2 - x ^ 2) / (a ^ 2 + x ^ 2) ^ 2 : ℝ) := by
  have hf : Integrable (fun t : ℝ => (|t| * Real.exp (-a * |t|) : ℂ)) := by
    refine (integrable_abs_mul_exp_neg_abs ha).mono' (by fun_prop) ?_
    exact Filter.Eventually.of_forall fun t => by simp [Complex.norm_exp]
  have hi := integral_eq_integral_Ioi_add_neg (integrable_mul_cexp_I_mul hf x)
  have he (t : ℝ) (ht : 0 < t) :
      ((|t| * Real.exp (-a * |t|) : ℂ) * cexp (I * x * t) +
        (|-t| * Real.exp (-a * |-t|) : ℂ) * cexp (I * x * (-t))) =
      2 * (cexp (-(a : ℂ) * t) * (t * Complex.cos (x * t))) := by
    rw [abs_neg, abs_of_pos ht]
    simp only [ofReal_mul, ofReal_neg, ofReal_exp, Complex.cos]
    rw [show I * (x : ℂ) * t = ↑x * t * I by ring,
      show I * (x : ℂ) * -t = -(↑x * t * I) by ring]
    ring
  simp only [ofReal_neg] at hi
  rw [setIntegral_congr_fun measurableSet_Ioi he, integral_const_mul] at hi
  have hl := laplaceTransform_mul_cos (a := (x : ℂ)) (s := (a : ℂ)) (by simpa using ha)
  unfold laplaceTransform at hl
  rw [fourierTransform, hi, hl, ← mul_assoc, inv_sqrt_two_pi_mul_two]
  push_cast
  rfl

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
  unfold fourierCosTransform
  have he : (fun t : ℝ => (Ioc 0 a).indicator (fun _ => (1 : ℂ)) t *
      (Real.cos (x * t) : ℂ)) = (Ioc 0 a).indicator (fun t => (Real.cos (x * t) : ℂ)) := by
    ext t
    by_cases ht : t ∈ Ioc 0 a <;> simp [ht]
  rw [he, setIntegral_indicator measurableSet_Ioc,
    inter_eq_right.mpr (Ioc_subset_Ioi_self), ← intervalIntegral.integral_of_le ha.le,
    intervalIntegral.integral_ofReal]
  rw [intervalIntegral.integral_comp_mul_left Real.cos hx.ne', integral_cos]
  simp only [mul_zero, Real.sin_zero, sub_zero]
  change (Real.sqrt (2 / Real.pi) : ℂ) *
    ((x⁻¹ * Real.sin (x * a) : ℝ) : ℂ) = _
  rw [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_sin, Complex.ofReal_mul]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_sin, mul_comm x a]
  ring

/-- DLMF Table 1.14.2, row 6: `e^{-at} ↦ √(2/π) a/(a² + x²)`, `ℜa > 0`. -/
@[dlmf 1.14.T2]
theorem fourierCosTransform_exp_neg {a : ℂ} (ha : 0 < a.re) {x : ℝ} :
    fourierCosTransform (fun t => cexp (-a * t)) x =
      (Real.sqrt (2 / Real.pi) : ℂ) * (a / (a ^ 2 + x ^ 2)) := by
  have h := laplaceTransform_cos (a := x) (s := a) (by simpa using ha)
  unfold fourierCosTransform
  congr 1
  convert h using 1
  simp only [laplaceTransform, ← ofReal_mul, ← ofReal_cos]

/-- `a² + ξ² ≠ 0` for real `ξ` when `ℜa > 0`. -/
private lemma sq_add_sq_ne_zero {a : ℂ} (ha : 0 < a.re) (ξ : ℝ) : a ^ 2 + (ξ : ℂ) ^ 2 ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [sq, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.zero_re, Complex.add_im, Complex.mul_im, Complex.zero_im] at hre him
  have hq : a.im = 0 := by nlinarith
  rw [hq] at hre
  nlinarith

/-- A lower bound `‖a² + ξ²‖ ≥ ξ²/2` for `ξ ≥ 2‖a‖`. -/
private lemma norm_sq_add_sq_ge {a : ℂ} {ξ : ℝ} (hξ : 2 * ‖a‖ ≤ ξ) :
    ξ ^ 2 / 2 ≤ ‖a ^ 2 + (ξ : ℂ) ^ 2‖ := by
  have h1 : ‖(ξ : ℂ) ^ 2‖ - ‖a ^ 2‖ ≤ ‖a ^ 2 + (ξ : ℂ) ^ 2‖ := by
    have := norm_sub_norm_le ((ξ : ℂ) ^ 2) (-(a ^ 2))
    simpa [sub_neg_eq_add, add_comm] using this
  rw [norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs] at h1
  have : 0 ≤ ‖a‖ := norm_nonneg a
  nlinarith

/-- Integrability on `(0, ∞)` of `ξ ↦ ξ^k/(a² + ξ²)^m` when `k + 1 < 2m`. -/
private lemma integrableOn_pow_div_sq_add_sq_pow {a : ℂ} (ha : 0 < a.re) (k m : ℕ)
    (hkm : k + 2 ≤ 2 * m) :
    IntegrableOn (fun ξ : ℝ => (ξ : ℂ) ^ k / (a ^ 2 + (ξ : ℂ) ^ 2) ^ m) (Ioi 0) := by
  have hcont : Continuous fun ξ : ℝ => (ξ : ℂ) ^ k / (a ^ 2 + (ξ : ℂ) ^ 2) ^ m :=
    Continuous.div (by fun_prop) (by fun_prop) fun ξ => pow_ne_zero _ (sq_add_sq_ne_zero ha ξ)
  refine IntegrableOn.mono_set (t := Ici 0) ?_ Ioi_subset_Ici_self
  refine LocallyIntegrableOn.integrableOn_of_isBigO_atTop
    ((hcont.locallyIntegrable (μ := volume)).locallyIntegrableOn (Ici 0))
    (g := fun ξ : ℝ => ξ ^ (-2 : ℝ)) ?_
    (integrableAtFilter_rpow_atTop_iff.2 (by norm_num))
  refine Asymptotics.IsBigO.of_bound (2 ^ m) ?_
  filter_upwards [eventually_ge_atTop (max (2 * ‖a‖) 1)] with ξ hξ
  have hξ1 : 1 ≤ ξ := le_of_max_le_right hξ
  have hξ0 : 0 < ξ := by linarith
  have hb := norm_sq_add_sq_ge (le_of_max_le_left hξ)
  rw [norm_div, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hξ0,
    Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hξ0 _), Real.rpow_neg hξ0.le,
    Real.rpow_two, div_le_iff₀ (pow_pos (lt_of_lt_of_le (by positivity) hb) _)]
  calc ξ ^ k ≤ ξ ^ (2 * m - 2) := pow_le_pow_right₀ hξ1 (by omega)
    _ = 2 ^ m * (ξ ^ 2)⁻¹ * (ξ ^ 2 / 2) ^ m := by
        rw [div_pow, ← pow_mul]
        obtain ⟨j, hj⟩ : ∃ j, 2 * m = j + 2 := ⟨2 * m - 2, by omega⟩
        rw [hj, Nat.add_sub_cancel, pow_add]
        field_simp
    _ ≤ 2 ^ m * (ξ ^ 2)⁻¹ * ‖a ^ 2 + (ξ : ℂ) ^ 2‖ ^ m := by
        gcongr

/-- A `C¹` function has bounded variation on every compact interval. -/
private lemma boundedVariationOn_Icc_of_contDiff {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f) {a b : ℝ}
    (hab : a ≤ b) : BoundedVariationOn f (Icc a b) := by
  obtain ⟨K, hK⟩ := hf.contDiffOn.exists_lipschitzOnWith (s := Icc a b) (by decide)
    (convex_Icc _ _) isCompact_Icc
  simpa only [inter_self] using hK.locallyBoundedVariationOn a b ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩

/-- `t ↦ e^{-at}` is `C¹` on `ℝ`. -/
private lemma contDiff_cexp_neg_mul (a : ℂ) : ContDiff ℝ 1 fun t : ℝ => cexp (-a * t) :=
  (contDiff_const.mul ofRealCLM.contDiff).cexp

/-- `√(π/2) = √(2/π) · π/2`. -/
private lemma sqrt_pi_div_two_eq :
    Real.sqrt (Real.pi / 2) = Real.sqrt (2 / Real.pi) * (Real.pi / 2) := by
  refine (sq_eq_sq₀ (by positivity) (by positivity)).mp ?_
  rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  field_simp

/-- `√(2/π) · √(2/π) · π/2 = 1`. -/
private lemma sqrt_two_div_pi_mul_self : (Real.sqrt (2 / Real.pi) : ℂ) * Real.sqrt (2 / Real.pi) *
    (Real.pi / 2) = 1 := by
  rw [← ofReal_mul, Real.mul_self_sqrt (by positivity)]
  have : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  push_cast
  field_simp

/-- `t ↦ e^{-at}` is integrable on `(0, ∞)` for `ℜa > 0`. -/
private lemma integrableOn_cexp_neg_mul {a : ℂ} (ha : 0 < a.re) :
    IntegrableOn (fun t : ℝ => cexp (-a * t)) (Ioi 0) :=
  integrableOn_exp_mul_complex_Ioi (by simpa using ha) 0

/-- `t ↦ t e^{-at}` is integrable on `(0, ∞)` for `ℜa > 0`. -/
private lemma integrableOn_mul_cexp_neg_mul {a : ℂ} (ha : 0 < a.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) * cexp (-a * t)) (Ioi 0) := by
  have hi := Complex.integrableOn_cpow_mul_exp_neg_mul (b := 2) (by norm_num) ha
  refine hi.congr_fun (fun t ht => ?_) measurableSet_Ioi
  simp only
  rw [show (2 : ℂ) - 1 = 1 by norm_num, cpow_one]
  ring_nf

/-- Fourier cosine transform of `(1 + at) e^{-at}`: `√(2/π) · 2a³/(a² + ξ²)²`, `ℜa > 0`. -/
private lemma fourierCosTransform_one_add_mul_exp_neg {a : ℂ} (ha : 0 < a.re) (ξ : ℝ) :
    fourierCosTransform (fun t : ℝ => (1 + a * t) * cexp (-a * t)) ξ =
      (Real.sqrt (2 / Real.pi) : ℂ) * (2 * a ^ 3 / (a ^ 2 + ξ ^ 2) ^ 2) := by
  have h1 := laplaceTransform_cos (a := (ξ : ℂ)) (s := a) (by simpa using ha)
  have h2 := laplaceTransform_mul_cos (a := (ξ : ℂ)) (s := a) (by simpa using ha)
  unfold laplaceTransform at h1 h2
  have hb : ∀ t : ℝ, ‖Complex.cos ((ξ : ℂ) * t)‖ ≤ 1 := fun t => by
    rw [← ofReal_mul, ← ofReal_cos, norm_real, Real.norm_eq_abs]
    exact Real.abs_cos_le_one _
  have hm : AEStronglyMeasurable (fun t : ℝ => Complex.cos ((ξ : ℂ) * t))
      (volume.restrict (Ioi 0)) := (by fun_prop : Continuous fun t : ℝ =>
        Complex.cos ((ξ : ℂ) * t)).aestronglyMeasurable
  have i1 : IntegrableOn (fun t : ℝ => cexp (-a * t) * Complex.cos ((ξ : ℂ) * t)) (Ioi 0) :=
    (integrableOn_cexp_neg_mul ha).mul_bdd hm (Eventually.of_forall hb)
  have i2 : IntegrableOn (fun t : ℝ => cexp (-a * t) * ((t : ℂ) * Complex.cos ((ξ : ℂ) * t)))
      (Ioi 0) := by
    refine IntegrableOn.congr_fun ((integrableOn_mul_cexp_neg_mul ha).mul_bdd hm
      (Eventually.of_forall hb)) (fun t _ => ?_) measurableSet_Ioi
    ring
  unfold fourierCosTransform
  congr 1
  rw [integral_congr_ae (g := fun t : ℝ => cexp (-a * t) * Complex.cos ((ξ : ℂ) * t) +
      a * (cexp (-a * t) * ((t : ℂ) * Complex.cos ((ξ : ℂ) * t))))
    (Eventually.of_forall fun t => by simp only [ofReal_cos, ofReal_mul]; ring),
    integral_add i1 (i2.const_mul a), integral_const_mul, h1, h2]
  have h0 := sq_add_sq_ne_zero ha ξ
  field_simp
  ring

/-- DLMF Table 1.14.2, row 3: `1/(a² + t²) ↦ √(π/2) e^{-ax}/a`, `ℜa > 0`. -/
@[dlmf 1.14.T2]
theorem fourierCosTransform_inv_sq_add_sq {a : ℂ} (ha : 0 < a.re) {x : ℝ} (hx : 0 < x) :
    fourierCosTransform (fun t => 1 / (a ^ 2 + t ^ 2)) x =
      (Real.sqrt (Real.pi / 2) : ℂ) * cexp (-a * x) / a := by
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha
  have hF : IntegrableOn (fourierCosTransform fun t : ℝ => cexp (-a * t)) (Ioi 0) := by
    have h := (integrableOn_pow_div_sq_add_sq_pow ha 0 1 (by norm_num)).const_mul
      ((Real.sqrt (2 / Real.pi) : ℂ) * a)
    refine IntegrableOn.congr_fun h (fun ξ _ => ?_) measurableSet_Ioi
    rw [fourierCosTransform_exp_neg ha]
    ring
  have hinv := fourierCosTransform_inversion (integrableOn_cexp_neg_mul ha) hx one_pos
    (boundedVariationOn_Icc_of_contDiff (contDiff_cexp_neg_mul a) (by linarith)) (by fun_prop) hF
  simp_rw [fourierCosTransform_exp_neg ha] at hinv
  unfold fourierCosTransform
  have hint : (∫ ξ in Ioi (0 : ℝ), (Real.sqrt (2 / Real.pi) : ℂ) * (a / (a ^ 2 + ξ ^ 2)) *
      (Real.cos (x * ξ) : ℂ)) = (Real.sqrt (2 / Real.pi) : ℂ) * a *
      ∫ t in Ioi (0 : ℝ), 1 / (a ^ 2 + t ^ 2) * (Real.cos (x * t) : ℂ) := by
    rw [← integral_const_mul]
    congr 1; funext t; ring
  rw [hint] at hinv
  generalize (∫ t in Ioi (0 : ℝ), 1 / (a ^ 2 + (t : ℂ) ^ 2) * (Real.cos (x * t) : ℂ)) = J at hinv ⊢
  rw [sqrt_pi_div_two_eq, hinv]
  have hs := sqrt_two_div_pi_mul_self
  push_cast
  field_simp
  linear_combination (-(2 * J)) * hs

/-- DLMF Table 1.14.2, row 4: `1/(a² + t²)² ↦ √(π/2) (1 + ax) e^{-ax}/(2a³)`, `ℜa > 0`. -/
@[dlmf 1.14.T2]
theorem fourierCosTransform_inv_sq_add_sq_sq {a : ℂ} (ha : 0 < a.re) {x : ℝ} (hx : 0 < x) :
    fourierCosTransform (fun t => 1 / (a ^ 2 + t ^ 2) ^ 2) x =
      (Real.sqrt (Real.pi / 2) : ℂ) * (1 + a * x) * cexp (-a * x) / (2 * a ^ 3) := by
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha
  have hfi : IntegrableOn (fun t : ℝ => (1 + a * t) * cexp (-a * t)) (Ioi 0) := by
    refine IntegrableOn.congr_fun ((integrableOn_cexp_neg_mul ha).add
      ((integrableOn_mul_cexp_neg_mul ha).const_mul a)) (fun t _ => ?_) measurableSet_Ioi
    simp only [Pi.add_apply]; ring
  have hF : IntegrableOn (fourierCosTransform fun t : ℝ => (1 + a * t) * cexp (-a * t))
      (Ioi 0) := by
    have h := (integrableOn_pow_div_sq_add_sq_pow ha 0 2 (by norm_num)).const_mul
      ((Real.sqrt (2 / Real.pi) : ℂ) * (2 * a ^ 3))
    refine IntegrableOn.congr_fun h (fun ξ _ => ?_) measurableSet_Ioi
    rw [fourierCosTransform_one_add_mul_exp_neg ha]
    ring
  have hinv := fourierCosTransform_inversion hfi hx one_pos
    (boundedVariationOn_Icc_of_contDiff ((contDiff_const.add (contDiff_const.mul
      ofRealCLM.contDiff)).mul (contDiff_cexp_neg_mul a)) (by linarith)) (by fun_prop) hF
  simp_rw [fourierCosTransform_one_add_mul_exp_neg ha] at hinv
  unfold fourierCosTransform
  have hint : (∫ ξ in Ioi (0 : ℝ), (Real.sqrt (2 / Real.pi) : ℂ) *
      (2 * a ^ 3 / (a ^ 2 + ξ ^ 2) ^ 2) * (Real.cos (x * ξ) : ℂ)) =
      (Real.sqrt (2 / Real.pi) : ℂ) * (2 * a ^ 3) *
      ∫ t in Ioi (0 : ℝ), 1 / (a ^ 2 + t ^ 2) ^ 2 * (Real.cos (x * t) : ℂ) := by
    rw [← integral_const_mul]
    congr 1; funext t; ring
  rw [hint] at hinv
  generalize (∫ t in Ioi (0 : ℝ), 1 / (a ^ 2 + (t : ℂ) ^ 2) ^ 2 *
    (Real.cos (x * t) : ℂ)) = J at hinv ⊢
  have hs := sqrt_two_div_pi_mul_self
  rw [sqrt_pi_div_two_eq, mul_assoc, hinv]
  push_cast
  field_simp
  linear_combination (-2 * J) * hs

/-- DLMF Table 1.14.2, row 5: `4a³/(4a⁴ + t⁴) ↦ √π e^{-ax} sin(ax + ¼π)`, `ℜa > 0`. -/
@[dlmf 1.14.T2]
theorem fourierCosTransform_quartic {a : ℂ} (ha : 0 < a.re) {x : ℝ} (hx : 0 < x) :
    fourierCosTransform (fun t => 4 * a ^ 3 / (4 * a ^ 4 + t ^ 4)) x =
      (Real.sqrt Real.pi : ℂ) * cexp (-a * x) * Complex.sin (a * x + Real.pi / 4) := by
  sorry

/-- DLMF Table 1.14.2, row 7: `e^{-at²} ↦ (2a)^{-1/2} e^{-x²/(4a)}`, `ℜa > 0`, principal power. -/
@[dlmf 1.14.T2]
theorem fourierCosTransform_gaussian {a : ℂ} (ha : 0 < a.re) {x : ℝ} :
    fourierCosTransform (fun t => cexp (-a * t ^ 2)) x =
      (2 * a) ^ (-(1 / 2 : ℂ)) * cexp (-x ^ 2 / (4 * a)) := by
  have hf : Integrable (fun t : ℝ => cexp (-a * t ^ 2)) := by
    simpa using integrable_cexp_quadratic ha 0 0
  have hi := integral_eq_integral_Ioi_add_neg (integrable_mul_cexp_I_mul hf x)
  have he (t : ℝ) : cexp (-a * t ^ 2) * cexp (I * x * t) +
      cexp (-a * (-t) ^ 2) * cexp (I * x * (-t)) =
      2 * (cexp (-a * t ^ 2) * (Real.cos (x * t) : ℂ)) := by
    simp only [neg_sq, ofReal_cos, Complex.cos]
    rw [show I * (x : ℂ) * t = ↑x * t * I by ring,
      show I * (x : ℂ) * -t = -(↑x * t * I) by ring]
    push_cast
    ring
  simp only [ofReal_neg] at hi
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => he t), integral_const_mul] at hi
  have hg := fourierIntegral_gaussian ha (x : ℂ)
  simp_rw [mul_comm (cexp (I * (x : ℂ) * _))] at hg
  have h := hi.symm.trans hg
  unfold fourierCosTransform
  have hn := gaussian_normalization ha
  have hc := inv_sqrt_two_pi_mul_two
  linear_combination (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ * h -
    (∫ t in Ioi (0 : ℝ), cexp (-a * t ^ 2) * (Real.cos (x * t) : ℂ)) * hc +
    cexp (-(x : ℂ) ^ 2 / (4 * a)) * hn

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
  have h := (Complex.continuous_ofReal.tendsto (Real.pi / 2)).comp
    (TauCeti.Contour.tendsto_integral_sin_mul_div_atTop hx)
  have hn : Real.sqrt (2 / Real.pi) * (Real.pi / 2) = Real.sqrt (Real.pi / 2) := by
    apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    field_simp
  have hlim := h.const_mul (Real.sqrt (2 / Real.pi) : ℂ)
  rw [← ofReal_mul, hn] at hlim
  convert hlim using 1
  funext R
  dsimp only [Function.comp_def]
  rw [← intervalIntegral.integral_ofReal]
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  push_cast
  ring

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

/-- DLMF Table 1.14.3, row 9: `e^{-at} ↦ √(2/π) x/(a² + x²)`, `ℜa > 0`. -/
@[dlmf 1.14.T3]
theorem fourierSinTransform_exp_neg {a : ℂ} (ha : 0 < a.re) {x : ℝ} :
    fourierSinTransform (fun t => cexp (-a * t)) x =
      (Real.sqrt (2 / Real.pi) : ℂ) * (x / (a ^ 2 + x ^ 2)) := by
  have h := laplaceTransform_sin (a := x) (s := a) (by simpa using ha)
  unfold fourierSinTransform
  congr 1
  convert h using 1
  simp only [laplaceTransform, ← ofReal_mul, ← ofReal_sin]

/-- DLMF Table 1.14.3, row 10: `t e^{-at} ↦ √(2/π) 2ax/(a² + x²)²`, `ℜa > 0`. -/
@[dlmf 1.14.T3]
theorem fourierSinTransform_mul_exp_neg {a : ℂ} (ha : 0 < a.re) {x : ℝ} :
    fourierSinTransform (fun t => t * cexp (-a * t)) x =
      (Real.sqrt (2 / Real.pi) : ℂ) * (2 * a * x / (a ^ 2 + x ^ 2) ^ 2) := by
  have h := laplaceTransform_mul_sin (a := x) (s := a) (by simpa using ha)
  unfold fourierSinTransform
  congr 1
  convert h using 1
  · unfold laplaceTransform
    congr 1; funext t
    simp only [← ofReal_mul, ← ofReal_sin]
    push_cast
    ring
  · ring

/-- `√(π/8) = √(2/π) · π/4`. -/
private lemma sqrt_pi_div_eight_eq :
    Real.sqrt (Real.pi / 8) = Real.sqrt (2 / Real.pi) * (Real.pi / 4) := by
  refine (sq_eq_sq₀ (by positivity) (by positivity)).mp ?_
  rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  field_simp
  ring

/-- DLMF Table 1.14.3, row 5: `t/(a² + t²) ↦ √(π/2) e^{-ax}`, `ℜa > 0` (conditionally
convergent). -/
@[dlmf 1.14.T3]
theorem tendsto_fourierSinTransform_div_sq_add_sq {a : ℂ} (ha : 0 < a.re) {x : ℝ}
    (hx : 0 < x) :
    Tendsto (fun R : ℝ => (Real.sqrt (2 / Real.pi) : ℂ) *
        ∫ t in (0 : ℝ)..R, t / (a ^ 2 + t ^ 2) * Real.sin (x * t)) atTop
      (𝓝 ((Real.sqrt (Real.pi / 2) : ℂ) * cexp (-a * x))) := by
  have hc : Continuous fun t : ℝ => cexp (-a * t) := by fun_prop
  have h := (tendsto_fourierSinTransform_inversion (integrableOn_cexp_neg_mul ha) hx one_pos
    (boundedVariationOn_Icc_of_contDiff (contDiff_cexp_neg_mul a) (by linarith))
    (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)).const_mul
    (Real.sqrt (Real.pi / 2) : ℂ)
  rw [← two_mul, mul_div_cancel_left₀ _ two_ne_zero] at h
  refine h.congr fun R => ?_
  simp_rw [fourierSinTransform_exp_neg ha]
  have hs := sqrt_two_div_pi_mul_self
  have h2 : (Real.sqrt (Real.pi / 2) : ℂ) = Real.sqrt (2 / Real.pi) * (Real.pi / 2) := by
    rw [sqrt_pi_div_two_eq]; push_cast; ring
  have hI : (∫ t in (0 : ℝ)..R, (Real.sqrt (2 / Real.pi) : ℂ) *
      ((t : ℂ) / (a ^ 2 + (t : ℂ) ^ 2)) * Real.sin (x * t)) = (Real.sqrt (2 / Real.pi) : ℂ) *
      ∫ t in (0 : ℝ)..R, (t : ℂ) / (a ^ 2 + (t : ℂ) ^ 2) * Real.sin (x * t) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext t; ring
  rw [h2, hI]
  generalize (∫ t in (0 : ℝ)..R, (t : ℂ) / (a ^ 2 + (t : ℂ) ^ 2) * Real.sin (x * t)) = J
  linear_combination (Real.sqrt (2 / Real.pi) : ℂ) * J * hs

/-- DLMF Table 1.14.3, row 6: `t/(a² + t²)² ↦ √(π/8) (x/a) e^{-ax}`, `ℜa > 0`. -/
@[dlmf 1.14.T3]
theorem fourierSinTransform_div_sq_add_sq_sq {a : ℂ} (ha : 0 < a.re) {x : ℝ} (hx : 0 < x) :
    fourierSinTransform (fun t => t / (a ^ 2 + t ^ 2) ^ 2) x =
      (Real.sqrt (Real.pi / 8) : ℂ) * (x / a) * cexp (-a * x) := by
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha
  have hF : IntegrableOn (fourierSinTransform fun t : ℝ => (t : ℂ) * cexp (-a * t)) (Ioi 0) := by
    have h := (integrableOn_pow_div_sq_add_sq_pow ha 1 2 (by norm_num)).const_mul
      ((Real.sqrt (2 / Real.pi) : ℂ) * (2 * a))
    refine IntegrableOn.congr_fun h (fun ξ _ => ?_) measurableSet_Ioi
    rw [fourierSinTransform_mul_exp_neg ha]
    ring
  have hinv := fourierSinTransform_inversion (integrableOn_mul_cexp_neg_mul ha) hx one_pos
    (boundedVariationOn_Icc_of_contDiff (ofRealCLM.contDiff.mul (contDiff_cexp_neg_mul a))
      (by linarith)) (by fun_prop) hF
  simp_rw [fourierSinTransform_mul_exp_neg ha] at hinv
  unfold fourierSinTransform
  have hint : (∫ ξ in Ioi (0 : ℝ), (Real.sqrt (2 / Real.pi) : ℂ) *
      (2 * a * ξ / (a ^ 2 + ξ ^ 2) ^ 2) * (Real.sin (x * ξ) : ℂ)) =
      (Real.sqrt (2 / Real.pi) : ℂ) * (2 * a) *
      ∫ t in Ioi (0 : ℝ), t / (a ^ 2 + t ^ 2) ^ 2 * (Real.sin (x * t) : ℂ) := by
    rw [← integral_const_mul]
    congr 1; funext t; ring
  rw [hint] at hinv
  generalize (∫ t in Ioi (0 : ℝ), (t : ℂ) / (a ^ 2 + (t : ℂ) ^ 2) ^ 2 *
    (Real.sin (x * t) : ℂ)) = J at hinv ⊢
  have hs := sqrt_two_div_pi_mul_self
  rw [sqrt_pi_div_eight_eq, mul_assoc, show (x : ℂ) / a * cexp (-a * x) =
    x * cexp (-a * x) / a by ring, hinv]
  push_cast
  field_simp
  linear_combination (-4 * J) * hs

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

/-- DLMF Table 1.14.3, row 11: `t e^{-at²} ↦ (2a)^{-3/2} x e^{-x²/(4a)}`, `|ph a| < ½π`
(that is, `ℜa > 0`), principal power. -/
@[dlmf 1.14.T3]
theorem fourierSinTransform_mul_gaussian {a : ℂ} (ha : 0 < a.re) {x : ℝ} :
    fourierSinTransform (fun t => t * cexp (-a * t ^ 2)) x =
      (2 * a) ^ (-(3 / 2 : ℂ)) * x * cexp (-x ^ 2 / (4 * a)) := by
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha
  have hcos (t : ℝ) : ‖Complex.cos ((x : ℂ) * t)‖ ≤ 1 := by
    rw [← ofReal_mul, ← ofReal_cos, norm_real, Real.norm_eq_abs]
    exact Real.abs_cos_le_one _
  have hsin (t : ℝ) : ‖Complex.sin ((x : ℂ) * t)‖ ≤ 1 := by
    rw [← ofReal_mul, ← ofReal_sin, norm_real, Real.norm_eq_abs]
    exact Real.abs_sin_le_one _
  have hC : IntegrableOn (fun t : ℝ => cexp (-a * t ^ 2) * Complex.cos (x * t)) (Ioi 0) := by
    refine ((integrable_cexp_neg_mul_sq ha).integrableOn (s := Ioi 0) |>.bdd_mul
      (c := 1) (by fun_prop) (Filter.Eventually.of_forall hcos)).congr ?_
    exact Filter.Eventually.of_forall fun t => mul_comm _ _
  have hS : IntegrableOn (fun t : ℝ => t * cexp (-a * t ^ 2) * Complex.sin (x * t)) (Ioi 0) := by
    refine ((integrable_mul_cexp_neg_mul_sq ha).integrableOn (s := Ioi 0) |>.bdd_mul
      (c := 1) (by fun_prop) (Filter.Eventually.of_forall hsin)).congr ?_
    exact Filter.Eventually.of_forall fun t => mul_comm _ _
  have hd (t : ℝ) : HasDerivAt
      (fun u : ℝ => cexp (-a * u ^ 2) * Complex.sin (x * u))
      ((-2 * a) * (t * cexp (-a * t ^ 2) * Complex.sin (x * t)) +
        x * (cexp (-a * t ^ 2) * Complex.cos (x * t))) t := by
    convert (((((hasDerivAt_id (t : ℂ)).pow 2).const_mul (-a)).cexp).mul
      (((hasDerivAt_id (t : ℂ)).const_mul (x : ℂ)).csin)).comp_ofReal using 1 <;> dsimp
    congr 1 <;> ring
  have ht : Tendsto (fun t : ℝ => cexp (-a * t ^ 2) * Complex.sin (x * t)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have he : Tendsto (fun t : ℝ => Real.exp (-a.re * t ^ 2)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp ((tendsto_pow_atTop two_ne_zero).const_mul_atTop_of_neg
        (neg_lt_zero.mpr ha))
    apply squeeze_zero (fun t => norm_nonneg _) _ he
    intro t
    rw [norm_mul, norm_cexp_neg_mul_sq]
    exact mul_le_of_le_one_right (Real.exp_pos _).le (hsin t)
  have hi := integral_Ioi_of_hasDerivAt_of_tendsto' (fun t _ => hd t)
    ((hS.const_mul (-2 * a)).add (hC.const_mul (x : ℂ))) ht
  rw [integral_add (hS.const_mul _) (hC.const_mul _), integral_const_mul,
    integral_const_mul] at hi
  simp only [ofReal_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    Complex.exp_zero, mul_zero, Complex.sin_zero, mul_zero, sub_zero] at hi
  have hc := fourierCosTransform_gaussian ha (x := x)
  unfold fourierCosTransform at hc
  simp_rw [← ofReal_mul, ← ofReal_cos, ← ofReal_sin] at hi
  have hp : (2 * a) ^ (-(3 / 2 : ℂ)) = (2 * a) ^ (-(1 / 2 : ℂ)) / (2 * a) := by
    rw [show -(3 / 2 : ℂ) = -(1 / 2 : ℂ) + -1 by ring,
      cpow_add _ _ (mul_ne_zero (by norm_num) ha0), cpow_neg_one]
    rfl
  unfold fourierSinTransform
  dsimp only
  rw [hp]
  rw [show (2 * a) ^ (-(1 / 2 : ℂ)) / (2 * a) * x * cexp (-(x : ℂ) ^ 2 / (4 * a)) =
    ((2 * a) ^ (-(1 / 2 : ℂ)) * x * cexp (-(x : ℂ) ^ 2 / (4 * a))) / (2 * a) by ring]
  have ha2 : 2 * a ≠ 0 := mul_ne_zero (by norm_num) ha0
  apply (eq_div_iff ha2).mpr
  linear_combination -(Real.sqrt (2 / Real.pi) : ℂ) * hi + (x : ℂ) * hc

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

/-! ### Table 1.14.5: Mellin transforms `∫₀^∞ x^{s-1} f(x) dx` (Mathlib's `mellin`) -/

/-- DLMF Table 1.14.5, row 2: `f = 1` for `x < a`, `0` for `x ≥ a`: `a^s/s`, `a ≥ 0`, `ℜs > 0`. -/
@[dlmf 1.14.T5]
theorem mellin_indicator_lt {a : ℝ} (ha : 0 ≤ a) {s : ℂ} (hs : 0 < s.re) :
    mellin (fun x => (Iio a).indicator (fun _ => (1 : ℂ)) x) s = (a : ℂ) ^ s / s := by
  have hs0 : s ≠ 0 := fun h => by simp [h] at hs
  unfold mellin
  have he : (fun x : ℝ => (x : ℂ) ^ (s - 1) •
      (Iio a).indicator (fun _ => (1 : ℂ)) x) =
      (Iio a).indicator (fun x => (x : ℂ) ^ (s - 1)) := by
    ext x
    by_cases hx : x ∈ Iio a <;> simp [hx]
  rw [he, setIntegral_indicator measurableSet_Iio, Ioi_inter_Iio,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ha,
    integral_cpow (Or.inl (by simp; linarith)), sub_add_cancel,
    ofReal_zero, Complex.zero_cpow hs0, sub_zero]

/-- DLMF Table 1.14.5, row 3: `ln(a/x)` for `x < a`, `0` for `x ≥ a`: `a^s/s²`, `a ≥ 0`;
valid for `ℜs > 0` (DLMF: `ℜs > 1`). -/
@[dlmf 1.14.T5]
theorem mellin_log_indicator_lt {a : ℝ} (ha : 0 ≤ a) {s : ℂ} (hs : 0 < s.re) :
    mellin (fun x => (Iio a).indicator (fun x => (Real.log (a / x) : ℂ)) x) s =
      (a : ℂ) ^ s / s ^ 2 := by
  have hs0 : s ≠ 0 := fun h => by simp [h] at hs
  rcases ha.eq_or_lt with rfl | ha
  · simp [mellin, Complex.zero_cpow hs0]
  let g : ℝ → ℂ := (Ioi 0).indicator (fun u => cexp (-s * u) * u)
  have he : (fun u : ℝ => cexp (-s * u) *
      (Iio a).indicator (fun x => (Real.log (a / x) : ℂ)) (Real.exp (-u))) =
      fun u => (a : ℂ) ^ s * g (u + Real.log a) := by
    funext u
    have hi : Real.exp (-u) < a ↔ 0 < u + Real.log a := by
      rw [← Real.log_lt_log_iff (Real.exp_pos _) ha, Real.log_exp]
      constructor <;> intro h <;> linarith
    by_cases hu : 0 < u + Real.log a
    · rw [indicator_of_mem (hi.mpr hu)]
      dsimp only [g]
      rw [indicator_of_mem hu, Real.log_div ha.ne' (Real.exp_pos _).ne', Real.log_exp]
      have hExp : (a : ℂ) ^ s * cexp (-s * ((u + Real.log a : ℝ) : ℂ)) = cexp (-s * u) := by
        rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr ha.ne'), ← ofReal_log ha.le, ← Complex.exp_add]
        congr 1
        push_cast
        ring
      rw [← mul_assoc, hExp]
      congr 1
      push_cast
      ring
    · rw [indicator_of_notMem (show Real.exp (-u) ∉ Iio a from fun h => hu (hi.mp h))]
      simp only [g, indicator_of_notMem (show u + Real.log a ∉ Ioi 0 from hu), mul_zero]
  rw [mellin_eq_integral_exp_mul, he, integral_const_mul, integral_add_right_eq_self,
    integral_indicator measurableSet_Ioi]
  have h := laplaceTransform_pow_div_factorial 1 hs
  simp only [laplaceTransform, pow_one, Nat.factorial_one, Nat.cast_one, div_one] at h
  rw [show (1 : ℕ) + 1 = 2 from rfl] at h
  rw [h]
  ring

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
  have h := DLMF.Gamma.mellin_one_add_cpow_neg (a := 1) hs0 (by simpa using hs1)
  simpa [Complex.cpow_neg, Complex.Gamma_one, Complex.Gamma_mul_Gamma_one_sub,
    mul_comm] using h

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

/-- A boundary term `F(t) tˢ/s` tends to zero where `|F(t)| ≤ C t^q` and `t^{q + ℜs} → 0`. -/
private lemma tendsto_mul_cpow_div_of_abs_le {l : Filter ℝ} {F : ℝ → ℝ} {s : ℂ} {C q : ℝ}
    (hl : ∀ᶠ t in l, 0 < t ∧ |F t| ≤ C * t ^ q)
    (hlim : Tendsto (fun t : ℝ => t ^ (q + s.re)) l (𝓝 0)) :
    Tendsto (fun t : ℝ => (F t : ℂ) * ((t : ℂ) ^ s / s)) l (𝓝 0) := by
  have h2 : Tendsto (fun t : ℝ => C * t ^ (q + s.re) / ‖s‖) l (𝓝 0) := by
    simpa using (hlim.const_mul C).div_const ‖s‖
  refine squeeze_zero_norm' ?_ h2
  filter_upwards [hl] with t ⟨ht, hF⟩
  rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_cpow_eq_rpow_re_of_pos ht, Real.rpow_add ht]
  have hpos : 0 ≤ t ^ s.re / ‖s‖ := by positivity
  calc |F t| * (t ^ s.re / ‖s‖) ≤ C * t ^ q * (t ^ s.re / ‖s‖) :=
        mul_le_mul_of_nonneg_right hF hpos
    _ = C * (t ^ q * t ^ s.re) / ‖s‖ := by ring

/-- `t^p → 0` as `t → 0⁺` for `p > 0`. -/
private lemma tendsto_rpow_nhdsGT_zero {p : ℝ} (hp : 0 < p) :
    Tendsto (fun t : ℝ => t ^ p) (𝓝[>] 0) (𝓝 0) := by
  have := (Real.continuousAt_rpow_const 0 p (Or.inr hp.le)).tendsto
  rw [Real.zero_rpow hp.ne'] at this
  exact this.mono_left nhdsWithin_le_nhds

/-- DLMF Table 1.14.5, row 8: `ln(1 + x)/x ↦ π csc(sπ)/(1 - s)`, `0 < ℜs < 1`. -/
@[dlmf 1.14.T5]
theorem mellin_log_one_add_div {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    mellin (fun x => (Real.log (1 + x) / x : ℂ)) s =
      Real.pi / Complex.sin (s * Real.pi) / (1 - s) := by
  have hs1' : s - 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  set ε := (1 - s.re) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hε1 : ε ≤ 1 := by rw [hε]; linarith
  -- bounds on `log (1 + t)`
  have hlog0 : ∀ t : ℝ, 0 < t → 0 ≤ Real.log (1 + t) := fun t ht =>
    Real.log_nonneg (by linarith)
  have hlog1 : ∀ t : ℝ, 0 < t → Real.log (1 + t) ≤ t := fun t ht => by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + t by linarith); linarith
  have hlog2 : ∀ t : ℝ, 1 ≤ t → Real.log (1 + t) ≤ 2 / ε * t ^ ε := fun t ht => by
    have h1 := Real.log_le_rpow_div (show (0 : ℝ) ≤ 1 + t by linarith) hε0
    have h2 : (1 + t) ^ ε ≤ (2 * t) ^ ε :=
      Real.rpow_le_rpow (by linarith) (by linarith) hε0.le
    have h3 : (2 * t) ^ ε ≤ 2 * t ^ ε := by
      rw [Real.mul_rpow (by norm_num) (by linarith)]
      gcongr
      calc (2 : ℝ) ^ ε ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hε1
        _ = 2 := Real.rpow_one 2
    calc Real.log (1 + t) ≤ (1 + t) ^ ε / ε := h1
      _ ≤ 2 * t ^ ε / ε := by gcongr; exact h2.trans h3
      _ = 2 / ε * t ^ ε := by ring
  have hcast : ∀ t : ℝ, (Real.log (1 + t) : ℂ) / (t : ℂ) = ((Real.log (1 + t) / t : ℝ) : ℂ) :=
    fun t => by push_cast; rfl
  -- convergence of the two Mellin integrals
  have hc1 : MellinConvergent (fun t : ℝ => 1 / (1 + (t : ℂ))) s := by
    have hnorm : ∀ t : ℝ, 0 < t → ‖1 / (1 + (t : ℂ))‖ = 1 / (1 + t) := fun t ht => by
      rw [show (1 : ℂ) + (t : ℂ) = ((1 + t : ℝ) : ℂ) by push_cast; ring, norm_div,
        norm_one, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    refine mellinConvergent_of_isBigO_rpow (a := 1) (b := 0) ?_ ?_ hs1 ?_ hs0
    · refine ContinuousOn.locallyIntegrableOn (fun t ht => ?_) measurableSet_Ioi
      refine (continuousAt_const.div (continuousAt_const.add
        Complex.continuous_ofReal.continuousAt) ?_).continuousWithinAt
      intro h
      have h' : ((1 + t : ℝ) : ℂ) = 0 := by push_cast; exact h
      have : (0 : ℝ) < 1 + t := by have : (0 : ℝ) < t := ht; linarith
      exact this.ne' (by exact_mod_cast h')
    · refine Asymptotics.IsBigO.of_bound 1 ?_
      filter_upwards [eventually_gt_atTop 0] with t ht
      rw [hnorm t ht, Real.norm_of_nonneg (Real.rpow_nonneg ht.le _), Real.rpow_neg_one,
        one_mul, one_div]
      exact inv_anti₀ ht (by linarith)
    · refine Asymptotics.IsBigO.of_bound 1 ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht' : (0 : ℝ) < t := ht
      rw [hnorm t ht', neg_zero, Real.rpow_zero, norm_one, one_mul,
        div_le_one (by linarith)]
      linarith
  have hc2 : MellinConvergent (fun t : ℝ => (Real.log (1 + t) / t : ℂ)) s := by
    refine mellinConvergent_of_isBigO_rpow (a := 1 - ε) (b := 0) ?_ ?_ (by rw [hε]; linarith)
      ?_ hs0
    · refine ContinuousOn.locallyIntegrableOn (fun t ht => ?_) measurableSet_Ioi
      have ht' : (0 : ℝ) < t := ht
      refine ContinuousAt.continuousWithinAt ?_
      refine ContinuousAt.div ?_ Complex.continuous_ofReal.continuousAt
        (by exact_mod_cast ht'.ne')
      exact Complex.continuous_ofReal.continuousAt.comp
        ((continuousAt_const.add continuousAt_id).log
          (show (1 : ℝ) + t ≠ 0 by linarith))
    · refine Asymptotics.IsBigO.of_bound (2 / ε) ?_
      filter_upwards [eventually_ge_atTop 1] with t ht
      have ht0 : (0 : ℝ) < t := by linarith
      rw [hcast,
        Complex.norm_real, Real.norm_of_nonneg (div_nonneg (hlog0 t ht0) ht0.le),
        Real.norm_of_nonneg (Real.rpow_nonneg ht0.le _), neg_sub, div_le_iff₀ ht0]
      calc Real.log (1 + t) ≤ 2 / ε * t ^ ε := hlog2 t ht
        _ = 2 / ε * t ^ (ε - 1) * t := by
          rw [mul_assoc, ← Real.rpow_add_one ht0.ne']; ring_nf
    · refine Asymptotics.IsBigO.of_bound 1 ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : (0 : ℝ) < t := ht
      rw [hcast,
        Complex.norm_real, Real.norm_of_nonneg (div_nonneg (hlog0 t ht0) ht0.le), neg_zero,
        Real.rpow_zero, norm_one, one_mul, div_le_one ht0]
      exact hlog1 t ht0
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul (a := 0) (a' := 0) (b' := 0)
    (u := fun t => (Real.log (1 + t) : ℂ)) (u' := fun t => ((1 / (1 + t) : ℝ) : ℂ))
    (v := fun t => (t : ℂ) ^ (s - 1) / (s - 1)) (v' := fun t => (t : ℂ) ^ (s - 1 - 1))
    (fun t ht => by
      have ht' : (0 : ℝ) < t := ht
      have h := ((hasDerivAt_id t).const_add 1).log (by simp; linarith)
      simpa using h.ofReal_comp)
    (fun t ht => by
      have h := (hasDerivAt_ofReal_cpow_const (ne_of_gt ht) hs1').div_const (s - 1)
      rwa [mul_div_cancel_left₀ _ hs1'] at h)
    (by
      refine hc2.congr_fun (fun t ht => ?_) measurableSet_Ioi
      have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (show (0 : ℝ) < t from ht))
      have hcp : (t : ℂ) ^ (s - 1) = (t : ℂ) ^ (s - 1 - 1) * t := by
        have h := Complex.cpow_add (s - 1 - 1) 1 ht'
        rwa [Complex.cpow_one, sub_add_cancel] at h
      simp only [Pi.mul_apply, smul_eq_mul]
      rw [hcp]
      field_simp)
    (by
      have hI : IntegrableOn (fun x : ℝ => 1 / (s - 1) *
          ((x : ℂ) ^ (s - 1) • (1 / (1 + (x : ℂ))))) (Ioi 0) :=
        Integrable.const_mul hc1 (1 / (s - 1))
      refine hI.congr_fun (fun t _ => ?_) measurableSet_Ioi
      simp only [Pi.mul_apply, smul_eq_mul]
      push_cast; ring)
    (tendsto_mul_cpow_div_of_abs_le (C := 1) (q := 1)
      (by
        filter_upwards [self_mem_nhdsWithin] with t ht
        have ht0 : (0 : ℝ) < t := ht
        refine ⟨ht0, ?_⟩
        rw [Real.rpow_one, one_mul, abs_of_nonneg (hlog0 t ht0)]
        exact hlog1 t ht0)
      (tendsto_rpow_nhdsGT_zero (by simp; linarith)))
    (tendsto_mul_cpow_div_of_abs_le (C := 2 / ε) (q := ε)
      (by
        filter_upwards [eventually_ge_atTop 1] with t ht
        have ht0 : (0 : ℝ) < t := by linarith
        exact ⟨ht0, by rw [abs_of_nonneg (hlog0 t ht0)]; exact hlog2 t ht⟩)
      (by
        have := tendsto_rpow_neg_atTop (y := ε) hε0
        convert this using 2
        simp only [sub_re, one_re]
        rw [hε]; ring_nf))
  simp only [sub_zero, zero_sub] at hibp
  have hm : mellin (fun t : ℝ => (Real.log (1 + t) / t : ℂ)) s =
      ∫ t in Ioi (0 : ℝ), (Real.log (1 + t) : ℂ) * (t : ℂ) ^ (s - 1 - 1) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (show (0 : ℝ) < t from ht))
    have hcp : (t : ℂ) ^ (s - 1) = (t : ℂ) ^ (s - 1 - 1) * t := by
      have h := Complex.cpow_add (s - 1 - 1) 1 ht'
      rwa [Complex.cpow_one, sub_add_cancel] at h
    simp only [smul_eq_mul]
    rw [hcp]
    field_simp
  have hm2 : ∫ t in Ioi (0 : ℝ), ((1 / (1 + t) : ℝ) : ℂ) * ((t : ℂ) ^ (s - 1) / (s - 1)) =
      1 / (s - 1) * mellin (fun t : ℝ => 1 / (1 + (t : ℂ))) s := by
    rw [mellin, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [smul_eq_mul]
    push_cast; ring
  rw [hm, hibp, hm2, mellin_inv_one_add hs0 hs1]
  have h1s : (1 : ℂ) - s ≠ 0 := fun h => hs1' (by linear_combination -h)
  field_simp
  ring

/-- Mellin transform of `t ↦ 1/(1 + t²)` at `s + 1`: `π/(2 cos(½sπ))`, `-1 < ℜs < 1`. -/
private lemma mellin_inv_one_add_sq_add_one {s : ℂ} (hs0 : -1 < s.re) (hs1 : s.re < 1) :
    MellinConvergent (fun t : ℝ => 1 / (1 + (t : ℂ) ^ 2)) (s + 1) ∧
      mellin (fun t : ℝ => 1 / (1 + (t : ℂ) ^ 2)) (s + 1) =
        Real.pi / (2 * Complex.cos (s * Real.pi / 2)) := by
  have hne : ∀ t : ℝ, 1 + (t : ℂ) ^ 2 ≠ 0 := fun t h => by
    have h' : ((1 + t ^ 2 : ℝ) : ℂ) = 0 := by push_cast; exact h
    have : (0 : ℝ) < 1 + t ^ 2 := by positivity
    exact this.ne' (by exact_mod_cast h')
  have hnorm : ∀ t : ℝ, ‖1 / (1 + (t : ℂ) ^ 2)‖ = 1 / (1 + t ^ 2) := fun t => by
    rw [show (1 : ℂ) + (t : ℂ) ^ 2 = ((1 + t ^ 2 : ℝ) : ℂ) by push_cast; ring, norm_div,
      norm_one, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  refine ⟨?_, ?_⟩
  · refine mellinConvergent_of_isBigO_rpow (a := 2) (b := 0) ?_ ?_ (by simp; linarith) ?_
      (by simp; linarith)
    · refine ContinuousOn.locallyIntegrableOn ?_ measurableSet_Ioi
      exact (continuous_const.div (continuous_const.add
        (Complex.continuous_ofReal.pow 2)) hne).continuousOn
    · refine Asymptotics.IsBigO.of_bound 1 ?_
      filter_upwards [eventually_gt_atTop 0] with t ht
      rw [hnorm, Real.norm_of_nonneg (Real.rpow_nonneg ht.le _), one_mul, Real.rpow_neg ht.le,
        Real.rpow_two, one_div]
      exact inv_anti₀ (by positivity) (by linarith)
    · refine Asymptotics.IsBigO.of_bound 1 ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      rw [hnorm, neg_zero, Real.rpow_zero, norm_one, one_mul]
      rw [div_le_one (by positivity)]
      nlinarith
  · have h := mellin_comp_rpow (fun t : ℝ => 1 / (1 + (t : ℂ))) (s + 1) 2
    simp only [Real.rpow_two, Complex.ofReal_pow] at h
    rw [h, mellin_inv_one_add (by simp; linarith) (by simp; linarith)]
    have hc : Complex.sin ((s + 1) / 2 * Real.pi) = Complex.cos (s * Real.pi / 2) := by
      rw [show (s + 1) / 2 * Real.pi = s * Real.pi / 2 + Real.pi / 2 by ring,
        Complex.sin_add_pi_div_two]
    push_cast
    rw [hc]
    simp only [abs_two, Complex.real_smul]
    push_cast
    field_simp

/-- Mellin transform by parts for `F` with `F'(t) = c/(1 + t²)`. -/
private lemma mellin_eq_of_hasDerivAt_div_one_add_sq {F : ℝ → ℝ} {c : ℝ} {s : ℂ}
    (hs0 : -1 < s.re) (hs1 : s.re < 1) (hs : s ≠ 0)
    (hF : ∀ t : ℝ, 0 < t → HasDerivAt F (c / (1 + t ^ 2)) t)
    (hconv : MellinConvergent (fun t => (F t : ℂ)) s)
    (h0 : Tendsto (fun t : ℝ => (F t : ℂ) * ((t : ℂ) ^ s / s)) (𝓝[>] 0) (𝓝 0))
    (hinf : Tendsto (fun t : ℝ => (F t : ℂ) * ((t : ℂ) ^ s / s)) atTop (𝓝 0)) :
    mellin (fun t => (F t : ℂ)) s =
      -(c * (Real.pi / Complex.cos (s * Real.pi / 2)) / (2 * s)) := by
  obtain ⟨hgc, hg⟩ := mellin_inv_one_add_sq_add_one hs0 hs1
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul (a := 0) (a' := 0) (b' := 0)
    (u := fun t => (F t : ℂ)) (u' := fun t => ((c / (1 + t ^ 2) : ℝ) : ℂ))
    (v := fun t => (t : ℂ) ^ s / s) (v' := fun t => (t : ℂ) ^ (s - 1))
    (fun t ht => (hF t ht).ofReal_comp)
    (fun t ht => by
      have h := (hasDerivAt_ofReal_cpow_const (ne_of_gt ht) hs).div_const s
      rwa [mul_div_cancel_left₀ _ hs] at h)
    (by
      refine hconv.congr_fun (fun t _ => ?_) measurableSet_Ioi
      simp only [Pi.mul_apply, smul_eq_mul]; ring)
    (by
      have hI : IntegrableOn (fun x : ℝ => (c : ℂ) / s *
          ((x : ℂ) ^ (s + 1 - 1) • (1 / (1 + (x : ℂ) ^ 2)))) (Ioi 0) :=
        Integrable.const_mul hgc ((c : ℂ) / s)
      refine hI.congr_fun (fun t _ => ?_) measurableSet_Ioi
      simp only [Pi.mul_apply, smul_eq_mul, add_sub_cancel_right]
      push_cast; ring)
    h0 hinf
  simp only [sub_zero, zero_sub] at hibp
  have hm : mellin (fun t => (F t : ℂ)) s =
      ∫ t in Ioi (0 : ℝ), (F t : ℂ) * (t : ℂ) ^ (s - 1) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [smul_eq_mul]; ring
  have hm2 : ∫ t in Ioi (0 : ℝ), ((c / (1 + t ^ 2) : ℝ) : ℂ) * ((t : ℂ) ^ s / s) =
      (c / s) * mellin (fun t : ℝ => 1 / (1 + (t : ℂ) ^ 2)) (s + 1) := by
    rw [mellin, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [smul_eq_mul, add_sub_cancel_right]
    push_cast; ring
  rw [hm, hibp, hm2, hg]
  field_simp

/-- DLMF Table 1.14.5, row 9: `arctan x ↦ -π sec(½sπ)/(2s)`, `-1 < ℜs < 0`. -/
@[dlmf 1.14.T5]
theorem mellin_arctan {s : ℂ} (hs0 : -1 < s.re) (hs1 : s.re < 0) :
    mellin (fun x => (Real.arctan x : ℂ)) s =
      -(Real.pi / Complex.cos (s * Real.pi / 2)) / (2 * s) := by
  have hs : s ≠ 0 := fun h => by simp [h] at hs1
  have hπ := Real.pi_pos
  have hbd : ∀ t : ℝ, |Real.arctan t| ≤ Real.pi / 2 := fun t =>
    abs_le.mpr ⟨(Real.neg_pi_div_two_lt_arctan t).le, (Real.arctan_lt_pi_div_two t).le⟩
  have h := mellin_eq_of_hasDerivAt_div_one_add_sq (F := Real.arctan) (c := 1) hs0 (by linarith)
    hs (fun t _ => by simpa using Real.hasDerivAt_arctan t)
    (by
      refine mellinConvergent_of_isBigO_rpow (a := 0) (b := -1)
        ((Complex.continuous_ofReal.comp Real.continuous_arctan).continuousOn.locallyIntegrableOn
          measurableSet_Ioi) ?_ hs1 ?_ hs0
      · refine Asymptotics.IsBigO.of_bound (Real.pi / 2) ?_
        filter_upwards [eventually_gt_atTop 0] with t ht
        rw [Complex.norm_real, Real.norm_eq_abs, neg_zero, Real.rpow_zero, norm_one, mul_one]
        exact hbd t
      · refine Asymptotics.IsBigO.of_bound 1 ?_
        filter_upwards [self_mem_nhdsWithin] with t ht
        rw [Complex.norm_real, Real.norm_eq_abs, neg_neg, Real.rpow_one, one_mul]
        exact Real.abs_arctan_le_abs)
    (tendsto_mul_cpow_div_of_abs_le (C := 1) (q := 1)
      (by
        filter_upwards [self_mem_nhdsWithin] with t ht
        refine ⟨ht, ?_⟩
        rw [Real.rpow_one, one_mul]
        exact Real.abs_arctan_le_abs.trans (abs_of_pos (show (0 : ℝ) < t from ht)).le)
      (tendsto_rpow_nhdsGT_zero (by linarith)))
    (tendsto_mul_cpow_div_of_abs_le (C := Real.pi / 2) (q := 0)
      (by
        filter_upwards [eventually_gt_atTop 0] with t ht
        exact ⟨ht, by rw [Real.rpow_zero, mul_one]; exact hbd t⟩)
      (by simpa using tendsto_rpow_neg_atTop (y := -s.re) (by linarith)))
  rw [h]
  push_cast
  ring

/-- DLMF Table 1.14.5, row 10: `arccot x = π/2 - arctan x ↦ π sec(½sπ)/(2s)`, `0 < ℜs < 1`. -/
@[dlmf 1.14.T5]
theorem mellin_arccot {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    mellin (fun x => ((Real.pi / 2 - Real.arctan x : ℝ) : ℂ)) s =
      Real.pi / Complex.cos (s * Real.pi / 2) / (2 * s) := by
  have hs : s ≠ 0 := fun h => by simp [h] at hs0
  have hπ := Real.pi_pos
  have hF : ∀ t : ℝ, 0 < t → |Real.pi / 2 - Real.arctan t| ≤ t⁻¹ ∧
      |Real.pi / 2 - Real.arctan t| ≤ Real.pi / 2 := by
    intro t ht
    rw [← Real.arctan_inv_of_pos ht, abs_of_pos (Real.arctan_pos.mpr (inv_pos.mpr ht))]
    exact ⟨Real.arctan_le_self (inv_pos.mpr ht).le, (Real.arctan_lt_pi_div_two _).le⟩
  have h := mellin_eq_of_hasDerivAt_div_one_add_sq
    (F := fun t => Real.pi / 2 - Real.arctan t) (c := -1) (by linarith) hs1
    hs (fun t _ => by
      have h := (hasDerivAt_const t (Real.pi / 2)).fun_sub (Real.hasDerivAt_arctan t)
      rwa [zero_sub, ← neg_div] at h)
    (by
      refine mellinConvergent_of_isBigO_rpow (a := 1) (b := 0)
        ((Complex.continuous_ofReal.comp (continuous_const.sub
          Real.continuous_arctan)).continuousOn.locallyIntegrableOn measurableSet_Ioi)
        ?_ hs1 ?_ hs0
      · refine Asymptotics.IsBigO.of_bound 1 ?_
        filter_upwards [eventually_gt_atTop 0] with t ht
        rw [Complex.norm_real, Real.norm_eq_abs, Real.norm_of_nonneg (Real.rpow_nonneg ht.le _),
          Real.rpow_neg_one, one_mul]
        exact (hF t ht).1
      · refine Asymptotics.IsBigO.of_bound (Real.pi / 2) ?_
        filter_upwards [self_mem_nhdsWithin] with t ht
        rw [Complex.norm_real, Real.norm_eq_abs, neg_zero, Real.rpow_zero, norm_one, mul_one]
        exact (hF t ht).2)
    (tendsto_mul_cpow_div_of_abs_le (C := Real.pi / 2) (q := 0)
      (by
        filter_upwards [self_mem_nhdsWithin] with t ht
        exact ⟨ht, by rw [Real.rpow_zero, mul_one]; exact (hF t ht).2⟩)
      (by simpa using tendsto_rpow_nhdsGT_zero hs0))
    (tendsto_mul_cpow_div_of_abs_le (C := 1) (q := -1)
      (by
        filter_upwards [eventually_gt_atTop 0] with t ht
        exact ⟨ht, by rw [Real.rpow_neg_one, one_mul]; exact (hF t ht).1⟩)
      (by
        have := tendsto_rpow_neg_atTop (y := 1 - s.re) (by linarith)
        simpa [neg_sub, sub_eq_neg_add] using this))
  rw [h]
  push_cast
  ring

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
