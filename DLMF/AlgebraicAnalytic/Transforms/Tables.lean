/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AlgebraicAnalytic.Transforms.Fourier
public import DLMF.AlgebraicAnalytic.Transforms.LaplaceTable
public import DLMF.Gamma.MellinBarnes
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
public import Mathlib.Analysis.MellinTransform
public import TauCeti.MeasureTheory.Integral.Bochner.Basic
public import TauCeti.Analysis.Fourier.ExpNegAbs
public import TauCeti.Analysis.Contour.WorkedExamples.HalfDisc.SineIntegral
public import DLMFMathlib.Analysis.MellinConvolution
public import DLMFMathlib.Analysis.SpecialFunctions.Pow.ComplexReal

/-!
# Tables of integral transforms (DLMF §1.14(vii), Tables 1.14.1–1.14.5)

The Laplace entries live in the imported `DLMF.AlgebraicAnalytic.Transforms.LaplaceTable`;
the Fourier and Mellin entries are proved here. Each row of DLMF Tables 1.14.1
(Fourier transforms, 1.14.1), 1.14.2 (Fourier cosine transforms,
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

Proved: the interval-indicator Fourier and cosine transforms (1.14.1.2, 1.14.2.2),
the two-sided exponential Fourier transform (1.14.1.3, from
`TauCeti.integral_exp_mul_I_mul_exp_neg_mul_abs`), the Gaussian Fourier transform (1.14.1.9),
the Gaussian and exponential cosine and sine entries and their first moments, the Dirichlet
sine integral (1.14.3.2, from `TauCeti.Contour.tendsto_integral_sin_mul_div_atTop`),
the elementary Laplace entries (in `LaplaceTable`), and the
Mellin transform of `1/(1+x)` (1.14.5.5). The latter specializes
`DLMF.Gamma.mellin_one_add_cpow_neg` and Mathlib’s Gamma reflection formula. Weighted
moment integrability uses TauCeti's `ExpDecay` and even-extension adapter; other rows are admitted.
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
  have hi := integral_eq_integral_Ioi_add_neg (g1e_integrable_mul_cexp hf x)
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
  have hi := integral_eq_integral_Ioi_add_neg (g1e_integrable_mul_cexp hf x)
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
theorem fourierCosTransform_exp_neg {a : ℂ} (ha : 0 < a.re) {x : ℝ} (_hx : 0 < x) :
    fourierCosTransform (fun t => cexp (-a * t)) x =
      (Real.sqrt (2 / Real.pi) : ℂ) * (a / (a ^ 2 + x ^ 2)) := by
  have h := laplaceTransform_cos (a := x) (s := a) (by simpa using ha)
  unfold fourierCosTransform
  congr 1
  convert h using 1
  simp only [laplaceTransform, ← ofReal_mul, ← ofReal_cos]

/-- DLMF Table 1.14.2, row 7: `e^{-at²} ↦ (2a)^{-1/2} e^{-x²/(4a)}`, `ℜa > 0`, principal power. -/
@[dlmf 1.14.T2]
theorem fourierCosTransform_gaussian {a : ℂ} (ha : 0 < a.re) {x : ℝ} (hx : 0 < x) :
    fourierCosTransform (fun t => cexp (-a * t ^ 2)) x =
      (2 * a) ^ (-(1 / 2 : ℂ)) * cexp (-x ^ 2 / (4 * a)) := by
  clear hx
  have hf : Integrable (fun t : ℝ => cexp (-a * t ^ 2)) := by
    simpa using integrable_cexp_quadratic ha 0 0
  have hi := integral_eq_integral_Ioi_add_neg (g1e_integrable_mul_cexp hf x)
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
theorem fourierSinTransform_exp_neg {a : ℂ} (ha : 0 < a.re) {x : ℝ} (_hx : 0 < x) :
    fourierSinTransform (fun t => cexp (-a * t)) x =
      (Real.sqrt (2 / Real.pi) : ℂ) * (x / (a ^ 2 + x ^ 2)) := by
  have h := laplaceTransform_sin (a := x) (s := a) (by simpa using ha)
  unfold fourierSinTransform
  congr 1
  convert h using 1
  simp only [laplaceTransform, ← ofReal_mul, ← ofReal_sin]

/-- DLMF Table 1.14.3, row 10: `t e^{-at} ↦ √(2/π) 2ax/(a² + x²)²`, `ℜa > 0`. -/
@[dlmf 1.14.T3]
theorem fourierSinTransform_mul_exp_neg {a : ℂ} (ha : 0 < a.re) {x : ℝ} (_hx : 0 < x) :
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

/-- DLMF Table 1.14.3, row 11: `t e^{-at²} ↦ (2a)^{-3/2} x e^{-x²/(4a)}`, `|ph a| < ½π`
(that is, `ℜa > 0`), principal power. -/
@[dlmf 1.14.T3]
theorem fourierSinTransform_mul_gaussian {a : ℂ} (ha : 0 < a.re) {x : ℝ} (hx : 0 < x) :
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
  have hc := fourierCosTransform_gaussian ha hx
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
