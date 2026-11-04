/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AlgebraicAnalytic.Transforms.Fourier
public import DLMF.AlgebraicAnalytic.Transforms.LaplaceTable
public import DLMF.AlgebraicAnalytic.Transforms.MellinTable
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
1.14.9) and 1.14.3 (Fourier sine transforms, 1.14.10) is a theorem here, tagged with the table
ID. The Laplace entries of Table 1.14.4 (1.14.17) are in the imported
`DLMF.AlgebraicAnalytic.Transforms.LaplaceTable`, the Mellin entries of Table 1.14.5 (1.14.32) in
the imported `DLMF.AlgebraicAnalytic.Transforms.MellinTable`.

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

## Implementation notes

Where the transform integral converges only conditionally (rows 1.14.1.10–11, 1.14.2.8–9,
1.14.3.2, 1.14.3.3, 1.14.3.5, 1.14.3.12, 1.14.3.14) the statement is the limit of the integrals
over `[-R, R]` or `[0, R]` as `R → ∞` (the Lebesgue integral would be Lean's junk value `0`).
Row 1.14.3.13 (`arctan(t/a)`) does not converge even conditionally; DLMF's entry is its Abel
value `lim_{ε→0+} ∫₀^∞ e^{-εt} …`, and it is stated so.

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

/-- `ℜ((a + ix)^{-1/2}) = (a + r)^{1/2}/(√2 r)` with `r = (a² + x²)^{1/2}`, `a > 0`. -/
private lemma re_cpow_neg_half {a : ℝ} (ha : 0 < a) (x : ℝ) :
    ((a + I * x) ^ (-(1 / 2 : ℂ))).re =
      Real.sqrt (a + Real.sqrt (a ^ 2 + x ^ 2)) /
        (Real.sqrt 2 * Real.sqrt (a ^ 2 + x ^ 2)) := by
  set w : ℂ := a + I * x with hw
  have hwre : w.re = a := by simp [hw]
  have hwim : w.im = x := by simp [hw]
  have hw0 : w ≠ 0 := fun h => by simp [h] at hwre; linarith
  have hnorm : ‖w‖ = Real.sqrt (a ^ 2 + x ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply, hwre, hwim]; ring_nf
  set r := Real.sqrt (a ^ 2 + x ^ 2) with hr
  have hr0 : 0 < r := by rw [← hnorm]; exact norm_pos_iff.mpr hw0
  have harg1 : -Real.pi ≤ w.arg := (neg_pi_lt_arg w).le
  have harg2 : w.arg ≤ Real.pi := arg_le_pi w
  have h := cpow_ofReal_re w (-(1 / 2 : ℝ))
  push_cast at h
  rw [h, hnorm, show w.arg * -(1 / 2 : ℝ) = -(w.arg / 2) by ring, Real.cos_neg,
    Real.cos_half harg1 harg2, Complex.cos_arg hw0, hwre, hnorm]
  have hs : Real.sqrt ((1 + a / r) / 2) = Real.sqrt (a + r) / (Real.sqrt 2 * Real.sqrt r) := by
    rw [← Real.sqrt_mul (by norm_num), ← Real.sqrt_div (by linarith)]
    congr 1
    field_simp
    ring
  rw [hs, Real.rpow_neg hr0.le, ← Real.sqrt_eq_rpow]
  have hsr : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr0
  field_simp
  rw [Real.sq_sqrt hr0.le]

/-- DLMF Table 1.14.1, row 6: `e^{-a|t|}/|t|^{1/2} ↦ (a + (a² + x²)^{1/2})^{1/2}/(a² + x²)^{1/2}`,
`a > 0`. -/
@[dlmf 1.14.T1]
theorem fourierTransform_exp_neg_abs_div_sqrt {a : ℝ} (ha : 0 < a) (x : ℝ) :
    fourierTransform (fun t => (Real.exp (-a * |t|) / Real.sqrt |t| : ℂ)) x =
      (Real.sqrt (a + Real.sqrt (a ^ 2 + x ^ 2)) / Real.sqrt (a ^ 2 + x ^ 2) : ℝ) := by
  set g : ℝ → ℂ := fun t => (Real.exp (-a * t) / Real.sqrt t : ℂ) with hg
  have hbound : IntegrableOn (fun t : ℝ => t ^ (-(1 / 2 : ℝ)) * Real.exp (-a * t ^ (1 : ℝ)))
      (Ioi 0) := integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num) one_pos ha
  have hnorm : ∀ t : ℝ, 0 < t → ∀ z : ℂ, z.re = a →
      ‖(t : ℂ) ^ ((1 / 2 : ℂ) - 1) * cexp (-(z * t))‖ =
        t ^ (-(1 / 2 : ℝ)) * Real.exp (-a * t ^ (1 : ℝ)) := by
    intro t ht z hz
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_exp, Real.rpow_one]
    congr 2
    · norm_num
    · simp [hz]
  have hpow : ∀ t : ℝ, 0 < t → (t : ℂ) ^ ((1 / 2 : ℂ) - 1) = ((Real.sqrt t)⁻¹ : ℝ) := by
    intro t ht
    rw [show (1 / 2 : ℂ) - 1 = -(1 / 2 : ℂ) by norm_num, cpow_neg, ofReal_inv]
    congr 1
    rw [Real.sqrt_eq_rpow, ofReal_cpow ht.le]
    norm_num
  have hIz : ∀ z : ℂ, z.re = a →
      IntegrableOn (fun t : ℝ => (t : ℂ) ^ ((1 / 2 : ℂ) - 1) * cexp (-(z * t))) (Ioi 0) := by
    intro z hz
    refine hbound.mono' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
      refine ContinuousAt.continuousWithinAt (ContinuousAt.mul ?_ (by fun_prop))
      exact ContinuousAt.cpow (f := fun u : ℝ => (u : ℂ)) continuous_ofReal.continuousAt
        continuousAt_const (by simpa using (show (0 : ℝ) < t from ht))
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact (hnorm t ht z hz).le
  have hgI : IntegrableOn g (Ioi 0) := by
    refine (hIz a (by simp)).congr_fun (fun t ht => ?_) measurableSet_Ioi
    simp only [hg]
    rw [hpow t ht]
    simp only [ofReal_exp, ofReal_mul, ofReal_neg, ofReal_inv]
    rw [div_eq_mul_inv, mul_comm]
    ring_nf
  have hf : Integrable (fun t => (Real.exp (-a * |t|) / Real.sqrt |t| : ℂ)) :=
    TauCeti.MeasureTheory.integrable_comp_abs hgI
  have hi := integral_eq_integral_Ioi_add_neg (integrable_mul_cexp_I_mul hf x)
  have he : ∀ t ∈ Ioi (0 : ℝ),
      (Real.exp (-a * |t|) / Real.sqrt |t| : ℂ) * cexp (I * x * t) +
        (Real.exp (-a * |-t|) / Real.sqrt |-t| : ℂ) * cexp (I * x * (-t)) =
      (t : ℂ) ^ ((1 / 2 : ℂ) - 1) * cexp (-((a - I * x) * t)) +
        (t : ℂ) ^ ((1 / 2 : ℂ) - 1) * cexp (-((a + I * x) * t)) := by
    intro t ht
    have e1 : cexp (-((a - I * x) * t)) = cexp (-(a : ℂ) * t) * cexp (I * x * t) := by
      rw [← Complex.exp_add]; ring_nf
    have e2 : cexp (-((a + I * x) * t)) = cexp (-(a : ℂ) * t) * cexp (I * x * (-t)) := by
      rw [← Complex.exp_add]; ring_nf
    rw [e1, e2, abs_neg, abs_of_pos (show (0 : ℝ) < t from ht), hpow t ht]
    push_cast
    ring
  simp only [ofReal_neg] at hi
  rw [setIntegral_congr_fun measurableSet_Ioi he, integral_add (hIz _ (by simp))
    (hIz _ (by simp)), integral_cpow_mul_cexp_neg_mul_Ioi (by norm_num) (by simp [ha]),
    integral_cpow_mul_cexp_neg_mul_Ioi (by norm_num) (by simp [ha])] at hi
  have hw : (a : ℂ) + I * x ∈ slitPlane := by
    rw [mem_slitPlane_iff]; left; simp [ha]
  have hc := cpow_conj ((a : ℂ) + I * x) (-(1 / 2 : ℂ)) (mem_slitPlane_iff_arg.mp hw).1
  have hconj : starRingEnd ℂ ((a : ℂ) + I * x) = a - I * x := by
    simp [conj_ofReal, conj_I]; ring
  have hn : starRingEnd ℂ (-(1 / 2 : ℂ)) = -(1 / 2 : ℂ) := by
    rw [map_neg, map_div₀, map_one, map_ofNat]
  rw [hn, hconj] at hc
  have hc' : ((a : ℂ) - I * x) ^ (-(1 / 2 : ℂ)) =
      starRingEnd ℂ (((a : ℂ) + I * x) ^ (-(1 / 2 : ℂ))) := by
    rw [hc, conj_conj]
  unfold fourierTransform
  rw [hi, hc', ← mul_add, add_comm (starRingEnd ℂ _), Complex.add_conj, re_cpow_neg_half ha x]
  have hΓ : Complex.Gamma (1 / 2) = (Real.sqrt Real.pi : ℂ) := by
    rw [Complex.Gamma_one_half_eq, Real.sqrt_eq_rpow, ofReal_cpow Real.pi_pos.le]
    norm_num
  rw [hΓ, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hr0 : 0 < Real.sqrt (a ^ 2 + x ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have h2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  push_cast
  have : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    rw [← ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have h2' : (Real.sqrt 2 : ℂ) ≠ 0 := ofReal_ne_zero.mpr h2.ne'
  have hpi' : (Real.sqrt Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr hpi.ne'
  have hr' : (Real.sqrt (a ^ 2 + x ^ 2) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr0.ne'
  field_simp
  linear_combination -(Real.sqrt (a + Real.sqrt (a ^ 2 + x ^ 2)) : ℂ) * this

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
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha
  have hne : ∀ t : ℝ, a ^ 2 + (t : ℂ) ^ 2 ≠ 0 := sq_add_sq_ne_zero ha
  -- the integrand and its partial fractions
  set F : ℝ → ℂ := fun t => 1 / ((t : ℂ) * (a ^ 2 + (t : ℂ) ^ 2)) * (Real.sin (x * t) : ℂ)
    with hFdef
  set A : ℝ → ℂ := fun t => ((t⁻¹ : ℝ) : ℂ) * (Real.sin (x * t) : ℂ) with hAdef
  set B : ℝ → ℂ := fun t => (t : ℂ) / (a ^ 2 + (t : ℂ) ^ 2) * (Real.sin (x * t) : ℂ)
    with hBdef
  have hpf : ∀ t, F t = (1 / a ^ 2) * (A t - B t) := by
    intro t
    simp only [hFdef, hAdef, hBdef]
    rcases eq_or_ne t 0 with rfl | ht
    · simp
    have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.2 ht
    push_cast
    field_simp [hne t]
    ring
  have hAb : ∀ t, ‖A t‖ ≤ x := by
    intro t
    simp only [hAdef, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs]
    rcases eq_or_ne t 0 with rfl | ht
    · simp; linarith
    have h := Real.abs_sin_le_abs (x := x * t)
    rw [abs_mul, abs_of_pos hx] at h
    calc |t|⁻¹ * |Real.sin (x * t)| ≤ |t|⁻¹ * (x * |t|) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = x := by field_simp
  have hAm : Measurable A := by simp only [hAdef]; fun_prop
  have hAi : ∀ R, IntervalIntegrable A volume 0 R := fun R =>
    (intervalIntegrable_const (c := x)).mono_fun' hAm.aestronglyMeasurable
      (Eventually.of_forall hAb)
  have hBc : Continuous B := by
    simp only [hBdef]
    exact (Continuous.div (by fun_prop) (by fun_prop) hne).mul (by fun_prop)
  -- integrability of `F`
  have hFi : IntegrableOn F (Ioi 0) := by
    have hg : IntegrableOn (fun t : ℝ => (x : ℂ) * ((t : ℂ) ^ 0 / (a ^ 2 + (t : ℂ) ^ 2) ^ 1))
        (Ioi 0) := (integrableOn_pow_div_sq_add_sq_pow ha 0 1 (by norm_num)).const_mul _
    refine Integrable.mono' hg.norm ?_ ?_
    · have hFm : Measurable F := by simp only [hFdef]; fun_prop
      exact hFm.aestronglyMeasurable
    · refine Eventually.of_forall fun t => ?_
      have hFt : F t = (t : ℂ) ^ 0 / (a ^ 2 + (t : ℂ) ^ 2) ^ 1 * A t := by
        simp only [hFdef, hAdef]
        rcases eq_or_ne t 0 with rfl | ht
        · simp
        have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.2 ht
        push_cast
        field_simp [hne t]
      rw [hFt, norm_mul, norm_mul (x : ℂ), Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hx, mul_comm x]
      exact mul_le_mul_of_nonneg_left (hAb t) (norm_nonneg _)
  -- limits
  have hlimF : Tendsto (fun R : ℝ => (Real.sqrt (2 / Real.pi) : ℂ) * ∫ t in (0 : ℝ)..R, F t)
      atTop (𝓝 (fourierSinTransform (fun t => 1 / (t * (a ^ 2 + t ^ 2))) x)) :=
    (intervalIntegral_tendsto_integral_Ioi 0 hFi tendsto_id).const_mul _
  have hlimA := tendsto_fourierSinTransform_inv hx
  have hlimB := tendsto_fourierSinTransform_div_sq_add_sq ha hx
  have hlim := (hlimA.sub hlimB).const_mul (1 / a ^ 2)
  refine tendsto_nhds_unique hlimF (hlim.congr' ?_) |>.trans ?_
  · filter_upwards [eventually_ge_atTop 0] with R hR
    simp only [intervalIntegral.integral_congr (fun t _ => hpf t)]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub (hAi R)
      (hBc.intervalIntegrable _ _)]
    simp only [hAdef, hBdef]
    ring
  · ring


/-- DLMF Table 1.14.3, row 8: `e^{-at}/t ↦ √(2/π) arctan(x/a)`, `ℜa > 0`, principal branch.
Stronger than DLMF, which assumes `x > 0`: every real `x` is allowed. -/
@[dlmf 1.14.T3]
theorem fourierSinTransform_exp_neg_div' {a : ℂ} (ha : 0 < a.re) (x : ℝ) :
    fourierSinTransform (fun t => cexp (-a * t) / t) x =
      (Real.sqrt (2 / Real.pi) : ℂ) * Complex.arctan (x / a) := by
  have h := laplaceTransform_sin_div (a := (x : ℂ)) (s := a) (by simpa using ha)
  unfold fourierSinTransform
  rw [← h]
  congr 1
  unfold laplaceTransform
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [ofReal_sin, ofReal_mul]
  ring

/-- DLMF Table 1.14.3, row 8: `e^{-at}/t ↦ √(2/π) arctan(x/a)`, `ℜa > 0`, principal branch. -/
@[dlmf 1.14.T3]
theorem fourierSinTransform_exp_neg_div {a : ℂ} (ha : 0 < a.re) {x : ℝ} (_hx : 0 < x) :
    fourierSinTransform (fun t => cexp (-a * t) / t) x =
      (Real.sqrt (2 / Real.pi) : ℂ) * Complex.arctan (x / a) :=
  fourierSinTransform_exp_neg_div' ha x

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

end DLMF.AlgebraicAnalytic
