/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AlgebraicAnalytic.Transforms.Tables.Fourier
import DLMFMathlib.Analysis.Integral.QuadraticKernel

/-!
# Logarithmic Fourier cosine transforms

The radial integral of a quadratic resolvent gives the principal logarithm
`log (1+a²/t²)`. Absolute integrability permits exchanging its radial parameter
integral with the Fourier cosine integral. Subtraction gives the logarithmic
ratio formula with separate principal logarithms. For complex parameters the principal
logarithm of a quotient can differ from the difference of the principal logarithms, so
the latter is the stated convention.

## Main results

* `fourierCosTransform_log_one_add`: Table 1.14.2, row 10.
* `fourierCosTransform_log_sub_log`: Table 1.14.2, row 11.
-/

public noncomputable section

open Complex MeasureTheory Filter Set
open scoped Real Topology Nat

namespace DLMF.AlgebraicAnalytic

/-- DLMF Table 1.14.2, row 10: `ln(1 + a²/t²) ↦ √(2π) (1 - e^{-ax})/x`, `ℜa > 0`, principal
logarithm. -/
@[dlmf 1.14.T2]
theorem fourierCosTransform_log_one_add {a : ℂ} (ha : 0 < a.re) {x : ℝ} (hx : 0 < x) :
    fourierCosTransform (fun t => Complex.log (1 + a ^ 2 / t ^ 2)) x =
      (Real.sqrt (2 * Real.pi) : ℂ) * (1 - cexp (-a * x)) / x := by
  let F : ℝ × ℝ → ℂ := fun p => (2 * a ^ 2 * p.1 / ((a * p.1) ^ 2 + p.2 ^ 2)) *
    (Real.cos (x * p.2) : ℂ)
  have hF : Integrable F ((volume.restrict (Ioc (0 : ℝ) 1)).prod
      (volume.restrict (Ioi (0 : ℝ)))) := by
    refine (Complex.integrable_quadratic_log_kernel ha).norm.mono' (by fun_prop) ?_
    exact Eventually.of_forall fun p => by
      dsimp only [F]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_of_le_one_right (norm_nonneg _) (Real.abs_cos_le_one _)
  have hswap := integral_integral_swap (f := fun r t => F (r, t)) hF
  have hpoint {t : ℝ} (ht : 0 < t) : (∫ r : ℝ in Ioc 0 1, F (r, t)) =
      Complex.log (1 + a ^ 2 / t ^ 2) * (Real.cos (x * t) : ℂ) := by
    dsimp only [F]
    rw [integral_mul_const, ← intervalIntegral.integral_of_le zero_le_one,
      Complex.integral_quadratic_log_kernel ha ht]
  unfold fourierCosTransform
  rw [← integral_congr_ae ((ae_restrict_mem measurableSet_Ioi).mono fun t ht => hpoint ht),
    ← hswap, ← integral_const_mul]
  have hrow {r : ℝ} (hr : r ∈ Ioc (0 : ℝ) 1) :
      (Real.sqrt (2 / Real.pi) : ℂ) * (∫ t : ℝ in Ioi 0, F (r, t)) =
        (Real.sqrt (2 * Real.pi) : ℂ) * a * cexp (-(a * r) * x) := by
    have har : 0 < (a * r).re := by simpa using mul_pos ha hr.1
    have h := fourierCosTransform_inv_sq_add_sq har hx
    have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.1.ne'
    have ha0 : a ≠ 0 := fun he => by simp [he] at ha
    dsimp only [F]
    have he : (fun t : ℝ => 2 * a ^ 2 * r / ((a * r) ^ 2 + t ^ 2) *
        (Real.cos (x * t) : ℂ)) = fun t => (2 * a ^ 2 * r) *
          (1 / ((a * r) ^ 2 + t ^ 2) * (Real.cos (x * t) : ℂ)) := by
      funext t
      ring
    rw [he, integral_const_mul]
    unfold fourierCosTransform at h
    rw [mul_left_comm, h]
    have hroot : 2 * Real.sqrt (Real.pi / 2) = Real.sqrt (2 * Real.pi) := by
      calc
        _ = Real.sqrt 4 * Real.sqrt (Real.pi / 2) := by
          congr 1
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
          norm_num
        _ = Real.sqrt (4 * (Real.pi / 2)) := (Real.sqrt_mul (by norm_num) _).symm
        _ = _ := by congr 1; ring
    rw [← hroot]
    push_cast
    field_simp [hr0, ha0]
  rw [setIntegral_congr_fun measurableSet_Ioc (fun r hr => hrow hr)]
  simp_rw [mul_assoc]
  rw [integral_const_mul, ← intervalIntegral.integral_of_le zero_le_one]
  have hder (r : ℝ) : HasDerivAt (fun r : ℝ => -cexp (-(a * r) * x) / x)
      (a * cexp (-(a * r) * x)) r := by
    have h := (((((hasDerivAt_id r).ofReal_comp.const_mul a).mul_const
      (x : ℂ)).neg).cexp.neg).div_const (x : ℂ)
    simp only [id_eq, ofReal_one, mul_one, Pi.neg_apply] at h
    simp only [neg_mul]
    refine h.congr_deriv ?_
    have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
    field_simp [hx0]
  have hc : Continuous (fun r : ℝ => a * cexp (-(a * r) * x)) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hder r)
    (hc.intervalIntegrable _ _)]
  norm_num
  ring

/-- DLMF Table 1.14.2, row 11, **corrected**: `ln(a² + t²) - ln(b² + t²) ↦
√(2π) (e^{-bx} - e^{-ax})/x`, `ℜa, ℜb > 0`. DLMF writes `ln((a² + t²)/(b² + t²))`; with the
principal logarithm of the quotient this fails for some complex `a`, `b` (module docstring). -/
@[dlmf 1.14.T2]
theorem fourierCosTransform_log_sub_log {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) {x : ℝ}
    (hx : 0 < x) :
    fourierCosTransform (fun t => Complex.log (a ^ 2 + t ^ 2) - Complex.log (b ^ 2 + t ^ 2)) x =
      (Real.sqrt (2 * Real.pi) : ℂ) * (cexp (-b * x) - cexp (-a * x)) / x := by
  have hsplit {d : ℂ} (hd : 0 < d.re) {t : ℝ} (ht : 0 < t) :
      Complex.log (d ^ 2 + t ^ 2) = (Real.log (t ^ 2) : ℂ) +
        Complex.log (1 + d ^ 2 / t ^ 2) := by
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
    have he : (((t ^ 2 : ℝ) : ℂ)) * (1 + d ^ 2 / t ^ 2) = d ^ 2 + t ^ 2 := by
      push_cast
      field_simp [ht0]
      ring
    have hne : 1 + d ^ 2 / (t : ℂ) ^ 2 ≠ 0 := by
      intro hn
      rw [hn, mul_zero] at he
      exact sq_add_sq_ne_zero hd t he.symm
    rw [← he, Complex.log_ofReal_mul (sq_pos_of_pos ht) hne]
  have hiA := Complex.integrableOn_log_one_add_sq_div_sq_mul_cos ha x
  have hiB := Complex.integrableOn_log_one_add_sq_div_sq_mul_cos hb x
  have hlin : fourierCosTransform (fun t => Complex.log (a ^ 2 + t ^ 2) -
      Complex.log (b ^ 2 + t ^ 2)) x =
      fourierCosTransform (fun t => Complex.log (1 + a ^ 2 / t ^ 2)) x -
        fourierCosTransform (fun t => Complex.log (1 + b ^ 2 / t ^ 2)) x := by
    unfold fourierCosTransform
    rw [← mul_sub, ← integral_sub hiA hiB]
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [hsplit ha ht, hsplit hb ht]
    ring
  rw [hlin, fourierCosTransform_log_one_add ha hx,
    fourierCosTransform_log_one_add hb hx]
  ring

end DLMF.AlgebraicAnalytic
