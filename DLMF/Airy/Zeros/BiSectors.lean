/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Airy.Basic.Properties
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Sectors containing the nonreal zeros of Bi and its derivative

An energy identity for Airy's equation on the segment from the origin to a zero shows that
all nonreal zeros of `Bi` and `Bi'` satisfy `π / 3 < |arg z| < π / 2`, as in DLMF §9.9(i).
The identity uses only the differential equation and the positive initial values.
-/

open Complex Filter Set MeasureTheory
open scoped Real Topology ComplexConjugate

@[expose] public noncomputable section

namespace DLMF.Airy.ComplexBiZeros

/-- Integrating Airy's equation along the segment to a zero gives its energy identity. -/
lemma energy_identity {z : ℂ} (hz : airyBi z = 0 ∨ airyBiDeriv z = 0) :
    z ^ 3 * (∫ t : ℝ in 0..1, t * ‖airyBi ((t : ℂ) * z)‖ ^ 2 : ℝ) +
      (∫ t : ℝ in 0..1, ‖z * airyBiDeriv ((t : ℂ) * z)‖ ^ 2 : ℝ) =
        -z * (airyBiDeriv 0 * conj (airyBi 0)) := by
  let u : ℝ → ℂ := fun t => airyBi ((t : ℂ) * z)
  let v : ℝ → ℂ := fun t => z * airyBiDeriv ((t : ℂ) * z)
  have hu (t : ℝ) : HasDerivAt u (v t) t := by
    have hp : HasDerivAt (fun t : ℝ => (t : ℂ) * z) z t := by
      simpa using ((hasDerivAt_id (t : ℂ)).comp_ofReal.mul_const z)
    have h := (hasDerivAt_airyBi ((t : ℂ) * z)).comp t hp
    simpa only [u, v, mul_comm, Function.comp_def] using! h
  have hv (t : ℝ) : HasDerivAt v (z ^ 3 * (t : ℂ) * u t) t := by
    have hp : HasDerivAt (fun t : ℝ => (t : ℂ) * z) z t := by
      simpa using ((hasDerivAt_id (t : ℂ)).comp_ofReal.mul_const z)
    have h := ((hasDerivAt_airyBiDeriv ((t : ℂ) * z)).comp t hp).const_mul z
    convert h using 1 <;> dsimp [u, v]
    ring
  have hc : Continuous u := continuous_iff_continuousAt.mpr fun t => (hu t).continuousAt
  have hcv : Continuous v := continuous_iff_continuousAt.mpr fun t => (hv t).continuousAt
  have hd (t : ℝ) : HasDerivAt (fun t => v t * conj (u t))
      (z ^ 3 * (t * ‖u t‖ ^ 2 : ℝ) + ‖v t‖ ^ 2) t := by
    have h := (hv t).mul (hu t).star
    change HasDerivAt (fun t => v t * conj (u t))
      (z ^ 3 * (t : ℂ) * u t * conj (u t) + v t * conj (v t)) t at h
    have he : z ^ 3 * (t : ℂ) * u t * conj (u t) + v t * conj (v t) =
        z ^ 3 * (t * ‖u t‖ ^ 2 : ℝ) + ‖v t‖ ^ 2 := by
      rw [show z ^ 3 * (t : ℂ) * u t * conj (u t) =
          z ^ 3 * (t : ℂ) * (u t * conj (u t)) by simp only [mul_assoc],
        Complex.mul_conj', Complex.mul_conj']
      push_cast
      ring
    simpa only [he] using! h
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1)
    (fun t _ => hd t)
    ((by fun_prop : Continuous fun t : ℝ =>
      z ^ 3 * (t * ‖u t‖ ^ 2 : ℝ) + ‖v t‖ ^ 2).intervalIntegrable _ _)
  rw [intervalIntegral.integral_add
      ((by fun_prop : Continuous fun t : ℝ => z ^ 3 * (t * ‖u t‖ ^ 2 : ℝ)).intervalIntegrable 0 1)
      ((by fun_prop : Continuous fun t : ℝ => (‖v t‖ ^ 2 : ℂ)).intervalIntegrable 0 1),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
    show (∫ t : ℝ in 0..1, (‖v t‖ : ℂ) ^ 2) =
      ((∫ t : ℝ in 0..1, ‖v t‖ ^ 2 : ℝ) : ℂ) by
        convert (intervalIntegral.integral_ofReal (f := fun t => ‖v t‖ ^ 2)
          (a := (0 : ℝ)) (b := 1) (μ := volume)) using 2 with t
        push_cast
        rfl] at h
  have hend : v 1 * conj (u 1) = 0 := by
    rcases hz with hz | hz <;> simp [u, v, hz]
  rw [hend] at h
  simpa only [u, v, ofReal_zero, zero_mul, zero_sub, neg_mul, mul_assoc] using h

/-- A nonreal zero of `Bi` or `Bi'` lies to the right of the imaginary axis and
outside the rays of argument `±π / 3`. -/
lemma zero_re_pos_and_im_sq {z : ℂ} (him : z.im ≠ 0)
    (hz : airyBi z = 0 ∨ airyBiDeriv z = 0) :
    0 < z.re ∧ 3 * z.re ^ 2 < z.im ^ 2 := by
  let I : ℝ := ∫ t : ℝ in 0..1, t * ‖airyBi ((t : ℂ) * z)‖ ^ 2
  let J : ℝ := ∫ t : ℝ in 0..1, ‖z * airyBiDeriv ((t : ℂ) * z)‖ ^ 2
  let A : ℝ := (airyBiDeriv 0).re * (airyBi 0).re
  have hp0 : 0 < (airyBi 0).re := by
    rw [airyBi_zero, show (2 / 3 : ℂ) = ((2 / 3 : ℝ) : ℂ) by norm_num, Complex.Gamma_ofReal,
      ←ofReal_mul, ←ofReal_one, ←ofReal_div, ofReal_re]
    have hG := Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 2 / 3)
    positivity
  have hp1 : 0 < (airyBiDeriv 0).re := by
    rw [airyBiDeriv_zero, show (1 / 3 : ℂ) = ((1 / 3 : ℝ) : ℂ) by norm_num, Complex.Gamma_ofReal,
      ←ofReal_div, ofReal_re]
    have hG := Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 3)
    positivity
  have ha : 0 < A := mul_pos hp1 hp0
  have hi0 : (airyBi 0).im = 0 := by simpa using airyBi_ofReal_im 0
  have hi1 : (airyBiDeriv 0).im = 0 := by simpa using airyBiDeriv_ofReal_im 0
  have hprod : airyBiDeriv 0 * conj (airyBi 0) = (A : ℂ) := by
    apply Complex.ext <;> simp [A, mul_re, mul_im, hi0, hi1]
  have hE : z ^ 3 * (I : ℂ) + (J : ℂ) = -z * (A : ℂ) := by
    simpa only [I, J, hprod] using energy_identity hz
  have hInonneg : 0 ≤ I := intervalIntegral.integral_nonneg zero_le_one fun t ht =>
    mul_nonneg ht.1 (sq_nonneg _)
  have hJpos : 0 < J := by
    have hvcont : Continuous (fun t : ℝ => z * airyBiDeriv ((t : ℂ) * z)) := by
      apply Continuous.const_mul _ z
      apply (continuous_iff_continuousAt.mpr
        (fun w => (hasDerivAt_airyBiDeriv w).continuousAt)).comp
      fun_prop
    apply intervalIntegral.integral_pos zero_lt_one
      (hvcont.norm.pow 2).continuousOn (fun _ _ => sq_nonneg _) ?_
    refine ⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩
    simp only [Pi.pow_apply, ofReal_zero, zero_mul]
    apply sq_pos_of_ne_zero
    apply norm_ne_zero_iff.mpr
    apply mul_ne_zero (fun h => him (by simp [h]))
    intro h
    have hp := hp1
    rw [h, zero_re] at hp
    exact lt_irrefl _ hp
  have hre := congrArg Complex.re hE
  have him' := congrArg Complex.im hE
  simp only [add_re, mul_re, neg_re, ofReal_re, ofReal_im, mul_zero, sub_zero,
    add_im, mul_im, neg_im, add_zero] at hre him'
  have hcubeRe : (z ^ 3).re = z.re ^ 3 - 3 * z.re * z.im ^ 2 := by
    simp [pow_succ, mul_re, mul_im]
    ring
  have hcubeIm : (z ^ 3).im = (3 * z.re ^ 2 - z.im ^ 2) * z.im := by
    simp [pow_succ, mul_re, mul_im]
    ring
  rw [hcubeRe] at hre
  rw [hcubeIm] at him'
  have hfactor : z.im * ((3 * z.re ^ 2 - z.im ^ 2) * I + A) = 0 := by linear_combination him'
  have hscalar := (mul_eq_zero.mp hfactor).resolve_left him
  have hIpos : 0 < I := by
    apply lt_of_le_of_ne hInonneg
    intro h
    rw [←h] at hscalar
    simp only [mul_zero, zero_add] at hscalar
    linarith
  have hden : 3 * z.re ^ 2 - z.im ^ 2 < 0 := by nlinarith
  have hJ : J = z.re * (2 * (z.re ^ 2 + z.im ^ 2) * I) := by
    linear_combination hre - z.re * hscalar
  have hcoef : 0 < 2 * (z.re ^ 2 + z.im ^ 2) * I := by
    have hsq := sq_pos_of_ne_zero him
    positivity
  refine ⟨?_, by linarith⟩
  rw [hJ] at hJpos
  exact (mul_pos_iff_of_pos_right hcoef).mp hJpos

/-- Nonreal zeros of `Bi` and `Bi'` lie in `π / 3 < |arg z| < π / 2`. -/
lemma zero_sector {z : ℂ} (him : z.im ≠ 0)
    (hz : airyBi z = 0 ∨ airyBiDeriv z = 0) :
    π / 3 < |arg z| ∧ |arg z| < π / 2 := by
  obtain ⟨hre, him2⟩ := zero_re_pos_and_im_sq him hz
  refine ⟨?_, abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre)⟩
  by_contra h
  have hθ : |arg z| ≤ π / 3 := not_lt.mp h
  have hc : 1 / 2 ≤ Real.cos (arg z) := by
    calc
      1 / 2 = Real.cos (π / 3) := Real.cos_pi_div_three.symm
      _ ≤ Real.cos |arg z| := Real.cos_le_cos_of_nonneg_of_le_pi
        (abs_nonneg _) (by linarith [Real.pi_pos]) hθ
      _ = Real.cos (arg z) := Real.cos_abs _
  have hz0 : z ≠ 0 := fun h => him (by simp [h])
  rw [Complex.cos_arg hz0] at hc
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hnorm : ‖z‖ ≤ 2 * z.re := by
    rw [le_div_iff₀ hn] at hc
    linarith
  have hs : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  nlinarith [norm_nonneg z]

end DLMF.Airy.ComplexBiZeros
