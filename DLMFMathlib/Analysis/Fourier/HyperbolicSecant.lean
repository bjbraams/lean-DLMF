/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.SpecialFunctions.Gamma.BetaHalfLine
public import DLMFMathlib.Analysis.SpecialFunctions.ImproperIntegralsExtra
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
public import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Fourier transform of the hyperbolic secant

The exponential substitution in Euler's second beta integral, followed by Gamma reflection,
gives the Fourier transform of the hyperbolic secant.
-/

@[expose] public noncomputable section

open Complex MeasureTheory Set
open scoped Real

namespace Complex

/-- A bilateral Laplace integral for the hyperbolic secant on its strip of convergence. -/
theorem integral_exp_div_cosh {c : ℂ} (hc : |c.re| < 1 / 2) :
    Integrable (fun t : ℝ => exp (2 * c * t) / (Real.cosh t : ℝ)) ∧
      (∫ t : ℝ, exp (2 * c * t) / (Real.cosh t : ℝ)) = π / cos (π * c) := by
  let f : ℝ → ℝ := fun t => Real.exp (2 * t)
  let f' : ℝ → ℝ := fun t => 2 * Real.exp (2 * t)
  let a : ℂ := 1 / 2 + c
  let b : ℂ := 1 / 2 - c
  have ha : 0 < a.re := by
    dsimp [a]
    norm_num
    linarith [(abs_lt.mp hc).1]
  have hb : 0 < b.re := by
    dsimp [b]
    norm_num
    linarith [(abs_lt.mp hc).2]
  let g : ℝ → ℂ := fun u => (u : ℂ) ^ (a - 1) / (1 + (u : ℂ)) ^ (a + b)
  have hderiv : ∀ t ∈ (univ : Set ℝ), HasDerivWithinAt f (f' t) univ t := by
    intro t _
    convert (((hasDerivAt_id t).const_mul (2 : ℝ)).exp).hasDerivWithinAt using 1 <;>
      simp [f, f', mul_comm]
  have hinj : InjOn f univ := fun x _ y _ hxy => by
    have := Real.exp_injective hxy
    linarith
  have himage : f '' univ = Ioi 0 := by
    rw [image_univ]
    ext u
    exact ⟨fun ⟨t, ht⟩ => ht ▸ Real.exp_pos _, fun hu =>
      ⟨Real.log u / 2, by dsimp [f]; rw [mul_div_cancel₀ _ two_ne_zero, Real.exp_log hu]⟩⟩
  have key := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hderiv hinj g
  have keyI := integrableOn_image_iff_integrableOn_abs_deriv_smul
    MeasurableSet.univ hderiv hinj g
  rw [himage] at key keyI
  have hpt (t : ℝ) : exp (2 * c * t) / (Real.cosh t : ℝ) = |f' t| • g (f t) := by
    have hpow : ((Real.exp (2 * t) : ℝ) : ℂ) ^ (a - 1) =
        exp ((2 * (t : ℂ)) * (a - 1)) := by
      rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr (Real.exp_pos _).ne'),
        ← ofReal_log (Real.exp_pos _).le, Real.log_exp]
      push_cast; rfl
    have hcosh : (Real.cosh t : ℂ) =
        exp (-(t : ℂ)) * (1 + (Real.exp (2 * t) : ℝ)) / 2 := by
      rw [Real.cosh_eq]
      push_cast
      rw [mul_add, mul_one, ← exp_add]
      congr 1
      ring_nf
    have hE : exp (-(t : ℂ)) ≠ 0 := exp_ne_zero _
    have hD : (1 : ℂ) + (Real.exp (2 * t) : ℝ) ≠ 0 := by
      exact_mod_cast (show (1 : ℝ) + Real.exp (2 * t) ≠ 0 by positivity)
    dsimp [f, f', g]
    rw [abs_of_pos (by positivity), hpow,
      show a + b = 1 by dsimp [a, b]; ring, cpow_one, hcosh]
    push_cast
    rw [show 2 * c * t = (2 * (t : ℂ)) * (a - 1) + (t : ℂ) by dsimp [a]; ring,
      exp_add]
    field_simp [hD, hE]
    rw [← exp_add]
    ring_nf
  have hi : Integrable (fun t : ℝ => exp (2 * c * t) / (Real.cosh t : ℝ)) := by
    rw [← integrableOn_univ]
    exact (keyI.mp (integrableOn_cpow_div_one_add_cpow ha hb)).congr_fun
      (fun t _ => (hpt t).symm) MeasurableSet.univ
  refine ⟨hi, ?_⟩
  rw [show (fun t : ℝ => exp (2 * c * t) / (Real.cosh t : ℝ)) =
      fun t => |f' t| • g (f t) from funext hpt, ← setIntegral_univ, ← key]
  change (∫ u : ℝ in Ioi 0, (u : ℂ) ^ (a - 1) / (1 + (u : ℂ)) ^ (a + b)) = _
  rw [integral_cpow_div_one_add_cpow, betaIntegral_eq_Gamma_mul_div a b ha hb,
    show a + b = 1 by dsimp [a, b]; ring, Gamma_one, div_one,
    show b = 1 - a by dsimp [a, b]; ring, Gamma_mul_Gamma_one_sub]
  congr 1
  rw [show (π : ℂ) * a = π / 2 + π * c by dsimp [a]; ring, sin_add, sin_pi_div_two,
    cos_pi_div_two]
  ring

/-- The bilateral Laplace integral of the hyperbolic secant at any positive scale. -/
theorem integral_exp_div_cosh_mul {b : ℝ} (hb : 0 < b) {c : ℂ} (hc : |c.re| < b) :
    Integrable (fun t : ℝ => exp (c * t) / (Real.cosh (b * t) : ℝ)) ∧
      (∫ t : ℝ, exp (c * t) / (Real.cosh (b * t) : ℝ)) =
        (Real.pi : ℂ) / (b * cos (Real.pi * c / ((2 * b : ℝ) : ℂ))) := by
  let d : ℂ := c / ((2 * b : ℝ) : ℂ)
  have hd : |d.re| < 1 / 2 := by
    dsimp [d]
    rw [div_ofReal_re, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * b)]
    exact (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * b)).mpr (by linarith)
  obtain ⟨hi, hv⟩ := integral_exp_div_cosh hd
  have he (t : ℝ) : exp (2 * d * (b * t)) / (Real.cosh (b * t) : ℝ) =
      exp (c * t) / (Real.cosh (b * t) : ℝ) := by
    congr 2
    dsimp [d]
    push_cast
    field_simp [ofReal_ne_zero.mpr hb.ne']
  refine ⟨?_, ?_⟩
  · simpa only [ofReal_mul, he] using
      (integrable_comp_mul_left_iff (fun t : ℝ => exp (2 * d * t) /
        (Real.cosh t : ℝ)) hb.ne').mpr hi
  · have h := MeasureTheory.Measure.integral_comp_mul_left (fun t : ℝ => exp (2 * d * t) /
      (Real.cosh t : ℝ)) b
    rw [hv] at h
    simp only [ofReal_mul, he, Complex.real_smul, abs_of_pos (inv_pos.mpr hb)] at h
    rw [h]
    dsimp [d]
    push_cast
    field_simp [ofReal_ne_zero.mpr hb.ne']

end Complex

namespace Real

/-- The cosine transform of the hyperbolic secant on the whole real line. -/
theorem integral_cos_div_cosh (y : ℝ) :
    Integrable (fun x : ℝ => Real.cos (y * x) / Real.cosh x) ∧
      (∫ x : ℝ, Real.cos (y * x) / Real.cosh x) = π / Real.cosh (π * y / 2) := by
  let c : ℂ := (y : ℂ) * I / 2
  have hc : |c.re| < 1 / 2 := by simp [c]
  obtain ⟨hi, hv⟩ := Complex.integral_exp_div_cosh hc
  have hpt (x : ℝ) : (Complex.exp (2 * c * x) / (Real.cosh x : ℝ)).re =
      Real.cos (y * x) / Real.cosh x := by
    rw [show 2 * c * (x : ℂ) = ((y * x : ℝ) : ℂ) * I by dsimp [c]; push_cast; ring]
    rw [Complex.div_ofReal_re, Complex.exp_mul_I]
    simp only [Complex.add_re, Complex.mul_I_re, Complex.cos_ofReal_re,
      Complex.sin_ofReal_im, neg_zero, add_zero]
  have hiv : Integrable (fun x : ℝ => Real.cos (y * x) / Real.cosh x) := by
    have h := hi.re
    change Integrable (fun x : ℝ => (Complex.exp (2 * c * x) /
      (Real.cosh x : ℝ)).re) at h
    simpa only [hpt] using h
  refine ⟨hiv, ?_⟩
  have h := congrArg Complex.re hv
  have hI := integral_re hi
  change (∫ x : ℝ, (Complex.exp (2 * c * x) / (Real.cosh x : ℝ)).re) =
    (∫ x : ℝ, Complex.exp (2 * c * x) / (Real.cosh x : ℝ)).re at hI
  rw [← hI] at h
  have hcos : Complex.cos ((π : ℂ) * c) = (Real.cosh (π * y / 2) : ℝ) := by
    rw [show (π : ℂ) * c = ((π * y / 2 : ℝ) : ℂ) * I by dsimp [c]; push_cast; ring,
      Complex.cos_mul_I, ← Complex.ofReal_cosh]
  simpa only [hpt, hcos, Complex.div_ofReal_re, Complex.ofReal_re] using h

/-- The cosine transform of the hyperbolic secant on the positive half-line. -/
theorem integral_cos_div_cosh_Ioi (y : ℝ) :
    IntegrableOn (fun x : ℝ => Real.cos (y * x) / Real.cosh x) (Ioi 0) ∧
      (∫ x in Ioi (0 : ℝ), Real.cos (y * x) / Real.cosh x) =
        π / (2 * Real.cosh (π * y / 2)) := by
  obtain ⟨hi, hv⟩ := integral_cos_div_cosh y
  refine ⟨hi.integrableOn, ?_⟩
  have h := integral_comp_abs (f := fun x : ℝ => Real.cos (y * x) / Real.cosh x)
  have heq (x : ℝ) : Real.cos (y * |x|) / Real.cosh |x| =
      Real.cos (y * x) / Real.cosh x := by
    rw [Real.cosh_abs]
    rcases abs_choice x with h | h <;> rw [h]; simp [Real.cos_neg]
  simp only [heq] at h
  rw [hv] at h
  rw [show π / (2 * Real.cosh (π * y / 2)) = (π / Real.cosh (π * y / 2)) / 2 by ring]
  linarith

/-- The normalized hyperbolic-secant cosine transform. -/
theorem integral_cos_div_cosh_pi_mul_div_two_Ioi (t : ℝ) :
    IntegrableOn (fun x : ℝ => Real.cos (t * x) / Real.cosh (π * x / 2)) (Ioi 0) ∧
      (∫ x in Ioi (0 : ℝ), Real.cos (t * x) / Real.cosh (π * x / 2)) =
        1 / Real.cosh t := by
  let y : ℝ := 2 * t / π
  let f : ℝ → ℝ := fun x => Real.cos (y * x) / Real.cosh x
  obtain ⟨hi, hv⟩ := integral_cos_div_cosh_Ioi y
  have hp : 0 < π / 2 := by positivity
  have heq (x : ℝ) : f ((π / 2) * x) = Real.cos (t * x) / Real.cosh (π * x / 2) := by
    dsimp [f, y]
    congr 2 <;> field_simp
  refine ⟨?_, ?_⟩
  · have h := (integrableOn_Ioi_comp_mul_left_iff f 0 hp).mpr (by simpa using hi)
    simpa only [heq] using h
  · have h := integral_comp_mul_left_Ioi f 0 hp
    rw [mul_zero, show (∫ x in Ioi (0 : ℝ), f x) = π / (2 * Real.cosh (π * y / 2)) from hv]
      at h
    simp only [heq, smul_eq_mul] at h
    rw [h]
    dsimp [y]
    rw [show π * (2 * t / π) / 2 = t by field_simp]
    field_simp

/-- A polynomial divided by a hyperbolic cosine is integrable on the positive half-line. -/
theorem integrableOn_one_add_pow_div_cosh {r : ℝ} (hr : 0 < r) (n : ℕ) :
    IntegrableOn (fun x : ℝ => (1 + x) ^ n / Real.cosh (r * x)) (Ioi 0) := by
  have hpow (k : ℕ) : IntegrableOn (fun x : ℝ => x ^ k * Real.exp (-(r * x))) (Ioi 0) := by
    simpa only [Real.rpow_natCast] using
      integrableOn_rpow_mul_exp_neg_mul (r := (k : ℝ))
        (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]) hr
  have hsum : IntegrableOn (fun x : ℝ => ∑ k ∈ Finset.range (n + 1),
      (n.choose k : ℝ) * (x ^ k * Real.exp (-(r * x)))) (Ioi 0) := by
    apply integrable_finsetSum
    intro k _
    exact (hpow k).const_mul _
  have hpoly : IntegrableOn (fun x : ℝ => (1 + x) ^ n * Real.exp (-(r * x))) (Ioi 0) := by
    refine hsum.congr_fun (fun x _ => ?_) measurableSet_Ioi
    rw [show 1 + x = x + 1 by ring, add_pow, Finset.sum_mul]
    simp only [one_pow, mul_one]
    apply Finset.sum_congr rfl
    intro k _
    ring
  refine (hpoly.const_mul 2).mono'
    ((Continuous.div (by fun_prop) (by fun_prop)
      (fun x => (Real.cosh_pos (r * x)).ne')).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0 < x := hx
  have hP : 0 ≤ (1 + x) ^ n := by positivity
  have hB : 1 / Real.cosh (r * x) ≤ 2 * Real.exp (-(r * x)) := by
    rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _), div_mul_eq_mul_div,
      div_le_iff₀ (Real.cosh_pos _), Real.cosh_eq]
    linarith [Real.exp_pos (-(r * x))]
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hP (Real.cosh_pos _).le)]
  calc
    _ = (1 + x) ^ n * (1 / Real.cosh (r * x)) := by ring
    _ ≤ (1 + x) ^ n * (2 * Real.exp (-(r * x))) := mul_le_mul_of_nonneg_left hB hP
    _ = _ := by ring

end Real
