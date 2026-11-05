/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.PSeries
public import DLMFMathlib.Analysis.SpecialFunctions.ImproperIntegralsExtra
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Fourier transforms of the Bose–Einstein kernel

The partial fractions and sine transform of `1 / (exp (2πx) - 1)`. The partial fractions
follow from Mathlib's cotangent expansion at an imaginary argument. These identities provide
the integral kernel in Hermite's representation of the Hurwitz zeta function.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory
open scoped Real Topology

namespace Real

/-- The partial fraction expansion of the regularized Bose–Einstein kernel. -/
theorem hasSum_two_mul_div_sq_add_two_pi_mul_sq {s : ℝ} (hs : 0 < s) :
    HasSum (fun m : ℕ => 2 * s / (s ^ 2 + (2 * π * (m + 1)) ^ 2))
      (1 / (Real.exp s - 1) - 1 / s + 1 / 2) := by
  set f : ℕ → ℝ := fun m => 2 * s / (s ^ 2 + (2 * π * (m + 1)) ^ 2) with hf
  set c : ℂ := -(2 * π) * I with hc
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hc0 : c ≠ 0 := by simp [hc, Real.pi_ne_zero]
  have hσ : 0 < s / (2 * π) := by positivity
  set x : ℂ := ((s / (2 * π) : ℝ) : ℂ) * I with hxdef
  have hxim : x.im = s / (2 * π) := by rw [hxdef, mul_I_im, ofReal_re]
  have hx : x ∈ Complex.integerComplement := by
    rintro ⟨n, hn⟩
    have := congrArg Complex.im hn
    rw [hxim, intCast_im] at this
    linarith
  have hterm : ∀ n : ℕ, cotTerm x n = c * (f n : ℂ) := by
    intro n
    have hprod : (x + (n + 1)) * (x - (n + 1)) =
        -(((s / (2 * π)) ^ 2 + ((n : ℝ) + 1) ^ 2 : ℝ) : ℂ) := by
      simp only [hxdef]
      push_cast
      linear_combination ((s : ℂ) / (2 * π)) ^ 2 * I_sq
    have hD : (0 : ℝ) < (s / (2 * π)) ^ 2 + ((n : ℝ) + 1) ^ 2 := by positivity
    have hD' : (0 : ℝ) < s ^ 2 + (2 * π * ((n : ℝ) + 1)) ^ 2 := by positivity
    rw [cotTerm_identity hx n, hprod]
    simp only [hf, hc, hxdef]
    have h1 : (((s / (2 * π)) ^ 2 + ((n : ℝ) + 1) ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
    have h2 : ((s ^ 2 + (2 * π * ((n : ℝ) + 1)) ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hD'.ne'
    push_cast at h1 h2 ⊢
    field_simp
  have hcot : (π : ℂ) * Complex.cot (π * x) - 1 / x =
      c * (((1 / (Real.exp s - 1) - 1 / s + 1 / 2) : ℝ) : ℂ) := by
    have hpx : (π : ℂ) * x = ((s / 2 : ℝ) : ℂ) * I := by
      rw [hxdef, ← mul_assoc, ← ofReal_mul, show π * (s / (2 * π)) = s / 2 by
        field_simp]
    have hsinh : Real.sinh (s / 2) ≠ 0 := (Real.sinh_pos_iff.mpr (by linarith)).ne'
    have hC : Real.cosh (s / 2) =
        (2 * (1 / (Real.exp s - 1) - 1 / s + 1 / 2) + 2 / s) * Real.sinh (s / 2) := by
      have hs2 : Real.exp s = Real.exp (s / 2) ^ 2 := by
        rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
      have hE : Real.exp s - 1 ≠ 0 := (sub_pos.mpr (Real.one_lt_exp_iff.mpr hs)).ne'
      have hS : s ≠ 0 := hs.ne'
      rw [Real.cosh_eq, Real.sinh_eq, Real.exp_neg]
      rw [hs2] at hE ⊢
      field_simp
      ring
    rw [hpx, Complex.cot_eq_cos_div_sin, Complex.cos_mul_I, Complex.sin_mul_I, ← ofReal_cosh,
      ← ofReal_sinh, hC, ofReal_mul]
    have hs0 : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
    have hsh : (Real.sinh (s / 2) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hsinh
    generalize ((Real.sinh (s / 2) : ℝ) : ℂ) = S at hsh ⊢
    have hσ0 : ((s / (2 * π) : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hσ.ne'
    rw [mul_comm S I, mul_div_mul_right _ _ hsh, hxdef, ← div_div, Complex.div_I,
      Complex.div_I, hc]
    push_cast
    field_simp
    ring
  have hsumC : Summable fun n => c * (f n : ℂ) := (summable_cotTerm hx).congr hterm
  have hsumR : Summable f := by
    have := hsumC.mul_left c⁻¹
    simp only [← mul_assoc, inv_mul_cancel₀ hc0, one_mul] at this
    exact Complex.summable_ofReal.mp this
  have h := cot_series_rep' hx
  rw [hcot] at h
  have hterm' : ∀ n : ℕ, 1 / (x - (n + 1)) + 1 / (x + (n + 1)) = c * (f n : ℂ) := hterm
  simp_rw [hterm'] at h
  rw [tsum_mul_left, ← Complex.ofReal_tsum] at h
  have h' : (1 / (Real.exp s - 1) - 1 / s + 1 / 2) = ∑' n, f n := by
    have hh := congrArg Complex.re (mul_left_cancel₀ hc0 h)
    simpa only [Complex.ofReal_re] using hh
  rw [h']
  exact hsumR.hasSum

/-- A geometric expansion of the Bose–Einstein kernel. -/
theorem hasSum_exp_neg_two_pi_mul_succ {t : ℝ} (ht : 0 < t) :
    HasSum (fun m : ℕ => Real.exp (-(2 * π * (m + 1)) * t))
      (1 / (Real.exp (2 * π * t) - 1)) := by
  set q := Real.exp (-(2 * π * t)) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  have hterm : ∀ m : ℕ, Real.exp (-(2 * π * (m + 1)) * t) = q * q ^ m := by
    intro m
    rw [hq, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  have hval : 1 / (Real.exp (2 * π * t) - 1) = q * (1 - q)⁻¹ := by
    have h1 : Real.exp (2 * π * t) * q = 1 := by rw [hq, ← Real.exp_add]; simp
    have h2 : Real.exp (2 * π * t) - 1 ≠ 0 :=
    (sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity))).ne'
    have h3 : 1 - q ≠ 0 := by linarith
    field_simp
    linear_combination -h1
  simp_rw [hterm, hval]
  exact (hasSum_geometric_of_lt_one hq0 hq1).mul_left q


/-- The cosine and sine Laplace transforms for a positive real damping parameter. -/
theorem integral_exp_neg_mul_cos_and_sin {x t : ℝ} (hx : 0 < x) :
    ∫ s in Ioi (0 : ℝ), Real.exp (-x * s) * Real.cos (t * s) = x / (x ^ 2 + t ^ 2) ∧
      ∫ s in Ioi (0 : ℝ), Real.exp (-x * s) * Real.sin (t * s) = t / (x ^ 2 + t ^ 2) := by
  set a : ℂ := -x + t * I with ha
  have hare : a.re < 0 := by simp [ha]; linarith
  have hint := integrableOn_exp_mul_complex_Ioi hare 0
  have h := integral_exp_mul_complex_Ioi hare 0
  simp only [ofReal_zero, mul_zero, Complex.exp_zero] at h
  have ha0 : a ≠ 0 := fun h0 => by rw [h0, zero_re] at hare; exact lt_irrefl _ hare
  have hd : ((x ^ 2 + t ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < x ^ 2 + t ^ 2 := by positivity
    exact_mod_cast this.ne'
  have hval : -1 / a = ((x / (x ^ 2 + t ^ 2) : ℝ) : ℂ) + ((t / (x ^ 2 + t ^ 2) : ℝ) : ℂ) * I := by
    have hd' : (x : ℂ) ^ 2 + (t : ℂ) ^ 2 ≠ 0 := by exact_mod_cast hd
    have e : ((x / (x ^ 2 + t ^ 2) : ℝ) : ℂ) + ((t / (x ^ 2 + t ^ 2) : ℝ) : ℂ) * I =
        ((x : ℂ) + t * I) / ((x : ℂ) ^ 2 + (t : ℂ) ^ 2) := by
      push_cast; field_simp
    rw [e, div_eq_div_iff ha0 hd', ha]
    linear_combination (-(t : ℂ) ^ 2) * I_sq
  rw [hval] at h
  have hre : ∀ s : ℝ, RCLike.re (Complex.exp (a * s)) =
      Real.exp (-x * s) * Real.cos (t * s) := by
    intro s
    rw [RCLike.re_to_complex, Complex.exp_re]
    simp [ha]
  have him : ∀ s : ℝ, RCLike.im (Complex.exp (a * s)) =
      Real.exp (-x * s) * Real.sin (t * s) := by
    intro s
    rw [RCLike.im_to_complex, Complex.exp_im]
    simp [ha]
  constructor
  · have := integral_re hint
    simp_rw [hre] at this
    rw [this, h, RCLike.re_to_complex, add_re, ofReal_re, mul_I_re, ofReal_im, neg_zero, add_zero]
  · have := integral_im hint
    simp_rw [him] at this
    rw [this, h, RCLike.im_to_complex, add_im, ofReal_im, mul_I_im, ofReal_re, zero_add]


/-- The sine transform of the Bose–Einstein kernel, with its removable singularity
at the lower integration endpoint. -/
theorem integral_sin_div_exp_two_pi_sub_one {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun x : ℝ => Real.sin (s * x) / (Real.exp (2 * π * x) - 1)) (Ioi 0) ∧
      2 * (∫ x in Ioi (0 : ℝ), Real.sin (s * x) / (Real.exp (2 * π * x) - 1)) =
        1 / (Real.exp s - 1) - 1 / s + 1 / 2 := by
  let a : ℕ → ℝ := fun m => 2 * π * (m + 1)
  let F : ℕ → ℝ → ℝ := fun m x => Real.sin (s * x) * Real.exp (-(a m * x))
  have ha (m : ℕ) : 0 < a m := by dsimp [a]; positivity
  have hmajor (m : ℕ) : IntegrableOn (fun x : ℝ => s * (x * Real.exp (-(a m * x)))) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul (r := 1) (by norm_num) (ha m)
    refine IntegrableOn.congr_fun (h.const_mul s) (fun x _ => ?_) measurableSet_Ioi
    simp only [Real.rpow_one]
  have hbound (m : ℕ) {x : ℝ} (hx : 0 < x) :
      ‖F m x‖ ≤ s * (x * Real.exp (-(a m * x))) := by
    dsimp [F]
    simp only [abs_mul, Real.abs_exp]
    have h := Real.abs_sin_le_abs (x := s * x)
    rw [abs_of_pos (mul_pos hs hx)] at h
    nlinarith [Real.exp_pos (-(a m * x))]
  have hint (m : ℕ) : IntegrableOn (F m) (Ioi 0) :=
    (hmajor m).mono' (by fun_prop : Continuous (F m)).aestronglyMeasurable
      (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx using hbound m hx)
  have hnorm (m : ℕ) : ∫ x in Ioi (0 : ℝ), ‖F m x‖ ≤ s / a m ^ 2 := by
    have hI := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (by norm_num) (ha m)
    norm_num [Real.rpow_natCast] at hI
    have hle := integral_mono_ae (hint m).norm (hmajor m)
      (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx using hbound m hx)
    rw [integral_const_mul, hI] at hle
    convert hle using 1 <;> ring
  have hsumMajor : Summable (fun m : ℕ => s / a m ^ 2) := by
    have h := (summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
    refine (h.mul_left (s / (2 * π) ^ 2)).congr fun m => ?_
    dsimp [a]
    push_cast
    field_simp
  have hsum : Summable (fun m => ∫ x in Ioi (0 : ℝ), ‖F m x‖) :=
    Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) hnorm hsumMajor
  have hval (m : ℕ) : ∫ x in Ioi (0 : ℝ), F m x = s / (s ^ 2 + (a m) ^ 2) := by
    simpa [F, mul_comm, add_comm] using (integral_exp_neg_mul_cos_and_sin (t := s) (ha m)).2
  have heq : (∫ x in Ioi (0 : ℝ), Real.sin (s * x) /
      (Real.exp (2 * π * x) - 1)) = ∑' m : ℕ, s / (s ^ 2 + (a m) ^ 2) := by
    have h := integral_tsum_of_summable_integral_norm hint hsum
    simp_rw [hval] at h
    rw [h]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    dsimp [F, a]
    rw [tsum_mul_left]
    have hgeom : (∑' m : ℕ, Real.exp (-(2 * π * (m + 1) * x))) =
        1 / (Real.exp (2 * π * x) - 1) := by
      convert (hasSum_exp_neg_two_pi_mul_succ hx).tsum_eq using 1
      congr 1
      funext m
      congr 1
      ring
    rw [hgeom]
    ring
  have hB := hasSum_two_mul_div_sq_add_two_pi_mul_sq hs
  have htwo : 2 * (∫ x in Ioi (0 : ℝ), Real.sin (s * x) /
      (Real.exp (2 * π * x) - 1)) = 1 / (Real.exp s - 1) - 1 / s + 1 / 2 := by
    rw [heq, ← tsum_mul_left, ← hB.tsum_eq]
    congr 1
    funext m
    dsimp [a]
    ring
  have hpos : 0 < ∑' m : ℕ, 2 * s / (s ^ 2 + (2 * π * (m + 1)) ^ 2) := by
    apply hB.summable.tsum_pos (fun m => by positivity) 0
    positivity
  have hne : (∫ x in Ioi (0 : ℝ), Real.sin (s * x) /
      (Real.exp (2 * π * x) - 1)) ≠ 0 := by
    intro hzero
    rw [← hB.tsum_eq, hzero, mul_zero] at htwo
    linarith
  exact ⟨Integrable.of_integral_ne_zero hne, htwo⟩

/-- A useful exponential majorant for the Bose–Einstein kernel. -/
theorem one_div_exp_sub_one_le_mul_exp_neg {u : ℝ} (hu : 0 < u) :
    1 / (Real.exp u - 1) ≤ (1 + 1 / u) * Real.exp (-u) := by
  have hE : 0 < Real.exp u - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hu)
  have huE : u ≤ Real.exp u - 1 := by linarith [Real.add_one_le_exp u]
  have hi : 1 / (Real.exp u - 1) ≤ 1 / u := one_div_le_one_div_of_le hu huE
  calc
    1 / (Real.exp u - 1) = (1 + 1 / (Real.exp u - 1)) * Real.exp (-u) := by
      rw [Real.exp_neg]
      field_simp
      ring
    _ ≤ (1 + 1 / u) * Real.exp (-u) := by gcongr

/-- Polynomial multiples of the regularized Bose–Einstein kernel are integrable on the
positive half-line. -/
theorem integrableOn_mul_one_add_pow_div_exp_two_pi_sub_one (n : ℕ) :
    IntegrableOn (fun x : ℝ => x * (1 + x) ^ n / (Real.exp (2 * π * x) - 1)) (Ioi 0) := by
  have hpow (k : ℕ) : IntegrableOn (fun x : ℝ => x ^ k * Real.exp (-(2 * π * x))) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul (r := (k : ℝ))
      (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]) (by positivity : 0 < 2 * π)
    refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
    simp only [Real.rpow_natCast]
  have hsum : IntegrableOn (fun x : ℝ => ∑ k ∈ Finset.range (n + 1),
      (n.choose k : ℝ) * (x ^ (k + 1) * Real.exp (-(2 * π * x)) +
        (1 / (2 * π)) * (x ^ k * Real.exp (-(2 * π * x))))) (Ioi 0) := by
    apply integrable_finsetSum
    intro k _
    exact ((hpow (k + 1)).add ((hpow k).const_mul (1 / (2 * π)))).const_mul (n.choose k : ℝ)
  have hpoly : IntegrableOn (fun x : ℝ =>
      (x + 1 / (2 * π)) * (1 + x) ^ n * Real.exp (-(2 * π * x))) (Ioi 0) := by
    refine hsum.congr_fun (fun x _ => ?_) measurableSet_Ioi
    rw [show 1 + x = x + 1 by ring, add_pow]
    simp only [one_pow, mul_one]
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    rw [pow_succ]
    ring
  refine hpoly.mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
    intro x hx
    have hx' : 0 < x := hx
    exact (sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity : 0 < 2 * π * x))).ne'
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx' : 0 < x := hx
    have hE : 0 < Real.exp (2 * π * x) - 1 :=
      sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity))
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ x * (1 + x) ^ n / (Real.exp (2 * π * x) - 1))]
    have h := mul_le_mul_of_nonneg_left
      (one_div_exp_sub_one_le_mul_exp_neg (by positivity : 0 < 2 * π * x))
      (by positivity : 0 ≤ x * (1 + x) ^ n)
    convert h using 1 <;> field_simp <;> ring

end Real
