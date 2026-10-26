/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Fourier series of entire periodic functions

Let `F : ℂ → ℂ` be entire and `2π`-periodic. Shifting the line of integration (Cauchy's theorem
for rectangles, the vertical sides cancel by periodicity) shows that the Fourier integrals
`c_k = ∫₀^{2π} F(x) e^{-ikx} dx` decay faster than any exponential, and applying Mathlib's
`has_pointwise_sum_fourier_series_of_summable` on every horizontal line gives the expansion
`F(z) = ∑_{k ∈ ℤ} (2π)⁻¹ c_k e^{ikz}` for **every complex** `z`.

## Main results

* `Complex.p1a2_integral_add_mul_I`: `∫₀^{2π} F(x + iy) dx = ∫₀^{2π} F(x) dx`.
* `Complex.p1a2_fourierInt_decay`: `|c_k| ≤ C e^{-R|k|}` for every `R`.
* `Complex.p1a2_hasSum_fourier`: the exponential Fourier series on all of `ℂ`.
* `Complex.p1a2_hasSum_cos`, `Complex.p1a2_hasSum_sin`: the cosine (sine) series of an even
  (odd) entire `2π`-periodic function, with coefficients `π⁻¹ ∫₀^{2π} F(x) cos mx dx` (halved
  for `m = 0`), resp. `π⁻¹ ∫₀^{2π} F(x) sin mx dx`.
* `Complex.p1a2_hasSum_cos_sq`, `Complex.p1a2_hasSum_sin_sq`: Parseval's identity in the form
  `∑ a_m ∫ F cos mx = ∫ F²` (squares, not absolute squares).
* `Complex.p1a2_hasSum_deriv_sin`: `F'(0) = ∑ m b_m` for odd `F`.
* `Complex.p1a2_integral_antiperiodic`, `Complex.p1a2_integral_odd_periodic`,
  `Complex.p1a2_integral_deriv_mul_cos`: elementary period integrals.

These are used for the Fourier series of the Mathieu functions (DLMF §28.4).
-/

@[expose] public section

open Complex Set Filter MeasureTheory
open scoped Topology Real

namespace Complex

variable {F : ℂ → ℂ}

/-- Contour shift for an entire `2π`-periodic function. -/
theorem p1a2_integral_add_mul_I (hF : Differentiable ℂ F) (hper : ∀ z, F (z + 2 * π) = F z)
    (y : ℝ) : ∫ x in (0 : ℝ)..2 * π, F (x + y * I) = ∫ x in (0 : ℝ)..2 * π, F x := by
  have h := integral_boundary_rect_eq_zero_of_differentiableOn F 0 (2 * π + y * I)
    hF.differentiableOn
  have e1 : (2 * π + y * I : ℂ).re = 2 * π := by simp
  have e2 : (2 * π + y * I : ℂ).im = y := by simp
  rw [e1, e2] at h
  simp only [zero_re, zero_im, ofReal_zero, zero_mul, add_zero, zero_add] at h
  have e3 : ∀ t : ℝ, F (((2 * π : ℝ) : ℂ) + t * I) = F (t * I) := fun t => by
    rw [show ((2 * π : ℝ) : ℂ) + t * I = t * I + 2 * π by push_cast; ring, hper]
  simp only [e3] at h
  linear_combination -h

/-- `exp(-ikz)` is `2π`-periodic for integer `k`. -/
theorem p1a2_exp_int_periodic (k : ℤ) (z : ℂ) :
    Complex.exp (-(k * (z + 2 * π) * I)) = Complex.exp (-(k * z * I)) := by
  rw [show -((k : ℂ) * (z + 2 * π) * I) = -(k * z * I) + -(k * (2 * π * I)) by ring,
    Complex.exp_add,
    show -((k : ℂ) * (2 * π * I)) = ((-k : ℤ) : ℂ) * (2 * π * I) by push_cast; ring,
    Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Shift of the Fourier integral of an entire `2π`-periodic function. -/
theorem p1a2_fourierInt_shift (hF : Differentiable ℂ F) (hper : ∀ z, F (z + 2 * π) = F z)
    (k : ℤ) (y : ℝ) :
    ∫ x in (0 : ℝ)..2 * π, F x * Complex.exp (-(k * x * I)) =
      Real.exp (k * y) * ∫ x in (0 : ℝ)..2 * π, F (x + y * I) * Complex.exp (-(k * x * I)) := by
  have h := p1a2_integral_add_mul_I (F := fun z => F z * Complex.exp (-(k * z * I)))
    (hF.mul (by fun_prop)) (fun z => by simp only [hper, p1a2_exp_int_periodic]) y
  rw [← h, ← intervalIntegral.integral_const_mul]
  congr 1; funext x
  rw [show -((k : ℂ) * (x + y * I) * I) = -(k * x * I) + k * y by
    ring_nf; rw [Complex.I_sq]; ring, Complex.exp_add]
  push_cast; ring

/-- Bound of the Fourier integral along a horizontal line. -/
theorem p1a2_exists_bound_line (hF : Differentiable ℂ F) (y : ℝ) :
    ∃ M, 0 ≤ M ∧ ∀ k : ℤ,
      ‖∫ x in (0 : ℝ)..2 * π, F (x + y * I) * Complex.exp (-(k * x * I))‖ ≤ M := by
  have hc : Continuous fun x : ℝ => F (x + y * I) := by
    have := hF.continuous; fun_prop
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 2 * π)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max B 0 * |2 * π - 0|, by positivity, fun k => ?_⟩
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro x hx
  rw [uIoc_of_le (by positivity)] at hx
  rw [norm_mul, show -((k : ℂ) * x * I) = ((-(k * x) : ℝ) : ℂ) * I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I, mul_one]
  exact (hB x (Ioc_subset_Icc_self hx)).trans (le_max_left _ _)

/-- Exponential decay of the Fourier coefficients of an entire `2π`-periodic function. -/
theorem p1a2_fourierInt_decay (hF : Differentiable ℂ F) (hper : ∀ z, F (z + 2 * π) = F z)
    (R : ℝ) : ∃ C, 0 ≤ C ∧ ∀ k : ℤ,
      ‖∫ x in (0 : ℝ)..2 * π, F x * Complex.exp (-(k * x * I))‖ ≤ C * Real.exp (-(R * |k|)) := by
  obtain ⟨M₁, hM₁, h₁⟩ := p1a2_exists_bound_line hF (-R)
  obtain ⟨M₂, hM₂, h₂⟩ := p1a2_exists_bound_line hF R
  refine ⟨M₁ + M₂, by positivity, fun k => ?_⟩
  rcases le_or_gt 0 k with hk | hk
  · rw [p1a2_fourierInt_shift hF hper k (-R), norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Real.abs_exp, Int.cast_abs, abs_of_nonneg (by exact_mod_cast hk : (0 : ℝ) ≤ k),
      mul_comm (Real.exp _), show (k : ℝ) * -R = -(R * k) by ring]
    exact mul_le_mul_of_nonneg_right ((h₁ k).trans (by linarith)) (Real.exp_pos _).le
  · rw [p1a2_fourierInt_shift hF hper k R, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Real.abs_exp, Int.cast_abs, abs_of_neg (by exact_mod_cast hk : (k : ℝ) < 0),
      mul_comm (Real.exp _), show (k : ℝ) * R = -(R * -k) by ring]
    exact mul_le_mul_of_nonneg_right ((h₂ k).trans (by linarith)) (Real.exp_pos _).le

/-- `∑_{k ∈ ℤ} exp(-|k|)` converges. -/
theorem p1a2_summable_exp_neg_abs : Summable fun k : ℤ => Real.exp (-|(k : ℝ)|) := by
  apply Summable.of_nat_of_neg
  · simpa using Real.summable_exp_neg_nat
  · simpa using Real.summable_exp_neg_nat

/-- **Fourier series of an entire `2π`-periodic function**: for every `z ∈ ℂ`,
`F(z) = ∑_{k ∈ ℤ} c_k e^{ikz}` with `c_k = (2π)⁻¹ ∫₀^{2π} F(x) e^{-ikx} dx`. -/
theorem p1a2_hasSum_fourier (hF : Differentiable ℂ F) (hper : ∀ z, F (z + 2 * π) = F z)
    (z : ℂ) :
    HasSum (fun k : ℤ => (1 / (2 * π) : ℂ) *
      (∫ x in (0 : ℝ)..2 * π, F x * Complex.exp (-(k * x * I))) * Complex.exp (k * z * I))
      (F z) := by
  set y := z.im
  set φ : ℝ → ℂ := fun x => F (x + y * I) with hφ
  have hφper : Function.Periodic φ (2 * π) := fun x => by
    simp only [φ]; push_cast
    rw [show (x : ℂ) + 2 * π + y * I = x + y * I + 2 * π by ring, hper]
  have hφc : Continuous φ := by have := hF.continuous; fun_prop
  have : Fact (0 < 2 * π) := ⟨by positivity⟩
  let Φ : C(AddCircle (2 * π), ℂ) := ⟨hφper.lift, continuous_coinduced_dom.mpr hφc⟩
  have hΦ : ∀ x : ℝ, Φ x = φ x := fun x => rfl
  have hcoef : ∀ k : ℤ, fourierCoeff Φ k = (1 / (2 * π) : ℂ) * Real.exp (-(k * y)) *
      ∫ x in (0 : ℝ)..2 * π, F x * Complex.exp (-(k * x * I)) := by
    intro k
    rw [fourierCoeff_eq_intervalIntegral Φ k 0, zero_add, p1a2_fourierInt_shift hF hper k y]
    have e : ∀ x : ℝ, fourier (-k) (x : AddCircle (2 * π)) • Φ x =
        F (x + y * I) * Complex.exp (-(k * x * I)) := by
      intro x
      rw [fourier_coe_apply, hΦ, smul_eq_mul, mul_comm]
      congr 2
      push_cast
      field_simp
    simp_rw [e]
    rw [Complex.real_smul]
    push_cast
    have hexp : Complex.exp (-((k : ℂ) * (y : ℂ))) * Complex.exp ((k : ℂ) * (y : ℂ)) = 1 := by
      rw [← Complex.exp_add]; simp
    linear_combination (-(1 / (2 * (π : ℂ))) *
      ∫ x in (0 : ℝ)..2 * π, F (x + y * I) * Complex.exp (-(k * x * I))) * hexp
  obtain ⟨C, hC0, hC⟩ := p1a2_fourierInt_decay hF hper (|y| + 1)
  have hsum : Summable (fourierCoeff Φ) := by
    refine Summable.of_norm_bounded (g := fun k : ℤ => (1 / (2 * π)) * C *
      Real.exp (-|(k : ℝ)|)) ((p1a2_summable_exp_neg_abs).mul_left _) (fun k => ?_)
    rw [hcoef, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.abs_exp]
    have h1 : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * π) := by
      rw [norm_div, norm_one, Complex.norm_mul, Complex.norm_ofNat, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [h1, mul_assoc, mul_assoc]
    apply mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h2 := hC k
    rw [Int.cast_abs] at h2
    have h3 : Real.exp (-(k * y)) * Real.exp (-((|y| + 1) * |(k : ℝ)|)) ≤
        Real.exp (-|(k : ℝ)|) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have := neg_abs_le ((k : ℝ) * y)
      rw [abs_mul] at this
      nlinarith [abs_nonneg (k : ℝ), abs_nonneg y]
    calc Real.exp (-(k * y)) * ‖∫ x in (0 : ℝ)..2 * π, F x * Complex.exp (-(k * x * I))‖
        ≤ Real.exp (-(k * y)) * (C * Real.exp (-((|y| + 1) * |(k : ℝ)|))) := by gcongr
      _ = C * (Real.exp (-(k * y)) * Real.exp (-((|y| + 1) * |(k : ℝ)|))) := by ring
      _ ≤ C * Real.exp (-|(k : ℝ)|) := by gcongr
  have h := has_pointwise_sum_fourier_series_of_summable hsum (z.re : AddCircle (2 * π))
  rw [hΦ, show φ z.re = F z by simp only [φ, y]; exact congrArg F (Complex.re_add_im z)] at h
  convert h using 1
  funext k
  have hf : fourier k (z.re : AddCircle (2 * π)) = Complex.exp (k * z.re * I) := by
    rw [fourier_coe_apply]; congr 1; push_cast; field_simp
  rw [hcoef, hf, smul_eq_mul]
  have : Complex.exp (k * z * I) = Real.exp (-(k * y)) * Complex.exp (k * z.re * I) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    conv_lhs => rw [← Complex.re_add_im z]
    push_cast
    ring_nf; rw [Complex.I_sq]; ring
  rw [this]; ring

/-- The integral over a period of an odd `2π`-periodic function vanishes. -/
theorem p1a2_integral_odd_periodic {g : ℝ → ℂ} (hg : Function.Periodic g (2 * π))
    (hodd : ∀ x, g (-x) = -g x) : ∫ x in (0 : ℝ)..2 * π, g x = 0 := by
  have h1 := hg.intervalIntegral_add_eq 0 (-π)
  rw [zero_add, show -π + 2 * π = π by ring] at h1
  rw [h1]
  have h2 : ∫ x in (-π)..π, g (-x) = ∫ x in (-π)..π, g x := by
    rw [intervalIntegral.integral_comp_neg, neg_neg]
  simp_rw [hodd, intervalIntegral.integral_neg] at h2
  linear_combination -h2 / 2

/-- `e^{-ikx} = cos kx - i sin kx` inside the Fourier integral. -/
theorem p1a2_fourierInt_eq (hF : Continuous F) (k : ℤ) :
    ∫ x in (0 : ℝ)..2 * π, F x * Complex.exp (-(k * x * I)) =
      (∫ x in (0 : ℝ)..2 * π, F x * Complex.cos (k * x)) -
        I * ∫ x in (0 : ℝ)..2 * π, F x * Complex.sin (k * x) := by
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub]
  · congr 1; funext x
    rw [show -((k : ℂ) * x * I) = (-(k * x)) * I by ring, Complex.exp_mul_I, Complex.cos_neg,
      Complex.sin_neg]
    ring
  · exact (by fun_prop : Continuous fun x : ℝ => F x * Complex.cos (k * x)).intervalIntegrable _ _
  · exact (by fun_prop : Continuous fun x : ℝ =>
      I * (F x * Complex.sin (k * x))).intervalIntegrable _ _

/-- Periodicity of `F(x) sin kx`. -/
theorem p1a2_periodic_mul_sin (hper : ∀ z, F (z + 2 * π) = F z) (k : ℤ) :
    Function.Periodic (fun x : ℝ => F x * Complex.sin (k * x)) (2 * π) := by
  intro x
  simp only
  push_cast
  rw [hper, show (k : ℂ) * (x + 2 * π) = k * x + k * (2 * π) by ring,
    Complex.sin_add_int_mul_two_pi]

/-- Periodicity of `F(x) cos kx`. -/
theorem p1a2_periodic_mul_cos (hper : ∀ z, F (z + 2 * π) = F z) (k : ℤ) :
    Function.Periodic (fun x : ℝ => F x * Complex.cos (k * x)) (2 * π) := by
  intro x
  simp only
  push_cast
  rw [hper, show (k : ℂ) * (x + 2 * π) = k * x + k * (2 * π) by ring,
    Complex.cos_add_int_mul_two_pi]

/-- **Cosine series of an even entire `2π`-periodic function**:
`F(z) = ∑_{m ≥ 0} a_m cos mz`, `a_0 = (2π)⁻¹ ∫₀^{2π} F`, `a_m = π⁻¹ ∫₀^{2π} F(x) cos mx dx`. -/
theorem p1a2_hasSum_cos (hF : Differentiable ℂ F) (hper : ∀ z, F (z + 2 * π) = F z)
    (hev : ∀ z, F (-z) = F z) (z : ℂ) :
    HasSum (fun m : ℕ => (if m = 0 then 1 / (2 * π) else 1 / π : ℂ) *
      (∫ x in (0 : ℝ)..2 * π, F x * Complex.cos (m * x)) * Complex.cos (m * z)) (F z) := by
  have hc := hF.continuous
  have hs0 : ∀ k : ℤ, ∫ x in (0 : ℝ)..2 * π, F x * Complex.sin (k * x) = 0 := by
    intro k
    apply p1a2_integral_odd_periodic (p1a2_periodic_mul_sin hper k)
    intro x
    push_cast
    rw [hev, show (k : ℂ) * -x = -(k * x) by ring, Complex.sin_neg]; ring
  have hcn : ∀ n : ℕ, ∫ x in (0 : ℝ)..2 * π, F x * Complex.cos (((-n : ℤ) : ℂ) * x) =
      ∫ x in (0 : ℝ)..2 * π, F x * Complex.cos (n * x) := by
    intro n; push_cast; simp_rw [neg_mul, Complex.cos_neg]
  have h := (p1a2_hasSum_fourier hF hper z).nat_add_neg
  simp only [p1a2_fourierInt_eq hc, hs0, mul_zero, sub_zero, hcn] at h
  set c0 := (1 / (2 * π) : ℂ) * (∫ x in (0 : ℝ)..2 * π, F x * Complex.cos (((0 : ℤ) : ℂ) * x)) *
    Complex.exp (((0 : ℤ) : ℂ) * z * I)
  have h2 := h.sub (hasSum_ite_eq 0 c0)
  rw [add_sub_cancel_right] at h2
  convert h2 using 1
  funext n
  have e1 : Complex.exp (n * z * I) = Complex.cos (n * z) + Complex.sin (n * z) * I := by
    rw [Complex.exp_mul_I]
  have e2 : Complex.exp (((-n : ℤ) : ℂ) * z * I) =
      Complex.cos (n * z) - Complex.sin (n * z) * I := by
    push_cast
    rw [show -(n : ℂ) * z * I = (-(n * z)) * I by ring, Complex.exp_mul_I, Complex.cos_neg,
      Complex.sin_neg]; ring
  rw [show ((n : ℤ) : ℂ) = (n : ℂ) by push_cast; rfl, e1, e2]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [c0]; simp
  · simp only [hn.ne', ↓reduceIte]
    field_simp
    ring

/-- **Sine series of an odd entire `2π`-periodic function**:
`F(z) = ∑_{m ≥ 0} b_m sin mz`, `b_m = π⁻¹ ∫₀^{2π} F(x) sin mx dx`. -/
theorem p1a2_hasSum_sin (hF : Differentiable ℂ F) (hper : ∀ z, F (z + 2 * π) = F z)
    (hodd : ∀ z, F (-z) = -F z) (z : ℂ) :
    HasSum (fun m : ℕ => (1 / π : ℂ) *
      (∫ x in (0 : ℝ)..2 * π, F x * Complex.sin (m * x)) * Complex.sin (m * z)) (F z) := by
  have hc := hF.continuous
  have hc0 : ∀ k : ℤ, ∫ x in (0 : ℝ)..2 * π, F x * Complex.cos (k * x) = 0 := by
    intro k
    apply p1a2_integral_odd_periodic (p1a2_periodic_mul_cos hper k)
    intro x
    push_cast
    rw [hodd, show (k : ℂ) * -x = -(k * x) by ring, Complex.cos_neg]; ring
  have hsn : ∀ n : ℕ, ∫ x in (0 : ℝ)..2 * π, F x * Complex.sin (((-n : ℤ) : ℂ) * x) =
      -∫ x in (0 : ℝ)..2 * π, F x * Complex.sin (n * x) := by
    intro n; push_cast; simp_rw [neg_mul, Complex.sin_neg, mul_neg, intervalIntegral.integral_neg]
  have h := (p1a2_hasSum_fourier hF hper z).nat_add_neg
  simp only [p1a2_fourierInt_eq hc, hc0, zero_sub, hsn] at h
  have h0 : ∫ x in (0 : ℝ)..2 * π, F x * Complex.sin (((0 : ℤ) : ℂ) * x) = 0 := by simp
  rw [h0, mul_zero, neg_zero, mul_zero, zero_mul, add_zero] at h
  convert h using 1
  funext n
  have e1 : Complex.exp (n * z * I) = Complex.cos (n * z) + Complex.sin (n * z) * I := by
    rw [Complex.exp_mul_I]
  have e2 : Complex.exp (((-n : ℤ) : ℂ) * z * I) =
      Complex.cos (n * z) - Complex.sin (n * z) * I := by
    push_cast
    rw [show -(n : ℂ) * z * I = (-(n * z)) * I by ring, Complex.exp_mul_I, Complex.cos_neg,
      Complex.sin_neg]; ring
  rw [show ((n : ℤ) : ℂ) = (n : ℂ) by push_cast; rfl, e1, e2]
  field_simp
  ring_nf
  rw [Complex.I_sq]; ring

/-- The integral over `[0, 2π]` of a continuous `π`-antiperiodic function vanishes. -/
theorem p1a2_integral_antiperiodic {g : ℝ → ℂ} (hg : Continuous g) (hanti : ∀ x, g (x + π) = -g x) :
    ∫ x in (0 : ℝ)..2 * π, g x = 0 := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := π) (hg.intervalIntegrable _ _)
    (hg.intervalIntegrable _ _)]
  have h := intervalIntegral.integral_comp_add_right (a := 0) (b := π) g π
  rw [zero_add, show π + π = 2 * π by ring] at h
  rw [← h]
  simp_rw [hanti, intervalIntegral.integral_neg]
  ring

/-- Integration by parts over a period: `∫₀^{2π} F'(x) cos kx dx = k ∫₀^{2π} F(x) sin kx dx`. -/
theorem p1a2_integral_deriv_mul_cos (hF : Differentiable ℂ F) (hper : ∀ z, F (z + 2 * π) = F z)
    (k : ℤ) :
    ∫ x in (0 : ℝ)..2 * π, deriv F x * Complex.cos (k * x) =
      k * ∫ x in (0 : ℝ)..2 * π, F x * Complex.sin (k * x) := by
  have hd : ∀ x : ℝ, HasDerivAt (fun x : ℝ => F x * Complex.cos (k * x))
      (deriv F x * Complex.cos (k * x) - k * (F x * Complex.sin (k * x))) x := by
    intro x
    have h0 : HasDerivAt (fun x : ℝ => F x) (deriv F x) x := (hF x).hasDerivAt.comp_ofReal
    have hl : HasDerivAt (fun x : ℝ => (k : ℂ) * (x : ℂ)) k x := by
      simpa using ((hasDerivAt_id (x : ℂ)).const_mul (k : ℂ)).comp_ofReal
    have hc : HasDerivAt (fun x : ℝ => Complex.cos (k * x)) (-Complex.sin (k * x) * k) x :=
      (Complex.hasDerivAt_cos _).comp x hl
    convert h0.mul hc using 1; ring
  have hcd : Continuous (deriv F) := (hF.contDiff (n := 1) |>.continuous_deriv le_rfl)
  have hc := hF.continuous
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 2 * π)
    (fun x _ => hd x) ((by fun_prop : Continuous fun x : ℝ =>
      deriv F x * Complex.cos (k * x) - k * (F x * Complex.sin (k * x))).intervalIntegrable _ _)
  rw [intervalIntegral.integral_sub ((by fun_prop : Continuous fun x : ℝ =>
      deriv F x * Complex.cos (k * x)).intervalIntegrable _ _) ((by fun_prop : Continuous
      fun x : ℝ => k * (F x * Complex.sin (k * x))).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul] at hint
  have e : F ((2 * π : ℝ) : ℂ) * Complex.cos (k * ((2 * π : ℝ) : ℂ)) =
      F ((0 : ℝ) : ℂ) * Complex.cos (k * ((0 : ℝ) : ℂ)) := by
    push_cast
    rw [show (k : ℂ) * (2 * π) = 0 + k * (2 * π) by ring, Complex.cos_add_int_mul_two_pi,
      show (2 * π : ℂ) = 0 + 2 * π by ring, hper]
    simp
  rw [e, sub_self] at hint
  linear_combination hint

/-- Summability of the cosine coefficients of an even entire `2π`-periodic function. -/
theorem p1a2_summable_cos_coeff (hF : Differentiable ℂ F) (hper : ∀ z, F (z + 2 * π) = F z)
    (hev : ∀ z, F (-z) = F z) :
    Summable fun m : ℕ => ‖∫ x in (0 : ℝ)..2 * π, F x * Complex.cos (m * x)‖ := by
  have hc := hF.continuous
  obtain ⟨C, hC0, hC⟩ := p1a2_fourierInt_decay hF hper 1
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_)
    (Real.summable_exp_neg_nat.mul_left C)
  have hs0 : ∫ x in (0 : ℝ)..2 * π, F x * Complex.sin (((m : ℤ) : ℂ) * x) = 0 := by
    apply p1a2_integral_odd_periodic (p1a2_periodic_mul_sin hper m)
    intro x
    push_cast
    rw [hev, show (m : ℂ) * -x = -(m * x) by ring, Complex.sin_neg]; ring
  have h := hC m
  rw [p1a2_fourierInt_eq hc, hs0, mul_zero, sub_zero] at h
  push_cast at h
  simpa using h

/-- Summability of the sine coefficients of an odd entire `2π`-periodic function. -/
theorem p1a2_summable_sin_coeff (hF : Differentiable ℂ F) (hper : ∀ z, F (z + 2 * π) = F z)
    (hodd : ∀ z, F (-z) = -F z) :
    Summable fun m : ℕ => ‖∫ x in (0 : ℝ)..2 * π, F x * Complex.sin (m * x)‖ := by
  have hc := hF.continuous
  obtain ⟨C, hC0, hC⟩ := p1a2_fourierInt_decay hF hper 1
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_)
    (Real.summable_exp_neg_nat.mul_left C)
  have hc0 : ∫ x in (0 : ℝ)..2 * π, F x * Complex.cos (((m : ℤ) : ℂ) * x) = 0 := by
    apply p1a2_integral_odd_periodic (p1a2_periodic_mul_cos hper m)
    intro x
    push_cast
    rw [hodd, show (m : ℂ) * -x = -(m * x) by ring, Complex.cos_neg]; ring
  have h := hC m
  rw [p1a2_fourierInt_eq hc, hc0, zero_sub, norm_neg, norm_mul, Complex.norm_I, one_mul] at h
  push_cast at h
  simpa using h

/-- **Parseval** for the cosine series of an even entire `2π`-periodic function:
`2a_0² + ∑_{m ≥ 1} a_m² = π⁻¹ ∫₀^{2π} F²` (squares, not absolute squares). -/
theorem p1a2_hasSum_cos_sq (hF : Differentiable ℂ F) (hper : ∀ z, F (z + 2 * π) = F z)
    (hev : ∀ z, F (-z) = F z) :
    HasSum (fun m : ℕ => (if m = 0 then 2 else 1) * ((if m = 0 then 1 / (2 * π) else 1 / π : ℂ) *
      (∫ x in (0 : ℝ)..2 * π, F x * Complex.cos (m * x))) ^ 2)
      ((1 / π : ℂ) * ∫ x in (0 : ℝ)..2 * π, F x ^ 2) := by
  have hc := hF.continuous
  set a : ℕ → ℂ := fun m => (if m = 0 then 1 / (2 * π) else 1 / π : ℂ) *
      (∫ x in (0 : ℝ)..2 * π, F x * Complex.cos (m * x)) with ha
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 2 * π)).exists_bound_of_continuousOn
    (hc.comp continuous_ofReal).continuousOn
  have hsa : Summable fun m => ‖a m‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_)
      ((p1a2_summable_cos_coeff hF hper hev).mul_left (1 / π))
    simp only [ha, norm_mul]
    gcongr
    split_ifs
    · rw [norm_div, norm_one, Complex.norm_mul, Complex.norm_ofNat, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      gcongr; linarith [Real.pi_pos]
    · rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have h := intervalIntegral.hasSum_integral_of_dominated_convergence
    (F := fun m (x : ℝ) => a m * (F x * Complex.cos (m * x))) (f := fun x : ℝ => F x ^ 2)
    (μ := MeasureTheory.volume) (a := 0) (b := 2 * π)
    (fun m _ => ‖a m‖ * max M 0)
    (fun m => (by fun_prop : Continuous fun x : ℝ =>
      a m * (F x * Complex.cos (m * x))).aestronglyMeasurable)
    (fun m => Eventually.of_forall fun x hx => by
      rw [uIoc_of_le (by positivity)] at hx
      rw [norm_mul, norm_mul]
      gcongr
      have h1 : ‖Complex.cos (m * x)‖ ≤ 1 := by
        rw [show (m : ℂ) * x = ((m * x : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cos,
          Complex.norm_real, Real.norm_eq_abs]
        exact Real.abs_cos_le_one _
      rw [norm_mul]
      calc ‖F x‖ * ‖Complex.cos (m * x)‖ ≤ max M 0 * 1 := by
            gcongr
            exact (hM x (Ioc_subset_Icc_self hx)).trans (le_max_left _ _)
        _ = max M 0 := mul_one _)
    (Eventually.of_forall fun x _ => hsa.mul_right _)
    intervalIntegrable_const
    (Eventually.of_forall fun x _ => by
      have := (p1a2_hasSum_cos hF hper hev x).mul_left (F x)
      simp only [ha]
      convert this using 1
      · funext m; ring
      · ring)
  rw [← intervalIntegral.integral_const_mul] at *
  convert h.mul_left (1 / π : ℂ) using 1
  · funext m
    rw [intervalIntegral.integral_const_mul]
    simp only [ha]
    split_ifs <;> field_simp
  · rw [intervalIntegral.integral_const_mul]

/-- **Parseval** for the sine series of an odd entire `2π`-periodic function:
`∑_{m} b_m² = π⁻¹ ∫₀^{2π} F²` (squares, not absolute squares). -/
theorem p1a2_hasSum_sin_sq (hF : Differentiable ℂ F) (hper : ∀ z, F (z + 2 * π) = F z)
    (hodd : ∀ z, F (-z) = -F z) :
    HasSum (fun m : ℕ => ((1 / π : ℂ) * (∫ x in (0 : ℝ)..2 * π, F x * Complex.sin (m * x))) ^ 2)
      ((1 / π : ℂ) * ∫ x in (0 : ℝ)..2 * π, F x ^ 2) := by
  have hc := hF.continuous
  set a : ℕ → ℂ := fun m => (1 / π : ℂ) *
      (∫ x in (0 : ℝ)..2 * π, F x * Complex.sin (m * x)) with ha
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 2 * π)).exists_bound_of_continuousOn
    (hc.comp continuous_ofReal).continuousOn
  have hsa : Summable fun m => ‖a m‖ := by
    simp only [ha, norm_mul]
    exact (p1a2_summable_sin_coeff hF hper hodd).mul_left _
  have h := intervalIntegral.hasSum_integral_of_dominated_convergence
    (F := fun m (x : ℝ) => a m * (F x * Complex.sin (m * x))) (f := fun x : ℝ => F x ^ 2)
    (μ := MeasureTheory.volume) (a := 0) (b := 2 * π)
    (fun m _ => ‖a m‖ * max M 0)
    (fun m => (by fun_prop : Continuous fun x : ℝ =>
      a m * (F x * Complex.sin (m * x))).aestronglyMeasurable)
    (fun m => Eventually.of_forall fun x hx => by
      rw [uIoc_of_le (by positivity)] at hx
      rw [norm_mul]
      gcongr
      have h1 : ‖Complex.sin (m * x)‖ ≤ 1 := by
        rw [show (m : ℂ) * x = ((m * x : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_sin,
          Complex.norm_real, Real.norm_eq_abs]
        exact Real.abs_sin_le_one _
      rw [norm_mul]
      calc ‖F x‖ * ‖Complex.sin (m * x)‖ ≤ max M 0 * 1 := by
            gcongr
            exact (hM x (Ioc_subset_Icc_self hx)).trans (le_max_left _ _)
        _ = max M 0 := mul_one _)
    (Eventually.of_forall fun x _ => hsa.mul_right _)
    intervalIntegrable_const
    (Eventually.of_forall fun x _ => by
      have := (p1a2_hasSum_sin hF hper hodd x).mul_left (F x)
      simp only [ha]
      convert this using 1
      · funext m; ring
      · ring)
  convert h.mul_left (1 / π : ℂ) using 1
  · funext m
    rw [intervalIntegral.integral_const_mul]
    simp only [ha]
    field_simp

/-- Termwise differentiation of the sine series at `0`: for an odd entire `2π`-periodic `F`,
`F'(0) = ∑_m m b_m`. -/
theorem p1a2_hasSum_deriv_sin (hF : Differentiable ℂ F) (hper : ∀ z, F (z + 2 * π) = F z)
    (hodd : ∀ z, F (-z) = -F z) :
    HasSum (fun m : ℕ => (m : ℂ) * ((1 / π : ℂ) *
      (∫ x in (0 : ℝ)..2 * π, F x * Complex.sin (m * x)))) (deriv F 0) := by
  have hd : Differentiable ℂ (deriv F) := fun z => (hF.analyticAt z).deriv.differentiableAt
  have hdper : ∀ z, deriv F (z + 2 * π) = deriv F z := by
    intro z
    have : (fun z => F (z + 2 * π)) = F := funext hper
    have h := deriv_comp_add_const (f := F) (a := (2 * π : ℂ)) (x := z)
    rw [this] at h
    exact h.symm
  have hdev : ∀ z, deriv F (-z) = deriv F z := by
    intro z
    have : (fun z => F (-z)) = fun z => -F z := funext hodd
    have h := deriv_comp_neg (f := F) (x := z)
    have hn : deriv (fun z => -F z) z = -deriv F z := by
      have e := (hF z).hasDerivAt.neg
      exact e.deriv
    rw [this, hn] at h
    linear_combination h
  have h := p1a2_hasSum_cos hd hdper hdev 0
  simp only [mul_zero, Complex.cos_zero, mul_one] at h
  convert h using 1
  funext m
  have e := p1a2_integral_deriv_mul_cos hF hper m
  push_cast at e
  rw [e]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · simp only [hm.ne', ↓reduceIte]
    ring

end Complex