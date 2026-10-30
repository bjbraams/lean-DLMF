/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Elliptic.Basic.Integrals
public import DLMF.Elliptic.Jacobi

/-!
# The elliptic integral of the third kind (Temme (12.17), DLMF §19.2)

For `n < 1` and `m < 1` the integrand `(1 - n sin²θ)⁻¹ (1 - m sin²θ)^{-1/2}` is continuous, so
`Π(φ, n, m) = ∫₀^φ (1 - n sin²θ)⁻¹ (1 - m sin²θ)^{-1/2} dθ` needs no principal value; the argument
order is DLMF's, with characteristic `n = α²` and parameter `m = k²`. It is odd and
quasi-periodic, `Π(φ+π, n, m) = Π(φ, n, m) + 2Π(n, m)`, and `Π(φ, 0, m) = F(φ, m)`. At `m = 0` it
is elementary: with `c = √(1-n)`,
`Π(φ, n, 0) = (φ - arctan((1-c) sin φ cos φ/(cos²φ + c sin²φ)))/c`, which is `arctan(c tan φ)/c` on
`(-π/2, π/2)` but is smooth on all of `ℝ`. In particular `Π(n, 0) = π/(2√(1-n))`.
-/

@[expose] public section

open Real Set Filter
open scoped Topology

noncomputable section

namespace DLMF.Elliptic

/-- For `n, m < 1` the integrand of the third kind is continuous. -/
theorem continuous_piIntegrand {n m : ℝ} (hn : n < 1) (hm : m < 1) :
    Continuous (piIntegrand n m) :=
  ((by fun_prop : Continuous fun θ : ℝ => 1 - n * sin θ ^ 2).inv₀
    fun θ => (one_sub_mul_sin_sq_pos hn θ).ne').mul (continuous_one_sub_mul_sin_sq_rpow hm _)

/-- The integrand is symmetric about `π/2`. -/
theorem piIntegrand_pi_sub (n m θ : ℝ) : piIntegrand n m (π - θ) = piIntegrand n m θ := by
  simp [piIntegrand, sin_pi_sub]

/-- The integrand is `π`-periodic. -/
theorem piIntegrand_add_pi (n m θ : ℝ) : piIntegrand n m (θ + π) = piIntegrand n m θ := by
  simp [piIntegrand, sin_add_pi]

/-- The integrand is even. -/
theorem piIntegrand_neg (n m θ : ℝ) : piIntegrand n m (-θ) = piIntegrand n m θ := by
  simp [piIntegrand, sin_neg]

/-- `Π(φ, 0, m) = F(φ, m)`. -/
theorem Real.incEllIntPim_char_zero (φ m : ℝ) : Real.incEllIntPim φ 0 m = Real.incEllIntFm φ m := by
  simp [Real.incEllIntPim, piIntegrand, Real.incEllIntFm]

/-- `∂Π/∂φ = (1 - n sin²φ)⁻¹ (1 - m sin²φ)^{-1/2}`. -/
theorem Real.hasDerivAt_incEllIntPim {n m : ℝ} (hn : n < 1) (hm : m < 1) (φ : ℝ) :
    HasDerivAt (fun φ => Real.incEllIntPim φ n m) (piIntegrand n m φ) φ :=
  intervalIntegral.integral_hasDerivAt_right
    ((continuous_piIntegrand hn hm).intervalIntegrable _ _)
    ((continuous_piIntegrand hn hm).stronglyMeasurableAtFilter _ _)
    (continuous_piIntegrand hn hm).continuousAt

/-- `Π(-φ, n, m) = -Π(φ, n, m)`. -/
theorem Real.incEllIntPim_neg (φ n m : ℝ) :
    Real.incEllIntPim (-φ) n m = -Real.incEllIntPim φ n m := by
  have h : ∫ θ in (0 : ℝ)..(-φ), piIntegrand n m θ =
      ∫ θ in (0 : ℝ)..(-φ), piIntegrand n m (-θ) := by simp only [piIntegrand_neg]
  rw [Real.incEllIntPim, Real.incEllIntPim, h,
    intervalIntegral.integral_comp_neg (piIntegrand n m), neg_neg, neg_zero,
    intervalIntegral.integral_symm]

/-- `Π(φ + π, n, m) = Π(φ, n, m) + 2Π(n, m)` (DLMF §19.2(ii)). -/
theorem Real.incEllIntPim_add_pi {n m : ℝ} (hn : n < 1) (hm : m < 1) (φ : ℝ) :
    Real.incEllIntPim (φ + π) n m = Real.incEllIntPim φ n m + 2 * Real.compEllIntPim n m := by
  have hc := continuous_piIntegrand hn hm
  have hper : ∫ θ in (0 : ℝ)..π, piIntegrand n m θ =
      2 * ∫ θ in (0 : ℝ)..(π / 2), piIntegrand n m θ := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := π / 2)
      (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
    have h := intervalIntegral.integral_comp_sub_left (piIntegrand n m) (a := 0) (b := π / 2) π
    simp only [piIntegrand_pi_sub, sub_zero, show π - π / 2 = π / 2 by ring] at h
    rw [← h]; ring
  unfold Real.incEllIntPim Real.compEllIntPim Real.incEllIntPim
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := π)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _), hper]
  have h := intervalIntegral.integral_comp_add_right (piIntegrand n m) (a := 0) (b := φ) π
  simp only [piIntegrand_add_pi, zero_add] at h
  rw [← h, add_comm]

/-- `cos²φ + c sin²φ > 0` for `c > 0`. -/
theorem cos_sq_add_mul_sin_sq_pos {c : ℝ} (hc : 0 < c) (φ : ℝ) : 0 < cos φ ^ 2 + c * sin φ ^ 2 := by
  rcases eq_or_ne (sin φ) 0 with h | h
  · have := sin_sq_add_cos_sq φ; rw [h] at this; nlinarith
  · have : 0 < sin φ ^ 2 := by positivity
    nlinarith [sq_nonneg (cos φ)]

/-- The primitive has derivative `(cos²φ + c² sin²φ)⁻¹` on all of `ℝ`. -/
theorem hasDerivAt_piZeroPrimitive {c : ℝ} (hc : 0 < c) (φ : ℝ) :
    HasDerivAt (piZeroPrimitive c) (1 / (cos φ ^ 2 + c ^ 2 * sin φ ^ 2)) φ := by
  have hD := cos_sq_add_mul_sin_sq_pos hc φ
  have hD2 := cos_sq_add_mul_sin_sq_pos (pow_pos hc 2) φ
  have hu : HasDerivAt (fun φ => (1 - c) * sin φ * cos φ / (cos φ ^ 2 + c * sin φ ^ 2))
      (((1 - c) * (cos φ * cos φ + sin φ * -sin φ) * (cos φ ^ 2 + c * sin φ ^ 2) -
        (1 - c) * sin φ * cos φ * (2 * cos φ * -sin φ + c * (2 * sin φ * cos φ))) /
          (cos φ ^ 2 + c * sin φ ^ 2) ^ 2) φ := by
    have h1 := (((hasDerivAt_sin φ).const_mul (1 - c)).mul (hasDerivAt_cos φ))
    have h2 := ((hasDerivAt_cos φ).pow 2).add (((hasDerivAt_sin φ).pow 2).const_mul c)
    convert h1.div h2 hD.ne' using 1
    simp; ring
  have h := ((hasDerivAt_id φ).sub hu.arctan).div_const c
  refine h.congr_deriv ?_
  have hsc := sin_sq_add_cos_sq φ
  field_simp
  linear_combination (c * (cos φ ^ 2 + sin φ ^ 2) * (c ^ 2 * sin φ ^ 2 + cos φ ^ 2)) * hsc

/-- Closed form at `m = 0`: `Π(φ, n, 0) = (φ - arctan((1-c) sin φ cos φ/(cos²φ + c sin²φ)))/c`
with `c = √(1-n)`; on `(-π/2, π/2)` this is `arctan(c tan φ)/c`. -/
theorem Real.incEllIntPim_param_zero {n : ℝ} (hn : n < 1) (φ : ℝ) :
    Real.incEllIntPim φ n 0 = piZeroPrimitive (√(1 - n)) φ := by
  set c := √(1 - n) with hcdef
  have hc : 0 < c := sqrt_pos.mpr (by linarith)
  have hc2 : c ^ 2 = 1 - n := sq_sqrt (by linarith)
  have hderiv : ∀ θ ∈ uIcc 0 φ, HasDerivAt (piZeroPrimitive c) (piIntegrand n 0 θ) θ := by
    intro θ _
    refine (hasDerivAt_piZeroPrimitive hc θ).congr_deriv ?_
    have := sin_sq_add_cos_sq θ
    simp only [piIntegrand, zero_mul, sub_zero, one_rpow, mul_one, hc2, one_div]
    congr 1
    linarith
  rw [Real.incEllIntPim, intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((continuous_piIntegrand hn (by norm_num)).intervalIntegrable _ _)]
  simp [piZeroPrimitive]

/-- `Π(n, 0) = π/(2√(1-n))` for `n < 1`. -/
theorem Real.compEllIntPim_param_zero {n : ℝ} (hn : n < 1) :
    Real.compEllIntPim n 0 = π / (2 * √(1 - n)) := by
  rw [Real.compEllIntPim, Real.incEllIntPim_param_zero hn, piZeroPrimitive]
  simp
  ring

/-- For a nonnegative parameter, the complete third-kind integral is at least its
value at parameter zero; this follows by comparing the positive integrands. -/
theorem Real.compEllIntPim_param_zero_le {n m : ℝ} (hn : n < 1) (hm0 : 0 ≤ m) (hm : m < 1) :
    Real.compEllIntPim n 0 ≤ Real.compEllIntPim n m := by
  apply intervalIntegral.integral_mono_on (show (0 : ℝ) ≤ π / 2 by positivity)
    ((continuous_piIntegrand hn (by norm_num : (0 : ℝ) < 1)).intervalIntegrable _ _)
    ((continuous_piIntegrand hn hm).intervalIntegrable _ _)
  intro θ hθ
  have hpos := one_sub_mul_sin_sq_pos hm θ
  have hle : 1 - m * Real.sin θ ^ 2 ≤ 1 := by nlinarith [sq_nonneg (Real.sin θ)]
  have hr := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hpos hle (by norm_num : (-(1 / 2) : ℝ) ≤ 0)
  simp only [piIntegrand, zero_mul, sub_zero, Real.one_rpow]
  nlinarith [inv_nonneg.mpr (one_sub_mul_sin_sq_pos hn θ).le]

/-- The complete third-kind integral dominates a positive multiple of the first-kind
integral: the reciprocal characteristic factor is at least `min 1 (1-n)⁻¹`. -/
theorem Real.compEllIntPim_ge_min_mul_compEllIntKm {n m : ℝ} (hn : n < 1) (hm : m < 1) :
    min 1 ((1 - n)⁻¹) * Real.compEllIntKm m ≤ Real.compEllIntPim n m := by
  rw [Real.compEllIntKm, Real.compEllIntPim, Real.incEllIntPim,
    ←intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on (show (0 : ℝ) ≤ π / 2 by positivity)
    (((continuous_one_sub_mul_sin_sq_rpow hm _).const_mul _).intervalIntegrable _ _)
    ((continuous_piIntegrand hn hm).intervalIntegrable _ _)
  intro θ hθ
  have hpos := one_sub_mul_sin_sq_pos hn θ
  have hc : min 1 ((1 - n)⁻¹) ≤ (1 - n * Real.sin θ ^ 2)⁻¹ := by
    by_cases hn0 : 0 ≤ n
    · refine (min_le_left _ _).trans ?_
      exact (one_le_inv₀ hpos).mpr (by nlinarith [sq_nonneg (Real.sin θ)])
    · refine (min_le_right _ _).trans ?_
      apply inv_anti₀ hpos
      nlinarith [Real.sin_sq_le_one θ]
  exact mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (one_sub_mul_sin_sq_pos hm θ).le _)

end DLMF.Elliptic

end
