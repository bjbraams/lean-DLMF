/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Struve.Properties

/-!
# Integral representations of `Y_ν` and of `K_ν = H_ν - Y_ν` (DLMF 10.9.5, 11.5.2)

For `re z > 0` let
`L_ν(z) = 2(z/2)^ν/(√π Γ(ν+½)) ∫₀^∞ e^{-zt} (1+t²)^{ν-½} dt` (`besselYLaplace`).

* `struveK_eq_integral` (DLMF 11.5.2): `K_ν(z) = H_ν(z) - Y_ν(z) = L_ν(z)` for **every** `ν`
  and `re z > 0`.
* `besselY_eq_integral` (DLMF 10.9.5): for `re ν > -½` and `re z > 0`,
  `Y_ν(z) = 2(z/2)^ν/(√π Γ(ν+½)) (∫₀¹ (1-t²)^{ν-½} sin(zt) dt - ∫₀^∞ e^{-zt} (1+t²)^{ν-½} dt)`.
* `besselJ_eq_poisson_cos`: Poisson's integral (DLMF 10.9.4) for complex `z` with `re z > 0`.
* `hankelH1_eq_integral_Ioi_one`: `H^{(1)}_ν(z)` through `∫₁^∞ e^{izu} (u²-1)^{ν-½} du`
  (DLMF 10.27.8 with 10.32.8) in the open first quadrant.

Proof. For `re ν > ½` and `z` in the open first quadrant, `H_ν - i J_ν` (Poisson integrals) and
`H^{(1)}_ν` (via `K_ν(-iz)` and DLMF 10.32.8) express `H_ν - Y_ν` through
`∫₀¹ (1-t²)^{ν-½} e^{izt} dt` and `∫₁^∞ (t²-1)^{ν-½} e^{izt} dt`. Cauchy's theorem on the squares
`[0,R]²` for `(-i(s-1))^{ν-½} (s+1)^{ν-½} e^{izs}` (`contour_identity`) rotates these onto the
imaginary axis, giving `L_ν(z)`. The identity theorem extends to `re z > 0`, and the lowering
relations `K_ν' = K_{ν-1} - (ν/z)K_ν`, `L_ν' = L_{ν-1} - (ν/z)L_ν` (the latter by differentiating
under the integral and integrating by parts) extend to all `ν` by downward induction.
-/

@[expose] public noncomputable section

open Complex MeasureTheory Set Filter
open scoped Real Topology

namespace DLMF.Bessel

/-- The Laplace kernel `e^{-zt} (1+t²)^{ν-1/2}`. -/
def yLaplaceKernel (ν z : ℂ) (t : ℝ) : ℂ := exp (-z * t) * (1 + (t : ℂ) ^ 2) ^ (ν - 1 / 2)

/-- `1 + t²` as a real cast. -/
private lemma one_add_sq_ofReal (t : ℝ) : (1 + (t : ℂ) ^ 2) = ((1 + t ^ 2 : ℝ) : ℂ) := by
  push_cast; ring

/-- `‖(1+t²)^w‖ ≤ (1+t)^N` when `2|Re w| ≤ N`. -/
private lemma norm_one_add_sq_cpow_le (w : ℂ) {t : ℝ} (ht : 0 ≤ t) {N : ℕ} (hN : 2 * |w.re| ≤ N) :
    ‖(1 + (t : ℂ) ^ 2) ^ w‖ ≤ (1 + t) ^ N := by
  rw [one_add_sq_ofReal, norm_cpow_eq_rpow_re_of_pos (by positivity)]
  rcases le_total 0 w.re with hw | hw
  · calc (1 + t ^ 2) ^ w.re ≤ ((1 + t) ^ 2) ^ w.re :=
          Real.rpow_le_rpow (by positivity) (by nlinarith) hw
      _ = (1 + t) ^ (2 * w.re) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
      _ ≤ (1 + t) ^ (N : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith)
          (by rw [abs_of_nonneg hw] at hN; exact hN)
      _ = _ := Real.rpow_natCast _ _
  · calc (1 + t ^ 2) ^ w.re ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith) hw
      _ ≤ (1 + t) ^ N := one_le_pow₀ (by linarith)

/-- Exponential bound for the Laplace kernel. -/
theorem norm_yLaplaceKernel_le (ν z : ℂ) {t : ℝ} (ht : 0 ≤ t) {N : ℕ}
    (hN : 2 * |(ν - 1 / 2).re| ≤ N) :
    ‖yLaplaceKernel ν z t‖ ≤ Real.exp (-z.re * t) * (1 + t) ^ N := by
  rw [yLaplaceKernel, norm_mul, Complex.norm_exp]
  refine mul_le_mul (le_of_eq (by simp)) (norm_one_add_sq_cpow_le _ ht hN) (norm_nonneg _)
    (Real.exp_pos _).le

/-- Continuity of the Laplace kernel in `t`. -/
theorem continuous_yLaplaceKernel (ν z : ℂ) : Continuous (yLaplaceKernel ν z) := by
  unfold yLaplaceKernel
  refine (by fun_prop : Continuous fun t : ℝ => exp (-z * t)).mul ?_
  refine Continuous.cpow (by fun_prop) continuous_const fun t => ?_
  rw [one_add_sq_ofReal]; exact ofReal_mem_slitPlane.mpr (by positivity)

/-- A natural bound for `2|Re w|`. -/
private lemma exists_nat_ge_two_abs (w : ℂ) : ∃ N : ℕ, 2 * |w.re| ≤ N := exists_nat_ge _

/-- Integrability of `t^k` times the kernel. -/
theorem integrableOn_pow_mul_yLaplaceKernel (ν : ℂ) {z : ℂ} (hz : 0 < z.re) (k : ℕ) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ k * yLaplaceKernel ν z t) (Ioi 0) := by
  obtain ⟨N, hN⟩ := exists_nat_ge_two_abs (ν - 1 / 2)
  have hb := DLMF.Confluent.integrableOn_exp_mul_rpow_mul_one_add_pow (s := 0) (δ := z.re)
    (by norm_num) hz
    (N + k)
  refine hb.mono' ((by fun_prop : Continuous fun t : ℝ => (t : ℂ) ^ k).mul
    (continuous_yLaplaceKernel ν z)).aestronglyMeasurable ?_
  refine (ae_restrict_mem measurableSet_Ioi).mono fun t (ht : 0 < t) => ?_
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg ht.le, Real.rpow_zero, mul_one]
  have h1 := norm_yLaplaceKernel_le ν z ht.le hN
  have h2 : t ^ k ≤ (1 + t) ^ k := pow_le_pow_left₀ ht.le (by linarith) k
  calc t ^ k * ‖yLaplaceKernel ν z t‖ ≤ (1 + t) ^ k * (Real.exp (-z.re * t) * (1 + t) ^ N) :=
        mul_le_mul h2 h1 (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- Integrability of the Laplace kernel for `re z > 0`. -/
theorem integrableOn_yLaplaceKernel (ν : ℂ) {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (yLaplaceKernel ν z) (Ioi 0) := by
  simpa using integrableOn_pow_mul_yLaplaceKernel ν hz 0

/-- Differentiation under the Laplace integral. -/
theorem hasDerivAt_integral_yLaplaceKernel (ν : ℂ) {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt (fun w => ∫ t in Ioi (0 : ℝ), yLaplaceKernel ν w t)
      (∫ t in Ioi (0 : ℝ), -((t : ℂ) * yLaplaceKernel ν z t)) z := by
  obtain ⟨N, hN⟩ := exists_nat_ge_two_abs (ν - 1 / 2)
  have hδ : 0 < z.re / 2 := by linarith
  have hball : Metric.ball z (z.re / 2) ∈ 𝓝 z := Metric.ball_mem_nhds z hδ
  have hb := DLMF.Confluent.integrableOn_exp_mul_rpow_mul_one_add_pow (s := 0) (δ := z.re / 2)
    (by norm_num) hδ
    (N + 1)
  have hre : ∀ w ∈ Metric.ball z (z.re / 2), z.re / 2 ≤ w.re := by
    intro w hw
    have h1 := abs_re_le_norm (w - z)
    rw [Metric.mem_ball, dist_eq_norm] at hw
    have := (abs_le.mp h1).1
    simp only [sub_re] at this
    linarith
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (bound := fun t : ℝ => Real.exp (-(z.re / 2) * t) * t ^ (0 : ℝ) * (1 + t) ^ (N + 1))
    (F' := fun w t => -((t : ℂ) * yLaplaceKernel ν w t))
    hball (Eventually.of_forall fun w => (continuous_yLaplaceKernel ν w).aestronglyMeasurable)
    (integrableOn_yLaplaceKernel ν hz)
    (((by fun_prop : Continuous fun t : ℝ => (t : ℂ)).mul
      (continuous_yLaplaceKernel ν z)).neg.aestronglyMeasurable) ?_ hb ?_).2
  · refine (ae_restrict_mem measurableSet_Ioi).mono fun t (ht : 0 < t) w hw => ?_
    rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.le, Real.rpow_zero,
      mul_one]
    have h1 := norm_yLaplaceKernel_le ν w ht.le hN
    have h3 : Real.exp (-w.re * t) ≤ Real.exp (-(z.re / 2) * t) :=
      Real.exp_le_exp.mpr (by nlinarith [hre w hw])
    calc t * ‖yLaplaceKernel ν w t‖ ≤ (1 + t) * (Real.exp (-(z.re / 2) * t) * (1 + t) ^ N) :=
          mul_le_mul (by linarith) (h1.trans (mul_le_mul_of_nonneg_right h3 (by positivity)))
            (norm_nonneg _) (by positivity)
      _ = _ := by ring
  · refine Eventually.of_forall fun t w _ => ?_
    unfold yLaplaceKernel
    have h := (((hasDerivAt_id' w).neg).mul_const (t : ℂ)).cexp.mul_const
      ((1 + (t : ℂ) ^ 2) ^ (ν - 1 / 2))
    exact h.congr_deriv (by simp only [Pi.neg_apply]; ring)


/-- `(1+t)^M e^{-bt} → 0`. -/
private lemma tendsto_one_add_pow_mul_exp_neg (M : ℕ) {b : ℝ} (hb : 0 < b) :
    Tendsto (fun t : ℝ => (1 + t) ^ M * Real.exp (-b * t)) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (M : ℝ) b hb).const_mul ((2 : ℝ) ^ M)
  rw [mul_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h ?_ ?_
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    positivity
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    rw [Real.rpow_natCast, ← mul_assoc, ← mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith) (by linarith) M)
      (Real.exp_pos _).le

/-- Derivative of `t ↦ (1+t²)^a`. -/
private lemma hasDerivAt_one_add_sq_cpow (a : ℂ) (x : ℝ) :
    HasDerivAt (fun t : ℝ => (1 + (t : ℂ) ^ 2) ^ a)
      (a * (1 + (x : ℂ) ^ 2) ^ (a - 1) * (2 * (x : ℂ))) x := by
  have hs : (1 + (x : ℂ) ^ 2) ∈ slitPlane := by
    rw [one_add_sq_ofReal]; exact ofReal_mem_slitPlane.mpr (by positivity)
  have h1 : HasDerivAt (fun w : ℂ => 1 + w ^ 2) (2 * (x : ℂ)) (x : ℂ) := by
    simpa using ((hasDerivAt_pow 2 (x : ℂ)).const_add 1)
  exact (h1.cpow_const (c := a) hs).comp_ofReal

/-- `t²(1+t²)^{a-1} = (1+t²)^a - (1+t²)^{a-1}`. -/
private lemma one_add_sq_cpow_sub_one (a : ℂ) (t : ℝ) :
    (t : ℂ) ^ 2 * (1 + (t : ℂ) ^ 2) ^ (a - 1) =
      (1 + (t : ℂ) ^ 2) ^ a - (1 + (t : ℂ) ^ 2) ^ (a - 1) := by
  have hne : (1 + (t : ℂ) ^ 2) ≠ 0 := by
    rw [one_add_sq_ofReal]; exact ofReal_ne_zero.mpr (by positivity)
  have : (1 + (t : ℂ) ^ 2) ^ a = (1 + (t : ℂ) ^ 2) ^ (a - 1) * (1 + (t : ℂ) ^ 2) := by
    have h := cpow_add (a - 1) 1 hne
    rw [cpow_one, sub_add_cancel] at h
    exact h
  rw [this]; ring

/-- Integration by parts: `z ∫ t k_ν = 2ν Λ_ν - (2ν-1) Λ_{ν-1}`. -/
theorem mul_integral_mul_yLaplaceKernel (ν : ℂ) {z : ℂ} (hz : 0 < z.re) :
    z * ∫ t in Ioi (0 : ℝ), (t : ℂ) * yLaplaceKernel ν z t =
      2 * ν * (∫ t in Ioi (0 : ℝ), yLaplaceKernel ν z t) -
        (2 * ν - 1) * ∫ t in Ioi (0 : ℝ), yLaplaceKernel (ν - 1) z t := by
  set a := ν - 1 / 2
  have hk1 := integrableOn_pow_mul_yLaplaceKernel ν hz 1
  simp only [pow_one] at hk1
  have hk := integrableOn_yLaplaceKernel ν hz
  have hk' := integrableOn_yLaplaceKernel (ν - 1) hz
  have hu : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun t : ℝ => (t : ℂ) * (1 + (t : ℂ) ^ 2) ^ a)
      ((1 + (x : ℂ) ^ 2) ^ a + x * (a * (1 + (x : ℂ) ^ 2) ^ (a - 1) * (2 * (x : ℂ)))) x := by
    intro x _
    have h0 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 x := (hasDerivAt_id x).ofReal_comp
    have := h0.mul (hasDerivAt_one_add_sq_cpow a x)
    convert this using 1
    ring
  have hv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun t : ℝ => exp (-z * t)) (exp (-z * x) * (-z)) x := by
    intro x _
    have := ((hasDerivAt_id (x : ℂ)).const_mul (-z)).cexp.comp_ofReal
    simpa using this
  have hIBP := integral_Ioi_mul_deriv_eq_deriv_mul (a := 0) (a' := 0) (b' := 0) hu hv ?_ ?_ ?_ ?_
  rotate_left
  · have h1' : IntegrableOn (fun t : ℝ => -z * ((t : ℂ) * yLaplaceKernel ν z t)) (Ioi 0) :=
      hk1.const_mul (-z)
    refine h1'.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [yLaplaceKernel, Pi.mul_apply]; ring
  · have : IntegrableOn (fun t : ℝ => (1 + 2 * a) * yLaplaceKernel ν z t -
        2 * a * yLaplaceKernel (ν - 1) z t) (Ioi 0) :=
      (hk.const_mul _).sub (hk'.const_mul _)
    refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
    have h2 := one_add_sq_cpow_sub_one a t
    simp only [yLaplaceKernel, Pi.mul_apply, show ν - 1 - 1 / 2 = a - 1 by ring]
    linear_combination (-(2 * a) * exp (-z * t)) * h2
  · have hc : ContinuousAt (fun t : ℝ => (t : ℂ) * (1 + (t : ℂ) ^ 2) ^ a * exp (-z * t)) 0 :=
      ((continuous_ofReal.mul (Continuous.cpow (by fun_prop) continuous_const fun t => by
        rw [one_add_sq_ofReal]; exact ofReal_mem_slitPlane.mpr (by positivity))).mul
        (by fun_prop)).continuousAt
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    rw [show ((0 : ℝ) : ℂ) * (1 + ((0 : ℝ) : ℂ) ^ 2) ^ a * exp (-z * ((0 : ℝ) : ℂ)) = 0 by simp]
      at this
    exact this
  · obtain ⟨N, hN⟩ := exists_nat_ge_two_abs a
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _)
      ?_ (tendsto_one_add_pow_mul_exp_neg (N + 1) hz)
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    have h1 := norm_yLaplaceKernel_le ν z ht hN
    simp only [Pi.mul_apply]
    rw [show (t : ℂ) * (1 + (t : ℂ) ^ 2) ^ a * exp (-z * t) = (t : ℂ) * yLaplaceKernel ν z t by
      simp only [yLaplaceKernel, a]; ring, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht]
    calc t * ‖yLaplaceKernel ν z t‖ ≤ (1 + t) * (Real.exp (-z.re * t) * (1 + t) ^ N) :=
          mul_le_mul (by linarith) h1 (norm_nonneg _) (by positivity)
      _ = _ := by ring
  simp only [sub_zero, zero_sub] at hIBP
  have e1 : ∫ x in Ioi (0 : ℝ), (x : ℂ) * (1 + (x : ℂ) ^ 2) ^ a * (exp (-z * x) * -z) =
      -z * ∫ t in Ioi (0 : ℝ), (t : ℂ) * yLaplaceKernel ν z t := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [yLaplaceKernel, a]; ring
  have e2 : ∫ x in Ioi (0 : ℝ), ((1 + (x : ℂ) ^ 2) ^ a +
      x * (a * (1 + (x : ℂ) ^ 2) ^ (a - 1) * (2 * (x : ℂ)))) * exp (-z * x) =
      ∫ t in Ioi (0 : ℝ), ((1 + 2 * a) * yLaplaceKernel ν z t -
        2 * a * yLaplaceKernel (ν - 1) z t) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    have h2 := one_add_sq_cpow_sub_one a t
    simp only [yLaplaceKernel, show ν - 1 - 1 / 2 = a - 1 by ring]
    linear_combination (2 * a * exp (-z * t)) * h2
  rw [e1, e2, integral_sub (hk.const_mul _) (hk'.const_mul _), integral_const_mul,
    integral_const_mul] at hIBP
  simp only [a] at hIBP
  linear_combination -hIBP


/-- The Laplace-type integral `2(z/2)^ν/(√π Γ(ν+½)) ∫₀^∞ e^{-zt} (1+t²)^{ν-½} dt`
(the second integral in DLMF 10.9.5 and the right side of DLMF 11.5.2). -/
def besselYLaplace (ν z : ℂ) : ℂ :=
  2 * (z / 2) ^ ν / (Real.sqrt π * Gamma (ν + 1 / 2)) * ∫ t in Ioi (0 : ℝ), yLaplaceKernel ν z t

/-- Weighted lowering relation `L_ν' = L_{ν-1} - (ν/z) L_ν` for the Laplace integral. -/
theorem hasDerivAt_besselYLaplace (ν : ℂ) {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt (besselYLaplace ν) (besselYLaplace (ν - 1) z - ν / z * besselYLaplace ν z) z := by
  have hzs : z ∈ slitPlane := Or.inl hz
  have hz0 : z ≠ 0 := slitPlane_ne_zero hzs
  have hz2 : z / 2 ≠ 0 := div_ne_zero hz0 two_ne_zero
  have hp : HasDerivAt (fun w : ℂ => (w / 2) ^ ν) (ν * (z / 2) ^ (ν - 1) * (1 / 2)) z := by
    have h := ((hasDerivAt_id z).div_const (2 : ℂ)).cpow_const (c := ν)
      (DLMF.Bessel.div_two_mem_slitPlane hzs)
    simpa using h
  have hΛ := hasDerivAt_integral_yLaplaceKernel ν hz
  have h := ((hp.const_mul 2).div_const (Real.sqrt π * Gamma (ν + 1 / 2))).mul hΛ
  unfold besselYLaplace
  refine h.congr_deriv ?_
  have hibp := mul_integral_mul_yLaplaceKernel ν hz
  rw [integral_neg]
  have hG : (Gamma (ν - 1 + 1 / 2))⁻¹ = (ν - 1 / 2) * (Gamma (ν + 1 / 2))⁻¹ := by
    have := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (ν - 1 / 2)
    rw [show ν - 1 / 2 + 1 = ν + 1 / 2 by ring] at this
    rw [show ν - 1 + 1 / 2 = ν - 1 / 2 by ring]; exact this
  rw [cpow_sub _ _ hz2, cpow_one]
  simp only [div_eq_mul_inv, mul_inv]
  simp only [div_eq_mul_inv] at hG
  rw [hG]
  set A := ∫ t in Ioi (0 : ℝ), yLaplaceKernel ν z t
  set B := ∫ t in Ioi (0 : ℝ), yLaplaceKernel (ν - 1) z t
  set M := ∫ t in Ioi (0 : ℝ), (t : ℂ) * yLaplaceKernel ν z t
  generalize (z * 2⁻¹) ^ ν = X
  generalize (Gamma (ν + 1 * 2⁻¹))⁻¹ = g
  linear_combination (norm := (field_simp; ring)) (-2 * X * (Real.sqrt π : ℂ)⁻¹ * g / z) * hibp

/-- `i^a = e^{iπa/2}`. -/
private lemma I_cpow' (a : ℂ) : I ^ a = exp (π / 2 * a * I) := by
  rw [cpow_def_of_ne_zero I_ne_zero, log_I]; ring_nf

/-- `(-i)^a = e^{-iπa/2}`. -/
private lemma neg_I_cpow' (a : ℂ) : (-I) ^ a = exp (-(π / 2 * a * I)) := by
  rw [cpow_def_of_ne_zero (neg_ne_zero.mpr I_ne_zero), log_neg_I]; ring_nf

/-- The contour integrand on the segment `[0,1]`. -/
theorem contour_branch_unit (a : ℂ) (ha : a ≠ 0) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (-I * ((t : ℂ) - 1)) ^ a * ((t : ℂ) + 1) ^ a = exp (π / 2 * a * I) * (1 - (t : ℂ) ^ 2) ^ a := by
  rcases ht1.lt_or_eq with ht1 | rfl
  · have h1 : -I * ((t : ℂ) - 1) = ((1 - t : ℝ) : ℂ) * I := by push_cast; ring
    have h2 : ((t : ℂ) + 1) = ((t + 1 : ℝ) : ℂ) := by push_cast; ring
    have h3 : (1 - (t : ℂ) ^ 2) = ((1 - t : ℝ) : ℂ) * ((t + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [h1, h2, h3, DLMF.Confluent.ofReal_mul_cpow' (by linarith) I_ne_zero,
      mul_cpow_ofReal_nonneg (by linarith) (by linarith), I_cpow']
    ring
  · simp [zero_cpow ha]

/-- The contour integrand on the ray `[1,∞)`. -/
theorem contour_branch_ray (a : ℂ) (ha : a ≠ 0) {t : ℝ} (ht1 : 1 ≤ t) :
    (-I * ((t : ℂ) - 1)) ^ a * ((t : ℂ) + 1) ^ a =
      exp (-(π / 2 * a * I)) * ((t : ℂ) ^ 2 - 1) ^ a := by
  rcases ht1.lt_or_eq with ht1 | rfl
  · have h1 : -I * ((t : ℂ) - 1) = ((t - 1 : ℝ) : ℂ) * (-I) := by push_cast; ring
    have h2 : ((t : ℂ) + 1) = ((t + 1 : ℝ) : ℂ) := by push_cast; ring
    have h3 : ((t : ℂ) ^ 2 - 1) = ((t - 1 : ℝ) : ℂ) * ((t + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [h1, h2, h3, DLMF.Confluent.ofReal_mul_cpow' (by linarith) (neg_ne_zero.mpr I_ne_zero),
      mul_cpow_ofReal_nonneg (by linarith) (by linarith), neg_I_cpow']
    ring
  · simp [zero_cpow ha]

/-- `(conj w)^a w^a = (|w|²)^a` for `re w > 0`. -/
private lemma conj_cpow_mul_cpow {w : ℂ} (hw : 0 < w.re) (a : ℂ) :
    (starRingEnd ℂ w) ^ a * w ^ a = ((Complex.normSq w : ℝ) : ℂ) ^ a := by
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw
  have hc0 : starRingEnd ℂ w ≠ 0 := by simpa using hw0
  have hn : (0 : ℝ) < Complex.normSq w := Complex.normSq_pos.mpr hw0
  have harg : arg w ≠ π := by
    intro h; have := arg_lt_pi_iff.mpr (Or.inl hw.le); linarith [this]
  rw [cpow_def_of_ne_zero hc0, cpow_def_of_ne_zero hw0,
    cpow_def_of_ne_zero (ofReal_ne_zero.mpr hn.ne'), ← exp_add, log_conj _ harg]
  congr 1
  rw [← add_mul]
  congr 1
  rw [← ofReal_log hn.le, Complex.ext_iff]
  constructor
  · simp only [add_re, conj_re, log_re, ofReal_re]
    rw [Complex.normSq_eq_norm_sq, Real.log_pow]; push_cast; ring
  · simp [log_im]

/-- The contour integrand on the imaginary axis. -/
theorem contour_branch_imag (a : ℂ) (y : ℝ) :
    (-I * ((y : ℂ) * I - 1)) ^ a * ((y : ℂ) * I + 1) ^ a =
      exp (π / 2 * a * I) * (1 + (y : ℂ) ^ 2) ^ a := by
  set w : ℂ := 1 + y * I
  have hwre : 0 < w.re := by simp [w]
  have h1 : -I * ((y : ℂ) * I - 1) = starRingEnd ℂ w * exp ((π / 2 : ℝ) * I) := by
    rw [DLMF.Bessel.exp_pi_div_two_mul_I']
    simp only [w, map_add, map_one, map_mul, conj_ofReal, conj_I]
    ring_nf
  have harg : |arg (starRingEnd ℂ w)| < π / 2 :=
    abs_arg_lt_pi_div_two_iff.mpr (Or.inl (by simpa using hwre))
  rw [h1, DLMF.Confluent.cpow_mul_exp_mul_I (by simpa using (fun h => by simp [h] at hwre))
      (by linarith [(abs_lt.mp harg).1, Real.pi_pos])
      (by linarith [(abs_lt.mp harg).2, Real.pi_pos])]
  rw [show (y : ℂ) * I + 1 = w by simp [w]; ring]
  rw [mul_comm ((starRingEnd ℂ w) ^ a), mul_assoc, conj_cpow_mul_cpow hwre]
  have hn : (Complex.normSq w : ℂ) = 1 + (y : ℂ) ^ 2 := by
    simp [w, Complex.normSq_apply]; ring
  rw [hn]; push_cast; ring_nf


/-- The integrand `(-i(s-1))^a (s+1)^a e^{izs}` of the quarter-plane contour argument. -/
def contourG (a z s : ℂ) : ℂ := (-I * (s - 1)) ^ a * (s + 1) ^ a * exp (I * z * s)

/-- `-i(s-1)` is in the slit plane for `im s ≥ 0`, `s ≠ 1`. -/
private lemma neg_I_mul_sub_one_mem_slitPlane {s : ℂ} (h1 : 0 ≤ s.im) (hs : s ≠ 1) :
    -I * (s - 1) ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  simp only [mul_re, neg_re, I_re, sub_re, one_re, neg_im, I_im, sub_im, one_im, mul_im]
  rcases h1.lt_or_eq with h | h
  · left; linarith
  · right
    intro h'
    apply hs
    apply Complex.ext <;> simp <;> linarith

/-- `s + 1` is in the slit plane for `re s ≥ 0`. -/
private lemma add_one_mem_slitPlane' {s : ℂ} (h0 : 0 ≤ s.re) : s + 1 ∈ slitPlane :=
  Or.inl (by simp; linarith)

/-- Continuity of the contour integrand on the closed quadrant. -/
theorem continuousAt_contourG {a : ℂ} (ha : 0 < a.re) (z : ℂ) {s : ℂ} (h0 : 0 ≤ s.re)
    (h1 : 0 ≤ s.im) : ContinuousAt (contourG a z) s := by
  unfold contourG
  have hB : ContinuousAt (fun s : ℂ => (s + 1) ^ a) s :=
    ContinuousAt.cpow (by fun_prop) continuousAt_const (add_one_mem_slitPlane' h0)
  have hA : ContinuousAt (fun s : ℂ => (-I * (s - 1)) ^ a) s := by
    by_cases hs : s = 1
    · subst hs
      have hc := continuousAt_cpow_zero_of_re_pos ha
      have hf : ContinuousAt (fun s : ℂ => (-I * (s - 1), a)) 1 := by fun_prop
      exact hc.comp_of_eq hf (by simp)
    · exact ContinuousAt.cpow (by fun_prop) continuousAt_const
        (neg_I_mul_sub_one_mem_slitPlane h1 hs)
  exact (hA.mul hB).mul (by fun_prop)

/-- Holomorphy of the contour integrand in the open upper quadrant. -/
theorem differentiableAt_contourG (a z : ℂ) {s : ℂ} (h0 : 0 ≤ s.re) (h1 : 0 < s.im) :
    DifferentiableAt ℂ (contourG a z) s := by
  unfold contourG
  have hs : s ≠ 1 := fun h => by simp [h] at h1
  have hA : DifferentiableAt ℂ (fun s : ℂ => (-I * (s - 1)) ^ a) s :=
    DifferentiableAt.cpow (by fun_prop) (differentiableAt_const _)
      (neg_I_mul_sub_one_mem_slitPlane h1.le hs)
  have hB : DifferentiableAt ℂ (fun s : ℂ => (s + 1) ^ a) s :=
    DifferentiableAt.cpow (by fun_prop) (differentiableAt_const _) (add_one_mem_slitPlane' h0)
  exact (hA.mul hB).mul (by fun_prop)

/-- Bound for the contour integrand on `[0,R]²`. -/
theorem norm_contourG_le {a : ℂ} (ha : 0 < a.re) (z : ℂ) {R : ℝ} (hR : 1 ≤ R) {s : ℂ}
    (h0 : 0 ≤ s.re) (h0' : s.re ≤ R) (h1 : 0 ≤ s.im) (h1' : s.im ≤ R) :
    ‖contourG a z s‖ ≤ (3 * R) ^ (2 * a.re) * Real.exp (2 * (π * |a.im|)) *
      Real.exp (-(z.re * s.im + z.im * s.re)) := by
  unfold contourG
  have hn : ‖s‖ ≤ s.re + s.im := by
    have := Complex.norm_le_abs_re_add_abs_im s
    rwa [abs_of_nonneg h0, abs_of_nonneg h1] at this
  have hA : ‖-I * (s - 1)‖ ≤ 3 * R := by
    rw [norm_mul, norm_neg, norm_I, one_mul]
    have := norm_sub_le s 1
    simp at this; linarith
  have hB : ‖s + 1‖ ≤ 3 * R := by
    have := norm_add_le s 1
    simp at this; linarith
  have h1 := (DLMF.Confluent.norm_cpow_le_exp (-I * (s - 1)) a).trans (mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow (norm_nonneg _) hA ha.le) (Real.exp_pos _).le)
  have h2 := (DLMF.Confluent.norm_cpow_le_exp (s + 1) a).trans (mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow (norm_nonneg _) hB ha.le) (Real.exp_pos _).le)
  have h3 : ‖exp (I * z * s)‖ = Real.exp (-(z.re * s.im + z.im * s.re)) := by
    rw [Complex.norm_exp]; congr 1; simp; ring
  rw [norm_mul, norm_mul, h3]
  have hR3 : (0 : ℝ) ≤ 3 * R := by linarith
  calc ‖(-I * (s - 1)) ^ a‖ * ‖(s + 1) ^ a‖ * Real.exp (-(z.re * s.im + z.im * s.re))
      ≤ ((3 * R) ^ a.re * Real.exp (π * |a.im|)) * ((3 * R) ^ a.re * Real.exp (π * |a.im|)) *
          Real.exp (-(z.re * s.im + z.im * s.re)) := by
        gcongr
    _ = _ := by
        rw [show 2 * a.re = a.re + a.re by ring, Real.rpow_add' hR3 (by linarith),
          show 2 * (π * |a.im|) = π * |a.im| + π * |a.im| by ring, Real.exp_add]
        ring

/-- The edge bound tends to zero. -/
theorem tendsto_contour_edge_bound {a : ℂ} (m : ℝ) (hm : 0 < m) :
    Tendsto (fun R : ℝ => (3 * R) ^ (2 * a.re) * Real.exp (2 * (π * |a.im|)) *
      Real.exp (-m * R) * R) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2 * a.re + 1) m hm).const_mul
    ((3 : ℝ) ^ (2 * a.re) * Real.exp (2 * (π * |a.im|)))
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  rw [Real.mul_rpow (by norm_num) hR.le, Real.rpow_add hR, Real.rpow_one]
  ring


/-- Integrability of `e^{izu} (u²-1)^a` on `(1,∞)` for `im z > 0`. -/
theorem integrableOn_exp_mul_sq_sub_one_cpow {a z : ℂ} (ha : 0 ≤ a.re) (hz : 0 < z.im) :
    IntegrableOn (fun u : ℝ => exp (I * z * u) * ((u : ℂ) ^ 2 - 1) ^ a) (Ioi 1) := by
  obtain ⟨N, hN⟩ := exists_nat_ge (2 * a.re)
  have hb := (DLMF.Confluent.integrableOn_exp_mul_rpow_mul_one_add_pow (s := 0) (δ := z.im)
    (by norm_num) hz N).mono_set (Ioi_subset_Ioi zero_le_one)
  have hcont : ContinuousOn (fun u : ℝ => exp (I * z * u) * ((u : ℂ) ^ 2 - 1) ^ a) (Ioi 1) := by
    intro u (hu : 1 < u)
    refine ContinuousAt.continuousWithinAt ?_
    refine (by fun_prop : Continuous fun u : ℝ => exp (I * z * u)).continuousAt.mul ?_
    refine ContinuousAt.cpow (by fun_prop) continuousAt_const ?_
    rw [show (u : ℂ) ^ 2 - 1 = ((u ^ 2 - 1 : ℝ) : ℂ) by push_cast; ring]
    exact ofReal_mem_slitPlane.mpr (by nlinarith)
  refine hb.mono' (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  refine (ae_restrict_mem measurableSet_Ioi).mono fun u (hu : 1 < u) => ?_
  rw [norm_mul, Complex.norm_exp, show (u : ℂ) ^ 2 - 1 = ((u ^ 2 - 1 : ℝ) : ℂ) by push_cast; ring,
    norm_cpow_eq_rpow_re_of_pos (by nlinarith), Real.rpow_zero, mul_one]
  have h1 : (I * z * u).re = -z.im * u := by simp
  rw [h1]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  calc (u ^ 2 - 1) ^ a.re ≤ ((1 + u) ^ 2) ^ a.re :=
        Real.rpow_le_rpow (by nlinarith) (by nlinarith) ha
    _ = (1 + u) ^ (2 * a.re) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
    _ ≤ (1 + u) ^ (N : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) hN
    _ = _ := Real.rpow_natCast _ _

/-- **Quarter-plane contour rotation.** For `re ν > 1/2`, `a = ν - 1/2`, and `z` in the open first
quadrant, `e^{iπa/2} ∫₀¹ (1-t²)^a e^{izt} dt + e^{-iπa/2} ∫₁^∞ e^{izu} (u²-1)^a du
= i e^{iπa/2} ∫₀^∞ e^{-zt} (1+t²)^a dt`. -/
theorem contour_identity {ν z : ℂ} (hν : 1 / 2 < ν.re) (hz : 0 < z.re) (hzi : 0 < z.im) :
    exp (π / 2 * (ν - 1 / 2) * I) * (∫ t in (0 : ℝ)..1, (1 - (t : ℂ) ^ 2) ^ (ν - 1 / 2) *
        exp (I * z * t)) +
      exp (-(π / 2 * (ν - 1 / 2) * I)) * ∫ u in Ioi (1 : ℝ), exp (I * z * u) *
        ((u : ℂ) ^ 2 - 1) ^ (ν - 1 / 2) =
      I * (exp (π / 2 * (ν - 1 / 2) * I) * ∫ t in Ioi (0 : ℝ), yLaplaceKernel ν z t) := by
  set a := ν - 1 / 2 with ha_def
  have ha : 0 < a.re := by simp [a]; linarith
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha
  set G := contourG a z
  set m := min z.re z.im
  have hm : 0 < m := lt_min hz hzi
  -- Cauchy's theorem on the squares `[0,R]²`
  have hC : ∀ R : ℝ, 0 ≤ R → ((∫ x in (0 : ℝ)..R, G x) - (∫ x in (0 : ℝ)..R, G (x + R * I)) +
      I * (∫ y in (0 : ℝ)..R, G (R + y * I))) - I * (∫ y in (0 : ℝ)..R, G (y * I)) = 0 := by
    intro R hR
    have h := integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn G 0
      (R + R * I) ?_ ?_
    · simpa using h
    · intro s hs
      simp only [mem_reProdIm, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
        mul_one, sub_self, add_zero, zero_re, add_im, mul_im, zero_add, zero_im] at hs
      rw [uIcc_of_le hR] at hs
      exact (continuousAt_contourG ha z hs.1.1 hs.2.1).continuousWithinAt
    · intro s hs
      simp only [mem_reProdIm, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
        mul_one, sub_self, add_zero, zero_re, add_im, mul_im, zero_add, zero_im,
        min_eq_left hR, max_eq_right hR] at hs
      exact (differentiableAt_contourG a z hs.1.1.le hs.2.1).differentiableWithinAt
  -- bottom edge
  have hbot : Tendsto (fun R : ℝ => ∫ x in (0 : ℝ)..R, G x) atTop
      (𝓝 (exp (π / 2 * a * I) * (∫ t in (0 : ℝ)..1, (1 - (t : ℂ) ^ 2) ^ a * exp (I * z * t)) +
        exp (-(π / 2 * a * I)) * ∫ u in Ioi (1 : ℝ), exp (I * z * u) * ((u : ℂ) ^ 2 - 1) ^ a)) := by
    have hQ := intervalIntegral_tendsto_integral_Ioi 1
      (integrableOn_exp_mul_sq_sub_one_cpow ha.le hzi) tendsto_id
    have hQ' := (hQ.const_mul (exp (-(π / 2 * a * I)))).const_add
      (exp (π / 2 * a * I) * (∫ t in (0 : ℝ)..1, (1 - (t : ℂ) ^ 2) ^ a * exp (I * z * t)))
    refine hQ'.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    have hGc : ∀ x : ℝ, 0 ≤ x → ContinuousAt (fun x : ℝ => G x) x := fun x hx =>
      (continuousAt_contourG ha z (by simpa using hx) (by simp)).comp continuous_ofReal.continuousAt
    have hii : ∀ b c : ℝ, 0 ≤ b → b ≤ c → IntervalIntegrable (fun x : ℝ => G x) volume b c :=
      fun b c hb hbc => (ContinuousOn.intervalIntegrable fun x hx => (hGc x (by
        rw [uIcc_of_le hbc] at hx; linarith [hx.1])).continuousWithinAt)
    rw [← intervalIntegral.integral_add_adjacent_intervals (hii 0 1 le_rfl zero_le_one)
      (hii 1 R zero_le_one hR), ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_const_mul]
    congr 1
    · refine intervalIntegral.integral_congr fun t ht => ?_
      rw [uIcc_of_le zero_le_one] at ht
      simp only [G, contourG]
      rw [contour_branch_unit a ha0 ht.1 ht.2]; ring
    · refine intervalIntegral.integral_congr fun t ht => ?_
      rw [id, uIcc_of_le hR] at ht
      simp only [G, contourG]
      rw [contour_branch_ray a ha0 ht.1]; ring
  -- left edge
  have hleft : Tendsto (fun R : ℝ => ∫ y in (0 : ℝ)..R, G (y * I)) atTop
      (𝓝 (exp (π / 2 * a * I) * ∫ t in Ioi (0 : ℝ), yLaplaceKernel ν z t)) := by
    have hL := (intervalIntegral_tendsto_integral_Ioi 0 (integrableOn_yLaplaceKernel ν hz)
      tendsto_id).const_mul (exp (π / 2 * a * I))
    refine hL.congr' (Eventually.of_forall fun R => ?_)
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun y _ => ?_
    simp only [G, contourG, yLaplaceKernel]
    rw [contour_branch_imag a y, show I * z * (y * I) = -z * y by ring_nf; rw [I_sq]; ring]
    ring
  -- top and right edges
  have hedge : ∀ (f : ℝ → ℝ → ℂ), (∀ R : ℝ, 1 ≤ R → ∀ x ∈ Ioc (0 : ℝ) R,
      ‖G (f R x)‖ ≤ (3 * R) ^ (2 * a.re) * Real.exp (2 * (π * |a.im|)) * Real.exp (-m * R)) →
      Tendsto (fun R : ℝ => ∫ x in (0 : ℝ)..R, G (f R x)) atTop (𝓝 0) := by
    intro f hf
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun R => norm_nonneg _) ?_
      (tendsto_contour_edge_bound (a := a) m hm)
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := R)
      (f := fun x => G (f R x)) (C := (3 * R) ^ (2 * a.re) * Real.exp (2 * (π * |a.im|)) *
        Real.exp (-m * R)) (fun x hx => by
          rw [uIoc_of_le (by linarith)] at hx; exact hf R hR x hx)
    rwa [sub_zero, abs_of_nonneg (show (0 : ℝ) ≤ R by linarith)] at this
  have htop := hedge (fun R x => x + R * I) fun R hR x hx => by
    refine (norm_contourG_le ha z hR (by simp; linarith [hx.1]) (by simp; exact hx.2)
      (by simp; linarith) (by simp)).trans ?_
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, add_im, mul_im, zero_add]
    nlinarith [min_le_left z.re z.im, hx.1]
  have hright := hedge (fun R y => R + y * I) fun R hR y hy => by
    refine (norm_contourG_le ha z hR (by simp; linarith) (by simp)
      (by simp; linarith [hy.1]) (by simp; exact hy.2)).trans ?_
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, add_im, mul_im, zero_add]
    nlinarith [min_le_right z.re z.im, hy.1]
  have hlim := ((hbot.sub htop).add (hright.const_mul I)).sub (hleft.const_mul I)
  have h0 : Tendsto (fun R : ℝ => ((∫ x in (0 : ℝ)..R, G x) - (∫ x in (0 : ℝ)..R, G (x + R * I)) +
      I * (∫ y in (0 : ℝ)..R, G (R + y * I))) - I * (∫ y in (0 : ℝ)..R, G (y * I))) atTop (𝓝 0) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR using (hC R hR).symm)
  have := tendsto_nhds_unique hlim h0
  linear_combination this

/-- `(-iz/2)^ν = (z/2)^ν e^{-iνπ/2}` for `re z > 0`. -/
private lemma neg_I_mul_div_two_cpow {z : ℂ} (hz : 0 < z.re) (ν : ℂ) :
    (-I * z / 2) ^ ν = (z / 2) ^ ν * exp (-(I * ν * π / 2)) := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have harg : |arg z| < π / 2 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz)
  have h := DLMF.Confluent.cpow_mul_exp_mul_I (div_ne_zero hz0 two_ne_zero) (α := -(π / 2))
    (by rw [arg_div_two]; linarith [(abs_lt.mp harg).1, Real.pi_pos])
    (by rw [arg_div_two]; linarith [(abs_lt.mp harg).2, Real.pi_pos]) ν
  rw [exp_neg_pi_div_two_mul_I'] at h
  rw [show -I * z / 2 = z / 2 * -I by ring, h]
  congr 2; push_cast; ring

/-- Poisson's integral (DLMF 10.9.4) for complex `z` with `re z > 0`, on `[0,1]` with `cos`;
the project's tagged form `besselJ_eq_poisson_integral` is for real `x > 0`. -/
theorem besselJ_eq_poisson_cos {ν z : ℂ} (hν : -1 / 2 < ν.re) (hz : 0 < z.re) :
    besselJ ν z = 2 * (z / 2) ^ ν / (Real.sqrt π * Gamma (ν + 1 / 2)) *
      ∫ t : ℝ in (0 : ℝ)..1, (1 - (t : ℂ) ^ 2) ^ (ν - 1 / 2) * cos (z * t) := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have harg : |arg z| < π / 2 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz)
  have hI := besselI_neg_I_mul hz0 (by linarith [(abs_lt.mp harg).1]) ν
  rw [besselI_eq_poisson_integral hν (mem_slitPlane_neg_I_mul hz),
    neg_I_mul_div_two_cpow hz] at hI
  have hw := DLMF.Struve.intervalIntegrable_poissonWeight hν
  set f : ℝ → ℂ := fun t => (1 - (t : ℂ) ^ 2) ^ (ν - 1 / 2) * exp (-I * z * t)
  have hf1 : IntervalIntegrable f volume 0 1 :=
    hw.mul_continuousOn (by fun_prop : Continuous fun t : ℝ => exp (-I * z * t)).continuousOn
  have hg1 : IntervalIntegrable (fun t => f (-t)) volume 0 1 := by
    have := hw.mul_continuousOn (by fun_prop : Continuous fun t : ℝ => exp (I * z * t)).continuousOn
    refine this.congr fun t _ => ?_
    simp only [f]; push_cast; ring_nf
  have hf0 : IntervalIntegrable f volume (-1) 0 := by
    have := (IntervalIntegrable.iff_comp_neg (f := fun t => f (-t)) (by simp)).mp hg1
    simp only [neg_neg, neg_zero] at this
    exact this.symm
  have hsplit : (∫ t : ℝ in (-1 : ℝ)..1, f t) =
      2 * ∫ t : ℝ in (0 : ℝ)..1, (1 - (t : ℂ) ^ 2) ^ (ν - 1 / 2) * cos (z * t) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hf0 hf1]
    have hneg : (∫ t : ℝ in (-1 : ℝ)..0, f t) = ∫ t : ℝ in (0 : ℝ)..1, f (-t) := by
      rw [intervalIntegral.integral_comp_neg (fun t => f t)]; norm_num
    rw [hneg, ← intervalIntegral.integral_add hg1 hf1, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [f, cos]
    push_cast
    ring_nf
  rw [hsplit] at hI
  have he : exp (-(I * ν * π / 2)) ≠ 0 := exp_ne_zero _
  apply mul_left_cancel₀ he
  rw [← hI]
  ring


/-- `H^{(1)}_ν(z)` as a boundary Laplace integral (DLMF 10.27.8 with 10.32.8), `z` in the open
first quadrant. -/
lemma hankelH1_eq_integral_Ioi_one {ν z : ℂ} (hν : -1 / 2 < ν.re) (hz : 0 < z.re) (hzi : 0 < z.im) :
    hankelH1 ν z = 2 * (z / 2) ^ ν / (Real.sqrt π * Gamma (ν + 1 / 2)) * (-I) *
      exp (-(I * ν * π)) *
        ∫ u in Ioi (1 : ℝ), exp (I * z * u) * ((u : ℂ) ^ 2 - 1) ^ (ν - 1 / 2) := by
  have hzs : z ∈ slitPlane := Or.inl hz
  have harg : |arg z| < π / 2 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz)
  rw [hankelH1_eq_besselK ν hzs (by linarith [(abs_lt.mp harg).1]),
    besselK_eq_integral_Ioi_one hν (by simpa using hzi), neg_I_mul_div_two_cpow hz]
  have hQ : (∫ u : ℝ in Ioi 1, exp (-(-I * z) * u) * ((u : ℂ) ^ 2 - 1) ^ (ν - 1 / 2)) =
      ∫ u in Ioi (1 : ℝ), exp (I * z * u) * ((u : ℂ) ^ 2 - 1) ^ (ν - 1 / 2) := by
    congr 1; funext u; ring_nf
  rw [hQ]
  generalize ∫ u in Ioi (1 : ℝ), exp (I * z * u) * ((u : ℂ) ^ 2 - 1) ^ (ν - 1 / 2) = Q
  have hsq : (Real.sqrt π : ℂ) * (Real.sqrt π : ℂ) = π := by
    rw [← ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
  have hsq0 : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have he : exp (-(I * ν * π / 2)) * exp (-(I * ν * π / 2)) = exp (-(I * ν * π)) := by
    rw [← exp_add]; ring_nf
  rw [← he]
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [← hsq]
  field_simp
  ring_nf
  rw [I_sq]
  ring

/-- **Base case.** For `re ν > 1/2` and `z` in the open first quadrant, `K_ν(z)` equals the
Laplace integral. -/
theorem struveK_eq_besselYLaplace_of_quadrant {ν z : ℂ} (hν : 1 / 2 < ν.re) (hz : 0 < z.re)
    (hzi : 0 < z.im) : DLMF.Struve.struveK ν z = besselYLaplace ν z := by
  have hν' : -1 / 2 < ν.re := by linarith
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have hw := DLMF.Struve.intervalIntegrable_poissonWeight hν'
  set c := 2 * (z / 2) ^ ν / (Real.sqrt π * Gamma (ν + 1 / 2))
  set w : ℝ → ℂ := fun t => (1 - (t : ℂ) ^ 2) ^ (ν - 1 / 2)
  have hH := DLMF.Struve.struveH_eq_poisson hν' hz0
  have hJ := besselJ_eq_poisson_cos hν' hz
  have hH1 := hankelH1_eq_integral_Ioi_one hν' hz hzi
  have hcon := contour_identity hν hz hzi
  have hP : (∫ t in (0 : ℝ)..1, (1 - (t : ℂ) ^ 2) ^ (ν - 1 / 2) * exp (I * z * t)) =
      (∫ t in (0 : ℝ)..1, (1 - (t : ℂ) ^ 2) ^ (ν - 1 / 2) * cos (z * t)) +
        I * ∫ t in (0 : ℝ)..1, (1 - (t : ℂ) ^ 2) ^ (ν - 1 / 2) * sin (z * t) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add
      (hw.mul_continuousOn (by fun_prop : Continuous fun t : ℝ => cos (z * t)).continuousOn)
      ((hw.mul_continuousOn
        (by fun_prop : Continuous fun t : ℝ => sin (z * t)).continuousOn).const_mul I)]
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [show I * z * t = (z * t) * I by ring, exp_mul_I]; ring
  rw [hP] at hcon
  have hY : besselY ν z = -I * (hankelH1 ν z - besselJ ν z) := by
    rw [hankelH1]; ring_nf; rw [I_sq]; ring
  have he : exp (-(π / 2 * (ν - 1 / 2) * I)) =
      I * exp (-(I * ν * π)) * exp (π / 2 * (ν - 1 / 2) * I) := by
    calc exp (-(π / 2 * (ν - 1 / 2) * I))
        = exp (((π / 2 : ℝ) : ℂ) * I) * exp (-(I * ν * π)) * exp (π / 2 * (ν - 1 / 2) * I) := by
          rw [← exp_add, ← exp_add]; congr 1; push_cast; ring
      _ = _ := by rw [exp_pi_div_two_mul_I']
  rw [he] at hcon
  have hep : exp (π / 2 * (ν - 1 / 2) * I) ≠ 0 := exp_ne_zero _
  unfold DLMF.Struve.struveK besselYLaplace
  rw [hY, hH1, hJ, hH]
  generalize ∫ t in (0 : ℝ)..1, (1 - (t : ℂ) ^ 2) ^ (ν - 1 / 2) * cos (z * t) = C at *
  generalize ∫ t in (0 : ℝ)..1, (1 - (t : ℂ) ^ 2) ^ (ν - 1 / 2) * sin (z * t) = Sn at *
  generalize ∫ u in Ioi (1 : ℝ), exp (I * z * u) * ((u : ℂ) ^ 2 - 1) ^ (ν - 1 / 2) = Q at *
  generalize ∫ t in Ioi (0 : ℝ), yLaplaceKernel ν z t = Λ at *
  generalize exp (π / 2 * (ν - 1 / 2) * I) = ep at *
  generalize exp (-(I * ν * π)) = E at *
  have hΛ : Λ = Sn + E * Q - I * C := by
    apply mul_left_cancel₀ (mul_ne_zero I_ne_zero hep)
    linear_combination (norm := (ring_nf; rw [I_sq]; ring_nf)) -hcon
  rw [hΛ]
  ring_nf; rw [I_sq]; ring


/-- The right half-plane is open. -/
private lemma isOpen_re_pos : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re

/-- The Laplace integral is analytic on the right half-plane. -/
theorem analyticOnNhd_besselYLaplace (ν : ℂ) : AnalyticOnNhd ℂ (besselYLaplace ν) {z | 0 < z.re} :=
  DifferentiableOn.analyticOnNhd (fun _ hz =>
    (hasDerivAt_besselYLaplace ν hz).differentiableAt.differentiableWithinAt) isOpen_re_pos

/-- `K_ν = H_ν - Y_ν` is analytic on the slit plane. -/
theorem analyticOnNhd_struveK (ν : ℂ) : AnalyticOnNhd ℂ (DLMF.Struve.struveK ν) slitPlane := by
  have h := (DLMF.Struve.struve_analytic ν).1.sub (DLMF.Struve.besselY_analytic ν)
  exact h

/-- The base case on the whole right half-plane. -/
theorem struveK_eq_besselYLaplace_of_re_gt {ν : ℂ} (hν : 1 / 2 < ν.re) {z : ℂ} (hz : 0 < z.re) :
    DLMF.Struve.struveK ν z = besselYLaplace ν z := by
  have hU : IsPreconnected {z : ℂ | 0 < z.re} := (convex_halfSpace_re_gt 0).isPreconnected
  have hK := (analyticOnNhd_struveK ν).mono
    (show {w : ℂ | 0 < w.re} ⊆ slitPlane from fun w hw => Or.inl hw)
  have hV : {w : ℂ | 0 < w.re} ∩ {w : ℂ | 0 < w.im} ∈ 𝓝 (1 + I) :=
    (isOpen_re_pos.inter (isOpen_lt continuous_const continuous_im)).mem_nhds (by simp)
  refine hK.eqOn_of_preconnected_of_eventuallyEq (analyticOnNhd_besselYLaplace ν) hU
    (z₀ := 1 + I) (by simp) ?_ hz
  filter_upwards [hV] with w hw
  exact struveK_eq_besselYLaplace_of_quadrant hν hw.1 hw.2

/-- Lowering relation `K_ν' = K_{ν-1} - (ν/z) K_ν` for `K_ν = H_ν - Y_ν` (DLMF 11.4.23–24 with
10.6.1–2). -/
theorem hasDerivAt_struveK_lower (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (DLMF.Struve.struveK ν)
      (DLMF.Struve.struveK (ν - 1) z - ν / z * DLMF.Struve.struveK ν z) z := by
  have hH := DLMF.Struve.struveH_derivative ν hz
  have hr := DLMF.Struve.struveH_recurrence ν hz
  have hY := hasDerivAt_besselY ν hz
  have hY3 := besselY_add_sub ν hz
  refine (hH.sub hY).congr_deriv ?_
  unfold DLMF.Struve.struveK
  linear_combination (-1 / 2) * hr - hY3

/-- **The Laplace integral for `K_ν = H_ν - Y_ν`** (DLMF 11.5.2), for every order `ν` and
`re z > 0`; at `ν + 1/2 ∈ {0,-1,…}` both sides vanish. -/
theorem struveK_eq_besselYLaplace (ν : ℂ) {z : ℂ} (hz : 0 < z.re) :
    DLMF.Struve.struveK ν z = besselYLaplace ν z := by
  suffices h : ∀ n : ℕ, ∀ μ : ℂ, 1 / 2 < μ.re + n → ∀ w : ℂ, 0 < w.re →
      DLMF.Struve.struveK μ w = besselYLaplace μ w by
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / 2 - ν.re)
    exact h n ν (by linarith) z hz
  intro n
  induction n with
  | zero => intro μ hμ w hw; exact struveK_eq_besselYLaplace_of_re_gt (by simpa using hμ) hw
  | succ n ih =>
    intro μ hμ w hw
    have ih' := ih (μ + 1) (by simp; push_cast at hμ; linarith)
    have hK := hasDerivAt_struveK_lower (μ + 1) (Or.inl hw : w ∈ slitPlane)
    have hL := hasDerivAt_besselYLaplace (μ + 1) hw
    have heq : DLMF.Struve.struveK (μ + 1) =ᶠ[𝓝 w] besselYLaplace (μ + 1) := by
      filter_upwards [isOpen_re_pos.mem_nhds hw] with v hv using ih' v hv
    have := hK.unique (hL.congr_of_eventuallyEq heq)
    rw [add_sub_cancel_right, ih' w hw] at this
    linear_combination this

/-- **DLMF 11.5.2** in explicit form. -/
theorem struveK_eq_integral (ν : ℂ) {z : ℂ} (hz : 0 < z.re) :
    DLMF.Struve.struveK ν z = 2 * (z / 2) ^ ν / (Real.sqrt π * Gamma (ν + 1 / 2)) *
      ∫ t in Ioi (0 : ℝ), exp (-z * t) * (1 + (t : ℂ) ^ 2) ^ (ν - 1 / 2) :=
  struveK_eq_besselYLaplace ν hz

/-- **Integral representation of `Y_ν`** (DLMF 10.9.5): for `re ν > -1/2` and `re z > 0`,
`Y_ν(z) = 2(z/2)^ν/(√π Γ(ν+½)) (∫₀¹ (1-t²)^{ν-½} sin(zt) dt - ∫₀^∞ e^{-zt} (1+t²)^{ν-½} dt)`. -/
@[dlmf 10.9.E5]
theorem besselY_eq_integral {ν z : ℂ} (hν : -1 / 2 < ν.re) (hz : 0 < z.re) :
    besselY ν z = 2 * (z / 2) ^ ν / (Real.sqrt π * Gamma (ν + 1 / 2)) *
      ((∫ t : ℝ in (0 : ℝ)..1, (1 - (t : ℂ) ^ 2) ^ (ν - 1 / 2) * sin (z * t)) -
        ∫ t in Ioi (0 : ℝ), exp (-z * t) * (1 + (t : ℂ) ^ 2) ^ (ν - 1 / 2)) := by
  have hK := struveK_eq_integral ν hz
  have hH := DLMF.Struve.struveH_eq_poisson hν (fun h : z = 0 => by simp [h] at hz)
  unfold DLMF.Struve.struveK at hK
  rw [mul_sub, ← hH, ← hK]
  ring

end DLMF.Bessel
