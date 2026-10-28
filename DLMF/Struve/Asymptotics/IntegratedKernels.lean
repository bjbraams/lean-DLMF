/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Struve.Asymptotics.Watson

/-!
# Integral kernels for integrated Struve expansions

Holomorphic primitives, Frullani integrals and Gamma constants prepare the integrated Struve
asymptotics.

Source references and common attribution are retained in
`DLMF.Struve.Asymptotics`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF

open scoped Real Topology Nat

namespace DLMF.Struve

open DLMF.Bessel DLMF.Airy

section StruvePrimitive

open scoped Interval

/-- `‖𝐊₀(w)‖ ≤ M (cos α)^{-1/2} (re (w e^{iα}))^{-1/2}` from the rotated Laplace integral. -/
theorem struvePrim_norm_struveK_zero_le {α : ℝ} (hα : |α| < π / 2) {w : ℂ}
    (hw : 0 < (w * exp (α * I)).re) :
    ‖struveK 0 w‖ ≤ ‖(2 : ℂ) / (Real.sqrt π * Gamma (1 / 2))‖ *
      (Real.cos α ^ (-(1 / 2 : ℝ)) * ((1 / (w * exp (α * I)).re) ^ (1 / 2 : ℝ) *
        Real.Gamma (1 / 2))) := by
  set ω := exp (α * I) with hω
  set a := (w * ω).re with ha
  have hcα : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [neg_abs_le α], by linarith [le_abs_self α]⟩
  rw [struveK_eq_struveKRotated 0 hα hw, struveKRotated, struveKRotIntegral]
  simp only [cpow_zero, mul_one, zero_add, zero_sub]
  rw [norm_mul, norm_mul, ← hω, norm_exp_ofReal_mul_I, one_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hbound : ∀ r ∈ Ioi (0 : ℝ), ‖struveKKernel (-(1 / 2)) w (r * ω)‖ ≤
      Real.cos α ^ (-(1 / 2 : ℝ)) * (r ^ ((1 / 2 : ℝ) - 1) * Real.exp (-(a * r))) := by
    intro r hr
    have hr : (0 : ℝ) < r := hr
    rw [struveKKernel, norm_mul, norm_exp,
      show (-(1 / 2) : ℂ) = ((-(1 / 2) : ℝ) : ℂ) by push_cast; ring, norm_cpow_real]
    have hre : (-w * (r * ω)).re = -(a * r) := by
      rw [ha, show -w * (r * ω) = -((r : ℂ) * (w * ω)) by ring, neg_re, re_ofReal_mul]; ring
    rw [hre, ← mul_assoc, mul_comm (Real.exp _)]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    have hlow : Real.cos α * r ≤ ‖1 + ((r : ℂ) * ω) ^ 2‖ := by
      refine le_trans ?_ (cos_mul_le_norm_one_add_sq r α)
      have : r ≤ 1 + r ^ 2 := by nlinarith [sq_nonneg (r - 1)]
      exact mul_le_mul_of_nonneg_left this hcα.le
    calc ‖1 + ((r : ℂ) * ω) ^ 2‖ ^ (-(1 / 2) : ℝ) ≤ (Real.cos α * r) ^ (-(1 / 2) : ℝ) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hlow (by norm_num)
      _ = _ := by rw [Real.mul_rpow hcα.le hr.le]; norm_num
  have hint : IntegrableOn (fun r : ℝ => Real.cos α ^ (-(1 / 2 : ℝ)) *
      (r ^ ((1 / 2 : ℝ) - 1) * Real.exp (-(a * r)))) (Ioi 0) := by
    have := (integrableOn_exp_neg_mul_mul_rpow_sub_one (s := 1 / 2) (by norm_num) hw).const_mul
      (Real.cos α ^ (-(1 / 2 : ℝ)))
    refine IntegrableOn.congr_fun this (fun r _ => ?_) measurableSet_Ioi
    simp only [neg_mul]; ring
  refine (norm_integral_le_of_norm_le hint ((ae_restrict_iff' measurableSet_Ioi).mpr
    (Eventually.of_forall hbound))).trans (le_of_eq ?_)
  rw [integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi (by norm_num) hw]

/-- Positive real multiples stay in the slit plane. -/
theorem struvePrim_ofReal_mul_mem {t : ℝ} (ht : 0 < t) {z : ℂ} (hz : z ∈ slitPlane) :
    (t : ℂ) * z ∈ slitPlane := by
  rw [mem_slitPlane_iff] at hz ⊢
  rw [re_ofReal_mul, im_ofReal_mul]
  rcases hz with h | h
  · left; positivity
  · right; exact mul_ne_zero ht.ne' h

/-- A local bound `‖𝐊₀(t y)‖ ≤ C t^{-1/2}`, uniform for `y` near a point of the slit plane. -/
theorem struvePrim_local_bound {z₀ : ℂ} (hz₀ : z₀ ∈ slitPlane) :
    ∃ V ∈ 𝓝 z₀, ∃ C : ℝ, ∀ y ∈ V, ∀ t : ℝ, 0 < t → ‖struveK 0 ((t : ℂ) * y)‖ ≤ C * t ^ (-(1 / 2 : ℝ)) := by
  set α : ℝ := -(arg z₀ / 2) with hα
  have hz0 : z₀ ≠ 0 := slitPlane_ne_zero hz₀
  have harg : |arg z₀| < π := by
    rw [abs_lt]; refine ⟨neg_pi_lt_arg _, lt_of_le_of_ne (arg_le_pi _) ?_⟩
    intro h; rw [mem_slitPlane_iff_arg] at hz₀; exact hz₀.1 h
  have hαπ : |α| < π / 2 := by rw [hα, abs_neg, abs_div, abs_two]; linarith
  set ω := exp (α * I) with hω
  have hre0 : 0 < (z₀ * ω).re := by
    rw [hω, DLMF.Confluent.re_mul_exp_mul_I, hα]
    refine mul_pos (norm_pos_iff.mpr hz0) (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩) <;>
      linarith [abs_lt.mp harg]
  set c := (z₀ * ω).re / 2 with hc
  have hc0 : 0 < c := by positivity
  refine ⟨{y | c < (y * ω).re}, (isOpen_lt continuous_const (by fun_prop)).mem_nhds
    (by show c < (z₀ * ω).re; linarith), ?_⟩
  set M := ‖(2 : ℂ) / (Real.sqrt π * Gamma (1 / 2))‖ * (Real.cos α ^ (-(1 / 2 : ℝ)) *
    Real.Gamma (1 / 2))
  refine ⟨M * (1 / c) ^ (1 / 2 : ℝ), fun y hy t ht => ?_⟩
  have hy' : c < (y * ω).re := hy
  have hty : 0 < ((t : ℂ) * y * ω).re := by
    rw [mul_assoc, re_ofReal_mul]; exact mul_pos ht (hc0.trans hy')
  refine (struvePrim_norm_struveK_zero_le hαπ hty).trans ?_
  rw [mul_assoc, re_ofReal_mul]
  have hM0 : 0 ≤ ‖(2 : ℂ) / (Real.sqrt π * Gamma (1 / 2))‖ * Real.cos α ^ (-(1 / 2 : ℝ)) * Real.Gamma (1 / 2) := by
    have := Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 2)
    have hcα : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [neg_abs_le α], by linarith [le_abs_self α]⟩
    have := Real.rpow_pos_of_pos hcα (-(1 / 2 : ℝ))
    positivity
  have hb : 0 < (y * ω).re := hc0.trans hy'
  have hle : (1 / (t * (y * ω).re)) ^ (1 / 2 : ℝ) ≤ (1 / c) ^ (1 / 2 : ℝ) * t ^ (-(1 / 2 : ℝ)) := by
    rw [Real.rpow_neg ht.le, ← Real.inv_rpow ht.le, ← Real.mul_rpow (by positivity) (by positivity)]
    refine Real.rpow_le_rpow (by positivity) ?_ (by norm_num)
    have := one_div_le_one_div_of_le (mul_pos ht hc0) (mul_le_mul_of_nonneg_left hy'.le ht.le)
    refine this.trans (le_of_eq ?_)
    field_simp
  calc ‖(2 : ℂ) / (Real.sqrt π * Gamma (1 / 2))‖ * (Real.cos α ^ (-(1 / 2 : ℝ)) *
        ((1 / (t * (y * ω).re)) ^ (1 / 2 : ℝ) * Real.Gamma (1 / 2)))
      = (‖(2 : ℂ) / (Real.sqrt π * Gamma (1 / 2))‖ * Real.cos α ^ (-(1 / 2 : ℝ)) *
          Real.Gamma (1 / 2)) * (1 / (t * (y * ω).re)) ^ (1 / 2 : ℝ) := by ring
    _ ≤ (‖(2 : ℂ) / (Real.sqrt π * Gamma (1 / 2))‖ * Real.cos α ^ (-(1 / 2 : ℝ)) *
          Real.Gamma (1 / 2)) * ((1 / c) ^ (1 / 2 : ℝ) * t ^ (-(1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left hle hM0
    _ = _ := by simp only [M]; ring

/-- `𝐊₀` is continuous on the slit plane. -/
theorem struvePrim_continuousOn : ContinuousOn (struveK 0) slitPlane :=
  (DLMF.Bessel.analyticOnNhd_struveK 0).continuousOn

/-- `t ↦ 𝐊₀(t z)` is continuous on `(0, ∞)` for `z` in the slit plane. -/
theorem struvePrim_continuousOn_ray {z : ℂ} (hz : z ∈ slitPlane) :
    ContinuousOn (fun t : ℝ => struveK 0 ((t : ℂ) * z)) (Ioi 0) :=
  struvePrim_continuousOn.comp (by fun_prop) fun t ht => struvePrim_ofReal_mul_mem ht hz

/-- `t ↦ 𝐊₀(t z)` is interval integrable on `[0, 1]`. -/
theorem struvePrim_intervalIntegrable {z : ℂ} (hz : z ∈ slitPlane) :
    IntervalIntegrable (fun t : ℝ => struveK 0 ((t : ℂ) * z)) volume 0 1 := by
  obtain ⟨V, hV, C, hC⟩ := struvePrim_local_bound hz
  have hg : IntervalIntegrable (fun t : ℝ => C * t ^ (-(1 / 2 : ℝ))) volume 0 1 :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul C
  have hI : Ι (0 : ℝ) 1 = Ioc 0 1 := uIoc_of_le zero_le_one
  refine hg.mono_fun' ?_ ?_
  · rw [hI]
    exact ((struvePrim_continuousOn_ray hz).mono Ioc_subset_Ioi_self).aestronglyMeasurable
      measurableSet_Ioc
  · rw [hI]
    exact (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t ht =>
      hC z (mem_of_mem_nhds hV) t ht.1)

/-- The segment DLMF.primitive of `𝐊₀` is holomorphic on the slit plane. -/
theorem struvePrim_differentiableOn :
    DifferentiableOn ℂ (fun w : ℂ => ∫ t in (0 : ℝ)..1, struveK 0 ((t : ℂ) * w)) slitPlane := by
  have hI : Ι (0 : ℝ) 1 = Ioc 0 1 := uIoc_of_le zero_le_one
  refine Complex.differentiableOn_intervalIntegral_of_locally_dominated
    (Φ := fun w (t : ℝ) => struveK 0 ((t : ℂ) * w)) isOpen_slitPlane 0 1 ?_ ?_ ?_
  · intro x hx
    rw [hI]
    exact ((struvePrim_continuousOn_ray hx).mono Ioc_subset_Ioi_self).aestronglyMeasurable
      measurableSet_Ioc
  · rw [hI]
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t ht => ?_)
    exact (DLMF.Bessel.analyticOnNhd_struveK 0).differentiableOn.comp (by fun_prop)
      fun w hw => struvePrim_ofReal_mul_mem ht.1 hw
  · intro x hx
    obtain ⟨V, hV, C, hC⟩ := struvePrim_local_bound hx
    refine ⟨V, hV, fun t => C * t ^ (-(1 / 2 : ℝ)), ?_, ?_⟩
    · have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1)
        (by norm_num : (-1 : ℝ) < -(1 / 2))).const_mul C
      exact (intervalIntegrable_iff.mp this)
    · rw [hI]
      exact (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t ht y hy =>
        hC y hy t ht.1)

/-- The DLMF.primitive `∫₀^z 𝐊₀` is a holomorphic antiderivative of `𝐊₀` on the slit plane. -/
theorem struvePrim_hasDerivAt {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (DLMF.primitive (struveK 0)) (struveK 0 z) z := by
  have hP : DLMF.primitive (struveK 0) = fun w : ℂ => w * ∫ t in (0 : ℝ)..1, struveK 0 ((t : ℂ) * w) := by
    funext w; simp [DLMF.primitive, segmentIntegral]
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have hPd : DifferentiableAt ℂ (DLMF.primitive (struveK 0)) z := by
    rw [hP]
    exact differentiableAt_id.mul (struvePrim_differentiableOn.differentiableAt
      (isOpen_slitPlane.mem_nhds hz))
  set F : ℝ → ℂ := fun u => struveK 0 ((u : ℂ) * z) * z with hF
  have hFc : ContinuousOn F (Ioi 0) := (struvePrim_continuousOn_ray hz).mul continuousOn_const
  have hFi : IntervalIntegrable F volume 0 1 := (struvePrim_intervalIntegrable hz).mul_const z
  have hd1 : HasDerivAt (fun s => ∫ u in (0 : ℝ)..s, F u) (F 1) 1 :=
    intervalIntegral.integral_hasDerivAt_right hFi
      (hFc.stronglyMeasurableAtFilter isOpen_Ioi 1 (by norm_num : (1 : ℝ) ∈ Ioi 0))
      (hFc.continuousAt (Ioi_mem_nhds one_pos))
  have heq : (fun s : ℝ => ∫ u in (0 : ℝ)..s, F u) =ᶠ[𝓝 1]
      fun s : ℝ => DLMF.primitive (struveK 0) ((s : ℂ) * z) := by
    filter_upwards [Ioi_mem_nhds one_pos] with s hs
    have hs0 : (s : ℝ) ≠ 0 := (show (0 : ℝ) < s from hs).ne'
    have h := intervalIntegral.integral_comp_mul_left (a := 0) (b := 1) F hs0
    rw [mul_zero, mul_one] at h
    rw [eq_inv_smul_iff₀ hs0] at h
    rw [← h, hP]
    simp only [hF, real_smul]
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    push_cast; ring_nf
  have hd2 : HasDerivAt (fun s : ℝ => DLMF.primitive (struveK 0) ((s : ℂ) * z))
      (deriv (DLMF.primitive (struveK 0)) z * z) 1 := by
    have h1 : HasDerivAt (fun w : ℂ => DLMF.primitive (struveK 0) (w * z))
        (deriv (DLMF.primitive (struveK 0)) z * z) ((1 : ℝ) : ℂ) := by
      have hPd' : HasDerivAt (DLMF.primitive (struveK 0)) (deriv (DLMF.primitive (struveK 0)) z)
          (((1 : ℝ) : ℂ) * z) := by rw [ofReal_one, one_mul]; exact hPd.hasDerivAt
      have := hPd'.comp ((1 : ℝ) : ℂ) (by
        simpa using (hasDerivAt_id ((1 : ℝ) : ℂ)).mul_const z :
          HasDerivAt (fun w : ℂ => w * z) z ((1 : ℝ) : ℂ))
      exact this
    exact h1.comp_ofReal
  have hu := (hd1.congr_of_eventuallyEq heq.symm).unique hd2
  simp only [hF, ofReal_one, one_mul] at hu
  have : deriv (DLMF.primitive (struveK 0)) z = struveK 0 z := mul_right_cancel₀ hz0 hu.symm
  rw [← this]
  exact hPd.hasDerivAt

/-- `∫₀^∞ ((1+τ²)^{-1/2} - (1+τ)⁻¹)/τ dτ = log 2`, with integrability. -/
theorem struvePrim_integral_log_two :
    IntegrableOn (fun τ : ℝ => (1 / Real.sqrt (1 + τ ^ 2) - 1 / (1 + τ)) / τ) (Ioi 0) ∧
    ∫ τ in Ioi (0 : ℝ), (1 / Real.sqrt (1 + τ ^ 2) - 1 / (1 + τ)) / τ = Real.log 2 := by
  set F : ℝ → ℝ := fun τ => Real.log (1 + τ) - Real.log (1 + Real.sqrt (1 + τ ^ 2)) with hF
  have hS : ∀ τ : ℝ, 0 < Real.sqrt (1 + τ ^ 2) := fun τ => Real.sqrt_pos.2 (by positivity)
  have hSS : ∀ τ : ℝ, Real.sqrt (1 + τ ^ 2) ^ 2 = 1 + τ ^ 2 := fun τ =>
    Real.sq_sqrt (by positivity)
  have hderiv : ∀ τ ∈ Ioi (0 : ℝ), HasDerivAt F
      ((1 / Real.sqrt (1 + τ ^ 2) - 1 / (1 + τ)) / τ) τ := by
    intro τ hτ
    have hτ0 : (0 : ℝ) < τ := hτ
    have h1 : HasDerivAt (fun τ : ℝ => Real.log (1 + τ)) (1 / (1 + τ)) τ := by
      have := ((hasDerivAt_id τ).const_add 1).log (by simp; linarith)
      simpa using this
    have hsq : HasDerivAt (fun τ : ℝ => Real.sqrt (1 + τ ^ 2))
        (τ / Real.sqrt (1 + τ ^ 2)) τ := by
      have := ((hasDerivAt_pow 2 τ).const_add 1).sqrt (by positivity)
      convert this using 1; push_cast; ring
    have h2 : HasDerivAt (fun τ : ℝ => Real.log (1 + Real.sqrt (1 + τ ^ 2)))
        (τ / Real.sqrt (1 + τ ^ 2) / (1 + Real.sqrt (1 + τ ^ 2))) τ := by
      have := (hsq.const_add 1).log (by have := hS τ; linarith)
      convert this using 1
    convert h1.sub h2 using 1
    have := hS τ
    have h3 := hSS τ
    field_simp
    linear_combination (-(1 + τ) * τ + τ ^ 2 - 1) * h3
  have hcont : ContinuousWithinAt F (Ici 0) 0 := by
    have : ContinuousAt F 0 := by
      refine ContinuousAt.sub ?_ ?_
      · exact (continuousAt_const.add continuousAt_id).log (by norm_num)
      · refine (continuousAt_const.add
          ((continuousAt_const.add (continuousAt_id.pow 2)).sqrt)).log ?_
        norm_num
    exact this.continuousWithinAt
  have hpos : ∀ τ ∈ Ioi (0 : ℝ), 0 ≤ (1 / Real.sqrt (1 + τ ^ 2) - 1 / (1 + τ)) / τ := by
    intro τ hτ
    have hτ0 : (0 : ℝ) < τ := hτ
    refine div_nonneg (sub_nonneg.2 ?_) hτ0.le
    refine one_div_le_one_div_of_le (hS τ) ?_
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have hlim : Tendsto F atTop (𝓝 0) := by
    set h : ℝ → ℝ := fun u => Real.log ((u + 1) / (u + Real.sqrt (u ^ 2 + 1))) with hh
    have hhc : ContinuousAt h 0 := by
      refine ContinuousAt.log ?_ (by norm_num)
      refine (continuousAt_id.add continuousAt_const).div
        (continuousAt_id.add ((continuousAt_id.pow 2).add continuousAt_const).sqrt) (by norm_num)
    have h0 : h 0 = 0 := by simp [hh]
    have ht := (hhc.tendsto.comp tendsto_inv_atTop_zero)
    rw [h0] at ht
    refine ht.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with τ hτ
    simp only [Function.comp, hh, hF]
    have hS1 : 0 < 1 + Real.sqrt (1 + τ ^ 2) := by have := hS τ; linarith
    rw [← Real.log_div (by linarith) hS1.ne']
    congr 1
    have hq : Real.sqrt (τ⁻¹ ^ 2 + 1) = Real.sqrt (1 + τ ^ 2) / τ := by
      rw [show τ⁻¹ ^ 2 + 1 = (1 + τ ^ 2) / τ ^ 2 by field_simp,
        Real.sqrt_div (by positivity), Real.sqrt_sq hτ.le]
    rw [hq]
    field_simp
  have hF0 : F 0 = -Real.log 2 := by
    simp only [hF]; norm_num
  refine ⟨integrableOn_Ioi_deriv_of_nonneg hcont hderiv hpos hlim, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg hcont hderiv hpos hlim, hF0]
  ring

/-- `∫₀^∞ ((1+τ)⁻¹ - (1+xτ)⁻¹)/τ dτ = log x` for `x > 0`, with integrability. -/
theorem struvePrim_integral_log {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun τ : ℝ => (1 / (1 + τ) - 1 / (1 + x * τ)) / τ) (Ioi 0) ∧
    ∫ τ in Ioi (0 : ℝ), (1 / (1 + τ) - 1 / (1 + x * τ)) / τ = Real.log x := by
  set G : ℝ → ℝ := fun τ => Real.log (1 + x * τ) - Real.log (1 + τ) with hG
  have hderiv : ∀ τ ∈ Ioi (0 : ℝ), HasDerivAt G ((1 / (1 + τ) - 1 / (1 + x * τ)) / τ) τ := by
    intro τ hτ
    have hτ0 : (0 : ℝ) < τ := hτ
    have h1 : HasDerivAt (fun τ : ℝ => Real.log (1 + x * τ)) (x / (1 + x * τ)) τ := by
      have hp : (1 : ℝ) + x * id τ ≠ 0 := by simp only [id_eq]; positivity
      have := (((hasDerivAt_id τ).const_mul x).const_add 1).log hp
      simpa using this
    have h2 : HasDerivAt (fun τ : ℝ => Real.log (1 + τ)) (1 / (1 + τ)) τ := by
      have := ((hasDerivAt_id τ).const_add 1).log (by simp; linarith)
      simpa using this
    convert h1.sub h2 using 1
    have : 0 < 1 + x * τ := by positivity
    field_simp
    ring
  have hcont : ContinuousWithinAt G (Ici 0) 0 := by
    have : ContinuousAt G 0 := by
      refine ContinuousAt.sub ?_ ?_
      · exact (continuousAt_const.add (continuousAt_id.const_mul x)).log (by norm_num)
      · exact (continuousAt_const.add continuousAt_id).log (by norm_num)
    exact this.continuousWithinAt
  have hlim : Tendsto G atTop (𝓝 (Real.log x)) := by
    set h : ℝ → ℝ := fun u => Real.log ((u + x) / (u + 1)) with hh
    have hhc : ContinuousAt h 0 := by
      refine ContinuousAt.log ?_ (by simp; exact hx.ne')
      exact (continuousAt_id.add continuousAt_const).div (continuousAt_id.add continuousAt_const)
        (by norm_num)
    have h0 : h 0 = Real.log x := by simp [hh]
    have ht := (hhc.tendsto.comp tendsto_inv_atTop_zero)
    rw [h0] at ht
    refine ht.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with τ hτ
    simp only [Function.comp, hh, hG]
    rw [← Real.log_div (by positivity) (by positivity)]
    congr 1
    field_simp
  have hint : IntegrableOn (fun τ : ℝ => (1 / (1 + τ) - 1 / (1 + x * τ)) / τ) (Ioi 0) := by
    refine Integrable.mono' ((integrable_inv_one_add_sq.const_mul (|x - 1| * (1 + 1 / x))).integrableOn)
      ((ContinuousOn.div (ContinuousOn.sub
        (continuousOn_const.div (by fun_prop) fun τ (hτ : 0 < τ) => by positivity)
        (continuousOn_const.div (by fun_prop) fun τ (hτ : 0 < τ) => by positivity)) continuousOn_id
        fun τ hτ => (ne_of_gt (show (0 : ℝ) < τ from hτ))).aestronglyMeasurable measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun τ hτ => ?_)
    have hτ0 : (0 : ℝ) < τ := hτ
    have e : (1 / (1 + τ) - 1 / (1 + x * τ)) / τ = (x - 1) / ((1 + τ) * (1 + x * τ)) := by
      have : 0 < 1 + x * τ := by positivity
      field_simp; ring
    rw [e, Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : 0 < (1 + τ) * (1 + x * τ)),
      div_eq_mul_inv |x - 1|, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [← one_div, ← one_div, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0 < 1 / x := by positivity
    have hx1 : (1 + 1 / x) * x = x + 1 := by field_simp
    nlinarith [mul_pos hτ0 hτ0, mul_pos this hτ0, mul_pos hx hτ0]
  refine ⟨hint, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim]
  simp [hG]

/-- `∫₀^∞ ((1+xτ)⁻¹ - e^{-xτ})/τ dτ = γ` for `x > 0`, with integrability. -/
theorem struvePrim_integral_euler {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun τ : ℝ => (1 / (1 + x * τ) - Real.exp (-(x * τ))) / τ) (Ioi 0) ∧
    ∫ τ in Ioi (0 : ℝ), (1 / (1 + x * τ) - Real.exp (-(x * τ))) / τ =
      Real.eulerMascheroniConstant := by
  set g : ℝ → ℝ := fun t => (1 / (1 + t) - Real.exp (-t)) / t with hg
  have hpt : ∀ τ : ℝ, (1 / (1 + x * τ) - Real.exp (-(x * τ))) / τ = x * g (x * τ) := by
    intro τ
    simp only [hg]
    rcases eq_or_ne τ 0 with h | h
    · simp [h]
    · field_simp
  have hgi : IntegrableOn (fun τ => g (x * τ)) (Ioi 0) := by
    rw [integrableOn_Ioi_comp_mul_left_iff g 0 hx, mul_zero]
    exact DLMF.Gamma.integrableOn_eulerIntegrand
  refine ⟨?_, ?_⟩
  · simp_rw [hpt]; exact hgi.const_mul x
  · simp_rw [hpt]
    rw [integral_const_mul, integral_comp_mul_left_Ioi g 0 hx, mul_zero, smul_eq_mul,
      ← mul_assoc, mul_inv_cancel₀ hx.ne', one_mul, DLMF.Gamma.eulerMascheroni_eq_integral_recip_one_add]

/-- The combined Frullani-type integral: `∫₀^∞ ((1+τ²)^{-1/2} - e^{-xτ})/τ dτ = log 2x + γ`. -/
theorem struvePrim_integral_log_two_mul {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun τ : ℝ => (1 / Real.sqrt (1 + τ ^ 2) - Real.exp (-(x * τ))) / τ) (Ioi 0) ∧
    ∫ τ in Ioi (0 : ℝ), (1 / Real.sqrt (1 + τ ^ 2) - Real.exp (-(x * τ))) / τ =
      Real.log (2 * x) + Real.eulerMascheroniConstant := by
  obtain ⟨i1, e1⟩ := struvePrim_integral_log_two
  obtain ⟨i2, e2⟩ := struvePrim_integral_log hx
  obtain ⟨i3, e3⟩ := struvePrim_integral_euler hx
  have hpt : (fun τ : ℝ => (1 / Real.sqrt (1 + τ ^ 2) - Real.exp (-(x * τ))) / τ) =
      fun τ => (1 / Real.sqrt (1 + τ ^ 2) - 1 / (1 + τ)) / τ +
        (1 / (1 + τ) - 1 / (1 + x * τ)) / τ + (1 / (1 + x * τ) - Real.exp (-(x * τ))) / τ := by
    funext τ; ring
  rw [hpt]
  refine ⟨(i1.add i2).add i3, ?_⟩
  have h12 := integral_add i1 i2
  have h123 := integral_add (i1.add i2) i3
  simp only [Pi.add_apply] at h12 h123
  rw [h123, h12, e1, e2, e3, Real.log_mul (by norm_num) hx.ne']

/-- The real Laplace form of `𝐊₀` on the positive axis (DLMF 11.5.2 with `ν = 0`). -/
theorem struvePrim_struveK_zero_ofReal {t : ℝ} (ht : 0 < t) :
    struveK 0 t = (((2 / π) * ∫ τ in Ioi (0 : ℝ),
      Real.exp (-(t * τ)) * (1 / Real.sqrt (1 + τ ^ 2)) : ℝ) : ℂ) := by
  rw [DLMF.Bessel.struveK_eq_integral 0 (by simpa using ht)]
  have hG : Gamma (0 + 1 / 2) = ((Real.sqrt π : ℝ) : ℂ) := by
    rw [zero_add, Complex.Gamma_one_half_eq, Real.sqrt_eq_rpow, ofReal_cpow Real.pi_pos.le]
    push_cast; rfl
  have hint : ∫ τ in Ioi (0 : ℝ), exp (-(t : ℂ) * τ) * (1 + (τ : ℂ) ^ 2) ^ ((0 : ℂ) - 1 / 2) =
      ((∫ τ in Ioi (0 : ℝ), Real.exp (-(t * τ)) * (1 / Real.sqrt (1 + τ ^ 2)) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun τ _ => ?_
    have h1 : (1 + (τ : ℂ) ^ 2) ^ ((0 : ℂ) - 1 / 2) = (((1 + τ ^ 2) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) := by
      rw [ofReal_cpow (by positivity)]; push_cast; ring_nf
    rw [h1, Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, ofReal_mul, ofReal_exp]
    push_cast; ring_nf
  rw [hint, hG, cpow_zero]
  have hs : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.2 (Real.sqrt_pos.2 Real.pi_pos).ne'
  have hss : ((Real.sqrt π : ℝ) : ℂ) * (Real.sqrt π : ℝ) = (π : ℂ) := by
    rw [← ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
  push_cast
  rw [mul_one, show (2 : ℂ) / (↑√π * ↑√π) = 2 / π from by rw [hss] ]

/-- `∫₀^x e^{-uτ} du = (1 - e^{-xτ})/τ` for `τ ≠ 0`. -/
theorem struvePrim_integral_exp {τ : ℝ} (hτ : τ ≠ 0) (x : ℝ) :
    ∫ u in (0 : ℝ)..x, Real.exp (-(u * τ)) = (1 - Real.exp (-(x * τ))) / τ := by
  have h : ∀ u ∈ [[(0 : ℝ), x]], HasDerivAt (fun u : ℝ => -Real.exp (-(u * τ)) / τ)
      (Real.exp (-(u * τ))) u := by
    intro u _
    have h0 : HasDerivAt (fun u : ℝ => -(u * τ)) (-τ) u := by
      exact (hasDerivAt_mul_const τ).neg
    have := (h0.exp.neg).div_const τ
    convert this using 1
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h
    ((by fun_prop : Continuous fun u : ℝ => Real.exp (-(u * τ))).intervalIntegrable _ _)]
  simp only [zero_mul, neg_zero, Real.exp_zero]
  ring

/-- Fubini for the DLMF.primitive: `∫₀^x 𝐊₀ = (2/π) ∫₀^∞ (1+τ²)^{-1/2} (1 - e^{-xτ})/τ dτ`. -/
theorem struvePrim_primitive_ofReal {x : ℝ} (hx : 0 < x) :
    DLMF.primitive (struveK 0) x = (((2 / π) * ∫ τ in Ioi (0 : ℝ),
      (1 / Real.sqrt (1 + τ ^ 2)) * ((1 - Real.exp (-(x * τ))) / τ) : ℝ) : ℂ) := by
  set g : ℝ → ℝ := fun τ => 1 / Real.sqrt (1 + τ ^ 2) with hg
  set k : ℝ → ℝ := fun u => (2 / π) * ∫ τ in Ioi (0 : ℝ), Real.exp (-(u * τ)) * g τ with hk
  -- the DLMF.primitive as a real interval integral
  have hP : DLMF.primitive (struveK 0) x = ((∫ u in (0 : ℝ)..x, k u : ℝ) : ℂ) := by
    simp only [DLMF.primitive, segmentIntegral, sub_zero, zero_add]
    have h1 : ∫ t in (0 : ℝ)..1, struveK 0 (↑t * ↑x) = ∫ t in (0 : ℝ)..1, ((k (x * t) : ℝ) : ℂ) := by
      refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun t ht => ?_)
      rw [uIoc_of_le zero_le_one] at ht
      rw [← ofReal_mul, mul_comm t x, struvePrim_struveK_zero_ofReal (by nlinarith [ht.1])]
    rw [h1, intervalIntegral.integral_ofReal]
    have h2 := intervalIntegral.integral_comp_mul_left (a := 0) (b := 1) k hx.ne'
    rw [mul_zero, mul_one, smul_eq_mul] at h2
    rw [h2, ← ofReal_mul, mul_inv_cancel_left₀ hx.ne']
  rw [hP]
  congr 1
  -- Fubini
  set f : ℝ → ℝ → ℝ := fun u τ => Real.exp (-(u * τ)) * g τ with hf
  have hg0 : ∀ τ, 0 ≤ g τ := fun τ => by simp only [hg]; positivity
  have hgle : ∀ τ, g τ ≤ 1 := fun τ => by
    simp only [hg]; rw [div_le_one (Real.sqrt_pos.2 (by positivity))]
    exact Real.one_le_sqrt.2 (by nlinarith)
  have hinner : ∀ τ ∈ Ioi (0 : ℝ), ∫ u in Ioc 0 x, f u τ = g τ * ((1 - Real.exp (-(x * τ))) / τ) := by
    intro τ hτ
    rw [← intervalIntegral.integral_of_le hx.le]
    simp only [hf]
    rw [intervalIntegral.integral_mul_const, struvePrim_integral_exp (ne_of_gt hτ), mul_comm]
  have hbd : ∀ τ ∈ Ioi (0 : ℝ), g τ * ((1 - Real.exp (-(x * τ))) / τ) ≤ 2 * (x + 1) * (1 + τ ^ 2)⁻¹ := by
    intro τ hτ
    have hτ0 : (0 : ℝ) < τ := hτ
    have he : 0 < Real.exp (-(x * τ)) := Real.exp_pos _
    have he1 : 1 - Real.exp (-(x * τ)) ≤ x * τ := by
      have := Real.add_one_le_exp (-(x * τ)); linarith
    rw [← div_eq_mul_inv]
    have hgτ := hgle τ
    have hg0τ := hg0 τ
    rcases le_or_gt τ 1 with h1 | h1
    · have hq : (1 - Real.exp (-(x * τ))) / τ ≤ x := by
        rw [div_le_iff₀ hτ0]; linarith
      have hq0 : 0 ≤ (1 - Real.exp (-(x * τ))) / τ := by
        have : Real.exp (-(x * τ)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
        exact div_nonneg (by linarith) hτ0.le
      calc g τ * ((1 - Real.exp (-(x * τ))) / τ) ≤ 1 * x := mul_le_mul hgτ hq hq0 zero_le_one
        _ ≤ 2 * (x + 1) / (1 + τ ^ 2) := by
          rw [le_div_iff₀ (by positivity)]
          nlinarith [mul_le_mul h1 h1 hτ0.le zero_le_one]
    · have hq : (1 - Real.exp (-(x * τ))) / τ ≤ 1 / τ := by
        gcongr; linarith
      have hgτ' : g τ ≤ 1 / τ := by
        simp only [hg]
        exact one_div_le_one_div_of_le hτ0 (Real.le_sqrt_of_sq_le (by nlinarith))
      have hq0 : 0 ≤ (1 - Real.exp (-(x * τ))) / τ := by
        have : Real.exp (-(x * τ)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
        exact div_nonneg (by linarith) hτ0.le
      calc g τ * ((1 - Real.exp (-(x * τ))) / τ) ≤ (1 / τ) * (1 / τ) :=
            mul_le_mul hgτ' hq hq0 (by positivity)
        _ ≤ 2 * (x + 1) / (1 + τ ^ 2) := by
          rw [div_mul_div_comm, one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
  have hgc : Continuous g := by
    simp only [hg]
    exact continuous_const.div (by fun_prop) fun τ => (Real.sqrt_pos.2 (by positivity)).ne'
  have hfc : Continuous (Function.uncurry f) := by
    simp only [hf]
    exact ((by fun_prop : Continuous fun p : ℝ × ℝ => Real.exp (-(p.1 * p.2)))).mul
      (hgc.comp continuous_snd)
  have hval : IntegrableOn (fun τ => g τ * ((1 - Real.exp (-(x * τ))) / τ)) (Ioi 0) := by
    refine Integrable.mono' ((integrable_inv_one_add_sq.const_mul (2 * (x + 1))).integrableOn)
      ((ContinuousOn.mul hgc.continuousOn (ContinuousOn.div (by fun_prop) continuousOn_id
        fun τ hτ => ne_of_gt (show (0 : ℝ) < τ from hτ))).aestronglyMeasurable measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun τ hτ => ?_)
    have hτ0 : (0 : ℝ) < τ := hτ
    have : Real.exp (-(x * τ)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hg0 τ) (div_nonneg (by linarith) hτ0.le))]
    exact hbd τ hτ
  have hint : Integrable (Function.uncurry f)
      ((volume.restrict (Ioc 0 x)).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    rw [integrable_prod_iff' hfc.aestronglyMeasurable]
    refine ⟨Eventually.of_forall fun τ => ?_, ?_⟩
    · exact (hfc.comp (by fun_prop : Continuous fun u : ℝ => (u, τ))).integrableOn_Ioc
    · refine hval.congr ((ae_restrict_iff' measurableSet_Ioi).mpr
        (Eventually.of_forall fun τ hτ => ?_))
      show g τ * ((1 - Real.exp (-(x * τ))) / τ) = ∫ u in Ioc 0 x, ‖Function.uncurry f (u, τ)‖
      rw [← hinner τ hτ]
      refine setIntegral_congr_fun measurableSet_Ioc fun u _ => ?_
      simp only [Function.uncurry_apply_pair, hf]
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (hg0 τ))]
  rw [intervalIntegral.integral_of_le hx.le]
  simp only [hk]
  rw [integral_const_mul]
  congr 1
  have hsw := integral_integral_swap hint
  simp only [hf] at hsw
  rw [hsw]
  refine setIntegral_congr_fun measurableSet_Ioi fun τ hτ => ?_
  have := hinner τ hτ
  simp only [hf] at this
  rw [this]

/-- For `τ > 0`, `0 ≤ (1 - (1+τ²)^{-1/2})/τ ≤ 1`. -/
theorem struvePrim_quot_bounds {τ : ℝ} (hτ0 : 0 < τ) :
    0 ≤ (1 - 1 / Real.sqrt (1 + τ ^ 2)) / τ ∧ (1 - 1 / Real.sqrt (1 + τ ^ 2)) / τ ≤ 1 := by
  have hS : 0 < Real.sqrt (1 + τ ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hg1 : 1 / Real.sqrt (1 + τ ^ 2) ≤ 1 := by
    rw [div_le_one hS]; exact Real.one_le_sqrt.2 (by nlinarith)
  refine ⟨div_nonneg (by linarith) hτ0.le, ?_⟩
  rw [div_le_one hτ0]
  have : 1 - τ ≤ 1 / Real.sqrt (1 + τ ^ 2) := by
    rcases le_or_gt τ 1 with h | h
    · rw [le_div_iff₀ hS]
      have hsq : Real.sqrt (1 + τ ^ 2) ≤ 1 + τ := by
        rw [Real.sqrt_le_left (by linarith)]; nlinarith
      nlinarith [hS]
    · have : 0 < 1 / Real.sqrt (1 + τ ^ 2) := by positivity
      linarith
  linarith

/-- Integrability of the remainder integrand `e^{-xτ}(1 - (1+τ²)^{-1/2})/τ` on `(0, ∞)`. -/
theorem struvePrim_rem_integrable {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun τ : ℝ => Real.exp (-(x * τ)) * ((1 - 1 / Real.sqrt (1 + τ ^ 2)) / τ))
      (Ioi 0) := by
  have hS : ∀ τ : ℝ, 0 < Real.sqrt (1 + τ ^ 2) := fun τ => Real.sqrt_pos.2 (by positivity)
  refine Integrable.mono' (exp_neg_integrableOn_Ioi 0 hx)
    ((ContinuousOn.mul (by fun_prop) (ContinuousOn.div (ContinuousOn.sub continuousOn_const
      (continuousOn_const.div (by fun_prop) fun τ _ => (hS τ).ne')) continuousOn_id
      fun τ hτ => ne_of_gt (show (0 : ℝ) < τ from hτ))).aestronglyMeasurable measurableSet_Ioi) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun τ hτ => ?_)
  obtain ⟨hq0, hq⟩ := struvePrim_quot_bounds (show (0 : ℝ) < τ from hτ)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hq0), neg_mul]
  calc Real.exp (-(x * τ)) * ((1 - 1 / Real.sqrt (1 + τ ^ 2)) / τ)
      ≤ Real.exp (-(x * τ)) * 1 := mul_le_mul_of_nonneg_left hq (Real.exp_pos _).le
    _ = _ := mul_one _

/-- On the positive axis, `∫₀^x 𝐊₀ - (2/π)(log 2x + γ) = (2/π) ∫₀^∞ e^{-xτ} (1 - (1+τ²)^{-1/2})/τ dτ`. -/
theorem struvePrim_remainder_ofReal {x : ℝ} (hx : 0 < x) :
    DLMF.primitive (struveK 0) x - 2 / π * (log (2 * x) + Real.eulerMascheroniConstant) =
      (((2 / π) * ∫ τ in Ioi (0 : ℝ),
        Real.exp (-(x * τ)) * ((1 - 1 / Real.sqrt (1 + τ ^ 2)) / τ) : ℝ) : ℂ) := by
  obtain ⟨i1, e1⟩ := struvePrim_integral_log_two_mul hx
  have hsplit : ∫ τ in Ioi (0 : ℝ), (1 / Real.sqrt (1 + τ ^ 2)) * ((1 - Real.exp (-(x * τ))) / τ) =
      (∫ τ in Ioi (0 : ℝ), (1 / Real.sqrt (1 + τ ^ 2) - Real.exp (-(x * τ))) / τ) +
        ∫ τ in Ioi (0 : ℝ), Real.exp (-(x * τ)) * ((1 - 1 / Real.sqrt (1 + τ ^ 2)) / τ) := by
    rw [← integral_add i1 (struvePrim_rem_integrable hx)]
    refine setIntegral_congr_fun measurableSet_Ioi fun τ _ => ?_
    ring
  rw [struvePrim_primitive_ofReal hx, hsplit, e1,
    show (2 : ℂ) * x = ((2 * x : ℝ) : ℂ) by push_cast; ring,
    ← ofReal_log (by positivity)]
  push_cast
  ring

/-- `∫₀^x 𝐊₀ - (2/π)(log 2x + γ) → 0` as `x → +∞` (the constant in DLMF 11.6.3). -/
theorem struvePrim_tendsto_ofReal :
    Tendsto (fun x : ℝ => DLMF.primitive (struveK 0) x -
      2 / π * (log (2 * x) + Real.eulerMascheroniConstant)) atTop (𝓝 0) := by
  have hb : ∀ᶠ x : ℝ in atTop, ‖DLMF.primitive (struveK 0) x -
      2 / π * (log (2 * x) + Real.eulerMascheroniConstant)‖ ≤ 2 / π * x⁻¹ := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [struvePrim_remainder_ofReal hx, norm_real, Real.norm_eq_abs]
    have hle : ∫ τ in Ioi (0 : ℝ), Real.exp (-(x * τ)) * ((1 - 1 / Real.sqrt (1 + τ ^ 2)) / τ) ≤
        ∫ τ in Ioi (0 : ℝ), Real.exp ((-x) * τ) := by
      refine setIntegral_mono_on (struvePrim_rem_integrable hx)
        (by simpa [neg_mul] using exp_neg_integrableOn_Ioi 0 hx) measurableSet_Ioi fun τ hτ => ?_
      obtain ⟨_, hq⟩ := struvePrim_quot_bounds (show (0 : ℝ) < τ from hτ)
      rw [neg_mul]
      calc Real.exp (-(x * τ)) * ((1 - 1 / Real.sqrt (1 + τ ^ 2)) / τ)
          ≤ Real.exp (-(x * τ)) * 1 := mul_le_mul_of_nonneg_left hq (Real.exp_pos _).le
        _ = _ := mul_one _
    have h0 : 0 ≤ ∫ τ in Ioi (0 : ℝ), Real.exp (-(x * τ)) * ((1 - 1 / Real.sqrt (1 + τ ^ 2)) / τ) :=
      setIntegral_nonneg measurableSet_Ioi fun τ hτ =>
        mul_nonneg (Real.exp_pos _).le (struvePrim_quot_bounds (show (0 : ℝ) < τ from hτ)).1
    rw [integral_exp_mul_Ioi (by linarith) 0, mul_zero, Real.exp_zero] at hle
    rw [abs_of_nonneg (mul_nonneg (by positivity) h0)]
    have : -1 / -x = x⁻¹ := by field_simp
    rw [this] at hle
    exact mul_le_mul_of_nonneg_left hle (by positivity)
  refine squeeze_zero_norm' hb ?_
  simpa using (tendsto_inv_atTop_zero.const_mul (2 / π))

/-- `arg (ρ e^{is}) = s` for `ρ > 0` and `s ∈ (-π, π]`. -/
theorem struvePrim_arg_ray {ρ s : ℝ} (hρ : 0 < ρ) (hs : s ∈ Ioc (-π) π) :
    arg ((ρ : ℂ) * exp (s * I)) = s := by
  rw [arg_real_mul _ hρ, exp_mul_I, arg_cos_add_sin_mul_I hs]

/-- Unpacking an eventual statement in `sector α`. -/
theorem struvePrim_exists_of_eventually_sector {α : ℝ} {p : ℂ → Prop}
    (h : ∀ᶠ z in sector α, p z) :
    ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → z ≠ 0 → |arg z| ≤ α → p z := by
  rw [sector, eventually_inf_principal] at h
  obtain ⟨t, ht, hsub⟩ := h
  obtain ⟨R, hR⟩ := mem_atTop_sets.1 ht
  exact ⟨R, fun z hz hz0 harg => hsub (hR _ hz) ⟨hz0, harg⟩⟩

/-- **Integration of a derivative bound in a sector.** If `G` is holomorphic on the slit plane,
`G(t) → 0` along the positive axis, and `‖G'(z)‖ ≤ C ‖z‖^{-(m+1)}` for large `z` with
`|arg z| ≤ α < π`, then `G(z) = O(z^{-m})` in `sector α`. -/
theorem struvePrim_isBigO_of_deriv {G G' : ℂ → ℂ} {α : ℝ} (hα0 : 0 ≤ α) (hα : α < π) {m : ℕ} (hm : 0 < m)
    (hG : ∀ z ∈ slitPlane, HasDerivAt G (G' z) z)
    (hlim : Tendsto (fun t : ℝ => G t) atTop (𝓝 0)) {R C : ℝ} (hR : 0 < R)
    (hC : ∀ z : ℂ, R ≤ ‖z‖ → |arg z| ≤ α → ‖G' z‖ ≤ C * ‖z‖ ^ (-((m : ℤ) + 1))) :
    G =O[sector α] (fun z : ℂ => z ^ (-(m : ℤ))) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  -- the ray estimate
  have hray : ∀ ρ : ℝ, R ≤ ρ → ‖G ρ‖ ≤ C / m * ρ ^ (-(m : ℤ)) := by
    intro ρ hρ
    have hρ0 : 0 < ρ := hR.trans_le hρ
    have hstep : ∀ t : ℝ, ρ ≤ t → ‖G t - G ρ‖ ≤ C / m * (ρ ^ (-(m : ℤ)) - t ^ (-(m : ℤ))) := by
      intro t ht
      have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary'
        (f := fun u : ℝ => G u - G ρ) (f' := fun u : ℝ => G' u) (a := ρ) (b := t)
        (B := fun u : ℝ => C / m * (ρ ^ (-(m : ℤ)) - u ^ (-(m : ℤ))))
        (B' := fun u : ℝ => C * u ^ (-((m : ℤ) + 1))) ?_ ?_ ?_ ?_ ?_ ?_ (right_mem_Icc.2 ht)
      · exact key
      · intro u hu
        have hu0 : 0 < u := hρ0.trans_le hu.1
        exact ((hG u (ofReal_mem_slitPlane.2 hu0)).comp_ofReal.sub_const _).continuousAt
          |>.continuousWithinAt
      · intro u hu
        have hu0 : 0 < u := hρ0.trans_le hu.1
        exact ((hG u (ofReal_mem_slitPlane.2 hu0)).comp_ofReal.sub_const _).hasDerivWithinAt
      · simp
      · intro u hu
        have hu0 : 0 < u := hρ0.trans_le hu.1
        exact ((continuousAt_const.sub (continuousAt_zpow₀ u _ (Or.inl hu0.ne'))).const_mul _)
          |>.continuousWithinAt
      · intro u hu
        have hu0 : 0 < u := hρ0.trans_le hu.1
        have h1 := ((hasDerivAt_zpow (-(m : ℤ)) u (Or.inl hu0.ne')).const_sub
          (ρ ^ (-(m : ℤ)))).const_mul (C / m)
        convert h1.hasDerivWithinAt using 1
        rw [show -(m : ℤ) - 1 = -((m : ℤ) + 1) by ring]
        push_cast
        field_simp
      · intro u hu
        have hu0 : 0 < u := hρ0.trans_le hu.1
        have h := hC u (by rw [norm_real, Real.norm_of_nonneg hu0.le]; linarith [hu.1])
          (by rw [arg_ofReal_of_nonneg hu0.le, abs_zero]; exact hα0)
        rwa [norm_real, Real.norm_of_nonneg hu0.le] at h
    have hlim' : Tendsto (fun t : ℝ => ‖G t - G ρ‖) atTop (𝓝 ‖G ρ‖) := by
      simpa using (hlim.sub_const (G ρ)).norm
    have hB : Tendsto (fun t : ℝ => C / m * (ρ ^ (-(m : ℤ)) - t ^ (-(m : ℤ)))) atTop
        (𝓝 (C / m * ρ ^ (-(m : ℤ)))) := by
      have : Tendsto (fun t : ℝ => t ^ (-(m : ℤ))) atTop (𝓝 0) :=
        tendsto_zpow_atTop_zero (by omega)
      simpa using (tendsto_const_nhds.sub this).const_mul (C / m)
    exact le_of_tendsto_of_tendsto hlim' hB
      (eventually_atTop.2 ⟨ρ, fun t ht => hstep t ht⟩)
  have hC0 : 0 ≤ C := by
    have h := hC R (by rw [norm_real, Real.norm_of_nonneg hR.le])
      (by rw [arg_ofReal_of_nonneg hR.le, abs_zero]; exact hα0)
    rw [norm_real, Real.norm_of_nonneg hR.le] at h
    have hp : 0 < R ^ (-((m : ℤ) + 1)) := zpow_pos hR _
    by_contra hneg
    push Not at hneg
    nlinarith [norm_nonneg (G' R)]
  have hev : ∀ᶠ z in sector α, R ≤ ‖z‖ ∧ z ∈ {z : ℂ | z ≠ 0 ∧ |arg z| ≤ α} :=
    (((tendsto_comap.mono_left inf_le_left : Tendsto (fun z : ℂ => ‖z‖) (sector α) atTop)).eventually
      (eventually_ge_atTop R)).and
      (mem_inf_of_right (mem_principal_self _))
  refine IsBigO.of_bound (C / m + C * α) (hev.mono fun z ⟨hzR, hz0, hzα⟩ => ?_)
  set ρ := ‖z‖ with hρdef
  have hρ0 : 0 < ρ := hR.trans_le hzR
  set f : ℝ → ℂ := fun s => G ((ρ : ℂ) * exp (s * I)) with hf
  have hmem : ∀ s ∈ Icc (-α) α, s ∈ Ioc (-π) π := fun s hs =>
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hnormw : ∀ s : ℝ, ‖(ρ : ℂ) * exp (s * I)‖ = ρ := fun s => by
    rw [norm_mul, norm_real, Real.norm_of_nonneg hρ0.le, norm_exp_ofReal_mul_I, mul_one]
  have hderiv : ∀ s ∈ Icc (-α) α, HasDerivWithinAt f
      (G' ((ρ : ℂ) * exp (s * I)) * ((ρ : ℂ) * (exp (s * I) * I))) (Icc (-α) α) s := by
    intro s hs
    have harg := struvePrim_arg_ray hρ0 (hmem s hs)
    have hsl : (ρ : ℂ) * exp (s * I) ∈ slitPlane := by
      rw [mem_slitPlane_iff_arg, harg]
      refine ⟨by linarith [hs.2], mul_ne_zero (ofReal_ne_zero.2 hρ0.ne') (exp_ne_zero _)⟩
    have h1 : HasDerivAt (fun s : ℝ => (ρ : ℂ) * exp (s * I)) ((ρ : ℂ) * (exp (s * I) * I)) s := by
      have := (((hasDerivAt_id s).ofReal_comp).mul_const I).cexp.const_mul (ρ : ℂ)
      simpa using this
    exact ((hG _ hsl).comp s h1).hasDerivWithinAt
  have hbound : ∀ s ∈ Icc (-α) α,
      ‖G' ((ρ : ℂ) * exp (s * I)) * ((ρ : ℂ) * (exp (s * I) * I))‖ ≤ C * ρ ^ (-(m : ℤ)) := by
    intro s hs
    have harg := struvePrim_arg_ray hρ0 (hmem s hs)
    have h := hC ((ρ : ℂ) * exp (s * I)) (by rw [hnormw]; exact hzR)
      (by rw [harg, abs_le]; exact ⟨hs.1, hs.2⟩)
    rw [hnormw] at h
    rw [norm_mul, ← mul_assoc, norm_mul _ I, hnormw, norm_I, mul_one]
    calc ‖G' ((ρ : ℂ) * exp (s * I))‖ * ρ ≤ C * ρ ^ (-((m : ℤ) + 1)) * ρ :=
          mul_le_mul_of_nonneg_right h hρ0.le
      _ = C * ρ ^ (-(m : ℤ)) := by
          rw [mul_assoc, ← zpow_add_one₀ hρ0.ne']; congr 2; ring
  have hθ : arg z ∈ Icc (-α) α := abs_le.1 hzα
  have hmvt := (convex_Icc (-α) α).norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
    (show (0 : ℝ) ∈ Icc (-α) α from ⟨by linarith, hα0⟩) hθ
  have hfz : f (arg z) = G z := by
    simp only [hf, hρdef]; rw [norm_mul_exp_arg_mul_I]
  have hf0 : f 0 = G ρ := by simp [hf]
  rw [hfz, hf0, sub_zero, Real.norm_eq_abs] at hmvt
  have hz' : ‖z ^ (-(m : ℤ))‖ = ρ ^ (-(m : ℤ)) := by rw [norm_zpow]
  rw [hz']
  have hp : 0 ≤ ρ ^ (-(m : ℤ)) := (zpow_pos hρ0 _).le
  have h1 := hray ρ hzR
  have h2 : C * ρ ^ (-(m : ℤ)) * |arg z| ≤ C * ρ ^ (-(m : ℤ)) * α :=
    mul_le_mul_of_nonneg_left hzα (mul_nonneg hC0 hp)
  calc ‖G z‖ ≤ ‖G ρ‖ + ‖G z - G ρ‖ := by
        have := norm_sub_norm_le (G z) (G ρ); linarith
    _ ≤ C / m * ρ ^ (-(m : ℤ)) + C * ρ ^ (-(m : ℤ)) * α := by linarith
    _ = (C / m + C * α) * ρ ^ (-(m : ℤ)) := by ring

end StruvePrimitive
end DLMF.Struve
end
