/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Airy.GeneralizedContours

/-!
# Airy integral representations, DLMF §9.5

Statements acquired from the NIST DLMF, checked 2026-10-19.
New statements are initially admitted; existing proved Airy results are retained.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF.Confluent
open scoped Real Topology
namespace DLMF.Airy

/-- `e^{(θ+π)i} = -e^{θi}`. -/
theorem exp_add_pi_mul_I (θ : ℝ) : exp (((θ + π : ℝ) : ℂ) * I) = -exp (θ * I) := by
  push_cast; rw [add_mul, exp_add, exp_pi_mul_I]; ring

/-- The Airy contour integrand at `u` equals the Reid kernel (p = 0) at `-u`. -/
theorem reidKernel_zero_eq_airyIntegrand (z w : ℂ) {u : ℂ} (hu : exp w = -u) :
    reidKernel z 0 w = exp (u ^ 3 / 3 - z * u) := by
  rw [reidKernel, show exp (3 * w) = exp w ^ 3 by rw [← exp_nat_mul]; push_cast; ring_nf, hu]
  congr 1; ring

/-- Airy rays are Reid rays (p = 0) rotated by `π`. -/
theorem rayIntegral_airy_eq_reidRay (z : ℂ) (θ : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    rayIntegral (fun t => exp (t ^ 3 / 3 - z * t)) θ r = -reidRay z 0 (θ + π) r := by
  rw [rayIntegral, reidRay, ← integral_neg]
  refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : r < t) => ?_
  have ht0 : 0 < t := hr.trans_lt ht
  rw [reidKernel_zero_eq_airyIntegrand z _ (u := t * exp (θ * I)), exp_add_pi_mul_I]
  · ring
  · rw [exp_add, exp_log (ofReal_ne_zero.mpr ht0.ne'), exp_add_pi_mul_I]; ring

/-- Airy arcs are Reid arcs (p = 0) rotated by `π`. -/
theorem arcIntegral_airy_eq_reidArc (z : ℂ) (α β : ℝ) :
    arcIntegral (fun t => exp (t ^ 3 / 3 - z * t)) α β = -reidArc z 0 (α + π) (β + π) := by
  rw [arcIntegral, reidArc, ← intervalIntegral.integral_comp_add_right, ← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  rw [reidKernel_zero_eq_airyIntegrand z _ (u := exp (θ * I)), exp_add_pi_mul_I]
  · ring
  · exact exp_add_pi_mul_I θ

/-- Airy contours are Reid contours (p = 0) rotated by `π`. -/
theorem contourIntegral_airy_eq_reidContour (z : ℂ) (α β : ℝ) :
    contourIntegral (fun t => exp (t ^ 3 / 3 - z * t)) α β =
      -reidContour z 0 (α + π) (β + π) := by
  rw [contourIntegral, reidContour, rayIntegral_airy_eq_reidRay z α zero_le_one,
    rayIntegral_airy_eq_reidRay z β zero_le_one, arcIntegral_airy_eq_reidArc]
  ring

/-- Reversing the orientation of a contour. -/
theorem contourIntegral_swap (f : ℂ → ℂ) (α β : ℝ) :
    contourIntegral f α β = -contourIntegral f β α := by
  rw [contourIntegral, contourIntegral, arcIntegral, arcIntegral, intervalIntegral.integral_symm]
  ring

/-- Concatenation of Reid contours. -/
theorem reidContour_add_adjacent (z p : ℂ) (a b c : ℝ) :
    reidContour z p a b + reidContour z p b c = reidContour z p a c := by
  rw [reidContour, reidContour, reidContour, ← reidArc_add_adjacent z p a b c]
  ring

/-- `Ai(z) = (2πi)⁻¹ ∫ exp(t³/3 - zt) dt` along a contour from `∞ e^{-πi/3}` to
`∞ e^{πi/3}` (DLMF 9.5.4). -/
@[dlmf 9.5.E4]
theorem airyAi_contour_integral (z : ℂ) :
    airyAi z = contourIntegral (fun t => exp (t ^ 3 / 3 - z * t)) (-π / 3) (π / 3) / (2 * π * I) := by
  rw [contourIntegral_swap, contourIntegral_airy_eq_reidContour, ← reidAiryA_zero_parameter,
    show π / 3 + π = 4 * π / 3 by ring, show -π / 3 + π = 2 * π / 3 by ring]
  simp only [reidAiryA, Fin.val_zero]
  ring

/-- `Bi(z) = (2π)⁻¹ (∫_{-∞}^{∞e^{πi/3}} + ∫_{-∞}^{∞e^{-πi/3}}) exp(t³/3 - zt) dt`
(DLMF 9.5.5). -/
@[dlmf 9.5.E5]
theorem airyBi_contour_integral (z : ℂ) :
    airyBi z = (contourIntegral (fun t => exp (t ^ 3 / 3 - z * t)) π (π / 3) +
      contourIntegral (fun t => exp (t ^ 3 / 3 - z * t)) π (-π / 3)) / (2 * π) := by
  rw [contourIntegral_airy_eq_reidContour, contourIntegral_airy_eq_reidContour,
    show π + π = 2 * π by ring, show π / 3 + π = 4 * π / 3 by ring,
    show -π / 3 + π = 2 * π / 3 by ring, ← reidContour_add_adjacent z 0 (2 * π) (4 * π / 3) (2 * π / 3)]
  have h0 : reidContour z 0 (4 * π / 3) (2 * π / 3) = 2 * π * I * airyAi z := by
    rw [← reidAiryA_zero_parameter]; simp only [reidAiryA, Fin.val_zero]
    field_simp
  have h1 : reidContour z 0 (2 * π) (4 * π / 3) =
      2 * π * I * (exp (2 * π * I / 3) * airyAi (z * exp (2 * π * I / 3))) := by
    rw [← (reidAiryA_zero_rotations z).1]; simp only [reidAiryA, Fin.val_one]
    field_simp
  rw [h0, h1, airyBi_eq_airyAi_omega]
  have hs := airyAi_add_omega z
  set b := airyAi (z * exp (2 * π * I / 3))
  set c := airyAi (z * exp (-(2 * π * I / 3)))
  rw [exp_two_pi_I_div_three, exp_neg_two_pi_I_div_three] at hs
  rw [exp_two_pi_I_div_three, exp_pi_I_div_six, exp_neg_pi_I_div_six]
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  linear_combination 2 * I * hs + 2 * (((Real.sqrt 3 / 2 : ℝ) : ℂ) * c + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * b) * I_sq

/-! ### The oscillatory integrals 9.5.1–9.5.3

The contours of 9.5.4–9.5.5 are collapsed onto rays from the origin (the integrand is entire),
and `∫₀^R e^{i(t³/3+xt)} dt` is rotated onto the ray `arg t = π/6`; the arc of radius `R`
vanishes by a Jordan-type bound. Real and imaginary parts give 9.5.1 and 9.5.3; 9.5.2 is a
linear substitution in 9.5.1.
-/

/-- Derivative of a primitive along the line `r ↦ r c`. -/
theorem airyInt_hasDerivAt_ray {f g : ℂ → ℂ} (hg : ∀ w, HasDerivAt g (f w) w) (c : ℂ) (r : ℝ) :
    HasDerivAt (fun r : ℝ => g (r * c)) (c * f (r * c)) r := by
  have h := (hg ((r : ℂ) * c)).comp (r : ℂ) ((hasDerivAt_id (r : ℂ)).mul_const c)
  simp only [Function.comp_def, id, one_mul] at h
  rw [mul_comm]
  exact h.comp_ofReal

/-- Derivative of a primitive along the circle `y ↦ R e^{iy}`. -/
theorem airyInt_hasDerivAt_arc {f g : ℂ → ℂ} (hg : ∀ w, HasDerivAt g (f w) w) (R y : ℝ) :
    HasDerivAt (fun y : ℝ => g (R * exp (y * I))) (I * R * exp (y * I) * f (R * exp (y * I))) y := by
  have h1 : HasDerivAt (fun w : ℂ => (R : ℂ) * exp (w * I)) (R * (exp (y * I) * I)) (y : ℂ) :=
    ((hasDerivAt_id (y : ℂ)).mul_const I).cexp.const_mul (R : ℂ) |>.congr_deriv (by simp)
  have h2 : HasDerivAt (fun w : ℂ => g (R * exp (w * I)))
      (f (R * exp (y * I)) * (R * (exp (y * I) * I))) (y : ℂ) := (hg _).comp (y : ℂ) h1
  have h := h2.comp_ofReal
  rw [show I * R * exp (y * I) * f (R * exp (y * I)) =
    f (R * exp (y * I)) * (R * (exp (y * I) * I)) by ring]
  exact h

/-- Integral of an entire function along a segment of the line `r ↦ r c`, via a primitive. -/
theorem airyInt_integral_segment {f g : ℂ → ℂ} (hg : ∀ w, HasDerivAt g (f w) w)
    (hf : Continuous f) (c : ℂ) (a b : ℝ) :
    ∫ r in a..b, c * f (r * c) = g (b * c) - g (a * c) :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => airyInt_hasDerivAt_ray hg c r)
    ((continuous_const.mul (hf.comp (continuous_ofReal.mul continuous_const))).intervalIntegrable _ _)

/-- Integral of an entire function along an arc of the circle of radius `R`, via a primitive. -/
theorem airyInt_integral_arc {f g : ℂ → ℂ} (hg : ∀ w, HasDerivAt g (f w) w)
    (hf : Continuous f) (R α β : ℝ) :
    ∫ y in α..β, I * R * exp (y * I) * f (R * exp (y * I)) =
      g (R * exp (β * I)) - g (R * exp (α * I)) :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => airyInt_hasDerivAt_arc hg R y)
    (Continuous.intervalIntegrable (by fun_prop) _ _)



/-- A ray integral from the origin splits into the segment `[0, e^{iθ}]` and the ray from radius one. -/
theorem airyInt_rayIntegral_zero {f g : ℂ → ℂ} (hg : ∀ w, HasDerivAt g (f w) w)
    (hf : Continuous f) (θ : ℝ)
    (hint : IntegrableOn (fun t : ℝ => exp (θ * I) * f (t * exp (θ * I))) (Ioi 0)) :
    rayIntegral f θ 0 = (g (exp (θ * I)) - g 0) + rayIntegral f θ 1 := by
  rw [rayIntegral, rayIntegral, ← Ioc_union_Ioi_eq_Ioi zero_le_one,
    setIntegral_union (Ioc_disjoint_Ioi_same) measurableSet_Ioi
      (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi zero_le_one)),
    ← intervalIntegral.integral_of_le zero_le_one, airyInt_integral_segment hg hf]
  simp

/-- For an entire integrand, a contour integral is the difference of two ray integrals from the origin. -/
theorem airyInt_contourIntegral_eq_rays {f g : ℂ → ℂ} (hg : ∀ w, HasDerivAt g (f w) w)
    (hf : Continuous f) (α β : ℝ)
    (hα : IntegrableOn (fun t : ℝ => exp (α * I) * f (t * exp (α * I))) (Ioi 0))
    (hβ : IntegrableOn (fun t : ℝ => exp (β * I) * f (t * exp (β * I))) (Ioi 0)) :
    contourIntegral f α β = -rayIntegral f α 0 + rayIntegral f β 0 := by
  rw [airyInt_rayIntegral_zero hg hf α hα, airyInt_rayIntegral_zero hg hf β hβ, contourIntegral,
    arcIntegral]
  have h := airyInt_integral_arc hg hf 1 α β
  simp only [ofReal_one, one_mul, mul_one] at h
  rw [h]
  ring

/-- The Airy integrand `exp(t³/3 - zt)` is integrable along a ray with `e^{3iθ} = -1`. -/
theorem airyInt_integrableOn_ray (z : ℂ) {θ : ℝ} (hθ : exp (3 * (θ * I)) = -1) :
    IntegrableOn (fun t : ℝ => exp (θ * I) *
      exp (((t : ℂ) * exp (θ * I)) ^ 3 / 3 - z * ((t : ℂ) * exp (θ * I)))) (Ioi 0) := by
  have hb : (0 : ℝ) < 1 / 3 := by norm_num
  refine (scorerAsym_integrableOn_pow_exp 0 (-‖z‖) hb).mono' ?_ ?_
  · exact Continuous.aestronglyMeasurable (by fun_prop)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
    have h3 : ((t : ℂ) * exp (θ * I)) ^ 3 = -((t : ℂ) ^ 3) := by
      rw [mul_pow, ← exp_nat_mul]; push_cast; rw [hθ]; ring
    rw [h3, norm_mul, norm_exp_ofReal_mul_I, one_mul, norm_exp, pow_zero, one_mul]
    apply Real.exp_le_exp.mpr
    have hre : (-((t : ℂ) ^ 3) / 3 - z * ((t : ℂ) * exp (θ * I))).re =
        -(t ^ 3 / 3) - (z * exp (θ * I)).re * t := by
      have : z * ((t : ℂ) * exp (θ * I)) = (z * exp (θ * I)) * (t : ℂ) := by ring
      rw [this, sub_re, re_mul_ofReal]
      simp [pow_succ]
      ring
    rw [hre]
    have h1 : -(z * exp (θ * I)).re ≤ ‖z‖ := by
      refine (neg_le_abs _).trans ((abs_re_le_norm _).trans ?_)
      rw [norm_mul, norm_exp_ofReal_mul_I, mul_one]
    nlinarith


/-- The Airy integrand `exp(t³/3 - x t)` for real `x`. -/
noncomputable def airyInt_kernel (x : ℝ) (t : ℂ) : ℂ := exp (t ^ 3 / 3 - (x : ℂ) * t)

/-- The Airy integrand has an entire primitive. -/
theorem airyInt_kernel_primitive (x : ℝ) :
    ∃ g : ℂ → ℂ, ∀ w, HasDerivAt g (airyInt_kernel x w) w := by
  have hd : Differentiable ℂ (airyInt_kernel x) := by unfold airyInt_kernel; fun_prop
  obtain ⟨g, hg⟩ := hd.isExactOn_univ
  exact ⟨g, fun w => hg w (mem_univ w)⟩

/-- The Airy integrand is continuous. -/
theorem airyInt_continuous_kernel (x : ℝ) : Continuous (airyInt_kernel x) := by
  unfold airyInt_kernel; fun_prop

/-- Complex conjugation reflects the Airy ray integrals for real `x`. -/
theorem airyInt_conj_rayIntegral (x θ : ℝ) (r : ℝ) :
    (starRingEnd ℂ) (rayIntegral (airyInt_kernel x) θ r) = rayIntegral (airyInt_kernel x) (-θ) r := by
  rw [rayIntegral, rayIntegral, ← integral_conj]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  have he : (starRingEnd ℂ) (exp (θ * I)) = exp (((-θ : ℝ) : ℂ) * I) := by
    rw [← exp_conj]; congr 1; simp
  simp only [airyInt_kernel, map_mul, he, ← exp_conj, map_sub, map_div₀, map_pow, conj_ofReal,
    map_ofNat]

/-- `e^{3iθ} = -1` at the odd multiples of `π/3`. -/
theorem airyInt_exp_three_mul (θ : ℝ) (k : ℤ) (h : θ = (2 * k + 1) * π / 3) :
    exp (3 * (θ * I)) = -1 := by
  rw [h, show (3 : ℂ) * ((((2 * k + 1) * π / 3 : ℝ)) * I) = (k : ℂ) * (2 * π * I) + π * I by
    push_cast; ring, exp_add, exp_int_mul_two_pi_mul_I, one_mul, exp_pi_mul_I]

/-- Integrability of the Airy integrand along the rays at odd multiples of `π/3`. -/
theorem airyInt_int_ray (x θ : ℝ) (k : ℤ) (h : θ = (2 * k + 1) * π / 3) :
    IntegrableOn (fun t : ℝ => exp (θ * I) * airyInt_kernel x (t * exp (θ * I))) (Ioi 0) :=
  airyInt_integrableOn_ray (x : ℂ) (airyInt_exp_three_mul θ k h)

/-- The ray integral `w(x) = ∫₀^∞ e^{-iπ/3} exp(-t³/3 - x t e^{-iπ/3}) dt`. -/
noncomputable def airyInt_w (x : ℝ) : ℂ := rayIntegral (airyInt_kernel x) (-π / 3) 0

/-- The Airy contour integrals as differences of ray integrals from the origin. -/
theorem airyInt_contour (x α β : ℝ) (kα kβ : ℤ) (hα : α = (2 * kα + 1) * π / 3)
    (hβ : β = (2 * kβ + 1) * π / 3) :
    contourIntegral (airyInt_kernel x) α β =
      -rayIntegral (airyInt_kernel x) α 0 + rayIntegral (airyInt_kernel x) β 0 := by
  obtain ⟨g, hg⟩ := airyInt_kernel_primitive x
  exact airyInt_contourIntegral_eq_rays hg (airyInt_continuous_kernel x) α β
    (airyInt_int_ray x α kα hα) (airyInt_int_ray x β kβ hβ)

/-- `π Ai(x) = -Im w(x)` for real `x`, from 9.5.4. -/
theorem airyInt_pi_airyAi (x : ℝ) : (π : ℂ) * airyAi x = ((-(airyInt_w x).im : ℝ) : ℂ) := by
  have h := airyAi_contour_integral (x : ℂ)
  have hc := airyInt_contour x (-π / 3) (π / 3) (-1) 0 (by push_cast; ring) (by push_cast; ring)
  have hk : (fun t => exp (t ^ 3 / 3 - (x : ℂ) * t)) = airyInt_kernel x := rfl
  rw [hk, hc] at h
  have hconj := airyInt_conj_rayIntegral x (-π / 3) 0
  rw [show -(-π / 3) = π / 3 by ring] at hconj
  rw [← hconj] at h
  rw [h]
  change (π : ℂ) * ((-airyInt_w x + (starRingEnd ℂ) (airyInt_w x)) / (2 * π * I)) = _
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hw : -airyInt_w x + (starRingEnd ℂ) (airyInt_w x) = -2 * I * ((airyInt_w x).im : ℂ) := by
    apply Complex.ext <;> simp; ring
  rw [hw]
  field_simp
  push_cast
  ring

/-- The Airy ray integral along the negative axis. -/
theorem airyInt_ray_pi (x : ℝ) :
    rayIntegral (airyInt_kernel x) π 0 = -∫ t : ℝ in Ioi 0, exp (-(t : ℂ) ^ 3 / 3 + x * t) := by
  rw [rayIntegral, ← integral_neg]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [airyInt_kernel, exp_pi_mul_I]
  ring_nf

/-- `π Bi(x) - ∫₀^∞ e^{-t³/3+xt} dt = Re w(x)` for real `x`, from 9.5.5. -/
theorem airyInt_pi_airyBi (x : ℝ) : (π : ℂ) * airyBi x -
    (∫ t : ℝ in Ioi 0, exp (-(t : ℂ) ^ 3 / 3 + x * t)) = (((airyInt_w x).re : ℝ) : ℂ) := by
  have h := airyBi_contour_integral (x : ℂ)
  have hk : (fun t => exp (t ^ 3 / 3 - (x : ℂ) * t)) = airyInt_kernel x := rfl
  rw [hk, airyInt_contour x π (π / 3) 1 0 (by push_cast; ring) (by push_cast; ring),
    airyInt_contour x π (-π / 3) 1 (-1) (by push_cast; ring) (by push_cast; ring),
    airyInt_ray_pi] at h
  have hconj := airyInt_conj_rayIntegral x (-π / 3) 0
  rw [show -(-π / 3) = π / 3 by ring] at hconj
  rw [← hconj] at h
  change airyBi x = (-(-_) + (starRingEnd ℂ) (airyInt_w x) + (-(-_) + airyInt_w x)) / (2 * π) at h
  rw [h]
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hw : (starRingEnd ℂ) (airyInt_w x) + airyInt_w x = 2 * ((airyInt_w x).re : ℂ) := by
    apply Complex.ext <;> simp; ring
  rw [neg_neg]
  calc (π : ℂ) * (((∫ t : ℝ in Ioi 0, exp (-(t : ℂ) ^ 3 / 3 + x * t)) + (starRingEnd ℂ) (airyInt_w x) +
        ((∫ t : ℝ in Ioi 0, exp (-(t : ℂ) ^ 3 / 3 + x * t)) + airyInt_w x)) / (2 * π)) -
        ∫ t : ℝ in Ioi 0, exp (-(t : ℂ) ^ 3 / 3 + x * t) =
        ((starRingEnd ℂ) (airyInt_w x) + airyInt_w x) / 2 := by field_simp; ring
    _ = _ := by rw [hw]; ring


/-- The oscillatory integrand `exp(i(t³/3 + x t))`. -/
noncomputable def airyInt_osc (x : ℝ) (t : ℂ) : ℂ := exp (I * (t ^ 3 / 3 + (x : ℂ) * t))

/-- The oscillatory integrand is continuous. -/
theorem airyInt_continuous_osc (x : ℝ) : Continuous (airyInt_osc x) := by
  unfold airyInt_osc; fun_prop

/-- `(e^{iπ/6})³ = i`. -/
theorem airyInt_exp_sixth_cube : exp (((π / 6 : ℝ) : ℂ) * I) ^ 3 = I := by
  rw [← exp_nat_mul, show ((3 : ℕ) : ℂ) * (((π / 6 : ℝ) : ℂ) * I) = π / 2 * I by push_cast; ring,
    exp_pi_div_two_mul_I]

/-- `e^{-iπ/3} = -i e^{iπ/6}`. -/
theorem airyInt_exp_neg_third : exp (((-π / 3 : ℝ) : ℂ) * I) = -I * exp (((π / 6 : ℝ) : ℂ) * I) := by
  rw [show (((-π / 3 : ℝ) : ℂ) * I) = ((π / 6 : ℝ) : ℂ) * I - π / 2 * I by push_cast; ring,
    exp_sub, exp_pi_div_two_mul_I, div_I]
  ring

/-- The rotated oscillatory integrand is `i` times the Airy ray integrand at angle `-π/3`. -/
theorem airyInt_osc_rotate (x r : ℝ) :
    exp (((π / 6 : ℝ) : ℂ) * I) * airyInt_osc x (r * exp (((π / 6 : ℝ) : ℂ) * I)) =
      I * (exp (((-π / 3 : ℝ) : ℂ) * I) *
        airyInt_kernel x (r * exp (((-π / 3 : ℝ) : ℂ) * I))) := by
  set u := exp (((π / 6 : ℝ) : ℂ) * I)
  have hu3 : u ^ 3 = I := airyInt_exp_sixth_cube
  rw [airyInt_exp_neg_third, airyInt_osc, airyInt_kernel]
  have e1 : I * (((r : ℂ) * u) ^ 3 / 3 + (x : ℂ) * (r * u)) = -(r : ℂ) ^ 3 / 3 + I * x * r * u := by
    rw [mul_pow, hu3]; linear_combination (r : ℂ) ^ 3 / 3 * I_sq
  have e2 : ((r : ℂ) * (-I * u)) ^ 3 / 3 - (x : ℂ) * (r * (-I * u)) =
      -(r : ℂ) ^ 3 / 3 + I * x * r * u := by
    rw [mul_pow, mul_pow, hu3]
    linear_combination (-(r : ℂ) ^ 3 / 3 * (I ^ 2 - 1)) * I_sq
  rw [e1, e2]
  linear_combination (u * exp (-(r : ℂ) ^ 3 / 3 + I * x * r * u)) * I_sq

/-- `∫₀^b e^{-ay} dy ≤ 1/a`. -/
theorem airyInt_integral_exp_neg_le {a : ℝ} (ha : 0 < a) (b : ℝ) :
    ∫ y in (0 : ℝ)..b, Real.exp (-(a * y)) ≤ 1 / a := by
  have hd : ∀ y ∈ uIcc 0 b, HasDerivAt (fun y => -Real.exp (-(a * y)) / a) (Real.exp (-(a * y))) y := by
    intro y _
    have h1 : HasDerivAt (fun y : ℝ => -(a * y)) (-(a * 1)) y := ((hasDerivAt_id' y).const_mul a).neg
    have := (h1.exp.neg).div_const a
    refine this.congr_deriv ?_
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  have := Real.exp_pos (-(a * b))
  simp only [mul_zero, neg_zero, Real.exp_zero]
  rw [div_sub_div_same, div_le_div_iff_of_pos_right ha]
  linarith

/-- The norm of the oscillatory integrand on the arc. -/
theorem airyInt_norm_osc_arc (x R y : ℝ) :
    ‖I * R * exp (y * I) * airyInt_osc x (R * exp (y * I))‖ =
      |R| * Real.exp (-(R ^ 3 * Real.sin (3 * y) / 3 + x * R * Real.sin y)) := by
  rw [norm_mul, norm_mul, norm_mul, norm_I, one_mul, norm_real, Real.norm_eq_abs,
    norm_exp_ofReal_mul_I, mul_one, airyInt_osc, norm_exp]
  congr 2
  have h3 : ((R : ℂ) * exp (y * I)) ^ 3 = ((R ^ 3 : ℝ) : ℂ) * exp (((3 * y : ℝ) : ℂ) * I) := by
    rw [mul_pow, ← exp_nat_mul]; push_cast; ring_nf
  rw [h3]
  simp only [mul_re, I_re, I_im, add_im, div_ofNat_im, mul_im, ofReal_re, ofReal_im,
    exp_ofReal_mul_I_re, exp_ofReal_mul_I_im, zero_mul, one_mul, add_re, div_ofNat_re]
  ring

/-- Jordan-type bound for the arc `0 ≤ arg t ≤ π/6`, `|t| = R`. -/
theorem airyInt_arc_bound (x : ℝ) {R : ℝ} (hR : 1 ≤ R) (hRx : 6 * |x| ≤ R ^ 2) :
    ‖∫ y in (0 : ℝ)..(π / 6), I * R * exp (y * I) * airyInt_osc x (R * exp (y * I))‖ ≤
      π / R ^ 2 := by
  have hR0 : 0 < R := by linarith
  have hpi := Real.pi_pos
  set a := R ^ 3 / π with ha
  have ha0 : 0 < a := by positivity
  have hbound : ∀ y ∈ Ioc (0 : ℝ) (π / 6),
      ‖I * R * exp (y * I) * airyInt_osc x (R * exp (y * I))‖ ≤ R * Real.exp (-(a * y)) := by
    intro y hy
    rw [airyInt_norm_osc_arc, abs_of_pos hR0]
    gcongr
    have hy0 : 0 ≤ y := hy.1.le
    have hs : 0 ≤ Real.sin y := Real.sin_nonneg_of_nonneg_of_le_pi hy0 (by linarith [hy.2])
    have hs2 : Real.sin y ≤ 1 / 2 := by
      rw [← Real.sin_pi_div_six]
      exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) hy.2
    have h3 : Real.sin y ≤ Real.sin (3 * y) := by
      have hsq : Real.sin y ^ 2 ≤ 1 / 4 := by nlinarith
      rw [Real.sin_three_mul]; nlinarith [mul_nonneg hs (by linarith : (0 : ℝ) ≤ 1 / 4 - Real.sin y ^ 2)]
    have hj : 2 / π * (3 * y) ≤ Real.sin (3 * y) := Real.mul_le_sin (by linarith) (by linarith [hy.2])
    have hxr : -(x * R * Real.sin y) ≤ R ^ 3 / 6 * Real.sin (3 * y) := by
      have h1 : -(x * R * Real.sin y) ≤ |x| * R * Real.sin (3 * y) := by
        have : -(x * R * Real.sin y) ≤ |x| * R * Real.sin y := by
          have := neg_abs_le x
          nlinarith [mul_nonneg hR0.le hs]
        refine this.trans ?_
        gcongr
      refine h1.trans ?_
      have hs3 : 0 ≤ Real.sin (3 * y) := hs.trans h3
      have : |x| * R ≤ R ^ 3 / 6 := by nlinarith
      nlinarith
    have : a * y = R ^ 3 / 6 * (2 / π * (3 * y)) := by rw [ha]; field_simp; ring
    rw [this]
    nlinarith [pow_pos hR0 3]
  calc _ ≤ ∫ y in (0 : ℝ)..(π / 6), R * Real.exp (-(a * y)) :=
        intervalIntegral.norm_integral_le_of_norm_le (by positivity)
          (Eventually.of_forall hbound) (Continuous.intervalIntegrable (by fun_prop) _ _)
    _ = R * ∫ y in (0 : ℝ)..(π / 6), Real.exp (-(a * y)) := intervalIntegral.integral_const_mul _ _
    _ ≤ R * (1 / a) := by gcongr; exact airyInt_integral_exp_neg_le ha0 _
    _ = π / R ^ 2 := by rw [ha]; field_simp

/-- `∫₀^R e^{i(t³/3+xt)} dt → i w(x)`. -/
theorem airyInt_tendsto_osc (x : ℝ) :
    Tendsto (fun R : ℝ => ∫ t in (0 : ℝ)..R, airyInt_osc x t) atTop (𝓝 (I * airyInt_w x)) := by
  obtain ⟨G, hG⟩ : ∃ G : ℂ → ℂ, ∀ w, HasDerivAt G (airyInt_osc x w) w := by
    have hd : Differentiable ℂ (airyInt_osc x) := by unfold airyInt_osc; fun_prop
    obtain ⟨g, hg⟩ := hd.isExactOn_univ
    exact ⟨g, fun w => hg w (mem_univ w)⟩
  set u := exp (((π / 6 : ℝ) : ℂ) * I)
  have hsplit : ∀ R : ℝ, ∫ t in (0 : ℝ)..R, airyInt_osc x t =
      (∫ r in (0 : ℝ)..R, u * airyInt_osc x (r * u)) -
        ∫ y in (0 : ℝ)..(π / 6), I * R * exp (y * I) * airyInt_osc x (R * exp (y * I)) := by
    intro R
    have h1 := airyInt_integral_segment hG (airyInt_continuous_osc x) 1 0 R
    have h2 := airyInt_integral_segment hG (airyInt_continuous_osc x) u 0 R
    have h3 := airyInt_integral_arc hG (airyInt_continuous_osc x) R 0 (π / 6)
    simp only [one_mul, mul_one, ofReal_zero, zero_mul] at h1 h2 h3
    rw [h1, h2, h3, exp_zero, mul_one]
    ring
  have hint : IntegrableOn (fun r : ℝ => u * airyInt_osc x (r * u)) (Ioi 0) := by
    have := (airyInt_int_ray x (-π / 3) (-1) (by push_cast; ring)).const_mul I
    exact IntegrableOn.congr_fun this (fun r _ => (airyInt_osc_rotate x r).symm) measurableSet_Ioi
  have hseg := intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id
  have hval : ∫ r in Ioi (0 : ℝ), u * airyInt_osc x (r * u) = I * airyInt_w x := by
    rw [airyInt_w, rayIntegral, ← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi fun r _ => airyInt_osc_rotate x r
  rw [hval] at hseg
  have harc : Tendsto (fun R : ℝ => ∫ y in (0 : ℝ)..(π / 6),
      I * R * exp (y * I) * airyInt_osc x (R * exp (y * I))) atTop (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun R : ℝ => π / R ^ 2) ?_
      ((tendsto_const_nhds (x := π)).div_atTop (tendsto_pow_atTop two_ne_zero))
    filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop (6 * |x| + 1)] with R hR hR'
    refine airyInt_arc_bound x hR ?_
    nlinarith [abs_nonneg x]
  simpa [hsplit] using hseg.sub harc


/-- The oscillatory integrand on the real axis. -/
theorem airyInt_osc_ofReal (x t : ℝ) :
    airyInt_osc x t = exp (((t ^ 3 / 3 + x * t : ℝ) : ℂ) * I) := by
  rw [airyInt_osc]; congr 1; push_cast; ring

/-- The cosine integral is the real part of the oscillatory integral. -/
theorem airyInt_integral_cos (x R : ℝ) :
    ∫ t in (0 : ℝ)..R, (Real.cos (t ^ 3 / 3 + x * t) : ℂ) =
      (((∫ t in (0 : ℝ)..R, airyInt_osc x t).re : ℝ) : ℂ) := by
  have h := intervalIntegral.intervalIntegral_re (μ := volume) (a := 0) (b := R)
    (f := fun t : ℝ => airyInt_osc x t)
    (Continuous.intervalIntegrable ((airyInt_continuous_osc x).comp continuous_ofReal) _ _)
  simp only [RCLike.re_to_complex] at h
  rw [intervalIntegral.integral_ofReal, ← h]
  congr 1
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [airyInt_osc_ofReal, exp_ofReal_mul_I_re]

/-- The sine integral is the imaginary part of the oscillatory integral. -/
theorem airyInt_integral_sin (x R : ℝ) :
    ∫ t in (0 : ℝ)..R, (Real.sin (t ^ 3 / 3 + x * t) : ℂ) =
      (((∫ t in (0 : ℝ)..R, airyInt_osc x t).im : ℝ) : ℂ) := by
  have h := intervalIntegral.intervalIntegral_im (μ := volume) (a := 0) (b := R)
    (f := fun t : ℝ => airyInt_osc x t)
    (Continuous.intervalIntegrable ((airyInt_continuous_osc x).comp continuous_ofReal) _ _)
  simp only [RCLike.im_to_complex] at h
  rw [intervalIntegral.integral_ofReal, ← h]
  congr 1
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [airyInt_osc_ofReal, exp_ofReal_mul_I_im]

/-- `Ai(x) = π⁻¹ ∫₀^∞ cos(t³/3 + xt) dt` for real `x`, as an improper integral
(DLMF 9.5.1). -/
@[dlmf 9.5.E1]
theorem airyAi_cos_integral (x : ℝ) :
    HasIntegralAtTop (fun t : ℝ => (Real.cos (t ^ 3 / 3 + x * t) : ℂ)) 0 (π * airyAi x) := by
  unfold HasIntegralAtTop
  rw [airyInt_pi_airyAi]
  simp_rw [airyInt_integral_cos]
  have h := ((continuous_ofReal.comp continuous_re).tendsto _).comp (airyInt_tendsto_osc x)
  have hv : ((-(airyInt_w x).im : ℝ) : ℂ) = (ofReal ∘ re) (I * airyInt_w x) := by simp
  rw [hv]; exact h

/-- `Bi(x) = π⁻¹ ∫₀^∞ (exp(-t³/3 + xt) + sin(t³/3 + xt)) dt` for real `x`, the first
integral absolutely convergent and the second improper (DLMF 9.5.3). -/
@[dlmf 9.5.E3]
theorem airyBi_real_integral (x : ℝ) :
    IntegrableOn (fun t : ℝ => exp (-(t : ℂ) ^ 3 / 3 + x * t)) (Ioi 0) ∧
      HasIntegralAtTop (fun t : ℝ => (Real.sin (t ^ 3 / 3 + x * t) : ℂ)) 0
        (π * airyBi x - ∫ t : ℝ in Ioi 0, exp (-(t : ℂ) ^ 3 / 3 + x * t)) := by
  refine ⟨(scorerHi_exp_integral x).1, ?_⟩
  unfold HasIntegralAtTop
  rw [airyInt_pi_airyBi]
  simp_rw [airyInt_integral_sin]
  have h := ((continuous_ofReal.comp continuous_im).tendsto _).comp (airyInt_tendsto_osc x)
  have hv : (((airyInt_w x).re : ℝ) : ℂ) = (ofReal ∘ im) (I * airyInt_w x) := by simp
  rw [hv]; exact h


/-- `Gi(x) = π⁻¹ ∫₀^∞ sin(t³/3 + xt) dt` for real `x`, as an improper integral
(DLMF 9.12.19). -/
@[dlmf 9.12.E19]
theorem scorerGi_sin_integral (x : ℝ) :
    HasIntegralAtTop (fun t : ℝ => (Real.sin (t ^ 3 / 3 + x * t) : ℂ)) 0 (π * scorerGi x) := by
  have h := (airyBi_real_integral x).2
  rw [scorerGi, mul_sub, (scorerHi_exp_integral x).2, mul_div_cancel₀ _
    (ofReal_ne_zero.mpr Real.pi_ne_zero)]
  exact h

/-- `Ai(-x) = (√x/π) ∫_{-1}^∞ cos(x^{3/2}(t³/3 + t² - 2/3)) dt` for `x > 0`, as an
improper integral (DLMF 9.5.2). -/
@[dlmf 9.5.E2]
theorem airyAi_neg_cos_integral {x : ℝ} (hx : 0 < x) :
    HasIntegralAtTop (fun t : ℝ => (Real.cos (x ^ (3 / 2 : ℝ) * (t ^ 3 / 3 + t ^ 2 - 2 / 3)) : ℂ))
      (-1) (π / Real.sqrt x * airyAi (-x)) := by
  set c := Real.sqrt x with hc
  have hc0 : 0 < c := Real.sqrt_pos.mpr hx
  have hcx : c ^ 2 = x := Real.sq_sqrt hx.le
  have h1 := airyAi_cos_integral (-x)
  unfold HasIntegralAtTop at h1 ⊢
  have hsub : ∀ R : ℝ, ∫ t in (-1 : ℝ)..R,
      (Real.cos (x ^ (3 / 2 : ℝ) * (t ^ 3 / 3 + t ^ 2 - 2 / 3)) : ℂ) =
      (c : ℂ)⁻¹ * ∫ s in (0 : ℝ)..(c * R + c), (Real.cos (s ^ 3 / 3 + -x * s) : ℂ) := by
    intro R
    have h := intervalIntegral.integral_comp_mul_add
      (fun s : ℝ => (Real.cos (s ^ 3 / 3 + -x * s) : ℂ)) hc0.ne' c (a := -1) (b := R)
    rw [show c * -1 + c = 0 by ring] at h
    rw [← ofReal_inv, ← Complex.real_smul, ← h]
    refine intervalIntegral.integral_congr fun t _ => ?_
    congr 2
    rw [rpow_three_halves_eq hx.le, ← hc, ← hcx]
    ring
  simp_rw [hsub]
  have h2 := h1.comp ((tendsto_id.const_mul_atTop hc0).atTop_add (tendsto_const_nhds (x := c)))
  have h3 := h2.const_mul (c : ℂ)⁻¹
  convert h3 using 2
  · simp
  · push_cast
    ring


/-! ### The Gaussian form 9.5.7

For `x > 0` the line `Im v = 0` of 9.5.1 is shifted to `Im v = √x` (Cauchy's theorem on a
rectangle, through a primitive); the result extends to the slit plane by the identity theorem.
-/
/-- Integral of an entire function along a line `r ↦ p + r c`, via a primitive. -/
theorem airyInt_integral_line {f g : ℂ → ℂ} (hg : ∀ w, HasDerivAt g (f w) w)
    (hf : Continuous f) (p c : ℂ) (a b : ℝ) :
    ∫ r in a..b, c * f (p + r * c) = g (p + b * c) - g (p + a * c) := by
  have hd : ∀ r : ℝ, HasDerivAt (fun r : ℝ => g (p + r * c)) (c * f (p + r * c)) r := by
    intro r
    have h := (hg (p + (r : ℂ) * c)).comp (r : ℂ)
      (((hasDerivAt_id (r : ℂ)).mul_const c).const_add p)
    simp only [Function.comp_def, id, one_mul] at h
    rw [mul_comm]
    exact h.comp_ofReal (e := fun w => g (p + w * c))
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hd r)
    (Continuous.intervalIntegrable (u := fun r : ℝ => c * f (p + r * c)) (by fun_prop) _ _)

/-- Norm of the oscillatory integrand on a vertical segment. -/
theorem airyInt_norm_osc_vert (x s b : ℝ) :
    ‖I * airyInt_osc x (s + b * I)‖ = Real.exp (-(s ^ 2 * b) + b ^ 3 / 3 - x * b) := by
  rw [norm_mul, norm_I, one_mul, airyInt_osc, norm_exp]
  congr 1
  simp only [mul_re, I_re, I_im, add_im, div_ofNat_im, mul_im, ofReal_re, ofReal_im, add_re,
    div_ofNat_re, zero_mul, one_mul, pow_succ, pow_zero, mul_one]
  ring

/-- Bound for the vertical sides of the rectangle `[-R, R] × [0, √x]`. -/
theorem airyInt_vert_bound {x c : ℝ} (hx : 0 ≤ x) (hc : 0 ≤ c) {s : ℝ} (hs : 1 ≤ s ^ 2) :
    ‖∫ b in (0 : ℝ)..c, I * airyInt_osc x (s + b * I)‖ ≤ Real.exp (c ^ 3 / 3) / s ^ 2 := by
  have hs0 : 0 < s ^ 2 := by linarith
  calc _ ≤ ∫ b in (0 : ℝ)..c, Real.exp (c ^ 3 / 3) * Real.exp (-(s ^ 2 * b)) := by
        refine intervalIntegral.norm_integral_le_of_norm_le hc (Eventually.of_forall fun b hb => ?_)
          (Continuous.intervalIntegrable (by fun_prop) _ _)
        rw [airyInt_norm_osc_vert, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hb0 : 0 ≤ b := hb.1.le
        have : b ^ 3 ≤ c ^ 3 := pow_le_pow_left₀ hb0 hb.2 3
        nlinarith [mul_nonneg hx hb0]
    _ = Real.exp (c ^ 3 / 3) * ∫ b in (0 : ℝ)..c, Real.exp (-(s ^ 2 * b)) :=
        intervalIntegral.integral_const_mul _ _
    _ ≤ Real.exp (c ^ 3 / 3) * (1 / s ^ 2) := by
        gcongr; exact airyInt_integral_exp_neg_le hs0 _
    _ = _ := by ring

/-- `osc(a) + osc(-a) = 2 cos(a³/3 + xa)` on the real axis. -/
theorem airyInt_osc_add_neg (x a : ℝ) :
    airyInt_osc x a + airyInt_osc x (-a : ℝ) = 2 * (Real.cos (a ^ 3 / 3 + x * a) : ℂ) := by
  rw [airyInt_osc_ofReal, airyInt_osc_ofReal, ofReal_cos, Complex.cos]
  push_cast; ring_nf

/-- The oscillatory integrand on the line `Im v = √x`. -/
theorem airyInt_osc_shift {x : ℝ} (hx : 0 ≤ x) (a : ℝ) :
    airyInt_osc x (a + Real.sqrt x * I) = exp (-(2 / 3 * (Real.sqrt x : ℂ) ^ 3)) *
      (exp (-(Real.sqrt x : ℂ) * (a : ℂ) ^ 2) * exp ((a : ℂ) ^ 3 / 3 * I)) := by
  have hc : ((Real.sqrt x : ℝ) : ℂ) ^ 2 = x := by rw [← ofReal_pow, Real.sq_sqrt hx]
  rw [airyInt_osc, ← exp_add, ← exp_add]
  congr 1
  rw [← hc]
  have h3 : I ^ 3 = -I := by rw [pow_succ, I_sq]; ring
  have h4 : I ^ 4 = 1 := by rw [show 4 = 2 * 2 by rfl, pow_mul, I_sq]; ring
  ring_nf
  rw [I_sq, h3, h4]
  ring


/-- The Gaussian–cosine integrand is dominated by the Gaussian. -/
theorem airyInt_norm_gauss_cos_le (s : ℂ) (t : ℝ) :
    ‖exp (-s * (t : ℂ) ^ 2) * cos ((t : ℂ) ^ 3 / 3)‖ ≤ Real.exp (-s.re * t ^ 2) := by
  rw [norm_mul, norm_exp, show (t : ℂ) ^ 3 / 3 = ((t ^ 3 / 3 : ℝ) : ℂ) by push_cast; ring,
    ← ofReal_cos, norm_real, Real.norm_eq_abs]
  have h1 := Real.abs_cos_le_one (t ^ 3 / 3)
  have h2 : (-s * (t : ℂ) ^ 2).re = -s.re * t ^ 2 := by
    rw [show (t : ℂ) ^ 2 = ((t ^ 2 : ℝ) : ℂ) by push_cast; ring, re_mul_ofReal, neg_re]
  rw [h2]
  calc _ ≤ Real.exp (-s.re * t ^ 2) * 1 := by gcongr
    _ = _ := mul_one _

/-- Integrability of the Gaussian–cosine integrand for `Re s > 0`. -/
theorem airyInt_integrable_gauss_cos {s : ℂ} (hs : 0 < s.re) :
    Integrable (fun t : ℝ => exp (-s * (t : ℂ) ^ 2) * cos ((t : ℂ) ^ 3 / 3)) :=
  (integrable_exp_neg_mul_sq hs).mono' (Continuous.aestronglyMeasurable (by fun_prop))
    (Eventually.of_forall fun t => airyInt_norm_gauss_cos_le s t)

/-- Symmetrization of an integral over `[-R, R]`. -/
theorem airyInt_integral_symm (f : ℝ → ℂ) (hf : Continuous f) (R : ℝ) :
    ∫ a in (-R)..R, f a = ∫ a in (0 : ℝ)..R, (f a + f (-a)) := by
  rw [intervalIntegral.integral_add (f := f) (g := fun a => f (-a)) (hf.intervalIntegrable _ _)
    ((hf.comp continuous_neg).intervalIntegrable _ _), intervalIntegral.integral_comp_neg, neg_zero,
    add_comm, intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable _ _)
      (hf.intervalIntegrable _ _)]

/-- The rectangle identity for the entire integrand `airyInt_osc x` with primitive `G`: the
integrals over `[-R, R]` and `[-R, R] + ci` differ by the two vertical edge integrals. -/
private lemma airyInt_gauss_rect {x : ℝ} {G : ℂ → ℂ} (hG : ∀ w, HasDerivAt G (airyInt_osc x w) w)
    (hoc : Continuous (airyInt_osc x)) (c R : ℝ) :
    (∫ a in (-R)..R, airyInt_osc x a) - ∫ a in (-R)..R, airyInt_osc x (a + c * I) =
      -(∫ b in (0 : ℝ)..c, I * airyInt_osc x (R + b * I)) +
        ∫ b in (0 : ℝ)..c, I * airyInt_osc x ((-R : ℝ) + b * I) := by
  have h1 := airyInt_integral_line hG hoc 0 1 (-R) R
  have h2 := airyInt_integral_line hG hoc (c * I) 1 (-R) R
  have h3 := airyInt_integral_line hG hoc R I 0 c
  have h4 := airyInt_integral_line hG hoc (-R : ℝ) I 0 c
  simp only [one_mul, mul_one, zero_add, ofReal_zero, zero_mul, add_zero] at h1 h2 h3 h4
  have e2 : ∫ a in (-R)..R, airyInt_osc x (a + c * I) =
      ∫ r in (-R)..R, airyInt_osc x (c * I + r) := by
    refine intervalIntegral.integral_congr fun a _ => ?_; simp only [add_comm]
  rw [e2, h1, h2, h3, h4]
  push_cast
  ring_nf

/-- The two vertical edge integrals of `airyInt_gauss_rect` tend to `0` as `R → ∞`. -/
private lemma airyInt_gauss_vert_tendsto {x c : ℝ} (hx : 0 ≤ x) (hc : 0 ≤ c) :
    Tendsto (fun R : ℝ => -(∫ b in (0 : ℝ)..c, I * airyInt_osc x (R + b * I)) +
      ∫ b in (0 : ℝ)..c, I * airyInt_osc x ((-R : ℝ) + b * I)) atTop (𝓝 0) := by
  set V : ℝ → ℂ := fun s => ∫ b in (0 : ℝ)..c, I * airyInt_osc x (s + b * I)
  have hV : ∀ s : ℝ, 1 ≤ s ^ 2 → ‖V s‖ ≤ Real.exp (c ^ 3 / 3) / s ^ 2 := fun s hs =>
    airyInt_vert_bound hx hc hs
  have hb : Tendsto (fun R : ℝ => Real.exp (c ^ 3 / 3) / R ^ 2) atTop (𝓝 0) :=
    (tendsto_const_nhds (x := Real.exp (c ^ 3 / 3))).div_atTop (tendsto_pow_atTop two_ne_zero)
  have h1 : Tendsto V atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [eventually_ge_atTop 1] with R hR
    exact hV R (by nlinarith)
  have h2 : Tendsto (fun R => V (-R)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [eventually_ge_atTop 1] with R hR
    have := hV (-R) (by nlinarith)
    rwa [neg_sq] at this
  have h := h1.neg.add h2
  rw [neg_zero, add_zero] at h
  exact h

/-- Real case of 9.5.7: `Ai(x) = e^{-ζ}/π ∫₀^∞ e^{-√x t²} cos(t³/3) dt` for `x > 0`. -/
theorem airyInt_gauss_real {x : ℝ} (hx : 0 < x) :
    airyAi x = exp (-(2 / 3 * (Real.sqrt x : ℂ) ^ 3)) / π *
      ∫ t : ℝ in Ioi 0, exp (-(Real.sqrt x : ℂ) * (t : ℂ) ^ 2) * cos ((t : ℂ) ^ 3 / 3) := by
  set c := Real.sqrt x with hcdef
  have hc0 : 0 < c := Real.sqrt_pos.mpr hx
  obtain ⟨G, hG⟩ : ∃ G : ℂ → ℂ, ∀ w, HasDerivAt G (airyInt_osc x w) w := by
    have hd : Differentiable ℂ (airyInt_osc x) := by unfold airyInt_osc; fun_prop
    obtain ⟨g, hg⟩ := hd.isExactOn_univ
    exact ⟨g, fun w => hg w (mem_univ w)⟩
  have hoc := airyInt_continuous_osc x
  set k : ℝ → ℂ := fun t => exp (-(c : ℂ) * (t : ℂ) ^ 2) * cos ((t : ℂ) ^ 3 / 3)
  have hrect := airyInt_gauss_rect hG hoc c
  -- limits
  have hlim1 : Tendsto (fun R : ℝ => ∫ a in (-R)..R, airyInt_osc x a) atTop
      (𝓝 (2 * (π * airyAi x))) := by
    have h := (airyAi_cos_integral x).const_mul 2
    refine h.congr fun R => ?_
    rw [airyInt_integral_symm (fun a : ℝ => airyInt_osc x a) (hoc.comp continuous_ofReal),
      ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun a _ => ?_
    rw [airyInt_osc_add_neg]
  have hkint : Integrable k := airyInt_integrable_gauss_cos (s := (c : ℂ)) (by simpa using hc0)
  have hlim2 : Tendsto (fun R : ℝ => ∫ a in (-R)..R, airyInt_osc x (a + c * I)) atTop
      (𝓝 (2 * exp (-(2 / 3 * (c : ℂ) ^ 3)) * ∫ t : ℝ in Ioi 0, k t)) := by
    have h := (intervalIntegral_tendsto_integral_Ioi 0 hkint.integrableOn tendsto_id).const_mul
      (2 * exp (-(2 / 3 * (c : ℂ) ^ 3)))
    refine h.congr fun R => ?_
    have hcont : Continuous fun a : ℝ => airyInt_osc x (a + c * I) := by
      unfold airyInt_osc; fun_prop
    rw [airyInt_integral_symm (fun a : ℝ => airyInt_osc x (a + c * I)) hcont,
      ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun a _ => ?_
    simp only [k]
    rw [hcdef, airyInt_osc_shift hx.le, airyInt_osc_shift hx.le, ← hcdef, Complex.cos]
    push_cast
    ring_nf
  have hVlim := airyInt_gauss_vert_tendsto (x := x) hx.le hc0.le
  have huniq := tendsto_nhds_unique (hlim1.sub hlim2) (hVlim.congr fun R => (hrect R).symm)
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [div_mul_eq_mul_div, eq_div_iff hpi]
  linear_combination huniq / 2


/-- Identity theorem from the positive reals: two functions holomorphic on an open preconnected
set containing `1` that agree at its positive real points agree on the whole set. -/
theorem airyInt_eqOn_of_pos_real {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    (h1 : (1 : ℂ) ∈ U) {f g : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    (heq : ∀ x : ℝ, 0 < x → (x : ℂ) ∈ U → f x = g x) : EqOn f g U := by
  refine (hf.analyticOnNhd hU).eqOn_of_preconnected_of_frequently_eq (hg.analyticOnNhd hU) hUc h1 ?_
  have ht : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[≠] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have := (continuous_ofReal.tendsto (1 : ℝ)).mono_left
        (nhdsWithin_le_nhds (s := ({1}ᶜ : Set ℝ)))
      rwa [ofReal_one] at this
    · filter_upwards [self_mem_nhdsWithin] with r hr
      simpa using hr
  apply ht.frequently
  apply Eventually.frequently
  have hU1 : (fun r : ℝ => (r : ℂ)) ⁻¹' U ∈ 𝓝 (1 : ℝ) :=
    continuous_ofReal.continuousAt.preimage_mem_nhds (by rw [ofReal_one]; exact hU.mem_nhds h1)
  filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds (zero_lt_one' ℝ)), nhdsWithin_le_nhds hU1]
    with r hr hrU
  exact heq r hr hrU

/-- `Re z^{1/2} > 0` on the slit plane. -/
theorem airyInt_re_sqrt_pos {z : ℂ} (hz : z ∈ slitPlane) : 0 < (z ^ (1 / 2 : ℂ)).re := by
  have hz0 := slitPlane_ne_zero hz
  rw [cpow_def_of_ne_zero hz0, exp_re]
  refine mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩)
  all_goals
    have h1 := neg_pi_lt_arg z
    have h2 : arg z < π := lt_of_le_of_ne (arg_le_pi z) (mem_slitPlane_iff_arg.mp hz).1
    simp [mul_im, log_re, log_im]
    linarith [Real.pi_pos]


/-- `x^{1/2}` for positive real `x`. -/
theorem airyInt_ofReal_cpow_half {x : ℝ} (hx : 0 ≤ x) : (x : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt x : ℂ) := by
  rw [Real.sqrt_eq_rpow, ofReal_cpow hx]; push_cast; ring_nf

/-- `ζ(x) = (2/3) (√x)³` for positive real `x`. -/
theorem airyInt_zeta_ofReal {x : ℝ} (hx : 0 ≤ x) :
    airyZetaComplex x = 2 / 3 * (Real.sqrt x : ℂ) ^ 3 := by
  rw [airyZetaComplex, show (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow hx,
    rpow_three_halves_eq hx]
  push_cast; ring

/-! ### The cubic form 9.5.6

For `x > 0` the substitution `s = t³/3` turns 9.5.6 into Schläfli's integral for `K_{1/3}`
(9.6.2); the sector `|ph z| < π/6` follows by the identity theorem, and `z = 0` by continuity.
-/

section CubicForm

open DLMF.Bessel
/-- The substitution `s = t³/3` in Schläfli's integral for `K_{-1/3}(ζ)`: the transformed
integrand is `3 · 3^{2/3} exp(-t³/3 - x³/(3t³))`. -/
private lemma airyInt_cubic_pt {x : ℝ} (hx : 0 < x) {t : ℝ} (ht : 0 < t) :
    (|(3 : ℝ)| * t ^ ((3 : ℝ) - 1)) •
      (exp (-((3⁻¹ * t ^ (3 : ℝ) : ℝ) : ℂ) -
          (airyZeta x : ℂ) ^ 2 / (4 * ((3⁻¹ * t ^ (3 : ℝ) : ℝ) : ℂ))) *
        ((3⁻¹ * t ^ (3 : ℝ) : ℝ) : ℂ) ^ (-(-1 / 3 : ℂ) - 1)) =
      ((3 * (3 : ℝ) ^ (2 / 3 : ℝ) : ℝ) : ℂ) *
        exp (-(t : ℂ) ^ 3 / 3 - (x : ℂ) ^ 3 / (3 * (t : ℂ) ^ 3)) := by
  have ht3 : t ^ (3 : ℝ) = t ^ 3 := Real.rpow_natCast t 3
  have ht2 : t ^ ((3 : ℝ) - 1) = t ^ 2 := by
    rw [show (3 : ℝ) - 1 = (2 : ℕ) by norm_num, Real.rpow_natCast]
  rw [ht3, ht2, abs_of_pos (by norm_num : (0 : ℝ) < 3), Complex.real_smul]
  have hs : 0 < 3⁻¹ * t ^ 3 := by positivity
  have hpow : ((3⁻¹ * t ^ 3 : ℝ) : ℂ) ^ (-(-1 / 3 : ℂ) - 1) =
      (((3 : ℝ) ^ (2 / 3 : ℝ) * (t ^ 2)⁻¹ : ℝ) : ℂ) := by
    rw [show -(-1 / 3 : ℂ) - 1 = ((-(2 / 3) : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow hs.le]
    congr 1
    rw [Real.mul_rpow (by norm_num) (by positivity), Real.inv_rpow (by norm_num),
      ← Real.rpow_neg (by norm_num), neg_neg, ← Real.rpow_natCast t 3, ← Real.rpow_mul ht.le,
      show ((3 : ℕ) : ℝ) * -(2 / 3) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg ht.le,
      Real.rpow_natCast]
  have hX2 : (airyZeta x : ℂ) ^ 2 = 4 * ((x : ℂ) ^ 3 / 9) := by
    rw [← airyZeta_sq_div_four hx.le]; ring
  have htc : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  have hexp : -((3⁻¹ * t ^ 3 : ℝ) : ℂ) - (airyZeta x : ℂ) ^ 2 / (4 * ((3⁻¹ * t ^ 3 : ℝ) : ℂ)) =
      -(t : ℂ) ^ 3 / 3 - (x : ℂ) ^ 3 / (3 * (t : ℂ) ^ 3) := by
    rw [hX2]; push_cast; field_simp; ring
  rw [hpow, hexp]
  push_cast
  field_simp

/-- Real case of 9.5.6, via Schläfli's integral for `K_{1/3}`. -/
theorem airyInt_cubic_real {x : ℝ} (hx : 0 < x) :
    airyAi x = Real.sqrt 3 / (2 * π) *
      ∫ t : ℝ in Ioi 0, exp (-(t : ℂ) ^ 3 / 3 - (x : ℂ) ^ 3 / (3 * (t : ℂ) ^ 3)) := by
  set X := airyZeta x with hXdef
  have hX : 0 < X := airyZeta_pos hx
  have hS := besselK_ofReal_eq_integral_schlafli hX (-1 / 3)
  have hK : besselK (-1 / 3) X = besselK (1 / 3) X := by
    rw [show (-1 / 3 : ℂ) = -(1 / 3) by ring, besselK_neg _ (Or.inl (by simpa using hX))]
  set h : ℝ → ℂ := fun s => exp (-(s : ℂ) - (X : ℂ) ^ 2 / (4 * s)) * (s : ℂ) ^ (-(-1 / 3 : ℂ) - 1)
    with hh
  have e1 := integral_comp_mul_left_Ioi h 0 (b := 3⁻¹) (by norm_num)
  have e2 := integral_comp_rpow_Ioi (fun y => h (3⁻¹ * y)) (p := 3) (by norm_num)
  rw [mul_zero, inv_inv] at e1
  have hpt : ∀ t : ℝ, 0 < t → (|(3 : ℝ)| * t ^ ((3 : ℝ) - 1)) • h (3⁻¹ * t ^ (3 : ℝ)) =
      ((3 * (3 : ℝ) ^ (2 / 3 : ℝ) : ℝ) : ℂ) *
        exp (-(t : ℂ) ^ 3 / 3 - (x : ℂ) ^ 3 / (3 * (t : ℂ) ^ 3)) :=
    fun t ht => airyInt_cubic_pt hx ht
  have hF : (3 : ℂ) * ∫ s : ℝ in Ioi 0, h s = ((3 * (3 : ℝ) ^ (2 / 3 : ℝ) : ℝ) : ℂ) *
      ∫ t : ℝ in Ioi 0, exp (-(t : ℂ) ^ 3 / 3 - (x : ℂ) ^ 3 / (3 * (t : ℂ) ^ 3)) := by
    calc (3 : ℂ) * ∫ s : ℝ in Ioi 0, h s = ∫ y : ℝ in Ioi 0, h (3⁻¹ * y) := by
          rw [e1, Complex.real_smul]; push_cast; ring
      _ = _ := e2.symm
      _ = ∫ t : ℝ in Ioi 0, ((3 * (3 : ℝ) ^ (2 / 3 : ℝ) : ℝ) : ℂ) *
            exp (-(t : ℂ) ^ 3 / 3 - (x : ℂ) ^ 3 / (3 * (t : ℂ) ^ 3)) :=
          setIntegral_congr_fun measurableSet_Ioi hpt
      _ = _ := integral_const_mul _ _
  have hhalf : ((X : ℂ) / 2) ^ (-1 / 3 : ℂ) = ((((3 : ℝ) ^ (-(1 / 3 : ℝ)) * Real.sqrt x)⁻¹ : ℝ) : ℂ) := by
    rw [show (-1 / 3 : ℂ) = ((-(1 / 3) : ℝ) : ℂ) by push_cast; ring, hXdef,
      half_airyZeta_cpow hx.le, Real.rpow_neg (by unfold airyZeta; positivity),
      half_airyZeta_rpow_third hx.le]
  rw [airyAi_eq_besselK hx, ← hXdef, ← hK, hS, hhalf]
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have h33 : (3 : ℝ) ^ (-(1 / 3 : ℝ)) * (3 : ℝ) ^ (1 : ℝ) = (3 : ℝ) ^ (2 / 3 : ℝ) := by
    rw [← Real.rpow_add (by norm_num)]; norm_num
  have h3p : 0 < (3 : ℝ) ^ (-(1 / 3 : ℝ)) := by positivity
  rw [Real.rpow_one] at h33
  have hI : ∫ s : ℝ in Ioi 0, h s = (((3 : ℝ) ^ (2 / 3 : ℝ) : ℝ) : ℂ) *
      ∫ t : ℝ in Ioi 0, exp (-(t : ℂ) ^ 3 / 3 - (x : ℂ) ^ 3 / (3 * (t : ℂ) ^ 3)) := by
    have := hF; push_cast at this; linear_combination this / 3
  rw [hI, sqrt_div_three hx.le, ← h33]
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hs3 : (Real.sqrt 3 : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hsx' : (Real.sqrt x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hsx.ne'
  push_cast
  field_simp


/-- The open sector `|arg z| < α` (origin excluded), `0 < α ≤ π`. -/
noncomputable def airyInt_sector (α : ℝ) : Set ℂ := slitPlane ∩ (fun z : ℂ => |arg z|) ⁻¹' Iio α

/-- The sector is open. -/
theorem airyInt_isOpen_sector (α : ℝ) : IsOpen (airyInt_sector α) :=
  ContinuousOn.isOpen_inter_preimage (fun _ hz => (continuousAt_arg hz).abs.continuousWithinAt)
    isOpen_slitPlane isOpen_Iio

/-- Membership in the sector. -/
theorem airyInt_mem_sector {α : ℝ} (hα : α ≤ π) {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < α) :
    z ∈ airyInt_sector α := by
  refine ⟨mem_slitPlane_iff_arg.mpr ⟨fun h => ?_, hz0⟩, hz⟩
  rw [h, abs_of_pos Real.pi_pos] at hz; linarith

/-- The sector is preconnected (the image of a strip under `exp`). -/
theorem airyInt_isPreconnected_sector {α : ℝ} (hα : α ≤ π) :
    IsPreconnected (airyInt_sector α) := by
  have hS : IsPreconnected (im ⁻¹' Ioo (-α) α) :=
    ((convex_Ioo _ _).linear_preimage imLm).isPreconnected
  have himg : exp '' (im ⁻¹' Ioo (-α) α) = airyInt_sector α := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hw' : -α < w.im ∧ w.im < α := hw
      have hlog : log (exp w) = w := log_exp (by linarith) (by linarith)
      have harg : arg (exp w) = w.im := by rw [← log_im, hlog]
      exact airyInt_mem_sector hα (exp_ne_zero w) (by rw [harg, abs_lt]; exact hw')
    · rintro ⟨hz, hz'⟩
      have hz0 : z ≠ 0 := slitPlane_ne_zero hz
      refine ⟨log z, ?_, exp_log hz0⟩
      have : |arg z| < α := hz'
      rw [mem_preimage, log_im, mem_Ioo]; exact abs_lt.mp this
  rw [← himg]
  exact hS.image _ continuous_exp.continuousOn

/-- `Re z³ ≥ 0` for `|arg z| ≤ π/6`. -/
theorem airyInt_re_cube_nonneg {z : ℂ} (hz : |arg z| ≤ π / 6) : 0 ≤ (z ^ 3).re := by
  have h : z ^ 3 = ((‖z‖ ^ 3 : ℝ) : ℂ) * exp (((3 * arg z : ℝ) : ℂ) * I) := by
    conv_lhs => rw [← norm_mul_exp_arg_mul_I z]
    rw [mul_pow, ← exp_nat_mul]; push_cast; ring_nf
  rw [h, re_ofReal_mul, exp_ofReal_mul_I_re]
  refine mul_nonneg (by positivity) (Real.cos_nonneg_of_mem_Icc ⟨?_, ?_⟩) <;>
    linarith [abs_le.mp hz]

/-- The cubic integrand of 9.5.6 is dominated by `e^{-t³/3}` when `Re w³ ≥ 0`. -/
theorem airyInt_norm_cubic_le {w : ℂ} (hw : 0 ≤ (w ^ 3).re) {t : ℝ} (ht : 0 < t) :
    ‖exp (-(t : ℂ) ^ 3 / 3 - w ^ 3 / (3 * (t : ℂ) ^ 3))‖ ≤ Real.exp (-(1 / 3) * t ^ 3) := by
  rw [norm_exp]
  apply Real.exp_le_exp.mpr
  have : (w ^ 3 / (3 * (t : ℂ) ^ 3)).re = (w ^ 3).re / (3 * t ^ 3) := by
    rw [show (3 * (t : ℂ) ^ 3) = ((3 * t ^ 3 : ℝ) : ℂ) by push_cast; ring, div_ofReal_re]
  rw [sub_re, this]
  have h1 : (-(t : ℂ) ^ 3 / 3).re = -(1 / 3) * t ^ 3 := by
    rw [show (-(t : ℂ) ^ 3 / 3) = ((-(1 / 3) * t ^ 3 : ℝ) : ℂ) by push_cast; ring, ofReal_re]
  rw [h1]
  have : 0 ≤ (w ^ 3).re / (3 * t ^ 3) := by positivity
  linarith

/-- The majorant `e^{-t³/3}` is integrable on `(0, ∞)`. -/
theorem airyInt_integrableOn_exp_neg_cube :
    IntegrableOn (fun t : ℝ => Real.exp (-(1 / 3) * t ^ 3)) (Ioi 0) := by
  have := scorerAsym_integrableOn_pow_exp 0 0 (b := 1 / 3) (by norm_num)
  refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp

/-- The case `z = 0` of 9.5.6, by continuity from the positive axis. -/
theorem airyInt_cubic_zero :
    airyAi 0 = Real.sqrt 3 / (2 * π) *
      ∫ t : ℝ in Ioi 0, exp (-(t : ℂ) ^ 3 / 3 - (0 : ℂ) ^ 3 / (3 * (t : ℂ) ^ 3)) := by
  set Φ : ℂ → ℝ → ℂ := fun z t => exp (-(t : ℂ) ^ 3 / 3 - z ^ 3 / (3 * (t : ℂ) ^ 3)) with hΦ
  have h1 : Tendsto (fun x : ℝ => airyAi x) (𝓝[>] 0) (𝓝 (airyAi 0)) := by
    have := ((differentiable_airyAi.continuous.comp continuous_ofReal).tendsto 0).mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa [Function.comp_def] using this
  have h2 : Tendsto (fun x : ℝ => ∫ t : ℝ in Ioi 0, Φ x t) (𝓝[>] 0)
      (𝓝 (∫ t : ℝ in Ioi 0, Φ 0 t)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun t => Real.exp (-(1 / 3) * t ^ 3))
      (Eventually.of_forall fun x => Measurable.aestronglyMeasurable (by simp only [hΦ]; fun_prop))
      ?_ airyInt_integrableOn_exp_neg_cube ?_
    · filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
      exact airyInt_norm_cubic_le (by rw [← ofReal_pow, ofReal_re]; positivity) ht
    · refine Eventually.of_forall fun t => ?_
      have hc : Continuous fun x : ℝ => Φ x t := by simp only [hΦ]; fun_prop
      simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have h3 := (h2.const_mul (Real.sqrt 3 / (2 * π) : ℂ))
  refine tendsto_nhds_unique h1 (h3.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
  exact (airyInt_cubic_real hx).symm

end CubicForm

/-- `Ai(z) = (√3/(2π)) ∫₀^∞ exp(-t³/3 - z³/(3t³)) dt` for `|arg z| < π/6`
(DLMF 9.5.6). -/
@[dlmf 9.5.E6]
theorem airyAi_cubic_integral {z : ℂ} (hz : |arg z| < π / 6) :
    airyAi z = Real.sqrt 3 / (2 * π) *
      ∫ t : ℝ in Ioi 0, exp (-(t : ℂ) ^ 3 / 3 - z ^ 3 / (3 * (t : ℂ) ^ 3)) := by
  by_cases hz0 : z = 0
  · subst hz0; exact airyInt_cubic_zero
  have hπ := Real.pi_pos
  have hα : π / 6 ≤ π := by linarith
  set U := airyInt_sector (π / 6)
  set Φ : ℂ → ℝ → ℂ := fun z t => exp (-(t : ℂ) ^ 3 / 3 - z ^ 3 / (3 * (t : ℂ) ^ 3)) with hΦ
  have hint : DifferentiableOn ℂ (fun z => ∫ t : ℝ in Ioi 0, Φ z t) U := by
    refine differentiableOn_integral_Ioi_of_locally_dominated (airyInt_isOpen_sector _) 0
      (fun z _ => (Measurable.aestronglyMeasurable (by simp only [hΦ]; fun_prop)))
      (Eventually.of_forall fun t w _ => ?_) (fun z0 _ => ?_)
    · refine DifferentiableAt.differentiableWithinAt ?_
      simp only [hΦ]; fun_prop
    · refine ⟨U, (airyInt_isOpen_sector _).mem_nhds ‹_›, fun t => Real.exp (-(1 / 3) * t ^ 3),
        ?_, ?_⟩
      · have := scorerAsym_integrableOn_pow_exp 0 0 (b := 1 / 3) (by norm_num)
        refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
        simp
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t) w hw
        rw [hΦ, norm_exp]
        apply Real.exp_le_exp.mpr
        have hw3 := airyInt_re_cube_nonneg hw.2.le
        have : (w ^ 3 / (3 * (t : ℂ) ^ 3)).re = (w ^ 3).re / (3 * t ^ 3) := by
          rw [show (3 * (t : ℂ) ^ 3) = ((3 * t ^ 3 : ℝ) : ℂ) by push_cast; ring, div_ofReal_re]
        rw [sub_re, this]
        have h1 : (-(t : ℂ) ^ 3 / 3).re = -(1 / 3) * t ^ 3 := by
          rw [show (-(t : ℂ) ^ 3 / 3) = ((-(1 / 3) * t ^ 3 : ℝ) : ℂ) by push_cast; ring, ofReal_re]
        rw [h1]
        have : 0 ≤ (w ^ 3).re / (3 * t ^ 3) := by positivity
        linarith
  have hg : DifferentiableOn ℂ (fun z => Real.sqrt 3 / (2 * π) * ∫ t : ℝ in Ioi 0, Φ z t) U :=
    hint.const_mul _
  have h1U : (1 : ℂ) ∈ U := airyInt_mem_sector hα one_ne_zero (by simp; positivity)
  have h := airyInt_eqOn_of_pos_real (airyInt_isOpen_sector _) (airyInt_isPreconnected_sector hα)
    h1U differentiable_airyAi.differentiableOn hg
    (fun x hx _ => by rw [airyInt_cubic_real hx]) (airyInt_mem_sector hα hz0 hz)
  exact h

/-- `Ai(z) = (e^{-ζ}/π) ∫₀^∞ exp(-z^{1/2} t²) cos(t³/3) dt` for `|arg z| < π`, with
`ζ = (2/3) z^{3/2}` (DLMF 9.5.7). -/
@[dlmf 9.5.E7]
theorem airyAi_gaussian_cos_integral {z : ℂ} (hz : z ∈ slitPlane) :
    airyAi z = exp (-airyZetaComplex z) / π *
      ∫ t : ℝ in Ioi 0, exp (-z ^ (1 / 2 : ℂ) * (t : ℂ) ^ 2) * cos ((t : ℂ) ^ 3 / 3) := by
  set Φ : ℂ → ℝ → ℂ := fun z t => exp (-z ^ (1 / 2 : ℂ) * (t : ℂ) ^ 2) * cos ((t : ℂ) ^ 3 / 3)
    with hΦ
  have hint : DifferentiableOn ℂ (fun z => ∫ t : ℝ in Ioi 0, Φ z t) slitPlane := by
    refine differentiableOn_integral_Ioi_of_locally_dominated isOpen_slitPlane 0
      (fun z _ => Continuous.aestronglyMeasurable (by simp only [hΦ]; fun_prop))
      (Eventually.of_forall fun t w hw => ?_) (fun z0 hz0 => ?_)
    · refine DifferentiableAt.differentiableWithinAt ?_
      simp only [hΦ]
      exact ((((differentiableAt_id.cpow (differentiableAt_const _) hw).neg).mul
        (differentiableAt_const _)).cexp).mul (differentiableAt_const _)
    · set δ := (z0 ^ (1 / 2 : ℂ)).re / 2
      have hδ : 0 < δ := half_pos (airyInt_re_sqrt_pos hz0)
      have hc : ContinuousAt (fun w : ℂ => (w ^ (1 / 2 : ℂ)).re) z0 :=
        continuous_re.continuousAt.comp
          (differentiableAt_id.cpow (differentiableAt_const _) hz0).continuousAt
      refine ⟨(fun w : ℂ => (w ^ (1 / 2 : ℂ)).re) ⁻¹' Ioi δ,
        hc.preimage_mem_nhds (Ioi_mem_nhds (half_lt_self (airyInt_re_sqrt_pos hz0))), fun t => Real.exp (-δ * t ^ 2),
        (integrable_exp_neg_mul_sq hδ).integrableOn, Eventually.of_forall fun t w hw => ?_⟩
      refine (airyInt_norm_gauss_cos_le _ t).trans (Real.exp_le_exp.mpr ?_)
      have hw' : δ < (w ^ (1 / 2 : ℂ)).re := hw
      nlinarith [sq_nonneg t]
  have hg : DifferentiableOn ℂ (fun z => exp (-airyZetaComplex z) / π *
      ∫ t : ℝ in Ioi 0, Φ z t) slitPlane := fun w hw =>
    ((((airyRot_differentiableAt_zeta hw).neg.cexp).div_const _).differentiableWithinAt).mul
      (hint w hw)
  have h := airyInt_eqOn_of_pos_real isOpen_slitPlane (starConvex_one_slitPlane.isPathConnected one_mem_slitPlane).isConnected.isPreconnected
    one_mem_slitPlane differentiable_airyAi.differentiableOn hg
    (fun x hx _ => by
      rw [airyInt_gauss_real hx, airyInt_zeta_ofReal hx.le]
      simp only [hΦ, airyInt_ofReal_cpow_half hx.le]) hz
  exact h

/-- `log (r e^{iθ}) = log r + iθ` for `r > 0`, `|θ| < π`. -/
theorem airyInt_log_ofReal_mul_exp {r : ℝ} (hr : 0 < r) {θ : ℝ} (hθ : |θ| < π) :
    log ((r : ℂ) * exp (θ * I)) = Real.log r + θ * I := by
  rw [log_ofReal_mul hr (exp_ne_zero _), log_exp (by simp; linarith [neg_abs_le θ])
    (by simp; linarith [le_abs_self θ])]

/-- The pointwise substitution behind 9.5.8. -/
theorem airyInt_laplace_pointwise {z : ℂ} (hz0 : z ≠ 0) {θ : ℝ} (hθ : |θ| < π)
    (hΛ : log 2 + airyLogZeta z = ((log 2 + airyLogZeta z).re : ℂ) - θ * I) {r : ℝ} (hr : 0 < r) :
    Complex.exp (-(((Real.exp (log 2 + airyLogZeta z).re : ℝ) : ℂ) * r)) •
        airyRot_kernel (5 / 6) (-1 / 6) ((r : ℂ) * exp (θ * I)) =
      exp ((log 2 + airyLogZeta z) / 6 + log 2 / 6) *
        (exp (-((Real.exp (log 2 + airyLogZeta z).re * r : ℝ) : ℂ)) *
          (((Real.exp (log 2 + airyLogZeta z).re * r : ℝ) : ℂ) ^ (-1 / 6 : ℂ)) *
          (2 + ((Real.exp (log 2 + airyLogZeta z).re * r : ℝ) : ℂ) / airyZetaComplex z) ^
            (-1 / 6 : ℂ)) := by
  set Λ := log 2 + airyLogZeta z with hΛdef
  set ρ := Λ.re
  have hζ : airyZetaComplex z = exp Λ / 2 := by
    rw [hΛdef, exp_log_two_add_airyLogZeta hz0]; ring
  set v : ℂ := (r : ℂ) * exp (θ * I)
  set w : ℂ := 1 + v
  have hv0 : v ≠ 0 := airyRot_ofReal_mul_exp_ne_zero hr θ
  have hw : w ∈ slitPlane := airySt_one_add_mem hr.le hθ
  have hw0 : w ≠ 0 := slitPlane_ne_zero hw
  have hcr : 0 < Real.exp ρ * r := by positivity
  have h2w : 2 + ((Real.exp ρ * r : ℝ) : ℂ) / airyZetaComplex z = ((2 : ℝ) : ℂ) * w := by
    rw [hζ]
    have : ((Real.exp ρ * r : ℝ) : ℂ) / (exp Λ / 2) = 2 * v := by
      rw [show v = (r : ℂ) * exp (θ * I) from rfl, hΛ]
      push_cast
      rw [exp_sub]
      field_simp
    rw [this]; push_cast; ring
  rw [h2w, smul_eq_mul, airyRot_kernel, cpow_def_of_ne_zero hv0, cpow_def_of_ne_zero hw0,
    cpow_def_of_ne_zero (ofReal_ne_zero.mpr hcr.ne'),
    cpow_def_of_ne_zero (mul_ne_zero (by norm_num) hw0),
    log_ofReal_mul (by norm_num) hw0, ← ofReal_log hcr.le, Real.log_mul (Real.exp_pos _).ne' hr.ne',
    Real.log_exp, airyInt_log_ofReal_mul_exp hr hθ]
  simp only [← exp_add]
  congr 1
  rw [show ((Real.log 2 : ℝ) : ℂ) = log 2 by rw [ofReal_log (by norm_num)]; norm_num]
  have hρ : (ρ : ℂ) = Λ + θ * I := by linear_combination -hΛ
  push_cast
  rw [hρ]
  ring


/-- The Laplace-type integral `Ai(z) = e^{-ζ} ζ^{-1/6} / (√π 48^{1/6} Γ(5/6))
∫₀^∞ e^{-t} t^{-1/6} (2 + t/ζ)^{-1/6} dt` for `|arg z| < 2π/3` (DLMF 9.5.8). -/
@[dlmf 9.5.E8]
theorem airyAi_laplace_integral {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < 2 * π / 3) :
    airyAi z = exp (-airyZetaComplex z) * exp (-airyLogZeta z / 6) /
      (Real.sqrt π * (48 : ℂ) ^ (1 / 6 : ℂ) * Gamma (5 / 6)) *
      ∫ t : ℝ in Ioi 0, exp (-t : ℂ) * (t : ℂ) ^ (-1 / 6 : ℂ) *
        (2 + (t : ℂ) / airyZetaComplex z) ^ (-1 / 6 : ℂ) := by
  set θ : ℝ := -(3 / 2 * arg z) with hθdef
  have hθ : |θ| < π := by
    rw [hθdef, abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]; linarith
  have hzθ : |3 / 2 * arg z + θ| < π / 2 := by
    rw [hθdef, add_neg_cancel, abs_zero]; positivity
  have h := airyRot_eq_of_anchor differentiable_airyAi _ _ (5 / 6) (-1 / 6) (by norm_num)
    (fun w hw harg => airyRot_airyAi_anchor hw harg) hθ hz0 hzθ
  rw [h]
  set Λ := log 2 + airyLogZeta z with hΛdef
  set ρ := Λ.re with hρdef
  have hΛ : Λ = (ρ : ℂ) - θ * I := by
    apply Complex.ext
    · simp [hρdef]
    · rw [hΛdef, im_log_two_add_airyLogZeta]; simp [hθdef]
  have hW : exp (Λ + θ * I) = ((Real.exp ρ : ℝ) : ℂ) := by
    rw [hΛ, sub_add_cancel, ofReal_exp]
  rw [hW]
  set J : ℝ → ℂ := fun t => exp (-t : ℂ) * (t : ℂ) ^ (-1 / 6 : ℂ) *
        (2 + (t : ℂ) / airyZetaComplex z) ^ (-1 / 6 : ℂ) with hJ
  have hlap : airyRot_lap (5 / 6) (-1 / 6) θ (Real.exp ρ) =
      exp (Λ / 6 + log 2 / 6) * (((Real.exp ρ)⁻¹ : ℝ) : ℂ) * ∫ t : ℝ in Ioi 0, J t := by
    rw [airyRot_lap]
    have hc := Real.exp_pos ρ
    calc _ = ∫ r : ℝ in Ioi 0, exp (Λ / 6 + log 2 / 6) * J (Real.exp ρ * r) := by
          refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
          rw [airyInt_laplace_pointwise hz0 hθ hΛ hr]
      _ = _ := by
          rw [integral_const_mul, integral_comp_mul_left_Ioi J 0 hc, mul_zero, Complex.real_smul]
          ring
  rw [hlap]
  have hG : Gamma (((5 / 6 : ℝ)) : ℂ) = Gamma (5 / 6) := by push_cast; ring_nf
  rw [hG]
  have key : (3 : ℂ) ^ (-1 / 6 : ℂ) * exp (2 / 3 * airyLogZeta z - airyZetaComplex z) *
      exp (θ * I) * exp (Λ / 6 + log 2 / 6) * (((Real.exp ρ)⁻¹ : ℝ) : ℂ) =
      exp (-airyZetaComplex z) * exp (-airyLogZeta z / 6) / (48 : ℂ) ^ (1 / 6 : ℂ) := by
    have hρ : (ρ : ℂ) = Λ + θ * I := by linear_combination -hΛ
    have h48 : log (48 : ℂ) = 4 * log 2 + log 3 := by
      rw [show (48 : ℂ) = ((48 : ℝ) : ℂ) by norm_num, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
        show (3 : ℂ) = ((3 : ℝ) : ℂ) by norm_num, ← ofReal_log (by norm_num),
        ← ofReal_log (by norm_num), ← ofReal_log (by norm_num),
        show (48 : ℝ) = 2 ^ 4 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num),
        Real.log_pow]
      push_cast; ring
    rw [cpow_def_of_ne_zero (by norm_num), cpow_def_of_ne_zero (by norm_num), ofReal_inv,
      ofReal_exp, ← exp_neg, hρ, h48]
    simp only [← exp_add, ← exp_sub]
    congr 1
    rw [hΛdef]
    ring
  have hpi : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  linear_combination ((∫ t : ℝ in Ioi 0, J t) / ((Real.sqrt π : ℂ) * Gamma (5 / 6))) * key

end DLMF.Airy
