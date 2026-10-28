/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Struve.Asymptotics.AngerWeberExpansions

/-!
# Turning-point bounds for scaled Struve kernels

Phase geometry and local integral estimates control the scaled Struve kernels near turning
points.

Source references and common attribution are retained in
`DLMF.Struve.Asymptotics`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF

open scoped Real Topology Nat

namespace DLMF.Struve

open DLMF.Bessel DLMF.Airy

section StruveScaled

open scoped Interval

/-- `re z^{1/2} ≥ 0`. -/
theorem struveSc_re_cpow_half_nonneg (z : ℂ) : 0 ≤ (z ^ (1 / 2 : ℂ)).re := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  rw [cpow_def_of_ne_zero hz, exp_re]
  refine mul_nonneg (Real.exp_pos _).le (Real.cos_nonneg_of_mem_Icc ⟨?_, ?_⟩)
  · have : (log z * (1 / 2)).im = arg z / 2 := by simp [log_im, div_eq_mul_inv]
    rw [this]; linarith [neg_pi_lt_arg z]
  · have : (log z * (1 / 2)).im = arg z / 2 := by simp [log_im, div_eq_mul_inv]
    rw [this]; linarith [arg_le_pi z]

/-- `im z^{1/2} ≤ 0` when `im z ≤ 0`. -/
theorem struveSc_im_cpow_half_nonpos {z : ℂ} (hz' : z ∈ slitPlane) (h : z.im ≤ 0) :
    (z ^ (1 / 2 : ℂ)).im ≤ 0 := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  rw [cpow_def_of_ne_zero hz, exp_im]
  have him : (log z * (1 / 2)).im = arg z / 2 := by simp [log_im, div_eq_mul_inv]
  rw [him]
  refine mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le ?_
  rcases eq_or_lt_of_le h with h0 | hneg
  · -- real axis
    have hre : 0 ≤ z.re := by
      rcases mem_slitPlane_iff.1 hz' with h1 | h1
      · exact h1.le
      · exact absurd h0 h1
    rw [arg_eq_zero_iff.2 ⟨hre, h0⟩]; simp
  · have := arg_neg_iff.2 hneg
    exact Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith) (by linarith [neg_pi_lt_arg z])

/-- `im z^{1/2} ≥ 0` when `im z ≥ 0`. -/
theorem struveSc_im_cpow_half_nonneg {z : ℂ} (h : 0 ≤ z.im) : 0 ≤ (z ^ (1 / 2 : ℂ)).im := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  rw [cpow_def_of_ne_zero hz, exp_im]
  have him : (log z * (1 / 2)).im = arg z / 2 := by simp [log_im, div_eq_mul_inv]
  rw [him]
  refine mul_nonneg (Real.exp_pos _).le (Real.sin_nonneg_of_nonneg_of_le_pi ?_ ?_)
  · linarith [arg_nonneg_iff.2 h]
  · linarith [arg_le_pi z, Real.pi_pos]

/-- The square of the rotated point. -/
theorem struveSc_sq (r a : ℝ) : ((r : ℂ) * exp (((-a : ℝ) : ℂ) * I)) ^ 2 =
    ((r ^ 2 * Real.cos (2 * a) : ℝ) : ℂ) - ((r ^ 2 * Real.sin (2 * a) : ℝ) : ℂ) * I := by
  rw [mul_pow, ← exp_nat_mul, show ((2 : ℕ) : ℂ) * (((-a : ℝ) : ℂ) * I) =
    ((-(2 * a) : ℝ) : ℂ) * I by push_cast; ring, exp_mul_I, ← ofReal_cos, ← ofReal_sin,
    Real.cos_neg, Real.sin_neg]
  push_cast; ring

/-- `1 + w²` lies in the slit plane on the rotated ray. -/
theorem struveSc_mem_slitPlane {a : ℝ} (ha : |a| < π / 2) {r : ℝ} :
    1 + ((r : ℂ) * exp (((-a : ℝ) : ℂ) * I)) ^ 2 ∈ slitPlane := by
  rw [struveSc_sq, mem_slitPlane_iff]
  simp only [add_re, one_re, sub_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero,
    sub_zero, mul_one, add_im, one_im, sub_im, zero_add, zero_sub]
  by_cases hs : Real.sin (2 * a) = 0
  · left
    have h2 : |2 * a| < π := by rw [abs_mul]; norm_num; linarith
    have ha0 : 2 * a = 0 := by
      rcases Real.sin_eq_zero_iff_of_lt_of_lt (by linarith [neg_abs_le (2 * a)])
        (by linarith [le_abs_self (2 * a)]) |>.1 hs with h; exact h
    rw [ha0, Real.cos_zero]
    nlinarith [sq_nonneg r]
  · rcases eq_or_ne r 0 with hr | hr
    · left; simp [hr]
    · right
      intro h
      have : r ^ 2 * Real.sin (2 * a) = 0 := by
        rw [mul_I_im, ofReal_re, neg_eq_zero] at h; exact h
      rcases mul_eq_zero.1 this with h1 | h1
      · exact hr (pow_eq_zero_iff two_ne_zero |>.1 h1)
      · exact hs h1

/-- Estimate under the stated parameter and domain assumptions: `0 < Real.cos a`. -/
theorem struveSc_cos_pos {a : ℝ} (ha : |a| < π / 2) : 0 < Real.cos a :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [neg_abs_le a], by linarith [le_abs_self a]⟩

/-- `re (e^{ia} (1+w²)^{1/2}) ≥ 0` on the ray `w = r e^{-ia}`. -/
theorem struveSc_re_rot_P {a : ℝ} (ha : |a| < π / 2) (r : ℝ) :
    0 ≤ (exp ((a : ℂ) * I) *
      (1 + ((r : ℂ) * exp (((-a : ℝ) : ℂ) * I)) ^ 2) ^ (1 / 2 : ℂ)).re := by
  set u := 1 + ((r : ℂ) * exp (((-a : ℝ) : ℂ) * I)) ^ 2 with hu
  have hmem : u ∈ slitPlane := struveSc_mem_slitPlane ha
  have hum : u.im = -(r ^ 2 * Real.sin (2 * a)) := by
    rw [hu, struveSc_sq, add_im, sub_im, one_im, ofReal_im, mul_I_im, ofReal_re]; ring
  have hc := struveSc_cos_pos ha
  rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  simp only [mul_re, add_re, ofReal_re, mul_im, ofReal_im, I_re, I_im, add_im, mul_zero,
    sub_zero, mul_one, zero_add]
  have hre := struveSc_re_cpow_half_nonneg u
  rcases le_or_gt 0 a with h0 | h0
  · have hs : 0 ≤ Real.sin a := Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [le_abs_self a])
    have hs2 : 0 ≤ Real.sin (2 * a) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [le_abs_self a])
    have him := struveSc_im_cpow_half_nonpos hmem (by rw [hum]; nlinarith [sq_nonneg r])
    nlinarith [mul_nonneg hc.le hre]
  · have hs : Real.sin a < 0 := Real.sin_neg_of_neg_of_neg_pi_lt h0 (by linarith [neg_abs_le a])
    have hs2 : Real.sin (2 * a) ≤ 0 :=
      Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith) (by linarith [neg_abs_le a])
    have him := struveSc_im_cpow_half_nonneg (z := u) (by rw [hum]; nlinarith [sq_nonneg r])
    nlinarith [mul_nonneg hc.le hre]

/-- `re (e^{ia} (1 - (1+w²)^{-1/2})) ≥ 0` on the ray `w = r e^{-ia}`. -/
theorem struveSc_re_one_sub_q {a : ℝ} (ha : |a| < π / 2) (r : ℝ) :
    0 ≤ (exp ((a : ℂ) * I) *
      (1 - (1 + ((r : ℂ) * exp (((-a : ℝ) : ℂ) * I)) ^ 2) ^ (-(1 / 2 : ℂ)))).re := by
  set w := (r : ℂ) * exp (((-a : ℝ) : ℂ) * I) with hw
  set u := 1 + w ^ 2 with hu
  set P := u ^ (1 / 2 : ℂ) with hP
  have hmem : u ∈ slitPlane := struveSc_mem_slitPlane ha
  have hu0 : u ≠ 0 := slitPlane_ne_zero hmem
  have hP0 : P ≠ 0 := by rw [hP]; exact (cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num)).2 hu0
  have hP2 : P ^ 2 = u := by
    rw [hP, ← cpow_nat_mul]; norm_num
  have hq : u ^ (-(1 / 2 : ℂ)) = P⁻¹ := by rw [cpow_neg]
  set ea := exp ((a : ℂ) * I) with hea
  have hc := struveSc_cos_pos ha
  set Z := ea * u + ea * P with hZ
  have hZre : (1 + r ^ 2) * Real.cos a ≤ Z.re := by
    have h1 : (ea * u).re = (1 + r ^ 2) * Real.cos a := by
      rw [hea, hu, struveSc_sq, exp_mul_I, ← ofReal_cos, ← ofReal_sin]
      simp only [mul_re, add_re, ofReal_re, mul_im, ofReal_im, I_re, I_im, add_im, mul_zero,
        sub_zero, mul_one, zero_add, one_re, one_im, sub_re, sub_im]
      rw [Real.cos_two_mul, Real.sin_two_mul]
      linear_combination (2 * r ^ 2 * Real.cos a) * Real.sin_sq_add_cos_sq a
    have h2 := struveSc_re_rot_P ha r
    simp only [hZ, add_re]
    rw [h1]; linarith
  have hZ0 : Z ≠ 0 := by
    intro h; rw [h, zero_re] at hZre; nlinarith [sq_nonneg r]
  have hkey : ea * (1 - u ^ (-(1 / 2 : ℂ))) * Z = (r : ℂ) ^ 2 := by
    have hee : ea * ea * w ^ 2 = (r : ℂ) ^ 2 := by
      rw [hw, hea, mul_pow, ← exp_nat_mul]
      have h1 : cexp (↑a * I) * cexp (↑a * I) * cexp (((2 : ℕ) : ℂ) * (((-a : ℝ) : ℂ) * I)) = 1 := by
        rw [← exp_add, ← exp_add]; push_cast; ring_nf; exact exp_zero
      linear_combination (r : ℂ) ^ 2 * h1
    rw [hq, hZ, ← hee, show w ^ 2 = P ^ 2 - 1 by rw [hP2, hu]; ring]
    field_simp
    linear_combination ea ^ 2 * (1 - P) * hP2
  have hX : ea * (1 - u ^ (-(1 / 2 : ℂ))) = ((r ^ 2 : ℝ) : ℂ) / Z := by
    rw [eq_div_iff hZ0, hkey]; push_cast; ring
  rw [hX, div_re, ofReal_re, ofReal_im, zero_mul, zero_div, add_zero]
  exact div_nonneg (mul_nonneg (sq_nonneg r) (by nlinarith [sq_nonneg r])) (normSq_nonneg _)

/-- The phase `Ψ(w) = λ w - log (w + (1+w²)^{1/2})` of the scaled `𝐀_{-ν}(λν)` integrand. -/
noncomputable def struveSc_phase (lam : ℝ) (w : ℂ) : ℂ :=
  (lam : ℂ) * w - log (w + (1 + w ^ 2) ^ (1 / 2 : ℂ))

/-- `Ψ'(w) = λ - (1+w²)^{-1/2}`. -/
theorem struveSc_hasDerivAt_phase (lam : ℝ) {w : ℂ} (hu : 1 + w ^ 2 ∈ slitPlane)
    (hx : w + (1 + w ^ 2) ^ (1 / 2 : ℂ) ∈ slitPlane) :
    HasDerivAt (struveSc_phase lam) ((lam : ℂ) - (1 + w ^ 2) ^ (-(1 / 2 : ℂ))) w := by
  have hu0 : 1 + w ^ 2 ≠ 0 := slitPlane_ne_zero hu
  have hP0 : (1 + w ^ 2) ^ (1 / 2 : ℂ) ≠ 0 :=
    (cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num)).2 hu0
  have hx0 : w + (1 + w ^ 2) ^ (1 / 2 : ℂ) ≠ 0 := slitPlane_ne_zero hx
  have hP2 : ((1 + w ^ 2) ^ (1 / 2 : ℂ)) ^ 2 = 1 + w ^ 2 := by
    rw [← cpow_nat_mul]; norm_num
  have h1 : HasDerivAt (fun w : ℂ => 1 + w ^ 2) (2 * w) w := by
    simpa using ((hasDerivAt_pow 2 w).const_add 1)
  have h2 := (h1.cpow_const (c := (1 / 2 : ℂ)) hu)
  have h3 := ((hasDerivAt_id' w).fun_add h2).clog hx
  have h4 := ((hasDerivAt_id' w).const_mul (lam : ℂ)).fun_sub h3
  convert h4 using 1
  · rfl
  rw [show (1 / 2 : ℂ) - 1 = -(1 / 2) by norm_num, cpow_neg]
  field_simp
  ring

/-- Estimate under the stated parameter and domain assumptions: `0 < ((r : ℂ) * exp (((-a : ℝ) :
ℂ) * I) + (1 + ((r : ℂ) * exp (((-a : ℝ) : ℂ) * I)) ^ 2) ^ (1 / 2 : ℂ)).re`. -/
theorem struveSc_re_x_pos {a : ℝ} (ha : |a| < π / 2) {r : ℝ} (hr : 0 ≤ r) :
    0 < ((r : ℂ) * exp (((-a : ℝ) : ℂ) * I) +
      (1 + ((r : ℂ) * exp (((-a : ℝ) : ℂ) * I)) ^ 2) ^ (1 / 2 : ℂ)).re := by
  have h1 := struveAs_re_cpow_half_pos (struveSc_mem_slitPlane (r := r) ha)
  rw [add_re, re_ofReal_mul, exp_ofReal_mul_I_re, Real.cos_neg]
  have := struveSc_cos_pos ha
  nlinarith

/-- The phase along the rotated ray. -/
theorem struveSc_hasDerivAt_phase_ray (lam : ℝ) {a : ℝ} (ha : |a| < π / 2) {r : ℝ} (hr : 0 ≤ r) :
    HasDerivAt (fun r : ℝ => struveSc_phase lam ((r : ℂ) * exp (((-a : ℝ) : ℂ) * I)))
      (exp (((-a : ℝ) : ℂ) * I) * ((lam : ℂ) -
        (1 + ((r : ℂ) * exp (((-a : ℝ) : ℂ) * I)) ^ 2) ^ (-(1 / 2 : ℂ)))) r := by
  have hd := struveSc_hasDerivAt_phase lam (struveSc_mem_slitPlane (r := r) ha)
    (mem_slitPlane_iff.2 (Or.inl (struveSc_re_x_pos ha hr)))
  have hl : HasDerivAt (fun r : ℝ => (r : ℂ) * exp (((-a : ℝ) : ℂ) * I))
      (exp (((-a : ℝ) : ℂ) * I)) r := by
    simpa using (hasDerivAt_id r).ofReal_comp.mul_const (exp (((-a : ℝ) : ℂ) * I))
  exact (hd.comp r hl).congr_deriv (mul_comm _ _)

/-- Identity under the stated parameter and domain assumptions: `struveSc_phase lam 0 = 0`. -/
theorem struveSc_phase_zero (lam : ℝ) : struveSc_phase lam 0 = 0 := by
  simp [struveSc_phase]

/-- At `s`, the function `(fun s => (f s).re)` has derivative `f'.re`. -/
theorem struveSc_hasDerivAt_re {f : ℝ → ℂ} {f' : ℂ} {s : ℝ} (h : HasDerivAt f f' s) :
    HasDerivAt (fun s => (f s).re) f'.re s := by
  have := reCLM.hasFDerivAt.comp_hasDerivAt s h
  convert this using 1
  · funext y; simp
  · simp

/-- **Growth of the phase.** With `ν = ρ e^{2ia}`, `re (ν Ψ(r e^{-ia})) ≥ (λ-1) cos a · ρ r`. -/
theorem struveSc_re_phase_ge {lam : ℝ} {a : ℝ} (ha : |a| < π / 2) {ρ : ℝ}
    (hρ : 0 ≤ ρ) {r : ℝ} (hr : 0 ≤ r) :
    (lam - 1) * Real.cos a * ρ * r ≤
      ((ρ : ℂ) * exp ((2 * a : ℝ) * I) *
        struveSc_phase lam ((r : ℂ) * exp (((-a : ℝ) : ℂ) * I))).re := by
  set ν : ℂ := (ρ : ℂ) * exp ((2 * a : ℝ) * I) with hν
  set g : ℝ → ℝ := fun s => (ν * struveSc_phase lam ((s : ℂ) * exp (((-a : ℝ) : ℂ) * I))).re -
    (lam - 1) * Real.cos a * ρ * s with hg
  have hνE : ν * exp (((-a : ℝ) : ℂ) * I) = (ρ : ℂ) * exp ((a : ℂ) * I) := by
    rw [hν, mul_assoc, ← exp_add]; congr 2; push_cast; ring
  have hderiv : ∀ s : ℝ, 0 ≤ s → HasDerivAt g
      ((ν * (exp (((-a : ℝ) : ℂ) * I) * ((lam : ℂ) -
        (1 + ((s : ℂ) * exp (((-a : ℝ) : ℂ) * I)) ^ 2) ^ (-(1 / 2 : ℂ))))).re -
        (lam - 1) * Real.cos a * ρ) s := by
    intro s hs
    have h1 := struveSc_hasDerivAt_re ((struveSc_hasDerivAt_phase_ray lam ha hs).const_mul ν)
    have h2 := h1.sub ((hasDerivAt_id' s).const_mul ((lam - 1) * Real.cos a * ρ))
    rw [mul_one] at h2
    exact h2
  have hmono : MonotoneOn g (Ici 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0) (f' := fun s =>
      (ν * (exp (((-a : ℝ) : ℂ) * I) * ((lam : ℂ) -
        (1 + ((s : ℂ) * exp (((-a : ℝ) : ℂ) * I)) ^ 2) ^ (-(1 / 2 : ℂ))))).re -
        (lam - 1) * Real.cos a * ρ) ?_ ?_ ?_
    · exact fun s hs => (hderiv s hs).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Ici] at hs ⊢
      exact (hderiv s (le_of_lt hs)).hasDerivWithinAt
    · intro s hs
      rw [interior_Ici] at hs
      have hpos := struveSc_re_one_sub_q ha s
      rw [← mul_assoc, hνE, sub_nonneg]
      set q := (1 + ((s : ℂ) * exp (((-a : ℝ) : ℂ) * I)) ^ 2) ^ (-(1 / 2 : ℂ))
      have e1 : ((ρ : ℂ) * exp ((a : ℂ) * I) * ((lam : ℂ) - q)).re =
          ρ * ((lam - 1) * Real.cos a + (exp ((a : ℂ) * I) * (1 - q)).re) := by
        have : (ρ : ℂ) * exp ((a : ℂ) * I) * ((lam : ℂ) - q) =
            (ρ : ℂ) * (((lam - 1 : ℝ) : ℂ) * exp ((a : ℂ) * I) + exp ((a : ℂ) * I) * (1 - q)) := by
          push_cast; ring
        rw [this, re_ofReal_mul, add_re, re_ofReal_mul, exp_ofReal_mul_I_re]
      rw [e1]
      nlinarith [mul_nonneg hρ hpos]
  have h0 : g 0 = 0 := by simp [hg, struveSc_phase_zero]
  have := hmono (mem_Ici.2 le_rfl) (show r ∈ Ici (0 : ℝ) from hr) hr
  rw [h0] at this
  simp only [hg] at this
  linarith

/-- Uniform bounds for `q = (1+w²)^{-1/2}` on the rotated rays: `|q| ≤ K`, `|1 - q| ≤ K r`. -/
theorem struveSc_q_bounds {δ : ℝ} (hδ : 0 < δ) : ∃ K > 0, ∀ a : ℝ, |a| ≤ (π - δ) / 2 →
    ∀ r : ℝ, 0 ≤ r →
      ‖(1 + ((r : ℂ) * exp (((-a : ℝ) : ℂ) * I)) ^ 2) ^ (-(1 / 2 : ℂ))‖ ≤ K ∧
      ‖1 - (1 + ((r : ℂ) * exp (((-a : ℝ) : ℂ) * I)) ^ 2) ^ (-(1 / 2 : ℂ))‖ ≤ K * r := by
  obtain ⟨c0, hc0, hc⟩ := Complex.exists_pos_le_norm_one_add_ofReal_mul_exp
    (Φ := π - δ) (by linarith)
  set K : ℝ := 1 + 1 / Real.sqrt c0 with hK
  have hs0 : 0 < Real.sqrt c0 := Real.sqrt_pos.2 hc0
  refine ⟨K, by positivity, fun a ha r hr => ?_⟩
  have ha' : |a| < π / 2 := by linarith
  set w := (r : ℂ) * exp (((-a : ℝ) : ℂ) * I) with hw
  set u := 1 + w ^ 2 with hu
  set P := u ^ (1 / 2 : ℂ) with hP
  have hmem : u ∈ slitPlane := struveSc_mem_slitPlane ha'
  have hu0 : u ≠ 0 := slitPlane_ne_zero hmem
  have hP0 : P ≠ 0 := by rw [hP]; exact (cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num)).2 hu0
  have hP2 : P ^ 2 = u := by rw [hP, ← cpow_nat_mul]; norm_num
  have hq : u ^ (-(1 / 2 : ℂ)) = P⁻¹ := by rw [cpow_neg]
  have hw2 : w ^ 2 = ((r ^ 2 : ℝ) : ℂ) * exp (((-(2 * a) : ℝ) : ℂ) * I) := by
    rw [hw, mul_pow, ← exp_nat_mul]; push_cast; ring_nf
  have hu_ge : c0 ≤ ‖u‖ := by
    rw [hu, hw2]; exact hc _ (sq_nonneg r) _ (by rw [abs_neg, abs_mul]; norm_num; linarith)
  have hPn : Real.sqrt c0 ≤ ‖P‖ := by
    have : ‖P‖ ^ 2 = ‖u‖ := by rw [← norm_pow, hP2]
    rw [show ‖P‖ = Real.sqrt (‖P‖ ^ 2) from (Real.sqrt_sq (norm_nonneg _)).symm, this]
    exact Real.sqrt_le_sqrt hu_ge
  have hPpos : 0 < ‖P‖ := hs0.trans_le hPn
  have hqn : ‖u ^ (-(1 / 2 : ℂ))‖ ≤ 1 / Real.sqrt c0 := by
    rw [hq, norm_inv, inv_eq_one_div]
    exact one_div_le_one_div_of_le hs0 hPn
  have hP1 : 1 ≤ ‖P + 1‖ := by
    have := struveSc_re_cpow_half_nonneg u
    have h := Complex.re_le_norm (P + 1)
    rw [add_re, one_re] at h
    linarith
  have hiden : (1 - u ^ (-(1 / 2 : ℂ))) * (P * (P + 1)) = w ^ 2 := by
    rw [hq, show w ^ 2 = P ^ 2 - 1 by rw [hP2, hu]; ring]
    field_simp
    ring
  have h1q : ‖1 - u ^ (-(1 / 2 : ℂ))‖ ≤ r ^ 2 / Real.sqrt c0 := by
    have hn : ‖1 - u ^ (-(1 / 2 : ℂ))‖ * (‖P‖ * ‖P + 1‖) = r ^ 2 := by
      rw [← norm_mul, ← norm_mul, hiden, hw2, norm_mul, norm_exp_ofReal_mul_I, mul_one,
        norm_real, Real.norm_of_nonneg (sq_nonneg r)]
    rw [le_div_iff₀ hs0, ← hn]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    nlinarith
  refine ⟨hqn.trans (by rw [hK]; linarith), ?_⟩
  rcases le_or_gt r 1 with h | h
  · calc ‖1 - u ^ (-(1 / 2 : ℂ))‖ ≤ r ^ 2 / Real.sqrt c0 := h1q
      _ ≤ r / Real.sqrt c0 := by gcongr; nlinarith
      _ ≤ K * r := by
        rw [hK, div_eq_mul_one_div r, mul_comm r]; gcongr; linarith
  · calc ‖1 - u ^ (-(1 / 2 : ℂ))‖ ≤ ‖(1 : ℂ)‖ + ‖u ^ (-(1 / 2 : ℂ))‖ := norm_sub_le _ _
      _ ≤ K := by rw [norm_one, hK]; linarith
      _ ≤ K * r := le_mul_of_one_le_right (by positivity) h.le

/-- `‖e^A - e^B‖ ≤ ‖A - B‖ e^M` when `re A, re B ≤ M`. -/
theorem struveSc_norm_exp_sub_exp_le {A B : ℂ} {M : ℝ} (hA : A.re ≤ M) (hB : B.re ≤ M) :
    ‖exp A - exp B‖ ≤ ‖A - B‖ * Real.exp M := by
  set g : ℝ → ℂ := fun t => exp (B + t * (A - B)) with hg
  have hd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt g ((A - B) * g t) (Icc 0 1) t := by
    intro t _
    have h1 : HasDerivAt (fun t : ℝ => B + (t : ℂ) * (A - B)) (A - B) t := by
      simpa using ((hasDerivAt_id t).ofReal_comp.mul_const (A - B)).const_add B
    have := h1.cexp
    rw [mul_comm] at this
    exact this.hasDerivWithinAt
  have hb : ∀ t ∈ Icc (0 : ℝ) 1, ‖(A - B) * g t‖ ≤ ‖A - B‖ * Real.exp M := by
    intro t ht
    rw [norm_mul, hg, norm_exp]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (norm_nonneg _)
    simp only [add_re, re_ofReal_mul, sub_re]
    nlinarith [ht.1, ht.2]
  have := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le hd hb
    (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one)
  simpa [hg] using this

/-- `‖Ψ(r e^{-ia}) - e^{-ia}(λ-1) r‖ ≤ K r²/2` from `|1 - q| ≤ K r`. -/
theorem struveSc_phase_sub_lin (lam : ℝ) {a : ℝ} (ha : |a| < π / 2) {K : ℝ}
    (hK : ∀ s : ℝ, 0 ≤ s →
      ‖1 - (1 + ((s : ℂ) * exp (((-a : ℝ) : ℂ) * I)) ^ 2) ^ (-(1 / 2 : ℂ))‖ ≤ K * s)
    {r : ℝ} (hr : 0 ≤ r) :
    ‖struveSc_phase lam ((r : ℂ) * exp (((-a : ℝ) : ℂ) * I)) -
      exp (((-a : ℝ) : ℂ) * I) * ((lam : ℂ) - 1) * r‖ ≤ K / 2 * r ^ 2 := by
  set E := exp (((-a : ℝ) : ℂ) * I) with hE
  set f : ℝ → ℂ := fun s => struveSc_phase lam ((s : ℂ) * E) - E * ((lam : ℂ) - 1) * s with hf
  have hfd : ∀ s : ℝ, 0 ≤ s → HasDerivAt f
      (E * (1 - (1 + ((s : ℂ) * E) ^ 2) ^ (-(1 / 2 : ℂ)))) s := by
    intro s hs
    have h1 := struveSc_hasDerivAt_phase_ray lam ha hs
    have h2 := (hasDerivAt_id s).ofReal_comp.const_mul (E * ((lam : ℂ) - 1))
    refine (h1.fun_sub h2).congr_deriv ?_
    rw [← hE, ofReal_one, mul_one]; ring
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := f) (a := 0) (b := r)
    (f' := fun s => E * (1 - (1 + ((s : ℂ) * E) ^ 2) ^ (-(1 / 2 : ℂ))))
    (B := fun s => K / 2 * s ^ 2) (B' := fun s => K * s)
    (fun s hs => (hfd s hs.1).continuousAt.continuousWithinAt)
    (fun s hs => (hfd s hs.1).hasDerivWithinAt)
    (by simp [hf, struveSc_phase_zero])
    (fun s => by
      have := (hasDerivAt_pow 2 s).const_mul (K / 2)
      convert this using 1; push_cast; ring)
    (fun s hs => by
      rw [norm_mul, hE, norm_exp_ofReal_mul_I, one_mul]; exact hK s hs.1)
    (right_mem_Icc.2 hr)
  simpa [hf] using key

/-- The integrand of the rotated representation of `𝐀_{-ν}(λν)` in terms of the phase. -/
theorem struveSc_integrand_eq (lam : ℝ) {a : ℝ} (ha : |a| < π / 2) (ν : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    exp (-((lam : ℂ) * ν * exp (((-a : ℝ) : ℂ) * I) * r)) *
      struveAs_kernel (-ν) ((r : ℂ) * exp (((-a : ℝ) : ℂ) * I)) =
    exp (-(ν * struveSc_phase lam ((r : ℂ) * exp (((-a : ℝ) : ℂ) * I)))) *
      (1 + ((r : ℂ) * exp (((-a : ℝ) : ℂ) * I)) ^ 2) ^ (-(1 / 2 : ℂ)) := by
  set w := (r : ℂ) * exp (((-a : ℝ) : ℂ) * I) with hw
  have hx : w + (1 + w ^ 2) ^ (1 / 2 : ℂ) ≠ 0 := by
    intro h; have := struveSc_re_x_pos ha hr; rw [← hw, h, zero_re] at this; exact lt_irrefl _ this
  rw [struveAs_kernel, neg_neg, cpow_def_of_ne_zero hx, struveSc_phase, ← mul_assoc, ← exp_add]
  congr 2
  rw [hw]; ring

/-- `∫₀^∞ e^{-br} rⁿ dr = n!/b^{n+1}`, with integrability. -/
theorem struveSc_integral_pow_exp (n : ℕ) {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun r : ℝ => Real.exp (-(b * r)) * r ^ n) (Ioi 0) ∧
    ∫ r in Ioi (0 : ℝ), Real.exp (-(b * r)) * r ^ n = n ! / b ^ (n + 1) := by
  have hcongr : EqOn (fun r : ℝ => r ^ ((n + 1 : ℝ) - 1) * Real.exp (-(b * r)))
      (fun r : ℝ => Real.exp (-(b * r)) * r ^ n) (Ioi 0) := by
    intro r hr
    simp only
    rw [show (n + 1 : ℝ) - 1 = (n : ℝ) by ring, Real.rpow_natCast, mul_comm]
  refine ⟨?_, ?_⟩
  · have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n : ℝ)) (p := 1) (b := b)
      (by have := Nat.cast_nonneg (α := ℝ) n; linarith) one_pos hb
    refine h.congr_fun (fun r hr => ?_) measurableSet_Ioi
    simp only [Real.rpow_one, Real.rpow_natCast, neg_mul]
    ring
  · rw [← setIntegral_congr_fun measurableSet_Ioi hcongr,
      Real.integral_rpow_mul_exp_neg_mul_Ioi (by positivity) hb, Real.Gamma_nat_eq_factorial,
      show (n + 1 : ℝ) = ((n + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast, div_pow, one_pow]
    field_simp

/-- **The main estimate** behind DLMF 11.11.14. -/
theorem struveSc_integral_est {lam : ℝ} (hlam : 1 < lam) {a : ℝ} (ha : |a| < π / 2) {K : ℝ}
    (hK : ∀ s : ℝ, 0 ≤ s →
      ‖(1 + ((s : ℂ) * exp (((-a : ℝ) : ℂ) * I)) ^ 2) ^ (-(1 / 2 : ℂ))‖ ≤ K ∧
      ‖1 - (1 + ((s : ℂ) * exp (((-a : ℝ) : ℂ) * I)) ^ 2) ^ (-(1 / 2 : ℂ))‖ ≤ K * s)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ‖exp (((-a : ℝ) : ℂ) * I) * (∫ r in Ioi (0 : ℝ),
        exp (-((lam : ℂ) * ((ρ : ℂ) * exp ((2 * a : ℝ) * I)) * exp (((-a : ℝ) : ℂ) * I) * r)) *
        struveAs_kernel (-((ρ : ℂ) * exp ((2 * a : ℝ) * I))) ((r : ℂ) * exp (((-a : ℝ) : ℂ) * I))) -
      1 / (((ρ : ℂ) * exp ((2 * a : ℝ) * I)) * ((lam : ℂ) - 1))‖ ≤
      (K / ((lam - 1) * Real.cos a) ^ 2 + K / ((lam - 1) * Real.cos a) ^ 3) / ρ ^ 2 := by
  set ν : ℂ := (ρ : ℂ) * exp ((2 * a : ℝ) * I) with hν
  set E : ℂ := exp (((-a : ℝ) : ℂ) * I) with hE
  set κ : ℝ := (lam - 1) * Real.cos a with hκ
  have hc := struveSc_cos_pos ha
  have hκ0 : 0 < κ := mul_pos (by linarith) hc
  set b : ℝ := κ * ρ with hb
  have hb0 : 0 < b := mul_pos hκ0 hρ
  set q : ℝ → ℂ := fun s => (1 + ((s : ℂ) * E) ^ 2) ^ (-(1 / 2 : ℂ)) with hq
  set Ψ : ℝ → ℂ := fun s => struveSc_phase lam ((s : ℂ) * E) with hΨ
  set F : ℝ → ℂ := fun r => exp (-(ν * Ψ r)) * q r with hF
  have hνE : ν * E = (ρ : ℂ) * exp ((a : ℂ) * I) := by
    rw [hν, hE, mul_assoc, ← exp_add]; congr 2; push_cast; ring
  set c : ℂ := -(ν * E * ((lam : ℂ) - 1)) with hcdef
  have hcre : c.re = -b := by
    rw [hcdef, hνE, hb, hκ, show (ρ : ℂ) * exp ((a : ℂ) * I) * ((lam : ℂ) - 1) =
      ((ρ * (lam - 1) : ℝ) : ℂ) * exp ((a : ℂ) * I) by push_cast; ring, neg_re, re_ofReal_mul,
      exp_ofReal_mul_I_re]
    ring
  set G : ℝ → ℂ := fun r => exp (c * r) with hG
  have hGi : IntegrableOn G (Ioi 0) := integrableOn_exp_mul_complex_Ioi (by rw [hcre]; linarith) 0
  have hc0 : c ≠ 0 := by intro h; rw [h, zero_re] at hcre; linarith
  have hGint : ∫ r in Ioi (0 : ℝ), G r = -1 / c := by
    rw [integral_exp_mul_complex_Ioi (by rw [hcre]; linarith) 0]; simp
  -- pointwise bound
  have hbound : ∀ r : ℝ, 0 < r → ‖F r - G r‖ ≤
      Real.exp (-(b * r)) * (K * r + ρ * (K / 2) * r ^ 2) := by
    intro r hr
    have hre := struveSc_re_phase_ge (lam := lam) ha hρ.le hr.le
    rw [← hν] at hre
    have hA : (-(ν * Ψ r)).re ≤ -(b * r) := by
      rw [neg_re, hb]; simp only [hΨ, hE]; nlinarith
    have hB : (c * r).re ≤ -(b * r) := by rw [re_mul_ofReal, hcre]; linarith
    have hsplit : F r - G r = exp (-(ν * Ψ r)) * (q r - 1) + (exp (-(ν * Ψ r)) - exp (c * r)) := by
      simp only [hF, hG]; ring
    have h1 : ‖exp (-(ν * Ψ r))‖ ≤ Real.exp (-(b * r)) := by
      rw [norm_exp]; exact Real.exp_le_exp.2 hA
    have h2 : ‖q r - 1‖ ≤ K * r := by rw [norm_sub_rev]; exact (hK r hr.le).2
    have hlin := struveSc_phase_sub_lin lam ha (fun s hs => (hK s hs).2) hr.le
    have h3 : ‖-(ν * Ψ r) - c * r‖ ≤ ρ * (K / 2 * r ^ 2) := by
      have : -(ν * Ψ r) - c * r = -(ν * (struveSc_phase lam ((r : ℂ) * E) -
          E * ((lam : ℂ) - 1) * r)) := by
        simp only [hΨ, hcdef]; ring
      rw [this, norm_neg, norm_mul, hν, norm_mul, norm_exp_ofReal_mul_I, mul_one, norm_real,
        Real.norm_of_nonneg hρ.le]
      exact mul_le_mul_of_nonneg_left hlin hρ.le
    have h4 := struveSc_norm_exp_sub_exp_le hA hB
    rw [hsplit]
    calc ‖exp (-(ν * Ψ r)) * (q r - 1) + (exp (-(ν * Ψ r)) - exp (c * r))‖
        ≤ ‖exp (-(ν * Ψ r))‖ * ‖q r - 1‖ + ‖-(ν * Ψ r) - c * r‖ * Real.exp (-(b * r)) := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul]; gcongr
      _ ≤ Real.exp (-(b * r)) * (K * r) + ρ * (K / 2 * r ^ 2) * Real.exp (-(b * r)) := by
          gcongr
      _ = _ := by ring
  -- integrability
  obtain ⟨i1, e1⟩ := struveSc_integral_pow_exp 1 hb0
  obtain ⟨i2, e2⟩ := struveSc_integral_pow_exp 2 hb0
  have hbi : IntegrableOn (fun r : ℝ => Real.exp (-(b * r)) * (K * r + ρ * (K / 2) * r ^ 2))
      (Ioi 0) := by
    have : IntegrableOn (fun r : ℝ => K * (Real.exp (-(b * r)) * r ^ 1) +
        ρ * (K / 2) * (Real.exp (-(b * r)) * r ^ 2)) (Ioi 0) :=
      (i1.const_mul K).add (i2.const_mul (ρ * (K / 2)))
    refine this.congr_fun (fun r _ => ?_) measurableSet_Ioi
    simp only [pow_one]; ring
  have hFc : ContinuousOn F (Ioi 0) := by
    intro r hr
    have hr0 : (0 : ℝ) ≤ r := le_of_lt hr
    have hΨc : ContinuousAt Ψ r := (struveSc_hasDerivAt_phase_ray lam ha hr0).continuousAt
    have hqc : ContinuousAt q r :=
      ((by fun_prop : Continuous fun s : ℝ => 1 + ((s : ℂ) * E) ^ 2).continuousAt).cpow
        continuousAt_const (struveSc_mem_slitPlane ha)
    exact ((continuous_exp.continuousAt.comp (hΨc.const_mul ν).neg).mul hqc).continuousWithinAt
  have hdm : AEStronglyMeasurable (fun r => F r - G r) (volume.restrict (Ioi 0)) :=
    (hFc.sub (by fun_prop : Continuous G).continuousOn).aestronglyMeasurable measurableSet_Ioi
  have hdi : IntegrableOn (fun r => F r - G r) (Ioi 0) := by
    refine Integrable.mono' hbi hdm ((ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun r hr => hbound r hr))
  have hFi : IntegrableOn F (Ioi 0) := by
    have : IntegrableOn (fun r => (F r - G r) + G r) (Ioi 0) := hdi.add hGi
    refine this.congr_fun (fun r _ => ?_) measurableSet_Ioi
    simp
  -- assemble
  have hint_eq : (∫ r in Ioi (0 : ℝ),
      exp (-((lam : ℂ) * ν * E * r)) * struveAs_kernel (-ν) ((r : ℂ) * E)) =
      ∫ r in Ioi (0 : ℝ), F r := by
    refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
    simp only [hF, hΨ, hq]
    exact struveSc_integrand_eq lam ha ν (le_of_lt hr)
  have hE1 : ‖E‖ = 1 := by rw [hE, norm_exp_ofReal_mul_I]
  have hE0 : E ≠ 0 := by rw [hE]; exact exp_ne_zero _
  have hν0 : ν ≠ 0 := by
    rw [hν]; exact mul_ne_zero (ofReal_ne_zero.2 hρ.ne') (exp_ne_zero _)
  have hl0 : (lam : ℂ) - 1 ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast hlam.ne'
  have hlead : 1 / (ν * ((lam : ℂ) - 1)) = E * ∫ r in Ioi (0 : ℝ), G r := by
    rw [hGint, hcdef]; field_simp
  rw [hint_eq, hlead, ← mul_sub, norm_mul, hE1, one_mul, ← integral_sub hFi hGi]
  refine (norm_integral_le_of_norm_le hbi ((ae_restrict_iff' measurableSet_Ioi).mpr
    (Eventually.of_forall fun r hr => hbound r hr))).trans (le_of_eq ?_)
  have hsum : ∫ r in Ioi (0 : ℝ), Real.exp (-(b * r)) * (K * r + ρ * (K / 2) * r ^ 2) =
      K * (1 / b ^ 2) + ρ * (K / 2) * (2 / b ^ 3) := by
    have h := integral_add (i1.const_mul K) (i2.const_mul (ρ * (K / 2)))
    rw [integral_const_mul, integral_const_mul, e1, e2] at h
    rw [← show (1 ! : ℝ) / b ^ (1 + 1) = 1 / b ^ 2 by norm_num,
      ← show (2 ! : ℝ) / b ^ (2 + 1) = 2 / b ^ 3 by norm_num, ← h]
    refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
    simp only [pow_one]; ring
  rw [hsum, hb]
  field_simp

/-- Quantitative form of `struveSc_re_one_sub_q`:
`re (e^{ia}(1 - q)) ≥ cos a · r²/(4(1+r²))`. -/
theorem struveSc_re_one_sub_q_ge {a : ℝ} (ha : |a| < π / 2) (r : ℝ) :
    Real.cos a * r ^ 2 / (4 * (1 + r ^ 2)) ≤ (exp ((a : ℂ) * I) *
      (1 - (1 + ((r : ℂ) * exp (((-a : ℝ) : ℂ) * I)) ^ 2) ^ (-(1 / 2 : ℂ)))).re := by
  set w := (r : ℂ) * exp (((-a : ℝ) : ℂ) * I) with hw
  set u := 1 + w ^ 2 with hu
  set P := u ^ (1 / 2 : ℂ) with hP
  have hmem : u ∈ slitPlane := struveSc_mem_slitPlane ha
  have hu0 : u ≠ 0 := slitPlane_ne_zero hmem
  have hP0 : P ≠ 0 := by rw [hP]; exact (cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num)).2 hu0
  have hP2 : P ^ 2 = u := by
    rw [hP, ← cpow_nat_mul]; norm_num
  have hq : u ^ (-(1 / 2 : ℂ)) = P⁻¹ := by rw [cpow_neg]
  set ea := exp ((a : ℂ) * I) with hea
  have hc := struveSc_cos_pos ha
  set Z := ea * u + ea * P with hZ
  have hZre : (1 + r ^ 2) * Real.cos a ≤ Z.re := by
    have h1 : (ea * u).re = (1 + r ^ 2) * Real.cos a := by
      rw [hea, hu, struveSc_sq, exp_mul_I, ← ofReal_cos, ← ofReal_sin]
      simp only [mul_re, add_re, ofReal_re, mul_im, ofReal_im, I_re, I_im, add_im, mul_zero,
        sub_zero, mul_one, zero_add, one_re, one_im, sub_re, sub_im]
      rw [Real.cos_two_mul, Real.sin_two_mul]
      linear_combination (2 * r ^ 2 * Real.cos a) * Real.sin_sq_add_cos_sq a
    have h2 := struveSc_re_rot_P ha r
    simp only [hZ, add_re]
    rw [h1]; linarith
  have hZ0 : Z ≠ 0 := by
    intro h; rw [h, zero_re] at hZre; nlinarith [sq_nonneg r]
  have hkey : ea * (1 - u ^ (-(1 / 2 : ℂ))) * Z = (r : ℂ) ^ 2 := by
    have hee : ea * ea * w ^ 2 = (r : ℂ) ^ 2 := by
      rw [hw, hea, mul_pow, ← exp_nat_mul]
      have h1 : cexp (↑a * I) * cexp (↑a * I) * cexp (((2 : ℕ) : ℂ) * (((-a : ℝ) : ℂ) * I)) = 1 := by
        rw [← exp_add, ← exp_add]; push_cast; ring_nf; exact exp_zero
      linear_combination (r : ℂ) ^ 2 * h1
    rw [hq, hZ, ← hee, show w ^ 2 = P ^ 2 - 1 by rw [hP2, hu]; ring]
    field_simp
    linear_combination ea ^ 2 * (1 - P) * hP2
  have hX : ea * (1 - u ^ (-(1 / 2 : ℂ))) = ((r ^ 2 : ℝ) : ℂ) / Z := by
    rw [eq_div_iff hZ0, hkey]; push_cast; ring
  have hwn : ‖w‖ = |r| := by
    rw [hw, norm_mul, norm_exp_ofReal_mul_I, mul_one, norm_real, Real.norm_eq_abs]
  have hun : ‖u‖ ≤ 1 + r ^ 2 := by
    rw [hu]; refine (norm_add_le _ _).trans ?_
    rw [norm_one, norm_pow, hwn, sq_abs]
  have hPn : ‖P‖ ≤ 1 + r ^ 2 := by
    have h2 : ‖P‖ ^ 2 = ‖u‖ := by rw [← norm_pow, hP2]
    nlinarith [norm_nonneg P, sq_nonneg r]
  have hZn : ‖Z‖ ≤ 2 * (1 + r ^ 2) := by
    rw [hZ]; refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, hea, norm_exp_ofReal_mul_I]; linarith
  rw [hX, div_re, ofReal_re, ofReal_im, zero_mul, zero_div, add_zero]
  have hnp : 0 < normSq Z := normSq_pos.2 hZ0
  have hns : normSq Z ≤ 4 * (1 + r ^ 2) ^ 2 := by
    rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg Z]
  rw [div_le_div_iff₀ (by positivity) hnp]
  have h1 := mul_le_mul_of_nonneg_left hns (mul_nonneg hc.le (sq_nonneg r))
  have h2 := mul_le_mul_of_nonneg_left hZre (by positivity : (0 : ℝ) ≤ 4 * r ^ 2 * (1 + r ^ 2))
  nlinarith

/-- Growth of the `λ = 1` phase: `re (ν Ψ₁(r e^{-ia})) ≥ cos a · ρ r³/(12(1+r²))`. -/
theorem struveSc_re_phase_one_ge {a : ℝ} (ha : |a| < π / 2) {ρ : ℝ}
    (hρ : 0 ≤ ρ) {r : ℝ} (hr : 0 ≤ r) :
    Real.cos a * ρ * (r ^ 3 / (12 * (1 + r ^ 2))) ≤
      ((ρ : ℂ) * exp ((2 * a : ℝ) * I) *
        struveSc_phase 1 ((r : ℂ) * exp (((-a : ℝ) : ℂ) * I))).re := by
  set ν : ℂ := (ρ : ℂ) * exp ((2 * a : ℝ) * I) with hν
  set h : ℝ → ℝ := fun s => s ^ 3 / (12 * (1 + s ^ 2)) with hh
  have hhd : ∀ s, HasDerivAt h (s ^ 2 * (3 + s ^ 2) / (12 * (1 + s ^ 2) ^ 2)) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => s ^ 3) (3 * s ^ 2) s := by simpa using hasDerivAt_pow 3 s
    have h2 : HasDerivAt (fun s : ℝ => 12 * (1 + s ^ 2)) (12 * (2 * s)) s := by
      simpa using ((hasDerivAt_pow 2 s).const_add 1).const_mul 12
    have h3 := h1.div h2 (by positivity)
    convert h3 using 1
    field_simp; ring
  set g : ℝ → ℝ := fun s => (ν * struveSc_phase 1 ((s : ℂ) * exp (((-a : ℝ) : ℂ) * I))).re -
    Real.cos a * ρ * h s with hg
  have hνE : ν * exp (((-a : ℝ) : ℂ) * I) = (ρ : ℂ) * exp ((a : ℂ) * I) := by
    rw [hν, mul_assoc, ← exp_add]; congr 2; push_cast; ring
  have hderiv : ∀ s : ℝ, 0 ≤ s → HasDerivAt g
      ((ν * (exp (((-a : ℝ) : ℂ) * I) * (((1 : ℝ) : ℂ) -
        (1 + ((s : ℂ) * exp (((-a : ℝ) : ℂ) * I)) ^ 2) ^ (-(1 / 2 : ℂ))))).re -
        Real.cos a * ρ * (s ^ 2 * (3 + s ^ 2) / (12 * (1 + s ^ 2) ^ 2))) s := by
    intro s hs
    exact (struveSc_hasDerivAt_re ((struveSc_hasDerivAt_phase_ray 1 ha hs).const_mul ν)).sub
      ((hhd s).const_mul _)
  have hc := struveSc_cos_pos ha
  have hmono : MonotoneOn g (Ici 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0) (f' := fun s =>
      (ν * (exp (((-a : ℝ) : ℂ) * I) * (((1 : ℝ) : ℂ) -
        (1 + ((s : ℂ) * exp (((-a : ℝ) : ℂ) * I)) ^ 2) ^ (-(1 / 2 : ℂ))))).re -
        Real.cos a * ρ * (s ^ 2 * (3 + s ^ 2) / (12 * (1 + s ^ 2) ^ 2))) ?_ ?_ ?_
    · exact fun s hs => (hderiv s hs).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Ici] at hs ⊢
      exact (hderiv s (le_of_lt hs)).hasDerivWithinAt
    · intro s hs
      rw [interior_Ici] at hs
      have hpos := struveSc_re_one_sub_q_ge ha s
      rw [← mul_assoc, hνE, sub_nonneg, ofReal_one, mul_assoc (ρ : ℂ), re_ofReal_mul]
      have hs2 : s ^ 2 * (3 + s ^ 2) / (12 * (1 + s ^ 2) ^ 2) ≤ s ^ 2 / (4 * (1 + s ^ 2)) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [sq_nonneg s, pow_nonneg (sq_nonneg s) 2, mul_nonneg (sq_nonneg s) (sq_nonneg s)]
      calc Real.cos a * ρ * (s ^ 2 * (3 + s ^ 2) / (12 * (1 + s ^ 2) ^ 2))
          ≤ Real.cos a * ρ * (s ^ 2 / (4 * (1 + s ^ 2))) := by gcongr
        _ = ρ * (Real.cos a * s ^ 2 / (4 * (1 + s ^ 2))) := by ring
        _ ≤ _ := by gcongr
  have h0 : g 0 = 0 := by simp [hg, hh, struveSc_phase_zero]
  have := hmono (mem_Ici.2 le_rfl) (show r ∈ Ici (0 : ℝ) from hr) hr
  rw [h0] at this
  simp only [hg, hh] at this
  linarith

/-- `‖Ψ₁(w) - w³/6‖ ≤ (1/2 + K)/5 · r⁵` on the ray `w = r e^{-ia}`, given `‖q‖ ≤ K`. -/
theorem struveSc_phase_one_sub_cube {a : ℝ} (ha : |a| < π / 2) {K : ℝ}
    (hK : ∀ s : ℝ, 0 ≤ s →
      ‖(1 + ((s : ℂ) * exp (((-a : ℝ) : ℂ) * I)) ^ 2) ^ (-(1 / 2 : ℂ))‖ ≤ K)
    {r : ℝ} (hr : 0 ≤ r) :
    ‖struveSc_phase 1 ((r : ℂ) * exp (((-a : ℝ) : ℂ) * I)) -
      ((r : ℂ) * exp (((-a : ℝ) : ℂ) * I)) ^ 3 / 6‖ ≤ (1 / 2 + K) / 5 * r ^ 5 := by
  set E := exp (((-a : ℝ) : ℂ) * I) with hE
  have hpt : ∀ s : ℝ, 0 ≤ s → ‖(1 - (1 + ((s : ℂ) * E) ^ 2) ^ (-(1 / 2 : ℂ))) -
      ((s : ℂ) * E) ^ 2 / 2‖ ≤ (1 / 2 + K) * s ^ 4 := by
    intro s hs
    have hqK := hK s hs
    set w := (s : ℂ) * E with hw
    set u := 1 + w ^ 2 with hu
    set P := u ^ (1 / 2 : ℂ) with hP
    have hmem : u ∈ slitPlane := struveSc_mem_slitPlane ha
    have hu0 : u ≠ 0 := slitPlane_ne_zero hmem
    have hP0 : P ≠ 0 := by
      rw [hP]; exact (cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num)).2 hu0
    have hP2 : P ^ 2 = u := by rw [hP, ← cpow_nat_mul]; norm_num
    have hq : u ^ (-(1 / 2 : ℂ)) = P⁻¹ := by rw [cpow_neg]
    have hP1 : 1 ≤ ‖P + 1‖ := by
      have := struveSc_re_cpow_half_nonneg u
      have h := Complex.re_le_norm (P + 1)
      rw [add_re, one_re] at h
      linarith
    have hwn : ‖w‖ = s := by
      rw [hw, norm_mul, hE, norm_exp_ofReal_mul_I, mul_one, norm_real, Real.norm_of_nonneg hs]
    have hPm1 : (P - 1) * (P + 1) = w ^ 2 := by
      rw [show w ^ 2 = P ^ 2 - 1 by rw [hP2, hu]; ring]; ring
    have hPm1n : ‖P - 1‖ ≤ s ^ 2 := by
      have : ‖P - 1‖ * ‖P + 1‖ = s ^ 2 := by rw [← norm_mul, hPm1, norm_pow, hwn]
      nlinarith [norm_nonneg (P - 1)]
    have hid : (1 - u ^ (-(1 / 2 : ℂ))) - w ^ 2 / 2 = -((P - 1) ^ 2 * (P + 2)) / (2 * P) := by
      rw [hq, show w ^ 2 = P ^ 2 - 1 by rw [hP2, hu]; ring]; field_simp; ring
    rw [hq, norm_inv] at hqK
    have hPp : 0 < ‖P‖ := norm_pos_iff.2 hP0
    have hKP : 1 ≤ K * ‖P‖ := by
      rwa [inv_le_iff_one_le_mul₀ hPp] at hqK
    rw [hid, norm_div, norm_neg, norm_mul, norm_mul, norm_pow, div_le_iff₀ (mul_pos (by norm_num) hPp)]
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2]
    have hP2n : ‖P + 2‖ ≤ ‖P‖ + 2 := by
      refine (norm_add_le _ _).trans ?_; simp
    have hsq : ‖P - 1‖ ^ 2 ≤ s ^ 4 := by
      rw [show s ^ 4 = (s ^ 2) ^ 2 by ring]
      exact pow_le_pow_left₀ (norm_nonneg _) hPm1n 2
    calc ‖P - 1‖ ^ 2 * ‖P + 2‖ ≤ s ^ 4 * (‖P‖ + 2) := by
          gcongr
      _ ≤ (1 / 2 + K) * s ^ 4 * (2 * ‖P‖) := by
          nlinarith [pow_nonneg hs 4]
  set f : ℝ → ℂ := fun s => struveSc_phase 1 ((s : ℂ) * E) - ((s : ℂ) * E) ^ 3 / 6 with hf
  have hfd : ∀ s : ℝ, 0 ≤ s → HasDerivAt f
      (E * ((1 - (1 + ((s : ℂ) * E) ^ 2) ^ (-(1 / 2 : ℂ))) - ((s : ℂ) * E) ^ 2 / 2)) s := by
    intro s hs
    have h1 := struveSc_hasDerivAt_phase_ray 1 ha hs
    have h2 := (((hasDerivAt_id s).ofReal_comp.mul_const E).pow 3).div_const 6
    refine (h1.fun_sub h2).congr_deriv ?_
    rw [← hE]; simp only [id, ofReal_one, one_mul]; push_cast; ring
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := f) (a := 0) (b := r)
    (f' := fun s => E * ((1 - (1 + ((s : ℂ) * E) ^ 2) ^ (-(1 / 2 : ℂ))) - ((s : ℂ) * E) ^ 2 / 2))
    (B := fun s => (1 / 2 + K) / 5 * s ^ 5) (B' := fun s => (1 / 2 + K) * s ^ 4)
    (fun s hs => (hfd s hs.1).continuousAt.continuousWithinAt)
    (fun s hs => (hfd s hs.1).hasDerivWithinAt)
    (by simp [hf, struveSc_phase_zero])
    (fun s => by
      have := (hasDerivAt_pow 5 s).const_mul ((1 / 2 + K) / 5)
      convert this using 1; push_cast; ring)
    (fun s hs => by
      rw [norm_mul, hE, norm_exp_ofReal_mul_I, one_mul]; exact hpt s hs.1)
    (right_mem_Icc.2 hr)
  simpa [hf] using key

/-- `∫₀^∞ e^{-b r³} rⁿ dr = b^{-(n+1)/3} Γ((n+1)/3)/3`, with integrability. -/
theorem struveSc_integral_pow_exp_cube (n : ℕ) {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun r : ℝ => Real.exp (-(b * r ^ 3)) * r ^ n) (Ioi 0) ∧
    ∫ r in Ioi (0 : ℝ), Real.exp (-(b * r ^ 3)) * r ^ n =
      b ^ (-((n : ℝ) + 1) / 3) * (1 / 3) * Real.Gamma (((n : ℝ) + 1) / 3) := by
  have hcongr : EqOn (fun r : ℝ => r ^ (n : ℝ) * Real.exp (-b * r ^ (3 : ℝ)))
      (fun r : ℝ => Real.exp (-(b * r ^ 3)) * r ^ n) (Ioi 0) := by
    intro r _
    simp only [Real.rpow_natCast, neg_mul]
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
  have hn : (-1 : ℝ) < n := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  refine ⟨(integrableOn_rpow_mul_exp_neg_mul_rpow hn (by norm_num) hb).congr_fun hcongr
    measurableSet_Ioi, ?_⟩
  rw [← setIntegral_congr_fun measurableSet_Ioi hcongr,
    integral_rpow_mul_exp_neg_mul_rpow (by norm_num) hn hb]

/-- `∫₀^∞ e^{-C r³} dr = Γ(4/3) C^{-1/3}` for `re C > 0`. -/
theorem struveSc_integral_exp_cube {C : ℂ} (hC : 0 < C.re) :
    ∫ r in Ioi (0 : ℝ), exp (-(C * (r : ℂ) ^ 3)) = Gamma (4 / 3) * C ^ (-(1 / 3 : ℂ)) := by
  have hsub := integral_comp_rpow_Ioi (fun y : ℝ => exp (-(C * (y : ℂ) ^ 3)))
    (p := 1 / 3) (by norm_num)
  rw [← hsub]
  have hG := integral_cpow_mul_cexp_neg_mul_Ioi (s := 1 / 3) (z := C) (by norm_num) hC
  have h43 : Gamma (4 / 3 : ℂ) = 1 / 3 * Gamma (1 / 3) := by
    rw [show (4 / 3 : ℂ) = 1 / 3 + 1 by norm_num, Gamma_add_one _ (by norm_num)]
  rw [h43, mul_assoc, show (-(1 / 3 : ℂ)) = -(1 / 3) from rfl, ← hG, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx0 : 0 < x := hx
  simp only [Complex.real_smul]
  have h3 : ((x ^ (1 / 3 : ℝ) : ℝ) : ℂ) ^ 3 = (x : ℂ) := by
    rw [← ofReal_pow, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
  rw [h3]
  have hc : ((|(1 / 3 : ℝ)| * x ^ ((1 / 3 : ℝ) - 1) : ℝ) : ℂ) =
      1 / 3 * (x : ℂ) ^ ((1 / 3 : ℂ) - 1) := by
    rw [abs_of_pos (by norm_num), ofReal_mul, ofReal_cpow hx0.le]; push_cast; ring
  rw [hc, mul_comm C]; ring

/-- Integrability of `e^{-C r³}` on `(0,∞)` for `re C > 0`. -/
theorem struveSc_integrableOn_exp_cube {C : ℂ} (hC : 0 < C.re) :
    IntegrableOn (fun r : ℝ => exp (-(C * (r : ℂ) ^ 3))) (Ioi 0) := by
  obtain ⟨hi, -⟩ := struveSc_integral_pow_exp_cube 0 hC
  refine Integrable.mono' hi ((by fun_prop : Continuous fun r : ℝ =>
    exp (-(C * (r : ℂ) ^ 3))).aestronglyMeasurable) ((ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun r _ => ?_))
  rw [norm_exp, pow_zero, mul_one, neg_re, ← ofReal_pow, mul_comm, re_ofReal_mul, mul_comm]

/-- `e^{-c ρ r³/(12(1+r²))} ≤ e^{-β r³} + e^{-β r}` with `β = cρ/24`. -/
theorem struveSc_exp_split {c ρ r : ℝ} (hc : 0 ≤ c) (hρ : 0 ≤ ρ) (hr : 0 ≤ r) :
    Real.exp (-(c * ρ * (r ^ 3 / (12 * (1 + r ^ 2))))) ≤
      Real.exp (-(c / 24 * ρ * r ^ 3)) + Real.exp (-(c / 24 * ρ * r)) := by
  have hcρ : 0 ≤ c * ρ := mul_nonneg hc hρ
  rcases le_total r 1 with h | h
  · have : c / 24 * ρ * r ^ 3 ≤ c * ρ * (r ^ 3 / (12 * (1 + r ^ 2))) := by
      rw [show c / 24 * ρ * r ^ 3 = c * ρ * (r ^ 3 / 24) by ring]
      refine mul_le_mul_of_nonneg_left ?_ hcρ
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      nlinarith [pow_nonneg hr 3, mul_nonneg (pow_nonneg hr 3) (sq_nonneg r), sq_nonneg r,
        mul_le_mul_of_nonneg_left (pow_le_one₀ hr h : r ^ 2 ≤ 1) (pow_nonneg hr 3)]
    linarith [Real.exp_le_exp.2 (neg_le_neg this), Real.exp_pos (-(c / 24 * ρ * r))]
  · have : c / 24 * ρ * r ≤ c * ρ * (r ^ 3 / (12 * (1 + r ^ 2))) := by
      rw [show c / 24 * ρ * r = c * ρ * (r / 24) by ring]
      refine mul_le_mul_of_nonneg_left ?_ hcρ
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      nlinarith [one_le_pow₀ h (n := 2), mul_le_mul_of_nonneg_left (one_le_pow₀ h (n := 2) : 1 ≤ r ^ 2) hr]
    linarith [Real.exp_le_exp.2 (neg_le_neg this), Real.exp_pos (-(c / 24 * ρ * r ^ 3))]

end StruveScaled
end DLMF.Struve
end
