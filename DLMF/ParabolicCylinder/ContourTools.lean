/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ParabolicCylinder.IntegralTools
public import DLMFMathlib.Analysis.Complex.BarnesResidue

/-!
# Contour tools for the parabolic cylinder integrals (DLMF 12.5.5–12.5.7)

* Vertical lines `t = c + iy`, `c > 0`: a Gaussian majorant `pcfCt_dom` for
  `e^{-zt+t²/2} t^p`, locally uniform in `z` and `p` (`pcfCt_vert_le`), and the shifted
  Gaussian integral `∫ e^{-wt+t²/2} dy = √(2π) e^{-w²/2}` (`pcfCt_gauss_vertical`).
* DLMF 12.5.6 in integral form (`pcfCt_vertical`): for `re a > -1/2`, Euler's integral
  `Γ(a+1/2) t^{-a-1/2} = ∫₀^∞ s^{a-1/2} e^{-ts} ds` (complex scale, `integral_cpow_mul_cexp_neg_mul_Ioi`),
  Fubini and the Gaussian reduce the vertical integral to DLMF 12.5.1 (`pcfU_eq_integral`);
  holomorphy in `a` (`pcfCt_vertical_differentiable`) and the identity theorem give all `a`.
* The horizontal lines `t = x ± ic` of DLMF 12.5.7 are the vertical lines rotated by `±π/2`
  (`pcfCt_horizontal_upper`, `pcfCt_horizontal_lower`).
* The Hankel loop of DLMF 12.5.5: in the variable `w = log t` the loop integrand is the entire
  function `pcfCt_F`, and the circle part `pcfCt_C` at radius `r` is its integral over the
  segment `log r + iθ`, `|θ| ≤ π`. Cauchy's theorem on the rectangle between two radii gives
  `pcfCt_C r₂ - pcfCt_C r₁ = κ(a) ∫_{r₁}^{r₂} t^{a-1/2} e^{-t²/2-zt} dt` (`pcfCt_C_sub`), with
  the jump `κ(a) = e^{-iπ(a-1/2)} - e^{iπ(a-1/2)}`. For `re a > -1/2` the circle shrinks to zero
  (`pcfCt_loop_limit_of_re`), and DLMF 12.5.1 with the reflection formula
  (`pcfCt_kappa_Gamma`) gives the value; holomorphy in `a` of the tail and of the circle part
  extends it to all `a` (`pcfCt_loop_value`).
* The kernel of DLMF 12.12.3 (`pcfCt_kernel`): for `0 < re μ < 2`, `x > 0`, `σ ≥ 0`,
  `∫₀^∞ t^{μ-1} cos(tσ + π/2 - πμ/2)/(x²+t²) dt = (π/2) x^{μ-2} e^{-xσ}`. In `w = log t` the
  two exponential halves are integrals of `pcfCt_Phi` over the lines `Im w = 0` and `Im w = π`;
  the vertical-shift residue lemma `Complex.barnesRes_vertical_shift` (after rotating by `i`)
  relates them through the residue at `w = log x + iπ/2` (`pcfCt_kernel_shift`).
* `pcfCt_U_decay`: `|e^{-t²/4} U(a,t)| ≤ M e^{-t}` on the real line, locally uniformly in `a`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Metric DLMF DLMF.Hypergeometric
open scoped Real Topology

namespace DLMF.Confluent

/-- Growth of `e^{-zt+t²/2}` on the vertical line `t = c+iy`. -/
theorem pcfCt_norm_exp_le (z : ℂ) {c : ℝ} (hc : 0 ≤ c) (y : ℝ) :
    ‖exp (-z*((c:ℂ)+y*I) + ((c:ℂ)+y*I)^2/2)‖ ≤
      Real.exp (‖z‖*c + c^2/2 + ‖z‖*|y| - y^2/2) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have h1 : (-z*((c:ℂ)+y*I) + ((c:ℂ)+y*I)^2/2).re = -(z.re*c) + z.im*y + (c^2 - y^2)/2 := by
    simp [sq]; ring
  rw [h1]
  have hr := abs_re_le_norm z
  have hi := abs_im_le_norm z
  have e1 : -(z.re*c) ≤ ‖z‖*c := by
    nlinarith [neg_abs_le z.re]
  have e2 : z.im*y ≤ ‖z‖*|y| := by
    calc z.im*y ≤ |z.im*y| := le_abs_self _
      _ = |z.im| * |y| := abs_mul _ _
      _ ≤ ‖z‖*|y| := by gcongr
  linarith

/-- Growth of `t^p` on the vertical line `t = c+iy`, `c > 0`. -/
theorem pcfCt_norm_cpow_le (p : ℂ) {c : ℝ} (hc : 0 < c) (y : ℝ) :
    ‖((c:ℂ)+y*I)^p‖ ≤ Real.exp (‖p‖*(|Real.log c| + π) + ‖p‖/c*|y|) := by
  set t : ℂ := (c:ℂ)+y*I
  have ht1 : c ≤ ‖t‖ := by
    have := re_le_norm t; simpa [t] using this
  have ht2 : ‖t‖ ≤ c + |y| := by
    refine (norm_add_le _ _).trans ?_
    simp [abs_of_pos hc]
  have htp : 0 < ‖t‖ := lt_of_lt_of_le hc ht1
  refine (pcfInt_norm_cpow_le t p).trans ?_
  rw [Real.rpow_def_of_pos htp, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hl1 : Real.log c ≤ Real.log ‖t‖ := Real.log_le_log hc ht1
  have hl2 : Real.log ‖t‖ ≤ Real.log c + |y|/c := by
    have : Real.log ‖t‖ ≤ Real.log (c + |y|) := Real.log_le_log htp ht2
    have h2 : Real.log (c + |y|) = Real.log c + Real.log (1 + |y|/c) := by
      rw [← Real.log_mul hc.ne' (by positivity)]; congr 1; field_simp
    have h3 : Real.log (1 + |y|/c) ≤ |y|/c := by
      have := Real.log_le_sub_one_of_pos (show 0 < 1 + |y|/c by positivity); linarith
    linarith
  have hab : |Real.log ‖t‖| ≤ |Real.log c| + |y|/c := by
    rw [abs_le]; constructor
    · linarith [neg_abs_le (Real.log c)]
    · linarith [le_abs_self (Real.log c)]
  have hre : Real.log ‖t‖ * p.re ≤ ‖p‖ * (|Real.log c| + |y|/c) := by
    calc Real.log ‖t‖ * p.re ≤ |Real.log ‖t‖ * p.re| := le_abs_self _
      _ = |Real.log ‖t‖| * |p.re| := abs_mul _ _
      _ ≤ (|Real.log c| + |y|/c) * ‖p‖ := by gcongr; exact abs_re_le_norm p
      _ = _ := by ring
  have him : π * |p.im| ≤ ‖p‖ * π := by
    rw [mul_comm]; gcongr; exact abs_im_le_norm p
  have : ‖p‖ * (|Real.log c| + |y|/c) = ‖p‖*|Real.log c| + ‖p‖/c*|y| := by ring
  nlinarith

/-- Dominating Gaussian for the vertical-line integrands. -/
noncomputable def pcfCt_dom (Z P c y : ℝ) : ℝ :=
  Real.exp (Z*c + c^2/2 + P*(|Real.log c| + π) + (Z + P/c)^2) * Real.exp (-(1/4) * y^2)

/-- The majorant `pcfCt_dom` is integrable. -/
theorem pcfCt_dom_integrable (Z P c : ℝ) : Integrable (pcfCt_dom Z P c) :=
  (integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/4)).const_mul _

/-- The vertical-line integrand is dominated by `pcfCt_dom`, uniformly for `‖z‖ ≤ Z`, `‖p‖ ≤ P`. -/
theorem pcfCt_vert_le {z p : ℂ} {Z P c : ℝ} (hc : 0 < c) (hZ : ‖z‖ ≤ Z) (hP : ‖p‖ ≤ P) (y : ℝ) :
    ‖exp (-z*((c:ℂ)+y*I) + ((c:ℂ)+y*I)^2/2) * ((c:ℂ)+y*I)^p‖ ≤ pcfCt_dom Z P c y := by
  rw [norm_mul]
  have h1 := pcfCt_norm_exp_le z hc.le y
  have h2 := pcfCt_norm_cpow_le p hc y
  refine (mul_le_mul h1 h2 (norm_nonneg _) (Real.exp_pos _).le).trans ?_
  rw [pcfCt_dom, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hy := abs_nonneg y
  have hy2 : |y|^2 = y^2 := sq_abs y
  have hZ0 : 0 ≤ Z := (norm_nonneg _).trans hZ
  have hP0 : 0 ≤ P := (norm_nonneg _).trans hP
  have hl : 0 ≤ |Real.log c| + π := by positivity
  have k1 : ‖z‖*c ≤ Z*c := by gcongr
  have k2 : ‖z‖*|y| ≤ Z*|y| := by gcongr
  have k3 : ‖p‖*(|Real.log c| + π) ≤ P*(|Real.log c| + π) := by gcongr
  have k4 : ‖p‖/c*|y| ≤ P/c*|y| := by gcongr
  nlinarith [sq_nonneg (Z + P/c - |y|/2)]

/-- The Gaussian on a vertical line: `∫ e^{-wt+t²/2} dy = √(2π) e^{-w²/2}`, `t = c+iy`. -/
theorem pcfCt_gauss_vertical (w : ℂ) (c : ℝ) :
    ∫ y : ℝ, exp (-w*((c:ℂ)+y*I) + ((c:ℂ)+y*I)^2/2) = (Real.sqrt (2*π) : ℂ) * exp (-w^2/2) := by
  have h : (fun y : ℝ => exp (-w*((c:ℂ)+y*I) + ((c:ℂ)+y*I)^2/2)) =
      fun y : ℝ => exp ((-1/2:ℂ) * y^2 + ((c - w)*I) * y + (c^2/2 - w*c)) := by
    funext y; congr 1; ring_nf; rw [I_sq]; ring
  rw [h, integral_cexp_quadratic (by norm_num) _ _]
  have e1 : (π / -(-1/2:ℂ)) ^ (1/2:ℂ) = (Real.sqrt (2*π) : ℂ) := by
    rw [show (π / -(-1/2:ℂ)) = ((2*π : ℝ) : ℂ) by push_cast; ring, Real.sqrt_eq_rpow,
      ofReal_cpow (by positivity)]
    norm_num
  rw [e1]; congr 2
  field_simp
  ring_nf; rw [I_sq]; ring

/-- Integrability of the Gaussian on a vertical line. -/
theorem pcfCt_gauss_vertical_integrable (w : ℂ) (c : ℝ) :
    Integrable (fun y : ℝ => exp (-w*((c:ℂ)+y*I) + ((c:ℂ)+y*I)^2/2)) := by
  have h : (fun y : ℝ => exp (-w*((c:ℂ)+y*I) + ((c:ℂ)+y*I)^2/2)) =
      fun y : ℝ => exp ((-1/2:ℂ) * y^2 + ((c - w)*I) * y + (c^2/2 - w*c)) := by
    funext y; congr 1; ring_nf; rw [I_sq]; ring
  rw [h]; exact integrable_cexp_quadratic' (by norm_num) _ _

/-- Continuity of the vertical-line integrand in `y`. -/
theorem pcfCt_vert_continuous (z p : ℂ) {c : ℝ} (hc : 0 < c) :
    Continuous (fun y : ℝ => exp (-z*((c:ℂ)+y*I) + ((c:ℂ)+y*I)^2/2) * ((c:ℂ)+y*I)^p) := by
  refine (by fun_prop : Continuous fun y : ℝ => exp (-z*((c:ℂ)+y*I) + ((c:ℂ)+y*I)^2/2)).mul ?_
  exact (by fun_prop : Continuous fun y : ℝ => (c:ℂ)+y*I).cpow continuous_const fun y =>
    mem_slitPlane_iff.mpr (Or.inl (by simp [hc]))

/-- Integrability of the vertical-line integrand. -/
theorem pcfCt_vert_integrable (z p : ℂ) {c : ℝ} (hc : 0 < c) :
    Integrable (fun y : ℝ => exp (-z*((c:ℂ)+y*I) + ((c:ℂ)+y*I)^2/2) * ((c:ℂ)+y*I)^p) :=
  (pcfCt_dom_integrable ‖z‖ ‖p‖ c).mono' (pcfCt_vert_continuous z p hc).aestronglyMeasurable
    (Eventually.of_forall fun y => pcfCt_vert_le hc le_rfl le_rfl y)

/-- DLMF 12.5.6 in integral form for `re a > -1/2` (Fubini against Euler's integral). -/
theorem pcfCt_vertical_of_re {a : ℂ} (ha : -1/2 < a.re) (z : ℂ) {c : ℝ} (hc : 0 < c) :
    ∫ y : ℝ, exp (-z*((c:ℂ)+y*I) + ((c:ℂ)+y*I)^2/2) * ((c:ℂ)+y*I)^(-a-1/2) =
      (Real.sqrt (2*π) : ℂ) * exp (-z^2/4) * pcfU a z := by
  set T : ℝ → ℂ := fun y => (c:ℂ)+y*I with hT
  set E : ℝ → ℂ := fun y => exp (-z*T y + (T y)^2/2) with hE
  have hs : 0 < (a+1/2).re := by simp; linarith
  have hTre : ∀ y, 0 < (T y).re := fun y => by simp [hT, hc]
  have hEul : ∀ y, ∫ s in Ioi (0:ℝ), (s:ℂ)^(a-1/2) * exp (-(T y * s)) =
      Gamma (a+1/2) * (T y)^(-a-1/2) := fun y => by
    have := integral_cpow_mul_cexp_neg_mul_Ioi hs (hTre y)
    rw [show a + 1/2 - 1 = a - 1/2 by ring, show -(a+1/2) = -a-1/2 by ring] at this
    exact this
  set F : ℝ × ℝ → ℂ := fun q => E q.1 * ((q.2:ℂ)^(a-1/2) * exp (-(T q.1 * q.2))) with hF
  -- integrability on the product
  have hEn : ∀ y, ‖E y‖ ≤ pcfCt_dom ‖z‖ 0 c y := fun y => by
    have := pcfCt_vert_le (z := z) (p := 0) (P := 0) hc le_rfl (by simp) y
    simpa [hE, hT] using this
  have hSi : Integrable (fun s : ℝ => s^(a.re - 1/2) * Real.exp (-c*s)) (volume.restrict (Ioi 0)) := by
    have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := a.re - 1/2) (b := c)
      (by linarith) one_pos hc
    simpa only [Real.rpow_one, IntegrableOn] using this
  have hprod : Integrable F (volume.prod (volume.restrict (Ioi 0))) := by
    have hP := (pcfCt_dom_integrable ‖z‖ 0 c).mul_prod hSi
    refine hP.mono' ?_ ?_
    · refine Measurable.aestronglyMeasurable ?_
      simp only [hF, hE, hT]
      fun_prop
    · have hae := (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ))
        (ν := volume.restrict (Ioi (0:ℝ)))).ae (ae_restrict_mem measurableSet_Ioi)
      filter_upwards [hae] with q hq
      have hq : 0 < q.2 := hq
      rw [hF]; dsimp only
      have h1 : (-(T q.1 * (q.2:ℂ))).re = -c * q.2 := by simp [hT]
      have h2 : (a - 1/2).re = a.re - 1/2 := by simp
      rw [norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos hq, Complex.norm_exp (-(T q.1 * (q.2:ℂ))),
        h1, h2]
      exact mul_le_mul_of_nonneg_right (hEn q.1) (by positivity)
  have hG0 : Gamma (a+1/2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs
  have hL : Gamma (a+1/2) * ∫ y : ℝ, E y * (T y)^(-a-1/2) = ∫ y : ℝ, ∫ s in Ioi (0:ℝ), F (y, s) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [hF]
    rw [integral_const_mul, hEul]; ring
  have hR : ∀ s : ℝ, ∫ y : ℝ, F (y, s) =
      (s:ℂ)^(a-1/2) * ((Real.sqrt (2*π) : ℂ) * exp (-(z+s)^2/2)) := fun s => by
    rw [← pcfCt_gauss_vertical (z+s) c, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [hF, hE, hT]
    rw [mul_left_comm, ← Complex.exp_add]; congr 2; ring
  rw [integral_integral_swap hprod] at hL
  simp_rw [hR] at hL
  have hU := pcfU_eq_integral (show -1/2 < a.re from ha) z
  have hJ : ∫ s in Ioi (0:ℝ), (s:ℂ)^(a-1/2) * ((Real.sqrt (2*π) : ℂ) * exp (-(z+s)^2/2)) =
      (Real.sqrt (2*π) : ℂ) * exp (-z^2/2) *
        ∫ t in Ioi (0:ℝ), (t:ℂ)^(a-1/2) * exp (-(t:ℂ)^2/2 - z*t) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    rw [show (-(z+s)^2/2 : ℂ) = -z^2/2 + (-(s:ℂ)^2/2 - z*s) by ring, Complex.exp_add]; ring
  rw [hJ] at hL
  have hGa : Gamma (1/2+a) = Gamma (a+1/2) := by rw [add_comm]
  rw [hGa] at hU
  have he : exp (-z^2/2) = exp (-z^2/4) * exp (-z^2/4) := by rw [← Complex.exp_add]; ring_nf
  apply mul_left_cancel₀ hG0
  rw [hL, hU, he]
  generalize Gamma (a+1/2) = G at hG0 ⊢
  generalize (∫ t in Ioi (0:ℝ), (t:ℂ)^(a-1/2) * exp (-(t:ℂ)^2/2 - z*t)) = J
  field_simp

/-- The vertical-line integral is entire in the parameter. -/
theorem pcfCt_vertical_differentiable (z : ℂ) {c : ℝ} (hc : 0 < c) :
    Differentiable ℂ (fun a : ℂ =>
      ∫ y : ℝ, exp (-z*((c:ℂ)+y*I) + ((c:ℂ)+y*I)^2/2) * ((c:ℂ)+y*I)^(-a-1/2)) := by
  refine differentiableOn_univ.mp (differentiableOn_integral_of_locally_dominated isOpen_univ
    (fun a _ => (pcfCt_vert_continuous z (-a-1/2) hc).aestronglyMeasurable) ?_ ?_)
  · refine Eventually.of_forall fun y a _ => ?_
    have hT0 : ((c:ℂ)+y*I) ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    exact ((differentiableAt_const _).mul
      ((differentiableAt_id.neg.sub_const _).const_cpow (Or.inl hT0))).differentiableWithinAt
  · intro a0 _
    refine ⟨ball a0 1, ball_mem_nhds _ one_pos, pcfCt_dom ‖z‖ (‖a0‖+3/2) c,
      pcfCt_dom_integrable _ _ _, Eventually.of_forall fun y a ha => ?_⟩
    refine pcfCt_vert_le hc le_rfl ?_ y
    rw [mem_ball, dist_eq_norm] at ha
    calc ‖-a-1/2‖ ≤ ‖a‖ + ‖(1/2:ℂ)‖ := by
          rw [show -a-1/2 = -(a + 1/2) by ring, norm_neg]; exact norm_add_le _ _
      _ ≤ (‖a0‖ + 1) + 1/2 := by
          gcongr
          · have := norm_le_norm_add_norm_sub' a a0
            linarith [norm_sub_rev a a0]
          · simp
      _ = ‖a0‖+3/2 := by ring

/-- DLMF 12.5.6 in integral form, all parameters. -/
theorem pcfCt_vertical (a z : ℂ) {c : ℝ} (hc : 0 < c) :
    ∫ y : ℝ, exp (-z*((c:ℂ)+y*I) + ((c:ℂ)+y*I)^2/2) * ((c:ℂ)+y*I)^(-a-1/2) =
      (Real.sqrt (2*π) : ℂ) * exp (-z^2/4) * pcfU a z := by
  have hf := pcfCt_vertical_differentiable z hc
  have hg : Differentiable ℂ (fun a : ℂ => (Real.sqrt (2*π) : ℂ) * exp (-z^2/4) * pcfU a z) :=
    (pcfU_entire_order z).const_mul _
  have heq : (fun a : ℂ =>
      ∫ y : ℝ, exp (-z*((c:ℂ)+y*I) + ((c:ℂ)+y*I)^2/2) * ((c:ℂ)+y*I)^(-a-1/2)) =ᶠ[𝓝 (1:ℂ)]
      (fun a : ℂ => (Real.sqrt (2*π) : ℂ) * exp (-z^2/4) * pcfU a z) := by
    have hopen : IsOpen {b : ℂ | -1/2 < b.re} := isOpen_lt continuous_const continuous_re
    filter_upwards [hopen.mem_nhds (show -1/2 < (1:ℂ).re by norm_num)] with b hb
    exact pcfCt_vertical_of_re hb z hc
  have hf' : AnalyticOnNhd ℂ (fun a : ℂ =>
      ∫ y : ℝ, exp (-z*((c:ℂ)+y*I) + ((c:ℂ)+y*I)^2/2) * ((c:ℂ)+y*I)^(-a-1/2)) univ :=
    fun x _ => hf.analyticAt x
  exact hf'.eqOn_of_preconnected_of_eventuallyEq (fun x _ => hg.analyticAt x) isPreconnected_univ
    (mem_univ 1) heq (mem_univ a)

/-- `(± i s)^w = s^w e^{± iπw/2}` for `re s > 0`. -/
theorem pcfCt_I_mul_cpow {s : ℂ} (hs : 0 < s.re) (w : ℂ) :
    (I*s)^w = s^w * exp (π/2*I*w) ∧ (-I*s)^w = s^w * exp (-(π/2)*I*w) := by
  have hs0 : s ≠ 0 := fun h => by rw [h] at hs; simp at hs
  have hz : |arg s| < π/2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hs)
  obtain ⟨h1, h2⟩ := abs_lt.mp hz
  have ha1 : arg (I*s) = arg s + π/2 := by
    rw [arg_mul I_ne_zero hs0 (by rw [arg_I]; constructor <;> linarith), arg_I]; ring
  have ha2 : arg (-I*s) = arg s - π/2 := by
    rw [arg_mul (neg_ne_zero.mpr I_ne_zero) hs0 (by rw [arg_neg_I]; constructor <;> linarith),
      arg_neg_I]; ring
  have hl1 : log (I*s) = log s + π/2*I := by
    apply Complex.ext
    · simp [log_re]
    · rw [log_im, ha1, add_im, log_im]; simp
  have hl2 : log (-I*s) = log s - π/2*I := by
    apply Complex.ext
    · simp [log_re]
    · rw [log_im, ha2, sub_im, log_im]; simp
  constructor
  · rw [cpow_def_of_ne_zero (mul_ne_zero I_ne_zero hs0), cpow_def_of_ne_zero hs0, hl1,
      ← Complex.exp_add]; congr 1; ring
  · rw [cpow_def_of_ne_zero (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hs0),
      cpow_def_of_ne_zero hs0, hl2, ← Complex.exp_add]; congr 1; ring

/-- The horizontal line above the axis, for DLMF 12.5.7. -/
theorem pcfCt_horizontal_upper (a z : ℂ) {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : ℝ => exp (z*((x:ℂ)+c*I) - ((x:ℂ)+c*I)^2/2) * ((x:ℂ)+c*I)^(a-1/2)) ∧
    ∫ x : ℝ, exp (z*((x:ℂ)+c*I) - ((x:ℂ)+c*I)^2/2) * ((x:ℂ)+c*I)^(a-1/2) =
      exp (I*π*(a/2-1/4)) * ((Real.sqrt (2*π) : ℂ) * exp (z^2/4) * pcfU (-a) (-I*z)) := by
  set G : ℝ → ℂ := fun y => exp (-(-I*z)*((c:ℂ)+y*I) + ((c:ℂ)+y*I)^2/2) * ((c:ℂ)+y*I)^(a-1/2)
  have hfun : (fun x : ℝ => exp (z*((x:ℂ)+c*I) - ((x:ℂ)+c*I)^2/2) * ((x:ℂ)+c*I)^(a-1/2)) =
      fun x => exp (I*π*(a/2-1/4)) * G (-x) := by
    funext x
    have hs : 0 < ((c:ℂ) + ((-x:ℝ):ℂ)*I).re := by simp [hc]
    have ht : (x:ℂ)+c*I = I*((c:ℂ) + ((-x:ℝ):ℂ)*I) := by push_cast; ring_nf; rw [I_sq]; ring
    rw [ht, (pcfCt_I_mul_cpow hs _).1]
    simp only [G]
    rw [show exp (z*(I*((c:ℂ) + ((-x:ℝ):ℂ)*I)) - (I*((c:ℂ) + ((-x:ℝ):ℂ)*I))^2/2) =
      exp (-(-I*z)*((c:ℂ)+((-x:ℝ):ℂ)*I) + ((c:ℂ)+((-x:ℝ):ℂ)*I)^2/2) by
        congr 1; linear_combination (-((c:ℂ)+((-x:ℝ):ℂ)*I)^2/2) * I_sq,
      show exp (π/2*I*(a-1/2)) = exp (I*π*(a/2-1/4)) by congr 1; ring]
    ring
  have hG : Integrable G := pcfCt_vert_integrable (-I*z) _ hc
  have hV := pcfCt_vertical (-a) (-I*z) hc
  rw [show (-I*z)^2 = -z^2 by rw [mul_pow, neg_sq, I_sq]; ring] at hV
  simp only [neg_neg] at hV
  rw [hfun]
  refine ⟨hG.comp_neg.const_mul _, ?_⟩
  rw [integral_const_mul, integral_neg_eq_self (fun y => G y)]
  simp only [G]; rw [hV]

/-- The horizontal line below the axis, for DLMF 12.5.7. -/
theorem pcfCt_horizontal_lower (a z : ℂ) {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : ℝ => exp (z*((x:ℂ)-c*I) - ((x:ℂ)-c*I)^2/2) * ((x:ℂ)-c*I)^(a-1/2)) ∧
    ∫ x : ℝ, exp (z*((x:ℂ)-c*I) - ((x:ℂ)-c*I)^2/2) * ((x:ℂ)-c*I)^(a-1/2) =
      exp (-I*π*(a/2-1/4)) * ((Real.sqrt (2*π) : ℂ) * exp (z^2/4) * pcfU (-a) (I*z)) := by
  set G : ℝ → ℂ := fun y => exp (-(I*z)*((c:ℂ)+y*I) + ((c:ℂ)+y*I)^2/2) * ((c:ℂ)+y*I)^(a-1/2)
  have hfun : (fun x : ℝ => exp (z*((x:ℂ)-c*I) - ((x:ℂ)-c*I)^2/2) * ((x:ℂ)-c*I)^(a-1/2)) =
      fun x => exp (-I*π*(a/2-1/4)) * G x := by
    funext x
    have hs : 0 < ((c:ℂ) + (x:ℂ)*I).re := by simp [hc]
    have ht : (x:ℂ)-c*I = -I*((c:ℂ) + (x:ℂ)*I) := by ring_nf; rw [I_sq]; ring
    rw [ht, (pcfCt_I_mul_cpow hs _).2]
    simp only [G]
    rw [show exp (z*(-I*((c:ℂ) + (x:ℂ)*I)) - (-I*((c:ℂ) + (x:ℂ)*I))^2/2) =
      exp (-(I*z)*((c:ℂ)+(x:ℂ)*I) + ((c:ℂ)+(x:ℂ)*I)^2/2) by
        congr 1; linear_combination (-((c:ℂ)+(x:ℂ)*I)^2/2) * I_sq,
      show exp (-(π/2)*I*(a-1/2)) = exp (-I*π*(a/2-1/4)) by congr 1; ring]
    ring
  have hG : Integrable G := pcfCt_vert_integrable (I*z) _ hc
  have hV := pcfCt_vertical (-a) (I*z) hc
  rw [show (I*z)^2 = -z^2 by rw [mul_pow, I_sq]; ring] at hV
  simp only [neg_neg] at hV
  rw [hfun]
  refine ⟨hG.const_mul _, ?_⟩
  rw [integral_const_mul]
  simp only [G]; rw [hV]

/-- The Hankel-loop integrand in the logarithmic variable `w = log t`:
`F(w) = exp(z e^w - e^{2w}/2 + (a+1/2) w)`, entire in `w` and in `a`. -/
noncomputable def pcfCt_F (a z w : ℂ) : ℂ := exp (z * exp w - exp w ^ 2 / 2 + (a + 1/2) * w)

/-- The Laplace integrand `t^{a-1/2} e^{-t²/2-zt}` of DLMF 12.5.1. -/
noncomputable def pcfCt_g (a z : ℂ) (t : ℝ) : ℂ := (t:ℂ)^(a-1/2) * exp (-(t:ℂ)^2/2 - z*t)

/-- The circle part of the Hankel loop, as an integral of `F` over `log r + iθ`, `|θ| ≤ π`. -/
noncomputable def pcfCt_C (a z : ℂ) (r : ℝ) : ℂ :=
  ∫ θ in -π..π, I * pcfCt_F a z (Real.log r + θ*I)

/-- The jump `e^{-iπ(a-1/2)} - e^{iπ(a-1/2)}` of `t^{a-1/2}` across the negative axis. -/
noncomputable def pcfCt_kappa (a : ℂ) : ℂ := exp (-(a-1/2)*π*I) - exp ((a-1/2)*π*I)

/-- `F` is entire. -/
theorem pcfCt_F_differentiable (a z : ℂ) : Differentiable ℂ (pcfCt_F a z) := by
  unfold pcfCt_F; fun_prop

/-- `(t : ℂ)^w = exp (w log t)` for `t > 0`. -/
theorem pcfCt_ofReal_cpow {t : ℝ} (ht : 0 < t) (w : ℂ) : (t:ℂ)^w = exp (w * Real.log t) := by
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr ht.ne'), ← ofReal_log ht.le, mul_comm]

/-- `F` on the two edges `x ± iπ` of the logarithmic strip. -/
theorem pcfCt_F_edge (a z : ℂ) (x : ℝ) (s : ℝ) (hs : s = 1 ∨ s = -1) :
    pcfCt_F a z (x + (s*π:ℝ)*I) = -exp (s*(a-1/2)*π*I) * (Real.exp x * pcfCt_g a z (Real.exp x)) := by
  have he : exp (((s*π:ℝ):ℂ)*I) = -1 := by
    rcases hs with rfl | rfl
    · simp [exp_pi_mul_I]
    · push_cast; rw [show (-1*(π:ℂ))*I = -(π*I) by ring, Complex.exp_neg, exp_pi_mul_I]; norm_num
  unfold pcfCt_F pcfCt_g
  rw [pcfCt_ofReal_cpow (Real.exp_pos x), Real.log_exp, Complex.exp_add (x:ℂ), he, ofReal_exp]
  have h2 : (-(exp (x:ℂ)))^2 = exp (x:ℂ)^2 := by ring
  rw [mul_neg_one, h2]
  rw [show (exp (x:ℂ):ℂ) = exp (x:ℂ) from rfl]
  rw [show -exp (↑s*(a-1/2)*↑π*I) * (exp (x:ℂ) * (exp ((a-1/2)*x) * exp (-exp (x:ℂ)^2/2 - z*exp x))) =
      -exp (↑s*(a-1/2)*↑π*I) * exp (x + (a-1/2)*x + (-exp (x:ℂ)^2/2 - z*exp x)) by
    rw [Complex.exp_add, Complex.exp_add]; ring]
  rw [show -exp (↑s*(a-1/2)*↑π*I) = exp (↑s*(a-1/2)*↑π*I) * exp (((s*π:ℝ):ℂ)*I) by rw [he]; ring,
    ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- `pcfCt_g` is continuous on the open half-line. -/
theorem pcfCt_g_continuousOn (a z : ℂ) : ContinuousOn (pcfCt_g a z) (Ioi 0) := by
  intro t ht
  refine ContinuousAt.continuousWithinAt ?_
  unfold pcfCt_g
  refine ContinuousAt.mul ?_ (by fun_prop)
  exact (continuous_ofReal.continuousAt).cpow continuousAt_const
    (ofReal_mem_slitPlane.mpr ht)

/-- Cauchy's theorem on the logarithmic rectangle: the circle parts at two radii differ by
the jump across the cut. -/
theorem pcfCt_C_sub (a z : ℂ) {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : 0 < r₂) :
    pcfCt_C a z r₂ - pcfCt_C a z r₁ = pcfCt_kappa a * ∫ t in r₁..r₂, pcfCt_g a z t := by
  have hR := Complex.integral_boundary_rect_eq_zero_of_differentiableOn (pcfCt_F a z)
    ⟨Real.log r₁, -π⟩ ⟨Real.log r₂, π⟩ (pcfCt_F_differentiable a z).differentiableOn
  simp only at hR
  have ep : ∀ x : ℝ, pcfCt_F a z (x + π*I) =
      -exp ((a-1/2)*π*I) * (Real.exp x * pcfCt_g a z (Real.exp x)) := fun x => by
    have := pcfCt_F_edge a z x 1 (Or.inl rfl); simpa using this
  have em : ∀ x : ℝ, pcfCt_F a z (x + ((-π:ℝ):ℂ)*I) =
      -exp (-(a-1/2)*π*I) * (Real.exp x * pcfCt_g a z (Real.exp x)) := fun x => by
    have := pcfCt_F_edge a z x (-1) (Or.inr rfl); simpa using this
  have hsub : ∫ x in Real.log r₁..Real.log r₂, ((Real.exp x:ℂ) * pcfCt_g a z (Real.exp x)) =
      ∫ t in r₁..r₂, pcfCt_g a z t := by
    have := intervalIntegral.integral_deriv_smul_comp' (a := Real.log r₁) (b := Real.log r₂)
      (f := Real.exp) (f' := Real.exp) (g := pcfCt_g a z)
      (fun x _ => Real.hasDerivAt_exp x) Real.continuous_exp.continuousOn
      ((pcfCt_g_continuousOn a z).mono (by
        rintro _ ⟨x, _, rfl⟩; exact Real.exp_pos x))
    rw [Real.exp_log h₁, Real.exp_log h₂] at this
    rw [← this]
    simp only [Function.comp, Complex.real_smul]
  simp_rw [em, ep] at hR
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hsub] at hR
  unfold pcfCt_C pcfCt_kappa
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  simp only [smul_eq_mul] at hR
  linear_combination hR

/-- The Hankel loop of DLMF 12.5.5 (the body of `pcfNegativeLoop`) in terms of the jump and the
circle part. -/
theorem pcfCt_loop_eq (a z : ℂ) {r R : ℝ} (hr : 0 < r) (hR : 0 < R) :
    (∫ t : ℝ in r..R, exp (-z*t-t^2/2)*exp ((a-1/2)*(Real.log t-π*I))) +
      (∫ θ : ℝ in -π..π, let t := r*exp (I*θ); exp (z*t-t^2/2)*exp ((a-1/2)*(Real.log r+I*θ))*I*t) -
      (∫ t : ℝ in r..R, exp (-z*t-t^2/2)*exp ((a-1/2)*(Real.log t+π*I))) =
    pcfCt_kappa a * (∫ t in r..R, pcfCt_g a z t) + pcfCt_C a z r := by
  have hpos : ∀ t ∈ uIcc r R, 0 < t := fun t ht => by
    rcases le_total r R with h | h
    · rw [uIcc_of_le h] at ht; exact lt_of_lt_of_le hr ht.1
    · rw [uIcc_of_ge h] at ht; exact lt_of_lt_of_le hR ht.1
  have h1 : ∫ t : ℝ in r..R, exp (-z*t-t^2/2)*exp ((a-1/2)*(Real.log t-π*I)) =
      ∫ t : ℝ in r..R, exp (-(a-1/2)*π*I) * pcfCt_g a z t := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    simp only [pcfCt_g]
    rw [pcfCt_ofReal_cpow (hpos t ht), ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1; ring
  have h3 : ∫ t : ℝ in r..R, exp (-z*t-t^2/2)*exp ((a-1/2)*(Real.log t+π*I)) =
      ∫ t : ℝ in r..R, exp ((a-1/2)*π*I) * pcfCt_g a z t := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    simp only [pcfCt_g]
    rw [pcfCt_ofReal_cpow (hpos t ht), ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1; ring
  have h2 : (∫ θ : ℝ in -π..π, let t := r*exp (I*θ); exp (z*t-t^2/2)*exp ((a-1/2)*(Real.log r+I*θ))*I*t) =
      pcfCt_C a z r := by
    unfold pcfCt_C
    refine intervalIntegral.integral_congr fun θ _ => ?_
    have hexp : exp ((Real.log r:ℂ) + θ*I) = r*exp (I*θ) := by
      rw [Complex.exp_add, ← ofReal_exp, Real.exp_log hr, mul_comm (θ:ℂ) I]
    simp only [pcfCt_F, hexp]
    rw [show (r:ℂ)*exp (I*θ) = exp ((Real.log r:ℂ) + θ*I) from hexp.symm, ← Complex.exp_add]
    rw [show (I:ℂ) * exp (z * exp (↑(Real.log r) + ↑θ * I) - exp (↑(Real.log r) + ↑θ * I) ^ 2 / 2 +
        (a + 1 / 2) * (↑(Real.log r) + ↑θ * I)) = I * (exp (z * exp (↑(Real.log r) + ↑θ * I) -
        exp (↑(Real.log r) + ↑θ * I) ^ 2 / 2 + (a - 1 / 2) * (↑(Real.log r) + I * ↑θ)) *
        exp (↑(Real.log r) + ↑θ * I)) by
      rw [← Complex.exp_add]; congr 2; ring]
    ring
  rw [h1, h2, h3, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  unfold pcfCt_kappa; ring

/-- Growth of `F`. -/
theorem pcfCt_norm_F_le (a z w : ℂ) :
    ‖pcfCt_F a z w‖ ≤ Real.exp (‖z‖*‖exp w‖ + ‖exp w‖^2/2 + ((a+1/2)*w).re) := by
  unfold pcfCt_F
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  simp only [add_re, sub_re]
  have h1 : (z * exp w).re ≤ ‖z‖*‖exp w‖ := (re_le_norm _).trans (norm_mul _ _).le
  have h2 : -((exp w ^ 2 / 2).re) ≤ ‖exp w‖^2/2 := by
    rw [Complex.div_ofNat_re]
    have := neg_le_abs (exp w ^ 2).re
    have h' := abs_re_le_norm (exp w ^ 2)
    rw [norm_pow] at h'
    linarith
  linarith

/-- The circle part on the circle of radius `ρ`. -/
theorem pcfCt_norm_F_circle_le (a z : ℂ) {ρ : ℝ} (hρ : 0 < ρ) {θ : ℝ} (hθ : |θ| ≤ π) :
    ‖pcfCt_F a z (Real.log ρ + θ*I)‖ ≤
      Real.exp (‖z‖*ρ + ρ^2/2 + |a.im| * π) * ρ^(a.re + 1/2) := by
  refine (pcfCt_norm_F_le a z _).trans ?_
  have he : ‖exp ((Real.log ρ:ℂ) + θ*I)‖ = ρ := by
    rw [Complex.norm_exp]; simp [Real.exp_log hρ]
  rw [he, Real.rpow_def_of_pos hρ, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hre : ((a+1/2)*((Real.log ρ:ℂ) + θ*I)).re = (a.re+1/2)*Real.log ρ - a.im*θ := by
    simp
  rw [hre]
  have : -(a.im*θ) ≤ |a.im| * π := by
    calc -(a.im*θ) ≤ |a.im*θ| := neg_le_abs _
      _ = |a.im| * |θ| := abs_mul _ _
      _ ≤ |a.im| * π := by gcongr
  nlinarith

/-- The circle part tends to zero as the radius shrinks, for `re a > -1/2`. -/
theorem pcfCt_C_tendsto_zero {a : ℂ} (ha : -1/2 < a.re) (z : ℂ) :
    Tendsto (pcfCt_C a z) (𝓝[>] 0) (𝓝 0) := by
  set s : ℝ := a.re + 1/2
  have hs : 0 < s := by simp only [s]; linarith
  set M : ℝ := Real.exp (‖z‖ + 1/2 + |a.im| * π) * (2*π)
  have hlim : Tendsto (fun ρ : ℝ => M * ρ^s) (𝓝[>] 0) (𝓝 0) := by
    have := ((Real.continuousAt_rpow_const 0 s (Or.inr hs.le)).tendsto).const_mul M
    rw [Real.zero_rpow hs.ne', mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [Ioo_mem_nhdsGT one_pos] with ρ hρ
  obtain ⟨hρ0, hρ1⟩ := hρ
  unfold pcfCt_C
  have hb : ∀ θ ∈ uIoc (-π) π, ‖I * pcfCt_F a z (Real.log ρ + θ*I)‖ ≤
      Real.exp (‖z‖ + 1/2 + |a.im| * π) * ρ^s := by
    intro θ hθ
    rw [uIoc_of_le (by linarith [Real.pi_pos])] at hθ
    have hθ' : |θ| ≤ π := abs_le.mpr ⟨hθ.1.le, hθ.2⟩
    rw [norm_mul, norm_I, one_mul]
    refine (pcfCt_norm_F_circle_le a z hρ0 hθ').trans ?_
    gcongr
    · nlinarith [norm_nonneg z]
    · nlinarith
  refine (intervalIntegral.norm_integral_le_of_norm_le_const hb).trans (le_of_eq ?_)
  rw [show π - -π = 2*π by ring, abs_of_pos (by linarith [Real.pi_pos] : (0:ℝ) < 2*π)]
  simp only [M]; ring

/-- For `re a > -1/2` the loop collapses onto the two sides of the cut. -/
theorem pcfCt_loop_limit_of_re {a : ℂ} (ha : -1/2 < a.re) (z : ℂ) {r : ℝ} (hr : 0 < r) :
    pcfCt_kappa a * (∫ t in Ioi r, pcfCt_g a z t) + pcfCt_C a z r =
      pcfCt_kappa a * ∫ t in Ioi (0:ℝ), pcfCt_g a z t := by
  have hg0 : IntegrableOn (pcfCt_g a z) (Ioi 0) :=
    integrableOn_pcfIntegrand (c := a - 1/2) (by simp; linarith) z
  set J := ∫ t in Ioi (0:ℝ), pcfCt_g a z t with hJ
  set κ := pcfCt_kappa a
  have hEq : ∀ ρ ∈ Ioo (0:ℝ) r, κ * (∫ t in Ioi r, pcfCt_g a z t) + pcfCt_C a z r =
      κ * (J - ∫ t in (0:ℝ)..ρ, pcfCt_g a z t) + pcfCt_C a z ρ := by
    intro ρ hρ
    have h1 := pcfCt_C_sub a z hρ.1 hr
    have h2 := intervalIntegral.integral_interval_add_Ioi (hg0.mono_set (Ioi_subset_Ioi hρ.1.le))
      (hg0.mono_set (Ioi_subset_Ioi hr.le))
    have h3 := intervalIntegral.integral_interval_add_Ioi hg0
      (hg0.mono_set (Ioi_subset_Ioi hρ.1.le))
    rw [← hJ] at h3
    linear_combination h1 + κ * h2 + κ * h3
  have hint : IntegrableOn (pcfCt_g a z) (uIcc 0 r) := by
    rw [uIcc_of_le hr.le, integrableOn_Icc_iff_integrableOn_Ioc]
    exact hg0.mono_set Ioc_subset_Ioi_self
  have hprim : Tendsto (fun ρ => ∫ t in (0:ℝ)..ρ, pcfCt_g a z t) (𝓝[>] 0) (𝓝 0) := by
    have hc := (intervalIntegral.continuousOn_primitive_interval hint (0:ℝ) left_mem_uIcc).tendsto
    rw [intervalIntegral.integral_same] at hc
    refine hc.mono_left (nhdsWithin_le_of_mem ?_)
    rw [uIcc_of_le hr.le]; exact Icc_mem_nhdsGT hr
  have hT : Tendsto (fun ρ => κ * (J - ∫ t in (0:ℝ)..ρ, pcfCt_g a z t) + pcfCt_C a z ρ)
      (𝓝[>] 0) (𝓝 (κ * J)) := by
    have := ((tendsto_const_nhds (x := J)).sub hprim).const_mul κ |>.add (pcfCt_C_tendsto_zero ha z)
    simpa using this
  have hev : (fun _ : ℝ => κ * (∫ t in Ioi r, pcfCt_g a z t) + pcfCt_C a z r) =ᶠ[𝓝[>] 0]
      (fun ρ => κ * (J - ∫ t in (0:ℝ)..ρ, pcfCt_g a z t) + pcfCt_C a z ρ) := by
    filter_upwards [Ioo_mem_nhdsGT hr] with ρ hρ using hEq ρ hρ
  exact tendsto_nhds_unique (tendsto_const_nhds.congr' hev) hT

/-- Gaussian majorant of `pcfCt_g` on `[r, ∞)`, uniform for `‖a - 1/2‖ ≤ Q`, `‖z‖ ≤ Z`. -/
theorem pcfCt_g_le {a z : ℂ} {Q Z r : ℝ} (hr : 0 < r) (hQ : ‖a-1/2‖ ≤ Q) (hZ : ‖z‖ ≤ Z) {t : ℝ}
    (ht : r ≤ t) :
    ‖pcfCt_g a z t‖ ≤ Real.exp (Q*|Real.log r| + (Q+Z)^2) * Real.exp (-(1/4) * t^2) := by
  have ht0 : 0 < t := lt_of_lt_of_le hr ht
  unfold pcfCt_g
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht0, Complex.norm_exp, Real.rpow_def_of_pos ht0,
    ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hre : (-(t:ℂ)^2/2 - z*t).re = -t^2/2 - z.re*t := by
    simp [sq]
  rw [hre]
  have hQ0 : 0 ≤ Q := (norm_nonneg _).trans hQ
  have hl1 : Real.log r ≤ Real.log t := Real.log_le_log hr ht
  have hl2 : Real.log t ≤ t := (Real.log_le_sub_one_of_pos ht0).trans (by linarith)
  have hab : |Real.log t| ≤ |Real.log r| + t := by
    rw [abs_le]; constructor
    · linarith [neg_abs_le (Real.log r)]
    · linarith [abs_nonneg (Real.log r)]
  have h1 : Real.log t * (a - 1/2).re ≤ Q * (|Real.log r| + t) := by
    calc Real.log t * (a - 1/2).re ≤ |Real.log t * (a - 1/2).re| := le_abs_self _
      _ = |Real.log t| * |(a - 1/2).re| := abs_mul _ _
      _ ≤ (|Real.log r| + t) * Q := by gcongr; exact (abs_re_le_norm _).trans hQ
      _ = _ := by ring
  have h2 : -(z.re*t) ≤ Z*t := by
    have := neg_abs_le z.re
    have := (abs_re_le_norm z).trans hZ
    nlinarith
  nlinarith [sq_nonneg (Q + Z - t/2)]

/-- `pcfCt_g` is integrable on `(r, ∞)` for every parameter. -/
theorem pcfCt_g_integrableOn (a z : ℂ) {r : ℝ} (hr : 0 < r) : IntegrableOn (pcfCt_g a z) (Ioi r) := by
  refine Integrable.mono' (((integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/4)).const_mul
    (Real.exp (‖a-1/2‖*|Real.log r| + (‖a-1/2‖+‖z‖)^2))).integrableOn)
    (((pcfCt_g_continuousOn a z).mono (Ioi_subset_Ioi hr.le)).aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact pcfCt_g_le hr le_rfl le_rfl (le_of_lt ht)

/-- The tail `∫_r^∞ t^{a-1/2} e^{-t²/2-zt} dt` is entire in `a`. -/
theorem pcfCt_tail_differentiable (z : ℂ) {r : ℝ} (hr : 0 < r) :
    Differentiable ℂ (fun a => ∫ t in Ioi r, pcfCt_g a z t) := by
  refine differentiableOn_univ.mp (differentiableOn_integral_of_locally_dominated isOpen_univ
    (fun a _ => ((pcfCt_g_continuousOn a z).mono (Ioi_subset_Ioi hr.le)).aestronglyMeasurable
      measurableSet_Ioi) ?_ ?_)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht a _
    have ht0 : (t:ℂ) ≠ 0 := ofReal_ne_zero.mpr (lt_trans hr ht).ne'
    unfold pcfCt_g
    exact (((differentiableAt_id.sub_const _).const_cpow (Or.inl ht0)).mul
      (differentiableAt_const _)).differentiableWithinAt
  · intro a0 _
    refine ⟨ball a0 1, ball_mem_nhds _ one_pos,
      fun t => Real.exp ((‖a0-1/2‖+1)*|Real.log r| + ((‖a0-1/2‖+1)+‖z‖)^2) *
        Real.exp (-(1/4) * t^2),
      ((integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/4)).const_mul _).integrableOn, ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht a ha
    refine pcfCt_g_le hr ?_ le_rfl (le_of_lt ht)
    rw [mem_ball, dist_eq_norm] at ha
    calc ‖a - 1/2‖ = ‖(a0 - 1/2) + (a - a0)‖ := by ring_nf
      _ ≤ ‖a0 - 1/2‖ + ‖a - a0‖ := norm_add_le _ _
      _ ≤ ‖a0-1/2‖+1 := by linarith

/-- The circle part is entire in `a`. -/
theorem pcfCt_C_differentiable (z : ℂ) {r : ℝ} (hr : 0 < r) :
    Differentiable ℂ (fun a => pcfCt_C a z r) := by
  have hcont : ∀ a : ℂ, Continuous (fun θ : ℝ => I * pcfCt_F a z (Real.log r + θ*I)) := fun a =>
    continuous_const.mul ((pcfCt_F_differentiable a z).continuous.comp (by fun_prop))
  unfold pcfCt_C
  simp_rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -π ≤ π)]
  refine differentiableOn_univ.mp (differentiableOn_integral_of_locally_dominated isOpen_univ
    (fun a _ => (hcont a).aestronglyMeasurable) ?_ ?_)
  · refine Eventually.of_forall fun θ a _ => ?_
    unfold pcfCt_F
    exact (by fun_prop : DifferentiableAt ℂ (fun a : ℂ => I * exp (z * exp ((Real.log r:ℂ) + θ*I) -
      exp ((Real.log r:ℂ) + θ*I) ^ 2 / 2 + (a + 1/2) * ((Real.log r:ℂ) + θ*I))) a).differentiableWithinAt
  · intro a0 _
    refine ⟨ball a0 1, ball_mem_nhds _ one_pos,
      fun _ => Real.exp (‖z‖*r + r^2/2 + (‖a0 + 1/2‖ + 1)*(|Real.log r| + π)),
      integrable_const _, ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ a ha
    rw [norm_mul, norm_I, one_mul]
    refine (pcfCt_norm_F_le a z _).trans (Real.exp_le_exp.mpr ?_)
    have he : ‖exp ((Real.log r:ℂ) + θ*I)‖ = r := by
      rw [Complex.norm_exp]; simp [Real.exp_log hr]
    rw [he]
    have hw : ‖(Real.log r:ℂ) + θ*I‖ ≤ |Real.log r| + π := by
      refine (norm_add_le _ _).trans ?_
      have : |θ| ≤ π := abs_le.mpr ⟨hθ.1.le, hθ.2⟩
      simp only [norm_real, Real.norm_eq_abs, norm_mul, norm_I, mul_one]
      linarith
    have ha' : ‖a + 1/2‖ ≤ ‖a0 + 1/2‖ + 1 := by
      rw [mem_ball, dist_eq_norm] at ha
      calc ‖a + 1/2‖ = ‖(a0 + 1/2) + (a - a0)‖ := by ring_nf
        _ ≤ ‖a0 + 1/2‖ + ‖a - a0‖ := norm_add_le _ _
        _ ≤ _ := by linarith
    have hre : ((a + 1/2) * ((Real.log r:ℂ) + θ*I)).re ≤ (‖a0 + 1/2‖ + 1)*(|Real.log r| + π) :=
      (re_le_norm _).trans (by
        rw [norm_mul]; exact mul_le_mul ha' hw (norm_nonneg _) (by positivity))
    linarith

/-- The jump times the reflection pair: `κ(a) Γ(1/2+a) Γ(1/2-a) = 2πi` when both Gammas are
finite and nonzero. -/
theorem pcfCt_kappa_Gamma {a : ℂ} (h1 : Gamma (1/2+a) ≠ 0) (h2 : Gamma (1/2-a) ≠ 0) :
    pcfCt_kappa a * Gamma (1/2+a) * Gamma (1/2-a) = 2*π*I := by
  have hr := Complex.Gamma_mul_Gamma_one_sub (1/2+a)
  rw [show (1:ℂ) - (1/2+a) = 1/2-a by ring] at hr
  have hs : Complex.sin (π*(1/2+a)) = -(pcfCt_kappa a * I / 2) := by
    rw [Complex.sin, pcfCt_kappa]
    have e1 : exp (-(π*(1/2+a))*I) = -exp (-(a-1/2)*π*I) := by
      rw [show -(π*(1/2+a))*I = -(a-1/2)*π*I + -(π*I) by ring, Complex.exp_add, Complex.exp_neg,
        exp_pi_mul_I]; ring
    have e2 : exp ((π*(1/2+a))*I) = -exp ((a-1/2)*π*I) := by
      rw [show (π*(1/2+a))*I = (a-1/2)*π*I + π*I by ring, Complex.exp_add, exp_pi_mul_I]; ring
    rw [show (↑π * (1 / 2 + a)) = (π*(1/2+a) : ℂ) from rfl, e1, e2]; ring
  have hne : Complex.sin (π*(1/2+a)) ≠ 0 := by
    intro h0; rw [h0, div_zero] at hr; exact mul_ne_zero h1 h2 hr
  rw [hs] at hr hne
  have hk : pcfCt_kappa a ≠ 0 := fun h => hne (by rw [h]; ring)
  rw [mul_assoc, hr, mul_div_assoc', div_eq_iff hne]
  linear_combination (pcfCt_kappa a * π) * I_sq

/-- The completed Hankel loop: `κ(a) ∫_r^∞ g + C(r) = 2πi e^{z²/4} U(a,z) / Γ(1/2-a)` for all
`a`, `z` and `r > 0`. -/
theorem pcfCt_loop_value (a z : ℂ) {r : ℝ} (hr : 0 < r) :
    pcfCt_kappa a * (∫ t in Ioi r, pcfCt_g a z t) + pcfCt_C a z r =
      2*π*I * exp (z^2/4) * pcfU a z * (Gamma (1/2-a))⁻¹ := by
  have hf : Differentiable ℂ (fun a => pcfCt_kappa a * (∫ t in Ioi r, pcfCt_g a z t) +
      pcfCt_C a z r) :=
    ((by unfold pcfCt_kappa; fun_prop : Differentiable ℂ pcfCt_kappa).mul
      (pcfCt_tail_differentiable z hr)).add (pcfCt_C_differentiable z hr)
  have hg : Differentiable ℂ (fun a => 2*π*I * exp (z^2/4) * pcfU a z * (Gamma (1/2-a))⁻¹) :=
    ((pcfU_entire_order z).const_mul _).mul (differentiable_one_div_Gamma.comp (by fun_prop))
  have hopen : IsOpen {b : ℂ | -1/2 < b.re ∧ b.re < 1/2} :=
    (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)
  have heq : (fun a => pcfCt_kappa a * (∫ t in Ioi r, pcfCt_g a z t) + pcfCt_C a z r) =ᶠ[𝓝 (0:ℂ)]
      (fun a => 2*π*I * exp (z^2/4) * pcfU a z * (Gamma (1/2-a))⁻¹) := by
    filter_upwards [hopen.mem_nhds (show (0:ℂ) ∈ {b : ℂ | -1/2 < b.re ∧ b.re < 1/2} by
      simp only [mem_ofPred_eq, zero_re]; norm_num)] with b hb
    obtain ⟨hb1, hb2⟩ := hb
    rw [pcfCt_loop_limit_of_re hb1 z hr]
    have h1 : Gamma (1/2+b) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
    have h2 : Gamma (1/2-b) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
    have hU := pcfU_eq_integral hb1 z
    have hk := pcfCt_kappa_Gamma h1 h2
    have he : exp (z^2/4) * exp (-z^2/4) = 1 := by rw [← Complex.exp_add]; ring_nf; simp
    have hJ : ∫ t in Ioi (0:ℝ), pcfCt_g b z t =
        ∫ t in Ioi (0:ℝ), (t:ℂ)^(b-1/2) * exp (-(t:ℂ)^2/2 - z*t) := rfl
    rw [hJ, hU]
    generalize (∫ t in Ioi (0:ℝ), (t:ℂ)^(b-1/2) * exp (-(t:ℂ)^2/2 - z*t)) = J
    generalize Gamma (1/2+b) = G1 at h1 hk ⊢
    generalize Gamma (1/2-b) = G2 at h2 hk ⊢
    have he' : exp (z^2/4) * exp (-(z^2/4)) = 1 := by rw [← Complex.exp_add]; ring_nf; simp
    rw [← hk]
    field_simp
    linear_combination (-(pcfCt_kappa b * J)) * he'
  have hf' : AnalyticOnNhd ℂ (fun a => pcfCt_kappa a * (∫ t in Ioi r, pcfCt_g a z t) +
      pcfCt_C a z r) univ := fun x _ => hf.analyticAt x
  exact hf'.eqOn_of_preconnected_of_eventuallyEq (fun x _ => hg.analyticAt x) isPreconnected_univ
    (mem_univ 0) heq (mem_univ a)

/-- The kernel `e^{μw} e^{iσe^w}/(x² + e^{2w})` of the Stieltjes–Fourier integral in `w = log t`. -/
noncomputable def pcfCt_Phi (μ : ℂ) (x σ : ℝ) (w : ℂ) : ℂ :=
  exp (μ*w) * exp (I*σ*exp w) / ((x:ℂ)^2 + exp w ^ 2)

/-- Growth of `pcfCt_Phi` on the strip `0 ≤ Im w ≤ π`. -/
theorem pcfCt_norm_Phi_le (μ : ℂ) (x : ℝ) {σ : ℝ} (hσ : 0 ≤ σ) {w : ℂ} (h0 : 0 ≤ w.im)
    (hπ : w.im ≤ π) (hd : x^2 ≠ Real.exp (2*w.re)) :
    ‖pcfCt_Phi μ x σ w‖ ≤ Real.exp (μ.re*w.re + |μ.im| * π) / |x^2 - Real.exp (2*w.re)| := by
  unfold pcfCt_Phi
  rw [norm_div, norm_mul, Complex.norm_exp, Complex.norm_exp]
  have h1 : (μ*w).re ≤ μ.re*w.re + |μ.im| * π := by
    simp only [mul_re]
    have : -(μ.im*w.im) ≤ |μ.im| * π := by
      calc -(μ.im*w.im) ≤ |μ.im*w.im| := neg_le_abs _
        _ = |μ.im| * |w.im| := abs_mul _ _
        _ ≤ |μ.im| * π := by gcongr; rw [abs_of_nonneg h0]; exact hπ
    linarith
  have h2 : (I*σ*exp w).re ≤ 0 := by
    have : (I*σ*exp w).re = -(σ * (Real.exp w.re * Real.sin w.im)) := by
      simp [Complex.exp_re, Complex.exp_im, mul_re, mul_im]
    rw [this]
    have := Real.sin_nonneg_of_nonneg_of_le_pi h0 hπ
    have := Real.exp_pos w.re
    have : 0 ≤ σ * (Real.exp w.re * Real.sin w.im) := by positivity
    linarith
  have h3 : |x^2 - Real.exp (2*w.re)| ≤ ‖(x:ℂ)^2 + exp w ^ 2‖ := by
    have hn : ‖exp w ^ 2‖ = Real.exp (2*w.re) := by
      rw [norm_pow, Complex.norm_exp, ← Real.exp_nat_mul]; push_cast; ring_nf
    have hx : ‖((x:ℂ))^2‖ = x^2 := by rw [norm_pow, norm_real, Real.norm_eq_abs, sq_abs]
    have := abs_norm_sub_norm_le ((x:ℂ)^2) (-(exp w ^ 2))
    rw [norm_neg, sub_neg_eq_add] at this
    rw [← hn, ← hx]; exact this
  have h : 0 < |x^2 - Real.exp (2*w.re)| := abs_pos.mpr (sub_ne_zero.mpr hd)
  calc Real.exp (μ*w).re * Real.exp (I*σ*exp w).re / ‖(x:ℂ)^2 + exp w ^ 2‖
        ≤ Real.exp (μ.re*w.re + |μ.im| * π) * 1 / |x^2 - Real.exp (2*w.re)| := by
          gcongr
          exact Real.exp_le_one_iff.mpr h2
    _ = _ := by ring

/-- The Stieltjes–Fourier integrand `t^{μ-1} e^{iσt}/(x² + t²)`. -/
noncomputable def pcfCt_gs (μ : ℂ) (x σ : ℝ) (t : ℝ) : ℂ :=
  (t:ℂ)^(μ-1) * exp (I*σ*t) / ((x:ℂ)^2 + (t:ℂ)^2)

/-- `pcfCt_Phi` on the real axis is `e^u g(e^u)` with `g = pcfCt_gs`. -/
theorem pcfCt_Phi_real (μ : ℂ) (x σ u : ℝ) :
    pcfCt_Phi μ x σ u = Real.exp u • pcfCt_gs μ x σ (Real.exp u) := by
  unfold pcfCt_Phi pcfCt_gs
  rw [pcfCt_ofReal_cpow (Real.exp_pos u), Real.log_exp, Complex.real_smul, ofReal_exp]
  rw [show exp (μ*u) = exp (u:ℂ) * exp ((μ-1)*u) by rw [← Complex.exp_add]; ring_nf]
  ring

/-- `pcfCt_Phi` on the line `Im w = π`. -/
theorem pcfCt_Phi_shift (μ : ℂ) (x σ u : ℝ) :
    pcfCt_Phi μ x σ (u + π*I) = exp (μ*π*I) * pcfCt_Phi μ x (-σ) u := by
  unfold pcfCt_Phi
  have he : exp ((u:ℂ) + π*I) = -exp (u:ℂ) := by rw [Complex.exp_add, exp_pi_mul_I]; ring
  rw [he, show exp (μ*((u:ℂ) + π*I)) = exp (μ*π*I) * exp (μ*u) by rw [← Complex.exp_add]; ring_nf]
  push_cast
  rw [show I*σ*(-exp (u:ℂ)) = I*(-σ)*exp (u:ℂ) by ring, neg_sq]
  ring

/-- The modulus of `pcfCt_Phi` on the real axis. -/
theorem pcfCt_norm_Phi_real (μ : ℂ) (x σ u : ℝ) :
    ‖pcfCt_Phi μ x σ u‖ = Real.exp (μ.re*u) / (x^2 + Real.exp u^2) := by
  unfold pcfCt_Phi
  have hd : (x:ℂ)^2 + exp (u:ℂ)^2 = ((x^2 + Real.exp u^2 : ℝ) : ℂ) := by push_cast; rfl
  rw [hd, norm_div, norm_mul, Complex.norm_exp, Complex.norm_exp, norm_real,
    Real.norm_of_nonneg (by positivity)]
  congr 1
  have h1 : (μ*u).re = μ.re*u := by simp
  have h2 : (I*σ*exp (u:ℂ)).re = 0 := by
    rw [← ofReal_exp]; simp
  rw [h1, h2, Real.exp_zero, mul_one]

/-- Exponential majorant of `e^{mu}/(x² + e^{2u})`. -/
theorem pcfCt_line_bound (m : ℝ) {x : ℝ} (hx : 0 < x) (u : ℝ) :
    Real.exp (m*u) / (x^2 + Real.exp u^2) ≤ (1 + 1/x^2) * Real.exp (-(min m (2-m) * |u|)) := by
  have hx2 : 0 < x^2 := by positivity
  have he := Real.exp_pos u
  rcases le_total 0 u with hu | hu
  · rw [abs_of_nonneg hu]
    have h1 : Real.exp (m*u) / (x^2 + Real.exp u^2) ≤ Real.exp (m*u) / Real.exp u^2 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    have h2 : Real.exp (m*u) / Real.exp u^2 = Real.exp (-((2-m)*u)) := by
      rw [← Real.exp_nat_mul, div_eq_iff (by positivity), ← Real.exp_add]; push_cast; ring_nf
    have h3 : Real.exp (-((2-m)*u)) ≤ Real.exp (-(min m (2-m) * u)) := by
      apply Real.exp_le_exp.mpr; have := min_le_right m (2-m); nlinarith
    have h4 : Real.exp (-(min m (2-m) * u)) ≤ (1 + 1/x^2) * Real.exp (-(min m (2-m) * u)) := by
      have : 0 ≤ 1/x^2 := by positivity
      nlinarith [Real.exp_pos (-(min m (2-m) * u))]
    linarith
  · rw [abs_of_nonpos hu]
    have h1 : Real.exp (m*u) / (x^2 + Real.exp u^2) ≤ Real.exp (m*u) / x^2 :=
      div_le_div_of_nonneg_left (by positivity) hx2 (by nlinarith)
    have h3 : Real.exp (m*u) ≤ Real.exp (-(min m (2-m) * -u)) := by
      apply Real.exp_le_exp.mpr; have := min_le_left m (2-m); nlinarith
    have h4 : Real.exp (m*u) / x^2 ≤ (1/x^2) * Real.exp (-(min m (2-m) * -u)) := by
      rw [div_eq_mul_inv, mul_comm, one_div]; gcongr
    have : 0 ≤ Real.exp (-(min m (2-m) * -u)) := (Real.exp_pos _).le
    nlinarith

/-- `pcfCt_Phi` is integrable on the real axis for `0 < re μ < 2`. -/
theorem pcfCt_Phi_real_integrable {μ : ℂ} (hm0 : 0 < μ.re) (hm2 : μ.re < 2) {x : ℝ} (hx : 0 < x)
    (σ : ℝ) : Integrable (fun u : ℝ => pcfCt_Phi μ x σ u) := by
  have hc : Continuous (fun u : ℝ => pcfCt_Phi μ x σ u) := by
    unfold pcfCt_Phi
    refine Continuous.div (by fun_prop) (by fun_prop) fun u => ?_
    have : (x:ℂ)^2 + exp (u:ℂ)^2 = ((x^2 + Real.exp u^2 : ℝ) : ℂ) := by push_cast; rfl
    rw [this]; exact ofReal_ne_zero.mpr (by positivity)
  refine ((TauCeti.integrable_exp_neg_mul_abs (a := min μ.re (2 - μ.re)) (lt_min hm0 (by linarith))).const_mul
    (1 + 1/x^2)).mono' hc.aestronglyMeasurable (Eventually.of_forall fun u => ?_)
  rw [pcfCt_norm_Phi_real]; exact pcfCt_line_bound μ.re hx u

/-- The real majorant of the kernel on vertical cross-sections tends to zero at both ends. -/
theorem pcfCt_cross_bound_tendsto {m : ℝ} (hm0 : 0 < m) (hm2 : m < 2) {x : ℝ} (hx : 0 < x) (c : ℝ) :
    Tendsto (fun u : ℝ => Real.exp (m*u + c) / |x^2 - Real.exp (2*u)|) atBot (𝓝 0) ∧
    Tendsto (fun u : ℝ => Real.exp (m*u + c) / |x^2 - Real.exp (2*u)|) atTop (𝓝 0) := by
  have hx2 : x^2 ≠ 0 := by positivity
  constructor
  · have hn : Tendsto (fun u : ℝ => Real.exp (m*u + c)) atBot (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_atBot_add_const_right _ c
        (tendsto_id.const_mul_atBot hm0))
    have hd : Tendsto (fun u : ℝ => |x^2 - Real.exp (2*u)|) atBot (𝓝 (|x^2 - 0|)) :=
      ((tendsto_const_nhds.sub (Real.tendsto_exp_atBot.comp
        (tendsto_id.const_mul_atBot two_pos)))).abs
    have h := hn.div hd (by rw [sub_zero, abs_of_pos (by positivity)]; exact hx2)
    rw [zero_div] at h; exact h
  · have heq : (fun u : ℝ => Real.exp (m*u + c) / |x^2 - Real.exp (2*u)|) =
        fun u => Real.exp ((m-2)*u + c) / |x^2 * Real.exp (-(2*u)) - 1| := by
      funext u
      have h1 : x^2 - Real.exp (2*u) = Real.exp (2*u) * (x^2 * Real.exp (-(2*u)) - 1) := by
        rw [mul_sub, ← mul_assoc, mul_comm (Real.exp (2*u)), mul_assoc, ← Real.exp_add]; simp
      rw [h1, abs_mul, abs_of_pos (Real.exp_pos _), ← div_div,
        show (m-2)*u + c = (m*u + c) - 2*u by ring, Real.exp_sub]
    rw [heq]
    have hn : Tendsto (fun u : ℝ => Real.exp ((m-2)*u + c)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_atBot_add_const_right _ c
        (tendsto_id.const_mul_atTop_of_neg (by linarith)))
    have hd : Tendsto (fun u : ℝ => |x^2 * Real.exp (-(2*u)) - 1|) atTop (𝓝 (|x^2 * 0 - 1|)) :=
      (((Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
        (tendsto_id.const_mul_atTop (two_pos : (0:ℝ) < 2)))).const_mul
        (x^2)).sub tendsto_const_nhds).abs
    have h := hn.div hd (by norm_num)
    rw [zero_div] at h; exact h

/-- The residue identity behind the kernel of DLMF 12.12.3: shifting the line `Im w = 0` to
`Im w = π` across the pole `w = log x + iπ/2` of `pcfCt_Phi`. -/
theorem pcfCt_kernel_shift {μ : ℂ} (hm0 : 0 < μ.re) (hm2 : μ.re < 2) {x : ℝ} (hx : 0 < x)
    {σ : ℝ} (hσ : 0 ≤ σ) :
    exp (μ*π*I) * (∫ u : ℝ, pcfCt_Phi μ x (-σ) u) - ∫ u : ℝ, pcfCt_Phi μ x σ u =
      2*π * (I * exp (μ*((Real.log x:ℂ) + π/2*I)) * exp (-(x*σ:ℂ)) / (2*(x:ℂ)^2)) := by
  set p : ℂ := (Real.log x:ℂ) + π/2*I with hp
  set q : ℂ := -I*p with hq
  have hep : exp p = x*I := by
    rw [hp, Complex.exp_add, ← ofReal_exp, Real.exp_log hx, exp_pi_div_two_mul_I]
  have hIq : I*q = p := by rw [hq, ← mul_assoc, mul_neg, I_mul_I]; ring
  have hqre : q.re = π/2 := by simp [hq, hp]
  have hpim : p.im = π/2 := by simp [hp]
  have hpre : p.re = Real.log x := by simp [hp]
  set D : ℂ → ℂ := dslope exp p with hD
  set φ : ℂ → ℂ := fun s => exp (μ*(I*s)) * exp (I*σ*exp (I*s)) / (I * D (I*s) * (exp (I*s) + I*x))
    with hφ
  have hx0 : (x:ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have key : ∀ s : ℂ, I*s ≠ p → φ s / (s - q) = pcfCt_Phi μ x σ (I*s) := by
    intro s hs
    have hsq : s - q ≠ 0 := fun h => hs (by rw [← hIq, sub_eq_zero.mp h])
    have hIs : I*s - p = I*(s - q) := by rw [mul_sub, hIq]
    simp only [hφ, hD, pcfCt_Phi]
    rw [dslope_of_ne _ hs, slope_def_field, hep, hIs, div_div]
    congr 1
    field_simp
    linear_combination (-(x:ℂ)^2) * I_sq
  have hDd : Differentiable ℂ D := fun z =>
    (((differentiableOn_dslope (Filter.univ_mem)).mpr differentiable_exp.differentiableOn) z
      (mem_univ z)).differentiableAt Filter.univ_mem
  -- nonvanishing of the denominator on the strip
  have hden : ∀ s : ℂ, 0 ≤ s.re → s.re ≤ π → I * D (I*s) * (exp (I*s) + I*x) ≠ 0 := by
    intro s h0 hπ
    have hIsim : (I*s).im = s.re := by simp
    refine mul_ne_zero (mul_ne_zero I_ne_zero ?_) ?_
    · by_cases hs : I*s = p
      · rw [hs, hD, dslope_same, Complex.deriv_exp]; exact Complex.exp_ne_zero _
      · rw [hD, dslope_of_ne _ hs, slope_def_field]
        refine div_ne_zero (sub_ne_zero.mpr fun he => ?_) (sub_ne_zero.mpr hs)
        obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp he
        have him := congrArg Complex.im hn
        rw [hIsim] at him
        simp [hpim] at him
        have hπ0 := Real.pi_pos
        have hn0 : n = 0 := by
          have h1 : (n:ℝ) < 1 := by nlinarith
          have h2 : (-1:ℝ) < n := by nlinarith
          have : n < 1 := by exact_mod_cast h1
          have : -1 < n := by exact_mod_cast h2
          omega
        apply hs; rw [hn, hn0]; simp
    · intro h0'
      have he : exp (I*s) = -(I*x) := by linear_combination h0'
      have him := congrArg Complex.im he
      rw [Complex.exp_im, hIsim] at him
      simp at him
      have := Real.sin_nonneg_of_nonneg_of_le_pi h0 hπ
      have := Real.exp_pos (-s.im)
      nlinarith
  have hφd : DifferentiableOn ℂ φ (re ⁻¹' Icc 0 π) := by
    intro s hs
    refine DifferentiableAt.differentiableWithinAt ?_
    simp only [hφ]
    refine DifferentiableAt.div (by fun_prop) ?_ (hden s hs.1 hs.2)
    exact ((differentiableAt_const _).mul ((hDd _).comp s (by fun_prop))).mul (by fun_prop)
  -- value at the pole
  have hval : φ q = I * exp (μ*p) * exp (-(x*σ:ℂ)) / (2*(x:ℂ)^2) := by
    simp only [hφ, hIq, hD, dslope_same, Complex.deriv_exp, hep]
    rw [show I*σ*(x*I) = -(x*σ:ℂ) * (-(I*I)) by ring, I_mul_I]
    field_simp
    ring_nf
    rw [show I^4 = (I^2)^2 by ring, I_sq]; norm_num
  -- the two boundary lines
  have hl0 : ∀ y : ℝ, φ (((0:ℝ):ℂ) + y*I) / (((0:ℝ):ℂ) + y*I - q) =
      pcfCt_Phi μ x σ ((-y:ℝ):ℂ) := by
    intro y
    have hw : I*(((0:ℝ):ℂ) + y*I) = ((-y:ℝ):ℂ) := by push_cast; ring_nf; rw [I_sq]; ring
    rw [key _ (by rw [hw]; intro h; have := congrArg Complex.im h; simp [hpim] at this; linarith [Real.pi_pos]),
      hw]
  have hlπ : ∀ y : ℝ, φ ((π:ℂ) + y*I) / ((π:ℂ) + y*I - q) =
      exp (μ*π*I) * pcfCt_Phi μ x (-σ) ((-y:ℝ):ℂ) := by
    intro y
    have hw : I*((π:ℂ) + y*I) = ((-y:ℝ):ℂ) + π*I := by push_cast; ring_nf; rw [I_sq]; ring
    rw [key _ (by
      rw [hw]; intro h; have := congrArg Complex.im h; simp [hpim] at this; linarith [Real.pi_pos]),
      hw, pcfCt_Phi_shift]
  have hint := pcfCt_Phi_real_integrable hm0 hm2 hx σ
  have hint' := pcfCt_Phi_real_integrable hm0 hm2 hx (-σ)
  have hi₁ : Integrable fun y : ℝ => φ (((0:ℝ):ℂ) + y*I) / (((0:ℝ):ℂ) + y*I - q) := by
    rw [funext hl0]; exact hint.comp_neg
  have hi₂ : Integrable fun y : ℝ => φ ((π:ℂ) + y*I) / ((π:ℂ) + y*I - q) := by
    rw [funext hlπ]; exact hint'.comp_neg.const_mul _
  -- cross-sections
  have hx2 : ∀ T : ℝ, T ≠ -Real.log x → x^2 ≠ Real.exp (2*(-T)) := by
    intro T hT h
    rw [show x^2 = Real.exp (2*Real.log x) by
      rw [show 2*Real.log x = Real.log x + Real.log x by ring, Real.exp_add, Real.exp_log hx]; ring] at h
    exact hT (by linarith [Real.exp_injective h])
  have hcross : ∀ T : ℝ, T ≠ -Real.log x →
      ‖∫ x' in (0:ℝ)..π, φ (x' + T*I) / (x' + T*I - q)‖ ≤
        Real.exp (μ.re*(-T) + |μ.im| * π) / |x^2 - Real.exp (2*(-T))| * |π - 0| := by
    intro T hT
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun x' hx' => ?_
    rw [uIoc_of_le Real.pi_pos.le] at hx'
    have hw : I*((x':ℂ) + T*I) = ((-T:ℝ):ℂ) + x'*I := by push_cast; ring_nf; rw [I_sq]; ring
    have hne : I*((x':ℂ) + T*I) ≠ p := by
      rw [hw]; intro h; have := congrArg Complex.re h; simp [hpre] at this; exact hT (by linarith)
    rw [key _ hne, hw]
    have := pcfCt_norm_Phi_le μ x hσ (w := ((-T:ℝ):ℂ) + x'*I) (by simp; exact hx'.1.le)
      (by simp; exact hx'.2) (by simpa using hx2 T hT)
    simpa using this
  obtain ⟨hB1, hB2⟩ := pcfCt_cross_bound_tendsto hm0 hm2 hx (|μ.im| * π)
  have htop : Tendsto (fun T : ℝ => ∫ x' in (0:ℝ)..π, φ (x' + T*I) / (x' + T*I - q)) atTop (𝓝 0) := by
    have hl := (hB1.comp tendsto_neg_atTop_atBot).mul_const |π - 0|
    rw [zero_mul] at hl
    refine squeeze_zero_norm' ?_ hl
    filter_upwards [eventually_ne_atTop (-Real.log x)] with T hT using hcross T hT
  have hbot : Tendsto (fun T : ℝ => ∫ x' in (0:ℝ)..π, φ (x' + T*I) / (x' + T*I - q)) atBot (𝓝 0) := by
    have hl := (hB2.comp tendsto_neg_atBot_atTop).mul_const |π - 0|
    rw [zero_mul] at hl
    refine squeeze_zero_norm' ?_ hl
    filter_upwards [eventually_ne_atBot (-Real.log x)] with T hT using hcross T hT
  have hB := Complex.barnesRes_vertical_shift (φ := φ) (c₁ := 0) (c₂ := π) (p := q)
    (by rw [hqre]; positivity) (by rw [hqre]; linarith [Real.pi_pos]) hφd hi₁ hi₂ htop hbot
  rw [integral_congr_ae (ae_of_all _ hlπ), integral_congr_ae (ae_of_all _ hl0), integral_const_mul,
    integral_neg_eq_self (fun u : ℝ => pcfCt_Phi μ x (-σ) u),
    integral_neg_eq_self (fun u : ℝ => pcfCt_Phi μ x σ u), hval] at hB
  exact hB

/-- The Stieltjes–Fourier kernel of DLMF 12.12.3: for `0 < re μ < 2`, `x > 0`, `σ ≥ 0`,
`∫₀^∞ t^{μ-1} cos(tσ + π/2 - πμ/2)/(x² + t²) dt = (π/2) x^{μ-2} e^{-xσ}`. -/
theorem pcfCt_kernel {μ : ℂ} (hm0 : 0 < μ.re) (hm2 : μ.re < 2) {x : ℝ} (hx : 0 < x)
    {σ : ℝ} (hσ : 0 ≤ σ) :
    IntegrableOn (fun t : ℝ => (t:ℂ)^(μ-1) * cos (t*σ + (π/2 - π*μ/2)) / ((x:ℂ)^2 + (t:ℂ)^2))
      (Ioi 0) ∧
    ∫ t in Ioi (0:ℝ), (t:ℂ)^(μ-1) * cos (t*σ + (π/2 - π*μ/2)) / ((x:ℂ)^2 + (t:ℂ)^2) =
      π/2 * (x:ℂ)^(μ-2) * exp (-(x*σ:ℂ)) := by
  have hA : ∀ s : ℝ, IntegrableOn (pcfCt_gs μ x s) (Ioi 0) ∧
      ∫ t in Ioi (0:ℝ), pcfCt_gs μ x s t = ∫ u : ℝ, pcfCt_Phi μ x s u := fun s => by
    have hf : (fun u : ℝ => pcfCt_Phi μ x s u) = fun u => Real.exp u • pcfCt_gs μ x s (Real.exp u) :=
      funext fun u => pcfCt_Phi_real μ x s u
    refine ⟨(integrable_comp_exp _).mp (hf ▸ pcfCt_Phi_real_integrable hm0 hm2 hx s), ?_⟩
    rw [hf, integral_comp_exp]
  obtain ⟨i1, v1⟩ := hA σ
  obtain ⟨i2, v2⟩ := hA (-σ)
  set c : ℂ := π/2 - π*μ/2
  have hfun : (fun t : ℝ => (t:ℂ)^(μ-1) * cos (t*σ + c) / ((x:ℂ)^2 + (t:ℂ)^2)) =
      fun t => (exp (c*I) * pcfCt_gs μ x σ t + exp (-(c*I)) * pcfCt_gs μ x (-σ) t) / 2 := by
    funext t
    simp only [pcfCt_gs, Complex.cos]
    rw [show ((t:ℂ)*σ + c)*I = I*σ*t + c*I by ring, show -((t:ℂ)*σ + c)*I = I*((-σ:ℝ):ℂ)*t + -(c*I) by
      push_cast; ring, Complex.exp_add, Complex.exp_add]
    ring
  rw [hfun]
  refine ⟨((i1.const_mul _).add (i2.const_mul _)).div_const 2, ?_⟩
  rw [integral_div, integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul,
    integral_const_mul, v1, v2]
  have hs := pcfCt_kernel_shift hm0 hm2 hx hσ
  generalize (∫ u : ℝ, pcfCt_Phi μ x σ u) = A at hs ⊢
  generalize (∫ u : ℝ, pcfCt_Phi μ x (-σ) u) = B at hs ⊢
  have e1 : exp (c*I) = I * exp (-(μ*π/2*I)) := by
    rw [show c*I = π/2*I + -(μ*π/2*I) by simp only [c]; ring, Complex.exp_add, exp_pi_div_two_mul_I]
  have e2 : exp (-(c*I)) = -(exp (c*I) * exp (μ*π*I)) := by
    rw [← Complex.exp_add, show -(c*I) = (c*I + μ*π*I) + -(π*I) by simp only [c]; ring,
      Complex.exp_add (c*I + μ*π*I), Complex.exp_neg, exp_pi_mul_I]; ring
  have e3 : exp (μ*((Real.log x:ℂ) + π/2*I)) = (x:ℂ)^μ * exp (μ*π/2*I) := by
    rw [pcfCt_ofReal_cpow hx, ← Complex.exp_add]; ring_nf
  have e4 : (x:ℂ)^(μ-2) = (x:ℂ)^μ / (x:ℂ)^2 := by
    rw [cpow_sub _ _ (ofReal_ne_zero.mpr hx.ne'), cpow_two]
  have e5 : exp (-(μ*π/2*I)) * exp (μ*π/2*I) = 1 := by rw [← Complex.exp_add]; simp
  have hx0 : (x:ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  rw [e2, e1, e4]
  rw [e3] at hs
  rw [show (I * exp (-(μ*π/2*I)) * A + -(I * exp (-(μ*π/2*I)) * exp (μ*π*I)) * B) / 2 =
      -(I * exp (-(μ*π/2*I)) / 2) * (exp (μ*π*I) * B - A) by ring, hs]
  set P : ℂ := π * (x:ℂ)^μ * exp (-(x*σ:ℂ)) / (2*(x:ℂ)^2)
  linear_combination P * e5 + (-(P * exp (-(μ*π/2*I)) * exp (μ*π/2*I))) * I_sq

/-- Exponential decay of `e^{-t²/4} U(a,t)` on the real line, uniform for `‖-a-1/2‖ ≤ P`
(from the vertical-line representation 12.5.6 at `c = 1`). -/
theorem pcfCt_U_decay (P : ℝ) : ∃ M : ℝ, ∀ a : ℂ, ‖-a-1/2‖ ≤ P → ∀ t : ℝ,
    ‖exp (-(t:ℂ)^2/4) * pcfU a t‖ ≤ M * Real.exp (-t) := by
  have hs : (0:ℝ) < Real.sqrt (2*π) := Real.sqrt_pos.mpr (by positivity)
  refine ⟨(∫ y, pcfCt_dom 0 P 1 y) / Real.sqrt (2*π), fun a ha t => ?_⟩
  have hV := pcfCt_vertical a t (c := 1) one_pos
  have hval : exp (-(t:ℂ)^2/4) * pcfU a t =
      (∫ y : ℝ, exp (-(t:ℂ)*(((1:ℝ):ℂ)+y*I) + (((1:ℝ):ℂ)+y*I)^2/2) * (((1:ℝ):ℂ)+y*I)^(-a-1/2)) /
        Real.sqrt (2*π) := by
    rw [hV]; field_simp
  rw [hval, norm_div, norm_real, Real.norm_of_nonneg hs.le]
  rw [div_le_iff₀ hs, show (∫ y, pcfCt_dom 0 P 1 y) / Real.sqrt (2*π) * Real.exp (-t) * Real.sqrt (2*π)
    = ∫ y, Real.exp (-t) * pcfCt_dom 0 P 1 y by
      rw [integral_const_mul]; field_simp]
  refine norm_integral_le_of_norm_le ((pcfCt_dom_integrable 0 P 1).const_mul _)
    (Eventually.of_forall fun y => ?_)
  have hb := pcfCt_vert_le (z := 0) (p := -a-1/2) (Z := 0) (P := P) one_pos (by simp) ha y
  have he : exp (-(t:ℂ)*(((1:ℝ):ℂ)+y*I) + (((1:ℝ):ℂ)+y*I)^2/2) =
      exp (-(t:ℂ)) * exp (((-(t*y):ℝ):ℂ)*I) * exp (-0*(((1:ℝ):ℂ)+y*I) + (((1:ℝ):ℂ)+y*I)^2/2) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; push_cast; ring_nf
  rw [he, mul_assoc, norm_mul, norm_mul, ← ofReal_neg, ← ofReal_exp, norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le, Complex.norm_exp_ofReal_mul_I, mul_one]
  exact mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le

end DLMF.Confluent
