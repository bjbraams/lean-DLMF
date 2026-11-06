/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Zeta.Lerch.HermiteKernel
public import DLMFMathlib.Analysis.SpecialFunctions.Trigonometric.BoseEinsteinWeighted
public import DLMFMathlib.Analysis.SpecialFunctions.Trigonometric.LinearBounds

/-!
# Uniform bounds for Lerch's Hermite kernel

The sine-power factor vanishes linearly at the origin. Together with the exponential growth
bounds for sine and cosine, this gives a common integrable majorant for bounded orders and
logarithmic arguments in any smaller strip `|Im w| ≤ θ < 2π`.
-/

@[expose] public noncomputable section

open Complex Set Filter MeasureTheory
open scoped Real Topology

namespace DLMF.Zeta.LerchHermite

/-- Bounded orders and logarithmic arguments in a subcritical strip give a common integrable
majorant for the Hermite kernel. -/
theorem exists_integrable_bound_kernel {a : ℂ} (ha : 0 < a.re) {M L θ : ℝ}
    (hM : 0 ≤ M) (hL : 0 ≤ L) (hθ : θ < 2 * π) :
    ∃ g : ℝ → ℝ, IntegrableOn g (Ioi 0) ∧
      ∀ s w : ℂ, ‖s‖ ≤ M → ‖w‖ ≤ L → |w.im| ≤ θ → ∀ x : ℝ, 0 < x →
        ‖kernel s a w x‖ ≤ g x := by
  obtain ⟨Cs, hCs, Ns, hS⟩ := exists_bound_sin_mul_arctan_div_cpow ha hM
  obtain ⟨Cc, hCc, Nc, hC⟩ := exists_bound_cos_mul_arctan_div_cpow ha hM
  refine ⟨fun x => (Cs + Cc * L) *
    (x * (1 + x) ^ (Ns + Nc) * Real.exp (θ * x) / (Real.exp (2 * π * x) - 1)),
    (Real.integrableOn_mul_one_add_pow_mul_exp_div_exp_two_pi_sub_one hθ (Ns + Nc)).const_mul _, ?_⟩
  intro s w hs hw hwi x hx
  have hE : 0 < Real.exp (2 * π * x) - 1 :=
    sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity))
  have hpowS : (1 + x) ^ Ns ≤ (1 + x) ^ (Ns + Nc) :=
    pow_le_pow_right₀ (by linarith) (by omega)
  have hpowC : (1 + x) ^ Nc ≤ (1 + x) ^ (Ns + Nc) :=
    pow_le_pow_right₀ (by linarith) (by omega)
  have hSp : ‖sin (s * arctan (x / a)) /
      (a ^ 2 + (x : ℂ) ^ 2) ^ (s / 2)‖ ≤ Cs * x * (1 + x) ^ (Ns + Nc) :=
    (hS s hs x hx.le).trans (mul_le_mul_of_nonneg_left hpowS (by positivity))
  have hCp : ‖cos (s * arctan (x / a)) /
      (a ^ 2 + (x : ℂ) ^ 2) ^ (s / 2)‖ ≤ Cc * (1 + x) ^ (Ns + Nc) :=
    (hC s hs x hx.le).trans (mul_le_mul_of_nonneg_left hpowC hCc.le)
  have hcos : ‖cos ((x : ℂ) * w)‖ ≤ Real.exp (θ * x) := by
    refine (norm_cos_le_exp_abs_im _).trans (Real.exp_le_exp.mpr ?_)
    rw [show ((x : ℂ) * w).im = x * w.im by simp, abs_mul, abs_of_pos hx]
    nlinarith
  have hsin : ‖sin ((x : ℂ) * w)‖ ≤ x * L * Real.exp (θ * x) := by
    have h := norm_sin_le_norm_mul_exp_abs_im ((x : ℂ) * w)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx,
      show ((x : ℂ) * w).im = x * w.im by simp, abs_mul, abs_of_pos hx] at h
    refine h.trans (mul_le_mul (mul_le_mul_of_nonneg_left hw hx.le)
      (Real.exp_le_exp.mpr (by nlinarith)) (Real.exp_pos _).le (by positivity))
  have hsplit : kernel s a w x =
      ((sin (s * arctan (x / a)) / (a ^ 2 + (x : ℂ) ^ 2) ^ (s / 2)) * cos (x * w) -
        (cos (s * arctan (x / a)) / (a ^ 2 + (x : ℂ) ^ 2) ^ (s / 2)) * sin (x * w)) /
        (Real.exp (2 * π * x) - 1 : ℝ) := by
    rw [kernel, sin_sub]
    ring
  rw [hsplit, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hE]
  calc
    _ ≤ (‖sin (s * arctan (x / a)) / (a ^ 2 + (x : ℂ) ^ 2) ^ (s / 2)‖ *
        ‖cos ((x : ℂ) * w)‖ +
        ‖cos (s * arctan (x / a)) / (a ^ 2 + (x : ℂ) ^ 2) ^ (s / 2)‖ *
          ‖sin ((x : ℂ) * w)‖) / (Real.exp (2 * π * x) - 1) := by
      apply div_le_div_of_nonneg_right _ hE.le
      convert norm_sub_le
        ((sin (s * arctan (x / a)) / (a ^ 2 + (x : ℂ) ^ 2) ^ (s / 2)) * cos (x * w))
        ((cos (s * arctan (x / a)) / (a ^ 2 + (x : ℂ) ^ 2) ^ (s / 2)) * sin (x * w))
        using 1; simp only [norm_mul]
    _ ≤ ((Cs * x * (1 + x) ^ (Ns + Nc)) * Real.exp (θ * x) +
        (Cc * (1 + x) ^ (Ns + Nc)) * (x * L * Real.exp (θ * x))) /
        (Real.exp (2 * π * x) - 1) := by
      apply div_le_div_of_nonneg_right _ hE.le
      exact add_le_add (mul_le_mul hSp hcos (norm_nonneg _) (by positivity))
        (mul_le_mul hCp hsin (norm_nonneg _) (by positivity))
    _ = _ := by ring

/-- The Hermite correction integral is absolutely convergent throughout the logarithmic strip. -/
theorem integrableOn_kernel {a w : ℂ} (ha : 0 < a.re) (hw : |w.im| < 2 * π) (s : ℂ) :
    IntegrableOn (kernel s a w) (Ioi 0) := by
  obtain ⟨g, hg, hb⟩ := exists_integrable_bound_kernel ha (norm_nonneg s) (norm_nonneg w) hw
  exact hg.mono' ((continuousOn_kernel ha s w).aestronglyMeasurable measurableSet_Ioi)
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx using
      hb s w le_rfl le_rfl le_rfl x hx)

/-- The ray kernel is continuous on the positive half-line. -/
theorem continuousOn_rayKernel {a : ℂ} (ha : 0 < a.re) (s w : ℂ) :
    ContinuousOn (rayKernel s a w) (Ioi 0) := by
  intro x hx
  have hx0 : 0 < x := hx
  have hz : a + x ∈ slitPlane := Or.inl (by simp; linarith)
  have he : ContinuousAt (fun t : ℝ => exp (w * t)) x := by fun_prop
  have hp : ContinuousAt (fun t : ℝ => (a + t) ^ (-s)) x :=
    ContinuousAt.cpow (by fun_prop) continuousAt_const hz
  exact (he.mul hp).continuousWithinAt

/-- For a positive integration variable the ray kernel is entire in the order. -/
theorem differentiable_rayKernel_order {a : ℂ} (ha : 0 < a.re) (w : ℂ) {x : ℝ}
    (hx : 0 < x) : Differentiable ℂ (fun s => rayKernel s a w x) := by
  have hn : a + x ≠ 0 := by intro h; have := congrArg re h; simp at this; linarith
  exact (differentiable_id.neg.const_cpow (Or.inl hn)).const_mul _

/-- The ray kernel is entire in its logarithmic argument at each integration variable. -/
theorem differentiable_rayKernel_argument (a s : ℂ) (x : ℝ) :
    Differentiable ℂ (fun w => rayKernel s a w x) := by unfold rayKernel; fun_prop

/-- Exponential damping gives an integrable ray majorant uniformly on bounded orders. -/
theorem exists_integrable_bound_rayKernel {a : ℂ} (ha : 0 < a.re) {M δ : ℝ}
    (hM : 0 ≤ M) (hδ : 0 < δ) :
    ∃ g : ℝ → ℝ, IntegrableOn g (Ioi 0) ∧
      ∀ s w : ℂ, ‖s‖ ≤ M → w.re ≤ -δ → ∀ x : ℝ, 0 < x →
        ‖rayKernel s a w x‖ ≤ g x := by
  obtain ⟨C, hC, N, hb⟩ := exists_bound_cpow_of_norm_bounds ha (norm_nonneg a) hM
  refine ⟨fun x => C * ((1 + |x|) ^ N * Real.exp (-(δ * |x|))),
    ((Real.integrable_one_add_abs_pow_mul_exp_neg hδ N).const_mul C).integrableOn, ?_⟩
  intro s w hs hw x hx
  have hlo : a.re ≤ ‖a + (x : ℂ)‖ := by
    have h := re_le_norm (a + (x : ℂ))
    simp only [add_re, ofReal_re] at h
    linarith
  have hhi : ‖a + (x : ℂ)‖ ≤ ‖a‖ + x := by
    simpa only [norm_real, Real.norm_eq_abs, abs_of_pos hx] using norm_add_le a (x : ℂ)
  have hp := hb (-s) (by simpa using hs) (a + x) x hx.le hlo hhi
  change ‖rayKernel s a w x‖ ≤ C * ((1 + |x|) ^ N * Real.exp (-(δ * |x|)))
  rw [rayKernel, norm_mul, norm_exp, show (w * x).re = w.re * x by simp, abs_of_pos hx]
  calc
    _ ≤ Real.exp (-(δ * x)) * (C * (1 + x) ^ N) := by
      exact mul_le_mul (Real.exp_le_exp.mpr (by nlinarith)) hp (norm_nonneg _)
        (Real.exp_pos _).le
    _ = _ := by ring

/-- The ray integral converges absolutely for all orders in the left half-plane of
logarithmic arguments. -/
theorem integrableOn_rayKernel_of_re_neg {a w : ℂ} (ha : 0 < a.re) (hw : w.re < 0) (s : ℂ) :
    IntegrableOn (rayKernel s a w) (Ioi 0) := by
  obtain ⟨g, hg, hb⟩ := exists_integrable_bound_rayKernel ha (norm_nonneg s) (neg_pos.mpr hw)
  exact hg.mono' ((continuousOn_rayKernel ha s w).aestronglyMeasurable measurableSet_Ioi)
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx using
      hb s w le_rfl (by simp) x hx)

/-- In the absolutely convergent order range, the ray kernel has an integrable majorant
uniformly on the closed left half-plane. -/
theorem exists_integrable_bound_rayKernel_boundary {a s : ℂ} (ha : 0 < a.re) (hs : 1 < s.re) :
    ∃ g : ℝ → ℝ, IntegrableOn g (Ioi 0) ∧
      ∀ w : ℂ, w.re ≤ 0 → ∀ x : ℝ, 0 < x → ‖rayKernel s a w x‖ ≤ g x := by
  refine ⟨fun x => (a.re + x) ^ (-s.re) * Real.exp (π * |s.im|), ?_, ?_⟩
  · have h := integrableOn_add_rpow_Ioi_of_lt (a := -s.re) (c := 0) (m := a.re)
      (by linarith) (by linarith)
    simpa only [IntegrableOn, add_comm] using h.mul_const (Real.exp (π * |s.im|))
  · intro w hw x hx
    have hr : 0 < a.re + x := by linarith
    have hlo : a.re + x ≤ ‖a + (x : ℂ)‖ := by simpa using re_le_norm (a + (x : ℂ))
    have hp := norm_cpow_le_of_norm_lower_bound hr hlo
      (s := -s) (by simp only [neg_re]; linarith)
    simp only [neg_re, neg_im, abs_neg] at hp
    rw [rayKernel, norm_mul, norm_exp, show (w * x).re = w.re * x by simp]
    calc
      _ ≤ 1 * ((a.re + x) ^ (-s.re) * Real.exp (π * |s.im|)) := by
        exact mul_le_mul (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg hw hx.le))
          hp (norm_nonneg _) (by norm_num)
      _ = _ := one_mul _

/-- Absolute convergence of the ray integral on the unit-circle boundary. -/
theorem integrableOn_rayKernel_of_re_le_zero {a s w : ℂ} (ha : 0 < a.re) (hs : 1 < s.re)
    (hw : w.re ≤ 0) : IntegrableOn (rayKernel s a w) (Ioi 0) := by
  obtain ⟨g, hg, hb⟩ := exists_integrable_bound_rayKernel_boundary ha hs
  exact hg.mono' ((continuousOn_rayKernel ha s w).aestronglyMeasurable measurableSet_Ioi)
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx using hb w hw x hx)

/-- The Hermite correction integral is entire in the order throughout its argument strip. -/
theorem differentiable_integral_kernel_order {a w : ℂ} (ha : 0 < a.re)
    (hw : |w.im| < 2 * π) :
    Differentiable ℂ (fun s => ∫ x in Ioi (0 : ℝ), kernel s a w x) := by
  rw [← differentiableOn_univ]
  refine differentiableOn_integral_Ioi_of_locally_dominated isOpen_univ 0 ?_ ?_ ?_
  · intro s _
    exact (continuousOn_kernel ha s w).aestronglyMeasurable measurableSet_Ioi
  · exact Eventually.of_forall fun x => (differentiable_kernel_order ha w x).differentiableOn
  · intro s _
    obtain ⟨g, hg, hb⟩ := exists_integrable_bound_kernel ha
      (M := ‖s‖ + 1) (L := ‖w‖) (by positivity) (norm_nonneg w) hw
    refine ⟨Metric.ball s 1, Metric.ball_mem_nhds s one_pos, g, hg, ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx t ht
    have ht' : ‖t‖ ≤ ‖s‖ + 1 := by
      have hdist : ‖t - s‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using ht
      have htri := norm_add_le (t - s) s
      rw [sub_add_cancel] at htri
      linarith
    exact hb t w ht' le_rfl le_rfl x hx

/-- The Hermite correction integral is holomorphic in its logarithmic argument. -/
theorem differentiableOn_integral_kernel_argument {a : ℂ} (ha : 0 < a.re) (s : ℂ) :
    DifferentiableOn ℂ (fun w => ∫ x in Ioi (0 : ℝ), kernel s a w x)
      {w : ℂ | |w.im| < 2 * π} := by
  refine differentiableOn_integral_Ioi_of_locally_dominated
    (isOpen_lt (continuous_abs.comp continuous_im) continuous_const) 0 ?_ ?_ ?_
  · intro w _
    exact (continuousOn_kernel ha s w).aestronglyMeasurable measurableSet_Ioi
  · exact Eventually.of_forall fun x => (differentiable_kernel_argument ha s x).differentiableOn
  · intro w hw
    change |w.im| < 2 * π at hw
    let θ : ℝ := (2 * π + |w.im|) / 2
    have hθ0 : |w.im| < θ := by dsimp [θ]; linarith
    have hθ : θ < 2 * π := by dsimp [θ]; linarith
    obtain ⟨g, hg, hb⟩ := exists_integrable_bound_kernel ha (norm_nonneg s)
      (L := ‖w‖ + 1) (by positivity) hθ
    let V : Set ℂ := Metric.ball w 1 ∩ {t : ℂ | |t.im| < θ}
    have hV : V ∈ 𝓝 w := Filter.inter_mem (Metric.ball_mem_nhds w one_pos)
      ((isOpen_lt (continuous_abs.comp continuous_im) continuous_const).mem_nhds hθ0)
    refine ⟨V, hV, g, hg, ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx t ht
    have ht' : ‖t‖ ≤ ‖w‖ + 1 := by
      have hdist : ‖t - w‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using ht.1
      have htri := norm_add_le (t - w) w
      rw [sub_add_cancel] at htri
      linarith
    exact hb s t le_rfl ht' ht.2.le x hx

/-- The exponentially damped ray integral is entire in the order. -/
theorem differentiable_integral_rayKernel_order {a w : ℂ} (ha : 0 < a.re) (hw : w.re < 0) :
    Differentiable ℂ (fun s => ∫ x in Ioi (0 : ℝ), rayKernel s a w x) := by
  rw [← differentiableOn_univ]
  refine differentiableOn_integral_Ioi_of_locally_dominated isOpen_univ 0 ?_ ?_ ?_
  · intro s _
    exact (continuousOn_rayKernel ha s w).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (differentiable_rayKernel_order ha w hx).differentiableOn
  · intro s _
    obtain ⟨g, hg, hb⟩ := exists_integrable_bound_rayKernel ha
      (M := ‖s‖ + 1) (by positivity) (neg_pos.mpr hw)
    refine ⟨Metric.ball s 1, Metric.ball_mem_nhds s one_pos, g, hg, ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx t ht
    have ht' : ‖t‖ ≤ ‖s‖ + 1 := by
      have hdist : ‖t - s‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using ht
      have htri := norm_add_le (t - s) s
      rw [sub_add_cancel] at htri
      linarith
    exact hb t w ht' (by simp) x hx

/-- The ray integral is holomorphic on the open left half-plane of logarithmic arguments. -/
theorem differentiableOn_integral_rayKernel_argument {a : ℂ} (ha : 0 < a.re) (s : ℂ) :
    DifferentiableOn ℂ (fun w => ∫ x in Ioi (0 : ℝ), rayKernel s a w x) {w : ℂ | w.re < 0} := by
  refine differentiableOn_integral_Ioi_of_locally_dominated
    (isOpen_lt continuous_re continuous_const) 0 ?_ ?_ ?_
  · intro w _
    exact (continuousOn_rayKernel ha s w).aestronglyMeasurable measurableSet_Ioi
  · exact Eventually.of_forall fun x => (differentiable_rayKernel_argument a s x).differentiableOn
  · intro w hw
    change w.re < 0 at hw
    have hδ : 0 < -w.re / 2 := by linarith
    obtain ⟨g, hg, hb⟩ := exists_integrable_bound_rayKernel ha (norm_nonneg s) hδ
    refine ⟨{t : ℂ | t.re < w.re / 2},
      (isOpen_lt continuous_re continuous_const).mem_nhds
        (show w.re < w.re / 2 by linarith), g, hg, ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx t ht
    exact hb s t le_rfl (by change t.re < w.re / 2 at ht; linarith) x hx

end DLMF.Zeta.LerchHermite
