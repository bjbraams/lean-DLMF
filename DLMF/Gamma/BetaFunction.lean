/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Complex.ParametricHolomorphy
public import TauCeti.Analysis.SpecialFunctions.Beta
public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.Analysis.Fourier.Inversion
public import DLMFMathlib.Analysis.Asymptotics.WatsonSector

/-!
# Beta function (DLMF §5.12)

The Euler integral and the identity `B(a,b) = Γ(a)Γ(b)/Γ(a+b)` are Mathlib
`betaIntegral` and `Gamma_mul_Gamma_eq_betaIntegral`, and are also
`selberg_integral_one` in `DLMF.Selberg.Basic`. The trigonometric integrals 5.12.5–5.12.6 use
Mathlib's binomial series (`Complex.one_add_cpow_hasFPowerSeriesOnBall_zero`). Contour
formulae 5.12.9–5.12.12 are deferred. The real Euler integral uses the Tau Ceti contributors’
`TauCeti.integral_rpow_mul_one_sub_rpow`, built on Mathlib’s beta theory.
-/

@[expose] public section

open Complex MeasureTheory intervalIntegral
open scoped Real

noncomputable section

namespace DLMF.Gamma

/-- Euler's Beta integral for real parameters, `∫₀¹ u^(a-1) (1-u)^(b-1) du = Γ(a)Γ(b)/Γ(a+b)`.
This is the real form of Mathlib's `Complex.Gamma_mul_Gamma_eq_betaIntegral`. -/
theorem real_betaIntegral {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ u : ℝ in (0 : ℝ)..1, u ^ (a - 1) * (1 - u) ^ (b - 1) =
      Real.Gamma a * Real.Gamma b / Real.Gamma (a + b) := by
  simpa only [ProbabilityTheory.beta] using
    TauCeti.integral_rpow_mul_one_sub_rpow ha hb

@[dlmf 5.12.E2]
theorem beta_sin_cos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ θ : ℝ in (0 : ℝ)..(π / 2), Real.sin θ ^ (2 * a - 1) * Real.cos θ ^ (2 * b - 1) =
      (1 / 2) * (Real.Gamma a * Real.Gamma b / Real.Gamma (a + b)) := by
  -- The substitution `u = sin² θ` maps `(0, π/2)` onto `(0, 1)`.
  set f : ℝ → ℝ := fun θ => Real.sin θ ^ 2 with hf
  set f' : ℝ → ℝ := fun θ => 2 * Real.sin θ * Real.cos θ with hf'
  have hsin {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hcos {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hderiv : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), HasDerivWithinAt f (f' θ) (Set.Ioo 0 (π / 2)) θ := by
    intro θ _
    refine HasDerivAt.hasDerivWithinAt ?_
    convert (Real.hasDerivAt_sin θ).pow 2 using 1
    simp only [hf']
    ring
  have hinj : Set.InjOn f (Set.Ioo 0 (π / 2)) := by
    intro x hx y hy hxy
    have h := (pow_left_inj₀ (hsin hx).le (hsin hy).le two_ne_zero).mp hxy
    exact Real.injOn_sin ⟨by linarith [hx.1, Real.pi_pos], hx.2.le⟩
      ⟨by linarith [hy.1, Real.pi_pos], hy.2.le⟩ h
  have himage : f '' Set.Ioo 0 (π / 2) = Set.Ioo 0 1 := by
    ext u
    constructor
    · rintro ⟨θ, hθ, rfl⟩
      have hs := hsin hθ
      have hc := hcos hθ
      refine ⟨by positivity, ?_⟩
      have := Real.sin_sq_add_cos_sq θ
      simp only [hf]
      nlinarith
    · rintro ⟨h0, h1⟩
      have hs0 : 0 < Real.sqrt u := Real.sqrt_pos.mpr h0
      have hs1 : Real.sqrt u < 1 := by rw [Real.sqrt_lt' one_pos]; simpa using h1
      refine ⟨Real.arcsin (Real.sqrt u), ⟨Real.arcsin_pos.mpr hs0, ?_⟩, ?_⟩
      · exact (Real.arcsin_lt_pi_div_two).mpr hs1
      · simp only [hf]
        rw [Real.sin_arcsin (by linarith) hs1.le, Real.sq_sqrt h0.le]
  have key := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj
    (fun u : ℝ => u ^ (a - 1) * (1 - u) ^ (b - 1))
  rw [himage] at key
  rw [← real_betaIntegral ha hb, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo, key, intervalIntegral.integral_of_le (by positivity),
    integral_Ioc_eq_integral_Ioo, ← MeasureTheory.integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo fun θ hθ => ?_
  have hs := hsin hθ
  have hc := hcos hθ
  have hpow {x : ℝ} (hx : 0 < x) (p : ℝ) : (x ^ 2) ^ (p - 1) = x ^ (2 * p - 1) / x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le, eq_div_iff hx.ne',
      ← Real.rpow_add_one hx.ne']
    norm_num
    ring_nf
  simp only [hf, hf', smul_eq_mul]
  rw [abs_of_pos (by positivity), show 1 - Real.sin θ ^ 2 = Real.cos θ ^ 2 by
    rw [Real.cos_sq']]
  rw [hpow hs, hpow hc]
  field_simp

@[dlmf 5.12.E3]
theorem beta_on_Ioi {a b : ℂ} (_ha : 0 < a.re) (_hb : 0 < b.re) :
    ∫ t : ℝ in Set.Ioi 0, (t : ℂ) ^ (a - 1) / (1 + (t : ℂ)) ^ (a + b) =
      betaIntegral a b := by
  -- The substitution `u = t / (1 + t)` maps `(0, ∞)` onto `(0, 1)`.
  set f : ℝ → ℝ := fun t => t / (1 + t) with hf
  set f' : ℝ → ℝ := fun t => 1 / (1 + t) ^ 2 with hf'
  have hderiv : ∀ t ∈ Set.Ioi (0 : ℝ), HasDerivWithinAt f (f' t) (Set.Ioi 0) t := by
    intro t ht
    have h1 : 1 + t ≠ 0 := ne_of_gt (by linarith [Set.mem_Ioi.mp ht])
    have hd : HasDerivAt f (f' t) t := by
      convert (hasDerivAt_id t).div ((hasDerivAt_id t).const_add 1) h1 using 1
      · rfl
      · simp only [hf', id]
        ring
    exact hd.hasDerivWithinAt
  have hinj : Set.InjOn f (Set.Ioi 0) := by
    intro x hx y hy hxy
    have hx' : 1 + x ≠ 0 := ne_of_gt (by linarith [Set.mem_Ioi.mp hx])
    have hy' : 1 + y ≠ 0 := ne_of_gt (by linarith [Set.mem_Ioi.mp hy])
    simp only [hf] at hxy
    field_simp at hxy
    linarith
  have himage : f '' Set.Ioi 0 = Set.Ioo 0 1 := by
    ext u
    constructor
    · rintro ⟨t, ht, rfl⟩
      have ht' : 0 < t := ht
      refine ⟨by positivity, ?_⟩
      rw [hf, div_lt_one (by linarith)]
      linarith
    · rintro ⟨h0, h1⟩
      refine ⟨u / (1 - u), div_pos h0 (by linarith), ?_⟩
      have : 1 - u ≠ 0 := ne_of_gt (by linarith)
      simp only [hf]
      field_simp
      ring
  have key := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj
    (fun u : ℝ => (u : ℂ) ^ (a - 1) * (1 - (u : ℂ)) ^ (b - 1))
  rw [himage] at key
  rw [betaIntegral, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo,
    key]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : 0 < t := ht
  have ht1 : 0 < 1 + t := by linarith
  have hft : 0 < f t := by simp only [hf]; positivity
  have hcpow (x : ℝ) (hx : 0 < x) (s : ℂ) :
      (x : ℂ) ^ s = Complex.exp (Real.log x * s) := by
    rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx.ne'), ofReal_log hx.le]
  have hlogf : Real.log (f t) = Real.log t - Real.log (1 + t) := by
    simp only [hf]
    exact Real.log_div ht0.ne' ht1.ne'
  have h1f : 1 - f t = (1 + t)⁻¹ := by
    simp only [hf]
    field_simp
    ring
  have habs : |f' t| = Real.exp (-2 * Real.log (1 + t)) := by
    rw [abs_of_pos (by simp only [hf']; positivity),
      show -2 * Real.log (1 + t) = -(Real.log (1 + t) + Real.log (1 + t)) by ring,
      Real.exp_neg, Real.exp_add, Real.exp_log ht1]
    simp only [hf']
    ring
  have e2 : (1 + (t : ℂ)) ^ (a + b) = Complex.exp (Real.log (1 + t) * (a + b)) := by
    rw [← hcpow _ ht1]
    push_cast
    rfl
  have e4 : (1 - ((f t : ℝ) : ℂ)) ^ (b - 1) = Complex.exp (-Real.log (1 + t) * (b - 1)) := by
    rw [show (1 - ((f t : ℝ) : ℂ)) = ((1 - f t : ℝ) : ℂ) by push_cast; rfl,
      hcpow _ (by rw [h1f]; positivity), h1f, Real.log_inv]
    push_cast
    rfl
  rw [hcpow _ ht0, e2, hcpow _ hft, e4, habs, Complex.real_smul, Complex.ofReal_exp, hlogf,
    ← Complex.exp_sub, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

section BetaShifted

open Filter
open scoped Topology

/-- Helper lemma for `beta_shifted`: the case of a positive real shift, by the substitution
`s = (1 + x) t / (x + t)`. -/
theorem beta_shifted_of_pos {a b : ℂ} {x : ℝ} (hx : 0 < x) :
    ∫ t : ℝ in Set.Ioo 0 1,
        (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - 1) * ((t : ℂ) + x) ^ (-(a + b)) =
      betaIntegral a b * (1 + (x : ℂ)) ^ (-a) * (x : ℂ) ^ (-b) := by
  set f : ℝ → ℝ := fun t => (1 + x) * t / (x + t) with hf
  set f' : ℝ → ℝ := fun t => x * (1 + x) / (x + t) ^ 2 with hf'
  have hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivWithinAt f (f' t) (Set.Ioo 0 1) t := by
    intro t ht
    have h1 : x + t ≠ 0 := ne_of_gt (by linarith [ht.1])
    have hd : HasDerivAt f (f' t) t := by
      convert ((hasDerivAt_id t).const_mul (1 + x)).div ((hasDerivAt_id t).const_add x) h1
        using 1
      · rfl
      · simp only [hf', id]
        ring
    exact hd.hasDerivWithinAt
  have hinj : Set.InjOn f (Set.Ioo 0 1) := by
    intro t ht u hu htu
    have h1 : x + t ≠ 0 := ne_of_gt (by linarith [ht.1])
    have h2 : x + u ≠ 0 := ne_of_gt (by linarith [hu.1])
    simp only [hf] at htu
    field_simp at htu
    have h3 : x * (t - u) = 0 := by linear_combination htu
    linarith [(mul_eq_zero.mp h3).resolve_left hx.ne']
  have himage : f '' Set.Ioo 0 1 = Set.Ioo 0 1 := by
    ext u
    constructor
    · rintro ⟨t, ht, rfl⟩
      have ht0 : 0 < t := ht.1
      have ht1 : t < 1 := ht.2
      refine ⟨by simp only [hf]; positivity, ?_⟩
      rw [hf, div_lt_one (by linarith)]
      nlinarith
    · rintro ⟨h0, h1⟩
      have hd : 0 < 1 + x - u := by linarith
      refine ⟨u * x / (1 + x - u), ⟨by positivity, ?_⟩, ?_⟩
      · rw [div_lt_one hd]
        nlinarith
      · simp only [hf]
        field_simp
        ring
  have key := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj
    (fun u : ℝ => (u : ℂ) ^ (a - 1) * (1 - (u : ℂ)) ^ (b - 1))
  rw [himage] at key
  rw [betaIntegral, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo,
    key, mul_assoc, ← MeasureTheory.integral_mul_const]
  refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
  have ht0 : 0 < t := ht.1
  have ht1 : 0 < 1 - t := by linarith [ht.2]
  have htx : 0 < t + x := by linarith
  have hx1 : 0 < 1 + x := by linarith
  have hcpow (y : ℝ) (hy : 0 < y) (w : ℂ) :
      (y : ℂ) ^ w = Complex.exp (Real.log y * w) := by
    rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hy.ne'), ofReal_log hy.le]
  have hft : 0 < f t := by simp only [hf]; positivity
  have h1f : 1 - f t = x * (1 - t) / (t + x) := by
    simp only [hf]
    field_simp
    ring
  have h1f0 : 0 < 1 - f t := by rw [h1f]; positivity
  have hlogf : Real.log (f t) = Real.log (1 + x) + Real.log t - Real.log (t + x) := by
    simp only [hf]
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) ht0.ne',
      add_comm x t]
  have hlog1f : Real.log (1 - f t) = Real.log x + Real.log (1 - t) - Real.log (t + x) := by
    rw [h1f, Real.log_div (by positivity) htx.ne', Real.log_mul hx.ne' ht1.ne']
  have habs : |f' t| =
      Real.exp (Real.log x + Real.log (1 + x) - 2 * Real.log (t + x)) := by
    rw [abs_of_pos (by simp only [hf']; positivity),
      show Real.log x + Real.log (1 + x) - 2 * Real.log (t + x) =
        Real.log x + Real.log (1 + x) - (Real.log (t + x) + Real.log (t + x)) by ring,
      Real.exp_sub, Real.exp_add, Real.exp_add, Real.exp_log hx, Real.exp_log hx1,
      Real.exp_log htx]
    simp only [hf']
    ring
  have e1 : (1 - (t : ℂ)) ^ (b - 1) = Complex.exp (Real.log (1 - t) * (b - 1)) := by
    rw [← hcpow _ ht1]
    push_cast
    rfl
  have e2 : ((t : ℂ) + x) ^ (-(a + b)) = Complex.exp (Real.log (t + x) * (-(a + b))) := by
    rw [← hcpow _ htx]
    push_cast
    rfl
  have e3 : (1 - ((f t : ℝ) : ℂ)) ^ (b - 1) = Complex.exp (Real.log (1 - f t) * (b - 1)) := by
    rw [← hcpow _ h1f0]
    push_cast
    rfl
  have e4 : (1 + (x : ℂ)) ^ (-a) = Complex.exp (Real.log (1 + x) * (-a)) := by
    rw [← hcpow _ hx1]
    push_cast
    rfl
  rw [hcpow t ht0, e1, e2, hcpow _ hft, e3, e4, hcpow x hx, habs, hlogf, hlog1f,
    Complex.real_smul, ofReal_exp]
  simp only [← Complex.exp_add]
  congr 1
  push_cast
  ring

@[dlmf 5.12.E4]
theorem beta_shifted {a b z : ℂ} (ha : 0 < a.re) (hb : 0 < b.re)
    (hz : z ∈ slitPlane) :
    ∫ t : ℝ in (0 : ℝ)..1,
        (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - 1) / ((t : ℂ) + z) ^ (a + b) =
      betaIntegral a b * (1 + z) ^ (-a) * z ^ (-b) := by
  have hform (w : ℂ) (t : ℝ) :
      (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - 1) / ((t : ℂ) + w) ^ (a + b) =
        (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - 1) * ((t : ℂ) + w) ^ (-(a + b)) := by
    rw [cpow_neg, div_eq_mul_inv]
  simp_rw [hform]
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  let I : ℂ → ℂ := fun w => ∫ t : ℝ in Set.Ioo 0 1,
    (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - 1) * ((t : ℂ) + w) ^ (-(a + b))
  change I z = _
  have hAint : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - 1))
      (Set.Ioo 0 1) := by
    have := betaIntegral_convergent ha hb
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at this
    exact this.mono_set Set.Ioo_subset_Ioc_self
  have hslit_add (t : ℝ) (ht : 0 ≤ t) (w : ℂ) (hw : w ∈ slitPlane) :
      (t : ℂ) + w ∈ slitPlane := by
    rw [mem_slitPlane_iff] at hw ⊢
    simp only [add_re, ofReal_re, add_im, ofReal_im, zero_add]
    rcases hw with h | h
    · left
      linarith
    · exact Or.inr h
  have hmeasF (w : ℂ) : AEStronglyMeasurable (fun t : ℝ =>
      (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - 1) * ((t : ℂ) + w) ^ (-(a + b)))
      (volume.restrict (Set.Ioo 0 1)) :=
    Measurable.aestronglyMeasurable (by fun_prop)
  have hdiff : DifferentiableOn ℂ I slitPlane := by
    intro w₀ hw₀
    set S := (fun t : ℝ => (t : ℂ) + w₀) '' Set.Icc 0 1 with hS
    have hSc : IsCompact S := isCompact_Icc.image (by fun_prop)
    have hSU : S ⊆ slitPlane := by
      rintro _ ⟨t, ht, rfl⟩
      exact hslit_add t ht.1 w₀ hw₀
    obtain ⟨δ, hδ, hδU⟩ := hSc.exists_cthickening_subset_open isOpen_slitPlane hSU
    have hKc : IsCompact (Metric.cthickening δ S) := hSc.cthickening
    have hmemK : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ w ∈ Metric.ball w₀ δ,
        (t : ℂ) + w ∈ Metric.cthickening δ S := by
      intro t ht w hw
      apply Metric.mem_cthickening_of_dist_le _ ((t : ℂ) + w₀) _ _
        (show (t : ℂ) + w₀ ∈ S from ⟨t, ht, rfl⟩)
      rw [dist_eq_norm, add_sub_add_left_eq_sub, ← dist_eq_norm]
      exact (Metric.mem_ball.mp hw).le
    have hcont (c : ℂ) : ContinuousOn (fun v : ℂ => v ^ c) (Metric.cthickening δ S) :=
      fun v hv => (continuousAt_cpow_const (hδU hv)).continuousWithinAt
    obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn (hcont (-(a + b) - 1))
    obtain ⟨M₀, hM₀⟩ := hKc.exists_bound_of_continuousOn (hcont (-(a + b)))
    have hball := Metric.ball_mem_nhds w₀ hδ
    have hint0 : Integrable (fun t : ℝ =>
        (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - 1) * ((t : ℂ) + w₀) ^ (-(a + b)))
        (volume.restrict (Set.Ioo 0 1)) := by
      refine Integrable.mono' (hAint.norm.mul_const M₀) (hmeasF w₀) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      rw [norm_mul _ (((t : ℂ) + w₀) ^ (-(a + b)))]
      exact mul_le_mul_of_nonneg_left
        (hM₀ _ (hmemK t (Set.Ioo_subset_Icc_self ht) w₀ (Metric.mem_ball_self hδ)))
        (norm_nonneg _)
    have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict (Set.Ioo 0 1))
      (F := fun w (t : ℝ) =>
        (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - 1) * ((t : ℂ) + w) ^ (-(a + b)))
      (F' := fun w (t : ℝ) => (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - 1) *
        (-(a + b) * ((t : ℂ) + w) ^ (-(a + b) - 1)))
      (bound := fun t : ℝ => ‖(t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - 1)‖ * (‖a + b‖ * M))
      hball (Eventually.of_forall hmeasF) hint0
      (Measurable.aestronglyMeasurable (by fun_prop)) ?_ (hAint.norm.mul_const _) ?_
    · exact h.2.differentiableAt.differentiableWithinAt
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht w hw
      rw [norm_mul _ (-(a + b) * _), norm_mul (-(a + b)), norm_neg]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (hM _ (hmemK t (Set.Ioo_subset_Icc_self ht) w hw)) (norm_nonneg _)) (norm_nonneg _)
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht w hw
      have hmem := hδU (hmemK t (Set.Ioo_subset_Icc_self ht) w hw)
      have := (((hasDerivAt_id w).const_add (t : ℂ)).cpow_const (c := -(a + b)) hmem).const_mul
        ((t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - 1))
      simp only [id, mul_one] at this
      exact this
  have hanI : AnalyticOnNhd ℂ I slitPlane := hdiff.analyticOnNhd isOpen_slitPlane
  have hanR : AnalyticOnNhd ℂ (fun w => betaIntegral a b * (1 + w) ^ (-a) * w ^ (-b))
      slitPlane := by
    refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) isOpen_slitPlane
    have h1w : 1 + w ∈ slitPlane := by simpa using hslit_add 1 zero_le_one w hw
    exact (((differentiableAt_const _).mul (((differentiableAt_const 1).add
      differentiableAt_id).cpow (differentiableAt_const _) h1w)).mul
      (differentiableAt_id.cpow (differentiableAt_const _) hw)).differentiableWithinAt
  have hfreq : ∃ᶠ w in 𝓝[≠] (1 : ℂ), I w = betaIntegral a b * (1 + w) ^ (-a) * w ^ (-b) := by
    have ht : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[≠] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have := (continuous_ofReal.tendsto (1 : ℝ)).mono_left
          (nhdsWithin_le_nhds (s := ({1}ᶜ : Set ℝ)))
        rwa [ofReal_one] at this
      · filter_upwards [self_mem_nhdsWithin] with r hr
        simpa using hr
    apply ht.frequently
    apply Eventually.frequently
    filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds (zero_lt_one' ℝ))] with r hr
    exact beta_shifted_of_pos hr
  exact hanI.eqOn_of_preconnected_of_frequently_eq hanR
    (starConvex_one_slitPlane.isPathConnected one_mem_slitPlane).isConnected.isPreconnected
    one_mem_slitPlane hfreq hz

end BetaShifted

section CosineBeta

/-! ### DLMF 5.12.5–5.12.6

For `a - 1 < b < a + 1` the integral `∫_{-π/2}^{π/2} (2 cos x)^{a-1} e^{ibx} dx` is the
Abel limit `r → 1⁻` of the termwise integral of the binomial series of
`(1 + r e^{2ix})^{a-1} e^{i(b-a+1)x}`. The same series integrated against `u^{s-1}` on `[0, 1]`
gives a Beta integral, and Euler's reflection formula identifies the result. The remaining
range `|b| ≤ a - 1` follows by induction on `a` from the integration-by-parts recurrence
`(a - 1 + b) K(a, b) = (a - 1) K(a - 1, b - 1)`.
-/

open Filter Topology

/-- `cos ^ β` is integrable on `[0, π/2]` for `β > -1`; the integral is a positive Beta value. -/
theorem intervalIntegrable_cos_rpow {β : ℝ} (hβ : -1 < β) :
    IntervalIntegrable (fun x : ℝ => Real.cos x ^ β) volume 0 (π / 2) := by
  have h := beta_sin_cos (a := 1 / 2) (b := (β + 1) / 2) (by norm_num) (by linarith)
  have heq : (fun θ : ℝ => Real.sin θ ^ (2 * (1 / 2 : ℝ) - 1) *
      Real.cos θ ^ (2 * ((β + 1) / 2) - 1)) = fun θ => Real.cos θ ^ β := by
    funext θ
    rw [show 2 * (1 / 2 : ℝ) - 1 = 0 by norm_num, Real.rpow_zero, one_mul]
    congr 1
    ring
  rw [heq] at h
  by_contra hni
  rw [intervalIntegral.integral_undef hni] at h
  have := Real.Gamma_pos_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)
  have := Real.Gamma_pos_of_pos (show (0 : ℝ) < (β + 1) / 2 by linarith)
  have := Real.Gamma_pos_of_pos (show (0 : ℝ) < 1 / 2 + (β + 1) / 2 by linarith)
  have : 0 < (1 / 2 : ℝ) * (Real.Gamma (1 / 2) * Real.Gamma ((β + 1) / 2) /
    Real.Gamma (1 / 2 + (β + 1) / 2)) := by positivity
  linarith

/-- `cos ^ β` is integrable on `[-π/2, π/2]` for `β > -1`. -/
theorem intervalIntegrable_cos_rpow' {β : ℝ} (hβ : -1 < β) :
    IntervalIntegrable (fun x : ℝ => Real.cos x ^ β) volume (-(π / 2)) (π / 2) := by
  have h0 := intervalIntegrable_cos_rpow hβ
  have h1 : IntervalIntegrable (fun x : ℝ => Real.cos x ^ β) volume (-(π / 2)) 0 := by
    have := (IntervalIntegrable.iff_comp_neg (f := fun x : ℝ => Real.cos x ^ β)).mp h0
    simpa [Real.cos_neg] using this.symm
  exact h1.trans h0

/-- An even function: the integral over `[-c, c]` is twice that over `[0, c]`. -/
theorem integral_symm_of_even {f : ℝ → ℝ} {c : ℝ}
    (hf : IntervalIntegrable f volume 0 c) (heven : ∀ x, f (-x) = f x) :
    ∫ x in (-c)..c, f x = 2 * ∫ x in (0 : ℝ)..c, f x := by
  have h1 : IntervalIntegrable f volume (-c) 0 := by
    have := (IntervalIntegrable.iff_comp_neg (f := f)).mp hf
    simpa [heven] using this.symm
  rw [← integral_add_adjacent_intervals h1 hf]
  have h2 : ∫ x in (-c)..0, f x = ∫ x in (0 : ℝ)..c, f x := by
    rw [← neg_zero, ← integral_comp_neg]
    simp [heven]
  rw [h2]
  ring

/-- An odd function integrates to zero over `[-c, c]`. -/
theorem integral_symm_of_odd {f : ℝ → ℝ} {c : ℝ}
    (hf : IntervalIntegrable f volume 0 c) (hodd : ∀ x, f (-x) = -f x) :
    ∫ x in (-c)..c, f x = 0 := by
  have h1 : IntervalIntegrable f volume (-c) 0 := by
    have h' : IntervalIntegrable (fun x => -f x) volume (-c) 0 := by
      simpa [hodd] using ((IntervalIntegrable.iff_comp_neg (f := f)).mp hf).symm
    have h'' := h'.neg
    simp only [Pi.neg_def, neg_neg] at h''
    exact h''
  rw [← integral_add_adjacent_intervals h1 hf]
  have h2 : ∫ x in (-c)..0, f x = -∫ x in (0 : ℝ)..c, f x := by
    rw [← neg_zero, ← integral_comp_neg]
    simp [hodd]
  rw [h2]
  ring

theorem intervalIntegrable_cos_rpow_mul {β : ℝ} (hβ : -1 < β) {g : ℝ → ℝ} (hg : Continuous g)
    {s t : ℝ} (hst : Set.uIcc s t ⊆ Set.Icc (-(π / 2)) (π / 2)) :
    IntervalIntegrable (fun x : ℝ => Real.cos x ^ β * g x) volume s t :=
  ((intervalIntegrable_cos_rpow' hβ).mul_continuousOn hg.continuousOn).mono_set (by
    rwa [Set.uIcc_of_le (by linarith [Real.pi_pos] : -(π / 2) ≤ π / 2)])

theorem intervalIntegrable_ofReal {f : ℝ → ℝ} {s t : ℝ} (hf : IntervalIntegrable f volume s t) :
    IntervalIntegrable (fun x => (f x : ℂ)) volume s t :=
  ⟨hf.1.ofReal, hf.2.ofReal⟩

/-- The complex exponential integral of `cos ^ α` over `[-π/2, π/2]` is twice the cosine
integral over `[0, π/2]`. -/
theorem integral_cos_rpow_mul_exp {α : ℝ} (hα : -1 < α) (b : ℝ) :
    ∫ x in (-(π / 2))..(π / 2), ((Real.cos x ^ α : ℝ) : ℂ) * Complex.exp (↑(b * x) * I) =
      ↑(2 * ∫ x in (0 : ℝ)..(π / 2), Real.cos x ^ α * Real.cos (b * x)) := by
  have hpt : ∀ x : ℝ, ((Real.cos x ^ α : ℝ) : ℂ) * Complex.exp (↑(b * x) * I) =
      ((Real.cos x ^ α * Real.cos (b * x) : ℝ) : ℂ) +
        ((Real.cos x ^ α * Real.sin (b * x) : ℝ) : ℂ) * I := by
    intro x
    rw [Complex.exp_mul_I]
    push_cast
    ring
  simp_rw [hpt]
  have hsub : Set.uIcc (-(π / 2)) (π / 2) ⊆ Set.Icc (-(π / 2)) (π / 2) := by
    rw [Set.uIcc_of_le (by linarith [Real.pi_pos])]
  have hsub0 : Set.uIcc 0 (π / 2) ⊆ Set.Icc (-(π / 2)) (π / 2) := by
    rw [Set.uIcc_of_le (by linarith [Real.pi_pos])]
    exact Set.Icc_subset_Icc (by linarith [Real.pi_pos]) le_rfl
  have hc := intervalIntegrable_cos_rpow_mul hα (g := fun x => Real.cos (b * x))
    (by fun_prop) hsub
  have hs := intervalIntegrable_cos_rpow_mul hα (g := fun x => Real.sin (b * x))
    (by fun_prop) hsub
  rw [intervalIntegral.integral_add (intervalIntegrable_ofReal hc)
      ((intervalIntegrable_ofReal hs).mul_const I),
    intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal,
    intervalIntegral.integral_ofReal]
  rw [integral_symm_of_odd (intervalIntegrable_cos_rpow_mul hα (g := fun x => Real.sin (b * x))
    (by fun_prop) hsub0) (fun x => by simp [Real.cos_neg, Real.sin_neg]),
    integral_symm_of_even (intervalIntegrable_cos_rpow_mul hα (g := fun x => Real.cos (b * x))
    (by fun_prop) hsub0) (fun x => by simp [Real.cos_neg])]
  simp


theorem ae_ne_real (c : ℝ) : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ c := by
  rw [ae_iff]
  simp

/-- The complex binomial series inside the unit disc. -/
theorem hasSum_choose_mul_pow (a : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => Ring.choose a n * z ^ n) ((1 + z) ^ a) := by
  have h := (Complex.one_add_cpow_hasFPowerSeriesOnBall_zero (a := a)).hasSum
    (y := z) (by
      simp only [Metric.mem_eball, edist_zero_right, ← ofReal_norm]
      exact ENNReal.ofReal_lt_one.mpr hz)
  simpa [binomialSeries, FormalMultilinearSeries.coeff_ofScalars, mul_comm] using h

/-- The real binomial series inside the unit interval. -/
theorem hasSum_choose_mul_pow_real (a : ℝ) {x : ℝ} (hx : |x| < 1) :
    HasSum (fun n : ℕ => Ring.choose a n * x ^ n) ((1 + x) ^ a) := by
  have h := (Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := a)).hasSum
    (y := x) (by
      simp only [Metric.mem_eball, edist_zero_right, ← ofReal_norm]
      exact ENNReal.ofReal_lt_one.mpr (by simpa using hx))
  simpa [binomialSeries, FormalMultilinearSeries.coeff_ofScalars, mul_comm] using h

/-- Absolute convergence of the binomial coefficients against `r ^ n` for `r < 1`. -/
theorem summable_norm_choose_mul_pow (a : ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    Summable (fun n : ℕ => ‖Ring.choose a n‖ * r ^ n) := by
  have h := (binomialSeries ℂ a).summable_norm_mul_pow (r := r.toNNReal)
    (lt_of_lt_of_le (ENNReal.coe_lt_one_iff.mpr (Real.toNNReal_lt_one.mpr hr))
      binomialSeries_radius_ge_one)
  simpa [binomialSeries, FormalMultilinearSeries.ofScalars_norm, Real.coe_toNNReal _ hr0] using h

/-- `∫_{-π/2}^{π/2} e^{i(2n+μ)x} dx = (-1)ⁿ sin(πμ/2) / (n + μ/2)`. -/
theorem integral_exp_shifted_freq (n : ℕ) {μ : ℝ} (hμ : 0 < μ) :
    ∫ x in (-(π / 2))..(π / 2), Complex.exp (↑((2 * n + μ) * x) * I) =
      ↑(Real.sin (π * (μ / 2)) * (-1) ^ n / (n + μ / 2)) := by
  have hν : (0 : ℝ) < 2 * n + μ := by positivity
  have hc : ((2 * n + μ : ℝ) : ℂ) * I ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hν.ne') I_ne_zero
  have hfun : (fun x : ℝ => Complex.exp (↑((2 * n + μ) * x) * I)) =
      fun x : ℝ => Complex.exp (((2 * n + μ : ℝ) : ℂ) * I * x) := by
    funext x
    push_cast
    ring_nf
  rw [hfun, integral_exp_mul_complex hc]
  set θ : ℝ := (2 * n + μ) * (π / 2) with hθ
  have h1 : ((2 * n + μ : ℝ) : ℂ) * I * ↑(π / 2) = (θ : ℂ) * I := by
    rw [hθ]; push_cast; ring
  have h2 : ((2 * n + μ : ℝ) : ℂ) * I * ↑(-(π / 2)) = ((-θ : ℝ) : ℂ) * I := by
    rw [hθ]; push_cast; ring
  rw [h1, h2, Complex.exp_mul_I, Complex.exp_mul_I]
  have hsin : Real.sin θ = (-1) ^ n * Real.sin (π * (μ / 2)) := by
    rw [hθ, show (2 * n + μ) * (π / 2) = π * (μ / 2) + n * π by ring, Real.sin_add_nat_mul_pi]
  have hne : ((2 * n + μ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hν.ne'
  have hne' : ((n : ℝ) + μ / 2 : ℂ) ≠ 0 := by
    have : (0 : ℝ) < n + μ / 2 := by positivity
    exact_mod_cast this.ne'
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_neg, Real.sin_neg, hsin]
  push_cast
  field_simp
  ring

/-- Termwise integration of the binomial series of `(1 + r e^{2ix})^α` against `e^{iμx}`. -/
theorem hasSum_integral_one_add_mul_exp (α : ℝ) {μ r : ℝ} (hμ : 0 < μ) (hr0 : 0 ≤ r)
    (hr1 : r < 1) :
    HasSum (fun n : ℕ =>
        ((Real.sin (π * (μ / 2)) * (Ring.choose α n * (-r) ^ n / (n + μ / 2)) : ℝ) : ℂ))
      (∫ x in (-(π / 2))..(π / 2),
        (1 + (r : ℂ) * Complex.exp (↑(2 * x) * I)) ^ (α : ℂ) * Complex.exp (↑(μ * x) * I)) := by
  have key := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := volume) (a := -(π / 2)) (b := π / 2)
    (F := fun (n : ℕ) (x : ℝ) =>
      Ring.choose (α : ℂ) n * (r : ℂ) ^ n * Complex.exp (↑((2 * n + μ) * x) * I))
    (f := fun x : ℝ =>
      (1 + (r : ℂ) * Complex.exp (↑(2 * x) * I)) ^ (α : ℂ) * Complex.exp (↑(μ * x) * I))
    (fun n _ => ‖Ring.choose (α : ℂ) n‖ * r ^ n)
    (fun n => (by fun_prop : Continuous fun x : ℝ =>
      Ring.choose (α : ℂ) n * (r : ℂ) ^ n *
        Complex.exp (↑((2 * n + μ) * x) * I)).aestronglyMeasurable)
    (fun n => Eventually.of_forall fun x _ => by
      rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr0,
        Complex.norm_exp_ofReal_mul_I, mul_one])
    (Eventually.of_forall fun x _ => summable_norm_choose_mul_pow (α : ℂ) hr0 hr1)
    intervalIntegrable_const
    (Eventually.of_forall fun x _ => by
      have hz : ‖(r : ℂ) * Complex.exp (↑(2 * x) * I)‖ < 1 := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0,
          Complex.norm_exp_ofReal_mul_I, mul_one]
        exact hr1
      convert (hasSum_choose_mul_pow (α : ℂ) hz).mul_right
        (Complex.exp (↑(μ * x) * I)) using 1
      funext n
      rw [mul_pow, ← Complex.exp_nat_mul, mul_assoc, mul_assoc, mul_assoc, ← Complex.exp_add]
      congr 3
      push_cast
      ring)
  convert key using 1
  funext n
  rw [intervalIntegral.integral_const_mul, integral_exp_shifted_freq n hμ]
  push_cast
  rw [neg_pow]
  ring

theorem integral_pow_mul_rpow (n : ℕ) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ∫ u in (0 : ℝ)..1, u ^ n * u ^ (s - 1) = 1 / (n + s) := by
  have hne : (n : ℝ) + (s - 1) ≠ 0 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp; linarith
    · have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
  have hcongr : ∀ u ∈ Set.uIcc (0 : ℝ) 1, u ^ n * u ^ (s - 1) = u ^ ((n : ℝ) + (s - 1)) := by
    intro u hu
    rw [Set.uIcc_of_le zero_le_one] at hu
    rw [Real.rpow_add' hu.1 hne, Real.rpow_natCast]
  rw [intervalIntegral.integral_congr hcongr,
    integral_rpow (Or.inl (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]))]
  rw [show (n : ℝ) + (s - 1) + 1 = n + s by ring, Real.one_rpow,
    Real.zero_rpow (by positivity)]
  simp

/-- Termwise integration of the binomial series of `(1 - r u)^α` against `u^(s-1)`. -/
theorem hasSum_integral_one_sub_mul (α : ℝ) {s r : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hr0 : 0 ≤ r)
    (hr1 : r < 1) :
    HasSum (fun n : ℕ => Ring.choose α n * (-r) ^ n / (n + s))
      (∫ u in (0 : ℝ)..1, (1 - r * u) ^ α * u ^ (s - 1)) := by
  have hsum : Summable fun n : ℕ => |Ring.choose α n| * r ^ n := by
    have := summable_norm_choose_mul_pow (α : ℂ) hr0 hr1
    simpa [← Complex.ofReal_choose, Complex.norm_real] using this
  have key := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := volume) (a := 0) (b := 1)
    (F := fun (n : ℕ) (u : ℝ) => Ring.choose α n * (-r) ^ n * (u ^ n * u ^ (s - 1)))
    (f := fun u : ℝ => (1 - r * u) ^ α * u ^ (s - 1))
    (fun n u => |Ring.choose α n| * r ^ n * u ^ (s - 1))
    (fun n => (by fun_prop : Measurable fun u : ℝ =>
      Ring.choose α n * (-r) ^ n * (u ^ n * u ^ (s - 1))).aestronglyMeasurable)
    (fun n => Eventually.of_forall fun u hu => by
      rw [Set.uIoc_of_le zero_le_one] at hu
      have hu0 : 0 ≤ u := hu.1.le
      rw [norm_mul, norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_pow, abs_neg, abs_of_nonneg hr0, abs_of_nonneg (pow_nonneg hu0 n),
        abs_of_nonneg (Real.rpow_nonneg hu0 _)]
      have h1 : u ^ n ≤ 1 := pow_le_one₀ hu0 hu.2
      have h2 : 0 ≤ |Ring.choose α n| * r ^ n := by positivity
      have h3 : 0 ≤ u ^ (s - 1) := Real.rpow_nonneg hu0 _
      calc |Ring.choose α n| * r ^ n * (u ^ n * u ^ (s - 1))
          ≤ |Ring.choose α n| * r ^ n * (1 * u ^ (s - 1)) := by gcongr
        _ = _ := by ring)
    (Eventually.of_forall fun u _ => hsum.mul_right _)
    (by
      simp_rw [tsum_mul_right]
      exact (intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul _)
    (Eventually.of_forall fun u hu => by
      rw [Set.uIoc_of_le zero_le_one] at hu
      have hx : |-(r * u)| < 1 := by
        rw [abs_neg, abs_of_nonneg (mul_nonneg hr0 hu.1.le)]
        calc r * u ≤ r * 1 := by gcongr; exact hu.2
          _ < 1 := by linarith
      convert (hasSum_choose_mul_pow_real α hx).mul_right (u ^ (s - 1)) using 1
      funext n
      ring)
  convert key using 1
  funext n
  rw [intervalIntegral.integral_const_mul, integral_pow_mul_rpow n hs0 hs1]
  ring



theorem norm_one_add_mul_exp_bounds {r x : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    Real.cos x ≤ ‖1 + (r : ℂ) * Complex.exp (↑(2 * x) * I)‖ ∧
      ‖1 + (r : ℂ) * Complex.exp (↑(2 * x) * I)‖ ≤ 2 := by
  constructor
  · rcases lt_or_ge (Real.cos x) 0 with hc | hc
    · exact hc.le.trans (norm_nonneg _)
    rw [← pow_le_pow_iff_left₀ hc (norm_nonneg _) two_ne_zero, Complex.sq_norm,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.normSq_apply]
    simp only [add_re, one_re, mul_re, ofReal_re, ofReal_im, add_im, one_im, mul_im, I_re, I_im]
    have h2c : Real.cos (2 * x) = 2 * Real.cos x ^ 2 - 1 := Real.cos_two_mul x
    have hs : Real.sin (2 * x) ^ 2 = 1 - Real.cos (2 * x) ^ 2 := by
      rw [← Real.sin_sq_add_cos_sq (2 * x)]; ring
    have hc1 : Real.cos x ^ 2 ≤ 1 := by
      rw [← Real.sin_sq_add_cos_sq x]; nlinarith [sq_nonneg (Real.sin x)]
    nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hr1), mul_nonneg (mul_nonneg hr0 hr0)
      (sub_nonneg.mpr hc1), sq_nonneg (1 - r), mul_nonneg (sq_nonneg (1 - r)) (sub_nonneg.mpr hc1)]
  · calc ‖1 + (r : ℂ) * Complex.exp (↑(2 * x) * I)‖
        ≤ ‖(1 : ℂ)‖ + ‖(r : ℂ) * Complex.exp (↑(2 * x) * I)‖ := norm_add_le _ _
      _ = 1 + r := by
        rw [norm_one, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0,
          Complex.norm_exp_ofReal_mul_I, mul_one]
      _ ≤ 2 := by linarith



theorem mem_Ioo_of_mem_uIoc {x : ℝ} (hx : x ≠ π / 2) (hxI : x ∈ Set.uIoc (-(π / 2)) (π / 2)) :
    x ∈ Set.Ioo (-(π / 2)) (π / 2) := by
  rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at hxI
  exact ⟨hxI.1, lt_of_le_of_ne hxI.2 hx⟩

/-- Abel limit `r → 1⁻` of the integral of `(1 + r e^{2ix})^α e^{iμx}`. -/
theorem tendsto_integral_one_add_mul_exp {α : ℝ} (hα : -1 < α) (μ : ℝ) :
    Tendsto (fun r : ℝ => ∫ x in (-(π / 2))..(π / 2),
        (1 + (r : ℂ) * Complex.exp (↑(2 * x) * I)) ^ (α : ℂ) * Complex.exp (↑(μ * x) * I))
      (𝓝[<] 1)
      (𝓝 (∫ x in (-(π / 2))..(π / 2),
        (1 + Complex.exp (↑(2 * x) * I)) ^ (α : ℂ) * Complex.exp (↑(μ * x) * I))) := by
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun x => (2 : ℝ) ^ α + Real.cos x ^ α)
  · exact Eventually.of_forall fun r => (by fun_prop : Measurable fun x : ℝ =>
      (1 + (r : ℂ) * Complex.exp (↑(2 * x) * I)) ^ (α : ℂ) *
        Complex.exp (↑(μ * x) * I)).aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
    filter_upwards [ae_ne_real (π / 2)] with x hx hxI
    have hxo := mem_Ioo_of_mem_uIoc hx hxI
    have hcpos : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo hxo
    obtain ⟨hlo, hhi⟩ := norm_one_add_mul_exp_bounds (x := x) hr.1.le hr.2.le
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_cpow_real]
    have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ α := by positivity
    have hc : (0 : ℝ) ≤ Real.cos x ^ α := Real.rpow_nonneg hcpos.le _
    rcases le_or_gt 0 α with hα0 | hα0
    · have := Real.rpow_le_rpow (norm_nonneg _) hhi hα0
      linarith
    · have := Real.rpow_le_rpow_of_nonpos hcpos hlo hα0.le
      linarith
  · exact intervalIntegrable_const.add (intervalIntegrable_cos_rpow' hα)
  · filter_upwards [ae_ne_real (π / 2)] with x hx hxI
    have hxo := mem_Ioo_of_mem_uIoc hx hxI
    have hcpos : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo hxo
    have hslit : 1 + ((1 : ℝ) : ℂ) * Complex.exp (↑(2 * x) * I) ∈ slitPlane := by
      refine Or.inl ?_
      rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      simp only [add_re, one_re, mul_re, ofReal_re, ofReal_im, I_re, I_im]
      rw [Real.cos_two_mul]
      nlinarith
    have hcont : ContinuousAt (fun r : ℝ =>
        (1 + (r : ℂ) * Complex.exp (↑(2 * x) * I)) ^ (α : ℂ) *
          Complex.exp (↑(μ * x) * I)) 1 :=
      (ContinuousAt.comp (f := fun r : ℝ => 1 + (r : ℂ) * Complex.exp (↑(2 * x) * I))
        (continuousAt_cpow_const (b := (α : ℂ)) hslit) (by fun_prop)).mul continuousAt_const
    have := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio (1 : ℝ)))
    simpa using this

/-- The Beta integrand is integrable on `[0, 1]`; its integral is a positive Gamma value. -/
theorem intervalIntegrable_beta_integrand {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    IntervalIntegrable (fun u : ℝ => u ^ (p - 1) * (1 - u) ^ (q - 1)) volume 0 1 := by
  have h := real_betaIntegral hp hq
  by_contra hni
  rw [intervalIntegral.integral_undef hni] at h
  have := Real.Gamma_pos_of_pos hp
  have := Real.Gamma_pos_of_pos hq
  have := Real.Gamma_pos_of_pos (add_pos hp hq)
  have : 0 < Real.Gamma p * Real.Gamma q / Real.Gamma (p + q) := by positivity
  linarith

/-- Abel limit `r → 1⁻` of `∫₀¹ (1 - r u)^α u^(s-1) du`. -/
theorem tendsto_integral_one_sub_mul {α s : ℝ} (hα : -1 < α) (hs0 : 0 < s) :
    Tendsto (fun r : ℝ => ∫ u in (0 : ℝ)..1, (1 - r * u) ^ α * u ^ (s - 1)) (𝓝[<] 1)
      (𝓝 (∫ u in (0 : ℝ)..1, (1 - u) ^ α * u ^ (s - 1))) := by
  have hB : IntervalIntegrable (fun u : ℝ => u ^ (s - 1) * (1 - u) ^ α) volume 0 1 := by
    have := intervalIntegrable_beta_integrand hs0 (show 0 < α + 1 by linarith)
    simpa only [add_sub_cancel_right] using this
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun u => u ^ (s - 1) + u ^ (s - 1) * (1 - u) ^ α)
  · exact Eventually.of_forall fun r => (by fun_prop : Measurable fun u : ℝ =>
      (1 - r * u) ^ α * u ^ (s - 1)).aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
    filter_upwards [ae_ne_real 1] with u hu huI
    rw [Set.uIoc_of_le zero_le_one] at huI
    have hu1 : u < 1 := lt_of_le_of_ne huI.2 hu
    have hu0 : 0 < u := huI.1
    have hlo : 1 - u ≤ 1 - r * u := by nlinarith [hr.2]
    have hpos : 0 < 1 - u := by linarith
    have hup : 1 - r * u ≤ 1 := by nlinarith [hr.1]
    have hp : 0 ≤ u ^ (s - 1) := Real.rpow_nonneg hu0.le _
    have hq : 0 ≤ (1 - u) ^ α := Real.rpow_nonneg hpos.le _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (by linarith) _) hp)]
    rcases le_or_gt 0 α with hα0 | hα0
    · have : (1 - r * u) ^ α ≤ 1 := Real.rpow_le_one (by linarith) hup hα0
      nlinarith [mul_nonneg hp hq]
    · have : (1 - r * u) ^ α ≤ (1 - u) ^ α := Real.rpow_le_rpow_of_nonpos hpos hlo hα0.le
      nlinarith [mul_nonneg hp hq]
  · exact (intervalIntegral.intervalIntegrable_rpow' (by linarith)).add hB
  · filter_upwards [ae_ne_real 1] with u hu huI
    rw [Set.uIoc_of_le zero_le_one] at huI
    have hu1 : u < 1 := lt_of_le_of_ne huI.2 hu
    have hcont : ContinuousAt (fun r : ℝ => (1 - r * u) ^ α * u ^ (s - 1)) 1 := by
      refine ContinuousAt.mul ?_ continuousAt_const
      exact ContinuousAt.rpow_const (by fun_prop) (Or.inl (by simp; linarith))
    have := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio (1 : ℝ)))
    simpa using this

/-- `(1 + e^{2ix})^α e^{iμx} = (2 cos x)^α e^{i(α+μ)x}` for `|x| < π/2`. -/
theorem one_add_exp_cpow_mul_exp {α μ x : ℝ} (hx : x ∈ Set.Ioo (-(π / 2)) (π / 2)) :
    (1 + Complex.exp (↑(2 * x) * I)) ^ (α : ℂ) * Complex.exp (↑(μ * x) * I) =
      (((2 : ℝ) ^ α * Real.cos x ^ α : ℝ) : ℂ) * Complex.exp (↑((α + μ) * x) * I) := by
  have hc : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo hx
  have hpi := Real.pi_pos
  have hfac : 1 + Complex.exp (↑(2 * x) * I) =
      ((2 * Real.cos x : ℝ) : ℂ) * Complex.exp (↑x * I) := by
    rw [Complex.exp_mul_I, Complex.exp_mul_I]
    push_cast
    rw [Complex.cos_two_mul, Complex.sin_two_mul]
    ring
  have hlog : Complex.log (((2 * Real.cos x : ℝ) : ℂ) * Complex.exp (↑x * I)) =
      (Real.log (2 * Real.cos x) : ℂ) + ↑x * I := by
    rw [Complex.log_ofReal_mul (by positivity) (Complex.exp_ne_zero _), Complex.log_exp]
    · simp; linarith [hx.1]
    · simp; linarith [hx.2]
  have hne : ((2 * Real.cos x : ℝ) : ℂ) * Complex.exp (↑x * I) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast (by positivity : (0 : ℝ) < 2 * Real.cos x).ne')
      (Complex.exp_ne_zero _)
  rw [hfac, Complex.cpow_def_of_ne_zero hne, hlog, ← Real.mul_rpow (by norm_num) hc.le,
    Real.rpow_def_of_pos (by positivity), Complex.ofReal_exp, ← Complex.exp_add,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- DLMF 5.12.5 in the range `a - 1 < b < a + 1`, by Abel summation of the binomial series
of `(1 + e^{2ix})^{a-1}`. -/
theorem integral_cos_rpow_mul_cos_of_lt {a b : ℝ} (ha : 0 < a) (h1 : a - 1 < b) (h2 : b < a + 1) :
    ∫ t in (0 : ℝ)..(π / 2), Real.cos t ^ (a - 1) * Real.cos (b * t) =
      π * Real.Gamma a /
        ((2 : ℝ) ^ a * (Real.Gamma ((a + b + 1) / 2) * Real.Gamma ((a - b + 1) / 2))) := by
  set α := a - 1 with hαdef
  set μ := b - a + 1 with hμdef
  set s := μ / 2 with hsdef
  have hα : -1 < α := by linarith
  have hμ : 0 < μ := by linarith
  have hs0 : 0 < s := by positivity
  have hs1 : s < 1 := by rw [hsdef]; linarith
  -- The Abel-regularized identity `L(r) = sin(πs) R(r)` and its limit `r → 1⁻`.
  have hL := tendsto_integral_one_add_mul_exp hα μ
  have hR := ((Complex.continuous_ofReal.tendsto _).comp
    ((tendsto_integral_one_sub_mul hα hs0).const_mul (Real.sin (π * s))))
  have heq : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), (∫ x in (-(π / 2))..(π / 2),
      (1 + (r : ℂ) * Complex.exp (↑(2 * x) * I)) ^ (α : ℂ) * Complex.exp (↑(μ * x) * I)) =
      (fun r : ℝ => ((Real.sin (π * s) *
        ∫ u in (0 : ℝ)..1, (1 - r * u) ^ α * u ^ (s - 1) : ℝ) : ℂ)) r := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
    have hA := hasSum_integral_one_add_mul_exp α hμ hr.1.le hr.2
    have hB := Complex.hasSum_ofReal.mpr
      ((hasSum_integral_one_sub_mul α hs0 hs1 hr.1.le hr.2).mul_left (Real.sin (π * s)))
    exact hA.unique hB
  have hlim := tendsto_nhds_unique (hL.congr' heq) hR
  -- Identify the two limits.
  have hbeta : ∫ u in (0 : ℝ)..1, (1 - u) ^ α * u ^ (s - 1) =
      Real.Gamma s * Real.Gamma a / Real.Gamma (s + a) := by
    rw [← real_betaIntegral hs0 ha]
    refine intervalIntegral.integral_congr fun u _ => ?_
    simp only [hαdef]
    ring
  have hleft : (∫ x in (-(π / 2))..(π / 2),
      (1 + Complex.exp (↑(2 * x) * I)) ^ (α : ℂ) * Complex.exp (↑(μ * x) * I)) =
      (((2 : ℝ) ^ α : ℝ) : ℂ) *
        ↑(2 * ∫ t in (0 : ℝ)..(π / 2), Real.cos t ^ α * Real.cos (b * t)) := by
    rw [← integral_cos_rpow_mul_exp hα b, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [ae_ne_real (π / 2)] with x hx hxI
    rw [one_add_exp_cpow_mul_exp (mem_Ioo_of_mem_uIoc hx hxI),
      show α + μ = b by rw [hαdef, hμdef]; ring]
    push_cast
    ring
  rw [hleft, hbeta] at hlim
  have hreal : (2 : ℝ) ^ α *
      (2 * ∫ t in (0 : ℝ)..(π / 2), Real.cos t ^ α * Real.cos (b * t)) =
      Real.sin (π * s) * (Real.Gamma s * Real.Gamma a / Real.Gamma (s + a)) := by
    exact_mod_cast hlim
  -- Euler's reflection formula.
  have hsin : 0 < Real.sin (π * s) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  have hrefl := Real.Gamma_mul_Gamma_one_sub s
  have hG1 : 0 < Real.Gamma (1 - s) := Real.Gamma_pos_of_pos (by linarith)
  have hGs : 0 < Real.Gamma s := Real.Gamma_pos_of_pos hs0
  have hGsa : 0 < Real.Gamma (s + a) := Real.Gamma_pos_of_pos (by linarith)
  have h2a : (2 : ℝ) ^ a = 2 ^ α * 2 := by
    rw [hαdef, Real.rpow_sub (by norm_num), Real.rpow_one]
    field_simp
  have hp : (a + b + 1) / 2 = s + a := by rw [hsdef, hμdef]; ring
  have hq : (a - b + 1) / 2 = 1 - s := by rw [hsdef, hμdef]; ring
  rw [hp, hq, h2a]
  have h2α : 0 < (2 : ℝ) ^ α := by positivity
  field_simp
  rw [eq_div_iff hsin.ne'] at hrefl
  have h3 : (2 : ℝ) ^ α * (2 * ∫ t in (0 : ℝ)..(π / 2), Real.cos t ^ α * Real.cos (b * t)) *
      Real.Gamma (s + a) = Real.sin (π * s) * Real.Gamma s * Real.Gamma a := by
    rw [hreal]
    field_simp
  linear_combination Real.Gamma (1 - s) * h3 + Real.Gamma a * hrefl

/-- Integration by parts of `d/dt (cos^(a-1) t · sin (b t))`:
`(a - 1 + b) K(a, b) = (a - 1) K(a - 1, b - 1)`. -/
theorem integral_cos_rpow_mul_cos_shift {a : ℝ} (ha : 1 < a) (b : ℝ) :
    (a - 1 + b) * ∫ t in (0 : ℝ)..(π / 2), Real.cos t ^ (a - 1) * Real.cos (b * t) =
      (a - 1) * ∫ t in (0 : ℝ)..(π / 2), Real.cos t ^ (a - 1 - 1) * Real.cos ((b - 1) * t) := by
  have hp : 0 < a - 1 := by linarith
  have hpi := Real.pi_pos
  have hsub : Set.uIcc 0 (π / 2) ⊆ Set.Icc (-(π / 2)) (π / 2) := by
    rw [Set.uIcc_of_le (by linarith)]
    exact Set.Icc_subset_Icc (by linarith) le_rfl
  have hA := intervalIntegrable_cos_rpow_mul (β := a - 1 - 1) (by linarith)
    (g := fun t => Real.cos ((b - 1) * t)) (by fun_prop) hsub
  have hB := intervalIntegrable_cos_rpow_mul (β := a - 1) (by linarith)
    (g := fun t => Real.cos (b * t)) (by fun_prop) hsub
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by linarith : (0 : ℝ) ≤ π / 2)
    (f := fun t => Real.cos t ^ (a - 1) * Real.sin (b * t))
    (f' := fun t => -(a - 1) * (Real.cos t ^ (a - 1 - 1) * Real.cos ((b - 1) * t)) +
      (a - 1 + b) * (Real.cos t ^ (a - 1) * Real.cos (b * t)))
    ((Real.continuous_cos.rpow_const fun _ => Or.inr hp.le).mul
      (by fun_prop : Continuous fun t : ℝ => Real.sin (b * t))).continuousOn
    (fun t ht => by
      have hc : 0 < Real.cos t :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1], ht.2⟩
      have h1 := (Real.hasDerivAt_cos t).rpow_const (p := a - 1) (Or.inl hc.ne')
      have h2 := (Real.hasDerivAt_sin (b * t)).comp t ((hasDerivAt_id t).const_mul b)
      refine (h1.mul h2).congr_deriv ?_
      have hcp : Real.cos t ^ (a - 1) = Real.cos t ^ (a - 1 - 1) * Real.cos t := by
        rw [← Real.rpow_add_one hc.ne', sub_add_cancel]
      rw [hcp, show (b - 1) * t = b * t - t by ring, Real.cos_sub]
      simp only [Function.comp_apply]
      ring)
    ((hA.const_mul _).add (hB.const_mul _))
  rw [intervalIntegral.integral_add (hA.const_mul _) (hB.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hftc
  simp only [Real.cos_pi_div_two, Real.zero_rpow hp.ne', zero_mul, Real.cos_zero,
    Real.one_rpow, mul_zero, Real.sin_zero, sub_zero] at hftc
  linarith

theorem integral_cos_rpow_mul_cos_neg (a b : ℝ) :
    ∫ t in (0 : ℝ)..(π / 2), Real.cos t ^ (a - 1) * Real.cos (-b * t) =
      ∫ t in (0 : ℝ)..(π / 2), Real.cos t ^ (a - 1) * Real.cos (b * t) := by
  simp only [neg_mul, Real.cos_neg]

/-- DLMF 5.12.5 with the right-hand side written as `π Γ(a) / (2^a Γ(p) Γ(q))`. -/
theorem integral_cos_rpow_mul_cos {a b : ℝ} (ha : 0 < a) (hb : |b| < a + 1) :
    ∫ t in (0 : ℝ)..(π / 2), Real.cos t ^ (a - 1) * Real.cos (b * t) =
      π * Real.Gamma a /
        ((2 : ℝ) ^ a * (Real.Gamma ((a + b + 1) / 2) * Real.Gamma ((a - b + 1) / 2))) := by
  suffices H : ∀ n : ℕ, ∀ a b : ℝ, 0 < a → a ≤ n → |b| < a + 1 →
      ∫ t in (0 : ℝ)..(π / 2), Real.cos t ^ (a - 1) * Real.cos (b * t) =
        π * Real.Gamma a /
          ((2 : ℝ) ^ a * (Real.Gamma ((a + b + 1) / 2) * Real.Gamma ((a - b + 1) / 2))) from
    H ⌈a⌉₊ a b ha (Nat.le_ceil a) hb
  intro n
  induction n with
  | zero => intro a b ha han _; norm_num at han; linarith
  | succ n ih =>
    intro a b ha han hb
    wlog hb0 : 0 ≤ b generalizing b with H'
    · have h := H' (-b) (by rwa [abs_neg]) (by linarith)
      rw [integral_cos_rpow_mul_cos_neg] at h
      rw [h, show a + -b + 1 = a - b + 1 by ring, show a - -b + 1 = a + b + 1 by ring,
        mul_comm (Real.Gamma ((a - b + 1) / 2))]
    have hb1 : b < a + 1 := (abs_lt.mp hb).2
    by_cases h : a - 1 < b
    · exact integral_cos_rpow_mul_cos_of_lt ha h hb1
    push Not at h
    rcases eq_or_lt_of_le (show 1 ≤ a by linarith) with h1 | h1
    · subst h1
      have hb' : b = 0 := by linarith
      subst hb'
      norm_num [Real.Gamma_one]
    · have hrec := integral_cos_rpow_mul_cos_shift h1 b
      have hih := ih (a - 1) (b - 1) (by linarith) (by push_cast at han; linarith)
        (abs_lt.mpr ⟨by linarith, by linarith⟩)
      rw [hih] at hrec
      have hpos : 0 < a - 1 + b := by linarith
      have e1 : a - 1 + (b - 1) + 1 = a + b - 1 := by ring
      have e2 : a - 1 - (b - 1) + 1 = a - b + 1 := by ring
      rw [e1, e2] at hrec
      have hGa : Real.Gamma a = (a - 1) * Real.Gamma (a - 1) := by
        rw [← Real.Gamma_add_one (by linarith : a - 1 ≠ 0)]; ring_nf
      have hGp : Real.Gamma ((a + b + 1) / 2) =
          (a + b - 1) / 2 * Real.Gamma ((a + b - 1) / 2) := by
        rw [← Real.Gamma_add_one (by linarith : (a + b - 1) / 2 ≠ 0)]; ring_nf
      have h2a : (2 : ℝ) ^ a = 2 * 2 ^ (a - 1) := by
        rw [Real.rpow_sub (by norm_num), Real.rpow_one]
        field_simp
      have g1 : 0 < Real.Gamma (a - 1) := Real.Gamma_pos_of_pos (by linarith)
      have g2 : 0 < Real.Gamma ((a + b - 1) / 2) := Real.Gamma_pos_of_pos (by linarith)
      have g3 : 0 < Real.Gamma ((a - b + 1) / 2) := Real.Gamma_pos_of_pos (by linarith)
      have h2 : 0 < (2 : ℝ) ^ (a - 1) := by positivity
      rw [hGa, hGp, h2a]
      field_simp at hrec ⊢
      rw [eq_div_iff (by linarith)]
      linear_combination hrec

end CosineBeta

@[dlmf 5.12.E5]
theorem beta_cos_cos {a b : ℝ} (ha : 0 < a) (hba : |b| < a + 1) :
    ∫ t : ℝ in (0 : ℝ)..(π / 2), Real.cos t ^ (a - 1) * Real.cos (b * t) =
      π / (2 : ℝ) ^ a /
        (a * (Real.Gamma ((a + b + 1) / 2) * Real.Gamma ((a - b + 1) / 2) /
          Real.Gamma (a + 1))) := by
  obtain ⟨hb1, hb2⟩ := abs_lt.mp hba
  rw [integral_cos_rpow_mul_cos ha hba, Real.Gamma_add_one ha.ne']
  have g1 : 0 < Real.Gamma a := Real.Gamma_pos_of_pos ha
  have g2 : 0 < Real.Gamma ((a + b + 1) / 2) := Real.Gamma_pos_of_pos (by linarith)
  have g3 : 0 < Real.Gamma ((a - b + 1) / 2) := Real.Gamma_pos_of_pos (by linarith)
  have h2 : 0 < (2 : ℝ) ^ a := by positivity
  field_simp

@[dlmf 5.12.E6]
theorem beta_sin_exp {a b : ℝ} (ha : 0 < a) (hba : |b| < a + 1) :
    ∫ t : ℝ in (0 : ℝ)..π, (Real.sin t : ℂ) ^ (a - 1 : ℂ) * Complex.exp (I * b * t) =
      (π : ℂ) / (2 : ℂ) ^ (a - 1 : ℂ) * Complex.exp (I * π * b / 2) /
        ((a : ℂ) * betaIntegral ((a + b + 1 : ℂ) / 2) ((a - b + 1 : ℂ) / 2)) := by
  obtain ⟨hb1, hb2⟩ := abs_lt.mp hba
  have hpi := Real.pi_pos
  -- Shift `t = x + π/2`.
  have hshift : ∫ t : ℝ in (0 : ℝ)..π, (Real.sin t : ℂ) ^ (a - 1 : ℂ) * Complex.exp (I * b * t) =
      ∫ x : ℝ in (-(π / 2))..(π / 2), (Real.sin (x + π / 2) : ℂ) ^ (a - 1 : ℂ) *
        Complex.exp (I * b * ↑(x + π / 2)) := by
    rw [intervalIntegral.integral_comp_add_right
      (fun t : ℝ => (Real.sin t : ℂ) ^ (a - 1 : ℂ) * Complex.exp (I * b * t))]
    congr 1 <;> ring
  have hcongr : ∀ x ∈ Set.uIcc (-(π / 2)) (π / 2),
      (Real.sin (x + π / 2) : ℂ) ^ (a - 1 : ℂ) * Complex.exp (I * b * ↑(x + π / 2)) =
        Complex.exp (I * π * b / 2) *
          (((Real.cos x ^ (a - 1) : ℝ) : ℂ) * Complex.exp (↑(b * x) * I)) := by
    intro x hx
    rw [Set.uIcc_of_le (by linarith)] at hx
    have hc : 0 ≤ Real.cos x := Real.cos_nonneg_of_mem_Icc hx
    rw [Real.sin_add_pi_div_two, Complex.ofReal_cpow hc,
      show ((a : ℂ) - 1) = ((a - 1 : ℝ) : ℂ) by push_cast; ring,
      mul_left_comm (Complex.exp _) _ _, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hshift, intervalIntegral.integral_congr hcongr, intervalIntegral.integral_const_mul,
    integral_cos_rpow_mul_exp (by linarith) b, integral_cos_rpow_mul_cos ha hba]
  -- Evaluate the Beta integral.
  have hbeta := Complex.Gamma_mul_Gamma_eq_betaIntegral
    (s := ((a + b + 1 : ℂ) / 2)) (t := ((a - b + 1 : ℂ) / 2))
    (by simp; linarith) (by simp; linarith)
  have e1 : ((a + b + 1 : ℂ) / 2) = (((a + b + 1) / 2 : ℝ) : ℂ) := by push_cast; ring
  have e2 : ((a - b + 1 : ℂ) / 2) = (((a - b + 1) / 2 : ℝ) : ℂ) := by push_cast; ring
  have e3 : ((a + b + 1 : ℂ) / 2) + ((a - b + 1 : ℂ) / 2) = ((a + 1 : ℝ) : ℂ) := by
    push_cast; ring
  rw [e3] at hbeta
  have g0 : 0 < Real.Gamma a := Real.Gamma_pos_of_pos ha
  have g1 : 0 < Real.Gamma ((a + b + 1) / 2) := Real.Gamma_pos_of_pos (by linarith)
  have g2 : 0 < Real.Gamma ((a - b + 1) / 2) := Real.Gamma_pos_of_pos (by linarith)
  have g3 : 0 < Real.Gamma (a + 1) := Real.Gamma_pos_of_pos (by linarith)
  have hB : betaIntegral ((a + b + 1 : ℂ) / 2) ((a - b + 1 : ℂ) / 2) =
      ((Real.Gamma ((a + b + 1) / 2) * Real.Gamma ((a - b + 1) / 2) / Real.Gamma (a + 1) : ℝ)
        : ℂ) := by
    have hne : Complex.Gamma ((a + 1 : ℝ) : ℂ) ≠ 0 := by
      rw [Complex.Gamma_ofReal]; exact_mod_cast g3.ne'
    have hB' : betaIntegral ((a + b + 1 : ℂ) / 2) ((a - b + 1 : ℂ) / 2) =
        Complex.Gamma ((a + b + 1 : ℂ) / 2) * Complex.Gamma ((a - b + 1 : ℂ) / 2) /
          Complex.Gamma ((a + 1 : ℝ) : ℂ) := by
      rw [hbeta]; field_simp
    rw [hB', e1, e2, Complex.Gamma_ofReal, Complex.Gamma_ofReal, Complex.Gamma_ofReal]
    push_cast
    ring
  have h2 : (2 : ℂ) ^ (a - 1 : ℂ) = (((2 : ℝ) ^ (a - 1) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (by norm_num)]
    push_cast
    ring_nf
  rw [hB, h2, Real.Gamma_add_one ha.ne']
  have h2a : (2 : ℝ) ^ a = 2 * 2 ^ (a - 1) := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_one]
    field_simp
  rw [h2a]
  have h2p : 0 < (2 : ℝ) ^ (a - 1) := by positivity
  have hE : Complex.exp (I * π * b / 2) ≠ 0 := Complex.exp_ne_zero _
  have c0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have c1 : ((Real.Gamma a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast g0.ne'
  have c2 : ((Real.Gamma ((a + b + 1) / 2) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast g1.ne'
  have c3 : ((Real.Gamma ((a - b + 1) / 2) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast g2.ne'
  have c4 : (((2 : ℝ) ^ (a - 1) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h2p.ne'
  push_cast
  field_simp

/-- The real form of `beta_on_Ioi`, together with integrability of the integrand. -/
theorem real_beta_on_Ioi {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    IntegrableOn (fun u : ℝ => u ^ (p - 1) / (1 + u) ^ (p + q)) (Set.Ioi 0) ∧
      ∫ u : ℝ in Set.Ioi 0, u ^ (p - 1) / (1 + u) ^ (p + q) =
        Real.Gamma p * Real.Gamma q / Real.Gamma (p + q) := by
  have hval : ∫ u : ℝ in Set.Ioi 0, u ^ (p - 1) / (1 + u) ^ (p + q) =
      Real.Gamma p * Real.Gamma q / Real.Gamma (p + q) := by
    apply Complex.ofReal_injective
    have hG := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := (p : ℂ)) (t := (q : ℂ))
      (by simpa using hp) (by simpa using hq)
    have hne : Complex.Gamma ((p : ℂ) + q) ≠ 0 :=
      Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
    push_cast
    rw [← Complex.Gamma_ofReal, ← Complex.Gamma_ofReal, ← Complex.Gamma_ofReal,
      Complex.ofReal_add, eq_div_iff hne, hG, ← integral_complex_ofReal, mul_comm,
      ← beta_on_Ioi (a := (p : ℂ)) (b := (q : ℂ)) (by simpa using hp) (by simpa using hq)]
    congr 1
    refine setIntegral_congr_fun (measurableSet_Ioi (a := (0 : ℝ))) fun u hu => ?_
    have hu0 : (0 : ℝ) ≤ u := (Set.mem_Ioi.mp hu).le
    rw [Complex.ofReal_div, Complex.ofReal_cpow hu0, Complex.ofReal_cpow (by linarith)]
    push_cast
    rfl
  refine ⟨?_, hval⟩
  by_contra h
  rw [integral_undef h] at hval
  have := Real.Gamma_pos_of_pos hp
  have := Real.Gamma_pos_of_pos hq
  have := Real.Gamma_pos_of_pos (add_pos hp hq)
  have : 0 < Real.Gamma p * Real.Gamma q / Real.Gamma (p + q) := by positivity
  linarith

/-- `cosh t ^ (2a)` written with exponentials, for the substitution `u = exp (2t)`. -/
theorem cosh_rpow_eq_exp_mul (a t : ℝ) :
    Real.cosh t ^ (2 * a) =
      Real.exp (-(2 * a * t)) * (1 + Real.exp (2 * t)) ^ (2 * a) / (2 : ℝ) ^ (2 * a) := by
  have h : Real.cosh t = Real.exp (-t) * (1 + Real.exp (2 * t)) / 2 := by
    rw [Real.cosh_eq, mul_add, ← Real.exp_add]
    ring_nf
  rw [h, Real.div_rpow (by positivity) (by norm_num), Real.mul_rpow (by positivity)
    (by positivity), ← Real.exp_mul]
  ring_nf

/-- `∫ exp(2ct) / cosh(t)^(2a) dt` over `ℝ`, by the substitution `u = exp (2t)` in
`real_beta_on_Ioi`. -/
theorem integral_exp_div_cosh_rpow {a c : ℝ} (hc : |c| < a) :
    Integrable (fun t : ℝ => Real.exp (2 * c * t) / Real.cosh t ^ (2 * a)) ∧
      ∫ t : ℝ, Real.exp (2 * c * t) / Real.cosh t ^ (2 * a) =
        (2 : ℝ) ^ (2 * a - 1) *
          (Real.Gamma (a + c) * Real.Gamma (a - c) / Real.Gamma (2 * a)) := by
  obtain ⟨h1, h2⟩ := abs_lt.mp hc
  -- The substitution `u = exp (2 t)` maps `ℝ` onto `(0, ∞)`.
  set f : ℝ → ℝ := fun t => Real.exp (2 * t) with hf
  set f' : ℝ → ℝ := fun t => 2 * Real.exp (2 * t) with hf'
  have hderiv : ∀ t ∈ (Set.univ : Set ℝ), HasDerivWithinAt f (f' t) Set.univ t := by
    intro t _
    refine HasDerivAt.hasDerivWithinAt ?_
    have h := ((hasDerivAt_id t).const_mul (2 : ℝ)).exp
    simp only [id, mul_one] at h
    exact h.congr_deriv (mul_comm _ _)
  have hinj : Set.InjOn f Set.univ := fun x _ y _ hxy => by
    simpa using Real.exp_injective hxy
  have himage : f '' Set.univ = Set.Ioi 0 := by
    rw [Set.image_univ]
    ext u
    refine ⟨fun ⟨t, ht⟩ => ht ▸ Real.exp_pos _, fun hu => ⟨Real.log u / 2, ?_⟩⟩
    simp only [hf]
    rw [mul_div_cancel₀ _ two_ne_zero, Real.exp_log hu]
  set g : ℝ → ℝ := fun u => u ^ (a + c - 1) / (1 + u) ^ (a + c + (a - c))
  obtain ⟨hint, hval⟩ := real_beta_on_Ioi (p := a + c) (q := a - c) (by linarith) (by linarith)
  have key := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hderiv hinj g
  have keyI := integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ hderiv hinj g
  rw [himage] at key keyI
  have hpt (t : ℝ) : Real.exp (2 * c * t) / Real.cosh t ^ (2 * a) =
      (2 : ℝ) ^ (2 * a - 1) * (|f' t| • g (f t)) := by
    simp only [hf, hf', g, smul_eq_mul]
    rw [abs_of_pos (by positivity), cosh_rpow_eq_exp_mul, ← Real.exp_mul,
      show a + c + (a - c) = 2 * a by ring, Real.rpow_sub (by norm_num), Real.rpow_one]
    field_simp
    rw [← Real.exp_add, ← Real.exp_add]
    ring_nf
  simp_rw [hpt]
  refine ⟨?_, ?_⟩
  · rw [← integrableOn_univ]
    exact (keyI.mp hint).const_mul _
  · rw [MeasureTheory.integral_const_mul, ← setIntegral_univ, ← key, hval, show a + c + (a - c) = 2 * a by ring]

@[dlmf 5.12.E7]
theorem beta_cosh {a b : ℝ} (ha : |b| < a) :
    ∫ t : ℝ in Set.Ioi 0, Real.cosh (2 * b * t) / Real.cosh t ^ (2 * a) =
      (4 : ℝ) ^ (a - 1) *
        (Real.Gamma (a + b) * Real.Gamma (a - b) / Real.Gamma (2 * a)) := by
  obtain ⟨hI₁, hv₁⟩ := integral_exp_div_cosh_rpow ha
  obtain ⟨hI₂, hv₂⟩ := integral_exp_div_cosh_rpow (c := -b) (by rwa [abs_neg])
  have heven := integral_comp_abs (f := fun t => Real.cosh (2 * b * t) / Real.cosh t ^ (2 * a))
  have habs (t : ℝ) : Real.cosh (2 * b * |t|) / Real.cosh |t| ^ (2 * a) =
      (1 / 2) * (Real.exp (2 * b * t) / Real.cosh t ^ (2 * a)) +
        (1 / 2) * (Real.exp (2 * -b * t) / Real.cosh t ^ (2 * a)) := by
    rw [Real.cosh_abs]
    rcases abs_choice t with h | h <;> rw [h] <;>
      simp only [Real.cosh_eq] <;> ring_nf
  simp only [habs] at heven
  rw [integral_add (hI₁.const_mul _) (hI₂.const_mul _), MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, hv₁, hv₂, sub_neg_eq_add,
    show a + -b = a - b by ring, mul_comm (Real.Gamma (a - b))] at heven
  have h4 : (4 : ℝ) ^ (a - 1) = (2 : ℝ) ^ (2 * a - 1) / 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num),
      show 2 * (a - 1) = 2 * a - 1 - 1 by ring, Real.rpow_sub_one two_ne_zero]
  rw [h4]
  linear_combination (-1 / 2 : ℝ) * heven

/-! ### Cauchy's vertical Beta integral (DLMF 5.12.8)

For `Re a > 0` and `Re b > 1` the factor `(w + i t)^{-a}` is a Laplace integral and
`(z - i t)^{-b}` is, by Fourier inversion, the Fourier transform of `s^{b-1} e^{-zs}`; Fubini
then gives the Gamma integral of `s^{a+b-2} e^{-(w+z)s}`. Analytic continuation in `b` and the
symmetry `t ↦ -t` extend the identity to `Re (a + b) > 1`. -/

section VerticalBeta

open Set Filter
open scoped Topology FourierTransform


/-- A linear lower bound for `‖w + i t‖` on the right half-plane. -/
theorem vb_norm_lower {w : ℂ} (hw : 0 < w.re) (t : ℝ) :
    w.re / (2 * (1 + ‖w‖)) * (1 + |t|) ≤ ‖w + I * t‖ := by
  have h1 : w.re ≤ ‖w + I * t‖ := by
    have := Complex.re_le_norm (w + I * t)
    simpa using this
  have h2 : |t| - ‖w‖ ≤ ‖w + I * t‖ := by
    have := norm_sub_norm_le (I * (t : ℂ)) (-w)
    rw [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, norm_neg, one_mul,
      sub_neg_eq_add, add_comm] at this
    exact this
  have hw1 : 0 < 1 + ‖w‖ := by positivity
  set c := w.re / (2 * (1 + ‖w‖)) with hc
  have hc0 : 0 ≤ c := by positivity
  have hcw : c * (2 * (1 + ‖w‖)) = w.re := by rw [hc]; field_simp
  have hre : w.re ≤ ‖w‖ := Complex.re_le_norm w
  have hc2 : c ≤ 1 / 2 := by
    rw [hc, div_le_iff₀ (by positivity)]
    linarith
  rcases le_or_gt |t| (2 * ‖w‖ + 1) with ht | ht
  · nlinarith
  · nlinarith [abs_nonneg t]

/-- A linear upper bound for `‖w + i t‖`. -/
theorem vb_norm_upper (w : ℂ) (t : ℝ) : ‖w + I * t‖ ≤ (1 + ‖w‖) * (1 + |t|) := by
  have h := norm_add_le w (I * (t : ℂ))
  rw [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul] at h
  nlinarith [norm_nonneg w, abs_nonneg t]

/-- `‖w + i t‖ ^ (-σ)` is bounded by a multiple of `(1 + |t|) ^ (-σ)`. -/
theorem vb_rpow_le {w : ℂ} (hw : 0 < w.re) (σ : ℝ) (t : ℝ) :
    ‖w + I * t‖ ^ (-σ) ≤
      max ((w.re / (2 * (1 + ‖w‖))) ^ (-σ)) ((1 + ‖w‖) ^ (-σ)) * (1 + |t|) ^ (-σ) := by
  set c₁ := w.re / (2 * (1 + ‖w‖))
  set c₂ := 1 + ‖w‖
  set u := 1 + |t|
  have hu : 0 < u := by positivity
  have hc₁ : 0 < c₁ := by positivity
  have hlo := vb_norm_lower hw t
  have hup := vb_norm_upper w t
  set x := ‖w + I * t‖
  have hx : x = x / u * u := by field_simp
  have hq1 : c₁ ≤ x / u := by rw [le_div_iff₀ hu]; exact hlo
  have hq2 : x / u ≤ c₂ := by rw [div_le_iff₀ hu]; exact hup
  have hq0 : 0 < x / u := lt_of_lt_of_le hc₁ hq1
  rw [hx, Real.mul_rpow hq0.le hu.le]
  gcongr
  rcases le_total 0 (-σ) with hσ | hσ
  · exact (Real.rpow_le_rpow hq0.le hq2 hσ).trans (le_max_right _ _)
  · exact (Real.rpow_le_rpow_of_nonpos hc₁ hq1 hσ).trans (le_max_left _ _)

theorem vb_ne_zero {w : ℂ} (hw : 0 < w.re) (t : ℝ) : w + I * t ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  linarith

theorem vb_sub_eq (z : ℂ) (t : ℝ) : z - I * t = z + I * ((-t : ℝ) : ℂ) := by
  push_cast; ring

/-- The real majorant `‖w + i t‖^{-α} ‖z - i t‖^{-β}` is integrable when `α + β > 1`. -/
theorem vb_integrable_rpow {w z : ℂ} (hw : 0 < w.re) (hz : 0 < z.re) {α β : ℝ}
    (h : 1 < α + β) :
    Integrable (fun t : ℝ => ‖w + I * t‖ ^ (-α) * ‖z - I * t‖ ^ (-β)) := by
  set C₁ := max ((w.re / (2 * (1 + ‖w‖))) ^ (-α)) ((1 + ‖w‖) ^ (-α))
  set C₂ := max ((z.re / (2 * (1 + ‖z‖))) ^ (-β)) ((1 + ‖z‖) ^ (-β))
  have hint : Integrable (fun t : ℝ => (1 + ‖t‖) ^ (-(α + β))) :=
    integrable_one_add_norm (by simp; linarith)
  refine (hint.const_mul (C₁ * C₂)).mono' (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  refine Eventually.of_forall fun t => ?_
  have h1 := vb_rpow_le hw α t
  have h2 := vb_rpow_le hz β (-t)
  rw [← vb_sub_eq, abs_neg] at h2
  have hu : 0 < 1 + |t| := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.norm_eq_abs,
    neg_add, Real.rpow_add hu]
  calc ‖w + I * t‖ ^ (-α) * ‖z - I * t‖ ^ (-β)
      ≤ (C₁ * (1 + |t|) ^ (-α)) * (C₂ * (1 + |t|) ^ (-β)) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = C₁ * C₂ * ((1 + |t|) ^ (-α) * (1 + |t|) ^ (-β)) := by ring

/-- `‖x ^ c‖ ≤ e^{π |Im c| / 2} ‖x‖ ^ {Re c}` on the right half-plane. -/
theorem vb_norm_cpow_le {x : ℂ} (hx : 0 < x.re) (c : ℂ) :
    ‖x ^ c‖ ≤ Real.exp (π / 2 * |c.im|) * ‖x‖ ^ c.re := by
  have hx0 : x ≠ 0 := fun h => by simp [h] at hx
  rw [norm_cpow_of_ne_zero hx0, div_eq_mul_inv, ← Real.exp_neg, mul_comm]
  gcongr
  have harg : |arg x| ≤ π / 2 := abs_arg_le_pi_div_two_iff.mpr hx.le
  have := neg_abs_le (arg x * c.im)
  rw [abs_mul] at this
  nlinarith [abs_nonneg c.im, abs_nonneg (arg x)]

theorem vb_rpow_le_add {x σ σ₁ σ₂ : ℝ} (hx : 0 < x) (h₁ : σ₁ ≤ σ) (h₂ : σ ≤ σ₂) :
    x ^ (-σ) ≤ x ^ (-σ₁) + x ^ (-σ₂) := by
  rcases le_total 1 x with h | h
  · have := Real.rpow_le_rpow_of_exponent_le h (neg_le_neg h₁)
    linarith [Real.rpow_nonneg hx.le (-σ₂)]
  · have := Real.rpow_le_rpow_of_exponent_ge hx h (neg_le_neg h₂)
    linarith [Real.rpow_nonneg hx.le (-σ₁)]

/-- The integrand of Cauchy's vertical Beta integral. -/
def vbF (a b w z : ℂ) (t : ℝ) : ℂ := (w + I * t) ^ (-a) * (z - I * t) ^ (-b)

theorem vb_re_sub {z : ℂ} (hz : 0 < z.re) (t : ℝ) : 0 < (z - I * t).re := by simpa using hz

theorem vb_re_add {w : ℂ} (hw : 0 < w.re) (t : ℝ) : 0 < (w + I * t).re := by simpa using hw

theorem vb_norm_vbF_le {a b w z : ℂ} (hw : 0 < w.re) (hz : 0 < z.re) (t : ℝ) :
    ‖vbF a b w z t‖ ≤ Real.exp (π / 2 * |a.im|) * Real.exp (π / 2 * |b.im|) *
      (‖w + I * t‖ ^ (-a.re) * ‖z - I * t‖ ^ (-b.re)) := by
  unfold vbF
  rw [norm_mul]
  have h1 := vb_norm_cpow_le (vb_re_add hw t) (-a)
  have h2 := vb_norm_cpow_le (vb_re_sub hz t) (-b)
  simp only [neg_im, abs_neg, neg_re] at h1 h2
  calc ‖(w + I * t) ^ (-a)‖ * ‖(z - I * t) ^ (-b)‖
      ≤ (Real.exp (π / 2 * |a.im|) * ‖w + I * t‖ ^ (-a.re)) *
        (Real.exp (π / 2 * |b.im|) * ‖z - I * t‖ ^ (-b.re)) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem vb_measurable_vbF (a b w z : ℂ) : Measurable (vbF a b w z) := by
  unfold vbF; fun_prop

theorem vb_integrable_vbF {a b w z : ℂ} (hw : 0 < w.re) (hz : 0 < z.re)
    (hab : 1 < (a + b).re) : Integrable (vbF a b w z) := by
  have := (vb_integrable_rpow hw hz (α := a.re) (β := b.re) (by simpa using hab)).const_mul
    (Real.exp (π / 2 * |a.im|) * Real.exp (π / 2 * |b.im|))
  exact this.mono' (vb_measurable_vbF a b w z).aestronglyMeasurable
    (Eventually.of_forall fun t => vb_norm_vbF_le hw hz t)

/-- A parametric integral of functions holomorphic in the parameter, locally dominated by an
integrable function, is holomorphic. -/
theorem vb_differentiableOn_integral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {U : Set ℂ} (hU : IsOpen U) {F : ℂ → α → ℂ}
    (hmeas : ∀ z ∈ U, AEStronglyMeasurable (F z) μ)
    (hdiff : ∀ᵐ x ∂μ, DifferentiableOn ℂ (fun z => F z x) U)
    (hbound : ∀ z₀ ∈ U, ∃ ε > 0, Metric.closedBall z₀ ε ⊆ U ∧ ∃ g : α → ℝ, Integrable g μ ∧
      ∀ᵐ x ∂μ, ∀ z ∈ Metric.closedBall z₀ ε, ‖F z x‖ ≤ g x) :
    DifferentiableOn ℂ (fun z => ∫ x, F z x ∂μ) U := by
  apply Complex.differentiableOn_integral_of_locally_dominated hU hmeas hdiff
  intro z₀ hz₀
  obtain ⟨ε, hε, _, g, hg, hgb⟩ := hbound z₀ hz₀
  exact ⟨Metric.closedBall z₀ ε, Metric.closedBall_mem_nhds z₀ hε, g, hg, hgb⟩

/-- The vertical Beta integral is holomorphic in `b` on `Re (a + b) > 1`. -/
theorem vb_differentiableOn_b {a w z : ℂ} (hw : 0 < w.re) (hz : 0 < z.re) :
    DifferentiableOn ℂ (fun b => ∫ t, vbF a b w z t) {b : ℂ | 1 - a.re < b.re} := by
  have hU : IsOpen {b : ℂ | 1 - a.re < b.re} := isOpen_lt continuous_const continuous_re
  refine vb_differentiableOn_integral hU
    (fun b _ => (vb_measurable_vbF a b w z).aestronglyMeasurable)
    (Eventually.of_forall fun t b _ => ?_) fun b₀ hb₀ => ?_
  · have hne : z - I * t ≠ 0 := fun h => by
      have := vb_re_sub hz t; rw [h] at this; simp at this
    unfold vbF
    exact ((differentiableAt_id.neg.const_cpow (Or.inl hne)).const_mul _).differentiableWithinAt
  · have hb₀' : 1 - a.re < b₀.re := hb₀
    set ε := (b₀.re - (1 - a.re)) / 2 with hε
    have hε0 : 0 < ε := by rw [hε]; linarith
    have hball : ∀ b ∈ Metric.closedBall b₀ ε,
        b₀.re - ε ≤ b.re ∧ b.re ≤ b₀.re + ε ∧ |b.im| ≤ |b₀.im| + ε := by
      intro b hb
      rw [Metric.mem_closedBall, dist_eq_norm] at hb
      have h1 := abs_re_le_norm (b - b₀)
      have h2 := abs_im_le_norm (b - b₀)
      rw [sub_re] at h1
      rw [sub_im] at h2
      have h3 := abs_sub_abs_le_abs_sub b.im b₀.im
      refine ⟨?_, ?_, ?_⟩ <;>
        [linarith [(abs_le.mp (h1.trans hb)).1]; linarith [(abs_le.mp (h1.trans hb)).2];
          linarith]
    refine ⟨ε, hε0, fun b hb => ?_, ?_⟩
    · have := (hball b hb).1
      show 1 - a.re < b.re
      linarith
    set K := Real.exp (π / 2 * |a.im|) * Real.exp (π / 2 * (|b₀.im| + ε))
    refine ⟨fun t => K * (‖w + I * t‖ ^ (-a.re) * ‖z - I * t‖ ^ (-(b₀.re - ε)) +
      ‖w + I * t‖ ^ (-a.re) * ‖z - I * t‖ ^ (-(b₀.re + ε))), ?_, ?_⟩
    · refine Integrable.const_mul (Integrable.add ?_ ?_) K
      · exact vb_integrable_rpow hw hz (by linarith)
      · exact vb_integrable_rpow hw hz (by linarith)
    · refine Eventually.of_forall fun t b hb => ?_
      obtain ⟨h1, h2, h3⟩ := hball b hb
      have hx : 0 < ‖z - I * t‖ := norm_pos_iff.mpr fun h => by
        have := vb_re_sub hz t; rw [h] at this; simp at this
      have hQ := vb_rpow_le_add (σ := b.re) hx h1 h2
      have hE : Real.exp (π / 2 * |b.im|) ≤ Real.exp (π / 2 * (|b₀.im| + ε)) :=
        Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
      refine (vb_norm_vbF_le hw hz t).trans ?_
      have hP : 0 ≤ ‖w + I * t‖ ^ (-a.re) := by positivity
      calc Real.exp (π / 2 * |a.im|) * Real.exp (π / 2 * |b.im|) *
            (‖w + I * t‖ ^ (-a.re) * ‖z - I * t‖ ^ (-b.re))
          ≤ K * (‖w + I * t‖ ^ (-a.re) *
              (‖z - I * t‖ ^ (-(b₀.re - ε)) + ‖z - I * t‖ ^ (-(b₀.re + ε)))) := by
            apply mul_le_mul _ (mul_le_mul_of_nonneg_left hQ hP) (by positivity) (by positivity)
            exact mul_le_mul_of_nonneg_left hE (by positivity)
        _ = _ := by ring

/-- Laplace representation of `x^{-a}`. -/
theorem vb_cpow_neg_eq_integral {a x : ℂ} (ha : 0 < a.re) (hx : 0 < x.re) :
    x ^ (-a) = (Complex.Gamma a)⁻¹ * ∫ s in Ioi (0 : ℝ), (s : ℂ) ^ (a - 1) * cexp (-(x * s)) := by
  rw [integral_cpow_mul_cexp_neg_mul_Ioi ha hx, ← mul_assoc,
    inv_mul_cancel₀ (Complex.Gamma_ne_zero_of_re_pos ha), one_mul]

theorem vb_integrableOn_cpow_exp {b z : ℂ} (hb : 0 < b.re) (hz : 0 < z.re) :
    IntegrableOn (fun v : ℝ => (v : ℂ) ^ (b - 1) * cexp (-(z * v))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := b.re - 1) (b := z.re)
    (by linarith) one_pos hz
  refine Integrable.mono' h (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hv, Complex.norm_exp, Real.rpow_one]
  simp

/-- The Fourier transform of `(z - i t)^{-b}`, by Fourier inversion. -/
theorem vb_fourier_inner {b z : ℂ} (hb : 1 < b.re) (hz : 0 < z.re) {s : ℝ} (hs : 0 < s) :
    ∫ t : ℝ, cexp (-(I * t * s)) * (z - I * t) ^ (-b) =
      2 * π * (Complex.Gamma b)⁻¹ * ((s : ℂ) ^ (b - 1) * cexp (-(z * s))) := by
  set g : ℝ → ℂ := indicator (Ioi 0) fun v => (v : ℂ) ^ (b - 1) * cexp (-(z * v)) with hg
  have hgi : Integrable g :=
    (vb_integrableOn_cpow_exp (by linarith) hz).integrable_indicator measurableSet_Ioi
  have hF : ∀ ξ : ℝ, 𝓕 g ξ = Complex.Gamma b * (z + I * ((2 * π * ξ : ℝ) : ℂ)) ^ (-b) := by
    intro ξ
    rw [Real.fourier_real_eq_integral_exp_smul]
    have hfun : (fun v : ℝ => cexp (((-2 * π * v * ξ : ℝ) : ℂ) * I) • g v) =
        indicator (Ioi 0) fun v : ℝ =>
          (v : ℂ) ^ (b - 1) * cexp (-((z + I * ((2 * π * ξ : ℝ) : ℂ)) * v)) := by
      funext v
      by_cases hv : v ∈ Ioi (0 : ℝ)
      · rw [hg, indicator_of_mem hv, indicator_of_mem hv, smul_eq_mul, mul_left_comm,
          ← Complex.exp_add]
        congr 2
        push_cast
        ring
      · rw [hg, indicator_of_notMem hv, indicator_of_notMem hv, smul_zero]
    rw [hfun, MeasureTheory.integral_indicator measurableSet_Ioi,
      integral_cpow_mul_cexp_neg_mul_Ioi (by linarith) (by simpa using hz)]
  have hFi : Integrable (𝓕 g) := by
    have h0 := vb_integrable_rpow (w := 1) (z := z) (α := 0) (β := b.re) (by simp) hz
      (by linarith)
    simp only [neg_zero, Real.rpow_zero, one_mul] at h0
    have h1 := h0.comp_mul_left' (R := -2 * π) (by positivity)
    have h2 := h1.const_mul (‖Complex.Gamma b‖ * Real.exp (π / 2 * |b.im|))
    refine h2.mono' ?_ (Eventually.of_forall fun ξ => ?_)
    · rw [show 𝓕 g = fun ξ : ℝ => Complex.Gamma b * (z + I * ((2 * π * ξ : ℝ) : ℂ)) ^ (-b) from
        funext hF]
      exact Measurable.aestronglyMeasurable (by fun_prop)
    · rw [hF, norm_mul]
      have hre : 0 < (z + I * ((2 * π * ξ : ℝ) : ℂ)).re := by simpa using hz
      have := vb_norm_cpow_le hre (-b)
      simp only [neg_im, abs_neg, neg_re] at this
      have he : z + I * ((2 * π * ξ : ℝ) : ℂ) = z - I * ((-2 * π * ξ : ℝ) : ℂ) := by
        push_cast; ring
      rw [he] at this
      calc ‖Complex.Gamma b‖ * ‖(z + I * ((2 * π * ξ : ℝ) : ℂ)) ^ (-b)‖
          ≤ ‖Complex.Gamma b‖ * (Real.exp (π / 2 * |b.im|) *
              ‖z - I * ((-2 * π * ξ : ℝ) : ℂ)‖ ^ (-b.re)) := by
            rw [he]; exact mul_le_mul_of_nonneg_left this (norm_nonneg _)
        _ = _ := by ring
  have hcont : ContinuousAt g s := by
    have hh : ContinuousAt (fun v : ℝ => (v : ℂ) ^ (b - 1) * cexp (-(z * v))) s :=
      (continuousAt_ofReal_cpow_const s (b - 1) (Or.inr hs.ne')).mul (by fun_prop)
    refine hh.congr (Filter.eventuallyEq_of_mem (Ioi_mem_nhds hs) fun v hv => ?_)
    rw [hg, indicator_of_mem hv]
  have hinv := hgi.fourierInv_fourier_eq hFi hcont
  rw [Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul] at hinv
  simp_rw [hF, smul_eq_mul] at hinv
  rw [hg, indicator_of_mem (show s ∈ Ioi (0 : ℝ) from hs)] at hinv
  set G : ℝ → ℂ := fun ξ => cexp (((-2 * π * ξ * -s : ℝ) : ℂ) * I) *
    (Complex.Gamma b * (z + I * ((2 * π * ξ : ℝ) : ℂ)) ^ (-b)) with hG
  have hcv := Measure.integral_comp_mul_left G (-1 / (2 * π))
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hGc : ∀ t : ℝ, G (-1 / (2 * π) * t) =
      Complex.Gamma b * (cexp (-(I * t * s)) * (z - I * t) ^ (-b)) := by
    intro t
    simp only [hG]
    have e1 : (((-2 * π * (-1 / (2 * π) * t) * -s : ℝ) : ℂ) * I) = -(I * t * s) := by
      push_cast; field_simp
    have e2 : z + I * ((2 * π * (-1 / (2 * π) * t) : ℝ) : ℂ) = z - I * t := by
      push_cast; field_simp; ring
    rw [e1, e2]; ring
  simp_rw [hGc] at hcv
  rw [MeasureTheory.integral_const_mul] at hcv
  have hab : |(-1 / (2 * π))⁻¹| = 2 * π := by
    rw [inv_div, abs_div, abs_neg, abs_one, div_one, abs_of_pos (by positivity)]
  rw [hab, ← hG] at hcv
  change ∫ ξ, G ξ = _ at hinv
  rw [hinv, Complex.real_smul] at hcv
  have hΓ : Complex.Gamma b ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
  rw [← mul_right_inj' hΓ, hcv]
  push_cast
  field_simp

/-- The base case `Re a > 0`, `Re b > 1` of 5.12.8, by Fubini and `vb_fourier_inner`. -/
theorem vb_base {a b w z : ℂ} (ha : 0 < a.re) (hb : 1 < b.re) (hw : 0 < w.re) (hz : 0 < z.re) :
    ∫ t, vbF a b w z t = 2 * π * ((Complex.Gamma a)⁻¹ * (Complex.Gamma b)⁻¹ *
      (Complex.Gamma (a + b - 1) * (w + z) ^ (-(a + b - 1)))) := by
  set H : ℝ → ℝ → ℂ := fun t s =>
    (s : ℂ) ^ (a - 1) * cexp (-((w + I * t) * s)) * (z - I * t) ^ (-b) with hH
  have h1 : ∀ t, vbF a b w z t = (Complex.Gamma a)⁻¹ * ∫ s in Ioi (0 : ℝ), H t s := by
    intro t
    simp only [vbF, hH]
    rw [vb_cpow_neg_eq_integral ha (vb_re_add hw t), mul_assoc, MeasureTheory.integral_mul_const]
  simp_rw [h1]
  rw [MeasureTheory.integral_const_mul]
  have hHint : Integrable (Function.uncurry H) (volume.prod (volume.restrict (Ioi 0))) := by
    have hf : Integrable (fun t : ℝ => Real.exp (π / 2 * |b.im|) * ‖z - I * t‖ ^ (-b.re)) := by
      have h0 := vb_integrable_rpow (w := 1) (z := z) (α := 0) (β := b.re) (by simp) hz
        (by linarith)
      simp only [neg_zero, Real.rpow_zero, one_mul] at h0
      exact h0.const_mul _
    have hg : Integrable (fun s : ℝ => s ^ (a.re - 1) * Real.exp (-w.re * s))
        (volume.restrict (Ioi 0)) := by
      have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := a.re - 1) (b := w.re)
        (by linarith) one_pos hw
      simp only [Real.rpow_one] at this
      exact this
    refine (hf.mul_prod hg).mono' (Measurable.aestronglyMeasurable (by simp only [hH]; fun_prop))
      ?_
    have hμ : (volume : Measure ℝ).prod (volume.restrict (Ioi (0 : ℝ))) =
        ((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict
          (univ ×ˢ Ioi (0 : ℝ)) := by
      rw [← Measure.prod_restrict, Measure.restrict_univ]
    rw [hμ]
    filter_upwards [ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Ioi)] with p hp
    have hs : 0 < p.2 := hp.2
    show ‖H p.1 p.2‖ ≤ _
    simp only [hH]
    rw [norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos hs, Complex.norm_exp]
    have hn := vb_norm_cpow_le (vb_re_sub hz p.1) (-b)
    simp only [neg_im, abs_neg, neg_re] at hn
    have hre : (-((w + I * (p.1 : ℂ)) * (p.2 : ℂ))).re = -w.re * p.2 := by simp
    rw [hre, sub_re, one_re]
    calc p.2 ^ (a.re - 1) * Real.exp (-w.re * p.2) * ‖(z - I * (p.1 : ℂ)) ^ (-b)‖
        ≤ p.2 ^ (a.re - 1) * Real.exp (-w.re * p.2) *
          (Real.exp (π / 2 * |b.im|) * ‖z - I * (p.1 : ℂ)‖ ^ (-b.re)) :=
          mul_le_mul_of_nonneg_left hn (by positivity)
      _ = _ := by ring
  rw [integral_integral_swap hHint]
  have h2 : ∀ s ∈ Ioi (0 : ℝ), ∫ t, H t s = 2 * π * (Complex.Gamma b)⁻¹ *
      ((s : ℂ) ^ ((a + b - 1) - 1) * cexp (-((w + z) * s))) := by
    intro s hs
    have hs' : (0 : ℝ) < s := hs
    have hsplit : ∀ t : ℝ, H t s = ((s : ℂ) ^ (a - 1) * cexp (-(w * s))) *
        (cexp (-(I * t * s)) * (z - I * t) ^ (-b)) := by
      intro t
      simp only [hH]
      rw [show -((w + I * (t : ℂ)) * s) = -(w * s) + -(I * t * s) by ring, Complex.exp_add]
      ring
    simp_rw [hsplit]
    rw [MeasureTheory.integral_const_mul, vb_fourier_inner hb hz hs']
    have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs'.ne'
    have hcp : (s : ℂ) ^ ((a + b - 1) - 1) = (s : ℂ) ^ (a - 1) * (s : ℂ) ^ (b - 1) := by
      rw [← cpow_add _ _ hs0]; ring_nf
    have hex : cexp (-((w + z) * s)) = cexp (-(w * s)) * cexp (-(z * s)) := by
      rw [← Complex.exp_add]; ring_nf
    rw [hcp, hex]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi h2, MeasureTheory.integral_const_mul,
    integral_cpow_mul_cexp_neg_mul_Ioi (by simp; linarith) (by simp; linarith)]
  ring

/-- The right-hand side of 5.12.8. -/
def vbR (a b w z : ℂ) : ℂ :=
  (w + z) ^ (1 - a - b) * Complex.Gamma (a + b) /
    ((a + b - 1) * Complex.Gamma a * Complex.Gamma b)

theorem vb_eq_base {a b w z : ℂ} (ha : 0 < a.re) (hb : 1 < b.re) (hw : 0 < w.re)
    (hz : 0 < z.re) : (1 / (2 * π)) * ∫ t, vbF a b w z t = vbR a b w z := by
  rw [vb_base ha hb hw hz, vbR]
  have hs : a + b - 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hΓ : Complex.Gamma (a + b) = (a + b - 1) * Complex.Gamma (a + b - 1) := by
    rw [← Complex.Gamma_add_one _ hs]; ring_nf
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have ha0 := Complex.Gamma_ne_zero_of_re_pos ha
  have hb0 := Complex.Gamma_ne_zero_of_re_pos (show 0 < b.re by linarith)
  rw [hΓ, show (1 : ℂ) - a - b = -(a + b - 1) by ring]
  field_simp

theorem vb_differentiableOn_vbR {a w z : ℂ} (hw : 0 < w.re) (hz : 0 < z.re) :
    DifferentiableOn ℂ (fun b => vbR a b w z) {b : ℂ | 1 - a.re < b.re} := by
  intro b hb
  have hb' : 1 - a.re < b.re := hb
  have hwz : w + z ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hs : a + b - 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hfun : (fun b => vbR a b w z) = fun b => (w + z) ^ (1 - a - b) *
      Complex.Gamma (a + b) * (a + b - 1)⁻¹ * (Complex.Gamma a)⁻¹ * (Complex.Gamma b)⁻¹ := by
    funext b; rw [vbR, div_eq_mul_inv, mul_inv, mul_inv]; ring
  rw [hfun]
  refine DifferentiableAt.differentiableWithinAt ?_
  have hG : DifferentiableAt ℂ (fun b => Complex.Gamma (a + b)) b := by
    refine (Complex.differentiableAt_Gamma _ fun m h => ?_).comp b
      ((differentiableAt_const a).add differentiableAt_id)
    have := congrArg Complex.re h; simp at this
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have h1 : DifferentiableAt ℂ (fun b => (w + z) ^ (1 - a - b)) b :=
    ((differentiableAt_const _).sub differentiableAt_id).const_cpow (Or.inl hwz)
  have h3 : DifferentiableAt ℂ (fun b => (a + b - 1)⁻¹) b :=
    (((differentiableAt_const a).add differentiableAt_id).sub (differentiableAt_const 1)).inv hs
  exact (((h1.mul hG).mul h3).mul (differentiableAt_const _)).mul
    (Complex.differentiable_one_div_Gamma b)

/-- 5.12.8 for `Re a > 0`, by analytic continuation in `b` from `vb_eq_base`. -/
theorem vb_eq_of_re_pos {a b w z : ℂ} (ha : 0 < a.re) (hab : 1 < (a + b).re) (hw : 0 < w.re)
    (hz : 0 < z.re) : (1 / (2 * π)) * ∫ t, vbF a b w z t = vbR a b w z := by
  set U : Set ℂ := {b : ℂ | 1 - a.re < b.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const continuous_re
  have hL : AnalyticOnNhd ℂ (fun b => (1 / (2 * π)) * ∫ t, vbF a b w z t) U :=
    ((vb_differentiableOn_b hw hz).const_mul _).analyticOnNhd hUo
  have hR : AnalyticOnNhd ℂ (fun b => vbR a b w z) U :=
    (vb_differentiableOn_vbR hw hz).analyticOnNhd hUo
  have h2 : (2 : ℂ) ∈ U := by show 1 - a.re < (2 : ℂ).re; simp; linarith
  have hev : (fun b => (1 / (2 * π)) * ∫ t, vbF a b w z t) =ᶠ[𝓝 2] fun b => vbR a b w z := by
    have hV : {b : ℂ | 1 < b.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (by simp)
    filter_upwards [hV] with b hb
    exact vb_eq_base ha hb hw hz
  have hbU : b ∈ U := by show 1 - a.re < b.re; simp at hab; linarith
  exact hL.eqOn_of_preconnected_of_eventuallyEq hR (convex_halfSpace_re_gt _).isPreconnected
    h2 hev hbU

theorem vb_integral_symm (a b w z : ℂ) : ∫ t, vbF a b w z t = ∫ t, vbF b a z w t := by
  have h := Measure.integral_comp_mul_left (vbF b a z w) (-1)
  rw [inv_neg, inv_one, abs_neg, abs_one, one_smul] at h
  rw [← h]
  congr 1
  funext t
  simp only [vbF]
  push_cast
  ring_nf

end VerticalBeta

/-- Cauchy's vertical Beta integral. `1/B(a,b)` is written as `Γ(a+b)/(Γ(a)Γ(b))`: Mathlib's
`betaIntegral a b` is the literal integral, which is `0` when `Re a ≤ 0` or `Re b ≤ 0`, while
the identity holds for all `a, b` with `Re (a + b) > 1`. -/
@[dlmf 5.12.E8]
theorem beta_vertical {a b : ℂ} {w z : ℂ} (hw : 0 < w.re) (hz : 0 < z.re)
    (hab : 1 < (a + b).re) :
    (1 / (2 * π)) * ∫ t : ℝ,
        1 / ((w + I * t) ^ a * (z - I * t) ^ b) =
      (w + z) ^ (1 - a - b) * Complex.Gamma (a + b) /
        ((a + b - 1) * Complex.Gamma a * Complex.Gamma b) := by
  have hfun : (fun t : ℝ => 1 / ((w + I * t) ^ a * (z - I * t) ^ b)) = vbF a b w z := by
    funext t; rw [vbF, one_div, mul_inv, cpow_neg, cpow_neg]
  rw [hfun]
  rcases lt_or_ge 0 a.re with ha | ha
  · exact vb_eq_of_re_pos ha hab hw hz
  · have hb : 0 < b.re := by simp at hab; linarith
    rw [vb_integral_symm, vb_eq_of_re_pos hb (by rwa [add_comm]) hz hw, vbR,
      show (1 : ℂ) - b - a = 1 - a - b by ring, add_comm z w, add_comm b a]
    ring

end DLMF.Gamma
