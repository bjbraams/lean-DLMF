/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Zeta.Hurwitz.SeriesAndContinuation
public import DLMFMathlib.Analysis.SpecialFunctions.Pow.ComplexReal
public import DLMFMathlib.Analysis.Complex.PuncturedHalfPlane
public import DLMF.Zeta.LerchContinuation
public import DLMFMathlib.Analysis.Integral.ImproperFourier
public import DLMFMathlib.Analysis.SpecialFunctions.ImproperIntegralsExtra

/-!
# Boundary convergence of the alternating Hurwitz integral

The integral kernel for DLMF 25.11.35 splits into a Gamma Fourier kernel and an
absolutely integrable remainder when the shift parameter lies on the imaginary axis.
-/

@[expose] public noncomputable section

open Complex Set Filter MeasureTheory
open scoped Topology

namespace DLMF.Zeta.AlternatingIntegral

/-- The denominator of the alternating Laplace kernel is uniformly bounded away from zero. -/
theorem one_le_norm_one_add_exp_neg (x : ℝ) :
    1 ≤ ‖(1 : ℂ) + exp (-(x : ℂ))‖ := by
  rw [← ofReal_neg, ← ofReal_exp, ← ofReal_one, ← ofReal_add, norm_real,
    Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 + Real.exp (-x))]
  linarith [Real.exp_pos (-x)]

/-- The alternating Laplace denominator never vanishes. -/
theorem one_add_exp_neg_ne_zero (x : ℝ) : (1 : ℂ) + exp (-(x : ℂ)) ≠ 0 := by
  intro h
  have := one_le_norm_one_add_exp_neg x
  rw [h, norm_zero] at this
  linarith

/-- Local integrability, including at the origin, for positive real part of the order. -/
theorem intervalIntegrable {s : ℂ} (hs : 0 < s.re) (a : ℂ) (b c : ℝ) :
    IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (s - 1) * exp (-(a * x)) /
      (1 + exp (-(x : ℂ)))) volume b c := by
  have hi := intervalIntegral.intervalIntegrable_cpow'
    (a := b) (b := c) (by simp; linarith : -1 < (s - 1).re)
  have hc : Continuous (fun x : ℝ => exp (-(a * x)) / (1 + exp (-(x : ℂ)))) :=
    Continuous.div (by fun_prop) (by fun_prop) one_add_exp_neg_ne_zero
  exact (hi.mul_continuousOn hc.continuousOn).congr (by
    intro x _
    ring)

/-- Absolute convergence in the interior of the shift half-plane. -/
theorem integrableOn {s a : ℂ} (hs : 0 < s.re) (ha : 0 < a.re) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 1) * exp (-(a * x)) /
      (1 + exp (-(x : ℂ)))) (Ioi 0) := by
  have h := Complex.integrableOn_cpow_mul_exp_neg_mul hs ha
  refine h.norm.mono' (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [norm_div]
  exact div_le_self (norm_nonneg _) (one_le_norm_one_add_exp_neg x)

/-- Conditional convergence on the nonzero imaginary axis. -/
theorem exists_tendsto_integral {s a : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (ha : a.re = 0) (ha0 : a ≠ 0) :
    ∃ L, Tendsto (fun X : ℝ => ∫ x in (0 : ℝ)..X,
      (x : ℂ) ^ (s - 1) * exp (-(a * x)) / (1 + exp (-(x : ℂ)))) atTop (𝓝 L) := by
  let B : ℝ → ℂ := fun x => (x : ℂ) ^ (s - 1) * exp (-(a * x))
  let R : ℝ → ℂ := fun x => B x * exp (-(x : ℂ)) / (1 + exp (-(x : ℂ)))
  have hRi : IntegrableOn R (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul (r := s.re - 1) (by linarith) one_pos
    refine h.mono' (Measurable.aestronglyMeasurable (by fun_prop)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := hx
    have hden := one_le_norm_one_add_exp_neg x
    dsimp [R, B]
    rw [norm_div, norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos hx0, norm_exp,
      ← ofReal_neg, norm_exp_ofReal]
    simp only [neg_re, mul_re, ofReal_re, ofReal_im, ha, zero_mul, mul_zero,
      sub_zero, neg_zero, Real.exp_zero, mul_one, sub_re, one_re, one_mul]
    exact div_le_self (by positivity) (by simpa only [ofReal_neg] using hden)
  have hRfi (b c : ℝ) : IntervalIntegrable R volume b c := by
    have h := intervalIntegral.intervalIntegrable_cpow'
      (a := b) (b := c) (by simp; linarith : -1 < (s - 1).re)
    have hc : Continuous (fun x : ℝ => exp (-(a * x)) * exp (-(x : ℂ)) /
        (1 + exp (-(x : ℂ)))) :=
      Continuous.div (by fun_prop) (by fun_prop) one_add_exp_neg_ne_zero
    exact (h.mul_continuousOn hc.continuousOn).congr (by
      intro x _
      dsimp [R, B]
      ring)
  obtain ⟨L, hL⟩ := Complex.exists_tendsto_integral_cpow_mul_exp_of_re_eq_zero hs0 hs1 ha ha0
  have hR := intervalIntegral_tendsto_integral_Ioi 0 hRi tendsto_id
  refine ⟨L - ∫ x in Ioi (0 : ℝ), R x, ?_⟩
  refine (hL.sub hR).congr fun X => ?_
  have hBfi : IntervalIntegrable B volume 0 X :=
    (intervalIntegral.intervalIntegrable_cpow' (by simp; linarith : -1 < (s - 1).re))
      |>.mul_continuousOn (show ContinuousOn (fun x : ℝ => exp (-(a * x))) (uIcc 0 X) by
        fun_prop)
  change (∫ x in (0 : ℝ)..X, B x) - (∫ x in (0 : ℝ)..X, R x) = _
  rw [← intervalIntegral.integral_sub hBfi (hRfi 0 X)]
  apply intervalIntegral.integral_congr
  intro x _
  dsimp [B, R]
  field_simp [one_add_exp_neg_ne_zero x]
  ring

/-- Continuity in a shift away from the real-axis poles, obtained from the unit recurrence. -/
theorem continuousAt_hurwitzZetaComplex {s a : ℂ} (hs : s ≠ 1) (ha : a.im ≠ 0)
    (haRe : -1 < a.re) : ContinuousAt (hurwitzZetaComplex s) a := by
  have hpos : 0 < (a + 1).re := by simp; linarith
  have hζ := ((differentiableOn_hurwitzZetaComplex_param hs (a + 1) hpos).differentiableAt
    ((isOpen_lt continuous_const continuous_re).mem_nhds hpos)).continuousAt
  have hζcomp : ContinuousAt (fun z => hurwitzZetaComplex s (z + 1)) a :=
    hζ.comp (f := fun z : ℂ => z + 1) (x := a) (by fun_prop)
  have hp : ContinuousAt (fun z : ℂ => z ^ (-s)) a :=
    continuousAt_id.cpow continuousAt_const (mem_slitPlane_iff.mpr (Or.inr ha))
  apply (hζcomp.add hp).congr_of_eventuallyEq
  filter_upwards [(isOpen_ne_fun continuous_im continuous_const).mem_nhds ha] with z hz
  exact hurwitzZetaComplex_eq_add_one hs fun m hm => by
    have h := congrArg Complex.im hm
    simp at h
    exact hz h

/-- Holomorphy in `s` of `∫_0^∞ x^{s-1} e^{-ax}/(1 + e^{-x}) dx` on `Re s > 0`. -/
private lemma differentiableOn_lerchIntegral_neg_one {a : ℂ} (ha : 0 < a.re) :
    DifferentiableOn ℂ (fun s => lerchIntegral s a (-1)) {s : ℂ | 0 < s.re} := by
  have hU : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const continuous_re
  have hden : ∀ x : ℝ, ‖1 - (-1) * cexp (-(x : ℂ))‖ ≥ 1 := by
    intro x
    have e : 1 - (-1) * cexp (-(x : ℂ)) = ((1 + Real.exp (-x) : ℝ) : ℂ) := by
      rw [Complex.ofReal_add, Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_one]; ring
    rw [e, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    linarith [Real.exp_pos (-x)]
  have hden0 : ∀ x : ℝ, 1 - (-1) * cexp (-(x : ℂ)) ≠ 0 := fun x h => by
    have := hden x; rw [h, norm_zero] at this; linarith
  refine Complex.differentiableOn_integral_Ioi_of_locally_dominated hU 0 (fun s _ => ?_) ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable (fun x hx => ?_) measurableSet_Ioi
    refine ContinuousAt.continuousWithinAt ?_
    exact ContinuousAt.div (ContinuousAt.mul (continuousAt_ofReal_cpow_const _ _
      (Or.inr (ne_of_gt hx))) (by fun_prop)) (by fun_prop) (hden0 x)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx s _
    have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hx)
    refine DifferentiableAt.differentiableWithinAt ?_
    exact (((differentiableAt_id.sub_const 1).const_cpow (Or.inl hx0)).mul
      (differentiableAt_const _)).div_const _
  · intro s₀ hs₀
    have hs₀' : 0 < s₀.re := hs₀
    set δ := s₀.re / 2
    have hδ : 0 < δ := by simp only [δ]; linarith
    refine ⟨Metric.ball s₀ δ, Metric.ball_mem_nhds _ hδ, fun x =>
      (x ^ ((s₀.re - δ) - 1) + x ^ ((s₀.re + δ) - 1)) * Real.exp (-(a.re * x)), ?_, ?_⟩
    · have h1 := integrableOn_rpow_mul_exp_neg (σ := s₀.re - δ) (by simp only [δ]; linarith) ha
      have h2 := integrableOn_rpow_mul_exp_neg (σ := s₀.re + δ) (by simp only [δ]; linarith) ha
      exact (h1.add h2).congr_fun (fun x _ => by simp only [Pi.add_apply]; ring)
        measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx s hs
      rw [Metric.mem_ball, dist_eq_norm] at hs
      have := abs_re_le_norm (s - s₀)
      simp only [sub_re] at this
      have h1 : s₀.re - δ ≤ s.re := by linarith [neg_abs_le (s.re - s₀.re)]
      have h2 : s.re ≤ s₀.re + δ := by linarith [le_abs_self (s.re - s₀.re)]
      rw [norm_div, norm_cpow_mul_exp_neg hx]
      have hd := hden x
      have hp : 0 ≤ x ^ (s.re - 1) * Real.exp (-(a.re * x)) :=
        mul_nonneg (Real.rpow_nonneg (le_of_lt hx) _) (Real.exp_pos _).le
      calc x ^ (s.re - 1) * Real.exp (-(a.re * x)) / ‖1 - (-1) * cexp (-(x : ℂ))‖
          ≤ x ^ (s.re - 1) * Real.exp (-(a.re * x)) := div_le_self hp hd
        _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          have := rpow_neg_sub_one_le_add (x := x) (σ := -s.re) (σ₀ := -(s₀.re + δ))
            (R := -(s₀.re - δ)) hx (by linarith) (by linarith)
          simp only [neg_neg] at this
          linarith

/-- The alternating Hurwitz integral (DLMF 25.11.35, integral form) for `Re a > 0`,
`Re s > 0`, `s ≠ 1`:
`(1/Γ(s)) ∫_0^∞ x^{s-1} e^{-ax}/(1+e^{-x}) dx = 2^{-s}(ζ(s,a/2) - ζ(s,(1+a)/2))`. -/
theorem one_div_Gamma_mul_lerchIntegral_neg_one {s a : ℂ} (hs0 : 0 < s.re) (hs1 : s ≠ 1)
    (ha : 0 < a.re) :
    1 / Gamma s * lerchIntegral s a (-1) =
      2 ^ (-s) * (hurwitzZetaComplex s (a / 2) - hurwitzZetaComplex s ((1 + a) / 2)) := by
  have ha2 : 0 < (a / 2).re := by simp; linarith
  have ha3 : 0 < ((1 + a) / 2).re := by simp; linarith
  set W : Set ℂ := {t : ℂ | 0 < t.re} \ {1}
  have hW : IsOpen W := (isOpen_lt continuous_const continuous_re).sdiff isClosed_singleton
  have hF : DifferentiableOn ℂ (fun t => 1 / Gamma t * lerchIntegral t a (-1)) W := by
    intro t ht
    have hI := ((differentiableOn_lerchIntegral_neg_one ha) t ht.1).differentiableAt
      ((isOpen_lt continuous_const continuous_re).mem_nhds ht.1)
    have h1 : DifferentiableAt ℂ (fun t : ℂ => 1 / Gamma t) t := by
      simpa only [one_div] using Complex.differentiable_one_div_Gamma t
    exact (h1.mul hI).differentiableWithinAt
  have hG : DifferentiableOn ℂ (fun t => (2 : ℂ) ^ (-t) * (hurwitzZetaComplex t (a / 2) -
      hurwitzZetaComplex t ((1 + a) / 2))) W := by
    intro t ht
    exact (((differentiableAt_id.neg).const_cpow (Or.inl two_ne_zero)).mul
      ((differentiableAt_hurwitzZetaComplex_of_add_natCast_ne_zero' ht.2
          (Complex.add_natCast_ne_zero_of_re_pos ha2)).sub
        (differentiableAt_hurwitzZetaComplex_of_add_natCast_ne_zero' ht.2
          (Complex.add_natCast_ne_zero_of_re_pos ha3)))).differentiableWithinAt
  refine (hF.analyticOnNhd hW).eqOn_of_preconnected_of_eventuallyEq (hG.analyticOnNhd hW)
    (Complex.isPreconnected_re_gt_sdiff_one (by norm_num)) (show (2 : ℂ) ∈ W by norm_num [W]) ?_
    ⟨hs0, hs1⟩
  have hopen : IsOpen {t : ℂ | 1 < t.re} := isOpen_lt continuous_const continuous_re
  filter_upwards [hopen.mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with t ht
  have hL := hasSum_lerch_lerchIntegral (z := -1) (by linarith) ha (Or.inr ⟨by simp, ht⟩)
  have hne : ∀ b : ℂ, 0 < b.re → ∀ m : ℕ, b ≠ -m := fun b hb m h => by
    have := congrArg Complex.re h; simp at this; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  have he := (hasSum_hurwitzZetaComplex ht (hne _ ha2)).mul_left ((2 : ℂ) ^ (-t))
  have ho := ((hasSum_hurwitzZetaComplex ht (hne _ ha3)).mul_left ((2 : ℂ) ^ (-t))).neg
  have hsplit : ∀ (m : ℕ) (b : ℂ), 0 < b.re →
      (2 : ℂ) ^ (-t) * (1 / ((m : ℂ) + b) ^ t) = 1 / (2 * (m : ℂ) + 2 * b) ^ t := by
    intro m b hb
    have hw : (m : ℂ) + b ≠ 0 := by rw [add_comm]; exact Complex.add_natCast_ne_zero_of_re_pos hb m
    rw [show 2 * (m : ℂ) + 2 * b = ((2 : ℝ) : ℂ) * ((m : ℂ) + b) by push_cast; ring,
      mul_comm (((2 : ℝ) : ℂ)) ((m : ℂ) + b),
      Complex.mul_ofReal_cpow_of_ne_zero hw two_pos, cpow_neg]
    push_cast
    have h2 : (2 : ℂ) ^ t ≠ 0 := by rw [Ne, cpow_eq_zero_iff]; simp
    have h3 : ((m : ℂ) + b) ^ t ≠ 0 := by rw [Ne, cpow_eq_zero_iff]; simp [hw]
    field_simp
  have hs := HasSum.even_add_odd (f := fun n : ℕ => (-1 : ℂ) ^ n / (a + n) ^ t)
    (he.congr_fun fun k => ?_) (ho.congr_fun fun k => ?_)
  · rw [← sub_eq_add_neg, ← mul_sub] at hs
    rw [one_div]; exact (hs.unique hL).symm
  · rw [hsplit k _ ha2, show (-1 : ℂ) ^ (2 * k) = 1 by rw [pow_mul]; norm_num]
    push_cast; ring_nf
  · rw [hsplit k _ ha3, show (-1 : ℂ) ^ (2 * k + 1) = -1 by rw [pow_succ, pow_mul]; norm_num]
    push_cast; ring_nf


/-- The alternating Hurwitz integral, including its conditionally convergent boundary. -/
theorem tendsto_integral {s a : ℂ} (hs1 : s ≠ 1)
    (h : (0 < a.re ∧ 0 < s.re) ∨ (a.re = 0 ∧ a.im ≠ 0 ∧ 0 < s.re ∧ s.re < 1)) :
    Tendsto (fun X : ℝ => 1 / Gamma s * ∫ x in (0 : ℝ)..X,
      (x : ℂ) ^ (s - 1) * exp (-(a * x)) / (1 + exp (-(x : ℂ)))) atTop
      (𝓝 (2 ^ (-s) * (hurwitzZetaComplex s (a / 2) -
        hurwitzZetaComplex s ((1 + a) / 2)))) := by
  rcases h with ⟨ha, hs⟩ | ⟨ha, haim, hs0, hslt⟩
  · have hlim := (intervalIntegral_tendsto_integral_Ioi 0 (integrableOn hs ha) tendsto_id)
      |>.const_mul (1 / Gamma s)
    have hv := one_div_Gamma_mul_lerchIntegral_neg_one hs hs1 ha
    simp only [lerchIntegral, neg_one_mul, sub_neg_eq_add] at hv
    simpa only [id_eq, hv] using hlim
  · let F : ℝ → ℂ := fun x => (x : ℂ) ^ (s - 1) * exp (-(a * x)) /
      (1 + exp (-(x : ℂ)))
    let T : ℂ → ℂ := fun b => 2 ^ (-s) * (hurwitzZetaComplex s (b / 2) -
      hurwitzZetaComplex s ((1 + b) / 2))
    have hFcont : ContinuousOn F (Ioi 0) := by
      intro x hx
      exact ((ContinuousAt.mul (continuousAt_ofReal_cpow_const _ _ (Or.inr (ne_of_gt hx)))
        (by fun_prop)).div (by fun_prop) (one_add_exp_neg_ne_zero x)).continuousWithinAt
    have hfi (b : ℝ) : IntervalIntegrable F volume 0 b := intervalIntegrable hs0 a 0 b
    have ha0 : a ≠ 0 := fun h => haim (by simp [h])
    obtain ⟨L, hL⟩ := exists_tendsto_integral hs0 hslt ha ha0
    have hpoint (ε x : ℝ) : Real.exp (-(ε * x)) • F x =
        (x : ℂ) ^ (s - 1) * exp (-((a + ε) * x)) / (1 + exp (-(x : ℂ))) := by
      dsimp [F]
      rw [ofReal_exp]
      calc
        _ = (x : ℂ) ^ (s - 1) * (exp ((-(ε * x) : ℝ)) * exp (-(a * x))) /
            (1 + exp (-(x : ℂ))) := by ring
        _ = _ := by
          rw [← exp_add]
          congr 3
          push_cast
          ring
    have hint (ε : ℝ) (hε : 0 < ε) :
        IntegrableOn (fun x => Real.exp (-(ε * x)) • F x) (Ioi 0) := by
      have haε : 0 < (a + ε).re := by simp [ha]; exact hε
      exact (integrableOn hs0 haε).congr_fun (fun x _ => (hpoint ε x).symm)
        measurableSet_Ioi
    have hAbel := (MeasureTheory.tendsto_integral_Ioi_exp_neg_mul_smul hFcont hfi hL hint)
      |>.const_mul (1 / Gamma s)
    have him1 : (a / 2).im ≠ 0 := by simpa using div_ne_zero haim (by norm_num : (2 : ℝ) ≠ 0)
    have him2 : ((1 + a) / 2).im ≠ 0 := by
      simpa using div_ne_zero haim (by norm_num : (2 : ℝ) ≠ 0)
    have hre1 : -1 < (a / 2).re := by simp [ha]
    have hre2 : -1 < ((1 + a) / 2).re := by simp [ha]; norm_num
    have hζ1 := continuousAt_hurwitzZetaComplex hs1 him1 hre1
    have hζ2 := continuousAt_hurwitzZetaComplex hs1 him2 hre2
    have hT : ContinuousAt T a := by
      exact continuousAt_const.mul
        ((hζ1.comp (f := fun z : ℂ => z / 2) (x := a) (by fun_prop)).sub
          (hζ2.comp (f := fun z : ℂ => (1 + z) / 2) (x := a) (by fun_prop)))
    have hPath : Tendsto (fun ε : ℝ => a + ε) (𝓝[>] 0) (𝓝 a) := by
      have hc : ContinuousAt (fun ε : ℝ => a + (ε : ℂ)) 0 := by fun_prop
      simpa only [ofReal_zero, add_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
    have hM := hT.tendsto.comp hPath
    have hEq : (fun ε : ℝ => 1 / Gamma s * ∫ x in Ioi (0 : ℝ),
        Real.exp (-(ε * x)) • F x) =ᶠ[𝓝[>] 0] (fun ε : ℝ => T (a + ε)) := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have haε : 0 < (a + ε).re := by simp [ha]; exact hε
      rw [setIntegral_congr_fun measurableSet_Ioi (fun x _ => hpoint ε x)]
      have hv := one_div_Gamma_mul_lerchIntegral_neg_one hs0 hs1 haε
      simpa only [lerchIntegral, neg_one_mul, sub_neg_eq_add, T] using hv
    have hValue : 1 / Gamma s * L = T a := tendsto_nhds_unique hAbel (hM.congr' hEq.symm)
    have h := hL.const_mul (1 / Gamma s)
    rw [hValue] at h
    exact h

end DLMF.Zeta.AlternatingIntegral
