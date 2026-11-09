/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

public import Mathlib.Analysis.MellinTransform
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Analytic.Uniqueness
public import DLMFMathlib.Analysis.SpecialFunctions.Pow.RightHalfPlane
public import DLMFMathlib.Analysis.SpecialFunctions.Pow.Decay
public import DLMFMathlib.Analysis.Fourier.HorizontalStrip
public import Mathlib.Basic.Real.Sign
public import DLMFMathlib.Analysis.SpecificLimits.Oscillation

/-!
# Entire continuation of oscillatory Mellin tails

For a nonzero real frequency, the Mellin transform of `exp(iκt)` on `(1, ∞)`
extends to an entire function of its exponent. Integration by parts gives a recurrence
that continues the initially absolutely convergent transform through successive half-planes.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Asymptotics
open scoped Topology Real ComplexConjugate

namespace Complex

namespace OscillatoryMellinTail

/-- The exponentially decaying integrand on the vertical ray from one. The principal
power is evaluated in the open right half-plane, where its real part is one. -/
def integrand (κ : ℝ) (w : ℂ) (y : ℝ) : ℂ :=
  (1 + I * (Real.sign κ : ℂ) * y) ^ (w - 1) * (Real.exp (-|κ| * y) : ℂ)

/-- The vertical-ray integrand is continuous in its real integration variable. -/
theorem continuous_integrand (κ : ℝ) (w : ℂ) : Continuous (integrand κ w) := by
  refine Continuous.mul ?_ (by fun_prop)
  apply continuous_iff_continuousAt.mpr
  intro y
  exact (by fun_prop : ContinuousAt (fun y : ℝ =>
    (1 : ℂ) + I * (Real.sign κ : ℂ) * y) y).cpow continuousAt_const (Or.inl (by simp))

/-- The vertical-ray kernel has an integrable bound, locally uniform in its exponent. -/
private theorem exists_integrable_bound {κ : ℝ} (hκ : κ ≠ 0) (w₀ : ℂ) :
    ∃ g : ℝ → ℝ, IntegrableOn g (Ioi 0) ∧ ∀ y : ℝ, 0 < y →
      ∀ w ∈ Metric.ball w₀ 1, ‖integrand κ w y‖ ≤ g y := by
  have hs : |Real.sign κ| = 1 := by
    rcases lt_or_gt_of_ne hκ with h | h
    · simp [Real.sign_of_neg h]
    · simp [Real.sign_of_pos h]
  obtain ⟨C, hC, N, hb⟩ := exists_bound_cpow_add_mul_I (a := (1 : ℂ)) (by norm_num)
    (M := ‖w₀ - 1‖ + 1) (by positivity)
  refine ⟨fun y => C * (1 + |y|) ^ N * Real.exp (-|κ| * |y|), ?_, ?_⟩
  · simpa only [neg_mul, mul_assoc] using
      ((Real.integrable_one_add_abs_pow_mul_exp_neg (abs_pos.mpr hκ) N).const_mul C).integrableOn
  · intro y hy w hw
    have hw' : ‖w - w₀‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hw
    have hW : ‖w - 1‖ ≤ ‖w₀ - 1‖ + 1 := by
      have he : w - 1 = (w - w₀) + (w₀ - 1) := by ring
      rw [he]
      linarith [norm_add_le (w - w₀) (w₀ - 1)]
    have hpow := hb (w - 1) hW (Real.sign κ * y)
    have he : (1 : ℂ) + I * (Real.sign κ : ℂ) * y =
        1 + ((Real.sign κ * y : ℝ) : ℂ) * I := by push_cast; ring
    rw [integrand, norm_mul, he, norm_real, Real.norm_eq_abs, Real.abs_exp]
    simp only [abs_mul, hs, one_mul] at hpow
    simpa only [abs_of_pos hy] using
      mul_le_mul_of_nonneg_right hpow (Real.exp_pos (-|κ| * y)).le

/-- Absolute integrability of the vertical-ray kernel for every complex exponent. -/
theorem integrableOn_integrand {κ : ℝ} (hκ : κ ≠ 0) (w : ℂ) :
    IntegrableOn (integrand κ w) (Ioi 0) := by
  obtain ⟨g, hg, hb⟩ := exists_integrable_bound hκ w
  refine hg.mono' (continuous_integrand κ w).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  exact hb y hy w (Metric.mem_ball_self zero_lt_one)

end OscillatoryMellinTail

/-- The entire oscillatory Mellin tail on the vertical ray from one, rotated into the
half-plane where `exp(iκu)` decays. The complex powers use the principal logarithm. -/
def oscillatoryMellinTail (κ : ℝ) (w : ℂ) : ℂ :=
  I * (Real.sign κ : ℂ) * exp (I * κ) *
    ∫ y in Ioi (0 : ℝ), OscillatoryMellinTail.integrand κ w y

/-- The vertical-ray oscillatory Mellin tail is entire in its exponent. -/
theorem differentiable_oscillatoryMellinTail {κ : ℝ} (hκ : κ ≠ 0) :
    Differentiable ℂ (oscillatoryMellinTail κ) := by
  have hd : DifferentiableOn ℂ (fun w : ℂ =>
      ∫ y in Ioi (0 : ℝ), OscillatoryMellinTail.integrand κ w y) univ := by
    apply differentiableOn_integral_Ioi_of_locally_dominated isOpen_univ 0
    · intro w _
      exact (OscillatoryMellinTail.continuous_integrand κ w).aestronglyMeasurable
    · filter_upwards [] with y w _
      have hbase : (1 : ℂ) + I * (Real.sign κ : ℂ) * y ≠ 0 := by
        intro he
        have hh := congrArg re he
        simp at hh
      exact (((differentiableAt_id.sub_const 1).const_cpow (Or.inl hbase)).mul_const
        (Real.exp (-|κ| * y) : ℂ)).differentiableWithinAt
    · intro w _
      obtain ⟨g, hg, hb⟩ := OscillatoryMellinTail.exists_integrable_bound hκ w
      refine ⟨Metric.ball w 1, Metric.ball_mem_nhds w zero_lt_one, g, hg, ?_⟩
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      exact hb y hy
  intro w
  exact ((differentiableOn_univ.mp hd) w).const_mul (I * (Real.sign κ : ℂ) * exp (I * κ))

/-- For positive frequency, the vertical-ray model equals the conditionally convergent
real-ray integral throughout `Re w < 1`. -/
theorem tendsto_integral_oscillatoryMellinTail_of_pos {κ : ℝ} (hκ : 0 < κ) {w : ℂ}
    (hw : w.re < 1) :
    Tendsto (fun T : ℝ => ∫ u in (1 : ℝ)..T,
      (u : ℂ) ^ (w - 1) * exp (I * κ * u)) atTop (𝓝 (oscillatoryMellinTail κ w)) := by
  let f : ℂ → ℂ := fun z => z ^ (w - 1) * exp (I * κ * z)
  let p := w.re - 1
  let C := Real.exp (Real.pi * |w.im|)
  have hC : 0 < C := Real.exp_pos _
  have hp : p < 0 := by dsimp [p]; linarith
  have hnorm (z : ℂ) (r : ℝ) (hr : 0 < r) (hrz : r ≤ ‖z‖) :
      ‖f z‖ ≤ C * r ^ p * Real.exp (-κ * z.im) := by
    have hz0 : z ≠ 0 := norm_pos_iff.mp (hr.trans_le hrz)
    have hpow := norm_cpow_le_rpow_mul_exp hz0 (w - 1)
    simp only [sub_re, one_re, sub_im, one_im, sub_zero] at hpow
    have hpr := Real.rpow_le_rpow_of_nonpos hr hrz hp.le
    have hexp : (I * (κ : ℂ) * z).re = -κ * z.im := by simp [mul_re, mul_im]
    dsimp only [f]
    rw [norm_mul, norm_exp, hexp]
    calc ‖z ^ (w - 1)‖ * Real.exp (-κ * z.im) ≤
        (‖z‖ ^ p * C) * Real.exp (-κ * z.im) :=
          mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
      _ ≤ (r ^ p * C) * Real.exp (-κ * z.im) := by gcongr
      _ = _ := by ring
  have htop : Tendsto (fun R : ℝ => ∫ x in (1 : ℝ)..R, f (x + R * I)) atTop (𝓝 0) := by
    have ht : Tendsto (fun R : ℝ => C * R ^ w.re * Real.exp (-κ * R)) atTop (𝓝 0) := by
      simpa only [mul_assoc, mul_zero] using
        (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero w.re κ hκ).const_mul C
    refine squeeze_zero_norm' ?_ ht
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := 1) (b := R) (C := C * R ^ p * Real.exp (-κ * R)) (fun x _ => by
        have hn : R ≤ ‖(x : ℂ) + R * I‖ := by simpa using im_le_norm ((x : ℂ) + R * I)
        simpa using hnorm (x + R * I) R hR0 hn)
    rw [abs_of_nonneg (sub_nonneg.mpr hR)] at hb
    calc ‖∫ x in (1 : ℝ)..R, f (x + R * I)‖ ≤
        (C * R ^ p * Real.exp (-κ * R)) * (R - 1) := hb
      _ ≤ (C * R ^ p * Real.exp (-κ * R)) * R := by gcongr; linarith
      _ = C * R ^ w.re * Real.exp (-κ * R) := by
        have he : R ^ p * R = R ^ w.re := by
          calc R ^ p * R = R ^ p * R ^ (1 : ℝ) := by rw [Real.rpow_one]
            _ = _ := by rw [← Real.rpow_add hR0]; congr 1; dsimp [p]; ring
        calc _ = C * (R ^ p * R) * Real.exp (-κ * R) := by ring
          _ = _ := by rw [he]
  have hright : Tendsto (fun R : ℝ => ∫ y in (0 : ℝ)..R, f (R + y * I)) atTop (𝓝 0) := by
    have ht : Tendsto (fun R : ℝ => C * R ^ p * κ⁻¹) atTop (𝓝 0) := by
      simpa only [p, neg_sub, mul_assoc, mul_zero, zero_mul, mul_comm, mul_left_comm] using
        (tendsto_rpow_neg_atTop (y := 1 - w.re) (by linarith)).const_mul (C * κ⁻¹)
    refine squeeze_zero_norm' ?_ ht
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
    have hb := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) hR0.le
      (g := fun y : ℝ => C * R ^ p * Real.exp (-κ * y))
      (Eventually.of_forall fun y _ => by
        have hn : R ≤ ‖(R : ℂ) + y * I‖ := by simpa using re_le_norm ((R : ℂ) + y * I)
        simpa using hnorm (R + y * I) R hR0 hn)
      (by apply Continuous.intervalIntegrable; fun_prop)
    have hexp : (∫ y in (0 : ℝ)..R, Real.exp (-κ * y)) ≤ κ⁻¹ := by
      calc (∫ y in (0 : ℝ)..R, Real.exp (-κ * y)) =
          ∫ y in Ioc (0 : ℝ) R, Real.exp (-κ * y) := intervalIntegral.integral_of_le hR0.le
        _ ≤ ∫ y in Ioi (0 : ℝ), Real.exp (-κ * y) :=
          setIntegral_mono_set (exp_neg_integrableOn_Ioi 0 hκ)
            (Eventually.of_forall fun _ => (Real.exp_pos _).le)
            (Eventually.of_forall fun _ hy => hy.1)
        _ = κ⁻¹ := by
          rw [integral_exp_mul_Ioi (neg_neg_of_pos hκ) 0]
          simp
    rw [intervalIntegral.integral_const_mul] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left hexp (by positivity))
  have hleft (y : ℝ) : f (1 + y * I) = exp (I * κ) * OscillatoryMellinTail.integrand κ w y := by
    dsimp [f, OscillatoryMellinTail.integrand]
    rw [Real.sign_of_pos hκ, abs_of_pos hκ]
    simp only [ofReal_one, mul_one]
    have he : I * (κ : ℂ) * (1 + y * I) = I * κ + ((-κ * y : ℝ) : ℂ) := by
      push_cast
      linear_combination (κ : ℂ) * y * I_sq
    rw [he, exp_add, ← ofReal_exp]
    ring
  have hleftlim : Tendsto (fun R : ℝ => I * ∫ y in (0 : ℝ)..R, f (1 + y * I)) atTop
      (𝓝 (oscillatoryMellinTail κ w)) := by
    simp_rw [hleft, intervalIntegral.integral_const_mul]
    simpa only [oscillatoryMellinTail, Real.sign_of_pos hκ, ofReal_one, mul_one, mul_assoc,
      id_eq] using
      (intervalIntegral_tendsto_integral_Ioi 0
        (OscillatoryMellinTail.integrableOn_integrand hκ.ne' w) tendsto_id).const_mul
          (I * exp (I * κ))
  have heq (R : ℝ) (hR : 1 ≤ R) : (∫ u in (1 : ℝ)..R, f u) =
      (I * ∫ y in (0 : ℝ)..R, f (1 + y * I)) +
        (∫ x in (1 : ℝ)..R, f (x + R * I)) - I * ∫ y in (0 : ℝ)..R, f (R + y * I) := by
    have hd : DifferentiableOn ℂ f (re ⁻¹' Icc 1 R) := by
      intro z hz
      have hz0 : 0 < z.re := lt_of_lt_of_le zero_lt_one hz.1
      exact (((hasDerivAt_id z).cpow_const (c := w - 1) (Or.inl hz0)).differentiableAt.mul
        (by fun_prop)).differentiableWithinAt
    have hr := integral_boundary_rect_eq_zero_of_differentiableOn f (1 : ℂ)
      ((R : ℂ) + R * I) (hd.mono fun z hz => by
        simp only [mem_reProdIm, one_re, one_im, add_re, ofReal_re, mul_re, I_re, mul_zero,
          ofReal_im, I_im, mul_one, sub_self, add_zero] at hz
        simpa only [mem_preimage, uIcc_of_le hR] using hz.1)
    simp only [one_re, one_im, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
      mul_one, sub_self, add_zero, add_im, mul_im, zero_add, zero_mul, ofReal_zero,
      ofReal_one, smul_eq_mul] at hr
    linear_combination hr
  have ht := (hleftlim.add htop).sub (hright.const_mul I)
  simp only [add_zero, mul_zero, sub_zero] at ht
  exact ht.congr' (by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    exact (heq R hR).symm)

/-- Reversing the frequency and conjugating the exponent conjugates the vertical-ray
oscillatory Mellin tail. -/
theorem oscillatoryMellinTail_neg_conj (κ : ℝ) (w : ℂ) :
    oscillatoryMellinTail (-κ) (conj w) = conj (oscillatoryMellinTail κ w) := by
  have hk (y : ℝ) : OscillatoryMellinTail.integrand (-κ) (conj w) y =
      conj (OscillatoryMellinTail.integrand κ w y) := by
    have hslit : (1 : ℂ) + I * (Real.sign κ : ℂ) * y ∈ slitPlane := Or.inl (by simp)
    have he : (1 : ℂ) + I * (Real.sign (-κ) : ℂ) * y =
        conj ((1 : ℂ) + I * (Real.sign κ : ℂ) * y) := by
      simp only [Real.sign_neg, ofReal_neg, map_add, map_mul, map_one, conj_I, conj_ofReal]
      ring
    dsimp only [OscillatoryMellinTail.integrand]
    rw [he, conj_cpow _ _ (mem_slitPlane_iff_arg.mp hslit).1]
    simp only [map_sub, conj_conj, map_one, map_mul, conj_ofReal, abs_neg]
  have hphase : I * (Real.sign (-κ) : ℂ) * exp (I * (-κ : ℝ)) =
      conj (I * (Real.sign κ : ℂ) * exp (I * κ)) := by
    simp only [Real.sign_neg, ofReal_neg, map_mul, conj_I, conj_ofReal, ← exp_conj]
    congr 1
    · ring
    · congr 1
      ring
  unfold oscillatoryMellinTail
  rw [map_mul, hphase, ← integral_conj]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y _
  exact hk y

/-- The vertical-ray model equals the real improper oscillatory Mellin integral for
`Re w < 1`, with either sign of the nonzero frequency. -/
theorem tendsto_integral_oscillatoryMellinTail {κ : ℝ} (hκ : κ ≠ 0) {w : ℂ}
    (hw : w.re < 1) :
    Tendsto (fun T : ℝ => ∫ u in (1 : ℝ)..T,
      (u : ℂ) ^ (w - 1) * exp (I * κ * u)) atTop (𝓝 (oscillatoryMellinTail κ w)) := by
  rcases lt_or_gt_of_ne hκ with hneg | hpos
  · have hp := tendsto_integral_oscillatoryMellinTail_of_pos (neg_pos.mpr hneg)
      (w := conj w) (by simpa using hw)
    have ht := continuous_conj.continuousAt.tendsto.comp hp
    rw [oscillatoryMellinTail_neg_conj, conj_conj] at ht
    refine ht.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    change conj (∫ u in (1 : ℝ)..T, (u : ℂ) ^ (conj w - 1) * exp (I * (-κ : ℝ) * u)) = _
    rw [← intervalIntegral.intervalIntegral_conj]
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hT] at hu
    have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu.1
    have harg : (u : ℂ).arg ≠ Real.pi := by
      rw [arg_ofReal_of_nonneg hu0.le]
      exact Real.pi_pos.ne
    have hpow : conj ((u : ℂ) ^ (conj w - 1)) = (u : ℂ) ^ (w - 1) := by
      simpa only [map_sub, map_one, conj_ofReal] using
        (conj_cpow (u : ℂ) (w - 1) harg).symm
    have hphase : conj (I * (-κ : ℝ) * (u : ℂ)) = I * κ * u := by
      simp only [ofReal_neg, map_mul, map_neg, conj_I, conj_ofReal]
      ring
    dsimp only
    rw [map_mul, hpow, ← exp_conj, hphase]
  · exact tendsto_integral_oscillatoryMellinTail_of_pos hpos hw

/-- At exponent one the continued tail is `i exp(iκ)/κ`. The corresponding real improper
integral is outside the convergence domain of the real-ray formula. -/
theorem oscillatoryMellinTail_one {κ : ℝ} (hκ : κ ≠ 0) :
    oscillatoryMellinTail κ 1 = I * exp (I * κ) / κ := by
  have hi : (∫ y in Ioi (0 : ℝ), OscillatoryMellinTail.integrand κ 1 y) =
      ((|κ| : ℝ) : ℂ)⁻¹ := by
    simp only [OscillatoryMellinTail.integrand, sub_self, cpow_zero, one_mul]
    rw [integral_complex_ofReal, integral_exp_mul_Ioi (neg_neg_of_pos (abs_pos.mpr hκ)) 0]
    simp
  have hs : (Real.sign κ : ℂ) * κ = ((|κ| : ℝ) : ℂ) := by
    rcases lt_or_gt_of_ne hκ with h | h
    · simp [Real.sign_of_neg h, abs_of_neg h]
    · simp [Real.sign_of_pos h, abs_of_pos h]
  rw [oscillatoryMellinTail, hi]
  have hκc : (κ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hκ
  have hac : ((|κ| : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (abs_pos.mpr hκ).ne'
  field_simp
  exact hs

/-- The real oscillatory integral at exponent one has no improper limit. -/
theorem not_tendsto_integral_exp_mul_I {κ : ℝ} (hκ : κ ≠ 0) (L : ℂ) :
    ¬ Tendsto (fun T : ℝ => ∫ u in (1 : ℝ)..T, exp (I * κ * u)) atTop (𝓝 L) := by
  intro h
  have hκc : I * (κ : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr hκ)
  have ht := (h.const_mul (I * κ)).add_const (exp (I * κ))
  apply not_tendsto_exp_mul_I_atTop hκ (I * κ * L + exp (I * κ))
  refine ht.congr fun T => ?_
  rw [integral_exp_mul_complex hκc]
  simp only [ofReal_one, mul_one]
  field_simp [ofReal_ne_zero.mpr hκ]
  <;> ring

/-- The absolutely convergent oscillatory Mellin tail, initially defined for `Re w < 0`. -/
def oscillatoryMellinTailIntegral (κ : ℝ) (w : ℂ) : ℂ :=
  ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (w - 1) * exp (I * κ * t)

/-- Absolute integrability of an oscillatory power on the tail. -/
theorem integrableOn_cpow_mul_exp_I {w : ℂ} (hw : w.re < 0) (κ : ℝ) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (w - 1) * exp (I * κ * t)) (Ioi 1) := by
  have hi : IntegrableOn (fun t : ℝ => t ^ (w.re - 1)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
  refine hi.mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
    exact (((continuous_ofReal.continuousAt).cpow continuousAt_const
      (ofReal_mem_slitPlane.mpr (lt_trans one_pos ht))).mul
        (by fun_prop)).continuousWithinAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_mul, norm_exp, norm_cpow_eq_rpow_re_of_pos (lt_trans one_pos ht)]
    simp

/-- The vertical-ray continuation agrees with the ordinary absolutely convergent integral
on `Re w < 0`. -/
theorem oscillatoryMellinTail_eq_integral {κ : ℝ} (hκ : κ ≠ 0) {w : ℂ} (hw : w.re < 0) :
    oscillatoryMellinTail κ w = oscillatoryMellinTailIntegral κ w := by
  change oscillatoryMellinTail κ w =
    ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (w - 1) * exp (I * κ * t)
  exact tendsto_nhds_unique (tendsto_integral_oscillatoryMellinTail hκ (by linarith))
    (by simpa only [id_eq] using
      (intervalIntegral_tendsto_integral_Ioi 1 (integrableOn_cpow_mul_exp_I hw κ) tendsto_id))

/-- Holomorphy of the initially convergent oscillatory tail. -/
theorem differentiableAt_oscillatoryMellinTailIntegral {w : ℂ} (hw : w.re < 0) (κ : ℝ) :
    DifferentiableAt ℂ (oscillatoryMellinTailIntegral κ) w := by
  let f : ℝ → ℂ := (Ioi (1 : ℝ)).indicator (fun t => exp (I * κ * t))
  have hc : LocallyIntegrableOn f (Ioi 0) :=
    ((Continuous.locallyIntegrable (by fun_prop :
      Continuous (fun t : ℝ => exp (I * κ * t)))).indicator
        measurableSet_Ioi).locallyIntegrableOn _
  have ht : f =O[atTop] (fun t : ℝ => t ^ (0 : ℝ)) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_gt_atTop 1] with t ht
    simp [f, ht, norm_exp]
  have hb : f =O[𝓝[>] 0] (fun t : ℝ => t ^ (-(w.re - 1))) := by
    refine (isBigO_zero _ _).congr' ?_ EventuallyEq.rfl
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    simp [f, not_lt.mpr ht.2.le]
  have hd := mellin_differentiableAt_of_isBigO_rpow (a := 0) hc
    (by simpa using ht) hw hb (sub_one_lt _)
  have he : mellin f = oscillatoryMellinTailIntegral κ := by
    funext z
    unfold mellin oscillatoryMellinTailIntegral f
    have hfun : (fun t : ℝ => (t : ℂ) ^ (z - 1) •
        (Ioi (1 : ℝ)).indicator (fun t => exp (I * κ * t)) t) =
        (Ioi (1 : ℝ)).indicator (fun t => (t : ℂ) ^ (z - 1) * exp (I * κ * t)) := by
      funext t
      by_cases ht : t ∈ Ioi (1 : ℝ) <;> simp [ht, smul_eq_mul]
    rw [hfun, integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
      inter_eq_left.mpr (Ioi_subset_Ioi zero_le_one)]
  exact he ▸ hd

/-- Integration by parts continues the oscillatory Mellin tail one unit to the right. -/
theorem oscillatoryMellinTailIntegral_recurrence {κ : ℝ} (hκ : κ ≠ 0) {w : ℂ}
    (hw : w.re < 0) :
    oscillatoryMellinTailIntegral κ w = -exp (I * κ) / (I * κ) -
      (w - 1) / (I * κ) * oscillatoryMellinTailIntegral κ (w - 1) := by
  let u : ℝ → ℂ := fun t => (t : ℂ) ^ (w - 1)
  let v : ℝ → ℂ := fun t => exp (I * κ * t) / (I * κ)
  have hκc : I * (κ : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr hκ)
  have hu (t : ℝ) (ht : t ∈ Ioi 1) :
      HasDerivAt u ((w - 1) * (t : ℂ) ^ (w - 1 - 1)) t := by
    simpa [u] using (((hasDerivAt_id (t : ℂ)).cpow_const
      (c := w - 1) (ofReal_mem_slitPlane.mpr (lt_trans one_pos ht))).comp_ofReal)
  have hv (t : ℝ) (_ : t ∈ Ioi 1) : HasDerivAt v (exp (I * κ * t)) t := by
    convert ((((hasDerivAt_id (t : ℂ)).const_mul (I * κ)).cexp.div_const
      (I * κ)).comp_ofReal) using 1 <;> dsimp [v]
    field_simp [hκ]
  have hi := integrableOn_cpow_mul_exp_I hw κ
  have hi' := (integrableOn_cpow_mul_exp_I (w := w - 1)
    (by simp; linarith) κ).const_mul ((w - 1) / (I * κ))
  have hzero : Tendsto (u * v) (𝓝[>] (1 : ℝ)) (𝓝 (exp (I * κ) / (I * κ))) := by
    have hc : ContinuousAt (u * v) 1 := by
      refine ContinuousAt.mul ?_ (by dsimp [v]; fun_prop)
      exact (continuous_ofReal.continuousAt).cpow continuousAt_const
        (ofReal_mem_slitPlane.mpr one_pos)
    simpa [u, v] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hinf : Tendsto (u * v) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_
      (by simpa using (tendsto_rpow_neg_atTop (y := 1 - w.re)
        (by linarith)).div_const ‖I * (κ : ℂ)‖)
    filter_upwards [eventually_gt_atTop 0] with t ht
    simp [u, v, norm_mul, norm_div, norm_exp, norm_cpow_eq_rpow_re_of_pos ht,
      div_eq_mul_inv]
  have h := integral_Ioi_mul_deriv_eq_deriv_mul hu hv hi
    (by
      apply Integrable.congr hi'
      filter_upwards [] with t
      dsimp [v]
      ring) hzero hinf
  dsimp [u, v] at h
  rw [show (fun t : ℝ => (w - 1) * (t : ℂ) ^ (w - 1 - 1) *
      (exp (I * κ * t) / (I * κ))) =
      (fun t : ℝ => ((w - 1) / (I * κ)) *
        ((t : ℂ) ^ ((w - 1) - 1) * exp (I * κ * t))) by funext t; ring,
    integral_const_mul] at h
  simpa [oscillatoryMellinTailIntegral, neg_div] using h

/-- A nonzero real frequency gives an entire continuation of the oscillatory Mellin tail.
The equality on the initial half-plane is an equality of absolutely convergent integrals. -/
theorem exists_entire_oscillatoryMellinTail {κ : ℝ} (hκ : κ ≠ 0) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
      ∀ w : ℂ, w.re < 0 → F w = oscillatoryMellinTailIntegral κ w := by
  exact ⟨oscillatoryMellinTail κ, differentiable_oscillatoryMellinTail hκ,
    fun w hw => oscillatoryMellinTail_eq_integral hκ hw⟩

/-- Multiplying by a power and making a positive real power substitution in an oscillatory
tail gives its Mellin transform in the half-plane of absolute convergence. -/
theorem hasMellin_indicator_exp_I_mul_rpow_cpow {κ p : ℝ} (hp : 0 < p) {β z : ℂ}
    (hz : z.re < β.re) :
    HasMellin ((Ioi (1 : ℝ)).indicator
      (fun t => exp (I * κ * (t ^ p : ℝ)) * (t : ℂ) ^ (-β))) z
      ((p : ℂ)⁻¹ * oscillatoryMellinTailIntegral κ ((z - β) / p)) := by
  let f : ℝ → ℂ := (Ioi (1 : ℝ)).indicator (fun t => exp (I * κ * t))
  have hw : ((z - β) / p).re < 0 := by
    rw [div_ofReal_re, sub_re]
    exact div_neg_of_neg_of_pos (sub_neg.mpr hz) hp
  have hi : MellinConvergent f ((z - β) / p) := by
    unfold MellinConvergent f
    have he : (fun t : ℝ => (t : ℂ) ^ (((z - β) / p) - 1) •
        (Ioi (1 : ℝ)).indicator (fun t => exp (I * κ * t)) t) =
        (Ioi (1 : ℝ)).indicator
          (fun t => (t : ℂ) ^ (((z - β) / p) - 1) * exp (I * κ * t)) := by
      funext t
      by_cases ht : t ∈ Ioi (1 : ℝ) <;> simp [ht, smul_eq_mul]
    rw [he]
    exact ((integrableOn_cpow_mul_exp_I hw κ).integrable_indicator
      measurableSet_Ioi).integrableOn
  have he : mellin f ((z - β) / p) =
      oscillatoryMellinTailIntegral κ ((z - β) / p) := by
    unfold mellin oscillatoryMellinTailIntegral f
    simp_rw [← indicator_smul]
    rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
      inter_eq_left.mpr (Ioi_subset_Ioi zero_le_one)]
    rfl
  have heq (t : ℝ) (ht0 : 0 < t) : ((Ioi (1 : ℝ)).indicator
      (fun t => exp (I * κ * (t ^ p : ℝ)) * (t : ℂ) ^ (-β))) t =
      (t : ℂ) ^ (-β) • f (t ^ p) := by
    have hiff : 1 < t ^ p ↔ 1 < t := by
      simpa [hp, not_lt.mpr hp.le] using Real.one_lt_rpow_iff ht0.le (y := p)
    by_cases ht : 1 < t <;> simp [f, ht, hiff, smul_eq_mul, mul_comm]
  have hi' : MellinConvergent (fun t => (t : ℂ) ^ (-β) • f (t ^ p)) z := by
    apply MellinConvergent.cpow_smul.mpr
    simpa only [sub_eq_add_neg] using (MellinConvergent.comp_rpow hp.ne').mpr hi
  refine ⟨hi'.congr_fun (fun t ht => by rw [heq t ht]) measurableSet_Ioi, ?_⟩
  · rw [show mellin ((Ioi (1 : ℝ)).indicator
        (fun t => exp (I * κ * (t ^ p : ℝ)) * (t : ℂ) ^ (-β))) z =
        mellin (fun t => (t : ℂ) ^ (-β) • f (t ^ p)) z by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [heq t ht],
      mellin_cpow_smul, mellin_comp_rpow, show z + -β = z - β by ring, he]
    simp [abs_of_pos hp, smul_eq_mul]

end Complex
