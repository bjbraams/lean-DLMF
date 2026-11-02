/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ExpIntegrals.TransformTools.LaplaceAndFourier

/-!
# Quadratic moments of exponential integrals

Squared and product integrals of `E₁`, `Ci` and `Si - π/2` over `(0, ∞)` (DLMF 6.14.4–6.14.7),
by integration by parts and explicit antiderivatives, and the auxiliary-function sums used for
DLMF §6.15, evaluated through Binet's formulas: the digamma kernel integral DLMF 5.9.15
(`DLMF.Gamma.digamma_coth`) and Binet's second formula DLMF 5.9.10
(`DLMF.Gamma.log_Gamma_binet_arctan`).

## Main definitions

* `ExpIntegralTransforms.realE1`: the real `E₁`, through `Ein`, defined for all real `t`.
* `ExpIntegralTransforms.realAuxF`, `ExpIntegralTransforms.realAuxG`: the real auxiliary functions
  `f(x)`, `g(x)` as Laplace integrals.
* `ExpIntegralTransforms.cosSiSinCiPrimitive`: the primitive of `cos t si(t) + sin t Ci(t)`,
  continuous at `0`.

## Main results

* `ExpIntegralTransforms.integral_cosInt_sq`, `ExpIntegralTransforms.integral_sinIntTail_sq`:
  `∫₀^∞ Ci² = ∫₀^∞ (Si - π/2)² = π/2`.
* `ExpIntegralTransforms.integral_cosInt_mul_sinIntTail`: `∫₀^∞ Ci(t) (Si(t) - π/2) dt = log 2`.
* `ExpIntegralTransforms.integral_realE1_sq`: `∫₀^∞ E₁(t)² dt = 2 log 2`.
* `ExpIntegralTransforms.hasSum_realAuxG`, `ExpIntegralTransforms.hasSum_realAuxF`: alternating sums
  of the auxiliary functions as Fermi-type integrals.
* `ExpIntegralTransforms.binetKernel_eq`, `ExpIntegralTransforms.arctanKernel_eq`,
  `ExpIntegralTransforms.integral_log_eq'`: evaluation of the resulting kernels through Binet's
  formulas.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics DLMF

open scoped Real Topology Nat

namespace DLMF.Confluent

/-- `t · Ci(t)² → 0` as `t → 0⁺`. -/
theorem ExpIntegralTransforms.tendsto_mul_cosInt_sq :
    Tendsto (fun t => t * Real.cosInt t ^ 2) (𝓝[>] 0) (𝓝 0) := by
  set c : ℝ → ℝ := fun t => -Real.cosIntCin t + Real.eulerMascheroniConstant
  have hc : Continuous c := ExpIntegralTransforms.continuous_cosIntCin.neg.add continuous_const
  have e : ∀ t, 0 < t → t * Real.cosInt t ^ 2 =
      t * c t ^ 2 + 2 * c t * (t * Real.log t) + (Real.log t * t ^ (1/2:ℝ)) ^ 2 := by
    intro t ht
    have : (t ^ (1/2:ℝ)) ^ 2 = t := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]; norm_num
    rw [mul_pow, this, Real.cosInt]; ring
  have h1 : Tendsto (fun t => t * c t ^ 2) (𝓝[>] 0) (𝓝 (0 * c 0 ^ 2)) :=
    ((continuous_id.mul (hc.pow 2)).tendsto 0).mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun t => 2 * c t * (t * Real.log t)) (𝓝[>] 0)
      (𝓝 (2 * c 0 * (0 * Real.log 0))) :=
    (((continuous_const.mul hc).mul Real.continuous_mul_log).tendsto 0).mono_left nhdsWithin_le_nhds
  have h3 := (tendsto_log_mul_rpow_nhdsGT_zero (by norm_num : (0:ℝ) < 1/2)).pow 2
  have := (h1.add h2).add h3
  simp only [zero_mul, mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (e t ht).symm

/-- `t ↦ t · Ci(t)²` is continuous on `[0, R]`. -/
theorem ExpIntegralTransforms.continuousOn_mul_cosInt_sq (R : ℝ) :
    ContinuousOn (fun t => t * Real.cosInt t ^ 2) (Icc 0 R) := by
  intro x hx
  rcases eq_or_lt_of_le hx.1 with h | h
  · subst h
    have : ContinuousWithinAt (fun t => t * Real.cosInt t ^ 2) (Ici 0) 0 := by
      rw [← continuousWithinAt_Ioi_iff_Ici, ContinuousWithinAt]
      simpa using ExpIntegralTransforms.tendsto_mul_cosInt_sq
    exact this.mono Icc_subset_Ici_self
  · exact (continuousAt_id.mul
        ((ExpIntegralTransforms.continuousAt_cosInt h).pow 2)).continuousWithinAt

/-- Integration by parts: `∫₀^R Ci² = R Ci(R)² - 2 ∫₀^R cos t · Ci(t) dt`. -/
theorem ExpIntegralTransforms.integral_cosInt_sq_eq {R : ℝ} (hR : 0 ≤ R) :
    ∫ t in (0:ℝ)..R, Real.cosInt t ^ 2 =
      R * Real.cosInt R ^ 2 - 2 * ∫ t in (0:ℝ)..R, Real.cos t * Real.cosInt t := by
  have hi1 : IntervalIntegrable (fun t => Real.cosInt t ^ 2) volume 0 R := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hR]
    exact ExpIntegralTransforms.integrableOn_cosInt_sq.mono_set Ioc_subset_Ioi_self
  have hi2 := (ExpIntegralTransforms.intervalIntegrable_cos_mul_cosInt R).const_mul 2
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hR
    (ExpIntegralTransforms.continuousOn_mul_cosInt_sq R) (f' := fun t => Real.cosInt t ^ 2 +
      2 * (Real.cos t * Real.cosInt t)) (fun x hx => ?_) (hi1.add hi2)
  · rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_const_mul] at h
    simp only [zero_mul, sub_zero] at h
    linarith
  · have hx0 : 0 < x := hx.1
    have := (hasDerivAt_id x).mul ((Real.hasDerivAt_cosInt hx0).pow 2)
    refine this.congr_deriv ?_
    simp only [id, one_mul, Nat.cast_ofNat, Pi.pow_apply]
    field_simp
    ring

/-- `∫₀^∞ Ci(t)² dt = π/2`. -/
theorem ExpIntegralTransforms.integral_cosInt_sq : ∫ t in Ioi (0:ℝ), Real.cosInt t ^ 2 = π / 2 := by
  have hlim := intervalIntegral_tendsto_integral_Ioi 0
      ExpIntegralTransforms.integrableOn_cosInt_sq tendsto_id
  refine tendsto_nhds_unique hlim ?_
  have h1 : Tendsto (fun R => R * Real.cosInt R ^ 2) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ ((tendsto_const_nhds (x := (4:ℝ))).div_atTop tendsto_id)
    filter_upwards [eventually_gt_atTop 0] with R hR
    have h := ExpIntegralTransforms.abs_cosInt_le hR
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hR, abs_of_nonneg (sq_nonneg _), ← sq_abs]
    calc R * |Real.cosInt R| ^ 2 ≤ R * (2 / R) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) h 2) hR.le
      _ = 4 / id R := by simp only [id]; field_simp; ring
  have := h1.sub (ExpIntegralTransforms.tendsto_integral_cos_mul_cosInt.const_mul 2)
  rw [show (0:ℝ) - 2 * -(π / 4) = π / 2 by ring] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with R hR
  simp only [id]
  rw [ExpIntegralTransforms.integral_cosInt_sq_eq hR]

/-- `t ↦ Si(t) - π/2` is continuous. -/
theorem ExpIntegralTransforms.continuous_sinIntTail : Continuous fun t => Real.sinInt t - π / 2 :=
  ExpIntegralTransforms.continuous_sinInt.sub continuous_const

/-- `(Si - π/2)²` is integrable on `(0, ∞)`. -/
theorem ExpIntegralTransforms.integrableOn_sinIntTail_sq :
    IntegrableOn (fun t => (Real.sinInt t - π / 2) ^ 2) (Ioi 0) := by
  refine ExpIntegralTransforms.integrableOn_Ioi_of_bound (A := 9) (B := 0) (C := 4)
    (ExpIntegralTransforms.continuous_sinIntTail.pow 2).aestronglyMeasurable (fun t ht => ?_)
        (fun t ht => ?_)
  · have h := ExpIntegralTransforms.abs_sinIntTail_le_small ht.1.le ht.2
    rw [abs_of_nonneg (sq_nonneg _), ← sq_abs, zero_mul, add_zero]
    calc |Real.sinInt t - π / 2| ^ 2 ≤ 3 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
      _ = 9 := by norm_num
  · have h := ExpIntegralTransforms.abs_sinIntTail_le (by linarith : (0:ℝ) < t)
    rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
    calc |Real.sinInt t - π / 2| ^ 2 ≤ (2 / t) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
      _ = 4 / t ^ 2 := by ring

/-- Integration by parts: `∫₀^R (Si - π/2)² = R (Si(R) - π/2)² - 2 ∫₀^R sin t (Si(t) - π/2) dt`. -/
theorem ExpIntegralTransforms.integral_sinIntTail_sq_eq (R : ℝ) :
    ∫ t in (0:ℝ)..R, (Real.sinInt t - π / 2) ^ 2 =
      R * (Real.sinInt R - π / 2) ^ 2 -
        2 * ∫ t in (0:ℝ)..R, Real.sin t * (Real.sinInt t - π / 2) := by
  have hi1 : IntervalIntegrable (fun t => (Real.sinInt t - π / 2) ^ 2) volume 0 R :=
    (ExpIntegralTransforms.continuous_sinIntTail.pow 2).intervalIntegrable 0 R
  have hi2 : IntervalIntegrable (fun t => 2 * (Real.sin t * (Real.sinInt t - π / 2))) volume 0 R :=
    ((Real.continuous_sin.mul ExpIntegralTransforms.continuous_sinIntTail).intervalIntegrable
        0 R).const_mul 2
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t => t * (Real.sinInt t - π / 2) ^ 2) (f' := fun t => (Real.sinInt t - π / 2) ^ 2 +
      2 * (Real.sin t * (Real.sinInt t - π / 2))) (fun x _ => ?_) (hi1.add hi2)
  · rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_const_mul] at h
    simp only [zero_mul, sub_zero] at h
    linarith
  · have := (hasDerivAt_id x).mul (((Real.hasDerivAt_sinInt x).sub_const (π / 2)).pow 2)
    refine this.congr_deriv ?_
    simp only [id, one_mul, Nat.cast_ofNat, Pi.pow_apply]
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    rw [Real.sinc_of_ne_zero hx]
    field_simp
    ring

/-- `∫₀^∞ (Si(t) - π/2)² dt = π/2`. -/
theorem ExpIntegralTransforms.integral_sinIntTail_sq : ∫ t in Ioi (0:ℝ),
    (Real.sinInt t - π / 2) ^ 2 = π / 2 := by
  have hlim := intervalIntegral_tendsto_integral_Ioi 0
      ExpIntegralTransforms.integrableOn_sinIntTail_sq tendsto_id
  refine tendsto_nhds_unique hlim ?_
  have h1 : Tendsto (fun R => R * (Real.sinInt R - π / 2) ^ 2) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ ((tendsto_const_nhds (x := (4:ℝ))).div_atTop tendsto_id)
    filter_upwards [eventually_gt_atTop 0] with R hR
    have h := ExpIntegralTransforms.abs_sinIntTail_le hR
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hR, abs_of_nonneg (sq_nonneg _), ← sq_abs]
    calc R * |Real.sinInt R - π / 2| ^ 2 ≤ R * (2 / R) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) h 2) hR.le
      _ = 4 / id R := by simp only [id]; field_simp; ring
  have := h1.sub (ExpIntegralTransforms.tendsto_integral_sin_mul_sinIntTail.const_mul 2)
  rw [show (0:ℝ) - 2 * -(π / 4) = π / 2 by ring] at this
  refine this.congr' (Eventually.of_forall fun R => ?_)
  simp only [id]
  rw [ExpIntegralTransforms.integral_sinIntTail_sq_eq R]

/-- The primitive of `cos t si(t) + sin t Ci(t)`, continuous at `0`. -/
noncomputable def ExpIntegralTransforms.cosSiSinCiPrimitive (t : ℝ) : ℝ :=
  Real.sin t * (Real.sinInt t - π / 2) - Real.cos t *
      (-Real.cosIntCin t + Real.eulerMascheroniConstant) +
    (-Real.cosIntCin (2 * t) + Real.eulerMascheroniConstant) + Real.log 2 +
    Real.sin (t / 2) * Real.sinc (t / 2) * (t * Real.log t)

/-- Explicit formula for `ExpIntegralTransforms.cosSiSinCiPrimitive` at `t > 0`. -/
theorem ExpIntegralTransforms.cosSiSinCiPrimitive_eq {t : ℝ} (ht : 0 < t) :
    ExpIntegralTransforms.cosSiSinCiPrimitive t =
    Real.sin t * (Real.sinInt t - π / 2) - Real.cos t * Real.cosInt t + Real.cosInt (2 * t) := by
  have h1 : Real.sin (t / 2) * Real.sinc (t / 2) * (t * Real.log t) =
      (1 - Real.cos t) * Real.log t := by
    rw [Real.sinc_of_ne_zero (by positivity)]
    have : Real.cos t = 1 - 2 * Real.sin (t / 2) ^ 2 := by
      have h2 := Real.cos_two_mul (t / 2)
      rw [show 2 * (t / 2) = t by ring] at h2
      rw [h2, Real.cos_sq']; ring
    rw [this]; field_simp; ring
  rw [ExpIntegralTransforms.cosSiSinCiPrimitive, h1, Real.cosInt, Real.cosInt,
      Real.log_mul (by norm_num) ht.ne']
  ring

/-- `ExpIntegralTransforms.cosSiSinCiPrimitive` is continuous. -/
theorem ExpIntegralTransforms.continuous_cosSiSinCiPrimitive : Continuous
    ExpIntegralTransforms.cosSiSinCiPrimitive := by
  unfold ExpIntegralTransforms.cosSiSinCiPrimitive
  have hc := ExpIntegralTransforms.continuous_cosIntCin
  have hs := ExpIntegralTransforms.continuous_sinInt
  have hl := Real.continuous_mul_log
  fun_prop

/-- Derivative of `ExpIntegralTransforms.cosSiSinCiPrimitive`: `cos x (Si(x) - π/2) + sin x Ci(x)`
for `x > 0`. -/
theorem ExpIntegralTransforms.hasDerivAt_cosSiSinCiPrimitive {x : ℝ} (hx : 0 < x) :
    HasDerivAt ExpIntegralTransforms.cosSiSinCiPrimitive
        (Real.cos x * (Real.sinInt x - π / 2) + Real.sin x * Real.cosInt x) x := by
  have hev : ExpIntegralTransforms.cosSiSinCiPrimitive =ᶠ[𝓝 x] fun t =>
      Real.sin t * (Real.sinInt t - π / 2) - Real.cos t * Real.cosInt t + Real.cosInt (2 * t) := by
    filter_upwards [lt_mem_nhds hx] with t ht using ExpIntegralTransforms.cosSiSinCiPrimitive_eq ht
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  have h1 := (Real.hasDerivAt_sin x).mul ((Real.hasDerivAt_sinInt x).sub_const (π / 2))
  have h2 := (Real.hasDerivAt_cos x).mul (Real.hasDerivAt_cosInt hx)
  have h3 := (Real.hasDerivAt_cosInt (by positivity : 0 < 2 * x)).comp x
    ((hasDerivAt_id x).const_mul 2)
  refine ((h1.sub h2).add h3).congr_deriv ?_
  rw [Real.sinc_of_ne_zero hx.ne', Real.cos_two_mul]
  simp only [mul_one]
  have := Real.sin_sq_add_cos_sq x
  field_simp
  nlinarith [this]

/-- `ExpIntegralTransforms.cosSiSinCiPrimitive 0 = log 2`. -/
theorem ExpIntegralTransforms.cosSiSinCiPrimitive_zero : ExpIntegralTransforms.cosSiSinCiPrimitive 0
    = Real.log 2 := by
  simp [ExpIntegralTransforms.cosSiSinCiPrimitive, Real.cosIntCin]

/-- `ExpIntegralTransforms.cosSiSinCiPrimitive(t) → 0` as `t → ∞`. -/
theorem ExpIntegralTransforms.tendsto_cosSiSinCiPrimitive : Tendsto
    ExpIntegralTransforms.cosSiSinCiPrimitive atTop (𝓝 0) := by
  have hb : ∀ (f g : ℝ → ℝ), (∀ x, |f x| ≤ 1) → Tendsto g atTop (𝓝 0) →
      Tendsto (fun x => f x * g x) atTop (𝓝 0) := fun f g hf hg => by
    refine squeeze_zero_norm (a := fun x => ‖g x‖) (fun x => ?_) (by simpa using hg.norm)
    rw [norm_mul, Real.norm_eq_abs (f x)]
    exact mul_le_of_le_one_left (norm_nonneg _) (hf x)
  have h1 := hb _ _ Real.abs_sin_le_one ExpIntegralTransforms.tendsto_sinIntTail_real
  have h2 := hb _ _ Real.abs_cos_le_one ExpIntegralTransforms.tendsto_cosInt_real
  have h3 := ExpIntegralTransforms.tendsto_cosInt_real.comp (tendsto_id.const_mul_atTop two_pos)
  have := (h1.sub h2).add h3
  simp only [sub_zero, add_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [ExpIntegralTransforms.cosSiSinCiPrimitive_eq ht]; rfl

/-- `∫₀^R (cos t (Si(t) - π/2) + sin t Ci(t)) dt = ExpIntegralTransforms.cosSiSinCiPrimitive R - log
2`. -/
theorem ExpIntegralTransforms.integral_cos_si_add_sin_ci {R : ℝ} (hR : 0 ≤ R) :
    ∫ t in (0:ℝ)..R, (Real.cos t * (Real.sinInt t - π / 2) + Real.sin t * Real.cosInt t) =
      ExpIntegralTransforms.cosSiSinCiPrimitive R - Real.log 2 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hR
      ExpIntegralTransforms.continuous_cosSiSinCiPrimitive.continuousOn
    (fun x hx => ExpIntegralTransforms.hasDerivAt_cosSiSinCiPrimitive hx.1)
    (((Real.continuous_cos.mul ExpIntegralTransforms.continuous_sinIntTail).add
      ExpIntegralTransforms.continuous_sin_mul_cosInt).intervalIntegrable 0 R),
          ExpIntegralTransforms.cosSiSinCiPrimitive_zero]

/-- `Ci · (Si - π/2)` is integrable on `(0, ∞)`. -/
theorem ExpIntegralTransforms.integrableOn_cosInt_mul_sinIntTail :
    IntegrableOn (fun t => Real.cosInt t * (Real.sinInt t - π / 2)) (Ioi 0) := by
  refine ExpIntegralTransforms.integrableOn_Ioi_of_bound (A := 6) (B := 12) (C := 4)
    (ExpIntegralTransforms.measurable_cosInt.mul
        ExpIntegralTransforms.continuous_sinIntTail.measurable).aestronglyMeasurable
    (fun t ht => ?_) (fun t ht => ?_)
  · have h := ExpIntegralTransforms.abs_cosInt_le_small ht.1 ht.2
    have h' := ExpIntegralTransforms.abs_sinIntTail_le_small ht.1.le ht.2
    have h1 := ExpIntegralTransforms.rpow_quarter_le ht.1 ht.2
    rw [abs_mul]
    calc |Real.cosInt t| * |Real.sinInt t - π / 2| ≤ (2 + 4 * t ^ (-(1/4:ℝ))) * 3 :=
          mul_le_mul h h' (abs_nonneg _)
            (by have := Real.rpow_nonneg ht.1.le (-(1/4:ℝ)); linarith)
      _ ≤ 6 + 12 * t ^ (-(1/2:ℝ)) := by nlinarith
  · have ht0 : (0:ℝ) < t := by linarith
    have h := ExpIntegralTransforms.abs_cosInt_le ht0
    have h' := ExpIntegralTransforms.abs_sinIntTail_le ht0
    rw [abs_mul]
    calc |Real.cosInt t| * |Real.sinInt t - π / 2| ≤ (2 / t) * (2 / t) :=
          mul_le_mul h h' (abs_nonneg _) (by positivity)
      _ = 4 / t ^ 2 := by ring

/-- Integration by parts for `∫₀^R Ci(t) (Si(t) - π/2) dt`. -/
theorem ExpIntegralTransforms.integral_cosInt_mul_sinIntTail_eq {R : ℝ} (hR : 0 ≤ R) :
    ∫ t in (0:ℝ)..R, Real.cosInt t * (Real.sinInt t - π / 2) =
      R * Real.cosInt R * (Real.sinInt R - π / 2) -
          (ExpIntegralTransforms.cosSiSinCiPrimitive R - Real.log 2) := by
  have hi1 : IntervalIntegrable (fun t => Real.cosInt t * (Real.sinInt t - π / 2)) volume 0 R := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hR]
    exact ExpIntegralTransforms.integrableOn_cosInt_mul_sinIntTail.mono_set Ioc_subset_Ioi_self
  have hi2 : IntervalIntegrable
      (fun t => Real.cos t * (Real.sinInt t - π / 2) + Real.sin t * Real.cosInt t) volume 0 R :=
    ((Real.continuous_cos.mul ExpIntegralTransforms.continuous_sinIntTail).add
      ExpIntegralTransforms.continuous_sin_mul_cosInt).intervalIntegrable 0 R
  have hc : Continuous fun t => t * Real.cosInt t * (Real.sinInt t - π / 2) :=
    ExpIntegralTransforms.continuous_mul_cosInt.mul ExpIntegralTransforms.continuous_sinIntTail
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hR hc.continuousOn
    (f' := fun t => Real.cosInt t * (Real.sinInt t - π / 2) +
      (Real.cos t * (Real.sinInt t - π / 2) + Real.sin t * Real.cosInt t)) (fun x hx => ?_)
    (hi1.add hi2)
  · rw [intervalIntegral.integral_add hi1 hi2,
        ExpIntegralTransforms.integral_cos_si_add_sin_ci hR] at h
    simp only [zero_mul, sub_zero] at h
    linarith
  · have hx0 : 0 < x := hx.1
    have := ((hasDerivAt_id x).mul (Real.hasDerivAt_cosInt hx0)).mul
      ((Real.hasDerivAt_sinInt x).sub_const (π / 2))
    refine this.congr_deriv ?_
    rw [Real.sinc_of_ne_zero hx0.ne']
    simp only [id, one_mul, Pi.mul_apply]
    field_simp
    ring

/-- `∫₀^∞ Ci(t) (Si(t) - π/2) dt = log 2`. -/
theorem ExpIntegralTransforms.integral_cosInt_mul_sinIntTail :
    ∫ t in Ioi (0:ℝ), Real.cosInt t * (Real.sinInt t - π / 2) = Real.log 2 := by
  have hlim := intervalIntegral_tendsto_integral_Ioi 0
      ExpIntegralTransforms.integrableOn_cosInt_mul_sinIntTail
    tendsto_id
  refine tendsto_nhds_unique hlim ?_
  have h1 : Tendsto (fun R => R * Real.cosInt R * (Real.sinInt R - π / 2)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ ((tendsto_const_nhds (x := (4:ℝ))).div_atTop tendsto_id)
    filter_upwards [eventually_gt_atTop 0] with R hR
    have h := ExpIntegralTransforms.abs_cosInt_le hR
    have h' := ExpIntegralTransforms.abs_sinIntTail_le hR
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hR]
    calc R * |Real.cosInt R| * |Real.sinInt R - π / 2| ≤ R * (2 / R) * (2 / R) := by
          gcongr
      _ = 4 / id R := by simp only [id]; field_simp; ring
  have := h1.sub (ExpIntegralTransforms.tendsto_cosSiSinCiPrimitive.sub_const (Real.log 2))
  rw [show (0:ℝ) - (0 - Real.log 2) = Real.log 2 by ring] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with R hR
  simp only [id]
  rw [ExpIntegralTransforms.integral_cosInt_mul_sinIntTail_eq hR]

/-- Real `E₁` through `Ein`, defined for all real `t`. -/
noncomputable def ExpIntegralTransforms.realE1 (t : ℝ) : ℝ := Real.expIntEin t - Real.log t -
    Real.eulerMascheroniConstant

/-- The entire exponential integral `Ein` is continuous on `ℝ`. -/
theorem ExpIntegralTransforms.continuous_expIntEin : Continuous Real.expIntEin := by
  have h : Real.expIntEin = fun x : ℝ => (expIntEin (x:ℂ)).re := by
    funext x; rw [expIntEin_ofReal]; simp
  rw [h]
  exact Complex.continuous_re.comp (expIntEin_entire.continuous.comp continuous_ofReal)

/-- `E₁(t)` equals the real function `ExpIntegralTransforms.realE1 t` for `t > 0`. -/
theorem ExpIntegralTransforms.E1_ofReal {t : ℝ} (ht : 0 < t) : genExpIntE 1 t =
    (ExpIntegralTransforms.realE1 t : ℂ) :=
  genExpIntE_one_eq_Ein ht

/-- Derivative of the real `E₁`: `-e^{-x}/x` for `x > 0`. -/
theorem ExpIntegralTransforms.hasDerivAt_realE1 {x : ℝ} (hx : 0 < x) : HasDerivAt
    ExpIntegralTransforms.realE1 (-Real.exp (-x) / x) x := by
  have := ((LogIntegralPrincipalValue.hasDerivAt_ein hx.ne').sub
      (Real.hasDerivAt_log hx.ne')).sub_const
    Real.eulerMascheroniConstant
  refine this.congr_deriv ?_
  field_simp; ring

/-- `0 ≤ E₁(t) ≤ e^{-t}/t` for `t > 0`. -/
theorem ExpIntegralTransforms.realE1_bounds {t : ℝ} (ht : 0 < t) : 0 ≤
    ExpIntegralTransforms.realE1 t ∧ ExpIntegralTransforms.realE1 t ≤ Real.exp (-t) / t := by
  have h := genExpIntE_one_eq_integral ht
  rw [ExpIntegralTransforms.E1_ofReal ht, ofReal_inj] at h
  rw [h]
  have hi := integrableOn_exp_neg_div ht
  constructor
  · refine setIntegral_nonneg measurableSet_Ioi fun s hs => ?_
    have : (0:ℝ) < s := lt_trans ht hs
    positivity
  · have he := exp_neg_integrableOn_Ioi t one_pos
    simp only [neg_mul, one_mul] at he
    have hi2 : IntegrableOn (fun s : ℝ => Real.exp (-s) / t) (Ioi t) := he.div_const t
    calc ∫ s in Ioi t, Real.exp (-s) / s ≤ ∫ s in Ioi t, Real.exp (-s) / t :=
          setIntegral_mono_on hi hi2 measurableSet_Ioi fun s hs =>
            div_le_div_of_nonneg_left (Real.exp_pos _).le ht (le_of_lt hs)
      _ = Real.exp (-t) / t := by rw [integral_div, integral_exp_neg_Ioi]

/-- `|Ein(t)| ≤ 1` for `0 ≤ t ≤ 1`. -/
theorem ExpIntegralTransforms.abs_expIntEin_le {t : ℝ} (ht : 0 ≤ t)
    (ht1 : t ≤ 1) : |Real.expIntEin t| ≤ 1 := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t) (C := 1)
    (f := fun s : ℝ => (1 - Real.exp (-s)) / s) (fun s hs => ?_)
  · rw [Real.expIntEin, ← Real.norm_eq_abs]
    calc _ ≤ 1 * |t - 0| := h
      _ ≤ 1 := by rw [sub_zero, abs_of_nonneg ht]; linarith
  · rw [uIoc_of_le ht] at hs
    have hs0 : 0 < s := hs.1
    have h1 := Real.add_one_le_exp (-s)
    have h2 : Real.exp (-s) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hs0, abs_of_pos (by linarith), div_le_one hs0]
    linarith

/-- `|E₁(t)| ≤ 2 + 4 t^{-1/4}` for `0 < t ≤ 1`. -/
theorem ExpIntegralTransforms.abs_realE1_le_small {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    |ExpIntegralTransforms.realE1 t| ≤ 2 + 4 * t ^ (-(1/4:ℝ)) := by
  have h1 := ExpIntegralTransforms.abs_expIntEin_le ht.le ht1
  have h2 := ExpIntegralTransforms.abs_log_le ht ht1
  have h3 := Real.eulerMascheroniConstant_lt_two_thirds
  have h4 := Real.one_half_lt_eulerMascheroniConstant
  rw [ExpIntegralTransforms.realE1]
  calc |Real.expIntEin t - Real.log t - Real.eulerMascheroniConstant|
      ≤ |Real.expIntEin t| + |Real.log t| + |Real.eulerMascheroniConstant| := by
        have := abs_sub (Real.expIntEin t - Real.log t) Real.eulerMascheroniConstant
        have := abs_sub (Real.expIntEin t) (Real.log t)
        linarith
    _ ≤ 2 + 4 * t ^ (-(1/4:ℝ)) := by
        rw [abs_of_pos (by linarith : (0:ℝ) < Real.eulerMascheroniConstant)]; linarith

/-- `|E₁(t)| ≤ 1/t` for `t ≥ 1`. -/
theorem ExpIntegralTransforms.realE1_le_recip {t : ℝ} (ht : 1 ≤ t) : |ExpIntegralTransforms.realE1
    t| ≤ 1 / t := by
  have ht0 : 0 < t := by linarith
  obtain ⟨h1, h2⟩ := ExpIntegralTransforms.realE1_bounds ht0
  rw [abs_of_nonneg h1]
  refine h2.trans (div_le_div_of_nonneg_right ?_ ht0.le)
  exact Real.exp_le_one_iff.2 (by linarith)

/-- The real `E₁` is measurable. -/
theorem ExpIntegralTransforms.measurable_realE1 : Measurable ExpIntegralTransforms.realE1 := by
  unfold ExpIntegralTransforms.realE1
  exact (ExpIntegralTransforms.continuous_expIntEin.measurable.sub Real.measurable_log).sub_const _

/-- `E₁²` is integrable on `(0, ∞)`. -/
theorem ExpIntegralTransforms.integrableOn_realE1_sq : IntegrableOn
    (fun t => ExpIntegralTransforms.realE1 t ^ 2) (Ioi 0) := by
  refine ExpIntegralTransforms.integrableOn_Ioi_of_bound (A := 4) (B := 32) (C := 1)
    (ExpIntegralTransforms.measurable_realE1.pow_const 2).aestronglyMeasurable (fun t ht => ?_)
        (fun t ht => ?_)
  · have h := ExpIntegralTransforms.abs_realE1_le_small ht.1 ht.2
    have h1 := ExpIntegralTransforms.rpow_quarter_le ht.1 ht.2
    have h2 := ExpIntegralTransforms.one_le_rpow ht.1 ht.2
    have hq : (t ^ (-(1/4:ℝ))) ^ 2 = t ^ (-(1/2:ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ht.1.le]; norm_num
    rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
    calc |ExpIntegralTransforms.realE1 t| ^ 2 ≤ (2 + 4 * t ^ (-(1/4:ℝ))) ^ 2 :=
           pow_le_pow_left₀ (abs_nonneg _) h 2
      _ = 4 + 16 * t ^ (-(1/4:ℝ)) + 16 * (t ^ (-(1/4:ℝ))) ^ 2 := by ring
      _ ≤ 4 + 32 * t ^ (-(1/2:ℝ)) := by rw [hq]; nlinarith
  · have h := ExpIntegralTransforms.realE1_le_recip ht.le
    rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
    calc |ExpIntegralTransforms.realE1 t| ^ 2 ≤ (1 / t) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
      _ = 1 / t ^ 2 := by ring

/-- `e^{-t} E₁(t)` is integrable on `(0, ∞)`. -/
theorem ExpIntegralTransforms.integrableOn_exp_mul_realE1 :
    IntegrableOn (fun t => Real.exp (-t) * ExpIntegralTransforms.realE1 t) (Ioi 0) := by
  refine ExpIntegralTransforms.integrableOn_Ioi_of_bound (A := 2) (B := 4) (C := 1)
    ((Real.continuous_exp.comp continuous_neg).measurable.mul
        ExpIntegralTransforms.measurable_realE1).aestronglyMeasurable
    (fun t ht => ?_) (fun t ht => ?_)
  · have h := ExpIntegralTransforms.abs_realE1_le_small ht.1 ht.2
    have h1 := ExpIntegralTransforms.rpow_quarter_le ht.1 ht.2
    have he : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.2 (by linarith [ht.1])
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (-t) * |ExpIntegralTransforms.realE1 t| ≤ 1 * |ExpIntegralTransforms.realE1 t| :=
          mul_le_mul_of_nonneg_right he (abs_nonneg _)
      _ ≤ 2 + 4 * t ^ (-(1/2:ℝ)) := by linarith
  · have ht0 : (0:ℝ) < t := by linarith
    have h := ExpIntegralTransforms.realE1_le_recip ht.le
    have he : Real.exp (-t) ≤ 1 / t := by
      rw [Real.exp_neg, ← one_div]
      exact one_div_le_one_div_of_le ht0 (by linarith [Real.add_one_le_exp t])
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (-t) * |ExpIntegralTransforms.realE1 t| ≤ (1 / t) * (1 / t) :=
          mul_le_mul he h (abs_nonneg _) (by positivity)
      _ = 1 / t ^ 2 := by ring

/-- `t (c(t) + log t)² → 0` as `t → 0⁺` for continuous `c`. -/
theorem ExpIntegralTransforms.tendsto_mul_sq_add_log {c : ℝ → ℝ} (hc : Continuous c) (σ : ℝ) :
    Tendsto (fun t => t * (c t + σ * Real.log t) ^ 2) (𝓝[>] 0) (𝓝 0) := by
  have e : ∀ t, 0 < t → t * (c t + σ * Real.log t) ^ 2 =
      t * c t ^ 2 + 2 * σ * c t * (t * Real.log t) + σ ^ 2 * (Real.log t * t ^ (1/2:ℝ)) ^ 2 := by
    intro t ht
    have : (t ^ (1/2:ℝ)) ^ 2 = t := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]; norm_num
    rw [mul_pow (Real.log t), this]; ring
  have h1 : Tendsto (fun t => t * c t ^ 2) (𝓝[>] 0) (𝓝 (0 * c 0 ^ 2)) :=
    ((continuous_id.mul (hc.pow 2)).tendsto 0).mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun t => 2 * σ * c t * (t * Real.log t)) (𝓝[>] 0)
      (𝓝 (2 * σ * c 0 * (0 * Real.log 0))) :=
    (((continuous_const.mul hc).mul Real.continuous_mul_log).tendsto 0).mono_left nhdsWithin_le_nhds
  have h3 := ((tendsto_log_mul_rpow_nhdsGT_zero (by norm_num : (0:ℝ) < 1/2)).pow
      2).const_mul (σ ^ 2)
  have := (h1.add h2).add h3
  simp only [zero_mul, mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (e t ht).symm

/-- `∫₀^∞ E₁(t)² dt = 2 log 2`. -/
theorem ExpIntegralTransforms.integral_realE1_sq : ∫ t in Ioi (0:ℝ),
    ExpIntegralTransforms.realE1 t ^ 2 = 2 * Real.log 2 := by
  have hF0 : ContinuousWithinAt (fun t => t * ExpIntegralTransforms.realE1 t ^ 2) (Ici 0) 0 := by
    rw [← continuousWithinAt_Ioi_iff_Ici, ContinuousWithinAt]
    have := ExpIntegralTransforms.tendsto_mul_sq_add_log
        (c := fun t => Real.expIntEin t - Real.eulerMascheroniConstant)
      (ExpIntegralTransforms.continuous_expIntEin.sub continuous_const) (-1)
    simp only [zero_mul]
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t _
    simp only [ExpIntegralTransforms.realE1]; ring
  have hd : ∀ x ∈ Ioi (0:ℝ), HasDerivAt (fun t => t * ExpIntegralTransforms.realE1 t ^ 2)
      (ExpIntegralTransforms.realE1 x ^ 2 - 2 *
          (Real.exp (-x) * ExpIntegralTransforms.realE1 x)) x := by
    intro x hx
    have hx0 : (0:ℝ) < x := hx
    refine ((hasDerivAt_id x).mul
        ((ExpIntegralTransforms.hasDerivAt_realE1 hx0).pow 2)).congr_deriv ?_
    simp only [id, one_mul, Nat.cast_ofNat, Pi.pow_apply]
    field_simp
    ring
  have hl : Tendsto (fun t => t * ExpIntegralTransforms.realE1 t ^ 2) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ ((tendsto_const_nhds (x := (1:ℝ))).div_atTop tendsto_id)
    filter_upwards [eventually_ge_atTop 1] with t ht
    have ht0 : (0:ℝ) < t := by linarith
    have h := ExpIntegralTransforms.realE1_le_recip ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos ht0, abs_of_nonneg (sq_nonneg _), ← sq_abs]
    calc t * |ExpIntegralTransforms.realE1 t| ^ 2 ≤ t * (1 / t) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) h 2) ht0.le
      _ = 1 / id t := by simp only [id]; field_simp
  have hint := ExpIntegralTransforms.integrableOn_realE1_sq.sub
      (ExpIntegralTransforms.integrableOn_exp_mul_realE1.const_mul 2)
  have h := integral_Ioi_of_hasDerivAt_of_tendsto hF0 hd hint hl
  rw [integral_sub ExpIntegralTransforms.integrableOn_realE1_sq
      (ExpIntegralTransforms.integrableOn_exp_mul_realE1.const_mul 2),
    integral_const_mul] at h
  simp only [zero_mul, sub_zero] at h
  have hL : ∫ t in Ioi (0:ℝ), Real.exp (-t) * ExpIntegralTransforms.realE1 t = Real.log 2 := by
    have h2 := (ExpIntegralTransforms.laplace_E1 (a := 1) (by simp)).2
    simp only [one_ne_zero, ite_false, div_one] at h2
    rw [setIntegral_congr_fun measurableSet_Ioi
      (g := fun t : ℝ => ((Real.exp (-t) * ExpIntegralTransforms.realE1 t : ℝ) : ℂ)) (fun t ht => by
        rw [ExpIntegralTransforms.E1_ofReal (show (0:ℝ) < t from ht)]; push_cast; ring_nf),
      integral_complex_ofReal, show (1:ℂ) + 1 = ((2:ℝ):ℂ) by norm_num,
      ← ofReal_log (by norm_num), ofReal_inj] at h2
    exact h2
  linarith

/-- `e^y - 1 ≥ y e^{y/2}` for `y ≥ 0`. -/
theorem ExpIntegralTransforms.exp_sub_one_ge {y : ℝ} (hy : 0 ≤ y) : y * Real.exp (y / 2) ≤
    Real.exp y - 1 := by
  have h := Real.self_le_sinh_iff.2 (by linarith : 0 ≤ y / 2)
  rw [Real.sinh_eq] at h
  have e1 : Real.exp y = Real.exp (y / 2) * Real.exp (y / 2) := by
    rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp (-(y / 2)) * Real.exp (y / 2) = 1 := by
    rw [← Real.exp_add]; simp
  have hp := Real.exp_pos (y / 2)
  nlinarith

/-- `e^y - 1 > 0` for `y > 0`. -/
theorem ExpIntegralTransforms.exp_sub_one_pos {y : ℝ} (hy : 0 < y) : 0 < Real.exp y - 1 :=
  sub_pos.2 (Real.one_lt_exp_iff.2 hy)

/-- Integrability of the Binet kernel `t/((t²+x²)(e^{ct} - 1))` on `(0, ∞)`. -/
theorem ExpIntegralTransforms.integrableOn_binetKernel {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    IntegrableOn (fun t => t / ((t ^ 2 + x ^ 2) * (Real.exp (c * t) - 1))) (Ioi 0) := by
  have hi : IntegrableOn (fun t : ℝ => (1 / (c * x ^ 2)) * Real.exp (-(c / 2) * t)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 (by positivity : 0 < c / 2)).const_mul _
  refine hi.mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    intro t ht
    have ht0 : (0:ℝ) < t := ht
    have : Real.exp (c * t) - 1 ≠ 0 := (ExpIntegralTransforms.exp_sub_one_pos (by positivity)).ne'
    exact (ContinuousAt.div continuousAt_id (by fun_prop) (by positivity)).continuousWithinAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0:ℝ) < t := ht
    have h1 := ExpIntegralTransforms.exp_sub_one_ge (by positivity : 0 ≤ c * t)
    have hp := Real.exp_pos (c * t / 2)
    have hpos : 0 < Real.exp (c * t) - 1 := ExpIntegralTransforms.exp_sub_one_pos (by positivity)
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    have he : Real.exp (-(c / 2) * t) = (Real.exp (c * t / 2))⁻¹ := by
      rw [← Real.exp_neg]; ring_nf
    rw [he, div_le_iff₀ (by positivity)]
    calc t = (1 / (c * x ^ 2)) * (Real.exp (c * t / 2))⁻¹ *
           (x ^ 2 * (c * t * Real.exp (c * t / 2))) := by
          field_simp
      _ ≤ (1 / (c * x ^ 2)) * (Real.exp (c * t / 2))⁻¹ *
          ((t ^ 2 + x ^ 2) * (Real.exp (c * t) - 1)) := by
          gcongr
          · nlinarith

/-- Binet-kernel integral via the digamma function (DLMF 5.9.15, `DLMF.Gamma.digamma_coth`). -/
theorem ExpIntegralTransforms.binetKernel_eq {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    ∫ t in Ioi (0:ℝ), t / ((t ^ 2 + x ^ 2) * (Real.exp (c * t) - 1)) =
      (Real.log (x * c / (2 * π)) - 1 / (2 * (x * c / (2 * π))) -
        Gamma.Real.digamma (x * c / (2 * π))) / 2 := by
  set y := x * c / (2 * π) with hy
  have hy0 : 0 < y := by positivity
  have hd := DLMF.Gamma.digamma_coth hy0
  set lam := 2 * π / c with hlam
  have hlam0 : 0 < lam := by positivity
  have hsub := integral_comp_mul_left_Ioi
    (fun t : ℝ => t / ((t ^ 2 + x ^ 2) * (Real.exp (c * t) - 1))) 0 hlam0
  simp only [mul_zero, smul_eq_mul] at hsub
  have hJ : ∫ t in Ioi (0:ℝ), t / ((t ^ 2 + x ^ 2) * (Real.exp (c * t) - 1)) =
      ∫ s in Ioi (0:ℝ), s / ((s ^ 2 + y ^ 2) * (Real.exp (2 * π * s) - 1)) := by
    rw [← mul_inv_cancel_left₀ hlam0.ne' (∫ t in Ioi (0:ℝ), _), ← hsub, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    have hs0 : (0:ℝ) < s := hs
    have hcl : c * (lam * s) = 2 * π * s := by rw [hlam]; field_simp
    have hne : Real.exp (2 * π * s) - 1 ≠ 0 :=
        (ExpIntegralTransforms.exp_sub_one_pos (by positivity)).ne'
    rw [hcl, hy, hlam]
    field_simp
  rw [hJ]
  linarith

/-- `ψ(2) = 1 - γ`. -/
theorem ExpIntegralTransforms.digamma_two : Gamma.Real.digamma 2 = 1 -
    Real.eulerMascheroniConstant := by
  have := Gamma.Real.digamma_add_one (x := 1) one_pos
  norm_num at this
  rw [this, Gamma.Real.digamma_one]; ring

/-- The real auxiliary function `g(x) = ∫₀^∞ u e^{-xu}/(u²+1) du`. -/
noncomputable def ExpIntegralTransforms.realAuxG (x : ℝ) : ℝ := ∫ u in Ioi (0:ℝ), u *
    Real.exp (-x * u) / (u ^ 2 + 1)

/-- The auxiliary function `g(x)` is real for `x > 0` and equals `ExpIntegralTransforms.realAuxG x`.
-/
theorem ExpIntegralTransforms.auxG_ofReal {x : ℝ} (hx : 0 < x) : expIntAuxG x =
    (ExpIntegralTransforms.realAuxG x : ℂ) := by
  rw [(ExpIntegralAuxiliary.ofReal_laplace_Ioi hx).2, ExpIntegralTransforms.realAuxG,
      ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  push_cast; ring_nf

/-- `Ci(x) = -g(x) cos x` when `sin x = 0`, `x > 0`. -/
theorem ExpIntegralTransforms.cosInt_of_sin_eq_zero {x : ℝ} (hx : 0 < x) (hs : Real.sin x = 0) :
    Real.cosInt x = -ExpIntegralTransforms.realAuxG x * Real.cos x := by
  have h := cosInt_eq_aux (x:ℂ)
  rw [cosInt_ofReal hx, ExpIntegralTransforms.auxG_ofReal hx, ← ofReal_sin, hs, ← ofReal_cos] at h
  have : ((Real.cosInt x : ℝ) : ℂ) =
      ((-ExpIntegralTransforms.realAuxG x * Real.cos x : ℝ) : ℂ) := by
    rw [h]; push_cast; ring
  exact_mod_cast this

/-- `0 ≤ g(x) ≤ 1/x²` for `x > 0`. -/
theorem ExpIntegralTransforms.realAuxG_nonneg_le {x : ℝ} (hx : 0 < x) : 0 ≤
    ExpIntegralTransforms.realAuxG x ∧ ExpIntegralTransforms.realAuxG x ≤ 1 / x ^ 2 := by
  have hb := DLMF.Gamma.integrableOn_mul_exp_neg_mul hx
  constructor
  · refine setIntegral_nonneg measurableSet_Ioi fun u hu => ?_
    have : (0:ℝ) < u := hu
    positivity
  · rw [← DLMF.Gamma.integral_mul_exp_neg_mul hx, ExpIntegralTransforms.realAuxG]
    refine setIntegral_mono_on ?_ hb measurableSet_Ioi fun u hu => ?_
    · refine hb.mono' ((Continuous.div (by fun_prop) (by fun_prop)
        (fun u => by positivity)).aestronglyMeasurable) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hu0 : (0:ℝ) < u := hu
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact div_le_self (by positivity) (by nlinarith)
    · have hu0 : (0:ℝ) < u := hu
      exact div_le_self (by positivity) (by nlinarith)

/-- Alternating sum `Σ (-1)ⁿ g(c(n+1))` as a Fermi-type integral, via the Laplace representation
  of `g`. -/
theorem ExpIntegralTransforms.hasSum_realAuxG {c : ℝ} (hc : 0 < c) :
    HasSum (fun n : ℕ => (-1) ^ n * ExpIntegralTransforms.realAuxG (c * (n + 1)))
      (∫ u in Ioi (0:ℝ), u / ((u ^ 2 + 1) * (Real.exp (c * u) + 1))) := by
  set F : ℕ → ℝ → ℝ := fun n u => (-1) ^ n * (u * Real.exp (-(c * (n + 1)) * u) / (u ^ 2 + 1))
  have hx : ∀ n : ℕ, 0 < c * (n + 1) := fun n => by positivity
  have hgi : ∀ n : ℕ, IntegrableOn (fun u : ℝ => u * Real.exp (-(c * (n + 1)) * u) / (u ^ 2 + 1))
      (Ioi 0) := fun n => by
    have hb := DLMF.Gamma.integrableOn_mul_exp_neg_mul (hx n)
    refine hb.mono' ((Continuous.div (by fun_prop) (by fun_prop)
        (fun u => by positivity)).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : (0:ℝ) < u := hu
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact div_le_self (by positivity) (by nlinarith)
  have hFi : ∀ n, Integrable (F n) (volume.restrict (Ioi 0)) := fun n => (hgi n).const_mul _
  have hFn : ∀ n, ∫ u in Ioi (0:ℝ), ‖F n u‖ =
      ExpIntegralTransforms.realAuxG (c * (n + 1)) := fun n => by
    rw [ExpIntegralTransforms.realAuxG]
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have hu0 : (0:ℝ) < u := hu
    simp only [F, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity)]
  have hFv : ∀ n, ∫ u in Ioi (0:ℝ), F n u = (-1) ^ n *
      ExpIntegralTransforms.realAuxG (c * (n + 1)) := fun n => by
    simp only [F]; rw [integral_const_mul, ExpIntegralTransforms.realAuxG]
  have hsumN : Summable fun n => ∫ u in Ioi (0:ℝ), ‖F n u‖ := by
    simp_rw [hFn]
    have hs : Summable fun n : ℕ => 1 / (c * ((n:ℝ) + 1)) ^ 2 := by
      have h1 := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 one_lt_two)
      refine (h1.mul_left (1 / c ^ 2)).congr fun n => ?_
      push_cast; field_simp
    exact hs.of_nonneg_of_le (fun n => (ExpIntegralTransforms.realAuxG_nonneg_le (hx n)).1)
      (fun n => (ExpIntegralTransforms.realAuxG_nonneg_le (hx n)).2)
  have key := integral_tsum_of_summable_integral_norm hFi hsumN
  have hsum : Summable fun n => ∫ u in Ioi (0:ℝ), F n u := by
    refine Summable.of_norm_bounded hsumN fun n => ?_
    exact norm_integral_le_integral_norm _
  simp_rw [← hFv]
  convert hsum.hasSum using 1
  rw [key]
  refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
  have hu0 : (0:ℝ) < u := hu
  set q := Real.exp (-(c * u)) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := Real.exp_lt_one_iff.2 (by nlinarith)
  have hg := (hasSum_geometric_of_abs_lt_one (r := -q)
      (by rw [abs_neg, abs_of_pos hq0]; exact hq1)).mul_left
    (u * q / (u ^ 2 + 1))
  have hterm : ∀ n : ℕ, F n u = u * q / (u ^ 2 + 1) * (-q) ^ n := fun n => by
    simp only [F]
    rw [show -(c * ((n:ℝ) + 1)) * u = ((n + 1 : ℕ) : ℝ) * (-(c * u)) by push_cast; ring,
      Real.exp_nat_mul, ← hq, neg_pow]
    ring
  simp_rw [hterm]
  rw [hg.tsum_eq]
  have he : Real.exp (c * u) = q⁻¹ := by rw [hq, Real.exp_neg, inv_inv]
  rw [he, show (1 - -q) = 1 + q by ring]
  field_simp

/-- Rewrite of the Fermi-type kernel in terms of two Bose-type (Binet) kernels. -/
theorem ExpIntegralTransforms.integral_fermi {c : ℝ} (hc : 0 < c) :
    ∫ u in Ioi (0:ℝ), u / ((u ^ 2 + 1) * (Real.exp (c * u) + 1)) =
      (∫ u in Ioi (0:ℝ), u / ((u ^ 2 + 1 ^ 2) * (Real.exp (c * u) - 1))) -
        2 * ∫ u in Ioi (0:ℝ), u / ((u ^ 2 + 1 ^ 2) * (Real.exp ((2 * c) * u) - 1)) := by
  rw [← integral_const_mul,
      ← integral_sub (ExpIntegralTransforms.integrableOn_binetKernel hc one_pos)
    ((ExpIntegralTransforms.integrableOn_binetKernel (by positivity : 0 < 2 * c)
        one_pos).const_mul 2)]
  refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
  have hu0 : (0:ℝ) < u := hu
  have h1 := ExpIntegralTransforms.exp_sub_one_pos (by positivity : 0 < c * u)
  have h2 : Real.exp ((2 * c) * u) = Real.exp (c * u) ^ 2 := by
    rw [← Real.exp_nat_mul]; ring_nf
  rw [h2]
  have h3 : Real.exp (c * u) ^ 2 - 1 = (Real.exp (c * u) - 1) * (Real.exp (c * u) + 1) := by ring
  rw [h3]
  have h4 : Real.exp (c * u) + 1 ≠ 0 := by positivity
  have h5 : Real.exp (c * u) - 1 ≠ 0 := h1.ne'
  have h6 : u ^ 2 + 1 ^ 2 ≠ 0 := by positivity
  generalize Real.exp (c * u) = E at h4 h5 ⊢
  field_simp
  ring

/-- The real auxiliary function `f(x) = ∫₀^∞ e^{-xu}/(u²+1) du`. -/
noncomputable def ExpIntegralTransforms.realAuxF (x : ℝ) : ℝ := ∫ u in Ioi (0:ℝ),
    Real.exp (-x * u) / (u ^ 2 + 1)

/-- The auxiliary function `f(x)` is real for `x > 0` and equals `ExpIntegralTransforms.realAuxF x`.
-/
theorem ExpIntegralTransforms.auxF_ofReal {x : ℝ} (hx : 0 < x) : expIntAuxF x =
    (ExpIntegralTransforms.realAuxF x : ℂ) := by
  rw [(ExpIntegralAuxiliary.ofReal_laplace_Ioi hx).1, ExpIntegralTransforms.realAuxF,
      ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  push_cast; ring_nf

/-- `Si(x) - π/2 = -f(x) cos x` when `sin x = 0`, `x > 0`. -/
theorem ExpIntegralTransforms.sinIntTail_of_sin_eq_zero {x : ℝ} (hx : 0 < x) (hs : Real.sin x = 0) :
    Real.sinInt x - π / 2 = -ExpIntegralTransforms.realAuxF x * Real.cos x := by
  have h := sinInt_eq_aux (x:ℂ)
  rw [sinInt_ofReal, ExpIntegralTransforms.auxF_ofReal hx, ← ofReal_sin, hs, ofReal_zero,
      mul_zero, sub_zero] at h
  have : ((Real.sinInt x - π / 2 : ℝ) : ℂ) =
      ((-ExpIntegralTransforms.realAuxF x * Real.cos x : ℝ) : ℂ) := by
    push_cast; rw [h]; ring
  exact_mod_cast this

/-- Integrability of `e^{-xu}/(u²+1)` on `(0, ∞)` for `x > 0`. -/
theorem ExpIntegralTransforms.integrableOn_realAuxF_kernel {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun u : ℝ => Real.exp (-x * u) / (u ^ 2 + 1)) (Ioi 0) := by
  refine (exp_neg_integrableOn_Ioi 0 hx).mono' ((Continuous.div (by fun_prop) (by fun_prop)
    (fun u => by positivity)).aestronglyMeasurable) (Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact div_le_self (by positivity) (by nlinarith [sq_nonneg u])

/-- `0 ≤ f(x) ≤ 1/x` for `x > 0`. -/
theorem ExpIntegralTransforms.realAuxF_nonneg_le {x : ℝ} (hx : 0 < x) : 0 ≤
    ExpIntegralTransforms.realAuxF x ∧ ExpIntegralTransforms.realAuxF x ≤ 1 / x := by
  have hb := exp_neg_integrableOn_Ioi 0 hx
  constructor
  · exact setIntegral_nonneg measurableSet_Ioi fun u _ => by positivity
  · have hv : ∫ u in Ioi (0:ℝ), Real.exp (-x * u) = 1 / x := by
      have := integral_exp_mul_Ioi (a := -x) (by linarith) 0
      simp only [mul_zero, Real.exp_zero] at this
      rw [this]; field_simp
    rw [← hv, ExpIntegralTransforms.realAuxF]
    exact setIntegral_mono_on (ExpIntegralTransforms.integrableOn_realAuxF_kernel hx) hb
        measurableSet_Ioi fun u _ =>
      div_le_self (by positivity) (by nlinarith [sq_nonneg u])

/-- Alternating sum `Σ (-1)ⁿ f(c(n+1))/(n+1)` as an integral of `log(1 + e^{-cu})/(u²+1)`. -/
theorem ExpIntegralTransforms.hasSum_realAuxF {c : ℝ} (hc : 0 < c) :
    HasSum (fun n : ℕ => (-1) ^ n * ExpIntegralTransforms.realAuxF (c * (n + 1)) / (n + 1))
      (∫ u in Ioi (0:ℝ), Real.log (1 + Real.exp (-(c * u))) / (u ^ 2 + 1)) := by
  set F : ℕ → ℝ → ℝ := fun n u =>
    (-1) ^ n / (n + 1) * (Real.exp (-(c * (n + 1)) * u) / (u ^ 2 + 1))
  have hx : ∀ n : ℕ, 0 < c * (n + 1) := fun n => by positivity
  have hFi : ∀ n, Integrable (F n) (volume.restrict (Ioi 0)) := fun n =>
    (ExpIntegralTransforms.integrableOn_realAuxF_kernel (hx n)).const_mul _
  have hFn : ∀ n : ℕ, ∫ u in Ioi (0:ℝ), ‖F n u‖ = ExpIntegralTransforms.realAuxF (c * (n + 1)) /
      (n + 1) := fun n => by
    rw [ExpIntegralTransforms.realAuxF, div_eq_inv_mul, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    simp only [F, Real.norm_eq_abs, abs_mul, abs_div, abs_pow, abs_neg, abs_one, one_pow]
    rw [abs_of_pos (by positivity : (0:ℝ) < (n:ℝ) + 1), abs_of_pos (Real.exp_pos _),
      abs_of_pos (by positivity : (0:ℝ) < u ^ 2 + 1)]
    ring
  have hFv : ∀ n : ℕ, ∫ u in Ioi (0:ℝ), F n u = (-1) ^ n *
      ExpIntegralTransforms.realAuxF (c * (n + 1)) / (n + 1) :=
    fun n => by simp only [F]; rw [integral_const_mul, ExpIntegralTransforms.realAuxF]; ring
  have hsumN : Summable fun n => ∫ u in Ioi (0:ℝ), ‖F n u‖ := by
    simp_rw [hFn]
    have hs : Summable fun n : ℕ => 1 / c * (1 / ((n:ℝ) + 1) ^ 2) := by
      have h1 := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 one_lt_two)
      refine (h1.mul_left (1 / c)).congr fun n => ?_
      push_cast; ring
    refine hs.of_nonneg_of_le
        (fun n => div_nonneg (ExpIntegralTransforms.realAuxF_nonneg_le (hx n)).1 (by positivity))
      (fun n => ?_)
    have := (ExpIntegralTransforms.realAuxF_nonneg_le (hx n)).2
    calc ExpIntegralTransforms.realAuxF (c * (n + 1)) / (n + 1) ≤ 1 / (c * (n + 1)) / (n + 1) :=
          div_le_div_of_nonneg_right this (by positivity)
      _ = 1 / c * (1 / ((n:ℝ) + 1) ^ 2) := by field_simp
  have key := integral_tsum_of_summable_integral_norm hFi hsumN
  have hsum : Summable fun n => ∫ u in Ioi (0:ℝ), F n u :=
    Summable.of_norm_bounded hsumN fun n => norm_integral_le_integral_norm _
  simp_rw [← hFv]
  convert hsum.hasSum using 1
  rw [key]
  refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
  have hu0 : (0:ℝ) < u := hu
  set q := Real.exp (-(c * u)) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := Real.exp_lt_one_iff.2 (by nlinarith)
  have hg := ((Real.hasSum_pow_div_log_of_abs_lt_one (x := -q)
    (by rw [abs_neg, abs_of_pos hq0]; exact hq1)).neg).mul_left (1 / (u ^ 2 + 1))
  have hterm : ∀ n : ℕ, F n u = 1 / (u ^ 2 + 1) * -((-q) ^ (n + 1) / (n + 1)) := fun n => by
    simp only [F]
    rw [show -(c * ((n:ℝ) + 1)) * u = ((n + 1 : ℕ) : ℝ) * (-(c * u)) by push_cast; ring,
      Real.exp_nat_mul, ← hq, neg_pow (q) (n + 1), pow_succ (-1 : ℝ) n]
    ring
  simp_rw [hterm]
  rw [hg.tsum_eq, neg_neg, sub_neg_eq_add]
  ring

/-- `0 ≤ log(1 + e^{-y}) ≤ e^{-y}`. -/
theorem ExpIntegralTransforms.log_one_add_exp_le (y : ℝ) :
    0 ≤ Real.log (1 + Real.exp (-y)) ∧ Real.log (1 + Real.exp (-y)) ≤ Real.exp (-y) := by
  have hp := Real.exp_pos (-y)
  exact ⟨Real.log_nonneg (by linarith), by
    have := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + Real.exp (-y)); linarith⟩

/-- Integration by parts: `∫₀^∞ log(1+e^{-cu})/(u²+1) du = c ∫₀^∞ arctan u/(e^{cu}+1) du`. -/
theorem ExpIntegralTransforms.integral_log_eq {c : ℝ} (hc : 0 < c) :
    ∫ u in Ioi (0:ℝ), Real.log (1 + Real.exp (-(c * u))) / (u ^ 2 + 1) =
      c * ∫ u in Ioi (0:ℝ), Real.arctan u / (Real.exp (c * u) + 1) := by
  have he := exp_neg_integrableOn_Ioi 0 hc
  have hi1 : IntegrableOn (fun u => Real.log (1 + Real.exp (-(c * u))) / (u ^ 2 + 1)) (Ioi 0) := by
    refine he.mono' ((Continuous.div (by
        exact Continuous.log (by fun_prop) (fun u => by positivity))
        (by fun_prop) (fun u => by positivity)).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : (0:ℝ) < u := hu
    obtain ⟨h1, h2⟩ := ExpIntegralTransforms.log_one_add_exp_le (c * u)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), neg_mul]
    calc _ ≤ Real.log (1 + Real.exp (-(c * u))) := div_le_self h1 (by nlinarith)
      _ ≤ _ := h2
  have hi2 : IntegrableOn (fun u => Real.arctan u / (Real.exp (c * u) + 1)) (Ioi 0) := by
    refine (he.const_mul (π / 2)).mono' ((Continuous.div (by fun_prop) (by fun_prop)
        (fun u => by positivity)).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : (0:ℝ) < u := hu
    have ha0 : 0 ≤ Real.arctan u := Real.arctan_nonneg.2 hu0.le
    have ha1 := Real.arctan_lt_pi_div_two u
    have hp : Real.exp (-c * u) * Real.exp (c * u) = 1 := by rw [← Real.exp_add]; simp
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
    nlinarith [Real.exp_pos (-c * u), Real.exp_pos (c * u)]
  have hd : ∀ x ∈ Ioi (0:ℝ),
      HasDerivAt (fun u => Real.arctan u * Real.log (1 + Real.exp (-(c * u))))
      (Real.log (1 + Real.exp (-(c * x))) / (x ^ 2 + 1) - c *
          (Real.arctan x / (Real.exp (c * x) + 1))) x := by
    intro x _
    have h1 := Real.hasDerivAt_arctan x
    have hin : HasDerivAt (fun u => -(c * u)) (-c) x := by
      have := ((hasDerivAt_id x).const_mul c).fun_neg
      simpa using this
    have h2 := ((hin.exp).const_add 1).log (by positivity)
    refine (h1.mul h2).congr_deriv ?_
    rw [Real.exp_neg]
    have hq : 0 < Real.exp (c * x) := Real.exp_pos _
    generalize Real.exp (c * x) = E at hq ⊢
    have : E + 1 ≠ 0 := by positivity
    have : x ^ 2 + 1 ≠ 0 := by positivity
    have : 1 + x ^ 2 ≠ 0 := by positivity
    have : 1 + E⁻¹ ≠ 0 := by positivity
    field_simp
    ring
  have hl : Tendsto (fun u => Real.arctan u * Real.log (1 + Real.exp (-(c * u)))) atTop (𝓝 0) := by
    have hb : Tendsto (fun u : ℝ => π / 2 * Real.exp (-(c * u))) atTop (𝓝 0) := by
      have := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hc)
      simpa [Function.comp_def] using this.const_mul (π / 2)
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [eventually_gt_atTop 0] with u hu
    obtain ⟨h1, h2⟩ := ExpIntegralTransforms.log_one_add_exp_le (c * u)
    have ha0 : 0 ≤ Real.arctan u := Real.arctan_nonneg.2 hu.le
    have ha1 := Real.arctan_lt_pi_div_two u
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul ha1.le h2 h1 (by positivity)
  have h := integral_Ioi_of_hasDerivAt_of_tendsto
    ((Real.continuous_arctan.mul (Continuous.log (by fun_prop)
      (fun u => by positivity))).continuousAt.continuousWithinAt) hd
    (hi1.sub (hi2.const_mul c)) hl
  rw [integral_sub hi1 (hi2.const_mul c), integral_const_mul] at h
  simp at h
  linarith

/-- Integrability of `arctan u/(e^{cu} - 1)` on `(0, ∞)`. -/
theorem ExpIntegralTransforms.integrableOn_arctanKernel {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun u => Real.arctan u / (Real.exp (c * u) - 1)) (Ioi 0) := by
  have hi : IntegrableOn (fun t : ℝ => (1 / c) * Real.exp (-(c / 2) * t)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 (by positivity : 0 < c / 2)).const_mul _
  refine hi.mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    intro t ht
    have ht0 : (0:ℝ) < t := ht
    have : Real.exp (c * t) - 1 ≠ 0 := (ExpIntegralTransforms.exp_sub_one_pos (by positivity)).ne'
    exact (Real.continuous_arctan.continuousAt.div
      (by fun_prop : ContinuousAt (fun u => Real.exp (c * u) - 1) t) this).continuousWithinAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0:ℝ) < t := ht
    have h1 := ExpIntegralTransforms.exp_sub_one_ge (by positivity : 0 ≤ c * t)
    have hp := Real.exp_pos (c * t / 2)
    have hpos : 0 < Real.exp (c * t) - 1 := ExpIntegralTransforms.exp_sub_one_pos (by positivity)
    have ha0 : 0 ≤ Real.arctan t := Real.arctan_nonneg.2 ht0.le
    have ha1 := Real.arctan_le_self ht0.le
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have he : Real.exp (-(c / 2) * t) = (Real.exp (c * t / 2))⁻¹ := by
      rw [← Real.exp_neg]; ring_nf
    rw [he, div_le_iff₀ hpos]
    calc Real.arctan t ≤ t := ha1
      _ = (1 / c) * (Real.exp (c * t / 2))⁻¹ * (c * t * Real.exp (c * t / 2)) := by field_simp
      _ ≤ (1 / c) * (Real.exp (c * t / 2))⁻¹ * (Real.exp (c * t) - 1) := by gcongr

/-- Binet's second formula (DLMF 5.9.10, `DLMF.Gamma.log_Gamma_binet_arctan`) in rescaled form. -/
theorem ExpIntegralTransforms.arctanKernel_eq {c : ℝ} (hc : 0 < c) :
    ∫ u in Ioi (0:ℝ), Real.arctan u / (Real.exp (c * u) - 1) =
      2 * π / c * ((Real.log (Real.Gamma (c / (2 * π))) - (c / (2 * π) - 1 / 2) *
        Real.log (c / (2 * π)) + c / (2 * π) - 1 / 2 * Real.log (2 * π)) / 2) := by
  set y := c / (2 * π) with hy
  have hy0 : 0 < y := by positivity
  have hb := DLMF.Gamma.log_Gamma_binet_arctan hy0
  set lam := 2 * π / c with hlam
  have hlam0 : 0 < lam := by positivity
  have hsub := integral_comp_mul_left_Ioi
    (fun u : ℝ => Real.arctan u / (Real.exp (c * u) - 1)) 0 hlam0
  simp only [mul_zero, smul_eq_mul] at hsub
  have hJ : ∫ u in Ioi (0:ℝ), Real.arctan u / (Real.exp (c * u) - 1) =
      lam * ∫ s in Ioi (0:ℝ), Real.arctan (s / y) / (Real.exp (2 * π * s) - 1) := by
    rw [← mul_inv_cancel_left₀ hlam0.ne' (∫ t in Ioi (0:ℝ), _), ← hsub]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    have hcl : c * (lam * s) = 2 * π * s := by rw [hlam]; field_simp
    have hsl : lam * s = s / y := by rw [hlam, hy]; field_simp
    rw [hcl, hsl]
  rw [hJ]
  congr 1
  linarith

/-- `∫₀^∞ log(1+e^{-cu})/(u²+1) du` through Binet's second formula. -/
theorem ExpIntegralTransforms.integral_log_eq' {c : ℝ} (hc : 0 < c) :
    ∫ u in Ioi (0:ℝ), Real.log (1 + Real.exp (-(c * u))) / (u ^ 2 + 1) =
      c * ((∫ u in Ioi (0:ℝ), Real.arctan u / (Real.exp (c * u) - 1)) -
        2 * ∫ u in Ioi (0:ℝ), Real.arctan u / (Real.exp ((2 * c) * u) - 1)) := by
  rw [ExpIntegralTransforms.integral_log_eq hc]
  congr 1
  rw [← integral_const_mul, ← integral_sub (ExpIntegralTransforms.integrableOn_arctanKernel hc)
    ((ExpIntegralTransforms.integrableOn_arctanKernel (by positivity : 0 < 2 * c)).const_mul 2)]
  refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
  have hu0 : (0:ℝ) < u := hu
  have h1 := ExpIntegralTransforms.exp_sub_one_pos (by positivity : 0 < c * u)
  have h2 : Real.exp ((2 * c) * u) = Real.exp (c * u) ^ 2 := by
    rw [← Real.exp_nat_mul]; ring_nf
  rw [h2]
  have h4 : Real.exp (c * u) + 1 ≠ 0 := by positivity
  have h5 : Real.exp (c * u) - 1 ≠ 0 := h1.ne'
  generalize Real.exp (c * u) = E at h4 h5 ⊢
  have h6 : E ^ 2 - 1 ≠ 0 := by
    rw [show E ^ 2 - 1 = (E - 1) * (E + 1) by ring]; exact mul_ne_zero h5 h4
  field_simp
  ring

end DLMF.Confluent

end
