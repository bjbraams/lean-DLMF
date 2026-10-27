/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Gamma.IntegralRepresentations
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-!
# Binet's formula for complex arguments (DLMF 5.11.1, 5.6.9)

Binet's function is taken in Stieltjes' form
`μ(z) = ∫₀^∞ P(t)/(z+t)² dt`, with the periodic weight `P(t) = ({t} - {t}²)/2 ∈ [0, 1/8]`.
This integral is holomorphic on the whole slit plane. On the positive reals it agrees with
the Laplace form `binetIntegral`: both differ from their unit shift by
`(x + 1/2) log(1 + 1/x) - 1` and tend to `0`. The identity theorem then gives

`Γ(z) = exp((z - 1/2) log z - z + (1/2) log 2π + μ(z))` for `z ∈ slitPlane`.

From `|z + t|² ≥ ((|z| + Re z)/(2|z|)) (|z| + t)²` follows Stieltjes' bound
`|μ(z)| ≤ 1/(6(|z| + Re z))`, in particular `|μ(z)| ≤ 1/(6|z|)` for `Re z ≥ 0`.
-/

@[expose] public section

open Complex Filter MeasureTheory Set
open scoped Real Topology

noncomputable section

namespace DLMF.Gamma

/-! ### The periodic weight -/

/-- Stieltjes' periodic weight `P(t) = ({t} - {t}²)/2`. -/
def binetWeight (t : ℝ) : ℝ := (Int.fract t - Int.fract t ^ 2) / 2

theorem binetWeight_nonneg (t : ℝ) : 0 ≤ binetWeight t := by
  unfold binetWeight
  have h0 := Int.fract_nonneg t
  have h1 := Int.fract_lt_one t
  nlinarith

theorem binetWeight_le (t : ℝ) : binetWeight t ≤ 1 / 8 := by
  unfold binetWeight
  nlinarith [sq_nonneg (Int.fract t - 1 / 2)]

theorem binetWeight_add_one (t : ℝ) : binetWeight (t + 1) = binetWeight t := by
  simp [binetWeight, Int.fract_add_one]

theorem measurable_binetWeight : Measurable binetWeight :=
  ((measurable_fract.sub (measurable_fract.pow_const 2)).div_const 2)

theorem binetWeight_of_mem_Ico {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    binetWeight t = (t - t ^ 2) / 2 := by
  simp [binetWeight, Int.fract_eq_self.2 ht]

/-! ### An integrable majorant -/

theorem integrableOn_recip_one_add_sq :
    IntegrableOn (fun t : ℝ => ((1 + t) ^ 2)⁻¹) (Ioi 0) := by
  have h := (integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by simp)).integrableOn
    (s := Ioi 0)
  refine h.congr_fun (fun t ht => ?_) measurableSet_Ioi
  have ht' : (0 : ℝ) < t := ht
  simp only [Real.norm_eq_abs, abs_of_pos ht']
  rw [Real.rpow_neg (by positivity), Real.rpow_two]

/-- A point of the slit plane stays at distance `≳ 1 + t` from `-t`, `t ≥ 0`. -/
theorem exists_mul_one_add_le_norm_add {z : ℂ} (hz : z ∈ slitPlane) :
    ∃ c > 0, ∀ t : ℝ, 0 ≤ t → c * (1 + t) ≤ ‖z + t‖ := by
  rcases mem_slitPlane_iff.1 hz with hre | him
  · refine ⟨z.re / (z.re + 1), by positivity, fun t ht => ?_⟩
    have h1 : z.re + t ≤ ‖z + t‖ := by
      simpa using re_le_norm (z + t)
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  · have hy : 0 < |z.im| := abs_pos.2 him
    refine ⟨|z.im| / (|z.im| + 1 + |z.re|), by positivity, fun t ht => ?_⟩
    have h1 : z.re + t ≤ ‖z + t‖ := by
      simpa using re_le_norm (z + t)
    have h2 : |z.im| ≤ ‖z + t‖ := by
      simpa using abs_im_le_norm (z + t)
    have h3 : -z.re ≤ |z.re| := neg_le_abs _
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left h2 (abs_nonneg z.re),
      mul_le_mul_of_nonneg_left h1 hy.le, mul_le_mul_of_nonneg_left h3 hy.le]

/-- Uniform version on a ball around a point of the slit plane. -/
theorem exists_ball_mul_one_add_le_norm_add {z₀ : ℂ} (hz : z₀ ∈ slitPlane) :
    ∃ c > 0, ∀ z ∈ Metric.ball z₀ c, ∀ t : ℝ, 0 ≤ t → c * (1 + t) ≤ ‖z + t‖ := by
  obtain ⟨c, hc, h⟩ := exists_mul_one_add_le_norm_add hz
  refine ⟨c / 2, by positivity, fun z hz t ht => ?_⟩
  have hd : ‖z - z₀‖ < c / 2 := by simpa [dist_eq_norm] using hz
  have h1 := h t ht
  have h2 : ‖z₀ + t‖ ≤ ‖z + t‖ + ‖z - z₀‖ := by
    calc ‖z₀ + t‖ = ‖(z + t) - (z - z₀)‖ := by congr 1; ring
      _ ≤ ‖z + t‖ + ‖z - z₀‖ := norm_sub_le _ _
  nlinarith

/-! ### Binet's function in Stieltjes' form -/

/-- Binet's function in Stieltjes' form, `μ(z) = ∫₀^∞ P(t)/(z+t)² dt`. -/
def binetMu (z : ℂ) : ℂ := ∫ t in Ioi (0 : ℝ), (binetWeight t : ℂ) / (z + t) ^ 2

/-- The real form of `binetMu`. -/
def binetMuReal (x : ℝ) : ℝ := ∫ t in Ioi (0 : ℝ), binetWeight t / (x + t) ^ 2

theorem norm_binetWeight_div_le {z : ℂ} {c t : ℝ} (hc : 0 < c) (ht : 0 ≤ t)
    (hzt : c * (1 + t) ≤ ‖z + t‖) (n : ℕ) :
    ‖(binetWeight t : ℂ) / (z + t) ^ (n + 2)‖ ≤ (1 / 8) / c ^ (n + 2) * ((1 + t) ^ 2)⁻¹ := by
  have h1t : 1 ≤ 1 + t := by linarith
  have hpos : 0 < c * (1 + t) := by positivity
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg (binetWeight_nonneg t)]
  have hden : (c * (1 + t)) ^ (n + 2) ≤ ‖z + t‖ ^ (n + 2) :=
    pow_le_pow_left₀ hpos.le hzt _
  have hge : c ^ (n + 2) * (1 + t) ^ 2 ≤ (c * (1 + t)) ^ (n + 2) := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1t (by omega)) (by positivity)
  calc binetWeight t / ‖z + t‖ ^ (n + 2) ≤ (1 / 8) / (c ^ (n + 2) * (1 + t) ^ 2) := by
        apply div_le_div₀ (by norm_num) (binetWeight_le t) (by positivity)
        exact hge.trans hden
    _ = (1 / 8) / c ^ (n + 2) * ((1 + t) ^ 2)⁻¹ := by
        rw [div_mul_eq_div_div, div_eq_mul_inv _ ((1 + t) ^ 2)]

theorem integrableOn_binetMu_integrand {z : ℂ} (hz : z ∈ slitPlane) :
    IntegrableOn (fun t : ℝ => (binetWeight t : ℂ) / (z + t) ^ 2) (Ioi 0) := by
  obtain ⟨c, hc, h⟩ := exists_mul_one_add_le_norm_add hz
  refine (integrableOn_recip_one_add_sq.const_mul ((1 / 8) / c ^ 2)).mono' ?_ ?_
  · refine (Measurable.aestronglyMeasurable ?_)
    exact (Complex.measurable_ofReal.comp measurable_binetWeight).div
      ((measurable_const.add Complex.measurable_ofReal).pow_const 2)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht' : (0 : ℝ) ≤ t := le_of_lt ht
    simpa using norm_binetWeight_div_le hc ht' (h t ht') 0

theorem hasDerivAt_binetMu_integrand {z : ℂ} {t : ℝ} (hzt : z + t ≠ 0) :
    HasDerivAt (fun w : ℂ => (binetWeight t : ℂ) / (w + t) ^ 2)
      (-2 * (binetWeight t : ℂ) / (z + t) ^ 3) z := by
  have h := (((hasDerivAt_id z).add_const (t : ℂ)).pow 2).inv (pow_ne_zero 2 hzt)
  have h2 := h.const_mul (binetWeight t : ℂ)
  convert h2 using 1
  · ext w; simp [div_eq_mul_inv]
  · field_simp
    simp
    ring

theorem hasDerivAt_binetMu {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt binetMu
      (∫ t in Ioi (0 : ℝ), -2 * (binetWeight t : ℂ) / (z + t) ^ 3) z := by
  obtain ⟨c, hc, h⟩ := exists_ball_mul_one_add_le_norm_add hz
  have hmeas : ∀ w : ℂ, AEStronglyMeasurable
      (fun t : ℝ => (binetWeight t : ℂ) / (w + t) ^ 2) (volume.restrict (Ioi 0)) := fun w =>
    ((Complex.measurable_ofReal.comp measurable_binetWeight).div
      ((measurable_const.add Complex.measurable_ofReal).pow_const 2)).aestronglyMeasurable
  have hne : ∀ w ∈ Metric.ball z c, ∀ t : ℝ, 0 ≤ t → w + t ≠ 0 := fun w hw t ht hwt => by
    have := h w hw t ht
    rw [hwt, norm_zero] at this
    nlinarith
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds z hc)
    (F' := fun w t => -2 * (binetWeight t : ℂ) / (w + t) ^ 3)
    (Eventually.of_forall hmeas) (integrableOn_binetMu_integrand hz) ?_ ?_
    (integrableOn_recip_one_add_sq.const_mul (2 * ((1 / 8) / c ^ 3))) ?_).2
  · exact (((measurable_const.mul (Complex.measurable_ofReal.comp measurable_binetWeight)).div
      ((measurable_const.add Complex.measurable_ofReal).pow_const 3))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht w hw
    have ht' : (0 : ℝ) ≤ t := le_of_lt ht
    have hb := norm_binetWeight_div_le hc ht' (h w hw t ht') 1
    rw [mul_div_assoc, norm_mul]
    simp only [norm_neg, Complex.norm_ofNat]
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht w hw
    exact hasDerivAt_binetMu_integrand (hne w hw t (le_of_lt ht))

theorem differentiableOn_binetMu : DifferentiableOn ℂ binetMu slitPlane := fun _ hz =>
  (hasDerivAt_binetMu hz).differentiableAt.differentiableWithinAt

/-! ### Agreement with the Laplace form on the positive reals -/

theorem binetMu_ofReal (x : ℝ) : binetMu x = binetMuReal x := by
  unfold binetMu binetMuReal
  rw [← integral_complex_ofReal]
  congr 1
  ext t
  push_cast
  rfl

theorem integrableOn_binetMuReal_integrand {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => binetWeight t / (x + t) ^ 2) (Ioi 0) := by
  have hz : (x : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.2 hx
  refine IntegrableOn.congr_fun (integrableOn_binetMu_integrand hz).norm (fun t ht => ?_)
    measurableSet_Ioi
  have ht' : (0 : ℝ) < t := ht
  rw [show (x : ℂ) + t = ((x + t : ℝ) : ℂ) by push_cast; ring, ← ofReal_pow, ← ofReal_div,
    Complex.norm_real, Real.norm_of_nonneg (div_nonneg (binetWeight_nonneg t) (by positivity))]

theorem setIntegral_Ioi_one_eq (f : ℝ → ℝ) :
    ∫ t in Ioi (1 : ℝ), f t = ∫ s in Ioi (0 : ℝ), f (s + 1) := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi,
    ← integral_add_right_eq_self _ (1 : ℝ)]
  congr 1
  ext s
  by_cases hs : 0 < s
  · simp [hs, show (1 : ℝ) < s + 1 by linarith]
  · simp [hs, show ¬ (1 : ℝ) < s + 1 by linarith]

/-- `∫₀¹ P(t)/(x+t)² dt = (x + 1/2) log(1 + 1/x) - 1`. -/
theorem integral_binetWeight_div_zero_one {x : ℝ} (hx : 0 < x) :
    ∫ t in (0 : ℝ)..1, binetWeight t / (x + t) ^ 2 =
      (x + 1 / 2) * (Real.log (x + 1) - Real.log x) - 1 := by
  set G : ℝ → ℝ := fun t =>
    (-t + (2 * x + 1) * Real.log (x + t) + x * (x + 1) / (x + t)) / 2 with hG
  have hint : IntervalIntegrable (fun t : ℝ => binetWeight t / (x + t) ^ 2) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2
      ((integrableOn_binetMuReal_integrand hx).mono_set Ioc_subset_Ioi_self)
  have hcont : ContinuousOn G (Icc 0 1) := by
    have hpos : ∀ t ∈ Icc (0 : ℝ) 1, x + t ≠ 0 := fun t ht => by
      have := ht.1; positivity
    refine ContinuousOn.div_const ?_ _
    refine ((continuousOn_neg.add ?_).add ?_)
    · exact continuousOn_const.mul
        ((continuousOn_const.add continuousOn_id).log fun t ht => hpos t ht)
    · exact continuousOn_const.div (continuousOn_const.add continuousOn_id) hpos
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont (fun t ht => ?_)
    hint]
  · simp only [hG, add_zero]
    have hx1 : x + 1 ≠ 0 := by positivity
    field_simp
    ring
  · have hxt : 0 < x + t := by linarith [ht.1]
    have h1 := ((hasDerivAt_id t).const_add x).log hxt.ne'
    have h2 := ((hasDerivAt_id t).const_add x).inv hxt.ne'
    have h := ((((hasDerivAt_id t).neg).add (h1.const_mul (2 * x + 1))).add
      (h2.const_mul (x * (x + 1)))).div_const 2
    rw [binetWeight_of_mem_Ico ⟨ht.1.le, ht.2⟩]
    convert h using 1
    · ext s; simp [hG, div_eq_mul_inv]
    · simp only [id]
      field_simp
      ring

theorem binetMuReal_sub_add_one {x : ℝ} (hx : 0 < x) :
    binetMuReal x - binetMuReal (x + 1) =
      (x + 1 / 2) * (Real.log (x + 1) - Real.log x) - 1 := by
  have hI := integrableOn_binetMuReal_integrand hx
  have hsplit := intervalIntegral.integral_interval_add_Ioi hI
    (hI.mono_set (Ioi_subset_Ioi zero_le_one))
  rw [← integral_binetWeight_div_zero_one hx, binetMuReal, ← hsplit, setIntegral_Ioi_one_eq,
    binetMuReal]
  have : ∀ s : ℝ, binetWeight (s + 1) / (x + (s + 1)) ^ 2 = binetWeight s / (x + 1 + s) ^ 2 :=
    fun s => by rw [binetWeight_add_one]; ring_nf
  simp only [this]
  ring

theorem binetIntegral_sub_add_one {x : ℝ} (hx : 0 < x) :
    binetIntegral x - binetIntegral (x + 1) =
      (x + 1 / 2) * (Real.log (x + 1) - Real.log x) - 1 := by
  have h0 := log_Gamma_eq_add_binetIntegral hx
  have h1 := log_Gamma_eq_add_binetIntegral (x := x + 1) (by linarith)
  rw [Real.Gamma_add_one hx.ne', Real.log_mul hx.ne' (Real.Gamma_pos_of_pos hx).ne'] at h1
  linarith

theorem integral_recip_add_sq {y : ℝ} (hy : 0 < y) :
    ∫ t in Ioi (0 : ℝ), 1 / (y + t) ^ 2 = 1 / y := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg' (a := 0) (l := 0)
    (g := fun t : ℝ => -(y + t)⁻¹) (g' := fun t => 1 / (y + t) ^ 2)
    (fun t ht => by
      have hyt : y + t ≠ 0 := by have : (0 : ℝ) ≤ t := ht; positivity
      convert (((hasDerivAt_id t).const_add y).inv hyt).neg using 1
      · funext s; simp
      · simp [neg_div])
    (fun t _ => by positivity) ?_
  · rw [h]; simp
  · have : Tendsto (fun t : ℝ => y + t) atTop atTop := tendsto_atTop_add_const_left _ _ tendsto_id
    simpa using this.inv_tendsto_atTop.neg

theorem binetMuReal_nonneg (x : ℝ) : 0 ≤ binetMuReal x :=
  setIntegral_nonneg measurableSet_Ioi fun t _ => div_nonneg (binetWeight_nonneg t) (sq_nonneg _)

theorem binetMuReal_le {x : ℝ} (hx : 0 < x) : binetMuReal x ≤ 1 / (8 * x) := by
  have hI : IntegrableOn (fun t : ℝ => 1 / (x + t) ^ 2) (Ioi 0) := by
    refine integrableOn_Ioi_deriv_of_nonneg' (g := fun t : ℝ => -(x + t)⁻¹) (l := 0)
      (fun t ht => ?_) (fun t _ => by positivity) ?_
    · have hxt : x + t ≠ 0 := by have : (0 : ℝ) ≤ t := ht; positivity
      convert (((hasDerivAt_id t).const_add x).inv hxt).neg using 1
      · funext s; simp
      · simp [neg_div]
    · have : Tendsto (fun t : ℝ => x + t) atTop atTop :=
        tendsto_atTop_add_const_left _ _ tendsto_id
      simpa using this.inv_tendsto_atTop.neg
  calc binetMuReal x ≤ ∫ t in Ioi (0 : ℝ), (1 / 8) * (1 / (x + t) ^ 2) := by
        refine setIntegral_mono_on (integrableOn_binetMuReal_integrand hx) (hI.const_mul _)
          measurableSet_Ioi fun t ht => ?_
        have : (0 : ℝ) < x + t := by have : (0 : ℝ) < t := ht; positivity
        rw [← mul_div_assoc, mul_one]
        exact div_le_div_of_nonneg_right (binetWeight_le t) (by positivity)
    _ = 1 / (8 * x) := by
        rw [integral_const_mul, integral_recip_add_sq hx]
        field_simp

theorem binetMuReal_eq_binetIntegral {x : ℝ} (hx : 0 < x) : binetMuReal x = binetIntegral x := by
  set D : ℝ → ℝ := fun y => binetMuReal y - binetIntegral y with hD
  have hper : ∀ n : ℕ, D x = D (x + n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hxn : 0 < x + n := by positivity
      have h1 := binetMuReal_sub_add_one hxn
      have h2 := binetIntegral_sub_add_one hxn
      rw [ih]
      simp only [hD, Nat.cast_succ, ← add_assoc]
      linarith
  have hbd : ∀ n : ℕ, |D x| ≤ (1 / 4) / (x + n) := by
    intro n
    have hxn : 0 < x + n := by positivity
    rw [hper n]
    have h1 := binetMuReal_nonneg (x + n)
    have h2 := binetMuReal_le hxn
    have h3 := binetIntegral_mem hxn
    have e1 : 1 / (8 * (x + n)) = (1 / 8) / (x + n) := by field_simp
    have e2 : 1 / (12 * (x + n)) = (1 / 12) / (x + n) := by field_simp
    have e3 : (1 / 4) / (x + n) = (1 / 8) / (x + n) + (1 / 8) / (x + n) := by ring
    have e4 : (1 / 12) / (x + n) ≤ (1 / 8) / (x + n) :=
      div_le_div_of_nonneg_right (by norm_num) hxn.le
    rw [abs_le]
    simp only [hD]
    constructor <;> linarith
  have hlim : Tendsto (fun n : ℕ => (1 / 4) / (x + n)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop)
  have h0 : |D x| ≤ 0 := ge_of_tendsto' hlim hbd
  have : D x = 0 := abs_nonpos_iff.1 h0
  simpa [hD, sub_eq_zero] using this

/-! ### Binet's formula on the slit plane -/

/-- The Stirling exponent `(z - 1/2) log z - z + (1/2) log 2π + μ(z)`. -/
def binetExponent (z : ℂ) : ℂ :=
  (z - 1 / 2) * log z - z + (1 / 2) * log (2 * π) + binetMu z

theorem differentiableOn_binetExponent : DifferentiableOn ℂ binetExponent slitPlane := by
  intro z hz
  have hlog : DifferentiableAt ℂ log z := differentiableAt_log hz
  have hmu : DifferentiableAt ℂ binetMu z :=
    (differentiableOn_binetMu z hz).differentiableAt (isOpen_slitPlane.mem_nhds hz)
  have h : DifferentiableAt ℂ
      (fun w => (w - 1 / 2) * log w - w + (1 / 2) * log (2 * π) + binetMu w) z :=
    ((((differentiableAt_id.sub_const _).mul hlog).sub differentiableAt_id).add_const _).add hmu
  exact h.differentiableWithinAt

theorem binetExponent_ofReal {x : ℝ} (hx : 0 < x) :
    binetExponent x = (Real.log (Real.Gamma x) : ℂ) := by
  rw [log_Gamma_eq_add_binetIntegral hx, binetExponent, binetMu_ofReal,
    binetMuReal_eq_binetIntegral hx, ← ofReal_log hx.le,
    show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; ring, ← ofReal_log (by positivity)]
  push_cast
  ring

/-- Binet's formula `Γ(z) = exp((z - 1/2) log z - z + (1/2) log 2π + μ(z))` on the slit plane
(DLMF 5.11.1 with the remainder in closed form). -/
@[dlmf 5.11.E1]
theorem Gamma_eq_exp_binetExponent {z : ℂ} (hz : z ∈ slitPlane) :
    Complex.Gamma z = exp (binetExponent z) := by
  have hGamma : DifferentiableOn ℂ Complex.Gamma slitPlane := fun w hw => by
    refine (Complex.differentiableAt_Gamma w fun m hm => ?_).differentiableWithinAt
    rw [hm] at hw
    rcases mem_slitPlane_iff.1 hw with h | h
    · simp at h; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    · simp at h
  have hexp : DifferentiableOn ℂ (fun w => exp (binetExponent w)) slitPlane :=
    differentiableOn_binetExponent.cexp
  refine AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq (z₀ := 1)
    (hGamma.analyticOnNhd isOpen_slitPlane) (hexp.analyticOnNhd isOpen_slitPlane)
    (Complex.starConvex_one_slitPlane.isPathConnected one_mem_slitPlane).isConnected.isPreconnected
    one_mem_slitPlane ?_ hz
  have hev : ∀ᶠ x : ℝ in 𝓝[≠] 1, Complex.Gamma x = exp (binetExponent x) := by
    filter_upwards [nhdsWithin_le_nhds (lt_mem_nhds one_pos)] with x hx
    rw [binetExponent_ofReal hx, ← ofReal_exp, Real.exp_log (Real.Gamma_pos_of_pos hx),
      Complex.Gamma_ofReal]
  have ht : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] 1) (𝓝[≠] 1) :=
    Complex.continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin fun x hx => by
      simpa using hx
  simpa using ht.frequently hev.frequently

/-! ### Stieltjes' bound -/

theorem norm_add_sq_ge {z : ℂ} (hz : z ≠ 0) (t : ℝ) :
    (‖z‖ + z.re) * (‖z‖ + t) ^ 2 ≤ 2 * ‖z‖ * ‖z + t‖ ^ 2 := by
  have hr : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hsq : ‖z + t‖ ^ 2 = (z.re + t) ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp; ring
  have hr2 : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have hx : z.re ≤ ‖z‖ := re_le_norm z
  rw [hsq]
  nlinarith [mul_nonneg (sub_nonneg.2 hx) (sq_nonneg (‖z‖ - t))]

/-- Stieltjes' bound `|μ(z)| ≤ 1/(6(|z| + Re z))` on the slit plane. -/
theorem norm_binetMu_le {z : ℂ} (hz : z ∈ slitPlane) :
    ‖binetMu z‖ ≤ 1 / (6 * (‖z‖ + z.re)) := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  set r := ‖z‖ with hr_def
  have hr : 0 < r := norm_pos_iff.2 hz0
  have hrx : 0 < r + z.re := by
    rcases mem_slitPlane_iff.1 hz with h | h
    · linarith [re_le_norm z]
    · have : |z.re| < r := by
        have h2 := Complex.normSq_eq_norm_sq z
        rw [Complex.normSq_apply] at h2
        have him : 0 < z.im * z.im := mul_self_pos.2 h
        have : z.re ^ 2 < r ^ 2 := by nlinarith
        exact abs_lt_of_sq_lt_sq this hr.le
      linarith [neg_abs_le z.re]
  set K := 2 * r / (r + z.re) with hK
  have hKpos : 0 < K := by positivity
  calc ‖binetMu z‖ ≤ ∫ t in Ioi (0 : ℝ), K * (binetWeight t / (r + t) ^ 2) := by
        refine norm_integral_le_of_norm_le
          ((integrableOn_binetMuReal_integrand hr).const_mul K) ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht' : (0 : ℝ) < t := ht
        have hzt : 0 < ‖z + t‖ := norm_pos_iff.2 fun h => by
          have := slitPlane_ne_zero (z := z + t) ?_
          · exact this h
          rcases mem_slitPlane_iff.1 hz with h' | h'
          · exact mem_slitPlane_iff.2 (Or.inl (by simp; linarith))
          · exact mem_slitPlane_iff.2 (Or.inr (by simpa using h'))
        rw [norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg (binetWeight_nonneg t),
          hK, ← mul_div_assoc, div_mul_eq_mul_div, div_div, div_le_div_iff₀ (by positivity)
          (by positivity)]
        have h1 := norm_add_sq_ge hz0 t
        have hw := binetWeight_nonneg t
        nlinarith [mul_le_mul_of_nonneg_left h1 hw]
    _ = K * binetIntegral r := by
        rw [integral_const_mul, ← binetMuReal, binetMuReal_eq_binetIntegral hr]
    _ ≤ K * (1 / (12 * r)) := mul_le_mul_of_nonneg_left (binetIntegral_mem hr).2 hKpos.le
    _ = 1 / (6 * (r + z.re)) := by
        rw [hK]; field_simp; ring

/-- `|μ(z)| ≤ 1/(6|z|)` in the closed right half-plane minus the origin. -/
theorem norm_binetMu_le_of_re_nonneg {z : ℂ} (hz : z ≠ 0) (hre : 0 ≤ z.re) :
    ‖binetMu z‖ ≤ 1 / (6 * ‖z‖) := by
  have hzs : z ∈ slitPlane := by
    rcases hre.lt_or_eq with h | h
    · exact mem_slitPlane_iff.2 (Or.inl h)
    · refine mem_slitPlane_iff.2 (Or.inr fun him => hz ?_)
      exact Complex.ext (by simpa using h.symm) (by simpa using him)
  have hr : 0 < ‖z‖ := norm_pos_iff.2 hz
  refine (norm_binetMu_le hzs).trans ?_
  gcongr
  linarith

/-! ### Consequences for `|Γ|` -/

theorem re_binetExponent (z : ℂ) :
    (binetExponent z).re = (z.re - 1 / 2) * Real.log ‖z‖ - z.im * arg z - z.re +
      (1 / 2) * Real.log (2 * π) + (binetMu z).re := by
  have h2 : log (2 * π : ℂ) = ((Real.log (2 * π) : ℝ) : ℂ) := by
    rw [ofReal_log (by positivity)]; push_cast; ring_nf
  simp [binetExponent, h2, log_re, log_im]

/-- `|Γ(z)| = √(2π) |z|^{Re z - 1/2} e^{-(Re z + Im z · arg z)} e^{Re μ(z)}` on the slit plane. -/
theorem norm_Gamma_eq_binet {z : ℂ} (hz : z ∈ slitPlane) :
    ‖Complex.Gamma z‖ = Real.sqrt (2 * π) * ‖z‖ ^ (z.re - 1 / 2) *
      Real.exp (-(z.re + z.im * arg z)) * Real.exp (binetMu z).re := by
  have hr : 0 < ‖z‖ := norm_pos_iff.2 (slitPlane_ne_zero hz)
  rw [Gamma_eq_exp_binetExponent hz, norm_exp, re_binetExponent, Real.sqrt_eq_rpow,
    Real.rpow_def_of_pos (by positivity), Real.rpow_def_of_pos hr, ← Real.exp_add,
    ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

theorem mul_cos_le_sin {ψ : ℝ} (h0 : 0 ≤ ψ) (h1 : ψ ≤ π / 2) : ψ * Real.cos ψ ≤ Real.sin ψ := by
  rcases h1.lt_or_eq with h | h
  · have hc : 0 < Real.cos ψ := Real.cos_pos_of_mem_Ioo ⟨by linarith, h⟩
    have ht := Real.le_tan h0 h
    rw [Real.tan_eq_sin_div_cos, le_div_iff₀ hc] at ht
    exact ht
  · rw [h, Real.cos_pi_div_two, Real.sin_pi_div_two]; norm_num

theorem pi_div_two_mul_abs_sin_le {θ : ℝ} (hθ : |θ| ≤ π / 2) :
    π / 2 * |Real.sin θ| ≤ Real.cos θ + θ * Real.sin θ := by
  have key : ∀ φ : ℝ, 0 ≤ φ → φ ≤ π / 2 →
      π / 2 * |Real.sin φ| ≤ Real.cos φ + φ * Real.sin φ := by
    intro φ h0 h1
    have hψ := mul_cos_le_sin (ψ := π / 2 - φ) (by linarith) (by linarith)
    rw [Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub] at hψ
    rw [abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [Real.pi_pos]))]
    nlinarith
  rcases le_total 0 θ with h | h
  · exact key θ h (le_of_abs_le hθ)
  · have := key (-θ) (by linarith) (by linarith [neg_abs_le θ, abs_neg θ ▸ hθ, neg_le_abs θ])
    simpa [Real.sin_neg, Real.cos_neg, abs_neg] using this

/-- In the closed right half-plane, `(π/2) |Im z| ≤ Re z + Im z · arg z`. -/
theorem pi_div_two_mul_abs_im_le {z : ℂ} (hre : 0 ≤ z.re) :
    π / 2 * |z.im| ≤ z.re + z.im * arg z := by
  have hθ : |arg z| ≤ π / 2 := abs_arg_le_pi_div_two_iff.2 hre
  have h := pi_div_two_mul_abs_sin_le hθ
  have hr : 0 ≤ ‖z‖ := norm_nonneg z
  rw [← norm_mul_cos_arg z, ← norm_mul_sin_arg z, abs_mul, abs_of_nonneg hr]
  nlinarith [mul_le_mul_of_nonneg_left h hr]

/-- On a vertical line, `|Γ(x+iy)| / (√(2π) y^{x-1/2} e^{-πy/2}) → 1` as `y → +∞`. -/
theorem tendsto_norm_Gamma_vertical_div (x : ℝ) :
    Tendsto (fun y : ℝ => ‖Complex.Gamma (x + I * y)‖ /
      (Real.sqrt (2 * π) * |y| ^ (x - 1 / 2) * Real.exp (-π * |y| / 2))) atTop (𝓝 1) := by
  set z : ℝ → ℂ := fun y => x + I * y with hz
  set r : ℝ → ℝ := fun y => ‖z y‖ with hr
  have hre : ∀ y, (z y).re = x := fun y => by simp [hz]
  have him : ∀ y, (z y).im = y := fun y => by simp [hz]
  have hr2 : ∀ y, r y ^ 2 = x ^ 2 + y ^ 2 := fun y => by
    rw [hr, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hre, him]; ring
  have hry : ∀ y, |y| ≤ r y := fun y => by
    simpa [him] using abs_im_le_norm (z y)
  -- `r/y → 1`
  have hratio : Tendsto (fun y => r y / y) atTop (𝓝 1) := by
    have h1 : Tendsto (fun y : ℝ => Real.sqrt (1 + (x / y) ^ 2)) atTop (𝓝 1) := by
      have : Tendsto (fun y : ℝ => x / y) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_id
      have h := ((this.pow 2).const_add 1).sqrt
      simpa using h
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with y hy
    have hry' : r y = Real.sqrt (x ^ 2 + y ^ 2) := by
      rw [← hr2, Real.sqrt_sq (norm_nonneg _)]
    rw [hry', show 1 + (x / y) ^ 2 = (x ^ 2 + y ^ 2) / y ^ 2 by field_simp; ring,
      Real.sqrt_div' _ (sq_nonneg y), Real.sqrt_sq hy.le]
  -- the argument term
  have harg : Tendsto (fun y => π * y / 2 - x - y * arg (z y)) atTop (𝓝 0) := by
    set u : ℝ → ℝ := fun y => x / r y with hu
    have hrpos : ∀ᶠ y in atTop, 0 < r y := by
      filter_upwards [eventually_gt_atTop 0] with y hy
      exact lt_of_lt_of_le hy ((le_abs_self y).trans (hry y))
    have hrtop : Tendsto r atTop atTop :=
      tendsto_atTop_mono' atTop (Eventually.of_forall fun y => (le_abs_self y).trans (hry y))
        tendsto_id
    have hu0 : Tendsto u atTop (𝓝 0) := tendsto_const_nhds.div_atTop hrtop
    have hyr : Tendsto (fun y => y / r y) atTop (𝓝 1) := by
      have := hratio.inv₀ one_ne_zero
      simp only [inv_one] at this
      refine this.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with y hy
      simp [inv_div]
    have heq : ∀ᶠ y in atTop, π * y / 2 - x - y * arg (z y) =
        y * (Real.arcsin (u y) - u y) + x * (y / r y - 1) := by
      filter_upwards [eventually_gt_atTop 0, hrpos] with y hy hrp
      rw [arg_of_im_pos (by rw [him]; exact hy), Real.arccos_eq_pi_div_two_sub_arcsin, hre]
      simp only [hu]
      field_simp
      ring
    refine Tendsto.congr' (EventuallyEq.symm heq) ?_
    rw [show (0 : ℝ) = 0 + x * (1 - 1) by ring]
    refine Tendsto.add ?_ ((hyr.sub_const 1).const_mul x)
    -- `arcsin u - u = o(u)` and `y u = x y / r` is bounded
    have hd : HasDerivAt Real.arcsin 1 0 := by
      simpa using Real.hasDerivAt_arcsin (x := 0) (by norm_num) (by norm_num)
    have ho := hasDerivAt_iff_isLittleO_nhds_zero.1 hd
    simp only [zero_add, Real.arcsin_zero, sub_zero, smul_eq_mul, mul_one] at ho
    have ho' : (fun y => Real.arcsin (u y) - u y) =o[atTop] u := ho.comp_tendsto hu0
    have hyu : (fun y => y * u y) =O[atTop] (fun _ => (1 : ℝ)) := by
      have : Tendsto (fun y => y * u y) atTop (𝓝 (x * 1)) := by
        refine (hyr.const_mul x).congr' ?_
        filter_upwards with y
        simp only [hu]; ring
      exact this.isBigO_one ℝ
    have h1 : (fun y => y * (Real.arcsin (u y) - u y)) =o[atTop] (fun y => y * u y) :=
      (Asymptotics.isBigO_refl (fun y : ℝ => y) atTop).mul_isLittleO ho'
    exact (h1.trans_isBigO hyu).tendsto_div_nhds_zero.congr (fun y => by simp)
  -- the `μ` term
  have hmu : Tendsto (fun y => (binetMu (z y)).re) atTop (𝓝 0) := by
    have htop : Tendsto (fun y => 6 * (r y + x)) atTop atTop := by
      refine Tendsto.const_mul_atTop (by norm_num) (tendsto_atTop_add_const_right _ _ ?_)
      exact tendsto_atTop_mono' atTop
        (Eventually.of_forall fun y => (le_abs_self y).trans (hry y)) tendsto_id
    have hb := (tendsto_const_nhds (x := (1 : ℝ))).div_atTop htop
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [eventually_gt_atTop 0] with y hy
    have hzs : z y ∈ slitPlane := mem_slitPlane_iff.2 (Or.inr (by rw [him]; exact hy.ne'))
    refine (abs_re_le_norm _).trans ?_
    have := norm_binetMu_le hzs
    rwa [hre] at this
  -- assemble
  have hlim : Tendsto (fun y => (r y / y) ^ (x - 1 / 2) *
      Real.exp ((π * y / 2 - x - y * arg (z y)) + (binetMu (z y)).re)) atTop (𝓝 1) := by
    have h1 := hratio.rpow_const (p := x - 1 / 2) (Or.inl one_ne_zero)
    have h0 : Tendsto (fun y => (π * y / 2 - x - y * arg (z y)) + (binetMu (z y)).re) atTop
        (𝓝 0) := by simpa using harg.add hmu
    have h2 := (Real.continuous_exp.tendsto 0).comp h0
    simpa using h1.mul h2
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with y hy
  have hzs : z y ∈ slitPlane := mem_slitPlane_iff.2 (Or.inr (by rw [him]; exact hy.ne'))
  have hrp : 0 < r y := lt_of_lt_of_le hy ((le_abs_self y).trans (hry y))
  show _ = ‖Complex.Gamma (z y)‖ / _
  rw [norm_Gamma_eq_binet hzs, hre, him, abs_of_pos hy, Real.div_rpow hrp.le hy.le]
  have hs : 0 < Real.sqrt (2 * π) := by positivity
  have hyp : 0 < y ^ (x - 1 / 2) := Real.rpow_pos_of_pos hy _
  rw [Real.exp_add, show π * y / 2 - x - y * arg (z y) =
    -(x + y * arg (z y)) - (-π * y / 2) by ring, Real.exp_sub]
  field_simp
  rfl

end DLMF.Gamma
