/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.Basic.ExponentialIntegrals

public import DLMF.Confluent.IncompleteGamma
public import TauCeti.Analysis.Contour.WorkedExamples.HalfDisc.SineIntegral

/-!
# Exponential, sine and cosine integrals (Temme §7.3.5; DLMF Chapter 6, §§8.19–8.20)

The generalized exponential integral is `E_p(z) = z^{p-1} Γ(1-p, z)` (DLMF 8.19.1), defined
through the project's Tricomi-based `upperIncGamma`. Its integral representation, recurrence,
derivative and asymptotic expansion follow from the corresponding properties of `U`.
For `p = 1` the classical function `E₁` is related to the entire function `Ein` and Euler's
constant, which gives its power series. The sine and cosine integrals `Si`, `Ci` are defined
on the real line together with their power series.

## Main results

* `genExpIntE_eq_exp_mul_kummerU`: `E_p(z) = e^{-z} U(1, 2-p, z)`.
* `genExpIntE_eq_integral`: `E_p(x) = ∫₁^∞ e^{-xt} t^{-p} dt` for `x > 0`.
* `genExpIntE_add_one`, `hasDerivAt_genExpIntE`: recurrence and derivative.
* `hasAsymptoticExpansion_genExpIntE`: `E_p(x) ~ e^{-x}/x ∑ (-1)^k (p)_k x^{-k}`.
* `genExpIntE_one_eq_Ein`, `genExpIntE_one_eq_tsum`: `E₁(x) = Ein(x) - log x - γ` and
  its power series.
* `Real.hasSum_sinInt`, `Real.tendsto_sinInt_atTop`: the series of `Si` and `Si(∞) = π/2`.
* `Real.cosInt_eq_tsum`, `Real.hasDerivAt_cosInt`: the series and derivative of `Ci`.

The limit `Ci(x) → 0` (DLMF 6.2.14) and the Laplace-type representations of the auxiliary
functions `f`, `g` (DLMF 6.2.17–6.2.20) are not formalized here.
-/

@[expose] public section

open Complex Filter MeasureTheory Asymptotics Set
open scoped Real Topology Nat
open DLMF.Hypergeometric

noncomputable section

namespace DLMF.Confluent

/-- `E_p(z) = z^{p-1} e^{-z} U(p, p, z)` (Temme §7.3.5). -/
@[dlmf 8.19.E16]
theorem genExpIntE_eq_cpow_mul_kummerU (p z : ℂ) :
    genExpIntE p z = z ^ (p - 1) * exp (-z) * kummerU p p z := by
  rw [genExpIntE, upperIncGamma, sub_sub_cancel]
  ring

/-- `E_p(z) = e^{-z} U(1, 2-p, z)` (Temme §7.3.5). -/
theorem genExpIntE_eq_exp_mul_kummerU (p : ℂ) {z : ℂ} (hz : z ≠ 0) :
    genExpIntE p z = exp (-z) * kummerU 1 (2 - p) z := by
  rw [genExpIntE, upperIncGamma_eq_cpow_mul_kummerU _ hz, show 1 - p + 1 = 2 - p by ring,
    ← mul_assoc, ← mul_assoc, ← Complex.cpow_add _ _ hz]
  simp

/-- **The exponential integral** (DLMF 8.19.3): `E_p(x) = ∫₁^∞ e^{-xt} t^{-p} dt` for `x > 0`
and all complex `p`. -/
@[dlmf 8.19.E3]
theorem genExpIntE_eq_integral (p : ℂ) {x : ℝ} (hx : 0 < x) :
    genExpIntE p x = ∫ t in Ioi (1 : ℝ), Real.exp (-x * t) • (t : ℂ) ^ (-p) := by
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  rw [genExpIntE, upperIncGamma_eq_cpow_mul_integral_Ioi_one _ hx, ← mul_assoc,
    ← Complex.cpow_add _ _ hx0]
  simp [show 1 - p - 1 = -p by ring]

/-- `E_0(z) = e^{-z}/z`. -/
@[dlmf 8.19.E5]
theorem genExpIntE_zero {z : ℂ} (hz : z ≠ 0) : genExpIntE 0 z = exp (-z) / z := by
  rw [genExpIntE, sub_zero, upperIncGamma_one, zero_sub, Complex.cpow_neg_one]
  field_simp

/-- The recurrence (DLMF 8.19.12): `p E_{p+1}(z) + z E_p(z) = e^{-z}`. -/
@[dlmf 8.19.E12]
theorem genExpIntE_add_one (p : ℂ) {z : ℂ} (hz : z ≠ 0) :
    p * genExpIntE (p + 1) z + z * genExpIntE p z = exp (-z) := by
  have h := upperIncGamma_add_one (-p) hz
  rw [show -p + 1 = 1 - p by ring] at h
  rw [genExpIntE, genExpIntE, show 1 - (p + 1) = -p by ring, show p + 1 - 1 = p by ring, h]
  have hzp : z * z ^ (p - 1) = z ^ p := by
    conv_rhs => rw [show p = 1 + (p - 1) by ring]
    rw [Complex.cpow_add _ _ hz, Complex.cpow_one]
  have hp : z ^ p * z ^ (-p) = 1 := by rw [← Complex.cpow_add _ _ hz]; simp
  linear_combination (exp (-z)) * hp +
    (-p * upperIncGamma (-p) z + z ^ (-p) * exp (-z)) * hzp

/-- The derivative (DLMF 8.19.13): `E_p'(z) = -E_{p-1}(z)` on the cut plane. -/
@[dlmf 8.19.E13]
theorem hasDerivAt_genExpIntE (p : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (genExpIntE p) (-genExpIntE (p - 1) z) z := by
  have hz0 := slitPlane_ne_zero hz
  have hU := (hasDerivAt_kummerU 1 (2 - p) hz)
  have hd := ((hasDerivAt_neg z).cexp).mul hU
  have hrel := kummerU_contiguous_a_b 1 (3 - p) z hz0
  rw [show (3 : ℂ) - p - 1 = 2 - p by ring, show (1 : ℂ) + 1 = 2 by norm_num] at hrel
  refine (hd.congr_deriv ?_).congr_of_eventuallyEq ?_
  · rw [genExpIntE_eq_exp_mul_kummerU _ hz0, show 2 - (p - 1) = 3 - p by ring,
      show (1 : ℂ) + 1 = 2 by norm_num, show 2 - p + 1 = 3 - p by ring]
    linear_combination exp (-z) * hrel
  · filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
    exact genExpIntE_eq_exp_mul_kummerU p (slitPlane_ne_zero hw)

/-- **Asymptotic expansion of `E_p(x)`** (DLMF 8.20.2, Temme §7.3.5):
`E_p(x) ~ e^{-x}/x ∑ (-1)^k (p)_k x^{-k}` as `x → +∞`, for all complex `p`. -/
@[dlmf 8.20.E2]
theorem hasAsymptoticExpansion_genExpIntE (p : ℂ) :
    HasAsymptoticExpansion atTop (fun (k : ℕ) (x : ℝ) => exp (-(x : ℂ)) * (x : ℂ) ^ (-1 - k : ℂ))
      (fun k => (-1) ^ k * poch p k) (fun x : ℝ => genExpIntE p x) := by
  refine (((hasAsymptoticExpansion_kummerU 1 (2 - p)).mul_left
    (fun x : ℝ => exp (-(x : ℂ)))).congr_scale fun k => Eventually.of_forall fun x => ?_
    ).congr_coeff ?_ |>.congr' ?_
  · simp only
    ring_nf
  · funext k
    rw [tricomiCoeff, poch_nat_one, show 1 - (2 - p) + 1 = p by ring]
    have hf : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
    field_simp
  · filter_upwards [eventually_gt_atTop 0] with x hx
    rw [genExpIntE_eq_exp_mul_kummerU _ (Complex.ofReal_ne_zero.mpr hx.ne'), smul_eq_mul]

/-! ### The exponential integral `E₁` -/

/-- `E₁(x) = ∫ₓ^∞ e^{-t}/t dt` for `x > 0` (DLMF 6.2.1). -/
@[dlmf 6.2.E1]
theorem genExpIntE_one_eq_integral {x : ℝ} (hx : 0 < x) :
    genExpIntE 1 x = ((∫ t in Ioi x, Real.exp (-t) / t : ℝ) : ℂ) := by
  rw [genExpIntE, sub_self, Complex.cpow_zero, one_mul, upperIncGamma_eq_integral 0 hx,
    ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht : (0 : ℝ) < t := lt_trans hx ht
  rw [zero_sub, Complex.cpow_neg_one]
  push_cast
  field_simp

/-- `(1 - e^{-t})/t` is interval integrable between nonnegative endpoints. -/
theorem intervalIntegrable_einIntegrand {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable (fun t : ℝ => (1 - Real.exp (-t)) / t) volume a b := by
  refine (intervalIntegrable_const (c := (1 : ℝ))).mono_fun'
    (by fun_prop : Measurable fun t : ℝ => (1 - Real.exp (-t)) / t).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_uIoc).mpr (Eventually.of_forall fun t ht => ?_)
  have ht0 : 0 < t := by
    rcases ht with ⟨h1, _⟩
    exact lt_of_le_of_lt (le_min ha hb) h1
  show ‖(1 - Real.exp (-t)) / t‖ ≤ 1
  rw [Real.norm_eq_abs, abs_div, abs_of_pos ht0, div_le_one ht0]
  have h1 := Real.add_one_le_exp (-t)
  have h2 : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  rw [abs_of_pos (by linarith)]
  linarith

/-- `e^{-t}/t` is integrable on `(a, ∞)` for `a > 0`. -/
theorem integrableOn_exp_neg_div {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => Real.exp (-t) / t) (Ioi a) := by
  refine ((exp_neg_integrableOn_Ioi a one_pos).const_mul a⁻¹).mono'
    ((by fun_prop : Measurable fun t : ℝ => Real.exp (-t) / t).aestronglyMeasurable) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
  have ht : a < t := ht
  have ht0 : 0 < t := lt_trans ha ht
  rw [Real.norm_eq_abs, abs_of_pos (by positivity), neg_one_mul, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_right (inv_anti₀ ha ht.le) (Real.exp_pos _).le

/-- `∫₀¹ dt/(1+t) = log 2`. -/
theorem integral_one_div_one_add_zero_one : ∫ t in (0 : ℝ)..1, 1 / (1 + t) = Real.log 2 := by
  have h := intervalIntegral.integral_comp_add_left (fun t : ℝ => 1 / t) (a := 0) (b := 1) 1
  simp only [add_zero] at h
  rw [h, integral_one_div_of_pos one_pos (by norm_num)]
  norm_num

/-- `∫₁^∞ dt/(t(1+t)) = log 2`. -/
theorem integral_Ioi_one_one_div_mul_one_add :
    ∫ t in Ioi (1 : ℝ), 1 / (t * (1 + t)) = Real.log 2 := by
  have hderiv : ∀ t ∈ Ioi (1 : ℝ), HasDerivAt (fun t => Real.log t - Real.log (1 + t))
      (1 / (t * (1 + t))) t := by
    intro t ht
    have ht : (1 : ℝ) < t := ht
    have h := (Real.hasDerivAt_log (by linarith : t ≠ 0)).sub
      ((Real.hasDerivAt_log (by linarith : 1 + t ≠ 0)).comp t ((hasDerivAt_id t).const_add 1))
    exact h.congr_deriv (by field_simp; ring)
  have hint : IntegrableOn (fun t : ℝ => 1 / (t * (1 + t))) (Ioi 1) := by
    refine (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) one_pos).mono'
      ((by fun_prop : Measurable fun t : ℝ => 1 / (t * (1 + t))).aestronglyMeasurable) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have ht : (1 : ℝ) < t := ht
    rw [Real.norm_eq_abs, abs_of_pos (by positivity), Real.rpow_neg (by linarith),
      show (2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast, one_div]
    exact inv_anti₀ (by positivity) (by nlinarith)
  have hlim : Tendsto (fun t : ℝ => Real.log t - Real.log (1 + t)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => Real.log (t / (1 + t))) atTop (𝓝 0) := by
      have h2 : Tendsto (fun t : ℝ => t / (1 + t)) atTop (𝓝 1) := by
        have h3 : Tendsto (fun t : ℝ => 1 - 1 / (1 + t)) atTop (𝓝 (1 - 0)) :=
          tendsto_const_nhds.sub ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop
            (tendsto_atTop_add_const_left _ 1 tendsto_id))
        rw [sub_zero] at h3
        refine h3.congr' ?_
        filter_upwards [eventually_gt_atTop 0] with t ht
        field_simp
        ring
      simpa [Function.comp_def] using (Real.continuousAt_log one_ne_zero).tendsto.comp h2
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    exact Real.log_div ht.ne' (by linarith)
  rw [integral_Ioi_of_hasDerivAt_of_tendsto (by fun_prop (disch := norm_num)) hderiv hint hlim]
  norm_num

/-- **`E₁` through `Ein`** (DLMF 6.2.4): `E₁(x) = Ein(x) - log x - γ` for `x > 0`. -/
@[dlmf 6.2.E4]
theorem genExpIntE_one_eq_Ein {x : ℝ} (hx : 0 < x) :
    genExpIntE 1 x =
      ((Real.expIntEin x - Real.log x - Real.eulerMascheroniConstant : ℝ) : ℂ) := by
  rw [genExpIntE_one_eq_integral hx]
  congr 1
  set f : ℝ → ℝ := fun t => Real.exp (-t) / t with hf
  set g : ℝ → ℝ := fun t => (1 - Real.exp (-t)) / t with hg
  set h : ℝ → ℝ := fun t => (1 / (1 + t) - Real.exp (-t)) / t with hh
  -- `γ = ∫₀¹ g - ∫₁^∞ f`
  have hγ : Real.eulerMascheroniConstant = (∫ t in (0 : ℝ)..1, g t) - ∫ t in Ioi (1 : ℝ), f t := by
    have hhint : IntegrableOn h (Ioi 0) := DLMF.Gamma.integrableOn_eulerIntegrand
    have hsplit := intervalIntegral.integral_Ioi_sub_Ioi hhint zero_le_one
    have h01 : ∫ t in (0 : ℝ)..1, h t = (∫ t in (0 : ℝ)..1, g t) - Real.log 2 := by
      rw [← integral_one_div_one_add_zero_one, ← intervalIntegral.integral_sub
        (intervalIntegrable_einIntegrand le_rfl zero_le_one) (by
          exact (continuousOn_of_forall_continuousAt fun t ht => by
            have : 0 ≤ t := by simp at ht; linarith [ht.1]
            fun_prop (disch := positivity)).intervalIntegrable)]
      refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun t ht => ?_)
      have ht0 : 0 < t := by simp at ht; exact ht.1
      simp only [hh]
      field_simp
      ring
    have h1 : ∫ t in Ioi (1 : ℝ), h t = Real.log 2 - ∫ t in Ioi (1 : ℝ), f t := by
      have hfi := integrableOn_exp_neg_div one_pos
      have hqi : IntegrableOn (fun t : ℝ => 1 / (t * (1 + t))) (Ioi 1) := by
        by_contra hc
        have := integral_undef hc
        rw [integral_Ioi_one_one_div_mul_one_add] at this
        exact absurd this (Real.log_pos (by norm_num)).ne'
      rw [← integral_Ioi_one_one_div_mul_one_add, ← integral_sub hqi hfi]
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      have ht : (1 : ℝ) < t := ht
      simp only [hh]
      field_simp
    rw [DLMF.Gamma.eulerMascheroni_eq_integral_recip_one_add]
    linarith [hsplit, h01, h1]
  -- `Ein(x) = ∫₀¹ g - ∫ₓ¹ g` and `log x = -∫ₓ¹ dt/t`
  have hEin : Real.expIntEin x = (∫ t in (0 : ℝ)..1, g t) - ∫ t in x..1, g t := by
    rw [Real.expIntEin, ← intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_einIntegrand le_rfl hx.le)
      (intervalIntegrable_einIntegrand hx.le zero_le_one)]
    ring
  have hlog : Real.log x = -∫ t in x..1, t⁻¹ := by
    rw [integral_inv_of_pos hx one_pos, one_div, Real.log_inv, neg_neg]
  have hE : ∫ t in Ioi x, f t = (∫ t in x..1, f t) + ∫ t in Ioi (1 : ℝ), f t := by
    rw [← intervalIntegral.integral_Ioi_sub_Ioi' (integrableOn_exp_neg_div hx)
      (integrableOn_exp_neg_div one_pos)]
    ring
  have hfg : ∫ t in x..1, f t = ∫ t in x..1, (t⁻¹ - g t) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    have ht0 : 0 < t := by
      rcases ht with ⟨h1, _⟩
      exact lt_of_lt_of_le (lt_min hx one_pos) h1
    simp only [hf, hg]
    field_simp
    ring
  have hsub : ∫ t in x..1, (t⁻¹ - g t) = (∫ t in x..1, t⁻¹) - ∫ t in x..1, g t :=
    intervalIntegral.integral_sub (intervalIntegral.intervalIntegrable_inv
      (fun t ht => by
        rcases ht with ⟨h1, _⟩
        exact (lt_of_lt_of_le (lt_min hx one_pos) h1).ne') continuousOn_id)
      (intervalIntegrable_einIntegrand hx.le zero_le_one)
  rw [hE, hfg, hsub, hEin, hlog, hγ]
  ring

/-- For `t ≠ 0`, `(1 - e^{-t})/t = ∑_k (-1)^k t^k/(k+1)!`. -/
theorem hasSum_einIntegrand {t : ℝ} (ht : t ≠ 0) :
    HasSum (fun k : ℕ => (-1) ^ k * t ^ k / (k + 1)!) ((1 - Real.exp (-t)) / t) := by
  have h := NormedSpace.expSeries_div_hasSum_exp (-t)
  rw [← Real.exp_eq_exp_ℝ, ← hasSum_nat_add_iff' 1] at h
  have h2 := h.mul_left (-1 / t)
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, Nat.factorial_zero,
    Nat.cast_one, div_one] at h2
  convert h2 using 1
  · funext k
    rw [pow_succ, neg_pow t k]
    field_simp
  · field_simp
    ring

/-- Termwise integration on `[0, x]` of a series dominated by a summable sequence. -/
theorem hasSum_intervalIntegral_of_dominated {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {b : ℕ → ℝ} (x : ℝ)
    (hF : ∀ k, Continuous (F k)) (hb : ∀ k t, |t| ≤ |x| → |F k t| ≤ b k) (hs : Summable b)
    (hlim : ∀ t, t ≠ 0 → HasSum (fun k => F k t) (f t)) :
    HasSum (fun k => ∫ t in (0 : ℝ)..x, F k t) (∫ t in (0 : ℝ)..x, f t) := by
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun k _ => b k) (fun k => (hF k).aestronglyMeasurable)
    (fun k => Eventually.of_forall fun t ht => ?_)
    (Eventually.of_forall fun t _ => hs) intervalIntegrable_const
    ((Measure.ae_ne volume 0).mono fun t ht _ => hlim t ht)
  refine (Real.norm_eq_abs _).symm ▸ hb k t ?_
  rcases ht with ⟨h1, h2⟩
  rcases le_total 0 x with hx | hx
  · simp only [hx, inf_of_le_left, sup_of_le_right] at h1 h2
    rw [abs_of_pos h1, abs_of_nonneg hx]; exact h2
  · simp only [hx, inf_of_le_right, sup_of_le_left] at h1 h2
    rw [abs_of_nonpos h2, abs_of_nonpos hx]; linarith

/-- **The power series of `Ein`** (DLMF 6.6.4):
`Ein(x) = ∑_{k≥0} (-1)^k x^{k+1} / ((k+1) (k+1)!)`. -/
@[dlmf 6.6.E4]
theorem Real.hasSum_expIntEin (x : ℝ) :
    HasSum (fun k : ℕ => (-1) ^ k * x ^ (k + 1) / ((k + 1) * (k + 1)!)) (Real.expIntEin x) := by
  have h := hasSum_intervalIntegral_of_dominated (F := fun k t =>
    (-1) ^ k * t ^ k / (k + 1)!) x (fun k => by fun_prop) (fun k t ht => ?_)
    (Real.summable_pow_div_factorial |x|) (fun t ht => hasSum_einIntegrand ht)
  · refine h.congr_fun fun k => ?_
    rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul, integral_pow]
    have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    ring
  · rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_pow,
      Nat.abs_cast]
    have hf : (k ! : ℝ) ≤ (k + 1)! := by exact_mod_cast Nat.factorial_le (Nat.le_succ k)
    calc |t| ^ k / ((k + 1)! : ℝ) ≤ |x| ^ k / (k + 1)! := by gcongr
      _ ≤ |x| ^ k / k ! := by gcongr

/-- **The series of `E₁`** (DLMF 6.6.2): for `x > 0`,
`E₁(x) = -γ - log x + ∑_{k≥0} (-1)^k x^{k+1} / ((k+1) (k+1)!)`. -/
@[dlmf 6.6.E2]
theorem genExpIntE_one_eq_tsum {x : ℝ} (hx : 0 < x) :
    genExpIntE 1 x = ((-Real.eulerMascheroniConstant - Real.log x +
      ∑' k : ℕ, (-1) ^ k * x ^ (k + 1) / ((k + 1) * (k + 1)!) : ℝ) : ℂ) := by
  rw [genExpIntE_one_eq_Ein hx, (Real.hasSum_expIntEin x).tsum_eq]
  congr 1
  ring

/-! ### Sine and cosine integrals -/

/-- `Si'(x) = sinc x`. -/
theorem Real.hasDerivAt_sinInt (x : ℝ) : HasDerivAt Real.sinInt (Real.sinc x) x :=
  intervalIntegral.integral_hasDerivAt_right (Real.continuous_sinc.intervalIntegrable _ _)
    (Real.continuous_sinc.stronglyMeasurableAtFilter _ _) Real.continuous_sinc.continuousAt

/-- `Si` is odd. -/
theorem Real.sinInt_neg (x : ℝ) : Real.sinInt (-x) = -Real.sinInt x := by
  have h := intervalIntegral.integral_comp_neg (a := 0) (b := x) Real.sinc
  simp only [Real.sinc_neg, neg_zero] at h
  rw [Real.sinInt, Real.sinInt, h, intervalIntegral.integral_symm]

/-- `Si(x) → π/2` as `x → +∞` (DLMF 6.2.14), from TauCeti's Dirichlet integral. -/
@[dlmf 6.2.E14]
theorem Real.tendsto_sinInt_atTop : Tendsto Real.sinInt atTop (𝓝 (π / 2)) :=
  TauCeti.Contour.tendsto_integral_sinc_atTop

/-- **The power series of `Si`** (DLMF 6.6.5):
`Si(x) = ∑_{k≥0} (-1)^k x^{2k+1} / ((2k+1) (2k+1)!)`. -/
@[dlmf 6.6.E5]
theorem Real.hasSum_sinInt (x : ℝ) :
    HasSum (fun k : ℕ => (-1) ^ k * x ^ (2 * k + 1) / ((2 * k + 1) * (2 * k + 1)!))
      (Real.sinInt x) := by
  have h := hasSum_intervalIntegral_of_dominated (F := fun k t =>
    (-1) ^ k * t ^ (2 * k) / (2 * k + 1)!) (f := Real.sinc) (b := fun k => (x ^ 2) ^ k / k !) x
    (fun k => by fun_prop) (fun k t ht => ?_) (Real.summable_pow_div_factorial _)
    (fun t ht => ?_)
  · refine h.congr_fun fun k => ?_
    rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul, integral_pow]
    have hk : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
    ring_nf
  · rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_pow, Nat.abs_cast,
      ← pow_mul, show x ^ (2 * k) = |x| ^ (2 * k) by rw [pow_mul, pow_mul, sq_abs]]
    have hf : (k ! : ℝ) ≤ (2 * k + 1)! := by exact_mod_cast Nat.factorial_le (by omega)
    calc |t| ^ (2 * k) / ((2 * k + 1)! : ℝ) ≤ |x| ^ (2 * k) / (2 * k + 1)! := by gcongr
      _ ≤ |x| ^ (2 * k) / k ! := by gcongr
  · have hs := (Real.hasSum_sin t).div_const t
    rw [← Real.sinc_of_ne_zero ht] at hs
    refine hs.congr_fun fun k => ?_
    rw [pow_succ]
    field_simp

/-- **The power series of `Cin`**: `Cin(x) = ∑_{k≥0} (-1)^k x^{2k+2} / ((2k+2) (2k+2)!)`. -/
theorem Real.hasSum_cosIntCin (x : ℝ) :
    HasSum (fun k : ℕ => (-1) ^ k * x ^ (2 * k + 2) / ((2 * k + 2) * (2 * k + 2)!))
      (Real.cosIntCin x) := by
  have h := hasSum_intervalIntegral_of_dominated (F := fun k t =>
    (-1) ^ k * t ^ (2 * k + 1) / (2 * k + 2)!) (f := fun t => (1 - Real.cos t) / t)
    (b := fun k => |x| * (x ^ 2) ^ k / k !) x
    (fun k => by fun_prop) (fun k t ht => ?_)
    ((Real.summable_pow_div_factorial (x ^ 2)).mul_left |x| |>.congr fun k => by ring)
    (fun t ht => ?_)
  · refine h.congr_fun fun k => ?_
    rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul, integral_pow]
    have hk : (2 * (k : ℝ) + 2) ≠ 0 := by positivity
    push_cast
    field_simp
    ring_nf
  · rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_pow, Nat.abs_cast,
      ← sq_abs x, ← pow_mul, pow_succ]
    have hf : (k ! : ℝ) ≤ (2 * k + 2)! := by exact_mod_cast Nat.factorial_le (by omega)
    calc |t| ^ (2 * k) * |t| / ((2 * k + 2)! : ℝ) ≤ |x| ^ (2 * k) * |x| / (2 * k + 2)! := by
          gcongr
      _ ≤ |x| ^ (2 * k) * |x| / k ! := by gcongr
      _ = |x| * |x| ^ (2 * k) / k ! := by ring
  · have hc := (Real.hasSum_cos t)
    rw [← hasSum_nat_add_iff' 1] at hc
    have hs := (hc.neg.div_const t)
    simp only [Finset.range_one, Finset.sum_singleton, mul_zero, pow_zero, Nat.factorial_zero,
      Nat.cast_one, div_one, mul_one] at hs
    convert hs using 1
    · funext k
      rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_succ (-1 : ℝ), pow_succ t (2 * k + 1)]
      field_simp
    · ring

/-- **The power series of `Ci`** (DLMF 6.6.6): for `x > 0`,
`Ci(x) = γ + log x + ∑_{k≥0} (-1)^{k+1} x^{2k+2} / ((2k+2) (2k+2)!)`. -/
@[dlmf 6.6.E6]
theorem Real.cosInt_eq_tsum (x : ℝ) :
    Real.cosInt x = Real.eulerMascheroniConstant + Real.log x +
      ∑' k : ℕ, (-1) ^ (k + 1) * x ^ (2 * k + 2) / ((2 * k + 2) * (2 * k + 2)!) := by
  rw [Real.cosInt, (Real.hasSum_cosIntCin x).tsum_eq.symm, ← tsum_neg]
  · have : (fun k : ℕ => (-1 : ℝ) ^ (k + 1) * x ^ (2 * k + 2) / ((2 * k + 2) * (2 * k + 2)!)) =
        fun k => -((-1) ^ k * x ^ (2 * k + 2) / ((2 * k + 2) * (2 * k + 2)!)) := by
      funext k; ring
    rw [this]
    ring

/-- `Ci'(x) = cos x / x` for `x > 0`. -/
theorem Real.hasDerivAt_cosInt {x : ℝ} (hx : 0 < x) :
    HasDerivAt Real.cosInt (Real.cos x / x) x := by
  have hcont : ContinuousOn (fun t : ℝ => (1 - Real.cos t) / t) (Set.Ioi 0) :=
    fun t ht => (by fun_prop (disch := exact (ne_of_gt ht)) :
      ContinuousAt (fun t : ℝ => (1 - Real.cos t) / t) t).continuousWithinAt
  have hCin : HasDerivAt Real.cosIntCin ((1 - Real.cos x) / x) x := by
    refine intervalIntegral.integral_hasDerivAt_right ?_ ?_
      (hcont.continuousAt (Ioi_mem_nhds hx))
    · refine (intervalIntegrable_const (c := |x|)).mono_fun'
        (by fun_prop : Measurable fun t : ℝ => (1 - Real.cos t) / t).aestronglyMeasurable ?_
      refine (ae_restrict_iff' measurableSet_uIoc).mpr (Eventually.of_forall fun t ht => ?_)
      have ht0 : 0 < t := by
        rcases ht with ⟨h1, _⟩
        exact lt_of_le_of_lt (le_min le_rfl hx.le) h1
      have htx : t ≤ x := by
        rcases ht with ⟨_, h2⟩
        exact h2.trans (max_le hx.le le_rfl)
      show ‖(1 - Real.cos t) / t‖ ≤ |x|
      have h1 := Real.one_sub_sq_div_two_le_cos (x := t)
      have h2 := Real.cos_le_one t
      rw [Real.norm_eq_abs, abs_div, abs_of_pos ht0, abs_of_nonneg (by linarith),
        div_le_iff₀ ht0, abs_of_pos hx]
      nlinarith
    · exact (hcont.stronglyMeasurableAtFilter isOpen_Ioi x hx)
  have h := (hCin.neg.add (Real.hasDerivAt_log hx.ne')).add_const Real.eulerMascheroniConstant
  refine h.congr_deriv ?_
  field_simp
  ring

end DLMF.Confluent
