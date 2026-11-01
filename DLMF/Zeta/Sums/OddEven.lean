/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Gamma.SeriesExpansions
public import DLMFMathlib.NumberTheory.BernoulliTaylor
public import Mathlib.Analysis.SpecialFunctions.Integrals.Log
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd
public import DLMF.Zeta.CotangentMoments
public import DLMF.Zeta.Riemann
public import DLMF.Zeta.Sums.PowerSeries

/-!
# Zeta sums with odd and even denominators (DLMF 25.8.9–25.8.10)

Integrating the cotangent series 25.8.6 over `[0, 1/2]` once or twice gives sums of
`ζ(2k)` against `1/(2k+1)` and `1/((2k+1)(2k+2))`. The resulting cotangent integrals are
evaluated with `∫ ln sin` and the cotangent moment of `DLMF.Zeta.CotangentMoments`.

## Main results

* `hasSum_riemannZeta_two_mul_div_odd`: `∑_{k≥1} ζ(2k)/((2k+1) 2^{2k}) = ½ - ½ ln 2` (25.8.9).
* `hasSum_riemannZeta_two_mul_div_odd_even`:
  `∑_{k≥1} ζ(2k)/((2k+1)(2k+2) 2^{2k}) = ¼ - (7/(4π²)) ζ(3)` (25.8.10).
-/

@[expose] public noncomputable section

open Complex Filter Topology Finset
open scoped Real Nat

namespace DLMF.Zeta

/-- `0 ≤ πx cot(πx) ≤ 1` for `0 ≤ x ≤ 1/2`. -/
private lemma abs_pi_mul_mul_cot_le_one {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    |π * x * Real.cot (π * x)| ≤ 1 := by
  rcases eq_or_lt_of_le hx0 with rfl | hx
  · simp
  have hy : 0 < π * x := by positivity
  have hy2 : π * x ≤ π / 2 := by nlinarith [Real.pi_pos]
  have hs : 0 < Real.sin (π * x) := Real.sin_pos_of_pos_of_lt_pi hy (by linarith [Real.pi_pos])
  have hc : 0 ≤ Real.cos (π * x) := Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) hy2
  rw [Real.cot_eq_cos_div_sin, abs_le]
  constructor
  · have : 0 ≤ π * x * (Real.cos (π * x) / Real.sin (π * x)) := by positivity
    linarith
  · rw [mul_div_assoc', div_le_one hs]
    rcases eq_or_lt_of_le hy2 with h | h
    · rw [h, Real.cos_pi_div_two, mul_zero, Real.sin_pi_div_two]; norm_num
    · have ht := Real.le_tan hy.le h
      rw [Real.tan_eq_sin_div_cos, le_div_iff₀ (by
        exact Real.cos_pos_of_mem_Ioo ⟨by linarith, h⟩)] at ht
      linarith

/-- `x ln sin(πx) → 0` as `x → 0` within `[0, 1/2]`. -/
private lemma continuousWithinAt_mul_log_sin :
    ContinuousWithinAt (fun x : ℝ => x * Real.log (Real.sin (π * x))) (Set.Icc 0 (1 / 2)) 0 := by
  have hb : ∀ x ∈ Set.Icc (0 : ℝ) (1 / 2), ‖x * Real.log (Real.sin (π * x))‖ ≤
      ‖x * Real.log (2 * x)‖ := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with h | hx0
    · subst h; simp
    have h2 : 2 * x ≤ Real.sin (π * x) := by
      have := Real.mul_le_sin (x := π * x) (by positivity) (by nlinarith [Real.pi_pos, hx.2])
      rwa [show 2 / π * (π * x) = 2 * x by field_simp] at this
    have h1 : Real.sin (π * x) ≤ 1 := Real.sin_le_one _
    have hl1 : Real.log (Real.sin (π * x)) ≤ 0 := Real.log_nonpos (by linarith) h1
    have hl2 : Real.log (2 * x) ≤ Real.log (Real.sin (π * x)) := Real.log_le_log (by positivity) h2
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hx0]
    refine mul_le_mul_of_nonneg_left ?_ hx0.le
    rw [abs_of_nonpos hl1, abs_of_nonpos (hl2.trans hl1)]
    linarith
  have hc : Tendsto (fun x : ℝ => x * Real.log (2 * x)) (𝓝[Set.Icc 0 (1 / 2)] 0) (𝓝 0) := by
    have h := (Real.continuous_mul_log.comp (continuous_const.mul continuous_id :
      Continuous fun x : ℝ => 2 * x)).tendsto 0
    have : (fun x : ℝ => x * Real.log (2 * x)) =
        fun x => (1 / 2) * ((2 * x) * Real.log (2 * x)) := by
      funext x; ring
    rw [this]
    simpa using (h.const_mul (1 / 2 : ℝ)).mono_left nhdsWithin_le_nhds
  show Tendsto _ _ _
  simp only [zero_mul]
  exact squeeze_zero_norm' (eventually_nhdsWithin_of_forall hb) (by simpa using hc.norm)

/-- `∫₀^{1/2} πx cot(πx) dx = ½ ln 2`. -/
private lemma integral_pi_mul_mul_cot :
    ∫ x in (0 : ℝ)..(1 / 2), π * x * Real.cot (π * x) = Real.log 2 / 2 := by
  set G : ℝ → ℝ := fun x => x * Real.log (Real.sin (π * x)) with hG
  have hlog : IntervalIntegrable (fun x : ℝ => Real.log (Real.sin (π * x))) MeasureTheory.volume
      0 (1 / 2) := by
    have := (intervalIntegrable_log_sin (a := 0) (b := π / 2)).comp_mul_left (c := π)
    simpa [Function.comp_def, show π / 2 / π = 1 / 2 by field_simp] using this
  have hcot : IntervalIntegrable (fun x : ℝ => π * x * Real.cot (π * x)) MeasureTheory.volume
      0 (1 / 2) := by
    refine (intervalIntegrable_const (c := (1 : ℝ))).mono_fun' ?_ ?_
    · simp only [Real.cot_eq_cos_div_sin]
      exact (by fun_prop : Measurable fun x : ℝ =>
        π * x * (Real.cos (π * x) / Real.sin (π * x))).aestronglyMeasurable
    · rw [Filter.EventuallyLE, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
      refine MeasureTheory.ae_of_all _ fun x hx => ?_
      rw [Set.uIoc_of_le (by norm_num)] at hx
      exact abs_pi_mul_mul_cot_le_one hx.1.le hx.2
  have hFTC : ∫ x in (0 : ℝ)..(1 / 2), (Real.log (Real.sin (π * x)) +
      π * x * Real.cot (π * x)) = G (1 / 2) - G 0 := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num) ?_ ?_ (hlog.add hcot)
    · intro x hx
      rcases eq_or_lt_of_le hx.1 with h | hx0
      · subst h; exact continuousWithinAt_mul_log_sin
      · refine ContinuousAt.continuousWithinAt ?_
        have hs : Real.sin (π * x) ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi (by positivity)
          (by nlinarith [Real.pi_pos, hx.2])).ne'
        exact continuousAt_id.mul ((Real.continuousAt_log hs).comp
          (f := fun x : ℝ => Real.sin (π * x)) (by fun_prop))
    · intro x hx
      have hs : Real.sin (π * x) ≠ 0 :=
        (Real.sin_pos_of_pos_of_lt_pi (by nlinarith [Real.pi_pos, hx.1])
          (by nlinarith [Real.pi_pos, hx.2])).ne'
      have h := (hasDerivAt_id x).mul ((((hasDerivAt_id x).const_mul π).sin).log hs)
      convert h using 1
      · funext y; simp [hG]
      · simp only [id, Real.cot_eq_cos_div_sin]
        field_simp
  have hG0 : G (1 / 2) - G 0 = 0 := by
    simp only [hG]
    rw [show π * (1 / 2) = π / 2 by ring, Real.sin_pi_div_two]
    simp
  rw [hG0, intervalIntegral.integral_add hlog hcot] at hFTC
  have hL : ∫ x in (0 : ℝ)..(1 / 2), Real.log (Real.sin (π * x)) = -Real.log 2 / 2 := by
    rw [intervalIntegral.integral_comp_mul_left (fun x => Real.log (Real.sin x)) Real.pi_ne_zero,
      mul_zero, show π * (1 / 2) = π / 2 by ring, integral_log_sin_zero_pi_div_two, smul_eq_mul]
    field_simp
  linarith

open scoped Interval in
/-- DLMF 25.8.9: `∑_{k≥1} ζ(2k)/((2k+1) 2^{2k}) = ½ - ½ ln 2`. -/
@[dlmf 25.8.E9]
theorem hasSum_riemannZeta_two_mul_div_odd :
    HasSum (fun k : ℕ => riemannZeta (2 * (k + 1)) / ((2 * (k + 1) + 1) * 2 ^ (2 * (k + 1))))
      (1 / 2 - 1 / 2 * Real.log 2) := by
  set F : ℕ → ℝ → ℂ := fun k x => riemannZeta (2 * (k + 1)) * (x : ℂ) ^ (2 * (k + 1)) with hF
  set f : ℝ → ℂ := fun x => (((1 - π * x * Real.cot (π * x)) / 2 : ℝ) : ℂ) with hf
  have hlim : ∀ x : ℝ, 0 < x → x ≤ 1 / 2 → HasSum (fun k => F k x) (f x) := by
    intro x hx0 hx1
    have hz : ‖(x : ℂ)‖ < 1 := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]; linarith
    have hz0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
    have h := (hasSum_nat_add_iff' 1).mpr (hasSum_riemannZeta_two_mul_mul_pow hz hz0)
    simp only [range_one, sum_singleton, Nat.cast_zero, mul_zero, pow_zero, mul_one,
      riemannZeta_zero] at h
    convert h using 1
    · funext k; simp only [hF]; push_cast; ring_nf
    · simp only [hf]
      rw [show (π : ℂ) * x = ((π * x : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cot]
      push_cast; ring
  have hzb : ∀ k : ℕ, ‖riemannZeta (2 * (k + 1))‖ ≤ 2 := by
    intro k
    have h := DLMF.Gamma.norm_riemannZeta_add_two_sub_one_le (2 * k)
    have e : ((2 * k : ℕ) : ℂ) + 2 = 2 * ((k : ℂ) + 1) := by push_cast; ring
    rw [e] at h
    have h1 : (1 / 2 : ℝ) ^ (2 * k) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have := norm_sub_norm_le (riemannZeta (2 * ((k : ℂ) + 1))) 1
    simp at this
    linarith
  set bound : ℕ → ℝ → ℝ := fun k _ => 2 * (1 / 4 : ℝ) ^ (k + 1) with hbound
  have hFb : ∀ k : ℕ, ∀ x ∈ Ι (0 : ℝ) (1 / 2), ‖F k x‖ ≤ bound k x := by
    intro k x hx
    rw [Set.uIoc_of_le (by norm_num)] at hx
    simp only [hF, hbound, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hx.1]
    have : x ^ (2 * (k + 1)) ≤ (1 / 4 : ℝ) ^ (k + 1) := by
      rw [pow_mul, show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num]
      exact pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ hx.1.le hx.2 2) _
    exact mul_le_mul (hzb k) this (pow_nonneg hx.1.le _) (by norm_num)
  have hbs : Summable (fun k : ℕ => 2 * (1 / 4 : ℝ) ^ (k + 1)) :=
    ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).comp_injective
      (add_left_injective 1)).mul_left 2
  have hI := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := MeasureTheory.volume)
    (a := 0) (b := 1 / 2) bound
    (fun k => (by fun_prop : Continuous (F k)).aestronglyMeasurable)
    (fun k => MeasureTheory.ae_of_all _ (hFb k))
    (MeasureTheory.ae_of_all _ fun _ _ => hbs)
    (by simp only [hbound]; exact intervalIntegrable_const)
    (MeasureTheory.ae_of_all _ fun x hx => by
      rw [Set.uIoc_of_le (by norm_num)] at hx; exact hlim x hx.1 hx.2)
  have hFk : ∀ k : ℕ, ∫ x in (0 : ℝ)..(1 / 2), F k x =
      riemannZeta (2 * (k + 1)) *
        (((1 / 2 : ℝ) ^ (2 * (k + 1) + 1) / (2 * (k + 1) + 1) : ℝ) : ℂ) := by
    intro k
    simp only [hF]
    rw [intervalIntegral.integral_const_mul]
    congr 1
    have : (fun x : ℝ => (x : ℂ) ^ (2 * (k + 1))) = fun x : ℝ => ((x ^ (2 * (k + 1)) : ℝ) : ℂ) := by
      funext x; push_cast; rfl
    rw [this, intervalIntegral.integral_ofReal, integral_pow]
    push_cast; ring
  have hfI : ∫ x in (0 : ℝ)..(1 / 2), f x = ((1 / 4 - Real.log 2 / 4 : ℝ) : ℂ) := by
    simp only [hf]
    rw [intervalIntegral.integral_ofReal]
    congr 1
    have hc : IntervalIntegrable (fun x : ℝ => π * x * Real.cot (π * x)) MeasureTheory.volume
        0 (1 / 2) := by
      by_contra hn
      have := intervalIntegral.integral_undef hn
      rw [integral_pi_mul_mul_cot] at this
      have : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      linarith
    rw [intervalIntegral.integral_div, intervalIntegral.integral_sub intervalIntegrable_const hc,
      integral_pi_mul_mul_cot]
    simp; ring
  simp only [hFk, hfI] at hI
  have h2 := hI.mul_left 2
  convert h2 using 1
  · funext k
    push_cast
    have h4 : ((1 : ℂ) / 2) ^ (2 * (k + 1) + 1) * 2 ^ (2 * (k + 1)) = 1 / 2 := by
      rw [pow_succ, mul_comm, ← mul_assoc, ← mul_pow]; norm_num
    have h5 : (2 * ((k : ℂ) + 1) + 1) ≠ 0 := by
      rw [show (2 * ((k : ℂ) + 1) + 1) = ((2 * k + 3 : ℕ) : ℂ) by push_cast; ring]
      exact_mod_cast (by omega : 2 * k + 3 ≠ 0)
    have h6 : (2 : ℂ) ^ (2 * (k + 1)) ≠ 0 := pow_ne_zero _ two_ne_zero
    field_simp
    linear_combination (-(2 : ℂ) * riemannZeta (2 * ((k : ℂ) + 1))) * h4
  · push_cast; ring

/-- DLMF 25.8.10: `∑_{k≥1} ζ(2k)/((2k+1)(2k+2) 2^{2k}) = ¼ - (7/(4π²)) ζ(3)`. -/
@[dlmf 25.8.E10]
theorem hasSum_riemannZeta_two_mul_div_odd_even :
    HasSum (fun k : ℕ => riemannZeta (2 * (k + 1)) /
        ((2 * (k + 1) + 1) * (2 * (k + 1) + 2) * 2 ^ (2 * (k + 1))))
      (1 / 4 - 7 / (4 * π ^ 2) * riemannZeta 3) := by
  set F : ℕ → ℝ → ℂ := fun k x => riemannZeta (2 * (k + 1)) *
    (((1 / 2 - x) * x ^ (2 * (k + 1)) : ℝ) : ℂ)
  set f : ℝ → ℂ := fun x => (((1 / 2 - x) / 2 -
    π / 2 * ((x / 2 - x ^ 2) * Real.cot (π * x)) : ℝ) : ℂ)
  have hlim : ∀ x : ℝ, 0 < x → x ≤ 1 / 2 → HasSum (fun k => F k x) (f x) := by
    intro x hx0 hx1
    have hz : ‖(x : ℂ)‖ < 1 := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]; linarith
    have hz0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
    have h := (hasSum_nat_add_iff' 1).mpr (hasSum_riemannZeta_two_mul_mul_pow hz hz0)
    simp only [range_one, sum_singleton, Nat.cast_zero, mul_zero, pow_zero, mul_one,
      riemannZeta_zero] at h
    have h' := h.mul_right (((1 / 2 - x : ℝ) : ℂ))
    convert h' using 1
    · funext k; simp only [F]; push_cast; ring
    · simp only [f]
      rw [show (π : ℂ) * x = ((π * x : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cot]
      push_cast; ring
  have hzb : ∀ k : ℕ, ‖riemannZeta (2 * (k + 1))‖ ≤ 2 := by
    intro k
    have h := DLMF.Gamma.norm_riemannZeta_add_two_sub_one_le (2 * k)
    have e : ((2 * k : ℕ) : ℂ) + 2 = 2 * ((k : ℂ) + 1) := by push_cast; ring
    rw [e] at h
    have h1 : (1 / 2 : ℝ) ^ (2 * k) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have := norm_sub_norm_le (riemannZeta (2 * ((k : ℂ) + 1))) 1
    simp at this
    linarith
  have hFb : ∀ k : ℕ, ∀ x ∈ Set.uIoc (0 : ℝ) (1 / 2),
      ‖F k x‖ ≤ 2 * (1 / 4 : ℝ) ^ (k + 1) := by
    intro k x hx
    rw [Set.uIoc_of_le (by norm_num)] at hx
    have hx0 := hx.1
    have hx1 := hx.2
    simp only [F, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (by linarith : 0 ≤ 1 / 2 - x), abs_of_pos hx.1]
    have hpow : x ^ (2 * (k + 1)) ≤ (1 / 4 : ℝ) ^ (k + 1) := by
      rw [pow_mul, show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num]
      exact pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ hx.1.le hx.2 2) _
    have hprod : (1 / 2 - x) * x ^ (2 * (k + 1)) ≤ (1 / 4 : ℝ) ^ (k + 1) := by
      exact (mul_le_mul_of_nonneg_right (by linarith : 1 / 2 - x ≤ 1) (by positivity)).trans
        (by simpa using hpow)
    exact mul_le_mul (hzb k) hprod (by positivity) (by norm_num)
  have hbs : Summable (fun k : ℕ => 2 * (1 / 4 : ℝ) ^ (k + 1)) :=
    ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).comp_injective
      (add_left_injective 1)).mul_left 2
  have hI := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := MeasureTheory.volume)
    (a := 0) (b := 1 / 2) (fun k _ => 2 * (1 / 4 : ℝ) ^ (k + 1))
    (fun k => (by fun_prop : Continuous (F k)).aestronglyMeasurable)
    (fun k => MeasureTheory.ae_of_all _ (hFb k))
    (MeasureTheory.ae_of_all _ fun _ _ => hbs) intervalIntegrable_const
    (MeasureTheory.ae_of_all _ fun x hx => by
      rw [Set.uIoc_of_le (by norm_num)] at hx; exact hlim x hx.1 hx.2)
  have hFk : ∀ k : ℕ, ∫ x in (0 : ℝ)..(1 / 2), F k x =
      riemannZeta (2 * (k + 1)) /
        (4 * ((2 * (k + 1) + 1) * (2 * (k + 1) + 2) * 2 ^ (2 * (k + 1)))) := by
    intro k
    simp only [F]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal]
    have he : (fun x : ℝ => (1 / 2 - x) * x ^ (2 * (k + 1))) =
        fun x => (1 / 2) * x ^ (2 * (k + 1)) - x ^ (2 * (k + 1) + 1) := by funext x; ring
    rw [he, intervalIntegral.integral_sub
      ((by fun_prop : Continuous fun x : ℝ => (1 / 2) * x ^ (2 * (k + 1))).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun x : ℝ => x ^ (2 * (k + 1) + 1)).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, integral_pow, integral_pow]
    push_cast
    have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
    have h3 : (2 * ((k : ℂ) + 1) + 1) ≠ 0 := by exact_mod_cast (show 2 * (k + 1) + 1 ≠ 0 by omega)
    have h4 : (2 * ((k : ℂ) + 1) + 1 + 1) ≠ 0 := by exact_mod_cast (show 2 * (k + 1) + 1 + 1 ≠ 0 by omega)
    simp only [zero_pow (by omega : 2 * (k + 1) + 1 ≠ 0), sub_zero,
      zero_pow (by omega : 2 * (k + 1) + 1 + 1 ≠ 0)]
    simp only [div_pow, one_pow, pow_succ]
    have hk2 : (k : ℂ) + 2 ≠ 0 := by exact_mod_cast (show k + 2 ≠ 0 by omega)
    field_simp [hk2]
    ring_nf
    field_simp [show (2 : ℂ) + k ≠ 0 by simpa [add_comm] using hk2]
    ring
  have hcot := integral_quadratic_mul_cot_pi (fun x hx => abs_pi_mul_mul_cot_le_one hx.1 hx.2)
  have hfI : ∫ x in (0 : ℝ)..(1 / 2), f x =
      1 / 16 - 7 / (16 * π ^ 2) * riemannZeta 3 := by
    simp only [f]
    rw [intervalIntegral.integral_ofReal,
      intervalIntegral.integral_sub
        ((by fun_prop : Continuous fun x : ℝ => (1 / 2 - x) / 2).intervalIntegrable _ _)
        (hcot.1.const_mul (π / 2)),
      intervalIntegral.integral_const_mul]
    push_cast
    rw [← intervalIntegral.integral_ofReal
      (f := fun x : ℝ => (x / 2 - x ^ 2) * Real.cot (π * x)), hcot.2]
    have he : (∫ x in (0 : ℝ)..(1 / 2), (1 / 2 - x) / 2) = 1 / 16 := by
      rw [intervalIntegral.integral_div, intervalIntegral.integral_sub
        (f := fun _ : ℝ => 1 / 2) (g := fun x : ℝ => x) intervalIntegrable_const
        (continuous_id.intervalIntegrable _ _), integral_id]
      norm_num
    rw [he]
    push_cast
    have hp : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp
    ring
  simp only [hFk, hfI] at hI
  have h4 := hI.mul_left 4
  convert h4 using 1
  · funext k; field_simp
  · ring

end DLMF.Zeta
