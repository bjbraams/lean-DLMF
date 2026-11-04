/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AlgebraicAnalytic.Transforms.LaplaceTable
public import DLMF.AlgebraicAnalytic.Transforms.StieltjesPower
public import DLMF.Gamma.MellinBarnes
public import DLMFMathlib.Analysis.MellinConvolution
public import DLMFMathlib.Analysis.SpecialFunctions.Pow.ComplexReal
public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import TauCeti.MeasureTheory.Integral.Bochner.Basic

/-!
# Table of Mellin transforms (DLMF §1.14(vii), Table 1.14.5)

Each row of DLMF Table 1.14.5 (Mellin transforms `∫₀^∞ x^{s-1} f(x) dx`, 1.14.32, Mathlib's
`mellin`) is a theorem here, tagged with the table ID. Parameters are complex where DLMF writes
`|ph a| < π`; principal branches throughout.

## Main results

* `mellin_indicator_lt`, `mellin_inv_one_add`, `mellin_log_one_add_mul`, `mellin_arctan`,
  `mellin_poisson_cos`, `mellin_poisson_sin` and the other `mellin_*` rows: Table 1.14.5.

## Implementation notes

Row 1.14.5.4 is a Cauchy principal value at `x = 1`, as DLMF says. Rows 1.14.5.11–12 and 1.14.5.6
reduce to the Stieltjes transform of a power on the cut plane
(`DLMF.AlgebraicAnalytic.Transforms.StieltjesPower`).

**Precisions.**
* 1.14.5.3: DLMF gives `ℜs > 1`; the integral converges and the formula holds for `ℜs > 0`
  (stated so, stronger than DLMF). 1.14.5.7 needs `s ≠ 0` in Lean (`π tan(0)/0` is junk `0`, the
  limit value is `π²/2`).
-/

@[expose] public noncomputable section

open MeasureTheory Complex Set Filter Topology
open scoped Nat

namespace DLMF.AlgebraicAnalytic

/-! ### Table 1.14.5: Mellin transforms `∫₀^∞ x^{s-1} f(x) dx` (Mathlib's `mellin`) -/

/-- DLMF Table 1.14.5, row 2: `f = 1` for `x < a`, `0` for `x ≥ a`: `a^s/s`, `a ≥ 0`, `ℜs > 0`. -/
@[dlmf 1.14.T5]
theorem mellin_indicator_lt {a : ℝ} (ha : 0 ≤ a) {s : ℂ} (hs : 0 < s.re) :
    mellin (fun x => (Iio a).indicator (fun _ => (1 : ℂ)) x) s = (a : ℂ) ^ s / s := by
  have hs0 : s ≠ 0 := fun h => by simp [h] at hs
  unfold mellin
  have he : (fun x : ℝ => (x : ℂ) ^ (s - 1) •
      (Iio a).indicator (fun _ => (1 : ℂ)) x) =
      (Iio a).indicator (fun x => (x : ℂ) ^ (s - 1)) := by
    ext x
    by_cases hx : x ∈ Iio a <;> simp [hx]
  rw [he, setIntegral_indicator measurableSet_Iio, Ioi_inter_Iio,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ha,
    integral_cpow (Or.inl (by simp; linarith)), sub_add_cancel,
    ofReal_zero, Complex.zero_cpow hs0, sub_zero]

/-- DLMF Table 1.14.5, row 3: `ln(a/x)` for `x < a`, `0` for `x ≥ a`: `a^s/s²`, `a ≥ 0`;
valid for `ℜs > 0` (DLMF: `ℜs > 1`). -/
@[dlmf 1.14.T5]
theorem mellin_log_indicator_lt {a : ℝ} (ha : 0 ≤ a) {s : ℂ} (hs : 0 < s.re) :
    mellin (fun x => (Iio a).indicator (fun x => (Real.log (a / x) : ℂ)) x) s =
      (a : ℂ) ^ s / s ^ 2 := by
  have hs0 : s ≠ 0 := fun h => by simp [h] at hs
  rcases ha.eq_or_lt with rfl | ha
  · simp [mellin, Complex.zero_cpow hs0]
  let g : ℝ → ℂ := (Ioi 0).indicator (fun u => cexp (-s * u) * u)
  have he : (fun u : ℝ => cexp (-s * u) *
      (Iio a).indicator (fun x => (Real.log (a / x) : ℂ)) (Real.exp (-u))) =
      fun u => (a : ℂ) ^ s * g (u + Real.log a) := by
    funext u
    have hi : Real.exp (-u) < a ↔ 0 < u + Real.log a := by
      rw [← Real.log_lt_log_iff (Real.exp_pos _) ha, Real.log_exp]
      constructor <;> intro h <;> linarith
    by_cases hu : 0 < u + Real.log a
    · rw [indicator_of_mem (hi.mpr hu)]
      dsimp only [g]
      rw [indicator_of_mem hu, Real.log_div ha.ne' (Real.exp_pos _).ne', Real.log_exp]
      have hExp : (a : ℂ) ^ s * cexp (-s * ((u + Real.log a : ℝ) : ℂ)) = cexp (-s * u) := by
        rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr ha.ne'), ← ofReal_log ha.le, ← Complex.exp_add]
        congr 1
        push_cast
        ring
      rw [← mul_assoc, hExp]
      congr 1
      push_cast
      ring
    · rw [indicator_of_notMem (show Real.exp (-u) ∉ Iio a from fun h => hu (hi.mp h))]
      simp only [g, indicator_of_notMem (show u + Real.log a ∉ Ioi 0 from hu), mul_zero]
  rw [mellin_eq_integral_exp_mul, he, integral_const_mul, integral_add_right_eq_self,
    integral_indicator measurableSet_Ioi]
  have h := laplaceTransform_pow_div_factorial 1 hs
  simp only [laplaceTransform, pow_one, Nat.factorial_one, Nat.cast_one, div_one] at h
  rw [show (1 : ℕ) + 1 = 2 from rfl] at h
  rw [h]
  ring

/-- DLMF Table 1.14.5, row 4: `1/(1 - x) ↦ π cot(sπ)`, `0 < ℜs < 1`, Cauchy principal value at
`x = 1`. -/
@[dlmf 1.14.T5]
theorem tendsto_mellin_inv_one_sub_pv {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    Tendsto (fun ε : ℝ => ∫ x in {x : ℝ | 0 < x ∧ ε < |x - 1|},
        (x : ℂ) ^ (s - 1) * (1 / (1 - x))) (𝓝[>] 0)
      (𝓝 (Real.pi * Complex.cot (s * Real.pi))) := by
  sorry

/-- DLMF Table 1.14.5, row 5: `1/(1 + x) ↦ π csc(sπ)`, `0 < ℜs < 1`. -/
@[dlmf 1.14.T5]
theorem mellin_inv_one_add {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    mellin (fun x => 1 / (1 + (x : ℂ))) s = Real.pi / Complex.sin (s * Real.pi) := by
  have h := DLMF.Gamma.mellin_one_add_cpow_neg (a := 1) hs0 (by simpa using hs1)
  simpa [Complex.cpow_neg, Complex.Gamma_one, Complex.Gamma_mul_Gamma_one_sub,
    mul_comm] using h

/-- The cut plane is closed under inversion. -/
private lemma inv_mem_slitPlane_of_mem {a : ℂ} (ha : a ∈ slitPlane) : a⁻¹ ∈ slitPlane := by
  have ha0 : a ≠ 0 := slitPlane_ne_zero ha
  have hn : 0 < normSq a := normSq_pos.mpr ha0
  rw [mem_slitPlane_iff] at ha ⊢
  rw [inv_re, inv_im]
  rcases ha with h | h
  · exact Or.inl (div_pos h hn)
  · exact Or.inr (div_ne_zero (neg_ne_zero.mpr h) hn.ne')

/-- `1 + at` lies in the cut plane for `a` in the cut plane and `t ≥ 0`. -/
private lemma one_add_mul_ofReal_mem_slitPlane {a : ℂ} (ha : a ∈ slitPlane) {t : ℝ}
    (ht : 0 ≤ t) : 1 + a * t ∈ slitPlane := by
  rw [mem_slitPlane_iff] at ha ⊢
  simp only [add_re, one_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero, add_im, one_im,
    mul_im, zero_add]
  rcases ha with h | h
  · exact Or.inl (by nlinarith)
  · rcases ht.eq_or_lt with h0 | h0
    · left; rw [← h0]; simp
    · exact Or.inr (mul_ne_zero h h0.ne')

/-- The log bound `‖log(1 + at)‖ ≤ K log(1 + t)` on `t ≥ 0` for `a` in the cut plane. -/
private lemma exists_norm_log_one_add_mul_le {a : ℂ} (ha : a ∈ slitPlane) :
    ∃ K > 0, ∀ t : ℝ, 0 ≤ t → ‖Complex.log (1 + a * t)‖ ≤ K * Real.log (1 + t) := by
  have ha0 : a ≠ 0 := slitPlane_ne_zero ha
  obtain ⟨c, hc, hb⟩ := TauCeti.exists_pos_forall_mem_ball_mul_one_add_le_norm_add
    (inv_mem_slitPlane_of_mem ha)
  have hlow : ∀ t : ℝ, 0 ≤ t → ‖a‖ * (c * (1 + t)) ≤ ‖1 + a * t‖ := by
    intro t ht
    have h := hb a⁻¹ (Metric.mem_ball_self hc) ⟨t, ht⟩
    change c * (1 + t) ≤ ‖a⁻¹ + (t : ℂ)‖ at h
    rw [show (1 : ℂ) + a * t = a * (a⁻¹ + t) by field_simp, norm_mul]
    exact mul_le_mul_of_nonneg_left h (norm_nonneg a)
  refine ⟨c⁻¹, inv_pos.mpr hc, fun T hT => ?_⟩
  have hderiv : ∀ t ∈ Ici (0 : ℝ), HasDerivAt (fun u : ℝ => Complex.log (1 + a * u))
      (a / (1 + a * t)) t := by
    intro t ht
    have h1 : HasDerivAt (fun u : ℝ => 1 + a * (u : ℂ)) a t := by
      simpa using ((hasDerivAt_id (t : ℂ)).const_mul a).const_add 1 |>.comp_ofReal
    exact h1.clog_real (one_add_mul_ofReal_mem_slitPlane ha ht)
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary'
    (f := fun u : ℝ => Complex.log (1 + a * u)) (a := 0) (b := T)
    (f' := fun t => a / (1 + a * t)) (B := fun t => c⁻¹ * Real.log (1 + t))
    (B' := fun t => c⁻¹ * (1 + t)⁻¹)
    (fun t ht => (hderiv t ht.1).continuousAt.continuousWithinAt)
    (fun t ht => (hderiv t ht.1).hasDerivWithinAt)
    (by simp)
    (fun t ht => by
      have : 0 < 1 + t := by linarith [ht.1]
      exact (((continuousAt_const.add continuousAt_id).log this.ne').const_mul _)
        |>.continuousWithinAt)
    (fun t ht => by
      have : 0 < 1 + t := by linarith [ht.1]
      have h := ((hasDerivAt_id t).const_add 1).log this.ne'
      simpa using (h.const_mul c⁻¹).hasDerivWithinAt)
    (fun t ht => by
      have ht0 : 0 ≤ t := ht.1
      have hpos : 0 < ‖a‖ * (c * (1 + t)) := by
        have := norm_pos_iff.mpr ha0; positivity
      rw [norm_div]
      calc ‖a‖ / ‖1 + a * t‖ ≤ ‖a‖ / (‖a‖ * (c * (1 + t))) :=
            div_le_div_of_nonneg_left (norm_nonneg _) hpos (hlow t ht0)
        _ = c⁻¹ * (1 + t)⁻¹ := by
            have := norm_pos_iff.mpr ha0
            field_simp)
  exact key ⟨hT, le_rfl⟩

/-- DLMF Table 1.14.5, row 6: `ln(1 + ax) ↦ π csc(sπ)/(s a^s)`, `|ph a| < π`, `-1 < ℜs < 0`. -/
@[dlmf 1.14.T5]
theorem mellin_log_one_add_mul {a : ℂ} (ha : a ∈ slitPlane) {s : ℂ} (hs0 : -1 < s.re)
    (hs1 : s.re < 0) :
    mellin (fun x => Complex.log (1 + a * x)) s =
      Real.pi / Complex.sin (s * Real.pi) / (s * a ^ s) := by
  have ha0 : a ≠ 0 := slitPlane_ne_zero ha
  have hs : s ≠ 0 := fun h => by simp [h] at hs1
  obtain ⟨K, hK, hlog⟩ := exists_norm_log_one_add_mul_le ha
  set ε := -s.re / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hε1 : ε ≤ 1 := by rw [hε]; linarith
  have hlog0 : ∀ t : ℝ, 0 ≤ t → 0 ≤ Real.log (1 + t) := fun t ht =>
    Real.log_nonneg (by linarith)
  have hlog1 : ∀ t : ℝ, 0 ≤ t → Real.log (1 + t) ≤ t := fun t ht => by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + t by linarith); linarith
  have hlog2 : ∀ t : ℝ, 1 ≤ t → Real.log (1 + t) ≤ 2 / ε * t ^ ε := fun t ht => by
    have h1 := Real.log_le_rpow_div (show (0 : ℝ) ≤ 1 + t by linarith) hε0
    have h2 : (1 + t) ^ ε ≤ (2 * t) ^ ε :=
      Real.rpow_le_rpow (by linarith) (by linarith) hε0.le
    have h3 : (2 * t) ^ ε ≤ 2 * t ^ ε := by
      rw [Real.mul_rpow (by norm_num) (by linarith)]
      gcongr
      calc (2 : ℝ) ^ ε ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hε1
        _ = 2 := Real.rpow_one 2
    calc Real.log (1 + t) ≤ (1 + t) ^ ε / ε := h1
      _ ≤ 2 * t ^ ε / ε := by gcongr; exact h2.trans h3
      _ = 2 / ε * t ^ ε := by ring
  have hcont : ∀ t : ℝ, 0 ≤ t → ContinuousAt (fun u : ℝ => Complex.log (1 + a * u)) t :=
    fun t ht => ContinuousAt.clog (f := fun u : ℝ => 1 + a * (u : ℂ)) (by fun_prop)
      (one_add_mul_ofReal_mem_slitPlane ha ht)
  have hconv : MellinConvergent (fun x : ℝ => Complex.log (1 + a * x)) s := by
    refine mellinConvergent_of_isBigO_rpow (a := -ε) (b := -1) ?_ ?_ (by rw [hε]; linarith)
      ?_ hs0
    · exact ContinuousOn.locallyIntegrableOn
        (fun t ht => (hcont t (le_of_lt ht)).continuousWithinAt) measurableSet_Ioi
    · refine Asymptotics.IsBigO.of_bound (K * (2 / ε)) ?_
      filter_upwards [eventually_ge_atTop 1] with t ht
      have ht0 : (0 : ℝ) < t := by linarith
      rw [neg_neg, Real.norm_of_nonneg (Real.rpow_nonneg ht0.le _)]
      calc ‖Complex.log (1 + a * t)‖ ≤ K * Real.log (1 + t) := hlog t ht0.le
        _ ≤ K * (2 / ε * t ^ ε) := by gcongr; exact hlog2 t ht
        _ = K * (2 / ε) * t ^ ε := by ring
    · refine Asymptotics.IsBigO.of_bound K ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : (0 : ℝ) < t := ht
      rw [neg_neg, Real.rpow_one, Real.norm_of_nonneg ht0.le]
      calc ‖Complex.log (1 + a * t)‖ ≤ K * Real.log (1 + t) := hlog t ht0.le
        _ ≤ K * t := by gcongr; exact hlog1 t ht0.le
  have hz := inv_mem_slitPlane_of_mem ha
  have hs10 : 0 < (s + 1).re := by simp; linarith
  have hs11 : (s + 1).re < 1 := by simp; linarith
  have huv_bound : ∀ t : ℝ, 0 < t →
      ‖Complex.log (1 + a * t) * ((t : ℂ) ^ s / s)‖ ≤ K * Real.log (1 + t) * t ^ s.re / ‖s‖ := by
    intro t ht
    rw [norm_mul, norm_div, norm_cpow_eq_rpow_re_of_pos ht, mul_div_assoc]
    gcongr
    exact hlog t ht.le
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul (a := 0) (a' := 0) (b' := 0)
    (u := fun t : ℝ => Complex.log (1 + a * t)) (u' := fun t : ℝ => a / (1 + a * t))
    (v := fun t => (t : ℂ) ^ s / s) (v' := fun t => (t : ℂ) ^ (s - 1))
    (fun t ht => by
      have h1 : HasDerivAt (fun u : ℝ => 1 + a * (u : ℂ)) a t := by
        simpa using ((hasDerivAt_id (t : ℂ)).const_mul a).const_add 1 |>.comp_ofReal
      exact h1.clog_real (one_add_mul_ofReal_mem_slitPlane ha (le_of_lt ht)))
    (fun t ht => by
      have h := (hasDerivAt_ofReal_cpow_const (ne_of_gt ht) hs).div_const s
      rwa [mul_div_cancel_left₀ _ hs] at h)
    (by
      refine hconv.congr_fun (fun t _ => ?_) measurableSet_Ioi
      simp only [Pi.mul_apply, smul_eq_mul]; ring)
    (by
      have hI : IntegrableOn (fun x : ℝ => a / s * ((x : ℂ) ^ (s + 1 - 1) *
          (a⁻¹ / (a⁻¹ + x)))) (Ioi 0) :=
        (integrableOn_cpow_sub_one_mul_div_add hs10 hs11 hz).const_mul (a / s)
      refine hI.congr_fun (fun t ht => ?_) measurableSet_Ioi
      have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
      have hn : 1 + a * t ≠ 0 := slitPlane_ne_zero (one_add_mul_ofReal_mem_slitPlane ha ht0)
      have hn' : a⁻¹ + t ≠ 0 := fun h => hn (by
        rw [show (1 : ℂ) + a * t = a * (a⁻¹ + t) by field_simp, h, mul_zero])
      simp only [Pi.mul_apply, add_sub_cancel_right]
      field_simp)
    (by
      show Tendsto (fun t : ℝ => Complex.log (1 + a * t) * ((t : ℂ) ^ s / s)) _ _
      refine squeeze_zero_norm' (a := fun t : ℝ => K * t ^ (1 + s.re) / ‖s‖) ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with t ht
        have ht0 : (0 : ℝ) < t := ht
        refine (huv_bound t ht0).trans ?_
        rw [Real.rpow_add ht0, Real.rpow_one]
        calc K * Real.log (1 + t) * t ^ s.re / ‖s‖ ≤ K * t * t ^ s.re / ‖s‖ := by
              gcongr; exact hlog1 t ht0.le
          _ = K * (t * t ^ s.re) / ‖s‖ := by ring
      · have h : Tendsto (fun t : ℝ => t ^ (1 + s.re)) (𝓝[>] 0) (𝓝 0) := by
          have := (Real.continuousAt_rpow_const 0 (1 + s.re) (Or.inr (by linarith)))
          simpa [Real.zero_rpow (show 1 + s.re ≠ 0 by linarith)] using
            this.tendsto.mono_left nhdsWithin_le_nhds
        simpa using (h.const_mul K).div_const ‖s‖)
    (by
      show Tendsto (fun t : ℝ => Complex.log (1 + a * t) * ((t : ℂ) ^ s / s)) _ _
      refine squeeze_zero_norm' (a := fun t : ℝ => K * (2 / ε) * t ^ (ε + s.re) / ‖s‖) ?_ ?_
      · filter_upwards [eventually_ge_atTop 1] with t ht
        have ht0 : (0 : ℝ) < t := by linarith
        refine (huv_bound t ht0).trans ?_
        rw [Real.rpow_add ht0]
        have := hlog2 t ht
        have h0 : 0 ≤ t ^ s.re := Real.rpow_nonneg ht0.le _
        have : K * Real.log (1 + t) * t ^ s.re ≤ K * (2 / ε * t ^ ε) * t ^ s.re := by gcongr
        calc K * Real.log (1 + t) * t ^ s.re / ‖s‖ ≤ K * (2 / ε * t ^ ε) * t ^ s.re / ‖s‖ := by
              gcongr
          _ = K * (2 / ε) * (t ^ ε * t ^ s.re) / ‖s‖ := by ring
      · have h := tendsto_rpow_neg_atTop (y := -(ε + s.re)) (by rw [hε]; linarith)
        simp only [neg_neg] at h
        simpa using (h.const_mul (K * (2 / ε))).div_const ‖s‖)
  simp only [sub_zero, zero_sub] at hibp
  have hm : mellin (fun x : ℝ => Complex.log (1 + a * x)) s =
      ∫ t in Ioi (0 : ℝ), Complex.log (1 + a * t) * (t : ℂ) ^ (s - 1) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [smul_eq_mul]; ring
  have hm2 : ∫ t in Ioi (0 : ℝ), a / (1 + a * t) * ((t : ℂ) ^ s / s) =
      a / s * ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s + 1 - 1) * (a⁻¹ / (a⁻¹ + t)) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
    have hn : 1 + a * t ≠ 0 := slitPlane_ne_zero (one_add_mul_ofReal_mem_slitPlane ha ht0)
    have hn' : a⁻¹ + t ≠ 0 := fun h => hn (by
      rw [show (1 : ℂ) + a * t = a * (a⁻¹ + t) by field_simp, h, mul_zero])
    simp only [add_sub_cancel_right]
    field_simp
  have harg : a.arg ≠ Real.pi := (mem_slitPlane_iff_arg.mp ha).1
  have hsin : Complex.sin ((s + 1) * Real.pi) = -Complex.sin (s * Real.pi) := by
    rw [add_mul, one_mul, Complex.sin_add_pi]
  have hsin0 : Complex.sin (s * Real.pi) ≠ 0 := by
    rw [Ne, Complex.sin_eq_zero_iff]
    rintro ⟨k, hk⟩
    have hs' : s = k := mul_right_cancel₀ (ofReal_ne_zero.mpr Real.pi_ne_zero) hk
    have h0 : (-1 : ℝ) < k := by simpa [hs'] using hs0
    have h1 : (k : ℝ) < 0 := by simpa [hs'] using hs1
    have h0' : -1 < k := by exact_mod_cast h0
    have h1' : k < 0 := by exact_mod_cast h1
    omega
  have has : a ^ s ≠ 0 := (cpow_ne_zero_iff_of_exponent_ne_zero hs).mpr ha0
  rw [hm, hibp, hm2, integral_cpow_sub_one_mul_div_add hs10 hs11 hz, hsin,
    cpow_add _ _ (inv_ne_zero ha0), cpow_one, inv_cpow _ _ harg]
  field_simp

/-- DLMF Table 1.14.5, row 7: `ln|(1 + x)/(1 - x)| ↦ π tan(½sπ)/s`, `-1 < ℜs < 1`, `s ≠ 0`. -/
@[dlmf 1.14.T5]
theorem mellin_log_abs_one_add_div_one_sub {s : ℂ} (hs0 : -1 < s.re) (hs1 : s.re < 1)
    (hs : s ≠ 0) :
    mellin (fun x => (Real.log |(1 + x) / (1 - x)| : ℂ)) s =
      Real.pi * Complex.tan (s * Real.pi / 2) / s := by
  sorry

/-- A boundary term `F(t) tˢ/s` tends to zero where `|F(t)| ≤ C t^q` and `t^{q + ℜs} → 0`. -/
private lemma tendsto_mul_cpow_div_of_abs_le {l : Filter ℝ} {F : ℝ → ℝ} {s : ℂ} {C q : ℝ}
    (hl : ∀ᶠ t in l, 0 < t ∧ |F t| ≤ C * t ^ q)
    (hlim : Tendsto (fun t : ℝ => t ^ (q + s.re)) l (𝓝 0)) :
    Tendsto (fun t : ℝ => (F t : ℂ) * ((t : ℂ) ^ s / s)) l (𝓝 0) := by
  have h2 : Tendsto (fun t : ℝ => C * t ^ (q + s.re) / ‖s‖) l (𝓝 0) := by
    simpa using (hlim.const_mul C).div_const ‖s‖
  refine squeeze_zero_norm' ?_ h2
  filter_upwards [hl] with t ⟨ht, hF⟩
  rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_cpow_eq_rpow_re_of_pos ht, Real.rpow_add ht]
  have hpos : 0 ≤ t ^ s.re / ‖s‖ := by positivity
  calc |F t| * (t ^ s.re / ‖s‖) ≤ C * t ^ q * (t ^ s.re / ‖s‖) :=
        mul_le_mul_of_nonneg_right hF hpos
    _ = C * (t ^ q * t ^ s.re) / ‖s‖ := by ring

/-- `t^p → 0` as `t → 0⁺` for `p > 0`. -/
private lemma tendsto_rpow_nhdsGT_zero {p : ℝ} (hp : 0 < p) :
    Tendsto (fun t : ℝ => t ^ p) (𝓝[>] 0) (𝓝 0) := by
  have := (Real.continuousAt_rpow_const 0 p (Or.inr hp.le)).tendsto
  rw [Real.zero_rpow hp.ne'] at this
  exact this.mono_left nhdsWithin_le_nhds

/-- DLMF Table 1.14.5, row 8: `ln(1 + x)/x ↦ π csc(sπ)/(1 - s)`, `0 < ℜs < 1`. -/
@[dlmf 1.14.T5]
theorem mellin_log_one_add_div {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    mellin (fun x => (Real.log (1 + x) / x : ℂ)) s =
      Real.pi / Complex.sin (s * Real.pi) / (1 - s) := by
  have hs1' : s - 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  set ε := (1 - s.re) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hε1 : ε ≤ 1 := by rw [hε]; linarith
  -- bounds on `log (1 + t)`
  have hlog0 : ∀ t : ℝ, 0 < t → 0 ≤ Real.log (1 + t) := fun t ht =>
    Real.log_nonneg (by linarith)
  have hlog1 : ∀ t : ℝ, 0 < t → Real.log (1 + t) ≤ t := fun t ht => by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + t by linarith); linarith
  have hlog2 : ∀ t : ℝ, 1 ≤ t → Real.log (1 + t) ≤ 2 / ε * t ^ ε := fun t ht => by
    have h1 := Real.log_le_rpow_div (show (0 : ℝ) ≤ 1 + t by linarith) hε0
    have h2 : (1 + t) ^ ε ≤ (2 * t) ^ ε :=
      Real.rpow_le_rpow (by linarith) (by linarith) hε0.le
    have h3 : (2 * t) ^ ε ≤ 2 * t ^ ε := by
      rw [Real.mul_rpow (by norm_num) (by linarith)]
      gcongr
      calc (2 : ℝ) ^ ε ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hε1
        _ = 2 := Real.rpow_one 2
    calc Real.log (1 + t) ≤ (1 + t) ^ ε / ε := h1
      _ ≤ 2 * t ^ ε / ε := by gcongr; exact h2.trans h3
      _ = 2 / ε * t ^ ε := by ring
  have hcast : ∀ t : ℝ, (Real.log (1 + t) : ℂ) / (t : ℂ) = ((Real.log (1 + t) / t : ℝ) : ℂ) :=
    fun t => by push_cast; rfl
  -- convergence of the two Mellin integrals
  have hc1 : MellinConvergent (fun t : ℝ => 1 / (1 + (t : ℂ))) s := by
    have hnorm : ∀ t : ℝ, 0 < t → ‖1 / (1 + (t : ℂ))‖ = 1 / (1 + t) := fun t ht => by
      rw [show (1 : ℂ) + (t : ℂ) = ((1 + t : ℝ) : ℂ) by push_cast; ring, norm_div,
        norm_one, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    refine mellinConvergent_of_isBigO_rpow (a := 1) (b := 0) ?_ ?_ hs1 ?_ hs0
    · refine ContinuousOn.locallyIntegrableOn (fun t ht => ?_) measurableSet_Ioi
      refine (continuousAt_const.div (continuousAt_const.add
        Complex.continuous_ofReal.continuousAt) ?_).continuousWithinAt
      intro h
      have h' : ((1 + t : ℝ) : ℂ) = 0 := by push_cast; exact h
      have : (0 : ℝ) < 1 + t := by have : (0 : ℝ) < t := ht; linarith
      exact this.ne' (by exact_mod_cast h')
    · refine Asymptotics.IsBigO.of_bound 1 ?_
      filter_upwards [eventually_gt_atTop 0] with t ht
      rw [hnorm t ht, Real.norm_of_nonneg (Real.rpow_nonneg ht.le _), Real.rpow_neg_one,
        one_mul, one_div]
      exact inv_anti₀ ht (by linarith)
    · refine Asymptotics.IsBigO.of_bound 1 ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht' : (0 : ℝ) < t := ht
      rw [hnorm t ht', neg_zero, Real.rpow_zero, norm_one, one_mul,
        div_le_one (by linarith)]
      linarith
  have hc2 : MellinConvergent (fun t : ℝ => (Real.log (1 + t) / t : ℂ)) s := by
    refine mellinConvergent_of_isBigO_rpow (a := 1 - ε) (b := 0) ?_ ?_ (by rw [hε]; linarith)
      ?_ hs0
    · refine ContinuousOn.locallyIntegrableOn (fun t ht => ?_) measurableSet_Ioi
      have ht' : (0 : ℝ) < t := ht
      refine ContinuousAt.continuousWithinAt ?_
      refine ContinuousAt.div ?_ Complex.continuous_ofReal.continuousAt
        (by exact_mod_cast ht'.ne')
      exact Complex.continuous_ofReal.continuousAt.comp
        ((continuousAt_const.add continuousAt_id).log
          (show (1 : ℝ) + t ≠ 0 by linarith))
    · refine Asymptotics.IsBigO.of_bound (2 / ε) ?_
      filter_upwards [eventually_ge_atTop 1] with t ht
      have ht0 : (0 : ℝ) < t := by linarith
      rw [hcast,
        Complex.norm_real, Real.norm_of_nonneg (div_nonneg (hlog0 t ht0) ht0.le),
        Real.norm_of_nonneg (Real.rpow_nonneg ht0.le _), neg_sub, div_le_iff₀ ht0]
      calc Real.log (1 + t) ≤ 2 / ε * t ^ ε := hlog2 t ht
        _ = 2 / ε * t ^ (ε - 1) * t := by
          rw [mul_assoc, ← Real.rpow_add_one ht0.ne']; ring_nf
    · refine Asymptotics.IsBigO.of_bound 1 ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : (0 : ℝ) < t := ht
      rw [hcast,
        Complex.norm_real, Real.norm_of_nonneg (div_nonneg (hlog0 t ht0) ht0.le), neg_zero,
        Real.rpow_zero, norm_one, one_mul, div_le_one ht0]
      exact hlog1 t ht0
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul (a := 0) (a' := 0) (b' := 0)
    (u := fun t => (Real.log (1 + t) : ℂ)) (u' := fun t => ((1 / (1 + t) : ℝ) : ℂ))
    (v := fun t => (t : ℂ) ^ (s - 1) / (s - 1)) (v' := fun t => (t : ℂ) ^ (s - 1 - 1))
    (fun t ht => by
      have ht' : (0 : ℝ) < t := ht
      have h := ((hasDerivAt_id t).const_add 1).log (by simp; linarith)
      simpa using h.ofReal_comp)
    (fun t ht => by
      have h := (hasDerivAt_ofReal_cpow_const (ne_of_gt ht) hs1').div_const (s - 1)
      rwa [mul_div_cancel_left₀ _ hs1'] at h)
    (by
      refine hc2.congr_fun (fun t ht => ?_) measurableSet_Ioi
      have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (show (0 : ℝ) < t from ht))
      have hcp : (t : ℂ) ^ (s - 1) = (t : ℂ) ^ (s - 1 - 1) * t := by
        have h := Complex.cpow_add (s - 1 - 1) 1 ht'
        rwa [Complex.cpow_one, sub_add_cancel] at h
      simp only [Pi.mul_apply, smul_eq_mul]
      rw [hcp]
      field_simp)
    (by
      have hI : IntegrableOn (fun x : ℝ => 1 / (s - 1) *
          ((x : ℂ) ^ (s - 1) • (1 / (1 + (x : ℂ))))) (Ioi 0) :=
        Integrable.const_mul hc1 (1 / (s - 1))
      refine hI.congr_fun (fun t _ => ?_) measurableSet_Ioi
      simp only [Pi.mul_apply, smul_eq_mul]
      push_cast; ring)
    (tendsto_mul_cpow_div_of_abs_le (C := 1) (q := 1)
      (by
        filter_upwards [self_mem_nhdsWithin] with t ht
        have ht0 : (0 : ℝ) < t := ht
        refine ⟨ht0, ?_⟩
        rw [Real.rpow_one, one_mul, abs_of_nonneg (hlog0 t ht0)]
        exact hlog1 t ht0)
      (tendsto_rpow_nhdsGT_zero (by simp; linarith)))
    (tendsto_mul_cpow_div_of_abs_le (C := 2 / ε) (q := ε)
      (by
        filter_upwards [eventually_ge_atTop 1] with t ht
        have ht0 : (0 : ℝ) < t := by linarith
        exact ⟨ht0, by rw [abs_of_nonneg (hlog0 t ht0)]; exact hlog2 t ht⟩)
      (by
        have := tendsto_rpow_neg_atTop (y := ε) hε0
        convert this using 2
        simp only [sub_re, one_re]
        rw [hε]; ring_nf))
  simp only [sub_zero, zero_sub] at hibp
  have hm : mellin (fun t : ℝ => (Real.log (1 + t) / t : ℂ)) s =
      ∫ t in Ioi (0 : ℝ), (Real.log (1 + t) : ℂ) * (t : ℂ) ^ (s - 1 - 1) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (show (0 : ℝ) < t from ht))
    have hcp : (t : ℂ) ^ (s - 1) = (t : ℂ) ^ (s - 1 - 1) * t := by
      have h := Complex.cpow_add (s - 1 - 1) 1 ht'
      rwa [Complex.cpow_one, sub_add_cancel] at h
    simp only [smul_eq_mul]
    rw [hcp]
    field_simp
  have hm2 : ∫ t in Ioi (0 : ℝ), ((1 / (1 + t) : ℝ) : ℂ) * ((t : ℂ) ^ (s - 1) / (s - 1)) =
      1 / (s - 1) * mellin (fun t : ℝ => 1 / (1 + (t : ℂ))) s := by
    rw [mellin, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [smul_eq_mul]
    push_cast; ring
  rw [hm, hibp, hm2, mellin_inv_one_add hs0 hs1]
  have h1s : (1 : ℂ) - s ≠ 0 := fun h => hs1' (by linear_combination -h)
  field_simp
  ring

/-- Mellin transform of `t ↦ 1/(1 + t²)` at `s + 1`: `π/(2 cos(½sπ))`, `-1 < ℜs < 1`. -/
private lemma mellin_inv_one_add_sq_add_one {s : ℂ} (hs0 : -1 < s.re) (hs1 : s.re < 1) :
    MellinConvergent (fun t : ℝ => 1 / (1 + (t : ℂ) ^ 2)) (s + 1) ∧
      mellin (fun t : ℝ => 1 / (1 + (t : ℂ) ^ 2)) (s + 1) =
        Real.pi / (2 * Complex.cos (s * Real.pi / 2)) := by
  have hne : ∀ t : ℝ, 1 + (t : ℂ) ^ 2 ≠ 0 := fun t h => by
    have h' : ((1 + t ^ 2 : ℝ) : ℂ) = 0 := by push_cast; exact h
    have : (0 : ℝ) < 1 + t ^ 2 := by positivity
    exact this.ne' (by exact_mod_cast h')
  have hnorm : ∀ t : ℝ, ‖1 / (1 + (t : ℂ) ^ 2)‖ = 1 / (1 + t ^ 2) := fun t => by
    rw [show (1 : ℂ) + (t : ℂ) ^ 2 = ((1 + t ^ 2 : ℝ) : ℂ) by push_cast; ring, norm_div,
      norm_one, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  refine ⟨?_, ?_⟩
  · refine mellinConvergent_of_isBigO_rpow (a := 2) (b := 0) ?_ ?_ (by simp; linarith) ?_
      (by simp; linarith)
    · refine ContinuousOn.locallyIntegrableOn ?_ measurableSet_Ioi
      exact (continuous_const.div (continuous_const.add
        (Complex.continuous_ofReal.pow 2)) hne).continuousOn
    · refine Asymptotics.IsBigO.of_bound 1 ?_
      filter_upwards [eventually_gt_atTop 0] with t ht
      rw [hnorm, Real.norm_of_nonneg (Real.rpow_nonneg ht.le _), one_mul, Real.rpow_neg ht.le,
        Real.rpow_two, one_div]
      exact inv_anti₀ (by positivity) (by linarith)
    · refine Asymptotics.IsBigO.of_bound 1 ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      rw [hnorm, neg_zero, Real.rpow_zero, norm_one, one_mul]
      rw [div_le_one (by positivity)]
      nlinarith
  · have h := mellin_comp_rpow (fun t : ℝ => 1 / (1 + (t : ℂ))) (s + 1) 2
    simp only [Real.rpow_two, Complex.ofReal_pow] at h
    rw [h, mellin_inv_one_add (by simp; linarith) (by simp; linarith)]
    have hc : Complex.sin ((s + 1) / 2 * Real.pi) = Complex.cos (s * Real.pi / 2) := by
      rw [show (s + 1) / 2 * Real.pi = s * Real.pi / 2 + Real.pi / 2 by ring,
        Complex.sin_add_pi_div_two]
    push_cast
    rw [hc]
    simp only [abs_two, Complex.real_smul]
    push_cast
    field_simp

/-- Mellin transform by parts for `F` with `F'(t) = c/(1 + t²)`. -/
private lemma mellin_eq_of_hasDerivAt_div_one_add_sq {F : ℝ → ℝ} {c : ℝ} {s : ℂ}
    (hs0 : -1 < s.re) (hs1 : s.re < 1) (hs : s ≠ 0)
    (hF : ∀ t : ℝ, 0 < t → HasDerivAt F (c / (1 + t ^ 2)) t)
    (hconv : MellinConvergent (fun t => (F t : ℂ)) s)
    (h0 : Tendsto (fun t : ℝ => (F t : ℂ) * ((t : ℂ) ^ s / s)) (𝓝[>] 0) (𝓝 0))
    (hinf : Tendsto (fun t : ℝ => (F t : ℂ) * ((t : ℂ) ^ s / s)) atTop (𝓝 0)) :
    mellin (fun t => (F t : ℂ)) s =
      -(c * (Real.pi / Complex.cos (s * Real.pi / 2)) / (2 * s)) := by
  obtain ⟨hgc, hg⟩ := mellin_inv_one_add_sq_add_one hs0 hs1
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul (a := 0) (a' := 0) (b' := 0)
    (u := fun t => (F t : ℂ)) (u' := fun t => ((c / (1 + t ^ 2) : ℝ) : ℂ))
    (v := fun t => (t : ℂ) ^ s / s) (v' := fun t => (t : ℂ) ^ (s - 1))
    (fun t ht => (hF t ht).ofReal_comp)
    (fun t ht => by
      have h := (hasDerivAt_ofReal_cpow_const (ne_of_gt ht) hs).div_const s
      rwa [mul_div_cancel_left₀ _ hs] at h)
    (by
      refine hconv.congr_fun (fun t _ => ?_) measurableSet_Ioi
      simp only [Pi.mul_apply, smul_eq_mul]; ring)
    (by
      have hI : IntegrableOn (fun x : ℝ => (c : ℂ) / s *
          ((x : ℂ) ^ (s + 1 - 1) • (1 / (1 + (x : ℂ) ^ 2)))) (Ioi 0) :=
        Integrable.const_mul hgc ((c : ℂ) / s)
      refine hI.congr_fun (fun t _ => ?_) measurableSet_Ioi
      simp only [Pi.mul_apply, smul_eq_mul, add_sub_cancel_right]
      push_cast; ring)
    h0 hinf
  simp only [sub_zero, zero_sub] at hibp
  have hm : mellin (fun t => (F t : ℂ)) s =
      ∫ t in Ioi (0 : ℝ), (F t : ℂ) * (t : ℂ) ^ (s - 1) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [smul_eq_mul]; ring
  have hm2 : ∫ t in Ioi (0 : ℝ), ((c / (1 + t ^ 2) : ℝ) : ℂ) * ((t : ℂ) ^ s / s) =
      (c / s) * mellin (fun t : ℝ => 1 / (1 + (t : ℂ) ^ 2)) (s + 1) := by
    rw [mellin, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [smul_eq_mul, add_sub_cancel_right]
    push_cast; ring
  rw [hm, hibp, hm2, hg]
  field_simp

/-- DLMF Table 1.14.5, row 9: `arctan x ↦ -π sec(½sπ)/(2s)`, `-1 < ℜs < 0`. -/
@[dlmf 1.14.T5]
theorem mellin_arctan {s : ℂ} (hs0 : -1 < s.re) (hs1 : s.re < 0) :
    mellin (fun x => (Real.arctan x : ℂ)) s =
      -(Real.pi / Complex.cos (s * Real.pi / 2)) / (2 * s) := by
  have hs : s ≠ 0 := fun h => by simp [h] at hs1
  have hπ := Real.pi_pos
  have hbd : ∀ t : ℝ, |Real.arctan t| ≤ Real.pi / 2 := fun t =>
    abs_le.mpr ⟨(Real.neg_pi_div_two_lt_arctan t).le, (Real.arctan_lt_pi_div_two t).le⟩
  have h := mellin_eq_of_hasDerivAt_div_one_add_sq (F := Real.arctan) (c := 1) hs0 (by linarith)
    hs (fun t _ => by simpa using Real.hasDerivAt_arctan t)
    (by
      refine mellinConvergent_of_isBigO_rpow (a := 0) (b := -1)
        ((Complex.continuous_ofReal.comp Real.continuous_arctan).continuousOn.locallyIntegrableOn
          measurableSet_Ioi) ?_ hs1 ?_ hs0
      · refine Asymptotics.IsBigO.of_bound (Real.pi / 2) ?_
        filter_upwards [eventually_gt_atTop 0] with t ht
        rw [Complex.norm_real, Real.norm_eq_abs, neg_zero, Real.rpow_zero, norm_one, mul_one]
        exact hbd t
      · refine Asymptotics.IsBigO.of_bound 1 ?_
        filter_upwards [self_mem_nhdsWithin] with t ht
        rw [Complex.norm_real, Real.norm_eq_abs, neg_neg, Real.rpow_one, one_mul]
        exact Real.abs_arctan_le_abs)
    (tendsto_mul_cpow_div_of_abs_le (C := 1) (q := 1)
      (by
        filter_upwards [self_mem_nhdsWithin] with t ht
        refine ⟨ht, ?_⟩
        rw [Real.rpow_one, one_mul]
        exact Real.abs_arctan_le_abs.trans (abs_of_pos (show (0 : ℝ) < t from ht)).le)
      (tendsto_rpow_nhdsGT_zero (by linarith)))
    (tendsto_mul_cpow_div_of_abs_le (C := Real.pi / 2) (q := 0)
      (by
        filter_upwards [eventually_gt_atTop 0] with t ht
        exact ⟨ht, by rw [Real.rpow_zero, mul_one]; exact hbd t⟩)
      (by simpa using tendsto_rpow_neg_atTop (y := -s.re) (by linarith)))
  rw [h]
  push_cast
  ring

/-- DLMF Table 1.14.5, row 10: `arccot x = π/2 - arctan x ↦ π sec(½sπ)/(2s)`, `0 < ℜs < 1`. -/
@[dlmf 1.14.T5]
theorem mellin_arccot {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    mellin (fun x => ((Real.pi / 2 - Real.arctan x : ℝ) : ℂ)) s =
      Real.pi / Complex.cos (s * Real.pi / 2) / (2 * s) := by
  have hs : s ≠ 0 := fun h => by simp [h] at hs0
  have hπ := Real.pi_pos
  have hF : ∀ t : ℝ, 0 < t → |Real.pi / 2 - Real.arctan t| ≤ t⁻¹ ∧
      |Real.pi / 2 - Real.arctan t| ≤ Real.pi / 2 := by
    intro t ht
    rw [← Real.arctan_inv_of_pos ht, abs_of_pos (Real.arctan_pos.mpr (inv_pos.mpr ht))]
    exact ⟨Real.arctan_le_self (inv_pos.mpr ht).le, (Real.arctan_lt_pi_div_two _).le⟩
  have h := mellin_eq_of_hasDerivAt_div_one_add_sq
    (F := fun t => Real.pi / 2 - Real.arctan t) (c := -1) (by linarith) hs1
    hs (fun t _ => by
      have h := (hasDerivAt_const t (Real.pi / 2)).fun_sub (Real.hasDerivAt_arctan t)
      rwa [zero_sub, ← neg_div] at h)
    (by
      refine mellinConvergent_of_isBigO_rpow (a := 1) (b := 0)
        ((Complex.continuous_ofReal.comp (continuous_const.sub
          Real.continuous_arctan)).continuousOn.locallyIntegrableOn measurableSet_Ioi)
        ?_ hs1 ?_ hs0
      · refine Asymptotics.IsBigO.of_bound 1 ?_
        filter_upwards [eventually_gt_atTop 0] with t ht
        rw [Complex.norm_real, Real.norm_eq_abs, Real.norm_of_nonneg (Real.rpow_nonneg ht.le _),
          Real.rpow_neg_one, one_mul]
        exact (hF t ht).1
      · refine Asymptotics.IsBigO.of_bound (Real.pi / 2) ?_
        filter_upwards [self_mem_nhdsWithin] with t ht
        rw [Complex.norm_real, Real.norm_eq_abs, neg_zero, Real.rpow_zero, norm_one, mul_one]
        exact (hF t ht).2)
    (tendsto_mul_cpow_div_of_abs_le (C := Real.pi / 2) (q := 0)
      (by
        filter_upwards [self_mem_nhdsWithin] with t ht
        exact ⟨ht, by rw [Real.rpow_zero, mul_one]; exact (hF t ht).2⟩)
      (by simpa using tendsto_rpow_nhdsGT_zero hs0))
    (tendsto_mul_cpow_div_of_abs_le (C := 1) (q := -1)
      (by
        filter_upwards [eventually_gt_atTop 0] with t ht
        exact ⟨ht, by rw [Real.rpow_neg_one, one_mul]; exact (hF t ht).1⟩)
      (by
        have := tendsto_rpow_neg_atTop (y := 1 - s.re) (by linarith)
        simpa [neg_sub, sub_eq_neg_add] using this))
  rw [h]
  push_cast
  ring

/-- A cut-plane point shifted by a nonnegative real stays in the cut plane. -/
private lemma add_ofReal_mem_slitPlane {z : ℂ} (hz : z ∈ slitPlane) {t : ℝ} (ht : 0 ≤ t) :
    z + t ∈ slitPlane := by
  rw [mem_slitPlane_iff] at hz ⊢
  simp only [add_re, ofReal_re, add_im, ofReal_im, add_zero]
  rcases hz with h | h
  · exact Or.inl (by linarith)
  · exact Or.inr h

/-- `e^{iθ}` lies in the cut plane for `-π < θ < π`. -/
private lemma exp_mul_I_mem_slitPlane {θ : ℝ} (hθ1 : -Real.pi < θ) (hθ2 : θ < Real.pi) :
    cexp (θ * I) ∈ slitPlane := by
  rw [mem_slitPlane_iff, exp_ofReal_mul_I_re, exp_ofReal_mul_I_im]
  by_cases h : Real.sin θ = 0
  · left
    rw [Real.sin_eq_zero_iff_of_lt_of_lt hθ1 hθ2] at h
    simp [h]
  · exact Or.inr h

/-- `(e^{iθ})^s = e^{isθ}` (principal power) for `-π < θ ≤ π`. -/
private lemma exp_mul_I_cpow {θ : ℝ} (hθ1 : -Real.pi < θ) (hθ2 : θ ≤ Real.pi) (s : ℂ) :
    cexp (θ * I) ^ s = cexp (s * θ * I) := by
  rw [cpow_def_of_ne_zero (exp_ne_zero _), log_exp (by simpa using hθ1) (by simpa using hθ2)]
  ring_nf

/-- DLMF Table 1.14.5, row 11: `(1 + x cos θ)/(1 + 2x cos θ + x²) ↦ π cos(sθ)/sin(sπ)`,
`-π < θ < π`, `0 < ℜs < 1`. -/
@[dlmf 1.14.T5]
theorem mellin_poisson_cos {θ : ℝ} (hθ1 : -Real.pi < θ) (hθ2 : θ < Real.pi) {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    mellin (fun x => (((1 + x * Real.cos θ) / (1 + 2 * x * Real.cos θ + x ^ 2) : ℝ) : ℂ)) s =
      Real.pi * Complex.cos (s * θ) / Complex.sin (s * Real.pi) := by
  set u := cexp ((-θ : ℝ) * I)
  set v := cexp (θ * I)
  have hu := exp_mul_I_mem_slitPlane (θ := -θ) (by linarith) (by linarith)
  have hv := exp_mul_I_mem_slitPlane hθ1 hθ2
  have he : ∀ x ∈ Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) •
      (((1 + x * Real.cos θ) / (1 + 2 * x * Real.cos θ + x ^ 2) : ℝ) : ℂ) =
      (1 / 2 : ℂ) * ((x : ℂ) ^ (s - 1) * (u / (u + x))) +
        (1 / 2 : ℂ) * ((x : ℂ) ^ (s - 1) * (v / (v + x))) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    have hu0 : u + x ≠ 0 := slitPlane_ne_zero (add_ofReal_mem_slitPlane hu hx0.le)
    have hv0 : v + x ≠ 0 := slitPlane_ne_zero (add_ofReal_mem_slitPlane hv hx0.le)
    have huv : u * v = 1 := by
      rw [← Complex.exp_add]; push_cast; ring_nf; exact Complex.exp_zero
    have hc : Complex.cos (θ : ℂ) = (u + v) / 2 := by
      simp only [u, v, Complex.cos, ofReal_neg, neg_mul]; ring
    have hD : ((1 + 2 * x * Real.cos θ + x ^ 2 : ℝ) : ℂ) = (u + x) * (v + x) := by
      push_cast; rw [hc]; linear_combination (-1 : ℂ) * huv
    rw [ofReal_div, hD, smul_eq_mul]
    push_cast
    rw [hc]
    field_simp
    linear_combination (-2 * (x : ℂ) ^ (s - 1)) * huv
  unfold mellin
  rw [setIntegral_congr_fun measurableSet_Ioi he, integral_add
    ((integrableOn_cpow_sub_one_mul_div_add hs0 hs1 hu).const_mul _)
    ((integrableOn_cpow_sub_one_mul_div_add hs0 hs1 hv).const_mul _), integral_const_mul,
    integral_const_mul, integral_cpow_sub_one_mul_div_add hs0 hs1 hu,
    integral_cpow_sub_one_mul_div_add hs0 hs1 hv, exp_mul_I_cpow (by linarith) (by linarith),
    exp_mul_I_cpow hθ1 hθ2.le, Complex.cos]
  push_cast
  ring_nf

/-- DLMF Table 1.14.5, row 12: `x sin θ/(1 + 2x cos θ + x²) ↦ π sin(sθ)/sin(sπ)`,
`-π < θ < π`, `0 < ℜs < 1`. -/
@[dlmf 1.14.T5]
theorem mellin_poisson_sin {θ : ℝ} (hθ1 : -Real.pi < θ) (hθ2 : θ < Real.pi) {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    mellin (fun x => ((x * Real.sin θ / (1 + 2 * x * Real.cos θ + x ^ 2) : ℝ) : ℂ)) s =
      Real.pi * Complex.sin (s * θ) / Complex.sin (s * Real.pi) := by
  set u := cexp ((-θ : ℝ) * I)
  set v := cexp (θ * I)
  have hu := exp_mul_I_mem_slitPlane (θ := -θ) (by linarith) (by linarith)
  have hv := exp_mul_I_mem_slitPlane hθ1 hθ2
  have he : ∀ x ∈ Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) •
      ((x * Real.sin θ / (1 + 2 * x * Real.cos θ + x ^ 2) : ℝ) : ℂ) =
      (-(I / 2)) * ((x : ℂ) ^ (s - 1) * (v / (v + x))) +
        (I / 2) * ((x : ℂ) ^ (s - 1) * (u / (u + x))) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    have hu0 : u + x ≠ 0 := slitPlane_ne_zero (add_ofReal_mem_slitPlane hu hx0.le)
    have hv0 : v + x ≠ 0 := slitPlane_ne_zero (add_ofReal_mem_slitPlane hv hx0.le)
    have huv : u * v = 1 := by
      rw [← Complex.exp_add]; push_cast; ring_nf; exact Complex.exp_zero
    have hc : Complex.cos (θ : ℂ) = (u + v) / 2 := by
      simp only [u, v, Complex.cos, ofReal_neg, neg_mul]; ring
    have hs : Complex.sin (θ : ℂ) = (u - v) * I / 2 := by
      simp only [u, v, Complex.sin, ofReal_neg, neg_mul]
    have hD : ((1 + 2 * x * Real.cos θ + x ^ 2 : ℝ) : ℂ) = (u + x) * (v + x) := by
      push_cast; rw [hc]; linear_combination (-1 : ℂ) * huv
    rw [ofReal_div, hD, smul_eq_mul]
    push_cast
    rw [hs]
    field_simp
    ring
  unfold mellin
  rw [setIntegral_congr_fun measurableSet_Ioi he, integral_add
    ((integrableOn_cpow_sub_one_mul_div_add hs0 hs1 hv).const_mul _)
    ((integrableOn_cpow_sub_one_mul_div_add hs0 hs1 hu).const_mul _), integral_const_mul,
    integral_const_mul, integral_cpow_sub_one_mul_div_add hs0 hs1 hu,
    integral_cpow_sub_one_mul_div_add hs0 hs1 hv,
    exp_mul_I_cpow (θ := -θ) (by linarith) (by linarith), exp_mul_I_cpow hθ1 hθ2.le]
  have hsθ : Complex.sin (s * θ) = (cexp (-(s * θ) * I) - cexp (s * θ * I)) * I / 2 := by
    rw [Complex.sin]
  rw [hsθ]
  push_cast
  ring_nf

end DLMF.AlgebraicAnalytic
