/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Airy.ModulusPhase.Nicholson

/-!
# Reciprocal Airy modulus expansions

Weighted Nicholson functions and reciprocal expansions prepare the integration of the Airy phase
derivatives.

Source references and common attribution are retained in
`DLMF.Airy.ModulusPhase`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF.Confluent

open scoped Real Topology

namespace DLMF.Airy

/-! ### The weighted Nicholson function for `|x|^{-1/4} N(x)` -/

/-- `e^{-u} u^a e^{-v u³/12}` is integrable on `(0, ∞)` for `a > -1` and `v ≥ 0`. -/
theorem airyMod_wInt {a : ℝ} (ha : -1 < a) {v : ℝ} (hv : 0 ≤ v) :
    IntegrableOn (fun u : ℝ => Real.exp (-u) * u ^ a * Real.exp (-(v * u ^ 3 / 12))) (Ioi 0) := by
  have hint := Real.GammaIntegral_convergent (s := a + 1) (by linarith)
  rw [show a + 1 - 1 = a by ring] at hint
  refine hint.mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
    exact (((Real.continuous_exp.comp continuous_neg).continuousAt.mul
      (Real.continuousAt_rpow_const _ _ (Or.inl (ne_of_gt ht)))).mul
      ((Real.continuous_exp.comp (by fun_prop)).continuousAt)).continuousWithinAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
    have h1 : Real.exp (-(v * t ^ 3 / 12)) ≤ 1 := Real.exp_le_one_iff.mpr
      (neg_nonpos.mpr (by positivity))
    have h0 : 0 ≤ Real.exp (-t) * t ^ a := by positivity
    rw [Real.norm_of_nonneg (by positivity)]
    calc Real.exp (-t) * t ^ a * Real.exp (-(v * t ^ 3 / 12)) ≤ Real.exp (-t) * t ^ a * 1 := by
          gcongr
      _ = _ := by ring

/-- The weighted Nicholson function `G(v) = ∫₀^∞ e^{-u}(u^{-1/2} + (v/2) u^{3/2}) e^{-vu³/12} du`. -/
noncomputable def airyMod_wG (v : ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), Real.exp (-u) * (u ^ (-(1 / 2) : ℝ) + v / 2 * u ^ (3 / 2 : ℝ)) *
    Real.exp (-(v * u ^ 3 / 12))

/-- The `v`-derivative of the integrand of `G`. -/
theorem airyMod_wG_hasDerivAt_integrand (u v : ℝ) :
    HasDerivAt (fun v : ℝ => Real.exp (-u) * (u ^ (-(1 / 2) : ℝ) + v / 2 * u ^ (3 / 2 : ℝ)) *
        Real.exp (-(v * u ^ 3 / 12)))
      (Real.exp (-u) * (u ^ (3 / 2 : ℝ) / 2 - u ^ 3 / 12 * (u ^ (-(1 / 2) : ℝ) +
        v / 2 * u ^ (3 / 2 : ℝ))) * Real.exp (-(v * u ^ 3 / 12))) v := by
  have h1 : HasDerivAt (fun v : ℝ => u ^ (-(1 / 2) : ℝ) + v / 2 * u ^ (3 / 2 : ℝ))
      (u ^ (3 / 2 : ℝ) / 2) v := by
    have := (((hasDerivAt_id' v).div_const 2).mul_const (u ^ (3 / 2 : ℝ))).const_add
      (u ^ (-(1 / 2) : ℝ))
    exact this.congr_deriv (by ring)
  have h2 : HasDerivAt (fun v : ℝ => Real.exp (-(v * u ^ 3 / 12)))
      (Real.exp (-(v * u ^ 3 / 12)) * (-(u ^ 3 / 12))) v := by
    have e : (fun v : ℝ => Real.exp (-(v * u ^ 3 / 12))) =
        fun v => Real.exp (v * (-(u ^ 3 / 12))) := by funext v; ring_nf
    rw [e]
    exact ((hasDerivAt_mul_const (-(u ^ 3 / 12))).exp).congr_deriv
      (by rw [show v * -(u ^ 3 / 12) = -(v * u ^ 3 / 12) by ring])
  have := (h1.const_mul (Real.exp (-u))).mul h2
  convert this using 1
  ring

/-- `u^{a} ≤ u^{b_1} + u^{b_2}` style domination: `u^a ≤ u^{-1/2} + u^{9/2}` for `-1/2 ≤ a ≤ 9/2`. -/
theorem airyMod_rpow_le_sum {u a : ℝ} (hu : 0 < u) (ha1 : -(1 / 2) ≤ a) (ha2 : a ≤ 9 / 2) :
    u ^ a ≤ u ^ (-(1 / 2) : ℝ) + u ^ (9 / 2 : ℝ) := by
  rcases le_total u 1 with h | h
  · have := Real.rpow_le_rpow_of_exponent_ge hu h ha1
    have : 0 ≤ u ^ (9 / 2 : ℝ) := by positivity
    linarith
  · have := Real.rpow_le_rpow_of_exponent_le h ha2
    have : 0 ≤ u ^ (-(1 / 2) : ℝ) := by positivity
    linarith

/-- Rewriting `u³ u^{a}` as `u^{a+3}` for `u > 0`. -/
theorem airyMod_pow_three_mul_rpow {u : ℝ} (hu : 0 < u) (a : ℝ) :
    u ^ 3 * u ^ a = u ^ (a + 3) := by
  rw [Real.rpow_add hu, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring

/-- Domination of the `v`-derivative of the integrand of `G` near `v`, uniformly for
`|w - v| < v/2`. -/
private lemma airyMod_wG_deriv_bound {u v w : ℝ} (hu : 0 < u)
    (hw : w ∈ Metric.ball v (v / 2)) :
    ‖Real.exp (-u) * (u ^ (3 / 2 : ℝ) / 2 - u ^ 3 / 12 * (u ^ (-(1 / 2) : ℝ) +
        w / 2 * u ^ (3 / 2 : ℝ))) * Real.exp (-(w * u ^ 3 / 12))‖ ≤
      (1 + 1 / 12 + v / 24 * 3 / 2 + 1) *
        (Real.exp (-u) * (u ^ (-(1 / 2) : ℝ) + u ^ (9 / 2 : ℝ))) := by
  have hw' : |w - v| < v / 2 := by simpa [Real.dist_eq] using hw
  have hw0 : 0 < w := by have := abs_lt.mp hw'; linarith
  have hw1 : w ≤ 3 * v / 2 := by have := abs_lt.mp hw'; linarith
  have hE : Real.exp (-(w * u ^ 3 / 12)) ≤ 1 := Real.exp_le_one_iff.mpr
    (neg_nonpos.mpr (by positivity))
  have hE0 := Real.exp_pos (-(w * u ^ 3 / 12))
  have he := Real.exp_pos (-u)
  -- the three powers appearing
  have p1 := airyMod_rpow_le_sum hu (a := 3 / 2) (by norm_num) (by norm_num)
  have p2 : u ^ 3 * u ^ (-(1 / 2) : ℝ) ≤ u ^ (-(1 / 2) : ℝ) + u ^ (9 / 2 : ℝ) := by
    rw [airyMod_pow_three_mul_rpow hu]
    exact airyMod_rpow_le_sum hu (by norm_num) (by norm_num)
  have p3 : u ^ 3 * u ^ (3 / 2 : ℝ) ≤ u ^ (-(1 / 2) : ℝ) + u ^ (9 / 2 : ℝ) := by
    rw [airyMod_pow_three_mul_rpow hu]
    exact airyMod_rpow_le_sum hu (by norm_num) (by norm_num)
  have q1 : 0 ≤ u ^ (3 / 2 : ℝ) := by positivity
  have q2 : 0 ≤ u ^ 3 * u ^ (-(1 / 2) : ℝ) := by positivity
  have q3 : 0 ≤ u ^ 3 * u ^ (3 / 2 : ℝ) := by positivity
  have hS : 0 ≤ u ^ (-(1 / 2) : ℝ) + u ^ (9 / 2 : ℝ) := by positivity
  have habs : |u ^ (3 / 2 : ℝ) / 2 - u ^ 3 / 12 * (u ^ (-(1 / 2) : ℝ) +
      w / 2 * u ^ (3 / 2 : ℝ))| ≤ (1 + 1 / 12 + v / 24 * 3 / 2 + 1) *
        (u ^ (-(1 / 2) : ℝ) + u ^ (9 / 2 : ℝ)) := by
    rw [abs_le]
    constructor <;> nlinarith
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos he, abs_of_pos hE0]
  calc Real.exp (-u) * |u ^ (3 / 2 : ℝ) / 2 - u ^ 3 / 12 * (u ^ (-(1 / 2) : ℝ) +
        w / 2 * u ^ (3 / 2 : ℝ))| * Real.exp (-(w * u ^ 3 / 12))
      ≤ Real.exp (-u) * ((1 + 1 / 12 + v / 24 * 3 / 2 + 1) *
        (u ^ (-(1 / 2) : ℝ) + u ^ (9 / 2 : ℝ))) * 1 := by
        gcongr
        exact mul_nonneg he.le (mul_nonneg (by linarith) hS)
    _ = _ := by ring

/-- `G'(v) = ∫₀^∞ e^{-u}(u^{3/2}/2 - u^{5/2}/12 - (v/24) u^{9/2}) e^{-vu³/12} du` for `v > 0`. -/
theorem airyMod_wG_hasDerivAt {v : ℝ} (hv : 0 < v) :
    HasDerivAt airyMod_wG (∫ u in Ioi (0 : ℝ), Real.exp (-u) *
      (u ^ (3 / 2 : ℝ) / 2 - u ^ 3 / 12 * (u ^ (-(1 / 2) : ℝ) + v / 2 * u ^ (3 / 2 : ℝ))) *
        Real.exp (-(v * u ^ 3 / 12))) v := by
  have hball : Metric.ball v (v / 2) ∈ 𝓝 v := Metric.ball_mem_nhds v (by positivity)
  set B : ℝ → ℝ := fun u => (1 + 1 / 12 + v / 24 * 3 / 2 + 1) *
    (Real.exp (-u) * (u ^ (-(1 / 2) : ℝ) + u ^ (9 / 2 : ℝ)))
  have hBi : IntegrableOn B (Ioi 0) := by
    have h1 := airyMod_wInt (a := -(1 / 2)) (by norm_num) (le_refl 0)
    have h2 := airyMod_wInt (a := 9 / 2) (by norm_num) (le_refl 0)
    refine IntegrableOn.congr_fun ((h1.add h2).const_mul (1 + 1 / 12 + v / 24 * 3 / 2 + 1))
      (fun u _ => ?_) measurableSet_Ioi
    simp only [B, Pi.add_apply, zero_mul, zero_div, neg_zero, Real.exp_zero, mul_one]; ring
  have hmeas : ∀ w : ℝ, AEStronglyMeasurable (fun u : ℝ => Real.exp (-u) *
      (u ^ (-(1 / 2) : ℝ) + w / 2 * u ^ (3 / 2 : ℝ)) * Real.exp (-(w * u ^ 3 / 12)))
      (volume.restrict (Ioi 0)) := by
    intro w
    refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
    exact (((Real.continuous_exp.comp continuous_neg).continuousAt.mul
      ((Real.continuousAt_rpow_const _ _ (Or.inl (ne_of_gt ht))).add
        (continuousAt_const.mul (Real.continuousAt_rpow_const _ _ (Or.inl (ne_of_gt ht)))))).mul
      ((Real.continuous_exp.comp (by fun_prop)).continuousAt)).continuousWithinAt
  have hint0 : IntegrableOn (fun u : ℝ => Real.exp (-u) *
      (u ^ (-(1 / 2) : ℝ) + v / 2 * u ^ (3 / 2 : ℝ)) * Real.exp (-(v * u ^ 3 / 12))) (Ioi 0) := by
    have h1 := airyMod_wInt (a := -(1 / 2)) (by norm_num) hv.le
    have h2 := (airyMod_wInt (a := 3 / 2) (by norm_num) hv.le).const_mul (v / 2)
    refine IntegrableOn.congr_fun (h1.add h2) (fun u _ => ?_) measurableSet_Ioi
    simp only [Pi.add_apply]; ring
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0)) hball
    (F := fun w (u : ℝ) => Real.exp (-u) * (u ^ (-(1 / 2) : ℝ) + w / 2 * u ^ (3 / 2 : ℝ)) *
      Real.exp (-(w * u ^ 3 / 12)))
    (F' := fun w (u : ℝ) => Real.exp (-u) *
      (u ^ (3 / 2 : ℝ) / 2 - u ^ 3 / 12 * (u ^ (-(1 / 2) : ℝ) + w / 2 * u ^ (3 / 2 : ℝ))) *
        Real.exp (-(w * u ^ 3 / 12)))
    (Eventually.of_forall hmeas) hint0 ?_
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu w hw => ?_)) hBi
    (Eventually.of_forall fun u w _ => airyMod_wG_hasDerivAt_integrand u w)
  · exact h.2
  · refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
    have hc1 := Real.continuousAt_rpow_const t (3 / 2 : ℝ) (Or.inl (ne_of_gt ht))
    have hc2 := Real.continuousAt_rpow_const t (-(1 / 2) : ℝ) (Or.inl (ne_of_gt ht))
    exact (((Real.continuous_exp.comp continuous_neg).continuousAt.mul
      ((hc1.div_const 2).sub (((continuous_pow 3).continuousAt.div_const 12).mul
        (hc2.add (continuousAt_const.mul hc1))))).mul
      ((Real.continuous_exp.comp (by fun_prop)).continuousAt)).continuousWithinAt
  · exact airyMod_wG_deriv_bound hu hw

/-- The boundary term `e^{-u} u^{5/2} e^{-vu³/12}` of the integration by parts tends to `0`
as `u → ∞`. -/
private lemma airyMod_wG_tendsto_boundary {v : ℝ} (hv : 0 < v) :
    Tendsto (fun u : ℝ => Real.exp (-u) * u ^ (5 / 2 : ℝ) * Real.exp (-(v * u ^ 3 / 12))) atTop
      (𝓝 0) := by
  have h0 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (5 / 2) 1 one_pos
  refine squeeze_zero' (Eventually.of_forall fun u => ?_) ?_ h0
  · rcases le_or_gt 0 u with hu | hu
    · positivity
    · rw [Real.rpow_def_of_neg hu]
      have h := Real.exp_pos (-u)
      have h' := Real.exp_pos (-(v * u ^ 3 / 12))
      have hc : 0 ≤ Real.exp (Real.log u * (5 / 2)) * Real.cos (5 / 2 * π) := by
        rw [show (5 / 2 : ℝ) * π = π / 2 + 2 * π by ring, Real.cos_add_two_pi,
          Real.cos_pi_div_two, mul_zero]
      positivity
  · filter_upwards [eventually_gt_atTop 0] with u hu
    have hE : Real.exp (-(v * u ^ 3 / 12)) ≤ 1 := Real.exp_le_one_iff.mpr
      (neg_nonpos.mpr (by positivity))
    calc Real.exp (-u) * u ^ (5 / 2 : ℝ) * Real.exp (-(v * u ^ 3 / 12))
        ≤ Real.exp (-u) * u ^ (5 / 2 : ℝ) * 1 := by gcongr
      _ = u ^ (5 / 2 : ℝ) * Real.exp (-1 * u) := by ring_nf

/-- **The integration by parts behind 9.8(iii)**: `G'(v) = (1/12) ∫₀^∞ e^{-u}(u^{5/2} + u^{3/2})
e^{-vu³/12} du`, which is positive. -/
theorem airyMod_wG_deriv_eq {v : ℝ} (hv : 0 < v) :
    (∫ u in Ioi (0 : ℝ), Real.exp (-u) *
      (u ^ (3 / 2 : ℝ) / 2 - u ^ 3 / 12 * (u ^ (-(1 / 2) : ℝ) + v / 2 * u ^ (3 / 2 : ℝ))) *
        Real.exp (-(v * u ^ 3 / 12))) =
      1 / 12 * ∫ u in Ioi (0 : ℝ), Real.exp (-u) * (u ^ (5 / 2 : ℝ) + u ^ (3 / 2 : ℝ)) *
        Real.exp (-(v * u ^ 3 / 12)) := by
  set E : ℝ → ℝ := fun u => Real.exp (-(v * u ^ 3 / 12))
  set φ : ℝ → ℝ := fun u => Real.exp (-u) * u ^ (5 / 2 : ℝ) * E u
  set φ' : ℝ → ℝ := fun u => Real.exp (-u) *
    (5 / 2 * u ^ (3 / 2 : ℝ) - u ^ (5 / 2 : ℝ) - v / 4 * u ^ (9 / 2 : ℝ)) * E u
  have i32 := airyMod_wInt (a := 3 / 2) (by norm_num) hv.le
  have i52 := airyMod_wInt (a := 5 / 2) (by norm_num) hv.le
  have i92 := airyMod_wInt (a := 9 / 2) (by norm_num) hv.le
  have hφ'i : IntegrableOn φ' (Ioi 0) := by
    refine IntegrableOn.congr_fun (((i32.const_mul (5 / 2)).sub i52).sub (i92.const_mul (v / 4)))
      (fun u _ => ?_) measurableSet_Ioi
    simp only [φ', E, Pi.sub_apply]; ring
  have hderiv : ∀ u ∈ Ioi (0 : ℝ), HasDerivAt φ (φ' u) u := by
    intro u (hu : 0 < u)
    have h1 : HasDerivAt (fun u : ℝ => Real.exp (-u)) (Real.exp (-u) * (-1)) u :=
      (hasDerivAt_neg u).exp
    have h2 : HasDerivAt (fun u : ℝ => u ^ (5 / 2 : ℝ)) (5 / 2 * u ^ (5 / 2 - 1 : ℝ)) u :=
      Real.hasDerivAt_rpow_const (Or.inl hu.ne')
    have h3 : HasDerivAt E (E u * (-(v * (3 * u ^ 2) / 12))) u := by
      have := ((((hasDerivAt_pow 3 u).const_mul v).div_const 12).neg).exp
      simp only [E]; convert this using 1
    have := (h1.mul h2).mul h3
    refine this.congr_deriv ?_
    simp only [φ', E, Pi.mul_apply]
    rw [show (5 / 2 - 1 : ℝ) = 3 / 2 by norm_num]
    have e1 : u ^ (5 / 2 : ℝ) * u ^ 2 = u ^ (9 / 2 : ℝ) := by
      rw [show (9 / 2 : ℝ) = 5 / 2 + 2 by norm_num, Real.rpow_add hu,
        show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [← e1]; ring
  have hcont : ContinuousWithinAt φ (Ici 0) 0 := by
    have : Continuous φ := by
      simp only [φ, E]
      exact ((Real.continuous_exp.comp continuous_neg).mul
        (Real.continuous_rpow_const (by norm_num))).mul (Real.continuous_exp.comp (by fun_prop))
    exact this.continuousWithinAt
  have hlim : Tendsto φ atTop (𝓝 0) := airyMod_wG_tendsto_boundary hv
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hφ'i hlim
  have hφ0 : φ 0 = 0 := by simp [φ]
  rw [hφ0, sub_zero] at hftc
  -- split the integrand
  have hsplit : ∀ u ∈ Ioi (0 : ℝ), Real.exp (-u) *
      (u ^ (3 / 2 : ℝ) / 2 - u ^ 3 / 12 * (u ^ (-(1 / 2) : ℝ) + v / 2 * u ^ (3 / 2 : ℝ))) *
        Real.exp (-(v * u ^ 3 / 12)) =
      1 / 12 * (Real.exp (-u) * (u ^ (5 / 2 : ℝ) + u ^ (3 / 2 : ℝ)) *
        Real.exp (-(v * u ^ 3 / 12))) + 1 / 6 * φ' u := by
    intro u (hu : 0 < u)
    simp only [φ', E]
    have e1 := airyMod_pow_three_mul_rpow hu (-(1 / 2))
    have e2 := airyMod_pow_three_mul_rpow hu (3 / 2)
    rw [show (-(1 / 2) + 3 : ℝ) = 5 / 2 by norm_num] at e1
    rw [show (3 / 2 + 3 : ℝ) = 9 / 2 by norm_num] at e2
    linear_combination (-(Real.exp (-u) * Real.exp (-(v * u ^ 3 / 12))) / 12) * e1 +
      (-(Real.exp (-u) * Real.exp (-(v * u ^ 3 / 12))) * v / 24) * e2
  have hI : IntegrableOn (fun u => Real.exp (-u) * (u ^ (5 / 2 : ℝ) + u ^ (3 / 2 : ℝ)) *
      Real.exp (-(v * u ^ 3 / 12))) (Ioi 0) :=
    (i52.add i32).congr_fun (fun u _ => by simp only [Pi.add_apply]; ring) measurableSet_Ioi
  rw [setIntegral_congr_fun measurableSet_Ioi hsplit,
    integral_add (hI.const_mul _) (hφ'i.const_mul _),
    integral_const_mul, integral_const_mul, hftc]
  ring

/-- `G'(v) > 0` for `v > 0`. -/
theorem airyMod_wG_deriv_pos {v : ℝ} (hv : 0 < v) : 0 < deriv airyMod_wG v := by
  rw [(airyMod_wG_hasDerivAt hv).deriv, airyMod_wG_deriv_eq hv]
  have i32 := airyMod_wInt (a := 3 / 2) (by norm_num) hv.le
  have i52 := airyMod_wInt (a := 5 / 2) (by norm_num) hv.le
  refine mul_pos (by norm_num) (airyMod_integral_pos
    (IntegrableOn.congr_fun (i52.add i32) (fun u _ => by simp only [Pi.add_apply]; ring)
      measurableSet_Ioi) fun u hu => by positivity)

/-- `G` is strictly increasing on `(0, ∞)`. -/
theorem airyMod_wG_strictMono : StrictMonoOn airyMod_wG (Ioi 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0) ?_ ?_
  · exact fun v hv => (airyMod_wG_hasDerivAt hv).continuousAt.continuousWithinAt
  · intro v hv
    rw [interior_Ioi] at hv
    exact airyMod_wG_deriv_pos hv

/-- Scaling `t = u/s` in the Nicholson-type integrals:
`∫₀^∞ e^{-st} e^{-t³/12} t^p dt = s^{-(p+1)} ∫₀^∞ e^{-u} u^p e^{-s^{-3}u³/12} du`. -/
theorem airyMod_wScale {s : ℝ} (hs : 0 < s) (p : ℝ) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-s * t) * (Real.exp (-(t ^ 3 / 12)) * t ^ p)) =
      s ^ (-(p + 1)) * ∫ u in Ioi (0 : ℝ), Real.exp (-u) * u ^ p *
        Real.exp (-((s ^ 3)⁻¹ * u ^ 3 / 12)) := by
  set g : ℝ → ℝ := fun t => Real.exp (-s * t) * (Real.exp (-(t ^ 3 / 12)) * t ^ p)
  have h := integral_comp_mul_left_Ioi g 0 (inv_pos.mpr hs)
  rw [mul_zero, smul_eq_mul, inv_inv] at h
  have key : ∀ u ∈ Ioi (0 : ℝ), g (s⁻¹ * u) = s ^ (-p) *
      (Real.exp (-u) * u ^ p * Real.exp (-((s ^ 3)⁻¹ * u ^ 3 / 12))) := by
    intro u (hu : 0 < u)
    simp only [g]
    rw [Real.mul_rpow (inv_pos.mpr hs).le hu.le, Real.inv_rpow hs.le, ← Real.rpow_neg hs.le]
    have : -s * (s⁻¹ * u) = -u := by field_simp
    rw [this, mul_pow, inv_pow]
    ring_nf
  rw [setIntegral_congr_fun measurableSet_Ioi key, integral_const_mul] at h
  have hs0 : 0 < s ^ (-p) := by positivity
  have : (∫ t in Ioi (0 : ℝ), g t) = s⁻¹ * (s ^ (-p) * ∫ u in Ioi (0 : ℝ),
      Real.exp (-u) * u ^ p * Real.exp (-((s ^ 3)⁻¹ * u ^ 3 / 12))) := by
    rw [h]; field_simp
  rw [this, Real.rpow_neg hs.le (p + 1), Real.rpow_neg hs.le p, Real.rpow_add_one hs.ne']
  field_simp

/-- **Scaling form for `N²`**: for `s > 0`, `π^{3/2} s^{-1/2} N(-s)² = G(s^{-3})`. -/
theorem airyMod_wG_scaling {s : ℝ} (hs : 0 < s) :
    s ^ (-(1 / 2) : ℝ) * airyDerivModulus (-s) ^ 2 = airyMod_wG ((s ^ 3)⁻¹) / (π * Real.sqrt π) := by
  have hv : 0 ≤ (s ^ 3)⁻¹ := by positivity
  have h0 : (∫ t in Ioi (0 : ℝ), airyMod_kernel (-s) t) = s ^ (-(-(1 / 2) + 1) : ℝ) *
      ∫ u in Ioi (0 : ℝ), Real.exp (-u) * u ^ (-(1 / 2) : ℝ) *
        Real.exp (-((s ^ 3)⁻¹ * u ^ 3 / 12)) := by
    rw [← airyMod_wScale hs]; rfl
  have h2 : (∫ t in Ioi (0 : ℝ), airyMod_kernel2 (-s) t) = s ^ (-(3 / 2 + 1) : ℝ) *
      ∫ u in Ioi (0 : ℝ), Real.exp (-u) * u ^ (3 / 2 : ℝ) *
        Real.exp (-((s ^ 3)⁻¹ * u ^ 3 / 12)) := by
    rw [← airyMod_wScale hs]
    refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
    simp only [airyMod_kernel2]
    rw [show (3 / 2 : ℝ) = 2 + -(1 / 2) by norm_num, Real.rpow_add ht,
      show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hG : airyMod_wG ((s ^ 3)⁻¹) = (∫ u in Ioi (0 : ℝ), Real.exp (-u) * u ^ (-(1 / 2) : ℝ) *
        Real.exp (-((s ^ 3)⁻¹ * u ^ 3 / 12))) + (s ^ 3)⁻¹ / 2 * ∫ u in Ioi (0 : ℝ),
          Real.exp (-u) * u ^ (3 / 2 : ℝ) * Real.exp (-((s ^ 3)⁻¹ * u ^ 3 / 12)) := by
    rw [← integral_const_mul, ← integral_add (airyMod_wInt (by norm_num) hv)
      ((airyMod_wInt (by norm_num) hv).const_mul _)]
    unfold airyMod_wG
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    ring
  rw [airyMod_derivSq_eq_integral, h0, h2, hG]
  have e1 : s ^ (-(1 / 2) : ℝ) * s ^ (-(3 / 2 + 1) : ℝ) = (s ^ 3)⁻¹ := by
    rw [← Real.rpow_add hs, ← Real.rpow_natCast, ← Real.rpow_neg hs.le]; norm_num
  have e2 : s ^ (-(1 / 2) : ℝ) * s * s ^ (-(-(1 / 2) + 1) : ℝ) = 1 := by
    rw [mul_assoc, mul_comm s, ← Real.rpow_add_one hs.ne', ← Real.rpow_add hs]; norm_num
  rw [mul_div_assoc']
  congr 1
  linear_combination (∫ u in Ioi (0 : ℝ), Real.exp (-u) * u ^ (3 / 2 : ℝ) *
      Real.exp (-((s ^ 3)⁻¹ * u ^ 3 / 12))) / 2 * e1 + (∫ u in Ioi (0 : ℝ), Real.exp (-u) *
        u ^ (-(1 / 2) : ℝ) * Real.exp (-((s ^ 3)⁻¹ * u ^ 3 / 12))) * e2

/-- `|x|^{-1/4} N(x)` is strictly increasing on `(-∞, 0)`, DLMF §9.8(iii). -/
theorem airy_weighted_derivModulus_monotone :
    StrictMonoOn (fun x : ℝ => |x| ^ (-1 / 4 : ℝ) * airyDerivModulus x) (Iio 0) := by
  intro x (hx : x < 0) y (hy : y < 0) hxy
  have hsq : ∀ z : ℝ, z < 0 → (|z| ^ (-1 / 4 : ℝ) * airyDerivModulus z) ^ 2 =
      airyMod_wG (((-z) ^ 3)⁻¹) / (π * Real.sqrt π) := by
    intro z hz
    rw [← airyMod_wG_scaling (neg_pos.mpr hz), neg_neg, mul_pow, abs_of_neg hz,
      ← Real.rpow_natCast, ← Real.rpow_mul (neg_pos.mpr hz).le]
    norm_num
  have hpos : ∀ z : ℝ, z < 0 → 0 ≤ |z| ^ (-1 / 4 : ℝ) * airyDerivModulus z := fun z _ =>
    mul_nonneg (by positivity) (airyDerivModulus_pos z).le
  refine lt_of_pow_lt_pow_left₀ 2 (hpos y hy) ?_
  rw [hsq x hx, hsq y hy]
  refine div_lt_div_of_pos_right ?_ (by positivity)
  have hx3 : 0 < (-x) ^ 3 := pow_pos (by linarith) 3
  have hy3 : 0 < (-y) ^ 3 := pow_pos (by linarith) 3
  have h3 : (-y) ^ 3 < (-x) ^ 3 := pow_lt_pow_left₀ (by linarith) (by linarith) (by norm_num)
  exact airyMod_wG_strictMono (inv_pos.mpr hx3) (inv_pos.mpr hy3) (inv_strictAnti₀ hy3 h3)

/-- `M(x) N(x)` is strictly increasing on `(-∞, 0]`, DLMF §9.8(iii). -/
theorem airy_modulus_product_monotone :
    StrictMonoOn (fun x => airyModulus x * airyDerivModulus x) (Iic 0) := by
  intro x _ y _ hxy
  have hπ := Real.pi_pos
  have w1 : ∀ t, 0 < t → 0 < Real.exp (-(t ^ 3 / 12)) * (t ^ 1 * t ^ (-(1 / 2) : ℝ)) :=
    fun t _ => by positivity
  have mono := airyMod_integral_exp_strictMono w1 (fun a => airyMod_integrableOn_exp_pow a 1) hxy
  have pos : 0 < ∫ t in Ioi (0 : ℝ), airyMod_kernel1 x t :=
    airyMod_integral_pos (airyMod_integrableOn_exp_pow x 1) fun t ht => by
      unfold airyMod_kernel1; positivity
  have hc : ∀ z, (airyModulus z * airyDerivModulus z) ^ 2 =
      (airyAiReal z * airyAiDerivReal z + airyBiReal z * airyBiDerivReal z) ^ 2 + (π ^ 2)⁻¹ := by
    intro z
    have hL := airy_lagrange z
    rw [mul_pow, airyModulus_sq, airyDerivModulus_sq]
    field_simp
    linear_combination hL
  have hx0 : 0 ≤ airyModulus x * airyDerivModulus x :=
    mul_nonneg (airyModulus_pos x).le (airyDerivModulus_pos x).le
  refine lt_of_pow_lt_pow_left₀ 2 (mul_nonneg (airyModulus_pos y).le (airyDerivModulus_pos y).le) ?_
  simp only
  rw [hc, hc, airyMod_cross_eq_integral, airyMod_cross_eq_integral]
  have hd : 0 < 2 * (π * Real.sqrt π) := by positivity
  simp only [airyMod_kernel1] at pos ⊢
  have : (∫ t in Ioi (0 : ℝ), Real.exp (x * t) * (Real.exp (-(t ^ 3 / 12)) *
      (t ^ 1 * t ^ (-(1 / 2) : ℝ)))) / (2 * (π * Real.sqrt π)) <
      (∫ t in Ioi (0 : ℝ), Real.exp (y * t) * (Real.exp (-(t ^ 3 / 12)) *
      (t ^ 1 * t ^ (-(1 / 2) : ℝ)))) / (2 * (π * Real.sqrt π)) := div_lt_div_of_pos_right mono hd
  have h0 : 0 < (∫ t in Ioi (0 : ℝ), Real.exp (x * t) * (Real.exp (-(t ^ 3 / 12)) *
      (t ^ 1 * t ^ (-(1 / 2) : ℝ)))) / (2 * (π * Real.sqrt π)) := div_pos pos hd
  nlinarith

/-- `θ'(x)` is strictly increasing on `(-∞, 0]`, DLMF §9.8(iii). -/
theorem airy_phase_deriv_monotone :
    StrictMonoOn (deriv airyPhase) (Iic 0) := by
  intro x _ y _ hxy
  rw [deriv_airyPhase]
  have hπ := Real.pi_pos
  have h := airyMod_sq_strictMono hxy
  have hx := pow_pos (airyModulus_pos x) 2
  simp only at h ⊢
  rw [neg_lt_neg_iff]
  exact one_div_lt_one_div_of_lt (by positivity) (mul_lt_mul_of_pos_left h hπ)

/-- `φ'(x)` is strictly increasing on `(-∞, 0]`, DLMF §9.8(iii). -/
theorem airy_derivPhase_deriv_monotone :
    StrictMonoOn (deriv airyDerivPhase) (Iic 0) := by
  have hπ := Real.pi_pos
  rw [deriv_airyDerivPhase]
  have key : ∀ x : ℝ, x < 0 → x / (π * airyDerivModulus x ^ 2) =
      -1 / (π * (π * Real.sqrt π)⁻¹ * ((∫ t in Ioi (0 : ℝ), airyMod_kernel2 x t) / (2 * (-x)) +
        ∫ t in Ioi (0 : ℝ), airyMod_kernel x t)) := by
    intro x hx
    have p2 : 0 < ∫ t in Ioi (0 : ℝ), airyMod_kernel2 x t :=
      airyMod_integral_pos (airyMod_kernel2_integrable x) fun t ht => by
        unfold airyMod_kernel2; positivity
    have p0 : 0 < ∫ t in Ioi (0 : ℝ), airyMod_kernel x t :=
      airyMod_integral_pos (airyMod_kernel_integrable x) (fun t ht => airyMod_kernel_pos x ht)
    have hN := pow_pos (airyDerivModulus_pos x) 2
    have hsp : 0 < Real.sqrt π := Real.sqrt_pos.mpr hπ
    have hq : 0 < (∫ t in Ioi (0 : ℝ), airyMod_kernel2 x t) / (2 * (-x)) +
        ∫ t in Ioi (0 : ℝ), airyMod_kernel x t := by
      have : 0 < (∫ t in Ioi (0 : ℝ), airyMod_kernel2 x t) / (2 * (-x)) :=
        div_pos p2 (by linarith)
      linarith
    rw [div_eq_div_iff (by positivity) (by positivity), airyMod_derivSq_eq_integral]
    have : x ≠ 0 := hx.ne
    field_simp
    ring
  intro x (hx : x ≤ 0) y (hy : y ≤ 0) hxy
  have hxn : x < 0 := lt_of_lt_of_le hxy hy
  simp only
  rcases hy.lt_or_eq with hy' | rfl
  · rw [key x hxn, key y hy']
    have w0 : ∀ t, 0 < t → 0 < Real.exp (-(t ^ 3 / 12)) * t ^ (-(1 / 2) : ℝ) :=
      fun t _ => by positivity
    have w2 : ∀ t, 0 < t → 0 < Real.exp (-(t ^ 3 / 12)) * (t ^ 2 * t ^ (-(1 / 2) : ℝ)) :=
      fun t _ => by positivity
    have i0 := airyMod_integral_exp_strictMono w0
      (fun a => (airyMod_integrableOn_exp a).congr_fun (fun t _ => rfl) measurableSet_Ioi) hxy
    have i2 := airyMod_integral_exp_strictMono w2 (fun a => airyMod_integrableOn_exp_pow a 2) hxy
    have p2 : 0 < ∫ t in Ioi (0 : ℝ), airyMod_kernel2 x t :=
      airyMod_integral_pos (airyMod_kernel2_integrable x) fun t ht => by
        unfold airyMod_kernel2; positivity
    have p0 : 0 < ∫ t in Ioi (0 : ℝ), airyMod_kernel x t :=
      airyMod_integral_pos (airyMod_kernel_integrable x) (fun t ht => airyMod_kernel_pos x ht)
    simp only [airyMod_kernel, airyMod_kernel2] at i0 i2 p0 p2 ⊢
    have hc : 0 < π * (π * Real.sqrt π)⁻¹ := by positivity
    have h2 : (∫ t in Ioi (0 : ℝ), Real.exp (x * t) * (Real.exp (-(t ^ 3 / 12)) *
        (t ^ 2 * t ^ (-(1 / 2) : ℝ)))) / (2 * -x) < (∫ t in Ioi (0 : ℝ), Real.exp (y * t) *
        (Real.exp (-(t ^ 3 / 12)) * (t ^ 2 * t ^ (-(1 / 2) : ℝ)))) / (2 * -y) := by
      rw [div_lt_div_iff₀ (by linarith) (by linarith)]
      nlinarith
    have hq : ∀ z : ℝ, z < 0 → 0 < (∫ t in Ioi (0 : ℝ), Real.exp (z * t) *
        (Real.exp (-(t ^ 3 / 12)) * (t ^ 2 * t ^ (-(1 / 2) : ℝ)))) / (2 * -z) +
        ∫ t in Ioi (0 : ℝ), Real.exp (z * t) * (Real.exp (-(t ^ 3 / 12)) * t ^ (-(1 / 2) : ℝ)) := by
      intro z hz
      have a2 : 0 < ∫ t in Ioi (0 : ℝ), airyMod_kernel2 z t :=
        airyMod_integral_pos (airyMod_kernel2_integrable z) fun t ht => by
          unfold airyMod_kernel2; positivity
      have a0 : 0 < ∫ t in Ioi (0 : ℝ), airyMod_kernel z t :=
        airyMod_integral_pos (airyMod_kernel_integrable z) (fun t ht => airyMod_kernel_pos z ht)
      simp only [airyMod_kernel, airyMod_kernel2] at a0 a2
      have : 0 < (∫ t in Ioi (0 : ℝ), Real.exp (z * t) *
          (Real.exp (-(t ^ 3 / 12)) * (t ^ 2 * t ^ (-(1 / 2) : ℝ)))) / (2 * -z) :=
        div_pos a2 (by linarith)
      linarith
    rw [neg_div, neg_div, neg_lt_neg_iff]
    exact one_div_lt_one_div_of_lt (mul_pos hc (hq x hxn))
      (mul_lt_mul_of_pos_left (add_lt_add h2 i0) hc)
  · have : 0 < airyDerivModulus x ^ 2 := pow_pos (airyDerivModulus_pos x) 2
    simp only [zero_div]
    exact div_neg_of_neg_of_pos hxn (by positivity)

/-- `|x|^{1/4} M(x)` is strictly decreasing on `(-∞, 0)`, DLMF §9.8(iii). -/
theorem airy_weighted_modulus_monotone :
    StrictAntiOn (fun x : ℝ => |x| ^ (1 / 4 : ℝ) * airyModulus x) (Iio 0) := by
  intro x (hx : x < 0) y (hy : y < 0) hxy
  have hπ := Real.pi_pos
  have hsq : ∀ z : ℝ, z < 0 → (|z| ^ (1 / 4 : ℝ) * airyModulus z) ^ 2 =
      (∫ u in Ioi (0 : ℝ), Real.exp (-u) * (Real.exp (-(u ^ 3 / (12 * (-z) ^ 3))) *
        u ^ (-(1 / 2) : ℝ))) / (π * Real.sqrt π) := by
    intro z hz
    rw [← airyMod_sqrt_mul_sq (neg_pos.mpr hz), neg_neg, mul_pow, abs_of_neg hz,
      ← Real.rpow_natCast, ← Real.rpow_mul (neg_pos.mpr hz).le]
    norm_num
  have hpos : ∀ z : ℝ, z < 0 → 0 ≤ |z| ^ (1 / 4 : ℝ) * airyModulus z := fun z _ =>
    mul_nonneg (by positivity) (airyModulus_pos z).le
  refine lt_of_pow_lt_pow_left₀ 2 (hpos x hx) ?_
  rw [hsq x hx, hsq y hy]
  refine div_lt_div_of_pos_right ?_ (by positivity)
  rw [← sub_pos, ← integral_sub (airyMod_scaled_integrable (by linarith)) (airyMod_scaled_integrable (by linarith))]
  refine airyMod_integral_pos ((airyMod_scaled_integrable (by linarith)).sub (airyMod_scaled_integrable (by linarith)))
    fun u hu => ?_
  have h3 : (-y) ^ 3 < (-x) ^ 3 := by
    have : 0 < -y := by linarith
    exact pow_lt_pow_left₀ (by linarith) this.le (by norm_num)
  have hy3 : 0 < (-y) ^ 3 := by have : 0 < -y := by linarith
                                positivity
  have hlt : u ^ 3 / (12 * (-x) ^ 3) < u ^ 3 / (12 * (-y) ^ 3) :=
    div_lt_div_of_pos_left (by positivity) (by positivity) (by linarith)
  have h1 := Real.exp_lt_exp.mpr (neg_lt_neg hlt)
  have h2 : 0 < Real.exp (-u) * u ^ (-(1 / 2) : ℝ) := by positivity
  nlinarith

/-- Monotonicity in DLMF §9.8(iii); singular endpoints are excluded from weighted expressions. -/
theorem airy_phase_monotone :
    StrictAntiOn (airyPhase) (Iic 0) := by
  refine (strictAnti_of_deriv_neg fun x => ?_).strictAntiOn _
  rw [deriv_airyPhase]
  have := airyModulus_pos x; have := Real.pi_pos
  simp only [neg_lt_zero]; positivity

/-- Monotonicity in DLMF §9.8(iii); singular endpoints are excluded from weighted expressions. -/
theorem airy_derivPhase_monotone :
    StrictAntiOn (airyDerivPhase) (Iic 0) := by
  refine strictAntiOn_of_deriv_neg (convex_Iic 0) airyDerivPhase_continuous.continuousOn
    fun x hx => ?_
  rw [interior_Iic, mem_Iio] at hx
  rw [deriv_airyDerivPhase]
  have := airyDerivModulus_pos x; have := Real.pi_pos
  exact div_neg_of_neg_of_pos hx (by positivity)

/-! ### Termwise integration of the reciprocal expansions (phases) -/

/-- A function whose derivative is bounded by `K s^{p-1}` (`p < 0`) on `[R, ∞)` converges at
`+∞`, and its distance to the limit is at most `K s^p / (-p)`. -/
theorem airyMod_tendsto_of_deriv_bound {F f : ℝ → ℝ} {R K p : ℝ} (hR : 0 < R) (hp : p < 0)
    (hF : ∀ s, R ≤ s → HasDerivAt F (f s) s) (hf : ∀ s, R ≤ s → |f s| ≤ K * s ^ (p - 1)) :
    ∃ L, Tendsto F atTop (𝓝 L) ∧ ∀ s, R ≤ s → |F s - L| ≤ K * s ^ p / (-p) := by
  set Q : ℝ → ℝ := fun s => K * s ^ p / (-p)
  have hK : 0 ≤ K := by
    have h := (abs_nonneg _).trans (hf R le_rfl)
    have : 0 < R ^ (p - 1) := Real.rpow_pos_of_pos hR _
    nlinarith
  have hQ : ∀ s, R ≤ s → HasDerivAt Q (-(K * s ^ (p - 1))) s := fun s hs => by
    have hs0 : s ≠ 0 := (hR.trans_le hs).ne'
    have := ((Real.hasDerivAt_rpow_const (p := p) (Or.inl hs0)).const_mul K).div_const (-p)
    convert this using 1
    field_simp [hp.ne]
  have hQ0 : ∀ s, R ≤ s → 0 ≤ Q s := fun s hs => by
    have : 0 ≤ s ^ p := Real.rpow_nonneg (hR.le.trans hs) p
    exact div_nonneg (mul_nonneg hK this) (by linarith)
  have mono : ∀ {g g' : ℝ → ℝ}, (∀ s, R ≤ s → HasDerivAt g (g' s) s) →
      (∀ s, R ≤ s → 0 ≤ g' s) → MonotoneOn g (Ici R) := by
    intro g g' hg hg'
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici R)
      (fun s hs => (hg s hs).continuousAt.continuousWithinAt)
      (fun s hs => (hg s (interior_subset hs)).hasDerivWithinAt) ?_
    intro s hs
    exact hg' s (interior_subset hs)
  have m1 : MonotoneOn (fun s => F s - Q s) (Ici R) :=
    mono (fun s hs => (hF s hs).sub (hQ s hs)) fun s hs => by
      have := (abs_le.mp (hf s hs)).1; linarith
  have m2 : MonotoneOn (fun s => -(F s + Q s)) (Ici R) :=
    mono (fun s hs => ((hF s hs).add (hQ s hs)).neg) fun s hs => by
      have := (abs_le.mp (hf s hs)).2; linarith
  have key : ∀ s t, R ≤ s → s ≤ t → |F t - F s| ≤ Q s := fun s t hs hst => by
    have h1 := m1 (show s ∈ Ici R from hs) (show t ∈ Ici R from hs.trans hst) hst
    have h2 := m2 (show s ∈ Ici R from hs) (show t ∈ Ici R from hs.trans hst) hst
    have h3 := hQ0 t (hs.trans hst)
    simp only at h1 h2
    rw [abs_le]; constructor <;> linarith
  have hQlim : Tendsto Q atTop (𝓝 0) := by
    have := ((tendsto_rpow_neg_atTop (y := -p) (by linarith)).const_mul K).div_const (-p)
    simp only [neg_neg, mul_zero, zero_div] at this
    exact this
  have hc : CauchySeq F := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := (eventually_ge_atTop R).and (hQlim.eventually (gt_mem_nhds hε)) |>.exists_forall_of_atTop
    refine ⟨max N R, fun n hn => ?_⟩
    have hNR := (hN (max N R) (le_max_left _ _))
    rw [Real.dist_eq]
    exact (key _ _ hNR.1 hn).trans_lt hNR.2
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨L, hL, fun s hs => ?_⟩
  have ht : Tendsto (fun t => |F t - F s|) atTop (𝓝 |L - F s|) :=
    ((hL.sub_const (F s)).abs)
  have := le_of_tendsto ht (eventually_ge_atTop s |>.mono fun t hst => key s t hs hst)
  rwa [abs_sub_comm] at this

/-- `s^a (-s)^{-3k} = (-1)^k s^{a-3k}` for `s > 0`. -/
theorem airyMod_rpow_mul_zpow {s : ℝ} (hs : 0 < s) (a : ℝ) (k : ℕ) :
    s ^ a * (-s) ^ (-(3 * k : ℤ)) = (-1) ^ k * s ^ (a - 3 * k) := by
  rw [show (-(3 * k : ℤ)) = -((3 * k : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast,
    neg_pow, show (-1 : ℝ) ^ (3 * k) = (-1) ^ k by rw [pow_mul]; norm_num,
    Real.rpow_sub hs, ← Real.rpow_natCast s (3 * k)]
  push_cast
  have : (0 : ℝ) < s ^ ((3 : ℝ) * k) := Real.rpow_pos_of_pos hs _
  have h1 : ((-1 : ℝ) ^ k) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  field_simp
  exact h1.symm

/-- Derivative of the primitive scale `(2/3) s^{3/2} (-s)^{-3k} / (1 - 2k)`. -/
theorem airyMod_hasDerivAt_sigma {s : ℝ} (hs : 0 < s) (k : ℕ) (c : ℝ) :
    HasDerivAt (fun s : ℝ => 2 / 3 * s ^ (3 / 2 : ℝ) * (-s) ^ (-(3 * k : ℤ)) * (c / (1 - 2 * k)))
      (s ^ (1 / 2 : ℝ) * (-s) ^ (-(3 * k : ℤ)) * c) s := by
  have hk : (1 - 2 * (k : ℝ)) ≠ 0 := by
    intro h
    have : (2 : ℝ) * k = 1 := by linarith
    have h2 : (2 * k : ℕ) = 1 := by exact_mod_cast this
    omega
  have e : ∀ u : ℝ, 0 < u → 2 / 3 * u ^ (3 / 2 : ℝ) * (-u) ^ (-(3 * k : ℤ)) * (c / (1 - 2 * k)) =
      2 / 3 * (c / (1 - 2 * k)) * (-1) ^ k * u ^ ((3 / 2 : ℝ) - 3 * k) := fun u hu => by
    rw [mul_assoc (2 / 3 : ℝ), airyMod_rpow_mul_zpow hu]; ring
  have h := ((Real.hasDerivAt_rpow_const (p := (3 / 2 : ℝ) - 3 * k) (Or.inl hs.ne')).const_mul
    (2 / 3 * (c / (1 - 2 * k)) * (-1) ^ k))
  refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards [lt_mem_nhds hs] with u hu
    exact e u hu
  · rw [airyMod_rpow_mul_zpow hs, show (3 / 2 : ℝ) - 3 * k - 1 = 1 / 2 - 3 * k by ring]
    field_simp

/-- `|s^a (-s)^{-3k}| = s^{a-3k}`. -/
theorem airyMod_abs_rpow_mul_zpow {s : ℝ} (hs : 0 < s) (a : ℝ) (k : ℕ) :
    |s ^ a * (-s) ^ (-(3 * k : ℤ))| = s ^ (a - 3 * k) := by
  rw [airyMod_rpow_mul_zpow hs, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos (Real.rpow_pos_of_pos hs _)]

/-- Each term `(2/3) a s^{3/2} (-s)^{-3(k+1)}` of the integrated expansion tends to `0`. -/
private lemma airyMod_tendsto_sigma_succ (k : ℕ) (a : ℝ) :
    Tendsto (fun s : ℝ => 2 / 3 * s ^ (3 / 2 : ℝ) * (-s) ^ (-(3 * ((k + 1 : ℕ) : ℤ))) * a)
      atTop (𝓝 0) := by
  have h : Tendsto (fun s : ℝ => 2 / 3 * a * (-1) ^ (k + 1) *
      s ^ ((3 / 2 : ℝ) - 3 * ((k + 1 : ℕ) : ℝ))) atTop (𝓝 0) := by
    have hq : (3 / 2 : ℝ) - 3 * ((k + 1 : ℕ) : ℝ) = -(3 * ((k + 1 : ℕ) : ℝ) - 3 / 2) := by ring
    rw [hq]
    simpa using (tendsto_rpow_neg_atTop (y := 3 * ((k + 1 : ℕ) : ℝ) - 3 / 2)
      (by push_cast; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])).const_mul
        (2 / 3 * a * (-1) ^ (k + 1))
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with s hs
  rw [mul_assoc (2 / 3 : ℝ) (s ^ (3 / 2 : ℝ)), airyMod_rpow_mul_zpow hs]; ring

/-- **Termwise integration of an expansion at `+∞`.** If `G' = g` and
`g(s) ~ ∑ c_k s^{1/2} (-s)^{-3k}`, then `G(s) - L ~ ∑ c_k/(1-2k) · (2/3) s^{3/2} (-s)^{-3k}` for a
constant `L = lim (G(s) - (2/3) c₀ s^{3/2})`. -/
theorem airyMod_expansion_of_deriv {G g : ℝ → ℝ} {c : ℕ → ℝ}
    (hG : ∀ s, 0 < s → HasDerivAt G (g s) s)
    (hg : ∀ N : ℕ, (fun s => g s - ∑ k ∈ Finset.range N, s ^ (1 / 2 : ℝ) * (-s) ^ (-(3 * k : ℤ)) * c k)
      =O[atTop] (fun s => s ^ (1 / 2 : ℝ) * (-s) ^ (-(3 * N : ℤ)))) :
    ∃ L, Tendsto (fun s => G s - 2 / 3 * s ^ (3 / 2 : ℝ) * c 0) atTop (𝓝 L) ∧
      ∀ N : ℕ, (fun s => G s - L - ∑ k ∈ Finset.range N,
        2 / 3 * s ^ (3 / 2 : ℝ) * (-s) ^ (-(3 * k : ℤ)) * (c k / (1 - 2 * k))) =O[atTop]
        (fun s => 2 / 3 * s ^ (3 / 2 : ℝ) * (-s) ^ (-(3 * N : ℤ))) := by
  set σ : ℕ → ℝ → ℝ := fun k s => 2 / 3 * s ^ (3 / 2 : ℝ) * (-s) ^ (-(3 * k : ℤ)) * (c k / (1 - 2 * k))
  set F : ℕ → ℝ → ℝ := fun N s => G s - ∑ k ∈ Finset.range N, σ k s
  have hF : ∀ N s, 0 < s → HasDerivAt (F N) (g s - ∑ k ∈ Finset.range N,
      s ^ (1 / 2 : ℝ) * (-s) ^ (-(3 * k : ℤ)) * c k) s := fun N s hs =>
    (hG s hs).sub (HasDerivAt.fun_sum fun k _ => airyMod_hasDerivAt_sigma hs k (c k))
  -- limits with explicit bounds for `N ≥ 1`
  have hlim : ∀ N : ℕ, 1 ≤ N → ∃ L K R, 0 < R ∧ Tendsto (F N) atTop (𝓝 L) ∧
      ∀ s, R ≤ s → |F N s - L| ≤ K * s ^ ((3 / 2 : ℝ) - 3 * N) / (-((3 / 2 : ℝ) - 3 * N)) := by
    intro N hN
    obtain ⟨K, hK⟩ := (hg N).bound
    obtain ⟨R, hR⟩ := eventually_atTop.mp hK
    have hp : (3 / 2 : ℝ) - 3 * N < 0 := by
      have : (1 : ℝ) ≤ N := by exact_mod_cast hN
      linarith
    obtain ⟨L, hL1, hL2⟩ := airyMod_tendsto_of_deriv_bound (F := F N) (R := max R 1) (K := K)
      (by positivity) hp (fun s hs => hF N s (by linarith [le_max_right R 1]))
      (fun s hs => by
        have hs0 : 0 < s := by linarith [le_max_right R 1]
        have := hR s (le_trans (le_max_left _ _) hs)
        rw [Real.norm_eq_abs, Real.norm_eq_abs, airyMod_abs_rpow_mul_zpow hs0] at this
        rwa [show (3 / 2 : ℝ) - 3 * N - 1 = 1 / 2 - 3 * N by ring])
    exact ⟨L, K, max R 1, by positivity, hL1, hL2⟩
  obtain ⟨L, K₁, R₁, hR₁, hL, hb₁⟩ := hlim 1 le_rfl
  have hF1 : F 1 = fun s => G s - 2 / 3 * s ^ (3 / 2 : ℝ) * c 0 := by
    funext s; simp [F, σ]
  have hσ0 : ∀ k, Tendsto (σ (k + 1)) atTop (𝓝 0) := fun k =>
    airyMod_tendsto_sigma_succ k _
  have hsame : ∀ N : ℕ, 1 ≤ N → Tendsto (F N) atTop (𝓝 L) := by
    intro N hN
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    have h : F (M + 1) = fun s => F 1 s - ∑ k ∈ Finset.range M, σ (k + 1) s := by
      funext s; simp only [F, Finset.sum_range_succ']; ring
    rw [h]
    simpa using hL.sub (tendsto_finsetSum _ fun k _ => hσ0 k)
  refine ⟨L, hF1 ▸ hL, fun N => ?_⟩
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · -- `G - L = (F 1 - L) + σ₀`
    simp only [Finset.range_zero, Finset.sum_empty, sub_zero, CharP.cast_eq_zero, mul_zero,
      neg_zero, zpow_zero, mul_one]
    have h1 : (fun s => F 1 s - L) =O[atTop] (fun s : ℝ => 2 / 3 * s ^ (3 / 2 : ℝ)) := by
      refine ((hL.sub_const L).isBigO_one ℝ).trans ?_
      refine IsBigO.of_bound (3 / 2) ?_
      filter_upwards [eventually_ge_atTop 1] with s hs
      rw [norm_one, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have : 1 ≤ s ^ (3 / 2 : ℝ) := Real.one_le_rpow hs (by norm_num)
      nlinarith
    have h2 : (fun s => 2 / 3 * s ^ (3 / 2 : ℝ) * c 0) =O[atTop] (fun s : ℝ => 2 / 3 * s ^ (3 / 2 : ℝ)) :=
      IsBigO.of_bound |c 0| (Eventually.of_forall fun s => by
        rw [norm_mul, Real.norm_eq_abs (c 0), mul_comm])
    refine (h1.add h2).congr' (Eventually.of_forall fun s => ?_) EventuallyEq.rfl
    simp [F, σ]
    ring
  · obtain ⟨L', K, R, hR, hL', hb⟩ := hlim N hN
    have hLL : L' = L := tendsto_nhds_unique hL' (hsame N hN)
    subst hLL
    refine IsBigO.of_bound (K * (3 / 2) / (-((3 / 2 : ℝ) - 3 * N))) ?_
    filter_upwards [eventually_ge_atTop R] with s hs
    have hs0 : 0 < s := hR.trans_le hs
    have hb' := hb s hs
    have e : G s - L' - ∑ k ∈ Finset.range N, σ k s = F N s - L' := by simp only [F]; ring
    rw [Real.norm_eq_abs, Real.norm_eq_abs, e, mul_assoc, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2 / 3),
      airyMod_abs_rpow_mul_zpow hs0]
    have : (0 : ℝ) < -((3 / 2 : ℝ) - 3 * N) := by
      have : (1 : ℝ) ≤ N := by exact_mod_cast hN
      linarith
    calc |F N s - L'| ≤ K * s ^ ((3 / 2 : ℝ) - 3 * N) / (-((3 / 2 : ℝ) - 3 * N)) := hb'
      _ = K * (3 / 2) / (-((3 / 2 : ℝ) - 3 * N)) * (2 / 3 * s ^ ((3 / 2 : ℝ) - 3 * N)) := by
        field_simp

/-- The reciprocal of the formal series `∑ c_k X^k` with `c₀ = 1` has coefficients
`airyReciprocalCoeff c`. -/
theorem airyMod_coeff_recip_mk {c : ℕ → ℝ} (hc : c 0 = 1) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk c)⁻¹ = airyReciprocalCoeff c n := by
  have h0 : PowerSeries.constantCoeff (PowerSeries.mk c) ≠ 0 := by
    simp [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hc]
  have key : PowerSeries.mk (airyReciprocalCoeff c) = (PowerSeries.mk c)⁻¹ := by
    rw [PowerSeries.eq_inv_iff_mul_eq_one h0]
    ext m
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    rcases m with _ | m
    · simp [airyReciprocalCoeff, hc]
    · rw [Finset.sum_range_succ]
      simp only [PowerSeries.coeff_mk, Nat.sub_self, hc, mul_one, PowerSeries.coeff_one,
        Nat.succ_ne_zero, ite_false]
      rw [airyReciprocalCoeff]
      rw [← Finset.sum_range_reflect]
      have : ∀ j ∈ Finset.range (m + 1), airyReciprocalCoeff c (m + 1 - 1 - j) * c (m + 1 - (m + 1 - 1 - j)) =
          c (j + 1) * airyReciprocalCoeff c (m - j) := by
        intro j hj
        have hj' := Finset.mem_range.mp hj
        rw [show m + 1 - 1 - j = m - j by omega, show m + 1 - (m - j) = j + 1 by omega, mul_comm]
      rw [Finset.sum_congr rfl this]
      ring
  rw [← key, PowerSeries.coeff_mk]

/-- Convert an expansion `F(x) ~ ∑ c_k p(x) x^{-3k}` at `-∞` to an asymptotic power series of
`F(-s)/p(-s)` in `w = (-s)^{-3}` at `+∞`. -/
theorem airyMod_powerSeries_of_expansion {F p : ℝ → ℝ} {c : ℕ → ℝ}
    (hF : HasAsymptoticExpansion atBot (fun k (x : ℝ) => p x * x ^ (-(3 * k : ℤ))) c F)
    (hp : ∀ x < 0, p x ≠ 0) :
    HasAsymptoticPowerSeries atTop (fun s : ℝ => (-s) ^ (-(3 : ℤ))) (PowerSeries.mk c)
      (fun s => F (-s) / p (-s)) := by
  intro N
  have h := ((hF N).comp_tendsto tendsto_neg_atTop_atBot).mul
    (isBigO_refl (fun s : ℝ => (p (-s))⁻¹) atTop)
  have hz : ∀ (s : ℝ) (k : ℕ), (-s) ^ (-(3 * k : ℤ)) = ((-s) ^ (-(3 : ℤ))) ^ k := fun s k => by
    rw [← zpow_natCast, ← zpow_mul]; congr 1
  refine h.congr' ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with s hs
    have hp0 := hp (-s) (by linarith)
    simp only [Function.comp_apply, smul_eq_mul, PowerSeries.coeff_mk]
    rw [sub_mul, Finset.sum_mul]
    simp only [hz]
    congr 1
    field_simp
  · filter_upwards [eventually_gt_atTop 0] with s hs
    have hp0 := hp (-s) (by linarith)
    simp only [Function.comp_apply]
    rw [hz]
    field_simp

/-- **Reciprocal expansion of an integrand.** If `F(x) ~ ∑ c_k p(x) x^{-3k}` at `-∞` with
`c₀ = 1` and `g(s) = s^{1/2} p(-s)/F(-s)`, then `g(s) ~ ∑ r_k s^{1/2} (-s)^{-3k}` with
`r = airyReciprocalCoeff c`. -/
theorem airyMod_integrand_expansion {F p g : ℝ → ℝ} {c : ℕ → ℝ}
    (hF : HasAsymptoticExpansion atBot (fun k (x : ℝ) => p x * x ^ (-(3 * k : ℤ))) c F)
    (hp : ∀ x < 0, p x ≠ 0) (hc : c 0 = 1)
    (hg : ∀ s, 0 < s → g s = s ^ (1 / 2 : ℝ) * (F (-s) / p (-s))⁻¹) (N : ℕ) :
    (fun s => g s - ∑ k ∈ Finset.range N, s ^ (1 / 2 : ℝ) * (-s) ^ (-(3 * k : ℤ)) *
      airyReciprocalCoeff c k) =O[atTop] (fun s => s ^ (1 / 2 : ℝ) * (-s) ^ (-(3 * N : ℤ))) := by
  have hw : Tendsto (fun s : ℝ => (-s) ^ (-(3 : ℤ))) atTop (𝓝 0) := by
    have : Tendsto (fun s : ℝ => -((s ^ 3)⁻¹)) atTop (𝓝 0) := by
      simpa using ((tendsto_pow_atTop (α := ℝ) (by norm_num : (3 : ℕ) ≠ 0)).inv_tendsto_atTop).neg
    refine this.congr fun s => ?_
    rw [zpow_neg, show (3 : ℤ) = ((3 : ℕ) : ℤ) by rfl, zpow_natCast, neg_pow]; ring_nf
  have h0 : PowerSeries.constantCoeff (PowerSeries.mk c) ≠ 0 := by
    simp [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hc]
  have hi := ((airyMod_powerSeries_of_expansion hF hp).recip hw h0) N
  have hz : ∀ (s : ℝ) (k : ℕ), (-s) ^ (-(3 * k : ℤ)) = ((-s) ^ (-(3 : ℤ))) ^ k := fun s k => by
    rw [← zpow_natCast, ← zpow_mul]; congr 1
  have h := (isBigO_refl (fun s : ℝ => s ^ (1 / 2 : ℝ)) atTop).mul hi
  refine h.congr' ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with s hs
    simp only [smul_eq_mul, airyMod_coeff_recip_mk hc, hg s hs]
    rw [mul_sub, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hz]; ring
  · filter_upwards with s
    rw [hz]

/-- As `x → -∞`, `M²(x) ∼ (1/(π(-x)^{1/2})) ∑ₖ aₖ x^{-3k}` with the coefficients
`airyModulusCoeff` (DLMF 9.8.20). -/
@[dlmf 9.8.E20]
theorem airyModulus_asymptotic :
    HasAsymptoticExpansion atBot (fun k (x : ℝ) => (-x) ^ (-1 / 2 : ℝ) / π * x ^ (-(3 * k : ℤ)))
      airyModulusCoeff (fun x => airyModulus x ^ 2) := by
  intro N
  refine IsBigO.of_bound |airyModulusCoeff N| ?_
  filter_upwards [eventually_lt_atBot 0] with x hx
  have h := (airyMod_sq_error_bound hx N).1
  simp only [smul_eq_mul, Real.norm_eq_abs]
  have e : ∑ n ∈ Finset.range N, (-x) ^ (-1 / 2 : ℝ) / π * x ^ (-(3 * n : ℤ)) * airyModulusCoeff n =
      (-x) ^ (-1 / 2 : ℝ) / π * airyModulusSum false N x := by
    simp only [airyModulusSum, Bool.false_eq_true, ite_false, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => by ring
  rw [e]
  calc _ ≤ _ := h
    _ = _ := by simp only [abs_mul]; ring

/-- As `x → -∞`, `N²(x) ∼ ((-x)^{1/2}/π) ∑ₖ bₖ x^{-3k}` with the coefficients
`airyDerivModulusCoeff` (DLMF 9.8.21). -/
@[dlmf 9.8.E21]
theorem airyDerivModulus_asymptotic :
    HasAsymptoticExpansion atBot (fun k (x : ℝ) => (-x) ^ (1 / 2 : ℝ) / π * x ^ (-(3 * k : ℤ)))
      airyDerivModulusCoeff (fun x => airyDerivModulus x ^ 2) := by
  have step : ∀ N : ℕ, (fun x => airyDerivModulus x ^ 2 - ∑ n ∈ Finset.range (N + 1),
      ((-x) ^ (1 / 2 : ℝ) / π * x ^ (-(3 * n : ℤ))) • airyDerivModulusCoeff n) =O[atBot]
      (fun x : ℝ => (-x) ^ (1 / 2 : ℝ) / π * x ^ (-(3 * (N + 1 : ℕ) : ℤ))) := fun N => by
    refine IsBigO.of_bound (|airyModulusCoeff (N + 1)| + π * ((π * Real.sqrt π)⁻¹ / 2 *
        (Real.Gamma ((3 * N + 2 : ℕ) + 1 / 2) / (12 ^ N * (Nat.factorial N : ℝ))))) ?_
    filter_upwards [eventually_lt_atBot 0] with x hx
    simp only [smul_eq_mul, Real.norm_eq_abs]
    exact airyMod_derivSq_error hx N
  intro N
  rcases N with _ | N
  · -- `N² = O(φ₀)` from the one-term bound
    have h1 := step 0
    have hφ : (fun x : ℝ => (-x) ^ (1 / 2 : ℝ) / π * x ^ (-(3 * (0 + 1 : ℕ) : ℤ))) =O[atBot]
        (fun x : ℝ => (-x) ^ (1 / 2 : ℝ) / π * x ^ (-(3 * (0 : ℕ) : ℤ))) := by
      refine IsBigO.of_bound 1 ?_
      filter_upwards [eventually_le_atBot (-1)] with x hx
      simp only [Nat.cast_zero, mul_zero, neg_zero, zpow_zero, mul_one, zero_add, Nat.cast_one,
        one_mul, Real.norm_eq_abs, abs_mul]
      have : |x ^ (-(3 : ℤ))| ≤ 1 := by
        rw [abs_zpow, zpow_neg]
        exact inv_le_one_of_one_le₀ (one_le_zpow₀ (by rw [abs_of_neg (by linarith)]; linarith)
          (by norm_num))
      have h0 : 0 ≤ |(-x) ^ (1 / 2 : ℝ) / π| := abs_nonneg _
      nlinarith
    have h0 : (fun x : ℝ => ∑ n ∈ Finset.range (0 + 1),
        ((-x) ^ (1 / 2 : ℝ) / π * x ^ (-(3 * n : ℤ))) • airyDerivModulusCoeff n) =O[atBot]
        (fun x : ℝ => (-x) ^ (1 / 2 : ℝ) / π * x ^ (-(3 * (0 : ℕ) : ℤ))) := by
      refine IsBigO.of_bound |airyDerivModulusCoeff 0| (Eventually.of_forall fun x => ?_)
      simp only [zero_add, Finset.range_one, Finset.sum_singleton, smul_eq_mul, Real.norm_eq_abs,
        abs_mul]
      push_cast
      ring_nf
      rfl
    simpa using (h1.trans hφ).add h0
  · simpa using step N

/-- Signed first-neglected-term bounds, DLMF §9.8(iv). -/
theorem airyModulus_error {x : ℝ} (hx : x < 0) {N : ℕ} (hN : 0 ≤ N) :
    |(airyModulus x ^ 2) - ((-x) ^ (-1 / 2 : ℝ) / π) * airyModulusSum false N x| ≤ |((-x) ^ (-1 / 2 : ℝ) / π) * airyModulusCoeff N * x ^ (-(3 * N : ℤ))| ∧
      0 ≤ ((airyModulus x ^ 2) - ((-x) ^ (-1 / 2 : ℝ) / π) * airyModulusSum false N x) * (((-x) ^ (-1 / 2 : ℝ) / π) * airyModulusCoeff N * x ^ (-(3 * N : ℤ))) :=
  airyMod_sq_error_bound hx N

/-- For `x < 0`, the error of the `θ` expansion after `N + 1` terms is bounded by, and has
the sign of, the first neglected term, DLMF §9.8(iv). -/
theorem airyPhase_error {x : ℝ} (hx : x < 0) {N : ℕ} (hN : 0 ≤ N) :
    |(airyPhase x - (π / 4)) - (2 / 3 * (-x) ^ (3 / 2 : ℝ)) * airyPhaseSum false (N + 1) x| ≤ |(2 / 3 * (-x) ^ (3 / 2 : ℝ)) * airyPhaseCoeff (N + 1) * x ^ (-(3 * (N + 1) : ℤ))| ∧
      0 ≤ ((airyPhase x - (π / 4)) - (2 / 3 * (-x) ^ (3 / 2 : ℝ)) * airyPhaseSum false (N + 1) x) * ((2 / 3 * (-x) ^ (3 / 2 : ℝ)) * airyPhaseCoeff (N + 1) * x ^ (-(3 * (N + 1) : ℤ))) := by
  sorry

/-- Signed first-neglected-term bounds, DLMF §9.8(iv). -/
theorem airyDerivModulus_error {x : ℝ} (hx : x < 0) {N : ℕ} (hN : 1 ≤ N) :
    |(airyDerivModulus x ^ 2) - ((-x) ^ (1 / 2 : ℝ) / π) * airyModulusSum true N x| ≤ |((-x) ^ (1 / 2 : ℝ) / π) * airyDerivModulusCoeff N * x ^ (-(3 * N : ℤ))| ∧
      0 ≤ ((airyDerivModulus x ^ 2) - ((-x) ^ (1 / 2 : ℝ) / π) * airyModulusSum true N x) * (((-x) ^ (1 / 2 : ℝ) / π) * airyDerivModulusCoeff N * x ^ (-(3 * N : ℤ))) := by
  obtain ⟨K, rfl⟩ : ∃ K, N = K + 1 := ⟨N - 1, by omega⟩
  obtain ⟨s, hs, rfl⟩ : ∃ s : ℝ, 0 < s ∧ x = -s := ⟨-x, by linarith, by ring⟩
  rw [neg_neg]
  have hπ := Real.pi_pos
  have hc : 0 < (π * Real.sqrt π)⁻¹ := by positivity
  rw [airyMod_derivSq_error_integral hs K, ← airyMod_derivMod_term_identity K hs]
  set J := ∫ t in Ioi (0 : ℝ), Real.exp (-s * t) * t ^ (-(1 / 2) : ℝ) *
    (t ^ 2 * airyMod_rem K (t ^ 3 / 12) / 4 - airyMod_rem (K + 1) (t ^ 3 / 12) / (2 * t))
  set c₀ : ℝ := (6 * K + 7) / (24 * 12 ^ K * Nat.factorial (K + 1))
  set G := Real.Gamma ((3 * K + 2 : ℕ) + 1 / 2) * s ^ (-(((3 * K + 2 : ℕ) : ℝ) + 1 / 2)) * c₀
  have hI := airyMod_mom_integral (3 * K + 2) hs
  have hJ1 : 0 ≤ (-1) ^ K * J := by
    rw [← integral_const_mul]
    exact setIntegral_nonneg measurableSet_Ioi fun t (ht : 0 < t) =>
      (airyMod_derivErr_pointwise s K ht).1
  have hJ2 : (-1) ^ K * J ≤ G := by
    rw [show G = ∫ t in Ioi (0 : ℝ), Real.exp (-s * t) *
        t ^ ((((3 * K + 2 : ℕ) : ℝ) + 1 / 2) - 1) * c₀ by
      rw [integral_mul_const, hI.2], ← integral_const_mul]
    exact setIntegral_mono_on ((airyMod_derivErr_integrable s hs K).const_mul _)
      (hI.1.mul_const _) measurableSet_Ioi fun t (ht : 0 < t) =>
        (airyMod_derivErr_pointwise s K ht).2
  have hsq : ((-1 : ℝ) ^ K) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hab : |(-1 : ℝ) ^ K| = 1 := by simp
  have hG : 0 ≤ G := hJ1.trans hJ2
  constructor
  · rw [show (π * Real.sqrt π)⁻¹ * J = (-1) ^ K * ((π * Real.sqrt π)⁻¹ * ((-1) ^ K * J)) by
      rw [← mul_assoc ((-1 : ℝ) ^ K), mul_comm ((-1 : ℝ) ^ K), mul_assoc, ← mul_assoc ((-1 : ℝ) ^ K),
        ← pow_two, hsq, one_mul],
      show (π * Real.sqrt π)⁻¹ * G * (-1) ^ K = (-1) ^ K * ((π * Real.sqrt π)⁻¹ * G) by ring,
      abs_mul ((-1 : ℝ) ^ K), abs_mul ((-1 : ℝ) ^ K), hab, one_mul, one_mul,
      abs_of_nonneg (mul_nonneg hc.le hJ1), abs_of_nonneg (mul_nonneg hc.le hG)]
    exact mul_le_mul_of_nonneg_left hJ2 hc.le
  · have : (π * Real.sqrt π)⁻¹ * J * ((π * Real.sqrt π)⁻¹ * G * (-1) ^ K) =
        ((π * Real.sqrt π)⁻¹ * ((-1) ^ K * J)) * ((π * Real.sqrt π)⁻¹ * G) := by ring
    rw [this]
    exact mul_nonneg (mul_nonneg hc.le hJ1) (mul_nonneg hc.le hG)

/-- For `x < 0`, the error of the `φ` expansion after `N + 1` terms is bounded by, and has
the sign of, the first neglected term, DLMF §9.8(iv). -/
theorem airyDerivPhase_error {x : ℝ} (hx : x < 0) {N : ℕ} (hN : 0 ≤ N) :
    |(airyDerivPhase x - (-π / 4)) - (2 / 3 * (-x) ^ (3 / 2 : ℝ)) * airyPhaseSum true (N + 1) x| ≤ |(2 / 3 * (-x) ^ (3 / 2 : ℝ)) * airyDerivPhaseCoeff (N + 1) * x ^ (-(3 * (N + 1) : ℤ))| ∧
      0 ≤ ((airyDerivPhase x - (-π / 4)) - (2 / 3 * (-x) ^ (3 / 2 : ℝ)) * airyPhaseSum true (N + 1) x) * ((2 / 3 * (-x) ^ (3 / 2 : ℝ)) * airyDerivPhaseCoeff (N + 1) * x ^ (-(3 * (N + 1) : ℤ))) := by
  sorry

end DLMF.Airy
end
