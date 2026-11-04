/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Zeta.HurwitzIntegrals

/-!
# The loop integral for the Hurwitz zeta function

The loop-integral representation DLMF 25.11.30 of `ζ(s, a)`, over the keyhole
`DLMF.Zeta.keyholeLoopIntegral` of any radius `0 < δ < 2π`.

## Main results

* `hurwitzZetaComplex_eq_loop_integral`: the loop integral DLMF 25.11.30.

## Implementation notes

For `Re s > 1` the keyhole integral reduces to the Laplace-type integral 25.11.25
(`Complex.keyholeIntegral_eq_mul_integral_Ioi`); both sides continue analytically to
`s ≠ 1, 2, 3, …` (`eq_Gamma_one_sub_mul_of_eq_sin_mul_Gamma`).
-/

@[expose] public section

open Complex Filter Set MeasureTheory
open scoped Real Topology

noncomputable section

namespace DLMF.Zeta

/-- The kernel `e^{az}/(1 - e^z)` of DLMF 25.11.30: holomorphy on `0 < |z| < 2π`, a pole of
order at most one at `0`, continuity on the circle and the edges, and exponential decay along the
negative real axis. -/
private lemma hurwitzLoopKernel_props {a : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hδ' : δ < 2 * π) :
    (∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < 2 * π →
      DifferentiableAt ℂ (fun z => cexp (a * z) / (1 - cexp z)) z) ∧
    (∃ M r : ℝ, 0 < r ∧ ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < r →
      ‖z * (cexp (a * z) / (1 - cexp z))‖ ≤ M) ∧
    ContinuousOn (fun z => cexp (a * z) / (1 - cexp z)) (Metric.sphere 0 δ) ∧
    ContinuousOn (fun x : ℝ => cexp (a * -(x : ℂ)) / (1 - cexp (-(x : ℂ)))) (Ioi δ) ∧
    ∀ x : ℝ, δ < x → ‖cexp (a * -(x : ℂ)) / (1 - cexp (-(x : ℂ)))‖ ≤
      (1 - Real.exp (-δ))⁻¹ * Real.exp (-a.re * x) := by
  have hne : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < 2 * π → 1 - cexp z ≠ 0 := fun z h0 h =>
    sub_ne_zero.mpr (Complex.exp_ne_one_of_norm_lt (norm_pos_iff.mp h0) h).symm
  have hd : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < 2 * π →
      DifferentiableAt ℂ (fun z => cexp (a * z) / (1 - cexp z)) z := fun z h0 h =>
    (((differentiableAt_const a).mul differentiableAt_id).cexp).div
      ((differentiableAt_const 1).sub differentiableAt_exp) (hne z h0 h)
  have hx1 : ∀ x : ℝ, 0 < x → 0 < 1 - Real.exp (-x) := fun x hx => by
    have := Real.exp_lt_exp.mpr (show -x < 0 by linarith); rw [Real.exp_zero] at this; linarith
  have hnx : ∀ x : ℝ, 0 < x → ‖1 - cexp (-(x : ℂ))‖ = 1 - Real.exp (-x) := fun x hx => by
    rw [show 1 - cexp (-(x : ℂ)) = ((1 - Real.exp (-x) : ℝ) : ℂ) by push_cast; rfl, norm_real,
      Real.norm_of_nonneg (hx1 x hx).le]
  refine ⟨hd, ⟨2 * Real.exp ‖a‖, 1 / 2, by norm_num, fun z h0 h => ?_⟩, fun z hz => ?_,
    fun x hx => ?_, fun x hx => ?_⟩
  · have h1 := Complex.half_norm_le_norm_exp_sub_one h.le
    have h2 : ‖cexp (a * z)‖ ≤ Real.exp ‖a‖ := by
      rw [norm_exp]
      refine Real.exp_le_exp.mpr ((re_le_norm _).trans ?_)
      rw [norm_mul]
      nlinarith [norm_nonneg a]
    rw [norm_mul, norm_div, norm_sub_rev, mul_div_assoc', div_le_iff₀ (by linarith)]
    nlinarith [norm_nonneg (cexp (a * z)), Real.exp_pos ‖a‖]
  · rw [mem_sphere_zero_iff_norm] at hz
    exact (hd z (by rw [hz]; exact hδ) (by rw [hz]; exact hδ')).continuousAt.continuousWithinAt
  · have hx0 : (0 : ℝ) < x := hδ.trans hx
    refine (ContinuousAt.div (by fun_prop) (by fun_prop) ?_).continuousWithinAt
    rw [← norm_ne_zero_iff, hnx x hx0]
    exact (hx1 x hx0).ne'
  · have hx0 : (0 : ℝ) < x := hδ.trans hx
    have hd1 := hx1 δ hδ
    rw [norm_div, hnx x hx0, norm_exp, show (a * -(x : ℂ)).re = -a.re * x by simp,
      div_le_iff₀ (hx1 x hx0)]
    have hle : Real.exp (-x) ≤ Real.exp (-δ) := Real.exp_le_exp.mpr (by linarith)
    have hE := Real.exp_pos (-a.re * x)
    have key : 1 ≤ (1 - Real.exp (-δ))⁻¹ * (1 - Real.exp (-x)) := by
      rw [le_inv_mul_iff₀ hd1]; linarith
    calc Real.exp (-a.re * x) = Real.exp (-a.re * x) * 1 := (mul_one _).symm
      _ ≤ Real.exp (-a.re * x) * ((1 - Real.exp (-δ))⁻¹ * (1 - Real.exp (-x))) := by gcongr
      _ = _ := by ring

/-- Integrability of the Laplace-type integrand of 25.11.25 for `Re s > 1`, `Re a > 0`. -/
private lemma integrableOn_cpow_mul_hurwitzKernel {s a : ℂ} (hs : 1 < s.re) (ha : 0 < a.re) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 1) * (cexp (a * -(x : ℂ)) /
      (1 - cexp (-(x : ℂ))))) (Ioi 0) := by
  have h1 := integrableOn_rpow_mul_exp_neg (σ := s.re) (by linarith) ha
  have h2 := integrableOn_rpow_mul_exp_neg (σ := s.re - 1) (by linarith) ha
  refine (h1.add h2).mono' (ContinuousOn.aestronglyMeasurable (fun x hx => ?_) measurableSet_Ioi)
    ?_
  · have hx0 : (0 : ℝ) < x := hx
    refine ContinuousAt.continuousWithinAt (ContinuousAt.mul
      (continuousAt_ofReal_cpow_const _ _ (Or.inr hx0.ne')) (ContinuousAt.div (by fun_prop)
      (by fun_prop) ?_))
    refine sub_ne_zero.mpr fun h => ?_
    have := congrArg Complex.re h
    rw [← ofReal_neg, ← ofReal_exp, ofReal_re, one_re] at this
    have := Real.exp_lt_exp.mpr (show -x < 0 by linarith)
    rw [Real.exp_zero] at this; linarith
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : (0 : ℝ) < x := hx
    have hex : Real.exp (-x) < 1 := by
      have := Real.exp_lt_exp.mpr (show -x < 0 by linarith); rwa [Real.exp_zero] at this
    have hd : 0 < 1 - Real.exp (-x) := by linarith
    have hnx : ‖1 - cexp (-(x : ℂ))‖ = 1 - Real.exp (-x) := by
      rw [show 1 - cexp (-(x : ℂ)) = ((1 - Real.exp (-x) : ℝ) : ℂ) by push_cast; rfl,
        norm_real, Real.norm_of_nonneg hd.le]
    -- `1/(1 - e^{-x}) ≤ 1 + 1/x`
    have hk : 1 / (1 - Real.exp (-x)) ≤ 1 + 1 / x := by
      rw [div_le_iff₀ hd]
      have h3 : (1 + x) * Real.exp (-x) ≤ 1 := by
        have := Real.add_one_le_exp x
        have he : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
        nlinarith [Real.exp_pos (-x)]
      field_simp
      nlinarith
    rw [norm_mul, norm_div, norm_cpow_eq_rpow_re_of_pos hx0, norm_exp, hnx,
      show (a * -(x : ℂ)).re = -(a.re * x) by simp, sub_re, one_re]
    simp only [Pi.add_apply]
    have hE := Real.exp_pos (-(a.re * x))
    have hp := Real.rpow_nonneg hx0.le (s.re - 1)
    have hsplit : x ^ (s.re - 1 - 1) = x ^ (s.re - 1) / x := by
      rw [Real.rpow_sub hx0, Real.rpow_one]
    rw [hsplit]
    calc x ^ (s.re - 1) * (Real.exp (-(a.re * x)) / (1 - Real.exp (-x)))
        = x ^ (s.re - 1) * Real.exp (-(a.re * x)) * (1 / (1 - Real.exp (-x))) := by ring
      _ ≤ x ^ (s.re - 1) * Real.exp (-(a.re * x)) * (1 + 1 / x) := by gcongr
      _ = _ := by ring

/-- **Loop integral** (DLMF 25.11.30): for `s ≠ 1, 2, 3, …` and `Re a > 0`,
`ζ(s, a) = (Γ(1-s)/(2πi)) ∫_{-∞}^{(0+)} e^{az} z^{s-1}/(1 - e^z) dz`, the loop encircling the origin
once positively without enclosing `±2πi, ±4πi, …`. As for 25.5.20 (`riemannZeta_eq_loop_integral`)
the loop is the keyhole `DLMF.Zeta.keyholeLoopIntegral` of radius `0 < δ < 2π`. -/
@[dlmf 25.11.E30]
theorem hurwitzZetaComplex_eq_loop_integral {s a : ℂ} (hs : ∀ n : ℕ, s ≠ n + 1) (ha : 0 < a.re)
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 2 * π) :
    hurwitzZetaComplex s a = Gamma (1 - s) / (2 * π * I) *
      keyholeLoopIntegral (fun z => cexp (a * z) / (1 - cexp z)) (s - 1) δ := by
  obtain ⟨hd, hbd, hcirc, hedge, hdec⟩ := hurwitzLoopKernel_props hδ hδ'
  have han : ∀ n : ℕ, a + n ≠ 0 := fun n h => by
    have := congrArg Complex.re h; simp at this; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  refine eq_Gamma_one_sub_mul_of_eq_sin_mul_Gamma (Φ := fun t => hurwitzZetaComplex t a)
    (k := fun s => keyholeLoopIntegral (fun z => cexp (a * z) / (1 - cexp z)) (s - 1) δ)
    (fun t ht => (differentiableAt_hurwitzZetaComplex_of_add_natCast_ne_zero' ht
      han).differentiableWithinAt) ?_ (fun t ht => ?_) hs
  · exact (Complex.differentiable_keyholeIntegral hδ ha hcirc hedge hdec).comp
      (differentiable_id.sub_const 1)
  · have hta : 0 < (t - 1).re := by simp; linarith
    simp only [keyholeLoopIntegral]
    rw [Complex.keyholeIntegral_eq_mul_integral_Ioi hta hδ hδ' hd
      (integrableOn_cpow_mul_hurwitzKernel ht ha) hbd, hurwitzZetaComplex_eq_integral ht ha]
    have hG : Gamma t ≠ 0 := Gamma_ne_zero_of_re_pos (by linarith)
    have hI : (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (t - 1) * (cexp (a * -(x : ℂ)) /
        (1 - cexp (-(x : ℂ))))) = ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (t - 1) * cexp (-(a * x)) /
        (1 - cexp (-(x : ℂ))) := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [mul_neg, mul_div_assoc]
    rw [hI]
    field_simp

end DLMF.Zeta
