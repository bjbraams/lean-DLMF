/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Complex.ParametricHolomorphy
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import TauCeti.MeasureTheory.Integral.ExpDecay

/-!
# Holomorphic Fourier–Laplace integrals in a horizontal strip

A measurable function bounded by a polynomial times `exp(-c |y|)` has a Fourier–Laplace
integral `∫ B(y) exp((σ + iy) w) dy` holomorphic in the strip `|Im w| < c`. Exponential
bounds on each smaller rectangle provide local domination. Polynomial times two-sided
exponential decay is integrable on the real line.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory
open scoped Real Topology

namespace Real

/-- Polynomial times `e^{-c|y|}` is integrable on `ℝ`. -/
theorem integrable_one_add_abs_pow_mul_exp_neg {c : ℝ} (hc : 0 < c) (K : ℕ) :
    Integrable (fun y : ℝ => (1 + |y|) ^ K * Real.exp (-(c * |y|))) := by
  -- `(1+t)^K e^{-ct/2}` is bounded on `t ≥ 0`
  have hlim : Tendsto (fun t : ℝ => (1 + t) ^ K * Real.exp (-(c / 2 * t))) atTop (𝓝 0) := by
    have hu : Tendsto (fun t : ℝ => c / 2 * (1 + t)) atTop atTop :=
      (tendsto_atTop_add_const_left _ 1 tendsto_id).const_mul_atTop (half_pos hc)
    have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero K).comp hu
    have h' := h.const_mul ((2 / c) ^ K * Real.exp (c / 2))
    rw [mul_zero] at h'
    refine h'.congr' (Eventually.of_forall fun t => ?_)
    simp only [Function.comp_apply]
    have hc' : c ≠ 0 := hc.ne'
    rw [show -(c / 2 * (1 + t)) = -(c / 2 * t) + -(c / 2) by ring, Real.exp_add, mul_pow]
    have h1 : Real.exp (c / 2) * Real.exp (-(c / 2)) = 1 := by rw [← Real.exp_add]; simp
    have h2 : (2 / c) ^ K * (c / 2) ^ K = 1 := by rw [← mul_pow]; field_simp; simp
    linear_combination ((1 + t) ^ K * Real.exp (-(c / 2 * t))) *
      ((2 / c) ^ K * (c / 2) ^ K * h1 + h2)
  obtain ⟨M, hM⟩ := (hlim.eventually (gt_mem_nhds one_pos)).exists_forall_of_atTop
  have hbd : ∃ D : ℝ, ∀ t : ℝ, 0 ≤ t → (1 + t) ^ K * Real.exp (-(c / 2 * t)) ≤ D := by
    obtain ⟨D, hD⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := max M 0)).exists_bound_of_continuousOn
      (f := fun t : ℝ => (1 + t) ^ K * Real.exp (-(c / 2 * t))) (by fun_prop)
    refine ⟨max D 1, fun t ht => ?_⟩
    by_cases htM : t ≤ max M 0
    · have := hD t ⟨ht, htM⟩
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at this
      exact this.trans (le_max_left _ _)
    · push Not at htM
      exact (hM t (le_of_lt (lt_of_le_of_lt (le_max_left _ _) htM))).le.trans (le_max_right _ _)
  obtain ⟨D, hD⟩ := hbd
  refine ((TauCeti.integrable_exp_neg_mul_abs (half_pos hc)).const_mul D).mono'
    (by fun_prop) (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h := hD |y| (abs_nonneg y)
  have he : Real.exp (-(c * |y|)) = Real.exp (-(c / 2 * |y|)) * Real.exp (-(c / 2 * |y|)) := by
    rw [← Real.exp_add]; ring_nf
  rw [he, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right h (Real.exp_pos _).le

end Real

namespace Complex

/-- Exponential decay of a coefficient bounds its Fourier–Laplace kernel on any rectangle. -/
theorem norm_mul_exp_le_of_exp_decay {B : ℝ → ℂ} {C c : ℝ} {K : ℕ}
    (hC : 0 ≤ C) (hB : ∀ y, ‖B y‖ ≤ C * (1 + |y|) ^ K * Real.exp (-(c * |y|)))
    (σ : ℝ) {w : ℂ} {R θ : ℝ} (hR : |w.re| ≤ R) (hθ : |w.im| ≤ θ) (y : ℝ) :
    ‖B y * exp (((σ : ℂ) + I * y) * w)‖ ≤
      C * Real.exp (|σ| * R) * ((1 + |y|) ^ K * Real.exp (-((c - θ) * |y|))) := by
  have hre : (((σ : ℂ) + I * y) * w).re = σ * w.re - y * w.im := by simp
  have hp : σ * w.re ≤ |σ| * R :=
    (le_abs_self (σ * w.re)).trans (by rw [abs_mul]; gcongr)
  have hm : -(y * w.im) ≤ θ * |y| := by
    calc
      _ ≤ |y * w.im| := neg_le_abs _
      _ = |w.im| * |y| := by rw [abs_mul, mul_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_right hθ (abs_nonneg y)
  rw [norm_mul, norm_exp]
  calc
    _ ≤ (C * (1 + |y|) ^ K * Real.exp (-(c * |y|))) *
        Real.exp (|σ| * R + θ * |y|) := by
      exact mul_le_mul (hB y) (Real.exp_le_exp.mpr (by rw [hre]; linarith))
        (Real.exp_pos _).le (by positivity)
    _ = _ := by
      rw [Real.exp_add, ← mul_assoc, show -((c - θ) * |y|) =
        -(c * |y|) + θ * |y| by ring, Real.exp_add]
      ring

/-- A Fourier–Laplace integral is absolutely convergent strictly inside the decay strip. -/
theorem integrable_mul_exp_of_exp_decay {B : ℝ → ℂ}
    (hB : AEStronglyMeasurable B) {C c : ℝ} {K : ℕ}
    (hbound : ∀ y, ‖B y‖ ≤ C * (1 + |y|) ^ K * Real.exp (-(c * |y|)))
    (σ : ℝ) {w : ℂ} (hw : |w.im| < c) :
    Integrable (fun y : ℝ => B y * exp (((σ : ℂ) + I * y) * w)) := by
  have hC : 0 ≤ C := (norm_nonneg (B 0)).trans (by simpa using hbound 0)
  refine ((Real.integrable_one_add_abs_pow_mul_exp_neg (sub_pos.mpr hw) K).const_mul
    (C * Real.exp (|σ| * |w.re|))).mono' ?_ ?_
  · exact hB.mul (Continuous.aestronglyMeasurable (by fun_prop))
  · exact Eventually.of_forall fun y => norm_mul_exp_le_of_exp_decay hC hbound σ le_rfl le_rfl y

/-- The Fourier–Laplace integral of an exponentially decaying coefficient is holomorphic
on the corresponding horizontal strip. -/
theorem differentiableOn_integral_mul_exp_of_exp_decay {B : ℝ → ℂ}
    (hB : AEStronglyMeasurable B) {C c : ℝ} {K : ℕ}
    (hbound : ∀ y, ‖B y‖ ≤ C * (1 + |y|) ^ K * Real.exp (-(c * |y|))) (σ : ℝ) :
    DifferentiableOn ℂ (fun w : ℂ => ∫ y : ℝ, B y * exp (((σ : ℂ) + I * y) * w))
      {w : ℂ | |w.im| < c} := by
  have hC : 0 ≤ C := (norm_nonneg (B 0)).trans (by simpa using hbound 0)
  refine differentiableOn_integral_of_locally_dominated
    (isOpen_lt (continuous_abs.comp continuous_im) continuous_const) ?_ ?_ ?_
  · intro w _
    exact hB.mul (Continuous.aestronglyMeasurable (by fun_prop))
  · exact Eventually.of_forall fun y => by fun_prop
  · intro w hw
    change |w.im| < c at hw
    let R := |w.re| + 1
    let θ := (c + |w.im|) / 2
    have hθ : |w.im| < θ := by dsimp [θ]; linarith
    have hc : 0 < c - θ := by dsimp [θ]; linarith
    let V : Set ℂ := {v | |v.re| < R ∧ |v.im| < θ}
    have hV : V ∈ 𝓝 w := by
      apply ((isOpen_lt (continuous_abs.comp continuous_re) continuous_const).inter
        (isOpen_lt (continuous_abs.comp continuous_im) continuous_const)).mem_nhds
      exact ⟨by dsimp [R]; linarith, hθ⟩
    refine ⟨V, hV, fun y => C * Real.exp (|σ| * R) *
      ((1 + |y|) ^ K * Real.exp (-((c - θ) * |y|))),
      (Real.integrable_one_add_abs_pow_mul_exp_neg hc K).const_mul _, ?_⟩
    exact Eventually.of_forall fun y v hv =>
      norm_mul_exp_le_of_exp_decay hC hbound σ hv.1.le hv.2.le y

/-- Holomorphic functions on a horizontal strip that agree at every negative real point
agree throughout the strip. -/
theorem eqOn_horizontalStrip_of_eq_ofReal_neg {f g : ℂ → ℂ} {c : ℝ} (hc : 0 < c)
    (hf : DifferentiableOn ℂ f {w : ℂ | |w.im| < c})
    (hg : DifferentiableOn ℂ g {w : ℂ | |w.im| < c})
    (h : ∀ x : ℝ, x < 0 → f x = g x) {w : ℂ} (hw : |w.im| < c) : f w = g w := by
  have hU : IsOpen {w : ℂ | |w.im| < c} :=
    isOpen_lt (continuous_abs.comp continuous_im) continuous_const
  have hconv : Convex ℝ {w : ℂ | |w.im| < c} := by
    have he : {w : ℂ | |w.im| < c} = {w : ℂ | -c < w.im ∧ w.im < c} := by
      ext z
      exact (abs_lt : |z.im| < c ↔ -c < z.im ∧ z.im < c)
    rw [he]
    exact (convex_halfSpace_im_gt (-c)).inter (convex_halfSpace_im_lt c)
  have h0 : (-1 : ℂ) ∈ {w : ℂ | |w.im| < c} := by simpa using hc
  refine (hf.analyticOnNhd hU).eqOn_of_preconnected_of_frequently_eq (hg.analyticOnNhd hU)
    hconv.isPreconnected h0 ?_ hw
  have hev : ∀ᶠ x : ℝ in 𝓝[≠] (-1), f x = g x := by
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (-1 : ℝ) < 0))] with x hx
    exact h x hx
  have ht : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] (-1)) (𝓝[≠] ((-1 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin
      (fun x hx => Complex.ofReal_injective.ne hx)
  simpa only [Complex.ofReal_neg, Complex.ofReal_one] using
    (ht.frequently (p := fun z : ℂ => f z = g z) hev.frequently)

end Complex
