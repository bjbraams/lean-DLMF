/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import DLMF.Bessel.SecondKind
public import DLMFMathlib.Analysis.Complex.ParametricHolomorphy

/-!
# Integral representations of `K_ν` (DLMF 10.32.9, 10.32.10)

For every complex order `ν` and `Re z > 0`,

`K_ν(z) = ½ ∫_ℝ e^{-z cosh t + νt} dt = ∫₀^∞ e^{-z cosh t} cosh(νt) dt` (DLMF 10.32.9),

and for `|ph z| < π/4`,

`K_ν(z) = ½ (z/2)^ν ∫₀^∞ e^{-t - z²/(4t)} t^{-ν-1} dt` (DLMF 10.32.10).

The proof does not use any Laplace-type representation of `K_ν`; this module sits below the
Tricomi integral representations (`DLMF.Confluent.IntegralRepresentations`), which may import it.

* The moments `Ψ_j(ν, z) = ∫ cosh^j t e^{-z cosh t + νt} dt` are holomorphic in `z` and `ν`, with
  `∂_z Ψ_j = -Ψ_{j+1}`; an integration by parts shows that `Φ = Ψ₀` solves the modified Bessel
  equation.
* For each solution `g`, the Wronskian combination `z (Φ g' - Φ' g)` is constant on the right
  half-plane; with `W{K_ν, I_ν} = 1/z` this gives `Φ = A(ν) K_ν - B(ν) I_ν`.
* The shift `t ↦ t - log(x/2)` and `v = e^t` turn `Φ` into Schläfli's form, whose limit as
  `x → 0⁺` gives `A(ν) = 2` for `Re ν > 0`; `A` is entire, hence `A ≡ 2`.
* The symmetry `Φ_{-ν} = Φ_ν`, `K_{-ν} = K_ν`, and the Wronskian of `I_{±ν}` give `B(ν) = 0` for
  `ν ∉ ℤ`; integer orders follow by continuity in `ν`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

namespace DLMF.Bessel

/-- The kernel `exp(-z cosh t + ν t)` of the integral `K_ν(z) = ½ ∫_ℝ e^{-z cosh t + νt} dt`. -/
def besselKKernel (ν z : ℂ) (t : ℝ) : ℂ := exp (-(z * (Real.cosh t : ℂ)) + ν * t)

lemma norm_besselKKernel (ν z : ℂ) (t : ℝ) :
    ‖besselKKernel ν z t‖ = Real.exp (-(z.re * Real.cosh t) + ν.re * t) := by
  simp [besselKKernel, Complex.norm_exp]

lemma continuous_besselKKernel (ν z : ℂ) : Continuous (besselKKernel ν z) := by
  unfold besselKKernel; fun_prop

lemma kInt_exp_abs_div_two_le_cosh (t : ℝ) : Real.exp |t| / 2 ≤ Real.cosh t := by
  rw [← Real.cosh_abs, Real.cosh_eq]
  linarith [Real.exp_pos (-|t|)]

lemma kInt_cosh_le_exp_abs (t : ℝ) : Real.cosh t ≤ Real.exp |t| := by
  rw [← Real.cosh_abs, Real.cosh_eq]
  have : Real.exp (-|t|) ≤ Real.exp |t| := Real.exp_le_exp.mpr (by linarith [abs_nonneg t])
  linarith

lemma kInt_sq_div_four_le_cosh (t : ℝ) : t ^ 2 / 4 ≤ Real.cosh t := by
  have h := Real.quadratic_le_exp_of_nonneg (abs_nonneg t)
  have := kInt_exp_abs_div_two_le_cosh t
  have h2 : |t| ^ 2 = t ^ 2 := sq_abs t
  nlinarith [abs_nonneg t]

/-- The Gaussian majorant of the kernel. -/
lemma kInt_exp_neg_mul_cosh_add_le {c M : ℝ} (hc : 0 < c) (t : ℝ) :
    Real.exp (-(c * Real.cosh t) + M * |t|) ≤
      Real.exp (2 * M ^ 2 / c) * Real.exp (-(c / 8) * t ^ 2) := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have h1 := kInt_sq_div_four_le_cosh t
  have h2 : M * |t| ≤ c / 8 * t ^ 2 + 2 * M ^ 2 / c := by
    have h3 : 0 ≤ (c / 8) * (|t| - 4 * M / c) ^ 2 := by positivity
    have h4 : |t| ^ 2 = t ^ 2 := sq_abs t
    have : (c / 8) * (|t| - 4 * M / c) ^ 2 = c / 8 * t ^ 2 + 2 * M ^ 2 / c - M * |t| := by
      field_simp
      rw [← h4]
      ring
    linarith
  nlinarith

lemma kInt_integrable_exp_neg_mul_cosh_add {c M : ℝ} (hc : 0 < c) :
    Integrable (fun t : ℝ => Real.exp (-(c * Real.cosh t) + M * |t|)) := by
  refine ((integrable_exp_neg_mul_sq (by positivity : 0 < c / 8)).const_mul
    (Real.exp (2 * M ^ 2 / c))).mono' (by fun_prop) (Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  simpa [neg_mul] using kInt_exp_neg_mul_cosh_add_le (M := M) hc t

/-- Uniform bound for `cosh^j t · e^{-z cosh t + νt}`. -/
lemma norm_cosh_pow_mul_besselKKernel_le {ν z : ℂ} {c M : ℝ} (hz : c ≤ z.re)
    (hν : |ν.re| ≤ M) (j : ℕ) (t : ℝ) :
    ‖(Real.cosh t : ℂ) ^ j * besselKKernel ν z t‖ ≤
      Real.exp (-(c * Real.cosh t) + (M + j) * |t|) := by
  rw [norm_mul, norm_pow, norm_besselKKernel, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.cosh_pos t)]
  have hc1 : Real.cosh t ^ j ≤ Real.exp (j * |t|) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.cosh_pos t).le (kInt_cosh_le_exp_abs t) j
  have hc2 : Real.exp (-(z.re * Real.cosh t) + ν.re * t) ≤
      Real.exp (-(c * Real.cosh t) + M * |t|) := by
    refine Real.exp_le_exp.mpr ?_
    have h1 : c * Real.cosh t ≤ z.re * Real.cosh t :=
      mul_le_mul_of_nonneg_right hz (Real.cosh_pos t).le
    have h2 : ν.re * t ≤ M * |t| := by
      calc ν.re * t ≤ |ν.re * t| := le_abs_self _
        _ = |ν.re| * |t| := abs_mul _ _
        _ ≤ M * |t| := mul_le_mul_of_nonneg_right hν (abs_nonneg t)
    linarith
  calc Real.cosh t ^ j * Real.exp (-(z.re * Real.cosh t) + ν.re * t)
      ≤ Real.exp (j * |t|) * Real.exp (-(c * Real.cosh t) + M * |t|) :=
        mul_le_mul hc1 hc2 (Real.exp_pos _).le (Real.exp_pos _).le
    _ = Real.exp (-(c * Real.cosh t) + (M + j) * |t|) := by rw [← Real.exp_add]; ring_nf

/-- The moments `Ψ_j(ν, z) = ∫_ℝ cosh^j t · e^{-z cosh t + νt} dt`. -/
def besselKMoment (j : ℕ) (ν z : ℂ) : ℂ := ∫ t : ℝ, (Real.cosh t : ℂ) ^ j * besselKKernel ν z t

lemma integrable_cosh_pow_mul_besselKKernel {ν z : ℂ} (hz : 0 < z.re) (j : ℕ) :
    Integrable (fun t : ℝ => (Real.cosh t : ℂ) ^ j * besselKKernel ν z t) :=
  (kInt_integrable_exp_neg_mul_cosh_add (M := |ν.re| + j) hz).mono'
    (by unfold besselKKernel; fun_prop)
    (Eventually.of_forall fun t => norm_cosh_pow_mul_besselKKernel_le le_rfl le_rfl j t)

lemma integrable_besselKKernel {ν z : ℂ} (hz : 0 < z.re) :
    Integrable (besselKKernel ν z) := by
  simpa using integrable_cosh_pow_mul_besselKKernel (ν := ν) hz 0

/-- `∂_z Ψ_j = -Ψ_{j+1}` on the right half-plane. -/
lemma hasDerivAt_besselKMoment (j : ℕ) (ν : ℂ) {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt (besselKMoment j ν) (-besselKMoment (j + 1) ν z) z := by
  have hε : 0 < z.re / 2 := half_pos hz
  have hball : ∀ w ∈ Metric.ball z (z.re / 2), z.re / 2 ≤ w.re := by
    intro w hw
    have h1 : |w.re - z.re| ≤ ‖w - z‖ := by
      simpa using Complex.abs_re_le_norm (w - z)
    have h2 : ‖w - z‖ < z.re / 2 := by simpa [dist_eq_norm] using hw
    have := (abs_lt.mp (lt_of_le_of_lt h1 h2)).1
    linarith
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun w t => (Real.cosh t : ℂ) ^ j * besselKKernel ν w t)
    (F' := fun w t => -((Real.cosh t : ℂ) ^ (j + 1) * besselKKernel ν w t))
    (x₀ := z) (bound := fun t => Real.exp (-(z.re / 2 * Real.cosh t) + (|ν.re| + (j + 1 : ℕ)) * |t|))
    (Metric.ball_mem_nhds z hε) (Eventually.of_forall fun w => by unfold besselKKernel; fun_prop)
    (integrable_cosh_pow_mul_besselKKernel hz j)
    (by unfold besselKKernel; fun_prop)
    (Eventually.of_forall fun t w hw => by
      rw [norm_neg]
      exact norm_cosh_pow_mul_besselKKernel_le (hball w hw) le_rfl (j + 1) t)
    (kInt_integrable_exp_neg_mul_cosh_add hε)
    (Eventually.of_forall fun t w _ => by
      have h1 : HasDerivAt (fun w : ℂ => -(w * (Real.cosh t : ℂ)) + ν * t)
          (-(Real.cosh t : ℂ)) w := by
        simpa using ((hasDerivAt_id w).mul_const (Real.cosh t : ℂ)).neg.add_const (ν * t)
      have h2 := (h1.cexp).const_mul ((Real.cosh t : ℂ) ^ j)
      unfold besselKKernel
      convert h2 using 1
      ring)
  rw [integral_neg] at h
  exact h.2

/-- `Ψ_j(ν, z)` is entire in `ν` for fixed `z` with `Re z > 0`. -/
lemma differentiable_besselKMoment_order (j : ℕ) {z : ℂ} (hz : 0 < z.re) :
    Differentiable ℂ fun ν => besselKMoment j ν z := by
  rw [← differentiableOn_univ]
  refine Complex.differentiableOn_integral_of_locally_dominated isOpen_univ
    (fun ν _ => by unfold besselKKernel; fun_prop)
    (Eventually.of_forall fun t => ?_) (fun ν _ => ?_)
  · unfold besselKKernel
    exact (Differentiable.const_mul (by fun_prop) _).differentiableOn
  · refine ⟨Metric.ball ν 1, Metric.ball_mem_nhds ν one_pos,
      fun t => Real.exp (-(z.re * Real.cosh t) + (|ν.re| + 1 + j) * |t|),
      kInt_integrable_exp_neg_mul_cosh_add hz, Eventually.of_forall fun t y hy => ?_⟩
    refine norm_cosh_pow_mul_besselKKernel_le le_rfl ?_ j t
    have h1 : |y.re - ν.re| ≤ ‖y - ν‖ := by simpa using Complex.abs_re_le_norm (y - ν)
    have h2 : ‖y - ν‖ < 1 := by simpa [dist_eq_norm] using hy
    have := abs_sub_abs_le_abs_sub y.re ν.re
    linarith

lemma kInt_tendsto_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) :
    Tendsto (fun t : ℝ => Real.exp (-b * t ^ 2)) atTop (𝓝 0) ∧
      Tendsto (fun t : ℝ => Real.exp (-b * t ^ 2)) atBot (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ => t ^ 2) atTop atTop := tendsto_pow_atTop two_ne_zero
  have h2 : Tendsto (fun t : ℝ => t ^ 2) atBot atTop := by
    have := h1.comp tendsto_neg_atBot_atTop
    refine this.congr fun t => ?_
    simp
  exact ⟨Real.tendsto_exp_atBot.comp ((tendsto_neg_atTop_atBot.comp
      (h1.const_mul_atTop hb)).congr fun t => by simp),
    Real.tendsto_exp_atBot.comp ((tendsto_neg_atTop_atBot.comp
      (h2.const_mul_atTop hb)).congr fun t => by simp)⟩

/-- Functions dominated by `C cosh t · |e^{-z cosh t + νt}|` vanish at both ends. -/
lemma tendsto_of_norm_le_cosh_mul_besselKKernel {ν z : ℂ} (hz : 0 < z.re) {f : ℝ → ℂ} {C : ℝ}
    (hf : ∀ t, ‖f t‖ ≤ C * ‖(Real.cosh t : ℂ) ^ 1 * besselKKernel ν z t‖) :
    Tendsto f atTop (𝓝 0) ∧ Tendsto f atBot (𝓝 0) := by
  have hb : ∀ t, ‖f t‖ ≤ C * (Real.exp (2 * (|ν.re| + (1 : ℕ)) ^ 2 / z.re) *
      Real.exp (-(z.re / 8) * t ^ 2)) := fun t => by
    have hC : 0 ≤ C := by
      have := (norm_nonneg _).trans (hf 0)
      by_contra h
      push Not at h
      have h0 : 0 < ‖(Real.cosh 0 : ℂ) ^ 1 * besselKKernel ν z 0‖ := by
        simp [besselKKernel, Complex.exp_ne_zero]
      nlinarith
    refine (hf t).trans (mul_le_mul_of_nonneg_left ?_ hC)
    exact (norm_cosh_pow_mul_besselKKernel_le le_rfl le_rfl 1 t).trans
      (kInt_exp_neg_mul_cosh_add_le hz t)
  obtain ⟨h1, h2⟩ := kInt_tendsto_exp_neg_mul_sq (by positivity : 0 < z.re / 8)
  constructor
  · refine squeeze_zero_norm hb ?_
    simpa using (h1.const_mul _).const_mul C
  · refine squeeze_zero_norm hb ?_
    simpa using (h2.const_mul _).const_mul C

/-- The boundary function `H(t) = -(z sinh t + ν) e^{-z cosh t + νt}` of the integration by
parts behind the modified Bessel equation. -/
lemma hasDerivAt_besselKKernel_boundary (ν z : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => -(z * (Real.sinh s : ℂ) + ν) * besselKKernel ν z s)
      (z ^ 2 * (Real.cosh t : ℂ) ^ 2 * besselKKernel ν z t -
        z * ((Real.cosh t : ℂ) ^ 1 * besselKKernel ν z t) -
        (z ^ 2 + ν ^ 2) * ((Real.cosh t : ℂ) ^ 0 * besselKKernel ν z t)) t := by
  have hsinh : HasDerivAt (fun s : ℝ => (Real.sinh s : ℂ)) (Real.cosh t : ℂ) t := by
    simpa using (Real.hasDerivAt_sinh t).ofReal_comp
  have hcosh : HasDerivAt (fun s : ℝ => (Real.cosh s : ℂ)) (Real.sinh t : ℂ) t := by
    simpa using (Real.hasDerivAt_cosh t).ofReal_comp
  have hlin : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
    simpa using (hasDerivAt_id t).ofReal_comp
  have hk : HasDerivAt (besselKKernel ν z)
      ((-(z * (Real.sinh t : ℂ)) + ν) * besselKKernel ν z t) t := by
    have := ((hcosh.const_mul z).neg.add (hlin.const_mul ν)).cexp
    unfold besselKKernel
    convert this using 1
    simp only [Pi.neg_apply, Pi.add_apply]
    ring
  have := ((hsinh.const_mul z).add_const ν).neg.mul hk
  convert this using 1
  have hc : (Real.cosh t : ℂ) ^ 2 = (Real.sinh t : ℂ) ^ 2 + 1 := by
    have := Real.cosh_sq t
    exact_mod_cast this
  rw [hc]
  simp only [Pi.neg_apply]
  ring

/-- The moments satisfy the modified Bessel equation:
`z² Ψ₂ - z Ψ₁ - (z² + ν²) Ψ₀ = 0`. -/
lemma besselKMoment_ode (ν : ℂ) {z : ℂ} (hz : 0 < z.re) :
    z ^ 2 * besselKMoment 2 ν z - z * besselKMoment 1 ν z -
      (z ^ 2 + ν ^ 2) * besselKMoment 0 ν z = 0 := by
  have hi := fun j => integrable_cosh_pow_mul_besselKKernel (ν := ν) hz j
  have hlim := tendsto_of_norm_le_cosh_mul_besselKKernel (ν := ν) hz
    (f := fun s : ℝ => -(z * (Real.sinh s : ℂ) + ν) * besselKKernel ν z s)
    (C := ‖z‖ + ‖ν‖) fun t => by
      rw [norm_mul, norm_neg, pow_one, norm_mul]
      have h1 : ‖z * (Real.sinh t : ℂ) + ν‖ ≤ (‖z‖ + ‖ν‖) * ‖(Real.cosh t : ℂ)‖ := by
        have hs : ‖(Real.sinh t : ℂ)‖ ≤ ‖(Real.cosh t : ℂ)‖ := by
          rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_pos (Real.cosh_pos t)]
          rw [Real.abs_sinh, ← Real.cosh_abs]
          exact (Real.sinh_lt_cosh (x := |t|)).le
        have hc1 : 1 ≤ ‖(Real.cosh t : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.cosh_pos t)]
          exact Real.one_le_cosh t
        calc ‖z * (Real.sinh t : ℂ) + ν‖ ≤ ‖z‖ * ‖(Real.sinh t : ℂ)‖ + ‖ν‖ := by
              simpa [norm_mul] using norm_add_le (z * (Real.sinh t : ℂ)) ν
          _ ≤ ‖z‖ * ‖(Real.cosh t : ℂ)‖ + ‖ν‖ * ‖(Real.cosh t : ℂ)‖ := by
              gcongr
              nlinarith [norm_nonneg ν]
          _ = _ := by ring
      calc ‖z * (Real.sinh t : ℂ) + ν‖ * ‖besselKKernel ν z t‖
          ≤ (‖z‖ + ‖ν‖) * ‖(Real.cosh t : ℂ)‖ * ‖besselKKernel ν z t‖ :=
            mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ = _ := by ring
  have h := integral_of_hasDerivAt_of_tendsto (hasDerivAt_besselKKernel_boundary ν z)
    ((((hi 2).const_mul (z ^ 2)).sub ((hi 1).const_mul z)).sub ((hi 0).const_mul (z ^ 2 + ν ^ 2))
      |>.congr (Eventually.of_forall fun t => by simp only [Pi.sub_apply]; ring))
    hlim.2 hlim.1
  have hA : Integrable (fun t : ℝ => z ^ 2 * (Real.cosh t : ℂ) ^ 2 * besselKKernel ν z t) :=
    ((hi 2).const_mul (z ^ 2)).congr (Eventually.of_forall fun t => by simp only; ring)
  have hB := (hi 1).const_mul z
  have hC := (hi 0).const_mul (z ^ 2 + ν ^ 2)
  have e1 := integral_sub (μ := volume) (hA.sub hB) hC
  have e2 := integral_sub (μ := volume) hA hB
  simp only [Pi.sub_apply] at e1 e2
  rw [sub_self, e1, e2, integral_const_mul, integral_const_mul] at h
  unfold besselKMoment
  rw [← h, ← integral_const_mul]
  congr 3
  funext t
  ring

/-- The open right half-plane. -/
abbrev kIntRightHalfPlane : Set ℂ := {z : ℂ | 0 < z.re}

lemma isOpen_kIntRightHalfPlane : IsOpen kIntRightHalfPlane := isOpen_lt continuous_const continuous_re

lemma kIntRightHalfPlane_subset_slitPlane : kIntRightHalfPlane ⊆ slitPlane := fun _ hz => Or.inl hz

/-- The Wronskian-type combination `z (Φ g' - Φ' g)` of the moment integral `Φ = Ψ₀` with a
solution `g` of the modified Bessel equation. -/
def besselKMomentWronskian (ν : ℂ) (g : ℂ → ℂ) (z : ℂ) : ℂ :=
  z * (besselKMoment 0 ν z * deriv g z + besselKMoment 1 ν z * g z)

/-- For any solution `g` of the modified Bessel equation on the slit plane, the combination
`z (Φ g' - Φ' g)` is constant on the right half-plane. -/
lemma besselKMomentWronskian_const (ν : ℂ) {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g slitPlane)
    (hode : ∀ z ∈ slitPlane, z ^ 2 * iteratedDeriv 2 g z + z * deriv g z -
      (z ^ 2 + ν ^ 2) * g z = 0) {z w : ℂ} (hz : 0 < z.re) (hw : 0 < w.re) :
    besselKMomentWronskian ν g z = besselKMomentWronskian ν g w := by
  have hderiv : ∀ u ∈ kIntRightHalfPlane, HasDerivAt (besselKMomentWronskian ν g) 0 u := by
    intro u hu
    have hu' : (0 : ℝ) < u.re := hu
    have hus := kIntRightHalfPlane_subset_slitPlane hu
    have hu0 := slitPlane_ne_zero hus
    have hga : AnalyticAt ℂ g u := hg.analyticAt (isOpen_slitPlane.mem_nhds hus)
    have hg1 : HasDerivAt g (deriv g u) u := hga.differentiableAt.hasDerivAt
    have hg2 : HasDerivAt (deriv g) (iteratedDeriv 2 g u) u := by
      rw [iteratedDeriv_succ, iteratedDeriv_one]
      exact hga.deriv.differentiableAt.hasDerivAt
    have h0 := hasDerivAt_besselKMoment 0 ν hu'
    have h1 := hasDerivAt_besselKMoment 1 ν hu'
    have hW := (hasDerivAt_id u).mul ((h0.mul hg2).add (h1.mul hg1))
    unfold besselKMomentWronskian
    refine hW.congr_deriv ?_
    have hode' := hode u hus
    have hmom := besselKMoment_ode ν hu'
    simp only [id, Pi.add_apply, Pi.mul_apply, zero_add, Nat.reduceAdd]
    refine mul_left_cancel₀ hu0 ?_
    linear_combination besselKMoment 0 ν u * hode' - g u * hmom
  exact isOpen_kIntRightHalfPlane.is_const_of_deriv_eq_zero (convex_halfSpace_re_gt 0).isPreconnected
    (fun u hu => (hderiv u hu).differentiableAt.differentiableWithinAt)
    (fun u hu => (hderiv u hu).deriv) hz hw

/-- `Φ_{-ν} = Φ_ν`. -/
lemma besselKMoment_neg_order (j : ℕ) (ν z : ℂ) :
    besselKMoment j (-ν) z = besselKMoment j ν z := by
  unfold besselKMoment
  rw [← integral_neg_eq_self]
  congr 1
  funext t
  simp only [besselKKernel, Real.cosh_neg, ofReal_neg]
  ring_nf

/-- The pointwise identity behind the shift `t ↦ t - log(x/2)` and the substitution `v = e^t`:
`e^u g(e^u) = (x/2)^ν e^{-x cosh(u - log(x/2)) + ν(u - log(x/2))}` for the Schläfli integrand `g`. -/
lemma exp_smul_kSchlafli_eq {x : ℝ} (hx : 0 < x) (ν : ℂ) (u : ℝ) :
    Real.exp u • (exp (-((Real.exp u : ℝ) : ℂ) - (x : ℂ) ^ 2 / (4 * ((Real.exp u : ℝ) : ℂ))) *
      ((Real.exp u : ℝ) : ℂ) ^ (ν - 1)) =
      ((x : ℂ) / 2) ^ ν * besselKKernel ν x (u + -Real.log (x / 2)) := by
  set L := Real.log (x / 2) with hL
  have hx2 : (0 : ℝ) < x / 2 := by positivity
  have hpow : ((x : ℂ) / 2) ^ ν = exp (ν * L) := by
    rw [show ((x : ℂ) / 2) = ((x / 2 : ℝ) : ℂ) by push_cast; ring,
      cpow_def_of_ne_zero (by exact_mod_cast hx2.ne'), ← ofReal_log hx2.le, mul_comm]
  rw [hpow]
  have hexpL : Real.exp L = x / 2 := by rw [hL, Real.exp_log hx2]
  have hcosh : x * Real.cosh (u + -L) = Real.exp u + x ^ 2 / 4 * Real.exp (-u) := by
    rw [Real.cosh_eq, show -(u + -L) = -u + L by ring, Real.exp_add, Real.exp_add, Real.exp_neg L,
      hexpL]
    field_simp
    ring
  have hev : (Real.exp u : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos u).ne'
  have hcp : ((Real.exp u : ℝ) : ℂ) ^ (ν - 1) = exp ((ν - 1) * u) := by
    rw [cpow_def_of_ne_zero hev, ← ofReal_log (Real.exp_pos u).le, Real.log_exp]
    ring_nf
  symm
  simp only [besselKKernel, real_smul]
  rw [hcp, ← exp_add, ← exp_add, ofReal_exp, ← exp_add]
  congr 1
  have hc : (x : ℂ) * (Real.cosh (u + -L) : ℂ) = exp u + (x : ℂ) ^ 2 / 4 * exp (-(u : ℂ)) := by
    have := congrArg (fun r : ℝ => (r : ℂ)) hcosh
    push_cast at this
    rw [← this]
    push_cast
    rfl
  rw [hc, Complex.exp_neg]
  have he : exp (u : ℂ) ≠ 0 := exp_ne_zero _
  push_cast
  field_simp
  ring

/-- After the shift `t ↦ t - log(x/2)` and the substitution `v = e^t`, the moment integral
becomes the Schläfli form `(x/2)^ν Φ_ν(x) = ∫₀^∞ e^{-v - x²/(4v)} v^{ν-1} dv`. -/
lemma cpow_mul_besselKMoment_eq {x : ℝ} (hx : 0 < x) (ν : ℂ) :
    ((x : ℂ) / 2) ^ ν * besselKMoment 0 ν x =
      ∫ v : ℝ in Ioi 0, exp (-(v : ℂ) - (x : ℂ) ^ 2 / (4 * v)) * (v : ℂ) ^ (ν - 1) := by
  unfold besselKMoment
  rw [← integral_const_mul, ← integral_add_right_eq_self (μ := volume) _ (-Real.log (x / 2)),
    ← integral_comp_exp]
  congr 1
  funext u
  rw [exp_smul_kSchlafli_eq hx ν u, pow_zero, one_mul]

/-- The Schläfli integrand is integrable on `(0, ∞)` for `x > 0` and every complex `ν`. -/
lemma integrableOn_kSchlafli_real {x : ℝ} (hx : 0 < x) (ν : ℂ) :
    IntegrableOn (fun v : ℝ => exp (-(v : ℂ) - (x : ℂ) ^ 2 / (4 * v)) * (v : ℂ) ^ (ν - 1))
      (Ioi 0) := by
  rw [← integrable_comp_exp]
  have hxr : (0 : ℝ) < (x : ℂ).re := by simpa using hx
  refine (((integrable_besselKKernel (ν := ν) hxr).comp_add_right
    (-Real.log (x / 2))).const_mul (((x : ℂ) / 2) ^ ν)).congr (Eventually.of_forall fun u => ?_)
  exact (exp_smul_kSchlafli_eq hx ν u).symm

/-- The leading small-argument behaviour `(x/2)^ν Φ_ν(x) → Γ(ν)` for `Re ν > 0`. -/
lemma tendsto_cpow_mul_besselKMoment {ν : ℂ} (hν : 0 < ν.re) :
    Tendsto (fun x : ℝ => ((x : ℂ) / 2) ^ ν * besselKMoment 0 ν x) (𝓝[>] 0)
      (𝓝 (Gamma ν)) := by
  have heq : (fun x : ℝ => ∫ v : ℝ in Ioi 0,
      exp (-(v : ℂ) - (x : ℂ) ^ 2 / (4 * v)) * (v : ℂ) ^ (ν - 1)) =ᶠ[𝓝[>] 0]
      (fun x : ℝ => ((x : ℂ) / 2) ^ ν * besselKMoment 0 ν x) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (cpow_mul_besselKMoment_eq hx ν).symm
  refine Tendsto.congr' heq ?_
  rw [Gamma_eq_integral hν, GammaIntegral]
  have hint := Real.GammaIntegral_convergent (s := ν.re) hν
  refine tendsto_integral_filter_of_dominated_convergence
    (fun v : ℝ => Real.exp (-v) * v ^ (ν.re - 1)) ?_ ?_ hint ?_
  · exact Eventually.of_forall fun x => (by fun_prop : Measurable fun v : ℝ =>
      exp (-(v : ℂ) - (x : ℂ) ^ 2 / (4 * v)) * (v : ℂ) ^ (ν - 1)).aestronglyMeasurable
  · refine Eventually.of_forall fun x => ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    have hv0 : (0 : ℝ) < v := hv
    rw [norm_mul, Complex.norm_exp, norm_cpow_eq_rpow_re_of_pos hv0]
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (by positivity)
    have : 0 ≤ ((x : ℂ) ^ 2 / (4 * v)).re := by
      rw [show (x : ℂ) ^ 2 / (4 * v) = ((x ^ 2 / (4 * v) : ℝ) : ℂ) by push_cast; ring, ofReal_re]
      positivity
    simp only [sub_re, neg_re, ofReal_re]
    linarith
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    have hc : Continuous fun x : ℝ => exp (-(v : ℂ) - (x : ℂ) ^ 2 / (4 * v)) * (v : ℂ) ^ (ν - 1) :=
      by fun_prop
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    convert this using 2
    simp [ofReal_exp]

lemma kInt_tendsto_regularized0F1_sq_div_four (c : ℂ) :
    Tendsto (fun x : ℝ => regularizedHGFun (∅ : Multiset ℂ) {c} ((x : ℂ) ^ 2 / 4)) (𝓝[>] 0)
      (𝓝 (1 / Gamma c)) := by
  have hc := continuous_regularized0F1.comp
    (by fun_prop : Continuous fun x : ℝ => (c, (x : ℂ) ^ 2 / 4))
  simp only [Function.comp_def] at hc
  have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  have h0 : regularizedHGFun (∅ : Multiset ℂ) {c} (((0 : ℝ) : ℂ) ^ 2 / 4) = 1 / Gamma c := by
    rw [show (((0 : ℝ) : ℂ) ^ 2 / 4) = 0 by simp, DLMF.Confluent.regularizedHGFun_zero,
      regularizedHGFunCoeff_empty]
    simp
  rwa [h0] at this

lemma kInt_cpow_ofReal_div_two_ne_zero {x : ℝ} (hx : 0 < x) (ν : ℂ) : ((x : ℂ) / 2) ^ ν ≠ 0 :=
  cpow_ne_zero_iff.mpr (Or.inl (div_ne_zero (by exact_mod_cast hx.ne') two_ne_zero))

/-- `(x/2)^ν I_{-ν}(x) → 1/Γ(1-ν)` as `x → 0⁺`. -/
lemma tendsto_cpow_mul_besselI_neg (ν : ℂ) :
    Tendsto (fun x : ℝ => ((x : ℂ) / 2) ^ ν * besselI (-ν) x) (𝓝[>] 0)
      (𝓝 (1 / Gamma (1 - ν))) := by
  have h := kInt_tendsto_regularized0F1_sq_div_four (-ν + 1)
  rw [show -ν + 1 = 1 - ν by ring] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx' : (0 : ℝ) < x := hx
  unfold besselI
  rw [cpow_neg, ← mul_assoc, mul_inv_cancel₀ (kInt_cpow_ofReal_div_two_ne_zero hx' ν), one_mul,
    show -ν + 1 = 1 - ν by ring]

/-- `(x/2)^ν I_ν(x) → 0` as `x → 0⁺` when `Re ν > 0`. -/
lemma tendsto_cpow_mul_besselI {ν : ℂ} (hν : 0 < ν.re) :
    Tendsto (fun x : ℝ => ((x : ℂ) / 2) ^ ν * besselI ν x) (𝓝[>] 0) (𝓝 0) := by
  have h := kInt_tendsto_regularized0F1_sq_div_four (ν + 1)
  have hp : Tendsto (fun x : ℝ => ((x : ℂ) / 2) ^ (2 * ν)) (𝓝[>] 0) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hr : Tendsto (fun x : ℝ => (x / 2) ^ (2 * ν.re)) (𝓝[>] 0) (𝓝 0) := by
      have hc : ContinuousAt (fun x : ℝ => (x / 2) ^ (2 * ν.re)) 0 :=
        (Real.continuousAt_rpow_const _ _ (Or.inr (by linarith))).comp
          (continuousAt_id.div_const 2)
      have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      simpa [Real.zero_rpow (by linarith : (2 * ν.re) ≠ 0)] using this
    refine hr.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx' : (0 : ℝ) < x := hx
    rw [show ((x : ℂ) / 2) = ((x / 2 : ℝ) : ℂ) by push_cast; ring,
      norm_cpow_eq_rpow_re_of_pos (by positivity)]
    simp
  have := hp.mul h
  rw [zero_mul] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx' : (0 : ℝ) < x := hx
  unfold besselI
  rw [← mul_assoc, ← cpow_add _ _ (div_ne_zero (by exact_mod_cast hx'.ne') two_ne_zero), two_mul]

lemma differentiableOn_besselK_slitPlane (ν : ℂ) : DifferentiableOn ℂ (besselK ν) slitPlane :=
  fun _ hz => (hasDerivAt_besselK ν hz).differentiableAt.differentiableWithinAt

lemma differentiableOn_besselI_slitPlane (ν : ℂ) : DifferentiableOn ℂ (besselI ν) slitPlane :=
  fun _ hz => (analyticAt_besselI ν hz).differentiableAt.differentiableWithinAt

/-- On the right half-plane `Φ_ν = A K_ν - B I_ν`, with `A, B` the Wronskian constants at `1`. -/
lemma besselKMoment_eq_wronskian_combination (ν : ℂ) {z : ℂ} (hz : 0 < z.re) :
    besselKMoment 0 ν z = besselKMomentWronskian ν (besselI ν) 1 * besselK ν z -
      besselKMomentWronskian ν (besselK ν) 1 * besselI ν z := by
  have h1 : (0 : ℝ) < (1 : ℂ).re := by simp
  have hzs : z ∈ slitPlane := Or.inl hz
  rw [← besselKMomentWronskian_const ν (differentiableOn_besselI_slitPlane ν) (fun w hw => besselI_ode hw)
      hz h1, ← besselKMomentWronskian_const ν (differentiableOn_besselK_slitPlane ν)
      (fun w hw => besselK_ode_all ν hw) hz h1]
  have hW := wronskian_besselK_besselI ν hzs
  have hW' : z * (besselK ν z * deriv (besselI ν) z - deriv (besselK ν) z * besselI ν z) = 1 := by
    rw [hW]; field_simp [slitPlane_ne_zero hzs]
  unfold besselKMomentWronskian
  linear_combination (-besselKMoment 0 ν z) * hW'

/-- The constant `A(ν)` is entire in `ν`. -/
lemma differentiable_besselKMomentWronskian_besselI :
    Differentiable ℂ fun ν => besselKMomentWronskian ν (besselI ν) 1 := by
  have h1 : (1 : ℂ) ∈ slitPlane := Or.inl (by simp)
  have he : (fun ν => besselKMomentWronskian ν (besselI ν) 1) = fun ν =>
      1 * (besselKMoment 0 ν 1 * (ν / 1 * besselI ν 1 + besselI (ν + 1) 1) +
        besselKMoment 1 ν 1 * besselI ν 1) := by
    funext ν
    unfold besselKMomentWronskian
    rw [(hasDerivAt_besselI (ν := ν) h1).deriv]
  rw [he]
  have hI := differentiable_besselI_order (one_ne_zero (α := ℂ))
  have hI1 : Differentiable ℂ fun ν : ℂ => besselI (ν + 1) 1 :=
    hI.comp (differentiable_id.add_const 1)
  have h0 := differentiable_besselKMoment_order 0 (z := 1) (by simp)
  have h1' := differentiable_besselKMoment_order 1 (z := 1) (by simp)
  fun_prop

lemma kInt_not_int_of_mem_ball_half {ν : ℂ} (hν : ν ∈ Metric.ball (1 / 2 : ℂ) (1 / 2)) :
    ∀ k : ℤ, ν ≠ k := by
  intro k hk
  subst hk
  have h1 : |((k : ℂ) - 1 / 2).re| ≤ ‖(k : ℂ) - 1 / 2‖ := Complex.abs_re_le_norm _
  have h2 : ‖(k : ℂ) - 1 / 2‖ < 1 / 2 := by simpa [dist_eq_norm] using hν
  have h3 : ((k : ℂ) - 1 / 2).re = (k : ℝ) - 1 / 2 := by simp
  rw [h3] at h1
  have h4 := abs_lt.mp (lt_of_le_of_lt h1 h2)
  have h5 : (0 : ℝ) < k := by linarith [h4.1]
  have h6 : (k : ℝ) < 1 := by linarith [h4.2]
  have h7 : (0 : ℤ) < k := by exact_mod_cast h5
  have h8 : k < (1 : ℤ) := by exact_mod_cast h6
  omega

/-- `A(ν) = 2` for `Re ν > 0`, `ν ∉ ℤ`, from the behaviour as `x → 0⁺`. -/
lemma besselKMomentWronskian_besselI_eq_two_of_re_pos {ν : ℂ} (hν : 0 < ν.re)
    (hνk : ∀ k : ℤ, ν ≠ k) : besselKMomentWronskian ν (besselI ν) 1 = 2 := by
  set A := besselKMomentWronskian ν (besselI ν) 1
  set B := besselKMomentWronskian ν (besselK ν) 1
  have hs := sin_mul_pi_ne_zero hνk
  have hK : Tendsto (fun x : ℝ => ((x : ℂ) / 2) ^ ν * besselK ν x) (𝓝[>] 0)
      (𝓝 (π / 2 * (1 / Gamma (1 - ν) - 0) / sin (ν * π))) := by
    have := (((tendsto_cpow_mul_besselI_neg ν).sub (tendsto_cpow_mul_besselI hν)).const_mul
      (π / 2 : ℂ)).div_const (sin (ν * π))
    refine this.congr fun x => ?_
    rw [besselK_eq_of_not_int hνk, besselE]
    ring
  have hlim := ((hK.const_mul A).sub ((tendsto_cpow_mul_besselI hν).const_mul B))
  have hlim' : Tendsto (fun x : ℝ => ((x : ℂ) / 2) ^ ν * besselKMoment 0 ν x) (𝓝[>] 0)
      (𝓝 (A * (π / 2 * (1 / Gamma (1 - ν) - 0) / sin (ν * π)) - B * 0)) := by
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx' : (0 : ℝ) < (x : ℂ).re := by simpa using hx
    rw [besselKMoment_eq_wronskian_combination ν hx']
    ring
  have heq := tendsto_nhds_unique (tendsto_cpow_mul_besselKMoment hν) hlim'
  have hG := Gamma_mul_Gamma_one_sub ν
  have hG0 : Gamma ν ≠ 0 := Gamma_ne_zero_of_re_pos hν
  have hG1 : Gamma (1 - ν) ≠ 0 := by
    intro h; rw [h, mul_zero] at hG
    have : (π : ℂ) / sin (π * ν) ≠ 0 := div_ne_zero (by exact_mod_cast Real.pi_ne_zero)
      (by rw [mul_comm]; exact hs)
    exact this hG.symm
  rw [show sin (ν * π) = sin (π * ν) by ring_nf] at heq
  have hs' : sin (π * ν) ≠ 0 := by rw [mul_comm]; exact hs
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp at heq hG
  apply mul_left_cancel₀ hpi
  linear_combination -heq + 2 * hG

/-- `A(ν) = 2` for every `ν`, by the identity theorem. -/
lemma besselKMomentWronskian_besselI_eq_two (ν : ℂ) :
    besselKMomentWronskian ν (besselI ν) 1 = 2 := by
  have hf : AnalyticOnNhd ℂ (fun ν => besselKMomentWronskian ν (besselI ν) 1) univ :=
    fun μ _ => differentiable_besselKMomentWronskian_besselI.analyticAt μ
  have hg : AnalyticOnNhd ℂ (fun _ : ℂ => (2 : ℂ)) univ := fun _ _ => analyticAt_const
  have hev : (fun ν => besselKMomentWronskian ν (besselI ν) 1) =ᶠ[𝓝 (1 / 2 : ℂ)]
      fun _ => (2 : ℂ) := by
    filter_upwards [Metric.ball_mem_nhds (1 / 2 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)] with μ hμ
    refine besselKMomentWronskian_besselI_eq_two_of_re_pos ?_ (kInt_not_int_of_mem_ball_half hμ)
    have h1 : |(μ - 1 / 2).re| ≤ ‖μ - 1 / 2‖ := Complex.abs_re_le_norm _
    have h2 : ‖μ - 1 / 2‖ < 1 / 2 := by simpa [dist_eq_norm] using hμ
    have h3 : (μ - 1 / 2).re = μ.re - 1 / 2 := by simp
    rw [h3] at h1
    linarith [(abs_lt.mp (lt_of_le_of_lt h1 h2)).1]
  exact congrFun (hf.eq_of_eventuallyEq hg hev) ν

/-- `B(ν) = 0` for `ν ∉ ℤ`: the moment integral has no `I_ν` component. -/
lemma besselKMomentWronskian_besselK_eq_zero {ν : ℂ} (hν : ∀ k : ℤ, ν ≠ k) :
    besselKMomentWronskian ν (besselK ν) 1 = 0 := by
  set B := fun μ : ℂ => besselKMomentWronskian μ (besselK μ) 1
  have h1 : (1 : ℂ) ∈ slitPlane := Or.inl (by simp)
  have hrel : ∀ z : ℂ, 0 < z.re → B ν * besselI ν z = B (-ν) * besselI (-ν) z := by
    intro z hz
    have e1 := besselKMoment_eq_wronskian_combination ν hz
    have e2 := besselKMoment_eq_wronskian_combination (-ν) hz
    rw [besselKMoment_neg_order, besselKMomentWronskian_besselI_eq_two,
      besselK_neg ν (Or.inl hz)] at e2
    rw [besselKMomentWronskian_besselI_eq_two] at e1
    simp only [B]
    linear_combination e1 - e2
  have hev : (fun z => B ν * besselI ν z) =ᶠ[𝓝 1] fun z => B (-ν) * besselI (-ν) z := by
    filter_upwards [isOpen_kIntRightHalfPlane.mem_nhds (show (0 : ℝ) < (1 : ℂ).re by simp)]
      with z hz using hrel z hz
  have hd := hev.deriv_eq
  rw [deriv_const_mul _ (analyticAt_besselI ν h1).differentiableAt,
    deriv_const_mul _ (analyticAt_besselI (-ν) h1).differentiableAt] at hd
  have hv := hrel 1 (by simp)
  have hW := wronskian_besselI_neg ν h1
  have hs := sin_mul_pi_ne_zero hν
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have key : B ν * (-2 * sin (ν * π) / (π * 1)) = 0 := by
    rw [← hW]
    linear_combination deriv (besselI (-ν)) 1 * hv - besselI (-ν) 1 * hd
  rcases mul_eq_zero.mp key with h | h
  · exact h
  · exfalso
    field_simp at h
    exact hs (by linear_combination -h / 2)

/-- **Integral representation of `K_ν` over the line** (equivalent to DLMF 10.32.9):
`K_ν(z) = ½ ∫_ℝ e^{-z cosh t + νt} dt` for every complex order `ν` and `Re z > 0`. -/
theorem besselK_eq_half_integral (ν : ℂ) {z : ℂ} (hz : 0 < z.re) :
    besselK ν z = 1 / 2 * ∫ t : ℝ, exp (-(z * (Real.cosh t : ℂ)) + ν * t) := by
  have hzs : z ∈ slitPlane := Or.inl hz
  have hmom : ∀ μ, (∫ t : ℝ, exp (-(z * (Real.cosh t : ℂ)) + μ * t)) = besselKMoment 0 μ z := by
    intro μ; simp [besselKMoment, besselKKernel]
  simp_rw [hmom]
  refine DLMF.Confluent.eq_of_continuousAt_of_integerComplement
    (f := fun μ => besselK μ z) (g := fun μ => 1 / 2 * besselKMoment 0 μ z)
    (continuousAt_besselK_order id continuous_id ν hzs)
    ((differentiable_besselKMoment_order 0 hz).continuous.continuousAt.const_mul _)
    (fun c hc => ?_)
  have hc' := DLMF.Confluent.forall_of_mem_integerComplement hc
  have e := besselKMoment_eq_wronskian_combination c hz
  rw [besselKMomentWronskian_besselI_eq_two, besselKMomentWronskian_besselK_eq_zero hc'] at e
  rw [e]
  ring

/-- **Basset-type integral for `K_ν`** (DLMF 10.32.9):
`K_ν(z) = ∫₀^∞ e^{-z cosh t} cosh(νt) dt` for every complex `ν` and `|ph z| < π/2`. -/
@[dlmf 10.32.E9]
theorem besselK_eq_integral_cosh (ν : ℂ) {z : ℂ} (hz : 0 < z.re) :
    besselK ν z = ∫ t : ℝ in Ioi 0, exp (-(z * (Real.cosh t : ℂ))) * cosh (ν * t) := by
  rw [besselK_eq_half_integral ν hz]
  have hk : Integrable (besselKKernel ν z) := integrable_besselKKernel hz
  have hsplit := intervalIntegral.integral_Iic_add_Ioi (b := 0) hk.integrableOn hk.integrableOn
  have hneg := integral_comp_neg_Ioi 0 (besselKKernel ν z)
  rw [neg_zero] at hneg
  have hsum : ∫ t : ℝ in Ioi 0, (besselKKernel ν z t + besselKKernel ν z (-t)) =
      ∫ t : ℝ in Ioi 0, 2 * (exp (-(z * (Real.cosh t : ℂ))) * cosh (ν * t)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [besselKKernel, Real.cosh_neg, ofReal_neg, Complex.cosh, exp_add]
    rw [show ν * -(t : ℂ) = -(ν * t) by ring]
    ring
  have hkneg : IntegrableOn (fun t => besselKKernel ν z (-t)) (Ioi 0) :=
    (hk.comp_neg).integrableOn
  rw [integral_add hk.integrableOn hkneg, hneg, add_comm, hsplit, integral_const_mul] at hsum
  have : (∫ t : ℝ, exp (-(z * (Real.cosh t : ℂ)) + ν * t)) = ∫ t : ℝ, besselKKernel ν z t := rfl
  rw [this, hsum]
  ring

/-- Schläfli's form for real argument: for `x > 0` and every complex `ν`,
`K_ν(x) = ½ (x/2)^ν ∫₀^∞ e^{-t - x²/(4t)} t^{-ν-1} dt`. -/
theorem besselK_ofReal_eq_integral_schlafli {x : ℝ} (hx : 0 < x) (ν : ℂ) :
    besselK ν x = 1 / 2 * ((x : ℂ) / 2) ^ ν *
      ∫ t : ℝ in Ioi 0, exp (-(t : ℂ) - (x : ℂ) ^ 2 / (4 * t)) * (t : ℂ) ^ (-ν - 1) := by
  have hxr : (0 : ℝ) < (x : ℂ).re := by simpa using hx
  have h := cpow_mul_besselKMoment_eq hx (-ν)
  rw [besselKMoment_neg_order] at h
  rw [← h, besselK_eq_half_integral ν hxr, cpow_neg]
  have : (∫ t : ℝ, exp (-((x : ℂ) * (Real.cosh t : ℂ)) + ν * t)) = besselKMoment 0 ν x := by
    simp [besselKMoment, besselKKernel]
  rw [this]
  field_simp [kInt_cpow_ofReal_div_two_ne_zero hx ν]

/-- Pointwise majorant of the Schläfli integrand. -/
lemma norm_kSchlafli_integrand_le {v : ℝ} (hv : 0 < v) {w ν : ℂ} (hw : 0 ≤ (w ^ 2).re) :
    ‖exp (-(v : ℂ) - w ^ 2 / (4 * v)) * (v : ℂ) ^ (ν - 1)‖ ≤ Real.exp (-v) * v ^ (ν.re - 1) := by
  rw [norm_mul, Complex.norm_exp, norm_cpow_eq_rpow_re_of_pos hv]
  refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (by positivity)
  have : 0 ≤ (w ^ 2 / (4 * v)).re := by
    rw [show w ^ 2 / (4 * v) = w ^ 2 * ((1 / (4 * v) : ℝ) : ℂ) by push_cast; ring,
      re_mul_ofReal]
    exact mul_nonneg hw (by positivity)
  simp only [sub_re, neg_re, ofReal_re]
  linarith

/-- For real order and argument the line integral equals the integral of the norm. -/
lemma norm_besselKMoment_ofReal (s y : ℝ) :
    ‖besselKMoment 0 s y‖ = ∫ t : ℝ, ‖besselKKernel s y t‖ := by
  have hk : ∀ t : ℝ, besselKKernel s y t = ((Real.exp (-(y * Real.cosh t) + s * t) : ℝ) : ℂ) := by
    intro t; simp [besselKKernel, ofReal_exp]
  have hn : ∀ t : ℝ, ‖besselKKernel s y t‖ = Real.exp (-(y * Real.cosh t) + s * t) := by
    intro t; rw [hk, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  have hI : besselKMoment 0 s y = ((∫ t : ℝ, Real.exp (-(y * Real.cosh t) + s * t) : ℝ) : ℂ) := by
    unfold besselKMoment
    simp_rw [pow_zero, one_mul, hk]
    exact integral_ofReal
  rw [hI, Complex.norm_real, Real.norm_of_nonneg (integral_nonneg fun t => (Real.exp_pos _).le)]
  simp_rw [hn]

/-- `‖Φ_s(y)‖ ≤ Γ(s) (y/2)^{-s}` for real `s > 0` and `y > 0`. -/
lemma norm_besselKMoment_ofReal_le {s y : ℝ} (hs : 0 < s) (hy : 0 < y) :
    ‖besselKMoment 0 s y‖ ≤ Real.Gamma s * (y / 2) ^ (-s) := by
  have h := cpow_mul_besselKMoment_eq hy (s : ℂ)
  have hy2 : (0 : ℝ) < y / 2 := by positivity
  have hpow : ‖((y : ℂ) / 2) ^ (s : ℂ)‖ = (y / 2) ^ s := by
    rw [show ((y : ℂ) / 2) = ((y / 2 : ℝ) : ℂ) by push_cast; ring,
      norm_cpow_eq_rpow_re_of_pos hy2]
    simp
  have hle : ‖∫ v : ℝ in Ioi 0, exp (-(v : ℂ) - (y : ℂ) ^ 2 / (4 * v)) * (v : ℂ) ^ ((s : ℂ) - 1)‖
      ≤ Real.Gamma s := by
    rw [Real.Gamma_eq_integral hs]
    have hb : ∀ v ∈ Ioi (0 : ℝ), ‖exp (-(v : ℂ) - (y : ℂ) ^ 2 / (4 * v)) * (v : ℂ) ^ ((s : ℂ) - 1)‖
        ≤ Real.exp (-v) * v ^ (s - 1) := fun v hv => by
      simpa using norm_kSchlafli_integrand_le hv (w := (y : ℂ)) (ν := (s : ℂ))
        (by rw [← ofReal_pow, ofReal_re]; positivity)
    refine (norm_integral_le_integral_norm _).trans (setIntegral_mono_on ?_
      (Real.GammaIntegral_convergent hs) measurableSet_Ioi hb)
    refine ((Real.GammaIntegral_convergent hs).mono' (by fun_prop) ?_).norm
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact hb v hv
  have hmain : (y / 2) ^ s * ‖besselKMoment 0 s y‖ ≤ Real.Gamma s := by
    rw [← hpow, ← norm_mul, h]; exact hle
  rw [Real.rpow_neg hy2.le]
  have hp : 0 < (y / 2) ^ s := Real.rpow_pos_of_pos hy2 s
  rw [← div_eq_mul_inv, le_div_iff₀ hp]
  linarith [mul_comm ((y / 2) ^ s) ‖besselKMoment 0 s y‖]

/-- Schläfli's form with the opposite power, for real argument:
`K_ν(x) = ½ (x/2)^{-ν} ∫₀^∞ e^{-t - x²/(4t)} t^{ν-1} dt` (DLMF 10.32.10 with `ν ↦ -ν`). -/
theorem besselK_ofReal_eq_integral_schlafli' {x : ℝ} (hx : 0 < x) (ν : ℂ) :
    besselK ν x = 1 / 2 * ((x : ℂ) / 2) ^ (-ν) *
      ∫ t : ℝ in Ioi 0, exp (-(t : ℂ) - (x : ℂ) ^ 2 / (4 * t)) * (t : ℂ) ^ (ν - 1) := by
  have hxr : (0 : ℝ) < (x : ℂ).re := by simpa using hx
  rw [← cpow_mul_besselKMoment_eq hx ν, besselK_eq_half_integral ν hxr, cpow_neg]
  have : (∫ t : ℝ, exp (-((x : ℂ) * (Real.cosh t : ℂ)) + ν * t)) = besselKMoment 0 ν x := by
    simp [besselKMoment, besselKKernel]
  rw [this]
  field_simp [kInt_cpow_ofReal_div_two_ne_zero hx ν]

/-- `∫ ‖e^{-w cosh t + νt}‖ dt ≤ 2 Γ(s) (Re w / 2)^{-s}` for `Re w > 0`, `s > 0`, `|Re ν| ≤ s`. -/
lemma integral_norm_besselKKernel_le {ν w : ℂ} (hw : 0 < w.re) {s : ℝ} (hs : 0 < s)
    (hνs : |ν.re| ≤ s) :
    ∫ t : ℝ, ‖besselKKernel ν w t‖ ≤ 2 * (Real.Gamma s * (w.re / 2) ^ (-s)) := by
  set y := w.re
  have hyc : (0 : ℝ) < (y : ℂ).re := by simpa using hw
  have hkn : ∀ t, ‖besselKKernel ν w t‖ ≤ ‖besselKKernel s y t‖ + ‖besselKKernel (-s) y t‖ := by
    intro t
    simp only [norm_besselKKernel, ofReal_re, neg_re]
    have h1 : ν.re * t ≤ s * |t| := by
      calc ν.re * t ≤ |ν.re * t| := le_abs_self _
        _ = |ν.re| * |t| := abs_mul _ _
        _ ≤ s * |t| := mul_le_mul_of_nonneg_right hνs (abs_nonneg t)
    rcases le_total 0 t with ht | ht
    · rw [abs_of_nonneg ht] at h1
      have := Real.exp_le_exp.mpr (by linarith : -(y * Real.cosh t) + ν.re * t ≤
        -(y * Real.cosh t) + s * t)
      linarith [Real.exp_pos (-(y * Real.cosh t) + -s * t)]
    · rw [abs_of_nonpos ht] at h1
      have := Real.exp_le_exp.mpr (by linarith : -(y * Real.cosh t) + ν.re * t ≤
        -(y * Real.cosh t) + -s * t)
      linarith [Real.exp_pos (-(y * Real.cosh t) + s * t)]
  have hint : ∀ μ : ℂ, Integrable fun t => ‖besselKKernel μ y t‖ :=
    fun μ => (integrable_besselKKernel hyc).norm
  have h1 : ∫ t : ℝ, ‖besselKKernel ν w t‖ ≤
      ‖besselKMoment 0 s y‖ + ‖besselKMoment 0 (-s) y‖ := by
    have e2 : besselKMoment 0 (-s) y = besselKMoment 0 ((-s : ℝ) : ℂ) y := by push_cast; rfl
    rw [norm_besselKMoment_ofReal, e2, norm_besselKMoment_ofReal, ← integral_add (hint _)
      (by simpa using hint (-(s : ℂ)))]
    refine integral_mono (integrable_besselKKernel hw).norm
      ((hint _).add (by simpa using hint (-(s : ℂ)))) fun t => ?_
    simpa [besselKKernel] using hkn t
  rw [besselKMoment_neg_order] at h1
  have h2 := norm_besselKMoment_ofReal_le hs hw
  linarith

/-- **A uniform bound for `K_ν`**: for `Re w > 0`, `s > 0` and `|Re ν| ≤ s`,
`‖K_ν(w)‖ ≤ Γ(s) (Re w / 2)^{-s}`. -/
theorem norm_besselK_le {ν w : ℂ} (hw : 0 < w.re) {s : ℝ} (hs : 0 < s) (hνs : |ν.re| ≤ s) :
    ‖besselK ν w‖ ≤ Real.Gamma s * (w.re / 2) ^ (-s) := by
  rw [besselK_eq_half_integral ν hw, norm_mul]
  have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [this]
  have h1 := (norm_integral_le_integral_norm (μ := volume) (besselKKernel ν w)).trans
    (integral_norm_besselKKernel_le hw hs hνs)
  have e : (∫ t : ℝ, exp (-(w * (Real.cosh t : ℂ)) + ν * t)) = ∫ t : ℝ, besselKKernel ν w t := rfl
  rw [e]
  linarith

/-- **Exponential decay bound for `K_ν`**: for `Re w > 0`, `s > 0` and `|Re ν| ≤ s`,
`‖K_ν(w)‖ ≤ e^{-Re w / 2} Γ(s) (Re w / 4)^{-s}`. -/
theorem norm_besselK_le_exp {ν w : ℂ} (hw : 0 < w.re) {s : ℝ} (hs : 0 < s)
    (hνs : |ν.re| ≤ s) :
    ‖besselK ν w‖ ≤ Real.exp (-(w.re / 2)) * (Real.Gamma s * (w.re / 4) ^ (-s)) := by
  set y := w.re
  have hy2 : (0 : ℝ) < ((y / 2 : ℝ) : ℂ).re := by simp; linarith
  have hk : ∀ t, ‖besselKKernel ν w t‖ ≤
      Real.exp (-(y / 2)) * ‖besselKKernel ν ((y / 2 : ℝ) : ℂ) t‖ := by
    intro t
    rw [norm_besselKKernel, norm_besselKKernel, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    simp only [ofReal_re]
    nlinarith [Real.one_le_cosh t]
  have hI : ∫ t : ℝ, ‖besselKKernel ν w t‖ ≤
      Real.exp (-(y / 2)) * (2 * (Real.Gamma s * (y / 4) ^ (-s))) := by
    have h := integral_norm_besselKKernel_le hy2 hs hνs
    simp only [ofReal_re] at h
    rw [show y / 2 / 2 = y / 4 by ring] at h
    calc ∫ t : ℝ, ‖besselKKernel ν w t‖
        ≤ ∫ t : ℝ, Real.exp (-(y / 2)) * ‖besselKKernel ν ((y / 2 : ℝ) : ℂ) t‖ :=
          integral_mono (integrable_besselKKernel hw).norm
            ((integrable_besselKKernel hy2).norm.const_mul _) hk
      _ = Real.exp (-(y / 2)) * ∫ t : ℝ, ‖besselKKernel ν ((y / 2 : ℝ) : ℂ) t‖ :=
          integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
  rw [besselK_eq_half_integral ν hw, norm_mul]
  have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [this]
  have h1 := (norm_integral_le_integral_norm (μ := volume) (besselKKernel ν w)).trans hI
  have e : (∫ t : ℝ, exp (-(w * (Real.cosh t : ℂ)) + ν * t)) = ∫ t : ℝ, besselKKernel ν w t := rfl
  rw [e]
  linarith

/-- The open sector `|ph z| < π/4`, written as `|Im z| < Re z`. -/
def kIntQuarterSector : Set ℂ := {z : ℂ | |z.im| < z.re}

lemma isOpen_kIntQuarterSector : IsOpen kIntQuarterSector :=
  isOpen_lt (continuous_abs.comp continuous_im) continuous_re

lemma convex_kIntQuarterSector : Convex ℝ kIntQuarterSector := by
  have h1 : Convex ℝ {z : ℂ | z.im - z.re < 0} :=
    convex_halfSpace_lt (f := fun z : ℂ => z.im - z.re)
      ⟨fun a b => by simp; ring, fun c a => by simp; ring⟩ 0
  have h2 : Convex ℝ {z : ℂ | -z.im - z.re < 0} :=
    convex_halfSpace_lt (f := fun z : ℂ => -z.im - z.re)
      ⟨fun a b => by simp; ring, fun c a => by simp; ring⟩ 0
  convert h1.inter h2 using 1
  ext z
  simp only [kIntQuarterSector, mem_ofPred_eq, mem_inter_iff, abs_lt]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

lemma re_pos_of_mem_kIntQuarterSector {z : ℂ} (hz : z ∈ kIntQuarterSector) : 0 < z.re :=
  (abs_nonneg _).trans_lt hz

lemma re_sq_pos_of_mem_kIntQuarterSector {z : ℂ} (hz : z ∈ kIntQuarterSector) : 0 < (z ^ 2).re := by
  have h : |z.im| < z.re := hz
  have h0 := (abs_nonneg z.im).trans_lt h
  rw [sq, mul_re]
  nlinarith [abs_mul_abs_self z.im, abs_nonneg z.im]

/-- Holomorphy of the Schläfli integral on `Re z² > 0`. -/
lemma differentiableOn_kSchlafli_integral (ν : ℂ) :
    DifferentiableOn ℂ (fun z : ℂ => ∫ t : ℝ in Ioi 0,
      exp (-(t : ℂ) - z ^ 2 / (4 * t)) * (t : ℂ) ^ (-ν - 1)) {z : ℂ | 0 < (z ^ 2).re} := by
  have hU : IsOpen {z : ℂ | 0 < (z ^ 2).re} :=
    isOpen_lt continuous_const (continuous_re.comp (continuous_pow 2))
  refine Complex.differentiableOn_integral_Ioi_of_locally_dominated hU 0
    (fun z _ => ?_) ?_ (fun z₀ hz₀ => ?_)
  · exact ContinuousOn.aestronglyMeasurable (fun t ht => by
      have ht' : (0 : ℝ) < t := ht
      have hts : (t : ℂ) ∈ slitPlane := by simpa using ht'
      refine ContinuousAt.continuousWithinAt ?_
      have hc : ContinuousAt (fun s : ℝ => (s : ℂ)) t := continuous_ofReal.continuousAt
      have hne : (4 * (t : ℂ)) ≠ 0 := by
        have : (t : ℂ) ≠ 0 := by exact_mod_cast ht'.ne'
        exact mul_ne_zero (by norm_num : (4 : ℂ) ≠ 0) this
      exact (((hc.neg).sub (continuousAt_const.div (continuousAt_const.mul hc) hne)).cexp).mul
        (hc.cpow continuousAt_const hts)) measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht' : (0 : ℝ) < t := ht
    have hne : (4 * (t : ℂ)) ≠ 0 := mul_ne_zero (by norm_num : (4 : ℂ) ≠ 0) (by exact_mod_cast ht'.ne')
    exact (((differentiable_const _).sub ((differentiable_pow 2).div_const _)).cexp.mul
      (differentiable_const _)).differentiableOn
  · change 0 < (z₀ ^ 2).re at hz₀
    set δ := (z₀ ^ 2).re / 2
    have hδ : 0 < δ := by positivity
    have hV : {z : ℂ | δ < (z ^ 2).re} ∈ 𝓝 z₀ :=
      (isOpen_lt continuous_const (continuous_re.comp (continuous_pow 2))).mem_nhds
        (by change δ < (z₀ ^ 2).re; exact half_lt_self hz₀)
    refine ⟨_, hV, fun t => ‖exp (-(t : ℂ) - ((Real.sqrt δ : ℝ) : ℂ) ^ 2 / (4 * t)) *
      (t : ℂ) ^ (-((ν.re : ℝ) : ℂ) - 1)‖, ?_, ?_⟩
    · have := (integrableOn_kSchlafli_real (Real.sqrt_pos.mpr hδ) (-((ν.re : ℝ) : ℂ))).norm
      exact this
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht z hz
      have ht' : (0 : ℝ) < t := ht
      change δ < (z ^ 2).re at hz
      rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp,
        norm_cpow_eq_rpow_re_of_pos ht', norm_cpow_eq_rpow_re_of_pos ht']
      have hr : ∀ w : ℂ, (-(t : ℂ) - w / (4 * t)).re = -t - w.re / (4 * t) := by
        intro w
        rw [show w / (4 * t) = w * ((1 / (4 * t) : ℝ) : ℂ) by push_cast; ring]
        simp
        ring
      rw [hr, hr, ← ofReal_pow, ofReal_re, Real.sq_sqrt hδ.le]
      have : (-ν - 1).re = (-((ν.re : ℝ) : ℂ) - 1).re := by simp
      rw [this]
      refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (by positivity)
      have h4 : 0 < 4 * t := by positivity
      have := div_le_div_of_nonneg_right hz.le h4.le
      linarith

/-- **Schläfli-type integral for `K_ν`** (DLMF 10.32.10), with the sector `|ph z| < π/4` written
as `|Im z| < Re z`: `K_ν(z) = ½ (z/2)^ν ∫₀^∞ e^{-t - z²/(4t)} t^{-ν-1} dt`, for every complex `ν`. -/
theorem besselK_eq_integral_schlafli (ν : ℂ) {z : ℂ} (hz : |z.im| < z.re) :
    besselK ν z = 1 / 2 * (z / 2) ^ ν *
      ∫ t : ℝ in Ioi 0, exp (-(t : ℂ) - z ^ 2 / (4 * t)) * (t : ℂ) ^ (-ν - 1) := by
  have hS : kIntQuarterSector ⊆ slitPlane := fun w hw => Or.inl (re_pos_of_mem_kIntQuarterSector hw)
  have hf : AnalyticOnNhd ℂ (besselK ν) kIntQuarterSector :=
    ((differentiableOn_besselK_slitPlane ν).mono hS).analyticOnNhd isOpen_kIntQuarterSector
  have hg : AnalyticOnNhd ℂ (fun w : ℂ => 1 / 2 * (w / 2) ^ ν *
      ∫ t : ℝ in Ioi 0, exp (-(t : ℂ) - w ^ 2 / (4 * t)) * (t : ℂ) ^ (-ν - 1))
      kIntQuarterSector := by
    refine DifferentiableOn.analyticOnNhd ?_ isOpen_kIntQuarterSector
    refine DifferentiableOn.mul ?_ ((differentiableOn_kSchlafli_integral ν).mono
      fun w hw => re_sq_pos_of_mem_kIntQuarterSector hw)
    refine DifferentiableOn.const_mul (fun w hw => ?_) _
    have hw2 : w / 2 ∈ slitPlane := Or.inl (by
      have := re_pos_of_mem_kIntQuarterSector hw; simp; linarith)
    exact ((differentiableAt_id.div_const 2).cpow_const hw2).differentiableWithinAt
  have h1 : (1 : ℂ) ∈ kIntQuarterSector := by simp [kIntQuarterSector]
  have hfreq : ∃ᶠ w in 𝓝[≠] (1 : ℂ), besselK ν w = 1 / 2 * (w / 2) ^ ν *
      ∫ t : ℝ in Ioi 0, exp (-(t : ℂ) - w ^ 2 / (4 * t)) * (t : ℂ) ^ (-ν - 1) := by
    have ht : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[≠] 1) (𝓝[≠] (1 : ℂ)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · exact ((continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds).trans (by simp)
      · filter_upwards [self_mem_nhdsWithin] with r hr
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, ofReal_eq_one] using hr
    apply ht.frequently
    apply Eventually.frequently
    filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds (zero_lt_one' ℝ))] with r hr
    exact besselK_ofReal_eq_integral_schlafli hr ν
  exact hf.eqOn_of_preconnected_of_frequently_eq hg convex_kIntQuarterSector.isPreconnected h1
    hfreq hz

lemma kInt_abs_im_lt_re_of_abs_arg_lt {z : ℂ} (hz0 : z ≠ 0) (hz : |z.arg| < π / 4) :
    |z.im| < z.re := by
  set θ := z.arg
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hpi := Real.pi_pos
  have habs : |θ| < π / 4 := hz
  have hb := abs_lt.mp habs
  have hcos : Real.cos (π / 4) < Real.cos θ := by
    rw [← Real.cos_abs θ]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi_div_two (abs_nonneg θ) (by linarith) habs
  have hsin : |Real.sin θ| < Real.sin (π / 4) := by
    rw [show |Real.sin θ| = Real.sin |θ| by
      rcases le_total 0 θ with h | h
      · rw [abs_of_nonneg h, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h (by linarith))]
      · rw [abs_of_nonpos h, abs_of_nonpos (Real.sin_nonpos_of_nonpos_of_neg_pi_le h
          (by linarith)), Real.sin_neg]]
    exact Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [abs_nonneg θ]) (by linarith) habs
  rw [Real.sin_pi_div_four] at hsin
  rw [Real.cos_pi_div_four] at hcos
  rw [← norm_mul_cos_arg z, ← norm_mul_sin_arg z, abs_mul, abs_of_pos hn]
  exact mul_lt_mul_of_pos_left (hsin.trans hcos) hn

/-- DLMF 10.32.10 in the phase form `|ph z| < π/4`, `z ≠ 0`. -/
@[dlmf 10.32.E10]
theorem besselK_eq_integral_schlafli_of_abs_arg_lt (ν : ℂ) {z : ℂ} (hz0 : z ≠ 0)
    (hz : |z.arg| < π / 4) :
    besselK ν z = 1 / 2 * (z / 2) ^ ν *
      ∫ t : ℝ in Ioi 0, exp (-(t : ℂ) - z ^ 2 / (4 * t)) * (t : ℂ) ^ (-ν - 1) :=
  besselK_eq_integral_schlafli ν (kInt_abs_im_lt_re_of_abs_arg_lt hz0 hz)

end DLMF.Bessel
