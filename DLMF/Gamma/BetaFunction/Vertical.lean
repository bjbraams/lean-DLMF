/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Gamma.BetaFunction.Cosine

/-!
# Cauchy vertical Beta integral

The vertical-line Beta integral, including convergence and evaluation.

Source references and common attribution are retained in
`DLMF.Gamma.BetaFunction`.
-/

@[expose] public section

open Complex MeasureTheory intervalIntegral

open scoped Real

noncomputable section

namespace DLMF.Gamma

/-! ### Cauchy's vertical Beta integral (DLMF 5.12.8)

For `Re a > 0` and `Re b > 1` the factor `(w + i t)^{-a}` is a Laplace integral and
`(z - i t)^{-b}` is, by Fourier inversion, the Fourier transform of `s^{b-1} e^{-zs}`; Fubini
then gives the Gamma integral of `s^{a+b-2} e^{-(w+z)s}`. Analytic continuation in `b` and the
symmetry `t ↦ -t` extend the identity to `Re (a + b) > 1`. -/

section VerticalBeta

open Set Filter
open scoped Topology FourierTransform

/-- A linear lower bound for `‖w + i t‖` on the right half-plane. -/
theorem vb_norm_lower {w : ℂ} (hw : 0 < w.re) (t : ℝ) :
    w.re / (2 * (1 + ‖w‖)) * (1 + |t|) ≤ ‖w + I * t‖ := by
  have h1 : w.re ≤ ‖w + I * t‖ := by
    have := Complex.re_le_norm (w + I * t)
    simpa using this
  have h2 : |t| - ‖w‖ ≤ ‖w + I * t‖ := by
    have := norm_sub_norm_le (I * (t : ℂ)) (-w)
    rw [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, norm_neg, one_mul,
      sub_neg_eq_add, add_comm] at this
    exact this
  have hw1 : 0 < 1 + ‖w‖ := by positivity
  set c := w.re / (2 * (1 + ‖w‖)) with hc
  have hc0 : 0 ≤ c := by positivity
  have hcw : c * (2 * (1 + ‖w‖)) = w.re := by rw [hc]; field_simp
  have hre : w.re ≤ ‖w‖ := Complex.re_le_norm w
  have hc2 : c ≤ 1 / 2 := by
    rw [hc, div_le_iff₀ (by positivity)]
    linarith
  rcases le_or_gt |t| (2 * ‖w‖ + 1) with ht | ht
  · nlinarith
  · nlinarith [abs_nonneg t]

/-- A linear upper bound for `‖w + i t‖`. -/
theorem vb_norm_upper (w : ℂ) (t : ℝ) : ‖w + I * t‖ ≤ (1 + ‖w‖) * (1 + |t|) := by
  have h := norm_add_le w (I * (t : ℂ))
  rw [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul] at h
  nlinarith [norm_nonneg w, abs_nonneg t]

/-- `‖w + i t‖ ^ (-σ)` is bounded by a multiple of `(1 + |t|) ^ (-σ)`. -/
theorem vb_rpow_le {w : ℂ} (hw : 0 < w.re) (σ : ℝ) (t : ℝ) :
    ‖w + I * t‖ ^ (-σ) ≤
      max ((w.re / (2 * (1 + ‖w‖))) ^ (-σ)) ((1 + ‖w‖) ^ (-σ)) * (1 + |t|) ^ (-σ) := by
  set c₁ := w.re / (2 * (1 + ‖w‖))
  set c₂ := 1 + ‖w‖
  set u := 1 + |t|
  have hu : 0 < u := by positivity
  have hc₁ : 0 < c₁ := by positivity
  have hlo := vb_norm_lower hw t
  have hup := vb_norm_upper w t
  set x := ‖w + I * t‖
  have hx : x = x / u * u := by field_simp
  have hq1 : c₁ ≤ x / u := by rw [le_div_iff₀ hu]; exact hlo
  have hq2 : x / u ≤ c₂ := by rw [div_le_iff₀ hu]; exact hup
  have hq0 : 0 < x / u := lt_of_lt_of_le hc₁ hq1
  rw [hx, Real.mul_rpow hq0.le hu.le]
  gcongr
  rcases le_total 0 (-σ) with hσ | hσ
  · exact (Real.rpow_le_rpow hq0.le hq2 hσ).trans (le_max_right _ _)
  · exact (Real.rpow_le_rpow_of_nonpos hc₁ hq1 hσ).trans (le_max_left _ _)

/-- `z - it = z + i(-t)`. -/
theorem vb_sub_eq (z : ℂ) (t : ℝ) : z - I * t = z + I * ((-t : ℝ) : ℂ) := by
  push_cast; ring

/-- The real majorant `‖w + i t‖^{-α} ‖z - i t‖^{-β}` is integrable when `α + β > 1`. -/
theorem vb_integrable_rpow {w z : ℂ} (hw : 0 < w.re) (hz : 0 < z.re) {α β : ℝ}
    (h : 1 < α + β) :
    Integrable (fun t : ℝ => ‖w + I * t‖ ^ (-α) * ‖z - I * t‖ ^ (-β)) := by
  set C₁ := max ((w.re / (2 * (1 + ‖w‖))) ^ (-α)) ((1 + ‖w‖) ^ (-α))
  set C₂ := max ((z.re / (2 * (1 + ‖z‖))) ^ (-β)) ((1 + ‖z‖) ^ (-β))
  have hint : Integrable (fun t : ℝ => (1 + ‖t‖) ^ (-(α + β))) :=
    integrable_one_add_norm (by simp; linarith)
  refine (hint.const_mul (C₁ * C₂)).mono' (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  refine Eventually.of_forall fun t => ?_
  have h1 := vb_rpow_le hw α t
  have h2 := vb_rpow_le hz β (-t)
  rw [← vb_sub_eq, abs_neg] at h2
  have hu : 0 < 1 + |t| := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.norm_eq_abs,
    neg_add, Real.rpow_add hu]
  calc ‖w + I * t‖ ^ (-α) * ‖z - I * t‖ ^ (-β)
      ≤ (C₁ * (1 + |t|) ^ (-α)) * (C₂ * (1 + |t|) ^ (-β)) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = C₁ * C₂ * ((1 + |t|) ^ (-α) * (1 + |t|) ^ (-β)) := by ring

/-- `‖x ^ c‖ ≤ e^{π |Im c| / 2} ‖x‖ ^ {Re c}` on the right half-plane. -/
theorem vb_norm_cpow_le {x : ℂ} (hx : 0 < x.re) (c : ℂ) :
    ‖x ^ c‖ ≤ Real.exp (π / 2 * |c.im|) * ‖x‖ ^ c.re := by
  have hx0 : x ≠ 0 := fun h => by simp [h] at hx
  rw [norm_cpow_of_ne_zero hx0, div_eq_mul_inv, ← Real.exp_neg, mul_comm]
  gcongr
  have harg : |arg x| ≤ π / 2 := abs_arg_le_pi_div_two_iff.mpr hx.le
  have := neg_abs_le (arg x * c.im)
  rw [abs_mul] at this
  nlinarith [abs_nonneg c.im, abs_nonneg (arg x)]

/-- For `x > 0` and `σ₁ ≤ σ ≤ σ₂`, `x^(-σ) ≤ x^(-σ₁) + x^(-σ₂)`. -/
theorem vb_rpow_le_add {x σ σ₁ σ₂ : ℝ} (hx : 0 < x) (h₁ : σ₁ ≤ σ) (h₂ : σ ≤ σ₂) :
    x ^ (-σ) ≤ x ^ (-σ₁) + x ^ (-σ₂) := by
  rcases le_total 1 x with h | h
  · have := Real.rpow_le_rpow_of_exponent_le h (neg_le_neg h₁)
    linarith [Real.rpow_nonneg hx.le (-σ₂)]
  · have := Real.rpow_le_rpow_of_exponent_ge hx h (neg_le_neg h₂)
    linarith [Real.rpow_nonneg hx.le (-σ₁)]

/-- The integrand of Cauchy's vertical Beta integral. -/
def vbF (a b w z : ℂ) (t : ℝ) : ℂ := (w + I * t) ^ (-a) * (z - I * t) ^ (-b)

/-- `Re(z - it) > 0` when `Re z > 0`. -/
theorem vb_re_sub {z : ℂ} (hz : 0 < z.re) (t : ℝ) : 0 < (z - I * t).re := by simpa using hz

/-- `Re(w + it) > 0` when `Re w > 0`. -/
theorem vb_re_add {w : ℂ} (hw : 0 < w.re) (t : ℝ) : 0 < (w + I * t).re := by simpa using hw

/-- Bound on the integrand `(w + it)^(-a) (z - it)^(-b)` of 5.12.8 by `e^(π|Im a|/2) e^(π|Im b|/2)
|w + it|^(-Re a) |z - it|^(-Re b)`. -/
theorem vb_norm_vbF_le {a b w z : ℂ} (hw : 0 < w.re) (hz : 0 < z.re) (t : ℝ) :
    ‖vbF a b w z t‖ ≤ Real.exp (π / 2 * |a.im|) * Real.exp (π / 2 * |b.im|) *
      (‖w + I * t‖ ^ (-a.re) * ‖z - I * t‖ ^ (-b.re)) := by
  unfold vbF
  rw [norm_mul]
  have h1 := vb_norm_cpow_le (vb_re_add hw t) (-a)
  have h2 := vb_norm_cpow_le (vb_re_sub hz t) (-b)
  simp only [neg_im, abs_neg, neg_re] at h1 h2
  calc ‖(w + I * t) ^ (-a)‖ * ‖(z - I * t) ^ (-b)‖
      ≤ (Real.exp (π / 2 * |a.im|) * ‖w + I * t‖ ^ (-a.re)) *
        (Real.exp (π / 2 * |b.im|) * ‖z - I * t‖ ^ (-b.re)) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- The integrand `vbF a b w z` of 5.12.8 is measurable. -/
theorem vb_measurable_vbF (a b w z : ℂ) : Measurable (vbF a b w z) := by
  unfold vbF; fun_prop

/-- A parametric integral of functions holomorphic in the parameter, locally dominated by an
integrable function, is holomorphic. -/
theorem vb_differentiableOn_integral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {U : Set ℂ} (hU : IsOpen U) {F : ℂ → α → ℂ}
    (hmeas : ∀ z ∈ U, AEStronglyMeasurable (F z) μ)
    (hdiff : ∀ᵐ x ∂μ, DifferentiableOn ℂ (fun z => F z x) U)
    (hbound : ∀ z₀ ∈ U, ∃ ε > 0, Metric.closedBall z₀ ε ⊆ U ∧ ∃ g : α → ℝ, Integrable g μ ∧
      ∀ᵐ x ∂μ, ∀ z ∈ Metric.closedBall z₀ ε, ‖F z x‖ ≤ g x) :
    DifferentiableOn ℂ (fun z => ∫ x, F z x ∂μ) U := by
  apply Complex.differentiableOn_integral_of_locally_dominated hU hmeas hdiff
  intro z₀ hz₀
  obtain ⟨ε, hε, _, g, hg, hgb⟩ := hbound z₀ hz₀
  exact ⟨Metric.closedBall z₀ ε, Metric.closedBall_mem_nhds z₀ hε, g, hg, hgb⟩

/-- The vertical Beta integral is holomorphic in `b` on `Re (a + b) > 1`. -/
theorem vb_differentiableOn_b {a w z : ℂ} (hw : 0 < w.re) (hz : 0 < z.re) :
    DifferentiableOn ℂ (fun b => ∫ t, vbF a b w z t) {b : ℂ | 1 - a.re < b.re} := by
  have hU : IsOpen {b : ℂ | 1 - a.re < b.re} := isOpen_lt continuous_const continuous_re
  refine vb_differentiableOn_integral hU
    (fun b _ => (vb_measurable_vbF a b w z).aestronglyMeasurable)
    (Eventually.of_forall fun t b _ => ?_) fun b₀ hb₀ => ?_
  · have hne : z - I * t ≠ 0 := fun h => by
      have := vb_re_sub hz t; rw [h] at this; simp at this
    unfold vbF
    exact ((differentiableAt_id.neg.const_cpow (Or.inl hne)).const_mul _).differentiableWithinAt
  · have hb₀' : 1 - a.re < b₀.re := hb₀
    set ε := (b₀.re - (1 - a.re)) / 2 with hε
    have hε0 : 0 < ε := by rw [hε]; linarith
    have hball : ∀ b ∈ Metric.closedBall b₀ ε,
        b₀.re - ε ≤ b.re ∧ b.re ≤ b₀.re + ε ∧ |b.im| ≤ |b₀.im| + ε := by
      intro b hb
      rw [Metric.mem_closedBall, dist_eq_norm] at hb
      have h1 := abs_re_le_norm (b - b₀)
      have h2 := abs_im_le_norm (b - b₀)
      rw [sub_re] at h1
      rw [sub_im] at h2
      have h3 := abs_sub_abs_le_abs_sub b.im b₀.im
      refine ⟨?_, ?_, ?_⟩ <;>
        [linarith [(abs_le.mp (h1.trans hb)).1]; linarith [(abs_le.mp (h1.trans hb)).2];
          linarith]
    refine ⟨ε, hε0, fun b hb => ?_, ?_⟩
    · have := (hball b hb).1
      show 1 - a.re < b.re
      linarith
    set K := Real.exp (π / 2 * |a.im|) * Real.exp (π / 2 * (|b₀.im| + ε))
    refine ⟨fun t => K * (‖w + I * t‖ ^ (-a.re) * ‖z - I * t‖ ^ (-(b₀.re - ε)) +
      ‖w + I * t‖ ^ (-a.re) * ‖z - I * t‖ ^ (-(b₀.re + ε))), ?_, ?_⟩
    · refine Integrable.const_mul (Integrable.add ?_ ?_) K
      · exact vb_integrable_rpow hw hz (by linarith)
      · exact vb_integrable_rpow hw hz (by linarith)
    · refine Eventually.of_forall fun t b hb => ?_
      obtain ⟨h1, h2, h3⟩ := hball b hb
      have hx : 0 < ‖z - I * t‖ := norm_pos_iff.mpr fun h => by
        have := vb_re_sub hz t; rw [h] at this; simp at this
      have hQ := vb_rpow_le_add (σ := b.re) hx h1 h2
      have hE : Real.exp (π / 2 * |b.im|) ≤ Real.exp (π / 2 * (|b₀.im| + ε)) :=
        Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
      refine (vb_norm_vbF_le hw hz t).trans ?_
      have hP : 0 ≤ ‖w + I * t‖ ^ (-a.re) := by positivity
      calc Real.exp (π / 2 * |a.im|) * Real.exp (π / 2 * |b.im|) *
            (‖w + I * t‖ ^ (-a.re) * ‖z - I * t‖ ^ (-b.re))
          ≤ K * (‖w + I * t‖ ^ (-a.re) *
              (‖z - I * t‖ ^ (-(b₀.re - ε)) + ‖z - I * t‖ ^ (-(b₀.re + ε)))) := by
            apply mul_le_mul _ (mul_le_mul_of_nonneg_left hQ hP) (by positivity) (by positivity)
            exact mul_le_mul_of_nonneg_left hE (by positivity)
        _ = _ := by ring

/-- Laplace representation of `x^{-a}`. -/
theorem vb_cpow_neg_eq_integral {a x : ℂ} (ha : 0 < a.re) (hx : 0 < x.re) :
    x ^ (-a) = (Complex.Gamma a)⁻¹ * ∫ s in Ioi (0 : ℝ), (s : ℂ) ^ (a - 1) * cexp (-(x * s)) := by
  rw [integral_cpow_mul_cexp_neg_mul_Ioi ha hx, ← mul_assoc,
    inv_mul_cancel₀ (Complex.Gamma_ne_zero_of_re_pos ha), one_mul]

/-- For `Re b, Re z > 0`, `v^(b-1) e^(-zv)` is integrable on `(0, ∞)`. -/
theorem vb_integrableOn_cpow_exp {b z : ℂ} (hb : 0 < b.re) (hz : 0 < z.re) :
    IntegrableOn (fun v : ℝ => (v : ℂ) ^ (b - 1) * cexp (-(z * v))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := b.re - 1) (b := z.re)
    (by linarith) one_pos hz
  refine Integrable.mono' h (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hv, Complex.norm_exp, Real.rpow_one]
  simp

/-- The Fourier transform of `(z - i t)^{-b}`, by Fourier inversion. -/
theorem vb_fourier_inner {b z : ℂ} (hb : 1 < b.re) (hz : 0 < z.re) {s : ℝ} (hs : 0 < s) :
    ∫ t : ℝ, cexp (-(I * t * s)) * (z - I * t) ^ (-b) =
      2 * π * (Complex.Gamma b)⁻¹ * ((s : ℂ) ^ (b - 1) * cexp (-(z * s))) := by
  set g : ℝ → ℂ := indicator (Ioi 0) fun v => (v : ℂ) ^ (b - 1) * cexp (-(z * v)) with hg
  have hgi : Integrable g :=
    (vb_integrableOn_cpow_exp (by linarith) hz).integrable_indicator measurableSet_Ioi
  have hF : ∀ ξ : ℝ, 𝓕 g ξ = Complex.Gamma b * (z + I * ((2 * π * ξ : ℝ) : ℂ)) ^ (-b) := by
    intro ξ
    rw [Real.fourier_real_eq_integral_exp_smul]
    have hfun : (fun v : ℝ => cexp (((-2 * π * v * ξ : ℝ) : ℂ) * I) • g v) =
        indicator (Ioi 0) fun v : ℝ =>
          (v : ℂ) ^ (b - 1) * cexp (-((z + I * ((2 * π * ξ : ℝ) : ℂ)) * v)) := by
      funext v
      by_cases hv : v ∈ Ioi (0 : ℝ)
      · rw [hg, indicator_of_mem hv, indicator_of_mem hv, smul_eq_mul, mul_left_comm,
          ← Complex.exp_add]
        congr 2
        push_cast
        ring
      · rw [hg, indicator_of_notMem hv, indicator_of_notMem hv, smul_zero]
    rw [hfun, MeasureTheory.integral_indicator measurableSet_Ioi,
      integral_cpow_mul_cexp_neg_mul_Ioi (by linarith) (by simpa using hz)]
  have hFi : Integrable (𝓕 g) := by
    have h0 := vb_integrable_rpow (w := 1) (z := z) (α := 0) (β := b.re) (by simp) hz
      (by linarith)
    simp only [neg_zero, Real.rpow_zero, one_mul] at h0
    have h1 := h0.comp_mul_left' (R := -2 * π) (by positivity)
    have h2 := h1.const_mul (‖Complex.Gamma b‖ * Real.exp (π / 2 * |b.im|))
    refine h2.mono' ?_ (Eventually.of_forall fun ξ => ?_)
    · rw [show 𝓕 g = fun ξ : ℝ => Complex.Gamma b * (z + I * ((2 * π * ξ : ℝ) : ℂ)) ^ (-b) from
        funext hF]
      exact Measurable.aestronglyMeasurable (by fun_prop)
    · rw [hF, norm_mul]
      have hre : 0 < (z + I * ((2 * π * ξ : ℝ) : ℂ)).re := by simpa using hz
      have := vb_norm_cpow_le hre (-b)
      simp only [neg_im, abs_neg, neg_re] at this
      have he : z + I * ((2 * π * ξ : ℝ) : ℂ) = z - I * ((-2 * π * ξ : ℝ) : ℂ) := by
        push_cast; ring
      rw [he] at this
      calc ‖Complex.Gamma b‖ * ‖(z + I * ((2 * π * ξ : ℝ) : ℂ)) ^ (-b)‖
          ≤ ‖Complex.Gamma b‖ * (Real.exp (π / 2 * |b.im|) *
              ‖z - I * ((-2 * π * ξ : ℝ) : ℂ)‖ ^ (-b.re)) := by
            rw [he]; exact mul_le_mul_of_nonneg_left this (norm_nonneg _)
        _ = _ := by ring
  have hcont : ContinuousAt g s := by
    have hh : ContinuousAt (fun v : ℝ => (v : ℂ) ^ (b - 1) * cexp (-(z * v))) s :=
      (continuousAt_ofReal_cpow_const s (b - 1) (Or.inr hs.ne')).mul (by fun_prop)
    refine hh.congr (Filter.eventuallyEq_of_mem (Ioi_mem_nhds hs) fun v hv => ?_)
    rw [hg, indicator_of_mem hv]
  have hinv := hgi.fourierInv_fourier_eq hFi hcont
  rw [Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul] at hinv
  simp_rw [hF, smul_eq_mul] at hinv
  rw [hg, indicator_of_mem (show s ∈ Ioi (0 : ℝ) from hs)] at hinv
  set G : ℝ → ℂ := fun ξ => cexp (((-2 * π * ξ * -s : ℝ) : ℂ) * I) *
    (Complex.Gamma b * (z + I * ((2 * π * ξ : ℝ) : ℂ)) ^ (-b)) with hG
  have hcv := Measure.integral_comp_mul_left G (-1 / (2 * π))
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hGc : ∀ t : ℝ, G (-1 / (2 * π) * t) =
      Complex.Gamma b * (cexp (-(I * t * s)) * (z - I * t) ^ (-b)) := by
    intro t
    simp only [hG]
    have e1 : (((-2 * π * (-1 / (2 * π) * t) * -s : ℝ) : ℂ) * I) = -(I * t * s) := by
      push_cast; field_simp
    have e2 : z + I * ((2 * π * (-1 / (2 * π) * t) : ℝ) : ℂ) = z - I * t := by
      push_cast; field_simp; ring
    rw [e1, e2]; ring
  simp_rw [hGc] at hcv
  rw [MeasureTheory.integral_const_mul] at hcv
  have hab : |(-1 / (2 * π))⁻¹| = 2 * π := by
    rw [inv_div, abs_div, abs_neg, abs_one, div_one, abs_of_pos (by positivity)]
  rw [hab, ← hG] at hcv
  change ∫ ξ, G ξ = _ at hinv
  rw [hinv, Complex.real_smul] at hcv
  have hΓ : Complex.Gamma b ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
  rw [← mul_right_inj' hΓ, hcv]
  push_cast
  field_simp

/-- The base case `Re a > 0`, `Re b > 1` of 5.12.8, by Fubini and `vb_fourier_inner`. -/
theorem vb_base {a b w z : ℂ} (ha : 0 < a.re) (hb : 1 < b.re) (hw : 0 < w.re) (hz : 0 < z.re) :
    ∫ t, vbF a b w z t = 2 * π * ((Complex.Gamma a)⁻¹ * (Complex.Gamma b)⁻¹ *
      (Complex.Gamma (a + b - 1) * (w + z) ^ (-(a + b - 1)))) := by
  set H : ℝ → ℝ → ℂ := fun t s =>
    (s : ℂ) ^ (a - 1) * cexp (-((w + I * t) * s)) * (z - I * t) ^ (-b) with hH
  have h1 : ∀ t, vbF a b w z t = (Complex.Gamma a)⁻¹ * ∫ s in Ioi (0 : ℝ), H t s := by
    intro t
    simp only [vbF, hH]
    rw [vb_cpow_neg_eq_integral ha (vb_re_add hw t), mul_assoc, MeasureTheory.integral_mul_const]
  simp_rw [h1]
  rw [MeasureTheory.integral_const_mul]
  have hHint : Integrable (Function.uncurry H) (volume.prod (volume.restrict (Ioi 0))) := by
    have hf : Integrable (fun t : ℝ => Real.exp (π / 2 * |b.im|) * ‖z - I * t‖ ^ (-b.re)) := by
      have h0 := vb_integrable_rpow (w := 1) (z := z) (α := 0) (β := b.re) (by simp) hz
        (by linarith)
      simp only [neg_zero, Real.rpow_zero, one_mul] at h0
      exact h0.const_mul _
    have hg : Integrable (fun s : ℝ => s ^ (a.re - 1) * Real.exp (-w.re * s))
        (volume.restrict (Ioi 0)) := by
      have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := a.re - 1) (b := w.re)
        (by linarith) one_pos hw
      simp only [Real.rpow_one] at this
      exact this
    refine (hf.mul_prod hg).mono' (Measurable.aestronglyMeasurable (by simp only [hH]; fun_prop))
      ?_
    have hμ : (volume : Measure ℝ).prod (volume.restrict (Ioi (0 : ℝ))) =
        ((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict
          (univ ×ˢ Ioi (0 : ℝ)) := by
      rw [← Measure.prod_restrict, Measure.restrict_univ]
    rw [hμ]
    filter_upwards [ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Ioi)] with p hp
    have hs : 0 < p.2 := hp.2
    show ‖H p.1 p.2‖ ≤ _
    simp only [hH]
    rw [norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos hs, Complex.norm_exp]
    have hn := vb_norm_cpow_le (vb_re_sub hz p.1) (-b)
    simp only [neg_im, abs_neg, neg_re] at hn
    have hre : (-((w + I * (p.1 : ℂ)) * (p.2 : ℂ))).re = -w.re * p.2 := by simp
    rw [hre, sub_re, one_re]
    calc p.2 ^ (a.re - 1) * Real.exp (-w.re * p.2) * ‖(z - I * (p.1 : ℂ)) ^ (-b)‖
        ≤ p.2 ^ (a.re - 1) * Real.exp (-w.re * p.2) *
          (Real.exp (π / 2 * |b.im|) * ‖z - I * (p.1 : ℂ)‖ ^ (-b.re)) :=
          mul_le_mul_of_nonneg_left hn (by positivity)
      _ = _ := by ring
  rw [integral_integral_swap hHint]
  have h2 : ∀ s ∈ Ioi (0 : ℝ), ∫ t, H t s = 2 * π * (Complex.Gamma b)⁻¹ *
      ((s : ℂ) ^ ((a + b - 1) - 1) * cexp (-((w + z) * s))) := by
    intro s hs
    have hs' : (0 : ℝ) < s := hs
    have hsplit : ∀ t : ℝ, H t s = ((s : ℂ) ^ (a - 1) * cexp (-(w * s))) *
        (cexp (-(I * t * s)) * (z - I * t) ^ (-b)) := by
      intro t
      simp only [hH]
      rw [show -((w + I * (t : ℂ)) * s) = -(w * s) + -(I * t * s) by ring, Complex.exp_add]
      ring
    simp_rw [hsplit]
    rw [MeasureTheory.integral_const_mul, vb_fourier_inner hb hz hs']
    have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs'.ne'
    have hcp : (s : ℂ) ^ ((a + b - 1) - 1) = (s : ℂ) ^ (a - 1) * (s : ℂ) ^ (b - 1) := by
      rw [← cpow_add _ _ hs0]; ring_nf
    have hex : cexp (-((w + z) * s)) = cexp (-(w * s)) * cexp (-(z * s)) := by
      rw [← Complex.exp_add]; ring_nf
    rw [hcp, hex]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi h2, MeasureTheory.integral_const_mul,
    integral_cpow_mul_cexp_neg_mul_Ioi (by simp; linarith) (by simp; linarith)]
  ring

/-- The right-hand side of 5.12.8. -/
def vbR (a b w z : ℂ) : ℂ :=
  (w + z) ^ (1 - a - b) * Complex.Gamma (a + b) /
    ((a + b - 1) * Complex.Gamma a * Complex.Gamma b)

/-- DLMF 5.12.8 for `Re a > 0`, `Re b > 1`: `(1/2π) ∫ (w + it)^(-a)(z - it)^(-b) dt = (w +
z)^(1-a-b) Γ(a + b) / ((a + b - 1) Γ(a) Γ(b))`. -/
theorem vb_eq_base {a b w z : ℂ} (ha : 0 < a.re) (hb : 1 < b.re) (hw : 0 < w.re)
    (hz : 0 < z.re) : (1 / (2 * π)) * ∫ t, vbF a b w z t = vbR a b w z := by
  rw [vb_base ha hb hw hz, vbR]
  have hs : a + b - 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hΓ : Complex.Gamma (a + b) = (a + b - 1) * Complex.Gamma (a + b - 1) := by
    rw [← Complex.Gamma_add_one _ hs]; ring_nf
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have ha0 := Complex.Gamma_ne_zero_of_re_pos ha
  have hb0 := Complex.Gamma_ne_zero_of_re_pos (show 0 < b.re by linarith)
  rw [hΓ, show (1 : ℂ) - a - b = -(a + b - 1) by ring]
  field_simp

/-- The right-hand side `vbR a b w z` of 5.12.8 is holomorphic in `b` on `Re b > 1 - Re a`. -/
theorem vb_differentiableOn_vbR {a w z : ℂ} (hw : 0 < w.re) (hz : 0 < z.re) :
    DifferentiableOn ℂ (fun b => vbR a b w z) {b : ℂ | 1 - a.re < b.re} := by
  intro b hb
  have hb' : 1 - a.re < b.re := hb
  have hwz : w + z ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hs : a + b - 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hfun : (fun b => vbR a b w z) = fun b => (w + z) ^ (1 - a - b) *
      Complex.Gamma (a + b) * (a + b - 1)⁻¹ * (Complex.Gamma a)⁻¹ * (Complex.Gamma b)⁻¹ := by
    funext b; rw [vbR, div_eq_mul_inv, mul_inv, mul_inv]; ring
  rw [hfun]
  refine DifferentiableAt.differentiableWithinAt ?_
  have hG : DifferentiableAt ℂ (fun b => Complex.Gamma (a + b)) b := by
    refine (Complex.differentiableAt_Gamma _ fun m h => ?_).comp b
      ((differentiableAt_const a).add differentiableAt_id)
    have := congrArg Complex.re h; simp at this
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have h1 : DifferentiableAt ℂ (fun b => (w + z) ^ (1 - a - b)) b :=
    ((differentiableAt_const _).sub differentiableAt_id).const_cpow (Or.inl hwz)
  have h3 : DifferentiableAt ℂ (fun b => (a + b - 1)⁻¹) b :=
    (((differentiableAt_const a).add differentiableAt_id).sub (differentiableAt_const 1)).inv hs
  exact (((h1.mul hG).mul h3).mul (differentiableAt_const _)).mul
    (Complex.differentiable_one_div_Gamma b)

/-- 5.12.8 for `Re a > 0`, by analytic continuation in `b` from `vb_eq_base`. -/
theorem vb_eq_of_re_pos {a b w z : ℂ} (ha : 0 < a.re) (hab : 1 < (a + b).re) (hw : 0 < w.re)
    (hz : 0 < z.re) : (1 / (2 * π)) * ∫ t, vbF a b w z t = vbR a b w z := by
  set U : Set ℂ := {b : ℂ | 1 - a.re < b.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const continuous_re
  have hL : AnalyticOnNhd ℂ (fun b => (1 / (2 * π)) * ∫ t, vbF a b w z t) U :=
    ((vb_differentiableOn_b hw hz).const_mul _).analyticOnNhd hUo
  have hR : AnalyticOnNhd ℂ (fun b => vbR a b w z) U :=
    (vb_differentiableOn_vbR hw hz).analyticOnNhd hUo
  have h2 : (2 : ℂ) ∈ U := by show 1 - a.re < (2 : ℂ).re; simp; linarith
  have hev : (fun b => (1 / (2 * π)) * ∫ t, vbF a b w z t) =ᶠ[𝓝 2] fun b => vbR a b w z := by
    have hV : {b : ℂ | 1 < b.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (by simp)
    filter_upwards [hV] with b hb
    exact vb_eq_base ha hb hw hz
  have hbU : b ∈ U := by show 1 - a.re < b.re; simp at hab; linarith
  exact hL.eqOn_of_preconnected_of_eventuallyEq hR (convex_halfSpace_re_gt _).isPreconnected
    h2 hev hbU

/-- Swapping `(a, w)` with `(b, z)` leaves the integral of 5.12.8 unchanged. -/
theorem vb_integral_symm (a b w z : ℂ) : ∫ t, vbF a b w z t = ∫ t, vbF b a z w t := by
  have h := Measure.integral_comp_mul_left (vbF b a z w) (-1)
  rw [inv_neg, inv_one, abs_neg, abs_one, one_smul] at h
  rw [← h]
  congr 1
  funext t
  simp only [vbF]
  push_cast
  ring_nf

end VerticalBeta

/-- Cauchy's vertical Beta integral. `1/B(a,b)` is written as `Γ(a+b)/(Γ(a)Γ(b))`: Mathlib's
`betaIntegral a b` is the literal integral, which is `0` when `Re a ≤ 0` or `Re b ≤ 0`, while
the identity holds for all `a, b` with `Re (a + b) > 1`. -/
@[dlmf 5.12.E8]
theorem beta_vertical {a b : ℂ} {w z : ℂ} (hw : 0 < w.re) (hz : 0 < z.re)
    (hab : 1 < (a + b).re) :
    (1 / (2 * π)) * ∫ t : ℝ,
        1 / ((w + I * t) ^ a * (z - I * t) ^ b) =
      (w + z) ^ (1 - a - b) * Complex.Gamma (a + b) /
        ((a + b - 1) * Complex.Gamma a * Complex.Gamma b) := by
  have hfun : (fun t : ℝ => 1 / ((w + I * t) ^ a * (z - I * t) ^ b)) = vbF a b w z := by
    funext t; rw [vbF, one_div, mul_inv, cpow_neg, cpow_neg]
  rw [hfun]
  rcases lt_or_ge 0 a.re with ha | ha
  · exact vb_eq_of_re_pos ha hab hw hz
  · have hb : 0 < b.re := by simp at hab; linarith
    rw [vb_integral_symm, vb_eq_of_re_pos hb (by rwa [add_comm]) hz hw, vbR,
      show (1 : ℂ) - b - a = 1 - a - b by ring, add_comm z w, add_comm b a]
    ring

end DLMF.Gamma

end
end
