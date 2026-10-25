/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.EllipticIntegrals.LegendreIdentities
public import DLMF.JacobiElliptic.SpecialValues
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Carlson.TwoVariable.R.ElementaryValues
public import Carlson.TwoVariable.Reduction

/-!
# Special cases of Legendre's integrals and of `R_C` (DLMF §19.6)

Statements of DLMF 19.6.1–19.6.15. DLMF's "`= ∞`" entries are stated as divergence of the norm
(or of the real part, for the real third-kind integrals) along the relevant one-sided limit;
DLMF's `lim_{φ→0} F(φ, k)/φ = 1` etc. are limits along `𝓝[≠] 0`. The third-kind integrals with
real `α² > 1` are Cauchy principal values (DLMF 19.6(i), 19.6(iv)); `c = csc²φ`.
`R_C` is ACQ19C's `symEllIntRC` (DLMF 19.2.17, principal value for `y < 0`).

The inverse Gudermannian of DLMF 19.6.8 is `gd⁻¹(φ) = ∫₀^φ sec t dt` (DLMF 4.23.41;
`DLMF.Elementary.inverseGudermannian`), written out here as that integral, and also as
`arsinh(tan φ)`.
-/

@[expose] public noncomputable section

open Complex Set Filter
open scoped Real Topology

namespace DLMF.EllipticIntegrals

open DLMF.JacobiElliptic

/-! ### §19.6(i) Complete elliptic integrals -/

theorem ei19a_jacobiComodulusk_zero : jacobiComodulusk 0 = 1 := by simp [jacobiComodulusk]

theorem ei19a_jacobiComodulusk_one : jacobiComodulusk 1 = 0 := by simp [jacobiComodulusk]

/-- `segmentIntegral f φ / φ → f 0` as `φ → 0` when `f` is continuous near `0`. -/
theorem p19lR1_tendsto_segmentIntegral_div {f : ℂ → ℂ} (hf : ∀ᶠ z in 𝓝 0, ContinuousAt f z) :
    Tendsto (fun φ => ei19a_segmentIntegral f φ / φ) (𝓝[≠] 0) (𝓝 (f 0)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨r, hr, hfr⟩ := Metric.eventually_nhds_iff_ball.1 hf
  obtain ⟨δ, hδ, hδf⟩ := Metric.continuousAt_iff.1 (hfr 0 (Metric.mem_ball_self hr)) (ε / 2)
    (half_pos hε)
  refine ⟨min r δ, lt_min hr hδ, fun φ hφ hφr => ?_⟩
  have hφ0 : φ ≠ 0 := hφ
  rw [dist_zero_right] at hφr
  have hball : ∀ t ∈ Icc (0 : ℝ) 1, ‖(t : ℂ) * φ‖ < min r δ := fun t ht => by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
    calc t * ‖φ‖ ≤ 1 * ‖φ‖ := by gcongr; exact ht.2
      _ < _ := by rwa [one_mul]
  have hcont : ContinuousOn (fun t : ℝ => f (t * φ)) (Icc 0 1) := by
    intro t ht
    have hm : (t : ℂ) * φ ∈ Metric.ball (0 : ℂ) r := by
      rw [Metric.mem_ball, dist_zero_right]
      exact (hball t ht).trans_le (min_le_left _ _)
    have h1 := hfr _ hm
    have h2 : ContinuousAt (fun t : ℝ => (t : ℂ) * φ) t := by fun_prop
    exact (ContinuousAt.comp (g := f) (f := fun t : ℝ => (t : ℂ) * φ) h1 h2).continuousWithinAt
  have hint : IntervalIntegrable (fun t : ℝ => f (t * φ)) MeasureTheory.volume 0 1 :=
    (hcont.mono (by rw [uIcc_of_le zero_le_one])).intervalIntegrable
  have heq : ei19a_segmentIntegral f φ / φ = ∫ t in (0 : ℝ)..1, f (t * φ) := by
    rw [ei19a_segmentIntegral, intervalIntegral.integral_const_mul]
    field_simp
  rw [heq, dist_eq_norm]
  have h2 : (∫ t in (0 : ℝ)..1, f (t * φ)) - f 0 = ∫ t in (0 : ℝ)..1, (f (t * φ) - f 0) := by
    rw [intervalIntegral.integral_sub hint intervalIntegrable_const]; simp
  rw [h2]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := ε / 2) fun t ht => ?_).trans_lt
    ?_
  · rw [uIoc_of_le zero_le_one] at ht
    have hm : dist ((t : ℂ) * φ) 0 < δ := by
      rw [dist_zero_right]
      exact (hball t (Ioc_subset_Icc_self ht)).trans_le (min_le_right _ _)
    have := hδf hm
    rw [dist_eq_norm] at this; exact this.le
  · simp; linarith

/-- `(1 - a sin²θ)^s` is continuous near `θ = 0`. -/
theorem p19lR1_eventually_continuousAt_cpow (a s : ℂ) :
    ∀ᶠ z in 𝓝 (0 : ℂ), ContinuousAt (fun θ => (1 - a * Complex.sin θ ^ 2) ^ s) z := by
  have hc : Continuous fun θ : ℂ => 1 - a * Complex.sin θ ^ 2 := by fun_prop
  have h0 : (fun θ : ℂ => 1 - a * Complex.sin θ ^ 2) 0 ∈ slitPlane := by simp
  filter_upwards [hc.continuousAt.preimage_mem_nhds (isOpen_slitPlane.mem_nhds h0)] with z hz
  exact (hc.continuousAt).cpow continuousAt_const hz

/-- For `|φ| < π/2`, `cos φ > 0`. -/
theorem p19lR1_cos_pos {φ : ℝ} (hφ : |φ| < π / 2) : 0 < Real.cos φ :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [neg_abs_le φ], by linarith [le_abs_self φ]⟩

/-- `∫₀^φ sec θ dθ = arsinh(tan φ)` for `|φ| < π/2`. -/
theorem p19lR1_integral_sec {φ : ℝ} (hφ : |φ| < π / 2) :
    ∫ θ in (0 : ℝ)..φ, (Real.cos θ)⁻¹ = Real.arsinh (Real.tan φ) := by
  have hsub : ∀ θ ∈ uIcc (0 : ℝ) φ, |θ| < π / 2 := by
    intro θ hθ
    rcases le_total 0 φ with h | h
    · rw [uIcc_of_le h] at hθ
      rw [abs_lt] at hφ ⊢; constructor <;> linarith [hθ.1, hθ.2]
    · rw [uIcc_of_ge h] at hθ
      rw [abs_lt] at hφ ⊢; constructor <;> linarith [hθ.1, hθ.2]
  have hd : ∀ θ ∈ uIcc (0 : ℝ) φ,
      HasDerivAt (fun θ => Real.arsinh (Real.tan θ)) (Real.cos θ)⁻¹ θ := by
    intro θ hθ
    have hc := p19lR1_cos_pos (hsub θ hθ)
    have h := (Real.hasDerivAt_arsinh (Real.tan θ)).comp θ (Real.hasDerivAt_tan hc.ne')
    refine h.congr_deriv ?_
    have h1 : 1 + Real.tan θ ^ 2 = (Real.cos θ)⁻¹ ^ 2 := by
      rw [Real.tan_eq_sin_div_cos]; field_simp; linarith [Real.sin_sq_add_cos_sq θ]
    rw [h1, Real.sqrt_sq (inv_nonneg.2 hc.le)]
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd]
  · simp
  · refine ContinuousOn.intervalIntegrable ?_
    exact ContinuousOn.inv₀ Real.continuous_cos.continuousOn fun θ hθ =>
      (p19lR1_cos_pos (hsub θ hθ)).ne'

/-- `Re cos z = cos(Re z) cosh(Im z)`. -/
theorem p19lR1_cos_re (z : ℂ) : (Complex.cos z).re = Real.cos z.re * Real.cosh z.im := by
  conv_lhs => rw [← Complex.re_add_im z, Complex.cos_add_mul_I]
  simp [← Complex.ofReal_cos, ← Complex.ofReal_cosh, ← Complex.ofReal_sin, ← Complex.ofReal_sinh]

/-- DLMF 19.6.1: `K(0) = E(0) = K'(1) = E'(1) = π/2`. -/
@[dlmf 19.6.E1]
theorem compEllInt_special_pi_div_two :
    compEllIntKk 0 = π / 2 ∧ compEllIntEk 0 = π / 2 ∧ cCompEllIntKk 1 = π / 2 ∧
      cCompEllIntEk 1 = π / 2 := by
  have hE0 : compEllIntEk 0 = π / 2 := by
    rw [compEllIntEk_eq_integral]; simp
  refine ⟨by simp [compEllIntKk], hE0, ?_, ?_⟩
  · rw [(cCompEllIntKk_of_re_pos (k := 1) (Or.inl (by simp))).1, compEllIntKk_jacobiComodulusk]
    simp [compEllIntKpk]
  · rw [(cCompEllIntKk_of_re_pos (k := 1) (Or.inl (by simp))).2, ei19a_jacobiComodulusk_one, hE0]

/-- DLMF 19.6.1: `E(1) = E'(0) = 1`. -/
@[dlmf 19.6.E1]
theorem compEllInt_special_one : compEllIntEk 1 = 1 ∧ cCompEllIntEk 0 = 1 := by
  have h1 : compEllIntEk 1 = 1 := by
    rw [compEllIntEk_eq_ofReal (m := 1) (by simp) le_rfl, DLMF.Elliptic.Real.compEllIntEm_one,
      ofReal_one]
  refine ⟨h1, ?_⟩
  rw [(cCompEllIntKk_of_re_pos (k := 0) (Or.inr (by simp))).2, ei19a_jacobiComodulusk_zero, h1]

/-- DLMF 19.6.1: `K(1) = ∞`, as `|K(k)| → ∞` for `k → 1-` (from the admitted
`DLMF.JacobiElliptic.tendsto_norm_compEllIntKk_one`). -/
@[dlmf 19.6.E1]
theorem tendsto_norm_compEllIntKk_one' :
    Tendsto (fun k : ℝ => ‖compEllIntKk k‖) (𝓝[<] 1) atTop :=
  tendsto_norm_compEllIntKk_one

/-- DLMF 19.6.1: `K'(0) = ∞`, as `|K'(k)| → ∞` for `k → 0+` (from the admitted
`DLMF.JacobiElliptic.tendsto_norm_compEllIntKpk_zero`). -/
@[dlmf 19.6.E1]
theorem tendsto_norm_cCompEllIntKk_zero :
    Tendsto (fun k : ℝ => ‖cCompEllIntKk k‖) (𝓝[>] 0) atTop := by
  refine tendsto_norm_compEllIntKpk_zero.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with k hk
  rw [(cCompEllIntKk_of_re_pos (k := k) (Or.inl (by simpa using hk))).1,
    compEllIntKk_jacobiComodulusk]

/-- `Δ(θ) = (1 - k² sin²θ)^{1/2}` for real `θ`. -/
abbrev p19lR1_Δ (k : ℂ) (θ : ℝ) : ℂ := (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (1 / 2 : ℂ)

/-- `Δ² = 1 - k² sin²θ`. -/
theorem p19lR1_Δ_sq (k : ℂ) (θ : ℝ) : p19lR1_Δ k θ ^ 2 = 1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2 := by
  rw [p19lR1_Δ, sq, ei19c_cpow_half_sq]

/-- `Δ ≠ 0` in the principal domain. -/
theorem p19lR1_Δ_ne_zero {k : ℂ} (hk : 1 - k ^ 2 ∈ slitPlane) (θ : ℝ) : p19lR1_Δ k θ ≠ 0 := by
  have h := ei19a_one_sub_sq_mul_sin_sq_mem_slitPlane hk θ
  rw [p19lR1_Δ, Ne, cpow_eq_zero_iff]; exact fun h' => slitPlane_ne_zero h h'.1

/-- `(1 - k² sin²θ)^{-1/2} = Δ⁻¹`. -/
theorem p19lR1_cpow_neg_half {k : ℂ} (θ : ℝ) :
    (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) = (p19lR1_Δ k θ)⁻¹ := by
  rw [cpow_neg]

/-- `Δ′ = -k² sin θ cos θ / Δ`. -/
theorem p19lR1_hasDerivAt_Δ {k : ℂ} (hk : 1 - k ^ 2 ∈ slitPlane) (θ : ℝ) :
    HasDerivAt (p19lR1_Δ k) (-(k ^ 2 * Real.sin θ * Real.cos θ) * (p19lR1_Δ k θ)⁻¹) θ := by
  have hb : HasDerivAt (fun θ : ℝ => 1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2)
      (-(k ^ 2 * (2 * Real.sin θ * Real.cos θ))) θ := by
    have := ((Real.hasDerivAt_sin θ).ofReal_comp.pow 2).const_mul (k ^ 2) |>.const_sub 1
    convert this using 1; push_cast; ring
  have h := (Complex.hasStrictDerivAt_cpow_const (c := (1 / 2 : ℂ))
    (ei19a_one_sub_sq_mul_sin_sq_mem_slitPlane hk θ)).hasDerivAt.comp θ hb
  refine h.congr_deriv ?_
  rw [show (1 / 2 : ℂ) - 1 = -(1 / 2) by norm_num, p19lR1_cpow_neg_half]
  ring

/-- `Δ` is continuous in the principal domain. -/
theorem p19lR1_continuous_Δ {k : ℂ} (hk : 1 - k ^ 2 ∈ slitPlane) : Continuous (p19lR1_Δ k) :=
  continuous_iff_continuousAt.2 fun θ => (p19lR1_hasDerivAt_Δ hk θ).continuousAt

/-- `∫₀^φ Δ⁻³ dθ = (E(φ, k) - k² sin φ cos φ/Δ(φ))/k′²` for real `φ`. -/
theorem p19lR1_integral_cube {k : ℂ} (hk : 1 - k ^ 2 ∈ slitPlane) (φ : ℝ) :
    ∫ θ in (0 : ℝ)..φ, (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2)⁻¹ *
        (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) =
      (incEllIntEk φ k - k ^ 2 * Real.sin φ * Real.cos φ / p19lR1_Δ k φ) / (1 - k ^ 2) := by
  have hk0 : (1 - k ^ 2) ≠ 0 := slitPlane_ne_zero hk
  set A : ℝ → ℂ := fun θ => ((∫ x in (0 : ℝ)..θ, p19lR1_Δ k x) -
    k ^ 2 * ((Real.sin θ : ℂ) * Real.cos θ / p19lR1_Δ k θ)) / (1 - k ^ 2) with hA
  have hd : ∀ θ : ℝ, HasDerivAt A ((1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2)⁻¹ *
      (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))) θ := by
    intro θ
    have hΔ := p19lR1_hasDerivAt_Δ hk θ
    have hΔ0 := p19lR1_Δ_ne_zero hk θ
    have hI := ((p19lR1_continuous_Δ hk).integral_hasStrictDerivAt 0 θ).hasDerivAt
    have hs := (Real.hasDerivAt_sin θ).ofReal_comp
    have hc := (Real.hasDerivAt_cos θ).ofReal_comp
    have h := ((hI.sub (((hs.mul hc).div hΔ hΔ0).const_mul (k ^ 2))).div_const (1 - k ^ 2))
    refine h.congr_deriv ?_
    rw [p19lR1_cpow_neg_half, ← p19lR1_Δ_sq]
    have hsc : (Real.sin θ : ℂ) ^ 2 + (Real.cos θ : ℂ) ^ 2 = 1 := by
      exact_mod_cast Real.sin_sq_add_cos_sq θ
    have h2 := p19lR1_Δ_sq k θ
    simp only [Pi.mul_apply, ofReal_neg]
    field_simp
    linear_combination (p19lR1_Δ k θ ^ 2 + (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) +
      k ^ 2 * ((Real.sin θ : ℂ) ^ 2 - (Real.cos θ : ℂ) ^ 2)) * h2 - k ^ 2 * hsc
  have hfun : (fun θ : ℝ => (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2)⁻¹ *
      (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))) =
      fun θ => (p19lR1_Δ k θ ^ 2)⁻¹ * (p19lR1_Δ k θ)⁻¹ := by
    funext θ; rw [p19lR1_cpow_neg_half, p19lR1_Δ_sq]
  have hcont : Continuous fun θ => (p19lR1_Δ k θ ^ 2)⁻¹ * (p19lR1_Δ k θ)⁻¹ := by
    have := p19lR1_continuous_Δ hk
    exact ((this.pow 2).inv₀ fun θ => pow_ne_zero 2 (p19lR1_Δ_ne_zero hk θ)).mul
      (this.inv₀ (p19lR1_Δ_ne_zero hk))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hd θ)
    (by rw [hfun]; exact hcont.intervalIntegrable _ _)]
  simp only [hA, intervalIntegral.integral_same, Real.sin_zero, ofReal_zero, zero_mul, zero_div,
    mul_zero, sub_zero, incEllIntEk_ofReal_eq_integral]
  ring

/-- `∫₀^φ sec²θ Δ⁻¹ dθ = F(φ, k) - (E(φ, k) - Δ(φ) tan φ)/k′²` for real `|φ| < π/2`. -/
theorem p19lR1_integral_sec_sq {k : ℂ} (hk : 1 - k ^ 2 ∈ slitPlane) {φ : ℝ} (hφ : |φ| < π / 2) :
    ∫ θ in (0 : ℝ)..φ, (1 - 1 * (Real.sin θ : ℂ) ^ 2)⁻¹ *
        (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) =
      incEllIntFk φ k - (incEllIntEk φ k - p19lR1_Δ k φ * Real.tan φ) / (1 - k ^ 2) := by
  have hk0 : (1 - k ^ 2) ≠ 0 := slitPlane_ne_zero hk
  have hsub : ∀ θ ∈ uIcc (0 : ℝ) φ, Real.cos θ ≠ 0 := by
    intro θ hθ
    refine (Real.cos_pos_of_mem_Ioo ?_).ne'
    rcases le_total 0 φ with h | h
    · rw [uIcc_of_le h] at hθ
      rw [abs_lt] at hφ; constructor <;> linarith [hθ.1, hθ.2]
    · rw [uIcc_of_ge h] at hθ
      rw [abs_lt] at hφ; constructor <;> linarith [hθ.1, hθ.2]
  set B : ℝ → ℂ := fun θ => (∫ x in (0 : ℝ)..θ, (p19lR1_Δ k x)⁻¹) -
    ((∫ x in (0 : ℝ)..θ, p19lR1_Δ k x) - p19lR1_Δ k θ * ((Real.sin θ : ℂ) / Real.cos θ)) /
      (1 - k ^ 2) with hB
  have hcΔi : Continuous fun θ => (p19lR1_Δ k θ)⁻¹ :=
    (p19lR1_continuous_Δ hk).inv₀ (p19lR1_Δ_ne_zero hk)
  have hd : ∀ θ ∈ uIcc (0 : ℝ) φ, HasDerivAt B ((1 - 1 * (Real.sin θ : ℂ) ^ 2)⁻¹ *
      (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))) θ := by
    intro θ hθ
    have hc0 : (Real.cos θ : ℂ) ≠ 0 := by exact_mod_cast hsub θ hθ
    have hΔ := p19lR1_hasDerivAt_Δ hk θ
    have hΔ0 := p19lR1_Δ_ne_zero hk θ
    have hI := ((p19lR1_continuous_Δ hk).integral_hasStrictDerivAt 0 θ).hasDerivAt
    have hJ := (hcΔi.integral_hasStrictDerivAt 0 θ).hasDerivAt
    have hs := (Real.hasDerivAt_sin θ).ofReal_comp
    have hc := (Real.hasDerivAt_cos θ).ofReal_comp
    have h := hJ.sub ((hI.sub (hΔ.mul (hs.div hc hc0))).div_const (1 - k ^ 2))
    refine h.congr_deriv ?_
    rw [p19lR1_cpow_neg_half]
    have hsc : (Real.sin θ : ℂ) ^ 2 + (Real.cos θ : ℂ) ^ 2 = 1 := by
      exact_mod_cast Real.sin_sq_add_cos_sq θ
    have h2 := p19lR1_Δ_sq k θ
    have h1 : (1 - 1 * (Real.sin θ : ℂ) ^ 2) = (Real.cos θ : ℂ) ^ 2 := by
      linear_combination -hsc
    rw [h1]
    simp only [ofReal_neg, Pi.div_apply]
    field_simp
    linear_combination (Real.sin θ : ℂ) ^ 2 * h2 +
      (1 - k ^ 2 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) * hsc
  have hint : IntervalIntegrable (fun θ : ℝ => (1 - 1 * (Real.sin θ : ℂ) ^ 2)⁻¹ *
      (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))) MeasureTheory.volume 0 φ := by
    have hfun : (fun θ : ℝ => (1 - 1 * (Real.sin θ : ℂ) ^ 2)⁻¹ *
        (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))) =
        fun θ => ((Real.cos θ : ℂ) ^ 2)⁻¹ * (p19lR1_Δ k θ)⁻¹ := by
      funext θ
      rw [p19lR1_cpow_neg_half]
      have hsc : (Real.sin θ : ℂ) ^ 2 + (Real.cos θ : ℂ) ^ 2 = 1 := by
        exact_mod_cast Real.sin_sq_add_cos_sq θ
      congr 2; linear_combination -hsc
    rw [hfun]
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.mul ?_ hcΔi.continuousOn
    exact ContinuousOn.inv₀ (by fun_prop) fun θ hθ => pow_ne_zero 2 (by exact_mod_cast hsub θ hθ)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
  simp only [hB, intervalIntegral.integral_same, Real.sin_zero, Real.cos_zero, ofReal_zero,
    ofReal_one, zero_div, mul_zero, sub_zero, incEllIntEk_ofReal_eq_integral,
    incEllIntFk_ofReal_eq_integral, p19lR1_cpow_neg_half, Real.tan_eq_sin_div_cos, ofReal_div]

/-- For real `φ`, `Π(φ, α², k)` is the interval integral when `1 - α² sin²θ` is bounded away from `0`. -/
theorem p19lR1_incEllIntPik_ofReal {φ : ℝ} {α2 k : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (h : ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖1 - α2 * (Real.sin (t * φ) : ℂ) ^ 2‖) :
    incEllIntPik φ α2 k = ∫ θ in (0 : ℝ)..φ, (1 - α2 * (Real.sin θ : ℂ) ^ 2)⁻¹ *
        (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) := by
  rw [incEllIntPik_eq_segmentIntegral hδ (fun t ht => by
    rw [← ofReal_mul, ← ofReal_sin]; exact h t ht), ei19a_segmentIntegral_ofReal]
  simp only [← Complex.ofReal_sin]

/-- In the principal domain `1 - k² sin²θ` is bounded away from `0` for real `θ`. -/
theorem p19lR1_exists_norm_lower {k : ℂ} (hk : 1 - k ^ 2 ∈ slitPlane) :
    ∃ δ > 0, ∀ θ : ℝ, δ ≤ ‖1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2‖ := by
  obtain ⟨u0, hu0, hmin⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_isMinOn
    (nonempty_Icc.2 zero_le_one)
    (by fun_prop : Continuous fun u : ℝ => ‖1 - k ^ 2 * (u : ℂ)‖).continuousOn
  refine ⟨‖1 - k ^ 2 * (u0 : ℂ)‖, norm_pos_iff.2 (slitPlane_ne_zero
    (ei19a_one_sub_mul_mem_slitPlane hk hu0.1 hu0.2)), fun θ => ?_⟩
  have := hmin (show Real.sin θ ^ 2 ∈ Icc (0 : ℝ) 1 from ⟨sq_nonneg _, Real.sin_sq_le_one θ⟩)
  simpa using this

/-- DLMF 19.6.2: `Π(k², k) = E(k)/k'²` (DLMF: `k² < 1`; here the principal domain
`1 - k² ∈ ℂ \ (-∞, 0]`). -/
@[dlmf 19.6.E2]
theorem compEllIntPik_sq_self {k : ℂ} (hk : 1 - k ^ 2 ∈ slitPlane) :
    compEllIntPik (k ^ 2) k = compEllIntEk k / (1 - k ^ 2) := by
  obtain ⟨δ, hδ, h⟩ := p19lR1_exists_norm_lower hk
  rw [compEllIntPik, show ((π : ℂ) / 2) = ((π / 2 : ℝ) : ℂ) by push_cast; ring,
    p19lR1_incEllIntPik_ofReal hδ (fun t _ => h _), p19lR1_integral_cube hk, compEllIntEk]
  simp

theorem incEllIntPik_special_k' {φ : ℝ} (hφ : |φ| < π / 2) {k : ℂ} (hk : 1 - k ^ 2 ∈ slitPlane) :
    incEllIntPik φ (k ^ 2) k = (incEllIntEk φ k - k ^ 2 * Real.sin φ * Real.cos φ /
        (1 - k ^ 2 * (Real.sin φ : ℂ) ^ 2) ^ (1 / 2 : ℂ)) / (1 - k ^ 2) ∧
      incEllIntPik φ 1 k = incEllIntFk φ k - (incEllIntEk φ k -
        (1 - k ^ 2 * (Real.sin φ : ℂ) ^ 2) ^ (1 / 2 : ℂ) * Real.tan φ) / (1 - k ^ 2) := by
  obtain ⟨δ, hδ, h⟩ := p19lR1_exists_norm_lower hk
  refine ⟨by rw [p19lR1_incEllIntPik_ofReal hδ (fun t _ => h _), p19lR1_integral_cube hk], ?_⟩
  have hc : 0 < Real.cos φ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [neg_abs_le φ], by linarith [le_abs_self φ]⟩
  have hcθ : ∀ t ∈ Icc (0 : ℝ) 1, Real.cos φ ≤ Real.cos (t * φ) := by
    intro t ht
    rw [← Real.cos_abs (t * φ), ← Real.cos_abs φ]
    refine Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) ?_
    rw [abs_mul, abs_of_nonneg ht.1]; exact mul_le_of_le_one_left (abs_nonneg _) ht.2
  rw [p19lR1_incEllIntPik_ofReal (δ := Real.cos φ ^ 2) (by positivity), p19lR1_integral_sec_sq hk hφ]
  intro t ht
  have : (1 - 1 * (Real.sin (t * φ) : ℂ) ^ 2) = ((Real.cos (t * φ) ^ 2 : ℝ) : ℂ) := by
    have h1 : (Real.sin (t * φ) : ℂ) ^ 2 + (Real.cos (t * φ) : ℂ) ^ 2 = 1 := by
      exact_mod_cast Real.sin_sq_add_cos_sq (t * φ)
    rw [ofReal_pow]
    linear_combination -h1
  rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have := hcθ t ht
  nlinarith

/-- **Admitted.** DLMF 19.6.2: `Π(-k, k) = π/(4(1 + k)) + K(k)/2` for real `k` with `k² < 1`. -/
@[dlmf 19.6.E2]
theorem compEllIntPik_neg_self {k : ℝ} (hk : k ^ 2 < 1) :
    compEllIntPik (-k) k = π / (4 * (1 + k)) + compEllIntKk k / 2 := by
  sorry

/-- DLMF 19.6.13 (first relation): `Π(φ, 0, k) = F(φ, k)` for all complex `φ`, `k`. -/
@[dlmf 19.6.E13]
theorem incEllIntPik_zero (φ k : ℂ) : incEllIntPik φ 0 k = incEllIntFk φ k := by
  rw [incEllIntPik_eq_segmentIntegral (δ := 1) one_pos (fun t _ => by simp), incEllIntFk]
  simp

/-- DLMF 19.6.3: `Π(α², 0) = π/(2√(1 - α²))` for real `α² < 1`, and `Π(0, k) = K(k)`. -/
@[dlmf 19.6.E3]
theorem compEllIntPik_special {α2 : ℝ} (hα : α2 < 1) (k : ℂ) :
    compEllIntPik α2 0 = π / (2 * Real.sqrt (1 - α2)) ∧ compEllIntPik 0 k = compEllIntKk k := by
  constructor
  · rw [compEllIntPik, show ((π : ℂ) / 2) = ((π / 2 : ℝ) : ℂ) by push_cast; ring,
      incEllIntPik_eq_ofReal (m := 0) (by simp) zero_le_one hα,
      ← DLMF.Elliptic.Real.compEllIntPim, DLMF.Elliptic.Real.compEllIntPim_param_zero hα]
    push_cast; ring
  · rw [compEllIntPik, incEllIntPik_zero, compEllIntKk_eq_incEllIntFk]

/-- **Admitted.** DLMF 19.6.4: for real `k` with `k² < 1`, `Π(α², k) → +∞` as `α² → 1-`; for real
`α² < 1`, `Π(α², k) → +∞` as `k² → 1-` (`∞ · sign(1 - α²)`; the case `α² > 1` is in 19.6.6). -/
@[dlmf 19.6.E4]
theorem tendsto_compEllIntPik {k α2 : ℝ} (hk : k ^ 2 < 1) (hα : α2 < 1) :
    Tendsto (fun a : ℝ => (compEllIntPik a k).re) (𝓝[<] 1) atTop ∧
      Tendsto (fun k : ℝ => (compEllIntPik α2 k).re) (𝓝[<] 1) atTop := by
  sorry

/-- **Admitted.** DLMF 19.6.5: for real `1 < α²` and real `k` with `k² < 1`, the Cauchy principal
value satisfies `Π(α², k) = K(k) - Π(k²/α², k)`. -/
@[dlmf 19.6.E5]
theorem compEllIntPik_of_one_lt {α2 k : ℝ} (hα : 1 < α2) (hk : k ^ 2 < 1) :
    compEllIntPik α2 k = compEllIntKk k - compEllIntPik (k ^ 2 / α2 : ℝ) k := by
  sorry

/-- **Admitted.** DLMF 19.6.6: for real `1 < α²` (Cauchy principal values), `Π(α², 0) = 0`;
for real `k` with `k² < 1`, `Π(α², k) → K(k) - E(k)/k'²` as `α² → 1+`; and for `1 < α²`,
`Π(α², k) → -∞` as `k² → 1-`. -/
@[dlmf 19.6.E6]
theorem compEllIntPik_of_one_lt_special {α2 k : ℝ} (hα : 1 < α2) (hk : k ^ 2 < 1) :
    compEllIntPik α2 0 = 0 ∧
      Tendsto (fun a : ℝ => compEllIntPik a k) (𝓝[>] 1)
        (𝓝 (compEllIntKk k - compEllIntEk k / (1 - k ^ 2))) ∧
      Tendsto (fun k : ℝ => (compEllIntPik α2 k).re) (𝓝[<] 1) atBot := by
  sorry

/-! ### §19.6(ii) `F(φ, k)` -/

/-- DLMF 19.6.7: `F(0, k) = 0`, `F(φ, 0) = φ` and `F(π/2, k) = K(k)` for all complex `φ`, `k`. -/
@[dlmf 19.6.E7]
theorem incEllIntFk_special (φ k : ℂ) :
    incEllIntFk 0 k = 0 ∧ incEllIntFk φ 0 = φ ∧ incEllIntFk (π / 2) k = compEllIntKk k := by
  refine ⟨by simp [incEllIntFk, ei19a_segmentIntegral], by simp [incEllIntFk,
    ei19a_segmentIntegral], (compEllIntKk_eq_incEllIntFk k).symm⟩

/-- For real `|φ| < π/2`, `F(φ, 1) = ∫₀^φ sec θ dθ = gd⁻¹(φ)` (DLMF 19.6.8, second equality, with
DLMF's definition 4.23.41 of `gd⁻¹`). -/
@[dlmf 19.6.E8]
theorem incEllIntFk_one_eq_integral_sec {φ : ℝ} (hφ : |φ| < π / 2) :
    incEllIntFk φ 1 = ((∫ θ in (0 : ℝ)..φ, (Real.cos θ)⁻¹ : ℝ) : ℂ) := by
  rw [incEllIntFk_eq_ofReal (m := 1) (by simp) le_rfl, DLMF.Elliptic.Real.incEllIntFm]
  congr 1
  refine intervalIntegral.integral_congr fun θ hθ => ?_
  have hθ' : |θ| < π / 2 := by
    rcases le_total 0 φ with h | h
    · rw [uIcc_of_le h] at hθ
      rw [abs_lt] at hφ ⊢; constructor <;> linarith [hθ.1, hθ.2]
    · rw [uIcc_of_ge h] at hθ
      rw [abs_lt] at hφ ⊢; constructor <;> linarith [hθ.1, hθ.2]
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [neg_abs_le θ],
    by linarith [le_abs_self θ]⟩
  rw [one_mul, ← Real.cos_sq', Real.rpow_neg (sq_nonneg _), ← Real.sqrt_eq_rpow,
    Real.sqrt_sq hc.le]

/-- DLMF 19.6.8: `F(φ, 1) = (sin φ) R_C(1, cos²φ) = gd⁻¹(φ) = arsinh(tan φ)` for
real `|φ| < π/2`. -/
@[dlmf 19.6.E8]
theorem incEllIntFk_one {φ : ℝ} (hφ : |φ| < π / 2) :
    incEllIntFk φ 1 = Real.sin φ * symEllIntRC 1 ((Real.cos φ : ℂ) ^ 2) ∧
      incEllIntFk φ 1 = (Real.arsinh (Real.tan φ) : ℂ) := by
  have h2 : incEllIntFk φ 1 = (Real.arsinh (Real.tan φ) : ℂ) := by
    rw [incEllIntFk_one_eq_integral_sec hφ, p19lR1_integral_sec hφ]
  refine ⟨?_, h2⟩
  have hc := p19lR1_cos_pos hφ
  set c := Real.cos φ
  have hl : 0 < c ^ 2 := by positivity
  have hx : ((1 + Real.tan φ ^ 2 : ℝ) : ℂ) ∈ slitPlane := by
    apply ofReal_mem_slitPlane.2; positivity
  have hRC := Carlson.TwoVariable.carlsonRC_mul_of_pos hl hx one_mem_slitPlane
  have e1 : ((c ^ 2 : ℝ) : ℂ) * ((1 + Real.tan φ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← ofReal_mul, Real.tan_eq_sin_div_cos]
    have : c ^ 2 * (1 + (Real.sin φ / c) ^ 2) = 1 := by
      field_simp; linarith [Real.sin_sq_add_cos_sq φ]
    rw [this, ofReal_one]
  have e2 : ((c ^ 2 : ℝ) : ℂ) * 1 = (c : ℂ) ^ 2 := by push_cast; ring
  rw [e1, e2] at hRC
  have e3 : ((c ^ 2 : ℝ) : ℂ) ^ (-1 / 2 : ℂ) = ((c⁻¹ : ℝ) : ℂ) := by
    rw [show (-1 / 2 : ℂ) = ((-(1 / 2) : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow hl.le,
      Real.rpow_neg hl.le, ← Real.sqrt_eq_rpow, Real.sqrt_sq hc.le]
  rw [symEllIntRC_eq_carlsonRC one_mem_slitPlane (by
      rw [← ofReal_pow]; exact ofReal_mem_slitPlane.2 hl), hRC, e3, h2,
    Carlson.TwoVariable.arsinh_eq_mul_carlsonRC (Real.tan φ), Real.tan_eq_sin_div_cos]
  push_cast
  rw [show ((c : ℝ) : ℂ) = Complex.cos φ from Complex.ofReal_cos φ]
  ring

/-- DLMF 19.6.7: `F(π/2, 1) = ∞`, as `|F(φ, 1)| → ∞` for real `φ → π/2-`; and
`lim_{φ→0} F(φ, k)/φ = 1`. -/
@[dlmf 19.6.E7]
theorem incEllIntFk_limits (k : ℂ) :
    Tendsto (fun φ : ℝ => ‖incEllIntFk φ 1‖) (𝓝[<] (π / 2)) atTop ∧
      Tendsto (fun φ : ℂ => incEllIntFk φ k / φ) (𝓝[≠] 0) (𝓝 1) := by
  refine ⟨?_, ?_⟩
  · have hA : Tendsto (fun φ : ℝ => Real.arsinh (Real.tan φ)) (𝓝[<] (π / 2)) atTop := by
      have hB : Tendsto Real.arsinh atTop atTop := by
        refine tendsto_atTop_atTop.2 fun b => ⟨Real.sinh b, fun x hx => ?_⟩
        rw [← Real.arsinh_sinh b]; exact Real.arsinh_le_arsinh.2 hx
      exact hB.comp Real.tendsto_tan_pi_div_two
    refine tendsto_atTop_mono' _ ?_ hA
    have hmem : Ioo (0 : ℝ) (π / 2) ∈ 𝓝[<] (π / 2) := Ioo_mem_nhdsLT (by positivity)
    filter_upwards [hmem] with φ hφ
    have habs : |φ| < π / 2 := by rw [abs_of_pos hφ.1]; exact hφ.2
    rw [(incEllIntFk_one habs).2, Complex.norm_real, Real.norm_eq_abs]
    exact le_abs_self _
  · have := p19lR1_tendsto_segmentIntegral_div
      (p19lR1_eventually_continuousAt_cpow (k ^ 2) (-(1 / 2)))
    simpa [incEllIntFk] using this

/-! ### §19.6(iii) `E(φ, k)` -/

/-- DLMF 19.6.9: `E(0, k) = 0`, `E(φ, 0) = φ`, `E(π/2, k) = E(k)` for all complex `φ`, `k`. -/
@[dlmf 19.6.E9]
theorem incEllIntEk_special (φ k : ℂ) :
    incEllIntEk 0 k = 0 ∧ incEllIntEk φ 0 = φ ∧ incEllIntEk (π / 2) k = compEllIntEk k :=
  ⟨by simp [incEllIntEk, ei19a_segmentIntegral], by simp [incEllIntEk, ei19a_segmentIntegral], rfl⟩

/-- DLMF 19.6.9: `E(φ, 1) = sin φ` for real `|φ| ≤ π/2` (for larger real `φ`, `E(φ, 1)` is
`∫₀^φ |cos θ| dθ ≠ sin φ`: the printed identity holds on DLMF's principal range); in particular
`E(π/2, 1) = 1`. -/
@[dlmf 19.6.E9]
theorem incEllIntEk_one {φ : ℝ} (hφ : |φ| ≤ π / 2) : incEllIntEk φ 1 = Real.sin φ := by
  rw [incEllIntEk_eq_ofReal (m := 1) (by simp) le_rfl, DLMF.Elliptic.Real.incEllIntEm]
  have h : ∀ θ ∈ uIcc (0 : ℝ) φ, (1 - 1 * Real.sin θ ^ 2) ^ (1 / 2 : ℝ) = Real.cos θ := by
    intro θ hθ
    have hθ' : |θ| ≤ π / 2 := by
      rcases le_total 0 φ with h | h
      · rw [uIcc_of_le h] at hθ
        rw [abs_le] at hφ ⊢; constructor <;> linarith [hθ.1, hθ.2]
      · rw [uIcc_of_ge h] at hθ
        rw [abs_le] at hφ ⊢; constructor <;> linarith [hθ.1, hθ.2]
    rw [one_mul, ← Real.cos_sq', ← Real.sqrt_eq_rpow, Real.sqrt_sq (Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [neg_abs_le θ], by linarith [le_abs_self θ]⟩)]
  rw [intervalIntegral.integral_congr h, integral_cos]
  simp

/-- DLMF 19.6.9: `E(π/2, 1) = 1`. -/
@[dlmf 19.6.E9]
theorem incEllIntEk_pi_div_two_one : incEllIntEk (π / 2) 1 = 1 := by
  have h := incEllIntEk_one (φ := π / 2) (by rw [abs_of_pos (by positivity)])
  rw [show ((π : ℂ) / 2) = ((π / 2 : ℝ) : ℂ) by push_cast; ring, h, Real.sin_pi_div_two,
    ofReal_one]

/-- DLMF 19.6.9 for complex amplitude: `E(φ, 1) = sin φ` when `|Re φ| < π/2`. -/
@[dlmf 19.6.E9]
theorem incEllIntEk_one_complex {φ : ℂ} (hφ : |φ.re| < π / 2) :
    incEllIntEk φ 1 = Complex.sin φ := by
  have hpt : ∀ t ∈ uIcc (0 : ℝ) 1,
      φ * (1 - (1 : ℂ) ^ 2 * Complex.sin (t * φ) ^ 2) ^ (1 / 2 : ℂ) = Complex.cos (t * φ) * φ := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    have hre : 0 < (Complex.cos (t * φ)).re := by
      rw [p19lR1_cos_re]
      refine mul_pos (Real.cos_pos_of_mem_Ioo ?_) (Real.cosh_pos _)
      have : (t * φ : ℂ).re = t * φ.re := by simp
      rw [this]
      have h1 : |t * φ.re| ≤ |φ.re| := by
        rw [abs_mul, abs_of_nonneg ht.1]; exact mul_le_of_le_one_left (abs_nonneg _) ht.2
      constructor <;> linarith [neg_abs_le (t * φ.re), le_abs_self (t * φ.re)]
    rw [one_pow, one_mul, ← Complex.cos_sq', show (1 / 2 : ℂ) = 2⁻¹ by norm_num,
      sq_cpow_two_inv hre, mul_comm]
  rw [incEllIntEk, ei19a_segmentIntegral, intervalIntegral.integral_congr hpt]
  have hd : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => Complex.sin (s * φ)) (Complex.cos (t * φ) * φ) t := by
    intro t _
    have h : HasDerivAt (fun z : ℂ => Complex.sin (z * φ)) (Complex.cos (t * φ) * φ) (t : ℂ) := by
      simpa using ((hasDerivAt_id (t : ℂ)).mul_const φ).csin
    exact h.comp_ofReal
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun s : ℝ => Complex.cos (s * φ) * φ).intervalIntegrable _ _)]
  simp

/-- DLMF 19.6.10: `lim_{φ→0} E(φ, k)/φ = 1`. -/
@[dlmf 19.6.E10]
theorem tendsto_incEllIntEk_div (k : ℂ) :
    Tendsto (fun φ : ℂ => incEllIntEk φ k / φ) (𝓝[≠] 0) (𝓝 1) := by
  have := p19lR1_tendsto_segmentIntegral_div (p19lR1_eventually_continuousAt_cpow (k ^ 2) (1/2))
  simpa [incEllIntEk] using this

/-! ### §19.6(iv) `Π(φ, α², k)` -/

/-- DLMF 19.6.11: `Π(0, α², k) = 0` and `Π(φ, 0, 0) = φ` for all complex `φ`, `α²`, `k`. -/
@[dlmf 19.6.E11]
theorem incEllIntPik_special (φ α2 k : ℂ) : incEllIntPik 0 α2 k = 0 ∧ incEllIntPik φ 0 0 = φ := by
  refine ⟨ei19a_pvSegmentIntegral_zero _ _, ?_⟩
  rw [incEllIntPik_zero, (incEllIntFk_special φ 0).2.1]

/-- DLMF 19.6.11: `Π(φ, 1, 0) = tan φ` for real `|φ| < π/2`. -/
@[dlmf 19.6.E11]
theorem incEllIntPik_one_zero {φ : ℝ} (hφ : |φ| < π / 2) :
    incEllIntPik φ 1 0 = Real.tan φ := by
  have hc : 0 < Real.cos φ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [neg_abs_le φ], by linarith [le_abs_self φ]⟩
  have hsub : ∀ θ ∈ uIcc (0 : ℝ) φ, |θ| ≤ |φ| := by
    intro θ hθ
    rcases le_total 0 φ with h | h
    · rw [uIcc_of_le h] at hθ
      rw [abs_of_nonneg h, abs_of_nonneg hθ.1]; exact hθ.2
    · rw [uIcc_of_ge h] at hθ
      rw [abs_of_nonpos h, abs_of_nonpos hθ.2]; linarith [hθ.1]
  have hcθ : ∀ θ ∈ uIcc (0 : ℝ) φ, Real.cos φ ≤ Real.cos θ := by
    intro θ hθ
    rw [← Real.cos_abs θ, ← Real.cos_abs φ]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos])
      (hsub θ hθ)
  rw [incEllIntPik_eq_segmentIntegral (δ := Real.cos φ ^ 2) (by positivity)]
  · rw [ei19a_segmentIntegral_ofReal]
    have hpt : ∀ θ ∈ uIcc (0 : ℝ) φ, (1 - (1 : ℂ) * Complex.sin (θ : ℂ) ^ 2)⁻¹ *
        (1 - (0 : ℂ) ^ 2 * Complex.sin (θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) =
          ((1 / Real.cos θ ^ 2 : ℝ) : ℂ) := by
      intro θ _
      simp only [one_mul, ← Complex.cos_sq', ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, zero_mul, sub_zero, one_cpow, mul_one]
      push_cast; simp
    rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_ofReal]
    congr 1
    have hd : ∀ θ ∈ uIcc (0 : ℝ) φ, HasDerivAt Real.tan (1 / Real.cos θ ^ 2) θ := fun θ hθ =>
      Real.hasDerivAt_tan (hc.trans_le (hcθ θ hθ)).ne'
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd]
    · simp
    · refine ContinuousOn.intervalIntegrable ?_
      refine ContinuousOn.div continuousOn_const (by fun_prop) fun θ hθ => ?_
      exact pow_ne_zero 2 (hc.trans_le (hcθ θ hθ)).ne'
  · intro t ht
    have hθ : (t * φ) ∈ uIcc (0 : ℝ) φ := by
      rcases le_total 0 φ with h | h
      · rw [uIcc_of_le h]; exact ⟨mul_nonneg ht.1 h, mul_le_of_le_one_left h ht.2⟩
      · rw [uIcc_of_ge h]; exact ⟨by nlinarith [ht.2], mul_nonpos_of_nonneg_of_nonpos ht.1 h⟩
    have : (1 - (1 : ℂ) * Complex.sin ((t : ℂ) * (φ : ℂ)) ^ 2) = ((Real.cos (t * φ) ^ 2 : ℝ) : ℂ) := by
      rw [one_mul, ← Complex.cos_sq']; push_cast; rfl
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have := hcθ _ hθ
    nlinarith

/-- **Admitted.** DLMF 19.6.12: with `c = csc²φ ≠ α²`, for real `0 < φ < π/2` and real `α²`
(Cauchy principal values when `α² > c`),
`Π(φ, α², 0) = R_C(c - 1, c - α²)`,
`Π(φ, α², 1) = (R_C(c, c - 1) - α² R_C(c, c - α²))/(1 - α²)` (`α² ≠ 1`), and
`Π(φ, 1, 1) = (R_C(c, c - 1) + √c/(c - 1))/2`. -/
@[dlmf 19.6.E12]
theorem incEllIntPik_special_RC {φ α2 : ℝ} (h0 : 0 < φ) (h1 : φ < π / 2)
    (hα : α2 ≠ 1 / Real.sin φ ^ 2) :
    incEllIntPik φ α2 0 =
        symEllIntRC (1 / Real.sin φ ^ 2 - 1 : ℝ) (1 / Real.sin φ ^ 2 - α2 : ℝ) ∧
      (α2 ≠ 1 → incEllIntPik φ α2 1 =
        (symEllIntRC (1 / Real.sin φ ^ 2 : ℝ) (1 / Real.sin φ ^ 2 - 1 : ℝ) -
          α2 * symEllIntRC (1 / Real.sin φ ^ 2 : ℝ) (1 / Real.sin φ ^ 2 - α2 : ℝ)) / (1 - α2)) ∧
      incEllIntPik φ 1 1 = (symEllIntRC (1 / Real.sin φ ^ 2 : ℝ) (1 / Real.sin φ ^ 2 - 1 : ℝ) +
        (Real.sqrt (1 / Real.sin φ ^ 2) / (1 / Real.sin φ ^ 2 - 1) : ℝ)) / 2 := by
  sorry

/-- DLMF 19.6.13: with `Δ = √(1 - k² sin²φ)`, for real `|φ| < π/2` and `k` in the
principal domain `1 - k² ∈ ℂ \ (-∞, 0]`,
`Π(φ, k², k) = (E(φ, k) - k² sin φ cos φ/Δ)/k'²` and
`Π(φ, 1, k) = F(φ, k) - (E(φ, k) - Δ tan φ)/k'²`. -/
@[dlmf 19.6.E13]
theorem incEllIntPik_special_k {φ : ℝ} (hφ : |φ| < π / 2) {k : ℂ} (hk : 1 - k ^ 2 ∈ slitPlane) :
    incEllIntPik φ (k ^ 2) k = (incEllIntEk φ k - k ^ 2 * Real.sin φ * Real.cos φ /
        (1 - k ^ 2 * (Real.sin φ : ℂ) ^ 2) ^ (1 / 2 : ℂ)) / (1 - k ^ 2) ∧
      incEllIntPik φ 1 k = incEllIntFk φ k - (incEllIntEk φ k -
        (1 - k ^ 2 * (Real.sin φ : ℂ) ^ 2) ^ (1 / 2 : ℂ) * Real.tan φ) / (1 - k ^ 2) := by
  obtain ⟨δ, hδ, h⟩ := p19lR1_exists_norm_lower hk
  refine ⟨by rw [p19lR1_incEllIntPik_ofReal hδ (fun t _ => h _), p19lR1_integral_cube hk], ?_⟩
  have hc : 0 < Real.cos φ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [neg_abs_le φ], by linarith [le_abs_self φ]⟩
  have hcθ : ∀ t ∈ Icc (0 : ℝ) 1, Real.cos φ ≤ Real.cos (t * φ) := by
    intro t ht
    rw [← Real.cos_abs (t * φ), ← Real.cos_abs φ]
    refine Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) ?_
    rw [abs_mul, abs_of_nonneg ht.1]; exact mul_le_of_le_one_left (abs_nonneg _) ht.2
  rw [p19lR1_incEllIntPik_ofReal (δ := Real.cos φ ^ 2) (by positivity), p19lR1_integral_sec_sq hk hφ]
  intro t ht
  have : (1 - 1 * (Real.sin (t * φ) : ℂ) ^ 2) = ((Real.cos (t * φ) ^ 2 : ℝ) : ℂ) := by
    have h1 : (Real.sin (t * φ) : ℂ) ^ 2 + (Real.cos (t * φ) : ℂ) ^ 2 = 1 := by
      exact_mod_cast Real.sin_sq_add_cos_sq (t * φ)
    rw [ofReal_pow]
    linear_combination -h1
  rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have := hcθ t ht
  nlinarith

/-- DLMF 19.6.14: `Π(π/2, α², k) = Π(α², k)`. -/
@[dlmf 19.6.E14]
theorem incEllIntPik_pi_div_two (α2 k : ℂ) : incEllIntPik (π / 2) α2 k = compEllIntPik α2 k := rfl

/-- DLMF 19.6.14: `lim_{φ→0} Π(φ, α², k)/φ = 1`. -/
@[dlmf 19.6.E14]
theorem tendsto_incEllIntPik_div (α2 k : ℂ) :
    Tendsto (fun φ : ℂ => incEllIntPik φ α2 k / φ) (𝓝[≠] 0) (𝓝 1) := by
  have hf : ∀ᶠ z in 𝓝 (0 : ℂ), ContinuousAt (fun θ => (1 - α2 * Complex.sin θ ^ 2)⁻¹ *
      (1 - k ^ 2 * Complex.sin θ ^ 2) ^ (-(1 / 2 : ℂ))) z := by
    have hc : Continuous fun θ : ℂ => 1 - α2 * Complex.sin θ ^ 2 := by fun_prop
    filter_upwards [p19lR1_eventually_continuousAt_cpow (k ^ 2) (-(1/2)),
      hc.continuousAt.preimage_mem_nhds (isOpen_ne.mem_nhds (by simp : (fun θ : ℂ =>
        1 - α2 * Complex.sin θ ^ 2) 0 ≠ 0))] with z h1 h2
    exact (hc.continuousAt.inv₀ h2).mul h1
  have := p19lR1_tendsto_segmentIntegral_div hf
  simp only [Complex.sin_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    sub_zero, inv_one, one_cpow, mul_one] at this
  refine this.congr' ?_
  -- near 0, the principal value is the ordinary integral
  have hc : Continuous fun θ : ℂ => ‖1 - α2 * Complex.sin θ ^ 2‖ := by fun_prop
  obtain ⟨r, hr, hfr⟩ := Metric.eventually_nhds_iff_ball.1
    (hc.continuousAt.preimage_mem_nhds (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) <
      ‖1 - α2 * Complex.sin 0 ^ 2‖)))
  filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds 0 hr)] with φ hφ
  rw [incEllIntPik_eq_segmentIntegral (δ := 1 / 2) (by norm_num)]
  intro t ht
  refine le_of_lt (hfr _ ?_)
  rw [Metric.mem_ball, dist_zero_right] at hφ ⊢
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
  calc t * ‖φ‖ ≤ 1 * ‖φ‖ := by gcongr; exact ht.2
    _ < _ := by rwa [one_mul]

/-! ### §19.6(v) `R_C(x, y)` -/

/-- **Admitted.** DLMF 19.6.15: `R_C(x, x) = x^{-1/2}` (`x ∈ ℂ \ (-∞, 0]`);
`R_C(λx, λy) = λ^{-1/2} R_C(x, y)` (real `λ > 0`, `x` not a negative real, `y ≠ 0`);
`R_C(0, y) = (π/2) y^{-1/2}` for `|ph y| < π`; and `R_C(0, y) = 0` for `y < 0` (principal
value). -/
@[dlmf 19.6.E15]
theorem symEllIntRC_special :
    (∀ x : ℂ, x ∈ slitPlane → symEllIntRC x x = x ^ (-(1 / 2 : ℂ))) ∧
      (∀ (l : ℝ) (x y : ℂ), 0 < l → symEllIntArg x → y ≠ 0 →
        symEllIntRC (l * x) (l * y) = (l : ℂ) ^ (-(1 / 2 : ℂ)) * symEllIntRC x y) ∧
      (∀ y : ℂ, y ∈ slitPlane → symEllIntRC 0 y = π / 2 * y ^ (-(1 / 2 : ℂ))) ∧
      (∀ y : ℝ, y < 0 → symEllIntRC 0 y = 0) := by
  sorry

/-- **Admitted.** DLMF 19.6.15: `R_C(x, y) → +∞` as `y → 0+` or `y → 0-`, for real `x > 0`. -/
@[dlmf 19.6.E15]
theorem tendsto_symEllIntRC_zero {x : ℝ} (hx : 0 < x) :
    Tendsto (fun y : ℝ => (symEllIntRC x y).re) (𝓝[≠] 0) atTop := by
  sorry

end DLMF.EllipticIntegrals
