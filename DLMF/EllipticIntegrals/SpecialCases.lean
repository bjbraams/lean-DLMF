/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.TwoVariable.R.ElementaryValues
public import Carlson.TwoVariable.Reduction
public import DLMF.EllipticIntegrals.Legendre
public import DLMF.EllipticIntegrals.LegendreIdentities
public import DLMF.EllipticIntegrals.LegendrePrincipalValue
public import DLMF.EllipticIntegrals.Symmetric
public import DLMF.JacobiElliptic.SpecialValues
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Special cases of Legendre's integrals and of `R_C` (DLMF §19.6)

Statements of DLMF 19.6.1–19.6.15: special values and limits of the complete and incomplete
Legendre integrals and of `R_C = symmetricEllipticRC` (DLMF 19.2.17, a principal value for `y < 0`).

## Main definitions

* `ellDelta`: `Δ(θ) = (1 - k² sin²θ)^{1/2}` for real `θ`.

## Main results

* `compEllInt_special_pi_div_two`, `compEllInt_special_one`, `tendsto_norm_completeEllipticK_one'`,
  `tendsto_norm_complementaryEllipticK_zero`: the values and infinities of DLMF 19.6.1.
* `completeEllipticPi_sq_self`, `completeEllipticPi_neg_self`: DLMF 19.6.2.
* `completeEllipticPi_special`, `tendsto_completeEllipticPi`: DLMF 19.6.3, 19.6.4.
* `completeEllipticPi_of_one_lt`, `completeEllipticPi_of_one_lt_special`: principal values for
  `α² > 1` (DLMF 19.6.5, 19.6.6).
* `incompleteEllipticF_special`, `incompleteEllipticF_limits`: DLMF 19.6.7.
* `incompleteEllipticF_one`, `incompleteEllipticF_one_eq_integral_sec`: `F(φ, 1) = gd⁻¹(φ)` (DLMF
  19.6.8).
* `incompleteEllipticE_special`, `incompleteEllipticE_one`, `incompleteEllipticE_one_complex`,
  `tendsto_incompleteEllipticE_div`: DLMF 19.6.9, 19.6.10.
* `incompleteEllipticPi_special`, `incompleteEllipticPi_one_zero`,
  `incompleteEllipticPi_special_RC`, `incompleteEllipticPi_special_k`, `incompleteEllipticPi_zero`:
  DLMF 19.6.11–19.6.13.
* `incompleteEllipticPi_pi_div_two`, `tendsto_incompleteEllipticPi_div`: DLMF 19.6.14.
* `symmetricEllipticRC_special`, `tendsto_symmetricEllipticRC_zero`: DLMF 19.6.15, including the
  homogeneity of the principal value `R_C(x, y)`, `y < 0`, for complex `x ∈ ℂ \ (-∞, 0]`.
* `tendsto_setIntegral_diff_Icc_nhdsGT`: excising a shrinking interval from an integrable
  function does not change the limit of its integral.
* `integral_inv_ellDelta_cube`: `∫₀^φ Δ⁻³ dθ` in terms of `E(φ, k)`.

## Implementation notes

DLMF's "`= ∞`" entries are stated as divergence of the norm (or of the real part, for the real
third-kind integrals) along the relevant one-sided limit; DLMF's `lim_{φ→0} F(φ, k)/φ = 1` etc.
are limits along `𝓝[≠] 0`. The third-kind integrals with real `α² > 1` are Cauchy principal
values (DLMF §19.6(i), §19.6(iv)); `c = csc²φ`.

The inverse Gudermannian of DLMF 19.6.8 is `gd⁻¹(φ) = ∫₀^φ sec t dt` (DLMF 4.23.41;
`DLMF.Elementary.inverseGudermannian`), written out here as that integral, and also as
`arsinh(tan φ)`.

## References

* NIST DLMF §19.6.
-/

@[expose] public noncomputable section

open Complex Set Filter
open scoped Real Topology

open DLMF.Core

namespace DLMF.EllipticIntegrals

open DLMF.JacobiElliptic

/-! ### §19.6(i) Complete elliptic integrals -/

/-- Identity under the stated parameter and domain assumptions: `jacobiComodulus 0 = 1`. -/
private lemma jacobiComodulus_zero : jacobiComodulus 0 = 1 := by simp [jacobiComodulus]

/-- Identity under the stated parameter and domain assumptions: `jacobiComodulus 1 = 0`. -/
private lemma jacobiComodulus_one : jacobiComodulus 1 = 0 := by simp [jacobiComodulus]

/-- `Core.primitive f φ / φ → f 0` as `φ → 0` when `f` is continuous near `0`. -/
private lemma tendsto_primitive_div {f : ℂ → ℂ} (hf : ∀ᶠ z in 𝓝 0, ContinuousAt f z) :
    Tendsto (fun φ => Core.primitive f φ / φ) (𝓝[≠] 0) (𝓝 (f 0)) := by
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
  have heq : Core.primitive f φ / φ = ∫ t in (0 : ℝ)..1, f (t * φ) := by
    rw [primitive_eq_integral, intervalIntegral.integral_const_mul]
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
private lemma eventually_continuousAt_one_sub_mul_sin_sq_cpow (a s : ℂ) :
    ∀ᶠ z in 𝓝 (0 : ℂ), ContinuousAt (fun θ => (1 - a * Complex.sin θ ^ 2) ^ s) z := by
  have hc : Continuous fun θ : ℂ => 1 - a * Complex.sin θ ^ 2 := by fun_prop
  have h0 : (fun θ : ℂ => 1 - a * Complex.sin θ ^ 2) 0 ∈ slitPlane := by simp
  filter_upwards [hc.continuousAt.preimage_mem_nhds (isOpen_slitPlane.mem_nhds h0)] with z hz
  exact (hc.continuousAt).cpow continuousAt_const hz

/-- For `|φ| < π/2`, `cos φ > 0`. -/
private lemma cos_pos_of_abs_lt_pi_div_two {φ : ℝ} (hφ : |φ| < π / 2) : 0 < Real.cos φ :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [neg_abs_le φ], by linarith [le_abs_self φ]⟩

/-- `∫₀^φ sec θ dθ = arsinh(tan φ)` for `|φ| < π/2`. -/
private lemma integral_inv_cos_eq_arsinh_tan {φ : ℝ} (hφ : |φ| < π / 2) :
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
    have hc := cos_pos_of_abs_lt_pi_div_two (hsub θ hθ)
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
      (cos_pos_of_abs_lt_pi_div_two (hsub θ hθ)).ne'

/-- `Re cos z = cos(Re z) cosh(Im z)`. -/
private lemma re_cos_eq_cos_mul_cosh (z : ℂ) : (Complex.cos z).re = Real.cos z.re *
    Real.cosh z.im := by
  conv_lhs => rw [← Complex.re_add_im z, Complex.cos_add_mul_I]
  simp [← Complex.ofReal_cos, ← Complex.ofReal_cosh, ← Complex.ofReal_sin, ← Complex.ofReal_sinh]

/-- DLMF 19.6.1: `K(0) = E(0) = K'(1) = E'(1) = π/2`. -/
@[dlmf 19.6.E1]
theorem compEllInt_special_pi_div_two :
    completeEllipticK 0 = π / 2 ∧ completeEllipticE 0 = π / 2 ∧ complementaryEllipticK 1 = π / 2 ∧
      complementaryEllipticE 1 = π / 2 := by
  have hE0 : completeEllipticE 0 = π / 2 := by
    rw [completeEllipticE_eq_integral]; simp
  refine ⟨by simp [completeEllipticK], hE0, ?_, ?_⟩
  · rw [(complementaryEllipticK_of_re_pos (k := 1) (Or.inl (by simp))).1,
        completeEllipticK_jacobiComodulusk]
    simp [completeEllipticKPrime]
  · rw [(complementaryEllipticK_of_re_pos (k := 1) (Or.inl (by simp))).2, jacobiComodulus_one, hE0]

/-- DLMF 19.6.1: `E(1) = E'(0) = 1`. -/
@[dlmf 19.6.E1]
theorem compEllInt_special_one : completeEllipticE 1 = 1 ∧ complementaryEllipticE 0 = 1 := by
  have h1 : completeEllipticE 1 = 1 := by
    rw [completeEllipticE_eq_ofReal (m := 1) (by simp) le_rfl,
        DLMF.Elliptic.Real.completeEllipticEOfParameter_one,
      ofReal_one]
  refine ⟨h1, ?_⟩
  rw [(complementaryEllipticK_of_re_pos (k := 0) (Or.inr (by simp))).2, jacobiComodulus_zero, h1]

/-- DLMF 19.6.1: `K(1) = ∞`, as `|K(k)| → ∞` for `k → 1-`. -/
@[dlmf 19.6.E1]
theorem tendsto_norm_completeEllipticK_one' :
    Tendsto (fun k : ℝ => ‖completeEllipticK k‖) (𝓝[<] 1) atTop :=
  tendsto_norm_completeEllipticK_one

/-- DLMF 19.6.1: `K'(0) = ∞`, as `|K'(k)| → ∞` for `k → 0+`. -/
@[dlmf 19.6.E1]
theorem tendsto_norm_complementaryEllipticK_zero :
    Tendsto (fun k : ℝ => ‖complementaryEllipticK k‖) (𝓝[>] 0) atTop := by
  refine tendsto_norm_completeEllipticKPrime_zero.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with k hk
  rw [(complementaryEllipticK_of_re_pos (k := k) (Or.inl (by simpa using hk))).1,
    completeEllipticK_jacobiComodulusk]

/-- `Δ(θ) = (1 - k² sin²θ)^{1/2}` for real `θ`. -/
abbrev ellDelta (k : ℂ) (θ : ℝ) : ℂ := (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (1 / 2 : ℂ)

/-- `Δ² = 1 - k² sin²θ`. -/
theorem ellDelta_sq (k : ℂ) (θ : ℝ) : ellDelta k θ ^ 2 = 1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2 := by
  rw [ellDelta, sq, cpow_half_mul_cpow_half]

/-- `Δ ≠ 0` in the principal domain. -/
theorem ellDelta_ne_zero {k : ℂ} (hk : 1 - k ^ 2 ∈ slitPlane) (θ : ℝ) : ellDelta k θ ≠ 0 := by
  have h := one_sub_sq_mul_sin_sq_mem_slitPlane hk θ
  rw [ellDelta, Ne, cpow_eq_zero_iff]; exact fun h' => slitPlane_ne_zero h h'.1

/-- `(1 - k² sin²θ)^{-1/2} = Δ⁻¹`. -/
private lemma one_sub_sq_mul_sin_sq_cpow_neg_half {k : ℂ} (θ : ℝ) :
    (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) = (ellDelta k θ)⁻¹ := by
  rw [cpow_neg]

/-- `Δ′ = -k² sin θ cos θ / Δ`. -/
theorem hasDerivAt_ellDelta {k : ℂ} (hk : 1 - k ^ 2 ∈ slitPlane) (θ : ℝ) :
    HasDerivAt (ellDelta k) (-(k ^ 2 * Real.sin θ * Real.cos θ) * (ellDelta k θ)⁻¹) θ := by
  have hb : HasDerivAt (fun θ : ℝ => 1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2)
      (-(k ^ 2 * (2 * Real.sin θ * Real.cos θ))) θ := by
    have := ((Real.hasDerivAt_sin θ).ofReal_comp.pow 2).const_mul (k ^ 2) |>.const_sub 1
    convert this using 1; push_cast; ring
  have h := (Complex.hasStrictDerivAt_cpow_const (c := (1 / 2 : ℂ))
    (one_sub_sq_mul_sin_sq_mem_slitPlane hk θ)).hasDerivAt.comp θ hb
  refine h.congr_deriv ?_
  rw [show (1 / 2 : ℂ) - 1 = -(1 / 2) by norm_num, one_sub_sq_mul_sin_sq_cpow_neg_half]
  ring

/-- `Δ` is continuous in the principal domain. -/
theorem continuous_ellDelta {k : ℂ} (hk : 1 - k ^ 2 ∈ slitPlane) : Continuous (ellDelta k) :=
  continuous_iff_continuousAt.2 fun θ => (hasDerivAt_ellDelta hk θ).continuousAt

/-- `∫₀^φ Δ⁻³ dθ = (E(φ, k) - k² sin φ cos φ/Δ(φ))/k′²` for real `φ`. -/
theorem integral_inv_ellDelta_cube {k : ℂ} (hk : 1 - k ^ 2 ∈ slitPlane) (φ : ℝ) :
    ∫ θ in (0 : ℝ)..φ, (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2)⁻¹ *
        (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) =
      (incompleteEllipticE φ k - k ^ 2 * Real.sin φ * Real.cos φ / ellDelta k φ) / (1 - k ^ 2) := by
  have hk0 : (1 - k ^ 2) ≠ 0 := slitPlane_ne_zero hk
  set A : ℝ → ℂ := fun θ => ((∫ x in (0 : ℝ)..θ, ellDelta k x) -
    k ^ 2 * ((Real.sin θ : ℂ) * Real.cos θ / ellDelta k θ)) / (1 - k ^ 2) with hA
  have hd : ∀ θ : ℝ, HasDerivAt A ((1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2)⁻¹ *
      (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))) θ := by
    intro θ
    have hΔ := hasDerivAt_ellDelta hk θ
    have hΔ0 := ellDelta_ne_zero hk θ
    have hI := ((continuous_ellDelta hk).integral_hasStrictDerivAt 0 θ).hasDerivAt
    have hs := (Real.hasDerivAt_sin θ).ofReal_comp
    have hc := (Real.hasDerivAt_cos θ).ofReal_comp
    have h := ((hI.sub (((hs.mul hc).div hΔ hΔ0).const_mul (k ^ 2))).div_const (1 - k ^ 2))
    refine h.congr_deriv ?_
    rw [one_sub_sq_mul_sin_sq_cpow_neg_half, ← ellDelta_sq]
    have hsc : (Real.sin θ : ℂ) ^ 2 + (Real.cos θ : ℂ) ^ 2 = 1 := by
      exact_mod_cast Real.sin_sq_add_cos_sq θ
    have h2 := ellDelta_sq k θ
    simp only [Pi.mul_apply, ofReal_neg]
    field_simp
    linear_combination (ellDelta k θ ^ 2 + (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) +
      k ^ 2 * ((Real.sin θ : ℂ) ^ 2 - (Real.cos θ : ℂ) ^ 2)) * h2 - k ^ 2 * hsc
  have hfun : (fun θ : ℝ => (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2)⁻¹ *
      (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))) =
      fun θ => (ellDelta k θ ^ 2)⁻¹ * (ellDelta k θ)⁻¹ := by
    funext θ; rw [one_sub_sq_mul_sin_sq_cpow_neg_half, ellDelta_sq]
  have hcont : Continuous fun θ => (ellDelta k θ ^ 2)⁻¹ * (ellDelta k θ)⁻¹ := by
    have := continuous_ellDelta hk
    exact ((this.pow 2).inv₀ fun θ => pow_ne_zero 2 (ellDelta_ne_zero hk θ)).mul
      (this.inv₀ (ellDelta_ne_zero hk))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hd θ)
    (by rw [hfun]; exact hcont.intervalIntegrable _ _)]
  simp only [hA, intervalIntegral.integral_same, Real.sin_zero, ofReal_zero, zero_mul, zero_div,
    mul_zero, sub_zero, incompleteEllipticE_ofReal_eq_integral]
  ring

/-- `∫₀^φ sec²θ Δ⁻¹ dθ = F(φ, k) - (E(φ, k) - Δ(φ) tan φ)/k′²` for real `|φ| < π/2`. -/
private lemma integral_sec_sq_mul_inv_ellDelta {k : ℂ} (hk : 1 - k ^ 2 ∈ slitPlane) {φ : ℝ}
    (hφ : |φ| < π / 2) :
    ∫ θ in (0 : ℝ)..φ, (1 - 1 * (Real.sin θ : ℂ) ^ 2)⁻¹ *
        (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) =
      incompleteEllipticF φ k - (incompleteEllipticE φ k - ellDelta k φ * Real.tan φ) /
          (1 - k ^ 2) := by
  have hk0 : (1 - k ^ 2) ≠ 0 := slitPlane_ne_zero hk
  have hsub : ∀ θ ∈ uIcc (0 : ℝ) φ, Real.cos θ ≠ 0 := by
    intro θ hθ
    refine (Real.cos_pos_of_mem_Ioo ?_).ne'
    rcases le_total 0 φ with h | h
    · rw [uIcc_of_le h] at hθ
      rw [abs_lt] at hφ; constructor <;> linarith [hθ.1, hθ.2]
    · rw [uIcc_of_ge h] at hθ
      rw [abs_lt] at hφ; constructor <;> linarith [hθ.1, hθ.2]
  set B : ℝ → ℂ := fun θ => (∫ x in (0 : ℝ)..θ, (ellDelta k x)⁻¹) -
    ((∫ x in (0 : ℝ)..θ, ellDelta k x) - ellDelta k θ * ((Real.sin θ : ℂ) / Real.cos θ)) /
      (1 - k ^ 2) with hB
  have hcΔi : Continuous fun θ => (ellDelta k θ)⁻¹ :=
    (continuous_ellDelta hk).inv₀ (ellDelta_ne_zero hk)
  have hd : ∀ θ ∈ uIcc (0 : ℝ) φ, HasDerivAt B ((1 - 1 * (Real.sin θ : ℂ) ^ 2)⁻¹ *
      (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))) θ := by
    intro θ hθ
    have hc0 : (Real.cos θ : ℂ) ≠ 0 := by exact_mod_cast hsub θ hθ
    have hΔ := hasDerivAt_ellDelta hk θ
    have hΔ0 := ellDelta_ne_zero hk θ
    have hI := ((continuous_ellDelta hk).integral_hasStrictDerivAt 0 θ).hasDerivAt
    have hJ := (hcΔi.integral_hasStrictDerivAt 0 θ).hasDerivAt
    have hs := (Real.hasDerivAt_sin θ).ofReal_comp
    have hc := (Real.hasDerivAt_cos θ).ofReal_comp
    have h := hJ.sub ((hI.sub (hΔ.mul (hs.div hc hc0))).div_const (1 - k ^ 2))
    refine h.congr_deriv ?_
    rw [one_sub_sq_mul_sin_sq_cpow_neg_half]
    have hsc : (Real.sin θ : ℂ) ^ 2 + (Real.cos θ : ℂ) ^ 2 = 1 := by
      exact_mod_cast Real.sin_sq_add_cos_sq θ
    have h2 := ellDelta_sq k θ
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
        fun θ => ((Real.cos θ : ℂ) ^ 2)⁻¹ * (ellDelta k θ)⁻¹ := by
      funext θ
      rw [one_sub_sq_mul_sin_sq_cpow_neg_half]
      have hsc : (Real.sin θ : ℂ) ^ 2 + (Real.cos θ : ℂ) ^ 2 = 1 := by
        exact_mod_cast Real.sin_sq_add_cos_sq θ
      congr 2; linear_combination -hsc
    rw [hfun]
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.mul ?_ hcΔi.continuousOn
    exact ContinuousOn.inv₀ (by fun_prop) fun θ hθ => pow_ne_zero 2 (by exact_mod_cast hsub θ hθ)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
  simp only [hB, intervalIntegral.integral_same, Real.sin_zero, Real.cos_zero, ofReal_zero,
    ofReal_one, zero_div, mul_zero, sub_zero, incompleteEllipticE_ofReal_eq_integral,
    incompleteEllipticF_ofReal_eq_integral, one_sub_sq_mul_sin_sq_cpow_neg_half,
        Real.tan_eq_sin_div_cos, ofReal_div]

/-- For real `φ`, `Π(φ, α², k)` is the interval integral when `1 - α² sin²θ` is bounded away from
`0`. -/
theorem incompleteEllipticPi_ofReal_eq_integral_of_norm_ge {φ : ℝ} {α2 k : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (h : ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖1 - α2 * (Real.sin (t * φ) : ℂ) ^ 2‖) :
    incompleteEllipticPi φ α2 k = ∫ θ in (0 : ℝ)..φ, (1 - α2 * (Real.sin θ : ℂ) ^ 2)⁻¹ *
        (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) := by
  rw [incompleteEllipticPi_eq_primitive hδ (fun t ht => by
    rw [← ofReal_mul, ← ofReal_sin]; exact h t ht), primitive_ofReal]
  simp only [← Complex.ofReal_sin]

/-- In the principal domain `1 - k² sin²θ` is bounded away from `0` for real `θ`. -/
private lemma exists_le_norm_one_sub_sq_mul_sin_sq {k : ℂ} (hk : 1 - k ^ 2 ∈ slitPlane) :
    ∃ δ > 0, ∀ θ : ℝ, δ ≤ ‖1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2‖ := by
  obtain ⟨u0, hu0, hmin⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_isMinOn
    (nonempty_Icc.2 zero_le_one)
    (by fun_prop : Continuous fun u : ℝ => ‖1 - k ^ 2 * (u : ℂ)‖).continuousOn
  refine ⟨‖1 - k ^ 2 * (u0 : ℂ)‖, norm_pos_iff.2 (slitPlane_ne_zero
    (one_sub_mul_ofReal_mem_slitPlane hk hu0.1 hu0.2)), fun θ => ?_⟩
  have := hmin (show Real.sin θ ^ 2 ∈ Icc (0 : ℝ) 1 from ⟨sq_nonneg _, Real.sin_sq_le_one θ⟩)
  simpa using this

/-- DLMF 19.6.2: `Π(k², k) = E(k)/k'²` (DLMF: `k² < 1`; here the principal domain
`1 - k² ∈ ℂ \ (-∞, 0]`). -/
@[dlmf 19.6.E2]
theorem completeEllipticPi_sq_self {k : ℂ} (hk : 1 - k ^ 2 ∈ slitPlane) :
    completeEllipticPi (k ^ 2) k = completeEllipticE k / (1 - k ^ 2) := by
  obtain ⟨δ, hδ, h⟩ := exists_le_norm_one_sub_sq_mul_sin_sq hk
  rw [completeEllipticPi, show ((π : ℂ) / 2) = ((π / 2 : ℝ) : ℂ) by push_cast; ring,
    incompleteEllipticPi_ofReal_eq_integral_of_norm_ge hδ (fun t _ => h _),
        integral_inv_ellDelta_cube hk, completeEllipticE]
  simp

/-- Identity under the stated parameter and domain assumptions: `incompleteEllipticPi φ (k ^ 2) k =
(incompleteEllipticE φ k - k ^ 2 * Real.sin φ * Real.cos φ / (1 - k ^ 2 * (Real.sin φ : ℂ) ^ 2) ^ (1
/ 2 : ℂ)) / (1 - k ^ 2) ∧ incompleteEllipticPi φ 1 k = incompleteEllipticF φ k -
(incompleteEllipticE φ k - (1 - k ^ 2 * (Real.sin φ : ℂ) ^ 2) ^ (1 / 2 : ℂ) * Real.tan φ) / (1 - k ^
2)`. -/
theorem incompleteEllipticPi_special_k' {φ : ℝ} (hφ : |φ| < π / 2) {k : ℂ}
    (hk : 1 - k ^ 2 ∈ slitPlane) :
    incompleteEllipticPi φ (k ^ 2) k = (incompleteEllipticE φ k - k ^ 2 * Real.sin φ * Real.cos φ /
        (1 - k ^ 2 * (Real.sin φ : ℂ) ^ 2) ^ (1 / 2 : ℂ)) / (1 - k ^ 2) ∧
      incompleteEllipticPi φ 1 k = incompleteEllipticF φ k - (incompleteEllipticE φ k -
        (1 - k ^ 2 * (Real.sin φ : ℂ) ^ 2) ^ (1 / 2 : ℂ) * Real.tan φ) / (1 - k ^ 2) := by
  obtain ⟨δ, hδ, h⟩ := exists_le_norm_one_sub_sq_mul_sin_sq hk
  refine ⟨by rw [incompleteEllipticPi_ofReal_eq_integral_of_norm_ge hδ (fun t _ => h _),
               integral_inv_ellDelta_cube hk], ?_⟩
  have hc : 0 < Real.cos φ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [neg_abs_le φ], by linarith [le_abs_self φ]⟩
  have hcθ : ∀ t ∈ Icc (0 : ℝ) 1, Real.cos φ ≤ Real.cos (t * φ) := by
    intro t ht
    rw [← Real.cos_abs (t * φ), ← Real.cos_abs φ]
    refine Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) ?_
    rw [abs_mul, abs_of_nonneg ht.1]; exact mul_le_of_le_one_left (abs_nonneg _) ht.2
  rw [incompleteEllipticPi_ofReal_eq_integral_of_norm_ge (δ := Real.cos φ ^ 2) (by positivity),
      integral_sec_sq_mul_inv_ellDelta hk hφ]
  intro t ht
  have : (1 - 1 * (Real.sin (t * φ) : ℂ) ^ 2) = ((Real.cos (t * φ) ^ 2 : ℝ) : ℂ) := by
    have h1 : (Real.sin (t * φ) : ℂ) ^ 2 + (Real.cos (t * φ) : ℂ) ^ 2 = 1 := by
      exact_mod_cast Real.sin_sq_add_cos_sq (t * φ)
    rw [ofReal_pow]
    linear_combination -h1
  rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have := hcθ t ht
  nlinarith

/-- `1 + k sin²θ > 0` for `k² < 1`. -/
private lemma one_add_mul_sin_sq_pos {k : ℝ} (hk : k ^ 2 < 1) (θ : ℝ) :
    0 < 1 + k * Real.sin θ ^ 2 := by
  have hk1 : 0 < 1 + k := by nlinarith
  have h1 := Real.sin_sq_le_one θ
  have h2 := sq_nonneg (Real.sin θ)
  rcases h2.lt_or_eq with h2 | h2
  · nlinarith [mul_pos hk1 h2]
  · rw [← h2]; norm_num

/-- `∫₀^{π/2} (1 - k sin²θ)/((1 + k sin²θ)√(1 - k² sin²θ)) dθ = π/(2(1 + k))` for `k² < 1`,
from the primitive `arctan((1 + k) tan θ/Δ)/(1 + k)`. -/
private lemma integral_neg_self_aux {k : ℝ} (hk : k ^ 2 < 1) :
    ∫ θ in (0 : ℝ)..(π / 2), (1 - k * Real.sin θ ^ 2) /
      ((1 + k * Real.sin θ ^ 2) * √(1 - k ^ 2 * Real.sin θ ^ 2)) = π / (2 * (1 + k)) := by
  have hk1 : 0 < 1 + k := by nlinarith
  have hD : ∀ θ : ℝ, 0 < 1 - k ^ 2 * Real.sin θ ^ 2 := fun θ => by
    nlinarith [Real.sin_sq_le_one θ, sq_nonneg (Real.sin θ)]
  have hP := one_add_mul_sin_sq_pos hk
  set h : ℝ → ℝ := fun θ => (1 - k * Real.sin θ ^ 2) /
      ((1 + k * Real.sin θ ^ 2) * √(1 - k ^ 2 * Real.sin θ ^ 2)) with hh
  have hcont : Continuous h := by
    refine Continuous.div (by fun_prop) (by fun_prop) fun θ => ?_
    exact mul_ne_zero (hP θ).ne' (Real.sqrt_pos.mpr (hD θ)).ne'
  set G : ℝ → ℝ := fun θ => Real.arctan ((1 + k) * Real.tan θ /
      √(1 - k ^ 2 * Real.sin θ ^ 2)) / (1 + k) with hG
  have hderiv : ∀ θ ∈ Ioo (-(π / 2)) (π / 2), HasDerivAt G (h θ) θ := by
    intro θ hθ
    have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo hθ
    have hsq := Real.sqrt_pos.mpr (hD θ)
    have hΔ : HasDerivAt (fun θ => √(1 - k ^ 2 * Real.sin θ ^ 2))
        (-(k ^ 2 * (2 * Real.sin θ * Real.cos θ)) / (2 * √(1 - k ^ 2 * Real.sin θ ^ 2))) θ := by
      have := ((((Real.hasDerivAt_sin θ).pow 2).const_mul (k ^ 2)).const_sub 1).sqrt (hD θ).ne'
      convert this using 1
      simp
    have htan : HasDerivAt Real.tan (1 / Real.cos θ ^ 2) θ := Real.hasDerivAt_tan hc.ne'
    have hw := ((htan.const_mul (1 + k)).div hΔ hsq.ne').arctan
    have := hw.div_const (1 + k)
    refine this.congr_deriv ?_
    simp only [Pi.div_apply, hh]
    rw [Real.tan_eq_sin_div_cos]
    have hsc : Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 := by linarith [Real.sin_sq_add_cos_sq θ]
    have hsq2 := Real.sq_sqrt (hD θ).le
    have := hP θ
    field_simp
    rw [hsq2, hsc]
    ring
  have hint : ∀ b ∈ Ioo 0 (π / 2), ∫ θ in (0 : ℝ)..b, h θ = G b := by
    intro b hb
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ hθ => hderiv θ ?_)
      (hcont.intervalIntegrable _ _)]
    · simp [hG]
    · rw [uIcc_of_le hb.1.le] at hθ
      exact ⟨by linarith [hθ.1, Real.pi_pos], hθ.2.trans_lt hb.2⟩
  have hL : Tendsto (fun b => ∫ θ in (0 : ℝ)..b, h θ) (𝓝[<] (π / 2))
      (𝓝 (∫ θ in (0 : ℝ)..(π / 2), h θ)) :=
    ((intervalIntegral.continuous_primitive (fun a b => hcont.intervalIntegrable a b) 0).tendsto
      _).mono_left nhdsWithin_le_nhds
  have hR : Tendsto G (𝓝[<] (π / 2)) (𝓝 (π / 2 / (1 + k))) := by
    have hΔ : Tendsto (fun θ => (1 + k) / √(1 - k ^ 2 * Real.sin θ ^ 2)) (𝓝[<] (π / 2))
        (𝓝 ((1 + k) / √(1 - k ^ 2 * Real.sin (π / 2) ^ 2))) := by
      refine (Continuous.tendsto ?_ _).mono_left nhdsWithin_le_nhds
      exact continuous_const.div (by fun_prop) fun θ => (Real.sqrt_pos.mpr (hD θ)).ne'
    have hw := Real.tendsto_tan_pi_div_two.atTop_mul_pos
      (div_pos hk1 (Real.sqrt_pos.mpr (hD _))) hΔ
    have := ((Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp hw).div_const (1 + k)
    refine this.congr fun θ => ?_
    simp only [hG, Function.comp_apply]
    congr 2
    ring
  have hev : (fun b => ∫ θ in (0 : ℝ)..b, h θ) =ᶠ[𝓝[<] (π / 2)] G := by
    filter_upwards [Ioo_mem_nhdsLT (by positivity : (0 : ℝ) < π / 2)] with b hb using hint b hb
  rw [tendsto_nhds_unique (hL.congr' hev) hR]
  field_simp

/-- DLMF 19.6.2: `Π(-k, k) = π/(4(1 + k)) + K(k)/2` for real `k` with `k² < 1`. -/
@[dlmf 19.6.E2]
theorem completeEllipticPi_neg_self {k : ℝ} (hk : k ^ 2 < 1) :
    completeEllipticPi (-k) k = π / (4 * (1 + k)) + completeEllipticK k / 2 := by
  have hk1 : -k < 1 := by nlinarith
  have hD : ∀ θ : ℝ, 0 < 1 - k ^ 2 * Real.sin θ ^ 2 := fun θ => by
    nlinarith [Real.sin_sq_le_one θ, sq_nonneg (Real.sin θ)]
  have hc1 : Continuous fun θ : ℝ => (1 - k ^ 2 * Real.sin θ ^ 2) ^ (-(1 / 2) : ℝ) :=
    Continuous.rpow_const (by fun_prop) fun θ => Or.inl (hD θ).ne'
  have hc2 : Continuous fun θ : ℝ => (1 - k * Real.sin θ ^ 2) /
      ((1 + k * Real.sin θ ^ 2) * √(1 - k ^ 2 * Real.sin θ ^ 2)) := by
    exact Continuous.div (by fun_prop) (by fun_prop) fun θ =>
      mul_ne_zero (one_add_mul_sin_sq_pos hk θ).ne' (Real.sqrt_pos.mpr (hD θ)).ne'
  rw [completeEllipticPi, show (π : ℂ) / 2 = ((π / 2 : ℝ) : ℂ) by push_cast; ring, ← ofReal_neg,
    incompleteEllipticPi_eq_ofReal (m := k ^ 2) (by push_cast; rfl) hk.le hk1,
        completeEllipticK_ofReal hk]
  have e : DLMF.Elliptic.Real.incompleteEllipticPiOfParameter (π / 2) (-k) (k ^ 2) =
      ∫ θ in (0 : ℝ)..(π / 2), ((1 / 2) * (1 - k ^ 2 * Real.sin θ ^ 2) ^ (-(1 / 2) : ℝ) +
        (1 / 2) * ((1 - k * Real.sin θ ^ 2) /
          ((1 + k * Real.sin θ ^ 2) * √(1 - k ^ 2 * Real.sin θ ^ 2)))) := by
    rw [DLMF.Elliptic.Real.incompleteEllipticPiOfParameter]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [DLMF.Elliptic.piIntegrand]
    rw [Real.rpow_neg (hD θ).le, ← Real.sqrt_eq_rpow]
    have := one_add_mul_sin_sq_pos hk θ
    have := Real.sqrt_pos.mpr (hD θ)
    rw [show 1 - -k * Real.sin θ ^ 2 = 1 + k * Real.sin θ ^ 2 by ring]
    field_simp
    ring
  rw [e, intervalIntegral.integral_add ((hc1.const_mul _).intervalIntegrable _ _)
    ((hc2.const_mul _).intervalIntegrable _ _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_neg_self_aux hk,
    ← DLMF.Elliptic.Real.completeEllipticKOfParameter]
  have h1k : (1 + (k : ℂ)) ≠ 0 := by
    rw [← ofReal_one, ← ofReal_add]; exact ofReal_ne_zero.mpr (by nlinarith)
  push_cast
  field_simp
  ring

/-- DLMF 19.6.13 (first relation): `Π(φ, 0, k) = F(φ, k)` for all complex `φ`, `k`. -/
@[dlmf 19.6.E13]
theorem incompleteEllipticPi_zero (φ k : ℂ) : incompleteEllipticPi φ 0 k =
    incompleteEllipticF φ k := by
  rw [incompleteEllipticPi_eq_primitive (δ := 1) one_pos (fun t _ => by simp),
      incompleteEllipticF]
  simp

/-- DLMF 19.6.3: `Π(α², 0) = π/(2√(1 - α²))` for real `α² < 1`, and `Π(0, k) = K(k)`. -/
@[dlmf 19.6.E3]
theorem completeEllipticPi_special {α2 : ℝ} (hα : α2 < 1) (k : ℂ) :
    completeEllipticPi α2 0 = π / (2 * Real.sqrt (1 - α2)) ∧ completeEllipticPi 0 k =
        completeEllipticK k := by
  constructor
  · rw [completeEllipticPi, show ((π : ℂ) / 2) = ((π / 2 : ℝ) : ℂ) by push_cast; ring,
      incompleteEllipticPi_eq_ofReal (m := 0) (by simp) zero_le_one hα,
      ← DLMF.Elliptic.Real.completeEllipticPiOfParameter,
          DLMF.Elliptic.Real.completeEllipticPiOfParameter_param_zero hα]
    push_cast; ring
  · rw [completeEllipticPi, incompleteEllipticPi_zero, completeEllipticK_eq_incompleteEllipticF]

/-- On real characteristics below one and real modulus with `k²<1`, the real part
of the complex complete integral is the real integral in parameter `k²`. -/
private lemma completeEllipticPi_re_ofReal {n k : ℝ} (hn : n < 1) (hk : k ^ 2 < 1) :
    (completeEllipticPi n k).re = DLMF.Elliptic.Real.completeEllipticPiOfParameter n (k ^ 2) := by
  rw [completeEllipticPi, show (π : ℂ) / 2 = ((π / 2 : ℝ) : ℂ) by push_cast; ring,
    incompleteEllipticPi_eq_ofReal (m:=k ^ 2) (by push_cast; rfl) hk.le hn, ofReal_re]
  rfl

/-- DLMF 19.6.4: for real `k` with `k² < 1`, `Π(α², k) → +∞` as `α² → 1-`; for real
`α² < 1`, `Π(α², k) → +∞` as `k² → 1-` (`∞ · sign(1 - α²)`; the case `α² > 1` is in 19.6.6). -/
@[dlmf 19.6.E4]
theorem tendsto_completeEllipticPi {k α2 : ℝ} (hk : k ^ 2 < 1) (hα : α2 < 1) :
    Tendsto (fun a : ℝ => (completeEllipticPi a k).re) (𝓝[<] 1) atTop ∧
      Tendsto (fun k : ℝ => (completeEllipticPi α2 k).re) (𝓝[<] 1) atTop := by
  constructor
  · have hs : Tendsto (fun a : ℝ => 1 - a) (𝓝[<] 1) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have h : Tendsto (fun a : ℝ => 1 - a) (𝓝 1) (𝓝 (1 - 1)) :=
          (continuous_const.sub continuous_id).tendsto 1
        simpa using h.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with a ha
        change a < 1 at ha
        exact sub_pos.mpr ha
    have hpow := (tendsto_rpow_neg_nhdsGT_zero (by norm_num : (-1 / 2 : ℝ) < 0)).comp hs
    have hlim := hpow.const_mul_atTop (by positivity : (0 : ℝ) < π / 2)
    refine tendsto_atTop_mono' _ ?_ hlim
    filter_upwards [self_mem_nhdsWithin] with a (ha : a < 1)
    rw [completeEllipticPi_re_ofReal ha hk]
    have hb := DLMF.Elliptic.Real.completeEllipticPiOfParameter_param_zero_le ha (sq_nonneg k) hk
    rw [DLMF.Elliptic.Real.completeEllipticPiOfParameter_param_zero ha] at hb
    convert hb using 1
    dsimp only [Function.comp_def]
    rw [show (-1 / 2 : ℝ)=-(1 / 2) by norm_num, Real.rpow_neg (by linarith : 0 ≤ 1 - a),
                                        ←Real.sqrt_eq_rpow]
    ring
  · let c : ℝ := min 1 ((1 - α2)⁻¹)
    have hc : 0 < c := lt_min zero_lt_one (inv_pos.mpr (sub_pos.mpr hα))
    have hlim := tendsto_norm_completeEllipticK_one.const_mul_atTop hc
    refine tendsto_atTop_mono' _ ?_ hlim
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
    have hr2 : r ^ 2 < 1 := by nlinarith [hr.1, hr.2]
    rw [completeEllipticPi_re_ofReal hα hr2, completeEllipticK_ofReal hr2, Complex.norm_real,
      Real.norm_of_nonneg (DLMF.Elliptic.Real.completeEllipticKOfParameter_pos hr2).le]
    exact DLMF.Elliptic.Real.completeEllipticPiOfParameter_ge_min_mul_completeEllipticKOfParameter
        hα hr2

/-- DLMF 19.6.5: for real `1 < α²` and real `k` with `k² < 1`, the Cauchy principal
value satisfies `Π(α², k) = K(k) - Π(k²/α², k)`. -/
@[dlmf 19.6.E5]
theorem completeEllipticPi_of_one_lt {α2 k : ℝ} (hα : 1 < α2) (hk : k ^ 2 < 1) :
    completeEllipticPi α2 k = completeEllipticK k - completeEllipticPi (k ^ 2 / α2 : ℝ) k := by
  have hslit : 1 - (k : ℂ) ^ 2 ∈ slitPlane := by
    rw [← ofReal_pow, ← ofReal_one, ← ofReal_sub]
    exact ofReal_mem_slitPlane.mpr (by linarith)
  have hω : k ^ 2 / α2 < 1 := (div_lt_one (by linarith : 0 < α2)).mpr (by linarith)
  have hP := completeEllipticPi_eq_symmetricEllipticRF_add_RJ hslit
    (show α2 ≠ 1 by linarith)
  have hQ := completeEllipticPi_eq_symmetricEllipticRF_add_RJ hslit hω.ne
  have H := symmetricEllipticRJ_complete_reciprocal_parameter hk hα
  have hK : completeEllipticK k = symmetricEllipticRF 0 (1 - (k : ℂ) ^ 2) 1 := by
    rw [completeEllipticK_eq_incompleteEllipticF,
      show ((π : ℂ) / 2) = ((π / 2 : ℝ) : ℂ) by push_cast; ring,
      incompleteEllipticF_ofReal_eq_integral,
      ← symmetricEllipticRF_csc_sq_eq_integral (by positivity) le_rfl (k : ℂ)]
    norm_num [csc_sq_pi_div_two]
  push_cast at H
  rw [hP, hQ, hK]
  push_cast
  linear_combination (1 / 3 : ℂ) * H

/-- DLMF 19.6.6: for real `1 < α²` (Cauchy principal values), `Π(α², 0) = 0`;
for real `k` with `k² < 1`, `Π(α², k) → K(k) - E(k)/k'²` as `α² → 1+`; and for `1 < α²`,
`Π(α², k) → -∞` as `k² → 1-`. -/
@[dlmf 19.6.E6]
theorem completeEllipticPi_of_one_lt_special {α2 k : ℝ} (hα : 1 < α2) (hk : k ^ 2 < 1) :
    completeEllipticPi α2 0 = 0 ∧
      Tendsto (fun a : ℝ => completeEllipticPi a k) (𝓝[>] 1)
        (𝓝 (completeEllipticK k - completeEllipticE k / (1 - k ^ 2))) ∧
      Tendsto (fun k : ℝ => (completeEllipticPi α2 k).re) (𝓝[<] 1) atBot := by
  have hα0 : 0 < α2 := by linarith
  have hslit : 1 - (k : ℂ) ^ 2 ∈ slitPlane := by
    rw [← ofReal_pow, ← ofReal_one, ← ofReal_sub]
    exact ofReal_mem_slitPlane.mpr (by linarith)
  constructor
  · have H := completeEllipticPi_of_one_lt hα (k := 0) (by norm_num)
    norm_num only [zero_pow (by decide : 2 ≠ 0), zero_div, ofReal_zero] at H
    rw [(completeEllipticPi_special (α2 := 0) zero_lt_one 0).2, sub_self] at H
    exact H
  constructor
  · have hC := continuousAt_completeEllipticPi_characteristic hslit hk
    have hq : Tendsto (fun a : ℝ => k ^ 2 / a) (𝓝[>] 1) (𝓝 (k ^ 2)) := by
      have H : ContinuousAt (fun a : ℝ => k ^ 2 / a) 1 := by fun_prop (disch := norm_num)
      simpa using H.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (1 : ℝ)))
    have hvalue : completeEllipticPi (k ^ 2 : ℝ) k =
        completeEllipticE k / (1 - k ^ 2 : ℝ) := by
      simpa only [ofReal_pow, ofReal_sub, ofReal_one] using completeEllipticPi_sq_self hslit
    have H := (tendsto_const_nhds (x := completeEllipticK k)).sub (hC.tendsto.comp hq)
    rw [hvalue] at H
    simp only [ofReal_sub, ofReal_pow, ofReal_one] at H
    apply H.congr'
    filter_upwards [self_mem_nhdsWithin] with a ha
    exact (completeEllipticPi_of_one_lt ha hk).symm
  · have hKlim : Tendsto (fun k : ℝ => (completeEllipticK k).re) (𝓝[<] 1) atTop := by
      apply tendsto_norm_completeEllipticK_one.congr'
      filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with k hk
      have hk2 : k ^ 2 < 1 := by nlinarith [hk.1, hk.2]
      rw [completeEllipticK_eq_ofReal (m := k ^ 2) (by push_cast; rfl) hk2.le,
        Complex.norm_real, Real.norm_of_nonneg
          (DLMF.Elliptic.Real.completeEllipticKOfParameter_pos hk2).le, ofReal_re]
    have H := (tendsto_atBot_add_const_right _ (π / 2)
      (tendsto_neg_atTop_atBot.comp hKlim)).const_mul_atBot (inv_pos.mpr hα0)
    refine tendsto_atBot_mono' _ ?_ H
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with k hk
    have hk2 : k ^ 2 < 1 := by nlinarith [hk.1, hk.2]
    have hn : k ^ 2 / α2 < 1 := (div_lt_one hα0).mpr (by linarith)
    have hP := ThirdKindBounds.completeEllipticPiOfParameter_ge_add (sq_nonneg k) hk2 hα
    have hE := ThirdKindBounds.completeEllipticEOfParameter_le_pi_div_two (sq_nonneg k) hk2
    change (completeEllipticPi α2 k).re ≤ α2⁻¹ * (-(completeEllipticK k).re + π / 2)
    rw [completeEllipticPi_of_one_lt hα hk2, sub_re,
      completeEllipticPi_re_ofReal hn hk2,
      completeEllipticK_eq_ofReal (m := k ^ 2) (by push_cast; rfl) hk2.le, ofReal_re]
    have HE := mul_le_mul_of_nonneg_left hE (inv_pos.mpr hα0).le
    simp only [one_div] at hP
    nlinarith

/-! ### §19.6(ii) `F(φ, k)` -/

/-- DLMF 19.6.7: `F(0, k) = 0`, `F(φ, 0) = φ` and `F(π/2, k) = K(k)` for all complex `φ`, `k`. -/
@[dlmf 19.6.E7]
theorem incompleteEllipticF_special (φ k : ℂ) :
    incompleteEllipticF 0 k = 0 ∧ incompleteEllipticF φ 0 = φ ∧ incompleteEllipticF (π / 2) k =
        completeEllipticK k := by
  refine ⟨by simp [incompleteEllipticF, primitive_eq_integral], by simp [incompleteEllipticF,
    primitive_eq_integral], (completeEllipticK_eq_incompleteEllipticF k).symm⟩

/-- For real `|φ| < π/2`, `F(φ, 1) = ∫₀^φ sec θ dθ = gd⁻¹(φ)` (DLMF 19.6.8, second equality, with
DLMF's definition 4.23.41 of `gd⁻¹`). -/
@[dlmf 19.6.E8]
theorem incompleteEllipticF_one_eq_integral_sec {φ : ℝ} (hφ : |φ| < π / 2) :
    incompleteEllipticF φ 1 = ((∫ θ in (0 : ℝ)..φ, (Real.cos θ)⁻¹ : ℝ) : ℂ) := by
  rw [incompleteEllipticF_eq_ofReal (m := 1) (by simp) le_rfl,
      DLMF.Elliptic.Real.incompleteEllipticFOfParameter]
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
theorem incompleteEllipticF_one {φ : ℝ} (hφ : |φ| < π / 2) :
    incompleteEllipticF φ 1 = Real.sin φ * symmetricEllipticRC 1 ((Real.cos φ : ℂ) ^ 2) ∧
      incompleteEllipticF φ 1 = (Real.arsinh (Real.tan φ) : ℂ) := by
  have h2 : incompleteEllipticF φ 1 = (Real.arsinh (Real.tan φ) : ℂ) := by
    rw [incompleteEllipticF_one_eq_integral_sec hφ, integral_inv_cos_eq_arsinh_tan hφ]
  refine ⟨?_, h2⟩
  have hc := cos_pos_of_abs_lt_pi_div_two hφ
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
  rw [symmetricEllipticRC_eq_carlsonRC one_mem_slitPlane (by
      rw [← ofReal_pow]; exact ofReal_mem_slitPlane.2 hl), hRC, e3, h2,
    Carlson.TwoVariable.arsinh_eq_mul_carlsonRC (Real.tan φ), Real.tan_eq_sin_div_cos]
  push_cast
  rw [show ((c : ℝ) : ℂ) = Complex.cos φ from Complex.ofReal_cos φ]
  ring

/-- DLMF 19.6.7: `F(π/2, 1) = ∞`, as `|F(φ, 1)| → ∞` for real `φ → π/2-`; and
`lim_{φ→0} F(φ, k)/φ = 1`. -/
@[dlmf 19.6.E7]
theorem incompleteEllipticF_limits (k : ℂ) :
    Tendsto (fun φ : ℝ => ‖incompleteEllipticF φ 1‖) (𝓝[<] (π / 2)) atTop ∧
      Tendsto (fun φ : ℂ => incompleteEllipticF φ k / φ) (𝓝[≠] 0) (𝓝 1) := by
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
    rw [(incompleteEllipticF_one habs).2, Complex.norm_real, Real.norm_eq_abs]
    exact le_abs_self _
  · have := tendsto_primitive_div
      (eventually_continuousAt_one_sub_mul_sin_sq_cpow (k ^ 2) (-(1 / 2)))
    simpa [incompleteEllipticF] using this

/-! ### §19.6(iii) `E(φ, k)` -/

/-- DLMF 19.6.9: `E(0, k) = 0`, `E(φ, 0) = φ`, `E(π/2, k) = E(k)` for all complex `φ`, `k`. -/
@[dlmf 19.6.E9]
theorem incompleteEllipticE_special (φ k : ℂ) :
    incompleteEllipticE 0 k = 0 ∧ incompleteEllipticE φ 0 = φ ∧ incompleteEllipticE (π / 2) k =
        completeEllipticE k :=
  ⟨by simp [incompleteEllipticE, primitive_eq_integral], by
        simp [incompleteEllipticE, primitive_eq_integral], rfl⟩

/-- DLMF 19.6.9: `E(φ, 1) = sin φ` for real `|φ| ≤ π/2` (for larger real `φ`, `E(φ, 1)` is
`∫₀^φ |cos θ| dθ ≠ sin φ`: the printed identity holds on DLMF's principal range); in particular
`E(π/2, 1) = 1`. -/
@[dlmf 19.6.E9]
theorem incompleteEllipticE_one {φ : ℝ} (hφ : |φ| ≤ π / 2) : incompleteEllipticE φ 1 =
    Real.sin φ := by
  rw [incompleteEllipticE_eq_ofReal (m := 1) (by simp) le_rfl,
      DLMF.Elliptic.Real.incompleteEllipticEOfParameter]
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
theorem incompleteEllipticE_pi_div_two_one : incompleteEllipticE (π / 2) 1 = 1 := by
  have h := incompleteEllipticE_one (φ := π / 2) (by rw [abs_of_pos (by positivity)])
  rw [show ((π : ℂ) / 2) = ((π / 2 : ℝ) : ℂ) by push_cast; ring, h, Real.sin_pi_div_two,
    ofReal_one]

/-- DLMF 19.6.9 for complex amplitude: `E(φ, 1) = sin φ` when `|Re φ| < π/2`. -/
@[dlmf 19.6.E9]
theorem incompleteEllipticE_one_complex {φ : ℂ} (hφ : |φ.re| < π / 2) :
    incompleteEllipticE φ 1 = Complex.sin φ := by
  have hpt : ∀ t ∈ uIcc (0 : ℝ) 1,
      φ * (1 - (1 : ℂ) ^ 2 * Complex.sin (t * φ) ^ 2) ^ (1 / 2 : ℂ) = Complex.cos (t * φ) * φ := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    have hre : 0 < (Complex.cos (t * φ)).re := by
      rw [re_cos_eq_cos_mul_cosh]
      refine mul_pos (Real.cos_pos_of_mem_Ioo ?_) (Real.cosh_pos _)
      have : (t * φ : ℂ).re = t * φ.re := by simp
      rw [this]
      have h1 : |t * φ.re| ≤ |φ.re| := by
        rw [abs_mul, abs_of_nonneg ht.1]; exact mul_le_of_le_one_left (abs_nonneg _) ht.2
      constructor <;> linarith [neg_abs_le (t * φ.re), le_abs_self (t * φ.re)]
    rw [one_pow, one_mul, ← Complex.cos_sq', show (1 / 2 : ℂ) = 2⁻¹ by norm_num,
      sq_cpow_two_inv hre, mul_comm]
  rw [incompleteEllipticE, primitive_eq_integral, intervalIntegral.integral_congr hpt]
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
theorem tendsto_incompleteEllipticE_div (k : ℂ) :
    Tendsto (fun φ : ℂ => incompleteEllipticE φ k / φ) (𝓝[≠] 0) (𝓝 1) := by
  have := tendsto_primitive_div
      (eventually_continuousAt_one_sub_mul_sin_sq_cpow (k ^ 2) (1/2))
  simpa [incompleteEllipticE] using this

/-! ### §19.6(iv) `Π(φ, α², k)` -/

/-- DLMF 19.6.11: `Π(0, α², k) = 0` and `Π(φ, 0, 0) = φ` for all complex `φ`, `α²`, `k`. -/
@[dlmf 19.6.E11]
theorem incompleteEllipticPi_special (φ α2 k : ℂ) : incompleteEllipticPi 0 α2 k = 0 ∧
    incompleteEllipticPi φ 0 0 = φ := by
  refine ⟨principalValueSegmentIntegral_zero _ _, ?_⟩
  rw [incompleteEllipticPi_zero, (incompleteEllipticF_special φ 0).2.1]

/-- DLMF 19.6.11: `Π(φ, 1, 0) = tan φ` for real `|φ| < π/2`. -/
@[dlmf 19.6.E11]
theorem incompleteEllipticPi_one_zero {φ : ℝ} (hφ : |φ| < π / 2) :
    incompleteEllipticPi φ 1 0 = Real.tan φ := by
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
  rw [incompleteEllipticPi_eq_primitive (δ := Real.cos φ ^ 2) (by positivity)]
  · rw [primitive_ofReal]
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
    have : (1 - (1 : ℂ) * Complex.sin ((t : ℂ) * (φ : ℂ)) ^ 2) =
        ((Real.cos (t * φ) ^ 2 : ℝ) : ℂ) := by
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
theorem incompleteEllipticPi_special_RC {φ α2 : ℝ} (h0 : 0 < φ) (h1 : φ < π / 2)
    (hα : α2 ≠ 1 / Real.sin φ ^ 2) :
    incompleteEllipticPi φ α2 0 =
        symmetricEllipticRC (1 / Real.sin φ ^ 2 - 1 : ℝ) (1 / Real.sin φ ^ 2 - α2 : ℝ) ∧
      (α2 ≠ 1 → incompleteEllipticPi φ α2 1 =
        (symmetricEllipticRC (1 / Real.sin φ ^ 2 : ℝ) (1 / Real.sin φ ^ 2 - 1 : ℝ) -
          α2 * symmetricEllipticRC (1 / Real.sin φ ^ 2 : ℝ)
              (1 / Real.sin φ ^ 2 - α2 : ℝ)) / (1 - α2)) ∧
      incompleteEllipticPi φ 1 1 =
          (symmetricEllipticRC (1 / Real.sin φ ^ 2 : ℝ) (1 / Real.sin φ ^ 2 - 1 : ℝ) +
        (Real.sqrt (1 / Real.sin φ ^ 2) / (1 / Real.sin φ ^ 2 - 1) : ℝ)) / 2 := by
  let c : ℝ := 1 / Real.sin φ ^ 2
  have hc1 : 1 < c := one_lt_csc_sq h0 h1
  have hc : 0 < c := by linarith
  have hcm : 0 < c - 1 := by linarith
  have hs : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
  have hcs : c * Real.sin φ ^ 2 = 1 := by dsimp [c]; field_simp [hs.ne']
  have hks0 : 1 - (0 : ℂ) ^ 2 * (Real.sin φ : ℂ) ^ 2 ∈ slitPlane := by
    norm_num
  have hks1 : 1 - (1 : ℂ) ^ 2 * (Real.sin φ : ℂ) ^ 2 ∈ slitPlane := by
    have hr : 0 < 1 - Real.sin φ ^ 2 := by nlinarith [sq_pos_of_pos hs]
    convert ofReal_mem_slitPlane.mpr hr using 1
    push_cast
    ring
  have hP0 := incompleteEllipticPi_eq_symmetricEllipticRF_add_RJ h0 h1.le hks0 hα
  have hP1 := incompleteEllipticPi_eq_symmetricEllipticRF_add_RJ h0 h1.le hks1 hα
  have hP11 := incompleteEllipticPi_eq_symmetricEllipticRF_add_RJ h0 h1.le hks1
    (show (1 : ℝ) ≠ 1 / Real.sin φ ^ 2 by change 1 ≠ c; linarith)
  change incompleteEllipticPi φ α2 0 =
    symmetricEllipticRF ((c : ℂ) - 1) ((c : ℂ) - (0 : ℂ) ^ 2) c + (α2 : ℂ) / 3 *
      symmetricEllipticRJ ((c : ℂ) - 1) ((c : ℂ) - (0 : ℂ) ^ 2) c (c - α2 : ℝ) at hP0
  change incompleteEllipticPi φ α2 1 =
    symmetricEllipticRF ((c : ℂ) - 1) ((c : ℂ) - (1 : ℂ) ^ 2) c + (α2 : ℂ) / 3 *
      symmetricEllipticRJ ((c : ℂ) - 1) ((c : ℂ) - (1 : ℂ) ^ 2) c (c - α2 : ℝ) at hP1
  change incompleteEllipticPi φ 1 1 =
    symmetricEllipticRF ((c : ℂ) - 1) ((c : ℂ) - (1 : ℂ) ^ 2) c + (1 : ℂ) / 3 *
      symmetricEllipticRJ ((c : ℂ) - 1) ((c : ℂ) - (1 : ℂ) ^ 2) c (c - 1 : ℝ) at hP11
  have hp : c - α2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hα)
  have hJ0 := mul_symmetricEllipticRJ_self_right_ofReal hcm hc hp
  have hJ1 := mul_symmetricEllipticRJ_self_right_ofReal hc hcm hp
  rw [symmetricEllipticRJ_comm_left, symmetricEllipticRJ_comm_right] at hJ1
  have hRC0 : symmetricEllipticRF (c - 1 : ℝ) c c = symmetricEllipticRC (c - 1 : ℝ) c :=
    (symmetricEllipticRC_eq_symmetricEllipticRF _
      (not_isNegReal_of_mem_slitPlane (ofReal_mem_slitPlane.mpr hc))).symm
  have hRC1 : symmetricEllipticRF (c - 1 : ℝ) (c - 1 : ℝ) c =
      symmetricEllipticRC c (c - 1 : ℝ) := by
    rw [symmetricEllipticRF_comm_right, symmetricEllipticRF_comm_left]
    exact (symmetricEllipticRC_eq_symmetricEllipticRF _
      (not_isNegReal_of_mem_slitPlane (ofReal_mem_slitPlane.mpr hcm))).symm
  have hRD := symmetricEllipticRD_self_right_of_mem_slitPlane
    (ofReal_mem_slitPlane.mpr hc) (ofReal_mem_slitPlane.mpr hcm)
    (by exact_mod_cast (show c ≠ c - 1 by linarith))
  rw [Carlson.ofReal_cpow_half hc.le] at hRD
  change incompleteEllipticPi φ α2 0 = symmetricEllipticRC (c - 1 : ℝ) (c - α2 : ℝ) ∧
    (α2 ≠ 1 → incompleteEllipticPi φ α2 1 =
      (symmetricEllipticRC c (c - 1 : ℝ) - α2 * symmetricEllipticRC c (c - α2 : ℝ)) /
        (1 - α2)) ∧
    incompleteEllipticPi φ 1 1 =
      (symmetricEllipticRC c (c - 1 : ℝ) + (Real.sqrt c / (c - 1) : ℝ)) / 2
  constructor
  · push_cast at hRC0 hJ0 hP0 ⊢
    norm_num only [zero_pow (by decide : 2 ≠ 0), sub_zero] at hP0
    rw [hRC0] at hP0
    linear_combination hP0 - (1 / 3 : ℂ) * hJ0
  constructor
  · intro hα1
    push_cast at hRC1 hJ1 hP1 ⊢
    norm_num only [one_pow] at hP1
    rw [hRC1] at hP1
    have ha : (1 : ℂ) - α2 ≠ 0 := by exact_mod_cast sub_ne_zero.mpr (Ne.symm hα1)
    apply (eq_div_iff ha).mpr
    linear_combination (1 - (α2 : ℂ)) * hP1 + (α2 : ℂ) / 3 * hJ1
  · push_cast at hRC1 hP11 hRD ⊢
    norm_num only [one_pow] at hP11
    rw [hRC1, symmetricEllipticRJ_comm_right, symmetricEllipticRJ_comm_left] at hP11
    change incompleteEllipticPi φ 1 1 = _ + (1 : ℂ) / 3 *
      symmetricEllipticRD (c : ℂ) ((c : ℂ) - 1) ((c : ℂ) - 1) at hP11
    norm_num [show (c : ℂ) - 1 - c = -1 by ring] at hRD
    linear_combination hP11 + (1 / 3 : ℂ) * hRD

/-- DLMF 19.6.13: with `Δ = √(1 - k² sin²φ)`, for real `|φ| < π/2` and `k` in the
principal domain `1 - k² ∈ ℂ \ (-∞, 0]`,
`Π(φ, k², k) = (E(φ, k) - k² sin φ cos φ/Δ)/k'²` and
`Π(φ, 1, k) = F(φ, k) - (E(φ, k) - Δ tan φ)/k'²`. -/
@[dlmf 19.6.E13]
theorem incompleteEllipticPi_special_k {φ : ℝ} (hφ : |φ| < π / 2) {k : ℂ}
    (hk : 1 - k ^ 2 ∈ slitPlane) :
    incompleteEllipticPi φ (k ^ 2) k = (incompleteEllipticE φ k - k ^ 2 * Real.sin φ * Real.cos φ /
        (1 - k ^ 2 * (Real.sin φ : ℂ) ^ 2) ^ (1 / 2 : ℂ)) / (1 - k ^ 2) ∧
      incompleteEllipticPi φ 1 k = incompleteEllipticF φ k - (incompleteEllipticE φ k -
        (1 - k ^ 2 * (Real.sin φ : ℂ) ^ 2) ^ (1 / 2 : ℂ) * Real.tan φ) / (1 - k ^ 2) := by
  obtain ⟨δ, hδ, h⟩ := exists_le_norm_one_sub_sq_mul_sin_sq hk
  refine ⟨by rw [incompleteEllipticPi_ofReal_eq_integral_of_norm_ge hδ (fun t _ => h _),
               integral_inv_ellDelta_cube hk], ?_⟩
  have hc : 0 < Real.cos φ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [neg_abs_le φ], by linarith [le_abs_self φ]⟩
  have hcθ : ∀ t ∈ Icc (0 : ℝ) 1, Real.cos φ ≤ Real.cos (t * φ) := by
    intro t ht
    rw [← Real.cos_abs (t * φ), ← Real.cos_abs φ]
    refine Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) ?_
    rw [abs_mul, abs_of_nonneg ht.1]; exact mul_le_of_le_one_left (abs_nonneg _) ht.2
  rw [incompleteEllipticPi_ofReal_eq_integral_of_norm_ge (δ := Real.cos φ ^ 2) (by positivity),
      integral_sec_sq_mul_inv_ellDelta hk hφ]
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
theorem incompleteEllipticPi_pi_div_two (α2 k : ℂ) : incompleteEllipticPi (π / 2) α2 k =
    completeEllipticPi α2 k := rfl

/-- DLMF 19.6.14: `lim_{φ→0} Π(φ, α², k)/φ = 1`. -/
@[dlmf 19.6.E14]
theorem tendsto_incompleteEllipticPi_div (α2 k : ℂ) :
    Tendsto (fun φ : ℂ => incompleteEllipticPi φ α2 k / φ) (𝓝[≠] 0) (𝓝 1) := by
  have hf : ∀ᶠ z in 𝓝 (0 : ℂ), ContinuousAt (fun θ => (1 - α2 * Complex.sin θ ^ 2)⁻¹ *
      (1 - k ^ 2 * Complex.sin θ ^ 2) ^ (-(1 / 2 : ℂ))) z := by
    have hc : Continuous fun θ : ℂ => 1 - α2 * Complex.sin θ ^ 2 := by fun_prop
    filter_upwards [eventually_continuousAt_one_sub_mul_sin_sq_cpow (k ^ 2) (-(1/2)),
      hc.continuousAt.preimage_mem_nhds (isOpen_ne.mem_nhds (by simp : (fun θ : ℂ =>
        1 - α2 * Complex.sin θ ^ 2) 0 ≠ 0))] with z h1 h2
    exact (hc.continuousAt.inv₀ h2).mul h1
  have := tendsto_primitive_div hf
  simp only [Complex.sin_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    sub_zero, inv_one, one_cpow, mul_one] at this
  refine this.congr' ?_
  -- near 0, the principal value is the ordinary integral
  have hc : Continuous fun θ : ℂ => ‖1 - α2 * Complex.sin θ ^ 2‖ := by fun_prop
  obtain ⟨r, hr, hfr⟩ := Metric.eventually_nhds_iff_ball.1
    (hc.continuousAt.preimage_mem_nhds (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) <
      ‖1 - α2 * Complex.sin 0 ^ 2‖)))
  filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds 0 hr)] with φ hφ
  rw [incompleteEllipticPi_eq_primitive (δ := 1 / 2) (by norm_num)]
  intro t ht
  refine le_of_lt (hfr _ ?_)
  rw [Metric.mem_ball, dist_zero_right] at hφ ⊢
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
  calc t * ‖φ‖ ≤ 1 * ‖φ‖ := by gcongr; exact ht.2
    _ < _ := by rwa [one_mul]

/-! ### §19.6(v) `R_C(x, y)` -/

/-! ### Principal values of `R_C` -/

section PrincipalValue

open MeasureTheory

/-- Symmetric excision of a shrinking interval about `c` does not change the limit of a set
integral of an integrable function. -/
theorem tendsto_setIntegral_diff_Icc_nhdsGT {g : ℝ → ℂ} {s : Set ℝ}
    (hg : IntegrableOn g s) (c : ℝ) :
    Tendsto (fun ε : ℝ => ∫ t in s \ Icc (c - ε) (c + ε), g t) (𝓝[>] 0)
      (𝓝 (∫ t in s, g t)) := by
  have he : ∀ ε : ℝ, ∫ t in s \ Icc (c - ε) (c + ε), g t =
      ∫ t in s, (Icc (c - ε) (c + ε))ᶜ.indicator g t := by
    intro ε
    rw [setIntegral_indicator measurableSet_Icc.compl, sdiff_eq]
  simp only [he]
  refine tendsto_integral_filter_of_dominated_convergence (fun t => ‖g t‖) ?_ ?_ hg.norm ?_
  · exact Eventually.of_forall fun ε =>
      (hg.aestronglyMeasurable.indicator measurableSet_Icc.compl)
  · refine Eventually.of_forall fun ε => Eventually.of_forall fun t => ?_
    by_cases ht : t ∈ (Icc (c - ε) (c + ε))ᶜ
    · simp [indicator_of_mem ht]
    · simp [indicator_of_notMem ht]
  · have hae : ∀ᵐ t ∂(volume.restrict s), t ≠ c :=
      ae_restrict_of_ae (by
        rw [ae_iff]; simp only [ne_eq, not_not, ofPred_eq_eq_singleton]; exact measure_singleton c)
    filter_upwards [hae] with t htc
    have hpos : 0 < |t - c| := abs_pos.mpr (sub_ne_zero.mpr htc)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hpos] with ε hε
    have hmem : t ∈ (Icc (c - ε) (c + ε))ᶜ := by
      intro h
      have : |t - c| ≤ ε := abs_le.mpr ⟨by linarith [h.1], by linarith [h.2]⟩
      linarith [hε.2]
    rw [indicator_of_mem hmem]

/-- Multiplying an integrable function on `(0, ∞)` by `(t + 1)/(t - q)` keeps it integrable
off a neighbourhood of `q`. -/
private lemma integrableOn_mul_add_one_div_sub {k : ℝ → ℂ} (hk : IntegrableOn k (Ioi 0))
    {q ε : ℝ} (hq : 0 < q) (hε : 0 < ε) :
    IntegrableOn (fun t : ℝ => k t * (((t : ℂ) + 1) / ((t : ℂ) - q)))
      (Ioi 0 \ Icc (q - ε) (q + ε)) := by
  have hm : MeasurableSet (Ioi (0 : ℝ) \ Icc (q - ε) (q + ε)) :=
    measurableSet_Ioi.diff measurableSet_Icc
  refine Integrable.mono' ((hk.mono_set sdiff_subset).norm.mul_const (1 + (q + 1) / ε))
    ((hk.mono_set sdiff_subset).aestronglyMeasurable.mul
      (by fun_prop : Measurable fun t : ℝ => ((t : ℂ) + 1) / ((t : ℂ) - q)).aestronglyMeasurable)
    ((ae_restrict_mem hm).mono fun t ht => ?_)
  have ht0 : 0 < t := ht.1
  have htq : ε < |t - q| := by
    by_contra hc
    push Not at hc
    exact ht.2 ⟨by linarith [(abs_le.mp hc).1], by linarith [(abs_le.mp hc).2]⟩
  rw [norm_mul]
  gcongr
  rw [show ((t : ℂ) + 1) / ((t : ℂ) - q) = ((((t + 1) / (t - q)) : ℝ) : ℂ) by push_cast; rfl,
    norm_real, Real.norm_eq_abs, abs_div, abs_of_pos (by linarith : 0 < t + 1)]
  have hap : 0 < |t - q| := hε.trans htq
  rw [div_le_iff₀ hap]
  have h1 : t + 1 ≤ |t - q| + (q + 1) := by linarith [le_abs_self (t - q)]
  have h2 : (q + 1) / ε * |t - q| ≥ q + 1 := by
    rw [ge_iff_le, div_mul_eq_mul_div, le_div_iff₀ hε]
    nlinarith
  nlinarith

/-- The kernel `((t + x)^{1/2} (t + 1))⁻¹` is integrable on `(0, ∞)` for admissible `x`. -/
private lemma integrableOn_rc_kernel_one {x : ℂ} (hx : x ∈ slitPlane ∨ x = 0) :
    IntegrableOn (fun t : ℝ => (((t : ℂ) + x) ^ (1 / 2 : ℂ) * ((t : ℂ) + 1))⁻¹) (Ioi 0) := by
  have h1 : (1 : ℂ) ∈ slitPlane := one_mem_slitPlane
  refine (integrableOn_symmetricEllipticRF_integrand hx h1 h1).congr_fun (fun t _ => ?_)
    measurableSet_Ioi
  simp only [mul_assoc, cpow_half_mul_cpow_half]

/-- The `R_C` kernel with a negative pole parameter `-q` is integrable off a neighbourhood of
the pole. -/
private lemma integrableOn_rc_kernel_neg {x : ℂ} (hx : x ∈ slitPlane ∨ x = 0) {q ε : ℝ}
    (hq : 0 < q) (hε : 0 < ε) :
    IntegrableOn (fun t : ℝ => (((t : ℂ) + x) ^ (1 / 2 : ℂ) * ((t : ℂ) - q))⁻¹)
      (Ioi 0 \ Icc (q - ε) (q + ε)) := by
  refine (integrableOn_mul_add_one_div_sub (integrableOn_rc_kernel_one hx) hq hε).congr_fun
    (fun t ht => ?_) (measurableSet_Ioi.diff measurableSet_Icc)
  have h1 : (t : ℂ) + 1 ≠ 0 := by
    rw [← ofReal_one, ← ofReal_add]; exact ofReal_ne_zero.mpr (by linarith [ht.1.out])
  simp only [mul_inv, div_eq_mul_inv]
  rw [mul_assoc, ← mul_assoc ((t : ℂ) + 1)⁻¹, inv_mul_cancel₀ h1]; ring


/-- `t ↦ ((t + x)^{1/2})⁻¹` is real-differentiable at `t > 0` for admissible `x`. -/
private lemma differentiableAt_inv_cpow_half {x : ℂ} (hx : x ∈ slitPlane ∨ x = 0) {t : ℝ}
    (ht : 0 < t) :
    DifferentiableAt ℝ (fun u : ℝ => (((u : ℂ) + x) ^ (1 / 2 : ℂ))⁻¹) t := by
  have hs := ofReal_pos_add_mem_slitPlane ht hx
  have he : DifferentiableAt ℂ (fun w : ℂ => ((w + x) ^ (1 / 2 : ℂ))⁻¹) (t : ℂ) :=
    ((differentiableAt_id.add_const x).cpow_const hs).inv (ofReal_pos_add_cpow_half_ne_zero ht hx)
  exact he.hasDerivAt.comp_ofReal.differentiableAt

/-- For `x ∈ ℂ \ (-∞, 0]` and `q > 0` the symmetric truncations of
`∫₀^∞ dt/(√(t + x)(t - q))` about `t = q` converge: the principal value defining
`R_C(x, -q)` exists. -/
private lemma exists_tendsto_integral_rc_truncated {x : ℂ} (hx : x ∈ slitPlane) {q : ℝ}
    (hq : 0 < q) :
    ∃ L : ℂ, Tendsto (fun ε : ℝ => ∫ t in Ioi (0 : ℝ) \ Icc (q - ε) (q + ε),
      (((t : ℂ) + x) ^ (1 / 2 : ℂ) * ((t : ℂ) - q))⁻¹) (𝓝[>] 0) (𝓝 L) := by
  set A : ℝ → Set ℝ := fun ε => Ioi (0 : ℝ) \ Icc (q - ε) (q + ε) with hA
  have hAm : ∀ ε, MeasurableSet (A ε) := fun ε => measurableSet_Ioi.diff measurableSet_Icc
  set f : ℝ → ℂ := fun t => (((t : ℂ) + x) ^ (1 / 2 : ℂ) * ((t : ℂ) - q))⁻¹ with hf
  set h : ℝ → ℂ := fun t => (((t : ℂ) + 0) ^ (1 / 2 : ℂ) * ((t : ℂ) - q))⁻¹ with hh
  set c : ℂ := (q : ℂ) ^ (1 / 2 : ℂ) / ((q : ℂ) + x) ^ (1 / 2 : ℂ) with hc
  set g : ℝ → ℂ := fun t => f t - c * h t with hg
  set φ : ℝ → ℂ := fun t => (((t : ℂ) + x) ^ (1 / 2 : ℂ))⁻¹ - c * (((t : ℂ) + 0) ^ (1 / 2 : ℂ))⁻¹
    with hφ
  have hx' : x ∈ slitPlane ∨ x = 0 := Or.inl hx
  have h0' : (0 : ℂ) ∈ slitPlane ∨ (0 : ℂ) = 0 := Or.inr rfl
  have hfi : ∀ ε, 0 < ε → IntegrableOn f (A ε) := fun ε hε =>
    integrableOn_rc_kernel_neg hx' hq hε
  have hhi : ∀ ε, 0 < ε → IntegrableOn h (A ε) := fun ε hε =>
    integrableOn_rc_kernel_neg h0' hq hε
  have hφq : φ q = 0 := by
    have h1 := ofReal_pos_add_cpow_half_ne_zero hq hx'
    have h2 := ofReal_pos_add_cpow_half_ne_zero hq h0'
    simp only [hφ, hc]
    field_simp
    simp
  have hgφ : ∀ t, t ≠ q → g t = dslope φ q t := by
    intro t htq
    rw [dslope_of_ne _ htq, slope_def_module, hφq, sub_zero]
    simp only [hg, hf, hh, hφ, mul_inv, real_smul, ofReal_inv, ofReal_sub]
    ring
  have hφc : ContinuousOn (dslope φ q) (Icc (q / 2) (3 * q / 2)) := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hd : DifferentiableAt ℝ φ t :=
      (differentiableAt_inv_cpow_half hx' ht0).sub
        ((differentiableAt_inv_cpow_half h0' ht0).const_mul c)
    rcases eq_or_ne t q with rfl | htq
    · exact (continuousAt_dslope_same.mpr hd).continuousWithinAt
    · exact ((continuousAt_dslope_of_ne htq).mpr hd.continuousAt).continuousWithinAt
  have hgm : IntegrableOn g (Icc (q / 2) (3 * q / 2)) := by
    refine hφc.integrableOn_Icc.congr_fun_ae ?_
    have hae : ∀ᵐ t ∂(volume.restrict (Icc (q / 2) (3 * q / 2))), t ≠ q :=
      ae_restrict_of_ae (by
        rw [ae_iff]; simp only [ne_eq, not_not, ofPred_eq_eq_singleton]; exact measure_singleton q)
    filter_upwards [hae] with t ht
    exact (hgφ t ht).symm
  have hgo : IntegrableOn g (A (q / 2)) :=
    (hfi _ (by linarith)).sub ((hhi _ (by linarith)).const_mul c)
  have hgi : IntegrableOn g (Ioi 0) := by
    refine (hgo.union hgm).mono_set fun t ht => ?_
    by_cases h' : t ∈ Icc (q - q / 2) (q + q / 2)
    · right; exact ⟨by linarith [h'.1], by linarith [h'.2]⟩
    · left; exact ⟨ht, h'⟩
  have hlh := tendsto_integral_symmetricEllipticRC_truncated (x := 0) (y := -q) le_rfl (by linarith)
  simp only [neg_neg, ofReal_zero, ofReal_neg, ← sub_eq_add_neg] at hlh
  refine ⟨(∫ t in Ioi (0 : ℝ), g t) + c * (2 * symmetricEllipticRC 0 (-(q : ℂ))), ?_⟩
  refine ((tendsto_setIntegral_diff_Icc_nhdsGT hgi q).add (hlh.const_mul c)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [← integral_const_mul, ← integral_add (hgi.mono_set sdiff_subset)
    ((hhi ε hε).const_mul c)]
  refine setIntegral_congr_fun (hAm ε) fun t _ => ?_
  simp only [hg, hh, hf]
  ring


/-- Scaling of the symmetric truncations of the principal-value `R_C` integral. -/
private lemma integral_rc_truncated_mul {l : ℝ} (hl : 0 < l) (x : ℂ) (q ε : ℝ) :
    ∫ t in Ioi (0 : ℝ) \ Icc (l * q - ε) (l * q + ε),
        (((t : ℂ) + l * x) ^ (1 / 2 : ℂ) * ((t : ℂ) - (l * q : ℝ)))⁻¹ =
      (((l : ℂ) ^ (1 / 2 : ℂ))⁻¹) * ∫ s in Ioi (0 : ℝ) \ Icc (q - ε / l) (q + ε / l),
        (((s : ℂ) + x) ^ (1 / 2 : ℂ) * ((s : ℂ) - q))⁻¹ := by
  set F : ℝ → ℂ := fun t => (((t : ℂ) + l * x) ^ (1 / 2 : ℂ) * ((t : ℂ) - (l * q : ℝ)))⁻¹
    with hF
  set f : ℝ → ℂ := fun s => (((s : ℂ) + x) ^ (1 / 2 : ℂ) * ((s : ℂ) - q))⁻¹ with hf
  have hm1 : MeasurableSet (Ioi (0 : ℝ) \ Icc (l * q - ε) (l * q + ε)) :=
    measurableSet_Ioi.diff measurableSet_Icc
  have hm2 : MeasurableSet (Ioi (0 : ℝ) \ Icc (q - ε / l) (q + ε / l)) :=
    measurableSet_Ioi.diff measurableSet_Icc
  have hFl : ∀ s, F (l * s) = ((l : ℂ) ^ (1 / 2 : ℂ))⁻¹ * (l : ℂ)⁻¹ * f s := by
    intro s
    simp only [hF, hf]
    rw [show ((l * s : ℝ) : ℂ) + l * x = (l : ℂ) * ((s : ℂ) + x) by push_cast; ring,
      TauCeti.ofReal_mul_cpow hl.le,
      show ((l * s : ℝ) : ℂ) - (l * q : ℝ) = (l : ℂ) * ((s : ℂ) - q) by push_cast; ring]
    simp only [mul_inv]
    ring
  have hind : ∀ s, (Ioi (0 : ℝ) \ Icc (l * q - ε) (l * q + ε)).indicator F (l * s) =
      (Ioi (0 : ℝ) \ Icc (q - ε / l) (q + ε / l)).indicator
        (fun s => ((l : ℂ) ^ (1 / 2 : ℂ))⁻¹ * (l : ℂ)⁻¹ * f s) s := by
    intro s
    have hmem : l * s ∈ Ioi (0 : ℝ) \ Icc (l * q - ε) (l * q + ε) ↔
        s ∈ Ioi (0 : ℝ) \ Icc (q - ε / l) (q + ε / l) := by
      simp only [Set.mem_sdiff, mem_Ioi, mem_Icc]
      have e1 : l * (q - ε / l) = l * q - ε := by field_simp
      have e2 : l * (q + ε / l) = l * q + ε := by field_simp
      have h1 : l * q - ε ≤ l * s ↔ q - ε / l ≤ s := by
        rw [← e1]; constructor <;> intro h <;> nlinarith
      have h2 : l * s ≤ l * q + ε ↔ s ≤ q + ε / l := by
        rw [← e2]; constructor <;> intro h <;> nlinarith
      rw [mul_pos_iff_of_pos_left hl, h1, h2]
    by_cases hs : s ∈ Ioi (0 : ℝ) \ Icc (q - ε / l) (q + ε / l)
    · rw [indicator_of_mem (hmem.mpr hs), indicator_of_mem hs, hFl]
    · rw [indicator_of_notMem (fun h => hs (hmem.mp h)), indicator_of_notMem hs]
  rw [← integral_indicator hm1, ← integral_indicator hm2]
  have h := Measure.integral_comp_mul_left
    ((Ioi (0 : ℝ) \ Icc (l * q - ε) (l * q + ε)).indicator F) l
  simp only [hind] at h
  rw [integral_indicator hm2, integral_const_mul, abs_inv, abs_of_pos hl] at h
  rw [integral_indicator hm2, show (∫ y, (Ioi (0 : ℝ) \ Icc (l * q - ε) (l * q + ε)).indicator
      F y) = l • (l⁻¹ • ∫ y, (Ioi (0 : ℝ) \ Icc (l * q - ε) (l * q + ε)).indicator F y) by
    rw [smul_smul, mul_inv_cancel₀ hl.ne', one_smul], ← h]
  have hl' : (l : ℂ) ≠ 0 := ofReal_ne_zero.mpr hl.ne'
  rw [real_smul]
  generalize (∫ a in Ioi (0 : ℝ) \ Icc (q - ε / l) (q + ε / l), f a) = I
  field_simp


/-- The principal-value truncations of `R_C(x, -q)` converge for admissible `x`. -/
private lemma exists_tendsto_integral_rc_truncated' {x : ℂ} (hx : IsCarlsonArgument x) {q : ℝ}
    (hq : 0 < q) :
    ∃ L : ℂ, Tendsto (fun ε : ℝ => ∫ t in Ioi (0 : ℝ) \ Icc (q - ε) (q + ε),
      (((t : ℂ) + x) ^ (1 / 2 : ℂ) * ((t : ℂ) - q))⁻¹) (𝓝[>] 0) (𝓝 L) := by
  rcases hx with hx | rfl
  · exact exists_tendsto_integral_rc_truncated hx hq
  · have hlh := tendsto_integral_symmetricEllipticRC_truncated (x := 0) (y := -q)
        le_rfl (by linarith)
    simp only [neg_neg, ofReal_zero, ofReal_neg, ← sub_eq_add_neg] at hlh
    exact ⟨_, hlh⟩

/-- `l x ∈ ℂ \ (-∞, 0]` for real `l > 0` and `x ∈ ℂ \ (-∞, 0]`. -/
private lemma ofReal_mul_mem_slitPlane {l : ℝ} (hl : 0 < l) {x : ℂ} (hx : x ∈ slitPlane) :
    (l : ℂ) * x ∈ slitPlane := by
  rw [mem_slitPlane_iff] at hx ⊢
  simp only [re_ofReal_mul, im_ofReal_mul]
  rcases hx with h | h
  · exact Or.inl (mul_pos hl h)
  · exact Or.inr (mul_ne_zero hl.ne' h)

/-- DLMF 19.6.15, homogeneity of `R_C` (including the principal-value case). -/
private lemma symmetricEllipticRC_ofReal_mul {l : ℝ} (hl : 0 < l) {x y : ℂ}
    (hx : IsCarlsonArgument x)
    (hy : y ≠ 0) :
    symmetricEllipticRC (l * x) (l * y) = (l : ℂ) ^ (-(1 / 2 : ℂ)) * symmetricEllipticRC x y := by
  by_cases hys : y ∈ slitPlane
  · rcases hx with hx | rfl
    · rw [symmetricEllipticRC_eq_carlsonRC (ofReal_mul_mem_slitPlane hl hx)
        (ofReal_mul_mem_slitPlane hl hys), symmetricEllipticRC_eq_carlsonRC hx hys,
        Carlson.TwoVariable.carlsonRC_mul_of_pos hl hx hys]
      norm_num
    · rw [mul_zero, symmetricEllipticRC_eq_symmetricEllipticRF 0
          (not_isNegReal_of_mem_slitPlane (ofReal_mul_mem_slitPlane hl hys)),
        symmetricEllipticRF_zero_left (ofReal_mul_mem_slitPlane hl hys)
          (ofReal_mul_mem_slitPlane hl hys),
        symmetricEllipticRC_eq_symmetricEllipticRF 0 (not_isNegReal_of_mem_slitPlane hys),
        symmetricEllipticRF_zero_left hys hys]
      have h1 : (![(l : ℂ) * y, (l : ℂ) * y] : Fin 2 → ℂ) = fun _ => (l : ℂ) * y := by
        funext i; fin_cases i <;> rfl
      have h2 : (![y, y] : Fin 2 → ℂ) = fun _ => y := by funext i; fin_cases i <;> rfl
      rw [h1, h2, symmetricEllipticR_const _ _ (ofReal_mul_mem_slitPlane hl hys) (by norm_num),
        symmetricEllipticR_const _ _ hys (by norm_num), TauCeti.ofReal_mul_cpow hl.le]
      ring
  · have hneg : IsNegReal y := by
      rw [mem_slitPlane_iff] at hys
      push Not at hys
      refine ⟨hys.2, lt_of_le_of_ne hys.1 fun h => hy ?_⟩
      exact Complex.ext h hys.2
    set q : ℝ := -y.re with hqdef
    have hq : 0 < q := by rw [hqdef]; linarith [hneg.2]
    have hyq : y = -((q : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hqdef, hneg.1]
    have hneg' : IsNegReal ((l : ℂ) * y) := ⟨by simp [hneg.1], by
      simp only [re_ofReal_mul]; exact mul_neg_of_pos_of_neg hl hneg.2⟩
    obtain ⟨L, hL⟩ := exists_tendsto_integral_rc_truncated' hx hq
    have hT1 : ∀ ε : ℝ, (∫ t in Ioi (0 : ℝ) \ Icc (-y.re - ε) (-y.re + ε),
        (((t : ℂ) + x) ^ (1 / 2 : ℂ) * ((t : ℂ) + y))⁻¹) =
        ∫ t in Ioi (0 : ℝ) \ Icc (q - ε) (q + ε), (((t : ℂ) + x) ^ (1 / 2 : ℂ) *
          ((t : ℂ) - q))⁻¹ := by
      intro ε; rw [hyq]; simp only [hqdef, neg_re, ofReal_re, neg_neg, ← sub_eq_add_neg]
    have hTl : ∀ ε : ℝ, (∫ t in Ioi (0 : ℝ) \ Icc (-((l : ℂ) * y).re - ε)
        (-((l : ℂ) * y).re + ε), (((t : ℂ) + l * x) ^ (1 / 2 : ℂ) * ((t : ℂ) + l * y))⁻¹) =
        ((l : ℂ) ^ (1 / 2 : ℂ))⁻¹ * ∫ s in Ioi (0 : ℝ) \ Icc (q - ε / l) (q + ε / l),
          (((s : ℂ) + x) ^ (1 / 2 : ℂ) * ((s : ℂ) - q))⁻¹ := by
      intro ε
      rw [← integral_rc_truncated_mul hl x q ε]
      have hre : -((l : ℂ) * y).re = l * q := by
        rw [re_ofReal_mul, hqdef]; ring
      rw [hre]
      congr 1
      funext t
      rw [hyq]
      push_cast
      ring_nf
    have hdiv : Tendsto (fun ε : ℝ => ε / l) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · simpa using ((continuous_id.div_const l).tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with ε hε using div_pos hε hl
    have hLl : Tendsto (fun ε : ℝ => ∫ t in Ioi (0 : ℝ) \ Icc (-((l : ℂ) * y).re - ε)
        (-((l : ℂ) * y).re + ε), (((t : ℂ) + l * x) ^ (1 / 2 : ℂ) * ((t : ℂ) + l * y))⁻¹)
        (𝓝[>] 0) (𝓝 (((l : ℂ) ^ (1 / 2 : ℂ))⁻¹ * L)) := by
      simp only [hTl]
      exact (hL.comp hdiv).const_mul _
    have hL1 : Tendsto (fun ε : ℝ => ∫ t in Ioi (0 : ℝ) \ Icc (-y.re - ε) (-y.re + ε),
        (((t : ℂ) + x) ^ (1 / 2 : ℂ) * ((t : ℂ) + y))⁻¹) (𝓝[>] 0) (𝓝 L) := by
      simp only [hT1]; exact hL
    rw [symmetricEllipticRC_eq_cauchyPV hneg', symmetricEllipticRC_eq_cauchyPV hneg,
        principalValueIoi,
        principalValueIoi,
      hLl.limUnder_eq, hL1.limUnder_eq, cpow_neg]
    ring

end PrincipalValue

/-- DLMF 19.6.15: `R_C(x, x) = x^{-1/2}` (`x ∈ ℂ \ (-∞, 0]`);
`R_C(λx, λy) = λ^{-1/2} R_C(x, y)` (real `λ > 0`, `x` not a negative real, `y ≠ 0`);
`R_C(0, y) = (π/2) y^{-1/2}` for `|ph y| < π`; and `R_C(0, y) = 0` for `y < 0` (principal
value). -/
@[dlmf 19.6.E15]
theorem symmetricEllipticRC_special :
    (∀ x : ℂ, x ∈ slitPlane → symmetricEllipticRC x x = x ^ (-(1 / 2 : ℂ))) ∧
      (∀ (l : ℝ) (x y : ℂ), 0 < l → IsCarlsonArgument x → y ≠ 0 →
        symmetricEllipticRC (l * x) (l * y) = (l : ℂ) ^ (-(1 / 2 : ℂ)) * symmetricEllipticRC x y) ∧
      (∀ y : ℂ, y ∈ slitPlane → symmetricEllipticRC 0 y = π / 2 * y ^ (-(1 / 2 : ℂ))) ∧
      (∀ y : ℝ, y < 0 → symmetricEllipticRC 0 y = 0) := by
  refine ⟨fun x hx => ?_, fun l x y hl hx hy => symmetricEllipticRC_ofReal_mul hl hx hy,
    fun y hy => ?_, fun y hy => ?_⟩
  · rw [symmetricEllipticRC_eq_symmetricEllipticR hx hx]
    have : (![x, x] : Fin 2 → ℂ) = fun _ => x := by funext i; fin_cases i <;> rfl
    rw [this, symmetricEllipticR_const _ _ hx]
    norm_num
    rw [show (3/2 : ℂ) = 1/2 + 1 by norm_num, Complex.Gamma_add_one _ (by norm_num)]
    exact mul_ne_zero (by norm_num) Gamma_one_half_ne_zero
  · rw [symmetricEllipticRC_eq_symmetricEllipticRF 0 (not_isNegReal_of_mem_slitPlane hy),
      symmetricEllipticRF_zero_left hy hy]
    have : (![y, y] : Fin 2 → ℂ) = fun _ => y := by funext i; fin_cases i <;> rfl
    rw [this, symmetricEllipticR_const _ _ hy (by norm_num)]
  · rw [← ofReal_zero, (symmetricEllipticRC_of_neg hy le_rfl).2.2]
    simp

/-- DLMF 19.6.15: `R_C(x, y) → +∞` as `y → 0+` or `y → 0-`, for real `x > 0`. -/
@[dlmf 19.6.E15]
theorem tendsto_symmetricEllipticRC_zero {x : ℝ} (hx : 0 < x) :
    Tendsto (fun y : ℝ => (symmetricEllipticRC x y).re) (𝓝[≠] 0) atTop := by
  have hi : Tendsto (fun y : ℝ => y) (𝓝[≠] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hs : Tendsto (fun y : ℝ => Real.sqrt (x - y)) (𝓝[≠] 0) (𝓝 (Real.sqrt x)) := by
    simpa using ((tendsto_const_nhds (x := x)).sub hi).sqrt
  have hsum : Tendsto (fun y : ℝ => Real.sqrt x + Real.sqrt (x - y)) (𝓝[≠] 0)
      (𝓝 (2 * Real.sqrt x)) := by simpa [two_mul] using hs.const_add (Real.sqrt x)
  have hlog := (Real.continuousAt_log (by positivity : 2 * Real.sqrt x ≠ 0)).tendsto.comp hsum
  have hmain := (tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsNE_zero).const_mul_atTop
    (by norm_num : (0 : ℝ) < 1 / 2)
  have hl := hlog.add_atTop hmain
  have hfinal := hl.atTop_mul_pos (by positivity : 0 < (Real.sqrt x)⁻¹) (hs.inv₀ (by positivity))
  apply hfinal.congr'
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hx).filter_mono nhdsWithin_le_nhds] with y hy0 hyx
  have hy0 : y ≠ 0 := by simpa using hy0
  have hxy : 0 < x - y := by linarith
  have hyabs : 0 < |y| := abs_pos.mpr hy0
  have hr : symmetricEllipticRC x y =
      ((Real.log ((Real.sqrt x + Real.sqrt (x - y)) / Real.sqrt |y|) /
          Real.sqrt (x - y) : ℝ) : ℂ) := by
    rcases hy0.lt_or_gt with hy | hy
    · simpa only [abs_of_neg hy] using (symmetricEllipticRC_of_neg hy hx.le).2.2
    · simpa only [abs_of_pos hy] using (symmetricEllipticRC_of_gt hy hyx).2
  rw [hr, ofReal_re, Real.log_div (by positivity) (by positivity), Real.log_sqrt hyabs.le,
    Real.log_abs]
  dsimp only [Function.comp_def]
  ring

end DLMF.EllipticIntegrals
