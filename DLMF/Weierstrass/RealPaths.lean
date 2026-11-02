/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Weierstrass.Addition
public import DLMFMathlib.Analysis.Calculus.Deriv.InjOn
public import DLMFMathlib.MeasureTheory.Function.JacobianSqrt

/-!
# `℘` along real paths

Tools for inverting `℘` by real integrals (DLMF §23.6(iv)): along an affine path `γ` on which
`℘` is real, the function `t ↦ ℜ℘(γ(t))` has nonvanishing derivative of modulus
`2√|∏ⱼ(℘ - e_j)|` away from the half-lattice, so it is injective (Rolle's theorem), and the
one-dimensional change of variables formula turns `∫ du/√|∏ⱼ(u - e_j)|` over its image into
twice the length of the parameter interval (`MeasureTheory.integral_image_one_div_sqrt`).

## Main results

* `HalfPeriods.hasDerivAt_re_weierstrassP_comp`: derivative and its modulus for `ℜ℘ ∘ γ`.
* `tendsto_re_weierstrassP_ofReal_nhdsGT_zero`: `℘(t) → +∞` as `t → 0⁺`.
-/

@[expose] public section

open Complex PeriodPair MeasureTheory Set Filter Topology
open scoped Real

noncomputable section

namespace DLMF.Weierstrass

namespace HalfPeriods

variable (H : HalfPeriods)

/-- Along an affine path `γ` (derivative `v`, `‖v‖ = 1`) on which `℘` is real and which avoids the
half-lattice, `t ↦ ℜ℘(γ(t))` has the nonvanishing derivative `ℜ(℘'(γ(t))v)` of modulus
`2√‖(℘ - e₁)(℘ - e₂)(℘ - e₃)‖`. -/
theorem hasDerivAt_re_weierstrassP_comp {γ : ℝ → ℂ} {v : ℂ} (hv : ‖v‖ = 1)
    (hγ : ∀ t, HasDerivAt γ v t) {α β : ℝ}
    (hL : ∀ t ∈ Ioo α β, γ t ∉ H.lattice ∧ 2 * γ t ∉ H.lattice)
    (hR : ∀ t ∈ Ioo α β, (H.weierstrassP (γ t)).im = 0) {t : ℝ} (ht : t ∈ Ioo α β) :
    HasDerivAt (fun s => (H.weierstrassP (γ s)).re) (H.derivWeierstrassP (γ t) * v).re t ∧
      (H.derivWeierstrassP (γ t) * v).re ≠ 0 ∧
      |(H.derivWeierstrassP (γ t) * v).re| = 2 * Real.sqrt
        ‖(H.weierstrassP (γ t) - H.e 1) * (H.weierstrassP (γ t) - H.e 2) *
          (H.weierstrassP (γ t) - H.e 3)‖ := by
  obtain ⟨h1, h2⟩ := hL t ht
  have hF : HasDerivAt (fun s => H.weierstrassP (γ s)) (H.derivWeierstrassP (γ t) * v) t :=
    (hasDerivAt_weierstrassP H.periodPair h1).comp t (hγ t)
  set D := H.derivWeierstrassP (γ t) * v with hD
  have hre : HasDerivAt (fun s => (H.weierstrassP (γ s)).re) D.re t := by
    exact (Complex.reCLM.hasFDerivAt).comp_hasDerivAt t hF
  have him : HasDerivAt (fun s => (H.weierstrassP (γ s)).im) D.im t := by
    exact (Complex.imCLM.hasFDerivAt).comp_hasDerivAt t hF
  have him0 : D.im = 0 := by
    have hc : HasDerivAt (fun s => (H.weierstrassP (γ s)).im) 0 t := by
      refine (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs using hR s hs
    exact him.unique hc
  have hnorm : ‖D‖ = |D.re| := (Complex.abs_re_eq_norm.mpr him0).symm
  have hP : H.derivWeierstrassP (γ t) ≠ 0 :=
    derivWeierstrassP_ne_zero_of_two_mul_not_mem H.periodPair h1 h2
  have hv0 : v ≠ 0 := by rintro rfl; simp at hv
  have hD0 : D ≠ 0 := mul_ne_zero hP hv0
  refine ⟨hre, ?_, ?_⟩
  · intro h0; apply hD0; rw [← norm_eq_zero, hnorm, h0, abs_zero]
  · have hsq := H.derivWeierstrassP_sq_eq_prod h1
    have hn : |D.re| ^ 2 = 4 * ‖(H.weierstrassP (γ t) - H.e 1) *
        (H.weierstrassP (γ t) - H.e 2) * (H.weierstrassP (γ t) - H.e 3)‖ := by
      rw [← hnorm, hD, norm_mul, hv, mul_one, ← norm_pow, hsq,
        show ∀ x y z : ℂ, 4 * x * y * z = 4 * (x * y * z) by intros; ring, norm_mul]
      norm_num
    rw [← Real.sqrt_sq (abs_nonneg D.re), hn, Real.sqrt_mul (by norm_num),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- Continuity of `t ↦ ℜ℘(γ(t))` off the lattice. -/
theorem continuousAt_re_weierstrassP_comp {γ : ℝ → ℂ} {v : ℂ} (hγ : ∀ t, HasDerivAt γ v t)
    {t : ℝ} (ht : γ t ∉ H.lattice) : ContinuousAt (fun s => (H.weierstrassP (γ s)).re) t :=
  Complex.continuous_re.continuousAt.comp
    ((hasDerivAt_weierstrassP H.periodPair ht).comp t (hγ t)).continuousAt

end HalfPeriods

/-- `ℜ℘(t) → +∞` as `t → 0⁺` along the real axis. -/
theorem tendsto_re_weierstrassP_ofReal_nhdsGT_zero (L : PeriodPair) :
    Tendsto (fun t : ℝ => (℘[L] (t : ℂ)).re) (𝓝[>] 0) atTop := by
  have hg := analyticAt_weierstrassP_sub L (zero_mem _)
  have h1 : ContinuousAt (fun t : ℝ => ℘[L] t - 1 / ((t : ℂ) - 0) ^ 2) 0 :=
    hg.continuousAt.comp_of_eq Complex.continuous_ofReal.continuousAt (by simp)
  obtain ⟨C, hgc⟩ : ∃ C, Tendsto (fun t : ℝ => (℘[L] t - 1 / ((t : ℂ) - 0) ^ 2).re)
      (𝓝[>] 0) (𝓝 C) :=
    ⟨_, (Complex.continuous_re.continuousAt.comp h1).tendsto.mono_left nhdsWithin_le_nhds⟩
  have hinf : Tendsto (fun t : ℝ => (t ^ 2)⁻¹) (𝓝[>] 0) atTop := by
    have := (tendsto_pow_atTop (two_ne_zero)).comp (tendsto_inv_nhdsGT_zero (𝕜 := ℝ))
    simpa [Function.comp_def, inv_pow] using this
  refine (hinf.atTop_add hgc).congr' ?_
  filter_upwards with t
  have : (1 / ((t : ℂ) - 0) ^ 2) = (((t ^ 2)⁻¹ : ℝ) : ℂ) := by push_cast; ring
  simp only [this, sub_re, ofReal_re]
  ring

end DLMF.Weierstrass
