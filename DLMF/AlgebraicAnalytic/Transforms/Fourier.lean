/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AlgebraicAnalytic.Transforms.Defs
public import Mathlib.Analysis.Fourier.Convolution
public import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
public import Mathlib.Topology.EMetricSpace.BoundedVariation

/-!
# Fourier, Fourier cosine and Fourier sine transforms (DLMF §1.14(i)–(ii))

The statements of DLMF §1.14(i)–(ii) for DLMF's Fourier transform
`𝓕(f)(x) = (2π)^{-1/2} ∫ f(t) e^{ixt} dt` (`fourierTransform`, 1.14.1) and the cosine and sine
transforms on `(0, ∞)`.

Proved here from Mathlib through the bridge `fourierTransform_eq_fourier`
(`𝓕(f)(x) = (2π)^{-1/2} 𝓕_Mathlib f(-x/(2π))`): continuity and the Riemann–Lebesgue lemma
(§1.14(i)), the bound 1.14.2, the inversion formula 1.14.4 when `F = 𝓕(f)` is integrable, the
convolution theorem (§1.14(i), after 1.14.5) and the uniqueness theorem. Parseval's formula
1.14.8 is derived from 1.14.7_5. The inversion theorem 1.14.3 for functions of bounded
variation (Dirichlet–Jordan), the principal-value form of 1.14.4, 1.14.6, 1.14.7, 1.14.7_5 and
the cosine and sine statements 1.14.11–1.14.16 are admitted.

Hypotheses DLMF leaves implicit are explicit: integrability for each transform, and the one-sided
limits `f(u±)` in 1.14.3 are given as hypotheses (they exist for functions of bounded variation).
-/

@[expose] public noncomputable section

open MeasureTheory Complex Set Filter Topology
open scoped FourierTransform ComplexConjugate

namespace DLMF.AlgebraicAnalytic

/-- The normalizing constant: `(2π)^{-1/2} · (2π)^{-1/2} = (2π)⁻¹` in `ℂ`. -/
private lemma g1e_inv_sqrt_mul_self :
    ((Real.sqrt (2 * Real.pi))⁻¹ : ℂ) * ((Real.sqrt (2 * Real.pi))⁻¹ : ℂ) =
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ := by
  rw [← mul_inv, ← ofReal_mul, Real.mul_self_sqrt (by positivity)]

private lemma g1e_inv_sqrt_ne_zero : ((Real.sqrt (2 * Real.pi))⁻¹ : ℂ) ≠ 0 := by
  refine inv_ne_zero (ofReal_ne_zero.mpr ?_)
  exact (Real.sqrt_pos.mpr (by positivity)).ne'

/-- The integrand of 1.14.1 is integrable when `f` is. -/
lemma g1e_integrable_mul_cexp {f : ℝ → ℂ} (hf : Integrable f) (x : ℝ) :
    Integrable fun t : ℝ => f t * cexp (I * x * t) := by
  refine hf.norm.mono' (hf.aestronglyMeasurable.mul (by fun_prop : Continuous fun t : ℝ =>
    cexp (I * x * t)).aestronglyMeasurable) (Eventually.of_forall fun t => ?_)
  rw [norm_mul, show I * (x : ℂ) * t = ((x * t : ℝ) : ℂ) * I by push_cast; ring,
    norm_exp_ofReal_mul_I, mul_one]

/-- The Fourier transform is linear in a constant factor. -/
theorem fourierTransform_const_mul (c : ℂ) (f : ℝ → ℂ) (x : ℝ) :
    fourierTransform (fun t => c * f t) x = c * fourierTransform f x := by
  simp only [fourierTransform, mul_assoc, integral_const_mul]
  ring

/-- DLMF 1.14.2: `|F(x)| ≤ (2π)^{-1/2} ∫ |f(t)| dt`. -/
@[dlmf 1.14.E2]
theorem norm_fourierTransform_le (f : ℝ → ℂ) (x : ℝ) :
    ‖fourierTransform f x‖ ≤ (Real.sqrt (2 * Real.pi))⁻¹ * ∫ t, ‖f t‖ := by
  rw [fourierTransform, norm_mul]
  have h1 : ‖((Real.sqrt (2 * Real.pi))⁻¹ : ℂ)‖ = (Real.sqrt (2 * Real.pi))⁻¹ := by
    rw [norm_inv, norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [h1]
  refine mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans_eq ?_)
    (inv_nonneg.mpr (Real.sqrt_nonneg _))
  congr 1
  funext t
  rw [norm_mul, show I * (x : ℂ) * t = ((x * t : ℝ) : ℂ) * I by push_cast; ring,
    norm_exp_ofReal_mul_I, mul_one]

/-- DLMF §1.14(i): if `f` is absolutely integrable then `F = 𝓕(f)` is continuous. -/
@[dlmf 1.14.i]
theorem continuous_fourierTransform {f : ℝ → ℂ} (hf : Integrable f) :
    Continuous (fourierTransform f) := by
  unfold fourierTransform
  refine continuous_const.mul (continuous_of_dominated (bound := fun t => ‖f t‖) ?_ ?_ hf.norm ?_)
  · exact fun x => (g1e_integrable_mul_cexp hf x).aestronglyMeasurable
  · refine fun x => Eventually.of_forall fun t => ?_
    rw [norm_mul, show I * (x : ℂ) * t = ((x * t : ℝ) : ℂ) * I by push_cast; ring,
      norm_exp_ofReal_mul_I, mul_one]
  · exact Eventually.of_forall fun t => by fun_prop

/-- DLMF §1.14(i) (Riemann–Lebesgue lemma): `F(x) → 0` as `x → ±∞`. As in Mathlib, no
integrability hypothesis is needed (for non-integrable `f` the transform is `0`). -/
@[dlmf 1.14.i]
theorem tendsto_fourierTransform_cocompact (f : ℝ → ℂ) :
    Tendsto (fourierTransform f) (cocompact ℝ) (𝓝 0) := by
  have h2 : (-(1 / (2 * Real.pi)) : ℝ) ≠ 0 := by
    have : 0 < 1 / (2 * Real.pi) := by positivity
    linarith
  have hlin : Tendsto (fun x : ℝ => -x / (2 * Real.pi)) (cocompact ℝ) (cocompact ℝ) := by
    have := Filter.tendsto_cocompact_mul_left₀ (K := ℝ) h2
    refine this.congr fun x => ?_
    ring
  have := (Real.zero_at_infty_fourier f).comp hlin
  have h := this.const_mul ((Real.sqrt (2 * Real.pi))⁻¹ : ℂ)
  rw [mul_zero] at h
  refine h.congr fun x => ?_
  simp [fourierTransform_eq_fourier, Function.comp]

/-- DLMF 1.14.3 (inversion, Dirichlet–Jordan): if `f` is absolutely integrable and of bounded
variation near `u`, then `½(f(u+) + f(u-)) = (2π)^{-1/2} P.V.∫ F(x) e^{-ixu} dx`, the principal
value at infinity, `lim_{R → ∞} ∫_{-R}^{R}`. The one-sided limits are hypotheses here (they
exist by bounded variation). -/
@[dlmf 1.14.E3]
theorem tendsto_fourierTransform_inversion_pv {f : ℝ → ℂ} (hf : Integrable f) {u δ : ℝ}
    (hδ : 0 < δ) (hbv : BoundedVariationOn f (Icc (u - δ) (u + δ))) {fp fm : ℂ}
    (hp : Tendsto f (𝓝[>] u) (𝓝 fp)) (hm : Tendsto f (𝓝[<] u) (𝓝 fm)) :
    Tendsto (fun R : ℝ => ((Real.sqrt (2 * Real.pi))⁻¹ : ℂ) *
        ∫ x in -R..R, fourierTransform f x * cexp (-(I * x * u))) atTop
      (𝓝 ((fp + fm) / 2)) := by
  sorry

/-- DLMF 1.14.4, principal-value form: if `f` is absolutely integrable and continuously
differentiable, then `f(t) = (2π)^{-1/2} lim_{R→∞} ∫_{-R}^{R} F(x) e^{-ixt} dx`. (DLMF writes an
ordinary integral; `F` need not be absolutely integrable, see `fourierTransform_inversion` for
that case.) -/
@[dlmf 1.14.E4]
theorem tendsto_fourierTransform_inversion_of_contDiff {f : ℝ → ℂ} (hf : Integrable f)
    (hf' : ContDiff ℝ 1 f) (t : ℝ) :
    Tendsto (fun R : ℝ => ((Real.sqrt (2 * Real.pi))⁻¹ : ℂ) *
        ∫ x in -R..R, fourierTransform f x * cexp (-(I * x * t))) atTop (𝓝 (f t)) := by
  sorry

/-- DLMF 1.14.4 (Fourier inversion): if `f` is continuous and absolutely integrable and
`F = 𝓕(f)` is absolutely integrable, then `f(t) = (2π)^{-1/2} ∫ F(x) e^{-ixt} dx`. Proved from
Mathlib's `Continuous.fourierInv_fourier_eq`. -/
@[dlmf 1.14.E4]
theorem fourierTransform_inversion {f : ℝ → ℂ} (hf : Continuous f) (hfi : Integrable f)
    (hF : Integrable (fourierTransform f)) (t : ℝ) :
    f t = ((Real.sqrt (2 * Real.pi))⁻¹ : ℂ) *
      ∫ x, fourierTransform f x * cexp (-(I * x * t)) := by
  set c : ℂ := ((Real.sqrt (2 * Real.pi))⁻¹ : ℂ) with hc
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  set a : ℝ := -(1 / (2 * Real.pi)) with ha
  have ha0 : a ≠ 0 := by
    have : 0 < 1 / (2 * Real.pi) := by positivity
    rw [ha]; linarith
  have hfun : fourierTransform f = fun x => c * 𝓕 f (a * x) := by
    funext x
    rw [fourierTransform_eq_fourier, ha]
    congr 2
    field_simp
  -- integrability of Mathlib's transform
  have hFF : Integrable (𝓕 f) := by
    have h1 : Integrable fun x => 𝓕 f (a * x) := by
      have := hF.const_mul c⁻¹
      rw [hfun] at this
      refine this.congr (Eventually.of_forall fun x => ?_)
      simp only
      rw [← mul_assoc, inv_mul_cancel₀ g1e_inv_sqrt_ne_zero, one_mul]
    exact (integrable_comp_mul_left_iff (𝓕 f) ha0).mp h1
  have hinv := congrFun (hf.fourierInv_fourier_eq hfi hFF) t
  rw [Real.fourierInv_eq'] at hinv
  set g : ℝ → ℂ := fun v => cexp (↑(2 * Real.pi * v * t) * I) * 𝓕 f v with hg
  have hstep : ∀ x : ℝ, fourierTransform f x * cexp (-(I * x * t)) = c * g (a * x) := by
    intro x
    rw [hfun, hg]
    simp only
    rw [mul_assoc, mul_comm (𝓕 f (a * x))]
    congr 3
    rw [ha]
    push_cast
    field_simp
  simp_rw [hstep, integral_const_mul]
  rw [Measure.integral_comp_mul_left g a, ← mul_assoc, ← hinv]
  simp only [hg, smul_eq_mul, inner]
  have hai : |a⁻¹| = 2 * Real.pi := by
    rw [ha, abs_inv, abs_neg, abs_of_pos (by positivity), one_div, inv_inv]
  rw [hai, Complex.real_smul, ← mul_assoc, hc, g1e_inv_sqrt_mul_self,
    inv_mul_cancel₀ (ofReal_ne_zero.mpr hpi), one_mul]
  congr 1
  funext v
  congr 3
  simp only [RCLike.re_to_real, star_trivial]
  push_cast
  ring

/-- DLMF §1.14(i): the convolution 1.14.5 of absolutely integrable functions is absolutely
integrable. -/
@[dlmf 1.14.i]
theorem integrable_fourierConvolution {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    Integrable (fourierConvolution f g) := by
  have h := (hg.integrable_convolution (L := ContinuousLinearMap.mul ℂ ℂ) hf).const_mul
    ((Real.sqrt (2 * Real.pi))⁻¹ : ℂ)
  refine h.congr (Eventually.of_forall fun t => ?_)
  simp only [fourierConvolution, convolution, ContinuousLinearMap.mul_apply']
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  exact mul_comm _ _

/-- DLMF §1.14(i) (convolution theorem): for absolutely integrable `f`, `g` the Fourier
transform of `f * g` (1.14.5) is `F(x) G(x)`. Proved from Mathlib's
`Real.fourier_mul_convolution_eq`. -/
@[dlmf 1.14.i]
theorem fourierTransform_fourierConvolution {f g : ℝ → ℂ} (hf : Integrable f)
    (hg : Integrable g) (x : ℝ) :
    fourierTransform (fourierConvolution f g) x = fourierTransform f x * fourierTransform g x := by
  have hconv : fourierConvolution f g =
      fun t => ((Real.sqrt (2 * Real.pi))⁻¹ : ℂ) *
        convolution g f (ContinuousLinearMap.mul ℂ ℂ) volume t := by
    funext t
    simp only [fourierConvolution, convolution, ContinuousLinearMap.mul_apply']
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    exact mul_comm _ _
  rw [hconv, fourierTransform_const_mul, fourierTransform_eq_fourier,
    Real.fourier_mul_convolution_eq hg hf, fourierTransform_eq_fourier,
    fourierTransform_eq_fourier]
  ring

/-- DLMF 1.14.6: for `f`, `g` absolutely and square integrable,
`(f * g)(t) = (2π)^{-1/2} ∫ F(x) G(x) e^{-itx} dx`. -/
@[dlmf 1.14.E6]
theorem fourierConvolution_eq_integral {f g : ℝ → ℂ} (hf : Integrable f) (hf2 : MemLp f 2)
    (hg : Integrable g) (hg2 : MemLp g 2) (t : ℝ) :
    fourierConvolution f g t = ((Real.sqrt (2 * Real.pi))⁻¹ : ℂ) *
      ∫ x, fourierTransform f x * fourierTransform g x * cexp (-(I * t * x)) := by
  sorry

/-- DLMF 1.14.7: for `f`, `g` absolutely and square integrable,
`∫ F(x) G(x) dx = ∫ f(t) g(-t) dt`. -/
@[dlmf 1.14.E7]
theorem integral_fourierTransform_mul {f g : ℝ → ℂ} (hf : Integrable f) (hf2 : MemLp f 2)
    (hg : Integrable g) (hg2 : MemLp g 2) :
    ∫ x, fourierTransform f x * fourierTransform g x = ∫ t, f t * g (-t) := by
  sorry

/-- DLMF 1.14.7_5 (Parseval's formula): for `f`, `g` absolutely and square integrable,
`∫ F(x) conj(G(x)) dx = ∫ f(t) conj(g(t)) dt`. -/
@[dlmf 1.14.E7_5]
theorem integral_fourierTransform_mul_conj {f g : ℝ → ℂ} (hf : Integrable f) (hf2 : MemLp f 2)
    (hg : Integrable g) (hg2 : MemLp g 2) :
    ∫ x, fourierTransform f x * conj (fourierTransform g x) = ∫ t, f t * conj (g t) := by
  sorry

/-- DLMF 1.14.8 (Parseval's formula, Plancherel): for `f` absolutely and square integrable,
`∫ |F(x)|² dx = ∫ |f(t)|² dt`. Derived from 1.14.7_5. -/
@[dlmf 1.14.E8]
theorem integral_norm_fourierTransform_sq {f : ℝ → ℂ} (hf : Integrable f) (hf2 : MemLp f 2) :
    ∫ x, ‖fourierTransform f x‖ ^ 2 = ∫ t, ‖f t‖ ^ 2 := by
  have h := integral_fourierTransform_mul_conj hf hf2 hf hf2
  simp_rw [mul_conj, normSq_eq_norm_sq] at h
  have h' : ((∫ x, ‖fourierTransform f x‖ ^ 2 : ℝ) : ℂ) = ((∫ t, ‖f t‖ ^ 2 : ℝ) : ℂ) := by
    rw [integral_complex_ofReal, integral_complex_ofReal] at h
    exact h
  exact_mod_cast h'

/-- DLMF §1.14(i) (uniqueness): if `f`, `g` are continuous and absolutely integrable and
`F(x) = G(x)` for all `x`, then `f = g`. Proved from Mathlib's Fourier inversion theorem. -/
@[dlmf 1.14.i]
theorem eq_of_fourierTransform_eq {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hfi : Integrable f) (hgi : Integrable g)
    (h : ∀ x, fourierTransform f x = fourierTransform g x) : f = g := by
  set k : ℝ → ℂ := fun t => f t - g t with hk
  have hki : Integrable k := hfi.sub hgi
  have hkc : Continuous k := hf.sub hg
  have hk0 : ∀ x, fourierTransform k x = 0 := by
    intro x
    have e1 : fourierTransform k x = fourierTransform f x - fourierTransform g x := by
      simp only [fourierTransform, hk, sub_mul]
      rw [integral_sub (g1e_integrable_mul_cexp hfi x) (g1e_integrable_mul_cexp hgi x), mul_sub]
    rw [e1, h x, sub_self]
  have hF0 : 𝓕 k = fun _ => 0 := by
    funext w
    have := hk0 (-(2 * Real.pi) * w)
    rw [fourierTransform_eq_fourier] at this
    have hw : -(-(2 * Real.pi) * w) / (2 * Real.pi) = w := by
      have : (2 * Real.pi : ℝ) ≠ 0 := by positivity
      field_simp
    rw [hw] at this
    exact (mul_eq_zero.mp this).resolve_left g1e_inv_sqrt_ne_zero
  have hinv := hkc.fourierInv_fourier_eq hki (by rw [hF0]; exact integrable_zero _ _ _)
  rw [hF0] at hinv
  funext t
  have := congrFun hinv t
  simp only [Real.fourierInv_eq', smul_zero, integral_zero] at this
  have : k t = 0 := this.symm
  exact sub_eq_zero.mp this

/-! ### Fourier cosine and sine transforms (§1.14(ii)) -/

/-- DLMF 1.14.11: if `f` is absolutely integrable on `[0, ∞)` and of bounded variation near
`u > 0`, then `½(f(u+) + f(u-)) = √(2/π) ∫₀^∞ F_c(x) cos(ux) dx`, the integral taken as
`lim_{R→∞} ∫₀^R`. -/
@[dlmf 1.14.E11]
theorem tendsto_fourierCosTransform_inversion {f : ℝ → ℂ} (hf : IntegrableOn f (Ioi 0))
    {u δ : ℝ} (hu : 0 < u) (hδ : 0 < δ) (hbv : BoundedVariationOn f (Icc (u - δ) (u + δ)))
    {fp fm : ℂ} (hp : Tendsto f (𝓝[>] u) (𝓝 fp)) (hm : Tendsto f (𝓝[<] u) (𝓝 fm)) :
    Tendsto (fun R : ℝ => (Real.sqrt (2 / Real.pi) : ℂ) *
        ∫ x in (0 : ℝ)..R, fourierCosTransform f x * (Real.cos (u * x) : ℂ)) atTop
      (𝓝 ((fp + fm) / 2)) := by
  sorry

/-- DLMF 1.14.12: the sine analogue of 1.14.11,
`½(f(u+) + f(u-)) = √(2/π) ∫₀^∞ F_s(x) sin(ux) dx`, for `u > 0`. -/
@[dlmf 1.14.E12]
theorem tendsto_fourierSinTransform_inversion {f : ℝ → ℂ} (hf : IntegrableOn f (Ioi 0))
    {u δ : ℝ} (hu : 0 < u) (hδ : 0 < δ) (hbv : BoundedVariationOn f (Icc (u - δ) (u + δ)))
    {fp fm : ℂ} (hp : Tendsto f (𝓝[>] u) (𝓝 fp)) (hm : Tendsto f (𝓝[<] u) (𝓝 fm)) :
    Tendsto (fun R : ℝ => (Real.sqrt (2 / Real.pi) : ℂ) *
        ∫ x in (0 : ℝ)..R, fourierSinTransform f x * (Real.sin (u * x) : ℂ)) atTop
      (𝓝 ((fp + fm) / 2)) := by
  sorry

/-- DLMF 1.14.13: for `f`, `g` absolutely and square integrable on `[0, ∞)`,
`∫₀^∞ F_c(x) G_c(x) dx = ∫₀^∞ f(t) g(t) dt`. -/
@[dlmf 1.14.E13]
theorem integral_fourierCosTransform_mul {f g : ℝ → ℂ} (hf : IntegrableOn f (Ioi 0))
    (hf2 : MemLp f 2 (volume.restrict (Ioi 0))) (hg : IntegrableOn g (Ioi 0))
    (hg2 : MemLp g 2 (volume.restrict (Ioi 0))) :
    ∫ x in Ioi (0 : ℝ), fourierCosTransform f x * fourierCosTransform g x =
      ∫ t in Ioi (0 : ℝ), f t * g t := by
  sorry

/-- DLMF 1.14.14: for `f`, `g` absolutely and square integrable on `[0, ∞)`,
`∫₀^∞ F_s(x) G_s(x) dx = ∫₀^∞ f(t) g(t) dt`. -/
@[dlmf 1.14.E14]
theorem integral_fourierSinTransform_mul {f g : ℝ → ℂ} (hf : IntegrableOn f (Ioi 0))
    (hf2 : MemLp f 2 (volume.restrict (Ioi 0))) (hg : IntegrableOn g (Ioi 0))
    (hg2 : MemLp g 2 (volume.restrict (Ioi 0))) :
    ∫ x in Ioi (0 : ℝ), fourierSinTransform f x * fourierSinTransform g x =
      ∫ t in Ioi (0 : ℝ), f t * g t := by
  sorry

/-- DLMF 1.14.15: `∫₀^∞ (F_c(x))² dx = ∫₀^∞ (f(t))² dt` (the case `g = f` of 1.14.13). -/
@[dlmf 1.14.E15]
theorem integral_fourierCosTransform_sq {f : ℝ → ℂ} (hf : IntegrableOn f (Ioi 0))
    (hf2 : MemLp f 2 (volume.restrict (Ioi 0))) :
    ∫ x in Ioi (0 : ℝ), fourierCosTransform f x ^ 2 = ∫ t in Ioi (0 : ℝ), f t ^ 2 := by
  simpa [sq] using integral_fourierCosTransform_mul hf hf2 hf hf2

/-- DLMF 1.14.16: `∫₀^∞ (F_s(x))² dx = ∫₀^∞ (f(t))² dt` (the case `g = f` of 1.14.14). -/
@[dlmf 1.14.E16]
theorem integral_fourierSinTransform_sq {f : ℝ → ℂ} (hf : IntegrableOn f (Ioi 0))
    (hf2 : MemLp f 2 (volume.restrict (Ioi 0))) :
    ∫ x in Ioi (0 : ℝ), fourierSinTransform f x ^ 2 = ∫ t in Ioi (0 : ℝ), f t ^ 2 := by
  simpa [sq] using integral_fourierSinTransform_mul hf hf2 hf hf2

end DLMF.AlgebraicAnalytic
