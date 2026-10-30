/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AlgebraicAnalytic.Transforms.Basic
public import Mathlib.Analysis.Fourier.Convolution
public import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import DLMFMathlib.Analysis.Fourier.L2Compatibility
public import DLMFMathlib.MeasureTheory.Integral.HalfLine

/-!
# Fourier, Fourier cosine and Fourier sine transforms (DLMF §1.14(i)–(ii))

The statements of DLMF §1.14(i)–(ii) for DLMF's Fourier transform
`𝓕(f)(x) = (2π)^{-1/2} ∫ f(t) e^{ixt} dt` (`fourierTransform`, 1.14.1) and the cosine and sine
transforms on `(0, ∞)`.

Proved here from Mathlib through the bridge `fourierTransform_eq_fourier`
(`𝓕(f)(x) = (2π)^{-1/2} 𝓕_Mathlib f(-x/(2π))`): continuity and the Riemann–Lebesgue lemma
(§1.14(i)), the bound 1.14.2, the inversion formula 1.14.4 when `F = 𝓕(f)` is integrable, the
convolution theorem (§1.14(i), after 1.14.5) and the uniqueness theorem. The integral
Fourier transform agrees almost everywhere with Mathlib's unitary `L²` transform, yielding
Parseval's formula 1.14.7_5, its bilinear form 1.14.7, convolution inversion 1.14.6 and the
norm identity 1.14.8. Even and odd extensions give the cosine and sine pairings
1.14.13–1.14.16. The bounded-variation inversion theorem 1.14.3, the principal-value form
of 1.14.4 and the half-line inversion theorems 1.14.11–1.14.12 remain admitted.

Hypotheses DLMF leaves implicit are explicit: integrability for each transform, and the one-sided
limits `f(u±)` in 1.14.3 are given as hypotheses (they exist for functions of bounded variation).
-/

@[expose] public noncomputable section

open MeasureTheory Complex Set Filter Topology
open scoped FourierTransform ComplexConjugate ENNReal

namespace DLMF.AlgebraicAnalytic

/-- The normalizing constant: `(2π)^{-1/2} · (2π)^{-1/2} = (2π)⁻¹` in `ℂ`. -/
private lemma g1e_inv_sqrt_mul_self :
    ((Real.sqrt (2 * Real.pi))⁻¹ : ℂ) * ((Real.sqrt (2 * Real.pi))⁻¹ : ℂ) =
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ := by
  rw [← mul_inv, ← ofReal_mul, Real.mul_self_sqrt (by positivity)]

/-- Nonvanishing under the stated hypotheses: `((Real.sqrt (2 * Real.pi))⁻¹ : ℂ) ≠ 0`. -/
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

/-- The two-sided Fourier normalization turns a factor of `2` into `sqrt(2/π)`. -/
lemma inv_sqrt_two_pi_mul_two :
    ((Real.sqrt (2 * Real.pi))⁻¹ : ℂ) * 2 = (Real.sqrt (2 / Real.pi) : ℂ) := by
  have h : (Real.sqrt (2 * Real.pi))⁻¹ * 2 = Real.sqrt (2 / Real.pi) := by
    apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow, inv_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    field_simp
  exact_mod_cast h

/-- The Fourier transform is linear in a constant factor. -/
theorem fourierTransform_const_mul (c : ℂ) (f : ℝ → ℂ) (x : ℝ) :
    fourierTransform (fun t => c * f t) x = c * fourierTransform f x := by
  simp only [fourierTransform, mul_assoc, integral_const_mul]
  ring

/-- Conjugating and reflecting a function conjugates its Fourier transform. -/
theorem fourierTransform_conj_neg (f : ℝ → ℂ) (x : ℝ) :
    fourierTransform (fun t => conj (f (-t))) x = conj (fourierTransform f x) := by
  unfold fourierTransform
  rw [map_mul, map_inv₀, conj_ofReal, ← integral_conj,
    ← integral_neg_eq_self (fun t : ℝ => conj (f t * cexp (I * x * t))) volume]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by simp [map_mul, ← exp_conj, mul_assoc]

/-- Translating a function multiplies its Fourier transform by the corresponding phase. -/
theorem fourierTransform_comp_sub (f : ℝ → ℂ) (t x : ℝ) :
    fourierTransform (fun u => f (u - t)) x = cexp (I * x * t) * fourierTransform f x := by
  unfold fourierTransform
  rw [← integral_add_right_eq_self (fun u : ℝ => f (u - t) * cexp (I * x * u)) t]
  simp_rw [add_sub_cancel_right, ofReal_add, mul_add, Complex.exp_add]
  simp_rw [← mul_assoc]
  rw [integral_mul_const]
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

/-- DLMF 1.14.7_5 (Parseval's formula): for `f`, `g` absolutely and square integrable,
`∫ F(x) conj(G(x)) dx = ∫ f(t) conj(g(t)) dt`. -/
@[dlmf 1.14.E7_5]
theorem integral_fourierTransform_mul_conj {f g : ℝ → ℂ} (hf : Integrable f) (hf2 : MemLp f 2)
    (hg : Integrable g) (hg2 : MemLp g 2) :
    ∫ x, fourierTransform f x * conj (fourierTransform g x) = ∫ t, f t * conj (g t) := by
  let a : ℝ := -(1 / (2 * Real.pi))
  have he : (fun x => fourierTransform f x * conj (fourierTransform g x)) =
      fun x => ((2 * Real.pi : ℝ) : ℂ)⁻¹ * (𝓕 f (a * x) * conj (𝓕 g (a * x))) := by
    funext x
    rw [fourierTransform_eq_fourier, fourierTransform_eq_fourier, map_mul, map_inv₀, conj_ofReal]
    have hx : -x / (2 * Real.pi) = a * x := by dsimp [a]; ring
    rw [hx, ← g1e_inv_sqrt_mul_self]
    ring
  rw [he, integral_const_mul, Measure.integral_comp_mul_left (fun x => 𝓕 f x * conj (𝓕 g x)) a]
  have habs : |a⁻¹| = 2 * Real.pi := by
    dsimp [a]
    rw [inv_neg, one_div, inv_inv, abs_neg, abs_of_pos (by positivity)]
  rw [habs, Complex.real_smul, ← mul_assoc,
    inv_mul_cancel₀ (ofReal_ne_zero.mpr (by positivity)), one_mul]
  exact Real.integral_fourier_mul_conj_eq hf hf2 hg hg2

/-- DLMF 1.14.6: for `f`, `g` absolutely and square integrable,
`(f * g)(t) = (2π)^{-1/2} ∫ F(x) G(x) e^{-itx} dx`. -/
@[dlmf 1.14.E6]
theorem fourierConvolution_eq_integral {f g : ℝ → ℂ} (hf : Integrable f) (hf2 : MemLp f 2)
    (hg : Integrable g) (hg2 : MemLp g 2) (t : ℝ) :
    fourierConvolution f g t = ((Real.sqrt (2 * Real.pi))⁻¹ : ℂ) *
      ∫ x, fourierTransform f x * fourierTransform g x * cexp (-(I * t * x)) := by
  have hi : Integrable (fun u => conj (f (t - u))) := by
    simpa only [Function.comp_def, Complex.conjLIE_apply] using
      (volume.measurePreserving_sub_left t).integrable_comp_of_integrable
        ((Complex.conjLIE.integrable_comp_iff).mpr hf)
  have hm : MemLp (fun u => conj (f (t - u))) 2 := by
    simpa only [Function.comp_def, Pi.star_apply, RCLike.star_def] using
      hf2.star.comp_measurePreserving (volume.measurePreserving_sub_left t)
  have he (x : ℝ) : fourierTransform (fun u => conj (f (t - u))) x =
      cexp (I * x * t) * conj (fourierTransform f x) := by
    convert fourierTransform_comp_sub (fun u => conj (f (-u))) t x using 1
    · congr 1; ext u; congr 2; ring
    · rw [fourierTransform_conj_neg]
  have h := integral_fourierTransform_mul_conj hg hg2 hi hm
  simp_rw [he, map_mul, starRingEnd_self_apply, ← exp_conj] at h
  unfold fourierConvolution
  have hright : (∫ u, g u * f (t - u)) = ∫ u, f (t - u) * g u := by
    simp_rw [mul_comm (g _) (f _)]
  rw [hright] at h
  rw [← h]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by simp [mul_assoc, mul_comm, mul_left_comm]

/-- DLMF 1.14.7: for `f`, `g` absolutely and square integrable,
`∫ F(x) G(x) dx = ∫ f(t) g(-t) dt`. -/
@[dlmf 1.14.E7]
theorem integral_fourierTransform_mul {f g : ℝ → ℂ} (hf : Integrable f) (hf2 : MemLp f 2)
    (hg : Integrable g) (hg2 : MemLp g 2) :
    ∫ x, fourierTransform f x * fourierTransform g x = ∫ t, f t * g (-t) := by
  have hi : Integrable (fun t => conj (g (-t))) := by
    simpa only [Function.comp_def, Complex.conjLIE_apply] using
      (volume.measurePreserving_neg).integrable_comp_of_integrable
        ((Complex.conjLIE.integrable_comp_iff).mpr hg)
  have hm : MemLp (fun t => conj (g (-t))) 2 := by
    simpa only [Function.comp_def, Pi.star_apply, RCLike.star_def] using
      hg2.star.comp_measurePreserving (volume.measurePreserving_neg)
  have h := integral_fourierTransform_mul_conj hf hf2 hi hm
  simpa only [fourierTransform_conj_neg, starRingEnd_self_apply] using h

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

/-- The even extension of a half-line function belongs to `L¹`. -/
private theorem integrable_evenExtension {f : ℝ → ℂ} (hf : IntegrableOn f (Ioi 0)) :
    Integrable (fun t : ℝ => f |t|) :=
  memLp_one_iff_integrable.mp ((memLp_one_iff_integrable.mpr hf).comp_abs)

/-- An extension odd away from zero belongs to the same `Lᵖ` space. The value at zero
is irrelevant for Lebesgue measure. -/
private theorem memLp_oddExtension {f : ℝ → ℂ} {p : ℝ≥0∞}
    (hf : MemLp f p (volume.restrict (Ioi 0))) :
    MemLp (fun t : ℝ => if 0 ≤ t then f |t| else -f |t|) p := by
  have h := hf.comp_abs
  have hp := MemLp.piecewise (s := Ici (0 : ℝ)) measurableSet_Ici.nullMeasurableSet
    (h.restrict _) (h.neg.restrict _)
  apply (memLp_congr_ae (f := (Ici (0 : ℝ)).piecewise (fun t => f |t|)
    (-fun t => f |t|)) ?_).mp hp
  exact Filter.Eventually.of_forall fun t => by simp [piecewise, mem_Ici]

/-- The Fourier transform of an even extension is the cosine transform. -/
private theorem fourierTransform_evenExtension {f : ℝ → ℂ} (hf : IntegrableOn f (Ioi 0))
    (x : ℝ) : fourierTransform (fun t : ℝ => f |t|) x = fourierCosTransform f x := by
  have hi := integral_eq_integral_Ioi_add_neg
    (g1e_integrable_mul_cexp (integrable_evenExtension hf) x)
  have he (t : ℝ) (ht : 0 < t) :
      f |t| * cexp (I * x * t) + f |-t| * cexp (I * x * (-t)) =
      2 * (f t * (Real.cos (x * t) : ℂ)) := by
    rw [abs_neg, abs_of_pos ht, ofReal_cos]
    simp only [Complex.cos, ofReal_mul]
    rw [show I * (x : ℂ) * t = ↑x * t * I by ring,
      show I * (x : ℂ) * -t = -(↑x * t * I) by ring]
    ring
  simp only [ofReal_neg] at hi
  rw [setIntegral_congr_fun measurableSet_Ioi he, integral_const_mul] at hi
  unfold fourierTransform fourierCosTransform
  rw [hi, ← mul_assoc]
  congr 1
  exact inv_sqrt_two_pi_mul_two

/-- The Fourier transform of an extension odd away from zero is `i` times the sine transform. -/
private theorem fourierTransform_oddExtension {f : ℝ → ℂ} (hf : IntegrableOn f (Ioi 0))
    (x : ℝ) : fourierTransform (fun t : ℝ => if 0 ≤ t then f |t| else -f |t|) x =
      I * fourierSinTransform f x := by
  have hfull : Integrable (fun t : ℝ => if 0 ≤ t then f |t| else -f |t|) :=
    memLp_one_iff_integrable.mp (memLp_oddExtension (memLp_one_iff_integrable.mpr hf))
  have hi := integral_eq_integral_Ioi_add_neg (g1e_integrable_mul_cexp hfull x)
  have he (t : ℝ) (ht : 0 < t) :
      (if 0 ≤ t then f |t| else -f |t|) * cexp (I * x * t) +
        (if 0 ≤ -t then f |-t| else -f |-t|) * cexp (I * x * (-t)) =
      2 * I * (f t * (Real.sin (x * t) : ℂ)) := by
    simp only [ite_eq_left ht.le, ite_eq_right (not_le.mpr (neg_neg_of_pos ht)), abs_of_pos ht,
      abs_neg, ofReal_sin, Complex.sin, ofReal_mul]
    rw [show I * (x : ℂ) * t = ↑x * t * I by ring,
      show I * (x : ℂ) * -t = -(↑x * t * I) by ring]
    ring_nf
    simp [I_sq]
    ring
  simp only [ofReal_neg] at hi
  rw [setIntegral_congr_fun measurableSet_Ioi he, integral_const_mul] at hi
  unfold fourierTransform fourierSinTransform
  rw [hi]
  linear_combination I * (∫ t in Ioi (0 : ℝ), f t * (Real.sin (x * t) : ℂ)) *
    inv_sqrt_two_pi_mul_two

/-- A cosine transform is even in its frequency. -/
private theorem fourierCosTransform_abs (f : ℝ → ℂ) (x : ℝ) :
    fourierCosTransform f |x| = fourierCosTransform f x := by
  unfold fourierCosTransform
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by
    rcases le_or_gt 0 x with hx | hx <;> simp [abs_of_nonneg, abs_of_neg, hx]

/-- The product of two sine transforms is even in its frequency. -/
private theorem fourierSinTransform_mul_abs (f g : ℝ → ℂ) (x : ℝ) :
    fourierSinTransform f |x| * fourierSinTransform g |x| =
      fourierSinTransform f x * fourierSinTransform g x := by
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · have he (h : ℝ → ℂ) : fourierSinTransform h (-x) = -fourierSinTransform h x := by
      simp only [fourierSinTransform, neg_mul, Real.sin_neg, ofReal_neg, mul_neg, integral_neg]
    rw [abs_of_neg hx, he, he, neg_mul_neg]

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
  have h := integral_fourierTransform_mul (integrable_evenExtension hf) hf2.comp_abs
    (integrable_evenExtension hg) hg2.comp_abs
  simp_rw [fourierTransform_evenExtension hf, fourierTransform_evenExtension hg, abs_neg] at h
  have hleft : (∫ x, fourierCosTransform f x * fourierCosTransform g x) =
      (2 : ℝ) • ∫ x in Ioi (0 : ℝ), fourierCosTransform f x * fourierCosTransform g x := by
    have he := integral_comp_abs_eq_two_smul
      (fun x => fourierCosTransform f x * fourierCosTransform g x)
    simpa only [fourierCosTransform_abs] using he
  rw [hleft, integral_comp_abs_eq_two_smul (fun t => f t * g t)] at h
  simp only [Complex.real_smul, ofReal_ofNat] at h
  exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) h

/-- DLMF 1.14.14: for `f`, `g` absolutely and square integrable on `[0, ∞)`,
`∫₀^∞ F_s(x) G_s(x) dx = ∫₀^∞ f(t) g(t) dt`. -/
@[dlmf 1.14.E14]
theorem integral_fourierSinTransform_mul {f g : ℝ → ℂ} (hf : IntegrableOn f (Ioi 0))
    (hf2 : MemLp f 2 (volume.restrict (Ioi 0))) (hg : IntegrableOn g (Ioi 0))
    (hg2 : MemLp g 2 (volume.restrict (Ioi 0))) :
    ∫ x in Ioi (0 : ℝ), fourierSinTransform f x * fourierSinTransform g x =
      ∫ t in Ioi (0 : ℝ), f t * g t := by
  have hfi : Integrable (fun t : ℝ => if 0 ≤ t then f |t| else -f |t|) :=
    memLp_one_iff_integrable.mp (memLp_oddExtension (memLp_one_iff_integrable.mpr hf))
  have hgi : Integrable (fun t : ℝ => if 0 ≤ t then g |t| else -g |t|) :=
    memLp_one_iff_integrable.mp (memLp_oddExtension (memLp_one_iff_integrable.mpr hg))
  have h := integral_fourierTransform_mul hfi (memLp_oddExtension hf2)
    hgi (memLp_oddExtension hg2)
  simp_rw [fourierTransform_oddExtension hf, fourierTransform_oddExtension hg] at h
  have hleft : (∫ x, I * fourierSinTransform f x * (I * fourierSinTransform g x)) =
      -(2 : ℝ) • ∫ x in Ioi (0 : ℝ), fourierSinTransform f x * fourierSinTransform g x := by
    have he := integral_comp_abs_eq_two_smul
      (fun x => fourierSinTransform f x * fourierSinTransform g x)
    simp_rw [fourierSinTransform_mul_abs] at he
    simp_rw [show ∀ u v : ℂ, I * u * (I * v) = -(u * v) by
      intro u v
      linear_combination u * v * I_sq]
    rw [integral_neg, he, neg_smul]
  have hright : (∫ t, (if 0 ≤ t then f |t| else -f |t|) *
      (if 0 ≤ -t then g |-t| else -g |-t|)) =
      -(2 : ℝ) • ∫ t in Ioi (0 : ℝ), f t * g t := by
    have he : (fun t : ℝ => (if 0 ≤ t then f |t| else -f |t|) *
        (if 0 ≤ -t then g |-t| else -g |-t|)) =ᵐ[volume]
        fun t => -(f |t| * g |t|) := by
      filter_upwards [volume.ae_ne (0 : ℝ)] with t ht
      rcases lt_or_gt_of_ne ht with ht | ht
      · simp [abs_neg, not_le.mpr ht, (neg_pos.mpr ht).le]
      · simp [abs_neg, ht.le, not_le.mpr (neg_neg_of_pos ht)]
    rw [integral_congr_ae he, integral_neg,
      integral_comp_abs_eq_two_smul (fun t => f t * g t), neg_smul]
  rw [hleft, hright] at h
  simp only [Complex.real_smul, ofReal_neg, ofReal_ofNat] at h
  exact mul_left_cancel₀ (by norm_num : -(2 : ℂ) ≠ 0) h

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
