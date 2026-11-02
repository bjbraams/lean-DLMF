/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AlgebraicAnalytic.Distributions.Basic
public import DLMF.AlgebraicAnalytic.Transforms.Fourier
public import Mathlib.MeasureTheory.Integral.PeakFunction
public import Mathlib.Algebra.BigOperators.Group.Finset.Interval
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
public import DLMF.Airy.Properties
public import DLMF.Coulomb.Energy.Basic
public import DLMF.Legendre.Harmonics

/-!
# Integral and series representations of the Dirac delta (DLMF §1.17)

Representations of the Dirac delta by delta sequences, Fourier integrals, Bessel, Coulomb and
Airy kernels, Fourier series and orthogonal-polynomial expansions.

## Main results

* `delta_apply_eq_zero_of_notMem_tsupport`: `δ(x) = 0` for `x ≠ 0` (DLMF 1.17.1); see also
  Mathlib's `Distribution.delta`.
* `tendsto_gaussian_integral`, `isDeltaSequence_gaussian`, `tendsto_gaussian_integral_of_growth`,
  `tendsto_gaussian_integral_jump`: the Gaussian delta sequence (DLMF 1.17.3–1.17.7).
* `fourier_inversion_dlmf`, `gaussian_fourier_eq`, `isDeltaSequence_gaussian_fourier`,
  `tendsto_fourier_kernel`: Fourier inversion and `δ(x-a) = (2π)⁻¹ ∫ e^{i(x-a)t} dt`
  (DLMF 1.17.8–1.17.12).
* `tendsto_cos_kernel`, `tendsto_sin_kernel`, `tendsto_bessel_kernel`,
  `tendsto_sphericalBessel_kernel`, `tendsto_coulomb_kernel`, `tendsto_airy_kernel`:
  DLMF 1.17.12_1–1.17.16.
* `tendsto_fourier_series`, `dirichletKernel_eq`, `tendsto_dirichletKernel_integral`: Fourier
  series and the Dirichlet kernel (DLMF 1.17.17–1.17.21).
* `tendsto_legendre_kernel`, `tendsto_laguerre_kernel`, `tendsto_hermite_kernel`,
  `tendsto_sphericalHarmonic_kernel`: DLMF 1.17.22–1.17.25.

## Implementation notes

DLMF writes the Dirac delta as a symbolic function `δ(x)` (1.17.1–1.17.2). Following the
rigorous reading of DLMF §1.17(i) and §1.17(iv), every representation here is stated as a
weak limit against test functions: a family `δ_R(x, a)` represents `δ(x - a)` when
`lim ∫ δ_R(x, a) φ(x) dx = φ(a)` for every smooth compactly supported `φ` (on the stated
interval), or for the class of functions DLMF names. Nothing is stated pointwise.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory Complex
open scoped Topology Distributions

namespace DLMF.AlgebraicAnalytic

/-! ## §1.17(i): delta sequences -/

/-- DLMF 1.17.1: `δ(x) = 0` for `x ≠ 0`, in the sense of distributions: `⟨δ, φ⟩ = 0` for
every test function whose support avoids `0`. -/
@[dlmf 1.17.E1]
theorem delta_apply_eq_zero_of_notMem_tsupport {Ω : TopologicalSpace.Opens ℝ}
    (φ : 𝓓(Ω, ℝ)) (h : (0 : ℝ) ∉ tsupport φ) :
    (Distribution.delta 0 : 𝓓'(Ω, ℝ)) φ = 0 := by
  rw [Distribution.delta_apply]
  exact image_eq_zero_of_notMem_tsupport h

/-- Identity under the stated parameter and domain assumptions: `∫ x, normalizedGaussian x = 1`. -/
private lemma integral_normalizedGaussian : ∫ x, normalizedGaussian x = 1 := by
  have h := integral_gaussian 1
  simp only [neg_mul, one_mul, div_one] at h
  simp only [normalizedGaussian, integral_div, h]
  exact div_self (by positivity)

/-- The map `(fun x : ℝ => ‖x‖ ^ Module.finrank ℝ ℝ * normalizedGaussian x)` tends to `(𝓝 0)`
along `(Bornology.cobounded ℝ)`. -/
private lemma tendsto_norm_pow_mul_normalizedGaussian :
    Tendsto (fun x : ℝ => ‖x‖ ^ Module.finrank ℝ ℝ * normalizedGaussian x) (Bornology.cobounded ℝ)
      (𝓝 0) := by
  rw [Metric.cobounded_eq_cocompact, cocompact_eq_atBot_atTop, ← comap_abs_atTop]
  have key : Tendsto (fun r : ℝ => r * Real.exp (-r ^ 2) / Real.sqrt Real.pi) atTop (𝓝 0) := by
    have h1 : Tendsto (fun r : ℝ => r ^ 1 * Real.exp (-r)) atTop (𝓝 0) :=
      Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    have h2 : Tendsto (fun r : ℝ => r * Real.exp (-r ^ 2)) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h1 ?_ ?_
      · filter_upwards [eventually_ge_atTop 0] with r hr
        positivity
      · filter_upwards [eventually_ge_atTop 1] with r hr
        rw [pow_one]
        gcongr
        nlinarith
    simpa using h2.div_const (Real.sqrt Real.pi)
  have : (fun x : ℝ => ‖x‖ ^ Module.finrank ℝ ℝ * normalizedGaussian x) =
      (fun r : ℝ => r * Real.exp (-r ^ 2) / Real.sqrt Real.pi) ∘ abs := by
    ext x
    simp [normalizedGaussian, Real.norm_eq_abs, sq_abs, mul_div_assoc]
  rw [this]
  exact key.comp tendsto_comap

/-- DLMF 1.17.5–1.17.6: `lim_{n→∞} √(n/π) ∫ e^{-n(x-a)²} φ(x) dx = φ(a)`, here for `φ`
integrable and continuous at `a` (proved from Mathlib's peak-function theorem
`tendsto_integral_comp_smul_smul_of_integrable'`). The general DLMF hypothesis (absolute
convergence for large `n`) is `tendsto_gaussian_integral_of_growth`. -/
@[dlmf 1.17.E5, dlmf 1.17.E6]
theorem tendsto_gaussian_integral {φ : ℝ → ℂ} {a : ℝ} (hφ : Integrable φ)
    (ha : ContinuousAt φ a) :
    Tendsto (fun n : ℕ => ∫ x, gaussianDeltaSeq n (x - a) * φ x) atTop (𝓝 (φ a)) := by
  have hmain := tendsto_integral_comp_smul_smul_of_integrable' (μ := volume)
    (fun x => by unfold normalizedGaussian; positivity) integral_normalizedGaussian
        tendsto_norm_pow_mul_normalizedGaussian hφ ha
  have hs : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  refine (hmain.comp hs).congr fun n => ?_
  simp only [Function.comp_apply, Module.finrank_self, pow_one]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [gaussianDeltaSeq, normalizedGaussian, smul_eq_mul, Complex.real_smul]
  congr 1
  rw [Real.sqrt_div' _ Real.pi_pos.le, mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  push_cast
  ring_nf

/-- The Gaussian sequence is a delta sequence (DLMF 1.17.3 for 1.17.5). -/
@[dlmf 1.17.E3, dlmf 1.17.E5]
theorem isDeltaSequence_gaussian : IsDeltaSequence gaussianDeltaSeq := fun _ hφ hcs _ =>
  tendsto_gaussian_integral (hφ.continuous.integrable_of_hasCompactSupport hcs)
    hφ.continuous.continuousAt

/-- DLMF 1.17.6: `φ` continuous at `a` and `∫ e^{-n(x-a)²} φ(x) dx` absolutely convergent for
some (hence all larger) `n`; this covers `φ(x) = O(e^{αx²})`. DLMF also assumes `φ` locally
integrable, which is not needed (stronger than DLMF). -/
@[dlmf 1.17.E6]
theorem tendsto_gaussian_integral_of_growth {φ : ℝ → ℂ} {a : ℝ} (n₀ : ℕ)
    (hφ : Integrable fun x => (Real.exp (-(n₀ * (x - a) ^ 2)) : ℂ) * φ x)
    (ha : ContinuousAt φ a) :
    Tendsto (fun n : ℕ => ∫ x, gaussianDeltaSeq n (x - a) * φ x) atTop (𝓝 (φ a)) := by
  let ψ : ℝ → ℂ := fun x => (Real.exp (-(n₀ * (x - a) ^ 2)) : ℂ) * φ x
  have hψ : ContinuousAt ψ a := by
    exact (by fun_prop : Continuous fun x : ℝ =>
      (Real.exp (-(n₀ * (x - a) ^ 2)) : ℂ)).continuousAt.mul ha
  have hbase := tendsto_gaussian_integral (φ := ψ) hφ hψ
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hdiv : Tendsto (fun n : ℕ => (n₀ : ℝ) / n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hn
  have hratio : Tendsto (fun n : ℕ => Real.sqrt ((n + n₀ : ℝ) / n)) atTop (𝓝 1) := by
    have hlim : Tendsto (fun n : ℕ => ((n : ℝ) + n₀) / n) atTop (𝓝 1) := by
      have h := tendsto_const_nhds.add hdiv (a := (1 : ℝ))
      simp only [add_zero] at h
      refine h.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (n : ℝ) ≠ 0 := by positivity
      field_simp
    convert hlim.sqrt using 1
    norm_num
  have hmul := ((Complex.continuous_ofReal.tendsto 1).comp hratio).mul hbase
  simp only [ψ, sub_self, zero_pow two_ne_zero, mul_zero, neg_zero, Real.exp_zero, ofReal_one,
    one_mul] at hmul
  rw [← tendsto_add_atTop_iff_nat n₀]
  refine hmul.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have he : Real.exp (-(((n : ℝ) + n₀) * (x - a) ^ 2)) =
      Real.exp (-((n : ℝ) * (x - a) ^ 2)) * Real.exp (-(n₀ * (x - a) ^ 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hs : Real.sqrt (((n : ℝ) + n₀) / n) * Real.sqrt ((n : ℝ) / Real.pi) =
      Real.sqrt (((n : ℝ) + n₀) / Real.pi) := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
  simp only [gaussianDeltaSeq, Nat.cast_add, ψ, he, Function.comp_apply]
  have hsc := congrArg (fun t : ℝ => (t : ℂ)) hs
  simp only [ofReal_mul] at hsc ⊢
  linear_combination (↑(Real.exp (-((n : ℝ) * (x - a) ^ 2))) *
    ↑(Real.exp (-(n₀ * (x - a) ^ 2))) * φ x) * hsc

/-- DLMF 1.17.7: for `φ` piecewise continuous with one-sided limits `φ(a±)` at `a`, and the
Gaussian integrals absolutely convergent for large `n`,
`lim √(n/π) ∫ e^{-n(x-a)²} φ(x) dx = ½ φ(a-) + ½ φ(a+)`. -/
@[dlmf 1.17.E7]
theorem tendsto_gaussian_integral_jump {φ : ℝ → ℂ} {a : ℝ} {φm φp : ℂ} (n₀ : ℕ)
    (hφ : Integrable fun x => (Real.exp (-(n₀ * (x - a) ^ 2)) : ℂ) * φ x)
    (hloc : LocallyIntegrable φ) (hm : Tendsto φ (𝓝[<] a) (𝓝 φm))
    (hp : Tendsto φ (𝓝[>] a) (𝓝 φp)) :
    Tendsto (fun n : ℕ => ∫ x, gaussianDeltaSeq n (x - a) * φ x) atTop
      (𝓝 ((1 / 2 : ℂ) * φm + (1 / 2 : ℂ) * φp)) := by
  sorry

/-! ## §1.17(ii): integral representations -/

/-- DLMF 1.17.8 (Fourier inversion in the normalization of 1.14.1, 1.14.4):
`(2π)⁻¹ ∫ e^{-iat} (∫ φ(x) e^{itx} dx) dt = φ(a)` for `φ` integrable, continuous, with
integrable Fourier transform. -/
@[dlmf 1.17.E8]
theorem fourier_inversion_dlmf {φ : ℝ → ℂ} (hφ : Integrable φ) (hc : Continuous φ)
    (hF : Integrable fun t : ℝ => ∫ x, φ x * exp (I * t * x)) (a : ℝ) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, exp (-(I * a * t)) * ∫ x, φ x * exp (I * t * x) =
      φ a := by
  have hFT : Integrable (fourierTransform φ) := hF.const_mul _
  have hi := (fourierTransform_inversion hc hφ hFT a).symm
  simp only [fourierTransform] at hi
  simp_rw [mul_assoc] at hi
  rw [integral_const_mul] at hi
  have hnorm : (((Real.sqrt (2 * Real.pi))⁻¹ : ℂ) *
      ((Real.sqrt (2 * Real.pi))⁻¹ : ℂ)) = (1 / (2 * Real.pi) : ℂ) := by
    rw [← mul_inv, ← pow_two, ← ofReal_pow, Real.sq_sqrt (by positivity)]
    push_cast
    ring
  rw [← mul_assoc, hnorm] at hi
  convert hi using 1
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  rw [mul_comm (cexp _)]
  congr 2 <;> ring

/-- DLMF 1.17.10: `(2π)⁻¹ ∫ e^{-t²/(4n)} e^{i(x-a)t} dt = √(n/π) e^{-n(x-a)²}` for `n > 0`. -/
@[dlmf 1.17.E10]
theorem gaussian_fourier_eq {n : ℝ} (hn : 0 < n) (x a : ℝ) :
    (1 / (2 * Real.pi) : ℂ) *
        ∫ t : ℝ, (Real.exp (-(t ^ 2 / (4 * n))) : ℂ) * exp (I * (x - a) * t) =
      ((Real.sqrt (n / Real.pi) * Real.exp (-(n * (x - a) ^ 2)) : ℝ) : ℂ) := by
  have hb : (-(1 / (4 * n : ℂ))).re < 0 := by
    have : (1 / (4 * n : ℂ)) = ((1 / (4 * n) : ℝ) : ℂ) := by push_cast; ring
    rw [this, neg_re, ofReal_re]
    have : 0 < 1 / (4 * n) := by positivity
    linarith
  have h := integral_cexp_quadratic hb (I * (x - a)) 0
  have e : (fun t : ℝ => (Real.exp (-(t ^ 2 / (4 * n))) : ℂ) * exp (I * (x - a) * t)) =
      fun t : ℝ => cexp (-(1 / (4 * n : ℂ)) * t ^ 2 + I * (x - a) * t + 0) := by
    ext t
    rw [ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [e, h]
  have hn' : (n : ℂ) ≠ 0 := ofReal_ne_zero.mpr hn.ne'
  have h1 : ((Real.pi : ℂ) / -(-(1 / (4 * (n : ℂ))))) = ((4 * Real.pi * n : ℝ) : ℂ) := by
    push_cast
    field_simp
  have h2 : (0 : ℂ) - (I * (x - a)) ^ 2 / (4 * -(1 / (4 * (n : ℂ)))) =
      ((-(n * (x - a) ^ 2) : ℝ) : ℂ) := by
    push_cast
    field_simp
    rw [I_sq]
    ring
  have h4 : ((1 / 2 : ℂ)) = ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [h1, h2, h4, ← ofReal_cpow (by positivity), ← ofReal_exp, ← Real.sqrt_eq_rpow]
  have hπ : 0 < Real.pi := Real.pi_pos
  have h5 : Real.sqrt (4 * Real.pi * n) = 2 * Real.pi * Real.sqrt (n / Real.pi) := by
    rw [show 4 * Real.pi * n = (2 * Real.pi) ^ 2 * (n / Real.pi) by field_simp; ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  rw [h5]
  push_cast
  field_simp

/-- DLMF 1.17.11 (with 1.17.10 and 1.17.5): `δₙ(x - a) = (2π)⁻¹ ∫ e^{-t²/(4n)} e^{i(x-a)t} dt`
is the Gaussian delta sequence, hence a delta sequence. -/
@[dlmf 1.17.E11]
theorem isDeltaSequence_gaussian_fourier :
    IsDeltaSequence fun n y => if n = 0 then 0 else (1 / (2 * Real.pi) : ℂ) *
      ∫ t : ℝ, (Real.exp (-(t ^ 2 / (4 * n))) : ℂ) * exp (I * y * t) := by
  intro φ hφ hcs a
  refine (isDeltaSequence_gaussian φ hφ hcs a).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  have hn0 : n ≠ 0 := by omega
  simp only [hn0, ite_false]
  have := gaussian_fourier_eq (n := (n : ℝ)) (by positivity) (x - a) 0
  push_cast at this ⊢
  simp only [sub_zero] at this
  rw [this]
  simp [gaussianDeltaSeq]

/-- `(2/π) ∫₀^R cos(xt) cos(at) dt` as a sum of two Dirichlet kernels, `x ≠ ±a`. -/
private lemma two_div_pi_integral_cos_mul_cos {x a : ℝ} (h1 : x - a ≠ 0) (h2 : x + a ≠ 0)
    (R : ℝ) :
    2 / Real.pi * ∫ t in (0 : ℝ)..R, Real.cos (x * t) * Real.cos (a * t) =
      Real.sin (R * (a - x)) / (Real.pi * (a - x)) +
        Real.sin (R * (-a - x)) / (Real.pi * (-a - x)) := by
  have hd : ∀ t ∈ uIcc (0 : ℝ) R, HasDerivAt (fun t => Real.sin ((x - a) * t) / (2 * (x - a)) +
      Real.sin ((x + a) * t) / (2 * (x + a))) (Real.cos (x * t) * Real.cos (a * t)) t := by
    intro t _
    have e1 := ((hasDerivAt_id t).const_mul (x - a)).sin.div_const (2 * (x - a))
    have e2 := ((hasDerivAt_id t).const_mul (x + a)).sin.div_const (2 * (x + a))
    convert e1.add e2 using 1
    · rfl
    simp only [id]
    rw [sub_mul, add_mul, Real.cos_sub, Real.cos_add]
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (by
    exact (by fun_prop : Continuous fun t => Real.cos (x * t) *
      Real.cos (a * t)).intervalIntegrable _ _)]
  have : Real.pi ≠ 0 := Real.pi_ne_zero
  have h3 : a - x ≠ 0 := fun h => h1 (by linarith)
  have h4 : -a - x ≠ 0 := fun h => h2 (by linarith)
  rw [show Real.sin (R * (a - x)) = -Real.sin ((x - a) * R) by rw [← Real.sin_neg]; ring_nf,
    show Real.sin (R * (-a - x)) = -Real.sin ((x + a) * R) by rw [← Real.sin_neg]; ring_nf]
  simp only [mul_zero, Real.sin_zero, zero_div, add_zero, sub_zero]
  field_simp
  ring

/-- `(2/π) ∫₀^R sin(xt) sin(at) dt` as a difference of two Dirichlet kernels, `x ≠ ±a`. -/
private lemma two_div_pi_integral_sin_mul_sin {x a : ℝ} (h1 : x - a ≠ 0) (h2 : x + a ≠ 0)
    (R : ℝ) :
    2 / Real.pi * ∫ t in (0 : ℝ)..R, Real.sin (x * t) * Real.sin (a * t) =
      Real.sin (R * (a - x)) / (Real.pi * (a - x)) -
        Real.sin (R * (-a - x)) / (Real.pi * (-a - x)) := by
  have hd : ∀ t ∈ uIcc (0 : ℝ) R, HasDerivAt (fun t => Real.sin ((x - a) * t) / (2 * (x - a)) -
      Real.sin ((x + a) * t) / (2 * (x + a))) (Real.sin (x * t) * Real.sin (a * t)) t := by
    intro t _
    have e1 := ((hasDerivAt_id t).const_mul (x - a)).sin.div_const (2 * (x - a))
    have e2 := ((hasDerivAt_id t).const_mul (x + a)).sin.div_const (2 * (x + a))
    convert e1.sub e2 using 1
    · rfl
    simp only [id]
    rw [sub_mul, add_mul, Real.cos_sub, Real.cos_add]
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (by
    exact (by fun_prop : Continuous fun t => Real.sin (x * t) *
      Real.sin (a * t)).intervalIntegrable _ _)]
  have : Real.pi ≠ 0 := Real.pi_ne_zero
  have h3 : a - x ≠ 0 := fun h => h1 (by linarith)
  have h4 : -a - x ≠ 0 := fun h => h2 (by linarith)
  rw [show Real.sin (R * (a - x)) = -Real.sin ((x - a) * R) by rw [← Real.sin_neg]; ring_nf,
    show Real.sin (R * (-a - x)) = -Real.sin ((x + a) * R) by rw [← Real.sin_neg]; ring_nf]
  simp only [mul_zero, Real.sin_zero, zero_div, sub_zero]
  field_simp
  ring

/-- Integrability of a test function against the Dirichlet kernel. -/
private lemma integrable_mul_dirichlet {φ : ℝ → ℂ} (hi : Integrable φ) (R b : ℝ) :
    Integrable fun x => φ x * ((Real.sin (R * (b - x)) / (Real.pi * (b - x)) : ℝ) : ℂ) := by
  refine hi.mul_bdd (c := |R| / Real.pi) (by fun_prop : Measurable fun x : ℝ =>
    ((Real.sin (R * (b - x)) / (Real.pi * (b - x)) : ℝ) : ℂ)).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos Real.pi_pos]
  rcases eq_or_ne (b - x) 0 with h | h
  · rw [h]; simp only [abs_zero, mul_zero, div_zero]; positivity
  rw [div_le_div_iff₀ (by positivity) Real.pi_pos]
  have := Real.abs_sin_le_abs (x := R * (b - x))
  rw [abs_mul] at this
  nlinarith [Real.pi_pos, abs_nonneg (b - x), abs_nonneg R]

/-- DLMF 1.17.9 and 1.17.12: `δ(x - a) = (2π)⁻¹ ∫ e^{i(x-a)t} dt`, in the sense
`lim_{R→∞} ∫ ((2π)⁻¹ ∫_{-R}^{R} e^{i(x-a)t} dt) φ(x) dx = φ(a)` for test functions `φ`. -/
@[dlmf 1.17.E9, dlmf 1.17.E12]
theorem tendsto_fourier_kernel {φ : ℝ → ℂ} (hφ : IsTestFunctionOn univ φ) (a : ℝ) :
    Tendsto (fun R : ℝ => ∫ x : ℝ, ((1 / (2 * Real.pi) : ℂ) *
      ∫ t in -R..R, exp (I * (x - a) * t)) * φ x) atTop (𝓝 (φ a)) := by
  have hi : Integrable φ := hφ.1.continuous.integrable_of_hasCompactSupport hφ.2.1
  refine (Real.tendsto_integral_mul_sin_div_of_differentiableAt hi
    ((hφ.1.differentiable (by simp)) a)).congr fun R => ?_
  refine integral_congr_ae ?_
  filter_upwards [Measure.ae_ne volume a] with x hx
  have hxa : x - a ≠ 0 := sub_ne_zero.2 hx
  have h := intervalIntegral_cexp_mul_I_symm hxa R
  rw [show (fun t : ℝ => cexp (((x - a : ℝ) : ℂ) * I * t)) =
    fun t : ℝ => cexp (I * (x - a) * t) from funext fun t => by push_cast; ring_nf] at h
  rw [h]
  have : Real.pi ≠ 0 := Real.pi_ne_zero
  have h1 : (a : ℂ) - x ≠ 0 := by exact_mod_cast sub_ne_zero.2 (Ne.symm hx)
  have h2 : (x : ℂ) - a ≠ 0 := by exact_mod_cast hxa
  rw [show Real.sin (R * (a - x)) = -Real.sin (R * (x - a)) by
    rw [← Real.sin_neg]; ring_nf]
  push_cast
  field_simp
  ring

/-- DLMF 1.17.12_1: `δ(x - a) = (2/π) ∫_0^∞ cos(xt) cos(at) dt` for `x, a > 0`. -/
@[dlmf 1.17.E12_1]
theorem tendsto_cos_kernel {φ : ℝ → ℂ} (hφ : IsTestFunctionOn (Ioi 0) φ) {a : ℝ}
    (ha : 0 < a) :
    Tendsto (fun R : ℝ => ∫ x in Ioi (0 : ℝ), ((2 / Real.pi : ℝ) *
      ∫ t in (0 : ℝ)..R, Real.cos (x * t) * Real.cos (a * t) : ℝ) * φ x) atTop (𝓝 (φ a)) := by
  have hi : Integrable φ := hφ.1.continuous.integrable_of_hasCompactSupport hφ.2.1
  have hd : Differentiable ℝ φ := hφ.1.differentiable (by simp)
  have hφa : φ (-a) = 0 := image_eq_zero_of_notMem_tsupport fun h => by
    have := hφ.2.2 h; simp only [mem_Ioi] at this; linarith
  have h := (Real.tendsto_integral_mul_sin_div_of_differentiableAt hi (hd a)).add
    (Real.tendsto_integral_mul_sin_div_of_differentiableAt hi (hd (-a)))
  rw [hφa, add_zero] at h
  refine h.congr fun R => ?_
  rw [← integral_add (integrable_mul_dirichlet hi R a) (integrable_mul_dirichlet hi R (-a)),
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hφ.2.2 h)), mul_zero]]
  refine integral_congr_ae ?_
  filter_upwards [Measure.ae_ne volume a, Measure.ae_ne volume (-a)] with x hx1 hx2
  rw [two_div_pi_integral_cos_mul_cos (sub_ne_zero.2 hx1) (fun h => hx2 (by linarith)) R]
  push_cast
  ring

/-- DLMF 1.17.12_2: `δ(x - a) = (2/π) ∫_0^∞ sin(xt) sin(at) dt` for `x, a > 0`. -/
@[dlmf 1.17.E12_2]
theorem tendsto_sin_kernel {φ : ℝ → ℂ} (hφ : IsTestFunctionOn (Ioi 0) φ) {a : ℝ}
    (ha : 0 < a) :
    Tendsto (fun R : ℝ => ∫ x in Ioi (0 : ℝ), ((2 / Real.pi : ℝ) *
      ∫ t in (0 : ℝ)..R, Real.sin (x * t) * Real.sin (a * t) : ℝ) * φ x) atTop (𝓝 (φ a)) := by
  have hi : Integrable φ := hφ.1.continuous.integrable_of_hasCompactSupport hφ.2.1
  have hd : Differentiable ℝ φ := hφ.1.differentiable (by simp)
  have hφa : φ (-a) = 0 := image_eq_zero_of_notMem_tsupport fun h => by
    have := hφ.2.2 h; simp only [mem_Ioi] at this; linarith
  have h := (Real.tendsto_integral_mul_sin_div_of_differentiableAt hi (hd a)).sub
    (Real.tendsto_integral_mul_sin_div_of_differentiableAt hi (hd (-a)))
  rw [hφa, sub_zero] at h
  refine h.congr fun R => ?_
  rw [← integral_sub (integrable_mul_dirichlet hi R a) (integrable_mul_dirichlet hi R (-a)),
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hφ.2.2 h)), mul_zero]]
  refine integral_congr_ae ?_
  filter_upwards [Measure.ae_ne volume a, Measure.ae_ne volume (-a)] with x hx1 hx2
  rw [two_div_pi_integral_sin_mul_sin (sub_ne_zero.2 hx1) (fun h => hx2 (by linarith)) R]
  push_cast
  ring

/-- DLMF 1.17.13: `δ(x - a) = x ∫_0^∞ t J_ν(xt) J_ν(at) dt` for `ℜν > -1`, `x, a > 0`
(Hankel inversion), with Mathlib's `Complex.besselJ`. -/
@[dlmf 1.17.E13]
theorem tendsto_bessel_kernel {ν : ℂ} (hν : -1 < ν.re) {φ : ℝ → ℂ}
    (hφ : IsTestFunctionOn (Ioi 0) φ) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun R : ℝ => ∫ x in Ioi (0 : ℝ), ((x : ℂ) *
      ∫ t in (0 : ℝ)..R, (t : ℂ) * Complex.besselJ ν (x * t) * Complex.besselJ ν (a * t)) *
        φ x) atTop (𝓝 (φ a)) := by
  sorry

/-- DLMF 1.17.14: `δ(x - a) = (2xa/π) ∫_0^∞ t² 𝗃_ℓ(xt) 𝗃_ℓ(at) dt` for `x, a > 0`, with the
spherical Bessel function `sphericalJ` of `DLMF.Core.Basic`. -/
@[dlmf 1.17.E14]
theorem tendsto_sphericalBessel_kernel (ℓ : ℕ) {φ : ℝ → ℂ} (hφ : IsTestFunctionOn (Ioi 0) φ)
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun R : ℝ => ∫ x in Ioi (0 : ℝ), ((2 * x * a / Real.pi : ℝ) *
      ∫ t in (0 : ℝ)..R, (t : ℂ) ^ 2 * Bessel.sphericalJ ℓ (x * t) * Bessel.sphericalJ ℓ (a * t)) *
        φ x) atTop (𝓝 (φ a)) := by
  sorry

/-- DLMF 1.17.15: `δ(x - a) = ∫_0^∞ s(x, ℓ; r) s(a, ℓ; r) dr` for energies `x, a > 0`, with the
energy-normalized Coulomb function `coulombs` (DLMF 33.14.9). The normalization is that of
Seaton (2002a); not verified numerically during acquisition. -/
@[dlmf 1.17.E15]
theorem tendsto_coulomb_kernel (ℓ : ℕ) {φ : ℝ → ℂ} (hφ : IsTestFunctionOn (Ioi 0) φ)
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun R : ℝ => ∫ x in Ioi (0 : ℝ), (∫ r in (0 : ℝ)..R,
      DLMF.Coulomb.coulombs x ℓ r * DLMF.Coulomb.coulombs a ℓ r) * φ x) atTop
      (𝓝 (φ a)) := by
  sorry

/-- DLMF 1.17.16: `δ(x - a) = ∫_{-∞}^{∞} Ai(t - x) Ai(t - a) dt`. The integral converges only
conditionally at `-∞`; it is taken as `lim_{R→∞} ∫_{-R}^{R}`. -/
@[dlmf 1.17.E16]
theorem tendsto_airy_kernel {φ : ℝ → ℂ} (hφ : IsTestFunctionOn univ φ) (a : ℝ) :
    Tendsto (fun R : ℝ => ∫ x : ℝ, (∫ t in -R..R,
      DLMF.Airy.airyAi (t - x) * DLMF.Airy.airyAi (t - a)) * φ x) atTop (𝓝 (φ a)) := by
  sorry

/-! ## §1.17(iii): series representations -/

/-- DLMF 1.17.17 (Fourier series at a point): for `φ` smooth and `2π`-periodic,
`(2π)⁻¹ Σ_k e^{-ika} ∫_{-π}^{π} φ(x) e^{ikx} dx = φ(a)`, as the limit of the symmetric partial
sums. -/
@[dlmf 1.17.E17]
theorem tendsto_fourier_series {φ : ℝ → ℂ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hper : Function.Periodic φ (2 * Real.pi)) (a : ℝ) :
    Tendsto (fun n : ℕ => (1 / (2 * Real.pi) : ℂ) * ∑ k ∈ Finset.Icc (-(n : ℤ)) n,
      exp (-(I * k * a)) * ∫ x in -Real.pi..Real.pi, φ x * exp (I * k * x)) atTop
      (𝓝 (φ a)) := by
  sorry

/-- DLMF 1.17.20 (closed form): `(2π)⁻¹ Σ_{k=-n}^{n} e^{ikθ} = sin((n+½)θ) / (2π sin(θ/2))`
when `sin(θ/2) ≠ 0`. -/
@[dlmf 1.17.E20]
theorem dirichletKernel_eq {θ : ℝ} (hθ : Real.sin (θ / 2) ≠ 0) (n : ℕ) :
    dirichletKernel n θ =
      ((Real.sin ((n + 1 / 2) * θ) / (2 * Real.pi * Real.sin (θ / 2)) : ℝ) : ℂ) := by
  have hsum (n : ℕ) :
      (Real.sin (θ / 2) : ℂ) *
          (∑ k ∈ Finset.Icc (-(n : ℤ)) n, exp (I * k * θ)) =
        (Real.sin ((n + 1 / 2) * θ) : ℂ) := by
    induction n with
    | zero => simp; congr 1; ring
    | succ n ih =>
      rw [Nat.cast_succ, Finset.sum_Icc_succ_eq_add_endpoints]
      have he : exp (I * ((n : ℤ) + 1) * θ) + exp (I * (-((n : ℤ) + 1)) * θ) =
          (2 * Real.cos (((n : ℝ) + 1) * θ) : ℝ) := by
        have h₁ : I * (((n : ℤ) + 1) : ℂ) * θ = (((n : ℝ) + 1) * θ : ℝ) * I := by
          push_cast; ring
        have h₂ : I * ((-((n : ℤ) + 1)) : ℂ) * θ = -((((n : ℝ) + 1) * θ : ℝ) : ℂ) * I := by
          push_cast; ring
        rw [h₁, h₂, exp_mul_I, exp_mul_I, cos_neg, sin_neg]
        simp only [← ofReal_cos, ← ofReal_sin]
        push_cast
        ring
      simp only [Int.cast_add, Int.cast_one, Int.cast_neg, Int.cast_natCast, Nat.cast_add,
        Nat.cast_one] at he ⊢
      rw [he, mul_add, ih]
      have hs := Real.sin_sub_sin (((n : ℝ) + 1 + 1 / 2) * θ)
        (((n : ℝ) + 1 / 2) * θ)
      rw [show ((((n : ℝ) + 1 + 1 / 2) * θ - ((n : ℝ) + 1 / 2) * θ) / 2) = θ / 2 by ring,
        show ((((n : ℝ) + 1 + 1 / 2) * θ + ((n : ℝ) + 1 / 2) * θ) / 2) =
          ((n : ℝ) + 1) * θ by ring] at hs
      exact_mod_cast (by linarith : Real.sin (θ / 2) *
        (2 * Real.cos (((n : ℝ) + 1) * θ)) + Real.sin (((n : ℝ) + 1 / 2) * θ) =
          Real.sin (((n : ℝ) + 1 + 1 / 2) * θ))
  have hθ' : (Real.sin (θ / 2) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hθ
  have hsum' : (∑ k ∈ Finset.Icc (-(n : ℤ)) n, exp (I * k * θ)) =
      (Real.sin ((n + 1 / 2) * θ) : ℂ) / Real.sin (θ / 2) :=
    (eq_div_iff hθ').mpr (by simpa only [mul_comm] using hsum n)
  rw [dirichletKernel, hsum']
  push_cast
  ring

/-- DLMF 1.17.18–1.17.21: `lim_{n→∞} ∫_{-π}^{π} δₙ(x - a) φ(x) dx = φ(a)` with the Dirichlet
kernel `δₙ` (1.17.20), the meaning of the formal `2π`-periodic series
`δ(x - a) = (2π)⁻¹ Σ_k e^{ik(x-a)}` (1.17.21).

DLMF asks only that `φ` be continuous and `2π`-periodic; that is not sufficient (by du
Bois-Reymond there are continuous periodic functions whose Fourier series diverge at a point,
and the integral here is the `n`-th symmetric partial sum of the Fourier series of `φ` at `a`).
The statement is made for continuously differentiable `φ` (any Dini-type condition of
§1.8(ii) would do). -/
@[dlmf 1.17.E18, dlmf 1.17.E19, dlmf 1.17.E21]
theorem tendsto_dirichletKernel_integral {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    (hper : Function.Periodic φ (2 * Real.pi)) (a : ℝ) :
    Tendsto (fun n : ℕ => ∫ x in -Real.pi..Real.pi, dirichletKernel n (x - a) * φ x) atTop
      (𝓝 (φ a)) := by
  sorry

/-- DLMF 1.17.22: `δ(x - a) = Σ_k (k + ½) P_k(x) P_k(a)` on `(-1, 1)` (Legendre polynomials
`legendrePolyP`), as the limit of the partial sums tested against test functions. -/
@[dlmf 1.17.E22]
theorem tendsto_legendre_kernel {φ : ℝ → ℂ} (hφ : IsTestFunctionOn (Ioo (-1) 1) φ) {a : ℝ}
    (ha : a ∈ Ioo (-1 : ℝ) 1) :
    Tendsto (fun N : ℕ => ∫ x in Ioo (-1 : ℝ) 1, (∑ k ∈ Finset.range N,
      ((k : ℂ) + 1 / 2) * DLMF.OrthogonalPolynomials.legendrePolyP k x *
        DLMF.OrthogonalPolynomials.legendrePolyP k a) * φ x) atTop (𝓝 (φ a)) := by
  sorry

/-- DLMF 1.17.23: `δ(x - a) = e^{-(x+a)/2} Σ_k L_k(x) L_k(a)` on `(0, ∞)` (Laguerre polynomials
`laguerrePolyL 0`). -/
@[dlmf 1.17.E23]
theorem tendsto_laguerre_kernel {φ : ℝ → ℂ} (hφ : IsTestFunctionOn (Ioi 0) φ) {a : ℝ}
    (ha : 0 < a) :
    Tendsto (fun N : ℕ => ∫ x in Ioi (0 : ℝ), ((Real.exp (-(x + a) / 2) : ℂ) *
      ∑ k ∈ Finset.range N, DLMF.OrthogonalPolynomials.laguerrePolyL 0 k x *
        DLMF.OrthogonalPolynomials.laguerrePolyL 0 k a) * φ x) atTop (𝓝 (φ a)) := by
  sorry

/-- DLMF 1.17.24: `δ(x - a) = π^{-1/2} e^{-(x²+a²)/2} Σ_k H_k(x) H_k(a) / (2^k k!)` on `ℝ`
(physicists' Hermite polynomials `hermitePolyH`). -/
@[dlmf 1.17.E24]
theorem tendsto_hermite_kernel {φ : ℝ → ℂ} (hφ : IsTestFunctionOn univ φ) (a : ℝ) :
    Tendsto (fun N : ℕ => ∫ x : ℝ, ((Real.exp (-(x ^ 2 + a ^ 2) / 2) / Real.sqrt Real.pi : ℝ) *
      ∑ k ∈ Finset.range N,
        (((DLMF.OrthogonalPolynomials.hermitePolyH k).map (Int.castRingHom ℝ)).eval x *
          ((DLMF.OrthogonalPolynomials.hermitePolyH k).map (Int.castRingHom ℝ)).eval a /
            (2 ^ k * k.factorial) : ℝ) : ℂ) * φ x) atTop (𝓝 (φ a)) := by
  sorry

/-- DLMF 1.17.25: `δ(cos θ₁ - cos θ₂) δ(φ₁ - φ₂) = Σ_ℓ Σ_{m=-ℓ}^{ℓ} Y_{ℓ,m}(θ₁, φ₁)
conj(Y_{ℓ,m}(θ₂, φ₂))`, tested against smooth functions `f(θ, φ)` on the sphere (`2π`-periodic
in `φ`, smooth as functions of the point of the sphere) with the surface measure
`sin θ dθ dφ`, at a point with `0 < θ₂ < π`. -/
@[dlmf 1.17.E25]
theorem tendsto_sphericalHarmonic_kernel {f : ℝ × ℝ → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) fun p : EuclideanSpace ℝ (Fin 3) =>
      f (Real.arccos (p 2 / ‖p‖), Complex.arg (p 0 + p 1 * I)))
    (hper : ∀ θ φ, f (θ, φ + 2 * Real.pi) = f (θ, φ)) {θ₂ φ₂ : ℝ}
    (hθ₂ : θ₂ ∈ Ioo 0 Real.pi) (hφ₂ : φ₂ ∈ Ioo (-Real.pi) Real.pi) :
    Tendsto (fun L : ℕ => ∫ θ₁ in (0 : ℝ)..Real.pi, ∫ φ₁ in -Real.pi..Real.pi,
      (∑ ℓ ∈ Finset.range L, ∑ m ∈ Finset.Icc (-(ℓ : ℤ)) ℓ,
        DLMF.Legendre.sphericalHarmonic ℓ m θ₁ φ₁ *
          starRingEnd ℂ (DLMF.Legendre.sphericalHarmonic ℓ m θ₂ φ₂)) *
        f (θ₁, φ₁) * Real.sin θ₁) atTop (𝓝 (f (θ₂, φ₂))) := by
  sorry

end DLMF.AlgebraicAnalytic
