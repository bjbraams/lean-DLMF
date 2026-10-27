/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AlgebraicAnalytic.Distributions.Defs
public import Mathlib.MeasureTheory.Integral.PeakFunction
public import DLMF.Airy.Basic
public import DLMF.Coulomb.Energy.Defs
public import DLMF.Legendre.Harmonics

/-!
# Integral and series representations of the Dirac delta (DLMF §1.17)

DLMF writes the Dirac delta as a symbolic function `δ(x)` (1.17.1–1.17.2). Following the
rigorous reading of DLMF §1.17(i) and §1.17(iv), every representation here is stated as a
weak limit against test functions: a family `δ_R(x, a)` represents `δ(x - a)` when
`lim ∫ δ_R(x, a) φ(x) dx = φ(a)` for every smooth compactly supported `φ` (on the stated
interval), or for the class of functions DLMF names. Nothing is stated pointwise.

* 1.17.1–1.17.2: `delta_apply_eq_zero_of_notMem_tsupport`; Mathlib's `Distribution.delta`.
* 1.17.3–1.17.7: `IsDeltaSequence`, the Gaussian sequence (`tendsto_gaussian_integral`,
  proved for integrable `φ` continuous at `a`; DLMF's growth condition and the one-sided
  version 1.17.7 are admitted).
* 1.17.8–1.17.12: Fourier inversion and `δ(x-a) = (2π)⁻¹ ∫ e^{i(x-a)t} dt`; the Gaussian
  regularization 1.17.10 is proved (`gaussian_fourier_eq`), hence 1.17.11.
* 1.17.12_1–1.17.16: cosine, sine, Bessel, spherical Bessel, Coulomb and Airy kernels.
* 1.17.17–1.17.21: Fourier series and the Dirichlet kernel (closed form 1.17.20 proved).
* 1.17.22–1.17.25: Legendre, Laguerre, Hermite and spherical-harmonic expansions.
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

lemma g1f_integral_gauss : ∫ x, normalizedGaussian x = 1 := by
  have h := integral_gaussian 1
  simp only [neg_mul, one_mul, div_one] at h
  simp only [normalizedGaussian, integral_div, h]
  exact div_self (by positivity)

lemma g1f_tendsto_gauss :
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
    (fun x => by unfold normalizedGaussian; positivity) g1f_integral_gauss g1f_tendsto_gauss hφ ha
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

/-- DLMF 1.17.6 under DLMF's hypotheses: `φ` continuous at `a`, locally integrable, and
`∫ e^{-n(x-a)²} φ(x) dx` absolutely convergent for some (hence all larger) `n`; this covers
`φ(x) = O(e^{αx²})`. -/
@[dlmf 1.17.E6]
theorem tendsto_gaussian_integral_of_growth {φ : ℝ → ℂ} {a : ℝ} (n₀ : ℕ)
    (hφ : Integrable fun x => (Real.exp (-(n₀ * (x - a) ^ 2)) : ℂ) * φ x)
    (hloc : LocallyIntegrable φ) (ha : ContinuousAt φ a) :
    Tendsto (fun n : ℕ => ∫ x, gaussianDeltaSeq n (x - a) * φ x) atTop (𝓝 (φ a)) := by
  sorry

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
  sorry

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

/-- DLMF 1.17.9 and 1.17.12: `δ(x - a) = (2π)⁻¹ ∫ e^{i(x-a)t} dt`, in the sense
`lim_{R→∞} ∫ ((2π)⁻¹ ∫_{-R}^{R} e^{i(x-a)t} dt) φ(x) dx = φ(a)` for test functions `φ`. -/
@[dlmf 1.17.E9, dlmf 1.17.E12]
theorem tendsto_fourier_kernel {φ : ℝ → ℂ} (hφ : IsTestFunctionOn univ φ) (a : ℝ) :
    Tendsto (fun R : ℝ => ∫ x : ℝ, ((1 / (2 * Real.pi) : ℂ) *
      ∫ t in -R..R, exp (I * (x - a) * t)) * φ x) atTop (𝓝 (φ a)) := by
  sorry

/-- DLMF 1.17.12_1: `δ(x - a) = (2/π) ∫_0^∞ cos(xt) cos(at) dt` for `x, a > 0`. -/
@[dlmf 1.17.E12_1]
theorem tendsto_cos_kernel {φ : ℝ → ℂ} (hφ : IsTestFunctionOn (Ioi 0) φ) {a : ℝ}
    (ha : 0 < a) :
    Tendsto (fun R : ℝ => ∫ x in Ioi (0 : ℝ), ((2 / Real.pi : ℝ) *
      ∫ t in (0 : ℝ)..R, Real.cos (x * t) * Real.cos (a * t) : ℝ) * φ x) atTop (𝓝 (φ a)) := by
  sorry

/-- DLMF 1.17.12_2: `δ(x - a) = (2/π) ∫_0^∞ sin(xt) sin(at) dt` for `x, a > 0`. -/
@[dlmf 1.17.E12_2]
theorem tendsto_sin_kernel {φ : ℝ → ℂ} (hφ : IsTestFunctionOn (Ioi 0) φ) {a : ℝ}
    (ha : 0 < a) :
    Tendsto (fun R : ℝ => ∫ x in Ioi (0 : ℝ), ((2 / Real.pi : ℝ) *
      ∫ t in (0 : ℝ)..R, Real.sin (x * t) * Real.sin (a * t) : ℝ) * φ x) atTop (𝓝 (φ a)) := by
  sorry

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
spherical Bessel function `sphericalJ` of `DLMF.Core.Framework`. -/
@[dlmf 1.17.E14]
theorem tendsto_sphericalBessel_kernel (ℓ : ℕ) {φ : ℝ → ℂ} (hφ : IsTestFunctionOn (Ioi 0) φ)
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun R : ℝ => ∫ x in Ioi (0 : ℝ), ((2 * x * a / Real.pi : ℝ) *
      ∫ t in (0 : ℝ)..R, (t : ℂ) ^ 2 * sphericalJ ℓ (x * t) * sphericalJ ℓ (a * t)) *
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
  sorry

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
