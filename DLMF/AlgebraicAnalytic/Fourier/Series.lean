/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AlgebraicAnalytic.Fourier.Basic
public import DLMFMathlib.Analysis.Fourier.AddCircle
public import DLMFMathlib.Analysis.Fourier.DirichletKernel
public import DLMFMathlib.Analysis.Fourier.GaussianSeries
public import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import TauCeti.Analysis.Calculus.PeriodicDeriv

/-!
# Fourier series (DLMF §1.8)

Statements of DLMF §1.8 for `f : ℝ → ℂ`, with the coefficients `fourierCosCoeff`,
`fourierSinCoeff`, `fourierExpCoeff` and the Lebesgue constants `lebesgueConstant` of
`DLMF.AlgebraicAnalytic.Fourier.Basic`.

## Main results

* `fourierExpCoeff_eq_fourierCoeffOn`: `c_n` is Mathlib's `fourierCoeffOn` on `[-π, π]`
  (DLMF 1.8.4).
* `fourierExpCoeff_natCast`, `fourierExpCoeff_neg_natCast`, `fourierExpCoeff_zero`:
  `c_n = (a_n - i b_n)/2`, `c_{-n} = (a_n + i b_n)/2`, `c_0 = a_0/2`.
* `fourierSinCoeff_eq_zero_of_even`, `fourierCosCoeff_eq_zero_of_odd`: even and odd functions.
* `hasSum_fourierSeries`, `hasSum_fourierExpSeries`: the Fourier series (DLMF 1.8.1, 1.8.3).
* `hasSum_norm_sq_fourierCosSinCoeff`, `hasSum_norm_sq_fourierExpCoeff`,
  `hasSum_fourierCosSinCoeff_mul_conj`, `hasSum_fourierExpCoeff_mul_conj`: Parseval's formulas
  (DLMF 1.8.5–1.8.6_2).
* `fourierCoeff_isLittleO`: decay of the coefficients of smooth functions (DLMF 1.8.7).
* `eq_of_fourierCoeff_eq`: uniqueness of Fourier series.
* `lebesgueConstant_isEquivalent`: `L_n ∼ (4/π²) ln n` (DLMF 1.8.9).
* `tendsto_intervalIntegral_mul_exp_atTop`, `tendsto_integral_mul_exp_atTop`: the
  Riemann–Lebesgue lemma (DLMF 1.8.10) and its extension to integrable functions on `ℝ`.
* `tendsto_fourierPartialSum_of_oneSidedDeriv`: pointwise convergence (DLMF 1.8.11); the primed
  form drops the piecewise-continuity hypothesis, and
  `tendsto_integral_mul_cosineKernel_of_oneSidedDeriv` is the Dirichlet-kernel form.
* `tendsto_integral_fourierSeries`, `tendsto_deriv_fourierSeries`: termwise integration and
  differentiation (DLMF 1.8.12, §1.8(iii)).
* `poisson_summation`, `poissonSummation_cos`: Poisson's summation formula (DLMF 1.8.14,
  1.8.15).
* `hasSum_exp_neg_sq_mul`: DLMF 1.8.16.

## Implementation notes

* DLMF series over `n = 1, 2, …` that may converge only conditionally (the Fourier series in
  1.8.1, 1.8.11, 1.8.12, the differentiated series of §1.8(iii) and 1.8.15) are stated as limits
  of partial sums (`Filter.Tendsto` of `∑ n ∈ Finset.range N`), not with `HasSum`, which over
  `ℂ` means absolute convergence. Series that converge absolutely under the stated hypotheses
  (Parseval 1.8.5–1.8.6_2, the exponential series 1.8.3 with summable coefficients, Poisson's
  formula 1.8.14, 1.8.16) use `HasSum`; doubly infinite series are indexed by `ℤ`.
* Periodicity is `Function.Periodic f (2 * π)`.
* Several DLMF hypotheses are formalized in a stronger-than-DLMF (more general) or special-case
  form; each docstring says which.
* The Gaussian Poisson identity 1.8.16 uses Mathlib's `Complex.tsum_exp_neg_quadratic`,
  retaining complex shifts and principal powers.
-/

@[expose] public noncomputable section

open Real Complex Filter MeasureTheory Set Asymptotics
open scoped Topology FourierTransform

namespace DLMF.AlgebraicAnalytic

/-! ## §1.8(i) Definitions and elementary properties -/

/-- DLMF 1.8.4: the exponential Fourier coefficient `c_n` is Mathlib's `fourierCoeffOn` for
the interval `[-π, π]` (period `2π`). -/
@[dlmf 1.8.E4]
theorem fourierExpCoeff_eq_fourierCoeffOn (f : ℝ → ℂ) (n : ℤ) :
    fourierExpCoeff f n = fourierCoeffOn (by linarith [pi_pos] : -π < π) f n := by
  rw [fourierCoeffOn_eq_integral, fourierExpCoeff, Complex.real_smul]
  have h2 : π - -π = 2 * π := by ring
  congr 1
  · rw [h2]; push_cast; ring
  · refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [smul_eq_mul]
    rw [fourier_coe_apply, h2, mul_comm]
    congr 1
    push_cast
    field_simp [pi_ne_zero]

/-- Identity under the stated parameter and domain assumptions: `Complex.exp (-(Complex.I * n *
x)) = (Real.cos (n * x) : ℂ) - Complex.I * (Real.sin (n * x) : ℂ)`. -/
private lemma cexp_neg_I_mul_eq_cos_sub_sin (n : ℤ) (x : ℝ) :
    Complex.exp (-(Complex.I * n * x)) =
      (Real.cos (n * x) : ℂ) - Complex.I * (Real.sin (n * x) : ℂ) := by
  rw [show -(Complex.I * n * x) = ((-(n * x) : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_mul_I]
  push_cast
  rw [Complex.cos_neg, Complex.sin_neg]
  ring

/-- Identity under the stated parameter and domain assumptions: `∫ x in (-π)..π, f x * Complex.exp
(-(Complex.I * n * x)) = (∫ x in (-π)..π, f x * (Real.cos (n * x) : ℂ)) - Complex.I * ∫ x in
(-π)..π, f x * (Real.sin (n * x) : ℂ)`. -/
private lemma integral_mul_cexp_neg_eq_cos_sub_sin {f : ℝ → ℂ}
    (hf : IntervalIntegrable f volume (-π) π)
    (n : ℤ) :
    ∫ x in (-π)..π, f x * Complex.exp (-(Complex.I * n * x)) =
      (∫ x in (-π)..π, f x * (Real.cos (n * x) : ℂ)) -
        Complex.I * ∫ x in (-π)..π, f x * (Real.sin (n * x) : ℂ) := by
  have hc : IntervalIntegrable (fun x => f x * (Real.cos (n * x) : ℂ)) volume (-π) π :=
    hf.mul_continuousOn (by fun_prop)
  have hs : IntervalIntegrable (fun x => f x * (Real.sin (n * x) : ℂ)) volume (-π) π :=
    hf.mul_continuousOn (by fun_prop)
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub hc
    (hs.const_mul _)]
  refine intervalIntegral.integral_congr fun x _ => ?_
  rw [cexp_neg_I_mul_eq_cos_sub_sin]
  ring

/-- DLMF §1.8(i) (after 1.8.4): `c_n = ½(a_n - i b_n)` for `n > 0` (in fact for all `n ≥ 0`),
for `f` integrable on `[-π, π]`. -/
@[dlmf 1.8.i]
theorem fourierExpCoeff_natCast {f : ℝ → ℂ} (hf : IntervalIntegrable f volume (-π) π)
    (n : ℕ) :
    fourierExpCoeff f n = (fourierCosCoeff f n - Complex.I * fourierSinCoeff f n) / 2 := by
  rw [fourierExpCoeff, integral_mul_cexp_neg_eq_cos_sub_sin hf, fourierCosCoeff, fourierSinCoeff]
  push_cast
  field_simp

/-- DLMF §1.8(i) (after 1.8.4): `c_{-n} = ½(a_n + i b_n)`, for `f` integrable on `[-π, π]`. -/
@[dlmf 1.8.i]
theorem fourierExpCoeff_neg_natCast {f : ℝ → ℂ} (hf : IntervalIntegrable f volume (-π) π)
    (n : ℕ) :
    fourierExpCoeff f (-(n : ℤ)) =
      (fourierCosCoeff f n + Complex.I * fourierSinCoeff f n) / 2 := by
  rw [fourierExpCoeff, integral_mul_cexp_neg_eq_cos_sub_sin hf, fourierCosCoeff, fourierSinCoeff]
  have hc : ∀ x : ℝ, Real.cos (((-(n : ℤ) : ℤ) : ℝ) * x) = Real.cos (n * x) := fun x => by
    push_cast; rw [neg_mul, Real.cos_neg]
  have hs : ∀ x : ℝ, Real.sin (((-(n : ℤ) : ℤ) : ℝ) * x) = -Real.sin (n * x) := fun x => by
    push_cast; rw [neg_mul, Real.sin_neg]
  simp only [hc, hs, Complex.ofReal_neg, mul_neg, intervalIntegral.integral_neg]
  field_simp
  ring

/-- DLMF §1.8(i) (after 1.8.4): `c_0 = ½ a_0`. -/
@[dlmf 1.8.i]
theorem fourierExpCoeff_zero {f : ℝ → ℂ} (hf : IntervalIntegrable f volume (-π) π) :
    fourierExpCoeff f 0 = fourierCosCoeff f 0 / 2 := by
  have h := fourierExpCoeff_natCast hf 0
  simp only [Nat.cast_zero] at h
  rw [h, fourierSinCoeff]
  simp

/-- Identity under the stated parameter and domain assumptions: `∫ x in (-π)..π, g x = 0`. -/
private lemma integral_neg_pi_pi_eq_zero_of_odd {g : ℝ → ℂ} (hg : ∀ x, g (-x) = -g x) :
    ∫ x in (-π)..π, g x = 0 := by
  have h := intervalIntegral.integral_comp_neg (a := -π) (b := π) g
  rw [neg_neg] at h
  simp only [hg, intervalIntegral.integral_neg] at h
  have : (2 : ℂ) * ∫ x in (-π)..π, g x = 0 := by linear_combination -h
  simpa using this

/-- DLMF §1.8(i): if `f(-x) = f(x)`, then `b_n = 0` for all `n`. No integrability is needed
(for a non-integrable `f` the coefficient is `0` by totalization). -/
@[dlmf 1.8.i]
theorem fourierSinCoeff_eq_zero_of_even {f : ℝ → ℂ} (hf : ∀ x, f (-x) = f x) (n : ℕ) :
    fourierSinCoeff f n = 0 := by
  rw [fourierSinCoeff, integral_neg_pi_pi_eq_zero_of_odd, mul_zero]
  intro x
  rw [hf, mul_neg, Real.sin_neg]
  push_cast
  ring

/-- DLMF §1.8(i): if `f(-x) = -f(x)`, then `a_n = 0` for all `n`. -/
@[dlmf 1.8.i]
theorem fourierCosCoeff_eq_zero_of_odd {f : ℝ → ℂ} (hf : ∀ x, f (-x) = -f x) (n : ℕ) :
    fourierCosCoeff f n = 0 := by
  rw [fourierCosCoeff, integral_neg_pi_pi_eq_zero_of_odd, mul_zero]
  intro x
  rw [hf, mul_neg, Real.cos_neg]
  ring

/-- The Fourier coefficients of the periodic lift to the circle agree with the
DLMF exponential coefficients on `[-π, π]`. -/
theorem fourierCoeff_lift_eq_fourierExpCoeff {f : ℝ → ℂ}
    (hper : Function.Periodic f (2 * π)) (n : ℤ) :
    letI : Fact (0 < 2 * π) := ⟨by positivity⟩
    fourierCoeff hper.lift n = fourierExpCoeff f n := by
  have : Fact (0 < 2 * π) := ⟨by positivity⟩
  rw [fourierCoeff_eq_intervalIntegral _ n (-π), fourierExpCoeff,
    show -π + 2 * π = π by ring, Complex.real_smul]
  congr 1
  · push_cast; ring
  · refine intervalIntegral.integral_congr fun y _ => ?_
    simp only [Function.Periodic.lift_coe, fourier_coe_apply,
      smul_eq_mul]
    rw [mul_comm]
    congr 2
    push_cast
    field_simp [pi_ne_zero]

/-- DLMF 1.8.3: the exponential Fourier series `f(x) = ∑_{n ∈ ℤ} c_n e^{inx}` of a continuous
`2π`-periodic `f` with summable coefficients `c_n` (1.8.4). This is Mathlib's
`has_pointwise_sum_fourier_series_of_summable` transported from `AddCircle (2π)` to `ℝ`. -/
@[dlmf 1.8.E3]
theorem hasSum_fourierExpSeries {f : ℝ → ℂ} (hf : Continuous f)
    (hper : Function.Periodic f (2 * π)) (hs : Summable (fourierExpCoeff f)) (x : ℝ) :
    HasSum (fun n : ℤ => fourierExpCoeff f n * Complex.exp (Complex.I * n * x)) (f x) := by
  have hT : Fact (0 < 2 * π) := ⟨by positivity⟩
  let F : C(AddCircle (2 * π), ℂ) := ⟨hper.lift, continuous_coinduced_dom.mpr hf⟩
  have hc : ∀ n, fourierCoeff F n = fourierExpCoeff f n :=
    fourierCoeff_lift_eq_fourierExpCoeff hper
  have hs' : Summable (fourierCoeff F) := by
    rw [show fourierCoeff F = fourierExpCoeff f from funext hc]; exact hs
  have h := has_pointwise_sum_fourier_series_of_summable hs' (x : AddCircle (2 * π))
  simp only [F, ContinuousMap.coe_mk, Function.Periodic.lift_coe, fourier_coe_apply,
    smul_eq_mul] at h
  convert h using 3 with n
  · exact (hc n).symm
  · congr 1
    push_cast
    field_simp [pi_ne_zero]

/-- DLMF 1.8.1: the trigonometric Fourier series of a continuous `2π`-periodic `f` whose
exponential coefficients are summable converges (absolutely) to `f(x)`:
`f(x) - ½a_0 = ∑_{n ≥ 1} (a_n cos nx + b_n sin nx)`. DLMF states 1.8.1 formally; the
summability hypothesis makes it a theorem (for convergence under weaker hypotheses see 1.8.11,
`tendsto_fourierPartialSum_of_oneSidedDeriv`). Derived from 1.8.3. -/
@[dlmf 1.8.E1]
theorem hasSum_fourierSeries {f : ℝ → ℂ} (hf : Continuous f) (hper : Function.Periodic f (2 * π))
    (hs : Summable (fourierExpCoeff f)) (x : ℝ) :
    HasSum (fun n : ℕ => fourierCosCoeff f (n + 1) * (Real.cos ((n + 1 : ℕ) * x) : ℂ) +
        fourierSinCoeff f (n + 1) * (Real.sin ((n + 1 : ℕ) * x) : ℂ))
      (f x - fourierCosCoeff f 0 / 2) := by
  have hi : IntervalIntegrable f volume (-π) π := hf.intervalIntegrable _ _
  have h := (hasSum_fourierExpSeries hf hper hs x).nat_add_neg
  have h1 := (hasSum_nat_add_iff' 1).mpr h
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, neg_zero,
    Int.cast_zero, mul_zero, zero_mul, Complex.exp_zero, mul_one] at h1
  rw [fourierExpCoeff_zero hi] at h1
  convert h1 using 1
  · funext n
    rw [fourierExpCoeff_natCast hi, fourierExpCoeff_neg_natCast hi]
    have e1 : Complex.exp (Complex.I * ((n + 1 : ℕ) : ℤ) * x) =
        (Real.cos ((n + 1 : ℕ) * x) : ℂ) + Complex.I * (Real.sin ((n + 1 : ℕ) * x) : ℂ) := by
      rw [show Complex.I * ((n + 1 : ℕ) : ℤ) * x = (((n + 1 : ℕ) * x : ℝ) : ℂ) * Complex.I by
        push_cast; ring, Complex.exp_mul_I]
      push_cast; ring
    have e2 : Complex.exp (Complex.I * ((-((n + 1 : ℕ) : ℤ) : ℤ) : ℂ) * x) =
        (Real.cos ((n + 1 : ℕ) * x) : ℂ) - Complex.I * (Real.sin ((n + 1 : ℕ) * x) : ℂ) := by
      rw [show Complex.I * ((-((n + 1 : ℕ) : ℤ) : ℤ) : ℂ) * x =
        ((-((n + 1 : ℕ) * x) : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.exp_mul_I]
      push_cast; rw [Complex.cos_neg, Complex.sin_neg]; ring
    push_cast at e1 e2 ⊢
    rw [e1, e2]
    ring_nf
    rw [Complex.I_sq]
    ring
  · ring

/-- DLMF 1.8.6 (Parseval's formula, exponential form): for `f` square integrable on
`[-π, π]`, `(2π)⁻¹ ∫_{-π}^{π} |f(x)|² dx = ∑_{n ∈ ℤ} |c_n|²`. From Mathlib's
`hasSum_sq_fourierCoeffOn`. -/
@[dlmf 1.8.E6]
theorem hasSum_norm_sq_fourierExpCoeff {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioc (-π) π))) :
    HasSum (fun n : ℤ => ‖fourierExpCoeff f n‖ ^ 2)
      ((2 * π)⁻¹ * ∫ x in (-π)..π, ‖f x‖ ^ 2) := by
  have h := hasSum_sq_fourierCoeffOn (by linarith [pi_pos] : -π < π) hf
  simp only [← fourierExpCoeff_eq_fourierCoeffOn, smul_eq_mul] at h
  convert h using 2
  ring

/-- Integrability between the indicated endpoints: `IntervalIntegrable f volume (-π) π`. -/
private lemma intervalIntegrable_neg_pi_pi_of_memLp {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioc (-π) π))) : IntervalIntegrable f volume (-π) π := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith [pi_pos])]
  have : IsFiniteMeasure (volume.restrict (Ioc (-π) π)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ, Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  exact hf.integrable (by norm_num)

/-- DLMF 1.8.5 (Parseval's formula, trigonometric form): for `f` square integrable on
`[-π, π]`, `π⁻¹ ∫_{-π}^{π} |f(x)|² dx = ½|a_0|² + ∑_{n ≥ 1} (|a_n|² + |b_n|²)`. Derived from
1.8.6 via the relations between `a_n`, `b_n` and `c_{±n}`. -/
@[dlmf 1.8.E5]
theorem hasSum_norm_sq_fourierCosSinCoeff {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioc (-π) π))) :
    HasSum (fun n : ℕ => ‖fourierCosCoeff f (n + 1)‖ ^ 2 + ‖fourierSinCoeff f (n + 1)‖ ^ 2)
      (π⁻¹ * (∫ x in (-π)..π, ‖f x‖ ^ 2) - ‖fourierCosCoeff f 0‖ ^ 2 / 2) := by
  have hi := intervalIntegrable_neg_pi_pi_of_memLp hf
  have h := (hasSum_norm_sq_fourierExpCoeff hf).nat_add_neg
  have h1 := (hasSum_nat_add_iff' 1).mpr h
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, neg_zero] at h1
  have key : ∀ n : ℕ, ‖fourierCosCoeff f n‖ ^ 2 + ‖fourierSinCoeff f n‖ ^ 2 =
      2 * (‖fourierExpCoeff f n‖ ^ 2 + ‖fourierExpCoeff f (-(n : ℤ))‖ ^ 2) := by
    intro n
    rw [fourierExpCoeff_natCast hi, fourierExpCoeff_neg_natCast hi, norm_div, norm_div]
    have hp := parallelogram_law_with_norm ℝ (fourierCosCoeff f n)
      (Complex.I * fourierSinCoeff f n)
    rw [norm_mul, Complex.norm_I, one_mul] at hp
    simp only [Complex.norm_ofNat]
    nlinarith [hp]
  have h0 : fourierExpCoeff f 0 = fourierCosCoeff f 0 / 2 := fourierExpCoeff_zero hi
  have h2 := h1.mul_left 2
  convert h2 using 1
  · funext n
    rw [key]
  · rw [h0, norm_div]
    simp only [Complex.norm_ofNat]
    field_simp
    ring

/-- DLMF 1.8.6_2 (Parseval's formula for two functions, exponential form): for `f`, `g`
square integrable on `[-π, π]`, `(2π)⁻¹ ∫_{-π}^{π} f(x) ḡ(x) dx = ∑_{n ∈ ℤ} c_n c̄'_n`. -/
@[dlmf 1.8.E6_2]
theorem hasSum_fourierExpCoeff_mul_conj {f g : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioc (-π) π)))
    (hg : MemLp g 2 (volume.restrict (Ioc (-π) π))) :
    HasSum (fun n : ℤ => fourierExpCoeff f n * starRingEnd ℂ (fourierExpCoeff g n))
      ((1 / (2 * π) : ℂ) * ∫ x in (-π)..π, f x * starRingEnd ℂ (g x)) := by
  have h := hasSum_fourierCoeffOn_mul_conj (by linarith [pi_pos] : -π < π) hf hg
  simp only [← fourierExpCoeff_eq_fourierCoeffOn, Complex.real_smul] at h
  convert h using 1
  congr 1
  push_cast
  ring

/-- DLMF 1.8.6_1 (Parseval's formula for two functions, trigonometric form): for `f`, `g`
square integrable on `[-π, π]`,
`π⁻¹ ∫_{-π}^{π} f(x) ḡ(x) dx = ½ a_0 ā'_0 + ∑_{n ≥ 1} (a_n ā'_n + b_n b̄'_n)`. -/
@[dlmf 1.8.E6_1]
theorem hasSum_fourierCosSinCoeff_mul_conj {f g : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioc (-π) π)))
    (hg : MemLp g 2 (volume.restrict (Ioc (-π) π))) :
    HasSum (fun n : ℕ => fourierCosCoeff f (n + 1) * starRingEnd ℂ (fourierCosCoeff g (n + 1)) +
        fourierSinCoeff f (n + 1) * starRingEnd ℂ (fourierSinCoeff g (n + 1)))
      ((1 / π : ℂ) * (∫ x in (-π)..π, f x * starRingEnd ℂ (g x)) -
        fourierCosCoeff f 0 * starRingEnd ℂ (fourierCosCoeff g 0) / 2) := by
  have hfi := intervalIntegrable_neg_pi_pi_of_memLp hf
  have hgi := intervalIntegrable_neg_pi_pi_of_memLp hg
  have h := (hasSum_fourierExpCoeff_mul_conj hf hg).nat_add_neg
  have h1 := (hasSum_nat_add_iff' 1).mpr h
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, neg_zero] at h1
  have key (n : ℕ) :
      fourierCosCoeff f n * starRingEnd ℂ (fourierCosCoeff g n) +
        fourierSinCoeff f n * starRingEnd ℂ (fourierSinCoeff g n) =
      2 * (fourierExpCoeff f n * starRingEnd ℂ (fourierExpCoeff g n) +
        fourierExpCoeff f (-(n : ℤ)) * starRingEnd ℂ (fourierExpCoeff g (-(n : ℤ)))) := by
    rw [fourierExpCoeff_natCast hfi, fourierExpCoeff_neg_natCast hfi,
      fourierExpCoeff_natCast hgi, fourierExpCoeff_neg_natCast hgi]
    simp only [map_div₀, map_sub, map_add, map_mul, Complex.conj_I, map_ofNat]
    ring_nf
    rw [Complex.I_sq]
    ring
  convert h1.mul_left 2 using 1
  · ext n
    rw [key]
  · rw [fourierExpCoeff_zero hfi, fourierExpCoeff_zero hgi]
    simp only [map_div₀, map_ofNat]
    field_simp
    ring

/-- The exponential Fourier coefficients are the Fourier transform of the function
restricted to a period, with the frequency and integral normalization rescaled. -/
lemma fourierExpCoeff_eq_fourier_indicator (f : ℝ → ℂ) (n : ℤ) :
    fourierExpCoeff f n = (1 / (2 * π) : ℂ) *
      𝓕 ((Ioc (-π) π).indicator f) ((n : ℝ) / (2 * π)) := by
  rw [fourierExpCoeff, intervalIntegral.integral_of_le (by linarith [pi_pos]),
    Real.fourier_eq', ← integral_indicator measurableSet_Ioc]
  congr 1
  apply integral_congr_ae (Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ Ioc (-π) π
  · simp only [indicator_of_mem hx, smul_eq_mul, mul_comm]
    congr 2
    simp only [RCLike.inner_apply, conj_trivial]
    push_cast
    field_simp [pi_ne_zero]
  · simp [hx]

/-- The exponential Fourier coefficients vanish along any sequence of integer
frequencies escaping finite sets; no convergence assumption is needed for totalized integrals. -/
lemma tendsto_fourierExpCoeff_comp {k : ℕ → ℤ} (f : ℝ → ℂ)
    (hk : Tendsto k atTop cofinite) :
    Tendsto (fun n => fourierExpCoeff f (k n)) atTop (𝓝 0) := by
  have hπ : (1 / (2 * π) : ℝ) ≠ 0 := by positivity
  have ht := (Filter.tendsto_cocompact_mul_left₀ (K := ℝ) hπ).comp
    (Int.tendsto_coe_cofinite.comp hk)
  have h := ((Real.zero_at_infty_fourier ((Ioc (-π) π).indicator f)).comp ht).const_mul
    (1 / (2 * π) : ℂ)
  simpa only [fourierExpCoeff_eq_fourier_indicator, mul_zero, div_eq_mul_inv,
    one_div, mul_comm, Function.comp_apply, one_mul, zero_mul] using h

/-- Differentiation of a continuously differentiable periodic function multiplies
its nonzero Fourier coefficients by `in`. This is Mathlib's integration-by-parts formula. -/
lemma fourierExpCoeff_deriv {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f)
    (hper : Function.Periodic f (2 * π)) {n : ℤ} (hn : n ≠ 0) :
    fourierExpCoeff (deriv f) n = (I * n) * fourierExpCoeff f n := by
  have h := fourierCoeffOn_of_hasDerivAt (by linarith [pi_pos] : -π < π) hn
    (fun x _ => (hf.differentiable (by norm_num) x).hasDerivAt)
    ((contDiff_one_iff_deriv.mp hf).2.intervalIntegrable (-π) π)
  have hp : f π = f (-π) := by simpa only [show -π + 2 * π = π by ring] using hper (-π)
  simp only [hp, sub_self, mul_zero, zero_sub, ← fourierExpCoeff_eq_fourierCoeffOn] at h
  have hn' : (n : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hn
  field_simp [pi_ne_zero, hn', I_ne_zero] at h
  apply mul_left_cancel₀ (show (2 * (π : ℂ)) ≠ 0 by exact_mod_cast (by positivity :
    (2 * π : ℝ) ≠ 0))
  push_cast at h
  linear_combination -h

/-- Repeated differentiation multiplies each nonzero Fourier coefficient by `(in)^m`.
Periodicity of derivatives is supplied by TauCeti's `Function.Periodic.deriv`. -/
lemma fourierExpCoeff_iteratedDeriv {f : ℝ → ℂ} {m : ℕ} (hf : ContDiff ℝ m f)
    (hper : Function.Periodic f (2 * π)) {n : ℤ} (hn : n ≠ 0) :
    fourierExpCoeff (iteratedDeriv m f) n = (I * n) ^ m * fourierExpCoeff f n := by
  induction m generalizing f with
  | zero => simp
  | succ m ih =>
    rw [iteratedDeriv_succ', ih hf.deriv' hper.deriv,
      fourierExpCoeff_deriv (hf.of_le (by exact_mod_cast Nat.succ_pos m)) hper hn,
      pow_succ]
    ring

/-- Along any nonzero integer multiple of the natural frequencies, a `C^m` periodic
function has coefficients `o(n⁻ᵐ)`. -/
lemma fourierExpCoeff_mul_nat_isLittleO {f : ℝ → ℂ} {m : ℕ} (hf : ContDiff ℝ m f)
    (hper : Function.Periodic f (2 * π)) (k : ℤ) (hk : k ≠ 0) :
    (fun n : ℕ => fourierExpCoeff f (k * n)) =o[atTop]
      (fun n : ℕ => ((n : ℝ) ^ m)⁻¹) := by
  have hk' : (k : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hk
  have hkc : Tendsto (fun n : ℕ => k * (n : ℤ)) atTop cofinite := by
    rw [← Nat.cofinite_eq_atTop]
    have hi : Function.Injective (fun n : ℕ => k * (n : ℤ)) := by
      intro n m h
      exact_mod_cast mul_left_cancel₀ hk h
    exact hi.tendsto_cofinite
  have ht := (tendsto_fourierExpCoeff_comp (iteratedDeriv m f) hkc).const_mul
    (((I * (k : ℂ)) ^ m)⁻¹)
  have he : (fun n : ℕ => fourierExpCoeff f (k * n) / ((n : ℂ) ^ m)⁻¹) =ᶠ[atTop]
      fun n => ((I * (k : ℂ)) ^ m)⁻¹ * fourierExpCoeff (iteratedDeriv m f) (k * n) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [fourierExpCoeff_iteratedDeriv hf hper (mul_ne_zero hk (by exact_mod_cast hn.ne'))]
    push_cast
    field_simp [hk', I_ne_zero]
    ring
  have hz : ∀ᶠ n : ℕ in atTop, ((n : ℂ) ^ m)⁻¹ = 0 → fourierExpCoeff f (k * n) = 0 := by
    filter_upwards [eventually_gt_atTop 0] with n hn hzero
    exact False.elim ((inv_ne_zero (pow_ne_zero _ (by exact_mod_cast hn.ne'))) hzero)
  have ho := (isLittleO_iff_tendsto' hz).mpr (by simpa only [mul_zero] using ht.congr' he.symm)
  simpa only [← ofReal_natCast, ← ofReal_pow, ← ofReal_inv, isLittleO_ofReal_right] using ho

/-- DLMF 1.8.7: if `f` has period `2π` and `f^{(m)}` is piecewise continuous, then
`a_n, b_n, c_n = o(n^{-m})` as `n → ∞`. Special case: `f` is assumed `C^m` (so `f^{(m)}` is
continuous). -/
@[dlmf 1.8.E7]
theorem fourierCoeff_isLittleO {f : ℝ → ℂ} {m : ℕ} (hf : ContDiff ℝ m f)
    (hper : Function.Periodic f (2 * π)) :
    (fun n : ℕ => fourierCosCoeff f n) =o[atTop] (fun n : ℕ => ((n : ℝ) ^ m)⁻¹) ∧
    (fun n : ℕ => fourierSinCoeff f n) =o[atTop] (fun n : ℕ => ((n : ℝ) ^ m)⁻¹) ∧
    (fun n : ℕ => fourierExpCoeff f n) =o[atTop] (fun n : ℕ => ((n : ℝ) ^ m)⁻¹) := by
  have hp := fourierExpCoeff_mul_nat_isLittleO hf hper 1 one_ne_zero
  have hm := fourierExpCoeff_mul_nat_isLittleO hf hper (-1) (by norm_num)
  simp only [one_mul, neg_one_mul] at hp hm
  have hi : IntervalIntegrable f volume (-π) π := hf.continuous.intervalIntegrable (-π) π
  refine ⟨(hp.add hm).congr_left (fun n => ?_),
    ((hp.sub hm).const_mul_left I).congr_left (fun n => ?_), hp⟩
  · rw [fourierExpCoeff_natCast hi, fourierExpCoeff_neg_natCast hi]
    ring
  · rw [fourierExpCoeff_natCast hi, fourierExpCoeff_neg_natCast hi]
    ring_nf
    rw [I_sq]
    ring

/-- DLMF §1.8(i) (uniqueness of Fourier series): continuous `2π`-periodic functions with the
same Fourier coefficients `a_n`, `b_n` are equal. -/
@[dlmf 1.8.i]
theorem eq_of_fourierCoeff_eq {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hfp : Function.Periodic f (2 * π)) (hgp : Function.Periodic g (2 * π))
    (ha : ∀ n, fourierCosCoeff f n = fourierCosCoeff g n)
    (hb : ∀ n, fourierSinCoeff f n = fourierSinCoeff g n) : f = g := by
  have : Fact (0 < 2 * π) := ⟨by positivity⟩
  let F : C(AddCircle (2 * π), ℂ) := ⟨hfp.lift, continuous_coinduced_dom.mpr hf⟩
  let G : C(AddCircle (2 * π), ℂ) := ⟨hgp.lift, continuous_coinduced_dom.mpr hg⟩
  have hc (n : ℤ) : fourierExpCoeff f n = fourierExpCoeff g n := by
    rcases n with n | n
    · change fourierExpCoeff f (n : ℤ) = fourierExpCoeff g (n : ℤ)
      rw [fourierExpCoeff_natCast (hf.intervalIntegrable _ _),
        fourierExpCoeff_natCast (hg.intervalIntegrable _ _), ha, hb]
    · change fourierExpCoeff f (-((n + 1 : ℕ) : ℤ)) =
        fourierExpCoeff g (-((n + 1 : ℕ) : ℤ))
      rw [fourierExpCoeff_neg_natCast (hf.intervalIntegrable _ _),
        fourierExpCoeff_neg_natCast (hg.intervalIntegrable _ _), ha, hb]
  have hFG : F = G := by
    apply ContinuousMap.toLp_injective (𝕜 := ℂ) (p := 2) AddCircle.haarAddCircle
    apply fourierBasis.repr.injective
    ext n
    rw [fourierBasis_repr, fourierBasis_repr, fourierCoeff_toLp, fourierCoeff_toLp]
    exact (fourierCoeff_lift_eq_fourierExpCoeff hfp n).trans
      ((hc n).trans (fourierCoeff_lift_eq_fourierExpCoeff hgp n).symm)
  funext x
  exact congrArg (fun H : C(AddCircle (2 * π), ℂ) => H (x : AddCircle (2 * π))) hFG

/-- DLMF 1.8.9: the Lebesgue constants satisfy `L_n ∼ (4/π²) ln n` as `n → ∞`. -/
@[dlmf 1.8.E9]
theorem lebesgueConstant_isEquivalent :
    (fun n : ℕ => lebesgueConstant n) ~[atTop] (fun n : ℕ => 4 / π ^ 2 * Real.log n) := by
  sorry

/-- DLMF §1.8(i) (extension of the Riemann–Lebesgue lemma 1.8.10 to infinite intervals): for
`f` Lebesgue integrable on `ℝ`, `∫ f(x) e^{iλx} dx → 0` as `λ → ∞` (no hypothesis is needed
in Lean: for non-integrable `f` the integral is `0` by totalization). This covers infinite
endpoints and integrable singularities; DLMF also allows conditionally convergent improper
integrals (uniform convergence at the endpoints and singularities), which is not covered here.
From Mathlib's `Real.tendsto_integral_exp_smul_cocompact`. -/
@[dlmf 1.8.i]
theorem tendsto_integral_mul_exp_atTop (f : ℝ → ℂ) :
    Tendsto (fun lam : ℝ => ∫ x, f x * Complex.exp (Complex.I * lam * x)) atTop (𝓝 0) := by
  have hw : Tendsto (fun lam : ℝ => -lam / (2 * π)) atTop (cocompact ℝ) :=
    ((tendsto_neg_atTop_atBot).atBot_div_const (by positivity)).mono_right atBot_le_cocompact
  have h := (Real.tendsto_integral_exp_smul_cocompact f).comp hw
  refine h.congr fun lam => ?_
  simp only [Function.comp_apply]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  rw [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, mul_comm _ (f x)]
  congr 2
  push_cast
  field_simp [pi_ne_zero]

/-- DLMF 1.8.10 (Riemann–Lebesgue lemma): for `f` integrable on `[a, b]`,
`∫_a^b f(x) e^{iλx} dx → 0` as `λ → ∞`. Stronger than DLMF: any `f` integrable on `[a, b]`
(Lebesgue) is covered, and in Lean no hypothesis is needed (a non-integrable integrand has
integral `0`). -/
@[dlmf 1.8.E10]
theorem tendsto_intervalIntegral_mul_exp_atTop (f : ℝ → ℂ) {a b : ℝ} (hab : a ≤ b) :
    Tendsto (fun lam : ℝ => ∫ x in a..b, f x * Complex.exp (Complex.I * lam * x)) atTop
      (𝓝 0) := by
  refine (tendsto_integral_mul_exp_atTop ((Ioc a b).indicator f)).congr fun lam => ?_
  rw [intervalIntegral.integral_of_le hab, ← integral_indicator measurableSet_Ioc]
  congr 1
  funext x
  by_cases hx : x ∈ Ioc a b <;> simp [hx]

/-! ## §1.8(ii) Convergence -/

/-- The Dirichlet kernel `½ + ∑_{n=1}^N cos(nu)` of the Fourier partial sums. -/
private noncomputable def partialSumKernel (N : ℕ) (u : ℝ) : ℝ :=
  1 / 2 + ∑ n ∈ Finset.range N, Real.cos ((n + 1 : ℕ) * u)

private lemma two_mul_sin_mul_partialSumKernel (N : ℕ) (u : ℝ) :
    2 * Real.sin (u / 2) * partialSumKernel N u = Real.sin ((N + 1 / 2) * u) := by
  induction N with
  | zero => simp [partialSumKernel]; ring_nf
  | succ N ih =>
    have h := Real.sin_sub_sin (((N + 1 : ℕ) + 1 / 2) * u) ((N + 1 / 2) * u)
    simp only [partialSumKernel, Finset.sum_range_succ] at ih ⊢
    have h1 : (((N + 1 : ℕ) : ℝ) + 1 / 2) * u - (N + 1 / 2) * u = 2 * (u / 2) := by
      push_cast; ring
    have h2 : (((N + 1 : ℕ) : ℝ) + 1 / 2) * u + (N + 1 / 2) * u = 2 * (((N + 1 : ℕ) : ℝ) * u) := by
      push_cast; ring
    rw [h1, h2] at h
    simp only [mul_div_cancel_left₀ _ (two_ne_zero' ℝ)] at h
    push_cast at h ih ⊢
    linear_combination ih - h

private lemma partialSumKernel_neg (N : ℕ) (u : ℝ) :
    partialSumKernel N (-u) = partialSumKernel N u := by
  simp [partialSumKernel, mul_neg, Real.cos_neg]

private lemma partialSumKernel_add_two_pi (N : ℕ) (u : ℝ) :
    partialSumKernel N (u + 2 * π) = partialSumKernel N u := by
  simp only [partialSumKernel]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [mul_add, show ((n + 1 : ℕ) : ℝ) * (2 * π) = ((n + 1 : ℕ) : ℕ) * (2 * π) by rfl,
    Real.cos_add_nat_mul_two_pi]

private lemma continuous_partialSumKernel (N : ℕ) : Continuous (partialSumKernel N) := by
  unfold partialSumKernel; fun_prop

private lemma integral_partialSumKernel (N : ℕ) :
    ∫ u in (0 : ℝ)..π, partialSumKernel N u = π / 2 := by
  have hc : ∀ n : ℕ, ∫ u in (0 : ℝ)..π, Real.cos ((n + 1 : ℕ) * u) = 0 := by
    intro n
    have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    rw [intervalIntegral.integral_comp_mul_left (fun u => Real.cos u) hn, integral_cos]
    simp only [mul_zero, Real.sin_zero, sub_zero]
    rw [Real.sin_nat_mul_pi, smul_zero]
  simp only [partialSumKernel]
  rw [intervalIntegral.integral_add intervalIntegrable_const
      ((by fun_prop : Continuous fun u : ℝ => ∑ n ∈ Finset.range N,
        Real.cos ((n + 1 : ℕ) * u)).intervalIntegrable _ _),
    intervalIntegral.integral_finsetSum fun n _ =>
      (by fun_prop : Continuous fun u => Real.cos ((n + 1 : ℕ) * u)).intervalIntegrable _ _]
  simp only [hc, Finset.sum_const_zero, intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- The Fourier partial sum as a Dirichlet-kernel integral. -/
private lemma fourierPartialSum_eq_integral {f : ℝ → ℂ}
    (hf : IntervalIntegrable f volume (-π) π) (x : ℝ) (N : ℕ) :
    fourierCosCoeff f 0 / 2 + ∑ n ∈ Finset.range N,
        (fourierCosCoeff f (n + 1) * (Real.cos ((n + 1 : ℕ) * x) : ℂ) +
          fourierSinCoeff f (n + 1) * (Real.sin ((n + 1 : ℕ) * x) : ℂ)) =
      (1 / π : ℂ) * ∫ t in (-π)..π, f t * (partialSumKernel N (t - x) : ℂ) := by
  have hI : ∀ g : ℝ → ℝ, Continuous g →
      IntervalIntegrable (fun t => f t * (g t : ℂ)) volume (-π) π := fun g hg =>
    hf.mul_continuousOn (Complex.continuous_ofReal.comp hg).continuousOn
  have hterm : ∀ n : ℕ, ∫ t in (-π)..π, f t * (Real.cos ((n + 1 : ℕ) * (t - x)) : ℂ) =
      (Real.cos ((n + 1 : ℕ) * x) : ℂ) *
        (∫ t in (-π)..π, f t * (Real.cos ((n + 1 : ℕ) * t) : ℂ)) +
      (Real.sin ((n + 1 : ℕ) * x) : ℂ) *
        ∫ t in (-π)..π, f t * (Real.sin ((n + 1 : ℕ) * t) : ℂ) := by
    intro n
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add
        ((hI (fun t => Real.cos ((n + 1 : ℕ) * t)) (by fun_prop)).const_mul _)
        ((hI (fun t => Real.sin ((n + 1 : ℕ) * t)) (by fun_prop)).const_mul _)]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [mul_sub, Real.cos_sub]
    push_cast; ring
  have hsplit : ∫ t in (-π)..π, f t * (partialSumKernel N (t - x) : ℂ) =
      (∫ t in (-π)..π, f t * ((1 / 2 : ℝ) : ℂ)) + ∑ n ∈ Finset.range N,
        ∫ t in (-π)..π, f t * (Real.cos ((n + 1 : ℕ) * (t - x)) : ℂ) := by
    have hS : ∀ n ∈ Finset.range N, IntervalIntegrable
        (fun t => f t * (Real.cos ((n + 1 : ℕ) * (t - x)) : ℂ)) volume (-π) π :=
      fun n _ => hI (fun t => Real.cos ((n + 1 : ℕ) * (t - x))) (by fun_prop)
    have hS' : IntervalIntegrable (fun t => ∑ n ∈ Finset.range N,
        f t * (Real.cos ((n + 1 : ℕ) * (t - x)) : ℂ)) volume (-π) π := by
      simpa only [Finset.sum_fn] using IntervalIntegrable.sum _ hS
    rw [← intervalIntegral.integral_finsetSum hS,
      ← intervalIntegral.integral_add (hI _ continuous_const) hS']
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [partialSumKernel]; push_cast
    rw [mul_add, Finset.mul_sum]
  rw [hsplit, mul_add, Finset.mul_sum]
  congr 1
  · simp only [fourierCosCoeff, CharP.cast_eq_zero, zero_mul, Real.cos_zero, ofReal_one,
      mul_one]
    rw [intervalIntegral.integral_mul_const]; push_cast; ring
  · refine Finset.sum_congr rfl fun n _ => ?_
    rw [hterm, fourierCosCoeff, fourierSinCoeff]; ring


/-- DLMF 1.8.11, stronger than DLMF, which also assumes that `f` is continuous except at
finitely many points of every bounded interval: for `f` integrable on `[-π, π]` and of period
`2π`, at a point `x` where `f` has one-sided limits `f(x∓)` and one-sided derivatives, the
Fourier partial sums converge to `½f(x-) + ½f(x+)`. -/
@[dlmf 1.8.E11]
theorem tendsto_fourierPartialSum_of_oneSidedDeriv' {f : ℝ → ℂ}
    (hf : IntervalIntegrable f volume (-π) π) (hper : Function.Periodic f (2 * π))
    {x : ℝ} {fL fR dL dR : ℂ}
    (hL : Tendsto (fun h : ℝ => (f (x + h) - fL) / h) (𝓝[<] 0) (𝓝 dL))
    (hR : Tendsto (fun h : ℝ => (f (x + h) - fR) / h) (𝓝[>] 0) (𝓝 dR)) :
    Tendsto (fun N : ℕ => fourierCosCoeff f 0 / 2 + ∑ n ∈ Finset.range N,
        (fourierCosCoeff f (n + 1) * (Real.cos ((n + 1 : ℕ) * x) : ℂ) +
          fourierSinCoeff f (n + 1) * (Real.sin ((n + 1 : ℕ) * x) : ℂ)))
      atTop (𝓝 (fL / 2 + fR / 2)) := by
  have hfint : ∀ a b, IntervalIntegrable f volume a b := by
    intro a b
    refine hper.intervalIntegrable Real.two_pi_pos.ne' (t := -π) ?_ a b
    convert hf using 2; ring
  have hfx : ∀ a b, IntervalIntegrable (fun u => f (x + u)) volume a b := fun a b => by
    simpa using (hfint (x + a) (x + b)).comp_add_left x
  have hfx' : ∀ a b, IntervalIntegrable (fun u => f (x - u)) volume a b := fun a b => by
    simpa using (hfint (x - a) (x - b)).comp_sub_left x
  have hKc : ∀ N, Continuous fun u => (partialSumKernel N u : ℂ) := fun N =>
    Complex.continuous_ofReal.comp (continuous_partialSumKernel N)
  -- shift to the point `x`
  have hshift : ∀ N, ∫ t in (-π)..π, f t * (partialSumKernel N (t - x) : ℂ) =
      ∫ u in (-π)..π, f (x + u) * (partialSumKernel N u : ℂ) := by
    intro N
    have hP : Function.Periodic (fun t => f t * (partialSumKernel N (t - x) : ℂ)) (2 * π) := by
      intro t
      simp only
      rw [hper t, show t + 2 * π - x = (t - x) + 2 * π by ring, partialSumKernel_add_two_pi]
    have h1 := intervalIntegral.integral_comp_add_left
      (fun t => f t * (partialSumKernel N (t - x) : ℂ)) x (a := -π) (b := π)
    simp only [add_sub_cancel_left] at h1
    rw [h1, show x + π = x + -π + 2 * π by ring, hP.intervalIntegral_add_eq (x + -π) (-π),
      show -π + 2 * π = π by ring]
  -- fold to `[0, π]`
  have hfold : ∀ N, ∫ u in (-π)..π, f (x + u) * (partialSumKernel N u : ℂ) =
      ∫ u in (0 : ℝ)..π, (f (x + u) + f (x - u)) * (partialSumKernel N u : ℂ) := by
    intro N
    have hG : ∀ a b, IntervalIntegrable (fun u => f (x + u) * (partialSumKernel N u : ℂ))
        volume a b := fun a b => (hfx a b).mul_continuousOn (hKc N).continuousOn
    have hG' : ∀ a b, IntervalIntegrable (fun u => f (x - u) * (partialSumKernel N u : ℂ))
        volume a b := fun a b => (hfx' a b).mul_continuousOn (hKc N).continuousOn
    rw [← intervalIntegral.integral_add_adjacent_intervals (hG (-π) 0) (hG 0 π)]
    have hneg := intervalIntegral.integral_comp_neg (a := 0) (b := π)
      (fun u => f (x + u) * (partialSumKernel N u : ℂ))
    simp only [neg_zero, partialSumKernel_neg, ← sub_eq_add_neg] at hneg
    rw [← hneg, ← intervalIntegral.integral_add (hG' 0 π) (hG 0 π)]
    refine intervalIntegral.integral_congr fun u _ => ?_
    ring
  set ψ : ℝ → ℂ := fun u => (f (x + u) - fR) + (f (x - u) - fL) with hψ
  set φ : ℝ → ℂ := fun u => ψ u * ((1 / (2 * Real.sin (u / 2)) : ℝ) : ℂ) with hφ
  have hψi : IntervalIntegrable ψ volume 0 π :=
    ((hfx 0 π).sub intervalIntegrable_const).add ((hfx' 0 π).sub intervalIntegrable_const)
  have hmain : ∀ N : ℕ, (fourierCosCoeff f 0 / 2 + ∑ n ∈ Finset.range N,
        (fourierCosCoeff f (n + 1) * (Real.cos ((n + 1 : ℕ) * x) : ℂ) +
          fourierSinCoeff f (n + 1) * (Real.sin ((n + 1 : ℕ) * x) : ℂ))) - (fL / 2 + fR / 2) =
      (1 / π : ℂ) * ∫ u in (0 : ℝ)..π, φ u * (Real.sin ((N + 1 / 2) * u) : ℂ) := by
    intro N
    rw [fourierPartialSum_eq_integral hf x N, hshift, hfold]
    have hK : ∫ u in (0 : ℝ)..π, (partialSumKernel N u : ℂ) = ((π / 2 : ℝ) : ℂ) := by
      rw [intervalIntegral.integral_ofReal, integral_partialSumKernel]
    have hsplit : ∫ u in (0 : ℝ)..π, (f (x + u) + f (x - u)) * (partialSumKernel N u : ℂ) =
        (∫ u in (0 : ℝ)..π, ψ u * (partialSumKernel N u : ℂ)) +
          (fR + fL) * ∫ u in (0 : ℝ)..π, (partialSumKernel N u : ℂ) := by
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add
        (hψi.mul_continuousOn (hKc N).continuousOn) (((hKc N).intervalIntegrable _ _).const_mul _)]
      refine intervalIntegral.integral_congr fun u _ => ?_
      simp only [hψ]; ring
    have hcongr : ∫ u in (0 : ℝ)..π, ψ u * (partialSumKernel N u : ℂ) =
        ∫ u in (0 : ℝ)..π, φ u * (Real.sin ((N + 1 / 2) * u) : ℂ) := by
      rw [intervalIntegral.integral_of_le pi_pos.le, intervalIntegral.integral_of_le pi_pos.le]
      refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
      have hs : 0 < Real.sin (u / 2) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith [hu.1]) (by linarith [hu.2, pi_pos])
      rw [← two_mul_sin_mul_partialSumKernel N u]
      have h1 : 1 / (2 * Real.sin (u / 2)) * (2 * Real.sin (u / 2) * partialSumKernel N u) =
          partialSumKernel N u := by field_simp
      simp only [hφ]
      rw [mul_assoc, ← Complex.ofReal_mul, h1]
    rw [hsplit, hK, hcongr]
    push_cast
    field_simp
    ring
  -- `ψ(u) = O(u)` near `0`
  obtain ⟨C, δ, hC, hδ, hCδ⟩ : ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ u ∈ Ioo 0 δ, ‖ψ u‖ ≤ C * u := by
    have hL' : Tendsto (fun u : ℝ => (f (x + -u) - fL) / ((-u : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 dL) := by
      have := hL.comp (by simpa using (tendsto_neg_nhdsGT_neg (a := (0 : ℝ))))
      simpa [Function.comp_def] using this
    have e1 := hR.norm.eventually (gt_mem_nhds (lt_add_one ‖dR‖))
    have e2 := hL'.norm.eventually (gt_mem_nhds (lt_add_one ‖dL‖))
    obtain ⟨δ, hδ, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (e1.and e2)
    refine ⟨‖dR‖ + 1 + (‖dL‖ + 1), δ, by positivity, hδ, fun u hu => ?_⟩
    obtain ⟨h1, h2⟩ := hsub hu
    have hu0 : 0 < u := hu.1
    simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos hu0,
      ← sub_eq_add_neg] at h1 h2
    rw [div_lt_iff₀ hu0] at h1 h2
    calc ‖ψ u‖ ≤ ‖f (x + u) - fR‖ + ‖f (x - u) - fL‖ := norm_add_le _ _
      _ ≤ _ := by nlinarith
  have hφi : IntegrableOn φ (Ioc 0 π) := by
    have hψI : IntegrableOn ψ (Ioc 0 π) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le pi_pos.le).1 hψi
    have hconst : IntegrableOn (fun _ : ℝ => C) (Ioc 0 π) :=
      integrableOn_const measure_Ioc_lt_top.ne
    refine Integrable.mono' ((hconst.add (hψI.norm.div_const δ)).const_mul (π / 2)) ?_ ?_
    · have hm : Measurable fun u : ℝ => ((1 / (2 * Real.sin (u / 2)) : ℝ) : ℂ) := by fun_prop
      exact hψI.aestronglyMeasurable.mul hm.aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun u hu => ?_)
      have hu0 : 0 < u := hu.1
      have hs : 2 / π * (u / 2) ≤ Real.sin (u / 2) :=
        Real.mul_le_sin (by linarith) (by linarith [hu.2])
      have hs0 : 0 < Real.sin (u / 2) :=
        lt_of_lt_of_le (by have := pi_pos; positivity) hs
      have hkey : ‖φ u‖ ≤ ‖ψ u‖ * (π / (2 * u)) := by
        simp only [hφ, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        rw [abs_of_pos (by positivity)]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have := pi_pos
        have h2 : 2 / π * (u / 2) * π = u := by field_simp
        nlinarith
      change ‖φ u‖ ≤ π / 2 * (C + ‖ψ u‖ / δ)
      refine hkey.trans ?_
      rcases lt_or_ge u δ with huδ | huδ
      · have h := hCδ u ⟨hu0, huδ⟩
        have : ‖ψ u‖ * (π / (2 * u)) ≤ C * u * (π / (2 * u)) :=
          mul_le_mul_of_nonneg_right h (by have := pi_pos; positivity)
        have h3 : C * u * (π / (2 * u)) = π / 2 * C := by field_simp
        have h4 : 0 ≤ ‖ψ u‖ / δ := by positivity
        have := pi_pos
        nlinarith
      · have h5 : ‖ψ u‖ * (π / (2 * u)) ≤ ‖ψ u‖ * (π / (2 * δ)) :=
          mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_left pi_pos.le (by positivity) (by linarith)) (norm_nonneg _)
        have h6 : ‖ψ u‖ * (π / (2 * δ)) = π / 2 * (‖ψ u‖ / δ) := by field_simp
        have := pi_pos
        nlinarith
  have hRL : Tendsto (fun N : ℕ => ∫ u in (0 : ℝ)..π, φ u * (Real.sin ((N + 1 / 2) * u) : ℂ))
      atTop (𝓝 0) := by
    have h := Real.tendsto_integral_mul_sin_atTop (hφi.integrable_indicator measurableSet_Ioc)
    have hη : Tendsto (fun N : ℕ => (N : ℝ) + 1 / 2) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    refine (h.comp hη).congr fun N => ?_
    simp only [Function.comp_apply]
    rw [intervalIntegral.integral_of_le pi_pos.le, ← integral_indicator measurableSet_Ioc]
    congr 1
    funext v
    by_cases hv : v ∈ Ioc 0 π <;> simp [hv]
  refine tendsto_sub_nhds_zero_iff.1 ?_
  simp_rw [hmain]
  simpa using hRL.const_mul (1 / π : ℂ)


/-- DLMF 1.8.11 in kernel form: under the hypotheses of
`tendsto_fourierPartialSum_of_oneSidedDeriv'`, the Dirichlet-kernel integrals
`π⁻¹ ∫_{-π}^{π} f(t) (½ + ∑_{n=1}^N cos(n(t - x))) dt` tend to `½f(x-) + ½f(x+)`. -/
theorem tendsto_integral_mul_cosineKernel_of_oneSidedDeriv {f : ℝ → ℂ}
    (hf : IntervalIntegrable f volume (-π) π) (hper : Function.Periodic f (2 * π))
    {x : ℝ} {fL fR dL dR : ℂ}
    (hL : Tendsto (fun h : ℝ => (f (x + h) - fL) / h) (𝓝[<] 0) (𝓝 dL))
    (hR : Tendsto (fun h : ℝ => (f (x + h) - fR) / h) (𝓝[>] 0) (𝓝 dR)) :
    Tendsto (fun N : ℕ => (1 / π : ℂ) * ∫ t in (-π)..π, f t *
        ((1 / 2 + ∑ n ∈ Finset.range N, Real.cos ((n + 1 : ℕ) * (t - x)) : ℝ) : ℂ))
      atTop (𝓝 (fL / 2 + fR / 2)) :=
  (tendsto_fourierPartialSum_of_oneSidedDeriv' hf hper hL hR).congr fun N =>
    fourierPartialSum_eq_integral hf x N

/-- DLMF 1.8.11: let `f` be absolutely integrable of period `2π` and continuous except at
finitely many points of every bounded interval. At a point `x` where `f` has one-sided limits
`f(x-)`, `f(x+)` and one-sided derivatives (difference quotients
`(f(x+h) - f(x∓))/h → f'_∓` as `h → 0∓`), the Fourier series 1.8.1 converges to
`½f(x-) + ½f(x+)`. Convergence is of the partial sums. -/
@[dlmf 1.8.E11]
theorem tendsto_fourierPartialSum_of_oneSidedDeriv {f : ℝ → ℂ}
    (hf : IntervalIntegrable f volume (-π) π) (hper : Function.Periodic f (2 * π))
    (_hfin : ∀ R : ℝ, {x ∈ Icc (-R) R | ¬ ContinuousAt f x}.Finite)
    {x : ℝ} {fL fR dL dR : ℂ}
    (hL : Tendsto (fun h : ℝ => (f (x + h) - fL) / h) (𝓝[<] 0) (𝓝 dL))
    (hR : Tendsto (fun h : ℝ => (f (x + h) - fR) / h) (𝓝[>] 0) (𝓝 dR)) :
    Tendsto (fun N : ℕ => fourierCosCoeff f 0 / 2 + ∑ n ∈ Finset.range N,
        (fourierCosCoeff f (n + 1) * (Real.cos ((n + 1 : ℕ) * x) : ℂ) +
          fourierSinCoeff f (n + 1) * (Real.sin ((n + 1 : ℕ) * x) : ℂ)))
      atTop (𝓝 (fL / 2 + fR / 2)) :=
  tendsto_fourierPartialSum_of_oneSidedDeriv' hf hper hL hR

/-! ## §1.8(iii) Integration and differentiation -/

/-- DLMF 1.8.12: if `a_n`, `b_n` are the Fourier coefficients of `f` on `[0, 2π]`
(`a_n = π⁻¹ ∫_0^{2π} f(t) cos(nt) dt`, `b_n = π⁻¹ ∫_0^{2π} f(t) sin(nt) dt`), then for
`0 ≤ x ≤ 2π`, `∫_0^x (f(t) - ½a_0) dt = ∑_{n ≥ 1} (a_n sin(nx) + b_n(1 - cos(nx)))/n`, as a
limit of partial sums. Stronger than DLMF: Lebesgue integrability on `[0, 2π]` replaces
piecewise continuity. -/
@[dlmf 1.8.E12]
theorem tendsto_integral_fourierSeries {f : ℝ → ℂ} (hf : IntervalIntegrable f volume 0 (2 * π))
    {x : ℝ} (hx : x ∈ Icc 0 (2 * π)) :
    let a : ℕ → ℂ := fun n => (1 / π : ℂ) * ∫ t in (0 : ℝ)..2 * π, f t * (Real.cos (n * t) : ℂ)
    let b : ℕ → ℂ := fun n => (1 / π : ℂ) * ∫ t in (0 : ℝ)..2 * π, f t * (Real.sin (n * t) : ℂ)
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N,
        (a (n + 1) * (Real.sin ((n + 1 : ℕ) * x) : ℂ) +
          b (n + 1) * (1 - (Real.cos ((n + 1 : ℕ) * x) : ℂ))) / ((n + 1 : ℕ) : ℂ))
      atTop (𝓝 (∫ t in (0 : ℝ)..x, (f t - a 0 / 2))) := by
  sorry

/-- Integration by parts for the Fourier coefficients of a derivative. -/
private lemma fourierCoeff_deriv {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f)
    (hper : Function.Periodic f (2 * π)) (m : ℕ) :
    fourierCosCoeff (deriv f) m = m * fourierSinCoeff f m ∧
      fourierSinCoeff (deriv f) m = -(m * fourierCosCoeff f m) := by
  have hfd : ∀ t, HasDerivAt f (deriv f t) t := fun t =>
    (hf.differentiable one_ne_zero t).hasDerivAt
  have hdc : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hend : f π = f (-π) := by
    have := hper (-π); rw [show -π + 2 * π = π by ring] at this; exact this
  have hcos : ∀ t, HasDerivAt (fun t : ℝ => (Real.cos (m * t) : ℂ))
      (-(m * (Real.sin (m * t) : ℂ))) t := by
    intro t
    have h := ((hasDerivAt_id t).const_mul (m : ℝ)).cos.ofReal_comp
    simp only [id, mul_one] at h
    convert h using 1
    push_cast; ring
  have hsin : ∀ t, HasDerivAt (fun t : ℝ => (Real.sin (m * t) : ℂ))
      (m * (Real.cos (m * t) : ℂ)) t := by
    intro t
    have h := ((hasDerivAt_id t).const_mul (m : ℝ)).sin.ofReal_comp
    simp only [id, mul_one] at h
    convert h using 1
    push_cast; ring
  have hI1 := intervalIntegral.integral_deriv_mul_eq_sub (a := -π) (b := π)
    (fun t _ => hfd t) (fun t _ => hcos t)
    (hdc.intervalIntegrable _ _) ((by fun_prop : Continuous fun t : ℝ =>
      -((m : ℂ) * (Real.sin (m * t) : ℂ))).intervalIntegrable _ _)
  have hI2 := intervalIntegral.integral_deriv_mul_eq_sub (a := -π) (b := π)
    (fun t _ => hfd t) (fun t _ => hsin t)
    (hdc.intervalIntegrable _ _) ((by fun_prop : Continuous fun t : ℝ =>
      (m : ℂ) * (Real.cos (m * t) : ℂ)).intervalIntegrable _ _)
  have hc1 : IntervalIntegrable (fun t => deriv f t * (Real.cos (m * t) : ℂ)) volume (-π) π :=
    (by fun_prop : Continuous fun t => deriv f t * (Real.cos (m * t) : ℂ)).intervalIntegrable _ _
  have hc2 : IntervalIntegrable (fun t => deriv f t * (Real.sin (m * t) : ℂ)) volume (-π) π :=
    (by fun_prop : Continuous fun t => deriv f t * (Real.sin (m * t) : ℂ)).intervalIntegrable _ _
  have hf0 : Continuous f := hf.continuous
  have hc3 : IntervalIntegrable (fun t => f t * (Real.sin (m * t) : ℂ)) volume (-π) π :=
    (by fun_prop : Continuous fun t => f t * (Real.sin (m * t) : ℂ)).intervalIntegrable _ _
  have hc4 : IntervalIntegrable (fun t => f t * (Real.cos (m * t) : ℂ)) volume (-π) π :=
    (by fun_prop : Continuous fun t => f t * (Real.cos (m * t) : ℂ)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add hc1 ((by fun_prop : Continuous fun t : ℝ =>
      f t * -((m : ℂ) * (Real.sin (m * t) : ℂ))).intervalIntegrable _ _)] at hI1
  rw [intervalIntegral.integral_add hc2 ((by fun_prop : Continuous fun t : ℝ =>
      f t * ((m : ℂ) * (Real.cos (m * t) : ℂ))).intervalIntegrable _ _)] at hI2
  have e1 : ∫ t in (-π)..π, f t * -((m : ℂ) * (Real.sin (m * t) : ℂ)) =
      -((m : ℂ) * ∫ t in (-π)..π, f t * (Real.sin (m * t) : ℂ)) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
    congr 1; funext t; ring
  have e2 : ∫ t in (-π)..π, f t * ((m : ℂ) * (Real.cos (m * t) : ℂ)) =
      (m : ℂ) * ∫ t in (-π)..π, f t * (Real.cos (m * t) : ℂ) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext t; ring
  rw [e1] at hI1
  rw [e2] at hI2
  simp only [mul_neg, Real.cos_neg, Real.sin_neg, hend, ofReal_neg, Real.sin_nat_mul_pi,
    ofReal_zero] at hI1 hI2
  constructor
  · simp only [fourierCosCoeff, fourierSinCoeff]
    linear_combination (1 / π : ℂ) * hI1
  · simp only [fourierCosCoeff, fourierSinCoeff]
    linear_combination (1 / π : ℂ) * hI2

/-- DLMF §1.8(iii): for a `2π`-periodic `f ∈ C²`, the term-by-term derivative of the Fourier
series, `∑_{n ≥ 1} n(b_n cos nx - a_n sin nx)`, converges at every point to `f'(x)`. -/
@[dlmf 1.8.iii]
theorem tendsto_deriv_fourierSeries {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hper : Function.Periodic f (2 * π)) (x : ℝ) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, ((n + 1 : ℕ) : ℂ) *
        (fourierSinCoeff f (n + 1) * (Real.cos ((n + 1 : ℕ) * x) : ℂ) -
          fourierCosCoeff f (n + 1) * (Real.sin ((n + 1 : ℕ) * x) : ℂ)))
      atTop (𝓝 (deriv f x)) := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hd1 : ContDiff ℝ 1 (deriv f) := by
    have := hf.iterate_deriv' 1 1
    simpa using this
  have hdper : Function.Periodic (deriv f) (2 * π) := hper.deriv
  have hdd : HasDerivAt (deriv f) (deriv (deriv f) x) x :=
    (hd1.differentiable one_ne_zero x).hasDerivAt
  have hslope := hdd.tendsto_slope_zero
  have hL : Tendsto (fun h : ℝ => (deriv f (x + h) - deriv f x) / h) (𝓝[<] 0)
      (𝓝 (deriv (deriv f) x)) := by
    refine (hslope.mono_left (nhdsWithin_mono _ fun h hh =>
      Set.mem_compl_singleton_iff.2 (ne_of_lt (Set.mem_Iio.1 hh)))).congr fun h => ?_
    rw [Complex.real_smul, div_eq_inv_mul, ofReal_inv]
  have hR : Tendsto (fun h : ℝ => (deriv f (x + h) - deriv f x) / h) (𝓝[>] 0)
      (𝓝 (deriv (deriv f) x)) := by
    refine (hslope.mono_left (nhdsWithin_mono _ fun h hh =>
      Set.mem_compl_singleton_iff.2 (ne_of_gt (Set.mem_Ioi.1 hh)))).congr fun h => ?_
    rw [Complex.real_smul, div_eq_inv_mul, ofReal_inv]
  have h := tendsto_fourierPartialSum_of_oneSidedDeriv'
    (hd1.continuous.intervalIntegrable _ _) hdper hL hR
  rw [add_halves] at h
  refine h.congr fun N => ?_
  rw [(fourierCoeff_deriv hf1 hper 0).1]
  simp only [CharP.cast_eq_zero, zero_mul, zero_div, zero_add]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [(fourierCoeff_deriv hf1 hper (n + 1)).1, (fourierCoeff_deriv hf1 hper (n + 1)).2]
  ring


/-! ## §1.8(iv) Poisson's summation formula -/

/-- DLMF 1.8.14 (Poisson's summation formula): if `f` is twice continuously differentiable and
`f` and `f''` are integrable over `ℝ`, then
`∑_{n ∈ ℤ} f(x + n) = ∑_{n ∈ ℤ} e^{2πinx} ∫_{-∞}^{∞} f(t) e^{-2πint} dt`; both series converge
(absolutely) to a common value. Mathlib's `Real.tsum_eq_tsum_fourier_of_rpow_decay` proves the
formula under decay hypotheses on `f` and its Fourier transform instead. -/
@[dlmf 1.8.E14]
theorem poisson_summation {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hi : Integrable f)
    (hi2 : Integrable (iteratedDeriv 2 f)) (x : ℝ) :
    ∃ s : ℂ, HasSum (fun n : ℤ => f (x + n)) s ∧
      HasSum (fun n : ℤ => Complex.exp (2 * π * Complex.I * n * x) *
        ∫ t, f t * Complex.exp (-(2 * π * Complex.I * n * t))) s := by
  sorry

/-- DLMF 1.8.15 (Poisson's summation formula, alternative form): if `f` is continuous and of
bounded variation on `[0, ∞)`, integrable on `[0, ∞)`, and `f(x) → 0` as `x → ∞`, then
`½f(0) + ∑_{n ≥ 1} f(n) = ∫_0^∞ f(x) dx + 2 ∑_{n ≥ 1} ∫_0^∞ f(x) cos(2πnx) dx`; both series
converge (as limits of partial sums) to a common value. -/
@[dlmf 1.8.E15]
theorem poissonSummation_cos {f : ℝ → ℂ} (hc : ContinuousOn f (Ici 0))
    (hbv : BoundedVariationOn f (Ici 0)) (hi : IntegrableOn f (Ioi 0))
    (hlim : Tendsto f atTop (𝓝 0)) :
    ∃ s : ℂ, Tendsto (fun N : ℕ => f 0 / 2 + ∑ n ∈ Finset.range N, f (n + 1)) atTop (𝓝 s) ∧
      Tendsto (fun N : ℕ => (∫ x in Ioi (0 : ℝ), f x) + 2 * ∑ n ∈ Finset.range N,
        ∫ x in Ioi (0 : ℝ), f x * (Real.cos (2 * π * (n + 1 : ℕ) * x) : ℂ)) atTop (𝓝 s) := by
  sorry

/-- DLMF 1.8.16: for `ℜω > 0`,
`∑_{n ∈ ℤ} e^{-(n+x)²ω} = √(π/ω) (1 + 2 ∑_{n ≥ 1} e^{-n²π²/ω} cos(2nπx))`, with the principal
square root. Stronger than DLMF: `x` may be complex. The special case `f(x) = e^{-ωx²}` of
1.8.14; compare Mathlib's `Complex.tsum_exp_neg_quadratic`. -/
@[dlmf 1.8.E16]
theorem hasSum_exp_neg_sq_mul {ω : ℂ} (hω : 0 < ω.re) (x : ℂ) :
    HasSum (fun n : ℤ => Complex.exp (-((n + x) ^ 2 * ω)))
      ((π / ω) ^ (1 / 2 : ℂ) * (1 + 2 * ∑' n : ℕ,
        Complex.exp (-(((n + 1 : ℕ) : ℂ) ^ 2 * π ^ 2 / ω)) *
          Complex.cos (2 * ((n + 1 : ℕ) : ℂ) * π * x))) := by
  have hω0 : ω ≠ 0 := fun h => by simp [h] at hω
  let a : ℂ := π / ω
  have ha : 0 < a.re := by
    dsimp [a]
    rw [div_eq_mul_inv, re_ofReal_mul, inv_re]
    exact mul_pos pi_pos (div_pos hω (normSq_pos.mpr hω0))
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha
  have hs : Summable (fun n : ℤ => cexp (-π * a * n ^ 2 + 2 * π * (-I * x) * n)) := by
    have hneg : (-π * a).re < 0 := by
      rw [neg_mul, neg_re, re_ofReal_mul]
      exact neg_neg_of_pos (mul_pos pi_pos ha)
    simpa only [add_zero] using Complex.summable_exp_quadratic hneg (2 * π * (-I * x)) 0
  have hpair := (hasSum_nat_add_iff' 1).mpr hs.hasSum.nat_add_neg
  simp only [Finset.range_one, Finset.sum_singleton, Int.cast_zero,
    pow_two, mul_zero, add_zero, Complex.exp_zero] at hpair
  have hterm (n : ℕ) :
      cexp (-π * a * (n : ℂ) ^ 2 + 2 * π * (-I * x) * n) +
        cexp (-π * a * (-(n : ℂ)) ^ 2 + 2 * π * (-I * x) * (-(n : ℂ))) =
      2 * (cexp (-((n : ℂ) ^ 2 * π ^ 2 / ω)) * Complex.cos (2 * n * π * x)) := by
    rw [Complex.exp_add, Complex.exp_add, Complex.cos]
    dsimp [a]
    have he₁ : -π * (π / ω) * (n : ℂ) ^ 2 = -((n : ℂ) ^ 2 * π ^ 2 / ω) := by ring
    have he₂ : -π * (π / ω) * (-(n : ℂ)) ^ 2 = -((n : ℂ) ^ 2 * π ^ 2 / ω) := by ring
    rw [he₁, he₂]
    ring
  have hsum : (∑' n : ℤ, cexp (-π * a * n ^ 2 + 2 * π * (-I * x) * n)) =
      1 + 2 * ∑' n : ℕ, cexp (-(((n + 1 : ℕ) : ℂ) ^ 2 * π ^ 2 / ω)) *
        Complex.cos (2 * ((n + 1 : ℕ) : ℂ) * π * x) := by
    have ht := hpair.tsum_eq
    simp only [Int.cast_natCast, Int.cast_neg] at ht
    simp_rw [← pow_two, hterm] at ht
    rw [tsum_mul_left] at ht
    norm_num only [Nat.cast_zero, zero_pow (by decide : 2 ≠ 0), zero_mul,
      zero_div, neg_zero, Complex.exp_zero, Complex.cos_zero, mul_one] at ht
    linear_combination -ht
  have he : (∑' n : ℤ, cexp (-π * a * n ^ 2 + 2 * π * (-I * x) * n)) =
      1 / a ^ (1 / 2 : ℂ) * ∑' n : ℤ, cexp (-((n + x) ^ 2 * ω)) := by
    convert Complex.tsum_exp_neg_quadratic ha (-I * x) using 1
    congr 1
    apply tsum_congr
    intro n
    congr 1
    dsimp [a]
    field_simp
    ring_nf
    simp [I_sq]
  have hmain : Summable (fun n : ℤ => cexp (-((n + x) ^ 2 * ω))) := by
    have hneg : (-ω).re < 0 := by simpa using neg_neg_of_pos hω
    convert Complex.summable_exp_quadratic hneg (-2 * x * ω) (-(x ^ 2 * ω)) using 1
    ext n
    congr 1
    ring
  rw [← hsum]
  convert hmain.hasSum using 1
  rw [he]
  change a ^ (1 / 2 : ℂ) * (1 / a ^ (1 / 2 : ℂ) * _) = _
  field_simp [cpow_ne_zero_iff.mpr (Or.inl ha0)]
  simp only [mul_comm]


end DLMF.AlgebraicAnalytic
