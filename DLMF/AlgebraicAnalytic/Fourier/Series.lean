/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AlgebraicAnalytic.Fourier.Defs
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
public import Mathlib.Topology.EMetricSpace.BoundedVariation

/-!
# Fourier series (DLMF §1.8)

Statements of DLMF §1.8 for `f : ℝ → ℂ`, with the coefficients `fourierCosCoeff`,
`fourierSinCoeff`, `fourierExpCoeff` and the Lebesgue constants `lebesgueConstant` of
`DLMF.AlgebraicAnalytic.Fourier.Defs`.

Conventions.
* DLMF series over `n = 1, 2, …` that may converge only conditionally (the Fourier series in
  1.8.1, 1.8.11, 1.8.12, the differentiated series of §1.8(iii) and 1.8.15) are stated as limits
  of partial sums (`Filter.Tendsto` of `∑ n ∈ Finset.range N`), not with `HasSum`, which over
  `ℂ` means absolute convergence. Series that converge absolutely under the stated hypotheses
  (Parseval 1.8.5–1.8.6_2, the exponential series 1.8.3 with summable coefficients, Poisson's
  formula 1.8.14, 1.8.16) use `HasSum`; doubly infinite series are indexed by `ℤ`.
* Periodicity is `Function.Periodic f (2 * π)`.
* Several DLMF hypotheses are formalized in a stronger-than-DLMF (more general) or special-case
  form; each docstring says which.

Proved here: the bridge `fourierExpCoeff = fourierCoeffOn` on `[-π, π]`, the relations
`c_n = (a_n - i b_n)/2`, `c_{-n} = (a_n + i b_n)/2`, `c_0 = a_0/2`, the vanishing of `b_n`
(`a_n`) for even (odd) `f`, Parseval's formula 1.8.6 (from Mathlib's
`hasSum_sq_fourierCoeffOn`) and 1.8.5, and the Riemann–Lebesgue lemma 1.8.10 together with
its extension to integrable functions on `ℝ` (from Mathlib's
`Real.tendsto_integral_exp_smul_cocompact`).
-/

@[expose] public noncomputable section

open Real Filter MeasureTheory Set Asymptotics
open scoped Topology

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
private lemma g1c_exp_neg_eq (n : ℤ) (x : ℝ) :
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
private lemma g1c_integral_split {f : ℝ → ℂ} (hf : IntervalIntegrable f volume (-π) π)
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
  rw [g1c_exp_neg_eq]
  ring

/-- DLMF §1.8(i) (after 1.8.4): `c_n = ½(a_n - i b_n)` for `n > 0` (in fact for all `n ≥ 0`),
for `f` integrable on `[-π, π]`. -/
@[dlmf 1.8.i]
theorem fourierExpCoeff_natCast {f : ℝ → ℂ} (hf : IntervalIntegrable f volume (-π) π)
    (n : ℕ) :
    fourierExpCoeff f n = (fourierCosCoeff f n - Complex.I * fourierSinCoeff f n) / 2 := by
  rw [fourierExpCoeff, g1c_integral_split hf, fourierCosCoeff, fourierSinCoeff]
  push_cast
  field_simp

/-- DLMF §1.8(i) (after 1.8.4): `c_{-n} = ½(a_n + i b_n)`, for `f` integrable on `[-π, π]`. -/
@[dlmf 1.8.i]
theorem fourierExpCoeff_neg_natCast {f : ℝ → ℂ} (hf : IntervalIntegrable f volume (-π) π)
    (n : ℕ) :
    fourierExpCoeff f (-(n : ℤ)) =
      (fourierCosCoeff f n + Complex.I * fourierSinCoeff f n) / 2 := by
  rw [fourierExpCoeff, g1c_integral_split hf, fourierCosCoeff, fourierSinCoeff]
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
private lemma g1c_integral_odd {g : ℝ → ℂ} (hg : ∀ x, g (-x) = -g x) :
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
  rw [fourierSinCoeff, g1c_integral_odd, mul_zero]
  intro x
  rw [hf, mul_neg, Real.sin_neg]
  push_cast
  ring

/-- DLMF §1.8(i): if `f(-x) = -f(x)`, then `a_n = 0` for all `n`. -/
@[dlmf 1.8.i]
theorem fourierCosCoeff_eq_zero_of_odd {f : ℝ → ℂ} (hf : ∀ x, f (-x) = -f x) (n : ℕ) :
    fourierCosCoeff f n = 0 := by
  rw [fourierCosCoeff, g1c_integral_odd, mul_zero]
  intro x
  rw [hf, mul_neg, Real.cos_neg]
  ring

/-- DLMF 1.8.3: the exponential Fourier series `f(x) = ∑_{n ∈ ℤ} c_n e^{inx}` of a continuous
`2π`-periodic `f` with summable coefficients `c_n` (1.8.4). This is Mathlib's
`has_pointwise_sum_fourier_series_of_summable` transported from `AddCircle (2π)` to `ℝ`. -/
@[dlmf 1.8.E3]
theorem hasSum_fourierExpSeries {f : ℝ → ℂ} (hf : Continuous f)
    (hper : Function.Periodic f (2 * π)) (hs : Summable (fourierExpCoeff f)) (x : ℝ) :
    HasSum (fun n : ℤ => fourierExpCoeff f n * Complex.exp (Complex.I * n * x)) (f x) := by
  have hT : Fact (0 < 2 * π) := ⟨by positivity⟩
  let F : C(AddCircle (2 * π), ℂ) := ⟨hper.lift, continuous_coinduced_dom.mpr hf⟩
  have hc : ∀ n, fourierCoeff F n = fourierExpCoeff f n := by
    intro n
    rw [fourierCoeff_eq_intervalIntegral _ n (-π), fourierExpCoeff,
      show -π + 2 * π = π by ring, Complex.real_smul]
    congr 1
    · push_cast; ring
    · refine intervalIntegral.integral_congr fun y _ => ?_
      simp only [F, ContinuousMap.coe_mk, Function.Periodic.lift_coe, fourier_coe_apply,
        smul_eq_mul]
      rw [mul_comm]
      congr 2
      push_cast
      field_simp [pi_ne_zero]
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
private lemma g1c_intervalIntegrable_of_memLp {f : ℝ → ℂ}
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
  have hi := g1c_intervalIntegrable_of_memLp hf
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
  sorry

/-- DLMF 1.8.6_2 (Parseval's formula for two functions, exponential form): for `f`, `g`
square integrable on `[-π, π]`, `(2π)⁻¹ ∫_{-π}^{π} f(x) ḡ(x) dx = ∑_{n ∈ ℤ} c_n c̄'_n`. -/
@[dlmf 1.8.E6_2]
theorem hasSum_fourierExpCoeff_mul_conj {f g : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioc (-π) π)))
    (hg : MemLp g 2 (volume.restrict (Ioc (-π) π))) :
    HasSum (fun n : ℤ => fourierExpCoeff f n * starRingEnd ℂ (fourierExpCoeff g n))
      ((1 / (2 * π) : ℂ) * ∫ x in (-π)..π, f x * starRingEnd ℂ (g x)) := by
  sorry

/-- DLMF 1.8.7: if `f` has period `2π` and `f^{(m)}` is piecewise continuous, then
`a_n, b_n, c_n = o(n^{-m})` as `n → ∞`. Special case: `f` is assumed `C^m` (so `f^{(m)}` is
continuous). -/
@[dlmf 1.8.E7]
theorem fourierCoeff_isLittleO {f : ℝ → ℂ} {m : ℕ} (hf : ContDiff ℝ m f)
    (hper : Function.Periodic f (2 * π)) :
    (fun n : ℕ => fourierCosCoeff f n) =o[atTop] (fun n : ℕ => ((n : ℝ) ^ m)⁻¹) ∧
    (fun n : ℕ => fourierSinCoeff f n) =o[atTop] (fun n : ℕ => ((n : ℝ) ^ m)⁻¹) ∧
    (fun n : ℕ => fourierExpCoeff f n) =o[atTop] (fun n : ℕ => ((n : ℝ) ^ m)⁻¹) := by
  sorry

/-- DLMF §1.8(i) (uniqueness of Fourier series): continuous `2π`-periodic functions with the
same Fourier coefficients `a_n`, `b_n` are equal. -/
@[dlmf 1.8.i]
theorem eq_of_fourierCoeff_eq {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hfp : Function.Periodic f (2 * π)) (hgp : Function.Periodic g (2 * π))
    (ha : ∀ n, fourierCosCoeff f n = fourierCosCoeff g n)
    (hb : ∀ n, fourierSinCoeff f n = fourierSinCoeff g n) : f = g := by
  sorry

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

/-- DLMF 1.8.11: let `f` be absolutely integrable of period `2π` and continuous except at
finitely many points of every bounded interval. At a point `x` where `f` has one-sided limits
`f(x-)`, `f(x+)` and one-sided derivatives (difference quotients
`(f(x+h) - f(x∓))/h → f'_∓` as `h → 0∓`), the Fourier series 1.8.1 converges to
`½f(x-) + ½f(x+)`. Convergence is of the partial sums. -/
@[dlmf 1.8.E11]
theorem tendsto_fourierPartialSum_of_oneSidedDeriv {f : ℝ → ℂ}
    (hf : IntervalIntegrable f volume (-π) π) (hper : Function.Periodic f (2 * π))
    (hfin : ∀ R : ℝ, {x ∈ Icc (-R) R | ¬ ContinuousAt f x}.Finite)
    {x : ℝ} {fL fR dL dR : ℂ}
    (hL : Tendsto (fun h : ℝ => (f (x + h) - fL) / h) (𝓝[<] 0) (𝓝 dL))
    (hR : Tendsto (fun h : ℝ => (f (x + h) - fR) / h) (𝓝[>] 0) (𝓝 dR)) :
    Tendsto (fun N : ℕ => fourierCosCoeff f 0 / 2 + ∑ n ∈ Finset.range N,
        (fourierCosCoeff f (n + 1) * (Real.cos ((n + 1 : ℕ) * x) : ℂ) +
          fourierSinCoeff f (n + 1) * (Real.sin ((n + 1 : ℕ) * x) : ℂ)))
      atTop (𝓝 (fL / 2 + fR / 2)) := by
  sorry

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

/-- DLMF §1.8(iii): for a `2π`-periodic `f ∈ C²`, the term-by-term derivative of the Fourier
series, `∑_{n ≥ 1} n(b_n cos nx - a_n sin nx)`, converges at every point to `f'(x)`. -/
@[dlmf 1.8.iii]
theorem tendsto_deriv_fourierSeries {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hper : Function.Periodic f (2 * π)) (x : ℝ) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, ((n + 1 : ℕ) : ℂ) *
        (fourierSinCoeff f (n + 1) * (Real.cos ((n + 1 : ℕ) * x) : ℂ) -
          fourierCosCoeff f (n + 1) * (Real.sin ((n + 1 : ℕ) * x) : ℂ)))
      atTop (𝓝 (deriv f x)) := by
  sorry

/-! ## §1.8(iv) Poisson's summation formula -/

/-- DLMF 1.8.14 (Poisson's summation formula): if `f` is twice continuously differentiable and
`f` and `f''` are integrable over `ℝ`, then
`∑_{n ∈ ℤ} f(x + n) = ∑_{n ∈ ℤ} e^{2πinx} ∫_{-∞}^{∞} f(t) e^{-2πint} dt`; both series converge
(absolutely) to a common value. Mathlib's `Real.tsum_eq_tsum_fourier_of_rpow_decay` proves the
formula under decay hypotheses on `f` and its Fourier transform instead. -/
@[dlmf 1.8.E14]
theorem poissonSummation {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hi : Integrable f)
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
  sorry

end DLMF.AlgebraicAnalytic
