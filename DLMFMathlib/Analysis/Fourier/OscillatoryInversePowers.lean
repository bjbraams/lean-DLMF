/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Fourier.ImproperConvergence
public import DLMFMathlib.Analysis.MellinOscillation
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic

/-!
# Uniform improper Fourier limits for oscillatory inverse powers

Oscillation may give uniformly convergent improper Fourier integrals even when the
amplitude's derivative is not absolutely integrable. Modulated inverse powers provide
a class closed under differentiation on the positive axis.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Complex Polynomial
open scoped Topology

namespace Complex

/-- Existence of an improper Fourier integral, uniformly on the indicated frequency set. -/
def HasUniformFourierLimit (q : ℝ → ℂ) (a : ℝ) (S : Set ℝ) : Prop :=
  ∃ L : ℝ → ℂ, TendstoUniformlyOn
    (fun (T x : ℝ) => ∫ t in a..T, exp (I * x * t) * q t) L atTop S

/-- Equality of amplitudes on the integration half-line preserves uniform Fourier limits. -/
theorem HasUniformFourierLimit.congr {q r : ℝ → ℂ} {a : ℝ} {S : Set ℝ}
    (hq : HasUniformFourierLimit q a S) (he : EqOn r q (Ici a)) :
    HasUniformFourierLimit r a S := by
  obtain ⟨L, hL⟩ := hq
  refine ⟨L, hL.congr ?_⟩
  filter_upwards [eventually_ge_atTop a] with T hT x _
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hT] at ht
  change exp (I * x * t) * q t = exp (I * x * t) * r t
  rw [he ht.1]

/-- Uniform Fourier limits are closed under constant multiplication. -/
theorem HasUniformFourierLimit.const_mul {q : ℝ → ℂ} {a : ℝ} {S : Set ℝ}
    (hq : HasUniformFourierLimit q a S) (c : ℂ) :
    HasUniformFourierLimit (fun t => c * q t) a S := by
  obtain ⟨L, hL⟩ := hq
  have h := ((ContinuousLinearMap.mul ℂ ℂ) c).uniformContinuous.comp_tendstoUniformlyOn hL
  refine ⟨fun x => c * L x, h.congr ?_⟩
  filter_upwards [] with T x _
  change c * (∫ t in a..T, exp (I * x * t) * q t) =
    ∫ t in a..T, exp (I * x * t) * (c * q t)
  rw [← intervalIntegral.integral_const_mul]
  congr 1
  funext t
  ring

/-- Adding continuous amplitudes adds their uniform improper Fourier limits. -/
theorem HasUniformFourierLimit.add {q r : ℝ → ℂ} {a : ℝ} {S : Set ℝ}
    (hq : HasUniformFourierLimit q a S) (hr : HasUniformFourierLimit r a S)
    (hqc : ContinuousOn q (Ici a)) (hrc : ContinuousOn r (Ici a)) :
    HasUniformFourierLimit (fun t => q t + r t) a S := by
  obtain ⟨L, hL⟩ := hq
  obtain ⟨M, hM⟩ := hr
  refine ⟨fun x => L x + M x, (hL.add hM).congr ?_⟩
  filter_upwards [eventually_ge_atTop a] with T hT x _
  have hqI : IntervalIntegrable (fun t : ℝ => exp (I * x * t) * q t) volume a T :=
    ((by fun_prop : ContinuousOn (fun t : ℝ => exp (I * x * t)) (Icc a T)).mul
      (hqc.mono Icc_subset_Ici_self)).intervalIntegrable_of_Icc hT
  have hrI : IntervalIntegrable (fun t : ℝ => exp (I * x * t) * r t) volume a T :=
    ((by fun_prop : ContinuousOn (fun t : ℝ => exp (I * x * t)) (Icc a T)).mul
      (hrc.mono Icc_subset_Ici_self)).intervalIntegrable_of_Icc hT
  simp only [Pi.add_apply, mul_add]
  exact (intervalIntegral.integral_add hqI hrI).symm

/-- A positive inverse power has a uniformly convergent Fourier integral away from zero
frequency, by an absolutely integrable derivative. -/
theorem hasUniformFourierLimit_cpow_neg {s : ℝ} (hs : 0 < s) :
    HasUniformFourierLimit (fun t : ℝ => (t : ℂ) ^ (-(s : ℂ))) 1 {x : ℝ | 1 ≤ |x|} := by
  let q : ℝ → ℂ := fun t => (t : ℂ) ^ (-(s : ℂ))
  let q' : ℝ → ℂ := fun t => -(s : ℂ) * (t : ℂ) ^ (-(s : ℂ) - 1)
  have hcont (w : ℂ) : ContinuousOn (fun t : ℝ => (t : ℂ) ^ w) (Ici 1) :=
    fun t ht => (continuousAt_ofReal_cpow_const _ _
      (Or.inr (by linarith [show 1 ≤ t from ht] : t ≠ 0))).continuousWithinAt
  have hd (t : ℝ) (ht : t ∈ Ici 1) : HasDerivWithinAt q (q' t) (Ici 1) t := by
    have h := ((hasDerivAt_id (t : ℂ)).cpow_const (c := -(s : ℂ))
      (Or.inl (by simp; linarith [show 1 ≤ t from ht] : 0 < (t : ℂ).re))).comp_ofReal
    simpa only [q, q', id_eq, mul_one] using h.hasDerivWithinAt
  have hzero : Tendsto q atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (tendsto_rpow_neg_atTop hs)
    filter_upwards [eventually_gt_atTop 0] with t ht
    change ‖(t : ℂ) ^ (-(s : ℂ))‖ ≤ t ^ (-s)
    rw [norm_cpow_eq_rpow_re_of_pos ht]
    simp
  have hi : IntegrableOn q' (Ioi 1) := by
    have h := (integrableOn_cpow_mul_exp_I (w := -(s : ℂ)) (by simp; linarith) 0).const_mul
      (-(s : ℂ))
    simpa only [q', ofReal_zero, mul_zero, zero_mul, exp_zero, mul_one, IntegrableOn] using! h
  exact ⟨_, tendstoUniformlyOn_integral_exp_mul_of_integrable_deriv
    (hcont _) (continuousOn_const.mul (hcont _)) hd hzero hi⟩

/-- A modulation by frequency at most one shifts the uniform Fourier limit to all
frequencies at least two. -/
theorem hasUniformFourierLimit_exp_mul_cpow_neg {s κ : ℝ} (hs : 0 < s) (hκ : |κ| ≤ 1) :
    HasUniformFourierLimit (fun t : ℝ => exp (I * κ * t) * (t : ℂ) ^ (-(s : ℂ))) 1 (Ici 2) := by
  obtain ⟨L, hL⟩ := hasUniformFourierLimit_cpow_neg hs
  have hsub : Ici (2 : ℝ) ⊆ (fun x : ℝ => x + κ) ⁻¹' {x : ℝ | 1 ≤ |x|} := by
    intro x hx
    change 1 ≤ |x + κ|
    have hk := (abs_le.mp hκ).1
    exact (by linarith [show 2 ≤ x from hx] : 1 ≤ x + κ).trans (le_abs_self _)
  have h := (hL.comp (fun x : ℝ => x + κ)).mono hsub
  refine ⟨L ∘ (fun x : ℝ => x + κ), h.congr ?_⟩
  filter_upwards [] with T x _
  apply intervalIntegral.integral_congr
  intro t _
  simp only [Function.comp_def, ofReal_add]
  rw [show I * ((x : ℂ) + κ) * t = I * x * t + I * κ * t by ring, exp_add]
  ring

namespace FourierInversePowers

/-- An exponential of real frequency times an inverse power polynomial on `t > 0`.
Its leading inverse factor is `t⁻¹`; polynomial coefficients have no normalization factors. -/
def amplitude (κ : ℝ) (P : Polynomial ℂ) (t : ℝ) : ℂ :=
  exp (I * κ * t) * (t : ℂ)⁻¹ * P.eval ((t : ℂ)⁻¹)

/-- Differentiating an inverse power polynomial amplitude acts by
`P ↦ (iκ-X)P-X²P'` on its polynomial. -/
def derivativePolynomial (κ : ℝ) (P : Polynomial ℂ) : Polynomial ℂ :=
  (C (I * κ) - X) * P - X ^ 2 * derivative P

/-- The polynomial for the `n`th derivative of `exp(iκt)/t` on the positive half-line. -/
def iteratedDerivativePolynomial (κ : ℝ) : ℕ → Polynomial ℂ
  | 0 => 1
  | n + 1 => derivativePolynomial κ (iteratedDerivativePolynomial κ n)

/-- The derivative of an oscillatory inverse power amplitude is given by its polynomial
recurrence at every nonzero real argument. -/
theorem hasDerivAt_amplitude (κ : ℝ) (P : Polynomial ℂ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (amplitude κ P) (amplitude κ (derivativePolynomial κ P) t) t := by
  have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht
  have hi := (hasDerivAt_id (t : ℂ)).inv ht'
  have he := ((hasDerivAt_id (t : ℂ)).const_mul (I * κ)).cexp
  have hp := (P.hasDerivAt ((t : ℂ)⁻¹)).comp (t : ℂ) hi
  convert ((he.mul hi).mul hp).comp_ofReal using 1
  · rfl
  · simp only [amplitude, derivativePolynomial, eval_sub, eval_mul, eval_C, eval_X, eval_pow,
      id_eq, mul_one, one_mul, Pi.inv_apply, Pi.mul_apply, Function.comp_def]
    field_simp [ht']
    <;> ring

/-- Oscillatory inverse power amplitudes are continuous on the integration half-line. -/
theorem continuousOn_amplitude (κ : ℝ) (P : Polynomial ℂ) :
    ContinuousOn (amplitude κ P) (Ici 1) := fun t ht =>
  (hasDerivAt_amplitude κ P (by linarith [show 1 ≤ t from ht])).continuousAt.continuousWithinAt

/-- Every inverse power polynomial amplitude has a uniformly convergent improper Fourier
integral for all frequencies at least two, when its modulation frequency has norm at most one. -/
theorem hasUniformFourierLimit_amplitude {κ : ℝ} (hκ : |κ| ≤ 1) (P : Polynomial ℂ) :
    HasUniformFourierLimit (amplitude κ P) 1 (Ici 2) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      apply (hP.add hQ (continuousOn_amplitude κ P) (continuousOn_amplitude κ Q)).congr
      intro t ht
      simp only [amplitude, eval_add]
      ring
  | monomial n c =>
      have h := (hasUniformFourierLimit_exp_mul_cpow_neg
        (s := (n : ℝ) + 1) (by positivity) hκ).const_mul c
      apply h.congr
      intro t ht
      simp only [amplitude, eval_monomial, ofReal_add, ofReal_natCast, ofReal_one,
        ← Nat.cast_add_one, cpow_neg, cpow_natCast, pow_succ, mul_assoc, ← inv_pow]
      ring

/-- Iterated derivatives on the half-line obey the same inverse power polynomial
recurrence; the one-sided derivative at the endpoint is included. -/
theorem iteratedDerivWithin_amplitude_one (κ : ℝ) (n : ℕ) :
    EqOn (iteratedDerivWithin n (amplitude κ 1) (Ici 1))
      (amplitude κ (iteratedDerivativePolynomial κ n)) (Ici 1) := by
  induction n with
  | zero => intro t ht; simp [iteratedDerivativePolynomial]
  | succ n ih =>
      intro t ht
      rw [iteratedDerivWithin_succ]
      have hd := (hasDerivAt_amplitude κ (iteratedDerivativePolynomial κ n)
        (by linarith [show 1 ≤ t from ht])).hasDerivWithinAt (s := Ici 1)
      have hd' := hd.congr_of_mem (fun x hx => ih hx) ht
      simpa only [iteratedDerivativePolynomial] using
        hd'.derivWithin (uniqueDiffOn_Ici (1 : ℝ) t ht)

/-- All derivatives of `exp(iκt)/t` have uniformly convergent improper Fourier integrals
for frequencies at least two when `|κ| ≤ 1`. -/
theorem hasUniformFourierLimit_iteratedDerivWithin_amplitude_one {κ : ℝ} (hκ : |κ| ≤ 1)
    (n : ℕ) :
    HasUniformFourierLimit (iteratedDerivWithin n (amplitude κ 1) (Ici 1)) 1 (Ici 2) :=
  (hasUniformFourierLimit_amplitude hκ (iteratedDerivativePolynomial κ n)).congr
    (iteratedDerivWithin_amplitude_one κ n)

/-- The derivatives of `sin(t)/t` are differences of two inverse power polynomial
amplitudes, including the one-sided derivatives at one. -/
theorem iteratedDerivWithin_sin_div (n : ℕ) :
    EqOn (iteratedDerivWithin n (fun t : ℝ => sin t / t) (Ici 1))
      (fun t : ℝ => (amplitude 1 (iteratedDerivativePolynomial 1 n) t -
        amplitude (-1) (iteratedDerivativePolynomial (-1) n) t) / (2 * I)) (Ici 1) := by
  induction n with
  | zero =>
      intro t ht
      simp only [iteratedDerivWithin_zero, iteratedDerivativePolynomial, amplitude,
        eval_one, mul_one, ofReal_one, ofReal_neg]
      rw [Complex.sin]
      have he₁ : -(t : ℂ) * I = I * -1 * t := by ring
      have he₂ : (t : ℂ) * I = I * 1 * t := by ring
      rw [he₁, he₂]
      field_simp
      ring_nf
      simp [I_sq]
  | succ n ih =>
      intro t ht
      rw [iteratedDerivWithin_succ]
      have ht0 : t ≠ 0 := by linarith [show 1 ≤ t from ht]
      have hd := ((hasDerivAt_amplitude 1 (iteratedDerivativePolynomial 1 n) ht0).sub
        (hasDerivAt_amplitude (-1) (iteratedDerivativePolynomial (-1) n) ht0)).div_const (2 * I)
      have hd' := hd.hasDerivWithinAt (s := Ici 1) |>.congr_of_mem (fun x hx => ih hx) ht
      simpa only [iteratedDerivativePolynomial] using
        hd'.derivWithin (uniqueDiffOn_Ici (1 : ℝ) t ht)

/-- Every derivative of `sin(t)/t` has a uniformly convergent improper Fourier integral
for frequencies at least two. This convergence is conditional already for its first derivative. -/
theorem hasUniformFourierLimit_iteratedDerivWithin_sin_div (n : ℕ) :
    HasUniformFourierLimit (iteratedDerivWithin n (fun t : ℝ => sin t / t) (Ici 1)) 1 (Ici 2) := by
  have hp := hasUniformFourierLimit_amplitude (κ := 1) (by norm_num)
    (iteratedDerivativePolynomial 1 n)
  have hm := (hasUniformFourierLimit_amplitude (κ := -1) (by norm_num)
    (iteratedDerivativePolynomial (-1) n)).const_mul (-1)
  have h := (hp.add hm (continuousOn_amplitude _ _)
    (continuousOn_const.mul (continuousOn_amplitude _ _))).const_mul ((2 * I)⁻¹)
  apply h.congr
  intro t ht
  rw [iteratedDerivWithin_sin_div n ht]
  ring

end FourierInversePowers

end Complex
