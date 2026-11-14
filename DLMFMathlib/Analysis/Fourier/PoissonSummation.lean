/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Fourier.PoissonSummation
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import TauCeti.Analysis.Sobolev.WeakDeriv.Interval
import DLMFMathlib.Analysis.Calculus.IntegrableDerivatives
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.PSeries
import Mathlib.Tactic

/-!
# Poisson summation from integrable derivatives

For a `C²` function on the line, integrability of the function and its second derivative
implies absolute Poisson summation. The first derivative is integrable by an integral
Taylor remainder. The `W^{1,1}` bound controls integer translates on each unit interval;
finite integer covers give normal convergence on compact sets. Quadratic Fourier decay
makes the Fourier lattice series absolutely convergent.

The proof uses TauCeti's `HasWeakLineDerivOn.norm_le_setAverage_add_integral` and classical
weak-derivative bridge, Mathlib's `Real.one_add_sq_mul_norm_fourier_le`, and its general
`Real.tsum_eq_tsum_fourier`. No upstream proof body is copied.

* `ContDiff.summable_norm_restrict_comp_add_int`: normal convergence of translates.
* `ContDiff.summable_fourier_int_of_integrable_iteratedDeriv_two`: Fourier summability.
* `Real.hasSum_poisson_of_integrable_iteratedDeriv_two`: Poisson summation.
-/

public noncomputable section

open MeasureTheory Set Filter TopologicalSpace AddCircle
open scoped Topology FourierTransform

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
/-- The value of a `C¹` function on a unit interval is bounded by its `W^{1,1}` norm. -/
lemma ContDiff.norm_le_integral_norm_add_integral_norm_deriv_unit {f : ℝ → F}
    (hf : ContDiff ℝ 1 f) (a : ℝ) {x : ℝ} (hx : x ∈ Icc a (a + 1)) :
    ‖f x‖ ≤ (∫ t in Ioo a (a + 1), ‖f t‖) + ∫ t in Ioo a (a + 1), ‖deriv f t‖ := by
  have hline (t : ℝ) : HasLineDerivAt ℝ f (deriv f t) t (1 : ℝ) := by
    simpa only [fderiv_apply_one_eq_deriv] using
      (hf.differentiable one_ne_zero t).hasFDerivAt.hasLineDerivAt (1 : ℝ)
  have hw := TauCeti.hasWeakLineDerivOn_of_hasLineDerivAt
    (μ := (volume : Measure ℝ)) (Ω := ⟨Ioo a (a + 1), isOpen_Ioo⟩)
    (hf.continuous.locallyIntegrable.locallyIntegrableOn _)
    ((hf.continuous_deriv le_rfl).locallyIntegrable.locallyIntegrableOn _)
    (fun t _ => hline t)
  have h := hw.norm_le_setAverage_add_integral (by linarith : a < a + 1)
    (((hf.continuous_deriv le_rfl).integrableOn_Icc).mono_set Ioo_subset_Icc_self)
    hf.continuous.continuousOn ae_eq_rfl hx
  have hlen : volume.real (Ioo a (a + 1)) = 1 := by simp [Measure.real]
  rw [setAverage_eq, hlen, inv_one, one_smul] at h
  exact h

/-- Integer translates of an integrable `C¹` function with integrable derivative converge
normally on a unit interval. -/
lemma ContDiff.summable_norm_restrict_comp_add_int_unit {f : ℝ → F}
    (hf : ContDiff ℝ 1 f) (hi : Integrable f) (hi' : Integrable (deriv f)) :
    Summable (fun n : ℤ =>
      ‖((⟨f, hf.continuous⟩ : C(ℝ, F)).comp (ContinuousMap.addRight (n : ℝ))).restrict
        (⟨Icc (0 : ℝ) 1, isCompact_Icc⟩ : Compacts ℝ)‖) := by
  let B : ℝ → ℝ := fun t => ‖f t‖ + ‖deriv f t‖
  have hB : Integrable B := hi.norm.add hi'.norm
  have hs := hB.hasSum_intervalIntegral_comp_add_int.summable
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) _ hs
  intro n
  have he : (∫ t : ℝ in (0 : ℝ)..1, B (t + n)) =
      (∫ t in Ioo (n : ℝ) (n + 1), ‖f t‖) +
        ∫ t in Ioo (n : ℝ) (n + 1), ‖deriv f t‖ := by
    rw [intervalIntegral.integral_comp_add_right]
    simp only [zero_add, add_comm 1 (n : ℝ)]
    rw [intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo]
    exact integral_add hi.norm.integrableOn hi'.norm.integrableOn
  rw [he]
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro x
  exact hf.norm_le_integral_norm_add_integral_norm_deriv_unit (n : ℝ)
    ⟨by dsimp; linarith [x.property.1], by dsimp; linarith [x.property.2]⟩

/-- Integer translates of an integrable `C¹` function with integrable derivative converge
normally on every compact subset of the real line. -/
lemma ContDiff.summable_norm_restrict_comp_add_int {f : ℝ → F}
    (hf : ContDiff ℝ 1 f) (hi : Integrable f) (hi' : Integrable (deriv f))
    (K : Compacts ℝ) :
    Summable (fun n : ℤ =>
      ‖((⟨f, hf.continuous⟩ : C(ℝ, F)).comp (ContinuousMap.addRight (n : ℝ))).restrict K‖) := by
  let fC : C(ℝ, F) := ⟨f, hf.continuous⟩
  let U : ℤ → ℝ := fun n =>
    ‖(fC.comp (ContinuousMap.addRight (n : ℝ))).restrict
      (⟨Icc (0 : ℝ) 1, isCompact_Icc⟩ : Compacts ℝ)‖
  have hU : Summable U := hf.summable_norm_restrict_comp_add_int_unit hi hi'
  obtain ⟨a, ha⟩ := K.isCompact.bddBelow
  obtain ⟨b, hb⟩ := K.isCompact.bddAbove
  let J : Finset ℤ := Finset.Icc (Int.floor a) (Int.floor b)
  have hS : Summable (fun n : ℤ => ∑ j ∈ J, U (n + j)) := by
    apply summable_sum
    intro j _
    exact (Equiv.addRight j).summable_iff.mpr hU
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) _ hS
  intro n
  apply (ContinuousMap.norm_le _ (Finset.sum_nonneg (fun j _ => norm_nonneg _))).mpr
  intro x
  let j : ℤ := Int.floor (x : ℝ)
  have hj : j ∈ J := Finset.mem_Icc.mpr ⟨Int.floor_mono (ha x.property),
    Int.floor_mono (hb x.property)⟩
  have hy : (x : ℝ) - (j : ℝ) ∈ Icc (0 : ℝ) 1 := by
    refine ⟨sub_nonneg.mpr (Int.floor_le (x : ℝ)), ?_⟩
    have h := Int.lt_floor_add_one (x : ℝ)
    dsimp only [j]
    linarith
  have hpt : ‖f ((x : ℝ) + n)‖ ≤ U (n + j) := by
    have h := ContinuousMap.norm_coe_le_norm
      ((fC.comp (ContinuousMap.addRight ((n + j : ℤ) : ℝ))).restrict
        (⟨Icc (0 : ℝ) 1, isCompact_Icc⟩ : Compacts ℝ)) ⟨(x : ℝ) - j, hy⟩
    convert h using 1
    congr 2
    simp only [ContinuousMap.coe_addRight]
    push_cast
    ring
  have hsingle : U (n + j) ≤ ∑ k ∈ J, U (n + k) :=
    Finset.single_le_sum (fun k _ => show 0 ≤ U (n + k) from norm_nonneg _) hj
  exact hpt.trans hsingle
/-- The Fourier values at integer frequencies of a `C²` function are absolutely summable
if its value and second derivative are integrable. -/
lemma ContDiff.summable_fourier_int_of_integrable_iteratedDeriv_two
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {f : ℝ → E} (hf : ContDiff ℝ 2 f) (hi : Integrable f)
    (hi2 : Integrable (iteratedDeriv 2 f)) : Summable (fun n : ℤ => 𝓕 f (n : ℝ)) := by
  have hi1 := hf.integrable_deriv_of_integrable_iteratedDeriv_two hi hi2
  have hj : ∀ k ≤ 2, Integrable (iteratedDeriv k f) := by
    intro k hk
    interval_cases k
    · simpa using hi
    · simpa using hi1
    · exact hi2
  let C := (∫ v, ‖f v‖) + (4 * Real.pi ^ 2)⁻¹ * ∫ v, ‖iteratedDeriv 2 f v‖
  have hbig : Asymptotics.IsBigO Filter.cofinite (fun n : ℤ => 𝓕 f (n : ℝ))
      (fun n : ℤ => |(n : ℝ)| ^ (-(2 : ℝ))) := by
    apply Asymptotics.IsBigO.of_bound C
    filter_upwards [Filter.eventually_cofinite_ne (0 : ℤ)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have hpos : 0 < (n : ℝ) ^ 2 := sq_pos_of_ne_zero hn0
    have h := Real.one_add_sq_mul_norm_fourier_le hf hj (n : ℝ)
    have hb : ‖𝓕 f (n : ℝ)‖ ≤ C / (n : ℝ) ^ 2 := by
      apply (le_div_iff₀ hpos).mpr
      dsimp only [C] at h ⊢
      nlinarith [norm_nonneg (𝓕 f (n : ℝ))]
    simpa only [Real.rpow_neg (abs_nonneg _), Real.rpow_two, sq_abs, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (sq_nonneg (n : ℝ))), div_eq_mul_inv] using hb
  exact summable_of_isBigO (Real.summable_abs_int_rpow (by norm_num : (1 : ℝ) < 2)) hbig
/-- Poisson summation for a `C²` function with integrable value and second derivative.
Both lattice series converge absolutely to the same value. -/
lemma Real.hasSum_poisson_of_integrable_iteratedDeriv_two {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hi : Integrable f)
    (hi2 : Integrable (iteratedDeriv 2 f)) (x : ℝ) :
    ∃ s : ℂ, HasSum (fun n : ℤ => f (x + n)) s ∧
      HasSum (fun n : ℤ => Complex.exp (2 * Real.pi * Complex.I * n * x) *
        ∫ t, f t * Complex.exp (-(2 * Real.pi * Complex.I * n * t))) s := by
  have hi1 := hf.integrable_deriv_of_integrable_iteratedDeriv_two hi hi2
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hN := hf1.summable_norm_restrict_comp_add_int hi hi1
  have hF := hf.summable_fourier_int_of_integrable_iteratedDeriv_two hi hi2
  have hs := ContinuousMap.summable_of_locally_summable_norm hN
  have hs1 : Summable (fun n : ℤ => f (x + n)) :=
    (ContinuousMap.hasSum_apply hs.hasSum x).summable
  have he : (∑' n : ℤ, f (x + n)) =
      ∑' n : ℤ, 𝓕 f (n : ℝ) * fourier n (x : UnitAddCircle) := by
    simpa only [ContinuousMap.coe_mk] using Real.tsum_eq_tsum_fourier hN hF x
  have hn : Summable (fun n : ℤ => 𝓕 f (n : ℝ) * fourier n (x : UnitAddCircle)) := by
    apply Summable.of_norm
    simpa only [norm_mul, fourier_apply, Circle.norm_coe, mul_one] using hF.norm
  have hterm (n : ℤ) : 𝓕 f (n : ℝ) * fourier n (x : UnitAddCircle) =
      Complex.exp (2 * Real.pi * Complex.I * n * x) *
        ∫ t, f t * Complex.exp (-(2 * Real.pi * Complex.I * n * t)) := by
    rw [fourier_coe_apply, Real.fourier_eq']
    simp only [Complex.ofReal_one, div_one, smul_eq_mul]
    rw [mul_comm]
    congr 1
    apply integral_congr_ae
    exact Eventually.of_forall fun t => by
      rw [mul_comm]
      simp only [Real.inner_apply]
      push_cast
      ring_nf
  refine ⟨∑' n : ℤ, f (x + n), hs1.hasSum, ?_⟩
  rw [he]
  exact hn.hasSum.congr_fun (fun n => (hterm n).symm)
