/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic

/-!
# Integrability of intermediate derivatives

A `C²` function and its second derivative in `L¹(ℝ)` have first derivative in `L¹(ℝ)`.
Taylor's formula with a unit increment expresses the first derivative using translates
of the function and convolution of its second derivative with a compact triangular kernel.
The target may be any complete real normed vector space.

The proof uses Mathlib's integral Taylor remainder and integrability of convolution.

* `ContDiff.deriv_eq_sub_sub_integral_iteratedDeriv_two`: the unit-increment remainder.
* `ContDiff.integrable_deriv_of_integrable_iteratedDeriv_two`: intermediate integrability.
-/

public noncomputable section

open MeasureTheory Set Filter
open scoped Topology Convolution

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
/-- The first derivative is a unit increment minus the second-order integral remainder. -/
lemma ContDiff.deriv_eq_sub_sub_integral_iteratedDeriv_two {f : ℝ → F}
    (hf : ContDiff ℝ 2 f) (x : ℝ) :
    deriv f x = f (x + 1) - f x -
      ∫ t : ℝ in (0 : ℝ)..1, (1 - t) • iteratedDeriv 2 f (x + t) := by
  have h := map_add_eq_sum_add_integral_iteratedFDeriv (n := 1) (x := x) (y := (1 : ℝ))
    (fun t _ => hf.contDiffAt)
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
    Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, inv_one, one_smul,
    iteratedFDeriv_zero_apply, iteratedFDeriv_one_apply, fderiv_apply_one_eq_deriv,
    pow_one, smul_eq_mul, mul_one] at h
  apply eq_sub_iff_add_eq.mpr
  apply eq_sub_iff_add_eq.mpr
  calc
    _ = f x + deriv f x +
        ∫ t : ℝ in (0 : ℝ)..1, (1 - t) • iteratedDeriv 2 f (x + t) := by abel
    _ = f (x + 1) := by simpa only [iteratedDeriv_eq_iteratedFDeriv] using h.symm

/-- A `C²` function with integrable value and second derivative has integrable first derivative. -/
lemma ContDiff.integrable_deriv_of_integrable_iteratedDeriv_two {f : ℝ → F}
    (hf : ContDiff ℝ 2 f) (hi : Integrable f) (hi2 : Integrable (iteratedDeriv 2 f)) :
    Integrable (deriv f) := by
  let k : ℝ → ℝ := (Ioc (0 : ℝ) 1).indicator (fun t => 1 - t)
  have hk : Integrable k :=
    (integrable_indicator_iff measurableSet_Ioc).mpr
      ((continuous_const.sub continuous_id).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
  let R : ℝ → F := fun x => ∫ t : ℝ in (0 : ℝ)..1,
    (1 - t) • iteratedDeriv 2 f (x + t)
  have hR : Integrable R := by
    have h := (hk.integrable_convolution (L := ContinuousLinearMap.lsmul ℝ ℝ) hi2.comp_neg).comp_neg
    convert h using 1
    funext x
    rw [convolution_def]
    dsimp only [R, k, ContinuousLinearMap.lsmul_apply]
    rw [intervalIntegral.integral_of_le zero_le_one, ← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    exact Eventually.of_forall fun t => by
      by_cases ht : t ∈ Ioc (0 : ℝ) 1 <;> simp [ht, add_comm]
  have he : deriv f = fun x => f (x + 1) - f x - R x :=
    funext hf.deriv_eq_sub_sub_integral_iteratedDeriv_two
  rw [he]
  exact ((hi.comp_add_right 1).sub hi).sub hR
