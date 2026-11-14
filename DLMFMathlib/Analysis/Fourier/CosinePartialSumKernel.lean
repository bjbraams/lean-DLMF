/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
# The cosine kernel of Fourier partial sums

The kernel `1/2 + ∑_{n=1}^N cos(nu)` is half the usual Dirichlet kernel. Its sine quotient,
evenness, periodicity and half-period integral give the elementary Fourier partial-sum API.
-/

public noncomputable section

open MeasureTheory
open scoped Real

namespace Real

/-- The Dirichlet kernel `½ + ∑_{n=1}^N cos(nu)` of the Fourier partial sums. -/
@[expose] def cosinePartialSumKernel (N : ℕ) (u : ℝ) : ℝ :=
  1 / 2 + ∑ n ∈ Finset.range N, Real.cos ((n + 1 : ℕ) * u)

/-- The defining finite cosine sum. -/
lemma cosinePartialSumKernel_def (N : ℕ) (u : ℝ) :
    cosinePartialSumKernel N u =
      1 / 2 + ∑ n ∈ Finset.range N, Real.cos ((n + 1 : ℕ) * u) := rfl

/-- The kernel with no positive-frequency terms is the constant one half. -/
@[simp] lemma cosinePartialSumKernel_zero (u : ℝ) : cosinePartialSumKernel 0 u = 1 / 2 := by
  simp [cosinePartialSumKernel]

/-- Adding one frequency adds its cosine. -/
lemma cosinePartialSumKernel_succ (N : ℕ) (u : ℝ) :
    cosinePartialSumKernel (N + 1) u =
      cosinePartialSumKernel N u + Real.cos ((N + 1 : ℕ) * u) := by
  simp only [cosinePartialSumKernel, Finset.sum_range_succ, add_assoc]

/-- Multiplication by twice the half-angle sine gives the finite-sum sine quotient. -/
lemma two_mul_sin_mul_cosinePartialSumKernel (N : ℕ) (u : ℝ) :
    2 * Real.sin (u / 2) * cosinePartialSumKernel N u = Real.sin ((N + 1 / 2) * u) := by
  induction N with
  | zero => simp [cosinePartialSumKernel]; ring_nf
  | succ N ih =>
    have h := Real.sin_sub_sin (((N + 1 : ℕ) + 1 / 2) * u) ((N + 1 / 2) * u)
    simp only [cosinePartialSumKernel, Finset.sum_range_succ] at ih ⊢
    have h1 : (((N + 1 : ℕ) : ℝ) + 1 / 2) * u - (N + 1 / 2) * u = 2 * (u / 2) := by
      push_cast; ring
    have h2 : (((N + 1 : ℕ) : ℝ) + 1 / 2) * u + (N + 1 / 2) * u = 2 * (((N + 1 : ℕ) : ℝ) * u) := by
      push_cast; ring
    rw [h1, h2] at h
    simp only [mul_div_cancel_left₀ _ (two_ne_zero' ℝ)] at h
    push_cast at h ih ⊢
    linear_combination ih - h

/-- The cosine kernel is even. -/
lemma cosinePartialSumKernel_neg (N : ℕ) (u : ℝ) :
    cosinePartialSumKernel N (-u) = cosinePartialSumKernel N u := by
  simp [cosinePartialSumKernel, mul_neg, Real.cos_neg]

/-- The cosine kernel has period two pi. -/
lemma cosinePartialSumKernel_add_two_pi (N : ℕ) (u : ℝ) :
    cosinePartialSumKernel N (u + 2 * π) = cosinePartialSumKernel N u := by
  simp only [cosinePartialSumKernel]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [mul_add, Real.cos_add_nat_mul_two_pi]

/-- The finite cosine kernel is continuous. -/
@[fun_prop] lemma continuous_cosinePartialSumKernel (N : ℕ) :
    Continuous (cosinePartialSumKernel N) := by
  unfold cosinePartialSumKernel; fun_prop

/-- The integral over a half period is pi over two. -/
lemma integral_cosinePartialSumKernel (N : ℕ) :
    ∫ u in (0 : ℝ)..π, cosinePartialSumKernel N u = π / 2 := by
  have hc : ∀ n : ℕ, ∫ u in (0 : ℝ)..π, Real.cos ((n + 1 : ℕ) * u) = 0 := by
    intro n
    have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    rw [intervalIntegral.integral_comp_mul_left (fun u => Real.cos u) hn, integral_cos]
    simp only [mul_zero, Real.sin_zero, sub_zero]
    rw [Real.sin_nat_mul_pi, smul_zero]
  simp only [cosinePartialSumKernel]
  rw [intervalIntegral.integral_add intervalIntegrable_const
      ((by fun_prop : Continuous fun u : ℝ => ∑ n ∈ Finset.range N,
        Real.cos ((n + 1 : ℕ) * u)).intervalIntegrable _ _),
    intervalIntegral.integral_finsetSum fun n _ =>
      (by fun_prop : Continuous fun u => Real.cos ((n + 1 : ℕ) * u)).intervalIntegrable _ _]
  simp only [hc, Finset.sum_const_zero, intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- Integration against the shifted cosine kernel is the finite cosine-sine Fourier sum,
for real or complex integrable data on an arbitrary interval. -/
lemma integral_mul_cosinePartialSumKernel_eq {K : Type*} [RCLike K] {g : ℝ → K} {a b : ℝ}
    (hg : IntervalIntegrable g volume a b) (x : ℝ) (N : ℕ) :
    (∫ t in a..b, g t * (cosinePartialSumKernel N (t - x) : K)) =
      (1 / 2 : K) * (∫ t in a..b, g t) + ∑ n ∈ Finset.range N,
        ((cos ((n + 1 : ℕ) * x) : K) *
          (∫ t in a..b, g t * (cos ((n + 1 : ℕ) * t) : K)) +
        (sin ((n + 1 : ℕ) * x) : K) *
          (∫ t in a..b, g t * (sin ((n + 1 : ℕ) * t) : K))) := by
  have hI : ∀ h : ℝ → ℝ, Continuous h →
      IntervalIntegrable (fun t => g t * (h t : K)) volume a b := fun h hh =>
    hg.mul_continuousOn (RCLike.continuous_ofReal.comp hh).continuousOn
  have hterm : ∀ n : ℕ, ∫ t in a..b, g t * (Real.cos ((n + 1 : ℕ) * (t - x)) : K) =
      (Real.cos ((n + 1 : ℕ) * x) : K) *
        (∫ t in a..b, g t * (Real.cos ((n + 1 : ℕ) * t) : K)) +
      (Real.sin ((n + 1 : ℕ) * x) : K) *
        ∫ t in a..b, g t * (Real.sin ((n + 1 : ℕ) * t) : K) := by
    intro n
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add
        ((hI (fun t => Real.cos ((n + 1 : ℕ) * t)) (by fun_prop)).const_mul _)
        ((hI (fun t => Real.sin ((n + 1 : ℕ) * t)) (by fun_prop)).const_mul _)]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [mul_sub, Real.cos_sub]
    push_cast; ring
  have hsplit : ∫ t in a..b, g t * (cosinePartialSumKernel N (t - x) : K) =
      (∫ t in a..b, g t * ((1 / 2 : ℝ) : K)) + ∑ n ∈ Finset.range N,
        ∫ t in a..b, g t * (Real.cos ((n + 1 : ℕ) * (t - x)) : K) := by
    have hS : ∀ n ∈ Finset.range N, IntervalIntegrable
        (fun t => g t * (Real.cos ((n + 1 : ℕ) * (t - x)) : K)) volume a b :=
      fun n _ => hI (fun t => Real.cos ((n + 1 : ℕ) * (t - x))) (by fun_prop)
    have hS' : IntervalIntegrable (fun t => ∑ n ∈ Finset.range N,
        g t * (Real.cos ((n + 1 : ℕ) * (t - x)) : K)) volume a b := by
      simpa only [Finset.sum_fn] using IntervalIntegrable.sum _ hS
    rw [← intervalIntegral.integral_finsetSum hS,
      ← intervalIntegral.integral_add (hI _ continuous_const) hS']
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [cosinePartialSumKernel_def]; push_cast
    rw [mul_add, Finset.mul_sum]
  rw [hsplit, intervalIntegral.integral_mul_const, mul_comm]
  simp_rw [hterm]
  push_cast
  rfl

end Real
