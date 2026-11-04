/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Elliptic.Basic.Integrals
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Jacobi's amplitude and elliptic functions

This file proves the basic properties of the incomplete elliptic integrals in the amplitude and
defines Jacobi's amplitude as the inverse of `φ ↦ F(φ|m)`, together with `sn`, `cn` and `dn`.

## Main definitions

* `Real.incompleteEllipticFOfParameterOrderIso`: `φ ↦ F(φ|m)` as an order isomorphism of `ℝ`, for
  `m < 1`.
* `Real.jacobiAmOfParameter`: Jacobi's amplitude `am(u|m)` (Temme (12.21), DLMF §22.16(i)).
* `Real.jacobiSnOfParameter`, `Real.jacobiCnOfParameter`: `sn(u|m) = sin am(u|m)` and
  `cn(u|m) = cos am(u|m)`.
* `Real.jacobiDnOfParameter`: `dn(u|m) = (1 - m sn²(u|m))^{1/2}` (DLMF 22.6.1).

## Main results

* `Real.incompleteEllipticFOfParameter_add_pi`, `Real.incompleteEllipticEOfParameter_add_pi`:
  `F(φ + π|m) = F(φ|m) + 2K(m)` and `E(φ + π|m) = E(φ|m) + 2E(m)` (DLMF §19.2(ii)).
* `Real.incompleteEllipticFOfParameter_pi_div_two`,
  `Real.incompleteEllipticEOfParameter_pi_div_two`: `F(π/2|m) = K(m)` and `E(π/2|m) = E(m)`.
* `Real.incompleteEllipticFOfParameter_neg`, `Real.incompleteEllipticFOfParameter_zero_param`:
  oddness and `F(φ|0) = φ`.
* `Real.hasDerivAt_incompleteEllipticFOfParameter`,
  `Real.hasDerivAt_incompleteEllipticEOfParameter`: derivatives in `φ`.
* `Real.strictMono_incompleteEllipticFOfParameter`,
  `Real.surjective_incompleteEllipticFOfParameter`: `φ ↦ F(φ|m)` is a strictly increasing bijection
  of `ℝ` for `m < 1`.

## Implementation notes

For `m ≥ 1` the amplitude is set to `am(u|m) = u`.
-/

@[expose] public noncomputable section

open Real Set Filter
open scoped Topology

namespace DLMF.Elliptic

/-- The integrand `(1 - m sin²θ)^p` is `π`-periodic and even, so its integral over a period is
twice the integral over `[0, π/2]`. -/
theorem integral_period {m : ℝ} (hm : m < 1) (p : ℝ) :
    ∫ θ in (0 : ℝ)..π, (1 - m * sin θ ^ 2) ^ p =
      2 * ∫ θ in (0 : ℝ)..(π / 2), (1 - m * sin θ ^ 2) ^ p := by
  have hc := continuous_one_sub_mul_sin_sq_rpow hm p
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := π / 2)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have h := intervalIntegral.integral_comp_sub_left
    (fun θ => (1 - m * sin θ ^ 2) ^ p) (a := 0) (b := π / 2) π
  simp only [sin_pi_sub, sub_zero, show π - π / 2 = π / 2 by ring] at h
  rw [← h]; ring

/-- Quasi-periodicity of the incomplete integrals in the amplitude. -/
theorem integral_add_pi {m : ℝ} (hm : m < 1) (p φ : ℝ) :
    ∫ θ in (0 : ℝ)..(φ + π), (1 - m * sin θ ^ 2) ^ p =
      (∫ θ in (0 : ℝ)..φ, (1 - m * sin θ ^ 2) ^ p) +
        2 * ∫ θ in (0 : ℝ)..(π / 2), (1 - m * sin θ ^ 2) ^ p := by
  have hc := continuous_one_sub_mul_sin_sq_rpow hm p
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := π)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _), integral_period hm]
  have h := intervalIntegral.integral_comp_add_right
    (fun θ => (1 - m * sin θ ^ 2) ^ p) (a := 0) (b := φ) π
  simp only [sin_add_pi, neg_sq, zero_add] at h
  rw [← h, add_comm]

/-- `F(φ + π|m) = F(φ|m) + 2K(m)` (DLMF §19.2(ii)). -/
theorem Real.incompleteEllipticFOfParameter_add_pi {m : ℝ} (hm : m < 1) (φ : ℝ) :
    Real.incompleteEllipticFOfParameter (φ + π) m = Real.incompleteEllipticFOfParameter φ m + 2 *
        Real.completeEllipticKOfParameter m := by
  unfold Real.incompleteEllipticFOfParameter Real.completeEllipticKOfParameter;
      exact integral_add_pi hm _ φ

/-- `E(φ + π|m) = E(φ|m) + 2E(m)` (DLMF §19.2(ii)). -/
theorem Real.incompleteEllipticEOfParameter_add_pi {m : ℝ} (hm : m < 1) (φ : ℝ) :
    Real.incompleteEllipticEOfParameter (φ + π) m = Real.incompleteEllipticEOfParameter φ m + 2 *
        Real.completeEllipticEOfParameter m := by
  unfold Real.incompleteEllipticEOfParameter Real.completeEllipticEOfParameter;
      exact integral_add_pi hm _ φ

/-- `F(π/2|m) = K(m)`. -/
theorem Real.incompleteEllipticFOfParameter_pi_div_two (m : ℝ) :
    Real.incompleteEllipticFOfParameter (π / 2) m = Real.completeEllipticKOfParameter m := rfl

/-- `E(π/2|m) = E(m)`. -/
theorem Real.incompleteEllipticEOfParameter_pi_div_two (m : ℝ) :
    Real.incompleteEllipticEOfParameter (π / 2) m = Real.completeEllipticEOfParameter m := rfl

/-- `F(-φ|m) = -F(φ|m)`. -/
theorem Real.incompleteEllipticFOfParameter_neg (φ m : ℝ) : Real.incompleteEllipticFOfParameter (-φ)
    m = -Real.incompleteEllipticFOfParameter φ m := by
  have h : ∫ θ in (0 : ℝ)..(-φ), (1 - m * sin θ ^ 2) ^ (-(1 / 2) : ℝ) =
      ∫ θ in (0 : ℝ)..(-φ), (1 - m * sin (-θ) ^ 2) ^ (-(1 / 2) : ℝ) := by
    simp only [sin_neg, neg_sq]
  rw [Real.incompleteEllipticFOfParameter, Real.incompleteEllipticFOfParameter, h,
    intervalIntegral.integral_comp_neg (fun θ => (1 - m * sin θ ^ 2) ^ (-(1 / 2) : ℝ)), neg_neg,
    neg_zero,
    intervalIntegral.integral_symm]

/-- `F(φ|0) = φ`. -/
theorem Real.incompleteEllipticFOfParameter_zero_param (φ : ℝ) : Real.incompleteEllipticFOfParameter
    φ 0 = φ := by simp [Real.incompleteEllipticFOfParameter]

/-- `∂F/∂φ = (1 - m sin²φ)^{-1/2}`. -/
theorem Real.hasDerivAt_incompleteEllipticFOfParameter {m : ℝ} (hm : m < 1) (φ : ℝ) :
    HasDerivAt (fun φ => Real.incompleteEllipticFOfParameter φ m)
        ((1 - m * sin φ ^ 2) ^ (-(1 / 2) : ℝ)) φ :=
  intervalIntegral.integral_hasDerivAt_right
    ((continuous_one_sub_mul_sin_sq_rpow hm _).intervalIntegrable _ _)
    ((continuous_one_sub_mul_sin_sq_rpow hm _).stronglyMeasurableAtFilter _ _)
    (continuous_one_sub_mul_sin_sq_rpow hm _).continuousAt

/-- `∂E/∂φ = (1 - m sin²φ)^{1/2}`. -/
theorem Real.hasDerivAt_incompleteEllipticEOfParameter {m : ℝ} (hm : m < 1) (φ : ℝ) :
    HasDerivAt (fun φ => Real.incompleteEllipticEOfParameter φ m)
        ((1 - m * sin φ ^ 2) ^ (1 / 2 : ℝ)) φ :=
  intervalIntegral.integral_hasDerivAt_right
    ((continuous_one_sub_mul_sin_sq_rpow hm _).intervalIntegrable _ _)
    ((continuous_one_sub_mul_sin_sq_rpow hm _).stronglyMeasurableAtFilter _ _)
    (continuous_one_sub_mul_sin_sq_rpow hm _).continuousAt

/-- `φ ↦ F(φ|m)` is strictly increasing for `m < 1`. -/
theorem Real.strictMono_incompleteEllipticFOfParameter {m : ℝ} (hm : m < 1) : StrictMono fun φ =>
    Real.incompleteEllipticFOfParameter φ m :=
  strictMono_of_deriv_pos fun φ => by
    rw [(Real.hasDerivAt_incompleteEllipticFOfParameter hm φ).deriv]
    exact rpow_pos_of_pos (one_sub_mul_sin_sq_pos hm φ) _

/-- `φ ↦ F(φ|m)` maps `ℝ` onto `ℝ` for `m < 1`. -/
theorem Real.surjective_incompleteEllipticFOfParameter {m : ℝ} (hm : m < 1) :
    Function.Surjective fun φ => Real.incompleteEllipticFOfParameter φ m := by
  have hcont : Continuous fun φ => Real.incompleteEllipticFOfParameter φ m :=
    continuous_iff_continuousAt.mpr fun φ =>
        (Real.hasDerivAt_incompleteEllipticFOfParameter hm φ).continuousAt
  have hK : 0 < Real.completeEllipticKOfParameter m := by
    rw [Real.completeEllipticKOfParameter]
    exact intervalIntegral.intervalIntegral_pos_of_pos_on
      ((continuous_one_sub_mul_sin_sq_rpow hm _).intervalIntegrable _ _)
      (fun θ _ => rpow_pos_of_pos (one_sub_mul_sin_sq_pos hm θ) _) (by positivity)
  -- `F(nπ) = 2nK`
  have hnat : ∀ n : ℕ, Real.incompleteEllipticFOfParameter (n * π) m = 2 * n *
      Real.completeEllipticKOfParameter m := by
    intro n
    induction n with
    | zero => simp [Real.incompleteEllipticFOfParameter]
    | succ n ih => push_cast;
                   rw [add_mul, one_mul, Real.incompleteEllipticFOfParameter_add_pi hm, ih]; ring
  have hmono := Real.strictMono_incompleteEllipticFOfParameter hm
  refine hcont.surjective ?_ ?_
  · refine tendsto_atTop_atTop.mpr fun b => ?_
    obtain ⟨n, hn⟩ := exists_nat_gt (b / (2 * Real.completeEllipticKOfParameter m))
    refine ⟨n * π, fun φ hφ => ?_⟩
    have := hmono.monotone hφ
    rw [hnat] at this
    rw [div_lt_iff₀ (by positivity)] at hn
    linarith
  · refine tendsto_atBot_atBot.mpr fun b => ?_
    obtain ⟨n, hn⟩ := exists_nat_gt (-b / (2 * Real.completeEllipticKOfParameter m))
    refine ⟨-(n * π), fun φ hφ => ?_⟩
    have := hmono.monotone hφ
    rw [Real.incompleteEllipticFOfParameter_neg, hnat] at this
    rw [div_lt_iff₀ (by positivity)] at hn
    linarith

/-- For `m < 1`, `φ ↦ F(φ|m)` as an order isomorphism of `ℝ`. -/
def Real.incompleteEllipticFOfParameterOrderIso {m : ℝ} (hm : m < 1) : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective _ (Real.strictMono_incompleteEllipticFOfParameter hm)
      (Real.surjective_incompleteEllipticFOfParameter hm)

/-- Jacobi's amplitude `am(u|m)`, the inverse of `φ ↦ F(φ|m)` for `m < 1` (Temme (12.21),
DLMF §22.16(i)); it is set to `u` for `m ≥ 1`. -/
def Real.jacobiAmOfParameter (u m : ℝ) : ℝ := if h : m < 1 then
    (Real.incompleteEllipticFOfParameterOrderIso h).symm u else u

/-- Jacobi's elliptic function `sn(u|m) = sin am(u|m)`. -/
def Real.jacobiSnOfParameter (u m : ℝ) : ℝ := sin (Real.jacobiAmOfParameter u m)

/-- Jacobi's elliptic function `cn(u|m) = cos am(u|m)`. -/
def Real.jacobiCnOfParameter (u m : ℝ) : ℝ := cos (Real.jacobiAmOfParameter u m)

/-- Jacobi's elliptic function `dn(u|m) = (1 - m sn²(u|m))^{1/2}` (DLMF 22.6.1). -/
def Real.jacobiDnOfParameter (u m : ℝ) : ℝ :=
    (1 - m * Real.jacobiSnOfParameter u m ^ 2) ^ (1 / 2 : ℝ)

end DLMF.Elliptic
