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
# Jacobi amplitude as the inverse elliptic integral
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
theorem Real.incEllIntFm_add_pi {m : ℝ} (hm : m < 1) (φ : ℝ) :
    Real.incEllIntFm (φ + π) m = Real.incEllIntFm φ m + 2 * Real.compEllIntKm m := by
  unfold Real.incEllIntFm Real.compEllIntKm; exact integral_add_pi hm _ φ

/-- `E(φ + π|m) = E(φ|m) + 2E(m)` (DLMF §19.2(ii)). -/
theorem Real.incEllIntEm_add_pi {m : ℝ} (hm : m < 1) (φ : ℝ) :
    Real.incEllIntEm (φ + π) m = Real.incEllIntEm φ m + 2 * Real.compEllIntEm m := by
  unfold Real.incEllIntEm Real.compEllIntEm; exact integral_add_pi hm _ φ

/-- `F(π/2|m) = K(m)`. -/
theorem Real.incEllIntFm_pi_div_two (m : ℝ) :
    Real.incEllIntFm (π / 2) m = Real.compEllIntKm m := rfl

/-- `E(π/2|m) = E(m)`. -/
theorem Real.incEllIntEm_pi_div_two (m : ℝ) :
    Real.incEllIntEm (π / 2) m = Real.compEllIntEm m := rfl

/-- `F(-φ|m) = -F(φ|m)`. -/
theorem Real.incEllIntFm_neg (φ m : ℝ) : Real.incEllIntFm (-φ) m = -Real.incEllIntFm φ m := by
  have h : ∫ θ in (0 : ℝ)..(-φ), (1 - m * sin θ ^ 2) ^ (-(1 / 2) : ℝ) =
      ∫ θ in (0 : ℝ)..(-φ), (1 - m * sin (-θ) ^ 2) ^ (-(1 / 2) : ℝ) := by
    simp only [sin_neg, neg_sq]
  rw [Real.incEllIntFm, Real.incEllIntFm, h,
    intervalIntegral.integral_comp_neg (fun θ => (1 - m * sin θ ^ 2) ^ (-(1 / 2) : ℝ)), neg_neg,
    neg_zero,
    intervalIntegral.integral_symm]

/-- `F(φ|0) = φ`. -/
theorem Real.incEllIntFm_zero_param (φ : ℝ) : Real.incEllIntFm φ 0 = φ := by simp [Real.incEllIntFm]

/-- `∂F/∂φ = (1 - m sin²φ)^{-1/2}`. -/
theorem Real.hasDerivAt_incEllIntFm {m : ℝ} (hm : m < 1) (φ : ℝ) :
    HasDerivAt (fun φ => Real.incEllIntFm φ m) ((1 - m * sin φ ^ 2) ^ (-(1 / 2) : ℝ)) φ :=
  intervalIntegral.integral_hasDerivAt_right
    ((continuous_one_sub_mul_sin_sq_rpow hm _).intervalIntegrable _ _)
    ((continuous_one_sub_mul_sin_sq_rpow hm _).stronglyMeasurableAtFilter _ _)
    (continuous_one_sub_mul_sin_sq_rpow hm _).continuousAt

/-- `∂E/∂φ = (1 - m sin²φ)^{1/2}`. -/
theorem Real.hasDerivAt_incEllIntEm {m : ℝ} (hm : m < 1) (φ : ℝ) :
    HasDerivAt (fun φ => Real.incEllIntEm φ m) ((1 - m * sin φ ^ 2) ^ (1 / 2 : ℝ)) φ :=
  intervalIntegral.integral_hasDerivAt_right
    ((continuous_one_sub_mul_sin_sq_rpow hm _).intervalIntegrable _ _)
    ((continuous_one_sub_mul_sin_sq_rpow hm _).stronglyMeasurableAtFilter _ _)
    (continuous_one_sub_mul_sin_sq_rpow hm _).continuousAt

/-- `φ ↦ F(φ|m)` is strictly increasing for `m < 1`. -/
theorem Real.strictMono_incEllIntFm {m : ℝ} (hm : m < 1) : StrictMono fun φ => Real.incEllIntFm φ m :=
  strictMono_of_deriv_pos fun φ => by
    rw [(Real.hasDerivAt_incEllIntFm hm φ).deriv]
    exact rpow_pos_of_pos (one_sub_mul_sin_sq_pos hm φ) _

/-- `φ ↦ F(φ|m)` maps `ℝ` onto `ℝ` for `m < 1`. -/
theorem Real.surjective_incEllIntFm {m : ℝ} (hm : m < 1) :
    Function.Surjective fun φ => Real.incEllIntFm φ m := by
  have hcont : Continuous fun φ => Real.incEllIntFm φ m :=
    continuous_iff_continuousAt.mpr fun φ => (Real.hasDerivAt_incEllIntFm hm φ).continuousAt
  have hK : 0 < Real.compEllIntKm m := by
    rw [Real.compEllIntKm]
    exact intervalIntegral.intervalIntegral_pos_of_pos_on
      ((continuous_one_sub_mul_sin_sq_rpow hm _).intervalIntegrable _ _)
      (fun θ _ => rpow_pos_of_pos (one_sub_mul_sin_sq_pos hm θ) _) (by positivity)
  -- `F(nπ) = 2nK`
  have hnat : ∀ n : ℕ, Real.incEllIntFm (n * π) m = 2 * n * Real.compEllIntKm m := by
    intro n
    induction n with
    | zero => simp [Real.incEllIntFm]
    | succ n ih => push_cast; rw [add_mul, one_mul, Real.incEllIntFm_add_pi hm, ih]; ring
  have hmono := Real.strictMono_incEllIntFm hm
  refine hcont.surjective ?_ ?_
  · refine tendsto_atTop_atTop.mpr fun b => ?_
    obtain ⟨n, hn⟩ := exists_nat_gt (b / (2 * Real.compEllIntKm m))
    refine ⟨n * π, fun φ hφ => ?_⟩
    have := hmono.monotone hφ
    rw [hnat] at this
    rw [div_lt_iff₀ (by positivity)] at hn
    linarith
  · refine tendsto_atBot_atBot.mpr fun b => ?_
    obtain ⟨n, hn⟩ := exists_nat_gt (-b / (2 * Real.compEllIntKm m))
    refine ⟨-(n * π), fun φ hφ => ?_⟩
    have := hmono.monotone hφ
    rw [Real.incEllIntFm_neg, hnat] at this
    rw [div_lt_iff₀ (by positivity)] at hn
    linarith

/-- For `m < 1`, `φ ↦ F(φ|m)` as an order isomorphism of `ℝ`. -/
def Real.incEllIntFmOrderIso {m : ℝ} (hm : m < 1) : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective _ (Real.strictMono_incEllIntFm hm)
      (Real.surjective_incEllIntFm hm)

/-- Jacobi's amplitude `am(u|m)`, the inverse of `φ ↦ F(φ|m)` for `m < 1` (Temme (12.21),
DLMF §22.16(i)); it is set to `u` for `m ≥ 1`. -/
def Real.jacobiAmm (u m : ℝ) : ℝ := if h : m < 1 then (Real.incEllIntFmOrderIso h).symm u else u

/-- Jacobi's elliptic function `sn(u|m) = sin am(u|m)`. -/
def Real.jacobiSnm (u m : ℝ) : ℝ := sin (Real.jacobiAmm u m)

/-- Jacobi's elliptic function `cn(u|m) = cos am(u|m)`. -/
def Real.jacobiCnm (u m : ℝ) : ℝ := cos (Real.jacobiAmm u m)

/-- Jacobi's elliptic function `dn(u|m) = (1 - m sn²(u|m))^{1/2}` (DLMF 22.6.1). -/
def Real.jacobiDnm (u m : ℝ) : ℝ := (1 - m * Real.jacobiSnm u m ^ 2) ^ (1 / 2 : ℝ)

end DLMF.Elliptic
