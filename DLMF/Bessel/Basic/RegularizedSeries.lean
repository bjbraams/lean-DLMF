/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Bessel
public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Tactic.CrossRefAttribute
public import DLMFMathlib.Analysis.Analytic.OfScalarsDeriv

/-!
# The regularized series `₀F̃₁`

Mathlib's regularized hypergeometric function `₀F̃₁(;c;w) = ∑ wⁿ / (n! Γ(c+n))` is entire in
`w` for every complex parameter `c`, including the nonpositive integers. This file collects the
basic calculus of this series, which underlies the Bessel functions (DLMF §10.2), the modified
Bessel functions (DLMF §10.25) and the Airy functions (DLMF §9.4).

## Main results

* `besselJ_eq_regularized`: `J_ν(z) = (z/2)^ν ₀F̃₁(;ν+1;-z²/4)` (DLMF 10.2.2).
* `hasFPowerSeriesOnBall_regularized0F1`, `analyticAt_regularized0F1`,
  `hasSum_regularized0F1`, `regularized0F1_eq_tsum`: the series is entire.
* `deriv_regularized0F1`, `hasDerivAt_regularized0F1`: differentiation raises the parameter.
* `regularized0F1_contiguous`: `₀F̃₁(;c;w) = c ₀F̃₁(;c+1;w) + w ₀F̃₁(;c+2;w)`.
* `regularized0F1_ode`: the differential equation `w F'' + c F' - F = 0`.
* `regularized0F1_conj`: for real `c` the series commutes with complex conjugation.

## Implementation notes

All statements hold at every parameter, since the regularized coefficients
`1 / (n! Γ(c+n))` need no exclusion of poles.
-/

@[expose] public section

open Complex FormalMultilinearSeries
open scoped Real Nat Topology ENNReal ComplexConjugate

noncomputable section

namespace DLMF.Bessel

/-! ### The regularized series -/

/-- Mathlib's Bessel function of the first kind `Complex.besselJ` as the regularized series
`J_ν(z) = (z/2)^ν ₀F̃₁(;ν+1;-z²/4)`, the normal form used in this project. -/
@[dlmf 10.2.E2]
theorem besselJ_eq_regularized (ν z : ℂ) :
    besselJ ν z = (z / 2) ^ ν * regularizedHGFun (∅ : Multiset ℂ) {ν + 1} (-(z ^ 2 / 4)) := by
  rw [besselJ, Multiset.empty_eq_zero, div_pow]
  norm_num

/-- Identity under the stated parameter and domain assumptions: `regularizedHGFunCoeff (∅ :
Multiset ℂ) {c} n = 1 / (n ! * Gamma (c + n))`. -/
theorem regularizedHGFunCoeff_empty (c : ℂ) (n : ℕ) :
    regularizedHGFunCoeff (∅ : Multiset ℂ) {c} n = 1 / (n ! * Gamma (c + n)) := by
  simp [regularizedHGFunCoeff]

/-- The regularized `₀F₁` series is entire, including nonpositive integer parameters. -/
theorem hasFPowerSeriesOnBall_regularized0F1 (c : ℂ) :
    HasFPowerSeriesOnBall (regularizedHGFun (∅ : Multiset ℂ) {c})
      (FormalMultilinearSeries.ofScalars ℂ (regularizedHGFunCoeff ∅ {c})) 0 ⊤ := by
  have hr : (regularizedHGFunSeries ∅ {c}).radius = ⊤ :=
    radius_regularizedHGFunSeries_eq_top (by simp)
  change HasFPowerSeriesOnBall (regularizedHGFunSeries ∅ {c}).sum
    (regularizedHGFunSeries ∅ {c}) 0 ⊤
  simpa only [hr] using (regularizedHGFunSeries ∅ {c}).hasFPowerSeriesOnBall
    (by rw [hr]; simp)

/-- The function `(regularizedHGFun (∅ : Multiset ℂ) {c})` is analytic over `ℂ` at `z`. -/
theorem analyticAt_regularized0F1 (c z : ℂ) :
    AnalyticAt ℂ (regularizedHGFun (∅ : Multiset ℂ) {c}) z :=
  (hasFPowerSeriesOnBall_regularized0F1 c).analyticAt_of_mem (by simp)

/-- The Maclaurin series of the regularized `₀F₁`, valid on all of `ℂ`. -/
theorem hasSum_regularized0F1 (c w : ℂ) :
    HasSum (fun n => regularizedHGFunCoeff (∅ : Multiset ℂ) {c} n * w ^ n)
      (regularizedHGFun (∅ : Multiset ℂ) {c} w) :=
  HasFPowerSeriesOnBall.hasSum_mul_pow (hasFPowerSeriesOnBall_regularized0F1 c) (by simp)

/-- The reciprocal Gamma recurrence avoids restrictions on the parameter. -/
theorem regularized0F1_coeff_recurrence (c : ℂ) (n : ℕ) :
    (n + 1 : ℂ) * (c + n) * regularizedHGFunCoeff ∅ {c} (n + 1) =
      regularizedHGFunCoeff ∅ {c} n := by
  simp only [regularizedHGFunCoeff_empty, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one, one_div, mul_inv_rev]
  rw [show c + (n + 1) = (c + n) + 1 by ring,
    one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (c + n)]
  field [Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)]

/-- Differentiating regularized `₀F₁` raises its parameter by one. -/
theorem deriv_regularized0F1 (c w : ℂ) :
    deriv (regularizedHGFun (∅ : Multiset ℂ) {c}) w = regularizedHGFun ∅ {c + 1} w := by
  have hd := (hasFPowerSeriesOnBall_regularized0F1 c).deriv_ofScalars.hasSum_mul_pow
    (z := w) (by simp)
  have he (n : ℕ) : (n + 1 : ℂ) * regularizedHGFunCoeff ∅ {c} (n + 1) =
      regularizedHGFunCoeff ∅ {c + 1} n := by
    simp only [regularizedHGFunCoeff_empty, Nat.factorial_succ, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one, one_div, mul_inv_rev]
    rw [show c + (n + 1) = c + 1 + n by ring]
    field [Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)]
  simp_rw [he] at hd
  exact hd.unique (hasSum_regularized0F1 (c + 1) w)

/-- At `w`, the function `(regularizedHGFun (∅ : Multiset ℂ) {c})` has derivative
`(regularizedHGFun ∅ {c + 1} w)`. -/
theorem hasDerivAt_regularized0F1 (c w : ℂ) :
    HasDerivAt (regularizedHGFun (∅ : Multiset ℂ) {c}) (regularizedHGFun ∅ {c + 1} w) w := by
  rw [← deriv_regularized0F1]
  exact (analyticAt_regularized0F1 c w).differentiableAt.hasDerivAt

/-- A contiguous relation valid even at the exceptional integer parameters. -/
theorem regularized0F1_contiguous (c w : ℂ) :
    regularizedHGFun (∅ : Multiset ℂ) {c} w =
      c * regularizedHGFun ∅ {c + 1} w + w * regularizedHGFun ∅ {c + 1 + 1} w := by
  have hf := hasFPowerSeriesOnBall_regularized0F1 (c + 1)
  have hs := ((hf.hasSum_mul_pow (z := w) (by simp)).mul_left c).add
    (hf.hasSum_z_mul_deriv (z := w) (by simp))
  have he (n : ℕ) : regularizedHGFunCoeff ∅ {c} n =
      (c + n) * regularizedHGFunCoeff ∅ {c + 1} n := by
    simp only [regularizedHGFunCoeff_empty, one_div, mul_inv_rev]
    rw [one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (c + n),
      show c + n + 1 = c + 1 + n by ring]
    ring
  have ht : HasSum (fun n => regularizedHGFunCoeff ∅ {c} n * w ^ n)
      (c * regularizedHGFun ∅ {c + 1} w + w * deriv (regularizedHGFun ∅ {c + 1}) w) := by
    convert! hs using 1
    funext n
    rw [he]
    ring
  rw [deriv_regularized0F1] at ht
  exact (hasSum_regularized0F1 c w).unique ht

/-- The differential equation for regularized `₀F₁`. -/
theorem regularized0F1_ode (c w : ℂ) :
    w * deriv (deriv (regularizedHGFun (∅ : Multiset ℂ) {c})) w +
      c * deriv (regularizedHGFun ∅ {c}) w - regularizedHGFun ∅ {c} w = 0 := by
  have h2 : deriv (deriv (regularizedHGFun (∅ : Multiset ℂ) {c})) w =
      regularizedHGFun ∅ {c + 1 + 1} w := by
    rw [funext (deriv_regularized0F1 c), deriv_regularized0F1]
  rw [h2, deriv_regularized0F1, regularized0F1_contiguous c w]
  ring

/-- Identity under the stated parameter and domain assumptions: `regularizedHGFun (∅ : Multiset ℂ)
{c} w = ∑' n : ℕ, w ^ n / n ! * (Gamma (c + n))⁻¹`. -/
theorem regularized0F1_eq_tsum (c w : ℂ) :
    regularizedHGFun (∅ : Multiset ℂ) {c} w = ∑' n : ℕ, w ^ n / n ! * (Gamma (c + n))⁻¹ := by
  rw [(hasSum_regularized0F1 c w).tsum_eq.symm]
  congr 1; funext n
  rw [regularizedHGFunCoeff_empty]; field_simp

/-- Summability of the indicated series: `Summable fun n : ℕ => w ^ n / n ! * (Gamma (c + n))⁻¹`. -/
theorem summable_regularized0F1_term (c w : ℂ) :
    Summable fun n : ℕ => w ^ n / n ! * (Gamma (c + n))⁻¹ := by
  have h := hasSum_regularized0F1 c w
  refine h.summable.congr fun n => ?_
  rw [regularizedHGFunCoeff_empty]; field_simp

/-- `₀F̃₁(c; ·)` with real parameter commutes with complex conjugation. -/
theorem regularized0F1_conj (c : ℝ) (w : ℂ) :
    regularizedHGFun (∅ : Multiset ℂ) {(c : ℂ)} (conj w) =
      conj (regularizedHGFun (∅ : Multiset ℂ) {(c : ℂ)} w) := by
  rw [regularized0F1_eq_tsum, regularized0F1_eq_tsum, Complex.conj_tsum]
  refine tsum_congr fun n => ?_
  simp only [map_mul, map_div₀, map_pow, map_inv₀, map_natCast, ← Complex.Gamma_conj, map_add,
    conj_ofReal]

end DLMF.Bessel
