/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bessel.Basic

/-!
# Modified Bessel functions (AAR §4.12)

`I_ν` is the `₀F₁` series with argument `+z²/4`. `K_ν` is the second-kind combination of
`I_ν` and `I_{-ν}`.
-/

@[expose] public section

open Complex MeasureTheory
open scoped Real Nat Topology

noncomputable section

namespace DLMF.Bessel

/-- Modified Bessel function of the first kind. -/
@[dlmf 10.25.E2]
def besselI (ν z : ℂ) : ℂ :=
  (z / 2) ^ ν * regularizedHGFun (∅ : Multiset ℂ) {ν + 1} (z ^ 2 / 4)

/-- Modified Bessel function of the second kind (Macdonald's `K_ν`), with integer
orders defined by their limits in the order parameter (AAR (4.12.3)). -/
@[dlmf 10.27.E4]
def besselK (ν z : ℂ) : ℂ := by
  classical
  exact if ∃ k : ℤ, ν = k then
    Filter.limUnder (𝓝[≠] ν) (fun μ =>
      π / 2 * (besselI (-μ) z - besselI μ z) / sin (μ * π))
  else π / 2 * (besselI (-ν) z - besselI ν z) / sin (ν * π)

theorem besselI_apply_zero {ν : ℂ} (hν : ν ≠ 0) : besselI ν 0 = 0 := by
  unfold besselI
  rw [zero_div, zero_cpow hν, zero_mul]

theorem besselI_zero_zero : besselI 0 0 = 1 := by
  unfold besselI
  rw [zero_div, cpow_zero, one_mul]
  have harg : (0 ^ 2 / 4 : ℂ) = 0 := by ring
  rw [harg, DLMF.Confluent.regularizedHGFun_zero, regularizedHGFunCoeff_empty]
  simp [Gamma_one]

/-- `I_ν(z) = i^{-ν} J_ν(i z)` (principal branch). -/
@[dlmf 10.27.E6]
theorem besselI_eq_besselJ {ν z : ℂ} (hz : z ≠ 0) (harg : z.arg ≤ π / 2) :
    besselI ν z = I ^ (-ν) * besselJ ν (I * z) := by
  have hz2 : z / 2 ≠ 0 := div_ne_zero hz (by norm_num)
  have harg2 : (z / 2).arg = z.arg := by
    simpa only [div_eq_mul_inv, ← ofReal_ofNat, ← ofReal_inv] using
      arg_mul_real (r := (2 : ℝ)⁻¹) (by norm_num) z
  have hlog : log (I * (z / 2)) = log I + log (z / 2) := by
    apply log_mul I_ne_zero hz2
    rw [arg_I, harg2]
    exact ⟨by linarith [neg_pi_lt_arg z, Real.pi_pos], by linarith⟩
  have hpow : (I * (z / 2)) ^ ν = I ^ ν * (z / 2) ^ ν := by
    rw [cpow_def_of_ne_zero (mul_ne_zero I_ne_zero hz2), hlog, add_mul, exp_add,
      ← cpow_def_of_ne_zero I_ne_zero, ← cpow_def_of_ne_zero hz2]
  have hsq : -((I * z) ^ 2 / 4) = z ^ 2 / 4 := by
    rw [mul_pow, I_sq]
    ring
  unfold besselI
  simp only [besselJ_eq_regularized]
  rw [hsq, show I * z / 2 = I * (z / 2) by ring, hpow, cpow_neg]
  field [(cpow_ne_zero_iff.mpr (Or.inl I_ne_zero) : I ^ ν ≠ 0)]

/-- Modified Bessel equation `z² y'' + z y' - (z² + ν²) y = 0`. -/
@[dlmf 10.25.E1]
theorem besselI_ode {ν z : ℂ} (hz : z ∈ slitPlane) :
    z ^ 2 * iteratedDeriv 2 (besselI ν) z + z * deriv (besselI ν) z -
      (z ^ 2 + ν ^ 2) * besselI ν z = 0 := by
  have he := besselSeries_ode ν 1 hz
  have hf : (fun w : ℂ => (w / 2) ^ ν * regularizedHGFun ∅ {ν + 1} (1 * w ^ 2 / 4)) =
      besselI ν := by funext w; simp only [besselI, one_mul]
  dsimp only at he
  rw [hf] at he
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero, besselI, one_mul] using he

/-- `I_ν` is analytic on the principal slit plane, for every order. -/
theorem analyticAt_besselI (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    AnalyticAt ℂ (besselI ν) z := by
  have he := analyticAt_besselSeries ν 1 hz
  have hf : (fun w : ℂ => (w / 2) ^ ν * regularizedHGFun ∅ {ν + 1} (1 * w ^ 2 / 4)) =
      besselI ν := by funext w; simp only [besselI, one_mul]
  rwa [hf] at he

@[dlmf 10.25.E1]
theorem besselK_ode {ν z : ℂ} (hz : z ∈ slitPlane) (hν : ∀ k : ℤ, ν ≠ k) :
    z ^ 2 * iteratedDeriv 2 (besselK ν) z + z * deriv (besselK ν) z -
      (z ^ 2 + ν ^ 2) * besselK ν z = 0 := by
  let a := -(π : ℂ) / (2 * sin (ν * π))
  let b := (π : ℂ) / (2 * sin (ν * π))
  have hf : besselK ν = (fun w => a * besselI ν w + b * besselI (-ν) w) := by
    funext w
    simp only [besselK, show ¬ ∃ k : ℤ, ν = k from not_exists.mpr hν, ↓reduceIte]
    dsimp [a, b]
    ring
  have hp := analyticAt_besselI ν hz
  have hn := analyticAt_besselI (-ν) hz
  rw [hf, iteratedDeriv_fun_add (contDiffAt_const.mul (hp.contDiffAt (n := 2)))
      (contDiffAt_const.mul (hn.contDiffAt (n := 2))),
    iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field,
    deriv_fun_add (hp.differentiableAt.const_mul a) (hn.differentiableAt.const_mul b),
    deriv_const_mul_field, deriv_const_mul_field]
  linear_combination a * besselI_ode (ν := ν) hz + b * besselI_ode (ν := -ν) hz

/-- Nicholson's integral for `J_ν² + Y_ν²` (AAR §4.13). -/
theorem nicholson_integral {ν : ℂ} {x : ℝ} (hx : 0 < x) :
    (besselJ ν x) ^ 2 + (besselY ν x) ^ 2 =
      (8 / (π ^ 2 : ℂ)) *
        ∫ t : ℝ in Set.Ioi (0 : ℝ),
          cosh (2 * ν * (t : ℂ)) * besselK 0 (2 * x * Real.sinh t : ℂ) := by
  sorry

end DLMF.Bessel
