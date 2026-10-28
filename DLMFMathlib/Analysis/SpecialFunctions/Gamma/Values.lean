/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
public import DLMFMathlib.Analysis.Complex.BarnesResidue

/-!
# Values and basic identities of the complex Gamma function

* `Complex.Gamma_one_half_eq_sqrt`: `Γ(1/2) = √π`, with the real square root;
* `Complex.Gamma_one_half_sub_nat_mul_factorial`: `Γ(1/2 - s) (2s)! = (-4)^s s! √π`;
* `Complex.pi_mul_inv_Gamma_mul_inv_Gamma_one_sub`: `π / (Γ(s) Γ(1-s)) = sin (π s)`
  for every `s`, including the poles;
* `Complex.analyticAt_Gamma`: `Γ` is analytic off the nonpositive integers;
* the everywhere convergent series of the regularized `₀F₁`.
-/

@[expose] public section
open scoped Real Nat

namespace Complex

/-- `Γ(1/2) = √π`, written with the real square root. -/
theorem Gamma_one_half_eq_sqrt : Gamma (1 / 2 : ℂ) = (Real.sqrt π : ℂ) := by
  rw [Complex.Gamma_one_half_eq, Real.sqrt_eq_rpow, Complex.ofReal_cpow Real.pi_pos.le]
  norm_num

/-- `Γ(1/2 - s) (2s)! = (-4)^s s! √π` for natural `s`. -/
theorem Gamma_one_half_sub_nat_mul_factorial (s : ℕ) :
    Gamma (1 / 2 - s) * ((2 * s).factorial : ℂ) = (-4 : ℂ) ^ s * s.factorial * Real.sqrt π := by
  induction s with
  | zero => simpa using Gamma_one_half_eq_sqrt
  | succ s ih =>
    have h1 : Gamma (1 / 2 - s) =
        (1 / 2 - ((s + 1 : ℕ) : ℂ)) * Gamma (1 / 2 - ((s + 1 : ℕ) : ℂ)) := by
      rw [← Gamma_add_one]
      · push_cast; ring_nf
      · intro h
        have := congrArg Complex.re h
        simp at this
        linarith
    rw [h1] at ih
    rw [show 2 * (s + 1) = 2 * s + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ,
      Nat.factorial_succ]
    push_cast at ih ⊢
    linear_combination (-2 * (2 * (s : ℂ) + 2)) * ih

/-- The reflection formula for reciprocals, valid at every `s`:
`π · Γ(s)⁻¹ Γ(1-s)⁻¹ = sin (π s)`. -/
theorem pi_mul_inv_Gamma_mul_inv_Gamma_one_sub (s : ℂ) :
    (π : ℂ) * ((Gamma s)⁻¹ * (Gamma (1 - s))⁻¹) = sin (π * s) := by
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [← mul_inv, Gamma_mul_Gamma_one_sub, inv_div]
  field_simp

/-- `Γ` is complex analytic at every point that is not a nonpositive integer. -/
theorem analyticAt_Gamma {s : ℂ} (hs : ∀ m : ℕ, s ≠ -(m : ℂ)) : AnalyticAt ℂ Gamma s := by
  have hU : IsOpen {s : ℂ | ∀ m : ℕ, s ≠ -m} := by
    simpa using barnesRes_isOpen_ne_sub_nat (0 : ℂ)
  exact DifferentiableOn.analyticAt
    (fun w hw => (differentiableAt_Gamma w hw).differentiableWithinAt) (hU.mem_nhds hs)

/-- The regularized `₀F₁(;c;w)` is the everywhere convergent series
`∑ wᵏ / (k! Γ(c + k))`. -/
theorem hasSum_regularizedHGFun_empty_singleton (c w : ℂ) :
    HasSum (fun k : ℕ => w ^ k / (k ! * Gamma (c + k))) (regularizedHGFun ∅ {c} w) := by
  have hr : (regularizedHGFunSeries (∅ : Multiset ℂ) {c}).radius = ⊤ :=
    radius_regularizedHGFunSeries_eq_top (by simp)
  have hp : HasFPowerSeriesOnBall (regularizedHGFun ∅ {c})
      (regularizedHGFunSeries (∅ : Multiset ℂ) {c}) 0 ⊤ := by
    rw [← hr]
    exact (regularizedHGFunSeries (∅ : Multiset ℂ) {c}).hasFPowerSeriesOnBall (by rw [hr]; simp)
  convert hp.hasSum (y := w) (by simp) using 1
  · funext k
    simp [regularizedHGFunSeries, regularizedHGFunCoeff]
    ring
  · simp

end Complex
