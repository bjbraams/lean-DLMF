/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Elementary.Basic.LambertW
public import DLMF.Gamma.Asymptotics
public import DLMFMathlib.Analysis.Complex.LagrangeBurmann

/-!
# Expansion coefficients and leading asymptotics of the Lambert W function

The coefficients of the branch-point, Puiseux and large-argument expansions of the Lambert W
function (DLMF §4.13), and the leading asymptotic of every branch at infinity.

## Main definitions

* `lambertXi`: the logarithmic sheet `log z + 2πik` of the branch asymptotics.
* `lambertC`, `lambertD`: coefficients of the branch-point and Puiseux expansions.
* `lambertWOver`: the removable quotient `W₀(z)/z`.
* `lambertAsymptoticTerm`: the terms of the large-argument expansion.

## Main results

* `lambertW_leading_asymptotic`: the leading asymptotic of every branch at infinity
  (DLMF 4.13.1_1).
-/

@[expose] public section

open Complex Filter Set Finset

open scoped Topology Real

noncomputable section

namespace DLMF.Elementary

/-- The logarithmic sheet used in the branch asymptotics. -/
def lambertXi (k : ℤ) (z : ℂ) : ℂ := Complex.log z + 2 * Real.pi * I * k

/-- Coefficients of the logarithmic square-root parameter at the branch point. -/
def lambertC (n : ℕ) : ℝ :=
  if h0 : n = 0 then 1 else if h1 : n = 1 then 1 else
    lambertC (n - 1) / (n + 1) - 1 / 2 *
      ∑ k : Fin (n - 2), lambertC (k.val + 2) * lambertC (n - 1 - k.val)
termination_by n
decreasing_by all_goals omega

/-- Coefficients in the principal Puiseux parameter at the branch point. -/
def lambertD (m : ℕ) : ℝ :=
  if h0 : m = 0 then -1 else if h1 : m = 1 then Real.sqrt 2 else
    (-2 * lambertD (m - 1) + (m - 1 : ℝ) / 2 *
      (∑ k : Fin (m - 2), lambertD (k.val + 1) * lambertD (m - 2 - k.val)) -
      (m + 1 : ℝ) / 2 *
      (∑ k : Fin (m - 2), lambertD (k.val + 2) * lambertD (m - 1 - k.val))) /
      ((m + 1 : ℝ) * Real.sqrt 2)
termination_by m
decreasing_by all_goals omega

/-- The normalized removable quotient `W₀(z)/z` at zero. -/
def lambertWOver (z : ℂ) : ℂ := if z = 0 then 1 else lambertW 0 z / z

/-- The exact nth outer term of the large-argument Lambert expansion. -/
def lambertAsymptoticTerm (k : ℤ) (z : ℂ) (n : ℕ) : ℂ :=
  (-1 : ℂ) ^ (n + 1) / lambertXi k z ^ (n + 1) *
    ∑ m ∈ range (n + 1), (Nat.stirlingFirst (n + 1) (n + 1 - m) : ℂ) *
      (-Complex.log (lambertXi k z)) ^ (m + 1) / (m + 1).factorial

/-- All integer branches have their normalized leading asymptotic at complex infinity. -/
@[dlmf 4.13.E1_1]
theorem lambertW_leading_asymptotic (k : ℤ) :
    Tendsto (fun z : ℂ => lambertW k z - lambertXi k z + Complex.log (lambertXi k z))
      (Bornology.cobounded ℂ) (𝓝 0) := by
  have hξ : Tendsto (lambertXi k) (Bornology.cobounded ℂ) (comap Complex.re atTop) := by
    rw [tendsto_comap_iff]
    refine (Real.tendsto_log_atTop.comp tendsto_norm_cobounded_atTop).congr fun z => ?_
    simp only [Function.comp, lambertXi]
    exact (re_log_add_two_pi_mul_I_mul k z).symm
  refine (tendsto_log_sub_log_lambertLogMapInv.comp hξ).congr' ?_
  filter_upwards [tendsto_norm_cobounded_atTop.eventually (eventually_gt_atTop 1)] with z hz
  have hW : lambertW k z = lambertLogMapInv (lambertXi k z) := by
    rw [lambertW_eq_lambertBranchValue, lambertBranchValue_of_one_lt_norm k hz, lambertXi]
  have hΩ : lambertXi k z ∈ lambertOmegaDomain := by
    left; rw [lambertXi, re_log_add_two_pi_mul_I_mul]; linarith [Real.log_pos hz]
  have hg := (lambertLogMapInv_spec hΩ).2
  rw [lambertLogMap] at hg
  simp only [Function.comp, hW]
  linear_combination -hg


end DLMF.Elementary
end
end
