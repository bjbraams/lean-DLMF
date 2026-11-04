/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.Basic
public import DLMF.Legendre.Basic.Properties

public import DLMF.Hypergeometric.ArgumentContinuation
public import DLMF.OrthogonalPolynomials.Classical

/-!
# Legendre functions of the first kind at integer degree (Temme §§8.1–8.2, DLMF §14.7)

The basic properties of `P_ν(z) = F(-ν, ν+1; 1; (1-z)/2)` (the value at `1`, the reflection
`P_{-ν-1} = P_ν`, the derivatives and Legendre's equation) are in
`DLMF.Legendre.Basic.Properties`.

## Main results

* `legendreP_nat`: at integer degree `P_n` is the Legendre polynomial (DLMF 14.7.1 with
  `μ = 0`).
-/

@[expose] public section

open Complex Filter Set DLMF.Hypergeometric
open scoped Topology
open DLMF.OrthogonalPolynomials

noncomputable section

namespace DLMF.Legendre

/-- For `n ∈ ℕ`, `P_n` is the Legendre polynomial (DLMF 14.7.1 with `μ = 0`). -/
theorem legendreP_nat (n : ℕ) {z : ℂ} (hz : 1 + z ∈ slitPlane) :
    legendreP n z = legendrePolynomialP n z := by
  have h1 : ∀ k : ℕ, (1 : ℂ) ≠ -(k : ℂ) := fun k h => by
    have := congrArg re h; simp at this; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  have hpoly : AnalyticOnNhd ℂ (fun w => ₂F₁ (-(n : ℂ)) ((n : ℂ) + 1) 1 w) cutPlane := by
    intro w _
    simp_rw [ordinaryHypergeometric_eq_sum_neg_nat]
    fun_prop
  have heq := regularizedGaussHypergeometric_unique hpoly (fun w hw => by
    rw [regularizedGaussHypergeometricFun_eq_div_Gamma h1, Gamma_one, div_one])
  rw [legendreP, ← heq (mem_cutPlane_of_one_add hz), legendrePolynomialP, jacobiPolynomialP]
  simp only [zero_add, add_zero, pochhammer_nat_one]
  rw [div_self (Nat.cast_ne_zero.mpr n.factorial_ne_zero), one_mul]

end DLMF.Legendre

end
