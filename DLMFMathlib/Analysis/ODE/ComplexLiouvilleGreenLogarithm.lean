/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.ODE.ComplexLiouvilleGreenExpansion
public import Mathlib.RingTheory.PowerSeries.Log

/-!
# Logarithmic and derivative Liouville–Green coefficients

The exponential coefficients are extracted from Mathlib's actual formal
`PowerSeries.logOf`, so their integration constants are tied to the selected
linear coefficient series. No analytic convergence of the formal series is
assumed. Source: Olver, *Asymptotics and Special Functions*, Chapter 10,
§2, pp. 364–366.
-/

@[expose] public noncomputable section

open Set
open scoped Real BigOperators

namespace Complex

/-- Every formal-log coefficient is analytic in the phase variable on its
coefficient domain. Olver, Chapter 10, §2, pp. 365–366. -/
theorem analyticOnNhd_liouvilleGreen_logarithmic_coefficient
    {ψ : ℂ → ℂ} {A : ℕ → ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D)
    (hA : IsComplexLiouvilleGreenCoefficientSequence ψ A D) (n : ℕ) :
    AnalyticOnNhd ℂ (fun z => PowerSeries.coeff n
      (PowerSeries.logOf (PowerSeries.mk fun k => A k z))) D := by
  sorry

/-- The exact differential recurrence for the exponential coefficients,
with constants fixed by the formal logarithm of the selected A-series.
Olver, Chapter 10, §2, pp. 365–366. -/
theorem liouvilleGreen_logarithmic_coefficient_recurrence
    {ψ : ℂ → ℂ} {A : ℕ → ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D)
    (hA : IsComplexLiouvilleGreenCoefficientSequence ψ A D) :
    let E := fun n z => PowerSeries.coeff n
      (PowerSeries.logOf (PowerSeries.mk fun k => A k z))
    (∀ z ∈ D, E 0 z = 0 ∧ deriv (E 1) z = ψ z / 2) ∧
      ∀ n z, z ∈ D → deriv (E (n + 2)) z =
        -(deriv (deriv (E (n + 1))) z +
          ∑ j ∈ Finset.Icc 1 n, deriv (E j) z * deriv (E (n + 1 - j)) z) / 2 := by
  sorry

/-- The derivative coefficients are `B_0=1` and `B_s=A_s+A_(s-1)'`.
The explicit final term makes this an exact finite-sum identity, rather than a
formal claim with a dropped highest derivative. Olver, Chapter 10, §2,
pp. 364–365. -/
theorem deriv_liouvilleGreenPartialSum
    {ψ : ℂ → ℂ} {A : ℕ → ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D)
    (hA : IsComplexLiouvilleGreenCoefficientSequence ψ A D) {u : ℂ} (hu : u ≠ 0)
    {N : ℕ} (hN : 1 ≤ N) {z : ℂ} (hz : z ∈ D) :
    deriv (liouvilleGreenPartialSum A u N) z / u = exp (u * z) *
      ((∑ n ∈ Finset.range N, (if n = 0 then 1 else A n z + deriv (A (n - 1)) z) / u ^ n) +
        deriv (A (N - 1)) z / u ^ N) := by
  sorry

end Complex
