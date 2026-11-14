/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bessel.Debye

/-!
# Real exponential Debye expansion for the ordinary Bessel function

Olver, *Asymptotics and Special Functions*, Chapter 4, §9,
pp. 130–134, synopsis O-4.12. The full expansion uses the same canonical
Debye polynomials as the modified-function expansions, evaluated at coth(alpha).
-/

@[expose] public noncomputable section

open Complex

namespace DLMF.Bessel

/-- The scaled-order ordinary Bessel expansion is uniform on compact positive hyperbolic
angles. Olver, Chapter 4, §9, synopsis O-4.12; DLMF 10.19.3. -/
theorem exists_uniform_besselJ_sech_debye_remainder {δ A : ℝ}
    (hδ : 0 < δ) (hA : δ ≤ A) (N : ℕ) :
    ∃ C R : ℝ, 0 < C ∧ 0 < R ∧ ∀ ν : ℝ, R ≤ ν → ∀ α ∈ Set.Icc δ A,
      ‖((Real.sqrt (2 * Real.pi * ν * Real.tanh α) *
          Real.exp (ν * (α - Real.tanh α)) : ℝ) : ℂ) *
        besselJ ν ((ν / Real.cosh α : ℝ) : ℂ) -
          ∑ k ∈ Finset.range N, Debye.coefficientU k (((Real.tanh α)⁻¹ : ℝ) : ℂ) /
            (ν : ℂ) ^ k‖ ≤ C / ν ^ N := by
  sorry

end DLMF.Bessel
