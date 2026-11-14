/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AsymptoticApproximations.ODE.Singularities

/-!
# The obstruction to a logarithm-free resonant Frobenius solution

Andrews, Askey and Roy, *Special Functions*, Appendix F, §F.2, pp. 638–640
(synopsis AAR-F.1–F.3). The smaller-root factor is normalized at the singularity.
Every chosen analytic logarithm on a punctured subdomain is allowed.
-/

@[expose] public noncomputable section
open Complex Metric Set
namespace DLMF.AsymptoticApproximations

/-- The resonant recurrence obstruction vanishes exactly when the smaller root has a
convergent logarithm-free Frobenius solution. Andrews–Askey–Roy, Appendix F, §F.2.
The coefficient at the resonant index is free; only its obstruction is prescribed. -/
theorem frobenius_obstruction_eq_zero_iff {P Q : ℂ → ℂ} {fs gs : ℕ → ℂ}
    {R : ℝ} (hR : 0 < R)
    (hP : ∀ z ∈ ball (0 : ℂ) R, HasSum (fun n => fs n * z ^ n) (P z))
    (hQ : ∀ z ∈ ball (0 : ℂ) R, HasSum (fun n => gs n * z ^ n) (Q z))
    {r₁ r₂ : ℂ} (hr₁ : indicialPoly (fs 0) (gs 0) r₁ = 0)
    (hr₂ : indicialPoly (fs 0) (gs 0) r₂ = 0)
    {N : ℕ} (hN : 0 < N) (hresonance : r₁ - r₂ = N) :
    (∑ j ∈ Finset.Icc 1 N,
      (fs j * (r₂ + N - j) + gs j) * frobeniusCoeff fs gs r₂ (N - j)) = 0 ↔
    ∃ (a : ℕ → ℂ) (A : ℂ → ℂ), a 0 = 1 ∧
      (∀ z ∈ ball (0 : ℂ) R, HasSum (fun n => a n * z ^ n) (A z)) ∧
      DifferentiableOn ℂ A (ball 0 R) ∧
      ∀ (U : Set ℂ) (L : ℂ → ℂ), IsOpen U →
        U ⊆ ball (0 : ℂ) R \ {0} → DifferentiableOn ℂ L U →
        (∀ z ∈ U, exp (L z) = z) →
        ∀ z ∈ U,
          z ^ 2 * iteratedDeriv 2 (fun w => exp (r₂ * L w) * A w) z +
            z * P z * deriv (fun w => exp (r₂ * L w) * A w) z +
            Q z * (exp (r₂ * L z) * A z) = 0 := by
  sorry

end DLMF.AsymptoticApproximations
