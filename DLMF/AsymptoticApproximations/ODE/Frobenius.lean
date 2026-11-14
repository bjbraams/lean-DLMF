/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AsymptoticApproximations.ODE.Basic
public import Mathlib.Analysis.Analytic.Basic

/-!
# A single Frobenius root under the exact nonresonance condition

The normalized analytic factor uses the existing canonical `frobeniusCoeff`.
Only the shifted indicial denominators for this root must be nonzero; one need not
assume that the difference of the two roots is nonintegral. This is Kristensson,
*Second Order Differential Equations*, Chapter 2, Theorem 2.3, pp. 18–20;
Olver, *Asymptotics and Special Functions*, Chapter 5, Theorem 4.1, pp. 148–151;
and Andrews–Askey–Roy, *Special Functions*, Appendix F, §F.2.
-/

@[expose] public noncomputable section

open Complex Set

namespace DLMF.AsymptoticApproximations

/-- The normalized analytic factor of a Frobenius solution about `z0`, using the
canonical coefficient recursion. Outside its convergence disc this is the totalized
sum; convergence theorems always specify the disc and indicial denominators. -/
def frobeniusAnalyticFactor (fs gs : ℕ → ℂ) (α z₀ z : ℂ) : ℂ :=
  ∑' n : ℕ, frobeniusCoeff fs gs α n * (z - z₀) ^ n

/-- The defining coefficient sum of the analytic Frobenius factor. -/
theorem frobeniusAnalyticFactor_def (fs gs : ℕ → ℂ) (α z₀ z : ℂ) :
    frobeniusAnalyticFactor fs gs α z₀ z =
      ∑' n : ℕ, frobeniusCoeff fs gs α n * (z - z₀) ^ n := rfl

/-- The canonical Frobenius factor is normalized to one at its center, independently
of convergence elsewhere. -/
@[simp] theorem frobeniusAnalyticFactor_self (fs gs : ℕ → ℂ) (α z₀ : ℂ) :
    frobeniusAnalyticFactor fs gs α z₀ z₀ = 1 := by
  simp only [frobeniusAnalyticFactor, sub_self]
  rw [tsum_eq_single 0]
  · simp [frobeniusCoeff]
  · intro n hn
    simp [zero_pow hn]

/-- The canonical recursion converges on the whole coefficient disc for a single
root satisfying the exact shifted-indicial exclusion. Kristensson, Theorem 2.3,
pp. 18–20; Olver, Chapter 5, Theorem 4.1, pp. 148–151; AAR Appendix F, §F.2. -/
theorem summable_frobeniusCoeff_of_nonresonant {fs gs : ℕ → ℂ}
    {α z₀ : ℂ} {R : ℝ} (hR : 0 < R)
    (hfs : ∀ z : ℂ, ‖z‖ < R → Summable (fun n => fs n * z ^ n))
    (hgs : ∀ z : ℂ, ‖z‖ < R → Summable (fun n => gs n * z ^ n))
    (hroot : indicialPoly (fs 0) (gs 0) α = 0)
    (hnonres : ∀ n : ℕ, 1 ≤ n → indicialPoly (fs 0) (gs 0) (α + n) ≠ 0)
    {z : ℂ} (hz : ‖z - z₀‖ < R) :
    Summable (fun n => frobeniusCoeff fs gs α n * (z - z₀) ^ n) := by
  sorry

/-- The single-root Frobenius factor is analytic throughout the full coefficient
disc. Kristensson, Theorem 2.3, pp. 18–20; Olver, Chapter 5, Theorem 4.1,
pp. 148–151. -/
theorem analyticOnNhd_frobeniusAnalyticFactor {fs gs : ℕ → ℂ}
    {α z₀ : ℂ} {R : ℝ} (hR : 0 < R)
    (hfs : ∀ z : ℂ, ‖z‖ < R → Summable (fun n => fs n * z ^ n))
    (hgs : ∀ z : ℂ, ‖z‖ < R → Summable (fun n => gs n * z ^ n))
    (hroot : indicialPoly (fs 0) (gs 0) α = 0)
    (hnonres : ∀ n : ℕ, 1 ≤ n → indicialPoly (fs 0) (gs 0) (α + n) ≠ 0) :
    AnalyticOnNhd ℂ (frobeniusAnalyticFactor fs gs α z₀) (Metric.ball z₀ R) := by
  sorry

/-- The normalized single-root solution solves the equation on the principal slit
disc. The coefficient values at the singular point may be totalized arbitrarily;
only their punctured Laurent expansions occur. Olver, Chapter 5, Theorem 4.1,
pp. 148–151; Kristensson, Theorem 2.3, pp. 18–20; AAR Appendix F, §F.2. -/
theorem frobeniusAnalyticFactor_isLinearODE2SolutionOn
    {f g : ℂ → ℂ} {fs gs : ℕ → ℂ} {α z₀ : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : ∀ z : ℂ, z ≠ z₀ → ‖z - z₀‖ < R →
      HasSum (fun n => fs n * (z - z₀) ^ n) ((z - z₀) * f z))
    (hg : ∀ z : ℂ, z ≠ z₀ → ‖z - z₀‖ < R →
      HasSum (fun n => gs n * (z - z₀) ^ n) ((z - z₀) ^ 2 * g z))
    (hroot : indicialPoly (fs 0) (gs 0) α = 0)
    (hnonres : ∀ n : ℕ, 1 ≤ n → indicialPoly (fs 0) (gs 0) (α + n) ≠ 0) :
    AlgebraicAnalytic.IsLinearODE2SolutionOn f g 0
      (fun z => (z - z₀) ^ α * frobeniusAnalyticFactor fs gs α z₀ z)
      (slitDisc z₀ R) := by
  sorry

/-- An arbitrary analytic logarithm branch gives the same Frobenius construction
with its explicitly chosen power. Olver, Chapter 5, Theorem 4.1, pp. 148–151. -/
theorem frobeniusAnalyticFactor_exp_log_isLinearODE2SolutionOn
    {f g : ℂ → ℂ} {fs gs : ℕ → ℂ} {α z₀ : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : ∀ z : ℂ, z ≠ z₀ → ‖z - z₀‖ < R →
      HasSum (fun n => fs n * (z - z₀) ^ n) ((z - z₀) * f z))
    (hg : ∀ z : ℂ, z ≠ z₀ → ‖z - z₀‖ < R →
      HasSum (fun n => gs n * (z - z₀) ^ n) ((z - z₀) ^ 2 * g z))
    (hroot : indicialPoly (fs 0) (gs 0) α = 0)
    (hnonres : ∀ n : ℕ, 1 ≤ n → indicialPoly (fs 0) (gs 0) (α + n) ≠ 0)
    {U : Set ℂ} (hU : IsOpen U) (hdisc : U ⊆ Metric.ball z₀ R \ {z₀})
    {L : ℂ → ℂ} (hL : AnalyticOnNhd ℂ L U)
    (hexp : ∀ z ∈ U, exp (L z) = z - z₀) :
    AlgebraicAnalytic.IsLinearODE2SolutionOn f g 0
      (fun z => exp (α * L z) * frobeniusAnalyticFactor fs gs α z₀ z) U := by
  sorry

end DLMF.AsymptoticApproximations
