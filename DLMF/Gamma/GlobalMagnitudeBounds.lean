/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Gamma.Basic
public import DLMFMathlib.Analysis.Complex.GlobalLogSineBounds
public import TauCeti.Analysis.SpecialFunctions.Gamma.Stirling
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Gamma magnitude bounds away from pole discs

Kristensson, *Second Order Differential Equations*, Appendix A, Lemmas A.3–A.4,
Corollary A.2 and the Binet remainder formula (A.6). These global magnitude estimates
allow arguments on both sides of the negative real axis; they do not replace sectorial
complex Gamma asymptotics. The normalized logarithm is TauCeti's `TauCeti.logGamma`.
-/

@[expose] public section

open Complex MeasureTheory Set
open scoped Real

noncomputable section

namespace DLMF.Gamma

/-- Kristensson, Appendix A, Lemma A.3, pp. 170–172: global two-sided Stirling
magnitude bounds away from discs about the Gamma poles. The argument is principal. -/
theorem exists_norm_Gamma_stirling_global_bounds {ε : ℝ}
    (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ z : ℂ,
      (∀ n : ℕ, ε < ‖z + n‖) →
      c ≤ ‖Complex.Gamma z‖ * Real.exp
        (-(z.re - 1 / 2) * Real.log ‖z‖ + z.im * z.arg + z.re) ∧
      ‖Complex.Gamma z‖ * Real.exp
        (-(z.re - 1 / 2) * Real.log ‖z‖ + z.im * z.arg + z.re) ≤ C := by
  sorry

/-- Kristensson, Appendix A, Corollary A.2, p. 172: the shifted Gamma magnitude
bound, with the power and exponential expressed in the original variable `z`. -/
theorem exists_norm_Gamma_add_stirling_global_bounds (α : ℂ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ z : ℂ, ε < ‖z‖ →
      (∀ n : ℕ, ε < ‖z + α + n‖) →
      c ≤ ‖Complex.Gamma (z + α)‖ * Real.exp
        (-(z.re + α.re - 1 / 2) * Real.log ‖z‖ + z.im * z.arg + z.re) ∧
      ‖Complex.Gamma (z + α)‖ * Real.exp
        (-(z.re + α.re - 1 / 2) * Real.log ‖z‖ + z.im * z.arg + z.re) ≤ C := by
  sorry

/-- Kristensson, Appendix A, Lemma A.4, pp. 172–173: a Gamma ratio is comparable
in magnitude to `‖z‖^(Re α)` globally away from both families of pole discs. -/
theorem exists_norm_Gamma_add_div_Gamma_global_bounds (α : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ z : ℂ,
      (∀ n : ℕ, ε < ‖z + n‖) → (∀ n : ℕ, ε < ‖z + α + n‖) →
      c * ‖z‖ ^ α.re ≤ ‖Complex.Gamma (z + α) / Complex.Gamma z‖ ∧
        ‖Complex.Gamma (z + α) / Complex.Gamma z‖ ≤ C * ‖z‖ ^ α.re := by
  sorry

/-- Kristensson, Appendix A, (A.6), p. 166: Binet's remainder as an absolutely
convergent logarithmic integral in the right half-plane. The logarithm of Gamma is
the branch real on the positive real axis. -/
theorem logGamma_stirling_remainder_eq_integral {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => z / (z ^ 2 + (t : ℂ) ^ 2) *
      (Real.log (1 / (1 - Real.exp (-2 * Real.pi * t))) : ℂ)) (Ioi 0) ∧
    TauCeti.logGamma z - (z - 1 / 2) * Complex.log z + z -
      (Real.log (2 * Real.pi) / 2 : ℝ) =
      (Real.pi : ℂ)⁻¹ * ∫ t : ℝ in Ioi 0,
        z / (z ^ 2 + (t : ℂ) ^ 2) *
          (Real.log (1 / (1 - Real.exp (-2 * Real.pi * t))) : ℂ) := by
  sorry

end DLMF.Gamma
