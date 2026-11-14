/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.IncompleteGamma.Basic
public import DLMF.IncompleteGamma.ContinuedProperties
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Incomplete-Gamma tails in steepest-ray remainder bounds

Olver, *Asymptotics and Special Functions*, Chapter 4, §10,
pp. 135–137, synopsis O-4.13. The omitted finite-ray tail is retained exactly.
-/

@[expose] public noncomputable section

open MeasureTheory Set Complex DLMF.Hypergeometric

namespace DLMF.Confluent

/-- The exact incomplete-Gamma tail of a decreasing exponential power majorant.
Olver, Chapter 4, §10, synopsis O-4.13. -/
theorem integral_Ioi_exp_neg_mul_rpow_eq_upperIncompleteGamma {ρ κ T : ℝ}
    (hρ : 0 < ρ) (hκ : 0 < κ) (hT : 0 < T) :
    ((∫ t : ℝ in Ioi T, Real.exp (-κ * t) * t ^ (ρ - 1) : ℝ) : ℂ) =
      ((κ ^ (-ρ) : ℝ) : ℂ) * upperIncompleteGamma ρ (κ * T) := by
  sorry

/-- A transformed steepest-ray tail inherits an explicit incomplete-Gamma majorant.
Olver, Chapter 4, §10, synopsis O-4.13. Here kappa=Re(z*exp(i*beta))-sigma. -/
theorem norm_integral_Ioi_le_upperIncompleteGamma {f : ℝ → ℂ} {K ρ κ T : ℝ}
    (hK : 0 ≤ K) (hρ : 0 < ρ) (hκ : 0 < κ) (hT : 0 < T)
    (hm : AEStronglyMeasurable f (volume.restrict (Ioi T)))
    (hbound : ∀ t ∈ Ioi T, ‖f t‖ ≤ K * Real.exp (-κ * t) * t ^ (ρ - 1)) :
    IntegrableOn f (Ioi T) ∧ ‖∫ t in Ioi T, f t‖ ≤
      K * κ ^ (-ρ) * (upperIncompleteGamma ρ (κ * T)).re := by
  sorry

/-- The exact large-argument finite expansion on every logarithmic sheet, including all
exceptional parameters. Olver, Chapter 4, §2, pp. 109–112, synopsis O-4.02. -/
theorem upperIncompleteGammaOnLog_eq_sum_add_shift (a w : ℂ) (N : ℕ) :
    upperIncompleteGammaOnLog a w =
      (∑ k ∈ Finset.range N, (-1 : ℂ) ^ k * pochhammer (1 - a) k *
        exp ((a - 1 - k) * w - exp w)) +
      (-1 : ℂ) ^ N * pochhammer (1 - a) N * upperIncompleteGammaOnLog (a - N) w := by
  sorry

end DLMF.Confluent
