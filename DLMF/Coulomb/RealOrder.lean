/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Coulomb.Basic.RealOrder
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Real-angular-momentum Coulomb normalization, equation and additive asymptotics

Temme, *Special Functions* (1996), Chapter 7, equation (7.19), pages 178–179.
The statements retain every nonnegative real angular momentum. Oscillatory asymptotics
use additive errors, so zeros of sine and cosine impose no excluded subsequences.
-/

@[expose] public noncomputable section

open Complex Filter Set Asymptotics
open scoped Real Topology

namespace DLMF.Coulomb.Real

/-- The complete complex regular expression is real on the physical radius ray.
Temme (7.19), synopsis TEM-07-06. -/
theorem coulombF_of_normalized_complex_wave {ℓ ρ : ℝ} (hℓ : 0 ≤ ℓ)
    (η : ℝ) (hρ : 0 < ρ) :
    (coulombF ℓ η ρ : ℂ) =
      coulombNormalization ℓ η * DLMF.Coulomb.coulombWaveComplex ℓ η ρ := by
  sorry

/-- The irregular wave has the exact real-valued Tricomi combination of the source.
Temme (7.19), synopsis TEM-07-06. -/
theorem coulombG_eq_tricomi_combination {ℓ ρ : ℝ} (hℓ : 0 ≤ ℓ)
    (η : ℝ) (hρ : 0 < ρ) :
    (coulombG ℓ η ρ : ℂ) = I * (coulombF ℓ η ρ : ℂ) + coulombIncoming ℓ η ρ := by
  sorry

/-- The real-order regular function agrees with the existing natural-order function.
Temme (7.19), synopsis TEM-07-06. -/
theorem coulombF_natCast (n : ℕ) (η : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    coulombF n η ρ = DLMF.Confluent.coulombF n η ρ := by
  sorry

/-- The real-order irregular function agrees with the existing natural-order function.
Temme (7.19), synopsis TEM-07-06. -/
theorem coulombG_natCast (n : ℕ) (η : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    coulombG n η ρ = DLMF.Confluent.coulombG n η ρ := by
  sorry

/-- Both real-order waves are analytic at every positive radius.
Temme (7.19), synopsis TEM-07-06. -/
theorem analyticOnNhd_coulombF_coulombG {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (η : ℝ) :
    AnalyticOnNhd ℝ (coulombF ℓ η) (Ioi 0) ∧
      AnalyticOnNhd ℝ (coulombG ℓ η) (Ioi 0) := by
  sorry

/-- The Coulomb equation for both real-angular-momentum solutions.
Temme (7.19), synopsis TEM-07-06. -/
theorem coulombF_coulombG_ode {ℓ ρ : ℝ} (hℓ : 0 ≤ ℓ) (η : ℝ) (hρ : 0 < ρ) :
    (iteratedDeriv 2 (coulombF ℓ η) ρ +
      (1 - 2 * η / ρ - ℓ * (ℓ + 1) / ρ ^ 2) * coulombF ℓ η ρ = 0) ∧
    (iteratedDeriv 2 (coulombG ℓ η) ρ +
      (1 - 2 * η / ρ - ℓ * (ℓ + 1) / ρ ^ 2) * coulombG ℓ η ρ = 0) := by
  sorry

/-- The regular-wave sine asymptotic has an additive `O(1/ρ)` error.
Temme (7.19), synopsis TEM-07-06. -/
theorem isBigO_coulombF_sub_sin {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (η : ℝ) :
    (fun ρ : ℝ => coulombF ℓ η ρ - _root_.Real.sin (coulombTheta ℓ η ρ)) =O[atTop]
      (fun ρ : ℝ => ρ⁻¹) := by
  sorry

/-- The irregular-wave cosine asymptotic has an additive `O(1/ρ)` error.
Temme (7.19), synopsis TEM-07-06. -/
theorem isBigO_coulombG_sub_cos {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (η : ℝ) :
    (fun ρ : ℝ => coulombG ℓ η ρ - _root_.Real.cos (coulombTheta ℓ η ρ)) =O[atTop]
      (fun ρ : ℝ => ρ⁻¹) := by
  sorry

end DLMF.Coulomb.Real
