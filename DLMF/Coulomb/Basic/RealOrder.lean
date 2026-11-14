/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Coulomb.Basic.AuxiliaryData

/-!
# Coulomb waves for nonnegative real angular momentum

Temme, *Special Functions* (1996), Chapter 7, equation (7.19), pages 178–179.
The parameter is a real angular momentum, not only a natural number. The regular
function reuses the canonical complex-order unnormalized wave; all powers at positive
radius have their positive-real normalization.
-/

@[expose] public noncomputable section

open Complex
open scoped Real

namespace DLMF.Coulomb.Real

/-- The positive Coulomb normalization for `ℓ≥0`, `η∈ℝ`.
Temme (7.19), synopsis TEM-07-06. -/
def coulombNormalization (ℓ η : ℝ) : ℝ :=
  (2 : ℝ) ^ ℓ * _root_.Real.exp (-π * η / 2) *
    ‖Gamma (ℓ + 1 + I * η)‖ / _root_.Real.Gamma (2 * ℓ + 2)

/-- The principal phase shift for real angular momentum.
Temme (7.19), synopsis TEM-07-06. -/
def coulombSigma (ℓ η : ℝ) : ℝ := arg (Gamma (ℓ + 1 + I * η))

/-- The real Coulomb phase, with the natural logarithm of the positive radius.
Temme (7.19), synopsis TEM-07-06. -/
def coulombTheta (ℓ η ρ : ℝ) : ℝ :=
  ρ - η * _root_.Real.log (2 * ρ) - ℓ * π / 2 + coulombSigma ℓ η

/-- The regular normalized real Coulomb wave for `ℓ≥0`, `ρ>0`.
Temme (7.19), synopsis TEM-07-06. -/
def coulombF (ℓ η ρ : ℝ) : ℝ :=
  (coulombNormalization ℓ η * DLMF.Coulomb.coulombWaveComplex ℓ η ρ).re

/-- The incoming solution `iB U(ℓ+1-iη,2ℓ+2,2iρ)` on the positive radius ray.
Temme (7.19), synopsis TEM-07-06. Principal Tricomi U is used at `2iρ`. -/
def coulombIncoming (ℓ η ρ : ℝ) : ℂ :=
  I * exp (π * η / 2 + I * ℓ * π - I * coulombSigma ℓ η - I * ρ) *
    (2 * (ρ : ℂ)) ^ ((ℓ : ℂ) + 1) *
      DLMF.Confluent.kummerU (ℓ + 1 - I * η) (2 * ℓ + 2) (2 * I * ρ)

/-- The irregular normalized real Coulomb wave for real angular momentum and positive radius.
Temme (7.19), synopsis TEM-07-06. -/
def coulombG (ℓ η ρ : ℝ) : ℝ := (coulombIncoming ℓ η ρ).re

/-- The defining positive-real normalization. -/
theorem coulombNormalization_def (ℓ η : ℝ) :
    coulombNormalization ℓ η = (2 : ℝ) ^ ℓ * _root_.Real.exp (-π * η / 2) *
      ‖Gamma (ℓ + 1 + I * η)‖ / _root_.Real.Gamma (2 * ℓ + 2) := rfl

/-- The defining principal Gamma phase. -/
theorem coulombSigma_def (ℓ η : ℝ) :
    coulombSigma ℓ η = arg (Gamma (ℓ + 1 + I * η)) := rfl

/-- The defining real oscillatory phase. -/
theorem coulombTheta_def (ℓ η ρ : ℝ) :
    coulombTheta ℓ η ρ =
      ρ - η * _root_.Real.log (2 * ρ) - ℓ * π / 2 + coulombSigma ℓ η := rfl

/-- The defining normalized regular wave. -/
theorem coulombF_def (ℓ η ρ : ℝ) :
    coulombF ℓ η ρ =
      (coulombNormalization ℓ η * DLMF.Coulomb.coulombWaveComplex ℓ η ρ).re := rfl

/-- The defining principal incoming solution. -/
theorem coulombIncoming_def (ℓ η ρ : ℝ) :
    coulombIncoming ℓ η ρ =
      I * exp (π * η / 2 + I * ℓ * π - I * coulombSigma ℓ η - I * ρ) *
        (2 * (ρ : ℂ)) ^ ((ℓ : ℂ) + 1) *
          DLMF.Confluent.kummerU (ℓ + 1 - I * η) (2 * ℓ + 2) (2 * I * ρ) := rfl

/-- The defining real irregular wave. -/
theorem coulombG_def (ℓ η ρ : ℝ) : coulombG ℓ η ρ = (coulombIncoming ℓ η ρ).re := rfl

/-- The physical real-angular-momentum normalization is strictly positive.
Temme (7.19), synopsis TEM-07-06. -/
theorem coulombNormalization_pos {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (η : ℝ) :
    0 < coulombNormalization ℓ η := by
  have hΓ : 0 < _root_.Real.Gamma (2 * ℓ + 2) :=
    _root_.Real.Gamma_pos_of_pos (by linarith)
  have hn : 0 < ‖Gamma (ℓ + 1 + I * η)‖ := by
    apply norm_pos_iff.mpr
    apply Complex.Gamma_ne_zero_of_re_pos
    simp only [add_re, ofReal_re, one_re, mul_re, I_re, I_im, ofReal_im]
    linarith
  unfold coulombNormalization
  positivity

/-- The real-order Gamma phase restricts to the natural-order phase.
Temme (7.19), synopsis TEM-07-06. -/
theorem coulombSigma_natCast (n : ℕ) (η : ℝ) :
    coulombSigma n η = DLMF.Confluent.coulombSigma n η := by
  simp only [coulombSigma, DLMF.Confluent.coulombSigma, ofReal_natCast]

end DLMF.Coulomb.Real
