/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import TauCeti.RepresentationTheory.SU2.Borel
public import TauCeti.RepresentationTheory.Compact.Haar
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Euler coordinates and probability Haar measure on SU(2)

Andrews, Askey and Roy, *Special Functions*, §§9.12–9.13, pp. 469–473.
TauCeti supplies the compact group and canonical probability Haar measure.
The off-diagonal Euler phase is `i`, as in the source.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped Matrix

namespace DLMF.SphericalHarmonics

/-- The source's Euler matrix: `a = exp(i(φ+ψ)/2) cos(θ/2)` and
`b = i exp(i(φ-ψ)/2) sin(θ/2)`. Andrews–Askey–Roy, *Special Functions*,
§§9.12–9.13 (synopsis AAR-9.11–9.16). -/
def suTwoEulerMatrix (θ φ ψ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  let a := Complex.exp (Complex.I * (φ + ψ) / 2) * Real.cos (θ / 2)
  let b := Complex.I * Complex.exp (Complex.I * (φ - ψ) / 2) * Real.sin (θ / 2)
  !![a, b; -star b, star a]

/-- The explicit Euler matrix. -/
theorem suTwoEulerMatrix_def (θ φ ψ : ℝ) :
    suTwoEulerMatrix θ φ ψ =
      let a := Complex.exp (Complex.I * (φ + ψ) / 2) * Real.cos (θ / 2)
      let b := Complex.I * Complex.exp (Complex.I * (φ - ψ) / 2) * Real.sin (θ / 2)
      !![a, b; -star b, star a] := rfl

/-- Every Euler matrix is special unitary. Andrews–Askey–Roy,
*Special Functions*, §9.12 (synopsis AAR-9.11–9.16). -/
theorem suTwoEulerMatrix_mem (θ φ ψ : ℝ) :
    suTwoEulerMatrix θ φ ψ ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  sorry

/-- Euler-coordinate probability Haar integration, including its exact normalization.
Andrews–Askey–Roy, *Special Functions*, §§9.12–9.13, pp. 469–473
(synopsis AAR-9.11–9.16). Continuity is required only on SU(2), so no
regularity outside the group is imposed on the ambient matrix function. -/
theorem integral_haarProb_suTwo_eq_euler_integral
    (F : Matrix (Fin 2) (Fin 2) ℂ → ℂ)
    (hF : ContinuousOn F (Matrix.specialUnitaryGroup (Fin 2) ℂ : Set _)) :
    (∫ g : TauCeti.SU2, F (g : Matrix (Fin 2) (Fin 2) ℂ) ∂TauCeti.haarProb TauCeti.SU2) =
      (1 / (16 * Real.pi ^ 2) : ℂ) *
        ∫ θ : ℝ in 0..Real.pi, ∫ φ : ℝ in 0..2 * Real.pi,
          ∫ ψ : ℝ in (-2 * Real.pi)..2 * Real.pi,
            F (suTwoEulerMatrix θ φ ψ) * Real.sin θ := by
  sorry

end DLMF.SphericalHarmonics
