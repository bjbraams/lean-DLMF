/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Calculus.CanonicalOperators
public import DLMF.Legendre.Basic.Harmonics
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Orbital angular-momentum eigenfunctions in Cartesian coordinates

Rao–Lakshminarayanan, *Generalized Hypergeometric Functions* (2018),
(5.26)–(5.35), p. 5-7, synopsis RL-5.02. The normalization is the raw derivative
of the Legendre polynomial, without the Condon–Shortley sign or unit L² factor.
The Cartesian formula removes the artificial cut in the azimuthal angle.
-/

@[expose] public noncomputable section
open Complex Laplacian
namespace DLMF.WignerSymbols.OrbitalModes

/-- The Euclidean radius used by the Cartesian angular modes. -/
def radius (x : Fin 3 → ℝ) : ℝ := Real.sqrt (∑ i : Fin 3, (x i) ^ 2)

/-- The raw-derivative angular mode. For negative order the transverse factor is
conjugated, giving `exp(i m φ)` in either sign convention. Rao–Lakshminarayanan
(5.26)–(5.35), synopsis RL-5.02. Its intended domain excludes the origin. -/
def value (l : ℕ) (m : ℤ) (x : Fin 3 → ℝ) : ℂ :=
  ((if m < 0 then (x 0 : ℂ) - I * x 1 else (x 0 : ℂ) + I * x 1) / radius x) ^ m.natAbs *
    iteratedDeriv m.natAbs (DLMF.OrthogonalPolynomials.legendrePolynomialP l) (x 2 / radius x)

/-- The defining radius formula. -/
theorem radius_def (x : Fin 3 → ℝ) : radius x = Real.sqrt (∑ i : Fin 3, (x i) ^ 2) := rfl

/-- The Cartesian angular-mode formula. -/
theorem value_def (l : ℕ) (m : ℤ) (x : Fin 3 → ℝ) :
    value l m x =
      ((if m < 0 then (x 0 : ℂ) - I * x 1 else (x 0 : ℂ) + I * x 1) / radius x) ^
        m.natAbs *
      iteratedDeriv m.natAbs (DLMF.OrthogonalPolynomials.legendrePolynomialP l)
        (x 2 / radius x) := rfl

/-- The Cartesian formula agrees with the raw spherical derivative convention,
Rao–Lakshminarayanan (5.26)–(5.35), synopsis RL-5.02. -/
theorem value_spherical (l : ℕ) (m : ℤ) {r θ : ℝ} (hr : 0 < r)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) Real.pi) (φ : ℝ) :
    value l m ![r * Real.sin θ * Real.cos φ, r * Real.sin θ * Real.sin φ, r * Real.cos θ] =
      (Real.sin θ : ℂ) ^ m.natAbs *
        iteratedDeriv m.natAbs (DLMF.OrthogonalPolynomials.legendrePolynomialP l) (Real.cos θ) *
          exp (I * m * φ) := by
  sorry

/-- The z-angular momentum has eigenvalue `m`, Rao–Lakshminarayanan
(5.26)–(5.35), synopsis RL-5.02. -/
theorem angularMomentum_two_value (l : ℕ) (m : ℤ) {x : Fin 3 → ℝ}
    (hx : x ≠ 0) :
    Complex.CanonicalOperators.angularMomentum 2 (value l m) x = m * value l m x := by
  sorry

/-- The orbital Casimir has eigenvalue `l(l+1)`, Rao–Lakshminarayanan
(5.26)–(5.35), synopsis RL-5.02. -/
theorem casimir_value (l : ℕ) (m : ℤ) (hm : m.natAbs ≤ l) {x : Fin 3 → ℝ}
    (hx : x ≠ 0) :
    Complex.CanonicalOperators.casimir (value l m) x = l * (l + 1) * value l m x := by
  sorry

/-- Multiplication by `r^l` gives a solid harmonic away from the origin,
Rao–Lakshminarayanan (5.26)–(5.35), synopsis RL-5.02. -/
theorem laplacian_solid_value (l : ℕ) (m : ℤ) (hm : m.natAbs ≤ l)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ≠ 0) :
    laplacian (fun y : EuclideanSpace ℝ (Fin 3) =>
      (radius (fun i => y i) : ℂ) ^ l * value l m (fun i => y i)) x = 0 := by
  sorry

end DLMF.WignerSymbols.OrbitalModes
