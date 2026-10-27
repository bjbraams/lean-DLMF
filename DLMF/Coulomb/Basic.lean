/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.Basic

/-!
# Coulomb functions: definitions (DLMF §33.2)

This is the definitions file of the Coulomb area (DLMF Chapter 33). The functions of
DLMF §33.2 were first defined in the Confluent area (`DLMF.Confluent.Coulomb`,
`DLMF.Confluent.CoulombAsymptotics`, `DLMF.Confluent.CoulombIrregular`); on 2026-10-26 their
definitions were moved down here unchanged, keeping the namespace `DLMF.Confluent`:

* `coulombWave`, `coulombWaveDeriv`: the unnormalized regular solution
  `ρ^{ℓ+1} e^{-iρ} M(ℓ+1-iη, 2ℓ+2, 2iρ)` and its derivative;
* `coulombC`: the normalizing constant `C_ℓ(η)` (DLMF 33.2.5);
* `coulombF`: the regular Coulomb function `F_ℓ(η,ρ)` (DLMF 33.2.4);
* `coulombSigma`, `coulombTheta`: the phase shift `σ_ℓ(η)` (principal branch of the phase) and
  the phase `θ_ℓ(η,ρ)` (DLMF 33.2.9–33.2.10);
* `coulombHPlus`, `coulombHMinus`: the irregular functions `H^±_ℓ(η,ρ)` (DLMF 33.2.8);
* `coulombAPlus`: the constant in `H^+_ℓ = A^+ ρ^{ℓ+1} e^{iρ} U(ℓ+1+iη, 2ℓ+2, -2iρ)`;
* `coulombG`: the irregular function `G_ℓ(η,ρ) = Re H^+_ℓ(η,ρ)` (DLMF 33.2.11).

New Chapter 33 definitions live in the namespace `DLMF.Coulomb`:

* `DLMF.Coulomb.turningPoint`: the outer turning point `ρ_tp(η,ℓ)` (DLMF 33.2.2).
-/

@[expose] public section

open Complex
open scoped Real Nat

noncomputable section

namespace DLMF.Confluent

/-- The unnormalized regular Coulomb wave function
`ρ^{ℓ+1} e^{-iρ} M(ℓ + 1 - iη, 2ℓ + 2, 2iρ)` (DLMF 33.2.4 without `C_ℓ(η)`), entire in `ρ`. -/
def coulombWave (ℓ : ℕ) (η z : ℂ) : ℂ :=
  z ^ (ℓ + 1) * exp (-I * z) * kummerM (ℓ + 1 - I * η) (2 * ℓ + 2) (2 * I * z)

/-- The derivative of `coulombWave`. -/
def coulombWaveDeriv (ℓ : ℕ) (η z : ℂ) : ℂ :=
  exp (-I * z) * (((ℓ + 1 : ℕ) : ℂ) * z ^ ℓ *
      kummerM (ℓ + 1 - I * η) (2 * ℓ + 2) (2 * I * z) -
    I * z ^ (ℓ + 1) * kummerM (ℓ + 1 - I * η) (2 * ℓ + 2) (2 * I * z) +
    2 * I * ((ℓ + 1 - I * η) / (2 * ℓ + 2)) * z ^ (ℓ + 1) *
      kummerM (ℓ + 1 - I * η + 1) (2 * ℓ + 2 + 1) (2 * I * z))

/-- The Coulomb normalizing constant `C_ℓ(η) = 2^ℓ e^{-πη/2} |Γ(ℓ+1+iη)| / (2ℓ+1)!`
(DLMF 33.2.5). -/
@[dlmf 33.2.E5]
def coulombC (ℓ : ℕ) (η : ℝ) : ℝ :=
  2 ^ ℓ * Real.exp (-π * η / 2) * ‖Gamma (ℓ + 1 + I * η)‖ / (2 * ℓ + 1)!

/-- **The regular Coulomb wave function** `F_ℓ(η,ρ) = C_ℓ(η) ρ^{ℓ+1} e^{-iρ}
M(ℓ+1-iη, 2ℓ+2, 2iρ)` (DLMF 33.2.4, Temme §7.3.2), for real `η` and `ρ`. -/
@[dlmf 33.2.E4]
def coulombF (ℓ : ℕ) (η ρ : ℝ) : ℝ :=
  (coulombC ℓ η * coulombWave ℓ η ρ).re

/-- The Coulomb phase shift `σ_ℓ(η) = ph Γ(ℓ+1+iη)` (DLMF 33.2.10), principal branch. -/
@[dlmf 33.2.E10]
def coulombSigma (ℓ : ℕ) (η : ℝ) : ℝ := arg (Gamma (ℓ + 1 + I * η))

/-- The Coulomb phase `θ_ℓ(η,ρ) = ρ - η ln(2ρ) - ℓπ/2 + σ_ℓ(η)` (DLMF 33.2.9). -/
@[dlmf 33.2.E9]
def coulombTheta (ℓ : ℕ) (η ρ : ℝ) : ℝ := ρ - η * Real.log (2 * ρ) - ℓ * π / 2 + coulombSigma ℓ η

/-- The outgoing Coulomb function
`H^+_ℓ(η,ρ) = e^{iθ_ℓ} (-2iρ)^{ℓ+1+iη} U(ℓ+1+iη, 2ℓ+2, -2iρ)` (DLMF 33.2.8, upper signs). -/
@[dlmf 33.2.E8]
def coulombHPlus (ℓ : ℕ) (η ρ : ℝ) : ℂ :=
  exp (I * coulombTheta ℓ η ρ) * (-2 * I * ρ) ^ ((ℓ : ℂ) + 1 + I * η) *
    kummerU ((ℓ : ℂ) + 1 + I * η) (2 * ℓ + 2) (-2 * I * ρ)

/-- The incoming Coulomb function
`H^-_ℓ(η,ρ) = e^{-iθ_ℓ} (2iρ)^{ℓ+1-iη} U(ℓ+1-iη, 2ℓ+2, 2iρ)` (DLMF 33.2.8, lower signs). -/
@[dlmf 33.2.E8]
def coulombHMinus (ℓ : ℕ) (η ρ : ℝ) : ℂ :=
  exp (-I * coulombTheta ℓ η ρ) * (2 * I * ρ) ^ ((ℓ : ℂ) + 1 - I * η) *
    kummerU ((ℓ : ℂ) + 1 - I * η) (2 * ℓ + 2) (2 * I * ρ)

/-- The constant in `H^+_ℓ = A^+ ρ^{ℓ+1} e^{iρ} U(ℓ+1+iη, 2ℓ+2, -2iρ)`. -/
def coulombAPlus (ℓ : ℕ) (η : ℝ) : ℂ :=
  exp (coulombSigma ℓ η * I) * Real.exp (π * η / 2) * 2 ^ (ℓ + 1) * (-1) ^ ℓ * (-I)

/-- **The irregular Coulomb function** `G_ℓ(η,ρ) = Re H^+_ℓ(η,ρ)`, defined by DLMF 33.2.11. -/
@[dlmf 33.2.E11]
def coulombG (ℓ : ℕ) (η ρ : ℝ) : ℝ := (coulombHPlus ℓ η ρ).re

end DLMF.Confluent

namespace DLMF.Coulomb

/-- The outer turning point `ρ_tp(η,ℓ) = η + (η² + ℓ(ℓ+1))^{1/2}` of the Coulomb wave equation
(DLMF 33.2.2). -/
@[dlmf 33.2.E2]
def turningPoint (η : ℝ) (ℓ : ℕ) : ℝ := η + Real.sqrt (η ^ 2 + ℓ * (ℓ + 1))

end DLMF.Coulomb
