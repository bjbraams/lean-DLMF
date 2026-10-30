/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Tactic.CrossRefAttribute
public import DLMF.Elliptic.Basic.Theta

/-!
# Jacobi theta functions, constants, nome forms and lattice data
-/

@[expose] public noncomputable section

open Complex Set Filter
open DLMF.Elliptic
open scoped Real Topology

namespace DLMF.Theta

/-- Nome form `θ₃(z,q) = ∑_{n∈ℤ} q^{n²} e^{2inz}` (DLMF 20.2.3, §20.1). For `‖q‖ < 1`. -/
def jacobiThetaThreeQ (z q : ℂ) : ℂ := ∑' n : ℤ, q ^ (n ^ 2) * cexp (2 * I * n * z)

/-- Nome form `θ₄(z,q) = ∑_{n∈ℤ} (-1)ⁿ q^{n²} e^{2inz}` (DLMF 20.2.4, §20.1). For `‖q‖ < 1`. -/
def jacobiThetaFourQ (z q : ℂ) : ℂ :=
  ∑' n : ℤ, (-1 : ℂ) ^ n * q ^ (n ^ 2) * cexp (2 * I * n * z)

/-- Nome form `θ₂(z,q) = q^{1/4} ∑_{n∈ℤ} q^{n(n+1)} e^{(2n+1)iz}` (DLMF 20.2.2, §20.1), i.e.
`∑ q^{(n+1/2)²} e^{(2n+1)iz}` with the principal fourth root `q^{1/4}`. For `‖q‖ < 1`. -/
def jacobiThetaTwoQ (z q : ℂ) : ℂ :=
  q ^ (1 / 4 : ℂ) * ∑' n : ℤ, q ^ (n * (n + 1)) * cexp ((2 * n + 1) * I * z)

/-- Nome form `θ₁(z,q) = -i q^{1/4} ∑_{n∈ℤ} (-1)ⁿ q^{n(n+1)} e^{(2n+1)iz}` (DLMF 20.2.1, §20.1),
with the principal fourth root `q^{1/4}`. For `‖q‖ < 1`. -/
def jacobiThetaOneQ (z q : ℂ) : ℂ :=
  -I * q ^ (1 / 4 : ℂ) * ∑' n : ℤ, (-1 : ℂ) ^ n * q ^ (n * (n + 1)) * cexp ((2 * n + 1) * I * z)

/-- The theta constant `θ₂(0|τ)` (DLMF §20.4). -/
abbrev jacobiThetaTwoNullTau (τ : ℂ) : ℂ := jacobiThetaTwoTau 0 τ

/-- The theta constant `θ₃(0|τ)` (DLMF §20.4); Mathlib's `jacobiTheta τ`. -/
abbrev jacobiThetaThreeNullTau (τ : ℂ) : ℂ := jacobiThetaThreeTau 0 τ

/-- The theta constant `θ₄(0|τ)` (DLMF §20.4). -/
abbrev jacobiThetaFourNullTau (τ : ℂ) : ℂ := jacobiThetaFourTau 0 τ

/-- `θ₁'(0|τ)`, the `z`-derivative of `θ₁(z|τ)` at `z = 0` (DLMF §20.1, §20.4). -/
def jacobiThetaOneDerivNullTau (τ : ℂ) : ℂ := deriv (fun z => jacobiThetaOneTau z τ) 0

/-- The theta constant `θ₂(0,q)` (principal `q^{1/4}`). -/
abbrev jacobiThetaTwoNullQ (q : ℂ) : ℂ := jacobiThetaTwoQ 0 q

/-- The theta constant `θ₃(0,q) = ∑ q^{n²}`. -/
abbrev jacobiThetaThreeNullQ (q : ℂ) : ℂ := jacobiThetaThreeQ 0 q

/-- The theta constant `θ₄(0,q) = ∑ (-1)ⁿ q^{n²}`. -/
abbrev jacobiThetaFourNullQ (q : ℂ) : ℂ := jacobiThetaFourQ 0 q

/-- `θ₁'(0,q)`, the `z`-derivative of `θ₁(z,q)` at `z = 0`. -/
def jacobiThetaOneDerivNullQ (q : ℂ) : ℂ := deriv (fun z => jacobiThetaOneQ z q) 0

/-- Theta functions indexed by `j = 1, 2, 3, 4` (`θⱼ(z|τ)`; other indices give `0`). -/
def jacobiThetaTau (j : ℕ) (z τ : ℂ) : ℂ :=
  match j with
  | 1 => jacobiThetaOneTau z τ
  | 2 => jacobiThetaTwoTau z τ
  | 3 => jacobiThetaThreeTau z τ
  | 4 => jacobiThetaFourTau z τ
  | _ => 0

/-- DLMF 20.2.5: the lattice points `z_{m,n} = (m + nτ)π`. -/
@[dlmf 20.2.E5]
def latticePoint (m n : ℤ) (τ : ℂ) : ℂ := (m + n * τ) * π

/-- DLMF 20.2.10: the multiplier `M(z|τ) = e^{iz + iπτ/4}`. -/
@[dlmf 20.2.E10]
def thetaMultiplierM (z τ : ℂ) : ℂ := cexp (I * z + π * I * τ / 4)

end DLMF.Theta
