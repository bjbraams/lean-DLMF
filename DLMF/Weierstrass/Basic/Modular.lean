/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Theta.Basic.Definitions
public import DLMF.JacobiElliptic.Basic.Definitions
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Mathlib.Analysis.Meromorphic.Basic
public import DLMFMathlib.NumberTheory.ModularForms.KleinJSurjective

/-!
# Elliptic modular functions: definitions (DLMF §§23.15, 23.18)

The bilinear transformations of `SL(2, ℤ)`, the notions of modular function, modular form and
cusp form, the elliptic modular function `λ(τ)`, the Dedekind sum and the eta multiplier.
Klein's complete invariant `J(τ)` is `ModularForm.kleinJ`.

## Main definitions

* `modularMobius`: the bilinear transformation `𝒜τ = (aτ + b)/(cτ + d)` of DLMF 23.15.3.
* `IsModularFunction`, `IsModularForm`, `IsCuspForm`: the notions of DLMF §23.15(i).
* `modularLambda`: `λ(τ) = θ₂⁴(0|τ)/θ₃⁴(0|τ)` (DLMF 23.15.6).
* `dedekindSum`, `etaMultiplier`: the Dedekind sum and eta multiplier (DLMF 23.18.6–23.18.7).

## Main results

* `modularMobius_det`, `modularMobius_coe`: DLMF 23.15.4 and the bridge to Mathlib's Möbius action
  of `SL(2, ℤ)` on `ℍ` (DLMF 23.15.3).
* `modularLambda_eq_modulus_sq`: `λ(τ) = k²` with `k = θ₂²(0|τ)/θ₃²(0|τ)` (DLMF 23.15.6).
* `jacobiThetaOneDerivNullTau_eq`: DLMF 23.15.8.

## Implementation notes

`λ` is defined from the project's theta functions in lattice-parameter form `θⱼ(0|τ)`
(`DLMF.Theta.jacobiThetaTwoNullTau` etc.). The general notions of §23.15(i) are formalized
literally: the level `ℓ` is an integer or half an odd integer, which we encode by the integer
`ℓ₂ = 2ℓ`, with `(cτ + d)^ℓ` the principal power. "Analytic at `q = 0` as a function of `q`"
means that `f(τ) = F(e^{iπτ})` with `F` analytic at `0`.

Klein's invariant is `ModularForm.kleinJ τ = E₄(τ)³/(E₄(τ)³ - E₆(τ)²)` on `ℍ` (in
`DLMFMathlib`); the theta-function formula of DLMF 23.15.7 is the theorem
`DLMF.Weierstrass.kleinJ_eq_jacobiTheta`.
-/

@[expose] public section

open Complex Matrix
open UpperHalfPlane hiding I
open scoped Real MatrixGroups

noncomputable section

namespace DLMF.Weierstrass

open DLMF.Elliptic DLMF.Theta DLMF.JacobiElliptic

/-- The bilinear transformation `𝒜τ = (aτ + b)/(cτ + d)` (DLMF 23.15.3) of
`𝒜 = [a b; c d] ∈ SL(2, ℤ)`. -/
@[dlmf 23.15.E3]
def modularMobius (A : SL(2, ℤ)) (τ : ℂ) : ℂ :=
  ((A 0 0 : ℂ) * τ + A 0 1) / ((A 1 0 : ℂ) * τ + A 1 1)

/-- DLMF 23.15.4: the entries of `𝒜 ∈ SL(2, ℤ)` satisfy `ad - bc = 1`. -/
@[dlmf 23.15.E4]
theorem modularMobius_det (A : SL(2, ℤ)) : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
  have h := A.2
  rwa [Matrix.det_fin_two] at h

/-- The Möbius action of `SL(2, ℤ)` on `ℍ` is the transformation 23.15.3. -/
@[dlmf 23.15.E3]
theorem modularMobius_coe (A : SL(2, ℤ)) (τ : ℍ) : ((A • τ : ℍ) : ℂ) = modularMobius A τ := by
  rw [coe_specialLinearGroup_apply, modularMobius]
  simp

/-! ### §23.15(i) General modular functions -/

/-- A modular function of level `ℓ = ℓ₂/2` for a subgroup `Γ ⊆ SL(2, ℤ)` (DLMF 23.15.5,
§23.15(i)): `f` is meromorphic in `ℑτ > 0` and for each `𝒜 ∈ Γ` there is a constant `c_𝒜` with
`f(𝒜τ) = c_𝒜 (cτ + d)^ℓ f(τ)` for `ℑτ > 0` (principal power). -/
@[dlmf 23.15.E5]
def IsModularFunction (Γ : Subgroup SL(2, ℤ)) (ℓ₂ : ℤ) (f : ℂ → ℂ) : Prop :=
  MeromorphicOn f {τ : ℂ | 0 < τ.im} ∧
    ∀ A ∈ Γ, ∃ c : ℂ, ∀ τ : ℍ,
      f (A • τ : ℍ) = c * ((A 1 0 : ℂ) * τ + A 1 1) ^ ((ℓ₂ : ℂ) / 2) * f τ

/-- A modular form (DLMF §23.15(i)): a modular function that, as a function of `q = e^{iπτ}`,
is analytic at `q = 0`. -/
@[dlmf 23.15.i]
def IsModularForm (Γ : Subgroup SL(2, ℤ)) (ℓ₂ : ℤ) (f : ℂ → ℂ) : Prop :=
  IsModularFunction Γ ℓ₂ f ∧
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F 0 ∧ ∀ τ : ℍ, f τ = F (cexp (π * I * τ))

/-- A cusp form (DLMF §23.15(i)): a modular form with `f(τ) → 0` as `q → 0`. -/
@[dlmf 23.15.i]
def IsCuspForm (Γ : Subgroup SL(2, ℤ)) (ℓ₂ : ℤ) (f : ℂ → ℂ) : Prop :=
  IsModularFunction Γ ℓ₂ f ∧
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F 0 ∧ F 0 = 0 ∧ ∀ τ : ℍ, f τ = F (cexp (π * I * τ))

/-! ### §23.15(ii) `λ(τ)` and `J(τ)` -/

/-- The elliptic modular function `λ(τ) = θ₂⁴(0|τ)/θ₃⁴(0|τ)` (DLMF 23.15.6), for `ℑτ > 0`. -/
@[dlmf 23.15.E6]
def modularLambda (τ : ℂ) : ℂ := jacobiThetaTwoNullTau τ ^ 4 / jacobiThetaThreeNullTau τ ^ 4

/-- 23.15.6, "compare also 23.15.2": `λ(τ) = k²` with `k = θ₂²/θ₃²`. -/
@[dlmf 23.15.E6]
theorem modularLambda_eq_modulus_sq (τ : ℂ) : modularLambda τ = jacobiModulusOfTau τ ^ 2 := by
  rw [modularLambda, jacobiModulusOfTau, div_pow, ← pow_mul, ← pow_mul]

/-- DLMF 23.15.8: `θ₁'(0|τ) = ∂θ₁(z|τ)/∂z` at `z = 0` (the definition of
`jacobiThetaOneDerivNullTau`). -/
@[dlmf 23.15.E8]
theorem jacobiThetaOneDerivNullTau_eq (τ : ℂ) :
    jacobiThetaOneDerivNullTau τ = deriv (fun z ↦ jacobiThetaOneTau z τ) 0 := rfl

/-! ### §23.18 The Dedekind sum and the eta multiplier -/

/-- The Dedekind sum `s(d, c) = ∑_{r=1}^{c-1} (r/c)(dr/c - ⌊dr/c⌋ - 1/2)` (DLMF 23.18.7, as
corrected in DLMF V1.0.11: no coprimality condition on `r`), for `c > 0`. -/
@[dlmf 23.18.E7]
def dedekindSum (d c : ℤ) : ℝ :=
  ∑ r ∈ Finset.Ico (1 : ℤ) c, (r / c : ℝ) * ((d * r / c : ℝ) - ⌊(d * r / c : ℝ)⌋ - 1 / 2)

/-- The eta multiplier `ε(𝒜) = exp(πi((a + d)/(12c) + s(-d, c)))` (DLMF 23.18.6), `c > 0`. -/
@[dlmf 23.18.E6]
def etaMultiplier (A : SL(2, ℤ)) : ℂ :=
  cexp (π * I * (((A 0 0 + A 1 1 : ℤ) : ℂ) / (12 * (A 1 0 : ℂ)) +
    (dedekindSum (-A 1 1) (A 1 0) : ℂ)))

end DLMF.Weierstrass

end
