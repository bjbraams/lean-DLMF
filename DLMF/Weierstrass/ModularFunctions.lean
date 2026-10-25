/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Weierstrass.Basic
public import DLMF.JacobiElliptic.Basic
public import DLMF.Theta.Basic
public import Mathlib.NumberTheory.ModularForms.DedekindEta
public import Mathlib.NumberTheory.ModularForms.Discriminant
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty

/-!
# Elliptic modular functions (DLMF §§23.15–23.19)

We define the elliptic modular function `λ(τ)` (23.15.6) and Klein's complete invariant `J(τ)`
(23.15.7) from the project's theta functions in lattice-parameter form `θⱼ(0|τ)`
(`DLMF.Theta.jacobiThetaTwoNullTau` etc.); Dedekind's eta function is Mathlib's
`ModularForm.eta`. DLMF writes `θⱼ(0, q)` with `q = e^{iπτ}`; the nome form of `θ₂` and of `θ₁'`
carries a branch of `q^{1/4}` which only changes them by a fourth root of unity, and `λ`
(fourth powers) and `J` (eighth powers) are unaffected by it.

The bilinear transformation `𝒜τ = (aτ + b)/(cτ + d)` of 23.15.3 is the Möbius action of
`SL(2, ℤ)` on the upper half-plane (`A • τ` for `A : SL(2, ℤ)`, `τ : ℍ`); `mobius_coe` is the
bridge to the explicit formula.

The general notions of 23.15(i) are formalized literally: the level `ℓ` is an integer or half
an odd integer, which we encode by the integer `ℓ₂ = 2ℓ`, with `(cτ + d)^ℓ` the principal
power. "Analytic at `q = 0` as a function of `q`" means that `f(τ) = F(e^{iπτ})` with `F`
analytic at `0`.

**Terminology in 23.18.** DLMF calls `J` "a modular form of level zero for `SL(2, ℤ)`", but by
23.17.5 `J` has a pole `q⁻²/1728` at `q = 0`, so it is not a modular form in the sense of
23.15(i); it is a modular function (`isModularFunction_kleinJ`).
-/

@[expose] public section

open Complex Asymptotics Matrix
open UpperHalfPlane hiding I
open scoped Real MatrixGroups ModularForm

noncomputable section

namespace DLMF.Weierstrass

open DLMF.Elliptic DLMF.Theta DLMF.JacobiElliptic

/-! ### §23.15(i) General modular functions -/

/-- DLMF 23.15.1: the nome of the modulus `k` is `q = exp(-πK'(k)/K(k)) = e^{iπτ}` with
`τ = iK'(k)/K(k)` (stated for every complex `k`, with the project's principal `K`, `K'`). -/
@[dlmf 23.15.E1]
theorem nome_eq_modulus (k : ℂ) :
    jacobiNomek k = cexp (-(π * compEllIntKpk k / compEllIntKk k)) ∧
      jacobiNomek k = cexp (π * I * jacobiTauk k) :=
  ⟨rfl, jacobiNomek_eq_exp_tau k⟩

/-- DLMF 23.15.2: for `k` in the modulus domain of DLMF 22.2 (`ℜk > 0`, and `k < 1` if `k` is
real) and `τ = iK'(k)/K(k)`, `k = θ₂²(0|τ)/θ₃²(0|τ)` and `k' = θ₄²(0|τ)/θ₃²(0|τ)`. -/
@[dlmf 23.15.E2]
theorem modulus_eq_theta {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    k = jacobiThetaTwoTau 0 (jacobiTauk k) ^ 2 / jacobiThetaThreeTau 0 (jacobiTauk k) ^ 2 ∧
      jacobiComodulusk k =
        jacobiThetaFourTau 0 (jacobiTauk k) ^ 2 / jacobiThetaThreeTau 0 (jacobiTauk k) ^ 2 := by
  obtain ⟨h1, h2, -⟩ := jacobi_inversion_k hk
  exact ⟨h1.symm, h2.symm⟩

/-- The bilinear transformation `𝒜τ = (aτ + b)/(cτ + d)` (DLMF 23.15.3) of
`𝒜 = [a b; c d] ∈ SL(2, ℤ)`. -/
@[dlmf 23.15.E3]
def mobius (A : SL(2, ℤ)) (τ : ℂ) : ℂ :=
  ((A 0 0 : ℂ) * τ + A 0 1) / ((A 1 0 : ℂ) * τ + A 1 1)

/-- DLMF 23.15.4: the entries of `𝒜 ∈ SL(2, ℤ)` satisfy `ad - bc = 1`. -/
@[dlmf 23.15.E4]
theorem mobius_det (A : SL(2, ℤ)) : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
  have h := A.2
  rwa [Matrix.det_fin_two] at h

/-- The Möbius action of `SL(2, ℤ)` on `ℍ` is the transformation 23.15.3. -/
@[dlmf 23.15.E3]
theorem mobius_coe (A : SL(2, ℤ)) (τ : ℍ) : ((A • τ : ℍ) : ℂ) = mobius A τ := by
  rw [coe_specialLinearGroup_apply, mobius]
  simp

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

/-! ### §23.15(ii) `λ(τ)`, `J(τ)`, `η(τ)` -/

/-- The elliptic modular function `λ(τ) = θ₂⁴(0|τ)/θ₃⁴(0|τ)` (DLMF 23.15.6), for `ℑτ > 0`. -/
@[dlmf 23.15.E6]
def modularLambda (τ : ℂ) : ℂ := jacobiThetaTwoNullTau τ ^ 4 / jacobiThetaThreeNullTau τ ^ 4

/-- 23.15.6, "compare also 23.15.2": `λ(τ) = k²` with `k = θ₂²/θ₃²`. -/
@[dlmf 23.15.E6]
theorem modularLambda_eq_modulus_sq (τ : ℂ) : modularLambda τ = jacobiModulusTau τ ^ 2 := by
  rw [modularLambda, jacobiModulusTau, div_pow, ← pow_mul, ← pow_mul]

/-- Klein's complete invariant
`J(τ) = (θ₂⁸(0|τ) + θ₃⁸(0|τ) + θ₄⁸(0|τ))³/(54 θ₁'(0|τ)⁸)` (DLMF 23.15.7), for `ℑτ > 0`. -/
@[dlmf 23.15.E7]
def kleinJ (τ : ℂ) : ℂ :=
  (jacobiThetaTwoNullTau τ ^ 8 + jacobiThetaThreeNullTau τ ^ 8 + jacobiThetaFourNullTau τ ^ 8) ^ 3 /
    (54 * jacobiThetaOneDerivNullTau τ ^ 8)

/-- DLMF 23.15.8: `θ₁'(0|τ) = ∂θ₁(z|τ)/∂z` at `z = 0` (the definition of
`jacobiThetaOneDerivNullTau`). -/
@[dlmf 23.15.E8]
theorem jacobiThetaOneDerivNullTau_eq (τ : ℂ) :
    jacobiThetaOneDerivNullTau τ = deriv (fun z ↦ jacobiThetaOneTau z τ) 0 := rfl

/-- DLMF 23.15.9: for `ℑτ > 0`, `η(τ)³ = θ₁'(0|τ)/2` (the cube root of DLMF being the branch
fixed by the second equality) and `η(τ) = e^{iπτ/12} θ₃(π(1 + τ)/2 | 3τ)`; `η` is Mathlib's
Dedekind eta function `ModularForm.eta`. -/
@[dlmf 23.15.E9]
theorem eta_pow_three_eq_theta (τ : ℍ) :
    η (τ : ℂ) ^ 3 = jacobiThetaOneDerivNullTau τ / 2 ∧
      η (τ : ℂ) = cexp (π * I * τ / 12) * jacobiThetaThreeTau (π * (1 + τ) / 2) (3 * τ) := by
  sorry

/-- 23.15.9, branch statement: on the positive imaginary axis `η` is real and positive. -/
@[dlmf 23.15.E9]
theorem eta_pos_of_re_eq_zero (τ : ℍ) (hτ : (τ : ℂ).re = 0) :
    (η (τ : ℂ)).im = 0 ∧ 0 < (η (τ : ℂ)).re := by
  sorry

/-! ### §23.17 Elementary properties -/

/-- DLMF 23.17.1: `λ(i) = 1/2` and `λ(e^{πi/3}) = e^{πi/3}`. -/
@[dlmf 23.17.E1]
theorem modularLambda_special :
    modularLambda I = 1 / 2 ∧ modularLambda (cexp (π * I / 3)) = cexp (π * I / 3) := by
  sorry

/-- DLMF 23.17.2: `J(i) = 1` and `J(e^{πi/3}) = 0`. -/
@[dlmf 23.17.E2]
theorem kleinJ_special : kleinJ I = 1 ∧ kleinJ (cexp (π * I / 3)) = 0 := by
  sorry

/-- DLMF 23.17.3: `η(i) = Γ(1/4)/(2π^{3/4})` and
`η(e^{πi/3}) = 3^{1/8}Γ(1/3)^{3/2}e^{πi/24}/(2π)`. -/
@[dlmf 23.17.E3]
theorem eta_special :
    η I = ((Real.Gamma (1 / 4) / (2 * π ^ (3 / 4 : ℝ)) : ℝ) : ℂ) ∧
      η (cexp (π * I / 3)) =
        ((3 ^ (1 / 8 : ℝ) * Real.Gamma (1 / 3) ^ (3 / 2 : ℝ) / (2 * π) : ℝ) : ℂ) *
        cexp (π * I / 24) := by
  sorry

/-- DLMF 23.17.4: `λ(τ) = 16q(1 - 8q + 44q² + O(q³))` as `q = e^{iπτ} → 0`. -/
@[dlmf 23.17.E4]
theorem modularLambda_isBigO :
    (fun τ : ℍ ↦ modularLambda τ - 16 * cexp (π * I * τ) *
        (1 - 8 * cexp (π * I * τ) + 44 * cexp (π * I * τ) ^ 2)) =O[atImInfty]
      fun τ ↦ cexp (π * I * τ) ^ 4 := by
  sorry

/-- DLMF 23.17.5: `1728J(τ) = q⁻² + 744 + 196884q² + 21493760q⁴ + O(q⁶)` as
`q = e^{iπτ} → 0`. -/
@[dlmf 23.17.E5]
theorem kleinJ_isBigO :
    (fun τ : ℍ ↦ 1728 * kleinJ τ - (cexp (π * I * τ) ^ (-2 : ℤ) + 744 +
        196884 * cexp (π * I * τ) ^ 2 + 21493760 * cexp (π * I * τ) ^ 4)) =O[atImInfty]
      fun τ ↦ cexp (π * I * τ) ^ 6 := by
  sorry

/-- DLMF 23.17.6: `η(τ) = ∑_{n∈ℤ} (-1)ⁿ q^{(6n+1)²/12}` with `q^{(6n+1)²/12} = e^{iπτ(6n+1)²/12}`,
for `ℑτ > 0` (Euler's pentagonal number theorem). -/
@[dlmf 23.17.E6]
theorem eta_hasSum (τ : ℍ) :
    HasSum (fun n : ℤ ↦ (-1) ^ n * cexp (π * I * τ * (6 * n + 1) ^ 2 / 12)) (η (τ : ℂ)) := by
  sorry

/-- DLMF 23.17.7: `λ(τ) = 16q ∏_{n≥1} ((1 + q^{2n})/(1 + q^{2n-1}))⁸`, `q = e^{iπτ}`, `ℑτ > 0`. -/
@[dlmf 23.17.E7]
theorem modularLambda_hasProd (τ : ℍ) :
    HasProd (fun n : ℕ ↦ ((1 + cexp (π * I * τ) ^ (2 * (n + 1))) /
        (1 + cexp (π * I * τ) ^ (2 * n + 1))) ^ 8)
      (modularLambda τ / (16 * cexp (π * I * τ))) := by
  sorry

/-- `e^{2πiτ} = (e^{iπτ})²`. -/
theorem wp23_cexp_two_pi (τ : ℂ) : cexp (2 * π * I * τ) = cexp (π * I * τ) ^ 2 := by
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- DLMF 23.17.8: `η(τ) = q^{1/12} ∏_{n≥1} (1 - q^{2n})` with `q^{1/12} = e^{iπτ/12}`,
`ℑτ > 0`; the product converges. -/
@[dlmf 23.17.E8]
theorem eta_hasProd (τ : ℍ) :
    HasProd (fun n : ℕ ↦ 1 - cexp (π * I * τ) ^ (2 * (n + 1)))
        (∏' n : ℕ, (1 - cexp (π * I * τ) ^ (2 * (n + 1)))) ∧
      η (τ : ℂ) = cexp (π * I * τ / 12) *
        ∏' n : ℕ, (1 - cexp (π * I * τ) ^ (2 * (n + 1))) := by
  have hq : ∀ n : ℕ, cexp (π * I * τ) ^ (2 * (n + 1)) = cexp (2 * π * I * τ) ^ (n + 1) := by
    intro n
    rw [pow_mul, wp23_cexp_two_pi]
  simp_rw [hq]
  refine ⟨(ModularForm.multipliable_one_sub_pow ?_).hasProd, ?_⟩
  · rw [Complex.norm_exp]
    rw [Real.exp_lt_one_iff]
    have : (2 * π * I * (τ : ℂ)).re = -(2 * π * τ.im) := by simp
    rw [this]
    have := τ.im_pos
    have := Real.pi_pos
    nlinarith
  · rw [ModularForm.eta, Function.Periodic.qParam]
    simp_rw [ModularForm.eta_q_eq_pow]
    congr 2
    push_cast
    ring

/-! ### §23.18 Modular transformations -/

/-- DLMF 23.18.1–23.18.2: `λ(𝒜τ)` equals `λ`, `1 - λ`, `1/λ`, `1/(1 - λ)`, `λ/(λ - 1)`,
`1 - 1/λ` according as `[a b; c d]` has parities `[o e; e o]`, `[e o; o e]`, `[o e; o o]`,
`[e o; o o]`, `[o o; e o]`, `[o o; o e]` (`e` even, `o` odd), for `ℑτ > 0`. -/
@[dlmf 23.18.E1, dlmf 23.18.E2]
theorem modularLambda_smul (A : SL(2, ℤ)) (τ : ℍ) :
    let a := A 0 0; let b := A 0 1; let c := A 1 0; let d := A 1 1
    let l := modularLambda τ; let l' := modularLambda (A • τ : ℍ)
    (Odd a → Even b → Even c → Odd d → l' = l) ∧
    (Even a → Odd b → Odd c → Even d → l' = 1 - l) ∧
    (Odd a → Even b → Odd c → Odd d → l' = 1 / l) ∧
    (Even a → Odd b → Odd c → Odd d → l' = 1 / (1 - l)) ∧
    (Odd a → Odd b → Even c → Odd d → l' = l / (l - 1)) ∧
    (Odd a → Odd b → Odd c → Even d → l' = 1 - 1 / l) := by
  sorry

/-- DLMF 23.18.3: if `a - 1, b, c, d - 1` are all even then `λ(𝒜τ) = λ(τ)`. -/
@[dlmf 23.18.E3]
theorem modularLambda_smul_of_even (A : SL(2, ℤ)) (τ : ℍ) (ha : Even (A 0 0 - 1))
    (hb : Even (A 0 1)) (hc : Even (A 1 0)) (hd : Even (A 1 1 - 1)) :
    modularLambda (A • τ : ℍ) = modularLambda τ := by
  have hao : Odd (A 0 0) := by
    obtain ⟨r, hr⟩ := ha; exact ⟨r, by omega⟩
  have hdo : Odd (A 1 1) := by
    obtain ⟨r, hr⟩ := hd; exact ⟨r, by omega⟩
  exact (modularLambda_smul A τ).1 hao hb hc hdo

/-- §23.18 after 23.18.3: `λ` is a cusp form of level zero for the subgroup of 23.18.3, which is
the principal congruence subgroup `Γ(2)`. -/
@[dlmf 23.18.E3]
theorem isCuspForm_modularLambda : IsCuspForm (CongruenceSubgroup.Gamma 2) 0 modularLambda := by
  sorry

/-- DLMF 23.18.4: `J(𝒜τ) = J(τ)` for `𝒜 ∈ SL(2, ℤ)`, `ℑτ > 0`. -/
@[dlmf 23.18.E4]
theorem kleinJ_smul (A : SL(2, ℤ)) (τ : ℍ) : kleinJ (A • τ : ℍ) = kleinJ τ := by
  sorry

/-- §23.18 after 23.18.4: `J` is a modular function of level zero for `SL(2, ℤ)`.
Corrected from the printed DLMF statement: DLMF calls `J` a "modular form of level zero", but `J`
has a pole at `q = 0`, so it is not a modular form in the sense of DLMF 23.15(i) (which requires
analyticity at `q = 0`); it is a modular function. -/
@[dlmf 23.18.E4]
theorem isModularFunction_kleinJ : IsModularFunction ⊤ 0 kleinJ := by
  sorry

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

/-- DLMF 23.18.5: for `𝒜 ∈ SL(2, ℤ)` with `c > 0` and `ℑτ > 0`,
`η(𝒜τ) = ε(𝒜)(-i(cτ + d))^{1/2} η(τ)` with the principal square root. -/
@[dlmf 23.18.E5]
theorem eta_smul (A : SL(2, ℤ)) (hc : 0 < A 1 0) (τ : ℍ) :
    η (A • τ : ℍ) = etaMultiplier A * (-I * ((A 1 0 : ℂ) * τ + A 1 1)) ^ (1 / 2 : ℂ) *
      η (τ : ℂ) := by
  sorry

/-- §23.18, last sentence: `η` is a modular function of level `1/2` for `SL(2, ℤ)`. -/
@[dlmf 23.18.E5]
theorem isModularFunction_eta : IsModularFunction ⊤ 1 ModularForm.eta := by
  sorry

/-! ### §23.19 Interrelations -/

/-- DLMF 23.19.1: `λ(τ) = 16(η²(2τ)η(τ/2)/η³(τ))⁸`, `ℑτ > 0`. -/
@[dlmf 23.19.E1]
theorem modularLambda_eq_eta (τ : ℍ) :
    modularLambda τ = 16 * (η (2 * τ) ^ 2 * η ((τ : ℂ) / 2) / η (τ : ℂ) ^ 3) ^ 8 := by
  sorry

/-- DLMF 23.19.2: `J(τ) = (4/27)(1 - λ + λ²)³/(λ(1 - λ))²`, `ℑτ > 0`. -/
@[dlmf 23.19.E2]
theorem kleinJ_eq_modularLambda (τ : ℍ) :
    kleinJ τ = 4 / 27 * (1 - modularLambda τ + modularLambda τ ^ 2) ^ 3 /
      (modularLambda τ * (1 - modularLambda τ)) ^ 2 := by
  sorry

/-- DLMF 23.19.3: `J(τ) = g₂³/(g₂³ - 27g₃²)` for the invariants of the lattice with generators
`1` and `τ` (half-periods `ω₁ = 1/2`, `ω₃ = τ/2`), `ℑτ > 0`. -/
@[dlmf 23.19.E3]
theorem kleinJ_eq_invariants (τ : ℍ) :
    kleinJ τ = (HalfPeriods.ofTau (1 / 2) (by norm_num) τ).g₂ ^ 3 /
      ((HalfPeriods.ofTau (1 / 2) (by norm_num) τ).g₂ ^ 3 -
        27 * (HalfPeriods.ofTau (1 / 2) (by norm_num) τ).g₃ ^ 2) := by
  sorry

/-- DLMF 23.19.4: `Δ = (2π)¹²η²⁴(τ)` for the lattice with generators `1` and `τ`, `ℑτ > 0`. -/
@[dlmf 23.19.E4]
theorem latticeDiscriminant_eq_eta (τ : ℍ) :
    latticeDiscriminant (HalfPeriods.ofTau (1 / 2) (by norm_num) τ).periodPair =
      (2 * π) ^ 12 * η (τ : ℂ) ^ 24 := by
  sorry

end DLMF.Weierstrass
