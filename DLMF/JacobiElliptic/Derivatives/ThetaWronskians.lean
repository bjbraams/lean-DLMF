/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.JacobiElliptic.AnalyticProperties
public import DLMF.JacobiElliptic.ElementaryIdentities
public import DLMF.Elliptic.Jacobi

/-!
# Theta Wronskians and Jacobi derivatives

Theta-function Wronskians and quotient differentiation give the complex derivative table,
DLMF Table 22.13.1, for the twelve Jacobian elliptic functions, with `k ∈ jacobiModulusDomain`
and away from the poles.

## Main definitions

* `jacobiLetterThetaConst`, `jacobiLetterThetaRaw`: the normalizing constant and the raw theta
  function of a Glaisher letter.

## Main results

* `hasDerivAt_jacobiPQ`: the derivative of a general quotient `pq(z, k)`.
* `jacobiCd_sq_add_jacobiComodulus_sq_mul_jacobiSd_sq`, `jacobiNc_sq_sub_jacobiSc_sq`,
  `jacobiNs_sq_sub_jacobiCs_sq` and companions: sums of squares for the quotient functions.
* `hasDerivAt_jacobiSn`, `hasDerivAt_jacobiCn`, `hasDerivAt_jacobiDn`: `sn' = cn dn`,
  `cn' = -sn dn`, `dn' = -k² sn cn`.
* `hasDerivAt_jacobiCd`, `hasDerivAt_jacobiSd`, `hasDerivAt_jacobiNd`,
  `hasDerivAt_jacobiDc`, `hasDerivAt_jacobiNc`, `hasDerivAt_jacobiSc`,
  `hasDerivAt_jacobiNs`, `hasDerivAt_jacobiDs`, `hasDerivAt_jacobiCs`: the remaining entries
  of Table 22.13.1.
-/

@[expose] public section

open Complex DLMF.Elliptic

open scoped Real Topology

noncomputable section

namespace DLMF.JacobiElliptic

open DLMF.EllipticIntegrals (completeEllipticK completeEllipticKPrime)

local notation "θ₁" => jacobiThetaOneTau

local notation "θ₂" => jacobiThetaTwoTau

local notation "θ₃" => jacobiThetaThreeTau

local notation "θ₄" => jacobiThetaFourTau

/-- Identity under the stated parameter and domain assumptions: `deriv f 0 = 0`. -/
private lemma deriv_zero_of_even {f : ℂ → ℂ} (hf : Differentiable ℂ f) (he : ∀ z, f (-z) = f z) :
    deriv f 0 = 0 :=
  DLMF.Theta.deriv_zero_of_even hf he

/-- Identity under the stated parameter and domain assumptions: `κ * (f' * g x - f x * g') = A x *
b' + C x * e'`. -/
private lemma wronskian_eq_of_mul_sub_eq_add {f g A B C E : ℂ → ℂ} {f' g' b' e' : ℂ} (κ x : ℂ)
    (hfg : ∀ y, κ * (f (x + y) * g (x - y)) = A x * B y + C x * E y)
    (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) (hB : HasDerivAt B b' 0)
    (hE : HasDerivAt E e' 0) : κ * (f' * g x - f x * g') = A x * b' + C x * e' := by
  have hf' : HasDerivAt f f' (x + 0) := by rwa [add_zero]
  have hg' : HasDerivAt g g' (x - 0) := by rwa [sub_zero]
  have hL := ((hf'.comp_const_add x 0).mul (hg'.comp_const_sub x 0)).const_mul κ
  have hR := (hB.const_mul (A x)).add (hE.const_mul (C x))
  have hL2 : HasDerivAt (fun y => A x * B y + C x * E y)
      (κ * (f' * g (x - 0) + f (x + 0) * -g')) 0 := by
    convert hL using 1; funext y; exact (hfg y).symm
  have := hL2.unique hR
  simp only [add_zero, sub_zero] at this
  linear_combination this

section
variable {τ : ℂ} (hτ : 0 < τ.im)
include hτ

/-- At `z`, the function `(fun w => θ₁ w τ)` has derivative `(deriv (fun w => θ₁ w τ) z)`. -/
private lemma hasDerivAt_jacobiThetaOneTau (z : ℂ) : HasDerivAt (fun w => θ₁ w τ)
    (deriv (fun w => θ₁ w τ) z) z :=
  ((DLMF.Theta.differentiable_jacobiThetaTau 1 hτ) z).hasDerivAt
/-- At `z`, the function `(fun w => θ₂ w τ)` has derivative `(deriv (fun w => θ₂ w τ) z)`. -/
private lemma hasDerivAt_jacobiThetaTwoTau (z : ℂ) : HasDerivAt (fun w => θ₂ w τ)
    (deriv (fun w => θ₂ w τ) z) z :=
  ((DLMF.Theta.differentiable_jacobiThetaTau 2 hτ) z).hasDerivAt
/-- At `z`, the function `(fun w => θ₃ w τ)` has derivative `(deriv (fun w => θ₃ w τ) z)`. -/
private lemma hasDerivAt_jacobiThetaThreeTau (z : ℂ) : HasDerivAt (fun w => θ₃ w τ)
    (deriv (fun w => θ₃ w τ) z) z :=
  ((DLMF.Theta.differentiable_jacobiThetaTau 3 hτ) z).hasDerivAt
/-- At `z`, the function `(fun w => θ₄ w τ)` has derivative `(deriv (fun w => θ₄ w τ) z)`. -/
theorem hasDerivAt_jacobiThetaFourTau (z : ℂ) : HasDerivAt (fun w => θ₄ w τ)
    (deriv (fun w => θ₄ w τ) z) z :=
  ((DLMF.Theta.differentiable_jacobiThetaTau 4 hτ) z).hasDerivAt

/-- Identity under the stated parameter and domain assumptions: `deriv (fun w => θ₂ w τ) 0 = 0`. -/
private lemma deriv_jacobiThetaTwoTau_zero : deriv (fun w => θ₂ w τ) 0 = 0 :=
  deriv_zero_of_even (DLMF.Theta.differentiable_jacobiThetaTau 2 hτ)
    fun z => jacobiThetaTwoTau_neg z τ
/-- Identity under the stated parameter and domain assumptions: `deriv (fun w => θ₃ w τ) 0 = 0`. -/
private lemma deriv_jacobiThetaThreeTau_zero : deriv (fun w => θ₃ w τ) 0 = 0 :=
  deriv_zero_of_even (DLMF.Theta.differentiable_jacobiThetaTau 3 hτ)
    fun z => jacobiThetaThreeTau_neg z τ
/-- Identity under the stated parameter and domain assumptions: `deriv (fun w => θ₄ w τ) 0 = 0`. -/
private lemma deriv_jacobiThetaFourTau_zero : deriv (fun w => θ₄ w τ) 0 = 0 :=
  deriv_zero_of_even (DLMF.Theta.differentiable_jacobiThetaTau 4 hτ)
    fun z => jacobiThetaFourTau_neg z τ
/-- Identity under the stated parameter and domain assumptions: `deriv (fun w => θ₁ w τ) 0 = θ₂ 0
τ * θ₃ 0 τ * θ₄ 0 τ`. -/
private lemma deriv_jacobiThetaOneTau_zero : deriv (fun w => θ₁ w τ) 0 = θ₂ 0 τ * θ₃ 0 τ * θ₄ 0 τ :=
  DLMF.Theta.jacobiThetaOneDerivNullTau_eq_mul hτ

/-- Wronskian `θ₁'θ₄ - θ₁θ₄' = θ₄(0)² θ₂θ₃`. -/
private lemma jacobiThetaTau_wronskian_one_four (x : ℂ) :
    deriv (fun w => θ₁ w τ) x * θ₄ x τ - θ₁ x τ * deriv (fun w => θ₄ w τ) x =
      θ₄ 0 τ ^ 2 * (θ₂ x τ * θ₃ x τ) := by
  have h := wronskian_eq_of_mul_sub_eq_add (f := fun w => θ₁ w τ) (g := fun w => θ₄ w τ)
    (A := fun w => θ₁ w τ * θ₄ w τ) (B := fun w => θ₂ w τ * θ₃ w τ)
    (C := fun w => θ₂ w τ * θ₃ w τ) (E := fun w => θ₁ w τ * θ₄ w τ) (θ₂ 0 τ * θ₃ 0 τ) x
    (fun y => jacobiThetaOneTau_add_mul_jacobiThetaFourTau_sub x y τ hτ)
        (hasDerivAt_jacobiThetaOneTau hτ x) (hasDerivAt_jacobiThetaFourTau hτ x)
    ((hasDerivAt_jacobiThetaTwoTau hτ 0).mul (hasDerivAt_jacobiThetaThreeTau hτ 0))
        ((hasDerivAt_jacobiThetaOneTau hτ 0).mul (hasDerivAt_jacobiThetaFourTau hτ 0))
  simp only [deriv_jacobiThetaOneTau_zero hτ, deriv_jacobiThetaTwoTau_zero hτ,
      deriv_jacobiThetaThreeTau_zero hτ, deriv_jacobiThetaFourTau_zero hτ,
    jacobiThetaOneTau_zero] at h
  obtain ⟨h2, h3, -, -⟩ := jacobiThetaTau_zero_ne_zero_and_pow_four τ hτ
  apply mul_left_cancel₀ (mul_ne_zero h2 h3)
  linear_combination h

/-- Identity under the stated parameter and domain assumptions: `deriv (fun w => θ₂ w τ) x * θ₄ x
τ - θ₂ x τ * deriv (fun w => θ₄ w τ) x = -(θ₃ 0 τ ^ 2 * (θ₁ x τ * θ₃ x τ))`. -/
private lemma jacobiThetaTau_wronskian_two_four (x : ℂ) :
    deriv (fun w => θ₂ w τ) x * θ₄ x τ - θ₂ x τ * deriv (fun w => θ₄ w τ) x =
      -(θ₃ 0 τ ^ 2 * (θ₁ x τ * θ₃ x τ)) := by
  have h := wronskian_eq_of_mul_sub_eq_add (f := fun w => θ₂ w τ) (g := fun w => θ₄ w τ)
    (A := fun w => θ₂ w τ * θ₄ w τ) (B := fun w => θ₂ w τ * θ₄ w τ)
    (C := fun w => -(θ₁ w τ * θ₃ w τ)) (E := fun w => θ₁ w τ * θ₃ w τ) (θ₂ 0 τ * θ₄ 0 τ) x
    (fun y => by have := jacobiThetaTwoTau_add_mul_jacobiThetaFourTau_sub x y τ hτ;
                 linear_combination this)
    (hasDerivAt_jacobiThetaTwoTau hτ x) (hasDerivAt_jacobiThetaFourTau hτ x)
    ((hasDerivAt_jacobiThetaTwoTau hτ 0).mul (hasDerivAt_jacobiThetaFourTau hτ 0))
        ((hasDerivAt_jacobiThetaOneTau hτ 0).mul (hasDerivAt_jacobiThetaThreeTau hτ 0))
  simp only [deriv_jacobiThetaOneTau_zero hτ, deriv_jacobiThetaTwoTau_zero hτ,
      deriv_jacobiThetaThreeTau_zero hτ, deriv_jacobiThetaFourTau_zero hτ,
    jacobiThetaOneTau_zero] at h
  obtain ⟨h2, h3, h4, -⟩ := jacobiThetaTau_zero_ne_zero_and_pow_four τ hτ
  apply mul_left_cancel₀ (mul_ne_zero h2 h4)
  linear_combination h

/-- Identity under the stated parameter and domain assumptions: `deriv (fun w => θ₃ w τ) x * θ₄ x
τ - θ₃ x τ * deriv (fun w => θ₄ w τ) x = -(θ₂ 0 τ ^ 2 * (θ₁ x τ * θ₂ x τ))`. -/
private lemma jacobiThetaTau_wronskian_three_four (x : ℂ) :
    deriv (fun w => θ₃ w τ) x * θ₄ x τ - θ₃ x τ * deriv (fun w => θ₄ w τ) x =
      -(θ₂ 0 τ ^ 2 * (θ₁ x τ * θ₂ x τ)) := by
  have h := wronskian_eq_of_mul_sub_eq_add (f := fun w => θ₃ w τ) (g := fun w => θ₄ w τ)
    (A := fun w => θ₃ w τ * θ₄ w τ) (B := fun w => θ₃ w τ * θ₄ w τ)
    (C := fun w => -(θ₁ w τ * θ₂ w τ)) (E := fun w => θ₁ w τ * θ₂ w τ) (θ₃ 0 τ * θ₄ 0 τ) x
    (fun y => by have := jacobiThetaThreeTau_add_mul_jacobiThetaFourTau_sub x y τ hτ;
                 linear_combination this)
    (hasDerivAt_jacobiThetaThreeTau hτ x) (hasDerivAt_jacobiThetaFourTau hτ x)
    ((hasDerivAt_jacobiThetaThreeTau hτ 0).mul (hasDerivAt_jacobiThetaFourTau hτ 0))
        ((hasDerivAt_jacobiThetaOneTau hτ 0).mul (hasDerivAt_jacobiThetaTwoTau hτ 0))
  simp only [deriv_jacobiThetaOneTau_zero hτ, deriv_jacobiThetaTwoTau_zero hτ,
      deriv_jacobiThetaThreeTau_zero hτ, deriv_jacobiThetaFourTau_zero hτ,
    jacobiThetaOneTau_zero] at h
  obtain ⟨h2, h3, h4, -⟩ := jacobiThetaTau_zero_ne_zero_and_pow_four τ hτ
  apply mul_left_cancel₀ (mul_ne_zero h3 h4)
  linear_combination h

/-- Identity under the stated parameter and domain assumptions: `deriv (fun w => θ₂ w τ) x * θ₃ x
τ - θ₂ x τ * deriv (fun w => θ₃ w τ) x = -(θ₄ 0 τ ^ 2 * (θ₁ x τ * θ₄ x τ))`. -/
private lemma jacobiThetaTau_wronskian_two_three (x : ℂ) :
    deriv (fun w => θ₂ w τ) x * θ₃ x τ - θ₂ x τ * deriv (fun w => θ₃ w τ) x =
      -(θ₄ 0 τ ^ 2 * (θ₁ x τ * θ₄ x τ)) := by
  have h := wronskian_eq_of_mul_sub_eq_add (f := fun w => θ₂ w τ) (g := fun w => θ₃ w τ)
    (A := fun w => θ₂ w τ * θ₃ w τ) (B := fun w => θ₂ w τ * θ₃ w τ)
    (C := fun w => -(θ₁ w τ * θ₄ w τ)) (E := fun w => θ₁ w τ * θ₄ w τ) (θ₂ 0 τ * θ₃ 0 τ) x
    (fun y => by have := jacobiThetaTwoTau_add_mul_jacobiThetaThreeTau_sub x y τ hτ;
                 linear_combination this)
    (hasDerivAt_jacobiThetaTwoTau hτ x) (hasDerivAt_jacobiThetaThreeTau hτ x)
    ((hasDerivAt_jacobiThetaTwoTau hτ 0).mul (hasDerivAt_jacobiThetaThreeTau hτ 0))
        ((hasDerivAt_jacobiThetaOneTau hτ 0).mul (hasDerivAt_jacobiThetaFourTau hτ 0))
  simp only [deriv_jacobiThetaOneTau_zero hτ, deriv_jacobiThetaTwoTau_zero hτ,
      deriv_jacobiThetaThreeTau_zero hτ, deriv_jacobiThetaFourTau_zero hτ,
    jacobiThetaOneTau_zero] at h
  obtain ⟨h2, h3, h4, -⟩ := jacobiThetaTau_zero_ne_zero_and_pow_four τ hτ
  apply mul_left_cancel₀ (mul_ne_zero h2 h3)
  linear_combination h

/-- Identity under the stated parameter and domain assumptions: `deriv (fun w => θ₁ w τ) x * θ₃ x
τ - θ₁ x τ * deriv (fun w => θ₃ w τ) x = θ₃ 0 τ ^ 2 * (θ₂ x τ * θ₄ x τ)`. -/
private lemma jacobiThetaTau_wronskian_one_three (x : ℂ) :
    deriv (fun w => θ₁ w τ) x * θ₃ x τ - θ₁ x τ * deriv (fun w => θ₃ w τ) x =
      θ₃ 0 τ ^ 2 * (θ₂ x τ * θ₄ x τ) := by
  have h := wronskian_eq_of_mul_sub_eq_add (f := fun w => θ₁ w τ) (g := fun w => θ₃ w τ)
    (A := fun w => θ₂ w τ * θ₄ w τ) (B := fun w => θ₁ w τ * θ₃ w τ)
    (C := fun w => θ₁ w τ * θ₃ w τ) (E := fun w => θ₂ w τ * θ₄ w τ) (θ₂ 0 τ * θ₄ 0 τ) x
    (fun y => by have := jacobiThetaOneTau_add_mul_jacobiThetaThreeTau_sub x y τ hτ;
                 linear_combination this)
    (hasDerivAt_jacobiThetaOneTau hτ x) (hasDerivAt_jacobiThetaThreeTau hτ x)
    ((hasDerivAt_jacobiThetaOneTau hτ 0).mul (hasDerivAt_jacobiThetaThreeTau hτ 0))
        ((hasDerivAt_jacobiThetaTwoTau hτ 0).mul (hasDerivAt_jacobiThetaFourTau hτ 0))
  simp only [deriv_jacobiThetaOneTau_zero hτ, deriv_jacobiThetaTwoTau_zero hτ,
      deriv_jacobiThetaThreeTau_zero hτ, deriv_jacobiThetaFourTau_zero hτ,
    jacobiThetaOneTau_zero] at h
  obtain ⟨h2, h3, h4, -⟩ := jacobiThetaTau_zero_ne_zero_and_pow_four τ hτ
  apply mul_left_cancel₀ (mul_ne_zero h2 h4)
  linear_combination h

/-- Identity under the stated parameter and domain assumptions: `deriv (fun w => θ₁ w τ) x * θ₂ x
τ - θ₁ x τ * deriv (fun w => θ₂ w τ) x = θ₂ 0 τ ^ 2 * (θ₃ x τ * θ₄ x τ)`. -/
private lemma jacobiThetaTau_wronskian_one_two (x : ℂ) :
    deriv (fun w => θ₁ w τ) x * θ₂ x τ - θ₁ x τ * deriv (fun w => θ₂ w τ) x =
      θ₂ 0 τ ^ 2 * (θ₃ x τ * θ₄ x τ) := by
  have h := wronskian_eq_of_mul_sub_eq_add (f := fun w => θ₁ w τ) (g := fun w => θ₂ w τ)
    (A := fun w => θ₁ w τ * θ₂ w τ) (B := fun w => θ₃ w τ * θ₄ w τ)
    (C := fun w => θ₃ w τ * θ₄ w τ) (E := fun w => θ₁ w τ * θ₂ w τ) (θ₃ 0 τ * θ₄ 0 τ) x
    (fun y => by have := jacobiThetaOneTau_add_mul_jacobiThetaTwoTau_sub x y τ hτ;
                 linear_combination this)
    (hasDerivAt_jacobiThetaOneTau hτ x) (hasDerivAt_jacobiThetaTwoTau hτ x)
    ((hasDerivAt_jacobiThetaThreeTau hτ 0).mul (hasDerivAt_jacobiThetaFourTau hτ 0))
        ((hasDerivAt_jacobiThetaOneTau hτ 0).mul (hasDerivAt_jacobiThetaTwoTau hτ 0))
  simp only [deriv_jacobiThetaOneTau_zero hτ, deriv_jacobiThetaTwoTau_zero hτ,
      deriv_jacobiThetaThreeTau_zero hτ, deriv_jacobiThetaFourTau_zero hτ,
    jacobiThetaOneTau_zero] at h
  obtain ⟨h2, h3, h4, -⟩ := jacobiThetaTau_zero_ne_zero_and_pow_four τ hτ
  apply mul_left_cancel₀ (mul_ne_zero h3 h4)
  linear_combination h

/-- Identity under the stated parameter and domain assumptions: `deriv (fun w => θ₄ w τ) x * θ₁ x
τ - θ₄ x τ * deriv (fun w => θ₁ w τ) x = -(θ₄ 0 τ ^ 2 * (θ₂ x τ * θ₃ x τ))`. -/
private lemma jacobiThetaTau_wronskian_four_one (x : ℂ) :
    deriv (fun w => θ₄ w τ) x * θ₁ x τ - θ₄ x τ * deriv (fun w => θ₁ w τ) x =
      -(θ₄ 0 τ ^ 2 * (θ₂ x τ * θ₃ x τ)) := by
  linear_combination -(jacobiThetaTau_wronskian_one_four hτ x)

/-- Identity under the stated parameter and domain assumptions: `deriv (fun w => θ₄ w τ) x * θ₂ x
τ - θ₄ x τ * deriv (fun w => θ₂ w τ) x = -(-(θ₃ 0 τ ^ 2 * (θ₁ x τ * θ₃ x τ)))`. -/
private lemma jacobiThetaTau_wronskian_four_two (x : ℂ) :
    deriv (fun w => θ₄ w τ) x * θ₂ x τ - θ₄ x τ * deriv (fun w => θ₂ w τ) x =
      -(-(θ₃ 0 τ ^ 2 * (θ₁ x τ * θ₃ x τ))) := by
  linear_combination -(jacobiThetaTau_wronskian_two_four hτ x)

/-- Identity under the stated parameter and domain assumptions: `deriv (fun w => θ₄ w τ) x * θ₃ x
τ - θ₄ x τ * deriv (fun w => θ₃ w τ) x = -(-(θ₂ 0 τ ^ 2 * (θ₁ x τ * θ₂ x τ)))`. -/
private lemma jacobiThetaTau_wronskian_four_three (x : ℂ) :
    deriv (fun w => θ₄ w τ) x * θ₃ x τ - θ₄ x τ * deriv (fun w => θ₃ w τ) x =
      -(-(θ₂ 0 τ ^ 2 * (θ₁ x τ * θ₂ x τ))) := by
  linear_combination -(jacobiThetaTau_wronskian_three_four hτ x)

/-- Identity under the stated parameter and domain assumptions: `deriv (fun w => θ₃ w τ) x * θ₂ x
τ - θ₃ x τ * deriv (fun w => θ₂ w τ) x = -(-(θ₄ 0 τ ^ 2 * (θ₁ x τ * θ₄ x τ)))`. -/
private lemma jacobiThetaTau_wronskian_three_two (x : ℂ) :
    deriv (fun w => θ₃ w τ) x * θ₂ x τ - θ₃ x τ * deriv (fun w => θ₂ w τ) x =
      -(-(θ₄ 0 τ ^ 2 * (θ₁ x τ * θ₄ x τ))) := by
  linear_combination -(jacobiThetaTau_wronskian_two_three hτ x)

/-- Identity under the stated parameter and domain assumptions: `deriv (fun w => θ₃ w τ) x * θ₁ x
τ - θ₃ x τ * deriv (fun w => θ₁ w τ) x = -(θ₃ 0 τ ^ 2 * (θ₂ x τ * θ₄ x τ))`. -/
private lemma jacobiThetaTau_wronskian_three_one (x : ℂ) :
    deriv (fun w => θ₃ w τ) x * θ₁ x τ - θ₃ x τ * deriv (fun w => θ₁ w τ) x =
      -(θ₃ 0 τ ^ 2 * (θ₂ x τ * θ₄ x τ)) := by
  linear_combination -(jacobiThetaTau_wronskian_one_three hτ x)

/-- Identity under the stated parameter and domain assumptions: `deriv (fun w => θ₂ w τ) x * θ₁ x
τ - θ₂ x τ * deriv (fun w => θ₁ w τ) x = -(θ₂ 0 τ ^ 2 * (θ₃ x τ * θ₄ x τ))`. -/
private lemma jacobiThetaTau_wronskian_two_one (x : ℂ) :
    deriv (fun w => θ₂ w τ) x * θ₁ x τ - θ₂ x τ * deriv (fun w => θ₁ w τ) x =
      -(θ₂ 0 τ ^ 2 * (θ₃ x τ * θ₄ x τ)) := by
  linear_combination -(jacobiThetaTau_wronskian_one_two hτ x)

end

/-- Normalizing constant of `jacobiLetterTheta` (helper). -/
noncomputable def jacobiLetterThetaConst : JacobiLetter → ℂ → ℂ
  | .s, τ => θ₃ 0 τ / (θ₂ 0 τ * θ₄ 0 τ)
  | .c, τ => 1 / θ₂ 0 τ
  | .d, τ => 1 / θ₃ 0 τ
  | .n, τ => 1 / θ₄ 0 τ

/-- The theta function of a letter (helper). -/
noncomputable def jacobiLetterThetaRaw : JacobiLetter → ℂ → ℂ → ℂ
  | .s => θ₁
  | .c => θ₂
  | .d => θ₃
  | .n => θ₄

/-- Identity under the stated parameter and domain assumptions:
`jacobiLetterTheta p ζ τ = jacobiLetterThetaConst p τ * jacobiLetterThetaRaw p ζ τ`. -/
theorem jacobiLetterTheta_eq_const_mul_raw (p : JacobiLetter) (ζ τ : ℂ) :
    jacobiLetterTheta p ζ τ = jacobiLetterThetaConst p τ * jacobiLetterThetaRaw p ζ τ := by
  cases p <;> simp [jacobiLetterTheta, jacobiLetterThetaConst, jacobiLetterThetaRaw] <;> ring

/-- Differentiability of the indicated parameterized function: `Differentiable ℂ (fun w =>
jacobiLetterThetaRaw p w τ)`. -/
theorem differentiable_jacobiLetterThetaRaw (p : JacobiLetter) {τ : ℂ} (hτ : 0 < τ.im) :
    Differentiable ℂ (fun w => jacobiLetterThetaRaw p w τ) := by
  cases p
  · exact DLMF.Theta.differentiable_jacobiThetaTau 1 hτ
  · exact DLMF.Theta.differentiable_jacobiThetaTau 2 hτ
  · exact DLMF.Theta.differentiable_jacobiThetaTau 3 hτ
  · exact DLMF.Theta.differentiable_jacobiThetaTau 4 hτ

/-- At `z`, the function `(fun z => jacobiPQ p q z k)` has derivative
`(jacobiLetterThetaConst p (jacobiTau k) / jacobiLetterThetaConst q (jacobiTau k) * (π / (2 *
completeEllipticK k)) * (deriv (fun w => jacobiLetterThetaRaw p w (jacobiTau k))
(jacobiThetaArgument z k) * jacobiLetterThetaRaw q (jacobiThetaArgument z k) (jacobiTau k) -
jacobiLetterThetaRaw p (jacobiThetaArgument z k) (jacobiTau k) * deriv (fun w =>
jacobiLetterThetaRaw q w (jacobiTau k)) (jacobiThetaArgument z k)) / jacobiLetterThetaRaw q
(jacobiThetaArgument z k) (jacobiTau k) ^ 2)`. -/
theorem hasDerivAt_jacobiPQ {k : ℂ} (hk : k ∈ jacobiModulusDomain) {p q : JacobiLetter}
    (hpq : p ≠ q) {z : ℂ} (hz : jacobiLetterTheta q (jacobiThetaArgument z k) (jacobiTau k) ≠ 0) :
    HasDerivAt (fun z => jacobiPQ p q z k)
      (jacobiLetterThetaConst p (jacobiTau k) / jacobiLetterThetaConst q (jacobiTau k) *
          (π / (2 * completeEllipticK k)) *
        (deriv (fun w => jacobiLetterThetaRaw p w (jacobiTau k)) (jacobiThetaArgument z k) *
            jacobiLetterThetaRaw q (jacobiThetaArgument z k) (jacobiTau k) -
          jacobiLetterThetaRaw p (jacobiThetaArgument z k) (jacobiTau k) *
            deriv (fun w => jacobiLetterThetaRaw q w (jacobiTau k)) (jacobiThetaArgument z k)) /
        jacobiLetterThetaRaw q (jacobiThetaArgument z k) (jacobiTau k) ^ 2) z := by
  have hτ := jacobiTau_im_pos hk
  have hK := completeEllipticK_ne_zero_of_mem_jacobiModulusDomain hk
  have hfun : (fun z => jacobiPQ p q z k) = fun z =>
      (jacobiLetterThetaConst p (jacobiTau k) *
          jacobiLetterThetaRaw p (jacobiThetaArgument z k) (jacobiTau k)) /
        (jacobiLetterThetaConst q (jacobiTau k) *
            jacobiLetterThetaRaw q (jacobiThetaArgument z k) (jacobiTau k)) := by
    funext w; simp [jacobiPQ, jacobiGlaisher, hpq, jacobiLetterTheta_eq_const_mul_raw]
  rw [hfun]
  rw [jacobiLetterTheta_eq_const_mul_raw] at hz
  have hζ : HasDerivAt (fun z => jacobiThetaArgument z k) (π / (2 * completeEllipticK k)) z := by
    have := ((hasDerivAt_id z).const_mul (π : ℂ)).div_const (2 * completeEllipticK k)
    simpa [jacobiThetaArgument] using this
  have hp := (((differentiable_jacobiLetterThetaRaw p hτ) _).hasDerivAt.comp z hζ).const_mul
    (jacobiLetterThetaConst p (jacobiTau k))
  have hq := (((differentiable_jacobiLetterThetaRaw q hτ) _).hasDerivAt.comp z hζ).const_mul
    (jacobiLetterThetaConst q (jacobiTau k))
  convert hp.div hq hz using 1
  · funext y; rfl
  have hN : jacobiLetterThetaConst q (jacobiTau k) ≠ 0 := left_ne_zero_of_mul hz
  have hT : jacobiLetterThetaRaw q (jacobiThetaArgument z k) (jacobiTau k) ≠ 0 :=
      right_ne_zero_of_mul hz
  simp only [Function.comp_def]
  field_simp

/-! ### Table 22.13.1, complex argument -/

section Complex

variable {k : ℂ}

/-- Identity under the stated parameter and domain assumptions: `jacobiCd z k ^ 2 +
jacobiComodulus k ^ 2 * jacobiSd z k ^ 2 = 1`. -/
lemma jacobiCd_sq_add_jacobiComodulus_sq_mul_jacobiSd_sq (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .d (jacobiThetaArgument z k) (jacobiTau k) ≠ 0) :
    jacobiCd z k ^ 2 + jacobiComodulus k ^ 2 * jacobiSd z k ^ 2 = 1 := by
  have hτ := jacobiTau_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  rw [← (jacobi_inversion_k hk).2.1]
  have hz' : θ₃ (jacobiThetaArgument z k) (jacobiTau k) ≠ 0 := by
    intro h'; apply hz; simp [jacobiLetterTheta, h']
  simp only [jacobiSd, jacobiCd, 
    jacobiPQ, jacobiGlaisher, jacobiLetterTheta, jacobiComodulusOfTau, reduceCtorEq, ↓reduceIte]
  rw [jacobiModulusOfTau] at hmod
  generalize jacobiThetaArgument z k = x at hz' ⊢
  generalize jacobiTau k = τ at hτ hz' hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := jacobiThetaTau_zero_ne_zero_and_pow_four τ hτ
  have e := DLMF.Theta.jacobiTheta_sq_two_three x τ hτ
  simp only [DLMF.Theta.jacobiThetaTwoNullTau, DLMF.Theta.jacobiThetaThreeNullTau,
    DLMF.Theta.jacobiThetaFourNullTau] at e
  field_simp
  linear_combination -e

/-- Identity under the stated parameter and domain assumptions: `jacobiNd z k ^ 2 - k ^ 2 *
jacobiSd z k ^ 2 = 1`. -/
lemma jacobiNd_sq_sub_sq_mul_jacobiSd_sq (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .d (jacobiThetaArgument z k) (jacobiTau k) ≠ 0) :
    jacobiNd z k ^ 2 - k ^ 2 * jacobiSd z k ^ 2 = 1 := by
  have hτ := jacobiTau_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  have hz' : θ₃ (jacobiThetaArgument z k) (jacobiTau k) ≠ 0 := by
    intro h'; apply hz; simp [jacobiLetterTheta, h']
  simp only [jacobiSd, jacobiNd, 
    jacobiPQ, jacobiGlaisher, jacobiLetterTheta, reduceCtorEq, ↓reduceIte]
  rw [jacobiModulusOfTau] at hmod
  generalize jacobiThetaArgument z k = x at hz' ⊢
  generalize jacobiTau k = τ at hτ hz' hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := jacobiThetaTau_zero_ne_zero_and_pow_four τ hτ
  have e := DLMF.Theta.jacobiTheta_sq_three_four x τ hτ
  simp only [DLMF.Theta.jacobiThetaTwoNullTau, DLMF.Theta.jacobiThetaThreeNullTau,
    DLMF.Theta.jacobiThetaFourNullTau] at e
  field_simp
  linear_combination e

/-- Identity under the stated parameter and domain assumptions: `jacobiNc z k ^ 2 - jacobiSc z k
^ 2 = 1`. -/
lemma jacobiNc_sq_sub_jacobiSc_sq (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .c (jacobiThetaArgument z k) (jacobiTau k) ≠ 0) :
    jacobiNc z k ^ 2 - jacobiSc z k ^ 2 = 1 := by
  have hτ := jacobiTau_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  have hz' : θ₂ (jacobiThetaArgument z k) (jacobiTau k) ≠ 0 := by
    intro h'; apply hz; simp [jacobiLetterTheta, h']
  simp only [jacobiSc, jacobiNc, 
    jacobiPQ, jacobiGlaisher, jacobiLetterTheta, reduceCtorEq, ↓reduceIte]
  rw [jacobiModulusOfTau] at hmod
  generalize jacobiThetaArgument z k = x at hz' ⊢
  generalize jacobiTau k = τ at hτ hz' hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := jacobiThetaTau_zero_ne_zero_and_pow_four τ hτ
  have e := DLMF.Theta.jacobiTheta_sq_two_four x τ hτ
  simp only [DLMF.Theta.jacobiThetaTwoNullTau, DLMF.Theta.jacobiThetaThreeNullTau,
    DLMF.Theta.jacobiThetaFourNullTau] at e
  field_simp
  linear_combination e

/-- Identity under the stated parameter and domain assumptions: `jacobiDc z k ^ 2 -
jacobiComodulus k ^ 2 * jacobiSc z k ^ 2 = 1`. -/
lemma jacobiDc_sq_sub_jacobiComodulus_sq_mul_jacobiSc_sq (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .c (jacobiThetaArgument z k) (jacobiTau k) ≠ 0) :
    jacobiDc z k ^ 2 - jacobiComodulus k ^ 2 * jacobiSc z k ^ 2 = 1 := by
  have hτ := jacobiTau_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  rw [← (jacobi_inversion_k hk).2.1]
  have hz' : θ₂ (jacobiThetaArgument z k) (jacobiTau k) ≠ 0 := by
    intro h'; apply hz; simp [jacobiLetterTheta, h']
  simp only [jacobiSc, jacobiDc, 
    jacobiPQ, jacobiGlaisher, jacobiLetterTheta, jacobiComodulusOfTau, reduceCtorEq, ↓reduceIte]
  rw [jacobiModulusOfTau] at hmod
  generalize jacobiThetaArgument z k = x at hz' ⊢
  generalize jacobiTau k = τ at hτ hz' hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := jacobiThetaTau_zero_ne_zero_and_pow_four τ hτ
  have e := DLMF.Theta.jacobiTheta_sq_two_three x τ hτ
  simp only [DLMF.Theta.jacobiThetaTwoNullTau, DLMF.Theta.jacobiThetaThreeNullTau,
    DLMF.Theta.jacobiThetaFourNullTau] at e
  field_simp
  linear_combination e

/-- Identity under the stated parameter and domain assumptions: `jacobiNs z k ^ 2 - jacobiCs z k
^ 2 = 1`. -/
lemma jacobiNs_sq_sub_jacobiCs_sq (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .s (jacobiThetaArgument z k) (jacobiTau k) ≠ 0) :
    jacobiNs z k ^ 2 - jacobiCs z k ^ 2 = 1 := by
  have hτ := jacobiTau_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  have hz' : θ₁ (jacobiThetaArgument z k) (jacobiTau k) ≠ 0 := by
    intro h'; apply hz; simp [jacobiLetterTheta, h']
  simp only [jacobiNs, jacobiCs,
    jacobiPQ, jacobiGlaisher, jacobiLetterTheta, reduceCtorEq, ↓reduceIte]
  rw [jacobiModulusOfTau] at hmod
  generalize jacobiThetaArgument z k = x at hz' ⊢
  generalize jacobiTau k = τ at hτ hz' hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := jacobiThetaTau_zero_ne_zero_and_pow_four τ hτ
  have e := DLMF.Theta.jacobiTheta_sq_two_four x τ hτ
  simp only [DLMF.Theta.jacobiThetaTwoNullTau, DLMF.Theta.jacobiThetaThreeNullTau,
    DLMF.Theta.jacobiThetaFourNullTau] at e
  field_simp
  linear_combination e

/-- Identity under the stated parameter and domain assumptions: `jacobiDs z k ^ 2 - jacobiCs z k
^ 2 = jacobiComodulus k ^ 2`. -/
lemma jacobiDs_sq_sub_jacobiCs_sq (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .s (jacobiThetaArgument z k) (jacobiTau k) ≠ 0) :
    jacobiDs z k ^ 2 - jacobiCs z k ^ 2 = jacobiComodulus k ^ 2 := by
  have hτ := jacobiTau_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  rw [← (jacobi_inversion_k hk).2.1]
  have hz' : θ₁ (jacobiThetaArgument z k) (jacobiTau k) ≠ 0 := by
    intro h'; apply hz; simp [jacobiLetterTheta, h']
  simp only [jacobiCs,
    jacobiDs, jacobiPQ, jacobiGlaisher, jacobiLetterTheta, jacobiComodulusOfTau, reduceCtorEq,
    ↓reduceIte]
  rw [jacobiModulusOfTau] at hmod
  generalize jacobiThetaArgument z k = x at hz' ⊢
  generalize jacobiTau k = τ at hτ hz' hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := jacobiThetaTau_zero_ne_zero_and_pow_four τ hτ
  have e := DLMF.Theta.jacobiTheta_sq_two_three x τ hτ
  simp only [DLMF.Theta.jacobiThetaTwoNullTau, DLMF.Theta.jacobiThetaThreeNullTau,
    DLMF.Theta.jacobiThetaFourNullTau] at e
  field_simp
  linear_combination e

/-- Nonvanishing under the stated hypotheses:
`∀ᶠ w in 𝓝 z, jacobiLetterTheta p (jacobiThetaArgument w k) (jacobiTau k) ≠ 0`. -/
theorem eventually_jacobiLetterTheta_ne_zero (hk : k ∈ jacobiModulusDomain)
    {p : JacobiLetter} {z : ℂ}
    (hz : jacobiLetterTheta p (jacobiThetaArgument z k) (jacobiTau k) ≠ 0) :
    ∀ᶠ w in 𝓝 z, jacobiLetterTheta p (jacobiThetaArgument w k) (jacobiTau k) ≠ 0 := by
  have hτ := jacobiTau_im_pos hk
  have hc : Continuous fun w => jacobiLetterTheta p (jacobiThetaArgument w k) (jacobiTau k) := by
    simp only [jacobiLetterTheta_eq_const_mul_raw]
    exact continuous_const.mul ((differentiable_jacobiLetterThetaRaw p hτ).continuous.comp
      (by unfold jacobiThetaArgument; fun_prop))
  exact hc.continuousAt.eventually_ne hz

/-- DLMF Table 22.13.1: `d sn(z,k)/dz = cn(z,k) dn(z,k)`, for `k ∈ jacobiModulusDomain` and `z`
not a pole of `sn` (`θ₄(πz/(2K)) ≠ 0`). -/
@[dlmf 22.13.T1 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem hasDerivAt_jacobiSn (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .n (jacobiThetaArgument z k) (jacobiTau k) ≠ 0) :
    HasDerivAt (fun z => jacobiSn z k) (jacobiCn z k * jacobiDn z k) z := by
  have h := hasDerivAt_jacobiPQ hk (p := .s) (q := .n) (by decide) hz
  refine h.congr_deriv ?_
  have hτ := jacobiTau_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  rw [← (jacobi_inversion_k hk).2.2]
  rw [jacobiLetterTheta_eq_const_mul_raw] at hz
  simp only [jacobiCn, jacobiDn, jacobiPQ, jacobiGlaisher, jacobiLetterTheta_eq_const_mul_raw,
      jacobiLetterThetaConst, jacobiLetterThetaRaw,
      reduceCtorEq, ↓reduceIte] at hz ⊢
  rw [jacobiThetaTau_wronskian_one_four hτ, completeEllipticKOfTau]
  rw [jacobiModulusOfTau] at hmod
  generalize jacobiThetaArgument z k = x at hz ⊢
  generalize jacobiTau k = τ at hτ hz hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := jacobiThetaTau_zero_ne_zero_and_pow_four τ hτ
  have hx := right_ne_zero_of_mul hz
  field_simp

/-- DLMF Table 22.13.1: `d cn(z,k)/dz = -sn(z,k) dn(z,k)`, away from the poles. -/
@[dlmf 22.13.T1 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem hasDerivAt_jacobiCn (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .n (jacobiThetaArgument z k) (jacobiTau k) ≠ 0) :
    HasDerivAt (fun z => jacobiCn z k) (-(jacobiSn z k * jacobiDn z k)) z := by
  have h := hasDerivAt_jacobiPQ hk (p := .c) (q := .n) (by decide) hz
  refine h.congr_deriv ?_
  have hτ := jacobiTau_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  rw [← (jacobi_inversion_k hk).2.2]
  rw [jacobiLetterTheta_eq_const_mul_raw] at hz
  simp only [jacobiDn, jacobiSn, jacobiPQ, jacobiGlaisher, jacobiLetterTheta_eq_const_mul_raw,
      jacobiLetterThetaConst, jacobiLetterThetaRaw,
      reduceCtorEq, ↓reduceIte] at hz ⊢
  rw [jacobiThetaTau_wronskian_two_four hτ, completeEllipticKOfTau]
  rw [jacobiModulusOfTau] at hmod
  generalize jacobiThetaArgument z k = x at hz ⊢
  generalize jacobiTau k = τ at hτ hz hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := jacobiThetaTau_zero_ne_zero_and_pow_four τ hτ
  have hx := right_ne_zero_of_mul hz
  field_simp

/-- DLMF Table 22.13.1: `d dn(z,k)/dz = -k² sn(z,k) cn(z,k)`, away from the poles. -/
@[dlmf 22.13.T1 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem hasDerivAt_jacobiDn (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .n (jacobiThetaArgument z k) (jacobiTau k) ≠ 0) :
    HasDerivAt (fun z => jacobiDn z k) (-(k ^ 2 * jacobiSn z k * jacobiCn z k)) z := by
  have h := hasDerivAt_jacobiPQ hk (p := .d) (q := .n) (by decide) hz
  refine h.congr_deriv ?_
  have hτ := jacobiTau_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  rw [← (jacobi_inversion_k hk).2.2]
  rw [jacobiLetterTheta_eq_const_mul_raw] at hz
  simp only [jacobiCn, jacobiSn, jacobiPQ, jacobiGlaisher, jacobiLetterTheta_eq_const_mul_raw,
      jacobiLetterThetaConst, jacobiLetterThetaRaw,
      reduceCtorEq, ↓reduceIte] at hz ⊢
  rw [jacobiThetaTau_wronskian_three_four hτ, completeEllipticKOfTau]
  rw [jacobiModulusOfTau] at hmod
  generalize jacobiThetaArgument z k = x at hz ⊢
  generalize jacobiTau k = τ at hτ hz hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := jacobiThetaTau_zero_ne_zero_and_pow_four τ hτ
  have hx := right_ne_zero_of_mul hz
  field_simp

/-- DLMF Table 22.13.1: `d cd(z,k)/dz = -k'² sd(z,k) nd(z,k)`, away from the poles
(`θ₃(πz/(2K)) ≠ 0`). -/
@[dlmf 22.13.T1 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem hasDerivAt_jacobiCd (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .d (jacobiThetaArgument z k) (jacobiTau k) ≠ 0) :
    HasDerivAt (fun z => jacobiCd z k)
      (-(jacobiComodulus k ^ 2 * jacobiSd z k * jacobiNd z k)) z := by
  have h := hasDerivAt_jacobiPQ hk (p := .c) (q := .d) (by decide) hz
  refine h.congr_deriv ?_
  have hτ := jacobiTau_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  rw [← (jacobi_inversion_k hk).2.2]
  rw [← (jacobi_inversion_k hk).2.1]
  rw [jacobiLetterTheta_eq_const_mul_raw] at hz
  simp only [jacobiNd, jacobiSd, jacobiPQ, jacobiGlaisher, jacobiLetterTheta_eq_const_mul_raw,
      jacobiLetterThetaConst, jacobiLetterThetaRaw,
      jacobiComodulusOfTau, reduceCtorEq, ↓reduceIte] at hz ⊢
  rw [jacobiThetaTau_wronskian_two_three hτ, completeEllipticKOfTau]
  rw [jacobiModulusOfTau] at hmod
  generalize jacobiThetaArgument z k = x at hz ⊢
  generalize jacobiTau k = τ at hτ hz hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := jacobiThetaTau_zero_ne_zero_and_pow_four τ hτ
  have hx := right_ne_zero_of_mul hz
  field_simp

/-- DLMF Table 22.13.1: `d sd(z,k)/dz = cd(z,k) nd(z,k)`, away from the poles. -/
@[dlmf 22.13.T1 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem hasDerivAt_jacobiSd (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .d (jacobiThetaArgument z k) (jacobiTau k) ≠ 0) :
    HasDerivAt (fun z => jacobiSd z k) (jacobiCd z k * jacobiNd z k) z := by
  have h := hasDerivAt_jacobiPQ hk (p := .s) (q := .d) (by decide) hz
  refine h.congr_deriv ?_
  have hτ := jacobiTau_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  rw [← (jacobi_inversion_k hk).2.2]
  rw [jacobiLetterTheta_eq_const_mul_raw] at hz
  simp only [jacobiCd, jacobiNd, jacobiPQ, jacobiGlaisher, jacobiLetterTheta_eq_const_mul_raw,
      jacobiLetterThetaConst, jacobiLetterThetaRaw,
      reduceCtorEq, ↓reduceIte] at hz ⊢
  rw [jacobiThetaTau_wronskian_one_three hτ, completeEllipticKOfTau]
  rw [jacobiModulusOfTau] at hmod
  generalize jacobiThetaArgument z k = x at hz ⊢
  generalize jacobiTau k = τ at hτ hz hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := jacobiThetaTau_zero_ne_zero_and_pow_four τ hτ
  have hx := right_ne_zero_of_mul hz
  field_simp

/-- DLMF Table 22.13.1: `d nd(z,k)/dz = k² sd(z,k) cd(z,k)`, away from the poles. -/
@[dlmf 22.13.T1 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem hasDerivAt_jacobiNd (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .d (jacobiThetaArgument z k) (jacobiTau k) ≠ 0) :
    HasDerivAt (fun z => jacobiNd z k) (k ^ 2 * jacobiSd z k * jacobiCd z k) z := by
  have h := hasDerivAt_jacobiPQ hk (p := .n) (q := .d) (by decide) hz
  refine h.congr_deriv ?_
  have hτ := jacobiTau_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  rw [← (jacobi_inversion_k hk).2.2]
  rw [jacobiLetterTheta_eq_const_mul_raw] at hz
  simp only [jacobiCd, jacobiSd, jacobiPQ, jacobiGlaisher, jacobiLetterTheta_eq_const_mul_raw,
      jacobiLetterThetaConst, jacobiLetterThetaRaw,
      reduceCtorEq, ↓reduceIte] at hz ⊢
  rw [jacobiThetaTau_wronskian_four_three hτ, completeEllipticKOfTau]
  rw [jacobiModulusOfTau] at hmod
  generalize jacobiThetaArgument z k = x at hz ⊢
  generalize jacobiTau k = τ at hτ hz hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := jacobiThetaTau_zero_ne_zero_and_pow_four τ hτ
  have hx := right_ne_zero_of_mul hz
  field_simp

/-- DLMF Table 22.13.1: `d dc(z,k)/dz = k'² sc(z,k) nc(z,k)`, away from the poles
(`θ₂(πz/(2K)) ≠ 0`). -/
@[dlmf 22.13.T1 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem hasDerivAt_jacobiDc (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .c (jacobiThetaArgument z k) (jacobiTau k) ≠ 0) :
    HasDerivAt (fun z => jacobiDc z k)
      (jacobiComodulus k ^ 2 * jacobiSc z k * jacobiNc z k) z := by
  have h := hasDerivAt_jacobiPQ hk (p := .d) (q := .c) (by decide) hz
  refine h.congr_deriv ?_
  have hτ := jacobiTau_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  rw [← (jacobi_inversion_k hk).2.2]
  rw [← (jacobi_inversion_k hk).2.1]
  rw [jacobiLetterTheta_eq_const_mul_raw] at hz
  simp only [jacobiNc, jacobiSc, jacobiPQ, jacobiGlaisher, jacobiLetterTheta_eq_const_mul_raw,
      jacobiLetterThetaConst, jacobiLetterThetaRaw,
      jacobiComodulusOfTau, reduceCtorEq, ↓reduceIte] at hz ⊢
  rw [jacobiThetaTau_wronskian_three_two hτ, completeEllipticKOfTau]
  rw [jacobiModulusOfTau] at hmod
  generalize jacobiThetaArgument z k = x at hz ⊢
  generalize jacobiTau k = τ at hτ hz hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := jacobiThetaTau_zero_ne_zero_and_pow_four τ hτ
  have hx := right_ne_zero_of_mul hz
  field_simp

/-- DLMF Table 22.13.1: `d nc(z,k)/dz = sc(z,k) dc(z,k)`, away from the poles. -/
@[dlmf 22.13.T1 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem hasDerivAt_jacobiNc (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .c (jacobiThetaArgument z k) (jacobiTau k) ≠ 0) :
    HasDerivAt (fun z => jacobiNc z k) (jacobiSc z k * jacobiDc z k) z := by
  have h := hasDerivAt_jacobiPQ hk (p := .n) (q := .c) (by decide) hz
  refine h.congr_deriv ?_
  have hτ := jacobiTau_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  rw [← (jacobi_inversion_k hk).2.2]
  rw [jacobiLetterTheta_eq_const_mul_raw] at hz
  simp only [jacobiDc, jacobiSc, jacobiPQ, jacobiGlaisher, jacobiLetterTheta_eq_const_mul_raw,
      jacobiLetterThetaConst, jacobiLetterThetaRaw,
      reduceCtorEq, ↓reduceIte] at hz ⊢
  rw [jacobiThetaTau_wronskian_four_two hτ, completeEllipticKOfTau]
  rw [jacobiModulusOfTau] at hmod
  generalize jacobiThetaArgument z k = x at hz ⊢
  generalize jacobiTau k = τ at hτ hz hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := jacobiThetaTau_zero_ne_zero_and_pow_four τ hτ
  have hx := right_ne_zero_of_mul hz
  field_simp

/-- DLMF Table 22.13.1: `d sc(z,k)/dz = dc(z,k) nc(z,k)`, away from the poles. -/
@[dlmf 22.13.T1 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem hasDerivAt_jacobiSc (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .c (jacobiThetaArgument z k) (jacobiTau k) ≠ 0) :
    HasDerivAt (fun z => jacobiSc z k) (jacobiDc z k * jacobiNc z k) z := by
  have h := hasDerivAt_jacobiPQ hk (p := .s) (q := .c) (by decide) hz
  refine h.congr_deriv ?_
  have hτ := jacobiTau_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  rw [← (jacobi_inversion_k hk).2.2]
  rw [jacobiLetterTheta_eq_const_mul_raw] at hz
  simp only [jacobiDc, jacobiNc, jacobiPQ, jacobiGlaisher, jacobiLetterTheta_eq_const_mul_raw,
      jacobiLetterThetaConst, jacobiLetterThetaRaw,
      reduceCtorEq, ↓reduceIte] at hz ⊢
  rw [jacobiThetaTau_wronskian_one_two hτ, completeEllipticKOfTau]
  rw [jacobiModulusOfTau] at hmod
  generalize jacobiThetaArgument z k = x at hz ⊢
  generalize jacobiTau k = τ at hτ hz hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := jacobiThetaTau_zero_ne_zero_and_pow_four τ hτ
  have hx := right_ne_zero_of_mul hz
  field_simp

/-- DLMF Table 22.13.1: `d ns(z,k)/dz = -ds(z,k) cs(z,k)`, away from the poles
(`θ₁(πz/(2K)) ≠ 0`). -/
@[dlmf 22.13.T1 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem hasDerivAt_jacobiNs (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .s (jacobiThetaArgument z k) (jacobiTau k) ≠ 0) :
    HasDerivAt (fun z => jacobiNs z k) (-(jacobiDs z k * jacobiCs z k)) z := by
  have h := hasDerivAt_jacobiPQ hk (p := .n) (q := .s) (by decide) hz
  refine h.congr_deriv ?_
  have hτ := jacobiTau_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  rw [← (jacobi_inversion_k hk).2.2]
  rw [jacobiLetterTheta_eq_const_mul_raw] at hz
  simp only [jacobiCs, jacobiDs, jacobiPQ, jacobiGlaisher, jacobiLetterTheta_eq_const_mul_raw,
      jacobiLetterThetaConst, jacobiLetterThetaRaw,
      reduceCtorEq, ↓reduceIte] at hz ⊢
  rw [jacobiThetaTau_wronskian_four_one hτ, completeEllipticKOfTau]
  rw [jacobiModulusOfTau] at hmod
  generalize jacobiThetaArgument z k = x at hz ⊢
  generalize jacobiTau k = τ at hτ hz hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := jacobiThetaTau_zero_ne_zero_and_pow_four τ hτ
  have hx := right_ne_zero_of_mul hz
  field_simp

/-- DLMF Table 22.13.1: `d ds(z,k)/dz = -cs(z,k) ns(z,k)`, away from the poles. -/
@[dlmf 22.13.T1 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem hasDerivAt_jacobiDs (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .s (jacobiThetaArgument z k) (jacobiTau k) ≠ 0) :
    HasDerivAt (fun z => jacobiDs z k) (-(jacobiCs z k * jacobiNs z k)) z := by
  have h := hasDerivAt_jacobiPQ hk (p := .d) (q := .s) (by decide) hz
  refine h.congr_deriv ?_
  have hτ := jacobiTau_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  rw [← (jacobi_inversion_k hk).2.2]
  rw [jacobiLetterTheta_eq_const_mul_raw] at hz
  simp only [jacobiCs, jacobiNs, jacobiPQ, jacobiGlaisher, jacobiLetterTheta_eq_const_mul_raw,
      jacobiLetterThetaConst, jacobiLetterThetaRaw,
      reduceCtorEq, ↓reduceIte] at hz ⊢
  rw [jacobiThetaTau_wronskian_three_one hτ, completeEllipticKOfTau]
  rw [jacobiModulusOfTau] at hmod
  generalize jacobiThetaArgument z k = x at hz ⊢
  generalize jacobiTau k = τ at hτ hz hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := jacobiThetaTau_zero_ne_zero_and_pow_four τ hτ
  have hx := right_ne_zero_of_mul hz
  field_simp

/-- DLMF Table 22.13.1: `d cs(z,k)/dz = -ns(z,k) ds(z,k)`, away from the poles. -/
@[dlmf 22.13.T1 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem hasDerivAt_jacobiCs (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .s (jacobiThetaArgument z k) (jacobiTau k) ≠ 0) :
    HasDerivAt (fun z => jacobiCs z k) (-(jacobiNs z k * jacobiDs z k)) z := by
  have h := hasDerivAt_jacobiPQ hk (p := .c) (q := .s) (by decide) hz
  refine h.congr_deriv ?_
  have hτ := jacobiTau_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  rw [← (jacobi_inversion_k hk).2.2]
  rw [jacobiLetterTheta_eq_const_mul_raw] at hz
  simp only [jacobiDs, jacobiNs, jacobiPQ, jacobiGlaisher, jacobiLetterTheta_eq_const_mul_raw,
      jacobiLetterThetaConst, jacobiLetterThetaRaw,
      reduceCtorEq, ↓reduceIte] at hz ⊢
  rw [jacobiThetaTau_wronskian_two_one hτ, completeEllipticKOfTau]
  rw [jacobiModulusOfTau] at hmod
  generalize jacobiThetaArgument z k = x at hz ⊢
  generalize jacobiTau k = τ at hτ hz hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := jacobiThetaTau_zero_ne_zero_and_pow_four τ hτ
  have hx := right_ne_zero_of_mul hz
  field_simp

end Complex
end DLMF.JacobiElliptic
end
end
