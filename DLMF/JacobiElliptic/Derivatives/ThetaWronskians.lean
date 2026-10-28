/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.JacobiElliptic.Basic
public import DLMF.JacobiElliptic.ElementaryIdentities
public import DLMF.Elliptic.Jacobi

/-!
# Theta Wronskians and Jacobi derivatives

Theta-function Wronskians and quotient differentiation give the complex derivative table for the
twelve Jacobian functions.

Source references and common attribution are retained in
`DLMF.JacobiElliptic.Derivatives`.
-/

@[expose] public section

open Complex DLMF.Elliptic

open scoped Real Topology

noncomputable section

namespace DLMF.JacobiElliptic

local notation "θ₁" => jacobiThetaOneTau

local notation "θ₂" => jacobiThetaTwoTau

local notation "θ₃" => jacobiThetaThreeTau

local notation "θ₄" => jacobiThetaFourTau

/-- Identity under the stated parameter and domain assumptions: `deriv f 0 = 0`. -/
lemma p22R1_deriv_even {f : ℂ → ℂ} (hf : Differentiable ℂ f) (he : ∀ z, f (-z) = f z) :
    deriv f 0 = 0 :=
  DLMF.Theta.p3t_deriv_even hf he

/-- Identity under the stated parameter and domain assumptions: `κ * (f' * g x - f x * g') = A x *
b' + C x * e'`. -/
lemma p22R1_wr {f g A B C E : ℂ → ℂ} {f' g' b' e' : ℂ} (κ x : ℂ)
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
lemma p22R1_hd1 (z : ℂ) : HasDerivAt (fun w => θ₁ w τ) (deriv (fun w => θ₁ w τ) z) z :=
  ((DLMF.Theta.differentiable_jacobiThetaTau 1 hτ) z).hasDerivAt
/-- At `z`, the function `(fun w => θ₂ w τ)` has derivative `(deriv (fun w => θ₂ w τ) z)`. -/
lemma p22R1_hd2 (z : ℂ) : HasDerivAt (fun w => θ₂ w τ) (deriv (fun w => θ₂ w τ) z) z :=
  ((DLMF.Theta.differentiable_jacobiThetaTau 2 hτ) z).hasDerivAt
/-- At `z`, the function `(fun w => θ₃ w τ)` has derivative `(deriv (fun w => θ₃ w τ) z)`. -/
lemma p22R1_hd3 (z : ℂ) : HasDerivAt (fun w => θ₃ w τ) (deriv (fun w => θ₃ w τ) z) z :=
  ((DLMF.Theta.differentiable_jacobiThetaTau 3 hτ) z).hasDerivAt
/-- At `z`, the function `(fun w => θ₄ w τ)` has derivative `(deriv (fun w => θ₄ w τ) z)`. -/
theorem p22R1_hd4 (z : ℂ) : HasDerivAt (fun w => θ₄ w τ) (deriv (fun w => θ₄ w τ) z) z :=
  ((DLMF.Theta.differentiable_jacobiThetaTau 4 hτ) z).hasDerivAt

/-- Identity under the stated parameter and domain assumptions: `deriv (fun w => θ₂ w τ) 0 = 0`. -/
lemma p22R1_d2zero : deriv (fun w => θ₂ w τ) 0 = 0 :=
  p22R1_deriv_even (DLMF.Theta.differentiable_jacobiThetaTau 2 hτ)
    fun z => jacobiThetaTwoTau_neg z τ
/-- Identity under the stated parameter and domain assumptions: `deriv (fun w => θ₃ w τ) 0 = 0`. -/
lemma p22R1_d3zero : deriv (fun w => θ₃ w τ) 0 = 0 :=
  p22R1_deriv_even (DLMF.Theta.differentiable_jacobiThetaTau 3 hτ)
    fun z => jacobiThetaThreeTau_neg z τ
/-- Identity under the stated parameter and domain assumptions: `deriv (fun w => θ₄ w τ) 0 = 0`. -/
lemma p22R1_d4zero : deriv (fun w => θ₄ w τ) 0 = 0 :=
  p22R1_deriv_even (DLMF.Theta.differentiable_jacobiThetaTau 4 hτ)
    fun z => jacobiThetaFourTau_neg z τ
/-- Identity under the stated parameter and domain assumptions: `deriv (fun w => θ₁ w τ) 0 = θ₂ 0
τ * θ₃ 0 τ * θ₄ 0 τ`. -/
lemma p22R1_d1zero : deriv (fun w => θ₁ w τ) 0 = θ₂ 0 τ * θ₃ 0 τ * θ₄ 0 τ :=
  DLMF.Theta.jacobiThetaOneDerivNullTau_eq_mul hτ

/-- Wronskian `θ₁'θ₄ - θ₁θ₄' = θ₄(0)² θ₂θ₃`. -/
lemma p22R1_W14 (x : ℂ) :
    deriv (fun w => θ₁ w τ) x * θ₄ x τ - θ₁ x τ * deriv (fun w => θ₄ w τ) x =
      θ₄ 0 τ ^ 2 * (θ₂ x τ * θ₃ x τ) := by
  have h := p22R1_wr (f := fun w => θ₁ w τ) (g := fun w => θ₄ w τ)
    (A := fun w => θ₁ w τ * θ₄ w τ) (B := fun w => θ₂ w τ * θ₃ w τ)
    (C := fun w => θ₂ w τ * θ₃ w τ) (E := fun w => θ₁ w τ * θ₄ w τ) (θ₂ 0 τ * θ₃ 0 τ) x
    (fun y => p22R1_mixed14 x y τ hτ) (p22R1_hd1 hτ x) (p22R1_hd4 hτ x)
    ((p22R1_hd2 hτ 0).mul (p22R1_hd3 hτ 0)) ((p22R1_hd1 hτ 0).mul (p22R1_hd4 hτ 0))
  simp only [p22R1_d1zero hτ, p22R1_d2zero hτ, p22R1_d3zero hτ, p22R1_d4zero hτ,
    je22a_thetaOne_zero] at h
  obtain ⟨h2, h3, -, -⟩ := p22R1_nulls τ hτ
  apply mul_left_cancel₀ (mul_ne_zero h2 h3)
  linear_combination h

/-- Identity under the stated parameter and domain assumptions: `deriv (fun w => θ₂ w τ) x * θ₄ x
τ - θ₂ x τ * deriv (fun w => θ₄ w τ) x = -(θ₃ 0 τ ^ 2 * (θ₁ x τ * θ₃ x τ))`. -/
lemma p22R1_W24 (x : ℂ) :
    deriv (fun w => θ₂ w τ) x * θ₄ x τ - θ₂ x τ * deriv (fun w => θ₄ w τ) x =
      -(θ₃ 0 τ ^ 2 * (θ₁ x τ * θ₃ x τ)) := by
  have h := p22R1_wr (f := fun w => θ₂ w τ) (g := fun w => θ₄ w τ)
    (A := fun w => θ₂ w τ * θ₄ w τ) (B := fun w => θ₂ w τ * θ₄ w τ)
    (C := fun w => -(θ₁ w τ * θ₃ w τ)) (E := fun w => θ₁ w τ * θ₃ w τ) (θ₂ 0 τ * θ₄ 0 τ) x
    (fun y => by have := p22R1_mixed24 x y τ hτ; linear_combination this)
    (p22R1_hd2 hτ x) (p22R1_hd4 hτ x)
    ((p22R1_hd2 hτ 0).mul (p22R1_hd4 hτ 0)) ((p22R1_hd1 hτ 0).mul (p22R1_hd3 hτ 0))
  simp only [p22R1_d1zero hτ, p22R1_d2zero hτ, p22R1_d3zero hτ, p22R1_d4zero hτ,
    je22a_thetaOne_zero] at h
  obtain ⟨h2, h3, h4, -⟩ := p22R1_nulls τ hτ
  apply mul_left_cancel₀ (mul_ne_zero h2 h4)
  linear_combination h

/-- Identity under the stated parameter and domain assumptions: `deriv (fun w => θ₃ w τ) x * θ₄ x
τ - θ₃ x τ * deriv (fun w => θ₄ w τ) x = -(θ₂ 0 τ ^ 2 * (θ₁ x τ * θ₂ x τ))`. -/
lemma p22R1_W34 (x : ℂ) :
    deriv (fun w => θ₃ w τ) x * θ₄ x τ - θ₃ x τ * deriv (fun w => θ₄ w τ) x =
      -(θ₂ 0 τ ^ 2 * (θ₁ x τ * θ₂ x τ)) := by
  have h := p22R1_wr (f := fun w => θ₃ w τ) (g := fun w => θ₄ w τ)
    (A := fun w => θ₃ w τ * θ₄ w τ) (B := fun w => θ₃ w τ * θ₄ w τ)
    (C := fun w => -(θ₁ w τ * θ₂ w τ)) (E := fun w => θ₁ w τ * θ₂ w τ) (θ₃ 0 τ * θ₄ 0 τ) x
    (fun y => by have := p22R1_mixed34 x y τ hτ; linear_combination this)
    (p22R1_hd3 hτ x) (p22R1_hd4 hτ x)
    ((p22R1_hd3 hτ 0).mul (p22R1_hd4 hτ 0)) ((p22R1_hd1 hτ 0).mul (p22R1_hd2 hτ 0))
  simp only [p22R1_d1zero hτ, p22R1_d2zero hτ, p22R1_d3zero hτ, p22R1_d4zero hτ,
    je22a_thetaOne_zero] at h
  obtain ⟨h2, h3, h4, -⟩ := p22R1_nulls τ hτ
  apply mul_left_cancel₀ (mul_ne_zero h3 h4)
  linear_combination h

/-- Identity under the stated parameter and domain assumptions: `deriv (fun w => θ₂ w τ) x * θ₃ x
τ - θ₂ x τ * deriv (fun w => θ₃ w τ) x = -(θ₄ 0 τ ^ 2 * (θ₁ x τ * θ₄ x τ))`. -/
lemma p22R1_W23 (x : ℂ) :
    deriv (fun w => θ₂ w τ) x * θ₃ x τ - θ₂ x τ * deriv (fun w => θ₃ w τ) x =
      -(θ₄ 0 τ ^ 2 * (θ₁ x τ * θ₄ x τ)) := by
  have h := p22R1_wr (f := fun w => θ₂ w τ) (g := fun w => θ₃ w τ)
    (A := fun w => θ₂ w τ * θ₃ w τ) (B := fun w => θ₂ w τ * θ₃ w τ)
    (C := fun w => -(θ₁ w τ * θ₄ w τ)) (E := fun w => θ₁ w τ * θ₄ w τ) (θ₂ 0 τ * θ₃ 0 τ) x
    (fun y => by have := p22R1_P23 x y τ hτ; linear_combination this)
    (p22R1_hd2 hτ x) (p22R1_hd3 hτ x)
    ((p22R1_hd2 hτ 0).mul (p22R1_hd3 hτ 0)) ((p22R1_hd1 hτ 0).mul (p22R1_hd4 hτ 0))
  simp only [p22R1_d1zero hτ, p22R1_d2zero hτ, p22R1_d3zero hτ, p22R1_d4zero hτ,
    je22a_thetaOne_zero] at h
  obtain ⟨h2, h3, h4, -⟩ := p22R1_nulls τ hτ
  apply mul_left_cancel₀ (mul_ne_zero h2 h3)
  linear_combination h

/-- Identity under the stated parameter and domain assumptions: `deriv (fun w => θ₁ w τ) x * θ₃ x
τ - θ₁ x τ * deriv (fun w => θ₃ w τ) x = θ₃ 0 τ ^ 2 * (θ₂ x τ * θ₄ x τ)`. -/
lemma p22R1_W13 (x : ℂ) :
    deriv (fun w => θ₁ w τ) x * θ₃ x τ - θ₁ x τ * deriv (fun w => θ₃ w τ) x =
      θ₃ 0 τ ^ 2 * (θ₂ x τ * θ₄ x τ) := by
  have h := p22R1_wr (f := fun w => θ₁ w τ) (g := fun w => θ₃ w τ)
    (A := fun w => θ₂ w τ * θ₄ w τ) (B := fun w => θ₁ w τ * θ₃ w τ)
    (C := fun w => θ₁ w τ * θ₃ w τ) (E := fun w => θ₂ w τ * θ₄ w τ) (θ₂ 0 τ * θ₄ 0 τ) x
    (fun y => by have := p22R1_P13 x y τ hτ; linear_combination this)
    (p22R1_hd1 hτ x) (p22R1_hd3 hτ x)
    ((p22R1_hd1 hτ 0).mul (p22R1_hd3 hτ 0)) ((p22R1_hd2 hτ 0).mul (p22R1_hd4 hτ 0))
  simp only [p22R1_d1zero hτ, p22R1_d2zero hτ, p22R1_d3zero hτ, p22R1_d4zero hτ,
    je22a_thetaOne_zero] at h
  obtain ⟨h2, h3, h4, -⟩ := p22R1_nulls τ hτ
  apply mul_left_cancel₀ (mul_ne_zero h2 h4)
  linear_combination h

/-- Identity under the stated parameter and domain assumptions: `deriv (fun w => θ₁ w τ) x * θ₂ x
τ - θ₁ x τ * deriv (fun w => θ₂ w τ) x = θ₂ 0 τ ^ 2 * (θ₃ x τ * θ₄ x τ)`. -/
lemma p22R1_W12 (x : ℂ) :
    deriv (fun w => θ₁ w τ) x * θ₂ x τ - θ₁ x τ * deriv (fun w => θ₂ w τ) x =
      θ₂ 0 τ ^ 2 * (θ₃ x τ * θ₄ x τ) := by
  have h := p22R1_wr (f := fun w => θ₁ w τ) (g := fun w => θ₂ w τ)
    (A := fun w => θ₁ w τ * θ₂ w τ) (B := fun w => θ₃ w τ * θ₄ w τ)
    (C := fun w => θ₃ w τ * θ₄ w τ) (E := fun w => θ₁ w τ * θ₂ w τ) (θ₃ 0 τ * θ₄ 0 τ) x
    (fun y => by have := p22R1_P12 x y τ hτ; linear_combination this)
    (p22R1_hd1 hτ x) (p22R1_hd2 hτ x)
    ((p22R1_hd3 hτ 0).mul (p22R1_hd4 hτ 0)) ((p22R1_hd1 hτ 0).mul (p22R1_hd2 hτ 0))
  simp only [p22R1_d1zero hτ, p22R1_d2zero hτ, p22R1_d3zero hτ, p22R1_d4zero hτ,
    je22a_thetaOne_zero] at h
  obtain ⟨h2, h3, h4, -⟩ := p22R1_nulls τ hτ
  apply mul_left_cancel₀ (mul_ne_zero h3 h4)
  linear_combination h

/-- Identity under the stated parameter and domain assumptions: `deriv (fun w => θ₄ w τ) x * θ₁ x
τ - θ₄ x τ * deriv (fun w => θ₁ w τ) x = -(θ₄ 0 τ ^ 2 * (θ₂ x τ * θ₃ x τ))`. -/
lemma p22R1_W41 (x : ℂ) :
    deriv (fun w => θ₄ w τ) x * θ₁ x τ - θ₄ x τ * deriv (fun w => θ₁ w τ) x =
      -(θ₄ 0 τ ^ 2 * (θ₂ x τ * θ₃ x τ)) := by
  linear_combination -(p22R1_W14 hτ x)

/-- Identity under the stated parameter and domain assumptions: `deriv (fun w => θ₄ w τ) x * θ₂ x
τ - θ₄ x τ * deriv (fun w => θ₂ w τ) x = -(-(θ₃ 0 τ ^ 2 * (θ₁ x τ * θ₃ x τ)))`. -/
lemma p22R1_W42 (x : ℂ) :
    deriv (fun w => θ₄ w τ) x * θ₂ x τ - θ₄ x τ * deriv (fun w => θ₂ w τ) x =
      -(-(θ₃ 0 τ ^ 2 * (θ₁ x τ * θ₃ x τ))) := by
  linear_combination -(p22R1_W24 hτ x)

/-- Identity under the stated parameter and domain assumptions: `deriv (fun w => θ₄ w τ) x * θ₃ x
τ - θ₄ x τ * deriv (fun w => θ₃ w τ) x = -(-(θ₂ 0 τ ^ 2 * (θ₁ x τ * θ₂ x τ)))`. -/
lemma p22R1_W43 (x : ℂ) :
    deriv (fun w => θ₄ w τ) x * θ₃ x τ - θ₄ x τ * deriv (fun w => θ₃ w τ) x =
      -(-(θ₂ 0 τ ^ 2 * (θ₁ x τ * θ₂ x τ))) := by
  linear_combination -(p22R1_W34 hτ x)

/-- Identity under the stated parameter and domain assumptions: `deriv (fun w => θ₃ w τ) x * θ₂ x
τ - θ₃ x τ * deriv (fun w => θ₂ w τ) x = -(-(θ₄ 0 τ ^ 2 * (θ₁ x τ * θ₄ x τ)))`. -/
lemma p22R1_W32 (x : ℂ) :
    deriv (fun w => θ₃ w τ) x * θ₂ x τ - θ₃ x τ * deriv (fun w => θ₂ w τ) x =
      -(-(θ₄ 0 τ ^ 2 * (θ₁ x τ * θ₄ x τ))) := by
  linear_combination -(p22R1_W23 hτ x)

/-- Identity under the stated parameter and domain assumptions: `deriv (fun w => θ₃ w τ) x * θ₁ x
τ - θ₃ x τ * deriv (fun w => θ₁ w τ) x = -(θ₃ 0 τ ^ 2 * (θ₂ x τ * θ₄ x τ))`. -/
lemma p22R1_W31 (x : ℂ) :
    deriv (fun w => θ₃ w τ) x * θ₁ x τ - θ₃ x τ * deriv (fun w => θ₁ w τ) x =
      -(θ₃ 0 τ ^ 2 * (θ₂ x τ * θ₄ x τ)) := by
  linear_combination -(p22R1_W13 hτ x)

/-- Identity under the stated parameter and domain assumptions: `deriv (fun w => θ₂ w τ) x * θ₁ x
τ - θ₂ x τ * deriv (fun w => θ₁ w τ) x = -(θ₂ 0 τ ^ 2 * (θ₃ x τ * θ₄ x τ))`. -/
lemma p22R1_W21 (x : ℂ) :
    deriv (fun w => θ₂ w τ) x * θ₁ x τ - θ₂ x τ * deriv (fun w => θ₁ w τ) x =
      -(θ₂ 0 τ ^ 2 * (θ₃ x τ * θ₄ x τ)) := by
  linear_combination -(p22R1_W12 hτ x)

end

/-- Normalizing constant of `jacobiLetterTheta` (helper). -/
noncomputable def p22R1_N : JacobiLetter → ℂ → ℂ
  | .s, τ => θ₃ 0 τ / (θ₂ 0 τ * θ₄ 0 τ)
  | .c, τ => 1 / θ₂ 0 τ
  | .d, τ => 1 / θ₃ 0 τ
  | .n, τ => 1 / θ₄ 0 τ

/-- The theta function of a letter (helper). -/
noncomputable def p22R1_th : JacobiLetter → ℂ → ℂ → ℂ
  | .s => θ₁
  | .c => θ₂
  | .d => θ₃
  | .n => θ₄

/-- Identity under the stated parameter and domain assumptions: `jacobiLetterTheta p ζ τ = p22R1_N
p τ * p22R1_th p ζ τ`. -/
theorem p22R1_letter_eq (p : JacobiLetter) (ζ τ : ℂ) :
    jacobiLetterTheta p ζ τ = p22R1_N p τ * p22R1_th p ζ τ := by
  cases p <;> simp [jacobiLetterTheta, p22R1_N, p22R1_th] <;> ring

/-- Differentiability of the indicated parameterized function: `Differentiable ℂ (fun w =>
p22R1_th p w τ)`. -/
theorem p22R1_differentiable_th (p : JacobiLetter) {τ : ℂ} (hτ : 0 < τ.im) :
    Differentiable ℂ (fun w => p22R1_th p w τ) := by
  cases p
  · exact DLMF.Theta.differentiable_jacobiThetaTau 1 hτ
  · exact DLMF.Theta.differentiable_jacobiThetaTau 2 hτ
  · exact DLMF.Theta.differentiable_jacobiThetaTau 3 hτ
  · exact DLMF.Theta.differentiable_jacobiThetaTau 4 hτ

/-- At `z`, the function `(fun z => jacobiPQk p q z k)` has derivative `(p22R1_N p (jacobiTauk k)
/ p22R1_N q (jacobiTauk k) * (π / (2 * compEllIntKk k)) * (deriv (fun w => p22R1_th p w
(jacobiTauk k)) (jacobiZetak z k) * p22R1_th q (jacobiZetak z k) (jacobiTauk k) - p22R1_th p
(jacobiZetak z k) (jacobiTauk k) * deriv (fun w => p22R1_th q w (jacobiTauk k)) (jacobiZetak z
k)) / p22R1_th q (jacobiZetak z k) (jacobiTauk k) ^ 2)`. -/
theorem p22R1_hasDerivAt_PQ {k : ℂ} (hk : k ∈ jacobiModulusDomain) {p q : JacobiLetter}
    (hpq : p ≠ q) {z : ℂ} (hz : jacobiLetterTheta q (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    HasDerivAt (fun z => jacobiPQk p q z k)
      (p22R1_N p (jacobiTauk k) / p22R1_N q (jacobiTauk k) * (π / (2 * compEllIntKk k)) *
        (deriv (fun w => p22R1_th p w (jacobiTauk k)) (jacobiZetak z k) *
            p22R1_th q (jacobiZetak z k) (jacobiTauk k) -
          p22R1_th p (jacobiZetak z k) (jacobiTauk k) *
            deriv (fun w => p22R1_th q w (jacobiTauk k)) (jacobiZetak z k)) /
        p22R1_th q (jacobiZetak z k) (jacobiTauk k) ^ 2) z := by
  have hτ := jacobiTauk_im_pos hk
  have hK := p22R1_compEllIntKk_ne_zero hk
  have hfun : (fun z => jacobiPQk p q z k) = fun z =>
      (p22R1_N p (jacobiTauk k) * p22R1_th p (jacobiZetak z k) (jacobiTauk k)) /
        (p22R1_N q (jacobiTauk k) * p22R1_th q (jacobiZetak z k) (jacobiTauk k)) := by
    funext w; simp [jacobiPQk, jacobiGlaisher, hpq, p22R1_letter_eq]
  rw [hfun]
  rw [p22R1_letter_eq] at hz
  have hζ : HasDerivAt (fun z => jacobiZetak z k) (π / (2 * compEllIntKk k)) z := by
    have := ((hasDerivAt_id z).const_mul (π : ℂ)).div_const (2 * compEllIntKk k)
    simpa [jacobiZetak] using this
  have hp := (((p22R1_differentiable_th p hτ) _).hasDerivAt.comp z hζ).const_mul
    (p22R1_N p (jacobiTauk k))
  have hq := (((p22R1_differentiable_th q hτ) _).hasDerivAt.comp z hζ).const_mul
    (p22R1_N q (jacobiTauk k))
  convert hp.div hq hz using 1
  · funext y; rfl
  have hN : p22R1_N q (jacobiTauk k) ≠ 0 := left_ne_zero_of_mul hz
  have hT : p22R1_th q (jacobiZetak z k) (jacobiTauk k) ≠ 0 := right_ne_zero_of_mul hz
  simp only [Function.comp_def]
  field_simp

/-! ### Table 22.13.1, complex argument -/

section Complex

variable {k : ℂ}

/-- Identity under the stated parameter and domain assumptions: `jacobiCdk z k ^ 2 +
jacobiComodulusk k ^ 2 * jacobiSdk z k ^ 2 = 1`. -/
lemma p22R1_sq_d1 (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .d (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    jacobiCdk z k ^ 2 + jacobiComodulusk k ^ 2 * jacobiSdk z k ^ 2 = 1 := by
  have hτ := jacobiTauk_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  rw [← (jacobi_inversion_k hk).2.1]
  have hz' : θ₃ (jacobiZetak z k) (jacobiTauk k) ≠ 0 := by
    intro h'; apply hz; simp [jacobiLetterTheta, h']
  simp only [jacobiSdk, jacobiCdk, 
    jacobiPQk, jacobiGlaisher, jacobiLetterTheta, jacobiComodulusTau, reduceCtorEq, ↓reduceIte]
  rw [jacobiModulusTau] at hmod
  generalize jacobiZetak z k = x at hz' ⊢
  generalize jacobiTauk k = τ at hτ hz' hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := p22R1_nulls τ hτ
  have e := DLMF.Theta.jacobiTheta_sq_two_three x τ hτ
  simp only [DLMF.Theta.jacobiThetaTwoNullTau, DLMF.Theta.jacobiThetaThreeNullTau,
    DLMF.Theta.jacobiThetaFourNullTau] at e
  field_simp
  linear_combination -e

/-- Identity under the stated parameter and domain assumptions: `jacobiNdk z k ^ 2 - k ^ 2 *
jacobiSdk z k ^ 2 = 1`. -/
lemma p22R1_sq_d2 (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .d (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    jacobiNdk z k ^ 2 - k ^ 2 * jacobiSdk z k ^ 2 = 1 := by
  have hτ := jacobiTauk_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  have hz' : θ₃ (jacobiZetak z k) (jacobiTauk k) ≠ 0 := by
    intro h'; apply hz; simp [jacobiLetterTheta, h']
  simp only [jacobiSdk, jacobiNdk, 
    jacobiPQk, jacobiGlaisher, jacobiLetterTheta, reduceCtorEq, ↓reduceIte]
  rw [jacobiModulusTau] at hmod
  generalize jacobiZetak z k = x at hz' ⊢
  generalize jacobiTauk k = τ at hτ hz' hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := p22R1_nulls τ hτ
  have e := DLMF.Theta.jacobiTheta_sq_three_four x τ hτ
  simp only [DLMF.Theta.jacobiThetaTwoNullTau, DLMF.Theta.jacobiThetaThreeNullTau,
    DLMF.Theta.jacobiThetaFourNullTau] at e
  field_simp
  linear_combination e

/-- Identity under the stated parameter and domain assumptions: `jacobiNck z k ^ 2 - jacobiSck z k
^ 2 = 1`. -/
lemma p22R1_sq_c1 (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .c (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    jacobiNck z k ^ 2 - jacobiSck z k ^ 2 = 1 := by
  have hτ := jacobiTauk_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  have hz' : θ₂ (jacobiZetak z k) (jacobiTauk k) ≠ 0 := by
    intro h'; apply hz; simp [jacobiLetterTheta, h']
  simp only [jacobiSck, jacobiNck, 
    jacobiPQk, jacobiGlaisher, jacobiLetterTheta, reduceCtorEq, ↓reduceIte]
  rw [jacobiModulusTau] at hmod
  generalize jacobiZetak z k = x at hz' ⊢
  generalize jacobiTauk k = τ at hτ hz' hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := p22R1_nulls τ hτ
  have e := DLMF.Theta.jacobiTheta_sq_two_four x τ hτ
  simp only [DLMF.Theta.jacobiThetaTwoNullTau, DLMF.Theta.jacobiThetaThreeNullTau,
    DLMF.Theta.jacobiThetaFourNullTau] at e
  field_simp
  linear_combination e

/-- Identity under the stated parameter and domain assumptions: `jacobiDck z k ^ 2 -
jacobiComodulusk k ^ 2 * jacobiSck z k ^ 2 = 1`. -/
lemma p22R1_sq_c2 (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .c (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    jacobiDck z k ^ 2 - jacobiComodulusk k ^ 2 * jacobiSck z k ^ 2 = 1 := by
  have hτ := jacobiTauk_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  rw [← (jacobi_inversion_k hk).2.1]
  have hz' : θ₂ (jacobiZetak z k) (jacobiTauk k) ≠ 0 := by
    intro h'; apply hz; simp [jacobiLetterTheta, h']
  simp only [jacobiSck, jacobiDck, 
    jacobiPQk, jacobiGlaisher, jacobiLetterTheta, jacobiComodulusTau, reduceCtorEq, ↓reduceIte]
  rw [jacobiModulusTau] at hmod
  generalize jacobiZetak z k = x at hz' ⊢
  generalize jacobiTauk k = τ at hτ hz' hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := p22R1_nulls τ hτ
  have e := DLMF.Theta.jacobiTheta_sq_two_three x τ hτ
  simp only [DLMF.Theta.jacobiThetaTwoNullTau, DLMF.Theta.jacobiThetaThreeNullTau,
    DLMF.Theta.jacobiThetaFourNullTau] at e
  field_simp
  linear_combination e

/-- Identity under the stated parameter and domain assumptions: `jacobiNsk z k ^ 2 - jacobiCsk z k
^ 2 = 1`. -/
lemma p22R1_sq_s1 (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .s (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    jacobiNsk z k ^ 2 - jacobiCsk z k ^ 2 = 1 := by
  have hτ := jacobiTauk_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  have hz' : θ₁ (jacobiZetak z k) (jacobiTauk k) ≠ 0 := by
    intro h'; apply hz; simp [jacobiLetterTheta, h']
  simp only [jacobiNsk, jacobiCsk,
    jacobiPQk, jacobiGlaisher, jacobiLetterTheta, reduceCtorEq, ↓reduceIte]
  rw [jacobiModulusTau] at hmod
  generalize jacobiZetak z k = x at hz' ⊢
  generalize jacobiTauk k = τ at hτ hz' hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := p22R1_nulls τ hτ
  have e := DLMF.Theta.jacobiTheta_sq_two_four x τ hτ
  simp only [DLMF.Theta.jacobiThetaTwoNullTau, DLMF.Theta.jacobiThetaThreeNullTau,
    DLMF.Theta.jacobiThetaFourNullTau] at e
  field_simp
  linear_combination e

/-- Identity under the stated parameter and domain assumptions: `jacobiDsk z k ^ 2 - jacobiCsk z k
^ 2 = jacobiComodulusk k ^ 2`. -/
lemma p22R1_sq_s2 (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .s (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    jacobiDsk z k ^ 2 - jacobiCsk z k ^ 2 = jacobiComodulusk k ^ 2 := by
  have hτ := jacobiTauk_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  rw [← (jacobi_inversion_k hk).2.1]
  have hz' : θ₁ (jacobiZetak z k) (jacobiTauk k) ≠ 0 := by
    intro h'; apply hz; simp [jacobiLetterTheta, h']
  simp only [jacobiCsk,
    jacobiDsk, jacobiPQk, jacobiGlaisher, jacobiLetterTheta, jacobiComodulusTau, reduceCtorEq,
    ↓reduceIte]
  rw [jacobiModulusTau] at hmod
  generalize jacobiZetak z k = x at hz' ⊢
  generalize jacobiTauk k = τ at hτ hz' hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := p22R1_nulls τ hτ
  have e := DLMF.Theta.jacobiTheta_sq_two_three x τ hτ
  simp only [DLMF.Theta.jacobiThetaTwoNullTau, DLMF.Theta.jacobiThetaThreeNullTau,
    DLMF.Theta.jacobiThetaFourNullTau] at e
  field_simp
  linear_combination e

/-- Nonvanishing under the stated hypotheses: `∀ᶠ w in 𝓝 z, jacobiLetterTheta p (jacobiZetak w k)
(jacobiTauk k) ≠ 0`. -/
theorem p22R1_eventually_ne (hk : k ∈ jacobiModulusDomain) {p : JacobiLetter} {z : ℂ}
    (hz : jacobiLetterTheta p (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    ∀ᶠ w in 𝓝 z, jacobiLetterTheta p (jacobiZetak w k) (jacobiTauk k) ≠ 0 := by
  have hτ := jacobiTauk_im_pos hk
  have hc : Continuous fun w => jacobiLetterTheta p (jacobiZetak w k) (jacobiTauk k) := by
    simp only [p22R1_letter_eq]
    exact continuous_const.mul ((p22R1_differentiable_th p hτ).continuous.comp
      (by unfold jacobiZetak; fun_prop))
  exact hc.continuousAt.eventually_ne hz

/-- DLMF Table 22.13.1: `d sn(z,k)/dz = cn(z,k) dn(z,k)`, for `k ∈ jacobiModulusDomain` and `z`
not a pole of `sn` (`θ₄(πz/(2K)) ≠ 0`). -/
@[dlmf 22.13.T1 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem hasDerivAt_jacobiSnk (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .n (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    HasDerivAt (fun z => jacobiSnk z k) (jacobiCnk z k * jacobiDnk z k) z := by
  have h := p22R1_hasDerivAt_PQ hk (p := .s) (q := .n) (by decide) hz
  refine h.congr_deriv ?_
  have hτ := jacobiTauk_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  rw [← (jacobi_inversion_k hk).2.2]
  rw [p22R1_letter_eq] at hz
  simp only [jacobiCnk, jacobiDnk, jacobiPQk, jacobiGlaisher, p22R1_letter_eq, p22R1_N, p22R1_th,
      reduceCtorEq, ↓reduceIte] at hz ⊢
  rw [p22R1_W14 hτ, compEllIntKTau]
  rw [jacobiModulusTau] at hmod
  generalize jacobiZetak z k = x at hz ⊢
  generalize jacobiTauk k = τ at hτ hz hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := p22R1_nulls τ hτ
  have hx := right_ne_zero_of_mul hz
  field_simp

/-- DLMF Table 22.13.1: `d cn(z,k)/dz = -sn(z,k) dn(z,k)`, away from the poles. -/
@[dlmf 22.13.T1 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem hasDerivAt_jacobiCnk (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .n (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    HasDerivAt (fun z => jacobiCnk z k) (-(jacobiSnk z k * jacobiDnk z k)) z := by
  have h := p22R1_hasDerivAt_PQ hk (p := .c) (q := .n) (by decide) hz
  refine h.congr_deriv ?_
  have hτ := jacobiTauk_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  rw [← (jacobi_inversion_k hk).2.2]
  rw [p22R1_letter_eq] at hz
  simp only [jacobiDnk, jacobiSnk, jacobiPQk, jacobiGlaisher, p22R1_letter_eq, p22R1_N, p22R1_th,
      reduceCtorEq, ↓reduceIte] at hz ⊢
  rw [p22R1_W24 hτ, compEllIntKTau]
  rw [jacobiModulusTau] at hmod
  generalize jacobiZetak z k = x at hz ⊢
  generalize jacobiTauk k = τ at hτ hz hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := p22R1_nulls τ hτ
  have hx := right_ne_zero_of_mul hz
  field_simp

/-- DLMF Table 22.13.1: `d dn(z,k)/dz = -k² sn(z,k) cn(z,k)`, away from the poles. -/
@[dlmf 22.13.T1 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem hasDerivAt_jacobiDnk (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .n (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    HasDerivAt (fun z => jacobiDnk z k) (-(k ^ 2 * jacobiSnk z k * jacobiCnk z k)) z := by
  have h := p22R1_hasDerivAt_PQ hk (p := .d) (q := .n) (by decide) hz
  refine h.congr_deriv ?_
  have hτ := jacobiTauk_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  rw [← (jacobi_inversion_k hk).2.2]
  rw [p22R1_letter_eq] at hz
  simp only [jacobiCnk, jacobiSnk, jacobiPQk, jacobiGlaisher, p22R1_letter_eq, p22R1_N, p22R1_th,
      reduceCtorEq, ↓reduceIte] at hz ⊢
  rw [p22R1_W34 hτ, compEllIntKTau]
  rw [jacobiModulusTau] at hmod
  generalize jacobiZetak z k = x at hz ⊢
  generalize jacobiTauk k = τ at hτ hz hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := p22R1_nulls τ hτ
  have hx := right_ne_zero_of_mul hz
  field_simp

/-- DLMF Table 22.13.1: `d cd(z,k)/dz = -k'² sd(z,k) nd(z,k)`, away from the poles
(`θ₃(πz/(2K)) ≠ 0`). -/
@[dlmf 22.13.T1 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem hasDerivAt_jacobiCdk (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .d (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    HasDerivAt (fun z => jacobiCdk z k)
      (-(jacobiComodulusk k ^ 2 * jacobiSdk z k * jacobiNdk z k)) z := by
  have h := p22R1_hasDerivAt_PQ hk (p := .c) (q := .d) (by decide) hz
  refine h.congr_deriv ?_
  have hτ := jacobiTauk_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  rw [← (jacobi_inversion_k hk).2.2]
  rw [← (jacobi_inversion_k hk).2.1]
  rw [p22R1_letter_eq] at hz
  simp only [jacobiNdk, jacobiSdk, jacobiPQk, jacobiGlaisher, p22R1_letter_eq, p22R1_N, p22R1_th,
      jacobiComodulusTau, reduceCtorEq, ↓reduceIte] at hz ⊢
  rw [p22R1_W23 hτ, compEllIntKTau]
  rw [jacobiModulusTau] at hmod
  generalize jacobiZetak z k = x at hz ⊢
  generalize jacobiTauk k = τ at hτ hz hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := p22R1_nulls τ hτ
  have hx := right_ne_zero_of_mul hz
  field_simp

/-- DLMF Table 22.13.1: `d sd(z,k)/dz = cd(z,k) nd(z,k)`, away from the poles. -/
@[dlmf 22.13.T1 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem hasDerivAt_jacobiSdk (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .d (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    HasDerivAt (fun z => jacobiSdk z k) (jacobiCdk z k * jacobiNdk z k) z := by
  have h := p22R1_hasDerivAt_PQ hk (p := .s) (q := .d) (by decide) hz
  refine h.congr_deriv ?_
  have hτ := jacobiTauk_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  rw [← (jacobi_inversion_k hk).2.2]
  rw [p22R1_letter_eq] at hz
  simp only [jacobiCdk, jacobiNdk, jacobiPQk, jacobiGlaisher, p22R1_letter_eq, p22R1_N, p22R1_th,
      reduceCtorEq, ↓reduceIte] at hz ⊢
  rw [p22R1_W13 hτ, compEllIntKTau]
  rw [jacobiModulusTau] at hmod
  generalize jacobiZetak z k = x at hz ⊢
  generalize jacobiTauk k = τ at hτ hz hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := p22R1_nulls τ hτ
  have hx := right_ne_zero_of_mul hz
  field_simp

/-- DLMF Table 22.13.1: `d nd(z,k)/dz = k² sd(z,k) cd(z,k)`, away from the poles. -/
@[dlmf 22.13.T1 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem hasDerivAt_jacobiNdk (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .d (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    HasDerivAt (fun z => jacobiNdk z k) (k ^ 2 * jacobiSdk z k * jacobiCdk z k) z := by
  have h := p22R1_hasDerivAt_PQ hk (p := .n) (q := .d) (by decide) hz
  refine h.congr_deriv ?_
  have hτ := jacobiTauk_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  rw [← (jacobi_inversion_k hk).2.2]
  rw [p22R1_letter_eq] at hz
  simp only [jacobiCdk, jacobiSdk, jacobiPQk, jacobiGlaisher, p22R1_letter_eq, p22R1_N, p22R1_th,
      reduceCtorEq, ↓reduceIte] at hz ⊢
  rw [p22R1_W43 hτ, compEllIntKTau]
  rw [jacobiModulusTau] at hmod
  generalize jacobiZetak z k = x at hz ⊢
  generalize jacobiTauk k = τ at hτ hz hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := p22R1_nulls τ hτ
  have hx := right_ne_zero_of_mul hz
  field_simp

/-- DLMF Table 22.13.1: `d dc(z,k)/dz = k'² sc(z,k) nc(z,k)`, away from the poles
(`θ₂(πz/(2K)) ≠ 0`). -/
@[dlmf 22.13.T1 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem hasDerivAt_jacobiDck (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .c (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    HasDerivAt (fun z => jacobiDck z k)
      (jacobiComodulusk k ^ 2 * jacobiSck z k * jacobiNck z k) z := by
  have h := p22R1_hasDerivAt_PQ hk (p := .d) (q := .c) (by decide) hz
  refine h.congr_deriv ?_
  have hτ := jacobiTauk_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  rw [← (jacobi_inversion_k hk).2.2]
  rw [← (jacobi_inversion_k hk).2.1]
  rw [p22R1_letter_eq] at hz
  simp only [jacobiNck, jacobiSck, jacobiPQk, jacobiGlaisher, p22R1_letter_eq, p22R1_N, p22R1_th,
      jacobiComodulusTau, reduceCtorEq, ↓reduceIte] at hz ⊢
  rw [p22R1_W32 hτ, compEllIntKTau]
  rw [jacobiModulusTau] at hmod
  generalize jacobiZetak z k = x at hz ⊢
  generalize jacobiTauk k = τ at hτ hz hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := p22R1_nulls τ hτ
  have hx := right_ne_zero_of_mul hz
  field_simp

/-- DLMF Table 22.13.1: `d nc(z,k)/dz = sc(z,k) dc(z,k)`, away from the poles. -/
@[dlmf 22.13.T1 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem hasDerivAt_jacobiNck (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .c (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    HasDerivAt (fun z => jacobiNck z k) (jacobiSck z k * jacobiDck z k) z := by
  have h := p22R1_hasDerivAt_PQ hk (p := .n) (q := .c) (by decide) hz
  refine h.congr_deriv ?_
  have hτ := jacobiTauk_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  rw [← (jacobi_inversion_k hk).2.2]
  rw [p22R1_letter_eq] at hz
  simp only [jacobiDck, jacobiSck, jacobiPQk, jacobiGlaisher, p22R1_letter_eq, p22R1_N, p22R1_th,
      reduceCtorEq, ↓reduceIte] at hz ⊢
  rw [p22R1_W42 hτ, compEllIntKTau]
  rw [jacobiModulusTau] at hmod
  generalize jacobiZetak z k = x at hz ⊢
  generalize jacobiTauk k = τ at hτ hz hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := p22R1_nulls τ hτ
  have hx := right_ne_zero_of_mul hz
  field_simp

/-- DLMF Table 22.13.1: `d sc(z,k)/dz = dc(z,k) nc(z,k)`, away from the poles. -/
@[dlmf 22.13.T1 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem hasDerivAt_jacobiSck (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .c (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    HasDerivAt (fun z => jacobiSck z k) (jacobiDck z k * jacobiNck z k) z := by
  have h := p22R1_hasDerivAt_PQ hk (p := .s) (q := .c) (by decide) hz
  refine h.congr_deriv ?_
  have hτ := jacobiTauk_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  rw [← (jacobi_inversion_k hk).2.2]
  rw [p22R1_letter_eq] at hz
  simp only [jacobiDck, jacobiNck, jacobiPQk, jacobiGlaisher, p22R1_letter_eq, p22R1_N, p22R1_th,
      reduceCtorEq, ↓reduceIte] at hz ⊢
  rw [p22R1_W12 hτ, compEllIntKTau]
  rw [jacobiModulusTau] at hmod
  generalize jacobiZetak z k = x at hz ⊢
  generalize jacobiTauk k = τ at hτ hz hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := p22R1_nulls τ hτ
  have hx := right_ne_zero_of_mul hz
  field_simp

/-- DLMF Table 22.13.1: `d ns(z,k)/dz = -ds(z,k) cs(z,k)`, away from the poles
(`θ₁(πz/(2K)) ≠ 0`). -/
@[dlmf 22.13.T1 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem hasDerivAt_jacobiNsk (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .s (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    HasDerivAt (fun z => jacobiNsk z k) (-(jacobiDsk z k * jacobiCsk z k)) z := by
  have h := p22R1_hasDerivAt_PQ hk (p := .n) (q := .s) (by decide) hz
  refine h.congr_deriv ?_
  have hτ := jacobiTauk_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  rw [← (jacobi_inversion_k hk).2.2]
  rw [p22R1_letter_eq] at hz
  simp only [jacobiCsk, jacobiDsk, jacobiPQk, jacobiGlaisher, p22R1_letter_eq, p22R1_N, p22R1_th,
      reduceCtorEq, ↓reduceIte] at hz ⊢
  rw [p22R1_W41 hτ, compEllIntKTau]
  rw [jacobiModulusTau] at hmod
  generalize jacobiZetak z k = x at hz ⊢
  generalize jacobiTauk k = τ at hτ hz hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := p22R1_nulls τ hτ
  have hx := right_ne_zero_of_mul hz
  field_simp

/-- DLMF Table 22.13.1: `d ds(z,k)/dz = -cs(z,k) ns(z,k)`, away from the poles. -/
@[dlmf 22.13.T1 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem hasDerivAt_jacobiDsk (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .s (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    HasDerivAt (fun z => jacobiDsk z k) (-(jacobiCsk z k * jacobiNsk z k)) z := by
  have h := p22R1_hasDerivAt_PQ hk (p := .d) (q := .s) (by decide) hz
  refine h.congr_deriv ?_
  have hτ := jacobiTauk_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  rw [← (jacobi_inversion_k hk).2.2]
  rw [p22R1_letter_eq] at hz
  simp only [jacobiCsk, jacobiNsk, jacobiPQk, jacobiGlaisher, p22R1_letter_eq, p22R1_N, p22R1_th,
      reduceCtorEq, ↓reduceIte] at hz ⊢
  rw [p22R1_W31 hτ, compEllIntKTau]
  rw [jacobiModulusTau] at hmod
  generalize jacobiZetak z k = x at hz ⊢
  generalize jacobiTauk k = τ at hτ hz hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := p22R1_nulls τ hτ
  have hx := right_ne_zero_of_mul hz
  field_simp

/-- DLMF Table 22.13.1: `d cs(z,k)/dz = -ns(z,k) ds(z,k)`, away from the poles. -/
@[dlmf 22.13.T1 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem hasDerivAt_jacobiCsk (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .s (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    HasDerivAt (fun z => jacobiCsk z k) (-(jacobiNsk z k * jacobiDsk z k)) z := by
  have h := p22R1_hasDerivAt_PQ hk (p := .c) (q := .s) (by decide) hz
  refine h.congr_deriv ?_
  have hτ := jacobiTauk_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  rw [← (jacobi_inversion_k hk).2.2]
  rw [p22R1_letter_eq] at hz
  simp only [jacobiDsk, jacobiNsk, jacobiPQk, jacobiGlaisher, p22R1_letter_eq, p22R1_N, p22R1_th,
      reduceCtorEq, ↓reduceIte] at hz ⊢
  rw [p22R1_W21 hτ, compEllIntKTau]
  rw [jacobiModulusTau] at hmod
  generalize jacobiZetak z k = x at hz ⊢
  generalize jacobiTauk k = τ at hτ hz hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := p22R1_nulls τ hτ
  have hx := right_ne_zero_of_mul hz
  field_simp

end Complex
end DLMF.JacobiElliptic
end
end
