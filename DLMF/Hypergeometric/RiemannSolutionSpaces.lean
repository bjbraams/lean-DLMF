/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Riemann
public import Mathlib.LinearAlgebra.Pi

/-!
# Linear equivalences of Riemann solution spaces

The maps are actual complex-linear maps on function spaces, whose restrictions
are bijections between the indicated solution sets. Zero extension outside the
open domains removes irrelevant arbitrary values and makes injectivity meaningful.
All differential operators are the canonical existing Riemann and Gauss operators.
Source: Kristensson, *Second Order Differential Equations*, Chapter 4,
§§4.1–4.4, pp. 45–60; Chapter 5, §5.1, pp. 63–69; DLMF §15.11.
-/

@[expose] public noncomputable section

open Complex Set

namespace DLMF.Hypergeometric

/-- Möbius pullback gives a complex-linear bijection of Riemann solution spaces
on any open domain avoiding the marked points and the coordinate pole. The image
domain is explicit. Zero extension excludes irrelevant values outside either domain.
Kristensson, Chapter 4, Theorem 4.1, pp. 52–55; DLMF 15.11.5–15.11.6. -/
theorem exists_linearMap_bijOn_riemannSolutions_mobius
    (α β γ a₁ a₂ b₁ b₂ c₁ c₂ κ l μ ν : ℂ)
    (hdet : κ * ν - l * μ ≠ 0) (hfuchs : a₁ + a₂ + b₁ + b₂ + c₁ + c₂ = 1)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hβγ : β ≠ γ)
    (hα : μ * α + ν ≠ 0) (hβ : μ * β + ν ≠ 0) (hγ : μ * γ + ν ≠ 0)
    {U : Set ℂ} (hU : IsOpen U)
    (hregular : ∀ z ∈ U, μ * z + ν ≠ 0 ∧ z ≠ α ∧ z ≠ β ∧ z ≠ γ) :
    let T := fun z : ℂ => (κ * z + l) / (μ * z + ν)
    let V := T '' U
    ∃ L : (ℂ → ℂ) →ₗ[ℂ] (ℂ → ℂ),
      (∀ f z, L f z = U.indicator (fun w => f (T w)) z) ∧
      BijOn L
        (riemannSolutions (T α) (T β) (T γ) a₁ a₂ b₁ b₂ c₁ c₂ V ∩
          {f | ∀ z, z ∉ V → f z = 0})
        (riemannSolutions α β γ a₁ a₂ b₁ b₂ c₁ c₂ U ∩
          {f | ∀ z, z ∉ U → f z = 0}) := by
  sorry

/-- The normalized exponent gauge is a complex-linear bijection, with inverse
obtained by negating both gauge exponents. Principal powers are analytic and
nonzero on the indicated branch domain. Kristensson, Chapter 4, §4.3.1, (4.3),
pp. 49–50; DLMF 15.11.8. -/
theorem exists_linearMap_bijOn_riemannNormalSolutions_gauge
    (a₁ a₂ b₁ b₂ c₁ c₂ l m : ℂ)
    (hfuchs : a₁ + a₂ + b₁ + b₂ + c₁ + c₂ = 1)
    {U : Set ℂ} (hU : IsOpen U)
    (hbranch : ∀ z ∈ U, z ∈ slitPlane ∧ 1 - z ∈ slitPlane) :
    ∃ L : (ℂ → ℂ) →ₗ[ℂ] (ℂ → ℂ),
      (∀ f z, L f z = U.indicator (fun w => w ^ l * (1 - w) ^ m * f w) z) ∧
      BijOn L
        {f | ContDiffOn ℂ 2 f U ∧
          (∀ z ∈ U, riemannNormalOperator a₁ a₂ b₁ b₂ c₁ c₂ f z = 0) ∧
          ∀ z, z ∉ U → f z = 0}
        {f | ContDiffOn ℂ 2 f U ∧
          (∀ z ∈ U, riemannNormalOperator (a₁ + l) (a₂ + l) (b₁ + m) (b₂ + m)
            (c₁ - l - m) (c₂ - l - m) f z = 0) ∧ ∀ z, z ∉ U → f z = 0} := by
  sorry

/-- Every finite-three-singularity Riemann equation is linearly equivalent to the
Gauss equation after the explicit cross-ratio and exponent gauge. No nonresonance
hypothesis is needed for an equivalence of differential-equation solution spaces.
Kristensson, Chapter 4, §4.3.1, (4.3), pp. 49–50, and Theorem 4.1, pp. 52–55;
Chapter 5, §5.1, pp. 63–69; DLMF 15.11.7. -/
theorem exists_linearMap_bijOn_riemannSolutions_gauss
    (α β γ a₁ a₂ b₁ b₂ c₁ c₂ : ℂ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hβγ : β ≠ γ)
    (hfuchs : a₁ + a₂ + b₁ + b₂ + c₁ + c₂ = 1)
    {U : Set ℂ} (hU : IsOpen U)
    (hregular : ∀ z ∈ U, z ≠ α ∧ z ≠ β ∧ z ≠ γ)
    (hbranch : ∀ z ∈ U,
      (z - α) / (z - γ) ∈ slitPlane ∧ (z - β) / (z - γ) ∈ slitPlane) :
    let T := fun z : ℂ => (z - α) * (β - γ) / ((z - γ) * (β - α))
    let V := T '' U
    let A := a₁ + b₁ + c₁
    let B := a₁ + b₁ + c₂
    let C := 1 + a₁ - a₂
    ∃ L : (ℂ → ℂ) →ₗ[ℂ] (ℂ → ℂ),
      (∀ f z, L f z = U.indicator (fun w =>
        ((w - α) / (w - γ)) ^ a₁ * ((w - β) / (w - γ)) ^ b₁ * f (T w)) z) ∧
      BijOn L
        {f | ContDiffOn ℂ 2 f V ∧ (∀ z ∈ V, gaussOperator A B C f z = 0) ∧
          ∀ z, z ∉ V → f z = 0}
        (riemannSolutions α β γ a₁ a₂ b₁ b₂ c₁ c₂ U ∩
          {f | ∀ z, z ∉ U → f z = 0}) := by
  sorry

end DLMF.Hypergeometric
