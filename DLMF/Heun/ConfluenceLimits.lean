/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Heun.Basic.Equation
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-!
# Square-root confluence of Heun's equation

Kristensson, *Second Order Differential Equations*, §§8.5–8.6, pp. 158–161.
The book's scaled accessory parameter is retained as `q=a b h`. The limiting
equation uses the existing `IsConfluentHeunSolutionOn` predicate with its
constant first-derivative coefficient equal to zero.
-/

@[expose] public section

open Complex Filter Set
open scoped Topology

noncomputable section

namespace DLMF.Heun

/-- Kristensson, (8.17), p. 158: square-root growth of the two exponents at
infinity gives locally uniform limits of both Heun coefficients off `0,1`. -/
theorem tendstoLocallyUniformlyOn_heun_coefficients_sqrt
    (k₁ k₂ c d h : ℂ) :
    TendstoLocallyUniformlyOn
      (fun A : ℝ => heunCoeffP A c d
        (k₁ * Real.sqrt A + k₂ * Real.sqrt A + 1 - c - d))
      (fun z => c / z + d / (z - 1)) atTop ({0, 1} : Set ℂ)ᶜ ∧
    TendstoLocallyUniformlyOn
      (fun A : ℝ => heunCoeffR A
        ((k₁ * Real.sqrt A) * (k₂ * Real.sqrt A) * h)
        (k₁ * Real.sqrt A) (k₂ * Real.sqrt A))
      (fun z => -(k₁ * k₂) * (z - h) / (z * (z - 1)))
      atTop ({0, 1} : Set ℂ)ᶜ := by
  sorry

/-- Kristensson, (8.18), p. 159: the square substitution in the singly
confluent equation, with its exact first- and zeroth-order coefficients. -/
theorem isLinearODE2On_comp_sq_of_confluentHeun {c d K h : ℂ}
    {u : ℂ → ℂ} {U V : Set ℂ} (hU : IsOpen U)
    (himage : (fun t : ℂ => t ^ 2) '' U ⊆ V)
    (hzero : ∀ t ∈ U, t ≠ 0) (hone : ∀ t ∈ U, t ^ 2 ≠ 1)
    (hu : IsConfluentHeunSolutionOn (-(K * h)) (-K) c d 0 u V) :
    IsLinearODE2On
      (fun t => (2 * c - 1) / t - 2 * d * t / (1 - t ^ 2))
      (fun t => -4 * K * (h - t ^ 2) / (1 - t ^ 2))
      (fun t => u (t ^ 2)) U := by
  sorry

/-- Kristensson, §8.6, pp. 160–161: the entire spheroidal factor equation is a
square pullback of the singly confluent Heun equation. The undivided accessory
parameter also covers `χ=0`, where the book's parameter `h` is not defined. -/
theorem isLinearODE2On_spheroidalFactor_of_confluentHeun {lam χ m : ℂ}
    {u : ℂ → ℂ} {U V : Set ℂ} (hU : IsOpen U)
    (himage : (fun t : ℂ => t ^ 2) '' U ⊆ V)
    (hzero : ∀ t ∈ U, t ≠ 0) (hone : ∀ t ∈ U, t ^ 2 ≠ 1)
    (hu : IsConfluentHeunSolutionOn ((lam + χ ^ 2 - m * (m + 1)) / 4)
      (χ ^ 2 / 4) (1 / 2) (m + 1) 0 u V) :
    IsLinearODE2On
      (fun t => -2 * (m + 1) * t / (1 - t ^ 2))
      (fun t => (lam - m * (m + 1) + χ ^ 2 * (1 - t ^ 2)) / (1 - t ^ 2))
      (fun t => u (t ^ 2)) U := by
  sorry

end DLMF.Heun
