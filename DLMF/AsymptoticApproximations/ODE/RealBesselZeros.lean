/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AsymptoticApproximations.ODE.RealBesselExpansion
public import DLMF.Bessel.FourierBessel
public import DLMF.Confluent.Basic.Whittaker
public import Mathlib.Analysis.Asymptotics.Defs

/-!
# Zeros of real simple-pole perturbations

The all-index estimates use complete adjacent comparison brackets inside the
transformed interval. Squaring the argument error retains both terms in the
coordinate error. The Whittaker application concerns a fixed zero index, and
does not assert infinitely many positive Whittaker zeros at each fixed parameter.
Source: Olver, *Asymptotics and Special Functions*, Chapter 12,
§7, pp. 451–453.
-/

@[expose] public noncomputable section

open Complex Set Filter ODE
open scoped Real Topology Asymptotics

namespace DLMF.AsymptoticApproximations.Real

/-- The real `J`/`Y` comparison solutions have one zero in every full bracket
and an argument displacement uniformly `O(1/u)` in the index. The squared
coordinate estimate keeps the additional `u^-4` term. Olver,
Chapter 12, §7, pp. 451–453. -/
theorem exists_simplePole_solutions_with_uniform_zero_bounds
    {D : Set ℝ} (hD : IsOpen D) (hconvex : Convex ℝ D) (hzero : 0 ∈ D)
    {α : EReal} (hα : α < 0) (hinterval : {x : ℝ | α < (x : EReal) ∧ x ≤ 0} ⊆ D)
    {ψ : ℝ → ℝ} {A B : ℕ → ℝ → ℂ} {ν : ℝ} (hν : 0 ≤ ν)
    (hcoeff : IsSimplePoleCoefficientSequence (fun x => (ψ x : ℂ)) ν A B D)
    (hvar : BoundedVariationOn (fun x : ℝ => (Real.sqrt |x| : ℂ) * B 0 x)
      {x : ℝ | α < (x : EReal) ∧ x < 0})
    (j y : ℕ → ℝ) (hj : DLMF.Bessel.IsPositiveBesselZeroSequence ν j)
    (hypos : ∀ n, 0 < y n) (hymono : StrictMono y) (hylim : Tendsto y atTop atTop)
    (hy : ∀ x : ℝ, 0 < x → (DLMF.Bessel.besselY ν x = 0 ↔ ∃ n, y n = x)) :
    ∃ (W : Fin 2 → ℝ → ℝ → ℝ) (C R : ℝ), 0 < C ∧ 0 < R ∧
      (∀ k u, R ≤ u → ContDiffOn ℝ 2 (W k u)
        {x : ℝ | α < (x : EReal) ∧ x < 0}) ∧
      (∀ (k : Fin 2) (u x : ℝ), R ≤ u → α < (x : EReal) → x < 0 →
        deriv (deriv (W k u)) x =
          (u ^ 2 / (4 * x) + (ν ^ 2 - 1) / (4 * x ^ 2) + ψ x / x) * W k u x) ∧
      (∀ (u x : ℝ), R ≤ u → α < (x : EReal) → x < 0 →
        u * Real.sqrt (-x) ≤ y 0 → W 0 u x ≠ 0) ∧
      (∀ (u : ℝ) (n : ℕ), R ≤ u →
        let left := -(y (n + 1) / u) ^ 2
        let right := -(y n / u) ^ 2
        α < (left : EReal) →
          (∃! x, x ∈ Ioo left right ∧ W 0 u x = 0) ∧
          ∀ x ∈ Ioo left right, W 0 u x = 0 →
            |u * Real.sqrt (-x) - j n| ≤ C / u ∧
              |x + j n ^ 2 / u ^ 2| ≤ C * (j n / u ^ 3 + 1 / u ^ 4)) ∧
      ∀ (u : ℝ) (n : ℕ), R ≤ u →
        let left := -(j n / u) ^ 2
        let right := if n = 0 then 0 else -(j (n - 1) / u) ^ 2
        α < (left : EReal) →
          (∃! x, x ∈ Ioo left right ∧ W 1 u x = 0) ∧
          ∀ x ∈ Ioo left right, W 1 u x = 0 →
            |u * Real.sqrt (-x) - y n| ≤ C / u ∧
              |x + y n ^ 2 / u ^ 2| ≤ C * (y n / u ^ 3 + 1 / u ^ 4) := by
  sorry

/-- Each fixed positive Whittaker zero starts with the corresponding squared
Bessel zero. The exact preceding-zero count fixes the index; no assertion about
an infinite zero family at a fixed `kappa` is needed. Olver, Chapter 12,
§7, pp. 452–453. -/
theorem isBigO_whittakerM_fixed_positive_zero {m : ℝ} (hm : 0 ≤ m)
    (j : ℕ → ℝ) (hj : DLMF.Bessel.IsPositiveBesselZeroSequence (2 * m) j)
    (x : ℝ → ℝ) (n : ℕ)
    (hzero : ∀ᶠ κ : ℝ in atTop, 0 < x κ ∧ DLMF.Confluent.whittakerM κ m (x κ) = 0 ∧
      ({t : ℝ | 0 < t ∧ t < x κ ∧ DLMF.Confluent.whittakerM κ m t = 0} : Set ℝ).ncard = n) :
    (fun κ : ℝ => x κ - j n ^ 2 / (4 * κ)) =O[atTop] (fun κ : ℝ => κ ^ (-2 : ℝ)) := by
  sorry

end DLMF.AsymptoticApproximations.Real
