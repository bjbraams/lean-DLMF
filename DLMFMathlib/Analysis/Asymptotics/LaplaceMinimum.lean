/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.Asymptotics.Defs

/-!
# Laplace asymptotics at finitely many separated quadratic minima

Olver, *Asymptotics and Special Functions*, Chapter 3, §7.1, p. 80,
synopsis O-3.06. Only local quadratic equivalents and amplitude continuity are
required near the minima; the remaining domain may be unbounded and improper.
-/

@[expose] public noncomputable section

open Filter Set MeasureTheory Asymptotics
open scoped Topology

namespace Asymptotics

/-- Each isolated quadratic global minimum contributes its own Gaussian leading term.
Olver, Chapter 3, §7.1, synopsis O-3.06. A single absolutely convergent Laplace
integral controls all distant tails. The domain can have finite or infinite endpoints. -/
theorem tendsto_sqrt_mul_integral_exp_of_finite_minima {ι : Type*} [Fintype ι]
    [Nonempty ι] {S : Set ℝ} (hS : MeasurableSet S) {p : ℝ → ℝ} {q : ℝ → ℂ}
    (hp : AEStronglyMeasurable p (volume.restrict S))
    (t : ι → ℝ) (ht : Function.Injective t) (hinterior : ∀ i, S ∈ 𝓝 (t i))
    (c : ι → ℝ) (hc : ∀ i, 0 < c i) (level x₀ : ℝ)
    (hphase : ∀ i, Tendsto (fun u : ℝ => (p u - level) / (u - t i) ^ 2)
      (𝓝[≠] (t i)) (𝓝 (c i / 2)))
    (hq : ∀ i, ContinuousAt q (t i))
    (hgap : ∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧
      ∀ u ∈ S, (∀ i, δ ≤ |u - t i|) → η ≤ p u - level)
    (hi : IntegrableOn (fun u => Real.exp (-x₀ * (p u - level)) • q u) S) :
    Tendsto (fun x : ℝ => Real.sqrt x •
      ∫ u in S, Real.exp (-x * (p u - level)) • q u) atTop
        (𝓝 (∑ i, (Real.sqrt (2 * Real.pi / c i) : ℂ) * q (t i))) := by
  sorry

end Asymptotics
