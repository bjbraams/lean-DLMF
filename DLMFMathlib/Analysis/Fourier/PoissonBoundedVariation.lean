/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import Mathlib.Topology.Defs.Filter

/-!
# Poisson summation for bounded variation with jumps

Andrews, Askey and Roy, *Special Functions*, Theorem D.4.1. The spatial sum
uses the mean of the two one-sided limits and is absolutely convergent. The
Fourier sum is a symmetric ordered limit, not an unconditional sum.
-/

@[expose] public section

open Filter MeasureTheory
open scoped Topology

namespace Real

/-- Bounded-variation Poisson summation with a positive even decreasing integrable envelope.
Andrews–Askey–Roy, *Special Functions*, Theorem D.4.1, pp. 623–627
(synopsis AAR-D.4.1). -/
theorem tendsto_sum_Icc_fourier_of_boundedVariationOn_dominated (g : ℝ → ℂ)
    (hg : Integrable g) (hbv : BoundedVariationOn g Set.univ)
    (h : ℝ → ℝ) (hpos : ∀ t : ℝ, 0 < h t) (heven : ∀ t : ℝ, h (-t) = h t)
    (hint : Integrable h) (hmono : AntitoneOn h (Set.Ici 0))
    (hbound : ∀ t : ℝ, ‖g t‖ ≤ h t) (x : ℝ) :
    Summable (fun k : ℤ =>
      (limUnder (𝓝[>] (x + k)) g + limUnder (𝓝[<] (x + k)) g) / 2) ∧
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      FourierTransform.fourier g (n : ℝ) *
        Complex.exp (2 * Real.pi * Complex.I * n * x)) atTop
      (𝓝 (∑' k : ℤ,
        (limUnder (𝓝[>] (x + k)) g + limUnder (𝓝[<] (x + k)) g) / 2)) := by
  sorry

end Real
