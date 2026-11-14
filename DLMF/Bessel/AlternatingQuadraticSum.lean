/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bessel.Basic.SecondKind
public import DLMF.Core.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
public import Mathlib.Analysis.Asymptotics.Defs

/-!
# Alternating quadratic sums and Macdonald functions

Olver, *Asymptotics and Special Functions*, Chapter 8, §7, pp. 302–304.
The left series is an ordinary symmetric limit, which includes conditionally
convergent orders. The right series converges absolutely and locally uniformly in
the right half-plane. Its finite truncations have exponentially small tails on
proper closed right subsectors. Every power is principal, continued from positive `z`.
-/

@[expose] public noncomputable section

open Complex Filter Finset
open scoped Real Topology Asymptotics

namespace DLMF.Bessel

/-- The Macdonald series for the alternating quadratic sum converges normally,
locally uniformly in both complex parameters in their right half-planes.
Olver, Chapter 8, §7, pp. 302–304. -/
theorem summableLocallyUniformlyOn_norm_alternatingQuadratic_macdonald :
    SummableLocallyUniformlyOn
      (fun k : ℕ => fun p : ℂ × ℂ =>
        ‖((k : ℂ) + 1 / 2) ^ (p.1 - 1 / 2) *
          besselK (p.1 - 1 / 2) (2 * Real.pi * ((k : ℂ) + 1 / 2) * p.2)‖)
      {p : ℂ × ℂ | 0 < p.1.re ∧ 0 < p.2.re} := by
  sorry

/-- The alternating two-sided quadratic sum equals the half-integer Macdonald
series. The left side is a symmetric ordinary limit; absolute convergence of that
left side is not assumed. Olver, Chapter 8, §7, pp. 302–304. -/
theorem tendsto_alternatingQuadraticSum_eq_macdonald {α z : ℂ}
    (hα : 0 < α.re) (hz : 0 < z.re) :
    Tendsto
      (fun N : ℕ => ∑ j ∈ Icc (-(N : ℤ)) (N : ℤ),
        (-1 : ℂ) ^ j / (z ^ 2 + (j : ℂ) ^ 2) ^ α)
      atTop
      (𝓝 (4 * (Real.pi : ℂ) ^ α * z ^ (1 / 2 - α) / Gamma α *
        ∑' k : ℕ, ((k : ℂ) + 1 / 2) ^ (α - 1 / 2) *
          besselK (α - 1 / 2) (2 * Real.pi * ((k : ℂ) + 1 / 2) * z))) := by
  sorry

/-- Every fixed Macdonald truncation leaves a tail at the next exponential scale,
uniformly on a proper closed right-half-plane sector. Olver, Chapter 8, §7,
pp. 302–304. This is an absolute error, including at zeros of a truncated sum. -/
theorem isBigO_alternatingQuadratic_macdonald_tail {α : ℂ} (hα : 0 < α.re)
    (N : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < Real.pi / 2) :
    (fun z : ℂ => 4 * (Real.pi : ℂ) ^ α * z ^ (1 / 2 - α) / Gamma α *
      ((∑' k : ℕ, ((k : ℂ) + 1 / 2) ^ (α - 1 / 2) *
          besselK (α - 1 / 2) (2 * Real.pi * ((k : ℂ) + 1 / 2) * z)) -
        ∑ k ∈ range N, ((k : ℂ) + 1 / 2) ^ (α - 1 / 2) *
          besselK (α - 1 / 2) (2 * Real.pi * ((k : ℂ) + 1 / 2) * z)))
      =O[DLMF.Core.sector (Real.pi / 2 - δ)]
        (fun z : ℂ => z ^ (-α) * exp (-2 * Real.pi * ((N : ℂ) + 1 / 2) * z)) := by
  sorry

end DLMF.Bessel
