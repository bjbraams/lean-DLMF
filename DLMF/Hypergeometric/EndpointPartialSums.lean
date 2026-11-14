/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Asymptotics of Gauss partial sums at one

Andrews, Askey and Roy, *Special Functions*, Theorem 2.1.4, pp. 63–65.
These are ordered finite partial sums of the canonical Gauss coefficients.
The normalized-limit formulation includes vanishing leading coefficients at
terminating upper parameters. No divergent infinite series is totalized as a limit.
-/

@[expose] public section

open Complex Filter
open scoped Topology

namespace DLMF.Hypergeometric

/-- Power growth of the Gauss coefficient partial sums at argument one.
Andrews–Askey–Roy, *Special Functions*, Theorem 2.1.4, pp. 63–65
(synopsis AAR-2.1.1–2.1.5). The reciprocal-gamma convention includes terminating
upper parameters, where the normalized limit is zero. -/
theorem tendsto_sum_gaussHypergeometricCoeff_div_cpow {a b c : ℂ}
    (hc : ∀ k : ℕ, c ≠ -(k : ℂ)) (hexcess : 0 < (a + b - c).re) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, gaussHypergeometricCoeff a b c n) /
        (N : ℂ) ^ (a + b - c)) atTop
      (𝓝 (Gamma c / (Gamma a * Gamma b * (a + b - c)))) := by
  sorry

/-- Logarithmic growth of the zero-excess Gauss coefficient partial sums.
Andrews–Askey–Roy, *Special Functions*, Theorem 2.1.4, pp. 63–65
(synopsis AAR-2.1.1–2.1.5). The lower parameter is regular, while every upper
parameter is permitted through the reciprocal-gamma normalization. -/
theorem tendsto_sum_gaussHypergeometricCoeff_div_log {a b : ℂ}
    (hc : ∀ k : ℕ, a + b ≠ -(k : ℂ)) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, gaussHypergeometricCoeff a b (a + b) n) /
        (Real.log N : ℂ)) atTop (𝓝 (Gamma (a + b) / (Gamma a * Gamma b))) := by
  sorry

end DLMF.Hypergeometric
