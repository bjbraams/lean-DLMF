/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.ChebyshevExpansion
public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Uniform reciprocal Chebyshev expansion

Temme, *Special Functions*, Example 6.3, pp. 163–164. The coefficients of the
existing pointwise expansion also give convergence uniformly on the closed interval.
-/

@[expose] public section

open Filter
open scoped Topology

namespace DLMF.OrthogonalPolynomials

/-- The reciprocal Chebyshev expansion converges uniformly on the closed interval.
Temme, *Special Functions*, Example 6.3, (6.66), pp. 163–164
(synopsis TEM-06-16). -/
theorem tendstoUniformlyOn_chebyshevT_recip_add {a : ℝ} (ha : 1 < a) :
    TendstoUniformlyOn (fun N : ℕ => fun x : ℝ =>
      (1 + 2 * ∑ n ∈ Finset.range N,
        (Real.sqrt (a ^ 2 - 1) - a) ^ (n + 1) *
          (Polynomial.Chebyshev.T ℝ (n + 1)).eval x) / Real.sqrt (a ^ 2 - 1))
      (fun x : ℝ => (a + x)⁻¹) atTop (Set.Icc (-1) 1) := by
  sorry

/-- The Chebyshev series of a function of bounded variation converges at an interior point
to its two-sided average. Temme, *Special Functions*, §6.9.2, equations (6.65)–(6.66),
pp. 163–164 (synopsis TEM-06-16). This is the Dirichlet–Jordan Fourier convergence
criterion transferred by `x = cos θ`; one-sided values are specified by their limits. -/
theorem tendsto_sum_chebyshevCoeff_of_boundedVariationOn
    {f : ℝ → ℝ} (hf : BoundedVariationOn f (Set.Icc (-1) 1))
    {x left right : ℝ} (hx : x ∈ Set.Ioo (-1) 1)
    (hleft : Tendsto f (nhdsWithin x (Set.Iio x)) (nhds left))
    (hright : Tendsto f (nhdsWithin x (Set.Ioi x)) (nhds right)) :
    Tendsto (fun N : ℕ =>
      ∑ n ∈ Finset.range (N + 1),
        (if n = 0 then 1 / 2 else 1) * chebyshevCoeff f n *
          (Polynomial.Chebyshev.T ℝ n).eval x)
      atTop (nhds ((left + right) / 2)) := by
  sorry

end DLMF.OrthogonalPolynomials
