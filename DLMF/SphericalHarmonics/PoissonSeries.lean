/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Basic.Classical
public import Mathlib.Topology.UniformSpace.UniformConvergence
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Uniform Gegenbauer expansion of the ball Poisson kernel

Andrews, Askey and Roy, *Special Functions*, Theorem 9.9.1, pp. 463–464.
Uniformity includes the full closed angular interval and every smaller closed
radial disk. There is no boundary convergence assertion at radius one.
-/

@[expose] public section

namespace DLMF.SphericalHarmonics

/-- The Poisson-kernel Gegenbauer series converges uniformly for `|r| ≤ R < 1` and
`-1 ≤ t ≤ 1`. Andrews–Askey–Roy, *Special Functions*, Theorem 9.9.1, pp. 463–464
(synopsis AAR-9.9.1). Surface measure is normalized to probability in this kernel. -/
theorem tendstoUniformlyOn_poissonKernel_gegenbauer {n : ℕ} (hn : 3 ≤ n)
    {R : ℝ} (hR : 0 ≤ R) (hRone : R < 1) :
    let lam : ℂ := ((n : ℂ) - 2) / 2
    TendstoUniformlyOn
      (fun N : ℕ => fun p : ℝ × ℝ =>
        ∑ k ∈ Finset.range N, ((k : ℂ) + lam) / lam *
          DLMF.OrthogonalPolynomials.ultrasphericalPolynomial lam k p.2 * (p.1 : ℂ) ^ k)
      (fun p : ℝ × ℝ =>
        (1 - (p.1 : ℂ) ^ 2) / (1 - 2 * (p.1 : ℂ) * p.2 + (p.1 : ℂ) ^ 2) ^
          ((n : ℂ) / 2))
      Filter.atTop (Set.Icc (-R) R ×ˢ Set.Icc (-1) 1) := by
  sorry

end DLMF.SphericalHarmonics
