/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bessel.Elementary
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-!
# Uniform convergence of Bessel generating series

Temme, *Special Functions* (1996), Chapter 9, (9.20)–(9.24), (9.33)–(9.34),
pp. 229–235, synopses TEM-09-05 and TEM-09-07. Bilateral sums use symmetric
finite cutoffs; the existing `HasSum` results also give absolute convergence.
-/

@[expose] public noncomputable section
open Complex Filter Finset
open scoped Topology
namespace DLMF.Bessel

/-- The J generating series converges locally uniformly on the punctured generating plane,
Temme (9.20)–(9.24), synopsis TEM-09-05. -/
theorem tendstoLocallyUniformlyOn_sum_besselJ_generating (z : ℂ) :
    TendstoLocallyUniformlyOn
      (fun N : ℕ => fun t : ℂ => ∑ m ∈ Icc (-(N : ℤ)) N, besselJ m z * t ^ m)
      (fun t : ℂ => exp (z * (t - t⁻¹) / 2)) atTop {t : ℂ | t ≠ 0} := by
  sorry

/-- The I generating series converges locally uniformly on the punctured generating plane,
Temme (9.33)–(9.34), synopsis TEM-09-07. -/
theorem tendstoLocallyUniformlyOn_sum_besselI_generating (z : ℂ) :
    TendstoLocallyUniformlyOn
      (fun N : ℕ => fun t : ℂ => ∑ m ∈ Icc (-(N : ℤ)) N, besselI m z * t ^ m)
      (fun t : ℂ => exp (z * (t + t⁻¹) / 2)) atTop {t : ℂ | t ≠ 0} := by
  sorry

/-- The I cosine series converges uniformly in the whole real angle,
Temme (9.33)–(9.34), synopsis TEM-09-07. -/
theorem tendstoUniformly_sum_besselI_cos (z : ℂ) :
    TendstoUniformly
      (fun N : ℕ => fun θ : ℝ => besselI 0 z + 2 * ∑ n ∈ range N,
        besselI (n + 1) z * Real.cos ((n + 1) * θ))
      (fun θ : ℝ => exp (z * Real.cos θ)) atTop := by
  sorry

end DLMF.Bessel
