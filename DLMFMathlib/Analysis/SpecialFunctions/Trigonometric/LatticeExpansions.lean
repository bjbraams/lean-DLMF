/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-!
# Locally uniform trigonometric lattice expansions

Andrews, Askey and Roy, *Special Functions*, Theorem 1.2.2, pp. 9–11
(synopsis AAR-1.2.1–1.2.7). Mathlib supplies Euler's sine product and the
paired cotangent partial fractions pointwise. These statements retain their
locally uniform convergence and the absolutely convergent square-lattice sum.
-/

@[expose] public section

open Filter Finset
open scoped Topology

namespace Complex

/-- Euler's sine product converges locally uniformly on the entire plane.
Andrews–Askey–Roy, *Special Functions*, Theorem 1.2.2
(synopsis AAR-1.2.1–1.2.7). The prefactor retains the value at zero. -/
theorem tendstoLocallyUniformly_euler_sin_prod :
    TendstoLocallyUniformly
      (fun N (z : ℂ) => (Real.pi : ℂ) * z *
        ∏ n ∈ range N, (1 - z ^ 2 / ((n + 1 : ℕ) : ℂ) ^ 2))
      (fun z : ℂ => sin (Real.pi * z)) atTop := by
  sorry

/-- The paired cotangent expansion converges locally uniformly off the integer lattice.
Andrews–Askey–Roy, *Special Functions*, Theorem 1.2.2
(synopsis AAR-1.2.1–1.2.7). The displayed symmetric pairing is part of the statement. -/
theorem tendstoLocallyUniformlyOn_cot_series :
    TendstoLocallyUniformlyOn
      (fun N (z : ℂ) => z⁻¹ +
        ∑ n ∈ range N, 2 * z / (z ^ 2 - ((n + 1 : ℕ) : ℂ) ^ 2))
      (fun z : ℂ => (Real.pi : ℂ) * cot (Real.pi * z)) atTop integerComplement := by
  sorry

/-- The reciprocal-square lattice expansion of the squared cosecant is absolute.
Andrews–Askey–Roy, *Special Functions*, Theorem 1.2.2
(synopsis AAR-1.2.1–1.2.7). No choice of ordering is needed for this series. -/
theorem hasSum_one_div_add_intCast_sq {z : ℂ} (hz : z ∈ integerComplement) :
    HasSum (fun n : ℤ => 1 / (z + n) ^ 2)
      ((Real.pi : ℂ) ^ 2 / sin (Real.pi * z) ^ 2) := by
  sorry

/-- Symmetric square-lattice partial sums converge locally uniformly off the poles.
Andrews–Askey–Roy, *Special Functions*, Theorem 1.2.2
(synopsis AAR-1.2.1–1.2.7). -/
theorem tendstoLocallyUniformlyOn_one_div_add_intCast_sq :
    TendstoLocallyUniformlyOn
      (fun N (z : ℂ) => ∑ n ∈ Icc (-(N : ℤ)) (N : ℤ), 1 / (z + n) ^ 2)
      (fun z : ℂ => (Real.pi : ℂ) ^ 2 / sin (Real.pi * z) ^ 2)
      atTop integerComplement := by
  sorry

end Complex
