/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Gamma.Kummer
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# Kummer's pointwise Fourier expansion

Andrews, Askey and Roy, *Special Functions*, Theorem 1.7.1, pp. 29–31
(synopsis AAR-1.6.1–1.7.1). Convergence uses ordered partial sums, since the
logarithmic sine series is conditionally convergent in the open unit interval.
-/

@[expose] public section

namespace DLMF.Gamma.Real

/-- Kummer's Fourier expansion of the real logarithmic gamma function.
Andrews–Askey–Roy, *Special Functions*, Theorem 1.7.1, pp. 29–31
(synopsis AAR-1.6.1–1.7.1). -/
theorem tendsto_sum_log_Gamma_sine {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N,
      Real.log (n + 1) / (n + 1) * Real.sin (2 * Real.pi * (n + 1) * x))
      Filter.atTop (nhds (Real.pi * (Real.log (Real.Gamma x) - Real.log (2 * Real.pi) / 2 +
        Real.log (2 * Real.sin (Real.pi * x)) / 2 -
        (Real.eulerMascheroniConstant + Real.log (2 * Real.pi)) * (1 / 2 - x)))) := by
  sorry

end DLMF.Gamma.Real
