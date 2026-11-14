/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Darboux's continuous-boundary coefficient principle

Andrews, Askey and Roy, *Special Functions*, Theorem 6.6.1. Coefficients are
identified by actual convergent power-series expansions inside the disk.
-/

@[expose] public section

open Filter
open scoped Topology

namespace Complex

/-- If two power-series sums have a difference continuous on the closed disk,
their coefficient difference is little-o of the inverse radius power.
Andrews–Askey–Roy, *Special Functions*, Theorem 6.6.1
(synopsis AAR-6.5.1–6.6.2). -/
theorem isLittleO_coeff_sub_of_continuousOn_closedBall {r : ℝ} (hr : 0 < r)
    (f g : ℂ → ℂ) (a b : ℕ → ℂ)
    (hf : ∀ z : ℂ, ‖z‖ < r → HasSum (fun n => a n * z ^ n) (f z))
    (hg : ∀ z : ℂ, ‖z‖ < r → HasSum (fun n => b n * z ^ n) (g z))
    (hcont : ContinuousOn (fun z => f z - g z) (Metric.closedBall 0 r)) :
    (fun n => a n - b n) =o[atTop] (fun n : ℕ => (r : ℂ) ^ (-(n : ℤ))) := by
  sorry

end Complex
