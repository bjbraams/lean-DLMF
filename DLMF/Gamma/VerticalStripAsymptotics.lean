/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Gamma.Basic
public import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Stirling's magnitude formula uniformly on vertical strips

Andrews, Askey and Roy, *Special Functions*, Corollaries 1.4.3–1.4.5,
pp. 20–22 (synopsis AAR-1.4.1–1.4.5). Both signs of the imaginary part
are included. Uniformity is with respect to the real part on any compact interval.
-/

@[expose] public section

open Filter

namespace DLMF.Gamma

/-- Stirling's Gamma magnitude asymptotic is uniform when the real part stays in a
compact interval. Andrews–Askey–Roy, *Special Functions*, Corollaries 1.4.3–1.4.5,
pp. 20–22 (synopsis AAR-1.4.1–1.4.5); DLMF 5.11.9. The two-sided filter
expresses `|t| → ∞`, retaining both conjugate vertical directions. -/
theorem tendstoUniformlyOn_norm_Gamma_vertical_div (a b : ℝ) :
    TendstoUniformlyOn
      (fun (t : ℝ) (σ : ℝ) => ‖Complex.Gamma (σ + t * Complex.I)‖ /
        (Real.sqrt (2 * Real.pi) * |t| ^ (σ - 1 / 2) *
          Real.exp (-Real.pi * |t| / 2)))
      (fun _ => (1 : ℝ)) (atTop ⊔ atBot) (Set.Icc a b) := by
  sorry

end DLMF.Gamma
