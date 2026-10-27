/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Core.Upstream
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.MellinTransform

/-!
# Mathlib coverage of DLMF §2.6

Pointers from DLMF §2.6 items to existing Mathlib declarations.
-/

dlmf_upstream 2.6.E58 not_integrableOn_Ioi_rpow
  "exact: the integrals ∫_0^∞ t^λ dt, λ ∈ ℝ, diverge (t^λ is not integrable on (0, ∞))"

dlmf_upstream 2.6.E61 mellin_comp_mul_left
  "stronger: 𝓜(h(x·))(s) = x^{-s} 𝓜h(s) for all s and x > 0; DLMF uses s = j + α"
