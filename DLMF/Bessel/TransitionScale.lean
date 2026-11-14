/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bessel.Basic
public import DLMF.Airy.Basic
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The Airy transition scale for large real Bessel order

Olver, *Asymptotics and Special Functions*, Chapter 9, §5,
pp. 334–336, synopsis O-9.06. The remainder is absolute and uniform for
complex shifts in compact sets; no division by an Airy factor occurs.
-/

@[expose] public noncomputable section
open Complex Filter Asymptotics
open scoped Topology
namespace DLMF.Bessel

/-- Compact-complex uniform Airy transition with absolute `O(nu^(-1))` error.
Olver, Chapter 9, §5, pp. 334–336. It includes zeros of the leading Airy factor. -/
theorem exists_norm_besselJ_transition_sub_airy_le {K : Set ℂ} (hK : IsCompact K) :
    ∃ C R : ℝ, 0 < C ∧ 0 < R ∧ ∀ ν : ℝ, R ≤ ν → ∀ a ∈ K,
      ‖besselJ ν ((ν : ℂ) + a * (ν ^ (1 / 3 : ℝ) : ℝ)) -
        ((2 : ℝ) ^ (1 / 3 : ℝ) * ν ^ (-1 / 3 : ℝ) : ℝ) *
          DLMF.Airy.airyAi (-((2 : ℝ) ^ (1 / 3 : ℝ) : ℝ) * a)‖ ≤ C / ν := by
  sorry

end DLMF.Bessel
