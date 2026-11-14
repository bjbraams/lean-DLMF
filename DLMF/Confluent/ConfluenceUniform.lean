/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.Confluence
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-!
# Locally uniform confluence limits

Kristensson, *Second Order Differential Equations*, Chapter 7, (7.1), pp. 123–125,
and (7.10)–(7.11), pp. 132–133. Limits are locally uniform in the complex argument.
The limiting `₀F₁` is used directly as Mathlib's regularized series times `Γ(c)`.
-/

@[expose] public section

open Complex Filter
open scoped Topology

namespace DLMF.Confluent

/-- Kristensson, Chapter 7, (7.1), pp. 123–125: Gauss-to-Kummer confluence,
locally uniformly in the argument. A fixed complex shift of the large upper parameter
is allowed, as in the existing pointwise confluence theorem. -/
theorem tendstoLocallyUniformly_ordinaryHypergeometric_add_div_atTop
    (a c d : ℂ) (hc : ∀ n : ℕ, c ≠ -(n : ℂ)) :
    TendstoLocallyUniformly
      (fun t : ℝ => fun z : ℂ => ordinaryHypergeometric a (d + t) c (z / t))
      (kummerM a c) atTop := by
  sorry

/-- Kristensson, Chapter 7, (7.10), pp. 132–133: sending both upper parameters
to infinity at square-root rate gives `₀F₁` with argument `k₁ k₂ z`.
The assertion includes zero values of either scale factor. -/
theorem tendstoLocallyUniformly_ordinaryHypergeometric_sqrt_div_atTop
    (k₁ k₂ c : ℂ) (hc : ∀ n : ℕ, c ≠ -(n : ℂ)) :
    TendstoLocallyUniformly
      (fun t : ℝ => fun z : ℂ => ordinaryHypergeometric
        (k₁ * Real.sqrt t) (k₂ * Real.sqrt t) c (z / t))
      (fun z => Gamma c * regularizedHGFun (∅ : Multiset ℂ) {c} (k₁ * k₂ * z))
      atTop := by
  sorry

end DLMF.Confluent
