/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
public import Mathlib.Topology.Algebra.InfiniteSum.Defs

/-!
# Zeros of locally absolutely convergent analytic products

Andrews, Askey and Roy, *Special Functions*, Corollary A.1.6, pp. 597–598.
These statements concern arbitrary analytic factors. TauCeti's canonical-product
zero-order theorem covers only its particular Weierstrass factors.
-/

@[expose] public section

open Filter

namespace Complex

/-- A locally uniformly convergent product of analytic factors is analytic, and under
absolute convergence its zeros and their orders come exactly from the factors.
Andrews–Askey–Roy, *Special Functions*, Corollary A.1.6, pp. 597–598
(synopsis AAR-A.1.1–A.1.6). The order sum is finite except for a possible
identically zero factor, whose analytic order is infinity. -/
theorem analyticOnNhd_product_zero_order {U : Set ℂ} (hU : IsOpen U)
    (f : ℕ → ℂ → ℂ) (hf : ∀ n, AnalyticOnNhd ℂ (f n) U) (F : ℂ → ℂ)
    (hF : TendstoLocallyUniformlyOn
      (fun N : ℕ => fun z : ℂ => ∏ n ∈ Finset.range N, f n z) F atTop U)
    (habs : ∀ z ∈ U, Summable fun n : ℕ => ‖f n z - 1‖) :
    AnalyticOnNhd ℂ F U ∧ ∀ z ∈ U,
      (F z = 0 ↔ ∃ n : ℕ, f n z = 0) ∧
      analyticOrderAt F z = ∑ᶠ n : ℕ, analyticOrderAt (f n) z := by
  sorry

end Complex
