/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QSeries.Basic
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-!
# Local uniform convergence and zeros of shifted-factorial products

Andrews, Askey and Roy, *Special Functions*, §§10.1 and 10.4, pp. 481–499.
All product zero sets are stated through their actual factors, including `q = 0`.
-/

@[expose] public noncomputable section

open scoped Classical

namespace DLMF.QSeries

/-- The shifted-factorial products converge locally uniformly in their parameter.
Andrews–Askey–Roy, *Special Functions*, §10.1, pp. 481–485
(synopsis AAR-10.1–10.2.4). -/
theorem tendstoLocallyUniformly_qPochhammer {q : ℂ} (hq : ‖q‖ < 1) :
    TendstoLocallyUniformly (fun N : ℕ => fun a : ℂ => qPochhammer a q N)
      (fun a : ℂ => qPochhammerInf a q) Filter.atTop := by
  sorry

/-- The infinite shifted factorial is entire in its first parameter.
Andrews–Askey–Roy, *Special Functions*, §10.1, pp. 481–485
(synopsis AAR-10.1–10.2.4). -/
theorem analyticOnNhd_qPochhammerInf {q : ℂ} (hq : ‖q‖ < 1) :
    AnalyticOnNhd ℂ (fun a : ℂ => qPochhammerInf a q) Set.univ := by
  sorry

/-- Exactly one factor vanishes at each zero of the infinite shifted factorial, so its
analytic order is one there and zero elsewhere. Andrews–Askey–Roy,
*Special Functions*, §10.1, pp. 481–485 (synopsis AAR-10.1–10.2.4).
For nonzero `q` these zeros are precisely `q^(-j)`; for `q = 0` only `a = 1` remains. -/
theorem analyticOrderAt_qPochhammerInf {q : ℂ} (hq : ‖q‖ < 1) (a : ℂ) :
    analyticOrderAt (fun z : ℂ => qPochhammerInf z q) a =
      if ∃ j : ℕ, a * q ^ j = 1 then 1 else 0 := by
  sorry

/-- The triple-product series converges locally uniformly on the punctured plane.
Andrews–Askey–Roy, *Special Functions*, Theorem 10.4.1, pp. 496–498
(synopsis AAR-10.4.1–10.6.1). The integer triangular exponent avoids any
unnecessary branch choice in the base `q`. -/
theorem tendstoLocallyUniformlyOn_jacobi_triple_product {q : ℂ} (hq : ‖q‖ < 1) :
    TendstoLocallyUniformlyOn
      (fun N : ℕ => fun z : ℂ => ∑ k ∈ Finset.Icc (-(N : ℤ)) N,
        TripleProduct.term q z k)
      (fun z : ℂ => qPochhammerInf q q * qPochhammerInf z q * qPochhammerInf (q / z) q)
      Filter.atTop {z : ℂ | z ≠ 0} := by
  sorry

end DLMF.QSeries
