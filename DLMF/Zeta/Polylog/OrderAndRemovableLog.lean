/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Zeta.Polylog.LogarithmicExpansion
public import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Polylogarithm order analyticity and the combined logarithmic limit

Olver, *Asymptotics and Special Functions*, Chapter 8, §7,
pp. 304–306, synopsis O-8.10. The Gamma pole and the zeta coefficient pole
must be combined before taking a positive-integer order limit.
-/

@[expose] public noncomputable section
open Complex Filter
open scoped Topology
namespace DLMF.Zeta

/-- For every fixed principal-cut argument, the polylogarithm is entire in its
complex order. Olver, Chapter 8, §7, pp. 304–306. -/
theorem differentiable_polylog_order {z : ℂ} (hz : z ∈ slitOne) :
    Differentiable ℂ (fun s : ℂ => polylog s z) := by
  sorry

/-- The complete Gamma-plus-zeta logarithmic expression has the removable value
at every positive integral order. Olver, Chapter 8, §7, pp. 304–306. Neither
singular term is totalized separately before the limit. -/
theorem tendsto_polylog_logarithmic_expression_nat {z : ℂ} (hz : z ∈ slitOne)
    (hz0 : z ≠ 0) (hlog : ‖log z‖ < 2 * Real.pi) {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun s : ℂ => Gamma (1 - s) * (-log z) ^ (s - 1) +
      ∑' n : ℕ, riemannZeta (s - n) * log z ^ n / n.factorial) (𝓝[≠] (m : ℂ))
      (𝓝 (polylog m z)) := by
  sorry

end DLMF.Zeta
