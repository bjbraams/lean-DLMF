/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.ContinuousBetaIntegrals
public import DLMF.Gamma.Basic
public import Mathlib.Topology.Defs.Filter

/-!
# The Wilson limit of the Askey–Wilson integral

Andrews, Askey and Roy, *Special Functions*, §10.8, pp. 513–520
(synopsis AAR-10.8.1–10.8.2), and §3.6. The normalization is explicit and the
limit is the actual Wilson half-line Gamma integral, rather than only a formal
replacement of shifted factorials by Gamma factors.
-/

@[expose] public section

open Complex Filter MeasureTheory DLMF.QSeries
open scoped Topology

namespace DLMF.QHypergeometric

/-- The normalized Askey–Wilson angle integral tends to Wilson's Gamma integral.
Andrews–Askey–Roy, *Special Functions*, §10.8, pp. 513–520
(synopsis AAR-10.8.1–10.8.2). The four positive shape parameters are fixed and
`q` approaches one from within the real open unit interval. -/
theorem tendsto_askeyWilson_integral_wilson (a : Fin 4 → ℝ) (ha : ∀ j, 0 < a j) :
    Tendsto
      (fun q : ℝ => qPochhammerInf (q : ℂ) q ^ 6 *
        (1 - q : ℂ) ^ ((5 - 2 * ∑ j, a j : ℝ) : ℂ) *
        ∫ θ : ℝ in Set.Ioo 0 Real.pi, pairedShiftedFactorial 1 q (2 * θ) /
          (∏ j : Fin 4, pairedShiftedFactorial ((q ^ a j : ℝ) : ℂ) q θ))
      (𝓝[Set.Ioo 0 1] (1 : ℝ))
      (𝓝 (∫ x : ℝ in Set.Ioi 0,
        (∏ j : Fin 4, (Gamma (a j + I * x) * Gamma (a j - I * x))) /
          (Gamma (2 * I * x) * Gamma (-2 * I * x)))) := by
  sorry

end DLMF.QHypergeometric
