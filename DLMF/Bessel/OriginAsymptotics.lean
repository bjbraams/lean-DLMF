/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bessel.Basic.SecondKind
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# Leading and logarithmic Bessel expansions at zero

Temme, *Special Functions* (1996), Chapter 9, (9.5)–(9.9) and (9.26)–(9.29),
pp. 223–227, 232–234, synopses TEM-09-02 and TEM-09-06.
-/

@[expose] public noncomputable section
open Complex Filter Asymptotics
open scoped Topology
namespace DLMF.Bessel

/-- Leading second-kind singularity for positive real order, Temme Chapter 9,
(9.5)–(9.9), synopsis TEM-09-02. -/
theorem tendsto_cpow_mul_besselY {ν : ℝ} (hν : 0 < ν) :
    Tendsto (fun x : ℝ => (x / 2 : ℂ) ^ (ν : ℂ) * besselY ν x)
      (𝓝[>] 0) (𝓝 (-Gamma ν / Real.pi)) := by
  sorry

/-- The order-zero logarithmic remainder, Temme Chapter 9,
(9.5)–(9.9), synopsis TEM-09-02. -/
theorem besselY_zero_sub_log_isBigO :
    (fun x : ℝ => besselY 0 x - (2 / (Real.pi : ℂ)) *
      (log (x / 2 : ℂ) + Real.eulerMascheroniConstant))
      =O[𝓝[>] 0] (fun x : ℝ => x ^ 2 * |Real.log x|) := by
  sorry

/-- The order-zero modified second-kind logarithmic remainder, Temme Chapter 9,
(9.26)–(9.29), synopsis TEM-09-06. -/
theorem besselK_zero_add_log_isBigO :
    (fun x : ℝ => besselK 0 x + log (x / 2 : ℂ) + Real.eulerMascheroniConstant)
      =O[𝓝[>] 0] (fun x : ℝ => x ^ 2 * |Real.log x|) := by
  sorry

end DLMF.Bessel
