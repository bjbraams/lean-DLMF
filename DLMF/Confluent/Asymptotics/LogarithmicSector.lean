/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.Basic.TricomiLogarithmic
public import DLMF.Confluent.Asymptotics.LargeArgument

/-!
# Complete Kummer expansions in sectors

Temme, *Special Functions* (1996), Chapter 7, equations (7.9) and (7.13), pages 174–177.
The logarithmic variable retains every sheet in `|arg z|<3π/2`, and integer second
parameters are continued through the whole connection formula.
-/

@[expose] public noncomputable section

open Asymptotics Complex Filter DLMF.Core
open scoped Real Topology

namespace DLMF.Confluent

/-- The exponentially dominant regularized Kummer expansion on the full closed
right-half-plane sectors, without extra real-part restrictions on the fixed parameters.
At nonpositive integral first parameters the exponential coefficient family may vanish;
this still states an asymptotic expansion, not equivalence to a zero leading function.
Temme (7.9), synopsis TEM-07-02. -/
theorem hasAsymptoticExpansion_regularizedConfluent_sector (a b : ℂ)
    {δ : ℝ} (hδ : 0 < δ) :
    HasAsymptoticExpansion (sectorAtTop δ)
      (fun (n : ℕ) (z : ℂ) => exp z * z ^ (a - b - n))
      (kummerCoeff a b) (fun z : ℂ => regularizedHGFun {a} {b} z) := by
  sorry

/-- The whole noninteger-parameter connection formula converges at every second parameter.
Temme (7.14)–(7.15), synopsis TEM-07-03 and TEM-07-04. -/
theorem tendsto_kummerUContinuedOnLog (a b w : ℂ) :
    Tendsto (fun c : ℂ => kummerUConnectionOnLog a c w) (𝓝[integerComplement] b)
      (𝓝 (kummerUContinuedOnLog a b w)) := by
  sorry

/-- The logarithmic continuation restricts to the principal Tricomi function.
Temme (7.12)–(7.15), synopsis TEM-07-03 and TEM-07-04. -/
theorem kummerUContinuedOnLog_eq_principal (a b : ℂ) {w : ℂ}
    (hw : |w.im| < π) :
    kummerUContinuedOnLog a b w = kummerU a b (exp w) := by
  have hleft : -Real.pi < w.im := (abs_lt.mp hw).1
  have hright : w.im ≤ Real.pi := (abs_lt.mp hw).2.le
  by_cases hb : ∀ k : ℤ, b ≠ k
  · rw [kummerUContinuedOnLog_of_not_int _ _ _ hb,
      kummerUConnectionOnLog_eq_connection _ _ hleft hright,
      kummerU_eq_connection a b _ hb]
  · rw [kummerUContinuedOnLog_def, ite_eq_right hb]
    have := integerComplement_nhdsWithin_neBot b
    have ht := tendsto_kummerUConnection a b (exp_ne_zero w)
    exact (ht.congr' (Filter.Eventually.of_forall fun c =>
      (kummerUConnectionOnLog_eq_connection a c hleft hright).symm)).limUnder_eq

/-- The continued function is analytic in the logarithmic argument and both parameters.
Temme (7.12)–(7.15), synopsis TEM-07-03 and TEM-07-04. -/
theorem analyticAt_kummerUContinuedOnLog (a b w : ℂ) :
    AnalyticAt ℂ (fun p : ℂ × ℂ × ℂ => kummerUContinuedOnLog p.1 p.2.1 p.2.2)
      (a, b, w) := by
  sorry

/-- Tricomi's complete expansion on every closed subsector of the full lifted sector.
All fixed complex first and second parameters, including integer second parameters, are
included. Temme (7.13), pages 175–177, synopsis TEM-07-04. -/
theorem hasAsymptoticExpansion_kummerUContinuedOnLog (a b : ℂ)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 3 * π / 2) :
    HasAsymptoticExpansion (logSector (3 * π / 2 - δ))
      (fun (n : ℕ) (w : ℂ) => exp (-((n : ℂ) + a) * w))
      (tricomiCoeff a b) (kummerUContinuedOnLog a b) := by
  sorry

end DLMF.Confluent
