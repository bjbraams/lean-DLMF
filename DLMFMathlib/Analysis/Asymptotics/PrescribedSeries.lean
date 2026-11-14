/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Asymptotics.AsymptoticExpansion
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Topology.Algebra.InfiniteSum.UniformOn

/-!
# Prescribed asymptotic sums on arbitrary regions and logarithmic sectors

Olver, *Asymptotics and Special Functions*, Chapter 1, §9, pp. 22–24,
synopsis O-1.15. The arbitrary-region construction need not be continuous.
The analytic construction lives in the logarithmic coordinate and keeps its sheet.
-/

@[expose] public noncomputable section

open Filter Set Asymptotics
open scoped Topology

namespace Asymptotics

/-- Every coefficient sequence has an asymptotic sum on an arbitrary unbounded region.
Olver, Chapter 1, §9, synopsis O-1.15. No continuity is asserted. -/
theorem exists_hasAsymptoticExpansion_inv_pow_region (a : ℕ → ℂ) (S : Set ℂ) :
    ∃ f : ℂ → ℂ, HasAsymptoticExpansion (comap norm atTop ⊓ 𝓟 S)
      (fun n (z : ℂ) => z⁻¹ ^ n) a f := by
  sorry

/-- The analytic cutoff construction converges normally on any bounded logarithmic sector and
has the prescribed expansion, even when the sector covers more than one full turn.
Olver, Chapter 1, §9, synopsis O-1.15. Zero coefficients are omitted. -/
theorem exists_analytic_cutoff_sum_log_sector (a : ℕ → ℂ) {α β R b p : ℝ}
    (hαβ : α < β) (hR : 0 < R) (hb : 0 < b) (hbR : b < R)
    (hp : 0 < p) (hpangle : p * (β - α) < Real.pi) :
    let term : ℕ → ℂ → ℂ := fun n w => if a n = 0 then 0 else
      a n * Complex.exp (-(n : ℂ) * w) *
        (1 - Complex.exp (-Complex.exp (p * (w - Complex.I * ((α + β) / 2))) *
          (b : ℂ) ^ n / ‖a n‖))
    SummableLocallyUniformlyOn term {w | Real.log R < w.re ∧ w.im ∈ Icc α β} ∧
      ∃ f : ℂ → ℂ,
        AnalyticOnNhd ℂ f {w | Real.log R < w.re ∧ w.im ∈ Icc α β} ∧
        (∀ w, Real.log R < w.re → w.im ∈ Icc α β → HasSum (fun n => term n w) (f w)) ∧
        HasAsymptoticExpansion (comap Complex.re atTop ⊓ 𝓟 {w | w.im ∈ Icc α β})
          (fun n w => Complex.exp (-(n : ℂ) * w)) a f := by
  sorry

end Asymptotics
