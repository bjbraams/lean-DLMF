/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.Basic.WhittakerLogarithmic
public import DLMF.Confluent.Asymptotics.LogarithmicSector

/-!
# Whittaker W on full logarithmic sectors

Olver, *Asymptotics and Special Functions*, Chapter 7, §10, pp. 260–262.
The all-parameter lift restricts to the principal function and has its complete
inverse-power expansion for `abs(Im w) <= 3*pi/2-delta`, as `Re w` tends to
infinity. The integer second-parameter cases use the whole Tricomi limit.
-/

@[expose] public noncomputable section

open Complex Filter Asymptotics DLMF.Core
open scoped Real Topology

namespace DLMF.Confluent

/-- The whole-parameter logarithmic Whittaker function restricts to its canonical
principal branch. Olver, Chapter 7, §10, pp. 260–262. -/
theorem whittakerWContinuedOnLog_eq_principal (κ μ : ℂ) {w : ℂ}
    (hw : |w.im| < Real.pi) :
    whittakerWContinuedOnLog κ μ w = whittakerW κ μ (exp w) := by
  rw [whittakerWContinuedOnLog_def, kummerUContinuedOnLog_eq_principal _ _ hw,
    whittakerW, cpow_def_of_ne_zero (exp_ne_zero w),
    log_exp (abs_lt.mp hw).1 (abs_lt.mp hw).2.le]
  congr 2 <;> ring_nf

/-- The continued Whittaker function is jointly analytic in both parameters and
its logarithmic argument. Olver, Chapter 7, §10, pp. 260–262. -/
theorem analyticAt_whittakerWContinuedOnLog (κ μ w : ℂ) :
    AnalyticAt ℂ (fun p : ℂ × ℂ × ℂ => whittakerWContinuedOnLog p.1 p.2.1 p.2.2)
      (κ, μ, w) := by
  sorry

/-- The complete lifted-sector expansion of Whittaker W, including half-integral
orders and all exceptional Tricomi second parameters. The coefficient is exactly
`(-1)^n*(mu-kappa+1/2)_n*(1/2-mu-kappa)_n/n!`.
Olver, Chapter 7, §10, pp. 260–262. -/
theorem hasAsymptoticExpansion_whittakerWContinuedOnLog (κ μ : ℂ)
    {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < 3 * Real.pi / 2) :
    HasAsymptoticExpansion (logSector (3 * Real.pi / 2 - δ))
      (fun (n : ℕ) (w : ℂ) => exp (-exp w / 2) * exp ((κ - n) * w))
      (tricomiCoeff (μ - κ + 1 / 2) (1 + 2 * μ)) (whittakerWContinuedOnLog κ μ) := by
  sorry

end DLMF.Confluent
