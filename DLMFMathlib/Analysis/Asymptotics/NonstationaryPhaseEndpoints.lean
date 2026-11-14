/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Asymptotics.Defs

/-!
# Nonstationary nonlinear phase with piecewise smooth data

Olver, *Asymptotics and Special Functions*, Chapter 3, §11.3,
pp. 97–98, synopsis O-3.10. The finite partition retains the source's
piecewise differentiability rather than demanding global second derivatives.
-/

@[expose] public noncomputable section

open Filter Set MeasureTheory Complex Asymptotics
open scoped Topology

namespace Asymptotics

/-- The leading endpoint expansion for a nonstationary nonlinear phase.
Olver, Chapter 3, §11.3, synopsis O-3.10. -/
theorem isLittleO_nonstationaryPhase_sub_endpoint_terms {M : ℕ} (hM : 0 < M)
    (cuts : Fin (M + 1) → ℝ) (hcuts : StrictMono cuts)
    {p : ℝ → ℝ} {q : ℝ → ℂ}
    (hp : ContDiffOn ℝ 1 p (Icc (cuts 0) (cuts (Fin.last M))))
    (hq : ContinuousOn q (Icc (cuts 0) (cuts (Fin.last M))))
    (hpp : ∀ j : Fin M, ContDiffOn ℝ 2 p (Icc (cuts j.castSucc) (cuts j.succ)))
    (hqp : ∀ j : Fin M, ContDiffOn ℝ 1 q (Icc (cuts j.castSucc) (cuts j.succ)))
    (hregular : ∀ t ∈ Icc (cuts 0) (cuts (Fin.last M)), deriv p t ≠ 0) :
    (fun x : ℝ => (∫ t in cuts 0..cuts (Fin.last M), exp (I * x * p t) * q t) -
      (exp (I * x * p (cuts (Fin.last M))) * q (cuts (Fin.last M)) /
          ((deriv p (cuts (Fin.last M)) : ℝ) : ℂ) -
        exp (I * x * p (cuts 0)) * q (cuts 0) / ((deriv p (cuts 0) : ℝ) : ℂ)) / (I * x))
      =o[atTop] (fun x : ℝ => x⁻¹) := by
  sorry

end Asymptotics
