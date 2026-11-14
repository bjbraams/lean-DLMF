/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AsymptoticApproximations.ODE.RankOneForcing

/-!
# Uniqueness of normalized homogeneous rank-one formal solutions

Olver, *Asymptotics and Special Functions*, Chapter 7, §§1–2,
pp. 229–232, synopsis O-7.01. The conjugated exponential-power operator
is evaluated by actual finite Laurent coefficient arithmetic. No value is
assigned to a divergent infinite numerical series.
-/

@[expose] public noncomputable section

namespace DLMF.AsymptoticApproximations.RankOne

/-- The canonical recursive coefficients are precisely the unique formal solution with
constant coefficient one of the exponential-power-conjugated differential operator.
Olver, Chapter 7, §§1–2, synopsis O-7.01. -/
theorem rankOneCoeff_formal_operator_eq_and_unique (pc qc : ℕ → ℂ) (lam : ℂ)
    (hroot : lam ^ 2 + pc 0 * lam + qc 0 = 0) (hdistinct : pc 0 + 2 * lam ≠ 0) :
    let P := fun n => pc n + if n = 0 then 2 * lam else 0
    let Q := fun n => qc n + lam * pc n + if n = 0 then lam ^ 2 else 0
    let μ := rankOneExponent pc qc lam
    (∀ n, RankOneForcing.operatorCoefficient P Q μ (rankOneCoeff pc qc lam) n = 0) ∧
      (∀ a : ℕ → ℂ, a 0 = 1 →
        (∀ n, RankOneForcing.operatorCoefficient P Q μ a n = 0) → a = rankOneCoeff pc qc lam) := by
  sorry

end DLMF.AsymptoticApproximations.RankOne
