/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Airy.Basic.Scorer
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Shifted Scorer moments

Olver, *Asymptotics and Special Functions*, Chapter 9, §§11–13,
pp. 351–360, synopses O-9.13–O-9.14. The even moments give positive error
majorants, and the first two moments bridge the canonical Scorer Hi function.
-/

@[expose] public noncomputable section
open MeasureTheory Set Complex
namespace DLMF.Airy.ShiftedScorerMoment

/-- The centered cubic moment Qi_s(y), for nonnegative real y.
Olver, Chapter 9, §§12–13, pp. 352–360. -/
def value (s : ℕ) (y : ℝ) : ℝ :=
  Real.pi⁻¹ * ∫ v in Ioi (0 : ℝ),
    Real.exp (-v ^ 3 / 3 + y * v) * (v - Real.sqrt y) ^ s

/-- The defining convergent real moment integral. -/
theorem value_def (s : ℕ) (y : ℝ) : value s y = Real.pi⁻¹ * ∫ v in Ioi (0 : ℝ),
    Real.exp (-v ^ 3 / 3 + y * v) * (v - Real.sqrt y) ^ s := rfl

/-- Every centered moment is absolutely convergent. Olver, Chapter 9, §12. -/
theorem integrableOn_value (s : ℕ) (y : ℝ) :
    IntegrableOn (fun v : ℝ =>
      Real.exp (-v ^ 3 / 3 + y * v) * (v - Real.sqrt y) ^ s) (Ioi 0) := by
  sorry

/-- The zeroth centered moment is the canonical Scorer Hi function.
Olver, Chapter 9, §12, pp. 352–354. -/
theorem value_zero (y : ℝ) : (value 0 y : ℂ) = scorerHi y := by
  sorry

/-- The first centered moment is Hi' minus its square-root multiple.
Olver, Chapter 9, §12, pp. 352–354. -/
theorem value_one (y : ℝ) : (value 1 y : ℂ) =
    scorerHiDeriv y - (Real.sqrt y : ℂ) * scorerHi y := by
  sorry

/-- Integration by parts gives every higher centered moment, including the
inhomogeneous endpoint term at s=0. Olver, Chapter 9, §12, pp. 352–354. -/
theorem value_add_two (s : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    value (s + 2) y + 2 * Real.sqrt y * value (s + 1) y =
      (s : ℝ) * value (s - 1) y + (-Real.sqrt y) ^ s / Real.pi := by
  sorry

/-- Every even centered Scorer moment is strictly positive.
Olver, Chapter 9, §§12–13, pp. 352–360. -/
theorem value_even_pos (s : ℕ) (y : ℝ) : 0 < value (2 * s) y := by
  sorry

/-- The canonical cubic endpoint contour integral is a scaled Scorer Hi.
Olver, Chapter 9, §11, pp. 351–352. Complex arguments are allowed because
the cubic decay dominates the linear complex perturbation. -/
theorem integral_exp_cubic_eq_scorerHi {u : ℝ} (hu : 0 < u) (ζ : ℂ) :
    (∫ w in Ioi (0 : ℝ), exp (-(u : ℂ) * ((w : ℂ) ^ 3 / 3 - ζ * w))) =
      ((Real.pi * u ^ (-1 / 3 : ℝ) : ℝ) : ℂ) *
        scorerHi ((u ^ (2 / 3 : ℝ) : ℝ) * ζ) := by
  sorry

end DLMF.Airy.ShiftedScorerMoment
