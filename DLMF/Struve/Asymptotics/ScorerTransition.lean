/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Struve.AngerWeber.IntegralAndSeries
public import DLMF.Airy.Scorer.ShiftedMoments
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The uniform Anger–Scorer cubic transition

Olver, *Asymptotics and Special Functions*, Chapter 9, §§12–13,
pp. 352–360, synopsis O-9.14. The canonical associated Anger function is
used directly. The even centered Scorer moments retain the positive error majorant.
-/

@[expose] public noncomputable section
open Set Complex
namespace DLMF.Struve.ScorerTransition

/-- The original hyperbolic phase. Olver, Chapter 9, §12, pp. 352–354. -/
def phase (a t : ℝ) : ℝ := (Real.cosh a)⁻¹ * Real.sinh t - t

/-- The nonnegative cubic saddle parameter, for a≥0. Olver §12. -/
def zeta (a : ℝ) : ℝ := (3 / 2 * (a - Real.tanh a)) ^ (2 / 3 : ℝ)

/-- The increasing inverse on the two sides of the cubic saddle.
Olver, Chapter 9, §12, pp. 352–354. -/
def inverse (a w : ℝ) : ℝ :=
  if w ≤ Real.sqrt (zeta a) then
    Function.invFunOn (phase a) (Icc 0 a) (w ^ 3 / 3 - zeta a * w)
  else Function.invFunOn (phase a) (Ici a) (w ^ 3 / 3 - zeta a * w)

/-- The coefficients are the actual inverse-Jacobian derivatives. Right
endpoint derivatives cover the cubic coalescence a=0. Olver §12. -/
def coefficient (s : ℕ) (a : ℝ) : ℝ :=
  iteratedDerivWithin s (derivWithin (inverse a) (Ici 0))
    (Ici 0) (Real.sqrt (zeta a)) / s.factorial

/-- The defining original phase. -/
theorem phase_def (a t : ℝ) : phase a t = (Real.cosh a)⁻¹ * Real.sinh t - t := rfl

/-- The defining cubic saddle parameter. -/
theorem zeta_def (a : ℝ) : zeta a = (3 / 2 * (a - Real.tanh a)) ^ (2 / 3 : ℝ) := rfl

/-- The defining branches of the cubic inverse. -/
theorem inverse_def (a w : ℝ) : inverse a w =
    if w ≤ Real.sqrt (zeta a) then
      Function.invFunOn (phase a) (Icc 0 a) (w ^ 3 / 3 - zeta a * w)
    else Function.invFunOn (phase a) (Ici a) (w ^ 3 / 3 - zeta a * w) := rfl

/-- The defining reversion coefficient. -/
theorem coefficient_def (s : ℕ) (a : ℝ) : coefficient s a =
    iteratedDerivWithin s (derivWithin (inverse a) (Ici 0))
      (Ici 0) (Real.sqrt (zeta a)) / s.factorial := rfl

/-- The exact increasing cubic coordinate, through the coalesced case a=0.
Olver, Chapter 9, §12, pp. 352–354. -/
theorem inverse_spec {a : ℝ} (ha : 0 ≤ a) :
    0 ≤ zeta a ∧ StrictMonoOn (inverse a) (Ici 0) ∧ inverse a 0 = 0 ∧
      inverse a (Real.sqrt (zeta a)) = a ∧
      ∀ w ≥ 0, phase a (inverse a w) = w ^ 3 / 3 - zeta a * w := by
  sorry

/-- The inverse Jacobian is given by its convergent local Taylor series.
Olver, Chapter 9, §12, pp. 352–354. -/
theorem hasSum_inverse_jacobian {a : ℝ} (ha : 0 ≤ a) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ w ≥ 0, |w - Real.sqrt (zeta a)| < ε →
      HasSum (fun s : ℕ => coefficient s a * (w - Real.sqrt (zeta a)) ^ s)
        (derivWithin (inverse a) (Ici 0) w) := by
  sorry

/-- Each reversion coefficient is continuous at coalescence.
Olver, Chapter 9, §12, pp. 352–354. -/
theorem continuousOn_coefficient (s : ℕ) : ContinuousOn (coefficient s) (Ici 0) := by
  sorry

/-- The even-N centered Scorer expansion is uniform on the entire nonnegative
a-axis and for every positive nu. Olver, Chapter 9, §§12–13, pp. 352–360. -/
theorem exists_uniform_remainder_le {N : ℕ} (hN : 2 ≤ N) (hNeven : Even N) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : ℝ, 0 ≤ a → ∀ ν : ℝ, 0 < ν →
      ‖angerA (-(ν : ℂ)) ((ν / Real.cosh a : ℝ) : ℂ) -
        ((∑ s ∈ Finset.range N, coefficient s a * ν ^ (-((s : ℝ) + 1) / 3) *
          DLMF.Airy.ShiftedScorerMoment.value s (ν ^ (2 / 3 : ℝ) * zeta a) : ℝ) : ℂ)‖ ≤
        C * (1 + zeta a) ^ (((N : ℝ) + 1) / 4) * ν ^ (-((N : ℝ) + 1) / 3) *
          DLMF.Airy.ShiftedScorerMoment.value N (ν ^ (2 / 3 : ℝ) * zeta a) := by
  sorry

end DLMF.Struve.ScorerTransition
