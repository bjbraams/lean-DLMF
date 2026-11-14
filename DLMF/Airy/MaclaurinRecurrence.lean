/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Airy.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Three-step Maclaurin recurrence for the Airy function

Olver, *Asymptotics and Special Functions*, Chapter 2, §8, pp. 53–55,
synopsis O-2.19. Taylor coefficients use the actual derivatives of the canonical function.
-/

@[expose] public noncomputable section

namespace DLMF.Airy

/-- The Airy equation gives the three-step Taylor recurrence, including the vanishing quadratic
coefficient. Olver, Chapter 2, §8, synopsis O-2.19. -/
theorem airyAi_maclaurin_coefficient_recurrence :
    let c : ℕ → ℂ := fun n => iteratedDeriv n airyAi 0 / (n.factorial : ℂ)
    c 2 = 0 ∧ ∀ n : ℕ, (n + 3 : ℂ) * (n + 2) * c (n + 3) = c n := by
  sorry

end DLMF.Airy
