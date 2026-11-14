/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AsymptoticApproximations.Integrals.Laplace

/-!
# The normalized first saddle correction

Olver, *Asymptotics and Special Functions*, Chapter 4, §7.3,
p. 127, synopsis O-4.11. The existing undivided coefficients remain valid
when the amplitude vanishes; normalization requires its nonzero value.
-/

@[expose] public noncomputable section

open Complex

namespace DLMF.AsymptoticApproximations

/-- The first normalized saddle coefficient, from the exact undivided b0 and b2 formulas.
Olver, Chapter 4, §7.3, synopsis O-4.11. -/
theorem saddle_coefficient_normalized (P Q : ℕ → ℂ) (L : ℂ)
    (hP : P 2 ≠ 0) (hQ : Q 0 ≠ 0)
    (hL : exp L = P 2 / 2) :
    laplaceCoeff L (fun k => P (k + 2) / (k + 2).factorial) (fun k => Q k / k.factorial) 1 2 2 /
      (2 * laplaceCoeff L (fun k => P (k + 2) / (k + 2).factorial)
        (fun k => Q k / k.factorial) 1 2 0) =
    Q 2 / (2 * Q 0 * P 2) - Q 1 * P 3 / (2 * Q 0 * P 2 ^ 2) -
      P 4 / (8 * P 2 ^ 2) + 5 * P 3 ^ 2 / (24 * P 2 ^ 3) := by
  rw [saddle_coeff_two hP, saddle_coeff_zero]
  have he : exp (3 * L / 2) = exp (L / 2) * (P 2 / 2) := by
    rw [← hL, ← Complex.exp_add]
    congr 1
    ring
  rw [he]
  field_simp
  ring

end DLMF.AsymptoticApproximations
