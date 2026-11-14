/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Gosper's polynomial antidifference criterion

Andrews, Askey and Roy, *Special Functions*, §3.10, pp. 163–166.
A rational certificate is represented by numerator and denominator polynomials.
This keeps both shifted denominators and every cancellation explicit.
-/

@[expose] public section

namespace Polynomial

variable {K : Type*} [Field K] [CharZero K]

/-- Gosper's normalized rational antidifference exists precisely when the polynomial
certificate equation is solvable. Andrews–Askey–Roy, *Special Functions*, §3.10,
pp. 163–166 (synopsis AAR-3.10–3.12). The dispersion condition is imposed for
all nonnegative integer shifts, and the rational identity is cleared of denominators. -/
theorem exists_gosper_rational_iff_polynomial (p q r : K[X])
    (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0)
    (hcoprime : ∀ j : ℕ, IsCoprime q (r.comp (X + C (j : K)))) :
    (∃ u v : K[X], v ≠ 0 ∧
      p * q * u * v.comp (X - 1) -
          p.comp (X - 1) * r * u.comp (X - 1) * v =
        p * q * v * v.comp (X - 1)) ↔
      ∃ f : K[X], p = q.comp (X + 1) * f - r * f.comp (X - 1) := by
  sorry

end Polynomial
