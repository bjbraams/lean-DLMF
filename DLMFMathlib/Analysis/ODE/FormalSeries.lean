/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Coefficient equations for ordinary and Frobenius solutions

Andrews, Askey and Roy, *Special Functions*, Appendix F, equations (F.1.4) and
(F.2.3). The formal identities are independent of analytic convergence. The
convergent majorant estimates are in `FrobeniusMajorants`.
-/

@[expose] public section

namespace PowerSeries

/-- Taylor coefficients of a second-order ordinary differential equation obey the
convolution recurrence. Andrews–Askey–Roy, *Special Functions*, Appendix F,
equation (F.1.4) (synopsis AAR-F.1–F.3). -/
theorem coeff_ordinary_second_order {K : Type*} [Field K] [CharZero K]
    (B C Y : PowerSeries K)
    (hY : derivative (derivative Y) = B * derivative Y + C * Y) (n : ℕ) :
    (n + 2 : K) * (n + 1) * coeff (n + 2) Y =
      ∑ j ∈ Finset.range (n + 1),
        (((n - j + 1 : ℕ) : K) * coeff j B * coeff (n - j + 1) Y +
          coeff j C * coeff (n - j) Y) := by
  sorry

/-- The constant coefficient of the Frobenius-transformed equation forces the indicial
polynomial to vanish. Andrews–Askey–Roy, *Special Functions*, Appendix F,
§F.2 (synopsis AAR-F.1–F.3). -/
theorem indicial_eq_zero_of_formal_frobenius {K : Type*} [Field K] [CharZero K]
    (P Q Y : PowerSeries K) (r : K) (hY₀ : coeff 0 Y ≠ 0)
    (hY : X ^ 2 * derivative (derivative Y) +
      X * (C (2 * r) + P) * derivative Y +
        (C (r * (r - 1)) + C r * P + Q) * Y = 0) :
    r * (r - 1) + coeff 0 P * r + coeff 0 Q = 0 := by
  sorry

/-- Higher Frobenius coefficients satisfy the exact shifted-indicial recurrence.
Andrews–Askey–Roy, *Special Functions*, Appendix F, equation (F.2.3)
(synopsis AAR-F.1–F.3). No nonresonance hypothesis is needed for this identity. -/
theorem coeff_formal_frobenius {K : Type*} [Field K] [CharZero K]
    (P Q Y : PowerSeries K) (r : K)
    (hY : X ^ 2 * derivative (derivative Y) +
      X * (C (2 * r) + P) * derivative Y +
        (C (r * (r - 1)) + C r * P + Q) * Y = 0)
    {n : ℕ} (hn : 1 ≤ n) :
    ((r + n) * (r + n - 1) + coeff 0 P * (r + n) + coeff 0 Q) * coeff n Y =
      -(∑ j ∈ Finset.Icc 1 n,
        (coeff j P * (r + n - j) + coeff j Q) * coeff (n - j) Y) := by
  sorry

end PowerSeries
