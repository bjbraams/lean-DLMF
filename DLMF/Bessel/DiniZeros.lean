/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bessel.Zeros
public import DLMF.Bessel.Basic.RegularizedSeries
public import DLMF.Bessel.Basic.SecondKind

/-!
# Reality, simplicity and orthogonality of Dini zeros

Temme, *Special Functions* (1996), Theorem 9.2 and Exercise 9.5(3),
pp. 241–242, 250, synopses TEM-09-11 and TEM-09-20. Removing the elementary
power gives an entire even function whose nonzero zeros can be studied
without a branch convention at the origin.
-/

@[expose] public noncomputable section
open Complex MeasureTheory
open scoped Real Topology Nat
namespace DLMF.Bessel

/-- The normalized Dini function `(z/2)^(-ν)(A J_ν(z)+z J_ν'(z))`,
Temme Exercise 9.5(3), synopsis TEM-09-20. The explicit series extends to zero. -/
def diniNormalized (ν A : ℝ) (z : ℂ) : ℂ :=
  (A + ν : ℂ) * regularizedHGFun ∅ {(ν : ℂ) + 1} (-((z / 2) ^ 2)) -
    z ^ 2 / 2 * regularizedHGFun ∅ {(ν : ℂ) + 2} (-((z / 2) ^ 2))

/-- The defining even-series expression for Dini zeros, Temme Exercise 9.5(3). -/
theorem diniNormalized_def (ν A : ℝ) (z : ℂ) : diniNormalized ν A z =
    (A + ν : ℂ) * regularizedHGFun ∅ {(ν : ℂ) + 1} (-((z / 2) ^ 2)) -
      z ^ 2 / 2 * regularizedHGFun ∅ {(ν : ℂ) + 2} (-((z / 2) ^ 2)) := rfl

/-- The Dini combination away from the origin, Temme Exercise 9.5(3), TEM-09-20. -/
theorem cpow_mul_diniNormalized {ν A : ℝ} {z : ℂ} (hz : z ∈ slitPlane) :
    (z / 2) ^ (ν : ℂ) * diniNormalized ν A z =
      A * besselJ ν z + z * deriv (besselJ ν) z := by
  sorry

/-- Nonzero zeros of the entire normalized `J` series are real,
Temme Theorem 9.2, pp. 241–242, synopsis TEM-09-11. -/
theorem im_eq_zero_of_normalized_besselJ_eq_zero {ν : ℝ} (hν : -1 < ν)
    {z : ℂ} (hz : z ≠ 0)
    (hJ : regularizedHGFun ∅ {(ν : ℂ) + 1} (-((z / 2) ^ 2)) = 0) : z.im = 0 := by
  sorry

/-- Reality of nonzero `J_ν` zeros on every power branch,
Temme Theorem 9.2, synopsis TEM-09-11. -/
theorem im_eq_zero_of_besselJ_eq_zero {ν : ℝ} (hν : -1 < ν)
    {z : ℂ} (hz : z ≠ 0) (hJ : besselJ ν z = 0) : z.im = 0 := by
  sorry

/-- Nonzero normalized Dini zeros are real under the sharp sign condition,
Temme Exercise 9.5(3), synopsis TEM-09-20. -/
theorem im_eq_zero_of_diniNormalized_eq_zero {ν A : ℝ} (hν : -1 < ν)
    (hA : 0 ≤ A + ν) {z : ℂ} (hz : z ≠ 0) (hD : diniNormalized ν A z = 0) : z.im = 0 := by
  sorry

/-- Nonzero normalized Dini zeros are simple,
Temme Exercise 9.5(3), synopsis TEM-09-20. -/
theorem deriv_diniNormalized_ne_zero {ν A : ℝ} (hν : -1 < ν)
    (hA : 0 ≤ A + ν) {z : ℂ} (hz : z ≠ 0) (hD : diniNormalized ν A z = 0) :
    deriv (diniNormalized ν A) z ≠ 0 := by
  sorry

/-- Between consecutive positive Dini zeros lies exactly one `J` zero,
Temme Exercise 9.5(3), synopsis TEM-09-20. -/
theorem existsUnique_besselJ_zero_between_diniZeros {ν A a b : ℝ}
    (hν : -1 < ν) (hA : 0 ≤ A + ν) (ha : 0 < a) (hab : a < b)
    (hDa : diniNormalized ν A a = 0) (hDb : diniNormalized ν A b = 0)
    (hnext : ∀ x ∈ Set.Ioo a b, diniNormalized ν A x ≠ 0) :
    ∃! x : ℝ, x ∈ Set.Ioo a b ∧ besselJ ν x = 0 := by
  sorry

/-- Between consecutive positive `J` zeros lies exactly one Dini zero,
Temme Exercise 9.5(3), synopsis TEM-09-20. -/
theorem existsUnique_diniZero_between_besselJ_zeros {ν A a b : ℝ}
    (hν : -1 < ν) (hA : 0 ≤ A + ν) (ha : 0 < a) (hab : a < b)
    (hJa : besselJ ν a = 0) (hJb : besselJ ν b = 0)
    (hnext : ∀ x ∈ Set.Ioo a b, besselJ ν x ≠ 0) :
    ∃! x : ℝ, x ∈ Set.Ioo a b ∧ diniNormalized ν A x = 0 := by
  sorry

/-- Robin modes belonging to different Dini zeros are orthogonal,
Temme Exercise 9.5(3), synopsis TEM-09-20. -/
theorem integral_besselJ_mul_eq_zero_of_diniZeros {ν A a b : ℝ}
    (hν : -1 < ν) (hA : 0 ≤ A + ν) (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b)
    (hDa : diniNormalized ν A a = 0) (hDb : diniNormalized ν A b = 0) :
    (∫ t : ℝ in (0 : ℝ)..1, (t : ℂ) * besselJ ν (a * t) * besselJ ν (b * t)) = 0 := by
  sorry

/-- The positive squared norm of a Dini mode,
Temme Exercise 9.5(3), synopsis TEM-09-20. -/
theorem integral_norm_besselJ_sq_of_diniZero {ν A a : ℝ}
    (hν : -1 < ν) (hA : 0 ≤ A + ν) (ha : 0 < a) (hDa : diniNormalized ν A a = 0) :
    (∫ t : ℝ in (0 : ℝ)..1, t * ‖besselJ ν (a * t)‖ ^ 2) =
      (1 + (A ^ 2 - ν ^ 2) / a ^ 2) * ‖besselJ ν a‖ ^ 2 / 2 ∧
      0 < ∫ t : ℝ in (0 : ℝ)..1, t * ‖besselJ ν (a * t)‖ ^ 2 := by
  sorry

end DLMF.Bessel
