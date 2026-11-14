/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bessel.Basic
public import DLMF.Core.Basic
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Analysis.Complex.SqrtDeriv

/-!
# Debye polynomials and uniform scaled-order modified Bessel expansions

The rational polynomials are defined by an actual finite coefficient algorithm,
which is the termwise zero-constant integration in the Debye recurrence. The
argument may range over an unbounded proper closed right subsector while the
positive real order tends to infinity. Source: Olver, *Asymptotics and Special
Functions*, Chapter 10, §7, pp. 374–378; DLMF §§10.41(ii)–(iii).
-/

@[expose] public noncomputable section

open Complex Polynomial DLMF.Core
open scoped Real

namespace DLMF.Bessel.Debye

/-- The rational Debye polynomial `U_n`. Each coefficient `a*t^k` contributes
`(k/2+1/(8(k+1)))*a*t^(k+1)-(k/2+5/(8(k+3)))*a*t^(k+3)`.
This is the polynomial form of the zero-constant integral recurrence.
Olver, Chapter 10, §7, pp. 374–375. -/
def polynomialU : ℕ → Polynomial ℚ
  | 0 => 1
  | n + 1 => (polynomialU n).sum fun k a =>
      monomial (k + 1) (((k : ℚ) / 2 + 1 / (8 * (k + 1))) * a) -
        monomial (k + 3) (((k : ℚ) / 2 + 5 / (8 * (k + 3))) * a)

/-- The initial Debye polynomial. -/
@[simp] theorem polynomialU_zero : polynomialU 0 = 1 := rfl

/-- The finite coefficient recursion defining the Debye polynomials. -/
theorem polynomialU_succ (n : ℕ) :
    polynomialU (n + 1) = (polynomialU n).sum fun k a =>
      monomial (k + 1) (((k : ℚ) / 2 + 1 / (8 * (k + 1))) * a) -
        monomial (k + 3) (((k : ℚ) / 2 + 5 / (8 * (k + 3))) * a) := rfl

/-- The derivative Debye polynomials, with the same normalization `V_0=1`.
Olver, Chapter 10, §7, p. 377. -/
def polynomialV : ℕ → Polynomial ℚ
  | 0 => 1
  | n + 1 => polynomialU (n + 1) +
      C (1 / 2) * X * (X ^ 2 - 1) * polynomialU n +
        X ^ 2 * (X ^ 2 - 1) * (polynomialU n).derivative

/-- The initial derivative Debye polynomial. -/
@[simp] theorem polynomialV_zero : polynomialV 0 = 1 := rfl

/-- The defining derivative-polynomial recursion. -/
theorem polynomialV_succ (n : ℕ) :
    polynomialV (n + 1) = polynomialU (n + 1) +
      C (1 / 2) * X * (X ^ 2 - 1) * polynomialU n +
        X ^ 2 * (X ^ 2 - 1) * (polynomialU n).derivative := rfl

/-- Complex evaluation of the rational Debye polynomial. -/
def coefficientU (n : ℕ) (t : ℂ) : ℂ := (polynomialU n).eval₂ (algebraMap ℚ ℂ) t

/-- The defining complex evaluation of `U_n`. -/
theorem coefficientU_def (n : ℕ) (t : ℂ) :
    coefficientU n t = (polynomialU n).eval₂ (algebraMap ℚ ℂ) t := rfl

/-- Complex evaluation of the derivative Debye polynomial. -/
def coefficientV (n : ℕ) (t : ℂ) : ℂ := (polynomialV n).eval₂ (algebraMap ℚ ℂ) t

/-- The defining complex evaluation of `V_n`. -/
theorem coefficientV_def (n : ℕ) (t : ℂ) :
    coefficientV n t = (polynomialV n).eval₂ (algebraMap ℚ ℂ) t := rfl

/-- The principal Debye phase, continued from positive real arguments.
The expansion theorems use `Re z>0`, avoiding the turning points `+i,-i`.
Olver, Chapter 10, §7, p. 374. -/
def phase (z : ℂ) : ℂ := sqrt (1 + z ^ 2) + log (z / (1 + sqrt (1 + z ^ 2)))

/-- The defining square-root and logarithm expression for the Debye phase. -/
theorem phase_def (z : ℂ) :
    phase z = sqrt (1 + z ^ 2) + log (z / (1 + sqrt (1 + z ^ 2))) := rfl

/-- The exact integral recurrence, with the primitive normalized to vanish at zero.
Olver, Chapter 10, §7, pp. 374–375. -/
theorem coefficientU_succ (n : ℕ) (t : ℂ) :
    coefficientU (n + 1) t = t ^ 2 * (1 - t ^ 2) / 2 * deriv (coefficientU n) t +
      segmentIntegral (fun v => (1 - 5 * v ^ 2) * coefficientU n v) 0 t / 8 := by
  sorry

/-- The first explicit Debye polynomial. Olver, Chapter 10, §7, p. 375. -/
theorem polynomialU_one :
    polynomialU 1 = C (1 / 24) * (3 * X - 5 * X ^ 3) := by
  sorry

/-- The second explicit Debye polynomial. Olver, Chapter 10, §7, p. 375. -/
theorem polynomialU_two :
    polynomialU 2 = C (1 / 1152) * (81 * X ^ 2 - 462 * X ^ 4 + 385 * X ^ 6) := by
  sorry

/-- The Debye polynomial has exact degree `3n`, including `n=0`.
Olver, Chapter 10, §7, p. 375. -/
theorem natDegree_polynomialU (n : ℕ) : (polynomialU n).natDegree = 3 * n := by
  sorry

end DLMF.Bessel.Debye

namespace DLMF.Bessel

/-- The all-orders Debye expansion for the modified first kind is uniform
on the entire unbounded closed right subsector. The derivative, when present,
is with respect to the full Bessel argument. Olver, Chapter 10, §7, pp. 375–378. -/
theorem exists_uniform_besselI_debye_remainder {δ : ℝ}
    (hδ : 0 < δ) (hδπ : δ < Real.pi / 2) (N : ℕ) :
    ∃ C ν₀ : ℝ, 0 < C ∧ 1 ≤ ν₀ ∧ ∀ ν : ℝ, ν₀ ≤ ν → ∀ z : ℂ,
      0 < z.re → |arg z| ≤ Real.pi / 2 - δ →
      ‖(Real.sqrt (2 * Real.pi * ν) : ℂ) * (1 + z ^ 2) ^ (1 / 4 : ℂ) *
          exp (-(ν : ℂ) * Debye.phase z) * besselI (ν : ℂ) ((ν : ℂ) * z) -
        ∑ n ∈ Finset.range N, Debye.coefficientU n ((1 + z ^ 2) ^ (-1 / 2 : ℂ)) /
          (ν : ℂ) ^ n‖ ≤ C / ν ^ N := by
  sorry

/-- The all-orders Debye expansion for the modified second kind is uniform
on the entire unbounded closed right subsector. The derivative, when present,
is with respect to the full Bessel argument. Olver, Chapter 10, §7, pp. 375–378. -/
theorem exists_uniform_besselK_debye_remainder {δ : ℝ}
    (hδ : 0 < δ) (hδπ : δ < Real.pi / 2) (N : ℕ) :
    ∃ C ν₀ : ℝ, 0 < C ∧ 1 ≤ ν₀ ∧ ∀ ν : ℝ, ν₀ ≤ ν → ∀ z : ℂ,
      0 < z.re → |arg z| ≤ Real.pi / 2 - δ →
      ‖(Real.sqrt (2 * ν / Real.pi) : ℂ) * (1 + z ^ 2) ^ (1 / 4 : ℂ) *
          exp ((ν : ℂ) * Debye.phase z) * besselK (ν : ℂ) ((ν : ℂ) * z) -
        ∑ n ∈ Finset.range N, (-1 : ℂ) ^ n * Debye.coefficientU n ((1 + z ^ 2) ^ (-1 / 2 : ℂ)) /
          (ν : ℂ) ^ n‖ ≤ C / ν ^ N := by
  sorry

/-- The all-orders Debye expansion for the modified first-kind derivative is uniform
on the entire unbounded closed right subsector. The derivative, when present,
is with respect to the full Bessel argument. Olver, Chapter 10, §7, pp. 375–378. -/
theorem exists_uniform_deriv_besselI_debye_remainder {δ : ℝ}
    (hδ : 0 < δ) (hδπ : δ < Real.pi / 2) (N : ℕ) :
    ∃ C ν₀ : ℝ, 0 < C ∧ 1 ≤ ν₀ ∧ ∀ ν : ℝ, ν₀ ≤ ν → ∀ z : ℂ,
      0 < z.re → |arg z| ≤ Real.pi / 2 - δ →
      ‖(Real.sqrt (2 * Real.pi * ν) : ℂ) * z * (1 + z ^ 2) ^ (-1 / 4 : ℂ) *
          exp (-(ν : ℂ) * Debye.phase z) * deriv (besselI (ν : ℂ)) ((ν : ℂ) * z) -
        ∑ n ∈ Finset.range N, Debye.coefficientV n ((1 + z ^ 2) ^ (-1 / 2 : ℂ)) /
          (ν : ℂ) ^ n‖ ≤ C / ν ^ N := by
  sorry

/-- The all-orders Debye expansion for the modified second-kind derivative is uniform
on the entire unbounded closed right subsector. The derivative, when present,
is with respect to the full Bessel argument. Olver, Chapter 10, §7, pp. 375–378. -/
theorem exists_uniform_deriv_besselK_debye_remainder {δ : ℝ}
    (hδ : 0 < δ) (hδπ : δ < Real.pi / 2) (N : ℕ) :
    ∃ C ν₀ : ℝ, 0 < C ∧ 1 ≤ ν₀ ∧ ∀ ν : ℝ, ν₀ ≤ ν → ∀ z : ℂ,
      0 < z.re → |arg z| ≤ Real.pi / 2 - δ →
      ‖-(Real.sqrt (2 * ν / Real.pi) : ℂ) * z * (1 + z ^ 2) ^ (-1 / 4 : ℂ) *
          exp ((ν : ℂ) * Debye.phase z) * deriv (besselK (ν : ℂ)) ((ν : ℂ) * z) -
        ∑ n ∈ Finset.range N, (-1 : ℂ) ^ n * Debye.coefficientV n ((1 + z ^ 2) ^ (-1 / 2 : ℂ)) /
          (ν : ℂ) ^ n‖ ≤ C / ν ^ N := by
  sorry

end DLMF.Bessel
