/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Painleve.Backlund
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Tactic.Polynomial.Basic

/-!
# Rational solutions of Painlevé II

The existence part of Beals–Wong Theorem 15.3.1 is constructed by the upward
Bäcklund shift, starting at zero. Polynomial numerator and denominator pairs
keep the rationality assertion explicit, and denominator polynomials are
proved nonzero. The equation is asserted on the full regular set of each
constructed quotient. This does not yet prove the converse or uniqueness.
-/

@[expose] public noncomputable section

open Complex Polynomial Set Filter
open scoped Topology

namespace DLMF.Painleve

/-- A polynomial quotient, with poles excluded in its solution theorems. -/
def rationalFn (p q : ℂ[X]) (x : ℂ) : ℂ := p.eval x / q.eval x

/-- The regular set of a polynomial quotient. -/
def polynomialDomain (q : ℂ[X]) : Set ℂ := {x | q.eval x ≠ 0}

/-- A polynomial quotient is regular on an open set. -/
theorem isOpen_polynomialDomain (q : ℂ[X]) : IsOpen (polynomialDomain q) :=
  isOpen_ne_fun q.continuous continuous_const

/-- A nonzero polynomial leaves a nonempty regular set. -/
theorem polynomialDomain_nonempty {q : ℂ[X]} (hq : q ≠ 0) : (polynomialDomain q).Nonempty := by
  by_contra h
  apply hq
  apply Polynomial.funext
  intro x
  have hx : ¬q.eval x ≠ 0 := fun hx => h ⟨x, hx⟩
  simpa using not_not.mp hx

/-- The explicit derivative of a polynomial quotient on its regular set. -/
theorem hasDerivAt_rationalFn (p q : ℂ[X]) {x : ℂ} (hx : q.eval x ≠ 0) :
    HasDerivAt (rationalFn p q)
      ((p.derivative.eval x * q.eval x - p.eval x * q.derivative.eval x) / q.eval x ^ 2) x :=
  (p.hasDerivAt x).div (q.hasDerivAt x) hx

/-- The polynomial numerator of the upward-shift denominator after clearing `q²`. -/
def rationalStepDenom (p q : ℂ[X]) : ℂ[X] :=
  X * q ^ 2 + C 2 * p ^ 2 - C 2 * p.derivative * q + C 2 * p * q.derivative

/-- Clearing the denominator in the upward Bäcklund transformation. -/
theorem backlundDenom_neg_rationalFn (p q : ℂ[X]) {x : ℂ} (hx : q.eval x ≠ 0) :
    backlundDenom (fun x => -rationalFn p q x) x =
      (rationalStepDenom p q).eval x / q.eval x ^ 2 := by
  rw [backlundDenom, show deriv (fun x => -rationalFn p q x) x = -deriv (rationalFn p q) x from deriv.neg,
    (hasDerivAt_rationalFn p q hx).deriv]
  simp only [rationalFn, rationalStepDenom, eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C]
  field_simp
  ring

/-- A rational solution at a nonnegative integral parameter has a nonzero upward-shift
polynomial, so the next rational function is defined on a nonempty regular set. -/
theorem rationalStepDenom_ne_zero {p q : ℂ[X]} (hq : q ≠ 0) (n : ℕ)
    (h : IsPIIOn (n : ℂ) (rationalFn p q) (polynomialDomain q)) :
    rationalStepDenom p q ≠ 0 := by
  intro hr
  have hc : 1 - 2 * (-(n : ℂ)) ≠ 0 := ne_zero_of_re_pos (by simp; positivity)
  obtain ⟨x, hx, hD⟩ := h.neg.exists_backlundDenom_ne_zero (isOpen_polynomialDomain q)
    (polynomialDomain_nonempty hq) hc
  rw [backlundDenom_neg_rationalFn p q hx, hr, eval_zero, zero_div] at hD
  exact hD rfl

/-- An explicit polynomial pair for one upward Bäcklund shift. -/
theorem backlundUp_rationalFn (p q : ℂ[X]) (c : ℂ) {x : ℂ}
    (hq : q.eval x ≠ 0) (hr : (rationalStepDenom p q).eval x ≠ 0) :
    backlundUp c (rationalFn p q) x =
      rationalFn (-p * rationalStepDenom p q + C (1 + 2 * c) * q ^ 3)
        (q * rationalStepDenom p q) x := by
  rw [backlundUp_eq, (hasDerivAt_rationalFn p q hq).deriv]
  have hR : (rationalStepDenom p q).eval x =
      x * q.eval x ^ 2 + 2 * p.eval x ^ 2 - 2 * p.derivative.eval x * q.eval x +
        2 * p.eval x * q.derivative.eval x := by
    simp [rationalStepDenom]
  have hD : x + 2 * rationalFn p q x ^ 2 - 2 *
      ((p.derivative.eval x * q.eval x - p.eval x * q.derivative.eval x) / q.eval x ^ 2) =
      (rationalStepDenom p q).eval x / q.eval x ^ 2 := by
    dsimp only [rationalFn]
    rw [hR]
    field_simp
    ring
  rw [hD]
  simp only [rationalFn, eval_add, eval_mul, eval_neg, eval_C, eval_pow]
  field_simp

/-- The canonical rational Painlevé II polynomial pair constructed from the zero solution
by successive upward Bäcklund transformations. Common factors are retained. -/
def rationalPIIPair : ℕ → ℂ[X] × ℂ[X]
  | 0 => (0, 1)
  | n + 1 =>
      let p := (rationalPIIPair n).1
      let q := (rationalPIIPair n).2
      let r := rationalStepDenom p q
      (-p * r + C (1 + 2 * (n : ℂ)) * q ^ 3, q * r)

/-- Every canonical rational polynomial pair has a nonzero denominator and solves PII
on its full regular set. -/
theorem rationalPIIPair_spec (n : ℕ) :
    (rationalPIIPair n).2 ≠ 0 ∧
      IsPIIOn (n : ℂ) (rationalFn (rationalPIIPair n).1 (rationalPIIPair n).2)
        (polynomialDomain (rationalPIIPair n).2) := by
  induction n with
  | zero =>
    refine ⟨one_ne_zero, ?_⟩
    change IsPIIOn _ (rationalFn 0 1) (polynomialDomain 1)
    have he : rationalFn (0 : ℂ[X]) 1 = fun _ => 0 := by funext x; simp [rationalFn]
    simpa only [he, Nat.cast_zero] using
      isPIIOn_zero (polynomialDomain (1 : ℂ[X]))
  | succ n ih =>
    obtain ⟨hq, hsol⟩ := ih
    let p := (rationalPIIPair n).1
    let q := (rationalPIIPair n).2
    let r := rationalStepDenom p q
    have hr : r ≠ 0 := rationalStepDenom_ne_zero hq n hsol
    change q * r ≠ 0 ∧ IsPIIOn _ (rationalFn (-p * r + C (1 + 2 * (n : ℂ)) * q ^ 3) (q * r)) (polynomialDomain (q * r))
    refine ⟨mul_ne_zero hq hr, ?_⟩
    have hsub : polynomialDomain (q * r) ⊆ polynomialDomain q := by
      intro x hx
      exact (mul_ne_zero_iff.mp (by simpa only [polynomialDomain, mem_ofPred_eq, eval_mul] using hx)).1
    have hD : ∀ x ∈ polynomialDomain (q * r), backlundDenom (fun x => -rationalFn p q x) x ≠ 0 := by
      intro x hx
      have hqr : q.eval x ≠ 0 ∧ r.eval x ≠ 0 :=
        mul_ne_zero_iff.mp (by simpa only [polynomialDomain, mem_ofPred_eq, eval_mul] using hx)
      rw [backlundDenom_neg_rationalFn p q hqr.1]
      exact div_ne_zero hqr.2 (pow_ne_zero _ hqr.1)
    have hnew := (hsol.mono hsub).shiftUp (isOpen_polynomialDomain (q * r)) hD
    have heq : EqOn (backlundUp (n : ℂ) (rationalFn p q))
        (rationalFn (-p * r + C (1 + 2 * (n : ℂ)) * q ^ 3) (q * r)) (polynomialDomain (q * r)) := by
      intro x hx
      have hqr : q.eval x ≠ 0 ∧ r.eval x ≠ 0 :=
        mul_ne_zero_iff.mp (by simpa only [polynomialDomain, mem_ofPred_eq, eval_mul] using hx)
      exact backlundUp_rationalFn p q n hqr.1 hqr.2
    simpa only [Nat.cast_add, Nat.cast_one] using hnew.congr (isOpen_polynomialDomain _) heq

/-- Every nonnegative integral parameter has a rational solution with nonzero denominator. -/
theorem exists_rational_solution_nat (n : ℕ) :
    ∃ p q : ℂ[X], q ≠ 0 ∧ IsPIIOn (n : ℂ) (rationalFn p q) (polynomialDomain q) :=
  ⟨(rationalPIIPair n).1, (rationalPIIPair n).2, rationalPIIPair_spec n⟩

/-- The first nonzero rational solution is represented by `1/X`, as on page 407. -/
theorem rationalPIIPair_one : rationalPIIPair 1 = (1, X) := by
  simp [rationalPIIPair, rationalStepDenom]

/-- The second rational solution is `(2X³-4)/(X(X³+4))`, equivalent to the book's
`-1/x + 3x²/(x³+4)`. -/
theorem rationalPIIPair_two : rationalPIIPair 2 = (C 2 * X ^ 3 - C 4, X * (X ^ 3 + C 4)) := by
  rw [rationalPIIPair, rationalPIIPair_one]
  simp only [rationalStepDenom, derivative_one, derivative_X, one_pow, mul_one, mul_zero,
    sub_zero, zero_mul, Nat.cast_one]
  apply Prod.ext <;> norm_num <;> simp only [C_ofNat] <;> ring

/-- Every integral parameter has a rational solution, the existence direction of
Beals–Wong Theorem 15.3.1. The converse and uniqueness are separate assertions. -/
theorem exists_rational_solution_int (n : ℤ) :
    ∃ p q : ℂ[X], q ≠ 0 ∧ IsPIIOn (n : ℂ) (rationalFn p q) (polynomialDomain q) := by
  cases n with
  | ofNat n => simpa using exists_rational_solution_nat n
  | negSucc n =>
    obtain ⟨p, q, hq, hsol⟩ := exists_rational_solution_nat (n + 1)
    refine ⟨-p, q, hq, ?_⟩
    convert hsol.neg using 1
    · push_cast; ring
    · funext x
      simp only [rationalFn, eval_neg]
      ring

end DLMF.Painleve
