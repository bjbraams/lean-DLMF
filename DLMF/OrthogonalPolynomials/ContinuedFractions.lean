/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Algebra.ContinuedFractions.ContinuantsRecurrence
public import DLMF.OrthogonalPolynomials.Differential
/-!
# Classical continued fractions (DLMF §18.13)

Statements from NIST DLMF Chapter 18, each tagged with its equation number by `@[dlmf]`.
Jacobi and Gegenbauer statements retain regularity hypotheses because the project's
hypergeometric definitions do not implement continuation in singular parameters.
-/

@[expose] public section

open Complex Polynomial MeasureTheory Filter
open scoped Real Nat Topology
open DLMF.Hypergeometric
open DLMF.Confluent

noncomputable section

set_option autoImplicit false

namespace DLMF.OrthogonalPolynomials

/-- A generalized continued fraction with zero integer part and prescribed
partial numerators and denominators, using Mathlib's continuants. -/
def polynomialFraction (a b : ℕ → ℂ) : GenContFract ℂ where
  h := 0
  s := Stream'.Seq.ofStream (fun k => ⟨a k, b k⟩)

/-- The initial denominator does not depend on the first partial numerator. -/
theorem polynomialFraction_dens_one (a b : ℕ → ℂ) :
    (polynomialFraction a b).dens 1 = b 0 :=
  GenContFract.first_den_eq (g := polynomialFraction a b) (gp := ⟨a 0, b 0⟩) (by rfl)

/-- Mathlib's denominator recurrence specialized to the prescribed stream. -/
theorem polynomialFraction_dens_step (a b : ℕ → ℂ) (n : ℕ) :
    (polynomialFraction a b).dens (n + 2) =
      b (n + 1) * (polynomialFraction a b).dens (n + 1) +
        a (n + 1) * (polynomialFraction a b).dens n :=
  GenContFract.dens_recurrence (g := polynomialFraction a b) (n := n)
    (gp := ⟨a (n + 1), b (n + 1)⟩) (by rfl) rfl rfl

/-- Identity under the stated parameter and domain assumptions: `(polynomialFraction (fun _ => -1)
(fun k => if k = 0 then x else 2 * x)).dens n = (Chebyshev.T ℂ n).eval x`. -/
@[dlmf 18.13.E1]
theorem chebyshevT_continued_fraction (n : ℕ) (x : ℂ) :
    (polynomialFraction (fun _ => -1) (fun k => if k = 0 then x else 2 * x)).dens n =
      (Chebyshev.T ℂ n).eval x := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp [polynomialFraction_dens_one]
  | more n ih0 ih1 =>
    rw [polynomialFraction_dens_step, ih0, ih1]
    simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false]
    push_cast
    rw [Chebyshev.T_add_two]
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]
    ring

/-- Identity under the stated parameter and domain assumptions: `(polynomialFraction (fun _ => -1)
(fun _ => 2 * x)).dens n = (Chebyshev.U ℂ n).eval x`. -/
@[dlmf 18.13.E2]
theorem chebyshevU_continued_fraction (n : ℕ) (x : ℂ) :
    (polynomialFraction (fun _ => -1) (fun _ => 2 * x)).dens n = (Chebyshev.U ℂ n).eval x := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp [polynomialFraction_dens_one]
  | more n ih0 ih1 =>
    rw [polynomialFraction_dens_step, ih0, ih1]
    push_cast
    rw [Chebyshev.U_add_two]
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]
    ring

/-- Identity under the stated parameter and domain assumptions: `(polynomialFraction (fun k => if
k = 0 then a else -(k : ℂ) / (k + 1)) (fun k => (2 * k + 1 : ℂ) / (k + 1) * x)).dens n =
legendrePolyP n x`. -/
@[dlmf 18.13.E3]
theorem legendre_continued_fraction (a : ℂ) (n : ℕ) (x : ℂ) :
    (polynomialFraction (fun k => if k = 0 then a else -(k : ℂ) / (k + 1))
      (fun k => (2 * k + 1 : ℂ) / (k + 1) * x)).dens n = legendrePolyP n x := by
  induction n using Nat.twoStepInduction with
  | zero => simp [legendrePolyP_zero]
  | one => simp [polynomialFraction_dens_one]
  | more n ih0 ih1 =>
    rw [polynomialFraction_dens_step, ih0, ih1]
    simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false]
    push_cast
    have hn : (n + 2 : ℂ) ≠ 0 := by exact_mod_cast (by omega : n + 2 ≠ 0)
    calc
      _ = ((2 * n + 3) * x * legendrePolyP (n + 1) x - (n + 1) * legendrePolyP n x) / (n + 2)
          := by ring
      _ = _ := (div_eq_iff hn).mpr (by linear_combination -(legendrePolyP_recurrence n x))

/-- Identity under the stated parameter and domain assumptions: `(polynomialFraction (fun k => if
k = 0 then a else -(k : ℂ) / (k + 1)) (fun k => (2 * k + 1 - x) / (k + 1))).dens n =
laguerrePolyL 0 n x`. -/
@[dlmf 18.13.E4]
theorem laguerrePolyL_continued_fraction (a : ℂ) (n : ℕ) (x : ℂ) :
    (polynomialFraction (fun k => if k = 0 then a else -(k : ℂ) / (k + 1))
      (fun k => (2 * k + 1 - x) / (k + 1))).dens n = laguerrePolyL 0 n x := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one =>
    have h1 : laguerrePolyL 0 1 x = 1 - x := by
      rw [laguerrePolyL, show -((1 : ℕ) : ℂ) = -(1 : ℂ) by norm_num,
        show -(1 : ℂ) = -((1 : ℕ) : ℂ) by norm_num, kummerM_eq_sum_neg_nat]
      simp [Finset.sum_range_succ, poch_one, poch_zero]
      ring
    rw [polynomialFraction_dens_one, h1]
    simp
  | more n ih0 ih1 =>
    rw [polynomialFraction_dens_step, ih0, ih1]
    simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false]
    push_cast
    have hn : (n + 2 : ℂ) ≠ 0 := by exact_mod_cast (by omega : n + 2 ≠ 0)
    have hrec := laguerrePolyL_recurrence (α := 0) (by simp) n x
    calc
      _ = ((2 * n + 3 - x) * laguerrePolyL 0 (n + 1) x - (n + 1) * laguerrePolyL 0 n x) / (n + 2)
          := by ring
      _ = _ := (div_eq_iff hn).mpr (by linear_combination -hrec)

/-- Identity under the stated parameter and domain assumptions: `(polynomialFraction (fun k => if
k = 0 then 1 else -2 * (k : ℂ)) (fun _ => 2 * x)).dens n = aeval x (hermitePolyH n)`. -/
@[dlmf 18.13.E5]
theorem hermitePolyH_continued_fraction (n : ℕ) (x : ℂ) :
    (polynomialFraction (fun k => if k = 0 then 1 else -2 * (k : ℂ))
      (fun _ => 2 * x)).dens n = aeval x (hermitePolyH n) := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp only [polynomialFraction_dens_one, hermitePolyH_one, map_mul, map_ofNat, aeval_X]
  | more n ih0 ih1 =>
    rw [polynomialFraction_dens_step, ih0, ih1, hermitePolyH_recurrence]
    simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false,
      map_sub, map_mul, map_ofNat, aeval_X, aeval_C]
    push_cast
    ring


end DLMF.OrthogonalPolynomials
