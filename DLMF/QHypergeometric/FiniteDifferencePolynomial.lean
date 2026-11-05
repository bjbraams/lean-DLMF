/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.BasicSummations.OnePhiZero
public import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Annihilation of polynomials by finite q-differences

The terminating q-binomial theorem shows that the finite q-difference of order `n`
vanishes on every polynomial of degree less than `n`. This finite-sum form supplies
polynomial interpolation proofs of terminating basic hypergeometric identities.
-/

@[expose] public noncomputable section

open Complex Finset Polynomial
open DLMF.QSeries

namespace DLMF.QHypergeometric.FiniteDifferencePolynomial

/-- The weights of the unnormalized finite q-difference of order `n`. -/
def coefficient (q : ℂ) (n k : ℕ) : ℂ :=
  qPochhammer (q ^ (-(n : ℤ))) q k / qPochhammer q q k * q ^ k

/-- A finite q-difference vanishes on a monomial of degree less than its order. -/
theorem sum_monomial_eq_zero {q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) {m n : ℕ}
    (hm : m < n) :
    ∑ k ∈ range (n + 1), coefficient q n k * (q ^ k) ^ m = 0 := by
  have h := one_phi_zero_terminating hq0 hq (q ^ (m + 1)) n
  rw [qPhi_terminates hq0 n, qPhiPartial] at h
  have he : qPhiExponent [q ^ (-(n : ℤ))] [] = 0 := by simp [qPhiExponent]
  simp only [qPhiTerm, he, qPochhammerList, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, one_mul, zpow_zero] at h
  have harg : q ^ (m + 1) * q ^ (-(n : ℤ)) = q ^ (-((n - m - 1 : ℕ) : ℤ)) := by
    rw [← zpow_natCast q (m + 1), ← zpow_add₀ hq0]
    congr 1
    omega
  rw [harg] at h
  simp only [zpow_neg, zpow_natCast] at h
  rw [qPochhammer_recip_pow_eq_zero hq0 (by omega : n - m - 1 < n)] at h
  have hp (k : ℕ) : q ^ k * (q ^ k) ^ m = (q ^ (m + 1)) ^ k := by
    rw [← pow_succ', ← pow_mul, ← pow_mul]
    congr 1
    ring
  simpa only [coefficient, zpow_neg, zpow_natCast, mul_assoc, hp] using h

/-- A finite q-difference vanishes on every polynomial of degree below its order. -/
theorem sum_eval_eq_zero_of_natDegree_lt {q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (P : Polynomial ℂ) {n : ℕ} (hP : P.natDegree < n) :
    ∑ k ∈ range (n + 1), coefficient q n k * P.eval (q ^ k) = 0 := by
  simp only [Polynomial.eval_eq_sum_range, mul_sum]
  rw [sum_comm]
  refine sum_eq_zero fun j hj => ?_
  have hjn : j < n := by simp only [mem_range] at hj; omega
  calc
    _ = P.coeff j * ∑ k ∈ range (n + 1), coefficient q n k * (q ^ k) ^ j := by
      rw [mul_sum]
      exact sum_congr rfl fun k _ => by ring
    _ = 0 := by rw [sum_monomial_eq_zero hq0 hq hjn, mul_zero]

end DLMF.QHypergeometric.FiniteDifferencePolynomial
