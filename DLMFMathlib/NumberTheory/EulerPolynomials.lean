/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.NumberTheory.BernoulliPolynomials
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Euler polynomials and Euler numbers

The Euler polynomials are the Appell sequence with exponential generating function
`2 e^{xt}/(e^t + 1) = ∑ Eₙ(x) tⁿ/n!`. Comparing coefficients in `(e^t + 1) ∑ Eₙ(x) tⁿ/n! =
2e^{xt}` gives the recursion `Eₙ = Xⁿ - ½ ∑_{k<n} (n choose k) E_k`, which we take as the
definition (compare `Polynomial.bernoulli`).

The basic tool is uniqueness for the difference equation `P(x+1) + P(x) = Q(x)`: the only
polynomial with `P(x+1) + P(x) = 0` is zero, since such a polynomial is `2`-periodic. Every
identity below is reduced to the defining relation `Eₙ(x+1) + Eₙ(x) = 2xⁿ` (Temme,
*Special Functions*, §1.2).

## Main definitions

* `Polynomial.euler`: the Euler polynomials `Eₙ`.
* `eulerNumber`: the Euler numbers `Eₙ = 2ⁿ Eₙ(1/2)`, the coefficients of `sech t`.
* `eulerFun`: `Eₙ` as a function `ℝ → ℝ`.

## Main results

* `Polynomial.euler_comp_X_add_one_add`: `Eₙ(x+1) + Eₙ(x) = 2xⁿ`.
* `Polynomial.derivative_euler`: `Eₙ' = n Eₙ₋₁`.
* `Polynomial.euler_comp_X_add_C`: the binomial (Appell) property
  `Eₙ(x+h) = ∑ₖ (n choose k) hⁿ⁻ᵏ Eₖ(x)`.
* `Polynomial.euler_comp_one_sub_X`: the reflection `Eₙ(1-x) = (-1)ⁿ Eₙ(x)`.
* `Polynomial.sum_range_neg_one_pow_mul_pow`: alternating power sums
  `∑_{k<N} (-1)ᵏ kⁿ = (Eₙ(0) - (-1)ᴺ Eₙ(N))/2`.
* `eulerNumber_eq_zero_of_odd` and `sum_choose_mul_eulerNumber`: odd Euler numbers vanish,
  and `∑ₖ (n choose k)(1 + (-1)ⁿ⁻ᵏ) Eₖ = 2 δ_{n0}`, the coefficient form of
  `cosh t · sech t = 1`.
-/

@[expose] public section

noncomputable section

open Finset

namespace Polynomial

/-- The Euler polynomials, by the recursion `Eₙ = Xⁿ - ½ ∑_{k<n} (n choose k) E_k`. -/
@[dlmf 24.2.E8]
def euler (n : ℕ) : ℚ[X] :=
  X ^ n - C (1 / 2) * ∑ k : Fin n, ((n.choose k : ℚ) • euler k)
decreasing_by exact k.2

theorem euler_def (n : ℕ) :
    euler n = X ^ n - C (1 / 2) * ∑ k ∈ range n, ((n.choose k : ℚ) • euler k) := by
  rw [euler, Fin.sum_univ_eq_sum_range (fun k => ((n.choose k : ℚ) • euler k))]

/-- The defining relation in summed form: `∑_{k<n} (n choose k) E_k + 2 Eₙ = 2 Xⁿ`. -/
theorem sum_range_choose_smul_euler (n : ℕ) :
    ∑ k ∈ range n, ((n.choose k : ℚ) • euler k) + 2 * euler n = 2 * X ^ n := by
  rw [euler_def n]
  have h : (2 : ℚ[X]) * C (1 / 2) = 1 := by rw [← C_ofNat, ← C_mul]; norm_num
  linear_combination (-(∑ k ∈ range n, ((n.choose k : ℚ) • euler k))) * h

@[simp]
theorem euler_zero : euler 0 = 1 := by rw [euler_def]; simp

theorem euler_one : euler 1 = X - C (1 / 2) := by
  rw [euler_def, sum_range_one, euler_zero]; simp

/-! ### Derivatives and the values at `0` and `1` -/

theorem derivative_euler_succ (n : ℕ) :
    derivative (euler (n + 1)) = (n + 1 : ℚ[X]) * euler n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rw [euler_def (n + 1), euler_def n]
  simp only [derivative_sub, derivative_X_pow, derivative_mul, derivative_C, zero_mul, zero_add,
    derivative_sum, derivative_smul]
  -- reindex the sum over `k < n + 1` by `k = j + 1`
  rw [sum_range_succ' _ n, euler_zero, derivative_one, smul_zero, add_zero]
  have hterm : ∀ j ∈ range n, ((n + 1).choose (j + 1) : ℚ) • derivative (euler (j + 1)) =
      (n + 1 : ℚ[X]) * ((n.choose j : ℚ) • euler j) := by
    intro j hj
    rw [ih j (mem_range.mp hj), smul_eq_C_mul, smul_eq_C_mul,
      show ((j : ℚ[X]) + 1) = C ((j : ℚ) + 1) by simp,
      show ((n : ℚ[X]) + 1) = C ((n : ℚ) + 1) by simp, ← mul_assoc, ← mul_assoc, ← C_mul,
      ← C_mul]
    have : ((n + 1).choose (j + 1) : ℚ) * (j + 1) = (n + 1) * n.choose j := by
      have h : ((n : ℚ) + 1) * n.choose j = (n + 1).choose (j + 1) * ((j : ℚ) + 1) := by
        exact_mod_cast Nat.add_one_mul_choose_eq n j
      linarith
    rw [this]
  rw [sum_congr rfl hterm, ← mul_sum]
  simp only [map_add, map_one, map_natCast, Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]
  ring

@[dlmf 24.4.E35]
theorem derivative_euler (n : ℕ) : derivative (euler n) = (n : ℚ[X]) * euler (n - 1) := by
  cases n with
  | zero => simp
  | succ n => simpa using derivative_euler_succ n

/-- `Eₙ(1) + Eₙ(0) = 2 · 0ⁿ`. -/
@[dlmf 24.4.E26]
theorem euler_eval_one_add_eval_zero (n : ℕ) :
    (euler n).eval 1 + (euler n).eval 0 = 2 * 0 ^ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases n with _ | n
  · simp; norm_num
  have h1 := congrArg (eval 1) (sum_range_choose_smul_euler (n + 1))
  have h0 := congrArg (eval 0) (sum_range_choose_smul_euler (n + 1))
  simp only [eval_add, eval_finsetSum, eval_smul, eval_mul, eval_ofNat, eval_pow, eval_X,
    smul_eq_mul] at h1 h0
  rw [sum_range_succ'] at h1 h0
  have hsum : ∑ k ∈ range n, ((n + 1).choose (k + 1) : ℚ) * (euler (k + 1)).eval 1 +
      ∑ k ∈ range n, ((n + 1).choose (k + 1) : ℚ) * (euler (k + 1)).eval 0 = 0 := by
    rw [← sum_add_distrib]
    refine sum_eq_zero fun k hk => ?_
    rw [← mul_add, ih (k + 1) (by simp at hk; omega)]
    simp
  simp only [euler_zero, eval_one, Nat.choose_zero_right, Nat.cast_one, mul_one] at h1 h0
  rw [zero_pow (Nat.succ_ne_zero n)] at h0 ⊢
  simp only [one_pow, mul_one, mul_zero] at h1 h0 ⊢
  linarith

/-! ### The difference equation and uniqueness -/

/-- A polynomial with `P(x+1) + P(x) = 0` vanishes. -/
theorem eq_zero_of_comp_X_add_one_add_self {P : ℚ[X]} (h : P.comp (X + 1) + P = 0) : P = 0 := by
  have h2 : ∀ x : ℚ, P.eval (x + 2) = P.eval x := by
    intro x
    have hx := congrArg (eval x) h
    have hx1 := congrArg (eval (x + 1)) h
    simp only [eval_add, eval_comp, eval_X, eval_one, eval_zero] at hx hx1
    rw [show x + 2 = x + 1 + 1 by ring]
    linarith
  have hk : ∀ k : ℕ, P.eval (2 * (k : ℚ)) = P.eval 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show (2 * ((k + 1 : ℕ) : ℚ)) = 2 * k + 2 by push_cast; ring, h2, ih]
  have hconst : P = C (P.eval 0) := by
    apply Polynomial.eq_of_infinite_eval_eq
    have hinj : Function.Injective (fun k : ℕ => (2 * k : ℚ)) := fun a b hab => by
      simpa using hab
    refine Set.infinite_of_injective_forall_mem hinj fun k => ?_
    simp [hk k]
  have h0 := congrArg (eval 0) h
  simp only [eval_add, eval_comp, eval_X, eval_one, zero_add, eval_zero] at h0
  have h1 : P.eval 1 = P.eval 0 := by
    rw [hconst]; simp
  have hz : P.eval 0 = 0 := by linarith
  rw [hconst, hz, C_0]

/-- Uniqueness for the difference equation `P(x+1) + P(x) = R(x)`. -/
theorem eq_of_comp_X_add_one_add_self_eq {P Q : ℚ[X]}
    (h : P.comp (X + 1) + P = Q.comp (X + 1) + Q) : P = Q := by
  have := eq_zero_of_comp_X_add_one_add_self (P := P - Q) (by
    rw [sub_comp]; linear_combination h)
  exact sub_eq_zero.mp this

/-- The defining property `Eₙ(x+1) + Eₙ(x) = 2xⁿ`. -/
@[dlmf 24.4.E2]
theorem euler_comp_X_add_one_add (n : ℕ) :
    (euler n).comp (X + 1) + euler n = 2 * X ^ n := by
  induction n with
  | zero => simp; norm_num
  | succ n ih =>
    -- the difference has zero derivative and vanishes at `0`
    set F := (euler (n + 1)).comp (X + 1) + euler (n + 1) - 2 * X ^ (n + 1) with hF
    have hD : derivative F = 0 := by
      simp only [hF, derivative_sub, derivative_add, derivative_comp, derivative_X,
        derivative_one, add_zero, one_mul, derivative_euler_succ, derivative_mul,
        derivative_ofNat, zero_mul, zero_add, derivative_X_pow, mul_comp, natCast_comp,
        add_comp, one_comp]
      rw [Nat.add_sub_cancel, show (2 : ℚ[X]) * (C ((n + 1 : ℕ) : ℚ) * X ^ n) =
          ((n : ℚ[X]) + 1) * (2 * X ^ n) by simp; ring, ← ih]
      ring
    have hconst : F = C (F.eval 0) := by
      rw [← coeff_zero_eq_eval_zero]
      exact eq_C_of_natDegree_eq_zero (derivative_eq_zero.mp hD)
    have h0 : F.eval 0 = 0 := by
      have := euler_eval_one_add_eval_zero (n + 1)
      simp only [hF, eval_sub, eval_add, eval_comp, eval_X, eval_one, zero_add, eval_mul,
        eval_pow, eval_ofNat]
      rw [this]
      ring
    rw [h0, C_0] at hconst
    exact sub_eq_zero.mp hconst

theorem euler_eval_add_one_add (n : ℕ) (x : ℚ) :
    (euler n).eval (x + 1) + (euler n).eval x = 2 * x ^ n := by
  simpa using congrArg (eval x) (euler_comp_X_add_one_add n)

/-! ### The binomial property and reflection -/

/-- The Appell property `Eₙ(x+h) = ∑ₖ (n choose k) h^{n-k} E_k(x)`. -/
@[dlmf 24.4.E13]
theorem euler_comp_X_add_C (n : ℕ) (h : ℚ) :
    (euler n).comp (X + C h) =
      ∑ k ∈ range (n + 1), C ((n.choose k : ℚ) * h ^ (n - k)) * euler k := by
  -- `P = ∑ₖ (n choose k) hⁿ⁻ᵏ Eₖ(x - h)` satisfies the defining relation
  set P := ∑ k ∈ range (n + 1), C ((n.choose k : ℚ) * h ^ (n - k)) * (euler k).comp (X - C h)
    with hP
  have hk : ∀ k, ((euler k).comp (X - C h)).comp (X + 1) + (euler k).comp (X - C h) =
      2 * (X - C h) ^ k := by
    intro k
    have hsw : (X - C h).comp (X + 1) = (X + 1).comp (X - C h) := by
      simp only [sub_comp, add_comp, X_comp, C_comp, one_comp]; ring
    rw [comp_assoc, hsw, ← comp_assoc, ← add_comp, euler_comp_X_add_one_add]
    simp
  have hPeq : P = euler n := by
    apply eq_of_comp_X_add_one_add_self_eq
    rw [euler_comp_X_add_one_add]
    simp only [hP, sum_comp, mul_comp, C_comp, ← sum_add_distrib, ← mul_add, hk]
    rw [show (2 : ℚ[X]) * X ^ n = 2 * ((X - C h) + C h) ^ n by ring, add_pow, mul_sum]
    refine sum_congr rfl fun k _ => ?_
    simp only [map_mul, map_pow, map_natCast]
    ring
  have hX : (X - C h).comp (X + C h) = (X : ℚ[X]) := by
    simp only [sub_comp, X_comp, C_comp]; ring
  rw [← hPeq, hP, sum_comp]
  refine sum_congr rfl fun k _ => ?_
  rw [mul_comp, C_comp, comp_assoc, hX, comp_X]

theorem euler_eval_add (n : ℕ) (x h : ℚ) :
    (euler n).eval (x + h) = ∑ k ∈ range (n + 1), (n.choose k : ℚ) * h ^ (n - k) *
      (euler k).eval x := by
  simpa [eval_finsetSum] using congrArg (eval x) (euler_comp_X_add_C n h)

/-- The reflection `Eₙ(1-x) = (-1)ⁿ Eₙ(x)`. -/
@[dlmf 24.4.E4]
theorem euler_comp_one_sub_X (n : ℕ) :
    (euler n).comp (1 - X) = C ((-1) ^ n) * euler n := by
  have hc : ((-1 : ℚ) ^ n) * (-1) ^ n = 1 := by rw [← mul_pow]; norm_num
  have hP : C ((-1 : ℚ) ^ n) * (euler n).comp (1 - X) = euler n := by
    apply eq_of_comp_X_add_one_add_self_eq
    rw [euler_comp_X_add_one_add]
    have h1 : (1 - X : ℚ[X]).comp (X + 1) = -X := by simp
    have h2 : (X + 1 : ℚ[X]).comp (-X) = 1 - X := by simp; ring
    have hA : ((euler n).comp (1 - X)).comp (X + 1) = (euler n).comp (-X) := by
      rw [comp_assoc, h1]
    have hB : (euler n).comp (1 - X) = ((euler n).comp (X + 1)).comp (-X) := by
      rw [comp_assoc, h2]
    have hE : ((euler n).comp (X + 1)).comp (-X) + (euler n).comp (-X) = 2 * (-X) ^ n := by
      rw [← add_comp, euler_comp_X_add_one_add]; simp
    rw [mul_comp, C_comp, hA, hB, ← mul_add, add_comm, hE, neg_pow (X : ℚ[X]),
      show ((-1 : ℚ[X])) ^ n = C ((-1) ^ n) by simp,
      show C ((-1 : ℚ) ^ n) * (2 * (C ((-1) ^ n) * X ^ n)) =
        2 * C ((-1) ^ n * (-1) ^ n) * X ^ n by rw [C_mul]; ring, hc]
    simp
  calc (euler n).comp (1 - X) = C ((-1) ^ n * (-1) ^ n) * (euler n).comp (1 - X) := by
        rw [hc]; simp
    _ = C ((-1) ^ n) * euler n := by rw [C_mul, mul_assoc, hP]

theorem euler_eval_one_sub (n : ℕ) (x : ℚ) :
    (euler n).eval (1 - x) = (-1) ^ n * (euler n).eval x := by
  simpa using congrArg (eval x) (euler_comp_one_sub_X n)

/-! ### Alternating power sums -/

/-- `2 ∑_{k<N} (-1)ᵏ kⁿ = Eₙ(0) - (-1)ᴺ Eₙ(N)`. -/
@[dlmf 24.4.E8]
theorem sum_range_neg_one_pow_mul_pow (n N : ℕ) :
    2 * ∑ k ∈ range N, (-1 : ℚ) ^ k * (k : ℚ) ^ n =
      (euler n).eval 0 - (-1) ^ N * (euler n).eval (N : ℚ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, mul_add, ih]
    have h := euler_eval_add_one_add n (N : ℚ)
    push_cast
    rw [pow_succ]
    linear_combination (-(-1 : ℚ) ^ N) * h

end Polynomial

/-! ### Euler numbers -/

open Polynomial

/-- The Euler numbers `Eₙ = 2ⁿ Eₙ(1/2)`, the coefficients of `sech t = ∑ Eₙ tⁿ/n!`. -/
@[dlmf 24.2.E9]
def eulerNumber (n : ℕ) : ℚ := 2 ^ n * (euler n).eval (1 / 2)

@[simp]
theorem eulerNumber_zero : eulerNumber 0 = 1 := by simp [eulerNumber]

/-- The odd Euler numbers vanish. -/
@[dlmf 24.2.E7]
theorem eulerNumber_eq_zero_of_odd {n : ℕ} (hn : Odd n) : eulerNumber n = 0 := by
  have h := euler_eval_one_sub n (1 / 2)
  rw [show (1 : ℚ) - 1 / 2 = 1 / 2 by norm_num, hn.neg_one_pow] at h
  have : (euler n).eval (1 / 2) = 0 := by linarith
  rw [eulerNumber, this, mul_zero]

/-- `∑ₖ (n choose k)(1 + (-1)ⁿ⁻ᵏ) Eₖ = 2 · 0ⁿ`, the coefficients of `cosh t · sech t = 1`. -/
theorem sum_choose_mul_eulerNumber (n : ℕ) :
    ∑ k ∈ range (n + 1), (n.choose k : ℚ) * (1 + (-1) ^ (n - k)) * eulerNumber k = 2 * 0 ^ n := by
  have h1 := euler_eval_add n (1 / 2) (1 / 2)
  have h0 := euler_eval_add n (1 / 2) (-(1 / 2))
  have hs := euler_eval_one_add_eval_zero n
  rw [show (1 : ℚ) / 2 + 1 / 2 = 1 by norm_num] at h1
  rw [show (1 : ℚ) / 2 + -(1 / 2) = 0 by norm_num] at h0
  rw [h1, h0, ← sum_add_distrib] at hs
  have key : ∀ k ∈ range (n + 1), (n.choose k : ℚ) * (1 + (-1) ^ (n - k)) * eulerNumber k =
      2 ^ n * ((n.choose k : ℚ) * (1 / 2) ^ (n - k) * (euler k).eval (1 / 2) +
        (n.choose k : ℚ) * (-(1 / 2)) ^ (n - k) * (euler k).eval (1 / 2)) := by
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
    have h2 : (2 : ℚ) ^ n = 2 ^ k * 2 ^ (n - k) := by rw [← pow_add, Nat.add_sub_cancel' hkn]
    rw [eulerNumber, neg_pow (1 / 2 : ℚ), h2, div_pow, one_pow]
    field_simp
  rw [sum_congr rfl key, ← mul_sum, hs]
  rcases n with _ | n
  · simp
  · simp

/-! ### Euler polynomials as real functions -/

/-- The function `x ↦ Eₙ(x) : ℝ → ℝ`. -/
@[dlmf 24.2.ii]
def eulerFun (n : ℕ) (x : ℝ) : ℝ := ((euler n).map (algebraMap ℚ ℝ)).eval x

theorem eulerFun_add_one_add (n : ℕ) (x : ℝ) :
    eulerFun n (x + 1) + eulerFun n x = 2 * x ^ n := by
  have h := congrArg (fun p => (p.map (algebraMap ℚ ℝ)).eval x) (euler_comp_X_add_one_add n)
  simpa [eulerFun, Polynomial.map_comp, eval_comp] using h

theorem eulerFun_one_sub (n : ℕ) (x : ℝ) : eulerFun n (1 - x) = (-1) ^ n * eulerFun n x := by
  have h := congrArg (fun p => (p.map (algebraMap ℚ ℝ)).eval x) (euler_comp_one_sub_X n)
  simpa [eulerFun, Polynomial.map_comp, eval_comp] using h

theorem hasDerivAt_eulerFun (n : ℕ) (x : ℝ) :
    HasDerivAt (eulerFun n) (n * eulerFun (n - 1) x) x := by
  convert! ((euler n).map (algebraMap ℚ ℝ)).hasDerivAt x using 1
  simp only [eulerFun, Polynomial.derivative_map, derivative_euler, Polynomial.map_mul,
    Polynomial.map_natCast, Polynomial.eval_mul, Polynomial.eval_natCast]

theorem continuous_eulerFun (n : ℕ) : Continuous (eulerFun n) :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_eulerFun n x).continuousAt
