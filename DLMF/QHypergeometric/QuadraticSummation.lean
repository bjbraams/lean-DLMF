/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.FiniteDifferencePolynomial
public import DLMF.QHypergeometric.DixonPolynomial
public import Mathlib.LinearAlgebra.Lagrange

/-!
# The first balanced quadratic summation

Polynomial interpolation gives the first balanced base-square sum of DLMF 17.7.12.
The finite q-difference method follows X. Wang and W. Chu, *Approach of q-Derivative
Operators to Terminating q-Series Formulae*, Communications in Mathematics 26 (2018),
§4, https://doi.org/10.2478/cm-2018-0007.
-/

@[expose] public noncomputable section

open Complex Finset Polynomial
open DLMF.QSeries

namespace DLMF.QHypergeometric.QuadraticSummation

/-- The degree of a polynomial shifted factorial is at most its length. -/
theorem natDegree_pochhammerPolynomial_le (a q : ℂ) (n : ℕ) :
    (DixonPolynomial.pochhammerPolynomial a q n).natDegree ≤ n := by
  unfold DixonPolynomial.pochhammerPolynomial
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  calc
    _ ≤ ∑ _j ∈ range n, 1 := by
      apply sum_le_sum
      intro j _
      refine (Polynomial.natDegree_sub_le _ _).trans ?_
      simp only [natDegree_one, zero_max]
      have h1 := Polynomial.natDegree_mul_le (p := C a) (q := (X : Polynomial ℂ))
      have h2 := Polynomial.natDegree_mul_le (p := C a * X) (q := C (q ^ j))
      simp only [natDegree_C, natDegree_X, Nat.zero_add, Nat.add_zero] at h1 h2
      exact h2.trans h1
    _ = n := by simp

/-- The polynomial remaining after cancellation of the squared lower parameter. -/
def termPolynomial (q : ℂ) (n : ℕ) : ℕ → Polynomial ℂ
  | 0 => DixonPolynomial.pochhammerPolynomial (-q) q n
  | k + 1 => (1 - X) * DixonPolynomial.pochhammerPolynomial (q ^ (k + 2)) q k *
      DixonPolynomial.pochhammerPolynomial (-q ^ (k + 2)) q (n - k - 1)

/-- The coefficients independent of the interpolated parameter. -/
def coefficient (b q : ℂ) (n k : ℕ) : ℂ :=
  qPochhammer ((q ^ 2) ^ (-(n : ℤ))) (q ^ 2) k *
    qPochhammer (b ^ 2 * q ^ (2 * n)) (q ^ 2) k /
      (qPochhammer b q (2 * k) * qPochhammer (q ^ 2) (q ^ 2) k) * (q ^ 2) ^ k

/-- The first balanced quadratic sum after clearing its parameter-dependent denominator. -/
def sumPolynomial (b q : ℂ) (n : ℕ) : Polynomial ℂ :=
  ∑ k ∈ range (n + 1), C (coefficient b q n k) * termPolynomial q n k

/-- The product value after clearing the parameter-dependent denominator. -/
def valuePolynomial (b q : ℂ) (n : ℕ) : Polynomial ℂ :=
  C (qPochhammer (-q) q n / qPochhammer b q n) *
    ∏ j ∈ range n, (X - C (b * q ^ j))

/-- The cancellation polynomial has degree at most `n`. -/
theorem natDegree_termPolynomial_le (q : ℂ) (n k : ℕ) (hk : k ≤ n) :
    (termPolynomial q n k).natDegree ≤ n := by
  cases k with
  | zero => exact natDegree_pochhammerPolynomial_le _ _ _
  | succ k =>
    have h1 := natDegree_pochhammerPolynomial_le (q ^ (k + 2)) q k
    have h2 := natDegree_pochhammerPolynomial_le (-q ^ (k + 2)) q (n - k - 1)
    have h3 : (1 - (X : Polynomial ℂ)).natDegree ≤ 1 := by
      exact (Polynomial.natDegree_sub_le _ _).trans (by simp)
    have h4 := Polynomial.natDegree_mul_le (p := 1 - (X : Polynomial ℂ))
      (q := DixonPolynomial.pochhammerPolynomial (q ^ (k + 2)) q k)
    have h5 := Polynomial.natDegree_mul_le
      (p := (1 - (X : Polynomial ℂ)) *
        DixonPolynomial.pochhammerPolynomial (q ^ (k + 2)) q k)
      (q := DixonPolynomial.pochhammerPolynomial (-q ^ (k + 2)) q (n - k - 1))
    dsimp [termPolynomial]
    omega

/-- The cleared finite sum has degree at most `n`. -/
theorem natDegree_sumPolynomial_le (b q : ℂ) (n : ℕ) :
    (sumPolynomial b q n).natDegree ≤ n := by
  unfold sumPolynomial
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  exact (Polynomial.natDegree_C_mul_le _ _).trans
    (natDegree_termPolynomial_le q n k (by simp at hk; omega))

/-- The product value has degree at most `n`. -/
theorem natDegree_valuePolynomial_le (b q : ℂ) (n : ℕ) :
    (valuePolynomial b q n).natDegree ≤ n := by
  unfold valuePolynomial
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  calc
    _ ≤ ∑ _j ∈ range n, 1 := by
      refine (Polynomial.natDegree_prod_le _ _).trans ?_
      apply sum_le_sum
      intro j _
      exact (Polynomial.natDegree_sub_le _ _).trans (by
        simp only [natDegree_X, natDegree_C, _root_.max_zero]
        exact le_rfl)
    _ = n := by simp

/-- Evaluation of the cancellation polynomial at index zero. -/
@[simp] theorem eval_termPolynomial_zero (a q : ℂ) (n : ℕ) :
    (termPolynomial q n 0).eval a = qPochhammer (-a * q) q n := by
  simp [termPolynomial, mul_comm]

/-- Evaluation of the cancellation polynomial at positive index. -/
@[simp] theorem eval_termPolynomial_succ (a q : ℂ) (n k : ℕ) :
    (termPolynomial q n (k + 1)).eval a = (1 - a) *
      qPochhammer (a * q ^ (k + 2)) q k *
      qPochhammer (-a * q ^ (k + 2)) q (n - k - 1) := by
  simp [termPolynomial, mul_comm]

/-- Clearing the squared shifted factorial recovers the uncancelled numerator. -/
theorem eval_termPolynomial_mul (a q : ℂ) (n k : ℕ) (hk : k ≤ n) :
    (termPolynomial q n k).eval a * qPochhammer (a ^ 2 * q ^ 2) (q ^ 2) k =
      qPochhammer a q (2 * k) * qPochhammer (-a * q) q n := by
  cases k with
  | zero => simp
  | succ k =>
    have hA : qPochhammer a q (2 * (k + 1)) = (1 - a) *
        qPochhammer (a * q) q (k + 1) * qPochhammer (a * q ^ (k + 2)) q k := by
      rw [show 2 * (k + 1) = (k + 2) + k by omega, qPochhammer_add,
        show k + 2 = (k + 1) + 1 by omega, qPochhammer_succ']
    have hB : qPochhammer (-a * q) q n = qPochhammer (-a * q) q (k + 1) *
        qPochhammer (-a * q ^ (k + 2)) q (n - k - 1) := by
      have h := qPochhammer_add (-a * q) q (k + 1) (n - k - 1)
      rw [show (k + 1) + (n - k - 1) = n by omega,
        show -a * q * q ^ (k + 1) = -a * q ^ (k + 2) by
          rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]; ring] at h
      exact h
    rw [eval_termPolynomial_succ, show a ^ 2 * q ^ 2 = (a * q) ^ 2 by ring,
      qPochhammer_squared, hA, hB]
    rw [show -(a * q) = -a * q by ring]
    ring

/-- Nonvanishing of a finite shifted factorial when its parameter and base are in the unit disk. -/
theorem pochhammer_ne_zero_of_norm_lt_one {a q : ℂ} (ha : ‖a‖ < 1) (hq : ‖q‖ < 1)
    (n : ℕ) : qPochhammer a q n ≠ 0 := by
  have h := qPochhammerInf_ne_zero_of_norm_lt_one ha hq
  rw [qPochhammerInf_mul_qPochhammer hq n] at h
  exact left_ne_zero_of_mul h

/-- The finite summand before cancellation. -/
def seriesTerm (a b q : ℂ) (n k : ℕ) : ℂ :=
  qPochhammer ((q ^ 2) ^ (-(n : ℤ))) (q ^ 2) k * qPochhammer a q (2 * k) *
    qPochhammer (b ^ 2 * q ^ (2 * n)) (q ^ 2) k /
      (qPochhammer (a ^ 2 * q ^ 2) (q ^ 2) k * qPochhammer b q (2 * k) *
        qPochhammer (q ^ 2) (q ^ 2) k) * (q ^ 2) ^ k

/-- The polynomial and finite series agree after multiplying by the removable factor. -/
theorem eval_sumPolynomial (a b q : ℂ) (n : ℕ) (hq : ‖q‖ < 1)
    (hA : qPochhammer (a ^ 2 * q ^ 2) (q ^ 2) n ≠ 0)
    (hB : qPochhammer b q (2 * n) ≠ 0) :
    (sumPolynomial b q n).eval a =
      qPochhammer (-a * q) q n * ∑ k ∈ range (n + 1), seriesTerm a b q n k := by
  have hQ : ‖q ^ 2‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (by omega)
  simp only [sumPolynomial, eval_finsetSum, eval_mul, eval_C, mul_sum]
  apply sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by simp at hk; omega
  have ha := qPochhammer_ne_zero_of_le hA hkn
  have hb := qPochhammer_ne_zero_of_le hB (show 2 * k ≤ 2 * n by omega)
  have hqq := qPochhammer_self_ne_zero hQ k
  have h := eval_termPolynomial_mul a q n k hkn
  have hT := (eq_div_iff ha).mpr h
  rw [hT]
  dsimp only [coefficient, seriesTerm]
  field_simp

/-- Interchanging the lengths in two successive shifted factorials. -/
theorem pochhammer_interchange (a q : ℂ) (m n : ℕ) :
    qPochhammer a q m * qPochhammer (a * q ^ m) q n =
      qPochhammer a q n * qPochhammer (a * q ^ n) q m := by
  rw [← qPochhammer_add, ← qPochhammer_add, Nat.add_comm]

/-- The sum polynomial has its prescribed value at one. -/
@[simp] theorem eval_sumPolynomial_one (b q : ℂ) (n : ℕ) :
    (sumPolynomial b q n).eval 1 = qPochhammer (-q) q n := by
  simp only [sumPolynomial, eval_finsetSum, eval_mul, eval_C]
  rw [sum_eq_single 0]
  · simp [coefficient]
  · intro k hk hk0
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    simp
  · simp

/-- The product polynomial has its prescribed value at one. -/
@[simp] theorem eval_valuePolynomial_one (b q : ℂ) (n : ℕ)
    (hb : qPochhammer b q n ≠ 0) :
    (valuePolynomial b q n).eval 1 = qPochhammer (-q) q n := by
  simp only [valuePolynomial, eval_mul, eval_C, eval_prod, eval_sub, eval_X]
  rw [← qPochhammer_eq_prod]
  exact div_mul_cancel₀ _ hb

/-- A root of the product polynomial at each of its displayed linear factors. -/
theorem eval_valuePolynomial_mul_pow (b q : ℂ) (n m : ℕ) (hm : m < n) :
    (valuePolynomial b q n).eval (b * q ^ m) = 0 := by
  simp only [valuePolynomial, eval_mul, eval_C, eval_prod, eval_sub, eval_X]
  rw [prod_eq_zero (mem_range.mpr hm) (by simp), mul_zero]

/-- The polynomial annihilated by the finite difference at a root of the product value. -/
def rootPolynomial (b q : ℂ) (n m : ℕ) : Polynomial ℂ :=
  DixonPolynomial.pochhammerPolynomial b q m *
    DixonPolynomial.pochhammerPolynomial (b ^ 2 * q ^ (2 * (m + 1)))
      (q ^ 2) (n - m - 1)

/-- The polynomial at a vanishing parameter has degree smaller than the difference order. -/
theorem natDegree_rootPolynomial_lt (b q : ℂ) (n m : ℕ) (hm : m < n) :
    (rootPolynomial b q n m).natDegree < n := by
  have h1 := natDegree_pochhammerPolynomial_le b q m
  have h2 := natDegree_pochhammerPolynomial_le (b ^ 2 * q ^ (2 * (m + 1)))
    (q ^ 2) (n - m - 1)
  have h3 := Polynomial.natDegree_mul_le
    (p := DixonPolynomial.pochhammerPolynomial b q m)
    (q := DixonPolynomial.pochhammerPolynomial (b ^ 2 * q ^ (2 * (m + 1)))
      (q ^ 2) (n - m - 1))
  dsimp [rootPolynomial]
  omega

/-- The finite series at a vanishing parameter is a finite difference after clearing constants. -/
theorem seriesTerm_root_mul {b q : ℂ} (hb : ‖b‖ < 1) (hq : ‖q‖ < 1)
    (n m k : ℕ) (hm : m < n) :
    seriesTerm (b * q ^ m) b q n k *
        (qPochhammer b q m *
          qPochhammer (b ^ 2 * q ^ (2 * (m + 1))) (q ^ 2) (n - m - 1)) =
      FiniteDifferencePolynomial.coefficient (q ^ 2) n k *
        (rootPolynomial b q n m).eval ((q ^ 2) ^ k) := by
  have hQ : ‖q ^ 2‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (by omega)
  have hB := pochhammer_ne_zero_of_norm_lt_one hb hq (2 * k)
  have hA : qPochhammer ((b * q ^ m) ^ 2 * q ^ 2) (q ^ 2) k ≠ 0 := by
    apply pochhammer_ne_zero_of_norm_lt_one _ hQ
    rw [← mul_pow]
    have h := DLMF.QSeries.norm_mul_pow_lt_one hb hq (m + 1)
    rw [pow_succ, ← mul_assoc] at h
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) h (by omega)
  have hqq := qPochhammer_self_ne_zero hQ k
  have h1 := pochhammer_interchange b q m (2 * k)
  have h2 := pochhammer_interchange (b ^ 2 * q ^ (2 * (m + 1)))
    (q ^ 2) (n - m - 1) k
  have hp : b ^ 2 * q ^ (2 * (m + 1)) * (q ^ 2) ^ (n - m - 1) =
      b ^ 2 * q ^ (2 * n) := by
    rw [← pow_mul, mul_assoc, ← pow_add]
    congr 2
    omega
  rw [hp] at h2
  have hpA : (b * q ^ m) ^ 2 * q ^ 2 = b ^ 2 * q ^ (2 * (m + 1)) := by
    rw [mul_pow, ← pow_mul]
    rw [mul_assoc, ← pow_add]
    congr 2
    omega
  simp only [rootPolynomial, eval_mul, DixonPolynomial.eval_pochhammerPolynomial]
  simp only [seriesTerm, FiniteDifferencePolynomial.coefficient]
  simp only [← pow_mul] at h2 ⊢
  rw [hpA] at hA ⊢
  field_simp
  linear_combination
    (qPochhammer ((q ^ 2) ^ (-(n : ℤ))) (q ^ 2) k * q ^ (2 * k)) *
      (congrArg₂ (fun x y : ℂ => x * y) h1 h2)

/-- Squared shifted parameters have nonvanishing finite factorials in the unit disk. -/
theorem pochhammer_squared_shift_ne_zero {b q : ℂ} (hb : ‖b‖ < 1) (hq : ‖q‖ < 1)
    (m r : ℕ) : qPochhammer (b ^ 2 * q ^ (2 * m)) (q ^ 2) r ≠ 0 := by
  apply pochhammer_ne_zero_of_norm_lt_one
  · rw [mul_comm 2 m, pow_mul, ← mul_pow, norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) (DLMF.QSeries.norm_mul_pow_lt_one hb hq m) (by omega)
  · rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hq (by omega)

/-- The finite series vanishes at each root of the product side. -/
theorem sum_seriesTerm_mul_pow_eq_zero {b q : ℂ} (hb : ‖b‖ < 1) (hq0 : q ≠ 0)
    (hq : ‖q‖ < 1) (n m : ℕ) (hm : m < n) :
    ∑ k ∈ range (n + 1), seriesTerm (b * q ^ m) b q n k = 0 := by
  have hQ : ‖q ^ 2‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (by omega)
  have hD : qPochhammer b q m *
      qPochhammer (b ^ 2 * q ^ (2 * (m + 1))) (q ^ 2) (n - m - 1) ≠ 0 :=
    mul_ne_zero (pochhammer_ne_zero_of_norm_lt_one hb hq m)
      (pochhammer_squared_shift_ne_zero hb hq (m + 1) _)
  apply (mul_eq_zero.mp (show
    (∑ k ∈ range (n + 1), seriesTerm (b * q ^ m) b q n k) *
      (qPochhammer b q m *
        qPochhammer (b ^ 2 * q ^ (2 * (m + 1))) (q ^ 2) (n - m - 1)) = 0 from ?_)).resolve_right hD
  rw [sum_mul]
  simp_rw [seriesTerm_root_mul hb hq n m _ hm]
  exact FiniteDifferencePolynomial.sum_eval_eq_zero_of_natDegree_lt (pow_ne_zero _ hq0) hQ
    (rootPolynomial b q n m) (natDegree_rootPolynomial_lt b q n m hm)

/-- The sum polynomial vanishes at each displayed root of the product polynomial. -/
theorem eval_sumPolynomial_mul_pow {b q : ℂ} (hb : ‖b‖ < 1) (hq0 : q ≠ 0)
    (hq : ‖q‖ < 1) (n m : ℕ) (hm : m < n) :
    (sumPolynomial b q n).eval (b * q ^ m) = 0 := by
  have hQ : ‖q ^ 2‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (by omega)
  have hA : qPochhammer ((b * q ^ m) ^ 2 * q ^ 2) (q ^ 2) n ≠ 0 := by
    apply pochhammer_ne_zero_of_norm_lt_one _ hQ
    rw [← mul_pow, norm_pow]
    have h := DLMF.QSeries.norm_mul_pow_lt_one hb hq (m + 1)
    rw [pow_succ, ← mul_assoc] at h
    exact pow_lt_one₀ (norm_nonneg _) h (by omega)
  rw [eval_sumPolynomial _ _ _ _ hq hA (pochhammer_ne_zero_of_norm_lt_one hb hq _),
    sum_seriesTerm_mul_pow_eq_zero hb hq0 hq n m hm, mul_zero]

/-- The interpolation nodes consist of one and the successive shifted parameters. -/
def interpolationPoint (b q : ℂ) : ℕ → ℂ
  | 0 => 1
  | m + 1 => b * q ^ m

/-- The interpolation nodes are distinct in the punctured open unit disk. -/
theorem injective_interpolationPoint {b q : ℂ} (hb0 : b ≠ 0) (hb : ‖b‖ < 1)
    (hq0 : q ≠ 0) (hq : ‖q‖ < 1) : Function.Injective (interpolationPoint b q) := by
  intro i j hij
  cases i with
  | zero =>
    cases j with
    | zero => rfl
    | succ j =>
      have h := DLMF.QSeries.norm_mul_pow_lt_one hb hq j
      change 1 = b * q ^ j at hij
      rw [← hij, norm_one] at h
      exact (lt_irrefl _ h).elim
  | succ i =>
    cases j with
    | zero =>
      have h := DLMF.QSeries.norm_mul_pow_lt_one hb hq i
      change b * q ^ i = 1 at hij
      rw [hij, norm_one] at h
      exact (lt_irrefl _ h).elim
    | succ j =>
      change b * q ^ i = b * q ^ j at hij
      have he : q ^ i = q ^ j := mul_left_cancel₀ hb0 hij
      have hn := congrArg norm he
      simp only [norm_pow] at hn
      have := (pow_right_strictAnti₀ (norm_pos_iff.mpr hq0) hq).injective hn
      omega

/-- Polynomial interpolation proves the first quadratic sum in the punctured unit disk. -/
theorem sumPolynomial_eq_valuePolynomial_of_norm_lt_one {b q : ℂ} (hb0 : b ≠ 0)
    (hb : ‖b‖ < 1) (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (n : ℕ) :
    sumPolynomial b q n = valuePolynomial b q n := by
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq (range (n + 1))
    (injective_interpolationPoint hb0 hb hq0 hq).injOn
  · apply Polynomial.degree_le_natDegree.trans_lt
    simp only [card_range]
    exact_mod_cast lt_of_le_of_lt (natDegree_sumPolynomial_le b q n) (Nat.lt_succ_self n)
  · apply Polynomial.degree_le_natDegree.trans_lt
    simp only [card_range]
    exact_mod_cast lt_of_le_of_lt (natDegree_valuePolynomial_le b q n) (Nat.lt_succ_self n)
  · intro i hi
    cases i with
    | zero =>
      simpa [interpolationPoint] using
        (eval_valuePolynomial_one b q n (pochhammer_ne_zero_of_norm_lt_one hb hq n)).symm
    | succ m =>
      have hm : m < n := by simp at hi; omega
      simp only [interpolationPoint, eval_sumPolynomial_mul_pow hb hq0 hq n m hm,
        eval_valuePolynomial_mul_pow b q n m hm]

/-- The first quadratic sum as a polynomial in its other parameter after clearing denominators. -/
def clearedSumPolynomial (a q : ℂ) (n : ℕ) : Polynomial ℂ :=
  ∑ k ∈ range (n + 1),
    C (qPochhammer ((q ^ 2) ^ (-(n : ℤ))) (q ^ 2) k /
      qPochhammer (q ^ 2) (q ^ 2) k * (q ^ 2) ^ k * (termPolynomial q n k).eval a) *
      (DixonPolynomial.pochhammerPolynomial (q ^ (2 * n)) (q ^ 2) k).comp (X ^ 2) *
      DixonPolynomial.pochhammerPolynomial (q ^ (2 * k)) q (2 * n - 2 * k)

/-- The product value as a polynomial in the remaining parameter. -/
def clearedValuePolynomial (a q : ℂ) (n : ℕ) : Polynomial ℂ :=
  C (qPochhammer (-q) q n) * (∏ j ∈ range n, (C a - X * C (q ^ j))) *
    DixonPolynomial.pochhammerPolynomial (q ^ n) q n

/-- Clearing the shifted factorial in the other parameter gives the polynomial sum. -/
theorem eval_clearedSumPolynomial (a b q : ℂ) (n : ℕ) (hq : ‖q‖ < 1)
    (hb : qPochhammer b q (2 * n) ≠ 0) :
    (clearedSumPolynomial a q n).eval b =
      qPochhammer b q (2 * n) * (sumPolynomial b q n).eval a := by
  have hQ : ‖q ^ 2‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (by omega)
  simp only [clearedSumPolynomial, sumPolynomial, eval_finsetSum, eval_mul, eval_C,
    Polynomial.eval_comp, eval_pow, eval_X, DixonPolynomial.eval_pochhammerPolynomial,
    mul_sum]
  apply sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by simp at hk; omega
  have hbk := qPochhammer_ne_zero_of_le hb (show 2 * k ≤ 2 * n by omega)
  have hqq := qPochhammer_self_ne_zero hQ k
  have h := qPochhammer_add b q (2 * k) (2 * n - 2 * k)
  rw [show 2 * k + (2 * n - 2 * k) = 2 * n by omega] at h
  rw [mul_comm (q ^ (2 * n)) (b ^ 2), mul_comm (q ^ (2 * k)) b]
  unfold coefficient
  field_simp
  linear_combination
    -(qPochhammer ((q ^ 2) ^ (-(n : ℤ))) (q ^ 2) k *
      qPochhammer (b ^ 2 * q ^ (2 * n)) (q ^ 2) k * (q ^ 2) ^ k *
      (termPolynomial q n k).eval a) * h

/-- Clearing the product denominator gives the polynomial product value. -/
theorem eval_clearedValuePolynomial (a b q : ℂ) (n : ℕ)
    (hb : qPochhammer b q (2 * n) ≠ 0) :
    (clearedValuePolynomial a q n).eval b =
      qPochhammer b q (2 * n) * (valuePolynomial b q n).eval a := by
  have hbn := qPochhammer_ne_zero_of_le hb (show n ≤ 2 * n by omega)
  have h := qPochhammer_add b q n n
  rw [← two_mul] at h
  simp only [clearedValuePolynomial, valuePolynomial, eval_mul, eval_C, eval_prod,
    eval_sub, eval_X, DixonPolynomial.eval_pochhammerPolynomial]
  rw [mul_comm (q ^ n) b, h]
  field_simp

/-- Polynomial continuation removes all restrictions on the remaining parameter. -/
theorem clearedSumPolynomial_eq_valuePolynomial {q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (a : ℂ) (n : ℕ) : clearedSumPolynomial a q n = clearedValuePolynomial a q n := by
  have hinj : Function.Injective (fun m : ℕ => q ^ (m + 1)) := by
    intro i j he
    have hn := congrArg norm he
    simp only [norm_pow] at hn
    have := (pow_right_strictAnti₀ (norm_pos_iff.mpr hq0) hq).injective hn
    omega
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective hinj).mono
  rintro b ⟨m, rfl⟩
  have hb : ‖q ^ (m + 1)‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hq (by omega)
  have hreg := pochhammer_ne_zero_of_norm_lt_one hb hq (2 * n)
  change (clearedSumPolynomial a q n).eval (q ^ (m + 1)) =
    (clearedValuePolynomial a q n).eval (q ^ (m + 1))
  rw [eval_clearedSumPolynomial _ _ _ _ hq hreg,
    eval_clearedValuePolynomial _ _ _ _ hreg,
    sumPolynomial_eq_valuePolynomial_of_norm_lt_one (pow_ne_zero _ hq0) hb hq0 hq]

/-- The first quadratic sum agrees with its product value at every regular parameter. -/
theorem eval_sumPolynomial_eq_valuePolynomial {q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (a b : ℂ) (n : ℕ) (hb : qPochhammer b q (2 * n) ≠ 0) :
    (sumPolynomial b q n).eval a = (valuePolynomial b q n).eval a := by
  have h := congrArg (Polynomial.eval b) (clearedSumPolynomial_eq_valuePolynomial hq0 hq a n)
  rw [eval_clearedSumPolynomial _ _ _ _ hq hb,
    eval_clearedValuePolynomial _ _ _ _ hb] at h
  exact mul_left_cancel₀ hb h

/-- The finite quadratic series equals its product at every regular terminating parameter. -/
theorem first_quadratic_sum {a b q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (n : ℕ)
    (hd : QDenominatorRegularThrough [b, b * q, a ^ 2 * q ^ 2] (q ^ 2) n) :
    qPhi [a, a * q, b ^ 2 * q ^ (2 * n), q ^ (-(2 * n : ℤ))]
        [b, b * q, a ^ 2 * q ^ 2] (q ^ 2) (q ^ 2) =
      qPochhammer (-q) q n * (∏ j ∈ range n, (a - b * q ^ j)) /
        qPochhammerList [-a * q, b] q n := by
  have hd' : qPochhammer b (q ^ 2) n * qPochhammer (b * q) (q ^ 2) n *
      qPochhammer (a ^ 2 * q ^ 2) (q ^ 2) n ≠ 0 := by
    simpa [QDenominatorRegularThrough, qPochhammerList, mul_assoc] using hd
  have hA := right_ne_zero_of_mul hd'
  have hB : qPochhammer b q (2 * n) ≠ 0 := by
    rw [qPochhammer_even]
    simpa [qPochhammerList] using left_ne_zero_of_mul hd'
  have hminus : qPochhammer (-a * q) q n ≠ 0 := by
    have h := hA
    rw [show a ^ 2 * q ^ 2 = (a * q) ^ 2 by ring, qPochhammer_squared] at h
    simpa only [neg_mul] using right_ne_zero_of_mul h
  have htrunc : qPhi [a, a * q, b ^ 2 * q ^ (2 * n), q ^ (-(2 * n : ℤ))]
        [b, b * q, a ^ 2 * q ^ 2] (q ^ 2) (q ^ 2) =
      ∑ k ∈ range (n + 1), seriesTerm a b q n k := by
    have hz : (q ^ 2) ^ (-(n : ℤ)) = q ^ (-(2 * n : ℤ)) := by
      rw [← zpow_natCast q 2, ← zpow_mul]
      congr 1
      ring
    unfold qPhi
    rw [tsum_eq_sum (s := range (n + 1)) (fun k hk => ?_)]
    · apply sum_congr rfl
      intro k _
      have he : qPhiExponent [a, a * q, b ^ 2 * q ^ (2 * n), q ^ (-(2 * n : ℤ))]
          [b, b * q, a ^ 2 * q ^ 2] = 0 := by simp [qPhiExponent]
      simp only [qPhiTerm, he, zpow_zero, mul_one]
      have hea := qPochhammer_even a q k
      have heb := qPochhammer_even b q k
      simp only [qPochhammerList, List.map_cons, List.map_nil, List.prod_cons,
        List.prod_nil, mul_one] at hea heb ⊢
      simp only [seriesTerm, hz]
      rw [hea, heb]
      ring
    · have hn : n < k := by simpa using hk
      have hz0 := qPochhammer_recip_pow_eq_zero (pow_ne_zero 2 hq0) hn
      have hzero : qPochhammer (q ^ (-(2 * n : ℤ))) (q ^ 2) k = 0 := by
        rw [← hz]
        simpa only [zpow_neg, zpow_natCast] using hz0
      simp only [qPhiTerm, qPochhammerList, List.map_cons, List.map_nil,
        List.prod_cons, List.prod_nil, hzero, mul_zero, zero_div, zero_mul]
  rw [htrunc]
  have he := eval_sumPolynomial_eq_valuePolynomial hq0 hq a b n hB
  rw [eval_sumPolynomial _ _ _ _ hq hA hB] at he
  simp only [valuePolynomial, eval_mul, eval_C, eval_prod, eval_sub, eval_X] at he
  have hbn := qPochhammer_ne_zero_of_le hB (show n ≤ 2 * n by omega)
  simp only [qPochhammerList, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one]
  apply (eq_div_iff (mul_ne_zero hminus hbn)).mpr
  field_simp at he
  simp only [neg_mul] at he ⊢
  linear_combination he

end DLMF.QHypergeometric.QuadraticSummation
