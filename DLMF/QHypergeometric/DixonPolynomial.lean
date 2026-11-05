/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QSeries.QBinomial
public import DLMF.QSeries.Basic.SeriesProperties
public import Mathlib.Algebra.Polynomial.Roots

/-!
# The polynomial form of Jackson's q-Dixon sum

The proof follows the parameter recurrence in V. J. W. Guo, *Elementary proofs of some
q-identities of Jackson and Andrews–Jain*, Discrete Mathematics 295 (2005), §2,
https://doi.org/10.1016/j.disc.2005.03.001. An antisymmetric odd sum gives the first parameter
value; the contiguous recurrence and polynomial uniqueness give the general identity.
All products are cleared, retaining their exceptional zeros.
-/

@[expose] public noncomputable section

open Complex Finset Polynomial
open DLMF.QSeries DLMF.QSeries.TripleProduct

namespace DLMF.QHypergeometric.DixonPolynomial

/-- The integral exponent in the symmetric terminating Dixon weight. -/
def exponent (n k : ℕ) : ℤ := (n : ℤ) * k - tri k

/-- The signed symmetric Dixon weight. -/
def weight (q : ℂ) (n k : ℕ) : ℂ := (-1) ^ k * q ^ exponent n k

/-- A polynomial shifted factorial in its free argument. -/
def pochhammerPolynomial (a q : ℂ) (n : ℕ) : Polynomial ℂ :=
  ∏ j ∈ range n, (1 - C a * X * C (q ^ j))

/-- Evaluation of the polynomial shifted factorial. -/
@[simp] theorem eval_pochhammerPolynomial (a q x : ℂ) (n : ℕ) :
    (pochhammerPolynomial a q n).eval x = qPochhammer (a * x) q n := by
  simp only [pochhammerPolynomial, eval_prod, eval_sub, eval_one, eval_mul, eval_C, eval_X,
    qPochhammer_eq_prod]

/-- The symmetric Dixon sum before inserting the second parameter. -/
def singleSum (b q : ℂ) (n : ℕ) : ℂ :=
  ∑ k ∈ range (2 * n + 1), weight q n k * qPochhammer b q k *
    qPochhammer b q (2 * n - k)

/-- The polynomial corresponding to the symmetric one-parameter sum. -/
def singleSumPolynomial (q : ℂ) (n : ℕ) : Polynomial ℂ :=
  ∑ k ∈ range (2 * n + 1), C (weight q n k) * pochhammerPolynomial 1 q k *
    pochhammerPolynomial 1 q (2 * n - k)

/-- The polynomial product corresponding to the one-parameter sum. -/
def singleValuePolynomial (q : ℂ) (n : ℕ) : Polynomial ℂ :=
  pochhammerPolynomial 1 q n * pochhammerPolynomial (q ^ (n + 1)) q n

/-- Evaluation of the polynomial one-parameter sum. -/
@[simp] theorem eval_singleSumPolynomial (b q : ℂ) (n : ℕ) :
    (singleSumPolynomial q n).eval b = singleSum b q n := by
  simp [singleSumPolynomial, singleSum, eval_finsetSum, mul_comm]

/-- Reflection in the odd length preserves the exponent. -/
theorem exponent_reflect (n k : ℕ) (hk : k ≤ 2 * n + 1) :
    exponent n (2 * n + 1 - k) = exponent n k := by
  have h0 := tri_mul_two (k : ℤ)
  have h1 := tri_mul_two ((2 * n + 1 - k : ℕ) : ℤ)
  have he : ((2 * n + 1 - k : ℕ) : ℤ) = 2 * (n : ℤ) + 1 - k := by omega
  rw [he] at h1
  dsimp [exponent]
  rw [he]
  nlinarith

/-- Reflection in the odd length reverses the signed weight. -/
theorem weight_reflect (q : ℂ) (n k : ℕ) (hk : k ≤ 2 * n + 1) :
    weight q n (2 * n + 1 - k) = -weight q n k := by
  rw [weight, exponent_reflect n k hk]
  have hs : (-1 : ℂ) ^ (2 * n + 1 - k) = -(-1 : ℂ) ^ k := by
    rw [pow_sub₀ (-1 : ℂ) (by norm_num) hk]
    simp [pow_succ, pow_mul]
    rw [← inv_pow]
    norm_num
  rw [hs, weight]
  ring

/-- The full odd sum cancels by reflection. -/
theorem odd_sum_eq_zero (b q : ℂ) (n : ℕ) :
    ∑ k ∈ range (2 * n + 2), weight q n k * qPochhammer b q k *
      qPochhammer b q (2 * n + 1 - k) = 0 := by
  let f := fun k => weight q n k * qPochhammer b q k *
    qPochhammer b q (2 * n + 1 - k)
  have h : ∑ k ∈ range (2 * n + 2), f k = -∑ k ∈ range (2 * n + 2), f k := by
    calc
      _ = ∑ k ∈ range (2 * n + 2), f (2 * n + 2 - 1 - k) :=
        (sum_range_reflect f (2 * n + 2)).symm
      _ = _ := by
        rw [← sum_neg_distrib]
        refine sum_congr rfl fun k hk => ?_
        have hk' : k ≤ 2 * n + 1 := by simp at hk; omega
        dsimp [f]
        rw [weight_reflect q n k hk', show 2 * n + 1 - (2 * n + 1 - k) = k by omega]
        ring
  change (∑ k ∈ range (2 * n + 2), f k) = 0
  linear_combination h / 2

/-- The exponent increases by `n-k` at the next index. -/
theorem exponent_succ (n k : ℕ) :
    exponent n (k + 1) = exponent n k + n - k := by
  have h0 := tri_mul_two (k : ℤ)
  have h1 := tri_mul_two ((k : ℤ) + 1)
  simp only [exponent, Nat.cast_add, Nat.cast_one]
  nlinarith

/-- The adjacent symmetric weights, with nonnegative powers on both sides. -/
theorem pow_mul_weight_succ {q : ℂ} (hq0 : q ≠ 0) (n k : ℕ) (hk : k ≤ 2 * n) :
    q ^ n * weight q n (k + 1) = -q ^ (2 * n - k) * weight q n k := by
  have he : (n : ℤ) + exponent n (k + 1) =
      ((2 * n - k : ℕ) : ℤ) + exponent n k := by
    rw [exponent_succ]
    have : ((2 * n - k : ℕ) : ℤ) = 2 * (n : ℤ) - k := by omega
    rw [this]
    ring
  simp only [weight, pow_succ]
  rw [show q ^ n * ((-1 : ℂ) ^ k * -1 * q ^ exponent n (k + 1)) =
      -((-1 : ℂ) ^ k * (q ^ (n : ℤ) * q ^ exponent n (k + 1))) by
        simp only [zpow_natCast]; ring,
    ← zpow_add₀ hq0, he, zpow_add₀ hq0, zpow_natCast]
  ring

/-- The odd summand whose reflection changes its sign. -/
def oddTerm (b q : ℂ) (n k : ℕ) : ℂ :=
  weight q n k * qPochhammer b q k * qPochhammer b q (2 * n + 1 - k)

/-- The single-parameter summand is an adjacent difference of odd summands. -/
theorem singleTerm_mul (b : ℂ) {q : ℂ} (hq0 : q ≠ 0) (n k : ℕ) (hk : k ≤ 2 * n) :
    (1 - b ^ 2 * q ^ (2 * n)) *
        (weight q n k * qPochhammer b q k * qPochhammer b q (2 * n - k)) =
      oddTerm b q n k - b * q ^ n * oddTerm b q n (k + 1) := by
  have hw := pow_mul_weight_succ hq0 n k hk
  have hp : q ^ (2 * n - k) * q ^ k = q ^ (2 * n) := by
    rw [← pow_add]
    congr 1
    omega
  simp only [oddTerm]
  rw [show 2 * n + 1 - k = (2 * n - k) + 1 by omega,
    show 2 * n + 1 - (k + 1) = 2 * n - k by omega,
    qPochhammer_succ, qPochhammer_succ]
  linear_combination
    (b * qPochhammer b q k * (1 - b * q ^ k) * qPochhammer b q (2 * n - k)) * hw +
      (b ^ 2 * weight q n k * qPochhammer b q k * qPochhammer b q (2 * n - k)) * hp

/-- Multiplying the single-parameter sum by its removable factors gives a shifted factorial. -/
theorem singleSum_mul (b : ℂ) {q : ℂ} (hq0 : q ≠ 0) (n : ℕ) :
    (1 - b ^ 2 * q ^ (2 * n)) * singleSum b q n =
      (1 + b * q ^ n) * qPochhammer b q (2 * n + 1) := by
  have hw0 : weight q n 0 = 1 := by simp [weight, exponent, tri]
  have hwl : weight q n (2 * n + 1) = -1 := by
    simpa only [Nat.sub_zero, hw0] using weight_reflect q n 0 (by omega)
  have hodd : ∑ k ∈ range (2 * n + 2), oddTerm b q n k = 0 := odd_sum_eq_zero b q n
  have hfirst : ∑ k ∈ range (2 * n + 1), oddTerm b q n k =
      qPochhammer b q (2 * n + 1) := by
    rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega, sum_range_succ] at hodd
    simp only [oddTerm, hwl, Nat.sub_self, qPochhammer_zero, mul_one, neg_one_mul] at hodd
    dsimp [oddTerm]
    linear_combination hodd
  have hshift : ∑ k ∈ range (2 * n + 1), oddTerm b q n (k + 1) =
      -qPochhammer b q (2 * n + 1) := by
    rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega, sum_range_succ'] at hodd
    simp only [oddTerm, hw0, qPochhammer_zero, one_mul, Nat.sub_zero] at hodd
    dsimp [oddTerm]
    linear_combination hodd
  rw [singleSum, mul_sum]
  rw [sum_congr rfl (fun k hk => singleTerm_mul b hq0 n k (by simp at hk; omega)),
    sum_sub_distrib, ← mul_sum, hfirst, hshift]
  ring

/-- The symmetric single-parameter sum has its product value even at removable zeros. -/
theorem singleSum_eq_product (b : ℂ) {q : ℂ} (hq0 : q ≠ 0) (n : ℕ) :
    singleSum b q n = qPochhammer b q n * qPochhammer (b * q ^ (n + 1)) q n := by
  let D : Polynomial ℂ := 1 - C (q ^ (2 * n)) * X ^ 2
  have hD : D ≠ 0 := by
    intro he
    have h := congrArg (Polynomial.eval 0) he
    simp [D] at h
  have he : D * singleSumPolynomial q n = D * singleValuePolynomial q n := by
    apply Polynomial.funext
    intro x
    have h := singleSum_mul x hq0 n
    have hs : qPochhammer x q (2 * n + 1) =
        (1 - x * q ^ n) * qPochhammer x q n * qPochhammer (x * q ^ (n + 1)) q n := by
      rw [show 2 * n + 1 = n + (n + 1) by omega, qPochhammer_add,
        qPochhammer_succ', show x * q ^ n * q = x * q ^ (n + 1) by ring]
      ring
    rw [hs, show q ^ (2 * n) = q ^ n * q ^ n by rw [two_mul, pow_add]] at h
    simp only [eval_mul, eval_sub, eval_one, eval_C, eval_pow, eval_X, D,
      eval_singleSumPolynomial, singleValuePolynomial, eval_pochhammerPolynomial, one_mul]
    rw [show q ^ (2 * n) = q ^ n * q ^ n by rw [two_mul, pow_add]]
    simp only [mul_comm (q ^ (n + 1)) x]
    linear_combination h
  have hpol := mul_left_cancel₀ hD he
  have hv := congrArg (Polynomial.eval b) hpol
  simpa [singleValuePolynomial, mul_comm] using hv

/-- The paired shifted factorials in a symmetric finite sum. -/
def pair (b q : ℂ) (N k : ℕ) : ℂ := qPochhammer b q k * qPochhammer b q (N - k)

/-- The cleared polynomial form of the terminating q-Dixon sum. -/
def clearedSum (b c q : ℂ) (n : ℕ) : ℂ :=
  ∑ k ∈ range (2 * n + 1), qBinom q (2 * n) k * weight q n k *
    pair b q (2 * n) k * pair c q (2 * n) k

/-- The cleared product value of the terminating q-Dixon sum. -/
def clearedValue (b c q : ℂ) (n : ℕ) : ℂ :=
  qPochhammer b q n * qPochhammer c q n * qPochhammer (q ^ (n + 1)) q n *
    qPochhammer (b * c * q ^ n) q n

/-- A shifted factorial with the initial factor moved to the other end. -/
theorem one_sub_mul_pochhammer_shift (b q : ℂ) (k : ℕ) :
    (1 - b) * qPochhammer (b * q) q k =
      (1 - b * q ^ k) * qPochhammer b q k := by
  rw [← qPochhammer_succ', qPochhammer_succ]
  ring

/-- The corresponding shift of two paired factorials. -/
theorem one_sub_sq_mul_pair_shift (b q : ℂ) (N k : ℕ) :
    (1 - b) ^ 2 * pair (b * q) q N k =
      (1 - b * q ^ k) * (1 - b * q ^ (N - k)) * pair b q N k := by
  dsimp [pair]
  linear_combination
    ((1 - b) * qPochhammer (b * q) q (N - k)) * one_sub_mul_pochhammer_shift b q k +
      ((1 - b * q ^ k) * qPochhammer b q k) *
        one_sub_mul_pochhammer_shift b q (N - k)

/-- The termwise parameter recurrence of the symmetric Dixon sum. -/
theorem clearedTerm_contiguous (b c q : ℂ) (n k : ℕ) (hk : k ≤ 2 * n) :
    b * (1 - c) ^ 2 * (qBinom q (2 * n) k * weight q n k *
        pair b q (2 * n) k * pair (c * q) q (2 * n) k) =
      (b - c) * (1 - b * c * q ^ (2 * n)) *
        (qBinom q (2 * n) k * weight q n k * pair b q (2 * n) k * pair c q (2 * n) k) +
      c * (1 - b) ^ 2 * (qBinom q (2 * n) k * weight q n k *
        pair (b * q) q (2 * n) k * pair c q (2 * n) k) := by
  have hp : q ^ k * q ^ (2 * n - k) = q ^ (2 * n) := by
    rw [← pow_add]
    congr 1
    omega
  have hc := one_sub_sq_mul_pair_shift c q (2 * n) k
  have hb := one_sub_sq_mul_pair_shift b q (2 * n) k
  have he : b * (1 - c * q ^ k) * (1 - c * q ^ (2 * n - k)) =
      (b - c) * (1 - b * c * q ^ (2 * n)) +
        c * (1 - b * q ^ k) * (1 - b * q ^ (2 * n - k)) := by
    linear_combination -(b * c * (b - c)) * hp
  linear_combination
    (b * qBinom q (2 * n) k * weight q n k * pair b q (2 * n) k) * hc -
    (c * qBinom q (2 * n) k * weight q n k * pair c q (2 * n) k) * hb +
    (qBinom q (2 * n) k * weight q n k * pair b q (2 * n) k * pair c q (2 * n) k) * he

/-- The parameter recurrence for the finite sum. -/
theorem clearedSum_contiguous (b c q : ℂ) (n : ℕ) :
    b * (1 - c) ^ 2 * clearedSum b (c * q) q n =
      (b - c) * (1 - b * c * q ^ (2 * n)) * clearedSum b c q n +
        c * (1 - b) ^ 2 * clearedSum (b * q) c q n := by
  simp only [clearedSum, mul_sum, ← sum_add_distrib]
  exact sum_congr rfl fun k hk => clearedTerm_contiguous b c q n k (by simp at hk; omega)

/-- The closed product has the same parameter recurrence. -/
theorem clearedValue_contiguous (b c q : ℂ) (n : ℕ) :
    b * (1 - c) ^ 2 * clearedValue b (c * q) q n =
      (b - c) * (1 - b * c * q ^ (2 * n)) * clearedValue b c q n +
        c * (1 - b) ^ 2 * clearedValue (b * q) c q n := by
  cases n with
  | zero => simp only [clearedValue, qPochhammer_zero, mul_one, Nat.mul_zero, pow_zero]; ring
  | succ m =>
    have hc := one_sub_mul_pochhammer_shift c q (m + 1)
    have hb := one_sub_mul_pochhammer_shift b q (m + 1)
    have he0 : b * (c * q) * q ^ (m + 1) = b * c * q ^ (m + 2) := by ring
    have he1 : b * q * c * q ^ (m + 1) = b * c * q ^ (m + 2) := by ring
    have he2 : b * c * q ^ (m + 1) * q = b * c * q ^ (m + 2) := by ring
    have he3 : b * c * q ^ (m + 2) * q ^ m = b * c * q ^ (2 * (m + 1)) := by
      rw [mul_assoc, ← pow_add]
      congr 2
      omega
    simp only [clearedValue, he0, he1]
    rw [qPochhammer_succ' (b * c * q ^ (m + 1)) q m, he2,
      qPochhammer_succ (b * c * q ^ (m + 2)) q m, he3]
    linear_combination
      (b * (1 - c) * qPochhammer b q (m + 1) *
        qPochhammer (q ^ (m + 1 + 1)) q (m + 1) *
        qPochhammer (b * c * q ^ (m + 2)) q m *
        (1 - b * c * q ^ (2 * (m + 1)))) * hc -
      (c * (1 - b) * qPochhammer c q (m + 1) *
        qPochhammer (q ^ (m + 1 + 1)) q (m + 1) *
        qPochhammer (b * c * q ^ (m + 2)) q m *
        (1 - b * c * q ^ (2 * (m + 1)))) * hb

/-- At second parameter `q`, the Gaussian coefficient cancels and the odd-sum identity applies. -/
theorem clearedSum_self {q : ℂ} (hq0 : q ≠ 0) (b : ℂ) (n : ℕ) :
    clearedSum b q q n = clearedValue b q q n := by
  have hterm (k : ℕ) (hk : k ∈ range (2 * n + 1)) :
      qBinom q (2 * n) k * weight q n k * pair b q (2 * n) k * pair q q (2 * n) k =
        qPochhammer q q (2 * n) *
          (weight q n k * qPochhammer b q k * qPochhammer b q (2 * n - k)) := by
    have hk' : k ≤ 2 * n := by simp at hk; omega
    have h := qBinom_mul_qPochhammer q k (2 * n - k)
    rw [Nat.add_sub_cancel' hk'] at h
    dsimp [pair]
    linear_combination (weight q n k * qPochhammer b q k *
      qPochhammer b q (2 * n - k)) * h
  have hq : qPochhammer q q (2 * n) =
      qPochhammer q q n * qPochhammer (q ^ (n + 1)) q n := by
    rw [two_mul, qPochhammer_add,
      show q * q ^ n = q ^ (n + 1) by rw [pow_succ]; ring]
  rw [clearedSum, sum_congr rfl hterm, ← mul_sum]
  change qPochhammer q q (2 * n) * singleSum b q n = _
  rw [singleSum_eq_product b hq0, hq]
  dsimp [clearedValue]
  rw [show b * q * q ^ n = b * q ^ (n + 1) by ring]
  ring

/-- The finite Dixon sum as a polynomial in the second parameter. -/
def sumPolynomial (b q : ℂ) (n : ℕ) : Polynomial ℂ :=
  ∑ k ∈ range (2 * n + 1), C (qBinom q (2 * n) k * weight q n k * pair b q (2 * n) k) *
    pochhammerPolynomial 1 q k * pochhammerPolynomial 1 q (2 * n - k)

/-- The Dixon product as a polynomial in the second parameter. -/
def valuePolynomial (b q : ℂ) (n : ℕ) : Polynomial ℂ :=
  C (qPochhammer b q n * qPochhammer (q ^ (n + 1)) q n) *
    pochhammerPolynomial 1 q n * pochhammerPolynomial (b * q ^ n) q n

/-- Evaluation of the polynomial finite Dixon sum. -/
@[simp] theorem eval_sumPolynomial (b c q : ℂ) (n : ℕ) :
    (sumPolynomial b q n).eval c = clearedSum b c q n := by
  simp [sumPolynomial, clearedSum, pair, eval_finsetSum, mul_assoc]

/-- Evaluation of the polynomial Dixon product. -/
@[simp] theorem eval_valuePolynomial (b c q : ℂ) (n : ℕ) :
    (valuePolynomial b q n).eval c = clearedValue b c q n := by
  simp [valuePolynomial, clearedValue, mul_comm, mul_left_comm, mul_assoc]

/-- The finite Dixon identity at every positive integral power of the base. -/
theorem clearedSum_pow_succ {q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (n m : ℕ) :
    ∀ b : ℂ, b ≠ 0 → clearedSum b (q ^ (m + 1)) q n =
      clearedValue b (q ^ (m + 1)) q n := by
  induction m with
  | zero => intro b _; simpa only [zero_add, pow_one] using clearedSum_self hq0 b n
  | succ m ih =>
    intro b hb
    have hsum := clearedSum_contiguous b (q ^ (m + 1)) q n
    have hvalue := clearedValue_contiguous b (q ^ (m + 1)) q n
    rw [ih b hb, ih (b * q) (mul_ne_zero hb hq0)] at hsum
    have hqn : q ^ (m + 1) ≠ 1 := by
      intro he
      have ht : ‖q ^ (m + 1)‖ < 1 := by
        rw [norm_pow]
        exact pow_lt_one₀ (norm_nonneg q) hq (by omega)
      rw [he, norm_one] at ht
      exact lt_irrefl _ ht
    have hcoef : b * (1 - q ^ (m + 1)) ^ 2 ≠ 0 :=
      mul_ne_zero hb (pow_ne_zero _ (sub_ne_zero.mpr hqn.symm))
    rw [← pow_succ] at hsum hvalue
    exact mul_left_cancel₀ hcoef (hsum.trans hvalue.symm)

/-- Jackson's polynomial q-Dixon identity, with no restrictions on zeros of its products. -/
theorem clearedSum_eq_value {b q : ℂ} (hb : b ≠ 0) (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (c : ℂ) (n : ℕ) : clearedSum b c q n = clearedValue b c q n := by
  have hinj : Function.Injective (fun m : ℕ => q ^ (m + 1)) := by
    intro i j he
    have he' : ‖q‖ ^ (i + 1) = ‖q‖ ^ (j + 1) := by
      simpa only [norm_pow] using congrArg norm he
    have h := (pow_right_strictAnti₀ (norm_pos_iff.mpr hq0) hq).injective he'
    omega
  have hinf : Set.Infinite (Set.range (fun m : ℕ => q ^ (m + 1))) :=
    Set.infinite_range_of_injective hinj
  have hp : sumPolynomial b q n = valuePolynomial b q n := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply hinf.mono
    rintro x ⟨m, rfl⟩
    simpa only [Set.mem_ofPred_eq, eval_sumPolynomial, eval_valuePolynomial] using
      clearedSum_pow_succ hq0 hq n m b hb
  have he := congrArg (Polynomial.eval c) hp
  simpa only [eval_sumPolynomial, eval_valuePolynomial] using he

end DLMF.QHypergeometric.DixonPolynomial
