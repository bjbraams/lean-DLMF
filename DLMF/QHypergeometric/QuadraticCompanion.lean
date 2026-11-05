/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.QuadraticSummation
public import DLMF.QHypergeometric.PfaffSaalschutz

/-!
# The companion balanced quadratic summation

Polynomial interpolation gives the companion base-square sum of DLMF 17.7.13.
The finite q-difference method follows X. Wang and W. Chu, *Approach of q-Derivative
Operators to Terminating q-Series Formulae*, Communications in Mathematics 26 (2018),
§4, https://doi.org/10.2478/cm-2018-0007.
-/

@[expose] public noncomputable section

open Complex Finset Polynomial
open DLMF.QSeries

namespace DLMF.QHypergeometric.QuadraticCompanion

open QuadraticSummation

/-- The polynomial remaining after cancellation of the squared lower parameter. -/
def termPolynomial (q : ℂ) (n k : ℕ) : Polynomial ℂ :=
  DixonPolynomial.pochhammerPolynomial (q ^ k) q k *
    DixonPolynomial.pochhammerPolynomial (-q ^ k) q (n - k)

/-- The coefficients independent of the interpolated parameter. -/
def coefficient (b q : ℂ) (n k : ℕ) : ℂ :=
  qPochhammer ((q ^ 2) ^ (-(n : ℤ))) (q ^ 2) k *
    qPochhammer (b ^ 2 * q ^ (2 * (n - 1))) (q ^ 2) k /
      (qPochhammer b q (2 * k) * qPochhammer (q ^ 2) (q ^ 2) k) * (q ^ 2) ^ k

/-- The first balanced quadratic sum after clearing its parameter-dependent denominator. -/
def sumPolynomial (b q : ℂ) (n : ℕ) : Polynomial ℂ :=
  ∑ k ∈ range (n + 1), C (coefficient b q n k) * termPolynomial q n k

/-- The product value after clearing the parameter-dependent denominator. -/
def valuePolynomial (b q : ℂ) (n : ℕ) : Polynomial ℂ :=
  C (qPochhammer (-q) q n * (1 - b * q ^ (n - 1)) /
    (qPochhammer b q n * (1 - b * q ^ (2 * n - 1)))) *
    ∏ j ∈ range n, (X - C (b * q ^ j))


/-- The cancellation polynomial has degree at most its truncation index. -/
theorem natDegree_termPolynomial_le (q : ℂ) (n k : ℕ) (hk : k ≤ n) :
    (termPolynomial q n k).natDegree ≤ n := by
  have h1 := natDegree_pochhammerPolynomial_le (q ^ k) q k
  have h2 := natDegree_pochhammerPolynomial_le (-q ^ k) q (n - k)
  have h3 := Polynomial.natDegree_mul_le
    (p := DixonPolynomial.pochhammerPolynomial (q ^ k) q k)
    (q := DixonPolynomial.pochhammerPolynomial (-q ^ k) q (n - k))
  dsimp [termPolynomial]
  omega

/-- Evaluation of the polynomial left after cancellation. -/
@[simp] theorem eval_termPolynomial (a q : ℂ) (n k : ℕ) :
    (termPolynomial q n k).eval a =
      qPochhammer (a * q ^ k) q k * qPochhammer (-a * q ^ k) q (n - k) := by
  simp [termPolynomial, mul_comm]

/-- Clearing the squared lower parameter recovers the original term. -/
theorem eval_termPolynomial_mul (a q : ℂ) (n k : ℕ) (hk : k ≤ n) :
    (termPolynomial q n k).eval a * qPochhammer (a ^ 2) (q ^ 2) k =
      qPochhammer a q (2 * k) * qPochhammer (-a) q n := by
  have hA : qPochhammer a q (2 * k) =
      qPochhammer a q k * qPochhammer (a * q ^ k) q k := by
    rw [two_mul, qPochhammer_add]
  have hB := qPochhammer_add (-a) q k (n - k)
  rw [Nat.add_sub_cancel' hk] at hB
  rw [eval_termPolynomial, qPochhammer_squared, hA, hB]
  ring

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

/-- The finite summand before cancellation. -/
def seriesTerm (a b q : ℂ) (n k : ℕ) : ℂ :=
  qPochhammer ((q ^ 2) ^ (-(n : ℤ))) (q ^ 2) k * qPochhammer a q (2 * k) *
    qPochhammer (b ^ 2 * q ^ (2 * (n - 1))) (q ^ 2) k /
      (qPochhammer (a ^ 2) (q ^ 2) k * qPochhammer b q (2 * k) *
        qPochhammer (q ^ 2) (q ^ 2) k) * (q ^ 2) ^ k

/-- The polynomial and finite series agree after multiplying by the removable factor. -/
theorem eval_sumPolynomial (a b q : ℂ) (n : ℕ) (hq : ‖q‖ < 1)
    (hA : qPochhammer (a ^ 2) (q ^ 2) n ≠ 0)
    (hB : qPochhammer b q (2 * n) ≠ 0) :
    (sumPolynomial b q n).eval a =
      qPochhammer (-a) q n * ∑ k ∈ range (n + 1), seriesTerm a b q n k := by
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

/-- The polynomial annihilated by the finite difference at a root of the product value. -/
def rootPolynomial (b q : ℂ) (n m : ℕ) : Polynomial ℂ :=
  DixonPolynomial.pochhammerPolynomial b q m *
    DixonPolynomial.pochhammerPolynomial (b ^ 2 * q ^ (2 * m))
      (q ^ 2) (n - m - 1)

/-- The polynomial at a vanishing parameter has degree smaller than the difference order. -/
theorem natDegree_rootPolynomial_lt (b q : ℂ) (n m : ℕ) (hm : m < n) :
    (rootPolynomial b q n m).natDegree < n := by
  have h1 := natDegree_pochhammerPolynomial_le b q m
  have h2 := natDegree_pochhammerPolynomial_le (b ^ 2 * q ^ (2 * m))
    (q ^ 2) (n - m - 1)
  have h3 := Polynomial.natDegree_mul_le
    (p := DixonPolynomial.pochhammerPolynomial b q m)
    (q := DixonPolynomial.pochhammerPolynomial (b ^ 2 * q ^ (2 * m))
      (q ^ 2) (n - m - 1))
  dsimp [rootPolynomial]
  omega

/-- The finite series at a vanishing parameter is a finite difference after clearing constants. -/
theorem seriesTerm_root_mul {b q : ℂ} (hb : ‖b‖ < 1) (hq : ‖q‖ < 1)
    (n m k : ℕ) (hm : m < n) :
    seriesTerm (b * q ^ m) b q n k *
        (qPochhammer b q m *
          qPochhammer (b ^ 2 * q ^ (2 * m)) (q ^ 2) (n - m - 1)) =
      FiniteDifferencePolynomial.coefficient (q ^ 2) n k *
        (rootPolynomial b q n m).eval ((q ^ 2) ^ k) := by
  have hQ : ‖q ^ 2‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (by omega)
  have hB := pochhammer_ne_zero_of_norm_lt_one hb hq (2 * k)
  have hA : qPochhammer ((b * q ^ m) ^ 2) (q ^ 2) k ≠ 0 := by
    apply pochhammer_ne_zero_of_norm_lt_one _ hQ
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) (DLMF.QSeries.norm_mul_pow_lt_one hb hq m) (by omega)
  have hqq := qPochhammer_self_ne_zero hQ k
  have h1 := pochhammer_interchange b q m (2 * k)
  have h2 := pochhammer_interchange (b ^ 2 * q ^ (2 * m))
    (q ^ 2) (n - m - 1) k
  have hp : b ^ 2 * q ^ (2 * m) * (q ^ 2) ^ (n - m - 1) =
      b ^ 2 * q ^ (2 * (n - 1)) := by
    rw [← pow_mul, mul_assoc, ← pow_add]
    congr 2
    omega
  rw [hp] at h2
  have hpA : (b * q ^ m) ^ 2 = b ^ 2 * q ^ (2 * m) := by
    rw [mul_pow, ← pow_mul, Nat.mul_comm m 2]
  simp only [rootPolynomial, eval_mul, DixonPolynomial.eval_pochhammerPolynomial]
  simp only [seriesTerm, FiniteDifferencePolynomial.coefficient]
  simp only [← pow_mul] at h2 ⊢
  rw [hpA] at hA ⊢
  field_simp
  linear_combination
    (qPochhammer ((q ^ 2) ^ (-(n : ℤ))) (q ^ 2) k * q ^ (2 * k)) *
      (congrArg₂ (fun x y : ℂ => x * y) h1 h2)

/-- The finite series vanishes at each root of the product side. -/
theorem sum_seriesTerm_mul_pow_eq_zero {b q : ℂ} (hb : ‖b‖ < 1) (hq0 : q ≠ 0)
    (hq : ‖q‖ < 1) (n m : ℕ) (hm : m < n) :
    ∑ k ∈ range (n + 1), seriesTerm (b * q ^ m) b q n k = 0 := by
  have hQ : ‖q ^ 2‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (by omega)
  have hD : qPochhammer b q m *
      qPochhammer (b ^ 2 * q ^ (2 * m)) (q ^ 2) (n - m - 1) ≠ 0 :=
    mul_ne_zero (pochhammer_ne_zero_of_norm_lt_one hb hq m)
      (pochhammer_squared_shift_ne_zero hb hq m _)
  apply (mul_eq_zero.mp (show
    (∑ k ∈ range (n + 1), seriesTerm (b * q ^ m) b q n k) *
      (qPochhammer b q m *
        qPochhammer (b ^ 2 * q ^ (2 * m)) (q ^ 2) (n - m - 1)) = 0 from ?_)).resolve_right hD
  rw [sum_mul]
  simp_rw [seriesTerm_root_mul hb hq n m _ hm]
  exact FiniteDifferencePolynomial.sum_eval_eq_zero_of_natDegree_lt (pow_ne_zero _ hq0) hQ
    (rootPolynomial b q n m) (natDegree_rootPolynomial_lt b q n m hm)

/-- The sum polynomial vanishes at each displayed root of the product polynomial. -/
theorem eval_sumPolynomial_mul_pow {b q : ℂ} (hb : ‖b‖ < 1) (hq0 : q ≠ 0)
    (hq : ‖q‖ < 1) (n m : ℕ) (hm : m < n) :
    (sumPolynomial b q n).eval (b * q ^ m) = 0 := by
  have hQ : ‖q ^ 2‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (by omega)
  have hA : qPochhammer ((b * q ^ m) ^ 2) (q ^ 2) n ≠ 0 := by
    apply pochhammer_ne_zero_of_norm_lt_one _ hQ
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) (DLMF.QSeries.norm_mul_pow_lt_one hb hq m) (by omega)
  rw [eval_sumPolynomial _ _ _ _ hq hA (pochhammer_ne_zero_of_norm_lt_one hb hq _),
    sum_seriesTerm_mul_pow_eq_zero hb hq0 hq n m hm, mul_zero]


/-- The normalizing finite balanced sum is evaluated at `a = q`. -/
theorem sum_seriesTerm_base_eq {b q : ℂ} (hb0 : b ≠ 0) (hb : ‖b‖ < ‖q‖)
    (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (N : ℕ) :
    ∑ k ∈ range (N + 1 + 1), seriesTerm q b q (N + 1) k =
      q ^ (N + 1) * (1 - b / q) / (1 - b * q ^ (2 * N + 1)) := by
  have hb1 := hb.trans hq
  have hQ : ‖q ^ 2‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (by omega)
  have hC := pochhammer_ne_zero_of_norm_lt_one hb1 hQ (N + 1)
  have hCq := pochhammer_ne_zero_of_norm_lt_one
    (DLMF.QSeries.norm_mul_pow_lt_one hb1 hq 1) hQ (N + 1)
  simp only [pow_one] at hCq
  have hbal : q * (b ^ 2 * q ^ (2 * N)) * (q ^ 2) ^ (1 - ((N + 1 : ℕ) : ℤ)) / b =
      b * q := by
    rw [show 1 - ((N + 1 : ℕ) : ℤ) = -(N : ℤ) by omega]
    simp only [zpow_neg, zpow_natCast, ← pow_mul]
    field_simp
  have hS := PfaffSaalschutz.sum_eq_quotient_of_ne_zero hq0
    (mul_ne_zero (pow_ne_zero 2 hb0) (pow_ne_zero _ hq0)) hb0 (pow_ne_zero 2 hq0) hQ
    (N + 1) (by rw [hbal]; exact hCq) hC
  have ht : ∀ k ∈ range (N + 1 + 1), seriesTerm q b q (N + 1) k =
      qPochhammer q (q ^ 2) k * qPochhammer (b ^ 2 * q ^ (2 * N)) (q ^ 2) k *
        qPochhammer ((q ^ 2) ^ (-((N + 1 : ℕ) : ℤ))) (q ^ 2) k /
          (qPochhammer b (q ^ 2) k * qPochhammer (b * q) (q ^ 2) k *
            qPochhammer (q ^ 2) (q ^ 2) k) * (q ^ 2) ^ k := by
    intro k hk
    have hkn : k ≤ N + 1 := by simp at hk; omega
    have hqq := qPochhammer_self_ne_zero hQ k
    have hbk := qPochhammer_ne_zero_of_le hC hkn
    have hbqk := qPochhammer_ne_zero_of_le hCq hkn
    have hE := qPochhammer_even q q k
    have hB := qPochhammer_even b q k
    simp only [qPochhammerList, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one] at hE hB
    simp only [seriesTerm, Nat.add_sub_cancel]
    rw [hE, hB]
    field_simp
  rw [sum_congr rfl ht]
  rw [hbal] at hS
  rw [hS]
  let u : ℂ := (q ^ 2) ^ (-(N : ℤ)) / b
  let v : ℂ := (q ^ 2) ^ (-(N : ℤ)) / (b * q)
  have hu : u ≠ 0 := div_ne_zero (zpow_ne_zero _ (pow_ne_zero _ hq0)) hb0
  have hv : v ≠ 0 := div_ne_zero (zpow_ne_zero _ (pow_ne_zero _ hq0)) (mul_ne_zero hb0 hq0)
  have huarg : b / (b ^ 2 * q ^ (2 * N)) = u := by
    dsimp [u]
    simp only [zpow_neg, zpow_natCast, ← pow_mul]
    field_simp
  have hvarg : b / (q * (b ^ 2 * q ^ (2 * N))) = v := by
    dsimp [v]
    simp only [zpow_neg, zpow_natCast, ← pow_mul]
    field_simp
  have hR := qPochhammer_reverse_ratio hu hv (pow_ne_zero 2 hq0) (N + 1)
  have huR : (q ^ 2) ^ (1 - ((N + 1 : ℕ) : ℤ)) / u = b := by
    rw [show 1 - ((N + 1 : ℕ) : ℤ) = -(N : ℤ) by omega]
    dsimp [u]
    field_simp
  have hvR : (q ^ 2) ^ (1 - ((N + 1 : ℕ) : ℤ)) / v = b * q := by
    rw [show 1 - ((N + 1 : ℕ) : ℤ) = -(N : ℤ) by omega]
    dsimp [v]
    field_simp
  have huv : u / v = q := by dsimp [u, v]; field_simp
  rw [huR, hvR, huv] at hR
  rw [huarg, hvarg]
  have hprod : qPochhammer (b / q) (q ^ 2) (N + 1) * qPochhammer u (q ^ 2) (N + 1) /
      (qPochhammer b (q ^ 2) (N + 1) * qPochhammer v (q ^ 2) (N + 1)) =
      q ^ (N + 1) * qPochhammer (b / q) (q ^ 2) (N + 1) /
        qPochhammer (b * q) (q ^ 2) (N + 1) := by
    calc
      _ = qPochhammer (b / q) (q ^ 2) (N + 1) / qPochhammer b (q ^ 2) (N + 1) *
          (qPochhammer u (q ^ 2) (N + 1) / qPochhammer v (q ^ 2) (N + 1)) := by ring
      _ = _ := by rw [hR]; field_simp
  rw [hprod]
  have hshift := DixonPolynomial.one_sub_mul_pochhammer_shift (b / q) (q ^ 2) (N + 1)
  have hp : b / q * (q ^ 2) ^ (N + 1) = b * q ^ (2 * N + 1) := by
    rw [← pow_mul, show 2 * (N + 1) = (2 * N + 1) + 1 by omega, pow_succ]
    field_simp
  rw [show b / q * q ^ 2 = b * q by field_simp, hp] at hshift
  have hlast : 1 - b * q ^ (2 * N + 1) ≠ 0 := by
    intro he
    have h := DLMF.QSeries.norm_mul_pow_lt_one hb1 hq (2 * N + 1)
    rw [← sub_eq_zero.mp he, norm_one] at h
    exact lt_irrefl _ h
  field_simp at hshift ⊢
  exact hshift.symm

/-- The product polynomial at the base is the finite normalizing value. -/
theorem eval_valuePolynomial_base {b q : ℂ} (hb : ‖b‖ < ‖q‖) (hq0 : q ≠ 0)
    (hq : ‖q‖ < 1) (N : ℕ) :
    (valuePolynomial b q (N + 1)).eval q = qPochhammer (-q) q (N + 1) *
      (q ^ (N + 1) * (1 - b / q) / (1 - b * q ^ (2 * N + 1))) := by
  have hb1 := hb.trans hq
  have hbn := pochhammer_ne_zero_of_norm_lt_one hb1 hq (N + 1)
  have hlast : 1 - b * q ^ (2 * N + 1) ≠ 0 := by
    intro he
    have h := DLMF.QSeries.norm_mul_pow_lt_one hb1 hq (2 * N + 1)
    rw [← sub_eq_zero.mp he, norm_one] at h
    exact lt_irrefl _ h
  simp only [valuePolynomial, eval_mul, eval_C, eval_prod, eval_sub, eval_X,
    Nat.add_sub_cancel, show 2 * (N + 1) - 1 = 2 * N + 1 by omega]
  rw [PfaffSaalschutz.prod_sub_mul_pow_eq_pow_mul_qPochhammer hq0]
  have hshift := DixonPolynomial.one_sub_mul_pochhammer_shift (b / q) q (N + 1)
  rw [div_mul_cancel₀ b hq0,
    show b / q * q ^ (N + 1) = b * q ^ N by rw [pow_succ]; field_simp] at hshift
  field_simp at hshift ⊢
  linear_combination -(qPochhammer (-q) q (N + 1)) * hshift

/-- The sum polynomial takes the required value at the base. -/
theorem eval_sumPolynomial_base {b q : ℂ} (hb0 : b ≠ 0) (hb : ‖b‖ < ‖q‖)
    (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (N : ℕ) :
    (sumPolynomial b q (N + 1)).eval q = (valuePolynomial b q (N + 1)).eval q := by
  have hQ : ‖q ^ 2‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (by omega)
  rw [eval_sumPolynomial _ _ _ _ hq (qPochhammer_self_ne_zero hQ _)
    (pochhammer_ne_zero_of_norm_lt_one (hb.trans hq) hq _),
    sum_seriesTerm_base_eq hb0 hb hq0 hq, eval_valuePolynomial_base hb hq0 hq]

/-- Each displayed linear factor gives a zero of the product polynomial. -/
theorem eval_valuePolynomial_mul_pow (b q : ℂ) (n m : ℕ) (hm : m < n) :
    (valuePolynomial b q n).eval (b * q ^ m) = 0 := by
  simp only [valuePolynomial, eval_mul, eval_C, eval_prod, eval_sub, eval_X]
  rw [prod_eq_zero (mem_range.mpr hm) (by simp), mul_zero]

/-- Interpolation proves the companion identity when the other parameter is close to zero. -/
theorem sumPolynomial_eq_valuePolynomial_of_norm_lt {b q : ℂ} (hb0 : b ≠ 0)
    (hb : ‖b‖ < ‖q‖) (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (N : ℕ) :
    sumPolynomial b q (N + 1) = valuePolynomial b q (N + 1) := by
  have hbdiv : ‖b / q‖ < 1 := by
    rw [norm_div]
    exact (div_lt_one (norm_pos_iff.mpr hq0)).mpr hb
  have hinj : Function.Injective (fun i : ℕ =>
      q * QuadraticSummation.interpolationPoint (b / q) q i) :=
    (mul_right_injective₀ hq0).comp
      (QuadraticSummation.injective_interpolationPoint (div_ne_zero hb0 hq0) hbdiv hq0 hq)
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq (range (N + 1 + 1)) hinj.injOn
  · apply Polynomial.degree_le_natDegree.trans_lt
    simp only [card_range]
    exact_mod_cast lt_of_le_of_lt (natDegree_sumPolynomial_le b q (N + 1))
      (Nat.lt_succ_self (N + 1))
  · apply Polynomial.degree_le_natDegree.trans_lt
    simp only [card_range]
    exact_mod_cast lt_of_le_of_lt (natDegree_valuePolynomial_le b q (N + 1))
      (Nat.lt_succ_self (N + 1))
  · intro i hi
    cases i with
    | zero =>
      simpa [QuadraticSummation.interpolationPoint] using
        eval_sumPolynomial_base hb0 hb hq0 hq N
    | succ m =>
      have hm : m < N + 1 := by simp at hi; omega
      have hp : q * QuadraticSummation.interpolationPoint (b / q) q (m + 1) = b * q ^ m := by
        dsimp [QuadraticSummation.interpolationPoint]
        field_simp
      rw [hp, eval_sumPolynomial_mul_pow (hb.trans hq) hq0 hq _ _ hm,
        eval_valuePolynomial_mul_pow _ _ _ _ hm]
/-- The first quadratic sum as a polynomial in its other parameter after clearing denominators. -/
def clearedSumPolynomial (a q : ℂ) (n : ℕ) : Polynomial ℂ :=
  ∑ k ∈ range (n + 1),
    C (qPochhammer ((q ^ 2) ^ (-(n : ℤ))) (q ^ 2) k /
      qPochhammer (q ^ 2) (q ^ 2) k * (q ^ 2) ^ k * (termPolynomial q n k).eval a) *
      (DixonPolynomial.pochhammerPolynomial (q ^ (2 * (n - 1))) (q ^ 2) k).comp (X ^ 2) *
      DixonPolynomial.pochhammerPolynomial (q ^ (2 * k)) q (2 * n - 2 * k)

/-- The denominator-free product polynomial for the companion sum. -/
def clearedValuePolynomial (a q : ℂ) (n : ℕ) : Polynomial ℂ :=
  C (qPochhammer (-q) q n) * (1 - X * C (q ^ (n - 1))) *
    (∏ j ∈ range n, (C a - X * C (q ^ j))) *
    DixonPolynomial.pochhammerPolynomial (q ^ n) q (n - 1)

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
  rw [mul_comm (q ^ (2 * (n - 1))) (b ^ 2), mul_comm (q ^ (2 * k)) b]
  unfold coefficient
  field_simp
  linear_combination
    -(qPochhammer ((q ^ 2) ^ (-(n : ℤ))) (q ^ 2) k *
      qPochhammer (b ^ 2 * q ^ (2 * (n - 1))) (q ^ 2) k * (q ^ 2) ^ k *
      (termPolynomial q n k).eval a) * h

/-- Clearing the companion product denominator gives its polynomial value. -/
theorem eval_clearedValuePolynomial (a b q : ℂ) (N : ℕ)
    (hb : qPochhammer b q (2 * (N + 1)) ≠ 0) :
    (clearedValuePolynomial a q (N + 1)).eval b =
      qPochhammer b q (2 * (N + 1)) * (valuePolynomial b q (N + 1)).eval a := by
  have hbn := qPochhammer_ne_zero_of_le hb (show N + 1 ≤ 2 * (N + 1) by omega)
  have hf : qPochhammer b q (2 * (N + 1)) = qPochhammer b q (N + 1) *
      qPochhammer (b * q ^ (N + 1)) q N * (1 - b * q ^ (2 * N + 1)) := by
    rw [two_mul, qPochhammer_add, qPochhammer_succ (b * q ^ (N + 1)) q N,
      mul_assoc b, ← pow_add, show N + 1 + N = 2 * N + 1 by omega]
    ring
  have hlast : 1 - b * q ^ (2 * N + 1) ≠ 0 := by
    rw [hf] at hb
    exact right_ne_zero_of_mul hb
  simp only [clearedValuePolynomial, valuePolynomial, eval_mul, eval_C, eval_prod,
    eval_sub, eval_one, eval_X, DixonPolynomial.eval_pochhammerPolynomial,
    Nat.add_sub_cancel, show 2 * (N + 1) - 1 = 2 * N + 1 by omega]
  rw [mul_comm (q ^ (N + 1)) b, hf]
  field_simp

/-- Polynomial continuation removes restrictions on the remaining companion parameter. -/
theorem clearedSumPolynomial_eq_valuePolynomial {q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (a : ℂ) (N : ℕ) :
    clearedSumPolynomial a q (N + 1) = clearedValuePolynomial a q (N + 1) := by
  have hinj : Function.Injective (fun m : ℕ => q ^ (m + 2)) := by
    intro i j he
    have hn := congrArg norm he
    simp only [norm_pow] at hn
    have := (pow_right_strictAnti₀ (norm_pos_iff.mpr hq0) hq).injective hn
    omega
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective hinj).mono
  rintro b ⟨m, rfl⟩
  have hb : ‖q ^ (m + 2)‖ < ‖q‖ := by
    rw [norm_pow]
    convert (pow_right_strictAnti₀ (norm_pos_iff.mpr hq0) hq) (show 1 < m + 2 by omega)
    simp
  have hreg := pochhammer_ne_zero_of_norm_lt_one (hb.trans hq) hq (2 * (N + 1))
  change (clearedSumPolynomial a q (N + 1)).eval (q ^ (m + 2)) =
    (clearedValuePolynomial a q (N + 1)).eval (q ^ (m + 2))
  rw [eval_clearedSumPolynomial _ _ _ _ hq hreg,
    eval_clearedValuePolynomial _ _ _ _ hreg,
    sumPolynomial_eq_valuePolynomial_of_norm_lt (pow_ne_zero _ hq0) hb hq0 hq]

/-- The companion polynomial identity at every regular parameter. -/
theorem eval_sumPolynomial_eq_valuePolynomial {q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (a b : ℂ) (N : ℕ) (hb : qPochhammer b q (2 * (N + 1)) ≠ 0) :
    (sumPolynomial b q (N + 1)).eval a = (valuePolynomial b q (N + 1)).eval a := by
  have h := congrArg (Polynomial.eval b) (clearedSumPolynomial_eq_valuePolynomial hq0 hq a N)
  rw [eval_clearedSumPolynomial _ _ _ _ hq hb,
    eval_clearedValuePolynomial _ _ _ _ hb] at h
  exact mul_left_cancel₀ hb h

/-- The finite quadratic series equals its product at every regular terminating parameter. -/
theorem second_quadratic_sum_positive {a b q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (N : ℕ)
    (hd : QDenominatorRegularThrough [b, b * q, a ^ 2] (q ^ 2) (N + 1)) :
    qPhi [a, a * q, b ^ 2 * q ^ (2 * N), q ^ (-(2 * (N + 1 : ℕ) : ℤ))]
        [b, b * q, a ^ 2] (q ^ 2) (q ^ 2) =
      qPochhammer (-q) q (N + 1) * (∏ j ∈ range (N + 1), (a - b * q ^ j)) *
        (1 - b * q ^ N) /
        (qPochhammerList [-a, b] q (N + 1) * (1 - b * q ^ (2 * N + 1))) := by
  have hd' : qPochhammer b (q ^ 2) (N + 1) * qPochhammer (b * q) (q ^ 2) (N + 1) *
      qPochhammer (a ^ 2) (q ^ 2) (N + 1) ≠ 0 := by
    simpa [QDenominatorRegularThrough, qPochhammerList, mul_assoc] using hd
  have hA := right_ne_zero_of_mul hd'
  have hB : qPochhammer b q (2 * (N + 1)) ≠ 0 := by
    rw [qPochhammer_even]
    simpa [qPochhammerList] using left_ne_zero_of_mul hd'
  have hminus : qPochhammer (-a) q (N + 1) ≠ 0 := by
    have h := hA
    rw [qPochhammer_squared] at h
    exact right_ne_zero_of_mul h
  have htrunc : qPhi [a, a * q, b ^ 2 * q ^ (2 * N), q ^ (-(2 * (N + 1 : ℕ) : ℤ))]
        [b, b * q, a ^ 2] (q ^ 2) (q ^ 2) =
      ∑ k ∈ range ((N + 1) + 1), seriesTerm a b q (N + 1) k := by
    have hz : (q ^ 2) ^ (-((N + 1 : ℕ) : ℤ)) = q ^ (-(2 * (N + 1 : ℕ) : ℤ)) := by
      rw [← zpow_natCast q 2, ← zpow_mul]
      congr 1
    unfold qPhi
    rw [tsum_eq_sum (s := range ((N + 1) + 1)) (fun k hk => ?_)]
    · apply sum_congr rfl
      intro k _
      have he : qPhiExponent [a, a * q, b ^ 2 * q ^ (2 * N), q ^ (-(2 * (N + 1 : ℕ) : ℤ))]
          [b, b * q, a ^ 2] = 0 := by simp [qPhiExponent]
      simp only [qPhiTerm, he, zpow_zero, mul_one]
      have hea := qPochhammer_even a q k
      have heb := qPochhammer_even b q k
      simp only [qPochhammerList, List.map_cons, List.map_nil, List.prod_cons,
        List.prod_nil, mul_one] at hea heb ⊢
      simp only [seriesTerm, Nat.add_sub_cancel, hz]
      rw [hea, heb]
      ring
    · have hn : (N + 1) < k := by simpa using hk
      have hz0 := qPochhammer_recip_pow_eq_zero (pow_ne_zero 2 hq0) hn
      have hzero : qPochhammer (q ^ (-(2 * (N + 1 : ℕ) : ℤ))) (q ^ 2) k = 0 := by
        rw [← hz]
        simpa only [zpow_neg, zpow_natCast] using hz0
      simp only [qPhiTerm, qPochhammerList, List.map_cons, List.map_nil,
        List.prod_cons, List.prod_nil, hzero, mul_zero, zero_div, zero_mul]
  rw [htrunc]
  have he := eval_sumPolynomial_eq_valuePolynomial hq0 hq a b N hB
  rw [eval_sumPolynomial _ _ _ _ hq hA hB] at he
  simp only [valuePolynomial, eval_mul, eval_C, eval_prod, eval_sub, eval_X] at he
  have hbn := qPochhammer_ne_zero_of_le hB (show (N + 1) ≤ 2 * (N + 1) by omega)
  simp only [qPochhammerList, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one]
  have hBfactor : qPochhammer b q (2 * (N + 1)) =
      qPochhammer b q (2 * N + 1) * (1 - b * q ^ (2 * N + 1)) := by
    rw [show 2 * (N + 1) = (2 * N + 1) + 1 by omega, qPochhammer_succ]
  have hlast : 1 - b * q ^ (2 * N + 1) ≠ 0 := by
    rw [hBfactor] at hB
    exact right_ne_zero_of_mul hB
  simp only [Nat.add_sub_cancel, show 2 * (N + 1) - 1 = 2 * N + 1 by omega] at he
  apply (eq_div_iff (mul_ne_zero (mul_ne_zero hminus hbn) hlast)).mpr
  field_simp at he
  linear_combination he

/-- The companion quadratic summation, including its removable value at truncation zero. -/
theorem second_quadratic_sum {a b q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (n : ℕ)
    (hd : QDenominatorRegularThrough [b, b * q, a ^ 2] (q ^ 2) n) :
    qPhi [a, a * q, b ^ 2 * q ^ (2 * (n : ℤ) - 2), q ^ (-(2 * n : ℤ))]
        [b, b * q, a ^ 2] (q ^ 2) (q ^ 2) =
      if n = 0 then 1 else qPochhammer (-q) q n *
        (∏ j ∈ range n, (a - b * q ^ j)) * (1 - b * q ^ ((n : ℤ) - 1)) /
        (qPochhammerList [-a, b] q n * (1 - b * q ^ (2 * (n : ℤ) - 1))) := by
  cases n with
  | zero =>
    rw [ite_eq_left rfl, PfaffSaalschutz.qPhi_eq_sum_of_mem (pow_ne_zero 2 hq0) 0 (by simp)]
    simp [qPhiTerm, qPhiExponent, qPochhammerList]
  | succ N =>
    rw [ite_eq_right (by omega)]
    have h1 : q ^ (((N + 1 : ℕ) : ℤ) - 1) = q ^ N := by
      rw [show ((N + 1 : ℕ) : ℤ) - 1 = (N : ℤ) by omega, zpow_natCast]
    have h2 : q ^ (2 * ((N + 1 : ℕ) : ℤ) - 1) = q ^ (2 * N + 1) := by
      rw [show 2 * ((N + 1 : ℕ) : ℤ) - 1 = ((2 * N + 1 : ℕ) : ℤ) by omega, zpow_natCast]
    have h3 : q ^ (2 * ((N + 1 : ℕ) : ℤ) - 2) = q ^ (2 * N) := by
      rw [show 2 * ((N + 1 : ℕ) : ℤ) - 2 = ((2 * N : ℕ) : ℤ) by omega, zpow_natCast]
    simp only [h1, h2, h3]
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using second_quadratic_sum_positive hq0 hq N hd

end DLMF.QHypergeometric.QuadraticCompanion
