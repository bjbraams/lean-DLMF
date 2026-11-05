/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.QuadraticSummation
public import DLMF.QHypergeometric.FiniteDifferenceRational

/-!
# The terminating q-Watson parity summation

Polynomial interpolation in the squared upper parameter proves the terminating parity
summation of DLMF 17.7.9. The proof follows Wang–Chu, *Approach of q-Derivative Operators
to Terminating q-Series Formulae*, §3, https://doi.org/10.2478/cm-2018-0007.
-/

@[expose] public noncomputable section

open Complex Finset Polynomial
open DLMF.QSeries

namespace DLMF.QHypergeometric.ParitySummation

/-- The polynomial left after clearing the parameter-dependent denominator in one summand.
-/
def termPolynomial (q : ℂ) (m k : ℕ) : Polynomial ℂ :=
  if Even k then
    DixonPolynomial.pochhammerPolynomial (q ^ k) (q ^ 2) (k / 2) *
      DixonPolynomial.pochhammerPolynomial (q ^ (k + 1)) (q ^ 2) (m - k / 2)
  else
    DixonPolynomial.pochhammerPolynomial (q ^ (k + 1)) (q ^ 2) (k / 2) *
      DixonPolynomial.pochhammerPolynomial (q ^ k) (q ^ 2) (m - k / 2)

/-- Every cancellation polynomial has degree at most the half truncation index. -/
lemma natDegree_termPolynomial_le (q : ℂ) (m k : ℕ) (hk : k / 2 ≤ m) :
    (termPolynomial q m k).natDegree ≤ m := by
  unfold termPolynomial
  split <;>
    exact natDegree_mul_le.trans (by
      have h1 := QuadraticSummation.natDegree_pochhammerPolynomial_le
        (q ^ k) (q ^ 2) (k / 2)
      have h2 := QuadraticSummation.natDegree_pochhammerPolynomial_le
        (q ^ (k + 1)) (q ^ 2) (m - k / 2)
      have h3 := QuadraticSummation.natDegree_pochhammerPolynomial_le
        (q ^ (k + 1)) (q ^ 2) (k / 2)
      have h4 := QuadraticSummation.natDegree_pochhammerPolynomial_le
        (q ^ k) (q ^ 2) (m - k / 2)
      omega)

/-- Clearing the ordinary lower shifted factorial gives the polynomial cancellation factor.
-/
lemma eval_termPolynomial_mul (x q : ℂ) (m k : ℕ) (hk : k / 2 ≤ m) :
    (termPolynomial q m k).eval x * qPochhammer x q k =
      qPochhammer x (q ^ 2) k * qPochhammer (x * q) (q ^ 2) m := by
  rcases Nat.even_or_odd k with he | ho
  · obtain ⟨r, hr⟩ := he
    have hkr : k = 2 * r := by omega
    clear hr
    subst k
    have hR : r ≤ m := by omega
    have h1 := qPochhammer_add x (q ^ 2) r r
    have h2 := qPochhammer_add (x * q) (q ^ 2) r (m - r)
    rw [Nat.add_sub_cancel' hR] at h2
    rw [← two_mul] at h1
    simp only [← pow_mul] at h1 h2
    have he : Even (2 * r) := ⟨r, by omega⟩
    simp only [termPolynomial, ite_eq_left he, show 2 * r / 2 = r by omega, eval_mul,
      DixonPolynomial.eval_pochhammerPolynomial]
    rw [qPochhammer_even, h1, h2]
    simp only [qPochhammerList, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one]
    rw [show q ^ (2 * r) * x = x * q ^ (2 * r) by ring,
      show q ^ (2 * r + 1) * x = x * q * q ^ (2 * r) by rw [pow_succ]; ring]
    ring
  · obtain ⟨r, hr⟩ := ho
    have hkr : k = 2 * r + 1 := by omega
    clear hr
    subst k
    have hR : r ≤ m := by omega
    have h1 := qPochhammer_add x (q ^ 2) (r + 1) r
    have h2 := qPochhammer_add (x * q) (q ^ 2) r (m - r)
    rw [Nat.add_sub_cancel' hR] at h2
    rw [show r + 1 + r = 2 * r + 1 by omega] at h1
    simp only [← pow_mul] at h1 h2
    have hodd : ¬Even (2 * r + 1) := by rintro ⟨j, hj⟩; omega
    simp only [termPolynomial, ite_eq_right hodd, show (2 * r + 1) / 2 = r by omega,
      eval_mul, DixonPolynomial.eval_pochhammerPolynomial]
    rw [qPochhammer_succ, qPochhammer_even, h1, h2]
    simp only [qPochhammerList, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one]
    rw [qPochhammer_succ]
    simp only [← pow_mul]
    rw [show q ^ (2 * r + 1 + 1) * x = x * q ^ (2 * (r + 1)) by
      rw [show 2 * r + 1 + 1 = 2 * (r + 1) by omega]; ring,
      show q ^ (2 * r + 1) * x = x * q * q ^ (2 * r) by rw [pow_succ]; ring]
    ring

/-- The finite q-Watson summand with its opposite upper parameters combined. -/
def seriesTerm (a x q : ℂ) (n k : ℕ) : ℂ :=
  FiniteDifferencePolynomial.coefficient q n k *
    qPochhammer (a * q ^ n) q k / qPochhammer (a * q) (q ^ 2) k *
      qPochhammer x (q ^ 2) k / qPochhammer x q k

/-- Clearing the squared upper parameter produces a polynomial of half the truncation degree.
-/
def sumPolynomial (a q : ℂ) (n : ℕ) : Polynomial ℂ :=
  ∑ k ∈ range (n + 1), C (FiniteDifferencePolynomial.coefficient q n k *
    qPochhammer (a * q ^ n) q k / qPochhammer (a * q) (q ^ 2) k) *
      termPolynomial q (n / 2) k

/-- The product value of the parity sum after clearing the parameter-dependent denominator. -/
def valuePolynomial (a q : ℂ) (n : ℕ) : Polynomial ℂ :=
  if Odd n then 0 else
    C (qPochhammer q (q ^ 2) (n / 2) / qPochhammer (a * q) (q ^ 2) (n / 2)) *
      ∏ j ∈ range (n / 2), (X - C (a * q ^ (2 * j + 1)))

/-- The cleared sum has degree at most its half truncation index. -/
lemma natDegree_sumPolynomial_le (a q : ℂ) (n : ℕ) :
    (sumPolynomial a q n).natDegree ≤ n / 2 := by
  unfold sumPolynomial
  apply natDegree_sum_le_of_forall_le
  intro k hk
  exact (natDegree_C_mul_le _ _).trans (natDegree_termPolynomial_le q (n / 2) k
    (by have := Finset.mem_range.mp hk; omega))

/-- The product value has degree at most its half truncation index. -/
lemma natDegree_valuePolynomial_le (a q : ℂ) (n : ℕ) :
    (valuePolynomial a q n).natDegree ≤ n / 2 := by
  unfold valuePolynomial
  split
  · simp
  · refine (natDegree_C_mul_le _ _).trans ?_
    calc
      _ ≤ ∑ _j ∈ range (n / 2), 1 := by
        refine natDegree_prod_le _ _ |>.trans ?_
        apply sum_le_sum
        intro j hj
        rw [natDegree_X_sub_C]
      _ = _ := by simp

/-- Evaluation of the cleared polynomial agrees with the finite series at regular parameters.
-/
lemma eval_sumPolynomial (a x q : ℂ) (n : ℕ) (hx : qPochhammer x q n ≠ 0) :
    (sumPolynomial a q n).eval x =
      qPochhammer (x * q) (q ^ 2) (n / 2) *
        ∑ k ∈ range (n + 1), seriesTerm a x q n k := by
  simp only [sumPolynomial, eval_finsetSum, eval_mul, eval_C, mul_sum]
  apply sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by have := Finset.mem_range.mp hk; omega
  have hkx := qPochhammer_ne_zero_of_le hx hkn
  have H := eval_termPolynomial_mul x q (n / 2) k (by omega)
  have he := (eq_div_iff hkx).mpr H
  rw [he]
  unfold seriesTerm
  ring

/-- Interpolation points are the successive odd shifts of the fixed parameter. -/
def interpolationPoint (a q : ℂ) (t : ℕ) : ℂ := a * q ^ (2 * t + 1)

/-- At a root of the parity product, the summand is a finite difference of this polynomial.
-/
def rootPolynomial (a q : ℂ) (n t : ℕ) : Polynomial ℂ :=
  DixonPolynomial.pochhammerPolynomial (interpolationPoint a q t) q (n - 2 * t - 1) *
    (DixonPolynomial.pochhammerPolynomial (a * q) (q ^ 2) t).comp (X ^ 2)

/-- The polynomial at a root has degree below the finite-difference order. -/
lemma natDegree_rootPolynomial_lt (a q : ℂ) (n t : ℕ) (ht : 2 * t < n) :
    (rootPolynomial a q n t).natDegree < n := by
  have h1 := QuadraticSummation.natDegree_pochhammerPolynomial_le
    (interpolationPoint a q t) q (n - 2 * t - 1)
  have h2 := QuadraticSummation.natDegree_pochhammerPolynomial_le (a * q) (q ^ 2) t
  have h3 := natDegree_comp_le
    (p := DixonPolynomial.pochhammerPolynomial (a * q) (q ^ 2) t) (q := X ^ 2)
  have h4 := natDegree_mul_le
    (p := DixonPolynomial.pochhammerPolynomial (interpolationPoint a q t) q (n - 2 * t - 1))
    (q := (DixonPolynomial.pochhammerPolynomial (a * q) (q ^ 2) t).comp (X ^ 2))
  simp only [natDegree_X_pow] at h3
  dsimp only [rootPolynomial]
  omega

/-- At each vanishing node, clearing fixed factors makes the summand a polynomial difference.
-/
lemma seriesTerm_root_mul {a q : ℂ} (ha : ‖a‖ < 1) (hq : ‖q‖ < 1)
    (n t k : ℕ) (ht : 2 * t < n) :
    seriesTerm a (interpolationPoint a q t) q n k *
        (qPochhammer (interpolationPoint a q t) q (n - 2 * t - 1) *
          qPochhammer (a * q) (q ^ 2) t) =
      FiniteDifferencePolynomial.coefficient q n k * (rootPolynomial a q n t).eval (q ^ k) := by
  let x := interpolationPoint a q t
  have hx : ‖x‖ < 1 := norm_mul_pow_lt_one ha hq (2 * t + 1)
  have haq : ‖a * q‖ < 1 := by simpa using norm_mul_pow_lt_one ha hq 1
  have hQ : ‖q ^ 2‖ < 1 := by rw [norm_pow]; nlinarith [norm_nonneg q]
  have hX := QuadraticSummation.pochhammer_ne_zero_of_norm_lt_one hx hq k
  have hA := QuadraticSummation.pochhammer_ne_zero_of_norm_lt_one haq hQ k
  have h1 := QuadraticSummation.pochhammer_interchange x q (n - 2 * t - 1) k
  have h2 := QuadraticSummation.pochhammer_interchange (a * q) (q ^ 2) t k
  have he1 : x * q ^ (n - 2 * t - 1) = a * q ^ n := by
    dsimp [x, interpolationPoint]
    rw [mul_assoc, ← pow_add, show 2 * t + 1 + (n - 2 * t - 1) = n by omega]
  have he2 : a * q * (q ^ 2) ^ t = x := by
    dsimp [x, interpolationPoint]
    rw [← pow_mul, pow_succ]
    ring
  rw [he1] at h1
  rw [he2] at h2
  have hprod : qPochhammer (a * q ^ n) q k * qPochhammer x (q ^ 2) k *
      (qPochhammer x q (n - 2 * t - 1) * qPochhammer (a * q) (q ^ 2) t) =
      (qPochhammer (a * q) (q ^ 2) k * qPochhammer x q k) *
        (qPochhammer (x * q ^ k) q (n - 2 * t - 1) *
          qPochhammer (a * q * (q ^ 2) ^ k) (q ^ 2) t) := by
    linear_combination congrArg₂ (fun u v : ℂ => u * v) h1 h2
  rw [show x * q ^ k = q ^ k * interpolationPoint a q t by dsimp [x]; ring] at hprod
  simp only [rootPolynomial, eval_mul, Polynomial.eval_comp, eval_pow, eval_X,
    DixonPolynomial.eval_pochhammerPolynomial]
  rw [show (a * q) * (q ^ k) ^ 2 = a * q * (q ^ 2) ^ k by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm k 2],
    show x * q ^ k = q ^ k * interpolationPoint a q t by dsimp [x]; ring]
  change seriesTerm a x q n k * _ = _
  calc
    _ = FiniteDifferencePolynomial.coefficient q n k *
        (qPochhammer (a * q ^ n) q k * qPochhammer x (q ^ 2) k *
          (qPochhammer x q (n - 2 * t - 1) * qPochhammer (a * q) (q ^ 2) t) /
          (qPochhammer (a * q) (q ^ 2) k * qPochhammer x q k)) := by
      unfold seriesTerm
      ring
    _ = _ := by rw [hprod]; field_simp [hA, hX]

/-- The finite series vanishes at every node corresponding to a product root. -/
lemma sum_seriesTerm_root_eq_zero {a q : ℂ} (ha : ‖a‖ < 1)
    (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (n t : ℕ) (ht : 2 * t < n) :
    ∑ k ∈ range (n + 1), seriesTerm a (interpolationPoint a q t) q n k = 0 := by
  have hx : ‖interpolationPoint a q t‖ < 1 := norm_mul_pow_lt_one ha hq (2 * t + 1)
  have haq : ‖a * q‖ < 1 := by simpa using norm_mul_pow_lt_one ha hq 1
  have hQ : ‖q ^ 2‖ < 1 := by rw [norm_pow]; nlinarith [norm_nonneg q]
  have hD : qPochhammer (interpolationPoint a q t) q (n - 2 * t - 1) *
      qPochhammer (a * q) (q ^ 2) t ≠ 0 :=
    mul_ne_zero (QuadraticSummation.pochhammer_ne_zero_of_norm_lt_one hx hq _)
      (QuadraticSummation.pochhammer_ne_zero_of_norm_lt_one haq hQ _)
  apply (mul_eq_zero.mp (show (∑ k ∈ range (n + 1),
    seriesTerm a (interpolationPoint a q t) q n k) *
      (qPochhammer (interpolationPoint a q t) q (n - 2 * t - 1) *
        qPochhammer (a * q) (q ^ 2) t) = 0 from ?_)).resolve_right hD
  rw [sum_mul]
  simp_rw [seriesTerm_root_mul ha hq n t _ ht]
  exact FiniteDifferencePolynomial.sum_eval_eq_zero_of_natDegree_lt hq0 hq
    (rootPolynomial a q n t) (natDegree_rootPolynomial_lt a q n t ht)

/-- The cleared sum polynomial vanishes at each of its prescribed interpolation roots. -/
lemma eval_sumPolynomial_root {a q : ℂ} (ha : ‖a‖ < 1)
    (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (n t : ℕ) (ht : 2 * t < n) :
    (sumPolynomial a q n).eval (interpolationPoint a q t) = 0 := by
  have hx : ‖interpolationPoint a q t‖ < 1 := norm_mul_pow_lt_one ha hq (2 * t + 1)
  rw [eval_sumPolynomial a _ q n
    (QuadraticSummation.pochhammer_ne_zero_of_norm_lt_one hx hq _),
    sum_seriesTerm_root_eq_zero ha hq0 hq n t ht, mul_zero]

/-- Distinct odd shifts give distinct interpolation points in the punctured unit disk. -/
lemma injective_interpolationPoint {a q : ℂ} (ha0 : a ≠ 0) (hq0 : q ≠ 0) (hq : ‖q‖ < 1) :
    Function.Injective (interpolationPoint a q) := by
  intro i j he
  have hp := mul_left_cancel₀ ha0 he
  have hn := congrArg norm hp
  simp only [norm_pow] at hn
  have hh := (pow_right_strictAnti₀ (norm_pos_iff.mpr hq0) hq).injective hn
  omega

/-- The polynomial whose rational finite difference fixes the even normalization. -/
def normalizationPolynomial (a q : ℂ) (m : ℕ) : Polynomial ℂ :=
  (DixonPolynomial.pochhammerPolynomial (a * q) (q ^ 2) m).comp (X ^ 2)

/-- The normalization polynomial has degree at most the even difference order. -/
lemma natDegree_normalizationPolynomial_le (a q : ℂ) (m : ℕ) :
    (normalizationPolynomial a q m).natDegree ≤ 2 * m := by
  have h := natDegree_comp_le
    (p := DixonPolynomial.pochhammerPolynomial (a * q) (q ^ 2) m) (q := X ^ 2)
  have h1 := QuadraticSummation.natDegree_pochhammerPolynomial_le (a * q) (q ^ 2) m
  simp only [natDegree_X_pow] at h
  dsimp [normalizationPolynomial]
  omega

/-- At the even normalization point, each summand is a rational finite-difference term. -/
lemma seriesTerm_normalization_mul {a q : ℂ} (ha : ‖a‖ < 1) (hq : ‖q‖ < 1)
    (m k : ℕ) :
    seriesTerm a (interpolationPoint a q m) q (2 * m) k *
        qPochhammer (a * q) (q ^ 2) m =
      (1 - a * q ^ (2 * m)) * FiniteDifferencePolynomial.coefficient q (2 * m) k *
        (normalizationPolynomial a q m).eval (q ^ k) /
        (1 - a * q ^ (2 * m) * q ^ k) := by
  let u := a * q ^ (2 * m)
  let x := interpolationPoint a q m
  have hx : x = u * q := by dsimp [x, u, interpolationPoint]; rw [pow_succ]; ring
  have hux : ‖u‖ < 1 := norm_mul_pow_lt_one ha hq (2 * m)
  have hxx : ‖x‖ < 1 := norm_mul_pow_lt_one ha hq (2 * m + 1)
  have haq : ‖a * q‖ < 1 := by simpa using norm_mul_pow_lt_one ha hq 1
  have hQ : ‖q ^ 2‖ < 1 := by rw [norm_pow]; nlinarith [norm_nonneg q]
  have hX := QuadraticSummation.pochhammer_ne_zero_of_norm_lt_one hxx hq k
  have hA := QuadraticSummation.pochhammer_ne_zero_of_norm_lt_one haq hQ k
  have huk : 1 - u * q ^ k ≠ 0 :=
    one_sub_ne_zero_of_norm_lt_one (norm_mul_pow_lt_one hux hq k)
  have h1 := QuadraticSummation.pochhammer_interchange (a * q) (q ^ 2) m k
  rw [show a * q * (q ^ 2) ^ m = x by
    dsimp [x, interpolationPoint]; rw [← pow_mul, pow_succ]; ring] at h1
  have h2 := qPochhammer_succ' u q k
  rw [qPochhammer_succ, ← hx] at h2
  have hr : qPochhammer u q k / qPochhammer x q k =
      (1 - u) / (1 - u * q ^ k) := by
    apply (div_eq_div_iff hX huk).mpr
    exact h2
  have hp : qPochhammer x (q ^ 2) k * qPochhammer (a * q) (q ^ 2) m /
      qPochhammer (a * q) (q ^ 2) k =
        (normalizationPolynomial a q m).eval (q ^ k) := by
    simp only [normalizationPolynomial, Polynomial.eval_comp, eval_pow, eval_X,
      DixonPolynomial.eval_pochhammerPolynomial]
    rw [show a * q * (q ^ k) ^ 2 = a * q * (q ^ 2) ^ k by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm k 2]]
    apply (div_eq_iff hA).mpr
    linear_combination h1
  calc
    _ = FiniteDifferencePolynomial.coefficient q (2 * m) k *
        (qPochhammer u q k / qPochhammer x q k) *
        (qPochhammer x (q ^ 2) k * qPochhammer (a * q) (q ^ 2) m /
          qPochhammer (a * q) (q ^ 2) k) := by dsimp [seriesTerm, u, x]; ring
    _ = _ := by rw [hr, hp]; dsimp [u]; ring

/-- The even normalization is the rational finite-difference evaluation. -/
lemma sum_seriesTerm_normalization_mul {a q : ℂ} (ha0 : a ≠ 0) (ha : ‖a‖ < 1)
    (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (m : ℕ) (hm : 0 < m) :
    (∑ k ∈ range (2 * m + 1), seriesTerm a (interpolationPoint a q m) q (2 * m) k) *
        qPochhammer (a * q) (q ^ 2) m =
      (1 - a * q ^ (2 * m)) *
        ((a * q ^ (2 * m)) ^ (2 * m) * qPochhammer q q (2 * m) /
          qPochhammer (a * q ^ (2 * m)) q (2 * m + 1) *
          (normalizationPolynomial a q m).eval (a * q ^ (2 * m))⁻¹) := by
  rw [sum_mul]
  simp_rw [seriesTerm_normalization_mul ha hq m]
  simp only [mul_div_assoc, mul_assoc]
  rw [← mul_sum]
  apply congrArg ((1 - a * q ^ (2 * m)) * ·)
  simpa only [mul_div_assoc, mul_assoc] using
    FiniteDifferencePolynomial.sum_coefficient_eval_div_one_sub hq0 hq
    (mul_ne_zero ha0 (pow_ne_zero _ hq0)) (2 * m) (by omega)
    (normalizationPolynomial a q m) (natDegree_normalizationPolynomial_le a q m)
    (QuadraticSummation.pochhammer_ne_zero_of_norm_lt_one
      (norm_mul_pow_lt_one ha hq (2 * m)) hq _)

/-- Reversing the two finite products gives the product normalization at the extra even node.
-/
lemma reversal_normalization {a q : ℂ} (ha0 : a ≠ 0) (hq0 : q ≠ 0) (m : ℕ) :
    (a * q ^ (2 * m)) ^ (2 * m) * qPochhammer q q (2 * m) *
        qPochhammer (a * q / (a * q ^ (2 * m)) ^ 2) (q ^ 2) m =
      qPochhammer q (q ^ 2) m * (interpolationPoint a q m) ^ m *
        qPochhammer (a * q / interpolationPoint a q m) (q ^ 2) m *
          qPochhammer (interpolationPoint a q m) (q ^ 2) m := by
  let u := a * q ^ (2 * m)
  let x := interpolationPoint a q m
  have hu0 : u ≠ 0 := mul_ne_zero ha0 (pow_ne_zero _ hq0)
  have hx0 : x ≠ 0 := mul_ne_zero ha0 (pow_ne_zero _ hq0)
  have hQ0 : q ^ 2 ≠ 0 := pow_ne_zero _ hq0
  have h1 : (q ^ 2) ^ (1 - (m : ℤ)) / (a * q / u ^ 2) = x := by
    rw [zpow_sub₀ hQ0, zpow_one, zpow_natCast]
    dsimp [x, u, interpolationPoint]
    rw [show q ^ (2 * m) = (q ^ 2) ^ m by rw [pow_mul],
      show q ^ (2 * m + 1) = (q ^ 2) ^ m * q by rw [pow_succ, pow_mul]]
    field_simp
  have h2 : (q ^ 2) ^ (1 - (m : ℤ)) / (a * q / x) = q ^ 2 := by
    rw [zpow_sub₀ hQ0, zpow_one, zpow_natCast]
    dsimp [x, interpolationPoint]
    rw [show q ^ (2 * m + 1) = (q ^ 2) ^ m * q by rw [pow_succ, pow_mul]]
    field_simp
  have hR1 := qPochhammer_reverse (div_ne_zero (mul_ne_zero ha0 hq0)
    (pow_ne_zero 2 hu0)) hQ0 m
  have hR2 := qPochhammer_reverse (div_ne_zero (mul_ne_zero ha0 hq0) hx0) hQ0 m
  rw [h1] at hR1
  rw [h2] at hR2
  have hF : qPochhammer q q (2 * m) =
      qPochhammer q (q ^ 2) m * qPochhammer (q ^ 2) (q ^ 2) m := by
    simpa only [qPochhammerList, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, ← pow_two] using qPochhammer_even q q m
  have hp1 : u ^ (2 * m) * (-(a * q / u ^ 2)) ^ m = (-a * q) ^ m := by
    rw [pow_mul, ← mul_pow]
    congr 1
    field_simp
  have hp2 : x ^ m * (-(a * q / x)) ^ m = (-a * q) ^ m := by
    rw [← mul_pow]
    congr 1
    field_simp
  change u ^ (2 * m) * qPochhammer q q (2 * m) *
    qPochhammer (a * q / u ^ 2) (q ^ 2) m = _
  rw [hR1, hR2, hF]
  calc
    _ = qPochhammer q (q ^ 2) m * qPochhammer (q ^ 2) (q ^ 2) m *
        qPochhammer x (q ^ 2) m * (q ^ 2) ^ m.choose 2 *
        (u ^ (2 * m) * (-(a * q / u ^ 2)) ^ m) := by ring
    _ = _ := by rw [hp1, ← hp2]; ring

/-- Evaluation of the product polynomial factors out the nonzero evaluation point. -/
lemma eval_valuePolynomial_even {a q x : ℂ} (hx0 : x ≠ 0) (m : ℕ) :
    (valuePolynomial a q (2 * m)).eval x =
      qPochhammer q (q ^ 2) m / qPochhammer (a * q) (q ^ 2) m *
        x ^ m * qPochhammer (a * q / x) (q ^ 2) m := by
  have hn : ¬Odd (2 * m) := by rintro ⟨j, hj⟩; omega
  simp only [valuePolynomial, ite_eq_right hn, show 2 * m / 2 = m by omega,
    eval_mul, eval_C, eval_prod, eval_sub, eval_X]
  rw [mul_assoc]
  congr 1
  rw [qPochhammer_eq_prod, show x ^ m = ∏ _j ∈ range m, x by simp,
    ← prod_mul_distrib]
  apply prod_congr rfl
  intro j hj
  rw [show q ^ (2 * j + 1) = q * (q ^ 2) ^ j by rw [pow_succ, pow_mul]; ring]
  field_simp

/-- The even normalization point gives the same value for the sum and product polynomials.
-/
lemma eval_sumPolynomial_normalization {a q : ℂ} (ha0 : a ≠ 0) (ha : ‖a‖ < 1)
    (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (m : ℕ) :
    (sumPolynomial a q (2 * m)).eval (interpolationPoint a q m) =
      (valuePolynomial a q (2 * m)).eval (interpolationPoint a q m) := by
  by_cases hm : m = 0
  · subst m
    simp [sumPolynomial, termPolynomial, valuePolynomial,
      FiniteDifferencePolynomial.coefficient]
  have hm0 : 0 < m := Nat.pos_of_ne_zero hm
  let u := a * q ^ (2 * m)
  let x := interpolationPoint a q m
  have hx : x = u * q := by dsimp [x, u, interpolationPoint]; rw [pow_succ]; ring
  have hx0 : x ≠ 0 := mul_ne_zero ha0 (pow_ne_zero _ hq0)
  have hux : ‖u‖ < 1 := norm_mul_pow_lt_one ha hq (2 * m)
  have hxx : ‖x‖ < 1 := norm_mul_pow_lt_one ha hq (2 * m + 1)
  have haq : ‖a * q‖ < 1 := by simpa using norm_mul_pow_lt_one ha hq 1
  have hQ : ‖q ^ 2‖ < 1 := by rw [norm_pow]; nlinarith [norm_nonneg q]
  have hA := QuadraticSummation.pochhammer_ne_zero_of_norm_lt_one haq hQ m
  have hX := QuadraticSummation.pochhammer_ne_zero_of_norm_lt_one hxx hQ m
  have hxq : ‖x * q‖ < 1 := by simpa using norm_mul_pow_lt_one hxx hq 1
  have hY := QuadraticSummation.pochhammer_ne_zero_of_norm_lt_one hxq hQ m
  have hu1 : 1 - u ≠ 0 := one_sub_ne_zero_of_norm_lt_one hux
  have hd : qPochhammer u q (2 * m + 1) =
      (1 - u) * qPochhammer x (q ^ 2) m * qPochhammer (x * q) (q ^ 2) m := by
    rw [qPochhammer_succ', qPochhammer_even, ← hx]
    simp [qPochhammerList, mul_assoc]
  have hS := sum_seriesTerm_normalization_mul ha0 ha hq0 hq m hm0
  change (∑ k ∈ range (2 * m + 1), seriesTerm a x q (2 * m) k) *
    qPochhammer (a * q) (q ^ 2) m =
      (1 - u) * (u ^ (2 * m) * qPochhammer q q (2 * m) /
        qPochhammer u q (2 * m + 1) * (normalizationPolynomial a q m).eval u⁻¹) at hS
  simp only [normalizationPolynomial, Polynomial.eval_comp, eval_pow, eval_X,
    DixonPolynomial.eval_pochhammerPolynomial, inv_pow, ← div_eq_mul_inv] at hS
  rw [hd] at hS
  have hR := reversal_normalization ha0 hq0 m
  change u ^ (2 * m) * qPochhammer q q (2 * m) *
    qPochhammer (a * q / u ^ 2) (q ^ 2) m =
      qPochhammer q (q ^ 2) m * x ^ m * qPochhammer (a * q / x) (q ^ 2) m *
        qPochhammer x (q ^ 2) m at hR
  rw [eval_sumPolynomial a _ q (2 * m)
    (QuadraticSummation.pochhammer_ne_zero_of_norm_lt_one hxx hq _),
    eval_valuePolynomial_even hx0 m]
  rw [show 2 * m / 2 = m by omega]
  change qPochhammer (x * q) (q ^ 2) m *
      (∑ k ∈ range (2 * m + 1), seriesTerm a x q (2 * m) k) =
    qPochhammer q (q ^ 2) m / qPochhammer (a * q) (q ^ 2) m * x ^ m *
      qPochhammer (a * q / x) (q ^ 2) m
  have hY' : qPochhammer (q * x) (q ^ 2) m ≠ 0 := by simpa [mul_comm] using hY
  field_simp [hA, hX, hY', hu1] at hS
  rw [mul_comm q x] at hS
  have hA' : qPochhammer (q * a) (q ^ 2) m ≠ 0 := by simpa [mul_comm] using hA
  apply mul_left_cancel₀ hA
  calc
    _ = qPochhammer q (q ^ 2) m * x ^ m * qPochhammer (a * q / x) (q ^ 2) m := by
      apply mul_right_cancel₀ hX
      linear_combination hS + hR
    _ = _ := by field_simp [hA']

/-- The product polynomial vanishes at the interpolation nodes of its displayed factors. -/
lemma eval_valuePolynomial_root (a q : ℂ) (n t : ℕ) (ht : 2 * t < n) :
    (valuePolynomial a q n).eval (interpolationPoint a q t) = 0 := by
  unfold valuePolynomial
  split
  · simp
  · rename_i hn
    have ht' : t < n / 2 := by
      have he := Nat.even_or_odd n
      rcases he with ⟨j, hj⟩ | ho
      · omega
      · exact (hn ho).elim
    simp only [eval_mul, eval_C, eval_prod, eval_sub, eval_X]
    rw [prod_eq_zero (Finset.mem_range.mpr ht') (by simp [interpolationPoint]), mul_zero]

/-- Interpolation proves the parity identity when the fixed parameter is in the punctured
unit disk. -/
lemma sumPolynomial_eq_valuePolynomial_of_norm_lt_one {a q : ℂ}
    (ha0 : a ≠ 0) (ha : ‖a‖ < 1) (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (n : ℕ) :
    sumPolynomial a q n = valuePolynomial a q n := by
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq (range (n / 2 + 1))
    (injective_interpolationPoint ha0 hq0 hq).injOn
  · apply Polynomial.degree_le_natDegree.trans_lt
    simp only [card_range]
    exact_mod_cast lt_of_le_of_lt (natDegree_sumPolynomial_le a q n) (Nat.lt_succ_self _)
  · apply Polynomial.degree_le_natDegree.trans_lt
    simp only [card_range]
    exact_mod_cast lt_of_le_of_lt (natDegree_valuePolynomial_le a q n) (Nat.lt_succ_self _)
  · intro t ht
    have htm : t ≤ n / 2 := by have := Finset.mem_range.mp ht; omega
    by_cases htn : 2 * t < n
    · rw [eval_sumPolynomial_root ha hq0 hq n t htn, eval_valuePolynomial_root a q n t htn]
    · have hn : n = 2 * t := by omega
      subst n
      exact eval_sumPolynomial_normalization ha0 ha hq0 hq t

/-- Clearing the fixed-parameter denominator gives a polynomial in that parameter. -/
def clearedSumPolynomial (x q : ℂ) (n : ℕ) : Polynomial ℂ :=
  ∑ k ∈ range (n + 1),
    C (FiniteDifferencePolynomial.coefficient q n k * (termPolynomial q (n / 2) k).eval x) *
      DixonPolynomial.pochhammerPolynomial (q ^ n) q k *
        DixonPolynomial.pochhammerPolynomial (q ^ (2 * k + 1)) (q ^ 2) (n - k)

/-- The product value with the same fixed-parameter denominator cleared. -/
def clearedValuePolynomial (x q : ℂ) (n : ℕ) : Polynomial ℂ :=
  if Odd n then 0 else
    C (qPochhammer q (q ^ 2) (n / 2)) *
      DixonPolynomial.pochhammerPolynomial (q ^ (2 * (n / 2) + 1)) (q ^ 2) (n - n / 2) *
        ∏ j ∈ range (n / 2), (C x - X * C (q ^ (2 * j + 1)))

/-- Evaluation of the cleared sum polynomial cancels the fixed shifted factorial. -/
lemma eval_clearedSumPolynomial (a x q : ℂ) (n : ℕ)
    (hA : qPochhammer (a * q) (q ^ 2) n ≠ 0) :
    (clearedSumPolynomial x q n).eval a =
      qPochhammer (a * q) (q ^ 2) n * (sumPolynomial a q n).eval x := by
  simp only [clearedSumPolynomial, sumPolynomial, eval_finsetSum, eval_mul, eval_C,
    DixonPolynomial.eval_pochhammerPolynomial, mul_sum]
  apply sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by have := Finset.mem_range.mp hk; omega
  have hAk := qPochhammer_ne_zero_of_le hA hkn
  have H := qPochhammer_add (a * q) (q ^ 2) k (n - k)
  rw [Nat.add_sub_cancel' hkn,
    show a * q * (q ^ 2) ^ k = a * q ^ (2 * k + 1) by rw [← pow_mul, pow_succ]; ring] at H
  have hr : qPochhammer (a * q ^ (2 * k + 1)) (q ^ 2) (n - k) =
      qPochhammer (a * q) (q ^ 2) n / qPochhammer (a * q) (q ^ 2) k := by
    apply (eq_div_iff hAk).mpr
    linear_combination -H
  rw [mul_comm (q ^ n) a, mul_comm (q ^ (2 * k + 1)) a, hr]
  ring

/-- Evaluation of the cleared value polynomial has the same normalization. -/
lemma eval_clearedValuePolynomial (a x q : ℂ) (n : ℕ)
    (hA : qPochhammer (a * q) (q ^ 2) n ≠ 0) :
    (clearedValuePolynomial x q n).eval a =
      qPochhammer (a * q) (q ^ 2) n * (valuePolynomial a q n).eval x := by
  unfold clearedValuePolynomial valuePolynomial
  split
  · simp
  · have hAm := qPochhammer_ne_zero_of_le hA (show n / 2 ≤ n by omega)
    have H := qPochhammer_add (a * q) (q ^ 2) (n / 2) (n - n / 2)
    rw [Nat.add_sub_cancel' (show n / 2 ≤ n by omega),
      show a * q * (q ^ 2) ^ (n / 2) = a * q ^ (2 * (n / 2) + 1) by
        rw [← pow_mul, pow_succ]; ring] at H
    have hr : qPochhammer (a * q ^ (2 * (n / 2) + 1)) (q ^ 2) (n - n / 2) =
        qPochhammer (a * q) (q ^ 2) n / qPochhammer (a * q) (q ^ 2) (n / 2) := by
      apply (eq_div_iff hAm).mpr
      linear_combination -H
    simp only [eval_mul, eval_C, eval_prod, eval_sub, eval_X,
      DixonPolynomial.eval_pochhammerPolynomial]
    rw [mul_comm (q ^ (2 * (n / 2) + 1)) a, hr]
    ring

/-- Polynomial continuation extends the parity identity to every regular fixed parameter. -/
lemma clearedSumPolynomial_eq_valuePolynomial {q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (x : ℂ) (n : ℕ) : clearedSumPolynomial x q n = clearedValuePolynomial x q n := by
  have hinj : Function.Injective (fun r : ℕ => q ^ (r + 1)) := by
    intro i j he
    have hn := congrArg norm he
    simp only [norm_pow] at hn
    have hh := (pow_right_strictAnti₀ (norm_pos_iff.mpr hq0) hq).injective hn
    omega
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective hinj).mono
  rintro a ⟨r, rfl⟩
  have ha : ‖q ^ (r + 1)‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq (by omega)
  have haq : ‖q ^ (r + 1) * q‖ < 1 := by simpa using norm_mul_pow_lt_one ha hq 1
  have hQ : ‖q ^ 2‖ < 1 := by rw [norm_pow]; nlinarith [norm_nonneg q]
  have hA := QuadraticSummation.pochhammer_ne_zero_of_norm_lt_one haq hQ n
  change (clearedSumPolynomial x q n).eval (q ^ (r + 1)) =
    (clearedValuePolynomial x q n).eval (q ^ (r + 1))
  rw [eval_clearedSumPolynomial _ _ _ _ hA, eval_clearedValuePolynomial _ _ _ _ hA,
    sumPolynomial_eq_valuePolynomial_of_norm_lt_one (pow_ne_zero _ hq0) ha hq0 hq]

/-- The sum and product polynomials agree for every parameter where the lower factorial is
regular, including the zero upper parameter. -/
lemma eval_sumPolynomial_eq_valuePolynomial {q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (a x : ℂ) (n : ℕ) (hA : qPochhammer (a * q) (q ^ 2) n ≠ 0) :
    (sumPolynomial a q n).eval x = (valuePolynomial a q n).eval x := by
  have H := congrArg (fun P : Polynomial ℂ => P.eval a)
    (clearedSumPolynomial_eq_valuePolynomial hq0 hq x n)
  rw [eval_clearedSumPolynomial _ _ _ _ hA, eval_clearedValuePolynomial _ _ _ _ hA] at H
  exact mul_left_cancel₀ hA H

/-- The finite parity sum equals its product value on the full natural regularity domain. -/
lemma sum_seriesTerm_eq {q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (a x : ℂ) (n : ℕ)
    (hA : qPochhammer (a * q) (q ^ 2) n ≠ 0) (hX : qPochhammer x q n ≠ 0) :
    ∑ k ∈ range (n + 1), seriesTerm a x q n k =
      if Odd n then 0 else
        qPochhammer q (q ^ 2) (n / 2) *
          (∏ j ∈ range (n / 2), (x - a * q ^ (2 * j + 1))) /
          (qPochhammer (a * q) (q ^ 2) (n / 2) *
            qPochhammer (x * q) (q ^ 2) (n / 2)) := by
  have hXe := qPochhammer_ne_zero_of_le hX (show 2 * (n / 2) ≤ n by omega)
  rw [qPochhammer_even] at hXe
  have hXP : qPochhammer x (q ^ 2) (n / 2) *
      qPochhammer (x * q) (q ^ 2) (n / 2) ≠ 0 := by
    simpa only [qPochhammerList, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one] using hXe
  have hY := right_ne_zero_of_mul hXP
  have H := eval_sumPolynomial_eq_valuePolynomial hq0 hq a x n hA
  rw [eval_sumPolynomial a x q n hX] at H
  by_cases hn : Odd n
  · simp only [valuePolynomial, ite_eq_left hn, eval_zero] at H ⊢
    exact (mul_eq_zero.mp H).resolve_left hY
  · simp only [valuePolynomial, ite_eq_right hn, eval_mul, eval_C, eval_prod,
      eval_sub, eval_X] at H ⊢
    calc
      _ = (qPochhammer q (q ^ 2) (n / 2) / qPochhammer (a * q) (q ^ 2) (n / 2) *
          ∏ j ∈ range (n / 2), (x - a * q ^ (2 * j + 1))) /
          qPochhammer (x * q) (q ^ 2) (n / 2) := by
        apply (eq_div_iff hY).mpr
        linear_combination H
      _ = _ := by ring

/-- Pairing opposite upper and lower parameters puts each q-Watson term in finite-product form.
-/
lemma qPhiTerm_eq_seriesTerm (a c q : ℂ) (n k : ℕ) :
    qPhiTerm [q ^ (-(n : ℤ)), a * q ^ n, c, -c]
      [Complex.sqrt (a * q), -Complex.sqrt (a * q), c ^ 2] q q k =
      seriesTerm a (c ^ 2) q n k := by
  have he : qPhiExponent [q ^ (-(n : ℤ)), a * q ^ n, c, -c]
      [Complex.sqrt (a * q), -Complex.sqrt (a * q), c ^ 2] = 0 := by simp [qPhiExponent]
  have hU := qPochhammer_squared c q k
  have hL := qPochhammer_squared (Complex.sqrt (a * q)) q k
  have hs : (Complex.sqrt (a * q)) ^ 2 = a * q := by
    rw [Complex.sqrt, ← Complex.cpow_nat_mul]; norm_num
  rw [hs] at hL
  simp only [qPhiTerm, he, zpow_zero, mul_one, qPochhammerList, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil, seriesTerm,
    FiniteDifferencePolynomial.coefficient]
  rw [hU, hL]
  ring

/-- The terminating q-Watson summation, retaining all regular zero upper parameters. -/
lemma four_phi_three_parity {a c q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (n : ℕ)
    (hd : QDenominatorRegularThrough [Complex.sqrt (a * q), -Complex.sqrt (a * q), c ^ 2] q n) :
    qPhi [q ^ (-(n : ℤ)), a * q ^ n, c, -c]
      [Complex.sqrt (a * q), -Complex.sqrt (a * q), c ^ 2] q q =
      if Odd n then 0 else qPochhammer q (q ^ 2) (n / 2) *
        (∏ j ∈ range (n / 2), (c ^ 2 - a * q ^ (2 * j + 1))) /
          qPochhammerList [a * q, c ^ 2 * q] (q ^ 2) (n / 2) := by
  have hDP : qPochhammer (Complex.sqrt (a * q)) q n *
      qPochhammer (-Complex.sqrt (a * q)) q n * qPochhammer (c ^ 2) q n ≠ 0 := by
    simpa only [QDenominatorRegularThrough, qPochhammerList, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, mul_one, ← mul_assoc] using hd
  have hA := left_ne_zero_of_mul hDP
  have hX := right_ne_zero_of_mul hDP
  have hs : (Complex.sqrt (a * q)) ^ 2 = a * q := by
    rw [Complex.sqrt, ← Complex.cpow_nat_mul]; norm_num
  rw [← qPochhammer_squared, hs] at hA
  rw [qPhi_terminates hq0 n, qPhiPartial]
  simp_rw [qPhiTerm_eq_seriesTerm]
  simpa only [qPochhammerList, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one] using sum_seriesTerm_eq hq0 hq a (c ^ 2) n hA hX

end DLMF.QHypergeometric.ParitySummation
