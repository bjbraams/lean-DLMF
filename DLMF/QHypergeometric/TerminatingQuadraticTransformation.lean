/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.PfaffSaalschutz
public import DLMF.QHypergeometric.Transformations
public import DLMF.QHypergeometric.DixonPolynomial
public import Mathlib.Algebra.Polynomial.BigOperators

/-!
# The terminating quadratic three-phi-two transformation

Finite q-binomial coefficients convert the terminating quadratic transformation of
DLMF 17.9.17 to a finite q-Pfaff–Saalschütz sum. The polynomial shifted factorial is reused
from `DixonPolynomial.pochhammerPolynomial`; all lower-parameter products are retained.
-/

@[expose] public noncomputable section

open Complex Filter Finset Set Polynomial
open scoped Topology
open DLMF.QSeries

namespace DLMF.QHypergeometric.QuadraticTransformation

/-- The polynomial shifted factorial has the finite q-binomial expansion. -/
lemma pochhammerPolynomial_eq_sum (u q : ℂ) (N : ℕ) :
    DixonPolynomial.pochhammerPolynomial u q N =
      ∑ j ∈ range (N + 1), monomial j (qBinom q N j * (-1) ^ j * q ^ j.choose 2 * u ^ j) := by
  apply Polynomial.funext
  intro z
  simp only [DixonPolynomial.eval_pochhammerPolynomial, eval_finsetSum, eval_monomial]
  rw [qPochhammer_eq_sum_qBinom]
  apply sum_congr rfl
  intro j hj
  rw [mul_pow]
  ring

/-- Coefficients of a finite shifted factorial are Gaussian binomial coefficients. -/
lemma coeff_pochhammerPolynomial (u q : ℂ) (N j : ℕ) :
    (DixonPolynomial.pochhammerPolynomial u q N).coeff j =
      qBinom q N j * (-1) ^ j * q ^ j.choose 2 * u ^ j := by
  rw [pochhammerPolynomial_eq_sum, finsetSum_coeff]
  by_cases hj : j ≤ N
  · rw [sum_eq_single j]
    · simp
    · intro k hk hkj
      simp [coeff_monomial, hkj]
    · intro hjN
      exact (hjN (Finset.mem_range.mpr (by omega))).elim
  · have hNj : N < j := Nat.lt_of_not_ge hj
    rw [qBinom_eq_zero_of_lt q hNj]
    simp only [zero_mul]
    apply sum_eq_zero
    intro k hk
    have hkj : k ≠ j := by have := Finset.mem_range.mp hk; omega
    simp [coeff_monomial, hkj]

/-- The four half-power upper factors combine to one even-index shifted factorial. -/
lemma half_power_pairs (a q : ℂ) (k : ℕ) :
    qPochhammer (a ^ (1 / 2 : ℂ)) q k * qPochhammer (-(a ^ (1 / 2 : ℂ))) q k *
      (qPochhammer ((a * q) ^ (1 / 2 : ℂ)) q k *
        qPochhammer (-((a * q) ^ (1 / 2 : ℂ))) q k) = qPochhammer a q (2 * k) := by
  have ha : (a ^ (1 / 2 : ℂ)) ^ 2 = a := by rw [← Complex.cpow_nat_mul]; norm_num
  have haq : ((a * q) ^ (1 / 2 : ℂ)) ^ 2 = a * q := by
    rw [← Complex.cpow_nat_mul]; norm_num
  rw [← qPochhammer_squared, ← qPochhammer_squared, ha, haq, qPochhammer_even]
  simp [qPochhammerList]

/-- The infinite prefactor of the quadratic transformation is a finite shifted factorial. -/
lemma qPochhammerInf_ratio_eq {q z : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hz : qPochhammerInf z q ≠ 0) (N : ℕ) :
    qPochhammerInf (q ^ (-(N : ℤ)) * z) q / qPochhammerInf z q =
      qPochhammer (q ^ (-(N : ℤ)) * z) q N := by
  have he : q ^ (-(N : ℤ)) * z * q ^ N = z := by
    rw [mul_right_comm, ← zpow_natCast q N, ← zpow_add₀ hq0]
    simp
  rw [qPochhammerInf_mul_qPochhammer hq N, he]
  field_simp

/-- Pairing the half-power parameters gives an even-index numerator in each quadratic term. -/
lemma qPhiTerm_half_power_pairs (a b c q z : ℂ) (k : ℕ) :
    qPhiTerm [a ^ (1 / 2 : ℂ), -(a ^ (1 / 2 : ℂ)), (a * q) ^ (1 / 2 : ℂ),
        -((a * q) ^ (1 / 2 : ℂ)), a * q / (b * c)] [a * q / b, a * q / c, a * z, q / z]
      q q k =
      qPochhammer a q (2 * k) * qPochhammer (a * q / (b * c)) q k /
        (qPochhammer (a * q / b) q k * qPochhammer (a * q / c) q k *
          qPochhammer (a * z) q k * qPochhammer (q / z) q k * qPochhammer q q k) * q ^ k := by
  have he : qPhiExponent [a ^ (1 / 2 : ℂ), -(a ^ (1 / 2 : ℂ)), (a * q) ^ (1 / 2 : ℂ),
      -((a * q) ^ (1 / 2 : ℂ)), a * q / (b * c)] [a * q / b, a * q / c, a * z, q / z] = 0 := by
    simp [qPhiExponent]
  have H := half_power_pairs a q k
  simp only [qPhiTerm, he, zpow_zero, mul_one, qPochhammerList, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil]
  linear_combination (qPochhammer (a * q / (b * c)) q k * q ^ k /
    (qPochhammer (a * q / b) q k * qPochhammer (a * q / c) q k *
      qPochhammer (a * z) q k * qPochhammer (q / z) q k * qPochhammer q q k)) * H

/-- The finite product quotient left after multiplying the quadratic prefactor reverses to
an ordinary shifted factorial in `z`. -/
lemma finite_prefactor_ratio {q z : ℂ} (hq0 : q ≠ 0) (hz0 : z ≠ 0) (N k : ℕ)
    (hk : 2 * k ≤ N)
    (hA : qPochhammer (q ^ (-(N : ℤ)) * z) q k ≠ 0)
    (hQ : qPochhammer (q / z) q k ≠ 0) :
    qPochhammer (q ^ (-(N : ℤ)) * z) q N /
        (qPochhammer (q ^ (-(N : ℤ)) * z) q k * qPochhammer (q / z) q k) * q ^ k =
      (-z) ^ k * q ^ (-(k.choose 2 : ℤ)) *
        qPochhammer (z * q ^ ((k : ℤ) - N)) q (N - 2 * k) := by
  have he1 : q ^ (-(N : ℤ)) * z * q ^ k = z * q ^ ((k : ℤ) - N) := by
    rw [mul_right_comm, ← zpow_natCast q k, ← zpow_add₀ hq0]
    rw [show -(N : ℤ) + (k : ℤ) = (k : ℤ) - N by ring]
    ring
  have he2 : z * q ^ ((k : ℤ) - N) * q ^ (N - 2 * k) = z * q ^ (-(k : ℤ)) := by
    rw [mul_assoc, ← zpow_natCast q (N - 2 * k), ← zpow_add₀ hq0]
    congr 2
    omega
  have hsplit := qPochhammer_add (q ^ (-(N : ℤ)) * z) q k (N - k)
  rw [Nat.add_sub_cancel' (by omega : k ≤ N), he1] at hsplit
  have hmiddle := qPochhammer_add (z * q ^ ((k : ℤ) - N)) q (N - 2 * k) k
  rw [show N - 2 * k + k = N - k by omega, he2] at hmiddle
  rw [hmiddle, qPochhammer_shift_negative hz0 hq0 k] at hsplit
  rw [hsplit, div_pow]
  field_simp [hA, hQ]

/-- Factoring out a nonzero constant converts a finite linear product to a shifted factorial.
-/
lemma prod_sub_eq_qPochhammer {a : ℂ} (ha : a ≠ 0) (d q : ℂ) (n : ℕ) :
    (∏ j ∈ range n, (a - d * q ^ j)) = a ^ n * qPochhammer (d / a) q n := by
  rw [qPochhammer_eq_prod, show a ^ n = ∏ _j ∈ range n, a by simp,
    ← Finset.prod_mul_distrib]
  apply prod_congr rfl
  intro j hj
  field_simp

/-- The nonzero-parameter product form of the finite q-Pfaff–Saalschütz identity. -/
lemma q_pfaff_saalschutz_ratio {u v d q : ℂ} (hu : u ≠ 0) (hv : v ≠ 0) (hd : d ≠ 0)
    (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (j : ℕ)
    (hreg : QDenominatorRegularThrough [d, u * v * q ^ (1 - (j : ℤ)) / d] q j) :
    qPhi [u, v, q ^ (-(j : ℤ))] [d, u * v * q ^ (1 - (j : ℤ)) / d] q q =
      qPochhammer (d / u) q j * qPochhammer (d / v) q j /
        (qPochhammer d q j * qPochhammer (d / (u * v)) q j) := by
  have H := q_pfaff_saalschutz hd hq0 hq j hreg
  rw [prod_sub_eq_qPochhammer hu, prod_sub_eq_qPochhammer hv,
    prod_sub_eq_qPochhammer (mul_ne_zero hu hv)] at H
  rw [H]
  simp only [div_eq_mul_inv, mul_inv_rev, mul_pow]
  field_simp [hu, hv]

/-- A terminating shifted factorial expressed with ordinary q-factorial products. -/
lemma qPochhammer_terminating {q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (N k : ℕ) (hk : k ≤ N) :
    qPochhammer (q ^ (-(N : ℤ))) q k =
      qPochhammer q q N / qPochhammer q q (N - k) * (-1) ^ k *
        q ^ ((k.choose 2 : ℤ) - (N : ℤ) * k) := by
  have hQ := qPochhammer_self_ne_zero hq (N - k)
  have he : q ^ (1 - (k : ℤ)) / q ^ (-(N : ℤ)) = q * q ^ (N - k) := by
    rw [← zpow_sub₀ hq0, show (1 - (k : ℤ)) - (-(N : ℤ)) = (N - k : ℕ) + 1 by omega,
      zpow_add₀ hq0, zpow_natCast, zpow_one]
    ring
  have hsplit := qPochhammer_add q q (N - k) k
  rw [Nat.sub_add_cancel hk] at hsplit
  have hpart : qPochhammer (q * q ^ (N - k)) q k =
      qPochhammer q q N / qPochhammer q q (N - k) := by
    apply (eq_div_iff hQ).mpr
    linear_combination -hsplit
  have hp : (q ^ (-(N : ℤ))) ^ k * q ^ k.choose 2 =
      q ^ ((k.choose 2 : ℤ) - (N : ℤ) * k) := by
    rw [← zpow_natCast (q ^ (-(N : ℤ))) k, ← zpow_mul,
      ← zpow_natCast q (k.choose 2), ← zpow_add₀ hq0]
    congr 1
    ring
  rw [qPochhammer_reverse (zpow_ne_zero _ hq0) hq0, he, hpart, neg_pow]
  rw [mul_assoc, mul_assoc, hp]
  ring

/-- The balanced finite three-phi-two sum occurring in a coefficient of the quadratic identity.
-/
lemma balanced_inner_sum {b c q : ℂ} (hb0 : b ≠ 0) (hc0 : c ≠ 0)
    (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (N j : ℕ) (hj : j ≤ N)
    (hreg : QDenominatorRegular [q ^ (-(N : ℤ)) * q / b, q ^ (-(N : ℤ)) * q / c] q) :
    qPhi [q ^ (-(j : ℤ)), q ^ (-((N - j : ℕ) : ℤ)), q ^ (-(N : ℤ)) * q / (b * c)]
        [q ^ (-(N : ℤ)) * q / b, q ^ (-(N : ℤ)) * q / c] q q =
      qPochhammer b q j * qPochhammer c q j /
        (qPochhammer (q ^ (-(N : ℤ)) * q / b) q j *
          qPochhammer (q ^ (-(N : ℤ)) * q / c) q j) *
      (q ^ (-(N : ℤ)) * q / (b * c)) ^ j := by
  let A := q ^ (-(N : ℤ))
  let u := q ^ (-((N - j : ℕ) : ℤ))
  let v := A * q / (b * c)
  let D := A * q / b
  let E := A * q / c
  have hA0 : A ≠ 0 := zpow_ne_zero _ hq0
  have hu0 : u ≠ 0 := zpow_ne_zero _ hq0
  have hv0 : v ≠ 0 := div_ne_zero (mul_ne_zero hA0 hq0) (mul_ne_zero hb0 hc0)
  have hD0 : D ≠ 0 := div_ne_zero (mul_ne_zero hA0 hq0) hb0
  have hE0 : E ≠ 0 := div_ne_zero (mul_ne_zero hA0 hq0) hc0
  have hp : u * q ^ (1 - (j : ℤ)) = A * q := by
    dsimp [u, A]
    calc
      _ = q ^ (-((N - j : ℕ) : ℤ) + (1 - (j : ℤ))) := (zpow_add₀ hq0 _ _).symm
      _ = q ^ (-(N : ℤ) + 1) := by congr 1; omega
      _ = q ^ (-(N : ℤ)) * q := by rw [zpow_add₀ hq0, zpow_one]
  have hbottom : u * v * q ^ (1 - (j : ℤ)) / D = E := by
    dsimp [v, D, E]
    field_simp
    linear_combination hp
  have hregD : QDenominatorRegular [D] q := by
    intro x hx k
    simp only [List.mem_singleton] at hx
    subst x
    exact hreg D (by simp [D, A]) k
  have hregE : QDenominatorRegular [E] q := by
    intro x hx k
    simp only [List.mem_singleton] at hx
    subst x
    exact hreg E (by simp [E, A]) k
  have hD := qPochhammer_ne_zero_of_qDenominatorRegular hq hregD j
  have hE := qPochhammer_ne_zero_of_qDenominatorRegular hq hregE j
  have hthrough : QDenominatorRegularThrough [D, u * v * q ^ (1 - (j : ℤ)) / D] q j := by
    simpa [QDenominatorRegularThrough, qPochhammerList, hbottom] using mul_ne_zero hD hE
  have H := q_pfaff_saalschutz_ratio hu0 hv0 hD0 hq0 hq j hthrough
  rw [hbottom] at H
  have hdv : D / v = c := by dsimp [D, v]; field_simp
  have hdu : D / u = q ^ (1 - (j : ℤ)) / b := by
    dsimp [D]
    field_simp
    linear_combination -hp
  have hduv : D / (u * v) = c * q ^ (N - j) := by
    dsimp [D, v, u]
    rw [zpow_neg, zpow_natCast]
    field_simp
  rw [hdv, hdu, hduv] at H
  have hswap : qPhi [q ^ (-(j : ℤ)), u, v] [D, E] q q = qPhi [u, v, q ^ (-(j : ℤ))] [D, E] q q := by
    unfold qPhi
    apply tsum_congr
    intro k
    simp [qPhiTerm, qPhiExponent, qPochhammerList, mul_assoc, mul_comm]
  change qPhi [q ^ (-(j : ℤ)), u, v] [D, E] q q = _
  rw [hswap, H]
  change _ = qPochhammer b q j * qPochhammer c q j /
    (qPochhammer D q j * qPochhammer E q j) * v ^ j
  have huInv : q ^ (N - j) * u = 1 := by
    dsimp [u]
    rw [zpow_neg, zpow_natCast]
    field_simp
  have hshiftpower : q ^ (1 - (j : ℤ)) = q ^ (N - j) * (A * q) := by
    calc
      _ = (q ^ (N - j) * u) * q ^ (1 - (j : ℤ)) := by rw [huInv, one_mul]
      _ = _ := by rw [mul_assoc, hp]
  have hearg : q ^ (1 - (j : ℤ)) / E = c * q ^ (N - j) := by
    dsimp [E]
    field_simp
    linear_combination hshiftpower
  have HR := qPochhammer_reverse_ratio hb0 hE0 hq0 j
  rw [hearg] at HR
  have hratio : qPochhammer (q ^ (1 - (j : ℤ)) / b) q j /
      qPochhammer (c * q ^ (N - j)) q j =
      qPochhammer b q j / qPochhammer E q j * (E / b) ^ j := by
    rw [HR, mul_assoc, ← mul_pow]
    rw [show b / E * (E / b) = 1 by field_simp, one_pow, mul_one]
  have hv : v = E / b := by dsimp [E, v]; ring
  rw [hv]
  calc
    _ = (qPochhammer (q ^ (1 - (j : ℤ)) / b) q j /
        qPochhammer (c * q ^ (N - j)) q j) * (qPochhammer c q j / qPochhammer D q j) := by ring
    _ = _ := by rw [hratio]; ring

/-- The q-power balance in the coefficient of a quadratic summand. -/
lemma coefficient_power_balance {q : ℂ} (hq0 : q ≠ 0) (N j k : ℕ)
    (hj : j ≤ N) (hk : k ≤ j) :
    q ^ (((2 * k).choose 2 : ℤ) - (N : ℤ) * (2 * k)) * q ^ (-(k.choose 2 : ℤ)) *
        q ^ (j - k).choose 2 * (q ^ ((k : ℤ) - N)) ^ (j - k) =
      q ^ ((j.choose 2 : ℤ) - (N : ℤ) * j) * q ^ ((k.choose 2 : ℤ) - (j : ℤ) * k) *
        q ^ ((k.choose 2 : ℤ) - ((N - j : ℕ) : ℤ) * k) * q ^ k := by
  have hchoose (x : ℕ) : (x.choose 2 : ℤ) * 2 + x = (x : ℤ) * x := by
    exact_mod_cast choose_two_mul_two_add_self x
  have h0 := hchoose (2 * k)
  have h1 := hchoose k
  have h2 := hchoose (j - k)
  have h3 := hchoose j
  rw [Nat.cast_sub hk] at h2
  push_cast at h0
  rw [← zpow_natCast q ((j - k).choose 2),
    ← zpow_natCast (q ^ ((k : ℤ) - N)) (j - k), ← zpow_mul, ← zpow_natCast q k]
  simp only [← zpow_add₀ hq0]
  congr 1
  rw [Nat.cast_sub hk, Nat.cast_sub hj]
  nlinarith

/-- The coefficient contributed by a quadratic summand is a balanced three-phi-two term
multiplied by the common terminating factor. -/
lemma coefficient_factor {q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (N j k : ℕ)
    (hj : j ≤ N) (hkj : k ≤ j) (hkn : k ≤ N - j) :
    qPochhammer (q ^ (-(N : ℤ))) q (2 * k) * (-1) ^ k * q ^ (-(k.choose 2 : ℤ)) *
        (qBinom q (N - 2 * k) (j - k) * (-1) ^ (j - k) * q ^ (j - k).choose 2 *
          (q ^ ((k : ℤ) - N)) ^ (j - k)) =
      (qPochhammer (q ^ (-(N : ℤ))) q j / qPochhammer q q j) *
        qPochhammer (q ^ (-(j : ℤ))) q k * qPochhammer (q ^ (-((N - j : ℕ) : ℤ))) q k *
        q ^ k := by
  have hk2 : 2 * k ≤ N := by omega
  have hR := qPochhammer_self_ne_zero hq (j - k)
  have hS := qPochhammer_self_ne_zero hq (N - j - k)
  have hT := qPochhammer_self_ne_zero hq (N - 2 * k)
  have hJ := qPochhammer_self_ne_zero hq j
  have hNJ := qPochhammer_self_ne_zero hq (N - j)
  have hB := qBinom_mul_qPochhammer q (j - k) (N - j - k)
  rw [show j - k + (N - j - k) = N - 2 * k by omega] at hB
  have hBratio : qBinom q (N - 2 * k) (j - k) =
      qPochhammer q q (N - 2 * k) /
        (qPochhammer q q (j - k) * qPochhammer q q (N - j - k)) := by
    apply (eq_div_iff (mul_ne_zero hR hS)).mpr
    linear_combination hB
  let L := q ^ (((2 * k).choose 2 : ℤ) - (N : ℤ) * (2 * k)) * q ^ (-(k.choose 2 : ℤ)) *
    q ^ (j - k).choose 2 * (q ^ ((k : ℤ) - N)) ^ (j - k)
  let R := q ^ ((j.choose 2 : ℤ) - (N : ℤ) * j) *
    q ^ ((k.choose 2 : ℤ) - (j : ℤ) * k) *
    q ^ ((k.choose 2 : ℤ) - ((N - j : ℕ) : ℤ) * k) * q ^ k
  let C := qPochhammer q q N /
    (qPochhammer q q (j - k) * qPochhammer q q (N - j - k))
  have hpower : L = R := coefficient_power_balance hq0 N j k hj hkj
  have hs2 : (-1 : ℂ) ^ (2 * k) = 1 := by simp [pow_mul]
  have hs : (-1 : ℂ) ^ (2 * k) * (-1) ^ k * (-1) ^ (j - k) = (-1) ^ j := by
    rw [hs2, one_mul, ← pow_add, Nat.add_sub_of_le hkj]
  have hss : (-1 : ℂ) ^ k * (-1) ^ k = 1 := by rw [← mul_pow]; norm_num
  calc
    _ = C * ((-1 : ℂ) ^ (2 * k) * (-1) ^ k * (-1) ^ (j - k)) * L := by
      rw [qPochhammer_terminating hq0 hq N (2 * k) hk2, hBratio]
      dsimp [C, L]
      field_simp [hR, hS, hT]
    _ = C * (-1) ^ j * R := by rw [hs, hpower]
    _ = C * ((-1) ^ j * ((-1) ^ k * (-1) ^ k)) * R := by rw [hss, mul_one]
    _ = _ := by
      rw [qPochhammer_terminating hq0 hq N j hj,
        qPochhammer_terminating hq0 hq j k hkj,
        qPochhammer_terminating hq0 hq (N - j) k hkn]
      dsimp [C, R]
      field_simp [hR, hS, hJ, hNJ]

/-- The scalar multiplying the shifted-factorial polynomial in a quadratic summand. -/
def summandCoefficient (b c q : ℂ) (N k : ℕ) : ℂ :=
  qPochhammer (q ^ (-(N : ℤ))) q (2 * k) *
    qPochhammer (q ^ (-(N : ℤ)) * q / (b * c)) q k /
      (qPochhammer (q ^ (-(N : ℤ)) * q / b) q k *
        qPochhammer (q ^ (-(N : ℤ)) * q / c) q k * qPochhammer q q k) *
    (-1) ^ k * q ^ (-(k.choose 2 : ℤ))

/-- The polynomial obtained after multiplying the five-phi-four series by its finite prefactor.
-/
def quadraticPolynomial (b c q : ℂ) (N : ℕ) : Polynomial ℂ :=
  ∑ k ∈ range (N / 2 + 1), C (summandCoefficient b c q N k) *
    (X ^ k * DixonPolynomial.pochhammerPolynomial (q ^ ((k : ℤ) - N)) q (N - 2 * k))

/-- The coefficient of the terminating three-phi-two on the other side. -/
def leftCoefficient (b c q : ℂ) (N j : ℕ) : ℂ :=
  qPochhammer (q ^ (-(N : ℤ))) q j * qPochhammer b q j * qPochhammer c q j /
    (qPochhammer (q ^ (-(N : ℤ)) * q / b) q j *
      qPochhammer (q ^ (-(N : ℤ)) * q / c) q j * qPochhammer q q j) *
    (q ^ (-(N : ℤ)) * q / (b * c)) ^ j

/-- Each coefficient of a quadratic summand is its corresponding balanced finite-series term.
-/
lemma coeff_summand {b c q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (N j k : ℕ) (hj : j ≤ N) (hk : 2 * k ≤ N) :
    (C (summandCoefficient b c q N k) *
        (X ^ k * DixonPolynomial.pochhammerPolynomial (q ^ ((k : ℤ) - N)) q (N - 2 * k))).coeff j =
      (qPochhammer (q ^ (-(N : ℤ))) q j / qPochhammer q q j) *
        qPhiTerm [q ^ (-(j : ℤ)), q ^ (-((N - j : ℕ) : ℤ)),
          q ^ (-(N : ℤ)) * q / (b * c)]
          [q ^ (-(N : ℤ)) * q / b, q ^ (-(N : ℤ)) * q / c] q q k := by
  rw [coeff_C_mul, coeff_X_pow_mul']
  by_cases hkj : k ≤ j
  · rw [ite_eq_left hkj, coeff_pochhammerPolynomial]
    by_cases hkn : k ≤ N - j
    · have H := coefficient_factor hq0 hq N j k hj hkj hkn
      have he : qPhiExponent [q ^ (-(j : ℤ)), q ^ (-((N - j : ℕ) : ℤ)),
          q ^ (-(N : ℤ)) * q / (b * c)]
          [q ^ (-(N : ℤ)) * q / b, q ^ (-(N : ℤ)) * q / c] = 0 := by simp [qPhiExponent]
      simp only [summandCoefficient, qPhiTerm, he, zpow_zero, mul_one, qPochhammerList,
        List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
      linear_combination (qPochhammer (q ^ (-(N : ℤ)) * q / (b * c)) q k /
        (qPochhammer (q ^ (-(N : ℤ)) * q / b) q k *
          qPochhammer (q ^ (-(N : ℤ)) * q / c) q k * qPochhammer q q k)) * H
    · have hbin : qBinom q (N - 2 * k) (j - k) = 0 :=
        qBinom_eq_zero_of_lt q (by omega)
      have hzero : qPochhammer (q ^ (-((N - j : ℕ) : ℤ))) q k = 0 := by
        simpa only [zpow_neg, zpow_natCast] using
          qPochhammer_recip_pow_eq_zero hq0 (Nat.lt_of_not_ge hkn)
      simp only [hbin, zero_mul, mul_zero, qPhiTerm, qPochhammerList,
        List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
      rw [hzero]
      simp
  · have hzero : qPochhammer (q ^ (-(j : ℤ))) q k = 0 := by
      simpa only [zpow_neg, zpow_natCast] using
        qPochhammer_recip_pow_eq_zero hq0 (Nat.lt_of_not_ge hkj)
    simp only [ite_eq_right hkj, mul_zero, qPhiTerm, qPochhammerList,
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
    rw [hzero]
    simp

/-- Coefficients above the terminating degree vanish in every quadratic summand. -/
lemma coeff_summand_eq_zero_of_lt {b c q : ℂ} (N j k : ℕ) (hj : N < j) (hk : 2 * k ≤ N) :
    (C (summandCoefficient b c q N k) *
      (X ^ k * DixonPolynomial.pochhammerPolynomial
        (q ^ ((k : ℤ) - N)) q (N - 2 * k))).coeff j = 0 := by
  rw [coeff_C_mul, coeff_X_pow_mul', ite_eq_left (by omega : k ≤ j),
    coeff_pochhammerPolynomial, qBinom_eq_zero_of_lt q (by omega)]
  ring

/-- The quadratic polynomial's coefficients are evaluated by the finite q-Saalschütz sum. -/
lemma coeff_quadraticPolynomial {b c q : ℂ} (hb0 : b ≠ 0) (hc0 : c ≠ 0)
    (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (N j : ℕ)
    (hreg : QDenominatorRegular [q ^ (-(N : ℤ)) * q / b, q ^ (-(N : ℤ)) * q / c] q) :
    (quadraticPolynomial b c q N).coeff j = if j ≤ N then leftCoefficient b c q N j else 0 := by
  rw [quadraticPolynomial, finsetSum_coeff]
  by_cases hj : j ≤ N
  · rw [ite_eq_left hj]
    have he (k : ℕ) (hk : k ∈ range (N / 2 + 1)) : 2 * k ≤ N := by
      have := Finset.mem_range.mp hk
      omega
    have hcs : ∑ k ∈ range (N / 2 + 1),
        (C (summandCoefficient b c q N k) *
          (X ^ k * DixonPolynomial.pochhammerPolynomial
            (q ^ ((k : ℤ) - N)) q (N - 2 * k))).coeff j =
        ∑ k ∈ range (N / 2 + 1),
          (qPochhammer (q ^ (-(N : ℤ))) q j / qPochhammer q q j) *
          qPhiTerm [q ^ (-(j : ℤ)), q ^ (-((N - j : ℕ) : ℤ)),
            q ^ (-(N : ℤ)) * q / (b * c)]
            [q ^ (-(N : ℤ)) * q / b, q ^ (-(N : ℤ)) * q / c] q q k := by
      apply sum_congr rfl
      intro k hk
      exact coeff_summand hq0 hq N j k hj (he k hk)
    rw [hcs]
    have hs : qPhi [q ^ (-(j : ℤ)), q ^ (-((N - j : ℕ) : ℤ)),
        q ^ (-(N : ℤ)) * q / (b * c)] [q ^ (-(N : ℤ)) * q / b, q ^ (-(N : ℤ)) * q / c] q q =
        ∑ k ∈ range (N / 2 + 1), qPhiTerm [q ^ (-(j : ℤ)), q ^ (-((N - j : ℕ) : ℤ)),
          q ^ (-(N : ℤ)) * q / (b * c)] [q ^ (-(N : ℤ)) * q / b, q ^ (-(N : ℤ)) * q / c] q q k := by
      unfold qPhi
      apply tsum_eq_sum
      intro k hk
      have hk' : N / 2 < k := by simpa using hk
      by_cases hkj : j < k
      · have hzero : qPochhammer (q ^ (-(j : ℤ))) q k = 0 := by
          simpa only [zpow_neg, zpow_natCast] using qPochhammer_recip_pow_eq_zero hq0 hkj
        simp only [qPhiTerm, qPochhammerList, List.map_cons, List.map_nil,
          List.prod_cons, List.prod_nil]
        rw [hzero]
        simp
      · have hkn : N - j < k := by omega
        have hzero : qPochhammer (q ^ (-((N - j : ℕ) : ℤ))) q k = 0 := by
          simpa only [zpow_neg, zpow_natCast] using qPochhammer_recip_pow_eq_zero hq0 hkn
        simp only [qPhiTerm, qPochhammerList, List.map_cons, List.map_nil,
          List.prod_cons, List.prod_nil]
        rw [hzero]
        simp
    rw [← mul_sum, ← hs, balanced_inner_sum hb0 hc0 hq0 hq N j hj hreg]
    simp only [leftCoefficient]
    ring
  · rw [ite_eq_right hj]
    apply sum_eq_zero
    intro k hk
    exact coeff_summand_eq_zero_of_lt N j k (Nat.lt_of_not_ge hj)
      (by have := Finset.mem_range.mp hk; omega)

/-- The quadratic polynomial has the coefficient expansion of a terminating three-phi-two. -/
lemma quadraticPolynomial_eq_sum {b c q : ℂ} (hb0 : b ≠ 0) (hc0 : c ≠ 0)
    (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (N : ℕ)
    (hreg : QDenominatorRegular [q ^ (-(N : ℤ)) * q / b, q ^ (-(N : ℤ)) * q / c] q) :
    quadraticPolynomial b c q N =
      ∑ j ∈ range (N + 1), monomial j (leftCoefficient b c q N j) := by
  ext j
  rw [coeff_quadraticPolynomial hb0 hc0 hq0 hq N j hreg, finsetSum_coeff]
  by_cases hj : j ≤ N
  · rw [ite_eq_left hj, sum_eq_single j]
    · simp
    · intro k hk hkj
      simp [coeff_monomial, hkj]
    · intro hjN
      exact (hjN (Finset.mem_range.mpr (by omega))).elim
  · rw [ite_eq_right hj]
    symm
    apply sum_eq_zero
    intro k hk
    have hkj : k ≠ j := by have := Finset.mem_range.mp hk; omega
    simp [coeff_monomial, hkj]

/-- Evaluating the coefficient polynomial gives the terminating three-phi-two series. -/
lemma eval_quadraticPolynomial_left {b c q : ℂ} (hb0 : b ≠ 0) (hc0 : c ≠ 0)
    (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (N : ℕ) (z : ℂ)
    (hreg : QDenominatorRegular [q ^ (-(N : ℤ)) * q / b, q ^ (-(N : ℤ)) * q / c] q) :
    (quadraticPolynomial b c q N).eval z =
      qPhi [q ^ (-(N : ℤ)), b, c]
        [q ^ (-(N : ℤ)) * q / b, q ^ (-(N : ℤ)) * q / c]
        q (q ^ (-(N : ℤ)) * q * z / (b * c)) := by
  rw [quadraticPolynomial_eq_sum hb0 hc0 hq0 hq N hreg, eval_finsetSum,
    qPhi_terminates hq0 N]
  unfold qPhiPartial
  apply sum_congr rfl
  intro j hj
  simp only [eval_monomial, leftCoefficient, qPhiTerm, qPhiExponent, List.length_cons,
    List.length_nil, Nat.reduceAdd, Nat.cast_ofNat, Int.reduceAdd, Int.reduceSub,
    zpow_zero, mul_one,
    qPochhammerList, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  rw [show q ^ (-(N : ℤ)) * q * z / (b * c) =
    (q ^ (-(N : ℤ)) * q / (b * c)) * z by ring, mul_pow]
  ring

/-- The five-phi-four truncates at the half-index forced by its paired upper parameters. -/
lemma quadratic_series_terminates {q : ℂ} (hq0 : q ≠ 0) (N : ℕ) (b c z : ℂ) :
    qPhi [(q ^ (-(N : ℤ))) ^ (1 / 2 : ℂ), -((q ^ (-(N : ℤ))) ^ (1 / 2 : ℂ)),
        (q ^ (-(N : ℤ)) * q) ^ (1 / 2 : ℂ),
        -((q ^ (-(N : ℤ)) * q) ^ (1 / 2 : ℂ)), q ^ (-(N : ℤ)) * q / (b * c)]
      [q ^ (-(N : ℤ)) * q / b, q ^ (-(N : ℤ)) * q / c,
        q ^ (-(N : ℤ)) * z, q / z] q q =
      ∑ k ∈ range (N / 2 + 1),
        qPochhammer (q ^ (-(N : ℤ))) q (2 * k) *
          qPochhammer (q ^ (-(N : ℤ)) * q / (b * c)) q k /
          (qPochhammer (q ^ (-(N : ℤ)) * q / b) q k *
            qPochhammer (q ^ (-(N : ℤ)) * q / c) q k *
            qPochhammer (q ^ (-(N : ℤ)) * z) q k *
            qPochhammer (q / z) q k * qPochhammer q q k) * q ^ k := by
  unfold qPhi
  simp_rw [qPhiTerm_half_power_pairs]
  apply tsum_eq_sum
  intro k hk
  have hNk : N < 2 * k := by
    have : N / 2 < k := by simpa using hk
    omega
  have hzero : qPochhammer (q ^ (-(N : ℤ))) q (2 * k) = 0 := by
    simpa only [zpow_neg, zpow_natCast] using qPochhammer_recip_pow_eq_zero hq0 hNk
  rw [hzero]
  simp

/-- Evaluating the quadratic polynomial gives the five-phi-four with its product prefactor.
-/
lemma eval_quadraticPolynomial_right {q z : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hz0 : z ≠ 0) (N : ℕ) (b c : ℂ)
    (hreg : QDenominatorRegular [z, q ^ (-(N : ℤ)) * z, q / z] q) :
    (quadraticPolynomial b c q N).eval z =
      qProductRatioInf [q ^ (-(N : ℤ)) * z] [z] q *
        qPhi [(q ^ (-(N : ℤ))) ^ (1 / 2 : ℂ), -((q ^ (-(N : ℤ))) ^ (1 / 2 : ℂ)),
          (q ^ (-(N : ℤ)) * q) ^ (1 / 2 : ℂ),
          -((q ^ (-(N : ℤ)) * q) ^ (1 / 2 : ℂ)), q ^ (-(N : ℤ)) * q / (b * c)]
          [q ^ (-(N : ℤ)) * q / b, q ^ (-(N : ℤ)) * q / c,
            q ^ (-(N : ℤ)) * z, q / z] q q := by
  have hzinf : qPochhammerInf z q ≠ 0 := qPochhammerInf_ne_zero hq fun j =>
    sub_ne_zero.mpr (Ne.symm (hreg z (by simp) j))
  have hA (k : ℕ) : qPochhammer (q ^ (-(N : ℤ)) * z) q k ≠ 0 :=
    qPochhammer_ne_zero_of_factors hq
      (fun j => sub_ne_zero.mpr (Ne.symm (hreg _ (by simp) j))) k
  have hQ (k : ℕ) : qPochhammer (q / z) q k ≠ 0 :=
    qPochhammer_ne_zero_of_factors hq
      (fun j => sub_ne_zero.mpr (Ne.symm (hreg _ (by simp) j))) k
  rw [quadraticPolynomial, eval_finsetSum, quadratic_series_terminates hq0 N b c z]
  simp only [qProductRatioInf, qPochhammerListInf, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one]
  rw [qPochhammerInf_ratio_eq hq0 hq hzinf N, mul_sum]
  apply sum_congr rfl
  intro k hk
  have hk2 : 2 * k ≤ N := by have := Finset.mem_range.mp hk; omega
  have H := finite_prefactor_ratio hq0 hz0 N k hk2 (hA k) (hQ k)
  simp only [eval_mul, eval_C, eval_pow, eval_X,
    DixonPolynomial.eval_pochhammerPolynomial, summandCoefficient]
  rw [show q ^ ((k : ℤ) - N) * z = z * q ^ ((k : ℤ) - N) by ring]
  rw [neg_pow] at H
  linear_combination -(qPochhammer (q ^ (-(N : ℤ))) q (2 * k) *
    qPochhammer (q ^ (-(N : ℤ)) * q / (b * c)) q k /
      (qPochhammer (q ^ (-(N : ℤ)) * q / b) q k *
        qPochhammer (q ^ (-(N : ℤ)) * q / c) q k * qPochhammer q q k)) * H

end DLMF.QHypergeometric.QuadraticTransformation

namespace DLMF.QHypergeometric

/-- DLMF 17.9.E17: qPhi3 terminating quadratic. -/
@[dlmf 17.9.E17]
theorem qPhi3_terminating_quadratic (n : ℕ) (a b c q z : ℂ)
    (hq : ‖q‖<1) (hq0 : q≠0)
    (hpar : ∀ x ∈ [b,c,z], x≠0)
    (hden : QDenominatorRegular [a*q/b,a*q/c,z,a*z,q/z] q)
    (ha : a=q^(-(n:ℤ))) :
    qPhi [a,b,c] [a*q/b,a*q/c] q (a*q*z/(b*c)) =
      qProductRatioInf [a*z] [z] q *
          qPhi [a^(1/2:ℂ), -a^(1/2:ℂ), (a*q)^(1/2:ℂ), -(a*q)^(1/2:ℂ), a*q/(b*c)]
          [a*q/b, a*q/c, a*z, q/z] q (q) := by
  subst a
  have hb0 : b ≠ 0 := hpar b (by simp)
  have hc0 : c ≠ 0 := hpar c (by simp)
  have hz0 : z ≠ 0 := hpar z (by simp)
  have hleft : QDenominatorRegular
      [q ^ (-(n : ℤ)) * q / b, q ^ (-(n : ℤ)) * q / c] q := by
    intro d hd j
    exact hden d (by simp only [List.mem_cons] at hd ⊢; tauto) j
  have hright : QDenominatorRegular [z, q ^ (-(n : ℤ)) * z, q / z] q := by
    intro d hd j
    exact hden d (by simp only [List.mem_cons] at hd ⊢; tauto) j
  rw [← QuadraticTransformation.eval_quadraticPolynomial_left hb0 hc0 hq0 hq n z hleft,
    QuadraticTransformation.eval_quadraticPolynomial_right hq0 hq hz0 n b c hright]

end DLMF.QHypergeometric
