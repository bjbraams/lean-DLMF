/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.Relations
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic

/-!
# Explicit formulas, symmetry, and transformations (DLMF §§18.5–18.7)

Statements from NIST DLMF Chapter 18, each tagged with its equation number by `@[dlmf]`.
Jacobi and Gegenbauer statements retain regularity hypotheses because the project's
hypergeometric definitions do not implement continuation in singular parameters.
The Gegenbauer sums 18.5.10–18.5.11 and the quadratic transformations 18.7.13–18.7.16
need the three-term recurrences of `Differential.lean`, which imports this file; they
are stated and proved in `GegenbauerSeries.lean`.
-/

@[expose] public section

open Complex Polynomial MeasureTheory Filter
open scoped Real Nat Topology
open DLMF.Hypergeometric
open DLMF.Confluent

noncomputable section

set_option autoImplicit false

namespace DLMF.OrthogonalPolynomials

/-- Polynomial continuation of Laguerre in its parameter, including negative
integers. The existing `laguerrePolyL` uses a totalized hypergeometric quotient and
agrees with this definition only at regular denominator parameters. -/
@[dlmf 18.5.E12]
def laguerreExtended (α : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), poch (α + k + 1) (n - k) /
    ((k.factorial : ℂ) * (n - k).factorial) * (-x) ^ k

/-- Identity under the stated parameter and domain assumptions: `laguerreExtended α n x =
laguerrePolyL α n x`. -/
@[dlmf 18.5.E12]
theorem laguerreExtended_eq {α : ℂ} (hα : ∀ k : ℕ, α + 1 ≠ -(k : ℂ)) (n : ℕ) (x : ℂ) :
    laguerreExtended α n x = laguerrePolyL α n x := by
  rw [laguerrePolyL_eq_sum hα]
  unfold laguerreExtended
  apply Finset.sum_congr rfl
  intro k _
  congr 2 <;> ring

/-- Chebyshev polynomials of the third kind, in the DLMF normalization. -/
@[dlmf 18.7.E5]
def chebyshevV (n : ℕ) (x : ℂ) : ℂ :=
  jacobiPolyP (-1 / 2) (1 / 2) n x / jacobiPolyP (-1 / 2) (1 / 2) n 1

/-- Chebyshev polynomials of the fourth kind, in the DLMF normalization. -/
@[dlmf 18.7.E6]
def chebyshevW (n : ℕ) (x : ℂ) : ℂ :=
  (2 * n + 1) * jacobiPolyP (1 / 2) (-1 / 2) n x / jacobiPolyP (1 / 2) (-1 / 2) n 1

/-- Formula under the stated hypotheses: `jacobiPolyP α β n x = ∑ k ∈ Finset.range (n + 1), poch
(n + α + β + 1) k * poch (α + k + 1) (n - k) / ((k.factorial : ℂ) * (n - k).factorial) * ((x -
1) / 2) ^ k`. -/
@[dlmf 18.5.E7]
theorem jacobi_finite_sum {α β : ℂ} (hα : -1 < α.re) (n : ℕ) (x : ℂ) :
    jacobiPolyP α β n x = ∑ k ∈ Finset.range (n + 1),
      poch (n + α + β + 1) k * poch (α + k + 1) (n - k) /
        ((k.factorial : ℂ) * (n - k).factorial) * ((x - 1) / 2) ^ k := by
  have hα' : ∀ k : ℕ, α + 1 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by
    simp only [Complex.add_re, Complex.one_re]
    linarith)
  have hn : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  unfold jacobiPolyP
  rw [ordinaryHypergeometric_eq_sum_neg_nat, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hck := poch_ne_zero_of_not_neg_nat hα' k
  have hk0 : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hnk : ((n - k).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (n - k).factorial_ne_zero
  have hadd := poch_add (α + 1) k (n - k)
  rw [Nat.add_sub_of_le hkn] at hadd
  have hdesc : (n.descFactorial k : ℂ) * (n - k).factorial = n.factorial := by
    have he := congrArg (Nat.cast : ℕ → ℂ)
      (show n.descFactorial k * (n - k).factorial = n.factorial by
        rw [Nat.descFactorial_eq_factorial_mul_choose]
        convert Nat.choose_mul_factorial_mul_factorial hkn using 1
        ring)
    simpa [Nat.cast_mul] using he
  have hz : ((x - 1) / 2) ^ k = (-1 : ℂ) ^ k * ((1 - x) / 2) ^ k := by
    rw [← mul_pow]
    congr 1
    ring
  rw [gaussHGCoeff, poch_neg_coe_nat, hadd, eq_div_of_mul_eq hnk hdesc, hz,
    show α + k + 1 = α + 1 + k by ring]
  field_simp [hck, hn, hk0, hnk]

/-- `(-n)_k (n-k)! = (-1)^k n!` for `k ≤ n`. -/
theorem poch_neg_nat_mul_factorial {n k : ℕ} (hk : k ≤ n) :
    poch (-(n : ℂ)) k * ((n - k) ! : ℂ) = (-1) ^ k * (n ! : ℂ) := by
  rw [poch, ascPochhammer_eval_neg_eq_descPochhammer, descPochhammer_eval_eq_descFactorial]
  have h := Nat.factorial_mul_descFactorial hk
  have h' : ((n - k) ! : ℂ) * (n.descFactorial k : ℂ) = n ! := by exact_mod_cast h
  linear_combination (-1 : ℂ) ^ k * h'

/-- 18.5.8 away from `x = -1`, via the terminating Pfaff transformation. -/
lemma jacobi_binomial_sum_aux {α β : ℂ} (hα : -1 < α.re) (n : ℕ) {x : ℂ} (hx : x ≠ -1) :
    jacobiPolyP α β n x = ((2 : ℂ) ^ n)⁻¹ * ∑ k ∈ Finset.range (n + 1),
      (poch (α + n - k + 1) k / k.factorial) *
      (poch (β + k + 1) (n - k) / (n - k).factorial) *
      (x - 1) ^ (n - k) * (x + 1) ^ k := by
  have hα' : ∀ k : ℕ, α + 1 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by
    simp only [Complex.add_re, Complex.one_re]
    linarith)
  have hw : (1 - x) / 2 ≠ 1 := fun h => hx (by linear_combination -2 * h)
  have hx1 : x + 1 ≠ 0 := fun h => hx (by linear_combination h)
  unfold jacobiPolyP
  rw [DLMF.Hypergeometric.terminating_pfaff n hα' hw, ordinaryHypergeometric_eq_sum_neg_nat,
    Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [show n + 1 - 1 - j = n - j by omega]
  obtain ⟨k, rfl⟩ : ∃ k, n = j + k := ⟨n - j, by omega⟩
  rw [Nat.add_sub_cancel_left]
  have h1 : 1 - (1 - x) / 2 = (x + 1) / 2 := by ring
  have h2 : (1 - x) / 2 / ((1 - x) / 2 - 1) = (x - 1) / (x + 1) := by
    have hd : (1 - x) / 2 - 1 ≠ 0 := fun h => hx1 (by linear_combination -2 * h)
    rw [div_eq_div_iff hd hx1]; ring
  have hpa := poch_add (α + 1) k j
  rw [show k + j = j + k by ring] at hpa
  have hpn := poch_neg_nat_mul_factorial (n := j + k) (k := k) (by omega)
  rw [show j + k - k = j by omega] at hpn
  have hpb := DLMF.Hypergeometric.poch_one_sub_sub (β + j + 1) k
  rw [show 1 - (β + j + 1) - (k : ℂ) = α + 1 - (((j + k : ℕ) : ℂ) + α + β + 1) by
    push_cast; ring] at hpb
  have hαk := poch_ne_zero_of_not_neg_nat hα' k
  have hfj : (j ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr j.factorial_ne_zero
  have hfk : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hfn : ((j + k) ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (j + k).factorial_ne_zero
  rw [h1, h2, gaussHGCoeff, hpb, hpa, show α + ((j + k : ℕ) : ℂ) - j + 1 = α + 1 + k by
    push_cast; ring]
  rw [div_pow, div_pow, show (j + k) = k + j by ring, pow_add (x + 1)]
  have hpn' : poch (-((k + j : ℕ) : ℂ)) k = (-1) ^ k * ((k + j) ! : ℂ) / j ! := by
    rw [eq_div_iff hfj, show k + j = j + k by ring, hpn]
  have hx1k : (x + 1) ^ k ≠ 0 := pow_ne_zero _ hx1
  have hsq : ((-1 : ℂ) ^ k) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  have hfn' : ((k + j) ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (k + j).factorial_ne_zero
  rw [hpn']
  field_simp
  rw [hsq, mul_one]

/-- Formula under the stated hypotheses: `jacobiPolyP α β n x = ((2 : ℂ) ^ n)⁻¹ * ∑ k ∈
Finset.range (n + 1), (poch (α + n - k + 1) k / k.factorial) * (poch (β + k + 1) (n - k) / (n
- k).factorial) * (x - 1) ^ (n - k) * (x + 1) ^ k`. -/
@[dlmf 18.5.E8]
theorem jacobi_binomial_sum {α β : ℂ} (hα : -1 < α.re) (n : ℕ) (x : ℂ) :
    jacobiPolyP α β n x = ((2 : ℂ) ^ n)⁻¹ * ∑ k ∈ Finset.range (n + 1),
      (poch (α + n - k + 1) k / k.factorial) *
      (poch (β + k + 1) (n - k) / (n - k).factorial) *
      (x - 1) ^ (n - k) * (x + 1) ^ k := by
  have hL : Continuous fun x => jacobiPolyP α β n x := by
    rw [show (fun x => jacobiPolyP α β n x) = fun x => ∑ k ∈ Finset.range (n + 1),
      poch (n + α + β + 1) k * poch (α + k + 1) (n - k) /
        ((k.factorial : ℂ) * (n - k).factorial) * ((x - 1) / 2) ^ k from
      funext (jacobi_finite_sum hα n)]
    fun_prop
  have hR : Continuous fun x : ℂ => ((2 : ℂ) ^ n)⁻¹ * ∑ k ∈ Finset.range (n + 1),
      (poch (α + n - k + 1) k / k.factorial) *
      (poch (β + k + 1) (n - k) / (n - k).factorial) *
      (x - 1) ^ (n - k) * (x + 1) ^ k := by fun_prop
  exact congrFun (Continuous.ext_on (dense_compl_singleton (-1 : ℂ)) hL hR
    fun y hy => jacobi_binomial_sum_aux hα n hy) x

/-- The finite sum for `H_n` at even degree `n = 2m`, via the confluent form 13.6.16. -/
theorem hermitePolyH_even_sum (m : ℕ) (x : ℂ) :
    aeval x (hermitePolyH (2 * m)) = ((2 * m) ! : ℂ) * ∑ k ∈ Finset.range (m + 1),
      (-1 : ℂ) ^ k * (2 * x) ^ (2 * m - 2 * k) / ((k ! : ℂ) * (2 * m - 2 * k) !) := by
  have h := Confluent.hermitePolyHEval_even_mul m x
  rw [Confluent.hermitePolyHEval_eq_aeval, kummerM_eq_sum_neg_nat] at h
  have hm : (m ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr m.factorial_ne_zero
  apply mul_right_cancel₀ hm
  rw [h]
  conv_rhs => rw [← Finset.sum_range_reflect]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjm : j ≤ m := by simp at hj; omega
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hjm
  rw [show j + i + 1 - 1 - j = i by omega, show 2 * (j + i) - 2 * i = 2 * j by omega]
  have q := poch_neg_nat_mul_factorial (n := j + i) (k := j) (by omega)
  rw [show j + i - j = i by omega] at q
  rw [DLMF.OrthogonalPolynomials.poch_half j]
  have hi : (i ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr i.factorial_ne_zero
  have hj' : (j ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr j.factorial_ne_zero
  have h2j : ((2 * j) ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (2 * j).factorial_ne_zero
  have hq : poch (-((j + i : ℕ) : ℂ)) j = (-1) ^ j * ((j + i) ! : ℂ) / (i ! : ℂ) := by
    field_simp; linear_combination q
  rw [hq]
  field_simp
  rw [pow_add, mul_pow, pow_mul, pow_mul]
  ring_nf
  simp only [pow_mul', neg_one_sq, one_pow, mul_one]

/-- The finite sum for `H_n` at odd degree `n = 2m + 1`, via the confluent form 13.6.17. -/
theorem hermitePolyH_odd_sum (m : ℕ) (x : ℂ) :
    aeval x (hermitePolyH (2 * m + 1)) = ((2 * m + 1) ! : ℂ) * ∑ k ∈ Finset.range (m + 1),
      (-1 : ℂ) ^ k * (2 * x) ^ (2 * m + 1 - 2 * k) / ((k ! : ℂ) * (2 * m + 1 - 2 * k) !) := by
  have h := Confluent.hermitePolyHEval_odd_mul m x
  rw [Confluent.hermitePolyHEval_eq_aeval, kummerM_eq_sum_neg_nat] at h
  have hm : (m ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr m.factorial_ne_zero
  apply mul_right_cancel₀ hm
  rw [h]
  conv_rhs => rw [← Finset.sum_range_reflect]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjm : j ≤ m := by simp at hj; omega
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hjm
  rw [show j + i + 1 - 1 - j = i by omega, show 2 * (j + i) + 1 - 2 * i = 2 * j + 1 by omega]
  have q := poch_neg_nat_mul_factorial (n := j + i) (k := j) (by omega)
  rw [show j + i - j = i by omega] at q
  rw [poch_three_halves_eq, DLMF.OrthogonalPolynomials.poch_half j]
  have hi : (i ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr i.factorial_ne_zero
  have hj' : (j ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr j.factorial_ne_zero
  have h2j : ((2 * j) ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (2 * j).factorial_ne_zero
  have hq : poch (-((j + i : ℕ) : ℂ)) j = (-1) ^ j * ((j + i) ! : ℂ) / (i ! : ℂ) := by
    field_simp; linear_combination q
  have h2j1 : (2 * (j : ℂ) + 1) ≠ 0 := by exact_mod_cast (by omega : 2 * j + 1 ≠ 0)
  rw [hq, Nat.factorial_succ (2 * j)]
  push_cast
  field_simp
  have e : (-1 : ℂ) ^ j * (-1) ^ j = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  have e4 : (4 : ℂ) ^ j = 2 ^ (2 * j) := by rw [pow_mul]; norm_num
  rw [e4]
  linear_combination (((2 * (j + i) + 1) ! : ℂ) * (-1) ^ i * 2 * x * 2 ^ (2 * j) * x ^ (2 * j)) * e

/-- Formula under the stated hypotheses: `aeval x (hermitePolyH n) = (n.factorial : ℂ) * ∑ k ∈
Finset.range (n / 2 + 1), (-1 : ℂ) ^ k * (2 * x) ^ (n - 2 * k) / ((k.factorial : ℂ) * (n - 2 *
k).factorial)`. -/
@[dlmf 18.5.E13]
theorem hermitePolyH_finite_sum (n : ℕ) (x : ℂ) :
    aeval x (hermitePolyH n) = (n.factorial : ℂ) * ∑ k ∈ Finset.range (n / 2 + 1),
      (-1 : ℂ) ^ k * (2 * x) ^ (n - 2 * k) /
        ((k.factorial : ℂ) * (n - 2 * k).factorial) := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [show 2 * m / 2 = m by omega]
    exact hermitePolyH_even_sum m x
  · rw [show (2 * m + 1) / 2 = m by omega]
    exact hermitePolyH_odd_sum m x

/-- Gamma normalization of the terminating regularized confluent function. -/
theorem laguerrePolyL_eq_Gamma_mul_regularized {α : ℂ}
    (hα : ∀ k : ℕ, α + 1 ≠ -(k : ℂ)) (n : ℕ) (z : ℂ) :
    laguerrePolyL α n z = Gamma ((n : ℂ) + α + 1) / (n.factorial : ℂ) *
      regularizedHGFun {-(n : ℂ)} {α + 1} z := by
  rw [laguerrePolyL, kummerM_eq_mul_regularizedHGFun hα]
  have hG := Gamma_add_nat_div_Gamma_eq (n := n) (α + 1) hα
  rw [show (n : ℂ) + α + 1 = (α + 1) + n by ring, poch, ← hG]
  field_simp [Gamma_ne_zero hα]

/-- Identity under the stated parameter and domain assumptions: `laguerrePolyL α n 0 = poch (α +
1) n / n.factorial`. -/
@[dlmf 18.6.E1]
theorem laguerrePolyL_at_zero (α : ℂ) (n : ℕ) : laguerrePolyL α n 0 = poch (α + 1) n
    / n.factorial := by
  simp [laguerrePolyL]

/-- Identity under the stated parameter and domain assumptions: `jacobiPolyP α β n 1 = poch (α +
1) n / n.factorial`. -/
@[dlmf 18.6.T1]
theorem jacobi_at_one {α β : ℂ} (hα : -1 < α.re) (n : ℕ) :
    jacobiPolyP α β n 1 = poch (α + 1) n / n.factorial := by
  simp [jacobiPolyP]

/-- Jacobi polynomials do not vanish at `x = 1` for `Re α > -1`. -/
theorem jacobiPolyP_one_ne_zero {α β : ℂ} (hα : -1 < α.re) (n : ℕ) : jacobiPolyP α β n 1 ≠ 0 := by
  rw [jacobi_at_one hα]
  exact div_ne_zero (poch_ne_zero_of_not_neg_nat (not_neg_nat_of_re_pos (by
    simp only [Complex.add_re, Complex.one_re]
    linarith)) n) (Nat.cast_ne_zero.mpr n.factorial_ne_zero)

/-- Identity under the stated parameter and domain assumptions: `ultrasphPoly lam n 1 = poch (2 *
lam) n / n.factorial`. -/
@[dlmf 18.6.T1]
theorem ultrasphPoly_at_one {lam : ℂ} (hlam : -1 / 2 < lam.re) (n : ℕ) :
    ultrasphPoly lam n 1 = poch (2 * lam) n / n.factorial := by
  simp [ultrasphPoly]

/-- Identity under the stated parameter and domain assumptions: `aeval (-x) (hermitePolyH n) = (-1
: ℂ) ^ n * aeval x (hermitePolyH n)`. -/
@[dlmf 18.6.T1]
theorem hermitePolyH_reflection (n : ℕ) (x : ℂ) :
    aeval (-x) (hermitePolyH n) = (-1 : ℂ) ^ n * aeval x (hermitePolyH n) := by
  have hp (n : ℕ) : (hermitePolyH n).comp (-X) = C ((-1 : ℤ) ^ n) * hermitePolyH n := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hd := congrArg derivative ih
      simp only [derivative_comp, derivative_neg, derivative_X, derivative_C_mul,
        neg_mul, one_mul] at hd
      have hd' := congrArg Neg.neg hd
      simp only [neg_neg] at hd'
      simp only [hermitePolyH_succ, sub_comp, mul_comp, ofNat_comp, X_comp, ih, hd',
        pow_succ, map_mul, map_neg, map_one]
      ring
  have he := congrArg (aeval x : ℤ[X] → ℂ) (hp n)
  simpa [aeval_comp] using he

/-- Identity under the stated parameter and domain assumptions: `(hermitePolyH (2 * n)).eval 0 =
(-1 : ℤ) ^ n * ((2 * n).factorial / n.factorial : ℕ)`. -/
@[dlmf 18.6.T1]
theorem hermitePolyH_even_at_zero (n : ℕ) :
    (hermitePolyH (2 * n)).eval 0 = (-1 : ℤ) ^ n * ((2 * n).factorial / n.factorial : ℕ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep : (hermitePolyH (2 * (n + 1))).eval 0 =
        -(2 * (2 * n + 1)) * (hermitePolyH (2 * n)).eval 0 := by
      rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, hermitePolyH_succ, hermitePolyH_derivative]
      simp only [eval_sub, eval_mul, eval_ofNat, eval_X, eval_C, mul_zero, zero_mul, zero_sub]
      push_cast
      ring
    obtain ⟨q, hq⟩ := Nat.factorial_dvd_factorial (show n ≤ 2 * n by omega)
    have h1 : (2 * n).factorial / n.factorial = q := by
      rw [hq, Nat.mul_div_cancel_left _ (Nat.factorial_pos n)]
    have h2 : (2 * (n + 1)).factorial / (n + 1).factorial = 2 * (2 * n + 1) * q := by
      rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ,
        Nat.factorial_succ n, hq,
        show (2 * n + 1 + 1) * ((2 * n + 1) * (n.factorial * q)) =
          ((n + 1) * n.factorial) * (2 * (2 * n + 1) * q) by ring]
      exact Nat.mul_div_cancel_left _ (by positivity)
    rw [hstep, ih, h1, h2]
    push_cast
    ring

/-- Identity under the stated parameter and domain assumptions: `chebyshevV n 1 = 1`. -/
@[dlmf 18.6.T1]
theorem chebyshevV_at_one (n : ℕ) : chebyshevV n 1 = 1 := by
  exact div_self (jacobiPolyP_one_ne_zero (by norm_num) n)

/-- Identity under the stated parameter and domain assumptions: `chebyshevW n 1 = 2 * n + 1`. -/
@[dlmf 18.6.T1]
theorem chebyshevW_at_one (n : ℕ) : chebyshevW n 1 = 2 * n + 1 := by
  unfold chebyshevW
  exact mul_div_cancel_right₀ _ (jacobiPolyP_one_ne_zero (by norm_num) n)

/-- Identity under the stated parameter and domain assumptions: `legendrePolyP n x = ultrasphPoly
(1 / 2) n x`. -/
@[dlmf 18.7.E9]
theorem legendre_eq_ultrasphPoly (n : ℕ) (x : ℂ) : legendrePolyP n x
    = ultrasphPoly (1 / 2) n x := by
  norm_num [legendrePolyP, jacobiPolyP, ultrasphPoly]

/-- `4^n (1/2)_n n! = (2n)!`. -/
theorem two_pow_mul_poch_half (n : ℕ) :
    (2 : ℂ) ^ (2 * n) * poch (1 / 2) n * n.factorial = (2 * n).factorial := by
  induction n with
  | zero => simp [poch_zero]
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, pow_succ, pow_succ, poch_succ, Nat.factorial_succ,
      Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    linear_combination (4 * (1 / 2 + (n : ℂ)) * ((n : ℂ) + 1)) * ih

/-- `4^n (3/2)_n n! = (2n+1)!`. -/
theorem two_pow_mul_poch_three_half (n : ℕ) :
    (2 : ℂ) ^ (2 * n) * poch (3 / 2) n * n.factorial = (2 * n + 1).factorial := by
  induction n with
  | zero => simp [poch_zero]
  | succ n ih =>
    rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 by ring, show 2 * (n + 1) = 2 * n + 1 + 1 by ring,
      pow_succ, pow_succ, poch_succ, Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    linear_combination (4 * (3 / 2 + (n : ℂ)) * ((n : ℂ) + 1)) * ih

/-- Identity under the stated parameter and domain assumptions: `aeval x (hermitePolyH (2 * n)) =
(-1 : ℂ) ^ n * 2 ^ (2 * n) * n.factorial * laguerrePolyL (-1 / 2) n (x ^ 2)`. -/
@[dlmf 18.7.E19]
theorem hermitePolyH_even_eq_laguerrePolyL (n : ℕ) (x : ℂ) :
    aeval x (hermitePolyH (2 * n)) = (-1 : ℂ) ^ n * 2 ^ (2 * n) * n.factorial
        * laguerrePolyL (-1 / 2) n (x ^ 2) := by
  have h := DLMF.Confluent.hermitePolyHEval_even_mul n x
  rw [DLMF.Confluent.hermitePolyHEval_eq_aeval] at h
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hL : laguerrePolyL (-1 / 2) n (x ^ 2) * n.factorial =
      poch (1 / 2) n * kummerM (-(n : ℂ)) (1 / 2) (x ^ 2) := by
    unfold laguerrePolyL
    rw [show (-1 / 2 : ℂ) + 1 = 1 / 2 by norm_num]
    field_simp
  have hp := two_pow_mul_poch_half n
  apply mul_right_cancel₀ hf
  linear_combination h - ((-1 : ℂ) ^ n * 2 ^ (2 * n) * n.factorial) * hL -
    ((-1 : ℂ) ^ n * kummerM (-(n : ℂ)) (1 / 2) (x ^ 2)) * hp

/-- Identity under the stated parameter and domain assumptions: `aeval x (hermitePolyH (2 * n +
1)) = (-1 : ℂ) ^ n * 2 ^ (2 * n + 1) * n.factorial * x * laguerrePolyL (1 / 2) n (x ^ 2)`. -/
@[dlmf 18.7.E20]
theorem hermitePolyH_odd_eq_laguerrePolyL (n : ℕ) (x : ℂ) :
    aeval x (hermitePolyH (2 * n + 1)) = (-1 : ℂ) ^ n * 2 ^ (2 * n + 1) * n.factorial * x
        * laguerrePolyL (1 / 2) n (x ^ 2) := by
  have h := DLMF.Confluent.hermitePolyHEval_odd_mul n x
  rw [DLMF.Confluent.hermitePolyHEval_eq_aeval] at h
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hL : laguerrePolyL (1 / 2) n (x ^ 2) * n.factorial =
      poch (3 / 2) n * kummerM (-(n : ℂ)) (3 / 2) (x ^ 2) := by
    unfold laguerrePolyL
    rw [show (1 / 2 : ℂ) + 1 = 3 / 2 by norm_num]
    field_simp
  have hp := two_pow_mul_poch_three_half n
  apply mul_right_cancel₀ hf
  linear_combination h - ((-1 : ℂ) ^ n * 2 ^ (2 * n + 1) * n.factorial * x) * hL -
    ((-1 : ℂ) ^ n * 2 * x * kummerM (-(n : ℂ)) (3 / 2) (x ^ 2)) * hp


/-- The cosines of `k` times the Chebyshev–Gauss angles sum to zero unless `2M ∣ k`. -/
theorem sum_cos_chebyshevGauss_eq_zero {M : ℕ} {k : ℤ} (hk : ¬ (2 * M : ℤ) ∣ k) :
    ∑ i ∈ Finset.range M, Real.cos (k * ((2 * i + 1) * π / (2 * M))) = 0 := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp
  set a : ℝ := k * π / (2 * M) with ha
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hs : Real.sin a ≠ 0 := by
    intro h
    obtain ⟨j, hj⟩ := Real.sin_eq_zero_iff.mp h
    apply hk
    refine ⟨j, ?_⟩
    have : (k : ℝ) = 2 * M * j := by
      rw [ha] at hj
      field_simp at hj
      rw [← hj]
      ring
    exact_mod_cast this
  have key : ∀ i : ℕ, 2 * Real.sin a * Real.cos (k * ((2 * i + 1) * π / (2 * M))) =
      Real.sin (((i + 1 : ℕ) : ℝ) * (2 * a)) - Real.sin ((i : ℝ) * (2 * a)) := by
    intro i
    rw [Real.two_mul_sin_mul_cos]
    push_cast
    rw [show a - k * ((2 * i + 1) * π / (2 * M)) = -(i * (2 * a)) by rw [ha]; ring,
      show a + k * ((2 * i + 1) * π / (2 * M)) = (i + 1) * (2 * a) by rw [ha]; ring,
      Real.sin_neg]
    ring
  have hsum : 2 * Real.sin a * ∑ i ∈ Finset.range M, Real.cos (k * ((2 * i + 1) * π / (2 * M)))
      = 0 := by
    rw [Finset.mul_sum, Finset.sum_congr rfl fun i _ => key i,
      Finset.sum_range_sub (fun i : ℕ => Real.sin ((i : ℝ) * (2 * a)))]
    rw [show (M : ℝ) * (2 * a) = (k : ℝ) * π by rw [ha]; field_simp]
    simp [Real.sin_int_mul_pi]
  exact (mul_eq_zero.mp hsum).resolve_left (mul_ne_zero two_ne_zero hs)

/-- Identity under the stated parameter and domain assumptions: `∑ i : Fin (N + 1), (Chebyshev.T ℝ
m).eval (Real.cos ((i.val + 1 / 2) * Real.pi / (N + 1))) * (Chebyshev.T ℝ n).eval (Real.cos
((i.val + 1 / 2) * Real.pi / (N + 1))) = 0`. -/
@[dlmf 18.3.E1]
theorem chebyshevT_discrete_orthogonality {N m n : ℕ} (hm : m ≤ N) (hn : n ≤ N)
    (hmn : m ≠ n) :
    ∑ i : Fin (N + 1),
      (Chebyshev.T ℝ m).eval (Real.cos ((i.val + 1 / 2) * Real.pi / (N + 1))) *
      (Chebyshev.T ℝ n).eval (Real.cos ((i.val + 1 / 2) * Real.pi / (N + 1))) = 0 := by
  have hnd : ∀ k : ℤ, 0 < |k| → |k| < 2 * (N + 1) → ¬ (2 * ((N + 1 : ℕ) : ℤ) ∣ k) := by
    intro k hk0 hk1 hdvd
    have := Int.le_of_dvd hk0 ((dvd_abs _ _).mpr hdvd)
    push_cast at this
    omega
  have h1 := sum_cos_chebyshevGauss_eq_zero (M := N + 1) (k := (m : ℤ) + n)
    (hnd _ (by rw [abs_pos]; omega) (by rw [abs_lt]; omega))
  have h2 := sum_cos_chebyshevGauss_eq_zero (M := N + 1) (k := (m : ℤ) - n)
    (hnd _ (by rw [abs_pos]; omega) (by rw [abs_lt]; omega))
  rw [Fin.sum_univ_eq_sum_range (fun i => (Chebyshev.T ℝ m).eval
    (Real.cos ((i + 1 / 2) * Real.pi / (N + 1))) * (Chebyshev.T ℝ n).eval
    (Real.cos ((i + 1 / 2) * Real.pi / (N + 1))))]
  have key : ∀ i : ℕ, (Chebyshev.T ℝ m).eval (Real.cos ((i + 1 / 2) * Real.pi / (N + 1))) *
      (Chebyshev.T ℝ n).eval (Real.cos ((i + 1 / 2) * Real.pi / (N + 1))) =
      (Real.cos (((m : ℤ) + n : ℤ) * ((2 * i + 1) * π / (2 * ((N + 1 : ℕ) : ℝ)))) +
        Real.cos (((m : ℤ) - n : ℤ) * ((2 * i + 1) * π / (2 * ((N + 1 : ℕ) : ℝ))))) / 2 := by
    intro i
    rw [Chebyshev.T_real_cos, Chebyshev.T_real_cos]
    push_cast
    rw [show ((m : ℝ) + n) * ((2 * i + 1) * π / (2 * (N + 1))) =
        m * ((i + 1 / 2) * π / (N + 1)) + n * ((i + 1 / 2) * π / (N + 1)) by field_simp,
      show ((m : ℝ) - n) * ((2 * i + 1) * π / (2 * (N + 1))) =
        m * ((i + 1 / 2) * π / (N + 1)) - n * ((i + 1 / 2) * π / (N + 1)) by field_simp,
      Real.cos_add, Real.cos_sub]
    ring
  rw [Finset.sum_congr rfl fun i _ => key i, ← Finset.sum_div, Finset.sum_add_distrib, h1, h2]
  simp

/-- `Uₙ(x) = ∑_{i+j=n} (-1)^j C(i,j) (2x)^{i-j}`, a weighted form of the Fibonacci identity. -/
theorem chebyshevU_eval_eq_sum_antidiagonal (n : ℕ) (x : ℂ) :
    (Chebyshev.U ℂ n).eval x = ∑ p ∈ Finset.antidiagonal n,
      (-1 : ℂ) ^ p.2 * (p.1.choose p.2 : ℂ) * (2 * x) ^ (p.1 - p.2) := by
  have hshift : ∀ i j : ℕ, (i.choose (j + 1) : ℂ) * ((2 * x) * (2 * x) ^ (i - (j + 1))) =
      (i.choose (j + 1) : ℂ) * (2 * x) ^ (i - j) := by
    intro i j
    rcases lt_or_ge i (j + 1) with h | h
    · simp [Nat.choose_eq_zero_of_lt h]
    · rw [← pow_succ', show i - (j + 1) + 1 = i - j by omega]
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp [Finset.Nat.antidiagonal_succ]
  | more n ih0 ih1 =>
    have h := Chebyshev.U_add_two ℂ (n : ℤ)
    rw [show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring] at h
    rw [show ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 by push_cast; ring, h, eval_sub, eval_mul, eval_mul,
      eval_X, eval_ofNat, ih0, ih1,
      Finset.Nat.antidiagonal_succ_succ', Finset.Nat.antidiagonal_succ']
    simp only [Finset.sum_cons, Finset.sum_map, Function.Embedding.coe_prodMap,
      Function.Embedding.coeFn_mk, Prod.map_fst, Prod.map_snd, Function.Embedding.refl_apply,
      Nat.succ_eq_add_one, Nat.choose_succ_succ, Nat.cast_add, Nat.choose_zero_succ,
      Nat.cast_zero, mul_zero, zero_mul, zero_add, Nat.choose_zero_right, Nat.cast_one,
      pow_zero, mul_one, one_mul, Nat.sub_zero, Nat.add_sub_add_right]
    rw [mul_add, Finset.mul_sum, ← pow_succ']
    rw [Finset.sum_congr rfl fun p _ => show 2 * x * ((-1 : ℂ) ^ (p.2 + 1) *
        (p.1.choose (p.2 + 1) : ℂ) * (2 * x) ^ (p.1 - (p.2 + 1))) =
        (-1 : ℂ) ^ (p.2 + 1) * (p.1.choose (p.2 + 1) : ℂ) * (2 * x) ^ (p.1 - p.2) by
      linear_combination (-1 : ℂ) ^ (p.2 + 1) * hshift p.1 p.2]
    rw [add_sub_assoc, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    ring

/-- Formula under the stated hypotheses: `(Chebyshev.U ℂ n).eval x = ∑ k ∈ Finset.range (n / 2 +
1), (-1 : ℂ) ^ k * (n - k).factorial / ((k.factorial : ℂ) * (n - 2 * k).factorial) * (2 * x) ^
(n - 2 * k)`. -/
@[dlmf 18.5.E11_3]
theorem chebyshevU_finite_sum (n : ℕ) (x : ℂ) :
    (Chebyshev.U ℂ n).eval x = ∑ k ∈ Finset.range (n / 2 + 1),
      (-1 : ℂ) ^ k * (n - k).factorial /
        ((k.factorial : ℂ) * (n - 2 * k).factorial) * (2 * x) ^ (n - 2 * k) := by
  rw [chebyshevU_eval_eq_sum_antidiagonal, ← Finset.Nat.sum_antidiagonal_swap]
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => (-1 : ℂ) ^ i * (j.choose i : ℂ) * (2 * x) ^ (j - i))]
  symm
  rw [← Finset.sum_subset (Finset.range_subset_range.mpr (by omega : n / 2 + 1 ≤ n + 1))]
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hk2 : 2 * k ≤ n := by simp at hk; omega
    rw [Nat.cast_choose ℂ (by omega : k ≤ n - k), show n - k - k = n - 2 * k by omega]
    ring
  · intro k _ hk
    have hk2 : n < 2 * k := by simp at hk; omega
    rw [Nat.choose_eq_zero_of_lt (by omega : n - k < k)]
    simp

/-- Formula under the stated hypotheses: `(Chebyshev.T ℂ n).eval x = (n : ℂ) / 2 * ∑ k ∈
Finset.range (n / 2 + 1), (-1 : ℂ) ^ k * (n - k - 1).factorial / ((k.factorial : ℂ) * (n - 2 *
k).factorial) * (2 * x) ^ (n - 2 * k)`. -/
@[dlmf 18.5.E11_1]
theorem chebyshevT_finite_sum {n : ℕ} (hn : 0 < n) (x : ℂ) :
    (Chebyshev.T ℂ n).eval x = (n : ℂ) / 2 * ∑ k ∈ Finset.range (n / 2 + 1),
      (-1 : ℂ) ^ k * (n - k - 1).factorial /
        ((k.factorial : ℂ) * (n - 2 * k).factorial) * (2 * x) ^ (n - 2 * k) := by
  obtain ⟨m, rfl⟩ | ⟨m, rfl⟩ : n = 1 ∨ ∃ m, n = m + 2 := by
    rcases n with _ | _ | m
    · omega
    · left; rfl
    · right; exact ⟨m, by ring⟩
  · simp
  have h := congrArg (eval x) (Chebyshev.two_mul_T_eq_U_sub_U ℂ (m : ℤ))
  simp only [eval_mul, eval_sub, eval_ofNat] at h
  rw [show ((m : ℤ) + 2) = ((m + 2 : ℕ) : ℤ) by push_cast; ring, chebyshevU_finite_sum,
    chebyshevU_finite_sum, show (m + 2) / 2 + 1 = m / 2 + 1 + 1 by omega,
    Finset.sum_range_succ'] at h
  rw [show (m + 2) / 2 + 1 = m / 2 + 1 + 1 by omega, Finset.sum_range_succ']
  have hkey : ∀ k ∈ Finset.range (m / 2 + 1),
      (-1 : ℂ) ^ (k + 1) * ((m + 2 - (k + 1)).factorial : ℂ) /
          (((k + 1).factorial : ℂ) * (m + 2 - 2 * (k + 1)).factorial) *
          (2 * x) ^ (m + 2 - 2 * (k + 1)) -
        (-1 : ℂ) ^ k * ((m - k).factorial : ℂ) / ((k.factorial : ℂ) * (m - 2 * k).factorial) *
          (2 * x) ^ (m - 2 * k) =
      ((m + 2 : ℕ) : ℂ) * ((-1 : ℂ) ^ (k + 1) * ((m + 2 - (k + 1) - 1).factorial : ℂ) /
        (((k + 1).factorial : ℂ) * (m + 2 - 2 * (k + 1)).factorial) *
          (2 * x) ^ (m + 2 - 2 * (k + 1))) := by
    intro k hk
    have hk2 : 2 * k ≤ m := by simp at hk; omega
    rw [show m + 2 - (k + 1) - 1 = m - k by omega, show m + 2 - (k + 1) = (m - k) + 1 by omega,
      show m + 2 - 2 * (k + 1) = m - 2 * k by omega, Nat.factorial_succ, Nat.factorial_succ k]
    have hk' : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
    have hk1 : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast (by omega : k + 1 ≠ 0)
    have hmk : ((m - 2 * k).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (m - 2 * k).factorial_ne_zero
    push_cast [Nat.cast_sub (by omega : k ≤ m)]
    field_simp
    ring
  rw [add_sub_right_comm, ← Finset.sum_sub_distrib, Finset.sum_congr rfl hkey,
    ← Finset.mul_sum] at h
  have hf : ((m + 2).factorial : ℂ) = (m + 2) * (m + 1).factorial := by
    rw [Nat.factorial_succ (m + 1)]; push_cast; ring
  have hf' : ((m + 1).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (m + 1).factorial_ne_zero
  have hm : (m : ℂ) + 2 ≠ 0 := by exact_mod_cast (by omega : m + 2 ≠ 0)
  simp only [pow_zero, Nat.sub_zero, mul_zero, Nat.factorial_zero, Nat.cast_one, one_mul, hf] at h ⊢
  push_cast at h ⊢
  field_simp at h ⊢
  linear_combination h

end DLMF.OrthogonalPolynomials
