/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Basic.Definitions
public import DLMF.Hypergeometric.Basic.GaussEquation
public import DLMF.Confluent.Basic.KummerProperties
public import DLMFMathlib.Analysis.Complex.NonInteger

/-!
# Basic properties of the classical orthogonal polynomials

Initial values, explicit sums, values at the endpoints, symmetry, and the bridges to the
Mathlib polynomials for the physicists' Hermite, Laguerre, Jacobi, Legendre, Gegenbauer and
Chebyshev families defined in `DLMF.OrthogonalPolynomials.Basic.Definitions`.

## Main results

* `hermitePolyH_zero`, `hermitePolyH_one`, `hermitePolyH_two`, `hermitePolyH_derivative`:
  initial values (DLMF 18.5.18) and the derivative formula DLMF 18.9.25.
* `aeval_hermitePolyH_succ_succ`: the Hermite three-term recurrence.
* `aeval_hermitePolyH_eq_hermite`: `H_n(x) = 2^{n/2} He_n(√2 x)`, relating to Mathlib's
  probabilists' Hermite polynomials (DLMF 18.7.11–18.7.12).
* `hermitePolyH_reflection`, `hermitePolyH_even_at_zero`: parity and values at `0`
  (Table 18.6.1).
* `laguerrePolyL_zero`, `jacobiPolyP_zero`, `legendrePolyP_zero`, `ultrasphPoly_zero`: the
  polynomials of degree zero.
* `laguerrePolyL_eq_sum_coeff`, `laguerrePolyL_eq_sum`, `laguerreExtended_eq`: explicit sums
  for `L_n^{(α)}` (DLMF 18.5.12).
* `laguerrePolyL_at_zero`, `jacobiPolyP_one`, `ultrasphPoly_at_one`, `chebyshevV_at_one`,
  `chebyshevW_at_one`: values at the endpoints (DLMF 18.6.1 and Table 18.6.1).
* `aeval_shiftedLegendre_eq_legendrePolyP`: Mathlib's shifted Legendre polynomials in terms of
  `legendrePolyP` (DLMF 18.7.10).
* `eval_U_eq_ultrasphPoly`: Mathlib's Chebyshev `U_n = C_n^{(1)}` (DLMF 18.7.4).
* `ultrasphPoly_eq_jacobiPolyP`, `legendre_eq_ultrasphPoly`: Gegenbauer polynomials as Jacobi
  polynomials and Legendre polynomials as Gegenbauer polynomials (DLMF 18.7.1, 18.7.9).

## Implementation notes

Orthogonality, generating functions and the Rodrigues formula are in
`DLMF.OrthogonalPolynomials.Classical`; the explicit sums of §18.5 for the other families are
in `DLMF.OrthogonalPolynomials.Explicit`.
-/

@[expose] public section

open Complex Polynomial
open scoped Nat
open DLMF.Hypergeometric
open DLMF.Confluent

noncomputable section

namespace DLMF.OrthogonalPolynomials

/-- A point of positive real part is not a nonpositive integer. -/
private lemma classicalBasic_not_neg_nat_of_re_pos {w : ℂ} (hw : 0 < w.re) :
    ∀ k : ℕ, w ≠ -k := by
  intro k h
  have hre := congrArg Complex.re h
  simp only [Complex.neg_re, Complex.natCast_re] at hre
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

/-- `H_0 = 1` (DLMF 18.5.18). -/
@[simp, dlmf 18.5.E18]
theorem hermitePolyH_zero : hermitePolyH 0 = 1 := rfl

/-- The recursion `H_{n+1} = 2x H_n - H_n'` defining the Hermite polynomials. -/
@[simp]
theorem hermitePolyH_succ (n : ℕ) :
    hermitePolyH (n + 1) = 2 * X * hermitePolyH n - derivative (hermitePolyH n) :=
  rfl

/-- Identity under the stated parameter and domain assumptions: `hermitePolyH 1 = 2 * X`. -/
@[dlmf 18.5.E18]
theorem hermitePolyH_one : hermitePolyH 1 = 2 * X := by
  simp [hermitePolyH_succ, hermitePolyH_zero]

/-- Identity under the stated parameter and domain assumptions: `hermitePolyH 2 = 4 * X ^ 2 - 2`. -/
@[dlmf 18.5.E18]
theorem hermitePolyH_two : hermitePolyH 2 = 4 * X ^ 2 - 2 := by
  simp [hermitePolyH_succ, pow_two]
  ring

/-- Identity under the stated parameter and domain assumptions: `derivative (hermitePolyH (n + 1))
= C (2 * (n + 1) : ℤ) * hermitePolyH n`. -/
@[dlmf 18.9.E25]
theorem hermitePolyH_derivative (n : ℕ) :
    derivative (hermitePolyH (n + 1)) = C (2 * (n + 1) : ℤ) * hermitePolyH n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show n + 1 + 1 = (n + 1) + 1 by omega, hermitePolyH_succ (n + 1)]
    simp only [derivative_sub, derivative_mul, derivative_ofNat, derivative_X,
      zero_mul, zero_add, mul_one]
    rw [ih]
    simp only [derivative_mul, derivative_C, zero_mul, zero_add]
    rw [hermitePolyH_succ n]
    push_cast
    simp only [map_add, map_mul, map_natCast, map_ofNat, map_one]
    ring

/-- The Hermite recurrence in evaluated form. -/
theorem aeval_hermitePolyH_succ_succ (x : ℂ) (n : ℕ) :
    (aeval x (hermitePolyH (n + 2)) : ℂ) =
      2 * x * aeval x (hermitePolyH (n + 1)) - 2 * (n + 1) * aeval x (hermitePolyH n) := by
  rw [hermitePolyH_succ (n + 1), hermitePolyH_derivative]
  simp only [map_sub, map_mul, aeval_X, aeval_C, map_ofNat]
  push_cast
  ring

/-- Relation to Mathlib's probabilists' Hermite polynomials:
`H_n(x) = 2^{n/2} He_n(√2 x)`. -/
@[dlmf 18.7.E11, dlmf 18.7.E12]
theorem aeval_hermitePolyH_eq_hermite (n : ℕ) (x : ℝ) :
    aeval x (hermitePolyH n) =
      (2 : ℝ) ^ (n / 2 : ℝ) * aeval (Real.sqrt 2 * x) (hermite n) := by
  have hscale (n : ℕ) (x : ℝ) : aeval x (hermitePolyH n) =
      Real.sqrt 2 ^ n * aeval (Real.sqrt 2 * x) (hermite n) := by
    induction n generalizing x with
    | zero => simp
    | succ n ih =>
      have hd := congrArg (fun f : ℝ → ℝ => deriv f x) (funext ih)
      have hcomp : HasDerivAt (fun y : ℝ => (aeval (Real.sqrt 2 * y) (hermite n) : ℝ))
          (aeval (Real.sqrt 2 * x) (derivative (hermite n)) * (Real.sqrt 2 * 1)) x :=
        ((hermite n).hasDerivAt_aeval (Real.sqrt 2 * x)).comp x
          ((hasDerivAt_id x).const_mul (Real.sqrt 2))
      rw [deriv_const_mul_field, hcomp.deriv, Polynomial.deriv_aeval] at hd
      simp only [mul_one] at hd
      simp only [hermitePolyH_succ, hermite_succ, map_sub, map_mul, map_ofNat, aeval_X,
        ih, hd, pow_succ]
      ring_nf
      norm_num [Real.sq_sqrt]
      ring
  rw [hscale, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 2
  ring

/-- `L_0^{(α)}(x) = 1` (DLMF 18.5.17). -/
@[simp, dlmf 18.5.E17, dlmf 18.5.E17_5]
theorem laguerrePolyL_zero (α x : ℂ) : laguerrePolyL α 0 x = 1 := by
  simp [laguerrePolyL, poch_zero, kummerM_of_zero_param]

/-- The terminating expansion, with coefficients separated from the variable. -/
@[dlmf 18.11.E2]
theorem laguerrePolyL_eq_sum_coeff (α : ℂ) (n : ℕ) (x : ℂ) :
    laguerrePolyL α n x = ∑ j ∈ Finset.range (n + 1),
      (poch (α + 1) n / n.factorial * kummerMCoeff (-(n : ℂ)) (α + 1) j) * x ^ j := by
  unfold laguerrePolyL
  rw [kummerM_eq_sum_neg_nat, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Helper lemma for `laguerrePolyL_generating_function`: the explicit terminating sum
`L_n^{(α)}(x) = ∑_{k=0}^n (α+1+k)_{n-k} (-x)^k / ((n-k)! k!)`. -/
@[dlmf 18.5.E12]
theorem laguerrePolyL_eq_sum {α : ℂ} (hα : ∀ k : ℕ, α + 1 ≠ -(k : ℂ)) (n : ℕ) (x : ℂ) :
    laguerrePolyL α n x =
      ∑ k ∈ Finset.range (n + 1),
        poch (α + 1 + k) (n - k) / ((n - k).factorial * k.factorial : ℂ) * (-x) ^ k := by
  have hn : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  unfold laguerrePolyL
  rw [kummerM_eq_sum_neg_nat, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hck := poch_ne_zero_of_not_neg_nat hα k
  have hk0 : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hnk : ((n - k).factorial : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (n - k).factorial_ne_zero
  have hadd := poch_add (α + 1) k (n - k)
  rw [Nat.add_sub_of_le hk'] at hadd
  have hdesc : (n.descFactorial k : ℂ) * (n - k).factorial = n.factorial := by
    have h := congrArg (Nat.cast : ℕ → ℂ)
      (show n.descFactorial k * (n - k).factorial = n.factorial by
        rw [Nat.descFactorial_eq_factorial_mul_choose]
        convert Nat.choose_mul_factorial_mul_factorial hk' using 1
        ring)
    simpa [Nat.cast_mul] using h
  have hdesc' : (n.descFactorial k : ℂ) = n.factorial / (n - k).factorial :=
    eq_div_of_mul_eq hnk hdesc
  rw [poch_neg_coe_nat, hadd, hdesc']
  field [hck, hn, hk0, hnk]

/-- `P_0^{(α,β)}(x) = 1`. -/
@[simp]
theorem jacobiPolyP_zero (α β x : ℂ) : jacobiPolyP α β 0 x = 1 := by
  simp [jacobiPolyP, poch_zero, ordinaryHypergeometric_zero_left]

/-- Identity under the stated parameter and domain assumptions: `legendrePolyP 0 x = 1`. -/
@[dlmf 18.5.E16]
theorem legendrePolyP_zero (x : ℂ) : legendrePolyP 0 x = 1 := by simp [legendrePolyP]

/-- Helper lemma for `aeval_shiftedLegendre_eq_legendrePolyP`. -/
theorem poch_nat_succ_eq_choose_mul_factorial (n k : ℕ) :
    poch ((n : ℂ) + 1) k = (n + k).choose n * k ! := by
  have hn : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hpoch : (n ! : ℂ) * poch ((n : ℂ) + 1) k = (n + k)! := by
    simpa [poch] using factorial_mul_ascPochhammer ℂ n k
  have hch : ((n + k).choose n : ℂ) * n ! * k ! = (n + k)! := by
    have h := congrArg (Nat.cast : ℕ → ℂ)
      (Nat.choose_mul_factorial_mul_factorial (show n ≤ n + k by omega))
    simpa [Nat.add_sub_cancel_left] using h
  apply mul_left_cancel₀ hn
  calc
    (n ! : ℂ) * poch ((n : ℂ) + 1) k = (n + k)! := hpoch
    _ = ((n + k).choose n : ℂ) * n ! * k ! := hch.symm
    _ = n ! * ((n + k).choose n * k !) := by ring

/-- Mathlib's `shiftedLegendre n` is `∑_k (-1)^k C(n,k) C(n+k,n) X^k`, whose leading
coefficient is `(-1)^n C(2n,n)`. The standard shifted Legendre polynomial `P_n(2x-1)`
has leading coefficient `C(2n,n)` (DLMF 18.7.10). Consequently Mathlib's polynomial
evaluates as `P_n(1-2x)` rather than `P_n(2x-1)`. -/
@[dlmf 18.7.E10]
theorem aeval_shiftedLegendre_eq_legendrePolyP (n : ℕ) (x : ℂ) :
    aeval x ((shiftedLegendre n).map (Int.castRingHom ℂ)) = legendrePolyP n (1 - 2 * x) := by
  have hmap : aeval x ((shiftedLegendre n).map (Int.castRingHom ℂ)) =
      aeval x (shiftedLegendre n) := by
    simp [aeval_def, eval₂_map]
  have hjac : legendrePolyP n (1 - 2 * x) =
      ₂F₁ (-(n : ℂ)) ((n : ℂ) + 1) 1 x := by
    unfold legendrePolyP jacobiPolyP
    have harg : (1 - (1 - 2 * x)) / 2 = x := by ring
    have hpoch : poch (0 + 1) n / (n.factorial : ℂ) = 1 := by
      rw [zero_add, poch_nat_one, div_self (Nat.cast_ne_zero.mpr n.factorial_ne_zero)]
    rw [hpoch, one_mul, harg]
    simp [add_zero]
  rw [hmap, aeval_eq_sum_range, natDegree_shiftedLegendre, hjac,
    ordinaryHypergeometric_eq_sum_neg_nat]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hcoeff : ((shiftedLegendre n).coeff k : ℂ) =
      (-1 : ℂ) ^ k * n.choose k * (n + k).choose n := by
    simp [coeff_shiftedLegendre]
  have hhg : gaussHGCoeff (-(n : ℂ)) ((n : ℂ) + 1) 1 k =
      (-1 : ℂ) ^ k * n.choose k * (n + k).choose n := by
    have hk0 : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
    rw [gaussHGCoeff_neg_nat, poch_nat_one, poch_nat_succ_eq_choose_mul_factorial]
    field_simp [hk0]
  simp [Algebra.smul_def, hcoeff, hhg]

/-- A terminating Gauss series is analytic everywhere, including its endpoints. -/
theorem analyticAt_gauss_neg_nat (n : ℕ) (b c z : ℂ) :
    AnalyticAt ℂ (₂F₁ (-(n : ℂ)) b c) z := by
  have heq : ₂F₁ (-(n : ℂ)) b c = fun w : ℂ =>
      ∑ k ∈ Finset.range (n + 1), gaussHGCoeff (-(n : ℂ)) b c k * w ^ k :=
    funext fun w => ordinaryHypergeometric_eq_sum_neg_nat n b c w
  rw [heq]
  fun_prop

/-- `C_0^{(λ)}(x) = 1`. -/
@[simp]
theorem ultrasphPoly_zero (lam x : ℂ) : ultrasphPoly lam 0 x = 1 := by
  simp [ultrasphPoly, poch_zero, ordinaryHypergeometric_zero_left]

/-- Helper lemma for `eval_U_eq_ultrasphPoly`: `(2)_n / n! = n+1`. -/
@[dlmf 18.5.E11_4]
theorem ultrasphPoly_param_one_eq (n : ℕ) (x : ℂ) :
    ultrasphPoly (1 : ℂ) n x =
      (n + 1 : ℂ) * ₂F₁ (-(n : ℂ)) ((n : ℂ) + 2) (3 / 2) ((1 - x) / 2) := by
  have hne : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hs : poch (2 : ℂ) n / n.factorial = (n + 1 : ℂ) := by
    rw [poch_nat_two]
    have hfac : ((n + 1).factorial : ℂ) = (n + 1 : ℂ) * n.factorial := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    rw [hfac, mul_div_cancel_right₀ _ hne]
  have hF :
      ₂F₁ (-(n : ℂ)) ((n : ℂ) + 2 * 1) ((1 : ℂ) + 1 / 2) ((1 - x) / 2) =
        ₂F₁ (-(n : ℂ)) ((n : ℂ) + 2) (3 / 2) ((1 - x) / 2) := by
    congr
    · ring
    · ring
  simp only [ultrasphPoly]
  rw [hF, show (2 * (1 : ℂ)) = (2 : ℂ) by ring, hs]

/-- Helper lemma for `eval_U_eq_ultrasphPoly`. -/
theorem ultrasphPoly_one_one (x : ℂ) : ultrasphPoly (1 : ℂ) 1 x = 2 * x := by
  rw [ultrasphPoly_param_one_eq]
  simp only [Nat.cast_one, one_add_one_eq_two]
  have h3 : (1 : ℂ) + 2 = 3 := by norm_num
  have hneg : (-1 : ℂ) = -(1 : ℕ) := by simp
  rw [h3, hneg, ordinaryHypergeometric_eq_sum_neg_nat (n := 1)]
  have h0 : gaussHGCoeff (-1 : ℂ) 3 (3 / 2) 0 = 1 := by
    simp [gaussHGCoeff, poch_zero]
  have h1 : gaussHGCoeff (-1 : ℂ) 3 (3 / 2) 1 = -2 := by
    simp [gaussHGCoeff, poch_one]
    ring
  simp [Finset.sum_range_succ]
  rw [h0, h1]
  ring

/-- Helper lemma for `eval_U_eq_ultrasphPoly`: `(1/2)_k = (2k)! / (4^k k!)`. -/
theorem poch_half (k : ℕ) :
    poch (1 / 2 : ℂ) k = (2 * k).factorial / (4 ^ k * k.factorial : ℂ) := by
  induction k with
  | zero => simp [poch_zero]
  | succ k ih =>
    have hk0 : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
    have h2k : ((2 * k).factorial : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (2 * k).factorial_ne_zero
    have h4 : (4 : ℂ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
    have hk1 : (k + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    rw [poch_succ, ih]
    have hks : ((k + 1).factorial : ℂ) = (k + 1) * k.factorial := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    have h2ks : ((2 * (k + 1)).factorial : ℂ) =
        (2 * k + 2 : ℂ) * (2 * k + 1) * (2 * k).factorial := by
      have h : 2 * (k + 1) = 2 * k + 2 := by omega
      rw [h, Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      ring
    have h4s : (4 : ℂ) ^ (k + 1) = 4 * 4 ^ k := by rw [pow_succ']
    have : ((2 * (k + 1)).factorial : ℂ) / (4 ^ (k + 1) * (k + 1).factorial) =
        (2 * k).factorial / (4 ^ k * k.factorial) * (1 / 2 + k) := by
      rw [h2ks, h4s, hks]
      field [hk0, h2k, h4, hk1]
    exact this.symm

/-- The rising factorial starting at `3/2`, expressed using ordinary factorials. -/
theorem poch_three_halves_factorial (k : ℕ) :
    poch (3 / 2 : ℂ) k = (2 * k + 1).factorial / (4 ^ k * k.factorial : ℂ) := by
  have hk0 : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have h4 : (4 : ℂ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  have h2k : ((2 * k).factorial : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (2 * k).factorial_ne_zero
  rw [poch_three_halves_eq, poch_half]
  have hfac : ((2 * k + 1).factorial : ℂ) = (2 * k + 1 : ℂ) * (2 * k).factorial := by
    have h : 2 * k + 1 = (2 * k).succ := by omega
    rw [h, Nat.factorial_succ]
    push_cast
    ring
  rw [hfac]
  field [hk0, h4, h2k]

/-- Helper lemma for `eval_U_eq_ultrasphPoly`: coefficient of `((1-x)/2)^k` in `C_n^{(1)}(x)`. -/
theorem ultrasphPoly_one_coeff {n k : ℕ} (hk : k ≤ n) :
    (n + 1 : ℂ) * gaussHGCoeff (-(n : ℂ)) ((n : ℂ) + 2) (3 / 2) k =
      (-1 : ℂ) ^ k * (4 : ℂ) ^ k * (n + k + 1).factorial /
        ((n - k).factorial * (2 * k + 1).factorial : ℂ) := by
  have hk0 : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hn : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hn1 : ((n + 1).factorial : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (n + 1).factorial_ne_zero
  have hnk : ((n - k).factorial : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (n - k).factorial_ne_zero
  have h2k : ((2 * k + 1).factorial : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (2 * k + 1).factorial_ne_zero
  have h4 : (4 : ℂ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  have hpoch : poch ((n : ℂ) + 2) k =
      (n + 1 + k).factorial / (n + 1).factorial := by
    have h := poch_nat_succ_eq_choose_mul_factorial (n + 1) k
    have harg : ((n + 1 : ℕ) : ℂ) + 1 = (n : ℂ) + 2 := by push_cast; ring
    rw [harg] at h
    have hmul : ((n + 1 + k).choose (n + 1) : ℂ) * (n + 1).factorial * k.factorial =
        (n + 1 + k).factorial := by
      have h' := congrArg (Nat.cast : ℕ → ℂ)
        (Nat.choose_mul_factorial_mul_factorial (show n + 1 ≤ n + 1 + k by omega))
      simpa [Nat.add_sub_cancel_left] using h'
    rw [h]
    apply eq_div_of_mul_eq hn1
    convert hmul using 1
    ring
  have hch : (n.choose k : ℂ) =
      n.factorial / (k.factorial * (n - k).factorial) := by
    have hmul := congrArg (Nat.cast : ℕ → ℂ)
      (Nat.choose_mul_factorial_mul_factorial hk)
    apply eq_div_of_mul_eq (mul_ne_zero hk0 hnk)
    simpa [mul_assoc] using hmul
  have hnk' : n + k + 1 = n + 1 + k := by omega
  have hfac : ((n + 1).factorial : ℂ) = (n + 1) * n.factorial := by
    rw [Nat.factorial_succ]; push_cast; ring
  rw [gaussHGCoeff_neg_nat, poch_three_halves_factorial, hpoch, hch, hnk', hfac]
  field [hk0, hn, hn1, hnk, h2k, h4]

/-- Helper lemma for `eval_U_eq_ultrasphPoly`. -/
theorem gegenbauerB_eq (n k : ℕ) :
    gegenbauerB n k =
      (n + 1 : ℂ) * gaussHGCoeff (-(n : ℂ)) ((n : ℂ) + 2) (3 / 2) k := by
  by_cases h : k ≤ n
  · simp [gegenbauerB, h, ultrasphPoly_one_coeff h]
  · simp [gegenbauerB, h, gaussHGCoeff, poch_neg_nat_eq_zero (Nat.lt_of_not_ge h)]

/-- Helper lemma for `eval_U_eq_ultrasphPoly`. -/
theorem gegenbauerB_zero (n : ℕ) : gegenbauerB n 0 = n + 1 := by
  simp [gegenbauerB]
  have hfac : ((n + 1).factorial : ℂ) = (n + 1) * n.factorial := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hn : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  rw [hfac]
  field [hn]

/-- Taylor derivatives of Chebyshev `U` at one match the terminating Gauss coefficients. -/
theorem iterate_derivative_U_eq_gaussHGCoeff (n k : ℕ) :
    (derivative^[k] (Polynomial.Chebyshev.U ℂ n)).eval 1 =
      k.factorial * (n + 1 : ℂ) * gaussHGCoeff (-(n : ℂ)) (n + 2) (3 / 2) k *
        (-(1 / 2 : ℂ)) ^ k := by
  induction k with
  | zero => simp [gaussHGCoeff, poch_zero, Polynomial.Chebyshev.U_eval_one]
  | succ k ih =>
    have hU := Polynomial.Chebyshev.iterate_derivative_U_eval_one_recurrence
      (R := ℂ) (n : ℤ) k
    have hF := gaussHGCoeff_recurrence (a := -(n : ℂ)) (b := (n : ℂ) + 2)
      Complex.three_div_two_ne_neg_natCast k
    have hne : (2 * k + 3 : ℂ) ≠ 0 := by
      have hpos : (0 : ℝ) < 2 * k + 3 := by positivity
      exact_mod_cast ne_of_gt hpos
    rw [ih] at hU
    push_cast at hU
    apply mul_left_cancel₀ hne
    rw [hU, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    linear_combination
      -2 * (k.factorial : ℂ) * (n + 1) * (-(1 / 2 : ℂ)) ^ (k + 1) * hF

/-- Chebyshev `U` as Gegenbauer with `λ = 1`: `U_n = C_n^{(1)}`.
The Taylor expansion at one is identified coefficientwise using Mathlib's recurrence
for the iterated derivatives of `U_n` and the Gauss coefficient recurrence. -/
@[dlmf 18.7.E4]
theorem eval_U_eq_ultrasphPoly (n : ℕ) (x : ℂ) :
    (Polynomial.Chebyshev.U ℂ n).eval x = ultrasphPoly 1 n x := by
  rw [ultrasphPoly_param_one_eq, ordinaryHypergeometric_eq_sum_neg_nat, Finset.mul_sum]
  rw [← Polynomial.taylor_eval_sub 1 (Polynomial.Chebyshev.U ℂ n) x,
    Polynomial.eval_eq_sum_range, Polynomial.natDegree_taylor,
    Polynomial.Chebyshev.natDegree_U_natCast]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hd := iterate_derivative_U_eq_gaussHGCoeff n k
  have hh := congrArg (fun p : ℂ[X] => p.eval 1)
    (congrFun (Polynomial.factorial_smul_hasseDeriv (R := ℂ) k)
      (Polynomial.Chebyshev.U ℂ n))
  change (k.factorial • hasseDeriv k (Polynomial.Chebyshev.U ℂ n)).eval 1 = _ at hh
  simp only [nsmul_eq_mul, eval_mul, eval_natCast] at hh
  rw [Polynomial.taylor_coeff]
  have hk : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  apply mul_left_cancel₀ hk
  calc
    _ = (k.factorial * (hasseDeriv k (Polynomial.Chebyshev.U ℂ n)).eval 1) *
        (x - 1) ^ k := by ring
    _ = _ := by
      rw [hh, hd]
      have hp : (-(1 / 2 : ℂ)) ^ k * (x - 1) ^ k = ((1 - x) / 2) ^ k := by
        rw [← mul_pow]
        congr 1
        ring
      rw [mul_assoc _ ((-(1 / 2 : ℂ)) ^ k), hp]
      ring

/-- Relation of Gegenbauer to Jacobi (AAR §6.11). Requires `(λ+1/2)_n ≠ 0` so that the
Jacobi representation is defined. -/
@[dlmf 18.7.E1]
theorem ultrasphPoly_eq_jacobiPolyP {lam : ℂ} (n : ℕ) (x : ℂ)
    (h : poch (lam + 1 / 2) n ≠ 0) :
    ultrasphPoly lam n x =
      poch (2 * lam) n / poch (lam + 1 / 2) n *
        jacobiPolyP (lam - 1 / 2) (lam - 1 / 2) n x := by
  unfold ultrasphPoly jacobiPolyP
  have hα : (lam - 1 / 2) + 1 = lam + 1 / 2 := by ring
  have hb : (n : ℂ) + (lam - 1 / 2) + (lam - 1 / 2) + 1 = n + 2 * lam := by ring
  simp_rw [hα, hb]
  field [h, Nat.cast_ne_zero.mpr n.factorial_ne_zero]

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

/-- Identity under the stated parameter and domain assumptions: `laguerrePolyL α n 0 = poch (α +
1) n / n.factorial`. -/
@[dlmf 18.6.E1]
theorem laguerrePolyL_at_zero (α : ℂ) (n : ℕ) : laguerrePolyL α n 0 = poch (α + 1) n
    / n.factorial := by
  simp [laguerrePolyL]

/-- Identity under the stated parameter and domain assumptions: `jacobiPolyP α β n 1 = poch (α +
1) n / n.factorial`. -/
@[dlmf 18.6.T1]
theorem jacobiPolyP_one {α β : ℂ} (n : ℕ) :
    jacobiPolyP α β n 1 = poch (α + 1) n / n.factorial := by
  simp [jacobiPolyP]

/-- Jacobi polynomials do not vanish at `x = 1` for `Re α > -1`. -/
theorem jacobiPolyP_one_ne_zero {α β : ℂ} (hα : -1 < α.re) (n : ℕ) : jacobiPolyP α β n 1 ≠ 0 := by
  rw [jacobiPolyP_one]
  exact div_ne_zero (poch_ne_zero_of_not_neg_nat (classicalBasic_not_neg_nat_of_re_pos (by
    simp only [Complex.add_re, Complex.one_re]
    linarith)) n) (Nat.cast_ne_zero.mpr n.factorial_ne_zero)

/-- Identity under the stated parameter and domain assumptions: `ultrasphPoly lam n 1 = poch (2 *
lam) n / n.factorial`. -/
@[dlmf 18.6.T1]
theorem ultrasphPoly_at_one {lam : ℂ} (n : ℕ) :
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

end DLMF.OrthogonalPolynomials
