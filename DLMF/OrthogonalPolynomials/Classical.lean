/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.Basic
public import DLMF.Hypergeometric.DiffEq
public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.RingTheory.Polynomial.Chebyshev
public import Mathlib.RingTheory.Polynomial.Hermite.Basic
public import Mathlib.RingTheory.Polynomial.ShiftedLegendre
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.SpecialFunctions.Bernstein

/-!
# Classical orthogonal polynomials (AAR Chapter 6)

Mathlib has the probabilists' Hermite polynomials `Polynomial.hermite` and the shifted
Legendre polynomials `shiftedLegendre`. This file adds the physicists' Hermite polynomials,
Laguerre, Jacobi, and Gegenbauer (ultraspherical) families, together with the standard
hypergeometric representations (AAR §§6.1–6.4, 6.10–6.11).
-/

@[expose] public section

open Complex Polynomial MeasureTheory intervalIntegral
open scoped Real Nat
open DLMF.Hypergeometric
open DLMF.Confluent

noncomputable section

namespace DLMF.OrthogonalPolynomials

/-- Physicists' Hermite polynomials, AAR §6.1: `H_{n+1} = 2x H_n - H_n'`. -/
def hermitePolyH : ℕ → ℤ[X]
  | 0 => 1
  | n + 1 => 2 * X * hermitePolyH n - derivative (hermitePolyH n)

/-- `H_0 = 1` (DLMF 18.5.18). -/
@[simp, dlmf 18.5.E18]
theorem hermitePolyH_zero : hermitePolyH 0 = 1 := rfl

/-- The recursion `H_{n+1} = 2x H_n - H_n'` defining the Hermite polynomials. -/
@[simp]
theorem hermitePolyH_succ (n : ℕ) :
    hermitePolyH (n + 1) = 2 * X * hermitePolyH n - derivative (hermitePolyH n) :=
  rfl

@[dlmf 18.5.E18]
theorem hermitePolyH_one : hermitePolyH 1 = 2 * X := by
  simp [hermitePolyH_succ, hermitePolyH_zero]

@[dlmf 18.5.E18]
theorem hermitePolyH_two : hermitePolyH 2 = 4 * X ^ 2 - 2 := by
  simp [hermitePolyH_succ, pow_two]
  ring

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

/-- Rodrigues formula for physicists' Hermite polynomials, AAR §6.1. -/
@[dlmf 18.5.T1]
theorem deriv_gaussian_eq_hermitePolyH (n : ℕ) (x : ℝ) :
    deriv^[n] (fun y => Real.exp (-(y ^ 2))) x =
      (-1 : ℝ) ^ n * aeval x (hermitePolyH n) * Real.exp (-(x ^ 2)) := by
  -- A direct adaptation of Mathlib's
  -- `Polynomial.deriv_gaussian_eq_hermite_mul_gaussian` to the physicists' normalization.
  rw [mul_assoc]
  induction n generalizing x with
  | zero => simp [hermitePolyH_zero]
  | succ n ih =>
    replace ih : deriv^[n] _ = _ := funext ih
    have hgaussian : deriv (fun y : ℝ => Real.exp (-(y ^ 2))) x =
        -(2 * x) * Real.exp (-(x ^ 2)) := by
      rw [deriv_exp (by fun_prop)]
      simp
      ring
    rw [Function.iterate_succ_apply', ih, deriv_const_mul_field, deriv_fun_mul,
      pow_succ, hgaussian, hermitePolyH_succ, map_sub, map_mul, map_mul, map_ofNat,
      aeval_X, Polynomial.deriv_aeval]
    · ring_nf
    · apply Polynomial.differentiable_aeval
    · fun_prop

/-- Complex Rodrigues formula for physicists' Hermite polynomials. Helper lemma for
`hermitePolyH_generating_function`. -/
theorem iteratedDeriv_cexp_neg_sq (n : ℕ) (x : ℂ) :
    iteratedDeriv n (fun y : ℂ => exp (-(y ^ 2))) x =
      (-1 : ℂ) ^ n * (aeval x (hermitePolyH n) : ℂ) * exp (-(x ^ 2)) := by
  rw [iteratedDeriv_eq_iterate, mul_assoc]
  induction n generalizing x with
  | zero => simp [hermitePolyH_zero]
  | succ n ih =>
    replace ih : deriv^[n] _ = _ := funext ih
    have hgaussian : deriv (fun y : ℂ => exp (-(y ^ 2))) x =
        -(2 * x) * exp (-(x ^ 2)) := by
      rw [deriv_cexp (by fun_prop)]
      simp [pow_two]
      ring
    rw [Function.iterate_succ_apply', ih, deriv_const_mul_field, deriv_fun_mul,
      pow_succ, hgaussian, hermitePolyH_succ, map_sub, map_mul, map_mul, map_ofNat,
      aeval_X, Polynomial.deriv_aeval]
    · ring_nf
    · apply Polynomial.differentiable_aeval
    · fun_prop

/-- Generating function `∑ H_n(x) t^n / n! = exp(2xt - t²)` (AAR §6.1). -/
theorem hasSum_hermitePolyH_generating_function (x t : ℂ) :
    HasSum (fun n : ℕ => (aeval x (hermitePolyH n) : ℂ) * t ^ n / n !)
      (exp (2 * x * t - t ^ 2)) := by
  have hf : Differentiable ℂ (fun y : ℂ => exp (-(y ^ 2))) := by fun_prop
  have hne : exp (-(x ^ 2)) ≠ 0 := exp_ne_zero _
  have hs := Complex.hasSum_taylorSeries_of_entire (E := ℂ) hf x (x - t)
  have hterm : (fun n : ℕ =>
      (n ! : ℂ)⁻¹ • ((x - t) - x) ^ n •
        iteratedDeriv n (fun y : ℂ => exp (-(y ^ 2))) x) =
      fun n => (aeval x (hermitePolyH n) : ℂ) * t ^ n / n ! * exp (-(x ^ 2)) := by
    funext n
    simp only [sub_sub_cancel_left, smul_eq_mul]
    rw [iteratedDeriv_cexp_neg_sq, neg_pow]
    ring_nf
    rw [mul_comm n 2, pow_mul, neg_one_sq, one_pow]
    ring
  rw [hterm] at hs
  have hs' := hs.mul_right (exp (-(x ^ 2)))⁻¹
  have hsimp : (fun n : ℕ =>
      (aeval x (hermitePolyH n) : ℂ) * t ^ n / n ! * exp (-(x ^ 2)) *
        (exp (-(x ^ 2)))⁻¹) =
      fun n => (aeval x (hermitePolyH n) : ℂ) * t ^ n / n ! := by
    funext n
    field [hne]
  rw [hsimp] at hs'
  have hval : exp (-((x - t) ^ 2)) * (exp (-(x ^ 2)))⁻¹ =
      exp (2 * x * t - t ^ 2) := by
    rw [← div_eq_mul_inv, div_eq_iff hne, ← exp_add]
    congr 1
    ring
  simpa only [hval] using hs'

/-- Exponential generating function of the physicists' Hermite polynomials. -/
@[dlmf 18.12.E15]
theorem hermitePolyH_generating_function (x t : ℂ) :
    ∑' n : ℕ, (aeval x (hermitePolyH n) : ℂ) * t ^ n / n ! =
      exp (2 * x * t - t ^ 2) :=
  (hasSum_hermitePolyH_generating_function x t).tsum_eq

/-- Hypergeometric realization of generalized Laguerre polynomials, AAR §6.2,
for `α + 1` not a nonpositive integer:
`L_n^{(α)}(x) = (α+1)_n / n! · ₁F₁(-n; α+1; x)`. -/
@[dlmf 18.5.E12]
def laguerrePolyL (α : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  poch (α + 1) n / n ! * kummerM (-n : ℂ) (α + 1) x

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

/-- Moments of the Laguerre weight are Gamma values; integrability is recorded as well. -/
theorem laguerrePolyL_weight_moment {α : ℝ} (hα : -1 < α) (k : ℕ) :
    Integrable (fun x : ℝ => (x : ℂ) ^ k * (x : ℂ) ^ (α : ℂ) * exp (-(x : ℂ)))
      (volume.restrict (Set.Ioi 0)) ∧
    (∫ x : ℝ in Set.Ioi 0, (x : ℂ) ^ k * (x : ℂ) ^ (α : ℂ) * exp (-(x : ℂ))) =
      Gamma ((α : ℂ) + k + 1) := by
  have hs : 0 < ((α : ℂ) + k + 1).re := by
    simp only [add_re, ofReal_re, natCast_re, one_re]
    have := Nat.cast_nonneg (α := ℝ) k
    linarith
  have heq : (fun x : ℝ => (x : ℂ) ^ k * (x : ℂ) ^ (α : ℂ) * exp (-(x : ℂ))) =ᵐ[
      volume.restrict (Set.Ioi 0)]
      (fun x : ℝ => ((-x).exp : ℂ) * (x : ℂ) ^ (((α : ℂ) + k + 1) - 1)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hx)
    rw [add_sub_cancel_right, cpow_add _ _ hx0, cpow_natCast]
    simp only [ofReal_exp, ofReal_neg]
    ring
  refine ⟨(GammaIntegral_convergent hs).congr heq.symm, ?_⟩
  rw [integral_congr_ae heq, Gamma_eq_integral hs, GammaIntegral]

/-- Expand a weighted Laguerre monomial into finitely many weight moments. -/
theorem laguerrePolyL_mul_monomial_eq_sum (α : ℂ) (n k : ℕ) (x : ℝ) :
    laguerrePolyL α n x * (x : ℂ) ^ k * (x : ℂ) ^ α * exp (-(x : ℂ)) =
      ∑ j ∈ Finset.range (n + 1),
        (poch (α + 1) n / n.factorial * kummerMCoeff (-(n : ℂ)) (α + 1) j) *
          ((x : ℂ) ^ (k + j) * (x : ℂ) ^ α * exp (-(x : ℂ))) := by
  rw [laguerrePolyL_eq_sum_coeff]
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_add]
  ring

/-- For `α > -1`, `L_n^{(α)}(x) xᵏ x^α e^{-x}` is integrable on `(0, ∞)`. -/
theorem integrable_laguerrePolyL_mul_monomial {α : ℝ} (hα : -1 < α) (n k : ℕ) :
    Integrable (fun x : ℝ => laguerrePolyL α n x * (x : ℂ) ^ k *
      (x : ℂ) ^ (α : ℂ) * exp (-(x : ℂ))) (volume.restrict (Set.Ioi 0)) := by
  simp_rw [laguerrePolyL_mul_monomial_eq_sum]
  exact integrable_finsetSum _ fun j _ => (laguerrePolyL_weight_moment hα (k + j)).1.const_mul _

/-- The Laguerre moments vanish below the polynomial's degree. -/
theorem integral_laguerrePolyL_mul_monomial {α : ℝ} (hα : -1 < α) (n k : ℕ) :
    (∫ x : ℝ in Set.Ioi 0, laguerrePolyL α n x * (x : ℂ) ^ k *
      (x : ℂ) ^ (α : ℂ) * exp (-(x : ℂ))) =
      Gamma ((α : ℂ) + k + 1) * poch (-(k : ℂ)) n / n.factorial := by
  have hc : ∀ j : ℕ, (α : ℂ) + 1 ≠ -j := not_neg_nat_of_re_pos (by
    simp only [add_re, ofReal_re, one_re]; linarith)
  have hs : ∀ j : ℕ, (α : ℂ) + k + 1 ≠ -j := not_neg_nat_of_re_pos (by
    simp only [add_re, ofReal_re, natCast_re, one_re]
    have := Nat.cast_nonneg (α := ℝ) k
    linarith)
  simp_rw [laguerrePolyL_mul_monomial_eq_sum]
  rw [integral_finsetSum _ (fun j _ => (laguerrePolyL_weight_moment hα (k + j)).1.const_mul _)]
  simp_rw [MeasureTheory.integral_const_mul, (laguerrePolyL_weight_moment hα _).2]
  have hterm (j : ℕ) :
      (poch ((α : ℂ) + 1) n / n.factorial * kummerMCoeff (-(n : ℂ)) (α + 1) j) *
        Gamma ((α : ℂ) + (k + j : ℕ) + 1) =
      (poch ((α : ℂ) + 1) n / n.factorial * Gamma ((α : ℂ) + k + 1)) *
        gaussHGCoeff (-(n : ℂ)) ((α : ℂ) + k + 1) (α + 1) j := by
    have hg := Gamma_add_nat_div_Gamma_eq (n := j) ((α : ℂ) + k + 1) hs
    have hgm := (div_eq_iff (Gamma_ne_zero hs)).mp hg
    have harg : (α : ℂ) + (k + j : ℕ) + 1 = ((α : ℂ) + k + 1) + j := by push_cast; ring
    rw [harg, hgm]
    unfold kummerMCoeff gaussHGCoeff
    ring
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  have hv := chu_vandermonde n (b := (α : ℂ) + k + 1) hc
  rw [ordinaryHypergeometric_eq_sum_neg_nat] at hv
  simp only [one_pow, mul_one] at hv
  rw [hv, show (α : ℂ) + 1 - (α + k + 1) = -k by ring]
  field [poch_ne_zero_of_not_neg_nat hc n]

/-- Orthogonality of Laguerre polynomials on `(0,∞)` with weight `x^α e^{-x}`. -/
@[dlmf 18.3.T1]
theorem laguerrePolyL_orthogonal {α : ℝ} {m n : ℕ} (hα : -1 < α) (hmn : m ≠ n) :
    ∫ x : ℝ in Set.Ioi (0 : ℝ),
        laguerrePolyL α m x * laguerrePolyL α n x * (x : ℂ) ^ (α : ℂ) * exp (-(x : ℂ)) = 0 := by
  have hlt (m n : ℕ) (hmn : m < n) :
      (∫ x : ℝ in Set.Ioi 0, laguerrePolyL α m x * laguerrePolyL α n x *
        (x : ℂ) ^ (α : ℂ) * exp (-(x : ℂ))) = 0 := by
    have heq : (fun x : ℝ => laguerrePolyL α m x * laguerrePolyL α n x *
        (x : ℂ) ^ (α : ℂ) * exp (-(x : ℂ))) =
        fun x : ℝ => ∑ k ∈ Finset.range (m + 1),
          (poch ((α : ℂ) + 1) m / m.factorial * kummerMCoeff (-(m : ℂ)) (α + 1) k) *
            (laguerrePolyL α n x * (x : ℂ) ^ k * (x : ℂ) ^ (α : ℂ) * exp (-(x : ℂ))) := by
      funext x
      rw [laguerrePolyL_eq_sum_coeff (α : ℂ) m]
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [heq, integral_finsetSum _ (fun k _ =>
      (integrable_laguerrePolyL_mul_monomial hα n k).const_mul _)]
    apply Finset.sum_eq_zero
    intro k hk
    have hkn : k < n := by have := Finset.mem_range.mp hk; omega
    rw [MeasureTheory.integral_const_mul, integral_laguerrePolyL_mul_monomial hα,
      poch_neg_nat_eq_zero hkn]
    simp
  rcases lt_or_gt_of_ne hmn with h | h
  · exact hlt m n h
  · calc
      _ = ∫ x : ℝ in Set.Ioi 0, laguerrePolyL α n x * laguerrePolyL α m x *
          (x : ℂ) ^ (α : ℂ) * exp (-(x : ℂ)) :=
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
      _ = 0 := hlt n m h

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

/-- The real binomial series, used as a nonnegative majorant for Laguerre's double sum. -/
theorem hasSum_poch_real {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (a : ℝ) :
    HasSum (fun m : ℕ => (ascPochhammer ℝ m).eval a / m.factorial * r ^ m)
      ((1 - r) ^ (-a)) := by
  have hs := hasSum_poch_div_factorial (β := (a : ℂ)) (z := (r : ℂ))
    (by simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0] using hr1)
  have hp : (1 - (r : ℂ)) ^ (-(a : ℂ)) = ((1 - r : ℝ) ^ (-a) : ℝ) := by
    rw [show 1 - (r : ℂ) = ((1 - r : ℝ) : ℂ) by push_cast; rfl,
      ← ofReal_neg, ← ofReal_cpow (by linarith : 0 ≤ 1 - r)]
  rw [hp] at hs
  simpa [poch_ofReal, ← ofReal_pow, ← ofReal_natCast, ← ofReal_div, ← ofReal_mul] using
    Complex.hasSum_re hs

/-- Absolute convergence of the double series obtained from Laguerre's terminating sum. -/
theorem summable_laguerrePolyL_double (α x : ℂ) {t : ℂ} (ht : ‖t‖ < 1) :
    Summable (fun km : ℕ × ℕ =>
      (poch (α + 1 + km.1) km.2 / km.2.factorial * t ^ km.2) *
        ((-x * t) ^ km.1 / km.1.factorial)) := by
  let A : ℝ := ‖α + 1‖
  let r : ℝ := ‖t‖
  let s : ℝ := ‖x‖ * r
  let B : ℕ × ℕ → ℝ := fun km =>
    ((ascPochhammer ℝ km.2).eval (A + km.1) / km.2.factorial * r ^ km.2) *
      (s ^ km.1 / km.1.factorial)
  have hr : 0 < 1 - r := sub_pos.mpr ht
  have hrow (k : ℕ) : HasSum (fun m => B (k, m))
      ((1 - r) ^ (-(A + k)) * (s ^ k / k.factorial)) :=
    (hasSum_poch_real (norm_nonneg t) ht (A + k)).mul_right _
  have hvalue (k : ℕ) : (1 - r) ^ (-(A + k)) * (s ^ k / k.factorial) =
      (1 - r) ^ (-A) * ((s / (1 - r)) ^ k / k.factorial) := by
    rw [show -(A + (k : ℝ)) = -A - k by ring, Real.rpow_sub hr,
      Real.rpow_natCast, div_pow]
    ring
  have hB : Summable B := summable_prod_of_nonneg
    (fun km => mul_nonneg
      (mul_nonneg (div_nonneg (poch_eval_nonneg (by positivity) _) (by positivity))
        (pow_nonneg (norm_nonneg t) _))
      (div_nonneg (pow_nonneg (by dsimp [s, r]; positivity) _) (by positivity))) |>.mpr
    ⟨fun k => (hrow k).summable, by
      have heq : (fun k => ∑' m, B (k, m)) =
          fun k => (1 - r) ^ (-A) * ((s / (1 - r)) ^ k / k.factorial) :=
        funext fun k => (hrow k).tsum_eq.trans (hvalue k)
      rw [heq]
      exact (NormedSpace.expSeries_div_hasSum_exp (s / (1 - r))).summable.mul_left _⟩
  apply Summable.of_norm
  apply hB.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro km
  rcases km with ⟨k, m⟩
  have hp : ‖poch (α + 1 + k) m‖ ≤ (ascPochhammer ℝ m).eval (A + k) :=
    (norm_poch_le _ _).trans (poch_eval_mono (norm_nonneg _) (by
      simpa [A] using norm_add_le (α + 1) (k : ℂ)) m)
  simp only [norm_mul, norm_div, norm_pow, norm_neg, Complex.norm_natCast]
  dsimp [B, s, r]
  gcongr

/-- Generating function
`(1-t)^{-α-1} exp(-xt/(1-t)) = ∑ L_n^{(α)}(x) t^n` (AAR §6.2). -/
@[dlmf 18.12.E13]
theorem laguerrePolyL_generating_function {α x t : ℂ}
    (hα : ∀ k : ℕ, α + 1 ≠ -(k : ℂ)) (ht : ‖t‖ < 1) :
    (1 - t) ^ (-α - 1) * exp (-x * t / (1 - t)) = ∑' n : ℕ, laguerrePolyL α n x * t ^ n := by
  let L : ℕ × ℕ → ℂ := fun km =>
    (poch (α + 1 + km.1) km.2 / km.2.factorial * t ^ km.2) *
      ((-x * t) ^ km.1 / km.1.factorial)
  have hL : Summable L := summable_laguerrePolyL_double α x ht
  have ht0 : 1 - t ≠ 0 := by
    intro h
    rw [← sub_eq_zero.mp h, norm_one] at ht
    exact (lt_irrefl 1) ht
  have hrow (k : ℕ) : HasSum (fun m => L (k, m))
      ((1 - t) ^ (-(α + 1 + k)) * ((-x * t) ^ k / k.factorial)) :=
    (hasSum_poch_div_factorial (β := α + 1 + k) ht).mul_right _
  have hvalue (k : ℕ) : (1 - t) ^ (-(α + 1 + k)) * ((-x * t) ^ k / k.factorial) =
      (1 - t) ^ (-α - 1) * ((-x * t / (1 - t)) ^ k / k.factorial) := by
    rw [show -(α + 1 + (k : ℂ)) = (-α - 1) - k by ring,
      cpow_sub _ _ ht0, cpow_natCast, div_pow]
    ring
  have hsum : ∑' km, L km = (1 - t) ^ (-α - 1) * exp (-x * t / (1 - t)) := by
    rw [hL.tsum_prod]
    calc
      _ = ∑' k : ℕ, (1 - t) ^ (-α - 1) *
          ((-x * t / (1 - t)) ^ k / k.factorial) :=
        tsum_congr fun k => (hrow k).tsum_eq.trans (hvalue k)
      _ = _ := by
        rw [tsum_mul_left]
        congr 1
        simpa only [Complex.exp_eq_exp_ℂ] using
          (NormedSpace.expSeries_div_hasSum_exp (-x * t / (1 - t))).tsum_eq
  have hdiag : ∑' km, L km =
      ∑' n : ℕ, ∑ k ∈ Finset.range (n + 1), L (k, n - k) := by
    have hsig := Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.summable_iff.mpr hL
    simp only [Function.comp_def] at hsig
    rw [← Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq L,
      hsig.tsum_sigma]
    apply tsum_congr
    intro n
    rw [tsum_fintype]
    change (∑ b : ↥(Finset.antidiagonal n), L b.val) = _
    exact (Finset.sum_finset_coe L (Finset.antidiagonal n)).trans
      (Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk L n)
  rw [← hsum, hdiag]
  apply tsum_congr
  intro n
  rw [laguerrePolyL_eq_sum hα, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have htprod : t ^ (n - k) * t ^ k = t ^ n := by
    rw [← pow_add, Nat.sub_add_cancel hk']
  dsimp [L]
  rw [mul_pow]
  calc
    _ = poch (α + 1 + k) (n - k) / ((n - k).factorial * k.factorial : ℂ) *
        (-x) ^ k * (t ^ (n - k) * t ^ k) := by ring
    _ = _ := by rw [htprod]

/-- Hypergeometric realization of Jacobi polynomials, AAR §6.3,
for `α + 1` not a nonpositive integer:
`P_n^{(α,β)}(x) = (α+1)_n / n! · ₂F₁(-n, n+α+β+1; α+1; (1-x)/2)`. -/
@[dlmf 18.5.E7]
def jacobiPolyP (α β : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  poch (α + 1) n / n ! * ₂F₁ (-n : ℂ) (n + α + β + 1) (α + 1) ((1 - x) / 2)

/-- `P_0^{(α,β)}(x) = 1`. -/
@[simp]
theorem jacobiPolyP_zero (α β x : ℂ) : jacobiPolyP α β 0 x = 1 := by
  simp [jacobiPolyP, poch_zero, ordinaryHypergeometric_zero_left]

/-- Legendre polynomials as Jacobi polynomials with `α = β = 0`. -/
@[dlmf 18.7.E9]
def legendrePolyP (n : ℕ) (x : ℂ) : ℂ :=
  jacobiPolyP 0 0 n x

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

/-- Orthogonality of the terminating Gauss polynomials for the shifted Jacobi weight. -/
theorem jacobi_shifted_orthogonal {α β : ℝ} (hα : -1 < α) (hβ : -1 < β)
    {m n : ℕ} (hmn : m < n) :
    (∫ t : ℝ in (0 : ℝ)..1,
      (t : ℂ) ^ (α : ℂ) * (1 - (t : ℂ)) ^ (β : ℂ) *
        ₂F₁ (-(n : ℂ)) (n + α + β + 1) (α + 1) (t : ℂ) *
        ₂F₁ (-(m : ℂ)) (m + α + β + 1) (α + 1) (t : ℂ)) = 0 := by
  let F (k : ℕ) : ℂ → ℂ := ₂F₁ (-(k : ℂ)) (k + α + β + 1) (α + 1)
  let L (k : ℕ) : ℂ := (k : ℂ) * (k + α + β + 1)
  let w : ℝ → ℂ := fun t => (t : ℂ) ^ (α : ℂ) * (1 - (t : ℂ)) ^ (β : ℂ)
  let p : ℝ → ℂ := fun t => (t : ℂ) ^ ((α : ℂ) + 1) *
    (1 - (t : ℂ)) ^ ((β : ℂ) + 1)
  let H : ℝ → ℂ := fun t => p t *
    (deriv (F n) t * F m t - F n t * deriv (F m) t)
  have hα' : 0 < ((α : ℂ) + 1).re := by simp; linarith
  have hβ' : 0 < ((β : ℂ) + 1).re := by simp; linarith
  have hc := not_neg_nat_of_re_pos hα'
  have hF (k : ℕ) (z : ℂ) : AnalyticAt ℂ (F k) z := analyticAt_gauss_neg_nat k _ _ z
  have hFc (k : ℕ) : Continuous (fun t : ℝ => F k t) :=
    (continuous_iff_continuousAt.mpr fun z => (hF k z).continuousAt).comp continuous_ofReal
  have hFdc (k : ℕ) : Continuous (fun t : ℝ => deriv (F k) t) :=
    (continuous_iff_continuousAt.mpr fun z => (hF k z).deriv.continuousAt).comp continuous_ofReal
  have hpcont : ContinuousOn p (Set.Icc 0 1) := by
    intro t ht
    apply ContinuousWithinAt.mul
    · exact ((continuousAt_cpow_const_of_re_pos (Or.inl (by simpa using ht.1)) hα').comp
        continuous_ofReal.continuousAt).continuousWithinAt
    · exact ((continuousAt_cpow_const_of_re_pos (Or.inl (by simp; linarith [ht.2])) hβ').comp
        (show ContinuousAt (fun u : ℝ => 1 - (u : ℂ)) t by fun_prop)).continuousWithinAt
  have hHcont : ContinuousOn H (Set.Icc 0 1) :=
    hpcont.mul (((hFdc n).continuousOn.mul (hFc m).continuousOn).sub
      ((hFc n).continuousOn.mul (hFdc m).continuousOn))
  have hw : IntervalIntegrable w volume 0 1 := by
    simpa only [add_sub_cancel_right] using betaIntegral_convergent hα' hβ'
  have hI : IntervalIntegrable (fun t : ℝ => w t * F n t * F m t) volume 0 1 :=
    (hw.mul_continuousOn (hFc n).continuousOn).mul_continuousOn (hFc m).continuousOn
  have hdH (t : ℝ) (ht : t ∈ Set.Ioo 0 1) :
      HasDerivAt H ((L m - L n) * (w t * F n t * F m t)) t := by
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.1.ne'
    have hspos : 0 < 1 - t := sub_pos.mpr ht.2
    have hs0 : 1 - (t : ℂ) ≠ 0 := by exact_mod_cast hspos.ne'
    have htSlit : (t : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr ht.1
    have hsSlit : 1 - (t : ℂ) ∈ slitPlane := Or.inl (by simp; linarith [ht.2])
    have hp : p t = w t * (t : ℂ) * (1 - (t : ℂ)) := by
      dsimp [p, w]
      rw [cpow_add _ _ ht0, cpow_add _ _ hs0, cpow_one, cpow_one]
      ring
    have hdp : HasDerivAt p
        (w t * ((α : ℂ) + 1 - ((α : ℂ) + β + 2) * t)) t := by
      have hd := ((hasDerivAt_id (t : ℂ)).cpow_const (c := (α : ℂ) + 1) htSlit).mul
        (((hasDerivAt_const (t : ℂ) 1).sub (hasDerivAt_id (t : ℂ))).cpow_const
          (c := (β : ℂ) + 1) hsSlit)
      convert! hd.comp_ofReal using 1
      simp only [id_eq, Pi.sub_apply, zero_sub, mul_one, add_sub_cancel_right]
      rw [cpow_add _ _ hs0, cpow_add _ _ ht0, cpow_one, cpow_one]
      dsimp [w]
      ring
    have hdf (k : ℕ) := (hF k (t : ℂ)).differentiableAt.hasDerivAt.comp_ofReal
    have hddf (k : ℕ) := (hF k (t : ℂ)).deriv.differentiableAt.hasDerivAt.comp_ofReal
    have hd := hdp.mul (((hddf n).mul (hdf m)).sub ((hdf n).mul (hddf m)))
    have ho (k : ℕ) : (t : ℂ) * (1 - t) * deriv (deriv (F k)) t +
        ((α : ℂ) + 1 - ((α : ℂ) + β + 2) * t) * deriv (F k) t + L k * F k t = 0 := by
      have h := ordinaryHypergeometric_ode (a := -(k : ℂ))
        (b := (k : ℂ) + α + β + 1) hc
        (by simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1] using ht.2)
        ht0 (by exact_mod_cast ne_of_lt ht.2)
      simp only [iteratedDeriv_succ, iteratedDeriv_zero] at h
      dsimp [F, L]
      linear_combination h
    convert! hd using 1
    simp only [Pi.sub_apply, Pi.mul_apply]
    rw [hp]
    linear_combination -(w t * F m t) * ho n + (w t * F n t) * ho m
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0 : ℝ) ≤ 1)
    hHcont hdH (hI.const_mul (L m - L n))
  have hα0 : (α : ℂ) + 1 ≠ 0 := by intro h; rw [h] at hα'; simp at hα'
  have hβ0 : (β : ℂ) + 1 ≠ 0 := by intro h; rw [h] at hβ'; simp at hβ'
  simp only [H, p, ofReal_zero, ofReal_one, zero_cpow hα0, zero_mul, sub_self,
    zero_cpow hβ0, mul_zero] at hFTC
  rw [intervalIntegral.integral_const_mul] at hFTC
  have hL : L m - L n ≠ 0 := by
    have hmn' : (m : ℝ) < n := by exact_mod_cast hmn
    have hn : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hpos : 0 < (n : ℝ) + m + α + β + 1 := by linarith
    have hprod : 0 < ((n : ℝ) - m) * (n + m + α + β + 1) := mul_pos (sub_pos.mpr hmn') hpos
    intro h
    have he := congrArg Complex.re h
    simp [L] at he
    nlinarith
  exact (mul_eq_zero.mp (by simpa using hFTC)).resolve_left hL

/-- Orthogonality of Jacobi polynomials on `[-1,1]` with weight `(1-x)^α (1+x)^β`. -/
@[dlmf 18.3.T1]
theorem jacobiPolyP_orthogonal {α β : ℝ} {m n : ℕ}
    (hα : -1 < α) (hβ : -1 < β) (hmn : m ≠ n) :
    ∫ x : ℝ in (-1 : ℝ)..1,
        jacobiPolyP α β m x * jacobiPolyP α β n x *
          (1 - (x : ℂ)) ^ (α : ℂ) * (1 + (x : ℂ)) ^ (β : ℂ) = 0 := by
  have hlt (m n : ℕ) (hmn : m < n) :
      (∫ x : ℝ in (-1 : ℝ)..1, jacobiPolyP α β m x * jacobiPolyP α β n x *
        (1 - (x : ℂ)) ^ (α : ℂ) * (1 + (x : ℂ)) ^ (β : ℂ)) = 0 := by
    let J : ℝ → ℂ := fun x => jacobiPolyP α β m x * jacobiPolyP α β n x *
      (1 - (x : ℂ)) ^ (α : ℂ) * (1 + (x : ℂ)) ^ (β : ℂ)
    let C : ℂ := (poch ((α : ℂ) + 1) m / m.factorial) *
      (poch ((α : ℂ) + 1) n / n.factorial) * (2 : ℂ) ^ (α : ℂ) * (2 : ℂ) ^ (β : ℂ)
    have hi : (∫ t : ℝ in (0 : ℝ)..1, J (-2 * t + 1)) =
        C * ∫ t : ℝ in (0 : ℝ)..1,
          (t : ℂ) ^ (α : ℂ) * (1 - (t : ℂ)) ^ (β : ℂ) *
            ₂F₁ (-(n : ℂ)) (n + α + β + 1) (α + 1) (t : ℂ) *
            ₂F₁ (-(m : ℂ)) (m + α + β + 1) (α + 1) (t : ℂ) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by simpa using ht
      have harg : (1 - ((-2 * t + 1 : ℝ) : ℂ)) / 2 = (t : ℂ) := by push_cast; ring
      have hleft : 1 - ((-2 * t + 1 : ℝ) : ℂ) = (2 : ℂ) * t := by push_cast; ring
      have hright : 1 + ((-2 * t + 1 : ℝ) : ℂ) = (2 : ℂ) * (1 - (t : ℂ)) := by
        push_cast; ring
      have hpowL : ((2 : ℂ) * t) ^ (α : ℂ) = (2 : ℂ) ^ (α : ℂ) * (t : ℂ) ^ (α : ℂ) :=
        mul_cpow_ofReal_nonneg (a := 2) (by norm_num) ht'.1 _
      have hpowR : ((2 : ℂ) * (1 - (t : ℂ))) ^ (β : ℂ) =
          (2 : ℂ) ^ (β : ℂ) * (1 - (t : ℂ)) ^ (β : ℂ) := by
        convert! mul_cpow_ofReal_nonneg (a := 2) (by norm_num)
          (sub_nonneg.mpr ht'.2) (β : ℂ) using 1 <;> push_cast <;> rfl
      dsimp [J, jacobiPolyP, C]
      rw [harg, hleft, hright, hpowL, hpowR]
      ring
    rw [jacobi_shifted_orthogonal hα hβ hmn, mul_zero] at hi
    have hsub := intervalIntegral.smul_integral_comp_mul_add J (a := (0 : ℝ)) (b := 1) (-2) 1
    rw [show (-2 : ℝ) * 0 + 1 = 1 by ring,
      show (-2 : ℝ) * 1 + 1 = -1 by ring,
      intervalIntegral.integral_symm (f := J), hi, smul_zero] at hsub
    exact neg_eq_zero.mp hsub.symm
  rcases lt_or_gt_of_ne hmn with h | h
  · exact hlt m n h
  · calc
      _ = ∫ x : ℝ in (-1 : ℝ)..1, jacobiPolyP α β n x * jacobiPolyP α β m x *
          (1 - (x : ℂ)) ^ (α : ℂ) * (1 + (x : ℂ)) ^ (β : ℂ) :=
        intervalIntegral.integral_congr fun x _ => by ring
      _ = 0 := hlt n m h

/-- Hypergeometric realization of Gegenbauer polynomials, AAR §6.11,
for `λ + 1/2` not a nonpositive integer:
`C_n^{(λ)}(x) = (2λ)_n / n! · ₂F₁(-n, n+2λ; λ+1/2; (1-x)/2)`. -/
@[dlmf 18.5.E9]
def ultrasphPoly (lam : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  poch (2 * lam) n / n ! * ₂F₁ (-n : ℂ) (n + 2 * lam) (lam + 1 / 2) ((1 - x) / 2)

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

/-- Helper lemma for `eval_U_eq_ultrasphPoly`. -/
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

/-- Helper lemma for `eval_U_eq_ultrasphPoly`. Closed form of the coefficients of `C_n^{(1)}`. -/
def gegenbauerB (n k : ℕ) : ℂ :=
  if k ≤ n then
    (-1 : ℂ) ^ k * (4 : ℂ) ^ k * (n + k + 1).factorial /
      ((n - k).factorial * (2 * k + 1).factorial : ℂ)
  else 0

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
      three_halves_not_neg_nat k
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

/-- The Jacobi weight measure on `(-1,1)`. -/
def jacobiMeasure (α β : ℝ) : Measure ℝ :=
  (volume.restrict (Set.Ioo (-1 : ℝ) 1)).withDensity
    (fun x => ENNReal.ofReal ((1 - x) ^ α * (1 + x) ^ β))

end DLMF.OrthogonalPolynomials
