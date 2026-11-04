/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Basic.Classical
public import DLMF.OrthogonalPolynomials.Basic.Definitions

public import DLMF.Confluent.KummerProperties
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
Legendre polynomials `shiftedLegendre`. This file develops the physicists' Hermite, Laguerre,
Jacobi and Gegenbauer (ultraspherical) families, defined in
`DLMF.OrthogonalPolynomials.Basic.Definitions`, with their standard hypergeometric
representations (AAR §§6.1–6.4, 6.10–6.11).

## Main results

* `deriv_gaussian_eq_hermitePolynomialH`: the Rodrigues formula for `H_n`.
* `hermitePolynomialH_generating_function`, `laguerrePolynomialL_generating_function`: the
  generating functions DLMF 18.12.15 and 18.12.13.
* `laguerrePolynomialL_orthogonal`, `jacobiPolynomialP_orthogonal`: orthogonality of the Laguerre
  and Jacobi polynomials (DLMF Table 18.3.1).
* `jacobi_shifted_orthogonal`: orthogonality of the terminating Gauss polynomials.

## Implementation notes

Initial values, explicit sums, endpoint values and the bridges to Mathlib's Hermite, shifted
Legendre and Chebyshev polynomials are in `DLMF.OrthogonalPolynomials.Basic.Classical`.
-/

@[expose] public section

open Complex Polynomial MeasureTheory intervalIntegral
open scoped Real Nat
open DLMF.Hypergeometric
open DLMF.Confluent

noncomputable section

namespace DLMF.OrthogonalPolynomials

/-- Rodrigues formula for physicists' Hermite polynomials, AAR §6.1. -/
@[dlmf 18.5.T1]
theorem deriv_gaussian_eq_hermitePolynomialH (n : ℕ) (x : ℝ) :
    deriv^[n] (fun y => Real.exp (-(y ^ 2))) x =
      (-1 : ℝ) ^ n * aeval x (hermitePolynomialH n) * Real.exp (-(x ^ 2)) := by
  -- A direct adaptation of Mathlib's
  -- `Polynomial.deriv_gaussian_eq_hermite_mul_gaussian` to the physicists' normalization.
  rw [mul_assoc]
  induction n generalizing x with
  | zero => simp [hermitePolynomialH_zero]
  | succ n ih =>
    replace ih : deriv^[n] _ = _ := funext ih
    have hgaussian : deriv (fun y : ℝ => Real.exp (-(y ^ 2))) x =
        -(2 * x) * Real.exp (-(x ^ 2)) := by
      rw [deriv_exp (by fun_prop)]
      simp
      ring
    rw [Function.iterate_succ_apply', ih, deriv_const_mul_field, deriv_fun_mul,
      pow_succ, hgaussian, hermitePolynomialH_succ, map_sub, map_mul, map_mul, map_ofNat,
      aeval_X, Polynomial.deriv_aeval]
    · ring_nf
    · apply Polynomial.differentiable_aeval
    · fun_prop

/-- Complex Rodrigues formula for physicists' Hermite polynomials. Helper lemma for
`hermitePolynomialH_generating_function`. -/
theorem iteratedDeriv_cexp_neg_sq (n : ℕ) (x : ℂ) :
    iteratedDeriv n (fun y : ℂ => exp (-(y ^ 2))) x =
      (-1 : ℂ) ^ n * (aeval x (hermitePolynomialH n) : ℂ) * exp (-(x ^ 2)) := by
  rw [iteratedDeriv_eq_iterate, mul_assoc]
  induction n generalizing x with
  | zero => simp [hermitePolynomialH_zero]
  | succ n ih =>
    replace ih : deriv^[n] _ = _ := funext ih
    have hgaussian : deriv (fun y : ℂ => exp (-(y ^ 2))) x =
        -(2 * x) * exp (-(x ^ 2)) := by
      rw [deriv_cexp (by fun_prop)]
      simp [pow_two]
      ring
    rw [Function.iterate_succ_apply', ih, deriv_const_mul_field, deriv_fun_mul,
      pow_succ, hgaussian, hermitePolynomialH_succ, map_sub, map_mul, map_mul, map_ofNat,
      aeval_X, Polynomial.deriv_aeval]
    · ring_nf
    · apply Polynomial.differentiable_aeval
    · fun_prop

/-- Generating function `∑ H_n(x) t^n / n! = exp(2xt - t²)` (AAR §6.1). -/
theorem hasSum_hermitePolynomialH_generating_function (x t : ℂ) :
    HasSum (fun n : ℕ => (aeval x (hermitePolynomialH n) : ℂ) * t ^ n / n !)
      (exp (2 * x * t - t ^ 2)) := by
  have hf : Differentiable ℂ (fun y : ℂ => exp (-(y ^ 2))) := by fun_prop
  have hne : exp (-(x ^ 2)) ≠ 0 := exp_ne_zero _
  have hs := Complex.hasSum_taylorSeries_of_entire (E := ℂ) hf x (x - t)
  have hterm : (fun n : ℕ =>
      (n ! : ℂ)⁻¹ • ((x - t) - x) ^ n •
        iteratedDeriv n (fun y : ℂ => exp (-(y ^ 2))) x) =
      fun n => (aeval x (hermitePolynomialH n) : ℂ) * t ^ n / n ! * exp (-(x ^ 2)) := by
    funext n
    simp only [sub_sub_cancel_left, smul_eq_mul]
    rw [iteratedDeriv_cexp_neg_sq, neg_pow]
    ring_nf
    rw [mul_comm n 2, pow_mul, neg_one_sq, one_pow]
    ring
  rw [hterm] at hs
  have hs' := hs.mul_right (exp (-(x ^ 2)))⁻¹
  have hsimp : (fun n : ℕ =>
      (aeval x (hermitePolynomialH n) : ℂ) * t ^ n / n ! * exp (-(x ^ 2)) *
        (exp (-(x ^ 2)))⁻¹) =
      fun n => (aeval x (hermitePolynomialH n) : ℂ) * t ^ n / n ! := by
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
theorem hermitePolynomialH_generating_function (x t : ℂ) :
    ∑' n : ℕ, (aeval x (hermitePolynomialH n) : ℂ) * t ^ n / n ! =
      exp (2 * x * t - t ^ 2) :=
  (hasSum_hermitePolynomialH_generating_function x t).tsum_eq

/-- Moments of the Laguerre weight are Gamma values; integrability is recorded as well. -/
theorem laguerrePolynomialL_weight_moment {α : ℝ} (hα : -1 < α) (k : ℕ) :
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
theorem laguerrePolynomialL_mul_monomial_eq_sum (α : ℂ) (n k : ℕ) (x : ℝ) :
    laguerrePolynomialL α n x * (x : ℂ) ^ k * (x : ℂ) ^ α * exp (-(x : ℂ)) =
      ∑ j ∈ Finset.range (n + 1),
        (pochhammer (α + 1) n / n.factorial * kummerMCoeff (-(n : ℂ)) (α + 1) j) *
          ((x : ℂ) ^ (k + j) * (x : ℂ) ^ α * exp (-(x : ℂ))) := by
  rw [laguerrePolynomialL_eq_sum_coeff]
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_add]
  ring

/-- For `α > -1`, `L_n^{(α)}(x) xᵏ x^α e^{-x}` is integrable on `(0, ∞)`. -/
theorem integrable_laguerrePolynomialL_mul_monomial {α : ℝ} (hα : -1 < α) (n k : ℕ) :
    Integrable (fun x : ℝ => laguerrePolynomialL α n x * (x : ℂ) ^ k *
      (x : ℂ) ^ (α : ℂ) * exp (-(x : ℂ))) (volume.restrict (Set.Ioi 0)) := by
  simp_rw [laguerrePolynomialL_mul_monomial_eq_sum]
  exact integrable_finsetSum _ fun j _ =>
      (laguerrePolynomialL_weight_moment hα (k + j)).1.const_mul _

/-- The Laguerre moments vanish below the polynomial's degree. -/
theorem integral_laguerrePolynomialL_mul_monomial {α : ℝ} (hα : -1 < α) (n k : ℕ) :
    (∫ x : ℝ in Set.Ioi 0, laguerrePolynomialL α n x * (x : ℂ) ^ k *
      (x : ℂ) ^ (α : ℂ) * exp (-(x : ℂ))) =
      Gamma ((α : ℂ) + k + 1) * pochhammer (-(k : ℂ)) n / n.factorial := by
  have hc : ∀ j : ℕ, (α : ℂ) + 1 ≠ -j := not_neg_nat_of_re_pos (by
    simp only [add_re, ofReal_re, one_re]; linarith)
  have hs : ∀ j : ℕ, (α : ℂ) + k + 1 ≠ -j := not_neg_nat_of_re_pos (by
    simp only [add_re, ofReal_re, natCast_re, one_re]
    have := Nat.cast_nonneg (α := ℝ) k
    linarith)
  simp_rw [laguerrePolynomialL_mul_monomial_eq_sum]
  rw [integral_finsetSum _
      (fun j _ => (laguerrePolynomialL_weight_moment hα (k + j)).1.const_mul _)]
  simp_rw [MeasureTheory.integral_const_mul, (laguerrePolynomialL_weight_moment hα _).2]
  have hterm (j : ℕ) :
      (pochhammer ((α : ℂ) + 1) n / n.factorial * kummerMCoeff (-(n : ℂ)) (α + 1) j) *
        Gamma ((α : ℂ) + (k + j : ℕ) + 1) =
      (pochhammer ((α : ℂ) + 1) n / n.factorial * Gamma ((α : ℂ) + k + 1)) *
        gaussHypergeometricCoeff (-(n : ℂ)) ((α : ℂ) + k + 1) (α + 1) j := by
    have hg := Gamma_add_nat_div_Gamma_eq (n := j) ((α : ℂ) + k + 1) hs
    have hgm := (div_eq_iff (Gamma_ne_zero hs)).mp hg
    have harg : (α : ℂ) + (k + j : ℕ) + 1 = ((α : ℂ) + k + 1) + j := by push_cast; ring
    rw [harg, hgm]
    unfold kummerMCoeff gaussHypergeometricCoeff
    ring
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  have hv := chu_vandermonde n (b := (α : ℂ) + k + 1) hc
  rw [ordinaryHypergeometric_eq_sum_neg_nat] at hv
  simp only [one_pow, mul_one] at hv
  rw [hv, show (α : ℂ) + 1 - (α + k + 1) = -k by ring]
  field [pochhammer_ne_zero_of_not_neg_nat hc n]

/-- Orthogonality of Laguerre polynomials on `(0,∞)` with weight `x^α e^{-x}`. -/
@[dlmf 18.3.T1]
theorem laguerrePolynomialL_orthogonal {α : ℝ} {m n : ℕ} (hα : -1 < α) (hmn : m ≠ n) :
    ∫ x : ℝ in Set.Ioi (0 : ℝ),
        laguerrePolynomialL α m x * laguerrePolynomialL α n x * (x : ℂ) ^ (α : ℂ) *
            exp (-(x : ℂ)) = 0 := by
  have hlt (m n : ℕ) (hmn : m < n) :
      (∫ x : ℝ in Set.Ioi 0, laguerrePolynomialL α m x * laguerrePolynomialL α n x *
        (x : ℂ) ^ (α : ℂ) * exp (-(x : ℂ))) = 0 := by
    have heq : (fun x : ℝ => laguerrePolynomialL α m x * laguerrePolynomialL α n x *
        (x : ℂ) ^ (α : ℂ) * exp (-(x : ℂ))) =
        fun x : ℝ => ∑ k ∈ Finset.range (m + 1),
          (pochhammer ((α : ℂ) + 1) m / m.factorial * kummerMCoeff (-(m : ℂ)) (α + 1) k) *
            (laguerrePolynomialL α n x * (x : ℂ) ^ k * (x : ℂ) ^ (α : ℂ) * exp (-(x : ℂ))) := by
      funext x
      rw [laguerrePolynomialL_eq_sum_coeff (α : ℂ) m]
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [heq, integral_finsetSum _ (fun k _ =>
      (integrable_laguerrePolynomialL_mul_monomial hα n k).const_mul _)]
    apply Finset.sum_eq_zero
    intro k hk
    have hkn : k < n := by have := Finset.mem_range.mp hk; omega
    rw [MeasureTheory.integral_const_mul, integral_laguerrePolynomialL_mul_monomial hα,
      pochhammer_neg_nat_eq_zero hkn]
    simp
  rcases lt_or_gt_of_ne hmn with h | h
  · exact hlt m n h
  · calc
      _ = ∫ x : ℝ in Set.Ioi 0, laguerrePolynomialL α n x * laguerrePolynomialL α m x *
          (x : ℂ) ^ (α : ℂ) * exp (-(x : ℂ)) :=
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
      _ = 0 := hlt n m h

/-- The real binomial series, used as a nonnegative majorant for Laguerre's double sum. -/
theorem hasSum_pochhammer_real {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (a : ℝ) :
    HasSum (fun m : ℕ => (ascPochhammer ℝ m).eval a / m.factorial * r ^ m)
      ((1 - r) ^ (-a)) := by
  have hs := hasSum_pochhammer_div_factorial (β := (a : ℂ)) (z := (r : ℂ))
    (by simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0] using hr1)
  have hp : (1 - (r : ℂ)) ^ (-(a : ℂ)) = ((1 - r : ℝ) ^ (-a) : ℝ) := by
    rw [show 1 - (r : ℂ) = ((1 - r : ℝ) : ℂ) by push_cast; rfl,
      ← ofReal_neg, ← ofReal_cpow (by linarith : 0 ≤ 1 - r)]
  rw [hp] at hs
  simpa [pochhammer_ofReal, ← ofReal_pow, ← ofReal_natCast, ← ofReal_div, ← ofReal_mul] using
    Complex.hasSum_re hs

/-- Absolute convergence of the double series obtained from Laguerre's terminating sum. -/
theorem summable_laguerrePolynomialL_double (α x : ℂ) {t : ℂ} (ht : ‖t‖ < 1) :
    Summable (fun km : ℕ × ℕ =>
      (pochhammer (α + 1 + km.1) km.2 / km.2.factorial * t ^ km.2) *
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
    (hasSum_pochhammer_real (norm_nonneg t) ht (A + k)).mul_right _
  have hvalue (k : ℕ) : (1 - r) ^ (-(A + k)) * (s ^ k / k.factorial) =
      (1 - r) ^ (-A) * ((s / (1 - r)) ^ k / k.factorial) := by
    rw [show -(A + (k : ℝ)) = -A - k by ring, Real.rpow_sub hr,
      Real.rpow_natCast, div_pow]
    ring
  have hB : Summable B := summable_prod_of_nonneg
    (fun km => mul_nonneg
      (mul_nonneg (div_nonneg (pochhammer_eval_nonneg (by positivity) _) (by positivity))
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
  have hp : ‖pochhammer (α + 1 + k) m‖ ≤ (ascPochhammer ℝ m).eval (A + k) :=
    (norm_pochhammer_le _ _).trans (pochhammer_eval_mono (norm_nonneg _) (by
      simpa [A] using norm_add_le (α + 1) (k : ℂ)) m)
  simp only [norm_mul, norm_div, norm_pow, norm_neg, Complex.norm_natCast]
  dsimp [B, s, r]
  gcongr

/-- Generating function
`(1-t)^{-α-1} exp(-xt/(1-t)) = ∑ L_n^{(α)}(x) t^n` (AAR §6.2). -/
@[dlmf 18.12.E13]
theorem laguerrePolynomialL_generating_function {α x t : ℂ}
    (hα : ∀ k : ℕ, α + 1 ≠ -(k : ℂ)) (ht : ‖t‖ < 1) :
    (1 - t) ^ (-α - 1) * exp (-x * t / (1 - t)) = ∑' n : ℕ, laguerrePolynomialL α n x * t ^ n := by
  let L : ℕ × ℕ → ℂ := fun km =>
    (pochhammer (α + 1 + km.1) km.2 / km.2.factorial * t ^ km.2) *
      ((-x * t) ^ km.1 / km.1.factorial)
  have hL : Summable L := summable_laguerrePolynomialL_double α x ht
  have ht0 : 1 - t ≠ 0 := by
    intro h
    rw [← sub_eq_zero.mp h, norm_one] at ht
    exact (lt_irrefl 1) ht
  have hrow (k : ℕ) : HasSum (fun m => L (k, m))
      ((1 - t) ^ (-(α + 1 + k)) * ((-x * t) ^ k / k.factorial)) :=
    (hasSum_pochhammer_div_factorial (β := α + 1 + k) ht).mul_right _
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
  rw [laguerrePolynomialL_eq_sum hα, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have htprod : t ^ (n - k) * t ^ k = t ^ n := by
    rw [← pow_add, Nat.sub_add_cancel hk']
  dsimp [L]
  rw [mul_pow]
  calc
    _ = pochhammer (α + 1 + k) (n - k) / ((n - k).factorial * k.factorial : ℂ) *
        (-x) ^ k * (t ^ (n - k) * t ^ k) := by ring
    _ = _ := by rw [htprod]

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
      have h := ordinaryHypergeometric_ode (a := -(k : ℂ)) (z := (t : ℂ))
        (b := (k : ℂ) + α + β + 1) hc
        (by simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1] using ht.2)
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
theorem jacobiPolynomialP_orthogonal {α β : ℝ} {m n : ℕ}
    (hα : -1 < α) (hβ : -1 < β) (hmn : m ≠ n) :
    ∫ x : ℝ in (-1 : ℝ)..1,
        jacobiPolynomialP α β m x * jacobiPolynomialP α β n x *
          (1 - (x : ℂ)) ^ (α : ℂ) * (1 + (x : ℂ)) ^ (β : ℂ) = 0 := by
  have hlt (m n : ℕ) (hmn : m < n) :
      (∫ x : ℝ in (-1 : ℝ)..1, jacobiPolynomialP α β m x * jacobiPolynomialP α β n x *
        (1 - (x : ℂ)) ^ (α : ℂ) * (1 + (x : ℂ)) ^ (β : ℂ)) = 0 := by
    let J : ℝ → ℂ := fun x => jacobiPolynomialP α β m x * jacobiPolynomialP α β n x *
      (1 - (x : ℂ)) ^ (α : ℂ) * (1 + (x : ℂ)) ^ (β : ℂ)
    let C : ℂ := (pochhammer ((α : ℂ) + 1) m / m.factorial) *
      (pochhammer ((α : ℂ) + 1) n / n.factorial) * (2 : ℂ) ^ (α : ℂ) * (2 : ℂ) ^ (β : ℂ)
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
      dsimp [J, jacobiPolynomialP, C]
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
      _ = ∫ x : ℝ in (-1 : ℝ)..1, jacobiPolynomialP α β n x * jacobiPolynomialP α β m x *
          (1 - (x : ℂ)) ^ (α : ℂ) * (1 + (x : ℂ)) ^ (β : ℂ) :=
        intervalIntegral.integral_congr fun x _ => by ring
      _ = 0 := hlt n m h

end DLMF.OrthogonalPolynomials
