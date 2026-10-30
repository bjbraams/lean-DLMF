/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bessel.RegularizedSeries

/-! # Sonine’s integral and Gamma-weighted integrals of regularized `₀F₁`

Termwise integration is justified by the absolute convergence of a regularized
`₁F₁` series whose first parameter is the real part of the Gamma weight.
Scaling and the substitution `u = t²` then give Sonine’s Bessel integral.
-/

@[expose] public noncomputable section

namespace DLMF.Bessel

open Complex MeasureTheory Set
open scoped Nat
open DLMF.Hypergeometric
open DLMF.Confluent

/-- Integrating regularized `₀F₁` against its Gamma weight gives an exponential. -/
theorem integral_regularized0F1_gamma {c w : ℂ} (hc : 0 < c.re) :
    ∫ t : ℝ in Ioi 0, (Real.exp (-t) : ℂ) * (t : ℂ) ^ (c - 1) *
      regularizedHGFun ∅ {c} (w * t) = exp w := by
  let d := regularizedHGFunCoeff (∅ : Multiset ℂ) {c}
  let F : ℕ → ℝ → ℂ := fun n t =>
    (d n * w ^ n) * ((Real.exp (-t) : ℂ) * (t : ℂ) ^ (c + n - 1))
  have hcn (n : ℕ) : 0 < (c + n).re := by simp; positivity
  have hFi (n : ℕ) : IntegrableOn (F n) (Ioi 0) :=
    (GammaIntegral_convergent (hcn n)).const_mul _
  have hnorm (n : ℕ) : (∫ t : ℝ in Ioi 0, ‖F n t‖) =
      ‖d n * w ^ n‖ * Real.Gamma (c.re + n) := by
    rw [Real.Gamma_eq_integral (by positivity : 0 < c.re + n), ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    simp only [F, norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le,
      norm_cpow_eq_rpow_re_of_pos ht, sub_re, add_re, natCast_re, one_re]
  have hcoeff (n : ℕ) : Gamma (c.re : ℂ) * regularizedHGFunCoeff {(c.re : ℂ)} {c} n =
      Gamma ((c.re : ℂ) + n) * d n := by
    dsimp only [d]
    have hp : poch (c.re : ℂ) n = Gamma ((c.re : ℂ) + n) / Gamma (c.re : ℂ) :=
      (Gamma_add_nat_div_Gamma_eq (n := n) (c.re : ℂ)
        (not_neg_nat_of_re_pos (by simpa using hc))).symm
    rw [regularizedHGFunCoeff_singleton, regularizedHGFunCoeff_empty, hp]
    field_simp [Gamma_ne_zero_of_re_pos (show 0 < (c.re : ℂ).re by simpa using hc)]
  have hnorm' (n : ℕ) : (∫ t : ℝ in Ioi 0, ‖F n t‖) =
      Real.Gamma c.re *
        ‖regularizedHGFunCoeff {(c.re : ℂ)} {c} n * (‖w‖ : ℂ) ^ n‖ := by
    rw [hnorm]
    have he := congrArg norm (hcoeff n)
    simp only [norm_mul, Gamma_ofReal, Complex.norm_of_nonneg (Real.Gamma_pos_of_pos hc).le] at he
    rw [show (c.re : ℂ) + n = ((c.re + n : ℝ) : ℂ) by push_cast; rfl,
      Gamma_ofReal, Complex.norm_of_nonneg (Real.Gamma_pos_of_pos (by positivity)).le] at he
    simp only [norm_mul, norm_pow, norm_real, Real.norm_eq_abs, abs_norm]
    linear_combination -(‖w‖ ^ n) * he
  have hr : (regularizedHGFunSeries {(c.re : ℂ)} {c}).radius = ⊤ :=
    radius_regularizedHGFunSeries_eq_top (by simp)
  have hseries : HasFPowerSeriesOnBall (regularizedHGFun {(c.re : ℂ)} {c})
      (regularizedHGFunSeries {(c.re : ℂ)} {c}) 0 ⊤ := by
    change HasFPowerSeriesOnBall (regularizedHGFunSeries {(c.re : ℂ)} {c}).sum
      (regularizedHGFunSeries {(c.re : ℂ)} {c}) 0 ⊤
    simpa only [hr] using (regularizedHGFunSeries {(c.re : ℂ)} {c}).hasFPowerSeriesOnBall
      (by rw [hr]; simp)
  have hsum : Summable (fun n => ∫ t : ℝ in Ioi 0, ‖F n t‖) := by
    simp_rw [hnorm']
    exact (hseries.hasSum_mul_pow (z := (‖w‖ : ℂ)) (by simp)).summable.norm.mul_left _
  have hterm (n : ℕ) : (∫ t : ℝ in Ioi 0, F n t) = w ^ n / n ! := by
    rw [show F n = fun t => (d n * w ^ n) *
      ((Real.exp (-t) : ℂ) * (t : ℂ) ^ (c + n - 1)) from rfl,
      integral_const_mul, ← GammaIntegral, ← Gamma_eq_integral (hcn n)]
    dsimp only [d]
    rw [regularizedHGFunCoeff_empty]
    field_simp [Gamma_ne_zero_of_re_pos (hcn n)]
  have hpoint (t : ℝ) (ht : 0 < t) : (∑' n, F n t) =
      (Real.exp (-t) : ℂ) * (t : ℂ) ^ (c - 1) * regularizedHGFun ∅ {c} (w * t) := by
    have hs := ((hasFPowerSeriesOnBall_regularized0F1 c).hasSum_mul_pow
      (z := w * t) (by simp)).mul_left ((Real.exp (-t) : ℂ) * (t : ℂ) ^ (c - 1))
    convert hs.tsum_eq using 1
    apply tsum_congr
    intro n
    dsimp only [F, d]
    rw [show c + n - 1 = (c - 1) + n by ring,
      cpow_add _ _ (ofReal_ne_zero.mpr ht.ne'), cpow_natCast, mul_pow]
    ring
  have hi := hasSum_integral_of_summable_integral_norm hFi hsum
  simp_rw [hterm] at hi
  have he : HasSum (fun n : ℕ => w ^ n / n !) (exp w) := by
    simpa only [exp_eq_exp_ℂ] using NormedSpace.expSeries_div_hasSum_exp w
  rw [← hi.unique he]
  exact setIntegral_congr_fun measurableSet_Ioi (fun t ht => (hpoint t ht).symm)

/-- The scaled Gamma-weighted integral of regularized `₀F₁`. -/
theorem integral_regularized0F1_gamma_scaled {c w : ℂ} {b : ℝ}
    (hc : 0 < c.re) (hb : 0 < b) :
    ∫ t : ℝ in Ioi 0, (Real.exp (-(b * t)) : ℂ) * (t : ℂ) ^ (c - 1) *
      regularizedHGFun ∅ {c} (w * t) = (1 / b : ℂ) ^ c * exp (w / b) := by
  let g : ℝ → ℂ := fun t => (Real.exp (-t) : ℂ) * (t : ℂ) ^ (c - 1) *
    regularizedHGFun ∅ {c} ((w / b) * t)
  have hb0 : (b : ℂ) ≠ 0 := ofReal_ne_zero.mpr hb.ne'
  have hp : (1 / b : ℂ) ^ (c - 1) * (b : ℂ) ^ (c - 1) = 1 := by
    rw [← ofReal_one, ← ofReal_div, ← mul_cpow_ofReal_nonneg (by positivity) hb.le,
      ← ofReal_mul, one_div_mul_cancel hb.ne', ofReal_one, one_cpow]
  calc
    _ = ∫ t : ℝ in Ioi 0, (1 / b : ℂ) ^ (c - 1) * g (b * t) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp [g]
      rw [ofReal_mul, mul_cpow_ofReal_nonneg hb.le ht.le,
        show w / (b : ℂ) * ((b : ℂ) * t) = w * t by field_simp]
      linear_combination -(Real.exp (-(b * t)) : ℂ) * (t : ℂ) ^ (c - 1) *
        regularizedHGFun ∅ {c} (w * t) * hp
    _ = (1 / b : ℂ) ^ (c - 1) * ((b : ℂ)⁻¹ * ∫ t : ℝ in Ioi 0, g t) := by
      rw [integral_const_mul, integral_comp_mul_left_Ioi g 0 hb, mul_zero,
        real_smul, ofReal_inv]
    _ = (1 / b : ℂ) ^ c * exp (w / b) := by
      rw [show (∫ t : ℝ in Ioi 0, g t) = exp (w / b) from integral_regularized0F1_gamma hc]
      have hpow : (1 / b : ℂ) ^ (c - 1) * (b : ℂ)⁻¹ = (1 / b : ℂ) ^ c := by
        calc
          _ = (1 / b : ℂ) ^ (c - 1) * (1 / b : ℂ) ^ (1 : ℂ) := by rw [cpow_one, one_div]
          _ = _ := by rw [← cpow_add _ _ (one_div_ne_zero hb0), sub_add_cancel]
      rw [← mul_assoc, hpow]

/-- Sonine's integral `∫_0^∞ J_ν(at) e^{-p² t²} t^{ν+1} dt` (AAR §4.11). -/
@[dlmf 10.22.E51]
theorem sonine_integral {ν : ℂ} {a p : ℝ} (hν : -1 < ν.re) (ha : 0 < a) (hp : 0 < p) :
    ∫ t : ℝ in Set.Ioi (0 : ℝ),
        besselJ ν (a * t) * exp (-(p : ℂ) ^ 2 * (t : ℂ) ^ 2) * (t : ℂ) ^ (ν + 1) =
      (a / (2 * p ^ 2)) ^ ν * exp (-(a : ℂ) ^ 2 / (4 * p ^ 2)) / (2 * p ^ 2) := by
  let g : ℝ → ℂ := fun u => (Real.exp (-(p ^ 2 * u)) : ℂ) * (u : ℂ) ^ ν *
    regularizedHGFun ∅ {ν + 1} ((-(a : ℂ) ^ 2 / 4) * u)
  have hp0 : (p : ℂ) ≠ 0 := ofReal_ne_zero.mpr hp.ne'
  have hi : (∫ u : ℝ in Ioi 0, g u) =
      (1 / (p : ℂ) ^ 2) ^ (ν + 1) * exp (-(a : ℂ) ^ 2 / (4 * p ^ 2)) := by
    have he := integral_regularized0F1_gamma_scaled (c := ν + 1)
      (w := -(a : ℂ) ^ 2 / 4) (b := p ^ 2) (by simp; linarith) (sq_pos_of_pos hp)
    simpa only [add_sub_cancel_right, ofReal_pow, div_div, g] using he
  have hs := integral_comp_rpow_Ioi_of_pos (g := g) (p := 2) (by norm_num)
  norm_num only [Real.rpow_two, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one] at hs
  have hpoint (t : ℝ) (ht : 0 < t) :
      besselJ ν (a * t) * exp (-(p : ℂ) ^ 2 * (t : ℂ) ^ 2) * (t : ℂ) ^ (ν + 1) =
        (a / 2 : ℂ) ^ ν / 2 * ((2 * t : ℝ) • g (t ^ 2)) := by
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
    have hbase : ((a : ℂ) * t / 2) ^ ν = (a / 2 : ℂ) ^ ν * (t : ℂ) ^ ν := by
      rw [show (a : ℂ) * t / 2 = ((a / 2 : ℝ) : ℂ) * (t : ℂ) by push_cast; ring,
        mul_cpow_ofReal_nonneg (by positivity) ht.le, ofReal_div, ofReal_ofNat]
    have hsquare : ((t : ℂ) ^ 2) ^ ν = (t : ℂ) ^ ν * (t : ℂ) ^ ν := by
      have he := cpow_mul_ofReal_nonneg ht.le 2 ν
      norm_num only [Real.rpow_two, ofReal_ofNat, ofReal_pow] at he
      rw [← he, show (2 : ℂ) * ν = ν + ν by ring, cpow_add _ _ ht0]
    have he : exp (-(p : ℂ) ^ 2 * (t : ℂ) ^ 2) = (Real.exp (-(p ^ 2 * t ^ 2)) : ℂ) := by
      rw [ofReal_exp]
      congr 1
      push_cast
      ring
    dsimp [g]
    rw [besselJ_eq_regularized, hbase, he, cpow_add _ _ ht0, cpow_one,
      ofReal_mul, ofReal_ofNat, ofReal_pow, hsquare,
      show -(((a : ℂ) * t) ^ 2 / 4) = (-(a : ℂ) ^ 2 / 4) * (t : ℂ) ^ 2 by ring]
    simp only [Multiset.empty_eq_zero]
    ring
  calc
    _ = (a / 2 : ℂ) ^ ν / 2 * ∫ t : ℝ in Ioi 0, (2 * t : ℝ) • g (t ^ 2) := by
      rw [← integral_const_mul]
      exact setIntegral_congr_fun measurableSet_Ioi (fun t ht => hpoint t ht)
    _ = (a / 2 : ℂ) ^ ν / 2 *
        ((1 / (p : ℂ) ^ 2) ^ (ν + 1) * exp (-(a : ℂ) ^ 2 / (4 * p ^ 2))) := by rw [hs, hi]
    _ = _ := by
      have hpow : (a / 2 : ℂ) ^ ν * (1 / (p : ℂ) ^ 2) ^ ν =
          (a / (2 * p ^ 2) : ℂ) ^ ν := by
        rw [← ofReal_ofNat (n := 2), ← ofReal_div, ← ofReal_pow, ← ofReal_one,
          ← ofReal_div, ← mul_cpow_ofReal_nonneg (by positivity) (by positivity)]
        congr 1
        push_cast
        ring
      rw [cpow_add _ _ (one_div_ne_zero (pow_ne_zero _ hp0)), cpow_one]
      linear_combination (norm := ring_nf)
        exp (-(a : ℂ) ^ 2 / (4 * p ^ 2)) / (2 * (p : ℂ) ^ 2) * hpow

end DLMF.Bessel
