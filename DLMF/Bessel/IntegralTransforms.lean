/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.Integrals

/-!
# Gaussian and Laplace integrals of Bessel functions

Beals–Wong (9.8.3), with complex order, power, and Gaussian scale of positive real part.
The complex Gamma integral and absolute summation of Kummer's series extend the
Gamma-weighted regularized `₀F₁` argument of `DLMF.Confluent.IntegralRepresentations`.
The substitution `u = t²` gives the Bessel formula. Keeping Kummer's function
regularized also retains exceptional orders.
The Laplace transform reuses the existing full-half-plane Kummer Laplace theorem and
uses the continued Gauss function, even when the argument leaves the series disk.
`DLMF.Bessel.LaplaceTransform` supplies the conventional quadratic Gauss form
without the Kummer representation's order exclusions.
-/

@[expose] public noncomputable section

open Complex MeasureTheory Set
open scoped Nat
open DLMF.Confluent
open DLMF.Hypergeometric

namespace DLMF.Bessel

/-- The Gamma-weighted `₀F₁` integral with complex scale of positive real part.
The proof uses the existing complex Gamma integral and absolute summation of Kummer's series. -/
private lemma integral_exp_cpow_regularized0F1_complex_scaled {a c w b : ℂ}
    (ha : 0 < a.re) (hb : 0 < b.re) :
    (∫ t : ℝ in Ioi 0, exp (-b * t) * (t : ℂ) ^ (a - 1) *
      regularizedHGFun ∅ {c} (w * t)) =
      b ^ (-a) * Gamma a * regularizedHGFun {a} {c} (w / b) := by
  let d := regularizedHGFunCoeff (∅ : Multiset ℂ) {c}
  let F : ℕ → ℝ → ℂ := fun n t =>
    (d n * w ^ n) * ((t : ℂ) ^ (a + n - 1) * exp (-(b * t)))
  let r : ℝ := b.re⁻¹
  have hr : 0 < r := inv_pos.mpr hb
  have hb0 : b ≠ 0 := by intro h; simp [h] at hb
  have han (n : ℕ) : 0 < (a + n).re := by simp; positivity
  have hFi (n : ℕ) : IntegrableOn (F n) (Ioi 0) :=
    (DLMF.Gamma.vb_integrableOn_cpow_exp (han n) hb).const_mul _
  have hnorm (n : ℕ) : (∫ t : ℝ in Ioi 0, ‖F n t‖) =
      ‖d n * w ^ n‖ * (r ^ (a.re + n) * Real.Gamma (a.re + n)) := by
    rw [show r = 1 / b.re by simp [r],
      ← Real.integral_rpow_mul_exp_neg_mul_Ioi (by positivity : 0 < a.re + n) hb,
      ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    simp only [F, norm_mul, norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_exp]
    simp
  have hcoeff (n : ℕ) : Gamma (a.re : ℂ) * regularizedHGFunCoeff {(a.re : ℂ)} {c} n =
      Gamma ((a.re : ℂ) + n) * d n := by
    dsimp only [d]
    have hp : poch (a.re : ℂ) n = Gamma ((a.re : ℂ) + n) / Gamma (a.re : ℂ) :=
      (Gamma_add_nat_div_Gamma_eq (n := n) (a.re : ℂ)
        (not_neg_nat_of_re_pos (by simpa using ha))).symm
    rw [regularizedHGFunCoeff_singleton, DLMF.Bessel.regularizedHGFunCoeff_empty, hp]
    field_simp [Gamma_ne_zero_of_re_pos (show 0 < (a.re : ℂ).re by simpa using ha)]
  have hnorm' (n : ℕ) : (∫ t : ℝ in Ioi 0, ‖F n t‖) =
      (r ^ a.re * Real.Gamma a.re) *
        ‖regularizedHGFunCoeff {(a.re : ℂ)} {c} n * ((r * ‖w‖ : ℝ) : ℂ) ^ n‖ := by
    rw [hnorm, Real.rpow_add hr, Real.rpow_natCast]
    have he := congrArg norm (hcoeff n)
    simp only [norm_mul, Gamma_ofReal, Complex.norm_of_nonneg (Real.Gamma_pos_of_pos ha).le] at he
    rw [show (a.re : ℂ) + n = ((a.re + n : ℝ) : ℂ) by push_cast; rfl,
      Gamma_ofReal, Complex.norm_of_nonneg (Real.Gamma_pos_of_pos (by positivity)).le] at he
    simp only [norm_mul, norm_pow, norm_real,
      Real.norm_of_nonneg (mul_nonneg hr.le (norm_nonneg w)), mul_pow]
    linear_combination -(r ^ a.re * r ^ n * ‖w‖ ^ n) * he
  have hsum : Summable (fun n => ∫ t : ℝ in Ioi 0, ‖F n t‖) := by
    simp_rw [hnorm']
    exact ((hasFPowerSeriesOnBall_regularizedConfluent (a.re : ℂ) c).hasSum_mul_pow
      (z := ((r * ‖w‖ : ℝ) : ℂ)) (by simp)).summable.norm.mul_left _
  have hterm (n : ℕ) : (∫ t : ℝ in Ioi 0, F n t) =
      (b ^ (-a) * Gamma a) * (regularizedHGFunCoeff {a} {c} n * (w / b) ^ n) := by
    rw [integral_const_mul, DLMF.Gamma.integral_cpow_mul_exp_neg_mul_Ioi (han n) hb]
    have hGa := (div_eq_iff (Gamma_ne_zero (not_neg_nat_of_re_pos ha))).mp
      (Gamma_add_nat_div_Gamma_eq (n := n) a (not_neg_nat_of_re_pos ha))
    rw [hGa, show -(a + (n : ℂ)) = -a + -(n : ℂ) by ring, cpow_add _ _ hb0]
    simp only [cpow_neg, cpow_natCast, d, regularizedHGFunCoeff_singleton,
      DLMF.Bessel.regularizedHGFunCoeff_empty, div_pow, poch]
    ring
  have hpoint (t : ℝ) (ht : 0 < t) : (∑' n, F n t) =
      exp (-b * t) * (t : ℂ) ^ (a - 1) * regularizedHGFun ∅ {c} (w * t) := by
    rw [regularizedHGFun_eq_tsum, ← tsum_mul_left]
    apply tsum_congr
    intro n
    dsimp only [F, d]
    rw [show a + n - 1 = (a - 1) + n by ring,
      cpow_add _ _ (ofReal_ne_zero.mpr ht.ne'), cpow_natCast, mul_pow]
    ring
  have hi := hasSum_integral_of_summable_integral_norm hFi hsum
  simp_rw [hterm] at hi
  have he := ((hasFPowerSeriesOnBall_regularizedConfluent a c).hasSum_mul_pow
    (z := w / b) (by simp)).mul_left (b ^ (-a) * Gamma a)
  rw [← hi.unique he]
  exact setIntegral_congr_fun measurableSet_Ioi (fun t ht => (hpoint t ht).symm)

/-- Gaussian–Bessel integral for complex Gaussian scale with positive real part.
The regularization retains all complex orders under `Re(μ+ν)>0`. -/
theorem besselJ_gaussian_integral_complex {μ ν s : ℂ} {w : ℝ}
    (hμν : 0 < (μ + ν).re) (hs : 0 < s.re) (hw : 0 < w) :
    (∫ t : ℝ in Ioi 0, (t : ℂ) ^ (μ - 1) * exp (-s * (t : ℂ) ^ 2) *
      besselJ ν (w * t)) =
      (w / 2 : ℂ) ^ ν / 2 * s ^ (-((μ + ν) / 2)) *
        Gamma ((μ + ν) / 2) *
        regularizedHGFun {(μ + ν) / 2} {ν + 1} (-(w : ℂ) ^ 2 / (4 * s)) := by
  let a : ℂ := (μ + ν) / 2
  let g : ℝ → ℂ := fun u => exp (-s * u) * (u : ℂ) ^ (a - 1) *
    regularizedHGFun ∅ {ν + 1} ((-(w : ℂ) ^ 2 / 4) * u)
  have ha : 0 < a.re := by dsimp [a]; simp only [div_ofNat_re]; linarith
  have hi := integral_exp_cpow_regularized0F1_complex_scaled (c := ν + 1)
    (w := -(w : ℂ) ^ 2 / 4) ha hs
  have he : (∫ u : ℝ in Ioi 0, g u) =
      s ^ (-a) * Gamma a *
        regularizedHGFun {a} {ν + 1} (-(w : ℂ) ^ 2 / (4 * s)) := by
    simpa only [g, div_div] using hi
  have hsubst := integral_comp_rpow_Ioi_of_pos (g := g) (p := 2) (by norm_num)
  norm_num only [Real.rpow_two, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one] at hsubst
  have hpoint (t : ℝ) (ht : 0 < t) :
      (t : ℂ) ^ (μ - 1) * exp (-s * (t : ℂ) ^ 2) * besselJ ν (w * t) =
        (w / 2 : ℂ) ^ ν / 2 * ((2 * t : ℝ) • g (t ^ 2)) := by
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
    have hbase : ((w : ℂ) * t / 2) ^ ν = (w / 2 : ℂ) ^ ν * (t : ℂ) ^ ν := by
      rw [show (w : ℂ) * t / 2 = ((w / 2 : ℝ) : ℂ) * t by push_cast; ring,
        mul_cpow_ofReal_nonneg (by positivity) ht.le, ofReal_div, ofReal_ofNat]
    have hsquare : ((t : ℂ) ^ 2) ^ (a - 1) = (t : ℂ) ^ (2 * (a - 1)) := by
      have h := cpow_mul_ofReal_nonneg ht.le 2 (a - 1)
      norm_num only [Real.rpow_two, ofReal_ofNat, ofReal_pow] at h
      exact h.symm
    have hpowers : (t : ℂ) ^ (μ - 1) * (t : ℂ) ^ ν =
        (t : ℂ) * ((t : ℂ) ^ 2) ^ (a - 1) := by
      rw [hsquare, ← cpow_add _ _ ht0]
      conv_rhs => lhs; rw [← cpow_one (t : ℂ)]
      rw [← cpow_add _ _ ht0]
      congr 1
      dsimp [a]
      ring
    dsimp only [g]
    rw [real_smul, besselJ_eq_regularized, hbase, ofReal_mul, ofReal_ofNat,
      ofReal_pow, show -(((w : ℂ) * t) ^ 2 / 4) =
        (-(w : ℂ) ^ 2 / 4) * (t : ℂ) ^ 2 by ring]
    linear_combination ((w / 2 : ℂ) ^ ν * exp (-s * (t : ℂ) ^ 2) *
      regularizedHGFun ∅ {ν + 1} ((-(w : ℂ) ^ 2 / 4) * (t : ℂ) ^ 2)) * hpowers
  calc
    _ = (w / 2 : ℂ) ^ ν / 2 * ∫ t : ℝ in Ioi 0, (2 * t : ℝ) • g (t ^ 2) := by
      rw [← integral_const_mul]
      exact setIntegral_congr_fun measurableSet_Ioi fun t ht => hpoint t ht
    _ = _ := by rw [hsubst, he]; dsimp [a]; ring

/-- Gaussian–Bessel integral, Beals–Wong (9.8.3), in regularized Kummer form.
The condition `Re(μ+ν)>0` guarantees convergence at zero; `s` and `w` are positive real. -/
theorem besselJ_gaussian_integral {μ ν : ℂ} {s w : ℝ}
    (hμν : 0 < (μ + ν).re) (hs : 0 < s) (hw : 0 < w) :
    (∫ t : ℝ in Ioi 0, (t : ℂ) ^ (μ - 1) * exp (-(s : ℂ) * (t : ℂ) ^ 2) *
      besselJ ν (w * t)) =
      (w / 2 : ℂ) ^ ν / 2 * (1 / (s : ℂ)) ^ ((μ + ν) / 2) *
        Gamma ((μ + ν) / 2) *
        regularizedHGFun {(μ + ν) / 2} {ν + 1} (-(w : ℂ) ^ 2 / (4 * s)) := by
  rw [besselJ_gaussian_integral_complex hμν (by simpa using hs) hw,
    one_div, inv_cpow_ofReal_nonneg hs.le, cpow_neg]

/-- The Gaussian–Bessel integral in ordinary Kummer notation, away from its denominator
poles. The regularized theorem above remains available at exceptional orders. -/
theorem besselJ_gaussian_integral_kummerM {μ ν : ℂ} {s w : ℝ}
    (hμν : 0 < (μ + ν).re) (hs : 0 < s) (hw : 0 < w)
    (hν : ∀ k : ℕ, ν + 1 ≠ -k) :
    (∫ t : ℝ in Ioi 0, (t : ℂ) ^ (μ - 1) * exp (-(s : ℂ) * (t : ℂ) ^ 2) *
      besselJ ν (w * t)) =
      (w / 2 : ℂ) ^ ν / 2 * (1 / (s : ℂ)) ^ ((μ + ν) / 2) *
        (Gamma ((μ + ν) / 2) / Gamma (ν + 1)) *
        kummerM ((μ + ν) / 2) (ν + 1) (-(w : ℂ) ^ 2 / (4 * s)) := by
  rw [besselJ_gaussian_integral hμν hs hw, kummerM_eq_mul_regularizedHGFun hν]
  field_simp [Gamma_ne_zero hν]

/-- The complex-scale Gaussian–Bessel integral in ordinary Kummer notation, away
from denominator poles; the regularized version covers all orders. -/
theorem besselJ_gaussian_integral_complex_kummerM {μ ν s : ℂ} {w : ℝ}
    (hμν : 0 < (μ + ν).re) (hs : 0 < s.re) (hw : 0 < w)
    (hν : ∀ k : ℕ, ν + 1 ≠ -k) :
    (∫ t : ℝ in Ioi 0, (t : ℂ) ^ (μ - 1) * exp (-s * (t : ℂ) ^ 2) *
      besselJ ν (w * t)) =
      (w / 2 : ℂ) ^ ν / 2 * s ^ (-((μ + ν) / 2)) *
        (Gamma ((μ + ν) / 2) / Gamma (ν + 1)) *
        kummerM ((μ + ν) / 2) (ν + 1) (-(w : ℂ) ^ 2 / (4 * s)) := by
  rw [besselJ_gaussian_integral_complex hμν hs hw, kummerM_eq_mul_regularizedHGFun hν]
  field_simp [Gamma_ne_zero hν]

/-- A Laplace–Bessel transform obtained from Kummer's representation of `J` and the full
Kummer Laplace theorem. The Laplace parameter ranges over `Re s > 0`, with no radius
restriction on the continued Gauss argument. The two explicit order exclusions belong
to this Kummer representation; they are not assertions of singularities of the integral. -/
theorem besselJ_laplace_integral_kummer {μ ν s : ℂ} {w : ℝ}
    (hμν : 0 < (μ + ν).re) (hs : 0 < s.re) (hw : 0 < w)
    (hν : ∀ k : ℕ, ν + 1 ≠ -k) (h2ν : ∀ k : ℕ, 2 * ν + 1 ≠ -k) :
    (∫ t : ℝ in Ioi 0, (t : ℂ) ^ (μ - 1) * exp (-s * t) * besselJ ν (w * t)) =
      ((w / 2 : ℂ) ^ ν * Gamma (2 * ν + 1) / Gamma (ν + 1)) *
        (Gamma (μ + ν) * (s + I * w) ^ (-(μ + ν)) *
          regularizedGaussHG (ν + 1 / 2) (μ + ν) (2 * ν + 1)
            (2 * I * w / (s + I * w))) := by
  let C : ℂ := (w / 2 : ℂ) ^ ν * Gamma (2 * ν + 1) / Gamma (ν + 1)
  have hz : 0 < (s + I * w).re := by simpa using hs
  have hzk : (2 * I * w : ℂ).re < (s + I * w).re := by simpa using hs
  have hp (t : ℝ) (ht : 0 < t) :
      (t : ℂ) ^ (μ - 1) * exp (-s * t) * besselJ ν (w * t) =
        C * (exp (-(s + I * w) * t) * (t : ℂ) ^ ((μ + ν) - 1) *
          regularizedHGFun {ν + 1 / 2} {2 * ν + 1} ((2 * I * w) * t)) := by
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
    have hbase : ((w : ℂ) * t / 2) ^ ν = (w / 2 : ℂ) ^ ν * (t : ℂ) ^ ν := by
      rw [show (w : ℂ) * t / 2 = ((w / 2 : ℝ) : ℂ) * t by push_cast; ring,
        mul_cpow_ofReal_nonneg (by positivity) ht.le, ofReal_div, ofReal_ofNat]
    have hexp : exp (-s * t) * exp (-I * (w * t)) = exp (-(s + I * w) * t) := by
      rw [← exp_add]
      congr 1
      ring
    have hpow : (t : ℂ) ^ (μ - 1) * (t : ℂ) ^ ν = (t : ℂ) ^ ((μ + ν) - 1) := by
      rw [← cpow_add _ _ ht0]
      congr 1
      ring
    rw [besselJ_eq_kummerM hν h2ν, hbase, kummerM_eq_mul_regularizedHGFun h2ν,
      show 2 * I * ((w : ℂ) * t) = (2 * I * w) * t by ring]
    calc
      _ = C * ((exp (-s * t) * exp (-I * (w * t))) *
          ((t : ℂ) ^ (μ - 1) * (t : ℂ) ^ ν) *
          regularizedHGFun {ν + 1 / 2} {2 * ν + 1} ((2 * I * w) * t)) := by dsimp [C]; ring
      _ = _ := by rw [hexp, hpow]
  calc
    _ = C * ∫ t : ℝ in Ioi 0,
        exp (-(s + I * w) * t) * (t : ℂ) ^ ((μ + ν) - 1) *
          regularizedHGFun {ν + 1 / 2} {2 * ν + 1} ((2 * I * w) * t) := by
      rw [← integral_const_mul]
      exact setIntegral_congr_fun measurableSet_Ioi fun t ht => hp t ht
    _ = _ := by rw [laplace_regularizedHGFun hμν hzk hz]

end DLMF.Bessel
