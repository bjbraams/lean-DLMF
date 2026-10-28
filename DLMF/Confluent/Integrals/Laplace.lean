/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.Growth
public import DLMF.Confluent.TricomiLaplace
public import DLMF.Confluent.KummerDecay
public import DLMF.Bessel.Asymptotics
public import DLMF.Bessel.Lommel
public import DLMF.Bessel.NeumannSeries
public import DLMF.Hypergeometric.Boundary
public import DLMF.Hypergeometric.Identities
public import Mathlib.Tactic.Monotonicity.Lemmas

/-!
# Laplace integrals of confluent hypergeometric functions

Initial Laplace-transform identities and the integrability estimates needed for them.

Source references and common attribution are retained in
`DLMF.Confluent.Integrals`.
This module uses results of the Tau Ceti contributors; see also `CREDITS.md`.
-/

@[expose] public section

open Complex Filter MeasureTheory FormalMultilinearSeries

open scoped Real Topology ENNReal

open DLMF.Hypergeometric

open DLMF.Bessel

noncomputable section

namespace DLMF.Confluent

/-- Identity under the stated parameter and domain assumptions: `deriv (regularizedHGFun {a - 1}
{b - 1}) z = (a - 1) * regularizedHGFun {a} {b} z`. -/
@[dlmf 13.10.E1]
theorem deriv_regularizedHGFun_shift {a b z : ℂ} (ha : a ≠ 1) :
    deriv (regularizedHGFun {a - 1} {b - 1}) z = (a - 1) * regularizedHGFun {a} {b} z := by
  have hr : (regularizedHGFunSeries {a - 1} {b - 1}).radius = ⊤ :=
    radius_regularizedHGFunSeries_eq_top (by simp)
  have hs : HasFPowerSeriesOnBall (regularizedHGFun {a - 1} {b - 1})
      (regularizedHGFunSeries {a - 1} {b - 1}) 0 ⊤ := by
    change HasFPowerSeriesOnBall (regularizedHGFunSeries {a - 1} {b - 1}).sum
      (regularizedHGFunSeries {a - 1} {b - 1}) 0 ⊤
    simpa only [hr] using (regularizedHGFunSeries {a - 1} {b - 1}).hasFPowerSeriesOnBall
      (by rw [hr]; simp)
  have ht : HasFPowerSeriesOnBall (regularizedHGFun {a} {b})
      (regularizedHGFunSeries {a} {b}) 0 ⊤ := by
    have hr' : (regularizedHGFunSeries {a} {b}).radius = ⊤ :=
      radius_regularizedHGFunSeries_eq_top (by simp)
    change HasFPowerSeriesOnBall (regularizedHGFunSeries {a} {b}).sum
      (regularizedHGFunSeries {a} {b}) 0 ⊤
    simpa only [hr'] using (regularizedHGFunSeries {a} {b}).hasFPowerSeriesOnBall
      (by rw [hr']; simp)
  have hcoeff (n : ℕ) :
      (n + 1 : ℂ) * regularizedHGFunCoeff {a - 1} {b - 1} (n + 1) =
        (a - 1) * regularizedHGFunCoeff {a} {b} n := by
    have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    rw [regularizedHGFunCoeff_singleton, regularizedHGFunCoeff_singleton, poch_succ_left]
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    rw [show (b - 1) + (n + 1) = b + n by ring,
      show a - 1 + 1 = a by ring]
    field [hn, Nat.cast_ne_zero.mpr n.factorial_ne_zero]
  have hd := hs.deriv_ofScalars.hasSum_mul_pow (z := z) (by simp)
  have he := (ht.hasSum_mul_pow (z := z) (by simp)).mul_left (a - 1)
  simp_rw [hcoeff] at hd
  simp only [mul_assoc] at hd he
  exact hd.unique he

/-- Derivative of Tricomi U with shifted parameters. `U` is not complex-differentiable on the cut,
so `z` is restricted to the slit plane. -/
@[dlmf 13.10.E2]
theorem deriv_kummerU_shift {a b z : ℂ} (ha : a ≠ 1) (hz : z ∈ slitPlane) :
    deriv (kummerU (a - 1) (b - 1)) z = -(a - 1) * kummerU a b z := by
  rw [deriv_kummerU (a - 1) (b - 1) hz, sub_add_cancel, sub_add_cancel]

/-- General Kummer Laplace transform in the region of absolute termwise integration. -/
theorem laplace_regularizedHGFun_of_norm_lt {a b c k z : ℂ}
    (hb : 0 < b.re) (hzpos : 0 < z.re) (hk : ‖k‖ < z.re) :
    (∫ t : ℝ in Set.Ioi 0,
      exp (-z * t) * (t : ℂ) ^ (b - 1) * regularizedHGFun {a} {c} (k * t)) =
      Gamma b * z ^ (-b) * DLMF.Hypergeometric.regularizedGaussHG a b c (k / z) := by
  let e : ℕ → ℂ := fun n => regularizedHGFunCoeff {a} {c} n * k ^ n
  let F : ℕ → ℝ → ℂ := fun n t => e n * ((t : ℂ) ^ (b + n - 1) * exp (-(z * t)))
  let r : ℝ := z.re⁻¹
  have hz0 : z ≠ 0 := by intro h; simp [h] at hzpos
  have hrpos : 0 < r := inv_pos.mpr hzpos
  have hrlt : r * ‖k‖ < 1 := by
    dsimp [r]
    rw [inv_mul_eq_div]
    exact (div_lt_one hzpos).mpr hk
  have hbn (n : ℕ) : 0 < (b + n).re := by simp; positivity
  have hnorm (n : ℕ) (t : ℝ) (ht : 0 < t) :
      ‖F n t‖ = ‖e n‖ * (t ^ (b.re + n - 1) * Real.exp (-(z.re * t))) := by
    simp only [F, norm_mul, norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_exp]
    simp
  have hFi (n : ℕ) : IntegrableOn (F n) (Set.Ioi 0) := by
    have hreal := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1)
      (s := b.re + n - 1) (b := z.re) (by have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
          one_pos hzpos
    simp only [Real.rpow_one] at hreal
    apply Integrable.mono' (hreal.const_mul ‖e n‖)
      (Measurable.aestronglyMeasurable (by dsimp [F]; fun_prop))
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [hnorm n t ht]
    simp only [one_mul, neg_mul, le_refl]
  have hInorm (n : ℕ) : (∫ t : ℝ in Set.Ioi 0, ‖F n t‖) =
      ‖e n‖ * (r ^ (b.re + n) * Real.Gamma (b.re + n)) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => hnorm n t ht), integral_const_mul,
      Real.integral_rpow_mul_exp_neg_mul_Ioi (by positivity) hzpos]
    simp only [r, one_div]
  have hGnorm (n : ℕ) : Real.Gamma (b.re + n) =
      ‖poch (b.re : ℂ) n‖ * Real.Gamma b.re := by
    have hp : ∀ k : ℕ, (b.re : ℂ) ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by simpa using hb)
    have hG := (div_eq_iff (Gamma_ne_zero hp)).mp
      (Gamma_add_nat_div_Gamma_eq (n := n) (b.re : ℂ) hp)
    have h := congrArg norm hG
    rw [norm_mul, show (b.re : ℂ) + n = ((b.re + n : ℝ) : ℂ) by push_cast; rfl,
      Gamma_ofReal, Gamma_ofReal, norm_real, norm_real,
      Real.norm_of_nonneg (Real.Gamma_pos_of_pos (by positivity)).le,
      Real.norm_of_nonneg (Real.Gamma_pos_of_pos hb).le] at h
    exact h
  have hsum : Summable (fun n => ∫ t : ℝ in Set.Ioi 0, ‖F n t‖) := by
    have h := DLMF.Hypergeometric.summable_norm_regularizedGaussHGFun_term
      a (b.re : ℂ) c (z := ((r * ‖k‖ : ℝ) : ℂ))
        (by simpa only [norm_real, Real.norm_of_nonneg (mul_nonneg hrpos.le (norm_nonneg k))] using
            hrlt)
    apply (h.mul_left (r ^ b.re * Real.Gamma b.re)).congr
    intro n
    rw [hInorm, hGnorm, Real.rpow_add hrpos, Real.rpow_natCast]
    simp only [e, regularizedHGFunCoeff_singleton, norm_mul, norm_div, norm_pow, norm_inv,
      norm_real, norm_norm,
      ofReal_mul, mul_pow, Real.norm_of_nonneg hrpos.le]
    ring
  have hI (n : ℕ) : (∫ t : ℝ in Set.Ioi 0, F n t) =
      (Gamma b * z ^ (-b)) * ((ascPochhammer ℂ n).eval a *
        (ascPochhammer ℂ n).eval b * (k / z) ^ n / n.factorial * (Gamma (c + n))⁻¹) := by
    rw [integral_const_mul, DLMF.Gamma.integral_cpow_mul_exp_neg_mul_Ioi (hbn n) hzpos]
    have hp := not_neg_nat_of_re_pos hb
    have hGb := (div_eq_iff (Gamma_ne_zero hp)).mp (Gamma_add_nat_div_Gamma_eq (n := n) b hp)
    rw [hGb, show -(b + (n : ℂ)) = -b + -(n : ℂ) by ring, cpow_add _ _ hz0]
    simp only [cpow_neg, cpow_natCast, e, regularizedHGFunCoeff_singleton, div_pow]
    simp only [poch]
    ring
  have ht (t : ℝ) (ht : 0 < t) : (∑' n, F n t) =
      exp (-z * t) * (t : ℂ) ^ (b - 1) * regularizedHGFun {a} {c} (k * t) := by
    rw [regularizedHGFun_eq_tsum, ← tsum_mul_left]
    apply tsum_congr
    intro n
    dsimp [F, e]
    rw [show b + n - 1 = (b - 1) + n by ring,
      cpow_add _ _ (ofReal_ne_zero.mpr ht.ne'), cpow_natCast, mul_pow]
    ring
  have hs := hasSum_integral_of_summable_integral_norm hFi hsum
  have harg : ‖k / z‖ < 1 := by
    rw [norm_div]
    exact (div_lt_one (norm_pos_iff.mpr hz0)).mpr (hk.trans_le (re_le_norm z))
  calc
    _ = ∫ t : ℝ in Set.Ioi 0, ∑' n, F n t :=
      setIntegral_congr_fun measurableSet_Ioi (fun t ht' => (ht t ht').symm)
    _ = ∑' n, ∫ t : ℝ in Set.Ioi 0, F n t := hs.tsum_eq.symm
    _ = _ := by
      simp_rw [hI]
      rw [tsum_mul_left, DLMF.Hypergeometric.regularizedGaussHG_eq_regularizedGaussHGFun a b c harg,
        DLMF.Hypergeometric.regularizedGaussHGFun_eq_tsum]

/-- The transformed argument stays on the Gauss cut plane throughout the Laplace half-plane. -/
theorem kummerLaplace_argument_mem_cutPlane {k z : ℂ}
    (hz : k.re < z.re) (hz0 : 0 < z.re) :
    k / z ∈ DLMF.Hypergeometric.cutPlane := by
  have hzN : z ≠ 0 := by intro h; simp [h] at hz0
  change 1 - k / z ∈ slitPlane
  apply mem_slitPlane_iff.mpr
  by_cases hi : (1 - k / z).im = 0
  · left
    by_contra hn
    have he : k = (1 - (1 - k / z)) * z := by field_simp; ring
    have hr := congrArg Complex.re he
    simp only [mul_re, sub_re, one_re, sub_im, one_im, hi, sub_self, zero_mul, sub_zero] at hr
    have hq : (1 - k / z).re ≤ 0 := le_of_not_gt hn
    simp only [sub_re, one_re] at hq
    nlinarith
  · exact Or.inr hi

/-- The regularized Kummer Laplace transform in its full convergence half-plane. -/
@[dlmf 13.10.E3]
theorem laplace_regularizedHGFun {a b c k z : ℂ}
    (hb : 0 < b.re) (hz : z.re > k.re) (hz0 : 0 < z.re) :
    ∫ t : ℝ in Set.Ioi 0,
        exp (-z * t) * (t : ℂ) ^ (b - 1) * regularizedHGFun {a} {c} (k * t) =
      Gamma b * z ^ (-b) * DLMF.Hypergeometric.regularizedGaussHG a b c (k / z) := by
  let V : Set ℂ := {w | max 0 k.re < w.re}
  have hVo : IsOpen V := isOpen_lt continuous_const continuous_re
  let L (w : ℂ) := ∫ t : ℝ in Set.Ioi 0,
    exp (-w * t) * (t : ℂ) ^ (b - 1) * regularizedHGFun {a} {c} (k * t)
  let R (w : ℂ) := Gamma b * w ^ (-b) * DLMF.Hypergeometric.regularizedGaussHG a b c (k / w)
  have hL : AnalyticOnNhd ℂ L V :=
    (differentiableOn_laplace_regularizedHGFun a b c k hb).analyticOnNhd hVo
  have hR : AnalyticOnNhd ℂ R V := by
    apply DifferentiableOn.analyticOnNhd _ hVo
    intro w hw
    have hw0 : 0 < w.re := (le_max_left 0 k.re).trans_lt hw
    have hwk : k.re < w.re := (le_max_right 0 k.re).trans_lt hw
    have hwN : w ≠ 0 := by intro h; simp [h] at hw0
    have hpow := differentiableAt_id.cpow (differentiableAt_const (-b)) (Or.inl hw0)
    have hG := (DLMF.Hypergeometric.differentiableAt_regularizedGaussHG a b c
      (kummerLaplace_argument_mem_cutPlane hwk hw0)).comp w
      ((differentiableAt_const k).div differentiableAt_id hwN)
    exact ((hpow.const_mul (Gamma b)).mul hG).differentiableWithinAt
  let w₀ : ℂ := (‖k‖ + 1 : ℝ)
  have hw₀ : w₀ ∈ V := by
    dsimp [w₀, V]
    rw [max_lt_iff]
    constructor
    · positivity
    · linarith [re_le_norm k]
  have heq : L =ᶠ[𝓝 w₀] R := by
    have hnh : {w : ℂ | ‖k‖ < w.re} ∈ 𝓝 w₀ :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (by dsimp [w₀]; simp)
    filter_upwards [hnh] with w hw
    exact laplace_regularizedHGFun_of_norm_lt hb ((norm_nonneg k).trans_lt hw) hw
  exact hL.eqOn_of_preconnected_of_eventuallyEq hR
    (convex_halfSpace_re_gt (max 0 k.re)).isPreconnected hw₀ heq (max_lt hz0 hz)

/-- Identity under the stated parameter and domain assumptions: `∫ t : ℝ in Set.Ioi 0, exp (-z *
t) * (t : ℂ) ^ (b - 1) * regularizedHGFun {a} {b} t = z ^ (-b) * (1 - z⁻¹) ^ (-a)`. -/
@[dlmf 13.10.E4]
theorem laplace_regularizedHGFun_self {a b z : ℂ} (hb : 0 < b.re) (hz : 1 < z.re) :
    ∫ t : ℝ in Set.Ioi 0,
        exp (-z * t) * (t : ℂ) ^ (b - 1) * regularizedHGFun {a} {b} t =
      z ^ (-b) * (1 - z⁻¹) ^ (-a) := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz; linarith
  have harg : ‖z⁻¹‖ < 1 := by
    rw [norm_inv, inv_lt_one₀ (norm_pos_iff.mpr hz0)]
    exact hz.trans_le (re_le_norm z)
  have hc := not_neg_nat_of_re_pos hb
  have h := laplace_regularizedHGFun_of_norm_lt (a := a) (b := b) (c := b) (k := 1)
    hb (by linarith) (by simpa using hz)
  simp only [one_mul, one_div] at h
  rw [h, DLMF.Hypergeometric.regularizedGaussHG_eq_regularizedGaussHGFun a b b harg,
    DLMF.Hypergeometric.regularizedGaussHGFun_eq_div_Gamma hc,
    ordinaryHypergeometric_eq_one_sub_neg_cpow
      (fun k hk => hc k (by linear_combination hk)) harg]
  field [Gamma_ne_zero hc]

/-- Absolute Gamma moments of the regularized Kummer coefficients at the boundary.
The proved Gamma-ratio estimate retains the exact convergence inequality. -/
theorem summable_kummer_gamma_moments (a c : ℂ) {b : ℝ} (hb : 0 < b)
    (h : b < (c - a).re) :
    Summable (fun n : ℕ => ‖regularizedHGFunCoeff {a} {c} n‖ * Real.Gamma (b + n)) := by
  by_cases ha : ∀ k : ℕ, a ≠ -k
  · have hs := (DLMF.Hypergeometric.CarlsonAux.summable_norm_Gamma_ratio a b c 1
      (by simp only [sub_re, add_re, ofReal_re, one_re] at h ⊢; linarith)).mul_left ‖Gamma a‖⁻¹
    refine hs.congr fun n => ?_
    have hg := (div_eq_iff (Gamma_ne_zero ha)).mp (Gamma_add_nat_div_Gamma_eq (n := n) a ha)
    rw [show (n : ℂ) + a = a + n by ring, hg,
      show (n : ℂ) + (b : ℂ) = ((b + n : ℝ) : ℂ) by push_cast; ring,
      Gamma_ofReal, Gamma_nat_eq_factorial, regularizedHGFunCoeff_singleton]
    simp only [norm_mul, norm_inv, Complex.norm_natCast, norm_real, norm_div,
      Real.norm_of_nonneg (Real.Gamma_pos_of_pos (by positivity : 0 < b + n)).le]
    rw [show (n : ℂ) + c = c + n by ring]
    field_simp [norm_ne_zero_iff.mpr (Gamma_ne_zero ha)]
  · push_neg at ha
    obtain ⟨m, rfl⟩ := ha
    apply (summable_nat_add_iff (m + 1)).mp
    have he : (fun n : ℕ => ‖regularizedHGFunCoeff {-(m : ℂ)} {c} (n + (m + 1))‖ *
        Real.Gamma (b + (n + (m + 1) : ℕ))) = fun _ : ℕ => 0 := by
      funext n
      simp [regularizedHGFunCoeff_singleton, poch_neg_nat_eq_zero (show m < n + (m + 1) by omega)]
    rw [he]
    exact summable_zero

/-- Identity under the stated parameter and domain assumptions: `∫ t : ℝ in Set.Ioi 0, exp (-(t :
ℂ)) * (t : ℂ) ^ (b - 1) * regularizedHGFun {a} {c} t = Gamma b * Gamma (c - a - b) / (Gamma (c
- a) * Gamma (c - b))`. -/
@[dlmf 13.10.E5]
theorem mellin_regularizedHGFun_exp {a b c : ℂ}
    (hb : 0 < b.re) (h : b.re < (c - a).re) :
    ∫ t : ℝ in Set.Ioi 0,
        exp (-(t : ℂ)) * (t : ℂ) ^ (b - 1) * regularizedHGFun {a} {c} t =
      Gamma b * Gamma (c - a - b) / (Gamma (c - a) * Gamma (c - b)) := by
  let e : ℕ → ℂ := fun n => regularizedHGFunCoeff {a} {c} n
  let F : ℕ → ℝ → ℂ := fun n t => e n * ((t : ℂ) ^ (b + n - 1) * exp (-(t : ℂ)))
  have hbn (n : ℕ) : 0 < (b + n).re := by simp; positivity
  have hnorm (n : ℕ) (t : ℝ) (ht : 0 < t) :
      ‖F n t‖ = ‖e n‖ * (t ^ (b.re + n - 1) * Real.exp (-t)) := by
    simp only [F, norm_mul, norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_exp]
    simp
  have hFi (n : ℕ) : IntegrableOn (F n) (Set.Ioi 0) := by
    have hreal := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1)
      (s := b.re + n - 1) (b := 1) (by have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
        one_pos one_pos
    simp only [Real.rpow_one] at hreal
    apply Integrable.mono' (hreal.const_mul ‖e n‖)
      (Measurable.aestronglyMeasurable (by dsimp [F]; fun_prop))
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [hnorm n t ht]
    simp only [one_mul, neg_mul, le_refl]
  have hInorm (n : ℕ) : (∫ t : ℝ in Set.Ioi 0, ‖F n t‖) =
      ‖e n‖ * Real.Gamma (b.re + n) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => hnorm n t ht), integral_const_mul]
    have hi := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := b.re + n) (r := 1) (by positivity) one_pos
    simpa using congrArg (fun u : ℝ => ‖e n‖ * u) hi
  have hsum : Summable (fun n => ∫ t : ℝ in Set.Ioi 0, ‖F n t‖) := by
    simp_rw [hInorm]
    exact summable_kummer_gamma_moments a c hb h
  have hI (n : ℕ) : (∫ t : ℝ in Set.Ioi 0, F n t) =
      Gamma b * (poch a n * poch b n / (n.factorial * Gamma (c + n))) := by
    rw [integral_const_mul]
    have hi := DLMF.Gamma.integral_cpow_mul_exp_neg_mul_Ioi (hbn n) (z := 1) (by simp)
    simp only [one_mul, one_cpow, mul_one] at hi
    rw [hi]
    have hg := (div_eq_iff (Gamma_ne_zero (not_neg_nat_of_re_pos hb))).mp
      (Gamma_add_nat_div_Gamma_eq (n := n) b (not_neg_nat_of_re_pos hb))
    rw [hg]
    dsimp only [e]
    rw [regularizedHGFunCoeff_singleton]
    ring
  have ht (t : ℝ) (ht : 0 < t) : (∑' n, F n t) =
      exp (-(t : ℂ)) * (t : ℂ) ^ (b - 1) * regularizedHGFun {a} {c} t := by
    rw [regularizedHGFun_eq_tsum, ← tsum_mul_left]
    apply tsum_congr
    intro n
    dsimp [F, e]
    rw [show b + n - 1 = (b - 1) + n by ring,
      cpow_add _ _ (ofReal_ne_zero.mpr ht.ne'), cpow_natCast]
    ring
  have hs := hasSum_integral_of_summable_integral_norm hFi hsum
  calc
    _ = ∫ t : ℝ in Set.Ioi 0, ∑' n, F n t :=
      setIntegral_congr_fun measurableSet_Ioi (fun t ht' => (ht t ht').symm)
    _ = ∑' n, ∫ t : ℝ in Set.Ioi 0, F n t := hs.tsum_eq.symm
    _ = _ := by
      simp_rw [hI]
      rw [tsum_mul_left, (DLMF.Hypergeometric.hasSum_regularizedGauss_one (by simp at h ⊢; linarith)).tsum_eq]
      ring

/-- The Laplace transform of Tricomi U; it converges for `0 < Re z`. -/
@[dlmf 13.10.E7]
theorem laplace_kummerU {a b c z : ℂ}
    (hb : 0 < b.re) (hbc : (c - 1).re < b.re) (hz : 0 < z.re) :
    ∫ t : ℝ in Set.Ioi 0,
        exp (-z * t) * (t : ℂ) ^ (b - 1) * kummerU a c t =
      Gamma b * Gamma (b - c + 1) * z ^ (-b) *
        DLMF.Hypergeometric.regularizedGaussHG a b (a + b - c + 1) (1 - z⁻¹) := by
  have hm := (laplace_kummerU_gauss (a := a) hb hbc hz).2
  change (∫ t : ℝ in Set.Ioi 0, tricomiLaplaceKernel a b c z t) = _
  rw [hm]
  have hz0 : z ≠ 0 := slitPlane_ne_zero (Or.inl hz)
  have hw : 1 - z ∈ DLMF.Hypergeometric.cutPlane := by
    change 1 - (1 - z) ∈ slitPlane
    rw [sub_sub_cancel]; exact Or.inl hz
  have hp := DLMF.Hypergeometric.regularizedGaussHG_pfaff b (b - c + 1) (a + b - c + 1) hw
  have hs := DLMF.Hypergeometric.regularizedGaussHG_symm b a (a + b - c + 1)
    (DLMF.Hypergeometric.div_sub_one_mem_cutPlane hw)
  rw [show (1 - z) / (1 - z - 1) = 1 - z⁻¹ by field_simp [hz0]; ring] at hp hs
  rw [sub_sub_cancel, show (a + b - c + 1) - (b - c + 1) = a by ring] at hp
  rw [hp, hs]
  ring

/-- Identity under the stated parameter and domain assumptions: `∫ t : ℝ in Set.Ioi 0, (t : ℂ) ^
(lam - 1) * regularizedHGFun {a} {b} (-t) = Gamma lam * Gamma (a - lam) / (Gamma a * Gamma (b
- lam))`. -/
@[dlmf 13.10.E10]
theorem mellin_regularizedHGFun {a b lam : ℂ} (hlam : 0 < lam.re) (ha : lam.re < a.re) :
    ∫ t : ℝ in Set.Ioi 0, (t : ℂ) ^ (lam - 1) * regularizedHGFun {a} {b} (-t) =
      Gamma lam * Gamma (a - lam) / (Gamma a * Gamma (b - lam)) := by
  -- Kummer's transformation reduces this to `mellin_regularizedHGFun_exp` at `(b-a, lam, b)`.
  have h := mellin_regularizedHGFun_exp (a := b - a) (b := lam) (c := b) hlam
    (by simpa using ha)
  rw [show b - (b - a) - lam = a - lam by ring, show b - (b - a) = a by ring] at h
  rw [← h]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [regularizedConfluent_kummer_transform a b (-(t : ℂ)), neg_neg]
  ring

/-- Absolute convergence of the double kernel used in Tricomi's Mellin transform.
The Tau Ceti contributors' second Beta integrability theorem controls the outer integral. -/
private lemma integrable_mellin_kummerU_kernel {a b lam : ℂ}
    (hlam0 : (b - 1).re < lam.re) (hlam1 : 0 < lam.re) (ha : lam.re < a.re) :
    Integrable (fun p : ℝ × ℝ =>
      (p.1 : ℂ) ^ (lam - 1) * exp (-(p.2 : ℂ) * p.1) *
        (p.2 : ℂ) ^ (a - 1) * (1 + (p.2 : ℂ)) ^ (b - a - 1))
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0))) := by
  let F (t u : ℝ) : ℂ := (t : ℂ) ^ (lam - 1) * exp (-(u : ℂ) * t) *
    (u : ℂ) ^ (a - 1) * (1 + (u : ℂ)) ^ (b - a - 1)
  let C (u : ℝ) : ℝ := u ^ (a.re - 1) * (1 + u) ^ (b.re - a.re - 1)
  have hnorm (t u : ℝ) (ht : 0 < t) (hu : 0 < u) :
      ‖F t u‖ = C u * (t ^ (lam.re - 1) * Real.exp (-(u * t))) := by
    dsimp only [F, C]
    rw [norm_mul, norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos ht,
      norm_cpow_eq_rpow_re_of_pos hu,
      show 1 + (u : ℂ) = ((1 + u : ℝ) : ℂ) by push_cast; rfl,
      norm_cpow_eq_rpow_re_of_pos (by positivity), Complex.norm_exp]
    simp only [sub_re, one_re, neg_re, mul_re, ofReal_re, ofReal_im]
    ring
  have hbase (u : ℝ) (hu : 0 < u) :
      IntegrableOn (fun t : ℝ => t ^ (lam.re - 1) * Real.exp (-(u * t))) (Set.Ioi 0) := by
    simpa only [Real.rpow_one, neg_mul] using
      integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := lam.re - 1) (b := u)
        (by linarith) one_pos hu
  have hnormIntegral (u : ℝ) (hu : 0 < u) :
      (∫ t : ℝ in Set.Ioi 0, ‖F t u‖) = Real.Gamma lam.re *
        (u ^ (a.re - lam.re - 1) * (1 + u) ^ (b.re - a.re - 1)) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => hnorm t u ht hu),
      integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi hlam1 hu,
      one_div, Real.inv_rpow hu.le, ← Real.rpow_neg hu.le]
    dsimp [C]
    rw [show a.re - lam.re - 1 = (a.re - 1) + -lam.re by ring, Real.rpow_add hu]
    ring
  have hmeas : AEStronglyMeasurable (Function.uncurry F)
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0))) :=
    Measurable.aestronglyMeasurable (by dsimp [F, Function.uncurry]; fun_prop)
  apply (integrable_prod_iff' hmeas).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    refine Integrable.mono' ((hbase u hu).const_mul (C u))
      (Measurable.aestronglyMeasurable (by dsimp [F]; fun_prop)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (hnorm t u ht hu).le
  · have hbeta := TauCeti.integrableOn_rpow_mul_one_add_rpow
      (a := a.re - lam.re) (b := lam.re - b.re + 1) (by linarith)
      (by simp only [sub_re, one_re] at hlam0; linarith)
    have he : -(a.re - lam.re + (lam.re - b.re + 1)) = b.re - a.re - 1 := by ring
    simp only [he] at hbeta
    refine (hbeta.const_mul (Real.Gamma lam.re)).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact (hnormIntegral u hu).symm

/-- Tricomi's Mellin transform is absolutely integrable throughout its stated strip. -/
theorem mellin_kummerU_integrable {a b lam : ℂ}
    (hlam0 : (b - 1).re < lam.re) (hlam1 : 0 < lam.re) (ha : lam.re < a.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (lam - 1) * kummerU a b t) (Set.Ioi 0) := by
  have ha0 : 0 < a.re := hlam1.trans ha
  have h := (integrable_mellin_kummerU_kernel hlam0 hlam1 ha).integral_prod_left
  refine (h.const_mul (1 / Gamma a)).congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [kummerU_laplace ha0 (by simpa using ht)]
  simp_rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  rw [show -(u : ℂ) * t = -(t : ℂ) * u by ring]
  ring

/-- Identity under the stated parameter and domain assumptions: `∫ t : ℝ in Set.Ioi 0, (t : ℂ) ^
(lam - 1) * kummerU a b t = Gamma lam * Gamma (a - lam) * Gamma (lam - b + 1) / (Gamma a *
Gamma (a - b + 1))`. -/
@[dlmf 13.10.E11]
theorem mellin_kummerU {a b lam : ℂ}
    (hlam0 : (b - 1).re < lam.re) (hlam1 : 0 < lam.re) (ha : lam.re < a.re) :
    ∫ t : ℝ in Set.Ioi 0, (t : ℂ) ^ (lam - 1) * kummerU a b t =
      Gamma lam * Gamma (a - lam) * Gamma (lam - b + 1) / (Gamma a * Gamma (a - b + 1)) := by
  have ha0 : 0 < a.re := hlam1.trans ha
  let F (t u : ℝ) : ℂ := (t : ℂ) ^ (lam - 1) * exp (-(u : ℂ) * t) *
    (u : ℂ) ^ (a - 1) * (1 + (u : ℂ)) ^ (b - a - 1)
  have hswap := integral_integral_swap (f := F) (integrable_mellin_kummerU_kernel hlam0 hlam1 ha)
  have hinner (u : ℝ) (hu : 0 < u) : (∫ t : ℝ in Set.Ioi 0, F t u) =
      Gamma lam * ((u : ℂ) ^ (a - lam - 1) / (1 + (u : ℂ)) ^ (a - b + 1)) := by
    have hu0 : (u : ℂ) ≠ 0 := ofReal_ne_zero.mpr hu.ne'
    have he : a - lam - 1 = -lam + (a - 1) := by ring
    have hp : (u : ℂ) ^ (-lam) * (u : ℂ) ^ (a - 1) = (u : ℂ) ^ (a - lam - 1) := by
      rw [← cpow_add _ _ hu0, ← he]
    have hf : (∫ t : ℝ in Set.Ioi 0, F t u) =
        (∫ t : ℝ in Set.Ioi 0, (t : ℂ) ^ (lam - 1) * exp (-((u : ℂ) * t))) *
          ((u : ℂ) ^ (a - 1) * (1 + (u : ℂ)) ^ (b - a - 1)) := by
      rw [← integral_mul_const]
      exact setIntegral_congr_fun measurableSet_Ioi (fun t _ => by
        dsimp [F]; simp only [neg_mul]; ring)
    rw [hf, DLMF.Gamma.integral_cpow_mul_exp_neg_mul_Ioi hlam1 (by simpa using hu)]
    rw [show b - a - 1 = -(a - b + 1) by ring]
    simp only [cpow_neg, div_eq_mul_inv] at hp ⊢
    linear_combination (Gamma lam * ((1 + (u : ℂ)) ^ (a - b + 1))⁻¹) * hp
  calc
    _ = 1 / Gamma a * ∫ t : ℝ in Set.Ioi 0, ∫ u : ℝ in Set.Ioi 0, F t u := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      rw [kummerU_laplace ha0 (by simpa using ht)]
      simp_rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
      dsimp [F]
      rw [show -(t : ℂ) * u = -(u : ℂ) * t by ring]
      ring
    _ = 1 / Gamma a * ∫ u : ℝ in Set.Ioi 0, ∫ t : ℝ in Set.Ioi 0, F t u := by
      rw [hswap]
    _ = 1 / Gamma a * (Gamma lam * betaIntegral (a - lam) (lam - b + 1)) := by
      rw [setIntegral_congr_fun measurableSet_Ioi (fun u hu => hinner u hu), integral_const_mul]
      congr 2
      rw [show a - b + 1 = (a - lam) + (lam - b + 1) by ring]
      exact DLMF.Gamma.beta_on_Ioi (by simp; linarith)
        (by simp only [sub_re, add_re, one_re] at hlam0 ⊢; linarith)
    _ = _ := by
      have hG : Gamma ((a - lam) + (lam - b + 1)) ≠ 0 :=
        Gamma_ne_zero_of_re_pos (by simp only [sub_re, add_re, one_re] at hlam0 ⊢; linarith)
      have hbeta := Gamma_mul_Gamma_eq_betaIntegral
        (s := a - lam) (t := lam - b + 1) (by simp; linarith)
        (by simp only [sub_re, add_re, one_re] at hlam0 ⊢; linarith)
      rw [show (a - lam) + (lam - b + 1) = a - b + 1 by ring] at hbeta hG
      have heB : betaIntegral (a - lam) (lam - b + 1) =
          Gamma (a - lam) * Gamma (lam - b + 1) / Gamma (a - b + 1) := by
        apply (eq_div_iff hG).mpr
        simpa only [mul_comm] using hbeta.symm
      rw [heB]
      simp only [div_eq_mul_inv]
      ring

end DLMF.Confluent
end
end
