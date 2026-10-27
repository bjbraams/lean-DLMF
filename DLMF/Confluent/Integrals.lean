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
# Integrals (DLMF §§13.10, 13.23)

Gauss functions in the transforms use cut-plane continuation. The former series-only
statements were false when their transformed argument left the unit disk.

The general regularized Kummer Laplace transform is proved by termwise integration
when `‖k‖ < Re z` and then by holomorphic continuation throughout the full
convergence half-plane, retaining all denominator parameters, including Gamma poles.
The self-transform specializes it using the binomial identity.
Mathlib's summable-integral-norm theorem justifies the exchange, using a regularized
Gauss series to sum the absolute Gamma moments. The Whittaker M closed transform
then follows with an explicit principal-logarithm calculation in the right half-plane.
Tricomi's Mellin transform follows from its Laplace representation and Mathlib's
Fubini theorem. Absolute convergence of the double kernel reduces to the Tau Ceti
contributors' second Beta integrability theorem; the local proved Gamma and Beta
integral formulas evaluate the exchanged integrals.

The boundary Mellin transform uses a summable Gamma-moment majorant from the
proved Gamma-ratio asymptotics. Regularized Gauss summation, including singular
denominator parameters, evaluates the resulting series; the regularized Whittaker
M transform follows by combining positive-real powers and exponential factors.

The Hankel-type transforms 13.10.14–13.10.15 and 13.23.10–13.23.11 use a power bound for the
kernel `t^{ν/2} J_ν(2√(xt))`, its termwise Laplace transform
`x^{ν/2} s^{-ν-1} e^{-x/s}`, Fubini against the Tricomi Laplace or the Euler integral, and the
substitutions `s ↦ 1/s` and `s = 1/(1+v)`. The cosine transforms 13.10.12 and 13.23.8 use the
Gaussian Fourier integral in the same way. In the Euler cases the result is extended to all
parameters by the identity theorem: the integrals are holomorphic in a parameter by the locally
uniform decay bound of `DLMF.Confluent.KummerDecay`, and `U` is entire in its first parameter.
The Stieltjes transform 13.4.6 is proved here as well.

Indefinite integrals are stated as derivative identities. Laplace, Mellin, and
Bessel transforms use real half-lines. Hankel-loop formulas 13.10.8–13.10.9 and
13.23.6–13.23.7, and the inversion pair 13.23.13–13.23.14, are deferred.
-/

@[expose] public section

open Complex Filter MeasureTheory FormalMultilinearSeries
open scoped Real Topology ENNReal
open DLMF.Hypergeometric
open DLMF.Bessel

noncomputable section

namespace DLMF.Confluent

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

section HankelKernel

/-! ### Hankel-kernel bounds and Laplace transform (used for 13.10.15, 13.23.11) -/

open Set Asymptotics

/-- `t^r e^{-st}` is integrable on `(0,∞)` for `r > -1`, `s > 0`. -/
theorem cfInt_integrableOn_rpow_exp {r s : ℝ} (hr : -1 < r) (hs : 0 < s) :
    IntegrableOn (fun t : ℝ => t ^ r * Real.exp (-(s * t))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := r) (b := s) hr one_pos hs
  refine h.congr_fun (fun t ht => ?_) measurableSet_Ioi
  simp [Real.rpow_one, neg_mul]

/-- `∫₀^∞ t^r e^{-st} dt = Γ(r+1) s^{-(r+1)}`. -/
theorem cfInt_integral_rpow_exp {r s : ℝ} (hr : -1 < r) (hs : 0 < s) :
    ∫ t : ℝ in Ioi 0, t ^ r * Real.exp (-(s * t)) = Real.Gamma (r + 1) * s ^ (-(r + 1)) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := r + 1) (r := s) (by linarith) hs
  rw [add_sub_cancel_right] at h
  rw [h, one_div, Real.inv_rpow hs.le, Real.rpow_neg hs.le]
  ring

/-- `∫₀^∞ e^{-st} t^r (1+t)^{-p} dt ≤ C s^{p-r-1} (1+s)^{-p}` for `r > -1`, `r - p > -1`. -/
theorem cfInt_laplace_rpow_le {r p : ℝ} (hr : -1 < r) (hrp : -1 < r - p) :
    ∃ C, ∀ s : ℝ, 0 < s →
      IntegrableOn (fun t : ℝ => t ^ r * (1 + t) ^ (-p) * Real.exp (-(s * t))) (Ioi 0) ∧
      ∫ t : ℝ in Ioi 0, t ^ r * (1 + t) ^ (-p) * Real.exp (-(s * t)) ≤
        C * (s ^ (p - r - 1) * (1 + s) ^ (-p)) := by
  have hmeas : ∀ s : ℝ, AEStronglyMeasurable
      (fun t : ℝ => t ^ r * (1 + t) ^ (-p) * Real.exp (-(s * t))) (volume.restrict (Ioi 0)) := by
    intro s
    refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
    have ht0 : (0 : ℝ) < t := ht
    exact (((Real.continuousAt_rpow_const _ _ (Or.inl ht0.ne')).mul
      (Real.continuousAt_rpow_const _ _ (Or.inl (by simp only [Pi.add_apply, _root_.id]; linarith)) |>.comp
        (continuous_const.add continuous_id).continuousAt)).mul
      (Real.continuous_exp.comp (by fun_prop)).continuousAt).continuousWithinAt
  rcases le_or_gt 0 p with hp | hp
  · refine ⟨2 ^ p * max (Real.Gamma (r + 1)) (Real.Gamma (r - p + 1)), fun s hs => ?_⟩
    have hI1 := cfInt_integrableOn_rpow_exp hr hs
    have hI2 := cfInt_integrableOn_rpow_exp hrp hs
    have hle1 : ∀ t ∈ Ioi (0 : ℝ), t ^ r * (1 + t) ^ (-p) * Real.exp (-(s * t)) ≤
        t ^ r * Real.exp (-(s * t)) := by
      intro t ht
      have ht0 : (0 : ℝ) < t := ht
      have : (1 + t) ^ (-p) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
      have h0 : 0 ≤ t ^ r * Real.exp (-(s * t)) := by positivity
      nlinarith [Real.rpow_nonneg (by linarith : (0:ℝ) ≤ 1 + t) (-p),
        mul_nonneg (Real.rpow_nonneg ht0.le r) (Real.exp_pos (-(s * t))).le]
    have hle2 : ∀ t ∈ Ioi (0 : ℝ), t ^ r * (1 + t) ^ (-p) * Real.exp (-(s * t)) ≤
        t ^ (r - p) * Real.exp (-(s * t)) := by
      intro t ht
      have ht0 : (0 : ℝ) < t := ht
      have h1 : (1 + t) ^ (-p) ≤ t ^ (-p) :=
        Real.rpow_le_rpow_of_nonpos ht0 (by linarith) (by linarith)
      rw [show r - p = r + -p by ring, Real.rpow_add ht0]
      have := mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg ht0.le r)
      exact mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
    have hnn : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ t ^ r * (1 + t) ^ (-p) * Real.exp (-(s * t)) := by
      intro t ht
      have ht0 : (0 : ℝ) < t := ht
      have := Real.rpow_nonneg (by linarith : (0:ℝ) ≤ 1 + t) (-p)
      positivity
    have hInt : IntegrableOn (fun t : ℝ => t ^ r * (1 + t) ^ (-p) * Real.exp (-(s * t))) (Ioi 0) :=
      hI1.mono' (hmeas s) (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        rw [Real.norm_of_nonneg (hnn t ht)]; exact hle1 t ht)
    refine ⟨hInt, ?_⟩
    have hJ1 := setIntegral_mono_on hInt hI1 measurableSet_Ioi hle1
    have hJ2 := setIntegral_mono_on hInt hI2 measurableSet_Ioi hle2
    rw [cfInt_integral_rpow_exp hr hs] at hJ1
    rw [cfInt_integral_rpow_exp hrp hs] at hJ2
    have hG1 := Real.Gamma_pos_of_pos (by linarith : 0 < r + 1)
    have hG2 := Real.Gamma_pos_of_pos (by linarith : 0 < r - p + 1)
    have h2p : (1 : ℝ) ≤ 2 ^ p := Real.one_le_rpow (by norm_num) hp
    rcases le_or_gt 1 s with hs1 | hs1
    · -- `s ≥ 1`: use the first bound
      refine hJ1.trans ?_
      have e1 : s ^ (-(r + 1)) = s ^ (p - r - 1) * s ^ (-p) := by
        rw [← Real.rpow_add hs]; ring_nf
      have e2 : s ^ (-p) ≤ 2 ^ p * (1 + s) ^ (-p) := by
        have key : (1 + s) ^ p ≤ 2 ^ p * s ^ p :=
          (Real.rpow_le_rpow (by linarith) (by linarith) hp).trans_eq
            (Real.mul_rpow (by norm_num) hs.le)
        rw [Real.rpow_neg hs.le, Real.rpow_neg (by linarith), ← div_eq_mul_inv,
          le_div_iff₀ (by positivity)]
        calc (s ^ p)⁻¹ * (1 + s) ^ p ≤ (s ^ p)⁻¹ * (2 ^ p * s ^ p) := by gcongr
          _ = 2 ^ p := by field_simp
      rw [e1]
      calc Real.Gamma (r + 1) * (s ^ (p - r - 1) * s ^ (-p))
          ≤ max (Real.Gamma (r + 1)) (Real.Gamma (r - p + 1)) *
              (s ^ (p - r - 1) * (2 ^ p * (1 + s) ^ (-p))) := by
            gcongr
            · exact le_max_left _ _
        _ = _ := by ring
    · -- `s < 1`: use the second bound
      refine hJ2.trans ?_
      have e1 : s ^ (-(r - p + 1)) = s ^ (p - r - 1) := by ring_nf
      have e2 : 1 ≤ 2 ^ p * (1 + s) ^ (-p) := by
        rw [Real.rpow_neg (by linarith), ← div_eq_mul_inv, le_div_iff₀ (by positivity), one_mul]
        exact Real.rpow_le_rpow (by linarith) (by linarith) hp
      rw [e1]
      calc Real.Gamma (r - p + 1) * s ^ (p - r - 1)
          ≤ max (Real.Gamma (r + 1)) (Real.Gamma (r - p + 1)) *
              (s ^ (p - r - 1) * (2 ^ p * (1 + s) ^ (-p))) := by
            have hs0 : 0 ≤ s ^ (p - r - 1) := by positivity
            calc Real.Gamma (r - p + 1) * s ^ (p - r - 1)
                ≤ max (Real.Gamma (r + 1)) (Real.Gamma (r - p + 1)) * (s ^ (p - r - 1) * 1) := by
                  rw [mul_one]; gcongr; exact le_max_right _ _
              _ ≤ _ := by gcongr
        _ = _ := by ring
  · set q := -p with hq
    have hq0 : 0 < q := by linarith
    refine ⟨2 ^ q * (Real.Gamma (r + 1) + Real.Gamma (r + q + 1)), fun s hs => ?_⟩
    have hI1 := cfInt_integrableOn_rpow_exp hr hs
    have hI2 := cfInt_integrableOn_rpow_exp (r := r + q) (by linarith) hs
    have hle : ∀ t ∈ Ioi (0 : ℝ), t ^ r * (1 + t) ^ (-p) * Real.exp (-(s * t)) ≤
        2 ^ q * (t ^ r * Real.exp (-(s * t)) + t ^ (r + q) * Real.exp (-(s * t))) := by
      intro t ht
      have ht0 : (0 : ℝ) < t := ht
      have h1 : (1 + t) ^ q ≤ 2 ^ q * (1 + t ^ q) := by
        rcases le_or_gt t 1 with ht1 | ht1
        · calc (1 + t) ^ q ≤ 2 ^ q := Real.rpow_le_rpow (by linarith) (by linarith) hq0.le
            _ ≤ 2 ^ q * (1 + t ^ q) := le_mul_of_one_le_right (by positivity)
                (by linarith [Real.rpow_nonneg ht0.le q])
        · calc (1 + t) ^ q ≤ (2 * t) ^ q := Real.rpow_le_rpow (by linarith) (by linarith) hq0.le
            _ = 2 ^ q * t ^ q := Real.mul_rpow (by norm_num) ht0.le
            _ ≤ 2 ^ q * (1 + t ^ q) := by gcongr; linarith
      rw [show -p = q by rw [hq]]
      rw [Real.rpow_add ht0]
      have he := (Real.exp_pos (-(s * t))).le
      have htr := Real.rpow_nonneg ht0.le r
      calc t ^ r * (1 + t) ^ q * Real.exp (-(s * t))
          ≤ t ^ r * (2 ^ q * (1 + t ^ q)) * Real.exp (-(s * t)) := by gcongr
        _ = _ := by ring
    have hnn : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ t ^ r * (1 + t) ^ (-p) * Real.exp (-(s * t)) := by
      intro t ht
      have ht0 : (0 : ℝ) < t := ht
      have := Real.rpow_nonneg (by linarith : (0:ℝ) ≤ 1 + t) (-p)
      positivity
    have hS : IntegrableOn (fun t : ℝ => 2 ^ q * (t ^ r * Real.exp (-(s * t)) +
        t ^ (r + q) * Real.exp (-(s * t)))) (Ioi 0) := (hI1.add hI2).const_mul (2 ^ q)
    have hInt : IntegrableOn (fun t : ℝ => t ^ r * (1 + t) ^ (-p) * Real.exp (-(s * t))) (Ioi 0) :=
      hS.mono' (hmeas s) (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        rw [Real.norm_of_nonneg (hnn t ht)]; exact hle t ht)
    refine ⟨hInt, ?_⟩
    have hJ := setIntegral_mono_on hInt hS measurableSet_Ioi hle
    rw [integral_const_mul, integral_add hI1 hI2, cfInt_integral_rpow_exp hr hs,
      cfInt_integral_rpow_exp (by linarith) hs] at hJ
    refine hJ.trans ?_
    have e1 : s ^ (-(r + 1)) ≤ s ^ (p - r - 1) * (1 + s) ^ (-p) := by
      rw [show p - r - 1 = -(r + 1) - q by rw [hq]; ring, ← hq, Real.rpow_sub hs, div_mul_eq_mul_div,
        le_div_iff₀ (by positivity)]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hs.le (by linarith) hq0.le) (by positivity)
    have e2 : s ^ (-(r + q + 1)) ≤ s ^ (p - r - 1) * (1 + s) ^ (-p) := by
      rw [show p - r - 1 = -(r + q + 1) by rw [hq]; ring, ← hq]
      exact le_mul_of_one_le_right (by positivity) (Real.one_le_rpow (by linarith) hq0.le)
    have hG1 := Real.Gamma_pos_of_pos (by linarith : 0 < r + 1)
    have hG2 := Real.Gamma_pos_of_pos (by linarith : 0 < r + q + 1)
    calc 2 ^ q * (Real.Gamma (r + 1) * s ^ (-(r + 1)) + Real.Gamma (r + q + 1) * s ^ (-(r + q + 1)))
        ≤ 2 ^ q * (Real.Gamma (r + 1) * (s ^ (p - r - 1) * (1 + s) ^ (-p)) +
            Real.Gamma (r + q + 1) * (s ^ (p - r - 1) * (1 + s) ^ (-p))) := by gcongr
      _ = _ := by ring

/-- Two comparable positive quantities have comparable real powers. -/
theorem cfInt_rpow_le_of_le_mul {A B m M : ℝ} (hA : 0 < A) (hm : 0 < m) (h1 : m * A ≤ B)
    (h2 : B ≤ M * A) (u : ℝ) : B ^ u ≤ max (m ^ u) (M ^ u) * A ^ u := by
  have hB : 0 < B := lt_of_lt_of_le (by positivity) h1
  have hM : 0 < M := by
    by_contra h; push Not at h; nlinarith
  rcases le_or_gt 0 u with hu | hu
  · calc B ^ u ≤ (M * A) ^ u := Real.rpow_le_rpow hB.le h2 hu
      _ = M ^ u * A ^ u := Real.mul_rpow hM.le hA.le
      _ ≤ _ := by gcongr; exact le_max_right _ _
  · calc B ^ u ≤ (m * A) ^ u := Real.rpow_le_rpow_of_nonpos (by positivity) h1 hu.le
      _ = m ^ u * A ^ u := Real.mul_rpow hm.le hA.le
      _ ≤ _ := by gcongr; exact le_max_left _ _

/-- A function continuous on `[a₀,∞)` and `O(g)` at infinity, with `g` continuous and positive,
is bounded by a multiple of `g` on `[a₀,∞)`. -/
theorem cfInt_exists_bound_Ici {f : ℝ → ℂ} {g : ℝ → ℝ} (a₀ : ℝ) (hf : ContinuousOn f (Ici a₀))
    (hg : ContinuousOn g (Ici a₀)) (hgpos : ∀ t, a₀ ≤ t → 0 < g t) (h : f =O[atTop] g) :
    ∃ C, ∀ t, a₀ ≤ t → ‖f t‖ ≤ C * g t := by
  obtain ⟨C1, hC1⟩ := h.bound
  obtain ⟨T, hT⟩ := eventually_atTop.mp hC1
  have hq : ContinuousOn (fun t => ‖f t‖ / g t) (Icc a₀ (max T a₀)) :=
    (hf.norm.div hg fun t ht => (hgpos t ht).ne').mono (fun t ht => ht.1)
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hq
  refine ⟨max C1 K, fun t ht => ?_⟩
  have hg0 := hgpos t ht
  rcases le_or_gt t (max T a₀) with htT | htT
  · have h1 := hK t ⟨ht, htT⟩
    rw [Real.norm_of_nonneg (div_nonneg (norm_nonneg _) hg0.le), div_le_iff₀ hg0] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hg0.le)
  · have h1 := hT t (le_of_lt (lt_of_le_of_lt (le_max_left _ _) htT))
    rw [Real.norm_of_nonneg hg0.le] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hg0.le)

/-- `‖cos w‖ ≤ e^{|Im w|}`. -/
theorem cfInt_norm_cos_le (w : ℂ) : ‖Complex.cos w‖ ≤ Real.exp |w.im| := by
  rw [Complex.cos]
  have h1 : ‖exp (w * I)‖ ≤ Real.exp |w.im| := by
    rw [Complex.norm_exp]; simp only [mul_re, I_re, mul_zero, I_im, mul_one, zero_sub]
    exact Real.exp_le_exp.mpr (neg_le_abs _)
  have h2 : ‖exp (-w * I)‖ ≤ Real.exp |w.im| := by
    rw [Complex.norm_exp]; simp only [mul_re, neg_re, I_re, mul_zero, neg_im, I_im, mul_one,
      zero_sub, neg_neg]
    exact Real.exp_le_exp.mpr (le_abs_self _)
  rw [norm_div, Complex.norm_two]
  have := norm_add_le (exp (w * I)) (exp (-w * I))
  linarith

/-- **Global bound for `J_ν` on the positive axis**: `|J_ν(y)| ≤ C y^{re ν} (1+y)^{-re ν - 1/2}`. -/
theorem cfInt_exists_norm_besselJ_le (ν : ℂ) :
    ∃ C, ∀ y : ℝ, 0 < y → ‖besselJ ν y‖ ≤ C * (y ^ ν.re * (1 + y) ^ (-(ν.re + 1 / 2))) := by
  set σ := ν.re
  obtain ⟨M, hM⟩ := exists_norm_besselJ_mul_le ν (c := 1) one_pos
  -- large `y`
  have hO : (fun y : ℝ => besselJ ν y) =O[atTop] fun y : ℝ => y ^ (-(1 / 2 : ℝ)) := by
    have h1 := besselJ_sub_cos_isBigO ν
    have h2 : (fun y : ℝ => (Real.sqrt (2 / (π * y)) : ℂ) * Complex.cos (y - ν * π / 2 - π / 4))
        =O[atTop] fun y : ℝ => y ^ (-(1 / 2 : ℝ)) := by
      refine IsBigO.of_bound (Real.sqrt (2 / π) * Real.exp |(ν * π / 2).im|) ?_
      filter_upwards [eventually_gt_atTop 0] with y hy
      rw [norm_mul, norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
        Real.norm_of_nonneg (by positivity)]
      have hc := cfInt_norm_cos_le ((y : ℂ) - ν * π / 2 - π / 4)
      have him : (((y : ℂ) - ν * π / 2 - π / 4)).im = -((ν * π / 2).im) := by
        simp
      rw [him, abs_neg] at hc
      have hs : Real.sqrt (2 / (π * y)) = Real.sqrt (2 / π) * y ^ (-(1 / 2 : ℝ)) := by
        rw [Real.rpow_neg hy.le, ← Real.sqrt_eq_rpow, div_mul_eq_div_div, Real.sqrt_div' _ hy.le]
        · ring
      rw [hs]
      calc Real.sqrt (2 / π) * y ^ (-(1 / 2 : ℝ)) * ‖Complex.cos (y - ν * π / 2 - π / 4)‖
          ≤ Real.sqrt (2 / π) * y ^ (-(1 / 2 : ℝ)) * Real.exp |(ν * π / 2).im| := by gcongr
        _ = _ := by ring
    have h3 : (fun y : ℝ => y ^ (-(3 / 2) : ℝ)) =O[atTop] fun y : ℝ => y ^ (-(1 / 2 : ℝ)) := by
      refine IsBigO.of_bound 1 ?_
      filter_upwards [eventually_ge_atTop 1] with y hy
      rw [one_mul, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
      exact Real.rpow_le_rpow_of_exponent_le hy (by norm_num)
    exact ((h1.trans h3).add h2).congr_left fun y => by ring
  have hcont : ContinuousOn (fun y : ℝ => besselJ ν y) (Ici 1) := by
    intro y hy
    have hy0 : (0 : ℝ) < y := by simp only [mem_Ici] at hy; linarith
    have := continuousAt_besselJ_mul ν (c := 1) one_pos hy0
    simp only [ofReal_one, one_mul] at this
    exact this.continuousWithinAt
  obtain ⟨C2, hC2⟩ := cfInt_exists_bound_Ici 1 hcont
    (fun y hy => (Real.continuousAt_rpow_const _ _ (Or.inl (by
      simp only [mem_Ici] at hy; linarith))).continuousWithinAt)
    (fun y hy => by positivity) hO
  set u := -(σ + 1 / 2)
  refine ⟨max (M * 2 ^ |u|) (C2 * 2 ^ |u|), fun y hy => ?_⟩
  rcases le_or_gt y 1 with hy1 | hy1
  · have h1 := hM y ⟨hy, hy1⟩
    simp only [ofReal_one, one_mul] at h1
    have h2 : 1 ≤ 2 ^ |u| * (1 + y) ^ u := by
      rcases le_or_gt 0 u with hu | hu
      · exact one_le_mul_of_one_le_of_one_le (Real.one_le_rpow (by norm_num) (abs_nonneg _))
          (Real.one_le_rpow (by linarith) hu)
      · rw [abs_of_neg hu]
        have : (2 : ℝ) ^ u ≤ (1 + y) ^ u := Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith)
          hu.le
        calc (1 : ℝ) = 2 ^ (-u) * 2 ^ u := by rw [← Real.rpow_add (by norm_num)]; simp
          _ ≤ _ := by gcongr
    have hM0 : 0 ≤ M := by
      have := (norm_nonneg _).trans h1
      exact nonneg_of_mul_nonneg_left this (by positivity)
    calc ‖besselJ ν y‖ ≤ M * y ^ σ := h1
      _ ≤ M * y ^ σ * (2 ^ |u| * (1 + y) ^ u) := le_mul_of_one_le_right (by positivity) h2
      _ = (M * 2 ^ |u|) * (y ^ σ * (1 + y) ^ u) := by ring
      _ ≤ _ := by gcongr; exact le_max_left _ _
  · have h1 := hC2 y hy1.le
    have h2 : y ^ (-(1 / 2 : ℝ)) ≤ 2 ^ |u| * (y ^ σ * (1 + y) ^ u) := by
      have := kumDec_rpow_le_one_add hy1.le u
      calc y ^ (-(1 / 2 : ℝ)) = y ^ σ * y ^ u := by
            rw [← Real.rpow_add hy]; congr 1; simp only [u]; ring
        _ ≤ y ^ σ * (2 ^ |u| * (1 + y) ^ u) := by gcongr
        _ = _ := by ring
    have hC20 : 0 ≤ C2 := by
      have := (norm_nonneg _).trans h1
      exact nonneg_of_mul_nonneg_left this (by positivity)
    calc ‖besselJ ν y‖ ≤ C2 * y ^ (-(1 / 2 : ℝ)) := h1
      _ ≤ C2 * (2 ^ |u| * (y ^ σ * (1 + y) ^ u)) := by gcongr
      _ = (C2 * 2 ^ |u|) * (y ^ σ * (1 + y) ^ u) := by ring
      _ ≤ _ := by
          gcongr
          exact le_max_right _ _

/-- `‖Γ(w+k)‖ Γ(re w) ≥ ‖Γ(w)‖ Γ(re w + k)` for `re w > 0`. -/
theorem cfInt_norm_Gamma_add_nat_ge {w : ℂ} (hw : 0 < w.re) (k : ℕ) :
    ‖Gamma w‖ * Real.Gamma (w.re + k) ≤ ‖Gamma (w + k)‖ * Real.Gamma w.re := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : Gamma (w + (k + 1 : ℕ)) = (w + k) * Gamma (w + k) := by
      rw [show w + ((k + 1 : ℕ) : ℂ) = (w + k) + 1 by push_cast; ring, Gamma_add_one]
      intro h; have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
    have h2 : Real.Gamma (w.re + (k + 1 : ℕ)) = (w.re + k) * Real.Gamma (w.re + k) := by
      rw [show w.re + ((k + 1 : ℕ) : ℝ) = (w.re + k) + 1 by push_cast; ring,
        Real.Gamma_add_one (by positivity)]
    have h3 : w.re + k ≤ ‖w + k‖ := by
      calc w.re + k = (w + k).re := by simp
        _ ≤ _ := re_le_norm _
    rw [h1, h2, norm_mul]
    have hG := (Real.Gamma_pos_of_pos (by positivity : 0 < w.re)).le
    calc ‖Gamma w‖ * ((w.re + k) * Real.Gamma (w.re + k))
        = (w.re + k) * (‖Gamma w‖ * Real.Gamma (w.re + k)) := by ring
      _ ≤ ‖w + k‖ * (‖Gamma (w + k)‖ * Real.Gamma w.re) := by
          gcongr
      _ = _ := by ring

/-- The kernel `t^{ν/2} J_ν(2√(xt))` in power-series form. -/
theorem cfInt_kernel_eq (ν : ℂ) {x : ℂ} (hx : x ≠ 0) {t : ℝ} (ht : 0 < t) :
    (t : ℂ) ^ (ν / 2) * besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) =
      x ^ (ν / 2) * ((t : ℂ) ^ ν * regularizedHGFun ∅ {ν + 1} (-x * t)) := by
  have htc : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  rw [besselJ_two_sqrt hx ht]
  have hνt : (t : ℂ) ^ (ν / 2) * (t : ℂ) ^ (ν / 2) = (t : ℂ) ^ ν := by
    rw [← cpow_add _ _ htc]; ring_nf
  linear_combination (x ^ (ν / 2) * regularizedHGFun ∅ {ν + 1} (-x * t)) * hνt

/-- The Hankel kernel `t^{ν/2} J_ν(2√(xt))` is continuous on `(0,∞)`. -/
theorem cfInt_continuousOn_kernel (ν : ℂ) {x : ℂ} (hx : x ≠ 0) :
    ContinuousOn (fun t : ℝ => (t : ℂ) ^ (ν / 2) * besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)))
      (Ioi 0) := by
  have h : ContinuousOn (fun t : ℝ => x ^ (ν / 2) * ((t : ℂ) ^ ν *
      regularizedHGFun ∅ {ν + 1} (-x * t))) (Ioi 0) := by
    refine continuousOn_const.mul (ContinuousOn.mul ?_ ?_)
    · exact ContinuousOn.cpow continuous_ofReal.continuousOn continuousOn_const
        fun t ht => ofReal_mem_slitPlane.mpr ht
    · exact (continuous_regularized0F1.comp (by fun_prop :
        Continuous fun t : ℝ => (ν + 1, -x * t))).continuousOn
  exact h.congr fun t ht => cfInt_kernel_eq ν hx ht

/-- **The Laplace transform of the Hankel kernel**:
`∫₀^∞ e^{-st} t^{ν/2} J_ν(2√(xt)) dt = x^{ν/2} s^{-ν-1} e^{-x/s}`, for `re ν > -1`, `s > 0`. -/
theorem cfInt_laplace_kernel {ν x : ℂ} (hν : -1 < ν.re) (hx : x ≠ 0) {s : ℝ} (hs : 0 < s) :
    ∫ t : ℝ in Ioi 0, exp (-(s * t : ℂ)) * ((t : ℂ) ^ (ν / 2) *
        besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ))) =
      x ^ (ν / 2) * ((s : ℂ) ^ (-(ν + 1)) * exp (-x / s)) := by
  set d := regularizedHGFunCoeff (∅ : Multiset ℂ) {ν + 1} with hd
  set F : ℕ → ℝ → ℂ := fun k t => x ^ (ν / 2) * (d k * (-x) ^ k) *
    ((t : ℂ) ^ (ν + k + 1 - 1) * exp (-(s * t : ℂ))) with hF
  have hνk : ∀ k : ℕ, 0 < (ν + k + 1).re := fun k => by
    simp; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  have hGk : ∀ k : ℕ, ∫ t : ℝ in Ioi 0, (t : ℂ) ^ (ν + k + 1 - 1) * exp (-(s * t : ℂ)) =
      (1 / (s : ℂ)) ^ (ν + k + 1) * Gamma (ν + k + 1) := fun k => by
    have := integral_cpow_mul_exp_neg_mul_Ioi (a := ν + k + 1) (r := s) (hνk k) hs
    simpa using this
  have hIk : ∀ k : ℕ, IntegrableOn (fun t : ℝ => (t : ℂ) ^ (ν + k + 1 - 1) *
      exp (-(s * t : ℂ))) (Ioi 0) := fun k => by
    have h := cfInt_integrableOn_rpow_exp (r := (ν + k + 1).re - 1) (by linarith [hνk k]) hs
    refine h.mono' ?_ ?_
    · exact (ContinuousOn.mul (ContinuousOn.cpow continuous_ofReal.continuousOn
        continuousOn_const fun t ht => ofReal_mem_slitPlane.mpr ht)
        (by fun_prop : Continuous fun t : ℝ => exp (-(s * t : ℂ))).continuousOn)
        |>.aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : (0 : ℝ) < t := ht
      rw [norm_mul, kumDec_norm_cpow_ofReal ht0, Complex.norm_exp]
      apply le_of_eq; simp
  have hFi : ∀ k, IntegrableOn (F k) (Ioi 0) := fun k => (hIk k).const_mul _
  have hGpos : 0 < Real.Gamma (ν.re + 1) := Real.Gamma_pos_of_pos (by linarith)
  have hG0 : Gamma (ν + 1) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hnormF : ∀ k : ℕ, ∫ t : ℝ in Ioi 0, ‖F k t‖ ≤
      ‖x ^ (ν / 2)‖ * (Real.Gamma (ν.re + 1) / ‖Gamma (ν + 1)‖) * s ^ (-(ν.re + 1)) *
        ((‖x‖ / s) ^ k / k.factorial) := by
    intro k
    have hint : ∫ t : ℝ in Ioi 0, ‖F k t‖ = ‖x ^ (ν / 2)‖ * ‖d k‖ * ‖x‖ ^ k *
        (Real.Gamma (ν.re + k + 1) * s ^ (-(ν.re + k + 1))) := by
      have : ∀ t ∈ Ioi (0 : ℝ), ‖F k t‖ = ‖x ^ (ν / 2)‖ * ‖d k‖ * ‖x‖ ^ k *
          (t ^ (ν.re + k) * Real.exp (-(s * t))) := by
        intro t ht
        have ht0 : (0 : ℝ) < t := ht
        simp only [hF, norm_mul, norm_pow, norm_neg]
        rw [kumDec_norm_cpow_ofReal ht0, Complex.norm_exp]
        simp only [add_re, natCast_re, add_sub_cancel_right]
        have : (-(↑s * ↑t : ℂ)).re = -(s * t) := by simp
        rw [this]; ring
      rw [setIntegral_congr_fun measurableSet_Ioi this, integral_const_mul,
        cfInt_integral_rpow_exp (by linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]) hs]
    rw [hint, hd, DLMF.Bessel.regularizedHGFunCoeff_empty]
    have hGk := cfInt_norm_Gamma_add_nat_ge (w := ν + 1) (by simp; linarith) k
    simp only [add_re, one_re] at hGk
    have hGnk : 0 < ‖Gamma (ν + 1 + k)‖ := by
      have := Gamma_ne_zero_of_re_pos (s := ν + 1 + k) (by simp; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)])
      exact norm_pos_iff.mpr this
    have hG1 : 0 < ‖Gamma (ν + 1)‖ := norm_pos_iff.mpr hG0
    rw [show ν + 1 + (k : ℂ) = ν + 1 + k by rfl] at hGnk
    simp only [norm_div, norm_one, norm_mul, Complex.norm_natCast]
    rw [show ν.re + k + 1 = ν.re + 1 + k by ring, show -(ν.re + 1 + k) = -(ν.re + 1) + -(k : ℝ) by ring,
      Real.rpow_add hs, Real.rpow_neg hs.le (k : ℝ), Real.rpow_natCast, div_pow]
    have hfac : (0 : ℝ) < k.factorial := by positivity
    have hsk : (0 : ℝ) < s ^ k := by positivity
    have hkey : Real.Gamma (ν.re + 1 + k) / ‖Gamma (ν + 1 + k)‖ ≤
        Real.Gamma (ν.re + 1) / ‖Gamma (ν + 1)‖ := by
      rw [div_le_div_iff₀ hGnk hG1]; linarith
    have hpos : 0 ≤ ‖x ^ (ν / 2)‖ * ‖x‖ ^ k * s ^ (-(ν.re + 1)) / (k.factorial * s ^ k) := by
      positivity
    calc ‖x ^ (ν / 2)‖ * (1 / (k.factorial * ‖Gamma (ν + 1 + k)‖)) * ‖x‖ ^ k *
          (Real.Gamma (ν.re + 1 + k) * (s ^ (-(ν.re + 1)) * (s ^ k)⁻¹))
        = (Real.Gamma (ν.re + 1 + k) / ‖Gamma (ν + 1 + k)‖) *
            (‖x ^ (ν / 2)‖ * ‖x‖ ^ k * s ^ (-(ν.re + 1)) / (k.factorial * s ^ k)) := by
          field_simp
      _ ≤ (Real.Gamma (ν.re + 1) / ‖Gamma (ν + 1)‖) *
            (‖x ^ (ν / 2)‖ * ‖x‖ ^ k * s ^ (-(ν.re + 1)) / (k.factorial * s ^ k)) := by
          gcongr
      _ = _ := by field_simp
  have hsum : Summable fun k => ∫ t : ℝ in Ioi 0, ‖F k t‖ := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun t => norm_nonneg _) hnormF ?_
    exact (Real.summable_pow_div_factorial (‖x‖ / s)).mul_left _
  have hs' := hasSum_integral_of_summable_integral_norm hFi hsum
  have hterm : ∀ k : ℕ, ∫ t : ℝ in Ioi 0, F k t =
      x ^ (ν / 2) * ((s : ℂ) ^ (-(ν + 1)) * ((-x / s) ^ k / k.factorial)) := by
    intro k
    have hs0 : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
    simp only [hF]
    rw [integral_const_mul, hGk k, hd, DLMF.Bessel.regularizedHGFunCoeff_empty]
    have hGk' : Gamma (ν + 1 + k) ≠ 0 := Gamma_ne_zero_of_re_pos (by
      simp; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)])
    have hp : (1 / (s : ℂ)) ^ (ν + k + 1) = (s : ℂ) ^ (-(ν + 1)) * ((s : ℂ) ^ k)⁻¹ := by
      rw [one_div, inv_cpow _ _ (by rw [arg_ofReal_of_nonneg hs.le]; exact Real.pi_ne_zero.symm),
        ← cpow_neg, show -(ν + k + 1) = -(ν + 1) + -(k : ℂ) by ring, cpow_add _ _ hs0, cpow_neg,
        cpow_neg (s : ℂ) (k : ℂ), cpow_natCast]
    rw [hp, show ν + k + 1 = ν + 1 + k by ring, div_pow]
    field_simp
  simp_rw [hterm] at hs'
  have hexp : HasSum (fun k : ℕ => (-x / s) ^ k / k.factorial) (exp (-x / s)) := by
    simpa only [exp_eq_exp_ℂ] using NormedSpace.expSeries_div_hasSum_exp (-x / s)
  have hR := (hexp.mul_left ((s : ℂ) ^ (-(ν + 1)))).mul_left (x ^ (ν / 2))
  rw [← hs'.unique hR]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : (0 : ℝ) < t := ht
  have htc : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht0.ne'
  rw [cfInt_kernel_eq ν hx ht0]
  have h0 := ((DLMF.Bessel.hasFPowerSeriesOnBall_regularized0F1 (ν + 1)).hasSum_mul_pow
    (z := -x * t) (by simp)).mul_left (x ^ (ν / 2) * (exp (-(s * t : ℂ)) * (t : ℂ) ^ ν))
  refine Eq.trans ?_ (h0.tsum_eq.symm.trans (tsum_congr fun k => ?_))
  · ring
  · simp only [hF, ← hd]
    rw [show ν + k + 1 - 1 = ν + k by ring, cpow_add _ _ htc, cpow_natCast, mul_pow]
    ring

/-- `2 ((r t)^{1/2})` as a real number. -/
theorem cfInt_two_sqrt_eq {r t : ℝ} (hr : 0 ≤ r) (ht : 0 ≤ t) :
    2 * ((r : ℂ) * t) ^ (1 / 2 : ℂ) = ((2 * (Real.sqrt r * Real.sqrt t) : ℝ) : ℂ) := by
  rw [show ((r : ℂ) * t) = ((r * t : ℝ) : ℂ) by push_cast; ring,
    show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow (by positivity),
    ← Real.sqrt_eq_rpow, Real.sqrt_mul hr]
  push_cast; ring

/-- The Hankel kernel bound `‖t^{ν/2} J_ν(2√(rt))‖ ≤ C t^{re ν} (1+t)^{-(re ν/2+1/4)}`. -/
theorem cfInt_exists_norm_kernel_le (ν : ℂ) {r : ℝ} (hr : 0 < r) :
    ∃ C, ∀ t : ℝ, 0 < t →
      ‖(t : ℂ) ^ (ν / 2) * besselJ ν (2 * ((r : ℂ) * t) ^ (1 / 2 : ℂ))‖ ≤
        C * (t ^ ν.re * (1 + t) ^ (-(ν.re / 2 + 1 / 4))) := by
  obtain ⟨C, hC⟩ := cfInt_exists_norm_besselJ_le ν
  set σ := ν.re with hσ
  set q := Real.sqrt r with hq
  have hq0 : 0 < q := Real.sqrt_pos.mpr hr
  set m := min 1 (2 * q) with hm
  set M := 1 + 2 * q with hM
  have hm0 : 0 < m := lt_min one_pos (by positivity)
  set u := -(σ + 1 / 2) with hu
  refine ⟨max C 0 * 2 ^ σ * q ^ σ * max (m ^ u) (M ^ u), fun t ht => ?_⟩
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  set y := 2 * (q * Real.sqrt t) with hy
  have hy0 : 0 < y := by positivity
  rw [cfInt_two_sqrt_eq hr.le ht.le, norm_mul, kumDec_norm_cpow_ofReal ht]
  have hre : (ν / 2).re = σ / 2 := by simp [hσ]
  rw [hre]
  set A := Real.sqrt (1 + t) with hA
  have hA0 : 0 < A := Real.sqrt_pos.mpr (by linarith)
  have hA1 : 1 ≤ A := by rw [hA, Real.one_le_sqrt]; linarith
  have hAt : Real.sqrt t ≤ A := Real.sqrt_le_sqrt (by linarith)
  have hA2 : A ≤ 1 + Real.sqrt t := by
    rw [hA, Real.sqrt_le_left (by positivity)]
    nlinarith [Real.sq_sqrt ht.le, hst]
  have h1 : m * A ≤ 1 + y := by
    have hm1 : m ≤ 1 := min_le_left _ _
    have hm2 : m ≤ 2 * q := min_le_right _ _
    calc m * A ≤ m * (1 + Real.sqrt t) := by gcongr
      _ = m + m * Real.sqrt t := by ring
      _ ≤ 1 + 2 * q * Real.sqrt t := by gcongr
      _ = 1 + y := by rw [hy]; ring
  have h2 : 1 + y ≤ M * A := by
    rw [hy, hM]; nlinarith
  have hB := cfInt_rpow_le_of_le_mul hA0 hm0 h1 h2 u
  have hAu : A ^ u = (1 + t) ^ (-(σ / 2 + 1 / 4)) := by
    rw [hA, Real.sqrt_eq_rpow, ← Real.rpow_mul (by linarith), hu]; congr 1; ring
  have hyσ : y ^ σ = 2 ^ σ * q ^ σ * t ^ (σ / 2) := by
    rw [hy, Real.mul_rpow (by norm_num) (by positivity), Real.mul_rpow hq0.le hst.le,
      Real.sqrt_eq_rpow t, ← Real.rpow_mul ht.le]
    ring_nf
  have htt : t ^ (σ / 2) * t ^ (σ / 2) = t ^ σ := by
    rw [← Real.rpow_add ht]; ring_nf
  have hJ := hC y hy0
  have hJ' : ‖besselJ ν (y : ℂ)‖ ≤ max C 0 * (y ^ σ * (max (m ^ u) (M ^ u) * A ^ u)) := by
    calc ‖besselJ ν (y : ℂ)‖ ≤ C * (y ^ σ * (1 + y) ^ u) := hJ
      _ ≤ max C 0 * (y ^ σ * (1 + y) ^ u) := by gcongr; exact le_max_left _ _
      _ ≤ _ := by gcongr
  have htp : 0 ≤ t ^ (σ / 2) := by positivity
  calc t ^ (σ / 2) * ‖besselJ ν (y : ℂ)‖
      ≤ t ^ (σ / 2) * (max C 0 * (y ^ σ * (max (m ^ u) (M ^ u) * A ^ u))) := by gcongr
    _ = _ := by
      rw [hAu, hyσ, ← htt]; ring

/-- The substitution `s ↦ 1/s` turning the Hankel–Laplace integral into a Tricomi `U` integral. -/
theorem cfInt_recip_subst_U {a b ν x : ℂ} (hx : 0 < x.re) (hA : 0 < (ν - b + 2).re) :
    ∫ s : ℝ in Ioi 0, (s : ℂ) ^ (a - 1) * (1 + (s : ℂ)) ^ (b - a - 1) *
        ((s : ℂ) ^ (-(ν + 1)) * exp (-x / s)) =
      Gamma (ν - b + 2) * kummerU (ν - b + 2) (ν - a + 2) x := by
  have hU := kummerU_laplace (a := ν - b + 2) (b := ν - a + 2) (z := x) hA hx
  have hGA : Gamma (ν - b + 2) ≠ 0 := Gamma_ne_zero_of_re_pos hA
  rw [show ν - a + 2 - (ν - b + 2) - 1 = b - a - 1 by ring,
    show ν - b + 2 - 1 = ν - b + 1 by ring] at hU
  set g : ℝ → ℂ := fun u => exp (-x * u) * (u : ℂ) ^ (ν - b + 1) * (1 + (u : ℂ)) ^ (b - a - 1)
    with hg
  have hsub := integral_comp_rpow_Ioi g (p := -1) (by norm_num)
  rw [hU, ← hsub]
  field_simp
  refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
  have hs0 : (0 : ℝ) < s := hs
  have hsc : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs0.ne'
  have harg : (s : ℂ).arg ≠ π := by rw [arg_ofReal_of_nonneg hs0.le]; exact Real.pi_ne_zero.symm
  simp only [hg, Real.rpow_neg_one, abs_neg, abs_one, one_mul, real_smul]
  have h2 : ((s ^ (-1 - 1 : ℝ) : ℝ) : ℂ) = (s : ℂ) ^ (-2 : ℂ) := by
    rw [ofReal_cpow hs0.le]; norm_num
  have hinv : ∀ w : ℂ, ((s⁻¹ : ℝ) : ℂ) ^ w = (s : ℂ) ^ (-w) := fun w => by
    rw [ofReal_inv, inv_cpow _ _ harg, cpow_neg]
  have h1s : (1 : ℂ) + ((s⁻¹ : ℝ) : ℂ) = ((1 + s : ℝ) : ℂ) * ((s⁻¹ : ℝ) : ℂ) := by
    push_cast; field_simp; ring
  rw [h2, hinv, h1s, mul_cpow_ofReal_nonneg (by linarith) (by positivity), hinv]
  have e1 : (s : ℂ) ^ (-2 : ℂ) * (s : ℂ) ^ (-(ν - b + 1)) * (s : ℂ) ^ (-(b - a - 1)) =
      (s : ℂ) ^ (a - ν - 2) := by
    rw [← cpow_add _ _ hsc, ← cpow_add _ _ hsc]; ring_nf
  have e2 : (s : ℂ) ^ (a - 1) * (s : ℂ) ^ (-(ν + 1)) = (s : ℂ) ^ (a - ν - 2) := by
    rw [← cpow_add _ _ hsc]; ring_nf
  have hex : exp (-x * ((s⁻¹ : ℝ) : ℂ)) = exp (-x / s) := by
    rw [ofReal_inv, div_eq_mul_inv]
  rw [hex]
  push_cast
  simp only [neg_div] at *
  linear_combination (-(exp (-(x / s)) * (1 + (s : ℂ)) ^ (b - a - 1))) * (e1 - e2)

/-- Tricomi's `U(a,b,z)` is entire in its first parameter, for fixed `b` and `z ≠ 0`. -/
theorem cfInt_differentiable_kummerU_fst (b : ℂ) {z : ℂ} (hz : z ≠ 0) :
    Differentiable ℂ (fun a => kummerU a b z) := by
  have hmem : ∀ c ∈ integerComplement, Differentiable ℂ (fun a => kummerU a c z) := by
    intro c hc
    have hfun : (fun a => kummerU a c z) = fun a => π / sin (π * c) * tricomiD a c z := by
      funext a
      rw [kummerU_eq_connection _ _ _ (forall_of_mem_integerComplement hc),
        kummerUConnection_eq_tricomiD hc]
    rw [hfun]
    refine Differentiable.const_mul ?_ _
    unfold tricomiD
    have h1 : Differentiable ℂ (fun a => regularizedHGFun {a} {c} z) :=
      differentiable_regularizedConfluent_comp differentiable_id (differentiable_const c) z
    have h2 : Differentiable ℂ (fun a => regularizedHGFun {a - c + 1} {2 - c} z) :=
      differentiable_regularizedConfluent_comp (by fun_prop) (differentiable_const _) z
    have h3 : Differentiable ℂ (fun a : ℂ => (Gamma (a - c + 1))⁻¹) :=
      differentiable_one_div_Gamma.comp (by fun_prop)
    have h4 : Differentiable ℂ (fun a : ℂ => (Gamma a)⁻¹) := differentiable_one_div_Gamma
    exact (h1.mul h3).sub ((h2.const_mul _).mul h4)
  have hT : TendstoLocallyUniformlyOn (fun c a => kummerU a c z) (fun a => kummerU a b z)
      (𝓝[integerComplement] b) univ := by
    rw [tendstoLocallyUniformlyOn_iff_filter]
    intro a _
    have hc : ContinuousAt (fun p : ℂ × ℂ => kummerU p.2 p.1 z) (b, a) := by
      have h := continuousAt_kummerU_param a b hz
      exact ContinuousAt.comp (g := fun q : ℂ × ℂ => kummerU q.1 q.2 z)
        (f := fun p : ℂ × ℂ => (p.2, p.1)) h (by fun_prop)
    exact (tendstoUniformlyOnFilter_of_continuousAt (F := fun c a => kummerU a c z) hc
      nhdsWithin_le_nhds).mono_right nhdsWithin_le_nhds
  have := integerComplement_nhdsWithin_neBot b
  have hd := hT.differentiableOn
    (eventually_nhdsWithin_of_forall fun c hc => (hmem c hc).differentiableOn) isOpen_univ
  exact differentiableOn_univ.mp hd

/-- The substitution `s = 1/(1+v)` turning an Euler-type integral on `(0,1)` into a
Tricomi `U` integral. -/
theorem cfInt_euler_subst_U {a c ν x : ℂ} (hx : 0 < x.re) (ha : 0 < a.re) :
    ∫ s in Ioo (0 : ℝ) 1, (s : ℂ) ^ (c - 1) * (1 - (s : ℂ)) ^ (a - 1) *
        ((s : ℂ) ^ (-(ν + 1)) * exp (-x / s)) =
      exp (-x) * (Gamma a * kummerU a (ν + 2 - c) x) := by
  have hU := kummerU_laplace (a := a) (b := ν + 2 - c) (z := x) ha hx
  rw [show ν + 2 - c - a - 1 = ν + 1 - c - a by ring] at hU
  have hGa : Gamma a ≠ 0 := Gamma_ne_zero_of_re_pos ha
  set f : ℝ → ℝ := fun v => (1 + v)⁻¹ with hf
  have himg : f '' Ioi 0 = Ioo 0 1 := by
    ext y
    simp only [mem_image, mem_Ioi, mem_Ioo, hf]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨by positivity, inv_lt_one_of_one_lt₀ (by linarith)⟩
    · rintro ⟨h0, h1⟩
      refine ⟨y⁻¹ - 1, ?_, ?_⟩
      · have : 1 < y⁻¹ := (one_lt_inv₀ h0).mpr h1
        linarith
      · rw [show 1 + (y⁻¹ - 1) = y⁻¹ by ring, inv_inv]
  have hderiv : ∀ v ∈ Ioi (0 : ℝ), HasDerivWithinAt f (-((1 + v) ^ 2)⁻¹) (Ioi 0) v := by
    intro v hv
    have hv0 : (0 : ℝ) < v := hv
    have h : HasDerivAt f (-((1 + v) ^ 2)⁻¹) v := by
      have := (hasDerivAt_inv (show (1 + v) ≠ 0 by linarith)).comp v
        ((hasDerivAt_id v).const_add 1)
      simpa [hf, Function.comp_def] using this
    exact h.hasDerivWithinAt
  have hinj : InjOn f (Ioi 0) := fun u _ v _ h => by
    simp only [hf] at h
    have := inv_injective h
    linarith
  set g : ℝ → ℂ := fun s => (s : ℂ) ^ (c - 1) * (1 - (s : ℂ)) ^ (a - 1) *
    ((s : ℂ) ^ (-(ν + 1)) * exp (-x / s)) with hg
  have hsub := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj g
  rw [himg] at hsub
  rw [hsub, hU, show exp (-x) * (Gamma a * (1 / Gamma a * ∫ t : ℝ in Ioi 0,
      exp (-x * t) * (t : ℂ) ^ (a - 1) * (1 + (t : ℂ)) ^ (ν + 1 - c - a))) =
      ∫ t : ℝ in Ioi 0, exp (-x) *
        (exp (-x * t) * (t : ℂ) ^ (a - 1) * (1 + (t : ℂ)) ^ (ν + 1 - c - a)) by
    rw [integral_const_mul]; field_simp]
  refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
  have hv0 : (0 : ℝ) < v := hv
  have hP0 : (0 : ℝ) < 1 + v := by linarith
  set P : ℂ := ((1 + v : ℝ) : ℂ) with hP
  have hPne : P ≠ 0 := ofReal_ne_zero.mpr hP0.ne'
  have harg : P.arg ≠ π := by rw [hP, arg_ofReal_of_nonneg hP0.le]; exact Real.pi_ne_zero.symm
  have hinv : ∀ w : ℂ, (((1 + v)⁻¹ : ℝ) : ℂ) ^ w = P ^ (-w) := fun w => by
    rw [ofReal_inv, inv_cpow _ _ harg, cpow_neg]
  have h1s : (1 : ℂ) - (((1 + v)⁻¹ : ℝ) : ℂ) = (v : ℂ) * (((1 + v)⁻¹ : ℝ) : ℂ) := by
    rw [ofReal_inv]
    have : (1 + (v : ℂ)) ≠ 0 := by
      have := hPne; rwa [hP, ofReal_add, ofReal_one] at this
    push_cast; field_simp; ring
  have hex : exp (-x / (((1 + v)⁻¹ : ℝ) : ℂ)) = exp (-x) * exp (-x * v) := by
    rw [ofReal_inv, div_inv_eq_mul, ← Complex.exp_add]; push_cast; ring_nf
  have hab : |(-((1 + v) ^ 2)⁻¹ : ℝ)| = ((1 + v) ^ 2)⁻¹ := by
    rw [abs_neg, abs_of_pos (by positivity)]
  have hP2 : ((((1 + v) ^ 2)⁻¹ : ℝ) : ℂ) = (P ^ 2)⁻¹ := by
    rw [hP]; push_cast; ring
  have e : (P ^ 2)⁻¹ * P ^ (-(c - 1)) * P ^ (-(a - 1)) * P ^ (-(-(ν + 1))) =
      P ^ (ν + 1 - c - a) := by
    rw [← cpow_natCast P 2, ← cpow_neg, ← cpow_add _ _ hPne, ← cpow_add _ _ hPne,
      ← cpow_add _ _ hPne]
    push_cast; ring_nf
  have hvP : (1 + (v : ℂ)) = P := by rw [hP]; push_cast; ring
  simp only [hg, hf]
  rw [hab, real_smul, hP2, hinv, h1s, mul_cpow_ofReal_nonneg hv0.le (by positivity), hinv, hinv,
    hex, hvP]
  linear_combination (exp (-x) * exp (-x * v) * (v : ℂ) ^ (a - 1)) * e

/-- 13.10.14 in the Euler region `0 < re a`, in the Kummer-transformed form. -/
theorem cfInt_bessel_M_euler {a b ν x : ℂ} (hx : 0 < x.re) (hxi : x.im = 0) (ha : 0 < a.re)
    (hν0 : -1 < ν.re) (hν1 : ν.re < 2 * (b - a).re - 3 / 2) :
    ∫ t : ℝ in Ioi 0, (t : ℂ) ^ (ν / 2) * besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) *
        regularizedHGFun {b - a} {b} (-(t : ℂ)) =
      x ^ (ν / 2) * exp (-x) / Gamma (b - a) * kummerU a (a - b + ν + 2) x := by
  set r := x.re with hr
  have hxr : x = (r : ℂ) := Complex.ext (by simp [hr]) (by simp [hxi])
  have hx0 : x ≠ 0 := by rw [hxr]; exact ofReal_ne_zero.mpr hx.ne'
  set c := b - a with hc
  have hbc : b - c = a := by rw [hc]; ring
  set σ := ν.re with hσ
  set p := σ / 2 + 1 / 4 with hp
  have hcre : σ / 2 + 3 / 4 < c.re := by linarith
  have hc0 : 0 < c.re := by linarith
  have hGa := Gamma_ne_zero_of_re_pos ha
  have hGc := Gamma_ne_zero_of_re_pos hc0
  set K : ℝ → ℂ := fun t => (t : ℂ) ^ (ν / 2) * besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) with hK
  set E : ℝ → ℝ → ℂ := fun t s => kumDec_eulerKernel c b t s with hE
  set G : ℝ → ℝ → ℂ := fun t s => K t * E t s with hG
  have hKc : ContinuousOn K (Ioi 0) := cfInt_continuousOn_kernel ν hx0
  obtain ⟨CK, hCK⟩ := cfInt_exists_norm_kernel_le ν hx
  obtain ⟨CL, hCL⟩ := cfInt_laplace_rpow_le (r := σ) (p := p) hν0 (by rw [hp]; linarith)
  have hKb : ∀ t : ℝ, 0 < t → ‖K t‖ ≤ CK * (t ^ σ * (1 + t) ^ (-p)) := by
    intro t ht
    have := hCK t ht
    simp only [hK]; rw [hxr]; exact this
  have hEm : Measurable (Function.uncurry E) := by
    simp only [hE, kumDec_eulerKernel]
    fun_prop
  have hm : AEStronglyMeasurable (Function.uncurry G)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioo (0:ℝ) 1))) :=
    ((hKc.aestronglyMeasurable measurableSet_Ioi).comp_fst
      (ν := volume.restrict (Ioo (0:ℝ) 1))).mul hEm.aestronglyMeasurable
  set M2 := max 1 ((2:ℝ) ^ (-p)) with hM2
  have h1s : ∀ s ∈ Ioo (0:ℝ) 1, (1 + s) ^ (-p) ≤ M2 := by
    intro s hs
    rcases le_or_gt 0 (-p) with h | h
    · exact (Real.rpow_le_rpow (by linarith [hs.1]) (by linarith [hs.2]) h).trans
        (le_max_right _ _)
    · exact (Real.rpow_le_one_of_one_le_of_nonpos (by linarith [hs.1]) h.le).trans
        (le_max_left _ _)
  set w : ℝ → ℝ := fun s => s ^ (c.re - 1) * (1 - s) ^ (a.re - 1) with hw
  have hnE : ∀ s ∈ Ioo (0:ℝ) 1, ∀ t, ‖E t s‖ = Real.exp (-(t * s)) * w s := by
    intro s hs t
    simp only [hE, hw]; rw [kumDec_norm_eulerKernel c b hs, hbc]; ring
  have hinner : ∀ s ∈ Ioo (0:ℝ) 1, IntegrableOn (fun t => G t s) (Ioi 0) ∧
      ∫ t in Ioi 0, ‖G t s‖ ≤ CK * CL * M2 * (s ^ (p - σ - 1) * w s) := by
    intro s hs
    obtain ⟨hI, hle⟩ := hCL s hs.1
    have hw0 : 0 ≤ w s :=
      mul_nonneg (Real.rpow_nonneg hs.1.le _) (Real.rpow_nonneg (by linarith [hs.2]) _)
    have hCL0 : 0 ≤ CL := by
      have h0 : 0 ≤ ∫ t in Ioi 0, t ^ σ * (1 + t) ^ (-p) * Real.exp (-(s * t)) :=
        setIntegral_nonneg measurableSet_Ioi fun t ht => by
          have : (0:ℝ) < t := ht
          positivity
      have hpos : 0 < s ^ (p - σ - 1) * (1 + s) ^ (-p) := by
        have := hs.1; positivity
      exact (mul_nonneg_iff_of_pos_right hpos).mp (h0.trans hle)
    have hbd : ∀ t ∈ Ioi (0:ℝ), ‖G t s‖ ≤
        CK * w s * (t ^ σ * (1 + t) ^ (-p) * Real.exp (-(s * t))) := by
      intro t ht
      show ‖K t * E t s‖ ≤ _
      rw [norm_mul (K t), hnE s hs t]
      calc ‖K t‖ * (Real.exp (-(t * s)) * w s)
          ≤ (CK * (t ^ σ * (1 + t) ^ (-p))) * (Real.exp (-(t * s)) * w s) := by
            gcongr; exact hKb t ht
        _ = _ := by rw [mul_comm t s]; ring
    have hInt : IntegrableOn (fun t => G t s) (Ioi 0) := by
      refine (hI.const_mul (CK * w s)).mono' ?_ ?_
      · exact (hKc.aestronglyMeasurable measurableSet_Ioi).mul
          ((hEm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact hbd t ht
    refine ⟨hInt, ?_⟩
    have hCK0 : 0 ≤ CK := by
      have h := (norm_nonneg _).trans (hKb 1 one_pos)
      exact (mul_nonneg_iff_of_pos_right (by positivity)).mp h
    calc ∫ t in Ioi 0, ‖G t s‖
        ≤ ∫ t in Ioi 0, CK * w s * (t ^ σ * (1 + t) ^ (-p) * Real.exp (-(s * t))) :=
          setIntegral_mono_on hInt.norm (hI.const_mul _) measurableSet_Ioi hbd
      _ = CK * w s * ∫ t in Ioi 0, t ^ σ * (1 + t) ^ (-p) * Real.exp (-(s * t)) :=
          integral_const_mul _ _
      _ ≤ CK * w s * (CL * (s ^ (p - σ - 1) * (1 + s) ^ (-p))) := by gcongr
      _ ≤ CK * w s * (CL * (s ^ (p - σ - 1) * M2)) := by
          have := hs.1
          gcongr; exact h1s s hs
      _ = _ := by ring
  have hmaj : IntegrableOn (fun s : ℝ => s ^ (p - σ - 1) * w s) (Ioo 0 1) := by
    have hB := Complex.betaIntegral_convergent (u := ((c.re + p - σ - 1 : ℝ) : ℂ))
      (v := ((a.re : ℝ) : ℂ)) (by simp; linarith) (by simpa using ha)
    have hB' := (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp hB.norm
    refine hB'.congr_fun (fun s hs => ?_) measurableSet_Ioo
    simp only [hw]
    rw [norm_mul, kumDec_norm_cpow_ofReal hs.1,
      show (1 : ℂ) - s = ((1 - s : ℝ) : ℂ) by push_cast; ring,
      kumDec_norm_cpow_ofReal (by linarith [hs.2])]
    simp only [sub_re, ofReal_re, one_re]
    rw [show c.re + p - σ - 1 - 1 = (p - σ - 1) + (c.re - 1) by ring, Real.rpow_add hs.1]
    ring
  have hGi : Integrable (Function.uncurry G)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioo (0:ℝ) 1))) := by
    refine (integrable_prod_iff' hm).mpr ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      exact (hinner s hs).1
    · refine (hmaj.const_mul (CK * CL * M2)).mono' hm.norm.prod_swap.integral_prod_right' ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      exact (hinner s hs).2
  have hts : ∀ t ∈ Ioi (0:ℝ), ∫ s in Ioo 0 1, G t s =
      K t * (Gamma c * Gamma a * regularizedHGFun {c} {b} (-(t : ℂ))) := by
    intro t ht
    have h := kumDec_regularizedHGFun_neg_eq (a := c) (b := b) hc0 (by rw [hbc]; exact ha) t
    rw [hbc] at h
    simp only [hG]
    rw [integral_const_mul, h, intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo]
    field_simp
    rfl
  have hst : ∀ s ∈ Ioo (0:ℝ) 1, ∫ t in Ioi 0, G t s =
      (s : ℂ) ^ (c - 1) * (1 - (s : ℂ)) ^ (a - 1) *
        (x ^ (ν / 2) * ((s : ℂ) ^ (-(ν + 1)) * exp (-x / s))) := by
    intro s hs
    have h := cfInt_laplace_kernel hν0 hx0 hs.1
    rw [← h, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [hG, hE, hK, kumDec_eulerKernel]
    rw [hbc, show -(t : ℂ) * s = -(s * t : ℂ) by ring]
    ring
  calc ∫ t : ℝ in Ioi 0, (t : ℂ) ^ (ν / 2) * besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) *
        regularizedHGFun {c} {b} (-(t : ℂ))
      = ∫ t : ℝ in Ioi 0, (Gamma c * Gamma a)⁻¹ * ∫ s in Ioo 0 1, G t s := by
        refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
        rw [hts t ht]; simp only [hK]; field_simp
    _ = (Gamma c * Gamma a)⁻¹ * ∫ s in Ioo 0 1, ∫ t in Ioi 0, G t s := by
        rw [integral_const_mul, integral_integral_swap hGi]
    _ = (Gamma c * Gamma a)⁻¹ * (x ^ (ν / 2) * ∫ s in Ioo (0:ℝ) 1, (s : ℂ) ^ (c - 1) *
          (1 - (s : ℂ)) ^ (a - 1) * ((s : ℂ) ^ (-(ν + 1)) * exp (-x / s))) := by
        rw [setIntegral_congr_fun measurableSet_Ioo hst, ← integral_const_mul,
          ← integral_const_mul, ← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_Ioo fun s _ => ?_
        ring
    _ = _ := by
        rw [cfInt_euler_subst_U hx ha, show ν + 2 - c = a - b + ν + 2 by rw [hc]; ring]
        field_simp

/-- The Gaussian cosine integral
`∫₀^∞ cos(2xt) e^{-st²} dt = (√π/2) s^{-1/2} e^{-x²/s}`, for `s > 0`. -/
theorem cfInt_integral_cos_gauss (x : ℝ) {s : ℝ} (hs : 0 < s) :
    ∫ t : ℝ in Ioi 0, Complex.cos (2 * x * t) * exp (-((t ^ 2 : ℝ) : ℂ) * s) =
      (Real.sqrt π : ℂ) / 2 * ((s : ℂ) ^ (-(1 / 2 : ℂ)) * exp (-(x : ℂ) ^ 2 / s)) := by
  set g : ℝ → ℝ := fun t => Real.cos (2 * x * t) * Real.exp (-(s * t ^ 2)) with hg
  have hfg : ∀ t : ℝ, Complex.cos (2 * x * t) * exp (-((t ^ 2 : ℝ) : ℂ) * s) = (g t : ℂ) := by
    intro t; simp only [hg]; push_cast; ring_nf
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => hfg t), integral_complex_ofReal]
  have habs : ∫ t, g |t| = 2 * ∫ t in Ioi 0, g t := integral_comp_abs
  have hgabs : (fun t => g |t|) = g := funext fun t => by
    simp only [hg]
    rcases abs_choice t with h | h <;> rw [h]
    simp [mul_neg, Real.cos_neg]
  rw [hgabs] at habs
  have hR : ∫ t in Ioi 0, g t = (∫ t, g t) / 2 := by linarith
  rw [hR]
  have hsplit : ∀ t : ℝ, (g t : ℂ) =
      (cexp (I * ((2 * x : ℝ) : ℂ) * t) * cexp (-(s : ℂ) * (t : ℂ) ^ 2) +
      cexp (I * ((-(2 * x) : ℝ) : ℂ) * t) * cexp (-(s : ℂ) * (t : ℂ) ^ 2)) / 2 := by
    intro t
    simp only [hg]
    push_cast
    rw [Complex.cos, show I * (2 * (x : ℂ)) * t = 2 * x * t * I by ring,
      show I * (-(2 * (x : ℂ))) * t = -(2 * x * t) * I by ring,
      show -((s : ℂ) * (t : ℂ) ^ 2) = -(s : ℂ) * (t : ℂ) ^ 2 by ring]
    ring
  have hI : ∀ T : ℝ, Integrable (fun t : ℝ => cexp (I * T * t) * cexp (-(s : ℂ) * (t : ℂ) ^ 2)) := by
    intro T
    refine (integrable_exp_neg_mul_sq hs).mono' (Continuous.aestronglyMeasurable (by fun_prop))
      (Eventually.of_forall fun t => ?_)
    rw [norm_mul, Complex.norm_exp, Complex.norm_exp,
      show (-(s : ℂ) * (t : ℂ) ^ 2) = ((-s * t ^ 2 : ℝ) : ℂ) by push_cast; ring, ofReal_re,
      show I * (T : ℂ) * t = ((T * t : ℝ) : ℂ) * I by push_cast; ring]
    simp
  have hsc : 0 < (s : ℂ).re := by simpa using hs
  have h1 := fourierIntegral_gaussian hsc ((2 * x : ℝ) : ℂ)
  have h2 := fourierIntegral_gaussian hsc ((-(2 * x) : ℝ) : ℂ)
  have hs0 : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
  have e1 : -((2 * x : ℝ) : ℂ) ^ 2 / (4 * (s : ℂ)) = -(x : ℂ) ^ 2 / s := by
    push_cast; field_simp; ring
  have e2 : -((-(2 * x) : ℝ) : ℂ) ^ 2 / (4 * (s : ℂ)) = -(x : ℂ) ^ 2 / s := by
    push_cast; field_simp; ring
  rw [e1] at h1
  rw [e2] at h2
  have hr : (π / s) ^ (1 / 2 : ℝ) = Real.sqrt π * s ^ (-(1 / 2) : ℝ) := by
    rw [Real.div_rpow (by positivity) hs.le, ← Real.sqrt_eq_rpow, Real.rpow_neg hs.le]; ring
  have hc := congrArg (fun r : ℝ => (r : ℂ)) hr
  rw [ofReal_cpow (by positivity), ofReal_mul, ofReal_cpow hs.le] at hc
  push_cast at hc
  rw [show (((∫ t, g t) / 2 : ℝ) : ℂ) = ((∫ t, g t : ℝ) : ℂ) / 2 by push_cast; ring,
    integral_complex_ofReal.symm, show (fun t : ℝ => (g t : ℂ)) = _ from funext hsplit, integral_div,
    integral_add (hI _) (hI _), h1, h2, hc]
  ring

/-- The cosine transform 13.10.12 in the Euler region `re (B - a) > 0`, before the Kummer
transformation of `U`. -/
theorem cfInt_cosine_euler {a x : ℝ} {B : ℂ} (hx : 0 < x) (ha : 1 / 2 < a) (hB : 0 < (B - a).re) :
    ∫ t : ℝ in Ioi 0, Complex.cos (2 * x * t) * regularizedHGFun {(a : ℂ)} {B} (-(t : ℂ) ^ 2) =
      (Real.sqrt π : ℂ) / (2 * Gamma (a : ℂ)) * exp (-(x : ℂ) ^ 2) *
        kummerU (B - a) (3 / 2 - a) ((x : ℂ) ^ 2) := by
  set A : ℂ := (a : ℂ) with hA
  have hA0 : 0 < A.re := by simp [hA]; linarith
  have hGA := Gamma_ne_zero_of_re_pos hA0
  have hGB := Gamma_ne_zero_of_re_pos hB
  have hBA : B - (B - A) = A := by ring
  set E : ℝ → ℝ → ℂ := fun t s => kumDec_eulerKernel A B (t ^ 2) s with hE
  set G : ℝ → ℝ → ℂ := fun t s => Complex.cos (2 * x * t) * E t s with hG
  have hEm : Measurable (Function.uncurry G) := by
    simp only [hG, hE, kumDec_eulerKernel]
    fun_prop
  have hm : AEStronglyMeasurable (Function.uncurry G)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioo (0:ℝ) 1))) :=
    hEm.aestronglyMeasurable
  set w : ℝ → ℝ := fun s => s ^ (a - 1) * (1 - s) ^ ((B - A).re - 1) with hw
  have hcos : ∀ t : ℝ, ‖Complex.cos (2 * x * t)‖ ≤ 1 := fun t => by
    rw [show (2 * (x : ℂ) * t) = ((2 * x * t : ℝ) : ℂ) by push_cast; ring, ← ofReal_cos,
      norm_real, Real.norm_eq_abs]
    exact Real.abs_cos_le_one _
  have hnG : ∀ s ∈ Ioo (0:ℝ) 1, ∀ t : ℝ, ‖G t s‖ ≤ w s * Real.exp (-s * t ^ 2) := by
    intro s hs t
    simp only [hG, hE]
    rw [norm_mul, kumDec_norm_eulerKernel A B hs]
    have hw0 : 0 ≤ Real.exp (-(t ^ 2 * s)) * s ^ (A.re - 1) * (1 - s) ^ ((B - A).re - 1) := by
      have := hs.1; have : 0 < 1 - s := by linarith [hs.2]
      positivity
    calc ‖Complex.cos (2 * x * t)‖ * (Real.exp (-(t ^ 2 * s)) * s ^ (A.re - 1) *
          (1 - s) ^ ((B - A).re - 1))
        ≤ 1 * (Real.exp (-(t ^ 2 * s)) * s ^ (A.re - 1) * (1 - s) ^ ((B - A).re - 1)) := by
          gcongr; exact hcos t
      _ = _ := by simp only [hw, hA, ofReal_re]; ring_nf
  have hinner : ∀ s ∈ Ioo (0:ℝ) 1, IntegrableOn (fun t => G t s) (Ioi 0) ∧
      ∫ t in Ioi 0, ‖G t s‖ ≤ Real.sqrt π / 2 * (s ^ (-(1 / 2) : ℝ) * w s) := by
    intro s hs
    have hI := (integrable_exp_neg_mul_sq hs.1).integrableOn (s := Ioi (0:ℝ))
    have hInt : IntegrableOn (fun t => G t s) (Ioi 0) :=
      (hI.const_mul (w s)).mono' ((hEm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
        (Eventually.of_forall fun t => hnG s hs t)
    refine ⟨hInt, ?_⟩
    calc ∫ t in Ioi 0, ‖G t s‖ ≤ ∫ t in Ioi 0, w s * Real.exp (-s * t ^ 2) :=
          setIntegral_mono_on hInt.norm (hI.const_mul _) measurableSet_Ioi fun t _ => hnG s hs t
      _ = w s * (Real.sqrt (π / s) / 2) := by rw [integral_const_mul, integral_gaussian_Ioi]
      _ = _ := by
          rw [Real.sqrt_div' _ hs.1.le, Real.sqrt_eq_rpow s, Real.rpow_neg hs.1.le]; ring
  have hmaj : IntegrableOn (fun s : ℝ => s ^ (-(1 / 2) : ℝ) * w s) (Ioo 0 1) := by
    have hB' := Complex.betaIntegral_convergent (u := ((a - 1 / 2 : ℝ) : ℂ))
      (v := (((B - A).re : ℝ) : ℂ)) (by simp; linarith) (by simpa using hB)
    have hB'' := (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp hB'.norm
    refine hB''.congr_fun (fun s hs => ?_) measurableSet_Ioo
    simp only [hw]
    rw [norm_mul, kumDec_norm_cpow_ofReal hs.1,
      show (1 : ℂ) - s = ((1 - s : ℝ) : ℂ) by push_cast; ring,
      kumDec_norm_cpow_ofReal (by linarith [hs.2])]
    simp only [sub_re, ofReal_re, one_re]
    rw [show a - 1 / 2 - 1 = -(1 / 2) + (a - 1) by ring, Real.rpow_add hs.1]
    ring
  have hGi : Integrable (Function.uncurry G)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioo (0:ℝ) 1))) := by
    refine (integrable_prod_iff' hm).mpr ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      exact (hinner s hs).1
    · refine (hmaj.const_mul (Real.sqrt π / 2)).mono' hm.norm.prod_swap.integral_prod_right' ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      exact (hinner s hs).2
  have hts : ∀ t : ℝ, ∫ s in Ioo 0 1, G t s =
      Complex.cos (2 * x * t) * (Gamma A * Gamma (B - A) *
        regularizedHGFun {A} {B} (-(t : ℂ) ^ 2)) := by
    intro t
    have h := kumDec_regularizedHGFun_neg_eq (a := A) (b := B) (t := t ^ 2) hA0 hB
    rw [show (((t ^ 2 : ℝ)) : ℂ) = (t : ℂ) ^ 2 by push_cast; ring] at h
    simp only [hG]
    rw [integral_const_mul, h, intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo]
    field_simp
    rfl
  have hst : ∀ s ∈ Ioo (0:ℝ) 1, ∫ t in Ioi 0, G t s =
      (s : ℂ) ^ (A - 1) * (1 - (s : ℂ)) ^ ((B - A) - 1) *
        ((Real.sqrt π : ℂ) / 2 * ((s : ℂ) ^ (-(1 / 2 : ℂ)) * exp (-((x : ℂ) ^ 2) / s))) := by
    intro s hs
    have h := cfInt_integral_cos_gauss x hs.1
    rw [show -((x : ℂ) ^ 2) = -(x : ℂ) ^ 2 by ring, ← h, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [hG, hE, kumDec_eulerKernel]
    ring
  have hX : 0 < ((x : ℂ) ^ 2).re := by
    rw [← ofReal_pow, ofReal_re]; positivity
  have hsub := cfInt_euler_subst_U (a := B - A) (c := A) (ν := -(1 / 2)) hX hB
  rw [show -(-(1 / 2 : ℂ) + 1) = -(1 / 2) by ring,
    show -(1 / 2 : ℂ) + 2 - A = 3 / 2 - A by ring] at hsub
  calc ∫ t : ℝ in Ioi 0, Complex.cos (2 * x * t) * regularizedHGFun {A} {B} (-(t : ℂ) ^ 2)
      = ∫ t : ℝ in Ioi 0, (Gamma A * Gamma (B - A))⁻¹ * ∫ s in Ioo 0 1, G t s := by
        refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
        rw [hts t]; field_simp
    _ = (Gamma A * Gamma (B - A))⁻¹ * ∫ s in Ioo 0 1, ∫ t in Ioi 0, G t s := by
        rw [integral_const_mul, integral_integral_swap hGi]
    _ = (Gamma A * Gamma (B - A))⁻¹ * ((Real.sqrt π : ℂ) / 2 * ∫ s in Ioo (0:ℝ) 1,
          (s : ℂ) ^ (A - 1) * (1 - (s : ℂ)) ^ ((B - A) - 1) *
            ((s : ℂ) ^ (-(1 / 2 : ℂ)) * exp (-((x : ℂ) ^ 2) / s))) := by
        rw [setIntegral_congr_fun measurableSet_Ioo hst, ← integral_const_mul,
          ← integral_const_mul, ← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_Ioo fun s _ => ?_
        ring
    _ = _ := by
        rw [hsub]
        field_simp

end HankelKernel

open Set in
/-- A cosine transform of `𝐌`. For `a ≤ 1/2` the integral converges only conditionally,
which Lean's integral does not capture, so `1/2 < a` is required. -/
@[dlmf 13.10.E12]
theorem cosine_regularizedHGFun {a b x : ℝ} (hx : 0 < x) (ha : 1 / 2 < a) :
    ∫ t : ℝ in Set.Ioi 0,
        Complex.cos (2 * x * t) * regularizedHGFun {(a : ℂ)} {(b : ℂ)} (-(t : ℂ) ^ 2) =
      (Real.sqrt π : ℂ) / (2 * Gamma (a : ℂ)) * (x : ℂ) ^ (2 * (a : ℂ) - 1) *
        exp (-(x : ℂ) ^ 2) *
        kummerU (b - 1 / 2) (a + 1 / 2) (x ^ 2) := by
  set A : ℂ := (a : ℂ) with hA
  have hAre : A.re = a := by simp [hA]
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hX0 : (x : ℂ) ^ 2 ≠ 0 := pow_ne_zero _ hx0
  set F : ℂ → ℂ := fun B => ∫ t : ℝ in Ioi 0,
    Complex.cos (2 * x * t) * regularizedHGFun {A} {B} (-(t : ℂ) ^ 2) with hF
  set H : ℂ → ℂ := fun B => (Real.sqrt π : ℂ) / (2 * Gamma A) * exp (-(x : ℂ) ^ 2) *
    kummerU (B - A) (3 / 2 - A) ((x : ℂ) ^ 2) with hH
  have hFH : ∀ B : ℂ, 0 < (B - A).re → F B = H B := fun B hB => cfInt_cosine_euler hx ha hB
  set ε := (a - 1 / 2) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hFd : Differentiable ℂ F := by
    refine differentiableOn_univ.mp (Complex.differentiableOn_integral_Ioi_of_locally_dominated
      (Φ := fun B t => Complex.cos (2 * x * t) * regularizedHGFun {A} {B} (-(t : ℂ) ^ 2))
      isOpen_univ 0 ?_ ?_ ?_)
    · intro B _
      exact ((by fun_prop : Continuous fun t : ℝ => Complex.cos (2 * x * t)).mul
        (continuous_regularizedConfluent.comp (by fun_prop :
          Continuous fun t : ℝ => (A, B, -(t : ℂ) ^ 2)))).aestronglyMeasurable
    · refine Eventually.of_forall fun t => ?_
      exact ((differentiable_regularizedConfluent_comp (A := fun _ => A) (B := fun w => w)
        (differentiable_const A) differentiable_id (-(t : ℂ) ^ 2)).const_mul _).differentiableOn
    · intro B₀ _
      obtain ⟨C, hC⟩ := exists_eventually_norm_regularizedHGFun_neg_le A B₀ hε0
      have htend : Tendsto (fun w : ℂ => (A, w)) (𝓝 B₀) (𝓝 (A, B₀)) :=
        ((continuous_const.prodMk continuous_id).tendsto B₀)
      refine ⟨_, htend.eventually hC, fun t => C * (1 + t ^ 2) ^ (-A.re + ε), ?_, ?_⟩
      · have hI := (integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume)
          (r := 2 * (a - ε)) (by simp; rw [hε]; linarith)).integrableOn (s := Ioi (0:ℝ))
        refine IntegrableOn.congr_fun (Integrable.const_mul hI C) (fun t _ => ?_)
          measurableSet_Ioi
        simp only [Real.norm_eq_abs, sq_abs, hAre]
        congr 2; ring
      · refine Eventually.of_forall fun t y hy => ?_
        have h := hy (t ^ 2) (sq_nonneg t)
        rw [show (((t ^ 2 : ℝ)) : ℂ) = (t : ℂ) ^ 2 by push_cast; ring] at h
        have hc : ‖Complex.cos (2 * x * t)‖ ≤ 1 := by
          rw [show (2 * (x : ℂ) * t) = ((2 * x * t : ℝ) : ℂ) by push_cast; ring, ← ofReal_cos,
            norm_real, Real.norm_eq_abs]
          exact Real.abs_cos_le_one _
        rw [norm_mul]
        calc ‖Complex.cos (2 * x * t)‖ * ‖regularizedHGFun {A} {y} (-(t : ℂ) ^ 2)‖
            ≤ 1 * (C * (1 + t ^ 2) ^ (-A.re + ε)) :=
              mul_le_mul hc h (norm_nonneg _) zero_le_one
          _ = _ := one_mul _
  have hHd : Differentiable ℂ H :=
    ((cfInt_differentiable_kummerU_fst (3 / 2 - A) hX0).comp
      (differentiable_id.sub_const A)).const_mul _
  have heq : F = H := by
    refine AnalyticOnNhd.eq_of_eventuallyEq (fun z _ => hFd.analyticAt z)
      (fun z _ => hHd.analyticAt z) (z₀ := A + 1) ?_
    have hopen : IsOpen {w : ℂ | 0 < (w - A).re} :=
      isOpen_lt continuous_const (continuous_re.comp (continuous_id.sub continuous_const))
    filter_upwards [hopen.mem_nhds (by simp : (0:ℝ) < (A + 1 - A).re)] with w hw
    exact hFH w hw
  have h := congrFun heq (b : ℂ)
  simp only [hF, hH] at h
  rw [h, kummerU_kummer_transform_all _ _ hX0,
    show (b : ℂ) - A - (3 / 2 - A) + 1 = b - 1 / 2 by ring,
    show (2 : ℂ) - (3 / 2 - A) = A + 1 / 2 by ring]
  have hp : ((x : ℂ) ^ 2) ^ (1 - (3 / 2 - A)) = (x : ℂ) ^ (2 * A - 1) := by
    rw [sq, mul_cpow_ofReal_nonneg hx.le hx.le, ← cpow_add _ _ hx0]; ring_nf
  rw [hp]
  ring

section LargeParamBessel

/-! ### The Hankel transform 13.10.13

Helpers with prefix `confLP_`. The integral, written with `t^{-ν/2} J_ν(2√(xt)) = x^{ν/2}
𝐅(;ν+1;-xt)`, is evaluated in the Euler region `0 < re a < re b < re ν + 1` by the Euler integral
of `𝐌(b-a,b,-t)`, the Laplace transform of `t^{b-1} 𝐅(;ν+1;-xt)`, the Euler integral of
`𝐌(b,ν+1,-x/s)` and two applications of Fubini's theorem. It is continued analytically in `a`,
and then extended to all orders `ν` by the downward recurrence that the `₀F₁` contiguous relation
and the Kummer contiguous relations induce on both sides. -/

open Set
open scoped Nat

/-- Laplace transform of `t^{β-1} 𝐅(;c;-xt)`. -/
theorem confLP_laplace_0F1 {β c x : ℂ} (hβ : 0 < β.re) {s : ℝ} (hs : 0 < s) :
    ∫ t : ℝ in Ioi 0, exp (-(s * t : ℂ)) * ((t : ℂ) ^ (β - 1) *
        regularizedHGFun (∅ : Multiset ℂ) {c} (-x * t)) =
      Gamma β * (s : ℂ) ^ (-β) * regularizedHGFun {β} {c} (-x / s) := by
  set d := regularizedHGFunCoeff (∅ : Multiset ℂ) {c} with hd
  set F : ℕ → ℝ → ℂ := fun k t => (d k * (-x) ^ k) *
    ((t : ℂ) ^ (β + k - 1) * exp (-(s * t : ℂ))) with hF
  have hβk : ∀ k : ℕ, 0 < (β + k).re := fun k => by
    simp; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  have hGk : ∀ k : ℕ, ∫ t : ℝ in Ioi 0, (t : ℂ) ^ (β + k - 1) * exp (-(s * t : ℂ)) =
      (1 / (s : ℂ)) ^ (β + k) * Gamma (β + k) := fun k => by
    have := integral_cpow_mul_exp_neg_mul_Ioi (a := β + k) (r := s) (hβk k) hs
    simpa using this
  have hIk : ∀ k : ℕ, IntegrableOn (fun t : ℝ => (t : ℂ) ^ (β + k - 1) *
      exp (-(s * t : ℂ))) (Ioi 0) := fun k => by
    have h := cfInt_integrableOn_rpow_exp (r := (β + k).re - 1) (by linarith [hβk k]) hs
    refine h.mono' ?_ ?_
    · exact (ContinuousOn.mul (ContinuousOn.cpow continuous_ofReal.continuousOn
        continuousOn_const fun t ht => ofReal_mem_slitPlane.mpr ht)
        (by fun_prop : Continuous fun t : ℝ => exp (-(s * t : ℂ))).continuousOn)
        |>.aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : (0 : ℝ) < t := ht
      rw [norm_mul, kumDec_norm_cpow_ofReal ht0, Complex.norm_exp]
      apply le_of_eq; simp
  have hFi : ∀ k, IntegrableOn (F k) (Ioi 0) := fun k => (hIk k).const_mul _
  set β0 := β.re with hβ0
  obtain ⟨Cg, hCg0, hCg⟩ := exists_norm_recip_Gamma_add_nat_le c
  have hβ0k : ∀ k : ℕ, ∀ i : ℕ, (β0 : ℂ) + i ≠ 0 := fun k i h => by
    have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg i : (0:ℝ) ≤ i)]
  have hnormF : ∀ k : ℕ, ∫ t : ℝ in Ioi 0, ‖F k t‖ ≤
      (‖Gamma (β0 : ℂ)‖ * Cg * Real.exp β0 * s ^ (-β0)) *
        ((2 * Real.exp 1 * (‖x‖ / s)) ^ k / k !) := by
    intro k
    have hint : ∫ t : ℝ in Ioi 0, ‖F k t‖ = ‖d k‖ * ‖x‖ ^ k *
        (Real.Gamma (β0 + k) * s ^ (-(β0 + k))) := by
      have : ∀ t ∈ Ioi (0 : ℝ), ‖F k t‖ = ‖d k‖ * ‖x‖ ^ k *
          (t ^ (β0 + k - 1) * Real.exp (-(s * t))) := by
        intro t ht
        have ht0 : (0 : ℝ) < t := ht
        simp only [hF, norm_mul, norm_pow, norm_neg]
        rw [kumDec_norm_cpow_ofReal ht0, Complex.norm_exp]
        have : (-(↑s * ↑t : ℂ)).re = -(s * t) := by simp
        rw [this]; simp [hβ0]
      rw [setIntegral_congr_fun measurableSet_Ioi this, integral_const_mul,
        cfInt_integral_rpow_exp (by linarith [hβk k, show (β + k).re = β0 + k by simp [hβ0]]) hs]
      ring_nf
    rw [hint, hd, DLMF.Bessel.regularizedHGFunCoeff_empty]
    have hGR : Real.Gamma (β0 + k) = ‖Gamma (β0 : ℂ)‖ * ‖poch (β0 : ℂ) k‖ := by
      rw [← norm_mul, ← Gamma_add_nat_eq_mul_poch (hβ0k k) k,
        show (β0 : ℂ) + k = ((β0 + k : ℝ) : ℂ) by push_cast; ring, Complex.Gamma_ofReal,
        Complex.norm_real, Real.norm_of_nonneg (Real.Gamma_pos_of_pos (by
          linarith [hβk k, show (β + k).re = β0 + k by simp [hβ0]])).le]
    have hp := norm_poch_le_factorial_mul_exp (β0 : ℂ) k
    rw [Complex.norm_real, Real.norm_of_nonneg hβ.le] at hp
    have hc := hCg k
    have hfac : (0 : ℝ) < k ! := by exact_mod_cast Nat.factorial_pos k
    rw [hGR, show -(β0 + k) = -β0 + -(k : ℝ) by ring, Real.rpow_add hs, Real.rpow_neg hs.le (k : ℝ),
      Real.rpow_natCast]
    simp only [norm_div, norm_one, norm_mul, Complex.norm_natCast]
    rw [div_eq_mul_inv, one_mul, mul_inv, ← norm_inv]
    have hsk : (0 : ℝ) < s ^ k := by positivity
    have e1 : Real.exp (β0 + k) = Real.exp β0 * Real.exp 1 ^ k := by
      rw [Real.exp_add, ← Real.exp_nat_mul, mul_one]
    calc (k ! : ℝ)⁻¹ * ‖(Gamma (c + k))⁻¹‖ * ‖x‖ ^ k *
          (‖Gamma (β0 : ℂ)‖ * ‖poch (β0 : ℂ) k‖ * (s ^ (-β0) * (s ^ k)⁻¹))
        ≤ (k ! : ℝ)⁻¹ * (Cg * (2 ^ k / k !)) * ‖x‖ ^ k *
          (‖Gamma (β0 : ℂ)‖ * (k ! * Real.exp (β0 + k)) * (s ^ (-β0) * (s ^ k)⁻¹)) := by
          gcongr
      _ = _ := by
          rw [e1, mul_pow, mul_pow, div_pow]
          field_simp
  have hsum : Summable fun k => ∫ t : ℝ in Ioi 0, ‖F k t‖ := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun t => norm_nonneg _) hnormF ?_
    exact (Real.summable_pow_div_factorial _).mul_left _
  have hs' := hasSum_integral_of_summable_integral_norm hFi hsum
  have hs0 : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
  have hterm : ∀ k : ℕ, ∫ t : ℝ in Ioi 0, F k t =
      Gamma β * (s : ℂ) ^ (-β) * (regularizedHGFunCoeff {β} {c} k * (-x / s) ^ k) := by
    intro k
    simp only [hF]
    rw [integral_const_mul, hGk k, hd, DLMF.Bessel.regularizedHGFunCoeff_empty,
      regularizedHGFunCoeff_singleton]
    have hp : (1 / (s : ℂ)) ^ (β + k) = (s : ℂ) ^ (-β) * ((s : ℂ) ^ k)⁻¹ := by
      rw [one_div, inv_cpow _ _ (by rw [arg_ofReal_of_nonneg hs.le]; exact Real.pi_ne_zero.symm),
        ← cpow_neg, show -(β + k) = -β + -(k : ℂ) by ring, cpow_add _ _ hs0,
        cpow_neg (s : ℂ) (k : ℂ), cpow_natCast]
    have hG : Gamma (β + k) = Gamma β * poch β k := Gamma_add_nat_eq_mul_poch (fun i h => by
      have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg i : (0:ℝ) ≤ i)]) k
    rw [hp, hG, div_pow]
    field_simp
  simp_rw [hterm] at hs'
  have hR := ((hasFPowerSeriesOnBall_regularizedConfluent β c).hasSum_mul_pow
    (by simp : (-x / s) ∈ Metric.eball (0 : ℂ) ⊤)).mul_left (Gamma β * (s : ℂ) ^ (-β))
  rw [← hs'.unique hR]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : (0 : ℝ) < t := ht
  have htc : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht0.ne'
  have h0 := ((DLMF.Bessel.hasFPowerSeriesOnBall_regularized0F1 c).hasSum_mul_pow
    (z := -x * t) (by simp)).mul_left (exp (-(s * t : ℂ)) * (t : ℂ) ^ (β - 1))
  refine Eq.trans ?_ (h0.tsum_eq.symm.trans (tsum_congr fun k => ?_))
  · ring
  · simp only [hF, ← hd]
    rw [show β + k - 1 = (β - 1) + k by ring, cpow_add _ _ htc, cpow_natCast, mul_pow]
    ring


/-- The inner integral `∫₀¹ s^{c-1}(1-s)^{a-1} s^{-(c+a)} e^{-y/s} ds = e^{-y} Γ(a) y^{-a}`. -/
theorem confLP_inner_integral {a c y : ℂ} (hy : 0 < y.re) (ha : 0 < a.re) :
    ∫ s in Ioo (0 : ℝ) 1, (s : ℂ) ^ (c - 1) * (1 - (s : ℂ)) ^ (a - 1) *
        ((s : ℂ) ^ (-(c + a)) * exp (-y / s)) =
      exp (-y) * (Gamma a * y ^ (-a)) := by
  have h := cfInt_euler_subst_U (a := a) (c := c) (ν := c + a - 1) (x := y) hy ha
  rw [show c + a - 1 + 1 = c + a by ring, show c + a - 1 + 2 - c = a + 1 by ring] at h
  have hy0 : y ≠ 0 := fun h0 => by simp [h0] at hy
  rw [h, kummerU_kummer_transform_all a _ hy0, show a - (a + 1) + 1 = 0 by ring, kummerU_zero,
    show (1 : ℂ) - (a + 1) = -a by ring, mul_one]

/-- `‖𝐅(;ν+1;-rt)‖ ≤ K (1+t)^{-(re ν/2 + 1/4)}` on `(0,∞)`. -/
theorem confLP_exists_norm_0F1_le (ν : ℂ) {r : ℝ} (hr : 0 < r) :
    ∃ K, ∀ t : ℝ, 0 < t → ‖regularizedHGFun (∅ : Multiset ℂ) {ν + 1} (-(r : ℂ) * t)‖ ≤
      K * (1 + t) ^ (-(ν.re / 2 + 1 / 4)) := by
  obtain ⟨C, hC⟩ := cfInt_exists_norm_kernel_le ν hr
  have hx0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
  have hn : 0 < ‖(r : ℂ) ^ (ν / 2)‖ := norm_pos_iff.mpr (by
    rw [cpow_def_of_ne_zero hx0]; exact exp_ne_zero _)
  refine ⟨C / ‖(r : ℂ) ^ (ν / 2)‖, fun t ht => ?_⟩
  have h := hC t ht
  rw [cfInt_kernel_eq ν hx0 ht, norm_mul, norm_mul, kumDec_norm_cpow_ofReal ht] at h
  have htσ : 0 < t ^ ν.re := Real.rpow_pos_of_pos ht _
  rw [div_mul_eq_mul_div, le_div_iff₀ hn]
  have : ‖(r : ℂ) ^ (ν / 2)‖ * (t ^ ν.re *
      ‖regularizedHGFun (∅ : Multiset ℂ) {ν + 1} (-(r : ℂ) * t)‖) ≤
      t ^ ν.re * (C * (1 + t) ^ (-(ν.re / 2 + 1 / 4))) := by linarith
  nlinarith [norm_nonneg (regularizedHGFun (∅ : Multiset ℂ) {ν + 1} (-(r : ℂ) * t))]

/-- Continuity of `t ↦ 𝐅(;ν+1;-rt)`. -/
theorem confLP_continuous_0F1 (ν : ℂ) (r : ℝ) :
    Continuous fun t : ℝ => regularizedHGFun (∅ : Multiset ℂ) {ν + 1} (-(r : ℂ) * t) := by
  have h := continuous_regularized0F1.comp
    (show Continuous fun t : ℝ => ((ν + 1 : ℂ), -(r : ℂ) * t) by fun_prop)
  exact h

/-- Integrability of the 13.10.13 integrand in the `₀F₁` form. -/
theorem confLP_integrableOn {a b ν : ℂ} {r : ℝ} (hr : 0 < r) (hb : 0 < b.re)
    (hν : 2 * a.re < ν.re + 1 / 2) :
    IntegrableOn (fun t : ℝ => exp (-(t : ℂ)) * (t : ℂ) ^ (b - 1) * regularizedHGFun {a} {b} t *
      regularizedHGFun (∅ : Multiset ℂ) {ν + 1} (-(r : ℂ) * t)) (Ioi 0) := by
  obtain ⟨K, hK⟩ := confLP_exists_norm_0F1_le ν hr
  have h := integrableOn_cpow_mul_regularizedHGFun_neg_mul (a := b - a) (b := b) (c := b)
    (h := fun t : ℝ => regularizedHGFun (∅ : Multiset ℂ) {ν + 1} (-(r : ℂ) * t)) (K := K)
    (r := ν.re / 2 + 1 / 4) (confLP_continuous_0F1 ν r).continuousOn hK hb
    (by simp only [sub_re]; linarith)
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  rw [regularizedConfluent_kummer_transform a b (t : ℂ)]
  have he : exp (-(t : ℂ)) * exp (t : ℂ) = 1 := by
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  linear_combination (-((t : ℂ) ^ (b - 1) * regularizedHGFun {b - a} {b} (-(t : ℂ)) *
    regularizedHGFun (∅ : Multiset ℂ) {ν + 1} (-(r : ℂ) * t))) * he


/-- Norm-integral of a function that is real and nonnegative on `S`. -/
theorem confLP_setIntegral_norm_of_ofReal {S : Set ℝ} {f : ℝ → ℂ} {g : ℝ → ℝ}
    (hS : MeasurableSet S) (hfg : ∀ s ∈ S, f s = (g s : ℂ)) (hg : ∀ s ∈ S, 0 ≤ g s) :
    ∫ s in S, ‖f s‖ = ‖∫ s in S, f s‖ := by
  rw [setIntegral_congr_fun hS (fun s hs => by
      rw [hfg s hs, Complex.norm_real, Real.norm_of_nonneg (hg s hs)]),
    setIntegral_congr_fun hS hfg, integral_complex_ofReal, Complex.norm_real,
    Real.norm_of_nonneg (setIntegral_nonneg hS hg)]

/-- A set integral that is nonzero comes from an integrable function. -/
theorem confLP_integrableOn_of_ne_zero {S : Set ℝ} {f : ℝ → ℂ} (h : ∫ s in S, f s ≠ 0) :
    IntegrableOn f S := by
  by_contra hf
  exact h (integral_undef hf)

/-- The Euler kernel with real parameters is real and nonnegative. -/
theorem confLP_eulerKernel_ofReal (γ β : ℝ) (t : ℝ) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    kumDec_eulerKernel (γ : ℂ) (β : ℂ) t s =
      ((Real.exp (-(t * s)) * s ^ (γ - 1) * (1 - s) ^ (β - γ - 1) : ℝ) : ℂ) := by
  simp only [kumDec_eulerKernel]
  rw [Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_exp,
    ofReal_cpow hs.1.le, ofReal_cpow (by linarith [hs.2] : (0:ℝ) ≤ 1 - s)]
  push_cast
  ring_nf

/-- The double-integral kernel of the second Fubini step. -/
def confLP_Q (c a b μ : ℂ) (r s ρ : ℝ) : ℂ :=
  (s : ℂ) ^ (c - 1) * (1 - (s : ℂ)) ^ (a - 1) * (s : ℂ) ^ (-b) *
    (exp (-(r : ℂ) / s * ρ) * (ρ : ℂ) ^ (b - 1) * (1 - (ρ : ℂ)) ^ (μ - b))

/-- Measurability of the kernel `confLP_Q`. -/
theorem confLP_measurable_Q (c a b μ : ℂ) (r : ℝ) :
    Measurable (Function.uncurry (confLP_Q c a b μ r)) := by
  unfold confLP_Q
  fun_prop

/-- The modulus of the kernel `confLP_Q` on the open unit square. -/
theorem confLP_norm_Q (c a b μ : ℂ) (r : ℝ) {s ρ : ℝ} (hs : s ∈ Ioo (0:ℝ) 1)
    (hρ : ρ ∈ Ioo (0:ℝ) 1) :
    ‖confLP_Q c a b μ r s ρ‖ = s ^ (c.re - 1) * (1 - s) ^ (a.re - 1) * s ^ (-b.re) *
      (Real.exp (-(r / s * ρ)) * ρ ^ (b.re - 1) * (1 - ρ) ^ (μ.re - b.re)) := by
  have h1 : (1 : ℂ) - s = ((1 - s : ℝ) : ℂ) := by push_cast; ring
  have h2 : (1 : ℂ) - ρ = ((1 - ρ : ℝ) : ℂ) := by push_cast; ring
  simp only [confLP_Q, norm_mul, Complex.norm_exp]
  rw [h1, h2, kumDec_norm_cpow_ofReal hs.1, kumDec_norm_cpow_ofReal hs.1,
    kumDec_norm_cpow_ofReal (by linarith [hs.2]), kumDec_norm_cpow_ofReal hρ.1,
    kumDec_norm_cpow_ofReal (by linarith [hρ.2])]
  have : (-(r : ℂ) / s * ρ).re = -(r / s * ρ) := by
    rw [show -(r : ℂ) / s * ρ = ((-(r / s * ρ) : ℝ) : ℂ) by push_cast; ring, ofReal_re]
  rw [this]
  simp

/-- With real parameters the kernel `confLP_Q` is real. -/
theorem confLP_Q_ofReal (γ α β μ r : ℝ) {s ρ : ℝ} (hs : s ∈ Ioo (0:ℝ) 1)
    (hρ : ρ ∈ Ioo (0:ℝ) 1) :
    confLP_Q (γ : ℂ) (α : ℂ) (β : ℂ) (μ : ℂ) r s ρ =
      ((s ^ (γ - 1) * (1 - s) ^ (α - 1) * s ^ (-β) *
        (Real.exp (-(r / s * ρ)) * ρ ^ (β - 1) * (1 - ρ) ^ (μ - β)) : ℝ) : ℂ) := by
  simp only [confLP_Q]
  push_cast
  rw [ofReal_cpow hs.1.le, ofReal_cpow (by linarith [hs.2] : (0:ℝ) ≤ 1 - s),
    ofReal_cpow hs.1.le, ofReal_cpow hρ.1.le, ofReal_cpow (by linarith [hρ.2] : (0:ℝ) ≤ 1 - ρ)]
  push_cast
  ring_nf

/-- The inner integral of `confLP_Q` over `s`. -/
theorem confLP_integral_Q {c a b μ : ℂ} {r : ℝ} (hr : 0 < r) (hcab : c + a = b) (ha : 0 < a.re)
    {ρ : ℝ} (hρ : ρ ∈ Ioo (0:ℝ) 1) :
    ∫ s in Ioo (0:ℝ) 1, confLP_Q c a b μ r s ρ =
      (ρ : ℂ) ^ (b - 1) * (1 - (ρ : ℂ)) ^ (μ - b) *
        (exp (-((r : ℂ) * ρ)) * (Gamma a * ((r : ℂ) * ρ) ^ (-a))) := by
  have hy : 0 < ((r : ℂ) * ρ).re := by
    rw [show (r : ℂ) * ρ = ((r * ρ : ℝ) : ℂ) by push_cast; ring, ofReal_re]
    exact mul_pos hr hρ.1
  have h := confLP_inner_integral (a := a) (c := c) (y := (r : ℂ) * ρ) hy ha
  rw [hcab] at h
  rw [← h, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
  simp only [confLP_Q]
  rw [show -(r : ℂ) / s * ρ = -((r : ℂ) * ρ) / s by ring]
  ring


/-- Base case of 13.10.13 (in `₀F₁` form) in the Euler region. -/
theorem confLP_base {a b ν : ℂ} {r : ℝ} (hr : 0 < r) (ha : 0 < a.re) (hba : 0 < (b - a).re)
    (hνb : 0 < (ν + 1 - b).re) (hν : 2 * a.re < ν.re + 1 / 2) :
    ∫ t : ℝ in Ioi 0, exp (-(t : ℂ)) * (t : ℂ) ^ (b - 1) * regularizedHGFun {a} {b} t *
        regularizedHGFun (∅ : Multiset ℂ) {ν + 1} (-(r : ℂ) * t) =
      (r : ℂ) ^ (-a) * exp (-(r : ℂ)) * regularizedHGFun {ν - b + 1} {ν - a + 1} r := by
  set c := b - a with hc
  have hbc : b - c = a := by rw [hc]; ring
  have hc0 : 0 < c.re := hba
  have hb0 : 0 < b.re := by
    have : b.re = c.re + a.re := by simp [hc]
    linarith
  set p := ν.re / 2 + 1 / 4 with hp
  have hap : a.re < p := by rw [hp]; linarith
  set F : ℝ → ℂ := fun t => regularizedHGFun (∅ : Multiset ℂ) {ν + 1} (-(r : ℂ) * t) with hF
  have hFc : Continuous F := confLP_continuous_0F1 ν r
  obtain ⟨KF, hKF⟩ := confLP_exists_norm_0F1_le ν hr
  set P : ℝ → ℂ := fun t => (t : ℂ) ^ (b - 1) * F t with hP
  set E : ℝ → ℝ → ℂ := fun t s => kumDec_eulerKernel c b t s with hE
  set G : ℝ → ℝ → ℂ := fun t s => P t * E t s with hG
  have hstep1 : ∀ t : ℝ, exp (-(t : ℂ)) * (t : ℂ) ^ (b - 1) * regularizedHGFun {a} {b} t *
      F t = P t * regularizedHGFun {c} {b} (-(t : ℂ)) := by
    intro t
    rw [regularizedConfluent_kummer_transform a b (t : ℂ)]
    have he : exp (-(t : ℂ)) * exp (t : ℂ) = 1 := by
      rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
    simp only [hP]
    linear_combination ((t : ℂ) ^ (b - 1) * regularizedHGFun {c} {b} (-(t : ℂ)) * F t) * he
  have hGa := Gamma_ne_zero_of_re_pos ha
  have hGc := Gamma_ne_zero_of_re_pos hc0
  have hGb := Gamma_ne_zero_of_re_pos hb0
  have hGνb := Gamma_ne_zero_of_re_pos hνb
  have hts : ∀ t : ℝ, ∫ s in Ioo 0 1, G t s =
      P t * (Gamma c * Gamma a * regularizedHGFun {c} {b} (-(t : ℂ))) := by
    intro t
    have h := kumDec_regularizedHGFun_neg_eq (a := c) (b := b) hc0 (by rw [hbc]; exact ha) t
    rw [hbc] at h
    simp only [hG]
    rw [integral_const_mul, h, intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo]
    field_simp
    rfl
  -- Fubini 1
  have hEm : Measurable (Function.uncurry E) := by
    simp only [hE, kumDec_eulerKernel]
    fun_prop
  have hPm : Measurable P := by
    simp only [hP]
    exact (by fun_prop : Measurable fun t : ℝ => (t : ℂ) ^ (b - 1)).mul hFc.measurable
  have hm1 : AEStronglyMeasurable (Function.uncurry G)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioo (0:ℝ) 1))) :=
    ((hPm.comp measurable_fst).mul hEm).aestronglyMeasurable
  set γ := c.re with hγ
  set α := a.re with hα
  set β := b.re with hβ
  have hβγα : β = γ + α := by simp [hβ, hγ, hα, hc]
  have hGi : Integrable (Function.uncurry G)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioo (0:ℝ) 1))) := by
    refine (integrable_prod_iff hm1).mpr ⟨Eventually.of_forall fun t => ?_, ?_⟩
    · have h := kumDec_intervalIntegrable_eulerKernel (a := c) (b := b) hc0
        (by rw [hbc]; exact ha) t
      exact ((intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp h).const_mul (P t)
    · have hI := integrableOn_cpow_mul_regularizedHGFun_neg_mul (a := (γ : ℂ)) (b := (β : ℂ))
        (c := (β : ℂ)) (h := F) (K := KF) (r := p) hFc.continuousOn hKF (by simpa using hb0)
        (by simp only [ofReal_re]; linarith)
      refine IntegrableOn.congr_fun (hI.norm.const_mul ‖Gamma (γ : ℂ) * Gamma (α : ℂ)‖) (fun t ht => ?_)
        measurableSet_Ioi
      have ht0 : (0:ℝ) < t := ht
      simp only [Function.uncurry_apply_pair]
      have hn : ∀ s ∈ Ioo (0:ℝ) 1, ‖G t s‖ = ‖P t‖ * ‖kumDec_eulerKernel (γ : ℂ) (β : ℂ) t s‖ := by
        intro s hs
        simp only [hG, hE, norm_mul]
        rw [kumDec_norm_eulerKernel c b hs, kumDec_norm_eulerKernel (γ : ℂ) (β : ℂ) hs, hbc]
        simp only [sub_re, ofReal_re]
        rw [show β - γ = α by rw [hβγα]; ring]
      rw [setIntegral_congr_fun measurableSet_Ioo hn, integral_const_mul,
        confLP_setIntegral_norm_of_ofReal measurableSet_Ioo
          (fun s hs => confLP_eulerKernel_ofReal γ β t hs) (fun s hs => by
            have := hs.1; have := hs.2
            exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (by linarith) _))
              (Real.rpow_nonneg (by linarith) _))]
      have hR := kumDec_regularizedHGFun_neg_eq (a := (γ : ℂ)) (b := (β : ℂ)) (by simpa using hc0)
        (by simp only [sub_re, ofReal_re]; linarith) t
      rw [show (β : ℂ) - γ = (α : ℂ) by rw [hβγα]; push_cast; ring] at hR
      have hGγ : Gamma (γ : ℂ) * Gamma (α : ℂ) ≠ 0 :=
        mul_ne_zero (Gamma_ne_zero_of_re_pos (by simpa using hc0))
          (Gamma_ne_zero_of_re_pos (by simpa using ha))
      have hint : ∫ s in Ioo (0:ℝ) 1, kumDec_eulerKernel (γ : ℂ) (β : ℂ) t s =
          Gamma (γ : ℂ) * Gamma (α : ℂ) * regularizedHGFun {(γ : ℂ)} {(β : ℂ)} (-(t : ℂ)) := by
        rw [hR, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo,
          ← mul_assoc, mul_one_div_cancel hGγ, one_mul]
      rw [hint, norm_mul, norm_mul, norm_mul, norm_mul]
      simp only [norm_mul]
      rw [kumDec_norm_cpow_ofReal ht0, kumDec_norm_cpow_ofReal ht0]
      simp only [sub_re, ofReal_re, one_re]
      ring
  have hst : ∀ s ∈ Ioo (0:ℝ) 1, ∫ t in Ioi 0, G t s =
      (s : ℂ) ^ (c - 1) * (1 - (s : ℂ)) ^ (a - 1) *
        (Gamma b * (s : ℂ) ^ (-b) * regularizedHGFun {b} {ν + 1} (-(r : ℂ) / s)) := by
    intro s hs
    have h := confLP_laplace_0F1 (β := b) (c := ν + 1) (x := (r : ℂ)) hb0 hs.1
    rw [← h, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [hG, hE, kumDec_eulerKernel]
    rw [hbc, show -(t : ℂ) * s = -(s * t : ℂ) by ring]
    ring
  set Q := confLP_Q c a b ν r with hQ
  have hsQ : ∀ s : ℝ, (s : ℂ) ^ (c - 1) * (1 - (s : ℂ)) ^ (a - 1) *
      (Gamma b * (s : ℂ) ^ (-b) * regularizedHGFun {b} {ν + 1} (-(r : ℂ) / s)) =
      (Gamma (ν + 1 - b))⁻¹ * ∫ ρ in Ioo (0:ℝ) 1, Q s ρ := by
    intro s
    rw [regularized_euler_integral hb0 hνb, intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo, ← integral_const_mul, ← integral_const_mul,
      ← integral_const_mul, ← integral_const_mul]
    congr 1
    funext ρ
    simp only [hQ, confLP_Q]
    rw [show ν + 1 - b - 1 = ν - b by ring]
    field_simp
  have hQm := confLP_measurable_Q c a b ν r
  set ν' := ν.re with hν'
  have hcpow : ∀ {z : ℂ} (w : ℂ), z ≠ 0 → z ^ w ≠ 0 := fun w hz => by
    rw [cpow_def_of_ne_zero hz]; exact exp_ne_zero _
  have hQi : Integrable (Function.uncurry Q)
      ((volume.restrict (Ioo (0:ℝ) 1)).prod (volume.restrict (Ioo (0:ℝ) 1))) := by
    have hnQ : ∀ ρ ∈ Ioo (0:ℝ) 1, ∀ s ∈ Ioo (0:ℝ) 1,
        ‖Q s ρ‖ = ‖confLP_Q (γ:ℂ) (α:ℂ) (β:ℂ) (ν':ℂ) r s ρ‖ := by
      intro ρ hρ s hs
      rw [hQ, confLP_norm_Q _ _ _ _ _ hs hρ, confLP_norm_Q _ _ _ _ _ hs hρ]
      simp only [ofReal_re]
      rfl
    have hRint : ∀ ρ ∈ Ioo (0:ℝ) 1, ∫ s in Ioo (0:ℝ) 1, confLP_Q (γ:ℂ) (α:ℂ) (β:ℂ) (ν':ℂ) r s ρ =
        (ρ : ℂ) ^ ((β:ℂ) - 1) * (1 - (ρ : ℂ)) ^ ((ν':ℂ) - β) *
          (exp (-((r : ℂ) * ρ)) * (Gamma (α:ℂ) * ((r : ℂ) * ρ) ^ (-(α:ℂ)))) := fun ρ hρ =>
      confLP_integral_Q hr (by rw [hβγα]; push_cast; ring) (by simpa using ha) hρ
    have hRnorm : ∀ ρ ∈ Ioo (0:ℝ) 1, ∫ s in Ioo (0:ℝ) 1, ‖Q s ρ‖ =
        ‖∫ s in Ioo (0:ℝ) 1, confLP_Q (γ:ℂ) (α:ℂ) (β:ℂ) (ν':ℂ) r s ρ‖ := by
      intro ρ hρ
      rw [setIntegral_congr_fun measurableSet_Ioo (hnQ ρ hρ)]
      refine confLP_setIntegral_norm_of_ofReal measurableSet_Ioo
        (fun s hs => confLP_Q_ofReal γ α β ν' r hs hρ) (fun s hs => ?_)
      have := hs.1; have := hs.2; have := hρ.1; have := hρ.2
      positivity
    refine (integrable_prod_iff' hQm.aestronglyMeasurable).mpr ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with ρ hρ
      have hρc : (ρ:ℂ) ≠ 0 := ofReal_ne_zero.mpr hρ.1.ne'
      have h1ρ : (1 - (ρ:ℂ)) ≠ 0 := by
        rw [sub_ne_zero]; intro h; have := congrArg re h; simp at this; linarith [hρ.2]
      have hrρ : (r:ℂ) * ρ ≠ 0 := mul_ne_zero (ofReal_ne_zero.mpr hr.ne') hρc
      have hne : ∫ s in Ioo (0:ℝ) 1, confLP_Q (γ:ℂ) (α:ℂ) (β:ℂ) (ν':ℂ) r s ρ ≠ 0 := by
        rw [hRint ρ hρ]
        exact mul_ne_zero (mul_ne_zero (hcpow _ hρc) (hcpow _ h1ρ)) (mul_ne_zero (exp_ne_zero _)
          (mul_ne_zero (Gamma_ne_zero_of_re_pos (by simpa using ha)) (hcpow _ hrρ)))
      have hint := confLP_integrableOn_of_ne_zero hne
      refine hint.norm.mono' ((hQm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      exact (hnQ ρ hρ s hs).le
    · have hB := Complex.betaIntegral_convergent (u := ((γ : ℝ) : ℂ))
        (v := ((ν' - β + 1 : ℝ) : ℂ)) (by simpa using hc0) (by
          simp only [ofReal_re]
          have : (ν + 1 - b).re = ν' - β + 1 := by simp [hν', hβ]; ring
          linarith)
      have hB' := (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp hB.norm
      refine (hB'.const_mul (‖Gamma (α:ℂ)‖ * r ^ (-α))).mono'
        hQm.aestronglyMeasurable.norm.prod_swap.integral_prod_right' ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with ρ hρ
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      simp only [Function.uncurry_apply_pair]
      rw [hRnorm ρ hρ, hRint ρ hρ]
      have h1 : (1 : ℂ) - ρ = ((1 - ρ : ℝ) : ℂ) := by push_cast; ring
      have hrρ : (r : ℂ) * ρ = ((r * ρ : ℝ) : ℂ) := by push_cast; ring
      have h1ρ : (0:ℝ) < 1 - ρ := by linarith [hρ.2]
      rw [h1, hrρ]
      simp only [norm_mul, kumDec_norm_cpow_ofReal hρ.1, kumDec_norm_cpow_ofReal h1ρ,
        kumDec_norm_cpow_ofReal (mul_pos hr hρ.1), Complex.norm_exp]
      simp only [sub_re, ofReal_re, one_re, neg_re]
      rw [show ν' - β + 1 - 1 = ν' - β by ring, Real.mul_rpow hr.le hρ.1.le]
      have he : Real.exp (-(r * ρ)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hρ.1])
      have hpow : ρ ^ (β - 1) * ρ ^ (-α) = ρ ^ (γ - 1) := by
        rw [← Real.rpow_add hρ.1, hβγα]; ring_nf
      have hρn : (0:ℝ) ≤ ρ ^ (γ - 1) * (1 - ρ) ^ (ν' - β) := by
        have := hρ.1; positivity
      calc ρ ^ (β - 1) * (1 - ρ) ^ (ν' - β) * (Real.exp (-(r * ρ)) *
            (‖Gamma (α:ℂ)‖ * (r ^ (-α) * ρ ^ (-α))))
          = (‖Gamma (α:ℂ)‖ * r ^ (-α)) * (ρ ^ (γ - 1) * (1 - ρ) ^ (ν' - β)) *
              Real.exp (-(r * ρ)) := by rw [← hpow]; ring
        _ ≤ (‖Gamma (α:ℂ)‖ * r ^ (-α)) * (ρ ^ (γ - 1) * (1 - ρ) ^ (ν' - β)) * 1 := by
            gcongr
        _ = _ := mul_one _
  have hcab : c + a = b := by rw [hc]; ring
  have hνac : 0 < (ν + 1 - a - c).re := by
    rw [show ν + 1 - a - c = ν + 1 - b by rw [hc]; ring]; exact hνb
  have hV : ∫ ρ in Ioo (0:ℝ) 1, (ρ : ℂ) ^ (b - 1) * (1 - (ρ : ℂ)) ^ (ν - b) *
        (exp (-((r : ℂ) * ρ)) * (Gamma a * ((r : ℂ) * ρ) ^ (-a))) =
      Gamma a * (r : ℂ) ^ (-a) * (Gamma c * Gamma (ν + 1 - b) *
        regularizedHGFun {c} {ν + 1 - a} (-(r : ℂ))) := by
    have hE2 := regularized_euler_integral (a := c) (b := ν + 1 - a) (z := -(r : ℂ)) hc0 hνac
    rw [show ν + 1 - a - c = ν + 1 - b by rw [hc]; ring, intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo] at hE2
    rw [hE2, ← mul_assoc (Gamma c * Gamma (ν + 1 - b)), mul_one_div_cancel (mul_ne_zero hGc hGνb),
      one_mul, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioo fun ρ hρ => ?_
    have hρc : (ρ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hρ.1.ne'
    rw [mul_cpow_ofReal_nonneg hr.le hρ.1.le,
      show ν + 1 - b - 1 = ν - b by ring]
    have hp : (ρ : ℂ) ^ (b - 1) * (ρ : ℂ) ^ (-a) = (ρ : ℂ) ^ (c - 1) := by
      rw [← cpow_add _ _ hρc]; congr 1; rw [hc]; ring
    rw [show -(r : ℂ) * ρ = -((r : ℂ) * ρ) by ring]
    linear_combination (Gamma a * (r : ℂ) ^ (-a) * exp (-((r : ℂ) * ρ)) *
      (1 - (ρ : ℂ)) ^ (ν - b)) * hp
  calc ∫ t : ℝ in Ioi 0, exp (-(t : ℂ)) * (t : ℂ) ^ (b - 1) * regularizedHGFun {a} {b} t * F t
      = ∫ t : ℝ in Ioi 0, (Gamma c * Gamma a)⁻¹ * ∫ s in Ioo 0 1, G t s := by
        refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
        rw [hstep1 t, hts t]
        field_simp
    _ = (Gamma c * Gamma a)⁻¹ * ∫ s in Ioo 0 1, ∫ t in Ioi 0, G t s := by
        rw [integral_const_mul, integral_integral_swap hGi]
    _ = (Gamma c * Gamma a)⁻¹ * ∫ s in Ioo (0:ℝ) 1,
          (Gamma (ν + 1 - b))⁻¹ * ∫ ρ in Ioo (0:ℝ) 1, Q s ρ := by
        rw [setIntegral_congr_fun measurableSet_Ioo fun s hs => (hst s hs).trans (hsQ s)]
    _ = (Gamma c * Gamma a)⁻¹ * ((Gamma (ν + 1 - b))⁻¹ *
          ∫ ρ in Ioo (0:ℝ) 1, ∫ s in Ioo (0:ℝ) 1, Q s ρ) := by
        rw [integral_const_mul, integral_integral_swap hQi]
    _ = (Gamma c * Gamma a)⁻¹ * ((Gamma (ν + 1 - b))⁻¹ *
          (Gamma a * (r : ℂ) ^ (-a) * (Gamma c * Gamma (ν + 1 - b) *
            regularizedHGFun {c} {ν + 1 - a} (-(r : ℂ))))) := by
        rw [← hV]
        congr 2
        exact setIntegral_congr_fun measurableSet_Ioo fun ρ hρ => confLP_integral_Q hr hcab ha hρ
    _ = _ := by
        rw [regularizedConfluent_kummer_transform c (ν + 1 - a) (-(r : ℂ)), neg_neg,
          show ν + 1 - a - c = ν - b + 1 by rw [hc]; ring, show ν + 1 - a = ν - a + 1 by ring]
        field_simp


/-- 13.10.13 (in `₀F₁` form) for `0 < re b < re ν + 1`, `re ν > -1/2`, by analytic continuation
in `a` from the Euler region. -/
theorem confLP_of_strip {a b ν : ℂ} {r : ℝ} (hr : 0 < r) (hb : 0 < b.re)
    (hbν : 0 < (ν + 1 - b).re) (hν0 : -1 / 2 < ν.re) (hν : 2 * a.re < ν.re + 1 / 2) :
    ∫ t : ℝ in Ioi 0, exp (-(t : ℂ)) * (t : ℂ) ^ (b - 1) * regularizedHGFun {a} {b} t *
        regularizedHGFun (∅ : Multiset ℂ) {ν + 1} (-(r : ℂ) * t) =
      (r : ℂ) ^ (-a) * exp (-(r : ℂ)) * regularizedHGFun {ν - b + 1} {ν - a + 1} r := by
  set p := ν.re / 2 + 1 / 4 with hp
  set F : ℝ → ℂ := fun t => regularizedHGFun (∅ : Multiset ℂ) {ν + 1} (-(r : ℂ) * t) with hF
  have hFc : Continuous F := confLP_continuous_0F1 ν r
  obtain ⟨KF, hKF⟩ := confLP_exists_norm_0F1_le ν hr
  have hKF0 : 0 ≤ KF := by
    have h := (norm_nonneg _).trans (hKF 1 one_pos)
    exact (mul_nonneg_iff_of_pos_right (by positivity)).mp h
  set Φ : ℂ → ℝ → ℂ := fun w t => (t : ℂ) ^ (b - 1) * regularizedHGFun {b - w} {b} (-(t : ℂ)) * F t
    with hΦ
  have hΨ : ∀ w : ℂ, ∫ t : ℝ in Ioi 0, exp (-(t : ℂ)) * (t : ℂ) ^ (b - 1) *
      regularizedHGFun {w} {b} t * F t = ∫ t : ℝ in Ioi 0, Φ w t := by
    intro w
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [regularizedConfluent_kummer_transform w b (t : ℂ)]
    have he : exp (-(t : ℂ)) * exp (t : ℂ) = 1 := by
      rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
    simp only [hΦ]
    linear_combination ((t : ℂ) ^ (b - 1) * regularizedHGFun {b - w} {b} (-(t : ℂ)) * F t) * he
  set U : Set ℂ := {w : ℂ | w.re < p} with hU
  have hUo : IsOpen U := isOpen_lt continuous_re continuous_const
  have hpre : IsPreconnected U := (convex_halfSpace_re_lt p).isPreconnected
  have hFd : DifferentiableOn ℂ (fun w => ∫ t : ℝ in Ioi 0, Φ w t) U := by
    refine Complex.differentiableOn_integral_Ioi_of_locally_dominated hUo 0 ?_ ?_ ?_
    · intro w _
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      exact ((ContinuousOn.cpow continuous_ofReal.continuousOn continuousOn_const
        fun t ht => ofReal_mem_slitPlane.mpr ht).mul
        (kumDec_continuous_neg (b - w) b).continuousOn).mul hFc.continuousOn
    · refine Eventually.of_forall fun t => ?_
      exact (((differentiable_regularizedConfluent_comp (A := fun w => b - w) (B := fun _ => b)
        (differentiable_const b |>.sub differentiable_id) (differentiable_const b)
        (-(t : ℂ))).const_mul ((t : ℂ) ^ (b - 1))).mul_const (F t)).differentiableOn
    · intro w₀ hw₀
      have hw₀' : w₀.re < p := hw₀
      set ε := (p - w₀.re) / 2 with hε
      have hε0 : 0 < ε := by rw [hε]; linarith
      obtain ⟨C, hC⟩ := exists_eventually_norm_regularizedHGFun_neg_le (b - w₀) b hε0
      have htend : Tendsto (fun w : ℂ => (b - w, b)) (𝓝 w₀) (𝓝 (b - w₀, b)) :=
        ((continuous_const.sub continuous_id).prodMk continuous_const).tendsto w₀
      refine ⟨_, htend.eventually hC, fun t => t ^ (b.re - 1) * (C * (1 + t) ^ (-(b - w₀).re + ε)) *
        (KF * (1 + t) ^ (-p)), ?_, ?_⟩
      · have hI := DLMF.Gamma.integrableOn_rpow_mul_one_add_rpow (σ := b.re)
          (α := p + (b - w₀).re - ε) hb (by simp only [sub_re]; rw [hε]; linarith)
        refine IntegrableOn.congr_fun (Integrable.const_mul hI (C * KF)) (fun t ht => ?_)
          measurableSet_Ioi
        have ht0 : (0:ℝ) < t := ht
        have e : (1 + t) ^ (-(b - w₀).re + ε) * (1 + t) ^ (-p) =
            (1 + t) ^ (-(p + (b - w₀).re - ε)) := by
          rw [← Real.rpow_add (by linarith)]; ring_nf
        rw [← e]
        ring
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        intro y hy
        have ht0 : (0:ℝ) < t := ht
        simp only [hΦ, norm_mul]
        rw [kumDec_norm_cpow_ofReal ht0]
        simp only [sub_re, one_re]
        refine mul_le_mul (mul_le_mul_of_nonneg_left (hy t ht0.le) (by positivity))
          (hKF t ht0) (norm_nonneg _) (by
            have := hy t ht0.le
            have h0 : 0 ≤ C * (1 + t) ^ (-(b - w₀).re + ε) := (norm_nonneg _).trans this
            exact mul_nonneg (by positivity) h0)
  set H : ℂ → ℂ := fun w => (r : ℂ) ^ (-w) * exp (-(r : ℂ)) *
    regularizedHGFun {ν - b + 1} {ν - w + 1} r with hH
  have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
  have hHd : Differentiable ℂ H := by
    refine ((differentiable_neg.const_cpow (Or.inl hr0)).mul_const _).mul ?_
    exact differentiable_regularizedConfluent_comp (A := fun _ => ν - b + 1)
      (B := fun w => ν - w + 1) (differentiable_const _)
      ((differentiable_const ν |>.sub differentiable_id).add_const 1) (r : ℂ)
  set m := min b.re p / 2 with hm
  have hp0 : 0 < p := by rw [hp]; linarith
  have hm0 : 0 < m := by rw [hm]; exact half_pos (lt_min hb hp0)
  have hmb : m < b.re := by rw [hm]; linarith [min_le_left b.re p]
  have hmp : m < p := by rw [hm]; linarith [min_le_right b.re p]
  have hmU : (m : ℂ) ∈ U := by show (m : ℂ).re < p; simpa using hmp
  have heq : Set.EqOn (fun w => ∫ t : ℝ in Ioi 0, Φ w t) H U := by
    refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (hFd.analyticOnNhd hUo)
      (fun z _ => hHd.analyticAt z) hpre hmU ?_
    have hopen : IsOpen {w : ℂ | 0 < w.re ∧ w.re < b.re ∧ w.re < p} :=
      (isOpen_lt continuous_const continuous_re).and
        ((isOpen_lt continuous_re continuous_const).and (isOpen_lt continuous_re continuous_const))
    filter_upwards [hopen.mem_nhds (show (m : ℂ) ∈ _ by
      simp only [Set.mem_ofPred_eq, ofReal_re]; exact ⟨hm0, hmb, hmp⟩)] with w hw
    rw [← hΨ w]
    exact confLP_base hr hw.1 (by simp only [sub_re]; linarith [hw.2.1]) hbν
      (by rw [hp] at hw; linarith [hw.2.2])
  have hfin := heq (show a ∈ U by show a.re < p; rw [hp]; linarith)
  rw [hΨ a]
  exact hfin


/-- `1/Γ(s) = s/Γ(s+1)` for every `s` (with `1/Γ = 0` at the poles). -/
theorem confLP_recip_Gamma_eq (s : ℂ) : (Gamma s)⁻¹ = s * (Gamma (s + 1))⁻¹ := by
  rcases eq_or_ne s 0 with rfl | hs
  · simp
  · rw [Complex.Gamma_add_one s hs, mul_inv, ← mul_assoc, mul_inv_cancel₀ hs, one_mul]

/-- The contiguous relation `𝐌(a,b,z) = (b-a) 𝐌(a,b+1,z) + a 𝐌(a+1,b+1,z)`, for all
parameters. -/
theorem confLP_contiguous_b (a b z : ℂ) :
    regularizedHGFun {a} {b} z =
      (b - a) * regularizedHGFun {a} {b + 1} z + a * regularizedHGFun {a + 1} {b + 1} z := by
  rw [regularizedConfluent_eq_tsum, regularizedConfluent_eq_tsum, regularizedConfluent_eq_tsum,
    ← tsum_mul_left, ← tsum_mul_left,
    ← ((summable_regularizedConfluent_term a (b + 1) z).mul_left (b - a)).tsum_add
      ((summable_regularizedConfluent_term (a + 1) (b + 1) z).mul_left a)]
  refine tsum_congr fun n => ?_
  have hp : a * poch (a + 1) n = poch a n * (a + n) := by
    rw [← poch_succ_left, poch_succ]
  rw [confLP_recip_Gamma_eq (b + n), show b + n + 1 = b + 1 + n by ring]
  linear_combination (-(z ^ n / n.factorial * (Gamma (b + 1 + n))⁻¹)) * hp

/-- The contiguous relation `𝐌(A-1,B-1,x) = (B-1) 𝐌(A,B,x) - (B-A) x 𝐌(A,B+1,x)`, for all
parameters. -/
theorem confLP_contiguous_down (A B x : ℂ) :
    regularizedHGFun {A - 1} {B - 1} x =
      (B - 1) * regularizedHGFun {A} {B} x - (B - A) * x * regularizedHGFun {A} {B + 1} x := by
  set T : ℂ → ℂ → ℕ → ℂ := fun a b n => poch a n * x ^ n / n.factorial * (Gamma (b + n))⁻¹
    with hT
  have hS : ∀ a b, HasSum (T a b) (regularizedHGFun {a} {b} x) := fun a b => by
    rw [regularizedConfluent_eq_tsum]
    exact (summable_regularizedConfluent_term a b x).hasSum
  set u : ℕ → ℂ := fun n => T (A - 1) (B - 1) n - (B - 1) * T A B n with hu
  have hU : HasSum u (regularizedHGFun {A - 1} {B - 1} x - (B - 1) * regularizedHGFun {A} {B} x) :=
    (hS _ _).sub ((hS A B).mul_left _)
  have hu0 : u 0 = 0 := by
    simp only [hu, hT, poch_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_mul,
      CharP.cast_eq_zero, add_zero]
    rw [confLP_recip_Gamma_eq (B - 1), sub_add_cancel]
    ring
  have husucc : ∀ n : ℕ, u (n + 1) = -(B - A) * x * T A (B + 1) n := by
    intro n
    simp only [hu, hT]
    have hp1 : poch (A - 1) (n + 1) = (A - 1) * poch A n := by
      rw [poch_succ_left, sub_add_cancel]
    rw [hp1, poch_succ, Nat.factorial_succ, pow_succ]
    push_cast
    rw [show B - 1 + ((n : ℂ) + 1) = B + n by ring, confLP_recip_Gamma_eq (B + n),
      show B + (n : ℂ) + 1 = B + 1 + n by ring, show B + ((n : ℂ) + 1) = B + 1 + n by ring]
    have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    have hn : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast n.succ_ne_zero
    field_simp
    ring
  have hU' : HasSum (fun n => u (n + 1)) (-(B - A) * x * regularizedHGFun {A} {B + 1} x) := by
    simp_rw [husucc]
    exact (hS A (B + 1)).mul_left _
  have h2 := (hasSum_nat_add_iff' 1).mpr hU
  simp only [Finset.range_one, Finset.sum_singleton, hu0, sub_zero] at h2
  have := h2.unique hU'
  linear_combination this


/-- The integral of 13.10.13 in `₀F₁` form. -/
def confLP_Psi (a b ν : ℂ) (r : ℝ) : ℂ :=
  ∫ t : ℝ in Ioi 0, exp (-(t : ℂ)) * (t : ℂ) ^ (b - 1) * regularizedHGFun {a} {b} t *
    regularizedHGFun (∅ : Multiset ℂ) {ν + 1} (-(r : ℂ) * t)

/-- The right side of 13.10.13 in `₀F₁` form. -/
def confLP_R (a b ν : ℂ) (r : ℝ) : ℂ :=
  (r : ℂ) ^ (-a) * exp (-(r : ℂ)) * regularizedHGFun {ν - b + 1} {ν - a + 1} r

/-- The order recurrence of the 13.10.13 integrals, from the `₀F₁` and Kummer contiguous
relations. -/
theorem confLP_Psi_rec {a b ν : ℂ} {r : ℝ} (hr : 0 < r) (hb : 0 < b.re)
    (hν : 2 * a.re < ν.re + 1 / 2) :
    confLP_Psi a b ν r = (ν + 1) * confLP_Psi a b (ν + 1) r -
      r * (b - a) * confLP_Psi a (b + 1) (ν + 2) r - r * a * confLP_Psi (a + 1) (b + 1) (ν + 2) r := by
  have h1 := confLP_integrableOn (a := a) (b := b) (ν := ν + 1) hr hb (by simp; linarith)
  have h2 := confLP_integrableOn (a := a) (b := b + 1) (ν := ν + 2) hr (by simp; linarith)
    (by simp; linarith)
  have h3 := confLP_integrableOn (a := a + 1) (b := b + 1) (ν := ν + 2) hr (by simp; linarith)
    (by simp; linarith)
  simp only [confLP_Psi]
  set f1 := fun t : ℝ => exp (-(t : ℂ)) * (t : ℂ) ^ (b - 1) * regularizedHGFun {a} {b} t *
    regularizedHGFun (∅ : Multiset ℂ) {ν + 1 + 1} (-(r : ℂ) * t) with hf1
  set f2 := fun t : ℝ => exp (-(t : ℂ)) * (t : ℂ) ^ (b + 1 - 1) * regularizedHGFun {a} {b + 1} t *
    regularizedHGFun (∅ : Multiset ℂ) {ν + 2 + 1} (-(r : ℂ) * t) with hf2
  set f3 := fun t : ℝ => exp (-(t : ℂ)) * (t : ℂ) ^ (b + 1 - 1) *
    regularizedHGFun {a + 1} {b + 1} t *
    regularizedHGFun (∅ : Multiset ℂ) {ν + 2 + 1} (-(r : ℂ) * t) with hf3
  have e : ∫ t in Ioi (0:ℝ), ((ν + 1) * f1 t - r * (b - a) * f2 t - r * a * f3 t) =
      (ν + 1) * (∫ t in Ioi (0:ℝ), f1 t) - r * (b - a) * (∫ t in Ioi (0:ℝ), f2 t) -
        r * a * (∫ t in Ioi (0:ℝ), f3 t) := by
    rw [integral_sub (f := fun t => (ν + 1) * f1 t - r * (b - a) * f2 t)
        (g := fun t => r * a * f3 t) ((h1.const_mul _).sub (h2.const_mul _)) (h3.const_mul _),
      integral_sub (f := fun t => (ν + 1) * f1 t) (g := fun t => r * (b - a) * f2 t)
        (h1.const_mul _) (h2.const_mul _), integral_const_mul, integral_const_mul,
      integral_const_mul]
  rw [← e]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : (0:ℝ) < t := ht
  have htc : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht0.ne'
  simp only [hf1, hf2, hf3]
  have hF := regularized0F1_contiguous (ν + 1) (-(r : ℂ) * t)
  have hM := confLP_contiguous_b a b (t : ℂ)
  have hp : (t : ℂ) ^ (b + 1 - 1) = (t : ℂ) * (t : ℂ) ^ (b - 1) := by
    rw [show b + 1 - 1 = (b - 1) + 1 by ring, cpow_add _ _ htc, cpow_one]; ring
  rw [hp]
  rw [show ν + 1 + 1 + 1 = ν + 2 + 1 by ring] at hF
  rw [hF, hM]
  ring

/-- The right sides satisfy the same recurrence. -/
theorem confLP_R_rec (a b ν : ℂ) {r : ℝ} (hr : 0 < r) :
    confLP_R a b ν r = (ν + 1) * confLP_R a b (ν + 1) r -
      r * (b - a) * confLP_R a (b + 1) (ν + 2) r - r * a * confLP_R (a + 1) (b + 1) (ν + 2) r := by
  have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
  simp only [confLP_R]
  have h := confLP_contiguous_down (ν + 1 - b + 1) (ν + 1 - a + 1) (r : ℂ)
  rw [show ν + 1 - b + 1 - 1 = ν - b + 1 by ring, show ν + 1 - a + 1 - 1 = ν - a + 1 by ring,
    show ν + 1 - a + 1 + 1 = ν + 2 - a + 1 by ring] at h
  rw [show ν + 2 - (b + 1) + 1 = ν + 1 - b + 1 by ring, show ν + 2 - (a + 1) + 1 = ν + 1 - a + 1 by ring,
    h]
  have hpow : (r : ℂ) ^ (-(a + 1)) * r = (r : ℂ) ^ (-a) := by
    rw [show -(a + 1) = -a + -1 by ring, cpow_add _ _ hr0, cpow_neg_one, mul_assoc,
      inv_mul_cancel₀ hr0, mul_one]
  linear_combination (a * exp (-(r : ℂ)) * regularizedHGFun {ν + 1 - b + 1} {ν + 1 - a + 1} r) * hpow

/-- 13.10.13 in `₀F₁` form for all admissible parameters. -/
theorem confLP_Psi_eq_R : ∀ n : ℕ, ∀ a b ν : ℂ, ∀ {r : ℝ}, 0 < r → 0 < b.re →
    -1 / 2 < ν.re + n → b.re < ν.re + 1 + n → 2 * a.re < ν.re + 1 / 2 →
    confLP_Psi a b ν r = confLP_R a b ν r := by
  intro n
  induction n with
  | zero =>
    intro a b ν r hr hb h1 h2 hν
    simp only [CharP.cast_eq_zero, add_zero] at h1 h2
    exact confLP_of_strip hr hb (by simp; linarith) h1 hν
  | succ n ih =>
    intro a b ν r hr hb h1 h2 hν
    push_cast at h1 h2
    rw [confLP_Psi_rec hr hb hν, confLP_R_rec a b ν hr,
      ih a b (ν + 1) hr hb (by simp; linarith) (by simp; linarith) (by simp; linarith),
      ih a (b + 1) (ν + 2) hr (by simp; linarith) (by simp; linarith) (by simp; linarith)
        (by simp; linarith),
      ih (a + 1) (b + 1) (ν + 2) hr (by simp; linarith) (by simp; linarith) (by simp; linarith)
        (by simp; linarith)]


end LargeParamBessel

/-- A Hankel-type transform of `𝐌`, for real `x > 0`. For non-real `x` the Bessel kernel grows like
`exp (c √t)`; the parameter bound makes the integrand absolutely integrable, as required for
Lean's integral. -/
@[dlmf 13.10.E13]
theorem bessel_regularizedHGFun {a b ν x : ℂ} (hx : 0 < x.re) (hxi : x.im = 0)
    (hb : 0 < b.re) (hν : 2 * a.re < ν.re + 1 / 2) :
    ∫ t : ℝ in Set.Ioi 0,
        exp (-(t : ℂ)) * (t : ℂ) ^ (b - 1 - ν / 2) * regularizedHGFun {a} {b} t *
          besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) =
      x ^ (-a + ν / 2) * exp (-x) * regularizedHGFun {ν - b + 1} {ν - a + 1} x := by
  set r := x.re with hr
  have hxr : x = (r : ℂ) := Complex.ext (by simp [hr]) (by simp [hxi])
  have hx0 : x ≠ 0 := by rw [hxr]; exact ofReal_ne_zero.mpr hx.ne'
  obtain ⟨n, hn⟩ := exists_nat_gt (max (-1 / 2 - ν.re) (b.re - ν.re - 1))
  have hm1 := le_max_left (-1 / 2 - ν.re) (b.re - ν.re - 1)
  have hm2 := le_max_right (-1 / 2 - ν.re) (b.re - ν.re - 1)
  have hP := confLP_Psi_eq_R n a b ν hx hb (by linarith) (by linarith) hν
  simp only [confLP_Psi, confLP_R] at hP
  rw [← hxr] at hP
  have hpt : ∀ t ∈ Set.Ioi (0:ℝ), exp (-(t : ℂ)) * (t : ℂ) ^ (b - 1 - ν / 2) *
      regularizedHGFun {a} {b} t * besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) =
      x ^ (ν / 2) * (exp (-(t : ℂ)) * (t : ℂ) ^ (b - 1) * regularizedHGFun {a} {b} t *
        regularizedHGFun (∅ : Multiset ℂ) {ν + 1} (-x * t)) := by
    intro t ht
    have ht0 : (0:ℝ) < t := ht
    have htc : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht0.ne'
    have hk := cfInt_kernel_eq ν hx0 ht0
    have hne : (t : ℂ) ^ (ν / 2) ≠ 0 := by
      rw [cpow_def_of_ne_zero htc]; exact exp_ne_zero _
    have e1 : (t : ℂ) ^ (b - 1 - ν / 2) * (t : ℂ) ^ (ν / 2) = (t : ℂ) ^ (b - 1) := by
      rw [← cpow_add _ _ htc]; ring_nf
    have e2 : (t : ℂ) ^ ν = (t : ℂ) ^ (ν / 2) * (t : ℂ) ^ (ν / 2) := by
      rw [← cpow_add _ _ htc]; ring_nf
    apply mul_left_cancel₀ hne
    rw [e2] at hk
    linear_combination (exp (-(t : ℂ)) * (t : ℂ) ^ (b - 1 - ν / 2) *
      regularizedHGFun {a} {b} t) * hk +
      (x ^ (ν / 2) * exp (-(t : ℂ)) * regularizedHGFun {a} {b} t *
        regularizedHGFun (∅ : Multiset ℂ) {ν + 1} (-x * t) * (t : ℂ) ^ (ν / 2)) * e1
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul, hP,
    cpow_add _ _ hx0]
  ring

open Set in
/-- A Hankel-type transform of `𝐌` in terms of U, for real `x > 0`. For non-real `x` the Bessel
kernel grows like `exp (c √t)`; the parameter bound makes the integrand absolutely integrable,
as required for Lean's integral. -/
@[dlmf 13.10.E14]
theorem bessel_regularizedHGFun_U {a b ν x : ℂ} (hx : 0 < x.re) (hxi : x.im = 0)
    (hν0 : -1 < ν.re) (hν1 : ν.re < 2 * (b - a).re - 3 / 2) :
    ∫ t : ℝ in Set.Ioi 0,
        exp (-(t : ℂ)) * (t : ℂ) ^ (ν / 2) * regularizedHGFun {a} {b} t *
          besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) =
      x ^ (ν / 2) * exp (-x) / Gamma (b - a) * kummerU a (a - b + ν + 2) x := by
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx
  set r := x.re with hr
  have hxr : x = (r : ℂ) := Complex.ext (by simp [hr]) (by simp [hxi])
  set c := b - a with hc
  set σ := ν.re with hσ
  set p := σ / 2 + 1 / 4 with hp
  set K : ℝ → ℂ := fun t => (t : ℂ) ^ (ν / 2) * besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) with hK
  have hpt : ∀ t : ℝ, exp (-(t : ℂ)) * (t : ℂ) ^ (ν / 2) * regularizedHGFun {a} {b} t *
      besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) = K t * regularizedHGFun {c} {b} (-(t : ℂ)) := by
    intro t
    rw [regularizedConfluent_kummer_transform a b (t : ℂ)]
    have he : exp (-(t : ℂ)) * exp (t : ℂ) = 1 := by
      rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
    simp only [hK]
    linear_combination ((t : ℂ) ^ (ν / 2) * regularizedHGFun {c} {b} (-(t : ℂ)) *
      besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ))) * he
  rw [setIntegral_congr_fun measurableSet_Ioi fun t _ => hpt t]
  set F : ℂ → ℂ := fun w => ∫ t : ℝ in Ioi 0, K t * regularizedHGFun {c} {w + c} (-(t : ℂ))
    with hF
  set H : ℂ → ℂ := fun w => x ^ (ν / 2) * exp (-x) / Gamma c * kummerU w (ν + 2 - c) x with hH
  have hFH : ∀ w : ℂ, 0 < w.re → F w = H w := by
    intro w hw
    have h := cfInt_bessel_M_euler (a := w) (b := w + c) hx hxi hw hν0
      (by rw [show w + c - w = c by ring]; exact hν1)
    rw [show w + c - w = c by ring, show w - (w + c) + ν + 2 = ν + 2 - c by ring] at h
    exact h
  have hKc : ContinuousOn K (Ioi 0) := cfInt_continuousOn_kernel ν hx0
  obtain ⟨CK, hCK⟩ := cfInt_exists_norm_kernel_le ν hx
  have hKb : ∀ t : ℝ, 0 < t → ‖K t‖ ≤ CK * (t ^ σ * (1 + t) ^ (-p)) := by
    intro t ht
    have := hCK t ht
    simp only [hK]; rw [hxr]; exact this
  have hCK0 : 0 ≤ CK := by
    have h := (norm_nonneg _).trans (hKb 1 one_pos)
    exact (mul_nonneg_iff_of_pos_right (by positivity)).mp h
  have hcre : σ / 2 + 3 / 4 < c.re := by linarith
  set ε := (c.re - σ / 2 - 3 / 4) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hFd : Differentiable ℂ F := by
    refine differentiableOn_univ.mp (Complex.differentiableOn_integral_Ioi_of_locally_dominated
      (Φ := fun w t => K t * regularizedHGFun {c} {w + c} (-(t : ℂ))) isOpen_univ 0 ?_ ?_ ?_)
    · intro w _
      exact (hKc.aestronglyMeasurable measurableSet_Ioi).mul
        (kumDec_continuous_neg c (w + c)).aestronglyMeasurable
    · refine Eventually.of_forall fun t => ?_
      exact ((differentiable_regularizedConfluent_comp (A := fun _ => c) (B := fun w => w + c)
        (differentiable_const c) (differentiable_id.add_const c) (-(t : ℂ))).const_mul
        (K t)).differentiableOn
    · intro w₀ _
      obtain ⟨C, hC⟩ := exists_eventually_norm_regularizedHGFun_neg_le c (w₀ + c) hε0
      have htend : Tendsto (fun w : ℂ => (c, w + c)) (𝓝 w₀) (𝓝 (c, w₀ + c)) :=
        ((continuous_const.prodMk (continuous_id.add continuous_const)).tendsto w₀)
      refine ⟨_, htend.eventually hC, fun t => CK * (t ^ σ * (1 + t) ^ (-p)) *
        (C * (1 + t) ^ (-c.re + ε)), ?_, ?_⟩
      · have hI := DLMF.Gamma.integrableOn_rpow_mul_one_add_rpow (σ := σ + 1)
          (α := p + c.re - ε) (by linarith) (by rw [hp, hε]; linarith)
        refine IntegrableOn.congr_fun (Integrable.const_mul hI (CK * C)) (fun t ht => ?_)
          measurableSet_Ioi
        have ht0 : (0:ℝ) < t := ht
        have e : (1 + t) ^ (-p) * (1 + t) ^ (-c.re + ε) = (1 + t) ^ (-(p + c.re - ε)) := by
          rw [← Real.rpow_add (by linarith)]; ring_nf
        rw [show σ + 1 - 1 = σ by ring, ← e]
        ring
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        intro y hy
        have ht0 : (0:ℝ) < t := ht
        rw [norm_mul]
        exact mul_le_mul (hKb t ht0) (hy t ht0.le) (norm_nonneg _) (by positivity)
  have hHd : Differentiable ℂ H :=
    (cfInt_differentiable_kummerU_fst (ν + 2 - c) hx0).const_mul _
  have heq : F = H := by
    refine AnalyticOnNhd.eq_of_eventuallyEq (fun z _ => hFd.analyticAt z)
      (fun z _ => hHd.analyticAt z) (z₀ := 1) ?_
    have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const continuous_re
    filter_upwards [hopen.mem_nhds (by simp : (0:ℝ) < (1:ℂ).re)] with w hw
    exact hFH w hw
  have h := congrFun heq a
  simp only [hF, hH, show a + c = b by rw [hc]; ring] at h
  rw [h, show ν + 2 - c = a - b + ν + 2 by rw [hc]; ring]

open Set in
/-- A Hankel-type transform of Tricomi U, for real `x > 0`. For non-real `x` the Bessel kernel grows
like `exp (c √t)`; the parameter bound makes the integrand absolutely integrable, as required
for Lean's integral. -/
@[dlmf 13.10.E15]
theorem bessel_kummerU {a b ν x : ℂ} (hx : 0 < x.re) (hxi : x.im = 0)
    (hν0 : (b - 2).re < ν.re) (hν1 : -1 < ν.re) (hν2 : ν.re < 2 * a.re - 3 / 2) :
    ∫ t : ℝ in Set.Ioi 0,
        (t : ℂ) ^ (ν / 2) * kummerU a b t * besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) =
      Gamma (ν - b + 2) / Gamma a * x ^ (ν / 2) * kummerU (ν - b + 2) (ν - a + 2) x := by
  set r := x.re with hr
  have hxr : x = (r : ℂ) := Complex.ext (by simp [hr]) (by simp [hxi])
  have hx0 : x ≠ 0 := by rw [hxr]; exact ofReal_ne_zero.mpr hx.ne'
  set σ := ν.re with hσ
  set α := a.re with hα
  set β := b.re with hβ
  have hb2 : β - 2 < σ := by simpa [hβ] using hν0
  have ha : 0 < α := by linarith
  have hGa : Gamma a ≠ 0 := Gamma_ne_zero_of_re_pos ha
  set K : ℝ → ℂ := fun t => (t : ℂ) ^ (ν / 2) * besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) with hK
  set f : ℝ → ℂ := fun s => (s : ℂ) ^ (a - 1) * (1 + (s : ℂ)) ^ (b - a - 1) with hf
  set G : ℝ → ℝ → ℂ := fun t s => K t * (exp (-(s * t : ℂ)) * f s) with hG
  have hKc : ContinuousOn K (Ioi 0) := cfInt_continuousOn_kernel ν hx0
  have hfc : ContinuousOn f (Ioi 0) := by
    refine ContinuousOn.mul ?_ ?_
    · exact ContinuousOn.cpow continuous_ofReal.continuousOn continuousOn_const
        fun t ht => ofReal_mem_slitPlane.mpr ht
    · refine ContinuousOn.cpow (by fun_prop) continuousOn_const fun t ht => ?_
      rw [show (1 : ℂ) + t = ((1 + t : ℝ) : ℂ) by push_cast; ring]
      exact ofReal_mem_slitPlane.mpr (by linarith [show (0 : ℝ) < t from ht])
  obtain ⟨CK, hCK⟩ := cfInt_exists_norm_kernel_le ν hx
  set p := σ / 2 + 1 / 4 with hp
  obtain ⟨CL, hCL⟩ := cfInt_laplace_rpow_le (r := σ) (p := p) hν1 (by rw [hp]; linarith)
  have hnf : ∀ s : ℝ, 0 < s → ‖f s‖ = s ^ (α - 1) * (1 + s) ^ (β - α - 1) := by
    intro s hs
    rw [hf, norm_mul, kumDec_norm_cpow_ofReal hs,
      show (1 : ℂ) + s = ((1 + s : ℝ) : ℂ) by push_cast; ring, kumDec_norm_cpow_ofReal (by linarith)]
    simp [hα, hβ]
  have hKb : ∀ t : ℝ, 0 < t → ‖K t‖ ≤ CK * (t ^ σ * (1 + t) ^ (-p)) := by
    intro t ht
    have := hCK t ht
    simp only [hK]; rw [hxr]; exact this
  have hCK0 : 0 ≤ CK := by
    have h := (norm_nonneg _).trans (hKb 1 one_pos)
    exact (mul_nonneg_iff_of_pos_right (by positivity)).mp h
  have hm : AEStronglyMeasurable (Function.uncurry G)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) :=
    ((hKc.aestronglyMeasurable measurableSet_Ioi).comp_fst
      (ν := volume.restrict (Ioi (0:ℝ)))).mul
      ((Continuous.aestronglyMeasurable (by fun_prop :
        Continuous fun q : ℝ × ℝ => exp (-((q.2 : ℂ) * q.1)))).mul
        ((hfc.aestronglyMeasurable measurableSet_Ioi).comp_snd))
  have hinner : ∀ s : ℝ, 0 < s → IntegrableOn (fun t => G t s) (Ioi 0) ∧
      ∫ t in Ioi 0, ‖G t s‖ ≤ ‖f s‖ * CK * (CL * (s ^ (p - σ - 1) * (1 + s) ^ (-p))) := by
    intro s hs
    obtain ⟨hI, hle⟩ := hCL s hs
    have hbd : ∀ t ∈ Ioi (0:ℝ), ‖G t s‖ ≤
        ‖f s‖ * CK * (t ^ σ * (1 + t) ^ (-p) * Real.exp (-(s * t))) := by
      intro t ht
      have ht0 : (0:ℝ) < t := ht
      show ‖K t * (exp (-(s * t : ℂ)) * f s)‖ ≤ _
      rw [norm_mul (K t), norm_mul (exp _), Complex.norm_exp]
      have : (-(↑s * ↑t : ℂ)).re = -(s * t) := by simp
      rw [this]
      calc ‖K t‖ * (Real.exp (-(s * t)) * ‖f s‖)
          ≤ (CK * (t ^ σ * (1 + t) ^ (-p))) * (Real.exp (-(s * t)) * ‖f s‖) := by
            gcongr; exact hKb t ht0
        _ = _ := by ring
    have hInt : IntegrableOn (fun t => G t s) (Ioi 0) := by
      refine (hI.const_mul (‖f s‖ * CK)).mono' ?_ ?_
      · exact (hKc.aestronglyMeasurable measurableSet_Ioi).mul
          ((Continuous.aestronglyMeasurable (by fun_prop)).mul aestronglyMeasurable_const)
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact hbd t ht
    refine ⟨hInt, ?_⟩
    calc ∫ t in Ioi 0, ‖G t s‖
        ≤ ∫ t in Ioi 0, ‖f s‖ * CK * (t ^ σ * (1 + t) ^ (-p) * Real.exp (-(s * t))) :=
          setIntegral_mono_on hInt.norm (hI.const_mul _) measurableSet_Ioi hbd
      _ = ‖f s‖ * CK * ∫ t in Ioi 0, t ^ σ * (1 + t) ^ (-p) * Real.exp (-(s * t)) :=
          integral_const_mul _ _
      _ ≤ _ := by gcongr
  have hmaj : IntegrableOn (fun s : ℝ => s ^ ((α + p - σ - 1) - 1) * (1 + s) ^ (-(α + 1 + p - β)))
      (Ioi 0) :=
    DLMF.Gamma.integrableOn_rpow_mul_one_add_rpow (by rw [hp]; linarith) (by linarith)
  have hGi : Integrable (Function.uncurry G)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
    refine (integrable_prod_iff' hm).mpr ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact (hinner s hs).1
    · refine (hmaj.const_mul (CK * CL)).mono' hm.norm.prod_swap.integral_prod_right' ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have hs0 : (0:ℝ) < s := hs
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      refine (hinner s hs0).2.trans (le_of_eq ?_)
      rw [hnf s hs0]
      have e1 : s ^ ((α + p - σ - 1) - 1) = s ^ (α - 1) * s ^ (p - σ - 1) := by
        rw [← Real.rpow_add hs0]; ring_nf
      have e2 : (1 + s) ^ (-(α + 1 + p - β)) = (1 + s) ^ (β - α - 1) * (1 + s) ^ (-p) := by
        rw [← Real.rpow_add (by linarith)]; ring_nf
      rw [e1, e2]; ring
  have hts : ∀ t ∈ Ioi (0:ℝ), ∫ s in Ioi 0, G t s = K t * (Gamma a * kummerU a b t) := by
    intro t ht
    have ht0 : (0:ℝ) < t := ht
    have hU := kummerU_laplace (a := a) (b := b) (z := t) ha (by simpa using ht0)
    simp only [hG]
    rw [integral_const_mul, hU]
    field_simp
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    simp only [hf]
    rw [show -((s : ℂ) * t) = -(t : ℂ) * s by ring]; ring_nf
  have hst : ∀ s ∈ Ioi (0:ℝ), ∫ t in Ioi 0, G t s =
      (s : ℂ) ^ (a - 1) * (1 + (s : ℂ)) ^ (b - a - 1) *
        (x ^ (ν / 2) * ((s : ℂ) ^ (-(ν + 1)) * exp (-x / s))) := by
    intro s hs
    have hs0 : (0:ℝ) < s := hs
    have h := cfInt_laplace_kernel hν1 hx0 hs0
    simp only [hG]
    rw [← h, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [hf, hK]; ring
  calc ∫ t : ℝ in Set.Ioi 0,
        (t : ℂ) ^ (ν / 2) * kummerU a b t * besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ))
      = ∫ t : ℝ in Ioi 0, (Gamma a)⁻¹ * ∫ s in Ioi 0, G t s := by
        refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
        rw [hts t ht]; simp only [hK]; field_simp
    _ = (Gamma a)⁻¹ * ∫ s in Ioi 0, ∫ t in Ioi 0, G t s := by
        rw [integral_const_mul, integral_integral_swap hGi]
    _ = (Gamma a)⁻¹ * (x ^ (ν / 2) * ∫ s : ℝ in Ioi 0, (s : ℂ) ^ (a - 1) *
          (1 + (s : ℂ)) ^ (b - a - 1) * ((s : ℂ) ^ (-(ν + 1)) * exp (-x / s))) := by
        rw [setIntegral_congr_fun measurableSet_Ioi hst, ← integral_const_mul,
          ← integral_const_mul, ← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
        ring
    _ = _ := by
        rw [cfInt_recip_subst_U hx (by simp; linarith)]
        field_simp

/-- `𝐅(a,b;c;0) = 1/Γ(c)`. -/
theorem regularizedGaussHG_zero_arg (a b c : ℂ) : regularizedGaussHG a b c 0 = (Gamma c)⁻¹ := by
  rw [regularizedGaussHG_eq_regularizedGaussHGFun a b c (by simp), regularizedGaussHGFun_eq_tsum,
    tsum_eq_single 0 (fun n hn => by simp [zero_pow hn])]
  simp

open Set in
open scoped Nat in
/-- Termwise integration of the Bessel series against the Tricomi Laplace transform; the
factor `t^n e^{-t/2} ≤ 2^n n!` gives a summable majorant. -/
@[dlmf 13.10.E16]
theorem bessel_kummerU_M {a b ν x : ℂ} (hx : 0 < x.re)
    (hν0 : (b - 2).re < ν.re) (hν1 : -1 < ν.re) :
    ∫ t : ℝ in Set.Ioi 0,
        exp (-(t : ℂ)) * (t : ℂ) ^ (ν / 2) * kummerU a b t *
          besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) =
      Gamma (ν - b + 2) * x ^ (ν / 2) * exp (-x) *
        regularizedHGFun {a} {a - b + ν + 2} x := by
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx
  set d := regularizedHGFunCoeff (∅ : Multiset ℂ) {ν + 1} with hd
  set F : ℕ → ℝ → ℂ := fun n t => (x ^ (ν / 2) * (d n * (-x) ^ n)) *
    tricomiLaplaceKernel a (ν + n + 1) b 1 t with hF
  have hν0' : b.re - 2 < ν.re := by
    have h := hν0; simp only [sub_re] at h; norm_num at h; linarith
  have hνn : ∀ n : ℕ, 0 < (ν + n + 1).re := fun n => by
    simp; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  have hνb : ∀ n : ℕ, (b - 1).re < (ν + n + 1).re := fun n => by
    simp; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  have hL : ∀ n : ℕ, _ := fun n =>
    laplace_kummerU_gauss (a := a) (b := ν + n + 1) (c := b) (z := 1) (hνn n) (hνb n) (by simp)
  have hFi : ∀ n : ℕ, IntegrableOn (F n) (Ioi 0) := fun n => (hL n).1.const_mul _
  -- the fixed half-weight majorant
  have hK0 := (laplace_kummerU_gauss (a := a) (b := ν + 1) (c := b) (z := (1 / 2 : ℂ))
    (by simp; linarith) (by simp; linarith) (by norm_num)).1
  set K0 := tricomiLaplaceKernel a (ν + 1) b (1 / 2) with hK0def
  have hker : ∀ n : ℕ, ∀ t : ℝ, 0 < t → tricomiLaplaceKernel a (ν + n + 1) b 1 t =
      ((t ^ n * Real.exp (-(t / 2)) : ℝ) : ℂ) * K0 t := by
    intro n t ht
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
    simp only [hK0def, tricomiLaplaceKernel]
    rw [show ν + n + 1 - 1 = (ν + 1 - 1) + n by ring, cpow_add _ _ ht0, cpow_natCast]
    have he : exp (-1 * (t : ℂ)) = exp (-(1 / 2) * (t : ℂ)) * exp (-(t / 2 : ℝ) : ℂ) := by
      rw [← exp_add]; push_cast; ring_nf
    rw [he]; push_cast; ring
  have htn : ∀ n : ℕ, ∀ t : ℝ, 0 < t → t ^ n * Real.exp (-(t / 2)) ≤ 2 ^ n * n ! := by
    intro n t ht
    have h := Real.pow_div_factorial_le_exp (x := t / 2) (by positivity) n
    rw [div_pow, div_div, div_le_iff₀ (by positivity)] at h
    have he : Real.exp (t / 2) * Real.exp (-(t / 2)) = 1 := by rw [← Real.exp_add]; simp
    calc t ^ n * Real.exp (-(t / 2)) ≤ Real.exp (t / 2) * (2 ^ n * n !) * Real.exp (-(t / 2)) := by
          gcongr
      _ = _ := by rw [mul_comm, ← mul_assoc, mul_comm (Real.exp _), he, one_mul]
  set C0 := ∫ t : ℝ in Ioi 0, ‖K0 t‖ with hC0
  have hbound : ∀ n : ℕ, (∫ t : ℝ in Ioi 0, ‖F n t‖) ≤
      ‖x ^ (ν / 2)‖ * C0 * (‖regularizedHGFunCoeff {(1 : ℂ)} {ν + 1} n‖ * (2 * ‖x‖) ^ n) := by
    intro n
    have hpt : ∀ t ∈ Ioi (0 : ℝ), ‖F n t‖ ≤
        (‖x ^ (ν / 2)‖ * ‖d n‖ * ‖x‖ ^ n * (2 ^ n * n !)) * ‖K0 t‖ := by
      intro t ht
      have ht0 : (0 : ℝ) < t := ht
      simp only [hF]
      rw [hker n t ht0, norm_mul, norm_mul, norm_mul, norm_mul, norm_pow, norm_neg,
        Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      have := htn n t ht0
      have h0 := norm_nonneg (K0 t)
      calc _ = (‖x ^ (ν / 2)‖ * ‖d n‖ * ‖x‖ ^ n) * (t ^ n * Real.exp (-(t / 2))) * ‖K0 t‖ := by ring
        _ ≤ (‖x ^ (ν / 2)‖ * ‖d n‖ * ‖x‖ ^ n) * (2 ^ n * n !) * ‖K0 t‖ := by gcongr
        _ = _ := by ring
    calc (∫ t : ℝ in Ioi 0, ‖F n t‖) ≤ ∫ t : ℝ in Ioi 0,
          (‖x ^ (ν / 2)‖ * ‖d n‖ * ‖x‖ ^ n * (2 ^ n * n !)) * ‖K0 t‖ :=
        setIntegral_mono_on (hFi n).norm (hK0.norm.const_mul _) measurableSet_Ioi hpt
      _ = _ := by
        rw [MeasureTheory.integral_const_mul, ← hC0, regularizedHGFunCoeff_singleton, hd,
          DLMF.Bessel.regularizedHGFunCoeff_empty]
        have hp : poch (1 : ℂ) n = n ! := by
          simp [poch, ascPochhammer_eval_one]
        have hfac : (n ! : ℝ) ≠ 0 := by positivity
        rw [hp]
        simp only [norm_div, norm_mul, one_div, norm_inv, Complex.norm_natCast, mul_pow]
        field_simp
  have hsum : Summable (fun n => ∫ t : ℝ in Ioi 0, ‖F n t‖) := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun t => norm_nonneg _) hbound ?_
    have h := ((hasFPowerSeriesOnBall_regularizedConfluent 1 (ν + 1)).hasSum_mul_pow
      (z := ((2 * ‖x‖ : ℝ) : ℂ)) (by simp)).summable.norm.mul_left (‖x ^ (ν / 2)‖ * C0)
    refine h.congr fun n => ?_
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hs := hasSum_integral_of_summable_integral_norm hFi hsum
  have hc : 0 < (ν - b + 2).re := by simp; linarith
  have hterm : ∀ n : ℕ, (∫ t : ℝ in Ioi 0, F n t) = x ^ (ν / 2) * Gamma (ν - b + 2) *
      (regularizedHGFunCoeff {ν - b + 2} {a - b + ν + 2} n * (-x) ^ n) := by
    intro n
    simp only [hF]
    rw [MeasureTheory.integral_const_mul, (hL n).2, sub_self, regularizedGaussHG_zero_arg, hd,
      DLMF.Bessel.regularizedHGFunCoeff_empty, regularizedHGFunCoeff_singleton]
    have hp := (Gamma_add_nat_div_Gamma_eq (n := n) (ν - b + 2) (not_neg_nat_of_re_pos hc))
    have hG1 : Gamma (ν + 1 + n) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)])
    have hG2 : Gamma (ν - b + 2) ≠ 0 := Gamma_ne_zero_of_re_pos hc
    rw [show poch (ν - b + 2) n = Gamma (ν - b + 2 + n) / Gamma (ν - b + 2) from hp.symm,
      show ν + n + 1 = ν + 1 + n by ring, show ν + 1 + n - b + 1 = ν - b + 2 + n by ring,
      show a + (ν + 1 + n) - b + 1 = a - b + ν + 2 + n by ring]
    field_simp
  simp_rw [hterm] at hs
  have hM := ((hasFPowerSeriesOnBall_regularizedConfluent (ν - b + 2) (a - b + ν + 2)).hasSum_mul_pow
    (z := -x) (by simp)).mul_left (x ^ (ν / 2) * Gamma (ν - b + 2))
  have hpt : ∀ t ∈ Ioi (0 : ℝ), exp (-(t : ℂ)) * (t : ℂ) ^ (ν / 2) * kummerU a b t *
      besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) = ∑' n, F n t := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    have htc : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht0.ne'
    have h0 := ((DLMF.Bessel.hasFPowerSeriesOnBall_regularized0F1 (ν + 1)).hasSum_mul_pow
      (z := -x * t) (by simp)).mul_left (x ^ (ν / 2) * (exp (-(t : ℂ)) * (t : ℂ) ^ ν * kummerU a b t))
    rw [besselJ_two_sqrt hx0 ht0]
    have hνt : (t : ℂ) ^ (ν / 2) * (t : ℂ) ^ (ν / 2) = (t : ℂ) ^ ν := by
      rw [← cpow_add _ _ htc]; ring_nf
    refine Eq.trans ?_ (h0.tsum_eq.symm.trans (tsum_congr fun n => ?_))
    · linear_combination (exp (-(t : ℂ)) * kummerU a b t * x ^ (ν / 2) *
        regularizedHGFun ∅ {ν + 1} (-x * t)) * hνt
    · simp only [hF, hd, tricomiLaplaceKernel]
      rw [show ν + n + 1 - 1 = ν + n by ring, cpow_add _ _ htc, cpow_natCast, mul_pow]
      ring_nf
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, hs.unique hM,
    regularizedConfluent_kummer_transform (ν - b + 2) (a - b + ν + 2) (-x), neg_neg,
    show a - b + ν + 2 - (ν - b + 2) = a by ring]
  ring

@[dlmf 13.23.E1]
theorem laplace_whittakerM {κ μ ν z : ℂ}
    (h : 0 < μ.re + ν.re + 1 / 2) (hz : 1 / 2 < z.re) :
    ∫ t : ℝ in Set.Ioi 0, exp (-z * t) * (t : ℂ) ^ (ν - 1) * whittakerM κ μ t =
      Gamma (μ + ν + 1 / 2) / (z + 1 / 2) ^ (μ + ν + 1 / 2) *
        ₂F₁ (1 / 2 + μ - κ) (1 / 2 + μ + ν) (1 + 2 * μ) (1 / (z + 1 / 2)) := by
  set A := 1 / 2 + μ - κ
  set B := 1 / 2 + μ + ν
  set C := 1 + 2 * μ
  set Z := z + 1 / 2
  rw [show μ + ν + 1 / 2 = B by simp only [B]; ring]
  have hB : 0 < B.re := by simp [B]; linarith
  have hZ : 0 < Z.re := by simp [Z]; linarith
  have hZ1 : ‖(1 : ℂ)‖ < Z.re := by simp [Z]; linarith
  have hZ0 : Z ≠ 0 := by intro h; simp [h] at hZ
  have hw : ‖1 / Z‖ < 1 := by
    rw [norm_div, norm_one, div_lt_one (norm_pos_iff.mpr hZ0)]
    exact (by simpa using hZ1 : (1 : ℝ) < Z.re).trans_le (re_le_norm Z)
  have hcongr : ∀ t ∈ Set.Ioi (0 : ℝ),
      exp (-z * t) * (t : ℂ) ^ (ν - 1) * whittakerM κ μ t =
        exp (-Z * t) * (t : ℂ) ^ (B - 1) * kummerM A C t := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht)
    have hp : (t : ℂ) ^ (ν - 1) * (t : ℂ) ^ (μ + 1 / 2) = (t : ℂ) ^ (B - 1) := by
      rw [← cpow_add _ _ ht0]; congr 1; simp only [B]; ring
    have he : exp (-z * t) * exp (-(t : ℂ) / 2) = exp (-Z * t) := by
      rw [← Complex.exp_add]; congr 1; simp only [Z]; ring
    rw [whittakerM, show μ - κ + 1 / 2 = A by simp only [A]; ring, ← hp, ← he]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, div_eq_mul_inv, ← cpow_neg]
  by_cases hC : ∀ k : ℕ, C ≠ -(k : ℂ)
  · have hl := laplace_regularizedHGFun_of_norm_lt (a := A) (c := C) (k := 1) hB hZ hZ1
    simp only [one_mul] at hl
    have hG := Gamma_ne_zero hC
    rw [DLMF.Hypergeometric.regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hw,
      DLMF.Hypergeometric.regularizedGaussHGFun_eq_div_Gamma hC] at hl
    simp_rw [kummerM_eq_mul_regularizedHGFun hC]
    have hm : (∫ t : ℝ in Set.Ioi 0,
        exp (-Z * t) * (t : ℂ) ^ (B - 1) * (Gamma C * regularizedHGFun {A} {C} t)) =
        Gamma C * ∫ t : ℝ in Set.Ioi 0,
          exp (-Z * t) * (t : ℂ) ^ (B - 1) * regularizedHGFun {A} {C} t := by
      rw [← integral_const_mul]; congr 1; funext t; ring
    rw [hm, hl]
    field_simp
  · push_neg at hC
    obtain ⟨m, hm⟩ := hC
    have hK : ∀ t : ℂ, kummerM A C t =
        ∑ n ∈ Finset.range (m + 1), poch A n / (poch C n * (n.factorial : ℂ)) * t ^ n := by
      intro t
      unfold kummerM
      refine tsum_eq_sum fun n hn => ?_
      have hmn : m < n := by rw [Finset.mem_range] at hn; omega
      simp [hm, poch_neg_nat_eq_zero hmn]
    have hF : ₂F₁ A B C (1 / Z) =
        ∑ n ∈ Finset.range (m + 1), gaussHGCoeff A B C n * (1 / Z) ^ n := by
      rw [ordinaryHypergeometric_eq_tsum]
      simp only [smul_eq_mul]
      have hterm : (fun k : ℕ =>
          ((k.factorial : ℂ)⁻¹) * (ascPochhammer ℂ k).eval A *
            (ascPochhammer ℂ k).eval B * ((ascPochhammer ℂ k).eval C)⁻¹ * (1 / Z) ^ k) =
          fun k => gaussHGCoeff A B C k * (1 / Z) ^ k := by
        funext k
        simp [gaussHGCoeff, poch, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      rw [hterm]
      refine tsum_eq_sum fun k hk => ?_
      have hmk : m < k := by rw [Finset.mem_range] at hk; omega
      simp [gaussHGCoeff, hm, poch_neg_nat_eq_zero hmk]
    have hBn (n : ℕ) : 0 < (B + n).re := by simp; positivity
    have hFi (n : ℕ) : IntegrableOn
        (fun t : ℝ => poch A n / (poch C n * (n.factorial : ℂ)) *
          ((t : ℂ) ^ (B + n - 1) * exp (-(Z * t)))) (Set.Ioi 0) := by
      refine Integrable.const_mul ?_ _
      have hreal := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1)
        (s := B.re + n - 1) (b := Z.re)
        (by have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith) one_pos hZ
      simp only [Real.rpow_one] at hreal
      apply Integrable.mono' hreal (Measurable.aestronglyMeasurable (by fun_prop))
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      simp only [norm_mul, norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_exp]
      simp
    have hpt : ∀ t ∈ Set.Ioi (0 : ℝ),
        exp (-Z * t) * (t : ℂ) ^ (B - 1) * kummerM A C t =
          ∑ n ∈ Finset.range (m + 1), poch A n / (poch C n * (n.factorial : ℂ)) *
            ((t : ℂ) ^ (B + n - 1) * exp (-(Z * t))) := by
      intro t ht
      have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht)
      rw [hK, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [show B + n - 1 = (B - 1) + n by ring, cpow_add _ _ ht0, cpow_natCast,
        neg_mul]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_finsetSum _ fun n _ => hFi n,
      hF, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [integral_const_mul, DLMF.Gamma.integral_cpow_mul_exp_neg_mul_Ioi (hBn n) hZ]
    have hp := not_neg_nat_of_re_pos hB
    have hGb := (div_eq_iff (Gamma_ne_zero hp)).mp (Gamma_add_nat_div_Gamma_eq (n := n) B hp)
    rw [hGb, show -(B + (n : ℂ)) = -B + -(n : ℂ) by ring, cpow_add _ _ hZ0, cpow_neg Z (n : ℂ),
      cpow_natCast, gaussHGCoeff, one_div, inv_pow]
    simp only [poch]
    ring

@[dlmf 13.23.E2]
theorem laplace_whittakerM_closed {κ μ z : ℂ}
    (hμ : -1 / 2 < μ.re) (hz : 1 / 2 < z.re) :
    ∫ t : ℝ in Set.Ioi 0, exp (-z * t) * (t : ℂ) ^ (μ - 1 / 2) * whittakerM κ μ t =
      Gamma (2 * μ + 1) * (z + 1 / 2) ^ (-κ - μ - 1 / 2) *
        (z - 1 / 2) ^ (κ - μ - 1 / 2) := by
  have hb : 0 < (2 * μ + 1).re := by simp; linarith
  have hp : ∀ k : ℕ, 1 + 2 * μ ≠ -(k : ℂ) :=
    not_neg_nat_of_re_pos (by simpa [add_comm] using hb)
  have hB : 0 < (z + 1 / 2).re := by simp; linarith
  have hA : 0 < (z - 1 / 2).re := by simp; linarith
  have hB0 : z + 1 / 2 ≠ 0 := by intro h; rw [h] at hB; simpa using hB
  have hA0 : z - 1 / 2 ≠ 0 := by intro h; rw [h] at hA; simpa using hA
  have hr : 1 - (z + 1 / 2)⁻¹ = (z - 1 / 2) / (z + 1 / 2) := by
    apply (eq_div_iff hB0).mpr
    rw [sub_mul, one_mul, inv_mul_cancel₀ hB0]
    ring
  have hargA := (abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hA)))
  have hargB := (abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hB)))
  have hargBπ : (z + 1 / 2).arg ≠ Real.pi := by linarith [Real.pi_pos]
  have hlog : log ((z - 1 / 2) / (z + 1 / 2)) = log (z - 1 / 2) - log (z + 1 / 2) := by
    rw [div_eq_mul_inv, Complex.log_mul hA0 (inv_ne_zero hB0), Complex.log_inv _ hargBπ]
    · rfl
    · rw [arg_inv, if_neg hargBπ]
      constructor <;> linarith [hargA.1, hargA.2, hargB.1, hargB.2]
  have hpow : (1 - (z + 1 / 2)⁻¹) ^ (κ - μ - 1 / 2) =
      (z - 1 / 2) ^ (κ - μ - 1 / 2) * (z + 1 / 2) ^ (-(κ - μ - 1 / 2)) := by
    rw [hr, cpow_def_of_ne_zero (div_ne_zero hA0 hB0), hlog,
      sub_mul, exp_sub, cpow_def_of_ne_zero hA0, cpow_def_of_ne_zero hB0,
      mul_neg, exp_neg, div_eq_mul_inv]
  have hi : (∫ t : ℝ in Set.Ioi 0,
      exp (-z * t) * (t : ℂ) ^ (μ - 1 / 2) * whittakerM κ μ t) =
      Gamma (2 * μ + 1) * ∫ t : ℝ in Set.Ioi 0,
        exp (-(z + 1 / 2) * t) * (t : ℂ) ^ ((2 * μ + 1) - 1) *
          regularizedHGFun {μ - κ + 1 / 2} {2 * μ + 1} t := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [whittakerM, kummerM_eq_mul_regularizedHGFun hp,
      show 1 + 2 * μ = 2 * μ + 1 by ring]
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
    have he : exp (-z * t) * exp (-(t : ℂ) / 2) = exp (-(z + 1 / 2) * t) := by
      rw [← exp_add]
      congr 1
      ring
    have htP : (t : ℂ) ^ (μ - 1 / 2) * (t : ℂ) ^ (μ + 1 / 2) =
        (t : ℂ) ^ ((2 * μ + 1) - 1) := by
      rw [← cpow_add _ _ ht0]
      congr 1
      ring
    calc
      _ = Gamma (2 * μ + 1) * (exp (-z * t) * exp (-(t : ℂ) / 2)) *
          ((t : ℂ) ^ (μ - 1 / 2) * (t : ℂ) ^ (μ + 1 / 2)) *
          regularizedHGFun {μ - κ + 1 / 2} {2 * μ + 1} t := by ring
      _ = _ := by rw [he, htP]; ring
  rw [hi, laplace_regularizedHGFun_self hb (by simp; linarith),
    show -(μ - κ + 1 / 2) = κ - μ - 1 / 2 by ring, hpow]
  rw [show -(2 * μ + 1) = (-κ - μ - 1 / 2) + (κ - μ - 1 / 2) by ring,
    cpow_add _ _ hB0]
  have hc : (z + 1 / 2) ^ (κ - μ - 1 / 2) * (z + 1 / 2) ^ (-(κ - μ - 1 / 2)) = 1 := by
    rw [cpow_neg, mul_inv_cancel₀ (cpow_ne_zero_iff.mpr (Or.inl hB0))]
  linear_combination Gamma (2 * μ + 1) * (z + 1 / 2) ^ (-κ - μ - 1 / 2) *
    (z - 1 / 2) ^ (κ - μ - 1 / 2) * hc

/-- The Mellin transform uses regularized M, including exceptional second parameters. -/
@[dlmf 13.23.E3]
theorem mellin_whittakerM {κ μ ν : ℂ}
    (h0 : -1 / 2 - μ.re < ν.re) (h1 : ν.re < κ.re) :
    ∫ t : ℝ in Set.Ioi 0, exp (-(t : ℂ) / 2) * (t : ℂ) ^ (ν - 1) *
        regularizedWhittakerM κ μ t =
      Gamma (μ + ν + 1 / 2) * Gamma (κ - ν) /
        (Gamma (1 / 2 + μ + κ) * Gamma (1 / 2 + μ - ν)) := by
  have hm := mellin_regularizedHGFun_exp (a := μ - κ + 1 / 2)
    (b := μ + ν + 1 / 2) (c := 1 + 2 * μ) (by simp; linarith) (by simp; linarith)
  have he : ∀ t ∈ Set.Ioi (0 : ℝ),
      exp (-(t : ℂ) / 2) * (t : ℂ) ^ (ν - 1) * regularizedWhittakerM κ μ t =
      exp (-(t : ℂ)) * (t : ℂ) ^ (μ + ν + 1 / 2 - 1) *
        regularizedHGFun {μ - κ + 1 / 2} {1 + 2 * μ} t := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
    have hp : (t : ℂ) ^ (ν - 1) * (t : ℂ) ^ (μ + 1 / 2) =
        (t : ℂ) ^ (μ + ν + 1 / 2 - 1) := by
      rw [← cpow_add _ _ ht0]; congr 1; ring
    have hx : exp (-(t : ℂ) / 2) * exp (-(t : ℂ) / 2) = exp (-(t : ℂ)) := by
      rw [← exp_add]; congr 1; ring
    rw [regularizedWhittakerM, ← hp, ← hx]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi he, hm,
    show (1 + 2 * μ) - (μ - κ + 1 / 2) - (μ + ν + 1 / 2) = κ - ν by ring,
    show (1 + 2 * μ) - (μ - κ + 1 / 2) = 1 / 2 + μ + κ by ring,
    show (1 + 2 * μ) - (μ + ν + 1 / 2) = 1 / 2 + μ - ν by ring]

@[dlmf 13.23.E4]
theorem laplace_whittakerW {κ μ ν z : ℂ}
    (h : |μ.re| < ν.re + 1 / 2) (hz : -1 / 2 < z.re) :
    ∫ t : ℝ in Set.Ioi 0, exp (-z * t) * (t : ℂ) ^ (ν - 1) * whittakerW κ μ t =
      Gamma (1 / 2 + μ + ν) * Gamma (1 / 2 - μ + ν) *
        DLMF.Hypergeometric.regularizedGaussHG (1 / 2 - μ + ν) (1 / 2 + μ + ν) (ν - κ + 1)
            (1 / 2 - z) := by
  have hμ := abs_le.mp (le_refl |μ.re|)
  have hm := (laplace_kummerU_gauss (a := 1 / 2 + μ - κ) (b := μ + ν + 1 / 2)
    (c := 1 + 2 * μ) (z := z + 1 / 2) (by simp; linarith)
      (by simp; linarith) (by simp; linarith)).2
  have he : ∀ t ∈ Set.Ioi (0 : ℝ),
      exp (-z * t) * (t : ℂ) ^ (ν - 1) * whittakerW κ μ t =
        tricomiLaplaceKernel (1 / 2 + μ - κ) (μ + ν + 1 / 2) (1 + 2 * μ) (z + 1 / 2) t := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
    have hp : (t : ℂ) ^ (ν - 1) * (t : ℂ) ^ (1 / 2 + μ) =
        (t : ℂ) ^ (μ + ν + 1 / 2 - 1) := by
      rw [← cpow_add _ _ ht0]; congr 1; ring
    have hx : exp (-z * t) * exp (-(t : ℂ) / 2) = exp (-(z + 1 / 2) * t) := by
      rw [← exp_add]; congr 1; ring
    rw [whittakerW, tricomiLaplaceKernel, ← hp, ← hx]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi he, hm,
    show μ + ν + 1 / 2 = 1 / 2 + μ + ν by ring,
    show (1 / 2 + μ + ν) - (1 + 2 * μ) + 1 = 1 / 2 - μ + ν by ring,
    show (1 / 2 + μ - κ) + (1 / 2 + μ + ν) - (1 + 2 * μ) + 1 = ν - κ + 1 by ring,
    show 1 - (z + 1 / 2) = 1 / 2 - z by ring,
    DLMF.Hypergeometric.regularizedGaussHG_symm _ _ _ (by
      change 1 - (1 / 2 - z) ∈ slitPlane
      left; simp; linarith)]

@[dlmf 13.23.E5]
theorem mellin_whittakerW {κ μ ν : ℂ}
    (h0 : |μ.re| - 1 / 2 < ν.re) (h1 : ν.re < -κ.re) :
    ∫ t : ℝ in Set.Ioi 0, exp ((t : ℂ) / 2) * (t : ℂ) ^ (ν - 1) * whittakerW κ μ t =
      Gamma (1 / 2 + μ + ν) * Gamma (1 / 2 - μ + ν) * Gamma (-κ - ν) /
        (Gamma (1 / 2 + μ - κ) * Gamma (1 / 2 - μ - κ)) := by
  have hμ := abs_le.mp (le_refl |μ.re|)
  have hm := mellin_kummerU (a := 1 / 2 + μ - κ) (b := 1 + 2 * μ) (lam := ν + μ + 1 / 2)
    (by simp; linarith) (by simp; linarith) (by simp; linarith)
  have hcongr : ∀ t ∈ Set.Ioi (0 : ℝ),
      exp ((t : ℂ) / 2) * (t : ℂ) ^ (ν - 1) * whittakerW κ μ t =
        (t : ℂ) ^ (ν + μ + 1 / 2 - 1) * kummerU (1 / 2 + μ - κ) (1 + 2 * μ) t := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht)
    have hp : (t : ℂ) ^ (ν - 1) * (t : ℂ) ^ (1 / 2 + μ) = (t : ℂ) ^ (ν + μ + 1 / 2 - 1) := by
      rw [← cpow_add _ _ ht0]; ring_nf
    have he : exp ((t : ℂ) / 2) * exp (-(t : ℂ) / 2) = 1 := by
      rw [← Complex.exp_add]; ring_nf; exact Complex.exp_zero
    rw [whittakerW, ← hp]
    linear_combination ((t : ℂ) ^ (ν - 1) * (t : ℂ) ^ (1 / 2 + μ) *
      kummerU (1 / 2 + μ - κ) (1 + 2 * μ) t) * he
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, hm]
  congr 1
  · rw [show ν + μ + 1 / 2 = 1 / 2 + μ + ν by ring,
      show 1 / 2 + μ - κ - (1 / 2 + μ + ν) = -κ - ν by ring,
      show 1 / 2 + μ + ν - (1 + 2 * μ) + 1 = 1 / 2 - μ + ν by ring]
    ring
  · rw [show 1 / 2 + μ - κ - (1 + 2 * μ) + 1 = 1 / 2 - μ - κ by ring]

open Set in
/-- A cosine transform of regularized Whittaker M. For `κ + μ ≤ 0` the integral converges only
conditionally, which Lean's integral does not capture, so `0 < κ + μ` is required. -/
@[dlmf 13.23.E8]
theorem cosine_whittakerM {κ μ x : ℝ} (hx : 0 < x)
    (h : 0 < (κ + μ : ℂ).re) :
    ∫ t : ℝ in Set.Ioi 0,
        Complex.cos (2 * x * t) * exp (-(t : ℂ) ^ 2 / 2) *
          (t : ℂ) ^ (-(2 * (μ : ℂ) + 1)) *
          regularizedWhittakerM κ μ ((t : ℂ) ^ 2) =
      (Real.sqrt π : ℂ) * exp (-(x : ℂ) ^ 2 / 2) * (x : ℂ) ^ ((μ : ℂ) + κ - 1) /
        (2 * Gamma (1 / 2 + (μ : ℂ) + κ)) *
        whittakerW (κ / 2 - 3 * μ / 2) (κ / 2 + μ / 2) (x ^ 2) := by
  have hκμ : 0 < κ + μ := by simpa using h
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hC := cosine_regularizedHGFun (a := μ + κ + 1 / 2) (b := 1 + 2 * μ) hx (by linarith)
  push_cast at hC
  have hcongr : ∀ t ∈ Ioi (0 : ℝ),
      Complex.cos (2 * x * t) * exp (-(t : ℂ) ^ 2 / 2) * (t : ℂ) ^ (-(2 * (μ : ℂ) + 1)) *
          regularizedWhittakerM κ μ ((t : ℂ) ^ 2) =
        Complex.cos (2 * x * t) *
          regularizedHGFun {(μ : ℂ) + κ + 1 / 2} {1 + 2 * (μ : ℂ)} (-(t : ℂ) ^ 2) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    have htc : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht0.ne'
    have hp : (t : ℂ) ^ (-(2 * (μ : ℂ) + 1)) * ((t : ℂ) ^ 2) ^ ((μ : ℂ) + 1 / 2) = 1 := by
      rw [sq, mul_cpow_ofReal_nonneg ht0.le ht0.le, ← cpow_add _ _ htc, ← cpow_add _ _ htc]
      ring_nf; exact cpow_zero _
    have he : exp (-(t : ℂ) ^ 2 / 2) * exp (-((t : ℂ) ^ 2) / 2) * exp ((t : ℂ) ^ 2) = 1 := by
      rw [← Complex.exp_add, ← Complex.exp_add]; ring_nf; exact Complex.exp_zero
    rw [regularizedWhittakerM, regularizedConfluent_kummer_transform,
      show 1 + 2 * (μ : ℂ) - ((μ : ℂ) - κ + 1 / 2) = (μ : ℂ) + κ + 1 / 2 by ring]
    linear_combination (Complex.cos (2 * x * t) *
      regularizedHGFun {(μ : ℂ) + κ + 1 / 2} {1 + 2 * (μ : ℂ)} (-(t : ℂ) ^ 2)) *
      (exp (-(t : ℂ) ^ 2 / 2) * exp (-((t : ℂ) ^ 2) / 2) * exp ((t : ℂ) ^ 2) * hp + he)
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, hC, whittakerW]
  rw [show (1 : ℂ) / 2 + ((κ : ℂ) / 2 + (μ : ℂ) / 2) - ((κ : ℂ) / 2 - 3 * (μ : ℂ) / 2) =
      1 + 2 * (μ : ℂ) - 1 / 2 by ring,
    show (1 : ℂ) + 2 * ((κ : ℂ) / 2 + (μ : ℂ) / 2) = (μ : ℂ) + κ + 1 / 2 + 1 / 2 by ring,
    show (1 : ℂ) / 2 + (μ : ℂ) + κ = (μ : ℂ) + κ + 1 / 2 by ring]
  have hp : (x : ℂ) ^ ((μ : ℂ) + κ - 1) * ((x : ℂ) ^ 2) ^ ((1 : ℂ) / 2 + ((κ : ℂ) / 2 + (μ : ℂ) / 2)) =
      (x : ℂ) ^ (2 * ((μ : ℂ) + κ + 1 / 2) - 1) := by
    rw [sq, mul_cpow_ofReal_nonneg hx.le hx.le, ← cpow_add _ _ hx0, ← cpow_add _ _ hx0]
    ring_nf
  have he : exp (-(x : ℂ) ^ 2 / 2) * exp (-((x : ℂ) ^ 2) / 2) = exp (-(x : ℂ) ^ 2) := by
    rw [← Complex.exp_add]; ring_nf
  rw [← hp, ← he]
  ring

/-- A Hankel-type transform of regularized Whittaker M, for real `x > 0`. For non-real `x` the Bessel kernel
grows like `exp (c √t)`; the parameter bound makes the integrand absolutely integrable, as
required for Lean's integral. -/
@[dlmf 13.23.E9]
theorem bessel_whittakerM {κ μ ν x : ℂ} (hx : 0 < x.re) (hxi : x.im = 0)
    (hμ : -1 / 2 < μ.re) (hμ' : μ.re < κ.re + ν.re / 2 - 1 / 4) :
    ∫ t : ℝ in Set.Ioi 0,
        exp (-(t : ℂ) / 2) * (t : ℂ) ^ (μ - (ν + 1) / 2) * regularizedWhittakerM κ μ t *
          besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) =
      exp (-x / 2) *
        x ^ ((κ - μ - 3 / 2) / 2) *
        regularizedWhittakerM ((κ + 3 * μ - ν + 1 / 2) / 2) ((κ - μ + ν - 1 / 2) / 2) x := by
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx
  have h := bessel_regularizedHGFun (a := μ - κ + 1 / 2) (b := 1 + 2 * μ) (ν := ν) hx hxi
    (by simp; linarith) (by simp; linarith)
  have hpt : ∀ t ∈ Set.Ioi (0:ℝ), exp (-(t : ℂ) / 2) * (t : ℂ) ^ (μ - (ν + 1) / 2) *
      regularizedWhittakerM κ μ t * besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) =
      exp (-(t : ℂ)) * (t : ℂ) ^ (1 + 2 * μ - 1 - ν / 2) *
        regularizedHGFun {μ - κ + 1 / 2} {1 + 2 * μ} t * besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) := by
    intro t ht
    have ht0 : (0:ℝ) < t := ht
    have htc : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht0.ne'
    have e1 : (t : ℂ) ^ (μ - (ν + 1) / 2) * (t : ℂ) ^ (μ + 1 / 2) = (t : ℂ) ^ (1 + 2 * μ - 1 - ν / 2) := by
      rw [← cpow_add _ _ htc]; ring_nf
    have e2 : exp (-(t : ℂ) / 2) * exp (-(t : ℂ) / 2) = exp (-(t : ℂ)) := by
      rw [← Complex.exp_add]; ring_nf
    simp only [regularizedWhittakerM]
    rw [← e1, ← e2]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, h]
  simp only [regularizedWhittakerM]
  have e3 : x ^ ((κ - μ - 3 / 2) / 2) * x ^ ((κ - μ + ν - 1 / 2) / 2 + 1 / 2) =
      x ^ (-(μ - κ + 1 / 2) + ν / 2) := by
    rw [← cpow_add _ _ hx0]; ring_nf
  have e2 : exp (-x / 2) * exp (-x / 2) = exp (-x) := by
    rw [← Complex.exp_add]; ring_nf
  rw [show (κ - μ + ν - 1 / 2) / 2 - (κ + 3 * μ - ν + 1 / 2) / 2 + 1 / 2 = ν - (1 + 2 * μ) + 1 by ring,
    show 1 + 2 * ((κ - μ + ν - 1 / 2) / 2) = ν - (μ - κ + 1 / 2) + 1 by ring, ← e3, ← e2]
  ring

open Set in
/-- A Hankel-type transform of regularized Whittaker M in terms of W, for real `x > 0`. For non-real `x` the
Bessel kernel grows like `exp (c √t)`; the parameter bound makes the integrand absolutely
integrable, as required for Lean's integral. -/
@[dlmf 13.23.E10]
theorem bessel_whittakerM_W {κ μ ν x : ℂ} (hx : 0 < x.re) (hxi : x.im = 0)
    (hν0 : -1 < ν.re) (hν1 : ν.re < 2 * (κ + μ).re - 1 / 2) :
    ∫ t : ℝ in Set.Ioi 0,
        exp (-(t : ℂ) / 2) * (t : ℂ) ^ ((ν - 1) / 2 - μ) * regularizedWhittakerM κ μ t *
          besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) =
      exp (-x / 2) * x ^ ((κ + μ - 3 / 2) / 2) / Gamma (1 / 2 + μ + κ) *
        whittakerW ((κ - 3 * μ + ν + 1 / 2) / 2) ((κ + μ - ν - 1 / 2) / 2) x := by
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx
  have hM := bessel_regularizedHGFun_U (a := μ - κ + 1 / 2) (b := 1 + 2 * μ) (ν := ν) hx hxi hν0
    (by simp at hν1 ⊢; linarith)
  have hcongr : ∀ t ∈ Ioi (0 : ℝ),
      exp (-(t : ℂ) / 2) * (t : ℂ) ^ ((ν - 1) / 2 - μ) * regularizedWhittakerM κ μ t *
          besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) =
        exp (-(t : ℂ)) * (t : ℂ) ^ (ν / 2) * regularizedHGFun {μ - κ + 1 / 2} {1 + 2 * μ} t *
          besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht)
    have hp : (t : ℂ) ^ ((ν - 1) / 2 - μ) * (t : ℂ) ^ (μ + 1 / 2) = (t : ℂ) ^ (ν / 2) := by
      rw [← cpow_add _ _ ht0]; ring_nf
    have he : exp (-(t : ℂ) / 2) * exp (-(t : ℂ) / 2) = exp (-(t : ℂ)) := by
      rw [← Complex.exp_add]; ring_nf
    rw [regularizedWhittakerM, ← hp, ← he]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, hM, whittakerW,
    show 1 / 2 + (κ + μ - ν - 1 / 2) / 2 - (κ - 3 * μ + ν + 1 / 2) / 2 =
      (μ - κ + 1 / 2) - (μ - κ + 1 / 2 - (1 + 2 * μ) + ν + 2) + 1 by ring,
    show 1 + 2 * ((κ + μ - ν - 1 / 2) / 2) = 2 - (μ - κ + 1 / 2 - (1 + 2 * μ) + ν + 2) by ring,
    kummerU_kummer_transform_all (μ - κ + 1 / 2) (μ - κ + 1 / 2 - (1 + 2 * μ) + ν + 2) hx0,
    show 1 + 2 * μ - (μ - κ + 1 / 2) = 1 / 2 + μ + κ by ring]
  have hp1 : x ^ (ν / 2) * x ^ (1 - (μ - κ + 1 / 2 - (1 + 2 * μ) + ν + 2)) =
      x ^ ((κ + μ - 3 / 2) / 2) * x ^ (1 / 2 + (κ + μ - ν - 1 / 2) / 2) := by
    rw [← cpow_add _ _ hx0, ← cpow_add _ _ hx0]; ring_nf
  have he : exp (-x / 2) * exp (-x / 2) = exp (-x) := by
    rw [← Complex.exp_add]; ring_nf
  rw [← he]
  linear_combination (exp (-x / 2) * exp (-x / 2) / Gamma (1 / 2 + μ + κ) *
    kummerU (μ - κ + 1 / 2 - (μ - κ + 1 / 2 - (1 + 2 * μ) + ν + 2) + 1)
      (2 - (μ - κ + 1 / 2 - (1 + 2 * μ) + ν + 2)) x) * hp1

open Set in
/-- A Hankel-type transform of `e^{t/2}` times Whittaker W, for real `x > 0`. For non-real `x` the
Bessel kernel grows like `exp (c √t)`; the parameter bound makes the integrand absolutely
integrable, as required for Lean's integral. -/
@[dlmf 13.23.E11]
theorem bessel_whittakerW {κ μ ν x : ℂ} (hx : 0 < x.re) (hxi : x.im = 0)
    (hν0 : (2 * μ.re - 1) < ν.re) (hν1 : -1 < ν.re) (hν2 : ν.re < 2 * (μ - κ).re - 1 / 2) :
    ∫ t : ℝ in Set.Ioi 0,
        exp ((t : ℂ) / 2) * (t : ℂ) ^ ((ν - 1) / 2 - μ) * whittakerW κ μ t *
          besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) =
      Gamma (ν - 2 * μ + 1) / Gamma (1 / 2 + μ - κ) * exp (x / 2) *
        x ^ ((μ - κ - 3 / 2) / 2) *
        whittakerW ((κ + 3 * μ - ν - 1 / 2) / 2) ((κ - μ + ν + 1 / 2) / 2) x := by
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx
  have hK := bessel_kummerU (a := 1 / 2 + μ - κ) (b := 1 + 2 * μ) (ν := ν) hx hxi
    (by simp; linarith) hν1 (by simp at hν2 ⊢; linarith)
  have hcongr : ∀ t ∈ Ioi (0 : ℝ),
      exp ((t : ℂ) / 2) * (t : ℂ) ^ ((ν - 1) / 2 - μ) * whittakerW κ μ t *
          besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) =
        (t : ℂ) ^ (ν / 2) * kummerU (1 / 2 + μ - κ) (1 + 2 * μ) t *
          besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht)
    have hp : (t : ℂ) ^ ((ν - 1) / 2 - μ) * (t : ℂ) ^ (1 / 2 + μ) = (t : ℂ) ^ (ν / 2) := by
      rw [← cpow_add _ _ ht0]; ring_nf
    have he : exp ((t : ℂ) / 2) * exp (-(t : ℂ) / 2) = 1 := by
      rw [← Complex.exp_add]; ring_nf; exact Complex.exp_zero
    rw [whittakerW, ← hp]
    linear_combination ((t : ℂ) ^ ((ν - 1) / 2 - μ) * (t : ℂ) ^ (1 / 2 + μ) *
      kummerU (1 / 2 + μ - κ) (1 + 2 * μ) t * besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ))) * he
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, hK, whittakerW,
    show 1 / 2 + (κ - μ + ν + 1 / 2) / 2 - (κ + 3 * μ - ν - 1 / 2) / 2 = ν - (1 + 2 * μ) + 2 by
      ring,
    show 1 + 2 * ((κ - μ + ν + 1 / 2) / 2) = ν - (1 / 2 + μ - κ) + 2 by ring]
  have hp : x ^ ((μ - κ - 3 / 2) / 2) * x ^ (1 / 2 + (κ - μ + ν + 1 / 2) / 2) = x ^ (ν / 2) := by
    rw [← cpow_add _ _ hx0]; ring_nf
  have he : exp (x / 2) * exp (-x / 2) = 1 := by
    rw [← Complex.exp_add]; ring_nf; exact Complex.exp_zero
  rw [show ν - 2 * μ + 1 = ν - (1 + 2 * μ) + 2 by ring, ← hp]
  linear_combination (Gamma (ν - (1 + 2 * μ) + 2) / Gamma (1 / 2 + μ - κ) *
    (x ^ ((μ - κ - 3 / 2) / 2) * x ^ (1 / 2 + (κ - μ + ν + 1 / 2) / 2)) *
    kummerU (ν - (1 + 2 * μ) + 2) (ν - (1 / 2 + μ - κ) + 2) x) * (-he)

open Set in
/-- The output M is regularized; Gamma poles in its second parameter are retained. -/
@[dlmf 13.23.E12]
theorem bessel_whittakerW_M {κ μ ν x : ℂ} (hx : 0 < x.re)
    (hν0 : (2 * μ.re - 1) < ν.re) (hν1 : -1 < ν.re) :
    ∫ t : ℝ in Set.Ioi 0,
        exp (-(t : ℂ) / 2) * (t : ℂ) ^ ((ν - 1) / 2 - μ) * whittakerW κ μ t *
          besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) =
      Gamma (ν - 2 * μ + 1) * exp (-x / 2) *
        x ^ ((μ + κ - 3 / 2) / 2) *
        regularizedWhittakerM ((κ - 3 * μ + ν + 1 / 2) / 2) ((ν - μ - κ + 1 / 2) / 2) x := by
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx
  have hpt : ∀ t ∈ Ioi (0 : ℝ),
      exp (-(t : ℂ) / 2) * (t : ℂ) ^ ((ν - 1) / 2 - μ) * whittakerW κ μ t *
        besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) =
      exp (-(t : ℂ)) * (t : ℂ) ^ (ν / 2) * kummerU (1 / 2 + μ - κ) (1 + 2 * μ) t *
        besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) := by
    intro t ht
    have htc : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht)
    have he : exp (-(t : ℂ) / 2) * exp (-(t : ℂ) / 2) = exp (-(t : ℂ)) := by
      rw [← exp_add]; ring_nf
    have hp : (t : ℂ) ^ ((ν - 1) / 2 - μ) * (t : ℂ) ^ (1 / 2 + μ) = (t : ℂ) ^ (ν / 2) := by
      rw [← cpow_add _ _ htc]; ring_nf
    rw [whittakerW, ← he, ← hp]; ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt,
    bessel_kummerU_M hx (by simp; linarith) hν1, regularizedWhittakerM,
    show 1 / 2 + μ - κ - (1 + 2 * μ) + ν + 2 = 1 + 2 * ((ν - μ - κ + 1 / 2) / 2) by ring,
    show ν - (1 + 2 * μ) + 2 = ν - 2 * μ + 1 by ring,
    show 1 / 2 + μ - κ = (ν - μ - κ + 1 / 2) / 2 - (κ - 3 * μ + ν + 1 / 2) / 2 + 1 / 2 by ring]
  have he : exp (-x / 2) * exp (-x / 2) = exp (-x) := by rw [← exp_add]; ring_nf
  have hp : x ^ ((μ + κ - 3 / 2) / 2) * x ^ ((ν - μ - κ + 1 / 2) / 2 + 1 / 2) = x ^ (ν / 2) := by
    rw [← cpow_add _ _ hx0]; ring_nf
  rw [← he, ← hp]; ring


/-! ### Gauss and Stieltjes representations (DLMF 13.4.5, 13.4.8, 13.16.6, 13.16.9)

These representations from §13.4 and §13.16 are proved here, after the Laplace transforms
they use. For `Re a > 0`, two applications of the regularized Kummer Laplace transform and
Fubini reduce 13.4.8 to Tricomi's Laplace representation. Tricomi's contiguous relation in
`a`, matched by a regularized Gauss contiguous relation that also raises `c`, then removes
the restriction on `a`. The Stieltjes form follows from `1/(t+z) = ∫ e^{-(t+z)s} ds`, the
Tricomi Laplace transform, Pfaff's transformation and 13.4.8 with `c = 1`. It is first proved
for `Re z > 0` and then continued holomorphically to the slit plane. -/

section GaussStieltjes

open Set

/-- `𝐅(a,c;c;w) = (1-w)^{-a}/Γ(c)` on the cut plane. -/
theorem regularizedGaussHG_self_right (a c : ℂ) {w : ℂ} (hw : w ∈ cutPlane) :
    regularizedGaussHG a c c w = (1 - w) ^ (-a) * (Gamma c)⁻¹ := by
  have h0 : regularizedGaussHG 0 (c - a) c w = (Gamma c)⁻¹ :=
    eqOn_cutPlane_of_eqOn_disk (f := regularizedGaussHG 0 (c - a) c) (g := fun _ => (Gamma c)⁻¹)
      (analyticOnNhd_regularizedGaussHG _ _ _) analyticOnNhd_const (fun u hu => by
        rw [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hu, regularizedGaussHGFun_eq_tsum,
          tsum_eq_single 0 (fun n hn => by
            obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
            simp [ascPochhammer_succ_left])]
        simp) hw
  rw [regularizedGaussHG_euler, show c - c = (0 : ℂ) by ring, regularizedGaussHG_symm _ _ _ hw, h0,
    show c - a - c = -a by ring]
  exact hw

theorem neg_ofReal_mem_cutPlane {t : ℝ} (ht : 0 ≤ t) : (-(t : ℂ)) ∈ cutPlane := by
  change 1 - -(t : ℂ) ∈ slitPlane
  rw [sub_neg_eq_add]
  exact Or.inl (by simp; linarith)

/-- The kernel of the Gauss–Laplace representation 13.4.8. -/
def kummerUGaussKernel (a b c z : ℂ) (t : ℝ) : ℂ :=
  exp (-z * t) * (t : ℂ) ^ (c - 1) * regularizedGaussHG a (a - b + 1) c (-(t : ℂ))

theorem kummerU_gauss_of_re_pos {a b c z : ℂ} (ha : 0 < a.re) (hc : 0 < c.re) (hz : 0 < z.re) :
    IntegrableOn (kummerUGaussKernel a b c z) (Ioi 0) ∧
      kummerU a b z = z ^ (c - a) * ∫ t : ℝ in Ioi 0, kummerUGaussKernel a b c z t := by
  obtain ⟨β, hβ⟩ : ∃ β : ℂ, β = a - b + 1 := ⟨_, rfl⟩
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  set F : ℝ → ℝ → ℂ := fun t s => exp (-z * t) * (t : ℂ) ^ (c - 1) *
    (exp (-z * s) * (s : ℂ) ^ (a - 1) * regularizedHGFun {β} {c} ((-z * t) * s)) with hF
  obtain ⟨C, hC, N, hM⟩ := regularizedConfluent_ray_growth β c (-z)
  have hmax : max 0 (-z).re = 0 := by simp; linarith
  have hRc : Continuous (fun q : ℝ × ℝ => regularizedHGFun {β} {c} ((-z * q.1) * q.2)) :=
    (continuous_regularizedConfluent.comp (show Continuous (fun w : ℂ => (β, c, w)) by fun_prop)).comp
      (show Continuous (fun q : ℝ × ℝ => (-z * (q.1 : ℂ)) * (q.2 : ℂ)) by fun_prop)
  have hRm := hRc.measurable
  have hmeas : AEStronglyMeasurable (Function.uncurry F) ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
    refine Measurable.aestronglyMeasurable ?_
    simp only [hF, Function.uncurry_def]
    fun_prop
  have hf1 := integrableOn_rpow_mul_one_add_pow_mul_exp (s := c.re - 1) (by linarith) hz N
  have hf2 := integrableOn_rpow_mul_one_add_pow_mul_exp (s := a.re - 1) (by linarith) hz N
  have hFi : Integrable (Function.uncurry F) ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
    refine ((hf1.mul_prod hf2).const_mul C).mono' hmeas ?_
    have hset : ∀ᵐ q ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))), q ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ) := by
      rw [Measure.prod_restrict]
      exact ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)
    filter_upwards [hset] with q hq
    obtain ⟨t, s⟩ := q
    obtain ⟨ht, hs⟩ := hq
    change 0 < t at ht; change 0 < s at hs
    have hb := hM (t * s) (by positivity)
    rw [hmax, zero_mul, Real.exp_zero, mul_one] at hb
    have harg : (-z * t) * s = -z * ((t * s : ℝ) : ℂ) := by push_cast; ring
    simp only [hF, Function.uncurry_def, norm_mul, Complex.norm_exp, norm_cpow_eq_rpow_re_of_pos ht,
      norm_cpow_eq_rpow_re_of_pos hs, harg]
    simp only [neg_mul, neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero, sub_re, one_re]
    have h1 : (1 + t * s) ^ N ≤ (1 + t) ^ N * (1 + s) ^ N := by
      rw [← mul_pow]; gcongr; nlinarith
    calc _ ≤ Real.exp (-(z.re * t)) * t ^ (c.re - 1) *
          (Real.exp (-(z.re * s)) * s ^ (a.re - 1) * (C * ((1 + t) ^ N * (1 + s) ^ N))) := by
          gcongr
          rw [← neg_mul]
          exact hb.trans (mul_le_mul_of_nonneg_left h1 hC)
      _ = _ := by ring
  have hpt : ∀ t ∈ Ioi (0 : ℝ), kummerUGaussKernel a b c z t =
      (Gamma a)⁻¹ * z ^ a * ∫ s : ℝ in Ioi 0, F t s := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    have hL := laplace_regularizedHGFun (a := β) (b := a) (c := c) (k := -z * t) (z := z) ha
      (by simp; nlinarith) hz
    have harg : (-z * t) / z = -(t : ℂ) := by field_simp
    rw [harg] at hL
    have hF' : ∫ s : ℝ in Ioi 0, F t s = exp (-z * t) * (t : ℂ) ^ (c - 1) *
        ∫ s : ℝ in Ioi 0, exp (-z * s) * (s : ℂ) ^ (a - 1) * regularizedHGFun {β} {c} ((-z * t) * s) := by
      simp only [hF]; rw [integral_const_mul]
    rw [hF', hL, kummerUGaussKernel, ← hβ,
      regularizedGaussHG_symm _ _ _ (neg_ofReal_mem_cutPlane ht0.le)]
    have hGa : Gamma a ≠ 0 := Gamma_ne_zero_of_re_pos ha
    have hza : z ^ a * z ^ (-a) = 1 := by rw [← cpow_add _ _ hz0]; simp
    have e : ∀ X Y : ℂ, (Gamma a)⁻¹ * z ^ a * (X * (Gamma a * z ^ (-a) * Y)) =
        X * Y * (z ^ a * z ^ (-a)) * ((Gamma a)⁻¹ * Gamma a) := fun X Y => by ring
    rw [e, hza, inv_mul_cancel₀ hGa]; ring
  have hinner : ∀ s ∈ Ioi (0 : ℝ), ∫ t : ℝ in Ioi 0, F t s =
      z ^ (-c) * (exp (-z * s) * (s : ℂ) ^ (a - 1) * (1 + (s : ℂ)) ^ (b - a - 1)) := by
    intro s hs
    have hs0 : (0 : ℝ) < s := hs
    have hL := laplace_regularizedHGFun (a := β) (b := c) (c := c) (k := -z * s) (z := z) hc
      (by simp; nlinarith) hz
    have harg : (-z * s) / z = -(s : ℂ) := by field_simp
    rw [harg, regularizedGaussHG_self_right _ _ (neg_ofReal_mem_cutPlane hs0.le)] at hL
    have hF' : ∫ t : ℝ in Ioi 0, F t s = (exp (-z * s) * (s : ℂ) ^ (a - 1)) *
        ∫ t : ℝ in Ioi 0, exp (-z * t) * (t : ℂ) ^ (c - 1) * regularizedHGFun {β} {c} ((-z * s) * t) := by
      rw [← integral_const_mul]
      congr 1; funext t
      simp only [hF]
      rw [show (-z * (t : ℂ)) * s = (-z * s) * t by ring]
      ring
    rw [hF', hL, sub_neg_eq_add, hβ, show -(a - b + 1) = b - a - 1 by ring]
    field_simp [Gamma_ne_zero_of_re_pos hc]
  have hint := (hFi.integral_prod_left.const_mul ((Gamma a)⁻¹ * z ^ a)).congr (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht; exact (hpt t ht).symm)
  refine ⟨hint, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul,
    integral_integral_swap hFi, setIntegral_congr_fun measurableSet_Ioi hinner, integral_const_mul,
    kummerU_laplace ha hz]
  have hzz : z ^ (c - a) * z ^ a * z ^ (-c) = 1 := by
    rw [← cpow_add _ _ hz0, ← cpow_add _ _ hz0]; ring_nf; exact cpow_zero _
  generalize (∫ s : ℝ in Ioi 0, exp (-z * s) * (s : ℂ) ^ (a - 1) * (1 + (s : ℂ)) ^ (b - a - 1)) = J
  linear_combination (-(Gamma a)⁻¹ * J) * hzz

/-- 13.4.8 with absolute integrability, for every first parameter, by Tricomi's
contiguous relation in `a` and the matching regularized Gauss relation. -/
lemma kummerU_gauss_aux {a b c z : ℂ} (hc : 0 < c.re) (hz : 0 < z.re) :
    IntegrableOn (kummerUGaussKernel a b c z) (Ioi 0) ∧
      kummerU a b z = z ^ (c - a) * ∫ t : ℝ in Ioi 0, kummerUGaussKernel a b c z t := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hshift : ∀ N : ℕ, ∀ a b c : ℂ, 0 < a.re + N → 0 < c.re →
      IntegrableOn (kummerUGaussKernel a b c z) (Ioi 0) ∧
        kummerU a b z = z ^ (c - a) * ∫ t : ℝ in Ioi 0, kummerUGaussKernel a b c z t := by
    intro N
    induction N with
    | zero => intro a b c ha hc; exact kummerU_gauss_of_re_pos (by simpa using ha) hc hz
    | succ N ih =>
      intro a b c ha hc
      have h1 := ih (a + 1) (b + 1) c (by simp at ha ⊢; linarith) hc
      have h2 := ih (a + 1) b (c + 1) (by simp at ha ⊢; linarith) (by simp; linarith)
      have hpt : ∀ t ∈ Ioi (0 : ℝ), kummerUGaussKernel a b c z t =
          kummerUGaussKernel (a + 1) (b + 1) c z t +
            (a - b + 1) * kummerUGaussKernel (a + 1) b (c + 1) z t := by
        intro t ht
        have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht)
        have hw := neg_ofReal_mem_cutPlane (le_of_lt (mem_Ioi.mp ht))
        have hg := regularizedGaussHG_contiguous_shift_b (a - b + 1) a c hw
        rw [regularizedGaussHG_symm _ _ _ hw, regularizedGaussHG_symm (a - b + 1) (a + 1) c hw,
          regularizedGaussHG_symm (a - b + 1 + 1) (a + 1) (c + 1) hw] at hg
        simp only [kummerUGaussKernel]
        rw [show a + 1 - (b + 1) + 1 = a - b + 1 by ring, show a + 1 - b + 1 = a - b + 1 + 1 by ring,
          show c + 1 - 1 = (c - 1) + 1 by ring, cpow_add _ _ ht0, cpow_one]
        linear_combination (exp (-z * t) * (t : ℂ) ^ (c - 1)) * hg
      have hi : IntegrableOn (kummerUGaussKernel a b c z) (Ioi 0) :=
        (h1.1.add (h2.1.const_mul (a - b + 1))).congr (by
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht; exact (hpt t ht).symm)
      refine ⟨hi, ?_⟩
      have hU := kummerU_contiguous_shift_a (a + 1) b z hz0
      rw [add_sub_cancel_right] at hU
      rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_add h1.1 (h2.1.const_mul _),
        integral_const_mul]
      have hz1 : z ^ (c - a) = z * z ^ (c - (a + 1)) := by
        rw [show c - a = 1 + (c - (a + 1)) by ring, cpow_add _ _ hz0, cpow_one]
      rw [show c + 1 - (a + 1) = c - a by ring] at h2
      rw [h1.2, h2.2] at hU
      rw [hz1] at hU ⊢
      linear_combination hU
  obtain ⟨N, hN⟩ := exists_nat_gt (-a.re)
  exact hshift N a b c (by linarith) hc

@[dlmf 13.4.E8]
theorem kummerU_gauss {a b c z : ℂ} (ha : 0 < c.re) (hz : 0 < z.re) :
    kummerU a b z =
      z ^ (c - a) *
        ∫ t : ℝ in Set.Ioi 0,
          exp (-z * t) * (t : ℂ) ^ (c - 1) *
            DLMF.Hypergeometric.regularizedGaussHG a (a - b + 1) c (-(t : ℂ)) :=
  (kummerU_gauss_aux ha hz).2

@[dlmf 13.16.E9]
theorem whittakerW_gauss {κ μ c z : ℂ} (hc : 0 < c.re) (hz : 0 < z.re) :
    whittakerW κ μ z =
      exp (-z / 2) * z ^ (κ + c) *
        ∫ t : ℝ in Set.Ioi 0,
          exp (-z * t) * (t : ℂ) ^ (c - 1) *
            DLMF.Hypergeometric.regularizedGaussHG (1 / 2 + μ - κ) (1 / 2 - μ - κ) c (-(t : ℂ)) := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  rw [whittakerW, kummerU_gauss (b := 1 + 2 * μ) hc hz,
    show 1 / 2 + μ - κ - (1 + 2 * μ) + 1 = 1 / 2 - μ - κ by ring]
  have hp : z ^ (1 / 2 + μ) * z ^ (c - (1 / 2 + μ - κ)) = z ^ (κ + c) := by
    rw [← cpow_add _ _ hz0]; ring_nf
  rw [← hp]; ring

/-- Points of the slit plane stay uniformly away from the closed negative ray. -/
theorem exists_forall_le_norm_add_of_mem_slitPlane {z₀ : ℂ} (hz₀ : z₀ ∈ slitPlane) :
    ∃ δ > 0, ∀ t : ℝ, 0 ≤ t → ∀ z ∈ Metric.ball z₀ δ, δ ≤ ‖(t : ℂ) + z‖ := by
  have hd : ∃ d > 0, ∀ t : ℝ, 0 ≤ t → d ≤ ‖(t : ℂ) + z₀‖ := by
    by_cases hre : 0 < z₀.re
    · refine ⟨z₀.re, hre, fun t ht => ?_⟩
      calc z₀.re ≤ ((t : ℂ) + z₀).re := by simp; linarith
        _ ≤ _ := re_le_norm _
    · have him : z₀.im ≠ 0 := by
        rcases mem_slitPlane_iff.mp hz₀ with h | h
        · exact absurd h hre
        · exact h
      refine ⟨|z₀.im|, abs_pos.mpr him, fun t _ => ?_⟩
      calc |z₀.im| = |((t : ℂ) + z₀).im| := by simp
        _ ≤ _ := abs_im_le_norm _
  obtain ⟨d, hd0, hd⟩ := hd
  refine ⟨d / 2, by linarith, fun t ht z hz => ?_⟩
  rw [Metric.mem_ball, dist_eq_norm] at hz
  have h1 := hd t ht
  have h2 : ‖(t : ℂ) + z₀‖ ≤ ‖(t : ℂ) + z‖ + ‖z - z₀‖ := by
    calc ‖(t : ℂ) + z₀‖ = ‖((t : ℂ) + z) - (z - z₀)‖ := by ring_nf
      _ ≤ _ := norm_sub_le _ _
  linarith

/-- The Stieltjes transform of an integrable function on the positive half-line is
holomorphic on the slit plane. -/
theorem differentiableOn_stieltjes_integral {g : ℝ → ℂ} (hg : IntegrableOn g (Ioi 0)) :
    DifferentiableOn ℂ (fun z => ∫ t : ℝ in Ioi 0, g t / ((t : ℂ) + z)) slitPlane := by
  intro z₀ hz₀
  obtain ⟨δ, hδ, hδb⟩ := exists_forall_le_norm_add_of_mem_slitPlane hz₀
  have hpos : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), 0 ≤ t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using le_of_lt ht
  have hne : ∀ t : ℝ, 0 ≤ t → ∀ z ∈ Metric.ball z₀ δ, (t : ℂ) + z ≠ 0 := fun t ht z hz h => by
    have := hδb t ht z hz; rw [h, norm_zero] at this; linarith
  have hmeas : ∀ z : ℂ, AEStronglyMeasurable (fun t : ℝ => g t / ((t : ℂ) + z))
      (volume.restrict (Ioi 0)) := fun z =>
    hg.aestronglyMeasurable.mul (Measurable.aestronglyMeasurable (by fun_prop))
  have hint : Integrable (fun t : ℝ => g t / ((t : ℂ) + z₀)) (volume.restrict (Ioi 0)) := by
    refine (hg.norm.const_mul δ⁻¹).mono' (hmeas z₀) ?_
    filter_upwards [hpos] with t ht
    rw [norm_div, div_eq_mul_inv, mul_comm]
    gcongr
    exact hδb t ht z₀ (Metric.mem_ball_self hδ)
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi 0))
    (F := fun z (t : ℝ) => g t / ((t : ℂ) + z))
    (F' := fun z (t : ℝ) => -(g t / ((t : ℂ) + z) ^ 2))
    (bound := fun t => (δ ^ 2)⁻¹ * ‖g t‖)
    (Metric.ball_mem_nhds _ hδ) (Eventually.of_forall hmeas) hint
    ((hg.aestronglyMeasurable.mul (Measurable.aestronglyMeasurable (by fun_prop))).neg)
    ?_ (hg.norm.const_mul _) ?_
  · exact hd.2.differentiableAt.differentiableWithinAt
  · filter_upwards [hpos] with t ht z hz
    rw [norm_neg, norm_div, norm_pow, div_eq_mul_inv, mul_comm]
    gcongr
    exact hδb t ht z hz
  · filter_upwards [hpos] with t ht z hz
    have h0 := hne t ht z hz
    have h := ((hasDerivAt_id z).const_add (t : ℂ)).inv h0
    have h' := h.const_mul (g t)
    simp only [id_eq] at h'
    convert h' using 1
    · ext w; simp [div_eq_mul_inv]
    · field_simp


/-- Tricomi's Stieltjes representation 13.4.5 in the right half-plane, by Fubini against
`1/(t+z) = ∫ e^{-(t+z)s} ds`, the Tricomi Laplace transform and Pfaff's transformation. -/
theorem kummerU_stieltjes_of_re_pos {a b z : ℂ} (hz : 0 < z.re)
    (ha : (b - 1).re < a.re) (ha0 : 0 < a.re) :
    kummerU a b z = z ^ (1 - a) / (Gamma a * Gamma (1 + a - b)) *
      ∫ t : ℝ in Set.Ioi 0, kummerU (b - a) b t * exp (-(t : ℂ)) * (t : ℂ) ^ (a - 1) /
        ((t : ℂ) + z) := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hab : 0 < (1 + a - b).re := by simp only [sub_re, add_re, one_re] at ha ⊢; linarith
  have hGa : Gamma a ≠ 0 := Gamma_ne_zero_of_re_pos ha0
  have hGab : Gamma (1 + a - b) ≠ 0 := Gamma_ne_zero_of_re_pos hab
  have hK := (laplace_kummerU_gauss (a := b - a) (b := a) (c := b) (z := 1) ha0 ha (by simp)).1
  set K := tricomiLaplaceKernel (b - a) a b 1 with hKdef
  set G : ℝ → ℝ → ℂ := fun t s => K t * exp (-((t : ℂ) + z) * s) with hG
  have he : IntegrableOn (fun s : ℝ => Real.exp (-z.re * s)) (Ioi 0) := exp_neg_integrableOn_Ioi 0 hz
  have hGi : Integrable (Function.uncurry G)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
    refine (hK.norm.mul_prod he).mono' ?_ ?_
    · have hm : AEStronglyMeasurable (fun q : ℝ × ℝ => K q.1 * exp (-((q.1 : ℂ) + z) * q.2))
          ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) :=
        (hK.aestronglyMeasurable.comp_fst (ν := volume.restrict (Ioi (0:ℝ)))).mul
          (Continuous.aestronglyMeasurable (by fun_prop))
      exact hm
    · have hset : ∀ᵐ q ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))),
          q ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ) := by
        rw [Measure.prod_restrict]
        exact ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)
      filter_upwards [hset] with q hq
      obtain ⟨t, s⟩ := q
      obtain ⟨ht, hs⟩ := hq
      change 0 < t at ht; change 0 < s at hs
      simp only [hG, Function.uncurry_def, norm_mul, Complex.norm_exp]
      gcongr
      simp; nlinarith
  have hsinner : ∀ t ∈ Ioi (0 : ℝ), ∫ s : ℝ in Ioi 0, G t s = K t / ((t : ℂ) + z) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    have hne : (t : ℂ) + z ≠ 0 := fun h => by
      have := congrArg re h; simp at this; linarith
    simp only [hG]
    rw [integral_const_mul, integral_exp_mul_complex_Ioi (by simp; linarith) 0]
    simp only [ofReal_zero, mul_zero, exp_zero]
    field_simp
  have htinner : ∀ s ∈ Ioi (0 : ℝ), ∫ t : ℝ in Ioi 0, G t s =
      Gamma a * Gamma (1 + a - b) *
        kummerUGaussKernel a b 1 z s := by
    intro s hs
    have hs0 : (0 : ℝ) < s := hs
    have hL := laplace_kummerU (a := b - a) (b := a) (c := b) (z := 1 + s) ha0 ha
      (by simp; linarith)
    have h1s : (1 + (s : ℂ)) = ((1 + s : ℝ) : ℂ) := by push_cast; ring
    have hw : 1 - (1 + (s : ℂ))⁻¹ ∈ cutPlane := by
      change 1 - (1 - (1 + (s : ℂ))⁻¹) ∈ slitPlane
      rw [sub_sub_cancel, h1s, ← ofReal_inv]
      exact ofReal_mem_slitPlane.mpr (by positivity)
    have hp := regularizedGaussHG_pfaff a (b - a) 1 hw
    rw [regularizedGaussHG_symm _ _ _ hw] at hL
    have hq : (1 - (1 + (s : ℂ))⁻¹) / (1 - (1 + (s : ℂ))⁻¹ - 1) = -(s : ℂ) := by
      have : (1 + (s : ℂ)) ≠ 0 := by rw [h1s]; exact ofReal_ne_zero.mpr (by positivity)
      field_simp; ring
    rw [hq, sub_sub_cancel, show (1 : ℂ) - (b - a) = a - b + 1 by ring] at hp
    rw [show b - a + a - b + 1 = (1 : ℂ) by ring, hp] at hL
    have hpow : (1 + (s : ℂ)) ^ (-a) * ((1 + (s : ℂ))⁻¹) ^ (-a) = 1 := by
      rw [h1s, ← ofReal_inv, ← mul_cpow_ofReal_nonneg (by positivity) (by positivity),
        ← ofReal_mul, mul_inv_cancel₀ (by positivity : (1 + s : ℝ) ≠ 0), ofReal_one, one_cpow]
    have hG' : ∀ t : ℝ, G t s = tricomiLaplaceKernel (b - a) a b (1 + s) t * exp (-z * s) := by
      intro t
      simp only [hG, hKdef, tricomiLaplaceKernel]
      have : exp (-1 * (t : ℂ)) * exp (-((t : ℂ) + z) * s) = exp (-(1 + (s : ℂ)) * t) * exp (-z * s) := by
        rw [← exp_add, ← exp_add]; ring_nf
      linear_combination ((t : ℂ) ^ (a - 1) * kummerU (b - a) b t) * this
    simp_rw [hG']
    rw [integral_mul_const]
    change (∫ t : ℝ in Ioi 0, exp (-(1 + (s : ℂ)) * t) * (t : ℂ) ^ (a - 1) * kummerU (b - a) b t) *
      exp (-z * s) = _
    rw [hL, kummerUGaussKernel, sub_self, cpow_zero,
      show a - b + 1 = 1 + a - b by ring]
    linear_combination (Gamma a * Gamma (1 + a - b) * exp (-z * s) *
      regularizedGaussHG a (1 + a - b) 1 (-(s : ℂ))) * hpow
  have hrw : ∀ t ∈ Ioi (0 : ℝ), kummerU (b - a) b t * exp (-(t : ℂ)) * (t : ℂ) ^ (a - 1) /
      ((t : ℂ) + z) = ∫ s : ℝ in Ioi 0, G t s := by
    intro t ht
    rw [hsinner t ht, hKdef, tricomiLaplaceKernel]
    ring_nf
  rw [setIntegral_congr_fun measurableSet_Ioi hrw, integral_integral_swap hGi,
    setIntegral_congr_fun measurableSet_Ioi htinner, integral_const_mul]
  have hU := (kummerU_gauss_aux (a := a) (b := b) (c := 1) (by simp) hz).2
  rw [hU]
  field_simp

@[dlmf 13.4.E5]
theorem kummerU_stieltjes {a b z : ℂ} (hz : z ∈ slitPlane)
    (ha : (b - 1).re < a.re) (ha0 : 0 < a.re) :
    kummerU a b z =
      z ^ (1 - a) / (Gamma a * Gamma (1 + a - b)) *
        ∫ t : ℝ in Set.Ioi 0,
          kummerU (b - a) b t * exp (-(t : ℂ)) * (t : ℂ) ^ (a - 1) /
            ((t : ℂ) + z) := by
  have hK := (laplace_kummerU_gauss (a := b - a) (b := a) (c := b) (z := 1) ha0 ha (by simp)).1
  have hg : IntegrableOn (fun t : ℝ => kummerU (b - a) b t * exp (-(t : ℂ)) * (t : ℂ) ^ (a - 1))
      (Ioi 0) := hK.congr (Eventually.of_forall fun t => by
        simp only [tricomiLaplaceKernel, neg_mul, one_mul]; ring)
  have hS := differentiableOn_stieltjes_integral hg
  set h : ℂ → ℂ := fun z => z ^ (1 - a) / (Gamma a * Gamma (1 + a - b)) *
    ∫ t : ℝ in Set.Ioi 0, kummerU (b - a) b t * exp (-(t : ℂ)) * (t : ℂ) ^ (a - 1) /
      ((t : ℂ) + z) with hh
  have hf : AnalyticOnNhd ℂ (kummerU a b) slitPlane :=
    (differentiableOn_kummerU a b).analyticOnNhd isOpen_slitPlane
  have hha : AnalyticOnNhd ℂ h slitPlane := by
    refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) isOpen_slitPlane
    exact (((differentiableAt_id.cpow (differentiableAt_const _) hw).div_const _).differentiableWithinAt).mul
      (hS w hw)
  have heq : kummerU a b =ᶠ[𝓝 1] h := by
    have hnh : {w : ℂ | 0 < w.re} ∈ 𝓝 (1 : ℂ) :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (by simp)
    filter_upwards [hnh] with w hw
    exact kummerU_stieltjes_of_re_pos hw ha ha0
  exact hf.eqOn_of_preconnected_of_eventuallyEq hha ((starConvex_one_slitPlane.isPathConnected one_mem_slitPlane).isConnected.isPreconnected)
    one_mem_slitPlane heq hz

/-- `1/(t+z)` is `O((1+t)^{-1})` on the positive half-line, for `z` in the slit plane. -/
theorem cfInt_norm_recip_add_le {z : ℂ} (hz : z ∈ slitPlane) :
    ∃ K, ∀ t : ℝ, 0 < t → ‖((t : ℂ) + z)⁻¹‖ ≤ K * (1 + t) ^ (-1 : ℝ) := by
  obtain ⟨δ, hδ, hδb⟩ := exists_forall_le_norm_add_of_mem_slitPlane hz
  refine ⟨1 / δ + 1 + ‖z‖ / δ, fun t ht => ?_⟩
  have h1 := hδb t ht.le z (Metric.mem_ball_self hδ)
  have hpos : 0 < ‖(t : ℂ) + z‖ := hδ.trans_le h1
  have h2 : t ≤ ‖(t : ℂ) + z‖ + ‖z‖ := by
    have := norm_sub_le ((t : ℂ) + z) z
    rw [add_sub_cancel_right, norm_real, Real.norm_of_nonneg ht.le] at this
    exact this
  have h3 : 1 + t ≤ (1 / δ + 1 + ‖z‖ / δ) * ‖(t : ℂ) + z‖ := by
    have e1 : 1 ≤ ‖(t : ℂ) + z‖ / δ := by rw [le_div_iff₀ hδ]; linarith
    have e2 : ‖z‖ ≤ ‖z‖ / δ * ‖(t : ℂ) + z‖ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
      exact mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    calc 1 + t ≤ ‖(t : ℂ) + z‖ / δ + (‖(t : ℂ) + z‖ + ‖z‖ / δ * ‖(t : ℂ) + z‖) := by
          linarith
      _ = _ := by ring
  rw [Real.rpow_neg_one, norm_inv, ← div_eq_mul_inv, le_div_iff₀ (by linarith),
    inv_mul_eq_div, div_le_iff₀ hpos]
  linarith

theorem cfInt_integrableOn_stieltjes {a b z : ℂ} {n : ℕ} (hz : z ∈ slitPlane)
    (h0 : -b.re < n) (h1 : (n : ℝ) < 1 + (a - b).re) :
    IntegrableOn (fun t : ℝ => regularizedHGFun {a} {b} (-(t : ℂ)) * (t : ℂ) ^ (b + n - 1) /
      ((t : ℂ) + z)) (Ioi 0) := by
  obtain ⟨K, hK⟩ := cfInt_norm_recip_add_le hz
  have hne : ∀ t : ℝ, 0 < t → (t : ℂ) + z ≠ 0 := fun t ht h => by
    obtain ⟨δ, hδ, hδb⟩ := exists_forall_le_norm_add_of_mem_slitPlane hz
    have := hδb t ht.le z (Metric.mem_ball_self hδ)
    rw [h, norm_zero] at this; linarith
  have hh : ContinuousOn (fun t : ℝ => ((t : ℂ) + z)⁻¹) (Ioi 0) :=
    ContinuousOn.inv₀ (by fun_prop) fun t ht => hne t ht
  have hI := integrableOn_cpow_mul_regularizedHGFun_neg_mul (a := a) (b := b) (c := b + n)
    hh hK (by simp; linarith) (by simp at h1 ⊢; linarith)
  refine hI.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only [div_eq_mul_inv]
  ring

theorem cfInt_integral_exp_Ioi {w : ℂ} (hw : 0 < w.re) :
    ∫ s : ℝ in Ioi 0, exp (-w * s) = w⁻¹ := by
  rw [integral_exp_mul_complex_Ioi (by simpa using hw) 0]
  simp [div_neg, neg_div]

theorem cfInt_integral_norm_exp_Ioi {w : ℂ} (hw : 0 < w.re) :
    ∫ s : ℝ in Ioi 0, ‖exp (-w * s)‖ = (w.re)⁻¹ := by
  have h := cfInt_integral_exp_Ioi (w := (w.re : ℂ)) (by simpa using hw)
  have he : ∀ s : ℝ, ‖exp (-w * s)‖ = Real.exp (-w.re * s) := fun s => by
    rw [Complex.norm_exp]; simp
  simp_rw [he]
  have h2 : ∫ s : ℝ in Ioi 0, ((Real.exp (-w.re * s) : ℝ) : ℂ) = ((w.re)⁻¹ : ℝ) := by
    rw [ofReal_inv, ← h]
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    rw [ofReal_exp]; push_cast; ring_nf
  rw [integral_complex_ofReal] at h2
  exact_mod_cast h2

/-- The base case `n = 0` of 13.4.6 in the right half-plane, by Fubini against
`1/(t+z) = ∫ e^{-(t+z)s} ds`, the Kummer Laplace transform 13.10.3 and Tricomi's Laplace
integral 13.4.4. -/
theorem cfInt_stieltjes_zero_of_re_pos {a b z : ℂ} (hz : 0 < z.re) (hb : 0 < b.re)
    (hab : b.re < 1 + a.re) :
    ∫ t : ℝ in Ioi 0, regularizedHGFun {a} {b} (-(t : ℂ)) * (t : ℂ) ^ (b - 1) / ((t : ℂ) + z) =
      z ^ (b - 1) * Gamma (1 + a - b) * kummerU a b z := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  set g : ℝ → ℂ := fun t => regularizedHGFun {a} {b} (-(t : ℂ)) * (t : ℂ) ^ (b - 1) with hg
  set G : ℝ → ℝ → ℂ := fun t s => g t * exp (-((t : ℂ) + z) * s) with hG
  have hgc : ContinuousOn g (Ioi 0) :=
    (kumDec_continuous_neg a b).continuousOn.mul (ContinuousOn.cpow continuous_ofReal.continuousOn
      continuousOn_const fun t ht => ofReal_mem_slitPlane.mpr ht)
  have hxz : ((z.re : ℝ) : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr hz
  have hS := cfInt_integrableOn_stieltjes (a := a) (b := b) (n := 0) hxz (by simpa using hb)
    (by simp; linarith)
  simp only [CharP.cast_eq_zero, add_zero] at hS
  have hGi : Integrable (Function.uncurry G)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
    have hm : AEStronglyMeasurable (Function.uncurry G)
        ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) :=
      ((hgc.aestronglyMeasurable measurableSet_Ioi).comp_fst
        (ν := volume.restrict (Ioi (0:ℝ)))).mul (Continuous.aestronglyMeasurable (by fun_prop))
    refine (integrable_prod_iff hm).mpr ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : (0 : ℝ) < t := ht
      exact (integrableOn_exp_mul_complex_Ioi (a := -((t : ℂ) + z)) (by simp; linarith) 0).const_mul
        (g t) |>.congr (Eventually.of_forall fun s => by simp [Function.uncurry, hG])
    · refine hS.norm.congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : (0 : ℝ) < t := ht
      simp only [Function.uncurry_apply_pair, hG, norm_mul]
      rw [integral_const_mul, cfInt_integral_norm_exp_Ioi (by simp; linarith), norm_div,
        div_eq_mul_inv]
      congr 2
      rw [show ((t : ℂ) + ((z.re : ℝ) : ℂ)) = ((t + z.re : ℝ) : ℂ) by push_cast; ring, norm_real,
        Real.norm_of_nonneg (by linarith)]
      simp
  have hsinner : ∀ t ∈ Ioi (0 : ℝ), ∫ s : ℝ in Ioi 0, G t s = g t / ((t : ℂ) + z) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    simp only [hG]
    rw [integral_const_mul, cfInt_integral_exp_Ioi (by simp; linarith), div_eq_mul_inv]
  have htinner : ∀ s ∈ Ioi (0 : ℝ), ∫ t : ℝ in Ioi 0, G t s =
      exp (-z * s) * ((s : ℂ) ^ (a - b) * (1 + (s : ℂ)) ^ (-a)) := by
    intro s hs
    have hs0 : (0 : ℝ) < s := hs
    have hL := laplace_regularizedHGFun (a := a) (b := b) (c := b) (k := -1) (z := s) hb
      (by simp; linarith) (by simpa using hs0)
    have hw : (-1 : ℂ) / s ∈ cutPlane := by
      change 1 - (-1 : ℂ) / s ∈ slitPlane
      rw [show (1 : ℂ) - (-1) / s = ((1 + s⁻¹ : ℝ) : ℂ) by push_cast; ring]
      exact ofReal_mem_slitPlane.mpr (by positivity)
    rw [regularizedGaussHG_self_right a b hw] at hL
    have hpow : (s : ℂ) ^ (-b) * (1 - (-1 : ℂ) / s) ^ (-a) =
        (s : ℂ) ^ (a - b) * (1 + (s : ℂ)) ^ (-a) := by
      have hs' : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs0.ne'
      rw [show (1 : ℂ) - (-1) / s = ((1 + s : ℝ) : ℂ) * ((s⁻¹ : ℝ) : ℂ) by push_cast; field_simp; ring,
        mul_cpow_ofReal_nonneg (by positivity) (by positivity), ofReal_inv,
        inv_cpow _ _ (by rw [arg_ofReal_of_nonneg hs0.le]; exact Real.pi_ne_zero.symm),
        ← cpow_neg, neg_neg, sub_eq_add_neg, cpow_add _ _ hs']
      push_cast; ring
    have hGb : Gamma b ≠ 0 := Gamma_ne_zero_of_re_pos hb
    calc ∫ t : ℝ in Ioi 0, G t s
        = exp (-z * s) * ∫ t : ℝ in Ioi 0,
            exp (-(s : ℂ) * t) * (t : ℂ) ^ (b - 1) * regularizedHGFun {a} {b} (-1 * t) := by
          rw [← integral_const_mul]
          refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
          simp only [hG, hg, neg_one_mul]
          have : exp (-((t : ℂ) + z) * s) = exp (-z * s) * exp (-(s : ℂ) * t) := by
            rw [← Complex.exp_add]; ring_nf
          rw [this]; ring
      _ = _ := by
          rw [hL, mul_assoc (Gamma b), ← mul_assoc ((s : ℂ) ^ (-b)), hpow]
          field_simp
  have hU := kummerU_laplace (a := a - b + 1) (b := 2 - b) (z := z) (by simp; linarith) hz
  rw [show (2 - b) - (a - b + 1) - 1 = -a by ring, show a - b + 1 - 1 = a - b by ring] at hU
  have hG1 : Gamma (a - b + 1) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hK := kummerU_kummer_transform_all a b hz0
  calc ∫ t : ℝ in Ioi 0, regularizedHGFun {a} {b} (-(t : ℂ)) * (t : ℂ) ^ (b - 1) / ((t : ℂ) + z)
      = ∫ t : ℝ in Ioi 0, ∫ s : ℝ in Ioi 0, G t s :=
        setIntegral_congr_fun measurableSet_Ioi fun t ht => (hsinner t ht).symm
    _ = ∫ s : ℝ in Ioi 0, ∫ t : ℝ in Ioi 0, G t s := integral_integral_swap hGi
    _ = ∫ s : ℝ in Ioi 0, exp (-z * s) * ((s : ℂ) ^ (a - b) * (1 + (s : ℂ)) ^ (-a)) :=
        setIntegral_congr_fun measurableSet_Ioi htinner
    _ = Gamma (a - b + 1) * kummerU (a - b + 1) (2 - b) z := by
        rw [hU]; field_simp
    _ = _ := by
        have hzz : z ^ (b - 1) * z ^ (1 - b) = 1 := by
          rw [← cpow_add _ _ hz0, show b - 1 + (1 - b) = 0 by ring, cpow_zero]
        rw [hK, show 1 + a - b = a - b + 1 by ring]
        linear_combination (-(Gamma (a - b + 1) * kummerU (a - b + 1) (2 - b) z)) * hzz

theorem cfInt_add_ne_zero {z : ℂ} (hz : z ∈ slitPlane) {t : ℝ} (ht : 0 ≤ t) : (t : ℂ) + z ≠ 0 := by
  obtain ⟨δ, hδ, hδb⟩ := exists_forall_le_norm_add_of_mem_slitPlane hz
  intro h
  have := hδb t ht z (Metric.mem_ball_self hδ)
  rw [h, norm_zero] at this; linarith

/-- A Stieltjes transform is holomorphic on the slit plane as soon as `g(t)/(t+1)` is integrable. -/
theorem cfInt_differentiableOn_stieltjes {g : ℝ → ℂ}
    (hg : IntegrableOn (fun t : ℝ => g t / ((t : ℂ) + 1)) (Ioi 0)) :
    DifferentiableOn ℂ (fun z => ∫ t : ℝ in Ioi 0, g t / ((t : ℂ) + z)) slitPlane := by
  set h : ℝ → ℂ := fun t => g t / ((t : ℂ) + 1) with hh
  have hS := differentiableOn_stieltjes_integral hg
  have hD : DifferentiableOn ℂ (fun z => (∫ t : ℝ in Ioi 0, h t) +
      (1 - z) * ∫ t : ℝ in Ioi 0, h t / ((t : ℂ) + z)) slitPlane :=
    (differentiableOn_const _).add ((differentiableOn_const _ |>.sub differentiableOn_id).mul hS)
  refine hD.congr fun z hz => ?_
  obtain ⟨δ, hδ, hδb⟩ := exists_forall_le_norm_add_of_mem_slitPlane hz
  have hint : IntegrableOn (fun t : ℝ => h t / ((t : ℂ) + z)) (Ioi 0) := by
    refine (hg.norm.const_mul δ⁻¹).mono' (hg.aestronglyMeasurable.mul
      (Measurable.aestronglyMeasurable (by fun_prop))) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_div, div_eq_mul_inv, mul_comm]
    gcongr
    exact hδb t (le_of_lt ht) z (Metric.mem_ball_self hδ)
  rw [← integral_const_mul, ← integral_add hg (hint.const_mul _)]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have h1 : (t : ℂ) + 1 ≠ 0 := cfInt_add_ne_zero one_mem_slitPlane (le_of_lt ht)
  have h2 : (t : ℂ) + z ≠ 0 := cfInt_add_ne_zero hz (le_of_lt ht)
  simp only [hh]
  field_simp
  ring

/-- The case `n = 0` of 13.4.6 on the slit plane. -/
theorem cfInt_stieltjes_zero {a b z : ℂ} (hz : z ∈ slitPlane) (hb : 0 < b.re)
    (hab : b.re < 1 + a.re) :
    ∫ t : ℝ in Ioi 0, regularizedHGFun {a} {b} (-(t : ℂ)) * (t : ℂ) ^ (b - 1) / ((t : ℂ) + z) =
      z ^ (b - 1) * Gamma (1 + a - b) * kummerU a b z := by
  have hS := cfInt_integrableOn_stieltjes (a := a) (b := b) (n := 0) one_mem_slitPlane
    (by simpa using hb) (by simp; linarith)
  simp only [CharP.cast_eq_zero, add_zero] at hS
  have hL := cfInt_differentiableOn_stieltjes hS
  have hLa : AnalyticOnNhd ℂ (fun z => ∫ t : ℝ in Ioi 0,
      regularizedHGFun {a} {b} (-(t : ℂ)) * (t : ℂ) ^ (b - 1) / ((t : ℂ) + z)) slitPlane :=
    hL.analyticOnNhd isOpen_slitPlane
  have hRa : AnalyticOnNhd ℂ (fun z => z ^ (b - 1) * Gamma (1 + a - b) * kummerU a b z)
      slitPlane := by
    refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) isOpen_slitPlane
    exact ((((differentiableAt_id.cpow (differentiableAt_const _) hw).mul_const _).mul
      ((differentiableOn_kummerU a b).differentiableAt (isOpen_slitPlane.mem_nhds hw)))).differentiableWithinAt
  have heq : (fun z => ∫ t : ℝ in Ioi 0,
      regularizedHGFun {a} {b} (-(t : ℂ)) * (t : ℂ) ^ (b - 1) / ((t : ℂ) + z)) =ᶠ[𝓝 1]
      fun z => z ^ (b - 1) * Gamma (1 + a - b) * kummerU a b z := by
    have hnh : {w : ℂ | 0 < w.re} ∈ 𝓝 (1 : ℂ) :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (by simp)
    filter_upwards [hnh] with w hw
    exact cfInt_stieltjes_zero_of_re_pos hw hb hab
  exact hLa.eqOn_of_preconnected_of_eventuallyEq hRa
    ((starConvex_one_slitPlane.isPathConnected one_mem_slitPlane).isConnected.isPreconnected)
    one_mem_slitPlane heq hz

/-- `b U(a,b+1,z) - a z U(a+1,b+2,z) = (b-a) U(a,b,z)`, from the contiguous relations 13.3.9
and 13.3.10; it is the Tricomi counterpart of 13.3.20 with `n = 1`. -/
theorem cfInt_kummerU_rel (a b : ℂ) {z : ℂ} (hz : z ≠ 0) :
    b * kummerU a (b + 1) z - a * z * kummerU (a + 1) (b + 2) z = (b - a) * kummerU a b z := by
  have h1 := kummerU_contiguous_shift_a (a + 1) (b + 1) z hz
  have h2 := kummerU_contiguous_a_b a (b + 1) z hz
  rw [add_sub_cancel_right, show b + 1 + 1 = b + 2 by ring] at h1
  rw [add_sub_cancel_right] at h2
  linear_combination a * h1 + (b - a) * h2

/-- 13.4.6 in the form `∫ 𝐌(a,b,-t) t^{b+n-1}/(t+z) dt = (-1)^n z^{b+n-1} Γ(1+a-b) U(a,b,z)`. -/
theorem cfInt_stieltjes_nat : ∀ n : ℕ, ∀ a b z : ℂ, z ∈ slitPlane → -b.re < n →
    (n : ℝ) < 1 + (a - b).re →
    ∫ t : ℝ in Ioi 0, regularizedHGFun {a} {b} (-(t : ℂ)) * (t : ℂ) ^ (b + n - 1) /
        ((t : ℂ) + z) =
      (-1) ^ n * z ^ (b + n - 1) * Gamma (1 + a - b) * kummerU a b z := by
  intro n
  induction n with
  | zero =>
    intro a b z hz h0 h1
    simp only [CharP.cast_eq_zero, add_zero, pow_zero, one_mul] at h0 h1 ⊢
    exact cfInt_stieltjes_zero hz (by linarith) (by simp at h1; linarith)
  | succ n ih =>
    intro a b z hz h0 h1
    have hz0 : z ≠ 0 := slitPlane_ne_zero hz
    push_cast at h0 h1
    have hab : (n : ℝ) < (a - b).re := by linarith
    have i1 := ih a (b + 1) z hz (by simp; linarith) (by simp at hab ⊢; linarith)
    have i2 := ih (a + 1) (b + 2) z hz (by simp; linarith) (by simp at hab ⊢; linarith)
    have I1 := cfInt_integrableOn_stieltjes (a := a) (b := b + 1) (n := n) hz
      (by simp; linarith) (by simp at hab ⊢; linarith)
    have I2 := cfInt_integrableOn_stieltjes (a := a + 1) (b := b + 2) (n := n) hz
      (by simp; linarith) (by simp at hab ⊢; linarith)
    have hpt : ∀ t ∈ Ioi (0 : ℝ), regularizedHGFun {a} {b} (-(t : ℂ)) *
        (t : ℂ) ^ (b + ((n + 1 : ℕ) : ℂ) - 1) / ((t : ℂ) + z) =
        b * (regularizedHGFun {a} {b + 1} (-(t : ℂ)) * (t : ℂ) ^ (b + 1 + n - 1) /
          ((t : ℂ) + z)) -
        a * (regularizedHGFun {a + 1} {b + 2} (-(t : ℂ)) * (t : ℂ) ^ (b + 2 + n - 1) /
          ((t : ℂ) + z)) := by
      intro t ht
      have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht)
      have hrel := regularizedConfluent_contiguous_mixed_b_pred a (b + 1) (-(t : ℂ))
      rw [add_sub_cancel_right, show b + 1 + 1 = b + 2 by ring] at hrel
      have hp : (t : ℂ) ^ (b + 2 + n - 1) = (t : ℂ) * (t : ℂ) ^ (b + 1 + n - 1) := by
        rw [show b + 2 + n - 1 = 1 + (b + 1 + n - 1) by ring, cpow_add _ _ ht0, cpow_one]
      rw [hp, show b + ((n + 1 : ℕ) : ℂ) - 1 = b + 1 + n - 1 by push_cast; ring]
      have h2 : (t : ℂ) + z ≠ 0 := cfInt_add_ne_zero hz (le_of_lt ht)
      field_simp
      linear_combination (-(t : ℂ) ^ (b + 1 + n - 1)) * hrel
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_sub (I1.const_mul _)
      (I2.const_mul _), integral_const_mul, integral_const_mul, i1, i2]
    have hrel := cfInt_kummerU_rel a b hz0
    have hG : Gamma (1 + a - b) = (a - b) * Gamma (a - b) := by
      rw [show 1 + a - b = (a - b) + 1 by ring, Gamma_add_one]
      intro h; rw [h] at hab; simp at hab; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hpz : z ^ (b + 2 + n - 1) = z * z ^ (b + 1 + n - 1) := by
      rw [show b + 2 + n - 1 = 1 + (b + 1 + n - 1) by ring, cpow_add _ _ hz0, cpow_one]
    rw [show b + ((n + 1 : ℕ) : ℂ) - 1 = b + 1 + n - 1 by push_cast; ring, hpz, hG,
      show 1 + a - (b + 1) = a - b by ring, show 1 + (a + 1) - (b + 2) = a - b by ring, pow_succ]
    linear_combination ((-1) ^ n * z ^ (b + 1 + n - 1) * Gamma (a - b)) * hrel

/-- Tricomi's Stieltjes representation 13.4.6, for every admissible `n`. The case `n = 0` is
Fubini against `1/(t+z) = ∫ e^{-(t+z)s} ds`, the Kummer Laplace transform 13.10.3 and
Tricomi's Laplace integral 13.4.4, continued from the right half-plane; the decay
`𝐌(a,b,-t) = O(t^{-Re a})` (`DLMF.Confluent.KummerDecay`) gives convergence. The step
`n ↦ n + 1` combines the contiguous relation 13.3.20 (`n = 1`) of `𝐌` with its Tricomi
counterpart `cfInt_kummerU_rel`. (Moved unchanged from `IntegralRepresentations`, which
precedes the Laplace transforms in the import order.) -/
@[dlmf 13.4.E6]
theorem kummerU_stieltjes_regularized {a b z : ℂ} (n : ℕ) (hz : z ∈ slitPlane)
    (hn0 : -b.re < n) (hn1 : (n : ℝ) < 1 + (a - b).re) :
    kummerU a b z =
      (-1 : ℂ) ^ n * z ^ (1 - b - n) / Gamma (1 + a - b) *
        ∫ t : ℝ in Set.Ioi 0,
          regularizedHGFun {b - a} {b} t * exp (-(t : ℂ)) * (t : ℂ) ^ (b + n - 1) /
            ((t : ℂ) + z) := by
  have hz0 := slitPlane_ne_zero hz
  have h := cfInt_stieltjes_nat n a b z hz hn0 hn1
  have hG : Gamma (1 + a - b) ≠ 0 := Gamma_ne_zero_of_re_pos (by
    simp only [sub_re, add_re, one_re] at hn1 ⊢; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have hcongr : ∀ t ∈ Ioi (0 : ℝ), regularizedHGFun {b - a} {b} t * exp (-(t : ℂ)) *
      (t : ℂ) ^ (b + n - 1) / ((t : ℂ) + z) =
      regularizedHGFun {a} {b} (-(t : ℂ)) * (t : ℂ) ^ (b + n - 1) / ((t : ℂ) + z) := by
    intro t _
    rw [regularizedConfluent_kummer_transform a b (-(t : ℂ)), neg_neg]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, h]
  have hzz : z ^ (1 - b - n) * z ^ (b + n - 1) = 1 := by
    rw [← cpow_add _ _ hz0, show 1 - b - n + (b + n - 1) = 0 by ring, cpow_zero]
  have hpm : ((-1 : ℂ) ^ n) * (-1) ^ n = 1 := by rw [← mul_pow]; simp
  calc kummerU a b z = ((-1 : ℂ) ^ n * (-1) ^ n) * (z ^ (1 - b - n) * z ^ (b + n - 1)) *
        (Gamma (1 + a - b) / Gamma (1 + a - b)) * kummerU a b z := by
        rw [hpm, hzz, div_self hG]; ring
    _ = _ := by ring

@[dlmf 13.16.E6]
theorem whittakerW_stieltjes {κ μ z : ℂ} (hz : z ∈ slitPlane)
    (hκ : (2 * μ.re) < (1 / 2 + μ - κ).re) (hκ0 : 0 < (1 / 2 + μ - κ).re) :
    whittakerW κ μ z =
      exp (-z / 2) * z ^ (κ + 1) /
          (Gamma (1 / 2 + μ - κ) * Gamma (1 / 2 - μ - κ)) *
        ∫ t : ℝ in Set.Ioi 0,
          whittakerW (-κ) μ t * exp (-(t : ℂ) / 2) * (t : ℂ) ^ (-κ - 1) /
            ((t : ℂ) + z) := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have hU := kummerU_stieltjes (a := 1 / 2 + μ - κ) (b := 1 + 2 * μ) hz
    (by simpa using hκ) hκ0
  rw [show 1 + (1 / 2 + μ - κ) - (1 + 2 * μ) = 1 / 2 - μ - κ by ring,
    show 1 + 2 * μ - (1 / 2 + μ - κ) = 1 / 2 + μ - (-κ) by ring] at hU
  have hint : ∀ t ∈ Ioi (0 : ℝ),
      whittakerW (-κ) μ t * exp (-(t : ℂ) / 2) * (t : ℂ) ^ (-κ - 1) / ((t : ℂ) + z) =
        kummerU (1 / 2 + μ - (-κ)) (1 + 2 * μ) t * exp (-(t : ℂ)) * (t : ℂ) ^ (1 / 2 + μ - κ - 1) /
          ((t : ℂ) + z) := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht)
    rw [whittakerW, show 1 / 2 + μ - κ - 1 = (1 / 2 + μ) + (-κ - 1) by ring,
      cpow_add (x := (t : ℂ)) (1 / 2 + μ) (-κ - 1) ht0]
    have he : exp (-(t : ℂ) / 2) * exp (-(t : ℂ) / 2) = exp (-(t : ℂ)) := by
      rw [← exp_add]; ring_nf
    rw [← he]; ring
  rw [setIntegral_congr_fun measurableSet_Ioi hint, whittakerW, hU]
  have hp : z ^ (1 / 2 + μ) * z ^ (1 - (1 / 2 + μ - κ)) = z ^ (κ + 1) := by
    rw [← cpow_add _ _ hz0]; ring_nf
  rw [← hp]; ring

end GaussStieltjes

/-!
### The Gaussian transform 13.10.6

Proof of 13.10.6 for real `z = ζ > 0`: subordinate `e^{-ζt}` to a Gaussian in `t` via the
`K_{1/2}` Schläfli integral, interchange the integrals (Fubini), evaluate the inner `t`-integral
by 13.10.3 with `s = t²`, apply Pfaff's transformation, and recognize the outer integral as
13.4.8 after `u ↦ 1/u`. The identity is then continued holomorphically to `Re z > 0`.
-/

section GaussTransform

open Set
open scoped Nat

/-- Subordination: `∫₀^∞ e^{-t²u - ζ²/(4u)} u^{-3/2} du = (2√π/ζ) e^{-ζt}` for `ζ, t > 0`. -/
theorem confLP_subordination {ζ t : ℝ} (hζ : 0 < ζ) (ht : 0 < t) :
    ∫ u : ℝ in Ioi 0, exp (-((t : ℂ) ^ 2 * u) - (ζ : ℂ) ^ 2 / (4 * u)) * (u : ℂ) ^ (-(3 / 2 : ℂ)) =
      2 * (Real.sqrt π : ℂ) / ζ * exp (-((ζ : ℂ) * t)) := by
  set y := ζ * t with hy
  have hy0 : 0 < y := mul_pos hζ ht
  have hK := besselK_ofReal_eq_integral_schlafli' hy0 (-(1 / 2))
  have hU := kummerU_besselK (-(1 / 2)) (y : ℂ) (ofReal_mem_slitPlane.mpr hy0)
  rw [show -(1 / 2 : ℂ) + 1 / 2 = 0 by ring, show 2 * (-(1 / 2 : ℂ)) + 1 = 0 by ring,
    kummerU_zero, neg_neg] at hU
  rw [neg_neg, show -(1 / 2 : ℂ) - 1 = -(3 / 2) by ring] at hK
  set J := ∫ s : ℝ in Ioi 0, exp (-(s : ℂ) - (y : ℂ) ^ 2 / (4 * s)) * (s : ℂ) ^ (-(3 / 2 : ℂ))
    with hJ
  have ht2 : 0 < t ^ 2 := by positivity
  have hsub := integral_comp_mul_left_Ioi
    (fun s : ℝ => exp (-(s : ℂ) - (y : ℂ) ^ 2 / (4 * s)) * (s : ℂ) ^ (-(3 / 2 : ℂ))) 0 ht2
  rw [mul_zero] at hsub
  have hpt : ∀ u ∈ Ioi (0:ℝ), exp (-((t : ℂ) ^ 2 * u) - (ζ : ℂ) ^ 2 / (4 * u)) *
      (u : ℂ) ^ (-(3 / 2 : ℂ)) = (t : ℂ) ^ 3 *
        (exp (-(((t ^ 2 * u : ℝ)) : ℂ) - (y : ℂ) ^ 2 / (4 * ((t ^ 2 * u : ℝ) : ℂ))) *
          (((t ^ 2 * u : ℝ)) : ℂ) ^ (-(3 / 2 : ℂ))) := by
    intro u hu
    have hu0 : (0:ℝ) < u := hu
    have htc : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
    have huc : (u : ℂ) ≠ 0 := ofReal_ne_zero.mpr hu0.ne'
    have hp : (((t ^ 2 * u : ℝ)) : ℂ) ^ (-(3 / 2 : ℂ)) =
        ((t : ℂ) ^ 3)⁻¹ * (u : ℂ) ^ (-(3 / 2 : ℂ)) := by
      have hp' : (((t ^ 2 : ℝ)) : ℂ) ^ (-(3 / 2 : ℂ)) = ((t : ℂ) ^ 3)⁻¹ := by
        rw [show (-(3 / 2 : ℂ)) = ((-(3 / 2) : ℝ) : ℂ) by push_cast; ring,
          ← ofReal_cpow (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul ht.le,
          show ((2 : ℕ) : ℝ) * (-(3 / 2)) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg ht.le,
          Real.rpow_natCast]
        push_cast; ring
      rw [ofReal_mul, mul_cpow_ofReal_nonneg (by positivity) hu0.le, hp']
    rw [hp]
    have he : -(((t ^ 2 * u : ℝ)) : ℂ) - (y : ℂ) ^ 2 / (4 * ((t ^ 2 * u : ℝ) : ℂ)) =
        -((t : ℂ) ^ 2 * u) - (ζ : ℂ) ^ 2 / (4 * u) := by
      rw [hy]; push_cast; field_simp
    rw [he]
    field_simp
  have hsq : (2 * (y : ℂ)) ^ (1 / 2 : ℂ) * ((y : ℂ) / 2) ^ (1 / 2 : ℂ) = y := by
    rw [show 2 * (y : ℂ) = ((2 * y : ℝ) : ℂ) by push_cast; ring,
      show (y : ℂ) / 2 = ((y / 2 : ℝ) : ℂ) by push_cast; ring,
      ← mul_cpow_ofReal_nonneg (by positivity) (by positivity), ← ofReal_mul,
      show 2 * y * (y / 2) = y ^ 2 by ring,
      show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow (by positivity),
      ← Real.rpow_natCast, ← Real.rpow_mul hy0.le]
    norm_num
  have hyc : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hy0.ne'
  have hsπ : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hJy : J * y * exp (y : ℂ) = 2 * (Real.sqrt π : ℂ) := by
    rw [hK] at hU
    have h1 : (Real.sqrt π : ℂ) * (1 / (Real.sqrt π : ℂ)) = 1 := mul_one_div_cancel hsπ
    linear_combination (-2 * (Real.sqrt π : ℂ)) * hU -
      (exp (y : ℂ) * (2 * (y : ℂ)) ^ (1 / 2 : ℂ) * ((y : ℂ) / 2) ^ (1 / 2 : ℂ) * J) * h1 -
      (J * exp (y : ℂ)) * hsq
  have hJv : J = 2 * (Real.sqrt π : ℂ) * exp (-(y : ℂ)) / y := by
    rw [← hJy, Complex.exp_neg]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul, hsub, ← hJ, hJv,
    real_smul, hy]
  have hζc : (ζ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hζ.ne'
  have htc : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  push_cast
  field_simp


/-- `(1+x)^m ≤ 2^m (1 + x^m)` for `x, m ≥ 0`. -/
theorem confLP_one_add_rpow_le {x m : ℝ} (hx : 0 ≤ x) (hm : 0 ≤ m) :
    (1 + x) ^ m ≤ 2 ^ m * (1 + x ^ m) := by
  rcases le_total x 1 with h | h
  · calc (1 + x) ^ m ≤ 2 ^ m := Real.rpow_le_rpow (by linarith) (by linarith) hm
      _ ≤ 2 ^ m * (1 + x ^ m) := le_mul_of_one_le_right (by positivity)
          (by linarith [Real.rpow_nonneg hx m])
  · calc (1 + x) ^ m ≤ (2 * x) ^ m := Real.rpow_le_rpow (by linarith) (by linarith) hm
      _ = 2 ^ m * x ^ m := Real.mul_rpow (by norm_num) hx
      _ ≤ 2 ^ m * (1 + x ^ m) := by gcongr; linarith

/-- A polynomial bound for the Gaussian-transform integrand. -/
theorem confLP_gauss_bound (a b : ℂ) : ∃ C m : ℝ, 0 ≤ m ∧ ∀ t : ℝ, 0 < t →
    ‖exp (-(t : ℂ) ^ 2) * (t : ℂ) ^ (2 * b - 2) * regularizedHGFun {a} {b} ((t : ℂ) ^ 2)‖ ≤
      C * (t ^ (2 * b.re - 2) + t ^ (2 * b.re - 2 + m)) := by
  obtain ⟨C, hC⟩ := exists_norm_regularizedHGFun_neg_le (b - a) b
  set γ := (b - a).re
  refine ⟨|C| * 2 ^ |γ|, 2 * |γ|, by positivity, fun t ht => ?_⟩
  have hs : (0:ℝ) ≤ t ^ 2 := by positivity
  have h1 := hC (t ^ 2) hs
  have hk : exp (-(t : ℂ) ^ 2) * regularizedHGFun {a} {b} ((t : ℂ) ^ 2) =
      regularizedHGFun {b - a} {b} (-((t ^ 2 : ℝ) : ℂ)) := by
    rw [regularizedConfluent_kummer_transform a b, ← mul_assoc, ← Complex.exp_add]
    push_cast; ring_nf; rw [Complex.exp_zero, one_mul]
  have e : exp (-(t : ℂ) ^ 2) * (t : ℂ) ^ (2 * b - 2) * regularizedHGFun {a} {b} ((t : ℂ) ^ 2) =
      (t : ℂ) ^ (2 * b - 2) * regularizedHGFun {b - a} {b} (-((t ^ 2 : ℝ) : ℂ)) := by
    rw [← hk]; ring
  rw [e, norm_mul, kumDec_norm_cpow_ofReal ht]
  simp only [sub_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]
  have h2 : (1 + t ^ 2) ^ (-γ) ≤ 2 ^ |γ| * (1 + t ^ (2 * |γ|)) := by
    calc (1 + t ^ 2) ^ (-γ) ≤ (1 + t ^ 2) ^ |γ| :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (neg_le_abs γ)
      _ ≤ 2 ^ |γ| * (1 + (t ^ 2) ^ |γ|) := confLP_one_add_rpow_le hs (abs_nonneg γ)
      _ = 2 ^ |γ| * (1 + t ^ (2 * |γ|)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]; norm_num
  have htp : 0 < t ^ (2 * b.re - 2) := Real.rpow_pos_of_pos ht _
  calc t ^ (2 * b.re - 2) * ‖regularizedHGFun {b - a} {b} (-((t ^ 2 : ℝ) : ℂ))‖
      ≤ t ^ (2 * b.re - 2) * (|C| * (2 ^ |γ| * (1 + t ^ (2 * |γ|)))) := by
        gcongr
        calc _ ≤ C * (1 + t ^ 2) ^ (-γ) := h1
          _ ≤ |C| * (1 + t ^ 2) ^ (-γ) := by gcongr; exact le_abs_self C
          _ ≤ _ := by gcongr
    _ = _ := by
        rw [Real.rpow_add ht]; ring

/-- Integrability of the 13.10.6 integrand for `0 < re z`. -/
theorem confLP_gauss_integrableOn {a b z : ℂ} (hb : (1 / 2 : ℝ) < b.re) (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => exp (-z * t - (t : ℂ) ^ 2) * (t : ℂ) ^ (2 * b - 2) *
      regularizedHGFun {a} {b} ((t : ℂ) ^ 2)) (Ioi 0) := by
  obtain ⟨C, m, hm, hC⟩ := confLP_gauss_bound a b
  have hI1 := cfInt_integrableOn_rpow_exp (r := 2 * b.re - 2) (by linarith) hz
  have hI2 := cfInt_integrableOn_rpow_exp (r := 2 * b.re - 2 + m) (by linarith) hz
  refine ((hI1.add hI2).const_mul C).mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ContinuousOn.mul (ContinuousOn.mul (by fun_prop) ?_) ?_
    · exact ContinuousOn.cpow continuous_ofReal.continuousOn continuousOn_const
        fun t ht => ofReal_mem_slitPlane.mpr ht
    · exact (continuous_regularizedConfluent.comp (by fun_prop :
        Continuous fun t : ℝ => (a, b, (t : ℂ) ^ 2))).continuousOn
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0:ℝ) < t := ht
    have e : exp (-z * t - (t : ℂ) ^ 2) * (t : ℂ) ^ (2 * b - 2) *
        regularizedHGFun {a} {b} ((t : ℂ) ^ 2) = exp (-z * t) * (exp (-(t : ℂ) ^ 2) *
        (t : ℂ) ^ (2 * b - 2) * regularizedHGFun {a} {b} ((t : ℂ) ^ 2)) := by
      rw [sub_eq_add_neg, Complex.exp_add]; ring
    rw [e, norm_mul, Complex.norm_exp]
    have : (-z * t).re = -(z.re * t) := by simp
    rw [this]
    calc Real.exp (-(z.re * t)) * ‖exp (-(t : ℂ) ^ 2) * (t : ℂ) ^ (2 * b - 2) *
          regularizedHGFun {a} {b} ((t : ℂ) ^ 2)‖
        ≤ Real.exp (-(z.re * t)) * (C * (t ^ (2 * b.re - 2) + t ^ (2 * b.re - 2 + m))) := by
          gcongr; exact hC t ht0
      _ = _ := by simp only [Pi.add_apply]; ring


/-- `((x²:ℝ):ℂ)^w = x^{2w}` for `x > 0`. -/
theorem confLP_sq_cpow {x : ℝ} (hx : 0 < x) (w : ℂ) :
    (((x ^ 2 : ℝ)) : ℂ) ^ w = (x : ℂ) ^ (2 * w) := by
  have hxc : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  rw [sq, ofReal_mul, mul_cpow_ofReal_nonneg hx.le hx.le, ← cpow_add _ _ hxc]; ring_nf

/-- The inner `t`-integral of 13.10.6: a Kummer Laplace transform after `s = t²`. -/
theorem confLP_gauss_inner {a b : ℂ} (hb : (1 / 2 : ℝ) < b.re) {u : ℝ} (hu : 0 < u) :
    ∫ t : ℝ in Ioi 0, exp (-(t : ℂ) ^ 2) * (t : ℂ) ^ (2 * b - 2) *
        regularizedHGFun {a} {b} ((t : ℂ) ^ 2) * exp (-((t : ℂ) ^ 2 * u)) =
      1 / 2 * (Gamma (b - 1 / 2) * (((1 + u : ℝ)) : ℂ) ^ (-(b - 1 / 2)) *
        DLMF.Hypergeometric.regularizedGaussHG a (b - 1 / 2) b (1 / ((1 + u : ℝ) : ℂ))) := by
  have hL := laplace_regularizedHGFun (a := a) (b := b - 1 / 2) (c := b) (k := 1)
    (z := ((1 + u : ℝ) : ℂ)) (by simp; linarith) (by simp; linarith) (by simp; linarith)
  rw [← hL, ← integral_const_mul]
  set g : ℝ → ℂ := fun s => 1 / 2 * (exp (-((1 + u : ℝ) : ℂ) * s) * (s : ℂ) ^ (b - 1 / 2 - 1) *
    regularizedHGFun {a} {b} (1 * s)) with hg
  have hsub := integral_comp_rpow_Ioi g (p := 2) two_ne_zero
  rw [← hsub]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : (0:ℝ) < t := ht
  have htc : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht0.ne'
  simp only [hg, real_smul]
  rw [show t ^ (2:ℝ) = t ^ 2 by norm_cast, confLP_sq_cpow ht0, show (2:ℝ) - 1 = 1 by norm_num,
    Real.rpow_one, abs_two]
  have hp : (t : ℂ) * (t : ℂ) ^ (2 * (b - 1 / 2 - 1)) = (t : ℂ) ^ (2 * b - 2) := by
    conv_lhs => arg 1; rw [← cpow_one (t : ℂ)]
    rw [← cpow_add _ _ htc]; ring_nf
  have he : exp (-(t : ℂ) ^ 2) * exp (-((t : ℂ) ^ 2 * u)) =
      exp (-((1 + u : ℝ) : ℂ) * ((t ^ 2 : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]; push_cast; ring_nf
  push_cast
  rw [← hp]
  push_cast at he
  rw [← he]
  ring

/-- Pfaff's transformation in the form used for 13.10.6. -/
theorem confLP_gauss_pfaff (a b : ℂ) {u : ℝ} (hu : 0 < u) :
    (((1 + u : ℝ)) : ℂ) ^ (-(b - 1 / 2)) *
        DLMF.Hypergeometric.regularizedGaussHG a (b - 1 / 2) b (1 / ((1 + u : ℝ) : ℂ)) =
      (u : ℂ) ^ (-(b - 1 / 2)) *
        DLMF.Hypergeometric.regularizedGaussHG (b - 1 / 2) (b - a) b (-(1 / (u : ℂ))) := by
  have h1u : (0:ℝ) < 1 + u := by linarith
  have hw : (1 / ((1 + u : ℝ) : ℂ)) ∈ DLMF.Hypergeometric.cutPlane := by
    rw [DLMF.Hypergeometric.mem_cutPlane]
    have h1c' : (1 : ℂ) + u ≠ 0 := by exact_mod_cast h1u.ne'
    rw [show (1 : ℂ) - 1 / ((1 + u : ℝ) : ℂ) = ((u / (1 + u) : ℝ) : ℂ) by
      push_cast; field_simp [h1c']; ring]
    exact ofReal_mem_slitPlane.mpr (by positivity)
  rw [DLMF.Hypergeometric.regularizedGaussHG_symm _ _ _ hw,
    DLMF.Hypergeometric.regularizedGaussHG_pfaff _ _ _ hw]
  have huc : (u : ℂ) ≠ 0 := ofReal_ne_zero.mpr hu.ne'
  have h1c : ((1 + u : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr h1u.ne'
  have h1c' : (1 : ℂ) + u ≠ 0 := by exact_mod_cast h1u.ne'
  have harg : (1 / ((1 + u : ℝ) : ℂ)) / (1 / ((1 + u : ℝ) : ℂ) - 1) = -(1 / (u : ℂ)) := by
    push_cast
    rw [div_sub_one h1c', div_div_div_cancel_right₀ h1c', show (1 : ℂ) - (1 + u) = -u by ring,
      div_neg]
  have h1w : (1 : ℂ) - 1 / ((1 + u : ℝ) : ℂ) = (u : ℂ) * (((1 + u : ℝ)) : ℂ)⁻¹ := by
    push_cast
    rw [one_div, ← div_eq_mul_inv, eq_div_iff h1c', sub_mul, inv_mul_cancel₀ h1c']; ring
  rw [harg, h1w, ← ofReal_inv, mul_cpow_ofReal_nonneg hu.le (by positivity), ofReal_inv,
    inv_cpow _ _ (by rw [arg_ofReal_of_nonneg h1u.le]; exact Real.pi_ne_zero.symm)]
  have hne : (((1 + u : ℝ)) : ℂ) ^ (-(b - 1 / 2)) ≠ 0 := by
    rw [cpow_def_of_ne_zero h1c]; exact exp_ne_zero _
  rw [show ∀ X Y Z : ℂ, X * (Y * X⁻¹ * Z) = X * X⁻¹ * (Y * Z) by intros; ring,
    mul_inv_cancel₀ hne, one_mul]


/-- The outer `u`-integral of 13.10.6: after `u = 1/v` it is Tricomi's Gauss-type integral 13.4.8. -/
theorem confLP_gauss_outer {a b : ℂ} (hb : (1 / 2 : ℝ) < b.re) {ζ : ℝ} (hζ : 0 < ζ) :
    ∫ u : ℝ in Ioi 0, exp (-(ζ : ℂ) ^ 2 / (4 * u)) * (u : ℂ) ^ (-(3 / 2 : ℂ)) *
        ((u : ℂ) ^ (-(b - 1 / 2)) *
          DLMF.Hypergeometric.regularizedGaussHG (b - 1 / 2) (b - a) b (-(1 / (u : ℂ)))) =
      2 / ζ * kummerU (b - 1 / 2) (a + 1 / 2) ((ζ : ℂ) ^ 2 / 4) := by
  set y : ℂ := (ζ : ℂ) ^ 2 / 4 with hy
  have hyr : y = (((ζ / 2) ^ 2 : ℝ) : ℂ) := by rw [hy]; push_cast; ring
  have hy0 : 0 < y.re := by rw [hyr, ofReal_re]; positivity
  have hU := kummerU_gauss (a := b - 1 / 2) (b := a + 1 / 2) (c := b) (z := y)
    (by linarith) hy0
  rw [show b - 1 / 2 - (a + 1 / 2) + 1 = b - a by ring, show b - (b - 1 / 2) = 1 / 2 by ring] at hU
  have hsq : y ^ (1 / 2 : ℂ) = (ζ : ℂ) / 2 := by
    rw [hyr, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow (by positivity),
      ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  rw [hU, hsq]
  set g : ℝ → ℂ := fun u => exp (-(ζ : ℂ) ^ 2 / (4 * u)) * (u : ℂ) ^ (-(3 / 2 : ℂ)) *
        ((u : ℂ) ^ (-(b - 1 / 2)) *
          DLMF.Hypergeometric.regularizedGaussHG (b - 1 / 2) (b - a) b (-(1 / (u : ℂ)))) with hg
  have hsub := integral_comp_rpow_Ioi g (p := -1) (by norm_num)
  rw [← hsub]
  have hζc : (ζ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hζ.ne'
  rw [show 2 / (ζ : ℂ) * ((ζ : ℂ) / 2 * ∫ t : ℝ in Ioi 0, exp (-y * t) * (t : ℂ) ^ (b - 1) *
      DLMF.Hypergeometric.regularizedGaussHG (b - 1 / 2) (b - a) b (-(t : ℂ))) =
      ∫ t : ℝ in Ioi 0, exp (-y * t) * (t : ℂ) ^ (b - 1) *
      DLMF.Hypergeometric.regularizedGaussHG (b - 1 / 2) (b - a) b (-(t : ℂ)) by field_simp]
  refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
  have hv0 : (0:ℝ) < v := hv
  have hvc : (v : ℂ) ≠ 0 := ofReal_ne_zero.mpr hv0.ne'
  have hargv : (v : ℂ).arg ≠ π := by rw [arg_ofReal_of_nonneg hv0.le]; exact Real.pi_ne_zero.symm
  simp only [hg, real_smul]
  rw [Real.rpow_neg_one, abs_neg, abs_one, one_mul, show (-1 : ℝ) - 1 = -2 by norm_num]
  have h2 : ((v ^ (-2 : ℝ) : ℝ) : ℂ) = (v : ℂ) ^ (-2 : ℂ) := by
    rw [ofReal_cpow hv0.le]; norm_num
  have hinv : ∀ w : ℂ, ((v⁻¹ : ℝ) : ℂ) ^ w = (v : ℂ) ^ (-w) := fun w => by
    rw [ofReal_inv, inv_cpow _ _ hargv, cpow_neg]
  rw [h2, hinv, hinv, ofReal_inv, show (1 : ℂ) / (v : ℂ)⁻¹ = v by rw [one_div, inv_inv]]
  have hp : (v : ℂ) ^ (-2 : ℂ) * ((v : ℂ) ^ (-(-(3 / 2 : ℂ))) * (v : ℂ) ^ (-(-(b - 1 / 2)))) =
      (v : ℂ) ^ (b - 1) := by
    rw [← cpow_add _ _ hvc, ← cpow_add _ _ hvc]; ring_nf
  have he : exp (-(ζ : ℂ) ^ 2 / (4 * (v : ℂ)⁻¹)) = exp (-y * v) := by
    rw [hy]; congr 1; field_simp
  rw [he, ← hp]
  ring


/-- `π^{-1/2} = 1/√π` as complex numbers. -/
theorem confLP_pi_cpow_neg_half : (π : ℂ) ^ (-(1 / 2 : ℂ)) = ((Real.sqrt π)⁻¹ : ℝ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg Real.pi_pos.le, ofReal_cpow Real.pi_pos.le]
  push_cast; ring_nf

/-- 13.10.6 for real positive `z`, by subordination and Fubini. -/
theorem confLP_gauss_real {a b : ℂ} (hb : (1 / 2 : ℝ) < b.re) {ζ : ℝ} (hζ : 0 < ζ) :
    ∫ t : ℝ in Ioi 0, exp (-(ζ : ℂ) * t - (t : ℂ) ^ 2) * (t : ℂ) ^ (2 * b - 2) *
        regularizedHGFun {a} {b} ((t : ℂ) ^ 2) =
      (1 / 2) * (π : ℂ) ^ (-(1 / 2 : ℂ)) * Gamma (b - 1 / 2) *
        kummerU (b - 1 / 2) (a + 1 / 2) ((ζ : ℂ) ^ 2 / 4) := by
  set c : ℝ → ℂ := fun t => exp (-(t : ℂ) ^ 2) * (t : ℂ) ^ (2 * b - 2) *
    regularizedHGFun {a} {b} ((t : ℂ) ^ 2) with hc
  set k : ℝ → ℝ → ℂ := fun t u => exp (-((t : ℂ) ^ 2 * u) - (ζ : ℂ) ^ 2 / (4 * u)) *
    (u : ℂ) ^ (-(3 / 2 : ℂ)) with hk
  set G : ℝ → ℝ → ℂ := fun t u => c t * k t u with hG
  have hsπ : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hζc : (ζ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hζ.ne'
  have hS : ∀ t : ℝ, 0 < t → ∫ u : ℝ in Ioi 0, k t u =
      2 * (Real.sqrt π : ℂ) / ζ * exp (-((ζ : ℂ) * t)) := fun t ht => confLP_subordination hζ ht
  have hpt : ∀ t ∈ Ioi (0:ℝ), exp (-(ζ : ℂ) * t - (t : ℂ) ^ 2) * (t : ℂ) ^ (2 * b - 2) *
      regularizedHGFun {a} {b} ((t : ℂ) ^ 2) =
      (ζ / (2 * Real.sqrt π) : ℂ) * ∫ u : ℝ in Ioi 0, G t u := by
    intro t ht
    simp only [hG]
    rw [integral_const_mul, hS t ht]
    simp only [hc]
    rw [sub_eq_add_neg, Complex.exp_add, show -(ζ : ℂ) * t = -((ζ : ℂ) * t) by ring]
    field_simp
  -- Fubini
  have hcm : Measurable c := by
    simp only [hc]
    exact (by fun_prop : Measurable fun t : ℝ => exp (-(t : ℂ) ^ 2) * (t : ℂ) ^ (2 * b - 2)).mul
      (continuous_regularizedConfluent.comp (by fun_prop :
        Continuous fun t : ℝ => (a, b, (t : ℂ) ^ 2))).measurable
  have hkm : Measurable (Function.uncurry k) := by
    simp only [hk]; fun_prop
  have hm : AEStronglyMeasurable (Function.uncurry G)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) :=
    ((hcm.comp measurable_fst).mul hkm).aestronglyMeasurable
  have hkR : ∀ t : ℝ, ∀ u ∈ Ioi (0:ℝ), k t u =
      ((Real.exp (-(t ^ 2 * u) - ζ ^ 2 / (4 * u)) * u ^ (-(3 / 2) : ℝ) : ℝ) : ℂ) := by
    intro t u hu
    have hu0 : (0:ℝ) < u := hu
    simp only [hk]
    rw [ofReal_mul, ofReal_exp, ofReal_cpow hu0.le]
    push_cast; ring_nf
  have hGi : Integrable (Function.uncurry G)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
    refine (integrable_prod_iff hm).mpr ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have hne : ∫ u : ℝ in Ioi 0, k t u ≠ 0 := by
        rw [hS t ht]
        exact mul_ne_zero (div_ne_zero (mul_ne_zero two_ne_zero hsπ) hζc) (exp_ne_zero _)
      exact (confLP_integrableOn_of_ne_zero hne).const_mul (c t)
    · have hI := (confLP_gauss_integrableOn (a := a) (z := (ζ : ℂ)) hb (by simpa using hζ)).norm
      refine IntegrableOn.congr_fun (hI.const_mul (2 * Real.sqrt π / ζ)) (fun t ht => ?_)
        measurableSet_Ioi
      have ht0 : (0:ℝ) < t := ht
      simp only [Function.uncurry_apply_pair, hG, norm_mul]
      rw [integral_const_mul, confLP_setIntegral_norm_of_ofReal measurableSet_Ioi (hkR t)
        (fun u hu => mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (le_of_lt hu) _)), hS t ht0]
      rw [sub_eq_add_neg, Complex.exp_add, show -(ζ : ℂ) * t = -((ζ : ℂ) * t) by ring]
      simp only [hc, norm_mul, norm_div, Complex.norm_real, Complex.norm_ofNat]
      rw [Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_of_nonneg hζ.le]
      ring
  have hinner : ∀ u ∈ Ioi (0:ℝ), ∫ t : ℝ in Ioi 0, G t u =
      1 / 2 * Gamma (b - 1 / 2) * (exp (-(ζ : ℂ) ^ 2 / (4 * u)) * (u : ℂ) ^ (-(3 / 2 : ℂ)) *
        ((u : ℂ) ^ (-(b - 1 / 2)) *
          DLMF.Hypergeometric.regularizedGaussHG (b - 1 / 2) (b - a) b (-(1 / (u : ℂ))))) := by
    intro u hu
    have hu0 : (0:ℝ) < u := hu
    have h := confLP_gauss_inner (a := a) hb hu0
    rw [mul_assoc (Gamma _), confLP_gauss_pfaff a b hu0] at h
    have e : ∀ t : ℝ, G t u = (exp (-(ζ : ℂ) ^ 2 / (4 * u)) * (u : ℂ) ^ (-(3 / 2 : ℂ))) *
        (exp (-(t : ℂ) ^ 2) * (t : ℂ) ^ (2 * b - 2) * regularizedHGFun {a} {b} ((t : ℂ) ^ 2) *
          exp (-((t : ℂ) ^ 2 * u))) := by
      intro t
      simp only [hG, hc, hk]
      rw [show -((t : ℂ) ^ 2 * u) - (ζ : ℂ) ^ 2 / (4 * u) =
        -((t : ℂ) ^ 2 * u) + -(ζ : ℂ) ^ 2 / (4 * u) by ring, Complex.exp_add]
      ring
    simp_rw [e]
    rw [integral_const_mul, h]
    ring
  calc ∫ t : ℝ in Ioi 0, exp (-(ζ : ℂ) * t - (t : ℂ) ^ 2) * (t : ℂ) ^ (2 * b - 2) *
        regularizedHGFun {a} {b} ((t : ℂ) ^ 2)
      = ∫ t : ℝ in Ioi 0, (ζ / (2 * Real.sqrt π) : ℂ) * ∫ u : ℝ in Ioi 0, G t u :=
        setIntegral_congr_fun measurableSet_Ioi hpt
    _ = (ζ / (2 * Real.sqrt π) : ℂ) * ∫ u : ℝ in Ioi 0, ∫ t : ℝ in Ioi 0, G t u := by
        rw [integral_const_mul, integral_integral_swap hGi]
    _ = (ζ / (2 * Real.sqrt π) : ℂ) * (1 / 2 * Gamma (b - 1 / 2) *
          (2 / ζ * kummerU (b - 1 / 2) (a + 1 / 2) ((ζ : ℂ) ^ 2 / 4))) := by
        rw [setIntegral_congr_fun measurableSet_Ioi hinner, integral_const_mul,
          confLP_gauss_outer hb hζ]
    _ = _ := by
        rw [confLP_pi_cpow_neg_half]
        push_cast
        field_simp


/-- The integrand of 13.10.6 factors as `e^{-z t}` times a `z`-independent part. -/
theorem confLP_gauss_factor (a b z : ℂ) (t : ℝ) :
    exp (-z * t - (t : ℂ) ^ 2) * (t : ℂ) ^ (2 * b - 2) * regularizedHGFun {a} {b} ((t : ℂ) ^ 2) =
      exp (-z * t) * (exp (-(t : ℂ) ^ 2) * (t : ℂ) ^ (2 * b - 2) *
        regularizedHGFun {a} {b} ((t : ℂ) ^ 2)) := by
  rw [sub_eq_add_neg, Complex.exp_add]; ring

/-- Holomorphic dependence of the Gaussian transform of `𝐌` on `z`. -/
theorem confLP_gauss_differentiableOn {a b : ℂ} (hb : (1 / 2 : ℝ) < b.re) :
    DifferentiableOn ℂ (fun z : ℂ => ∫ t : ℝ in Ioi 0,
      exp (-z * t - (t : ℂ) ^ 2) * (t : ℂ) ^ (2 * b - 2) *
        regularizedHGFun {a} {b} ((t : ℂ) ^ 2)) {z : ℂ | 0 < z.re} := by
  intro z₀ hz₀
  change 0 < z₀.re at hz₀
  let δ : ℝ := z₀.re / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hre (z : ℂ) (hz : z ∈ Metric.ball z₀ δ) : δ < z.re := by
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have hh := (abs_lt.mp ((abs_re_le_norm (z - z₀)).trans_lt hz)).1
    simp only [sub_re] at hh
    dsimp [δ] at *
    linarith
  obtain ⟨C, m, hm, hC⟩ := confLP_gauss_bound a b
  let Q (t : ℝ) : ℂ := exp (-(t : ℂ) ^ 2) * (t : ℂ) ^ (2 * b - 2) *
    regularizedHGFun {a} {b} ((t : ℂ) ^ 2)
  let F (z : ℂ) (t : ℝ) : ℂ := exp (-z * t - (t : ℂ) ^ 2) * (t : ℂ) ^ (2 * b - 2) *
    regularizedHGFun {a} {b} ((t : ℂ) ^ 2)
  let r : ℝ := 2 * b.re - 2
  let bd (t : ℝ) : ℝ := C * (t ^ (r + 1) * Real.exp (-(δ * t)) +
    t ^ (r + 1 + m) * Real.exp (-(δ * t)))
  have hbd : IntegrableOn bd (Ioi 0) := by
    have h1 := cfInt_integrableOn_rpow_exp (r := r + 1) (by dsimp [r]; linarith) hδ
    have h2 := cfInt_integrableOn_rpow_exp (r := r + 1 + m) (by dsimp [r]; linarith) hδ
    exact (h1.add h2).const_mul C
  have hmeas : ∀ᶠ z in 𝓝 z₀, AEStronglyMeasurable (F z) (volume.restrict (Ioi 0)) := by
    filter_upwards [Metric.ball_mem_nhds _ hδ] with z hz
    exact (confLP_gauss_integrableOn (a := a) hb (hδ.trans (hre z hz))).aestronglyMeasurable
  have hF0 : Integrable (F z₀) (volume.restrict (Ioi 0)) := confLP_gauss_integrableOn hb hz₀
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi 0)) (F := F) (F' := fun z t => -(t : ℂ) * F z t)
    (bound := bd) (Metric.ball_mem_nhds _ hδ) hmeas hF0
    ((by fun_prop : Measurable fun t : ℝ => -(t : ℂ)).aestronglyMeasurable.mul
      hF0.aestronglyMeasurable) ?_ hbd ?_
  · exact hd.2.differentiableAt.differentiableWithinAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht z hz
    change 0 < t at ht
    have he : Real.exp (-z.re * t) ≤ Real.exp (-(δ * t)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hre z hz]
    have hQ := hC t ht
    have hp1 : t * t ^ r = t ^ (r + 1) := by
      rw [Real.rpow_add_one ht.ne']; ring
    have hp2 : t * t ^ (r + m) = t ^ (r + 1 + m) := by
      rw [show r + 1 + m = (r + m) + 1 by ring, Real.rpow_add_one ht.ne']; ring
    dsimp only [F]
    rw [confLP_gauss_factor, norm_mul, norm_mul, norm_neg, Complex.norm_real,
      Real.norm_of_nonneg ht.le, Complex.norm_exp]
    simp only [neg_mul, neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    calc t * (Real.exp (-(z.re * t)) * ‖Q t‖)
        ≤ t * (Real.exp (-(δ * t)) * (C * (t ^ r + t ^ (r + m)))) := by
          have : Real.exp (-(z.re * t)) ≤ Real.exp (-(δ * t)) := by simpa [neg_mul] using he
          gcongr
      _ = bd t := by
          dsimp only [bd]
          rw [← hp1, ← hp2]; ring
  · filter_upwards with t z _
    have hh := (((((hasDerivAt_id z).neg.mul_const (t : ℂ)).sub_const
      ((t : ℂ) ^ 2)).cexp.mul_const ((t : ℂ) ^ (2 * b - 2))).mul_const
      (regularizedHGFun {a} {b} ((t : ℂ) ^ 2)))
    simp only [Pi.neg_apply, id_eq] at hh
    convert hh using 1
    dsimp only [F]
    ring

/-- **DLMF 13.10.6** (proof). -/
theorem confLP_gauss {a b z : ℂ} (hb : (1 / 2 : ℝ) < b.re) (hz : 0 < z.re) :
    ∫ t : ℝ in Ioi 0,
        exp (-z * t - (t : ℂ) ^ 2) * (t : ℂ) ^ (2 * b - 2) *
          regularizedHGFun {a} {b} ((t : ℂ) ^ 2) =
      (1 / 2) * (π : ℂ) ^ (-(1 / 2 : ℂ)) * Gamma (b - 1 / 2) *
        kummerU (b - 1 / 2) (a + 1 / 2) (z ^ 2 / 4) := by
  let V : Set ℂ := {z | 0 < z.re}
  have hVo : IsOpen V := isOpen_lt continuous_const continuous_re
  have hJ : AnalyticOnNhd ℂ (fun z : ℂ => ∫ t : ℝ in Ioi 0,
      exp (-z * t - (t : ℂ) ^ 2) * (t : ℂ) ^ (2 * b - 2) *
        regularizedHGFun {a} {b} ((t : ℂ) ^ 2)) V :=
    (confLP_gauss_differentiableOn hb).analyticOnNhd hVo
  have hU : AnalyticOnNhd ℂ (fun z : ℂ => (1 / 2) * (π : ℂ) ^ (-(1 / 2 : ℂ)) *
      Gamma (b - 1 / 2) * kummerU (b - 1 / 2) (a + 1 / 2) (z ^ 2 / 4)) V := by
    apply DifferentiableOn.analyticOnNhd _ hVo
    intro w hw
    have hw0 : 0 < w.re := hw
    have hw' : w ^ 2 / 4 ∈ slitPlane := by
      have hre : (w ^ 2 / 4).re = (w.re ^ 2 - w.im ^ 2) / 4 := by
        rw [Complex.div_ofNat_re]; simp [sq]
      have him : (w ^ 2 / 4).im = 2 * w.re * w.im / 4 := by
        rw [Complex.div_ofNat_im]; simp [sq]; ring
      rw [mem_slitPlane_iff]
      by_cases hy : w.im = 0
      · left; rw [hre, hy]; nlinarith
      · right; rw [him]; exact div_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hw0.ne') hy)
          (by norm_num)
    exact (((differentiableAt_kummerU (b - 1 / 2) (a + 1 / 2) hw').comp (f := fun z : ℂ => z ^ 2 / 4) w
      (by fun_prop)).const_mul
      ((1 / 2) * (π : ℂ) ^ (-(1 / 2 : ℂ)) * Gamma (b - 1 / 2))).differentiableWithinAt
  have hfreq : ∃ᶠ w in 𝓝[≠] ((1 : ℝ) : ℂ), (fun z : ℂ => ∫ t : ℝ in Ioi 0,
      exp (-z * t - (t : ℂ) ^ 2) * (t : ℂ) ^ (2 * b - 2) *
        regularizedHGFun {a} {b} ((t : ℂ) ^ 2)) w =
      (fun z : ℂ => (1 / 2) * (π : ℂ) ^ (-(1 / 2 : ℂ)) *
        Gamma (b - 1 / 2) * kummerU (b - 1 / 2) (a + 1 / 2) (z ^ 2 / 4)) w := by
    have ht : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[≠] (1:ℝ)) (𝓝[≠] ((1:ℝ) : ℂ)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · exact (continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with r hr
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, ofReal_inj] using hr
    apply ht.frequently
    apply Eventually.frequently
    filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds (zero_lt_one' ℝ))] with r hr
    exact confLP_gauss_real hb hr
  exact hJ.eqOn_of_preconnected_of_frequently_eq hU (convex_halfSpace_re_gt 0).isPreconnected
    (by change 0 < ((1:ℝ) : ℂ).re; simp) hfreq hz

end GaussTransform

/-- A Gaussian-weighted Laplace transform of `𝐌`; it converges for `0 < Re z`.
It is placed after the Stieltjes section because its proof uses 13.4.8. -/
@[dlmf 13.10.E6]
theorem gauss_regularizedHGFun {a b z : ℂ} (hb : (1 / 2 : ℝ) < b.re) (hz : 0 < z.re) :
    ∫ t : ℝ in Set.Ioi 0,
        exp (-z * t - (t : ℂ) ^ 2) * (t : ℂ) ^ (2 * b - 2) *
          regularizedHGFun {a} {b} ((t : ℂ) ^ 2) =
      (1 / 2) * (π : ℂ) ^ (-(1 / 2 : ℂ)) * Gamma (b - 1 / 2) *
        kummerU (b - 1 / 2) (a + 1 / 2) (z ^ 2 / 4) :=
  confLP_gauss hb hz

end DLMF.Confluent
