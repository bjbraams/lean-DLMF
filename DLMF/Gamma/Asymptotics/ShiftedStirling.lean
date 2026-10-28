/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Gamma.Asymptotics.Stirling

/-!
# Shifted complex Stirling expansions

Complex Laplace representations and exponentiation of the shifted Stirling expansion.

Source references and common attribution are retained in
`DLMF.Gamma.Asymptotics`.
-/

@[expose] public section

open Complex Filter MeasureTheory

open scoped Real Topology

open DLMF.Hypergeometric

noncomputable section

namespace DLMF.Gamma

section ShiftedStirling

/-! ### The shifted Stirling expansion and the Gamma-ratio expansion

DLMF 5.11.8 is proved for complex shifts `a` along the positive real axis. Binet's function
is written in Laplace form `μ(t + a) = ∫₀^∞ e^{-ts} e^{-as} β(s)/s ds`, and Watson's lemma
applies to the kernel `e^{-as} β(s)/s`, whose Taylor coefficients at `0⁺` are a Cauchy
product of exponential and Bernoulli coefficients. The elementary part
`(t + a - 1/2) log(1 + a/t) - a` is expanded with `logTaylor`. Collecting coefficients gives
the Bernoulli polynomials. Exponentiating the difference of two such expansions gives
5.11.13 with the coefficients of `stirlingRatioG`. -/

open Set Asymptotics
open scoped Nat

/-! ### Expansions at `0⁺` -/

/-- `f(s) = ∑_{n<N} cₙ sⁿ + O(s^N)` as `s → 0⁺`, for every `N`. -/
def HasSeriesAtZero (f : ℝ → ℂ) (c : ℕ → ℂ) : Prop :=
  ∀ N : ℕ, (fun s : ℝ => f s - ∑ n ∈ Finset.range N, c n * (s : ℂ) ^ n) =O[𝓝[>] 0]
    fun s => s ^ N

/-- `sᴺ` (as a complex number) is `O(sᴺ)` as `s → 0⁺`. -/
theorem isBigO_ofReal_pow (N : ℕ) :
    (fun s : ℝ => (s : ℂ) ^ N) =O[𝓝[>] (0 : ℝ)] fun s => s ^ N :=
  IsBigO.of_bound 1 (Eventually.of_forall fun s => by simp)

/-- A complex polynomial evaluated at real `s` is bounded as `s → 0⁺`. -/
theorem isBigO_polynomial_eval_one (q : Polynomial ℂ) :
    (fun s : ℝ => q.eval (s : ℂ)) =O[𝓝[>] (0 : ℝ)] fun _ => (1 : ℝ) := by
  have hc : Continuous fun s : ℝ => q.eval (s : ℂ) :=
    q.continuous.comp continuous_ofReal
  exact (hc.continuousAt (x := 0)).tendsto.isBigO_one ℝ |>.mono nhdsWithin_le_nhds

/-- A complex polynomial whose coefficients below degree `N` vanish is `O(sᴺ)` as `s → 0⁺`. -/
theorem isBigO_polynomial_eval_of_coeff (q : Polynomial ℂ) (N : ℕ)
    (h : ∀ m < N, q.coeff m = 0) :
    (fun s : ℝ => q.eval (s : ℂ)) =O[𝓝[>] (0 : ℝ)] fun s => s ^ N := by
  obtain ⟨r, hr⟩ := Polynomial.X_pow_dvd_iff.2 h
  have h1 := (isBigO_ofReal_pow N).mul (isBigO_polynomial_eval_one r)
  refine (h1.congr_left fun s => ?_).congr_right fun s => mul_one _
  rw [hr, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]

/-- A finite power sum `∑_{n<N} cₙ zⁿ` is the evaluation of the truncated power series. -/
theorem sum_range_eq_eval_trunc (c : ℕ → ℂ) (N : ℕ) (z : ℂ) :
    ∑ n ∈ Finset.range N, c n * z ^ n = (PowerSeries.trunc N (PowerSeries.mk c)).eval z := by
  rw [Polynomial.eval, PowerSeries.eval₂_trunc_eq_sum_range]
  simp

/-- A function with an expansion at `0⁺` is bounded near `0⁺`. -/
theorem HasSeriesAtZero.isBigO_one {f : ℝ → ℂ} {c : ℕ → ℂ} (hf : HasSeriesAtZero f c) :
    f =O[𝓝[>] (0 : ℝ)] fun _ => (1 : ℝ) := by
  have h := hf 0
  simp only [Finset.range_zero, Finset.sum_empty, sub_zero, pow_zero] at h
  exact h

/-- Expansions at `0⁺` multiply: the coefficients of `f g` are those of the product power series. -/
theorem HasSeriesAtZero.mul {f g : ℝ → ℂ} {c d : ℕ → ℂ} (hf : HasSeriesAtZero f c)
    (hg : HasSeriesAtZero g d) :
    HasSeriesAtZero (fun s => f s * g s)
      (fun n => PowerSeries.coeff n (PowerSeries.mk c * PowerSeries.mk d)) := by
  intro N
  set F := PowerSeries.trunc N (PowerSeries.mk c) with hF
  set G := PowerSeries.trunc N (PowerSeries.mk d) with hG
  have hsum : ∀ s : ℝ, ∑ n ∈ Finset.range N,
      PowerSeries.coeff n (PowerSeries.mk c * PowerSeries.mk d) * (s : ℂ) ^ n =
      (PowerSeries.trunc N ((F * G : Polynomial ℂ) : PowerSeries ℂ)).eval (s : ℂ) := by
    intro s
    rw [Polynomial.coe_mul, hF, hG, PowerSeries.trunc_trunc_mul_trunc, Polynomial.eval,
      PowerSeries.eval₂_trunc_eq_sum_range]
    simp
  have hfF : ∀ s : ℝ, ∑ n ∈ Finset.range N, c n * (s : ℂ) ^ n = F.eval (s : ℂ) := fun s =>
    sum_range_eq_eval_trunc c N s
  have hgG : ∀ s : ℝ, ∑ n ∈ Finset.range N, d n * (s : ℂ) ^ n = G.eval (s : ℂ) := fun s =>
    sum_range_eq_eval_trunc d N s
  have h1 : (fun s : ℝ => (f s - F.eval (s : ℂ)) * g s) =O[𝓝[>] 0] fun s => s ^ N :=
    (((hf N).congr_left fun s => by rw [hfF]).mul hg.isBigO_one).congr_right fun s => mul_one _
  have h2 : (fun s : ℝ => F.eval (s : ℂ) * (g s - G.eval (s : ℂ))) =O[𝓝[>] 0]
      fun s => s ^ N :=
    ((isBigO_polynomial_eval_one F).mul ((hg N).congr_left fun s => by rw [hgG])).congr_right
      fun s => one_mul _
  have h3 : (fun s : ℝ => (F * G - PowerSeries.trunc N ((F * G : Polynomial ℂ) :
      PowerSeries ℂ)).eval (s : ℂ)) =O[𝓝[>] 0] fun s => s ^ N := by
    refine isBigO_polynomial_eval_of_coeff _ N fun m hm => ?_
    simp [Polynomial.coeff_sub, PowerSeries.coeff_trunc, hm, -Polynomial.coe_mul]
  refine ((h1.add h2).add h3).congr_left fun s => ?_
  rw [hsum, Polynomial.eval_sub, Polynomial.eval_mul, ← hfF, ← hgG]
  ring

/-- `A |s| ≤ 1` for all `s` near `0⁺`. -/
theorem eventually_mul_abs_le_one (A : ℝ) : ∀ᶠ s in 𝓝[>] (0 : ℝ), A * |s| ≤ 1 := by
  have h : Tendsto (fun s : ℝ => A * |s|) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_const.mul continuous_abs).tendsto (0 : ℝ) (f := fun s : ℝ => A * |s|)
  exact nhdsWithin_le_nhds (h.eventually (Iic_mem_nhds zero_lt_one))

/-- `e^(-as) = ∑ (-a)ⁿ sⁿ/n!` as an expansion at `0⁺`. -/
theorem hasSeriesAtZero_exp (a : ℂ) :
    HasSeriesAtZero (fun s => cexp (-a * s)) (fun n => (-a) ^ n / (n ! : ℂ)) := by
  intro N
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [Finset.range_zero, Finset.sum_empty, sub_zero, pow_zero]
    have hc : Continuous fun s : ℝ => cexp (-a * s) := by fun_prop
    exact (hc.continuousAt (x := 0)).tendsto.isBigO_one ℝ |>.mono nhdsWithin_le_nhds
  refine IsBigO.of_bound (‖a‖ ^ N * ((N.succ : ℝ) * (N ! * N : ℝ)⁻¹)) ?_
  filter_upwards [eventually_mul_abs_le_one ‖a‖] with s hs
  have hx : ‖-a * (s : ℂ)‖ ≤ 1 := by simpa [norm_mul] using hs
  have hb := Complex.exp_bound hx hN
  have hsum : ∑ m ∈ Finset.range N, (-a * (s : ℂ)) ^ m / (m ! : ℂ) =
      ∑ n ∈ Finset.range N, (-a) ^ n / (n ! : ℂ) * (s : ℂ) ^ n :=
    Finset.sum_congr rfl fun n _ => by rw [mul_pow]; ring
  rw [hsum] at hb
  refine hb.trans (le_of_eq ?_)
  simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, mul_pow, norm_pow]
  ring

/-- `binetPoly N s = ∑_{n<2N} B_{n+2}/(n+2)! sⁿ` (odd Bernoulli numbers beyond `B₁` vanish). -/
theorem binetPoly_eq_sum_range_two_mul (N : ℕ) (s : ℝ) :
    binetPoly N s = ∑ n ∈ Finset.range (2 * N),
      (bernoulli (n + 2) : ℝ) / ((n + 2)! : ℝ) * s ^ n := by
  induction N with
  | zero => simp [binetPoly]
  | succ N ih =>
    rw [binetPoly_eq_range] at ih ⊢
    rw [Finset.sum_range_succ, ih, show 2 * (N + 1) = 2 * N + 1 + 1 by ring,
      Finset.sum_range_succ, Finset.sum_range_succ,
      bernoulli_eq_zero_of_odd (n := 2 * N + 1 + 2) ⟨N + 1, by ring⟩ (by omega)]
    simp only [Rat.cast_zero, zero_div, zero_mul, add_zero]

/-- `β(s)/s` has the expansion `∑ B_{n+2}/(n+2)! sⁿ` at `0⁺`. -/
theorem hasSeriesAtZero_binetBeta_div :
    HasSeriesAtZero (fun s => ((binetBeta s / s : ℝ) : ℂ))
      (fun n => ((bernoulli (n + 2) : ℚ) : ℂ) / ((n + 2)! : ℂ)) := by
  intro N
  set c : ℕ → ℂ := fun n => ((bernoulli (n + 2) : ℚ) : ℂ) / ((n + 2)! : ℂ) with hc
  have hP : ∀ s : ℝ, ((binetPoly N s : ℝ) : ℂ) = ∑ n ∈ Finset.range (2 * N), c n * (s : ℂ) ^ n :=
    fun s => by rw [binetPoly_eq_sum_range_two_mul]; push_cast; rfl
  -- the Bernoulli remainder
  have h1 : (fun s : ℝ => ((binetBeta s / s - binetPoly N s : ℝ) : ℂ)) =O[𝓝[>] 0]
      fun s => s ^ N := by
    refine IsBigO.of_bound (2 * binetRemConst N) ?_
    filter_upwards [self_mem_nhdsWithin, eventually_mul_abs_le_one 1] with s hs hs1
    have hs' : (0 : ℝ) < s := hs
    have hs1' : s ≤ 1 := by simpa [abs_of_pos hs'] using hs1
    rw [Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (pow_pos hs' N)]
    refine (abs_binetBeta_div_sub_binetPoly_le N hs').trans ?_
    have hS : 0 ≤ binetRemConst N := tsum_nonneg fun m => by positivity
    exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hs'.le hs1' (by omega))
      (by positivity)
  -- the tail of the polynomial
  have h2 : (fun s : ℝ => ∑ n ∈ Finset.range (2 * N), c n * (s : ℂ) ^ n -
      ∑ n ∈ Finset.range N, c n * (s : ℂ) ^ n) =O[𝓝[>] 0] fun s => s ^ N := by
    simp_rw [sum_range_eq_eval_trunc, ← Polynomial.eval_sub]
    refine isBigO_polynomial_eval_of_coeff _ N fun m hm => ?_
    simp [Polynomial.coeff_sub, PowerSeries.coeff_trunc, hm, show m < 2 * N by omega]
  refine (h1.add h2).congr_left fun s => ?_
  rw [← hP]
  push_cast
  ring

/-! ### The Laplace form of `μ` for complex arguments -/

/-- The Laplace integrand `e^{-ws} β(s)/s`. -/
theorem integrableOn_cexp_mul_binetBeta_div {w : ℂ} (hw : 0 < w.re) :
    IntegrableOn (fun s : ℝ => cexp (-w * s) * ((binetBeta s / s : ℝ) : ℂ)) (Ioi 0) := by
  refine (integrableOn_exp_mul_binetBeta_div hw).norm.mono' ?_ ?_
  · refine ((by fun_prop : Continuous fun s : ℝ => cexp (-w * s)).continuousOn.mul
      (continuous_ofReal.comp_continuousOn (continuousOn_binetBeta.div continuousOn_id
        fun t ht => ne_of_gt ht))).aestronglyMeasurable measurableSet_Ioi
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun s hs => ?_)
    have hs' : (0 : ℝ) < s := hs
    rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (mul_nonneg (Real.exp_pos _).le (binetBeta_nonneg hs'))
        hs'.le), abs_of_nonneg (div_nonneg (binetBeta_nonneg hs') hs'.le)]
    simp only [neg_mul, neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    rw [mul_div_assoc]

/-- `|β(s)/s| ≤ 1/12` for `s > 0`. -/
theorem norm_binetBeta_div_le {s : ℝ} (hs : 0 < s) : ‖((binetBeta s / s : ℝ) : ℂ)‖ ≤ 1 / 12 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (binetBeta_nonneg hs)
    hs.le), div_le_iff₀ hs]
  linarith [binetBeta_le hs]

/-- The Laplace transform `w ↦ ∫₀^∞ e^(-ws) β(s)/s ds` is differentiable in `w` for `Re w > 0`, with
derivative under the integral sign. -/
theorem hasDerivAt_laplace_binetMu {w₀ : ℂ} (hw₀ : 0 < w₀.re) :
    HasDerivAt (fun w : ℂ => ∫ s in Ioi (0 : ℝ), cexp (-w * s) * ((binetBeta s / s : ℝ) : ℂ))
      (∫ s in Ioi (0 : ℝ), -(s : ℂ) * cexp (-w₀ * s) * ((binetBeta s / s : ℝ) : ℂ)) w₀ := by
  set σ := w₀.re / 2 with hσ
  have hσ0 : 0 < σ := by positivity
  have hball : ∀ w ∈ Metric.ball w₀ σ, σ < w.re := fun w hw => by
    have h1 : |w.re - w₀.re| < σ := by
      have := abs_re_le_norm (w - w₀)
      rw [sub_re] at this
      exact lt_of_le_of_lt this (by simpa [dist_eq_norm] using hw)
    have := neg_abs_le (w.re - w₀.re)
    linarith
  have hk : Measurable fun s : ℝ => ((binetBeta s / s : ℝ) : ℂ) := by
    refine continuous_ofReal.measurable.comp ?_
    unfold binetBeta
    fun_prop
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds w₀ hσ0)
    (μ := volume.restrict (Ioi 0))
    (F := fun w s => cexp (-w * s) * ((binetBeta s / s : ℝ) : ℂ))
    (F' := fun w s => -(s : ℂ) * cexp (-w * s) * ((binetBeta s / s : ℝ) : ℂ))
    (bound := fun s => (1 / 12) * (Real.exp (-σ * s) * s ^ 1)) ?_
    (integrableOn_cexp_mul_binetBeta_div hw₀) ?_ ?_
    ((integrableOn_exp_mul_pow hσ0 1).const_mul _) ?_).2
  · exact Eventually.of_forall fun w =>
      ((by fun_prop : Continuous fun s : ℝ => cexp (-w * s)).measurable.mul
        hk).aestronglyMeasurable
  · exact (((by fun_prop : Continuous fun s : ℝ => -(s : ℂ) * cexp (-w₀ * s)).measurable.mul
      hk)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs w hw
    have hs' : (0 : ℝ) < s := hs
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs',
      Complex.norm_exp]
    have he : Real.exp (-w * s : ℂ).re ≤ Real.exp (-σ * s) := by
      apply Real.exp_le_exp.2
      simp only [neg_mul, neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
      nlinarith [hball w hw]
    have hb := norm_binetBeta_div_le hs'
    calc s * Real.exp (-w * s : ℂ).re * ‖((binetBeta s / s : ℝ) : ℂ)‖
        ≤ s * Real.exp (-σ * s) * (1 / 12) := by gcongr
      _ = (1 / 12) * (Real.exp (-σ * s) * s ^ 1) := by ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs w hw
    have h := (((hasDerivAt_id w).neg.mul_const (s : ℂ)).cexp).mul_const
      ((binetBeta s / s : ℝ) : ℂ)
    convert h using 1
    · ext v; simp
    · simp only [Pi.neg_apply, id]; ring

/-- The Laplace form `μ(w) = ∫₀^∞ e^{-ws} β(s)/s ds` for `Re w > 0` (Temme (3.27)). -/
theorem binetMu_eq_laplace {w : ℂ} (hw : 0 < w.re) :
    binetMu w = ∫ s in Ioi (0 : ℝ), cexp (-w * s) * ((binetBeta s / s : ℝ) : ℂ) := by
  set U : Set ℂ := {w | 0 < w.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUs : U ⊆ slitPlane := fun w hw => mem_slitPlane_iff.2 (Or.inl hw)
  have h1 : AnalyticOnNhd ℂ binetMu U :=
    (differentiableOn_binetMu.mono hUs).analyticOnNhd hUo
  have h2 : AnalyticOnNhd ℂ (fun w : ℂ =>
      ∫ s in Ioi (0 : ℝ), cexp (-w * s) * ((binetBeta s / s : ℝ) : ℂ)) U :=
    DifferentiableOn.analyticOnNhd (fun w hw =>
      (hasDerivAt_laplace_binetMu hw).differentiableAt.differentiableWithinAt) hUo
  refine h1.eqOn_of_preconnected_of_frequently_eq h2
    (convex_halfSpace_re_gt 0).isPreconnected (z₀ := 1) (by simp [hU]) ?_ hw
  have hev : ∀ᶠ x : ℝ in 𝓝[≠] 1, binetMu x =
      ∫ s in Ioi (0 : ℝ), cexp (-(x : ℂ) * s) * ((binetBeta s / s : ℝ) : ℂ) := by
    filter_upwards [nhdsWithin_le_nhds (lt_mem_nhds one_pos)] with x hx
    rw [binetMu_ofReal, binetMuReal_eq_binetIntegral hx, binetIntegral, ← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    push_cast
    ring_nf
  have ht : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] 1) (𝓝[≠] 1) :=
    Complex.continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin fun x hx => by
      simpa using hx
  exact ht.frequently hev.frequently

/-- Watson's lemma for `μ(t + a)`, `t → +∞`. -/
theorem hasAsymptoticExpansion_binetMu_add (a : ℂ) :
    HasAsymptoticExpansion atTop (fun (n : ℕ) (t : ℝ) => t ^ (-((n : ℝ) + 1)))
      (fun n => Real.Gamma ((n : ℝ) + 1) • PowerSeries.coeff n
        (PowerSeries.mk (fun n => (-a) ^ n / (n ! : ℂ)) *
          PowerSeries.mk (fun n => ((bernoulli (n + 2) : ℚ) : ℂ) / ((n + 2)! : ℂ))))
      (fun t => binetMu (t + a)) := by
  set F : ℝ → ℂ := fun s => cexp (-a * s) * ((binetBeta s / s : ℝ) : ℂ) with hF
  have hser := (hasSeriesAtZero_exp a).mul hasSeriesAtZero_binetBeta_div
  have hint : IntegrableOn (fun s => Real.exp (-(‖a‖ + 1) * s) • F s) (Ioi 0) := by
    have hre : 0 < (((‖a‖ + 1 : ℝ) : ℂ) + a).re := by
      simp only [add_re, ofReal_re]
      linarith [neg_abs_le a.re, abs_re_le_norm a]
    refine (integrableOn_cexp_mul_binetBeta_div hre).congr_fun (fun s _ => ?_)
      measurableSet_Ioi
    simp only [hF, real_smul, ofReal_exp]
    rw [← mul_assoc, ← Complex.exp_add]
    push_cast
    ring_nf
  have hW := hasAsymptoticExpansion_integral_exp_smul (μ := 1) one_pos hint (fun N => by
    refine ((hser N).congr_left fun s => ?_).congr_right fun s => ?_
    · simp only [hF, add_sub_cancel_right, Real.rpow_natCast, real_smul]
      congr 1
      refine Finset.sum_congr rfl fun n _ => ?_
      push_cast
      ring
    · simp [Real.rpow_natCast])
  refine hW.congr' ?_
  filter_upwards [eventually_gt_atTop ‖a‖] with t ht
  have hre : 0 < ((t : ℂ) + a).re := by
    simp only [add_re, ofReal_re]
    linarith [neg_abs_le a.re, abs_re_le_norm a]
  rw [binetMu_eq_laplace hre]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  simp only [hF, real_smul, ofReal_exp]
  rw [← mul_assoc, ← Complex.exp_add]
  push_cast
  ring_nf

/-! ### The elementary part of the shifted Stirling expansion -/

/-- `(t + a - 1/2)(log(t + a) - log t) - a`. -/
def stirlingLogPart (a : ℂ) (t : ℝ) : ℂ :=
  ((t : ℂ) + a - 1 / 2) * (log ((t : ℂ) + a) - log t) - a

/-- Coefficients of `stirlingLogPart`. -/
def stirlingLogCoeff (a : ℂ) (n : ℕ) : ℂ :=
  (-1) ^ n * (a ^ (n + 2) / ((n + 1) * (n + 2)) - a ^ (n + 1) / (2 * (n + 1)))

/-- The `m`-th coefficient of the truncation to degree `< M` of `mk f` is `f m` if `m < M` and `0`
otherwise. -/
theorem coeff_trunc_mk (f : ℕ → ℂ) (M m : ℕ) :
    (PowerSeries.trunc M (PowerSeries.mk f)).coeff m = if m < M then f m else 0 := by
  simp [PowerSeries.coeff_trunc]

/-- `t (t⁻¹)^(N+2) = t^(-(N+1))` eventually as `t → ∞`. -/
theorem isBigO_rpow_neg_of_recip_pow (N : ℕ) :
    (fun t : ℝ => t * (t⁻¹) ^ (N + 2)) =ᶠ[atTop] fun t => t ^ (-((N : ℝ) + 1)) := by
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [Real.rpow_neg ht.le, show (N : ℝ) + 1 = ((N + 1 : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_natCast, inv_pow, pow_succ _ (N + 1)]
  field_simp

/-- The elementary part `(t + a - 1/2)(log(t + a) - log t) - a` has an asymptotic expansion in
powers `t^(-(n+1))` with coefficients `stirlingLogCoeff a`. -/
theorem hasAsymptoticExpansion_stirlingLogPart (a : ℂ) :
    HasAsymptoticExpansion atTop (fun (n : ℕ) (t : ℝ) => t ^ (-((n : ℝ) + 1)))
      (stirlingLogCoeff a) (stirlingLogPart a) := by
  intro N
  set lc : ℕ → ℂ := fun j => (-1) ^ (j + 1) * a ^ j / j with hlc
  set Q : Polynomial ℂ := (1 + Polynomial.C (a - 1 / 2) * Polynomial.X) *
      PowerSeries.trunc (N + 2) (PowerSeries.mk lc) - Polynomial.C a * Polynomial.X -
      Polynomial.X ^ 2 * PowerSeries.trunc N (PowerSeries.mk (stirlingLogCoeff a)) with hQ
  have hQc : ∀ m < N + 2, Q.coeff m = 0 := by
    intro m hm
    have hmul : ∀ P : Polynomial ℂ, ((1 + Polynomial.C (a - 1 / 2) * Polynomial.X) * P) =
        P + Polynomial.C (a - 1 / 2) * (Polynomial.X * P) := fun P => by ring
    rw [hQ, Polynomial.coeff_sub, Polynomial.coeff_sub, hmul, Polynomial.coeff_add,
      Polynomial.coeff_C_mul, Polynomial.coeff_C_mul_X, Polynomial.coeff_X_pow_mul']
    rcases m with _ | _ | k
    · simp [hlc, coeff_trunc_mk]
    · simp [hlc, coeff_trunc_mk]
    · rw [Polynomial.coeff_X_mul, coeff_trunc_mk, coeff_trunc_mk, coeff_trunc_mk]
      simp only [show k + 1 + 1 < N + 2 from hm, show k + 1 < N + 2 by omega,
        show k + 1 + 1 ≠ 1 by omega, show 2 ≤ k + 1 + 1 by omega,
        show k + 1 + 1 - 2 = k by omega, show k < N by omega, ite_true, ite_false]
      simp only [hlc, stirlingLogCoeff]
      push_cast
      have h1 : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
      have h2 : (k : ℂ) + 1 + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (k + 1)
      have h2' : (k : ℂ) + 2 ≠ 0 := by
        rw [show (k : ℂ) + 2 = k + 1 + 1 by ring]; exact h2
      field_simp
      ring
  -- the polynomial part
  have hQO : (fun t : ℝ => (t : ℂ) * Q.eval ((t⁻¹ : ℝ) : ℂ)) =O[atTop]
      fun t => t ^ (-((N : ℝ) + 1)) := by
    have h1 := (isBigO_polynomial_eval_of_coeff Q (N + 2) hQc).comp_tendsto
      tendsto_inv_atTop_nhdsGT_zero
    have h2 : (fun t : ℝ => (t : ℂ)) =O[atTop] fun t => t :=
      IsBigO.of_bound 1 (Eventually.of_forall fun t => by simp)
    exact ((h2.mul h1).trans_eventuallyEq (isBigO_rpow_neg_of_recip_pow N))
  -- the logarithm remainder
  have hz : Tendsto (fun t : ℝ => a / (t : ℂ)) atTop (𝓝 0) := by
    have : Tendsto (fun t : ℝ => ((t⁻¹ : ℝ) : ℂ)) atTop (𝓝 0) := by
      have h := (continuous_ofReal.tendsto 0).comp (tendsto_inv_atTop_zero (𝕜 := ℝ))
      simpa only [Function.comp_def, ofReal_zero] using h
    simpa [div_eq_mul_inv] using this.const_mul a
  have hlogO : (fun t : ℝ => ((t : ℂ) + a - 1 / 2) *
      (log (1 + a / t) - logTaylor (N + 2) (a / t))) =O[atTop]
      fun t => t ^ (-((N : ℝ) + 1)) := by
    have h1 := (log_sub_logTaylor_isBigO (N + 1)).comp_tendsto hz
    have h1' : (fun t : ℝ => log (1 + a / t) - logTaylor (N + 2) (a / t)) =O[atTop]
        fun t : ℝ => (t⁻¹) ^ (N + 2) := by
      refine h1.trans (IsBigO.of_bound (‖a‖ ^ (N + 2)) ?_)
      filter_upwards [eventually_gt_atTop 0] with t ht
      simp only [Function.comp, norm_pow, norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos ht, inv_pow, abs_inv, abs_pow]
      exact le_of_eq (by rw [div_pow]; ring)
    have h2 : (fun t : ℝ => (t : ℂ) + a - 1 / 2) =O[atTop] fun t => t := by
      refine IsBigO.of_bound (2 + ‖a‖) ?_
      filter_upwards [eventually_ge_atTop 1] with t ht
      have : ‖(t : ℂ) + a - 1 / 2‖ ≤ t + ‖a‖ + 1 / 2 := by
        refine (norm_sub_le _ _).trans ?_
        have := norm_add_le (t : ℂ) a
        simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < t)]
          at this
        norm_num
        linarith
      rw [Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < t)]
      nlinarith [norm_nonneg a]
    exact (h2.mul h1').trans_eventuallyEq (isBigO_rpow_neg_of_recip_pow N)
  refine (hlogO.add hQO).congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [eventually_gt_atTop (2 * ‖a‖)] with t ht
  have ht0 : 0 < t := lt_of_le_of_lt (by positivity) ht
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
  have hlt : ‖a / (t : ℂ)‖ < 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0, div_lt_one ht0]
    linarith [norm_nonneg a]
  have h1 : (1 : ℂ) + a / t ≠ 0 := fun h => by
    have : a / (t : ℂ) = -1 := by linear_combination h
    rw [this] at hlt; simp at hlt
  have hlog : log ((t : ℂ) + a) - log t = log (1 + a / t) := by
    rw [show (t : ℂ) + a = (t : ℂ) * (1 + a / t) by field_simp, log_ofReal_mul ht0 h1,
      ← ofReal_log ht0.le]
    ring
  simp only [stirlingLogPart, hlog, hQ, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_pow, ← sum_range_eq_eval_trunc, logTaylor, hlc, real_smul]
  have e1 : ∑ j ∈ Finset.range (N + 2), (-1) ^ (j + 1) * (a / (t : ℂ)) ^ j / (j : ℂ) =
      ∑ n ∈ Finset.range (N + 2), (-1) ^ (n + 1) * a ^ n / (n : ℂ) * ((t⁻¹ : ℝ) : ℂ) ^ n :=
    Finset.sum_congr rfl fun n _ => by rw [div_pow]; push_cast; ring
  have e2 : ∑ x ∈ Finset.range N, ((t ^ (-((x : ℝ) + 1)) : ℝ) : ℂ) * stirlingLogCoeff a x =
      (t : ℂ) * (((t⁻¹ : ℝ) : ℂ) ^ 2 *
        ∑ n ∈ Finset.range N, stirlingLogCoeff a n * ((t⁻¹ : ℝ) : ℂ) ^ n) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Real.rpow_neg ht0.le, show (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast]
    push_cast
    simp only [inv_pow]
    field_simp
    ring
  rw [e1, e2]
  generalize ∑ n ∈ Finset.range (N + 2), (-1) ^ (n + 1) * a ^ n / (n : ℂ) *
    ((t⁻¹ : ℝ) : ℂ) ^ n = S1
  generalize ∑ n ∈ Finset.range N, stirlingLogCoeff a n * ((t⁻¹ : ℝ) : ℂ) ^ n = S2
  push_cast
  field_simp
  ring

/-! ### The shifted Stirling expansion (DLMF 5.11.8) -/

/-- The coefficients `(-1)ⁿ B_{n+2}(a)/((n+1)(n+2))` of DLMF 5.11.8. -/
def stirlingShiftCoeff (a : ℂ) (n : ℕ) : ℂ :=
  (-1) ^ n * Polynomial.aeval a (Polynomial.bernoulli (n + 2)) / ((n + 1) * (n + 2))

/-- `Bₙ(a) = ∑_{i≤n} Bᵢ C(n, i) a^(n-i)`. -/
theorem aeval_bernoulli_eq_sum (a : ℂ) (n : ℕ) :
    Polynomial.aeval a (Polynomial.bernoulli n) =
      ∑ i ∈ Finset.range (n + 1), ((bernoulli i : ℚ) : ℂ) * (n.choose i : ℂ) * a ^ (n - i) := by
  simp [Polynomial.bernoulli, map_sum, Polynomial.aeval_monomial]

/-- `(-1)^k B_{k+2} = B_{k+2}` (odd Bernoulli numbers beyond `B₁` vanish). -/
theorem neg_one_pow_mul_bernoulli_add_two (k : ℕ) :
    (-1 : ℂ) ^ k * ((bernoulli (k + 2) : ℚ) : ℂ) = ((bernoulli (k + 2) : ℚ) : ℂ) := by
  rcases Nat.even_or_odd k with hk | hk
  · rw [hk.neg_one_pow, one_mul]
  · rw [bernoulli_eq_zero_of_odd (hk.add_even even_two) (by omega)]
    simp

/-- The coefficients of the elementary and the Laplace parts add up to the coefficients `(-1)ⁿ
B_{n+2}(a)/((n+1)(n+2))` of DLMF 5.11.8. -/
theorem stirlingLogCoeff_add_coeff (a : ℂ) (n : ℕ) :
    stirlingLogCoeff a n + Real.Gamma ((n : ℝ) + 1) • PowerSeries.coeff n
        (PowerSeries.mk (fun n => (-a) ^ n / (n ! : ℂ)) *
          PowerSeries.mk (fun n => ((bernoulli (n + 2) : ℚ) : ℂ) / ((n + 2)! : ℂ))) =
      stirlingShiftCoeff a n := by
  rw [PowerSeries.coeff_mul, ← Finset.Nat.sum_antidiagonal_swap]
  simp only [Prod.fst_swap, Prod.snd_swap, PowerSeries.coeff_mk]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j =>
    (-a) ^ j / (j ! : ℂ) * (((bernoulli (i + 2) : ℚ) : ℂ) / ((i + 2)! : ℂ))),
    Real.Gamma_nat_eq_factorial, stirlingShiftCoeff, aeval_bernoulli_eq_sum, real_smul,
    Finset.mul_sum]
  conv_rhs => rw [Finset.sum_range_succ', Finset.sum_range_succ']
  have hn1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hn2 : (n : ℂ) + 2 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n + 1)
  have hterm : ∀ k ∈ Finset.range n.succ, (((n ! : ℝ)) : ℂ) * ((-a) ^ (n - k) /
      ((n - k) ! : ℂ) * (((bernoulli (k + 2) : ℚ) : ℂ) / ((k + 2)! : ℂ))) =
      (-1) ^ n / ((n + 1) * (n + 2)) * (((bernoulli (k + 1 + 1) : ℚ) : ℂ) *
        ((n + 2).choose (k + 1 + 1) : ℂ) * a ^ (n + 2 - (k + 1 + 1))) := by
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    have hch := Nat.choose_mul_factorial_mul_factorial (show k + 2 ≤ n + 2 by omega)
    rw [show n + 2 - (k + 2) = n - k by omega] at hch
    have hchC : ((n + 2).choose (k + 2) : ℂ) * ((k + 2)! : ℂ) * ((n - k)! : ℂ) =
        ((n + 2)! : ℂ) := by exact_mod_cast hch
    have hfac : ((n + 2)! : ℂ) = ((n : ℂ) + 2) * ((n : ℂ) + 1) * (n ! : ℂ) := by
      push_cast [Nat.factorial_succ]; ring
    have hk1 : ((k + 2)! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    have hk2 : ((n - k)! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    have hchoose : ((n + 2).choose (k + 2) : ℂ) =
        ((n : ℂ) + 2) * ((n : ℂ) + 1) * (n ! : ℂ) / (((k + 2)! : ℂ) * ((n - k)! : ℂ)) := by
      rw [eq_div_iff (mul_ne_zero hk1 hk2), ← hfac, ← hchC]
      ring
    have hpow : (-1 : ℂ) ^ (n - k) * ((bernoulli (k + 2) : ℚ) : ℂ) =
        (-1) ^ n * ((bernoulli (k + 2) : ℚ) : ℂ) := by
      calc (-1 : ℂ) ^ (n - k) * ((bernoulli (k + 2) : ℚ) : ℂ)
          = (-1) ^ (n - k) * ((-1) ^ k * ((bernoulli (k + 2) : ℚ) : ℂ)) := by
            rw [neg_one_pow_mul_bernoulli_add_two]
        _ = (-1) ^ n * ((bernoulli (k + 2) : ℚ) : ℂ) := by
            rw [← mul_assoc, ← pow_add, show n - k + k = n by omega]
    rw [show n + 2 - (k + 1 + 1) = n - k by omega, show k + 1 + 1 = k + 2 by ring, hchoose,
      neg_pow, Complex.ofReal_natCast]
    rw [show (n ! : ℂ) * ((-1) ^ (n - k) * a ^ (n - k) / ((n - k)! : ℂ) *
        (((bernoulli (k + 2) : ℚ) : ℂ) / ((k + 2)! : ℂ))) =
        (n ! : ℂ) * a ^ (n - k) / (((n - k)! : ℂ) * ((k + 2)! : ℂ)) *
          ((-1) ^ (n - k) * ((bernoulli (k + 2) : ℚ) : ℂ)) by ring, hpow]
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  generalize ∑ k ∈ Finset.range n.succ, ((bernoulli (k + 1 + 1) : ℚ) : ℂ) *
    ((n + 2).choose (k + 1 + 1) : ℂ) * a ^ (n + 2 - (k + 1 + 1)) = S
  simp only [stirlingLogCoeff, bernoulli_zero, bernoulli_one, Nat.choose_zero_right,
    Nat.choose_one_right, zero_add, Nat.sub_zero]
  rw [show n + 2 - 1 = n + 1 by omega]
  push_cast
  field_simp
  ring

/-- `B(t + a) - ((t + a - 1/2) log t - t + (1/2) log 2π)`, with `B` the Binet exponent. -/
def stirlingShiftRem (a : ℂ) (t : ℝ) : ℂ :=
  binetExponent (t + a) - (((t : ℂ) + a - 1 / 2) * log t - t + (1 / 2) * log (2 * π))

/-- The shifted Stirling remainder is the elementary part plus `μ(t + a)`. -/
theorem stirlingShiftRem_eq (a : ℂ) :
    stirlingShiftRem a = stirlingLogPart a + fun t : ℝ => binetMu ((t : ℂ) + a) := by
  funext t
  simp only [stirlingShiftRem, stirlingLogPart, binetExponent, Pi.add_apply]
  ring

/-- DLMF 5.11.8: `log Γ(t + a) ~ (t + a - 1/2) log t - t + (1/2) log 2π
  + ∑ (-1)ⁿ B_{n+2}(a)/((n+1)(n+2)) t^{-(n+1)}`, with `log Γ` the Binet exponent. -/
theorem hasAsymptoticExpansion_stirlingShiftRem (a : ℂ) :
    HasAsymptoticExpansion atTop (fun (n : ℕ) (t : ℝ) => t ^ (-((n : ℝ) + 1)))
      (stirlingShiftCoeff a) (stirlingShiftRem a) := by
  rw [stirlingShiftRem_eq]
  refine ((hasAsymptoticExpansion_stirlingLogPart a).add
    (hasAsymptoticExpansion_binetMu_add a)).congr_coeff ?_
  funext n
  exact stirlingLogCoeff_add_coeff a n

/-! ### Exponentiating an asymptotic expansion -/

/-- If `(n+1) Gₙ₊₁ = ∑_{k ≤ n} (k+1) dₖ G_{n-k}` and `G₀ = 1`, then
`exp(∑_{k<N} dₖ x^{k+1}) = ∑_{k ≤ N} Gₖ xᵏ + O(x^{N+1})` as `x → 0⁺`. -/
theorem cexp_poly_sub_isBigO (d G : ℕ → ℂ) (hG0 : G 0 = 1)
    (hG : ∀ n : ℕ, ((n : ℂ) + 1) * G (n + 1) =
      ∑ k ∈ Finset.range (n + 1), ((k : ℂ) + 1) * d k * G (n - k)) (N : ℕ) :
    (fun x : ℝ => cexp (∑ k ∈ Finset.range N, d k * (x : ℂ) ^ (k + 1)) -
      ∑ k ∈ Finset.range (N + 1), G k * (x : ℂ) ^ k) =O[𝓝[>] 0] fun x => x ^ (N + 1) := by
  set P : Polynomial ℂ := Polynomial.X * PowerSeries.trunc N (PowerSeries.mk d) with hP
  set E : Polynomial ℂ := PowerSeries.trunc (N + 1) (PowerSeries.mk G) with hE
  have hPe : ∀ z : ℂ, P.eval z = ∑ k ∈ Finset.range N, d k * z ^ (k + 1) := fun z => by
    rw [hP, Polynomial.eval_mul, Polynomial.eval_X, ← sum_range_eq_eval_trunc, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hEe : ∀ z : ℂ, E.eval z = ∑ k ∈ Finset.range (N + 1), G k * z ^ k := fun z =>
    (sum_range_eq_eval_trunc G (N + 1) z).symm
  set D : Polynomial ℂ := Polynomial.derivative E - Polynomial.derivative P * E with hD
  have hDc : ∀ m < N, D.coeff m = 0 := by
    intro m hm
    rw [hD, Polynomial.coeff_sub, Polynomial.coeff_derivative, Polynomial.coeff_mul, hE,
      coeff_trunc_mk]
    simp only [show m + 1 < N + 1 by omega, ↓reduceIte]
    have hsum : ∑ x ∈ Finset.antidiagonal m, (Polynomial.derivative P).coeff x.1 *
        (PowerSeries.trunc (N + 1) (PowerSeries.mk G)).coeff x.2 =
        ∑ x ∈ Finset.antidiagonal m, ((x.1 : ℂ) + 1) * d x.1 * G x.2 := by
      refine Finset.sum_congr rfl fun x hx => ?_
      have hx' := Finset.mem_antidiagonal.1 hx
      rw [Polynomial.coeff_derivative, hP, Polynomial.coeff_X_mul, coeff_trunc_mk,
        coeff_trunc_mk]
      simp only [show x.1 < N by omega, show x.2 < N + 1 by omega, ↓reduceIte]
      ring
    rw [hsum, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => ((i : ℂ) + 1) * d i * G j), ← hG m]
    ring
  obtain ⟨R, hR⟩ := Polynomial.X_pow_dvd_iff.2 hDc
  have hDe : ∀ z : ℂ, D.eval z = z ^ N * R.eval z := fun z => by
    rw [hR, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
  set h : ℝ → ℂ := fun x => cexp (-P.eval (x : ℂ)) * E.eval (x : ℂ) with hh
  have hderiv : ∀ x : ℝ, HasDerivAt h (cexp (-P.eval (x : ℂ)) * D.eval (x : ℂ)) x := by
    intro x
    have hP' : HasDerivAt (fun y : ℝ => P.eval (y : ℂ)) ((Polynomial.derivative P).eval x) x :=
      (P.hasDerivAt (x : ℂ)).comp_ofReal
    have hE' : HasDerivAt (fun y : ℝ => E.eval (y : ℂ)) ((Polynomial.derivative E).eval x) x :=
      (E.hasDerivAt (x : ℂ)).comp_ofReal
    convert (hP'.neg.cexp).mul hE' using 1
    have : D.eval (x : ℂ) = (Polynomial.derivative E).eval (x : ℂ) -
        (Polynomial.derivative P).eval (x : ℂ) * E.eval (x : ℂ) := by
      rw [hD, Polynomial.eval_sub, Polynomial.eval_mul]
    rw [this]
    simp only [Pi.neg_apply]
    ring
  -- bounds on `[0, 1]`
  obtain ⟨M, hM⟩ := IsCompact.exists_bound_of_continuousOn (isCompact_Icc (a := (0 : ℝ)) (b := 1))
    (f := fun y : ℝ => cexp (-P.eval (y : ℂ)) * R.eval (y : ℂ))
    (by fun_prop)
  obtain ⟨K, hK⟩ := IsCompact.exists_bound_of_continuousOn (isCompact_Icc (a := (0 : ℝ)) (b := 1))
    (f := fun y : ℝ => cexp (P.eval (y : ℂ))) (by fun_prop)
  have hh0 : h 0 = 1 := by
    simp only [hh, ofReal_zero, ← Polynomial.coeff_zero_eq_eval_zero, hP, hE,
      Polynomial.coeff_X_mul_zero, neg_zero, Complex.exp_zero, one_mul, coeff_trunc_mk]
    simp [hG0]
  refine IsBigO.of_bound (K * M) ?_
  filter_upwards [self_mem_nhdsWithin, eventually_mul_abs_le_one 1] with x hx hx1
  have hx0 : (0 : ℝ) < x := hx
  have hx1' : x ≤ 1 := by simpa [abs_of_pos hx0] using hx1
  have hMV := norm_image_sub_le_of_norm_deriv_le_segment' (a := 0) (b := x) (f := h)
    (C := M * x ^ N) (fun y _ => (hderiv y).hasDerivWithinAt) (fun y hy => by
      rw [hDe, norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hy.1]
      have h1 := hM y ⟨hy.1, by linarith [hy.2, hx1']⟩
      rw [norm_mul] at h1
      have h2 : y ^ N ≤ x ^ N := pow_le_pow_left₀ hy.1 hy.2.le N
      have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, zero_le_one⟩)
      calc ‖cexp (-P.eval (y : ℂ))‖ * (y ^ N * ‖R.eval (y : ℂ)‖)
          = y ^ N * (‖cexp (-P.eval (y : ℂ))‖ * ‖R.eval (y : ℂ)‖) := by ring
        _ ≤ x ^ N * M := mul_le_mul h2 h1 (by positivity) (by positivity)
        _ = M * x ^ N := by ring) x ⟨hx0.le, le_rfl⟩
  rw [hh0, sub_zero] at hMV
  have hKx := hK x ⟨hx0.le, hx1'⟩
  have heq : cexp (∑ k ∈ Finset.range N, d k * (x : ℂ) ^ (k + 1)) -
      ∑ k ∈ Finset.range (N + 1), G k * (x : ℂ) ^ k =
      cexp (P.eval (x : ℂ)) * (1 - h x) := by
    have hhx : h x = cexp (-P.eval (x : ℂ)) * E.eval (x : ℂ) := rfl
    rw [hhx, ← hPe, ← hEe, mul_sub, mul_one, ← mul_assoc, ← Complex.exp_add]
    simp
  rw [heq, norm_mul, Real.norm_eq_abs, abs_of_pos (pow_pos hx0 _), norm_sub_rev]
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, zero_le_one⟩)
  calc ‖cexp (P.eval (x : ℂ))‖ * ‖h x - 1‖ ≤ K * (M * x ^ N * x) :=
        mul_le_mul hKx hMV (norm_nonneg _) ((norm_nonneg _).trans hKx)
    _ = K * M * x ^ (N + 1) := by ring

/-- `t^(-(n+1)) = (t⁻¹)^(n+1)` for `t > 0`. -/
theorem rpow_neg_add_one_eq_recip_pow {t : ℝ} (ht : 0 < t) (n : ℕ) :
    t ^ (-((n : ℝ) + 1)) = (t⁻¹) ^ (n + 1) := by
  rw [Real.rpow_neg ht.le, show (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_natCast, inv_pow]

/-- Exponentiation of an asymptotic expansion in powers of `1/t` without constant term. -/
theorem isBigO_cexp_sub_of_hasAsymptoticExpansion {L : ℝ → ℂ} {d G : ℕ → ℂ}
    (hL : HasAsymptoticExpansion atTop (fun (n : ℕ) (t : ℝ) => t ^ (-((n : ℝ) + 1))) d L)
    (hG0 : G 0 = 1)
    (hG : ∀ n : ℕ, ((n : ℂ) + 1) * G (n + 1) =
      ∑ k ∈ Finset.range (n + 1), ((k : ℂ) + 1) * d k * G (n - k)) (N : ℕ) :
    (fun t => cexp (L t) - ∑ k ∈ Finset.range (N + 1), G k * ((t⁻¹ : ℝ) : ℂ) ^ k) =O[atTop]
      fun t => t ^ (-((N : ℝ) + 1)) := by
  set Pd : ℝ → ℂ := fun x => ∑ k ∈ Finset.range N, d k * (x : ℂ) ^ (k + 1) with hPd
  set r : ℝ → ℂ := fun t => L t - Pd t⁻¹ with hr
  have hrO : r =O[atTop] fun t => t ^ (-((N : ℝ) + 1)) := by
    refine (hL N).congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_gt_atTop 0] with t ht
    simp only [hr, hPd, real_smul]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [rpow_neg_add_one_eq_recip_pow ht]
    push_cast
    ring
  have hr0 : Tendsto r atTop (𝓝 0) := by
    refine hrO.trans_tendsto ?_
    have h := (tendsto_rpow_neg_atTop (y := (N : ℝ) + 1) (by positivity))
    simpa using h
  -- `exp r - 1 = O(r)`
  have hexp : (fun t => cexp (r t) - 1) =O[atTop] r := by
    refine IsBigO.of_bound 2 ?_
    filter_upwards [hr0.eventually (Metric.closedBall_mem_nhds 0 zero_lt_one)] with t ht
    exact Complex.norm_exp_sub_one_le (by simpa using ht)
  -- `exp(Pd(1/t))` is bounded
  have hPdb : (fun t : ℝ => cexp (Pd t⁻¹)) =O[atTop] fun _ => (1 : ℝ) := by
    have hc : Continuous fun x : ℝ => cexp (Pd x) := by simp only [hPd]; fun_prop
    exact ((hc.tendsto 0).comp tendsto_inv_atTop_zero).isBigO_one ℝ
  have h1 := (hPdb.mul (hexp.trans hrO)).congr_right fun t => one_mul _
  have hev : (fun t : ℝ => (t⁻¹) ^ (N + 1)) =ᶠ[atTop] fun t => t ^ (-((N : ℝ) + 1)) := by
    filter_upwards [eventually_gt_atTop 0] with t ht
    exact (rpow_neg_add_one_eq_recip_pow ht N).symm
  have h2 := ((cexp_poly_sub_isBigO d G hG0 hG N).comp_tendsto
    tendsto_inv_atTop_nhdsGT_zero).trans_eventuallyEq hev
  refine (h1.add h2).congr_left fun t => ?_
  simp only [Function.comp_apply, hr]
  rw [mul_sub, mul_one, ← Complex.exp_add, add_sub_cancel]
  simp only [hPd]
  ring

/-- `G₀(a, b) = 1` for the coefficients of DLMF 5.11.15. -/
theorem stirlingRatioG_zero (a b : ℂ) : stirlingRatioG a b 0 = 1 := by
  rw [stirlingRatioG]

/-- The coefficients `Gₙ(a, b)` of DLMF 5.11.15 satisfy `(n + 1) G_{n+1} = ∑_{k≤n} (k + 1)(cₖ(a) -
cₖ(b)) G_{n-k}`, with `cₖ` the coefficients of 5.11.8. -/
theorem stirlingRatioG_recurrence (a b : ℂ) (n : ℕ) :
    ((n : ℂ) + 1) * stirlingRatioG a b (n + 1) = ∑ k ∈ Finset.range (n + 1),
      ((k : ℂ) + 1) * (stirlingShiftCoeff a k - stirlingShiftCoeff b k) *
        stirlingRatioG a b (n - k) := by
  rw [stirlingRatioG]
  have hn : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  rw [mul_div_cancel₀ _ hn, Fin.sum_univ_eq_sum_range (fun k => (-1 : ℂ) ^ k *
    (Polynomial.aeval a (Polynomial.bernoulli (k + 2)) -
      Polynomial.aeval b (Polynomial.bernoulli (k + 2))) / (k + 2) *
    stirlingRatioG a b (n - k)) (n + 1)]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have h2 : (k : ℂ) + 2 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (k + 1)
  simp only [stirlingShiftCoeff]
  field_simp

end ShiftedStirling

/-- The all-order positive-ray Gamma-ratio expansion with its order-dependent remainder. -/
@[dlmf 5.11.E13]
theorem Gamma_ratio_expansion (a b : ℂ) (n : ℕ) :
    Asymptotics.IsBigO atTop
      (fun t : ℝ => Complex.Gamma (t + a) / Complex.Gamma (t + b) -
        (t : ℂ) ^ (a - b) * ∑ k ∈ Finset.range n, stirlingRatioG a b k / (t : ℂ) ^ k)
      (fun t : ℝ => (t : ℂ) ^ (a - b - n)) := by
  set G := stirlingRatioG a b with hGdef
  have hL := (hasAsymptoticExpansion_stirlingShiftRem a).sub
    (hasAsymptoticExpansion_stirlingShiftRem b)
  have hE := isBigO_cexp_sub_of_hasAsymptoticExpansion hL (stirlingRatioG_zero a b)
    (fun m => by simpa using stirlingRatioG_recurrence a b m) n
  -- drop the last term
  have hlast : (fun t : ℝ => G n * ((t⁻¹ : ℝ) : ℂ) ^ n) =O[atTop] fun t => t ^ (-(n : ℝ)) := by
    refine Asymptotics.IsBigO.of_bound ‖G n‖ ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 ht), abs_of_pos (Real.rpow_pos_of_pos ht _), Real.rpow_neg ht.le,
      Real.rpow_natCast, inv_pow]
  have hstep : (fun t : ℝ => t ^ (-((n : ℝ) + 1))) =O[atTop] fun t => t ^ (-(n : ℝ)) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop 1] with t ht
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (by linarith) _),
      abs_of_pos (Real.rpow_pos_of_pos (by linarith) _), one_mul]
    exact Real.rpow_le_rpow_of_exponent_le ht (by linarith)
  have hX : (fun t : ℝ => cexp ((stirlingShiftRem a - stirlingShiftRem b) t) -
      ∑ k ∈ Finset.range n, G k * ((t⁻¹ : ℝ) : ℂ) ^ k) =O[atTop]
      fun t => ((t ^ (-(n : ℝ)) : ℝ) : ℂ) := by
    refine (((hE.trans hstep).add hlast).congr_left fun t => ?_).trans
      (Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun t => by simp))
    rw [Finset.sum_range_succ]
    ring
  have hmain := (Asymptotics.isBigO_refl (fun t : ℝ => (t : ℂ) ^ (a - b)) atTop).mul hX
  refine (hmain.congr' ?_ ?_)
  · filter_upwards [eventually_gt_atTop (max ‖a‖ ‖b‖)] with t ht
    have hta : (t : ℂ) + a ∈ slitPlane := mem_slitPlane_iff.2 (Or.inl (by
      simp only [add_re, ofReal_re]
      linarith [neg_abs_le a.re, abs_re_le_norm a, le_max_left ‖a‖ ‖b‖]))
    have htb : (t : ℂ) + b ∈ slitPlane := mem_slitPlane_iff.2 (Or.inl (by
      simp only [add_re, ofReal_re]
      linarith [neg_abs_le b.re, abs_re_le_norm b, le_max_right ‖a‖ ‖b‖]))
    have ht0 : (t : ℂ) ≠ 0 := by
      have : 0 < t := lt_of_le_of_lt (le_max_of_le_left (norm_nonneg a)) ht
      exact_mod_cast this.ne'
    rw [Gamma_eq_exp_binetExponent hta, Gamma_eq_exp_binetExponent htb, ← Complex.exp_sub,
      cpow_def_of_ne_zero ht0, mul_sub, ← Complex.exp_add]
    simp only [Pi.sub_apply, stirlingShiftRem]
    congr 1
    · congr 1; ring
    · congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      push_cast
      rw [div_eq_mul_inv, inv_pow]
  · filter_upwards [eventually_gt_atTop 0] with t ht
    have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    rw [Complex.ofReal_cpow ht.le, ← cpow_add _ _ ht0]
    push_cast
    ring_nf

end DLMF.Gamma
end
end
