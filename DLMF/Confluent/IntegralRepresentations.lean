/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.Confluence
public import DLMF.Confluent.Whittaker
public import DLMF.Confluent.Recurrence
public import DLMF.Bessel.Modified
public import DLMF.Bessel.KIntegralRep
public import DLMF.Hypergeometric.IntegralRepresentations

/-!
# Integral representations (DLMF §§13.4, 13.16)

Gauss kernels use cut-plane continuation, since their arguments range over the
negative ray. Argument bounds explicitly exclude zero where needed.

Euler, Laplace, Bessel, and vertical Barnes integrals are acquired on real
intervals or vertical lines. Hankel-loop and Pochhammer-double-loop formulas
13.4.9–13.4.15 are deferred pending a contour API, matching Chapter 15.
The `M` form of 13.4.1 is already `kummerM_eq_euler_integral` in `Basic`.
Tricomi's Laplace representation is proved in its full stated region. The Gauss
connection formula tends to the defining Tricomi connection, while its Euler
integral tends to the Laplace integral. The Tau Ceti contributors' second Beta
integrability theorem supplies the fixed majorant; Mathlib's real Bernoulli
inequality and dominated convergence justify the limit. Holomorphic continuation
in the argument and continuity in the second parameter cover every parameter.
The Whittaker W Laplace representation follows by an affine substitution.
The Gauss and Stieltjes representations 13.4.5, 13.4.6, 13.4.8, 13.16.6 and 13.16.9 use the
Kummer and Tricomi Laplace transforms, so they are proved in `DLMF.Confluent.Integrals`.
The exponential Barnes integrals 13.4.18 and 13.16.12 insert the Cahen–Mellin integral for
`e^{-x(1+τ)}` into Tricomi's Laplace integral and evaluate Euler's second Beta integral
in `τ`. Tricomi's contiguous relation in `a`, matched by the reciprocal Gamma recurrence,
then removes the restriction `Re a > 0`.
-/

@[expose] public section

open Complex Filter MeasureTheory intervalIntegral
open scoped Real Topology ENNReal
open DLMF.Hypergeometric
open DLMF.Bessel

noncomputable section

namespace DLMF.Confluent

@[dlmf 13.4.E1]
theorem regularized_euler_integral {a b z : ℂ} (ha : 0 < a.re) (hba : 0 < (b - a).re) :
    regularizedHGFun {a} {b} z =
      1 / (Gamma a * Gamma (b - a)) *
        ∫ t : ℝ in (0 : ℝ)..1,
          exp (z * t) * (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - a - 1) := by
  have hb : ∀ k : ℕ, b ≠ -k := not_neg_nat_of_re_pos (by
    have h : b.re = a.re + (b - a).re := by simp [sub_re]
    linarith)
  have hG : Gamma b ≠ 0 := Gamma_ne_zero hb
  have hM := kummerM_eq_euler_integral (a := a) (c := b) (z := z) ha hba
  rw [kummerM_eq_mul_regularizedHGFun hb] at hM
  apply mul_left_cancel₀ hG
  rw [hM]
  have hinter :
      (∫ t : ℝ in (0 : ℝ)..1,
        (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - a - 1) * exp (z * t)) =
      ∫ t : ℝ in (0 : ℝ)..1,
        exp (z * t) * (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - a - 1) :=
    intervalIntegral.integral_congr fun t _ => by ring
  rw [hinter]
  simp [div_eq_mul_inv, one_div, mul_assoc]

/-- Raising the denominator parameter by termwise Beta integration of the entire
regularized Kummer series. -/
@[dlmf 13.4.E2]
theorem regularized_parameter_integral {a b c z : ℂ}
    (hc : 0 < c.re) (hbc : 0 < (b - c).re) :
    regularizedHGFun {a} {b} z =
      1 / Gamma (b - c) *
        ∫ t : ℝ in (0 : ℝ)..1,
          regularizedHGFun {a} {c} (z * t) * (t : ℂ) ^ (c - 1) *
            (1 - (t : ℂ)) ^ (b - c - 1) := by
  let w : ℝ → ℂ := fun t => (t : ℂ) ^ (c - 1) * (1 - (t : ℂ)) ^ (b - c - 1)
  let d : ℕ → ℂ := fun n => regularizedHGFunCoeff {a} {c} n * z ^ n
  let F : ℕ → ℝ → ℂ := fun n t => w t * (d n * (t : ℂ) ^ n)
  have hw : IntervalIntegrable w volume 0 1 := betaIntegral_convergent hc hbc
  have hd : Summable (fun n => ‖d n‖) :=
    ((hasFPowerSeriesOnBall_regularizedConfluent a c).hasSum_mul_pow
      (z := z) (by simp)).summable.norm
  have hFi (n : ℕ) : IntervalIntegrable (F n) volume 0 1 :=
    hw.mul_continuousOn (by fun_prop)
  have hs := intervalIntegral.hasSum_integral_of_dominated_convergence
    (a := (0 : ℝ)) (b := 1) (μ := volume)
    (F := F) (f := fun t => w t * regularizedHGFun {a} {c} (z * t))
    (fun n t => ‖d n‖ * ‖w t‖) (fun n => (hFi n).def'.aestronglyMeasurable)
    (fun n => Filter.Eventually.of_forall fun t ht => ?_)
    (Filter.Eventually.of_forall fun t _ => hd.mul_right ‖w t‖)
    (by simp_rw [tsum_mul_right]; exact hw.norm.const_mul _)
    (Filter.Eventually.of_forall fun t _ => ?_)
  · have hterm (n : ℕ) : (∫ t : ℝ in (0 : ℝ)..1, F n t) =
        d n * betaIntegral (c + n) (b - c) := by
      rw [betaIntegral, ← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      intro t ht
      dsimp only
      rw [show c + n - 1 = (c - 1) + n by ring,
        cpow_add _ _ (ofReal_ne_zero.mpr ht.1.ne'), cpow_natCast]
      dsimp [F, w]
      ring
    have hscaled (n : ℕ) : 1 / Gamma (b - c) * (∫ t : ℝ in (0 : ℝ)..1, F n t) =
        regularizedHGFunCoeff {a} {b} n * z ^ n := by
      have hcn : 0 < (c + n).re := by simp; positivity
      have hbn : 0 < (b + n).re := by
        have he : b.re = c.re + (b - c).re := by simp
        simp only [add_re, natCast_re]
        linarith [Nat.cast_nonneg (α := ℝ) n]
      have hbeta : betaIntegral (c + n) (b - c) =
          Gamma (c + n) * Gamma (b - c) / Gamma (b + n) := by
        apply (eq_div_iff (Gamma_ne_zero_of_re_pos hbn)).mpr
        have he := Gamma_mul_Gamma_eq_betaIntegral hcn hbc
        rw [show c + n + (b - c) = b + n by ring] at he
        simpa [mul_comm] using he.symm
      rw [hterm, hbeta]
      dsimp only [d]
      rw [regularizedHGFunCoeff_singleton, regularizedHGFunCoeff_singleton]
      field_simp [Gamma_ne_zero_of_re_pos hbc, Gamma_ne_zero_of_re_pos hcn]
    have ht := hs.mul_left (1 / Gamma (b - c))
    simp_rw [hscaled] at ht
    have hseries := (hasFPowerSeriesOnBall_regularizedConfluent a b).hasSum_mul_pow
      (z := z) (by simp)
    rw [← ht.unique hseries]
    congr 1
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only [w]
    ring
  · rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    have ht1 : ‖(t : ℂ)‖ ≤ 1 := by
      simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1] using ht.2
    change ‖w t * (d n * (t : ℂ) ^ n)‖ ≤ ‖d n‖ * ‖w t‖
    simp only [norm_mul, norm_pow]
    calc
      ‖w t‖ * (‖d n‖ * ‖(t : ℂ)‖ ^ n) ≤ ‖w t‖ * (‖d n‖ * 1) := by
        gcongr
        exact pow_le_one₀ (norm_nonneg _) ht1
      _ = _ := by ring
  · convert ((hasFPowerSeriesOnBall_regularizedConfluent a c).hasSum_mul_pow
      (z := z * t) (by simp)).mul_left (w t) using 1
    funext n
    simp only [F, d, mul_pow]
    ring

/-- Gamma-weighted integral of regularized `₀F₁`, a generalization of
`integral_regularized0F1_gamma`: `∫₀^∞ e^{-t} t^{a-1} ₀F̃₁(;c;wt) dt = Γ(a) M̃(a,c,w)`. -/
theorem integral_exp_cpow_regularized0F1 {a c w : ℂ} (ha : 0 < a.re) :
    ∫ t : ℝ in Set.Ioi 0, (Real.exp (-t) : ℂ) * (t : ℂ) ^ (a - 1) *
      regularizedHGFun ∅ {c} (w * t) = Gamma a * regularizedHGFun {a} {c} w := by
  let d := regularizedHGFunCoeff (∅ : Multiset ℂ) {c}
  let F : ℕ → ℝ → ℂ := fun n t =>
    (d n * w ^ n) * ((Real.exp (-t) : ℂ) * (t : ℂ) ^ (a + n - 1))
  have han (n : ℕ) : 0 < (a + n).re := by simp; positivity
  have hFi (n : ℕ) : IntegrableOn (F n) (Set.Ioi 0) :=
    (GammaIntegral_convergent (han n)).const_mul _
  have hnorm (n : ℕ) : (∫ t : ℝ in Set.Ioi 0, ‖F n t‖) =
      ‖d n * w ^ n‖ * Real.Gamma (a.re + n) := by
    rw [Real.Gamma_eq_integral (by positivity : 0 < a.re + n), ← MeasureTheory.integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    simp only [F, norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le,
      norm_cpow_eq_rpow_re_of_pos ht, sub_re, add_re, natCast_re, one_re]
  have hcoeff (n : ℕ) : Gamma (a.re : ℂ) * regularizedHGFunCoeff {(a.re : ℂ)} {c} n =
      Gamma ((a.re : ℂ) + n) * d n := by
    dsimp only [d]
    have hp : poch (a.re : ℂ) n = Gamma ((a.re : ℂ) + n) / Gamma (a.re : ℂ) :=
      (Gamma_add_nat_div_Gamma_eq (n := n) (a.re : ℂ)
        (not_neg_nat_of_re_pos (by simpa using ha))).symm
    rw [regularizedHGFunCoeff_singleton, DLMF.Bessel.regularizedHGFunCoeff_empty, hp]
    field_simp [Gamma_ne_zero_of_re_pos (show 0 < (a.re : ℂ).re by simpa using ha)]
  have hnorm' (n : ℕ) : (∫ t : ℝ in Set.Ioi 0, ‖F n t‖) =
      Real.Gamma a.re *
        ‖regularizedHGFunCoeff {(a.re : ℂ)} {c} n * (‖w‖ : ℂ) ^ n‖ := by
    rw [hnorm]
    have he := congrArg norm (hcoeff n)
    simp only [norm_mul, Gamma_ofReal, Complex.norm_of_nonneg (Real.Gamma_pos_of_pos ha).le] at he
    rw [show (a.re : ℂ) + n = ((a.re + n : ℝ) : ℂ) by push_cast; rfl,
      Gamma_ofReal, Complex.norm_of_nonneg (Real.Gamma_pos_of_pos (by positivity)).le] at he
    simp only [norm_mul, norm_pow, norm_real, Real.norm_eq_abs, abs_norm]
    linear_combination -(‖w‖ ^ n) * he
  have hsum : Summable (fun n => ∫ t : ℝ in Set.Ioi 0, ‖F n t‖) := by
    simp_rw [hnorm']
    exact ((hasFPowerSeriesOnBall_regularizedConfluent (a.re : ℂ) c).hasSum_mul_pow
      (z := (‖w‖ : ℂ)) (by simp)).summable.norm.mul_left _
  have hterm (n : ℕ) : (∫ t : ℝ in Set.Ioi 0, F n t) =
      Gamma a * (regularizedHGFunCoeff {a} {c} n * w ^ n) := by
    rw [show F n = fun t => (d n * w ^ n) *
      ((Real.exp (-t) : ℂ) * (t : ℂ) ^ (a + n - 1)) from rfl,
      MeasureTheory.integral_const_mul, ← GammaIntegral, ← Gamma_eq_integral (han n)]
    dsimp only [d]
    have hp : poch a n = Gamma (a + n) / Gamma a :=
      (Gamma_add_nat_div_Gamma_eq (n := n) a (not_neg_nat_of_re_pos ha)).symm
    rw [DLMF.Bessel.regularizedHGFunCoeff_empty, regularizedHGFunCoeff_singleton, hp]
    field_simp [Gamma_ne_zero_of_re_pos ha]
  have hpoint (t : ℝ) (ht : 0 < t) : (∑' n, F n t) =
      (Real.exp (-t) : ℂ) * (t : ℂ) ^ (a - 1) * regularizedHGFun ∅ {c} (w * t) := by
    have hs := ((DLMF.Bessel.hasFPowerSeriesOnBall_regularized0F1 c).hasSum_mul_pow
      (z := w * t) (by simp)).mul_left ((Real.exp (-t) : ℂ) * (t : ℂ) ^ (a - 1))
    convert hs.tsum_eq using 1
    apply tsum_congr
    intro n
    dsimp only [F, d]
    rw [show a + n - 1 = (a - 1) + n by ring,
      cpow_add _ _ (ofReal_ne_zero.mpr ht.ne'), cpow_natCast, mul_pow]
    ring
  have hi := hasSum_integral_of_summable_integral_norm hFi hsum
  simp_rw [hterm] at hi
  have he := ((hasFPowerSeriesOnBall_regularizedConfluent a c).hasSum_mul_pow
    (z := w) (by simp)).mul_left (Gamma a)
  rw [← hi.unique he]
  exact setIntegral_congr_fun measurableSet_Ioi (fun t ht => (hpoint t ht).symm)

/-- `(z t)^w = z^w t^w` for `t > 0`. -/
private lemma mul_ofReal_cpow_of_pos {z : ℂ} (hz : z ≠ 0) {t : ℝ} (ht : 0 < t) (w : ℂ) :
    (z * t) ^ w = z ^ w * (t : ℂ) ^ w := by
  have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  rw [cpow_def_of_ne_zero (mul_ne_zero hz ht0), log_mul_ofReal t ht z hz,
    cpow_def_of_ne_zero hz, cpow_def_of_ne_zero ht0, ← ofReal_log ht.le, ← Complex.exp_add]
  ring_nf

/-- `((z t)^{1/2})^ν = z^{ν/2} t^{ν/2}` for `t > 0`. -/
private lemma sqrt_mul_cpow {z : ℂ} (hz : z ≠ 0) {t : ℝ} (ht : 0 < t) (ν : ℂ) :
    ((z * t) ^ (1 / 2 : ℂ)) ^ ν = z ^ (ν / 2) * (t : ℂ) ^ (ν / 2) := by
  have hzt : z * t ≠ 0 := mul_ne_zero hz (ofReal_ne_zero.mpr ht.ne')
  have him : (log (z * t) * (1 / 2 : ℂ)).im = arg (z * t) / 2 := by
    simp [log_im]; ring
  rw [← cpow_mul _ (by rw [him]; linarith [neg_pi_lt_arg (z * t), Real.pi_pos])
      (by rw [him]; linarith [arg_le_pi (z * t), Real.pi_pos]),
    show 1 / 2 * ν = ν / 2 by ring, mul_ofReal_cpow_of_pos hz ht]

/-- `((w)^{1/2})^2 = w`. -/
private lemma cpow_half_sq (w : ℂ) : (w ^ (1 / 2 : ℂ)) ^ 2 = w := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  · rw [sq, ← cpow_add _ _ hw]
    norm_num

/-- `J_ν(2√(zt)) = z^{ν/2} t^{ν/2} ₀F̃₁(ν+1; -zt)`. -/
theorem besselJ_two_sqrt {z : ℂ} (hz : z ≠ 0) {t : ℝ} (ht : 0 < t) (ν : ℂ) :
    besselJ ν (2 * (z * t) ^ (1 / 2 : ℂ)) =
      z ^ (ν / 2) * (t : ℂ) ^ (ν / 2) * regularizedHGFun ∅ {ν + 1} (-z * t) := by
  rw [besselJ_eq_regularized, show 2 * (z * t) ^ (1 / 2 : ℂ) / 2 = (z * t) ^ (1 / 2 : ℂ) by ring,
    sqrt_mul_cpow hz ht, mul_pow, cpow_half_sq]
  congr 2
  ring

/-- `I_ν(2√(zt)) = z^{ν/2} t^{ν/2} ₀F̃₁(ν+1; zt)`. -/
theorem besselI_two_sqrt {z : ℂ} (hz : z ≠ 0) {t : ℝ} (ht : 0 < t) (ν : ℂ) :
    besselI ν (2 * (z * t) ^ (1 / 2 : ℂ)) =
      z ^ (ν / 2) * (t : ℂ) ^ (ν / 2) * regularizedHGFun ∅ {ν + 1} (z * t) := by
  rw [besselI, show 2 * (z * t) ^ (1 / 2 : ℂ) / 2 = (z * t) ^ (1 / 2 : ℂ) by ring,
    sqrt_mul_cpow hz ht, mul_pow, cpow_half_sq]
  congr 2
  ring

@[dlmf 13.4.E3]
theorem regularized_bessel_integral {a b z : ℂ} (ha : 0 < a.re) (hz : 0 < z.re) :
    regularizedHGFun {a} {b} (-z) =
      z ^ ((1 - b) / 2) / Gamma a *
        ∫ t : ℝ in Set.Ioi 0,
          exp (-(t : ℂ)) * (t : ℂ) ^ (a - b / 2 - 1 / 2) * besselJ (b - 1) (2 * (z * t) ^ (1 / 2 : ℂ)) := by
  have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
  have hG : Gamma a ≠ 0 := Gamma_ne_zero_of_re_pos ha
  have hcongr : ∀ t ∈ Set.Ioi (0 : ℝ),
      exp (-(t : ℂ)) * (t : ℂ) ^ (a - b / 2 - 1 / 2) *
          besselJ (b - 1) (2 * (z * t) ^ (1 / 2 : ℂ)) =
        z ^ ((b - 1) / 2) * ((Real.exp (-t) : ℂ) * (t : ℂ) ^ (a - 1) *
          regularizedHGFun ∅ {b} (-z * t)) := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht)
    rw [besselJ_two_sqrt hz0 ht, show b - 1 + 1 = b by ring, ofReal_exp, ofReal_neg]
    have hp : (t : ℂ) ^ (a - b / 2 - 1 / 2) * (t : ℂ) ^ ((b - 1) / 2) = (t : ℂ) ^ (a - 1) := by
      rw [← cpow_add _ _ ht0]; ring_nf
    linear_combination (exp (-(t : ℂ)) * z ^ ((b - 1) / 2) *
      regularizedHGFun ∅ {b} (-z * t)) * hp
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, MeasureTheory.integral_const_mul,
    integral_exp_cpow_regularized0F1 ha]
  have hzz : z ^ ((1 - b) / 2) * z ^ ((b - 1) / 2) = 1 := by
    rw [← cpow_add _ _ hz0]; ring_nf; exact cpow_zero z
  rw [div_mul_eq_mul_div, eq_div_iff hG]
  linear_combination (-(Gamma a * regularizedHGFun {a} {b} (-z))) * hzz

/-- Absolute convergence of Tricomi's Laplace kernel throughout its stated
parameter region. A natural power of `1+t` supplies a finite Gamma majorant. -/
theorem kummerU_laplace_integrable {a b z : ℂ} (ha : 0 < a.re) (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => exp (-z * t) * (t : ℂ) ^ (a - 1) *
      (1 + (t : ℂ)) ^ (b - a - 1)) (Set.Ioi 0) := by
  let N : ℕ := ⌈(b - a - 1).re⌉₊
  let G : ℕ → ℝ → ℝ := fun k t => (N.choose k : ℝ) *
    (t ^ (a.re + k - 1) * Real.exp (-z.re * t))
  have hG (k : ℕ) : IntegrableOn (G k) (Set.Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1)
      (s := a.re + k - 1) (b := z.re)
      (by have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith) one_pos hz
    simp only [Real.rpow_one] at h
    exact h.const_mul _
  have hsum : IntegrableOn (fun t => ∑ k ∈ Finset.range (N + 1), G k t) (Set.Ioi 0) :=
    integrable_finsetSum _ (fun k _ => hG k)
  have hmajor (t : ℝ) (ht : 0 < t) : (∑ k ∈ Finset.range (N + 1), G k t) =
      Real.exp (-z.re * t) * t ^ (a.re - 1) * (1 + t) ^ N := by
    rw [add_comm (1 : ℝ) t, add_pow, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    dsimp [G]
    rw [show a.re + k - 1 = (a.re - 1) + k by ring,
      Real.rpow_add ht, Real.rpow_natCast, one_pow]
    ring
  refine Integrable.mono' hsum (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change 0 < t at ht
  rw [hmajor t ht, norm_mul, norm_mul, Complex.norm_exp,
    norm_cpow_eq_rpow_re_of_pos ht,
    show 1 + (t : ℂ) = ((1 + t : ℝ) : ℂ) by push_cast; rfl,
    norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < 1 + t)]
  simp only [neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero, sub_re, one_re]
  apply mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by simpa [N] using Nat.le_ceil (b - a - 1).re)

/-- Tricomi's normalized Laplace integral is continuous in the second parameter.
A fixed integer power dominates every kernel in a neighborhood of that parameter. -/
theorem continuous_kummerU_laplace_integral {a z : ℂ} (ha : 0 < a.re) (hz : 0 < z.re) :
    Continuous (fun b : ℂ => 1 / Gamma a * ∫ t : ℝ in Set.Ioi 0,
      exp (-z * t) * (t : ℂ) ^ (a - 1) * (1 + (t : ℂ)) ^ (b - a - 1)) := by
  apply continuous_iff_continuousAt.mpr
  intro b₀
  apply ContinuousAt.const_mul
  obtain ⟨N, hN⟩ : ∃ N : ℕ, b₀.re - a.re ≤ N := exists_nat_ge _
  let F (b : ℂ) (t : ℝ) := exp (-z * t) * (t : ℂ) ^ (a - 1) *
    (1 + (t : ℂ)) ^ (b - a - 1)
  have hmeas (b : ℂ) : AEStronglyMeasurable (F b) (volume.restrict (Set.Ioi 0)) :=
    Measurable.aestronglyMeasurable (by dsimp [F]; fun_prop)
  apply continuousAt_of_dominated (F := F) (bound := fun t => ‖F (a + N + 1) t‖)
    (Eventually.of_forall hmeas) ?_ (kummerU_laplace_integrable (b := a + N + 1) ha hz).norm ?_
  · filter_upwards [Metric.ball_mem_nhds b₀ (by norm_num : (0 : ℝ) < 1)] with b hb
    have hbR : b.re < b₀.re + 1 := by
      rw [Metric.mem_ball, dist_eq_norm] at hb
      have hh := (abs_lt.mp ((abs_re_le_norm (b - b₀)).trans_lt hb)).2
      simp only [sub_re] at hh
      linarith
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 0 < t at ht
    dsimp only [F]
    rw [norm_mul, norm_mul, norm_mul, norm_mul,
      show 1 + (t : ℂ) = ((1 + t : ℝ) : ℂ) by push_cast; rfl,
      norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < 1 + t),
      norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < 1 + t)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    simp only [sub_re, add_re, one_re, natCast_re]
    linarith
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 0 < t at ht
    have hbase : 1 + (t : ℂ) ≠ 0 := by
      have hh : 0 < (1 + (t : ℂ)).re := by simp; linarith
      intro he
      simp [he] at hh
    exact ((continuousAt_id.sub continuousAt_const).sub continuousAt_const).const_cpow
      (Or.inl hbase) |>.const_mul _

/-- Once the Laplace representation is identified off the integer second parameters,
continuity supplies every integer parameter as well. -/
theorem kummerU_laplace_of_eqOn_integerComplement {a b z : ℂ}
    (ha : 0 < a.re) (hz : 0 < z.re)
    (h : ∀ c ∈ integerComplement, kummerU a c z =
      1 / Gamma a * ∫ t : ℝ in Set.Ioi 0, exp (-z * t) * (t : ℂ) ^ (a - 1) *
        (1 + (t : ℂ)) ^ (c - a - 1)) :
    kummerU a b z = 1 / Gamma a * ∫ t : ℝ in Set.Ioi 0,
      exp (-z * t) * (t : ℂ) ^ (a - 1) * (1 + (t : ℂ)) ^ (b - a - 1) := by
  have hzN : z ≠ 0 := by intro he; simp [he] at hz
  exact eq_of_continuousAt_of_integerComplement
    (continuousAt_kummerU_comp continuousAt_const continuousAt_id hzN)
    ((continuous_kummerU_laplace_integral ha hz).continuousAt) h

/-- Bernoulli's inequality compares rational approximations to the exponential. -/
private lemma rpow_one_add_div_neg_le {u B T : ℝ} (hu : 0 ≤ u) (hB : 0 < B) (hBT : B ≤ T) :
    (1 + u / T) ^ (-T) ≤ (1 + u / B) ^ (-B) := by
  have hT : 0 < T := hB.trans_le hBT
  have hp := one_add_mul_self_le_rpow_one_add (s := u / T)
    (by have hh : 0 ≤ u / T := div_nonneg hu hT.le; linarith)
    ((le_div_iff₀ hB).mpr (by simpa using hBT) : 1 ≤ T / B)
  rw [show 1 + T / B * (u / T) = 1 + u / B by field_simp] at hp
  have hpow := Real.rpow_le_rpow (by positivity) hp hB.le
  rw [← Real.rpow_mul (by positivity), div_mul_cancel₀ _ hB.ne'] at hpow
  rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity)]
  exact (inv_le_inv₀ (by positivity) (by positivity)).mpr hpow

/-- The rational Euler kernels tend to Tricomi's Laplace kernel on a sufficiently
large positive real ray. The Tau Ceti contributors' second Beta integrability
theorem supplies the fixed majorant. -/
private lemma tendsto_tricomi_rational_integral {a b : ℂ} (ha : 0 < a.re) {x : ℝ}
    (hx : max 0 b.re < x) :
    Tendsto (fun T : ℝ => 1 / Gamma a * ∫ t : ℝ in Set.Ioi 0,
      (1 + (x : ℂ) * t / T) ^ (-(T : ℂ)) * (t : ℂ) ^ (a - 1) *
        (1 + (t : ℂ)) ^ (b - a - 1)) atTop
      (𝓝 (1 / Gamma a * ∫ t : ℝ in Set.Ioi 0,
        exp (-(x : ℂ) * t) * (t : ℂ) ^ (a - 1) * (1 + (t : ℂ)) ^ (b - a - 1))) := by
  let B : ℝ := (max 0 b.re + x) / 2
  have hx0 : 0 < x := (le_max_left _ _).trans_lt hx
  have hB : 0 < B := by dsimp [B]; linarith [le_max_left 0 b.re]
  have hBx : B ≤ x := by dsimp [B]; linarith
  have hBb : b.re < B := by dsimp [B]; linarith [le_max_right 0 b.re]
  let F (T t : ℝ) : ℂ := (1 + (x : ℂ) * t / T) ^ (-(T : ℂ)) * (t : ℂ) ^ (a - 1) *
    (1 + (t : ℂ)) ^ (b - a - 1)
  let G (t : ℝ) : ℝ := t ^ (a.re - 1) * (1 + t) ^ (-(a.re + (B - b.re + 1)))
  have hG : IntegrableOn G (Set.Ioi 0) :=
    TauCeti.integrableOn_rpow_mul_one_add_rpow ha (by linarith)
  have hmeas (T : ℝ) : AEStronglyMeasurable (F T) (volume.restrict (Set.Ioi 0)) :=
    Measurable.aestronglyMeasurable (by dsimp [F]; fun_prop)
  have hbound : ∀ᶠ T : ℝ in atTop, ∀ᵐ t ∂volume.restrict (Set.Ioi 0), ‖F T t‖ ≤ G t := by
    filter_upwards [eventually_ge_atTop B] with T hBT
    have hT : 0 < T := hB.trans_le hBT
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 0 < t at ht
    have hrat : (1 + x * t / T) ^ (-T) ≤ (1 + t) ^ (-B) := by
      apply (rpow_one_add_div_neg_le (mul_nonneg hx0.le ht.le) hB hBT).trans
      apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by linarith)
      have hxt : t ≤ x * t / B := (le_div_iff₀ hB).mpr (by nlinarith)
      linarith
    dsimp only [F, G]
    rw [norm_mul, norm_mul,
      show 1 + (x : ℂ) * t / T = ((1 + x * t / T : ℝ) : ℂ) by push_cast; rfl,
      show 1 + (t : ℂ) = ((1 + t : ℝ) : ℂ) by push_cast; rfl,
      norm_cpow_eq_rpow_re_of_pos (by positivity : 0 < 1 + x * t / T),
      norm_cpow_eq_rpow_re_of_pos ht,
      norm_cpow_eq_rpow_re_of_pos (by positivity : 0 < 1 + t)]
    simp only [neg_re, ofReal_re, sub_re, one_re]
    calc
      _ ≤ (1 + t) ^ (-B) * t ^ (a.re - 1) * (1 + t) ^ (b.re - a.re - 1) := by gcongr
      _ = _ := by
        rw [show -(a.re + (B - b.re + 1)) = -B + (b.re - a.re - 1) by ring]
        rw [Real.rpow_add (by positivity)]
        ring
  have hlim : ∀ᵐ t ∂volume.restrict (Set.Ioi 0), Tendsto (fun T => F T t) atTop
      (𝓝 (exp (-(x : ℂ) * t) * (t : ℂ) ^ (a - 1) * (1 + (t : ℂ)) ^ (b - a - 1))) := by
    filter_upwards with t
    have hh := (Complex.tendsto_one_add_div_cpow_exp ((x : ℂ) * t)).inv₀ (exp_ne_zero _)
    rw [← Complex.exp_neg] at hh
    simpa only [F, cpow_neg, neg_mul] using (hh.mul_const ((t : ℂ) ^ (a - 1))).mul_const
      ((1 + (t : ℂ)) ^ (b - a - 1))
  exact (tendsto_integral_filter_of_dominated_convergence G
    (Eventually.of_forall hmeas) hbound hG hlim).const_mul _

/-- Cancel only the two regular Gamma factors in the Gauss connection formula. -/
private lemma gauss_connection_cancel (C D A B E H K P Q : ℂ) (hC : C ≠ 0) (hD : D ≠ 0) :
    D / C * (C * A / (D * B) * P + C * E / (H * K) * Q) =
      A / B * P + D / K * (E / H) * Q := by
  rw [mul_add]
  congr 1
  · calc
      _ = (C * C⁻¹) * (D * D⁻¹) * (A / B * P) := by
        simp only [div_eq_mul_inv, mul_inv_rev]; ring
      _ = _ := by rw [mul_inv_cancel₀ hC, mul_inv_cancel₀ hD]; ring
  · calc
      _ = (C * C⁻¹) * (D / K * (E / H) * Q) := by
        simp only [div_eq_mul_inv, mul_inv_rev]; ring
      _ = _ := by rw [mul_inv_cancel₀ hC]; ring

/-- The normalized Gauss connection formula converges to the defining Tricomi connection. -/
private lemma tendsto_gauss_tricomi_connection {a b : ℂ} (ha : 0 < a.re)
    (hb : ∀ j : ℤ, b ≠ j) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun T : ℝ => Gamma (T + 1 - b) / Gamma (T + a + 1 - b) *
      ₂F₁ a (T : ℂ) (T + a + 1 - b) (1 - (x : ℂ) / T)) atTop
      (𝓝 (kummerU a b x)) := by
  have hM := tendsto_ordinaryHypergeometric_add_div_atTop a b 0 (x : ℂ)
  simp only [zero_add] at hM
  have hM₂ := tendsto_ordinaryHypergeometric_add_div_atTop (a - b + 1) (2 - b) (1 - b) (x : ℂ)
  have hQ := DLMF.Gamma.Gamma_ratio_power (a := 1 - b) (b := 0)
  simp only [add_zero, sub_zero] at hQ
  simp_rw [show ∀ T : ℝ, (T : ℂ) + (1 - b) = (T : ℂ) + 1 - b from fun T => by ring] at hQ
  have hsum := (hM.const_mul (Gamma (1 - b) / Gamma (a - b + 1))).add
    (((hQ.mul_const ((x : ℂ) ^ (1 - b))).mul hM₂).const_mul (Gamma (b - 1) / Gamma a))
  simp only [one_mul] at hsum
  rw [kummerU_eq_connection a b x hb, kummerUConnection]
  simp only [mul_assoc] at hsum ⊢
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop (max x (max 0 b.re) + 1)] with T hT
  have hTx : x < T := by linarith [le_max_left x (max 0 b.re)]
  have hT0 : 0 < T := hx.trans hTx
  have hTb : b.re < T := by
    linarith [le_max_right x (max 0 b.re), le_max_right 0 b.re]
  have hTc : 0 < (T + a + 1 - b : ℂ).re := by simp; linarith
  have hTd : 0 < (T + 1 - b : ℂ).re := by simp; linarith
  have hC := Gamma_ne_zero_of_re_pos hTc
  have hD := Gamma_ne_zero_of_re_pos hTd
  have he : ∀ j : ℤ, (T + a + 1 - b : ℂ) - a - T ≠ j := by
    intro j hj
    apply hb (1 - j)
    push_cast
    linear_combination -hj
  have hxt : 0 < x / T := div_pos hx hT0
  have hxT : x / T < 1 := (div_lt_one hT0).mpr hTx
  have hz : ‖1 - (x : ℂ) / T‖ < 1 := by
    rw [show 1 - (x : ℂ) / T = ((1 - x / T : ℝ) : ℂ) by push_cast; rfl,
      norm_real, Real.norm_of_nonneg (by linarith)]
    linarith
  have hw : ‖1 - (1 - (x : ℂ) / T)‖ < 1 := by
    rw [sub_sub_cancel, show (x : ℂ) / T = ((x / T : ℝ) : ℂ) by push_cast; rfl,
      norm_real, Real.norm_of_nonneg hxt.le]
    exact hxT
  have hc := DLMF.Hypergeometric.zero_first_connection_one_of_not_neg_nat
    (a := a) (b := (T : ℂ)) (not_neg_nat_of_re_pos hTc) he hz hw
  simp only [DLMF.Hypergeometric.oneFirst, DLMF.Hypergeometric.oneSecond, sub_sub_cancel] at hc
  rw [show (T + a + 1 - b : ℂ) - a - T + 1 = 2 - b by ring,
    show a + T - (T + a + 1 - b : ℂ) + 1 = b by ring,
    show (T + a + 1 - b : ℂ) - a - T = 1 - b by ring,
    show (T + a + 1 - b : ℂ) - a = T + 1 - b by ring,
    show (T + a + 1 - b : ℂ) - T = a - b + 1 by ring,
    show a + T - (T + a + 1 - b : ℂ) = b - 1 by ring] at hc
  rw [hc, gauss_connection_cancel _ _ _ _ _ _ _ _ _ hC hD,
    DLMF.Hypergeometric.ordinaryHypergeometric_symm (T + 1 - b) (a - b + 1)]
  have hp : ((x : ℂ) / T) ^ (1 - b) = (x : ℂ) ^ (1 - b) / (T : ℂ) ^ (1 - b) := by
    exact div_cpow_ofReal_nonneg hx.le hT0.le _
  rw [hp, show 1 - b + (T : ℂ) = T + 1 - b by ring]
  ring

/-- Euler's half-line representation supplies the same normalized Gauss limit. -/
private lemma gauss_tricomi_rational_integral {a b : ℂ} (ha : 0 < a.re) {x T : ℝ}
    (hx : 0 < x) (hTx : x < T) (hTb : b.re < T) :
    Gamma (T + 1 - b) / Gamma (T + a + 1 - b) *
      ₂F₁ a (T : ℂ) (T + a + 1 - b) (1 - (x : ℂ) / T) =
        1 / Gamma a * ∫ t : ℝ in Set.Ioi 0,
          (1 + (x : ℂ) * t / T) ^ (-(T : ℂ)) * (t : ℂ) ^ (a - 1) *
            (1 + (t : ℂ)) ^ (b - a - 1) := by
  have hT : 0 < T := hx.trans hTx
  have hca : 0 < ((T + a + 1 - b : ℂ) - a).re := by simp; linarith
  have hc : 0 < (T + a + 1 - b : ℂ).re := by simp; linarith
  have hD : Gamma (T + 1 - b) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hC := Gamma_ne_zero_of_re_pos hc
  have hz : ‖1 - (x : ℂ) / T‖ < 1 := by
    rw [show 1 - (x : ℂ) / T = ((1 - x / T : ℝ) : ℂ) by push_cast; rfl,
      norm_real, Real.norm_of_nonneg (by rw [sub_nonneg, div_le_one hT]; exact hTx.le)]
    linarith [div_pos hx hT]
  have he := DLMF.Hypergeometric.integral_Ioi (a := (T : ℂ)) (b := a)
    (c := T + a + 1 - b) ha hca hz
  rw [DLMF.Hypergeometric.regularizedGaussHGFun_eq_div_Gamma (not_neg_nat_of_re_pos hc),
    DLMF.Hypergeometric.ordinaryHypergeometric_symm (T : ℂ) a,
    show (T + a + 1 - b : ℂ) - a = T + 1 - b by ring,
    show (T : ℂ) - (T + a + 1 - b) = b - a - 1 by ring] at he
  have hn : Gamma (T + 1 - b) / Gamma (T + a + 1 - b) *
      ₂F₁ a (T : ℂ) (T + a + 1 - b) (1 - (x : ℂ) / T) =
      1 / Gamma a * ∫ t : ℝ in Set.Ioi 0,
        (t : ℂ) ^ (a - 1) * (t + 1 : ℂ) ^ (b - a - 1) /
          ((t : ℂ) - (1 - (x : ℂ) / T) * t + 1) ^ (T : ℂ) := by
    have hcancel (A D I : ℂ) (hD : D ≠ 0) : D * (1 / (A * D) * I) = 1 / A * I := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      calc
        _ = (D * D⁻¹) * (A⁻¹ * I) := by ring
        _ = _ := by rw [mul_inv_cancel₀ hD]; ring
    calc
      _ = Gamma (T + 1 - b) *
          (₂F₁ a (T : ℂ) (T + a + 1 - b) (1 - (x : ℂ) / T) /
            Gamma (T + a + 1 - b)) := by ring
      _ = _ := by
        rw [he]
        exact hcancel _ _ _ hD
  rw [hn]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  dsimp only
  rw [show (t : ℂ) - (1 - (x : ℂ) / T) * t + 1 = 1 + (x : ℂ) * t / T by ring,
    show (t + 1 : ℂ) = 1 + t by ring, cpow_neg]
  ring

/-- Tricomi's Laplace representation on a nonempty real ray follows by comparing
the Euler and connection limits of the same Gauss function. -/
private lemma kummerU_laplace_of_real_large {a b : ℂ} (ha : 0 < a.re)
    (hb : ∀ j : ℤ, b ≠ j) {x : ℝ} (hx : max 0 b.re < x) :
    kummerU a b x = 1 / Gamma a * ∫ t : ℝ in Set.Ioi 0,
      exp (-(x : ℂ) * t) * (t : ℂ) ^ (a - 1) * (1 + (t : ℂ)) ^ (b - a - 1) := by
  have hx0 : 0 < x := (le_max_left _ _).trans_lt hx
  apply tendsto_nhds_unique (tendsto_gauss_tricomi_connection ha hb hx0)
  apply (tendsto_tricomi_rational_integral ha hx).congr'
  filter_upwards [eventually_gt_atTop (max x b.re)] with T hT
  exact (gauss_tricomi_rational_integral ha hx0
    ((le_max_left _ _).trans_lt hT) ((le_max_right _ _).trans_lt hT)).symm

/-- Holomorphic dependence of Tricomi's normalized Laplace integral on the argument. -/
theorem differentiableOn_kummerU_laplace_integral {a b : ℂ} (ha : 0 < a.re) :
    DifferentiableOn ℂ (fun z : ℂ => 1 / Gamma a * ∫ t : ℝ in Set.Ioi 0,
      exp (-z * t) * (t : ℂ) ^ (a - 1) * (1 + (t : ℂ)) ^ (b - a - 1))
      {z : ℂ | 0 < z.re} := by
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
  let F (z : ℂ) (t : ℝ) := exp (-z * t) * (t : ℂ) ^ (a - 1) *
    (1 + (t : ℂ)) ^ (b - a - 1)
  let G (t : ℝ) := ‖exp (-(δ : ℂ) * t) * (t : ℂ) ^ a *
    (1 + (t : ℂ)) ^ (b - a - 1)‖
  have hG : IntegrableOn G (Set.Ioi 0) := by
    change Integrable G (volume.restrict (Set.Ioi 0))
    have h := (kummerU_laplace_integrable (a := a + 1) (b := b + 1) (z := (δ : ℂ))
      (by simp; linarith) (by simpa using hδ)).norm
    simpa only [G, add_sub_cancel_right, show (b + 1) - (a + 1) - 1 = b - a - 1 by ring] using h
  have hmeas (z : ℂ) : AEStronglyMeasurable (F z) (volume.restrict (Set.Ioi 0)) :=
    Measurable.aestronglyMeasurable (by dsimp [F]; fun_prop)
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioi 0)) (F := F) (F' := fun z t => -(t : ℂ) * F z t)
    (bound := G) (Metric.ball_mem_nhds _ hδ) (Eventually.of_forall hmeas)
    (kummerU_laplace_integrable ha hz₀)
    (Measurable.aestronglyMeasurable (by dsimp [F]; fun_prop)) ?_ hG ?_
  · exact (hd.2.const_mul (1 / Gamma a)).differentiableAt.differentiableWithinAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht z hz
    change 0 < t at ht
    have he : Real.exp (-z.re * t) ≤ Real.exp (-δ * t) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hre z hz]
    have hp : t ^ (a.re - 1) * t = t ^ a.re := by
      have hh := Real.rpow_add_one ht.ne' (a.re - 1)
      simpa only [sub_add_cancel] using hh.symm
    dsimp only [F, G]
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg ht.le]
    simp only [norm_mul, Complex.norm_exp, neg_re, mul_re, ofReal_re, ofReal_im,
      mul_zero, sub_zero, norm_cpow_eq_rpow_re_of_pos ht, sub_re, one_re]
    calc
      _ = Real.exp (-z.re * t) * (t ^ (a.re - 1) * t) *
          ‖(1 + (t : ℂ)) ^ (b - a - 1)‖ := by ring
      _ = Real.exp (-z.re * t) * t ^ a.re * ‖(1 + (t : ℂ)) ^ (b - a - 1)‖ := by rw [hp]
      _ ≤ _ := by gcongr
  · filter_upwards with t z _
    have hh := (((hasDerivAt_id z).neg.mul_const (t : ℂ)).cexp.mul_const
      ((t : ℂ) ^ (a - 1))).mul_const ((1 + (t : ℂ)) ^ (b - a - 1))
    simp only [Pi.neg_apply, id_eq] at hh
    convert hh using 1
    dsimp only [F]
    ring

/-- The real-ray identity extends holomorphically to the full right half-plane. -/
private lemma kummerU_laplace_of_not_int {a b z : ℂ} (ha : 0 < a.re)
    (hb : ∀ j : ℤ, b ≠ j) (hz : 0 < z.re) :
    kummerU a b z = 1 / Gamma a * ∫ t : ℝ in Set.Ioi 0,
      exp (-z * t) * (t : ℂ) ^ (a - 1) * (1 + (t : ℂ)) ^ (b - a - 1) := by
  let V : Set ℂ := {z | 0 < z.re}
  have hVo : IsOpen V := isOpen_lt continuous_const continuous_re
  let J (z : ℂ) := 1 / Gamma a * ∫ t : ℝ in Set.Ioi 0,
    exp (-z * t) * (t : ℂ) ^ (a - 1) * (1 + (t : ℂ)) ^ (b - a - 1)
  have hU : AnalyticOnNhd ℂ (kummerU a b) V := by
    apply DifferentiableOn.analyticOnNhd _ hVo
    intro w hw
    exact (differentiableAt_kummerU a b (Or.inl hw)).differentiableWithinAt
  have hJ : AnalyticOnNhd ℂ J V := (differentiableOn_kummerU_laplace_integral ha).analyticOnNhd hVo
  let x₀ : ℝ := max 0 b.re + 1
  have hx₀ : max 0 b.re < x₀ := by dsimp [x₀]; linarith
  have hx₀0 : 0 < x₀ := (le_max_left _ _).trans_lt hx₀
  have hfreq : ∃ᶠ w in 𝓝[≠] (x₀ : ℂ), kummerU a b w = J w := by
    have ht : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[≠] x₀) (𝓝[≠] (x₀ : ℂ)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · exact (continuous_ofReal.tendsto x₀).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with r hr
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, ofReal_inj] using hr
    apply ht.frequently
    apply Eventually.frequently
    filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds hx₀)] with r hr
    exact kummerU_laplace_of_real_large ha hb hr
  exact hU.eqOn_of_preconnected_of_frequently_eq hJ (convex_halfSpace_re_gt 0).isPreconnected
    (by change 0 < (x₀ : ℂ).re; simpa using hx₀0) hfreq hz

@[dlmf 13.4.E4]
theorem kummerU_laplace {a b z : ℂ} (ha : 0 < a.re) (hz : 0 < z.re) :
    kummerU a b z =
      1 / Gamma a *
        ∫ t : ℝ in Set.Ioi 0,
          exp (-z * t) * (t : ℂ) ^ (a - 1) * (1 + (t : ℂ)) ^ (b - a - 1) := by
  exact kummerU_laplace_of_eqOn_integerComplement ha hz
    (fun c hc => kummerU_laplace_of_not_int ha (forall_of_mem_integerComplement hc) hz)

/-- The nonnegative integer shifted family specializes the full Tricomi representation. -/
theorem kummerU_laplace_shift_nat {a z : ℂ} (ha : 0 < a.re) (hz : 0 < z.re) (N : ℕ) :
    kummerU a (a + N + 1) z = 1 / Gamma a * ∫ t : ℝ in Set.Ioi 0,
      exp (-z * t) * (t : ℂ) ^ (a - 1) * (1 + (t : ℂ)) ^ ((a + N + 1) - a - 1) :=
  kummerU_laplace ha hz

/-- The unit parameter shift specializes the full Tricomi representation. -/
theorem kummerU_laplace_shift_one {a z : ℂ} (ha : 0 < a.re) (hz : 0 < z.re) :
    kummerU a (a + 1) z = 1 / Gamma a * ∫ t : ℝ in Set.Ioi 0,
      exp (-z * t) * (t : ℂ) ^ (a - 1) * (1 + (t : ℂ)) ^ ((a + 1) - a - 1) :=
  kummerU_laplace ha hz

section BesselKIntegral

open Set

/-- Complex powers of a positive real through the real logarithm. -/
private lemma ofReal_cpow_eq_exp_log_aux {r : ℝ} (hr : 0 < r) (c : ℂ) :
    (r : ℂ) ^ c = exp (c * Real.log r) := by
  rw [cpow_def_of_ne_zero (by exact_mod_cast hr.ne'), ← ofReal_log hr.le, mul_comm]

/-- The double integrand behind DLMF 13.4.7. -/
def besselKUKernel (a b : ℂ) (x : ℝ) (t s : ℝ) : ℂ :=
  exp (-(t : ℂ)) * (t : ℂ) ^ (a - b) * (exp (-(s : ℂ) - x * t / s) * (s : ℂ) ^ (b - 2))

/-- Step 1: insert Schläfli's integral for `K_{b-1}(2√(xt))`. -/
theorem besselK_kernel_eq_integral {a b : ℂ} {x t : ℝ} (hx : 0 < x) (ht : 0 < t) :
    exp (-(t : ℂ)) * (t : ℂ) ^ (a - b / 2 - 1 / 2) * besselK (b - 1) (2 * ((x : ℂ) * t) ^ (1 / 2 : ℂ)) =
      1 / 2 * (x : ℂ) ^ ((1 - b) / 2) * ∫ s : ℝ in Ioi 0, besselKUKernel a b x t s := by
  have hxt : 0 < x * t := mul_pos hx ht
  have hy : 0 < 2 * Real.sqrt (x * t) := by positivity
  have hsq : ((Real.sqrt (x * t) : ℝ) : ℂ) = ((x : ℂ) * t) ^ (1 / 2 : ℂ) := by
    rw [Real.sqrt_eq_rpow, ofReal_cpow hxt.le]; push_cast; ring_nf
  have harg : 2 * ((x : ℂ) * t) ^ (1 / 2 : ℂ) = ((2 * Real.sqrt (x * t) : ℝ) : ℂ) := by
    push_cast; rw [hsq]
  rw [harg, besselK_ofReal_eq_integral_schlafli' hy]
  have hint : ∫ s : ℝ in Ioi 0, besselKUKernel a b x t s = exp (-(t : ℂ)) * (t : ℂ) ^ (a - b) *
      ∫ s : ℝ in Ioi 0, exp (-(s : ℂ) - ((2 * Real.sqrt (x * t) : ℝ) : ℂ) ^ 2 / (4 * s)) *
        (s : ℂ) ^ (b - 1 - 1) := by
    rw [← MeasureTheory.integral_const_mul]
    congr 1
    funext s
    unfold besselKUKernel
    have h4 : ((2 * Real.sqrt (x * t) : ℝ) : ℂ) ^ 2 = 4 * (x * t : ℝ) := by
      rw [← ofReal_pow, mul_pow, Real.sq_sqrt hxt.le]; push_cast; ring
    rw [h4, show b - 1 - 1 = b - 2 by ring]
    push_cast
    field_simp
  rw [hint]
  have hs2 : ((2 * Real.sqrt (x * t) : ℝ) : ℂ) / 2 = ((Real.sqrt (x * t) : ℝ) : ℂ) := by
    push_cast; ring
  rw [hs2, ofReal_cpow_eq_exp_log_aux (Real.sqrt_pos.mpr hxt), ofReal_cpow_eq_exp_log_aux ht,
    ofReal_cpow_eq_exp_log_aux hx, ofReal_cpow_eq_exp_log_aux ht, Real.log_sqrt hxt.le,
    Real.log_mul hx.ne' ht.ne']
  set I := ∫ s : ℝ in Ioi 0, exp (-(s : ℂ) - ((2 * Real.sqrt (x * t) : ℝ) : ℂ) ^ 2 / (4 * s)) *
        (s : ℂ) ^ (b - 1 - 1)
  have key : exp (-(t : ℂ)) * exp ((a - b / 2 - 1 / 2) * (Real.log t : ℂ)) *
      exp (-(b - 1) * ((Real.log x + Real.log t) / 2 : ℝ)) =
      exp ((1 - b) / 2 * (Real.log x : ℂ)) * (exp (-(t : ℂ)) * exp ((a - b) * (Real.log t : ℂ))) := by
    rw [← exp_add, ← exp_add, ← exp_add, ← exp_add]
    congr 1
    push_cast
    ring
  linear_combination (1 / 2 * I) * key

/-- Step 2: the inner Gamma integral in `t`. -/
theorem integral_besselKUKernel_t {a b : ℂ} {x s : ℝ} (hx : 0 < x) (hs : 0 < s)
    (hab : 0 < (a - b + 1).re) :
    ∫ t : ℝ in Ioi 0, besselKUKernel a b x t s =
      exp (-(s : ℂ)) * (s : ℂ) ^ (b - 2) * (((1 / (1 + x / s) : ℝ) : ℂ) ^ (a - b + 1) *
        Gamma (a - b + 1)) := by
  have hr : 0 < 1 + x / s := by positivity
  have h := integral_cpow_mul_exp_neg_mul_Ioi hab hr
  rw [show a - b + 1 - 1 = a - b by ring] at h
  rw [ofReal_div, ofReal_one, ← h, ← MeasureTheory.integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  unfold besselKUKernel
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have he : exp (-(t : ℂ)) * exp (-(s : ℂ) - x * t / s) =
      exp (-(s : ℂ)) * exp (-(((1 + x / s : ℝ) : ℂ) * t)) := by
    rw [← exp_add, ← exp_add]; congr 1; push_cast; field_simp; ring
  linear_combination (t : ℂ) ^ (a - b) * (s : ℂ) ^ (b - 2) * he

/-- Step 3: the outer integral in `s` is a scaled Tricomi Laplace integral. -/
theorem integral_besselKU_s {a b : ℂ} {x : ℝ} (hx : 0 < x) :
    ∫ s : ℝ in Ioi 0, exp (-(s : ℂ)) * (s : ℂ) ^ (b - 2) * ((1 / (1 + x / s) : ℝ) : ℂ) ^ (a - b + 1) =
      (x : ℂ) ^ (b - 1) * ∫ u : ℝ in Ioi 0,
        exp (-(x : ℂ) * u) * (u : ℂ) ^ (a - 1) * (1 + (u : ℂ)) ^ (b - a - 1) := by
  have h := integral_comp_mul_left_Ioi (fun s : ℝ => exp (-(s : ℂ)) * (s : ℂ) ^ (b - 2) *
    ((1 / (1 + x / s) : ℝ) : ℂ) ^ (a - b + 1)) 0 hx
  rw [mul_zero] at h
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  rw [← smul_eq_mul (a := (x : ℂ) ^ (b - 1)), ← MeasureTheory.integral_smul]
  have h2 : ∫ s : ℝ in Ioi 0, exp (-(s : ℂ)) * (s : ℂ) ^ (b - 2) *
      ((1 / (1 + x / s) : ℝ) : ℂ) ^ (a - b + 1) = (x : ℂ) * ∫ u : ℝ in Ioi 0,
      exp (-((x * u : ℝ) : ℂ)) * ((x * u : ℝ) : ℂ) ^ (b - 2) *
        ((1 / (1 + x / (x * u)) : ℝ) : ℂ) ^ (a - b + 1) := by
    rw [h, real_smul]
    push_cast
    field_simp
  rw [h2, ← smul_eq_mul (a := (x : ℂ)), ← MeasureTheory.integral_smul]
  refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
  have hu0 : (0 : ℝ) < u := hu
  have hq : 1 / (1 + x / (x * u)) = u / (1 + u) := by field_simp; ring
  rw [hq, smul_eq_mul, smul_eq_mul, ofReal_cpow_eq_exp_log_aux (mul_pos hx hu0),
    ofReal_cpow_eq_exp_log_aux (by positivity : 0 < u / (1 + u)), Real.log_mul hx.ne' hu0.ne',
    Real.log_div hu0.ne' (by positivity : (1 + u) ≠ 0), ofReal_cpow_eq_exp_log_aux hx,
    ofReal_cpow_eq_exp_log_aux hu0,
    show (1 + (u : ℂ)) = ((1 + u : ℝ) : ℂ) by push_cast; ring,
    ofReal_cpow_eq_exp_log_aux (by positivity : 0 < 1 + u)]
  have hxe : (x : ℂ) = exp (Real.log x) := by rw [← ofReal_exp, Real.exp_log hx]
  conv_lhs => rw [hxe]
  have key : ∀ A B C D : ℂ, exp A * (exp B * exp C * exp D) = exp (A + B + C + D) := by
    intro A B C D; rw [exp_add, exp_add, exp_add]; ring
  have key2 : ∀ A B C D : ℂ, exp A * (exp B * exp C * exp D) = exp (A + B + C + D) := key
  rw [key, key2]
  congr 1
  push_cast
  ring

/-- Measurability of the double integrand. -/
theorem measurable_besselKUKernel (a b : ℂ) (x : ℝ) :
    Measurable (Function.uncurry (besselKUKernel a b x)) := by
  unfold besselKUKernel Function.uncurry
  fun_prop

/-- The norm of the double integrand. -/
theorem norm_besselKUKernel {a b : ℂ} {x t s : ℝ} (ht : 0 < t) (hs : 0 < s) :
    ‖besselKUKernel a b x t s‖ = Real.exp (-s) * s ^ (b.re - 2) *
      (t ^ (a - b).re * Real.exp (-(1 + x / s) * t)) := by
  unfold besselKUKernel
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp,
    norm_cpow_eq_rpow_re_of_pos ht, norm_cpow_eq_rpow_re_of_pos hs]
  have h1 : (-(s : ℂ) - x * t / s).re = -s - x * t / s := by
    rw [show (x : ℂ) * t / s = ((x * t / s : ℝ) : ℂ) by push_cast; ring]
    simp
  rw [h1]
  simp only [neg_re, ofReal_re, sub_re]
  have : Real.exp (-t) * Real.exp (-s - x * t / s) = Real.exp (-s) * Real.exp (-(1 + x / s) * t) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; field_simp; ring
  simp only [show (2 : ℂ).re = 2 by norm_num]
  linear_combination t ^ (a - b).re * s ^ (b.re - 2) * this

/-- Absolute integrability of the double integrand on `(0,∞)²`. -/
theorem integrable_besselKUKernel {a b : ℂ} {x : ℝ} (hx : 0 < x) (hab : 0 < (a - b + 1).re)
    (ha : 0 < a.re) :
    Integrable (Function.uncurry (besselKUKernel a b x))
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  set A := (a - b).re
  have hA : -1 < A := by simp only [A, sub_re] at hab ⊢; simp at hab; linarith
  rw [integrable_prod_iff' (measurable_besselKUKernel a b x).aestronglyMeasurable]
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : (0 : ℝ) < s := hs
    have hg := (integrableOn_rpow_mul_exp_neg_mul_rpow (s := A) (p := 1) hA one_pos
      (by positivity : 0 < 1 + x / s)).const_mul (Real.exp (-s) * s ^ (b.re - 2))
    refine hg.mono' ((measurable_besselKUKernel a b x).comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Function.uncurry_apply_pair, norm_besselKUKernel ht hs0, Real.rpow_one]
  · have hcl : ∀ s ∈ Ioi (0 : ℝ), ∫ t : ℝ in Ioi 0, ‖Function.uncurry (besselKUKernel a b x) (t, s)‖ =
        Real.exp (-s) * s ^ (b.re - 2) * ((1 / (1 + x / s)) ^ (A + 1) * Real.Gamma (A + 1)) := by
      intro s hs
      have hs0 : (0 : ℝ) < s := hs
      rw [← Real.integral_rpow_mul_exp_neg_mul_Ioi (by linarith) (by positivity : 0 < 1 + x / s),
        ← MeasureTheory.integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      rw [Function.uncurry_apply_pair, norm_besselKUKernel ht hs0, add_sub_cancel_right]
      simp only [A]
      ring_nf
    refine Integrable.congr ?_ ((ae_restrict_mem measurableSet_Ioi).mono fun s hs => (hcl s hs).symm)
    have hG := (Real.GammaIntegral_convergent ha).const_mul
      (Real.Gamma (A + 1) * x ^ (-(A + 1)))
    refine hG.mono' ?_ ?_
    · exact (by fun_prop : Measurable fun s : ℝ => Real.exp (-s) * s ^ (b.re - 2) *
        ((1 / (1 + x / s)) ^ (A + 1) * Real.Gamma (A + 1))).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have hs0 : (0 : ℝ) < s := hs
      have hGp : 0 < Real.Gamma (A + 1) := Real.Gamma_pos_of_pos (by linarith)
      have hq : 1 / (1 + x / s) = s / (s + x) := by field_simp
      rw [Real.norm_of_nonneg (by positivity), hq, Real.div_rpow hs0.le (by positivity)]
      have hsx : x ^ (A + 1) ≤ (s + x) ^ (A + 1) :=
        Real.rpow_le_rpow hx.le (by linarith) (by linarith)
      have hsA : s ^ (b.re - 2) * s ^ (A + 1) = s ^ (a.re - 1) := by
        rw [← Real.rpow_add hs0]; congr 1; simp only [A, sub_re]; ring
      have hxp : 0 < x ^ (A + 1) := Real.rpow_pos_of_pos hx _
      rw [Real.rpow_neg hx.le]
      have h3 : s ^ (A + 1) / (s + x) ^ (A + 1) ≤ s ^ (A + 1) * (x ^ (A + 1))⁻¹ := by
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left (inv_anti₀ hxp hsx) (by positivity)
      calc Real.exp (-s) * s ^ (b.re - 2) * (s ^ (A + 1) / (s + x) ^ (A + 1) * Real.Gamma (A + 1))
          ≤ Real.exp (-s) * s ^ (b.re - 2) * (s ^ (A + 1) * (x ^ (A + 1))⁻¹ * Real.Gamma (A + 1)) := by
            gcongr
        _ = Real.Gamma (A + 1) * (x ^ (A + 1))⁻¹ * (Real.exp (-s) * (s ^ (b.re - 2) * s ^ (A + 1))) := by
            ring
        _ = _ := by rw [hsA]

/-- DLMF 13.4.7 for real positive argument. -/
theorem kummerU_eq_integral_besselK_ofReal {a b : ℂ} {x : ℝ} (hx : 0 < x)
    (ha : (b - 1).re < a.re) (ha0 : 0 < a.re) :
    kummerU a b x = 2 * (x : ℂ) ^ ((1 - b) / 2) / (Gamma a * Gamma (a - b + 1)) *
      ∫ t : ℝ in Ioi 0, exp (-(t : ℂ)) * (t : ℂ) ^ (a - b / 2 - 1 / 2) *
        besselK (b - 1) (2 * ((x : ℂ) * t) ^ (1 / 2 : ℂ)) := by
  have hab : 0 < (a - b + 1).re := by simp at ha ⊢; linarith
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hxre : 0 < (x : ℂ).re := by simpa using hx
  have h1 : ∫ t : ℝ in Ioi 0, exp (-(t : ℂ)) * (t : ℂ) ^ (a - b / 2 - 1 / 2) *
        besselK (b - 1) (2 * ((x : ℂ) * t) ^ (1 / 2 : ℂ)) =
      1 / 2 * (x : ℂ) ^ ((1 - b) / 2) * ∫ t : ℝ in Ioi 0, ∫ s : ℝ in Ioi 0,
        besselKUKernel a b x t s := by
    rw [← MeasureTheory.integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi fun t ht => besselK_kernel_eq_integral hx ht
  have h2 : ∫ t : ℝ in Ioi 0, ∫ s : ℝ in Ioi 0, besselKUKernel a b x t s =
      Gamma (a - b + 1) * ∫ s : ℝ in Ioi 0, exp (-(s : ℂ)) * (s : ℂ) ^ (b - 2) *
        ((1 / (1 + x / s) : ℝ) : ℂ) ^ (a - b + 1) := by
    rw [integral_integral_swap (integrable_besselKUKernel hx hab ha0), ← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    rw [integral_besselKUKernel_t hx hs hab]
    ring
  have hU := kummerU_laplace ha0 (b := b) (z := (x : ℂ)) hxre
  have hG : Gamma a ≠ 0 := Gamma_ne_zero_of_re_pos ha0
  have hG' : Gamma (a - b + 1) ≠ 0 := Gamma_ne_zero_of_re_pos hab
  rw [h1, h2, integral_besselKU_s hx]
  set L := ∫ u : ℝ in Ioi 0, exp (-(x : ℂ) * u) * (u : ℂ) ^ (a - 1) * (1 + (u : ℂ)) ^ (b - a - 1)
  have hL : L = Gamma a * kummerU a b x := by rw [hU]; field_simp
  rw [hL]
  have hp : (x : ℂ) ^ ((1 - b) / 2) * (x : ℂ) ^ ((1 - b) / 2) * (x : ℂ) ^ (b - 1) = 1 := by
    rw [← cpow_add _ _ hx0, ← cpow_add _ _ hx0, show (1 - b) / 2 + (1 - b) / 2 + (b - 1) = 0 by
      ring, cpow_zero]
  field_simp
  linear_combination (-(kummerU a b x)) * hp

/-- `(r w)^c = r^c w^c` for positive real `r`. -/
private lemma ofReal_mul_cpow_aux {r : ℝ} (hr : 0 < r) {w : ℂ} (hw : w ≠ 0) (c : ℂ) :
    ((r : ℂ) * w) ^ c = (r : ℂ) ^ c * w ^ c := by
  rw [cpow_def_of_ne_zero (mul_ne_zero (by exact_mod_cast hr.ne') hw), log_ofReal_mul hr hw,
    cpow_def_of_ne_zero (by exact_mod_cast hr.ne'), cpow_def_of_ne_zero hw, ← exp_add,
    ofReal_log hr.le]
  ring_nf

/-- The slit plane is stable under positive real scaling. -/
theorem mul_ofReal_mem_slitPlane {z : ℂ} (hz : z ∈ slitPlane) {t : ℝ} (ht : 0 < t) :
    z * t ∈ slitPlane := by
  rw [mem_slitPlane_iff] at hz ⊢
  simp only [mul_re, mul_im, ofReal_re, ofReal_im, mul_zero, sub_zero, zero_add]
  rcases hz with h | h
  · exact Or.inl (mul_pos h ht)
  · exact Or.inr (mul_ne_zero h ht.ne')

/-- `2 (z t)^{1/2} = 2 √t z^{1/2}` for `t > 0`. -/
theorem two_mul_cpow_half_mul_ofReal {z : ℂ} (hz : z ≠ 0) {t : ℝ} (ht : 0 < t) :
    2 * (z * t) ^ (1 / 2 : ℂ) = 2 * (Real.sqrt t : ℂ) * z ^ (1 / 2 : ℂ) := by
  rw [mul_comm z, ofReal_mul_cpow_aux ht hz, Real.sqrt_eq_rpow, ofReal_cpow ht.le]
  push_cast; ring

/-- The real part of `2 (z t)^{1/2}`. -/
theorem re_two_mul_cpow_half_mul_ofReal {z : ℂ} (hz : z ≠ 0) {t : ℝ} (ht : 0 < t) :
    (2 * (z * t) ^ (1 / 2 : ℂ)).re = 2 * Real.sqrt t * (z ^ (1 / 2 : ℂ)).re := by
  rw [two_mul_cpow_half_mul_ofReal hz ht, show (2 : ℂ) * (Real.sqrt t : ℂ) =
    ((2 * Real.sqrt t : ℝ) : ℂ) by push_cast; ring, re_ofReal_mul]

/-- `2 (z t)^{1/2}` lies in the right half-plane. -/
theorem two_mul_cpow_half_mem_slitPlane {z : ℂ} (hz : z ∈ slitPlane) {t : ℝ} (ht : 0 < t) :
    2 * (z * t) ^ (1 / 2 : ℂ) ∈ slitPlane := by
  refine Or.inl ?_
  rw [re_two_mul_cpow_half_mul_ofReal (slitPlane_ne_zero hz) ht]
  have := re_cpow_half_pos_of_mem_slitPlane hz
  have := Real.sqrt_pos.mpr ht
  positivity

/-- Holomorphy in `z` of the Bessel-`K` integral of DLMF 13.4.7 on the slit plane. -/
theorem differentiableOn_integral_besselK {a b : ℂ} (ha : (b - 1).re < a.re) (ha0 : 0 < a.re) :
    DifferentiableOn ℂ (fun z : ℂ => ∫ t : ℝ in Ioi 0, exp (-(t : ℂ)) *
      (t : ℂ) ^ (a - b / 2 - 1 / 2) * besselK (b - 1) (2 * (z * t) ^ (1 / 2 : ℂ))) slitPlane := by
  set σ := |(b - 1).re|
  set D := a.re - b.re / 2 + 1 / 2 - σ / 2
  have hD : 0 < D := by
    simp only [D, σ]
    simp only [sub_re, one_re] at ha ⊢
    rcases le_total 0 (b.re - 1) with h | h
    · rw [abs_of_nonneg h]; linarith
    · rw [abs_of_nonpos h]; linarith
  set s := σ + D
  have hs : 0 < s := by positivity
  have hσs : |(b - 1).re| ≤ s := by simp only [s, σ]; linarith
  refine Complex.differentiableOn_integral_Ioi_of_locally_dominated isOpen_slitPlane 0
    (fun z hz => ?_) ?_ (fun z₀ hz₀ => ?_)
  · refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
    have ht0 : (0 : ℝ) < t := ht
    refine ContinuousAt.continuousWithinAt ?_
    have hts : (t : ℂ) ∈ slitPlane := by simpa using ht0
    have hzt : z * t ∈ slitPlane := mul_ofReal_mem_slitPlane hz ht0
    have hw := two_mul_cpow_half_mem_slitPlane hz ht0
    have hc : ContinuousAt (fun s : ℝ => (s : ℂ)) t := continuous_ofReal.continuousAt
    have hK : ContinuousAt (besselK (b - 1)) (2 * (z * t) ^ (1 / 2 : ℂ)) :=
      (differentiableOn_besselK_slitPlane (b - 1)).continuousOn.continuousAt (isOpen_slitPlane.mem_nhds hw)
    have hin : ContinuousAt (fun s : ℝ => 2 * (z * s) ^ (1 / 2 : ℂ)) t :=
      continuousAt_const.mul ((continuousAt_const.mul hc).cpow continuousAt_const hzt)
    exact ((hc.neg.cexp).mul (hc.cpow continuousAt_const hts)).mul
      (hK.comp (f := fun s : ℝ => 2 * (z * s) ^ (1 / 2 : ℂ)) hin)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0 : ℝ) < t := ht
    intro z hz
    have hzt : z * t ∈ slitPlane := mul_ofReal_mem_slitPlane hz ht0
    have hw := two_mul_cpow_half_mem_slitPlane hz ht0
    have hK := (hasDerivAt_besselK (b - 1) hw).differentiableAt
    have hin : DifferentiableAt ℂ (fun z : ℂ => 2 * (z * t) ^ (1 / 2 : ℂ)) z :=
      ((differentiableAt_id.mul_const (t : ℂ)).cpow_const hzt).const_mul 2
    exact ((hK.comp z hin).const_mul _).differentiableWithinAt
  · set c := (z₀ ^ (1 / 2 : ℂ)).re / 2
    have hc0 : 0 < c := half_pos (re_cpow_half_pos_of_mem_slitPlane hz₀)
    have hcont : ContinuousAt (fun z : ℂ => (z ^ (1 / 2 : ℂ)).re) z₀ :=
      continuous_re.continuousAt.comp (continuousAt_id.cpow continuousAt_const hz₀)
    have hV : {z : ℂ | c < (z ^ (1 / 2 : ℂ)).re} ∩ slitPlane ∈ 𝓝 z₀ :=
      Filter.inter_mem (hcont.eventually (lt_mem_nhds (half_lt_self
        (re_cpow_half_pos_of_mem_slitPlane hz₀)))) (isOpen_slitPlane.mem_nhds hz₀)
    refine ⟨_, hV, fun t => Real.Gamma s * c ^ (-s) * (Real.exp (-t) * t ^ (D / 2 - 1)),
      (Real.GammaIntegral_convergent (half_pos hD)).const_mul _, ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht z hz
    have ht0 : (0 : ℝ) < t := ht
    have hzs : z ∈ slitPlane := hz.2
    have hzc : c < (z ^ (1 / 2 : ℂ)).re := hz.1
    have hz0 := slitPlane_ne_zero hzs
    have hsq := Real.sqrt_pos.mpr ht0
    have hre := re_two_mul_cpow_half_mul_ofReal hz0 ht0
    have hrepos : 0 < (2 * (z * t) ^ (1 / 2 : ℂ)).re := by rw [hre]; nlinarith
    have hKb := norm_besselK_le hrepos hs hσs
    have hge : Real.sqrt t * c ≤ (2 * (z * t) ^ (1 / 2 : ℂ)).re / 2 := by
      rw [hre]; nlinarith
    have hpow : ((2 * (z * t) ^ (1 / 2 : ℂ)).re / 2) ^ (-s) ≤ (Real.sqrt t * c) ^ (-s) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hge (by linarith)
    have hsplit : (Real.sqrt t * c) ^ (-s) = t ^ (-s / 2) * c ^ (-s) := by
      rw [Real.mul_rpow hsq.le hc0.le, Real.sqrt_eq_rpow, ← Real.rpow_mul ht0.le]
      ring_nf
    rw [norm_mul, norm_mul, Complex.norm_exp, norm_cpow_eq_rpow_re_of_pos ht0]
    have hα : (a - b / 2 - 1 / 2).re = a.re - b.re / 2 - 1 / 2 := by simp
    rw [hα]
    simp only [neg_re, ofReal_re]
    have htp : t ^ (a.re - b.re / 2 - 1 / 2) * t ^ (-s / 2) = t ^ (D / 2 - 1) := by
      rw [← Real.rpow_add ht0]
      congr 1
      simp only [s, D]
      ring
    have hG : 0 ≤ Real.Gamma s := (Real.Gamma_pos_of_pos hs).le
    calc Real.exp (-t) * t ^ (a.re - b.re / 2 - 1 / 2) * ‖besselK (b - 1) (2 * (z * t) ^ (1 / 2 : ℂ))‖
        ≤ Real.exp (-t) * t ^ (a.re - b.re / 2 - 1 / 2) *
            (Real.Gamma s * (t ^ (-s / 2) * c ^ (-s))) := by
          gcongr
          exact hKb.trans (mul_le_mul_of_nonneg_left (hpow.trans hsplit.le) hG)
      _ = Real.Gamma s * c ^ (-s) * (Real.exp (-t) *
            (t ^ (a.re - b.re / 2 - 1 / 2) * t ^ (-s / 2))) := by ring
      _ = _ := by rw [htp]

/-- **A Bessel-`K` integral for Tricomi's `U`** (DLMF 13.4.7) on the whole slit plane
(stronger than DLMF, which states `|ph z| < π/2`):
`U(a,b,z) = 2 z^{(1-b)/2} / (Γ(a) Γ(a-b+1)) ∫₀^∞ e^{-t} t^{a-b/2-1/2} K_{b-1}(2√(zt)) dt`. -/
theorem kummerU_eq_integral_besselK {a b z : ℂ} (hz : z ∈ slitPlane)
    (ha : (b - 1).re < a.re) (ha0 : 0 < a.re) :
    kummerU a b z =
      2 * z ^ ((1 - b) / 2) / (Gamma a * Gamma (a - b + 1)) *
        ∫ t : ℝ in Ioi 0,
          exp (-(t : ℂ)) * (t : ℂ) ^ (a - b / 2 - 1 / 2) *
            besselK (b - 1) (2 * (z * t) ^ (1 / 2 : ℂ)) := by
  have hf : AnalyticOnNhd ℂ (kummerU a b) slitPlane :=
    (differentiableOn_kummerU a b).analyticOnNhd isOpen_slitPlane
  have hg : AnalyticOnNhd ℂ (fun z : ℂ => 2 * z ^ ((1 - b) / 2) / (Gamma a * Gamma (a - b + 1)) *
      ∫ t : ℝ in Ioi 0, exp (-(t : ℂ)) * (t : ℂ) ^ (a - b / 2 - 1 / 2) *
        besselK (b - 1) (2 * (z * t) ^ (1 / 2 : ℂ))) slitPlane := by
    refine DifferentiableOn.analyticOnNhd ?_ isOpen_slitPlane
    refine DifferentiableOn.mul ?_ (differentiableOn_integral_besselK ha ha0)
    refine DifferentiableOn.div_const (DifferentiableOn.const_mul (fun w hw => ?_) _) _
    exact (differentiableAt_id.cpow_const hw).differentiableWithinAt
  have hfreq : ∃ᶠ w in 𝓝[≠] (1 : ℂ), kummerU a b w =
      2 * w ^ ((1 - b) / 2) / (Gamma a * Gamma (a - b + 1)) *
        ∫ t : ℝ in Ioi 0, exp (-(t : ℂ)) * (t : ℂ) ^ (a - b / 2 - 1 / 2) *
          besselK (b - 1) (2 * (w * t) ^ (1 / 2 : ℂ)) := by
    have ht : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[≠] 1) (𝓝[≠] (1 : ℂ)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · exact ((continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds).trans (by simp)
      · filter_upwards [self_mem_nhdsWithin] with r hr
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, ofReal_eq_one] using hr
    apply ht.frequently
    apply Eventually.frequently
    filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds (zero_lt_one' ℝ))] with r hr
    exact kummerU_eq_integral_besselK_ofReal hr ha ha0
  exact hf.eqOn_of_preconnected_of_frequently_eq hg
    (starConvex_one_slitPlane.isPathConnected one_mem_slitPlane).isConnected.isPreconnected
    one_mem_slitPlane hfreq hz

end BesselKIntegral

/-- A Bessel-K integral for Tricomi U, away from `z = 0` where the totalized values of both
sides differ. -/
@[dlmf 13.4.E7]
theorem kummerU_integral_besselK {a b z : ℂ} (hz : 0 ≤ z.re) (hz0 : z ≠ 0)
    (ha : (b - 1).re < a.re) (ha0 : 0 < a.re) :
    kummerU a b z =
      2 * z ^ ((1 - b) / 2) / (Gamma a * Gamma (a - b + 1)) *
        ∫ t : ℝ in Set.Ioi 0,
          exp (-(t : ℂ)) * (t : ℂ) ^ (a - b / 2 - 1 / 2) *
            besselK (b - 1) (2 * (z * t) ^ (1 / 2 : ℂ)) := by
  refine kummerU_eq_integral_besselK ?_ ha ha0
  rw [mem_slitPlane_iff]
  rcases hz.lt_or_eq with h | h
  · exact Or.inl h
  · refine Or.inr fun him => hz0 (Complex.ext ?_ ?_) <;> simp [← h, him]

open Set MeasureTheory DLMF.Gamma in
/-- The Cahen–Mellin integral in Barnes's orientation: `e^{-v} = 1/(2π) ∫ Γ(-(σ+iy)) v^{σ+iy} dy`
for `σ < 0 < v`. -/
theorem exp_neg_eq_integral_barnes {σ : ℝ} (hσ : σ < 0) {v : ℝ} (hv : 0 < v) :
    exp (-(v : ℂ)) =
      1 / (2 * π) * ∫ y : ℝ, Gamma (-((σ : ℂ) + I * y)) * (v : ℂ) ^ ((σ : ℂ) + I * y) := by
  have h := exp_neg_eq_integral (σ := -σ) (by linarith) hv
  rw [ofReal_exp, ofReal_neg] at h
  rw [h, ← integral_neg_eq_self]
  congr 2; funext y
  rw [show (((-σ : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I) = -((σ : ℂ) + I * y) by push_cast; ring, neg_neg]

open Set MeasureTheory DLMF.Gamma in
/-- For `σ < 0`, `y ↦ Γ(-(σ + iy))` is integrable on the real line. -/
theorem integrable_Gamma_neg_vertical {σ : ℝ} (hσ : σ < 0) :
    Integrable (fun y : ℝ => Gamma (-((σ : ℂ) + I * y))) := by
  refine (integrable_Gamma_vertical (σ := -σ) (by linarith)).comp_neg.congr
    (Eventually.of_forall fun y => ?_)
  simp only [Function.comp_apply]
  rw [show (((-σ : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I) = -((σ : ℂ) + I * y) by push_cast; ring]

open Set MeasureTheory DLMF.Gamma in
/-- Barnes's integral for `𝐌` (DLMF 13.4.16) when `re (b - a) > 0`, from Kummer's integral. -/
theorem regularized_barnes_integral_of_re_sub_pos {a b : ℂ} {x σ : ℝ}
    (hx : 0 < x) (ha : 0 < a.re + σ) (hσ : σ < 0) (hba : 0 < (b - a).re) :
    regularizedHGFun {a} {b} (-(x : ℂ)) =
      1 / (2 * π * Gamma a) * ∫ y : ℝ, Gamma (a + σ + I * y) * Gamma (-((σ : ℂ) + I * y)) /
        Gamma (b + σ + I * y) * (x : ℂ) ^ ((σ : ℂ) + I * y) := by
  have ha0 : 0 < a.re := by linarith
  have hb0 : 0 < b.re := by simp only [sub_re] at hba; linarith
  set Ψ : ℝ → ℂ := fun y => Gamma (-((σ : ℂ) + I * y)) with hΨ
  have hΨi : Integrable Ψ := integrable_Gamma_neg_vertical hσ
  have hΨc : Continuous Ψ := continuous_iff_continuousAt.mpr fun y =>
    (continuousAt_Gamma_of_re_pos (by simp; linarith)).comp (by fun_prop)
  set H : ℝ → ℝ → ℂ := fun t y => (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - a - 1) *
    (Ψ y * (x : ℂ) ^ ((σ : ℂ) + I * y) * (t : ℂ) ^ ((σ : ℂ) + I * y)) with hH
  have hGa : Gamma a ≠ 0 := Complex.Gamma_ne_zero_of_re_pos ha0
  have hGba : Gamma (b - a) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hba
  have hpt : ∀ t ∈ Ioo (0 : ℝ) 1,
      exp (-(x : ℂ) * t) * (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - a - 1) =
        1 / (2 * π) * ∫ y : ℝ, H t y := by
    intro t ht
    have hxt : 0 < x * t := mul_pos hx ht.1
    have hCM := exp_neg_eq_integral_barnes hσ hxt
    have hH' : ∫ y : ℝ, H t y = (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - a - 1) *
        ∫ y : ℝ, Ψ y * ((x * t : ℝ) : ℂ) ^ ((σ : ℂ) + I * y) := by
      rw [← MeasureTheory.integral_const_mul]
      congr 1; funext y
      rw [hH, ofReal_mul, mul_cpow_ofReal_nonneg hx.le ht.1.le]; ring
    rw [hH', show -(x : ℂ) * t = -((x * t : ℝ) : ℂ) by push_cast; ring, hCM]
    ring
  set μ : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1) with hμ
  have hμprod :
      μ.prod volume = (volume.prod volume).restrict (Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) := by
    rw [hμ, ← Measure.prod_restrict, Measure.restrict_univ]
  have hf : Integrable (fun t : ℝ => ‖(t : ℂ) ^ (a + σ - 1) * (1 - (t : ℂ)) ^ (b - a - 1)‖) μ := by
    have h := betaIntegral_convergent (u := a + σ) (v := b - a) (by simp; linarith) hba
    have h' := (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp h
    exact (h'.mono_set Ioo_subset_Ioc_self).norm
  have hg : Integrable (fun y : ℝ => ‖Ψ y‖ * x ^ σ) := hΨi.norm.mul_const _
  have hcont : ContinuousOn (Function.uncurry H) (Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) := by
    rintro ⟨t, y⟩ ⟨ht, -⟩
    have ht0 : (0 : ℝ) < t := ht.1
    have ht1 : t < 1 := ht.2
    refine ContinuousAt.continuousWithinAt ?_
    simp only [hH, Function.uncurry_def]
    refine ContinuousAt.mul (ContinuousAt.mul ?_ ?_) (ContinuousAt.mul (ContinuousAt.mul ?_ ?_) ?_)
    · exact ContinuousAt.cpow (by fun_prop) continuousAt_const (ofReal_mem_slitPlane.mpr ht0)
    · refine ContinuousAt.cpow (by fun_prop) continuousAt_const ?_
      rw [mem_slitPlane_iff]; left; simp; linarith
    · exact (hΨc.comp continuous_snd).continuousAt
    · exact ContinuousAt.cpow continuousAt_const (by fun_prop) (ofReal_mem_slitPlane.mpr hx)
    · exact ContinuousAt.cpow (by fun_prop) (by fun_prop) (ofReal_mem_slitPlane.mpr ht0)
  have hHi : Integrable (Function.uncurry H) (μ.prod volume) := by
    refine (hf.mul_prod hg).mono' ?_ ?_
    · rw [hμprod]
      exact hcont.aestronglyMeasurable (measurableSet_Ioo.prod MeasurableSet.univ)
    · rw [hμprod]
      refine (ae_restrict_iff' (measurableSet_Ioo.prod MeasurableSet.univ)).mpr
        (Eventually.of_forall ?_)
      rintro ⟨t, y⟩ ⟨ht, -⟩
      have ht0 : (0 : ℝ) < t := ht.1
      simp only [hH, Function.uncurry_def, norm_mul]
      rw [norm_cpow_eq_rpow_re_of_pos ht0, norm_cpow_eq_rpow_re_of_pos ht0,
        norm_cpow_eq_rpow_re_of_pos hx, norm_cpow_eq_rpow_re_of_pos ht0]
      simp only [sub_re, add_re, ofReal_re, one_re, mul_re, I_re, I_im, ofReal_im, zero_mul,
        sub_zero, mul_zero, add_zero]
      rw [show a.re + σ - 1 = (a.re - 1) + σ by ring, Real.rpow_add ht0]
      apply le_of_eq; ring
  have hswap := integral_integral_swap hHi
  have hinner : ∀ y : ℝ, ∫ t, H t y ∂μ = Ψ y * (x : ℂ) ^ ((σ : ℂ) + I * y) *
      (Gamma (a + σ + I * y) * Gamma (b - a) / Gamma (b + σ + I * y)) := by
    intro y
    have has : 0 < (a + σ + I * y).re := by
      simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, zero_mul, mul_zero, sub_zero,
        add_zero]; linarith
    have hB := Complex.Gamma_mul_Gamma_eq_betaIntegral has hba
    rw [show a + σ + I * y + (b - a) = b + σ + I * y by ring] at hB
    have hGbs : Gamma (b + σ + I * y) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by
      simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, zero_mul, mul_zero, sub_zero,
        add_zero]; linarith [sub_re b a])
    have hbeta : betaIntegral (a + σ + I * y) (b - a) =
        ∫ t, (t : ℂ) ^ (a + σ + I * y - 1) * (1 - (t : ℂ)) ^ (b - a - 1) ∂μ := by
      rw [betaIntegral, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
    calc ∫ t, H t y ∂μ = Ψ y * (x : ℂ) ^ ((σ : ℂ) + I * y) *
          ∫ t, (t : ℂ) ^ (a + σ + I * y - 1) * (1 - (t : ℂ)) ^ (b - a - 1) ∂μ := by
          rw [← MeasureTheory.integral_const_mul]
          refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
          have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.1.ne'
          have hsplit : (t : ℂ) ^ (a + σ + I * y - 1) =
              (t : ℂ) ^ (a - 1) * (t : ℂ) ^ ((σ : ℂ) + I * y) := by
            rw [← cpow_add _ _ ht0]; ring_nf
          simp only [hH]
          rw [hsplit]
          ring
      _ = _ := by
          rw [← hbeta]
          congr 1
          rw [eq_div_iff hGbs, hB]; ring
  rw [regularized_euler_integral ha0 hba, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo, setIntegral_congr_fun measurableSet_Ioo hpt,
    MeasureTheory.integral_const_mul]
  change 1 / (Gamma a * Gamma (b - a)) * (1 / (2 * π) * ∫ t, ∫ y, H t y ∂volume ∂μ) = _
  rw [hswap, integral_congr_ae (ae_of_all _ hinner)]
  have hlast : ∫ y : ℝ, Ψ y * (x : ℂ) ^ ((σ : ℂ) + I * y) *
      (Gamma (a + σ + I * y) * Gamma (b - a) / Gamma (b + σ + I * y)) =
      Gamma (b - a) * ∫ y : ℝ, Gamma (a + σ + I * y) * Gamma (-((σ : ℂ) + I * y)) /
        Gamma (b + σ + I * y) * (x : ℂ) ^ ((σ : ℂ) + I * y) := by
    rw [← MeasureTheory.integral_const_mul]
    congr 1; funext y; rw [hΨ]; ring
  rw [hlast]
  generalize (∫ y : ℝ, Gamma (a + σ + I * y) * Gamma (-((σ : ℂ) + I * y)) /
    Gamma (b + σ + I * y) * (x : ℂ) ^ ((σ : ℂ) + I * y)) = J
  field_simp

/-- Vertical Mellin–Barnes line; the factor `i` from `dt` is included. -/
@[dlmf 13.4.E16]
theorem regularized_barnes_integral {a b : ℂ} {x σ : ℝ}
    (hx : 0 < x) (ha : 0 < a.re + σ) (hσ : σ < 0) :
    regularizedHGFun {a} {b} (-(x : ℂ)) =
      1 / (2 * π * I * Gamma a) *
        ∫ t : ℝ, Gamma (a + σ + I * t) * Gamma (-(σ + I * t)) /
          Gamma (b + σ + I * t) * (x : ℂ) ^ (σ + I * t) * I := by
  set A : ℝ → ℂ := fun y => Gamma (a + σ + I * y) * Gamma (-((σ : ℂ) + I * y)) *
    (x : ℂ) ^ ((σ : ℂ) + I * y) with hA
  have hAc : Continuous A := by
    refine continuous_iff_continuousAt.mpr fun y => ?_
    refine ContinuousAt.mul (ContinuousAt.mul ?_ ?_) ?_
    · exact (DLMF.Gamma.continuousAt_Gamma_of_re_pos (by simp; linarith)).comp (by fun_prop)
    · exact (DLMF.Gamma.continuousAt_Gamma_of_re_pos (by simp; linarith)).comp (by fun_prop)
    · exact ContinuousAt.cpow continuousAt_const (by fun_prop) (ofReal_mem_slitPlane.mpr hx)
  obtain ⟨Ca, Ka, hCa⟩ := DLMF.Gamma.exists_norm_Gamma_shift_le (x := a.re + σ) ha a.im
  obtain ⟨Cs, Ks, hCs⟩ := DLMF.Gamma.exists_norm_Gamma_shift_le (x := -σ) (by linarith) 0
  have hCa0 : 0 ≤ Ca := (norm_nonneg _).trans (by simpa using hCa 0)
  have hCs0 : 0 ≤ Cs := (norm_nonneg _).trans (by simpa using hCs 0)
  have hAb : ∀ y : ℝ, ‖A y‖ ≤ Ca * Cs * x ^ σ * (1 + |y|) ^ (Ka + Ks) *
      Real.exp (-(π * |y|)) := by
    intro y
    have e1 : a + σ + I * y = ((a.re + σ : ℝ) : ℂ) + I * ((a.im : ℂ) + (y : ℂ)) := by
      apply Complex.ext <;> simp
    have e3 : -((σ : ℂ) + I * y) = ((-σ : ℝ) : ℂ) + I * (((0 : ℝ) : ℂ) + ((-y : ℝ) : ℂ)) := by
      push_cast; ring
    have h1 := hCa y; rw [← e1] at h1
    have h3 := hCs (-y); rw [← e3, abs_neg] at h3
    have h4 : ‖(x : ℂ) ^ ((σ : ℂ) + I * y)‖ = x ^ σ := by
      rw [norm_cpow_eq_rpow_re_of_pos hx]; simp
    simp only [hA, norm_mul]
    rw [h4]
    have hE : Real.exp (-(π * |y|) / 2) * Real.exp (-(π * |y|) / 2) = Real.exp (-(π * |y|)) := by
      rw [← Real.exp_add]; ring_nf
    calc ‖Gamma (a + σ + I * y)‖ * ‖Gamma (-((σ : ℂ) + I * y))‖ * x ^ σ
        ≤ (Ca * (1 + |y|) ^ Ka * Real.exp (-(π * |y|) / 2)) *
            (Cs * (1 + |y|) ^ Ks * Real.exp (-(π * |y|) / 2)) * x ^ σ := by gcongr
      _ = _ := by rw [pow_add, ← hE]; ring
  have hR := DLMF.Gamma.differentiable_integral_mul_recip_Gamma hAc hAb σ
  have hrw : ∀ b : ℂ, ∫ y : ℝ, Gamma (a + σ + I * y) * Gamma (-((σ : ℂ) + I * y)) /
      Gamma (b + σ + I * y) * (x : ℂ) ^ ((σ : ℂ) + I * y) =
      ∫ y : ℝ, A y * (Gamma (b + σ + I * y))⁻¹ := fun b => by
    congr 1; funext y; simp only [hA]; ring
  have key := DLMF.Hypergeometric.eq_of_analyticOnNhd_univ_of_eqOn
    (analyticOnNhd_regularizedConfluent_b a (-(x : ℂ)))
    (g := fun b => 1 / (2 * π * Gamma a) * ∫ y : ℝ, A y * (Gamma (b + σ + I * y))⁻¹)
    (fun b _ => (hR.const_mul _).analyticAt b)
    (U := {b : ℂ | 0 < (b - a).re})
    (isOpen_lt continuous_const (continuous_re.comp (continuous_id.sub continuous_const)))
    ⟨a + 1, by simp⟩
    (fun b hb => by
      simp only
      rw [regularized_barnes_integral_of_re_sub_pos hx ha hσ hb, hrw])
  have hb := congrFun key b
  rw [hb, ← hrw]
  have hrw2 : ∫ t : ℝ, Gamma (a + σ + I * t) * Gamma (-(σ + I * t)) /
      Gamma (b + σ + I * t) * (x : ℂ) ^ (σ + I * t) * I =
      I * ∫ y : ℝ, Gamma (a + σ + I * y) * Gamma (-((σ : ℂ) + I * y)) /
        Gamma (b + σ + I * y) * (x : ℂ) ^ ((σ : ℂ) + I * y) := by
    rw [← MeasureTheory.integral_const_mul]; congr 1; funext y; ring
  rw [hrw2]
  generalize (∫ y : ℝ, Gamma (a + σ + I * y) * Gamma (-((σ : ℂ) + I * y)) /
    Gamma (b + σ + I * y) * (x : ℂ) ^ ((σ : ℂ) + I * y)) = J
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  field_simp

open Set MeasureTheory in
/-- Barnes's integral for `₁F₁`, AAR Theorem 4.2.1, along the upward vertical
line `s = σ + it`, with `-Re a < σ < 0`. -/
theorem kummerM_eq_barnes_integral {a c z : ℂ} {σ : ℝ}
    (haσ : -a.re < σ) (hσ : σ < 0) (hc : ∀ k : ℕ, c ≠ -k)
    (hz : z ≠ 0) (harg : |(-z).arg| < π / 2) :
    kummerM a c z =
      Gamma c / (2 * π * I * Gamma a) *
        ∫ t : ℝ, Gamma (-(σ + I * t)) * Gamma (a + σ + I * t) /
          Gamma (c + σ + I * t) * (-z) ^ (σ + I * t) * I := by
  set B : ℝ → ℂ := fun t => Gamma (-((σ : ℂ) + I * t)) * Gamma (a + σ + I * t) /
    Gamma (c + σ + I * t) with hBdef
  have ha : 0 < a.re + σ := by linarith
  have hBc : Continuous B := by
    refine continuous_iff_continuousAt.mpr fun y => ?_
    refine ContinuousAt.mul (ContinuousAt.mul ?_ ?_) ?_
    · exact (DLMF.Gamma.continuousAt_Gamma_of_re_pos (by simp; linarith)).comp (by fun_prop)
    · exact (DLMF.Gamma.continuousAt_Gamma_of_re_pos (by simp; linarith)).comp (by fun_prop)
    · exact (DLMF.Gamma.differentiable_recip_Gamma.continuous.comp (by fun_prop)).continuousAt
  -- the decay of `B`
  obtain ⟨Cs, Ks, hCs⟩ := DLMF.Gamma.exists_norm_Gamma_shift_le (x := -σ) (by linarith) 0
  obtain ⟨Ca, Ka, hCa⟩ := DLMF.Gamma.exists_norm_Gamma_shift_le (x := a.re + σ) ha a.im
  obtain ⟨Cc, Kc, hCc⟩ := DLMF.Gamma.exists_norm_recip_Gamma_shift_le (c.re + σ) c.im
  have hCs0 : 0 ≤ Cs := (norm_nonneg _).trans (by simpa using hCs 0)
  have hCa0 : 0 ≤ Ca := (norm_nonneg _).trans (by simpa using hCa 0)
  have hBb : ∀ y : ℝ, ‖B y‖ ≤ Cs * Ca * Cc * (1 + |y|) ^ (Ks + Ka + Kc) *
      Real.exp (-(π * |y|) / 2) := by
    intro y
    have e1 : -((σ : ℂ) + I * y) = ((-σ : ℝ) : ℂ) + I * (((0 : ℝ) : ℂ) + ((-y : ℝ) : ℂ)) := by
      push_cast; ring
    have e2 : a + σ + I * y = ((a.re + σ : ℝ) : ℂ) + I * ((a.im : ℂ) + (y : ℂ)) := by
      apply Complex.ext <;> simp
    have e3 : c + σ + I * y = ((c.re + σ : ℝ) : ℂ) + I * ((c.im : ℂ) + (y : ℂ)) := by
      apply Complex.ext <;> simp
    have h1 := hCs (-y); rw [← e1, abs_neg] at h1
    have h2 := hCa y; rw [← e2] at h2
    have h3 := hCc y; rw [← e3] at h3
    simp only [hBdef]
    rw [div_eq_mul_inv, norm_mul, norm_mul]
    have hE : Real.exp (-(π * |y|) / 2) * Real.exp (-(π * |y|) / 2) * Real.exp (π * |y| / 2) =
        Real.exp (-(π * |y|) / 2) := by
      rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    calc ‖Gamma (-((σ : ℂ) + I * y))‖ * ‖Gamma (a + σ + I * y)‖ * ‖(Gamma (c + σ + I * y))⁻¹‖
        ≤ (Cs * (1 + |y|) ^ Ks * Real.exp (-(π * |y|) / 2)) *
            (Ca * (1 + |y|) ^ Ka * Real.exp (-(π * |y|) / 2)) *
            (Cc * (1 + |y|) ^ Kc * Real.exp (π * |y| / 2)) := by gcongr
      _ = _ := by
          rw [pow_add, pow_add]
          generalize Real.exp (-(π * |y|) / 2) = E at hE ⊢
          generalize Real.exp (π * |y| / 2) = F at hE ⊢
          linear_combination (Cs * Ca * Cc * (1 + |y|) ^ Ks * (1 + |y|) ^ Ka * (1 + |y|) ^ Kc) * hE
  have hG := DLMF.Gamma.differentiableOn_integral_mul_cpow hBc hBb σ
  -- both sides are analytic on the left half-plane
  set Ω : Set ℂ := {z : ℂ | z.re < 0} with hΩ
  have hΩo : IsOpen Ω := isOpen_lt continuous_re continuous_const
  have hzΩ : z ∈ Ω := by
    have := abs_arg_lt_pi_div_two_iff.mp harg
    rcases this with h | h
    · simpa [hΩ] using h
    · exact absurd (neg_eq_zero.mp h) hz
  set g : ℂ → ℂ := fun z => Gamma c / (2 * π * I * Gamma a) *
    (I * ∫ t : ℝ, B t * (-z) ^ ((σ : ℂ) + I * t)) with hg
  have hgd : DifferentiableOn ℂ g Ω := by
    refine (DifferentiableOn.const_mul (DifferentiableOn.const_mul ?_ _) _)
    exact hG.comp (differentiableOn_neg _) (fun w hw => by simpa [hΩ] using hw)
  have hga : AnalyticOnNhd ℂ g Ω := hgd.analyticOnNhd hΩo
  have hfa : AnalyticOnNhd ℂ (kummerM a c) Ω := fun w _ => analyticOnNhd_kummerM hc w trivial
  -- agreement on the negative axis
  have hagree : ∀ x : ℝ, 0 < x → kummerM a c (-(x : ℂ)) = g (-(x : ℂ)) := by
    intro x hx
    rw [kummerM_eq_mul_regularizedHGFun hc, regularized_barnes_integral hx ha hσ]
    simp only [hg, neg_neg]
    have hrw : ∫ t : ℝ, Gamma (a + σ + I * t) * Gamma (-(σ + I * t)) /
        Gamma (c + σ + I * t) * (x : ℂ) ^ (σ + I * t) * I =
        I * ∫ t : ℝ, B t * (x : ℂ) ^ ((σ : ℂ) + I * t) := by
      rw [← MeasureTheory.integral_const_mul]; congr 1; funext t; simp only [hBdef]; ring
    rw [hrw]
    have hGa : Gamma a ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
    have hI : (I : ℂ) ≠ 0 := I_ne_zero
    field_simp
  have hfreq : ∃ᶠ w in 𝓝[≠] (-1 : ℂ), kummerM a c w = g w := by
    have ht : Tendsto (fun x : ℝ => -(x : ℂ)) (𝓝[≠] (1 : ℝ)) (𝓝[≠] (-1 : ℂ)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have h1 := (continuous_ofReal.tendsto (1 : ℝ)).neg
        rw [ofReal_one] at h1
        exact h1.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with x hx
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx ⊢
        intro h; apply hx; have := congrArg re h; simpa using this
    refine ht.frequently ?_
    have hpos : ∀ᶠ x in 𝓝[≠] (1 : ℝ), 0 < x :=
      (eventually_gt_nhds one_pos).filter_mono nhdsWithin_le_nhds
    exact (hpos.mono fun x hx => hagree x hx).frequently
  have hΩc : IsPreconnected Ω := (convex_halfSpace_re_lt (r := 0)).isPreconnected
  have heq := hfa.eqOn_of_preconnected_of_frequently_eq hga hΩc (by simp [hΩ]) hfreq hzΩ
  rw [heq]
  simp only [hg]
  congr 1
  rw [← MeasureTheory.integral_const_mul]; congr 1; funext t; simp only [hBdef]; push_cast; ring

open Set MeasureTheory in
@[dlmf 13.4.E17]
theorem kummerU_barnes {a b : ℂ} {x σ : ℝ}
    (hx : 0 < x) (ha : 0 < a.re + σ) (hab : 0 < (1 + a - b).re + σ) (hσ : σ < 0) :
    kummerU a b x =
      (x : ℂ) ^ (-a) / (2 * π * I) *
        ∫ t : ℝ, Gamma (a + σ + I * t) * Gamma (1 + a - b + σ + I * t) *
          Gamma (-(σ + I * t)) / (Gamma a * Gamma (1 + a - b)) *
          (x : ℂ) ^ (-(σ + I * t)) * I := by
  have ha0 : 0 < a.re := by linarith
  have hA0 : 0 < (1 + a - b).re := by linarith
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hGa : Gamma a ≠ 0 := Complex.Gamma_ne_zero_of_re_pos ha0
  have hGA : Gamma (1 + a - b) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hA0
  set Φ : ℝ → ℂ := fun y => Gamma (-((σ : ℂ) + I * y)) * Gamma (1 + a - b + σ + I * y) with hΦ
  have hΦi : Integrable Φ := DLMF.Hypergeometric.integrable_Gamma_neg_mul_Gamma hσ hab
  have hΦc : Continuous Φ := DLMF.Hypergeometric.continuous_Gamma_neg_mul_Gamma hσ hab
  set H : ℝ → ℝ → ℂ := fun t y => exp (-(x : ℂ) * t) * (t : ℂ) ^ (a - 1) *
    (Φ y * (t : ℂ) ^ ((σ : ℂ) + I * y)) with hH
  -- the Laplace integral, with the Mellin–Barnes integral inserted
  have hpt : ∀ t ∈ Ioi (0 : ℝ),
      exp (-(x : ℂ) * t) * (t : ℂ) ^ (a - 1) * (1 + (t : ℂ)) ^ (b - a - 1) =
        (Gamma (1 + a - b))⁻¹ * (1 / (2 * π)) * ∫ y : ℝ, H t y := by
    intro t ht
    have hMB := DLMF.Hypergeometric.Gamma_mul_one_add_cpow_neg_barnes (a := 1 + a - b) hσ hab ht
    have hpow : (1 + (t : ℂ)) ^ (b - a - 1) = (Gamma (1 + a - b))⁻¹ *
        (1 / (2 * π) * ∫ y : ℝ, Φ y * (t : ℂ) ^ ((σ : ℂ) + I * y)) := by
      rw [← hMB, show b - a - 1 = -(1 + a - b) by ring]; push_cast; field_simp
    have hHt : ∫ y : ℝ, H t y = exp (-(x : ℂ) * t) * (t : ℂ) ^ (a - 1) *
        ∫ y : ℝ, Φ y * (t : ℂ) ^ ((σ : ℂ) + I * y) := by
      rw [← MeasureTheory.integral_const_mul]
    rw [hpow, hHt]; ring
  -- integrability on the product
  set μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ)) with hμ
  have hμprod : μ.prod volume = (volume.prod volume).restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := by
    rw [hμ, ← Measure.prod_restrict, Measure.restrict_univ]
  have hf : Integrable (fun t : ℝ => ‖(t : ℂ) ^ (a + σ - 1) * exp (-((x : ℂ) * t))‖) μ := by
    have h := integral_cpow_mul_cexp_neg_mul_Ioi (s := a + σ) (z := x) (by simp; linarith)
      (by simpa using hx)
    have hi : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (a + σ - 1) * exp (-((x : ℂ) * t))) (Ioi 0) := by
      by_contra hni
      rw [integral_undef hni] at h
      exact (mul_ne_zero (Complex.Gamma_ne_zero_of_re_pos (by simp; linarith))
        (by rw [cpow_def_of_ne_zero hx0]; exact exp_ne_zero _)) h.symm
    exact hi.norm
  have hg : Integrable (fun y : ℝ => ‖Φ y‖) := hΦi.norm
  have hcont : ContinuousOn (Function.uncurry H) (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := by
    rintro ⟨t, y⟩ ⟨ht, -⟩
    have ht0 : (0 : ℝ) < t := ht
    refine ContinuousAt.continuousWithinAt ?_
    simp only [hH, Function.uncurry_def]
    refine ContinuousAt.mul (ContinuousAt.mul (by fun_prop) ?_) (ContinuousAt.mul ?_ ?_)
    · exact ContinuousAt.cpow (by fun_prop) continuousAt_const (ofReal_mem_slitPlane.mpr ht0)
    · exact (hΦc.comp continuous_snd).continuousAt
    · exact ContinuousAt.cpow (by fun_prop) (by fun_prop) (ofReal_mem_slitPlane.mpr ht0)
  have hHi : Integrable (Function.uncurry H) (μ.prod volume) := by
    refine (hf.mul_prod hg).mono' ?_ ?_
    · rw [hμprod]
      exact hcont.aestronglyMeasurable (measurableSet_Ioi.prod MeasurableSet.univ)
    · rw [hμprod]
      refine (ae_restrict_iff' (measurableSet_Ioi.prod MeasurableSet.univ)).mpr
        (Eventually.of_forall ?_)
      rintro ⟨t, y⟩ ⟨ht, -⟩
      have ht0 : (0 : ℝ) < t := ht
      simp only [hH, Function.uncurry_def, norm_mul]
      rw [norm_cpow_eq_rpow_re_of_pos ht0, norm_cpow_eq_rpow_re_of_pos ht0,
        norm_cpow_eq_rpow_re_of_pos ht0]
      simp only [sub_re, add_re, ofReal_re, one_re, mul_re, I_re, I_im, ofReal_im, zero_mul,
        sub_zero, mul_zero, add_zero, neg_mul]
      rw [show a.re + σ - 1 = (a.re - 1) + σ by ring, Real.rpow_add ht0]
      apply le_of_eq; ring
  have hswap := integral_integral_swap hHi
  -- the inner Gamma integrals
  have hinner : ∀ y : ℝ, ∫ t, H t y ∂μ = Φ y * (Gamma (a + σ + I * y) *
      (x : ℂ) ^ (-(a + σ + I * y))) := by
    intro y
    have h := integral_cpow_mul_cexp_neg_mul_Ioi (s := a + σ + I * y) (z := x)
      (by simp; linarith) (by simpa using hx)
    rw [← h, ← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht)
    have hsplit : (t : ℂ) ^ (a + σ + I * y - 1) =
        (t : ℂ) ^ (a - 1) * (t : ℂ) ^ ((σ : ℂ) + I * y) := by
      rw [← cpow_add _ _ ht0]; ring_nf
    simp only [hH]
    rw [hsplit, show -((x : ℂ) * t) = -(x : ℂ) * t by ring]
    ring
  -- assemble
  rw [kummerU_laplace ha0 (by simpa using hx), setIntegral_congr_fun measurableSet_Ioi hpt,
    MeasureTheory.integral_const_mul]
  change 1 / Gamma a * ((Gamma (1 + a - b))⁻¹ * (1 / (2 * π)) *
    ∫ t, ∫ y, H t y ∂volume ∂μ) = _
  rw [hswap, integral_congr_ae (ae_of_all _ hinner)]
  have hlast : ∫ y : ℝ, Φ y * (Gamma (a + σ + I * y) * (x : ℂ) ^ (-(a + σ + I * y))) =
      (x : ℂ) ^ (-a) * ∫ t : ℝ, Gamma (a + σ + I * t) * Gamma (1 + a - b + σ + I * t) *
        Gamma (-(σ + I * t)) * (x : ℂ) ^ (-(σ + I * t)) := by
    rw [← MeasureTheory.integral_const_mul]
    congr 1; funext y
    rw [hΦ, show -(a + σ + I * y) = -a + -(σ + I * y) by ring, cpow_add _ _ hx0]
    ring
  have hlast' : ∫ t : ℝ, Gamma (a + σ + I * t) * Gamma (1 + a - b + σ + I * t) *
      Gamma (-(σ + I * t)) / (Gamma a * Gamma (1 + a - b)) * (x : ℂ) ^ (-(σ + I * t)) * I =
      I / (Gamma a * Gamma (1 + a - b)) * ∫ t : ℝ, Gamma (a + σ + I * t) *
        Gamma (1 + a - b + σ + I * t) * Gamma (-(σ + I * t)) * (x : ℂ) ^ (-(σ + I * t)) := by
    rw [← MeasureTheory.integral_const_mul]
    congr 1; funext y; ring
  rw [hlast, hlast']
  generalize (∫ t : ℝ, Gamma (a + σ + I * t) * Gamma (1 + a - b + σ + I * t) *
    Gamma (-(σ + I * t)) * (x : ℂ) ^ (-(σ + I * t))) = J
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

open Set MeasureTheory in
/-- The exponential Barnes integrand of 13.4.18 is integrable for every first parameter. -/
theorem integrable_kummerU_barnes_exp_integrand {a b : ℂ} {x σ : ℝ} (hx : 0 < x)
    (hb : 0 < (b - 1).re + σ) (hσ : 0 < σ) :
    Integrable (fun t : ℝ => Gamma (b - 1 + σ + I * t) * Gamma (σ + I * t) /
      Gamma (a + σ + I * t) * (x : ℂ) ^ (-(σ + I * t)) * I) := by
  obtain ⟨C1, K1, h1⟩ := DLMF.Gamma.exists_norm_Gamma_shift_le hb (b - 1).im
  obtain ⟨C2, K2, h2⟩ := DLMF.Gamma.exists_norm_Gamma_shift_le hσ 0
  obtain ⟨C3, K3, h3⟩ := DLMF.Gamma.exists_norm_recip_Gamma_shift_le (a.re + σ) a.im
  have hcont : Continuous (fun t : ℝ => Gamma (b - 1 + σ + I * t) * Gamma (σ + I * t) /
      Gamma (a + σ + I * t) * (x : ℂ) ^ (-(σ + I * t)) * I) := by
    refine continuous_iff_continuousAt.mpr fun y => ?_
    refine ContinuousAt.mul (ContinuousAt.mul (ContinuousAt.mul (ContinuousAt.mul ?_ ?_) ?_) ?_)
      continuousAt_const
    · exact (DLMF.Gamma.continuousAt_Gamma_of_re_pos (by simp at hb ⊢; linarith)).comp (by fun_prop)
    · exact (DLMF.Gamma.continuousAt_Gamma_of_re_pos (by simp; linarith)).comp (by fun_prop)
    · exact (DLMF.Gamma.differentiable_recip_Gamma.continuous.comp (by fun_prop)).continuousAt
    · exact ContinuousAt.cpow continuousAt_const (by fun_prop) (ofReal_mem_slitPlane.mpr hx)
  refine ((DLMF.Gamma.integrable_one_add_abs_pow_mul_exp_neg (c := π / 2) (by positivity)
    (K1 + K2 + K3)).const_mul (C1 * C2 * C3 * x ^ (-σ))).mono' hcont.aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  have e1 : b - 1 + σ + I * y = (((b - 1).re + σ : ℝ) : ℂ) + I * (((b - 1).im : ℂ) + (y : ℂ)) := by
    apply Complex.ext <;> simp
  have e2 : (σ : ℂ) + I * y = ((σ : ℝ) : ℂ) + I * (((0 : ℝ) : ℂ) + (y : ℂ)) := by push_cast; ring
  have e3 : a + σ + I * y = ((a.re + σ : ℝ) : ℂ) + I * ((a.im : ℂ) + (y : ℂ)) := by
    apply Complex.ext <;> simp
  have b1 := h1 y; rw [← e1] at b1
  have b2 := h2 y; rw [← e2] at b2
  have b3 := h3 y; rw [← e3] at b3
  have h4 : ‖(x : ℂ) ^ (-((σ : ℂ) + I * y))‖ = x ^ (-σ) := by
    rw [norm_cpow_eq_rpow_re_of_pos hx]; simp
  rw [div_eq_mul_inv, norm_mul, norm_mul, norm_mul, norm_mul, h4, norm_I, mul_one]
  have hC1 : 0 ≤ C1 := (norm_nonneg _).trans (by simpa using h1 0)
  have hC2 : 0 ≤ C2 := (norm_nonneg _).trans (by simpa using h2 0)
  calc ‖Gamma (b - 1 + σ + I * y)‖ * ‖Gamma (σ + I * y)‖ * ‖(Gamma (a + σ + I * y))⁻¹‖ * x ^ (-σ)
      ≤ (C1 * (1 + |y|) ^ K1 * Real.exp (-(π * |y|) / 2)) *
          (C2 * (1 + |y|) ^ K2 * Real.exp (-(π * |y|) / 2)) *
          (C3 * (1 + |y|) ^ K3 * Real.exp (π * |y| / 2)) * x ^ (-σ) := by gcongr
    _ = _ := by
        rw [pow_add, pow_add]
        have hE : Real.exp (-(π * |y|) / 2) * Real.exp (-(π * |y|) / 2) * Real.exp (π * |y| / 2) =
            Real.exp (-(π / 2 * |y|)) := by
          rw [← Real.exp_add, ← Real.exp_add]; ring_nf
        rw [← hE]; ring

open Set MeasureTheory in
/-- 13.4.18 for `Re a > 0`: the Cahen–Mellin integral for `e^{-x(1+τ)}` inserted into
Tricomi's Laplace integral, and Euler's second Beta integral in `τ`. -/
theorem kummerU_barnes_exp_of_re_pos {a b : ℂ} {x σ : ℝ}
    (hx : 0 < x) (ha : 0 < a.re) (hb : 0 < (b - 1).re + σ) (hσ : 0 < σ) :
    kummerU a b x =
      (x : ℂ) ^ (1 - b) * exp x / (2 * π * I) *
        ∫ t : ℝ, Gamma (b - 1 + σ + I * t) * Gamma (σ + I * t) /
          Gamma (a + σ + I * t) * (x : ℂ) ^ (-(σ + I * t)) * I := by
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hGa : Gamma a ≠ 0 := Complex.Gamma_ne_zero_of_re_pos ha
  set Ψ : ℝ → ℂ := fun t => Gamma (b - 1 + σ + I * t) with hΨ
  have hΨi : Integrable Ψ := by
    have h := (DLMF.Gamma.integrable_Gamma_vertical hb).comp_add_right (b - 1).im
    refine h.congr (Eventually.of_forall fun t => ?_)
    simp only [hΨ]
    congr 1; apply Complex.ext <;> simp; ring
  have hΨc : Continuous Ψ := continuous_iff_continuousAt.mpr fun y =>
    (DLMF.Gamma.continuousAt_Gamma_of_re_pos (by simp at hb ⊢; linarith)).comp (by fun_prop)
  have hCM : ∀ u : ℝ, 0 < u →
      exp (-(u : ℂ)) = 1 / (2 * π) * ∫ t : ℝ, Ψ t * (u : ℂ) ^ (-(b - 1 + σ + I * t)) := by
    intro u hu
    have h := DLMF.Gamma.exp_neg_eq_integral hb hu
    rw [ofReal_exp, ofReal_neg] at h
    rw [h, ← integral_add_right_eq_self _ (b - 1).im]
    congr 2; funext t
    have e : ((((b - 1).re + σ : ℝ) : ℂ)) + ((t + (b - 1).im : ℝ) : ℂ) * I = b - 1 + σ + I * t := by
      apply Complex.ext <;> simp; ring
    rw [e]
  set H : ℝ → ℝ → ℂ := fun τ t => (τ : ℂ) ^ (a - 1) * ((1 + τ : ℝ) : ℂ) ^ (-a) *
    (Ψ t * (x : ℂ) ^ (-((σ : ℂ) + I * t)) * ((1 + τ : ℝ) : ℂ) ^ (-((σ : ℂ) + I * t))) with hH
  have hpt : ∀ τ ∈ Ioi (0 : ℝ),
      exp (-(x : ℂ) * τ) * (τ : ℂ) ^ (a - 1) * (1 + (τ : ℂ)) ^ (b - a - 1) =
        (x : ℂ) ^ (1 - b) * exp x * (1 / (2 * π) * ∫ t : ℝ, H τ t) := by
    intro τ hτ
    have hτ0 : (0 : ℝ) < τ := hτ
    have h1τ : (0 : ℝ) < 1 + τ := by linarith
    have h1τ0 : ((1 + τ : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr h1τ.ne'
    have hu : 0 < x * (1 + τ) := mul_pos hx h1τ
    have hu0 : ((x * (1 + τ) : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hu.ne'
    set J := ∫ t : ℝ, Ψ t * (x : ℂ) ^ (-((σ : ℂ) + I * t)) *
      ((1 + τ : ℝ) : ℂ) ^ (-((σ : ℂ) + I * t)) with hJ
    have F1 : ∫ t : ℝ, H τ t = (τ : ℂ) ^ (a - 1) * ((1 + τ : ℝ) : ℂ) ^ (-a) * J := by
      rw [hJ, ← MeasureTheory.integral_const_mul]
    have F2 : exp (-((x * (1 + τ) : ℝ) : ℂ)) =
        1 / (2 * π) * (((x * (1 + τ) : ℝ) : ℂ) ^ (-(b - 1)) * J) := by
      rw [hCM _ hu, hJ, ← MeasureTheory.integral_const_mul (((x * (1 + τ) : ℝ) : ℂ) ^ (-(b - 1)))]
      congr 1; congr 1; funext t
      rw [show -(b - 1 + σ + I * t) = -(b - 1) + -((σ : ℂ) + I * t) by ring, cpow_add _ _ hu0,
        ofReal_mul, mul_cpow_ofReal_nonneg hx.le h1τ.le, mul_cpow_ofReal_nonneg hx.le h1τ.le]
      ring
    have F3 : ((x * (1 + τ) : ℝ) : ℂ) ^ (-(b - 1)) =
        (x : ℂ) ^ (1 - b) * ((1 + τ : ℝ) : ℂ) ^ (-(b - 1)) := by
      rw [ofReal_mul, mul_cpow_ofReal_nonneg hx.le h1τ.le, show -(b - 1) = 1 - b by ring]
    have F4 : exp (-(x : ℂ) * τ) = exp x * exp (-((x * (1 + τ) : ℝ) : ℂ)) := by
      rw [← exp_add]; push_cast; ring_nf
    have F5 : ((1 + τ : ℝ) : ℂ) ^ (-(b - 1)) * ((1 + τ : ℝ) : ℂ) ^ (b - a - 1) =
        ((1 + τ : ℝ) : ℂ) ^ (-a) := by
      rw [← cpow_add _ _ h1τ0]; ring_nf
    have F6 : (1 + (τ : ℂ)) = ((1 + τ : ℝ) : ℂ) := by push_cast; ring
    rw [F1, F4, F2, F3, F6]
    linear_combination (exp x * (1 / (2 * π)) * (x : ℂ) ^ (1 - b) * J * (τ : ℂ) ^ (a - 1)) * F5
  set μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ)) with hμ
  have hμprod : μ.prod volume = (volume.prod volume).restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := by
    rw [hμ, ← Measure.prod_restrict, Measure.restrict_univ]
  have hf : Integrable (fun τ : ℝ => τ ^ (a.re - 1) * (1 + τ) ^ (-(a.re + σ))) μ :=
    TauCeti.integrableOn_rpow_mul_one_add_rpow ha hσ
  have hg : Integrable (fun t : ℝ => ‖Ψ t‖ * x ^ (-σ)) := hΨi.norm.mul_const _
  have hcont : ContinuousOn (Function.uncurry H) (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := by
    rintro ⟨τ, y⟩ ⟨hτ, -⟩
    have hτ0 : (0 : ℝ) < τ := hτ
    have h1 : ((1 + τ : ℝ) : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr (by linarith)
    refine ContinuousAt.continuousWithinAt ?_
    simp only [hH, Function.uncurry_def]
    refine ContinuousAt.mul (ContinuousAt.mul ?_ ?_) (ContinuousAt.mul (ContinuousAt.mul ?_ ?_) ?_)
    · exact ContinuousAt.cpow (by fun_prop) continuousAt_const (ofReal_mem_slitPlane.mpr hτ0)
    · exact ContinuousAt.cpow (by fun_prop) continuousAt_const h1
    · exact (hΨc.comp continuous_snd).continuousAt
    · exact ContinuousAt.cpow continuousAt_const (by fun_prop) (ofReal_mem_slitPlane.mpr hx)
    · exact ContinuousAt.cpow (by fun_prop) (by fun_prop) h1
  have hHi : Integrable (Function.uncurry H) (μ.prod volume) := by
    refine (hf.mul_prod hg).mono' ?_ ?_
    · rw [hμprod]
      exact hcont.aestronglyMeasurable (measurableSet_Ioi.prod MeasurableSet.univ)
    · rw [hμprod]
      refine (ae_restrict_iff' (measurableSet_Ioi.prod MeasurableSet.univ)).mpr
        (Eventually.of_forall ?_)
      rintro ⟨τ, y⟩ ⟨hτ, -⟩
      have hτ0 : (0 : ℝ) < τ := hτ
      have h1τ : (0 : ℝ) < 1 + τ := by linarith
      simp only [hH, Function.uncurry_def, norm_mul]
      rw [norm_cpow_eq_rpow_re_of_pos hτ0, norm_cpow_eq_rpow_re_of_pos h1τ,
        norm_cpow_eq_rpow_re_of_pos hx, norm_cpow_eq_rpow_re_of_pos h1τ]
      simp only [sub_re, neg_re, add_re, ofReal_re, one_re, mul_re, I_re, I_im, ofReal_im,
        zero_mul, sub_zero, mul_zero, add_zero]
      rw [show -(a.re + σ) = -a.re + -σ by ring, Real.rpow_add h1τ]
      apply le_of_eq; ring
  have hswap := integral_integral_swap hHi
  have hinner : ∀ y : ℝ, ∫ τ, H τ y ∂μ = Ψ y * (x : ℂ) ^ (-((σ : ℂ) + I * y)) *
      (Gamma a * Gamma (σ + I * y) / Gamma (a + (σ + I * y))) := by
    intro y
    have hm := DLMF.Gamma.mellin_one_add_cpow_neg (a := a + (σ + I * y)) (s := a) ha
      (by simp; linarith)
    rw [mellin, show a + (σ + I * y) - a = σ + I * y by ring] at hm
    rw [← hm, ← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun τ hτ => ?_
    have h1τ0 : ((1 + τ : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by linarith [mem_Ioi.mp hτ])
    simp only [hH, smul_eq_mul]
    rw [show -(a + ((σ : ℂ) + I * y)) = -a + -((σ : ℂ) + I * y) by ring, cpow_add _ _ h1τ0]
    ring
  rw [kummerU_laplace ha (by simpa using hx), setIntegral_congr_fun measurableSet_Ioi hpt,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  change 1 / Gamma a * ((x : ℂ) ^ (1 - b) * exp x * (1 / (2 * π) *
    ∫ τ, ∫ t, H τ t ∂volume ∂μ)) = _
  rw [hswap, integral_congr_ae (ae_of_all _ hinner)]
  have hlast : ∫ y : ℝ, Ψ y * (x : ℂ) ^ (-((σ : ℂ) + I * y)) *
      (Gamma a * Gamma (σ + I * y) / Gamma (a + (σ + I * y))) =
      Gamma a * ∫ t : ℝ, Gamma (b - 1 + σ + I * t) * Gamma (σ + I * t) /
        Gamma (a + σ + I * t) * (x : ℂ) ^ (-(σ + I * t)) := by
    rw [← MeasureTheory.integral_const_mul]
    congr 1; funext y
    rw [hΨ, show a + ((σ : ℂ) + I * y) = a + σ + I * y by ring]
    ring
  rw [hlast, MeasureTheory.integral_mul_const]
  generalize (∫ t : ℝ, Gamma (b - 1 + σ + I * t) * Gamma (σ + I * t) /
    Gamma (a + σ + I * t) * (x : ℂ) ^ (-(σ + I * t))) = J
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

@[dlmf 13.4.E18]
theorem kummerU_barnes_exp {a b : ℂ} {x σ : ℝ}
    (hx : 0 < x) (hb : 0 < (b - 1).re + σ) (hσ : 0 < σ) :
    kummerU a b x =
      (x : ℂ) ^ (1 - b) * exp x / (2 * π * I) *
        ∫ t : ℝ, Gamma (b - 1 + σ + I * t) * Gamma (σ + I * t) /
          Gamma (a + σ + I * t) * (x : ℂ) ^ (-(σ + I * t)) * I := by
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hshift : ∀ N : ℕ, ∀ a b : ℂ, 0 < a.re + N → 0 < (b - 1).re + σ →
      kummerU a b x = (x : ℂ) ^ (1 - b) * exp x / (2 * π * I) *
        ∫ t : ℝ, Gamma (b - 1 + σ + I * t) * Gamma (σ + I * t) /
          Gamma (a + σ + I * t) * (x : ℂ) ^ (-(σ + I * t)) * I := by
    intro N
    induction N with
    | zero => intro a b ha hb; exact kummerU_barnes_exp_of_re_pos hx (by simpa using ha) hb hσ
    | succ N ih =>
      intro a b ha hb
      have hb1 : 0 < (b + 1 - 1).re + σ := by simp at hb ⊢; linarith
      have h1 := ih (a + 1) (b + 1) (by simp at ha ⊢; linarith) hb1
      have h2 := ih (a + 1) b (by simp at ha ⊢; linarith) hb
      have hU := kummerU_contiguous_shift_a (a + 1) b x hx0
      rw [add_sub_cancel_right] at hU
      have hi1 := integrable_kummerU_barnes_exp_integrand (a := a + 1) hx hb1 hσ
      have hi2 := integrable_kummerU_barnes_exp_integrand (a := a + 1) hx hb hσ
      have hpt : ∀ t : ℝ, Gamma (b - 1 + σ + I * t) * Gamma (σ + I * t) /
          Gamma (a + σ + I * t) * (x : ℂ) ^ (-(σ + I * t)) * I =
          Gamma (b + 1 - 1 + σ + I * t) * Gamma (σ + I * t) /
            Gamma (a + 1 + σ + I * t) * (x : ℂ) ^ (-(σ + I * t)) * I +
          (a + 1 - b) * (Gamma (b - 1 + σ + I * t) * Gamma (σ + I * t) /
            Gamma (a + 1 + σ + I * t) * (x : ℂ) ^ (-(σ + I * t)) * I) := by
        intro t
        have hw : b - 1 + σ + I * t ≠ 0 := fun h => by
          have := congrArg re h; simp at this hb; linarith
        rw [show b + 1 - 1 + σ + I * t = (b - 1 + σ + I * t) + 1 by ring,
          Complex.Gamma_add_one _ hw, show a + 1 + σ + I * t = (a + σ + I * t) + 1 by ring,
          div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv,
          one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (a + σ + I * t)]
        ring
      rw [integral_congr_ae (ae_of_all _ hpt), integral_add hi1 (hi2.const_mul _),
        MeasureTheory.integral_const_mul]
      have hUa : kummerU a b x = x * kummerU (a + 1) (b + 1) x + (a + 1 - b) * kummerU (a + 1) b x := by
        linear_combination hU
      have hxp : (x : ℂ) ^ (1 - b) = x * (x : ℂ) ^ (1 - (b + 1)) := by
        rw [show 1 - b = 1 + (1 - (b + 1)) by ring, cpow_add _ _ hx0, cpow_one]
      rw [hUa, h1, h2, hxp]; ring
  obtain ⟨N, hN⟩ := exists_nat_gt (-a.re)
  exact hshift N a b (by linarith) hb

@[dlmf 13.16.E1]
theorem whittakerM_euler {κ μ z : ℂ}
    (hμ : 0 < μ.re + 1 / 2 - |κ.re|) (hz : z ∈ slitPlane) :
    whittakerM κ μ z =
      Gamma (1 + 2 * μ) * z ^ (μ + 1 / 2) * (2 : ℂ) ^ (-(2 * μ)) /
          (Gamma (1 / 2 + μ - κ) * Gamma (1 / 2 + μ + κ)) *
        ∫ t : ℝ in (-1 : ℝ)..1,
          exp (z * t / 2) * (1 + (t : ℂ)) ^ (μ - 1 / 2 - κ) *
            (1 - (t : ℂ)) ^ (μ - 1 / 2 + κ) := by
  let a := 1 / 2 + μ - κ
  let d := 1 / 2 + μ + κ
  have ha : 0 < a.re := by
    dsimp [a]
    norm_num
    linarith [le_abs_self κ.re]
  have hd : 0 < d.re := by
    dsimp [d]
    norm_num
    linarith [neg_abs_le κ.re]
  have hba : 1 + 2 * μ - a = d := by dsimp [a, d]; ring
  let F : ℝ → ℂ := fun t => exp (z * t) * (t : ℂ) ^ (a - 1) *
    (1 - (t : ℂ)) ^ (d - 1)
  have hsub : (∫ t : ℝ in (0 : ℝ)..1, F t) = (1 / 2 : ℂ) *
      ∫ t : ℝ in (-1 : ℝ)..1, F ((1 / 2 : ℝ) * t + 1 / 2) := by
    have he := intervalIntegral.integral_comp_mul_add (f := F) (a := (-1 : ℝ))
      (b := 1) (by norm_num : (1 / 2 : ℝ) ≠ 0) (1 / 2 : ℝ)
    norm_num only [smul_eq_mul] at he
    rw [he]
    simp [Complex.real_smul]
  have hi : exp (-z / 2) * (∫ t : ℝ in (0 : ℝ)..1, F t) =
      (2 : ℂ) ^ (-(2 * μ)) * ∫ t : ℝ in (-1 : ℝ)..1,
        exp (z * t / 2) * (1 + (t : ℂ)) ^ (μ - 1 / 2 - κ) *
          (1 - (t : ℂ)) ^ (μ - 1 / 2 + κ) := by
    rw [hsub, ← mul_assoc, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro t ht
    dsimp only [F]
    have hp : 0 ≤ 1 + t := by linarith [ht.1]
    have hm : 0 ≤ 1 - t := by linarith [ht.2]
    have he : exp (-z / 2) * exp (z * ((1 / 2 : ℝ) * t + 1 / 2)) = exp (z * t / 2) := by
      rw [← exp_add]
      congr 1
      push_cast
      ring
    have htcast : (((1 / 2 : ℝ) * t + 1 / 2 : ℝ) : ℂ) = (1 + (t : ℂ)) / 2 := by
      push_cast; ring
    have htcast' : 1 - (((1 / 2 : ℝ) * t + 1 / 2 : ℝ) : ℂ) = (1 - (t : ℂ)) / 2 := by
      rw [htcast]; ring
    have hp' : ((1 + (t : ℂ)) / 2) ^ (a - 1) =
        (1 + (t : ℂ)) ^ (a - 1) / (2 : ℂ) ^ (a - 1) := by
      convert div_cpow_ofReal_nonneg (a := 1 + t) (b := 2) hp (by norm_num) (a - 1) using 1 <;> push_cast <;> rfl
    have hm' : ((1 - (t : ℂ)) / 2) ^ (d - 1) =
        (1 - (t : ℂ)) ^ (d - 1) / (2 : ℂ) ^ (d - 1) := by
      convert div_cpow_ofReal_nonneg (a := 1 - t) (b := 2) hm (by norm_num) (d - 1) using 1 <;> push_cast <;> rfl
    rw [htcast', htcast, hp', hm']
    have htwo : (1 / 2 : ℂ) / ((2 : ℂ) ^ (a - 1) * (2 : ℂ) ^ (d - 1)) =
        (2 : ℂ) ^ (-(2 * μ)) := by
      rw [← cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0)]
      have hab : (a - 1) + (d - 1) = 2 * μ - 1 := by dsimp [a, d]; ring
      rw [hab, one_div, ← cpow_neg_one, ← cpow_sub _ _ (by norm_num : (2 : ℂ) ≠ 0)]
      congr 1
      ring
    have ha' : a - 1 = μ - 1 / 2 - κ := by dsimp [a]; ring
    have hd' : d - 1 = μ - 1 / 2 + κ := by dsimp [d]; ring
    calc
      _ = (exp (-z / 2) * exp (z * ((1 + (t : ℂ)) / 2))) *
          ((1 / 2 : ℂ) / ((2 : ℂ) ^ (a - 1) * (2 : ℂ) ^ (d - 1))) *
          (1 + (t : ℂ)) ^ (a - 1) * (1 - (t : ℂ)) ^ (d - 1) := by ring
      _ = _ := by
        rw [← htcast]
        push_cast
        norm_num only [ofReal_div, ofReal_one, ofReal_ofNat] at he
        rw [he, htwo, ha', hd']
        ring
  have hb : 0 < (1 + 2 * μ).re := by
    have hab : a + d = 1 + 2 * μ := by dsimp [a, d]; ring
    rw [← hab, add_re]
    exact add_pos ha hd
  rw [whittakerM, show μ - κ + 1 / 2 = a by dsimp [a]; ring,
    kummerM_eq_mul_regularizedHGFun (not_neg_nat_of_re_pos hb),
    regularized_euler_integral ha (by rw [hba]; exact hd), hba]
  change exp (-z / 2) * z ^ (μ + 1 / 2) *
    (Gamma (1 + 2 * μ) * (1 / (Gamma a * Gamma d) * ∫ t : ℝ in (0 : ℝ)..1, F t)) = _
  calc
    _ = Gamma (1 + 2 * μ) * z ^ (μ + 1 / 2) / (Gamma a * Gamma d) *
        (exp (-z / 2) * ∫ t : ℝ in (0 : ℝ)..1, F t) := by ring
    _ = _ := by rw [hi]; dsimp [a, d]; ring

@[dlmf 13.16.E2]
theorem whittakerM_parameter_integral {κ μ lam z : ℂ}
    (hμ : lam.re < μ.re + 1 / 2) (hlam : 0 < lam.re) (hz : z ∈ slitPlane) :
    whittakerM κ μ z =
      Gamma (1 + 2 * μ) * z ^ lam / (Gamma (1 + 2 * μ - 2 * lam) * Gamma (2 * lam)) *
        ∫ t : ℝ in (0 : ℝ)..1,
          whittakerM (κ - lam) (μ - lam) (z * t) * exp (z * (t - 1) / 2) *
            (t : ℂ) ^ (μ - lam - 1 / 2) * (1 - (t : ℂ)) ^ (2 * lam - 1) := by
  let a := μ - κ + 1 / 2
  let b := 1 + 2 * μ
  let c := 1 + 2 * μ - 2 * lam
  let r := μ - lam + 1 / 2
  have hc : 0 < c.re := by dsimp [c]; simp only [mul_re]; norm_num; linarith
  have hb : 0 < b.re := by dsimp [b]; simp only [mul_re]; norm_num; linarith
  have hbc : b - c = 2 * lam := by dsimp [b, c]; ring
  have hl : 0 < (2 * lam).re := by simpa using mul_pos (by norm_num : (0 : ℝ) < 2) hlam
  have hM := regularized_parameter_integral (a := a) (b := b) (c := c) (z := z) hc
    (by rw [hbc]; exact hl)
  rw [hbc] at hM
  have hi : (∫ t : ℝ in (0 : ℝ)..1,
      whittakerM (κ - lam) (μ - lam) (z * t) * exp (z * (t - 1) / 2) *
        (t : ℂ) ^ (μ - lam - 1 / 2) * (1 - (t : ℂ)) ^ (2 * lam - 1)) =
      (exp (-z / 2) * z ^ r * Gamma c) *
        ∫ t : ℝ in (0 : ℝ)..1, regularizedHGFun {a} {c} (z * t) *
          (t : ℂ) ^ (c - 1) * (1 - (t : ℂ)) ^ (2 * lam - 1) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro t ht
    dsimp only
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.1.ne'
    have hp : (z * t) ^ r = z ^ r * (t : ℂ) ^ r := by
      rw [cpow_def_of_ne_zero (mul_ne_zero (slitPlane_ne_zero hz) ht0),
        log_mul_ofReal t ht.1 z (slitPlane_ne_zero hz), add_mul, exp_add,
        cpow_def_of_ne_zero (slitPlane_ne_zero hz), cpow_def_of_ne_zero ht0,
        ofReal_log ht.1.le]
      ring
    rw [whittakerM, show μ - lam - (κ - lam) + 1 / 2 = a by dsimp [a]; ring,
      show 1 + 2 * (μ - lam) = c by dsimp [c]; ring,
      kummerM_eq_mul_regularizedHGFun (not_neg_nat_of_re_pos hc)]
    change exp (-(z * t) / 2) * (z * t) ^ r *
        (Gamma c * regularizedHGFun {a} {c} (z * t)) * exp (z * (t - 1) / 2) *
        (t : ℂ) ^ (μ - lam - 1 / 2) * (1 - (t : ℂ)) ^ (2 * lam - 1) = _
    rw [hp]
    have he : exp (-(z * t) / 2) * exp (z * (t - 1) / 2) = exp (-z / 2) := by
      rw [← exp_add]; congr 1; ring
    have hpow : (t : ℂ) ^ r * (t : ℂ) ^ (μ - lam - 1 / 2) = (t : ℂ) ^ (c - 1) := by
      rw [← cpow_add _ _ ht0]
      congr 1
      dsimp [r, c]
      ring
    calc
      _ = (exp (-(z * t) / 2) * exp (z * (t - 1) / 2)) * z ^ r * Gamma c *
          regularizedHGFun {a} {c} (z * t) *
          ((t : ℂ) ^ r * (t : ℂ) ^ (μ - lam - 1 / 2)) *
          (1 - (t : ℂ)) ^ (2 * lam - 1) := by ring
      _ = _ := by rw [he, hpow]; ring
  rw [hi, whittakerM, kummerM_eq_mul_regularizedHGFun (not_neg_nat_of_re_pos hb)]
  change exp (-z / 2) * z ^ (μ + 1 / 2) * (Gamma b * regularizedHGFun {a} {b} z) = _
  rw [hM]
  have hp : z ^ lam * z ^ r = z ^ (μ + 1 / 2) := by
    rw [← cpow_add _ _ (slitPlane_ne_zero hz)]
    congr 1
    dsimp [r]
    ring
  dsimp only [b, c] at *
  have hp' : z ^ lam * z ^ r = z ^ ((2 * μ + 1) / 2) := by
    rw [hp]
    congr 1
    ring
  field_simp [Gamma_ne_zero_of_re_pos hc, Gamma_ne_zero_of_re_pos hl]
  linear_combination -Gamma (1 + 2 * μ) *
    (∫ t : ℝ in (0 : ℝ)..1, regularizedHGFun {a} {1 + 2 * μ - 2 * lam} (z * t) *
      (t : ℂ) ^ (1 + 2 * μ - 2 * lam - 1) * (1 - (t : ℂ)) ^ (2 * lam - 1)) * hp'

@[dlmf 13.16.E3]
theorem whittakerM_integral_besselJ {κ μ z : ℂ} (hκ : 0 < (κ + μ).re + 1 / 2)
    (hz : z ∈ slitPlane) (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) :
    whittakerM κ μ z / Gamma (1 + 2 * μ) =
      z ^ (1 / 2 : ℂ) * exp (z / 2) / Gamma (1 / 2 + μ + κ) *
        ∫ t : ℝ in Set.Ioi 0,
          exp (-(t : ℂ)) * (t : ℂ) ^ (κ - 1 / 2) *
            besselJ (2 * μ) (2 * (z * t) ^ (1 / 2 : ℂ)) := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  set A := 1 / 2 + μ + κ
  have hA : 0 < A.re := by simp only [A, add_re] at hκ ⊢; norm_num at hκ ⊢; linarith
  have hG : Gamma A ≠ 0 := Gamma_ne_zero_of_re_pos hA
  have hcongr : ∀ t ∈ Set.Ioi (0 : ℝ),
      exp (-(t : ℂ)) * (t : ℂ) ^ (κ - 1 / 2) *
          besselJ (2 * μ) (2 * (z * t) ^ (1 / 2 : ℂ)) =
        z ^ μ * ((Real.exp (-t) : ℂ) * (t : ℂ) ^ (A - 1) *
          regularizedHGFun ∅ {1 + 2 * μ} (-z * t)) := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht)
    rw [besselJ_two_sqrt hz0 ht, show 2 * μ + 1 = 1 + 2 * μ by ring,
      show 2 * μ / 2 = μ by ring, ofReal_exp, ofReal_neg]
    have hp : (t : ℂ) ^ (κ - 1 / 2) * (t : ℂ) ^ μ = (t : ℂ) ^ (A - 1) := by
      rw [← cpow_add _ _ ht0]; simp only [A]; ring_nf
    linear_combination (exp (-(t : ℂ)) * z ^ μ *
      regularizedHGFun ∅ {1 + 2 * μ} (-z * t)) * hp
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, MeasureTheory.integral_const_mul,
    integral_exp_cpow_regularized0F1 hA, whittakerM, kummerM_kummer_transform hμ,
    kummerM_eq_mul_regularizedHGFun hμ, show 1 + 2 * μ - (μ - κ + 1 / 2) = A by
      simp only [A]; ring]
  have hzz : z ^ (μ + 1 / 2) = z ^ (1 / 2 : ℂ) * z ^ μ := by
    rw [← cpow_add _ _ hz0]; ring_nf
  have hex : exp (-z / 2) * exp z = exp (z / 2) := by
    rw [← Complex.exp_add]; ring_nf
  have hΓ : Gamma (1 + 2 * μ) ≠ 0 := Gamma_ne_zero hμ
  rw [hzz, ← hex]
  field_simp

@[dlmf 13.16.E4]
theorem whittakerM_integral_besselI {κ μ z : ℂ} (hκ : (κ - μ).re - 1 / 2 < 0)
    (hz : z ∈ slitPlane) (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) :
    whittakerM κ μ z / Gamma (1 + 2 * μ) =
      z ^ (1 / 2 : ℂ) * exp (-z / 2) / Gamma (1 / 2 + μ - κ) *
        ∫ t : ℝ in Set.Ioi 0,
          exp (-(t : ℂ)) * (t : ℂ) ^ (-κ - 1 / 2) *
            besselI (2 * μ) (2 * (z * t) ^ (1 / 2 : ℂ)) := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  set A := 1 / 2 + μ - κ
  have hA : 0 < A.re := by
    simp only [A, add_re, sub_re] at hκ ⊢; norm_num at hκ ⊢; linarith
  have hG : Gamma A ≠ 0 := Gamma_ne_zero_of_re_pos hA
  have hcongr : ∀ t ∈ Set.Ioi (0 : ℝ),
      exp (-(t : ℂ)) * (t : ℂ) ^ (-κ - 1 / 2) *
          besselI (2 * μ) (2 * (z * t) ^ (1 / 2 : ℂ)) =
        z ^ μ * ((Real.exp (-t) : ℂ) * (t : ℂ) ^ (A - 1) *
          regularizedHGFun ∅ {1 + 2 * μ} (z * t)) := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht)
    rw [besselI_two_sqrt hz0 ht, show 2 * μ + 1 = 1 + 2 * μ by ring,
      show 2 * μ / 2 = μ by ring, ofReal_exp, ofReal_neg]
    have hp : (t : ℂ) ^ (-κ - 1 / 2) * (t : ℂ) ^ μ = (t : ℂ) ^ (A - 1) := by
      rw [← cpow_add _ _ ht0]; simp only [A]; ring_nf
    linear_combination (exp (-(t : ℂ)) * z ^ μ *
      regularizedHGFun ∅ {1 + 2 * μ} (z * t)) * hp
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, MeasureTheory.integral_const_mul,
    integral_exp_cpow_regularized0F1 hA, whittakerM, kummerM_eq_mul_regularizedHGFun hμ,
    show μ - κ + 1 / 2 = A by simp only [A]; ring]
  have hzz : z ^ (μ + 1 / 2) = z ^ (1 / 2 : ℂ) * z ^ μ := by
    rw [← cpow_add _ _ hz0]; ring_nf
  have hΓ : Gamma (1 + 2 * μ) ≠ 0 := Gamma_ne_zero hμ
  rw [hzz]
  field_simp

@[dlmf 13.16.E5]
theorem whittakerW_laplace {κ μ z : ℂ} (hμ : κ.re < μ.re + 1 / 2)
    (hz : 0 < z.re) :
    whittakerW κ μ z =
      z ^ (μ + 1 / 2) * (2 : ℂ) ^ (-(2 * μ)) / Gamma (1 / 2 + μ - κ) *
        ∫ t : ℝ in Set.Ioi 1,
          exp (-z * t / 2) * ((t : ℂ) - 1) ^ (μ - 1 / 2 - κ) *
            ((t : ℂ) + 1) ^ (μ - 1 / 2 + κ) := by
  let p : ℂ := μ - 1 / 2 - κ
  let q : ℂ := μ - 1 / 2 + κ
  let F (t : ℝ) := exp (-z * t / 2) * ((t : ℂ) - 1) ^ p * ((t : ℂ) + 1) ^ q
  have ha : 0 < (1 / 2 + μ - κ).re := by simp; linarith
  have hderiv (u : ℝ) (_hu : u ∈ Set.Ioi (0 : ℝ)) :
      HasDerivWithinAt (fun u : ℝ => 1 + 2 * u) 2 (Set.Ioi 0) u := by
    convert ((hasDerivAt_id u).const_mul 2).const_add 1 |>.hasDerivWithinAt using 1
    · rfl
    · ring
  have hinj : Set.InjOn (fun u : ℝ => 1 + 2 * u) (Set.Ioi 0) := by
    intro u _ v _ h
    linarith
  have himage : (fun u : ℝ => 1 + 2 * u) '' Set.Ioi 0 = Set.Ioi 1 := by
    ext t
    constructor
    · rintro ⟨u, hu, rfl⟩
      change 0 < u at hu
      change 1 < 1 + 2 * u
      linarith
    · intro ht
      change 1 < t at ht
      exact ⟨(t - 1) / 2, by change 0 < (t - 1) / 2; linarith, by ring⟩
  have hs := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj F
  rw [himage] at hs
  have hpoint (u : ℝ) (hu : 0 < u) : |(2 : ℝ)| • F (1 + 2 * u) =
      ((2 : ℂ) ^ (2 * μ) * exp (-z / 2)) *
        (exp (-z * u) * (u : ℂ) ^ p * (1 + (u : ℂ)) ^ q) := by
    have hpow : (2 : ℂ) ^ p * (2 : ℂ) ^ q * 2 = (2 : ℂ) ^ (2 * μ) := by
      calc
        _ = (2 : ℂ) ^ (p + q + 1) := by
          rw [cpow_add (p + q) 1 (by norm_num : (2 : ℂ) ≠ 0), cpow_one,
            cpow_add p q (by norm_num : (2 : ℂ) ≠ 0)]
        _ = _ := by congr 1; dsimp [p, q]; ring
    dsimp only [F]
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 2), Complex.real_smul]
    push_cast
    rw [show -z * (1 + 2 * (u : ℂ)) / 2 = -z / 2 + -z * u by ring,
      show (1 + 2 * (u : ℂ)) - 1 = 2 * u by ring,
      show (1 + 2 * (u : ℂ)) + 1 = 2 * (1 + u) by ring,
      Complex.exp_add,
      mul_cpow_of_re_pos (u := 2) (v := (u : ℂ)) (by norm_num) (by simpa using hu) p,
      mul_cpow_of_re_pos (u := 2) (v := 1 + (u : ℂ)) (by norm_num) (by simp; linarith) q]
    linear_combination (exp (-z / 2) * exp (-z * u) * (u : ℂ) ^ p *
      (1 + (u : ℂ)) ^ q) * hpow
  have hI : (∫ t : ℝ in Set.Ioi 1, F t) = ((2 : ℂ) ^ (2 * μ) * exp (-z / 2)) *
      ∫ u : ℝ in Set.Ioi 0, exp (-z * u) * (u : ℂ) ^ p * (1 + (u : ℂ)) ^ q := by
    rw [hs, ← MeasureTheory.integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi (fun u hu => hpoint u hu)
  have h2 : (2 : ℂ) ^ (2 * μ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  rw [whittakerW, kummerU_laplace ha hz,
    show (1 / 2 + μ - κ) - 1 = p by dsimp [p]; ring,
    show (1 + 2 * μ) - (1 / 2 + μ - κ) - 1 = q by dsimp [q]; ring,
    show (1 / 2 : ℂ) + μ = μ + 1 / 2 by ring]
  change exp (-z / 2) * z ^ (μ + 1 / 2) * (1 / Gamma (μ + 1 / 2 - κ) * _) =
    z ^ (μ + 1 / 2) * (2 : ℂ) ^ (-(2 * μ)) / Gamma (μ + 1 / 2 - κ) *
      ∫ t : ℝ in Set.Ioi 1, F t
  rw [hI, cpow_neg]
  have hcancel (A B D E I : ℂ) (hD : D ≠ 0) :
      E * B * (1 / A * I) = B * D⁻¹ / A * ((D * E) * I) := by
    simp only [div_eq_mul_inv, one_mul]
    linear_combination -(E * B * A⁻¹ * I) * (inv_mul_cancel₀ hD)
  exact hcancel _ _ _ _ _ h2

/-- A Bessel-K integral for Whittaker W. Both parameter bounds are necessary for the
ordinary integral: at `κ = 0`, `μ = 1/2` the omitted second bound would give a zero
Gamma prefactor although `W` is nonzero. The totalized values also differ at `z = 0`. -/
@[dlmf 13.16.E8]
theorem whittakerW_integral_besselK {κ μ z : ℂ} (hκ : 0 < (μ - κ).re + 1 / 2)
    (hκ' : 0 < (-μ - κ).re + 1 / 2)
    (hz : 0 ≤ z.re) (hz0 : z ≠ 0) :
    whittakerW κ μ z =
      2 * z ^ (1 / 2 : ℂ) * exp (-z / 2) /
          (Gamma (1 / 2 + μ - κ) * Gamma (1 / 2 - μ - κ)) *
        ∫ t : ℝ in Set.Ioi 0,
          exp (-(t : ℂ)) * (t : ℂ) ^ (-κ - 1 / 2) *
            besselK (2 * μ) (2 * (z * t) ^ (1 / 2 : ℂ)) := by
  have hzs : z ∈ slitPlane := by
    rw [mem_slitPlane_iff]
    rcases hz.lt_or_eq with h | h
    · exact Or.inl h
    · refine Or.inr fun him => hz0 (Complex.ext ?_ ?_) <;> simp [← h, him]
  have hU := kummerU_eq_integral_besselK (a := 1 / 2 + μ - κ) (b := 1 + 2 * μ) hzs
    (by simp at hκ' ⊢; linarith) (by simp at hκ ⊢; linarith)
  rw [show (1 - (1 + 2 * μ)) / 2 = -μ by ring,
    show 1 / 2 + μ - κ - (1 + 2 * μ) + 1 = 1 / 2 - μ - κ by ring,
    show 1 / 2 + μ - κ - (1 + 2 * μ) / 2 - 1 / 2 = -κ - 1 / 2 by ring,
    show (1 : ℂ) + 2 * μ - 1 = 2 * μ by ring] at hU
  rw [whittakerW, hU]
  have hp : z ^ (1 / 2 + μ) * z ^ (-μ) = z ^ (1 / 2 : ℂ) := by
    rw [← cpow_add _ _ hz0]; ring_nf
  rw [← hp]
  ring

@[dlmf 13.16.E11]
theorem whittakerW_barnes {κ μ : ℂ} {x σ : ℝ} (hx : 0 < x)
    (hμ : 0 < (1 / 2 + μ).re + σ) (hμ' : 0 < (1 / 2 - μ).re + σ)
    (hκ : κ.re + σ < 0) :
    whittakerW κ μ x =
      exp (-(x : ℂ) / 2) / (2 * π * I) *
        ∫ t : ℝ, Gamma (1 / 2 + μ + σ + I * t) * Gamma (1 / 2 - μ + σ + I * t) *
          Gamma (-κ - (σ + I * t)) /
          (Gamma (1 / 2 + μ - κ) * Gamma (1 / 2 - μ - κ)) *
          (x : ℂ) ^ (-(σ + I * t)) * I := by
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hU := kummerU_barnes (a := 1 / 2 + μ - κ) (b := 1 + 2 * μ) (σ := σ + κ.re) hx
    (by simp only [sub_re, add_re] at hμ ⊢; linarith)
    (by simp only [sub_re, add_re, mul_re] at hμ' ⊢; norm_num at hμ' ⊢; linarith)
    (by linarith)
  set F : ℝ → ℂ := fun t => Gamma (1 / 2 + μ - κ + ((σ + κ.re : ℝ) : ℂ) + I * t) *
    Gamma (1 + (1 / 2 + μ - κ) - (1 + 2 * μ) + ((σ + κ.re : ℝ) : ℂ) + I * t) *
    Gamma (-(((σ + κ.re : ℝ) : ℂ) + I * t)) /
    (Gamma (1 / 2 + μ - κ) * Gamma (1 + (1 / 2 + μ - κ) - (1 + 2 * μ))) *
    (x : ℂ) ^ (-(((σ + κ.re : ℝ) : ℂ) + I * t)) * I with hF
  have htr := MeasureTheory.integral_add_right_eq_self (μ := MeasureTheory.volume) F κ.im
  rw [← htr] at hU
  have hpt : ∀ t : ℝ, F (t + κ.im) = (x : ℂ) ^ (-κ) *
      (Gamma (1 / 2 + μ + σ + I * t) * Gamma (1 / 2 - μ + σ + I * t) *
        Gamma (-κ - (σ + I * t)) / (Gamma (1 / 2 + μ - κ) * Gamma (1 / 2 - μ - κ)) *
        (x : ℂ) ^ (-(σ + I * t)) * I) := by
    intro t
    have e : ((σ + κ.re : ℝ) : ℂ) + I * ((t + κ.im : ℝ) : ℂ) = σ + I * t + κ := by
      apply Complex.ext <;> simp
    simp only [hF]
    rw [show 1 / 2 + μ - κ + ((σ + κ.re : ℝ) : ℂ) + I * ((t + κ.im : ℝ) : ℂ) =
        1 / 2 + μ - κ + (((σ + κ.re : ℝ) : ℂ) + I * ((t + κ.im : ℝ) : ℂ)) by ring,
      show 1 + (1 / 2 + μ - κ) - (1 + 2 * μ) + ((σ + κ.re : ℝ) : ℂ) + I * ((t + κ.im : ℝ) : ℂ) =
        1 + (1 / 2 + μ - κ) - (1 + 2 * μ) + (((σ + κ.re : ℝ) : ℂ) + I * ((t + κ.im : ℝ) : ℂ)) by
        ring, e,
      show 1 / 2 + μ - κ + (σ + I * t + κ) = 1 / 2 + μ + σ + I * t by ring,
      show 1 + (1 / 2 + μ - κ) - (1 + 2 * μ) + (σ + I * t + κ) = 1 / 2 - μ + σ + I * t by ring,
      show 1 + (1 / 2 + μ - κ) - (1 + 2 * μ) = 1 / 2 - μ - κ by ring,
      show -((σ : ℂ) + I * t + κ) = -κ - (σ + I * t) by ring,
      show -κ - ((σ : ℂ) + I * t) = -κ + -(σ + I * t) by ring, cpow_add _ _ hx0]
    rw [show -κ + -((σ : ℂ) + I * t) = -κ - (σ + I * t) by ring]
    ring
  simp only [hpt] at hU
  rw [MeasureTheory.integral_const_mul] at hU
  rw [whittakerW, hU]
  have hxx : (x : ℂ) ^ (1 / 2 + μ) * (x : ℂ) ^ (-(1 / 2 + μ - κ)) * (x : ℂ) ^ (-κ) = 1 := by
    rw [← cpow_add _ _ hx0, ← cpow_add _ _ hx0]; ring_nf; exact cpow_zero _
  generalize (∫ t : ℝ, Gamma (1 / 2 + μ + σ + I * t) * Gamma (1 / 2 - μ + σ + I * t) *
    Gamma (-κ - (σ + I * t)) / (Gamma (1 / 2 + μ - κ) * Gamma (1 / 2 - μ - κ)) *
    (x : ℂ) ^ (-(σ + I * t)) * I) = J
  linear_combination (exp (-(x : ℂ) / 2) / (2 * π * I) * J) * hxx

@[dlmf 13.16.E12]
theorem whittakerW_barnes_exp {κ μ : ℂ} {x σ : ℝ} (hx : 0 < x)
    (hμ : 0 < (1 / 2 + μ).re + σ) (hμ' : 0 < (1 / 2 - μ).re + σ) (hσ : 0 < σ) :
    whittakerW κ μ x =
      exp ((x : ℂ) / 2) / (2 * π * I) *
        ∫ t : ℝ, Gamma (1 / 2 + μ + σ + I * t) * Gamma (1 / 2 - μ + σ + I * t) /
          Gamma (1 - κ + σ + I * t) * (x : ℂ) ^ (-(σ + I * t)) * I := by
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  set σ₁ : ℝ := σ + (1 / 2 - μ).re with hσ₁
  set τ₁ : ℝ := (1 / 2 - μ).im with hτ₁
  have hU := kummerU_barnes_exp (a := 1 / 2 + μ - κ) (b := 1 + 2 * μ) (σ := σ₁) hx
    (by simp only [hσ₁, sub_re, add_re, mul_re] at hμ ⊢; norm_num at hμ ⊢; linarith)
    (by simp only [hσ₁] at hμ' ⊢; linarith)
  set F : ℝ → ℂ := fun t => Gamma (1 + 2 * μ - 1 + σ₁ + I * t) * Gamma (σ₁ + I * t) /
    Gamma (1 / 2 + μ - κ + σ₁ + I * t) * (x : ℂ) ^ (-(σ₁ + I * t)) * I with hF
  have htr := MeasureTheory.integral_add_right_eq_self (μ := MeasureTheory.volume) F τ₁
  rw [← htr] at hU
  have hpt : ∀ t : ℝ, F (t + τ₁) = (x : ℂ) ^ (-(1 / 2 - μ)) *
      (Gamma (1 / 2 + μ + σ + I * t) * Gamma (1 / 2 - μ + σ + I * t) /
        Gamma (1 - κ + σ + I * t) * (x : ℂ) ^ (-(σ + I * t)) * I) := by
    intro t
    have e : (σ₁ : ℂ) + I * ((t + τ₁ : ℝ) : ℂ) = σ + I * t + (1 / 2 - μ) := by
      apply Complex.ext <;> simp [hσ₁, hτ₁]
    simp only [hF]
    rw [show 1 + 2 * μ - 1 + (σ₁ : ℂ) + I * ((t + τ₁ : ℝ) : ℂ) =
        1 + 2 * μ - 1 + ((σ₁ : ℂ) + I * ((t + τ₁ : ℝ) : ℂ)) by ring,
      show 1 / 2 + μ - κ + (σ₁ : ℂ) + I * ((t + τ₁ : ℝ) : ℂ) =
        1 / 2 + μ - κ + ((σ₁ : ℂ) + I * ((t + τ₁ : ℝ) : ℂ)) by ring, e,
      show 1 + 2 * μ - 1 + (σ + I * t + (1 / 2 - μ)) = 1 / 2 + μ + σ + I * t by ring,
      show (σ : ℂ) + I * t + (1 / 2 - μ) = 1 / 2 - μ + σ + I * t by ring,
      show 1 / 2 + μ - κ + (1 / 2 - μ + σ + I * t) = 1 - κ + σ + I * t by ring,
      show -(1 / 2 - μ + σ + I * t) = -(1 / 2 - μ) + -((σ : ℂ) + I * t) by ring,
      cpow_add _ _ hx0]
    ring
  simp only [hpt] at hU
  rw [MeasureTheory.integral_const_mul] at hU
  rw [whittakerW, hU]
  have hxx : (x : ℂ) ^ (1 / 2 + μ) * (x : ℂ) ^ (1 - (1 + 2 * μ)) * (x : ℂ) ^ (-(1 / 2 - μ)) = 1 := by
    rw [← cpow_add _ _ hx0, ← cpow_add _ _ hx0]; ring_nf; exact cpow_zero _
  have hee : exp (-(x : ℂ) / 2) * exp (x : ℂ) = exp ((x : ℂ) / 2) := by
    rw [← exp_add]; ring_nf
  generalize (∫ t : ℝ, Gamma (1 / 2 + μ + σ + I * t) * Gamma (1 / 2 - μ + σ + I * t) /
    Gamma (1 - κ + σ + I * t) * (x : ℂ) ^ (-(σ + I * t)) * I) = J
  rw [← hee]
  linear_combination (exp (-(x : ℂ) / 2) * exp (x : ℂ) / (2 * π * I) * J) * hxx

end DLMF.Confluent
