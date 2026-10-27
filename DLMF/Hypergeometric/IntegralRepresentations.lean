/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.BarnesAux
public import DLMF.Hypergeometric.FurtherTransformations
public import DLMF.Hypergeometric.Saalschutz
public import DLMF.Gamma.Integrals

/-!
# Integral representations (DLMF §15.6)

The source uses Olver's regularized function. Euler's E1 is already recorded,
with the equivalent ordinary-function normalization, in `EulerIntegral`.
The substitutions and vertical Barnes integrals below need no continued contour
branches. Barnes's integral E6 is proved in `DLMF.Hypergeometric.BarnesAux` from the
Mellin–Barnes integral for `(1+u)^{-a}` and analytic continuation in `c`. The loop integral E2 is
in `DLMF.Hypergeometric.LoopIntegral`, over an explicit loop about `1`; E3–E5 (Pochhammer and
other loop contours) are not recorded. E7 follows from Barnes's first lemma
(`DLMF.Gamma.mellin_barnes_four`) after the binomial expansion of `(1-z)^s`; E9 follows by
termwise integration and the Chu–Vandermonde and Pfaff–Saalschütz sums.
-/

@[expose] public section

open Complex Filter
open scoped Real Topology

noncomputable section

namespace DLMF.Hypergeometric

@[dlmf 15.6.E2_5]
theorem integral_Ioi {a b c z : ℂ} (hb : 0 < b.re) (hcb : 0 < (c - b).re) (hz : ‖z‖ < 1) :
    regularizedGaussHGFun a b c z =
      (1 / (Gamma b * Gamma (c - b))) * ∫ t : ℝ in Set.Ioi 0,
        (t : ℂ) ^ (b - 1) * (t + 1 : ℂ) ^ (a - c) / ((t : ℂ) - z * t + 1) ^ a := by
  have hc0 : 0 < c.re := by
    have : c.re = b.re + (c - b).re := by simp
    linarith
  have hcn : ∀ k : ℕ, c ≠ -(k : ℂ) := not_neg_nat_of_re_pos hc0
  have hΓc : Gamma c ≠ 0 := Gamma_ne_zero_of_re_pos hc0
  -- The substitution `u = t/(1+t)`.
  set f : ℝ → ℝ := fun t => t / (1 + t) with hf
  set f' : ℝ → ℝ := fun t => 1 / (1 + t) ^ 2 with hf'
  have hderiv : ∀ t ∈ Set.Ioi (0 : ℝ), HasDerivWithinAt f (f' t) (Set.Ioi 0) t := by
    intro t ht
    have h1 : 1 + t ≠ 0 := ne_of_gt (by linarith [Set.mem_Ioi.mp ht])
    have hd : HasDerivAt f (f' t) t := by
      convert (hasDerivAt_id t).div ((hasDerivAt_id t).const_add 1) h1 using 1
      · rfl
      · simp only [hf', id]; ring
    exact hd.hasDerivWithinAt
  have hinj : Set.InjOn f (Set.Ioi 0) := by
    intro x hx y hy hxy
    have hx' : 1 + x ≠ 0 := ne_of_gt (by linarith [Set.mem_Ioi.mp hx])
    have hy' : 1 + y ≠ 0 := ne_of_gt (by linarith [Set.mem_Ioi.mp hy])
    simp only [hf] at hxy
    field_simp at hxy
    linarith
  have himage : f '' Set.Ioi 0 = Set.Ioo 0 1 := by
    ext u
    constructor
    · rintro ⟨t, ht, rfl⟩
      have ht' : 0 < t := ht
      refine ⟨by positivity, ?_⟩
      rw [hf, div_lt_one (by linarith)]
      linarith
    · rintro ⟨h0, h1⟩
      refine ⟨u / (1 - u), div_pos h0 (by linarith), ?_⟩
      have : 1 - u ≠ 0 := ne_of_gt (by linarith)
      simp only [hf]
      field_simp
      ring
  have key := MeasureTheory.integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj
    (fun u : ℝ => (u : ℂ) ^ (b - 1) * (1 - (u : ℂ)) ^ (c - b - 1) * (1 - z * u) ^ (-a))
  rw [himage] at key
  rw [regularizedGaussHGFun_eq_div_Gamma hcn, ordinaryHypergeometric_eq_integral hb hcb hz,
    intervalIntegral.integral_of_le zero_le_one, MeasureTheory.integral_Ioc_eq_integral_Ioo, key]
  have hpt : ∫ t : ℝ in Set.Ioi 0, |f' t| • ((f t : ℂ) ^ (b - 1) * (1 - (f t : ℂ)) ^ (c - b - 1) *
      (1 - z * f t) ^ (-a)) = ∫ t : ℝ in Set.Ioi 0,
        (t : ℂ) ^ (b - 1) * (t + 1 : ℂ) ^ (a - c) / ((t : ℂ) - z * t + 1) ^ a := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := ht
    have ht1 : 0 < 1 + t := by linarith
    set X : ℂ := 1 + t - z * t with hX
    have hXre : 0 < X.re := by
      have := (re_le_norm z).trans_lt hz
      simp only [hX, sub_re, add_re, one_re, ofReal_re, mul_re, ofReal_im, mul_zero, sub_zero]
      nlinarith
    have hX0 : X ≠ 0 := by intro h; rw [h] at hXre; simp at hXre
    have hft : 0 < f t := by simp only [hf]; positivity
    have h1ft : 1 - f t = 1 / (1 + t) := by simp only [hf]; field_simp; ring
    have e1 : (1 - (f t : ℂ)) = ((1 / (1 + t) : ℝ) : ℂ) := by rw [← h1ft]; push_cast; ring
    have e2 : 1 - z * (f t : ℂ) = X * (((1 + t)⁻¹ : ℝ) : ℂ) := by
      have h1t : (1 + (t : ℂ)) ≠ 0 := by exact_mod_cast ht1.ne'
      simp only [hf, hX]; push_cast; field_simp
    have e3 : ((t : ℂ) - z * t + 1) = X := by rw [hX]; ring
    have e4 : (t + 1 : ℂ) = ((1 + t : ℝ) : ℂ) := by push_cast; ring
    rw [e1, e2, e3, e4, abs_of_pos (by simp only [hf']; positivity), Complex.real_smul,
      ofReal_cpow_eq_exp_log hft, ofReal_cpow_eq_exp_log (by positivity),
      ofReal_cpow_eq_exp_log ht0, ofReal_cpow_eq_exp_log ht1,
      cpow_def_of_ne_zero (mul_ne_zero hX0 (ofReal_ne_zero.mpr (by positivity))),
      Complex.log_mul_ofReal _ (by positivity) _ hX0, cpow_def_of_ne_zero hX0,
      show ((f' t : ℝ) : ℂ) = Complex.exp (((-2 * Real.log (1 + t) : ℝ) : ℂ)) by
        rw [← ofReal_exp, show -2 * Real.log (1 + t) = -(Real.log (1 + t) + Real.log (1 + t)) by
          ring, Real.exp_neg, Real.exp_add, Real.exp_log ht1]
        simp only [hf']; push_cast; ring,
      show f t = t / (1 + t) from rfl, Real.log_div ht0.ne' ht1.ne', one_div,
      Real.log_inv, div_eq_mul_inv, ← Complex.exp_neg]
    simp only [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hpt, show ∀ Y : ℂ, Gamma c / (Gamma b * Gamma (c - b)) * Y / Gamma c =
    1 / (Gamma b * Gamma (c - b)) * Y from fun Y => by field_simp]

/-- A vertical separating line `t = σ + i y`; the factor `i` from `dt` is canceled. -/
@[dlmf 15.6.E6]
theorem barnes_integral {a b c : ℂ} {x σ : ℝ} (hx : -1 < x) (hx0 : x < 0)
    (ha : 0 < a.re + σ) (hb : 0 < b.re + σ) (hσ : σ < 0) :
    regularizedGaussHGFun a b c (x : ℂ) =
      (1 / (2 * Real.pi * Gamma a * Gamma b)) * ∫ y : ℝ,
        Gamma (a + σ + I * y) * Gamma (b + σ + I * y) * Gamma (-((σ : ℂ) + I * y)) /
          Gamma (c + σ + I * y) * (-(x : ℂ)) ^ ((σ : ℂ) + I * y) :=
  barnes_integral_all hx hx0 ha hb hσ

/-- `Γ(x+n) = (x)ₙ Γ(x)` for real `x > 0`. -/
theorem hypSV_real_Gamma_add_nat {x : ℝ} (hx : 0 < x) (n : ℕ) :
    Real.Gamma (n + x) = (ascPochhammer ℝ n).eval x * Real.Gamma x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ascPochhammer_succ_eval, show ((n + 1 : ℕ) : ℝ) + x = (n + x) + 1 by push_cast; ring,
      Real.Gamma_add_one (by positivity), ih]
    ring

open MeasureTheory in
open scoped Nat in
@[dlmf 15.6.E7]
theorem barnes_integral_one_sub {a b c z : ℂ} {σ : ℝ} (hz : ‖z‖ < 1)
    (ha : 0 < a.re + σ) (hb : 0 < b.re + σ) (hσ : σ < 0)
    (hc : σ < (c - a - b).re) :
    regularizedGaussHGFun a b c z =
      (1 / (2 * Real.pi * Gamma a * Gamma b * Gamma (c - a) * Gamma (c - b))) * ∫ y : ℝ,
        Gamma (a + σ + I * y) * Gamma (b + σ + I * y) * Gamma (c - a - b - σ - I * y)*
          Gamma (-((σ : ℂ) + I * y)) * (1 - z) ^ ((σ : ℂ) + I * y) := by
  set τ : ℝ := -σ with hτ
  have hτ0 : 0 < τ := by rw [hτ]; linarith
  set a' : ℂ := a + σ with ha'
  set b' : ℂ := b + σ with hb'
  set c' : ℂ := c - a - b - σ with hc'
  have ha'0 : 0 < a'.re := by simp [ha']; linarith
  have hb'0 : 0 < b'.re := by simp [hb']; linarith
  have hc'0 : 0 < c'.re := by simp [hc']; simp at hc; linarith
  -- terms
  set F : ℕ → ℝ → ℂ := fun n y => Gamma (a' + I * y) * Gamma (b' + I * y) * Gamma (c' - I * y) *
    Gamma ((n - σ : ℝ) - I * y) * (z ^ n / n !) with hF
  have hlim : ∀ y : ℝ, HasSum (fun n => F n y)
      (Gamma (a + σ + I * y) * Gamma (b + σ + I * y) * Gamma (c - a - b - σ - I * y) *
        Gamma (-((σ : ℂ) + I * y)) * (1 - z) ^ ((σ : ℂ) + I * y)) := by
    intro y
    have hs : ∀ k : ℕ, -((σ : ℂ) + I * y) ≠ -(k : ℂ) := by
      apply not_neg_nat_of_re_pos; simp; linarith
    have h := (hasSum_one_sub_cpow_neg (-((σ : ℂ) + I * y)) hz).mul_left
      (Gamma (a + σ + I * y) * Gamma (b + σ + I * y) * Gamma (c - a - b - σ - I * y) *
        Gamma (-((σ : ℂ) + I * y)))
    rw [neg_neg] at h
    refine h.congr_fun fun n => ?_
    have hG := Gamma_add_nat_div_Gamma_eq (n := n) _ hs
    rw [div_eq_iff (Gamma_ne_zero hs)] at hG
    simp only [hF, ha', hb', hc']
    rw [show ((n - σ : ℝ) : ℂ) - I * y = -((σ : ℂ) + I * y) + n by push_cast; ring, hG]
    simp only [poch]
    ring
  have hcont (w : ℂ) (hw : 0 < w.re) (e : ℂ) (he : e.re = 0) :
      Continuous fun y : ℝ => Gamma (w + e * y) := by
    rw [continuous_iff_continuousAt]
    intro y
    refine ContinuousAt.comp (g := Gamma) (DLMF.Gamma.continuousAt_Gamma_of_re_pos ?_) (by fun_prop)
    simp [he, hw]
  have hcont' (w : ℂ) (hw : 0 < w.re) : Continuous fun y : ℝ => Gamma (w - I * y) := by
    have := hcont w hw (-I) (by simp)
    refine this.congr fun y => ?_
    ring_nf
  have hτn (n : ℕ) : 0 < ((n - σ : ℝ) : ℂ).re := by
    simp; have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
  have hmeas (n : ℕ) : AEStronglyMeasurable (F n) volume := by
    refine Continuous.aestronglyMeasurable ?_
    simp only [hF]
    have := hcont a' ha'0 I (by simp)
    have := hcont b' hb'0 I (by simp)
    have := hcont' c' hc'0
    have := hcont' _ (hτn n)
    fun_prop
  set e : ℕ → ℝ := fun n => Real.Gamma (n + τ) * (‖z‖ ^ n / n !) with he
  have he_s : Summable e := by
    have h := (hasSum_one_sub_cpow_neg (τ : ℂ) (z := (‖z‖ : ℂ)) (by simpa using hz)).summable
    have h' : Summable fun n : ℕ => (ascPochhammer ℝ n).eval τ / n ! * ‖z‖ ^ n := by
      rw [← Complex.summable_ofReal]
      refine h.congr fun n => ?_
      simp only [poch, ascPochhammer_eval_ofReal]
      push_cast; ring
    refine (h'.mul_left (Real.Gamma τ)).congr fun n => ?_
    simp only [he]
    rw [hypSV_real_Gamma_add_nat hτ0]
    ring
  set g : ℝ → ℝ := fun y => ‖Gamma (a' + I * y) * Gamma (c' - I * y)‖ with hg
  have hg_int : Integrable g :=
    (DLMF.Gamma.integrable_Gamma_add_mul_Gamma_sub ha'0 hc'0).norm
  set bound : ℕ → ℝ → ℝ := fun n y => Real.Gamma b'.re * e n * g y with hbound
  have hbd (n : ℕ) (y : ℝ) : ‖F n y‖ ≤ bound n y := by
    simp only [hF, hbound, he, hg, norm_mul, norm_div, norm_pow, Complex.norm_natCast]
    have h1 : ‖Gamma (b' + I * y)‖ ≤ Real.Gamma b'.re := by
      have := DLMF.Gamma.RamanujanAux.norm_Gamma_le_Gamma_re (z := b' + I * y) (by simpa using hb'0)
      simpa using this
    have h2 : ‖Gamma (((n - σ : ℝ) : ℂ) - I * y)‖ ≤ Real.Gamma (n + τ) := by
      have := DLMF.Gamma.RamanujanAux.norm_Gamma_le_Gamma_re (z := ((n - σ : ℝ) : ℂ) - I * y)
        (by simpa using hτn n)
      simpa [hτ, sub_eq_add_neg] using this
    have h0 : 0 ≤ ‖z‖ ^ n / (n ! : ℝ) := by positivity
    calc ‖Gamma (a' + I * y)‖ * ‖Gamma (b' + I * y)‖ * ‖Gamma (c' - I * y)‖ *
          ‖Gamma (((n - σ : ℝ) : ℂ) - I * y)‖ * (‖z‖ ^ n / (n ! : ℝ))
        ≤ ‖Gamma (a' + I * y)‖ * Real.Gamma b'.re * ‖Gamma (c' - I * y)‖ *
          Real.Gamma (n + τ) * (‖z‖ ^ n / (n ! : ℝ)) := by gcongr
      _ = _ := by ring
  have hS := hasSum_integral_of_dominated_convergence bound hmeas
    (fun n => Eventually.of_forall fun y => hbd n y)
    (Eventually.of_forall fun y => by
      simp only [hbound]; exact (he_s.mul_left _).mul_right _)
    (by
      simp only [hbound]
      simp_rw [tsum_mul_right, tsum_mul_left]
      exact hg_int.const_mul _)
    (Eventually.of_forall hlim)
  have hΓa : Gamma a ≠ 0 := Gamma_ne_zero_of_re_pos (by simp [ha'] at ha'0; linarith)
  have hΓb : Gamma b ≠ 0 := Gamma_ne_zero_of_re_pos (by simp [hb'] at hb'0; linarith)
  have hΓca : Gamma (c - a) ≠ 0 := Gamma_ne_zero_of_re_pos (by
    simp [hc'] at hc'0; simp [hb'] at hb'0; simp; linarith)
  have hΓcb : Gamma (c - b) ≠ 0 := Gamma_ne_zero_of_re_pos (by
    simp [hc'] at hc'0; simp [ha'] at ha'0; simp; linarith)
  have hterm (n : ℕ) : 1 / (2 * Real.pi * Gamma a * Gamma b * Gamma (c - a) * Gamma (c - b)) *
      ∫ y, F n y = poch a n * poch b n / (n ! * Gamma (c + n)) * z ^ n := by
    simp only [hF]
    rw [integral_mul_const]
    have hMB := DLMF.Gamma.mellin_barnes_four (a := a') (b := b') (c := c')
      (d := ((n - σ : ℝ) : ℂ)) ha'0 hb'0 hc'0 (hτn n)
    have hπ : (2 * (Real.pi : ℂ)) ≠ 0 := by
      have := Real.pi_pos; exact mul_ne_zero two_ne_zero (by exact_mod_cast this.ne')
    have hI : ∫ y : ℝ, Gamma (a' + I * y) * Gamma (b' + I * y) * Gamma (c' - I * y) *
        Gamma (((n - σ : ℝ) : ℂ) - I * y) = 2 * Real.pi * (Gamma (a' + c') *
          Gamma (a' + ((n - σ : ℝ) : ℂ)) * Gamma (b' + c') * Gamma (b' + ((n - σ : ℝ) : ℂ)) /
          Gamma (a' + b' + c' + ((n - σ : ℝ) : ℂ))) := by
      rw [← hMB]; field_simp
    rw [hI]
    have e1 : a' + c' = c - b := by simp only [ha', hc']; ring
    have e2 : a' + ((n - σ : ℝ) : ℂ) = a + n := by simp only [ha']; push_cast; ring
    have e3 : b' + c' = c - a := by simp only [hb', hc']; ring
    have e4 : b' + ((n - σ : ℝ) : ℂ) = b + n := by simp only [hb']; push_cast; ring
    have e5 : a' + b' + c' + ((n - σ : ℝ) : ℂ) = c + n := by
      simp only [ha', hb', hc']; push_cast; ring
    rw [e1, e2, e3, e4, e5]
    have hpa := Gamma_add_nat_div_Gamma_eq (n := n) a (not_neg_nat_of_re_pos (by
      simp [ha'] at ha'0; linarith))
    have hpb := Gamma_add_nat_div_Gamma_eq (n := n) b (not_neg_nat_of_re_pos (by
      simp [hb'] at hb'0; linarith))
    rw [div_eq_iff hΓa] at hpa
    rw [div_eq_iff hΓb] at hpb
    rw [hpa, hpb]
    simp only [poch]
    have hn! : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    by_cases hΓc : Gamma (c + n) = 0
    · simp [hΓc]
    field_simp
  have hS' := hS.mul_left (1 / (2 * Real.pi * Gamma a * Gamma b * Gamma (c - a) * Gamma (c - b)))
  rw [funext hterm] at hS'
  exact (hasSum_regularizedGaussHGFun_coeff a b c hz).unique hS'

/-- Absolute summability of the regularized series inside the unit disk. -/
theorem summable_norm_regularizedGaussHGFun_term (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable fun n : ℕ => ‖(ascPochhammer ℂ n).eval a * (ascPochhammer ℂ n).eval b * z ^ n /
      n.factorial * (Gamma (c + n))⁻¹‖ := by
  have h := (regularizedGaussHGFunSeries a b c).summable_norm_apply
    (mem_eball_radius_regularizedGaussHGFunSeries a b c hz)
  refine h.congr fun n => ?_
  rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff, coeff_regularizedGaussHGFunSeries,
    smul_eq_mul]
  congr 1
  ring

@[dlmf 15.6.E8]
theorem fractional_integral {a b c d z : ℂ} (hd : 0 < d.re) (hcd : 0 < (c - d).re) (hz : ‖z‖ < 1) :
    regularizedGaussHGFun a b c z =
      (1 / Gamma (c - d)) * ∫ t : ℝ in (0 : ℝ)..1,
        regularizedGaussHGFun a b d (z * t) * (t : ℂ) ^ (d - 1) * (1 - (t : ℂ)) ^ (c - d - 1) := by
  let w : ℝ → ℂ := fun t => (t : ℂ) ^ (d - 1) * (1 - (t : ℂ)) ^ (c - d - 1)
  let e : ℕ → ℂ := fun n => (ascPochhammer ℂ n).eval a * (ascPochhammer ℂ n).eval b * z ^ n /
    n.factorial * (Gamma (d + n))⁻¹
  let F : ℕ → ℝ → ℂ := fun n t => w t * (e n * (t : ℂ) ^ n)
  have hw : IntervalIntegrable w MeasureTheory.volume 0 1 := betaIntegral_convergent hd hcd
  have he : Summable (fun n => ‖e n‖) := summable_norm_regularizedGaussHGFun_term a b d hz
  have hFi (n : ℕ) : IntervalIntegrable (F n) MeasureTheory.volume 0 1 :=
    hw.mul_continuousOn (by fun_prop)
  have hs := intervalIntegral.hasSum_integral_of_dominated_convergence
    (a := (0 : ℝ)) (b := 1) (μ := MeasureTheory.volume)
    (F := F) (f := fun t => regularizedGaussHGFun a b d (z * t) * (t : ℂ) ^ (d - 1) *
      (1 - (t : ℂ)) ^ (c - d - 1))
    (fun n t => ‖e n‖ * ‖w t‖) (fun n => (hFi n).def'.aestronglyMeasurable)
    (fun n => Filter.Eventually.of_forall fun t ht => ?_)
    (Filter.Eventually.of_forall fun t _ => he.mul_right ‖w t‖)
    (by
      simp_rw [tsum_mul_right]
      exact hw.norm.const_mul _)
    (Filter.Eventually.of_forall fun t ht => ?_)
  · have hc0 : 0 < c.re := by
      have : c.re = d.re + (c - d).re := by simp
      linarith
    have hterm (n : ℕ) : ∫ t : ℝ in (0 : ℝ)..1, F n t = e n * betaIntegral (d + n) (c - d) := by
      rw [betaIntegral, ← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      intro t ht
      have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht.1)
      have hp : (t : ℂ) ^ (d + n - 1) = (t : ℂ) ^ (d - 1) * (t : ℂ) ^ n := by
        rw [show d + n - 1 = (d - 1) + n by ring, cpow_add _ _ ht0, cpow_natCast]
      simp only [F, w, e]
      rw [hp]
      ring
    have hdn (n : ℕ) : 0 < (d + n).re := by
      have : (d + n).re = d.re + n := by simp
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hscaled (n : ℕ) : 1 / Gamma (c - d) * (∫ t : ℝ in (0 : ℝ)..1, F n t) =
        (ascPochhammer ℂ n).eval a * (ascPochhammer ℂ n).eval b * z ^ n / n.factorial *
          (Gamma (c + n))⁻¹ := by
      have hB := Gamma_mul_Gamma_eq_betaIntegral (hdn n) hcd
      rw [show d + n + (c - d) = c + n by ring] at hB
      have hcn : Gamma (c + n) ≠ 0 := Gamma_ne_zero_of_re_pos (by
        have : (c + n).re = c.re + n := by simp
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith)
      have hdn0 : Gamma (d + n) ≠ 0 := Gamma_ne_zero_of_re_pos (hdn n)
      have hcd0 : Gamma (c - d) ≠ 0 := Gamma_ne_zero_of_re_pos hcd
      have hBeq : betaIntegral (d + n) (c - d) = Gamma (d + n) * Gamma (c - d) / Gamma (c + n) := by
        rw [eq_div_iff hcn, mul_comm]; exact hB.symm
      rw [hterm, hBeq]
      simp only [e]
      field_simp
    have hs' := hs.mul_left (1 / Gamma (c - d))
    simp_rw [hscaled] at hs'
    rw [regularizedGaussHGFun_eq_tsum, ← hs'.tsum_eq]
  · rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    have ht1 : ‖(t : ℂ)‖ ≤ 1 := by
      simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1] using ht.2
    calc
      ‖F n t‖ = ‖w t‖ * (‖e n‖ * ‖(t : ℂ)‖ ^ n) := by
        simp only [F, norm_mul, norm_pow]
      _ ≤ ‖w t‖ * (‖e n‖ * 1) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) ht1) (norm_nonneg _))
          (norm_nonneg _)
      _ = _ := by ring
  · rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    have hzt : ‖z * t‖ < 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1]
      nlinarith [norm_nonneg z, ht.2]
    have h := (summable_regularizedGaussHGFun_term a b d hzt).hasSum
    rw [← regularizedGaussHGFun_eq_tsum] at h
    have h' := h.mul_left (w t)
    simp only [F, e, w]
    convert h' using 1
    · funext n
      rw [mul_pow]
      ring
    · ring

section hypSVProduct

open Finset
open scoped Nat

/-- A summable double series is the sum of its antidiagonal sums. -/
theorem hypSV_hasSum_antidiag {g : ℕ × ℕ → ℂ} (h : Summable g) :
    HasSum (fun N => ∑ p ∈ antidiagonal N, g p) (∑' p, g p) := by
  set e := Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)
  have h' : HasSum (g ∘ e) (∑' p, g p) := by
    rw [e.hasSum_iff]; exact h.hasSum
  refine h'.sigma fun N => ?_
  have := hasSum_fintype (fun c : antidiagonal N => g c.1)
  rw [Finset.sum_coe_sort (antidiagonal N) g] at this
  exact this

/-- A nonnegative double series with summable antidiagonal sums is summable. -/
theorem hypSV_summable_of_antidiag {G : ℕ × ℕ → ℝ} (h0 : ∀ p, 0 ≤ G p)
    (h : Summable fun N => ∑ p ∈ antidiagonal N, G p) : Summable G := by
  set e := Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)
  rw [← e.summable_iff]
  refine (summable_sigma_of_nonneg (f := G ∘ e) (fun _ => h0 _)).mpr
    ⟨fun N => Summable.of_finite, h.congr fun N => ?_⟩
  rw [tsum_fintype]
  exact (Finset.sum_coe_sort (antidiagonal N) G).symm

/-- Real Chu–Vandermonde in factorial form. -/
theorem hypSV_real_vandermonde (u v : ℝ) (N : ℕ) :
    ∑ p ∈ antidiagonal N, (ascPochhammer ℝ p.1).eval u / p.1 ! *
      ((ascPochhammer ℝ p.2).eval v / p.2 !) = (ascPochhammer ℝ N).eval (u + v) / N ! := by
  have h := poch_add_eq_sum (u : ℂ) v N
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => (ascPochhammer ℝ i).eval u / i ! * ((ascPochhammer ℝ j).eval v / j !))]
  apply Complex.ofReal_injective
  push_cast
  simp only [poch, ← ofReal_add, ascPochhammer_eval_ofReal] at h
  rw [h, Finset.sum_div]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' : m ≤ N := by simpa [Nat.lt_succ_iff] using hm
  have hc := Nat.choose_mul_factorial_mul_factorial hm'
  have hc' : (N.choose m : ℂ) * m ! * (N - m)! = N ! := by exact_mod_cast hc
  have h1 : (m ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr m.factorial_ne_zero
  have h2 : ((N - m)! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (N - m).factorial_ne_zero
  have h3 : (N.choose m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos hm').ne'
  rw [← hc']
  field_simp

/-- `Re c` controls the Pochhammer symbol from below. -/
theorem hypSV_norm_poch_ge {c : ℂ} (hc : 0 < c.re) (n : ℕ) :
    (ascPochhammer ℝ n).eval c.re ≤ ‖poch c n‖ := by
  induction n with
  | zero => simp [poch_zero]
  | succ n ih =>
    rw [poch_succ, norm_mul, ascPochhammer_succ_eval]
    have h1 : c.re + n ≤ ‖c + n‖ := by
      have := Complex.re_le_norm (c + n)
      simpa using this
    exact mul_le_mul ih h1 (by positivity) (norm_nonneg _)

/-- `‖Γ(c+N)‖⁻¹ ≤ (‖Γ(Re c)‖/‖Γ c‖) ‖Γ(Re c + N)‖⁻¹` for `Re c > 0`. -/
theorem hypSV_norm_recip_Gamma_le {c : ℂ} (hc : 0 < c.re) (N : ℕ) :
    ‖Gamma (c + N)‖⁻¹ ≤ ‖Gamma (c.re : ℂ)‖ / ‖Gamma c‖ * ‖Gamma ((c.re : ℂ) + N)‖⁻¹ := by
  have hcn : ∀ k : ℕ, c ≠ -k := not_neg_nat_of_re_pos hc
  have hCn : ∀ k : ℕ, (c.re : ℂ) ≠ -k := not_neg_nat_of_re_pos (by simpa using hc)
  have h1 := Gamma_add_nat_div_Gamma_eq (n := N) c hcn
  have h2 := Gamma_add_nat_div_Gamma_eq (n := N) (c.re : ℂ) hCn
  have hg1 : Gamma c ≠ 0 := Gamma_ne_zero hcn
  have hg2 : Gamma (c.re : ℂ) ≠ 0 := Gamma_ne_zero hCn
  rw [div_eq_iff hg1] at h1
  rw [div_eq_iff hg2] at h2
  rw [h1, h2, ascPochhammer_eval_ofReal, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hP : 0 < (ascPochhammer ℝ N).eval c.re := by
    have := ascPochhammer_pos N c.re hc
    exact this
  rw [abs_of_pos hP]
  have hle := hypSV_norm_poch_ge hc N
  have hn1 : 0 < ‖Gamma c‖ := norm_pos_iff.mpr hg1
  have hn2 : 0 < ‖Gamma (c.re : ℂ)‖ := norm_pos_iff.mpr hg2
  have hpc : 0 < ‖(ascPochhammer ℂ N).eval c‖ := hP.trans_le hle
  rw [show ‖Gamma (c.re : ℂ)‖ / ‖Gamma c‖ * ((ascPochhammer ℝ N).eval c.re * ‖Gamma (c.re : ℂ)‖)⁻¹
      = (‖Gamma c‖ * (ascPochhammer ℝ N).eval c.re)⁻¹ by field_simp]
  rw [mul_comm]
  exact inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left hle hn1.le)

/-- Rearranging `∑ₘ (p)ₘ(q)ₘ/m! xᵐ 𝐅(s+m, r; c+m; x)` by total degree. -/
theorem hypSV_hasSum_shift_series (p q r s c A B : ℂ) (hc : 0 < c.re) {x : ℂ} (hx : ‖x‖ < 1)
    (hK : ∀ N, ∑ m ∈ range (N + 1), poch p m * poch q m / m ! *
      (poch (s + m) (N - m) * poch r (N - m) / (N - m)!) = poch A N * poch B N / N !) :
    HasSum (fun m : ℕ => poch p m * poch q m / m ! * x ^ m *
      regularizedGaussHGFun (s + m) r (c + m) x) (regularizedGaussHGFun A B c x) := by
  set g : ℕ × ℕ → ℂ := fun mk => poch p mk.1 * poch q mk.1 / mk.1 ! * x ^ mk.1 *
    (poch (s + mk.1) mk.2 * poch r mk.2 / (mk.2 ! * Gamma (c + mk.1 + mk.2)) * x ^ mk.2) with hg
  have hrow (m : ℕ) : HasSum (fun k => g (m, k)) (poch p m * poch q m / m ! * x ^ m *
      regularizedGaussHGFun (s + m) r (c + m) x) :=
    (hasSum_regularizedGaussHGFun_coeff (s + m) r (c + m) hx).mul_left _
  set M : ℝ := ‖p‖ + ‖q‖ + ‖r‖ + ‖s‖ with hM
  have hM0 : 0 ≤ M := by positivity
  set C : ℝ := c.re with hC
  set P : ℝ → ℕ → ℝ := fun y n => (ascPochhammer ℝ n).eval y with hP
  set K : ℝ := ‖Gamma (C : ℂ)‖ / ‖Gamma c‖ with hK0
  set H : ℕ × ℕ → ℝ := fun mk => K * (P M mk.1 / mk.1 ! * (P M mk.2 / mk.2 !)) *
    (P M (mk.1 + mk.2) * ‖x‖ ^ (mk.1 + mk.2) * ‖Gamma ((C : ℂ) + ((mk.1 + mk.2 : ℕ) : ℂ))‖⁻¹)
    with hH
  have hPle {z : ℂ} (hz : ‖z‖ ≤ M) (n : ℕ) : ‖poch z n‖ ≤ P M n :=
    (norm_poch_le z n).trans (ascPochhammer_eval_mono (norm_nonneg z) hz n)
  have hPadd (m k : ℕ) : P M m * P (M + m) k = P M (m + k) := by
    apply Complex.ofReal_injective
    simp only [hP]
    push_cast
    rw [← ascPochhammer_eval_ofReal, ← ascPochhammer_eval_ofReal, ← ascPochhammer_eval_ofReal]
    have := poch_add (M : ℂ) m k
    simp only [poch] at this
    rw [this]; push_cast; ring
  have hP0 (y : ℝ) (hy : 0 ≤ y) (n : ℕ) : 0 ≤ P y n := ascPochhammer_eval_nonneg hy n
  have hH0 : ∀ mk, 0 ≤ H mk := fun mk => by
    simp only [hH]
    have a1 := hP0 M hM0 mk.1
    have a2 := hP0 M hM0 mk.2
    have a3 := hP0 M hM0 (mk.1 + mk.2)
    have hK0' : 0 ≤ K := by positivity
    have : 0 ≤ ‖Gamma ((C : ℂ) + ((mk.1 + mk.2 : ℕ) : ℂ))‖⁻¹ := by positivity
    have : 0 ≤ ‖x‖ ^ (mk.1 + mk.2) := by positivity
    have : (0 : ℝ) ≤ mk.1 ! := by positivity
    have : (0 : ℝ) ≤ mk.2 ! := by positivity
    apply mul_nonneg (mul_nonneg hK0' (mul_nonneg (div_nonneg a1 ‹_›) (div_nonneg a2 ‹_›)))
    exact mul_nonneg (mul_nonneg a3 ‹_›) ‹_›
  have hbound : ∀ mk, ‖g mk‖ ≤ H mk := by
    rintro ⟨m, k⟩
    simp only [hg, hH, norm_mul, norm_div, norm_pow, Complex.norm_natCast]
    have e1 := hPle (z := p) (by rw [hM]; linarith [norm_nonneg q, norm_nonneg r, norm_nonneg s]) m
    have e2 := hPle (z := q) (by rw [hM]; linarith [norm_nonneg p, norm_nonneg r, norm_nonneg s]) m
    have e3 := hPle (z := r) (by rw [hM]; linarith [norm_nonneg p, norm_nonneg q, norm_nonneg s]) k
    have e4 : ‖poch (s + m) k‖ ≤ P (M + m) k := by
      refine (norm_poch_le _ k).trans (ascPochhammer_eval_mono (norm_nonneg _) ?_ k)
      calc ‖s + m‖ ≤ ‖s‖ + ‖(m : ℂ)‖ := norm_add_le _ _
        _ ≤ M + m := by
          rw [Complex.norm_natCast, hM]; linarith [norm_nonneg p, norm_nonneg q, norm_nonneg r]
    have e5 := hypSV_norm_recip_Gamma_le hc (m + k)
    rw [← hC] at e5
    rw [show c + (m : ℂ) + (k : ℂ) = c + ((m + k : ℕ) : ℂ) by push_cast; ring]
    have q0 := hP0 M hM0 m
    have q1 := hP0 M hM0 k
    have q2 := hP0 (M + m) (by positivity) k
    have A1 : ‖poch p m‖ * ‖poch q m‖ * ‖poch (s + m) k‖ * ‖poch r k‖ ≤
        P M m * P M m * P (M + m) k * P M k :=
      mul_le_mul (mul_le_mul (mul_le_mul e1 e2 (norm_nonneg _) q0) e4 (norm_nonneg _)
        (mul_nonneg q0 q0)) e3 (norm_nonneg _) (mul_nonneg (mul_nonneg q0 q0) q2)
    have A2 := mul_le_mul A1 e5 (by positivity) (mul_nonneg (mul_nonneg (mul_nonneg q0 q0) q2) q1)
    have hX : 0 ≤ ‖x‖ ^ m * ‖x‖ ^ k / ((m ! : ℝ) * k !) := by positivity
    calc _ = ‖poch p m‖ * ‖poch q m‖ * ‖poch (s + m) k‖ * ‖poch r k‖ *
            ‖Gamma (c + ((m + k : ℕ) : ℂ))‖⁻¹ * (‖x‖ ^ m * ‖x‖ ^ k / ((m ! : ℝ) * k !)) := by
          ring
      _ ≤ P M m * P M m * P (M + m) k * P M k * (‖Gamma (C : ℂ)‖ / ‖Gamma c‖ *
            ‖Gamma ((C : ℂ) + ((m + k : ℕ) : ℂ))‖⁻¹) *
            (‖x‖ ^ m * ‖x‖ ^ k / ((m ! : ℝ) * k !)) := mul_le_mul_of_nonneg_right A2 hX
      _ = _ := by rw [← hPadd, pow_add]; ring
  have hHs : Summable H := by
    refine hypSV_summable_of_antidiag hH0 ?_
    have hT := summable_norm_regularizedGaussHGFun_term ((2 * M : ℝ) : ℂ) (M : ℂ) (C : ℂ)
      (z := ((‖x‖ : ℝ) : ℂ)) (by simpa using hx)
    refine (hT.mul_left K).congr fun N => ?_
    have hfib : ∑ mk ∈ antidiagonal N, H mk = K * (∑ mk ∈ antidiagonal N,
        P M mk.1 / mk.1 ! * (P M mk.2 / mk.2 !)) *
        (P M N * ‖x‖ ^ N * ‖Gamma ((C : ℂ) + (N : ℂ))‖⁻¹) := by
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun mk hmk => ?_
      rw [Finset.mem_antidiagonal] at hmk
      simp only [hH, hmk]
    rw [hfib, hypSV_real_vandermonde]
    simp only [norm_mul, norm_div, norm_pow, norm_inv, Complex.norm_natCast, Complex.norm_real,
      Real.norm_eq_abs, ascPochhammer_eval_ofReal, abs_norm, hP]
    rw [abs_of_nonneg (hP0 _ (by positivity) N), abs_of_nonneg (hP0 _ hM0 N),
      show M + M = 2 * M by ring]
    ring
  have hgs : Summable g := Summable.of_norm_bounded hHs hbound
  have h1 := hgs.hasSum.prod_fiberwise hrow
  have h2 := hypSV_hasSum_antidiag hgs
  have h3 : (fun N => ∑ mk ∈ antidiagonal N, g mk) =
      fun N => poch A N * poch B N / (N ! * Gamma (c + N)) * x ^ N := by
    funext N
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => g (i, j))]
    have e : ∀ m ∈ range (N + 1), g (m, N - m) = poch p m * poch q m / m ! *
        (poch (s + m) (N - m) * poch r (N - m) / (N - m)!) * ((Gamma (c + N))⁻¹ * x ^ N) := by
      intro m hm
      have hm' : m ≤ N := by simpa [Nat.lt_succ_iff] using hm
      simp only [hg]
      rw [show c + (m : ℂ) + ((N - m : ℕ) : ℂ) = c + N by push_cast [Nat.cast_sub hm']; ring,
        show x ^ N = x ^ m * x ^ (N - m) by rw [← pow_add, Nat.add_sub_cancel' hm']]
      ring
    rw [Finset.sum_congr rfl e, ← Finset.sum_mul, hK]
    ring
  rw [h3] at h2
  have h4 := hasSum_regularizedGaussHGFun_coeff A B c hx
  rw [h2.unique h4] at h1
  exact h1

/-- The Vandermonde coefficient identity behind the inner sum of 15.6.9. -/
theorem hypSV_coeff_inner (α u v : ℂ) (N : ℕ) :
    ∑ n ∈ range (N + 1), poch α n * poch u n / n ! *
      (poch (α + n) (N - n) * poch v (N - n) / (N - n)!) = poch α N * poch (u + v) N / N ! := by
  rw [poch_add_eq_sum u v N, Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn' : n ≤ N := by simpa [Nat.lt_succ_iff] using hn
  have hp := poch_add α n (N - n)
  rw [Nat.add_sub_cancel' hn'] at hp
  have hc := Nat.choose_mul_factorial_mul_factorial hn'
  have hc' : (N.choose n : ℂ) * n ! * (N - n)! = N ! := by exact_mod_cast hc
  have h1 : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have h2 : ((N - n)! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (N - n).factorial_ne_zero
  have h3 : (N.choose n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos hn').ne'
  rw [hp, ← hc']
  field_simp

/-- The Pfaff–Saalschütz coefficient identity behind the outer sum of 15.6.9, for all `l`. -/
theorem hypSV_coeff_outer (a b l : ℂ) (N : ℕ) :
    ∑ m ∈ range (N + 1), poch (l - a) m * poch (l - b) m / m ! *
      (poch (l + m) (N - m) * poch (a + b - l) (N - m) / (N - m)!) =
      poch a N * poch b N / N ! := by
  have hgen : ∀ l : ℂ, l ∈ (Set.range fun k : ℕ => -(k : ℂ))ᶜ →
      ∑ m ∈ range (N + 1), poch (l - a) m * poch (l - b) m / m ! *
        (poch (l + m) (N - m) * poch (a + b - l) (N - m) / (N - m)!) =
        poch a N * poch b N / N ! := by
    intro l hl
    have hl' : ∀ k : ℕ, l ≠ -(k : ℂ) := fun k hk => hl ⟨k, hk.symm⟩
    have h := regularized_saalschutz_convolution (l - a) (l - b) l N
    rw [show l - (l - a) - (l - b) = a + b - l by ring, show l - (l - a) = a by ring,
      show l - (l - b) = b by ring] at h
    have hΓN : Gamma (l + N) ≠ 0 := Gamma_ne_zero (not_neg_nat_add_nat hl' N)
    have hN : (N ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr N.factorial_ne_zero
    have h' := congrArg (· * Gamma (l + N)) h
    rw [show poch a N * poch b N / (N ! * Gamma (l + N)) * Gamma (l + N) =
      poch a N * poch b N / (N ! : ℂ) by field_simp] at h'
    rw [Finset.sum_mul] at h'
    rw [← h']
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm' : m ≤ N := by simpa [Nat.lt_succ_iff] using hm
    have hlm : ∀ k : ℕ, l + m ≠ -(k : ℂ) := not_neg_nat_add_nat hl' m
    have hG := Gamma_add_nat_div_Gamma_eq (n := N - m) (l + m) hlm
    rw [show l + (m : ℂ) + ((N - m : ℕ) : ℂ) = l + N by push_cast [Nat.cast_sub hm']; ring] at hG
    have hΓm : Gamma (l + m) ≠ 0 := Gamma_ne_zero hlm
    have hm0 : (m ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr m.factorial_ne_zero
    rw [div_eq_iff hΓm] at hG
    simp only [poch]
    rw [hG]
    field_simp
  have hdense : Dense (Set.range fun k : ℕ => -(k : ℂ))ᶜ :=
    (Set.countable_range _).dense_compl ℝ
  have hcont1 : Continuous fun l : ℂ => ∑ m ∈ range (N + 1), poch (l - a) m * poch (l - b) m /
      m ! * (poch (l + m) (N - m) * poch (a + b - l) (N - m) / (N - m)!) := by
    simp only [poch]
    have hp (n : ℕ) : Continuous fun z : ℂ => (ascPochhammer ℂ n).eval z :=
      (ascPochhammer ℂ n).continuous
    refine continuous_finsetSum _ fun m _ => ?_
    have := hp m; have := hp (N - m)
    fun_prop
  have := hcont1.ext_on hdense continuous_const (fun l hl => hgen l hl)
  exact congrFun this l

/-- Termwise integration of `w u ∑ cₙ vⁿ` over `[0,1]` for integrable `w`, continuous `u, v`
and `‖v‖ ≤ ρ` with `∑ ‖cₙ‖ ρⁿ < ∞`. -/
theorem hypSV_hasSum_integral {w u v S : ℝ → ℂ} {c : ℕ → ℂ} {ρ : ℝ}
    (hw : IntervalIntegrable w MeasureTheory.volume 0 1)
    (hu : ContinuousOn u (Set.Icc 0 1)) (hv : ContinuousOn v (Set.Icc 0 1))
    (hvρ : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖v t‖ ≤ ρ) (hc : Summable fun n => ‖c n‖ * ρ ^ n)
    (hS : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasSum (fun n => c n * v t ^ n) (S t)) :
    HasSum (fun n => ∫ t in (0 : ℝ)..1, w t * (u t * (c n * v t ^ n)))
      (∫ t in (0 : ℝ)..1, w t * (u t * S t)) := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hu
  have hB0 : 0 ≤ max B 0 := le_max_right _ _
  have hρ0 : ∀ n, 0 ≤ ‖c n‖ * ρ ^ n := fun n => by
    have := hvρ 0 ⟨le_refl _, zero_le_one⟩
    have : 0 ≤ ρ := (norm_nonneg _).trans this
    positivity
  have hFi (n : ℕ) : IntervalIntegrable (fun t => w t * (u t * (c n * v t ^ n)))
      MeasureTheory.volume 0 1 := by
    refine hw.mul_continuousOn ?_
    rw [Set.uIcc_of_le zero_le_one]
    exact hu.mul (continuousOn_const.mul (hv.pow n))
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun n t => ‖c n‖ * ρ ^ n * (max B 0 * ‖w t‖)) (fun n => (hFi n).def'.aestronglyMeasurable)
    (fun n => Filter.Eventually.of_forall fun t ht => ?_)
    (Filter.Eventually.of_forall fun t _ => hc.mul_right _)
    (by
      simp_rw [tsum_mul_right]
      exact (hw.norm.const_mul _).const_mul _)
    (Filter.Eventually.of_forall fun t ht => ?_)
  · rw [Set.uIoc_of_le zero_le_one] at ht
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
    have h1 : ‖u t‖ ≤ max B 0 := (hB t ht').trans (le_max_left _ _)
    have h2 : ‖v t‖ ^ n ≤ ρ ^ n := pow_le_pow_left₀ (norm_nonneg _) (hvρ t ht') n
    rw [norm_mul, norm_mul, norm_mul, norm_pow]
    calc ‖w t‖ * (‖u t‖ * (‖c n‖ * ‖v t‖ ^ n))
        ≤ ‖w t‖ * (max B 0 * (‖c n‖ * ρ ^ n)) := by gcongr
      _ = _ := by ring
  · rw [Set.uIoc_of_le zero_le_one] at ht
    exact ((hS t ⟨ht.1.le, ht.2⟩).mul_left (u t)).mul_left (w t)

/-- The inner Euler integral of 15.6.9 after expanding both series. -/
theorem hypSV_product_inner_term {α c d K : ℂ} {x : ℝ} (m n : ℕ) (hd : 0 < d.re)
    (hcd : 0 < (c - d).re) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    ∫ t in (0 : ℝ)..1, (t : ℂ) ^ (d + m - 1) * (1 - (t : ℂ)) ^ (c - d - 1) *
        (((1 - (x : ℂ) * t) ^ α)⁻¹ * (K * ((1 - (t : ℂ)) * x / (1 - (x : ℂ) * t)) ^ n)) =
      K * (x : ℂ) ^ n * (Gamma (d + m) * Gamma (c - d + n) *
        regularizedGaussHGFun (α + n) (d + m) (c + m + n) (x : ℂ)) := by
  have hxn : ‖(x : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0]; exact hx1
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hdm : 0 < (d + m).re := by
    have : (d + m).re = d.re + m := by simp
    rw [this]; linarith
  have hcdn' : 0 < (c - d + n).re := by
    have : (c - d + n).re = (c - d).re + n := by simp
    rw [this]; linarith
  have hcdn : 0 < (c + m + n - (d + m)).re := by
    rw [show c + m + n - (d + m) = c - d + n by ring]; exact hcdn'
  have hE := ordinaryHypergeometric_eq_integral (a := α + n) hdm hcdn hxn
  rw [show c + m + n - (d + m) = c - d + n by ring] at hE
  have hc0 : 0 < (c + m + n).re := by
    have : (c + m + n).re = (d + m).re + (c - d + n).re := by simp; ring
    rw [this]; exact add_pos hdm hcdn'
  have hcn : ∀ k : ℕ, c + m + n ≠ -(k : ℂ) := not_neg_nat_of_re_pos hc0
  have hg1 : Gamma (d + m) ≠ 0 := Gamma_ne_zero_of_re_pos hdm
  have hg2 : Gamma (c - d + n) ≠ 0 := Gamma_ne_zero_of_re_pos hcdn'
  have hg3 : Gamma (c + m + n) ≠ 0 := Gamma_ne_zero hcn
  rw [regularizedGaussHGFun_eq_div_Gamma hcn, hE]
  have hI : ∫ t in (0 : ℝ)..1, (t : ℂ) ^ (d + m - 1) * (1 - (t : ℂ)) ^ (c - d - 1) *
        (((1 - (x : ℂ) * t) ^ α)⁻¹ * (K * ((1 - (t : ℂ)) * x / (1 - (x : ℂ) * t)) ^ n)) =
      K * (x : ℂ) ^ n * ∫ t in (0 : ℝ)..1, (t : ℂ) ^ (d + m - 1) * (1 - (t : ℂ)) ^ (c - d + n - 1) *
        (1 - (x : ℂ) * t) ^ (-(α + n)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
    intro t ht
    have hpos : 0 < 1 - x * t := by nlinarith [ht.1, ht.2]
    have hX : (1 - (x : ℂ) * t) ≠ 0 := by
      rw [show (1 - (x : ℂ) * t) = ((1 - x * t : ℝ) : ℂ) by push_cast; ring]
      exact_mod_cast hpos.ne'
    have hT : (1 - (t : ℂ)) ≠ 0 := by
      intro h; have := congrArg re h; simp at this; linarith [ht.2]
    simp only
    rw [show c - d + n - 1 = (c - d - 1) + n by ring, cpow_add _ _ hT, cpow_natCast,
      show -(α + n) = -α + -(n : ℂ) by ring, cpow_add _ _ hX, cpow_neg, cpow_neg, cpow_natCast,
      div_pow, mul_pow]
    field_simp
  rw [hI]
  generalize (∫ t in (0 : ℝ)..1, (t : ℂ) ^ (d + m - 1) * (1 - (t : ℂ)) ^ (c - d + n - 1) *
        (1 - (x : ℂ) * t) ^ (-(α + n))) = J
  field_simp

@[dlmf 15.6.E9]
theorem product_integral {a b c d : ℂ} (l : ℂ) {x : ℝ}
    (hd : 0 < d.re) (hcd : 0 < (c - d).re) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    regularizedGaussHGFun a b c (x : ℂ) =
      ∫ t : ℝ in (0 : ℝ)..1,
        (t : ℂ) ^ (d - 1) * (1 - (t : ℂ)) ^ (c - d - 1) / (1 - (x : ℂ) * t) ^ (a + b - l) *
          regularizedGaussHGFun (l - a) (l - b) d ((x : ℂ) * t) *
          regularizedGaussHGFun (a + b - l) (l - d) (c - d) ((1 - (t : ℂ)) * x / (1 - (x : ℂ) * t)) := by
  set α := a + b - l with hα
  have hc0 : 0 < c.re := by
    rw [sub_re] at hcd; linarith
  have hxn : ‖(x : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0]; exact hx1
  set W : ℝ → ℂ := fun t => (1 - (t : ℂ)) * x / (1 - (x : ℂ) * t) with hW
  set h : ℝ → ℂ := fun t => ((1 - (x : ℂ) * t) ^ α)⁻¹ with hh
  set F2 := regularizedGaussHGFun α (l - d) (c - d) with hF2
  have hpos : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < 1 - x * t := fun t ht => by nlinarith [ht.1, ht.2]
  have hcast : ∀ t : ℝ, (1 - (x : ℂ) * t) = ((1 - x * t : ℝ) : ℂ) := fun t => by push_cast; ring
  have hX : ∀ t ∈ Set.Icc (0 : ℝ) 1, (1 - (x : ℂ) * t) ≠ 0 := fun t ht => by
    rw [hcast]; exact_mod_cast (hpos t ht).ne'
  have hWle : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖W t‖ ≤ x := fun t ht => by
    have hp := hpos t ht
    have hWr : W t = (((1 - t) * x / (1 - x * t) : ℝ) : ℂ) := by simp only [hW]; push_cast; ring
    rw [hWr, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by
      exact div_nonneg (mul_nonneg (sub_nonneg.2 ht.2) hx0) hp.le), div_le_iff₀ hp]
    nlinarith [mul_nonneg (mul_nonneg hx0 ht.1) (sub_nonneg.2 hx1.le)]
  have hWn : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖W t‖ < 1 := fun t ht => (hWle t ht).trans_lt hx1
  have hWc : ContinuousOn W (Set.Icc 0 1) := by
    refine ContinuousOn.div (by fun_prop) (by fun_prop) hX
  have hhc : ContinuousOn h (Set.Icc 0 1) := by
    refine ContinuousOn.inv₀ ?_ fun t ht => by
      rw [cpow_def_of_ne_zero (hX t ht)]; exact exp_ne_zero _
    refine ContinuousOn.cpow (by fun_prop) continuousOn_const fun t ht => ?_
    rw [hcast]; exact ofReal_mem_slitPlane.2 (hpos t ht)
  have hF2c : ContinuousOn (fun t => F2 (W t)) (Set.Icc 0 1) := fun t ht =>
    (differentiableAt_regularizedGaussHGFun _ _ _ (hWn t ht)).continuousAt.comp_continuousWithinAt
      (hWc t ht)
  have hsumm (p q r : ℂ) : Summable fun n : ℕ =>
      ‖poch p n * poch q n / (n ! * Gamma (r + n))‖ * x ^ n := by
    refine (summable_norm_regularizedGaussHGFun_term p q r hxn).congr fun n => ?_
    rw [show x ^ n = ‖(x : ℂ) ^ n‖ by
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0], ← norm_mul]
    congr 1
    simp only [poch]
    ring
  set cA : ℕ → ℂ := fun m => poch (l - a) m * poch (l - b) m / (m ! * Gamma (d + m)) with hcA
  set cB : ℕ → ℂ := fun n => poch α n * poch (l - d) n / (n ! * Gamma (c - d + n)) with hcB
  have hw0 := betaIntegral_convergent hd hcd
  -- Step 1: expand the first factor.
  have hS1 := hypSV_hasSum_integral (u := fun t => h t * F2 (W t)) (v := fun t => (x : ℂ) * t)
    (c := cA) (ρ := x) (S := fun t => regularizedGaussHGFun (l - a) (l - b) d ((x : ℂ) * t))
    hw0 (hhc.mul hF2c) (by fun_prop)
    (fun t ht => by
      rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hx0, abs_of_nonneg ht.1]
      nlinarith [ht.1, ht.2])
    (hsumm (l - a) (l - b) d)
    (fun t ht => hasSum_regularizedGaussHGFun_coeff (l - a) (l - b) d (by
      rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hx0, abs_of_nonneg ht.1]
      nlinarith [ht.1, ht.2]))
  have hR : (∫ t : ℝ in (0 : ℝ)..1,
        (t : ℂ) ^ (d - 1) * (1 - (t : ℂ)) ^ (c - d - 1) / (1 - (x : ℂ) * t) ^ α *
          regularizedGaussHGFun (l - a) (l - b) d ((x : ℂ) * t) * F2 (W t)) =
      ∫ t in (0 : ℝ)..1, (t : ℂ) ^ (d - 1) * (1 - (t : ℂ)) ^ (c - d - 1) *
        ((h t * F2 (W t)) * regularizedGaussHGFun (l - a) (l - b) d ((x : ℂ) * t)) := by
    congr 1; funext t; simp only [hh]; ring
  rw [hR]
  -- Step 2 and 3: each term.
  have hterm (m : ℕ) : (∫ t in (0 : ℝ)..1, (t : ℂ) ^ (d - 1) * (1 - (t : ℂ)) ^ (c - d - 1) *
      ((h t * F2 (W t)) * (cA m * ((x : ℂ) * t) ^ m))) =
      poch (l - a) m * poch (l - b) m / m ! * (x : ℂ) ^ m *
        regularizedGaussHGFun (l + m) α (c + m) (x : ℂ) := by
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hdm : 0 < (d + m).re := by
      have : (d + m).re = d.re + m := by simp
      rw [this]; linarith
    have hg1 : Gamma (d + m) ≠ 0 := Gamma_ne_zero_of_re_pos hdm
    have hm! : (m ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr m.factorial_ne_zero
    have h2 : (∫ t in (0 : ℝ)..1, (t : ℂ) ^ (d - 1) * (1 - (t : ℂ)) ^ (c - d - 1) *
        ((h t * F2 (W t)) * (cA m * ((x : ℂ) * t) ^ m))) =
        cA m * (x : ℂ) ^ m * ∫ t in (0 : ℝ)..1, (t : ℂ) ^ (d + m - 1) *
          (1 - (t : ℂ)) ^ (c - d - 1) * (h t * F2 (W t)) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
      intro t ht
      have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.1.ne'
      simp only
      rw [show d + m - 1 = (d - 1) + m by ring, cpow_add _ _ ht0, cpow_natCast, mul_pow]
      ring
    have hwm := betaIntegral_convergent hdm hcd
    have hS2 := hypSV_hasSum_integral (u := h) (v := W) (c := cB) (ρ := x)
      (S := fun t => F2 (W t)) hwm hhc hWc hWle (hsumm α (l - d) (c - d))
      (fun t ht => hasSum_regularizedGaussHGFun_coeff α (l - d) (c - d) (hWn t ht))
    have hcm : 0 < (c + m).re := by
      have : (c + m).re = c.re + m := by simp
      rw [this]; linarith
    have hGL := (hypSV_hasSum_shift_series α (l - d) (d + m) α (c + m) α ((l - d) + (d + m))
      hcm hxn (hypSV_coeff_inner α (l - d) (d + m))).mul_left (Gamma (d + m))
    have hS2' : HasSum (fun n : ℕ => Gamma (d + m) * (poch α n * poch (l - d) n / n ! *
        (x : ℂ) ^ n * regularizedGaussHGFun (α + n) (d + m) (c + m + n) (x : ℂ)))
        (∫ t in (0 : ℝ)..1, (t : ℂ) ^ (d + m - 1) * (1 - (t : ℂ)) ^ (c - d - 1) *
          (h t * F2 (W t))) := by
      refine hS2.congr_fun fun n => ?_
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hg2 : Gamma (c - d + n) ≠ 0 := Gamma_ne_zero_of_re_pos (by
        have : (c - d + n).re = (c - d).re + n := by simp
        rw [this]; linarith)
      have hn! : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
      have := hypSV_product_inner_term (α := α) (K := cB n) m n hd hcd hx0 hx1
      rw [this]
      simp only [hcB]
      field_simp
    rw [h2, hS2'.unique hGL, show l - d + (d + m) = l + m by ring,
      regularizedGaussHGFun_symm α (l + m)]
    simp only [hcA]
    field_simp
  have hOut := hypSV_hasSum_shift_series (l - a) (l - b) α l c a b hc0 hxn
    (hypSV_coeff_outer a b l)
  rw [funext hterm] at hS1
  exact (hS1.unique hOut).symm

end hypSVProduct

end DLMF.Hypergeometric
