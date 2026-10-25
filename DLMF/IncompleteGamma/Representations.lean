/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.IncompleteGamma.SpecialValues
public import DLMF.IncompleteGamma.SeriesRecurrences
public import DLMF.Confluent.Integrals
public import DLMF.Bessel.Elementary
public import DLMFMathlib.Analysis.Complex.BarnesResidue
public import DLMFMathlib.Analysis.Integral.PrincipalValue

/-!
# Real, contour and Mellin–Barnes representations, DLMF §8.6

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
New theorem statements are initially admitted and are not completed proofs.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Confluent

open DLMF.Statistical

/-- Termwise evaluation of `∫_{-π}^{π} e^{iaθ + z e^{iθ}} dθ`. -/
lemma hasSum_integral_exp_circle {a : ℂ} (ha : ∀ n : ℕ, a ≠ -n) (z : ℂ) :
    HasSum (fun n : ℕ => 2*sin (π*a)*((-z)^n/((n.factorial : ℂ)*(a+n))))
      (∫ θ : ℝ in (-π)..π, exp (a*I*θ+z*exp (I*θ))) := by
  set F : ℕ → ℝ → ℂ := fun n θ => exp (a*I*θ)*((z*exp (I*θ))^n/(n.factorial : ℂ))
  have hF : ∀ n, Continuous (F n) := fun n => by fun_prop
  have hnorm : ∀ n θ, ‖F n θ‖ = ‖exp (a*I*θ)‖*(‖z‖^n/(n.factorial : ℝ)) := by
    intro n θ
    simp only [F, norm_mul, norm_div, norm_pow, Complex.norm_natCast]
    rw [show I*(θ:ℂ) = (θ:ℂ)*I by ring, norm_exp_ofReal_mul_I, mul_one]
  have hsum := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume)
    (a := -π) (b := π) (F := F) (f := fun θ : ℝ => exp (a*I*θ+z*exp (I*θ)))
    (fun n θ => ‖exp (a*I*θ)‖*(‖z‖^n/(n.factorial : ℝ)))
    (fun n => (hF n).aestronglyMeasurable)
    (fun n => Eventually.of_forall fun θ _ => (hnorm n θ).le)
    (Eventually.of_forall fun θ _ => (Real.summable_pow_div_factorial ‖z‖).mul_left _)
    (by
      have : (fun t : ℝ => ∑' n : ℕ, ‖exp (a*I*t)‖*(‖z‖^n/(n.factorial : ℝ))) =
          fun t : ℝ => ‖exp (a*I*(t:ℂ))‖*Real.exp ‖z‖ := by
        funext t
        rw [tsum_mul_left, Real.exp_eq_exp_ℝ, ← NormedSpace.expSeries_div_hasSum_exp ‖z‖ |>.tsum_eq]
      rw [this]
      exact (by fun_prop : Continuous fun t : ℝ => ‖exp (a*I*(t:ℂ))‖*Real.exp ‖z‖).intervalIntegrable _ _)
    (Eventually.of_forall fun θ _ => by
      have h : HasSum (fun n : ℕ => (z*exp (I*θ))^n/(n.factorial : ℂ)) (exp (z*exp (I*θ))) := by
        simpa only [Complex.exp_eq_exp_ℂ] using NormedSpace.expSeries_div_hasSum_exp (z*exp (I*θ))
      simpa only [F, Complex.exp_add] using h.mul_left (exp (a*I*θ)))
  refine hsum.congr_fun fun n => ?_
  have han : a + n ≠ 0 := fun h => ha n (by linear_combination h)
  have hc : I*(a+n) ≠ 0 := mul_ne_zero I_ne_zero han
  have hint : (∫ θ : ℝ in (-π)..π, F n θ) =
      z^n/(n.factorial : ℂ) * ∫ θ : ℝ in (-π)..π, exp (I*(a+n)*θ) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [F]
    rw [mul_pow, ← Complex.exp_nat_mul, show I*(a+n)*(θ:ℂ) = a*I*θ + n*(I*θ) by ring,
      Complex.exp_add]
    ring
  rw [hint, integral_exp_mul_complex hc]
  have hs : sin (π*(a+n)) = (-1)^n*sin (π*a) := by
    rw [mul_add, show (π:ℂ)*n = n*π by ring, Complex.sin_antiperiodic.add_nat_mul_eq n]
  have hsin : exp (I*(a+n)*π) - exp (I*(a+n)*(-π:ℝ)) = 2*I*sin (π*(a+n)) := by
    rw [Complex.sin, ofReal_neg]
    ring_nf
    rw [I_sq]
    ring_nf
  rw [hsin, hs, neg_pow]
  field_simp

/-- lowerIncGamma trigonometric integral. -/
@[dlmf 8.6.E1]
theorem lowerIncGamma_trigonometric_integral {a : ℂ} (ha : ∀ n : ℤ, a ≠ n) (z : ℂ) :
    lowerIncGamma a z=z^a/sin (π*a)*(∫ t : ℝ in 0..π, exp (z*Real.cos t)*cos (a*t+z*Real.sin t)) := by
  have ha' : ∀ n : ℕ, a ≠ -n := fun n h => ha (-n) (by push_cast; exact h)
  have hsin : sin (π*a) ≠ 0 := by
    rw [Complex.sin_ne_zero_iff]
    intro k hk
    exact ha k (by
      have hπ : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
      field_simp at hk
      linear_combination hk)
  set G : ℝ → ℂ := fun θ => exp (a*I*θ+z*exp (I*θ))
  have hGc : Continuous G := by fun_prop
  have heq : (∫ t : ℝ in 0..π, exp (z*Real.cos t)*cos (a*t+z*Real.sin t)) =
      (1/2) * ∫ θ : ℝ in (-π)..π, G θ := by
    have h1 : (∫ t : ℝ in 0..π, exp (z*Real.cos t)*cos (a*t+z*Real.sin t)) =
        ∫ t : ℝ in 0..π, (1/2)*(G t + G (-t)) := by
      refine intervalIntegral.integral_congr fun t _ => ?_
      have hp : exp (I*(t:ℂ)) = Real.cos t + Real.sin t * I := by
        rw [show I*(t:ℂ) = t*I by ring, exp_mul_I, ← ofReal_cos, ← ofReal_sin]
      have hn : exp (I*((-t:ℝ):ℂ)) = Real.cos t - Real.sin t * I := by
        rw [show I*((-t:ℝ):ℂ) = ((-t:ℝ):ℂ)*I by ring, exp_mul_I, ← ofReal_cos, ← ofReal_sin,
          Real.cos_neg, Real.sin_neg, ofReal_neg]
        ring
      have e1 : G t = exp (z*Real.cos t) * exp ((a*t+z*Real.sin t)*I) := by
        simp only [G, hp]; rw [← Complex.exp_add]; congr 1; ring
      have e2 : G (-t) = exp (z*Real.cos t) * exp (-((a*t+z*Real.sin t)*I)) := by
        simp only [G, hn]; rw [← Complex.exp_add]; congr 1; push_cast; ring
      rw [e1, e2, Complex.cos]
      ring
    have hGi : ∀ c d : ℝ, IntervalIntegrable G volume c d := fun c d => hGc.intervalIntegrable c d
    have hGn : IntervalIntegrable (fun x => G (-x)) volume 0 π :=
      (hGc.comp continuous_neg).intervalIntegrable 0 π
    rw [h1, intervalIntegral.integral_const_mul, intervalIntegral.integral_add (hGi 0 π) hGn,
      intervalIntegral.integral_comp_neg,
      neg_zero, add_comm, intervalIntegral.integral_add_adjacent_intervals (hGi _ _) (hGi _ _)]
  rw [heq, ← (hasSum_integral_exp_circle ha' z).tsum_eq, tsum_mul_left,
    lowerIncGamma_eq_regularized ha', regularizedConfluent_self_succ_neg,
    ← (scIncGamma_hasSum_alternating ha' z).tsum_eq]
  have hG := Gamma_ne_zero ha'
  have hT : (∑' k : ℕ, (-z)^k/(Gamma a*(k.factorial : ℂ)*(a+k))) =
      (∑' k : ℕ, (-z)^k/((k.factorial : ℂ)*(a+k)))/Gamma a := by
    rw [← tsum_div_const]
    congr 1; funext k; field_simp
  rw [hT]
  set T := ∑' k : ℕ, (-z)^k/((k.factorial : ℂ)*(a+k))
  field_simp

/-- `(t z)^w = t^w z^w` for real `t > 0` and `z ≠ 0`. -/
lemma lgJ_ofReal_mul_cpow {t : ℝ} (ht : 0 < t) {z : ℂ} (hz : z ≠ 0) (w : ℂ) :
    ((t : ℂ) * z) ^ w = (t : ℂ) ^ w * z ^ w := by
  have htz : (t : ℂ) * z ≠ 0 := mul_ne_zero (by exact_mod_cast ht.ne') hz
  rw [cpow_def_of_ne_zero htz, cpow_def_of_ne_zero (by exact_mod_cast ht.ne'),
    cpow_def_of_ne_zero hz, log_ofReal_mul ht hz, ← Complex.exp_add, ofReal_log ht.le]
  ring_nf

/-- `‖Γ(a+1)‖ Γ(σ+1+k) ≤ ‖Γ(a+1+k)‖ Γ(σ+1)` for `σ = Re a > 0`. -/
lemma lgJ_norm_Gamma_ge {a : ℂ} (ha : 0 < a.re) (k : ℕ) :
    ‖Gamma (a + 1)‖ * Real.Gamma (a.re + 1 + k) ≤ ‖Gamma (a + 1 + k)‖ * Real.Gamma (a.re + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hne : a + 1 + k ≠ 0 := by
      intro h; have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
    have hpos : 0 < a.re + 1 + k := by positivity
    rw [show a + 1 + ((k + 1 : ℕ) : ℂ) = (a + 1 + k) + 1 by push_cast; ring, Gamma_add_one _ hne,
      show a.re + 1 + ((k + 1 : ℕ) : ℝ) = (a.re + 1 + k) + 1 by push_cast; ring,
      Real.Gamma_add_one hpos.ne', norm_mul]
    have hre : a.re + 1 + k ≤ ‖a + 1 + k‖ := by
      have := re_le_norm (a + 1 + k); simpa using this
    have hG : 0 ≤ Real.Gamma (a.re + 1) := (Real.Gamma_pos_of_pos (by linarith)).le
    calc ‖Gamma (a + 1)‖ * ((a.re + 1 + k) * Real.Gamma (a.re + 1 + k))
        = (a.re + 1 + k) * (‖Gamma (a + 1)‖ * Real.Gamma (a.re + 1 + k)) := by ring
      _ ≤ (a.re + 1 + k) * (‖Gamma (a + 1 + k)‖ * Real.Gamma (a.re + 1)) :=
          mul_le_mul_of_nonneg_left ih hpos.le
      _ ≤ ‖a + 1 + k‖ * (‖Gamma (a + 1 + k)‖ * Real.Gamma (a.re + 1)) :=
          mul_le_mul_of_nonneg_right hre (by positivity)
      _ = _ := by ring

/-- lowerIncGamma besselJ integral. -/
@[dlmf 8.6.E2]
theorem lowerIncGamma_besselJ_integral {a : ℂ} (ha : 0 < a.re) {z : ℂ} (hz : z ∈ slitPlane) :
    lowerIncGamma a z=z^(a/2)*(∫ t : ℝ in Ioi 0, exp (-t : ℂ)*(t : ℂ)^(a/2-1)*besselJ a (2*(z*t)^(1/2 : ℂ))) := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have ha' : ∀ n : ℕ, a ≠ -n := fun n h => by
    have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  set c : ℕ → ℂ := fun k => regularizedHGFunCoeff 0 {a + 1} k with hc
  have hck : ∀ k : ℕ, c k = 1 / (k ! * Gamma (a + 1 + k)) := fun k => by
    simp [hc, regularizedHGFunCoeff]
  set F : ℕ → ℝ → ℂ := fun k t => z ^ (a / 2) * (c k * (-z) ^ k) *
    (((Real.exp (-t) : ℝ) : ℂ) * (t : ℂ) ^ (a + k - 1)) with hF
  -- pointwise expansion
  have hpt : ∀ t : ℝ, 0 < t → exp (-t : ℂ)*(t : ℂ)^(a/2-1)*besselJ a (2*(z*t)^(1/2 : ℂ)) =
      ∑' k : ℕ, F k t := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    set u : ℂ := (z * t) ^ (1 / 2 : ℂ) with hu
    have hu2 : u ^ 2 = z * t := by
      rw [hu, show (1 / 2 : ℂ) = ((2 : ℕ) : ℂ)⁻¹ by norm_num]
      exact cpow_nat_inv_pow _ (by norm_num)
    have hzt : z * t ≠ 0 := mul_ne_zero hz0 ht0
    have hua : u ^ a = (t : ℂ) ^ (a / 2) * z ^ (a / 2) := by
      have harg1 := neg_pi_lt_arg (z * t)
      have harg2 := arg_le_pi (z * t)
      have him : (log (z * t) * (1 / 2 : ℂ)).im = arg (z * t) / 2 := by
        simp [log_im]; ring
      rw [hu, ← cpow_mul _ (by rw [him]; linarith [Real.pi_pos])
        (by rw [him]; linarith [Real.pi_pos]), mul_comm z, lgJ_ofReal_mul_cpow ht hz0]
      ring_nf
    have hJ : besselJ a (2 * u) = u ^ a * ∑' k : ℕ, c k * (-(z * t)) ^ k := by
      rw [besselJ, show 2 * u / 2 = u by ring, regularizedHGFun_eq_tsum, hu2]
    have hpow : (t : ℂ) ^ (a / 2 - 1) * (t : ℂ) ^ (a / 2) = (t : ℂ) ^ (a - 1) := by
      rw [← cpow_add _ _ ht0]; ring_nf
    have hpowk : ∀ k : ℕ, (t : ℂ) ^ (a + k - 1) = (t : ℂ) ^ (a - 1) * (t : ℂ) ^ k := by
      intro k
      rw [show a + k - 1 = (a - 1) + k by ring, cpow_add _ _ ht0, cpow_natCast]
    rw [hJ, hua, ← tsum_mul_left, ← tsum_mul_left]
    refine tsum_congr fun k => ?_
    simp only [hF, hpowk, Complex.ofReal_exp, Complex.ofReal_neg]
    rw [← hpow]
    ring
  set σ : ℝ := a.re
  have hre : ∀ k : ℕ, 0 < (a + k).re := fun k => by
    simp only [add_re, natCast_re]; positivity
  have hint : ∀ k : ℕ, Integrable (F k) (volume.restrict (Ioi 0)) := fun k => by
    have := (GammaIntegral_convergent (hre k)).const_mul (z ^ (a / 2) * (c k * (-z) ^ k))
    simpa [hF] using this
  have hnorm : ∀ k : ℕ, (∫ t in Ioi 0, ‖F k t‖) =
      ‖z ^ (a / 2) * (c k * (-z) ^ k)‖ * Real.Gamma (σ + k) := by
    intro k
    have hσk : 0 < σ + k := by have := hre k; simpa using this
    rw [Real.Gamma_eq_integral hσk, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := ht
    simp only [hF, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    simp [σ]
  have hGa : 0 < ‖Gamma (a + 1)‖ := norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos (by
    simp only [add_re, one_re]; linarith))
  set M : ℝ := ‖z ^ (a / 2)‖ * Real.Gamma (σ + 1) / (‖Gamma (a + 1)‖ * σ)
  have hbound : ∀ k : ℕ, ‖z ^ (a / 2) * (c k * (-z) ^ k)‖ * Real.Gamma (σ + k) ≤
      M * (‖z‖ ^ k / k !) := by
    intro k
    have hGk : 0 < ‖Gamma (a + 1 + k)‖ := norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos (by
      simp only [add_re, one_re, natCast_re]; positivity))
    have hσk : 0 < σ + k := by have := hre k; simpa using this
    have hGσ : 0 < Real.Gamma (σ + k) := Real.Gamma_pos_of_pos hσk
    have h1 := lgJ_norm_Gamma_ge ha k
    rw [show σ + 1 + (k : ℝ) = (σ + k) + 1 by ring, Real.Gamma_add_one hσk.ne'] at h1
    have h2 : ‖Gamma (a + 1)‖ * σ * Real.Gamma (σ + k) ≤
        ‖Gamma (a + 1 + k)‖ * Real.Gamma (σ + 1) := by
      refine le_trans ?_ h1
      have : σ ≤ σ + k := by linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
      have := mul_le_mul_of_nonneg_left this (le_of_lt hGa)
      nlinarith
    rw [norm_mul, norm_mul, hck, norm_div, norm_one, norm_mul, norm_pow, norm_neg,
      Complex.norm_natCast]
    have hf : (0 : ℝ) < k ! := by exact_mod_cast Nat.factorial_pos k
    simp only [M]
    rw [div_mul_div_comm, mul_comm (‖Gamma (a + 1)‖ * σ)]
    rw [show ‖z ^ (a / 2)‖ * (1 / (↑k ! * ‖Gamma (a + 1 + ↑k)‖) * ‖z‖ ^ k) * Real.Gamma (σ + k)
        = ‖z ^ (a / 2)‖ * ‖z‖ ^ k * Real.Gamma (σ + k) / (↑k ! * ‖Gamma (a + 1 + ↑k)‖) by
      field_simp]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hzn : 0 ≤ ‖z ^ (a / 2)‖ * ‖z‖ ^ k := by positivity
    calc ‖z ^ (a / 2)‖ * ‖z‖ ^ k * Real.Gamma (σ + k) * (↑k ! * (‖Gamma (a + 1)‖ * σ))
        = ‖z ^ (a / 2)‖ * ‖z‖ ^ k * ↑k ! * (‖Gamma (a + 1)‖ * σ * Real.Gamma (σ + k)) := by ring
      _ ≤ ‖z ^ (a / 2)‖ * ‖z‖ ^ k * ↑k ! * (‖Gamma (a + 1 + k)‖ * Real.Gamma (σ + 1)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = _ := by ring
  have hsum : Summable fun k : ℕ => ∫ t in Ioi 0, ‖F k t‖ := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun t => norm_nonneg _)
      (fun k => (hnorm k).trans_le (hbound k)) ((Real.summable_pow_div_factorial ‖z‖).mul_left M)
  have key := integral_tsum_of_summable_integral_norm hint hsum
  have hFk : ∀ k : ℕ, (∫ t in Ioi 0, F k t) = z ^ (a / 2) * ((-z) ^ k / (k ! * (a + k))) := by
    intro k
    have hne : a + k ≠ 0 := fun h => by have := hre k; rw [h] at this; simp at this
    simp only [hF]
    rw [integral_const_mul, ← GammaIntegral, ← Gamma_eq_integral (hre k), hck,
      show a + 1 + (k : ℂ) = (a + k) + 1 by ring, Gamma_add_one _ hne]
    have hG := Complex.Gamma_ne_zero_of_re_pos (hre k)
    have hf : ((k ! : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    field_simp
  have hI : (∫ t : ℝ in Ioi 0, exp (-t : ℂ)*(t : ℂ)^(a/2-1)*besselJ a (2*(z*t)^(1/2 : ℂ))) =
      ∫ t : ℝ in Ioi 0, ∑' k : ℕ, F k t :=
    setIntegral_congr_fun measurableSet_Ioi fun t ht => hpt t ht
  rw [hI, ← key, tsum_congr hFk, tsum_mul_left, ← mul_assoc, ← cpow_add _ _ hz0, add_halves,
    lowerIncGamma_eq_regularized ha', regularizedConfluent_self_succ_neg,
    ← (scIncGamma_hasSum_alternating ha' z).tsum_eq]
  have hG := Gamma_ne_zero ha'
  have hT : (∑' k : ℕ, (-z)^k/(Gamma a*(k ! : ℂ)*(a+k))) =
      (∑' k : ℕ, (-z)^k/((k ! : ℂ)*(a+k)))/Gamma a := by
    rw [← tsum_div_const]
    congr 1; funext k; field_simp
  rw [hT]
  field_simp

/-- `(e^x)^w = e^{xw}` for real `x`. -/
lemma ofReal_exp_cpow_eq_exp_mul (x : ℝ) (w : ℂ) : ((Real.exp x : ℝ) : ℂ)^w = exp (x*w) := by
  rw [ofReal_exp, cpow_def_of_ne_zero (Complex.exp_ne_zero _), log_exp (by simp [Real.pi_pos])
    (by simp [Real.pi_pos.le])]

/-- lowerIncGamma logarithmic integral. -/
@[dlmf 8.6.E3]
theorem lowerIncGamma_logarithmic_integral {a : ℂ} (ha : 0 < a.re) {z : ℂ} (hz : z ≠ 0) :
    lowerIncGamma a z=z^a*(∫ t : ℝ in Ioi 0, exp (-a*t-z*Real.exp (-t))) := by
  have ha' : ∀ k : ℕ, a ≠ -k := fun k hk => by
    have := congrArg Complex.re hk
    simp at this
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hk := regularizedConfluent_kummer_transform a (a+1) (-z)
  rw [show a+1-a=1 by ring, neg_neg] at hk
  have hsc : regularizedHGFun {a} {a+1} (-z) = scIncGamma a z := by
    rw [hk, scIncGamma]
  rw [lowerIncGamma_eq_regularized ha', hsc, scIncGamma_integral ha]
  have hG := Gamma_ne_zero ha'
  rw [show Gamma a * z^a * (1/Gamma a * ∫ t : ℝ in 0..1, (t : ℂ)^(a-1)*exp (-z*t)) =
    z^a * ∫ t : ℝ in 0..1, (t : ℂ)^(a-1)*exp (-z*t) by field_simp]
  congr 1
  set g : ℝ → ℂ := fun s => (s : ℂ)^(a-1)*exp (-z*s)
  have hneg := integral_comp_neg_Ioi 0 (fun x : ℝ => Real.exp x • g (Real.exp x))
  have himg := integral_image_eq_integral_abs_deriv_smul (s := Iio (0:ℝ)) (f := Real.exp)
    measurableSet_Iio (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    Real.exp_injective.injOn g
  rw [Real.image_exp_Iio, Real.exp_zero] at himg
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo, himg,
    ← integral_Iic_eq_integral_Iio]
  simp_rw [abs_of_pos (Real.exp_pos _)]
  rw [neg_zero] at hneg
  rw [← hneg]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [g, Complex.real_smul]
  rw [ofReal_exp_cpow_eq_exp_mul, ofReal_exp, ← Complex.exp_add]
  push_cast
  rw [← Complex.exp_add]
  congr 1
  ring

/-- upperIncGamma stieltjes integral. -/
@[dlmf 8.6.E4]
theorem upperIncGamma_stieltjes_integral {a : ℂ} (ha : a.re < 1) {z : ℂ} (hz : z ∈ slitPlane) :
    upperIncGamma a z=z^a*exp (-z)/Gamma (1-a)*(∫ t : ℝ in Ioi 0, (t : ℂ)^(-a)*exp (-t : ℂ)/(z+t)) := by
  -- Tricomi's Stieltjes representation 13.4.5 at `a = b = 1 - a`, where `U(0,b,t) = 1`.
  have h := kummerU_stieltjes (a := 1 - a) (b := 1 - a) hz (by simp) (by simp; linarith)
  rw [upperIncGamma, h, show 1 - (1 - a) = a by ring, show (1 : ℂ) + (1 - a) - (1 - a) = 1 by ring,
    show (1 - a) - (1 - a) = (0 : ℂ) by ring, show (1 - a) - 1 = -a by ring, Gamma_one, mul_one]
  have hi : (∫ t : ℝ in Ioi 0, kummerU 0 (1 - a) t * exp (-(t : ℂ)) * (t : ℂ) ^ (-a) /
      ((t : ℂ) + z)) = ∫ t : ℝ in Ioi 0, (t : ℂ)^(-a)*exp (-t : ℂ)/(z+t) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [kummerU_zero, add_comm (t : ℂ) z]; ring
  rw [hi]; ring

/-- upperIncGamma laplace integral complex. -/
@[dlmf 8.6.E5]
theorem upperIncGamma_laplace_integral_complex (a : ℂ) {z : ℂ} (hz : 0 < z.re) :
    upperIncGamma a z=z^a*exp (-z)*(∫ t : ℝ in Ioi 0, exp (-z*t)*(1+(t : ℂ))^(a-1)) := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero (Or.inl hz)
  rw [upperIncGamma_eq_cpow_mul_kummerU a hz0, kummerU_laplace (by norm_num) hz, Gamma_one,
    div_one, one_mul]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [sub_self, cpow_zero, mul_one, show a+1-1-1 = a-1 by ring]

/-- upperIncGamma besselK integral. -/
@[dlmf 8.6.E6]
theorem upperIncGamma_besselK_integral {a : ℂ} (ha : a.re < 1) {z : ℂ} (hz : z ∈ slitPlane) :
    upperIncGamma a z=2*z^(a/2)*exp (-z)/Gamma (1-a)*(∫ t : ℝ in Ioi 0, exp (-t : ℂ)*(t : ℂ)^(-a/2)*DLMF.Bessel.besselK a (2*(z*t)^(1/2 : ℂ))) := by
  -- DLMF 13.4.7 at `a = b = 1 - a`, with `K_{-a} = K_a`.
  have h := kummerU_eq_integral_besselK (a := 1 - a) (b := 1 - a) hz (by simp) (by simp; linarith)
  rw [show (1 - (1 - a)) / 2 = a / 2 by ring, show 1 - a - (1 - a) + 1 = (1 : ℂ) by ring,
    show 1 - a - (1 - a) / 2 - 1 / 2 = -a / 2 by ring, show 1 - a - 1 = -a by ring,
    Gamma_one, mul_one] at h
  have hi : (∫ t : ℝ in Ioi 0, exp (-(t : ℂ)) * (t : ℂ) ^ (-a / 2) *
      DLMF.Bessel.besselK (-a) (2 * (z * t) ^ (1 / 2 : ℂ))) =
      ∫ t : ℝ in Ioi 0, exp (-t : ℂ)*(t : ℂ)^(-a/2)*DLMF.Bessel.besselK a (2*(z*t)^(1/2 : ℂ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [DLMF.Bessel.besselK_neg a (two_mul_cpow_half_mem_slitPlane hz ht)]
  rw [upperIncGamma, h, hi]
  ring

/-- upperIncGamma logarithmic integral. -/
@[dlmf 8.6.E7]
theorem upperIncGamma_logarithmic_integral (a : ℂ) {z : ℂ} (hz : 0 < z.re) :
    upperIncGamma a z=z^a*(∫ t : ℝ in Ioi 0, exp (a*t-z*Real.exp t)) := by
  rw [upperIncGamma_laplace_integral_complex a hz, mul_assoc]
  congr 1
  have hshift := setIntegral_Ioi_comp_add_right
    (fun s : ℝ => exp (-z*(s-1))*(s:ℂ)^(a-1)) 0 1
  simp only [zero_add] at hshift
  have h1 : (∫ t : ℝ in Ioi 0, exp (-z*t)*(1+(t : ℂ))^(a-1)) =
      ∫ s : ℝ in Ioi 1, exp (-z*((s:ℂ)-1))*(s:ℂ)^(a-1) := by
    rw [← hshift]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    push_cast; ring_nf
  have h2 := integral_comp_exp_Ioi (fun s : ℝ => exp (-z*((s:ℂ)-1))*(s:ℂ)^(a-1)) 0
  rw [Real.exp_zero] at h2
  rw [h1, ← h2, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [Complex.real_smul]
  rw [ofReal_exp_cpow_eq_exp_mul, ofReal_exp, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  ring

/-- lowerIncGamma circle integral. -/
@[dlmf 8.6.E8]
theorem lowerIncGamma_circle_integral {a : ℂ} (ha : ∀ n : ℤ, a ≠ n) {z : ℂ} (hz : z ≠ 0) :
    lowerIncGamma a z = -I*z^a/(2*sin (π*a))*(∫ θ : ℝ in (-π)..π, I*exp (a*I*θ+z*exp (I*θ))) := by
  have ha' : ∀ n : ℕ, a ≠ -n := fun n h => ha (-n) (by push_cast; exact h)
  have hsin : sin (π*a) ≠ 0 := by
    rw [Complex.sin_ne_zero_iff]
    intro k hk
    exact ha k (by
      have hπ : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
      field_simp at hk
      linear_combination hk)
  rw [intervalIntegral.integral_const_mul, ← (hasSum_integral_exp_circle ha' z).tsum_eq,
    tsum_mul_left, lowerIncGamma_eq_regularized ha', regularizedConfluent_self_succ_neg,
    ← (scIncGamma_hasSum_alternating ha' z).tsum_eq]
  have hG := Gamma_ne_zero ha'
  have hT : (∑' k : ℕ, (-z)^k/(Gamma a*(k.factorial : ℂ)*(a+k))) =
      (∑' k : ℕ, (-z)^k/((k.factorial : ℂ)*(a+k)))/Gamma a := by
    rw [← tsum_div_const]
    congr 1; funext k; field_simp
  rw [hT]
  set T := ∑' k : ℕ, (-z)^k/((k.factorial : ℂ)*(a+k))
  field_simp
  ring_nf
  rw [I_sq]
  ring

/-- Symmetric principal value underlying the indented contour of 8.6.9. -/
def upperGammaIndentPV (a z : ℂ) : ℂ :=
  limUnder (𝓝[>] (0 : ℝ)) (fun ε => (∫ t : ℝ in 0..(1-ε), (t : ℂ)^a*exp (-z*t)/(t-1)) + improperAtTop (fun t : ℝ => (t : ℂ)^a*exp (-z*t)/(t-1)) (1+ε))

/-- A symmetric principal value on `[a, ∞)` at `c` exists when `f t - A/(t - c)` is integrable
near `c` and `f` is integrable on every half-line `(d, ∞)`, `d > c`. -/
lemma ugPV_hasPrincipalValueIoi {f : ℝ → ℂ} {a b c : ℝ} (A : ℂ) (hac : a < c) (hcb : c < b)
    (hsub : IntegrableOn (fun t => f t - A / (t - c)) (Icc a b))
    (htail : ∀ d : ℝ, c < d → IntegrableOn f (Ioi d)) :
    HasPrincipalValueIoi f a c
      ((∫ t in a..b, (f t - A / (t - c))) + A * Real.log ((b - c) / (c - a)) +
        ∫ t in Ioi b, f t) := by
  have hI : ∀ d : ℝ, c < d → HasIntegralAtTop f d (∫ t in Ioi d, f t) := fun d hd =>
    intervalIntegral_tendsto_integral_Ioi d (htail d hd) tendsto_id
  have himp : ∀ d : ℝ, c < d → improperAtTop f d = ∫ t in Ioi d, f t := fun d hd =>
    (hI d hd).limUnder_eq
  refine ⟨hac, fun ε hε => ?_, ?_⟩
  · rw [himp _ (by linarith)]; exact hI _ (by linarith)
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (∫ t in a..c - ε, f t) + improperAtTop f (c + ε) =
      ((∫ t in a..c - ε, f t) + ∫ t in c + ε..b, f t) + ∫ t in Ioi b, f t := by
    filter_upwards [Ioo_mem_nhdsGT (sub_pos.mpr hcb)] with ε hε
    have hd : c < c + ε := by linarith [hε.1]
    have hdb : c + ε ≤ b := by linarith [hε.2]
    have hfi : IntervalIntegrable f volume (c + ε) b :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hdb).mpr
        ((htail _ hd).mono_set Ioc_subset_Ioi_self)
    have hloc : ∀ R, b ≤ R → IntervalIntegrable f volume b R := fun R hR =>
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hR).mpr
        ((htail _ (by linarith)).mono_set Ioc_subset_Ioi_self)
    have h := pv_tendsto_intervalIntegral_atTop_of_le (hI b hcb) hfi hloc
    rw [himp _ hd, tendsto_nhds_unique
      (intervalIntegral_tendsto_integral_Ioi _ (htail _ hd) tendsto_id) h]
    ring
  exact ((pv_tendsto_of_integrableOn_sub A hac hcb hsub).add_const _).congr'
    (EventuallyEq.symm hev)

/-- upperGammaIndentPV converges. -/
@[dlmf 8.6.E9]
theorem upperGammaIndentPV_converges {a z : ℂ} (ha : -1 < a.re) (hz : 0 < z.re) :
    HasPrincipalValueIoi (fun t : ℝ => (t : ℂ)^a*exp (-z*t)/(t-1)) 0 1 (upperGammaIndentPV a z) := by
  set g : ℝ → ℂ := fun t => (t : ℂ)^a*exp (-z*t)
  have hgi : IntegrableOn g (Icc 0 2) := by
    have h1 := intervalIntegral.intervalIntegrable_cpow' (a := 0) (b := 2) ha
    have h2 : IntervalIntegrable g volume 0 2 :=
      h1.mul_continuousOn (Continuous.continuousOn (by fun_prop))
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mp h2
  have hgd : DifferentiableAt ℝ g 1 := by
    have h1 : DifferentiableAt ℝ (fun t : ℝ => (t : ℂ)^a) 1 := by
      have h := (hasDerivAt_id ((1 : ℝ) : ℂ)).cpow_const (c := a) (by simp)
      exact (h.comp_ofReal (z := 1)).differentiableAt
    exact h1.mul (by fun_prop)
  have hsub : IntegrableOn (fun t : ℝ => (t : ℂ)^a*exp (-z*t)/(t-1) - g 1 / (t - 1))
      (Icc 0 2) := pv_integrableOn_sub_of_differentiableAt (c := 1) hgi hgd
  have htail : ∀ d : ℝ, 1 < d → IntegrableOn (fun t : ℝ => (t : ℂ)^a*exp (-z*t)/(t-1)) (Ioi d) := by
    intro d hd
    have hb := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) ha (by norm_num) hz
    have hb' : IntegrableOn (fun t : ℝ => t ^ a.re * Real.exp (-z.re * t) / (d - 1)) (Ioi d) :=
      IntegrableOn.congr_fun ((hb.mono_set (Ioi_subset_Ioi (by linarith))).div_const (d - 1))
        (fun t _ => by simp [Real.rpow_one]) measurableSet_Ioi
    refine hb'.mono' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
      have ht0 : 0 < t := by linarith [mem_Ioi.mp ht]
      refine ContinuousAt.continuousWithinAt (ContinuousAt.div ?_ (by fun_prop) ?_)
      · refine ContinuousAt.mul ?_ (by fun_prop)
        exact (continuousAt_ofReal_cpow_const _ _ (Or.inr ht0.ne'))
      · intro h; have := congrArg re h; simp at this; linarith [mem_Ioi.mp ht]
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => ?_)
      have ht0 : 0 < t := by linarith [mem_Ioi.mp ht]
      have ht1 : d - 1 ≤ t - 1 := by linarith [mem_Ioi.mp ht]
      rw [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.norm_exp,
        show ((t : ℂ) - 1) = ((t - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by linarith)]
      simp only [neg_mul, Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero]
      exact div_le_div_of_nonneg_left (by positivity) (by linarith) ht1
  have h := ugPV_hasPrincipalValueIoi (g 1) (by norm_num : (0:ℝ) < 1) (by norm_num : (1:ℝ) < 2)
    hsub htail
  refine ⟨h.1, h.2.1, ?_⟩
  have hl := h.2.2
  have hv : upperGammaIndentPV a z = limUnder (𝓝[>] (0:ℝ)) (fun ε =>
      (∫ t in (0:ℝ)..1-ε, (t : ℂ)^a*exp (-z*t)/(t-1)) +
        improperAtTop (fun t : ℝ => (t : ℂ)^a*exp (-z*t)/(t-1)) (1+ε)) := rfl
  rw [hv, hl.limUnder_eq]
  exact hl

/-- upperIncGamma indented integral. -/
@[dlmf 8.6.E9]
theorem upperIncGamma_indented_integral {a z : ℂ} (ha : -1 < a.re) (hz : 0 < z.re) {ε : ℝ} (hε : ε=1 ∨ ε = -1) :
    upperIncGammaOnLog (-a) (log z+ε*π*I)=exp z*exp (-ε*π*I*a)/Gamma (1+a)*(upperGammaIndentPV a z-ε*π*I*exp (-z)) := by
  sorry


/-- The Mellin–Barnes integrand `Γ(s+a) z^{-s}/s`, `s = c+iy`, of DLMF 8.6.11. -/
noncomputable def upperIncGammaMBIntegrand (a z : ℂ) (c y : ℝ) : ℂ :=
  Gamma ((c+y*I)+a)*z^(-((c:ℂ)+y*I))/((c:ℂ)+y*I)

/-- The Mellin–Barnes integrand is continuous in `y`. -/
lemma continuous_upperIncGammaMBIntegrand (a : ℂ) {z : ℂ} (hz : z ≠ 0) {c : ℝ} (hc : 0 < c)
    (hca : 0 < c+a.re) : Continuous (upperIncGammaMBIntegrand a z c) := by
  refine continuous_iff_continuousAt.mpr fun y => ?_
  unfold upperIncGammaMBIntegrand
  refine ContinuousAt.div (ContinuousAt.mul ?_ ?_) (by fun_prop) ?_
  · exact (DLMF.Gamma.continuousAt_Gamma_of_re_pos (by simp; linarith)).comp (by fun_prop)
  · exact (Continuous.const_cpow (f := fun y : ℝ => -((c:ℂ)+y*I)) (by fun_prop) (Or.inl hz)).continuousAt
  · intro h; have := congrArg re h; simp at this; linarith

/-- Uniform bound for the Mellin–Barnes integrand on `‖z‖ ≥ ρ`, `|arg z| ≤ θ`. -/
lemma norm_upperIncGammaMBIntegrand_le (a : ℂ) {c : ℝ} (hc : 0 < c) (hca : 0 < c+a.re) :
    ∃ C : ℝ, ∃ K : ℕ, ∀ {ρ θ : ℝ}, 0 < ρ → ∀ z : ℂ, ρ ≤ ‖z‖ → |arg z| ≤ θ → ∀ y : ℝ,
      ‖upperIncGammaMBIntegrand a z c y‖ ≤
        C * ρ ^ (-c) / c * ((1 + |y|) ^ K * Real.exp (-((π/2-θ) * |y|))) := by
  obtain ⟨C, K, hC⟩ := DLMF.Gamma.exists_norm_Gamma_shift_le hca a.im
  refine ⟨C, K, fun {ρ θ} hρ z hzρ hθ y => ?_⟩
  have hz : z ≠ 0 := norm_pos_iff.mp (hρ.trans_le hzρ)
  have e : ((c:ℂ)+y*I)+a = ((c + a.re : ℝ) : ℂ) + I * ((a.im : ℂ) + (y : ℂ)) := by
    apply Complex.ext <;> simp; ring
  have h1 := hC y; rw [← e] at h1
  have h2 : ‖z^(-((c:ℂ)+y*I))‖ ≤ ρ ^ (-c) * Real.exp (θ * |y|) := by
    rw [norm_cpow_of_ne_zero hz]
    simp only [neg_re, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, add_zero, neg_im, add_im, mul_im, zero_add]
    rw [div_eq_mul_inv, ← Real.exp_neg]
    refine mul_le_mul (Real.rpow_le_rpow_of_nonpos hρ hzρ (by linarith)) (Real.exp_le_exp.mpr ?_)
      (by positivity) (by positivity)
    calc -(arg z * -y) = arg z * y := by ring
      _ ≤ |arg z * y| := le_abs_self _
      _ = |arg z| * |y| := abs_mul _ _
      _ ≤ θ * |y| := by gcongr
  have h3 : ‖((c:ℂ)+y*I)‖⁻¹ ≤ 1/c := by
    rw [one_div]
    refine inv_anti₀ hc ?_
    have := Complex.abs_re_le_norm ((c:ℂ)+y*I)
    simp at this
    rwa [abs_of_pos hc] at this
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (by simpa using hC 0)
  unfold upperIncGammaMBIntegrand
  rw [div_eq_mul_inv, norm_mul, norm_mul, norm_inv]
  calc _ ≤ (C * (1 + |y|) ^ K * Real.exp (-(π * |y|) / 2)) * (ρ ^ (-c) * Real.exp (θ * |y|)) *
        (1/c) := by gcongr
    _ = _ := by
      have : Real.exp (-(π * |y|) / 2) * Real.exp (θ * |y|) = Real.exp (-((π/2-θ) * |y|)) := by
        rw [← Real.exp_add]; ring_nf
      rw [← this]; ring

/-- The Mellin–Barnes integrand is integrable for `Re z > 0`. -/
lemma integrable_upperIncGammaMBIntegrand (a : ℂ) {z : ℂ} (hz : 0 < z.re) {c : ℝ} (hc : 0 < c)
    (hca : 0 < c+a.re) : Integrable (upperIncGammaMBIntegrand a z c) := by
  obtain ⟨C, K, hCK⟩ := norm_upperIncGammaMBIntegrand_le a hc hca
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
  have hθ : |arg z| < π/2 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz)
  refine ((DLMF.Gamma.integrable_one_add_abs_pow_mul_exp_neg (c := π/2-|arg z|) (by linarith)
    K).const_mul (C * ‖z‖ ^ (-c) / c)).mono'
    (continuous_upperIncGammaMBIntegrand a hz0 hc hca).aestronglyMeasurable
    (Eventually.of_forall fun y => hCK (norm_pos_iff.mpr hz0) z le_rfl le_rfl y)

/-- The Mellin–Barnes integral is holomorphic in `z` on the right half-plane. -/
lemma differentiableOn_integral_upperIncGammaMBIntegrand (a : ℂ) {c : ℝ} (hc : 0 < c)
    (hca : 0 < c+a.re) :
    DifferentiableOn ℂ (fun z => ∫ y, upperIncGammaMBIntegrand a z c y) {z : ℂ | 0 < z.re} := by
  obtain ⟨C, K, hCK⟩ := norm_upperIncGammaMBIntegrand_le a hc hca
  have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
  refine Complex.differentiableOn_integral_of_locally_dominated hU (fun z hz => ?_) ?_ ?_
  · exact (continuous_upperIncGammaMBIntegrand a (fun h => by
      rw [h] at hz; simp at hz) hc hca).aestronglyMeasurable
  · refine Eventually.of_forall fun y z hz => ?_
    have hz' : z ∈ slitPlane := Or.inl hz
    unfold upperIncGammaMBIntegrand
    refine (DifferentiableAt.div_const (DifferentiableAt.const_mul ?_ _) _).differentiableWithinAt
    exact differentiableAt_id.cpow (differentiableAt_const _) hz'
  · intro z0 hz0
    have hz00 : z0 ≠ 0 := fun h => by rw [h] at hz0; simp at hz0
    have hθ : |arg z0| < π/2 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz0)
    obtain ⟨θ, hθ1, hθ2⟩ : ∃ θ : ℝ, |arg z0| < θ ∧ θ < π/2 := ⟨(|arg z0| + π/2)/2, by linarith, by linarith⟩
    have hρ : 0 < ‖z0‖/2 := by have := norm_pos_iff.mpr hz00; linarith
    have harg : ∀ᶠ z in 𝓝 z0, |arg z| < θ :=
      ((continuousAt_arg (Or.inl hz0)).abs).eventually_lt continuousAt_const hθ1
    have hnorm : ∀ᶠ z in 𝓝 z0, ‖z0‖/2 < ‖z‖ :=
      continuousAt_const.eventually_lt continuous_norm.continuousAt (by linarith)
    refine ⟨_, harg.and hnorm, fun y => C * (‖z0‖/2) ^ (-c) / c *
      ((1 + |y|) ^ K * Real.exp (-((π/2-θ) * |y|))), ?_, Eventually.of_forall fun y z hz =>
        hCK hρ z hz.2.le hz.1.le y⟩
    exact (DLMF.Gamma.integrable_one_add_abs_pow_mul_exp_neg (c := π/2-θ) (by linarith)
      K).const_mul _

/-- DLMF 8.6.11 for real `x > 0`, from the Barnes integral for `U` (DLMF 13.4.18). -/
lemma integral_upperIncGammaMBIntegrand_ofReal (a : ℂ) {x : ℝ} (hx : 0 < x) {c : ℝ} (hc : 0 < c)
    (hca : 0 < c+a.re) :
    ∫ y, upperIncGammaMBIntegrand a x c y = 2*π*upperIncGamma a x := by
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hB := kummerU_barnes_exp (a := 1-a) (b := 1-a) (σ := c+a.re) hx
    (by simp; linarith) hca
  set σ : ℝ := c+a.re with hσ
  set H : ℝ → ℂ := fun t => Gamma (σ + I*t) / (-a + σ + I*t) * (x:ℂ)^(-(σ + I*t)) with hH
  have hG : ∀ t : ℝ, Gamma (1 - a - 1 + σ + I * t) * Gamma (σ + I * t) /
      Gamma (1 - a + σ + I * t) * (x : ℂ) ^ (-(σ + I * t)) * I = H t * I := by
    intro t
    have hw : -a + σ + I*t ≠ 0 := fun h => by
      have := congrArg re h; simp [hσ] at this; linarith
    have hw' : Gamma (-a + σ + I*t) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp [hσ]; linarith)
    rw [show 1 - a - 1 + σ + I * t = -a + σ + I*t by ring,
      show 1 - a + σ + I * t = (-a + σ + I*t) + 1 by ring, Gamma_add_one _ hw, hH]
    field_simp
  rw [integral_congr_ae (ae_of_all _ hG), integral_mul_const] at hB
  have hshift : ∫ y, upperIncGammaMBIntegrand a x c y = ∫ y, (x:ℂ)^a * H (y + a.im) := by
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    have e1 : (σ:ℂ) + I*((y + a.im : ℝ) : ℂ) = ((c:ℂ)+y*I)+a := by
      apply Complex.ext <;> simp [hσ]
    have e2 : -a + (σ:ℂ) + I*((y + a.im : ℝ) : ℂ) = (c:ℂ)+y*I := by
      rw [add_assoc, e1]; ring
    simp only [hH, upperIncGammaMBIntegrand]
    rw [e2, e1, show -(((c:ℂ)+y*I)+a) = -((c:ℂ)+y*I) + -a by ring,
      cpow_add _ _ hx0, cpow_neg (x:ℂ) a]
    have hxa : (x:ℂ)^a ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hx0)
    field_simp
  rw [hshift, integral_const_mul, integral_add_right_eq_self (fun t => H t) a.im, upperIncGamma, hB]
  have hpi : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have he : exp (-(x:ℂ)) * exp x = 1 := by rw [← exp_add]; simp
  rw [show (1:ℂ) - (1 - a) = a by ring]
  field_simp
  linear_combination -((x:ℂ)^a * (∫ t, H t)) * he

/-- upperIncGamma mellinBarnes. -/
@[dlmf 8.6.E11]
theorem upperIncGamma_mellinBarnes (a : ℂ) {z : ℂ} (hz : 0 < z.re) {c : ℝ} (hc : 0 < c) (hca : 0 < c+a.re) :
    HasIntegralWholeLine (fun y : ℝ => let s : ℂ := c+y*I; Gamma (s+a)*z^(-s)/s) (2*π*upperIncGamma a z) := by
  set U : Set ℂ := {z : ℂ | 0 < z.re}
  have hUo : IsOpen U := isOpen_lt continuous_const continuous_re
  have hF := (differentiableOn_integral_upperIncGammaMBIntegrand a hc hca).analyticOnNhd hUo
  have hG : AnalyticOnNhd ℂ (fun z => 2*π*upperIncGamma a z) U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hUo
    unfold upperIncGamma
    exact ((differentiableAt_neg_iff.mpr differentiableAt_id |>.cexp).mul
      (differentiableAt_kummerU _ _ (Or.inl hz))).const_mul _ |>.differentiableWithinAt
  have h1 : (1:ℂ) ∈ U := by simp [U]
  have hfreq : ∃ᶠ w in 𝓝[≠] (1:ℂ), (∫ y, upperIncGammaMBIntegrand a w c y) = 2*π*upperIncGamma a w := by
    have hmap : Tendsto (fun x : ℝ => (x:ℂ)) (𝓝[≠] (1:ℝ)) (𝓝[≠] (1:ℂ)) := by
      have := continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin (s := {(1:ℝ)}ᶜ)
        (t := {(1:ℂ)}ᶜ) (x := 1) (fun x hx h => hx (by simp at h ⊢; exact_mod_cast h))
      simpa using this
    have hev : ∀ᶠ x : ℝ in 𝓝[≠] (1:ℝ), (∫ y, upperIncGammaMBIntegrand a (x:ℂ) c y) =
        2*π*upperIncGamma a x := by
      filter_upwards [nhdsWithin_le_nhds (lt_mem_nhds (show (0:ℝ) < 1 by norm_num))] with x hx
      exact integral_upperIncGammaMBIntegrand_ofReal a hx hc hca
    exact hmap.frequently hev.frequently
  have heq := hF.eqOn_of_preconnected_of_frequently_eq hG
    (convex_halfSpace_re_gt (0:ℝ)).isPreconnected h1 hfreq hz
  have hint := integrable_upperIncGammaMBIntegrand a hz hc hca
  have hfun : (fun y : ℝ => let s : ℂ := c+y*I; Gamma (s+a)*z^(-s)/s) =
      upperIncGammaMBIntegrand a z c := rfl
  rw [hfun]
  refine ⟨_, _, intervalIntegral_tendsto_integral_Iic 0 hint.integrableOn tendsto_id,
    intervalIntegral_tendsto_integral_Ioi 0 hint.integrableOn tendsto_id, ?_⟩
  rw [intervalIntegral.integral_Iic_add_Ioi hint.integrableOn hint.integrableOn]
  exact heq

/-! ### Tools for DLMF 8.6.10 -/

/-- The Mellin–Barnes integrand `Γ(s) z^{a-s}/(a-s)`, `s = c+iy`, of DLMF 8.6.10. -/
noncomputable def incRep_L (a z : ℂ) (c y : ℝ) : ℂ :=
  Gamma (c+y*I)/(a-(c+y*I))*z^(a-(c+y*I))

/-- A whole-line improper integral of an integrable function is its Lebesgue integral. -/
lemma incRep_integral_eq {f : ℝ → ℂ} {v : ℂ} (hf : Integrable f) (h : HasIntegralWholeLine f v) :
    ∫ y, f y = v := by
  obtain ⟨u, w, hu, hw, huw⟩ := h
  have hu' := tendsto_nhds_unique hu
    (intervalIntegral_tendsto_integral_Iic 0 hf.integrableOn tendsto_id)
  have hw' := tendsto_nhds_unique hw
    (intervalIntegral_tendsto_integral_Ioi 0 hf.integrableOn tendsto_id)
  rw [← huw, hu', hw', intervalIntegral.integral_Iic_add_Ioi hf.integrableOn hf.integrableOn]

/-- An integrable function has its Lebesgue integral as whole-line improper integral. -/
lemma incRep_hasIntegralWholeLine {f : ℝ → ℂ} (hf : Integrable f) :
    HasIntegralWholeLine f (∫ y, f y) :=
  ⟨_, _, intervalIntegral_tendsto_integral_Iic 0 hf.integrableOn tendsto_id,
    intervalIntegral_tendsto_integral_Ioi 0 hf.integrableOn tendsto_id,
    intervalIntegral.integral_Iic_add_Ioi hf.integrableOn hf.integrableOn⟩

/-- The 8.6.10 integrand is the negative of a shifted 8.6.11 integrand. -/
lemma incRep_L_eq_upper (a z : ℂ) (c y : ℝ) :
    incRep_L a z c y = -upperIncGammaMBIntegrand a z (c - a.re) (y - a.im) := by
  unfold incRep_L upperIncGammaMBIntegrand
  rw [show ((c - a.re : ℝ) : ℂ) + ((y - a.im : ℝ) : ℂ) * I = (c + y*I) - a by
    apply Complex.ext <;> simp, sub_add_cancel, neg_sub, ← neg_sub (c + y*I : ℂ) a, div_neg]
  ring

/-- DLMF 8.6.10 to the right of the pole: the line integral is `-2π Γ(a,z)`. -/
lemma incRep_integral_right {a z : ℂ} (hz : 0 < z.re) {c : ℝ} (hc : 0 < c) (hca : a.re < c) :
    Integrable (incRep_L a z c) ∧ ∫ y, incRep_L a z c y = -(2*π*upperIncGamma a z) := by
  have hc0 : 0 < c - a.re := by linarith
  have hca' : 0 < (c - a.re) + a.re := by linarith
  have hint := integrable_upperIncGammaMBIntegrand a hz hc0 hca'
  have hfun : incRep_L a z c = fun y => -upperIncGammaMBIntegrand a z (c - a.re) (y - a.im) :=
    funext fun y => incRep_L_eq_upper a z c y
  have hv := upperIncGamma_mellinBarnes a hz hc0 hca'
  have hv' : ∫ y, upperIncGammaMBIntegrand a z (c - a.re) y = 2*π*upperIncGamma a z :=
    incRep_integral_eq hint hv
  refine ⟨hfun ▸ (hint.comp_sub_right a.im).neg, ?_⟩
  rw [hfun, integral_neg, integral_sub_right_eq_self (fun y => upperIncGammaMBIntegrand a z (c - a.re) y) a.im, hv']

/-- Pointwise bound for the 8.6.10 integrand. -/
lemma incRep_norm_L_le (a : ℂ) {z : ℂ} (hz : z ≠ 0) (c y : ℝ) :
    ‖incRep_L a z c y‖ ≤ ‖Gamma (c+y*I)‖ * (‖z‖^(a.re - c) * Real.exp (|arg z| * |a.im|) *
      Real.exp (|arg z| * |y|)) / ‖a - (c+y*I)‖ := by
  unfold incRep_L
  have hre : (a - (c+y*I)).re = a.re - c := by simp
  have him : (a - (c+y*I)).im = a.im - y := by simp
  have hexp : (Real.exp (arg z * (a.im - y)))⁻¹ ≤
      Real.exp (|arg z| * |a.im|) * Real.exp (|arg z| * |y|) := by
    rw [← Real.exp_neg, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 : -(arg z * (a.im - y)) ≤ |arg z * (a.im - y)| := neg_le_abs _
    have h2 : |arg z * (a.im - y)| ≤ |arg z| * (|a.im| + |y|) := by
      rw [abs_mul]; gcongr; exact abs_sub _ _
    linarith
  rw [norm_mul, norm_div, norm_cpow_of_ne_zero hz, hre, him, div_eq_mul_inv (‖z‖^_)]
  calc ‖Gamma (c+y*I)‖ / ‖a - (c+y*I)‖ * (‖z‖^(a.re - c) * (Real.exp (arg z * (a.im - y)))⁻¹)
      ≤ ‖Gamma (c+y*I)‖ / ‖a - (c+y*I)‖ * (‖z‖^(a.re - c) *
          (Real.exp (|arg z| * |a.im|) * Real.exp (|arg z| * |y|))) := by gcongr
    _ = _ := by ring

/-- `|Γ(x+iy)| ≤ Γ(x)/Γ(x') |Γ(x'+iy)|` for `0 < x ≤ x'`. -/
lemma incRep_norm_Gamma_le {x x' : ℝ} (hx : 0 < x) (hxx : x ≤ x') (y : ℝ) :
    ‖Gamma (x + I*y)‖ ≤ Real.Gamma x / Real.Gamma x' * ‖Gamma (x' + I*y)‖ := by
  have hx' : 0 < x' := hx.trans_le hxx
  have h1 := DLMF.Gamma.norm_Gamma_sq_eq hx y
  have h2 := DLMF.Gamma.norm_Gamma_sq_eq hx' y
  have hP := DLMF.Gamma.gammaVertProd_anti hx hxx y
  have hP1 := DLMF.Gamma.one_le_gammaVertProd x' y
  have hG' := Real.Gamma_pos_of_pos hx'
  have hG := Real.Gamma_pos_of_pos hx
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero, mul_pow, h1, h2]
  calc Real.Gamma x ^ 2 / DLMF.Gamma.gammaVertProd x y
      ≤ Real.Gamma x ^ 2 / DLMF.Gamma.gammaVertProd x' y :=
        div_le_div_of_nonneg_left (by positivity) (by linarith) hP
    _ = _ := by field_simp

/-- `(1+u)^K e^{-bu} → 0`. -/
lemma incRep_tendsto_poly_exp {b : ℝ} (hb : 0 < b) (K : ℕ) :
    Tendsto (fun u : ℝ => (1 + u) ^ K * Real.exp (-(b * u))) atTop (𝓝 0) := by
  have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero K).comp
    ((tendsto_id.const_mul_atTop hb).comp (tendsto_atTop_add_const_left _ 1 tendsto_id))).const_mul
    ((b ^ K)⁻¹ * Real.exp b)
  rw [mul_zero] at h
  refine h.congr fun u => ?_
  simp only [Function.comp_def, id]
  rw [mul_pow, show -(b * (1 + u)) = -b + -(b*u) by ring, Real.exp_add, Real.exp_neg b]
  have : b ^ K ≠ 0 := by positivity
  field_simp

/-- The 8.6.10 integrand is integrable on every line `Re s = c > 0` missing the pole. -/
lemma incRep_integrable {a z : ℂ} (hz : 0 < z.re) {c : ℝ} (hc : 0 < c) (hca : c ≠ a.re) :
    Integrable (incRep_L a z c) := by
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
  have hθ : |arg z| < π/2 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz)
  obtain ⟨C, K, hC⟩ := DLMF.Gamma.exists_norm_Gamma_shift_le hc 0
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (by simpa using hC 0)
  set d : ℝ := |a.re - c| with hd
  have hd0 : 0 < d := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hca))
  have hne : ∀ y : ℝ, d ≤ ‖a - (c + y*I)‖ := fun y => by
    have := Complex.abs_re_le_norm (a - (c + y*I)); simpa [hd] using this
  have hcont : Continuous (incRep_L a z c) := by
    refine continuous_iff_continuousAt.mpr fun y => ?_
    unfold incRep_L
    refine ContinuousAt.mul (ContinuousAt.div ?_ (by fun_prop) ?_) ?_
    · exact (DLMF.Gamma.continuousAt_Gamma_of_re_pos (by simp [hc])).comp (by fun_prop)
    · intro h; have := hne y; rw [h, norm_zero] at this; linarith
    · exact (Continuous.const_cpow (f := fun y : ℝ => a - ((c:ℂ)+y*I)) (by fun_prop)
        (Or.inl hz0)).continuousAt
  set M : ℝ := C * (‖z‖^(a.re - c) * Real.exp (|arg z| * |a.im|)) / d
  refine ((DLMF.Gamma.integrable_one_add_abs_pow_mul_exp_neg (c := π/2-|arg z|) (by linarith)
    K).const_mul M).mono' hcont.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  have h1 := hC y
  rw [show ((c:ℝ):ℂ) + I * (((0:ℝ):ℂ) + (y:ℂ)) = c + y*I by push_cast; ring] at h1
  refine (incRep_norm_L_le a hz0 c y).trans ?_
  have hA : 0 ≤ ‖z‖^(a.re - c) * Real.exp (|arg z| * |a.im|) := by positivity
  calc ‖Gamma (c+y*I)‖ * (‖z‖^(a.re - c) * Real.exp (|arg z| * |a.im|) *
        Real.exp (|arg z| * |y|)) / ‖a - (c+y*I)‖
      ≤ (C * (1 + |y|) ^ K * Real.exp (-(π * |y|) / 2)) * (‖z‖^(a.re - c) *
          Real.exp (|arg z| * |a.im|) * Real.exp (|arg z| * |y|)) / d := by
        gcongr
        exact hne y
    _ = M * ((1 + |y|) ^ K * Real.exp (-((π/2 - |arg z|) * |y|))) := by
        have : Real.exp (-(π * |y|) / 2) * Real.exp (|arg z| * |y|) =
            Real.exp (-((π/2 - |arg z|) * |y|)) := by rw [← Real.exp_add]; ring_nf
        simp only [M]; rw [← this]; field_simp

/-- The 8.6.10 integrand in the residue-shift form `φ(s)/(s-a)`. -/
lemma incRep_L_eq_div (a z : ℂ) (x T : ℝ) :
    (-(Gamma ((x:ℂ)+T*I) * z^(a-((x:ℂ)+T*I)))) / ((x:ℂ)+T*I - a) = incRep_L a z x T := by
  unfold incRep_L; rw [neg_div, ← div_neg, neg_sub]; ring

open scoped Interval in
/-- Horizontal cross-sections of the 8.6.10 integrand vanish at `±i∞`. -/
lemma incRep_horizontal {a z : ℂ} (hz : 0 < z.re) {c c' : ℝ} (hc : 0 < c) (hcc : c ≤ c') :
    Tendsto (fun T : ℝ => ∫ x in c..c', (-(Gamma ((x:ℂ)+T*I) * z^(a-((x:ℂ)+T*I)))) /
      ((x:ℂ)+T*I - a)) atTop (𝓝 0) ∧
    Tendsto (fun T : ℝ => ∫ x in c..c', (-(Gamma ((x:ℂ)+T*I) * z^(a-((x:ℂ)+T*I)))) /
      ((x:ℂ)+T*I - a)) atBot (𝓝 0) := by
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
  have hθ : |arg z| < π/2 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz)
  have hc' : 0 < c' := hc.trans_le hcc
  obtain ⟨G, hG⟩ := (isCompact_Icc (a := c) (b := c')).exists_bound_of_continuousOn (f := Real.Gamma)
    (fun x hx => (Real.differentiableAt_Gamma (fun m h => by
      have : (0:ℝ) < x := hc.trans_le hx.1
      linarith [(m.cast_nonneg : (0:ℝ) ≤ m)])).continuousAt.continuousWithinAt)
  obtain ⟨C, K, hC⟩ := DLMF.Gamma.exists_norm_Gamma_le hc'
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (by simpa using hC 0)
  have hGc' := Real.Gamma_pos_of_pos hc'
  set A : ℝ := ‖z‖^(a.re - c) + ‖z‖^(a.re - c')
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hA : ∀ x ∈ Icc c c', ‖z‖^(a.re - x) ≤ A := by
    intro x hx
    rcases le_total 1 ‖z‖ with h1 | h1
    · have := Real.rpow_le_rpow_of_exponent_le h1 (show a.re - x ≤ a.re - c by linarith [hx.1])
      linarith [Real.rpow_nonneg hzn.le (a.re - c')]
    · have := Real.rpow_le_rpow_of_exponent_ge hzn h1 (show a.re - c' ≤ a.re - x by linarith [hx.2])
      linarith [Real.rpow_nonneg hzn.le (a.re - c)]
  set b : ℝ := π/2 - |arg z|
  have hb : 0 < b := by simp only [b]; linarith
  set K0 : ℝ := (c' - c) * (|G| / Real.Gamma c' * C * A * Real.exp (|arg z| * |a.im|))
  have key : ∀ T : ℝ, 1 ≤ |a.im - T| → ‖∫ x in c..c', (-(Gamma ((x:ℂ)+T*I) * z^(a-((x:ℂ)+T*I)))) /
      ((x:ℂ)+T*I - a)‖ ≤ K0 * ((1 + |T|) ^ K * Real.exp (-(b * |T|))) := by
    intro T hT
    have hpt : ∀ x ∈ Ι c c', ‖(-(Gamma ((x:ℂ)+T*I) * z^(a-((x:ℂ)+T*I)))) / ((x:ℂ)+T*I - a)‖ ≤
        |G| / Real.Gamma c' * C * A * Real.exp (|arg z| * |a.im|) *
          ((1 + |T|) ^ K * Real.exp (-(b * |T|))) := by
      intro x hx
      rw [uIoc_of_le hcc] at hx
      have hxI : x ∈ Icc c c' := ⟨hx.1.le, hx.2⟩
      have hx0 : 0 < x := hc.trans hx.1
      rw [incRep_L_eq_div]
      refine (incRep_norm_L_le a hz0 x T).trans ?_
      have hg1 : ‖Gamma ((x:ℂ)+T*I)‖ ≤ |G| / Real.Gamma c' * (C * (1 + |T|) ^ K *
          Real.exp (-(π * |T|) / 2)) := by
        rw [show (x:ℂ)+T*I = x + I*T by ring]
        refine (incRep_norm_Gamma_le hx0 hxI.2 T).trans ?_
        have hGx : Real.Gamma x ≤ |G| := by
          have := hG x hxI; rw [Real.norm_eq_abs] at this
          exact (le_abs_self _).trans (this.trans (le_abs_self G))
        gcongr
        exact hC T
      have hden : 1 ≤ ‖a - ((x:ℂ)+T*I)‖ := by
        have := Complex.abs_im_le_norm (a - ((x:ℂ)+T*I)); simp at this; linarith
      have hexp : Real.exp (-(π * |T|) / 2) * Real.exp (|arg z| * |T|) = Real.exp (-(b * |T|)) := by
        rw [← Real.exp_add]; simp only [b]; ring_nf
      calc ‖Gamma ((x:ℂ)+T*I)‖ * (‖z‖^(a.re - x) * Real.exp (|arg z| * |a.im|) *
            Real.exp (|arg z| * |T|)) / ‖a - ((x:ℂ)+T*I)‖
          ≤ ‖Gamma ((x:ℂ)+T*I)‖ * (‖z‖^(a.re - x) * Real.exp (|arg z| * |a.im|) *
            Real.exp (|arg z| * |T|)) := div_le_self (by positivity) hden
        _ ≤ (|G| / Real.Gamma c' * (C * (1 + |T|) ^ K * Real.exp (-(π * |T|) / 2))) *
            (A * Real.exp (|arg z| * |a.im|) * Real.exp (|arg z| * |T|)) := by
            gcongr
            · exact hA x hxI
        _ = _ := by rw [← hexp]; ring
    have := intervalIntegral.norm_integral_le_of_norm_le_const hpt
    rw [abs_of_nonneg (sub_nonneg.mpr hcc)] at this
    calc _ ≤ _ := this
      _ = K0 * ((1 + |T|) ^ K * Real.exp (-(b * |T|))) := by simp only [K0]; ring
  have hlim := incRep_tendsto_poly_exp hb K
  constructor
  · refine squeeze_zero_norm' ?_ (by simpa using (hlim.comp tendsto_abs_atTop_atTop).const_mul K0)
    filter_upwards [eventually_ge_atTop (a.im + 1)] with T hT
    exact key T (by rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith)
  · refine squeeze_zero_norm' ?_ (by simpa using (hlim.comp tendsto_abs_atBot_atTop).const_mul K0)
    filter_upwards [eventually_le_atBot (a.im - 1)] with T hT
    exact key T (by rw [abs_of_nonneg (by linarith)]; linarith)

/-- The value of the 8.6.10 line integral. -/
lemma incRep_integral_value {a z : ℂ} (ha : ∀ n : ℕ, a ≠ -n) (hz : 0 < z.re) {c : ℝ} (hc : 0 < c)
    (hca : c ≠ a.re) :
    ∫ y, incRep_L a z c y = 2*π*(lowerIncGamma a z-(if a.re < c then Gamma a else 0)) := by
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
  have hsum := lowerIncGamma_add_upperIncGamma ha hz0
  by_cases h : a.re < c
  · simp only [h, ↓reduceIte]
    have hR := (incRep_integral_right hz hc h).2
    linear_combination hR - 2*π*hsum
  · simp only [h, ↓reduceIte, sub_zero]
    have hlt : c < a.re := lt_of_le_of_ne (not_lt.mp h) hca
    set c' : ℝ := a.re + 1
    have hc' : 0 < c' := by simp only [c']; linarith
    have hR := incRep_integral_right hz hc' (show a.re < c' by simp only [c']; linarith)
    set Φ : ℂ → ℂ := fun s => -(Gamma s * z^(a-s)) with hΦdef
    have e : ∀ c0 : ℝ, (fun y : ℝ => Φ ((c0:ℂ) + y*I) / ((c0:ℂ)+y*I - a)) = incRep_L a z c0 :=
      fun c0 => funext fun y => incRep_L_eq_div a z c0 y
    have hΦ : DifferentiableOn ℂ Φ (re ⁻¹' Icc c c') := by
      intro s hs
      have hs0 : 0 < s.re := hc.trans_le hs.1
      refine DifferentiableAt.differentiableWithinAt ?_
      refine ((Complex.differentiableAt_Gamma s fun m hm => ?_).mul
        ((differentiableAt_const a).sub differentiableAt_id |>.const_cpow (Or.inl hz0))).neg
      have := congrArg re hm; simp at this; linarith [(m.cast_nonneg : (0:ℝ) ≤ m)]
    have hH := incRep_horizontal (a := a) hz hc (show c ≤ c' by simp only [c']; linarith)
    have hshift := Complex.barnesRes_vertical_shift (p := a) hlt
      (show a.re < c' by simp only [c']; linarith) hΦ
      (by rw [e c]; exact incRep_integrable hz hc hca) (by rw [e c']; exact hR.1) hH.1 hH.2
    rw [show (fun y : ℝ => Φ ((c':ℂ) + y*I) / ((c':ℂ)+y*I - a)) = incRep_L a z c' from e c',
      show (fun y : ℝ => Φ ((c:ℂ) + y*I) / ((c:ℂ)+y*I - a)) = incRep_L a z c from e c, hR.2] at hshift
    simp only [hΦdef, sub_self, cpow_zero, mul_one] at hshift
    linear_combination -hshift - 2*π*hsum

/-- The separating contour expressed by a vertical line and its crossed-pole residue. -/
@[dlmf 8.6.E10]
theorem lowerIncGamma_mellinBarnes {a z : ℂ} (ha : ∀ n : ℕ, a ≠ -n) (hz : 0 < z.re) {c : ℝ} (hc : 0 < c) (hca : c ≠ a.re) :
    HasIntegralWholeLine (fun y : ℝ => let s : ℂ := c+y*I; Gamma s/(a-s)*z^(a-s)) (2*π*(lowerIncGamma a z-(if a.re < c then Gamma a else 0))) := by
  have hfun : (fun y : ℝ => let s : ℂ := c+y*I; Gamma s/(a-s)*z^(a-s)) = incRep_L a z c := rfl
  rw [hfun, ← incRep_integral_value ha hz hc hca]
  exact incRep_hasIntegralWholeLine (incRep_integrable hz hc hca)

/-! ### Tools for DLMF 8.6.12 -/

/-- Uniform vertical bounds for `Γ` on a strip `|Re w| ≤ X`: with the factor `|sin(π Re w)|`
for all heights, and without it for `|Im w| ≥ 1`. -/
lemma incRep_Gamma_bound (X : ℝ) :
    ∃ C : ℝ, ∃ K : ℕ, 0 ≤ C ∧ ∀ x ∈ Icc (-X) X, ∀ y : ℝ,
      ‖Gamma (x + I*y)‖ * |Real.sin (π*x)| ≤ C * (1+|y|)^K * Real.exp (-(π*|y|)/2) ∧
      (1 ≤ |y| → ‖Gamma (x + I*y)‖ ≤ C * (1+|y|)^K * Real.exp (-(π*|y|)/2)) := by
  obtain ⟨C, K, hC⟩ := DLMF.Gamma.exists_norm_recip_Gamma_le (X+1)
  set C0 : ℝ := max C 0
  refine ⟨4*π*C0, K, by positivity, fun x hx y => ?_⟩
  set E : ℝ := Real.exp (π*|y|/2) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hE2 : Real.exp (π*|y|) = E*E := by rw [hE, ← Real.exp_add]; ring_nf
  have hEi : Real.exp (-(π*|y|)/2) = E⁻¹ := by rw [hE, ← Real.exp_neg]; ring_nf
  have hP : 0 ≤ (1+|y|)^K := by positivity
  have h1 : ‖(Gamma (1 - (x + I*y)))⁻¹‖ ≤ C0 * (1+|y|)^K * E := by
    have := hC (1-x) ⟨by linarith [hx.2], by linarith [hx.1]⟩ (-y)
    rw [show ((1-x:ℝ):ℂ) + I*((-y:ℝ):ℂ) = 1 - (x + I*y) by push_cast; ring, abs_neg] at this
    refine this.trans ?_
    gcongr
    exact le_max_left _ _
  have h2 := (Complex.barnesRes_norm_Gamma_mul_sin_le (x + I*y)).trans (mul_le_mul_of_nonneg_left h1 Real.pi_pos.le)
  have hw : (π:ℂ)*(x + I*y) = ((π*x:ℝ):ℂ) + ((π*y:ℝ):ℂ)*I := by push_cast; ring
  rw [hw] at h2
  have hcosh : E*E/2 ≤ Real.cosh (π*y) := by
    rw [← Real.cosh_abs, abs_mul, abs_of_pos Real.pi_pos, Real.cosh_eq, ← hE2]
    have := Real.exp_pos (-(π*|y|)); linarith
  have hG0 := norm_nonneg (Gamma (x + I*y))
  constructor
  · have hs := Complex.barnesRes_abs_sin_mul_cosh_le_norm_sin (π*x) (π*y)
    have h3 : ‖Gamma (x + I*y)‖ * |Real.sin (π*x)| * (E*E/2) ≤ π * (C0 * (1+|y|)^K * E) := by
      refine le_trans ?_ h2
      rw [mul_assoc]
      gcongr
      exact (mul_le_mul_of_nonneg_left hcosh (abs_nonneg _)).trans hs
    rw [hEi]
    rw [← le_div_iff₀ (by positivity)] at h3
    refine h3.trans ?_
    have e : π * (C0 * (1+|y|)^K * E) / (E*E/2) = 2*(π*C0*(1+|y|)^K*E⁻¹) := by field_simp
    have : 0 ≤ π*C0*(1+|y|)^K*E⁻¹ := by positivity
    rw [e]; linarith
  · intro hy
    have hs := Complex.barnesRes_abs_sinh_le_norm_sin (π*x) (π*y)
    have hsinh : E*E/4 ≤ |Real.sinh (π*y)| := by
      rw [Real.abs_sinh, abs_mul, abs_of_pos Real.pi_pos, Real.sinh_eq, ← hE2]
      have hu : π ≤ π*|y| := by nlinarith [Real.pi_pos]
      have h4 := Real.add_one_le_exp (π*|y|)
      have h5 : Real.exp (-(π*|y|)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos])
      nlinarith [Real.pi_gt_three]
    have h3 : ‖Gamma (x + I*y)‖ * (E*E/4) ≤ π * (C0 * (1+|y|)^K * E) := by
      refine le_trans ?_ h2
      gcongr
      exact hsinh.trans hs
    rw [hEi]
    rw [← le_div_iff₀ (by positivity)] at h3
    refine h3.trans (le_of_eq ?_)
    field_simp

/-- Vertical bound for `Γ` on a line `Re w = x` missing the poles. -/
lemma incRep_Gamma_bound_pt {x : ℝ} (hx : ∀ n : ℕ, x ≠ -n) :
    ∃ C : ℝ, ∃ K : ℕ, 0 ≤ C ∧ ∀ y : ℝ,
      ‖Gamma (x + I*y)‖ ≤ C * (1+|y|)^K * Real.exp (-(π*|y|)/2) := by
  by_cases hx0 : 0 < x
  · obtain ⟨C, K, h⟩ := DLMF.Gamma.exists_norm_Gamma_le hx0
    exact ⟨C, K, (norm_nonneg _).trans (by simpa using h 0), h⟩
  · push Not at hx0
    have hs := Complex.barnesRes_real_sin_ne_zero hx0 hx
    have hs0 : 0 < |Real.sin (π*x)| := abs_pos.mpr hs
    obtain ⟨C, K, hC0, h⟩ := incRep_Gamma_bound |x|
    refine ⟨C / |Real.sin (π*x)|, K, by positivity, fun y => ?_⟩
    have := (h x ⟨neg_abs_le x, le_abs_self x⟩ y).1
    rw [← le_div_iff₀ hs0] at this
    refine this.trans (le_of_eq ?_)
    field_simp

/-- The DLMF 8.6.12 integrand `Γ(s+1-a) π/sin(πs) e^{-sw}`. -/
def incRep_f (a w s : ℂ) : ℂ := Gamma (s+1-a)*π/Complex.sin (π*s)*exp (-s*w)

/-- Pointwise bound for the 8.6.12 integrand. -/
lemma incRep_norm_f_le {a w : ℂ} (x y : ℝ) {C S : ℝ} {K : ℕ} (hC : 0 ≤ C) (hS : 0 < S)
    (g : ‖Gamma ((x+1-a.re : ℝ) + I*(y - a.im : ℝ))‖ ≤
      C * (1+|y - a.im|)^K * Real.exp (-(π*|y - a.im|)/2))
    (gs : S * Real.exp (π*|y|) ≤ ‖Complex.sin (π*((x:ℂ) + y*I))‖) :
    ‖incRep_f a w (x + y*I)‖ ≤ C * (1+|a.im|)^K * Real.exp (π*|a.im|/2) * (π/S) *
      Real.exp (-(x*w.re)) * ((1+|y|)^K * Real.exp (-((3*π/2 - |w.im|)*|y|))) := by
  have e1 : (x:ℂ) + y*I + 1 - a = ((x+1-a.re : ℝ) : ℂ) + I*((y - a.im : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  have hp : (1 + |y - a.im|)^K ≤ (1+|a.im|)^K * (1+|y|)^K := by
    rw [← mul_pow]; gcongr
    have := abs_sub y a.im
    nlinarith [abs_nonneg a.im, abs_nonneg y]
  have he : Real.exp (-(π * |y - a.im|) / 2) ≤ Real.exp (π*|a.im|/2) * Real.exp (-(π*|y|)/2) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.mpr
    have := abs_sub_abs_le_abs_sub y a.im
    nlinarith [Real.pi_pos]
  have hE : ‖exp (-((x:ℂ) + y*I)*w)‖ ≤ Real.exp (-(x*w.re)) * Real.exp (|w.im| * |y|) := by
    rw [Complex.norm_exp, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : (-((x:ℂ) + y*I)*w).re = -(x*w.re) + y*w.im := by simp
    rw [this]
    have := neg_abs_le (y*w.im); have := le_abs_self (y*w.im)
    rw [abs_mul] at *; nlinarith [abs_nonneg y, abs_nonneg w.im]
  have hsin0 : 0 < ‖Complex.sin (π*((x:ℂ) + y*I))‖ :=
    lt_of_lt_of_le (by positivity) gs
  have hpis : ‖(π:ℂ) / Complex.sin (π*((x:ℂ) + y*I))‖ ≤ π/S * Real.exp (-(π*|y|)) := by
    rw [norm_div, norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, div_le_iff₀ hsin0]
    calc π = π/S * Real.exp (-(π*|y|)) * (S * Real.exp (π*|y|)) := by
          rw [show π/S * Real.exp (-(π*|y|)) * (S * Real.exp (π*|y|)) =
            π * (Real.exp (-(π*|y|)) * Real.exp (π*|y|)) * (S/S) by ring, ← Real.exp_add,
            neg_add_cancel, Real.exp_zero, div_self hS.ne']; ring
      _ ≤ _ := by gcongr
  unfold incRep_f
  rw [mul_div_assoc, norm_mul, norm_mul, e1]
  calc ‖Gamma (((x+1-a.re : ℝ) : ℂ) + I*((y - a.im : ℝ) : ℂ))‖ *
        ‖(π:ℂ) / Complex.sin (π*((x:ℂ) + y*I))‖ * ‖exp (-((x:ℂ) + y*I)*w)‖
      ≤ (C * ((1+|a.im|)^K * (1+|y|)^K) * (Real.exp (π*|a.im|/2) * Real.exp (-(π*|y|)/2))) *
          (π/S * Real.exp (-(π*|y|))) * (Real.exp (-(x*w.re)) * Real.exp (|w.im| * |y|)) := by
        gcongr
        exact g.trans (by gcongr)
    _ = C * (1+|a.im|)^K * Real.exp (π*|a.im|/2) * (π/S) * Real.exp (-(x*w.re)) *
          ((1+|y|)^K * (Real.exp (-(π*|y|)/2) * Real.exp (-(π*|y|)) * Real.exp (|w.im| * |y|))) := by
        ring
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; ring_nf

lemma incRep_f_differentiableAt {a w s : ℂ} (hs : Complex.sin (π*s) ≠ 0)
    (hA : ∀ m : ℕ, s+1-a ≠ -m) : DifferentiableAt ℂ (incRep_f a w) s := by
  unfold incRep_f
  exact ((((differentiableAt_Gamma _ hA).comp s (by fun_prop)).mul_const _).div
    ((Complex.differentiable_sin _).comp s (by fun_prop)) hs).mul (by fun_prop)

lemma incRep_f_differentiableAt_param {a w s : ℂ} (hA : ∀ m : ℕ, s+1-a ≠ -m) :
    DifferentiableAt ℂ (fun a => incRep_f a w s) a := by
  unfold incRep_f
  exact ((((differentiableAt_Gamma _ hA).comp a (by fun_prop)).mul_const _).div_const _).mul_const _

lemma incRep_f_differentiableAt_w {a w s : ℂ} : DifferentiableAt ℂ (fun w => incRep_f a w s) w := by
  unfold incRep_f; fun_prop

lemma incRep_ne_pole {a : ℂ} {x : ℝ} (hav : ∀ n : ℕ, a.re - 1 - n ≠ x) (y : ℝ) :
    ∀ m : ℕ, (x:ℂ) + y*I + 1 - a ≠ -m := fun m h => by
  have := congrArg re h; simp at this; exact hav m (by linarith)

lemma incRep_f_continuous {a w : ℂ} {c : ℝ} (hs : Real.sin (π*c) ≠ 0)
    (hav : ∀ n : ℕ, a.re - 1 - n ≠ c) : Continuous fun y : ℝ => incRep_f a w (c + y*I) :=
  continuous_iff_continuousAt.mpr fun y => by
    have h := (incRep_f_differentiableAt (w := w) (Complex.barnesRes_sin_ne_zero_of_re (by simpa using hs))
      (incRep_ne_pole hav y)).continuousAt
    exact h.comp (f := fun y : ℝ => (c:ℂ) + y*I) (by fun_prop)

/-- The 8.6.12 integrand is integrable on admissible lines. -/
lemma incRep_f_integrable {a w : ℂ} (hw : |w.im| < 3*π/2) {c : ℝ} (hs : Real.sin (π*c) ≠ 0)
    (hav : ∀ n : ℕ, a.re - 1 - n ≠ c) : Integrable fun y : ℝ => incRep_f a w (c + y*I) := by
  obtain ⟨C, K, hC, h⟩ := incRep_Gamma_bound_pt (x := c+1-a.re) (fun n h => hav n (by linarith))
  have hS : 0 < |Real.sin (π*c)|/2 := by positivity
  refine ((DLMF.Gamma.integrable_one_add_abs_pow_mul_exp_neg (c := 3*π/2 - |w.im|)
    (by linarith) K).const_mul _).mono' (incRep_f_continuous hs hav).aestronglyMeasurable
    (Eventually.of_forall fun y => incRep_norm_f_le c y hC hS (h _) (Complex.barnesRes_sin_lower_line c y))

open scoped Interval in
/-- Horizontal cross-sections of the 8.6.12 integrand vanish at `±i∞`. -/
lemma incRep_f_horizontal {a w : ℂ} (hw : |w.im| < 3*π/2) {c₁ c₂ : ℝ} (h12 : c₁ ≤ c₂) :
    Tendsto (fun T : ℝ => ∫ x in c₁..c₂, incRep_f a w (x + T*I)) atTop (𝓝 0) ∧
    Tendsto (fun T : ℝ => ∫ x in c₁..c₂, incRep_f a w (x + T*I)) atBot (𝓝 0) := by
  obtain ⟨C, K, hC, h⟩ := incRep_Gamma_bound (|c₁| + |c₂| + 1 + |a.re|)
  set b : ℝ := 3*π/2 - |w.im|
  have hb : 0 < b := by simp only [b]; linarith
  set M : ℝ := C * (1+|a.im|)^K * Real.exp (π*|a.im|/2) * (π/(1/4)) *
    Real.exp ((|c₁| + |c₂|) * |w.re|)
  have key : ∀ T : ℝ, 1 ≤ |T| → 1 ≤ |T - a.im| → ‖∫ x in c₁..c₂, incRep_f a w (x + T*I)‖ ≤
      (c₂ - c₁) * (M * ((1 + |T|) ^ K * Real.exp (-(b * |T|)))) := by
    intro T hT hTa
    have hpt : ∀ x ∈ Ι c₁ c₂, ‖incRep_f a w (x + T*I)‖ ≤
        M * ((1 + |T|) ^ K * Real.exp (-(b * |T|))) := by
      intro x hx
      rw [uIoc_of_le h12] at hx
      have hX : x + 1 - a.re ∈ Icc (-(|c₁| + |c₂| + 1 + |a.re|)) (|c₁| + |c₂| + 1 + |a.re|) := by
        have := abs_le.mp (le_refl |c₁|); have := abs_le.mp (le_refl |c₂|)
        have := abs_le.mp (le_refl |a.re|)
        constructor <;> linarith [hx.1, hx.2]
      refine (incRep_norm_f_le x T hC (by norm_num) ((h _ hX _).2 hTa)
        (Complex.barnesRes_sin_lower_far x hT)).trans ?_
      have hxw : Real.exp (-(x*w.re)) ≤ Real.exp ((|c₁| + |c₂|) * |w.re|) := by
        apply Real.exp_le_exp.mpr
        have h1 : |x| ≤ |c₁| + |c₂| := by
          rw [abs_le]; constructor <;> linarith [hx.1, hx.2, abs_le.mp (le_refl |c₁|),
            abs_le.mp (le_refl |c₂|)]
        have := neg_abs_le (x*w.re); rw [abs_mul] at this
        nlinarith [abs_nonneg w.re, abs_nonneg x]
      simp only [M, b]
      gcongr
    have := intervalIntegral.norm_integral_le_of_norm_le_const hpt
    rw [abs_of_nonneg (sub_nonneg.mpr h12)] at this
    linarith
  have hlim := Complex.barnesRes_tendsto_poly_exp hb K
  have l1 := ((hlim.comp tendsto_abs_atTop_atTop).const_mul M).const_mul (c₂ - c₁)
  have l2 := ((hlim.comp tendsto_abs_atBot_atTop).const_mul M).const_mul (c₂ - c₁)
  simp only [mul_zero] at l1 l2
  constructor
  · refine squeeze_zero_norm' ?_ l1
    filter_upwards [eventually_ge_atTop (|a.im| + 1)] with T hT
    have h0 := abs_nonneg a.im
    exact key T (by rw [abs_of_nonneg (by linarith)]; linarith) (by
      rw [abs_of_nonneg (by linarith [le_abs_self a.im])]; linarith [le_abs_self a.im])
  · refine squeeze_zero_norm' ?_ l2
    filter_upwards [eventually_le_atBot (-(|a.im| + 1))] with T hT
    have h0 := abs_nonneg a.im
    exact key T (by rw [abs_of_nonpos (by linarith)]; linarith) (by
      rw [abs_of_nonpos (by linarith [neg_abs_le a.im])]; linarith [neg_abs_le a.im])

/-- Shifting the 8.6.12 line when no pole lies in the closed strip. -/
lemma incRep_shift_none {a w : ℂ} (hw : |w.im| < 3*π/2) {c₁ c₂ : ℝ} (h12 : c₁ < c₂)
    (hsin : ∀ x ∈ Icc c₁ c₂, Real.sin (π*x) ≠ 0) (hno : ∀ n : ℕ, a.re - 1 - n ∉ Icc c₁ c₂) :
    (∫ y : ℝ, incRep_f a w (c₂ + y*I)) = ∫ y : ℝ, incRep_f a w (c₁ + y*I) := by
  have hav : ∀ c ∈ Icc c₁ c₂, ∀ n : ℕ, a.re - 1 - n ≠ c := fun c hcI n h => hno n (h ▸ hcI)
  obtain ⟨ht, hb⟩ := incRep_f_horizontal (a := a) hw h12.le
  have h1I : c₁ ∈ Icc c₁ c₂ := ⟨le_rfl, h12.le⟩
  have h2I : c₂ ∈ Icc c₁ c₂ := ⟨h12.le, le_rfl⟩
  refine Complex.barnesRes_vertical_shift_of_differentiableOn h12 (fun t htS => ?_)
    (incRep_f_integrable hw (hsin c₁ h1I) (hav c₁ h1I))
    (incRep_f_integrable hw (hsin c₂ h2I) (hav c₂ h2I)) ht hb
  have htS' : t.re ∈ Icc c₁ c₂ := htS
  refine (incRep_f_differentiableAt (Complex.barnesRes_sin_ne_zero_of_re (hsin _ htS')) fun m h => ?_
    ).differentiableWithinAt
  have := congrArg re h; simp at this
  exact hno m (by rw [show a.re - 1 - m = t.re by linarith]; exact htS')

/-- The residue of the 8.6.12 integrand at `s = a-1-n`. -/
def incRep_res (a w : ℂ) (n : ℕ) : ℂ :=
  (-1)^n/(n.factorial:ℂ) * (π/Complex.sin (π*(a-1-n))) * exp (-(a-1-n)*w)

/-- The removable-singularity form `(s - (a-1-n)) f(s)`. -/
def incRep_phi (a w : ℂ) (n : ℕ) (s : ℂ) : ℂ :=
  Gamma (s+1-a+n+1) / (∏ j ∈ Finset.range n, (s+1-a+j)) * (π/Complex.sin (π*s)) * exp (-s*w)

lemma incRep_phi_pole (a w : ℂ) (n : ℕ) : incRep_phi a w n (a-1-n) = incRep_res a w n := by
  unfold incRep_phi incRep_res
  have h1 : a-1-n+1-a+n+1 = (1:ℂ) := by ring
  have h2 : ∏ j ∈ Finset.range n, (a-1-n+1-a+(j:ℂ)) = (-1)^n * n.factorial := by
    rw [← Complex.barnesRes_prod_sub_nat n]; exact Finset.prod_congr rfl fun j _ => by ring
  rw [h1, h2, Gamma_one]
  have hinv : ((-1:ℂ)^n)⁻¹ = (-1)^n := by rw [← inv_pow, inv_neg, inv_one]
  rw [div_eq_mul_inv (1:ℂ), one_mul, mul_inv, hinv]
  ring

/-- `φ(s)/(s - p) = f(s)` away from the pole `p = a-1-n` and from the poles of index `< n`. -/
lemma incRep_phi_div {a w s : ℂ} {n : ℕ} (hs : s ≠ a-1-n)
    (hj : ∀ j : ℕ, j < n → s+1-a+j ≠ 0) :
    incRep_phi a w n s / (s - (a-1-n)) = incRep_f a w s := by
  have hn : s+1-a+n ≠ 0 := fun h => hs (by linear_combination h)
  have hall : ∀ j : ℕ, j ≤ n → s+1-a+j ≠ 0 := fun j hjn => by
    rcases lt_or_eq_of_le hjn with h | rfl
    · exact hj j h
    · exact hn
  have hG := Complex.barnesRes_Gamma_add_nat_succ (s+1-a) n hall
  rw [Finset.prod_range_succ] at hG
  have hP : ∏ j ∈ Finset.range n, (s+1-a+j) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j hj' => hj j (Finset.mem_range.mp hj')
  have hd : s - (a-1-n) ≠ 0 := sub_ne_zero.mpr hs
  unfold incRep_phi incRep_f
  rw [hG, show s+1-a+(n:ℂ) = s - (a-1-n) by ring]
  field_simp

lemma incRep_phi_differentiableAt {a w s : ℂ} {n : ℕ} (hs : Complex.sin (π*s) ≠ 0)
    (hA : ∀ m : ℕ, s+1-a+n+1 ≠ -m) (hj : ∀ j : ℕ, j < n → s+1-a+j ≠ 0) :
    DifferentiableAt ℂ (incRep_phi a w n) s := by
  have hP : ∏ j ∈ Finset.range n, (s+1-a+j) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j hj' => hj j (Finset.mem_range.mp hj')
  unfold incRep_phi
  refine ((((differentiableAt_Gamma _ hA).comp s (by fun_prop)).div (by fun_prop) hP).mul
    ((differentiableAt_const _).div ((Complex.differentiable_sin _).comp s (by fun_prop)) hs)).mul
    (by fun_prop)

/-- Shifting the 8.6.12 line across exactly one pole `s = a-1-n`. -/
lemma incRep_shift_one {a w : ℂ} (hw : |w.im| < 3*π/2) {c₁ c₂ : ℝ}
    (hsin : ∀ x ∈ Icc c₁ c₂, Real.sin (π*x) ≠ 0) {n : ℕ} (hn₁ : c₁ < a.re - 1 - n)
    (hn₂ : a.re - 1 - n < c₂) (hno : ∀ m : ℕ, m ≠ n → a.re - 1 - m ∉ Icc c₁ c₂) :
    (∫ y : ℝ, incRep_f a w (c₂ + y*I)) - (∫ y : ℝ, incRep_f a w (c₁ + y*I)) =
      2*π*incRep_res a w n := by
  have h12 : c₁ < c₂ := hn₁.trans hn₂
  set p : ℂ := a-1-n with hp
  have hpre : p.re = a.re - 1 - n := by simp [hp]
  have hpim : p.im = a.im := by simp [hp]
  have hj : ∀ t : ℂ, t.re ∈ Icc c₁ c₂ → ∀ j : ℕ, j < n → t+1-a+j ≠ 0 := by
    intro t htS j hjn h
    have := congrArg re h; simp at this
    exact hno j hjn.ne (by rw [show a.re - 1 - j = t.re by linarith]; exact htS)
  have hdiv : ∀ t : ℂ, t.re ∈ Icc c₁ c₂ → t ≠ p → incRep_phi a w n t / (t - p) = incRep_f a w t :=
    fun t htS htp => incRep_phi_div htp (hj t htS)
  have hav : ∀ c ∈ Icc c₁ c₂, c ≠ a.re - 1 - n → ∀ m : ℕ, a.re - 1 - m ≠ c := by
    intro c hcI hcn m h
    by_cases hm : m = n
    · subst hm; exact hcn h.symm
    · exact hno m hm (h ▸ hcI)
  have hline : ∀ c ∈ Icc c₁ c₂, c ≠ a.re - 1 - n →
      (fun y : ℝ => incRep_phi a w n (c + y*I) / (c + y*I - p)) =
        fun y : ℝ => incRep_f a w (c + y*I) := by
    intro c hcI hcn
    funext y
    exact hdiv _ (by simpa using hcI) (fun h => hcn (by
      have := congrArg re h; simp at this; rw [this, hpre]))
  have h1I : c₁ ∈ Icc c₁ c₂ := ⟨le_rfl, h12.le⟩
  have h2I : c₂ ∈ Icc c₁ c₂ := ⟨h12.le, le_rfl⟩
  have hn1 : c₁ ≠ a.re - 1 - n := hn₁.ne
  have hn2 : c₂ ≠ a.re - 1 - n := hn₂.ne'
  obtain ⟨ht, hb⟩ := incRep_f_horizontal (a := a) hw h12.le
  have hH : ∀ T : ℝ, T ≠ a.im → (∫ x in c₁..c₂, incRep_phi a w n (x + T*I) / (x + T*I - p)) =
      ∫ x in c₁..c₂, incRep_f a w (x + T*I) := by
    intro T hT
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le h12.le] at hx
    exact hdiv _ (by simpa using hx) (fun h => hT (by
      have := congrArg im h; simp at this; rw [this, hpim]))
  have hΦ : DifferentiableOn ℂ (incRep_phi a w n) (re ⁻¹' Icc c₁ c₂) := by
    intro t htS
    have htS' : t.re ∈ Icc c₁ c₂ := htS
    refine (incRep_phi_differentiableAt (Complex.barnesRes_sin_ne_zero_of_re (hsin _ htS'))
      (fun m h => ?_) (hj t htS')).differentiableWithinAt
    have := congrArg re h; simp at this
    exact hno (n+1+m) (by omega) (by
      rw [show a.re - 1 - ((n+1+m : ℕ) : ℝ) = t.re by push_cast; linarith]; exact htS')
  have key := Complex.barnesRes_vertical_shift (p := p)
    (by rw [hpre]; exact hn₁) (by rw [hpre]; exact hn₂) hΦ
    (by rw [hline c₁ h1I hn1]; exact incRep_f_integrable hw (hsin c₁ h1I) (hav c₁ h1I hn1))
    (by rw [hline c₂ h2I hn2]; exact incRep_f_integrable hw (hsin c₂ h2I) (hav c₂ h2I hn2))
    (ht.congr' (by
      filter_upwards [eventually_gt_atTop a.im] with T hT
      exact (hH T hT.ne').symm))
    (hb.congr' (by
      filter_upwards [eventually_lt_atBot a.im] with T hT
      exact (hH T hT.ne).symm))
  rw [hline c₁ h1I hn1, hline c₂ h2I hn2, hp, incRep_phi_pole] at key
  exact key

/-- The `limUnder` residue of `gammaBarnesResidueSum` is the explicit residue. -/
lemma incRep_limUnder_res {a w : ℂ} {n : ℕ} (hs : Complex.sin (π*(a-1-n)) ≠ 0) :
    limUnder (𝓝[≠] (a-1-n)) (fun s : ℂ => (s-(a-1-n))*Gamma (s+1-a)*π/Complex.sin (π*s)*
      exp (-s*w)) = incRep_res a w n := by
  set p : ℂ := a-1-n with hp
  have hjp : ∀ j : ℕ, j < n → p+1-a+j ≠ 0 := fun j hj h => by
    have : (j:ℂ) = n := by linear_combination h
    exact hj.ne (by exact_mod_cast this)
  have hd := incRep_phi_differentiableAt (a := a) (w := w) (n := n) hs
    (fun m h => by
      have : (m:ℂ) = -1 := by rw [hp] at h; linear_combination h
      have := congrArg re this; simp at this; linarith [(m.cast_nonneg : (0:ℝ) ≤ m)]) hjp
  have hc := hd.continuousAt
  rw [← incRep_phi_pole]
  refine Tendsto.limUnder_eq ?_
  have hev : ∀ᶠ s in 𝓝[≠] p, incRep_phi a w n s =
      (s-p)*Gamma (s+1-a)*π/Complex.sin (π*s)*exp (-s*w) := by
    have hcj : ∀ j ∈ Finset.range n, ∀ᶠ s in 𝓝 p, s+1-a+j ≠ 0 := fun j hj =>
      ((continuous_id.add continuous_const).sub continuous_const |>.add
        continuous_const).continuousAt.eventually_ne (hjp j (Finset.mem_range.mp hj))
    have hall := (Finset.eventually_all (Finset.range n)).mpr hcj
    filter_upwards [nhdsWithin_le_nhds hall, self_mem_nhdsWithin] with s hs1 hs2
    have := incRep_phi_div (w := w) hs2 (fun j hj => hs1 j (Finset.mem_range.mpr hj))
    rw [div_eq_iff (sub_ne_zero.mpr hs2)] at this
    rw [this]; unfold incRep_f; ring
  exact (hc.tendsto.mono_left nhdsWithin_le_nhds).congr' hev


/-- `sin(πc) ≠ 0` for `-1 < c < 0`. -/
lemma incRep_sin_ne_zero_strip {c : ℝ} (h0 : -1 < c) (h1 : c < 0) : Real.sin (π*c) ≠ 0 := by
  have : 0 < Real.sin (-(π*c)) := Real.sin_pos_of_pos_of_lt_pi (by nlinarith [Real.pi_pos])
    (by nlinarith [Real.pi_pos])
  rw [Real.sin_neg] at this; linarith

/-- The right-hand side of DLMF 8.6.12 (without residues). -/
def incRep_W (a w : ℂ) : ℂ := -Gamma (1-a)*exp ((1-a)*w+exp w)*upperIncGammaOnLog a w

/-- DLMF 8.6.12 for real `w` and `Re a < 1 + c`, from the Barnes integral for `U` (13.4.17). -/
lemma incRep_base_real {a : ℂ} (ha : ∀ n : ℕ, a ≠ n+1) {c : ℝ} (hc0 : -1 < c) (hc1 : c < 0)
    (hac : a.re < 1 + c) (w : ℝ) :
    ∫ y : ℝ, incRep_f a w (c + y*I) = 2*π*incRep_W a w := by
  set x : ℝ := Real.exp w with hx
  have hx0 : 0 < x := Real.exp_pos w
  have hb := kummerU_barnes (a := 1-a) (b := 1-a) (σ := c) hx0 (by simp; linarith)
    (by simp; linarith) hc1
  have hG1 : Gamma (1-a) ≠ 0 := Gamma_ne_zero fun m h => ha m (by linear_combination -h)
  have hxc : ∀ s : ℂ, (x:ℂ)^s = exp (s*w) := fun s => by
    rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx0.ne'), hx, ofReal_exp,
      Complex.log_exp (by simp [Real.pi_pos]) (by simp [Real.pi_pos.le])]; ring_nf
  have hpt : ∀ t : ℝ, Gamma (1-a + c + I*t) * Gamma (1 + (1-a) - (1-a) + c + I*t) *
      Gamma (-(c + I*t)) / (Gamma (1-a) * Gamma (1 + (1-a) - (1-a))) * (x:ℂ)^(-(c + I*t)) * I =
      (-I/Gamma (1-a)) * incRep_f a w (c + t*I) := by
    intro t
    have hr := Complex.Gamma_mul_Gamma_one_sub (-(c + I*t))
    rw [show 1 - -((c:ℂ) + I*t) = 1 + (1-a) - (1-a) + c + I*t by ring,
      show (π:ℂ) * -((c:ℂ) + I*t) = -(π*(c + t*I)) by ring, Complex.sin_neg] at hr
    rw [show 1 + (1-a) - (1-a) = (1:ℂ) by ring, Gamma_one, mul_one, hxc]
    unfold incRep_f
    rw [show (1:ℂ) + c + I*t = 1 + (1-a) - (1-a) + c + I*t by ring,
      show (1-a + c + I*t : ℂ) = c + t*I + 1 - a by ring, show -((c:ℂ) + I*t) = -(c + t*I) by ring]
    rw [show (c:ℂ) + t*I + 1 - a = (c + t*I) + 1 - a by ring] at *
    have hrr : Gamma (1 + (1-a) - (1-a) + c + I*t) * Gamma (-(c + t*I)) =
        -(π / Complex.sin (π*(c + t*I))) := by
      rw [show -((c:ℂ) + t*I) = -(c + I*t) by ring, mul_comm, hr, div_neg]
    rw [div_mul_eq_mul_div, mul_assoc (Gamma _), hrr]
    field_simp
  simp only [hpt] at hb
  rw [integral_const_mul] at hb
  rw [incRep_W, upperIncGammaOnLog_eq_upperIncGamma a (by simp [Real.pi_pos])
    (by simp [Real.pi_pos.le]), upperIncGamma, ← ofReal_exp, ← hx, hb, hxc]
  have hpi : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have he : exp (-(1-a)*w) * exp ((1-a)*w) = 1 := by rw [← Complex.exp_add]; ring_nf; simp
  have he2 : exp (-(x:ℂ)) * exp (x:ℂ) = 1 := by rw [← Complex.exp_add]; simp
  rw [show (1-a)*(w:ℂ) + (x:ℂ) = (1-a)*w + x by ring, Complex.exp_add]
  field_simp
  have hI : (∫ y : ℝ, incRep_f a w (c + I*y)) = ∫ y : ℝ, incRep_f a w (c + y*I) := by
    congr 1; funext y; ring_nf
  rw [hI]
  have he3 : exp ((1-a)*(w:ℂ)) * exp (-((1-a)*(w:ℂ))) = 1 := by
    rw [← Complex.exp_add]; simp
  set J := ∫ y : ℝ, incRep_f a w (c + y*I)
  linear_combination (-J) * he3 - (J * exp ((1-a)*(w:ℂ)) * exp (-((1-a)*(w:ℂ)))) * he2

/-- The 8.6.12 line integral is holomorphic in `w` on the strip `|Im w| < 3π/2`. -/
lemma incRep_integral_differentiableOn_w (a : ℂ) {c : ℝ} (hs : Real.sin (π*c) ≠ 0)
    (hav : ∀ n : ℕ, a.re - 1 - n ≠ c) :
    DifferentiableOn ℂ (fun w => ∫ y : ℝ, incRep_f a w (c + y*I))
      {w : ℂ | |w.im| < 3*π/2} := by
  have hU : IsOpen {w : ℂ | |w.im| < 3*π/2} :=
    isOpen_lt (continuous_abs.comp continuous_im) continuous_const
  obtain ⟨C, K, hC, h⟩ := incRep_Gamma_bound_pt (x := c+1-a.re) (fun n h => hav n (by linarith))
  have hS : 0 < |Real.sin (π*c)|/2 := by positivity
  refine Complex.differentiableOn_integral_of_locally_dominated hU
    (fun w hw => (incRep_f_continuous hs hav).aestronglyMeasurable)
    (Eventually.of_forall fun y w hw => incRep_f_differentiableAt_w.differentiableWithinAt) ?_
  intro w₀ hw₀
  have hw₀' : |w₀.im| < 3*π/2 := hw₀
  set θ : ℝ := (|w₀.im| + 3*π/2)/2
  have harg : ∀ᶠ w in 𝓝 w₀, |w.im| < θ :=
    (continuous_abs.comp continuous_im).continuousAt.eventually_lt continuousAt_const
      (by show |w₀.im| < θ; simp only [θ]; linarith)
  have hre : ∀ᶠ w in 𝓝 w₀, |w.re - w₀.re| < 1 := by
    have : Continuous fun w : ℂ => |w.re - w₀.re| := by fun_prop
    exact this.continuousAt.eventually_lt continuousAt_const (by simp)
  refine ⟨_, harg.and hre, fun y => C * (1+|a.im|)^K * Real.exp (π*|a.im|/2) *
      (π/(|Real.sin (π*c)|/2)) * Real.exp (|c| * (|w₀.re| + 1)) *
      ((1+|y|)^K * Real.exp (-((3*π/2 - θ)*|y|))),
    (DLMF.Gamma.integrable_one_add_abs_pow_mul_exp_neg (by simp only [θ]; linarith) K).const_mul _,
    Eventually.of_forall fun y w hw => ?_⟩
  obtain ⟨h1, h2⟩ := hw
  refine (incRep_norm_f_le c y hC hS (h _) (Complex.barnesRes_sin_lower_line c y)).trans ?_
  have hx : Real.exp (-(c*w.re)) ≤ Real.exp (|c| * (|w₀.re| + 1)) := by
    apply Real.exp_le_exp.mpr
    have h3 : |w.re| ≤ |w₀.re| + 1 := by
      have := abs_sub_abs_le_abs_sub w.re w₀.re; linarith
    have := neg_abs_le (c*w.re); rw [abs_mul] at this
    nlinarith [abs_nonneg c, abs_nonneg w.re]
  have he : Real.exp (-((3*π/2 - |w.im|)*|y|)) ≤ Real.exp (-((3*π/2 - θ)*|y|)) := by
    apply Real.exp_le_exp.mpr; nlinarith [abs_nonneg y]
  dsimp only
  gcongr

/-- DLMF 8.6.12 in the base regime `Re a < 1 + c` (no crossed poles). -/
lemma incRep_base {a : ℂ} (ha : ∀ n : ℕ, a ≠ n+1) {c : ℝ} (hc0 : -1 < c) (hc1 : c < 0)
    (hac : a.re < 1 + c) {w : ℂ} (hw : |w.im| < 3*π/2) :
    ∫ y : ℝ, incRep_f a w (c + y*I) = 2*π*incRep_W a w := by
  have hs := incRep_sin_ne_zero_strip hc0 hc1
  have hav : ∀ n : ℕ, a.re - 1 - n ≠ c := fun n h => by
    linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]
  set U : Set ℂ := {w : ℂ | |w.im| < 3*π/2}
  have hUo : IsOpen U := isOpen_lt (continuous_abs.comp continuous_im) continuous_const
  have hF := (incRep_integral_differentiableOn_w a hs hav).analyticOnNhd hUo
  have hG : AnalyticOnNhd ℂ (fun w => 2*π*incRep_W a w) U := by
    refine DifferentiableOn.analyticOnNhd (fun w _ => ?_) hUo
    unfold incRep_W
    exact (((differentiableAt_const _).mul (by fun_prop)).mul
      (hasDerivAt_upperIncGammaOnLog a w).differentiableAt).const_mul _ |>.differentiableWithinAt
  have h0 : (0:ℂ) ∈ U := by simp [U, Real.pi_pos]
  have hfreq : ∃ᶠ v in 𝓝[≠] (0:ℂ), (∫ y : ℝ, incRep_f a v (c + y*I)) = 2*π*incRep_W a v := by
    have hmap : Tendsto (fun x : ℝ => (x:ℂ)) (𝓝[≠] (0:ℝ)) (𝓝[≠] (0:ℂ)) := by
      have := continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin (s := {(0:ℝ)}ᶜ)
        (t := {(0:ℂ)}ᶜ) (x := 0) (fun x hx h => hx (by simp at h ⊢; exact_mod_cast h))
      simpa using this
    have hev : ∀ᶠ x : ℝ in 𝓝[≠] (0:ℝ), (∫ y : ℝ, incRep_f a (x:ℂ) (c + y*I)) =
        2*π*incRep_W a x := Eventually.of_forall fun x => incRep_base_real ha hc0 hc1 hac x
    exact hmap.frequently hev.frequently
  have hconv : Convex ℝ U := by
    have : U = im ⁻¹' Ioo (-(3*π/2)) (3*π/2) := by
      ext v; simp [U, abs_lt]
    rw [this]; exact (convex_Ioo _ _).linear_preimage imLm
  exact hF.eqOn_of_preconnected_of_frequently_eq hG hconv.isPreconnected h0 hfreq hw

/-- A natural-number ceiling is determined by the naturals below it. -/
lemma incRep_ceil_eq_of_iff {x : ℝ} {k : ℕ} (h : ∀ n : ℕ, (n:ℝ) < x ↔ n < k) : ⌈x⌉₊ = k := by
  apply le_antisymm
  · by_contra h'
    push Not at h'
    have := (h k).mp (Nat.lt_ceil.mp h')
    exact lt_irrefl _ this
  · by_contra h'
    push Not at h'
    exact lt_irrefl _ (Nat.lt_ceil.mpr ((h _).mpr h'))

/-- The residue-corrected 8.6.12 line integral. -/
def incRep_J (a w : ℂ) (c : ℝ) : ℂ :=
  (∫ y : ℝ, incRep_f a w (c + y*I)) + 2*π*∑ n ∈ Finset.range ⌈a.re-1-c⌉₊, incRep_res a w n

lemma incRep_sin_strip_Icc {c₁ c₂ : ℝ} (h1 : -1 < c₁) (h2 : c₂ < 0) :
    ∀ x ∈ Icc c₁ c₂, Real.sin (π*x) ≠ 0 := fun x hx =>
  incRep_sin_ne_zero_strip (by linarith [hx.1]) (by linarith [hx.2])

lemma incRep_J_eq_of_le {a w : ℂ} (hw : |w.im| < 3*π/2) {c₁ c₂ : ℝ} (h1 : -1 < c₁)
    (h12 : c₁ ≤ c₂) (h2 : c₂ < 0) (hav₁ : ∀ n : ℕ, a.re - 1 - n ≠ c₁)
    (hav₂ : ∀ n : ℕ, a.re - 1 - n ≠ c₂) : incRep_J a w c₁ = incRep_J a w c₂ := by
  rcases eq_or_lt_of_le h12 with h | h12'
  · rw [h]
  have hsin := incRep_sin_strip_Icc h1 h2
  by_cases hex : ∃ n₀ : ℕ, a.re - 1 - n₀ ∈ Icc c₁ c₂
  · obtain ⟨n₀, hn₀⟩ := hex
    have hp1 : c₁ < a.re - 1 - n₀ := lt_of_le_of_ne hn₀.1 (hav₁ n₀).symm
    have hp2 : a.re - 1 - n₀ < c₂ := lt_of_le_of_ne hn₀.2 (hav₂ n₀)
    have hno : ∀ m : ℕ, m ≠ n₀ → a.re - 1 - m ∉ Icc c₁ c₂ := by
      intro m hm hmI
      rcases lt_or_gt_of_ne hm with h' | h'
      · have : (m:ℝ) + 1 ≤ n₀ := by exact_mod_cast h'
        linarith [hmI.2]
      · have : (n₀:ℝ) + 1 ≤ m := by exact_mod_cast h'
        linarith [hmI.1]
    have hsh := incRep_shift_one hw hsin hp1 hp2 hno
    have hN1 : ⌈a.re - 1 - c₁⌉₊ = n₀ + 1 := incRep_ceil_eq_of_iff fun n => by
      constructor
      · intro hn
        by_contra h'
        have : (n₀:ℝ) + 1 ≤ n := by exact_mod_cast (show n₀ + 1 ≤ n by omega)
        linarith
      · intro hn
        have : (n:ℝ) ≤ n₀ := by exact_mod_cast (show n ≤ n₀ by omega)
        linarith
    have hN2 : ⌈a.re - 1 - c₂⌉₊ = n₀ := incRep_ceil_eq_of_iff fun n => by
      constructor
      · intro hn
        by_contra h'
        have : (n₀:ℝ) ≤ n := by exact_mod_cast (show n₀ ≤ n by omega)
        linarith
      · intro hn
        have : (n:ℝ) + 1 ≤ n₀ := by exact_mod_cast (show n + 1 ≤ n₀ by omega)
        linarith
    unfold incRep_J
    rw [hN1, hN2, Finset.sum_range_succ]
    linear_combination -hsh
  · push Not at hex
    have hN : ⌈a.re - 1 - c₁⌉₊ = ⌈a.re - 1 - c₂⌉₊ := incRep_ceil_eq_of_iff fun n => by
      rw [Nat.lt_ceil]
      constructor
      · intro hn
        by_contra h'
        exact hex n ⟨by linarith, by linarith⟩
      · intro hn; linarith
    unfold incRep_J
    rw [hN, incRep_shift_none hw h12' hsin hex]

lemma incRep_J_eq {a w : ℂ} (hw : |w.im| < 3*π/2) {c₁ c₂ : ℝ} (h1 : -1 < c₁) (h1' : c₁ < 0)
    (h2 : -1 < c₂) (h2' : c₂ < 0) (hav₁ : ∀ n : ℕ, a.re - 1 - n ≠ c₁)
    (hav₂ : ∀ n : ℕ, a.re - 1 - n ≠ c₂) : incRep_J a w c₁ = incRep_J a w c₂ := by
  rcases le_total c₁ c₂ with h | h
  · exact incRep_J_eq_of_le hw h1 h h2' hav₁ hav₂
  · exact (incRep_J_eq_of_le hw h2 h h1' hav₂ hav₁).symm

/-- A canonical admissible line in `(-1, 0)`. -/
def incRep_cg (a : ℂ) : ℝ :=
  if Int.fract a.re < 1/2 then (Int.fract a.re - 1)/2 else (Int.fract a.re - 2)/2

lemma incRep_cg_spec (a : ℂ) : ∃ m : ℤ, -1 < incRep_cg a ∧ incRep_cg a < 0 ∧
    (m:ℝ) + 1/4 ≤ a.re - 1 - incRep_cg a ∧ a.re - 1 - incRep_cg a ≤ m + 3/4 := by
  have h0 := Int.fract_nonneg a.re
  have h1 := Int.fract_lt_one a.re
  have he : a.re = ⌊a.re⌋ + Int.fract a.re := (Int.floor_add_fract a.re).symm
  unfold incRep_cg
  split_ifs with h
  · exact ⟨⌊a.re⌋ - 1, by linarith, by linarith, by push_cast; linarith, by push_cast; linarith⟩
  · push Not at h
    exact ⟨⌊a.re⌋, by linarith, by linarith, by linarith, by linarith⟩

lemma incRep_no_nat {m : ℤ} {x : ℝ} (h1 : (m:ℝ) < x) (h2 : x < m + 1) (n : ℕ) : (n:ℝ) ≠ x := by
  intro h
  rw [← h] at h1 h2
  have : (m:ℤ) < n := by exact_mod_cast h1
  have : (n:ℤ) < m + 1 := by exact_mod_cast h2
  omega

lemma incRep_ceil_near {m : ℤ} {x y : ℝ} (hx1 : (m:ℝ) < x) (hx2 : x < m + 1) (hy1 : (m:ℝ) < y)
    (hy2 : y < m + 1) : ⌈x⌉₊ = ⌈y⌉₊ :=
  incRep_ceil_eq_of_iff fun n => by
    rw [Nat.lt_ceil]
    have key : ∀ u : ℝ, (m:ℝ) < u → u < m + 1 → ((n:ℝ) < u ↔ (n:ℤ) ≤ m) := by
      intro u hu1 hu2
      constructor
      · intro hn
        have : ((n:ℤ):ℝ) < m + 1 := by push_cast; linarith
        exact Int.lt_add_one_iff.mp (by exact_mod_cast this)
      · intro hn
        have : ((n:ℤ):ℝ) ≤ m := by exact_mod_cast hn
        push_cast at this; linarith
    rw [key x hx1 hx2, key y hy1 hy2]

lemma incRep_sin_lower (m : ℤ) : ∃ δ : ℝ, 0 < δ ∧
    ∀ x ∈ Icc ((m:ℝ) + 1/8) (m + 7/8), δ ≤ |Real.sin (π*x)| := by
  obtain ⟨x₁, hx₁, hmin⟩ := (isCompact_Icc (a := (m:ℝ) + 1/8) (b := m + 7/8)).exists_isMinOn
    (nonempty_Icc.mpr (by linarith)) ((Real.continuous_sin.comp (continuous_const.mul
      continuous_id)).abs.continuousOn)
  refine ⟨|Real.sin (π*x₁)|, abs_pos.mpr fun h => ?_, fun x hx => hmin hx⟩
  obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp h
  have hxk : x₁ = k := by
    have := Real.pi_pos
    have h2 : ((k:ℝ) - x₁) * π = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h3 | h3 <;> linarith
  rw [hxk] at hx₁
  have h1 : (m:ℝ) < k := by linarith [hx₁.1]
  have h2 : (k:ℝ) < m + 1 := by linarith [hx₁.2]
  have : m < k := by exact_mod_cast h1
  have : k < m + 1 := by exact_mod_cast h2
  omega

lemma incRep_cg_near {a₀ a : ℂ} (h : |a.re - a₀.re| < 1/8) : ∃ m : ℤ,
    (m:ℝ) + 1/8 < a.re - 1 - incRep_cg a₀ ∧ a.re - 1 - incRep_cg a₀ < m + 7/8 ∧
    (m:ℝ) + 1/8 < a₀.re - 1 - incRep_cg a₀ ∧ a₀.re - 1 - incRep_cg a₀ < m + 7/8 := by
  obtain ⟨m, -, -, h1, h2⟩ := incRep_cg_spec a₀
  have := abs_lt.mp h
  exact ⟨m, by linarith, by linarith, by linarith, by linarith⟩

lemma incRep_cg_avoid {a₀ a : ℂ} (h : |a.re - a₀.re| < 1/8) (n : ℕ) :
    a.re - 1 - n ≠ incRep_cg a₀ := by
  obtain ⟨m, h1, h2, -, -⟩ := incRep_cg_near h
  intro he
  exact incRep_no_nat (m := m) (x := a.re - 1 - incRep_cg a₀) (by linarith) (by linarith) n
    (by linarith)

/-- On the canonical line of `a₀` the 8.6.12 integral is holomorphic in `a` near `a₀`. -/
lemma incRep_integral_differentiableOn_a {w : ℂ} (hw : |w.im| < 3*π/2) (a₀ : ℂ) :
    DifferentiableOn ℂ (fun a => ∫ y : ℝ, incRep_f a w (incRep_cg a₀ + y*I))
      (Metric.ball a₀ (1/8)) := by
  set c₀ := incRep_cg a₀ with hc₀
  obtain ⟨m, hcm1, hcm2, -, -⟩ := incRep_cg_spec a₀
  have hs := incRep_sin_ne_zero_strip hcm1 hcm2
  have hre : ∀ a ∈ Metric.ball a₀ (1/8), |a.re - a₀.re| < 1/8 := fun a ha => by
    have := abs_re_le_norm (a - a₀)
    rw [Metric.mem_ball, dist_eq_norm] at ha
    simp only [sub_re] at this; linarith
  have him : ∀ a ∈ Metric.ball a₀ (1/8), |a.im| ≤ |a₀.im| + 1/8 := fun a ha => by
    have := abs_im_le_norm (a - a₀)
    rw [Metric.mem_ball, dist_eq_norm] at ha
    simp only [sub_im] at this
    have := abs_sub_abs_le_abs_sub a.im a₀.im; linarith
  obtain ⟨m', hm'1, hm'2, hm'3, hm'4⟩ := incRep_cg_near (a₀ := a₀) (a := a₀) (by simp)
  obtain ⟨C, K, hC, h⟩ := incRep_Gamma_bound (|(m':ℝ)| + 2)
  obtain ⟨δ, hδ, hδx⟩ := incRep_sin_lower (-m'-1)
  have hS : 0 < |Real.sin (π*c₀)|/2 := by positivity
  set M : ℝ := |a₀.im| + 1/8
  set b : ℝ := 3*π/2 - |w.im|
  have hb : 0 < b := by simp only [b]; linarith
  set K0 : ℝ := C/δ * (1+M)^K * Real.exp (π*M/2) * (π/(|Real.sin (π*c₀)|/2)) *
    Real.exp (-(c₀*w.re))
  have hbound : ∀ a ∈ Metric.ball a₀ (1/8), ∀ y : ℝ,
      ‖incRep_f a w (c₀ + y*I)‖ ≤ K0 * ((1+|y|)^K * Real.exp (-(b*|y|))) := by
    intro a ha y
    obtain ⟨m, h1, h2, h3, h4⟩ := incRep_cg_near (hre a ha)
    have hmm : m = m' := by
      have e1 : (m:ℝ) < m' + 1 := by linarith
      have e2 : (m':ℝ) < m + 1 := by linarith
      have : m < m' + 1 := by exact_mod_cast e1
      have : m' < m + 1 := by exact_mod_cast e2
      omega
    subst hmm
    have hxI : c₀ + 1 - a.re ∈ Icc (((-m-1 : ℤ):ℝ) + 1/8) (((-m-1 : ℤ):ℝ) + 7/8) := by
      push_cast; constructor <;> linarith
    have hxX : c₀ + 1 - a.re ∈ Icc (-(|(m:ℝ)| + 2)) (|(m:ℝ)| + 2) := by
      have := le_abs_self (m:ℝ); have := neg_abs_le (m:ℝ)
      push_cast at hxI
      constructor <;> linarith [hxI.1, hxI.2]
    have hsx := hδx _ hxI
    have hG : ‖Gamma ((c₀+1-a.re : ℝ) + I*(y - a.im : ℝ))‖ ≤
        C/δ * (1+|y - a.im|)^K * Real.exp (-(π*|y - a.im|)/2) := by
      have h' := (h _ hxX (y - a.im)).1
      have h'' : ‖Gamma ((c₀+1-a.re : ℝ) + I*(y - a.im : ℝ))‖ * δ ≤
          C * (1+|y - a.im|)^K * Real.exp (-(π*|y - a.im|)/2) :=
        le_trans (mul_le_mul_of_nonneg_left hsx (norm_nonneg _)) h'
      rw [← le_div_iff₀ hδ] at h''
      exact h''.trans (le_of_eq (by ring))
    refine (incRep_norm_f_le c₀ y (by positivity) hS hG
      (Complex.barnesRes_sin_lower_line c₀ y)).trans ?_
    have hAim := him a ha
    simp only [K0, b, M]
    gcongr
  have hav : ∀ a ∈ Metric.ball a₀ (1/8), ∀ n : ℕ, a.re - 1 - n ≠ c₀ := fun a ha =>
    incRep_cg_avoid (hre a ha)
  refine Complex.differentiableOn_integral_of_locally_dominated Metric.isOpen_ball
    (fun a ha => (incRep_f_continuous hs (hav a ha)).aestronglyMeasurable)
    (Eventually.of_forall fun y a ha =>
      (incRep_f_differentiableAt_param (incRep_ne_pole (hav a ha) y)).differentiableWithinAt)
    (fun a ha => ⟨_, Metric.isOpen_ball.mem_nhds ha,
      fun y => K0 * ((1+|y|)^K * Real.exp (-(b*|y|))),
      (DLMF.Gamma.integrable_one_add_abs_pow_mul_exp_neg hb _).const_mul _,
      Eventually.of_forall fun y a' ha' => hbound a' ha' y⟩)

lemma incRep_sin_res_ne {a : ℂ} (ha : ∀ n : ℕ, a ≠ n+1) {c : ℝ} (hc : -1 < c) {n : ℕ}
    (hn : c < a.re - 1 - n) : Complex.sin (π*(a-1-n)) ≠ 0 := by
  intro h
  obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp h
  have hpi : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hk' : a - 1 - n = k := by
    have := hk; rw [mul_comm (k:ℂ)] at this; exact mul_left_cancel₀ hpi this
  have hre := congrArg re hk'
  simp at hre
  have hk0 : 0 ≤ k := by
    have : (-1:ℝ) < k := by linarith
    have : (-1:ℤ) < k := by exact_mod_cast this
    omega
  apply ha (k.toNat + n)
  have : ((k.toNat : ℕ) : ℂ) = k := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hk0]
  push_cast
  rw [this]
  linear_combination hk'

lemma incRep_res_differentiableAt (w : ℂ) {a₀ : ℂ} {n : ℕ}
    (hs : Complex.sin (π*(a₀-1-n)) ≠ 0) :
    DifferentiableAt ℂ (fun a => incRep_res a w n) a₀ := by
  have h1 : DifferentiableAt ℂ (fun a : ℂ => Complex.sin (π*(a-1-n))) a₀ :=
    ((differentiableAt_const (π:ℂ)).mul ((differentiableAt_id.sub_const 1).sub_const
      (n:ℂ))).csin
  have h2 : DifferentiableAt ℂ (fun a : ℂ => exp (-(a-1-n)*w)) a₀ :=
    (((differentiableAt_id.sub_const 1).sub_const (n:ℂ)).neg.mul_const w).cexp
  unfold incRep_res
  exact ((differentiableAt_const _).mul ((differentiableAt_const (π:ℂ)).div h1 hs)).mul h2

/-- The canonical-line value of the residue-corrected 8.6.12 integral. -/
def incRep_G (w a : ℂ) : ℂ := incRep_J a w (incRep_cg a)

lemma incRep_G_eq_J {w : ℂ} (hw : |w.im| < 3*π/2) (a : ℂ) {c : ℝ} (hc0 : -1 < c) (hc1 : c < 0)
    (hav : ∀ n : ℕ, a.re - 1 - n ≠ c) : incRep_J a w c = incRep_G w a := by
  obtain ⟨m, h1, h2, -, -⟩ := incRep_cg_spec a
  exact incRep_J_eq hw hc0 hc1 h1 h2 hav (incRep_cg_avoid (by simp))

lemma incRep_G_differentiableAt {w : ℂ} (hw : |w.im| < 3*π/2) {a₀ : ℂ}
    (ha : ∀ n : ℕ, a₀ ≠ n+1) : DifferentiableAt ℂ (incRep_G w) a₀ := by
  obtain ⟨m₀, hc1, hc2, -, -⟩ := incRep_cg_spec a₀
  set H : ℂ → ℂ := fun a => (∫ y : ℝ, incRep_f a w (incRep_cg a₀ + y*I)) +
    2*π*∑ n ∈ Finset.range ⌈a₀.re-1-incRep_cg a₀⌉₊, incRep_res a w n
  have hre : ∀ a ∈ Metric.ball a₀ (1/8), |a.re - a₀.re| < 1/8 := fun a ha' => by
    have := abs_re_le_norm (a - a₀)
    rw [Metric.mem_ball, dist_eq_norm] at ha'
    simp only [sub_re] at this; linarith
  have heq : incRep_G w =ᶠ[𝓝 a₀] H := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by norm_num : (0:ℝ) < 1/8))]
      with a ha'
    rw [← incRep_G_eq_J hw a hc1 hc2 (incRep_cg_avoid (hre a ha'))]
    obtain ⟨m, h1, h2, h3, h4⟩ := incRep_cg_near (hre a ha')
    unfold incRep_J
    rw [incRep_ceil_near (m := m) (x := a.re - 1 - incRep_cg a₀) (y := a₀.re - 1 - incRep_cg a₀)
      (by linarith) (by linarith) (by linarith) (by linarith)]
  refine DifferentiableAt.congr_of_eventuallyEq ?_ heq
  refine DifferentiableAt.add ?_ ((DifferentiableAt.fun_sum fun n hn =>
    incRep_res_differentiableAt w (incRep_sin_res_ne (n := n) ha hc1 (by
      have := Nat.lt_ceil.mp (Finset.mem_range.mp hn); linarith))).const_mul _)
  exact (incRep_integral_differentiableOn_a hw a₀).differentiableAt
    (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by norm_num)))

/-- Finitely many residues recording indentation past right-hand Gamma poles. -/
def gammaBarnesResidueSum (a w : ℂ) (c : ℝ) : ℂ :=
  ∑ n ∈ Finset.range ⌈a.re-1-c⌉₊, limUnder (𝓝[≠] (a-1-n)) (fun s : ℂ => (s-(a-1-n))*Gamma (s+1-a)*π/sin (π*s)*exp (-s*w))

lemma incRep_residueSum_eq {a : ℂ} (ha : ∀ n : ℕ, a ≠ n+1) (w : ℂ) {c : ℝ} (hc0 : -1 < c) :
    gammaBarnesResidueSum a w c = ∑ n ∈ Finset.range ⌈a.re-1-c⌉₊, incRep_res a w n := by
  unfold gammaBarnesResidueSum
  refine Finset.sum_congr rfl fun n hn => incRep_limUnder_res (incRep_sin_res_ne ha hc0 ?_)
  have := Nat.lt_ceil.mp (Finset.mem_range.mp hn); linarith

/-- Logarithmic-plane formula with explicit separating-contour residues. -/
@[dlmf 8.6.E12]
theorem upperIncGamma_mellinBarnes_continued {a : ℂ} (ha : ∀ n : ℕ, a ≠ n+1) (w : ℂ) (hw : |w.im| < 3*π/2) {c : ℝ} (hc0 : -1 < c) (hc1 : c < 0) (hca : ∀ n : ℕ, a.re-1-n ≠ c) :
    HasIntegralWholeLine (fun y : ℝ => let s : ℂ := c+y*I; Gamma (s+1-a)*π/sin (π*s)*exp (-s*w)) (2*π*(-Gamma (1-a)*exp ((1-a)*w+exp w)*upperIncGammaOnLog a w-gammaBarnesResidueSum a w c)) := by
  set D : Set ℂ := {a : ℂ | ∀ n : ℕ, a ≠ n+1}
  set E : Set ℂ := {b : ℂ | ∀ n : ℕ, b ≠ 0 - n}
  have hDE : D = (fun a : ℂ => 1 - a) ⁻¹' E := by
    ext b; simp only [D, E, mem_ofPred_eq, mem_preimage]
    exact forall_congr' fun n => not_congr ⟨fun h => by linear_combination -h,
      fun h => by linear_combination -h⟩
  have hDE' : D = (fun b : ℂ => 1 - b) '' E := by
    ext b; constructor
    · intro hb; refine ⟨1 - b, ?_, by ring⟩
      have : b ∈ (fun a : ℂ => 1 - a) ⁻¹' E := hDE ▸ hb
      exact this
    · rintro ⟨e, he, rfl⟩
      rw [hDE]; show 1 - (1 - e) ∈ E; rw [show 1 - (1 - e) = e by ring]; exact he
  have hDo : IsOpen D := hDE ▸ (Complex.barnesRes_isOpen_ne_sub_nat 0).preimage (by fun_prop)
  have hDc : IsPreconnected D :=
    hDE' ▸ (Complex.barnesRes_isPreconnected_ne_sub_nat 0).image _ (by fun_prop)
  have hGa : AnalyticOnNhd ℂ (incRep_G w) D := DifferentiableOn.analyticOnNhd
    (fun b hb => (incRep_G_differentiableAt hw hb).differentiableWithinAt) hDo
  have hWa : AnalyticOnNhd ℂ (fun b => 2*π*incRep_W b w) D := by
    refine DifferentiableOn.analyticOnNhd (fun b hb => ?_) hDo
    have hG : ∀ m : ℕ, 1 - b ≠ -m := fun m h => hb m (by linear_combination -h)
    unfold incRep_W
    exact ((((differentiableAt_Gamma _ hG).comp b (by fun_prop)).neg.mul (by fun_prop)).mul
      (upperIncGammaOnLog_parameter_entire w b)).const_mul _ |>.differentiableWithinAt
  have hpos : ∀ b : ℂ, b.re < 1/2 → incRep_G w b = 2*π*incRep_W b w := by
    intro b hb
    have hbD : ∀ n : ℕ, b ≠ n+1 := fun n h => by
      have := congrArg re h; simp at this; linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]
    have hav : ∀ n : ℕ, b.re - 1 - n ≠ -1/2 := fun n h => by
      linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]
    rw [← incRep_G_eq_J hw b (by norm_num) (by norm_num) hav]
    unfold incRep_J
    rw [Nat.ceil_eq_zero.mpr (by linarith), Finset.range_zero, Finset.sum_empty, mul_zero,
      add_zero]
    exact incRep_base hbD (by norm_num) (by norm_num) (by linarith) hw
  have h0 : (0:ℂ) ∈ D := fun n h => by
    have := congrArg re h; simp at this; linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]
  have hev : incRep_G w =ᶠ[𝓝 0] fun b => 2*π*incRep_W b w := by
    have ho : IsOpen {b : ℂ | b.re < 1/2} := isOpen_lt continuous_re continuous_const
    filter_upwards [ho.mem_nhds (by simp)] with b hb
    exact hpos b hb
  have hEq := hGa.eqOn_of_preconnected_of_eventuallyEq hWa hDc h0 hev ha
  have hJ := incRep_G_eq_J hw a hc0 hc1 hca
  rw [hEq] at hJ
  have hfun : (fun y : ℝ => let s : ℂ := c+y*I; Gamma (s+1-a)*π/sin (π*s)*exp (-s*w)) =
      fun y : ℝ => incRep_f a w (c + y*I) := rfl
  rw [hfun, incRep_residueSum_eq ha w hc0]
  have hint := incRep_f_integrable hw (incRep_sin_ne_zero_strip hc0 hc1) hca
  have hv : ∫ y : ℝ, incRep_f a w (c + y*I) = 2*π*(-Gamma (1-a)*exp ((1-a)*w+exp w)*
      upperIncGammaOnLog a w - ∑ n ∈ Finset.range ⌈a.re-1-c⌉₊, incRep_res a w n) := by
    unfold incRep_J at hJ; unfold incRep_W at hJ
    linear_combination hJ
  rw [← hv]
  exact incRep_hasIntegralWholeLine hint

end DLMF.Confluent
