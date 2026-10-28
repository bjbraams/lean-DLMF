/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.IncompleteGamma.SeriesRecurrences
public import DLMFMathlib.Analysis.Complex.BarnesResidue
public import DLMFMathlib.Analysis.Integral.PrincipalValue

/-!
# Integral representations of the lower incomplete Gamma function

Real and complex integrals, vertical-contour estimates and the lower incomplete-Gamma Barnes
representation.

Source references and common attribution are retained in
`DLMF.IncompleteGamma.Representations`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF

open scoped Real Topology Nat

namespace DLMF.Confluent

open DLMF.Statistical

/-- Termwise evaluation of `∫_{-π}^{π} e^{iaθ + z e^{iθ}} dθ`. -/
theorem hasSum_integral_exp_circle {a : ℂ} (ha : ∀ n : ℕ, a ≠ -n) (z : ℂ) :
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

/-- Identity under the stated parameter and domain assumptions: `lowerIncGamma a z=z^a/sin
(π*a)*(∫ t : ℝ in 0..π, exp (z*Real.cos t)*cos (a*t+z*Real.sin t))`. -/
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
theorem lgJ_ofReal_mul_cpow {t : ℝ} (ht : 0 < t) {z : ℂ} (hz : z ≠ 0) (w : ℂ) :
    ((t : ℂ) * z) ^ w = (t : ℂ) ^ w * z ^ w := by
  have htz : (t : ℂ) * z ≠ 0 := mul_ne_zero (by exact_mod_cast ht.ne') hz
  rw [cpow_def_of_ne_zero htz, cpow_def_of_ne_zero (by exact_mod_cast ht.ne'),
    cpow_def_of_ne_zero hz, log_ofReal_mul ht hz, ← Complex.exp_add, ofReal_log ht.le]
  ring_nf

/-- `‖Γ(a+1)‖ Γ(σ+1+k) ≤ ‖Γ(a+1+k)‖ Γ(σ+1)` for `σ = Re a > 0`. -/
theorem lgJ_norm_Gamma_ge {a : ℂ} (ha : 0 < a.re) (k : ℕ) :
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

/-- Identity under the stated parameter and domain assumptions: `lowerIncGamma a z=z^(a/2)*(∫ t :
ℝ in Ioi 0, exp (-t : ℂ)*(t : ℂ)^(a/2-1)*besselJ a (2*(z*t)^(1/2 : ℂ)))`. -/
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
theorem ofReal_exp_cpow_eq_exp_mul (x : ℝ) (w : ℂ) : ((Real.exp x : ℝ) : ℂ)^w = exp (x*w) := by
  rw [ofReal_exp, cpow_def_of_ne_zero (Complex.exp_ne_zero _), log_exp (by simp [Real.pi_pos])
    (by simp [Real.pi_pos.le])]

/-- Identity under the stated parameter and domain assumptions: `lowerIncGamma a z=z^a*(∫ t : ℝ in
Ioi 0, exp (-a*t-z*Real.exp (-t)))`. -/
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

/-- Identity under the stated parameter and domain assumptions: `upperIncGamma a z=z^a*exp
(-z)/Gamma (1-a)*(∫ t : ℝ in Ioi 0, (t : ℂ)^(-a)*exp (-t : ℂ)/(z+t))`. -/
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

/-- Identity under the stated parameter and domain assumptions: `upperIncGamma a z=z^a*exp (-z)*(∫
t : ℝ in Ioi 0, exp (-z*t)*(1+(t : ℂ))^(a-1))`. -/
@[dlmf 8.6.E5]
theorem upperIncGamma_laplace_integral_complex (a : ℂ) {z : ℂ} (hz : 0 < z.re) :
    upperIncGamma a z=z^a*exp (-z)*(∫ t : ℝ in Ioi 0, exp (-z*t)*(1+(t : ℂ))^(a-1)) := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero (Or.inl hz)
  rw [upperIncGamma_eq_cpow_mul_kummerU a hz0, kummerU_laplace (by norm_num) hz, Gamma_one,
    div_one, one_mul]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [sub_self, cpow_zero, mul_one, show a+1-1-1 = a-1 by ring]

/-- Identity under the stated parameter and domain assumptions: `upperIncGamma a z=2*z^(a/2)*exp
(-z)/Gamma (1-a)*(∫ t : ℝ in Ioi 0, exp (-t : ℂ)*(t : ℂ)^(-a/2)*DLMF.Bessel.besselK a
(2*(z*t)^(1/2 : ℂ)))`. -/
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

/-- Identity under the stated parameter and domain assumptions: `upperIncGamma a z=z^a*(∫ t : ℝ in
Ioi 0, exp (a*t-z*Real.exp t))`. -/
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

/-- Identity under the stated parameter and domain assumptions: `lowerIncGamma a z = -I*z^a/(2*sin
(π*a))*(∫ θ : ℝ in (-π)..π, I*exp (a*I*θ+z*exp (I*θ)))`. -/
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
theorem ugPV_hasPrincipalValueIoi {f : ℝ → ℂ} {a b c : ℝ} (A : ℂ) (hac : a < c) (hcb : c < b)
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

/-- Identity under the stated parameter and domain assumptions: `HasPrincipalValueIoi (fun t : ℝ
=> (t : ℂ)^a*exp (-z*t)/(t-1)) 0 1 (upperGammaIndentPV a z)`. -/
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

/-- Identity under the stated parameter and domain assumptions: `upperIncGammaOnLog (-a) (log
z+ε*π*I)=exp z*exp (-ε*π*I*a)/Gamma (1+a)*(upperGammaIndentPV a z-ε*π*I*exp (-z))`. -/
@[dlmf 8.6.E9]
theorem upperIncGamma_indented_integral {a z : ℂ} (ha : -1 < a.re) (hz : 0 < z.re) {ε : ℝ} (hε : ε=1 ∨ ε = -1) :
    upperIncGammaOnLog (-a) (log z+ε*π*I)=exp z*exp (-ε*π*I*a)/Gamma (1+a)*(upperGammaIndentPV a z-ε*π*I*exp (-z)) := by
  sorry

/-- The Mellin–Barnes integrand `Γ(s+a) z^{-s}/s`, `s = c+iy`, of DLMF 8.6.11. -/
noncomputable def upperIncGammaMBIntegrand (a z : ℂ) (c y : ℝ) : ℂ :=
  Gamma ((c+y*I)+a)*z^(-((c:ℂ)+y*I))/((c:ℂ)+y*I)

/-- The Mellin–Barnes integrand is continuous in `y`. -/
theorem continuous_upperIncGammaMBIntegrand (a : ℂ) {z : ℂ} (hz : z ≠ 0) {c : ℝ} (hc : 0 < c)
    (hca : 0 < c+a.re) : Continuous (upperIncGammaMBIntegrand a z c) := by
  refine continuous_iff_continuousAt.mpr fun y => ?_
  unfold upperIncGammaMBIntegrand
  refine ContinuousAt.div (ContinuousAt.mul ?_ ?_) (by fun_prop) ?_
  · exact (DLMF.Gamma.continuousAt_Gamma_of_re_pos (by simp; linarith)).comp (by fun_prop)
  · exact (Continuous.const_cpow (f := fun y : ℝ => -((c:ℂ)+y*I)) (by fun_prop) (Or.inl hz)).continuousAt
  · intro h; have := congrArg re h; simp at this; linarith

/-- Uniform bound for the Mellin–Barnes integrand on `‖z‖ ≥ ρ`, `|arg z| ≤ θ`. -/
theorem norm_upperIncGammaMBIntegrand_le (a : ℂ) {c : ℝ} (hc : 0 < c) (hca : 0 < c+a.re) :
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
theorem integrable_upperIncGammaMBIntegrand (a : ℂ) {z : ℂ} (hz : 0 < z.re) {c : ℝ} (hc : 0 < c)
    (hca : 0 < c+a.re) : Integrable (upperIncGammaMBIntegrand a z c) := by
  obtain ⟨C, K, hCK⟩ := norm_upperIncGammaMBIntegrand_le a hc hca
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
  have hθ : |arg z| < π/2 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz)
  refine ((DLMF.Gamma.integrable_one_add_abs_pow_mul_exp_neg (c := π/2-|arg z|) (by linarith)
    K).const_mul (C * ‖z‖ ^ (-c) / c)).mono'
    (continuous_upperIncGammaMBIntegrand a hz0 hc hca).aestronglyMeasurable
    (Eventually.of_forall fun y => hCK (norm_pos_iff.mpr hz0) z le_rfl le_rfl y)

/-- The Mellin–Barnes integral is holomorphic in `z` on the right half-plane. -/
theorem differentiableOn_integral_upperIncGammaMBIntegrand (a : ℂ) {c : ℝ} (hc : 0 < c)
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
theorem integral_upperIncGammaMBIntegrand_ofReal (a : ℂ) {x : ℝ} (hx : 0 < x) {c : ℝ} (hc : 0 < c)
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

/-- Identity under the stated parameter and domain assumptions: `HasIntegralWholeLine (fun y : ℝ
=> let s : ℂ := c+y*I; Gamma (s+a)*z^(-s)/s) (2*π*upperIncGamma a z)`. -/
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
theorem incRep_integral_eq {f : ℝ → ℂ} {v : ℂ} (hf : Integrable f) (h : HasIntegralWholeLine f v) :
    ∫ y, f y = v := by
  obtain ⟨u, w, hu, hw, huw⟩ := h
  have hu' := tendsto_nhds_unique hu
    (intervalIntegral_tendsto_integral_Iic 0 hf.integrableOn tendsto_id)
  have hw' := tendsto_nhds_unique hw
    (intervalIntegral_tendsto_integral_Ioi 0 hf.integrableOn tendsto_id)
  rw [← huw, hu', hw', intervalIntegral.integral_Iic_add_Ioi hf.integrableOn hf.integrableOn]

/-- An integrable function has its Lebesgue integral as whole-line improper integral. -/
theorem incRep_hasIntegralWholeLine {f : ℝ → ℂ} (hf : Integrable f) :
    HasIntegralWholeLine f (∫ y, f y) :=
  ⟨_, _, intervalIntegral_tendsto_integral_Iic 0 hf.integrableOn tendsto_id,
    intervalIntegral_tendsto_integral_Ioi 0 hf.integrableOn tendsto_id,
    intervalIntegral.integral_Iic_add_Ioi hf.integrableOn hf.integrableOn⟩

/-- The 8.6.10 integrand is the negative of a shifted 8.6.11 integrand. -/
theorem incRep_L_eq_upper (a z : ℂ) (c y : ℝ) :
    incRep_L a z c y = -upperIncGammaMBIntegrand a z (c - a.re) (y - a.im) := by
  unfold incRep_L upperIncGammaMBIntegrand
  rw [show ((c - a.re : ℝ) : ℂ) + ((y - a.im : ℝ) : ℂ) * I = (c + y*I) - a by
    apply Complex.ext <;> simp, sub_add_cancel, neg_sub, ← neg_sub (c + y*I : ℂ) a, div_neg]
  ring

/-- DLMF 8.6.10 to the right of the pole: the line integral is `-2π Γ(a,z)`. -/
theorem incRep_integral_right {a z : ℂ} (hz : 0 < z.re) {c : ℝ} (hc : 0 < c) (hca : a.re < c) :
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
theorem incRep_norm_L_le (a : ℂ) {z : ℂ} (hz : z ≠ 0) (c y : ℝ) :
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
theorem incRep_norm_Gamma_le {x x' : ℝ} (hx : 0 < x) (hxx : x ≤ x') (y : ℝ) :
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
theorem incRep_tendsto_poly_exp {b : ℝ} (hb : 0 < b) (K : ℕ) :
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
theorem incRep_integrable {a z : ℂ} (hz : 0 < z.re) {c : ℝ} (hc : 0 < c) (hca : c ≠ a.re) :
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
theorem incRep_L_eq_div (a z : ℂ) (x T : ℝ) :
    (-(Gamma ((x:ℂ)+T*I) * z^(a-((x:ℂ)+T*I)))) / ((x:ℂ)+T*I - a) = incRep_L a z x T := by
  unfold incRep_L; rw [neg_div, ← div_neg, neg_sub]; ring

open scoped Interval in
/-- Horizontal cross-sections of the 8.6.10 integrand vanish at `±i∞`. -/
theorem incRep_horizontal {a z : ℂ} (hz : 0 < z.re) {c c' : ℝ} (hc : 0 < c) (hcc : c ≤ c') :
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
theorem incRep_integral_value {a z : ℂ} (ha : ∀ n : ℕ, a ≠ -n) (hz : 0 < z.re) {c : ℝ} (hc : 0 < c)
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

end DLMF.Confluent
end
