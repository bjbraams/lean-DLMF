/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.Integrals.Laplace
public import DLMFMathlib.Analysis.Fourier.L1Inversion
public import DLMFMathlib.Analysis.Complex.LaplaceInversion

/-!
# Fourier pairings for the incomplete Beta Barnes integral

The Laplace transform of the regularized Kummer function gives the integrable Fourier
transform `s^(-a)/(s-x)`. Pairing it with a Gamma kernel evaluates the vertical integral
in DLMF 8.17.10 without assumptions of square integrability.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory DLMF.Hypergeometric
open scoped Real Topology FourierTransform

namespace DLMF.Confluent.IncompleteBetaBarnes

/-- The Gamma density without its constant normalization, extended by zero to the left. -/
def gammaKernel (b d t : ℝ) : ℂ :=
  (Ioi (0 : ℝ)).indicator (fun u => (u : ℂ) ^ ((b : ℂ)-1) * exp (-(d : ℂ)*u)) t

/-- The regularized Kummer Laplace kernel, extended by zero to the left. -/
def kummerKernel (a x c t : ℝ) : ℂ :=
  (Ioi (0 : ℝ)).indicator (fun u => exp (-(c : ℂ)*u) * (u : ℂ) ^ (a : ℂ) *
    regularizedHGFun {1} {(a : ℂ)+1} ((x : ℂ)*u)) t

/-- The Gamma kernel is integrable for positive shape and rate. -/
theorem integrable_gammaKernel {b d : ℝ} (hb : 0 < b) (hd : 0 < d) :
    Integrable (gammaKernel b d) := by
  unfold gammaKernel
  rw [integrable_indicator_iff measurableSet_Ioi]
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := b-1) (b := d)
    (by linarith) one_pos hd
  refine h.mono' (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht, norm_exp]
  simp only [sub_re, ofReal_re, one_re, neg_mul, neg_re, mul_re, ofReal_im,
    mul_zero, sub_zero, Real.rpow_one]
  exact le_rfl

/-- The regularized Kummer kernel is integrable when its rate exceeds its argument scale. -/
theorem integrable_kummerKernel {a x c : ℝ} (ha : 0 < a) (hx : 0 < x) (hxc : x < c) :
    Integrable (kummerKernel a x c) := by
  unfold kummerKernel
  rw [integrable_indicator_iff measurableSet_Ioi]
  simpa only [add_sub_cancel_right] using
    (laplace_regularizedHGFun_integrable (a := 1) (b := (a:ℂ)+1) (c := (a:ℂ)+1)
      (k := x) (z := c) (by simp; linarith) (by simpa [max_eq_right hx.le] using hxc))

/-- Fourier transform of the Gamma kernel. -/
theorem fourier_gammaKernel {b d : ℝ} (hb : 0 < b) (hd : 0 < d) (ξ : ℝ) :
    𝓕 (gammaKernel b d) ξ = Gamma b * ((d:ℂ)+(2*π*ξ:ℝ)*I)^(-(b:ℂ)) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  rw [← integral_cpow_mul_cexp_neg_mul_Ioi (by simpa using hb : 0 < (b:ℂ).re)
    (by simpa using hd : 0 < ((d:ℂ)+(2*π*ξ:ℝ)*I).re),
    ← integral_indicator measurableSet_Ioi]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  by_cases ht : 0 < t
  · simp only [gammaKernel, indicator_of_mem (show t ∈ Ioi (0:ℝ) from ht)]
    rw [mul_left_comm, mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  · simp [gammaKernel, ht]

/-- Fourier transform of the regularized Kummer kernel. -/
theorem fourier_kummerKernel {a x c : ℝ} (ha : 0 < a) (hx : 0 < x) (hxc : x < c) (ξ : ℝ) :
    𝓕 (kummerKernel a x c) ξ =
      ((c:ℂ)+(2*π*ξ:ℝ)*I)^(-(a:ℂ))/((c:ℂ)+(2*π*ξ:ℝ)*I-x) := by
  let z : ℂ := (c:ℂ)+(2*π*ξ:ℝ)*I
  have hc : 0 < c := hx.trans hxc
  have hz : 0 < z.re := by simpa [z] using hc
  have hzx : (x:ℂ).re < z.re := by simpa [z] using hxc
  have hz0 : z ≠ 0 := ne_zero_of_re_pos hz
  have harg : ‖(x:ℂ)/z‖ < 1 := by
    rw [norm_div, div_lt_one (norm_pos_iff.mpr hz0), norm_real, Real.norm_of_nonneg hx.le]
    exact hzx.trans_le (re_le_norm z)
  have hreg := not_neg_nat_of_re_pos (show 0 < ((a:ℂ)+1).re by simp; linarith)
  have h := laplace_regularizedHGFun (a := 1) (b := (a:ℂ)+1) (c := (a:ℂ)+1)
    (k := x) (z := z) (by simp; linarith) hzx hz
  rw [regularizedGaussHypergeometric_eq_regularizedGaussHypergeometricFun _ _ _ harg,
    regularizedGaussHypergeometricFun_eq_div_Gamma hreg,
    ordinaryHypergeometric_eq_one_sub_neg_cpow
      (fun k hk => hreg k (by linear_combination hk)) harg] at h
  have hg : Gamma ((a:ℂ)+1) ≠ 0 := Gamma_ne_zero hreg
  have hright : Gamma ((a:ℂ)+1) * z^(-((a:ℂ)+1)) *
      ((1-(x:ℂ)/z)^(-(1:ℂ))/Gamma ((a:ℂ)+1)) = z^(-(a:ℂ))/(z-x) := by
    rw [cpow_neg_one, show -((a:ℂ)+1) = -(a:ℂ)-1 by ring,
      cpow_sub _ _ hz0, cpow_one]
    field_simp
  rw [hright] at h
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  change _ = z^(-(a:ℂ))/(z-x)
  rw [← h, ← integral_indicator measurableSet_Ioi]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  by_cases ht : 0 < t
  · simp only [kummerKernel, indicator_of_mem (show t ∈ Ioi (0:ℝ) from ht), add_sub_cancel_right]
    rw [← mul_assoc, ← mul_assoc, ← Complex.exp_add]
    congr 2
    simp only [z]
    push_cast
    ring
  · simp [kummerKernel, ht]

/-- The regularized Kummer transform is integrable on the frequency axis. -/
theorem integrable_fourier_kummerKernel {a x c : ℝ} (ha : 0 < a) (hx : 0 < x)
    (hxc : x < c) : Integrable (𝓕 (kummerKernel a x c)) := by
  have hc : 0 < c := hx.trans hxc
  have hcx : 0 < c-x := sub_pos.mpr hxc
  have hm := (integrable_norm_vertical_rpow (a := a+1) (by linarith) hcx).1
  have hπ : (2*π:ℝ) ≠ 0 := by positivity
  have hm' := (hm.comp_mul_left' hπ).const_mul (1:ℝ)
  refine hm'.mono' ?_ ?_
  · exact (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ (integrable_kummerKernel ha hx hxc)).aestronglyMeasurable
  · filter_upwards [] with ξ
    rw [fourier_kummerKernel ha hx hxc, norm_div, ← ofReal_neg, norm_cpow_real]
    have hnorm : ‖((c-x:ℝ):ℂ)+(2*π*ξ:ℝ)*I‖ ≤ ‖(c:ℂ)+(2*π*ξ:ℝ)*I‖ := by
      have h1 := norm_add_mul_I_sub_sq (c-x) (2*π*ξ) 0
      have h2 := norm_add_mul_I_sub_sq c (2*π*ξ) 0
      simp only [sub_zero, zero_re, zero_im] at h1 h2
      nlinarith [norm_nonneg (((c-x:ℝ):ℂ)+(2*π*ξ:ℝ)*I),
        norm_nonneg ((c:ℂ)+(2*π*ξ:ℝ)*I)]
    have hn : 0 < ‖((c-x:ℝ):ℂ)+(2*π*ξ:ℝ)*I‖ := norm_pos_iff.mpr
      (ne_zero_of_re_pos (by simpa using hcx))
    have he : (c:ℂ)+(2*π*ξ:ℝ)*I-x = ((c-x:ℝ):ℂ)+(2*π*ξ:ℝ)*I := by push_cast; ring
    simp only [he, one_mul]
    have hr := Real.rpow_le_rpow_of_nonpos hn hnorm (by linarith : -a ≤ 0)
    calc ‖(c:ℂ)+(2*π*ξ:ℝ)*I‖^(-a) / ‖((c-x:ℝ):ℂ)+(2*π*ξ:ℝ)*I‖
        ≤ ‖((c-x:ℝ):ℂ)+(2*π*ξ:ℝ)*I‖^(-a) /
          ‖((c-x:ℝ):ℂ)+(2*π*ξ:ℝ)*I‖ := div_le_div_of_nonneg_right hr hn.le
      _ = _ := by
        rw [← Real.rpow_sub_one hn.ne']
        congr 1
        ring

/-- The time-domain product is a single regularized Kummer Laplace integral. -/
theorem integral_kummerKernel_mul_gammaKernel {a b x c : ℝ} (ha : 0 < a) (hb : 0 < b)
    (_hx : 0 < x) (hx1 : x < 1) :
    (∫ t : ℝ, kummerKernel a x c t * gammaKernel b (1-c) t) =
      Gamma ((a:ℂ)+b) * regularizedGaussHypergeometric 1 ((a:ℂ)+b) ((a:ℂ)+1) x := by
  simp only [kummerKernel, gammaKernel, ← indicator_mul, integral_indicator measurableSet_Ioi]
  have h := laplace_regularizedHGFun (a := 1) (b := (a:ℂ)+b) (c := (a:ℂ)+1)
    (k := x) (z := 1) (by simp; linarith) (by simpa) (by simp)
  simp only [one_cpow, mul_one, div_one] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have he : exp (-(c:ℂ)*t) * exp (-((1-c:ℝ):ℂ)*t) = exp (-(1:ℂ)*t) := by
    rw [← Complex.exp_add]; push_cast; congr 1; ring
  have hp : (t:ℂ)^(a:ℂ) * (t:ℂ)^((b:ℂ)-1) = (t:ℂ)^((a:ℂ)+b-1) := by
    rw [← cpow_add _ _ (ofReal_ne_zero.mpr ht.ne')]; congr 1; ring
  linear_combination (t:ℂ)^(a:ℂ) * (t:ℂ)^((b:ℂ)-1) *
    regularizedHGFun {1} {(a:ℂ)+1} ((x:ℂ)*t) * he +
    exp (-(1:ℂ)*t) * regularizedHGFun {1} {(a:ℂ)+1} ((x:ℂ)*t) * hp

/-- The vertical incomplete-Beta integrand is absolutely integrable, and its integral
is the regularized Gauss expression for the incomplete Beta function. -/
theorem integral_vertical {a b x c : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hx : 0 < x) (hxc : x < c) (hc1 : c < 1) :
    let F := fun y : ℝ => let s : ℂ := c+y*I;
      s^(-(a:ℂ))*(1-s)^(-(b:ℂ))/(s-x)
    Integrable F ∧ (∫ y, F y) = 2*π * Gamma ((a:ℂ)+b) / Gamma b *
      regularizedGaussHypergeometric 1 ((a:ℂ)+b) ((a:ℂ)+1) x := by
  dsimp only
  let F := fun y : ℝ => let s : ℂ := c+y*I;
    s^(-(a:ℂ))*(1-s)^(-(b:ℂ))/(s-x)
  have hπ : (2*π:ℝ) ≠ 0 := by positivity
  have hg := integrable_gammaKernel hb (sub_pos.mpr hc1)
  have hq := integrable_kummerKernel ha hx hxc
  have hQ := integrable_fourier_kummerKernel ha hx hxc
  have hGcont : Continuous (𝓕 (gammaKernel b (1-c))) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hg
  have hfreq (ξ : ℝ) :
      𝓕 (gammaKernel b (1-c)) (-ξ) * 𝓕 (kummerKernel a x c) ξ =
        Gamma b * F (2*π*ξ) := by
    rw [fourier_gammaKernel hb (sub_pos.mpr hc1), fourier_kummerKernel ha hx hxc]
    have he : ((1-c:ℝ):ℂ)+(2*π*(-ξ):ℝ)*I = 1-((c:ℂ)+(2*π*ξ:ℝ)*I) := by
      push_cast
      ring
    rw [he]
    dsimp only [F]
    ring
  have hfreqInt := hQ.bdd_mul (hGcont.comp continuous_neg).aestronglyMeasurable
    (ae_of_all _ fun ξ => Real.norm_fourier_le_integral_norm (gammaKernel b (1-c)) (-ξ))
  have hGb : Gamma (b:ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by simpa using hb)
  have hscaleInt : Integrable (fun ξ : ℝ => F (2*π*ξ)) := by
    apply (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hGb) _).mp
    exact hfreqInt.congr (ae_of_all _ hfreq)
  have hF : Integrable F := (integrable_comp_mul_left_iff F hπ).mp hscaleInt
  refine ⟨hF, ?_⟩
  have hp := Real.integral_mul_eq_integral_fourier_neg_mul hg hq hQ
  have htime : (∫ t : ℝ, gammaKernel b (1-c) t * kummerKernel a x c t) =
      Gamma ((a:ℂ)+b) * regularizedGaussHypergeometric 1 ((a:ℂ)+b) ((a:ℂ)+1) x := by
    simpa only [mul_comm] using integral_kummerKernel_mul_gammaKernel (c := c)
      ha hb hx (hxc.trans hc1)
  rw [htime] at hp
  have hscale := Measure.integral_comp_mul_left F (2*π)
  simp only [abs_of_pos (inv_pos.mpr (by positivity : 0 < (2*π:ℝ))),
    Complex.real_smul, ofReal_inv, ofReal_mul, ofReal_ofNat] at hscale
  have hr : (∫ ξ : ℝ, 𝓕 (gammaKernel b (1-c)) (-ξ) * 𝓕 (kummerKernel a x c) ξ) =
      Gamma b * ((2*π:ℂ)⁻¹ * ∫ y, F y) := by
    simp_rw [hfreq]
    rw [integral_const_mul, hscale]
  rw [hr] at hp
  have hπc : (2*π:ℂ) ≠ 0 := by exact_mod_cast hπ
  apply (mul_left_cancel₀ hGb)
  calc Gamma (b:ℂ) * (∫ y, F y) = (2*π:ℂ) *
        (Gamma ((a:ℂ)+b) * regularizedGaussHypergeometric 1 ((a:ℂ)+b) ((a:ℂ)+1) x) := by
          rw [hp]
          field_simp
    _ = _ := by field_simp

end DLMF.Confluent.IncompleteBetaBarnes
