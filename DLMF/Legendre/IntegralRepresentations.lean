/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.Neumann
public import DLMF.Legendre.IntegralTools
public import DLMF.Legendre.Singularities
public import DLMF.Hypergeometric.EulerHalfLine
public import Mathlib.Analysis.SpecialFunctions.Arcosh

/-!
# Integral representations and fractional integration

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Legendre

/-! ### Helpers for DLMF 14.12.6 and 14.25.1–2 (prefix `legInt_`) -/

/-- Splitting a principal power of a product when the imaginary parts have opposite signs. -/
theorem legInt_cpow_mul_of_im {A B : ℂ} (hA : A ∈ slitPlane) (hB : B ≠ 0)
    (h : A.im = 0 ∨ A.im * B.im < 0) (p : ℂ) : (A * B) ^ p = A ^ p * B ^ p := by
  have hA0 : A ≠ 0 := slitPlane_ne_zero hA
  have hlog : log (A * B) = log A + log B := by
    rw [log_mul_eq_add_log_iff hA0 hB]
    have h1 := neg_pi_lt_arg A; have h2 := arg_le_pi A
    have h3 := neg_pi_lt_arg B; have h4 := arg_le_pi B
    rcases h with h | h
    · have : arg A = 0 := by
        rw [arg_eq_zero_iff]; refine ⟨?_, h⟩
        rcases (mem_slitPlane_iff.mp hA) with h' | h'
        · exact h'.le
        · exact absurd h h'
      rw [this, zero_add]; exact ⟨h3, h4⟩
    · rcases lt_or_gt_of_ne (show A.im ≠ 0 by rintro h0; simp [h0] at h) with ha | ha
      · have hb : 0 < B.im := by nlinarith
        have := arg_neg_iff.mpr ha
        have := arg_nonneg_iff.mpr hb.le
        constructor <;> linarith
      · have hb : B.im < 0 := by nlinarith
        have := arg_neg_iff.mpr hb
        have := arg_nonneg_iff.mpr ha.le
        constructor <;> linarith
  rw [cpow_def_of_ne_zero (mul_ne_zero hA0 hB), cpow_def_of_ne_zero hA0, cpow_def_of_ne_zero hB,
    hlog, add_mul, exp_add]

/-- The half-angle substitution `s = tanh²(t/2) = (cosh t - 1)/(cosh t + 1)`. -/
noncomputable def legInt_hs (t : ℝ) : ℝ := (Real.cosh t - 1) / (Real.cosh t + 1)

/-- Its derivative `2 sinh t/(cosh t + 1)²`. -/
noncomputable def legInt_hs' (t : ℝ) : ℝ := 2 * Real.sinh t / (Real.cosh t + 1) ^ 2

/-- Derivative of the half-angle substitution. -/
theorem legInt_hasDerivAt_hs (t : ℝ) : HasDerivAt legInt_hs (legInt_hs' t) t := by
  have hc : 0 < Real.cosh t + 1 := by linarith [Real.cosh_pos t]
  have h := ((Real.hasDerivAt_cosh t).sub_const 1).div ((Real.hasDerivAt_cosh t).add_const 1) hc.ne'
  unfold legInt_hs legInt_hs'
  convert h using 1
  field_simp; ring

/-- The half-angle substitution maps `(0, ∞)` onto `(0, 1)`. -/
theorem legInt_image_hs : legInt_hs '' Ioi 0 = Ioo 0 1 := by
  ext s; constructor
  · rintro ⟨t, ht, rfl⟩
    have h1 : 1 < Real.cosh t := Real.one_lt_cosh.mpr (ne_of_gt ht)
    refine ⟨div_pos (by linarith) (by linarith), (div_lt_one (by linarith)).mpr (by linarith)⟩
  · rintro ⟨h0, h1⟩
    have hq : 1 < (1+s)/(1-s) := by rw [one_lt_div (by linarith)]; linarith
    refine ⟨Real.arcosh ((1+s)/(1-s)), Real.arcosh_pos hq, ?_⟩
    rw [legInt_hs, Real.cosh_arcosh hq.le]
    have : (1:ℝ) - s ≠ 0 := by linarith
    field_simp; ring

/-- The half-angle substitution is injective on `(0, ∞)`. -/
theorem legInt_injOn_hs : InjOn legInt_hs (Ioi 0) := by
  intro u hu v hv he
  have hu1 : 0 < Real.cosh u + 1 := by linarith [Real.cosh_pos u]
  have hv1 : 0 < Real.cosh v + 1 := by linarith [Real.cosh_pos v]
  simp only [legInt_hs] at he
  rw [div_eq_div_iff hu1.ne' hv1.ne'] at he
  have hc : Real.cosh u = Real.cosh v := by linarith
  have : |u| = |v| := by
    rcases lt_trichotomy |u| |v| with h | h | h
    · exact absurd hc (ne_of_lt (Real.cosh_lt_cosh.mpr h))
    · exact h
    · exact absurd hc (ne_of_gt (Real.cosh_lt_cosh.mpr h))
  rwa [abs_of_pos (show (0:ℝ) < u from hu), abs_of_pos (show (0:ℝ) < v from hv)] at this

/-- Change of variables `s = tanh²(t/2)` from `(0,1)` to `(0,∞)`. -/
theorem legInt_hs_cov {g : ℝ → ℂ} (hg : IntegrableOn g (Ioo 0 1)) :
    IntegrableOn (fun t => |legInt_hs' t| • g (legInt_hs t)) (Ioi 0) ∧
      ∫ t in Ioi 0, |legInt_hs' t| • g (legInt_hs t) = ∫ s in Ioo 0 1, g s := by
  have hd : ∀ t ∈ Ioi (0:ℝ), HasDerivWithinAt legInt_hs (legInt_hs' t) (Ioi 0) t :=
    fun t _ => (legInt_hasDerivAt_hs t).hasDerivWithinAt
  have hcov := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hd legInt_injOn_hs g
  have hcovI := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hd
    legInt_injOn_hs g
  rw [legInt_image_hs] at hcov hcovI
  exact ⟨hcovI.mp hg, hcov.symm⟩

/-- `z + c = (z+1) (c+1)/2 (1 - x s)`, `x = (z-1)/(z+1)`, `s = (c-1)/(c+1)`, split into powers. -/
theorem legInt_cpow_z_add_cosh {z : ℂ} (hz : z+1 ∈ slitPlane) {t : ℝ} (ht : 0 < t) (p : ℂ) :
    (z + Real.cosh t) ^ p = (z+1)^p * (((Real.cosh t + 1)/2 : ℝ) : ℂ)^p *
      (1 - (z-1)/(z+1) * (legInt_hs t : ℂ))^p := by
  have hc1 : 1 < Real.cosh t := Real.one_lt_cosh.mpr (ne_of_gt ht)
  have hA0 : z + 1 ≠ 0 := slitPlane_ne_zero hz
  have hcp : (Real.cosh t : ℂ) + 1 ≠ 0 := by exact_mod_cast (show Real.cosh t + 1 ≠ 0 by linarith)
  set B : ℂ := 1 - (z-1)/(z+1) * (legInt_hs t : ℂ)
  have hzc : z + Real.cosh t ≠ 0 := by
    intro h0
    have h1 := congrArg re h0; have h2 := congrArg im h0
    simp at h1 h2
    rcases mem_slitPlane_iff.mp hz with h | h
    · simp at h; linarith
    · simp at h; exact h h2
  have hBe : B = 2 * (z + Real.cosh t) / ((z+1) * (Real.cosh t + 1)) := by
    simp only [B, legInt_hs, ofReal_div, ofReal_sub, ofReal_add, ofReal_one]; field_simp; ring
  have hB0 : B ≠ 0 := by rw [hBe]; exact div_ne_zero (mul_ne_zero two_ne_zero hzc) (mul_ne_zero hA0 hcp)
  have hr : (0:ℝ) < (Real.cosh t + 1)/2 := by linarith
  have hrB : (((Real.cosh t + 1)/2 : ℝ) : ℂ) * B = (z + Real.cosh t)/(z+1) := by
    rw [hBe, ofReal_div, ofReal_add, ofReal_one, ofReal_ofNat]; field_simp
  have hsplit2 := legInt_cpow_mul_of_im (A := (((Real.cosh t + 1)/2 : ℝ) : ℂ)) (B := B)
    (Or.inl hr) hB0 (Or.inl (by simp)) p
  have him : (z+1).im = 0 ∨ (z+1).im * ((z + Real.cosh t)/(z+1)).im < 0 := by
    by_cases h0 : (z+1).im = 0
    · exact Or.inl h0
    · right
      have e : (z + Real.cosh t)/(z+1) = 1 + ((Real.cosh t - 1 : ℝ) : ℂ) * (z+1)⁻¹ := by
        rw [ofReal_sub, ofReal_one]; field_simp; ring
      have e2 : ((1:ℂ) + ((Real.cosh t - 1 : ℝ):ℂ) * (z+1)⁻¹).im =
          (Real.cosh t - 1) * (-(z+1).im / normSq (z+1)) := by
        rw [add_im, one_im, zero_add, im_ofReal_mul, inv_im]
      rw [e, e2]
      have hn : 0 < normSq (z+1) := normSq_pos.mpr hA0
      have : (z+1).im * ((Real.cosh t - 1) * (-(z+1).im / normSq (z+1))) =
          -((Real.cosh t - 1) * (z+1).im^2 / normSq (z+1)) := by ring
      rw [this, neg_lt_zero]
      exact div_pos (mul_pos (by linarith) (by positivity)) hn
  have hsplit1 := legInt_cpow_mul_of_im hz (div_ne_zero hzc hA0) him p
  rw [mul_div_cancel₀ _ hA0] at hsplit1
  rw [hsplit1, ← hrB, hsplit2, mul_assoc]

/-- Real logarithms along the half-angle substitution. -/
theorem legInt_hs_logs {t : ℝ} (ht : 0 < t) :
    2 * Real.log (Real.sinh t) = Real.log (Real.cosh t - 1) + Real.log (Real.cosh t + 1) ∧
    Real.log |legInt_hs' t| = Real.log 2 + Real.log (Real.sinh t) - 2 * Real.log (Real.cosh t + 1) ∧
    Real.log (legInt_hs t) = Real.log (Real.cosh t - 1) - Real.log (Real.cosh t + 1) ∧
    Real.log (1 - legInt_hs t) = Real.log 2 - Real.log (Real.cosh t + 1) ∧
    Real.log ((Real.cosh t + 1)/2) = Real.log (Real.cosh t + 1) - Real.log 2 := by
  have hc1 : 1 < Real.cosh t := Real.one_lt_cosh.mpr (ne_of_gt ht)
  have hs : 0 < Real.sinh t := Real.sinh_pos_iff.mpr ht
  have hp : 0 < Real.cosh t + 1 := by linarith
  have hm : 0 < Real.cosh t - 1 := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← Real.log_mul hm.ne' hp.ne', show (Real.cosh t - 1) * (Real.cosh t + 1) = Real.sinh t ^ 2 by
      nlinarith [Real.cosh_sq_sub_sinh_sq t], Real.log_pow]; push_cast; ring
  · rw [legInt_hs', abs_of_pos (by positivity), Real.log_div (by positivity) (by positivity),
      Real.log_mul two_ne_zero hs.ne', Real.log_pow]; push_cast; ring
  · rw [legInt_hs, Real.log_div hm.ne' hp.ne']
  · rw [show 1 - legInt_hs t = 2 / (Real.cosh t + 1) by rw [legInt_hs]; field_simp; ring,
      Real.log_div two_ne_zero hp.ne']
  · rw [Real.log_div hp.ne' two_ne_zero]

/-- The integrand of DLMF 14.25.1 after the substitution `s = tanh²(t/2)`. -/
theorem legInt_kernel_P {ν μ z : ℂ} (hz : z+1 ∈ slitPlane) {t : ℝ} (ht : 0 < t) :
    (Real.sinh t:ℂ)^(2*ν+1) / (z+Real.cosh t)^(ν+μ+1) = 2^(2*ν+1) * ((z+1)^(ν+μ+1))⁻¹ *
      (|legInt_hs' t| • eulerKernel (ν+μ+1) (ν+1) (μ+1) ((z-1)/(z+1)) (legInt_hs t)) := by
  have hc1 : 1 < Real.cosh t := Real.one_lt_cosh.mpr (ne_of_gt ht)
  have hs : 0 < Real.sinh t := Real.sinh_pos_iff.mpr ht
  have hs0 : 0 < legInt_hs t := div_pos (by linarith) (by linarith)
  have hs1 : 0 < 1 - legInt_hs t := by
    rw [show 1 - legInt_hs t = 2 / (Real.cosh t + 1) by rw [legInt_hs]; field_simp; ring]
    exact div_pos two_pos (by linarith)
  have hr : 0 < (Real.cosh t + 1)/2 := by linarith
  have hd : 0 < |legInt_hs' t| := abs_pos.mpr (by rw [legInt_hs']; positivity)
  obtain ⟨l1, l2, l3, l4, l5⟩ := legInt_hs_logs ht
  have hA0 : z + 1 ≠ 0 := slitPlane_ne_zero hz
  have hX0 : 1 - (z-1)/(z+1) * (legInt_hs t : ℂ) ≠ 0 := by
    have hc : (z-1)/(z+1) ∈ cutPlane := by
      rw [mem_cutPlane, show 1 - (z-1)/(z+1) = 2 * (z+1)⁻¹ by field_simp; ring]
      have := recip_mem_slitPlane' hz
      rcases mem_slitPlane_iff.mp this with h | h
      · exact Or.inl (by simpa using h)
      · exact Or.inr (by simpa using h)
    exact slitPlane_ne_zero (one_sub_mul_mem_slitPlane hc ⟨hs0.le, by linarith⟩)
  rw [legInt_cpow_z_add_cosh hz ht, eulerKernel, real_smul,
    show (1:ℂ) - (legInt_hs t : ℂ) = ((1 - legInt_hs t : ℝ) : ℂ) by push_cast; ring,
    cpow_neg, show (2:ℂ)^(2*ν+1) = ((2:ℝ):ℂ)^(2*ν+1) by norm_num,
    legInt_cpow_ofReal hs, legInt_cpow_ofReal two_pos, legInt_cpow_ofReal hr,
    legInt_cpow_ofReal hs0, legInt_cpow_ofReal hs1,
    show ((|legInt_hs' t| : ℝ) : ℂ) = exp (Real.log |legInt_hs' t| : ℂ) by
      rw [← ofReal_exp, Real.exp_log hd]]
  have hA : (z+1)^(ν+μ+1) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hA0)
  have hX : (1 - (z-1)/(z+1) * (legInt_hs t : ℂ))^(ν+μ+1) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hX0)
  have key : exp (Real.log (Real.sinh t) * (2*ν+1)) = exp (Real.log 2 * (2*ν+1)) *
      exp (Real.log |legInt_hs' t| : ℂ) * exp (Real.log (legInt_hs t) * (ν+1-1)) *
      exp (Real.log (1 - legInt_hs t) * (μ+1-(ν+1)-1)) *
      exp (Real.log ((Real.cosh t + 1)/2) * (ν+μ+1)) := by
    simp only [← exp_add]
    congr 1
    rw [l2, l3, l4, l5]
    have l1' : (2:ℂ) * Real.log (Real.sinh t) = Real.log (Real.cosh t - 1) + Real.log (Real.cosh t + 1) := by
      exact_mod_cast l1
    push_cast
    linear_combination ν * l1'
  rw [key]
  field_simp

/-- `x = (z-1)/(z+1)` lies in the cut plane. -/
theorem legInt_ratio_mem_cutPlane {z : ℂ} (hz : z+1 ∈ slitPlane) : (z-1)/(z+1) ∈ cutPlane := by
  have hA0 : z + 1 ≠ 0 := slitPlane_ne_zero hz
  rw [mem_cutPlane, show 1 - (z-1)/(z+1) = 2 * (z+1)⁻¹ by field_simp; ring]
  have := recip_mem_slitPlane' hz
  rcases mem_slitPlane_iff.mp this with h | h
  · exact Or.inl (by simpa using h)
  · exact Or.inr (by simpa using h)

/-- Pfaff's transformation in the form needed for DLMF 14.25.1. -/
theorem legInt_associatedP_pfaff (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    associatedP ν (-μ) z = exp (-μ/2*(log (z+1)-log (z-1))) * ((z+1)/2)^(-(ν+1)) *
      regularizedGaussHG (ν+μ+1) (ν+1) (μ+1) ((z-1)/(z+1)) := by
  have hz1 := one_add_mem_slitPlane_of_sub_one hz
  have hz1' : z+1 ∈ slitPlane := by simpa [add_comm] using hz1
  have hA0 : z + 1 ≠ 0 := slitPlane_ne_zero hz1'
  have hw := mem_cutPlane_of_one_add hz1
  rw [associatedP, regularizedGaussHG_pfaff _ _ _ hw,
    show (1-z)/2/((1-z)/2-1) = (z-1)/(z+1) by
      rw [show (1-z)/2 - 1 = -((z+1)/2) by ring]; field_simp; ring,
    regularizedGaussHG_symm _ _ _ (legInt_ratio_mem_cutPlane hz1'),
    show (1:ℂ) - (1-z)/2 = (z+1)/2 by ring, show (1:ℂ) - -μ - -ν = ν+μ+1 by ring,
    show (1:ℂ) - -μ = μ+1 by ring, show -μ/2 = (-μ)/2 by ring]
  ring

/-- DLMF 14.25.1, proved by the substitution `s = tanh²(t/2)`, Euler's integral and Pfaff. -/
theorem legInt_associatedP_complex_integral {ν μ : ℂ} (h0 : -1 < ν.re) (h1 : ν.re < μ.re) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    HasIntegralAtTop (fun t : ℝ => legendreBranchPower μ z/(2^ν*Gamma (μ-ν)*Gamma (ν+1))*((Real.sinh t:ℂ)^(2*ν+1)/(z+Real.cosh t)^(ν+μ+1))) 0 (associatedP ν (-μ) z) := by
  have hz1' : z+1 ∈ slitPlane := by simpa [add_comm] using one_add_mem_slitPlane_of_sub_one hz
  have hA0 : z + 1 ≠ 0 := slitPlane_ne_zero hz1'
  have hx := legInt_ratio_mem_cutPlane hz1'
  have hb : 0 < (ν+1).re := by simp; linarith
  have hcb : 0 < (μ+1-(ν+1)).re := by simp; linarith
  have hg := intervalIntegrable_eulerKernel (a := ν+μ+1) hb hcb hx
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one,
    integrableOn_Ioc_iff_integrableOn_Ioo] at hg
  obtain ⟨hI, hE⟩ := legInt_hs_cov hg
  set K : ℂ := legendreBranchPower μ z/(2^ν*Gamma (μ-ν)*Gamma (ν+1)) *
    (2^(2*ν+1) * ((z+1)^(ν+μ+1))⁻¹)
  have hf : ∀ t ∈ Ioi (0:ℝ), K * (|legInt_hs' t| • eulerKernel (ν+μ+1) (ν+1) (μ+1) ((z-1)/(z+1))
      (legInt_hs t)) = legendreBranchPower μ z/(2^ν*Gamma (μ-ν)*Gamma (ν+1))*
        ((Real.sinh t:ℂ)^(2*ν+1)/(z+Real.cosh t)^(ν+μ+1)) := by
    intro t ht
    rw [legInt_kernel_P hz1' ht]; simp only [K]; ring
  have hint := IntegrableOn.congr_fun (hI.const_mul K) hf measurableSet_Ioi
  have hval := setIntegral_congr_fun (μ := volume) measurableSet_Ioi hf
  rw [integral_const_mul, hE] at hval
  have hG := regularizedGaussHG_eq_regularizedGaussHGIntegral (a := ν+μ+1) hb hcb hx
  rw [regularizedGaussHGIntegral, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo] at hG
  have hG1 : Gamma (ν+1) ≠ 0 := Gamma_ne_zero_of_re_pos hb
  have hG2 : Gamma (μ-ν) ≠ 0 := Gamma_ne_zero_of_re_pos (by simpa using hcb)
  have hint' : ∫ s in Ioo (0:ℝ) 1, eulerKernel (ν+μ+1) (ν+1) (μ+1) ((z-1)/(z+1)) s =
      Gamma (ν+1) * Gamma (μ-ν) * regularizedGaussHG (ν+μ+1) (ν+1) (μ+1) ((z-1)/(z+1)) := by
    rw [hG, show μ+1-(ν+1) = μ-ν by ring]; field_simp
  rw [hint'] at hval
  have hlim := intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id
  rw [← hval] at hlim
  suffices hv : K * (Gamma (ν + 1) * Gamma (μ - ν) *
      regularizedGaussHG (ν + μ + 1) (ν + 1) (μ + 1) ((z - 1) / (z + 1))) = associatedP ν (-μ) z by
    rw [hv] at hlim; exact hlim
  rw [legInt_associatedP_pfaff ν μ hz]
  simp only [K]
  have h2 : (2:ℂ) = ((2:ℝ):ℂ) := by norm_num
  have hl : log ((z+1)/2) = log (z+1) - Real.log 2 := by
    rw [div_eq_mul_inv, show (2:ℂ)⁻¹ = ((2⁻¹:ℝ):ℂ) by push_cast; ring,
      log_mul_ofReal _ (by norm_num) _ hA0, Real.log_inv]; push_cast; ring
  rw [h2, legInt_cpow_ofReal two_pos, legInt_cpow_ofReal two_pos, ← h2,
    cpow_def_of_ne_zero (div_ne_zero hA0 two_ne_zero), hl, cpow_def_of_ne_zero hA0,
    legendreBranchPower]
  have e : exp (μ/2*(log (z-1)+log (z+1))) * exp (Real.log 2 * (2*ν+1)) =
      exp (-μ/2*(log (z+1)-log (z-1))) * exp ((log (z+1) - Real.log 2)*(-(ν+1))) *
        exp (Real.log 2 * ν) * exp (log (z+1) * (ν+μ+1)) := by
    simp only [← exp_add]; congr 1; ring
  have : exp (Real.log 2 * ν) ≠ 0 := exp_ne_zero _
  have : exp (log (z+1) * (ν+μ+1)) ≠ 0 := exp_ne_zero _
  rw [(eq_div_iff (exp_ne_zero _)).mpr e]
  field_simp

/-! ### The inverse Joukowski map (copied from `Legendre/FourierTools.lean`, which is downstream) -/
/-- The square root `√(z²-1)` continued from `z > 1` to `ℂ ∖ (-∞, 1]`. -/
noncomputable def legInt_root (z : ℂ) : ℂ := exp ((log (z-1) + log (z+1))/2)

/-- The inverse Joukowski map `ζ = z - √(z²-1)`, so that `z = (ζ + ζ⁻¹)/2` and `|ζ| < 1`. -/
noncomputable def legInt_zeta (z : ℂ) : ℂ := z - legInt_root z

/-- `z+1 ∈ slitPlane` when `z-1 ∈ slitPlane`. -/
theorem legInt_add_one {z : ℂ} (hz : z-1 ∈ slitPlane) : z+1 ∈ slitPlane := by
  simpa [add_comm] using one_add_mem_slitPlane_of_sub_one hz

/-- `(√(z²-1))² = z²-1`. -/
theorem legInt_root_sq {z : ℂ} (hz : z-1 ∈ slitPlane) : legInt_root z ^ 2 = z^2 - 1 := by
  rw [legInt_root, ← exp_nat_mul, show ((2:ℕ):ℂ) * ((log (z-1) + log (z+1))/2) =
    log (z-1) + log (z+1) by push_cast; ring, exp_add, exp_log (slitPlane_ne_zero hz),
    exp_log (slitPlane_ne_zero (legInt_add_one hz))]
  ring

/-- `ζ (z + √(z²-1)) = 1`, written as `ζ (2z - ζ) = 1`. -/
theorem legInt_zeta_mul {z : ℂ} (hz : z-1 ∈ slitPlane) : legInt_zeta z * (2*z - legInt_zeta z) = 1 := by
  have := legInt_root_sq hz
  rw [legInt_zeta]; linear_combination -this

/-- `ζ ≠ 0`. -/
theorem legInt_zeta_ne_zero {z : ℂ} (hz : z-1 ∈ slitPlane) : legInt_zeta z ≠ 0 := by
  intro h; have := legInt_zeta_mul hz; rw [h, zero_mul] at this; exact zero_ne_one this

/-- `2z = ζ + ζ⁻¹`. -/
theorem legInt_two_mul_eq {z : ℂ} (hz : z-1 ∈ slitPlane) :
    2*z = legInt_zeta z + (legInt_zeta z)⁻¹ := by
  have h0 := legInt_zeta_ne_zero hz
  have := legInt_zeta_mul hz
  field_simp
  linear_combination this

/-- A point of `ℂ ∖ (-∞, 1]` is not a real number `≤ 1`. -/
theorem legInt_not_real_le_one {z : ℂ} (hz : z-1 ∈ slitPlane) {r : ℝ} (hr : r ≤ 1) : z ≠ r := by
  rintro rfl
  rw [mem_slitPlane_iff] at hz
  simp at hz; linarith

/-- `|ζ| ≠ 1` off `(-∞, 1]`: otherwise `z = Re ζ ∈ [-1, 1]`. -/
theorem legInt_norm_zeta_ne_one {z : ℂ} (hz : z-1 ∈ slitPlane) : ‖legInt_zeta z‖ ≠ 1 := by
  intro h1
  set w := legInt_zeta z
  have h0 : w ≠ 0 := legInt_zeta_ne_zero hz
  have hinv : w⁻¹ = (starRingEnd ℂ) w := by
    rw [inv_def, normSq_eq_norm_sq, h1]; simp
  have h2 := legInt_two_mul_eq hz
  rw [hinv, add_conj] at h2
  have hz' : z = ((w.re:ℝ):ℂ) := by
    push_cast at h2; linear_combination h2/2
  refine legInt_not_real_le_one hz (r := w.re) ?_ hz'
  have := re_le_norm w; linarith

/-- For real `t > 1`, `ζ(t) = t - √(t²-1)`. -/
theorem legInt_zeta_real {t : ℝ} (ht : 1 < t) : legInt_zeta t = ((t - Real.sqrt (t^2-1) : ℝ) : ℂ) := by
  have hl : log ((t:ℂ)-1) + log ((t:ℂ)+1) = ((Real.log (t^2-1) : ℝ) : ℂ) := by
    rw [show (t:ℂ)-1 = ((t-1:ℝ):ℂ) by push_cast; ring, show (t:ℂ)+1 = ((t+1:ℝ):ℂ) by push_cast; ring,
      ← ofReal_log (by linarith), ← ofReal_log (by linarith), ← ofReal_add,
      ← Real.log_mul (by linarith) (by linarith)]
    congr 2; ring
  rw [legInt_zeta, legInt_root, hl, show ((Real.log (t^2-1) : ℝ) : ℂ)/2 = ((Real.log (t^2-1)/2 : ℝ) : ℂ)
    by push_cast; ring, ← ofReal_exp, Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by nlinarith)]
  push_cast; ring_nf

/-- `ζ` is analytic on `ℂ ∖ (-∞, 1]`. -/
theorem legInt_zeta_analyticAt {z : ℂ} (hz : z-1 ∈ slitPlane) : AnalyticAt ℂ legInt_zeta z := by
  have h1 : AnalyticAt ℂ (fun w : ℂ => log (w-1)) z :=
    (analyticAt_clog hz).comp_of_eq (f := fun w : ℂ => w - 1) (by fun_prop) rfl
  have h2 : AnalyticAt ℂ (fun w : ℂ => log (w+1)) z :=
    (analyticAt_clog (legInt_add_one hz)).comp_of_eq (f := fun w : ℂ => w + 1) (by fun_prop) rfl
  exact analyticAt_id.sub ((h1.add h2).div_const.cexp)

/-- `0 < t - √(t²-1) < 1` for `t > 1`. -/
theorem legInt_real_bounds {t : ℝ} (ht : 1 < t) :
    0 < t - Real.sqrt (t^2-1) ∧ t - Real.sqrt (t^2-1) < 1 := by
  have h0 : 0 ≤ t^2 - 1 := by nlinarith
  have hs := Real.sq_sqrt h0
  have hs0 := Real.sqrt_nonneg (t^2-1)
  constructor
  · nlinarith
  · have : 0 < Real.sqrt (t^2-1) := Real.sqrt_pos.mpr (by nlinarith)
    nlinarith

/-- `|ζ| < 1` on `ℂ ∖ (-∞, 1]` (connectedness and `|ζ| ≠ 1`). -/
theorem legInt_norm_zeta_lt_one {z : ℂ} (hz : z-1 ∈ slitPlane) : ‖legInt_zeta z‖ < 1 := by
  by_contra h
  push Not at h
  set D : Set ℂ := {w : ℂ | w-1 ∈ slitPlane}
  have h2 : ((2:ℝ):ℂ) ∈ D := by show ((2:ℝ):ℂ) - 1 ∈ slitPlane; norm_num
  have hc : ContinuousOn (fun w => ‖legInt_zeta w‖) D := fun w hw =>
    (legInt_zeta_analyticAt hw).continuousAt.norm.continuousWithinAt
  have hlt : ‖legInt_zeta ((2:ℝ):ℂ)‖ < 1 := by
    obtain ⟨hp, hl⟩ := legInt_real_bounds (show (1:ℝ) < 2 by norm_num)
    rw [legInt_zeta_real (by norm_num), norm_real, Real.norm_eq_abs, abs_of_pos hp]
    exact hl
  obtain ⟨w, hw, hw1⟩ := isPreconnected_sub_one_mem_slitPlane.intermediate_value h2 hz hc
    ⟨hlt.le, h⟩
  exact legInt_norm_zeta_ne_one hw hw1

/-- `ζ ∉ (-∞, 0]` on `ℂ ∖ (-∞, 1]`. -/
theorem legInt_zeta_mem_slitPlane {z : ℂ} (hz : z-1 ∈ slitPlane) : legInt_zeta z ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  by_contra h
  push Not at h
  obtain ⟨hre, him⟩ := h
  set w := legInt_zeta z
  have h0 : w ≠ 0 := legInt_zeta_ne_zero hz
  have hw : w = ((w.re:ℝ):ℂ) := by apply Complex.ext <;> simp [him]
  have hre' : w.re < 0 := lt_of_le_of_ne hre (fun h => h0 (by rw [hw, h]; simp))
  have h2 : 2*z = w + w⁻¹ := legInt_two_mul_eq hz
  have hz' : z = (((w.re + (w.re)⁻¹)/2 : ℝ) : ℂ) := by
    rw [hw] at h2
    push_cast at h2 ⊢; linear_combination h2/2
  refine legInt_not_real_le_one hz ?_ hz'
  have : (w.re)⁻¹ < 0 := inv_lt_zero.mpr hre'
  linarith


/-! ### DLMF 14.25.2 -/

/-- Splitting a principal power of a product of two factors in the right half-plane. -/
theorem legInt_cpow_mul_of_re {A B : ℂ} (hA : 0 < A.re) (hB : 0 < B.re) (p : ℂ) :
    (A * B) ^ p = A ^ p * B ^ p := by
  have hA0 : A ≠ 0 := fun h => by simp [h] at hA
  have hB0 : B ≠ 0 := fun h => by simp [h] at hB
  have h1 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hA)
  have h2 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hB)
  have hlog : log (A * B) = log A + log B := by
    rw [log_mul_eq_add_log_iff hA0 hB0]
    rw [abs_lt] at h1 h2
    constructor <;> linarith [Real.pi_pos]
  rw [cpow_def_of_ne_zero (mul_ne_zero hA0 hB0), cpow_def_of_ne_zero hA0, cpow_def_of_ne_zero hB0,
    hlog, add_mul, exp_add]

/-- `z + √(z²-1) cosh t = ζ⁻¹ ((cosh t + 1)/2) (1 - ζ² s)`, split into principal powers. -/
theorem legInt_cpow_root_cosh {z : ℂ} (hz : z-1 ∈ slitPlane) {t : ℝ} (ht : 0 < t) (p : ℂ) :
    (z + legInt_root z * Real.cosh t) ^ p = ((legInt_zeta z) ^ p)⁻¹ *
      (((Real.cosh t + 1)/2 : ℝ) : ℂ)^p * (1 - (legInt_zeta z)^2 * (legInt_hs t : ℂ))^p := by
  set ζ := legInt_zeta z with hζ
  have hζ0 : ζ ≠ 0 := legInt_zeta_ne_zero hz
  have hζs : ζ ∈ slitPlane := legInt_zeta_mem_slitPlane hz
  have hζ1 : ‖ζ‖ < 1 := legInt_norm_zeta_lt_one hz
  have hc1 : 1 < Real.cosh t := Real.one_lt_cosh.mpr (ne_of_gt ht)
  have hs0 : 0 < legInt_hs t := div_pos (by linarith) (by linarith)
  have hs1 : legInt_hs t < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  have hr : (0:ℝ) < (Real.cosh t + 1)/2 := by linarith
  set B : ℂ := 1 - ζ^2 * (legInt_hs t : ℂ) with hB
  have hBre : 0 < B.re := by
    have : ‖ζ^2 * (legInt_hs t : ℂ)‖ < 1 := by
      rw [norm_mul, norm_pow, norm_real, Real.norm_eq_abs, abs_of_pos hs0]
      have : ‖ζ‖^2 < 1 := by nlinarith [norm_nonneg ζ]
      nlinarith
    have := re_le_norm (ζ^2 * (legInt_hs t : ℂ))
    simp only [hB, sub_re, one_re]; linarith
  have hB0 : B ≠ 0 := fun h => by simp [h] at hBre
  have hroot : legInt_root z = z - ζ := by simp [hζ, legInt_zeta]
  have h2z := legInt_two_mul_eq hz
  rw [← hζ] at h2z
  have halg : z + legInt_root z * Real.cosh t = (((Real.cosh t + 1)/2 : ℝ) : ℂ) * (ζ⁻¹ * B) := by
    have hcp : (Real.cosh t : ℂ) + 1 ≠ 0 := by
      exact_mod_cast (show Real.cosh t + 1 ≠ 0 by linarith)
    have hz' : z = (ζ + ζ⁻¹)/2 := by linear_combination h2z/2
    rw [hroot, hB, legInt_hs, hz']
    simp only [ofReal_div, ofReal_sub, ofReal_add, ofReal_one, ofReal_ofNat]
    field_simp; ring
  have hW0 : ζ⁻¹ * B ≠ 0 := mul_ne_zero (inv_ne_zero hζ0) hB0
  rw [halg, legInt_cpow_mul_of_im (Or.inl hr) hW0 (Or.inl (by simp)) p]
  have hsplit : (ζ⁻¹ * B)^p = (ζ⁻¹)^p * B^p := by
    rcases lt_or_ge 0 ζ.re with h | h
    · refine legInt_cpow_mul_of_re ?_ hBre p
      rw [inv_re]; exact div_pos h (normSq_pos.mpr hζ0)
    · have him : ζ.im ≠ 0 := by
        rcases mem_slitPlane_iff.mp hζs with h' | h'
        · linarith
        · exact h'
      have hBim : B.im = -(legInt_hs t * (2 * ζ.re * ζ.im)) := by
        simp only [hB, sub_im, one_im, zero_sub, pow_two, mul_im, ofReal_re, ofReal_im]
        ring
      rcases lt_or_eq_of_le h with h' | h'
      · refine legInt_cpow_mul_of_im (recip_mem_slitPlane' hζs) hB0 (Or.inr ?_) p
        rw [inv_im, hBim]
        have hn := normSq_pos.mpr hζ0
        have : -ζ.im / normSq ζ * -(legInt_hs t * (2 * ζ.re * ζ.im)) =
            2 * legInt_hs t * ζ.re * ζ.im^2 / normSq ζ := by ring
        rw [this]
        exact div_neg_of_neg_of_pos (by
          have : 0 < ζ.im^2 := by positivity
          have : 2 * legInt_hs t * ζ.re < 0 := by nlinarith
          nlinarith) hn
      · rw [mul_comm, legInt_cpow_mul_of_im (Or.inl hBre) (inv_ne_zero hζ0)
          (Or.inl (by rw [hBim, h']; ring)) p, mul_comm]
  rw [hsplit, inv_cpow _ _ (slitPlane_arg_ne_pi hζs)]
  ring

/-- The integrand of DLMF 14.25.2 after the substitution `s = tanh²(t/2)`. -/
theorem legInt_kernel_Q {ν μ z : ℂ} (hz : z-1 ∈ slitPlane) {t : ℝ} (ht : 0 < t) :
    (Real.sinh t:ℂ)^(2*μ) / (z + legInt_root z * Real.cosh t)^(ν+μ+1) =
      2^(2*μ) * (legInt_zeta z)^(ν+μ+1) *
      (|legInt_hs' t| • eulerKernel (ν+μ+1) (μ+1/2) (ν+3/2) ((legInt_zeta z)^2) (legInt_hs t)) := by
  have hc1 : 1 < Real.cosh t := Real.one_lt_cosh.mpr (ne_of_gt ht)
  have hs : 0 < Real.sinh t := Real.sinh_pos_iff.mpr ht
  have hs0 : 0 < legInt_hs t := div_pos (by linarith) (by linarith)
  have hs1 : 0 < 1 - legInt_hs t := by
    rw [show 1 - legInt_hs t = 2 / (Real.cosh t + 1) by rw [legInt_hs]; field_simp; ring]
    exact div_pos two_pos (by linarith)
  have hr : 0 < (Real.cosh t + 1)/2 := by linarith
  have hd : 0 < |legInt_hs' t| := abs_pos.mpr (by rw [legInt_hs']; positivity)
  obtain ⟨l1, l2, l3, l4, l5⟩ := legInt_hs_logs ht
  have hζ0 := legInt_zeta_ne_zero hz
  have hX0 : 1 - (legInt_zeta z)^2 * (legInt_hs t : ℂ) ≠ 0 := by
    have hc : (legInt_zeta z)^2 ∈ cutPlane := by
      refine mem_cutPlane_of_norm_lt_one ?_
      rw [norm_pow]; have := legInt_norm_zeta_lt_one hz; nlinarith [norm_nonneg (legInt_zeta z)]
    exact slitPlane_ne_zero (one_sub_mul_mem_slitPlane hc ⟨hs0.le, by linarith⟩)
  rw [legInt_cpow_root_cosh hz ht, eulerKernel, real_smul,
    show (1:ℂ) - (legInt_hs t : ℂ) = ((1 - legInt_hs t : ℝ) : ℂ) by push_cast; ring,
    cpow_neg, show (2:ℂ)^(2*μ) = ((2:ℝ):ℂ)^(2*μ) by norm_num,
    legInt_cpow_ofReal hs, legInt_cpow_ofReal two_pos, legInt_cpow_ofReal hr,
    legInt_cpow_ofReal hs0, legInt_cpow_ofReal hs1,
    show ((|legInt_hs' t| : ℝ) : ℂ) = exp (Real.log |legInt_hs' t| : ℂ) by
      rw [← ofReal_exp, Real.exp_log hd]]
  have hA : (legInt_zeta z)^(ν+μ+1) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hζ0)
  have hX : (1 - (legInt_zeta z)^2 * (legInt_hs t : ℂ))^(ν+μ+1) ≠ 0 :=
    cpow_ne_zero_iff.mpr (Or.inl hX0)
  have key : exp (Real.log (Real.sinh t) * (2*μ)) = exp (Real.log 2 * (2*μ)) *
      exp (Real.log |legInt_hs' t| : ℂ) * exp (Real.log (legInt_hs t) * (μ+1/2-1)) *
      exp (Real.log (1 - legInt_hs t) * (ν+3/2-(μ+1/2)-1)) *
      exp (Real.log ((Real.cosh t + 1)/2) * (ν+μ+1)) := by
    simp only [← exp_add]
    congr 1
    rw [l2, l3, l4, l5]
    have l1' : (2:ℂ) * Real.log (Real.sinh t) = Real.log (Real.cosh t - 1) + Real.log (Real.cosh t + 1) := by
      exact_mod_cast l1
    push_cast
    linear_combination (μ - 1/2) * l1'
  rw [key]
  field_simp

/-- The closed form produced by the integral in DLMF 14.25.2:
`√π (z²-1)^{μ/2} 2^μ ζ^{ν+μ+1} 𝐅(ν+μ+1, μ+1/2; ν+3/2; ζ²)`. -/
noncomputable def legInt_QForm (ν μ z : ℂ) : ℂ :=
  Real.sqrt π * legendreBranchPower μ z * 2^μ * (legInt_zeta z)^(ν+μ+1) *
    regularizedGaussHG (ν+μ+1) (μ+1/2) (ν+3/2) ((legInt_zeta z)^2)

/-- `legInt_QForm ν μ` is analytic on `ℂ ∖ (-∞, 1]`. -/
theorem legInt_QForm_analyticAt (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    AnalyticAt ℂ (legInt_QForm ν μ) z := by
  have hp : z+1 ∈ slitPlane := legInt_add_one hz
  have hζ := legInt_zeta_analyticAt hz
  have hB : AnalyticAt ℂ (legendreBranchPower μ) z := by
    unfold legendreBranchPower
    fun_prop (disch := assumption)
  have hc : (legInt_zeta z)^2 ∈ cutPlane := by
    refine mem_cutPlane_of_norm_lt_one ?_
    rw [norm_pow]; have := legInt_norm_zeta_lt_one hz; nlinarith [norm_nonneg (legInt_zeta z)]
  have hF : AnalyticAt ℂ (fun w => regularizedGaussHG (ν+μ+1) (μ+1/2) (ν+3/2) ((legInt_zeta w)^2)) z :=
    (analyticAt_regularizedGaussHG _ _ _ hc).comp_of_eq (hζ.pow 2) rfl
  have hP : AnalyticAt ℂ (fun w => (legInt_zeta w)^(ν+μ+1)) z :=
    hζ.cpow analyticAt_const (legInt_zeta_mem_slitPlane hz)
  unfold legInt_QForm
  exact (((analyticAt_const.mul hB).mul analyticAt_const).mul hP).mul hF

/-- The `ζ`-form of `𝑸^μ_ν` on `(1, ∞)`, by the quadratic transformation DLMF 15.8.15. -/
theorem legInt_olverQ_eq_QForm_real (ν μ : ℂ) (hc : ∀ k : ℕ, ν + 3/2 ≠ -(k:ℂ)) {x : ℝ} (hx : 1 < x) :
    olverQ ν μ x = legInt_QForm ν μ x := by
  have hz : (x:ℂ) - 1 ∈ slitPlane := legInt_one_lt_mem hx
  obtain ⟨hq0, hq1⟩ := legInt_real_bounds hx
  set q := x - Real.sqrt (x^2-1) with hqdef
  have hζ : legInt_zeta x = (q:ℂ) := legInt_zeta_real hx
  have h2x : 2 * (x:ℂ) = q + (q:ℂ)⁻¹ := by rw [← hζ]; exact legInt_two_mul_eq hz
  have hq0' : (q:ℂ) ≠ 0 := ofReal_ne_zero.mpr hq0.ne'
  have hxr : x = (1+q^2)/(2*q) := by
    have : (2*x:ℝ) = q + q⁻¹ := by exact_mod_cast h2x
    field_simp; linarith [this, show q * q⁻¹ = 1 from mul_inv_cancel₀ hq0.ne', show (2*x)*q = q*q + q⁻¹*q by rw [this]; ring,
      show q⁻¹ * q = 1 from inv_mul_cancel₀ hq0.ne']
  have hx0 : 0 < x := by linarith
  have hn1 : ‖((q^2:ℝ):ℂ)‖ < 1 := by
    rw [norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]; nlinarith
  have harg : 1/(x:ℂ)^2 = 4*((q^2:ℝ):ℂ)/(1+((q^2:ℝ):ℂ))^2 := by
    rw [hxr]; push_cast; field_simp; norm_num
  have hn2 : ‖4*((q^2:ℝ):ℂ)/(1+((q^2:ℝ):ℂ))^2‖ < 1 := by
    rw [← harg, norm_div, norm_one, norm_pow, norm_real, Real.norm_eq_abs, abs_of_pos hx0]
    rw [div_lt_one (by positivity)]; nlinarith
  have hc' : ∀ k : ℕ, ν + μ + 1 - (μ + 1/2) + 1 ≠ -(k:ℂ) := by
    intro k; rw [show ν + μ + 1 - (μ + 1/2) + 1 = ν + 3/2 by ring]; exact hc k
  have hqt := quadratic_well_poised_plus (a := ν+μ+1) (b := μ+1/2) hc' hn1 hn2
  rw [show ν + μ + 1 - (μ + 1/2) + 1 = ν + 3/2 by ring] at hqt
  unfold olverQ legInt_QForm
  rw [hζ, harg, show ((q:ℂ))^2 = ((q^2:ℝ):ℂ) by push_cast; ring,
    regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hn1,
    regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hn2,
    regularizedGaussHGFun_eq_div_Gamma hc, regularizedGaussHGFun_eq_div_Gamma hc, hqt,
    ordinaryHypergeometric_symm, show (ν+μ+2)/2 = (ν+μ+1+1)/2 by ring]
  -- powers of positive reals
  have h1q : (1:ℂ) + ((q^2:ℝ):ℂ) = ((1+q^2:ℝ):ℂ) := by push_cast; ring
  have hpos : 0 < 1 + q^2 := by positivity
  rw [h1q, cpow_neg, legInt_cpow_ofReal hpos, legInt_cpow_ofReal hq0, legInt_cpow_ofReal hx0,
    show (2:ℂ)^μ = ((2:ℝ):ℂ)^μ by norm_num, show (2:ℂ)^(ν+1) = ((2:ℝ):ℂ)^(ν+1) by norm_num,
    legInt_cpow_ofReal two_pos, legInt_cpow_ofReal two_pos]
  have hl : Real.log (1+q^2) = Real.log 2 + Real.log q + Real.log x := by
    rw [← Real.log_mul two_ne_zero hq0.ne', ← Real.log_mul (by positivity) hx0.ne', hxr]
    congr 1; field_simp
  have e : exp (Real.log 2 * μ) * exp (Real.log q * (ν+μ+1)) * exp (Real.log 2 * (ν+1)) *
      exp (Real.log x * (ν+μ+1)) = exp (Real.log (1+q^2) * (ν+μ+1)) := by
    simp only [← exp_add]; congr 1; rw [hl]; push_cast; ring
  have : exp (Real.log (1+q^2) * (ν+μ+1)) ≠ 0 := exp_ne_zero _
  have : exp (Real.log 2 * (ν+1)) ≠ 0 := exp_ne_zero _
  have : exp (Real.log x * (ν+μ+1)) ≠ 0 := exp_ne_zero _
  rw [← e]
  field_simp

/-- The `ζ`-form of `𝑸^μ_ν` on `ℂ ∖ (-∞, 1]` (identity theorem from `(1, ∞)`). -/
theorem legInt_olverQ_eq_QForm (ν μ : ℂ) (hc : ∀ k : ℕ, ν + 3/2 ≠ -(k:ℂ)) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    olverQ ν μ z = legInt_QForm ν μ z := by
  set D : Set ℂ := {w : ℂ | w-1 ∈ slitPlane}
  have h2 : ((2 : ℝ) : ℂ) ∈ D := by show ((2 : ℝ) : ℂ) - 1 ∈ slitPlane; norm_num
  refine (olverQ_analytic ν μ).eqOn_of_preconnected_of_frequently_eq
    (fun w hw => legInt_QForm_analyticAt ν μ hw) isPreconnected_sub_one_mem_slitPlane h2 ?_ hz
  have ht : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[≠] (2 : ℝ)) (𝓝[≠] ((2 : ℝ) : ℂ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact (continuous_ofReal.tendsto _).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, ofReal_inj] using hr
  apply ht.frequently
  apply Eventually.frequently
  filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds (show (1 : ℝ) < 2 by norm_num))] with t ht
  exact legInt_olverQ_eq_QForm_real ν μ hc ht

/-- DLMF 14.25.2, proved by the substitution `s = tanh²(t/2)`, Euler's integral and the `ζ`-form. -/
theorem legInt_olverQ_complex_integral {ν μ : ℂ} (h0 : -1/2 < μ.re) (h1 : μ.re < (ν+1).re) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    HasIntegralAtTop (fun t : ℝ => Real.sqrt π*legendreBranchPower μ z/(2^μ*Gamma (μ+1/2)*Gamma (ν-μ+1))*((Real.sinh t:ℂ)^(2*μ)/(z+exp ((log (z-1)+log (z+1))/2)*Real.cosh t)^(ν+μ+1))) 0 (olverQ ν μ z) := by
  have hx : (legInt_zeta z)^2 ∈ cutPlane := by
    refine mem_cutPlane_of_norm_lt_one ?_
    rw [norm_pow]; have := legInt_norm_zeta_lt_one hz; nlinarith [norm_nonneg (legInt_zeta z)]
  have hb : 0 < (μ+1/2).re := by simp; linarith
  have hcb : 0 < (ν+3/2-(μ+1/2)).re := by simp at h1 ⊢; linarith
  have hg := intervalIntegrable_eulerKernel (a := ν+μ+1) hb hcb hx
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one,
    integrableOn_Ioc_iff_integrableOn_Ioo] at hg
  obtain ⟨hI, hE⟩ := legInt_hs_cov hg
  set K : ℂ := Real.sqrt π*legendreBranchPower μ z/(2^μ*Gamma (μ+1/2)*Gamma (ν-μ+1)) *
    (2^(2*μ) * (legInt_zeta z)^(ν+μ+1))
  have hf : ∀ t ∈ Ioi (0:ℝ), K * (|legInt_hs' t| • eulerKernel (ν+μ+1) (μ+1/2) (ν+3/2)
      ((legInt_zeta z)^2) (legInt_hs t)) = Real.sqrt π*legendreBranchPower μ z/(2^μ*Gamma (μ+1/2)*
        Gamma (ν-μ+1))*((Real.sinh t:ℂ)^(2*μ)/(z+exp ((log (z-1)+log (z+1))/2)*Real.cosh t)^(ν+μ+1)) := by
    intro t ht
    have := legInt_kernel_Q (ν := ν) (μ := μ) hz ht
    rw [legInt_root] at this
    rw [this]; simp only [K]; ring
  have hint := IntegrableOn.congr_fun (hI.const_mul K) hf measurableSet_Ioi
  have hval := setIntegral_congr_fun (μ := volume) measurableSet_Ioi hf
  rw [integral_const_mul, hE] at hval
  have hG := regularizedGaussHG_eq_regularizedGaussHGIntegral (a := ν+μ+1) hb hcb hx
  rw [regularizedGaussHGIntegral, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo] at hG
  have hG1 : Gamma (μ+1/2) ≠ 0 := Gamma_ne_zero_of_re_pos hb
  have hG2 : Gamma (ν-μ+1) ≠ 0 := Gamma_ne_zero_of_re_pos (by
    rw [show ν-μ+1 = ν+3/2-(μ+1/2) by ring]; exact hcb)
  have hint' : ∫ s in Ioo (0:ℝ) 1, eulerKernel (ν+μ+1) (μ+1/2) (ν+3/2) ((legInt_zeta z)^2) s =
      Gamma (μ+1/2) * Gamma (ν-μ+1) * regularizedGaussHG (ν+μ+1) (μ+1/2) (ν+3/2) ((legInt_zeta z)^2) := by
    rw [hG, show ν+3/2-(μ+1/2) = ν-μ+1 by ring, ← mul_assoc, mul_inv_cancel₀ (mul_ne_zero hG1 hG2),
      one_mul]
  rw [hint'] at hval
  have hlim := intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id
  rw [← hval] at hlim
  have hc : ∀ k : ℕ, ν + 3/2 ≠ -(k:ℂ) := by
    intro k hk
    have := congrArg re hk; simp at this h1
    linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  suffices hv : K * (Gamma (μ+1/2) * Gamma (ν-μ+1) *
      regularizedGaussHG (ν+μ+1) (μ+1/2) (ν+3/2) ((legInt_zeta z)^2)) = olverQ ν μ z by
    rw [hv] at hlim; exact hlim
  rw [legInt_olverQ_eq_QForm ν μ hc hz, legInt_QForm]
  simp only [K]
  have h22 : (2:ℂ)^(2*μ) = 2^μ * 2^μ := by
    rw [two_mul, cpow_add _ _ two_ne_zero]
  have : (2:ℂ)^μ ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl two_ne_zero)
  rw [h22]
  have hG1' : Gamma ((μ*2+1)/2) ≠ 0 := by rwa [show (μ*2+1)/2 = μ+1/2 by ring]
  field_simp




/-! ### Helpers for DLMF 14.12.4 (prefix `legInt_`) -/

/-- The half-line Euler kernel of DLMF 14.12.4 at `v = E/q`, with `2qx = 1 + q²`. -/
theorem legInt_halfLine_point (ν μ : ℂ) {x q E : ℝ} (hq : 0 < q) (hqx : 1 + q^2 = 2*q*x) (hE : 0 < E) :
    ((E/q : ℝ):ℂ) * eulerHalfLineKernel (μ+1/2) (ν+μ+1) (μ-ν) (((q^2)⁻¹ : ℝ) : ℂ) (E/q) =
      (q:ℂ)^(μ-ν) * (2:ℂ)^(-(μ+1/2)) * (E:ℂ)^(ν+1/2) * ((x + (E + E⁻¹)/2 : ℝ):ℂ)^(-(μ+1/2)) := by
  have hv : 0 < E/q := div_pos hE hq
  have hX : 0 < x + (E + E⁻¹)/2 := by
    have : 0 < x := by nlinarith
    positivity
  have hsum : Real.log (q+E) + Real.log (1+q*E) =
      Real.log E + Real.log 2 + Real.log q + Real.log (x + (E + E⁻¹)/2) := by
    rw [← Real.log_mul (by positivity) (by positivity), ← Real.log_mul hE.ne' two_ne_zero,
      ← Real.log_mul (by positivity) hq.ne', ← Real.log_mul (by positivity) hX.ne']
    congr 1
    field_simp
    nlinarith [hqx]
  have l1 : Real.log (E/q) = Real.log E - Real.log q := Real.log_div hE.ne' hq.ne'
  have l2 : Real.log (1 + E/q) = Real.log (q+E) - Real.log q := by
    rw [← Real.log_div (by positivity) hq.ne']; congr 1; field_simp
  have l3 : Real.log ((q^2)⁻¹ + E/q) = Real.log (1+q*E) - 2*Real.log q := by
    rw [show 2*Real.log q = Real.log (q^2) by rw [Real.log_pow]; push_cast; ring,
      ← Real.log_div (by positivity) (by positivity)]
    congr 1; field_simp
  unfold eulerHalfLineKernel
  rw [show (1:ℂ) + ((E/q:ℝ):ℂ) = ((1 + E/q : ℝ):ℂ) by push_cast; ring,
    show (((q^2)⁻¹:ℝ):ℂ) + ((E/q:ℝ):ℂ) = (((q^2)⁻¹ + E/q : ℝ):ℂ) by push_cast; ring,
    show (2:ℂ)^(-(μ+1/2)) = ((2:ℝ):ℂ)^(-(μ+1/2)) by norm_num,
    legInt_cpow_ofReal hv, legInt_cpow_ofReal (by positivity : (0:ℝ) < 1 + E/q),
    legInt_cpow_ofReal (by positivity : (0:ℝ) < (q^2)⁻¹ + E/q), legInt_cpow_ofReal hq,
    legInt_cpow_ofReal two_pos, legInt_cpow_ofReal hE, legInt_cpow_ofReal hX,
    show ((E/q:ℝ):ℂ) = exp (Real.log (E/q) : ℂ) by rw [← ofReal_exp, Real.exp_log hv]]
  simp only [← exp_add]
  congr 1
  rw [l1, l2, l3]
  have hsum' : ((Real.log (q+E) : ℝ):ℂ) + Real.log (1+q*E) =
      Real.log E + Real.log 2 + Real.log q + Real.log (x + (E + E⁻¹)/2) := by exact_mod_cast hsum
  push_cast
  linear_combination (-(μ+1/2)) * hsum'

/-- The substitutions `v = e^{±t}/q` split a half-line integral at `1/q`. -/
theorem legInt_exp_split {q : ℝ} (hq : 0 < q) {K : ℝ → ℂ} (hK : IntegrableOn K (Ioi 0)) :
    IntegrableOn (fun t => (Real.exp t / q) • K (Real.exp t / q)) (Ioi 0) ∧
    IntegrableOn (fun t => (Real.exp (-t) / q) • K (Real.exp (-t) / q)) (Ioi 0) ∧
    ∫ t in Ioi 0, ((Real.exp t / q) • K (Real.exp t / q) + (Real.exp (-t) / q) • K (Real.exp (-t) / q)) =
      ∫ v in Ioi 0, K v := by
  -- the increasing branch on `[0, ∞)`
  have hd1 : ∀ t ∈ Ici (0:ℝ), HasDerivWithinAt (fun t => Real.exp t / q) (Real.exp t / q) (Ici 0) t :=
    fun t _ => ((Real.hasDerivAt_exp t).div_const q).hasDerivWithinAt
  have hi1 : InjOn (fun t => Real.exp t / q) (Ici 0) := fun a _ b _ h => by
    have : Real.exp a = Real.exp b := by
      have := congrArg (· * q) h; simpa [div_mul_cancel₀ _ hq.ne'] using this
    exact Real.exp_injective this
  have him1 : (fun t => Real.exp t / q) '' Ici 0 = Ici (1/q) := by
    ext v; constructor
    · rintro ⟨t, ht, rfl⟩
      exact div_le_div_of_nonneg_right (by simpa using Real.one_le_exp (show (0:ℝ) ≤ t from ht)) hq.le
    · intro hv
      have hv' : 1 ≤ q * v := by
        have := mul_le_mul_of_nonneg_left (show 1/q ≤ v from hv) hq.le
        rwa [mul_one_div_cancel hq.ne'] at this
      refine ⟨Real.log (q*v), Real.log_nonneg hv', ?_⟩
      simp only
      rw [Real.exp_log (by linarith)]; field_simp
  -- the decreasing branch on `(0, ∞)`
  have hd2 : ∀ t ∈ Ioi (0:ℝ), HasDerivWithinAt (fun t => Real.exp (-t) / q) (-(Real.exp (-t) / q))
      (Ioi 0) t := fun t _ => by
    have h : HasDerivAt (fun x => Real.exp (-x)) (Real.exp (-t) * -1) t :=
      (Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)
    exact ((h.div_const q).congr_deriv (by ring)).hasDerivWithinAt
  have hi2 : InjOn (fun t => Real.exp (-t) / q) (Ioi 0) := fun a _ b _ h => by
    have : Real.exp (-a) = Real.exp (-b) := by
      have := congrArg (· * q) h; simpa [div_mul_cancel₀ _ hq.ne'] using this
    linarith [Real.exp_injective this]
  have him2 : (fun t => Real.exp (-t) / q) '' Ioi 0 = Ioo 0 (1/q) := by
    ext v; constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨by positivity, div_lt_div_of_pos_right ?_ hq⟩
      exact Real.exp_lt_one_iff.mpr (by simp at ht ⊢; linarith [show (0:ℝ) < t from ht])
    · rintro ⟨hv0, hv⟩
      have hv' : q * v < 1 := by
        have := mul_lt_mul_of_pos_left hv hq
        rwa [mul_one_div_cancel hq.ne'] at this
      refine ⟨-Real.log (q*v), ?_, ?_⟩
      · simp only [mem_Ioi, Left.neg_pos_iff]; exact Real.log_neg (by positivity) hv'
      · simp only [neg_neg]; rw [Real.exp_log (by positivity)]; field_simp
  have hK1 : IntegrableOn K (Ici (1/q)) := hK.mono_set (fun v (hv : 1/q ≤ v) =>
    show (0:ℝ) < v from lt_of_lt_of_le (by positivity : (0:ℝ) < 1/q) hv)
  have hK2 : IntegrableOn K (Ioo 0 (1/q)) := hK.mono_set Ioo_subset_Ioi_self
  have c1 := integral_image_eq_integral_abs_deriv_smul measurableSet_Ici hd1 hi1 K
  have c1I := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ici hd1 hi1 K
  have c2 := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hd2 hi2 K
  have c2I := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hd2 hi2 K
  rw [him1] at c1 c1I; rw [him2] at c2 c2I
  have a1 : ∀ t : ℝ, |Real.exp t / q| = Real.exp t / q := fun t => abs_of_pos (by positivity)
  have a2 : ∀ t : ℝ, |-(Real.exp (-t) / q)| = Real.exp (-t) / q := fun t => by
    rw [abs_neg]; exact abs_of_pos (by positivity)
  simp only [a1] at c1 c1I; simp only [a2] at c2 c2I
  have I1 : IntegrableOn (fun t => (Real.exp t / q) • K (Real.exp t / q)) (Ioi 0) :=
    (c1I.mp hK1).mono_set Ioi_subset_Ici_self
  have I2 := c2I.mp hK2
  refine ⟨I1, I2, ?_⟩
  rw [integral_add I1 I2, ← integral_Ici_eq_integral_Ioi, ← c1, ← c2, add_comm,
    ← setIntegral_union (Set.disjoint_left.mpr fun v (hv : v ∈ Ioo 0 (1/q)) (hv' : v ∈ Ici (1/q)) =>
      absurd (show 1/q ≤ v from hv') (not_le.mpr hv.2)) measurableSet_Ici hK2 hK1,
    Ioo_union_Ici_eq_Ioi (by positivity)]

/-- The hypergeometric value behind DLMF 14.12.4:
`𝐅(μ+1/2, μ-ν; 2μ+1; 1-q⁻²) = q^{2(μ-ν)} (qx)^{ν-μ} Γ(μ+1)/Γ(2μ+1) 𝐅((μ-ν)/2, (μ-ν+1)/2; μ+1; 1-1/x²)`. -/
theorem legInt_cosh_hyp (ν μ : ℂ) (hμ : -1/2 < μ.re) {x q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hqx : 1 + q^2 = 2*q*x) :
    regularizedGaussHG (μ+1/2) (μ-ν) (2*μ+1) (1 - (((q^2)⁻¹:ℝ):ℂ)) =
      exp (Real.log q * (2*(μ-ν))) * exp ((Real.log q + Real.log x) * (ν-μ)) *
        (Gamma (μ+1) / Gamma (2*μ+1)) *
        regularizedGaussHG ((μ-ν)/2) ((μ-ν+1)/2) (μ+1) (1 - 1/(x:ℂ)^2) := by
  have hx0 : 0 < x := by nlinarith
  have hx1 : 1 < x := by
    by_contra h; push Not at h
    nlinarith [mul_pos hq0 (sub_pos.mpr hq1), mul_le_mul_of_nonneg_left h (by linarith : (0:ℝ) ≤ 2*q)]
  have hq2 : 0 < (q^2)⁻¹ := by positivity
  have hw : 1 - (((q^2)⁻¹:ℝ):ℂ) ∈ cutPlane := by
    rw [mem_cutPlane, sub_sub_cancel]; exact Or.inl (by simp only [ofReal_re]; exact hq2)
  have hc : ∀ k : ℕ, 2*μ+1 ≠ -(k:ℂ) := fun k hk => by
    have := congrArg re hk; simp at this; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  have hc2 : ∀ k : ℕ, 2*(μ+1/2) ≠ -(k:ℂ) := fun k => by rw [show 2*(μ+1/2) = 2*μ+1 by ring]; exact hc k
  have hc3 : ∀ k : ℕ, μ+1/2+1/2 ≠ -(k:ℂ) := fun k hk => by
    have := congrArg re hk; simp at this; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  have hc4 : ∀ k : ℕ, μ+1 ≠ -(k:ℂ) := fun k => by rw [show μ+1 = μ+1/2+1/2 by ring]; exact hc3 k
  have hz1 : ‖((1-q^2:ℝ):ℂ)‖ < 1 := by
    rw [norm_real, Real.norm_eq_abs, abs_lt]; constructor <;> nlinarith
  have hratio : (((1-q^2:ℝ):ℂ)/(2-((1-q^2:ℝ):ℂ)))^2 = 1 - 1/(x:ℂ)^2 := by
    have hR : ((1-q^2)/(2-(1-q^2)))^2 = 1 - 1/x^2 := by
      have : x = (1+q^2)/(2*q) := by field_simp; linarith
      rw [show (2:ℝ) - (1-q^2) = 1+q^2 by ring, this]; field_simp; ring
    have := congrArg (fun r : ℝ => (r:ℂ)) hR
    push_cast at this ⊢; exact this
  have hz2 : ‖(1:ℂ) - 1/(x:ℂ)^2‖ < 1 := by
    rw [show (1:ℂ) - 1/(x:ℂ)^2 = ((1 - 1/x^2 : ℝ):ℂ) by push_cast; ring, norm_real, Real.norm_eq_abs,
      abs_lt]
    have : 0 < 1/x^2 := by positivity
    have : 1/x^2 < 1 := by rw [div_lt_one (by positivity)]; nlinarith
    constructor <;> linarith
  have hquad := quadratic_double_denominator (a := μ-ν) (b := μ+1/2) (z := ((1-q^2:ℝ):ℂ)) hc2 hc3 hz1
  rw [hratio, show μ+1/2+1/2 = μ+1 by ring, show 2*(μ+1/2) = 2*μ+1 by ring] at hquad
  rw [regularizedGaussHG_symm _ _ _ hw, regularizedGaussHG_pfaff _ _ _ hw,
    show 2*μ+1-(μ+1/2) = μ+1/2 by ring, sub_sub_cancel,
    show (1 - (((q^2)⁻¹:ℝ):ℂ))/((1 - (((q^2)⁻¹:ℝ):ℂ)) - 1) = ((1-q^2:ℝ):ℂ) by
      push_cast
      have : (q:ℂ) ≠ 0 := by exact_mod_cast hq0.ne'
      field_simp; ring,
    regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hz1, regularizedGaussHGFun_eq_div_Gamma hc,
    hquad, regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hz2, regularizedGaussHGFun_eq_div_Gamma hc4,
    legInt_cpow_ofReal hq2,
    show (1:ℂ) - ((1-q^2:ℝ):ℂ)/2 = ((q*x:ℝ):ℂ) by
      rw [← show 1 - (1-q^2)/2 = q*x by linarith]; push_cast; ring,
    legInt_cpow_ofReal (by positivity : (0:ℝ) < q*x), Real.log_inv, Real.log_pow,
    Real.log_mul hq0.ne' hx0.ne']
  have hG1 : Gamma (2*μ+1) ≠ 0 := Gamma_ne_zero hc
  have hG2 : Gamma (μ+1) ≠ 0 := Gamma_ne_zero hc4
  field_simp
  push_cast
  ring_nf

/-- The constant in DLMF 14.12.4, by the duplication formula. -/
theorem legInt_cosh_value (ν μ F P : ℂ) {x q : ℝ} (hq0 : 0 < q) (hx0 : 0 < x)
    (ha : 0 < (ν+μ+1).re) (h : 0 < (μ-ν).re) (hμ : -1/2 < μ.re) :
    Real.sqrt 2*Gamma (μ+1/2)*P/(Real.sqrt π*Gamma (ν+μ+1)*Gamma (μ-ν)) /
      (2 * ((q:ℂ)^(μ-ν) * (2:ℂ)^(-(μ+1/2)))) * (Gamma (ν + μ + 1) * Gamma (μ - ν) *
      (cexp (↑(Real.log q) * (2 * (μ - ν))) * cexp ((↑(Real.log q) + ↑(Real.log x)) * (ν - μ)) *
          (Gamma (μ + 1) / Gamma (2 * μ + 1)) * F)) =
      2^(-μ) * (x:ℂ)^(ν-μ) * P * F := by
  have hdup := Complex.Gamma_mul_Gamma_add_half (μ+1/2)
  rw [show μ+1/2+1/2 = μ+1 by ring, show 2*(μ+1/2) = 2*μ+1 by ring] at hdup
  have hc : ∀ k : ℕ, 2*μ+1 ≠ -(k:ℂ) := fun k hk => by
    have := congrArg re hk; simp at this; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  have hGa : Gamma (μ+1/2) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hGs : Gamma (ν+μ+1) ≠ 0 := Gamma_ne_zero_of_re_pos ha
  have hGd : Gamma (μ-ν) ≠ 0 := Gamma_ne_zero_of_re_pos h
  have hG2 : Gamma (2*μ+1) ≠ 0 := Gamma_ne_zero hc
  have hpi : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hG1 : Gamma (μ+1) / Gamma (2*μ+1) = 2^(1-(2*μ+1)) * Real.sqrt π / Gamma (μ+1/2) := by
    rw [eq_div_iff hGa, div_mul_eq_mul_div, div_eq_iff hG2, mul_comm (Gamma (μ+1)), hdup]; ring
  rw [hG1]
  have hs2 : ((Real.sqrt 2 : ℝ) : ℂ) = exp (Real.log 2 * (1/2)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos two_pos, ofReal_exp]; push_cast; ring_nf
  have h2 : ∀ w : ℂ, (2:ℂ)^w = exp (Real.log 2 * w) := fun w => by
    rw [show (2:ℂ) = ((2:ℝ):ℂ) by norm_num, legInt_cpow_ofReal two_pos]
  rw [hs2, h2, h2, h2, legInt_cpow_ofReal hq0, legInt_cpow_ofReal hx0]
  have e : exp (Real.log 2 * (1/2)) * exp (Real.log 2 * (1 - (2*μ+1))) *
      exp (↑(Real.log q) * (2 * (μ - ν))) * exp ((↑(Real.log q) + ↑(Real.log x)) * (ν - μ)) =
      exp (Real.log 2 : ℂ) * (exp (Real.log q * (μ-ν)) * exp (Real.log 2 * (-(μ+1/2)))) *
        (exp (Real.log 2 * (-μ)) * exp (Real.log x * (ν-μ))) := by
    simp only [← exp_add]; congr 1; ring
  have h2e : exp (Real.log 2 : ℂ) = 2 := by rw [← ofReal_exp, Real.exp_log two_pos]; norm_num
  rw [h2e] at e
  have hne : exp (Real.log q * (μ-ν)) * exp (Real.log 2 * (-(μ+1/2))) ≠ 0 :=
    mul_ne_zero (exp_ne_zero _) (exp_ne_zero _)
  calc _ = (exp (Real.log 2 * (1/2)) * exp (Real.log 2 * (1 - (2*μ+1))) *
      exp (↑(Real.log q) * (2 * (μ - ν))) * exp ((↑(Real.log q) + ↑(Real.log x)) * (ν - μ))) /
      (2 * (exp (Real.log q * (μ-ν)) * exp (Real.log 2 * (-(μ+1/2))))) * (P * F) *
      ((Gamma (μ+1/2) * (Gamma (μ+1/2))⁻¹) * ((Real.sqrt π:ℂ) * (Real.sqrt π:ℂ)⁻¹) *
      (Gamma (ν+μ+1) * (Gamma (ν+μ+1))⁻¹) * (Gamma (μ-ν) * (Gamma (μ-ν))⁻¹)) := by ring
    _ = _ := by
      rw [mul_inv_cancel₀ hGa, mul_inv_cancel₀ hpi, mul_inv_cancel₀ hGs, mul_inv_cancel₀ hGd, e,
        mul_div_cancel_left₀ _ (mul_ne_zero two_ne_zero hne)]
      ring

/-- DLMF 14.12.4 by the substitution `v = e^{±t}/q`, Euler's half-line integral, Pfaff, the
quadratic transformation 15.8.13 and 14.3.18. -/
theorem legInt_associatedP_cosh_integral {ν μ : ℂ} (h : 0 < (μ-ν).re) (hconv : -1 < (μ+ν).re) {x : ℝ} (hx : 1 < x) :
    HasIntegralAtTop (fun t : ℝ => Real.sqrt 2*Gamma (μ+1/2)*(x^2-1:ℂ)^(μ/2)/(Real.sqrt π*Gamma (ν+μ+1)*Gamma (μ-ν))*cosh ((ν+1/2)*t)/(x+Real.cosh t:ℂ)^(μ+1/2)) 0 (associatedP ν (-μ) x) := by
  set r := Real.sqrt (x^2-1) with hr
  have hr2 : r^2 = x^2-1 := Real.sq_sqrt (by nlinarith)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  set q := x - r with hqdef
  have hqx : 1 + q^2 = 2*q*x := by rw [hqdef]; nlinarith [hr2]
  have hq0 : 0 < q := by
    have : r < x := by nlinarith
    linarith
  have hq1 : q < 1 := by
    have : 0 < r := Real.sqrt_pos.mpr (by nlinarith)
    nlinarith
  have hμ : -1/2 < μ.re := by simp at h hconv; linarith
  have ha : 0 < (ν+μ+1).re := by simp at hconv ⊢; linarith
  have hz : 0 < ((((q^2)⁻¹:ℝ)):ℂ).re := by simp only [ofReal_re]; positivity
  obtain ⟨hKI, hKv⟩ := eulerHalfLine_integrable_integral (p := μ+1/2) ha h hz
  rw [show ν+μ+1+(μ-ν) = 2*μ+1 by ring, legInt_cosh_hyp ν μ hμ hq0 hq1 hqx] at hKv
  obtain ⟨I1, I2, hsum⟩ := legInt_exp_split hq0 hKI
  set C : ℂ := (q:ℂ)^(μ-ν) * (2:ℂ)^(-(μ+1/2))
  have hp : ∀ t : ℝ, (Real.exp t / q) • eulerHalfLineKernel (μ+1/2) (ν+μ+1) (μ-ν) (((q^2)⁻¹:ℝ):ℂ)
      (Real.exp t / q) + (Real.exp (-t) / q) • eulerHalfLineKernel (μ+1/2) (ν+μ+1) (μ-ν)
      (((q^2)⁻¹:ℝ):ℂ) (Real.exp (-t) / q) =
      2*C * (cosh ((ν+1/2)*t)/(x+Real.cosh t:ℂ)^(μ+1/2)) := by
    intro t
    rw [real_smul, real_smul, legInt_halfLine_point ν μ hq0 hqx (Real.exp_pos t),
      legInt_halfLine_point ν μ hq0 hqx (Real.exp_pos (-t)), ← Real.exp_neg, ← Real.exp_neg, neg_neg,
      show Real.exp (-t) + Real.exp t = Real.exp t + Real.exp (-t) by ring, ← Real.cosh_eq,
      legInt_cpow_ofReal (Real.exp_pos t), legInt_cpow_ofReal (Real.exp_pos (-t)), Real.log_exp,
      Real.log_exp]
    have hc : cosh ((ν+1/2)*t) = (exp ((t:ℂ)*(ν+1/2)) + exp (((-t:ℝ):ℂ)*(ν+1/2)))/2 := by
      rw [Complex.cosh]; push_cast; ring_nf
    rw [hc, show ((x + Real.cosh t : ℝ):ℂ) = (x:ℂ) + (Real.cosh t:ℂ) by push_cast; ring]
    simp only [C, cpow_neg]
    ring
  set Cst : ℂ := Real.sqrt 2*Gamma (μ+1/2)*(x^2-1:ℂ)^(μ/2)/(Real.sqrt π*Gamma (ν+μ+1)*Gamma (μ-ν))
  have hC : C ≠ 0 := mul_ne_zero
    (cpow_ne_zero_iff.mpr (Or.inl (ofReal_ne_zero.mpr hq0.ne')))
    (cpow_ne_zero_iff.mpr (Or.inl two_ne_zero))
  have hf : ∀ t ∈ Ioi (0:ℝ), Cst/(2*C) * ((Real.exp t / q) • eulerHalfLineKernel (μ+1/2) (ν+μ+1) (μ-ν)
      (((q^2)⁻¹:ℝ):ℂ) (Real.exp t / q) + (Real.exp (-t) / q) • eulerHalfLineKernel (μ+1/2) (ν+μ+1)
      (μ-ν) (((q^2)⁻¹:ℝ):ℂ) (Real.exp (-t) / q)) =
      Real.sqrt 2*Gamma (μ+1/2)*(x^2-1:ℂ)^(μ/2)/(Real.sqrt π*Gamma (ν+μ+1)*Gamma (μ-ν))*
        cosh ((ν+1/2)*t)/(x+Real.cosh t:ℂ)^(μ+1/2) := by
    intro t _
    rw [hp t]; simp only [Cst]; field_simp
  have hint := IntegrableOn.congr_fun ((I1.add I2).const_mul (Cst/(2*C))) hf measurableSet_Ioi
  have hval : (∫ t in Ioi (0:ℝ), Real.sqrt 2*Gamma (μ+1/2)*(x^2-1:ℂ)^(μ/2)/(Real.sqrt π*
      Gamma (ν+μ+1)*Gamma (μ-ν))*cosh ((ν+1/2)*t)/(x+Real.cosh t:ℂ)^(μ+1/2)) =
      Cst / (2 * C) * (Gamma (ν + μ + 1) * Gamma (μ - ν) *
      (cexp (↑(Real.log q) * (2 * (μ - ν))) * cexp ((↑(Real.log q) + ↑(Real.log x)) * (ν - μ)) *
          (Gamma (μ + 1) / Gamma (2 * μ + 1)) *
        regularizedGaussHG ((μ - ν) / 2) ((μ - ν + 1) / 2) (μ + 1) (1 - 1 / ↑x ^ 2))) := by
    rw [← setIntegral_congr_fun measurableSet_Ioi hf, integral_const_mul, hsum, hKv]
  have hlim := intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id
  rw [hval] at hlim
  suffices hv : Cst / (2 * C) * (Gamma (ν + μ + 1) * Gamma (μ - ν) *
      (cexp (↑(Real.log q) * (2 * (μ - ν))) * cexp ((↑(Real.log q) + ↑(Real.log x)) * (ν - μ)) *
          (Gamma (μ + 1) / Gamma (2 * μ + 1)) *
        regularizedGaussHG ((μ - ν) / 2) ((μ - ν + 1) / 2) (μ + 1) (1 - 1 / ↑x ^ 2))) =
      associatedP ν (-μ) x by
    rw [hv] at hlim; exact hlim
  have hx0 : 0 < x := by linarith
  rw [associated_hypergeometric_18 ν μ (legInt_one_lt_mem hx) (by simp; linarith),
    legInt_legendreBranchPower_real μ hx]
  exact legInt_cosh_value ν μ _ _ hq0 hx0 ha h hμ

/-! ### Helpers for DLMF 14.12.1 -/

/-- The substitution `u = (1 - cos s)/(1 - cos θ)` of DLMF 14.12.1. -/
noncomputable def legInt_md (θ s : ℝ) : ℝ := (1 - Real.cos s) / (1 - Real.cos θ)

/-- Change of variables `u = (1 - cos s)/(1 - cos θ)` from `(0, 1)` to `(0, θ)`. -/
theorem legInt_md_cov {θ : ℝ} (h0 : 0 < θ) (hπ : θ < π) (g : ℝ → ℂ) :
    ∫ s in Ioo 0 θ, |Real.sin s / (1 - Real.cos θ)| • g (legInt_md θ s) = ∫ u in Ioo 0 1, g u := by
  have hD : 0 < 1 - Real.cos θ := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hπ.le h0; rw [Real.cos_zero] at this; linarith
  have hd : ∀ s ∈ Ioo (0:ℝ) θ, HasDerivWithinAt (legInt_md θ) (Real.sin s / (1 - Real.cos θ))
      (Ioo 0 θ) s := by
    intro s _
    have h := ((Real.hasDerivAt_cos s).const_sub 1).div_const (1 - Real.cos θ)
    unfold legInt_md
    convert h.hasDerivWithinAt using 1; ring
  have hinj : InjOn (legInt_md θ) (Ioo 0 θ) := by
    intro a ha b hb he
    simp only [legInt_md] at he
    rw [div_left_inj' hD.ne'] at he
    exact Real.injOn_cos ⟨ha.1.le, by linarith [ha.2]⟩ ⟨hb.1.le, by linarith [hb.2]⟩ (by linarith)
  have him : legInt_md θ '' Ioo 0 θ = Ioo 0 1 := by
    ext u; constructor
    · rintro ⟨s, hs, rfl⟩
      have h1 := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl (by linarith [hs.2]) hs.1
      have h2 := Real.cos_lt_cos_of_nonneg_of_le_pi hs.1.le hπ.le hs.2
      rw [Real.cos_zero] at h1
      refine ⟨div_pos (by linarith) hD, (div_lt_one hD).mpr (by linarith)⟩
    · rintro ⟨hu0, hu1⟩
      set y := 1 - u * (1 - Real.cos θ)
      have hy1 : y < 1 := by simp only [y]; nlinarith
      have hy2 : Real.cos θ < y := by simp only [y]; nlinarith
      have hc1 : -1 ≤ Real.cos θ := Real.neg_one_le_cos θ
      refine ⟨Real.arccos y, ⟨Real.arccos_pos.mpr hy1, ?_⟩, ?_⟩
      · have := Real.arccos_lt_arccos hc1 hy2 hy1.le
        rwa [Real.arccos_cos h0.le hπ.le] at this
      · rw [legInt_md, Real.cos_arccos (by linarith) hy1.le]
        simp only [y]; field_simp; ring
  have hcov := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hd hinj g
  rw [him] at hcov
  exact hcov.symm

/-- `√r = e^{(log r)/2}` for `r > 0`, as complex numbers. -/
theorem legInt_sqrt_eq_exp {r : ℝ} (hr : 0 < r) : ((Real.sqrt r : ℝ) : ℂ) = exp (Real.log r / 2) := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hr, ofReal_exp]; push_cast; ring_nf

/-- The integrand of 15.6.8 after the substitution `u = (1 - cos s)/(1 - cos θ)`, by DLMF 15.4.14. -/
theorem legInt_md_point (ν μ : ℂ) {θ s : ℝ} (hs0 : 0 < s) (hsθ : s < θ) (hπ : θ < π) :
    |Real.sin s / (1 - Real.cos θ)| • (regularizedGaussHGFun (ν+1) (-ν) (1/2)
      ((1 - (Real.cos θ:ℂ))/2 * (legInt_md θ s : ℂ)) * (legInt_md θ s : ℂ)^((1/2:ℂ)-1) *
      (1 - (legInt_md θ s : ℂ))^((1-μ)-1/2-1)) =
    (Real.sqrt 2 * exp (Real.log (1 - Real.cos θ) * μ) / Real.sqrt π) *
      (cos ((ν+1/2)*s) / (Real.cos s - Real.cos θ : ℂ)^(μ+1/2)) := by
  have h0 : 0 < θ := by linarith
  obtain ⟨D, hDdef⟩ : ∃ D, D = 1 - Real.cos θ := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B, B = Real.cos s - Real.cos θ := ⟨_, rfl⟩
  have hD : 0 < D := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hπ.le h0; rw [Real.cos_zero] at this; linarith
  have hB : 0 < B := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi hs0.le hπ.le hsθ; linarith
  obtain ⟨s2, hs2⟩ : ∃ s2, s2 = Real.sin (s/2) := ⟨_, rfl⟩
  obtain ⟨c2, hc2⟩ : ∃ c2, c2 = Real.cos (s/2) := ⟨_, rfl⟩
  have hs2p : 0 < s2 := hs2 ▸ Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hc2p : 0 < c2 := hc2 ▸ Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hsin : Real.sin s = 2*s2*c2 := by
    rw [hs2, hc2, ← Real.sin_two_mul]; ring_nf
  have hA : 1 - Real.cos s = 2*s2^2 := by
    have h1 := Real.cos_sq (s/2); have h2 := Real.sin_sq_add_cos_sq (s/2)
    rw [show 2*(s/2) = s by ring] at h1; rw [hs2]; linarith
  have hmd : legInt_md θ s = 2*s2^2/D := by rw [legInt_md, hA, hDdef]
  have hmd1 : 1 - legInt_md θ s = B/D := by
    rw [legInt_md, hBdef, ← hDdef]; field_simp; rw [hDdef]; ring
  have hD0 : (D:ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  have hz : (1 - (Real.cos θ:ℂ))/2 * (legInt_md θ s : ℂ) = ((Real.sin (s/2):ℝ):ℂ)^2 := by
    rw [hmd, ← hs2, show (1:ℂ) - (Real.cos θ:ℂ) = (D:ℂ) by rw [hDdef, ofReal_sub, ofReal_one]]
    simp only [ofReal_div, ofReal_mul, ofReal_pow, ofReal_ofNat]
    field_simp
  have hc12 : ∀ k : ℕ, (1 / 2 : ℂ) ≠ -(k : ℂ) := fun k h => by
    have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hF := sin_sq_cos_quotient (ν+1) (x := s/2) (by rw [abs_of_pos (by linarith)]; linarith)
  rw [show (1:ℂ) - (ν+1) = -ν by ring, ← hc2] at hF
  rw [hz, regularizedGaussHGFun_eq_div_Gamma hc12, hF, legendre_Gamma_one_half,
    show (1 - (legInt_md θ s : ℂ)) = ((1 - legInt_md θ s : ℝ):ℂ) by rw [ofReal_sub, ofReal_one], hmd1,
    legInt_cpow_ofReal (div_pos hB hD),
    show ((1/2:ℂ)-1) = (((-1/2:ℝ)):ℂ) by push_cast; ring,
    ← ofReal_cpow (by rw [hmd]; positivity),
    show (Real.cos s - Real.cos θ : ℂ) = (B:ℂ) by rw [hBdef, ofReal_sub],
    legInt_cpow_ofReal hB, Real.log_div hB.ne' hD.ne', ← hDdef]
  have ht : legInt_md θ s ^ (-1/2:ℝ) = Real.sqrt D / (Real.sqrt 2 * s2) := by
    rw [hmd, show (-1/2:ℝ) = -(1/2) by ring, Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow,
      Real.sqrt_div' _ hD.le, Real.sqrt_mul (by norm_num), Real.sqrt_sq hs2p.le, inv_div]
  have hE : exp (((Real.log B - Real.log D : ℝ) : ℂ) * ((1-μ)-1/2-1)) =
      exp (Real.log D * μ) * ((Real.sqrt D:ℝ):ℂ) / exp (Real.log B * (μ+1/2)) := by
    rw [legInt_sqrt_eq_exp hD, eq_div_iff (exp_ne_zero _), ← exp_add, ← exp_add]
    congr 1; push_cast; ring
  rw [ht, hE, abs_of_pos (div_pos (by rw [hsin]; positivity) hD), hsin,
    show (2:ℂ)*(ν+1)-1 = 2*(ν+1/2) by ring, show 2*(ν+1/2)*((s/2:ℝ):ℂ) = (ν+1/2)*s by push_cast; ring]
  have hsq2 : (Real.sqrt 2:ℂ)^2 = 2 := by
    rw [← ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hsqD : (Real.sqrt D:ℂ)^2 = D := by
    rw [← ofReal_pow, Real.sq_sqrt hD.le]
  have h2 : (Real.sqrt 2:ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr two_pos).ne'
  have hπ0 : (Real.sqrt π:ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hc0 : (c2:ℂ) ≠ 0 := by exact_mod_cast hc2p.ne'
  have hs0' : (s2:ℂ) ≠ 0 := by exact_mod_cast hs2p.ne'
  have hE0 : exp (Real.log B * (μ+1/2)) ≠ 0 := exp_ne_zero _
  rw [real_smul]
  simp only [ofReal_div, ofReal_mul, ofReal_ofNat]
  field_simp
  rw [hsq2, hsqD]; ring

/-- ferrersP Mehler–Dirichlet integral, from the fractional integral 15.6.8 with `d = 1/2` and
DLMF 15.4.14, by the substitution `u = (1 - cos t)/(1 - cos θ)`. -/
@[dlmf 14.12.E1]
theorem ferrersP_mehler_dirichlet {μ : ℂ} (hμ : μ.re < 1/2) (ν : ℂ) {θ : ℝ} (h0 : 0 < θ) (hπ : θ < π) :
    ferrersP ν μ (Real.cos θ)=Real.sqrt 2*(Real.sin θ:ℂ)^μ/(Real.sqrt π*Gamma (1/2-μ))*∫ t : ℝ in 0..θ, cos ((ν+1/2)*t)/(Real.cos t-Real.cos θ:ℂ)^(μ+1/2) := by
  have hD : 0 < 1 - Real.cos θ := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hπ.le h0; rw [Real.cos_zero] at this; linarith
  have hP : 0 < 1 + Real.cos θ := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi h0.le le_rfl hπ; rw [Real.cos_pi] at this; linarith
  have hS : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi h0 hπ
  have hz : ‖(1 - (Real.cos θ:ℂ))/2‖ < 1 := by
    rw [show (1 - (Real.cos θ:ℂ))/2 = (((1 - Real.cos θ)/2 : ℝ):ℂ) by push_cast; ring, norm_real,
      Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  have hcd : 0 < ((1-μ) - 1/2).re := by simp; linarith
  unfold ferrersP
  rw [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hz,
    fractional_integral (d := 1/2) (by norm_num) hcd hz,
    intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo,
    ← legInt_md_cov h0 hπ, setIntegral_congr_fun measurableSet_Ioo
      (fun s hs => legInt_md_point ν μ hs.1 hs.2 hπ), integral_const_mul,
    intervalIntegral.integral_of_le h0.le, integral_Ioc_eq_integral_Ioo]
  have hlog : Real.log (Real.sin θ) = (Real.log (1 - Real.cos θ) + Real.log (1 + Real.cos θ))/2 := by
    have h2 : Real.sin θ ^ 2 = (1 - Real.cos θ) * (1 + Real.cos θ) := by
      nlinarith [Real.sin_sq_add_cos_sq θ]
    have := congrArg Real.log h2
    rw [Real.log_pow, Real.log_mul hD.ne' hP.ne'] at this
    push_cast at this; linarith
  rw [legInt_cpow_ofReal (div_pos hP hD), legInt_cpow_ofReal hS, hlog, Real.log_div hP.ne' hD.ne',
    show (1:ℂ) - μ - 1/2 = 1/2 - μ by ring]
  have hπ0 : (Real.sqrt π:ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hG : Gamma (1/2 - μ) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  have he : exp (((Real.log (1 + Real.cos θ) - Real.log (1 - Real.cos θ) : ℝ) : ℂ) * (μ/2)) *
      exp (Real.log (1 - Real.cos θ) * μ) =
      exp ((((Real.log (1 - Real.cos θ) + Real.log (1 + Real.cos θ))/2 : ℝ) : ℂ) * μ) := by
    rw [← exp_add]; congr 1; push_cast; ring
  rw [← he]
  field_simp

/-- ferrersP fractional integral. -/
@[dlmf 14.12.E2]
theorem ferrersP_fractional_integral {μ : ℂ} (hμ : 0 < μ.re) (ν : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersP ν (-μ) x=(1-x^2:ℂ)^(-μ/2)/Gamma μ*∫ t : ℝ in x..1, ferrersP ν 0 t*(t-x:ℂ)^(μ-1) := by
  have h1 : (0:ℝ) < 1 + x := by linarith [hx.1]
  have h2 : (0:ℝ) < 1 - x := by linarith [hx.2]
  set z : ℂ := (1-(x:ℂ))/2 with hz
  have hzn : ‖z‖ < 1 := by
    rw [hz, show (1-(x:ℂ))/2 = (((1-x)/2:ℝ):ℂ) by push_cast; ring, norm_real, Real.norm_eq_abs,
      abs_lt]
    constructor <;> linarith [hx.1, hx.2]
  have hfr := fractional_integral (a := ν+1) (b := -ν) (c := 1+μ) (d := 1) (by norm_num)
    (by simpa using hμ) hzn
  rw [show 1+μ-1 = μ by ring] at hfr
  -- the substituted integral
  have hsub : (∫ t : ℝ in x..1, ferrersP ν 0 t*(t-x:ℂ)^(μ-1)) =
      ((1-x:ℝ):ℂ)^μ * ∫ s : ℝ in (0:ℝ)..1,
        regularizedGaussHGFun (ν+1) (-ν) 1 (z*s) * (s:ℂ)^((1:ℂ)-1) * (1-(s:ℂ))^(μ-1) := by
    have hc : (1-x) ≠ 0 := h2.ne'
    have h := intervalIntegral.integral_comp_sub_mul
      (fun t : ℝ => ferrersP ν 0 t*(t-x:ℂ)^(μ-1)) (a := 0) (b := 1) hc 1
    simp only [mul_one, mul_zero, sub_zero, sub_sub_cancel] at h
    rw [show (∫ t : ℝ in x..1, ferrersP ν 0 t*(t-x:ℂ)^(μ-1)) =
      (1-x) • ∫ s : ℝ in (0:ℝ)..1, ferrersP ν 0 (1-(1-x)*s)*((1-(1-x)*s : ℝ)-x:ℂ)^(μ-1) by
      rw [h, smul_inv_smul₀ hc]]
    rw [real_smul, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le zero_le_one] at hs
    have hzs : ‖z*s‖ < 1 := by
      rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
      calc ‖z‖*s ≤ ‖z‖*1 := by gcongr; exact hs.2
        _ < 1 := by rw [mul_one]; exact hzn
    have hF : ferrersP ν 0 (1-(1-x)*s) = regularizedGaussHGFun (ν+1) (-ν) 1 (z*s) := by
      simp only [ferrersP, zero_div, cpow_zero, one_mul, sub_zero]
      rw [← regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hzs, hz]
      congr 1; push_cast; ring
    have hp : (((1-(1-x)*s : ℝ):ℂ)-x)^(μ-1) = ((1-x:ℝ):ℂ)^(μ-1) * (1-(s:ℂ))^(μ-1) := by
      rw [show (((1-(1-x)*s : ℝ):ℂ)-x) = (((1-x)*(1-s):ℝ):ℂ) by push_cast; ring,
        ofReal_mul, mul_cpow_ofReal_nonneg h2.le (by linarith [hs.2])]
      push_cast; ring_nf
    rw [hF, hp, sub_self, cpow_zero, mul_one]
    have hμ1 : ((1-x:ℝ):ℂ)^μ = ((1-x:ℝ):ℂ) * ((1-x:ℝ):ℂ)^(μ-1) := by
      conv_lhs => rw [show μ = (μ-1)+1 by ring]
      rw [cpow_add _ _ (ofReal_ne_zero.2 hc), cpow_one]; ring
    rw [hμ1]; push_cast; ring
  have hG : Gamma μ ≠ 0 := Gamma_ne_zero_of_re_pos hμ
  have hI : (∫ s : ℝ in (0:ℝ)..1,
        regularizedGaussHGFun (ν+1) (-ν) 1 (z*s) * (s:ℂ)^((1:ℂ)-1) * (1-(s:ℂ))^(μ-1)) =
      Gamma μ * regularizedGaussHGFun (ν+1) (-ν) (1+μ) z := by
    rw [hfr]; field_simp
  have hpow : (((1+x)/(1-x):ℝ):ℂ)^(-μ/2) = (1-(x:ℂ)^2)^(-μ/2) * ((1-x:ℝ):ℂ)^μ := by
    rw [show (1-(x:ℂ)^2) = (((1+x)*(1-x):ℝ):ℂ) by push_cast; ring,
      legInt_cpow_ofReal (div_pos h1 h2), legInt_cpow_ofReal (mul_pos h1 h2),
      legInt_cpow_ofReal h2, ← exp_add, Real.log_div h1.ne' h2.ne', Real.log_mul h1.ne' h2.ne']
    congr 1; push_cast; ring
  rw [hsub, hI, ferrersP, show (1:ℂ) - -μ = 1+μ by ring,
    regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hzn, show -μ/2 = (-μ)/2 by ring]
  rw [show (-μ)/2 = -μ/2 by ring, hpow]
  field_simp

/-- associatedP fractional integral. -/
@[dlmf 14.12.E5]
theorem associatedP_fractional_integral {μ : ℂ} (hμ : 0 < μ.re) (ν : ℂ) {x : ℝ} (hx : 1 < x) :
    associatedP ν (-μ) x=(x^2-1:ℂ)^(-μ/2)/Gamma μ*∫ t : ℝ in 1..x, associatedP ν 0 t*(x-t:ℂ)^(μ-1) := by
  have h1 : (0:ℝ) < x - 1 := by linarith
  have h2 : (0:ℝ) < x + 1 := by linarith
  set z : ℂ := (1-(x:ℂ))/2 with hz
  have hzc : z ∈ cutPlane := by
    rw [mem_cutPlane, hz]; left; simp; linarith
  have hsub : (∫ t : ℝ in (1:ℝ)..x, associatedP ν 0 t*(x-t:ℂ)^(μ-1)) =
      ((x-1:ℝ):ℂ)^μ * ∫ s : ℝ in (0:ℝ)..1,
        (1-(s:ℂ))^(μ-1) * regularizedGaussHG (ν+1) (-ν) 1 (z * s) := by
    have hc : (x-1) ≠ 0 := h1.ne'
    have h := intervalIntegral.integral_comp_add_mul
      (fun t : ℝ => associatedP ν 0 t*(x-t:ℂ)^(μ-1)) (a := 0) (b := 1) hc 1
    simp only [mul_one, mul_zero, add_zero, add_sub_cancel] at h
    rw [show (∫ t : ℝ in (1:ℝ)..x, associatedP ν 0 t*(x-t:ℂ)^(μ-1)) =
      (x-1) • ∫ s : ℝ in (0:ℝ)..1, associatedP ν 0 ((1+(x-1)*s : ℝ))*(x-((1+(x-1)*s : ℝ)):ℂ)^(μ-1) by
      rw [h, smul_inv_smul₀ hc]]
    rw [real_smul, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le zero_le_one] at hs
    have hF : associatedP ν 0 ((1+(x-1)*s : ℝ)) = regularizedGaussHG (ν+1) (-ν) 1 (z*s) := by
      simp only [associatedP, zero_div, zero_mul, exp_zero, one_mul, sub_zero]
      rw [hz]; congr 1; push_cast; ring
    have hp : ((x:ℂ)-((1+(x-1)*s : ℝ)))^(μ-1) = ((x-1:ℝ):ℂ)^(μ-1) * (1-(s:ℂ))^(μ-1) := by
      rw [show ((x:ℂ)-((1+(x-1)*s : ℝ))) = (((x-1)*(1-s):ℝ):ℂ) by push_cast; ring,
        ofReal_mul, mul_cpow_ofReal_nonneg h1.le (by linarith [hs.2])]
      push_cast; ring_nf
    rw [hF, hp]
    have hμ1 : ((x-1:ℝ):ℂ)^μ = ((x-1:ℝ):ℂ) * ((x-1:ℝ):ℂ)^(μ-1) := by
      conv_lhs => rw [show μ = (μ-1)+1 by ring]
      rw [cpow_add _ _ (ofReal_ne_zero.2 hc), cpow_one]; ring
    rw [hμ1]; push_cast; ring
  have hG : Gamma μ ≠ 0 := Gamma_ne_zero_of_re_pos hμ
  rw [hsub, ← legInt_fractional_cutPlane _ _ hμ hzc]
  have hpow : exp (-μ/2*(log ((x:ℂ)+1)-log ((x:ℂ)-1))) = ((x:ℂ)^2-1)^(-μ/2) * ((x-1:ℝ):ℂ)^μ := by
    rw [show ((x:ℂ)^2-1) = (((x+1)*(x-1):ℝ):ℂ) by push_cast; ring,
      legInt_cpow_ofReal (mul_pos h2 h1), legInt_cpow_ofReal h1, ← exp_add, Real.log_mul h2.ne' h1.ne',
      show (x:ℂ)+1 = ((x+1:ℝ):ℂ) by push_cast; ring, show (x:ℂ)-1 = ((x-1:ℝ):ℂ) by push_cast; ring,
      ← ofReal_log h2.le, ← ofReal_log h1.le]
    congr 1; push_cast; ring
  rw [associatedP, show (1:ℂ) - -μ = 1+μ by ring, show -μ/2 = (-μ)/2 by ring]
  rw [show (-μ)/2 = -μ/2 by ring, hpow, hz]
  field_simp

-- DLMF 14.12.3 `ferrersQ_complex_integral` is in `DLMF.Legendre.FourierTools` (needs the boundary values).

/-- associatedP cosh integral. The hypothesis `hν` is implied by `hconv` and is not used. -/
@[dlmf 14.12.E4]
theorem associatedP_cosh_integral {ν μ : ℂ} (hν : LegendreQRegular ν μ) (h : 0 < (μ-ν).re) (hconv : -1 < (μ+ν).re) {x : ℝ} (hx : 1 < x) :
    HasIntegralAtTop (fun t : ℝ => Real.sqrt 2*Gamma (μ+1/2)*(x^2-1:ℂ)^(μ/2)/(Real.sqrt π*Gamma (ν+μ+1)*Gamma (μ-ν))*cosh ((ν+1/2)*t)/(x+Real.cosh t:ℂ)^(μ+1/2)) 0 (associatedP ν (-μ) x) :=
  legInt_associatedP_cosh_integral h hconv hx

/-- olverQ real integral. -/
@[dlmf 14.12.E6]
theorem olverQ_real_integral {ν μ : ℂ} (h0 : -1/2 < μ.re) (h1 : μ.re < (ν+1).re) {x : ℝ} (hx : 1 < x) :
    HasIntegralAtTop (fun t : ℝ => Real.sqrt π*(x^2-1:ℂ)^(μ/2)/(2^μ*Gamma (μ+1/2)*Gamma (ν-μ+1))*(Real.sinh t:ℂ)^(2*μ)/(x+Real.sqrt (x^2-1)*Real.cosh t:ℂ)^(ν+μ+1)) 0 (olverQ ν μ x) := by
  have h := legInt_olverQ_complex_integral h0 h1 (legInt_one_lt_mem hx)
  have hr : exp ((log ((x:ℂ)-1)+log ((x:ℂ)+1))/2) = (Real.sqrt (x^2-1) : ℂ) := by
    have := legInt_zeta_real hx
    rw [legInt_zeta, legInt_root] at this
    push_cast at this
    linear_combination -this
  rw [hr, legInt_legendreBranchPower_real μ hx] at h
  convert h using 3 with t
  ring

/-- associatedP fourier integral. -/
@[dlmf 14.12.E7]
theorem associatedP_fourier_integral (ν : ℂ) (m : ℕ) {x : ℝ} (hx : 1 < x) :
    associatedP ν m x=poch (ν+1) m/π*∫ θ : ℝ in 0..π, (x+Real.sqrt (x^2-1)*Real.cos θ:ℂ)^ν*Real.cos (m*θ) := by
  have hx1 : ((x:ℂ)-1) ∈ slitPlane := legInt_one_lt_mem hx
  set s := Real.sqrt (x^2-1) with hs_def
  have hs : (s:ℂ) ≠ 0 := ofReal_ne_zero.2 (Real.sqrt_pos.2 (by nlinarith)).ne'
  have hb1 : legendreBranchPower 1 x = s := by
    rw [legInt_legendreBranchPower_real _ hx, show (x:ℂ)^2-1 = ((x^2-1:ℝ):ℂ) by push_cast; ring,
      hs_def, Real.sqrt_eq_rpow, ofReal_cpow (by nlinarith)]
    push_cast; ring_nf
  have hbm : legendreBranchPower (-1) x * s = 1 := by
    rw [← hb1, legendreBranchPower_mul, neg_add_cancel]; simp [legendreBranchPower]
  have hπ : (π:ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have h0 : ∀ μ : ℂ, associatedP μ 0 x = 1/π * legInt_L μ x 0 := fun μ => by
    rw [associatedP_zero_order _ hx1, legendreP_laplace _ hx.le, legInt_L]
    simp
  have key : ∀ k : ℕ, associatedP ν k x = poch (ν+1) k/π * legInt_L ν x k ∧
      associatedP ν (k+1:ℕ) x = poch (ν+1) (k+1)/π * legInt_L ν x (k+1) := by
    intro k
    induction k with
    | zero =>
      refine ⟨by rw [Nat.cast_zero, h0 ν]; simp [poch], ?_⟩
      have h7 := associatedP_recurrence_7 ν 0 hx1
      have hL : legInt_L (ν+1) x 0 = x * legInt_L ν x 0 + s * legInt_L ν x 1 := by
        simp only [legInt_L, CharP.cast_eq_zero, zero_mul, Real.cos_zero, ofReal_one, mul_one,
          Nat.cast_one, one_mul]
        rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
          ← intervalIntegral.integral_add]
        · refine intervalIntegral.integral_congr fun θ _ => ?_
          have hw := legInt_laplace_pos hx θ
          rw [cpow_add _ _ (ofReal_ne_zero.2 hw.ne'), cpow_one]; push_cast; ring
        · exact ((by simpa using legInt_cont_L ν hx 0 : Continuous fun θ : ℝ =>
            (((x + Real.sqrt (x^2-1) * Real.cos θ : ℝ)) : ℂ)^ν).intervalIntegrable _ _).const_mul _
        · exact ((by simpa using legInt_cont_L ν hx 1 : Continuous fun θ : ℝ =>
            (((x + Real.sqrt (x^2-1) * Real.cos θ : ℝ)) : ℂ)^ν * Real.cos θ).intervalIntegrable
              _ _).const_mul _
      rw [h0 ν, h0 (ν+1), hb1, hL, zero_add] at h7
      apply mul_left_cancel₀ hs
      simp only [Nat.cast_zero, zero_add, Nat.cast_one, poch_succ, poch_zero, one_mul]
      linear_combination h7
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have h6 := associatedP_recurrence_6 ν (k:ℂ) hx1
      have hr := legInt_L_rec ν hx k
      rw [show (k:ℂ)+1 = ((k+1:ℕ):ℂ) by push_cast; ring, ih.2,
        show (k:ℂ)+2 = ((k+1+1:ℕ):ℂ) by push_cast; ring, ih.1] at h6
      apply mul_left_cancel₀ hs
      simp only [poch_succ] at h6 ⊢
      simp only [show k+1+1 = k+2 by ring] at h6 hr ⊢
      push_cast at h6 hr ⊢
      linear_combination (s:ℂ) * h6 - 2*((k:ℂ)+1)*x*(poch (ν+1) k*(ν+1+k)/π*legInt_L ν x (k+1)) * hbm
        - poch (ν+1) k*(ν+1+k)/π * hr
  rw [(key m).1, legInt_L]; push_cast; rfl

/-- associatedP nat integral. -/
@[dlmf 14.12.E8]
theorem associatedP_nat_integral (n m : ℕ) (hmn : m ≤ n) {x : ℝ} (hx : 1 < x) :
    associatedP n m x=2^m*(m.factorial:ℂ)*(n+m).factorial*(x^2-1:ℂ)^((m:ℂ)/2)/(((2*m).factorial:ℂ)*(n-m).factorial*π)*∫ θ : ℝ in 0..π, (x+Real.sqrt (x^2-1)*Real.cos θ:ℂ)^(n-m)*(Real.sin θ:ℂ)^(2*m) := by
  obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le hmn
  have hpow : ((x:ℂ)^2-1)^((m:ℂ)/2) = (Real.sqrt (x^2-1):ℂ)^m := by
    rw [show (x:ℂ)^2-1 = ((x^2-1:ℝ):ℂ) by push_cast; ring,
      show (m:ℂ)/2 = (((m:ℝ)/2 : ℝ):ℂ) by push_cast; ring, ← ofReal_cpow (by nlinarith),
      ← ofReal_pow]
    congr 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast (by nlinarith)]
    ring_nf
  have hI : (∫ θ : ℝ in 0..π, (x+Real.sqrt (x^2-1)*Real.cos θ:ℂ)^(m+p-m)*(Real.sin θ:ℂ)^(2*m)) =
      legInt_Ks x p m := by
    rw [legInt_Ks, ← intervalIntegral.integral_ofReal, Nat.add_sub_cancel_left]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [legInt_w]; push_cast; ring
  rw [hI, hpow, legInt_associatedP_Ks hx, legInt_cK, Nat.add_sub_cancel_left,
    show m+p+m = 2*m+p by ring]
  ring

/-- legendreUCoordinate. -/
@[dlmf 14.12.E10]
def legendreUCoordinate (x : ℝ) : ℝ :=
  1/2*Real.log ((x+1)/(x-1))

/-- olverQ nat finite integral. -/
@[dlmf 14.12.E9]
theorem olverQ_nat_finite_integral (n m : ℕ) {x : ℝ} (hx : 1 < x) :
    olverQ n m x=1/(n.factorial:ℂ)*∫ t : ℝ in 0..legendreUCoordinate x, (x-Real.sqrt (x^2-1)*Real.cosh t:ℂ)^n*Real.cosh (m*t) := by
  rw [show legendreUCoordinate x = legInt_u x from rfl]
  have hx1 : (x:ℂ)-1 ∈ slitPlane := legInt_one_lt_mem hx
  set s := Real.sqrt (x^2-1) with hs_def
  have hs : (s:ℂ) ≠ 0 := ofReal_ne_zero.2 (Real.sqrt_pos.2 (by nlinarith)).ne'
  have hb1 : legendreBranchPower 1 x = s := by
    rw [legInt_legendreBranchPower_real _ hx, show (x:ℂ)^2-1 = ((x^2-1:ℝ):ℂ) by push_cast; ring,
      hs_def, Real.sqrt_eq_rpow, ofReal_cpow (by nlinarith)]
    push_cast; ring_nf
  have hbm : legendreBranchPower (-1) x * s = 1 := by
    rw [← hb1, legendreBranchPower_mul, neg_add_cancel]; simp [legendreBranchPower]
  have hf : (n.factorial:ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
  have hI : (∫ t : ℝ in 0..legInt_u x, (x-Real.sqrt (x^2-1)*Real.cosh t:ℂ)^n*Real.cosh (m*t)) =
      legInt_M x n m := by
    rw [legInt_M, ← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [legInt_f, legInt_V]; push_cast; ring
  rw [hI]
  have h0 : ∀ k : ℕ, olverQ k 0 x = legInt_M x k 0 / k.factorial := fun k => by
    rw [legInt_olverQ_nat_zero_order _ hx1, legInt_legendreQ_M hx]
  have key : ∀ m : ℕ, olverQ n m x = legInt_M x n m / n.factorial ∧
      olverQ n (m+1:ℕ) x = legInt_M x n (m+1) / n.factorial := by
    intro m
    induction m with
    | zero =>
      refine ⟨by simpa using h0 n, ?_⟩
      have h7 := olverQ_recurrence_7 (n:ℂ) 0 hx1
      have h1 := legInt_M_one x n
      rw [hb1, zero_add, h0 n, show (n:ℂ)+1 = ((n+1:ℕ):ℂ) by push_cast; ring, h0 (n+1)] at h7
      apply mul_left_cancel₀ hs
      simp only [zero_add, Nat.cast_one]
      apply_fun ((↑) : ℝ → ℂ) at h1
      rw [Nat.factorial_succ] at h7
      push_cast at h1 h7
      have e : ((n:ℂ)+1)*((legInt_M x (n+1) 0:ℂ)/(((n:ℂ)+1)*n.factorial)) =
          (legInt_M x (n+1) 0:ℂ)/n.factorial := by
        have : (n:ℂ)+1 ≠ 0 := by norm_cast
        field_simp
      linear_combination -h7 - e - h1/(n.factorial:ℂ)
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have h6 := olverQ_recurrence_6 (n:ℂ) (k:ℂ) hx1
      have hr := legInt_M_ord hx n k
      rw [show (k:ℂ)+1 = ((k+1:ℕ):ℂ) by push_cast; ring, ih.2,
        show (k:ℂ)+2 = ((k+1+1:ℕ):ℂ) by push_cast; ring, ih.1] at h6
      have hnk : ((n:ℂ)+((k+1+1:ℕ):ℂ)) ≠ 0 := by norm_cast
      apply mul_left_cancel₀ (mul_ne_zero hnk hs)
      apply_fun ((↑) : ℝ → ℂ) at hr
      push_cast at hr h6 ⊢
      linear_combination (s:ℂ) * h6 + 2*((k:ℂ)+1)*x*((legInt_M x n (k+1):ℂ)/n.factorial)*hbm -
        hr/(n.factorial:ℂ)
  rw [(key m).1]; ring

/-- olverQ nat interval integral. -/
@[dlmf 14.12.E11]
theorem olverQ_nat_interval_integral (n m : ℕ) {x : ℝ} (hx : 1 < x) :
    olverQ n m x=(x^2-1:ℂ)^((m:ℂ)/2)/(2^(n+1)*(n.factorial:ℂ))*∫ t : ℝ in -1..1, (1-t^2:ℂ)^n/(x-t:ℂ)^(n+m+1) := by
  have hx1 : (x:ℂ)-1 ∈ slitPlane := legInt_one_lt_mem hx
  set s := Real.sqrt (x^2-1) with hs_def
  have hs : (s:ℂ) ≠ 0 := ofReal_ne_zero.2 (Real.sqrt_pos.2 (by nlinarith)).ne'
  have hss : (s:ℂ)^2 = (x:ℂ)^2-1 := by
    rw [← ofReal_pow, hs_def, Real.sq_sqrt (by nlinarith)]; push_cast; ring
  have hb1 : legendreBranchPower 1 x = s := by
    rw [legInt_legendreBranchPower_real _ hx, show (x:ℂ)^2-1 = ((x^2-1:ℝ):ℂ) by push_cast; ring,
      hs_def, Real.sqrt_eq_rpow, ofReal_cpow (by nlinarith)]
    push_cast; ring_nf
  have hbm : legendreBranchPower (-1) x * s = 1 := by
    rw [← hb1, legendreBranchPower_mul, neg_add_cancel]; simp [legendreBranchPower]
  have hpow : ((x:ℂ)^2-1)^((m:ℂ)/2) = (s:ℂ)^m := by
    rw [show (x:ℂ)^2-1 = ((x^2-1:ℝ):ℂ) by push_cast; ring,
      show (m:ℂ)/2 = (((m:ℝ)/2 : ℝ):ℂ) by push_cast; ring, ← ofReal_cpow (by nlinarith),
      ← ofReal_pow]
    congr 1
    rw [hs_def, Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast (by nlinarith)]
    ring_nf
  have hI : (∫ t : ℝ in -1..1, (1-t^2:ℂ)^n/(x-t:ℂ)^(n+m+1)) = legInt_A x n (n+m+1) := by
    rw [legInt_A, ← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr fun t _ => ?_
    push_cast; ring
  rw [hI, hpow]
  set C : ℂ := 1/(2^(n+1)*(n.factorial:ℂ)) with hC
  have h0 : ∀ k : ℕ, olverQ k 0 x = legInt_A x k (k+1) / (2^(k+1)*k.factorial) := fun k => by
    rw [legInt_olverQ_nat_zero_order _ hx1, legInt_legendreQ_A hx, div_div]
  have key : ∀ m : ℕ, olverQ n m x = C * s^m * legInt_A x n (n+m+1) ∧
      olverQ n (m+1:ℕ) x = C * s^(m+1) * legInt_A x n (n+(m+1)+1) := by
    intro m
    induction m with
    | zero =>
      refine ⟨by rw [Nat.cast_zero, h0 n, hC]; simp; ring, ?_⟩
      have h7 := olverQ_recurrence_7 (n:ℂ) 0 hx1
      have hb := legInt_A_b hx n
      rw [hb1, zero_add, h0 n, show (n:ℂ)+1 = ((n+1:ℕ):ℂ) by push_cast; ring, h0 (n+1)] at h7
      apply mul_left_cancel₀ hs
      simp only [zero_add, Nat.cast_one]
      apply_fun ((↑) : ℝ → ℂ) at hb
      rw [Nat.factorial_succ] at h7
      push_cast at hb h7
      have hn1 : (n:ℂ)+1 ≠ 0 := by norm_cast
      have hf : (n.factorial:ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
      have e : ((n:ℂ)+1)*((legInt_A x (n+1) (n+1+1):ℂ)/(2^(n+1+1)*(((n:ℂ)+1)*n.factorial))) =
          C * (legInt_A x (n+1) (n+2):ℂ)/2 := by
        rw [hC]; field_simp; ring
      rw [show n+1+1 = n+2 by ring] at e h7 ⊢
      have e2 : (legInt_A x n (n+1):ℂ)/(2^(n+1)*n.factorial) = C * legInt_A x n (n+1) := by
        rw [hC]; ring
      rw [e2] at h7
      linear_combination -h7 - e - C/2*hb - C*(legInt_A x n (n+2):ℂ)*hss
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have h6 := olverQ_recurrence_6 (n:ℂ) (k:ℂ) hx1
      have hord := legInt_A_ord hx n (n+k+1)
      rw [show (k:ℂ)+1 = ((k+1:ℕ):ℂ) by push_cast; ring, ih.2,
        show (k:ℂ)+2 = ((k+1+1:ℕ):ℂ) by push_cast; ring, ih.1] at h6
      have hnk : ((n:ℂ)+((k+1+1:ℕ):ℂ)) ≠ 0 := by norm_cast
      apply mul_left_cancel₀ (mul_ne_zero hnk hs)
      apply_fun ((↑) : ℝ → ℂ) at hord
      simp only [show n+(k+1)+1 = n+k+1+1 by ring, show n+(k+1+1)+1 = n+k+1+2 by ring] at h6 ⊢
      push_cast at hord h6 ⊢
      linear_combination (s:ℂ) * h6 + 2*((k:ℂ)+1)*x*C*(s:ℂ)^(k+1)*(legInt_A x n (n+k+1+1):ℂ)*hbm
        + C*(s:ℂ)^(k+1)*hord - ((n:ℂ)+k+2)*C*(s:ℂ)^(k+1)*(legInt_A x n (n+k+1+2):ℂ)*hss
  rw [(key m).1, hC]; ring

/-! ### Helpers for DLMF 14.12.12 (prefix `legIR_`) -/

/-- For real `t > 1`, `t - 1` lies in the slit plane. -/
theorem legIR_sub_one_mem {t : ℝ} (ht : 1 < t) : (t:ℂ) - 1 ∈ slitPlane := by
  rw [show (t:ℂ)-1 = ((t-1:ℝ):ℂ) by push_cast; ring]
  exact ofReal_mem_slitPlane.2 (by linarith)

/-- A terminating `₂F₁(-N,-n;c+1;w)` sum with `w ≥ 0` has real part at least `1`. -/
theorem legIR_sum_re_ge (N n c : ℕ) {w : ℝ} (hw : 0 ≤ w) :
    1 ≤ (∑ k ∈ Finset.range (N+1), gaussHGCoeff (-(N:ℂ)) (-(n:ℂ)) ((c:ℂ)+1) k * (w:ℂ)^k).re := by
  have hterm : ∀ k, gaussHGCoeff (-(N:ℂ)) (-(n:ℂ)) ((c:ℂ)+1) k * (w:ℂ)^k =
      ((((N.descFactorial k * n.descFactorial k : ℕ):ℝ) / (((c+1).ascFactorial k * k ! : ℕ):ℝ) * w^k : ℝ) : ℂ) := by
    intro k
    have h1 : ((-1:ℂ))^k * (-1)^k = 1 := by rw [← mul_pow]; norm_num
    rw [gaussHGCoeff, poch_neg_coe_nat, poch_neg_coe_nat, show (c:ℂ)+1 = ((c+1:ℕ):ℂ) by push_cast; ring,
      poch, ascPochhammer_nat_eq_natCast_ascFactorial]
    push_cast
    linear_combination ((N.descFactorial k:ℂ) * n.descFactorial k / (((c+1).ascFactorial k:ℂ) * k !) * (w:ℂ)^k) * h1
  simp_rw [hterm]
  rw [← ofReal_sum, ofReal_re]
  have h0 : ∀ k ∈ Finset.range (N+1), 0 ≤ (((N.descFactorial k * n.descFactorial k : ℕ):ℝ) / (((c+1).ascFactorial k * k ! : ℕ):ℝ) * w^k) :=
    fun k _ => by positivity
  refine le_trans ?_ (Finset.single_le_sum h0 (Finset.mem_range.2 (Nat.succ_pos N)))
  simp

/-- Norm of the branch power `(t²-1)^{m/2}` for real `t > 1`. -/
theorem legIR_norm_bp (m : ℕ) {t : ℝ} (ht : 1 < t) :
    ‖legendreBranchPower m t‖ = Real.exp (m/2*(Real.log (t-1) + Real.log (t+1))) := by
  rw [legendreBranchPower, norm_exp, show (t:ℂ)-1 = ((t-1:ℝ):ℂ) by push_cast; ring,
    show (t:ℂ)+1 = ((t+1:ℝ):ℂ) by push_cast; ring, ← ofReal_log (by linarith), ← ofReal_log (by linarith)]
  simp

/-- For integers `0 ≤ m ≤ n`, `|P^m_n(t)| ≥ C (t²-1)^{m/2}` on `t > 1`, via Pfaff to a
terminating series with nonnegative terms. -/
theorem legIR_norm_associatedP_ge (n m : ℕ) (hmn : m ≤ n) : ∃ C > 0, ∀ t : ℝ, 1 < t →
    C * ‖legendreBranchPower m t‖ ≤ ‖associatedP n m t‖ := by
  obtain ⟨N, rfl⟩ := Nat.exists_eq_add_of_le hmn
  set K := poch (((m+N:ℕ):ℂ) - m + 1) (2*m) / 2^m with hKdef
  have hK : K ≠ 0 := by
    rw [hKdef, show ((m+N:ℕ):ℂ) - m + 1 = ((N+1:ℕ):ℂ) by push_cast; ring, poch,
      ascPochhammer_nat_eq_natCast_ascFactorial]
    have : (N+1).ascFactorial (2*m) ≠ 0 := (Nat.ascFactorial_pos _ _).ne'
    exact div_ne_zero (by exact_mod_cast this) (pow_ne_zero _ two_ne_zero)
  have hc : ∀ k : ℕ, (m:ℂ)+1 ≠ -(k:ℂ) := fun k h => by
    have := congrArg re h; simp at this; linarith
  have hΓ : Gamma ((m:ℂ)+1) ≠ 0 := Gamma_ne_zero (fun k h => hc k h)
  refine ⟨‖K‖ / ‖Gamma ((m:ℂ)+1)‖, by positivity, fun t ht => ?_⟩
  have hs := legIR_sub_one_mem ht
  rw [associatedP_integer_hypergeometric_8 _ m hs]
  have h1z : 1 - (1-(t:ℂ))/2 = (((1+t)/2 : ℝ) : ℂ) := by push_cast; ring
  have hz : (1-(t:ℂ))/2 ∈ cutPlane := by
    rw [mem_cutPlane, h1z]; exact ofReal_mem_slitPlane.2 (by linarith)
  have hw : (1-(t:ℂ))/2/((1-(t:ℂ))/2-1) = (((t-1)/(t+1) : ℝ) : ℂ) := by
    have : (t:ℂ)+1 ≠ 0 := by
      rw [show (t:ℂ)+1 = ((t+1:ℝ):ℂ) by push_cast; ring]; exact ofReal_ne_zero.2 (by linarith)
    have hd : (1-(t:ℂ))/2-1 ≠ 0 := by
      rw [show (1-(t:ℂ))/2-1 = -((t:ℂ)+1)/2 by ring]; exact div_ne_zero (neg_ne_zero.2 this) two_ne_zero
    push_cast; rw [div_eq_div_iff hd this]; ring
  have hwn : ‖(1-(t:ℂ))/2/((1-(t:ℂ))/2-1)‖ < 1 := by
    rw [hw, norm_real, Real.norm_eq_abs, abs_lt]
    constructor
    · rw [lt_div_iff₀ (by linarith)]; linarith
    · rw [div_lt_iff₀ (by linarith)]; linarith
  rw [regularizedGaussHG_symm _ _ _ hz, regularizedGaussHG_pfaff _ _ _ hz,
    regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hwn, regularizedGaussHGFun_eq_div_Gamma hc,
    show (m:ℂ) - ((m+N:ℕ):ℂ) = -(N:ℂ) by push_cast; ring,
    show (m:ℂ) + 1 - (((m+N:ℕ):ℂ) + m + 1) = -((m+N:ℕ):ℂ) by push_cast; ring,
    ordinaryHypergeometric_eq_sum_neg_nat, hw, h1z]
  have hsum := le_trans (legIR_sum_re_ge N (m+N) m (w := (t-1)/(t+1))
    (div_nonneg (by linarith) (by linarith))) (re_le_norm _)
  have hpow : 1 ≤ ‖((((1+t)/2 : ℝ)) : ℂ)^(-(-(N:ℂ)))‖ := by
    rw [norm_cpow_eq_rpow_re_of_pos (by linarith)]
    exact Real.one_le_rpow (by linarith) (by simp)
  rw [norm_mul, norm_mul, norm_mul, norm_div _ (Gamma ((m:ℂ)+1))]
  have hbp : 0 ≤ ‖legendreBranchPower (m:ℂ) (t:ℂ)‖ := norm_nonneg _
  have hΓn : 0 < ‖Gamma ((m:ℂ)+1)‖ := norm_pos_iff.2 hΓ
  calc ‖K‖ / ‖Gamma ((m:ℂ)+1)‖ * ‖legendreBranchPower (m:ℂ) (t:ℂ)‖
      = ‖K‖ * ‖legendreBranchPower (m:ℂ) (t:ℂ)‖ * (1 * (1 / ‖Gamma ((m:ℂ)+1)‖)) := by ring
    _ ≤ _ := by gcongr

/-- `𝑸^m_n(x) → 0` as `x → ∞` (from DLMF 14.8.15). -/
theorem legIR_olverQ_tendsto_zero (n m : ℕ) :
    Tendsto (fun x : ℝ => olverQ n m x) atTop (𝓝 0) := by
  have hν : ∀ k : ℕ, (n:ℂ) ≠ -k-3/2 := fun k h => by
    have := congrArg re h; simp at this; linarith
  refine (legendre_singular_15 (n:ℂ) (m:ℂ) hν).symm.tendsto_nhds ?_
  have h : Tendsto (fun x : ℝ => (Real.sqrt π/Gamma ((n:ℂ)+3/2)) * ((((2*x)^(n+1))⁻¹ : ℝ) : ℂ)) atTop (𝓝 0) := by
    have := (continuous_ofReal.tendsto 0).comp (tendsto_inv_atTop_zero.comp
      ((tendsto_pow_atTop (Nat.succ_ne_zero n)).comp (tendsto_id.const_mul_atTop (two_pos (α := ℝ)))))
    simpa using this.const_mul (Real.sqrt π/Gamma ((n:ℂ)+3/2))
  refine h.congr' ?_
  filter_upwards with x
  rw [show (n:ℂ)+1 = ((n+1:ℕ):ℂ) by push_cast; ring, cpow_natCast]
  push_cast; ring


/-- olverQ nat reduction integral. -/
@[dlmf 14.12.E12]
theorem olverQ_nat_reduction_integral (n m : ℕ) (hmn : m ≤ n) {x : ℝ} (hx : 1 < x) :
    HasIntegralAtTop (fun t : ℝ => associatedP n m x/((n-m).factorial:ℂ)/((t^2-1:ℂ)*(associatedP n m t)^2)) x (olverQ n m x) := by
  obtain ⟨C, hC, hPC⟩ := legIR_norm_associatedP_ge n m hmn
  have hPne : ∀ t : ℝ, 1 < t → associatedP n m t ≠ 0 := fun t ht h => by
    have h1 := hPC t ht
    rw [h, norm_zero, legIR_norm_bp m ht] at h1
    have : 0 < C * Real.exp (m/2*(Real.log (t-1) + Real.log (t+1))) := by positivity
    linarith
  have hfac : Gamma ((n:ℂ)-m+1) = ((n-m).factorial:ℂ) := by
    rw [show (n:ℂ)-m+1 = ((n-m:ℕ):ℂ)+1 by push_cast [Nat.cast_sub hmn]; ring, Gamma_nat_eq_factorial]
  have hfac0 : ((n-m).factorial:ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  set F : ℝ → ℂ := fun s => -associatedP n m x * (olverQ n m s / associatedP n m s) with hF
  have hderiv : ∀ t : ℝ, 1 < t → HasDerivAt F
      (associatedP n m x/((n-m).factorial:ℂ)/((t^2-1:ℂ)*(associatedP n m t)^2)) t := by
    intro t ht
    have hs := legIR_sub_one_mem ht
    have hQd := ((olverQ_analytic n m) _ hs).differentiableAt.hasDerivAt
    have hPd := ((associatedP_analytic n m) _ hs).differentiableAt.hasDerivAt
    have h := ((hQd.div hPd (hPne t ht)).comp_ofReal).const_mul (-associatedP n m x)
    have hw := olverQ_wronskian_pos (n:ℂ) (m:ℂ) hs
    rw [LegendreWronskian, hfac] at hw
    have ht2 : (t:ℂ)^2-1 ≠ 0 := by
      rw [show (t:ℂ)^2-1 = ((t^2-1:ℝ):ℂ) by push_cast; ring]; exact ofReal_ne_zero.2 (by nlinarith)
    convert h using 1
    have hP := hPne t ht
    rw [show deriv (olverQ n m) t * associatedP n m t - olverQ n m t * deriv (associatedP n m) t
      = associatedP n m t * deriv (olverQ n m) t - olverQ n m t * deriv (associatedP n m) t by ring, hw]
    field_simp
  have hcont : ∀ t : ℝ, 1 < t → ContinuousAt (fun t : ℝ => associatedP n m x/((n-m).factorial:ℂ)/((t^2-1:ℂ)*(associatedP n m t)^2)) t := by
    intro t ht
    have hs := legIR_sub_one_mem ht
    have hPc : ContinuousAt (fun s : ℝ => associatedP n m s) t :=
      ((associatedP_analytic n m) _ hs).continuousAt.comp continuous_ofReal.continuousAt
    have ht2 : (t:ℂ)^2-1 ≠ 0 := by
      rw [show (t:ℂ)^2-1 = ((t^2-1:ℝ):ℂ) by push_cast; ring]; exact ofReal_ne_zero.2 (by nlinarith)
    exact continuousAt_const.div (((continuous_ofReal.continuousAt.pow 2).sub continuousAt_const).mul
      (hPc.pow 2)) (mul_ne_zero ht2 (pow_ne_zero _ (hPne t ht)))
  have hint : ∀ R, x ≤ R → ∫ t in x..R, associatedP n m x/((n-m).factorial:ℂ)/((t^2-1:ℂ)*(associatedP n m t)^2) = F R - F x := by
    intro R hR
    have hmem : ∀ t ∈ uIcc x R, 1 < t := fun t ht => by
      rw [uIcc_of_le hR] at ht; linarith [ht.1]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hderiv t (hmem t ht))
      (ContinuousOn.intervalIntegrable fun t ht => (hcont t (hmem t ht)).continuousWithinAt)
  have hFx : F x = -olverQ n m x := by
    simp only [hF]; field_simp [hPne x hx]
  have hQP : Tendsto (fun R : ℝ => olverQ n m R / associatedP n m R) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (by simpa using ((legIR_olverQ_tendsto_zero n m).norm.div_const C))
    filter_upwards [eventually_ge_atTop (2:ℝ)] with R hR
    have h1 := hPC R (by linarith)
    rw [legIR_norm_bp m (by linarith)] at h1
    have he : 1 ≤ Real.exp (m/2*(Real.log (R-1) + Real.log (R+1))) :=
      Real.one_le_exp (by
        have := Real.log_nonneg (show (1:ℝ) ≤ R-1 by linarith)
        have := Real.log_nonneg (show (1:ℝ) ≤ R+1 by linarith)
        positivity)
    rw [norm_div, div_le_div_iff₀ (by nlinarith) hC]
    exact mul_le_mul_of_nonneg_left (by nlinarith) (norm_nonneg _)
  have hlim : Tendsto (fun R => F R - F x) atTop (𝓝 (olverQ n m x)) := by
    have := ((hQP.const_mul (-associatedP n m x)).sub_const (F x))
    rw [hFx, mul_zero, zero_sub, neg_neg] at this
    rw [hFx]
    exact this
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop x] with R hR
  exact (hint R hR).symm

/-- olverQ nat neumann. -/
@[dlmf 14.12.E13]
theorem olverQ_nat_neumann (n : ℕ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    olverQ n 0 z=1/(2*(n.factorial:ℂ))*∫ t : ℝ in -1..1, legendreP n t/(z-t) := by
  have hreg : LegendreQRegular (n:ℂ) 0 := fun k hk => by
    have := congrArg re hk; simp at this; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  have hf : (n.factorial:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hi : ∫ t : ℝ in -1..1, legendreP n t/(z-t) =
      ∫ t : ℝ in -1..1, DLMF.OrthogonalPolynomials.legendrePolyP n t/(z-t) := by
    refine intervalIntegral.integral_congr_ae ?_
    have : ∀ᵐ t : ℝ ∂volume, t ≠ -1 := by
      simp [ae_iff]
    filter_upwards [this] with t ht htm
    rw [uIoc_of_le (by norm_num)] at htm
    rw [legendreP_nat n (Or.inl (by simp; linarith [htm.1]))]
  rw [olverQ_normalization hreg, associatedQ_zero_order _ hz, add_zero, Gamma_nat_eq_factorial, hi,
    legendreQ_nat_eq_integral n hz]
  simp
  field_simp

/-- olverQ nat heine. -/
@[dlmf 14.12.E14]
theorem olverQ_nat_heine (n : ℕ) {x : ℝ} (hx : 1 < x) :
    HasIntegralAtTop (fun t : ℝ => 1/((n.factorial:ℂ)*(x+Real.sqrt (x^2-1)*Real.cosh t:ℂ)^(n+1))) 0 (olverQ n 0 x) := by
  rw [legInt_olverQ_nat_zero_order _ (legInt_one_lt_mem hx)]
  refine ((legInt_heine x hx n).div_const (n.factorial:ℂ)).congr fun R => ?_
  rw [← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_div]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [legInt_W]; push_cast
  field_simp

/-- associatedP complex integral. -/
@[dlmf 14.25.E1]
theorem associatedP_complex_integral {ν μ : ℂ} (h0 : -1 < ν.re) (h1 : ν.re < μ.re) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    HasIntegralAtTop (fun t : ℝ => legendreBranchPower μ z/(2^ν*Gamma (μ-ν)*Gamma (ν+1))*((Real.sinh t:ℂ)^(2*ν+1)/(z+Real.cosh t)^(ν+μ+1))) 0 (associatedP ν (-μ) z) :=
  legInt_associatedP_complex_integral h0 h1 hz

/-- olverQ complex integral. -/
@[dlmf 14.25.E2]
theorem olverQ_complex_integral {ν μ : ℂ} (h0 : -1/2 < μ.re) (h1 : μ.re < (ν+1).re) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    HasIntegralAtTop (fun t : ℝ => Real.sqrt π*legendreBranchPower μ z/(2^μ*Gamma (μ+1/2)*Gamma (ν-μ+1))*((Real.sinh t:ℂ)^(2*μ)/(z+exp ((log (z-1)+log (z+1))/2)*Real.cosh t)^(ν+μ+1))) 0 (olverQ ν μ z) :=
  legInt_olverQ_complex_integral h0 h1 hz

/-- ferrersP negative order integral. -/
@[dlmf 14.6.E6]
theorem ferrersP_negative_order_integral (ν : ℂ) (m : ℕ) (hm : 0 < m) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersP ν (-m) x=(1-x^2:ℂ)^(-(m:ℂ)/2)*((fun f : ℝ → ℂ => fun x => ∫ t : ℝ in x..1, f t)^[m]) (ferrersP ν 0) x := by
  rw [legInt_iterate_ferrers ν m ⟨hx.1, hx.2.le⟩, legInt_H, ferrersP]
  have h1 : (0:ℝ) < 1 + x := by linarith [hx.1]
  have h2 : (0:ℝ) < 1 - x := by linarith [hx.2]
  have hreal : ((1+x)/(1-x)) ^ (-(m:ℝ)/2) = (1-x^2) ^ (-(m:ℝ)/2) * (1-x)^m := by
    rw [Real.div_rpow h1.le h2.le, show 1 - x^2 = (1+x)*(1-x) by ring,
      Real.mul_rpow h1.le h2.le, ← Real.rpow_natCast (1-x) m, div_eq_mul_inv, mul_assoc,
      ← Real.rpow_neg h2.le, ← Real.rpow_add h2]
    congr 2; ring
  have hc := congrArg (fun r : ℝ => (r:ℂ)) hreal
  rw [ofReal_mul, ofReal_cpow (div_pos h1 h2).le, ofReal_cpow (by nlinarith), ofReal_pow] at hc
  push_cast at hc
  push_cast
  rw [hc, show (1:ℂ) - -(m:ℂ) = m+1 by ring]
  ring

/-- associatedP negative order integral. -/
@[dlmf 14.6.E7]
theorem associatedP_negative_order_integral (ν : ℂ) (m : ℕ) (hm : 0 < m) {x : ℝ} (hx : 1 < x) :
    associatedP ν (-m) x=(x^2-1:ℂ)^(-(m:ℂ)/2)*((fun f : ℝ → ℂ => fun x => ∫ t : ℝ in 1..x, f t)^[m]) (fun x : ℝ => associatedP ν 0 x) x := by
  have hz : (x:ℂ)-1 ∈ slitPlane := Or.inl (by simp; linarith)
  rw [legInt_iterate_associated ν m hx.le, legInt_associatedP_neg_nat ν m hz,
    legInt_legendreBranchPower_real _ hx]

/-- associatedQ negative order integral. -/
@[dlmf 14.6.E8]
theorem associatedQ_negative_order_integral (ν : ℂ) (m : ℕ) (hm : 0 < m) (hν : (m:ℝ)-1 < ν.re) {x : ℝ} (hx : 1 < x) :
    associatedQ ν (-m) x=(-1)^m*(x^2-1:ℂ)^(-(m:ℂ)/2)*((fun f : ℝ → ℂ => fun x => improperAtTop f x)^[m]) (fun x : ℝ => associatedQ ν 0 x) x := by
  rw [legInt_iterate_Q ν m hν hx, legInt_g, legInt_legendreBranchPower_real _ hx]
  have hne : ((x:ℂ)^2-1) ≠ 0 := by
    rw [show (x:ℂ)^2-1 = ((x^2-1:ℝ):ℂ) by push_cast; ring]
    exact_mod_cast (by nlinarith : (x^2-1:ℝ) ≠ 0)
  have hc : ((x:ℂ)^2-1)^(-(m:ℂ)/2) * ((x:ℂ)^2-1)^((m:ℂ)/2) = 1 := by
    rw [← cpow_add _ _ hne, show -(m:ℂ)/2 + (m:ℂ)/2 = 0 by ring, cpow_zero]
  have hsq : (-1:ℂ)^m*(-1)^m = 1 := by rw [← mul_pow]; norm_num
  linear_combination (-(associatedQ ν (-m) x)*(-1)^m*(-1)^m) * hc - (associatedQ ν (-m) x) * hsq

/-- DLMF 14.6.7 extended to the principal complex sheet by iterated segment primitives. -/
@[dlmf 14.6.E7]
theorem associatedP_negative_order_integral_complex (ν : ℂ) (m : ℕ) (hm : 0 < m)
    {z : ℂ} (hz : z-1 ∈ slitPlane) :
    associatedP ν (-m) z=legendreBranchPower (-m) z*
      ((fun f : ℂ → ℂ => fun z => segmentIntegral f 1 z)^[m]) (associatedP ν 0) z := by
  rw [legInt_iterate_segment ν m (Or.inr hz), legInt_associatedP_neg_nat ν m hz]

/-- DLMF 14.6.8: a tail joined to the positive real axis, with actual convergence. -/
@[dlmf 14.6.E8]
theorem associatedQ_negative_order_integral_complex (ν : ℂ) (m : ℕ) (hm : 0 < m)
    (hν : (m:ℝ)-1 < ν.re) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    associatedQ ν (-m) z=(-1)^m*legendreBranchPower (-m) z*
      ((fun f : ℂ → ℂ => fun z => segmentIntegral f z 2+improperAtTop (fun t : ℝ => f t) 2)^[m])
        (associatedQ ν 0) z := by
  rw [legInt_iterate_Qc ν m hν hz, legInt_g]
  have hc : legendreBranchPower (-m) z * legendreBranchPower m z = 1 := by
    rw [legendreBranchPower_mul, neg_add_cancel]; simp [legendreBranchPower]
  have hsq : (-1:ℂ)^m*(-1)^m = 1 := by rw [← mul_pow]; norm_num
  linear_combination (-(associatedQ ν (-m) z)*(-1)^m*(-1)^m) * hc - (associatedQ ν (-m) z) * hsq

end DLMF.Legendre
