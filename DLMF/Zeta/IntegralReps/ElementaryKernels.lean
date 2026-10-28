/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Gamma.Polygamma
public import DLMF.Zeta.Riemann
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
public import DLMF.Gamma.PolygammaHurwitz

/-!
# Zeta integrals with elementary kernels

Real elementary-kernel representations of the Riemann zeta function, with endpoint estimates.

Source references and common attribution are retained in
`DLMF.Zeta.IntegralReps`.
-/

@[expose] public noncomputable section

open Complex Filter Topology MeasureTheory Set Finset

open scoped Real

namespace DLMF.Zeta

/-- `t^{s-1} e^{-t}/(1 - e^{-t}) = t^{s-1}/(e^t - 1)` for `t > 0`. -/
lemma q25a_exp_div_one_sub_exp {s : ℂ} {t : ℝ} (ht : 0 < t) :
    (t : ℂ) ^ (s - 1) * cexp (-((1 : ℝ) * (t : ℂ))) / (1 - cexp (-(t : ℂ))) =
      (t : ℂ) ^ (s - 1) / (cexp t - 1) := by
  have h1 : cexp (t : ℂ) - 1 ≠ 0 := by
    rw [sub_ne_zero, ← ofReal_exp]
    exact_mod_cast (Real.one_lt_exp_iff.mpr ht).ne'
  have h2 : cexp (t : ℂ) ≠ 0 := Complex.exp_ne_zero _
  have h3 : (1 : ℂ) - cexp (-(t : ℂ)) ≠ 0 := by
    rw [sub_ne_zero, ← ofReal_neg, ← ofReal_exp]
    exact_mod_cast (Real.exp_lt_one_iff.mpr (by linarith)).ne'
  rw [ofReal_one, one_mul, Complex.exp_neg]
  field_simp
/-- The integrand of 25.5.1 is integrable for `Re s > 1`. -/
lemma q25a_integrableOn_exp_sub_one {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 1) / (cexp x - 1)) (Ioi 0) := by
  set σ : ℂ := (s.re : ℂ)
  have hσ : 1 < σ.re := by simpa [σ] using hs
  have hval := DLMF.Gamma.integral_cpow_mul_exp_div_one_sub_exp hσ (x := 1) one_pos
  have hne : (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (σ - 1) * cexp (-((1 : ℝ) * (t : ℂ))) /
      (1 - cexp (-(t : ℂ)))) ≠ 0 := by
    rw [hval]
    refine mul_ne_zero (Gamma_ne_zero_of_re_pos (by linarith)) ?_
    rw [show (∑' k : ℕ, 1 / ((k : ℂ) + ((1 : ℝ) : ℂ)) ^ σ) = riemannZeta σ by
      rw [zeta_eq_tsum_one_div_nat_add_one_cpow hσ]; push_cast; rfl]
    exact riemannZeta_ne_zero_of_one_lt_re hσ
  have hg := Integrable.of_integral_ne_zero hne
  refine hg.norm.mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    refine ContinuousAt.continuousWithinAt ?_
    refine ContinuousAt.div ?_ ?_ ?_
    · exact (continuousAt_ofReal_cpow_const _ _ (Or.inr hx0.ne'))
    · exact (Complex.continuous_exp.comp continuous_ofReal).continuousAt.sub continuousAt_const
    · rw [sub_ne_zero, ← ofReal_exp]
      exact_mod_cast (Real.one_lt_exp_iff.mpr hx0).ne'
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0 : ℝ) < t := ht
    rw [q25a_exp_div_one_sub_exp ht0, norm_div, norm_div,
      norm_cpow_eq_rpow_re_of_pos ht0, norm_cpow_eq_rpow_re_of_pos ht0]
    simp [σ]
/-- `∫₀^∞ eᵗ tˢ/(eᵗ-1)² dt = Γ(s+1) ζ(s)` for `Re s > 1`, by termwise integration of
`eᵗ/(eᵗ-1)² = ∑ k e^{-kt}`. -/
lemma q25a_integral_exp_sub_one_sq {s : ℂ} (hs : 1 < s.re) :
    ∫ t in Ioi (0 : ℝ), cexp t * (t : ℂ) ^ s / (cexp t - 1) ^ 2 =
      Gamma (s + 1) * riemannZeta s := by
  have hs1 : 0 < (s + 1).re := by simp; linarith
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs; linarith
  set F : ℕ → ℝ → ℂ := fun k t => (t : ℂ) ^ s * ((k : ℂ) * cexp (-((k : ℂ) * t))) with hF
  have hFint (k : ℕ) : Integrable (F k) (volume.restrict (Ioi 0)) := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [hF]
    · have := (DLMF.Gamma.integrableOn_cpow_mul_exp_neg_mul hs1
        (r := (k : ℝ)) (by exact_mod_cast hk)).mul_const (k : ℂ)
      refine IntegrableOn.congr_fun this (fun t _ => ?_) measurableSet_Ioi
      simp only [hF, add_sub_cancel_right, ofReal_natCast]; ring
  have hFval (k : ℕ) : ∫ t in Ioi (0 : ℝ), F k t = Gamma (s + 1) * (1 / (k : ℂ) ^ s) := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [hF, zero_cpow hs0]
    · have hk' : (0 : ℝ) < k := by exact_mod_cast hk
      have h := integral_cpow_mul_exp_neg_mul_Ioi hs1 hk'
      simp only [add_sub_cancel_right, ofReal_natCast] at h
      rw [show (fun t => F k t) = fun t : ℝ => (k : ℂ) * ((t : ℂ) ^ s * cexp (-((k : ℂ) * t))) by
        funext t; simp only [hF]; ring, integral_const_mul, h]
      have hkc : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
      have harg : ((k : ℂ)).arg ≠ π := by
        rw [← ofReal_natCast, arg_ofReal_of_nonneg hk'.le]; exact Real.pi_ne_zero.symm
      rw [one_div, inv_cpow _ _ harg, cpow_add _ _ hkc, cpow_one]
      field_simp
  have hnorm (k : ℕ) : ∫ t in Ioi (0 : ℝ), ‖F k t‖ = k * ((1 / (k : ℝ)) ^ (s.re + 1) *
      Real.Gamma (s.re + 1)) := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [hF]
    · have hk' : (0 : ℝ) < k := by exact_mod_cast hk
      rw [← Real.integral_rpow_mul_exp_neg_mul_Ioi (by linarith) hk', ← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      have ht' : (0 : ℝ) < t := ht
      simp only [hF]
      rw [norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos ht',
        show -((k : ℂ) * t) = ((-((k : ℝ) * t) : ℝ) : ℂ) by push_cast; ring, norm_exp_ofReal,
        Complex.norm_natCast, add_sub_cancel_right]
      ring
  have hsum : Summable fun k => ∫ t in Ioi (0 : ℝ), ‖F k t‖ := by
    simp_rw [hnorm]
    have h := Real.summable_one_div_nat_rpow.mpr hs
    refine (h.mul_right (Real.Gamma (s.re + 1))).congr fun k => ?_
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [Real.zero_rpow (by linarith : s.re ≠ 0)]
    · have hk' : (0 : ℝ) < k := by exact_mod_cast hk
      rw [Real.div_rpow zero_le_one hk'.le, Real.one_rpow, Real.rpow_add hk', Real.rpow_one]
      field_simp
  have key := integral_tsum_of_summable_integral_norm hFint hsum
  simp_rw [hFval] at key
  rw [tsum_mul_left, ← zeta_eq_tsum_one_div_nat_cpow hs] at key
  rw [key]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht' : (0 : ℝ) < t := ht
  have hq : ‖cexp (-(t : ℂ))‖ < 1 := by
    rw [show -(t : ℂ) = ((-t : ℝ) : ℂ) by push_cast; ring, norm_exp_ofReal]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hgeom := (hasSum_coe_mul_geometric_of_norm_lt_one hq).mul_left ((t : ℂ) ^ s)
  have hE : cexp (t : ℂ) - 1 ≠ 0 := by
    rw [sub_ne_zero, ← ofReal_exp]
    exact_mod_cast (Real.one_lt_exp_iff.mpr ht').ne'
  have hE2 : (1 : ℂ) - cexp (-(t : ℂ)) ≠ 0 := by
    rw [sub_ne_zero, ← ofReal_neg, ← ofReal_exp]
    exact_mod_cast (Real.exp_lt_one_iff.mpr (by linarith)).ne'
  have : cexp t * (t : ℂ) ^ s / (cexp t - 1) ^ 2 =
      (t : ℂ) ^ s * (cexp (-(t : ℂ)) / (1 - cexp (-(t : ℂ))) ^ 2) := by
    rw [Complex.exp_neg] at hE2 ⊢
    have h0 : cexp (t : ℂ) ≠ 0 := Complex.exp_ne_zero _
    field_simp
  rw [this, ← hgeom.tsum_eq]
  congr 1
  funext k
  simp only [hF]
  rw [← Complex.exp_nat_mul]
  ring_nf

/-- DLMF 25.5.1: `ζ(s) = Γ(s)⁻¹ ∫₀^∞ x^{s-1}/(eˣ - 1) dx` for `Re s > 1`. -/
@[dlmf 25.5.E1]
theorem riemannZeta_eq_integral_exp_sub_one {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 1) / (cexp x - 1)) (Ioi 0) ∧
      riemannZeta s = 1 / Gamma s * ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) / (cexp x - 1) := by
  refine ⟨q25a_integrableOn_exp_sub_one hs, ?_⟩
  have hval := DLMF.Gamma.integral_cpow_mul_exp_div_one_sub_exp hs (x := 1) one_pos
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => q25a_exp_div_one_sub_exp ht)] at hval
  rw [hval, show (∑' k : ℕ, 1 / ((k : ℂ) + ((1 : ℝ) : ℂ)) ^ s) = riemannZeta s by
      rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]; push_cast; rfl]
  have hG : Gamma s ≠ 0 := Gamma_ne_zero_of_re_pos (by linarith)
  field_simp

/-- `eᵗ - 1 ≠ 0` for `t > 0`. -/
lemma q25a_exp_sub_one_ne {t : ℝ} (ht : 0 < t) : cexp (t : ℂ) - 1 ≠ 0 := by
  rw [sub_ne_zero, ← ofReal_exp]
  exact_mod_cast (Real.one_lt_exp_iff.mpr ht).ne'
/-- Integrability transfers along equal norms on `(0, ∞)` for functions continuous there. -/
lemma q25a_integrableOn_of_norm_eq {f g : ℝ → ℂ} (hg : IntegrableOn g (Ioi 0))
    (hf : ContinuousOn f (Ioi 0)) (h : ∀ t : ℝ, 0 < t → ‖f t‖ = ‖g t‖) :
    IntegrableOn f (Ioi 0) := by
  refine hg.norm.mono' (hf.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact (h t ht).le
/-- Integrability and value under the scaling `x ↦ 2x` on `(0, ∞)`. -/
lemma q25a_scale_two {f : ℝ → ℂ} (hf : IntegrableOn f (Ioi 0)) :
    IntegrableOn (fun x => f (2 * x)) (Ioi 0) ∧
      ∫ x in Ioi (0 : ℝ), f (2 * x) = 1 / 2 * ∫ x in Ioi (0 : ℝ), f x := by
  refine ⟨(integrableOn_Ioi_comp_mul_left_iff f 0 two_pos).mpr (by simpa using hf), ?_⟩
  rw [integral_comp_mul_left_Ioi f 0 two_pos, mul_zero, Complex.real_smul]
  push_cast; ring
/-- The continuity of `t ↦ eᵗ tˢ / (eᵗ - 1)²` on `(0, ∞)`. -/
lemma q25a_continuousOn_exp_sq (s : ℂ) :
    ContinuousOn (fun t : ℝ => cexp t * (t : ℂ) ^ s / (cexp t - 1) ^ 2) (Ioi 0) := by
  intro x hx
  have hx0 : (0 : ℝ) < x := hx
  refine ContinuousAt.continuousWithinAt ?_
  refine ContinuousAt.div ?_ ?_ (pow_ne_zero _ (q25a_exp_sub_one_ne hx0))
  · exact (Complex.continuous_exp.comp continuous_ofReal).continuousAt.mul
      (continuousAt_ofReal_cpow_const _ _ (Or.inr hx0.ne'))
  · exact ((Complex.continuous_exp.comp continuous_ofReal).continuousAt.sub
      continuousAt_const).pow 2
/-- The integrand of 25.5.2 is integrable for `Re s > 1`. -/
lemma q25a_integrableOn_exp_sub_one_sq {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => cexp x * (x : ℂ) ^ s / (cexp x - 1) ^ 2) (Ioi 0) := by
  set σ : ℂ := (s.re : ℂ)
  have hσ : 1 < σ.re := by simpa [σ] using hs
  have hne : (∫ t in Ioi (0 : ℝ), cexp t * (t : ℂ) ^ σ / (cexp t - 1) ^ 2) ≠ 0 := by
    rw [q25a_integral_exp_sub_one_sq hσ]
    exact mul_ne_zero (Gamma_ne_zero_of_re_pos (by simp; linarith))
      (riemannZeta_ne_zero_of_one_lt_re hσ)
  refine q25a_integrableOn_of_norm_eq (Integrable.of_integral_ne_zero hne)
    (q25a_continuousOn_exp_sq s) fun t ht => ?_
  rw [norm_div, norm_div, norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos ht,
    norm_cpow_eq_rpow_re_of_pos ht]
  simp [σ]

/-- DLMF 25.5.2: `ζ(s) = Γ(s+1)⁻¹ ∫₀^∞ eˣ xˢ/(eˣ - 1)² dx` for `Re s > 1`. -/
@[dlmf 25.5.E2]
theorem riemannZeta_eq_integral_exp_sub_one_sq {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => cexp x * (x : ℂ) ^ s / (cexp x - 1) ^ 2) (Ioi 0) ∧
      riemannZeta s =
        1 / Gamma (s + 1) * ∫ x in Ioi (0 : ℝ), cexp x * (x : ℂ) ^ s / (cexp x - 1) ^ 2 := by
  refine ⟨q25a_integrableOn_exp_sub_one_sq hs, ?_⟩
  rw [q25a_integral_exp_sub_one_sq hs]
  have hG : Gamma (s + 1) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  field_simp

/-- `x^a ≤ x^{a₁} + x^{a₂}` for `x > 0`, `a₁ ≤ a ≤ a₂`. -/
lemma q25a_rpow_le_add {x a a₁ a₂ : ℝ} (hx : 0 < x) (h1 : a₁ ≤ a) (h2 : a ≤ a₂) :
    x ^ a ≤ x ^ a₁ + x ^ a₂ := by
  rcases le_or_gt x 1 with hx1 | hx1
  · have := Real.rpow_le_rpow_of_exponent_ge hx hx1 h1
    linarith [Real.rpow_nonneg hx.le a₂]
  · have := Real.rpow_le_rpow_of_exponent_le hx1.le h2
    linarith [Real.rpow_nonneg hx.le a₁]
/-- `s ↦ ∫₀^∞ x^{s-1} φ(x) dx` is holomorphic on `Re s > 0` when `φ` is continuous on
`(0, ∞)` and `|φ(x)| ≤ e^{-x}`. -/
lemma q25a_differentiableOn_mellin {φ : ℝ → ℂ} (hφc : ContinuousOn φ (Ioi 0))
    (hφ : ∀ x : ℝ, 0 < x → ‖φ x‖ ≤ Real.exp (-x)) :
    DifferentiableOn ℂ (fun s : ℂ => ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) * φ x)
      {s | 0 < s.re} := by
  have hmeasφ : AEStronglyMeasurable φ (volume.restrict (Ioi 0)) :=
    hφc.aestronglyMeasurable measurableSet_Ioi
  refine Complex.differentiableOn_integral_Ioi_of_locally_dominated
    (isOpen_lt continuous_const continuous_re) 0 ?_ ?_ ?_
  · intro s _
    refine AEStronglyMeasurable.mul ?_ hmeasφ
    refine ContinuousOn.aestronglyMeasurable (fun x hx => ?_) measurableSet_Ioi
    exact (continuousAt_ofReal_cpow_const _ _ (Or.inr (ne_of_gt hx))).continuousWithinAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt ht)
    intro s _
    refine DifferentiableAt.differentiableWithinAt (DifferentiableAt.mul_const ?_ _)
    exact (differentiableAt_id.sub_const 1).const_cpow (Or.inl ht0)
  · intro s0 hs0
    have hs0' : 0 < s0.re := hs0
    refine ⟨{s | s0.re / 2 < s.re ∧ s.re < s0.re + 1}, ?_,
      fun x => Real.exp (-x) * x ^ (s0.re / 2 - 1) + Real.exp (-x) * x ^ (s0.re + 1 - 1),
      (Real.GammaIntegral_convergent (s := s0.re / 2) (by linarith)).add
        (Real.GammaIntegral_convergent (s := s0.re + 1) (by linarith)), ?_⟩
    · exact ((isOpen_lt continuous_const continuous_re).inter
        (isOpen_lt continuous_re continuous_const)).mem_nhds
        (show s0.re / 2 < s0.re ∧ s0.re < s0.re + 1 from ⟨by linarith, by linarith⟩)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht s hs
      have ht0 : (0 : ℝ) < t := ht
      obtain ⟨hs1, hs2⟩ := hs
      rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht0, sub_re, one_re, ← mul_add]
      have h1 := q25a_rpow_le_add ht0 (a := s.re - 1) (a₁ := s0.re / 2 - 1)
        (a₂ := s0.re + 1 - 1) (by linarith) (by linarith)
      have := mul_le_mul h1 (hφ t ht0) (norm_nonneg _) (by positivity)
      exact this.trans_eq (by ring)
/-- The domain `Re s > a` minus the ray `[1, ∞)`, star-shaped about a real point `c`,
`a < c < 1`. -/
lemma q25a_isPreconnected_ray {a c : ℝ} (hac : a < c) (hc1 : c < 1) :
    IsPreconnected ({s : ℂ | a < s.re} \ {s : ℂ | s.im = 0 ∧ 1 ≤ s.re}) := by
  refine (StarConvex.isPathConnected (a := (c : ℂ)) ?_ ?_).isConnected.isPreconnected
  · intro z hz u v hu hv huv
    have hz1 : a < z.re := hz.1
    have hz2 : ¬ (z.im = 0 ∧ 1 ≤ z.re) := hz.2
    rw [Complex.real_smul, Complex.real_smul]
    refine ⟨?_, ?_⟩
    · show a < ((u : ℂ) * c + (v : ℂ) * z).re
      simp only [add_re, re_ofReal_mul, ofReal_re]
      rcases eq_or_lt_of_le hu with rfl | hu'
      · simp at huv; subst huv; linarith
      · nlinarith [mul_pos hu' (sub_pos.mpr hac), mul_nonneg hv (sub_nonneg.mpr hz1.le)]
    · rintro ⟨him, hre⟩
      simp only [add_im, im_ofReal_mul, ofReal_im, mul_zero, zero_add] at him
      simp only [add_re, re_ofReal_mul, ofReal_re] at hre
      rcases eq_or_lt_of_le hv with rfl | hv'
      · simp at huv; subst huv; linarith
      · have hzi : z.im = 0 := by
          rcases mul_eq_zero.mp him with h | h
          · linarith
          · exact h
        have : z.re < 1 := by
          by_contra h; exact hz2 ⟨hzi, not_lt.mp h⟩
        nlinarith
  · refine ⟨?_, ?_⟩
    · show a < (c : ℂ).re
      simpa using hac
    · rintro ⟨-, h⟩; simp at h; linarith
/-- `|1/(eˣ+1)| ≤ e^{-x}`. -/
lemma q25a_norm_inv_exp_add_one_le {x : ℝ} :
    ‖1 / (cexp x + 1)‖ ≤ Real.exp (-x) := by
  rw [show cexp (x : ℂ) + 1 = ((Real.exp x + 1 : ℝ) : ℂ) by push_cast; rfl, norm_div, norm_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity), Real.exp_neg]
  exact (one_div_le_one_div_of_le (Real.exp_pos x) (by linarith)).trans_eq (one_div _)
/-- `|eˣ/(eˣ+1)²| ≤ e^{-x}`. -/
lemma q25a_norm_exp_div_exp_add_one_sq_le {x : ℝ} :
    ‖cexp x / (cexp x + 1) ^ 2‖ ≤ Real.exp (-x) := by
  rw [show cexp (x : ℂ) + 1 = ((Real.exp x + 1 : ℝ) : ℂ) by push_cast; rfl, ← ofReal_exp,
    ← ofReal_pow, ← ofReal_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity), Real.exp_neg, div_le_iff₀ (by positivity)]
  have h := Real.exp_pos x
  field_simp
  nlinarith
/-- 25.5.3 for `Re s > 1`: the integrand of 25.5.3 splits as `h(x) - 2^{2-s} h(2x)`. -/
lemma q25a_exp_add_one_split {s : ℂ} {x : ℝ} (hx : 0 < x) :
    (x : ℂ) ^ (s - 1) / (cexp x + 1) = (x : ℂ) ^ (s - 1) / (cexp x - 1) -
      2 * (2 : ℂ) ^ (1 - s) * (((2 * x : ℝ) : ℂ) ^ (s - 1) / (cexp ((2 * x : ℝ) : ℂ) - 1)) := by
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  rw [ofReal_mul, mul_cpow_ofReal_nonneg (by norm_num) hx.le, ofReal_ofNat]
  have hE := q25a_exp_sub_one_ne hx
  have hE1 : cexp (x : ℂ) + 1 ≠ 0 := by
    rw [← ofReal_exp]; exact_mod_cast (by positivity : Real.exp x + 1 ≠ 0)
  have hc : (2 : ℂ) ^ (1 - s) * (2 : ℂ) ^ (s - 1) = 1 := by
    rw [← cpow_add _ _ h2]; simp
  rw [show cexp (2 * (x : ℂ)) - 1 = (cexp x - 1) * (cexp x + 1) by
    rw [show 2 * (x : ℂ) = x + x by ring, Complex.exp_add]; ring]
  rw [show 2 * (2 : ℂ) ^ (1 - s) * ((2 : ℂ) ^ (s - 1) * (x : ℂ) ^ (s - 1) /
      ((cexp x - 1) * (cexp x + 1))) = 2 * ((2 : ℂ) ^ (1 - s) * (2 : ℂ) ^ (s - 1)) *
      ((x : ℂ) ^ (s - 1) / ((cexp x - 1) * (cexp x + 1))) by ring, hc]
  field_simp
  ring

/-- DLMF 25.5.3 (multiplied form): `(1 - 2^{1-s}) Γ(s) ζ(s) = ∫₀^∞ x^{s-1}/(eˣ + 1) dx` for
`Re s > 0`, `s ≠ 1`. -/
@[dlmf 25.5.E3]
theorem riemannZeta_eq_integral_exp_add_one {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 1) / (cexp x + 1)) (Ioi 0) ∧
      (1 - 2 ^ (1 - s)) * Gamma s * riemannZeta s =
        ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) / (cexp x + 1) := by
  have hφc : ContinuousOn (fun x : ℝ => 1 / (cexp x + 1)) (Ioi 0) := by
    refine Continuous.continuousOn ?_
    refine continuous_const.div (by fun_prop) fun x => ?_
    rw [← ofReal_exp]; exact_mod_cast (by positivity : Real.exp x + 1 ≠ 0)
  have hint : ∀ z : ℂ, 0 < z.re →
      IntegrableOn (fun x : ℝ => (x : ℂ) ^ (z - 1) / (cexp x + 1)) (Ioi 0) := by
    intro z hz
    refine (show Integrable _ (volume.restrict (Ioi (0 : ℝ))) from
      DLMF.Gamma.integrableOn_cpow_mul_exp_neg_mul hz one_pos).norm.mono' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable (fun x hx => ?_) measurableSet_Ioi
      have hx0 : (0 : ℝ) < x := hx
      refine ContinuousAt.continuousWithinAt (ContinuousAt.div ?_ ?_ ?_)
      · exact continuousAt_ofReal_cpow_const _ _ (Or.inr hx0.ne')
      · fun_prop
      · rw [← ofReal_exp]; exact_mod_cast (by positivity : Real.exp x + 1 ≠ 0)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : (0 : ℝ) < x := hx
      rw [div_eq_mul_one_div, norm_mul, norm_mul, ofReal_one, one_mul,
        show -((x : ℂ)) = ((-x : ℝ) : ℂ) by push_cast; ring, norm_exp_ofReal]
      exact mul_le_mul_of_nonneg_left q25a_norm_inv_exp_add_one_le (norm_nonneg _)
  refine ⟨hint s hs, ?_⟩
  -- the case `Re s > 1`
  have hgt : ∀ z : ℂ, 1 < z.re → (1 - 2 ^ (1 - z)) * Gamma z * riemannZeta z =
      ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (z - 1) / (cexp x + 1) := by
    intro z hz
    have hI := q25a_integrableOn_exp_sub_one hz
    obtain ⟨hI2, hV2⟩ := q25a_scale_two hI
    have hval := (riemannZeta_eq_integral_exp_sub_one hz).2
    have hG : Gamma z ≠ 0 := Gamma_ne_zero_of_re_pos (by linarith)
    rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx => q25a_exp_add_one_split hx),
      integral_sub hI (hI2.const_mul _), integral_const_mul, hV2]
    have hJ : ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (z - 1) / (cexp x - 1) = Gamma z * riemannZeta z := by
      rw [hval]; field_simp
    rw [hJ]
    ring
  set U : Set ℂ := {s : ℂ | 0 < s.re} \ {s : ℂ | s.im = 0 ∧ 1 ≤ s.re} with hU
  have hUo : IsOpen U := (isOpen_lt continuous_const continuous_re).sdiff
    ((isClosed_eq continuous_im continuous_const).inter
      (isClosed_le continuous_const continuous_re))
  have hF : DifferentiableOn ℂ (fun z => (1 - 2 ^ (1 - z)) * Gamma z * riemannZeta z) U := by
    intro z hz
    have hz0 : 0 < z.re := hz.1
    have hz1 : z ≠ 1 := fun h => hz.2 ⟨by rw [h]; simp, by rw [h]; simp⟩
    refine DifferentiableAt.differentiableWithinAt (DifferentiableAt.mul (DifferentiableAt.mul
      ?_ ?_) (differentiableAt_riemannZeta hz1))
    · exact (differentiableAt_const _).sub
        (((differentiableAt_const _).sub differentiableAt_id).const_cpow (Or.inl two_ne_zero))
    · refine differentiableAt_Gamma z fun m hm => ?_
      have := congrArg re hm; simp at this; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  have hG : DifferentiableOn ℂ (fun z => ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (z - 1) / (cexp x + 1)) U
      := by
    have := q25a_differentiableOn_mellin hφc (fun x _ => q25a_norm_inv_exp_add_one_le)
    refine (this.mono (fun z (hz : z ∈ U) => hz.1)).congr fun z _ => ?_
    show ∫ x in Ioi (0 : ℝ), _ = ∫ x in Ioi (0 : ℝ), _
    congr 1; funext x; rw [div_eq_mul_one_div]
  have hz0 : (2 + I : ℂ) ∈ U := ⟨by show (0 : ℝ) < (2 + I : ℂ).re; simp,
    by rintro ⟨h, -⟩; simp at h⟩
  have hev : (fun z => (1 - 2 ^ (1 - z)) * Gamma z * riemannZeta z) =ᶠ[𝓝 (2 + I : ℂ)]
      (fun z => ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (z - 1) / (cexp x + 1)) := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (show (1 : ℝ) < (2 + I : ℂ).re by simp)] with z hz
    exact hgt z hz
  have heq := (hF.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq
    (hG.analyticOnNhd hUo) (q25a_isPreconnected_ray (a := 0) (c := 1 / 2) (by norm_num)
      (by norm_num)) hz0 hev
  by_cases hsU : s ∈ U
  · exact heq hsU
  · have hray : s.im = 0 ∧ 1 ≤ s.re := by
      by_contra h; exact hsU ⟨hs, h⟩
    have hre : 1 < s.re := by
      rcases eq_or_lt_of_le hray.2 with h | h
      · exfalso; apply hs1; apply Complex.ext <;> simp [hray.1, ← h]
      · exact h
    exact hgt s hre

/-- The integrand of 25.5.4 splits as `h(x) - 4·2^{-s} h(2x)` with `h(u) = eᵘ uˢ/(eᵘ-1)²`. -/
lemma q25a_exp_add_one_sq_split {s : ℂ} {x : ℝ} (hx : 0 < x) :
    cexp x * (x : ℂ) ^ s / (cexp x + 1) ^ 2 = cexp x * (x : ℂ) ^ s / (cexp x - 1) ^ 2 -
      4 * (2 : ℂ) ^ (-s) * (cexp ((2 * x : ℝ) : ℂ) * ((2 * x : ℝ) : ℂ) ^ s /
        (cexp ((2 * x : ℝ) : ℂ) - 1) ^ 2) := by
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  rw [ofReal_mul, mul_cpow_ofReal_nonneg (by norm_num) hx.le, ofReal_ofNat]
  have hE := q25a_exp_sub_one_ne hx
  have hE1 : cexp (x : ℂ) + 1 ≠ 0 := by
    rw [← ofReal_exp]; exact_mod_cast (by positivity : Real.exp x + 1 ≠ 0)
  have hc : (2 : ℂ) ^ (-s) * (2 : ℂ) ^ s = 1 := by
    rw [← cpow_add _ _ h2]; simp
  have he2 : cexp (2 * (x : ℂ)) = cexp x * cexp x := by
    rw [show 2 * (x : ℂ) = x + x by ring, Complex.exp_add]
  rw [he2, show 4 * (2 : ℂ) ^ (-s) * (cexp x * cexp x * ((2 : ℂ) ^ s * (x : ℂ) ^ s) /
      (cexp x * cexp x - 1) ^ 2) = 4 * ((2 : ℂ) ^ (-s) * (2 : ℂ) ^ s) *
      (cexp x * cexp x * (x : ℂ) ^ s / (cexp x * cexp x - 1) ^ 2) by ring, hc,
    show cexp (x : ℂ) * cexp x - 1 = (cexp x - 1) * (cexp x + 1) by ring]
  field_simp
  ring

/-- DLMF 25.5.4 (multiplied form): `(1 - 2^{1-s}) Γ(s+1) ζ(s) = ∫₀^∞ eˣ xˢ/(eˣ + 1)² dx` for
`Re s > 0`, `s ≠ 1`. -/
@[dlmf 25.5.E4]
theorem riemannZeta_eq_integral_exp_add_one_sq {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    IntegrableOn (fun x : ℝ => cexp x * (x : ℂ) ^ s / (cexp x + 1) ^ 2) (Ioi 0) ∧
      (1 - 2 ^ (1 - s)) * Gamma (s + 1) * riemannZeta s =
        ∫ x in Ioi (0 : ℝ), cexp x * (x : ℂ) ^ s / (cexp x + 1) ^ 2 := by
  set φ : ℝ → ℂ := fun x => cexp x / (cexp x + 1) ^ 2 with hφdef
  have hφc : ContinuousOn φ (Ioi 0) := by
    refine Continuous.continuousOn ?_
    refine (by fun_prop : Continuous fun x : ℝ => cexp x).div (by fun_prop) fun x => ?_
    refine pow_ne_zero _ ?_
    rw [← ofReal_exp]; exact_mod_cast (by positivity : Real.exp x + 1 ≠ 0)
  have hform : ∀ z : ℂ, ∀ x : ℝ, 0 < x →
      cexp x * (x : ℂ) ^ z / (cexp x + 1) ^ 2 = (x : ℂ) ^ (z + 1 - 1) * φ x := by
    intro z x _; simp only [hφdef, add_sub_cancel_right]; ring
  have hint : ∀ z : ℂ, 0 < z.re →
      IntegrableOn (fun x : ℝ => cexp x * (x : ℂ) ^ z / (cexp x + 1) ^ 2) (Ioi 0) := by
    intro z hz
    have hz1 : 0 < (z + 1).re := by simp; linarith
    refine (show Integrable _ (volume.restrict (Ioi (0 : ℝ))) from
      DLMF.Gamma.integrableOn_cpow_mul_exp_neg_mul hz1 one_pos).norm.mono' ?_ ?_
    · refine (ContinuousOn.congr (f := fun x : ℝ => (x : ℂ) ^ (z + 1 - 1) * φ x) ?_
        (fun x hx => hform z x hx)).aestronglyMeasurable measurableSet_Ioi
      refine ContinuousOn.mul (fun x hx => ?_) hφc
      exact (continuousAt_ofReal_cpow_const _ _ (Or.inr (ne_of_gt hx))).continuousWithinAt
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : (0 : ℝ) < x := hx
      rw [hform z x hx0, norm_mul, norm_mul, ofReal_one, one_mul,
        show -((x : ℂ)) = ((-x : ℝ) : ℂ) by push_cast; ring, norm_exp_ofReal]
      exact mul_le_mul_of_nonneg_left q25a_norm_exp_div_exp_add_one_sq_le (norm_nonneg _)
  refine ⟨hint s hs, ?_⟩
  have hgt : ∀ z : ℂ, 1 < z.re → (1 - 2 ^ (1 - z)) * Gamma (z + 1) * riemannZeta z =
      ∫ x in Ioi (0 : ℝ), cexp x * (x : ℂ) ^ z / (cexp x + 1) ^ 2 := by
    intro z hz
    have hI := q25a_integrableOn_exp_sub_one_sq hz
    obtain ⟨hI2, hV2⟩ := q25a_scale_two hI
    rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx => q25a_exp_add_one_sq_split hx),
      integral_sub hI (hI2.const_mul _), integral_const_mul, hV2,
      q25a_integral_exp_sub_one_sq hz]
    have h1s : (2 : ℂ) ^ (1 - z) = 2 * (2 : ℂ) ^ (-z) := by
      rw [sub_eq_add_neg, cpow_add _ _ two_ne_zero, cpow_one]
    rw [h1s]
    ring
  set U : Set ℂ := {s : ℂ | 0 < s.re} \ {s : ℂ | s.im = 0 ∧ 1 ≤ s.re} with hU
  have hUo : IsOpen U := (isOpen_lt continuous_const continuous_re).sdiff
    ((isClosed_eq continuous_im continuous_const).inter
      (isClosed_le continuous_const continuous_re))
  have hF : DifferentiableOn ℂ (fun z => (1 - 2 ^ (1 - z)) * Gamma (z + 1) * riemannZeta z) U := by
    intro z hz
    have hz0 : 0 < z.re := hz.1
    have hz1 : z ≠ 1 := fun h => hz.2 ⟨by rw [h]; simp, by rw [h]; simp⟩
    refine DifferentiableAt.differentiableWithinAt (DifferentiableAt.mul (DifferentiableAt.mul
      ?_ ?_) (differentiableAt_riemannZeta hz1))
    · exact (differentiableAt_const _).sub
        (((differentiableAt_const _).sub differentiableAt_id).const_cpow (Or.inl two_ne_zero))
    · refine (differentiableAt_Gamma (z + 1) fun m hm => ?_).comp z
        (differentiableAt_id.add_const 1)
      have := congrArg re hm; simp at this; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  have hG : DifferentiableOn ℂ
      (fun z => ∫ x in Ioi (0 : ℝ), cexp x * (x : ℂ) ^ z / (cexp x + 1) ^ 2) U := by
    have hM := q25a_differentiableOn_mellin hφc (fun x _ => q25a_norm_exp_div_exp_add_one_sq_le)
    have hcomp := hM.comp (differentiableOn_id.add_const (1 : ℂ))
      (fun z (hz : z ∈ U) => show 0 < (z + 1).re by have : 0 < z.re := hz.1; simp; linarith)
    refine hcomp.congr fun z _ => ?_
    show ∫ x in Ioi (0 : ℝ), _ = ∫ x in Ioi (0 : ℝ), _
    exact setIntegral_congr_fun measurableSet_Ioi fun x hx => hform z x hx
  have hz0 : (2 + I : ℂ) ∈ U := ⟨by show (0 : ℝ) < (2 + I : ℂ).re; simp,
    by rintro ⟨h, -⟩; simp at h⟩
  have hev : (fun z => (1 - 2 ^ (1 - z)) * Gamma (z + 1) * riemannZeta z) =ᶠ[𝓝 (2 + I : ℂ)]
      (fun z => ∫ x in Ioi (0 : ℝ), cexp x * (x : ℂ) ^ z / (cexp x + 1) ^ 2) := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (show (1 : ℝ) < (2 + I : ℂ).re by simp)] with z hz
    exact hgt z hz
  have heq := (hF.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq
    (hG.analyticOnNhd hUo) (q25a_isPreconnected_ray (a := 0) (c := 1 / 2) (by norm_num)
      (by norm_num)) hz0 hev
  by_cases hsU : s ∈ U
  · exact heq hsU
  · have hray : s.im = 0 ∧ 1 ≤ s.re := by
      by_contra h; exact hsU ⟨hs, h⟩
    have hre : 1 < s.re := by
      rcases eq_or_lt_of_le hray.2 with h | h
      · exfalso; apply hs1; apply Complex.ext <;> simp [hray.1, ← h]
      · exact h
    exact hgt s hre

open DLMF.BernoulliEuler in
/-- `binom(s+2, 3) = (s+2)(s+1)s/6`. -/
lemma r25a_gbinom_three (s : ℂ) : z25a_gbinom (s + 2) 3 = (s + 2) * (s + 1) * s / 6 := by
  simp only [z25a_gbinom, descPochhammer_succ_right, descPochhammer_zero, Polynomial.eval_mul,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_natCast, Polynomial.eval_one,
    Polynomial.eval_ofNat, Nat.factorial, Nat.cast_ofNat]
  push_cast
  ring

open DLMF.BernoulliEuler in
/-- For `-1 < Re s`, `s ≠ 1`: `ζ(s) = ½ + 1/(s-1) + s/12 - s(s+1)/2 ∫₁^∞ B̃₂(x) x^{-s-2} dx`. -/
lemma r25a_zeta_eq_B2 {s : ℂ} (hs : -1 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s = 1 / 2 + 1 / (s - 1) + s / 12 - s * (s + 1) / 2 *
      ∫ x in Ioi (1 : ℝ), (periodicBernoulliB 2 x : ℂ) / (x : ℂ) ^ (s + 2) := by
  have h := q25a_zeta_eq_emRHS (n := 1) (N := 1) le_rfl le_rfl (by simp; linarith) hs1
  simp [q25a_emRHS, q25a_gbinom_one] at h
  have hr := q25a_recursion (p := 2) (by norm_num) (w := s + 2) (by simp; linarith)
    (a := 1) one_pos
  have hB3 : periodicBernoulliB 3 1 = 0 := by
    simp [periodicBernoulliB, bernoulliFun_eval_zero, bernoulli_eq_zero_of_odd (n := 3)
      ⟨1, rfl⟩ (by norm_num)]
  rw [hB3] at hr
  simp only [ofReal_zero, ofReal_one, one_cpow, div_one, neg_zero, zero_add] at hr
  rw [h, r25a_gbinom_three]
  push_cast at hr
  have e : (2 : ℂ) + 1 = 3 := by norm_num
  rw [e] at hr
  linear_combination (s * (s + 1) / 6) * hr

open scoped Interval in
open DLMF.BernoulliEuler in
/-- DLMF 25.5.5: `ζ(s) = -s ∫₀^∞ (x - ⌊x⌋ - ½) x^{-s-1} dx` for `-1 < Re s < 0`. The integral
converges only conditionally at `∞`; it is the limit of `∫₀^R` as `R → ∞`. -/
@[dlmf 25.5.E5]
theorem tendsto_integral_fract_sub_half {s : ℂ} (hs : -1 < s.re) (hs' : s.re < 0) :
    Tendsto (fun R : ℝ => -s * ∫ x in (0 : ℝ)..R,
        ((Int.fract x - 1 / 2 : ℝ) : ℂ) / (x : ℂ) ^ (s + 1)) atTop (𝓝 (riemannZeta s)) := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs'
  have hs1 : s ≠ 1 := by rintro rfl; norm_num at hs'
  set f : ℝ → ℂ := fun x => ((Int.fract x - 1 / 2 : ℝ) : ℂ) / (x : ℂ) ^ (s + 1) with hf
  set g : ℝ → ℂ := fun x => (x : ℂ) ^ (-s) - 1 / 2 * (x : ℂ) ^ (-(s + 1)) with hg
  -- on `(0, 1)`, `f = g`
  have hne1 : ∀ᵐ x : ℝ ∂volume, x ≠ 1 := by rw [ae_iff]; simp
  have hfg : ∀ᵐ x : ℝ ∂volume, x ∈ Ι (0 : ℝ) 1 → f x = g x := by
    filter_upwards [hne1] with x hx1 hx
    rw [Set.uIoc_of_le zero_le_one] at hx
    have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.1.ne'
    have hfr : Int.fract x = x := Int.fract_eq_self.mpr ⟨hx.1.le, lt_of_le_of_ne hx.2 hx1⟩
    simp only [hf, hg, hfr]
    rw [show -s = 1 - (s + 1) by ring, cpow_sub _ _ hx0, cpow_one, cpow_neg]
    push_cast
    ring
  have hg1 : IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (-s)) volume 0 1 :=
    intervalIntegral.intervalIntegrable_cpow' (by simp; linarith)
  have hg2 : IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (-(s + 1))) volume 0 1 :=
    intervalIntegral.intervalIntegrable_cpow' (by simp; linarith)
  have hgI : IntervalIntegrable g volume 0 1 := hg1.sub (hg2.const_mul _)
  have hfI : IntervalIntegrable f volume 0 1 := hgI.congr_ae (by
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [hfg] with x hx hxm using (hx hxm).symm)
  have hint01 : ∫ x in (0 : ℝ)..1, f x = 1 / (1 - s) + 1 / (2 * s) := by
    rw [intervalIntegral.integral_congr_ae hfg, intervalIntegral.integral_sub hg1
      (hg2.const_mul _), intervalIntegral.integral_const_mul,
      integral_cpow (Or.inl (by simp; linarith)), integral_cpow (Or.inl (by simp; linarith))]
    have h1 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
    rw [show -s + 1 = 1 - s by ring, show -(s + 1) + 1 = -s by ring]
    simp only [ofReal_one, one_cpow, ofReal_zero, zero_cpow h1, zero_cpow (neg_ne_zero.mpr hs0)]
    field_simp
    ring
  -- on `[1, R]`, integration by parts against `B̃₂`
  obtain ⟨C1, hC1⟩ := q25a_periodicBernoulliB_bound 1
  obtain ⟨C2, hC2⟩ := q25a_periodicBernoulliB_bound 2
  have hfB : ∀ x, f x = (periodicBernoulliB 1 x : ℂ) / (x : ℂ) ^ (s + 1) := fun x => by
    simp [hf, periodicBernoulliB, bernoulliFun_one]
  set I2 := ∫ x in Ioi (1 : ℝ), (periodicBernoulliB 2 x : ℂ) / (x : ℂ) ^ (s + 2) with hI2
  have hstep : ∀ R : ℝ, 1 ≤ R → ∫ x in (1 : ℝ)..R, f x =
      ((periodicBernoulliB 2 R : ℂ) / (R : ℂ) ^ (s + 1) - 1 / 6 +
        (s + 1) * ∫ x in (1 : ℝ)..R, (periodicBernoulliB 2 x : ℂ) / (x : ℂ) ^ (s + 2)) / 2 := by
    intro R hR
    have h := q25a_integral_ibp (p := 1) le_rfl (s + 1) one_pos hR
    have i1 := q25a_intervalIntegrable_bdd_div_cpow (q25a_measurable_periodicBernoulliB 1) hC1
      (s + 1) one_pos hR
    have i2 := q25a_intervalIntegrable_bdd_div_cpow (q25a_measurable_periodicBernoulliB 2) hC2
      (s + 1 + 1) one_pos hR
    rw [intervalIntegral.integral_sub (i1.const_mul _) (i2.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h
    have hB2 : periodicBernoulliB 2 1 = 1 / 6 := by
      simp [periodicBernoulliB, bernoulliFun_eval_zero, bernoulli_two]
    rw [hB2] at h
    simp only [ofReal_one, one_cpow, div_one] at h
    simp_rw [hfB]
    rw [show s + 1 + 1 = s + 2 by ring] at h
    push_cast at h ⊢
    linear_combination h / 2
  have hlimB : Tendsto (fun R : ℝ => (periodicBernoulliB 2 R : ℂ) / (R : ℂ) ^ (s + 1)) atTop
      (𝓝 0) := q25a_tendsto_pB_div_cpow 2 (by simp; linarith)
  have hlimI : Tendsto (fun R : ℝ => ∫ x in (1 : ℝ)..R,
      (periodicBernoulliB 2 x : ℂ) / (x : ℂ) ^ (s + 2)) atTop (𝓝 I2) :=
    intervalIntegral_tendsto_integral_Ioi 1 (q25a_integrableOn_bdd_div_cpow
      (q25a_measurable_periodicBernoulliB 2) hC2 (by simp; linarith) one_pos) tendsto_id
  have hlim : Tendsto (fun R : ℝ => -s * ((1 / (1 - s) + 1 / (2 * s)) +
      ((periodicBernoulliB 2 R : ℂ) / (R : ℂ) ^ (s + 1) - 1 / 6 +
        (s + 1) * ∫ x in (1 : ℝ)..R, (periodicBernoulliB 2 x : ℂ) / (x : ℂ) ^ (s + 2)) / 2))
      atTop (𝓝 (-s * ((1 / (1 - s) + 1 / (2 * s)) + (0 - 1 / 6 + (s + 1) * I2) / 2))) :=
    ((((hlimB.sub_const _).add (hlimI.const_mul _)).div_const _).const_add _).const_mul _
  have hval : -s * ((1 / (1 - s) + 1 / (2 * s)) + (0 - 1 / 6 + (s + 1) * I2) / 2) =
      riemannZeta s := by
    rw [r25a_zeta_eq_B2 hs hs1]
    have h1 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
    have h2 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    field_simp
    ring
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with R hR
  have hfR : IntervalIntegrable f volume 1 R := by
    have := q25a_intervalIntegrable_bdd_div_cpow (q25a_measurable_periodicBernoulliB 1) hC1
      (s + 1) one_pos hR
    refine this.congr_ae (ae_of_all _ fun x => (hfB x).symm)
  rw [← intervalIntegral.integral_add_adjacent_intervals hfI hfR, hint01, hstep R hR]

/-- `|1/(eˣ-1) - 1/x + 1/2| ≤ x` for `x > 0`. -/
lemma r25a_abs_bose_sub_le {x : ℝ} (hx : 0 < x) :
    |1 / (Real.exp x - 1) - 1 / x + 1 / 2| ≤ x := by
  set E := Real.exp x - 1 with hE
  have hq := Real.quadratic_le_exp_of_nonneg hx.le
  have hE0 : 0 < E := by nlinarith
  have key : 1 / E - 1 / x + 1 / 2 = (2 * x - 2 * E + x * E) / (2 * x * E) := by
    field_simp
  rw [key, abs_div, abs_of_pos (by positivity : 0 < 2 * x * E), div_le_iff₀ (by positivity),
    abs_le]
  constructor
  · rcases le_or_gt x 1 with hx1 | hx1
    · have hb := Real.exp_bound' hx.le hx1 (n := 3) (by norm_num)
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_one,
        pow_zero, pow_one, Nat.succ_eq_add_one, Nat.cast_ofNat] at hb
      norm_num at hb
      have hE' : E ≤ x + x ^ 2 / 2 + 2 / 9 * x ^ 3 := by rw [hE]; nlinarith
      nlinarith [mul_pos hx hx, mul_pos (mul_pos hx hx) hx, mul_pos (mul_pos hx hx) hE0,
        mul_le_mul_of_nonneg_left hE' (by positivity : (0 : ℝ) ≤ x ^ 2)]
    · nlinarith [mul_pos hx hE0, mul_pos (mul_pos hx hx) hE0]
  · nlinarith [mul_pos hx hx, mul_pos (mul_pos hx hx) hx, mul_pos (mul_pos hx hx) hE0,
      mul_pos (mul_pos (mul_pos hx hx) hx) hx]

/-- DLMF 25.5.6: `ζ(s) = ½ + 1/(s-1) + Γ(s)⁻¹ ∫₀^∞ (1/(eˣ-1) - 1/x + ½) x^{s-1} e^{-x} dx` for
`Re s > -1`, `s ≠ 1` (at `s = 0` the factor `1/Γ(0)` is `0`). -/
@[dlmf 25.5.E6]
theorem riemannZeta_eq_half_add_integral {s : ℂ} (hs : -1 < s.re) (hs1 : s ≠ 1) :
    IntegrableOn (fun x : ℝ => (1 / (cexp x - 1) - 1 / x + 1 / 2) * (x : ℂ) ^ (s - 1) /
        cexp x) (Ioi 0) ∧
      riemannZeta s = 1 / 2 + 1 / (s - 1) + 1 / Gamma s * ∫ x in Ioi (0 : ℝ),
        (1 / (cexp x - 1) - 1 / x + 1 / 2) * (x : ℂ) ^ (s - 1) / cexp x := by
  set Jf : ℂ → ℝ → ℂ := fun z x => (1 / (cexp x - 1) - 1 / x + 1 / 2) * (x : ℂ) ^ (z - 1) /
    cexp x with hJf
  set ph : ℝ → ℂ := fun x => (1 / (cexp x - 1) - 1 / x + 1 / 2) / x / cexp x with hph
  have hreal : ∀ x : ℝ, 0 < x → (1 / (cexp x - 1) - 1 / x + 1 / 2 : ℂ) =
      ((1 / (Real.exp x - 1) - 1 / x + 1 / 2 : ℝ) : ℂ) := fun x _ => by
    push_cast; rw [← ofReal_exp]
  have hphb : ∀ x : ℝ, 0 < x → ‖ph x‖ ≤ Real.exp (-x) := by
    intro x hx
    simp only [hph]
    rw [hreal x hx, norm_div, norm_div, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hx, Complex.norm_exp_ofReal, Real.exp_neg]
    rw [div_div, div_le_iff₀ (by positivity)]
    have := r25a_abs_bose_sub_le hx
    calc _ ≤ x := this
      _ = (Real.exp x)⁻¹ * (x * Real.exp x) := by field_simp
  have hphc : ContinuousOn ph (Ioi 0) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    have h1 : cexp (x : ℂ) - 1 ≠ 0 := q25a_exp_sub_one_ne hx0
    have h2 : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
    refine ContinuousAt.continuousWithinAt ?_
    simp only [hph]
    refine ContinuousAt.div (ContinuousAt.div ?_ (by fun_prop) h2) (by fun_prop)
      (Complex.exp_ne_zero _)
    refine ContinuousAt.add (ContinuousAt.sub ?_ ?_) continuousAt_const
    · exact continuousAt_const.div (by fun_prop) h1
    · exact continuousAt_const.div (by fun_prop) h2
  have hIph : ∀ z : ℂ, ∀ x : ℝ, 0 < x → Jf z x = (x : ℂ) ^ (z + 1 - 1) * ph x := by
    intro z x hx
    have h2 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    simp only [hJf, hph]
    rw [show z + 1 - 1 = (z - 1) + 1 by ring, cpow_add _ _ h2, cpow_one]
    field_simp
  -- integrability for `Re z > -1`
  have hint : ∀ z : ℂ, -1 < z.re → IntegrableOn (Jf z) (Ioi 0) := by
    intro z hz
    have hz' : 0 < (z + 1).re := by simp; linarith
    refine (show Integrable _ (volume.restrict (Ioi (0 : ℝ))) from
      DLMF.Gamma.integrableOn_cpow_mul_exp_neg_mul hz' one_pos).norm.mono' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      refine ContinuousOn.congr (f := fun x : ℝ => (x : ℂ) ^ (z + 1 - 1) * ph x) ?_
        (fun x hx => hIph z x hx)
      refine ContinuousOn.mul (fun x hx => ?_) hphc
      exact (continuousAt_ofReal_cpow_const _ _ (Or.inr (ne_of_gt hx))).continuousWithinAt
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : (0 : ℝ) < x := hx
      rw [hIph z x hx0, norm_mul, norm_mul, ofReal_one, one_mul,
        show -((x : ℂ)) = ((-x : ℝ) : ℂ) by push_cast; ring, norm_exp_ofReal]
      exact mul_le_mul_of_nonneg_left (hphb x hx0) (norm_nonneg _)
  refine ⟨hint s hs, ?_⟩
  -- the case `Re s > 1`
  have hgt : ∀ z : ℂ, 1 < z.re → riemannZeta z = 1 / 2 + 1 / (z - 1) +
      1 / Gamma z * ∫ x in Ioi (0 : ℝ), Jf z x := by
    intro z hz
    have hz0 : 0 < z.re := by linarith
    have hz1 : 0 < (z - 1).re := by simp; linarith
    have hA := q25a_integrableOn_exp_sub_one hz
    have hB := Complex.GammaIntegral_convergent hz0
    have hC := Complex.GammaIntegral_convergent hz1
    have hsplit : ∀ x ∈ Ioi (0 : ℝ), Jf z x = (x : ℂ) ^ (z - 1) / (cexp x - 1) -
        (((-x).exp : ℝ) : ℂ) * (x : ℂ) ^ (z - 1) - (((-x).exp : ℝ) : ℂ) * (x : ℂ) ^ (z - 1 - 1) +
        1 / 2 * ((((-x).exp : ℝ) : ℂ) * (x : ℂ) ^ (z - 1)) := by
      intro x hx
      have hx0 : (0 : ℝ) < x := hx
      have h1 := q25a_exp_sub_one_ne hx0
      have h2 : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
      have h3 : cexp (x : ℂ) ≠ 0 := Complex.exp_ne_zero _
      simp only [hJf]
      rw [show z - 1 = (z - 1 - 1) + 1 by ring, cpow_add _ _ h2, cpow_one, ofReal_exp,
        ofReal_neg, Complex.exp_neg]
      field_simp
      ring_nf
    rw [setIntegral_congr_fun measurableSet_Ioi hsplit, integral_add ?i1 ?i2,
      integral_sub ?i3 ?i4, integral_sub ?i5 ?i6, integral_const_mul]
    case i1 => exact (hA.sub hB).sub hC
    case i2 => exact hB.const_mul _
    case i3 => exact hA.sub hB
    case i4 => exact hC
    case i5 => exact hA
    case i6 => exact hB
    have hA' : ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (z - 1) / (cexp x - 1) = Gamma z * riemannZeta z := by
      have h := (riemannZeta_eq_integral_exp_sub_one hz).2
      have hG : Gamma z ≠ 0 := Gamma_ne_zero_of_re_pos hz0
      rw [h]; field_simp
    have hB' : ∫ x in Ioi (0 : ℝ), (((-x).exp : ℝ) : ℂ) * (x : ℂ) ^ (z - 1) = Gamma z :=
      (Gamma_eq_integral hz0).symm
    have hC' : ∫ x in Ioi (0 : ℝ), (((-x).exp : ℝ) : ℂ) * (x : ℂ) ^ (z - 1 - 1) = Gamma (z - 1) :=
      (Gamma_eq_integral hz1).symm
    rw [hA', hB', hC']
    have hz1' : z - 1 ≠ 0 := by
      intro h; have := congrArg re h; simp at this; linarith
    have hGz : Gamma z = (z - 1) * Gamma (z - 1) := by
      rw [← Complex.Gamma_add_one _ hz1', sub_add_cancel]
    have hG : Gamma z ≠ 0 := Gamma_ne_zero_of_re_pos hz0
    have hG1 : Gamma (z - 1) ≠ 0 := Gamma_ne_zero_of_re_pos hz1
    rw [hGz]
    field_simp
    ring
  set U : Set ℂ := {s : ℂ | -1 < s.re} \ {s : ℂ | s.im = 0 ∧ 1 ≤ s.re} with hU
  have hUo : IsOpen U := (isOpen_lt continuous_const continuous_re).sdiff
    ((isClosed_eq continuous_im continuous_const).inter
      (isClosed_le continuous_const continuous_re))
  have hne1 : ∀ z ∈ U, z ≠ 1 := fun z hz h => hz.2 ⟨by rw [h]; simp, by rw [h]; simp⟩
  have hF : DifferentiableOn ℂ riemannZeta U := fun z hz =>
    (differentiableAt_riemannZeta (hne1 z hz)).differentiableWithinAt
  have hM := q25a_differentiableOn_mellin hphc hphb
  have hG : DifferentiableOn ℂ (fun z => 1 / 2 + 1 / (z - 1) + 1 / Gamma z *
      ∫ x in Ioi (0 : ℝ), Jf z x) U := by
    have hMI : DifferentiableOn ℂ (fun z => ∫ x in Ioi (0 : ℝ), Jf z x) U := by
      have h1 : DifferentiableOn ℂ (fun z : ℂ => ∫ x in Ioi (0 : ℝ),
          (x : ℂ) ^ (z + 1 - 1) * ph x) U :=
        hM.comp (differentiableOn_id.add_const 1) (fun z hz => by
          have h := hz.1
          simp only [Set.mem_ofPred_eq] at h
          show 0 < (z + 1).re
          simp; linarith)
      refine h1.congr fun z _ => setIntegral_congr_fun measurableSet_Ioi fun x hx => hIph z x hx
    refine DifferentiableOn.add (DifferentiableOn.add (differentiableOn_const _) ?_) ?_
    · exact DifferentiableOn.div (differentiableOn_const _) (differentiableOn_id.sub_const 1)
        fun z hz => sub_ne_zero.mpr (hne1 z hz)
    · refine DifferentiableOn.mul ?_ hMI
      simpa [one_div] using differentiable_one_div_Gamma.differentiableOn
  have hz0 : (2 + I : ℂ) ∈ U := ⟨by show (-1 : ℝ) < (2 + I : ℂ).re; simp; norm_num,
    by rintro ⟨h, -⟩; simp at h⟩
  have hev : riemannZeta =ᶠ[𝓝 (2 + I : ℂ)]
      (fun z => 1 / 2 + 1 / (z - 1) + 1 / Gamma z * ∫ x in Ioi (0 : ℝ), Jf z x) := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (show (1 : ℝ) < (2 + I : ℂ).re by simp)] with z hz
    exact hgt z hz
  have heq := (hF.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq
    (hG.analyticOnNhd hUo) (q25a_isPreconnected_ray (a := -1) (c := 1 / 2) (by norm_num)
      (by norm_num)) hz0 hev
  by_cases hsU : s ∈ U
  · exact heq hsU
  · have hray : s.im = 0 ∧ 1 ≤ s.re := by
      by_contra h; exact hsU ⟨hs, h⟩
    have hre : 1 < s.re := by
      rcases eq_or_lt_of_le hray.2 with h | h
      · exfalso; apply hs1; apply Complex.ext <;> simp [hray.1, ← h]
      · exact h
    exact hgt s hre

/-- DLMF 25.5.7: for `n ≥ 1`, `Re s > -(2n+1)`, `s ≠ 1`,
`ζ(s) = ½ + 1/(s-1) + ∑_{m=1}^{n} (B_{2m}/(2m)!) (s)_{2m-1}
  + Γ(s)⁻¹ ∫₀^∞ (1/(eˣ-1) - 1/x + ½ - ∑_{m=1}^{n} (B_{2m}/(2m)!) x^{2m-1}) x^{s-1} e^{-x} dx`,
with the Pochhammer symbol `(s)_k = ascPochhammer ℂ k` evaluated at `s`. -/
@[dlmf 25.5.E7]
theorem riemannZeta_eq_half_add_bernoulli_integral {s : ℂ} {n : ℕ} (hn : 1 ≤ n)
    (hs : -(2 * n + 1 : ℝ) < s.re) (hs1 : s ≠ 1) :
    IntegrableOn (fun x : ℝ => (1 / (cexp x - 1) - 1 / x + 1 / 2 -
        ∑ m ∈ Finset.Icc (1 : ℕ) n, (bernoulli (2 * m) : ℂ) / (2 * m).factorial *
          (x : ℂ) ^ (2 * m - 1)) * (x : ℂ) ^ (s - 1) / cexp x) (Ioi 0) ∧
      riemannZeta s = 1 / 2 + 1 / (s - 1) +
        ∑ m ∈ Finset.Icc (1 : ℕ) n, (bernoulli (2 * m) : ℂ) / (2 * m).factorial *
          (ascPochhammer ℂ (2 * m - 1)).eval s +
        1 / Gamma s * ∫ x in Ioi (0 : ℝ), (1 / (cexp x - 1) - 1 / x + 1 / 2 -
          ∑ m ∈ Finset.Icc (1 : ℕ) n, (bernoulli (2 * m) : ℂ) / (2 * m).factorial *
            (x : ℂ) ^ (2 * m - 1)) * (x : ℂ) ^ (s - 1) / cexp x := by
  sorry

/-- DLMF 25.5.8: `ζ(s) = (2(1 - 2^{-s}) Γ(s))⁻¹ ∫₀^∞ x^{s-1}/sinh x dx` for `Re s > 1` (where
`1 - 2^{-s} ≠ 0`). -/
@[dlmf 25.5.E8]
theorem riemannZeta_eq_integral_sinh {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 1) / sinh x) (Ioi 0) ∧
      riemannZeta s = 1 / (2 * (1 - 2 ^ (-s)) * Gamma s) *
        ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) / sinh x := by
  set h : ℝ → ℂ := fun x => (x : ℂ) ^ (s - 1) / (cexp x - 1) with hh
  have hI := q25a_integrableOn_exp_sub_one hs
  obtain ⟨hI2, hV2⟩ := q25a_scale_two hI
  have hval := (riemannZeta_eq_integral_exp_sub_one hs).2
  have hG : Gamma s ≠ 0 := Gamma_ne_zero_of_re_pos (by linarith)
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  have hpt : ∀ x : ℝ, 0 < x → (x : ℂ) ^ (s - 1) / sinh x =
      2 * h x - 2 * (2 : ℂ) ^ (1 - s) * h (2 * x) := by
    intro x hx
    simp only [hh]
    rw [ofReal_mul, mul_cpow_ofReal_nonneg (by norm_num) hx.le, ofReal_ofNat]
    have hE := q25a_exp_sub_one_ne hx
    have hE2 : cexp (2 * (x : ℂ)) - 1 ≠ 0 := by
      have := q25a_exp_sub_one_ne (by linarith : (0 : ℝ) < 2 * x); push_cast at this; exact this
    have hc : (2 : ℂ) ^ (1 - s) * (2 : ℂ) ^ (s - 1) = 1 := by
      rw [← cpow_add _ _ h2]; simp
    have hsh : sinh (x : ℂ) = (cexp x - 1) * (cexp x + 1) / (2 * cexp x) := by
      rw [Complex.sinh, Complex.exp_neg]
      field_simp
      ring
    have h0 : cexp (x : ℂ) ≠ 0 := Complex.exp_ne_zero _
    have hE1 : cexp (x : ℂ) + 1 ≠ 0 := by
      rw [← ofReal_exp]; exact_mod_cast (by positivity : Real.exp x + 1 ≠ 0)
    rw [hsh, show cexp (2 * (x : ℂ)) - 1 = (cexp x - 1) * (cexp x + 1) by
      rw [show 2 * (x : ℂ) = x + x by ring, Complex.exp_add]; ring]
    rw [show 2 * (2 : ℂ) ^ (1 - s) * ((2 : ℂ) ^ (s - 1) * (x : ℂ) ^ (s - 1) /
        ((cexp x - 1) * (cexp x + 1))) = 2 * ((2 : ℂ) ^ (1 - s) * (2 : ℂ) ^ (s - 1)) *
        ((x : ℂ) ^ (s - 1) / ((cexp x - 1) * (cexp x + 1))) by ring, hc]
    field_simp
    ring
  have hInt : IntegrableOn (fun x : ℝ => 2 * h x - 2 * (2 : ℂ) ^ (1 - s) * h (2 * x)) (Ioi 0) :=
    (hI.const_mul 2).sub (hI2.const_mul _)
  have hInt' : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 1) / sinh x) (Ioi 0) :=
    hInt.congr_fun (fun x hx => (hpt x hx).symm) measurableSet_Ioi
  refine ⟨hInt', ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_sub (hI.const_mul 2)
    (hI2.const_mul _), integral_const_mul, integral_const_mul, hV2]
  have hJ : ∫ x in Ioi (0 : ℝ), h x = Gamma s * riemannZeta s := by
    rw [hval]; field_simp; rfl
  rw [hJ]
  have h1s : (2 : ℂ) ^ (1 - s) = 2 * (2 : ℂ) ^ (-s) := by
    rw [sub_eq_add_neg, cpow_add _ _ h2, cpow_one]
  rw [h1s]
  have hne : (1 : ℂ) - 2 ^ (-s) ≠ 0 := by
    have h2s : ‖(2 : ℂ) ^ (-s)‖ < 1 := by
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, norm_cpow_eq_rpow_re_of_pos (by norm_num)]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by simp; linarith)
    intro h0; rw [sub_eq_zero] at h0; rw [← h0] at h2s; simp at h2s
  field_simp

/-- DLMF 25.5.9: `ζ(s) = 2^{s-1} Γ(s+1)⁻¹ ∫₀^∞ xˢ/sinh² x dx` for `Re s > 1`. -/
@[dlmf 25.5.E9]
theorem riemannZeta_eq_integral_sinh_sq {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ s / sinh x ^ 2) (Ioi 0) ∧
      riemannZeta s = 2 ^ (s - 1) / Gamma (s + 1) *
        ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ s / sinh x ^ 2 := by
  set h : ℝ → ℂ := fun x => cexp x * (x : ℂ) ^ s / (cexp x - 1) ^ 2 with hh
  have hI := q25a_integrableOn_exp_sub_one_sq hs
  obtain ⟨hI2, hV2⟩ := q25a_scale_two hI
  have hG : Gamma (s + 1) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  have hpt : ∀ x : ℝ, 0 < x → (x : ℂ) ^ s / sinh x ^ 2 = 4 * (2 : ℂ) ^ (-s) * h (2 * x) := by
    intro x hx
    simp only [hh]
    rw [ofReal_mul, mul_cpow_ofReal_nonneg (by norm_num) hx.le, ofReal_ofNat]
    have hc : (2 : ℂ) ^ (-s) * (2 : ℂ) ^ s = 1 := by
      rw [← cpow_add _ _ h2]; simp
    have hsh : sinh (x : ℂ) = (cexp x - 1) * (cexp x + 1) / (2 * cexp x) := by
      rw [Complex.sinh, Complex.exp_neg]
      field_simp
      ring
    have hE := q25a_exp_sub_one_ne hx
    have h0 : cexp (x : ℂ) ≠ 0 := Complex.exp_ne_zero _
    have hE1 : cexp (x : ℂ) + 1 ≠ 0 := by
      rw [← ofReal_exp]; exact_mod_cast (by positivity : Real.exp x + 1 ≠ 0)
    have he2 : cexp (2 * (x : ℂ)) = cexp x * cexp x := by
      rw [show 2 * (x : ℂ) = x + x by ring, Complex.exp_add]
    rw [hsh, he2]
    rw [show 4 * (2 : ℂ) ^ (-s) * (cexp x * cexp x * ((2 : ℂ) ^ s * (x : ℂ) ^ s) /
        (cexp x * cexp x - 1) ^ 2) = 4 * ((2 : ℂ) ^ (-s) * (2 : ℂ) ^ s) *
        (cexp x * cexp x * (x : ℂ) ^ s / (cexp x * cexp x - 1) ^ 2) by ring, hc]
    rw [show cexp (x : ℂ) * cexp x - 1 = (cexp x - 1) * (cexp x + 1) by ring]
    field_simp
    ring
  have hInt' : IntegrableOn (fun x : ℝ => (x : ℂ) ^ s / sinh x ^ 2) (Ioi 0) :=
    IntegrableOn.congr_fun (hI2.const_mul (4 * (2 : ℂ) ^ (-s)))
      (fun x hx => (hpt x hx).symm) measurableSet_Ioi
  refine ⟨hInt', ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul, hV2,
    q25a_integral_exp_sub_one_sq hs]
  have hc : (2 : ℂ) ^ (s - 1) * (2 : ℂ) ^ (-s) = 1 / 2 := by
    rw [← cpow_add _ _ h2, show s - 1 + -s = -1 by ring, cpow_neg_one, one_div]
  rw [show 2 ^ (s - 1) / Gamma (s + 1) * (4 * 2 ^ (-s) * (1 / 2 * (Gamma (s + 1) *
      riemannZeta s))) = 2 * ((2 : ℂ) ^ (s - 1) * (2 : ℂ) ^ (-s)) * (Gamma (s + 1) /
      Gamma (s + 1)) * riemannZeta s by ring, hc, div_self hG]
  ring

/-- DLMF 25.5.10 (multiplied form): for `s ≠ 1`,
`(1 - 2^{1-s}) ζ(s) = 2^{s-1} ∫₀^∞ cos(s arctan x) / ((1+x²)^{s/2} cosh(πx/2)) dx`. -/
@[dlmf 25.5.E10]
theorem riemannZeta_eq_integral_arctan_cosh {s : ℂ} (hs1 : s ≠ 1) :
    IntegrableOn (fun x : ℝ => cos (s * Real.arctan x) /
        (((1 + x ^ 2 : ℝ) : ℂ) ^ (s / 2) * cosh (π * x / 2))) (Ioi 0) ∧
      (1 - 2 ^ (1 - s)) * riemannZeta s = 2 ^ (s - 1) * ∫ x in Ioi (0 : ℝ),
        cos (s * Real.arctan x) / (((1 + x ^ 2 : ℝ) : ℂ) ^ (s / 2) * cosh (π * x / 2)) := by
  sorry

/-- DLMF 25.5.11: for `s ≠ 1`,
`ζ(s) = ½ + 1/(s-1) + 2 ∫₀^∞ sin(s arctan x) / ((1+x²)^{s/2} (e^{2πx} - 1)) dx`. -/
@[dlmf 25.5.E11]
theorem riemannZeta_eq_integral_arctan_exp_sub_one {s : ℂ} (hs1 : s ≠ 1) :
    IntegrableOn (fun x : ℝ => sin (s * Real.arctan x) /
        (((1 + x ^ 2 : ℝ) : ℂ) ^ (s / 2) * (cexp (2 * π * x) - 1))) (Ioi 0) ∧
      riemannZeta s = 1 / 2 + 1 / (s - 1) + 2 * ∫ x in Ioi (0 : ℝ),
        sin (s * Real.arctan x) / (((1 + x ^ 2 : ℝ) : ℂ) ^ (s / 2) * (cexp (2 * π * x) - 1)) := by
  sorry

/-- DLMF 25.5.12: for `s ≠ 1`,
`ζ(s) = 2^{s-1}/(s-1) - 2^s ∫₀^∞ sin(s arctan x) / ((1+x²)^{s/2} (e^{πx} + 1)) dx`. -/
@[dlmf 25.5.E12]
theorem riemannZeta_eq_integral_arctan_exp_add_one {s : ℂ} (hs1 : s ≠ 1) :
    IntegrableOn (fun x : ℝ => sin (s * Real.arctan x) /
        (((1 + x ^ 2 : ℝ) : ℂ) ^ (s / 2) * (cexp (π * x) + 1))) (Ioi 0) ∧
      riemannZeta s = 2 ^ (s - 1) / (s - 1) - 2 ^ s * ∫ x in Ioi (0 : ℝ),
        sin (s * Real.arctan x) / (((1 + x ^ 2 : ℝ) : ℂ) ^ (s / 2) * (cexp (π * x) + 1)) := by
  sorry

end DLMF.Zeta
end
