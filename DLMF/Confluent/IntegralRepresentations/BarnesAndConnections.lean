/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.IntegralRepresentations.EulerAndBessel

/-!
# Barnes integrals and continued Tricomi representations

Vertical Gamma integrals, Barnes representations and connection identities on the declared
complex branches.

Source references and common attribution are retained in
`DLMF.Confluent.IntegralRepresentations`.
This module uses results of the Tau Ceti contributors; see also `CREDITS.md`.
-/

@[expose] public section

open Complex Filter MeasureTheory intervalIntegral

open scoped Real Topology ENNReal

open DLMF.Hypergeometric

open DLMF.Bessel

noncomputable section

namespace DLMF.Confluent

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
/-- Identity under the stated parameter and domain assumptions: `kummerU a b x = (x : ℂ) ^ (-a) /
(2 * π * I) * ∫ t : ℝ, Gamma (a + σ + I * t) * Gamma (1 + a - b + σ + I * t) * Gamma (-(σ + I
* t)) / (Gamma a * Gamma (1 + a - b)) * (x : ℂ) ^ (-(σ + I * t)) * I`. -/
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

/-- Identity under the stated parameter and domain assumptions: `kummerU a b x = (x : ℂ) ^ (1 - b)
* exp x / (2 * π * I) * ∫ t : ℝ, Gamma (b - 1 + σ + I * t) * Gamma (σ + I * t) / Gamma (a + σ
+ I * t) * (x : ℂ) ^ (-(σ + I * t)) * I`. -/
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

/-- Identity under the stated parameter and domain assumptions: `whittakerM κ μ z = Gamma (1 + 2 *
μ) * z ^ (μ + 1 / 2) * (2 : ℂ) ^ (-(2 * μ)) / (Gamma (1 / 2 + μ - κ) * Gamma (1 / 2 + μ + κ))
* ∫ t : ℝ in (-1 : ℝ)..1, exp (z * t / 2) * (1 + (t : ℂ)) ^ (μ - 1 / 2 - κ) * (1 - (t : ℂ)) ^
(μ - 1 / 2 + κ)`. -/
@[dlmf 13.16.E1]
theorem whittakerM_euler {κ μ z : ℂ}
    (hμ : 0 < μ.re + 1 / 2 - |κ.re|) :
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

/-- Identity under the stated parameter and domain assumptions: `whittakerM κ μ z = Gamma (1 + 2 *
μ) * z ^ lam / (Gamma (1 + 2 * μ - 2 * lam) * Gamma (2 * lam)) * ∫ t : ℝ in (0 : ℝ)..1,
whittakerM (κ - lam) (μ - lam) (z * t) * exp (z * (t - 1) / 2) * (t : ℂ) ^ (μ - lam - 1 / 2) *
(1 - (t : ℂ)) ^ (2 * lam - 1)`. -/
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

/-- Identity under the stated parameter and domain assumptions: `whittakerM κ μ z / Gamma (1 + 2 *
μ) = z ^ (1 / 2 : ℂ) * exp (z / 2) / Gamma (1 / 2 + μ + κ) * ∫ t : ℝ in Set.Ioi 0, exp (-(t :
ℂ)) * (t : ℂ) ^ (κ - 1 / 2) * besselJ (2 * μ) (2 * (z * t) ^ (1 / 2 : ℂ))`. -/
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

/-- Identity under the stated parameter and domain assumptions: `whittakerM κ μ z / Gamma (1 + 2 *
μ) = z ^ (1 / 2 : ℂ) * exp (-z / 2) / Gamma (1 / 2 + μ - κ) * ∫ t : ℝ in Set.Ioi 0, exp (-(t :
ℂ)) * (t : ℂ) ^ (-κ - 1 / 2) * besselI (2 * μ) (2 * (z * t) ^ (1 / 2 : ℂ))`. -/
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

/-- Identity under the stated parameter and domain assumptions: `whittakerW κ μ z = z ^ (μ + 1 /
2) * (2 : ℂ) ^ (-(2 * μ)) / Gamma (1 / 2 + μ - κ) * ∫ t : ℝ in Set.Ioi 1, exp (-z * t / 2) *
((t : ℂ) - 1) ^ (μ - 1 / 2 - κ) * ((t : ℂ) + 1) ^ (μ - 1 / 2 + κ)`. -/
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

/-- Identity under the stated parameter and domain assumptions: `whittakerW κ μ x = exp (-(x : ℂ)
/ 2) / (2 * π * I) * ∫ t : ℝ, Gamma (1 / 2 + μ + σ + I * t) * Gamma (1 / 2 - μ + σ + I * t) *
Gamma (-κ - (σ + I * t)) / (Gamma (1 / 2 + μ - κ) * Gamma (1 / 2 - μ - κ)) * (x : ℂ) ^ (-(σ +
I * t)) * I`. -/
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

/-- Identity under the stated parameter and domain assumptions: `whittakerW κ μ x = exp ((x : ℂ) /
2) / (2 * π * I) * ∫ t : ℝ, Gamma (1 / 2 + μ + σ + I * t) * Gamma (1 / 2 - μ + σ + I * t) /
Gamma (1 - κ + σ + I * t) * (x : ℂ) ^ (-(σ + I * t)) * I`. -/
@[dlmf 13.16.E12]
theorem whittakerW_barnes_exp {κ μ : ℂ} {x σ : ℝ} (hx : 0 < x)
    (hμ : 0 < (1 / 2 + μ).re + σ) (hμ' : 0 < (1 / 2 - μ).re + σ) :
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

end
end
