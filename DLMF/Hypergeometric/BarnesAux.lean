/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Continuation
public import DLMF.Gamma.MellinBarnes

/-!
# Barnes's integral for `₂F₁` (DLMF 15.6.6): the Euler-integral case

Inserting the Mellin–Barnes integral for `(1+ut)^{-a}` (`DLMF.Gamma.Gamma_mul_one_add_cpow_neg`)
into Euler's integral (DLMF 15.6.1) and integrating termwise with Fubini and the Beta integral
gives Barnes's integral when `re (c - b) > 0`.
-/

@[expose] public section

open Complex Filter Set MeasureTheory
open scoped Topology Real

noncomputable section

namespace DLMF.Hypergeometric

open DLMF.Gamma

/-- The Mellin–Barnes integral in Barnes's orientation: for `σ < 0 < re a + σ` and `v > 0`,
`Γ(a)(1+v)^{-a} = 1/(2π) ∫ Γ(-(σ+iy)) Γ(a+σ+iy) v^{σ+iy} dy`. -/
theorem Gamma_mul_one_add_cpow_neg_barnes {a : ℂ} {σ : ℝ} (hσ : σ < 0) (haσ : 0 < a.re + σ)
    {v : ℝ} (hv : 0 < v) :
    Gamma a * ((1 + v : ℝ) : ℂ) ^ (-a) =
      1 / (2 * π) * ∫ y : ℝ, Gamma (-((σ : ℂ) + I * y)) * Gamma (a + σ + I * y) *
        (v : ℂ) ^ ((σ : ℂ) + I * y) := by
  rw [Gamma_mul_one_add_cpow_neg (σ := -σ) (by linarith) (by linarith) hv]
  congr 1
  rw [← integral_neg_eq_self]
  congr 1
  funext y
  rw [show (((-σ : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I) = -((σ : ℂ) + I * y) by push_cast; ring,
    show a - -((σ : ℂ) + I * y) = a + σ + I * y by ring, neg_neg]

theorem integrable_Gamma_neg_mul_Gamma {a : ℂ} {σ : ℝ} (hσ : σ < 0) (haσ : 0 < a.re + σ) :
    Integrable (fun y : ℝ => Gamma (-((σ : ℂ) + I * y)) * Gamma (a + σ + I * y)) := by
  have h := (integrable_Gamma_mul_Gamma_vertical (a := a) (σ := -σ) (by linarith)
    (by linarith)).comp_neg
  refine h.congr (Eventually.of_forall fun y => ?_)
  simp only [Function.comp_apply]
  rw [show (((-σ : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I) = -((σ : ℂ) + I * y) by push_cast; ring,
    show a - -((σ : ℂ) + I * y) = a + σ + I * y by ring]

theorem continuous_Gamma_neg_mul_Gamma {a : ℂ} {σ : ℝ} (hσ : σ < 0) (haσ : 0 < a.re + σ) :
    Continuous (fun y : ℝ => Gamma (-((σ : ℂ) + I * y)) * Gamma (a + σ + I * y)) := by
  refine continuous_iff_continuousAt.mpr fun y => ContinuousAt.mul ?_ ?_
  · exact (continuousAt_Gamma_of_re_pos (by simp; linarith)).comp (by fun_prop)
  · exact (continuousAt_Gamma_of_re_pos (by simp; linarith)).comp (by fun_prop)

/-- **Barnes's integral** (DLMF 15.6.6) when `re (c - b) > 0`. -/
theorem barnes_integral_of_re_sub_pos {a b c : ℂ} {x σ : ℝ} (hx : -1 < x) (hx0 : x < 0)
    (ha : 0 < a.re + σ) (hb : 0 < b.re + σ) (hσ : σ < 0) (hcb : 0 < (c - b).re) :
    regularizedGaussHGFun a b c (x : ℂ) =
      (1 / (2 * Real.pi * Gamma a * Gamma b)) * ∫ y : ℝ,
        Gamma (a + σ + I * y) * Gamma (b + σ + I * y) * Gamma (-((σ : ℂ) + I * y)) /
          Gamma (c + σ + I * y) * (-(x : ℂ)) ^ ((σ : ℂ) + I * y) := by
  set u : ℝ := -x with hudef
  have hu : 0 < u := by linarith
  have hu1 : u < 1 := by linarith
  have ha0 : 0 < a.re := by linarith
  have hb0 : 0 < b.re := by linarith
  have hc0 : 0 < c.re := by simp only [sub_re] at hcb; linarith
  have hcn : ∀ k : ℕ, c ≠ -k := fun k h => by
    have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hxn : ‖(x : ℂ)‖ < 1 := by rw [norm_real, Real.norm_eq_abs, abs_lt]; constructor <;> linarith
  set Φ : ℝ → ℂ := fun y => Gamma (-((σ : ℂ) + I * y)) * Gamma (a + σ + I * y) with hΦ
  have hΦi : Integrable Φ := integrable_Gamma_neg_mul_Gamma hσ ha
  have hΦc : Continuous Φ := continuous_Gamma_neg_mul_Gamma hσ ha
  set H : ℝ → ℝ → ℂ := fun t y => (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) *
    (Φ y * (u : ℂ) ^ ((σ : ℂ) + I * y) * (t : ℂ) ^ ((σ : ℂ) + I * y)) with hH
  have hGa : Gamma a ≠ 0 := Complex.Gamma_ne_zero_of_re_pos ha0
  have hGb : Gamma b ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hb0
  have hGcb : Gamma (c - b) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hcb
  -- Euler's integral, with the Mellin–Barnes integral inserted
  have hpt : ∀ t ∈ Ioo (0 : ℝ) 1,
      (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * (1 - (x : ℂ) * t) ^ (-a) =
        (Gamma a)⁻¹ * (1 / (2 * π)) * ∫ y : ℝ, H t y := by
    intro t ht
    have hut : 0 < u * t := mul_pos hu ht.1
    have hMB := Gamma_mul_one_add_cpow_neg_barnes hσ ha hut
    have h1 : (1 - (x : ℂ) * t) = ((1 + u * t : ℝ) : ℂ) := by rw [hudef]; push_cast; ring
    have hpow : ((1 + u * t : ℝ) : ℂ) ^ (-a) =
        (Gamma a)⁻¹ * (1 / (2 * π) * ∫ y : ℝ, Φ y * ((u * t : ℝ) : ℂ) ^ ((σ : ℂ) + I * y)) := by
      rw [← hMB]; field_simp
    have hH : ∫ y : ℝ, H t y = (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) *
        ∫ y : ℝ, Φ y * ((u * t : ℝ) : ℂ) ^ ((σ : ℂ) + I * y) := by
      rw [← integral_const_mul]
      congr 1; funext y
      rw [hH, ofReal_mul, mul_cpow_ofReal_nonneg hu.le ht.1.le]; ring
    rw [h1, hpow, hH]; ring
  -- integrability on the product
  set μ : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1) with hμ
  have hμprod :
      μ.prod volume = (volume.prod volume).restrict (Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) := by
    rw [hμ, ← Measure.prod_restrict, Measure.restrict_univ]
  have hf : Integrable (fun t : ℝ => ‖(t : ℂ) ^ (b + σ - 1) * (1 - (t : ℂ)) ^ (c - b - 1)‖) μ := by
    have h := betaIntegral_convergent (u := b + σ) (v := c - b) (by simp; linarith) hcb
    have h' := (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp h
    exact (h'.mono_set Ioo_subset_Ioc_self).norm
  have hg : Integrable (fun y : ℝ => ‖Φ y‖ * u ^ σ) := hΦi.norm.mul_const _
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
    · exact (hΦc.comp continuous_snd).continuousAt
    · exact ContinuousAt.cpow continuousAt_const (by fun_prop) (ofReal_mem_slitPlane.mpr hu)
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
        norm_cpow_eq_rpow_re_of_pos hu, norm_cpow_eq_rpow_re_of_pos ht0]
      simp only [sub_re, add_re, ofReal_re, one_re, mul_re, I_re, I_im, ofReal_im, zero_mul,
        sub_zero, mul_zero, add_zero]
      rw [show b.re + σ - 1 = (b.re - 1) + σ by ring, Real.rpow_add ht0]
      apply le_of_eq; ring
  have hswap := integral_integral_swap hHi
  -- the inner Beta integrals
  have hinner : ∀ y : ℝ, ∫ t, H t y ∂μ = Φ y * (u : ℂ) ^ ((σ : ℂ) + I * y) *
      (Gamma (b + σ + I * y) * Gamma (c - b) / Gamma (c + σ + I * y)) := by
    intro y
    have hbs : 0 < (b + σ + I * y).re := by
      simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, zero_mul, mul_zero, sub_zero,
        add_zero]; linarith
    have hB := Complex.Gamma_mul_Gamma_eq_betaIntegral hbs hcb
    rw [show b + σ + I * y + (c - b) = c + σ + I * y by ring] at hB
    have hGcs : Gamma (c + σ + I * y) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by
      simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, zero_mul, mul_zero, sub_zero,
        add_zero]; linarith [sub_re c b])
    have hbeta : betaIntegral (b + σ + I * y) (c - b) =
        ∫ t, (t : ℂ) ^ (b + σ + I * y - 1) * (1 - (t : ℂ)) ^ (c - b - 1) ∂μ := by
      rw [betaIntegral, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
    calc ∫ t, H t y ∂μ = Φ y * (u : ℂ) ^ ((σ : ℂ) + I * y) *
          ∫ t, (t : ℂ) ^ (b + σ + I * y - 1) * (1 - (t : ℂ)) ^ (c - b - 1) ∂μ := by
          rw [← integral_const_mul]
          refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
          have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.1.ne'
          have hsplit : (t : ℂ) ^ (b + σ + I * y - 1) =
              (t : ℂ) ^ (b - 1) * (t : ℂ) ^ ((σ : ℂ) + I * y) := by
            rw [← cpow_add _ _ ht0]; ring_nf
          simp only [hH]
          rw [hsplit]
          ring
      _ = _ := by
          rw [← hbeta]
          congr 1
          rw [eq_div_iff hGcs, hB]; ring
  -- assemble
  rw [regularizedGaussHGFun_eq_div_Gamma hcn, ordinaryHypergeometric_eq_integral hb0 hcb hxn,
    intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo,
    setIntegral_congr_fun measurableSet_Ioo hpt, integral_const_mul]
  change Gamma c / (Gamma b * Gamma (c - b)) *
      ((Gamma a)⁻¹ * (1 / (2 * π)) * ∫ t, ∫ y, H t y ∂volume ∂μ) / Gamma c = _
  rw [hswap, integral_congr_ae (ae_of_all _ hinner)]
  have hlast : ∫ y : ℝ, Φ y * (u : ℂ) ^ ((σ : ℂ) + I * y) *
      (Gamma (b + σ + I * y) * Gamma (c - b) / Gamma (c + σ + I * y)) =
      Gamma (c - b) * ∫ y : ℝ, Gamma (a + σ + I * y) * Gamma (b + σ + I * y) *
        Gamma (-((σ : ℂ) + I * y)) / Gamma (c + σ + I * y) * (-(x : ℂ)) ^ ((σ : ℂ) + I * y) := by
    rw [← integral_const_mul]
    congr 1; funext y
    rw [hΦ, show (-(x : ℂ)) = (u : ℂ) by rw [hudef]; push_cast; ring]
    ring
  rw [hlast]
  have hGc : Gamma c ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hc0
  generalize (∫ y : ℝ, Gamma (a + σ + I * y) * Gamma (b + σ + I * y) *
    Gamma (-((σ : ℂ) + I * y)) / Gamma (c + σ + I * y) * (-(x : ℂ)) ^ ((σ : ℂ) + I * y)) = J
  field_simp

/-- The numerator of Barnes's integrand, `Γ(a+s)Γ(b+s)Γ(-s)(-x)^s` on `s = σ + iy`, decays like
`e^{-3π|y|/2}`. -/
theorem exists_norm_barnes_numerator_le {a b : ℂ} {x σ : ℝ} (hx0 : x < 0)
    (ha : 0 < a.re + σ) (hb : 0 < b.re + σ) (hσ : σ < 0) :
    ∃ C : ℝ, ∃ K : ℕ, ∀ y : ℝ,
      ‖Gamma (a + σ + I * y) * Gamma (b + σ + I * y) * Gamma (-((σ : ℂ) + I * y)) *
        (-(x : ℂ)) ^ ((σ : ℂ) + I * y)‖ ≤ C * (1 + |y|) ^ K * Real.exp (-(π * |y|)) := by
  obtain ⟨Ca, Ka, hCa⟩ := exists_norm_Gamma_shift_le (x := a.re + σ) ha a.im
  obtain ⟨Cb, Kb, hCb⟩ := exists_norm_Gamma_shift_le (x := b.re + σ) hb b.im
  obtain ⟨Cs, Ks, hCs⟩ := exists_norm_Gamma_shift_le (x := -σ) (by linarith) 0
  have hCa0 : 0 ≤ Ca := (norm_nonneg _).trans (by simpa using hCa 0)
  have hCb0 : 0 ≤ Cb := (norm_nonneg _).trans (by simpa using hCb 0)
  have hCs0 : 0 ≤ Cs := (norm_nonneg _).trans (by simpa using hCs 0)
  have hu : 0 < -x := by linarith
  refine ⟨Ca * Cb * Cs * (-x) ^ σ, Ka + Kb + Ks, fun y => ?_⟩
  have e1 : a + σ + I * y = ((a.re + σ : ℝ) : ℂ) + I * ((a.im : ℂ) + (y : ℂ)) := by
    apply Complex.ext <;> simp
  have e2 : b + σ + I * y = ((b.re + σ : ℝ) : ℂ) + I * ((b.im : ℂ) + (y : ℂ)) := by
    apply Complex.ext <;> simp
  have e3 : -((σ : ℂ) + I * y) = ((-σ : ℝ) : ℂ) + I * (((0 : ℝ) : ℂ) + ((-y : ℝ) : ℂ)) := by
    push_cast; ring
  have h1 := hCa y; rw [← e1] at h1
  have h2 := hCb y; rw [← e2] at h2
  have h3 := hCs (-y); rw [← e3, abs_neg] at h3
  have h4 : ‖(-(x : ℂ)) ^ ((σ : ℂ) + I * y)‖ = (-x) ^ σ := by
    rw [show (-(x : ℂ)) = ((-x : ℝ) : ℂ) by push_cast; ring, norm_cpow_eq_rpow_re_of_pos hu]
    simp
  have hE : Real.exp (-(π * |y|) / 2) * Real.exp (-(π * |y|) / 2) * Real.exp (-(π * |y|) / 2)
      ≤ Real.exp (-(π * |y|)) := by
    rw [← Real.exp_add, ← Real.exp_add]; apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos, abs_nonneg y]
  rw [norm_mul, norm_mul, norm_mul, h4]
  have hp : 0 ≤ (1 + |y|) ^ (Ka + Kb + Ks) := by positivity
  calc ‖Gamma (a + σ + I * y)‖ * ‖Gamma (b + σ + I * y)‖ * ‖Gamma (-((σ : ℂ) + I * y))‖ *
        (-x) ^ σ
      ≤ (Ca * (1 + |y|) ^ Ka * Real.exp (-(π * |y|) / 2)) *
          (Cb * (1 + |y|) ^ Kb * Real.exp (-(π * |y|) / 2)) *
          (Cs * (1 + |y|) ^ Ks * Real.exp (-(π * |y|) / 2)) * (-x) ^ σ := by
        gcongr
    _ = Ca * Cb * Cs * (-x) ^ σ * (1 + |y|) ^ (Ka + Kb + Ks) *
          (Real.exp (-(π * |y|) / 2) * Real.exp (-(π * |y|) / 2) *
            Real.exp (-(π * |y|) / 2)) := by rw [pow_add, pow_add]; ring
    _ ≤ _ := by gcongr

/-- **Barnes's integral** (DLMF 15.6.6) for all `c`, by analytic continuation in `c` from
`barnes_integral_of_re_sub_pos`. -/
theorem barnes_integral_all {a b c : ℂ} {x σ : ℝ} (hx : -1 < x) (hx0 : x < 0)
    (ha : 0 < a.re + σ) (hb : 0 < b.re + σ) (hσ : σ < 0) :
    regularizedGaussHGFun a b c (x : ℂ) =
      (1 / (2 * Real.pi * Gamma a * Gamma b)) * ∫ y : ℝ,
        Gamma (a + σ + I * y) * Gamma (b + σ + I * y) * Gamma (-((σ : ℂ) + I * y)) /
          Gamma (c + σ + I * y) * (-(x : ℂ)) ^ ((σ : ℂ) + I * y) := by
  have hxn : ‖(x : ℂ)‖ < 1 := by
    rw [norm_real, Real.norm_eq_abs, abs_lt]; constructor <;> linarith
  set A : ℝ → ℂ := fun y => Gamma (a + σ + I * y) * Gamma (b + σ + I * y) *
    Gamma (-((σ : ℂ) + I * y)) * (-(x : ℂ)) ^ ((σ : ℂ) + I * y) with hA
  have hAc : Continuous A := by
    refine continuous_iff_continuousAt.mpr fun y => ?_
    refine ContinuousAt.mul (ContinuousAt.mul (ContinuousAt.mul ?_ ?_) ?_) ?_
    · exact (continuousAt_Gamma_of_re_pos (by simp; linarith)).comp (by fun_prop)
    · exact (continuousAt_Gamma_of_re_pos (by simp; linarith)).comp (by fun_prop)
    · exact (continuousAt_Gamma_of_re_pos (by simp; linarith)).comp (by fun_prop)
    · exact ContinuousAt.cpow continuousAt_const (by fun_prop)
        (by rw [show (-(x : ℂ)) = ((-x : ℝ) : ℂ) by push_cast; ring]
            exact ofReal_mem_slitPlane.mpr (by linarith))
  obtain ⟨C, K, hCK⟩ := exists_norm_barnes_numerator_le hx0 ha hb hσ
  have hR := differentiable_integral_mul_recip_Gamma hAc hCK σ
  have hrw : ∀ c : ℂ, ∫ y : ℝ, Gamma (a + σ + I * y) * Gamma (b + σ + I * y) *
      Gamma (-((σ : ℂ) + I * y)) / Gamma (c + σ + I * y) * (-(x : ℂ)) ^ ((σ : ℂ) + I * y) =
      ∫ y : ℝ, A y * (Gamma (c + σ + I * y))⁻¹ := fun c => by
    congr 1; funext y; simp only [hA]; ring
  have key := eq_of_analyticOnNhd_univ_of_eqOn (analyticOnNhd_regularizedGaussHGFun_c a b hxn)
    (g := fun c => (1 / (2 * Real.pi * Gamma a * Gamma b)) *
      ∫ y : ℝ, A y * (Gamma (c + σ + I * y))⁻¹)
    (fun c _ => (hR.const_mul _).analyticAt c)
    (U := {c : ℂ | 0 < (c - b).re})
    (isOpen_lt continuous_const (continuous_re.comp (continuous_id.sub continuous_const)))
    ⟨b + 1, by simp⟩
    (fun c hc => by
      simp only
      rw [barnes_integral_of_re_sub_pos hx hx0 ha hb hσ hc, hrw])
  rw [hrw]
  exact congrFun key c

end DLMF.Hypergeometric
