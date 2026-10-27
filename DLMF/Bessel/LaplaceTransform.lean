/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.Integrals

/-!
# The regularized Laplace–Bessel transform

Beals–Wong §9.8 in the conventional quadratic Gauss form. The proof starts with
Kummer's Laplace transform and the quadratic transformation, then lowers the
regularized denominator parameter by contiguous relations. This retains the
exceptional orders without cancellation of singular Gamma factors.
-/

@[expose] public noncomputable section

open Complex MeasureTheory Set Filter
open scoped Nat Topology
open DLMF.Confluent DLMF.Hypergeometric

namespace DLMF.Bessel

/-- The quadratic Laplace argument stays on the continued Gauss cut plane. -/
theorem besselLaplace_argument_mem_cutPlane {s : ℂ} (hs : 0 < s.re) {w : ℝ} (hw : 0 < w) :
    -(w : ℂ) ^ 2 / s ^ 2 ∈ cutPlane := by
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs
  let r : ℂ := w / s
  have hr : 0 < r.re := by
    dsimp [r]
    rw [div_re]
    simp only [ofReal_re, ofReal_im, zero_mul, zero_div, add_zero]
    exact div_pos (mul_pos hw hs) (normSq_pos.mpr hs0)
  have he : 1 - (-(w : ℂ) ^ 2 / s ^ 2) = 1 + r ^ 2 := by dsimp [r]; field_simp; ring
  rw [mem_cutPlane, he, mem_slitPlane_iff]
  by_cases hi : r.im = 0
  · left
    simp [pow_two, hi]
    positivity
  · right
    simp only [add_im, one_im, zero_add, pow_two, mul_im]
    rw [show r.re * r.im + r.im * r.re = 2 * r.re * r.im by ring]
    exact mul_ne_zero (mul_ne_zero two_ne_zero hr.ne') hi

/-- The quadratic Gauss transformation needed by the Kummer Laplace formula, continued
throughout the right half-plane in the Laplace variable. -/
private lemma besselLaplace_quadratic {b c s : ℂ} (hc : (1 / 2 : ℝ) < c.re)
    (hs : 0 < s.re) {w : ℝ} (hw : 0 < w) :
    Gamma (2 * c - 1) / Gamma c * (s + I * w) ^ (-b) *
        regularizedGaussHG (c - 1 / 2) b (2 * c - 1) (2 * I * w / (s + I * w)) =
      s ^ (-b) * regularizedGaussHG (b / 2) ((b + 1) / 2) c (-(w : ℂ) ^ 2 / s ^ 2) := by
  let V : Set ℂ := {s | 0 < s.re}
  let L (s : ℂ) := Gamma (2 * c - 1) / Gamma c * (s + I * w) ^ (-b) *
    regularizedGaussHG (c - 1 / 2) b (2 * c - 1) (2 * I * w / (s + I * w))
  let R (s : ℂ) := s ^ (-b) *
    regularizedGaussHG (b / 2) ((b + 1) / 2) c (-(w : ℂ) ^ 2 / s ^ 2)
  have hVo : IsOpen V := isOpen_lt continuous_const continuous_re
  have hL : AnalyticOnNhd ℂ L V := by
    apply DifferentiableOn.analyticOnNhd _ hVo
    intro z hz
    change 0 < z.re at hz
    have hzp : 0 < (z + I * w).re := by simpa using hz
    have hz0 : z + I * w ≠ 0 := by intro h; simp [h] at hzp
    have harg := kummerLaplace_argument_mem_cutPlane
      (k := 2 * I * w) (z := z + I * w) (by simpa using hz) hzp
    have hφ : DifferentiableAt ℂ (fun z : ℂ => 2 * I * w / (z + I * w)) z := by
      fun_prop (disch := assumption)
    have hp : DifferentiableAt ℂ (fun z : ℂ => (z + I * w) ^ (-b)) z :=
      ((differentiableAt_id : DifferentiableAt ℂ (fun z : ℂ => z) z).add_const (I * w)).cpow
        (differentiableAt_const (-b)) (Or.inl hzp)
    exact ((hp.const_mul _).mul
      ((differentiableAt_regularizedGaussHG _ _ _ harg).comp z hφ)).differentiableWithinAt
  have hR : AnalyticOnNhd ℂ R V := by
    apply DifferentiableOn.analyticOnNhd _ hVo
    intro z hz
    change 0 < z.re at hz
    have hz0 : z ≠ 0 := by intro h; simp [h] at hz
    have hφ : DifferentiableAt ℂ (fun z : ℂ => -(w : ℂ) ^ 2 / z ^ 2) z := by
      fun_prop (disch := exact pow_ne_zero 2 hz0)
    have hp : DifferentiableAt ℂ (fun z : ℂ => z ^ (-b)) z :=
      differentiableAt_id.cpow (differentiableAt_const (-b)) (Or.inl hz)
    exact (hp.mul ((differentiableAt_regularizedGaussHG _ _ _
      (besselLaplace_argument_mem_cutPlane hz hw)).comp z hφ)).differentiableWithinAt
  let z₀ : ℂ := (2 * w + 1 : ℝ)
  have hz₀ : z₀ ∈ V := by change 0 < (2 * w + 1 : ℝ); linarith
  have heq : L =ᶠ[𝓝 z₀] R := by
    have hnh : {z : ℂ | 2 * w < z.re} ∈ 𝓝 z₀ :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (by change 2 * w < (2 * w + 1 : ℝ); linarith)
    filter_upwards [hnh] with z hz
    have hzp : 0 < z.re := by linarith
    have hz0 : z ≠ 0 := by intro h; simp [h] at hzp
    have hAp : 0 < (z + I * w).re := by simpa using hzp
    have hA0 : z + I * w ≠ 0 := by intro h; simp [h] at hAp
    let u : ℂ := 2 * I * w / (z + I * w)
    have hu : ‖u‖ < 1 := by
      dsimp [u]
      rw [norm_div, div_lt_one (norm_pos_iff.mpr hA0)]
      simp only [norm_mul, norm_ofNat, norm_I, mul_one, norm_real, Real.norm_of_nonneg hw.le]
      exact hz.trans_le (by simpa using re_le_norm (z + I * w))
    have hy : ‖-(w : ℂ) ^ 2 / z ^ 2‖ < 1 := by
      rw [norm_div, norm_neg, norm_pow, norm_pow, norm_real, Real.norm_of_nonneg hw.le,
        div_lt_one (by positivity : 0 < ‖z‖ ^ 2)]
      nlinarith [re_le_norm z]
    have h2u : 2 - u ≠ 0 := by
      intro h
      have he : u = 2 := by linear_combination -h
      rw [he] at hu
      norm_num at hu
    have hmap : (u / (2 - u)) ^ 2 = -(w : ℂ) ^ 2 / z ^ 2 := by
      dsimp [u]
      field_simp [hz0, hA0]
      simp [I_sq]
    have hc0 : ∀ k : ℕ, c ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by linarith)
    have h2c : ∀ k : ℕ, 2 * (c - 1 / 2) ≠ -(k : ℂ) :=
      not_neg_nat_of_re_pos (by simp; linarith)
    have hct : ∀ k : ℕ, c - 1 / 2 + 1 / 2 ≠ -(k : ℂ) := by simpa using hc0
    have hq := quadratic_double_denominator (a := b) (b := c - 1 / 2) h2c hct hu
    rw [show 2 * (c - 1 / 2) = 2 * c - 1 by ring,
      show c - 1 / 2 + 1 / 2 = c by ring, hmap,
      ordinaryHypergeometric_eq_Gamma_mul_regularizedGaussHG
        (by simpa only [show 2 * (c - 1 / 2) = 2 * c - 1 by ring] using h2c) hu,
      ordinaryHypergeometric_eq_Gamma_mul_regularizedGaussHG hc0 hy] at hq
    have hargA := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hAp))
    have hargZ := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hzp))
    have hargAπ : (z + I * w).arg ≠ Real.pi := by linarith [Real.pi_pos]
    have hlog : log (z / (z + I * w)) = log z - log (z + I * w) := by
      rw [div_eq_mul_inv, Complex.log_mul hz0 (inv_ne_zero hA0), Complex.log_inv _ hargAπ]
      · rfl
      · rw [arg_inv, ite_eq_right hargAπ]
        constructor <;> linarith [hargA.1, hargA.2, hargZ.1, hargZ.2]
    have hratio : 1 - u / 2 = z / (z + I * w) := by dsimp [u]; field_simp; ring
    have hphase : (z + I * w) ^ (-b) * (1 - u / 2) ^ (-b) = z ^ (-b) := by
      rw [hratio, cpow_def_of_ne_zero hA0,
        cpow_def_of_ne_zero (div_ne_zero hz0 hA0), hlog, ← exp_add,
        cpow_def_of_ne_zero hz0]
      congr 1
      ring
    dsimp [L, R]
    rw [regularizedGaussHG_symm _ _ _ (mem_cutPlane_of_norm_lt_one hu)]
    have hGc : Gamma c ≠ 0 := Gamma_ne_zero hc0
    calc
      _ = ((z + I * w) ^ (-b) * (Gamma (2 * c - 1) *
          regularizedGaussHG b (c - 1 / 2) (2 * c - 1) u)) / Gamma c := by ring
      _ = ((z + I * w) ^ (-b) * ((1 - u / 2) ^ (-b) * (Gamma c *
          regularizedGaussHG (b / 2) ((b + 1) / 2) c (-(w : ℂ) ^ 2 / z ^ 2)))) / Gamma c := by rw [hq]
      _ = _ := by rw [← mul_assoc, hphase]; field_simp
  exact hL.eqOn_of_preconnected_of_eventuallyEq hR
    (convex_halfSpace_re_gt 0).isPreconnected hz₀ heq hs

/-- The nonsingular starting range for the regularized `₀F₁` Laplace transform. -/
private lemma laplace_regularized0F1_of_re_pos {b c s : ℂ}
    (hb : 0 < b.re) (hc : (1 / 2 : ℝ) < c.re) (hs : 0 < s.re)
    {w : ℝ} (hw : 0 < w) :
    IntegrableOn (fun t : ℝ => exp (-s * t) * (t : ℂ) ^ (b - 1) *
      regularizedHGFun ∅ {c} (-(w : ℂ) ^ 2 / 4 * (t : ℂ) ^ 2)) (Ioi 0) ∧
    (∫ t : ℝ in Ioi 0, exp (-s * t) * (t : ℂ) ^ (b - 1) *
      regularizedHGFun ∅ {c} (-(w : ℂ) ^ 2 / 4 * (t : ℂ) ^ 2)) =
      Gamma b * s ^ (-b) * regularizedGaussHG (b / 2) ((b + 1) / 2) c
        (-(w : ℂ) ^ 2 / s ^ 2) := by
  have hcpos : 0 < c.re := by linarith
  have h2cpos : 0 < (2 * c - 1).re := by simp; linarith
  have hc0 := not_neg_nat_of_re_pos hcpos
  have h2c0 := not_neg_nat_of_re_pos h2cpos
  let C : ℂ := Gamma (2 * c - 1) / Gamma c
  let K (t : ℝ) := exp (-(s + I * w) * t) * (t : ℂ) ^ (b - 1) *
    regularizedHGFun {c - 1 / 2} {2 * c - 1} ((2 * I * w) * t)
  have hK : IntegrableOn K (Ioi 0) := laplace_regularizedHGFun_integrable hb (by simpa using hs)
  have hrepr (t : ℝ) : regularizedHGFun ∅ {c} (-(w : ℂ) ^ 2 / 4 * (t : ℂ) ^ 2) =
      C * exp (-I * w * t) * regularizedHGFun {c - 1 / 2} {2 * c - 1} ((2 * I * w) * t) := by
    have h := kummerM_eq_exp_mul_regularized0F1 (ν := c - 1)
      (by simpa using hc0) (by simpa only [show 2 * (c - 1) + 1 = 2 * c - 1 by ring] using h2c0) ((2 * I * w) * t)
    rw [show c - 1 + 1 / 2 = c - 1 / 2 by ring,
      show 2 * (c - 1) + 1 = 2 * c - 1 by ring,
      show c - 1 + 1 = c by ring, kummerM_eq_mul_regularizedHGFun h2c0,
      show ((2 * I * w) * (t : ℂ)) ^ 2 / 16 = -(w : ℂ) ^ 2 / 4 * (t : ℂ) ^ 2 by
        linear_combination (w : ℂ) ^ 2 * (t : ℂ) ^ 2 / 4 * I_sq] at h
    have hexp : exp (-I * w * t) * exp ((2 * I * w * t) / 2) = 1 := by
      rw [← exp_add, show -I * w * (t : ℂ) + 2 * I * w * t / 2 = 0 by ring, exp_zero]
    have hh : exp (-I * w * t) * (Gamma (2 * c - 1) *
        regularizedHGFun {c - 1 / 2} {2 * c - 1} ((2 * I * w) * t)) =
        Gamma c * regularizedHGFun ∅ {c} (-(w : ℂ) ^ 2 / 4 * (t : ℂ) ^ 2) := by
      rw [h]
      calc
        _ = (exp (-I * w * t) * exp ((2 * I * w * t) / 2)) *
            (Gamma c * regularizedHGFun ∅ {c} (-(w : ℂ) ^ 2 / 4 * (t : ℂ) ^ 2)) := by ring
        _ = _ := by rw [hexp, one_mul]
    calc
      _ = (Gamma c * regularizedHGFun ∅ {c} (-(w : ℂ) ^ 2 / 4 * (t : ℂ) ^ 2)) / Gamma c :=
        (mul_div_cancel_left₀ _ (Gamma_ne_zero hc0)).symm
      _ = _ := by rw [← hh]; dsimp only [C]; ring
  have hp (t : ℝ) : exp (-s * t) * (t : ℂ) ^ (b - 1) *
      regularizedHGFun ∅ {c} (-(w : ℂ) ^ 2 / 4 * (t : ℂ) ^ 2) = C * K t := by
    rw [hrepr]
    have he : exp (-s * t) * exp (-I * w * t) = exp (-(s + I * w) * t) := by
      rw [← exp_add]
      congr 1
      ring
    dsimp only [K]
    linear_combination (C * (t : ℂ) ^ (b - 1) *
      regularizedHGFun {c - 1 / 2} {2 * c - 1} ((2 * I * w) * t)) * he
  constructor
  · exact (hK.const_mul C).congr (Filter.Eventually.of_forall fun t => (hp t).symm)
  · simp_rw [hp]
    rw [integral_const_mul, laplace_regularizedHGFun hb (by simpa using hs) (by simpa using hs)]
    have hq := besselLaplace_quadratic (b := b) hc hs hw
    dsimp [C]
    linear_combination (Gamma b) * hq

/-- The contiguous relation that lowers a regularized Gauss denominator by one, without
any exclusions on its parameters. -/
private lemma regularizedGaussHG_lower_c (a b c : ℂ) {z : ℂ} (hz : z ∈ cutPlane) :
    regularizedGaussHG a b c z = c * regularizedGaussHG a b (c + 1) z +
      a * b * z * regularizedGaussHG (a + 1) (b + 1) (c + 1 + 1) z := by
  have h1 := regularizedGaussHG_contiguous_c a b c hz
  have h2 := regularizedGaussHG_contiguous_shift_b b a (c + 1) hz
  rw [regularizedGaussHG_symm b a _ hz, regularizedGaussHG_symm b (a + 1) _ hz,
    regularizedGaussHG_symm (b + 1) (a + 1) _ hz] at h2
  linear_combination h1 - a * h2

/-- The convergence and evaluation assertion used in lowering the `₀F₁` denominator. -/
private def Laplace0F1Formula (c : ℂ) (w : ℝ) : Prop :=
  ∀ {b s : ℂ}, 0 < b.re → 0 < s.re →
    IntegrableOn (fun t : ℝ => exp (-s * t) * (t : ℂ) ^ (b - 1) *
      regularizedHGFun ∅ {c} (-(w : ℂ) ^ 2 / 4 * (t : ℂ) ^ 2)) (Ioi 0) ∧
    (∫ t : ℝ in Ioi 0, exp (-s * t) * (t : ℂ) ^ (b - 1) *
      regularizedHGFun ∅ {c} (-(w : ℂ) ^ 2 / 4 * (t : ℂ) ^ 2)) =
      Gamma b * s ^ (-b) * regularizedGaussHG (b / 2) ((b + 1) / 2) c
        (-(w : ℂ) ^ 2 / s ^ 2)

/-- Lower the denominator by the regularized contiguous relations, transporting absolute
integrability together with the evaluated integral. -/
private lemma laplace0F1Formula_lower {c : ℂ} {w : ℝ} (hw : 0 < w)
    (h1 : Laplace0F1Formula (c + 1) w) (h2 : Laplace0F1Formula (c + 1 + 1) w) :
    Laplace0F1Formula c w := by
  intro b s hb hs
  obtain ⟨hi1, he1⟩ := h1 hb hs
  obtain ⟨hi2, he2⟩ := h2 (b := b + 2) (by simp; linarith) hs
  let K (c b : ℂ) (t : ℝ) := exp (-s * t) * (t : ℂ) ^ (b - 1) *
    regularizedHGFun ∅ {c} (-(w : ℂ) ^ 2 / 4 * (t : ℂ) ^ 2)
  have hp (t : ℝ) (ht : 0 < t) : K c b t =
      c * K (c + 1) b t + (-(w : ℂ) ^ 2 / 4) * K (c + 1 + 1) (b + 2) t := by
    have hpow : (t : ℂ) ^ ((b + 2) - 1) = (t : ℂ) ^ (b - 1) * (t : ℂ) ^ 2 := by
      rw [show (b + 2) - 1 = (b - 1) + (2 : ℕ) by push_cast; ring,
        cpow_add _ _ (ofReal_ne_zero.mpr ht.ne'), cpow_natCast]
    dsimp only [K]
    rw [regularized0F1_contiguous, hpow]
    ring
  have hi := (hi1.const_mul c).add (hi2.const_mul (-(w : ℂ) ^ 2 / 4))
  have hae : K c b =ᵐ[volume.restrict (Ioi 0)]
      (fun t => c * K (c + 1) b t + (-(w : ℂ) ^ 2 / 4) * K (c + 1 + 1) (b + 2) t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using hp t ht
  refine ⟨hi.congr hae.symm, ?_⟩
  change (∫ t : ℝ in Ioi 0, K c b t) = _
  rw [integral_congr_ae hae, integral_add (hi1.const_mul c) (hi2.const_mul _),
    integral_const_mul, integral_const_mul, show (∫ t : ℝ in Ioi 0, K (c + 1) b t) = _ from he1,
    show (∫ t : ℝ in Ioi 0, K (c + 1 + 1) (b + 2) t) = _ from he2]
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs
  have hb0 : b ≠ 0 := by intro h; simp [h] at hb
  have hb1 : b + 1 ≠ 0 := by intro h; have := congrArg re h; simp at this; linarith
  have hG : Gamma (b + 2) = (b + 1) * b * Gamma b := by
    rw [show b + 2 = (b + 1) + 1 by ring, Gamma_add_one _ hb1, Gamma_add_one _ hb0]
    ring
  have hpow : s ^ (-(b + 2)) = s ^ (-b) / s ^ 2 := by
    rw [show -(b + 2) = -b + -(2 : ℕ) by push_cast; ring, cpow_add _ _ hs0,
      ]
    simp only [cpow_neg, cpow_natCast, div_eq_mul_inv]
  have hq := regularizedGaussHG_lower_c (b / 2) ((b + 1) / 2) c
    (besselLaplace_argument_mem_cutPlane hs hw)
  rw [hG, hpow, show (b + 2) / 2 = b / 2 + 1 by ring,
    show ((b + 2) + 1) / 2 = (b + 1) / 2 + 1 by ring]
  linear_combination -(Gamma b * s ^ (-b)) * hq

/-- Absolute convergence and evaluation of the Laplace transform of regularized `₀F₁`
on a negative quadratic ray, with every complex denominator parameter retained. -/
theorem laplace_regularized0F1 {b c s : ℂ} (hb : 0 < b.re) (hs : 0 < s.re)
    {w : ℝ} (hw : 0 < w) :
    IntegrableOn (fun t : ℝ => exp (-s * t) * (t : ℂ) ^ (b - 1) *
      regularizedHGFun ∅ {c} (-(w : ℂ) ^ 2 / 4 * (t : ℂ) ^ 2)) (Ioi 0) ∧
    (∫ t : ℝ in Ioi 0, exp (-s * t) * (t : ℂ) ^ (b - 1) *
      regularizedHGFun ∅ {c} (-(w : ℂ) ^ 2 / 4 * (t : ℂ) ^ 2)) =
      Gamma b * s ^ (-b) * regularizedGaussHG (b / 2) ((b + 1) / 2) c
        (-(w : ℂ) ^ 2 / s ^ 2) := by
  have hshift : ∀ M : ℕ, ∀ c : ℂ, (1 / 2 : ℝ) < c.re + M → Laplace0F1Formula c w := by
    intro M
    induction M with
    | zero =>
      intro c hc b s hb hs
      exact laplace_regularized0F1_of_re_pos hb (by simpa using hc) hs hw
    | succ M ih =>
      intro c hc
      apply laplace0F1Formula_lower hw
      · apply ih (c + 1)
        simp only [add_re, one_re, Nat.cast_add, Nat.cast_one] at hc ⊢
        linarith
      · apply ih (c + 1 + 1)
        simp only [add_re, one_re, Nat.cast_add, Nat.cast_one] at hc ⊢
        linarith
  obtain ⟨M, hM⟩ := exists_nat_gt (1 / 2 - c.re)
  exact hshift M c (by linarith) hb hs

/-- Factor the positive-real Bessel argument into the regularized quadratic-ray kernel. -/
private lemma besselJ_laplaceKernel_eq (μ ν s : ℂ) {w t : ℝ} (hw : 0 < w) (ht : 0 < t) :
  (t : ℂ) ^ (μ - 1) * exp (-s * t) * besselJ ν (w * t) =
    (w / 2 : ℂ) ^ ν * (exp (-s * t) * (t : ℂ) ^ (μ + ν - 1) *
      regularizedHGFun ∅ {ν + 1} (-(w : ℂ) ^ 2 / 4 * (t : ℂ) ^ 2)) := by
  have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  have hbase : ((w : ℂ) * t / 2) ^ ν = (w / 2 : ℂ) ^ ν * (t : ℂ) ^ ν := by
    rw [show (w : ℂ) * t / 2 = ((w / 2 : ℝ) : ℂ) * t by push_cast; ring,
      mul_cpow_ofReal_nonneg (by positivity) ht.le, ofReal_div, ofReal_ofNat]
  have hpow : (t : ℂ) ^ (μ - 1) * (t : ℂ) ^ ν = (t : ℂ) ^ (μ + ν - 1) := by
    rw [← cpow_add _ _ ht0]
    congr 1
    ring
  rw [besselJ_eq_regularized, hbase,
    show -(((w : ℂ) * t) ^ 2 / 4) = -(w : ℂ) ^ 2 / 4 * (t : ℂ) ^ 2 by ring]
  linear_combination ((w / 2 : ℂ) ^ ν * exp (-s * t) *
    regularizedHGFun ∅ {ν + 1} (-(w : ℂ) ^ 2 / 4 * (t : ℂ) ^ 2)) * hpow

/-- Absolute convergence of the Laplace–Bessel integral on the full right half-plane,
including all exceptional complex orders under the stated sufficient condition at zero. -/
theorem besselJ_laplace_integrable {μ ν s : ℂ} {w : ℝ}
    (hμν : 0 < (μ + ν).re) (hs : 0 < s.re) (hw : 0 < w) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (μ - 1) * exp (-s * t) * besselJ ν (w * t))
      (Ioi 0) := by
  apply ((laplace_regularized0F1 (c := ν + 1) hμν hs hw).1.const_mul ((w / 2 : ℂ) ^ ν)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact (besselJ_laplaceKernel_eq μ ν s hw ht).symm

/-- The Laplace–Bessel integral in the conventional regularized Gauss form, on the full
right half-plane and with no exceptional-order exclusions. -/
theorem besselJ_laplace_integral {μ ν s : ℂ} {w : ℝ}
    (hμν : 0 < (μ + ν).re) (hs : 0 < s.re) (hw : 0 < w) :
    (∫ t : ℝ in Ioi 0, (t : ℂ) ^ (μ - 1) * exp (-s * t) * besselJ ν (w * t)) =
      (w / 2 : ℂ) ^ ν * Gamma (μ + ν) * s ^ (-(μ + ν)) *
        regularizedGaussHG ((μ + ν) / 2) ((μ + ν + 1) / 2) (ν + 1)
          (-(w : ℂ) ^ 2 / s ^ 2) := by
  calc
    _ = (w / 2 : ℂ) ^ ν * ∫ t : ℝ in Ioi 0, exp (-s * t) * (t : ℂ) ^ (μ + ν - 1) *
        regularizedHGFun ∅ {ν + 1} (-(w : ℂ) ^ 2 / 4 * (t : ℂ) ^ 2) := by
      rw [← integral_const_mul]
      exact setIntegral_congr_fun measurableSet_Ioi fun t ht => besselJ_laplaceKernel_eq μ ν s hw ht
    _ = _ := by rw [(laplace_regularized0F1 hμν hs hw).2]; ring

end DLMF.Bessel
