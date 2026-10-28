/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.Integrals.Stieltjes

/-!
# Gauss transforms of confluent hypergeometric functions

Gaussian integral transforms of Kummer functions, including their branch powers and
normalization.

Source references and common attribution are retained in
`DLMF.Confluent.Integrals`.
-/

@[expose] public section

open Complex Filter MeasureTheory FormalMultilinearSeries

open scoped Real Topology ENNReal

open DLMF.Hypergeometric

open DLMF.Bessel

noncomputable section

namespace DLMF.Confluent

section GaussTransform

open Set
open scoped Nat

/-- Subordination: `∫₀^∞ e^{-t²u - ζ²/(4u)} u^{-3/2} du = (2√π/ζ) e^{-ζt}` for `ζ, t > 0`. -/
theorem confLP_subordination {ζ t : ℝ} (hζ : 0 < ζ) (ht : 0 < t) :
    ∫ u : ℝ in Ioi 0, exp (-((t : ℂ) ^ 2 * u) - (ζ : ℂ) ^ 2 / (4 * u)) * (u : ℂ) ^ (-(3 / 2 : ℂ)) =
      2 * (Real.sqrt π : ℂ) / ζ * exp (-((ζ : ℂ) * t)) := by
  set y := ζ * t with hy
  have hy0 : 0 < y := mul_pos hζ ht
  have hK := besselK_ofReal_eq_integral_schlafli' hy0 (-(1 / 2))
  have hU := kummerU_besselK (-(1 / 2)) (y : ℂ) (ofReal_mem_slitPlane.mpr hy0)
  rw [show -(1 / 2 : ℂ) + 1 / 2 = 0 by ring, show 2 * (-(1 / 2 : ℂ)) + 1 = 0 by ring,
    kummerU_zero, neg_neg] at hU
  rw [neg_neg, show -(1 / 2 : ℂ) - 1 = -(3 / 2) by ring] at hK
  set J := ∫ s : ℝ in Ioi 0, exp (-(s : ℂ) - (y : ℂ) ^ 2 / (4 * s)) * (s : ℂ) ^ (-(3 / 2 : ℂ))
    with hJ
  have ht2 : 0 < t ^ 2 := by positivity
  have hsub := integral_comp_mul_left_Ioi
    (fun s : ℝ => exp (-(s : ℂ) - (y : ℂ) ^ 2 / (4 * s)) * (s : ℂ) ^ (-(3 / 2 : ℂ))) 0 ht2
  rw [mul_zero] at hsub
  have hpt : ∀ u ∈ Ioi (0:ℝ), exp (-((t : ℂ) ^ 2 * u) - (ζ : ℂ) ^ 2 / (4 * u)) *
      (u : ℂ) ^ (-(3 / 2 : ℂ)) = (t : ℂ) ^ 3 *
        (exp (-(((t ^ 2 * u : ℝ)) : ℂ) - (y : ℂ) ^ 2 / (4 * ((t ^ 2 * u : ℝ) : ℂ))) *
          (((t ^ 2 * u : ℝ)) : ℂ) ^ (-(3 / 2 : ℂ))) := by
    intro u hu
    have hu0 : (0:ℝ) < u := hu
    have htc : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
    have huc : (u : ℂ) ≠ 0 := ofReal_ne_zero.mpr hu0.ne'
    have hp : (((t ^ 2 * u : ℝ)) : ℂ) ^ (-(3 / 2 : ℂ)) =
        ((t : ℂ) ^ 3)⁻¹ * (u : ℂ) ^ (-(3 / 2 : ℂ)) := by
      have hp' : (((t ^ 2 : ℝ)) : ℂ) ^ (-(3 / 2 : ℂ)) = ((t : ℂ) ^ 3)⁻¹ := by
        rw [show (-(3 / 2 : ℂ)) = ((-(3 / 2) : ℝ) : ℂ) by push_cast; ring,
          ← ofReal_cpow (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul ht.le,
          show ((2 : ℕ) : ℝ) * (-(3 / 2)) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg ht.le,
          Real.rpow_natCast]
        push_cast; ring
      rw [ofReal_mul, mul_cpow_ofReal_nonneg (by positivity) hu0.le, hp']
    rw [hp]
    have he : -(((t ^ 2 * u : ℝ)) : ℂ) - (y : ℂ) ^ 2 / (4 * ((t ^ 2 * u : ℝ) : ℂ)) =
        -((t : ℂ) ^ 2 * u) - (ζ : ℂ) ^ 2 / (4 * u) := by
      rw [hy]; push_cast; field_simp
    rw [he]
    field_simp
  have hsq : (2 * (y : ℂ)) ^ (1 / 2 : ℂ) * ((y : ℂ) / 2) ^ (1 / 2 : ℂ) = y := by
    rw [show 2 * (y : ℂ) = ((2 * y : ℝ) : ℂ) by push_cast; ring,
      show (y : ℂ) / 2 = ((y / 2 : ℝ) : ℂ) by push_cast; ring,
      ← mul_cpow_ofReal_nonneg (by positivity) (by positivity), ← ofReal_mul,
      show 2 * y * (y / 2) = y ^ 2 by ring,
      show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow (by positivity),
      ← Real.rpow_natCast, ← Real.rpow_mul hy0.le]
    norm_num
  have hyc : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hy0.ne'
  have hsπ : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hJy : J * y * exp (y : ℂ) = 2 * (Real.sqrt π : ℂ) := by
    rw [hK] at hU
    have h1 : (Real.sqrt π : ℂ) * (1 / (Real.sqrt π : ℂ)) = 1 := mul_one_div_cancel hsπ
    linear_combination (-2 * (Real.sqrt π : ℂ)) * hU -
      (exp (y : ℂ) * (2 * (y : ℂ)) ^ (1 / 2 : ℂ) * ((y : ℂ) / 2) ^ (1 / 2 : ℂ) * J) * h1 -
      (J * exp (y : ℂ)) * hsq
  have hJv : J = 2 * (Real.sqrt π : ℂ) * exp (-(y : ℂ)) / y := by
    rw [← hJy, Complex.exp_neg]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul, hsub, ← hJ, hJv,
    real_smul, hy]
  have hζc : (ζ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hζ.ne'
  have htc : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  push_cast
  field_simp

/-- `(1+x)^m ≤ 2^m (1 + x^m)` for `x, m ≥ 0`. -/
theorem confLP_one_add_rpow_le {x m : ℝ} (hx : 0 ≤ x) (hm : 0 ≤ m) :
    (1 + x) ^ m ≤ 2 ^ m * (1 + x ^ m) := by
  rcases le_total x 1 with h | h
  · calc (1 + x) ^ m ≤ 2 ^ m := Real.rpow_le_rpow (by linarith) (by linarith) hm
      _ ≤ 2 ^ m * (1 + x ^ m) := le_mul_of_one_le_right (by positivity)
          (by linarith [Real.rpow_nonneg hx m])
  · calc (1 + x) ^ m ≤ (2 * x) ^ m := Real.rpow_le_rpow (by linarith) (by linarith) hm
      _ = 2 ^ m * x ^ m := Real.mul_rpow (by norm_num) hx
      _ ≤ 2 ^ m * (1 + x ^ m) := by gcongr; linarith

/-- A polynomial bound for the Gaussian-transform integrand. -/
theorem confLP_gauss_bound (a b : ℂ) : ∃ C m : ℝ, 0 ≤ m ∧ ∀ t : ℝ, 0 < t →
    ‖exp (-(t : ℂ) ^ 2) * (t : ℂ) ^ (2 * b - 2) * regularizedHGFun {a} {b} ((t : ℂ) ^ 2)‖ ≤
      C * (t ^ (2 * b.re - 2) + t ^ (2 * b.re - 2 + m)) := by
  obtain ⟨C, hC⟩ := exists_norm_regularizedHGFun_neg_le (b - a) b
  set γ := (b - a).re
  refine ⟨|C| * 2 ^ |γ|, 2 * |γ|, by positivity, fun t ht => ?_⟩
  have hs : (0:ℝ) ≤ t ^ 2 := by positivity
  have h1 := hC (t ^ 2) hs
  have hk : exp (-(t : ℂ) ^ 2) * regularizedHGFun {a} {b} ((t : ℂ) ^ 2) =
      regularizedHGFun {b - a} {b} (-((t ^ 2 : ℝ) : ℂ)) := by
    rw [regularizedConfluent_kummer_transform a b, ← mul_assoc, ← Complex.exp_add]
    push_cast; ring_nf; rw [Complex.exp_zero, one_mul]
  have e : exp (-(t : ℂ) ^ 2) * (t : ℂ) ^ (2 * b - 2) * regularizedHGFun {a} {b} ((t : ℂ) ^ 2) =
      (t : ℂ) ^ (2 * b - 2) * regularizedHGFun {b - a} {b} (-((t ^ 2 : ℝ) : ℂ)) := by
    rw [← hk]; ring
  rw [e, norm_mul, norm_cpow_eq_rpow_re_of_pos ht]
  simp only [sub_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]
  have h2 : (1 + t ^ 2) ^ (-γ) ≤ 2 ^ |γ| * (1 + t ^ (2 * |γ|)) := by
    calc (1 + t ^ 2) ^ (-γ) ≤ (1 + t ^ 2) ^ |γ| :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (neg_le_abs γ)
      _ ≤ 2 ^ |γ| * (1 + (t ^ 2) ^ |γ|) := confLP_one_add_rpow_le hs (abs_nonneg γ)
      _ = 2 ^ |γ| * (1 + t ^ (2 * |γ|)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]; norm_num
  have htp : 0 < t ^ (2 * b.re - 2) := Real.rpow_pos_of_pos ht _
  calc t ^ (2 * b.re - 2) * ‖regularizedHGFun {b - a} {b} (-((t ^ 2 : ℝ) : ℂ))‖
      ≤ t ^ (2 * b.re - 2) * (|C| * (2 ^ |γ| * (1 + t ^ (2 * |γ|)))) := by
        gcongr
        calc _ ≤ C * (1 + t ^ 2) ^ (-γ) := h1
          _ ≤ |C| * (1 + t ^ 2) ^ (-γ) := by gcongr; exact le_abs_self C
          _ ≤ _ := by gcongr
    _ = _ := by
        rw [Real.rpow_add ht]; ring

/-- Integrability of the 13.10.6 integrand for `0 < re z`. -/
theorem confLP_gauss_integrableOn {a b z : ℂ} (hb : (1 / 2 : ℝ) < b.re) (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => exp (-z * t - (t : ℂ) ^ 2) * (t : ℂ) ^ (2 * b - 2) *
      regularizedHGFun {a} {b} ((t : ℂ) ^ 2)) (Ioi 0) := by
  obtain ⟨C, m, hm, hC⟩ := confLP_gauss_bound a b
  have hI1 := cfInt_integrableOn_rpow_exp (r := 2 * b.re - 2) (by linarith) hz
  have hI2 := cfInt_integrableOn_rpow_exp (r := 2 * b.re - 2 + m) (by linarith) hz
  refine ((hI1.add hI2).const_mul C).mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ContinuousOn.mul (ContinuousOn.mul (by fun_prop) ?_) ?_
    · exact ContinuousOn.cpow continuous_ofReal.continuousOn continuousOn_const
        fun t ht => ofReal_mem_slitPlane.mpr ht
    · exact (continuous_regularizedConfluent.comp (by fun_prop :
        Continuous fun t : ℝ => (a, b, (t : ℂ) ^ 2))).continuousOn
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0:ℝ) < t := ht
    have e : exp (-z * t - (t : ℂ) ^ 2) * (t : ℂ) ^ (2 * b - 2) *
        regularizedHGFun {a} {b} ((t : ℂ) ^ 2) = exp (-z * t) * (exp (-(t : ℂ) ^ 2) *
        (t : ℂ) ^ (2 * b - 2) * regularizedHGFun {a} {b} ((t : ℂ) ^ 2)) := by
      rw [sub_eq_add_neg, Complex.exp_add]; ring
    rw [e, norm_mul, Complex.norm_exp]
    have : (-z * t).re = -(z.re * t) := by simp
    rw [this]
    calc Real.exp (-(z.re * t)) * ‖exp (-(t : ℂ) ^ 2) * (t : ℂ) ^ (2 * b - 2) *
          regularizedHGFun {a} {b} ((t : ℂ) ^ 2)‖
        ≤ Real.exp (-(z.re * t)) * (C * (t ^ (2 * b.re - 2) + t ^ (2 * b.re - 2 + m))) := by
          gcongr; exact hC t ht0
      _ = _ := by simp only [Pi.add_apply]; ring

/-- `((x²:ℝ):ℂ)^w = x^{2w}` for `x > 0`. -/
theorem confLP_sq_cpow {x : ℝ} (hx : 0 < x) (w : ℂ) :
    (((x ^ 2 : ℝ)) : ℂ) ^ w = (x : ℂ) ^ (2 * w) := by
  have hxc : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  rw [sq, ofReal_mul, mul_cpow_ofReal_nonneg hx.le hx.le, ← cpow_add _ _ hxc]; ring_nf

/-- The inner `t`-integral of 13.10.6: a Kummer Laplace transform after `s = t²`. -/
theorem confLP_gauss_inner {a b : ℂ} (hb : (1 / 2 : ℝ) < b.re) {u : ℝ} (hu : 0 < u) :
    ∫ t : ℝ in Ioi 0, exp (-(t : ℂ) ^ 2) * (t : ℂ) ^ (2 * b - 2) *
        regularizedHGFun {a} {b} ((t : ℂ) ^ 2) * exp (-((t : ℂ) ^ 2 * u)) =
      1 / 2 * (Gamma (b - 1 / 2) * (((1 + u : ℝ)) : ℂ) ^ (-(b - 1 / 2)) *
        DLMF.Hypergeometric.regularizedGaussHG a (b - 1 / 2) b (1 / ((1 + u : ℝ) : ℂ))) := by
  have hL := laplace_regularizedHGFun (a := a) (b := b - 1 / 2) (c := b) (k := 1)
    (z := ((1 + u : ℝ) : ℂ)) (by simp; linarith) (by simp; linarith) (by simp; linarith)
  rw [← hL, ← integral_const_mul]
  set g : ℝ → ℂ := fun s => 1 / 2 * (exp (-((1 + u : ℝ) : ℂ) * s) * (s : ℂ) ^ (b - 1 / 2 - 1) *
    regularizedHGFun {a} {b} (1 * s)) with hg
  have hsub := integral_comp_rpow_Ioi g (p := 2) two_ne_zero
  rw [← hsub]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : (0:ℝ) < t := ht
  have htc : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht0.ne'
  simp only [hg, real_smul]
  rw [show t ^ (2:ℝ) = t ^ 2 by norm_cast, confLP_sq_cpow ht0, show (2:ℝ) - 1 = 1 by norm_num,
    Real.rpow_one, abs_two]
  have hp : (t : ℂ) * (t : ℂ) ^ (2 * (b - 1 / 2 - 1)) = (t : ℂ) ^ (2 * b - 2) := by
    conv_lhs => arg 1; rw [← cpow_one (t : ℂ)]
    rw [← cpow_add _ _ htc]; ring_nf
  have he : exp (-(t : ℂ) ^ 2) * exp (-((t : ℂ) ^ 2 * u)) =
      exp (-((1 + u : ℝ) : ℂ) * ((t ^ 2 : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]; push_cast; ring_nf
  push_cast
  rw [← hp]
  push_cast at he
  rw [← he]
  ring

/-- Pfaff's transformation in the form used for 13.10.6. -/
theorem confLP_gauss_pfaff (a b : ℂ) {u : ℝ} (hu : 0 < u) :
    (((1 + u : ℝ)) : ℂ) ^ (-(b - 1 / 2)) *
        DLMF.Hypergeometric.regularizedGaussHG a (b - 1 / 2) b (1 / ((1 + u : ℝ) : ℂ)) =
      (u : ℂ) ^ (-(b - 1 / 2)) *
        DLMF.Hypergeometric.regularizedGaussHG (b - 1 / 2) (b - a) b (-(1 / (u : ℂ))) := by
  have h1u : (0:ℝ) < 1 + u := by linarith
  have hw : (1 / ((1 + u : ℝ) : ℂ)) ∈ DLMF.Hypergeometric.cutPlane := by
    rw [DLMF.Hypergeometric.mem_cutPlane]
    have h1c' : (1 : ℂ) + u ≠ 0 := by exact_mod_cast h1u.ne'
    rw [show (1 : ℂ) - 1 / ((1 + u : ℝ) : ℂ) = ((u / (1 + u) : ℝ) : ℂ) by
      push_cast; field_simp [h1c']; ring]
    exact ofReal_mem_slitPlane.mpr (by positivity)
  rw [DLMF.Hypergeometric.regularizedGaussHG_symm _ _ _ hw,
    DLMF.Hypergeometric.regularizedGaussHG_pfaff _ _ _ hw]
  have huc : (u : ℂ) ≠ 0 := ofReal_ne_zero.mpr hu.ne'
  have h1c : ((1 + u : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr h1u.ne'
  have h1c' : (1 : ℂ) + u ≠ 0 := by exact_mod_cast h1u.ne'
  have harg : (1 / ((1 + u : ℝ) : ℂ)) / (1 / ((1 + u : ℝ) : ℂ) - 1) = -(1 / (u : ℂ)) := by
    push_cast
    rw [div_sub_one h1c', div_div_div_cancel_right₀ h1c', show (1 : ℂ) - (1 + u) = -u by ring,
      div_neg]
  have h1w : (1 : ℂ) - 1 / ((1 + u : ℝ) : ℂ) = (u : ℂ) * (((1 + u : ℝ)) : ℂ)⁻¹ := by
    push_cast
    rw [one_div, ← div_eq_mul_inv, eq_div_iff h1c', sub_mul, inv_mul_cancel₀ h1c']; ring
  rw [harg, h1w, ← ofReal_inv, mul_cpow_ofReal_nonneg hu.le (by positivity), ofReal_inv,
    inv_cpow _ _ (by rw [arg_ofReal_of_nonneg h1u.le]; exact Real.pi_ne_zero.symm)]
  have hne : (((1 + u : ℝ)) : ℂ) ^ (-(b - 1 / 2)) ≠ 0 := by
    rw [cpow_def_of_ne_zero h1c]; exact exp_ne_zero _
  rw [show ∀ X Y Z : ℂ, X * (Y * X⁻¹ * Z) = X * X⁻¹ * (Y * Z) by intros; ring,
    mul_inv_cancel₀ hne, one_mul]

/-- The outer `u`-integral of 13.10.6: after `u = 1/v` it is Tricomi's Gauss-type integral 13.4.8. -/
theorem confLP_gauss_outer {a b : ℂ} (hb : (1 / 2 : ℝ) < b.re) {ζ : ℝ} (hζ : 0 < ζ) :
    ∫ u : ℝ in Ioi 0, exp (-(ζ : ℂ) ^ 2 / (4 * u)) * (u : ℂ) ^ (-(3 / 2 : ℂ)) *
        ((u : ℂ) ^ (-(b - 1 / 2)) *
          DLMF.Hypergeometric.regularizedGaussHG (b - 1 / 2) (b - a) b (-(1 / (u : ℂ)))) =
      2 / ζ * kummerU (b - 1 / 2) (a + 1 / 2) ((ζ : ℂ) ^ 2 / 4) := by
  set y : ℂ := (ζ : ℂ) ^ 2 / 4 with hy
  have hyr : y = (((ζ / 2) ^ 2 : ℝ) : ℂ) := by rw [hy]; push_cast; ring
  have hy0 : 0 < y.re := by rw [hyr, ofReal_re]; positivity
  have hU := kummerU_gauss (a := b - 1 / 2) (b := a + 1 / 2) (c := b) (z := y)
    (by linarith) hy0
  rw [show b - 1 / 2 - (a + 1 / 2) + 1 = b - a by ring, show b - (b - 1 / 2) = 1 / 2 by ring] at hU
  have hsq : y ^ (1 / 2 : ℂ) = (ζ : ℂ) / 2 := by
    rw [hyr, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow (by positivity),
      ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  rw [hU, hsq]
  set g : ℝ → ℂ := fun u => exp (-(ζ : ℂ) ^ 2 / (4 * u)) * (u : ℂ) ^ (-(3 / 2 : ℂ)) *
        ((u : ℂ) ^ (-(b - 1 / 2)) *
          DLMF.Hypergeometric.regularizedGaussHG (b - 1 / 2) (b - a) b (-(1 / (u : ℂ)))) with hg
  have hsub := integral_comp_rpow_Ioi g (p := -1) (by norm_num)
  rw [← hsub]
  have hζc : (ζ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hζ.ne'
  rw [show 2 / (ζ : ℂ) * ((ζ : ℂ) / 2 * ∫ t : ℝ in Ioi 0, exp (-y * t) * (t : ℂ) ^ (b - 1) *
      DLMF.Hypergeometric.regularizedGaussHG (b - 1 / 2) (b - a) b (-(t : ℂ))) =
      ∫ t : ℝ in Ioi 0, exp (-y * t) * (t : ℂ) ^ (b - 1) *
      DLMF.Hypergeometric.regularizedGaussHG (b - 1 / 2) (b - a) b (-(t : ℂ)) by field_simp]
  refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
  have hv0 : (0:ℝ) < v := hv
  have hvc : (v : ℂ) ≠ 0 := ofReal_ne_zero.mpr hv0.ne'
  have hargv : (v : ℂ).arg ≠ π := by rw [arg_ofReal_of_nonneg hv0.le]; exact Real.pi_ne_zero.symm
  simp only [hg, real_smul]
  rw [Real.rpow_neg_one, abs_neg, abs_one, one_mul, show (-1 : ℝ) - 1 = -2 by norm_num]
  have h2 : ((v ^ (-2 : ℝ) : ℝ) : ℂ) = (v : ℂ) ^ (-2 : ℂ) := by
    rw [ofReal_cpow hv0.le]; norm_num
  have hinv : ∀ w : ℂ, ((v⁻¹ : ℝ) : ℂ) ^ w = (v : ℂ) ^ (-w) := fun w => by
    rw [ofReal_inv, inv_cpow _ _ hargv, cpow_neg]
  rw [h2, hinv, hinv, ofReal_inv, show (1 : ℂ) / (v : ℂ)⁻¹ = v by rw [one_div, inv_inv]]
  have hp : (v : ℂ) ^ (-2 : ℂ) * ((v : ℂ) ^ (-(-(3 / 2 : ℂ))) * (v : ℂ) ^ (-(-(b - 1 / 2)))) =
      (v : ℂ) ^ (b - 1) := by
    rw [← cpow_add _ _ hvc, ← cpow_add _ _ hvc]; ring_nf
  have he : exp (-(ζ : ℂ) ^ 2 / (4 * (v : ℂ)⁻¹)) = exp (-y * v) := by
    rw [hy]; congr 1; field_simp
  rw [he, ← hp]
  ring

/-- `π^{-1/2} = 1/√π` as complex numbers. -/
theorem confLP_pi_cpow_neg_half : (π : ℂ) ^ (-(1 / 2 : ℂ)) = ((Real.sqrt π)⁻¹ : ℝ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg Real.pi_pos.le, ofReal_cpow Real.pi_pos.le]
  push_cast; ring_nf

/-- 13.10.6 for real positive `z`, by subordination and Fubini. -/
theorem confLP_gauss_real {a b : ℂ} (hb : (1 / 2 : ℝ) < b.re) {ζ : ℝ} (hζ : 0 < ζ) :
    ∫ t : ℝ in Ioi 0, exp (-(ζ : ℂ) * t - (t : ℂ) ^ 2) * (t : ℂ) ^ (2 * b - 2) *
        regularizedHGFun {a} {b} ((t : ℂ) ^ 2) =
      (1 / 2) * (π : ℂ) ^ (-(1 / 2 : ℂ)) * Gamma (b - 1 / 2) *
        kummerU (b - 1 / 2) (a + 1 / 2) ((ζ : ℂ) ^ 2 / 4) := by
  set c : ℝ → ℂ := fun t => exp (-(t : ℂ) ^ 2) * (t : ℂ) ^ (2 * b - 2) *
    regularizedHGFun {a} {b} ((t : ℂ) ^ 2) with hc
  set k : ℝ → ℝ → ℂ := fun t u => exp (-((t : ℂ) ^ 2 * u) - (ζ : ℂ) ^ 2 / (4 * u)) *
    (u : ℂ) ^ (-(3 / 2 : ℂ)) with hk
  set G : ℝ → ℝ → ℂ := fun t u => c t * k t u with hG
  have hsπ : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hζc : (ζ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hζ.ne'
  have hS : ∀ t : ℝ, 0 < t → ∫ u : ℝ in Ioi 0, k t u =
      2 * (Real.sqrt π : ℂ) / ζ * exp (-((ζ : ℂ) * t)) := fun t ht => confLP_subordination hζ ht
  have hpt : ∀ t ∈ Ioi (0:ℝ), exp (-(ζ : ℂ) * t - (t : ℂ) ^ 2) * (t : ℂ) ^ (2 * b - 2) *
      regularizedHGFun {a} {b} ((t : ℂ) ^ 2) =
      (ζ / (2 * Real.sqrt π) : ℂ) * ∫ u : ℝ in Ioi 0, G t u := by
    intro t ht
    simp only [hG]
    rw [integral_const_mul, hS t ht]
    simp only [hc]
    rw [sub_eq_add_neg, Complex.exp_add, show -(ζ : ℂ) * t = -((ζ : ℂ) * t) by ring]
    field_simp
  -- Fubini
  have hcm : Measurable c := by
    simp only [hc]
    exact (by fun_prop : Measurable fun t : ℝ => exp (-(t : ℂ) ^ 2) * (t : ℂ) ^ (2 * b - 2)).mul
      (continuous_regularizedConfluent.comp (by fun_prop :
        Continuous fun t : ℝ => (a, b, (t : ℂ) ^ 2))).measurable
  have hkm : Measurable (Function.uncurry k) := by
    simp only [hk]; fun_prop
  have hm : AEStronglyMeasurable (Function.uncurry G)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) :=
    ((hcm.comp measurable_fst).mul hkm).aestronglyMeasurable
  have hkR : ∀ t : ℝ, ∀ u ∈ Ioi (0:ℝ), k t u =
      ((Real.exp (-(t ^ 2 * u) - ζ ^ 2 / (4 * u)) * u ^ (-(3 / 2) : ℝ) : ℝ) : ℂ) := by
    intro t u hu
    have hu0 : (0:ℝ) < u := hu
    simp only [hk]
    rw [ofReal_mul, ofReal_exp, ofReal_cpow hu0.le]
    push_cast; ring_nf
  have hGi : Integrable (Function.uncurry G)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
    refine (integrable_prod_iff hm).mpr ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have hne : ∫ u : ℝ in Ioi 0, k t u ≠ 0 := by
        rw [hS t ht]
        exact mul_ne_zero (div_ne_zero (mul_ne_zero two_ne_zero hsπ) hζc) (exp_ne_zero _)
      exact (confLP_integrableOn_of_ne_zero hne).const_mul (c t)
    · have hI := (confLP_gauss_integrableOn (a := a) (z := (ζ : ℂ)) hb (by simpa using hζ)).norm
      refine IntegrableOn.congr_fun (hI.const_mul (2 * Real.sqrt π / ζ)) (fun t ht => ?_)
        measurableSet_Ioi
      have ht0 : (0:ℝ) < t := ht
      simp only [Function.uncurry_apply_pair, hG, norm_mul]
      rw [integral_const_mul, confLP_setIntegral_norm_of_ofReal measurableSet_Ioi (hkR t)
        (fun u hu => mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (le_of_lt hu) _)), hS t ht0]
      rw [sub_eq_add_neg, Complex.exp_add, show -(ζ : ℂ) * t = -((ζ : ℂ) * t) by ring]
      simp only [hc, norm_mul, norm_div, Complex.norm_real, Complex.norm_ofNat]
      rw [Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_of_nonneg hζ.le]
      ring
  have hinner : ∀ u ∈ Ioi (0:ℝ), ∫ t : ℝ in Ioi 0, G t u =
      1 / 2 * Gamma (b - 1 / 2) * (exp (-(ζ : ℂ) ^ 2 / (4 * u)) * (u : ℂ) ^ (-(3 / 2 : ℂ)) *
        ((u : ℂ) ^ (-(b - 1 / 2)) *
          DLMF.Hypergeometric.regularizedGaussHG (b - 1 / 2) (b - a) b (-(1 / (u : ℂ))))) := by
    intro u hu
    have hu0 : (0:ℝ) < u := hu
    have h := confLP_gauss_inner (a := a) hb hu0
    rw [mul_assoc (Gamma _), confLP_gauss_pfaff a b hu0] at h
    have e : ∀ t : ℝ, G t u = (exp (-(ζ : ℂ) ^ 2 / (4 * u)) * (u : ℂ) ^ (-(3 / 2 : ℂ))) *
        (exp (-(t : ℂ) ^ 2) * (t : ℂ) ^ (2 * b - 2) * regularizedHGFun {a} {b} ((t : ℂ) ^ 2) *
          exp (-((t : ℂ) ^ 2 * u))) := by
      intro t
      simp only [hG, hc, hk]
      rw [show -((t : ℂ) ^ 2 * u) - (ζ : ℂ) ^ 2 / (4 * u) =
        -((t : ℂ) ^ 2 * u) + -(ζ : ℂ) ^ 2 / (4 * u) by ring, Complex.exp_add]
      ring
    simp_rw [e]
    rw [integral_const_mul, h]
    ring
  calc ∫ t : ℝ in Ioi 0, exp (-(ζ : ℂ) * t - (t : ℂ) ^ 2) * (t : ℂ) ^ (2 * b - 2) *
        regularizedHGFun {a} {b} ((t : ℂ) ^ 2)
      = ∫ t : ℝ in Ioi 0, (ζ / (2 * Real.sqrt π) : ℂ) * ∫ u : ℝ in Ioi 0, G t u :=
        setIntegral_congr_fun measurableSet_Ioi hpt
    _ = (ζ / (2 * Real.sqrt π) : ℂ) * ∫ u : ℝ in Ioi 0, ∫ t : ℝ in Ioi 0, G t u := by
        rw [integral_const_mul, integral_integral_swap hGi]
    _ = (ζ / (2 * Real.sqrt π) : ℂ) * (1 / 2 * Gamma (b - 1 / 2) *
          (2 / ζ * kummerU (b - 1 / 2) (a + 1 / 2) ((ζ : ℂ) ^ 2 / 4))) := by
        rw [setIntegral_congr_fun measurableSet_Ioi hinner, integral_const_mul,
          confLP_gauss_outer hb hζ]
    _ = _ := by
        rw [confLP_pi_cpow_neg_half]
        push_cast
        field_simp

/-- The integrand of 13.10.6 factors as `e^{-z t}` times a `z`-independent part. -/
theorem confLP_gauss_factor (a b z : ℂ) (t : ℝ) :
    exp (-z * t - (t : ℂ) ^ 2) * (t : ℂ) ^ (2 * b - 2) * regularizedHGFun {a} {b} ((t : ℂ) ^ 2) =
      exp (-z * t) * (exp (-(t : ℂ) ^ 2) * (t : ℂ) ^ (2 * b - 2) *
        regularizedHGFun {a} {b} ((t : ℂ) ^ 2)) := by
  rw [sub_eq_add_neg, Complex.exp_add]; ring

/-- Holomorphic dependence of the Gaussian transform of `𝐌` on `z`. -/
theorem confLP_gauss_differentiableOn {a b : ℂ} (hb : (1 / 2 : ℝ) < b.re) :
    DifferentiableOn ℂ (fun z : ℂ => ∫ t : ℝ in Ioi 0,
      exp (-z * t - (t : ℂ) ^ 2) * (t : ℂ) ^ (2 * b - 2) *
        regularizedHGFun {a} {b} ((t : ℂ) ^ 2)) {z : ℂ | 0 < z.re} := by
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
  obtain ⟨C, m, hm, hC⟩ := confLP_gauss_bound a b
  let Q (t : ℝ) : ℂ := exp (-(t : ℂ) ^ 2) * (t : ℂ) ^ (2 * b - 2) *
    regularizedHGFun {a} {b} ((t : ℂ) ^ 2)
  let F (z : ℂ) (t : ℝ) : ℂ := exp (-z * t - (t : ℂ) ^ 2) * (t : ℂ) ^ (2 * b - 2) *
    regularizedHGFun {a} {b} ((t : ℂ) ^ 2)
  let r : ℝ := 2 * b.re - 2
  let bd (t : ℝ) : ℝ := C * (t ^ (r + 1) * Real.exp (-(δ * t)) +
    t ^ (r + 1 + m) * Real.exp (-(δ * t)))
  have hbd : IntegrableOn bd (Ioi 0) := by
    have h1 := cfInt_integrableOn_rpow_exp (r := r + 1) (by dsimp [r]; linarith) hδ
    have h2 := cfInt_integrableOn_rpow_exp (r := r + 1 + m) (by dsimp [r]; linarith) hδ
    exact (h1.add h2).const_mul C
  have hmeas : ∀ᶠ z in 𝓝 z₀, AEStronglyMeasurable (F z) (volume.restrict (Ioi 0)) := by
    filter_upwards [Metric.ball_mem_nhds _ hδ] with z hz
    exact (confLP_gauss_integrableOn (a := a) hb (hδ.trans (hre z hz))).aestronglyMeasurable
  have hF0 : Integrable (F z₀) (volume.restrict (Ioi 0)) := confLP_gauss_integrableOn hb hz₀
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi 0)) (F := F) (F' := fun z t => -(t : ℂ) * F z t)
    (bound := bd) (Metric.ball_mem_nhds _ hδ) hmeas hF0
    ((by fun_prop : Measurable fun t : ℝ => -(t : ℂ)).aestronglyMeasurable.mul
      hF0.aestronglyMeasurable) ?_ hbd ?_
  · exact hd.2.differentiableAt.differentiableWithinAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht z hz
    change 0 < t at ht
    have he : Real.exp (-z.re * t) ≤ Real.exp (-(δ * t)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hre z hz]
    have hQ := hC t ht
    have hp1 : t * t ^ r = t ^ (r + 1) := by
      rw [Real.rpow_add_one ht.ne']; ring
    have hp2 : t * t ^ (r + m) = t ^ (r + 1 + m) := by
      rw [show r + 1 + m = (r + m) + 1 by ring, Real.rpow_add_one ht.ne']; ring
    dsimp only [F]
    rw [confLP_gauss_factor, norm_mul, norm_mul, norm_neg, Complex.norm_real,
      Real.norm_of_nonneg ht.le, Complex.norm_exp]
    simp only [neg_mul, neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    calc t * (Real.exp (-(z.re * t)) * ‖Q t‖)
        ≤ t * (Real.exp (-(δ * t)) * (C * (t ^ r + t ^ (r + m)))) := by
          have : Real.exp (-(z.re * t)) ≤ Real.exp (-(δ * t)) := by simpa [neg_mul] using he
          gcongr
      _ = bd t := by
          dsimp only [bd]
          rw [← hp1, ← hp2]; ring
  · filter_upwards with t z _
    have hh := (((((hasDerivAt_id z).neg.mul_const (t : ℂ)).sub_const
      ((t : ℂ) ^ 2)).cexp.mul_const ((t : ℂ) ^ (2 * b - 2))).mul_const
      (regularizedHGFun {a} {b} ((t : ℂ) ^ 2)))
    simp only [Pi.neg_apply, id_eq] at hh
    convert hh using 1
    dsimp only [F]
    ring

/-- A Gaussian-weighted Laplace transform of `𝐌`; it converges for `0 < Re z`.
It is placed after the Stieltjes section because its proof uses 13.4.8. -/
@[dlmf 13.10.E6]
theorem gauss_regularizedHGFun {a b z : ℂ} (hb : (1 / 2 : ℝ) < b.re) (hz : 0 < z.re) :
    ∫ t : ℝ in Set.Ioi 0,
        exp (-z * t - (t : ℂ) ^ 2) * (t : ℂ) ^ (2 * b - 2) *
          regularizedHGFun {a} {b} ((t : ℂ) ^ 2) =
      (1 / 2) * (π : ℂ) ^ (-(1 / 2 : ℂ)) * Gamma (b - 1 / 2) *
        kummerU (b - 1 / 2) (a + 1 / 2) (z ^ 2 / 4) := by
  let V : Set ℂ := {z | 0 < z.re}
  have hVo : IsOpen V := isOpen_lt continuous_const continuous_re
  have hJ : AnalyticOnNhd ℂ (fun z : ℂ => ∫ t : ℝ in Ioi 0,
      exp (-z * t - (t : ℂ) ^ 2) * (t : ℂ) ^ (2 * b - 2) *
        regularizedHGFun {a} {b} ((t : ℂ) ^ 2)) V :=
    (confLP_gauss_differentiableOn hb).analyticOnNhd hVo
  have hU : AnalyticOnNhd ℂ (fun z : ℂ => (1 / 2) * (π : ℂ) ^ (-(1 / 2 : ℂ)) *
      Gamma (b - 1 / 2) * kummerU (b - 1 / 2) (a + 1 / 2) (z ^ 2 / 4)) V := by
    apply DifferentiableOn.analyticOnNhd _ hVo
    intro w hw
    have hw0 : 0 < w.re := hw
    have hw' : w ^ 2 / 4 ∈ slitPlane := by
      have hre : (w ^ 2 / 4).re = (w.re ^ 2 - w.im ^ 2) / 4 := by
        rw [Complex.div_ofNat_re]; simp [sq]
      have him : (w ^ 2 / 4).im = 2 * w.re * w.im / 4 := by
        rw [Complex.div_ofNat_im]; simp [sq]; ring
      rw [mem_slitPlane_iff]
      by_cases hy : w.im = 0
      · left; rw [hre, hy]; nlinarith
      · right; rw [him]; exact div_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hw0.ne') hy)
          (by norm_num)
    exact (((differentiableAt_kummerU (b - 1 / 2) (a + 1 / 2) hw').comp (f := fun z : ℂ => z ^ 2 / 4) w
      (by fun_prop)).const_mul
      ((1 / 2) * (π : ℂ) ^ (-(1 / 2 : ℂ)) * Gamma (b - 1 / 2))).differentiableWithinAt
  have hfreq : ∃ᶠ w in 𝓝[≠] ((1 : ℝ) : ℂ), (fun z : ℂ => ∫ t : ℝ in Ioi 0,
      exp (-z * t - (t : ℂ) ^ 2) * (t : ℂ) ^ (2 * b - 2) *
        regularizedHGFun {a} {b} ((t : ℂ) ^ 2)) w =
      (fun z : ℂ => (1 / 2) * (π : ℂ) ^ (-(1 / 2 : ℂ)) *
        Gamma (b - 1 / 2) * kummerU (b - 1 / 2) (a + 1 / 2) (z ^ 2 / 4)) w := by
    have ht : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[≠] (1:ℝ)) (𝓝[≠] ((1:ℝ) : ℂ)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · exact (continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with r hr
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, ofReal_inj] using hr
    apply ht.frequently
    apply Eventually.frequently
    filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds (zero_lt_one' ℝ))] with r hr
    exact confLP_gauss_real hb hr
  exact hJ.eqOn_of_preconnected_of_frequently_eq hU (convex_halfSpace_re_gt 0).isPreconnected
    (by change 0 < ((1:ℝ) : ℂ).re; simp) hfreq hz

end GaussTransform

end DLMF.Confluent

end
end
