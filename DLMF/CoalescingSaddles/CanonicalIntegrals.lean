/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.CoalescingSaddles.Basic
public import DLMF.Core.Framework
public import DLMF.Airy.IntegralRepresentations
public import Mathlib.Analysis.SpecialFunctions.PolarCoord

/-!
# Catastrophes and canonical integrals (DLMF §36.2)

Statements acquired from the NIST DLMF (version 1.2.8), checked 2026-10-26.

The canonical integrals are defined in `DLMF.CoalescingSaddles.Basic` as absolutely convergent
integrals over rotated contours. This file proves their integrability, states the agreement with
the oscillatory real integrals of DLMF (36.2.4, 36.2.5; admitted), and acquires the alternative
representations 36.2.6–36.2.9, the special cases 36.2.12–36.2.21, 36.2.28–36.2.29 and the
symmetries 36.2.22–36.2.27.

## Main results

* `integrable_cuspoidIntegrand`: the rotated-contour integrand is integrable (any phase `κ > 0`);
* `cuspoidIntegral_zero_dim` (36.2.12), `cuspoidIntegral_one` (36.2.13, Airy),
  `cuspoidIntegral_at_zero` (36.2.15);
* `cuspoidIntegral_even_symm` (36.2.22), `cuspoidIntegral_odd_conj` (36.2.23);
* `hyperbolicUmbilicIntegral_z_zero` (36.2.21), `hyperbolicUmbilicIntegral_zero` (36.2.18),
  `hyperbolicUmbilicIntegral_conj` (36.2.24), `hyperbolicUmbilicIntegral_swap` (36.2.27);
* `ellipticUmbilicIntegral_rotate` (36.2.26).
-/

@[expose] public noncomputable section

open Complex MeasureTheory Set Filter
open scoped Real Topology ComplexConjugate

namespace DLMF.CoalescingSaddles

/-! ### The rotated cuspoid contour -/

lemma s36a_angle_mul (K : ℕ) : ((K : ℝ) + 2) * cuspoidAngle K = π / 2 := by
  unfold cuspoidAngle; field_simp

lemma s36a_exp_angle_pow (K : ℕ) : exp ((cuspoidAngle K : ℂ) * I) ^ (K + 2) = I := by
  rw [← exp_nat_mul]
  have : ((K + 2 : ℕ) : ℂ) * ((cuspoidAngle K : ℂ) * I) = (π / 2 : ℝ) * I := by
    rw [← s36a_angle_mul]; push_cast; ring
  rw [this]; push_cast; exact exp_pi_div_two_mul_I

lemma s36a_exp_neg_angle_pow (K : ℕ) : exp (-(cuspoidAngle K : ℂ) * I) ^ (K + 2) = -I := by
  rw [← exp_nat_mul]
  have : ((K + 2 : ℕ) : ℂ) * (-(cuspoidAngle K : ℂ) * I) = -(π : ℂ) / 2 * I := by
    have h := s36a_angle_mul K
    have h' : ((K : ℂ) + 2) * (cuspoidAngle K : ℂ) = (π : ℂ) / 2 := by exact_mod_cast h
    push_cast; linear_combination (-I) * h'
  rw [this]; exact exp_neg_pi_div_two_mul_I

/-- The contour direction has modulus one. -/
theorem norm_cuspoidContourDir (K : ℕ) (r : ℝ) : ‖cuspoidContourDir K r‖ = 1 := by
  unfold cuspoidContourDir
  split_ifs
  · exact norm_exp_ofReal_mul_I _
  · rw [show -(cuspoidAngle K : ℂ) * I = ((-cuspoidAngle K : ℝ) : ℂ) * I by push_cast; ring]
    exact norm_exp_ofReal_mul_I _

theorem norm_cuspoidContour (K : ℕ) (r : ℝ) : ‖cuspoidContour K r‖ = |r| := by
  rw [cuspoidContour, norm_mul, norm_cuspoidContourDir, mul_one, norm_real, Real.norm_eq_abs]

/-- On the rotated contour, `t^{K+2} = i |r|^{K+2}`. -/
theorem cuspoidContour_pow (K : ℕ) (r : ℝ) :
    cuspoidContour K r ^ (K + 2) = I * ((|r| ^ (K + 2) : ℝ) : ℂ) := by
  unfold cuspoidContour cuspoidContourDir
  split_ifs with h
  · rw [mul_pow, s36a_exp_angle_pow]
    have : (r : ℂ) ^ (K + 2) = ((|r| ^ (K + 2) : ℝ) : ℂ) := by
      rcases h with h | h
      · rw [abs_of_nonneg h]; push_cast; ring
      · have he : Even (K + 2) := h.add even_two
        rw [he.pow_abs]; push_cast; ring
    rw [this]; ring
  · push Not at h
    rw [mul_pow, s36a_exp_neg_angle_pow]
    have ho : Odd (K + 2) := (Nat.not_even_iff_odd.mp h.2).add_even even_two
    have : (r : ℂ) ^ (K + 2) = -((|r| ^ (K + 2) : ℝ) : ℂ) := by
      rw [abs_of_neg h.1, ho.neg_pow]; push_cast; ring
    rw [this]; ring

theorem measurable_cuspoidContourDir (K : ℕ) : Measurable (cuspoidContourDir K) := by
  unfold cuspoidContourDir
  exact Measurable.ite ((measurableSet_le measurable_const measurable_id).union
    (MeasurableSet.const _)) measurable_const measurable_const

theorem measurable_cuspoidContour (K : ℕ) : Measurable (cuspoidContour K) :=
  measurable_ofReal.mul (measurable_cuspoidContourDir K)

theorem continuous_cuspoidPotential (K : ℕ) (x : Fin K → ℝ) :
    Continuous fun t => cuspoidPotential K t x := by
  unfold cuspoidPotential; fun_prop

lemma s36a_pow_le_one_add (a : ℝ) (ha : 0 ≤ a) {j K : ℕ} (hj : j ≤ K) : a ^ j ≤ 1 + a ^ K := by
  rcases le_total a 1 with h | h
  · have := pow_le_one₀ ha h (n := j); have := pow_nonneg ha K; linarith
  · have := pow_le_pow_right₀ h hj; linarith

/-- Lower bound for `Im Φ_K` on the rotated contour. -/
theorem s36a_im_potential_ge (K : ℕ) (x : Fin K → ℝ) (r : ℝ) :
    |r| ^ (K + 2) - (∑ m, |x m|) * (1 + |r| ^ K) ≤
      (cuspoidPotential K (cuspoidContour K r) x).im := by
  rw [cuspoidPotential, add_im, cuspoidContour_pow, im_sum]
  have him : (I * ((|r| ^ (K + 2) : ℝ) : ℂ)).im = |r| ^ (K + 2) := by
    rw [I_mul_im, ofReal_re]
  rw [him]
  have hterm : ∀ m : Fin K, -(|x m| * (1 + |r| ^ K)) ≤
      (((x m : ℝ) : ℂ) * cuspoidContour K r ^ ((m : ℕ) + 1)).im := by
    intro m
    have h1 := neg_abs_le (((x m : ℝ) : ℂ) * cuspoidContour K r ^ ((m : ℕ) + 1)).im
    have h2 := abs_im_le_norm (((x m : ℝ) : ℂ) * cuspoidContour K r ^ ((m : ℕ) + 1))
    rw [norm_mul, norm_pow, norm_cuspoidContour, norm_real, Real.norm_eq_abs] at h2
    have h3 := s36a_pow_le_one_add |r| (abs_nonneg r) (show (m : ℕ) + 1 ≤ K from m.isLt)
    have h4 : |x m| * |r| ^ ((m : ℕ) + 1) ≤ |x m| * (1 + |r| ^ K) :=
      mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
    linarith
  have := Finset.sum_le_sum (fun m (_ : m ∈ Finset.univ) => hterm m)
  rw [Finset.sum_neg_distrib, ← Finset.sum_mul] at this
  linarith

/-- Elementary bound: `C a^K ≤ a^{K+2}/2 + C (1 + 2C)^K` for `a, C ≥ 0`. -/
theorem s36a_young (K : ℕ) {a C : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ C) :
    C * a ^ K ≤ a ^ (K + 2) / 2 + C * (1 + 2 * C) ^ K := by
  have hp : 0 ≤ C * (1 + 2 * C) ^ K := mul_nonneg hC (pow_nonneg (by linarith) K)
  rcases le_or_gt (2 * C) (a ^ 2) with h | h
  · have hk := pow_nonneg ha K
    have : C * a ^ K ≤ a ^ (K + 2) / 2 := by
      rw [pow_add]; nlinarith
    linarith
  · have ha' : a ≤ 1 + 2 * C := by nlinarith
    have := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha ha' K) hC
    have := pow_nonneg ha (K + 2)
    linarith

theorem s36a_pow_ge_sq_sub_one (K : ℕ) {a : ℝ} (ha : 0 ≤ a) : a ^ 2 - 1 ≤ a ^ (K + 2) := by
  rcases le_total a 1 with h | h
  · nlinarith [pow_nonneg ha (K + 2)]
  · have := pow_le_pow_right₀ h (show 2 ≤ K + 2 by omega); linarith

/-- Gaussian bound for the rotated-contour integrand with phase `κ > 0`. -/
theorem s36a_norm_integrand_le (K : ℕ) (x : Fin K → ℝ) {κ : ℝ} (hκ : 0 < κ) (r : ℝ) :
    ‖cuspoidContourDir K r * exp (I * κ * cuspoidPotential K (cuspoidContour K r) x)‖ ≤
      Real.exp (κ * (1 / 2 + (∑ m, |x m|) + (∑ m, |x m|) * (1 + 2 * ∑ m, |x m|) ^ K)) *
        Real.exp (-(κ / 2) * r ^ 2) := by
  set C := ∑ m, |x m|
  have hC : 0 ≤ C := Finset.sum_nonneg fun m _ => abs_nonneg _
  rw [norm_mul, norm_cuspoidContourDir, one_mul, norm_exp, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hre : (I * κ * cuspoidPotential K (cuspoidContour K r) x).re =
      -κ * (cuspoidPotential K (cuspoidContour K r) x).im := by
    simp [mul_re, mul_im]
  rw [hre]
  have h1 := s36a_im_potential_ge K x r
  have h2 := s36a_young K (abs_nonneg r) hC
  have h3 := s36a_pow_ge_sq_sub_one K (abs_nonneg r)
  rw [sq_abs] at h3
  have key : (r ^ 2 - 1) / 2 - C - C * (1 + 2 * C) ^ K ≤
      (cuspoidPotential K (cuspoidContour K r) x).im := by
    rw [mul_add, mul_one] at h1; linarith
  nlinarith [mul_le_mul_of_nonneg_left key hκ.le]

lemma s36a_measurable_integrand (K : ℕ) (x : Fin K → ℝ) (κ : ℂ) :
    Measurable fun r : ℝ =>
      cuspoidContourDir K r * exp (I * κ * cuspoidPotential K (cuspoidContour K r) x) :=
  (measurable_cuspoidContourDir K).mul (measurable_exp.comp (measurable_const.mul
    ((continuous_cuspoidPotential K x).measurable.comp (measurable_cuspoidContour K))))

/-- The rotated-contour integrand of `cuspoidIntegral` and `cuspoidDiffraction` (phase `κ > 0`)
is integrable on `ℝ`. -/
theorem integrable_cuspoidIntegrand (K : ℕ) (x : Fin K → ℝ) {κ : ℝ} (hκ : 0 < κ) :
    Integrable fun r : ℝ =>
      cuspoidContourDir K r * exp (I * κ * cuspoidPotential K (cuspoidContour K r) x) :=
  Integrable.mono' ((integrable_exp_neg_mul_sq (half_pos hκ)).const_mul _)
    (s36a_measurable_integrand K x κ).aestronglyMeasurable
    (ae_of_all _ (s36a_norm_integrand_le K x hκ))

/-- The integrand of `cuspoidIntegral` is integrable on `ℝ`. -/
theorem integrable_cuspoidIntegral_integrand (K : ℕ) (x : Fin K → ℝ) :
    Integrable fun r : ℝ =>
      cuspoidContourDir K r * exp (I * cuspoidPotential K (cuspoidContour K r) x) := by
  simpa using integrable_cuspoidIntegrand K x one_pos

theorem s36a_dir_of_even {K : ℕ} (hK : Even K) (r : ℝ) :
    cuspoidContourDir K r = exp ((cuspoidAngle K : ℂ) * I) := by
  simp [cuspoidContourDir, hK]

theorem s36a_dir_of_nonneg (K : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    cuspoidContourDir K r = exp ((cuspoidAngle K : ℂ) * I) := by
  simp [cuspoidContourDir, hr]

theorem s36a_dir_of_odd_neg {K : ℕ} (hK : ¬ Even K) {r : ℝ} (hr : r < 0) :
    cuspoidContourDir K r = exp (-(cuspoidAngle K : ℂ) * I) := by
  simp [cuspoidContourDir, hK, not_le.mpr hr]

/-! ### Special cases (§36.2(ii)) -/

/-- `Ψ₀ = √π e^{iπ/4}` (DLMF 36.2.12): the Fresnel integral `∫ exp(it²) dt`. -/
@[dlmf 36.2.E12]
theorem cuspoidIntegral_zero_dim (x : Fin 0 → ℝ) :
    cuspoidIntegral 0 x = (Real.sqrt π : ℂ) * exp (I * π / 4) := by
  have hθ : (cuspoidAngle 0 : ℂ) * I = I * π / 4 := by
    unfold cuspoidAngle; push_cast; ring
  have hint : ∀ r : ℝ, cuspoidContourDir 0 r *
      exp (I * cuspoidPotential 0 (cuspoidContour 0 r) x) =
      exp (I * π / 4) * ((Real.exp (-1 * r ^ 2) : ℝ) : ℂ) := by
    intro r
    rw [cuspoidPotential, Finset.univ_eq_empty, Finset.sum_empty, add_zero, cuspoidContour_pow,
      s36a_dir_of_even (by decide : Even 0), hθ, ofReal_exp]
    congr 2
    rw [← mul_assoc, I_mul_I, sq_abs]; push_cast; ring
  unfold cuspoidIntegral
  simp_rw [hint]
  rw [integral_const_mul, integral_complex_ofReal, integral_gaussian, div_one, mul_comm]

theorem s36a_integral_exp_neg_pow (n : ℕ) (hn : 0 < n) :
    ∫ r in Ioi (0 : ℝ), Real.exp (-r ^ n) = Real.Gamma (1 / n + 1) := by
  rw [← integral_exp_neg_rpow (by exact_mod_cast hn : (0 : ℝ) < n)]
  refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
  simp [Real.rpow_natCast]

theorem s36a_dir_neg_one (K : ℕ) : cuspoidContourDir K (-1) =
    if Even K then exp ((cuspoidAngle K : ℂ) * I) else exp (-(cuspoidAngle K : ℂ) * I) := by
  have h : ¬ (0 : ℝ) ≤ -1 := by norm_num
  by_cases hK : Even K <;> simp [cuspoidContourDir, h, hK]

theorem s36a_dir_neg {K : ℕ} {r : ℝ} (hr : r < 0) :
    cuspoidContourDir K r = cuspoidContourDir K (-1) := by
  rw [s36a_dir_neg_one]
  split_ifs with h
  · exact s36a_dir_of_even h r
  · exact s36a_dir_of_odd_neg h hr

/-- `Ψ_K(0) = (2/(K+2)) Γ(1/(K+2)) · (e^{iπ/(2(K+2))} or cos(π/(2(K+2))))` for `K` even or odd
(DLMF 36.2.15). -/
@[dlmf 36.2.E15]
theorem cuspoidIntegral_at_zero (K : ℕ) :
    cuspoidIntegral K 0 = 2 / ((K : ℂ) + 2) * (Real.Gamma (1 / ((K : ℝ) + 2)) : ℂ) *
      (if Even K then exp (I * (π / (2 * ((K : ℂ) + 2))))
        else (Real.cos (π / (2 * ((K : ℝ) + 2))) : ℂ)) := by
  set G : ℂ := (Real.Gamma (1 / ((K + 2 : ℕ) : ℝ) + 1) : ℂ) with hG
  have hf : ∀ r, cuspoidContourDir K r * exp (I * cuspoidPotential K (cuspoidContour K r) 0) =
      cuspoidContourDir K r * ((Real.exp (-|r| ^ (K + 2)) : ℝ) : ℂ) := by
    intro r; congr 1
    simp only [cuspoidPotential, Pi.zero_apply, ofReal_zero, zero_mul, Finset.sum_const_zero,
      add_zero, cuspoidContour_pow]
    rw [ofReal_exp, ← mul_assoc, I_mul_I]; push_cast; ring_nf
  have hint := integrable_cuspoidIntegral_integrand K 0
  unfold cuspoidIntegral
  rw [← intervalIntegral.integral_Iic_add_Ioi hint.integrableOn hint.integrableOn (b := 0)]
  have hR : ∫ r in Ioi (0 : ℝ), cuspoidContourDir K r *
      exp (I * cuspoidPotential K (cuspoidContour K r) 0) =
      exp ((cuspoidAngle K : ℂ) * I) * G := by
    rw [hG, ← s36a_integral_exp_neg_pow (K + 2) (by omega), ← integral_complex_ofReal,
      ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun r (hr : 0 < r) => ?_
    rw [hf, s36a_dir_of_nonneg K hr.le, abs_of_pos hr]
  have hL : ∫ r in Iic (0 : ℝ), cuspoidContourDir K r *
      exp (I * cuspoidPotential K (cuspoidContour K r) 0) = cuspoidContourDir K (-1) * G := by
    have := integral_comp_neg_Ioi 0 (fun r => cuspoidContourDir K r *
      exp (I * cuspoidPotential K (cuspoidContour K r) 0))
    rw [neg_zero] at this
    rw [← this, hG, ← s36a_integral_exp_neg_pow (K + 2) (by omega), ← integral_complex_ofReal,
      ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun r (hr : 0 < r) => ?_
    rw [hf, s36a_dir_neg (neg_neg_of_pos hr), abs_neg, abs_of_pos hr]
  rw [hL, hR]
  have hGa : G = 1 / ((K : ℂ) + 2) * (Real.Gamma (1 / ((K : ℝ) + 2)) : ℂ) := by
    rw [hG, Real.Gamma_add_one (by positivity)]; push_cast; ring
  have hθ : (cuspoidAngle K : ℂ) = π / (2 * ((K : ℂ) + 2)) := by
    unfold cuspoidAngle; push_cast; ring
  rw [hGa, s36a_dir_neg_one]
  split_ifs with h
  · rw [hθ]; ring_nf
  · rw [ofReal_cos, Complex.cos, hθ]; push_cast; ring_nf

/-! ### Symmetries (§36.2(iii)) -/

theorem conj_cuspoidPotential (K : ℕ) (t : ℂ) (x : Fin K → ℝ) :
    conj (cuspoidPotential K t x) = cuspoidPotential K (conj t) x := by
  simp [cuspoidPotential, map_sum, conj_ofReal]

lemma s36a_potential_neg_even {K : ℕ} (hK : Even K) (t : ℂ) (x : Fin K → ℝ) :
    cuspoidPotential K (-t) x = cuspoidPotential K t (fun m => (-1) ^ ((m : ℕ) + 1) * x m) := by
  unfold cuspoidPotential
  rw [(hK.add even_two).neg_pow]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [neg_pow]; push_cast; ring

lemma s36a_potential_neg_odd {K : ℕ} (hK : ¬ Even K) (t : ℂ) (x : Fin K → ℝ) :
    cuspoidPotential K (-t) x = -cuspoidPotential K t (fun m => (-1) ^ (m : ℕ) * x m) := by
  unfold cuspoidPotential
  rw [((Nat.not_even_iff_odd.mp hK).add_even even_two).neg_pow, neg_add, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [neg_pow, pow_succ]; push_cast; ring

/-- `Ψ_{2K}(x') = Ψ_{2K}(x)` with `x'_{2m+1} = -x_{2m+1}`, `x'_{2m} = x_{2m}` (DLMF 36.2.22); in the
Lean indexing `x m = x_{m+1}`, the parameter `x m` is multiplied by `(-1)^{m+1}`. Stated for every
even `K`. -/
@[dlmf 36.2.E22]
theorem cuspoidIntegral_even_symm {K : ℕ} (hK : Even K) (x : Fin K → ℝ) :
    cuspoidIntegral K (fun m => (-1) ^ ((m : ℕ) + 1) * x m) = cuspoidIntegral K x := by
  unfold cuspoidIntegral
  rw [← integral_neg_eq_self (fun r => cuspoidContourDir K r *
    exp (I * cuspoidPotential K (cuspoidContour K r) x)) volume]
  congr 1; ext r
  simp only [cuspoidContour, s36a_dir_of_even hK, ofReal_neg, neg_mul]
  rw [s36a_potential_neg_even hK]

/-- `Ψ_{2K+1}(x') = conj Ψ_{2K+1}(x)` with `x'_{2m+1} = x_{2m+1}`, `x'_{2m} = -x_{2m}`
(DLMF 36.2.23); in the Lean indexing `x m` is multiplied by `(-1)^m`. Stated for every odd `K`. -/
@[dlmf 36.2.E23]
theorem cuspoidIntegral_odd_conj {K : ℕ} (hK : ¬ Even K) (x : Fin K → ℝ) :
    cuspoidIntegral K (fun m => (-1) ^ (m : ℕ) * x m) = conj (cuspoidIntegral K x) := by
  unfold cuspoidIntegral
  rw [← integral_conj, ← integral_neg_eq_self (fun r => conj (cuspoidContourDir K r *
    exp (I * cuspoidPotential K (cuspoidContour K r) x))) volume]
  refine integral_congr_ae ?_
  filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))] with r hr
  have hr0 : r ≠ 0 := hr
  have hd : conj (cuspoidContourDir K (-r)) = cuspoidContourDir K r := by
    rcases lt_or_gt_of_ne hr0 with h | h
    · rw [s36a_dir_of_nonneg K (by linarith), s36a_dir_of_odd_neg hK h, ← exp_conj]
      congr 1; simp [conj_ofReal]
    · rw [s36a_dir_of_odd_neg hK (by linarith), s36a_dir_of_nonneg K h.le, ← exp_conj]
      congr 1; simp [conj_ofReal]
  have hc : conj (cuspoidContour K (-r)) = -cuspoidContour K r := by
    rw [cuspoidContour, map_mul, conj_ofReal, hd, cuspoidContour]; push_cast; ring
  rw [map_mul, ← exp_conj, map_mul, conj_I, conj_cuspoidPotential, hd, hc,
    s36a_potential_neg_odd hK]
  ring_nf

/-! ### The fold: `Ψ₁` and the Airy function -/

lemma s36a_airy_ray (x : ℝ) :
    ∫ r in Ioi (0 : ℝ), exp (((π / 6 : ℝ) : ℂ) * I) *
      DLMF.Airy.airyInt_osc x (r * exp (((π / 6 : ℝ) : ℂ) * I)) = I * DLMF.Airy.airyInt_w x := by
  rw [DLMF.Airy.airyInt_w, DLMF.Airy.rayIntegral, ← integral_const_mul]
  exact setIntegral_congr_fun measurableSet_Ioi fun r _ => DLMF.Airy.airyInt_osc_rotate x r

lemma s36a_flip_one (x : ℝ) : (fun m : Fin 1 => (-1 : ℝ) ^ (m : ℕ) * ![x] m) = ![x] := by
  funext m; rw [Fin.fin_one_eq_zero m]; simp

/-- For odd `K` and `r > 0`, the integrand at `-r` is the conjugate of the integrand at `r` with
the parameters `x'_m = (-1)^m x_m`. -/
lemma s36a_integrand_neg_odd {K : ℕ} (hK : ¬ Even K) (x : Fin K → ℝ) {r : ℝ} (hr : 0 < r) :
    cuspoidContourDir K (-r) * exp (I * cuspoidPotential K (cuspoidContour K (-r)) x) =
      conj (cuspoidContourDir K r *
        exp (I * cuspoidPotential K (cuspoidContour K r) (fun m => (-1) ^ (m : ℕ) * x m))) := by
  have hd : conj (cuspoidContourDir K r) = cuspoidContourDir K (-r) := by
    rw [s36a_dir_of_nonneg K hr.le, s36a_dir_of_odd_neg hK (by linarith), ← exp_conj]
    congr 1; simp [conj_ofReal]
  have hc : cuspoidContour K (-r) = -conj (cuspoidContour K r) := by
    simp only [cuspoidContour, map_mul, conj_ofReal, hd]; push_cast; ring
  rw [map_mul, ← exp_conj, map_mul, conj_I, conj_cuspoidPotential, hd, hc,
    s36a_potential_neg_odd hK, mul_neg, neg_mul]

/-- `Ψ₁(x) = (2π/3^{1/3}) Ai(x/3^{1/3})` (DLMF 36.2.13): the fold canonical integral is an Airy
function. -/
@[dlmf 36.2.E13]
theorem cuspoidIntegral_one (x : ℝ) :
    cuspoidIntegral 1 ![x] = 2 * π / (((3 : ℝ) ^ (1 / 3 : ℝ) : ℝ) : ℂ) *
      DLMF.Airy.airyAi ((x / (3 : ℝ) ^ (1 / 3 : ℝ) : ℝ) : ℂ) := by
  set a : ℝ := (3 : ℝ) ^ (1 / 3 : ℝ) with ha_def
  have ha : 0 < a := by positivity
  have ha3 : (a : ℂ) ^ 3 = 3 := by
    have : a ^ 3 = 3 := by
      rw [ha_def, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    exact_mod_cast this
  have ha0 : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha.ne'
  set u : ℂ := exp (((π / 6 : ℝ) : ℂ) * I) with hu
  have hθ : (cuspoidAngle 1 : ℂ) = ((π / 6 : ℝ) : ℂ) := by
    unfold cuspoidAngle; push_cast; ring
  have hint := integrable_cuspoidIntegral_integrand 1 ![x]
  set f := fun r : ℝ =>
    cuspoidContourDir 1 r * exp (I * cuspoidPotential 1 (cuspoidContour 1 r) ![x]) with hf
  have hR : ∫ r in Ioi (0 : ℝ), f r = (a⁻¹ : ℝ) * (I * DLMF.Airy.airyInt_w (x / a)) := by
    have h1 : ∀ r ∈ Ioi (0 : ℝ),
        f r = (fun ρ : ℝ => u * DLMF.Airy.airyInt_osc (x / a) (ρ * u)) (a * r) := by
      intro r hr
      simp only [hf, cuspoidContour, s36a_dir_of_nonneg 1 (le_of_lt hr), hθ, cuspoidPotential,
        DLMF.Airy.airyInt_osc, Fin.sum_univ_one]
      congr 2
      simp only [Matrix.cons_val_fin_one, Fin.val_zero, zero_add, pow_one]
      rw [ofReal_div x a, ofReal_mul, ← hu]
      field_simp
      linear_combination (-(r : ℂ) ^ 3 * u ^ 3) * ha3
    rw [setIntegral_congr_fun measurableSet_Ioi h1]
    rw [integral_comp_mul_left_Ioi (fun ρ : ℝ => u * DLMF.Airy.airyInt_osc (x / a) (ρ * u)) 0 ha,
      mul_zero, s36a_airy_ray, Complex.real_smul]
  have hL : ∫ r in Iic (0 : ℝ), f r = conj (∫ r in Ioi (0 : ℝ), f r) := by
    have := integral_comp_neg_Ioi 0 f
    rw [neg_zero] at this
    rw [← this, ← integral_conj]
    refine setIntegral_congr_fun measurableSet_Ioi fun r (hr : 0 < r) => ?_
    have := s36a_integrand_neg_odd (K := 1) (by decide) ![x] hr
    rw [s36a_flip_one] at this
    exact this
  unfold cuspoidIntegral
  rw [← intervalIntegral.integral_Iic_add_Ioi hint.integrableOn hint.integrableOn (b := 0),
    ← hf, hL, hR]
  have hpi := DLMF.Airy.airyInt_pi_airyAi (x / a)
  have hAi : DLMF.Airy.airyAi ((x / a : ℝ) : ℂ) =
      (((-(DLMF.Airy.airyInt_w (x / a)).im : ℝ) : ℂ)) / π := by
    rw [← hpi]; field_simp
  rw [hAi]
  apply Complex.ext <;> simp [map_mul, conj_ofReal]
  field_simp
  ring

/-! ### The hyperbolic umbilic -/

lemma s36a_conj_dir_neg {K : ℕ} (hK : ¬ Even K) {r : ℝ} (hr : r ≠ 0) :
    conj (cuspoidContourDir K (-r)) = cuspoidContourDir K r := by
  rcases lt_or_gt_of_ne hr with h | h
  · rw [s36a_dir_of_nonneg K (by linarith), s36a_dir_of_odd_neg hK h, ← exp_conj]
    congr 1; simp [conj_ofReal]
  · rw [s36a_dir_of_odd_neg hK (by linarith), s36a_dir_of_nonneg K h.le, ← exp_conj]
    congr 1; simp [conj_ofReal]

lemma s36a_conj_contour_neg {K : ℕ} (hK : ¬ Even K) {r : ℝ} (hr : r ≠ 0) :
    conj (cuspoidContour K (-r)) = -cuspoidContour K r := by
  simp only [cuspoidContour, map_mul, conj_ofReal, s36a_conj_dir_neg hK hr]; push_cast; ring

lemma s36a_ae_ne_zero_prod : ∀ᵐ p : ℝ × ℝ ∂volume, p.1 ≠ 0 ∧ p.2 ≠ 0 := by
  rw [Measure.volume_eq_prod]
  have h0 : ∀ᵐ r : ℝ ∂volume, r ≠ 0 := compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae h0,
    Measure.quasiMeasurePreserving_snd.ae h0] with p h1 h2
  exact ⟨h1, h2⟩

/-- At `z = 0` the hyperbolic umbilic integral factorizes: `Ψ^{(H)}(x, y, 0) = Ψ₁(x) Ψ₁(y)`. -/
theorem hyperbolicUmbilicIntegral_z_zero_eq (x y : ℝ) :
    hyperbolicUmbilicIntegral x y 0 = cuspoidIntegral 1 ![x] * cuspoidIntegral 1 ![y] := by
  unfold hyperbolicUmbilicIntegral cuspoidIntegral
  rw [Measure.volume_eq_prod, ← integral_prod_mul]
  congr 1; ext p
  simp only [hyperbolicUmbilicPotential, cuspoidPotential, Fin.sum_univ_one,
    Matrix.cons_val_fin_one, Fin.val_zero, zero_add, pow_one, ofReal_zero, zero_mul, add_zero]
  rw [mul_mul_mul_comm, ← exp_add]
  congr 2; ring

/-- `Ψ^{(H)}(x, y, 0) = (4π²/3^{2/3}) Ai(x/3^{1/3}) Ai(y/3^{1/3})` (DLMF 36.2.21). -/
@[dlmf 36.2.E21]
theorem hyperbolicUmbilicIntegral_z_zero (x y : ℝ) :
    hyperbolicUmbilicIntegral x y 0 = 4 * π ^ 2 / (((3 : ℝ) ^ (2 / 3 : ℝ) : ℝ) : ℂ) *
      DLMF.Airy.airyAi ((x / (3 : ℝ) ^ (1 / 3 : ℝ) : ℝ) : ℂ) *
      DLMF.Airy.airyAi ((y / (3 : ℝ) ^ (1 / 3 : ℝ) : ℝ) : ℂ) := by
  rw [hyperbolicUmbilicIntegral_z_zero_eq, cuspoidIntegral_one, cuspoidIntegral_one]
  have h : ((3 : ℝ) ^ (2 / 3 : ℝ)) = ((3 : ℝ) ^ (1 / 3 : ℝ)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  have h0 : ((3 : ℝ) ^ (1 / 3 : ℝ)) ≠ 0 := by positivity
  rw [h]; push_cast; field_simp; ring

/-- `Ψ^{(H)}(0) = Γ(1/3)²/3` (DLMF 36.2.18; the decimal value 2.39224 is not acquired). -/
@[dlmf 36.2.E18]
theorem hyperbolicUmbilicIntegral_zero :
    hyperbolicUmbilicIntegral 0 0 0 = (Real.Gamma (1 / 3) : ℂ) ^ 2 / 3 := by
  have h0 : (![(0 : ℝ)] : Fin 1 → ℝ) = 0 := by funext m; simp
  rw [hyperbolicUmbilicIntegral_z_zero_eq, h0, cuspoidIntegral_at_zero]
  have hc : Real.cos (π / (2 * (((1 : ℕ) : ℝ) + 2))) = Real.sqrt 3 / 2 := by
    rw [show π / (2 * (((1 : ℕ) : ℝ) + 2)) = π / 6 by push_cast; ring, Real.cos_pi_div_six]
  have hg : Real.Gamma (1 / (((1 : ℕ) : ℝ) + 2)) = Real.Gamma (1 / 3) := by norm_num
  simp only [show ¬ Even 1 by decide, ite_false, hc, hg]
  have h3 : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
    rw [← ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  push_cast
  linear_combination (Real.Gamma (1 / 3) : ℂ) ^ 2 / 9 * h3

/-- `Ψ^{(H)}(x, y, z) = conj Ψ^{(H)}(x, y, -z)` (DLMF 36.2.24, `U = H`). -/
@[dlmf 36.2.E24]
theorem hyperbolicUmbilicIntegral_conj (x y z : ℝ) :
    hyperbolicUmbilicIntegral x y z = conj (hyperbolicUmbilicIntegral x y (-z)) := by
  unfold hyperbolicUmbilicIntegral
  rw [← integral_conj, ← integral_neg_eq_self (fun p : ℝ × ℝ => conj (cuspoidContourDir 1 p.1 *
    cuspoidContourDir 1 p.2 * exp (I * hyperbolicUmbilicPotential (cuspoidContour 1 p.1)
      (cuspoidContour 1 p.2) x y (-z)))) volume]
  refine integral_congr_ae ?_
  filter_upwards [s36a_ae_ne_zero_prod] with p hp
  have hK : ¬ Even 1 := by decide
  simp only [Prod.fst_neg, Prod.snd_neg, map_mul, ← exp_conj, conj_I,
    s36a_conj_dir_neg hK hp.1, s36a_conj_dir_neg hK hp.2]
  congr 2
  simp only [hyperbolicUmbilicPotential, map_add, map_mul, map_pow, conj_ofReal,
    s36a_conj_contour_neg hK hp.1, s36a_conj_contour_neg hK hp.2]
  push_cast; ring

/-- `Ψ^{(H)}(x, y, z) = Ψ^{(H)}(y, x, z)` (DLMF 36.2.27). -/
@[dlmf 36.2.E27]
theorem hyperbolicUmbilicIntegral_swap (x y z : ℝ) :
    hyperbolicUmbilicIntegral x y z = hyperbolicUmbilicIntegral y x z := by
  unfold hyperbolicUmbilicIntegral
  rw [Measure.volume_eq_prod, ← integral_prod_swap]
  congr 1; ext p
  simp only [Prod.fst_swap, Prod.snd_swap, hyperbolicUmbilicPotential]
  rw [mul_comm (cuspoidContourDir 1 p.2)]
  congr 3; ring

/-! ### The elliptic umbilic -/

/-- The elliptic umbilic potential in the coordinates `a = s + it`, `b = s - it`. -/
theorem ellipticUmbilicPotentialAB_eq (a b : ℂ) (x y z : ℝ) :
    ellipticUmbilicPotentialAB a b x y z =
      (a ^ 3 + b ^ 3) / 2 + z * a * b + (x - I * y) / 2 * a + (x + I * y) / 2 * b := by
  unfold ellipticUmbilicPotentialAB ellipticUmbilicPotential
  have hI : (2 * I)⁻¹ = -I / 2 := by rw [mul_inv, inv_I]; ring
  simp only [div_eq_mul_inv (a - b), hI]
  ring_nf
  simp only [I_sq]
  ring

lemma s36a_rayDir_eq (j : Fin 3) : ellipticUmbilicRayDir j =
    ![(Real.sqrt 3 / 2 : ℝ) + I / 2, -(Real.sqrt 3 / 2 : ℝ) + I / 2, -I] j := by
  fin_cases j
  · simp only [ellipticUmbilicRayDir, Fin.zero_eta, Nat.cast_zero, mul_zero,
      zero_div, add_zero, exp_mul_I, ← ofReal_cos, ← ofReal_sin, Real.cos_pi_div_six,
      Real.sin_pi_div_six, Matrix.cons_val_zero]
    push_cast; ring
  · simp only [ellipticUmbilicRayDir, Fin.mk_one, Nat.cast_one, exp_mul_I,
      ← ofReal_cos, ← ofReal_sin, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [show π / 6 + 2 * π * 1 / 3 = π - π / 6 by ring, Real.cos_pi_sub, Real.sin_pi_sub,
      Real.cos_pi_div_six, Real.sin_pi_div_six]
    push_cast; ring
  · simp only [ellipticUmbilicRayDir, exp_mul_I, ← ofReal_cos, ← ofReal_sin]
    rw [show π / 6 + 2 * π * ((2 : ℕ) : ℝ) / 3 = π / 2 + π by push_cast; ring, Real.cos_add_pi,
      Real.sin_add_pi, Real.cos_pi_div_two, Real.sin_pi_div_two]
    simp

lemma s36a_rayDir_eq' (j : Fin 3) : ellipticUmbilicRayDir j =
    ![(Real.sqrt 3 : ℂ) / 2 + I / 2, -(Real.sqrt 3 : ℂ) / 2 + I / 2, -I] j := by
  rw [s36a_rayDir_eq]; fin_cases j <;> simp; ring

lemma s36a_sqrt3_sq : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
  rw [← ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num

lemma s36a_cycle_symm (j k : Fin 3) : ellipticUmbilicCycle j k = ellipticUmbilicCycle k j := by
  fin_cases j <;> fin_cases k <;> rfl

/-- Swapping the ray factors `a ↔ b` corresponds to `y ↦ -y`. -/
lemma s36a_quadrant_swap (κ x y z : ℝ) (j k : Fin 3) :
    ellipticUmbilicQuadrant κ x (-y) z j k = ellipticUmbilicQuadrant κ x y z k j := by
  unfold ellipticUmbilicQuadrant
  rw [Measure.volume_eq_prod]
  conv_rhs => rw [← setIntegral_prod_swap]
  congr 1; ext p
  simp only [Prod.fst_swap, Prod.snd_swap, ellipticUmbilicPotentialAB_eq]
  rw [mul_comm (ellipticUmbilicRayDir k)]
  congr 3; push_cast; ring

/-- `Ψ^{(E)}(x, -y, z) = Ψ^{(E)}(x, y, z)` (DLMF 36.2.25). -/
@[dlmf 36.2.E25]
theorem ellipticUmbilicIntegral_neg_y (x y z : ℝ) :
    ellipticUmbilicIntegral x (-y) z = ellipticUmbilicIntegral x y z := by
  unfold ellipticUmbilicIntegral
  simp only [s36a_quadrant_swap]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [s36a_cycle_symm]

/-- A rotation of the `(a, b)` coordinates permuting the rays. -/
lemma s36a_quadrant_rot {κ x y z x' y' : ℝ} {ω ω' : ℂ} (hωω : ω * ω' = 1)
    (hΦ : ∀ a b, ellipticUmbilicPotentialAB a b x' y' z =
      ellipticUmbilicPotentialAB (ω * a) (ω' * b) x y z)
    {j k j' k' : Fin 3} (hj : ω * ellipticUmbilicRayDir j = ellipticUmbilicRayDir j')
    (hk : ω' * ellipticUmbilicRayDir k = ellipticUmbilicRayDir k') :
    ellipticUmbilicQuadrant κ x' y' z j k = ellipticUmbilicQuadrant κ x y z j' k' := by
  unfold ellipticUmbilicQuadrant
  congr 1; ext p
  rw [hΦ, ← hj, ← hk]
  congr 1
  · linear_combination (-(ellipticUmbilicRayDir j * ellipticUmbilicRayDir k)) * hωω
  · congr 3 <;> ring

/-- Invariance under rotation by `∓2π/3` in the `(x, y)` plane (DLMF 36.2.26): the first
component is the upper signs, the second the lower signs. -/
@[dlmf 36.2.E26]
theorem ellipticUmbilicIntegral_rotate (x y z : ℝ) :
    ellipticUmbilicIntegral (-x / 2 - Real.sqrt 3 / 2 * y) (Real.sqrt 3 / 2 * x - y / 2) z =
        ellipticUmbilicIntegral x y z ∧
      ellipticUmbilicIntegral (-x / 2 + Real.sqrt 3 / 2 * y) (-(Real.sqrt 3 / 2) * x - y / 2) z =
        ellipticUmbilicIntegral x y z := by
  have hs := s36a_sqrt3_sq
  set s : ℂ := ((Real.sqrt 3 : ℝ) : ℂ) with hs_def
  have hd := s36a_rayDir_eq'
  constructor
  · have hωω : (-1 / 2 - I * s / 2) * (-1 / 2 + I * s / 2) = 1 := by
      linear_combination (-I ^ 2 / 4) * hs + (-3 / 4) * I_sq
    have hΦ : ∀ a b, ellipticUmbilicPotentialAB a b (-x / 2 - Real.sqrt 3 / 2 * y)
        (Real.sqrt 3 / 2 * x - y / 2) z = ellipticUmbilicPotentialAB
          ((-1 / 2 - I * s / 2) * a) ((-1 / 2 + I * s / 2) * b) x y z := by
      intro a b
      rw [ellipticUmbilicPotentialAB_eq, ellipticUmbilicPotentialAB_eq]
      push_cast
      rw [← hs_def]
      linear_combination (-(a ^ 3) / 2) * ((-I ^ 3 * s / 8 - 3 * I ^ 2 / 8) * hs +
        (-3 * I * s / 8 - 9 / 8) * I_sq) + (-(b ^ 3) / 2) * ((I ^ 3 * s / 8 - 3 * I ^ 2 / 8) * hs
        + (3 * I * s / 8 - 9 / 8) * I_sq) + (-(z : ℂ) * a * b) * hωω +
        (-a * s * y / 4 - b * s * y / 4) * I_sq
    have hj : ∀ j, (-1 / 2 - I * s / 2) * ellipticUmbilicRayDir j =
        ellipticUmbilicRayDir (![2, 0, 1] j) := by
      intro j; fin_cases j <;> simp only [hd] <;> simp
      · linear_combination (-I / 4) * hs + (-s / 4) * I_sq
      · linear_combination (I / 4) * hs + (-s / 4) * I_sq
      · linear_combination (s / 2) * I_sq
    have hk : ∀ k, (-1 / 2 + I * s / 2) * ellipticUmbilicRayDir k =
        ellipticUmbilicRayDir (![1, 2, 0] k) := by
      intro k; fin_cases k <;> simp only [hd] <;> simp
      · linear_combination (I / 4) * hs + (s / 4) * I_sq
      · linear_combination (-I / 4) * hs + (s / 4) * I_sq
      · linear_combination (-s / 2) * I_sq
    have hQ : ∀ j k, ellipticUmbilicQuadrant 1 (-x / 2 - Real.sqrt 3 / 2 * y)
        (Real.sqrt 3 / 2 * x - y / 2) z j k =
        ellipticUmbilicQuadrant 1 x y z (![2, 0, 1] j) (![1, 2, 0] k) :=
      fun j k => s36a_quadrant_rot hωω hΦ (hj j) (hk k)
    unfold ellipticUmbilicIntegral
    simp only [Fin.sum_univ_three, hQ]
    simp [ellipticUmbilicCycle]
    ring
  · have hωω : (-1 / 2 + I * s / 2) * (-1 / 2 - I * s / 2) = 1 := by
      linear_combination (-I ^ 2 / 4) * hs + (-3 / 4) * I_sq
    have hΦ : ∀ a b, ellipticUmbilicPotentialAB a b (-x / 2 + Real.sqrt 3 / 2 * y)
        (-(Real.sqrt 3 / 2) * x - y / 2) z = ellipticUmbilicPotentialAB
          ((-1 / 2 + I * s / 2) * a) ((-1 / 2 - I * s / 2) * b) x y z := by
      intro a b
      rw [ellipticUmbilicPotentialAB_eq, ellipticUmbilicPotentialAB_eq]
      push_cast
      rw [← hs_def]
      linear_combination (-(a ^ 3) / 2) * ((I ^ 3 * s / 8 - 3 * I ^ 2 / 8) * hs +
        (3 * I * s / 8 - 9 / 8) * I_sq) + (-(b ^ 3) / 2) * ((-I ^ 3 * s / 8 - 3 * I ^ 2 / 8) * hs
        + (-3 * I * s / 8 - 9 / 8) * I_sq) + (-(z : ℂ) * a * b) * hωω +
        (a * s * y / 4 + b * s * y / 4) * I_sq
    have hj : ∀ j, (-1 / 2 + I * s / 2) * ellipticUmbilicRayDir j =
        ellipticUmbilicRayDir (![1, 2, 0] j) := by
      intro j; fin_cases j <;> simp only [hd] <;> simp
      · linear_combination (I / 4) * hs + (s / 4) * I_sq
      · linear_combination (-I / 4) * hs + (s / 4) * I_sq
      · linear_combination (-s / 2) * I_sq
    have hk : ∀ k, (-1 / 2 - I * s / 2) * ellipticUmbilicRayDir k =
        ellipticUmbilicRayDir (![2, 0, 1] k) := by
      intro k; fin_cases k <;> simp only [hd] <;> simp
      · linear_combination (-I / 4) * hs + (-s / 4) * I_sq
      · linear_combination (I / 4) * hs + (-s / 4) * I_sq
      · linear_combination (s / 2) * I_sq
    have hQ : ∀ j k, ellipticUmbilicQuadrant 1 (-x / 2 + Real.sqrt 3 / 2 * y)
        (-(Real.sqrt 3 / 2) * x - y / 2) z j k =
        ellipticUmbilicQuadrant 1 x y z (![1, 2, 0] j) (![2, 0, 1] k) :=
      fun j k => s36a_quadrant_rot hωω hΦ (hj j) (hk k)
    unfold ellipticUmbilicIntegral
    simp only [Fin.sum_univ_three, hQ]
    simp [ellipticUmbilicCycle]
    ring

/-- Complex conjugation of a quadrant integral with `z ↦ -z`. -/
lemma s36a_quadrant_conj {κ x y z : ℝ} {j k j' k' : Fin 3}
    (hj : conj (ellipticUmbilicRayDir j) = -ellipticUmbilicRayDir j')
    (hk : conj (ellipticUmbilicRayDir k) = -ellipticUmbilicRayDir k') :
    conj (ellipticUmbilicQuadrant κ x y (-z) j k) = ellipticUmbilicQuadrant κ x y z k' j' := by
  unfold ellipticUmbilicQuadrant
  rw [← integral_conj, Measure.volume_eq_prod]
  conv_rhs => rw [← setIntegral_prod_swap]
  congr 1; ext p
  have h2 : conj (2 : ℂ) = 2 := map_ofNat _ 2
  simp only [Prod.fst_swap, Prod.snd_swap, ellipticUmbilicPotentialAB_eq, map_mul, ← exp_conj,
    map_add, map_div₀, map_pow, map_sub, conj_ofReal, conj_I, h2, hj, hk]
  congr 1
  · ring
  · congr 1; push_cast; ring

lemma s36a_conj_rayDir (j : Fin 3) :
    conj (ellipticUmbilicRayDir j) = -ellipticUmbilicRayDir (![1, 0, 2] j) := by
  have h2 : conj (2 : ℂ) = 2 := map_ofNat _ 2
  fin_cases j <;> simp [s36a_rayDir_eq', conj_ofReal, h2] <;> ring

/-- `Ψ^{(E)}(x, y, z) = conj Ψ^{(E)}(x, y, -z)` (DLMF 36.2.24, `U = E`). -/
@[dlmf 36.2.E24]
theorem ellipticUmbilicIntegral_conj (x y z : ℝ) :
    ellipticUmbilicIntegral x y z = conj (ellipticUmbilicIntegral x y (-z)) := by
  have hQ : ∀ j k, conj (ellipticUmbilicQuadrant 1 x y (-z) j k) =
      ellipticUmbilicQuadrant 1 x y z (![1, 0, 2] k) (![1, 0, 2] j) :=
    fun j k => s36a_quadrant_conj (s36a_conj_rayDir j) (s36a_conj_rayDir k)
  have h2 : conj (2 : ℂ) = 2 := map_ofNat _ 2
  unfold ellipticUmbilicIntegral
  simp only [map_mul, map_sum, map_intCast, conj_I, map_div₀, h2]
  simp only [hQ, Fin.sum_univ_three]
  simp [ellipticUmbilicCycle]
  ring

theorem s36a_rayDir_cube (j : Fin 3) : ellipticUmbilicRayDir j ^ 3 = I := by
  have hs := s36a_sqrt3_sq
  rw [s36a_rayDir_eq']
  fin_cases j <;> simp
  · linear_combination (3 * I / 8 + (Real.sqrt 3 : ℂ) / 8) * hs +
      (I / 8 + 3 * (Real.sqrt 3 : ℂ) / 8) * I_sq
  · linear_combination (3 * I / 8 - (Real.sqrt 3 : ℂ) / 8) * hs +
      (I / 8 - 3 * (Real.sqrt 3 : ℂ) / 8) * I_sq
  · linear_combination (-I) * I_sq

lemma s36a_ray_integral_zero (d : ℂ) (hd : d ^ 3 = I) :
    ∫ r in Ioi (0 : ℝ), d * exp (I * ((r * d) ^ 3 / 2)) =
      d * (((1 / 2 : ℝ) ^ (-1 / 3 : ℝ) * Real.Gamma (1 / 3 + 1) : ℝ) : ℂ) := by
  have h := _root_.integral_exp_neg_mul_rpow (p := 3) (b := 1 / 2) (by norm_num) (by norm_num)
  rw [← h, ← integral_complex_ofReal, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
  rw [mul_pow, hd, ofReal_exp]
  congr 2
  rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  push_cast
  linear_combination ((r : ℂ) ^ 3 / 2) * I_sq

/-- `√π Γ(1/6)/3 = (3√3/2)(2^{1/3} Γ(4/3))²`, from the duplication and reflection formulas. -/
lemma s36a_gamma_sixth : Real.sqrt π * Real.Gamma (1 / 6) / 3 =
    3 * Real.sqrt 3 / 2 * ((1 / 2 : ℝ) ^ (-1 / 3 : ℝ) * Real.Gamma (1 / 3 + 1)) ^ 2 := by
  have h1 := Real.Gamma_mul_Gamma_add_half (1 / 6)
  have h2 := Real.Gamma_mul_Gamma_one_sub (1 / 3)
  rw [show (1 : ℝ) / 6 + 1 / 2 = 2 / 3 by norm_num, show 2 * (1 / 6 : ℝ) = 1 / 3 by norm_num,
    show (1 : ℝ) - 1 / 3 = 2 / 3 by norm_num] at h1
  rw [show (1 : ℝ) - 1 / 3 = 2 / 3 by norm_num, show π * (1 / 3) = π / 3 by ring,
    Real.sin_pi_div_three] at h2
  have h3 : Real.Gamma (1 / 3 + 1) = 1 / 3 * Real.Gamma (1 / 3) := by
    rw [Real.Gamma_add_one (by norm_num)]
  have h4 : ((1 / 2 : ℝ) ^ (-1 / 3 : ℝ)) ^ 2 = (2 : ℝ) ^ (2 / 3 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), one_div,
      Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
    norm_num
  have hp : Real.sqrt π ^ 2 = π := Real.sq_sqrt Real.pi_pos.le
  have hr : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hp0 : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  have hr0 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hg2 : 0 < Real.Gamma (2 / 3) := Real.Gamma_pos_of_pos (by norm_num)
  rw [mul_pow, h4, h3]
  -- from h1, h2: Γ(1/6) · 2√π = Γ(1/3)² 2^{2/3} √3
  have h2' : Real.Gamma (1 / 3) * Real.Gamma (2 / 3) * Real.sqrt 3 = 2 * π := by
    rw [h2]; field_simp
  have key : Real.Gamma (1 / 6) * (2 * Real.sqrt π) =
      Real.Gamma (1 / 3) ^ 2 * (2 : ℝ) ^ (2 / 3 : ℝ) * Real.sqrt 3 := by
    have e2 : Real.Gamma (1 / 6) * (2 * Real.sqrt π) * Real.Gamma (2 / 3) =
        Real.Gamma (1 / 3) ^ 2 * (2 : ℝ) ^ (2 / 3 : ℝ) * Real.sqrt 3 * Real.Gamma (2 / 3) := by
      linear_combination (2 * Real.sqrt π) * h1 - (Real.Gamma (1 / 3) * (2 : ℝ) ^ (2 / 3 : ℝ)) * h2'
        + (2 * Real.Gamma (1 / 3) * (2 : ℝ) ^ (2 / 3 : ℝ)) * hp
    exact mul_right_cancel₀ hg2.ne' e2
  linear_combination key / 6

/-- `Ψ^{(E)}(0) = √π Γ(1/6)/3` (DLMF 36.2.18; the decimal value 3.28868 is not acquired). -/
@[dlmf 36.2.E18]
theorem ellipticUmbilicIntegral_zero :
    ellipticUmbilicIntegral 0 0 0 = ((Real.sqrt π * Real.Gamma (1 / 6) / 3 : ℝ) : ℂ) := by
  set C : ℂ := (((1 / 2 : ℝ) ^ (-1 / 3 : ℝ) * Real.Gamma (1 / 3 + 1) : ℝ) : ℂ) with hC
  have hQ : ∀ j k, ellipticUmbilicQuadrant 1 0 0 0 j k =
      ellipticUmbilicRayDir j * ellipticUmbilicRayDir k * C ^ 2 := by
    intro j k
    unfold ellipticUmbilicQuadrant
    set f : ℝ → ℂ := fun r : ℝ => ellipticUmbilicRayDir j *
      exp (I * ((r * ellipticUmbilicRayDir j) ^ 3 / 2)) with hf
    set g : ℝ → ℂ := fun q : ℝ => ellipticUmbilicRayDir k *
      exp (I * ((q * ellipticUmbilicRayDir k) ^ 3 / 2)) with hg
    have hfac : (fun p : ℝ × ℝ => ellipticUmbilicRayDir j * ellipticUmbilicRayDir k *
        exp (I * ((1 : ℝ) : ℂ) * ellipticUmbilicPotentialAB ((p.1 : ℂ) * ellipticUmbilicRayDir j)
          ((p.2 : ℂ) * ellipticUmbilicRayDir k) 0 0 0)) =
        fun p : ℝ × ℝ => f p.1 * g p.2 := by
      funext p
      simp only [hf, hg, ellipticUmbilicPotentialAB_eq, ofReal_zero, ofReal_one, zero_mul,
        mul_zero, sub_zero, add_zero, zero_div, mul_one]
      rw [mul_mul_mul_comm (ellipticUmbilicRayDir j), ← exp_add]
      congr 2; ring
    rw [hfac, Measure.volume_eq_prod, setIntegral_prod_mul f g, hf, hg,
      s36a_ray_integral_zero _ (s36a_rayDir_cube j),
      s36a_ray_integral_zero _ (s36a_rayDir_cube k), ← hC]
    ring
  unfold ellipticUmbilicIntegral
  simp only [hQ, Fin.sum_univ_three]
  rw [s36a_gamma_sixth]
  have hR : (((3 * Real.sqrt 3 / 2 * ((1 / 2 : ℝ) ^ (-1 / 3 : ℝ) *
      Real.Gamma (1 / 3 + 1)) ^ 2) : ℝ) : ℂ) = 3 * (Real.sqrt 3 : ℂ) / 2 * C ^ 2 := by
    rw [hC]; push_cast; ring
  rw [hR]
  simp [ellipticUmbilicCycle, s36a_rayDir_eq']
  linear_combination (-3 * C ^ 2 * (Real.sqrt 3 : ℂ) / 2) * I_sq

/-! ### Agreement with the oscillatory integrals of DLMF (§36.2(i)) -/

/-! #### Contour rotation for the cuspoids (36.2.4, 36.2.10) -/

/-- Powers of a point `R e^{iy}` on a circle. -/
lemma q2s_pow_exp (R y : ℝ) (j : ℕ) :
    ((R : ℂ) * exp (y * I)) ^ j = ((R ^ j : ℝ) : ℂ) * exp (((j * y : ℝ) : ℂ) * I) := by
  rw [mul_pow, ← exp_nat_mul]; push_cast; ring_nf

/-- `Im (R e^{iy})^j = R^j sin(jy)`. -/
lemma q2s_im_pow_exp (R y : ℝ) (j : ℕ) :
    (((R : ℂ) * exp (y * I)) ^ j).im = R ^ j * Real.sin (j * y) := by
  rw [q2s_pow_exp, im_ofReal_mul, exp_ofReal_mul_I_im]

/-- Lower bound for `Im Φ_K` on the circle of radius `R`, `y ≥ 0`. -/
lemma q2s_im_potential_arc (K : ℕ) (x : Fin K → ℝ) {R y : ℝ} (hR : 0 ≤ R) (hy : 0 ≤ y) :
    R ^ (K + 2) * Real.sin (((K + 2 : ℕ) : ℝ) * y) -
        ((K + 2 : ℕ) : ℝ) * y * ((∑ m, |x m|) * (1 + R ^ K)) ≤
      (cuspoidPotential K ((R : ℂ) * exp (y * I)) x).im := by
  rw [cuspoidPotential, add_im, im_sum, q2s_im_pow_exp]
  have hterm : ∀ m : Fin K, -(((K + 2 : ℕ) : ℝ) * y * (|x m| * (1 + R ^ K))) ≤
      (((x m : ℝ) : ℂ) * ((R : ℂ) * exp (y * I)) ^ ((m : ℕ) + 1)).im := by
    intro m
    rw [im_ofReal_mul, q2s_im_pow_exp]
    have h3 := s36a_pow_le_one_add R hR (show (m : ℕ) + 1 ≤ K from m.isLt)
    have hs : |Real.sin (((m : ℕ) + 1 : ℕ) * y)| ≤ ((K + 2 : ℕ) : ℝ) * y := by
      refine Real.abs_sin_le_abs.trans ?_
      rw [abs_of_nonneg (by positivity)]
      have : (((m : ℕ) + 1 : ℕ) : ℝ) ≤ ((K + 2 : ℕ) : ℝ) := by
        exact_mod_cast (by omega : (m : ℕ) + 1 ≤ K + 2)
      exact mul_le_mul_of_nonneg_right this hy
    have habs : |x m * (R ^ ((m : ℕ) + 1) * Real.sin (((m : ℕ) + 1 : ℕ) * y))| ≤
        ((K + 2 : ℕ) : ℝ) * y * (|x m| * (1 + R ^ K)) := by
      rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hR _)]
      calc |x m| * (R ^ ((m : ℕ) + 1) * |Real.sin (((m : ℕ) + 1 : ℕ) * y)|) ≤
            |x m| * ((1 + R ^ K) * (((K + 2 : ℕ) : ℝ) * y)) := by
            gcongr
        _ = _ := by ring
    linarith [neg_abs_le (x m * (R ^ ((m : ℕ) + 1) * Real.sin (((m : ℕ) + 1 : ℕ) * y)))]
  have := Finset.sum_le_sum (fun m (_ : m ∈ Finset.univ) => hterm m)
  rw [Finset.sum_neg_distrib, ← Finset.mul_sum, ← Finset.sum_mul] at this
  linarith


/-- Lower bound `Im Φ_K(R e^{iy}) ≥ (R²/π) y` on the arc `0 ≤ y ≤ π/(2(K+2))` for large `R`. -/
lemma q2s_im_potential_arc_ge (K : ℕ) (x : Fin K → ℝ) {R y : ℝ} (hR : 1 ≤ R)
    (hRC : 2 * π * (∑ m, |x m|) ≤ R ^ 2) (hy : 0 ≤ y) (hyθ : y ≤ cuspoidAngle K) :
    R ^ 2 / π * y ≤ (cuspoidPotential K ((R : ℂ) * exp (y * I)) x).im := by
  have h := q2s_im_potential_arc K x (by linarith : (0 : ℝ) ≤ R) hy
  set C := ∑ m, |x m|
  set n : ℝ := ((K + 2 : ℕ) : ℝ) with hn
  have hn2 : 2 ≤ n := by rw [hn]; push_cast; linarith [(K.cast_nonneg : (0 : ℝ) ≤ K)]
  have hpi := Real.pi_pos
  have hny : n * y ≤ π / 2 := by
    have := s36a_angle_mul K
    rw [hn]; push_cast
    calc ((K : ℝ) + 2) * y ≤ ((K : ℝ) + 2) * cuspoidAngle K := by
          gcongr
      _ = π / 2 := this
  have hsin := Real.mul_le_sin (by positivity) hny
  have hRK : 1 ≤ R ^ K := one_le_pow₀ hR
  have hR0 : 0 < R := by linarith
  have hpow : R ^ (K + 2) = R ^ K * R ^ 2 := pow_add _ _ _
  have hC : 0 ≤ C := Finset.sum_nonneg fun m _ => abs_nonneg _
  -- R^(K+2) sin(n y) ≥ R^K R^2 (2/π) n y
  have h1 : R ^ (K + 2) * (2 / π * (n * y)) ≤ R ^ (K + 2) * Real.sin (n * y) :=
    mul_le_mul_of_nonneg_left hsin (by positivity)
  have h2 : n * y * (C * (1 + R ^ K)) ≤ n * y * (C * (2 * R ^ K)) := by
    gcongr; linarith
  have hny0 : 0 ≤ n * y := by positivity
  have key : R ^ 2 / π * y ≤ R ^ (K + 2) * (2 / π * (n * y)) - n * y * (C * (2 * R ^ K)) := by
    rw [hpow]
    have e : R ^ K * R ^ 2 * (2 / π * (n * y)) - n * y * (C * (2 * R ^ K)) =
        n * y * R ^ K * (2 * R ^ 2 / π - 2 * C) := by ring
    rw [e]
    have hC' : C ≤ R ^ 2 / (2 * π) := by rw [le_div_iff₀ (by positivity)]; linarith
    have hb : R ^ 2 / π ≤ 2 * R ^ 2 / π - 2 * C := by
      have : R ^ 2 / (2 * π) * 2 = R ^ 2 / π := by field_simp
      have : 2 * R ^ 2 / π = R ^ 2 / π + R ^ 2 / π := by ring
      nlinarith
    have hy' : R ^ 2 / π * y ≤ n * y * R ^ K * (R ^ 2 / π) := by
      have : y ≤ n * y * R ^ K := by nlinarith
      nlinarith [div_nonneg (sq_nonneg R) hpi.le]
    calc R ^ 2 / π * y ≤ n * y * R ^ K * (R ^ 2 / π) := hy'
      _ ≤ _ := by gcongr
  linarith

/-- Jordan-type bound for the arc `0 ≤ arg t ≤ π/(2(K+2))`, `|t| = R`, phase `κ > 0`. -/
lemma q2s_arc_bound (K : ℕ) (x : Fin K → ℝ) {κ : ℝ} (hκ : 0 < κ) {R : ℝ} (hR : 1 ≤ R)
    (hRC : 2 * π * (∑ m, |x m|) ≤ R ^ 2) :
    ‖∫ y in (0 : ℝ)..cuspoidAngle K, I * R * exp (y * I) *
        exp (I * κ * cuspoidPotential K ((R : ℂ) * exp (y * I)) x)‖ ≤ π / (κ * R) := by
  have hR0 : 0 < R := by linarith
  have hpi := Real.pi_pos
  have hθ : 0 ≤ cuspoidAngle K := by unfold cuspoidAngle; positivity
  set a := κ * (R ^ 2 / π) with ha
  have ha0 : 0 < a := by positivity
  have hbound : ∀ y ∈ Ioc (0 : ℝ) (cuspoidAngle K),
      ‖I * R * exp (y * I) * exp (I * κ * cuspoidPotential K ((R : ℂ) * exp (y * I)) x)‖ ≤
        R * Real.exp (-(a * y)) := by
    intro y hy
    rw [norm_mul, norm_mul, norm_mul, norm_I, one_mul, norm_real, Real.norm_eq_abs,
      norm_exp_ofReal_mul_I, mul_one, norm_exp, abs_of_pos hR0]
    gcongr
    have hre : (I * κ * cuspoidPotential K ((R : ℂ) * exp (y * I)) x).re =
        -κ * (cuspoidPotential K ((R : ℂ) * exp (y * I)) x).im := by
      simp [mul_re, mul_im]
    rw [hre]
    have := q2s_im_potential_arc_ge K x hR hRC hy.1.le hy.2
    rw [ha]; nlinarith
  calc _ ≤ ∫ y in (0 : ℝ)..cuspoidAngle K, R * Real.exp (-(a * y)) :=
        intervalIntegral.norm_integral_le_of_norm_le hθ
          (Eventually.of_forall hbound) (Continuous.intervalIntegrable (by fun_prop) _ _)
    _ = R * ∫ y in (0 : ℝ)..cuspoidAngle K, Real.exp (-(a * y)) :=
        intervalIntegral.integral_const_mul _ _
    _ ≤ R * (1 / a) := by gcongr; exact DLMF.Airy.airyInt_integral_exp_neg_le ha0 _
    _ = π / (κ * R) := by rw [ha]; field_simp


/-- The right tail: `∫₀^R exp(iκΦ_K(t; x)) dt` tends to the integral over the rotated ray
`arg t = π/(2(K+2))` (Cauchy's theorem on the sector and the Jordan-type arc bound). -/
lemma q2s_tendsto_right (K : ℕ) (x : Fin K → ℝ) {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun R : ℝ => ∫ t in (0 : ℝ)..R, exp (I * κ * cuspoidPotential K t x)) atTop
      (𝓝 (∫ r in Ioi (0 : ℝ), cuspoidContourDir K r *
        exp (I * κ * cuspoidPotential K (cuspoidContour K r) x))) := by
  set f : ℂ → ℂ := fun w => exp (I * κ * cuspoidPotential K w x) with hf
  have hfc : Continuous f := by
    rw [hf]; exact continuous_exp.comp (continuous_const.mul (continuous_cuspoidPotential K x))
  obtain ⟨G, hG⟩ : ∃ G : ℂ → ℂ, ∀ w, HasDerivAt G (f w) w := by
    have hd : Differentiable ℂ f := by
      rw [hf]; unfold cuspoidPotential; fun_prop
    obtain ⟨g, hg⟩ := hd.isExactOn_univ
    exact ⟨g, fun w => hg w (mem_univ w)⟩
  set u := exp ((cuspoidAngle K : ℂ) * I) with hu
  have hsplit : ∀ R : ℝ, ∫ t in (0 : ℝ)..R, f t =
      (∫ r in (0 : ℝ)..R, u * f (r * u)) -
        ∫ y in (0 : ℝ)..cuspoidAngle K, I * R * exp (y * I) * f (R * exp (y * I)) := by
    intro R
    have h1 := DLMF.Airy.airyInt_integral_segment hG hfc 1 0 R
    have h2 := DLMF.Airy.airyInt_integral_segment hG hfc u 0 R
    have h3 := DLMF.Airy.airyInt_integral_arc hG hfc R 0 (cuspoidAngle K)
    simp only [one_mul, mul_one, ofReal_zero, zero_mul] at h1 h2 h3
    rw [h1, h2, h3, exp_zero, mul_one]
    ring
  have hint0 := (integrable_cuspoidIntegrand K x hκ).integrableOn (s := Ioi 0)
  have heq : EqOn (fun r : ℝ => cuspoidContourDir K r *
      exp (I * κ * cuspoidPotential K (cuspoidContour K r) x)) (fun r : ℝ => u * f (r * u))
      (Ioi 0) := by
    intro r hr
    simp only [hf, cuspoidContour, s36a_dir_of_nonneg K (le_of_lt hr), hu]
  have hint : IntegrableOn (fun r : ℝ => u * f (r * u)) (Ioi 0) :=
    hint0.congr_fun heq measurableSet_Ioi
  have hseg := intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id
  rw [← setIntegral_congr_fun measurableSet_Ioi heq] at hseg
  have harc : Tendsto (fun R : ℝ => ∫ y in (0 : ℝ)..cuspoidAngle K,
      I * R * exp (y * I) * f (R * exp (y * I))) atTop (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun R : ℝ => π / κ * R⁻¹) ?_
      (by simpa using (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul (π / κ))
    filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop (2 * π * (∑ m, |x m|) + 1)]
      with R hR hR'
    have hCs : 0 ≤ ∑ m, |x m| := Finset.sum_nonneg fun m _ => abs_nonneg (x m)
    have hb := q2s_arc_bound K x hκ hR (by nlinarith [Real.pi_pos])
    calc _ ≤ π / (κ * R) := by simpa only [hf] using hb
      _ = π / κ * R⁻¹ := by field_simp
  have := hseg.sub harc
  rw [sub_zero] at this
  refine this.congr fun R => ?_
  simp only [id]
  rw [hsplit R]


/-- Conjugation commutes with interval integrals. -/
lemma q2s_intervalIntegral_conj (f : ℝ → ℂ) (a b : ℝ) :
    ∫ t in a..b, conj (f t) = conj (∫ t in a..b, f t) := by
  simp only [intervalIntegral, map_sub, integral_conj]

/-- The left tail: `∫_R^0 exp(iκΦ_K(t; x)) dt` tends, as `R → -∞`, to the integral over the
rotated left ray of the contour of `cuspoidIntegral`. -/
lemma q2s_tendsto_left (K : ℕ) (x : Fin K → ℝ) {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun R : ℝ => ∫ t in R..0, exp (I * κ * cuspoidPotential K t x)) atBot
      (𝓝 (∫ r in Iic (0 : ℝ), cuspoidContourDir K r *
        exp (I * κ * cuspoidPotential K (cuspoidContour K r) x))) := by
  have hneg : ∀ R : ℝ, ∫ t in R..0, exp (I * κ * cuspoidPotential K t x) =
      ∫ t in (0 : ℝ)..(-R), exp (I * κ * cuspoidPotential K (-(t : ℂ)) x) := by
    intro R
    have := intervalIntegral.integral_comp_neg (a := 0) (b := -R)
      (fun t : ℝ => exp (I * κ * cuspoidPotential K t x))
    simp only [neg_neg, neg_zero, ofReal_neg] at this
    exact this.symm
  have hL := integral_comp_neg_Ioi 0 (fun r => cuspoidContourDir K r *
      exp (I * κ * cuspoidPotential K (cuspoidContour K r) x))
  rw [neg_zero] at hL
  rw [← hL]
  simp_rw [hneg]
  refine Tendsto.comp (g := fun S : ℝ => ∫ t in (0 : ℝ)..S,
    exp (I * κ * cuspoidPotential K (-(t : ℂ)) x)) ?_ tendsto_neg_atBot_atTop
  by_cases hK : Even K
  · have h := q2s_tendsto_right K (fun m => (-1) ^ ((m : ℕ) + 1) * x m) hκ
    simp_rw [s36a_potential_neg_even hK]
    convert h using 2
    refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
    simp only [cuspoidContour, s36a_dir_of_even hK, ofReal_neg, neg_mul]
    rw [s36a_potential_neg_even hK]
  · have h := q2s_tendsto_right K (fun m => (-1) ^ (m : ℕ) * x m) hκ
    have h' := ((continuous_conj).tendsto _).comp h
    rw [Function.comp_def] at h'
    have hfun : ∀ S : ℝ, ∫ t in (0 : ℝ)..S, exp (I * κ * cuspoidPotential K (-(t : ℂ)) x) =
        conj (∫ t in (0 : ℝ)..S, exp (I * κ *
          cuspoidPotential K (t : ℂ) (fun m => (-1) ^ (m : ℕ) * x m))) := by
      intro S
      rw [← q2s_intervalIntegral_conj]
      refine intervalIntegral.integral_congr fun t _ => ?_
      rw [← exp_conj, map_mul, map_mul, conj_I, conj_ofReal, conj_cuspoidPotential, conj_ofReal,
        s36a_potential_neg_odd hK]
      ring_nf
    simp_rw [hfun]
    convert h' using 2
    rw [← integral_conj]
    refine setIntegral_congr_fun measurableSet_Ioi fun r (hr : 0 < r) => ?_
    have hd : conj (cuspoidContourDir K r) = cuspoidContourDir K (-r) := by
      rw [s36a_dir_of_nonneg K hr.le, s36a_dir_of_odd_neg hK (by linarith), ← exp_conj]
      congr 1; simp [conj_ofReal]
    rw [map_mul, ← exp_conj, map_mul, map_mul, conj_I, conj_ofReal, conj_cuspoidPotential, hd]
    have hc : conj (cuspoidContour K r) = -cuspoidContour K (-r) := by
      rw [cuspoidContour, map_mul, conj_ofReal, hd, cuspoidContour]; push_cast; ring
    have hx : (fun m : Fin K => (-1 : ℝ) ^ (m : ℕ) * ((-1) ^ (m : ℕ) * x m)) = x := by
      funext m; rw [← mul_assoc, ← mul_pow]; simp
    rw [hc, s36a_potential_neg_odd hK, hx]
    ring_nf


/-- The improper real integral `∫ exp(iκΦ_K(t; x)) dt` converges (both tails) to the
rotated-contour integral, for every phase `κ > 0`. -/
lemma q2s_hasIntegralWholeLine (K : ℕ) (x : Fin K → ℝ) {κ : ℝ} (hκ : 0 < κ) :
    HasIntegralWholeLine (fun t : ℝ => exp (I * κ * cuspoidPotential K t x))
      (∫ r : ℝ, cuspoidContourDir K r *
        exp (I * κ * cuspoidPotential K (cuspoidContour K r) x)) := by
  have hint := integrable_cuspoidIntegrand K x hκ
  refine ⟨_, _, q2s_tendsto_left K x hκ, q2s_tendsto_right K x hκ, ?_⟩
  exact intervalIntegral.integral_Iic_add_Ioi hint.integrableOn hint.integrableOn

/-- A constant factor passes through an improper whole-line integral. -/
lemma q2s_hasIntegralWholeLine_const_mul {f : ℝ → ℂ} {v : ℂ} (c : ℂ)
    (h : HasIntegralWholeLine f v) : HasIntegralWholeLine (fun t => c * f t) (c * v) := by
  obtain ⟨u, w, hu, hw, huw⟩ := h
  refine ⟨c * u, c * w, ?_, ?_, by rw [← huw]; ring⟩
  · unfold HasIntegralAtBot at hu ⊢
    simp_rw [intervalIntegral.integral_const_mul]
    exact hu.const_mul c
  · unfold HasIntegralAtTop at hw ⊢
    simp_rw [intervalIntegral.integral_const_mul]
    exact hw.const_mul c


/-- The improper real integral `∫_{-∞}^{∞} exp(iΦ_K(t; x)) dt` converges (both tails separately)
to the rotated-contour integral `Ψ_K(x)` (DLMF 36.2.4; contour rotation, Jordan's lemma). -/
@[dlmf 36.2.E4]
theorem hasIntegralWholeLine_cuspoidIntegral (K : ℕ) (x : Fin K → ℝ) :
    HasIntegralWholeLine (fun t : ℝ => exp (I * cuspoidPotential K t x))
      (cuspoidIntegral K x) := by
  simpa [cuspoidIntegral] using q2s_hasIntegralWholeLine K x one_pos

/-- DLMF 36.2.5 for `U = H` as an iterated improper integral: for each real `t` the inner
`s`-integral converges, and the outer `t`-integral of the result converges to `Ψ^{(H)}(x)`. -/
@[dlmf 36.2.E5]
theorem hasIteratedIntegral_hyperbolicUmbilicIntegral (x y z : ℝ) :
    ∃ g : ℝ → ℂ, (∀ t : ℝ, HasIntegralWholeLine
        (fun s : ℝ => exp (I * hyperbolicUmbilicPotential s t x y z)) (g t)) ∧
      HasIntegralWholeLine g (hyperbolicUmbilicIntegral x y z) := by
  sorry

/-- DLMF 36.2.5 for `U = E` as an iterated improper integral: for each real `t` the inner
`s`-integral converges, and the outer `t`-integral of the result converges to `Ψ^{(E)}(x)`. -/
@[dlmf 36.2.E5]
theorem hasIteratedIntegral_ellipticUmbilicIntegral (x y z : ℝ) :
    ∃ g : ℝ → ℂ, (∀ t : ℝ, HasIntegralWholeLine
        (fun s : ℝ => exp (I * ellipticUmbilicPotential s t x y z)) (g t)) ∧
      HasIntegralWholeLine g (ellipticUmbilicIntegral x y z) := by
  sorry

/-- The diffraction catastrophe at `k = 1` is the canonical integral. -/
@[simp] theorem cuspoidDiffraction_one (K : ℕ) (x : Fin K → ℝ) :
    cuspoidDiffraction K x 1 = cuspoidIntegral K x := by
  simp [cuspoidDiffraction, cuspoidIntegral]

/-- The umbilic diffraction catastrophes at `k = 1` are the canonical integrals. -/
@[simp] theorem hyperbolicUmbilicDiffraction_one (x y z : ℝ) :
    hyperbolicUmbilicDiffraction x y z 1 = hyperbolicUmbilicIntegral x y z := by
  simp [hyperbolicUmbilicDiffraction, hyperbolicUmbilicIntegral]

@[simp] theorem ellipticUmbilicDiffraction_one (x y z : ℝ) :
    ellipticUmbilicDiffraction x y z 1 = ellipticUmbilicIntegral x y z := by
  simp [ellipticUmbilicDiffraction, ellipticUmbilicIntegral]

/-- The improper integral `√k ∫ exp(ikΦ_K(t; x)) dt` converges to `Ψ_K(x; k)` for `k > 0`
(DLMF 36.2.10). -/
@[dlmf 36.2.E10]
theorem hasIntegralWholeLine_cuspoidDiffraction (K : ℕ) (x : Fin K → ℝ) {k : ℝ} (hk : 0 < k) :
    HasIntegralWholeLine (fun t : ℝ => (Real.sqrt k : ℂ) * exp (I * k * cuspoidPotential K t x))
      (cuspoidDiffraction K x k) :=
  q2s_hasIntegralWholeLine_const_mul _ (q2s_hasIntegralWholeLine K x hk)

/-- DLMF 36.2.11 (`U = H`): `k ∫∫ exp(ikΦ^{(H)}) ds dt` as an iterated improper integral
converges to `Ψ^{(H)}(x; k)` for `k > 0`. -/
@[dlmf 36.2.E11]
theorem hasIteratedIntegral_hyperbolicUmbilicDiffraction (x y z : ℝ) {k : ℝ} (hk : 0 < k) :
    ∃ g : ℝ → ℂ, (∀ t : ℝ, HasIntegralWholeLine
        (fun s : ℝ => (k : ℂ) * exp (I * k * hyperbolicUmbilicPotential s t x y z)) (g t)) ∧
      HasIntegralWholeLine g (hyperbolicUmbilicDiffraction x y z k) := by
  sorry

/-- DLMF 36.2.11 (`U = E`): `k ∫∫ exp(ikΦ^{(E)}) ds dt` as an iterated improper integral
converges to `Ψ^{(E)}(x; k)` for `k > 0`. -/
@[dlmf 36.2.E11]
theorem hasIteratedIntegral_ellipticUmbilicDiffraction (x y z : ℝ) {k : ℝ} (hk : 0 < k) :
    ∃ g : ℝ → ℂ, (∀ t : ℝ, HasIntegralWholeLine
        (fun s : ℝ => (k : ℂ) * exp (I * k * ellipticUmbilicPotential s t x y z)) (g t)) ∧
      HasIntegralWholeLine g (ellipticUmbilicDiffraction x y z k) := by
  sorry

/-! ### The fold with a complex coefficient; Fubini for the hyperbolic umbilic -/

/-- `Im t³ = |r|³` on the cubic V-contour `t = cuspoidContour 1 r`. -/
lemma q2s_im_cube_contour (r : ℝ) : (cuspoidContour 1 r ^ 3).im = |r| ^ 3 := by
  have h := cuspoidContour_pow 1 r
  norm_num at h
  rw [h, I_mul_im, ← ofReal_pow, ofReal_re]

/-- Elementary bound `B a² + A a ≤ a³ - a²/2 + (B + 1)³ + A²/2` for `a, A, B ≥ 0`. -/
lemma q2s_cubic_ineq {a A B : ℝ} (ha : 0 ≤ a) (hB : 0 ≤ B) :
    B * a ^ 2 + A * a ≤ a ^ 3 - a ^ 2 / 2 + (B + 1) ^ 3 + A ^ 2 / 2 := by
  have h1 : A * a ≤ a ^ 2 / 2 + A ^ 2 / 2 := by nlinarith [sq_nonneg (A - a)]
  have h2 : 0 ≤ a ^ 2 * (a - (B + 1)) + (B + 1) ^ 3 := by
    rcases le_total (B + 1) a with h | h
    · have : 0 ≤ a ^ 2 * (a - (B + 1)) := mul_nonneg (sq_nonneg a) (by linarith)
      nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ B + 1) 3]
    · have ha2 : a ^ 2 ≤ (B + 1) ^ 2 := by nlinarith
      have : a ^ 2 * (B + 1 - a) ≤ (B + 1) ^ 2 * (B + 1) :=
        mul_le_mul ha2 (by linarith) (by linarith) (sq_nonneg _)
      nlinarith
  nlinarith

/-- `Im(c t) ≥ -‖c‖ |r|` on the cubic V-contour. -/
lemma q2s_im_mul_contour_ge (c : ℂ) (r : ℝ) :
    -(‖c‖ * |r|) ≤ (c * cuspoidContour 1 r).im := by
  have := neg_abs_le (c * cuspoidContour 1 r).im
  have h2 := abs_im_le_norm (c * cuspoidContour 1 r)
  rw [norm_mul, norm_cuspoidContour] at h2
  linarith

/-- Gaussian bound for the cubic integrand with a complex linear coefficient. -/
lemma q2s_norm_fold_le (c : ℂ) (r : ℝ) :
    ‖cuspoidContourDir 1 r * exp (I * (cuspoidContour 1 r ^ 3 + c * cuspoidContour 1 r))‖ ≤
      Real.exp (1 + ‖c‖ ^ 2 / 2) * Real.exp (-(1 / 2) * r ^ 2) := by
  rw [norm_mul, norm_cuspoidContourDir, one_mul, norm_exp, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hre : (I * (cuspoidContour 1 r ^ 3 + c * cuspoidContour 1 r)).re =
      -((cuspoidContour 1 r ^ 3).im + (c * cuspoidContour 1 r).im) := by
    simp [mul_re, add_im]
  rw [hre, q2s_im_cube_contour]
  have h1 := q2s_im_mul_contour_ge c r
  have h2 := q2s_cubic_ineq (A := ‖c‖) (abs_nonneg r) (le_refl (0 : ℝ))
  rw [sq_abs] at h2
  nlinarith

/-- Measurability of the cubic integrand with complex linear coefficient. -/
lemma q2s_measurable_fold (c : ℂ) :
    Measurable fun r : ℝ =>
      cuspoidContourDir 1 r * exp (I * (cuspoidContour 1 r ^ 3 + c * cuspoidContour 1 r)) :=
  (measurable_cuspoidContourDir 1).mul (measurable_exp.comp (measurable_const.mul
    (((measurable_cuspoidContour 1).pow_const 3).add
      (measurable_const.mul (measurable_cuspoidContour 1)))))

/-- Integrability of the cubic integrand with complex linear coefficient. -/
lemma q2s_integrable_fold (c : ℂ) :
    Integrable fun r : ℝ =>
      cuspoidContourDir 1 r * exp (I * (cuspoidContour 1 r ^ 3 + c * cuspoidContour 1 r)) :=
  Integrable.mono' ((integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).const_mul _)
    (q2s_measurable_fold c).aestronglyMeasurable
    (ae_of_all _ fun r => by simpa using q2s_norm_fold_le c r)


/-- The fold integral with a complex linear coefficient:
`∫ exp(i(t³ + ct)) dt = (2π/3^{1/3}) Ai(c/3^{1/3})` over the cubic V-contour (36.2.13 for
complex `c`). -/
lemma q2s_fold_airy (c : ℂ) :
    ∫ r : ℝ, cuspoidContourDir 1 r *
        exp (I * (cuspoidContour 1 r ^ 3 + c * cuspoidContour 1 r)) =
      2 * π / (((3 : ℝ) ^ (1 / 3 : ℝ) : ℝ) : ℂ) *
        DLMF.Airy.airyAi (c / (((3 : ℝ) ^ (1 / 3 : ℝ) : ℝ) : ℂ)) := by
  set a : ℝ := (3 : ℝ) ^ (1 / 3 : ℝ) with ha_def
  have ha : 0 < a := by positivity
  have ha3 : (a : ℂ) ^ 3 = 3 := by
    have : a ^ 3 = 3 := by
      rw [ha_def, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    exact_mod_cast this
  have ha0 : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha.ne'
  set w : ℂ := c / a with hw_def
  have hw : (a : ℂ) * w = c := by rw [hw_def]; field_simp
  clear_value w
  set Kf : ℂ → ℂ := fun t => exp (t ^ 3 / 3 - w * t) with hKf
  set F : ℝ → ℂ := fun r => cuspoidContourDir 1 r *
    exp (I * (cuspoidContour 1 r ^ 3 + c * cuspoidContour 1 r)) with hF
  have hint : Integrable F := q2s_integrable_fold c
  set u : ℂ := exp (((π / 6 : ℝ) : ℂ) * I) with hu
  have hu3 : u ^ 3 = I := DLMF.Airy.airyInt_exp_sixth_cube
  have hθ : (cuspoidAngle 1 : ℂ) = ((π / 6 : ℝ) : ℂ) := by
    unfold cuspoidAngle; push_cast; ring
  have hv : exp (((-π / 3 : ℝ) : ℂ) * I) = -I * u := DLMF.Airy.airyInt_exp_neg_third
  have hv' : exp (((π / 3 : ℝ) : ℂ) * I) = u ^ 2 := by
    rw [hu, ← exp_nat_mul]; congr 1; push_cast; ring
  have hm : exp (-(cuspoidAngle 1 : ℂ) * I) = -I * u ^ 2 := by
    rw [neg_mul, exp_neg, hθ, ← hu]
    refine inv_eq_of_mul_eq_one_right ?_
    linear_combination (-I) * hu3 - I_sq
  -- the right ray
  set g : ℝ → ℂ := fun ρ : ℝ =>
    exp (((-π / 3 : ℝ) : ℂ) * I) * Kf ((ρ : ℂ) * exp (((-π / 3 : ℝ) : ℂ) * I)) with hg
  have hR : ∫ r in Ioi (0 : ℝ), F r =
      I * (a⁻¹ : ℝ) * DLMF.Airy.rayIntegral Kf (-π / 3) 0 := by
    have h1 : ∀ r ∈ Ioi (0 : ℝ), F r = I * g (a * r) := by
      intro r hr
      simp only [hF, hg, hKf]
      rw [cuspoidContour, s36a_dir_of_nonneg 1 (le_of_lt hr), hθ, hv, ← hu]
      have e : I * (((r : ℂ) * u) ^ 3 + c * ((r : ℂ) * u)) =
          (((a * r : ℝ) : ℂ) * (-I * u)) ^ 3 / 3 - w * (((a * r : ℝ) : ℂ) * (-I * u)) := by
        push_cast
        linear_combination ((a : ℂ) ^ 3 * (r : ℂ) ^ 3 * I * u ^ 3 / 3) * I_sq +
          (-(r : ℂ) ^ 3 * I * u ^ 3 / 3) * ha3 + (-I * r * u) * hw
      rw [e]
      linear_combination (u * exp ((((a * r : ℝ) : ℂ) * (-I * u)) ^ 3 / 3 -
        w * (((a * r : ℝ) : ℂ) * (-I * u)))) * I_sq
    rw [setIntegral_congr_fun measurableSet_Ioi h1, integral_const_mul,
      integral_comp_mul_left_Ioi g 0 ha, mul_zero, hg, DLMF.Airy.rayIntegral, Complex.real_smul]
    ring
  -- the left ray
  set g' : ℝ → ℂ := fun ρ : ℝ =>
    exp (((π / 3 : ℝ) : ℂ) * I) * Kf ((ρ : ℂ) * exp (((π / 3 : ℝ) : ℂ) * I)) with hg'
  have hL : ∫ r in Iic (0 : ℝ), F r =
      -I * (a⁻¹ : ℝ) * DLMF.Airy.rayIntegral Kf (π / 3) 0 := by
    have := integral_comp_neg_Ioi 0 F
    rw [neg_zero] at this
    rw [← this]
    have h1 : ∀ r ∈ Ioi (0 : ℝ), F (-r) = -I * g' (a * r) := by
      intro r hr
      simp only [hF, hg', hKf]
      rw [cuspoidContour, s36a_dir_of_odd_neg (by decide : ¬ Even 1)
        (by linarith [hr.out] : -r < 0), hm, hv']
      have e : I * ((((-r : ℝ) : ℂ) * (-I * u ^ 2)) ^ 3 + c * (((-r : ℝ) : ℂ) * (-I * u ^ 2)))
          = (((a * r : ℝ) : ℂ) * u ^ 2) ^ 3 / 3 - w * (((a * r : ℝ) : ℂ) * u ^ 2) := by
        push_cast
        linear_combination ((r : ℂ) ^ 3 * u ^ 6 * (I ^ 2 - 1) + c * r * u ^ 2) * I_sq +
          (-(r : ℂ) ^ 3 * u ^ 6 / 3) * ha3 + ((r : ℂ) * u ^ 2) * hw
      rw [e]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi h1, integral_const_mul,
      integral_comp_mul_left_Ioi g' 0 ha, mul_zero, hg', DLMF.Airy.rayIntegral, Complex.real_smul]
    ring
  -- the Airy contour integral as two rays
  obtain ⟨G, hG⟩ : ∃ G : ℂ → ℂ, ∀ t, HasDerivAt G (Kf t) t := by
    have hd : Differentiable ℂ Kf := by rw [hKf]; fun_prop
    obtain ⟨g, hg⟩ := hd.isExactOn_univ
    exact ⟨g, fun t => hg t (mem_univ t)⟩
  have hKc : Continuous Kf := by rw [hKf]; fun_prop
  have hcont := DLMF.Airy.airyInt_contourIntegral_eq_rays hG hKc (-π / 3) (π / 3)
    (DLMF.Airy.airyInt_integrableOn_ray w (DLMF.Airy.airyInt_exp_three_mul _ (-1)
      (by push_cast; ring)))
    (DLMF.Airy.airyInt_integrableOn_ray w (DLMF.Airy.airyInt_exp_three_mul _ 0
      (by push_cast; ring)))
  have hAi := DLMF.Airy.airyAi_contour_integral w
  rw [← hKf, hcont] at hAi
  rw [← intervalIntegral.integral_Iic_add_Ioi hint.integrableOn hint.integrableOn (b := 0),
    hL, hR, hAi]
  generalize DLMF.Airy.rayIntegral Kf (-π / 3) 0 = A
  generalize DLMF.Airy.rayIntegral Kf (π / 3) 0 = B
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp
  linear_combination (A - B) * I_sq


/-- `Im(c t) ≥ -|c| |r|` on the cubic V-contour, real `c`. -/
lemma q2s_im_lin_contour_ge (c : ℝ) (r : ℝ) :
    -(|c| * |r|) ≤ ((c : ℂ) * cuspoidContour 1 r).im := by
  simpa using q2s_im_mul_contour_ge (c : ℂ) r

/-- Gaussian bound for the hyperbolic umbilic integrand on the product of V-contours. -/
lemma q2s_norm_hyperbolic_le (x y z : ℝ) (p : ℝ × ℝ) :
    ‖cuspoidContourDir 1 p.1 * cuspoidContourDir 1 p.2 *
        exp (I * hyperbolicUmbilicPotential (cuspoidContour 1 p.1) (cuspoidContour 1 p.2) x y z)‖
      ≤ Real.exp (2 * (|z| / 2 + 1) ^ 3 + x ^ 2 / 2 + y ^ 2 / 2) *
        (Real.exp (-(1 / 2) * p.1 ^ 2) * Real.exp (-(1 / 2) * p.2 ^ 2)) := by
  rw [norm_mul, norm_mul, norm_cuspoidContourDir, norm_cuspoidContourDir, one_mul, one_mul,
    norm_exp, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  set σ := cuspoidContour 1 p.1
  set τ := cuspoidContour 1 p.2
  have hre : (I * hyperbolicUmbilicPotential σ τ x y z).re =
      -((σ ^ 3).im + (τ ^ 3).im + ((z : ℂ) * (σ * τ)).im + ((y : ℂ) * τ).im +
        ((x : ℂ) * σ).im) := by
    simp only [hyperbolicUmbilicPotential, mul_re, I_re, I_im, add_im, zero_mul, one_mul,
      zero_sub]
    ring_nf
  rw [hre, q2s_im_cube_contour, q2s_im_cube_contour]
  have h1 := q2s_im_lin_contour_ge x p.1
  have h2 := q2s_im_lin_contour_ge y p.2
  have h3 : -(|z| * (|p.1| * |p.2|)) ≤ ((z : ℂ) * (σ * τ)).im := by
    have := neg_abs_le ((z : ℂ) * (σ * τ)).im
    have h := abs_im_le_norm ((z : ℂ) * (σ * τ))
    rw [norm_mul, norm_mul, norm_cuspoidContour, norm_cuspoidContour, norm_real,
      Real.norm_eq_abs] at h
    linarith
  have h4 : |z| * (|p.1| * |p.2|) ≤ |z| / 2 * |p.1| ^ 2 + |z| / 2 * |p.2| ^ 2 := by
    nlinarith [sq_nonneg (|p.1| - |p.2|), abs_nonneg z]
  have hB : 0 ≤ |z| / 2 := by positivity
  have c1 := q2s_cubic_ineq (A := |x|) (abs_nonneg p.1) hB
  have c2 := q2s_cubic_ineq (A := |y|) (abs_nonneg p.2) hB
  rw [sq_abs] at c1 c2
  rw [sq_abs p.1, sq_abs p.2] at h4
  have hx2 : |x| ^ 2 = x ^ 2 := sq_abs x
  have hy2 : |y| ^ 2 = y ^ 2 := sq_abs y
  rw [hx2] at c1; rw [hy2] at c2
  nlinarith

/-- Measurability of the hyperbolic umbilic integrand. -/
lemma q2s_measurable_hyperbolic (x y z : ℝ) :
    Measurable fun p : ℝ × ℝ => cuspoidContourDir 1 p.1 * cuspoidContourDir 1 p.2 *
      exp (I * hyperbolicUmbilicPotential (cuspoidContour 1 p.1) (cuspoidContour 1 p.2) x y z) := by
  have h1 : Measurable fun p : ℝ × ℝ => cuspoidContour 1 p.1 :=
    (measurable_cuspoidContour 1).comp measurable_fst
  have h2 : Measurable fun p : ℝ × ℝ => cuspoidContour 1 p.2 :=
    (measurable_cuspoidContour 1).comp measurable_snd
  refine (((measurable_cuspoidContourDir 1).comp measurable_fst).mul
    ((measurable_cuspoidContourDir 1).comp measurable_snd)).mul (measurable_exp.comp
    (measurable_const.mul ?_))
  unfold hyperbolicUmbilicPotential
  exact ((((h1.pow_const 3).add (h2.pow_const 3)).add
    ((measurable_const.mul h1).mul h2)).add (measurable_const.mul h2)).add
    (measurable_const.mul h1)

/-- The integrand of `hyperbolicUmbilicIntegral` is integrable on `ℝ²`. -/
lemma q2s_integrable_hyperbolic (x y z : ℝ) :
    Integrable (fun p : ℝ × ℝ => cuspoidContourDir 1 p.1 * cuspoidContourDir 1 p.2 *
      exp (I * hyperbolicUmbilicPotential (cuspoidContour 1 p.1) (cuspoidContour 1 p.2) x y z))
      (volume : Measure (ℝ × ℝ)) := by
  have hg := integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)
  have hprod : Integrable (fun p : ℝ × ℝ =>
      Real.exp (-(1 / 2) * p.1 ^ 2) * Real.exp (-(1 / 2) * p.2 ^ 2))
      (volume : Measure (ℝ × ℝ)) := by
    rw [Measure.volume_eq_prod]; exact hg.mul_prod hg
  exact Integrable.mono' (hprod.const_mul _)
    (q2s_measurable_hyperbolic x y z).aestronglyMeasurable
    (ae_of_all _ fun p => q2s_norm_hyperbolic_le x y z p)

/-! ### One-dimensional representations of the umbilic integrals (§36.2(i)) -/

/-- DLMF 36.2.6: `Ψ^{(E)}(x) = 2√(π/3) exp(i(4z³/27 + xz/3 - π/4)) ∫ exp(i(u⁶ + 2zu⁴ + (z² + x)u²
+ y²/(12u²))) du`, the contour running from `∞e^{-7πi/12}` to `∞e^{πi/12}` and passing to the lower
right of `u = 0` (rays from radius one and the arc of the unit circle from `-7π/12` to `π/12`). -/
@[dlmf 36.2.E6]
theorem ellipticUmbilicIntegral_eq_contour (x y z : ℝ) :
    ellipticUmbilicIntegral x y z = 2 * (Real.sqrt (π / 3) : ℂ) *
      exp (I * (4 / 27 * (z : ℂ) ^ 3 + 1 / 3 * x * z - π / 4)) *
      DLMF.Airy.contourIntegral (fun u => exp (I * (u ^ 6 + 2 * z * u ^ 4 +
        ((z : ℂ) ^ 2 + x) * u ^ 2
        + (y : ℂ) ^ 2 / (12 * u ^ 2)))) (-7 * π / 12) (π / 12) := by
  sorry

/-- DLMF 36.2.7:
`Ψ^{(E)}(x) = (4π/3^{1/3}) exp(i(2z³/27 - xz/3)) (e^{-iπ/6} F₊(x) + e^{iπ/6} F₋(x))`
with
`F_±(x) = ∫₀^∞ cos(r y e^{±iπ/6}) exp(2ir²z e^{±iπ/3}) Ai(3^{2/3}r² + 3^{-1/3}e^{∓iπ/3}(z²/3 - x))
dr`; here `F σ` with `σ = 1` is `F₊` and `σ = -1` is `F₋`. -/
@[dlmf 36.2.E7]
theorem ellipticUmbilicIntegral_eq_airy (x y z : ℝ) :
    let F : ℂ → ℂ := fun σ => ∫ r in Ioi (0 : ℝ),
      Complex.cos (r * y * exp (σ * I * π / 6)) * exp (2 * I * r ^ 2 * z * exp (σ * I * π / 3)) *
        DLMF.Airy.airyAi ((((3 : ℝ) ^ (2 / 3 : ℝ) : ℝ) : ℂ) * r ^ 2 +
          (((3 : ℝ) ^ (-1 / 3 : ℝ) : ℝ) : ℂ) * exp (-σ * I * π / 3) * ((z : ℂ) ^ 2 / 3 - x))
    ellipticUmbilicIntegral x y z = 4 * π / (((3 : ℝ) ^ (1 / 3 : ℝ) : ℝ) : ℂ) *
      exp (I * (2 / 27 * (z : ℂ) ^ 3 - 1 / 3 * x * z)) *
      (exp (-I * π / 6) * F 1 + exp (I * π / 6) * F (-1)) := by
  sorry

/-- DLMF 36.2.8: `Ψ^{(H)}(x) = 4√(π/6) exp(i(z³/27 + z(y + x)/6 + π/4)) ∫ exp(i(2u⁶ + 2zu⁴
+ (z²/2 + x + y)u² - (y - x)²/(24u²))) du`, the contour running from `∞e^{5πi/12}` to `∞e^{πi/12}`
and passing to the upper right of `u = 0` (unit-circle arc from `5π/12` to `π/12`). -/
@[dlmf 36.2.E8]
theorem hyperbolicUmbilicIntegral_eq_contour (x y z : ℝ) :
    hyperbolicUmbilicIntegral x y z = 4 * (Real.sqrt (π / 6) : ℂ) *
      exp (I * (1 / 27 * (z : ℂ) ^ 3 + 1 / 6 * z * (y + x) + π / 4)) *
      DLMF.Airy.contourIntegral (fun u => exp (I * (2 * u ^ 6 + 2 * z * u ^ 4 +
        (1 / 2 * (z : ℂ) ^ 2 + x + y) * u ^ 2 - ((y : ℂ) - x) ^ 2 / (24 * u ^ 2))))
        (5 * π / 12) (π / 12) := by
  sorry

/-- DLMF 36.2.9: `Ψ^{(H)}(x) = (2π/3^{1/3}) ∫ exp(i(s³ + xs)) Ai((zs + y)/3^{1/3}) ds`, the contour
running from `∞e^{5πi/6}` to `∞e^{πi/6}` (the integrand is entire). -/
@[dlmf 36.2.E9]
theorem hyperbolicUmbilicIntegral_eq_airy (x y z : ℝ) :
    hyperbolicUmbilicIntegral x y z = 2 * π / (((3 : ℝ) ^ (1 / 3 : ℝ) : ℝ) : ℂ) *
      DLMF.Airy.contourIntegral (fun s => exp (I * (s ^ 3 + x * s)) *
        DLMF.Airy.airyAi ((z * s + y) / (((3 : ℝ) ^ (1 / 3 : ℝ) : ℝ) : ℂ)))
        (5 * π / 6) (π / 6) := by
  set a : ℂ := (((3 : ℝ) ^ (1 / 3 : ℝ) : ℝ) : ℂ) with ha
  set h0 : ℂ → ℂ := fun s => exp (I * (s ^ 3 + x * s)) * DLMF.Airy.airyAi ((z * s + y) / a)
    with hh0
  set f : ℝ → ℂ := fun r => cuspoidContourDir 1 r * h0 (cuspoidContour 1 r) with hf
  have hint := q2s_integrable_hyperbolic x y z
  have hinner : ∀ r : ℝ, ∫ q : ℝ, cuspoidContourDir 1 r * cuspoidContourDir 1 q *
      exp (I * hyperbolicUmbilicPotential (cuspoidContour 1 r) (cuspoidContour 1 q) x y z) =
      2 * π / a * f r := by
    intro r
    have e : ∀ q : ℝ, cuspoidContourDir 1 r * cuspoidContourDir 1 q *
        exp (I * hyperbolicUmbilicPotential (cuspoidContour 1 r) (cuspoidContour 1 q) x y z) =
        (cuspoidContourDir 1 r * exp (I * (cuspoidContour 1 r ^ 3 + x * cuspoidContour 1 r))) *
          (cuspoidContourDir 1 q * exp (I * (cuspoidContour 1 q ^ 3 +
            (z * cuspoidContour 1 r + y) * cuspoidContour 1 q))) := by
      intro q
      rw [mul_mul_mul_comm, ← exp_add]
      congr 2
      unfold hyperbolicUmbilicPotential; ring
    simp_rw [e]
    rw [integral_const_mul, q2s_fold_airy, hf, hh0]
    simp only
    ring
  have hval : hyperbolicUmbilicIntegral x y z = 2 * π / a * ∫ r, f r := by
    unfold hyperbolicUmbilicIntegral
    rw [Measure.volume_eq_prod] at hint ⊢
    rw [integral_prod _ hint]
    simp_rw [hinner]
    rw [integral_const_mul]
  have hfint : Integrable f := by
    rw [Measure.volume_eq_prod] at hint
    have h2 : Integrable (fun r : ℝ => 2 * π / a * f r) := by
      have := (hint.integral_prod_left)
      simp only at this
      refine this.congr (ae_of_all _ fun r => ?_)
      exact hinner r
    have ha0 : (2 * π / a : ℂ) ≠ 0 := by
      have : (a : ℂ) ≠ 0 := by rw [ha]; exact ofReal_ne_zero.mpr (by positivity)
      have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
      exact div_ne_zero (mul_ne_zero two_ne_zero hpi) this
    have := h2.const_mul (2 * π / a)⁻¹
    refine this.congr (ae_of_all _ fun r => ?_)
    simp only
    rw [← mul_assoc, inv_mul_cancel₀ ha0, one_mul]
  have hθ : (cuspoidAngle 1 : ℂ) = ((π / 6 : ℝ) : ℂ) := by
    unfold cuspoidAngle; push_cast; ring
  have h56 : exp (((5 * π / 6 : ℝ) : ℂ) * I) = -exp (-(cuspoidAngle 1 : ℂ) * I) := by
    rw [show (5 * π / 6 : ℝ) = -(π / 6) + π by ring, DLMF.Airy.exp_add_pi_mul_I, hθ]
    push_cast; ring_nf
  have hR : ∫ r in Ioi (0 : ℝ), f r = DLMF.Airy.rayIntegral h0 (π / 6) 0 := by
    rw [DLMF.Airy.rayIntegral]
    refine setIntegral_congr_fun measurableSet_Ioi fun r (hr : 0 < r) => ?_
    simp only [hf, cuspoidContour, s36a_dir_of_nonneg 1 hr.le, hθ]
  have hneg : ∀ r : ℝ, 0 < r → f (-r) =
      -(exp (((5 * π / 6 : ℝ) : ℂ) * I) * h0 ((r : ℂ) * exp (((5 * π / 6 : ℝ) : ℂ) * I))) := by
    intro r hr
    simp only [hf, cuspoidContour, s36a_dir_of_odd_neg (by decide : ¬ Even 1)
      (by linarith : -r < 0), h56]
    push_cast
    ring_nf
  have hL : ∫ r in Iic (0 : ℝ), f r = -DLMF.Airy.rayIntegral h0 (5 * π / 6) 0 := by
    have := integral_comp_neg_Ioi 0 f
    rw [neg_zero] at this
    rw [← this, DLMF.Airy.rayIntegral, ← integral_neg]
    exact setIntegral_congr_fun measurableSet_Ioi fun r (hr : 0 < r) => hneg r hr
  have hray1 : IntegrableOn (fun t : ℝ => exp (((π / 6 : ℝ) : ℂ) * I) *
      h0 ((t : ℂ) * exp (((π / 6 : ℝ) : ℂ) * I))) (Ioi 0) := by
    refine hfint.integrableOn.congr_fun (fun r (hr : 0 < r) => ?_) measurableSet_Ioi
    simp only [hf, cuspoidContour, s36a_dir_of_nonneg 1 hr.le, hθ]
  have hray2 : IntegrableOn (fun t : ℝ => exp (((5 * π / 6 : ℝ) : ℂ) * I) *
      h0 ((t : ℂ) * exp (((5 * π / 6 : ℝ) : ℂ) * I))) (Ioi 0) := by
    have := (hfint.comp_neg.integrableOn (s := Ioi 0)).neg
    refine this.congr_fun (fun r (hr : 0 < r) => ?_) measurableSet_Ioi
    rw [Pi.neg_apply, hneg r hr, neg_neg]
  obtain ⟨G, hG⟩ : ∃ G : ℂ → ℂ, ∀ t, HasDerivAt G (h0 t) t := by
    have hd : Differentiable ℂ h0 := by
      rw [hh0]
      exact (by fun_prop : Differentiable ℂ fun s : ℂ => exp (I * (s ^ 3 + x * s))).mul
        (DLMF.Airy.differentiable_airyAi.comp (by fun_prop))
    obtain ⟨g, hg⟩ := hd.isExactOn_univ
    exact ⟨g, fun t => hg t (mem_univ t)⟩
  have hc : Continuous h0 := by
    rw [hh0]
    exact (by fun_prop : Continuous fun s : ℂ => exp (I * (s ^ 3 + x * s))).mul
      (DLMF.Airy.differentiable_airyAi.continuous.comp (by fun_prop))
  rw [DLMF.Airy.airyInt_contourIntegral_eq_rays hG hc (5 * π / 6) (π / 6) hray2 hray1, hval,
    ← intervalIntegral.integral_Iic_add_Ioi hfint.integrableOn hfint.integrableOn (b := 0),
    hL, hR]

/-! ### Further special cases -/

/-- The cusp potential: `Φ₂(t; x₁, x₂) = t⁴ + x₂t² + x₁t`. -/
theorem cuspoidPotential_two (t : ℂ) (x₁ x₂ : ℝ) :
    cuspoidPotential 2 t ![x₁, x₂] = t ^ 4 + x₂ * t ^ 2 + x₁ * t := by
  simp [cuspoidPotential, Fin.sum_univ_two]; ring

/-- The Pearcey integral `P(x₂, x₁) = ∫ exp(i(t⁴ + x₂t² + x₁t)) dt` as an improper integral
(DLMF 36.2.14; from 36.2.4). -/
@[dlmf 36.2.E14]
theorem hasIntegralWholeLine_pearcey (x₂ x₁ : ℝ) :
    HasIntegralWholeLine (fun t : ℝ => exp (I * (t ^ 4 + x₂ * t ^ 2 + x₁ * t)))
      (pearcey x₂ x₁) := by
  have h := hasIntegralWholeLine_cuspoidIntegral 2 ![x₁, x₂]
  simp only [cuspoidPotential_two] at h
  exact h

/-- The moments of `exp(iΦ_K(t; 0)) = exp(i t^{K+2})` over the rotated contour:
`∫ d(r) t(r)^p exp(i t(r)^{K+2}) dr = (e^{iθ(p+1)} + (-1)^p d(-1)^{p+1}) Γ((p+1)/(K+2))/(K+2)`. -/
theorem q2s_moment_at_zero (K p : ℕ) :
    ∫ r : ℝ, cuspoidContourDir K r * cuspoidContour K r ^ p *
        exp (I * cuspoidPotential K (cuspoidContour K r) 0) =
      (exp ((cuspoidAngle K : ℂ) * I) ^ (p + 1) + (-1) ^ p * cuspoidContourDir K (-1) ^ (p + 1)) *
        ((1 / ((K : ℝ) + 2) * Real.Gamma ((p + 1) / ((K : ℝ) + 2)) : ℝ) : ℂ) := by
  set G : ℂ := ((1 / ((K : ℝ) + 2) * Real.Gamma ((p + 1) / ((K : ℝ) + 2)) : ℝ) : ℂ) with hG
  have hGi : ∫ r in Ioi (0 : ℝ), ((r ^ p * Real.exp (-r ^ (K + 2)) : ℝ) : ℂ) = G := by
    rw [integral_complex_ofReal, hG]
    congr 1
    have h := integral_rpow_mul_exp_neg_rpow (p := ((K + 2 : ℕ) : ℝ)) (q := (p : ℝ))
      (by positivity) (by have := p.cast_nonneg (α := ℝ); linarith)
    push_cast at h
    rw [← h]
    refine setIntegral_congr_fun measurableSet_Ioi fun r (hr : 0 < r) => ?_
    rw [← Real.rpow_natCast r p]
    congr 2
    rw [show ((K : ℝ) + 2) = ((K + 2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  have hf : ∀ r, cuspoidContourDir K r * cuspoidContour K r ^ p *
      exp (I * cuspoidPotential K (cuspoidContour K r) 0) =
      cuspoidContourDir K r * cuspoidContour K r ^ p * ((Real.exp (-|r| ^ (K + 2)) : ℝ) : ℂ) := by
    intro r; congr 1
    simp only [cuspoidPotential, Pi.zero_apply, ofReal_zero, zero_mul, Finset.sum_const_zero,
      add_zero, cuspoidContour_pow]
    rw [ofReal_exp, ← mul_assoc, I_mul_I]; push_cast; ring_nf
  have hint : Integrable fun r : ℝ => cuspoidContourDir K r * cuspoidContour K r ^ p *
      exp (I * cuspoidPotential K (cuspoidContour K r) 0) := by
    have hg : Integrable fun r : ℝ => Real.exp 1 * (|r| ^ p * Real.exp (-1 * r ^ 2)) := by
      have h := integrable_rpow_mul_exp_neg_mul_sq (b := 1) one_pos (s := (p : ℝ))
        (by have := p.cast_nonneg (α := ℝ); linarith)
      refine (h.norm.congr (ae_of_all _ fun r => ?_)).const_mul _
      simp only [Real.rpow_natCast, norm_mul, Real.norm_eq_abs, abs_pow,
        abs_of_pos (Real.exp_pos _)]
    refine hg.mono' ?_ (ae_of_all _ fun r => ?_)
    · simp_rw [hf]
      exact (((measurable_cuspoidContourDir K).mul
        ((measurable_cuspoidContour K).pow_const p)).mul
        (measurable_ofReal.comp (by fun_prop))).aestronglyMeasurable
    · rw [hf, norm_mul, norm_mul, norm_pow, norm_cuspoidContourDir, norm_cuspoidContour,
        norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), one_mul]
      rw [show Real.exp 1 * (|r| ^ p * Real.exp (-1 * r ^ 2)) =
        |r| ^ p * Real.exp (1 + -1 * r ^ 2) by rw [Real.exp_add]; ring]
      gcongr
      have := s36a_pow_ge_sq_sub_one K (abs_nonneg r)
      rw [sq_abs] at this
      linarith
  rw [← intervalIntegral.integral_Iic_add_Ioi hint.integrableOn hint.integrableOn (b := 0)]
  have hR : ∫ r in Ioi (0 : ℝ), cuspoidContourDir K r * cuspoidContour K r ^ p *
      exp (I * cuspoidPotential K (cuspoidContour K r) 0) =
      exp ((cuspoidAngle K : ℂ) * I) ^ (p + 1) * G := by
    rw [← hGi, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun r (hr : 0 < r) => ?_
    rw [hf, cuspoidContour, s36a_dir_of_nonneg K hr.le, abs_of_pos hr]
    push_cast; ring
  have hL : ∫ r in Iic (0 : ℝ), cuspoidContourDir K r * cuspoidContour K r ^ p *
      exp (I * cuspoidPotential K (cuspoidContour K r) 0) =
      (-1) ^ p * cuspoidContourDir K (-1) ^ (p + 1) * G := by
    have := integral_comp_neg_Ioi 0 (fun r => cuspoidContourDir K r * cuspoidContour K r ^ p *
      exp (I * cuspoidPotential K (cuspoidContour K r) 0))
    rw [neg_zero] at this
    rw [← this, ← hGi, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun r (hr : 0 < r) => ?_
    rw [hf, cuspoidContour, s36a_dir_neg (neg_neg_of_pos hr), abs_neg, abs_of_pos hr]
    push_cast; ring
  rw [hL, hR]; ring

/-- `I^p` as an exponential. -/
theorem q2s_I_pow (p : ℕ) : I ^ p = exp (((p * (π / 2) : ℝ) : ℂ) * I) := by
  conv_lhs => rw [← exp_pi_div_two_mul_I]
  rw [← exp_nat_mul]; congr 1; push_cast; ring

/-- `(-I)^p` as an exponential. -/
theorem q2s_negI_pow (p : ℕ) : (-1 : ℂ) ^ p * I ^ p = exp (-(((p * (π / 2) : ℝ) : ℂ) * I)) := by
  rw [← mul_pow, show (-1 : ℂ) * I = -I by ring]
  conv_lhs => rw [← exp_neg_pi_div_two_mul_I]
  rw [← exp_nat_mul]; congr 1; push_cast; ring

/-- `(e^{±iθ})^{p+1}` with `θ = π/(2(K+2))`. -/
theorem q2s_exp_angle_pow (K p : ℕ) (σ : ℝ) : exp ((σ * cuspoidAngle K : ℝ) * I) ^ (p + 1) =
    exp ((σ * ((p + 1) * (π / (2 * ((K : ℝ) + 2)))) : ℝ) * I) := by
  rw [← exp_nat_mul]; congr 1; unfold cuspoidAngle; push_cast; ring

/-- DLMF 36.2.19: `Ψ₂(0, y) = (π/2)√(|y|/2) exp(-iy²/8) (e^{iπ/8} J_{-1/4}(y²/8)
- sign(y) e^{-iπ/8} J_{1/4}(y²/8))`. At `y = 0` the right side is a `0 · ∞` limit (it equals
`Ψ₂(0)`), so the statement is for `y ≠ 0`, where `sign y = ±1`. -/
@[dlmf 36.2.E19]
theorem cuspoidIntegral_two_zero_left {y : ℝ} (hy : y ≠ 0) :
    cuspoidIntegral 2 ![0, y] = π / 2 * (Real.sqrt (|y| / 2) : ℂ) * exp (-I * (y : ℂ) ^ 2 / 8) *
      (exp (I * π / 8) * Complex.besselJ (-1 / 4) ((y : ℂ) ^ 2 / 8) -
        (if 0 < y then 1 else -1 : ℂ) * exp (-I * π / 8) *
          Complex.besselJ (1 / 4) ((y : ℂ) ^ 2 / 8)) := by
  sorry

/-- A ray integral of the elliptic umbilic integrand at `z = 0` as an Airy ray integral:
for `d = i e^{iθ}` and `β³ = 3/2`, `∫₀^∞ d exp(i((rd)³ + c rd)/2) dr = (i/β) P_θ(c/(2β))`. -/
lemma q2s_E_ray (θ : ℝ) {d : ℂ} (hd : d = I * exp (θ * I)) (c : ℂ) {β : ℝ} (hβ : 0 < β)
    (hβ3 : (β : ℂ) ^ 3 = 3 / 2) :
    ∫ r in Ioi (0 : ℝ), d * exp (I * (((r : ℂ) * d) ^ 3 / 2 + c / 2 * ((r : ℂ) * d))) =
      I * (β⁻¹ : ℝ) * DLMF.Airy.rayIntegral
        (fun t => exp (t ^ 3 / 3 - c / (2 * β) * t)) θ 0 := by
  have hβ0 : (β : ℂ) ≠ 0 := ofReal_ne_zero.mpr hβ.ne'
  set g : ℝ → ℂ := fun ρ : ℝ => exp (θ * I) *
    (fun t => exp (t ^ 3 / 3 - c / (2 * β) * t)) ((ρ : ℂ) * exp (θ * I)) with hg
  have h1 : ∀ r ∈ Ioi (0 : ℝ), d * exp (I * (((r : ℂ) * d) ^ 3 / 2 + c / 2 * ((r : ℂ) * d))) =
      I * g (β * r) := by
    intro r _
    simp only [hg, hd]
    push_cast
    set e := exp (θ * I)
    have : I * ((r * (I * e)) ^ 3 / 2 + c / 2 * (r * (I * e))) =
        ((β : ℂ) * r * e) ^ 3 / 3 - c / (2 * β) * ((β : ℂ) * r * e) := by
      have hc : c / (2 * β) * ((β : ℂ) * r * e) = c / 2 * (r * e) := by field_simp
      rw [hc]
      linear_combination ((r : ℂ) ^ 3 * e ^ 3 * (I ^ 2 - 1) / 2 + c * r * e / 2) * I_sq -
        ((r : ℂ) ^ 3 * e ^ 3 / 3) * hβ3
    rw [this]; ring
  rw [setIntegral_congr_fun measurableSet_Ioi h1, integral_const_mul,
    integral_comp_mul_left_Ioi g 0 hβ, mul_zero, hg, DLMF.Airy.rayIntegral, Complex.real_smul]
  ring


/-- The three Airy ray integrals `P_θ(w) = ∫₀^∞ e^{iθ} exp((te^{iθ})³/3 - w t e^{iθ}) dt` at
`θ = -π/3, π/3, π` give `Ai` and `Bi` (DLMF 9.5.4, 9.5.5). -/
lemma q2s_airy_rays (w : ℂ) :
    2 * π * I * DLMF.Airy.airyAi w =
        DLMF.Airy.rayIntegral (fun t => exp (t ^ 3 / 3 - w * t)) (π / 3) 0 -
          DLMF.Airy.rayIntegral (fun t => exp (t ^ 3 / 3 - w * t)) (-π / 3) 0 ∧
      2 * π * DLMF.Airy.airyBi w =
        DLMF.Airy.rayIntegral (fun t => exp (t ^ 3 / 3 - w * t)) (π / 3) 0 +
          DLMF.Airy.rayIntegral (fun t => exp (t ^ 3 / 3 - w * t)) (-π / 3) 0 -
          2 * DLMF.Airy.rayIntegral (fun t => exp (t ^ 3 / 3 - w * t)) π 0 := by
  set Kf : ℂ → ℂ := fun t => exp (t ^ 3 / 3 - w * t) with hKf
  obtain ⟨G, hG⟩ : ∃ G : ℂ → ℂ, ∀ t, HasDerivAt G (Kf t) t := by
    have hd : Differentiable ℂ Kf := by rw [hKf]; fun_prop
    obtain ⟨g, hg⟩ := hd.isExactOn_univ
    exact ⟨g, fun t => hg t (mem_univ t)⟩
  have hKc : Continuous Kf := by rw [hKf]; fun_prop
  have i1 := DLMF.Airy.airyInt_integrableOn_ray w (DLMF.Airy.airyInt_exp_three_mul (-π / 3) (-1)
    (by push_cast; ring))
  have i2 := DLMF.Airy.airyInt_integrableOn_ray w (DLMF.Airy.airyInt_exp_three_mul (π / 3) 0
    (by push_cast; ring))
  have i3 := DLMF.Airy.airyInt_integrableOn_ray w (DLMF.Airy.airyInt_exp_three_mul π 1
    (by push_cast; ring))
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  constructor
  · rw [DLMF.Airy.airyAi_contour_integral, ← hKf,
      DLMF.Airy.airyInt_contourIntegral_eq_rays hG hKc _ _ i1 i2]
    field_simp; ring
  · rw [DLMF.Airy.airyBi_contour_integral, ← hKf,
      DLMF.Airy.airyInt_contourIntegral_eq_rays hG hKc _ _ i3 i2,
      DLMF.Airy.airyInt_contourIntegral_eq_rays hG hKc _ _ i3 i1]
    field_simp; ring

/-- DLMF 36.2.20:
`Ψ^{(E)}(x, y, 0) = 2π²(2/3)^{2/3} Re(Ai((x + iy)/12^{1/3}) Bi((x - iy)/12^{1/3}))`. -/
@[dlmf 36.2.E20]
theorem ellipticUmbilicIntegral_z_zero (x y : ℝ) :
    ellipticUmbilicIntegral x y 0 = 2 * π ^ 2 * ((((2 / 3 : ℝ) ^ (2 / 3 : ℝ)) : ℝ) : ℂ) *
      ((DLMF.Airy.airyAi ((x + I * y) / (((12 : ℝ) ^ (1 / 3 : ℝ) : ℝ) : ℂ)) *
        DLMF.Airy.airyBi ((x - I * y) / (((12 : ℝ) ^ (1 / 3 : ℝ) : ℝ) : ℂ))).re : ℂ) := by
  set β : ℝ := (12 : ℝ) ^ (1 / 3 : ℝ) / 2 with hβdef
  have h12 : (0 : ℝ) < (12 : ℝ) ^ (1 / 3 : ℝ) := by positivity
  have hβ : 0 < β := by positivity
  have h12c : ((12 : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = 12 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  have hβr : β ^ 3 = 3 / 2 := by rw [hβdef, div_pow, h12c]; norm_num
  have hβ3 : (β : ℂ) ^ 3 = 3 / 2 := by rw [← ofReal_pow, hβr]; norm_num
  have h2β : (((12 : ℝ) ^ (1 / 3 : ℝ) : ℝ) : ℂ) = 2 * β := by rw [hβdef]; push_cast; ring
  have hβ2 : (((2 / 3 : ℝ) ^ (2 / 3 : ℝ) : ℝ) : ℂ) = ((β⁻¹ : ℝ) : ℂ) ^ 2 := by
    have : (2 / 3 : ℝ) ^ (2 / 3 : ℝ) = (β⁻¹) ^ 2 := by
      have hpos : (0 : ℝ) ≤ (2 / 3 : ℝ) ^ (2 / 3 : ℝ) := by positivity
      have hc1 : ((2 / 3 : ℝ) ^ (2 / 3 : ℝ)) ^ 3 = 4 / 9 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num [Real.rpow_two]
      have hc2 : (β⁻¹ ^ 2) ^ 3 = 4 / 9 := by
        rw [inv_pow, inv_pow, ← pow_mul, show 2 * 3 = 3 * 2 by rfl, pow_mul, hβr]; norm_num
      exact (pow_left_inj₀ hpos (by positivity) (by norm_num : (3 : ℕ) ≠ 0)).mp
        (hc1.trans hc2.symm)
    rw [this]; push_cast; ring
  set θ : Fin 3 → ℝ := ![-π / 3, π / 3, π] with hθ
  have hs3 : Real.sin (π / 3) = Real.sqrt 3 / 2 := Real.sin_pi_div_three
  have hdir : ∀ j : Fin 3, ellipticUmbilicRayDir j = I * exp ((θ j : ℂ) * I) := by
    intro j
    rw [s36a_rayDir_eq', exp_mul_I, ← ofReal_cos, ← ofReal_sin]
    fin_cases j
    · simp only [hθ, Fin.zero_eta, Matrix.cons_val_zero, Real.cos_neg, Real.sin_neg,
        Real.cos_pi_div_three, neg_div]
      rw [hs3]; push_cast; linear_combination ((Real.sqrt 3 : ℂ) / 2) * I_sq
    · simp only [hθ, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero,
        Real.cos_pi_div_three]
      rw [hs3]; push_cast; linear_combination (-(Real.sqrt 3 : ℂ) / 2) * I_sq
    · simp [hθ]
  set c : ℂ := (x : ℂ) - I * y with hc
  set c' : ℂ := (x : ℂ) + I * y with hc'
  set P : ℝ → ℂ → ℂ := fun t w =>
    DLMF.Airy.rayIntegral (fun s => exp (s ^ 3 / 3 - w * s)) t 0 with hP
  have hR : ∀ (j : Fin 3) (b : ℂ), ∫ r in Ioi (0 : ℝ), ellipticUmbilicRayDir j *
      exp (I * (((r : ℂ) * ellipticUmbilicRayDir j) ^ 3 / 2 +
        b / 2 * ((r : ℂ) * ellipticUmbilicRayDir j))) = I * (β⁻¹ : ℝ) * P (θ j) (b / (2 * β)) :=
    fun j b => q2s_E_ray (θ j) (hdir j) b hβ hβ3
  have hQ : ∀ j k, ellipticUmbilicQuadrant 1 x y 0 j k =
      (I * (β⁻¹ : ℝ) * P (θ j) (c / (2 * β))) * (I * (β⁻¹ : ℝ) * P (θ k) (c' / (2 * β))) := by
    intro j k
    unfold ellipticUmbilicQuadrant
    set f : ℝ → ℂ := fun r : ℝ => ellipticUmbilicRayDir j *
      exp (I * (((r : ℂ) * ellipticUmbilicRayDir j) ^ 3 / 2 +
        c / 2 * ((r : ℂ) * ellipticUmbilicRayDir j))) with hf
    set g : ℝ → ℂ := fun q : ℝ => ellipticUmbilicRayDir k *
      exp (I * (((q : ℂ) * ellipticUmbilicRayDir k) ^ 3 / 2 +
        c' / 2 * ((q : ℂ) * ellipticUmbilicRayDir k))) with hg
    have hfac : (fun p : ℝ × ℝ => ellipticUmbilicRayDir j * ellipticUmbilicRayDir k *
        exp (I * ((1 : ℝ) : ℂ) * ellipticUmbilicPotentialAB ((p.1 : ℂ) * ellipticUmbilicRayDir j)
          ((p.2 : ℂ) * ellipticUmbilicRayDir k) x y 0)) =
        fun p : ℝ × ℝ => f p.1 * g p.2 := by
      funext p
      simp only [hf, hg, ellipticUmbilicPotentialAB_eq, ofReal_zero, ofReal_one, zero_mul,
        add_zero, mul_one]
      rw [mul_mul_mul_comm (ellipticUmbilicRayDir j), ← exp_add]
      congr 2
      all_goals (try simp only [hc, hc'])
      all_goals ring
    rw [hfac, Measure.volume_eq_prod, setIntegral_prod_mul f g, hf, hg, hR, hR]
  have hw : conj ((x + I * y) / (((12 : ℝ) ^ (1 / 3 : ℝ) : ℝ) : ℂ)) =
      (x - I * y) / (((12 : ℝ) ^ (1 / 3 : ℝ) : ℝ) : ℂ) := by
    simp [map_div₀, conj_ofReal]
    ring
  have hw' : conj ((x - I * y) / (((12 : ℝ) ^ (1 / 3 : ℝ) : ℝ) : ℂ)) =
      (x + I * y) / (((12 : ℝ) ^ (1 / 3 : ℝ) : ℝ) : ℂ) := by
    simp [map_div₀, conj_ofReal, sub_eq_add_neg]
  have hre : ∀ X : ℂ, ((X.re : ℝ) : ℂ) = (X + conj X) / 2 := by
    intro X; rw [add_conj]; push_cast; ring
  rw [hre, map_mul, ← DLMF.Airy.airyAi_conj, ← DLMF.Airy.airyBi_conj, hw, hw', h2β, hβ2,
    ← hc, ← hc']
  have hA : 2 * π * I * DLMF.Airy.airyAi (c / (2 * β)) =
      P (π / 3) (c / (2 * β)) - P (-π / 3) (c / (2 * β)) := (q2s_airy_rays _).1
  have hB : 2 * π * DLMF.Airy.airyBi (c / (2 * β)) =
      P (π / 3) (c / (2 * β)) + P (-π / 3) (c / (2 * β)) - 2 * P π (c / (2 * β)) :=
    (q2s_airy_rays _).2
  have hA' : 2 * π * I * DLMF.Airy.airyAi (c' / (2 * β)) =
      P (π / 3) (c' / (2 * β)) - P (-π / 3) (c' / (2 * β)) := (q2s_airy_rays _).1
  have hB' : 2 * π * DLMF.Airy.airyBi (c' / (2 * β)) =
      P (π / 3) (c' / (2 * β)) + P (-π / 3) (c' / (2 * β)) - 2 * P π (c' / (2 * β)) :=
    (q2s_airy_rays _).2
  clear_value P
  have e00 : ellipticUmbilicCycle 0 0 = -1 := rfl
  have e01 : ellipticUmbilicCycle 0 1 = 0 := rfl
  have e02 : ellipticUmbilicCycle 0 2 = 1 := rfl
  have e10 : ellipticUmbilicCycle 1 0 = 0 := rfl
  have e11 : ellipticUmbilicCycle 1 1 = 1 := rfl
  have e12 : ellipticUmbilicCycle 1 2 = -1 := rfl
  have e20 : ellipticUmbilicCycle 2 0 = 1 := rfl
  have e21 : ellipticUmbilicCycle 2 1 = -1 := rfl
  have e22 : ellipticUmbilicCycle 2 2 = 0 := rfl
  have t0 : θ 0 = -π / 3 := rfl
  have t1 : θ 1 = π / 3 := rfl
  have t2 : θ 2 = π := rfl
  unfold ellipticUmbilicIntegral
  simp only [hQ, Fin.sum_univ_three, e00, e01, e02, e10, e11, e12, e20, e21, e22, t0, t1, t2]
  set A := DLMF.Airy.airyAi (c / (2 * β))
  set B := DLMF.Airy.airyBi (c / (2 * β))
  set A' := DLMF.Airy.airyAi (c' / (2 * β))
  set B' := DLMF.Airy.airyBi (c' / (2 * β))
  have hP1 : P (π / 3) (c / (2 * β)) = P (-π / 3) (c / (2 * β)) + 2 * π * I * A := by
    linear_combination -hA
  have hP2 : P π (c / (2 * β)) = P (-π / 3) (c / (2 * β)) + π * I * A - π * B := by
    linear_combination (1 / 2 : ℂ) * hB - (1 / 2 : ℂ) * hA
  have hP1' : P (π / 3) (c' / (2 * β)) = P (-π / 3) (c' / (2 * β)) + 2 * π * I * A' := by
    linear_combination -hA'
  have hP2' : P π (c' / (2 * β)) = P (-π / 3) (c' / (2 * β)) + π * I * A' - π * B' := by
    linear_combination (1 / 2 : ℂ) * hB' - (1 / 2 : ℂ) * hA'
  rw [hP1, hP2, hP1', hP2']
  push_cast
  linear_combination (I ^ 2 - 1) * π ^ 2 * (β : ℂ)⁻¹ ^ 2 * (A * B' + B * A') * I_sq

/-- DLMF 36.2.28 (§36.2(iv), Berry–Howls): for `z ≥ 0`,
`Ψ^{(E)}(0, 0, z) = conj Ψ^{(E)}(0, 0, -z) = 2π√(πz/27) exp(2iz³/27) (J_{-1/6}(2z³/27)
+ i J_{1/6}(2z³/27))`. The first equality is 36.2.24. At `z = 0` the right side is read as its
limit `Ψ^{(E)}(0)`, so the Bessel form is stated for `z > 0`. -/
@[dlmf 36.2.E28]
theorem ellipticUmbilicIntegral_axis {z : ℝ} (hz : 0 < z) :
    ellipticUmbilicIntegral 0 0 z = 2 * π * (Real.sqrt (π * z / 27) : ℂ) *
      exp (2 / 27 * I * (z : ℂ) ^ 3) * (Complex.besselJ (-1 / 6) (2 / 27 * (z : ℂ) ^ 3) +
        I * Complex.besselJ (1 / 6) (2 / 27 * (z : ℂ) ^ 3)) := by
  sorry

/-- DLMF 36.2.29 (§36.2(iv), Berry–Howls): for real `z`, `Ψ^{(H)}(0, 0, z)` equals
`conj Ψ^{(H)}(0, 0, -z) = (2^{1/3}/√3) exp(iz³/27) Ψ^{(E)}(0, 0, -z/2^{2/3})`. The first
equality is 36.2.24. -/
@[dlmf 36.2.E29]
theorem hyperbolicUmbilicIntegral_axis (z : ℝ) :
    hyperbolicUmbilicIntegral 0 0 z = (((2 : ℝ) ^ (1 / 3 : ℝ) : ℝ) : ℂ) / (Real.sqrt 3 : ℂ) *
      exp (I * (z : ℂ) ^ 3 / 27) * ellipticUmbilicIntegral 0 0 (-z / (2 : ℝ) ^ (2 / 3 : ℝ)) := by
  sorry

end DLMF.CoalescingSaddles
