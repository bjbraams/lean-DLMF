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
# Canonical saddle contours and symmetries

Rotated cuspoid contours, elementary special cases and symmetries of the canonical umbilic
integrals.

Source references and common attribution are retained in
`DLMF.CoalescingSaddles.CanonicalIntegrals`.
-/

@[expose] public noncomputable section

open Complex MeasureTheory Set Filter

open scoped Real Topology ComplexConjugate

namespace DLMF.CoalescingSaddles

/-- `(K + 2) · θ_K = π/2` for the cuspoid contour angle `θ_K`. -/
lemma s36a_angle_mul (K : ℕ) : ((K : ℝ) + 2) * cuspoidAngle K = π / 2 := by
  unfold cuspoidAngle; field_simp

/-- `(e^{iθ_K})^{K+2} = i`. -/
lemma s36a_exp_angle_pow (K : ℕ) : exp ((cuspoidAngle K : ℂ) * I) ^ (K + 2) = I := by
  rw [← exp_nat_mul]
  have : ((K + 2 : ℕ) : ℂ) * ((cuspoidAngle K : ℂ) * I) = (π / 2 : ℝ) * I := by
    rw [← s36a_angle_mul]; push_cast; ring
  rw [this]; push_cast; exact exp_pi_div_two_mul_I

/-- `(e^{-iθ_K})^{K+2} = -i`. -/
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

/-- The cuspoid contour point at parameter `r` has modulus `|r|`. -/
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

/-- The direction factor of the cuspoid contour is measurable. -/
theorem measurable_cuspoidContourDir (K : ℕ) : Measurable (cuspoidContourDir K) := by
  unfold cuspoidContourDir
  exact Measurable.ite ((measurableSet_le measurable_const measurable_id).union
    (MeasurableSet.const _)) measurable_const measurable_const

/-- The cuspoid contour parametrization is measurable. -/
theorem measurable_cuspoidContour (K : ℕ) : Measurable (cuspoidContour K) :=
  measurable_ofReal.mul (measurable_cuspoidContourDir K)

/-- The cuspoid potential is continuous in `t`. -/
theorem continuous_cuspoidPotential (K : ℕ) (x : Fin K → ℝ) :
    Continuous fun t => cuspoidPotential K t x := by
  unfold cuspoidPotential; fun_prop

/-- `a^j ≤ 1 + a^K` for `a ≥ 0` and `j ≤ K`. -/
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

/-- `a² - 1 ≤ a^{K+2}` for `a ≥ 0`. -/
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

/-- The cuspoid contour integrand `r ↦ dir(r) exp(iκ Φ_K(t(r); x))` is measurable. -/
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

/-- For even `K` the contour direction is `e^{iθ_K}` on the whole line. -/
theorem s36a_dir_of_even {K : ℕ} (hK : Even K) (r : ℝ) :
    cuspoidContourDir K r = exp ((cuspoidAngle K : ℂ) * I) := by
  simp [cuspoidContourDir, hK]

/-- For `r ≥ 0` the contour direction is `e^{iθ_K}`. -/
theorem s36a_dir_of_nonneg (K : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    cuspoidContourDir K r = exp ((cuspoidAngle K : ℂ) * I) := by
  simp [cuspoidContourDir, hr]

/-- For odd `K` and `r < 0` the contour direction is `e^{-iθ_K}`. -/
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

/-- `∫_0^∞ e^{-r^n} dr = Γ(1/n + 1)` for `n > 0`. -/
theorem s36a_integral_exp_neg_pow (n : ℕ) (hn : 0 < n) :
    ∫ r in Ioi (0 : ℝ), Real.exp (-r ^ n) = Real.Gamma (1 / n + 1) := by
  rw [← integral_exp_neg_rpow (by exact_mod_cast hn : (0 : ℝ) < n)]
  refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
  simp [Real.rpow_natCast]

/-- The contour direction at `r = -1`: `e^{iθ_K}` for even `K` and `e^{-iθ_K}` for odd `K`. -/
theorem s36a_dir_neg_one (K : ℕ) : cuspoidContourDir K (-1) =
    if Even K then exp ((cuspoidAngle K : ℂ) * I) else exp (-(cuspoidAngle K : ℂ) * I) := by
  have h : ¬ (0 : ℝ) ≤ -1 := by norm_num
  by_cases hK : Even K <;> simp [cuspoidContourDir, h, hK]

/-- The contour direction is constant on the negative half line. -/
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

/-- Complex conjugation commutes with the (real-coefficient) cuspoid potential. -/
theorem conj_cuspoidPotential (K : ℕ) (t : ℂ) (x : Fin K → ℝ) :
    conj (cuspoidPotential K t x) = cuspoidPotential K (conj t) x := by
  simp [cuspoidPotential, map_sum, conj_ofReal]

/-- For even `K`, `Φ_K(-t; x) = Φ_K(t; x')` with `x'_m = (-1)^{m+1} x_m`. -/
lemma s36a_potential_neg_even {K : ℕ} (hK : Even K) (t : ℂ) (x : Fin K → ℝ) :
    cuspoidPotential K (-t) x = cuspoidPotential K t (fun m => (-1) ^ ((m : ℕ) + 1) * x m) := by
  unfold cuspoidPotential
  rw [(hK.add even_two).neg_pow]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [neg_pow]; push_cast; ring

/-- For odd `K`, `Φ_K(-t; x) = -Φ_K(t; x')` with `x'_m = (-1)^m x_m`. -/
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

/-- The fold ray integral along `arg t = π/6` equals `i w(x)`, with `w` the Airy ray integral. -/
lemma s36a_airy_ray (x : ℝ) :
    ∫ r in Ioi (0 : ℝ), exp (((π / 6 : ℝ) : ℂ) * I) *
      DLMF.Airy.airyInt_osc x (r * exp (((π / 6 : ℝ) : ℂ) * I)) = I * DLMF.Airy.airyInt_w x := by
  rw [DLMF.Airy.airyInt_w, DLMF.Airy.rayIntegral, ← integral_const_mul]
  exact setIntegral_congr_fun measurableSet_Ioi fun r _ => DLMF.Airy.airyInt_osc_rotate x r

/-- For `K = 1` the sign flip `x_m ↦ (-1)^m x_m` is the identity. -/
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

/-- For odd `K` and `r ≠ 0`, the conjugate of the direction at `-r` is the direction at `r`. -/
lemma s36a_conj_dir_neg {K : ℕ} (hK : ¬ Even K) {r : ℝ} (hr : r ≠ 0) :
    conj (cuspoidContourDir K (-r)) = cuspoidContourDir K r := by
  rcases lt_or_gt_of_ne hr with h | h
  · rw [s36a_dir_of_nonneg K (by linarith), s36a_dir_of_odd_neg hK h, ← exp_conj]
    congr 1; simp [conj_ofReal]
  · rw [s36a_dir_of_odd_neg hK (by linarith), s36a_dir_of_nonneg K h.le, ← exp_conj]
    congr 1; simp [conj_ofReal]

/-- For odd `K` and `r ≠ 0`, the conjugate of the contour point at `-r` is minus the point at `r`.
-/
lemma s36a_conj_contour_neg {K : ℕ} (hK : ¬ Even K) {r : ℝ} (hr : r ≠ 0) :
    conj (cuspoidContour K (-r)) = -cuspoidContour K r := by
  simp only [cuspoidContour, map_mul, conj_ofReal, s36a_conj_dir_neg hK hr]; push_cast; ring

/-- Almost every point of `ℝ²` has both coordinates nonzero. -/
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

/-- The three elliptic umbilic ray directions are `±√3/2 + i/2` and `-i`. -/
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

/-- The three elliptic umbilic ray directions are `±√3/2 + i/2` and `-i` (complex `√3` form). -/
lemma s36a_rayDir_eq' (j : Fin 3) : ellipticUmbilicRayDir j =
    ![(Real.sqrt 3 : ℂ) / 2 + I / 2, -(Real.sqrt 3 : ℂ) / 2 + I / 2, -I] j := by
  rw [s36a_rayDir_eq]; fin_cases j <;> simp; ring

/-- The elliptic umbilic cycle coefficients `ε_{jk}` are symmetric. -/
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
  have hs := Airy.sqrt_three_sq
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

/-- Conjugation permutes the elliptic umbilic ray directions up to sign: `conj ρ_j = -ρ_{σ j}` with
`σ = (0 1)`. -/
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

/-- Each elliptic umbilic ray direction `ρ_j` satisfies `ρ_j³ = i`. -/
theorem s36a_rayDir_cube (j : Fin 3) : ellipticUmbilicRayDir j ^ 3 = I := by
  have hs := Airy.sqrt_three_sq
  rw [s36a_rayDir_eq']
  fin_cases j <;> simp
  · linear_combination (3 * I / 8 + (Real.sqrt 3 : ℂ) / 8) * hs +
      (I / 8 + 3 * (Real.sqrt 3 : ℂ) / 8) * I_sq
  · linear_combination (3 * I / 8 - (Real.sqrt 3 : ℂ) / 8) * hs +
      (I / 8 - 3 * (Real.sqrt 3 : ℂ) / 8) * I_sq
  · linear_combination (-I) * I_sq

/-- For `d³ = i`, `∫_0^∞ d exp(i (rd)³/2) dr = d (1/2)^{-1/3} Γ(4/3)`. -/
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

end DLMF.CoalescingSaddles
end
