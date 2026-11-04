/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Airy.Scorer.Representations
public import DLMFMathlib.Analysis.Integral.PrincipalValue

/-!
# Scorer asymptotic expansions and real zeros

Asymptotic expansions of `Gi`, `Hi` and their derivatives (DLMF 9.12.25–9.12.28), obtained by
rotating a Laplace contour, and the real zeros of `Gi` and `Gi'` (DLMF §9.12).

## Main definitions

* `ScorerExpansions.laplace`, `ScorerExpansions.coeff`: the Laplace integral and the Taylor
  coefficients of `e^{-t³/3}`.
* `ScorerZeros.gi`, `ScorerZeros.gi'`, `ScorerZeros.hi`: `Gi`, `Gi'`, `Hi` on the real axis.

## Main results

* `scorerGi_asymptotic`, `scorerGiDeriv_asymptotic`: DLMF 9.12.25, 9.12.26.
* `scorerHi_asymptotic`, `scorerHiDeriv_asymptotic`: DLMF 9.12.27, 9.12.28.
* `scorerGi_nonneg_ne_zero`, `scorerGiDeriv_unique_nonneg_zero`: `Gi` has no zeros on
  `[0, ∞)` and `Gi'` exactly one.
* `scorerGi_infinite_negative_zeros`, `scorerGiDeriv_infinite_negative_zeros`,
  `scorerGi_zeros_interlace`, `scorerGiDeriv_zeros_interlace`: infinitely many negative zeros
  and interlacing, proved with the decreasing energy `Gi'² - x Gi² + 2 Gi/π`.
* `scorerGiDeriv_ne_zero_of_scorerGi_ofReal_eq_zero`: the real zeros of `Gi` are simple.
* `scorerGi_principalValue_converges`: convergence of the principal value in DLMF 9.12.23.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF.Confluent

open scoped Real Topology Nat

open DLMF.Core

namespace DLMF.Airy

macro "sqrt3_ring" : tactic =>
  `(tactic| (ring_nf; simp only [sqrt_three_sq, sqrt_three_pow_three_complex,
    sqrt_three_pow_four, I_sq, I_pow_three]; ring_nf))

/-! ### Asymptotic expansions of Hi, Hi', Gi, Gi' (DLMF 9.12(viii))

The Laplace integrals `π Hi(z) = ∫₀^∞ e^{zt} e^{-t³/3} dt` and
`π Hi'(z) = ∫₀^∞ e^{zt} t e^{-t³/3} dt` are rotated to rays `|arg t| < π/6` and expanded by Watson's
lemma (`hasAsymptoticExpansion_integral_cexp_smul_rotate_comap`); two rotated rays cover the sector
`|arg(-z)| < 2π/3`. The expansions of `Gi`, `Gi'` follow from the rotation formula 9.12.12. -/

/-- The cubic kernel `e^{-t³/3}` along the ray `t = r e^{iy}`. -/
theorem ScorerExpansions.norm_kernel (r y : ℝ) :
    ‖cexp (-(((r : ℂ) * exp (y * I)) ^ 3 / 3))‖ = Real.exp (-(r ^ 3 * Real.cos (3 * y)) / 3) := by
  rw [Complex.norm_exp]
  congr 1
  have h : ((r : ℂ) * exp (y * I)) ^ 3 = ((r ^ 3 : ℝ) : ℂ) * exp (((3 * y : ℝ) : ℂ) * I) := by
    rw [mul_pow, ← Complex.exp_nat_mul]; push_cast; ring_nf
  rw [h, neg_re, div_ofNat_re, re_ofReal_mul, exp_ofReal_mul_I_re]
  ring

/-- The cubic kernel is bounded by `1` in the sector `|arg t| ≤ π/6`. -/
theorem ScorerExpansions.norm_kernel_le_one {r : ℝ} (hr : 0 ≤ r) {y : ℝ} (hy : |y| ≤ π / 6) :
    ‖cexp (-(((r : ℂ) * exp (y * I)) ^ 3 / 3))‖ ≤ 1 := by
  rw [ScorerExpansions.norm_kernel, Real.exp_le_one_iff]
  have : 0 ≤ Real.cos (3 * y) := by
    rw [← Real.cos_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [abs_nonneg y, Real.pi_pos], by linarith⟩
  have := mul_nonneg (pow_nonneg hr 3) this
  linarith

/-- `r^m e^{-cr - br³}` is integrable on `(0, ∞)` for `b > 0`. -/
theorem ScorerExpansions.integrableOn_pow_exp (m : ℕ) (c : ℝ) {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun r : ℝ => r ^ m * Real.exp (-c * r - b * r ^ 3)) (Ioi 0) := by
  set A : ℝ := |c| + 2
  set R : ℝ := Real.sqrt (A / b)
  have hA : 2 ≤ A := by simp only [A]; linarith [abs_nonneg c]
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hR2 : R ^ 2 = A / b := Real.sq_sqrt (by positivity)
  have hint : IntegrableOn (fun r : ℝ => (m.factorial * Real.exp (A * R)) * Real.exp (-1 * r))
      (Ioi 0) := (exp_neg_integrableOn_Ioi 0 one_pos).const_mul _
  refine hint.mono' (Continuous.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r (hr : 0 < r)
  rw [norm_mul, norm_pow, Real.norm_of_nonneg hr.le, Real.norm_of_nonneg (Real.exp_pos _).le]
  have h1 : r ^ m ≤ m.factorial * Real.exp r := by
    have := Real.pow_div_factorial_le_exp r hr.le m
    rwa [div_le_iff₀ (by positivity), mul_comm] at this
  have hc : -c * r ≤ (A - 2) * r := by
    have := neg_abs_le c
    have : -c ≤ A - 2 := by simp only [A]; linarith
    nlinarith
  have h2 : -c * r - b * r ^ 3 ≤ A * R + -1 * r - r := by
    rcases le_or_gt R r with h | h
    · have : A * r ≤ b * r ^ 3 := by
        have hb2 : A = b * R ^ 2 := by rw [hR2]; field_simp
        rw [hb2]
        have : R ^ 2 ≤ r ^ 2 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg hb.le hr.le)]
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ A) hR0]
    · have : 0 ≤ b * r ^ 3 := by positivity
      nlinarith
  calc r ^ m * Real.exp (-c * r - b * r ^ 3)
      ≤ (m.factorial * Real.exp r) * Real.exp (A * R + -1 * r - r) :=
        mul_le_mul h1 (Real.exp_le_exp.mpr h2) (Real.exp_pos _).le (by positivity)
    _ = (m.factorial * Real.exp (A * R)) * Real.exp (-1 * r) := by
        rw [mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add]; ring_nf

/-- The rotated kernel `(re^{iθ})^m e^{-(re^{iθ})³/3}` is Laplace-integrable for `|θ| < π/6`. -/
theorem ScorerExpansions.integrableOn_rotate (m : ℕ) (c : ℝ) {θ : ℝ} (hθ : |θ| < π / 6) :
    IntegrableOn (fun r : ℝ => Real.exp (-c * r) •
      (((r : ℂ) * exp (θ * I)) ^ m * cexp (-(((r : ℂ) * exp (θ * I)) ^ 3 / 3)))) (Ioi 0) := by
  have hb : 0 < Real.cos (3 * θ) / 3 := by
    have : 0 < Real.cos (3 * θ) := by
      rw [← Real.cos_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
      exact Real.cos_pos_of_mem_Ioo ⟨by linarith [abs_nonneg θ, Real.pi_pos], by linarith⟩
    positivity
  refine (ScorerExpansions.integrableOn_pow_exp m c hb).mono' ?_ ?_
  · exact (Continuous.aestronglyMeasurable (by fun_prop))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r (hr : 0 < r)
    rw [norm_smul, norm_mul, norm_pow, norm_mul, norm_real, norm_exp_ofReal_mul_I, mul_one,
      ScorerExpansions.norm_kernel, Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.norm_of_nonneg hr.le, ← mul_assoc, mul_comm (Real.exp _), mul_assoc, ← Real.exp_add]
    apply le_of_eq; congr 2; ring

/-- The Laplace integral `∫₀^∞ e^{-wt} t^m e^{-t³/3} dt` (an entire function of `w`). -/
noncomputable def ScorerExpansions.laplace (m : ℕ) (w : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), cexp (-(w * t)) • ((t : ℂ) ^ m * cexp (-((t : ℂ) ^ 3 / 3)))

/-- `e^{-ct} tᵐ e^{-t³/3}` is integrable on `(0, ∞)` for every real `c`. -/
theorem ScorerExpansions.integrableOn_zero (m : ℕ) (c : ℝ) :
    IntegrableOn (fun t : ℝ => Real.exp (-c * t) • ((t : ℂ) ^ m * cexp (-((t : ℂ) ^ 3 / 3))))
      (Ioi 0) := by
  have h := ScorerExpansions.integrableOn_rotate m c (θ := 0) (by rw [abs_zero]; positivity)
  simpa using h

/-- The Laplace integral `∫₀^∞ e^{-wt} tᵐ e^{-t³/3} dt` is an entire function of `w`. -/
theorem ScorerExpansions.differentiable_laplace (m : ℕ) : Differentiable ℂ
    (ScorerExpansions.laplace m) :=
  fun w => (differentiableOn_integral_cexp_neg_mul_smul
    (ScorerExpansions.integrableOn_zero m (w.re - 1))).differentiableAt
    ((isOpen_lt continuous_const continuous_re).mem_nhds (by simp))

/-- Hi and Hi' as Laplace integrals: `π Hi(z) = L₀(-z)`, `π Hi'(z) = L₁(-z)`. -/
theorem ScorerExpansions.scorerHi_eq (z : ℂ) : π * scorerHi z =
    ScorerExpansions.laplace 0 (-z) := by
  rw [(scorerHi_exp_integral z).2, ScorerExpansions.laplace, mul_div_cancel₀ _
    (ofReal_ne_zero.mpr Real.pi_ne_zero)]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [smul_eq_mul, pow_zero, one_mul]
  rw [← Complex.exp_add]; ring_nf

/-- `π Hi'(z) = L₁(-z)`, the Laplace integral of `t e^{-t³/3}` at `-z`. -/
theorem ScorerExpansions.scorerHiDeriv_eq (z : ℂ) : π * scorerHiDeriv z =
    ScorerExpansions.laplace 1 (-z) := by
  rw [scorerHiDeriv_exp_integral z, ScorerExpansions.laplace, mul_div_cancel₀ _
    (ofReal_ne_zero.mpr Real.pi_ne_zero)]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [smul_eq_mul, pow_one]
  rw [mul_left_comm, ← Complex.exp_add]; ring_nf

/-- **Rotation of the Laplace contour** for `|θ| < π/6`, valid for every complex `w`. -/
theorem ScorerExpansions.laplace_rotate (m : ℕ) {θ : ℝ} (hθ : |θ| < π / 6) (w : ℂ) :
    ScorerExpansions.laplace m w = exp (θ * I) • ∫ r in Ioi (0 : ℝ), cexp (-(w * exp (θ * I) * r)) •
      (((r : ℂ) * exp (θ * I)) ^ m * cexp (-(((r : ℂ) * exp (θ * I)) ^ 3 / 3))) := by
  have hd2 : Differentiable ℂ (fun w : ℂ => exp (θ * I) • ∫ r in Ioi (0 : ℝ),
      cexp (-(w * exp (θ * I) * r)) •
        (((r : ℂ) * exp (θ * I)) ^ m * cexp (-(((r : ℂ) * exp (θ * I)) ^ 3 / 3)))) := by
    have hL : Differentiable ℂ (fun v : ℂ => ∫ r in Ioi (0 : ℝ), cexp (-(v * r)) •
        (((r : ℂ) * exp (θ * I)) ^ m * cexp (-(((r : ℂ) * exp (θ * I)) ^ 3 / 3)))) := fun v =>
      (differentiableOn_integral_cexp_neg_mul_smul
        (ScorerExpansions.integrableOn_rotate m (v.re - 1) hθ)).differentiableAt
        ((isOpen_lt continuous_const continuous_re).mem_nhds (by simp))
    exact (hL.comp (differentiable_id.mul_const (exp (θ * I)))).const_smul (exp (θ * I))
  have hy : ∀ y ∈ uIcc 0 θ, |y| ≤ π / 6 := fun y hy =>
    (abs_le_abs_of_mem_uIcc_zero hy).trans hθ.le
  have hreal : ∀ x : ℝ, 0 < x → ScorerExpansions.laplace m x = exp (θ * I) • ∫ r in Ioi (0 : ℝ),
      cexp (-((x : ℂ) * exp (θ * I) * r)) •
        (((r : ℂ) * exp (θ * I)) ^ m * cexp (-(((r : ℂ) * exp (θ * I)) ^ 3 / 3))) := by
    intro x hx
    simp only [ScorerExpansions.laplace, smul_eq_mul]
    refine integral_cexp_neg_mul_mul_eq_rotate (F := fun t => t ^ m * cexp (-(t ^ 3 / 3)))
      (σ := m + 1) (C := 1) (k := m) (by positivity) (fun r _ y _ => by fun_prop)
      (fun r hr _ y hy' => ?_) (fun r hr y hy' => ?_) (fun y hy' => ?_)
    · rw [add_sub_cancel_right, one_mul, Real.rpow_natCast, norm_mul, norm_pow, norm_mul,
        norm_real, Real.norm_of_nonneg hr.le, norm_exp_ofReal_mul_I, mul_one]
      calc r ^ m * _ ≤ r ^ m * 1 := by
            gcongr; exact ScorerExpansions.norm_kernel_le_one hr.le (hy y hy')
        _ = r ^ m := mul_one _
    · have hr0 : 0 ≤ r := by linarith
      rw [one_mul, Real.rpow_natCast, norm_mul, norm_pow, norm_mul,
        norm_real, Real.norm_of_nonneg hr0, norm_exp_ofReal_mul_I, mul_one]
      calc r ^ m * _ ≤ r ^ m * 1 := by
            gcongr; exact ScorerExpansions.norm_kernel_le_one hr0 (hy y hy')
        _ = r ^ m := mul_one _
    · rw [re_ofReal_mul, exp_ofReal_mul_I_re]
      have := hy y hy'
      exact mul_pos hx (Real.cos_pos_of_mem_Ioo ⟨by linarith [neg_abs_le y, Real.pi_pos],
        by linarith [le_abs_self y, Real.pi_pos]⟩)
  have hfreq : ∃ᶠ v in 𝓝[≠] (1 : ℂ), ScorerExpansions.laplace m v = exp (θ * I) •
      ∫ r in Ioi (0 : ℝ), cexp (-(v * exp (θ * I) * r)) •
        (((r : ℂ) * exp (θ * I)) ^ m * cexp (-(((r : ℂ) * exp (θ * I)) ^ 3 / 3))) := by
    have ht : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[≠] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have := (continuous_ofReal.tendsto (1 : ℝ)).mono_left
          (nhdsWithin_le_nhds (s := ({1}ᶜ : Set ℝ)))
        rwa [ofReal_one] at this
      · filter_upwards [self_mem_nhdsWithin] with r hr
        simpa using hr
    apply ht.frequently
    apply Eventually.frequently
    filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds (zero_lt_one' ℝ))] with r hr
    exact hreal r hr
  exact ((ScorerExpansions.differentiable_laplace m).differentiableOn.analyticOnNhd
    isOpen_univ).eqOn_of_preconnected_of_frequently_eq
    (hd2.differentiableOn.analyticOnNhd isOpen_univ) isPreconnected_univ (mem_univ _) hfreq
    (mem_univ w)

/-- Taylor coefficients of `e^{-t³/3} = ∑ aₙ tⁿ`. -/
noncomputable def ScorerExpansions.coeff (n : ℕ) : ℂ :=
  if 3 ∣ n then (-1 / 3 : ℂ) ^ (n / 3) / ((n / 3).factorial : ℂ) else 0

/-- Partial sums of the Taylor series `∑ aₙ tⁿ` of `e^{-t³/3}` up to `3M`, `3M+1` and `3M+2` terms
equal the partial sums of the exponential series in `-t³/3`. -/
theorem ScorerExpansions.sum_coeff (t : ℂ) (M : ℕ) :
    (∑ n ∈ Finset.range (3 * M), t ^ n * ScorerExpansions.coeff n =
      ∑ k ∈ Finset.range M, (-(t ^ 3 / 3)) ^ k / (k.factorial : ℂ)) ∧
    (∑ n ∈ Finset.range (3 * M + 1), t ^ n * ScorerExpansions.coeff n =
      ∑ k ∈ Finset.range (M + 1), (-(t ^ 3 / 3)) ^ k / (k.factorial : ℂ)) ∧
    (∑ n ∈ Finset.range (3 * M + 2), t ^ n * ScorerExpansions.coeff n =
      ∑ k ∈ Finset.range (M + 1), (-(t ^ 3 / 3)) ^ k / (k.factorial : ℂ)) := by
  have h0 : ∀ M : ℕ, ∑ n ∈ Finset.range (3 * M), t ^ n * ScorerExpansions.coeff n =
      ∑ k ∈ Finset.range M, (-(t ^ 3 / 3)) ^ k / (k.factorial : ℂ) := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      rw [show 3 * (M + 1) = 3 * M + 1 + 1 + 1 by ring, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]
      have h1 : ¬ 3 ∣ 3 * M + 1 := by omega
      have h2 : ¬ 3 ∣ 3 * M + 1 + 1 := by omega
      have h3 : (3 * M) / 3 = M := by omega
      simp only [ScorerExpansions.coeff, h1, h2, ite_false, mul_zero, add_zero,
        dvd_mul_right, ite_true, h3]
      congr 1
      rw [pow_mul, neg_pow, div_pow]
      field_simp
      rw [div_pow]; field_simp
  have h1 : ∑ n ∈ Finset.range (3 * M + 1), t ^ n * ScorerExpansions.coeff n =
      ∑ k ∈ Finset.range (M + 1), (-(t ^ 3 / 3)) ^ k / (k.factorial : ℂ) := by
    rw [Finset.sum_range_succ, h0, Finset.sum_range_succ]
    have h3 : (3 * M) / 3 = M := by omega
    simp only [ScorerExpansions.coeff, dvd_mul_right, ite_true, h3]
    congr 1
    rw [pow_mul, neg_pow, div_pow]
    field_simp
    rw [div_pow]; field_simp
  refine ⟨h0 M, h1, ?_⟩
  rw [Finset.sum_range_succ, h1]
  have h2 : ¬ 3 ∣ 3 * M + 1 := by omega
  simp [ScorerExpansions.coeff, h2]

/-- Taylor remainders of `t^m e^{-t³/3}` along a ray, as required by Watson's lemma. -/
theorem ScorerExpansions.sub_sum_isBigO (m : ℕ) (θ : ℝ) (N : ℕ) :
    (fun r : ℝ => ((r : ℂ) * exp (θ * I)) ^ m * cexp (-(((r : ℂ) * exp (θ * I)) ^ 3 / 3)) -
      ∑ n ∈ Finset.range N,
        (((r : ℂ) * exp (θ * I)) ^ ((n : ℂ) + ((m : ℂ) + 1) - 1)) • ScorerExpansions.coeff n)
      =O[𝓝[>] 0] fun r => r ^ ((N : ℝ) + ((m : ℂ) + 1).re - 1) := by
  obtain ⟨M, hM⟩ : ∃ M : ℕ, N ≤ 3 * M ∧
      ∀ t : ℂ, ∑ n ∈ Finset.range N, t ^ n * ScorerExpansions.coeff n =
        ∑ k ∈ Finset.range M, (-(t ^ 3 / 3)) ^ k / (k.factorial : ℂ) := by
    rcases (by omega : N % 3 = 0 ∨ N % 3 = 1 ∨ N % 3 = 2) with h | h | h
    · obtain ⟨q, rfl⟩ : ∃ q, N = 3 * q := ⟨N / 3, by omega⟩
      exact ⟨q, le_rfl, fun t => (ScorerExpansions.sum_coeff t q).1⟩
    · obtain ⟨q, rfl⟩ : ∃ q, N = 3 * q + 1 := ⟨N / 3, by omega⟩
      exact ⟨q + 1, by omega, fun t => (ScorerExpansions.sum_coeff t q).2.1⟩
    · obtain ⟨q, rfl⟩ : ∃ q, N = 3 * q + 2 := ⟨N / 3, by omega⟩
      exact ⟨q + 1, by omega, fun t => (ScorerExpansions.sum_coeff t q).2.2⟩
  refine IsBigO.of_bound 3 ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds (zero_lt_one' ℝ))]
    with r hr hr1
  have hr : (0 : ℝ) < r := hr
  have hr1 : r < 1 := hr1
  set t : ℂ := (r : ℂ) * exp (θ * I)
  have hnt : ‖t‖ = r := by
    simp only [t]; rw [norm_mul, norm_real, Real.norm_of_nonneg hr.le, norm_exp_ofReal_mul_I,
      mul_one]
  have hsum : ∑ n ∈ Finset.range N, (t ^ ((n : ℂ) + ((m : ℂ) + 1) - 1)) • ScorerExpansions.coeff n =
      t ^ m * ∑ n ∈ Finset.range N, t ^ n * ScorerExpansions.coeff n := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [show (n : ℂ) + ((m : ℂ) + 1) - 1 = ((n + m : ℕ) : ℂ) by push_cast; ring, cpow_natCast,
      smul_eq_mul, pow_add]
    ring
  rw [hsum, hM.2, ← mul_sub]
  have hb := Complex.norm_exp_sub_sum_le_norm_mul_exp (-(t ^ 3 / 3)) M
  have hn : ‖-(t ^ 3 / 3)‖ = r ^ 3 / 3 := by
    rw [norm_neg, norm_div, norm_pow, hnt]; simp
  rw [hn] at hb
  simp only [add_re, natCast_re, one_re]
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hr.le _), show (N : ℝ) + ((m : ℝ) + 1) - 1 =
        ((N + m : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast, norm_mul,
    norm_pow, hnt]
  have h1 : (r ^ 3 / 3) ^ M ≤ r ^ N := by
    calc (r ^ 3 / 3) ^ M ≤ (r ^ 3) ^ M := by
          gcongr; linarith [pow_nonneg hr.le 3]
      _ = r ^ (3 * M) := by rw [← pow_mul]
      _ ≤ r ^ N := pow_le_pow_of_le_one hr.le hr1.le hM.1
  have h2 : Real.exp (r ^ 3 / 3) ≤ 3 := by
    have : r ^ 3 / 3 ≤ 1 := by nlinarith [pow_le_one₀ hr.le hr1.le (n := 3)]
    calc Real.exp (r ^ 3 / 3) ≤ Real.exp 1 := Real.exp_le_exp.mpr this
      _ ≤ 3 := by have := Real.exp_one_lt_d9; linarith
  calc r ^ m * ‖cexp (-(t ^ 3 / 3)) - ∑ k ∈ Finset.range M, (-(t ^ 3 / 3)) ^ k / (k.factorial : ℂ)‖
      ≤ r ^ m * ((r ^ 3 / 3) ^ M * Real.exp (r ^ 3 / 3)) := by gcongr
    _ ≤ r ^ m * (r ^ N * 3) := by gcongr
    _ = 3 * r ^ (N + m) := by ring

/-- Watson's expansion of `L_m(w) = ∫₀^∞ e^{-wt} t^m e^{-t³/3} dt` in the sector
`|arg w| ≤ α < 2π/3`, obtained from two rotated rays. -/
theorem ScorerExpansions.laplace_expansion (m : ℕ) {α : ℝ} (hα0 : 0 ≤ α) (hα : α < 2 * π / 3) :
    HasAsymptoticExpansion (airySector α) (fun (n : ℕ) (w : ℂ) => w ^ (-((n : ℂ) + ((m : ℂ) + 1))))
      (fun n => Gamma ((n : ℂ) + ((m : ℂ) + 1)) • ScorerExpansions.coeff n)
          (ScorerExpansions.laplace m) := by
  have hπ := Real.pi_pos
  have hcov := le_sup_comap_rotate (α := α) (β := α / 4) (γ := 3 * α / 4)
    (by linarith) (by linarith) (by linarith) (by linarith)
  have hcos : 0 < Real.cos (3 * α / 4) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hrot : ∀ θ : ℝ, |θ| < π / 6 → HasAsymptoticExpansion
      (comap (fun w : ℂ => w * exp (θ * I)) (sectorAtTop (Real.cos (3 * α / 4))))
      (fun (n : ℕ) (w : ℂ) => w ^ (-((n : ℂ) + ((m : ℂ) + 1))))
      (fun n => Gamma ((n : ℂ) + ((m : ℂ) + 1)) • ScorerExpansions.coeff n)
          (ScorerExpansions.laplace m) := by
    intro θ hθ
    have hθ' : |θ| < π / 2 := by linarith
    have hμ : 0 < ((m : ℂ) + 1).re := by simp; positivity
    refine (hasAsymptoticExpansion_integral_cexp_smul_rotate_comap
      (F := fun t => t ^ m * cexp (-(t ^ 3 / 3))) (a := ScorerExpansions.coeff) (μ := (m : ℂ) + 1)
      (c := 0) hθ' hμ hcos (ScorerExpansions.integrableOn_rotate m 0 hθ)
      (ScorerExpansions.sub_sum_isBigO m θ)).congr' (Eventually.of_forall fun w => ?_)
    exact (ScorerExpansions.laplace_rotate m hθ w).symm
  have hb : |α / 4| < π / 6 := by rw [abs_of_nonneg (by linarith)]; linarith
  have h1 := hrot (-(α / 4)) (by rwa [abs_neg])
  have h2 := hrot (α / 4) hb
  exact (h1.sup h2).mono hcov

/-- A sum over `n < 3N` of a sequence vanishing at `n ≢ 0 (mod 3)` is the sum over `k < N` of
its values at `3k`. -/
theorem ScorerExpansions.sum_three {g : ℕ → ℂ} (h1 : ∀ k, g (3 * k + 1) = 0)
    (h2 : ∀ k, g (3 * k + 2) = 0)
    (N : ℕ) : ∑ n ∈ Finset.range (3 * N), g n = ∑ k ∈ Finset.range N, g (3 * k) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 3 * (N + 1) = 3 * N + 1 + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, Finset.sum_range_succ, h1, h2]
    ring

/-- The expansion of `L_m(-z)` in powers of `1/z`, truncated after `N` nonzero terms, for
`-z` in the sector `|arg(-z)| ≤ α < 2π/3`. -/
theorem ScorerExpansions.laplace_neg_isBigO (m : ℕ) {α : ℝ} (hα0 : 0 ≤ α)
    (hα : α < 2 * π / 3) (N : ℕ) :
    IsBigO (comap (fun z : ℂ => -z) (airySector α))
      (fun z => ScorerExpansions.laplace m (-z) - ∑ k ∈ Finset.range N,
        ((3 * k + m).factorial : ℂ) * ((-1 / 3 : ℂ) ^ k / (k.factorial : ℂ)) *
          ((-z) ^ (3 * k + m + 1))⁻¹)
      (fun z => ((z ^ (3 * N + m + 1))⁻¹)) := by
  have hE := (ScorerExpansions.laplace_expansion m hα0 hα (3 * N)).comp_tendsto
    (tendsto_comap : Tendsto (fun z : ℂ => -z) (comap (fun z : ℂ => -z) (airySector α))
      (airySector α))
  have hpow : ∀ (j : ℕ) (w : ℂ), w ^ (-((j : ℂ) + ((m : ℂ) + 1))) = (w ^ (j + m + 1))⁻¹ := by
    intro j w
    rw [show ((j : ℂ) + ((m : ℂ) + 1)) = ((j + m + 1 : ℕ) : ℂ) by push_cast; ring, cpow_neg,
      cpow_natCast]
  refine (hE.congr' (Eventually.of_forall fun z => ?_) EventuallyEq.rfl).trans ?_
  · simp only [Function.comp_apply]
    congr 1
    rw [ScorerExpansions.sum_three (g := fun n => (-z) ^ (-((n : ℂ) + ((m : ℂ) + 1))) •
      (Gamma ((n : ℂ) + ((m : ℂ) + 1)) • ScorerExpansions.coeff n))]
    · refine Finset.sum_congr rfl fun k _ => ?_
      have hd : 3 ∣ 3 * k := dvd_mul_right 3 k
      have hk : 3 * k / 3 = k := by omega
      simp only [ScorerExpansions.coeff, hd, ite_true, hk, smul_eq_mul, hpow]
      rw [show ((3 * k : ℕ) : ℂ) + ((m : ℂ) + 1) = ((3 * k + m : ℕ) : ℂ) + 1 by push_cast; ring,
        Gamma_nat_eq_factorial]
      ring
    · intro k
      have : ¬ 3 ∣ 3 * k + 1 := by omega
      simp [ScorerExpansions.coeff, this]
    · intro k
      have : ¬ 3 ∣ 3 * k + 2 := by omega
      simp [ScorerExpansions.coeff, this]
  · refine IsBigO.of_bound 1 (Eventually.of_forall fun z => ?_)
    simp only [Function.comp_apply]
    rw [hpow, one_mul, norm_inv, norm_inv, norm_pow, norm_pow, norm_neg]

/-- Eventually in the reflected sector `|arg(-z)| ≤ α`, `z ≠ 0`. -/
theorem ScorerExpansions.eventually_ne_zero (α : ℝ) :
    ∀ᶠ z in comap (fun z : ℂ => -z) (airySector α), z ≠ 0 := by
  have h : ∀ᶠ w in airySector α, w ≠ 0 ∧ |arg w| ≤ α := mem_inf_of_right (mem_principal_self _)
  exact (tendsto_comap.eventually h).mono fun z hz => neg_ne_zero.mp hz.1

/-- `(-1)^{3k+j} = (-1)^k (-1)^j`. -/
theorem ScorerExpansions.neg_one_pow (k j : ℕ) : (-1 : ℂ) ^ (3 * k + j) = (-1) ^ k * (-1) ^ j := by
  rw [pow_add, pow_mul]; norm_num

/-- `Hi(z) = -(πz)⁻¹ ∑_{k<N} (3k)!/(k!(3z³)^k) + O(z^{-3N-1})` for `|arg(-z)| ≤ α < 2π/3`. -/
theorem ScorerExpansions.scorerHi_isBigO {α : ℝ} (hα0 : 0 ≤ α) (hα : α < 2 * π / 3) (N : ℕ) :
    IsBigO (comap (fun z : ℂ => -z) (airySector α))
      (fun z : ℂ => scorerHi z - -1 / (π * z ^ 1) *
        ∑ k ∈ Finset.range N, (((3 * k + 0).factorial : ℂ) / k.factorial) / (3 * z ^ 3) ^ k)
      (fun z : ℂ => (z ^ (3 * N + 0 + 1))⁻¹) := by
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have h := (ScorerExpansions.laplace_neg_isBigO 0 hα0 hα N).const_mul_left (1 / π : ℂ)
  refine h.congr' ?_ EventuallyEq.rfl
  filter_upwards [ScorerExpansions.eventually_ne_zero α] with z hz
  rw [← ScorerExpansions.scorerHi_eq, mul_sub, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · field_simp
  · refine Finset.sum_congr rfl fun k _ => ?_
    simp only [add_zero, pow_one]
    rw [neg_pow, ScorerExpansions.neg_one_pow k 1, mul_pow, ← pow_mul, div_pow, pow_succ z]
    have hf : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    field_simp

/-- `Hi'(z) = (πz²)⁻¹ ∑_{k<N} (3k+1)!/(k!(3z³)^k) + O(z^{-3N-2})` for `|arg(-z)| ≤ α < 2π/3`. -/
theorem ScorerExpansions.scorerHiDeriv_isBigO {α : ℝ} (hα0 : 0 ≤ α) (hα : α < 2 * π / 3) (N : ℕ) :
    IsBigO (comap (fun z : ℂ => -z) (airySector α))
      (fun z : ℂ => scorerHiDeriv z - 1 / (π * z ^ 2) *
        ∑ k ∈ Finset.range N, (((3 * k + 1).factorial : ℂ) / k.factorial) / (3 * z ^ 3) ^ k)
      (fun z : ℂ => (z ^ (3 * N + 1 + 1))⁻¹) := by
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have h := (ScorerExpansions.laplace_neg_isBigO 1 hα0 hα N).const_mul_left (1 / π : ℂ)
  refine h.congr' ?_ EventuallyEq.rfl
  filter_upwards [ScorerExpansions.eventually_ne_zero α] with z hz
  rw [← ScorerExpansions.scorerHiDeriv_eq, mul_sub, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · field_simp
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [show 3 * k + 1 + 1 = 3 * k + 2 by ring, neg_pow, ScorerExpansions.neg_one_pow k 2, mul_pow,
      ← pow_mul, div_pow, pow_add z (3 * k) 2]
    have hf : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    field_simp

/-- Rotation by `e^{∓2πi/3}` maps the sector `|arg z| ≤ π/3 - δ` into the reflected sector
`|arg(-z)| ≤ 2π/3 - δ`. -/
theorem ScorerExpansions.tendsto_omega {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < π / 3) :
    Tendsto (fun z : ℂ => z * exp (-2 * π * I / 3)) (airySector (π / 3 - δ))
        (comap (fun z : ℂ => -z) (airySector (2 * π / 3 - δ))) ∧
      Tendsto (fun z : ℂ => z * exp (2 * π * I / 3)) (airySector (π / 3 - δ))
        (comap (fun z : ℂ => -z) (airySector (2 * π / 3 - δ))) := by
  have hπ := Real.pi_pos
  have e1 : ∀ z : ℂ, -(z * exp (-2 * π * I / 3)) = z * exp (((π / 3 : ℝ) : ℂ) * I) := fun z => by
    rw [show (-2 * π * I / 3 : ℂ) = ((π / 3 : ℝ) : ℂ) * I - π * I by push_cast; ring,
      Complex.exp_sub, exp_pi_mul_I]; field_simp
  have e2 : ∀ z : ℂ, -(z * exp (2 * π * I / 3)) = z * exp (((-(π / 3)) : ℝ) * I) := fun z => by
    rw [show (2 * π * I / 3 : ℂ) = ((-(π / 3)) : ℝ) * I + π * I by push_cast; ring,
      Complex.exp_add, exp_pi_mul_I]; ring
  constructor
  · refine tendsto_comap_iff.mpr ?_
    have := RotatedExpansions.tendsto_rotate (α := π / 3 - δ) (β := 2 * π / 3 - δ) (c := π / 3)
      (by rw [abs_of_pos (by positivity)]; linarith) (by linarith)
    exact this.congr fun z => (e1 z).symm
  · refine tendsto_comap_iff.mpr ?_
    have := RotatedExpansions.tendsto_rotate (α := π / 3 - δ) (β := 2 * π / 3 - δ) (c := -(π / 3))
      (by rw [abs_neg, abs_of_pos (by positivity)]; linarith) (by linarith)
    exact this.congr fun z => (e2 z).symm

/-- The derivative of the rotation formula 9.12.12. -/
theorem ScorerExpansions.scorerGiDeriv_rotations (z : ℂ) :
    scorerGiDeriv z = exp (π * I / 3) / 2 * (scorerHiDeriv (z * exp (-2 * π * I / 3)) *
        exp (-2 * π * I / 3)) +
      exp (-π * I / 3) / 2 * (scorerHiDeriv (z * exp (2 * π * I / 3)) * exp (2 * π * I / 3)) := by
  have hfun : scorerGi = fun z => exp (π * I / 3) / 2 * scorerHi (z * exp (-2 * π * I / 3)) +
      exp (-π * I / 3) / 2 * scorerHi (z * exp (2 * π * I / 3)) := funext scorerGi_rotations
  have h1 := (hasDerivAt_scorerHi (z * exp (-2 * π * I / 3))).comp z
    ((hasDerivAt_id z).mul_const (exp (-2 * π * I / 3)))
  have h2 := (hasDerivAt_scorerHi (z * exp (2 * π * I / 3))).comp z
    ((hasDerivAt_id z).mul_const (exp (2 * π * I / 3)))
  have h := (h1.const_mul (exp (π * I / 3) / 2)).add (h2.const_mul (exp (-π * I / 3) / 2))
  rw [scorerGiDeriv, hfun]
  refine h.deriv.trans ?_
  simp

/-- The unitCube roots of unity `e^{±2πi/3}` have norm `1`. -/
theorem ScorerExpansions.norm_omega : ‖exp (-2 * π * I / 3)‖ = 1 ∧ ‖exp (2 * π * I / 3)‖ = 1 := by
  constructor
  · rw [show (-2 * π * I / 3 : ℂ) = ((-2 * π / 3 : ℝ) : ℂ) * I by push_cast; ring,
      norm_exp_ofReal_mul_I]
  · rw [show (2 * π * I / 3 : ℂ) = ((2 * π / 3 : ℝ) : ℂ) * I by push_cast; ring,
      norm_exp_ofReal_mul_I]

/-- The unitCube roots of unity `e^{±2πi/3}` unitCube to `1`. -/
theorem ScorerExpansions.omega_pow_three_eq_one : exp (-2 * π * I / 3) ^ 3 = 1 ∧
    exp (2 * π * I / 3) ^ 3 = 1 := by
  constructor
  · rw [show (-2 * π * I / 3 : ℂ) = -(2 * π * I / 3) by ring]; exact omega_recip_cube
  · exact omega_cube

/-- Composite bound: `((z c)^n)⁻¹ = O((z^n)⁻¹)` when `‖c‖ = 1`. -/
theorem ScorerExpansions.isBigO_inv_pow_mul {l : Filter ℂ} {c : ℂ} (hc : ‖c‖ = 1) (n : ℕ) :
    (fun z : ℂ => ((z * c) ^ n)⁻¹) =O[l] (fun z : ℂ => (z ^ n)⁻¹) :=
  IsBigO.of_bound 1 (Eventually.of_forall fun z => by
    rw [one_mul, norm_inv, norm_inv, norm_pow, norm_pow, norm_mul, hc, mul_one])

/-- The coefficients of 9.12.12: `e^{πi/3}/2 = -e^{-2πi/3}/2` and `e^{-πi/3}/2 = -e^{2πi/3}/2`. -/
theorem ScorerExpansions.rotation_coeffs :
    exp (π * I / 3) / 2 = -exp (-2 * π * I / 3) / 2 ∧
      exp (-π * I / 3) / 2 = -exp (2 * π * I / 3) / 2 := by
  constructor
  · rw [show (-2 * π * I / 3 : ℂ) = π * I / 3 - π * I by ring, Complex.exp_sub, exp_pi_mul_I]
    ring
  · rw [show (2 * π * I / 3 : ℂ) = -π * I / 3 + π * I by ring, Complex.exp_add, exp_pi_mul_I]
    ring

/-- `Gi(z) ~ (πz)⁻¹ ∑ (3k)!/(k! (3z³)^k)` as `z → ∞` in `|arg z| ≤ π/3 - δ`, with remainder
`O(z^{-3N-1})` (DLMF 9.12.25). -/
@[dlmf 9.12.E25]
theorem scorerGi_asymptotic {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < π / 3) (N : ℕ) :
    IsBigO (comap (fun z : ℂ => z) (airySector (π / 3 - δ)))
      (fun z : ℂ => scorerGi z - 1 / (π * z ^ 1) *
        ∑ k ∈ Finset.range N, (((3 * k + 0).factorial : ℂ) / k.factorial) / (3 * z ^ 3) ^ k)
      (fun z : ℂ => z ^ (-(3 * (N : ℂ) + 1))) := by
  rw [comap_id']
  have hπ := Real.pi_pos
  obtain ⟨T1, T2⟩ := ScorerExpansions.tendsto_omega hδ hδ'
  obtain ⟨n1, n2⟩ := ScorerExpansions.norm_omega
  obtain ⟨c1, c2⟩ := ScorerExpansions.omega_pow_three_eq_one
  obtain ⟨ha, hb⟩ := ScorerExpansions.rotation_coeffs
  have H := ScorerExpansions.scorerHi_isBigO (α := 2 * π / 3 - δ) (by linarith) (by linarith) N
  have h1 := ((H.comp_tendsto T1).trans (ScorerExpansions.isBigO_inv_pow_mul n1 _)).const_mul_left
    (exp (π * I / 3) / 2)
  have h2 := ((H.comp_tendsto T2).trans (ScorerExpansions.isBigO_inv_pow_mul n2 _)).const_mul_left
    (exp (-π * I / 3) / 2)
  have hev : ∀ᶠ z in airySector (π / 3 - δ), z ≠ 0 ∧ |arg z| ≤ π / 3 - δ :=
    mem_inf_of_right (mem_principal_self _)
  refine (h1.add h2).congr' ?_ (Eventually.of_forall fun z => ?_)
  · filter_upwards [hev] with z hz
    have hz0 := hz.1
    set S : ℂ → ℂ := fun w => ∑ k ∈ Finset.range N,
      (((3 * k + 0).factorial : ℂ) / k.factorial) / (3 * w ^ 3) ^ k with hSdef
    have hS : ∀ c : ℂ, c ^ 3 = 1 → S (z * c) = S z := fun c hc => by
      simp only [hSdef, mul_pow, hc, mul_one]
    simp only [Function.comp_apply]
    change exp (π * I / 3) / 2 * (scorerHi (z * exp (-2 * π * I / 3)) -
        -1 / (π * (z * exp (-2 * π * I / 3)) ^ 1) * S (z * exp (-2 * π * I / 3))) +
      exp (-π * I / 3) / 2 * (scorerHi (z * exp (2 * π * I / 3)) -
        -1 / (π * (z * exp (2 * π * I / 3)) ^ 1) * S (z * exp (2 * π * I / 3))) =
      scorerGi z - 1 / (π * z ^ 1) * S z
    rw [hS _ c1, hS _ c2, scorerGi_rotations, ha, hb]
    have e1 : exp (-2 * π * I / 3) ≠ 0 := exp_ne_zero _
    have e2 : exp (2 * π * I / 3) ≠ 0 := exp_ne_zero _
    have hp : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp
    ring
  · simp only
    rw [show (3 * (N : ℂ) + 1) = ((3 * N + 0 + 1 : ℕ) : ℂ) by push_cast; ring, cpow_neg,
      cpow_natCast]

/-- `Gi'(z) ~ -(πz²)⁻¹ ∑ (3k+1)!/(k! (3z³)^k)` as `z → ∞` in `|arg z| ≤ π/3 - δ`, with
remainder `O(z^{-3N-2})` (DLMF 9.12.26). -/
@[dlmf 9.12.E26]
theorem scorerGiDeriv_asymptotic {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < π / 3) (N : ℕ) :
    IsBigO (comap (fun z : ℂ => z) (airySector (π / 3 - δ)))
      (fun z : ℂ => scorerGiDeriv z - -1 / (π * z ^ 2) *
        ∑ k ∈ Finset.range N, (((3 * k + 1).factorial : ℂ) / k.factorial) / (3 * z ^ 3) ^ k)
      (fun z : ℂ => z ^ (-(3 * (N : ℂ) + 2))) := by
  rw [comap_id']
  have hπ := Real.pi_pos
  obtain ⟨T1, T2⟩ := ScorerExpansions.tendsto_omega hδ hδ'
  obtain ⟨n1, n2⟩ := ScorerExpansions.norm_omega
  obtain ⟨c1, c2⟩ := ScorerExpansions.omega_pow_three_eq_one
  obtain ⟨ha, hb⟩ := ScorerExpansions.rotation_coeffs
  have H := ScorerExpansions.scorerHiDeriv_isBigO (α := 2 * π / 3 - δ) (by linarith) (by linarith) N
  have h1 := ((H.comp_tendsto T1).trans (ScorerExpansions.isBigO_inv_pow_mul n1 _)).const_mul_left
    (exp (π * I / 3) / 2 * exp (-2 * π * I / 3))
  have h2 := ((H.comp_tendsto T2).trans (ScorerExpansions.isBigO_inv_pow_mul n2 _)).const_mul_left
    (exp (-π * I / 3) / 2 * exp (2 * π * I / 3))
  have hev : ∀ᶠ z in airySector (π / 3 - δ), z ≠ 0 ∧ |arg z| ≤ π / 3 - δ :=
    mem_inf_of_right (mem_principal_self _)
  refine (h1.add h2).congr' ?_ (Eventually.of_forall fun z => ?_)
  · filter_upwards [hev] with z hz
    have hz0 := hz.1
    set S : ℂ → ℂ := fun w => ∑ k ∈ Finset.range N,
      (((3 * k + 1).factorial : ℂ) / k.factorial) / (3 * w ^ 3) ^ k with hSdef
    have hS : ∀ c : ℂ, c ^ 3 = 1 → S (z * c) = S z := fun c hc => by
      simp only [hSdef, mul_pow, hc, mul_one]
    simp only [Function.comp_apply]
    change exp (π * I / 3) / 2 * exp (-2 * π * I / 3) * (scorerHiDeriv (z * exp (-2 * π * I / 3)) -
        1 / (π * (z * exp (-2 * π * I / 3)) ^ 2) * S (z * exp (-2 * π * I / 3))) +
      exp (-π * I / 3) / 2 * exp (2 * π * I / 3) * (scorerHiDeriv (z * exp (2 * π * I / 3)) -
        1 / (π * (z * exp (2 * π * I / 3)) ^ 2) * S (z * exp (2 * π * I / 3))) =
      scorerGiDeriv z - -1 / (π * z ^ 2) * S z
    rw [hS _ c1, hS _ c2, ScorerExpansions.scorerGiDeriv_rotations, ha, hb]
    have e1 : exp (-2 * π * I / 3) ≠ 0 := exp_ne_zero _
    have e2 : exp (2 * π * I / 3) ≠ 0 := exp_ne_zero _
    have hp : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp
    ring
  · simp only
    rw [show (3 * (N : ℂ) + 2) = ((3 * N + 1 + 1 : ℕ) : ℂ) by push_cast; ring, cpow_neg,
      cpow_natCast]

/-- `Hi(z) ~ -(πz)⁻¹ ∑ (3k)!/(k! (3z³)^k)` as `z → ∞` in `|arg(-z)| ≤ 2π/3 - δ`, with
remainder `O(z^{-3N-1})` (DLMF 9.12.27). -/
@[dlmf 9.12.E27]
theorem scorerHi_asymptotic {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 2 * π / 3) (N : ℕ) :
    IsBigO (comap (fun z : ℂ => -z) (airySector (2 * π / 3 - δ)))
      (fun z : ℂ => scorerHi z - -1 / (π * z ^ 1) *
        ∑ k ∈ Finset.range N, (((3 * k + 0).factorial : ℂ) / k.factorial) / (3 * z ^ 3) ^ k)
      (fun z : ℂ => z ^ (-(3 * (N : ℂ) + 1))) := by
  refine (ScorerExpansions.scorerHi_isBigO (α := 2 * π / 3 - δ) (by linarith)
      (by linarith) N).congr'
    EventuallyEq.rfl (Eventually.of_forall fun z => ?_)
  simp only
  rw [show (3 * (N : ℂ) + 1) = ((3 * N + 0 + 1 : ℕ) : ℂ) by push_cast; ring, cpow_neg, cpow_natCast]

/-- `Hi'(z) ~ (πz²)⁻¹ ∑ (3k+1)!/(k! (3z³)^k)` as `z → ∞` in `|arg(-z)| ≤ 2π/3 - δ`, with
remainder `O(z^{-3N-2})` (DLMF 9.12.28). -/
@[dlmf 9.12.E28]
theorem scorerHiDeriv_asymptotic {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 2 * π / 3) (N : ℕ) :
    IsBigO (comap (fun z : ℂ => -z) (airySector (2 * π / 3 - δ)))
      (fun z : ℂ => scorerHiDeriv z - 1 / (π * z ^ 2) *
        ∑ k ∈ Finset.range N, (((3 * k + 1).factorial : ℂ) / k.factorial) / (3 * z ^ 3) ^ k)
      (fun z : ℂ => z ^ (-(3 * (N : ℂ) + 2))) := by
  refine (ScorerExpansions.scorerHiDeriv_isBigO (α := 2 * π / 3 - δ) (by linarith) (by linarith)
    N).congr' EventuallyEq.rfl (Eventually.of_forall fun z => ?_)
  simp only
  rw [show (3 * (N : ℂ) + 2) = ((3 * N + 1 + 1 : ℕ) : ℂ) by push_cast; ring, cpow_neg,
    cpow_natCast]

/-- All zeros of `Gi`, real or complex, are simple, DLMF §9.12(ix). -/
@[dlmf 9.12.ix]
theorem scorerGi_simple_zeros {z : ℂ} (hz : scorerGi z = 0) : deriv scorerGi z ≠ 0 := by
  sorry

/-- All zeros of `Hi`, real or complex, are simple, DLMF §9.12(ix). -/
@[dlmf 9.12.ix]
theorem scorerHi_simple_zeros {z : ℂ} (hz : scorerHi z = 0) : deriv scorerHi z ≠ 0 := by
  sorry

/-- On the real line the Laplace integral is real. -/
theorem integral_pow_mul_exp_cubic_ofReal (m : ℕ) (x : ℝ) :
    ∫ t : ℝ in Ioi 0, (t : ℂ) ^ m * exp (-(t : ℂ) ^ 3 / 3 + x * t) =
      ((∫ t : ℝ in Ioi 0, t ^ m * Real.exp (-(t ^ 3 / 3) + x * t) : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  push_cast; rw [neg_div]

/-- The real Laplace integral is positive. -/
theorem integral_pow_mul_exp_cubic_pos (m : ℕ) (x : ℝ) :
    0 < ∫ t : ℝ in Ioi 0, t ^ m * Real.exp (-(t ^ 3 / 3) + x * t) := by
  have hi : IntegrableOn (fun t : ℝ => t ^ m * Real.exp (-(t ^ 3 / 3) + x * t)) (Ioi 0) := by
    have := (integrableOn_pow_mul_exp_cubic m x).re
    refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
    beta_reduce
    rw [RCLike.re_to_complex, show (-(t : ℂ) ^ 3 / 3 + (x : ℂ) * t) =
        ((-(t ^ 3 / 3) + x * t : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_exp, ← ofReal_pow, ← ofReal_mul, ofReal_re]
  rw [setIntegral_pos_iff_support_of_nonneg_ae _ hi]
  · rw [show Function.support (fun t : ℝ => t ^ m * Real.exp (-(t ^ 3 / 3) + x * t)) ∩ Ioi 0 =
        Ioi 0 by
      ext t
      simp only [mem_inter_iff, Function.mem_support, mem_Ioi]
      constructor
      · exact fun h => h.2
      · intro ht; exact ⟨(mul_pos (pow_pos ht m) (Real.exp_pos _)).ne', ht⟩]
    simp
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
    exact (mul_pos (pow_pos ht m) (Real.exp_pos _)).le

/-- There are no real zeros, DLMF §9.12(ix). -/
@[dlmf 9.12.ix]
theorem scorerHi_real_ne_zero (x : ℝ) :
    scorerHi x ≠ 0 := by
  rw [(scorerHi_exp_integral x).2]
  have h := integral_pow_mul_exp_cubic_ofReal 0 x
  simp only [pow_zero, one_mul] at h
  rw [h]
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hp := integral_pow_mul_exp_cubic_pos 0 x
  simp only [pow_zero, one_mul] at hp
  exact div_ne_zero (ofReal_ne_zero.mpr hp.ne') hpi

/-- There are no real zeros, DLMF §9.12(ix). -/
@[dlmf 9.12.ix]
theorem scorerHiDeriv_real_ne_zero (x : ℝ) :
    scorerHiDeriv x ≠ 0 := by
  rw [scorerHiDeriv_exp_integral]
  have h := integral_pow_mul_exp_cubic_ofReal 1 x
  simp only [pow_one] at h
  rw [h]
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hp := integral_pow_mul_exp_cubic_pos 1 x
  simp only [pow_one] at hp
  exact div_ne_zero (ofReal_ne_zero.mpr hp.ne') hpi

/-! ### Real zeros of `Gi` and `Gi'`

The real restrictions satisfy `Gi'' = x Gi - 1/π`. Positivity on `[0, ∞)` follows from the
maximum principle (`ODE.sturmCount_neg_of_maxPrinciple`) and the asymptotics 9.12.25–26; on
the negative axis `Gi = Bi - Hi`, where `Hi(x) ≤ 1/(π|x|)` is dominated by the Airy modulus
`M(x)`, so `Gi` alternates in sign at the points where the Airy phase is a multiple of `π`.
-/

/-- `Gi` on the real axis. -/
def ScorerZeros.gi (x : ℝ) : ℝ := (scorerGi x).re
/-- `Gi'` on the real axis. -/
def ScorerZeros.gi' (x : ℝ) : ℝ := (scorerGiDeriv x).re
/-- `Hi` on the real axis, as a real Laplace integral. -/
def ScorerZeros.hi (x : ℝ) : ℝ := (∫ t in Ioi (0 : ℝ), Real.exp (-(t ^ 3 / 3) + x * t)) / π

/-- `tᵐ e^{-t³/3 + xt}` is integrable on `(0, ∞)` for real `x`. -/
theorem ScorerZeros.integrable (m : ℕ) (x : ℝ) :
    IntegrableOn (fun t : ℝ => t ^ m * Real.exp (-(t ^ 3 / 3) + x * t)) (Ioi 0) := by
  have := (integrableOn_pow_mul_exp_cubic m x).re
  refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
  beta_reduce
  rw [RCLike.re_to_complex, show (-(t : ℂ) ^ 3 / 3 + (x : ℂ) * t) =
      ((-(t ^ 3 / 3) + x * t : ℝ) : ℂ) by push_cast; ring,
    ← ofReal_exp, ← ofReal_pow, ← ofReal_mul, ofReal_re]

/-- `Hi(x)` is the real number `ScorerZeros.hi x` on the real axis. -/
theorem ScorerZeros.hi_eq (x : ℝ) : scorerHi x = (ScorerZeros.hi x : ℂ) := by
  rw [(scorerHi_exp_integral x).2]
  have h := integral_pow_mul_exp_cubic_ofReal 0 x
  simp only [pow_zero, one_mul] at h
  rw [h, ScorerZeros.hi]; push_cast; rfl

/-- On the real axis, `Hi'(x) = π⁻¹ ∫₀^∞ t e^{-t³/3 + xt} dt`, a real number. -/
theorem ScorerZeros.hiDeriv_eq (x : ℝ) : scorerHiDeriv x =
    (((∫ t in Ioi (0 : ℝ), t ^ 1 * Real.exp (-(t ^ 3 / 3) + x * t)) / π : ℝ) : ℂ) := by
  rw [scorerHiDeriv_exp_integral]
  have h := integral_pow_mul_exp_cubic_ofReal 1 x
  simp only [pow_one] at h ⊢
  rw [h]; push_cast; rfl

/-- `Gi(x)` is the real number `ScorerZeros.gi x` on the real axis. -/
theorem ScorerZeros.gi_ofReal (x : ℝ) : scorerGi x = (ScorerZeros.gi x : ℂ) := by
  have h : scorerGi x = ((DLMF.Airy.Real.airyBi x - ScorerZeros.hi x : ℝ) : ℂ) := by
    rw [scorerGi, airyBi_ofReal_eq, ScorerZeros.hi_eq]; push_cast; ring
  rw [ScorerZeros.gi, h, ofReal_re]

/-- On the real axis, `Gi = Bi - Hi`. -/
theorem ScorerZeros.gi_eq (x : ℝ) : ScorerZeros.gi x = DLMF.Airy.Real.airyBi x -
    ScorerZeros.hi x := by
  rw [ScorerZeros.gi, scorerGi, sub_re, ScorerZeros.hi_eq, ofReal_re]; rfl

/-- `Gi'(x)` is the real number `ScorerZeros.gi' x` on the real axis. -/
theorem ScorerZeros.gi'_ofReal (x : ℝ) : scorerGiDeriv x = (ScorerZeros.gi' x : ℂ) := by
  have h : ∃ r : ℝ, scorerGiDeriv x = (r : ℂ) := by
    rw [scorerGiDeriv_eq, airyBiDeriv_ofReal_eq, ScorerZeros.hiDeriv_eq]
    exact ⟨DLMF.Airy.Real.airyBiDeriv x -
        (∫ t in Ioi (0 : ℝ), t ^ 1 * Real.exp (-(t ^ 3 / 3) + x * t)) / π,
      by push_cast; ring⟩
  obtain ⟨r, hr⟩ := h
  rw [ScorerZeros.gi', hr, ofReal_re]

/-- The real function `Gi` has derivative `Gi'`. -/
theorem ScorerZeros.hasDerivAt_gi (x : ℝ) : HasDerivAt ScorerZeros.gi (ScorerZeros.gi' x) x :=
  ((isAiryInhomSol_scorerGi x).1).real_of_complex

/-- The real function `Gi'` has derivative `x Gi(x) - 1/π` (the inhomogeneous Airy equation). -/
theorem ScorerZeros.hasDerivAt_gi' (x : ℝ) :
    HasDerivAt ScorerZeros.gi' (x * ScorerZeros.gi x - 1 / π) x := by
  have h : HasDerivAt ScorerZeros.gi' _ x := ((isAiryInhomSol_scorerGi x).2).real_of_complex
  refine h.congr_deriv ?_
  rw [ScorerZeros.gi_ofReal]
  simp only [add_re, re_ofReal_mul, neg_re, div_ofReal_re, one_re]
  rw [ofReal_re]; ring

/-- The derivative of `x Gi(x) - 1/π` is `Gi(x) + x Gi'(x)`. -/
theorem ScorerZeros.hasDerivAt_gi'' (x : ℝ) :
    HasDerivAt (fun t => t * ScorerZeros.gi t - 1 / π)
        (ScorerZeros.gi x + x * ScorerZeros.gi' x) x := by
  have := ((hasDerivAt_id x).mul (ScorerZeros.hasDerivAt_gi x)).sub_const (1 / π)
  convert this using 1 <;> simp

/-- The real function `Gi` is continuous. -/
theorem ScorerZeros.continuous_gi : Continuous ScorerZeros.gi :=
  continuous_iff_continuousAt.mpr fun x => (ScorerZeros.hasDerivAt_gi x).continuousAt

/-- The real function `Gi'` is continuous. -/
theorem ScorerZeros.continuous_gi' : Continuous ScorerZeros.gi' :=
  continuous_iff_continuousAt.mpr fun x => (ScorerZeros.hasDerivAt_gi' x).continuousAt

/-- `Gi(0) > 0`. -/
theorem ScorerZeros.gi_zero_pos : 0 < ScorerZeros.gi 0 := by
  rw [ScorerZeros.gi, ofReal_zero, scorer_zero.2.1, div_ofNat_re]
  exact div_pos (DLMF.Airy.Real.airyBi_pos le_rfl) (by norm_num)

/-- `Gi'(0) > 0`. -/
theorem ScorerZeros.gi'_zero_pos : 0 < ScorerZeros.gi' 0 := by
  rw [ScorerZeros.gi', ofReal_zero, scorerDeriv_zero.2.1, div_ofNat_re]
  exact div_pos DLMF.Airy.Real.airyBiDeriv_zero_pos (by norm_num)

/-- Real form of a sector bound: `‖F x‖ ≤ C x^{-p}` eventually along the positive axis. -/
theorem ScorerZeros.real_bound {F : ℂ → ℂ} {p : ℂ}
    (h : IsBigO (comap (fun z : ℂ => z) (airySector (π / 3 - π / 6))) F (fun z => z ^ p)) :
    ∃ C, ∀ᶠ x : ℝ in atTop, ‖F x‖ ≤ C * x ^ p.re := by
  rw [comap_id'] at h
  obtain ⟨C, hC⟩ := (h.comp_tendsto (IntegralRepresentation.tendsto_ofReal_sector (by
    linarith [Real.pi_pos]))).bound
  refine ⟨C, ?_⟩
  filter_upwards [hC, eventually_gt_atTop 0] with x hx hx0
  simpa [Function.comp, Complex.norm_cpow_eq_rpow_re_of_pos hx0] using hx

/-- `Gi(x) > 0` for all sufficiently large real `x`. -/
theorem ScorerZeros.gi_eventually_pos : ∀ᶠ x in atTop, 0 < ScorerZeros.gi x := by
  have hπ := Real.pi_pos
  obtain ⟨C, hC⟩ := ScorerZeros.real_bound (scorerGi_asymptotic (δ := π / 6)
    (by positivity) (by linarith) 1)
  filter_upwards [hC, eventually_gt_atTop (max 1 (C * π))] with x hx hxM
  have hx1 : 1 < x := (le_max_left _ _).trans_lt hxM
  have hxC : C * π < x := (le_max_right _ _).trans_lt hxM
  have hx0 : 0 < x := by linarith
  simp only [Finset.sum_range_one, Nat.factorial_zero, Nat.cast_one, div_one, pow_zero,
    mul_one, mul_zero, zero_add, pow_one] at hx
  rw [ScorerZeros.gi_ofReal, show (1 : ℂ) / (π * (x : ℂ)) = ((1 / (π * x) : ℝ) : ℂ) by
      push_cast; ring,
    ← ofReal_sub, norm_real, Real.norm_eq_abs] at hx
  have hre : (-(3 + 1 : ℂ)).re = -4 := by norm_num
  rw [hre, Real.rpow_neg hx0.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    at hx
  have h1 := (abs_le.mp hx).1
  have hx4 : 0 < x ^ 4 := by positivity
  have key : C * (x ^ 4)⁻¹ < 1 / (π * x) := by
    rw [← div_eq_mul_inv, div_lt_div_iff₀ hx4 (by positivity)]
    have : x ≤ x ^ 3 := le_self_pow₀ hx1.le (by norm_num)
    nlinarith
  linarith

/-- `Gi'(x) < 0` for all sufficiently large real `x`. -/
theorem ScorerZeros.gi'_eventually_neg : ∀ᶠ x in atTop, ScorerZeros.gi' x < 0 := by
  have hπ := Real.pi_pos
  obtain ⟨C, hC⟩ := ScorerZeros.real_bound (scorerGiDeriv_asymptotic (δ := π / 6)
    (by positivity) (by linarith) 1)
  filter_upwards [hC, eventually_gt_atTop (max 1 (C * π))] with x hx hxM
  have hx1 : 1 < x := (le_max_left _ _).trans_lt hxM
  have hxC : C * π < x := (le_max_right _ _).trans_lt hxM
  have hx0 : 0 < x := by linarith
  simp only [Finset.sum_range_one, Nat.factorial_zero, Nat.cast_one, div_one, pow_zero,
    mul_one, mul_zero, zero_add, Nat.factorial_one] at hx
  rw [ScorerZeros.gi'_ofReal, show (-1 : ℂ) / (π * (x : ℂ) ^ 2) = ((-1 / (π * x ^ 2) : ℝ) : ℂ) by
      push_cast; ring, ← ofReal_sub, norm_real, Real.norm_eq_abs] at hx
  have hre : (-(3 + 2 : ℂ)).re = -5 := by norm_num
  rw [hre, Real.rpow_neg hx0.le, show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    at hx
  have h1 := (abs_le.mp hx).2
  have hx5 : 0 < x ^ 5 := by positivity
  have key : C * (x ^ 5)⁻¹ < 1 / (π * x ^ 2) := by
    rw [← div_eq_mul_inv, div_lt_div_iff₀ hx5 (by positivity)]
    have : x ≤ x ^ 3 := le_self_pow₀ hx1.le (by norm_num)
    nlinarith [pow_pos hx0 2]
  have : -1 / (π * x ^ 2) = -(1 / (π * x ^ 2)) := by ring
  linarith

/-- `Gi(x) > 0` for `x ≥ 0`. -/
theorem ScorerZeros.gi_pos {x : ℝ} (hx : 0 ≤ x) : 0 < ScorerZeros.gi x := by
  obtain ⟨X, hX, hXx⟩ := (ScorerZeros.gi_eventually_pos.and (eventually_gt_atTop x)).exists
  have hπ := Real.pi_pos
  have := ODE.sturmCount_neg_of_maxPrinciple (g := fun t => -ScorerZeros.gi t)
    (g' := fun t => -ScorerZeros.gi' t) (g'' := fun t => -(t * ScorerZeros.gi t - 1 / π))
        (a := 0) (b := X)
    ScorerZeros.continuous_gi.neg.continuousOn (fun t _ => (ScorerZeros.hasDerivAt_gi t).neg)
    (fun t _ => (ScorerZeros.hasDerivAt_gi' t).neg) (by simpa using ScorerZeros.gi_zero_pos)
    (by simpa using hX) (fun t ht h0 _ => by
      have : t * ScorerZeros.gi t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht.1.le (by linarith)
      have : 0 < 1 / π := by positivity
      linarith) x ⟨hx, hXx.le⟩
  linarith

/-- `Gi'` has at most one zero on `[0, ∞)`. -/
theorem ScorerZeros.gi'_zero_unique {y₁ y₂ : ℝ} (h₁ : 0 ≤ y₁) (hlt : y₁ < y₂)
    (e₁ : ScorerZeros.gi' y₁ = 0)
    (e₂ : ScorerZeros.gi' y₂ = 0) : False := by
  obtain ⟨X, hX, hXx⟩ := (ScorerZeros.gi'_eventually_neg.and (eventually_gt_atTop y₂)).exists
  have hle := ODE.sturmCount_nonpos_of_maxPrinciple (g := ScorerZeros.gi')
    (g' := fun t => t * ScorerZeros.gi t - 1 / π)
        (g'' := fun t => ScorerZeros.gi t + t * ScorerZeros.gi' t)
    (a := y₁) (b := X) ScorerZeros.continuous_gi'.continuousOn
    (fun t _ => ScorerZeros.hasDerivAt_gi' t) (fun t _ => ScorerZeros.hasDerivAt_gi'' t) e₁.le hX.le
    (fun t ht hpos _ => by
      have h0 : 0 < t := lt_of_le_of_lt h₁ ht.1
      have := ScorerZeros.gi_pos h0.le
      positivity)
  have hloc : IsLocalMax ScorerZeros.gi' y₂ := by
    filter_upwards [Icc_mem_nhds hlt hXx] with t ht
    rw [e₂]; exact hle t ht
  have hd0 := hloc.hasDerivAt_eq_zero (ScorerZeros.hasDerivAt_gi' y₂)
  refine ODE.sturmCount_not_isLocalMax (Eventually.of_forall fun t => ScorerZeros.hasDerivAt_gi' t)
    (ScorerZeros.hasDerivAt_gi'' y₂) hd0 ?_ hloc
  rw [e₂, mul_zero, add_zero]
  exact ScorerZeros.gi_pos (h₁.trans hlt.le)

/-- `0 < Hi(x) ≤ 1/(π|x|)` for `x < 0`. -/
theorem ScorerZeros.hi_le {x : ℝ} (hx : x < 0) : ScorerZeros.hi x ≤ 1 / (π * (-x)) := by
  have hπ := Real.pi_pos
  have hI : ∫ t in Ioi (0 : ℝ), Real.exp (-(t ^ 3 / 3) + x * t) ≤ 1 / (-x) := by
    calc ∫ t in Ioi (0 : ℝ), Real.exp (-(t ^ 3 / 3) + x * t)
        ≤ ∫ t in Ioi (0 : ℝ), Real.exp (x * t) := by
          refine setIntegral_mono_on (by simpa using ScorerZeros.integrable 0 x)
            (integrableOn_exp_mul_Ioi hx 0) measurableSet_Ioi fun t ht => ?_
          have ht : (0 : ℝ) < t := ht
          exact Real.exp_le_exp.mpr (by nlinarith [pow_pos ht 3])
      _ = 1 / (-x) := by rw [integral_exp_mul_Ioi hx 0]; simp; field_simp
  rw [ScorerZeros.hi, mul_comm, ← div_div]
  exact div_le_div_of_nonneg_right hI hπ.le

/-- The Airy modulus beats the Hi bound: `1/(π|x|) < M(x)` for `x ≤ -1`. -/
theorem ScorerZeros.modulus_gt {x : ℝ} (hx : x ≤ -1) : 1 / (π * (-x)) < airyModulus x := by
  have hπ := Real.pi_pos
  set s := -x with hs
  have hs1 : 1 ≤ s := by linarith
  have hs0 : 0 < s := by linarith
  obtain ⟨hb, -⟩ := ModulusPhase.modulus_bounds hs0
  rw [hs, neg_neg] at hb
  set r := s ^ (1 / 2 : ℝ)
  have hr2 : r ^ 2 = s := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs0.le]; norm_num
  have hr1 : 1 ≤ r := Real.one_le_rpow hs1 (by norm_num)
  have hrs : r ≤ s := by nlinarith
  have hM := airyModulus_pos x
  have h3 : (s ^ 3)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hs1)
  have hb' : 27 / 32 ≤ π * r * airyModulus x ^ 2 := by linarith
  rw [div_lt_iff₀ (by positivity)]
  -- `(π s M)² ≥ π s · 27/32 > 1`
  have hsq : 1 < (airyModulus x * (π * s)) ^ 2 := by
    have : (airyModulus x * (π * s)) ^ 2 = (π * r * airyModulus x ^ 2) * (π * s * r) := by
      have e : s ^ 2 = s * r ^ 2 := by rw [hr2]; ring
      linear_combination (airyModulus x ^ 2 * π ^ 2) * e
    rw [this]
    have hsr : 1 ≤ s * r := one_le_mul_of_one_le_of_one_le hs1 hr1
    have h1 : 3 ≤ π * s * r := by nlinarith [Real.pi_gt_three]
    nlinarith
  nlinarith [sq_nonneg (airyModulus x * (π * s) - 1), mul_pos hM (mul_pos hπ hs0)]

/-- `Gi` takes both signs arbitrarily far to the left. -/
theorem ScorerZeros.gi_signs (M : ℝ) (σ : ℝ) (hσ : σ = 0 ∨ σ = π) :
    ∃ x < M, x ≤ -1 ∧ Real.cos (airyPhase x) = Real.cos σ := by
  have hπ := Real.pi_pos
  set A := min M (-1) - 1
  obtain ⟨m, hm⟩ := exists_nat_gt (airyPhase A / (2 * π))
  have hmA : airyPhase A < m * (2 * π) := by
    rwa [div_lt_iff₀ (by positivity)] at hm
  obtain ⟨y, hy, hyA⟩ := ((tendsto_airyPhase_atBot.eventually
    (eventually_ge_atTop (m * (2 * π) + π))).and (eventually_lt_atBot A)).exists
  have hσ0 : 0 ≤ σ ∧ σ ≤ π := by rcases hσ with rfl | rfl <;> constructor <;> linarith
  obtain ⟨x, hx, hxθ⟩ := intermediate_value_Icc' hyA.le airyPhase_continuous.continuousOn
    (show m * (2 * π) + σ ∈ Icc (airyPhase A) (airyPhase y) from
      ⟨by linarith, by linarith⟩)
  refine ⟨x, ?_, ?_, ?_⟩
  · have : A < M := by simp only [A]; linarith [min_le_left M (-1)]
    linarith [hx.2]
  · have : A ≤ -2 := by simp only [A]; linarith [min_le_right M (-1)]
    linarith [hx.2]
  · rw [hxθ, add_comm, Real.cos_add_nat_mul_two_pi]

/-- `Gi` takes both positive and negative values below every real `M`. -/
theorem ScorerZeros.gi_frequently (M : ℝ) :
    (∃ x < M, 0 < ScorerZeros.gi x) ∧ ∃ x < M, ScorerZeros.gi x < 0 := by
  have hπ := Real.pi_pos
  constructor
  · obtain ⟨x, hxM, hx1, hc⟩ := ScorerZeros.gi_signs M 0 (Or.inl rfl)
    refine ⟨x, hxM, ?_⟩
    rw [ScorerZeros.gi_eq, DLMF.Airy.Real.airyBi_eq_modulus_cos, hc, Real.cos_zero, mul_one]
    linarith [ScorerZeros.hi_le (show x < 0 by linarith), ScorerZeros.modulus_gt hx1]
  · obtain ⟨x, hxM, hx1, hc⟩ := ScorerZeros.gi_signs M π (Or.inr rfl)
    refine ⟨x, hxM, ?_⟩
    rw [ScorerZeros.gi_eq, DLMF.Airy.Real.airyBi_eq_modulus_cos, hc, Real.cos_pi, mul_neg_one]
    have : 0 < ScorerZeros.hi x := by
      rw [ScorerZeros.hi]
      exact div_pos (by simpa using integral_pow_mul_exp_cubic_pos 0 x) hπ
    linarith [airyModulus_pos x]

/-- The real function `Gi` has infinitely many negative zeros. -/
theorem ScorerZeros.gi_zeros_infinite : {x : ℝ | x < 0 ∧ ScorerZeros.gi x = 0}.Infinite :=
  ODE.sturmCount_infinite_zeros_atBot ScorerZeros.continuous_gi.continuousOn
    (fun M => (ScorerZeros.gi_frequently M).1) (fun M => (ScorerZeros.gi_frequently M).2)

/-- Gi has no nonnegative real zeros, DLMF §9.12(ix). -/
@[dlmf 9.12.ix]
theorem scorerGi_nonneg_ne_zero {x : ℝ} (hx : 0 ≤ x) :
    scorerGi x ≠ 0 := by
  rw [ScorerZeros.gi_ofReal, ofReal_ne_zero]
  exact (ScorerZeros.gi_pos hx).ne'

/-- Gi' has exactly one nonnegative real zero, DLMF §9.12(ix). -/
@[dlmf 9.12.ix]
theorem scorerGiDeriv_unique_nonneg_zero : ∃! x : ℝ, 0 ≤ x ∧ scorerGiDeriv x = 0 := by
  obtain ⟨X, hX, hX0⟩ := (ScorerZeros.gi'_eventually_neg.and (eventually_gt_atTop 0)).exists
  obtain ⟨x, hx, hx0⟩ := intermediate_value_Icc' hX0.le ScorerZeros.continuous_gi'.continuousOn
    ⟨hX.le, ScorerZeros.gi'_zero_pos.le⟩
  refine ⟨x, ⟨hx.1, by rw [ScorerZeros.gi'_ofReal, hx0, ofReal_zero]⟩, fun y ⟨hy, hy0⟩ => ?_⟩
  rw [ScorerZeros.gi'_ofReal, ofReal_eq_zero] at hy0
  rcases lt_trichotomy y x with h | h | h
  · exact (ScorerZeros.gi'_zero_unique hy h hy0 hx0).elim
  · exact h
  · exact (ScorerZeros.gi'_zero_unique hx.1 h hx0 hy0).elim

/-- Infinitely many negative real zeros, DLMF §9.12(ix). -/
@[dlmf 9.12.ix]
theorem scorerGi_infinite_negative_zeros : Set.Infinite {x : ℝ | x < 0 ∧ scorerGi x = 0} := by
  convert ScorerZeros.gi_zeros_infinite using 3 with x
  rw [ScorerZeros.gi_ofReal, ofReal_eq_zero]

/-- Infinitely many negative real zeros, DLMF §9.12(ix). -/
@[dlmf 9.12.ix]
theorem scorerGiDeriv_infinite_negative_zeros :
    Set.Infinite {x : ℝ | x < 0 ∧ scorerGiDeriv x = 0} := by
  have h := ODE.sturmCount_infinite_deriv_zeros (s := Iio 0) ordConnected_Iio
    (fun x _ => ScorerZeros.hasDerivAt_gi x) ScorerZeros.gi_zeros_infinite
  convert h using 3 with x
  rw [ScorerZeros.gi'_ofReal, ofReal_eq_zero]; rfl

/-- Near a zero `x₀` of `f` with `f'(x₀) = d ≠ 0`, the sign of `f x` is that of `d (x - x₀)`. -/
private theorem ScorerZeros.eventually_sign {f : ℝ → ℝ} {d x₀ : ℝ} (hf : HasDerivAt f d x₀)
    (h0 : f x₀ = 0) (hd : d ≠ 0) : ∀ᶠ x in 𝓝[≠] x₀, 0 < f x * (d * (x - x₀)) := by
  have hsl := hasDerivAt_iff_tendsto_slope.mp hf
  have hev : ∀ᶠ x in 𝓝[≠] x₀, 0 < slope f x₀ x * d :=
    (hsl.mul_const d).eventually (lt_mem_nhds (mul_self_pos.mpr hd))
  filter_upwards [hev, self_mem_nhdsWithin] with x hx hne
  have hx0 : x - x₀ ≠ 0 := sub_ne_zero.mpr hne
  rw [slope_def_field, h0, sub_zero] at hx
  have e : f x * (d * (x - x₀)) = f x / (x - x₀) * d * (x - x₀) ^ 2 := by
    field_simp
  rw [e]
  exact mul_pos hx (by positivity)

/-- The energy `E = Gi'² - x Gi² + 2 Gi/π`, with `E' = -Gi²`. -/
private theorem ScorerZeros.hasDerivAt_energy (x : ℝ) :
    HasDerivAt (fun t => ScorerZeros.gi' t ^ 2 - t * ScorerZeros.gi t ^ 2 +
      2 * ScorerZeros.gi t / π) (-(ScorerZeros.gi x ^ 2)) x := by
  have h1 := (ScorerZeros.hasDerivAt_gi' x).pow 2
  have h2 := (hasDerivAt_id x).mul ((ScorerZeros.hasDerivAt_gi x).pow 2)
  have h3 := ((ScorerZeros.hasDerivAt_gi x).const_mul 2).div_const π
  refine ((h1.sub h2).add h3).congr_deriv ?_
  simp only [id, Pi.pow_apply]
  field_simp
  ring

/-- The energy is antitone. -/
private theorem ScorerZeros.antitone_energy :
    Antitone (fun t => ScorerZeros.gi' t ^ 2 - t * ScorerZeros.gi t ^ 2 +
      2 * ScorerZeros.gi t / π) :=
  antitone_of_deriv_nonpos (fun x => (ScorerZeros.hasDerivAt_energy x).differentiableAt)
    fun x => by
      rw [(ScorerZeros.hasDerivAt_energy x).deriv]; nlinarith [sq_nonneg (ScorerZeros.gi x)]

/-- For `x < 0` with `Gi(x) < 0`, the energy is nonnegative. -/
private theorem ScorerZeros.energy_nonneg {x : ℝ} (hx : x < 0) (hg : ScorerZeros.gi x < 0) :
    0 ≤ ScorerZeros.gi' x ^ 2 - x * ScorerZeros.gi x ^ 2 + 2 * ScorerZeros.gi x / π := by
  obtain ⟨z, hz, hz0⟩ := intermediate_value_Ioo hx.le ScorerZeros.continuous_gi.continuousOn
    ⟨hg, ScorerZeros.gi_zero_pos⟩
  have := ScorerZeros.antitone_energy hz.1.le
  simp only [hz0] at this
  norm_num at this
  nlinarith [sq_nonneg (ScorerZeros.gi' z)]

/-- At a critical point `c < 0` with `Gi(c) ≤ 0`: `Gi(c) < 0` and `c Gi(c) ≥ 2/π`. -/
private theorem ScorerZeros.critical_of_nonpos {c : ℝ} (hc : c < 0) (h1 : ScorerZeros.gi' c = 0)
    (h2 : ScorerZeros.gi c ≤ 0) : ScorerZeros.gi c < 0 ∧ 2 / π ≤ c * ScorerZeros.gi c := by
  have hπ := Real.pi_pos
  rcases h2.lt_or_eq with hlt | heq
  · refine ⟨hlt, ?_⟩
    have hE := ScorerZeros.energy_nonneg hc hlt
    rw [h1] at hE
    have : 0 ≤ ScorerZeros.gi c * (2 / π - c * ScorerZeros.gi c) := by
      have e : ScorerZeros.gi c * (2 / π - c * ScorerZeros.gi c) =
          0 ^ 2 - c * ScorerZeros.gi c ^ 2 + 2 * ScorerZeros.gi c / π := by ring
      rw [e]; exact hE
    nlinarith
  · exfalso
    -- `Gi'' (c) = -1/π`, so `Gi' < 0` just right of `c`
    have hd := ScorerZeros.hasDerivAt_gi' c
    rw [heq, mul_zero, zero_sub] at hd
    have hev := (ScorerZeros.eventually_sign hd h1 (by
      have := Real.pi_pos; exact neg_ne_zero.mpr (one_div_pos.mpr this).ne')).filter_mono
      (nhdsGT_le_nhdsNE c)
    obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (hev.and
      (Ioo_mem_nhdsGT (show c < c / 2 by linarith)))
    have hu' : c < u := hu
    set x₁ := (c + u) / 2 with hx₁
    have hmem : ∀ x ∈ Ioc c x₁, ScorerZeros.gi' x < 0 ∧ x < 0 := by
      intro x hx
      obtain ⟨h1, h2⟩ := hsub ⟨hx.1, by linarith [hx.2]⟩
      have hxc : 0 < x - c := sub_pos.mpr hx.1
      refine ⟨?_, by linarith [h2.2]⟩
      have : ScorerZeros.gi' x * ((x - c) / π) < 0 := by
        have e : ScorerZeros.gi' x * (-(1 / π) * (x - c)) =
            -(ScorerZeros.gi' x * ((x - c) / π)) := by ring
        rw [e] at h1; linarith
      by_contra hc'
      have : 0 ≤ ScorerZeros.gi' x * ((x - c) / π) :=
        mul_nonneg (not_lt.mp hc') (by positivity)
      linarith
    have hcx : c < x₁ := by rw [hx₁]; linarith
    have hanti : StrictAntiOn ScorerZeros.gi (Icc c x₁) := by
      refine strictAntiOn_of_deriv_neg (convex_Icc c x₁)
        ScorerZeros.continuous_gi.continuousOn fun x hx => ?_
      rw [interior_Icc] at hx
      rw [(ScorerZeros.hasDerivAt_gi x).deriv]
      exact (hmem x ⟨hx.1, hx.2.le⟩).1
    have hneg : ∀ x ∈ Ioc c x₁, ScorerZeros.gi x < 0 := fun x hx => by
      have := hanti ⟨le_rfl, hcx.le⟩ ⟨hx.1.le, hx.2⟩ hx.1
      rwa [heq] at this
    have hEanti : StrictAntiOn (fun t => ScorerZeros.gi' t ^ 2 - t * ScorerZeros.gi t ^ 2 +
        2 * ScorerZeros.gi t / π) (Icc c x₁) := by
      refine strictAntiOn_of_deriv_neg (convex_Icc c x₁)
        (fun x _ => (ScorerZeros.hasDerivAt_energy x).continuousAt.continuousWithinAt)
        fun x hx => ?_
      rw [interior_Icc] at hx
      rw [(ScorerZeros.hasDerivAt_energy x).deriv]
      have := hneg x ⟨hx.1, hx.2.le⟩
      nlinarith
    have hlt := hEanti ⟨le_rfl, hcx.le⟩ ⟨hcx.le, le_rfl⟩ hcx
    simp only [h1, heq] at hlt
    have hE := ScorerZeros.energy_nonneg (hmem x₁ ⟨hcx, le_rfl⟩).2 (hneg x₁ ⟨hcx, le_rfl⟩)
    norm_num at hlt
    linarith

/-- A function whose derivative is positive at each of its zeros in `[p, q]` cannot vanish at
both `p < q`. -/
private theorem ScorerZeros.not_two_zeros {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    {p q : ℝ} (hpq : p < q) (hp : f p = 0) (hq : f q = 0)
    (hpos : ∀ x ∈ Icc p q, f x = 0 → 0 < f' x) : False := by
  have hcont : Continuous f := continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
  have hdp := hpos p ⟨le_rfl, hpq.le⟩ hp
  obtain ⟨p', hp', hpq'⟩ := (((ScorerZeros.eventually_sign (hf p) hp hdp.ne').filter_mono
    (nhdsGT_le_nhdsNE p)).and (Ioo_mem_nhdsGT hpq)).exists
  have hfp' : 0 < f p' := by
    have : 0 < f' p * (p' - p) := mul_pos hdp (sub_pos.mpr hpq'.1)
    by_contra h
    nlinarith [mul_nonpos_of_nonpos_of_nonneg (not_lt.mp h) this.le]
  set T : Set ℝ := Icc p' q ∩ {x | f x ≤ 0} with hT
  have hTc : IsClosed T := isClosed_Icc.inter (isClosed_le hcont continuous_const)
  have hTn : T.Nonempty := ⟨q, ⟨hpq'.2.le, le_rfl⟩, by simp [hq]⟩
  have hTb : BddBelow T := ⟨p', fun x hx => hx.1.1⟩
  have hm := hTc.csInf_mem hTn hTb
  set m := sInf T
  have hpm : p' < m := lt_of_le_of_ne hm.1.1 (by
    rintro h; rw [← h] at hm; exact absurd (show f p' ≤ 0 from hm.2) (not_le.mpr hfp'))
  have hfm : f m = 0 := by
    by_contra hne
    have hlt : f m < 0 := lt_of_le_of_ne hm.2 hne
    obtain ⟨z, hz, hz0⟩ := intermediate_value_Ioo' hpm.le hcont.continuousOn ⟨hlt, hfp'⟩
    have : m ≤ z := csInf_le hTb ⟨⟨hz.1.le, hz.2.le.trans hm.1.2⟩, by simp [hz0]⟩
    linarith [hz.2]
  have hdm := hpos m ⟨(hpq'.1.trans hpm).le, hm.1.2⟩ hfm
  obtain ⟨x, hx, hxm⟩ := (((ScorerZeros.eventually_sign (hf m) hfm hdm.ne').filter_mono
    (nhdsLT_le_nhdsNE m)).and (Ioo_mem_nhdsLT hpm)).exists
  have hfx : f x ≤ 0 := by
    have : f' m * (x - m) < 0 := mul_neg_of_pos_of_neg hdm (sub_neg.mpr hxm.2)
    by_contra h
    nlinarith [mul_neg_of_pos_of_neg (not_le.mp h) this]
  have : m ≤ x := csInf_le hTb ⟨⟨hxm.1.le, hxm.2.le.trans hm.1.2⟩, hfx⟩
  linarith [hxm.2]

/-- A continuous function without zeros on `(a, b)` has constant sign there. -/
private theorem ScorerZeros.pos_of_pos {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ}
    (hne : ∀ x ∈ Ioo a b, f x ≠ 0) {x y : ℝ} (hx : x ∈ Ioo a b) (hy : y ∈ Ioo a b)
    (hfx : 0 < f x) : 0 < f y := by
  by_contra h
  have hy0 : f y < 0 := lt_of_le_of_ne (not_lt.mp h) (hne y hy)
  obtain ⟨z, hz, hz0⟩ := intermediate_value_uIcc (a := y) (b := x) hf.continuousOn
    (show (0:ℝ) ∈ uIcc (f y) (f x) from Set.mem_uIcc.mpr (Or.inl ⟨hy0.le, hfx.le⟩))
  exact hne z ((ordConnected_Ioo).uIcc_subset hy hx hz) hz0

/-- Between consecutive negative zeros of `Gi` there is exactly one zero of `Gi'` (real form). -/
private theorem ScorerZeros.gi_interlace {a b : ℝ} (hab : a < b) (hb : b < 0)
    (ha0 : ScorerZeros.gi a = 0) (hb0 : ScorerZeros.gi b = 0)
    (hgap : ∀ x ∈ Ioo a b, ScorerZeros.gi x ≠ 0) :
    ∃! x : ℝ, x ∈ Ioo a b ∧ ScorerZeros.gi' x = 0 := by
  obtain ⟨c, hc, hc0⟩ := exists_hasDerivAt_eq_zero hab ScorerZeros.continuous_gi.continuousOn
    (ha0.trans hb0.symm) fun x _ => ScorerZeros.hasDerivAt_gi x
  refine ⟨c, ⟨hc, hc0⟩, fun d ⟨hd, hd0⟩ => ?_⟩
  by_contra hdc
  -- two distinct critical points `c₁ < c₂` in `(a, b)`
  obtain ⟨c₁, c₂, h₁, h₂, h12, e₁, e₂⟩ : ∃ c₁ c₂, c₁ ∈ Ioo a b ∧ c₂ ∈ Ioo a b ∧ c₁ < c₂ ∧
      ScorerZeros.gi' c₁ = 0 ∧ ScorerZeros.gi' c₂ = 0 := by
    rcases lt_or_gt_of_ne hdc with h | h
    · exact ⟨d, c, hd, hc, h, hd0, hc0⟩
    · exact ⟨c, d, hc, hd, h, hc0, hd0⟩
  have hsub : Icc c₁ c₂ ⊆ Ioo a b := fun x hx => ⟨h₁.1.trans_le hx.1, hx.2.trans_lt h₂.2⟩
  rcases lt_or_gt_of_ne (hgap c hc) with hneg | hpos
  · -- `Gi < 0` on `(a, b)`: zeros of `Gi'` are upcrossings
    have hneg' : ∀ x ∈ Ioo a b, ScorerZeros.gi x < 0 := fun x hx => by
      by_contra h
      have := ScorerZeros.pos_of_pos (f := fun t => -ScorerZeros.gi t)
        ScorerZeros.continuous_gi.neg (fun t ht => neg_ne_zero.mpr (hgap t ht)) hc hx
        (by linarith)
      exact h (by linarith)
    refine ScorerZeros.not_two_zeros ScorerZeros.hasDerivAt_gi' h12 e₁ e₂ fun x hx hx0 => ?_
    have hx' := hsub hx
    have := (ScorerZeros.critical_of_nonpos (hx'.2.trans hb) hx0 (hneg' x hx').le).2
    have := Real.pi_pos
    have : 1 / π < 2 / π := by gcongr; norm_num
    linarith
  · have hpos' : ∀ x ∈ Ioo a b, 0 < ScorerZeros.gi x := fun x hx =>
      ScorerZeros.pos_of_pos ScorerZeros.continuous_gi hgap hc hx hpos
    refine ScorerZeros.not_two_zeros (f := fun t => -ScorerZeros.gi' t)
      (fun x => (ScorerZeros.hasDerivAt_gi' x).neg) h12 (by simp [e₁]) (by simp [e₂])
      fun x hx _ => ?_
    have hx' := hsub hx
    have h1 : x * ScorerZeros.gi x < 0 := mul_neg_of_neg_of_pos (hx'.2.trans hb) (hpos' x hx')
    have := Real.pi_pos
    have : 0 < 1 / π := by positivity
    linarith

/-- Between consecutive negative zeros of `Gi'` there is exactly one zero of `Gi` (real form). -/
private theorem ScorerZeros.gi'_interlace {a b : ℝ} (hab : a < b) (hb : b < 0)
    (ha0 : ScorerZeros.gi' a = 0) (hb0 : ScorerZeros.gi' b = 0)
    (hgap : ∀ x ∈ Ioo a b, ScorerZeros.gi' x ≠ 0) :
    ∃! x : ℝ, x ∈ Ioo a b ∧ ScorerZeros.gi x = 0 := by
  have ha : a < 0 := hab.trans hb
  have hπ := Real.pi_pos
  have hπ' : 0 < 1 / π := by positivity
  have h12 : 1 / π < 2 / π := by gcongr; norm_num
  set m := (a + b) / 2
  have hm : m ∈ Ioo a b := ⟨by simp only [m]; linarith, by simp only [m]; linarith⟩
  have hint : interior (Icc a b) = Ioo a b := interior_Icc
  rcases lt_or_gt_of_ne (hgap m hm) with hneg | hpos
  · have hneg' : ∀ x ∈ Ioo a b, ScorerZeros.gi' x < 0 := fun x hx => by
      by_contra h
      have := ScorerZeros.pos_of_pos (f := fun t => -ScorerZeros.gi' t)
        ScorerZeros.continuous_gi'.neg (fun t ht => neg_ne_zero.mpr (hgap t ht)) hm hx
        (by linarith)
      exact h (by linarith)
    have hga : 0 < ScorerZeros.gi a := by
      by_contra h
      have hc := (ScorerZeros.critical_of_nonpos ha ha0 (not_lt.mp h)).2
      obtain ⟨x, hx, hxab⟩ := (((ScorerZeros.eventually_sign (ScorerZeros.hasDerivAt_gi' a) ha0
        (by linarith)).filter_mono (nhdsGT_le_nhdsNE a)).and (Ioo_mem_nhdsGT hab)).exists
      have := hneg' x hxab
      have : 0 < (a * ScorerZeros.gi a - 1 / π) * (x - a) := mul_pos (by linarith)
        (sub_pos.mpr hxab.1)
      nlinarith
    have hgb : ScorerZeros.gi b < 0 := by
      rcases lt_or_ge 0 (ScorerZeros.gi b) with h | h
      · exfalso
        have hd : b * ScorerZeros.gi b - 1 / π < 0 := by
          nlinarith [mul_neg_of_neg_of_pos hb h]
        obtain ⟨x, hx, hxab⟩ := (((ScorerZeros.eventually_sign (ScorerZeros.hasDerivAt_gi' b)
          hb0 hd.ne).filter_mono (nhdsLT_le_nhdsNE b)).and (Ioo_mem_nhdsLT hab)).exists
        have := hneg' x hxab
        have : 0 < (b * ScorerZeros.gi b - 1 / π) * (x - b) :=
          mul_pos_of_neg_of_neg hd (sub_neg.mpr hxab.2)
        nlinarith
      · exact (ScorerZeros.critical_of_nonpos hb hb0 h).1
    obtain ⟨z, hz, hz0⟩ := intermediate_value_Ioo' hab.le ScorerZeros.continuous_gi.continuousOn
      ⟨hgb, hga⟩
    have hanti : StrictAntiOn ScorerZeros.gi (Icc a b) :=
      strictAntiOn_of_deriv_neg (convex_Icc a b) ScorerZeros.continuous_gi.continuousOn
        fun x hx => by
          rw [hint] at hx; rw [(ScorerZeros.hasDerivAt_gi x).deriv]; exact hneg' x hx
    exact ⟨z, ⟨hz, hz0⟩, fun y ⟨hy, hy0⟩ => hanti.injOn ⟨hy.1.le, hy.2.le⟩
      ⟨hz.1.le, hz.2.le⟩ (hy0.trans hz0.symm)⟩
  · have hpos' : ∀ x ∈ Ioo a b, 0 < ScorerZeros.gi' x := fun x hx =>
      ScorerZeros.pos_of_pos ScorerZeros.continuous_gi' hgap hm hx hpos
    have hga : ScorerZeros.gi a < 0 := by
      rcases lt_or_ge 0 (ScorerZeros.gi a) with h | h
      · exfalso
        have hd : a * ScorerZeros.gi a - 1 / π < 0 := by
          nlinarith [mul_neg_of_neg_of_pos ha h]
        obtain ⟨x, hx, hxab⟩ := (((ScorerZeros.eventually_sign (ScorerZeros.hasDerivAt_gi' a)
          ha0 hd.ne).filter_mono (nhdsGT_le_nhdsNE a)).and (Ioo_mem_nhdsGT hab)).exists
        have := hpos' x hxab
        have : (a * ScorerZeros.gi a - 1 / π) * (x - a) < 0 :=
          mul_neg_of_neg_of_pos hd (sub_pos.mpr hxab.1)
        nlinarith
      · exact (ScorerZeros.critical_of_nonpos ha ha0 h).1
    have hgb : 0 < ScorerZeros.gi b := by
      by_contra h
      have hc := (ScorerZeros.critical_of_nonpos hb hb0 (not_lt.mp h)).2
      obtain ⟨x, hx, hxab⟩ := (((ScorerZeros.eventually_sign (ScorerZeros.hasDerivAt_gi' b) hb0
        (by linarith)).filter_mono (nhdsLT_le_nhdsNE b)).and (Ioo_mem_nhdsLT hab)).exists
      have := hpos' x hxab
      have : (b * ScorerZeros.gi b - 1 / π) * (x - b) < 0 := mul_neg_of_pos_of_neg (by linarith)
        (sub_neg.mpr hxab.2)
      nlinarith
    obtain ⟨z, hz, hz0⟩ := intermediate_value_Ioo hab.le ScorerZeros.continuous_gi.continuousOn
      ⟨hga, hgb⟩
    have hmono : StrictMonoOn ScorerZeros.gi (Icc a b) :=
      strictMonoOn_of_deriv_pos (convex_Icc a b) ScorerZeros.continuous_gi.continuousOn
        fun x hx => by
          rw [hint] at hx; rw [(ScorerZeros.hasDerivAt_gi x).deriv]; exact hpos' x hx
    exact ⟨z, ⟨hz, hz0⟩, fun y ⟨hy, hy0⟩ => hmono.injOn ⟨hy.1.le, hy.2.le⟩
      ⟨hz.1.le, hz.2.le⟩ (hy0.trans hz0.symm)⟩

/-- Every real zero of `Gi` is simple, DLMF §9.12(ix). -/
@[dlmf 9.12.ix "special case: real zeros of Gi"]
theorem scorerGiDeriv_ne_zero_of_scorerGi_ofReal_eq_zero {x : ℝ} (hx : scorerGi x = 0) :
    scorerGiDeriv x ≠ 0 := by
  rw [ScorerZeros.gi_ofReal, ofReal_eq_zero] at hx
  rw [ScorerZeros.gi'_ofReal, ne_eq, ofReal_eq_zero]
  intro h
  rcases lt_or_ge x 0 with hneg | hnn
  · exact (ScorerZeros.critical_of_nonpos hneg h hx.le).1.ne hx
  · exact (ScorerZeros.gi_pos hnn).ne' hx

/-- Negative zeros of Gi and Gi' interlace, DLMF §9.12(ix). -/
@[dlmf 9.12.ix]
theorem scorerGi_zeros_interlace {a b : ℝ} (hab : a < b) (hb : b < 0)
    (ha0 : scorerGi a = 0) (hb0 : scorerGi b = 0)
    (hgap : ∀ x ∈ Ioo a b, scorerGi x ≠ 0) :
    ∃! x : ℝ, x ∈ Ioo a b ∧ scorerGiDeriv x = 0 := by
  simp only [ScorerZeros.gi_ofReal, ScorerZeros.gi'_ofReal, ofReal_eq_zero, ne_eq] at *
  exact ScorerZeros.gi_interlace hab hb ha0 hb0 hgap

/-- The reverse interlacing of the negative zeros of Gi and Gi', DLMF §9.12(ix). -/
@[dlmf 9.12.ix]
theorem scorerGiDeriv_zeros_interlace {a b : ℝ} (hab : a < b) (hb : b < 0)
    (ha0 : scorerGiDeriv a = 0) (hb0 : scorerGiDeriv b = 0)
    (hgap : ∀ x ∈ Ioo a b, scorerGiDeriv x ≠ 0) :
    ∃! x : ℝ, x ∈ Ioo a b ∧ scorerGi x = 0 := by
  simp only [ScorerZeros.gi_ofReal, ScorerZeros.gi'_ofReal, ofReal_eq_zero, ne_eq] at *
  exact ScorerZeros.gi'_interlace hab hb ha0 hb0 hgap

/-- `Ai` is bounded on `[0, ∞)`. -/
private theorem ScorerPrincipalValue.exists_norm_airyAi_le :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℝ, 0 ≤ s → ‖airyAi s‖ ≤ M := by
  obtain ⟨R, hR⟩ := (eventually_atTop.mp ((tendsto_order.1
    DLMF.Airy.Real.tendsto_airyAi_atTop.norm).2 1 (by norm_num)))
  have hc : ContinuousOn (fun s : ℝ => airyAi s) (Icc 0 R) :=
    Continuous.continuousOn (continuous_iff_continuousAt.mpr fun s =>
      ((hasDerivAt_airyAi (s : ℂ)).comp_ofReal (z := s)).continuousAt)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max C 1, le_max_of_le_right zero_le_one, fun s hs => ?_⟩
  rcases le_or_gt s R with h | h
  · exact (hC s ⟨hs, h⟩).trans (le_max_left _ _)
  · rw [airyAi_ofReal_eq, Complex.norm_real]
    exact (hR s h.le).le.trans (le_max_right _ _)

/-- `K_{1/3}(t) = O(t^{-1/3})` on `(0, ∞)`, through `Ai(x) = π⁻¹ √(x/3) K_{1/3}(ζ)`. -/
private theorem ScorerPrincipalValue.exists_norm_besselK_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t →
      ‖DLMF.Bessel.besselK (1 / 3) (t : ℂ)‖ ≤ C * t ^ (-(1 / 3) : ℝ) := by
  obtain ⟨M, hM0, hM⟩ := ScorerPrincipalValue.exists_norm_airyAi_le
  refine ⟨M * π * Real.sqrt 3 * (3 / 2 : ℝ) ^ (-(1 / 3) : ℝ), by positivity, fun t ht => ?_⟩
  set s : ℝ := (3 * t / 2) ^ (2 / 3 : ℝ) with hs
  have hs0 : 0 < s := by positivity
  have hζ : airyZeta s = t := by
    rw [airyZeta, hs, ← Real.rpow_mul (by positivity)]
    norm_num
  have hA := airyAi_eq_besselK hs0
  rw [hζ] at hA
  have hq : 0 < π⁻¹ * Real.sqrt (s / 3) := by positivity
  have hK : DLMF.Bessel.besselK (1 / 3) (t : ℂ) =
      airyAi s / ((π⁻¹ * Real.sqrt (s / 3) : ℝ) : ℂ) := by
    rw [hA, mul_div_cancel_left₀ _ (ofReal_ne_zero.mpr hq.ne')]
  have hsq : Real.sqrt s = (3 / 2 : ℝ) ^ (1 / 3 : ℝ) * t ^ (1 / 3 : ℝ) := by
    rw [Real.sqrt_eq_rpow, hs, ← Real.rpow_mul (by positivity), show 3 * t / 2 = 3 / 2 * t by ring,
      Real.mul_rpow (by norm_num) ht.le]
    norm_num
  rw [hK, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq]
  rw [div_le_iff₀ hq]
  have h1 := hM s hs0.le
  have h3 : Real.sqrt (s / 3) = Real.sqrt s / Real.sqrt 3 := Real.sqrt_div' s (by norm_num)
  have hpos3 : 0 < Real.sqrt 3 := by positivity
  have e : M * π * Real.sqrt 3 * (3 / 2 : ℝ) ^ (-(1 / 3) : ℝ) * t ^ (-(1 / 3) : ℝ) *
      (π⁻¹ * Real.sqrt (s / 3)) = M := by
    rw [h3, hsq, Real.rpow_neg (by norm_num), Real.rpow_neg ht.le]
    have : (0:ℝ) < (3 / 2 : ℝ) ^ (1 / 3 : ℝ) := by positivity
    have : (0:ℝ) < t ^ (1 / 3 : ℝ) := by positivity
    field_simp
  rw [e]; exact h1

/-- `t ↦ K_{1/3}(t)` is differentiable at every `t > 0`. -/
private theorem ScorerPrincipalValue.hasDerivAt_besselK {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => DLMF.Bessel.besselK (1 / 3) (s : ℂ))
      ((1 / 3 / (t : ℂ)) * DLMF.Bessel.besselK (1 / 3) t -
        DLMF.Bessel.besselK (1 / 3 + 1) t) t :=
  (DLMF.Bessel.hasDerivAt_besselK (1 / 3) (Complex.ofReal_mem_slitPlane.mpr ht)).comp_ofReal

/-- Convergence of the symmetric principal value in DLMF 9.12.23. -/
@[dlmf 9.12.E23]
theorem scorerGi_principalValue_converges {x : ℝ} (hx : 0 < x) :
    let f := fun t : ℝ => DLMF.Bessel.besselK (1 / 3) t /
      ((airyZeta x : ℂ) ^ 2 - (t : ℂ) ^ 2)
    HasPrincipalValueIoi f (airyZeta x) (principalValueIoi f (airyZeta x)) := by
  intro f
  set c := airyZeta x with hcdef
  have hc : 0 < c := airyZeta_pos hx
  set K : ℝ → ℂ := fun s => DLMF.Bessel.besselK (1 / 3) (s : ℂ) with hK
  have hKc : ContinuousOn K (Ioi 0) := fun t ht =>
    (ScorerPrincipalValue.hasDerivAt_besselK ht).continuousAt.continuousWithinAt
  obtain ⟨C, hC0, hC⟩ := ScorerPrincipalValue.exists_norm_besselK_le
  set h : ℝ → ℂ := fun t => K t * (-((c : ℂ) + t)⁻¹) with hh
  have hfh : ∀ t : ℝ, 0 ≤ t → t ≠ c → f t = h t / (t - c) := by
    intro t ht htc
    have h1 : (t : ℂ) - c ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast htc)
    have h2 : (c : ℂ) + t ≠ 0 := by exact_mod_cast (by linarith : c + t ≠ 0)
    simp only [f, h, hK]
    rw [show (c : ℂ) ^ 2 - (t : ℂ) ^ 2 = -(((t : ℂ) - c) * ((c : ℂ) + t)) by ring]
    field_simp
  set b : ℝ := c + 1 with hb
  have hcb : c < b := by rw [hb]; linarith
  have hKi : IntegrableOn K (Icc 0 b) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    have hr : IntegrableOn (fun t : ℝ => C * t ^ (-(1 / 3) : ℝ)) (Ioc 0 b) := by
      have := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := b)
        (r := (-(1 / 3) : ℝ)) (by norm_num)
      exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mp this).const_mul C
    refine hr.mono' ((hKc.mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hC t ht.1
  have hqc : ContinuousOn (fun t : ℝ => -((c : ℂ) + t)⁻¹) (Icc 0 b) := by
    intro t ht
    have : (c : ℂ) + t ≠ 0 := by exact_mod_cast (by linarith [ht.1] : c + t ≠ 0)
    exact ((continuous_const.add continuous_ofReal).continuousAt.inv₀ this).neg.continuousWithinAt
  have hhi : IntegrableOn h (Icc 0 b) := hKi.mul_continuousOn hqc isCompact_Icc
  have hhd : DifferentiableAt ℝ h c := by
    have : (c : ℂ) + c ≠ 0 := by exact_mod_cast (by linarith : c + c ≠ 0)
    exact (ScorerPrincipalValue.hasDerivAt_besselK hc).differentiableAt.mul
      (((differentiableAt_const _).add Complex.ofRealCLM.differentiableAt).inv this).neg
  have hsub0 := pv_integrableOn_sub_of_differentiableAt hhi hhd
  have hsub : IntegrableOn (fun t => f t - h c / (t - c)) (Icc 0 b) := by
    refine hsub0.congr_fun_ae ?_
    have : ∀ᵐ t ∂(volume.restrict (Icc 0 b)), t ≠ c :=
      ae_restrict_of_ae (by simp [ae_iff, measure_singleton])
    filter_upwards [this, ae_restrict_mem measurableSet_Icc] with t ht ht'
    simp only [hfh t ht'.1 ht]
  have htail : ∀ d : ℝ, c < d → IntegrableOn f (Ioi d) := by
    intro d hd
    have hd0 : 0 < d := hc.trans hd
    have hk : 0 < 1 - c ^ 2 / d ^ 2 := by
      have : c ^ 2 / d ^ 2 < 1 := (div_lt_one (by positivity)).mpr (by nlinarith)
      linarith
    have hr : IntegrableOn (fun t : ℝ => C * d ^ (-(1 / 3) : ℝ) / (1 - c ^ 2 / d ^ 2) *
        t ^ (-2 : ℝ)) (Ioi d) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num) hd0).const_mul _
    have hfc : ContinuousOn f (Ioi d) := by
      intro t ht
      have ht0 : 0 < t := hd0.trans ht
      have hne : (c : ℂ) ^ 2 - (t : ℂ) ^ 2 ≠ 0 := by
        rw [← ofReal_pow, ← ofReal_pow, ← ofReal_sub, ofReal_ne_zero]
        nlinarith [show c < t from hd.trans ht]
      exact ((ScorerPrincipalValue.hasDerivAt_besselK ht0).continuousAt.div
        (continuous_const.sub (continuous_ofReal.pow 2)).continuousAt hne).continuousWithinAt
    refine hr.mono' (hfc.aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht : d < t := ht
    have ht0 : 0 < t := hd0.trans ht
    have hden : (1 - c ^ 2 / d ^ 2) * t ^ 2 ≤ t ^ 2 - c ^ 2 := by
      have : c ^ 2 / d ^ 2 * t ^ 2 ≥ c ^ 2 := by
        rw [ge_iff_le, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        have : d ^ 2 ≤ t ^ 2 := by nlinarith
        nlinarith [sq_nonneg c]
      nlinarith
    have hpos : 0 < (1 - c ^ 2 / d ^ 2) * t ^ 2 := by positivity
    simp only [f]
    rw [norm_div, show (c : ℂ) ^ 2 - (t : ℂ) ^ 2 = ((c ^ 2 - t ^ 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by nlinarith), Real.rpow_neg ht0.le,
      Real.rpow_two]
    have hKt : ‖DLMF.Bessel.besselK (1 / 3) (t : ℂ)‖ ≤ C * d ^ (-(1 / 3) : ℝ) :=
      (hC t ht0).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hd0 ht.le (by norm_num)) hC0)
    rw [div_le_iff₀ (by nlinarith)]
    calc ‖DLMF.Bessel.besselK (1 / 3) (t : ℂ)‖ ≤ C * d ^ (-(1 / 3) : ℝ) := hKt
      _ = C * d ^ (-(1 / 3) : ℝ) / (1 - c ^ 2 / d ^ 2) * (t ^ 2)⁻¹ *
          ((1 - c ^ 2 / d ^ 2) * t ^ 2) := by
            have : (0:ℝ) < d ^ 2 - c ^ 2 := by nlinarith
            field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hI : ∀ d : ℝ, c < d → HasIntegralAtTop f d (∫ t in Ioi d, f t) := fun d hd =>
    intervalIntegral_tendsto_integral_Ioi d (htail d hd) tendsto_id
  have himp : ∀ d : ℝ, c < d → improperAtTop f d = ∫ t in Ioi d, f t := fun d hd =>
    (hI d hd).limUnder_eq
  have hP : HasPrincipalValueIoi f c ((∫ t in (0:ℝ)..b, (f t - h c / (t - c))) +
      h c * Real.log ((b - c) / (c - 0)) + ∫ t in Ioi b, f t) := by
    refine ⟨fun ε hε => ?_, ?_⟩
    · rw [himp _ (by linarith)]; exact hI _ (by linarith)
    have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (∫ t in (0:ℝ)..c - ε, f t) + improperAtTop f (c + ε) =
        ((∫ t in (0:ℝ)..c - ε, f t) + ∫ t in c + ε..b, f t) + ∫ t in Ioi b, f t := by
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
    exact ((pv_tendsto_of_integrableOn_sub (h c) hc hcb hsub).add_const _).congr'
      (EventuallyEq.symm hev)
  refine ⟨hP.1, ?_⟩
  rw [principalValueIoi, hP.2.limUnder_eq]
  exact hP.2

end DLMF.Airy

end
