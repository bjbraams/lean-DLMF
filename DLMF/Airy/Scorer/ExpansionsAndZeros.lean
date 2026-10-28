/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Airy.Scorer.Representations

/-!
# Scorer asymptotic expansions and real zeros

Asymptotic expansions of Gi and Hi and their derivatives, followed by the real zero-counting
results.

Source references and common attribution are retained in
`DLMF.Airy.Scorer`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF.Confluent

open scoped Real Topology Nat

namespace DLMF.Airy

macro "sqrt3_ring" : tactic =>
  `(tactic| (ring_nf; simp only [sqrt_three_sq, sqrt_three_pow_three_complex,
    sqrt_three_pow_four, I_sq, I_pow_three]; ring_nf))

/-! ### Asymptotic expansions of Hi, Hi', Gi, Gi' (DLMF 9.12(viii))

The Laplace integrals `π Hi(z) = ∫₀^∞ e^{zt} e^{-t³/3} dt` and `π Hi'(z) = ∫₀^∞ e^{zt} t e^{-t³/3} dt`
are rotated to rays `|arg t| < π/6` and expanded by Watson's lemma
(`hasAsymptoticExpansion_integral_cexp_smul_rotate_comap`); two rotated rays cover the sector
`|arg(-z)| < 2π/3`. The expansions of `Gi`, `Gi'` follow from the rotation formula 9.12.12. -/

/-- The cubic kernel `e^{-t³/3}` along the ray `t = r e^{iy}`. -/
theorem scorerAsym_norm_kernel (r y : ℝ) :
    ‖cexp (-(((r : ℂ) * exp (y * I)) ^ 3 / 3))‖ = Real.exp (-(r ^ 3 * Real.cos (3 * y)) / 3) := by
  rw [Complex.norm_exp]
  congr 1
  have h : ((r : ℂ) * exp (y * I)) ^ 3 = ((r ^ 3 : ℝ) : ℂ) * exp (((3 * y : ℝ) : ℂ) * I) := by
    rw [mul_pow, ← Complex.exp_nat_mul]; push_cast; ring_nf
  rw [h, neg_re, div_ofNat_re, re_ofReal_mul, exp_ofReal_mul_I_re]
  ring

/-- The cubic kernel is bounded by `1` in the sector `|arg t| ≤ π/6`. -/
theorem scorerAsym_norm_kernel_le_one {r : ℝ} (hr : 0 ≤ r) {y : ℝ} (hy : |y| ≤ π / 6) :
    ‖cexp (-(((r : ℂ) * exp (y * I)) ^ 3 / 3))‖ ≤ 1 := by
  rw [scorerAsym_norm_kernel, Real.exp_le_one_iff]
  have : 0 ≤ Real.cos (3 * y) := by
    rw [← Real.cos_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [abs_nonneg y, Real.pi_pos], by linarith⟩
  have := mul_nonneg (pow_nonneg hr 3) this
  linarith

/-- `r^m e^{-cr - br³}` is integrable on `(0, ∞)` for `b > 0`. -/
theorem scorerAsym_integrableOn_pow_exp (m : ℕ) (c : ℝ) {b : ℝ} (hb : 0 < b) :
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
theorem scorerAsym_integrableOn_rotate (m : ℕ) (c : ℝ) {θ : ℝ} (hθ : |θ| < π / 6) :
    IntegrableOn (fun r : ℝ => Real.exp (-c * r) •
      (((r : ℂ) * exp (θ * I)) ^ m * cexp (-(((r : ℂ) * exp (θ * I)) ^ 3 / 3)))) (Ioi 0) := by
  have hb : 0 < Real.cos (3 * θ) / 3 := by
    have : 0 < Real.cos (3 * θ) := by
      rw [← Real.cos_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
      exact Real.cos_pos_of_mem_Ioo ⟨by linarith [abs_nonneg θ, Real.pi_pos], by linarith⟩
    positivity
  refine (scorerAsym_integrableOn_pow_exp m c hb).mono' ?_ ?_
  · exact (Continuous.aestronglyMeasurable (by fun_prop))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r (hr : 0 < r)
    rw [norm_smul, norm_mul, norm_pow, norm_mul, norm_real, norm_exp_ofReal_mul_I, mul_one,
      scorerAsym_norm_kernel, Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.norm_of_nonneg hr.le, ← mul_assoc, mul_comm (Real.exp _), mul_assoc, ← Real.exp_add]
    apply le_of_eq; congr 2; ring

/-- The Laplace integral `∫₀^∞ e^{-wt} t^m e^{-t³/3} dt` (an entire function of `w`). -/
noncomputable def scorerAsym_laplace (m : ℕ) (w : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), cexp (-(w * t)) • ((t : ℂ) ^ m * cexp (-((t : ℂ) ^ 3 / 3)))

/-- `e^{-ct} tᵐ e^{-t³/3}` is integrable on `(0, ∞)` for every real `c`. -/
theorem scorerAsym_integrableOn_zero (m : ℕ) (c : ℝ) :
    IntegrableOn (fun t : ℝ => Real.exp (-c * t) • ((t : ℂ) ^ m * cexp (-((t : ℂ) ^ 3 / 3))))
      (Ioi 0) := by
  have h := scorerAsym_integrableOn_rotate m c (θ := 0) (by rw [abs_zero]; positivity)
  simpa using h

/-- The Laplace integral `∫₀^∞ e^{-wt} tᵐ e^{-t³/3} dt` is an entire function of `w`. -/
theorem scorerAsym_differentiable_laplace (m : ℕ) : Differentiable ℂ (scorerAsym_laplace m) :=
  fun w => (differentiableOn_integral_cexp_neg_mul_smul
    (scorerAsym_integrableOn_zero m (w.re - 1))).differentiableAt
    ((isOpen_lt continuous_const continuous_re).mem_nhds (by simp))

/-- Hi and Hi' as Laplace integrals: `π Hi(z) = L₀(-z)`, `π Hi'(z) = L₁(-z)`. -/
theorem scorerAsym_scorerHi_eq (z : ℂ) : π * scorerHi z = scorerAsym_laplace 0 (-z) := by
  rw [(scorerHi_exp_integral z).2, scorerAsym_laplace, mul_div_cancel₀ _
    (ofReal_ne_zero.mpr Real.pi_ne_zero)]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [smul_eq_mul, pow_zero, one_mul]
  rw [← Complex.exp_add]; ring_nf

/-- `π Hi'(z) = L₁(-z)`, the Laplace integral of `t e^{-t³/3}` at `-z`. -/
theorem scorerAsym_scorerHiDeriv_eq (z : ℂ) : π * scorerHiDeriv z = scorerAsym_laplace 1 (-z) := by
  rw [scorerHiDeriv_exp_integral z, scorerAsym_laplace, mul_div_cancel₀ _
    (ofReal_ne_zero.mpr Real.pi_ne_zero)]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [smul_eq_mul, pow_one]
  rw [mul_left_comm, ← Complex.exp_add]; ring_nf

/-- **Rotation of the Laplace contour** for `|θ| < π/6`, valid for every complex `w`. -/
theorem scorerAsym_laplace_rotate (m : ℕ) {θ : ℝ} (hθ : |θ| < π / 6) (w : ℂ) :
    scorerAsym_laplace m w = exp (θ * I) • ∫ r in Ioi (0 : ℝ), cexp (-(w * exp (θ * I) * r)) •
      (((r : ℂ) * exp (θ * I)) ^ m * cexp (-(((r : ℂ) * exp (θ * I)) ^ 3 / 3))) := by
  have hd2 : Differentiable ℂ (fun w : ℂ => exp (θ * I) • ∫ r in Ioi (0 : ℝ),
      cexp (-(w * exp (θ * I) * r)) •
        (((r : ℂ) * exp (θ * I)) ^ m * cexp (-(((r : ℂ) * exp (θ * I)) ^ 3 / 3)))) := by
    have hL : Differentiable ℂ (fun v : ℂ => ∫ r in Ioi (0 : ℝ), cexp (-(v * r)) •
        (((r : ℂ) * exp (θ * I)) ^ m * cexp (-(((r : ℂ) * exp (θ * I)) ^ 3 / 3)))) := fun v =>
      (differentiableOn_integral_cexp_neg_mul_smul
        (scorerAsym_integrableOn_rotate m (v.re - 1) hθ)).differentiableAt
        ((isOpen_lt continuous_const continuous_re).mem_nhds (by simp))
    exact (hL.comp (differentiable_id.mul_const (exp (θ * I)))).const_smul (exp (θ * I))
  have hy : ∀ y ∈ uIcc 0 θ, |y| ≤ π / 6 := fun y hy =>
    (abs_le_abs_of_mem_uIcc_zero hy).trans hθ.le
  have hreal : ∀ x : ℝ, 0 < x → scorerAsym_laplace m x = exp (θ * I) • ∫ r in Ioi (0 : ℝ),
      cexp (-((x : ℂ) * exp (θ * I) * r)) •
        (((r : ℂ) * exp (θ * I)) ^ m * cexp (-(((r : ℂ) * exp (θ * I)) ^ 3 / 3))) := by
    intro x hx
    simp only [scorerAsym_laplace, smul_eq_mul]
    refine integral_cexp_neg_mul_mul_eq_rotate (F := fun t => t ^ m * cexp (-(t ^ 3 / 3)))
      (σ := m + 1) (C := 1) (k := m) (by positivity) (fun r _ y _ => by fun_prop)
      (fun r hr _ y hy' => ?_) (fun r hr y hy' => ?_) (fun y hy' => ?_)
    · rw [add_sub_cancel_right, one_mul, Real.rpow_natCast, norm_mul, norm_pow, norm_mul,
        norm_real, Real.norm_of_nonneg hr.le, norm_exp_ofReal_mul_I, mul_one]
      calc r ^ m * _ ≤ r ^ m * 1 := by
            gcongr; exact scorerAsym_norm_kernel_le_one hr.le (hy y hy')
        _ = r ^ m := mul_one _
    · have hr0 : 0 ≤ r := by linarith
      rw [one_mul, Real.rpow_natCast, norm_mul, norm_pow, norm_mul,
        norm_real, Real.norm_of_nonneg hr0, norm_exp_ofReal_mul_I, mul_one]
      calc r ^ m * _ ≤ r ^ m * 1 := by
            gcongr; exact scorerAsym_norm_kernel_le_one hr0 (hy y hy')
        _ = r ^ m := mul_one _
    · rw [re_ofReal_mul, exp_ofReal_mul_I_re]
      have := hy y hy'
      exact mul_pos hx (Real.cos_pos_of_mem_Ioo ⟨by linarith [neg_abs_le y, Real.pi_pos],
        by linarith [le_abs_self y, Real.pi_pos]⟩)
  have hfreq : ∃ᶠ v in 𝓝[≠] (1 : ℂ), scorerAsym_laplace m v = exp (θ * I) •
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
  exact ((scorerAsym_differentiable_laplace m).differentiableOn.analyticOnNhd
    isOpen_univ).eqOn_of_preconnected_of_frequently_eq
    (hd2.differentiableOn.analyticOnNhd isOpen_univ) isPreconnected_univ (mem_univ _) hfreq
    (mem_univ w)

/-- Taylor coefficients of `e^{-t³/3} = ∑ aₙ tⁿ`. -/
noncomputable def scorerAsym_coeff (n : ℕ) : ℂ :=
  if 3 ∣ n then (-1 / 3 : ℂ) ^ (n / 3) / ((n / 3).factorial : ℂ) else 0

/-- Partial sums of the Taylor series `∑ aₙ tⁿ` of `e^{-t³/3}` up to `3M`, `3M+1` and `3M+2` terms
equal the partial sums of the exponential series in `-t³/3`. -/
theorem scorerAsym_sum_coeff (t : ℂ) (M : ℕ) :
    (∑ n ∈ Finset.range (3 * M), t ^ n * scorerAsym_coeff n =
      ∑ k ∈ Finset.range M, (-(t ^ 3 / 3)) ^ k / (k.factorial : ℂ)) ∧
    (∑ n ∈ Finset.range (3 * M + 1), t ^ n * scorerAsym_coeff n =
      ∑ k ∈ Finset.range (M + 1), (-(t ^ 3 / 3)) ^ k / (k.factorial : ℂ)) ∧
    (∑ n ∈ Finset.range (3 * M + 2), t ^ n * scorerAsym_coeff n =
      ∑ k ∈ Finset.range (M + 1), (-(t ^ 3 / 3)) ^ k / (k.factorial : ℂ)) := by
  have h0 : ∀ M : ℕ, ∑ n ∈ Finset.range (3 * M), t ^ n * scorerAsym_coeff n =
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
      simp only [scorerAsym_coeff, h1, h2, ite_false, mul_zero, add_zero,
        dvd_mul_right, ite_true, h3]
      congr 1
      rw [pow_mul, neg_pow, div_pow]
      field_simp
      rw [div_pow]; field_simp
  have h1 : ∑ n ∈ Finset.range (3 * M + 1), t ^ n * scorerAsym_coeff n =
      ∑ k ∈ Finset.range (M + 1), (-(t ^ 3 / 3)) ^ k / (k.factorial : ℂ) := by
    rw [Finset.sum_range_succ, h0, Finset.sum_range_succ]
    have h3 : (3 * M) / 3 = M := by omega
    simp only [scorerAsym_coeff, dvd_mul_right, ite_true, h3]
    congr 1
    rw [pow_mul, neg_pow, div_pow]
    field_simp
    rw [div_pow]; field_simp
  refine ⟨h0 M, h1, ?_⟩
  rw [Finset.sum_range_succ, h1]
  have h2 : ¬ 3 ∣ 3 * M + 1 := by omega
  simp [scorerAsym_coeff, h2]

/-- Taylor remainders of `t^m e^{-t³/3}` along a ray, as required by Watson's lemma. -/
theorem scorerAsym_sub_sum_isBigO (m : ℕ) (θ : ℝ) (N : ℕ) :
    (fun r : ℝ => ((r : ℂ) * exp (θ * I)) ^ m * cexp (-(((r : ℂ) * exp (θ * I)) ^ 3 / 3)) -
      ∑ n ∈ Finset.range N,
        (((r : ℂ) * exp (θ * I)) ^ ((n : ℂ) + ((m : ℂ) + 1) - 1)) • scorerAsym_coeff n)
      =O[𝓝[>] 0] fun r => r ^ ((N : ℝ) + ((m : ℂ) + 1).re - 1) := by
  obtain ⟨M, hM⟩ : ∃ M : ℕ, N ≤ 3 * M ∧
      ∀ t : ℂ, ∑ n ∈ Finset.range N, t ^ n * scorerAsym_coeff n =
        ∑ k ∈ Finset.range M, (-(t ^ 3 / 3)) ^ k / (k.factorial : ℂ) := by
    rcases (by omega : N % 3 = 0 ∨ N % 3 = 1 ∨ N % 3 = 2) with h | h | h
    · obtain ⟨q, rfl⟩ : ∃ q, N = 3 * q := ⟨N / 3, by omega⟩
      exact ⟨q, le_rfl, fun t => (scorerAsym_sum_coeff t q).1⟩
    · obtain ⟨q, rfl⟩ : ∃ q, N = 3 * q + 1 := ⟨N / 3, by omega⟩
      exact ⟨q + 1, by omega, fun t => (scorerAsym_sum_coeff t q).2.1⟩
    · obtain ⟨q, rfl⟩ : ∃ q, N = 3 * q + 2 := ⟨N / 3, by omega⟩
      exact ⟨q + 1, by omega, fun t => (scorerAsym_sum_coeff t q).2.2⟩
  refine IsBigO.of_bound 3 ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds (zero_lt_one' ℝ))]
    with r hr hr1
  have hr : (0 : ℝ) < r := hr
  have hr1 : r < 1 := hr1
  set t : ℂ := (r : ℂ) * exp (θ * I)
  have hnt : ‖t‖ = r := by
    simp only [t]; rw [norm_mul, norm_real, Real.norm_of_nonneg hr.le, norm_exp_ofReal_mul_I,
      mul_one]
  have hsum : ∑ n ∈ Finset.range N, (t ^ ((n : ℂ) + ((m : ℂ) + 1) - 1)) • scorerAsym_coeff n =
      t ^ m * ∑ n ∈ Finset.range N, t ^ n * scorerAsym_coeff n := by
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
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hr.le _),
    show (N : ℝ) + ((m : ℝ) + 1) - 1 =
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
theorem scorerAsym_laplace_expansion (m : ℕ) {α : ℝ} (hα0 : 0 ≤ α) (hα : α < 2 * π / 3) :
    HasAsymptoticExpansion (airySector α) (fun (n : ℕ) (w : ℂ) => w ^ (-((n : ℂ) + ((m : ℂ) + 1))))
      (fun n => Gamma ((n : ℂ) + ((m : ℂ) + 1)) • scorerAsym_coeff n) (scorerAsym_laplace m) := by
  have hπ := Real.pi_pos
  have hcov := le_sup_comap_rotate (α := α) (β := α / 4) (γ := 3 * α / 4)
    (by linarith) (by linarith) (by linarith) (by linarith)
  have hcos : 0 < Real.cos (3 * α / 4) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hrot : ∀ θ : ℝ, |θ| < π / 6 → HasAsymptoticExpansion
      (comap (fun w : ℂ => w * exp (θ * I)) (sectorAtTop (Real.cos (3 * α / 4))))
      (fun (n : ℕ) (w : ℂ) => w ^ (-((n : ℂ) + ((m : ℂ) + 1))))
      (fun n => Gamma ((n : ℂ) + ((m : ℂ) + 1)) • scorerAsym_coeff n) (scorerAsym_laplace m) := by
    intro θ hθ
    have hθ' : |θ| < π / 2 := by linarith
    have hμ : 0 < ((m : ℂ) + 1).re := by simp; positivity
    refine (hasAsymptoticExpansion_integral_cexp_smul_rotate_comap
      (F := fun t => t ^ m * cexp (-(t ^ 3 / 3))) (a := scorerAsym_coeff) (μ := (m : ℂ) + 1)
      (c := 0) hθ' hμ hcos (scorerAsym_integrableOn_rotate m 0 hθ)
      (scorerAsym_sub_sum_isBigO m θ)).congr' (Eventually.of_forall fun w => ?_)
    exact (scorerAsym_laplace_rotate m hθ w).symm
  have hb : |α / 4| < π / 6 := by rw [abs_of_nonneg (by linarith)]; linarith
  have h1 := hrot (-(α / 4)) (by rwa [abs_neg])
  have h2 := hrot (α / 4) hb
  exact (h1.sup h2).mono hcov

/-- A sum over `n < 3N` of a sequence vanishing at `n ≢ 0 (mod 3)` is the sum over `k < N` of
its values at `3k`. -/
theorem scorerAsym_sum_three {g : ℕ → ℂ} (h1 : ∀ k, g (3 * k + 1) = 0) (h2 : ∀ k, g (3 * k + 2) = 0)
    (N : ℕ) : ∑ n ∈ Finset.range (3 * N), g n = ∑ k ∈ Finset.range N, g (3 * k) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 3 * (N + 1) = 3 * N + 1 + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, Finset.sum_range_succ, h1, h2]
    ring

/-- The expansion of `L_m(-z)` in powers of `1/z`, truncated after `N` nonzero terms, for
`-z` in the sector `|arg(-z)| ≤ α < 2π/3`. -/
theorem scorerAsym_laplace_neg_isBigO (m : ℕ) {α : ℝ} (hα0 : 0 ≤ α) (hα : α < 2 * π / 3) (N : ℕ) :
    IsBigO (comap (fun z : ℂ => -z) (airySector α))
      (fun z => scorerAsym_laplace m (-z) - ∑ k ∈ Finset.range N,
        ((3 * k + m).factorial : ℂ) * ((-1 / 3 : ℂ) ^ k / (k.factorial : ℂ)) *
          ((-z) ^ (3 * k + m + 1))⁻¹)
      (fun z => ((z ^ (3 * N + m + 1))⁻¹)) := by
  have hE := (scorerAsym_laplace_expansion m hα0 hα (3 * N)).comp_tendsto
    (tendsto_comap : Tendsto (fun z : ℂ => -z) (comap (fun z : ℂ => -z) (airySector α))
      (airySector α))
  have hpow : ∀ (j : ℕ) (w : ℂ), w ^ (-((j : ℂ) + ((m : ℂ) + 1))) = (w ^ (j + m + 1))⁻¹ := by
    intro j w
    rw [show ((j : ℂ) + ((m : ℂ) + 1)) = ((j + m + 1 : ℕ) : ℂ) by push_cast; ring, cpow_neg,
      cpow_natCast]
  refine (hE.congr' (Eventually.of_forall fun z => ?_) EventuallyEq.rfl).trans ?_
  · simp only [Function.comp_apply]
    congr 1
    rw [scorerAsym_sum_three (g := fun n => (-z) ^ (-((n : ℂ) + ((m : ℂ) + 1))) •
      (Gamma ((n : ℂ) + ((m : ℂ) + 1)) • scorerAsym_coeff n))]
    · refine Finset.sum_congr rfl fun k _ => ?_
      have hd : 3 ∣ 3 * k := dvd_mul_right 3 k
      have hk : 3 * k / 3 = k := by omega
      simp only [scorerAsym_coeff, hd, ite_true, hk, smul_eq_mul, hpow]
      rw [show ((3 * k : ℕ) : ℂ) + ((m : ℂ) + 1) = ((3 * k + m : ℕ) : ℂ) + 1 by push_cast; ring,
        Gamma_nat_eq_factorial]
      ring
    · intro k
      have : ¬ 3 ∣ 3 * k + 1 := by omega
      simp [scorerAsym_coeff, this]
    · intro k
      have : ¬ 3 ∣ 3 * k + 2 := by omega
      simp [scorerAsym_coeff, this]
  · refine IsBigO.of_bound 1 (Eventually.of_forall fun z => ?_)
    simp only [Function.comp_apply]
    rw [hpow, one_mul, norm_inv, norm_inv, norm_pow, norm_pow, norm_neg]

/-- Eventually in the reflected sector `|arg(-z)| ≤ α`, `z ≠ 0`. -/
theorem scorerAsym_eventually_ne_zero (α : ℝ) :
    ∀ᶠ z in comap (fun z : ℂ => -z) (airySector α), z ≠ 0 := by
  have h : ∀ᶠ w in airySector α, w ≠ 0 ∧ |arg w| ≤ α := mem_inf_of_right (mem_principal_self _)
  exact (tendsto_comap.eventually h).mono fun z hz => neg_ne_zero.mp hz.1

/-- `(-1)^{3k+j} = (-1)^k (-1)^j`. -/
theorem scorerAsym_neg_one_pow (k j : ℕ) : (-1 : ℂ) ^ (3 * k + j) = (-1) ^ k * (-1) ^ j := by
  rw [pow_add, pow_mul]; norm_num

/-- `Hi(z) = -(πz)⁻¹ ∑_{k<N} (3k)!/(k!(3z³)^k) + O(z^{-3N-1})` for `|arg(-z)| ≤ α < 2π/3`. -/
theorem scorerAsym_scorerHi_isBigO {α : ℝ} (hα0 : 0 ≤ α) (hα : α < 2 * π / 3) (N : ℕ) :
    IsBigO (comap (fun z : ℂ => -z) (airySector α))
      (fun z : ℂ => scorerHi z - -1 / (π * z ^ 1) *
        ∑ k ∈ Finset.range N, (((3 * k + 0).factorial : ℂ) / k.factorial) / (3 * z ^ 3) ^ k)
      (fun z : ℂ => (z ^ (3 * N + 0 + 1))⁻¹) := by
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have h := (scorerAsym_laplace_neg_isBigO 0 hα0 hα N).const_mul_left (1 / π : ℂ)
  refine h.congr' ?_ EventuallyEq.rfl
  filter_upwards [scorerAsym_eventually_ne_zero α] with z hz
  rw [← scorerAsym_scorerHi_eq, mul_sub, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · field_simp
  · refine Finset.sum_congr rfl fun k _ => ?_
    simp only [add_zero, pow_one]
    rw [neg_pow, scorerAsym_neg_one_pow k 1, mul_pow, ← pow_mul, div_pow, pow_succ z]
    have hf : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    field_simp

/-- `Hi'(z) = (πz²)⁻¹ ∑_{k<N} (3k+1)!/(k!(3z³)^k) + O(z^{-3N-2})` for `|arg(-z)| ≤ α < 2π/3`. -/
theorem scorerAsym_scorerHiDeriv_isBigO {α : ℝ} (hα0 : 0 ≤ α) (hα : α < 2 * π / 3) (N : ℕ) :
    IsBigO (comap (fun z : ℂ => -z) (airySector α))
      (fun z : ℂ => scorerHiDeriv z - 1 / (π * z ^ 2) *
        ∑ k ∈ Finset.range N, (((3 * k + 1).factorial : ℂ) / k.factorial) / (3 * z ^ 3) ^ k)
      (fun z : ℂ => (z ^ (3 * N + 1 + 1))⁻¹) := by
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have h := (scorerAsym_laplace_neg_isBigO 1 hα0 hα N).const_mul_left (1 / π : ℂ)
  refine h.congr' ?_ EventuallyEq.rfl
  filter_upwards [scorerAsym_eventually_ne_zero α] with z hz
  rw [← scorerAsym_scorerHiDeriv_eq, mul_sub, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · field_simp
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [show 3 * k + 1 + 1 = 3 * k + 2 by ring, neg_pow, scorerAsym_neg_one_pow k 2, mul_pow,
      ← pow_mul, div_pow, pow_add z (3 * k) 2]
    have hf : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    field_simp

/-- Rotation by `e^{∓2πi/3}` maps the sector `|arg z| ≤ π/3 - δ` into the reflected sector
`|arg(-z)| ≤ 2π/3 - δ`. -/
theorem scorerAsym_tendsto_omega {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < π / 3) :
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
    have := airyRot_tendsto_rotate (α := π / 3 - δ) (β := 2 * π / 3 - δ) (c := π / 3)
      (by rw [abs_of_pos (by positivity)]; linarith) (by linarith)
    exact this.congr fun z => (e1 z).symm
  · refine tendsto_comap_iff.mpr ?_
    have := airyRot_tendsto_rotate (α := π / 3 - δ) (β := 2 * π / 3 - δ) (c := -(π / 3))
      (by rw [abs_neg, abs_of_pos (by positivity)]; linarith) (by linarith)
    exact this.congr fun z => (e2 z).symm

/-- The derivative of the rotation formula 9.12.12. -/
theorem scorerAsym_scorerGiDeriv_rotations (z : ℂ) :
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

/-- The cube roots of unity `e^{±2πi/3}` have norm `1`. -/
theorem scorerAsym_norm_omega : ‖exp (-2 * π * I / 3)‖ = 1 ∧ ‖exp (2 * π * I / 3)‖ = 1 := by
  constructor
  · rw [show (-2 * π * I / 3 : ℂ) = ((-2 * π / 3 : ℝ) : ℂ) * I by push_cast; ring,
      norm_exp_ofReal_mul_I]
  · rw [show (2 * π * I / 3 : ℂ) = ((2 * π / 3 : ℝ) : ℂ) * I by push_cast; ring,
      norm_exp_ofReal_mul_I]

/-- The cube roots of unity `e^{±2πi/3}` cube to `1`. -/
theorem scorerAsym_omega_cube : exp (-2 * π * I / 3) ^ 3 = 1 ∧ exp (2 * π * I / 3) ^ 3 = 1 := by
  constructor
  · rw [show (-2 * π * I / 3 : ℂ) = -(2 * π * I / 3) by ring]; exact omega_recip_cube
  · exact omega_cube

/-- Composite bound: `((z c)^n)⁻¹ = O((z^n)⁻¹)` when `‖c‖ = 1`. -/
theorem scorerAsym_isBigO_recip_pow_mul {l : Filter ℂ} {c : ℂ} (hc : ‖c‖ = 1) (n : ℕ) :
    (fun z : ℂ => ((z * c) ^ n)⁻¹) =O[l] (fun z : ℂ => (z ^ n)⁻¹) :=
  IsBigO.of_bound 1 (Eventually.of_forall fun z => by
    rw [one_mul, norm_inv, norm_inv, norm_pow, norm_pow, norm_mul, hc, mul_one])

/-- The coefficients of 9.12.12: `e^{πi/3}/2 = -e^{-2πi/3}/2` and `e^{-πi/3}/2 = -e^{2πi/3}/2`. -/
theorem scorerAsym_rot_coeffs :
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
  obtain ⟨T1, T2⟩ := scorerAsym_tendsto_omega hδ hδ'
  obtain ⟨n1, n2⟩ := scorerAsym_norm_omega
  obtain ⟨c1, c2⟩ := scorerAsym_omega_cube
  obtain ⟨ha, hb⟩ := scorerAsym_rot_coeffs
  have H := scorerAsym_scorerHi_isBigO (α := 2 * π / 3 - δ) (by linarith) (by linarith) N
  have h1 := ((H.comp_tendsto T1).trans (scorerAsym_isBigO_recip_pow_mul n1 _)).const_mul_left
    (exp (π * I / 3) / 2)
  have h2 := ((H.comp_tendsto T2).trans (scorerAsym_isBigO_recip_pow_mul n2 _)).const_mul_left
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
  obtain ⟨T1, T2⟩ := scorerAsym_tendsto_omega hδ hδ'
  obtain ⟨n1, n2⟩ := scorerAsym_norm_omega
  obtain ⟨c1, c2⟩ := scorerAsym_omega_cube
  obtain ⟨ha, hb⟩ := scorerAsym_rot_coeffs
  have H := scorerAsym_scorerHiDeriv_isBigO (α := 2 * π / 3 - δ) (by linarith) (by linarith) N
  have h1 := ((H.comp_tendsto T1).trans (scorerAsym_isBigO_recip_pow_mul n1 _)).const_mul_left
    (exp (π * I / 3) / 2 * exp (-2 * π * I / 3))
  have h2 := ((H.comp_tendsto T2).trans (scorerAsym_isBigO_recip_pow_mul n2 _)).const_mul_left
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
    rw [hS _ c1, hS _ c2, scorerAsym_scorerGiDeriv_rotations, ha, hb]
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
  refine (scorerAsym_scorerHi_isBigO (α := 2 * π / 3 - δ) (by linarith) (by linarith) N).congr'
    EventuallyEq.rfl (Eventually.of_forall fun z => ?_)
  simp only
  rw [show (3 * (N : ℂ) + 1) = ((3 * N + 0 + 1 : ℕ) : ℂ) by push_cast; ring, cpow_neg,
    cpow_natCast]

/-- `Hi'(z) ~ (πz²)⁻¹ ∑ (3k+1)!/(k! (3z³)^k)` as `z → ∞` in `|arg(-z)| ≤ 2π/3 - δ`, with
remainder `O(z^{-3N-2})` (DLMF 9.12.28). -/
@[dlmf 9.12.E28]
theorem scorerHiDeriv_asymptotic {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 2 * π / 3) (N : ℕ) :
    IsBigO (comap (fun z : ℂ => -z) (airySector (2 * π / 3 - δ)))
      (fun z : ℂ => scorerHiDeriv z - 1 / (π * z ^ 2) *
        ∑ k ∈ Finset.range N, (((3 * k + 1).factorial : ℂ) / k.factorial) / (3 * z ^ 3) ^ k)
      (fun z : ℂ => z ^ (-(3 * (N : ℂ) + 2))) := by
  refine (scorerAsym_scorerHiDeriv_isBigO (α := 2 * π / 3 - δ) (by linarith) (by linarith)
    N).congr' EventuallyEq.rfl (Eventually.of_forall fun z => ?_)
  simp only
  rw [show (3 * (N : ℂ) + 2) = ((3 * N + 1 + 1 : ℕ) : ℂ) by push_cast; ring, cpow_neg,
    cpow_natCast]

/-- All complex zeros are simple, DLMF §9.12(ix). -/
theorem scorerGi_simple_zeros {z : ℂ} (hz : scorerGi z = 0) :
    deriv scorerGi z ≠ 0 := by
  sorry

/-- All complex zeros are simple, DLMF §9.12(ix). -/
theorem scorerHi_simple_zeros {z : ℂ} (hz : scorerHi z = 0) :
    deriv scorerHi z ≠ 0 := by
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
def scorerZ_gi (x : ℝ) : ℝ := (scorerGi x).re
/-- `Gi'` on the real axis. -/
def scorerZ_gi' (x : ℝ) : ℝ := (scorerGiDeriv x).re
/-- `Hi` on the real axis, as a real Laplace integral. -/
def scorerZ_hi (x : ℝ) : ℝ := (∫ t in Ioi (0 : ℝ), Real.exp (-(t ^ 3 / 3) + x * t)) / π

/-- `tᵐ e^{-t³/3 + xt}` is integrable on `(0, ∞)` for real `x`. -/
theorem scorerZ_integrable (m : ℕ) (x : ℝ) :
    IntegrableOn (fun t : ℝ => t ^ m * Real.exp (-(t ^ 3 / 3) + x * t)) (Ioi 0) := by
  have := (integrableOn_pow_mul_exp_cubic m x).re
  refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
  beta_reduce
  rw [RCLike.re_to_complex, show (-(t : ℂ) ^ 3 / 3 + (x : ℂ) * t) =
      ((-(t ^ 3 / 3) + x * t : ℝ) : ℂ) by push_cast; ring,
    ← ofReal_exp, ← ofReal_pow, ← ofReal_mul, ofReal_re]

/-- `Hi(x)` is the real number `scorerZ_hi x` on the real axis. -/
theorem scorerZ_hi_eq (x : ℝ) : scorerHi x = (scorerZ_hi x : ℂ) := by
  rw [(scorerHi_exp_integral x).2]
  have h := integral_pow_mul_exp_cubic_ofReal 0 x
  simp only [pow_zero, one_mul] at h
  rw [h, scorerZ_hi]; push_cast; rfl

/-- On the real axis, `Hi'(x) = π⁻¹ ∫₀^∞ t e^{-t³/3 + xt} dt`, a real number. -/
theorem scorerZ_hiDeriv_eq (x : ℝ) : scorerHiDeriv x =
    (((∫ t in Ioi (0 : ℝ), t ^ 1 * Real.exp (-(t ^ 3 / 3) + x * t)) / π : ℝ) : ℂ) := by
  rw [scorerHiDeriv_exp_integral]
  have h := integral_pow_mul_exp_cubic_ofReal 1 x
  simp only [pow_one] at h ⊢
  rw [h]; push_cast; rfl

/-- `Gi(x)` is the real number `scorerZ_gi x` on the real axis. -/
theorem scorerZ_gi_ofReal (x : ℝ) : scorerGi x = (scorerZ_gi x : ℂ) := by
  have h : scorerGi x = ((airyBiReal x - scorerZ_hi x : ℝ) : ℂ) := by
    rw [scorerGi, airyBi_ofReal_eq, scorerZ_hi_eq]; push_cast; ring
  rw [scorerZ_gi, h, ofReal_re]

/-- On the real axis, `Gi = Bi - Hi`. -/
theorem scorerZ_gi_eq (x : ℝ) : scorerZ_gi x = airyBiReal x - scorerZ_hi x := by
  rw [scorerZ_gi, scorerGi, sub_re, scorerZ_hi_eq, ofReal_re]; rfl

/-- `Gi'(x)` is the real number `scorerZ_gi' x` on the real axis. -/
theorem scorerZ_gi'_ofReal (x : ℝ) : scorerGiDeriv x = (scorerZ_gi' x : ℂ) := by
  have h : ∃ r : ℝ, scorerGiDeriv x = (r : ℂ) := by
    rw [scorerGiDeriv_eq, airyBiDeriv_ofReal_eq, scorerZ_hiDeriv_eq]
    exact ⟨airyBiDerivReal x - (∫ t in Ioi (0 : ℝ), t ^ 1 * Real.exp (-(t ^ 3 / 3) + x * t)) / π,
      by push_cast; ring⟩
  obtain ⟨r, hr⟩ := h
  rw [scorerZ_gi', hr, ofReal_re]

/-- The real function `Gi` has derivative `Gi'`. -/
theorem scorerZ_hasDerivAt_gi (x : ℝ) : HasDerivAt scorerZ_gi (scorerZ_gi' x) x :=
  ((isAiryInhomSol_scorerGi x).1).real_of_complex

/-- The real function `Gi'` has derivative `x Gi(x) - 1/π` (the inhomogeneous Airy equation). -/
theorem scorerZ_hasDerivAt_gi' (x : ℝ) :
    HasDerivAt scorerZ_gi' (x * scorerZ_gi x - 1 / π) x := by
  have h : HasDerivAt scorerZ_gi' _ x := ((isAiryInhomSol_scorerGi x).2).real_of_complex
  refine h.congr_deriv ?_
  rw [scorerZ_gi_ofReal]
  simp only [add_re, re_ofReal_mul, neg_re, div_ofReal_re, one_re]
  rw [ofReal_re]; ring

/-- The derivative of `x Gi(x) - 1/π` is `Gi(x) + x Gi'(x)`. -/
theorem scorerZ_hasDerivAt_gi'' (x : ℝ) :
    HasDerivAt (fun t => t * scorerZ_gi t - 1 / π) (scorerZ_gi x + x * scorerZ_gi' x) x := by
  have := ((hasDerivAt_id x).mul (scorerZ_hasDerivAt_gi x)).sub_const (1 / π)
  convert this using 1 <;> simp

/-- The real function `Gi` is continuous. -/
theorem scorerZ_continuous_gi : Continuous scorerZ_gi :=
  continuous_iff_continuousAt.mpr fun x => (scorerZ_hasDerivAt_gi x).continuousAt

/-- The real function `Gi'` is continuous. -/
theorem scorerZ_continuous_gi' : Continuous scorerZ_gi' :=
  continuous_iff_continuousAt.mpr fun x => (scorerZ_hasDerivAt_gi' x).continuousAt

/-- `Gi(0) > 0`. -/
theorem scorerZ_gi_zero_pos : 0 < scorerZ_gi 0 := by
  rw [scorerZ_gi, ofReal_zero, scorer_zero.2.1, div_ofNat_re]
  exact div_pos (airyBiReal_pos le_rfl) (by norm_num)

/-- `Gi'(0) > 0`. -/
theorem scorerZ_gi'_zero_pos : 0 < scorerZ_gi' 0 := by
  rw [scorerZ_gi', ofReal_zero, scorerDeriv_zero.2.1, div_ofNat_re]
  exact div_pos airyBiDerivReal_zero_pos (by norm_num)

/-- Real form of a sector bound: `‖F x‖ ≤ C x^{-p}` eventually along the positive axis. -/
theorem scorerZ_real_bound {F : ℂ → ℂ} {p : ℂ}
    (h : IsBigO (comap (fun z : ℂ => z) (airySector (π / 3 - π / 6))) F (fun z => z ^ p)) :
    ∃ C, ∀ᶠ x : ℝ in atTop, ‖F x‖ ≤ C * x ^ p.re := by
  rw [comap_id'] at h
  obtain ⟨C, hC⟩ := (h.comp_tendsto (airyInt_tendsto_ofReal_sector (by
    linarith [Real.pi_pos]))).bound
  refine ⟨C, ?_⟩
  filter_upwards [hC, eventually_gt_atTop 0] with x hx hx0
  simpa [Function.comp, Complex.norm_cpow_eq_rpow_re_of_pos hx0] using hx

/-- `Gi(x) > 0` for all sufficiently large real `x`. -/
theorem scorerZ_gi_eventually_pos : ∀ᶠ x in atTop, 0 < scorerZ_gi x := by
  have hπ := Real.pi_pos
  obtain ⟨C, hC⟩ := scorerZ_real_bound (scorerGi_asymptotic (δ := π / 6)
    (by positivity) (by linarith) 1)
  filter_upwards [hC, eventually_gt_atTop (max 1 (C * π))] with x hx hxM
  have hx1 : 1 < x := (le_max_left _ _).trans_lt hxM
  have hxC : C * π < x := (le_max_right _ _).trans_lt hxM
  have hx0 : 0 < x := by linarith
  simp only [Finset.sum_range_one, Nat.factorial_zero, Nat.cast_one, div_one, pow_zero,
    mul_one, mul_zero, zero_add, pow_one] at hx
  rw [scorerZ_gi_ofReal, show (1 : ℂ) / (π * (x : ℂ)) = ((1 / (π * x) : ℝ) : ℂ) by push_cast; ring,
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
theorem scorerZ_gi'_eventually_neg : ∀ᶠ x in atTop, scorerZ_gi' x < 0 := by
  have hπ := Real.pi_pos
  obtain ⟨C, hC⟩ := scorerZ_real_bound (scorerGiDeriv_asymptotic (δ := π / 6)
    (by positivity) (by linarith) 1)
  filter_upwards [hC, eventually_gt_atTop (max 1 (C * π))] with x hx hxM
  have hx1 : 1 < x := (le_max_left _ _).trans_lt hxM
  have hxC : C * π < x := (le_max_right _ _).trans_lt hxM
  have hx0 : 0 < x := by linarith
  simp only [Finset.sum_range_one, Nat.factorial_zero, Nat.cast_one, div_one, pow_zero,
    mul_one, mul_zero, zero_add, Nat.factorial_one] at hx
  rw [scorerZ_gi'_ofReal, show (-1 : ℂ) / (π * (x : ℂ) ^ 2) = ((-1 / (π * x ^ 2) : ℝ) : ℂ) by
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
theorem scorerZ_gi_pos {x : ℝ} (hx : 0 ≤ x) : 0 < scorerZ_gi x := by
  obtain ⟨X, hX, hXx⟩ := (scorerZ_gi_eventually_pos.and (eventually_gt_atTop x)).exists
  have hπ := Real.pi_pos
  have := ODE.sturmCount_neg_of_maxPrinciple (g := fun t => -scorerZ_gi t)
    (g' := fun t => -scorerZ_gi' t) (g'' := fun t => -(t * scorerZ_gi t - 1 / π)) (a := 0) (b := X)
    scorerZ_continuous_gi.neg.continuousOn (fun t _ => (scorerZ_hasDerivAt_gi t).neg)
    (fun t _ => (scorerZ_hasDerivAt_gi' t).neg) (by simpa using scorerZ_gi_zero_pos)
    (by simpa using hX) (fun t ht h0 _ => by
      have : t * scorerZ_gi t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht.1.le (by linarith)
      have : 0 < 1 / π := by positivity
      linarith) x ⟨hx, hXx.le⟩
  linarith

/-- `Gi'` has at most one zero on `[0, ∞)`. -/
theorem scorerZ_gi'_zero_unique {y₁ y₂ : ℝ} (h₁ : 0 ≤ y₁) (hlt : y₁ < y₂) (e₁ : scorerZ_gi' y₁ = 0)
    (e₂ : scorerZ_gi' y₂ = 0) : False := by
  obtain ⟨X, hX, hXx⟩ := (scorerZ_gi'_eventually_neg.and (eventually_gt_atTop y₂)).exists
  have hle := ODE.sturmCount_nonpos_of_maxPrinciple (g := scorerZ_gi')
    (g' := fun t => t * scorerZ_gi t - 1 / π) (g'' := fun t => scorerZ_gi t + t * scorerZ_gi' t)
    (a := y₁) (b := X) scorerZ_continuous_gi'.continuousOn
    (fun t _ => scorerZ_hasDerivAt_gi' t) (fun t _ => scorerZ_hasDerivAt_gi'' t) e₁.le hX.le
    (fun t ht hpos _ => by
      have h0 : 0 < t := lt_of_le_of_lt h₁ ht.1
      have := scorerZ_gi_pos h0.le
      positivity)
  have hloc : IsLocalMax scorerZ_gi' y₂ := by
    filter_upwards [Icc_mem_nhds hlt hXx] with t ht
    rw [e₂]; exact hle t ht
  have hd0 := hloc.hasDerivAt_eq_zero (scorerZ_hasDerivAt_gi' y₂)
  refine ODE.sturmCount_not_isLocalMax (Eventually.of_forall fun t => scorerZ_hasDerivAt_gi' t)
    (scorerZ_hasDerivAt_gi'' y₂) hd0 ?_ hloc
  rw [e₂, mul_zero, add_zero]
  exact scorerZ_gi_pos (h₁.trans hlt.le)

/-- `0 < Hi(x) ≤ 1/(π|x|)` for `x < 0`. -/
theorem scorerZ_hi_le {x : ℝ} (hx : x < 0) : scorerZ_hi x ≤ 1 / (π * (-x)) := by
  have hπ := Real.pi_pos
  have hI : ∫ t in Ioi (0 : ℝ), Real.exp (-(t ^ 3 / 3) + x * t) ≤ 1 / (-x) := by
    calc ∫ t in Ioi (0 : ℝ), Real.exp (-(t ^ 3 / 3) + x * t)
        ≤ ∫ t in Ioi (0 : ℝ), Real.exp (x * t) := by
          refine setIntegral_mono_on (by simpa using scorerZ_integrable 0 x)
            (integrableOn_exp_mul_Ioi hx 0) measurableSet_Ioi fun t ht => ?_
          have ht : (0 : ℝ) < t := ht
          exact Real.exp_le_exp.mpr (by nlinarith [pow_pos ht 3])
      _ = 1 / (-x) := by rw [integral_exp_mul_Ioi hx 0]; simp; field_simp
  rw [scorerZ_hi, mul_comm, ← div_div]
  exact div_le_div_of_nonneg_right hI hπ.le

/-- The Airy modulus beats the Hi bound: `1/(π|x|) < M(x)` for `x ≤ -1`. -/
theorem scorerZ_modulus_gt {x : ℝ} (hx : x ≤ -1) : 1 / (π * (-x)) < airyModulus x := by
  have hπ := Real.pi_pos
  set s := -x with hs
  have hs1 : 1 ≤ s := by linarith
  have hs0 : 0 < s := by linarith
  obtain ⟨hb, -⟩ := airyMod_modulus_bounds hs0
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
theorem scorerZ_gi_signs (M : ℝ) (σ : ℝ) (hσ : σ = 0 ∨ σ = π) :
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
theorem scorerZ_gi_frequently (M : ℝ) :
    (∃ x < M, 0 < scorerZ_gi x) ∧ ∃ x < M, scorerZ_gi x < 0 := by
  have hπ := Real.pi_pos
  constructor
  · obtain ⟨x, hxM, hx1, hc⟩ := scorerZ_gi_signs M 0 (Or.inl rfl)
    refine ⟨x, hxM, ?_⟩
    rw [scorerZ_gi_eq, airyBiReal_eq_modulus_cos, hc, Real.cos_zero, mul_one]
    linarith [scorerZ_hi_le (show x < 0 by linarith), scorerZ_modulus_gt hx1]
  · obtain ⟨x, hxM, hx1, hc⟩ := scorerZ_gi_signs M π (Or.inr rfl)
    refine ⟨x, hxM, ?_⟩
    rw [scorerZ_gi_eq, airyBiReal_eq_modulus_cos, hc, Real.cos_pi, mul_neg_one]
    have : 0 < scorerZ_hi x := by
      rw [scorerZ_hi]
      exact div_pos (by simpa using integral_pow_mul_exp_cubic_pos 0 x) hπ
    linarith [airyModulus_pos x]

/-- The real function `Gi` has infinitely many negative zeros. -/
theorem scorerZ_gi_zeros_infinite : {x : ℝ | x < 0 ∧ scorerZ_gi x = 0}.Infinite :=
  ODE.sturmCount_infinite_zeros_atBot scorerZ_continuous_gi.continuousOn
    (fun M => (scorerZ_gi_frequently M).1) (fun M => (scorerZ_gi_frequently M).2)

/-- Gi has no nonnegative real zeros, DLMF §9.12(ix). -/
theorem scorerGi_nonneg_ne_zero {x : ℝ} (hx : 0 ≤ x) :
    scorerGi x ≠ 0 := by
  rw [scorerZ_gi_ofReal, ofReal_ne_zero]
  exact (scorerZ_gi_pos hx).ne'

/-- Gi' has exactly one nonnegative real zero, DLMF §9.12(ix). -/
theorem scorerGiDeriv_unique_nonneg_zero  :
    ∃! x : ℝ, 0 ≤ x ∧ scorerGiDeriv x = 0 := by
  obtain ⟨X, hX, hX0⟩ := (scorerZ_gi'_eventually_neg.and (eventually_gt_atTop 0)).exists
  obtain ⟨x, hx, hx0⟩ := intermediate_value_Icc' hX0.le scorerZ_continuous_gi'.continuousOn
    ⟨hX.le, scorerZ_gi'_zero_pos.le⟩
  refine ⟨x, ⟨hx.1, by rw [scorerZ_gi'_ofReal, hx0, ofReal_zero]⟩, fun y ⟨hy, hy0⟩ => ?_⟩
  rw [scorerZ_gi'_ofReal, ofReal_eq_zero] at hy0
  rcases lt_trichotomy y x with h | h | h
  · exact (scorerZ_gi'_zero_unique hy h hy0 hx0).elim
  · exact h
  · exact (scorerZ_gi'_zero_unique hx.1 h hx0 hy0).elim

/-- Infinitely many negative real zeros, DLMF §9.12(ix). -/
theorem scorerGi_infinite_negative_zeros  :
    Set.Infinite {x : ℝ | x < 0 ∧ scorerGi x = 0} := by
  convert scorerZ_gi_zeros_infinite using 3 with x
  rw [scorerZ_gi_ofReal, ofReal_eq_zero]

/-- Infinitely many negative real zeros, DLMF §9.12(ix). -/
theorem scorerGiDeriv_infinite_negative_zeros  :
    Set.Infinite {x : ℝ | x < 0 ∧ scorerGiDeriv x = 0} := by
  have h := ODE.sturmCount_infinite_deriv_zeros (s := Iio 0) ordConnected_Iio
    (fun x _ => scorerZ_hasDerivAt_gi x) scorerZ_gi_zeros_infinite
  convert h using 3 with x
  rw [scorerZ_gi'_ofReal, ofReal_eq_zero]; rfl

/-- Negative zeros of Gi and Gi' interlace, DLMF §9.12(ix). -/
theorem scorerGi_zeros_interlace {a b : ℝ} (hab : a < b) (hb : b < 0)
    (ha0 : scorerGi a = 0) (hb0 : scorerGi b = 0)
    (hgap : ∀ x ∈ Ioo a b, scorerGi x ≠ 0) :
    ∃! x : ℝ, x ∈ Ioo a b ∧ scorerGiDeriv x = 0 := by
  sorry

/-- The reverse interlacing of the two negative real Scorer zero families. -/
theorem scorerGiDeriv_zeros_interlace {a b : ℝ} (hab : a < b) (hb : b < 0)
    (ha0 : scorerGiDeriv a = 0) (hb0 : scorerGiDeriv b = 0)
    (hgap : ∀ x ∈ Ioo a b, scorerGiDeriv x ≠ 0) :
    ∃! x : ℝ, x ∈ Ioo a b ∧ scorerGi x = 0 := by
  sorry

/-- Convergence of the symmetric principal value in DLMF 9.12.23. -/
@[dlmf 9.12.E23]
theorem scorerGi_principalValue_converges {x : ℝ} (hx : 0 < x) :
    let f := fun t : ℝ => DLMF.Bessel.besselK (1 / 3) t /
      ((airyZeta x : ℂ) ^ 2 - (t : ℂ) ^ 2)
    HasPrincipalValueIoi f (airyZeta x) (principalValueIoi f (airyZeta x)) := by
  sorry

end DLMF.Airy

end
