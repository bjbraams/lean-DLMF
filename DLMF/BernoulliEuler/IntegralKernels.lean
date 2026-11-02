/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.BernoulliEuler.Series
public import DLMFMathlib.Analysis.Complex.ParametricHolomorphy

/-!
# Kernel integrals for the Bernoulli and Euler polynomials

This file provides the analytic tools for the integral representations DLMF 24.7.7–24.7.10 of
`Bₙ(x)` and `Eₙ(x)` for `0 < Re x < 1`. The kernels `(cos 2πx - e^{-2πt})/(cosh 2πt - cos 2πx)`,
`sin 2πx/(cosh 2πt - cos 2πx)`, `sin πx cosh πt/(cosh 2πt - cos 2πx)` and
`cos πx sinh πt/(cosh 2πt - cos 2πx)` are combinations of geometric series in
`e^{-2πt ± 2πix}`, respectively in the odd powers of `e^{-πt ± πix}`.

## Main results

* `tendsto_sum_integral_pow_mul_geometric`: the moments `∫₀^∞ tᵐ p/(1 - r) dt` of a geometric
  kernel, `p = e^{-αt + iθ}`, `r = e^{-βt + iη}`, `cos η < 1`, as limits of the partial sums of
  the termwise moments. The remainder `p rᴺ/(1 - r)` is estimated directly, so no absolute
  convergence of the resulting series is needed (it fails for `m = 0`).
* `geometric_kernel_add`, `geometric_kernel_sub`, `geometric_odd_kernel_add`,
  `geometric_odd_kernel_sub`: the kernels as sums of two geometric kernels.
* `tendsto_sum_cos_integral_bernoulliKernel`, `tendsto_sum_sin_integral_bernoulliKernel`,
  `tendsto_sum_sin_integral_eulerKernel`, `tendsto_sum_cos_integral_eulerKernel`: the moments of
  the four kernels at real `x ∈ (0, 1)` as limits of trigonometric sums.
* `differentiableOn_integral_div_cosh_sub_cos`: holomorphy of the kernel integrals in the strip
  `0 < Re x < 1`, from the lower bound `|cosh 2πt - cos 2πx| ≥ sin²(π Re x) e^{2πt}/2`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Complex
open scoped Nat Real

namespace DLMF.BernoulliEuler

/-- `∫₀^∞ tᵐ e^{-λt} dt = m!/λ^{m+1}`. -/
private lemma integral_pow_mul_exp_neg_mul (m : ℕ) {l : ℝ} (hl : 0 < l) :
    ∫ t in Ioi (0 : ℝ), t ^ m * Real.exp (-(l * t)) = m ! / l ^ (m + 1) := by
  have key := Real.integral_rpow_mul_exp_neg_mul_Ioi (by positivity : (0 : ℝ) < m + 1) hl
  have e : ∀ t ∈ Ioi (0 : ℝ), t ^ ((m : ℝ) + 1 - 1) * Real.exp (-(l * t)) =
      t ^ m * Real.exp (-(l * t)) := fun t _ => by
    rw [add_sub_cancel_right, Real.rpow_natCast]
  rw [setIntegral_congr_fun measurableSet_Ioi e] at key
  rw [key, Real.Gamma_nat_eq_factorial, Real.div_rpow zero_le_one hl.le, Real.one_rpow,
    show ((m : ℝ) + 1) = ((m + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  ring

private lemma integrableOn_pow_mul_exp_neg_mul (m : ℕ) {l : ℝ} (hl : 0 < l) :
    IntegrableOn (fun t : ℝ => t ^ m * Real.exp (-(l * t))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := m) (p := 1) (b := l)
    (by have := (Nat.cast_nonneg m : (0:ℝ) ≤ m); linarith) one_pos hl
  refine h.congr_fun (fun t ht => ?_) measurableSet_Ioi
  simp [Real.rpow_natCast, neg_mul]

/-- A function continuous on `(0, ∞)` and dominated by `C tᵐ e^{-λt}` is integrable there, with
integral of norm at most `C m!/λ^{m+1}`. -/
private lemma integrableOn_and_norm_integral_le {F : ℝ → ℂ} (m : ℕ) {l C : ℝ} (hl : 0 < l)
    (hF : ContinuousOn F (Ioi 0))
    (hb : ∀ t ∈ Ioi (0 : ℝ), ‖F t‖ ≤ C * (t ^ m * Real.exp (-(l * t)))) :
    IntegrableOn F (Ioi 0) ∧ ‖∫ t in Ioi (0 : ℝ), F t‖ ≤ C * (m ! / l ^ (m + 1)) := by
  have hg := (integrableOn_pow_mul_exp_neg_mul m hl).const_mul C
  have hI : IntegrableOn F (Ioi 0) :=
    hg.mono' (hF.aestronglyMeasurable measurableSet_Ioi)
      ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ hb))
  refine ⟨hI, ?_⟩
  rw [← integral_pow_mul_exp_neg_mul m hl, ← integral_const_mul]
  exact norm_integral_le_of_norm_le hg ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ hb))


/-- `cexp (-(a t) + i b)`, the geometric kernel. -/
private lemma norm_cexp_kernel (a b t : ℝ) : ‖cexp (((-(a * t) : ℝ) : ℂ) + b * I)‖ =
    Real.exp (-(a * t)) := by
  rw [Complex.norm_exp]; simp

/-- Lower bound for `Re (1 - e^{-bt + iη})`. -/
private lemma min_le_re_one_sub_kernel {b η t : ℝ} (hb : 0 ≤ b * t) :
    min 1 (1 - Real.cos η) ≤ (1 - cexp (((-(b * t) : ℝ) : ℂ) + η * I)).re := by
  rw [Complex.sub_re, Complex.one_re, Complex.exp_re]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.add_im, Complex.mul_im,
    zero_add]
  have he : Real.exp (-(b * t)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have he0 := Real.exp_pos (-(b * t))
  rcases le_or_gt (Real.cos η) 0 with h | h
  · exact (min_le_left _ _).trans (by nlinarith)
  · exact (min_le_right _ _).trans (by nlinarith)

private lemma norm_one_sub_kernel_ge {b η t : ℝ} (hb : 0 ≤ b * t) :
    min 1 (1 - Real.cos η) ≤ ‖1 - cexp (((-(b * t) : ℝ) : ℂ) + η * I)‖ :=
  (min_le_re_one_sub_kernel hb).trans (Complex.re_le_norm _)

/-- Moments of a single geometric term. -/
private lemma integral_pow_mul_kernel (m : ℕ) {a : ℝ} (ha : 0 < a) (b : ℝ) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ m * cexp (((-(a * t) : ℝ) : ℂ) + b * I) =
      cexp (b * I) * ((m ! / a ^ (m + 1) : ℝ) : ℂ) := by
  have e : ∀ t : ℝ, (t : ℂ) ^ m * cexp (((-(a * t) : ℝ) : ℂ) + b * I) =
      cexp (b * I) * ((t ^ m * Real.exp (-(a * t)) : ℝ) : ℂ) := fun t => by
    rw [Complex.exp_add]; push_cast; ring
  simp_rw [e]
  rw [integral_const_mul, integral_complex_ofReal, integral_pow_mul_exp_neg_mul m ha]

private lemma integrableOn_pow_mul_kernel (m : ℕ) {a : ℝ} (ha : 0 < a) (b : ℝ) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ m * cexp (((-(a * t) : ℝ) : ℂ) + b * I)) (Ioi 0) := by
  refine (integrableOn_and_norm_integral_le (C := 1) m ha (Continuous.continuousOn
    (by fun_prop)) fun t ht => ?_).1
  rw [norm_mul, norm_cexp_kernel, norm_pow, Complex.norm_real, Real.norm_of_nonneg
    (le_of_lt ht), one_mul]

/-- **Moments of a geometric kernel.** For `α, β > 0` and `cos η < 1`, the moments of
`p/(1 - r)` with `p = e^{-αt + iθ}`, `r = e^{-βt + iη}` are the sums of the moments of the
geometric terms `p rᵏ`, as a limit of partial sums. -/
theorem tendsto_sum_integral_pow_mul_geometric (m : ℕ) {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (θ : ℝ) {η : ℝ} (hη : Real.cos η < 1) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ m * (cexp (((-(α * t) : ℝ) : ℂ) + θ * I) /
        (1 - cexp (((-(β * t) : ℝ) : ℂ) + η * I)))) (Ioi 0) ∧
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N,
        cexp ((θ + k * η : ℝ) * I) * ((m ! / (α + k * β) ^ (m + 1) : ℝ) : ℂ)) atTop
      (𝓝 (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ m * (cexp (((-(α * t) : ℝ) : ℂ) + θ * I) /
        (1 - cexp (((-(β * t) : ℝ) : ℂ) + η * I))))) := by
  set c := min 1 (1 - Real.cos η)
  have hc : 0 < c := lt_min one_pos (by linarith)
  set P : ℝ → ℂ := fun t => cexp (((-(α * t) : ℝ) : ℂ) + θ * I)
  set R : ℝ → ℂ := fun t => cexp (((-(β * t) : ℝ) : ℂ) + η * I)
  have hR : ∀ t, 0 ≤ t → c ≤ ‖1 - R t‖ := fun t ht =>
    norm_one_sub_kernel_ge (mul_nonneg hβ.le ht)
  have hR0 : ∀ t, 0 ≤ t → 1 - R t ≠ 0 := fun t ht h => by
    have := hR t ht; rw [h, norm_zero] at this; linarith
  have hPR : ∀ (k : ℕ) (t : ℝ), P t * R t ^ k =
      cexp (((-((α + k * β) * t) : ℝ) : ℂ) + ((θ + k * η : ℝ) : ℂ) * I) := fun k t => by
    simp only [P, R, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1; push_cast; ring
  have hαk : ∀ k : ℕ, 0 < α + k * β := fun k => by positivity
  have hcont : ∀ N : ℕ, ContinuousOn (fun t : ℝ => (t : ℂ) ^ m * (P t * R t ^ N / (1 - R t)))
      (Ioi 0) := fun N => by
    refine ContinuousOn.mul (by fun_prop) (ContinuousOn.div (by fun_prop) (by fun_prop)
      fun t ht => hR0 t (le_of_lt ht))
  have hbound : ∀ N : ℕ, ∀ t ∈ Ioi (0 : ℝ), ‖(t : ℂ) ^ m * (P t * R t ^ N / (1 - R t))‖ ≤
      c⁻¹ * (t ^ m * Real.exp (-((α + N * β) * t))) := fun N t ht => by
    have ht0 : 0 ≤ t := le_of_lt ht
    rw [hPR, norm_mul, norm_div, norm_cexp_kernel, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg ht0]
    have h1 := hR t ht0
    have h2 : 0 ≤ t ^ m * Real.exp (-((α + N * β) * t)) := by positivity
    calc t ^ m * (Real.exp (-((α + N * β) * t)) / ‖1 - R t‖)
        = (t ^ m * Real.exp (-((α + N * β) * t))) / ‖1 - R t‖ := by ring
      _ ≤ (t ^ m * Real.exp (-((α + N * β) * t))) / c := div_le_div_of_nonneg_left h2 hc h1
      _ = _ := by ring
  have hrem := fun N => integrableOn_and_norm_integral_le m (hαk N) (hcont N) (hbound N)
  -- the identity `∫ tᵐ p/(1-r) - ∑_{k<N} ∫ tᵐ p rᵏ = ∫ tᵐ p rᴺ/(1-r)`
  have hsplit : ∀ N : ℕ, ∀ t ∈ Ioi (0 : ℝ), (t : ℂ) ^ m * (P t / (1 - R t)) =
      ∑ k ∈ Finset.range N, (t : ℂ) ^ m * (P t * R t ^ k) +
        (t : ℂ) ^ m * (P t * R t ^ N / (1 - R t)) := fun N t ht => by
    have h0 := hR0 t (le_of_lt ht)
    have h1 : R t ≠ 1 := fun h => h0 (by rw [h]; ring)
    have h2 : R t - 1 ≠ 0 := sub_ne_zero.mpr h1
    rw [← Finset.mul_sum, ← mul_add, ← Finset.mul_sum, geom_sum_eq h1]
    field_simp; ring
  have hInt : ∀ N : ℕ, ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ m * (P t / (1 - R t)) =
      ∑ k ∈ Finset.range N, cexp ((θ + k * η : ℝ) * I) * ((m ! / (α + k * β) ^ (m + 1) : ℝ) : ℂ) +
        ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ m * (P t * R t ^ N / (1 - R t)) := fun N => by
    rw [setIntegral_congr_fun measurableSet_Ioi (hsplit N), integral_add, integral_finsetSum]
    · congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      simp_rw [hPR]
      exact integral_pow_mul_kernel m (hαk k) _
    · intro k _; simp_rw [hPR]; exact integrableOn_pow_mul_kernel m (hαk k) _
    · refine integrable_finsetSum _ fun k _ => ?_
      simp_rw [hPR]; exact integrableOn_pow_mul_kernel m (hαk k) _
    · exact (hrem N).1
  refine ⟨(hrem 0).1.congr_fun (fun t _ => by simp [P, R]) measurableSet_Ioi, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun N : ℕ => c⁻¹ * (m ! / (α + N * β) ^ (m + 1))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => α + N * β) atTop atTop :=
      tendsto_atTop_add_const_left _ _
        (tendsto_natCast_atTop_atTop.atTop_mul_const hβ)
    have h2 := (tendsto_pow_atTop (n := m + 1) (by omega)).comp h1
    simpa [div_eq_mul_inv] using (h2.inv_tendsto_atTop.const_mul ((m ! : ℝ))).const_mul c⁻¹
  refine squeeze_zero (fun N => norm_nonneg _) (fun N => ?_) hlim
  rw [hInt N, norm_sub_rev, add_sub_cancel_left]
  exact (hrem N).2


private lemma kernel_factor (u v : ℂ) : cosh v - cos u =
    (cexp v - cexp (u * I)) * (cexp v * cexp (u * I) - 1) / (2 * cexp v * cexp (u * I)) := by
  rw [Complex.cos, Complex.cosh, show -u * I = -(u * I) by ring, Complex.exp_neg,
    Complex.exp_neg]
  have := Complex.exp_ne_zero v
  have := Complex.exp_ne_zero (u * I)
  field_simp
  ring

private lemma kernel_ne {u v : ℂ} (h : cosh v - cos u ≠ 0) :
    cexp v - cexp (u * I) ≠ 0 ∧ cexp v * cexp (u * I) - 1 ≠ 0 := by
  rw [kernel_factor] at h
  exact ⟨fun h' => h (by rw [h']; ring), fun h' => h (by rw [h']; ring)⟩

/-- The even geometric kernel. -/
theorem geometric_kernel_add {u v : ℂ} (h : cosh v - cos u ≠ 0) :
    cexp (-v + u * I) / (1 - cexp (-v + u * I)) + cexp (-v + -u * I) / (1 - cexp (-v + -u * I)) =
      (cos u - cexp (-v)) / (cosh v - cos u) := by
  obtain ⟨h1, h2⟩ := kernel_ne h
  rw [kernel_factor]
  have hE := Complex.exp_ne_zero (u * I)
  have hF := Complex.exp_ne_zero v
  rw [Complex.cos, show -u * I = -(u * I) by ring, Complex.exp_add, Complex.exp_add,
    Complex.exp_neg, Complex.exp_neg]
  set E := cexp (u * I)
  set F := cexp v
  have h3 : 1 - F⁻¹ * E ≠ 0 := by
    rw [show 1 - F⁻¹ * E = (F - E) / F by field_simp]; exact div_ne_zero h1 hF
  have h4 : 1 - F⁻¹ * E⁻¹ ≠ 0 := by
    rw [show 1 - F⁻¹ * E⁻¹ = (F * E - 1) / (F * E) by field_simp]
    exact div_ne_zero h2 (mul_ne_zero hF hE)
  field_simp
  ring

/-- The odd geometric kernel. -/
theorem geometric_kernel_sub {u v : ℂ} (h : cosh v - cos u ≠ 0) :
    cexp (-v + u * I) / (1 - cexp (-v + u * I)) - cexp (-v + -u * I) / (1 - cexp (-v + -u * I)) =
      I * sin u / (cosh v - cos u) := by
  obtain ⟨h1, h2⟩ := kernel_ne h
  rw [kernel_factor]
  have hE := Complex.exp_ne_zero (u * I)
  have hF := Complex.exp_ne_zero v
  rw [Complex.sin, show -u * I = -(u * I) by ring, Complex.exp_add, Complex.exp_add,
    Complex.exp_neg, Complex.exp_neg]
  set E := cexp (u * I)
  set F := cexp v
  have h3 : 1 - F⁻¹ * E ≠ 0 := by
    rw [show 1 - F⁻¹ * E = (F - E) / F by field_simp]; exact div_ne_zero h1 hF
  have h4 : 1 - F⁻¹ * E⁻¹ ≠ 0 := by
    rw [show 1 - F⁻¹ * E⁻¹ = (F * E - 1) / (F * E) by field_simp]
    exact div_ne_zero h2 (mul_ne_zero hF hE)
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring


private lemma cexp_two_mul (z : ℂ) : cexp (2 * z) = cexp z ^ 2 := by
  rw [two_mul, Complex.exp_add, sq]

private lemma euler_kernel_setup {a b : ℂ} (h : cosh (2 * b) - cos (2 * a) ≠ 0) :
    cexp b ^ 2 - cexp (a * I) ^ 2 ≠ 0 ∧ cexp b ^ 2 * cexp (a * I) ^ 2 - 1 ≠ 0 := by
  obtain ⟨h1, h2⟩ := kernel_ne h
  rw [show 2 * a * I = 2 * (a * I) by ring, cexp_two_mul, cexp_two_mul] at h1 h2
  exact ⟨h1, h2⟩

/-- The odd-power even kernel. -/
theorem geometric_odd_kernel_add {a b : ℂ} (h : cosh (2 * b) - cos (2 * a) ≠ 0) :
    cexp (-b + a * I) / (1 - cexp (-(2 * b) + 2 * a * I)) +
      cexp (-b + -a * I) / (1 - cexp (-(2 * b) + -(2 * a) * I)) =
      2 * sinh b * cos a / (cosh (2 * b) - cos (2 * a)) := by
  obtain ⟨h1, h2⟩ := euler_kernel_setup h
  rw [kernel_factor]
  have hE := Complex.exp_ne_zero (a * I)
  have hF := Complex.exp_ne_zero b
  rw [Complex.cos, Complex.sinh, show -a * I = -(a * I) by ring,
    show -(2 * a) * I = -(2 * (a * I)) by ring, show 2 * a * I = 2 * (a * I) by ring]
  simp only [Complex.exp_add, Complex.exp_neg, cexp_two_mul]
  set E := cexp (a * I)
  set F := cexp b
  have h3 : 1 - (F ^ 2)⁻¹ * E ^ 2 ≠ 0 := by
    rw [show 1 - (F ^ 2)⁻¹ * E ^ 2 = (F ^ 2 - E ^ 2) / F ^ 2 by field_simp]
    exact div_ne_zero h1 (pow_ne_zero _ hF)
  have h4 : 1 - (F ^ 2)⁻¹ * (E ^ 2)⁻¹ ≠ 0 := by
    rw [show 1 - (F ^ 2)⁻¹ * (E ^ 2)⁻¹ = (F ^ 2 * E ^ 2 - 1) / (F ^ 2 * E ^ 2) by field_simp]
    exact div_ne_zero h2 (by positivity)
  field_simp
  ring

/-- The odd-power odd kernel. -/
theorem geometric_odd_kernel_sub {a b : ℂ} (h : cosh (2 * b) - cos (2 * a) ≠ 0) :
    cexp (-b + a * I) / (1 - cexp (-(2 * b) + 2 * a * I)) -
      cexp (-b + -a * I) / (1 - cexp (-(2 * b) + -(2 * a) * I)) =
      2 * I * cosh b * sin a / (cosh (2 * b) - cos (2 * a)) := by
  obtain ⟨h1, h2⟩ := euler_kernel_setup h
  rw [kernel_factor]
  have hE := Complex.exp_ne_zero (a * I)
  have hF := Complex.exp_ne_zero b
  rw [Complex.sin, Complex.cosh, show -a * I = -(a * I) by ring,
    show -(2 * a) * I = -(2 * (a * I)) by ring, show 2 * a * I = 2 * (a * I) by ring]
  simp only [Complex.exp_add, Complex.exp_neg, cexp_two_mul]
  set E := cexp (a * I)
  set F := cexp b
  have h3 : 1 - (F ^ 2)⁻¹ * E ^ 2 ≠ 0 := by
    rw [show 1 - (F ^ 2)⁻¹ * E ^ 2 = (F ^ 2 - E ^ 2) / F ^ 2 by field_simp]
    exact div_ne_zero h1 (pow_ne_zero _ hF)
  have h4 : 1 - (F ^ 2)⁻¹ * (E ^ 2)⁻¹ ≠ 0 := by
    rw [show 1 - (F ^ 2)⁻¹ * (E ^ 2)⁻¹ = (F ^ 2 * E ^ 2 - 1) / (F ^ 2 * E ^ 2) by field_simp]
    exact div_ne_zero h2 (by positivity)
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring


/-- `‖sinh (X + iY)‖ ≥ cosh X |sin Y|`. -/
private lemma cosh_mul_abs_sin_le_norm_sinh (X Y : ℝ) :
    Real.cosh X * |Real.sin Y| ≤ ‖Complex.sinh (X + Y * I)‖ := by
  refine le_trans (le_of_eq ?_) (abs_im_le_norm _)
  rw [Complex.sinh_add, Complex.sinh_mul_I, Complex.cosh_mul_I, ← Complex.ofReal_sinh,
    ← Complex.ofReal_cosh, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, zero_mul, add_zero, mul_one, Complex.mul_re, sub_zero, zero_add]
  rw [abs_mul, abs_of_pos (Real.cosh_pos X)]

private lemma cosh_sub_cos_eq (t : ℝ) (y : ℂ) :
    Complex.cosh (2 * π * t) - Complex.cos (2 * π * y) =
      2 * Complex.sinh (π * t + π * y * I) * Complex.sinh (π * t - π * y * I) := by
  rw [Complex.cosh, Complex.cos, Complex.sinh, Complex.sinh]
  simp only [neg_sub, neg_add, Complex.exp_add, Complex.exp_sub, Complex.exp_neg]
  have h1 : cexp (2 * π * t) = cexp (π * t) ^ 2 := by rw [← Complex.exp_nat_mul]; ring_nf
  have h2 : cexp (2 * π * y * I) = cexp (π * y * I) ^ 2 := by rw [← Complex.exp_nat_mul]; ring_nf
  have h4 : cexp (-(2 * π * y) * I) = (cexp (π * y * I) ^ 2)⁻¹ := by
    rw [show -(2 * π * y) * I = -(2 * π * y * I) by ring, Complex.exp_neg, h2]
  simp only [h1, h2, h4]
  have := Complex.exp_ne_zero (π * t)
  have := Complex.exp_ne_zero (π * y * I)
  field_simp
  ring

/-- **Lower bound for the denominator.** For `t ≥ 0`,
`|cosh 2πt - cos 2πy| ≥ sin²(π Re y) e^{2πt}/2`. -/
private lemma norm_cosh_sub_cos_ge (t : ℝ) (y : ℂ) :
    Real.sin (π * y.re) ^ 2 * Real.exp (2 * π * t) / 2 ≤
      ‖Complex.cosh (2 * π * t) - Complex.cos (2 * π * y)‖ := by
  rw [cosh_sub_cos_eq]
  have e1 : (π * t + π * y * I : ℂ) = ((π * (t - y.im) : ℝ) : ℂ) + ((π * y.re : ℝ) : ℂ) * I := by
    conv_lhs => rw [← Complex.re_add_im y]
    push_cast; ring_nf; rw [Complex.I_sq]; ring
  have e2 : (π * t - π * y * I : ℂ) =
      ((π * (t + y.im) : ℝ) : ℂ) + ((-(π * y.re)) : ℝ) * I := by
    conv_lhs => rw [← Complex.re_add_im y]
    push_cast; ring_nf; rw [Complex.I_sq]; ring
  rw [e1, e2, norm_mul, norm_mul]
  have b1 := cosh_mul_abs_sin_le_norm_sinh (π * (t - y.im)) (π * y.re)
  have b2 := cosh_mul_abs_sin_le_norm_sinh (π * (t + y.im)) (-(π * y.re))
  rw [Real.sin_neg, abs_neg] at b2
  have hprod : Real.cosh (π * (t - y.im)) * Real.cosh (π * (t + y.im)) =
      (Real.cosh (2 * π * t) + Real.cosh (2 * π * y.im)) / 2 := by
    rw [show π * (t - y.im) = π * t - π * y.im by ring,
      show π * (t + y.im) = π * t + π * y.im by ring,
      Real.cosh_sub, Real.cosh_add, show 2 * π * t = 2 * (π * t) by ring,
      show 2 * π * y.im = 2 * (π * y.im) by ring, Real.cosh_two_mul, Real.cosh_two_mul]
    have hA := Real.cosh_sq_sub_sinh_sq (π * t)
    have hB := Real.cosh_sq_sub_sinh_sq (π * y.im)
    linear_combination (Real.cosh (π * y.im) ^ 2 - 1 / 2 -
      (Real.cosh (π * y.im) ^ 2 - Real.sinh (π * y.im) ^ 2 - 1)) * hA +
      (Real.cosh (π * t) ^ 2 - 1 / 2) * hB
  have hc1 : Real.exp (2 * π * t) / 2 ≤ Real.cosh (2 * π * t) := by
    rw [Real.cosh_eq]; linarith [Real.exp_pos (-(2 * π * t))]
  have hc2 : 0 ≤ Real.cosh (2 * π * y.im) := (Real.cosh_pos _).le
  have hs : |Real.sin (π * y.re)| ^ 2 = Real.sin (π * y.re) ^ 2 := sq_abs _
  have hA := Real.cosh_pos (π * (t - y.im))
  have hB := Real.cosh_pos (π * (t + y.im))
  have hS := abs_nonneg (Real.sin (π * y.re))
  calc Real.sin (π * y.re) ^ 2 * Real.exp (2 * π * t) / 2
      ≤ 2 * (Real.cosh (π * (t - y.im)) * |Real.sin (π * y.re)|) *
          (Real.cosh (π * (t + y.im)) * |Real.sin (π * y.re)|) := by
        rw [show 2 * (Real.cosh (π * (t - y.im)) * |Real.sin (π * y.re)|) *
          (Real.cosh (π * (t + y.im)) * |Real.sin (π * y.re)|) =
          2 * (Real.cosh (π * (t - y.im)) * Real.cosh (π * (t + y.im))) *
            |Real.sin (π * y.re)| ^ 2 by ring, hprod, hs]
        nlinarith [sq_nonneg (Real.sin (π * y.re))]
    _ ≤ ‖(2 : ℂ)‖ * ‖Complex.sinh (((π * (t - y.im) : ℝ) : ℂ) + ((π * y.re : ℝ) : ℂ) * I)‖ *
          ‖Complex.sinh (((π * (t + y.im) : ℝ) : ℂ) + ((-(π * y.re)) : ℝ) * I)‖ := by
        rw [Complex.norm_two]
        gcongr



/-- The vertical strip `0 < Re x < 1`. -/
private lemma isOpen_strip : IsOpen {x : ℂ | 0 < x.re ∧ x.re < 1} :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)

private lemma cosh_sub_cos_ne_zero {y : ℂ} (hy : 0 < y.re ∧ y.re < 1) (t : ℝ) :
    Complex.cosh (2 * π * t) - Complex.cos (2 * π * y) ≠ 0 := by
  intro h
  have hb := norm_cosh_sub_cos_ge t y
  rw [h, norm_zero] at hb
  have hs : 0 < Real.sin (π * y.re) :=
    Real.sin_pos_of_pos_of_lt_pi (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
  have : 0 < Real.sin (π * y.re) ^ 2 * Real.exp (2 * π * t) / 2 := by positivity
  linarith

/-- **Holomorphy of the kernel integrals** of DLMF 24.7.7–24.7.10 in the strip `0 < Re x < 1`. -/
theorem differentiableOn_integral_div_cosh_sub_cos (m : ℕ) (N : ℂ → ℝ → ℂ)
    (hNd : ∀ t, Differentiable ℂ (fun y => N y t)) (hNc : ∀ y, Continuous (N y))
    (hNb : ∀ x₀ : ℂ, ∃ C, ∀ᶠ y in 𝓝 x₀, ∀ t : ℝ, 0 < t → ‖N y t‖ ≤ C * Real.exp (π * t)) :
    DifferentiableOn ℂ (fun y => ∫ t in Ioi (0 : ℝ),
      N y t / (Complex.cosh (2 * π * t) - Complex.cos (2 * π * y)) * (t : ℂ) ^ m)
      {x : ℂ | 0 < x.re ∧ x.re < 1} := by
  refine differentiableOn_integral_Ioi_of_locally_dominated isOpen_strip 0 (fun y hy => ?_)
    (ae_of_all _ fun t => ?_) (fun x₀ hx₀ => ?_)
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine Continuous.continuousOn ?_
    refine Continuous.mul (Continuous.div (hNc y) (by fun_prop)
      fun t => cosh_sub_cos_ne_zero hy t) (by fun_prop)
  · refine DifferentiableOn.mul (DifferentiableOn.div (hNd t).differentiableOn (by fun_prop)
      fun y hy => cosh_sub_cos_ne_zero hy t) (differentiableOn_const _)
  · obtain ⟨C, hC⟩ := hNb x₀
    set s₀ := Real.sin (π * x₀.re)
    have hs₀ : 0 < s₀ :=
      Real.sin_pos_of_pos_of_lt_pi (by nlinarith [Real.pi_pos, hx₀.1])
        (by nlinarith [Real.pi_pos, hx₀.2])
    have hcont : Tendsto (fun y : ℂ => Real.sin (π * y.re)) (𝓝 x₀) (𝓝 s₀) :=
      ((Real.continuous_sin.comp (continuous_const.mul Complex.continuous_re)).tendsto x₀)
    have hev := hcont.eventually (lt_mem_nhds (by linarith : s₀ / 2 < s₀))
    refine ⟨_, hC.and hev, fun t => C * (8 / s₀ ^ 2) * (t ^ m * Real.exp (-(π * t))),
      (integrableOn_pow_mul_exp_neg_mul m Real.pi_pos).const_mul _,
      (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht y hy => ?_)⟩
    obtain ⟨hN, hsy⟩ := hy
    have ht0 : 0 < t := ht
    have hD := norm_cosh_sub_cos_ge t y
    have hsy' : (s₀ / 2) ^ 2 ≤ Real.sin (π * y.re) ^ 2 := by
      have : 0 ≤ s₀ / 2 := by positivity
      nlinarith
    have hE : Real.exp (2 * π * t) = Real.exp (π * t) * Real.exp (π * t) := by
      rw [← Real.exp_add]; ring_nf
    have hDpos : 0 < (s₀ / 2) ^ 2 * Real.exp (2 * π * t) / 2 := by positivity
    have hD' : (s₀ / 2) ^ 2 * Real.exp (2 * π * t) / 2 ≤
        ‖Complex.cosh (2 * π * t) - Complex.cos (2 * π * y)‖ :=
      le_trans (by gcongr) hD
    have hNy := hN t ht0
    have hC0 : 0 ≤ C := by
      have := (norm_nonneg (N y t)).trans hNy
      exact nonneg_of_mul_nonneg_left this (Real.exp_pos _)
    rw [norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg ht0.le]
    calc ‖N y t‖ / ‖Complex.cosh (2 * π * t) - Complex.cos (2 * π * y)‖ * t ^ m
        ≤ C * Real.exp (π * t) / ((s₀ / 2) ^ 2 * Real.exp (2 * π * t) / 2) * t ^ m := by
          gcongr
      _ = C * (8 / s₀ ^ 2) * (t ^ m * Real.exp (-(π * t))) := by
          rw [hE, Real.exp_neg]
          field_simp
          ring


private lemma cos_two_pi_mul_lt_one {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    Real.cos (2 * π * x) < 1 := by
  refine lt_of_le_of_ne (Real.cos_le_one _) fun h => ?_
  have := (Real.cos_eq_one_iff_of_lt_of_lt (x := 2 * π * x) (by nlinarith [Real.pi_pos])
    (by nlinarith [Real.pi_pos])).mp h
  have : 0 < 2 * π * x := by positivity
  linarith

private lemma cexp_add_cexp_neg (a : ℝ) :
    cexp ((a : ℂ) * I) + cexp (((-a : ℝ) : ℂ) * I) = ((2 * Real.cos a : ℝ) : ℂ) := by
  push_cast
  rw [Complex.cos, show -(a : ℂ) * I = -((a : ℂ) * I) by ring]
  ring

private lemma cexp_sub_cexp_neg (a : ℝ) :
    cexp ((a : ℂ) * I) - cexp (((-a : ℝ) : ℂ) * I) = I * ((2 * Real.sin a : ℝ) : ℂ) := by
  push_cast
  rw [Complex.sin, show -(a : ℂ) * I = -((a : ℂ) * I) by ring]
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

private lemma mem_strip_ofReal {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    0 < (x : ℂ).re ∧ (x : ℂ).re < 1 := by simpa using ⟨hx0, hx1⟩

/-- Moments of the even Bernoulli kernel at real `x ∈ (0, 1)`. -/
theorem tendsto_sum_cos_integral_bernoulliKernel (m : ℕ) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N,
        ((2 * Real.cos (2 * π * (k + 1) * x) * (m ! / (2 * π * (k + 1)) ^ (m + 1)) : ℝ) : ℂ))
      atTop (𝓝 (∫ t in Ioi (0 : ℝ), (Complex.cos (2 * π * x) - Complex.exp (-(2 * π * t))) /
        (Complex.cosh (2 * π * t) - Complex.cos (2 * π * x)) * (t : ℂ) ^ m)) := by
  have hc := cos_two_pi_mul_lt_one hx0 hx1
  have hc' : Real.cos (-(2 * π * x)) < 1 := by rwa [Real.cos_neg]
  have h2π : (0 : ℝ) < 2 * π := by positivity
  obtain ⟨i₁, t₁⟩ := tendsto_sum_integral_pow_mul_geometric m h2π h2π _ hc
  obtain ⟨i₂, t₂⟩ := tendsto_sum_integral_pow_mul_geometric m h2π h2π _ hc'
  have h := t₁.add t₂
  rw [← integral_add i₁ i₂] at h
  convert h using 2 with N
  · rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show 2 * π * x + k * (2 * π * x) = 2 * π * (k + 1) * x by ring,
      show -(2 * π * x) + k * -(2 * π * x) = -(2 * π * (k + 1) * x) by ring,
      show 2 * π + k * (2 * π) = 2 * π * (k + 1) by ring, ← add_mul, cexp_add_cexp_neg]
    push_cast; ring
  · refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    have hD := cosh_sub_cos_ne_zero (mem_strip_ofReal hx0 hx1) t
    rw [← mul_add]
    have hk := geometric_kernel_add (u := 2 * π * x) (v := 2 * π * t) hD
    push_cast
    rw [show -(2 * (π : ℂ) * t) + -(2 * π * x) * I = -(2 * π * t) + -(2 * π * x) * I by ring,
      show -(2 * (π : ℂ) * t) + 2 * π * x * I = -(2 * π * t) + 2 * π * x * I by ring]
    rw [show -(2 * (π : ℂ) * t) = -(2 * π * t) by ring] at *
    rw [hk]; ring


/-- Moments of the odd Bernoulli kernel at real `x ∈ (0, 1)`. -/
theorem tendsto_sum_sin_integral_bernoulliKernel (m : ℕ) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N,
        ((2 * Real.sin (2 * π * (k + 1) * x) * (m ! / (2 * π * (k + 1)) ^ (m + 1)) : ℝ) : ℂ))
      atTop (𝓝 (∫ t in Ioi (0 : ℝ), Complex.sin (2 * π * x) /
        (Complex.cosh (2 * π * t) - Complex.cos (2 * π * x)) * (t : ℂ) ^ m)) := by
  have hc := cos_two_pi_mul_lt_one hx0 hx1
  have hc' : Real.cos (-(2 * π * x)) < 1 := by rwa [Real.cos_neg]
  have h2π : (0 : ℝ) < 2 * π := by positivity
  obtain ⟨i₁, t₁⟩ := tendsto_sum_integral_pow_mul_geometric m h2π h2π _ hc
  obtain ⟨i₂, t₂⟩ := tendsto_sum_integral_pow_mul_geometric m h2π h2π _ hc'
  have h := (t₁.sub t₂).const_mul (-I)
  rw [← integral_sub i₁ i₂, ← integral_const_mul] at h
  convert h using 2 with N
  · rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show 2 * π * x + k * (2 * π * x) = 2 * π * (k + 1) * x by ring,
      show -(2 * π * x) + k * -(2 * π * x) = -(2 * π * (k + 1) * x) by ring,
      show 2 * π + k * (2 * π) = 2 * π * (k + 1) by ring, ← sub_mul, cexp_sub_cexp_neg]
    push_cast; ring_nf; rw [Complex.I_sq]; ring
  · refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    have hD := cosh_sub_cos_ne_zero (mem_strip_ofReal hx0 hx1) t
    rw [← mul_sub]
    have hk := geometric_kernel_sub (u := 2 * π * x) (v := 2 * π * t) hD
    push_cast
    rw [show -(2 * (π : ℂ) * t) + -(2 * π * x) * I = -(2 * π * t) + -(2 * π * x) * I by ring,
      show -(2 * (π : ℂ) * t) + 2 * π * x * I = -(2 * π * t) + 2 * π * x * I by ring]
    rw [hk]; ring_nf; rw [Complex.I_sq]; ring

/-- Moments of the odd-power sine kernel at real `x ∈ (0, 1)`. -/
theorem tendsto_sum_sin_integral_eulerKernel (m : ℕ) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N,
        ((Real.sin ((2 * k + 1) * π * x) * (m ! / ((2 * k + 1) * π) ^ (m + 1)) : ℝ) : ℂ))
      atTop (𝓝 (∫ t in Ioi (0 : ℝ), Complex.sin (π * x) * Complex.cosh (π * t) /
        (Complex.cosh (2 * π * t) - Complex.cos (2 * π * x)) * (t : ℂ) ^ m)) := by
  have hc := cos_two_pi_mul_lt_one hx0 hx1
  have hc' : Real.cos (-(2 * π * x)) < 1 := by rwa [Real.cos_neg]
  have h2π : (0 : ℝ) < 2 * π := by positivity
  obtain ⟨i₁, t₁⟩ := tendsto_sum_integral_pow_mul_geometric m Real.pi_pos h2π (π * x) hc
  obtain ⟨i₂, t₂⟩ := tendsto_sum_integral_pow_mul_geometric m Real.pi_pos h2π (-(π * x)) hc'
  have h := (t₁.sub t₂).const_mul (-I / 2)
  rw [← integral_sub i₁ i₂, ← integral_const_mul] at h
  convert h using 2 with N
  · rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show π * x + k * (2 * π * x) = (2 * k + 1) * π * x by ring,
      show -(π * x) + k * -(2 * π * x) = -((2 * k + 1) * π * x) by ring,
      show π + k * (2 * π) = (2 * k + 1) * π by ring, ← sub_mul, cexp_sub_cexp_neg]
    push_cast; ring_nf; rw [Complex.I_sq]; ring
  · refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    have hD := cosh_sub_cos_ne_zero (mem_strip_ofReal hx0 hx1) t
    rw [← mul_sub]
    have hD' : Complex.cosh (2 * (π * t)) - Complex.cos (2 * (π * x)) ≠ 0 := by
      rw [← mul_assoc, ← mul_assoc]; exact hD
    have hk := geometric_odd_kernel_sub hD'
    push_cast
    rw [show -(π * (t : ℂ)) + π * x * I = -(π * t) + π * x * I by ring,
      show -(2 * (π : ℂ) * t) + 2 * π * x * I = -(2 * (π * t)) + 2 * (π * x) * I by ring,
      show -((π : ℂ) * t) + -(π * x) * I = -(π * t) + -(π * x) * I by ring,
      show -(2 * (π : ℂ) * t) + -(2 * π * x) * I = -(2 * (π * t)) + -(2 * (π * x)) * I by ring]
    rw [hk, ← mul_assoc, ← mul_assoc]; ring_nf; rw [Complex.I_sq]; ring

/-- Moments of the odd-power cosine kernel at real `x ∈ (0, 1)`. -/
theorem tendsto_sum_cos_integral_eulerKernel (m : ℕ) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N,
        ((Real.cos ((2 * k + 1) * π * x) * (m ! / ((2 * k + 1) * π) ^ (m + 1)) : ℝ) : ℂ))
      atTop (𝓝 (∫ t in Ioi (0 : ℝ), Complex.cos (π * x) * Complex.sinh (π * t) /
        (Complex.cosh (2 * π * t) - Complex.cos (2 * π * x)) * (t : ℂ) ^ m)) := by
  have hc := cos_two_pi_mul_lt_one hx0 hx1
  have hc' : Real.cos (-(2 * π * x)) < 1 := by rwa [Real.cos_neg]
  have h2π : (0 : ℝ) < 2 * π := by positivity
  obtain ⟨i₁, t₁⟩ := tendsto_sum_integral_pow_mul_geometric m Real.pi_pos h2π (π * x) hc
  obtain ⟨i₂, t₂⟩ := tendsto_sum_integral_pow_mul_geometric m Real.pi_pos h2π (-(π * x)) hc'
  have h := (t₁.add t₂).const_mul (1 / 2 : ℂ)
  rw [← integral_add i₁ i₂, ← integral_const_mul] at h
  convert h using 2 with N
  · rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show π * x + k * (2 * π * x) = (2 * k + 1) * π * x by ring,
      show -(π * x) + k * -(2 * π * x) = -((2 * k + 1) * π * x) by ring,
      show π + k * (2 * π) = (2 * k + 1) * π by ring, ← add_mul, cexp_add_cexp_neg]
    push_cast; ring
  · refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    have hD := cosh_sub_cos_ne_zero (mem_strip_ofReal hx0 hx1) t
    rw [← mul_add]
    have hD' : Complex.cosh (2 * (π * t)) - Complex.cos (2 * (π * x)) ≠ 0 := by
      rw [← mul_assoc, ← mul_assoc]; exact hD
    have hk := geometric_odd_kernel_add hD'
    push_cast
    rw [show -(π * (t : ℂ)) + π * x * I = -(π * t) + π * x * I by ring,
      show -(2 * (π : ℂ) * t) + 2 * π * x * I = -(2 * (π * t)) + 2 * (π * x) * I by ring,
      show -((π : ℂ) * t) + -(π * x) * I = -(π * t) + -(π * x) * I by ring,
      show -(2 * (π : ℂ) * t) + -(2 * π * x) * I = -(2 * (π * t)) + -(2 * (π * x)) * I by ring]
    rw [hk, ← mul_assoc, ← mul_assoc]; ring_nf

end DLMF.BernoulliEuler
