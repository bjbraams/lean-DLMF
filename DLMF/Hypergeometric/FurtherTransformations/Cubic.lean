/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.FurtherTransformations.Quadratic

/-!
# Cubic transformations of Gauss functions

Branch-power identities and cubic transformations, including the Borwein cubic relation.

Source references and common attribution are retained in
`DLMF.Hypergeometric.FurtherTransformations`.
-/

@[expose] public section

open Complex Filter

open scoped Real Topology ComplexConjugate

noncomputable section

namespace DLMF.Hypergeometric

/-- Principal powers of a square in the right half-plane. -/
theorem sq_cpow {x : ℂ} (hx : 0 < x.re) (y : ℂ) : (x ^ 2) ^ y = x ^ (2 * y) := by
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  have harg : |x.arg| < Real.pi / 2 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hx)
  have hsq : x ^ 2 = exp (2 * log x) := by
    rw [show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, exp_nat_mul, exp_log hx0]
  have hlog : log (x ^ 2) = 2 * log x := by
    rw [hsq, log_exp]
    · simp only [mul_im, log_im, re_ofNat, im_ofNat, zero_mul, add_zero]
      linarith [(abs_lt.mp harg).1]
    · simp only [mul_im, log_im, re_ofNat, im_ofNat, zero_mul, add_zero]
      linarith [(abs_lt.mp harg).2]
  rw [cpow_def_of_ne_zero (pow_ne_zero 2 hx0), hlog, cpow_def_of_ne_zero hx0]
  ring_nf

/-- `‖1 - 1/s‖ < 1` exactly when `Re s > 1/2`. -/
theorem norm_one_sub_recip_lt_one_iff {s : ℂ} (hs : s ≠ 0) : ‖1 - 1 / s‖ < 1 ↔ 1 / 2 < s.re := by
  rw [show 1 - 1 / s = (s - 1) / s by field_simp, norm_div, div_lt_one (norm_pos_iff.mpr hs),
    ← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _), ← normSq_eq_norm_sq, ← normSq_eq_norm_sq,
    normSq_apply, normSq_apply]
  simp only [sub_re, one_re, sub_im, one_im, sub_zero]
  constructor <;> intro h <;> nlinarith

/-- The half-sum quadratic domain is star-shaped about the origin. -/
theorem isPreconnected_halfSum :
    IsPreconnected {z : ℂ | ‖z‖ < 1 ∧ z.re < 1 / 2 ∧ ‖4 * z * (z - 1) / (1 - 2 * z) ^ 2‖ < 1} := by
  have hv : ∀ z : ℂ, 1 - 2 * z ≠ 0 →
      4 * z * (z - 1) / (1 - 2 * z) ^ 2 = 1 - 1 / (1 - 2 * z) ^ 2 := by
    intro z hz
    rw [eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq (pow_ne_zero 2 hz)]
    ring
  have hstar : StarConvex ℝ 0
      {z : ℂ | ‖z‖ < 1 ∧ z.re < 1 / 2 ∧ ‖4 * z * (z - 1) / (1 - 2 * z) ^ 2‖ < 1} := by
    intro z ⟨h1, h2, h3⟩ t u ht hu htu
    have hu' : u = 1 - t := by linarith
    subst hu'
    simp only [smul_zero, zero_add, real_smul]
    have hre0 : 0 < (1 - 2 * z).re := by simp; linarith
    have hz0 : 1 - 2 * z ≠ 0 := by intro h; rw [h] at hre0; simp at hre0
    have e0 : (1 - 2 * ((1 - t : ℝ) : ℂ) * z).re = 1 - 2 * (1 - t) * z.re := by
      simp [mul_re]
    have hre0' : 0 < (1 - 2 * ((1 - t : ℝ) : ℂ) * z).re := by
      rw [e0]
      rcases le_or_gt z.re 0 with h | h <;> nlinarith
    have hz0' : 1 - 2 * ((1 - t : ℝ) : ℂ) * z ≠ 0 := by
      intro h; rw [h] at hre0'; simp at hre0'
    refine ⟨?_, ?_, ?_⟩
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      nlinarith [norm_nonneg z]
    · simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
      rcases le_or_gt z.re 0 with h | h
      · nlinarith
      · nlinarith
    · rw [show 4 * (((1 - t : ℝ) : ℂ) * z) * (((1 - t : ℝ) : ℂ) * z - 1) /
          (1 - 2 * (((1 - t : ℝ) : ℂ) * z)) ^ 2 =
          1 - 1 / (1 - 2 * ((1 - t : ℝ) : ℂ) * z) ^ 2 by
            rw [hv _ (by rwa [← mul_assoc]), ← mul_assoc]]
      rw [hv z hz0, norm_one_sub_recip_lt_one_iff (pow_ne_zero 2 hz0)] at h3
      rw [norm_one_sub_recip_lt_one_iff (pow_ne_zero 2 hz0')]
      have hsq : (1 - 2 * z) ^ 2 = (1 - 2 * z) * (1 - 2 * z) := sq _
      have hR : 1 / 2 < (1 - 2 * z).re ^ 2 - (1 - 2 * z).im ^ 2 := by
        rw [hsq, mul_re] at h3; nlinarith
      have hx0 : 1 / 2 < (1 - 2 * z).re := by nlinarith
      have e : 1 - 2 * ((1 - t : ℝ) : ℂ) * z = (t : ℂ) + ((1 - t : ℝ) : ℂ) * (1 - 2 * z) := by
        push_cast; ring
      rw [e, sq, mul_re]
      simp only [add_re, ofReal_re, mul_re, ofReal_im, zero_mul, sub_zero, add_im, mul_im,
        zero_add, add_zero]
      have hpos : 0 < t ^ 2 / 2 + (1 - t) ^ 2 * ((1 - 2 * z).re ^ 2 - (1 - 2 * z).im ^ 2 - 1 / 2) := by
        rcases eq_or_lt_of_le ht with h | h
        · subst h; simp at hR ⊢; linarith
        · have : 0 < t ^ 2 / 2 := by positivity
          nlinarith [sq_nonneg (1 - t)]
      nlinarith [mul_nonneg (mul_nonneg ht hu) (le_of_lt (sub_pos.mpr hx0))]
  exact (hstar.isPathConnected ⟨by simp, by simp, by simp⟩).isConnected.isPreconnected

/-- Identity under the stated parameter and domain assumptions: `₂F₁ a b ((a + b + 1) / 2) z = (1
- 2 * z) ^ (-a) * ₂F₁ (a / 2) ((a + 1) / 2) ((a + b + 1) / 2) (4 * z * (z - 1) / (1 - 2 * z) ^
2)`. -/
@[dlmf 15.8.E17]
theorem quadratic_half_sum
    {a b z : ℂ}
    (hc : ∀ k : ℕ,
    (a + b + 1) / 2 ≠ -(k : ℂ))
    (hz : ‖z‖ < 1)
    (hr : z.re < 1 / 2)
    (hw : ‖4 * z *
    (z - 1) /
    (1 - 2 * z) ^ 2‖ < 1) :
    ₂F₁ a b ((a + b + 1) / 2) z =
      (1 - 2 * z) ^ (-a) * ₂F₁ (a / 2) ((a + 1) / 2) ((a + b + 1) / 2) (4 * z * (z - 1) / (1 - 2 * z) ^ 2) := by
  set C := (a + b + 1) / 2 with hC
  set H : ℂ → ℂ := ₂F₁ (a / 2) ((a + 1) / 2) C with hH
  set v : ℂ → ℂ := fun w => 4 * w * (w - 1) / (1 - 2 * w) ^ 2 with hvdef
  have hre : ∀ w : ℂ, w.re < 1 / 2 → 0 < (1 - 2 * w).re := fun w hw => by simp; linarith
  have hne : ∀ w : ℂ, w.re < 1 / 2 → 1 - 2 * w ≠ 0 := fun w hw h => by
    have := hre w hw; rw [h] at this; simp at this
  have hslit : ∀ w : ℂ, w.re < 1 / 2 → 1 - 2 * w ∈ slitPlane := fun w hw =>
    mem_slitPlane_iff.mpr (Or.inl (hre w hw))
  have hva : ∀ w : ℂ, w.re < 1 / 2 → AnalyticAt ℂ v w := fun w hw =>
    ((analyticAt_const.mul analyticAt_id).mul (analyticAt_id.sub analyticAt_const)).div
      ((analyticAt_const.sub (analyticAt_const.mul analyticAt_id)).pow 2)
      (pow_ne_zero 2 (hne w hw))
  have hPa : ∀ w : ℂ, w.re < 1 / 2 → AnalyticAt ℂ (fun w : ℂ => (1 - 2 * w) ^ (-a)) w :=
    fun w hw => (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)).cpow
      analyticAt_const (hslit w hw)
  -- Near the origin, via Gauss's quadratic transformation and Pfaff's transformation.
  have hball : ∀ w ∈ Metric.ball (0 : ℂ) (1 / 16),
      ₂F₁ a b C w = (1 - 2 * w) ^ (-a) * H (v w) := by
    intro w hw
    have hw' : ‖w‖ < 1 / 16 := by simpa using hw
    have hw1 : ‖w‖ < 1 := by linarith
    have hwre : w.re < 1 / 2 := by linarith [re_le_norm w]
    have hn1 : ‖1 - w‖ ≤ 1 + ‖w‖ := by
      have := norm_sub_le (1 : ℂ) w; rwa [norm_one] at this
    have hy : ‖4 * w * (1 - w)‖ < 1 := by
      rw [norm_mul, norm_mul, show ‖(4 : ℂ)‖ = 4 by norm_num]
      nlinarith [norm_nonneg w, norm_nonneg (1 - w)]
    have h12 : 7 / 8 ≤ ‖1 - 2 * w‖ := by
      have := norm_sub_norm_le (1 : ℂ) (2 * w)
      rw [norm_one, norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num] at this
      linarith
    have hyy : 4 * w * (1 - w) / (4 * w * (1 - w) - 1) = v w := by
      have := hne w hwre
      have h' : 4 * w * (1 - w) - 1 = -(1 - 2 * w) ^ 2 := by ring
      rw [h']
      simp only [hvdef]
      field_simp
      ring
    have hvw : ‖v w‖ < 1 := by
      simp only [hvdef, norm_div, norm_mul, norm_pow, show ‖(4 : ℂ)‖ = 4 by norm_num]
      rw [div_lt_one (by positivity)]
      have hn2 : ‖w - 1‖ ≤ 1 + ‖w‖ := by
        have := norm_sub_le w (1 : ℂ); rwa [norm_one, add_comm] at this
      nlinarith [norm_nonneg w, norm_nonneg (w - 1)]
    have hq := gauss_quadratic (a := a / 2) (b := b / 2)
      (by rw [show a / 2 + b / 2 + 1 / 2 = C by rw [hC]; ring]; exact hc) hw1 hy hwre
    rw [show a / 2 + b / 2 + 1 / 2 = C by rw [hC]; ring, show 2 * (a / 2) = a by ring,
      show 2 * (b / 2) = b by ring] at hq
    rw [hq, pfaff_transformation_of_ne_neg_nat hc hy (by rwa [hyy]), hyy,
      show C - b / 2 = (a + 1) / 2 by rw [hC]; ring,
      show 1 - 4 * w * (1 - w) = (1 - 2 * w) ^ 2 by ring, sq_cpow (hre w hwre),
      show 2 * -(a / 2) = -a by ring]
  -- Continuation over the star-shaped domain.
  set D : Set ℂ :=
    {z : ℂ | ‖z‖ < 1 ∧ z.re < 1 / 2 ∧ ‖4 * z * (z - 1) / (1 - 2 * z) ^ 2‖ < 1} with hD
  have hLan : AnalyticOnNhd ℂ (₂F₁ a b C : ℂ → ℂ) D := fun w hw =>
    analyticAt_ordinaryHypergeometric hw.1
  have hRan : AnalyticOnNhd ℂ (fun w => (1 - 2 * w) ^ (-a) * H (v w)) D := fun w hw =>
    (hPa w hw.2.1).mul ((analyticAt_ordinaryHypergeometric hw.2.2).comp (f := v)
      (hva w hw.2.1))
  have hev : (₂F₁ a b C : ℂ → ℂ) =ᶠ[𝓝 0] fun w => (1 - 2 * w) ^ (-a) * H (v w) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 16)] with w hw
    exact hball w hw
  exact hLan.eqOn_of_preconnected_of_eventuallyEq hRan isPreconnected_halfSum
    (by simp [hD]) hev ⟨hz, hr, hw⟩

/-- Identity under the stated parameter and domain assumptions: `₂F₁ a (1 - a) c z = (1 - 2 * z) ^
(1 - a - c) * (1 - z) ^ (c - 1) * ₂F₁ ((a + c) / 2) ((a + c - 1) / 2) c (4 * z * (z - 1) / (1
- 2 * z) ^ 2)`. -/
@[dlmf 15.8.E19]
theorem quadratic_complementary
    {a c z : ℂ}
    (hc : ∀ k : ℕ, c ≠ -(k : ℂ))
    (hz : ‖z‖ < 1)
    (hr : z.re < 1 / 2)
    (hw : ‖4 * z *
    (z - 1) /
    (1 - 2 * z) ^ 2‖ < 1) :
    ₂F₁ a (1 - a) c z =
      (1 - 2 * z) ^ (1 - a - c) * (1 - z) ^ (c - 1) * ₂F₁ ((a + c) / 2) ((a + c - 1) / 2) c (4 * z * (z - 1)
        / (1 - 2 * z) ^ 2) := by
  have hc' : ∀ k : ℕ, (c + a - 1 + (c - a) + 1) / 2 ≠ -(k : ℂ) := by
    rw [show (c + a - 1 + (c - a) + 1) / 2 = c by ring]; exact hc
  have h := quadratic_half_sum (a := c + a - 1) (b := c - a) hc' hz hr hw
  rw [show (c + a - 1 + (c - a) + 1) / 2 = c by ring] at h
  rw [euler_transformation_of_ne_neg_nat hc hz, show c - a - (1 - a) = c - 1 by ring,
    show c - (1 - a) = c + a - 1 by ring, ordinaryHypergeometric_symm (c - a) (c + a - 1), h,
    show -(c + a - 1) = 1 - a - c by ring, show (c + a - 1) / 2 = (a + c - 1) / 2 by ring,
    show (c + a - 1 + 1) / 2 = (a + c) / 2 by ring,
    ordinaryHypergeometric_symm ((a + c - 1) / 2) ((a + c) / 2)]
  ring

/-- Identity under the stated parameter and domain assumptions: `₂F₁ a (1 - a) c z = (1 - z) ^ (c
- 1) * ₂F₁ ((c - a) / 2) ((a + c - 1) / 2) c (4 * z * (1 - z))`. -/
@[dlmf 15.8.E20]
theorem quadratic_complementary_four_mul
    {a c z : ℂ}
    (hc : ∀ k : ℕ, c ≠ -(k : ℂ))
    (hz : ‖z‖ < 1)
    (hr : z.re < 1 / 2)
    (hw : ‖4 * z *
    (1 - z)‖ < 1) :
    ₂F₁ a (1 - a) c z =
      (1 - z) ^ (c - 1) * ₂F₁ ((c - a) / 2) ((a + c - 1) / 2) c (4 * z * (1 - z)) := by
  have hq := gauss_quadratic (a := (c - a) / 2) (b := (a + c - 1) / 2)
    (by rw [show (c - a) / 2 + (a + c - 1) / 2 + 1 / 2 = c by ring]; exact hc) hz hw hr
  rw [show (c - a) / 2 + (a + c - 1) / 2 + 1 / 2 = c by ring,
    show 2 * ((c - a) / 2) = c - a by ring, show 2 * ((a + c - 1) / 2) = c - (1 - a) by ring] at hq
  rw [euler_transformation_of_ne_neg_nat hc hz, show c - a - (1 - a) = c - 1 by ring, hq]

/-- The principal square root of a point of the slit plane lies in the right half-plane. -/
theorem re_cpow_half_pos_of_mem_slitPlane {z : ℂ} (hz : z ∈ slitPlane) :
    0 < (z ^ (1 / 2 : ℂ)).re := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have h1 : -Real.pi < z.arg := neg_pi_lt_arg z
  have h2 : z.arg < Real.pi := arg_lt_pi_iff.mpr (by
    rcases mem_slitPlane_iff.mp hz with h | h
    · exact Or.inl h.le
    · exact Or.inr h)
  rw [cpow_def_of_ne_zero hz0, exp_re]
  apply mul_pos (Real.exp_pos _)
  apply Real.cos_pos_of_mem_Ioo
  simp only [mul_im, log_im, log_re, one_div, inv_re, inv_im, re_ofNat, im_ofNat]
  constructor <;> norm_num <;> nlinarith [Real.pi_pos]

/-- Branch bookkeeping for the square-root quadratic transformation. -/
theorem phase_quadratic_sqrt {a z : ℂ} (hz : ‖z‖ < 1) (hs : z ∈ slitPlane) :
    (1 + z ^ (1 / 2 : ℂ)) ^ (-2 * a) *
      ((1 + z) / (1 + z ^ (1 / 2 : ℂ)) ^ 2) ^ (-a) = (1 + z) ^ (-a) := by
  set t := z ^ (1 / 2 : ℂ) with ht
  have htre : 0 < t.re := re_cpow_half_pos_of_mem_slitPlane hs
  have hz0 : z ≠ 0 := slitPlane_ne_zero hs
  have htsq : t ^ 2 = z := cpow_half_sq hz0
  have hre1 : 0 < (1 + z).re := by
    have := neg_le_of_abs_le (abs_re_le_norm z)
    simp only [add_re, one_re]; linarith
  have hre2 : 0 < (1 + t).re := by simp only [add_re, one_re]; linarith
  have h1 : 1 + z ≠ 0 := by intro h; rw [h] at hre1; simp at hre1
  have h2 : 1 + t ≠ 0 := by intro h; rw [h] at hre2; simp at hre2
  have harg1 := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre1))
  have harg2 := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre2))
  have himz : z.im = 2 * t.re * t.im := by rw [← htsq, sq, mul_im]; ring
  have hsame : ((1 + z).arg ≤ 0 ∧ (1 + t).arg ≤ 0) ∨ (0 ≤ (1 + z).arg ∧ 0 ≤ (1 + t).arg) := by
    rcases le_total t.im 0 with h | h
    · left
      exact ⟨arg_le_zero_of_im_nonpos hre1 (by simp; nlinarith),
        arg_le_zero_of_im_nonpos hre2 (by simp; linarith)⟩
    · right
      exact ⟨arg_nonneg_iff.mpr (by simp; nlinarith), arg_nonneg_iff.mpr (by simp; linarith)⟩
  have hexp : exp (log (1 + z) - 2 * log (1 + t)) = (1 + z) / (1 + t) ^ 2 := by
    rw [exp_sub, show (2 : ℂ) * log (1 + t) = ((2 : ℕ) : ℂ) * log (1 + t) by norm_num,
      exp_nat_mul, exp_log h1, exp_log h2]
  have him : (log (1 + z) - 2 * log (1 + t)).im = (1 + z).arg - 2 * (1 + t).arg := by
    simp [log_im]
  rw [cpow_eq_exp_of_exp_eq hexp (by rw [him]; rcases hsame with h | h <;> nlinarith)
      (by rw [him]; rcases hsame with h | h <;> nlinarith),
    cpow_def_of_ne_zero h2, cpow_def_of_ne_zero h1, ← exp_add]
  congr 1
  ring

/-- Identity under the stated parameter and domain assumptions: `₂F₁ a b (a - b + 1) z = (1 + z ^
(1 / 2 : ℂ)) ^ (-2 * a) * ₂F₁ a (a - b + 1 / 2) (2 * a - 2 * b + 1) (4 * z ^ (1 / 2 : ℂ) / (1
+ z ^ (1 / 2 : ℂ)) ^ 2)`. -/
@[dlmf 15.8.E21]
theorem quadratic_sqrt
    {a b z : ℂ}
    (hc : ∀ k : ℕ, a - b + 1 ≠ -(k : ℂ))
    (ht : ∀ k : ℕ, 2 * a - 2 * b + 1 ≠ -(k : ℂ))
    (hz : ‖z‖ < 1)
    (hs : z ∈ slitPlane)
    (hw : ‖4 * z ^
    (1 / 2 : ℂ) /
    (1 + z ^
    (1 / 2 : ℂ)) ^ 2‖ < 1) :
    ₂F₁ a b (a - b + 1) z =
      (1 + z ^ (1 / 2 : ℂ)) ^ (-2 * a) * ₂F₁ a (a - b + 1 / 2) (2 * a - 2 * b + 1) (4 * z ^ (1 / 2 : ℂ) / (1
        + z ^ (1 / 2 : ℂ)) ^ 2) := by
  set t := z ^ (1 / 2 : ℂ) with htdef
  have htre : 0 < t.re := re_cpow_half_pos_of_mem_slitPlane hs
  have hz0 : z ≠ 0 := slitPlane_ne_zero hs
  have htsq : t ^ 2 = z := cpow_half_sq hz0
  have h1t : 1 + t ≠ 0 := by
    intro h; have := congrArg re h; simp at this; linarith
  have h1z : 1 + z ≠ 0 := by
    intro h; have : z = -1 := by linear_combination h
    rw [this] at hz; simp at hz
  set z' := 4 * t / (1 + t) ^ 2 with hz'
  have hz'n : ‖z'‖ < 1 := hw
  have h2z' : 2 - z' ≠ 0 := by
    intro h; have : z' = 2 := by linear_combination -h
    rw [this] at hz'n; norm_num at hz'n
  have hsq : (z' / (2 - z')) ^ 2 = 4 * z / (1 + z) ^ 2 := by
    have e : 2 - z' = 2 * (1 + z) / (1 + t) ^ 2 := by
      rw [hz', ← htsq]; field_simp; ring
    rw [e, hz', ← htsq]
    field_simp
    ring
  have hw15 : ‖4 * z / (1 + z) ^ 2‖ < 1 := by
    rw [← hsq]
    have h2 : 1 < ‖2 - z'‖ := by
      have := norm_sub_norm_le (2 : ℂ) z'
      rw [show ‖(2 : ℂ)‖ = 2 by norm_num] at this
      linarith
    rw [norm_pow, norm_div]
    have : ‖z'‖ / ‖2 - z'‖ < 1 := by rw [div_lt_one (by linarith)]; linarith
    have h0 : 0 ≤ ‖z'‖ / ‖2 - z'‖ := by positivity
    nlinarith
  have h13 := quadratic_double_denominator (a := a) (b := a - b + 1 / 2) (z := z')
    (by rw [show 2 * (a - b + 1 / 2) = 2 * a - 2 * b + 1 by ring]; exact ht)
    (by rw [show a - b + 1 / 2 + 1 / 2 = a - b + 1 by ring]; exact hc) hz'n
  rw [show 2 * (a - b + 1 / 2) = 2 * a - 2 * b + 1 by ring,
    show a - b + 1 / 2 + 1 / 2 = a - b + 1 by ring, hsq] at h13
  have h1z' : 1 - z' / 2 = (1 + z) / (1 + t) ^ 2 := by
    rw [hz', ← htsq]; field_simp; ring
  rw [h13, quadratic_well_poised_plus hc hz hw15, h1z', ← mul_assoc,
    phase_quadratic_sqrt hz hs]

/-- Complex powers of a positive real through the real logarithm. -/
theorem ofReal_cpow_eq_exp_log {u : ℝ} (hu : 0 < u) (s : ℂ) :
    (u : ℂ) ^ s = exp (Real.log u * s) := by
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hu.ne'), ofReal_log hu.le]

/-- Data for the real quadratic transformations on `(-1, 0)`. -/
theorem reciprocal_sqrt_data {x : ℝ} (hx : -1 < x) (hx0 : x < 0) :
    2 < 1 - 1 / x ∧ 1 < Real.sqrt (1 - 1 / x) ∧
      Real.sqrt (1 - 1 / x) ^ 2 = 1 - 1 / x ∧ x / (x - 1) = 1 / (1 - 1 / x) := by
  have hq : 2 < 1 - 1 / x := by
    have : 1 / x < -1 := by
      rw [div_lt_iff_of_neg hx0]; linarith
    linarith
  have hsq : Real.sqrt (1 - 1 / x) ^ 2 = 1 - 1 / x := Real.sq_sqrt (by linarith)
  refine ⟨hq, ?_, hsq, ?_⟩
  · exact (Real.lt_sqrt (by norm_num)).mpr (by linarith)
  · have : x - 1 ≠ 0 := by linarith
    have : x ≠ 0 := by linarith
    field_simp

/-- Identity under the stated parameter and domain assumptions: `₂F₁ a b ((a + b + 1) / 2) (x : ℂ)
= ((((1 - 1 / x).sqrt - 1) / ((1 - 1 / x).sqrt + 1) : ℝ) : ℂ) ^ a * ₂F₁ a ((a + b) / 2) (a +
b) ((4 * (1 - 1 / x).sqrt / ((1 - 1 / x).sqrt + 1) ^ 2 : ℝ) : ℂ)`. -/
@[dlmf 15.8.E22]
theorem quadratic_reciprocal_sqrt
    {a b : ℂ}
    {x : ℝ}
    (hc : ∀ k : ℕ,
    (a + b + 1) / 2 ≠ -(k : ℂ))
    (ht : ∀ k : ℕ, a + b ≠ -(k : ℂ))
    (hx : -1 < x)
    (hx0 : x < 0) :
    ₂F₁ a b ((a + b + 1) / 2) (x : ℂ) =
      ((((1 - 1 / x).sqrt - 1) / ((1 - 1 / x).sqrt + 1) : ℝ) : ℂ) ^ a * ₂F₁ a ((a + b) / 2) (a + b) ((4 * (1
        - 1 / x).sqrt / ((1 - 1 / x).sqrt + 1) ^ 2 : ℝ) : ℂ) := by
  obtain ⟨hq, hr1, hrsq, hy⟩ := reciprocal_sqrt_data hx hx0
  set q := 1 - 1 / x with hqdef
  set r := Real.sqrt q with hrdef
  have hr0 : 0 < r := by linarith
  set y : ℝ := x / (x - 1) with hydef
  have hy0 : 0 < y := by rw [hy]; positivity
  have hy1 : y < 1 := by rw [hy, div_lt_one (by linarith)]; linarith
  have hxn : ‖(x : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_lt]; constructor <;> linarith
  have hyC : (x : ℂ) / ((x : ℂ) - 1) = (y : ℂ) := by push_cast [hydef]; ring
  have hyn : ‖(y : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy0]; exact hy1
  have hys : (y : ℂ) ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inl (by simpa using hy0))
  have hsqrt : (y : ℂ) ^ (1 / 2 : ℂ) = ((1 / r : ℝ) : ℂ) := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow hy0.le,
      ← Real.sqrt_eq_rpow, hy, Real.sqrt_div' _ (by linarith : (0 : ℝ) ≤ q), Real.sqrt_one]
  have harg : 4 * (y : ℂ) ^ (1 / 2 : ℂ) / (1 + (y : ℂ) ^ (1 / 2 : ℂ)) ^ 2 =
      ((4 * r / (r + 1) ^ 2 : ℝ) : ℂ) := by
    rw [hsqrt]
    have hr' : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr0.ne'
    have hr1' : (r : ℂ) + 1 ≠ 0 := by
      rw [← ofReal_one, ← ofReal_add, ofReal_ne_zero]; linarith
    push_cast
    field_simp
  have hargn : ‖4 * (y : ℂ) ^ (1 / 2 : ℂ) / (1 + (y : ℂ) ^ (1 / 2 : ℂ)) ^ 2‖ < 1 := by
    rw [harg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity),
      div_lt_one (by positivity)]
    nlinarith
  have h21 := quadratic_sqrt (a := a) (b := (a - b + 1) / 2) (z := (y : ℂ))
    (by rw [show a - (a - b + 1) / 2 + 1 = (a + b + 1) / 2 by ring]; exact hc)
    (by rw [show 2 * a - 2 * ((a - b + 1) / 2) + 1 = a + b by ring]; exact ht) hyn hys hargn
  rw [show a - (a - b + 1) / 2 + 1 = (a + b + 1) / 2 by ring,
    show a - (a - b + 1) / 2 + 1 / 2 = (a + b) / 2 by ring,
    show 2 * a - 2 * ((a - b + 1) / 2) + 1 = a + b by ring, harg, hsqrt] at h21
  rw [pfaff_transformation_of_ne_neg_nat hc hxn (by rw [hyC]; exact hyn), hyC,
    show (a + b + 1) / 2 - b = (a - b + 1) / 2 by ring, h21, ← mul_assoc]
  congr 1
  have h1x : 0 < 1 - x := by linarith
  have hrm : 0 < r - 1 := by linarith
  rw [show (1 : ℂ) - (x : ℂ) = ((1 - x : ℝ) : ℂ) by push_cast; ring,
    show (1 : ℂ) + ((1 / r : ℝ) : ℂ) = ((1 + 1 / r : ℝ) : ℂ) by push_cast; ring,
    ofReal_cpow_eq_exp_log h1x, ofReal_cpow_eq_exp_log (by positivity),
    ofReal_cpow_eq_exp_log (by positivity : (0 : ℝ) < (r - 1) / (r + 1)), ← exp_add]
  congr 1
  have e1 : 1 - x = r ^ 2 / ((r - 1) * (r + 1)) := by
    have hx' : x ≠ 0 := by linarith
    rw [show (r - 1) * (r + 1) = r ^ 2 - 1 by ring, hrsq, hqdef]
    field_simp
    ring
  have e2 : 1 + 1 / r = (r + 1) / r := by field_simp
  rw [e1, e2, Real.log_div (by positivity) (by positivity), Real.log_mul hrm.ne' (by positivity),
    Real.log_div (by positivity) hr0.ne', Real.log_div hrm.ne' (by positivity),
    Real.log_pow]
  push_cast
  ring

/-- Identity under the stated parameter and domain assumptions: `₂F₁ a (1 - a) c (x : ℂ) = (((1 -
1 / x).sqrt - 1 : ℝ) : ℂ) ^ (1 - a) * (((1 - 1 / x).sqrt + 1 : ℝ) : ℂ) ^ (a - 2 * c + 1) * ((1
- 1 / x : ℝ) : ℂ) ^ (c - 1) * ₂F₁ (c - a) (c - 1 / 2) (2 * c - 1) ((4 * (1 - 1 / x).sqrt / ((1
- 1 / x).sqrt + 1) ^ 2 : ℝ) : ℂ)`. -/
@[dlmf 15.8.E23]
theorem quadratic_reciprocal_sqrt_complementary
    {a c : ℂ}
    {x : ℝ}
    (hc : ∀ k : ℕ, c ≠ -(k : ℂ))
    (ht : ∀ k : ℕ, 2 * c - 1 ≠ -(k : ℂ))
    (hx : -1 < x)
    (hx0 : x < 0) :
    ₂F₁ a (1 - a) c (x : ℂ) =
      (((1 - 1 / x).sqrt - 1 : ℝ) : ℂ) ^ (1 - a) * (((1 - 1 / x).sqrt + 1 : ℝ) : ℂ) ^ (a - 2 * c + 1) * ((1
        - 1 / x : ℝ) : ℂ) ^ (c - 1) * ₂F₁ (c - a) (c - 1 / 2) (2 * c - 1) ((4 * (1 - 1 / x).sqrt / ((1 - 1 /
        x).sqrt + 1) ^ 2 : ℝ) : ℂ) := by
  obtain ⟨hq, hr1, hrsq, hy⟩ := reciprocal_sqrt_data hx hx0
  set q := 1 - 1 / x with hqdef
  set r := Real.sqrt q with hrdef
  have hxn : ‖(x : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_lt]; constructor <;> linarith
  have h22 := quadratic_reciprocal_sqrt (a := c - a) (b := c + a - 1)
    (by rw [show (c - a + (c + a - 1) + 1) / 2 = c by ring]; exact hc)
    (by rw [show c - a + (c + a - 1) = 2 * c - 1 by ring]; exact ht) hx hx0
  rw [show (c - a + (c + a - 1) + 1) / 2 = c by ring,
    show (c - a + (c + a - 1)) / 2 = c - 1 / 2 by ring,
    show c - a + (c + a - 1) = 2 * c - 1 by ring] at h22
  rw [euler_transformation_of_ne_neg_nat hc hxn, show c - a - (1 - a) = c - 1 by ring,
    show c - (1 - a) = c + a - 1 by ring, h22, ← mul_assoc]
  congr 1
  have hr0 : 0 < r := by linarith
  have hrm : 0 < r - 1 := by linarith
  have h1x : 0 < 1 - x := by linarith
  rw [show (1 : ℂ) - (x : ℂ) = ((1 - x : ℝ) : ℂ) by push_cast; ring,
    ofReal_cpow_eq_exp_log h1x, ofReal_cpow_eq_exp_log (by positivity : (0 : ℝ) < (r - 1) / (r + 1)),
    ofReal_cpow_eq_exp_log hrm, ofReal_cpow_eq_exp_log (by positivity : (0 : ℝ) < r + 1),
    ofReal_cpow_eq_exp_log (by linarith : (0 : ℝ) < q), ← exp_add, ← exp_add, ← exp_add]
  congr 1
  have e1 : 1 - x = q / ((r - 1) * (r + 1)) := by
    have hx' : x ≠ 0 := by linarith
    rw [show (r - 1) * (r + 1) = r ^ 2 - 1 by ring, hrsq, hqdef]
    field_simp
    ring
  rw [e1, Real.log_div (by linarith) (by positivity), Real.log_mul hrm.ne' (by positivity),
    Real.log_div hrm.ne' (by positivity)]
  push_cast
  ring

/-- `exp L` lies in the slit plane when `|Im L| < π`. -/
theorem exp_mem_slitPlane_of_im_mem {L : ℂ} (h1 : -Real.pi < L.im) (h2 : L.im < Real.pi) : exp L ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  by_cases hs : Real.sin L.im = 0
  · left
    have : L.im = 0 := by
      rcases Real.sin_eq_zero_iff_of_lt_of_lt h1 h2 |>.mp hs with h
      exact h
    rw [exp_re, this, Real.cos_zero, mul_one]
    exact Real.exp_pos _
  · right
    rw [exp_im]
    exact mul_ne_zero (Real.exp_pos _).ne' hs

/-- Arguments of two points with the same imaginary part, the second further right. -/
theorem arg_le_arg_of_im_eq {p q : ℂ} (hq : 0 < q.re) (hpq : q.re ≤ p.re) (him : p.im = q.im)
    (hy : 0 ≤ p.im) : 0 ≤ p.arg ∧ p.arg ≤ q.arg := by
  have hp : 0 < p.re := lt_of_lt_of_le hq hpq
  rw [arg_of_re_nonneg hp.le, arg_of_re_nonneg hq.le]
  have hnp : 0 < ‖p‖ := norm_pos_iff.mpr (by rintro rfl; simp at hp)
  have hnq : 0 < ‖q‖ := norm_pos_iff.mpr (by rintro rfl; simp at hq)
  have hle : ‖q‖ ≤ ‖p‖ := by
    rw [← sq_le_sq₀ hnq.le hnp.le, ← normSq_eq_norm_sq, ← normSq_eq_norm_sq, normSq_apply,
      normSq_apply, him]
    nlinarith
  constructor
  · exact Real.arcsin_nonneg.mpr (div_nonneg hy hnp.le)
  · apply Real.arcsin_le_arcsin
    rw [him]
    exact div_le_div_of_nonneg_left (by rw [← him]; exact hy) hnq hle

/-- The cubic map sends the half-plane `Re z < 8/9` into the cut plane. -/
theorem cubic_map_mem_cutPlane {z : ℂ} (hr : z.re < 8 / 9) :
    27 * z ^ 2 * (z - 1) / (9 * z - 8) ^ 2 ∈ cutPlane := by
  rw [mem_cutPlane]
  set p : ℂ := 4 / 3 - z with hp
  set q : ℂ := 8 / 9 - z with hq
  have hqre : 0 < q.re := by simp [hq]; linarith
  have hpq : q.re ≤ p.re := by simp [hp, hq]; norm_num
  have him : p.im = q.im := by simp [hp, hq]
  have hp0 : p ≠ 0 := by intro h; rw [h] at hpq; simp at hpq; linarith
  have hq0 : q ≠ 0 := by intro h; rw [h] at hqre; simp at hqre
  have h98 : 9 * z - 8 ≠ 0 := by
    intro h; apply hq0; rw [hq]; linear_combination -h / 9
  have hval : 1 - 27 * z ^ 2 * (z - 1) / (9 * z - 8) ^ 2 =
      (1 / 3 : ℝ) * exp (3 * log p - 2 * log q) := by
    have he : exp (3 * log p - 2 * log q) = p ^ 3 / q ^ 2 := by
      rw [exp_sub, show (3 : ℂ) * log p = ((3 : ℕ) : ℂ) * log p by norm_num, exp_nat_mul,
        exp_log hp0, show (2 : ℂ) * log q = ((2 : ℕ) : ℂ) * log q by norm_num, exp_nat_mul,
        exp_log hq0]
    rw [he]
    have hzq : z = 8 / 9 - q := by rw [hq]; ring
    have hpq' : p = 4 / 9 + q := by rw [hp, hq]; ring
    rw [hpq', hzq, show 9 * (8 / 9 - q) - 8 = -(9 * q) by ring]
    push_cast
    field_simp
    ring
  rw [hval]
  have hL : -Real.pi < (3 * log p - 2 * log q).im ∧ (3 * log p - 2 * log q).im < Real.pi := by
    have him' : (3 * log p - 2 * log q).im = 3 * p.arg - 2 * q.arg := by
      simp [log_im]
    rw [him']
    have hq2 : |q.arg| < Real.pi / 2 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hqre)
    rw [abs_lt] at hq2
    rcases le_total 0 p.im with hy | hy
    · obtain ⟨h1, h2⟩ := arg_le_arg_of_im_eq hqre hpq him hy
      constructor <;> linarith
    · have hc := arg_le_arg_of_im_eq (p := conj p) (q := conj q) (by simpa using hqre)
        (by simpa using hpq) (by simp [him]) (by simp; linarith)
      have hpc : (conj p).arg = -p.arg := by
        rw [arg_conj]; split_ifs with h
        · exfalso; have := (arg_eq_pi_iff.mp h).1; linarith
        · rfl
      have hqc : (conj q).arg = -q.arg := by
        rw [arg_conj]; split_ifs with h
        · exfalso; have := (arg_eq_pi_iff.mp h).1; linarith
        · rfl
      rw [hpc, hqc] at hc
      obtain ⟨h1, h2⟩ := hc
      constructor <;> linarith
  have hexp := exp_mem_slitPlane_of_im_mem hL.1 hL.2
  rw [mem_slitPlane_iff] at hexp ⊢
  rcases hexp with h | h
  · left; simp; positivity
  · right; simp; exact h

/-- Identity under the stated parameter and domain assumptions: `₂F₁ (3 * a) (3 * a + 1 / 2) (4 *
a + 2 / 3) z = (1 - 9 * z / 8) ^ (-2 * a) * ₂F₁ a (a + 1 / 2) (2 * a + 5 / 6) (27 * z ^ 2 * (z
- 1) / (9 * z - 8) ^ 2)`. -/
@[dlmf 15.8.E31]
theorem cubic_transformation
    {a z : ℂ}
    (hc : ∀ k : ℕ, 4 * a + 2 / 3 ≠ -(k : ℂ))
    (ht : ∀ k : ℕ, 2 * a + 5 / 6 ≠ -(k : ℂ))
    (hz : ‖z‖ < 1)
    (hr : z.re < 8 / 9)
    (hw : ‖27 * z ^ 2 *
    (z - 1) /
    (9 * z - 8) ^ 2‖ < 1) :
    ₂F₁ (3 * a) (3 * a + 1 / 2) (4 * a + 2 / 3) z =
      (1 - 9 * z / 8) ^ (-2 * a) * ₂F₁ a (a + 1 / 2) (2 * a + 5 / 6) (27 * z ^ 2 * (z - 1) / (9 * z - 8) ^
        2) := by
  set H : ℂ → ℂ := ₂F₁ a (a + 1 / 2) (2 * a + 5 / 6) with hH
  set P : ℂ → ℂ := fun w => (1 + (-9 / 8) * w) ^ (-2 * a) with hP
  set φ : ℂ → ℂ := fun w => 27 * w ^ 2 * (w - 1) / (9 * w - 8) ^ 2 with hφdef
  have hsmall : ∀ w ∈ Metric.ball (0 : ℂ) (1 / 4), ‖w‖ < 1 / 4 := fun w hw => by simpa using hw
  have h98 : ∀ w : ℂ, w.re < 8 / 9 → 9 * w - 8 ≠ 0 := by
    intro w hw h
    have := congrArg re h
    simp at this; linarith
  have hslit : ∀ w : ℂ, w.re < 8 / 9 → 1 + (-9 / 8) * w ∈ slitPlane := by
    intro w hw
    refine mem_slitPlane_iff.mpr (Or.inl ?_)
    simp; linarith
  have hre : ∀ w : ℂ, ‖w‖ < 1 / 4 → w.re < 8 / 9 := fun w hw => by
    have := re_le_norm w; linarith
  have hφn : ∀ w : ℂ, ‖w‖ < 1 / 4 → ‖φ w‖ < 1 := by
    intro w hw
    have h1 : 23 / 4 ≤ ‖9 * w - 8‖ := by
      have := norm_sub_norm_le (8 : ℂ) (9 * w)
      rw [norm_sub_rev] at this
      rw [show ‖(8 : ℂ)‖ = 8 by norm_num, norm_mul, show ‖(9 : ℂ)‖ = 9 by norm_num] at this
      linarith
    have h2 : ‖w - 1‖ ≤ 5 / 4 := by
      have := norm_sub_le w 1; rw [norm_one] at this; linarith
    simp only [hφdef, norm_div, norm_mul, norm_pow, show ‖(27 : ℂ)‖ = 27 by norm_num]
    rw [div_lt_one (by positivity)]
    have hw0 := norm_nonneg w
    have : ‖w‖ ^ 2 ≤ 1 / 16 := by nlinarith
    calc 27 * ‖w‖ ^ 2 * ‖w - 1‖ ≤ 27 * (1 / 16) * (5 / 4) := by gcongr
      _ < (23 / 4) ^ 2 := by norm_num
      _ ≤ ‖9 * w - 8‖ ^ 2 := by gcongr
  have hPa : ∀ w : ℂ, w.re < 8 / 9 → AnalyticAt ℂ P w := fun w hw =>
    (analyticAt_const.add (analyticAt_const.mul analyticAt_id)).cpow analyticAt_const (hslit w hw)
  have hφa : ∀ w : ℂ, w.re < 8 / 9 → AnalyticAt ℂ φ w := fun w hw =>
    ((analyticAt_const.mul (analyticAt_id.pow 2)).mul (analyticAt_id.sub analyticAt_const)).div
      (((analyticAt_const.mul analyticAt_id).sub analyticAt_const).pow 2) (pow_ne_zero 2 (h98 w hw))
  have hφd : ∀ w : ℂ, w.re < 8 / 9 → HasDerivAt φ (27 * w * (3 * w - 4) ^ 2 / (9 * w - 8) ^ 3) w := by
    intro w hw
    have h := ((((hasDerivAt_id w).pow 2).const_mul 27).mul ((hasDerivAt_id w).sub_const 1)).div
      ((((hasDerivAt_id w).const_mul 9).sub_const 8).pow 2) (pow_ne_zero 2 (h98 w hw))
    refine h.congr_deriv ?_
    have := h98 w hw
    simp only [id, Pi.pow_apply, Pi.mul_apply, Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    rw [div_eq_div_iff (pow_ne_zero _ (pow_ne_zero _ this)) (pow_ne_zero _ this)]
    ring
  have hφdd : ∀ w : ℂ, w.re < 8 / 9 → deriv (deriv φ) w = 864 * (3 * w - 4) / (9 * w - 8) ^ 4 := by
    intro w hw
    have hev : deriv φ =ᶠ[𝓝 w] fun v => 27 * v * (3 * v - 4) ^ 2 / (9 * v - 8) ^ 3 := by
      have hopen : IsOpen {v : ℂ | v.re < 8 / 9} := isOpen_lt continuous_re continuous_const
      filter_upwards [hopen.mem_nhds hw] with v hv
      exact (hφd v hv).deriv
    rw [hev.deriv_eq]
    have h := (((hasDerivAt_id w).const_mul 27).mul ((((hasDerivAt_id w).const_mul 3).sub_const
      4).pow 2)).div ((((hasDerivAt_id w).const_mul 9).sub_const 8).pow 3)
      (pow_ne_zero 3 (h98 w hw))
    have h' : HasDerivAt (fun v => 27 * v * (3 * v - 4) ^ 2 / (9 * v - 8) ^ 3) _ w := h
    rw [h'.deriv]
    have := h98 w hw
    simp only [id, Pi.pow_apply, Pi.mul_apply, Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl,
      show (3 : ℕ) - 1 = 2 from rfl, pow_one]
    rw [div_eq_div_iff (pow_ne_zero _ (pow_ne_zero _ this)) (pow_ne_zero _ this)]
    ring
  have hG : ∀ w ∈ Metric.ball (0 : ℂ) (1 / 4), (fun v => P v * H (φ v)) w =
      ₂F₁ (3 * a) (3 * a + 1 / 2) (4 * a + 2 / 3) w := by
    refine eq_ordinaryHypergeometric_of_gaussOperator hc (by norm_num) (by norm_num) ?_ ?_ ?_
    · intro w hw
      have hw1 := hsmall w hw
      exact (hPa w (hre w hw1)).mul ((analyticAt_ordinaryHypergeometric (hφn w hw1)).comp
        (f := φ) (hφa w (hre w hw1)))
    · intro w hw
      have hw1 := hsmall w hw
      have hwr := hre w hw1
      have hHa : AnalyticAt ℂ H (φ w) := analyticAt_ordinaryHypergeometric (hφn w hw1)
      rw [gaussOperator_mul_comp (hPa w hwr) (hφa w hwr) hHa,
        show deriv P w = _ from deriv_affine_cpow (hslit w hwr),
        show deriv (deriv P) w = _ from deriv_deriv_affine_cpow (hslit w hwr),
        (hφd w hwr).deriv, hφdd w hwr]
      have hode := gaussOperator_ordinaryHypergeometric (a := a) (b := a + 1 / 2) ht (hφn w hw1)
      simp only [gaussOperator] at hode
      have h9 := h98 w hwr
      have h1 : 1 + (-9 / 8) * w ≠ 0 := slitPlane_ne_zero (hslit w hwr)
      have key : w * (1 - w) * (-2 * a * (-2 * a - 1) * (-9 / 8) ^ 2 * (1 + -9 / 8 * w) ^ (-2 * a) /
            (1 + -9 / 8 * w) ^ 2 * H (φ w) +
          2 * (-2 * a * (-9 / 8) * (1 + -9 / 8 * w) ^ (-2 * a) / (1 + -9 / 8 * w)) *
            (deriv H (φ w) * (27 * w * (3 * w - 4) ^ 2 / (9 * w - 8) ^ 3)) +
          P w * (iteratedDeriv 2 H (φ w) * (27 * w * (3 * w - 4) ^ 2 / (9 * w - 8) ^ 3) ^ 2 +
            deriv H (φ w) * (864 * (3 * w - 4) / (9 * w - 8) ^ 4))) +
          (4 * a + 2 / 3 - (3 * a + (3 * a + 1 / 2) + 1) * w) *
            (-2 * a * (-9 / 8) * (1 + -9 / 8 * w) ^ (-2 * a) / (1 + -9 / 8 * w) * H (φ w) +
              P w * (deriv H (φ w) * (27 * w * (3 * w - 4) ^ 2 / (9 * w - 8) ^ 3))) -
          3 * a * (3 * a + 1 / 2) * (P w * H (φ w)) =
          P w * 27 * w * (3 * w - 4) / (9 * w - 8) ^ 2 *
            (φ w * (1 - φ w) * iteratedDeriv 2 H (φ w) +
              (2 * a + 5 / 6 - (a + (a + 1 / 2) + 1) * φ w) * deriv H (φ w) -
              a * (a + 1 / 2) * H (φ w)) := by
        simp only [hP]
        generalize H (φ w) = h0
        generalize deriv H (φ w) = h1
        generalize iteratedDeriv 2 H (φ w) = h2
        generalize (1 + -9 / 8 * w) ^ (-2 * a) = pw
        simp only [hφdef]
        obtain ⟨u, hu⟩ : ∃ u, u = 9 * w - 8 := ⟨_, rfl⟩
        have hwu : w = (u + 8) / 9 := by rw [hu]; ring
        have hu0 : u ≠ 0 := by rw [hu]; exact h9
        rw [show (1 : ℂ) + -9 / 8 * w = -u / 8 by rw [hu]; ring, ← hu]
        subst hwu
        field_simp
        ring
      rw [key, hode, mul_zero]
    · simp [hP, hφdef, hH, ordinaryHypergeometric_zero]
  -- extension to `‖w‖ < 1, Re w < 8/9` through the cut-plane continuation
  set c₂ := 2 * a + 5 / 6 with hc₂
  set R : ℂ → ℂ := fun w => P w * (Gamma c₂ * regularizedGaussHG a (a + 1 / 2) c₂ (φ w)) with hR
  set A : Set ℂ := {w | ‖w‖ < 1 ∧ w.re < 8 / 9} with hA
  have hAc : IsPreconnected A := by
    have : A = Metric.ball (0 : ℂ) 1 ∩ {w | w.re < 8 / 9} := by
      ext w; simp [hA]
    rw [this]
    exact ((convex_ball (0 : ℂ) 1).inter (convex_halfSpace_re_lt (8 / 9))).isPreconnected
  have hRe : ∀ w : ℂ, ‖φ w‖ < 1 → R w = P w * H (φ w) := by
    intro w hw
    simp only [hR, hH]
    rw [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hw, regularizedGaussHGFun_eq_div_Gamma ht,
      mul_div_cancel₀ _ (Gamma_ne_zero ht)]
  have hLan : AnalyticOnNhd ℂ (₂F₁ (3 * a) (3 * a + 1 / 2) (4 * a + 2 / 3) : ℂ → ℂ) A :=
    fun w hw => analyticAt_ordinaryHypergeometric hw.1
  have hRan : AnalyticOnNhd ℂ R A := fun w hw =>
    (hPa w hw.2).mul (analyticAt_const.mul ((analyticAt_regularizedGaussHG _ _ _
      (cubic_map_mem_cutPlane hw.2)).comp (f := φ) (hφa w hw.2)))
  have h0A : (0 : ℂ) ∈ A := by simp [hA]
  have hev : (₂F₁ (3 * a) (3 * a + 1 / 2) (4 * a + 2 / 3) : ℂ → ℂ) =ᶠ[𝓝 0] R := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 4)] with w hw
    rw [hRe w (hφn w (hsmall w hw))]
    exact (hG w hw).symm
  have hEq := hLan.eqOn_of_preconnected_of_eventuallyEq hRan hAc h0A hev ⟨hz, hr⟩
  rw [hEq, hRe z hw]
  simp only [hP, hφdef, hH]
  rw [show (1 : ℂ) - 9 * z / 8 = 1 + -9 / 8 * z by ring]

/-- Second derivative of a composition, for analytic data. -/
theorem deriv_deriv_comp {φ F : ℂ → ℂ} {z : ℂ} (hφ : AnalyticAt ℂ φ z)
    (hF : AnalyticAt ℂ F (φ z)) :
    deriv (deriv (fun w => F (φ w))) z =
      iteratedDeriv 2 F (φ z) * deriv φ z ^ 2 + deriv F (φ z) * deriv (deriv φ) z := by
  have hev : deriv (fun w => F (φ w)) =ᶠ[𝓝 z] fun w => deriv F (φ w) * deriv φ w := by
    filter_upwards [hφ.eventually_analyticAt,
      hφ.continuousAt.tendsto.eventually hF.eventually_analyticAt] with w h1 h2
    exact (h2.differentiableAt.hasDerivAt.comp w h1.differentiableAt.hasDerivAt).deriv
  rw [hev.deriv_eq]
  have h := (hF.deriv.differentiableAt.hasDerivAt.comp z hφ.differentiableAt.hasDerivAt).mul
    hφ.deriv.differentiableAt.hasDerivAt
  have h' : HasDerivAt (fun w => deriv F (φ w) * deriv φ w) _ z := h
  rw [h'.deriv]
  simp only [iteratedDeriv_succ, iteratedDeriv_zero, Function.comp_apply]
  ring

/-- The principal cube root has positive real part. -/
theorem re_cpow_third_pos {x : ℂ} (hx : x ≠ 0) : 0 < (x ^ (1 / 3 : ℂ)).re := by
  rw [cpow_def_of_ne_zero hx, exp_re]
  refine mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩)
  · have := neg_pi_lt_arg x
    simp [log_im]
    nlinarith [Real.pi_pos]
  · have := arg_le_pi x
    simp [log_im]
    nlinarith [Real.pi_pos]

/-- `(x^{1/3})³ = x`. -/
theorem cpow_third_cube (x : ℂ) : (x ^ (1 / 3 : ℂ)) ^ 3 = x := by
  rw [← cpow_nat_mul]; norm_num

/-- `‖1 - t‖ < ‖1 + 2t‖` when `Re t > 0`. -/
theorem norm_one_sub_lt_norm_one_add_two_mul {t : ℂ} (ht : 0 < t.re) : ‖1 - t‖ < ‖1 + 2 * t‖ := by
  rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _), ← normSq_eq_norm_sq, ← normSq_eq_norm_sq,
    normSq_apply, normSq_apply]
  simp only [sub_re, one_re, sub_im, one_im, add_re, add_im, mul_re, mul_im, re_ofNat, im_ofNat]
  nlinarith [sq_nonneg t.im, sq_nonneg t.re]

/-- The cubic transformation of the Borweins for `₂F₁(1/3,2/3;1;·)`. -/
theorem borwein_cubic {v : ℂ} (hv : ‖v‖ < 1) :
    ₂F₁ (1 / 3 : ℂ) (2 / 3) 1 v = 3 / (1 + 2 * (1 - v) ^ (1 / 3 : ℂ)) *
      ₂F₁ (1 / 3 : ℂ) (2 / 3) 1 (((1 - (1 - v) ^ (1 / 3 : ℂ)) / (1 + 2 * (1 - v) ^ (1 / 3 : ℂ))) ^ 3) := by
  set H : ℂ → ℂ := ₂F₁ (1 / 3 : ℂ) (2 / 3) 1 with hH
  set S : ℂ → ℂ := fun v => (1 - v) ^ (1 / 3 : ℂ) with hS
  set p : ℂ → ℂ := fun t => 3 / (1 + 2 * t) with hp
  set ψ : ℂ → ℂ := fun t => ((1 - t) / (1 + 2 * t)) ^ 3 with hψ
  have hball : ∀ w ∈ Metric.ball (0 : ℂ) 1, ‖w‖ < 1 := fun w hw => by simpa using hw
  have h1v : ∀ w : ℂ, ‖w‖ < 1 → 1 - w ∈ slitPlane := by
    intro w hw
    refine mem_slitPlane_iff.mpr (Or.inl ?_)
    have := (re_le_norm w).trans_lt hw
    simp only [sub_re, one_re]; linarith
  have hSre : ∀ w : ℂ, ‖w‖ < 1 → 0 < (S w).re := fun w hw =>
    re_cpow_third_pos (slitPlane_ne_zero (h1v w hw))
  have h12 : ∀ t : ℂ, 0 < t.re → 1 + 2 * t ≠ 0 := by
    intro t ht h
    have := congrArg re h
    simp at this; linarith
  have hS0 : ∀ w : ℂ, ‖w‖ < 1 → S w ≠ 0 := fun w hw h => by
    have := hSre w hw; rw [h] at this; simp at this
  have hψn : ∀ t : ℂ, 0 < t.re → ‖ψ t‖ < 1 := by
    intro t ht
    simp only [hψ, norm_pow, norm_div]
    have h1 := norm_one_sub_lt_norm_one_add_two_mul ht
    have h2 : 0 < ‖1 + 2 * t‖ := norm_pos_iff.mpr (h12 t ht)
    have h3 : ‖1 - t‖ / ‖1 + 2 * t‖ < 1 := by rw [div_lt_one h2]; exact h1
    have h4 : 0 ≤ ‖1 - t‖ / ‖1 + 2 * t‖ := by positivity
    calc (‖1 - t‖ / ‖1 + 2 * t‖) ^ 3 < 1 ^ 3 := by gcongr
      _ = 1 := one_pow 3
  have hS3 : ∀ w : ℂ, S w ^ 3 = 1 - w := fun w => cpow_third_cube _
  -- derivatives of `S`
  have hSd : ∀ w : ℂ, ‖w‖ < 1 → HasDerivAt S (-1 / (3 * S w ^ 2)) w := by
    intro w hw
    have h := ((hasDerivAt_const w (1 : ℂ)).sub (hasDerivAt_id w)).cpow_const (c := 1 / 3) (h1v w hw)
    refine h.congr_deriv ?_
    have h0 := hS0 w hw
    have h1 : (1 - w) ≠ 0 := slitPlane_ne_zero (h1v w hw)
    simp only [id, Pi.sub_apply]
    rw [cpow_sub _ _ h1, cpow_one]
    have e : (1 - w) = S w ^ 3 := (hS3 w).symm
    simp only [hS] at h0 e ⊢
    generalize (1 - w) ^ (1 / 3 : ℂ) = s at h0 e ⊢
    rw [e]
    field_simp
    ring
  have hSa : ∀ w : ℂ, ‖w‖ < 1 → AnalyticAt ℂ S w := fun w hw =>
    (analyticAt_const.sub analyticAt_id).cpow analyticAt_const (h1v w hw)
  have hSdd : ∀ w : ℂ, ‖w‖ < 1 → deriv (deriv S) w = -2 / (9 * S w ^ 5) := by
    intro w hw
    have hopen : IsOpen {w : ℂ | ‖w‖ < 1} := isOpen_lt continuous_norm continuous_const
    have hev : deriv S =ᶠ[𝓝 w] fun v => -1 / (3 * S v ^ 2) := by
      filter_upwards [hopen.mem_nhds hw] with v hv
      exact (hSd v hv).deriv
    rw [hev.deriv_eq]
    have h0 := hS0 w hw
    have h := ((hSd w hw).pow 2).const_mul 3 |>.inv (by simpa using h0) |>.const_mul (-1)
    have h' : HasDerivAt (fun v => -1 / (3 * S v ^ 2)) (-2 / (9 * S w ^ 5)) w := by
      have h2 := h.congr_of_eventuallyEq (f₁ := fun v => -1 / (3 * S v ^ 2))
        (Eventually.of_forall fun v => by simp [div_eq_mul_inv])
      refine h2.congr_deriv ?_
      simp only [Pi.pow_apply, Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
      field_simp
      ring
    rw [h'.deriv]
  -- derivatives of `p` and `ψ`
  have hpd : ∀ t : ℂ, 1 + 2 * t ≠ 0 → HasDerivAt p (-6 / (1 + 2 * t) ^ 2) t := by
    intro t ht
    have h := (hasDerivAt_const t (3 : ℂ)).div (((hasDerivAt_id t).const_mul 2).const_add 1) ht
    refine h.congr_deriv ?_
    simp only [id]; field_simp; ring
  have hψd : ∀ t : ℂ, 1 + 2 * t ≠ 0 → HasDerivAt ψ (-9 * (1 - t) ^ 2 / (1 + 2 * t) ^ 4) t := by
    intro t ht
    have h := (((hasDerivAt_const t (1 : ℂ)).sub (hasDerivAt_id t)).div
      (((hasDerivAt_id t).const_mul 2).const_add 1) ht).pow 3
    refine h.congr_deriv ?_
    simp only [id, Pi.div_apply, Pi.sub_apply, Nat.cast_ofNat, show (3 : ℕ) - 1 = 2 from rfl]
    field_simp
    ring
  have hopen12 : IsOpen {t : ℂ | 1 + 2 * t ≠ 0} := isOpen_ne_fun (by fun_prop) continuous_const
  have hpdd : ∀ t : ℂ, 1 + 2 * t ≠ 0 → deriv (deriv p) t = 24 / (1 + 2 * t) ^ 3 := by
    intro t ht
    have hev : deriv p =ᶠ[𝓝 t] fun u => -6 / (1 + 2 * u) ^ 2 := by
      filter_upwards [hopen12.mem_nhds ht] with u hu
      exact (hpd u hu).deriv
    rw [hev.deriv_eq]
    have h := (hasDerivAt_const t (-6 : ℂ)).div ((((hasDerivAt_id t).const_mul 2).const_add 1).pow 2)
      (pow_ne_zero 2 ht)
    have h' : HasDerivAt (fun u => -6 / (1 + 2 * u) ^ 2) _ t := h
    rw [h'.deriv]
    simp only [id, Pi.pow_apply, Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    field_simp
    ring
  have hψdd : ∀ t : ℂ, 1 + 2 * t ≠ 0 →
      deriv (deriv ψ) t = 18 * (1 - t) * (5 - 2 * t) / (1 + 2 * t) ^ 5 := by
    intro t ht
    have hev : deriv ψ =ᶠ[𝓝 t] fun u => -9 * (1 - u) ^ 2 / (1 + 2 * u) ^ 4 := by
      filter_upwards [hopen12.mem_nhds ht] with u hu
      exact (hψd u hu).deriv
    rw [hev.deriv_eq]
    have h := ((((hasDerivAt_const t (1 : ℂ)).sub (hasDerivAt_id t)).pow 2).const_mul (-9)).div
      ((((hasDerivAt_id t).const_mul 2).const_add 1).pow 4) (pow_ne_zero 4 ht)
    have h' : HasDerivAt (fun u => -9 * (1 - u) ^ 2 / (1 + 2 * u) ^ 4) _ t := h
    rw [h'.deriv]
    simp only [id, Pi.pow_apply, Pi.sub_apply, Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl,
      show (4 : ℕ) - 1 = 3 from rfl, pow_one]
    field_simp
    ring
  have hpa : ∀ t : ℂ, 1 + 2 * t ≠ 0 → AnalyticAt ℂ p t := fun t ht =>
    analyticAt_const.div (analyticAt_const.add (analyticAt_const.mul analyticAt_id)) ht
  have hψa : ∀ t : ℂ, 1 + 2 * t ≠ 0 → AnalyticAt ℂ ψ t := fun t ht =>
    ((analyticAt_const.sub analyticAt_id).div
      (analyticAt_const.add (analyticAt_const.mul analyticAt_id)) ht).pow 3
  set Q : ℂ → ℂ := fun t => p t * H (ψ t) with hQ
  have hQa : ∀ t : ℂ, 0 < t.re → AnalyticAt ℂ Q t := fun t ht =>
    (hpa t (h12 t ht)).mul ((analyticAt_ordinaryHypergeometric (hψn t ht)).comp
      (f := ψ) (hψa t (h12 t ht)))
  have hc1 : ∀ k : ℕ, (1 : ℂ) ≠ -(k : ℂ) := fun k h => by
    have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hG := eq_ordinaryHypergeometric_of_gaussOperator (a := 1 / 3) (b := 2 / 3) hc1 one_pos le_rfl
    (g := fun v => Q (S v)) ?_ ?_ ?_ v (by simpa using hv)
  · exact hG.symm
  · intro w hw
    exact (hQa _ (hSre w (hball w hw))).comp (f := S) (hSa w (hball w hw))
  · intro w hw
    have hw1 := hball w hw
    set t := S w with ht
    have htre := hSre w hw1
    have ht12 := h12 t htre
    have ht0 := hS0 w hw1
    have hHa : AnalyticAt ℂ H (ψ t) := analyticAt_ordinaryHypergeometric (hψn t htre)
    have hd1 : deriv (fun v => Q (S v)) w = deriv Q t * deriv S w := by
      have hQd : HasDerivAt Q (deriv Q t) (S w) := (hQa t htre).differentiableAt.hasDerivAt
      have h := hQd.comp w (hSa w hw1).differentiableAt.hasDerivAt
      exact h.deriv
    have hd2 := deriv_deriv_comp (hSa w hw1) (hQa t htre)
    have hQ1 : deriv Q t = deriv p t * H (ψ t) + p t * (deriv H (ψ t) * deriv ψ t) :=
      (deriv_mul_comp_eventuallyEq (hpa t ht12) (hψa t ht12) hHa).eq_of_nhds
    have hQ2 : iteratedDeriv 2 Q t = deriv (deriv p) t * H (ψ t) +
        2 * deriv p t * (deriv H (ψ t) * deriv ψ t) +
        p t * (iteratedDeriv 2 H (ψ t) * deriv ψ t ^ 2 + deriv H (ψ t) * deriv (deriv ψ) t) := by
      rw [show iteratedDeriv 2 Q t = deriv (deriv Q) t by
        simp only [iteratedDeriv_succ, iteratedDeriv_zero]]
      exact deriv_deriv_mul_comp (hpa t ht12) (hψa t ht12) hHa
    simp only [gaussOperator]
    rw [show iteratedDeriv 2 (fun v => Q (S v)) w = deriv (deriv (fun v => Q (S v))) w by
      simp only [iteratedDeriv_succ, iteratedDeriv_zero], hd2, hd1, hQ2, hQ1,
      (hSd w hw1).deriv, hSdd w hw1, (hpd t ht12).deriv, hpdd t ht12, (hψd t ht12).deriv,
      hψdd t ht12]
    have hode : gaussOperator (1 / 3) (2 / 3) 1 H (ψ t) = 0 :=
      gaussOperator_ordinaryHypergeometric (a := 1 / 3) (b := 2 / 3) hc1 (hψn t htre)
    simp only [gaussOperator] at hode
    have hwt : w = 1 - t ^ 3 := by rw [hS3 w]; ring
    rw [← ht]
    have ht0' : t ≠ 0 := ht0
    clear_value t
    simp only [hQ]
    generalize H (ψ t) = h0 at hode ⊢
    generalize deriv H (ψ t) = h1 at hode ⊢
    generalize iteratedDeriv 2 H (ψ t) = h2 at hode ⊢
    simp only [hp, hψ] at hode ⊢
    rw [hwt]
    have hu : (1 + 2 * t) ≠ 0 := ht12
    obtain ⟨u, hu', rfl⟩ : ∃ u : ℂ, u ≠ 0 ∧ t = (u - 1) / 2 := ⟨1 + 2 * t, hu, by ring⟩
    have hu1 : u - 1 ≠ 0 := by intro h; apply ht0'; rw [h]; ring
    rw [show 1 + 2 * ((u - 1) / 2) = u by ring] at hode ⊢
    linear_combination (norm := skip) (3 * ((u - 1) / 2 - 1) ^ 2 / (((u - 1) / 2) ^ 2 * u ^ 3)) * hode
    field_simp
    ring
  · simp [hQ, hp, hψ, hS, hH, ordinaryHypergeometric_zero]
    norm_num

/-- Identity under the stated parameter and domain assumptions: `₂F₁ (1 / 3 : ℂ) (2 / 3) 1 (1 -
(((1 - x) / (1 + 2 * x) : ℝ) : ℂ) ^ 3) = (1 + 2 * (x : ℂ)) * ₂F₁ (1 / 3 : ℂ) (2 / 3) 1 ((x :
ℂ) ^ 3)`. -/
@[dlmf 15.8.E33]
theorem ramanujan_cubic {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    ₂F₁ (1 / 3 : ℂ) (2 / 3) 1 (1 - (((1 - x) / (1 + 2 * x) : ℝ) : ℂ) ^ 3) =
      (1 + 2 * (x : ℂ)) * ₂F₁ (1 / 3 : ℂ) (2 / 3) 1 ((x : ℂ) ^ 3) := by
  set r : ℝ := (1 - x) / (1 + 2 * x) with hr
  have h12 : 0 < 1 + 2 * x := by linarith
  have hr0 : 0 < r := div_pos (by linarith) h12
  have hr1 : r < 1 := by rw [hr, div_lt_one h12]; linarith
  have hv : ‖1 - (r : ℂ) ^ 3‖ < 1 := by
    rw [show 1 - (r : ℂ) ^ 3 = ((1 - r ^ 3 : ℝ) : ℂ) by push_cast; ring, norm_real, Real.norm_eq_abs]
    have : r ^ 3 < 1 := by
      calc r ^ 3 < 1 ^ 3 := by gcongr
        _ = 1 := one_pow 3
    have : 0 < r ^ 3 := by positivity
    rw [abs_lt]; constructor <;> linarith
  have hroot : (1 - (1 - (r : ℂ) ^ 3)) ^ (1 / 3 : ℂ) = r := by
    rw [sub_sub_cancel, show (r : ℂ) ^ 3 = ((r ^ 3 : ℝ) : ℂ) by push_cast; ring,
      show (1 / 3 : ℂ) = ((1 / 3 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow (by positivity),
      show (1 / 3 : ℝ) = ((3 : ℕ) : ℝ)⁻¹ by norm_num, Real.pow_rpow_inv_natCast hr0.le (by norm_num)]
  rw [borwein_cubic hv, hroot]
  have e1 : (3 : ℂ) / (1 + 2 * (r : ℂ)) = 1 + 2 * (x : ℂ) := by
    have : (1 + 2 * r) * (1 + 2 * x) = 3 := by rw [hr]; field_simp; ring
    have h1r : (1 + 2 * (r : ℂ)) ≠ 0 := by
      exact_mod_cast (show (1 + 2 * r : ℝ) ≠ 0 by linarith)
    rw [div_eq_iff h1r]
    exact_mod_cast (by linarith [this] : (3 : ℝ) = (1 + 2 * x) * (1 + 2 * r))
  have e2 : (1 - (r : ℂ)) / (1 + 2 * (r : ℂ)) = x := by
    have : (1 - r) / (1 + 2 * r) = x := by rw [hr]; field_simp; ring
    exact_mod_cast this
  rw [e1, e2]

attribute [dlmf 15.8.E29] quadratic_sqrt

end DLMF.Hypergeometric

end
end
