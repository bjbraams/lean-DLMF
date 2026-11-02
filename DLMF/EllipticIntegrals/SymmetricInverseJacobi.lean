/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.EllipticIntegrals.Symmetric
public import DLMF.JacobiElliptic.Inverse

/-!
# Inverse Jacobian functions as symmetric integrals (DLMF 19.25.32–19.25.34)

The inverse Jacobian elliptic functions of `DLMF.JacobiElliptic.Inverse` (real argument `x`,
real parameter `m = k² < 1`) as Carlson's `R_F` (DLMF §19.25(v)). Each formula follows from
the integral representation of the inverse function by an elementary substitution in the
integral defining `R_F`: `s = t² - x²` for `arcps` (19.25.32), `s = x²/t² - 1` for `arcsp`
(19.25.33), and `s = (t² - x²)/(1 - t²)` for `arcpq` (19.25.34).

## Main results

* `jacobiArcps_eq_symEllIntRF`, `jacobiArcps_eq_symEllIntRF'`: `arccs`, `arcds`, `arcns`
  (DLMF 19.25.32).
* `jacobiArcsp_eq_symEllIntRF`, `jacobiArcsp_eq_symEllIntRF'`: `arcsc`, `arcsd`, `arcsn`
  (DLMF 19.25.33).
* `jacobiArcpq_eq_symEllIntRF`: `arccd`, `arccn`, `arcdc`, `arcnc`, `arcdn`, `arcnd`
  (DLMF 19.25.34).

## Implementation notes

The ranges of `x` are those for which the integral representations hold; DLMF's statements for
real `x` of either sign are corrected to `x ≥ 0` where the left side is not even in `x`.

## References

* NIST DLMF §19.25(v).
-/

@[expose] public noncomputable section

open Complex Set MeasureTheory
open scoped Real

namespace DLMF.EllipticIntegrals

open DLMF.JacobiElliptic

/-- `r^{1/2} = √r` for real `r ≥ 0`. -/
private lemma ofReal_cpow_half_eq_sqrt {r : ℝ} (hr : 0 ≤ r) :
    (r : ℂ) ^ (1 / 2 : ℂ) = ((√r : ℝ) : ℂ) := by
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow hr,
    ← Real.sqrt_eq_rpow]

/-- The substitution `s = x²/t² - 1`: for `x > 0`,
`x R_F(1, 1 + a x², 1 + b x²) = ∫₀ˣ dt/√((1 + a t²)(1 + b t²))`. -/
private lemma mul_symEllIntRF_one_eq_integral_of_pos {x a b : ℝ} (hx : 0 < x)
    (ha : 0 ≤ 1 + a * x ^ 2) (hb : 0 ≤ 1 + b * x ^ 2) :
    (x : ℂ) * symEllIntRF 1 ((1 + a * x ^ 2 : ℝ) : ℂ) ((1 + b * x ^ 2 : ℝ) : ℂ) =
      ((∫ t in (0 : ℝ)..x, 1 / √((1 + a * t ^ 2) * (1 + b * t ^ 2)) : ℝ) : ℂ) := by
  set f : ℝ → ℝ := fun t => x ^ 2 / t ^ 2 - 1 with hf
  have hderiv : ∀ t ∈ Ioo 0 x, HasDerivWithinAt f (-(2 * x ^ 2 / t ^ 3)) (Ioo 0 x) t := by
    intro t ht
    have ht0 : t ≠ 0 := ht.1.ne'
    have h := (((hasDerivAt_pow 2 t).inv (pow_ne_zero 2 ht0)).const_mul (x ^ 2)).sub_const 1
    refine (h.congr_deriv ?_).hasDerivWithinAt.congr_of_mem (fun s _ => ?_) ht
    · field_simp; ring
    · simp [hf, div_eq_mul_inv]
  have hinj : InjOn f (Ioo 0 x) := by
    intro s hs t ht hst
    have hs0 := hs.1; have ht0 := ht.1
    simp only [hf, sub_left_inj] at hst
    field_simp at hst
    have : s ^ 2 = t ^ 2 := by nlinarith [sq_pos_of_pos hx]
    nlinarith [sq_nonneg (s - t), sq_nonneg (s + t)]
  have himg : f '' Ioo 0 x = Ioi 0 := by
    ext u; constructor
    · rintro ⟨t, ht, rfl⟩
      have h2 : t ^ 2 < x ^ 2 := pow_lt_pow_left₀ ht.2 ht.1.le two_ne_zero
      have ht2 : 0 < t ^ 2 := by have := ht.1; positivity
      simp only [hf, mem_Ioi, sub_pos]
      rw [lt_div_iff₀ ht2]; linarith
    · intro hu
      have hu : 0 < u := hu
      refine ⟨x / √(u + 1), ⟨by positivity, ?_⟩, ?_⟩
      · rw [div_lt_iff₀ (by positivity)]
        have : 1 < √(u + 1) := (Real.lt_sqrt zero_le_one).mpr (by linarith)
        nlinarith
      · simp only [hf]
        rw [div_pow, Real.sq_sqrt (by positivity)]
        field_simp
        ring
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj
    (fun t => (symEllIntS 1 ((1 + a * x ^ 2 : ℝ) : ℂ) ((1 + b * x ^ 2 : ℝ) : ℂ) t)⁻¹)
  rw [himg] at h
  rw [symEllIntRF, h, intervalIntegral.integral_of_le hx.le, integral_Ioc_eq_integral_Ioo,
    ← integral_complex_ofReal, ← integral_const_mul, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
  have ht0 : 0 < t := ht.1
  have h2 : t ^ 2 < x ^ 2 := pow_lt_pow_left₀ ht.2 ht.1.le two_ne_zero
  have hA : 0 < 1 + a * t ^ 2 := by
    rcases le_total 0 a with h | h
    · positivity
    · nlinarith
  have hB : 0 < 1 + b * t ^ 2 := by
    rcases le_total 0 b with h | h
    · positivity
    · nlinarith
  have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht0.ne'
  have e0 : ((f t : ℝ) : ℂ) + 1 = (((x / t) ^ 2 : ℝ) : ℂ) := by
    simp only [hf]; push_cast; ring
  have e1 : ((f t : ℝ) : ℂ) + ((1 + a * x ^ 2 : ℝ) : ℂ) =
      (((x / t) ^ 2 * (1 + a * t ^ 2) : ℝ) : ℂ) := by
    simp only [hf]; push_cast; field_simp; ring
  have e2 : ((f t : ℝ) : ℂ) + ((1 + b * x ^ 2 : ℝ) : ℂ) =
      (((x / t) ^ 2 * (1 + b * t ^ 2) : ℝ) : ℂ) := by
    simp only [hf]; push_cast; field_simp; ring
  simp only [symEllIntS]
  rw [e0, e1, e2, ofReal_cpow_half_eq_sqrt (sq_nonneg _),
    ofReal_cpow_half_eq_sqrt (by positivity), ofReal_cpow_half_eq_sqrt (by positivity),
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity),
    abs_neg, abs_of_pos (by positivity), real_smul, Real.sqrt_mul hA.le]
  have h1 : 0 < √(1 + a * t ^ 2) := Real.sqrt_pos.mpr hA
  have h2 : 0 < √(1 + b * t ^ 2) := Real.sqrt_pos.mpr hB
  have h1' : ((√(1 + a * t ^ 2) : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr h1.ne'
  have h2' : ((√(1 + b * t ^ 2) : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr h2.ne'
  have hx' : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  push_cast
  field_simp

/-- `x R_F(1, 1 + a x², 1 + b x²) = ∫₀ˣ dt/√((1 + a t²)(1 + b t²))` for every real `x` with
`1 + a x² ≥ 0`, `1 + b x² ≥ 0`. -/
private lemma mul_symEllIntRF_one_eq_integral {x a b : ℝ}
    (ha : 0 ≤ 1 + a * x ^ 2) (hb : 0 ≤ 1 + b * x ^ 2) :
    (x : ℂ) * symEllIntRF 1 ((1 + a * x ^ 2 : ℝ) : ℂ) ((1 + b * x ^ 2 : ℝ) : ℂ) =
      ((∫ t in (0 : ℝ)..x, 1 / √((1 + a * t ^ 2) * (1 + b * t ^ 2)) : ℝ) : ℂ) := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have h := mul_symEllIntRF_one_eq_integral_of_pos (neg_pos.mpr hx)
      (a := a) (b := b) (by simpa using ha) (by simpa using hb)
    simp only [neg_sq] at h
    have hc := intervalIntegral.integral_comp_neg (a := 0) (b := -x)
      (fun t => 1 / √((1 + a * t ^ 2) * (1 + b * t ^ 2)))
    simp only [neg_sq, neg_zero, neg_neg] at hc
    have : (∫ t in (0 : ℝ)..x, 1 / √((1 + a * t ^ 2) * (1 + b * t ^ 2))) =
        -∫ t in (0 : ℝ)..-x, 1 / √((1 + a * t ^ 2) * (1 + b * t ^ 2)) := by
      rw [hc, intervalIntegral.integral_symm]
    rw [this, ofReal_neg, ← h]
    push_cast; ring
  · simp
  · exact mul_symEllIntRF_one_eq_integral_of_pos hx ha hb

/-- `(y²)^{1/2} = y` for real `y ≥ 0`. -/
private lemma ofReal_sq_cpow_half' {y : ℝ} (hy : 0 ≤ y) : ((y ^ 2 : ℝ) : ℂ) ^ (1 / 2 : ℂ) = y := by
  rw [ofReal_cpow_half_eq_sqrt (sq_nonneg y), Real.sqrt_sq hy]

/-- The substitution `s = (t² - x²)/(1 - t²)` on `(x, 1)`: for `0 ≤ x < 1` and `1 + C ≥ 0`,
`R_F(x², 1, 1 + C) = ∫ₓ¹ dt/√((1 - t²)(1 - x² + C(1 - t²)))`. -/
private lemma symEllIntRF_sq_one_eq_integral_of_lt_one {x C : ℝ} (hx : 0 ≤ x) (hx1 : x < 1)
    (hC : 0 ≤ 1 + C) :
    symEllIntRF ((x ^ 2 : ℝ) : ℂ) 1 ((1 + C : ℝ) : ℂ) =
      ((∫ t in x..1, 1 / √((1 - t ^ 2) * (1 - x ^ 2 + C * (1 - t ^ 2))) : ℝ) : ℂ) := by
  have hx2 : x ^ 2 < 1 := by nlinarith
  set f : ℝ → ℝ := fun t => (t ^ 2 - x ^ 2) / (1 - t ^ 2) with hf
  have hderiv : ∀ t ∈ Ioo x 1, HasDerivWithinAt f (2 * t * (1 - x ^ 2) / (1 - t ^ 2) ^ 2)
      (Ioo x 1) t := by
    intro t ht
    have ht0 : 1 - t ^ 2 ≠ 0 := by nlinarith [ht.1, ht.2]
    have h := ((hasDerivAt_pow 2 t).sub_const (x ^ 2)).div
      ((hasDerivAt_pow 2 t).const_sub 1) ht0
    refine (h.congr_deriv ?_).hasDerivWithinAt.congr_of_mem (fun s _ => rfl) ht
    field_simp; ring
  have hinj : InjOn f (Ioo x 1) := by
    intro s hs t ht hst
    have h1 : 1 - s ^ 2 ≠ 0 := by nlinarith [hs.1, hs.2]
    have h2 : 1 - t ^ 2 ≠ 0 := by nlinarith [ht.1, ht.2]
    simp only [hf] at hst
    rw [div_eq_div_iff h1 h2] at hst
    have : (s ^ 2 - t ^ 2) * (1 - x ^ 2) = 0 := by linear_combination hst
    have hst2 : s ^ 2 = t ^ 2 := by
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · exact absurd h (by linarith)
    nlinarith [hs.1, ht.1, sq_nonneg (s - t), sq_nonneg (s + t)]
  have himg : f '' Ioo x 1 = Ioi 0 := by
    ext u; constructor
    · rintro ⟨t, ht, rfl⟩
      have h1 : 0 < 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
      have h2 : 0 < t ^ 2 - x ^ 2 := by nlinarith [ht.1, ht.2]
      exact div_pos h2 h1
    · intro hu
      have hu : 0 < u := hu
      have hq : 0 ≤ (u + x ^ 2) / (u + 1) := by positivity
      have hq2 : √((u + x ^ 2) / (u + 1)) ^ 2 = (u + x ^ 2) / (u + 1) := Real.sq_sqrt hq
      refine ⟨√((u + x ^ 2) / (u + 1)), ⟨?_, ?_⟩, ?_⟩
      · refine (Real.lt_sqrt hx).mpr ?_
        rw [lt_div_iff₀ (by positivity)]; nlinarith
      · rw [Real.sqrt_lt' one_pos, div_lt_iff₀ (by positivity)]; linarith
      · simp only [hf]
        rw [hq2]
        have h1 : u + 1 ≠ 0 := by positivity
        have h2 : 1 - (u + x ^ 2) / (u + 1) ≠ 0 := by
          rw [one_sub_div h1]; exact div_ne_zero (by linarith) h1
        rw [div_eq_iff h2]
        field_simp
        ring
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj
    (fun t => (symEllIntS ((x ^ 2 : ℝ) : ℂ) 1 ((1 + C : ℝ) : ℂ) t)⁻¹)
  rw [himg] at h
  rw [symEllIntRF, h, intervalIntegral.integral_of_le hx1.le, integral_Ioc_eq_integral_Ioo,
    ← integral_complex_ofReal, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
  have ht0 : 0 < t := hx.trans_lt ht.1
  have hD : 0 < 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
  have hxt : x ^ 2 < t ^ 2 := by nlinarith [ht.1, ht.2]
  have hR : 0 < 1 - x ^ 2 + C * (1 - t ^ 2) := by nlinarith
  set p := √(1 - x ^ 2) with hp
  set q := √(1 - t ^ 2) with hq
  set r := √(1 - x ^ 2 + C * (1 - t ^ 2)) with hr
  have hp0 : 0 < p := Real.sqrt_pos.mpr (by linarith)
  have hq0 : 0 < q := Real.sqrt_pos.mpr hD
  have hr0 : 0 < r := Real.sqrt_pos.mpr hR
  have hp2 : p ^ 2 = 1 - x ^ 2 := Real.sq_sqrt (by linarith)
  have hq2 : q ^ 2 = 1 - t ^ 2 := Real.sq_sqrt hD.le
  have hr2 : r ^ 2 = 1 - x ^ 2 + C * (1 - t ^ 2) := Real.sq_sqrt hR.le
  have hD' := hD.ne'
  have e0 : ((f t : ℝ) : ℂ) + ((x ^ 2 : ℝ) : ℂ) = (((t * p / q) ^ 2 : ℝ) : ℂ) := by
    rw [← ofReal_add]; congr 1; simp only [hf]; rw [div_pow, mul_pow, hp2, hq2]; field_simp; ring
  have e1 : ((f t : ℝ) : ℂ) + 1 = (((p / q) ^ 2 : ℝ) : ℂ) := by
    rw [← ofReal_one, ← ofReal_add]
    congr 1; simp only [hf]; rw [div_pow, hp2, hq2]; field_simp; ring
  have e2 : ((f t : ℝ) : ℂ) + ((1 + C : ℝ) : ℂ) = (((r / q) ^ 2 : ℝ) : ℂ) := by
    rw [← ofReal_add]; congr 1; simp only [hf]; rw [div_pow, hr2, hq2]; field_simp; ring
  simp only [symEllIntS]
  rw [e0, e1, e2, ofReal_sq_cpow_half' (by positivity), ofReal_sq_cpow_half' (by positivity),
    ofReal_sq_cpow_half' (by positivity), abs_of_pos (by positivity), real_smul,
    Real.sqrt_mul hD.le, ← hq, ← hr, ← hp2, ← hq2]
  have : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht0.ne'
  have : (p : ℂ) ≠ 0 := ofReal_ne_zero.mpr hp0.ne'
  have : (q : ℂ) ≠ 0 := ofReal_ne_zero.mpr hq0.ne'
  have : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr0.ne'
  push_cast
  field_simp

/-- The substitution `s = (x² - t²)/(t² - 1)` on `(1, x)`: for `1 < x` and `1 + C ≥ 0`,
`R_F(x², 1, 1 + C) = ∫₁ˣ dt/√((t² - 1)(x² - 1 + C(t² - 1)))`. -/
private lemma symEllIntRF_sq_one_eq_integral_of_one_lt {x C : ℝ} (hx1 : 1 < x)
    (hC : 0 ≤ 1 + C) :
    symEllIntRF ((x ^ 2 : ℝ) : ℂ) 1 ((1 + C : ℝ) : ℂ) =
      ((∫ t in (1 : ℝ)..x, 1 / √((t ^ 2 - 1) * (x ^ 2 - 1 + C * (t ^ 2 - 1))) : ℝ) : ℂ) := by
  have hx2 : 1 < x ^ 2 := by nlinarith
  set f : ℝ → ℝ := fun t => (x ^ 2 - t ^ 2) / (t ^ 2 - 1) with hf
  have hderiv : ∀ t ∈ Ioo 1 x, HasDerivWithinAt f (-(2 * t * (x ^ 2 - 1) / (t ^ 2 - 1) ^ 2))
      (Ioo 1 x) t := by
    intro t ht
    have ht0 : t ^ 2 - 1 ≠ 0 := by nlinarith [ht.1, ht.2]
    have h := ((hasDerivAt_pow 2 t).const_sub (x ^ 2)).div
      ((hasDerivAt_pow 2 t).sub_const 1) ht0
    refine (h.congr_deriv ?_).hasDerivWithinAt.congr_of_mem (fun s _ => rfl) ht
    field_simp; ring
  have hinj : InjOn f (Ioo 1 x) := by
    intro s hs t ht hst
    have h1 : s ^ 2 - 1 ≠ 0 := by nlinarith [hs.1, hs.2]
    have h2 : t ^ 2 - 1 ≠ 0 := by nlinarith [ht.1, ht.2]
    simp only [hf] at hst
    rw [div_eq_div_iff h1 h2] at hst
    have : (s ^ 2 - t ^ 2) * (x ^ 2 - 1) = 0 := by linear_combination -hst
    have hst2 : s ^ 2 = t ^ 2 := by
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · exact absurd h (by linarith)
    nlinarith [hs.1, ht.1, sq_nonneg (s - t), sq_nonneg (s + t)]
  have himg : f '' Ioo 1 x = Ioi 0 := by
    ext u; constructor
    · rintro ⟨t, ht, rfl⟩
      have h1 : 0 < t ^ 2 - 1 := by nlinarith [ht.1, ht.2]
      have h2 : 0 < x ^ 2 - t ^ 2 := by nlinarith [ht.1, ht.2]
      exact div_pos h2 h1
    · intro hu
      have hu : 0 < u := hu
      have hq : 0 ≤ (x ^ 2 + u) / (1 + u) := by positivity
      have hq2 : √((x ^ 2 + u) / (1 + u)) ^ 2 = (x ^ 2 + u) / (1 + u) := Real.sq_sqrt hq
      refine ⟨√((x ^ 2 + u) / (1 + u)), ⟨?_, ?_⟩, ?_⟩
      · refine (Real.lt_sqrt zero_le_one).mpr ?_
        rw [lt_div_iff₀ (by positivity)]; nlinarith
      · rw [Real.sqrt_lt' (by linarith), div_lt_iff₀ (by positivity)]; nlinarith
      · simp only [hf]
        rw [hq2]
        have h1 : 1 + u ≠ 0 := by positivity
        have h2 : (x ^ 2 + u) / (1 + u) - 1 ≠ 0 := by
          rw [div_sub_one h1]; exact div_ne_zero (by linarith) h1
        rw [div_eq_iff h2]
        field_simp
        ring
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj
    (fun t => (symEllIntS ((x ^ 2 : ℝ) : ℂ) 1 ((1 + C : ℝ) : ℂ) t)⁻¹)
  rw [himg] at h
  rw [symEllIntRF, h, intervalIntegral.integral_of_le hx1.le, integral_Ioc_eq_integral_Ioo,
    ← integral_complex_ofReal, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
  have ht0 : 0 < t := one_pos.trans ht.1
  have hD : 0 < t ^ 2 - 1 := by nlinarith [ht.1, ht.2]
  have hxt : t ^ 2 < x ^ 2 := by nlinarith [ht.1, ht.2]
  have hR : 0 < x ^ 2 - 1 + C * (t ^ 2 - 1) := by nlinarith
  set p := √(x ^ 2 - 1) with hp
  set q := √(t ^ 2 - 1) with hq
  set r := √(x ^ 2 - 1 + C * (t ^ 2 - 1)) with hr
  have hp0 : 0 < p := Real.sqrt_pos.mpr (by linarith)
  have hq0 : 0 < q := Real.sqrt_pos.mpr hD
  have hr0 : 0 < r := Real.sqrt_pos.mpr hR
  have hp2 : p ^ 2 = x ^ 2 - 1 := Real.sq_sqrt (by linarith)
  have hq2 : q ^ 2 = t ^ 2 - 1 := Real.sq_sqrt hD.le
  have hr2 : r ^ 2 = x ^ 2 - 1 + C * (t ^ 2 - 1) := Real.sq_sqrt hR.le
  have hD' := hD.ne'
  have e0 : ((f t : ℝ) : ℂ) + ((x ^ 2 : ℝ) : ℂ) = (((t * p / q) ^ 2 : ℝ) : ℂ) := by
    rw [← ofReal_add]; congr 1; simp only [hf]; rw [div_pow, mul_pow, hp2, hq2]; field_simp; ring
  have e1 : ((f t : ℝ) : ℂ) + 1 = (((p / q) ^ 2 : ℝ) : ℂ) := by
    rw [← ofReal_one, ← ofReal_add]
    congr 1; simp only [hf]; rw [div_pow, hp2, hq2]; field_simp; ring
  have e2 : ((f t : ℝ) : ℂ) + ((1 + C : ℝ) : ℂ) = (((r / q) ^ 2 : ℝ) : ℂ) := by
    rw [← ofReal_add]; congr 1; simp only [hf]; rw [div_pow, hr2, hq2]; field_simp; ring
  simp only [symEllIntS]
  rw [e0, e1, e2, ofReal_sq_cpow_half' (by positivity), ofReal_sq_cpow_half' (by positivity),
    ofReal_sq_cpow_half' (by positivity), abs_neg, abs_of_pos (by positivity), real_smul,
    Real.sqrt_mul hD.le, ← hq, ← hr, ← hp2, ← hq2]
  have : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht0.ne'
  have : (p : ℂ) ≠ 0 := ofReal_ne_zero.mpr hp0.ne'
  have : (q : ℂ) ≠ 0 := ofReal_ne_zero.mpr hq0.ne'
  have : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr0.ne'
  push_cast
  field_simp

/-- Pulling `√w` into an integral of reciprocal square roots:
`√w ∫ dt/√(D(t) R(t)) = ∫ dt/√(D(t) Q(t))` when `R = w Q`, `w > 0`. -/
private lemma sqrt_mul_integral_one_div_sqrt {w : ℝ} (hw : 0 < w) (a b : ℝ) (D R Q : ℝ → ℝ)
    (h : ∀ t, R t = w * Q t) :
    √w * ∫ t in a..b, 1 / √(D t * R t) = ∫ t in a..b, 1 / √(D t * Q t) := by
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun t _ => ?_
  rw [h, mul_left_comm, Real.sqrt_mul hw.le, mul_one_div,
    div_mul_cancel_left₀ (Real.sqrt_pos.mpr hw).ne', one_div]

/-- The substitution `s = t² - x²`: `R_F(x², x² + a, x² + b) = ∫ₓ^∞ dt/√((t² + a)(t² + b))`. -/
private lemma symEllIntRF_sq_add_eq_integral_Ioi {x a b : ℝ} (hx : 0 ≤ x) (ha : 0 ≤ x ^ 2 + a)
    (hb : 0 ≤ x ^ 2 + b) :
    symEllIntRF ((x ^ 2 : ℝ) : ℂ) ((x ^ 2 + a : ℝ) : ℂ) ((x ^ 2 + b : ℝ) : ℂ) =
      ((∫ t in Ioi x, 1 / √((t ^ 2 + a) * (t ^ 2 + b)) : ℝ) : ℂ) := by
  set f : ℝ → ℝ := fun t => t ^ 2 - x ^ 2 with hf
  have hderiv : ∀ t ∈ Ioi x, HasDerivWithinAt f (2 * t) (Ioi x) t := by
    intro t _
    have h := ((hasDerivAt_pow 2 t).sub_const (x ^ 2)).hasDerivWithinAt (s := Ioi x)
    simpa [hf] using h
  have hinj : InjOn f (Ioi x) := by
    intro s hs t ht hst
    have hs' : 0 ≤ s := hx.trans (le_of_lt hs)
    have ht' : 0 ≤ t := hx.trans (le_of_lt ht)
    simp only [hf, sub_left_inj] at hst
    nlinarith [sq_nonneg (s - t), sq_nonneg (s + t)]
  have himg : f '' Ioi x = Ioi 0 := by
    ext u; constructor
    · rintro ⟨t, ht, rfl⟩
      have ht : x < t := ht
      simp only [hf, mem_Ioi, sub_pos]
      exact pow_lt_pow_left₀ ht hx two_ne_zero
    · intro hu
      have hu : 0 < u := hu
      refine ⟨√(u + x ^ 2), ?_, ?_⟩
      · show x < √(u + x ^ 2)
        exact (Real.lt_sqrt hx).mpr (by linarith)
      · simp only [hf]
        rw [Real.sq_sqrt (by positivity)]; ring
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj
    (fun t => (symEllIntS ((x ^ 2 : ℝ) : ℂ) ((x ^ 2 + a : ℝ) : ℂ) ((x ^ 2 + b : ℝ) : ℂ) t)⁻¹)
  rw [himg] at h
  rw [symEllIntRF, h, ← integral_complex_ofReal, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht : x < t := ht
  have ht0 : 0 < t := hx.trans_lt ht
  have hxt : x ^ 2 < t ^ 2 := pow_lt_pow_left₀ ht hx two_ne_zero
  have hA : 0 < t ^ 2 + a := by linarith
  have hB : 0 < t ^ 2 + b := by linarith
  have e0 : ((f t : ℝ) : ℂ) + ((x ^ 2 : ℝ) : ℂ) = ((t ^ 2 : ℝ) : ℂ) := by
    simp only [hf]; push_cast; ring
  have e1 : ((f t : ℝ) : ℂ) + ((x ^ 2 + a : ℝ) : ℂ) = ((t ^ 2 + a : ℝ) : ℂ) := by
    simp only [hf]; push_cast; ring
  have e2 : ((f t : ℝ) : ℂ) + ((x ^ 2 + b : ℝ) : ℂ) = ((t ^ 2 + b : ℝ) : ℂ) := by
    simp only [hf]; push_cast; ring
  simp only [symEllIntS]
  rw [e0, e1, e2, ofReal_cpow_half_eq_sqrt (sq_nonneg t), ofReal_cpow_half_eq_sqrt hA.le,
    ofReal_cpow_half_eq_sqrt hB.le, Real.sqrt_sq ht0.le, abs_of_pos (by positivity), real_smul,
    Real.sqrt_mul hA.le]
  have h1 : 0 < √(t ^ 2 + a) := Real.sqrt_pos.mpr hA
  have h2 : 0 < √(t ^ 2 + b) := Real.sqrt_pos.mpr hB
  have h1' : ((√(t ^ 2 + a) : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr h1.ne'
  have h2' : ((√(t ^ 2 + b) : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr h2.ne'
  have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht0.ne'
  push_cast
  field_simp

/-- DLMF 19.25.32 (`arccs`, `arcds`, `arcns` as `R_F`); stronger than DLMF, which assumes
`0 ≤ k²`: only `k² < 1` is needed. -/
@[dlmf 19.25.E32]
theorem jacobiArcps_eq_symEllIntRF' {m x : ℝ} (hm : m < 1) :
    (0 ≤ x → (Real.jacobiArccsm x m : ℂ) =
        symEllIntRF ((x ^ 2 : ℝ) : ℂ) ((x ^ 2 + (1 - m) : ℝ) : ℂ) ((x ^ 2 + 1 : ℝ) : ℂ)) ∧
      (√(1 - m) ≤ x → (Real.jacobiArcdsm x m : ℂ) =
        symEllIntRF ((x ^ 2 : ℝ) : ℂ) ((x ^ 2 - (1 - m) : ℝ) : ℂ) ((x ^ 2 + m : ℝ) : ℂ)) ∧
      (1 ≤ x → (Real.jacobiArcnsm x m : ℂ) =
        symEllIntRF ((x ^ 2 : ℝ) : ℂ) ((x ^ 2 - 1 : ℝ) : ℂ) ((x ^ 2 - m : ℝ) : ℂ)) := by
  refine ⟨fun hx => ?_, fun hx => ?_, fun hx => ?_⟩
  · rw [symEllIntRF_sq_add_eq_integral_Ioi hx (by nlinarith) (by nlinarith), Real.jacobiArccsm]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    ring_nf
  · have hx0 : 0 ≤ x := (Real.sqrt_nonneg _).trans hx
    have hx2 : 1 - m ≤ x ^ 2 := by
      have := pow_le_pow_left₀ (Real.sqrt_nonneg _) hx 2
      rwa [Real.sq_sqrt (by linarith)] at this
    rw [show x ^ 2 - (1 - m) = x ^ 2 + -(1 - m) by ring,
      symEllIntRF_sq_add_eq_integral_Ioi hx0 (by linarith) (by nlinarith), Real.jacobiArcdsm]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    ring_nf
  · have hx0 : 0 ≤ x := zero_le_one.trans hx
    rw [show x ^ 2 - 1 = x ^ 2 + -1 by ring, show x ^ 2 - m = x ^ 2 + -m by ring,
      symEllIntRF_sq_add_eq_integral_Ioi hx0 (by nlinarith) (by nlinarith), Real.jacobiArcnsm]
    rfl

/-- DLMF 19.25.32 for `ps = cs, ds, ns` (with `Δ(d, c) = k'²`, `Δ(n, c) = 1`, `Δ(n, d) = k²`,
19.25.29): `arcps(x, k) = R_F(x², x² + Δ(q, p), x² + Δ(r, p))`, i.e.
`arccs x = R_F(x², x² + k'², x² + 1)` for `x ≥ 0` (**corrected**: DLMF says `x` real; the left
side is not even in `x`), `arcds x = R_F(x², x² - k'², x² + k²)` for `x ≥ k'`, and
`arcns x = R_F(x², x² - 1, x² - k²)` for `x ≥ 1`; real parameter `0 ≤ m = k² < 1`. -/
@[dlmf 19.25.E32]
theorem jacobiArcps_eq_symEllIntRF {m x : ℝ} (_hm0 : 0 ≤ m) (hm : m < 1) :
    (0 ≤ x → (Real.jacobiArccsm x m : ℂ) =
        symEllIntRF ((x ^ 2 : ℝ) : ℂ) ((x ^ 2 + (1 - m) : ℝ) : ℂ) ((x ^ 2 + 1 : ℝ) : ℂ)) ∧
      (√(1 - m) ≤ x → (Real.jacobiArcdsm x m : ℂ) =
        symEllIntRF ((x ^ 2 : ℝ) : ℂ) ((x ^ 2 - (1 - m) : ℝ) : ℂ) ((x ^ 2 + m : ℝ) : ℂ)) ∧
      (1 ≤ x → (Real.jacobiArcnsm x m : ℂ) =
        symEllIntRF ((x ^ 2 : ℝ) : ℂ) ((x ^ 2 - 1 : ℝ) : ℂ) ((x ^ 2 - m : ℝ) : ℂ)) := by
  exact jacobiArcps_eq_symEllIntRF' hm

/-- DLMF 19.25.33 (`arcsc`, `arcsd`, `arcsn` as `R_F`); stronger than DLMF, which assumes
`0 ≤ k²`: only `k² < 1` is needed. -/
@[dlmf 19.25.E33]
theorem jacobiArcsp_eq_symEllIntRF' {m x : ℝ} (hm : m < 1) :
    ((Real.jacobiArcscm x m : ℂ) =
        x * symEllIntRF 1 ((1 + (1 - m) * x ^ 2 : ℝ) : ℂ) ((1 + x ^ 2 : ℝ) : ℂ)) ∧
      ((1 - m) * x ^ 2 ≤ 1 → (Real.jacobiArcsdm x m : ℂ) =
        x * symEllIntRF 1 ((1 - (1 - m) * x ^ 2 : ℝ) : ℂ) ((1 + m * x ^ 2 : ℝ) : ℂ)) ∧
      (x ^ 2 ≤ 1 → (DLMF.Elliptic.Real.jacobiArcsnm x m : ℂ) =
        x * symEllIntRF 1 ((1 - x ^ 2 : ℝ) : ℂ) ((1 - m * x ^ 2 : ℝ) : ℂ)) := by
  refine ⟨?_, fun hx => ?_, fun hx => ?_⟩
  · rw [show (1 + x ^ 2 : ℝ) = 1 + 1 * x ^ 2 by ring,
      mul_symEllIntRF_one_eq_integral (by nlinarith) (by nlinarith), Real.jacobiArcscm]
    congr 1
    refine intervalIntegral.integral_congr fun t _ => ?_
    ring_nf
  · rw [show (1 - (1 - m) * x ^ 2 : ℝ) = 1 + -(1 - m) * x ^ 2 by ring,
      mul_symEllIntRF_one_eq_integral (by nlinarith) (by nlinarith), Real.jacobiArcsdm]
    congr 1
    refine intervalIntegral.integral_congr fun t _ => ?_
    ring_nf
  · have hx1 : |x| ≤ 1 := by
      rw [← abs_one, ← sq_le_sq]; simpa using hx
    rw [show (1 - x ^ 2 : ℝ) = 1 + -1 * x ^ 2 by ring,
      show (1 - m * x ^ 2 : ℝ) = 1 + -m * x ^ 2 by ring,
      mul_symEllIntRF_one_eq_integral (by nlinarith) (by nlinarith),
      Real.jacobiArcsnm_eq_integral hm (abs_le.mp hx1).1 (abs_le.mp hx1).2]
    congr 1
    refine intervalIntegral.integral_congr fun t _ => ?_
    ring_nf

/-- DLMF 19.25.33 for `sp = sc, sd, sn`: `arcsp(x, k) = x R_F(1, 1 + Δ(q, p) x², 1 + Δ(r, p) x²)`,
i.e. `arcsc x = x R_F(1, 1 + k'² x², 1 + x²)` for real `x`,
`arcsd x = x R_F(1, 1 - k'² x², 1 + k² x²)` for `0 ≤ x² ≤ 1/k'²`, and
`arcsn x = x R_F(1, 1 - x², 1 - k² x²)` for `0 ≤ x² ≤ 1`; real `0 ≤ m = k² < 1`. -/
@[dlmf 19.25.E33]
theorem jacobiArcsp_eq_symEllIntRF {m x : ℝ} (_hm0 : 0 ≤ m) (hm : m < 1) :
    ((Real.jacobiArcscm x m : ℂ) =
        x * symEllIntRF 1 ((1 + (1 - m) * x ^ 2 : ℝ) : ℂ) ((1 + x ^ 2 : ℝ) : ℂ)) ∧
      ((1 - m) * x ^ 2 ≤ 1 → (Real.jacobiArcsdm x m : ℂ) =
        x * symEllIntRF 1 ((1 - (1 - m) * x ^ 2 : ℝ) : ℂ) ((1 + m * x ^ 2 : ℝ) : ℂ)) ∧
      (x ^ 2 ≤ 1 → (DLMF.Elliptic.Real.jacobiArcsnm x m : ℂ) =
        x * symEllIntRF 1 ((1 - x ^ 2 : ℝ) : ℂ) ((1 - m * x ^ 2 : ℝ) : ℂ)) := by
  exact jacobiArcsp_eq_symEllIntRF' hm

/-- DLMF 19.25.34 for the six `pq` with `p, q ∈ {c, d, n}`:
`arcpq(x, k) = √w R_F(x², 1, 1 + Δ(r, q) w)`, `w = (1 - x²)/Δ(q, p)`, with `0 < m = k² < 1`:
`arccd` and `arccn` for `0 ≤ x ≤ 1` (**corrected**: DLMF allows `0 ≤ x² ≤ 1`, but the left sides
are not even in `x`), `arcdc` and `arcnc` for `x ≥ 1`, `arcdn` for `k' ≤ x ≤ 1`, `arcnd` for
`1 ≤ x ≤ 1/k'`. -/
@[dlmf 19.25.E34]
theorem jacobiArcpq_eq_symEllIntRF {m x : ℝ} (hm0 : 0 < m) (hm : m < 1) :
    -- `cd`: `p = c, q = d, r = n`, `w = (1 - x²)/k'²`, `Δ(n, d) = k²`
    (0 ≤ x → x ≤ 1 → (Real.jacobiArccdm x m : ℂ) =
        ((√((1 - x ^ 2) / (1 - m)) : ℝ) : ℂ) *
          symEllIntRF ((x ^ 2 : ℝ) : ℂ) 1 ((1 + m * ((1 - x ^ 2) / (1 - m)) : ℝ) : ℂ)) ∧
    -- `cn`: `p = c, q = n, r = d`, `w = 1 - x²`, `Δ(d, n) = -k²`
    (0 ≤ x → x ≤ 1 → (Real.jacobiArccnm x m : ℂ) =
        ((√(1 - x ^ 2) : ℝ) : ℂ) * symEllIntRF ((x ^ 2 : ℝ) : ℂ) 1 ((1 - m * (1 - x ^ 2) : ℝ) : ℂ))
          ∧
    -- `dc`: `p = d, q = c, r = n`, `w = (x² - 1)/k'²`, `Δ(n, c) = 1`
    (1 ≤ x → (Real.jacobiArcdcm x m : ℂ) =
        ((√((x ^ 2 - 1) / (1 - m)) : ℝ) : ℂ) *
          symEllIntRF ((x ^ 2 : ℝ) : ℂ) 1 ((1 + (x ^ 2 - 1) / (1 - m) : ℝ) : ℂ)) ∧
    -- `nc`: `p = n, q = c, r = d`, `w = x² - 1`, `Δ(d, c) = k'²`
    (1 ≤ x → (Real.jacobiArcncm x m : ℂ) =
        ((√(x ^ 2 - 1) : ℝ) : ℂ) * symEllIntRF ((x ^ 2 : ℝ) : ℂ) 1
          ((1 + (1 - m) * (x ^ 2 - 1) : ℝ) : ℂ)) ∧
    -- `dn`: `p = d, q = n, r = c`, `w = (1 - x²)/k²`, `Δ(c, n) = -1`
    (√(1 - m) ≤ x → x ≤ 1 → (Real.jacobiArcdnm x m : ℂ) =
        ((√((1 - x ^ 2) / m) : ℝ) : ℂ) * symEllIntRF ((x ^ 2 : ℝ) : ℂ) 1
          ((1 - (1 - x ^ 2) / m : ℝ) : ℂ)) ∧
    -- `nd`: `p = n, q = d, r = c`, `w = (x² - 1)/k²`, `Δ(c, d) = -k'²`
    (1 ≤ x → x * √(1 - m) ≤ 1 → (Real.jacobiArcndm x m : ℂ) =
        ((√((x ^ 2 - 1) / m) : ℝ) : ℂ) *
          symEllIntRF ((x ^ 2 : ℝ) : ℂ) 1 ((1 - (1 - m) * ((x ^ 2 - 1) / m) : ℝ) : ℂ)) := by
  have hm1 : 0 < 1 - m := by linarith
  refine ⟨fun hx0 hx1 => ?_, fun hx0 hx1 => ?_, fun hx1 => ?_, fun hx1 => ?_,
    fun hx0 hx1 => ?_, fun hx1 hxm => ?_⟩
  · -- `cd`
    rcases hx1.lt_or_eq with hx1 | rfl
    · have hw : 0 < (1 - x ^ 2) / (1 - m) := div_pos (by nlinarith) hm1
      rw [symEllIntRF_sq_one_eq_integral_of_lt_one hx0 hx1 (by positivity), ← ofReal_mul,
        sqrt_mul_integral_one_div_sqrt hw x 1 (fun t => 1 - t ^ 2)
          (fun t => 1 - x ^ 2 + m * ((1 - x ^ 2) / (1 - m)) * (1 - t ^ 2))
          (fun t => 1 - m * t ^ 2) (fun t => by field_simp; ring), Real.jacobiArccdm]
    · simp [Real.jacobiArccdm]
  · -- `cn`
    have hw : 0 ≤ 1 - x ^ 2 := by nlinarith
    have hB := mul_symEllIntRF_one_eq_integral (x := √(1 - x ^ 2)) (a := -1) (b := -m)
      (by rw [Real.sq_sqrt hw]; nlinarith) (by rw [Real.sq_sqrt hw]; nlinarith)
    rw [Real.sq_sqrt hw, show (1 + -1 * (1 - x ^ 2) : ℝ) = x ^ 2 by ring,
      show (1 + -m * (1 - x ^ 2) : ℝ) = 1 - m * (1 - x ^ 2) by ring] at hB
    rw [symEllIntRF_comm_left, hB, Real.jacobiArccnm, Real.arccos_eq_arcsin hx0,
      ← DLMF.Elliptic.Real.integral_recip_sqrt_eq_incEllIntFm hm (Real.sqrt_nonneg _)
        (Real.sqrt_le_one.mpr (by nlinarith))]
    congr 1
    refine intervalIntegral.integral_congr fun t _ => ?_
    ring_nf
  · -- `dc`
    rcases hx1.lt_or_eq with hx1 | rfl
    · have hw : 0 < (x ^ 2 - 1) / (1 - m) := div_pos (by nlinarith) hm1
      rw [symEllIntRF_sq_one_eq_integral_of_one_lt hx1 (by positivity), ← ofReal_mul,
        sqrt_mul_integral_one_div_sqrt hw 1 x (fun t => t ^ 2 - 1)
          (fun t => x ^ 2 - 1 + (x ^ 2 - 1) / (1 - m) * (t ^ 2 - 1))
          (fun t => t ^ 2 - m) (fun t => by field_simp; ring), Real.jacobiArcdcm]
    · simp [Real.jacobiArcdcm]
  · -- `nc`
    rcases hx1.lt_or_eq with hx1 | rfl
    · have hw : 0 < x ^ 2 - 1 := by nlinarith
      rw [symEllIntRF_sq_one_eq_integral_of_one_lt hx1 (by nlinarith), ← ofReal_mul,
        sqrt_mul_integral_one_div_sqrt hw 1 x (fun t => t ^ 2 - 1)
          (fun t => x ^ 2 - 1 + (1 - m) * (x ^ 2 - 1) * (t ^ 2 - 1))
          (fun t => m + (1 - m) * t ^ 2) (fun t => by ring), Real.jacobiArcncm]
    · simp [Real.jacobiArcncm]
  · -- `dn`
    have hx0' : 0 ≤ x := (Real.sqrt_nonneg _).trans hx0
    have hx2 : 1 - m ≤ x ^ 2 := by
      have := pow_le_pow_left₀ (Real.sqrt_nonneg _) hx0 2
      rwa [Real.sq_sqrt hm1.le] at this
    have hw : 0 ≤ (1 - x ^ 2) / m := div_nonneg (by nlinarith) hm0.le
    have hw1 : (1 - x ^ 2) / m ≤ 1 := by rw [div_le_one hm0]; linarith
    have hB := mul_symEllIntRF_one_eq_integral (x := √((1 - x ^ 2) / m)) (a := -m) (b := -1)
      (by rw [Real.sq_sqrt hw]; field_simp; nlinarith) (by rw [Real.sq_sqrt hw]; linarith)
    rw [Real.sq_sqrt hw, show (1 + -m * ((1 - x ^ 2) / m) : ℝ) = x ^ 2 by field_simp; ring,
      show (1 + -1 * ((1 - x ^ 2) / m) : ℝ) = 1 - (1 - x ^ 2) / m by ring] at hB
    rw [symEllIntRF_comm_left, hB, Real.jacobiArcdnm,
      ← DLMF.Elliptic.Real.integral_recip_sqrt_eq_incEllIntFm hm (Real.sqrt_nonneg _)
        (Real.sqrt_le_one.mpr hw1)]
    congr 1
    refine intervalIntegral.integral_congr fun t _ => ?_
    ring_nf
  · -- `nd`
    have hxm2 : (1 - m) * x ^ 2 ≤ 1 := by
      have h0 : 0 ≤ x * √(1 - m) := by positivity
      have := pow_le_pow_left₀ h0 hxm 2
      rw [mul_pow, Real.sq_sqrt hm1.le, one_pow] at this
      linarith
    rcases hx1.lt_or_eq with hx1 | rfl
    · have hw : 0 < (x ^ 2 - 1) / m := div_pos (by nlinarith) hm0
      rw [show (1 - (1 - m) * ((x ^ 2 - 1) / m) : ℝ) = 1 + -((1 - m) * ((x ^ 2 - 1) / m)) by ring,
        symEllIntRF_sq_one_eq_integral_of_one_lt hx1
          (by rw [← sub_eq_add_neg, sub_nonneg, ← mul_div_assoc, div_le_one hm0]; nlinarith),
        ← ofReal_mul,
        sqrt_mul_integral_one_div_sqrt hw 1 x (fun t => t ^ 2 - 1)
          (fun t => x ^ 2 - 1 + -((1 - m) * ((x ^ 2 - 1) / m)) * (t ^ 2 - 1))
          (fun t => 1 - (1 - m) * t ^ 2) (fun t => by field_simp; ring), Real.jacobiArcndm]
    · simp [Real.jacobiArcndm]

end DLMF.EllipticIntegrals
