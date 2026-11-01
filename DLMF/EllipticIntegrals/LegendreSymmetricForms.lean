/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.EllipticIntegrals.Legendre
public import DLMF.EllipticIntegrals.Symmetric

/-!
# Legendre's integrals as symmetric integrals: the substitution (DLMF §19.25(i))

Supporting results for expressing Legendre's integrals through Carlson's symmetric integrals.
For real `0 < φ ≤ π/2` and `c = csc² φ`, the substitution `t = csc² θ - c`, `θ ∈ (0, φ)`, maps
`(0, φ)` onto `(0, ∞)` with `|dt/dθ| = 2 cos θ / sin³ θ`. Under it `√(t + c - 1) = cot θ`,
`√(t + c - w) = √(1 - w sin² θ)/sin θ`, `√(t + c) = csc θ` (principal branches, any complex
`w`), so the defining integrals of `R_F`, `R_D`, `R_J` at `(c - 1, c - k², c, c - α²)` become
Legendre-type integrals over `(0, φ)` **for every complex `k`** (no branch condition is needed
at the level of the integrals).

## Main results

* `integral_Ioi_eq_integral_Ioo_csc_sq_subst`: the substitution `t = csc² θ - csc² φ`.
* `symEllIntRF_csc_sq_eq_integral`, `symEllIntRD_csc_sq_eq_integral`,
  `symEllIntRJ_csc_sq_eq_integral`: DLMF 19.25.5, 19.25.13 and 19.25.14 at the level of
  integrals.
* `incEllIntDk_eq_one_third_symEllIntRD`, `incEllIntEk_eq_symEllIntRF_sub_one_third_symEllIntRD`:
  DLMF 19.25.13 and 19.25.9 with explicit `c = csc² φ`.
* `incEllIntEk_eq_symEllIntR_csc_sq`, `incEllIntPik_eq_symEllIntR_csc_sq`: DLMF 19.25.8 and
  19.25.15 in terms of `symEllIntR`.
* `compEllIntPik_eq_pi_div_two_mul_symEllIntR`: DLMF 19.25.3.
* `symEllIntRF_scale`, `symEllIntRJ_scale`, `symEllIntRD_scale`, `symEllIntRG_scale`:
  homogeneity of the symmetric integrals under real positive scaling.
* `real_symmetric_legendre_parametrization`: the data of §19.25(iii) as complex scalings.
* `bulirschEl1_eq_symEllIntRF_of_pos`, `bulirschEl2_eq_symEllIntRD`: Bulirsch's integrals as
  symmetric integrals.

## References

* NIST DLMF §19.25.
-/

@[expose] public noncomputable section

open Complex Set Filter MeasureTheory
open scoped Real Topology

namespace DLMF.EllipticIntegrals

/-- `(r w)^s = r^s w^s` for real `r > 0` and any complex `w`, `s`. -/
private lemma ofReal_mul_cpow_of_pos {r : ℝ} (hr : 0 < r) (w s : ℂ) :
    ((r : ℂ) * w) ^ s = (r : ℂ) ^ s * w ^ s := by
  have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
  by_cases hw : w = 0
  · subst hw
    by_cases hs : s = 0
    · simp [hs]
    · simp [zero_cpow hs]
  · rw [cpow_def_of_ne_zero (mul_ne_zero hr0 hw), log_ofReal_mul hr hw, cpow_def_of_ne_zero hr0,
      cpow_def_of_ne_zero hw, ← Complex.exp_add, ← ofReal_log hr.le]
    congr 1; ring

/-- The substitution `t = csc² θ - csc² φ` on `(0, φ)`, `0 < φ ≤ π/2`:
`∫₀^∞ G(t) dt = ∫₀^φ (2 cos θ / sin³ θ) G(csc² θ - csc² φ) dθ` (no integrability needed). -/
lemma integral_Ioi_eq_integral_Ioo_csc_sq_subst {φ : ℝ} (h0 : 0 < φ) (h1 : φ ≤ π / 2) (G : ℝ → ℂ) :
    ∫ t in Ioi (0 : ℝ), G t = ∫ θ in Ioo (0 : ℝ) φ,
      ((2 * Real.cos θ / Real.sin θ ^ 3 : ℝ) : ℂ) * G (1 / Real.sin θ ^ 2 - 1 / Real.sin φ ^ 2) := by
  set f : ℝ → ℝ := fun θ => 1 / Real.sin θ ^ 2 - 1 / Real.sin φ ^ 2 with hf
  have hsinpos : ∀ θ ∈ Ioo (0 : ℝ) φ, 0 < Real.sin θ := fun θ hθ =>
    Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hcospos : ∀ θ ∈ Ioo (0 : ℝ) φ, 0 < Real.cos θ := fun θ hθ =>
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩
  have hsφ : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
  have hderiv : ∀ θ ∈ Ioo (0 : ℝ) φ, HasDerivWithinAt f (-(2 * Real.cos θ / Real.sin θ ^ 3))
      (Ioo 0 φ) θ := by
    intro θ hθ
    have hs := (hsinpos θ hθ).ne'
    have h := (((Real.hasDerivAt_sin θ).pow 2).inv (pow_ne_zero 2 hs)).sub_const
      (1 / Real.sin φ ^ 2)
    refine (h.congr_deriv ?_).hasDerivWithinAt.congr_of_mem (fun x _ => by simp [hf]) hθ
    simp only [Pi.pow_apply]
    field_simp
    ring
  have hlt : ∀ θ ∈ Ioo (0 : ℝ) φ, Real.sin θ < Real.sin φ := fun θ hθ =>
    Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [hθ.1, Real.pi_pos]) h1 hθ.2
  have hinj : InjOn f (Ioo 0 φ) := by
    intro a ha b hb hab
    have hsub : ∀ θ ∈ Ioo (0 : ℝ) φ, θ ∈ Icc (-(π / 2)) (π / 2) := fun θ hθ =>
      ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩
    have h2 : Real.sin a ^ 2 = Real.sin b ^ 2 := by
      have := hsinpos a ha; have := hsinpos b hb
      simp only [hf, sub_left_inj] at hab
      field_simp at hab
      linarith
    have h3 : Real.sin a = Real.sin b := by
      have := hsinpos a ha; have := hsinpos b hb
      nlinarith [sq_nonneg (Real.sin a - Real.sin b), sq_nonneg (Real.sin a + Real.sin b)]
    exact Real.injOn_sin (hsub a ha) (hsub b hb) h3
  have himg : f '' Ioo 0 φ = Ioi 0 := by
    ext t; constructor
    · rintro ⟨θ, hθ, rfl⟩
      have := hsinpos θ hθ; have := hlt θ hθ
      simp only [hf, mem_Ioi, sub_pos]
      exact one_div_lt_one_div_of_lt (by positivity)
        (pow_lt_pow_left₀ (hlt θ hθ) (hsinpos θ hθ).le two_ne_zero)
    · intro ht
      have ht0 : 0 < t := ht
      set u := t + 1 / Real.sin φ ^ 2 with hu
      have hu0 : 0 < u := by positivity
      set v := 1 / Real.sqrt u with hv
      have hv0 : 0 < v := by positivity
      have hvs : v < Real.sin φ := by
        rw [hv, div_lt_iff₀ (Real.sqrt_pos.mpr hu0)]
        have : 1 / Real.sin φ ^ 2 < u := by rw [hu]; linarith
        have h' : 1 < Real.sin φ ^ 2 * u := by
          rw [div_lt_iff₀ (by positivity)] at this; linarith
        have h'' : 1 < (Real.sin φ * Real.sqrt u) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hu0.le]; linarith
        exact lt_of_pow_lt_pow_left₀ 2 (by positivity) (by rw [one_pow]; exact h'')
      have hv1 : v ≤ 1 := le_trans hvs.le (Real.sin_le_one φ)
      refine ⟨Real.arcsin v, ⟨Real.arcsin_pos.mpr hv0, ?_⟩, ?_⟩
      · have := Real.arcsin_lt_arcsin (by linarith) hvs (Real.sin_le_one φ)
        rwa [Real.arcsin_sin (by linarith [Real.pi_pos]) h1] at this
      · simp only [hf]
        rw [Real.sin_arcsin (by linarith) hv1, hv, div_pow, Real.sq_sqrt hu0.le]
        rw [hu]
        field_simp
        ring
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj G
  rw [himg] at h
  rw [h]
  refine setIntegral_congr_fun measurableSet_Ioo fun θ hθ => ?_
  have := hsinpos θ hθ; have := hcospos θ hθ
  rw [abs_neg, abs_of_pos (by positivity), real_smul]

/-- `(r²)^{1/2} = r` for real `r ≥ 0`. -/
private lemma ofReal_sq_cpow_half {r : ℝ} (hr : 0 ≤ r) : ((r ^ 2 : ℝ) : ℂ) ^ (1 / 2 : ℂ) = r := by
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow (sq_nonneg r),
    ← Real.sqrt_eq_rpow, Real.sqrt_sq hr]

/-- Under the substitution: `√(t + c - w) = √(1 - w sin² θ)/sin θ` with `t = csc² θ - c`. -/
private lemma csc_sq_subst_cpow_half {θ : ℝ} (hs : 0 < Real.sin θ) (a : ℝ) (w : ℂ) :
    (((1 / Real.sin θ ^ 2 - a : ℝ) : ℂ) + ((a : ℂ) - w)) ^ (1 / 2 : ℂ) =
      (1 - w * (Real.sin θ : ℂ) ^ 2) ^ (1 / 2 : ℂ) * ((1 / Real.sin θ : ℝ) : ℂ) := by
  have hs0 : Complex.sin (θ : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_sin]; exact ofReal_ne_zero.mpr hs.ne'
  have e : ((1 / Real.sin θ ^ 2 - a : ℝ) : ℂ) + ((a : ℂ) - w) =
      (((1 / Real.sin θ) ^ 2 : ℝ) : ℂ) * (1 - w * (Real.sin θ : ℂ) ^ 2) := by
    push_cast; field_simp; ring
  rw [e, ofReal_mul_cpow_of_pos (by positivity), ofReal_sq_cpow_half (by positivity),
    mul_comm]

/-- `(1 - sin² θ)^{1/2} = cos θ` when `cos θ > 0`. -/
private lemma one_sub_one_mul_sin_sq_cpow_half {θ : ℝ} (hc : 0 < Real.cos θ) :
    (1 - 1 * (Real.sin θ : ℂ) ^ 2) ^ (1 / 2 : ℂ) = Real.cos θ := by
  have : (1 - 1 * (Real.sin θ : ℂ) ^ 2) = ((Real.cos θ ^ 2 : ℝ) : ℂ) := by
    push_cast
    have := Complex.sin_sq_add_cos_sq (θ : ℂ); linear_combination -this
  rw [this, ofReal_sq_cpow_half hc.le]

/-- The pointwise form of `symEllIntS (c - 1) (c - k²) c` under the substitution. -/
lemma symEllIntS_csc_sq_subst {φ θ : ℝ} (hs : 0 < Real.sin θ) (hc : 0 < Real.cos θ) (k : ℂ) :
    symEllIntS (((1 / Real.sin φ ^ 2 : ℝ) : ℂ) - 1) (((1 / Real.sin φ ^ 2 : ℝ) : ℂ) - k ^ 2)
        ((1 / Real.sin φ ^ 2 : ℝ) : ℂ) (1 / Real.sin θ ^ 2 - 1 / Real.sin φ ^ 2) =
      (Real.cos θ : ℂ) * (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (1 / 2 : ℂ) *
        ((1 / Real.sin θ ^ 3 : ℝ) : ℂ) := by
  have h1 := csc_sq_subst_cpow_half hs (1 / Real.sin φ ^ 2) 1
  have h2 := csc_sq_subst_cpow_half hs (1 / Real.sin φ ^ 2) (k ^ 2)
  have h3 := csc_sq_subst_cpow_half hs (1 / Real.sin φ ^ 2) 0
  rw [one_sub_one_mul_sin_sq_cpow_half hc] at h1
  simp only [zero_mul, sub_zero, one_cpow, one_mul] at h3
  simp only [symEllIntS]
  rw [h1, h2, h3]
  have hs0 : (Real.sin θ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
  push_cast
  field_simp

/-- **DLMF 19.25.5 at the level of integrals**: for real `0 < φ ≤ π/2`, `c = csc² φ` and every
complex `k`, `R_F(c - 1, c - k², c) = ∫₀^φ (1 - k² sin² θ)^{-1/2} dθ`. -/
theorem symEllIntRF_csc_sq_eq_integral {φ : ℝ} (h0 : 0 < φ) (h1 : φ ≤ π / 2) (k : ℂ) :
    symEllIntRF (((1 / Real.sin φ ^ 2 : ℝ) : ℂ) - 1) (((1 / Real.sin φ ^ 2 : ℝ) : ℂ) - k ^ 2)
        ((1 / Real.sin φ ^ 2 : ℝ) : ℂ) =
      ∫ θ in (0 : ℝ)..φ, (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) := by
  rw [symEllIntRF, integral_Ioi_eq_integral_Ioo_csc_sq_subst h0 h1, intervalIntegral.integral_of_le h0.le,
    integral_Ioc_eq_integral_Ioo, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo fun θ hθ => ?_
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hc : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩
  rw [symEllIntS_csc_sq_subst hs hc k, cpow_neg]
  generalize (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (1 / 2 : ℂ) = V
  have hs0 : Complex.sin (θ : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_sin]; exact ofReal_ne_zero.mpr hs.ne'
  have hc0 : Complex.cos (θ : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_cos]; exact ofReal_ne_zero.mpr hc.ne'
  push_cast
  by_cases hV : V = 0
  · simp [hV]
  · field_simp

/-- **DLMF 19.25.13 at the level of integrals**: `R_D(c - 1, c - k², c) =
3 ∫₀^φ sin² θ (1 - k² sin² θ)^{-1/2} dθ` for real `0 < φ ≤ π/2`, every complex `k`. -/
theorem symEllIntRD_csc_sq_eq_integral {φ : ℝ} (h0 : 0 < φ) (h1 : φ ≤ π / 2) (k : ℂ) :
    symEllIntRD (((1 / Real.sin φ ^ 2 : ℝ) : ℂ) - 1) (((1 / Real.sin φ ^ 2 : ℝ) : ℂ) - k ^ 2)
        ((1 / Real.sin φ ^ 2 : ℝ) : ℂ) =
      3 * ∫ θ in (0 : ℝ)..φ,
        (Real.sin θ : ℂ) ^ 2 * (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) := by
  have hsφ : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
  rw [symEllIntRD_eq_integral (not_isNegReal_of_mem_slitPlane
      (ofReal_mem_slitPlane.mpr (by positivity))),
    integral_Ioi_eq_integral_Ioo_csc_sq_subst h0 h1, intervalIntegral.integral_of_le h0.le,
    integral_Ioc_eq_integral_Ioo, ← integral_const_mul, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo fun θ hθ => ?_
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hc : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩
  rw [symEllIntS_csc_sq_subst hs hc k, cpow_neg]
  have e : (((1 / Real.sin θ ^ 2 - 1 / Real.sin φ ^ 2 : ℝ) : ℂ) + ((1 / Real.sin φ ^ 2 : ℝ) : ℂ))
      = ((1 / Real.sin θ ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [e]
  generalize (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (1 / 2 : ℂ) = V
  have hs0 : Complex.sin (θ : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_sin]; exact ofReal_ne_zero.mpr hs.ne'
  have hc0 : Complex.cos (θ : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_cos]; exact ofReal_ne_zero.mpr hc.ne'
  push_cast
  by_cases hV : V = 0
  · simp [hV]
  · field_simp

/-- **DLMF 19.25.14 at the level of integrals**: `R_J(c - 1, c - k², c, c - α²) =
3 ∫₀^φ sin² θ (1 - α² sin² θ)⁻¹ (1 - k² sin² θ)^{-1/2} dθ` for real `0 < φ ≤ π/2`, every complex
`k`, and `c - α²` not a negative real (no principal value). -/
theorem symEllIntRJ_csc_sq_eq_integral {φ : ℝ} (h0 : 0 < φ) (h1 : φ ≤ π / 2) (k α2 : ℂ)
    (hα : ¬ IsNegReal (((1 / Real.sin φ ^ 2 : ℝ) : ℂ) - α2)) :
    symEllIntRJ (((1 / Real.sin φ ^ 2 : ℝ) : ℂ) - 1) (((1 / Real.sin φ ^ 2 : ℝ) : ℂ) - k ^ 2)
        ((1 / Real.sin φ ^ 2 : ℝ) : ℂ) (((1 / Real.sin φ ^ 2 : ℝ) : ℂ) - α2) =
      3 * ∫ θ in (0 : ℝ)..φ, (Real.sin θ : ℂ) ^ 2 * (1 - α2 * (Real.sin θ : ℂ) ^ 2)⁻¹ *
        (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) := by
  rw [symEllIntRJ]
  simp only [hα, ↓reduceIte]
  rw [integral_Ioi_eq_integral_Ioo_csc_sq_subst h0 h1,
    intervalIntegral.integral_of_le h0.le, integral_Ioc_eq_integral_Ioo, ← integral_const_mul,
    ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo fun θ hθ => ?_
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hc : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩
  rw [symEllIntS_csc_sq_subst hs hc k, cpow_neg]
  have e : (((1 / Real.sin θ ^ 2 - 1 / Real.sin φ ^ 2 : ℝ) : ℂ) +
      (((1 / Real.sin φ ^ 2 : ℝ) : ℂ) - α2)) =
      (1 - α2 * (Real.sin θ : ℂ) ^ 2) / (Real.sin θ : ℂ) ^ 2 := by
    have hs0 : Complex.sin (θ : ℂ) ≠ 0 := by
      rw [← Complex.ofReal_sin]; exact ofReal_ne_zero.mpr hs.ne'
    push_cast; field_simp; ring
  rw [e]
  generalize (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (1 / 2 : ℂ) = V
  generalize (1 - α2 * (Real.sin θ : ℂ) ^ 2) = A
  have hs0 : Complex.sin (θ : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_sin]; exact ofReal_ne_zero.mpr hs.ne'
  have hc0 : Complex.cos (θ : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_cos]; exact ofReal_ne_zero.mpr hc.ne'
  push_cast
  by_cases hV : V = 0
  · simp [hV]
  by_cases hA : A = 0
  · simp [hA]
  field_simp

/-- For `0 ≤ θ ≤ φ ≤ π/2`, `1 - k² sin² θ` lies on the segment from `1` to `1 - k² sin² φ`, so it
is in the slit plane when `1 - k² sin² φ` is. -/
private lemma one_sub_mul_sin_sq_mem_slitPlane_of_le {φ θ : ℝ} (h1 : φ ≤ π / 2) {w : ℂ}
    (hk : 1 - w * (Real.sin φ : ℂ) ^ 2 ∈ slitPlane) (hθ0 : 0 ≤ θ) (hθ : θ ≤ φ) :
    1 - w * (Real.sin θ : ℂ) ^ 2 ∈ slitPlane := by
  have hs0 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ0 (by linarith [Real.pi_pos])
  have hsle : Real.sin θ ≤ Real.sin φ :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) h1 hθ
  rcases eq_or_lt_of_le hs0 with h | hpos
  · rw [← h]; simp
  have hsφ : 0 < Real.sin φ := lt_of_lt_of_le hpos hsle
  set t : ℝ := Real.sin θ ^ 2 / Real.sin φ ^ 2 with ht
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 := by
    rw [ht, div_le_one (by positivity)]; gcongr
  have := starConvex_one_slitPlane.add_smul_mem (y := -(w * (Real.sin φ : ℂ) ^ 2))
    (by rw [← sub_eq_add_neg]; exact hk) ht0 ht1
  convert this using 1
  rw [Complex.real_smul, ht]
  have : Complex.sin (φ : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_sin]; exact ofReal_ne_zero.mpr hsφ.ne'
  push_cast
  field_simp
  ring

/-- The function `(fun θ : ℝ => (1 - w * (Real.sin θ : ℂ) ^ 2) ^ s)` is continuous on `(uIcc 0
φ)`. -/
private lemma continuousOn_one_sub_mul_sin_sq_cpow {φ : ℝ} (h0 : 0 ≤ φ) (h1 : φ ≤ π / 2) {w : ℂ}
    (hk : 1 - w * (Real.sin φ : ℂ) ^ 2 ∈ slitPlane) (s : ℂ) :
    ContinuousOn (fun θ : ℝ => (1 - w * (Real.sin θ : ℂ) ^ 2) ^ s) (uIcc 0 φ) := by
  intro θ hθ
  rw [uIcc_of_le h0] at hθ
  refine ContinuousAt.continuousWithinAt ?_
  exact ContinuousAt.cpow (by fun_prop) continuousAt_const
    (one_sub_mul_sin_sq_mem_slitPlane_of_le h1 hk hθ.1 hθ.2)

/-- `E(φ, k) = F(φ, k) - k² D(φ, k)` for real `0 ≤ φ ≤ π/2` and `1 - k² sin² φ ∈ ℂ \ (-∞, 0]`. -/
theorem incEllIntEk_eq_incEllIntFk_sub {φ : ℝ} (h0 : 0 ≤ φ) (h1 : φ ≤ π / 2) {k : ℂ}
    (hk : 1 - k ^ 2 * (Real.sin φ : ℂ) ^ 2 ∈ slitPlane) :
    incEllIntEk φ k = incEllIntFk φ k - k ^ 2 * incEllIntDk φ k := by
  rw [incEllIntEk_ofReal_eq_integral, incEllIntFk_ofReal_eq_integral,
    incEllIntDk_ofReal_eq_integral, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub]
  · refine intervalIntegral.integral_congr fun θ hθ => ?_
    have hm : 1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2 ∈ slitPlane := by
      rw [uIcc_of_le h0] at hθ; exact one_sub_mul_sin_sq_mem_slitPlane_of_le h1 hk hθ.1 hθ.2
    have hne := slitPlane_ne_zero hm
    generalize hA : (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) = A at hne ⊢
    have : A ^ (1 / 2 : ℂ) = A * A ^ (-(1 / 2 : ℂ)) := by
      have : A ^ (1 / 2 : ℂ) ≠ 0 := by
        rw [Ne, cpow_eq_zero_iff]; tauto
      rw [cpow_neg, eq_mul_inv_iff_mul_eq₀ this, cpow_half_mul_cpow_half]
    rw [this]
    subst hA
    ring
  · exact (continuousOn_one_sub_mul_sin_sq_cpow h0 h1 hk _).intervalIntegrable
  · refine ContinuousOn.intervalIntegrable ?_
    exact continuousOn_const.mul ((Continuous.continuousOn (by fun_prop)).mul
      (continuousOn_one_sub_mul_sin_sq_cpow h0 h1 hk _))

/-- For real `0 ≤ φ ≤ π/2` and `1 - α² sin² φ ∈ ℂ \ (-∞, 0]`, the principal value in `Π` is not
needed: `Π(φ, α², k) = ∫₀^φ (1 - α² sin²θ)⁻¹ (1 - k² sin²θ)^{-1/2} dθ`. -/
private lemma incEllIntPik_eq_integral_of_mem_slitPlane {φ : ℝ} (h0 : 0 ≤ φ) (h1 : φ ≤ π / 2) {α2 : ℂ}
    (hα : 1 - α2 * (Real.sin φ : ℂ) ^ 2 ∈ slitPlane) (k : ℂ) :
    incEllIntPik φ α2 k = ∫ θ in (0 : ℝ)..φ, ((1 - α2 * (Real.sin θ : ℂ) ^ 2)⁻¹ *
      (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))) := by
  set g : ℝ → ℝ := fun t => ‖1 - α2 * (Real.sin (t * φ) : ℂ) ^ 2‖ with hg
  have hgc : ContinuousOn g (Icc 0 1) := (Continuous.continuousOn (by fun_prop))
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, 1 - α2 * (Real.sin (t * φ) : ℂ) ^ 2 ∈ slitPlane := by
    intro t ht
    exact one_sub_mul_sin_sq_mem_slitPlane_of_le h1 hα (mul_nonneg ht.1 h0)
      (by nlinarith [ht.1, ht.2])
  obtain ⟨t0, ht0, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr zero_le_one) hgc
  have hδ : 0 < g t0 := norm_pos_iff.mpr (slitPlane_ne_zero (hmem t0 ht0))
  rw [incEllIntPik_eq_segmentIntegral (δ := g t0) hδ, segmentIntegral_ofReal]
  · simp only [← Complex.ofReal_sin]
  · intro t ht
    have := hmin ht
    simp only [hg] at this
    simpa [← Complex.ofReal_sin, ← Complex.ofReal_mul] using this

/-- The function `(fun θ : ℝ => (1 - α2 * (Real.sin θ : ℂ) ^ 2)⁻¹)` is continuous on `(uIcc 0 φ)`. -/
private lemma continuousOn_inv_one_sub_mul_sin_sq {φ : ℝ} (h0 : 0 ≤ φ) (h1 : φ ≤ π / 2) {α2 : ℂ}
    (hα : 1 - α2 * (Real.sin φ : ℂ) ^ 2 ∈ slitPlane) :
    ContinuousOn (fun θ : ℝ => (1 - α2 * (Real.sin θ : ℂ) ^ 2)⁻¹) (uIcc 0 φ) := by
  intro θ hθ
  rw [uIcc_of_le h0] at hθ
  refine ContinuousAt.continuousWithinAt ?_
  exact ContinuousAt.inv₀ (by fun_prop)
    (slitPlane_ne_zero (one_sub_mul_sin_sq_mem_slitPlane_of_le h1 hα hθ.1 hθ.2))

/-- `Π(φ, α², k) - F(φ, k) = α² ∫₀^φ sin²θ (1 - α² sin²θ)⁻¹ (1 - k² sin²θ)^{-1/2} dθ`. -/
theorem incEllIntPik_sub_incEllIntFk_eq_integral {φ : ℝ} (h0 : 0 ≤ φ) (h1 : φ ≤ π / 2) {k α2 : ℂ}
    (hk : 1 - k ^ 2 * (Real.sin φ : ℂ) ^ 2 ∈ slitPlane)
    (hα : 1 - α2 * (Real.sin φ : ℂ) ^ 2 ∈ slitPlane) :
    incEllIntPik φ α2 k - incEllIntFk φ k = α2 * ∫ θ in (0 : ℝ)..φ,
      (Real.sin θ : ℂ) ^ 2 * (1 - α2 * (Real.sin θ : ℂ) ^ 2)⁻¹ *
        (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) := by
  rw [incEllIntPik_eq_integral_of_mem_slitPlane h0 h1 hα, incEllIntFk_ofReal_eq_integral,
    ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub]
  · refine intervalIntegral.integral_congr fun θ hθ => ?_
    have hm : 1 - α2 * (Real.sin θ : ℂ) ^ 2 ∈ slitPlane := by
      rw [uIcc_of_le h0] at hθ; exact one_sub_mul_sin_sq_mem_slitPlane_of_le h1 hα hθ.1 hθ.2
    have hne := slitPlane_ne_zero hm
    generalize (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) = V
    field_simp
    ring
  · refine ContinuousOn.intervalIntegrable ?_
    exact (continuousOn_inv_one_sub_mul_sin_sq h0 h1 hα).mul (continuousOn_one_sub_mul_sin_sq_cpow h0 h1 hk _)
  · exact (continuousOn_one_sub_mul_sin_sq_cpow h0 h1 hk _).intervalIntegrable

/-- `c = csc² φ ≥ 1` for `0 < φ ≤ π/2`. -/
private lemma one_le_csc_sq {φ : ℝ} (h0 : 0 < φ) (h1 : φ ≤ π / 2) :
    1 ≤ 1 / Real.sin φ ^ 2 := by
  have hs : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
  rw [le_div_iff₀ (by positivity), one_mul]
  nlinarith [Real.sin_le_one φ]

/-- Estimate under the stated parameter and domain assumptions: `1 < 1 / Real.sin φ ^ 2`. -/
private lemma one_lt_csc_sq {φ : ℝ} (h0 : 0 < φ) (h1 : φ < π / 2) :
    1 < 1 / Real.sin φ ^ 2 := by
  have hs : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
  have hs1 : Real.sin φ < 1 := by
    rw [← Real.sin_pi_div_two]
    exact Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) le_rfl h1
  rw [lt_div_iff₀ (by positivity), one_mul]
  nlinarith

/-- Formula under the stated hypotheses: `((1 / Real.sin φ ^ 2 : ℝ) : ℂ) ∈ slitPlane`. -/
theorem csc_sq_mem_slitPlane {φ : ℝ} (h0 : 0 < φ) (h1 : φ ≤ π / 2) :
    ((1 / Real.sin φ ^ 2 : ℝ) : ℂ) ∈ slitPlane :=
  ofReal_mem_slitPlane.mpr (lt_of_lt_of_le one_pos (one_le_csc_sq h0 h1))

/-- The stated relation follows from the given hypotheses: `SymEllIntArg (((1 / Real.sin φ ^ 2 :
ℝ) : ℂ) - 1)`. -/
theorem symEllIntArg_csc_sq_sub_one {φ : ℝ} (h0 : 0 < φ) (h1 : φ ≤ π / 2) :
    SymEllIntArg (((1 / Real.sin φ ^ 2 : ℝ) : ℂ) - 1) := by
  rcases eq_or_lt_of_le (one_le_csc_sq h0 h1) with h | h
  · right; rw [← h]; simp
  · left
    rw [show ((1 / Real.sin φ ^ 2 : ℝ) : ℂ) - 1 = ((1 / Real.sin φ ^ 2 - 1 : ℝ) : ℂ) by
      push_cast; ring]
    exact ofReal_mem_slitPlane.mpr (by linarith)

/-- Formula under the stated hypotheses: `((1 / Real.sin φ ^ 2 : ℝ) : ℂ) - 1 ∈ slitPlane`. -/
theorem csc_sq_sub_one_mem_slitPlane {φ : ℝ} (h0 : 0 < φ) (h1 : φ < π / 2) :
    ((1 / Real.sin φ ^ 2 : ℝ) : ℂ) - 1 ∈ slitPlane := by
  rw [show ((1 / Real.sin φ ^ 2 : ℝ) : ℂ) - 1 = ((1 / Real.sin φ ^ 2 - 1 : ℝ) : ℂ) by
    push_cast; ring]
  exact ofReal_mem_slitPlane.mpr (by linarith [one_lt_csc_sq h0 h1])

/-- `c - w = c (1 - w sin² φ)` is in the slit plane when `1 - w sin² φ` is. -/
theorem csc_sq_sub_mem_slitPlane {φ : ℝ} (h0 : 0 < φ) (h1 : φ ≤ π / 2) {w : ℂ}
    (hw : 1 - w * (Real.sin φ : ℂ) ^ 2 ∈ slitPlane) :
    ((1 / Real.sin φ ^ 2 : ℝ) : ℂ) - w ∈ slitPlane := by
  have hs : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
  have e : ((1 / Real.sin φ ^ 2 : ℝ) : ℂ) - w =
      ((1 / Real.sin φ ^ 2 : ℝ) : ℂ) * (1 - w * (Real.sin φ : ℂ) ^ 2) := by
    have : Complex.sin (φ : ℂ) ≠ 0 := by
      rw [← Complex.ofReal_sin]; exact ofReal_ne_zero.mpr hs.ne'
    push_cast; field_simp
  rw [e]
  set r : ℝ := 1 / Real.sin φ ^ 2
  have hr : 0 < r := by positivity
  rcases mem_slitPlane_iff.mp hw with h | h
  · exact mem_slitPlane_iff.mpr (Or.inl (by simpa using mul_pos hr h))
  · exact mem_slitPlane_iff.mpr (Or.inr (by simpa using And.intro hr.ne' h))

/-- Identity under the stated parameter and domain assumptions: `((1 / Real.sin (π / 2) ^ 2 : ℝ) :
ℂ) = 1`. -/
theorem csc_sq_pi_div_two : ((1 / Real.sin (π / 2) ^ 2 : ℝ) : ℂ) = 1 := by
  simp [Real.sin_pi_div_two]

/-- DLMF 19.25.13 with explicit `c = csc² φ`, every complex `k`. -/
theorem incEllIntDk_eq_one_third_symEllIntRD {φ : ℝ} (h0 : 0 < φ) (h1 : φ ≤ π / 2) (k : ℂ) :
    incEllIntDk φ k = (1 / 3) * symEllIntRD (((1 / Real.sin φ ^ 2 : ℝ) : ℂ) - 1)
      (((1 / Real.sin φ ^ 2 : ℝ) : ℂ) - k ^ 2) ((1 / Real.sin φ ^ 2 : ℝ) : ℂ) := by
  rw [symEllIntRD_csc_sq_eq_integral h0 h1 k, incEllIntDk_ofReal_eq_integral]
  ring

/-- DLMF 19.25.9 with explicit `c = csc² φ`. -/
theorem incEllIntEk_eq_symEllIntRF_sub_one_third_symEllIntRD {φ : ℝ} (h0 : 0 < φ) (h1 : φ ≤ π / 2) {k : ℂ}
    (hk : 1 - k ^ 2 * (Real.sin φ : ℂ) ^ 2 ∈ slitPlane) :
    incEllIntEk φ k = symEllIntRF (((1 / Real.sin φ ^ 2 : ℝ) : ℂ) - 1)
        (((1 / Real.sin φ ^ 2 : ℝ) : ℂ) - k ^ 2) ((1 / Real.sin φ ^ 2 : ℝ) : ℂ) -
      (1 / 3) * k ^ 2 * symEllIntRD (((1 / Real.sin φ ^ 2 : ℝ) : ℂ) - 1)
        (((1 / Real.sin φ ^ 2 : ℝ) : ℂ) - k ^ 2) ((1 / Real.sin φ ^ 2 : ℝ) : ℂ) := by
  rw [incEllIntEk_eq_incEllIntFk_sub h0.le h1 hk, incEllIntDk_eq_one_third_symEllIntRD h0 h1,
    incEllIntFk_ofReal_eq_integral, ← symEllIntRF_csc_sq_eq_integral h0 h1 k]
  ring

/-- DLMF 19.25.8 with explicit `c = csc² φ`, real `0 < φ < π/2`. -/
theorem incEllIntEk_eq_symEllIntR_csc_sq {φ : ℝ} (h0 : 0 < φ) (h1 : φ < π / 2) {k : ℂ}
    (hk : 1 - k ^ 2 * (Real.sin φ : ℂ) ^ 2 ∈ slitPlane) :
    incEllIntEk φ k = symEllIntR (1 / 2) ![1 / 2, -1 / 2, 3 / 2]
      ![((1 / Real.sin φ ^ 2 : ℝ) : ℂ) - 1, ((1 / Real.sin φ ^ 2 : ℝ) : ℂ) - k ^ 2,
        ((1 / Real.sin φ ^ 2 : ℝ) : ℂ)] := by
  have hx := csc_sq_sub_one_mem_slitPlane h0 h1
  have hy := csc_sq_sub_mem_slitPlane h0 h1.le hk
  have hz := csc_sq_mem_slitPlane h0 h1.le
  rw [symEllIntR_eq_integral (a' := 1) (by norm_num) (by norm_num)
    (by simp [Fin.sum_univ_three]; try norm_num) (vec3_mem_carlsonRSlitDomain hx hy hz),
    inv_betaIntegral (by norm_num) (by norm_num)]
  simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, sub_self, cpow_zero, one_mul, Gamma_one, mul_one]
  rw [show (1 / 2 : ℂ) + 1 = 3 / 2 by norm_num, Carlson.Gamma_three_halves,
    mul_div_assoc, div_self Gamma_one_half_ne_zero, mul_one]
  rw [integral_Ioi_eq_integral_Ioo_csc_sq_subst h0 h1.le, incEllIntEk_ofReal_eq_integral,
    intervalIntegral.integral_of_le h0.le, integral_Ioc_eq_integral_Ioo, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo fun θ hθ => ?_
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hc : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩
  have h1' := csc_sq_subst_cpow_half hs (1 / Real.sin φ ^ 2) 1
  have h2' := csc_sq_subst_cpow_half hs (1 / Real.sin φ ^ 2) (k ^ 2)
  have h3' := csc_sq_subst_cpow_half hs (1 / Real.sin φ ^ 2) 0
  rw [one_sub_one_mul_sin_sq_cpow_half hc] at h1'
  simp only [zero_mul, sub_zero, one_cpow, one_mul] at h3'
  have hZ : ((1 / Real.sin θ ^ 2 - 1 / Real.sin φ ^ 2 : ℝ) : ℂ) + ((1 / Real.sin φ ^ 2 : ℝ) : ℂ) =
      ((1 / Real.sin θ ^ 2 : ℝ) : ℂ) := by push_cast; ring
  have hZ0 : ((1 / Real.sin θ ^ 2 - 1 / Real.sin φ ^ 2 : ℝ) : ℂ) +
      ((1 / Real.sin φ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    rw [hZ]; exact ofReal_ne_zero.mpr (by positivity)
  rw [show -(-1 / 2 : ℂ) = 1 / 2 by norm_num, cpow_neg_three_halves_eq hZ0]
  simp only [cpow_neg]
  rw [h1', h2', h3', hZ]
  generalize (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (1 / 2 : ℂ) = V
  have hs0 : Complex.sin (θ : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_sin]; exact ofReal_ne_zero.mpr hs.ne'
  have hc0 : Complex.cos (θ : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_cos]; exact ofReal_ne_zero.mpr hc.ne'
  push_cast
  field_simp

/-- DLMF 19.25.15 with explicit `c = csc² φ`, real `0 < φ < π/2`. -/
theorem incEllIntPik_eq_symEllIntR_csc_sq {φ : ℝ} (h0 : 0 < φ) (h1 : φ < π / 2) {k α2 : ℂ}
    (hk : 1 - k ^ 2 * (Real.sin φ : ℂ) ^ 2 ∈ slitPlane)
    (hα : 1 - α2 * (Real.sin φ : ℂ) ^ 2 ∈ slitPlane) :
    incEllIntPik φ α2 k = symEllIntR (1 / 2) ![1 / 2, 1 / 2, -1 / 2, 1]
      ![((1 / Real.sin φ ^ 2 : ℝ) : ℂ) - 1, ((1 / Real.sin φ ^ 2 : ℝ) : ℂ) - k ^ 2,
        ((1 / Real.sin φ ^ 2 : ℝ) : ℂ), ((1 / Real.sin φ ^ 2 : ℝ) : ℂ) - α2] := by
  have hx := csc_sq_sub_one_mem_slitPlane h0 h1
  have hy := csc_sq_sub_mem_slitPlane h0 h1.le hk
  have hz := csc_sq_mem_slitPlane h0 h1.le
  have hp := csc_sq_sub_mem_slitPlane h0 h1.le hα
  rw [symEllIntR_eq_integral (a' := 1) (by norm_num) (by norm_num)
    (by simp [Fin.sum_univ_four]; try norm_num) (vec4_mem_carlsonRSlitDomain hx hy hz hp),
    inv_betaIntegral (by norm_num) (by norm_num)]
  simp only [Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, sub_self, cpow_zero, one_mul,
    Gamma_one, mul_one]
  rw [show (1 / 2 : ℂ) + 1 = 3 / 2 by norm_num, Carlson.Gamma_three_halves,
    mul_div_assoc, div_self Gamma_one_half_ne_zero, mul_one]
  rw [integral_Ioi_eq_integral_Ioo_csc_sq_subst h0 h1.le, incEllIntPik_eq_integral_of_mem_slitPlane h0.le h1.le hα,
    intervalIntegral.integral_of_le h0.le, integral_Ioc_eq_integral_Ioo, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo fun θ hθ => ?_
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hc : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩
  have h1' := csc_sq_subst_cpow_half hs (1 / Real.sin φ ^ 2) 1
  have h2' := csc_sq_subst_cpow_half hs (1 / Real.sin φ ^ 2) (k ^ 2)
  have h3' := csc_sq_subst_cpow_half hs (1 / Real.sin φ ^ 2) 0
  rw [one_sub_one_mul_sin_sq_cpow_half hc] at h1'
  simp only [zero_mul, sub_zero, one_cpow, one_mul] at h3'
  have hs0 : Complex.sin (θ : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_sin]; exact ofReal_ne_zero.mpr hs.ne'
  have hc0 : Complex.cos (θ : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_cos]; exact ofReal_ne_zero.mpr hc.ne'
  have e : (((1 / Real.sin θ ^ 2 - 1 / Real.sin φ ^ 2 : ℝ) : ℂ) +
      (((1 / Real.sin φ ^ 2 : ℝ) : ℂ) - α2)) =
      (1 - α2 * (Real.sin θ : ℂ) ^ 2) / (Real.sin θ : ℂ) ^ 2 := by
    push_cast; field_simp; ring
  rw [show -(-1 / 2 : ℂ) = 1 / 2 by norm_num, cpow_neg_one]
  simp only [cpow_neg]
  rw [h1', h2', h3', e]
  have hA : 1 - α2 * (Real.sin θ : ℂ) ^ 2 ≠ 0 :=
    slitPlane_ne_zero (one_sub_mul_sin_sq_mem_slitPlane_of_le h1.le hα hθ.1.le hθ.2.le)
  generalize (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (1 / 2 : ℂ) = V
  generalize (1 - α2 * (Real.sin θ : ℂ) ^ 2) = A at hA ⊢
  push_cast
  by_cases hV : V = 0
  · simp [hV]
  field_simp

/-- DLMF 19.25.3: `Π(α², k) = (π/2) R_{-1/2}(1/2, -1/2, 1; k'², 1, 1 - α²)`. -/
theorem compEllIntPik_eq_pi_div_two_mul_symEllIntR {k α2 : ℂ} (hk : 1 - k ^ 2 ∈ slitPlane)
    (hα : 1 - α2 ∈ slitPlane) :
    compEllIntPik α2 k =
      (π / 2) * symEllIntR (1 / 2) ![1 / 2, -1 / 2, 1] ![1 - k ^ 2, 1, 1 - α2] := by
  have hp : (0 : ℝ) < π / 2 := by positivity
  have hk' : 1 - k ^ 2 * (Real.sin (π / 2) : ℂ) ^ 2 ∈ slitPlane := by
    simpa [Real.sin_pi_div_two] using hk
  have hα' : 1 - α2 * (Real.sin (π / 2) : ℂ) ^ 2 ∈ slitPlane := by
    simpa [Real.sin_pi_div_two] using hα
  rw [symEllIntR_eq_integral (a' := 1 / 2) (by norm_num) (by norm_num)
    (by simp [Fin.sum_univ_three]; try norm_num) (vec3_mem_carlsonRSlitDomain hk one_mem_slitPlane hα),
    inv_betaIntegral (by norm_num) (by norm_num)]
  simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [show (1 / 2 : ℂ) + 1 / 2 = 1 by norm_num, Gamma_one, Complex.Gamma_one_half_eq,
    cpow_half_mul_cpow_half]
  rw [compEllIntPik, show ((π : ℂ) / 2) = ((π / 2 : ℝ) : ℂ) by push_cast; ring,
    incEllIntPik_eq_integral_of_mem_slitPlane hp.le le_rfl hα', integral_Ioi_eq_integral_Ioo_csc_sq_subst hp le_rfl,
    intervalIntegral.integral_of_le hp.le, integral_Ioc_eq_integral_Ioo, ← integral_const_mul,
    ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo fun θ hθ => ?_
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hc : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩
  have ha : (1 / Real.sin (π / 2) ^ 2 : ℝ) = 1 := by simp [Real.sin_pi_div_two]
  have h1' := csc_sq_subst_cpow_half hs 1 1
  have h2' := csc_sq_subst_cpow_half hs 1 (k ^ 2)
  have h3' := csc_sq_subst_cpow_half hs 1 0
  rw [one_sub_one_mul_sin_sq_cpow_half hc] at h1'
  simp only [zero_mul, sub_zero, one_cpow, one_mul, ofReal_one, sub_self, add_zero] at h1' h2' h3'
  have hs0 : Complex.sin (θ : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_sin]; exact ofReal_ne_zero.mpr hs.ne'
  have hc0 : Complex.cos (θ : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_cos]; exact ofReal_ne_zero.mpr hc.ne'
  have e : (((1 / Real.sin θ ^ 2 - 1 : ℝ) : ℂ) + (1 - α2)) =
      (1 - α2 * (Real.sin θ : ℂ) ^ 2) / (Real.sin θ : ℂ) ^ 2 := by
    push_cast; field_simp; ring
  rw [ha]
  rw [show -(-1 / 2 : ℂ) = 1 / 2 by norm_num, cpow_neg_one, show (1 / 2 : ℂ) - 1 = -(1 / 2) by
    norm_num]
  simp only [cpow_neg]
  rw [h1', h2', h3', e]
  have hA : 1 - α2 * (Real.sin θ : ℂ) ^ 2 ≠ 0 :=
    slitPlane_ne_zero (one_sub_mul_sin_sq_mem_slitPlane_of_le le_rfl hα' hθ.1.le hθ.2.le)
  generalize (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (1 / 2 : ℂ) = V
  generalize (1 - α2 * (Real.sin θ : ℂ) ^ 2) = A at hA ⊢
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_pos.ne'
  push_cast
  by_cases hV : V = 0
  · simp [hV]
  field_simp

/-! ### Homogeneity for all arguments (positive real scale) -/

/-- Identity under the stated parameter and domain assumptions: `∫ t in Ioi (0 : ℝ), g t = (l : ℂ)
* ∫ s in Ioi (0 : ℝ), g (l * s)`. -/
private lemma integral_Ioi_scale (g : ℝ → ℂ) {l : ℝ} (hl : 0 < l) :
    ∫ t in Ioi (0 : ℝ), g t = (l : ℂ) * ∫ s in Ioi (0 : ℝ), g (l * s) := by
  have h := integral_comp_mul_left_Ioi' g 0 hl
  rw [mul_zero] at h
  rw [← h, Complex.real_smul]

/-- Identity under the stated parameter and domain assumptions: `symEllIntS ((l : ℂ) * x) ((l : ℂ)
* y) ((l : ℂ) * z) (l * s) = ((l : ℂ) ^ (1 / 2 : ℂ)) ^ 3 * symEllIntS x y z s`. -/
private lemma symEllIntS_scale {l : ℝ} (hl : 0 < l) (x y z : ℂ) (s : ℝ) :
    symEllIntS ((l : ℂ) * x) ((l : ℂ) * y) ((l : ℂ) * z) (l * s) =
      ((l : ℂ) ^ (1 / 2 : ℂ)) ^ 3 * symEllIntS x y z s := by
  simp only [symEllIntS]
  have e : ∀ w : ℂ, ((l * s : ℝ) : ℂ) + (l : ℂ) * w = (l : ℂ) * ((s : ℂ) + w) := by
    intro w; push_cast; ring
  rw [e, e, e, ofReal_mul_cpow_of_pos hl, ofReal_mul_cpow_of_pos hl, ofReal_mul_cpow_of_pos hl]
  ring

/-- Identity under the stated parameter and domain assumptions: `((l : ℂ) ^ (1 / 2 : ℂ)) ^ 2 = l`. -/
theorem ofReal_cpow_half_sq {l : ℝ} : ((l : ℂ) ^ (1 / 2 : ℂ)) ^ 2 = l := by
  rw [sq, cpow_half_mul_cpow_half]

/-- Nonvanishing under the stated hypotheses: `(l : ℂ) ^ (1 / 2 : ℂ) ≠ 0`. -/
theorem ofReal_cpow_half_ne_zero {l : ℝ} (hl : 0 < l) : (l : ℂ) ^ (1 / 2 : ℂ) ≠ 0 := by
  rw [Ne, cpow_eq_zero_iff]; push Not; intro h; exact absurd h (ofReal_ne_zero.mpr hl.ne')

/-- `R_F(λx, λy, λz) = λ^{-1/2} R_F(x, y, z)` for real `λ > 0` and **all** complex arguments. -/
theorem symEllIntRF_scale {l : ℝ} (hl : 0 < l) (x y z : ℂ) :
    symEllIntRF ((l : ℂ) * x) ((l : ℂ) * y) ((l : ℂ) * z) =
      ((l : ℂ) ^ (1 / 2 : ℂ))⁻¹ * symEllIntRF x y z := by
  unfold symEllIntRF
  rw [integral_Ioi_scale _ hl]
  simp_rw [symEllIntS_scale hl, mul_inv]
  rw [integral_const_mul]
  have hL := ofReal_cpow_half_sq (l := l)
  have hL0 := ofReal_cpow_half_ne_zero hl
  generalize (l : ℂ) ^ (1 / 2 : ℂ) = L at hL hL0 ⊢
  rw [← hL]
  field_simp

/-- `R_J(λx, λy, λz, λp) = λ^{-3/2} R_J(x, y, z, p)` for real `λ > 0`, all `x, y, z` and `p` not a
negative real. -/
theorem symEllIntRJ_scale {l : ℝ} (hl : 0 < l) (x y z p : ℂ) (hp : ¬ IsNegReal p) :
    symEllIntRJ ((l : ℂ) * x) ((l : ℂ) * y) ((l : ℂ) * z) ((l : ℂ) * p) =
      (((l : ℂ) ^ (1 / 2 : ℂ)) ^ 3)⁻¹ * symEllIntRJ x y z p := by
  have hp' : ¬ IsNegReal ((l : ℂ) * p) := by
    rintro ⟨h1, h2⟩
    apply hp
    simp only [mul_im, ofReal_re, ofReal_im, zero_mul, add_zero, mul_re, sub_zero] at h1 h2
    exact ⟨by
      rcases mul_eq_zero.mp h1 with h | h
      · exact absurd h hl.ne'
      · exact h, by nlinarith⟩
  unfold symEllIntRJ
  simp only [hp, hp', ↓reduceIte]
  rw [integral_Ioi_scale _ hl]
  have e : ∀ s : ℝ, ((l * s : ℝ) : ℂ) + (l : ℂ) * p = (l : ℂ) * ((s : ℂ) + p) := by
    intro s; push_cast; ring
  simp_rw [symEllIntS_scale hl, e, mul_inv]
  have hL := ofReal_cpow_half_sq (l := l)
  have hL0 := ofReal_cpow_half_ne_zero hl
  have hl0 : (l : ℂ) ≠ 0 := ofReal_ne_zero.mpr hl.ne'
  have : ∀ s : ℝ, ((((l : ℂ) ^ (1 / 2 : ℂ)) ^ 3)⁻¹ * (symEllIntS x y z s)⁻¹ * ((l : ℂ)⁻¹ *
      ((s : ℂ) + p)⁻¹)) = (((l : ℂ) ^ (1 / 2 : ℂ)) ^ 3)⁻¹ * (l : ℂ)⁻¹ *
        ((symEllIntS x y z s)⁻¹ * ((s : ℂ) + p)⁻¹) := fun s => by ring
  simp_rw [this]
  rw [integral_const_mul]
  field_simp

/-- `R_D(λx, λy, λz) = λ^{-3/2} R_D(x, y, z)` for real `λ > 0`, `z` not a negative real. -/
theorem symEllIntRD_scale {l : ℝ} (hl : 0 < l) (x y z : ℂ) (hz : ¬ IsNegReal z) :
    symEllIntRD ((l : ℂ) * x) ((l : ℂ) * y) ((l : ℂ) * z) =
      (((l : ℂ) ^ (1 / 2 : ℂ)) ^ 3)⁻¹ * symEllIntRD x y z :=
  symEllIntRJ_scale hl x y z z hz

/-- `R_G(λx, λy, λz) = λ^{1/2} R_G(x, y, z)` for real `λ > 0` and all complex arguments. -/
theorem symEllIntRG_scale {l : ℝ} (hl : 0 < l) (x y z : ℂ) :
    symEllIntRG ((l : ℂ) * x) ((l : ℂ) * y) ((l : ℂ) * z) =
      (l : ℂ) ^ (1 / 2 : ℂ) * symEllIntRG x y z := by
  unfold symEllIntRG
  rw [integral_Ioi_scale _ hl]
  have hL := ofReal_cpow_half_sq (l := l)
  have hL0 := ofReal_cpow_half_ne_zero hl
  have hl0 : (l : ℂ) ≠ 0 := ofReal_ne_zero.mpr hl.ne'
  have e : ∀ s : ℝ, ∀ w : ℂ, (l : ℂ) * w / (((l * s : ℝ) : ℂ) + (l : ℂ) * w) =
      w / ((s : ℂ) + w) := by
    intro s w
    rw [show ((l * s : ℝ) : ℂ) + (l : ℂ) * w = (l : ℂ) * ((s : ℂ) + w) by push_cast; ring,
      mul_div_mul_left _ _ hl0]
  have : ∀ s : ℝ, (symEllIntS ((l : ℂ) * x) ((l : ℂ) * y) ((l : ℂ) * z) (l * s))⁻¹ *
      ((l : ℂ) * x / (((l * s : ℝ) : ℂ) + (l : ℂ) * x) +
        (l : ℂ) * y / (((l * s : ℝ) : ℂ) + (l : ℂ) * y) +
        (l : ℂ) * z / (((l * s : ℝ) : ℂ) + (l : ℂ) * z)) * ((l * s : ℝ) : ℂ) =
      ((((l : ℂ) ^ (1 / 2 : ℂ)) ^ 3)⁻¹ * l) * ((symEllIntS x y z s)⁻¹ *
        (x / ((s : ℂ) + x) + y / ((s : ℂ) + y) + z / ((s : ℂ) + z)) * s) := by
    intro s
    rw [e, e, e, symEllIntS_scale hl]
    push_cast
    ring
  simp_rw [this]
  rw [integral_const_mul]
  generalize (l : ℂ) ^ (1 / 2 : ℂ) = L at hL hL0 ⊢
  rw [← hL]
  field_simp

/-! ### §19.25(iii): the parametrization `sin² φ = (z - x)/z`, `k² = (z - y)/(z - x)` -/

/-- Estimate under the stated parameter and domain assumptions: `0 < Real.arccos √(x / z) ∧
Real.arccos √(x / z) ≤ π / 2 ∧ 1 / Real.sin (Real.arccos √(x / z)) ^ 2 = z / (z - x)`. -/
private lemma arccos_sqrt_div_mem_and_csc_sq {x z : ℝ} (hx : 0 ≤ x) (hxz : x < z) :
    0 < Real.arccos √(x / z) ∧ Real.arccos √(x / z) ≤ π / 2 ∧
      1 / Real.sin (Real.arccos √(x / z)) ^ 2 = z / (z - x) := by
  have hz : 0 < z := lt_of_le_of_lt hx hxz
  have hxz' : x / z < 1 := (div_lt_one hz).mpr hxz
  have hxz0 : 0 ≤ x / z := div_nonneg hx hz.le
  refine ⟨Real.arccos_pos.mpr ?_, Real.arccos_le_pi_div_two.mpr (Real.sqrt_nonneg _), ?_⟩
  · rw [Real.sqrt_lt' one_pos]; simpa using hxz'
  · rw [Real.sin_arccos, Real.sq_sqrt (by rw [Real.sq_sqrt hxz0]; linarith),
      Real.sq_sqrt hxz0]
    have : z - x ≠ 0 := by linarith
    field_simp

/-- Identity under the stated parameter and domain assumptions: `(w : ℂ) = ((z - x : ℝ) : ℂ) * ((c
: ℂ) - (((z - w) / (z - x) : ℝ) : ℂ))`. -/
theorem ofReal_eq_sub_mul_csc_sq_sub {x z w : ℝ} (hxz : x < z) (c : ℝ) (hc : c = z / (z - x)) :
    (w : ℂ) = ((z - x : ℝ) : ℂ) * ((c : ℂ) - (((z - w) / (z - x) : ℝ) : ℂ)) := by
  have : (z - x : ℝ) ≠ 0 := by linarith
  have : ((z : ℂ) - x) ≠ 0 := by exact_mod_cast this
  subst hc
  push_cast
  field_simp
  ring

/-- Identity under the stated parameter and domain assumptions: `((√r : ℝ) : ℂ) ^ 2 = (r : ℂ)`. -/
theorem ofReal_sqrt_sq_of_nonneg {r : ℝ} (hr : 0 ≤ r) : ((√r : ℝ) : ℂ) ^ 2 = (r : ℂ) := by
  rw [← ofReal_pow, Real.sq_sqrt hr]

/-- Identity under the stated parameter and domain assumptions: `((√r : ℝ) : ℂ) = (r : ℂ) ^ (1 / 2
: ℂ)`. -/
theorem ofReal_sqrt_eq_cpow_half {r : ℝ} (hr : 0 ≤ r) : ((√r : ℝ) : ℂ) = (r : ℂ) ^ (1 / 2 : ℂ) := by
  rw [Real.sqrt_eq_rpow, ofReal_cpow hr]; push_cast; ring_nf

/-- The data of §19.25(iii) as complex scalings: `x = (z - x)(c - 1)`, `y = (z - x)(c - k²)`,
`z = (z - x) c`, with `c = csc² φ`, plus `sin² φ = (z - x)/z` and `1 - k² sin² φ = y/z`. -/
theorem real_symmetric_legendre_parametrization {x y z : ℝ} (hx : 0 ≤ x) (hyz : y ≤ z) (hxz : x < z) :
    let φ := Real.arccos √(x / z)
    let k := √((z - y) / (z - x))
    let c : ℂ := ((1 / Real.sin φ ^ 2 : ℝ) : ℂ)
    0 < φ ∧ φ ≤ π / 2 ∧ (x : ℂ) = ((z - x : ℝ) : ℂ) * (c - 1) ∧
      (y : ℂ) = ((z - x : ℝ) : ℂ) * (c - (k : ℂ) ^ 2) ∧ (z : ℂ) = ((z - x : ℝ) : ℂ) * c ∧
      Real.sin φ ^ 2 = (z - x) / z ∧
      1 - (k : ℂ) ^ 2 * (Real.sin φ : ℂ) ^ 2 = ((y / z : ℝ) : ℂ) ∧
      (k : ℂ) ^ 2 = (((z - y) / (z - x) : ℝ) : ℂ) := by
  intro φ k c
  have hl : 0 < z - x := by linarith
  have hz : 0 < z := by linarith
  obtain ⟨hφ0, hφ1, hc⟩ := arccos_sqrt_div_mem_and_csc_sq hx hxz
  have hc' : 1 / Real.sin φ ^ 2 = z / (z - x) := hc
  have hk2 : (k : ℂ) ^ 2 = (((z - y) / (z - x) : ℝ) : ℂ) :=
    ofReal_sqrt_sq_of_nonneg (div_nonneg (by linarith) hl.le)
  have hs2 : Real.sin φ ^ 2 = (z - x) / z := by
    rw [← one_div_one_div (Real.sin φ ^ 2), hc', one_div_div]
  refine ⟨hφ0, hφ1, ?_, ?_, ?_, hs2, ?_, hk2⟩
  · have := ofReal_eq_sub_mul_csc_sq_sub (w := x) hxz _ hc'
    rwa [div_self hl.ne', ofReal_one] at this
  · have := ofReal_eq_sub_mul_csc_sq_sub (w := y) hxz _ hc'
    rwa [← hk2] at this
  · have := ofReal_eq_sub_mul_csc_sq_sub (w := z) hxz _ hc'
    rwa [sub_self, zero_div, ofReal_zero, sub_zero] at this
  · rw [hk2, ← ofReal_pow, hs2]
    have : (z : ℂ) ≠ 0 := ofReal_ne_zero.mpr hz.ne'
    have : ((z : ℂ) - x) ≠ 0 := by exact_mod_cast hl.ne'
    push_cast
    field_simp
    ring

/-- Identity under the stated parameter and domain assumptions: `(((l ^ (3 / 2 : ℝ) : ℝ)) : ℂ) =
((l : ℂ) ^ (1 / 2 : ℂ)) ^ 3`. -/
theorem ofReal_rpow_three_halves {l : ℝ} (hl : 0 < l) :
    (((l ^ (3 / 2 : ℝ) : ℝ)) : ℂ) = ((l : ℂ) ^ (1 / 2 : ℂ)) ^ 3 := by
  rw [← ofReal_sqrt_eq_cpow_half hl.le, ← ofReal_pow, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
    ← Real.rpow_mul hl.le]
  norm_num

/-- Identity under the stated parameter and domain assumptions: `(((l ^ (-1 / 2 : ℝ) : ℝ)) : ℂ) =
((l : ℂ) ^ (1 / 2 : ℂ))⁻¹`. -/
theorem ofReal_rpow_neg_half {l : ℝ} (hl : 0 < l) :
    (((l ^ (-1 / 2 : ℝ) : ℝ)) : ℂ) = ((l : ℂ) ^ (1 / 2 : ℂ))⁻¹ := by
  rw [← ofReal_sqrt_eq_cpow_half hl.le, show (-1 / 2 : ℝ) = -(1 / 2) by norm_num,
    Real.rpow_neg hl.le, ← Real.sqrt_eq_rpow, ofReal_inv]

/-- `cot φ √(1 - κ sin² φ) = √(c - 1) √(c - κ)/√c` with `c = csc² φ`, `0 < φ ≤ π/2`. -/
theorem cot_mul_sqrt_eq_sqrt_csc_sq {φ : ℝ} (h0 : 0 < φ) (h1 : φ ≤ π / 2) {κ : ℝ}
    (hA : 0 ≤ 1 - κ * Real.sin φ ^ 2) :
    Real.cot φ * √(1 - κ * Real.sin φ ^ 2) =
      √(1 / Real.sin φ ^ 2 - 1) * √(1 / Real.sin φ ^ 2 - κ) / √(1 / Real.sin φ ^ 2) := by
  have hs : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
  have hc : 0 ≤ Real.cos φ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], h1⟩
  have e1 : 1 / Real.sin φ ^ 2 - 1 = (Real.cos φ / Real.sin φ) ^ 2 := by
    have := Real.sin_sq_add_cos_sq φ
    field_simp; linarith
  have e2 : 1 / Real.sin φ ^ 2 - κ = (√(1 - κ * Real.sin φ ^ 2) / Real.sin φ) ^ 2 := by
    rw [div_pow, Real.sq_sqrt hA]; field_simp
  have e3 : 1 / Real.sin φ ^ 2 = (1 / Real.sin φ) ^ 2 := by ring
  rw [e1, e2, e3, Real.sqrt_sq (div_nonneg hc hs.le),
    Real.sqrt_sq (div_nonneg (Real.sqrt_nonneg _) hs.le), Real.sqrt_sq (by positivity),
    Real.cot_eq_cos_div_sin]
  field_simp

/-! ### §19.25(ii): Bulirsch's `el1`, `el2` -/

/-- Estimate under the stated parameter and domain assumptions: `0 < Real.arctan x ∧ Real.arctan x
< π / 2 ∧ 1 / Real.sin (Real.arctan x) ^ 2 = 1 / x ^ 2 + 1`. -/
private lemma arctan_mem_and_csc_sq {x : ℝ} (hx : 0 < x) :
    0 < Real.arctan x ∧ Real.arctan x < π / 2 ∧
      1 / Real.sin (Real.arctan x) ^ 2 = 1 / x ^ 2 + 1 := by
  refine ⟨Real.arctan_pos.mpr hx, Real.arctan_lt_pi_div_two x, ?_⟩
  rw [Real.sin_arctan, div_pow, Real.sq_sqrt (by positivity)]
  field_simp

/-- `cos² θ + k_c² sin² θ = 1 - (1 - k_c²) sin² θ`, with `(1 - k_c²) = ((1 - k_c²)^{1/2})²`. -/
private lemma cos_sq_add_kc_sq_mul_sin_sq (θ : ℝ) (kc : ℂ) :
    Complex.cos (θ : ℂ) ^ 2 + kc ^ 2 * Complex.sin (θ : ℂ) ^ 2 =
      1 - ((1 - kc ^ 2) ^ (1 / 2 : ℂ)) ^ 2 * (Real.sin θ : ℂ) ^ 2 := by
  rw [sq ((1 - kc ^ 2) ^ (1 / 2 : ℂ)), cpow_half_mul_cpow_half, Complex.ofReal_sin,
    Complex.cos_sq']
  ring

/-- Identity under the stated parameter and domain assumptions: `bulirschEl1 x kc = symEllIntRF
((1 / x ^ 2 : ℝ) : ℂ) (((1 / x ^ 2 : ℝ) : ℂ) + kc ^ 2) (((1 / x ^ 2 : ℝ) : ℂ) + 1)`. -/
theorem bulirschEl1_eq_symEllIntRF_of_pos {x : ℝ} (hx : 0 < x) (kc : ℂ) :
    bulirschEl1 x kc = symEllIntRF ((1 / x ^ 2 : ℝ) : ℂ) (((1 / x ^ 2 : ℝ) : ℂ) + kc ^ 2)
      (((1 / x ^ 2 : ℝ) : ℂ) + 1) := by
  obtain ⟨h0, h1, hc⟩ := arctan_mem_and_csc_sq hx
  rw [bulirschEl1, ← ofReal_arctan, segmentIntegral_ofReal]
  simp_rw [cos_sq_add_kc_sq_mul_sin_sq]
  rw [← symEllIntRF_csc_sq_eq_integral h0 h1.le, sq ((1 - kc ^ 2) ^ (1 / 2 : ℂ)),
    cpow_half_mul_cpow_half, hc]
  push_cast
  ring_nf

/-- Formula under the stated hypotheses: `1 - ((1 - kc ^ 2) ^ (1 / 2 : ℂ)) ^ 2 * (Real.sin φ : ℂ)
^ 2 ∈ slitPlane`. -/
private lemma one_sub_bulirsch_mul_sin_sq_mem_slitPlane {φ : ℝ} {kc : ℂ} (hkc : kc ^ 2 ∈ slitPlane) :
    1 - ((1 - kc ^ 2) ^ (1 / 2 : ℂ)) ^ 2 * (Real.sin φ : ℂ) ^ 2 ∈ slitPlane := by
  rw [sq ((1 - kc ^ 2) ^ (1 / 2 : ℂ)), cpow_half_mul_cpow_half]
  have h := starConvex_one_slitPlane.add_smul_mem (y := kc ^ 2 - 1) (by simpa using hkc)
    (sq_nonneg (Real.sin φ)) (by nlinarith [Real.sin_sq_le_one φ])
  convert h using 1
  rw [Complex.real_smul]; push_cast; ring

/-- Identity under the stated parameter and domain assumptions: `((a : ℂ) + (b : ℂ) * Complex.tan
(θ : ℂ) ^ 2) * ((1 + Complex.tan (θ : ℂ) ^ 2) * (1 + kc ^ 2 * Complex.tan (θ : ℂ) ^ 2)) ^ (-(1
/ 2 : ℂ)) = (a : ℂ) * (1 - ((1 - kc ^ 2) ^ (1 / 2 : ℂ)) ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2
: ℂ)) + ((b - a : ℝ) : ℂ) * ((Real.sin θ : ℂ) ^ 2 * (1 - ((1 - kc ^ 2) ^ (1 / 2 : ℂ)) ^ 2 *
(Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)))`. -/
private lemma bulirschEl2_integrand_eq {θ : ℝ} (hc : 0 < Real.cos θ) (kc : ℂ) (a b : ℝ) :
    ((a : ℂ) + (b : ℂ) * Complex.tan (θ : ℂ) ^ 2) *
        ((1 + Complex.tan (θ : ℂ) ^ 2) * (1 + kc ^ 2 * Complex.tan (θ : ℂ) ^ 2)) ^ (-(1 / 2 : ℂ)) =
      (a : ℂ) * (1 - ((1 - kc ^ 2) ^ (1 / 2 : ℂ)) ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) +
        ((b - a : ℝ) : ℂ) * ((Real.sin θ : ℂ) ^ 2 *
          (1 - ((1 - kc ^ 2) ^ (1 / 2 : ℂ)) ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))) := by
  have hc0 : (Real.cos θ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hc.ne'
  have hsc : (Real.sin θ : ℂ) ^ 2 + (Real.cos θ : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.sin_sq_add_cos_sq θ
  have ht : Complex.tan (θ : ℂ) = (Real.sin θ : ℂ) / (Real.cos θ : ℂ) := by
    rw [Complex.tan_eq_sin_div_cos, Complex.ofReal_sin, Complex.ofReal_cos]
  rw [sq ((1 - kc ^ 2) ^ (1 / 2 : ℂ)), cpow_half_mul_cpow_half]
  have hprod : (1 + Complex.tan (θ : ℂ) ^ 2) * (1 + kc ^ 2 * Complex.tan (θ : ℂ) ^ 2) =
      (((1 / Real.cos θ ^ 2) ^ 2 : ℝ) : ℂ) * (1 - (1 - kc ^ 2) * (Real.sin θ : ℂ) ^ 2) := by
    rw [ht]
    simp only [ofReal_pow, ofReal_div, ofReal_one]
    generalize (Real.sin θ : ℂ) = s at hsc ⊢
    generalize (Real.cos θ : ℂ) = co at hsc hc0 ⊢
    field_simp
    linear_combination (co ^ 2 + kc ^ 2 * s ^ 2 + 1) * hsc
  rw [hprod, ofReal_mul_cpow_of_pos (by positivity), cpow_neg (((((1 / Real.cos θ ^ 2) ^ 2 : ℝ) :
    ℂ))), ofReal_sq_cpow_half (by positivity), ht]
  generalize (1 - (1 - kc ^ 2) * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) = V
  simp only [ofReal_pow, ofReal_div, ofReal_one, ofReal_sub]
  generalize (Real.sin θ : ℂ) = s at hsc ⊢
  generalize (Real.cos θ : ℂ) = co at hsc hc0 ⊢
  field_simp
  linear_combination (a : ℂ) * V * hsc

/-- Identity under the stated parameter and domain assumptions: `bulirschEl1 x kc = ∫ θ in (0 :
ℝ)..Real.arctan x, (1 - ((1 - kc ^ 2) ^ (1 / 2 : ℂ)) ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 :
ℂ))`. -/
private lemma bulirschEl1_eq_integral {x : ℝ} (kc : ℂ) :
    bulirschEl1 x kc = ∫ θ in (0 : ℝ)..Real.arctan x,
      (1 - ((1 - kc ^ 2) ^ (1 / 2 : ℂ)) ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) := by
  rw [bulirschEl1, ← ofReal_arctan, segmentIntegral_ofReal]
  simp_rw [cos_sq_add_kc_sq_mul_sin_sq]

/-- Identity under the stated parameter and domain assumptions: `bulirschEl2 x kc a b = a *
bulirschEl1 x kc + (1 / 3) * ((b - a : ℝ) : ℂ) * symEllIntRD ((1 / x ^ 2 : ℝ) : ℂ) (((1 / x ^
2 : ℝ) : ℂ) + kc ^ 2) (((1 / x ^ 2 : ℝ) : ℂ) + 1)`. -/
theorem bulirschEl2_eq_symEllIntRD {x : ℝ} (hx : 0 < x) {kc : ℂ} (hkc : kc ^ 2 ∈ slitPlane) (a b : ℝ) :
    bulirschEl2 x kc a b = a * bulirschEl1 x kc + (1 / 3) * ((b - a : ℝ) : ℂ) *
      symEllIntRD ((1 / x ^ 2 : ℝ) : ℂ) (((1 / x ^ 2 : ℝ) : ℂ) + kc ^ 2)
        (((1 / x ^ 2 : ℝ) : ℂ) + 1) := by
  obtain ⟨h0, h1, hc⟩ := arctan_mem_and_csc_sq hx
  have hk := one_sub_bulirsch_mul_sin_sq_mem_slitPlane (φ := Real.arctan x) hkc
  rw [sq ((1 - kc ^ 2) ^ (1 / 2 : ℂ)), cpow_half_mul_cpow_half] at hk
  have hD := symEllIntRD_csc_sq_eq_integral h0 h1.le ((1 - kc ^ 2) ^ (1 / 2 : ℂ))
  rw [sq ((1 - kc ^ 2) ^ (1 / 2 : ℂ)), cpow_half_mul_cpow_half, hc] at hD
  have e1 : ((1 / x ^ 2 + 1 : ℝ) : ℂ) - 1 = ((1 / x ^ 2 : ℝ) : ℂ) := by push_cast; ring
  have e2 : ((1 / x ^ 2 + 1 : ℝ) : ℂ) - (1 - kc ^ 2) = ((1 / x ^ 2 : ℝ) : ℂ) + kc ^ 2 := by
    push_cast; ring
  have e3 : ((1 / x ^ 2 + 1 : ℝ) : ℂ) = ((1 / x ^ 2 : ℝ) : ℂ) + 1 := by push_cast; ring
  rw [e1, e2, e3] at hD
  have hF := bulirschEl1_eq_integral (x := x) kc
  simp_rw [sq ((1 - kc ^ 2) ^ (1 / 2 : ℂ)), cpow_half_mul_cpow_half] at hF
  rw [hD, hF, bulirschEl2, ← ofReal_arctan, segmentIntegral_ofReal]
  have hcont := continuousOn_one_sub_mul_sin_sq_cpow h0.le h1.le hk (-(1 / 2 : ℂ))
  rw [intervalIntegral.integral_congr (g := fun θ : ℝ => (a : ℂ) *
      (1 - (1 - kc ^ 2) * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) +
        ((b - a : ℝ) : ℂ) * ((Real.sin θ : ℂ) ^ 2 *
          (1 - (1 - kc ^ 2) * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))))]
  · rw [intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    · ring
    · exact (continuousOn_const.mul hcont).intervalIntegrable
    · exact (continuousOn_const.mul ((Continuous.continuousOn (by fun_prop)).mul hcont)
        ).intervalIntegrable
  · intro θ hθ
    rw [uIcc_of_le h0.le] at hθ
    have := bulirschEl2_integrand_eq (θ := θ)
      (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, h1]⟩) kc a b
    rw [sq ((1 - kc ^ 2) ^ (1 / 2 : ℂ)), cpow_half_mul_cpow_half] at this
    exact this

end DLMF.EllipticIntegrals
