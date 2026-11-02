/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.EllipticIntegrals.Legendre
public import DLMF.EllipticIntegrals.SymmetricRelations
public import Carlson.Elliptic.QuarticIntegral
public import Carlson.Elliptic.Asymptotic

/-!
# Reduction of general elliptic integrals (DLMF §19.14)

The examples of §19.14(i) of the reduction of elliptic integrals to Legendre's `F(φ, k)`
(`incEllIntFk`, at real arguments): integrals of `(t³ - 1)^{-1/2}`, `(1 - t³)^{-1/2}`,
`(1 + t⁴)^{-1/2}` and of the reciprocal square root of a product of two quadratics.

## Main definitions

* `ellRedQuadU`: the quantity `U` of DLMF 19.14.6 and 19.29.22.
* `QuadraticProductReductionHyp`: the hypotheses of DLMF 19.14.4.

## Main results

* `integral_inv_sqrt_cube_sub_one`, `integral_inv_sqrt_one_sub_cube`,
  `integral_inv_sqrt_one_add_pow_four`: DLMF 19.14.1–19.14.3.
* `integral_inv_sqrt_two_quadratics`: the reduction of
  `∫_y^x dt/√((a₁ + b₁t²)(a₂ + b₂t²))` (DLMF 19.14.4–19.14.6).
* `integral_inv_sqrt_two_quadratics_zero`, `integral_inv_sqrt_two_quadratics_infty`,
  `integral_inv_sqrt_two_quadratics_left`, `integral_inv_sqrt_two_quadratics_right`: the
  special cases DLMF 19.14.7–19.14.10.
* `integral_quadratic_product_eq_symEllIntRF`, `integral_quadratic_product_eq_symEllIntRF_of_pos`,
  `integral_Ioi_quadratic_product_eq_symEllIntRF`: the symmetric form (DLMF 19.29.19, and its
  case `x = ∞`, 19.29.23) without an integrability hypothesis, from Carlson's exercise in
  `lean-codes` by a limit in the endpoints.
* `tendsto_symEllIntRF_ofReal_of_pos`, `tendsto_symEllIntRF_ofReal`,
  `tendsto_symEllIntRF_re_atTop`, `symEllIntRF_zero_zero_ofReal`, `ellRedQuadU_args_pos`:
  continuity of `R_F` along real triples and positivity of the arguments in (19.29.19).

## Implementation notes

In (19.14.1)–(19.14.3) DLMF assumes the integrand and `cos φ` nonnegative; with
`φ = arccos(…) ∈ [0, π/2]` this is the range of `x` stated in each theorem
(`1 ≤ x ≤ √3 + 1`, `1 - √3 ≤ x ≤ 1`, `|x| ≤ 1`). In (19.14.4)–(19.14.6) the amplitude
`φ ∈ [0, π/2]` is given by `sin²φ` (19.14.5); `α ≤ β ≤ γ` is the ordered permutation of
`0, a₁b₂, a₂b₁` (stated as a multiset equality), not all zero. The special cases (19.14.7),
(19.14.9), (19.14.10) are derived from (19.14.4)–(19.14.6) by computing `U`; (19.14.8)
(`x = ∞`) is the improper integral over `(y, ∞)`.

§19.14(ii) (Legendre's reduction of every elliptic integral to `F`, `E`, `Π` and elementary
functions, and the reduction algorithms of Labahn–Mutrie, Byrd–Friedman and Erdélyi et al.) is
descriptive and is not formalized; the symmetric-integral reduction is §19.29.

## References

* NIST DLMF §19.14.
-/

@[expose] public noncomputable section

open Complex Set Filter MeasureTheory
open scoped Real Topology

namespace DLMF.EllipticIntegrals

/-! ### Examples (19.14.1)–(19.14.3) -/

/-- `√√3 = 3^{1/4}`. -/
private lemma sqrt_sqrt_three : √(√3) = (3 : ℝ) ^ (1 / 4 : ℝ) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num)]; norm_num

/-- `(r²)^{-1/2} = r⁻¹` for real `r > 0`. -/
private lemma sq_rpow_neg_half {r : ℝ} (hr : 0 < r) : (r ^ 2) ^ (-(1 / 2) : ℝ) = r⁻¹ := by
  rw [Real.rpow_neg (sq_nonneg r), ← Real.sqrt_eq_rpow, Real.sqrt_sq hr.le]

/-- Real form of DLMF 19.14.1: `∫₁ˣ dt/√(t³ - 1) = 3^{-1/4} F(φ | m)`. -/
private lemma integral_inv_sqrt_cube_sub_one_real {x : ℝ} (h1 : 1 < x) (h2 : x ≤ √3 + 1) :
    ∫ t in (1 : ℝ)..x, (√(t ^ 3 - 1))⁻¹ =
      (3 : ℝ) ^ (-(1 / 4) : ℝ) * DLMF.Elliptic.Real.incEllIntFm
        (Real.arccos ((√3 + 1 - x) / (√3 - 1 + x))) ((2 - √3) / 4) := by
  set s := √3 with hs
  have hs2 : s ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < s := by positivity
  set m := (2 - s) / 4 with hm
  set u : ℝ → ℝ := fun t => (s + 1 - t) / (s - 1 + t) with hu
  set f : ℝ → ℝ := fun t => Real.arccos (u t) with hf
  have hD : ∀ t, 1 ≤ t → 0 < s - 1 + t := fun t ht => by linarith
  have hu1 : ∀ t, 1 ≤ t → t ≤ s + 1 → u t ∈ Icc (-1) 1 := fun t ht ht' => by
    have := hD t ht
    simp only [hu, mem_Icc]
    constructor
    · rw [le_div_iff₀ this]; linarith
    · rw [div_le_iff₀ this]; linarith
  have hanti : StrictAntiOn u (Icc 1 x) := by
    intro a ha b hb hab
    have := hD a ha.1; have := hD b hb.1
    simp only [hu]
    rw [div_lt_div_iff₀ (hD b hb.1) (hD a ha.1)]
    nlinarith
  have hmono : StrictMonoOn f (Icc 1 x) := by
    intro a ha b hb hab
    exact Real.strictAntiOn_arccos (hu1 b hb.1 (hb.2.trans h2)) (hu1 a ha.1 (ha.2.trans h2))
      (hanti ha hb hab)
  have hcont : ContinuousOn f (Icc 1 x) := by
    refine Real.continuous_arccos.comp_continuousOn ?_
    refine ContinuousOn.div (by fun_prop) (by fun_prop) fun t ht => (hD t ht.1).ne'
  have hf1 : f 1 = 0 := by simp [hf, hu, div_self hs0.ne']
  have himg : f '' Ioo 1 x = Ioo 0 (f x) := by
    rw [hcont.image_Ioo_of_strictMonoOn h1.le hmono, hf1]
  -- derivative
  set f' : ℝ → ℝ := fun t => 2 * s / ((s - 1 + t) ^ 2 * √(1 - u t ^ 2)) with hf'
  have hderiv : ∀ t ∈ Ioo 1 x, HasDerivWithinAt f (f' t) (Ioo 1 x) t := by
    intro t ht
    have hDt := hD t ht.1.le
    have hut : u t ∈ Ioo (-1) 1 := by
      simp only [hu, mem_Ioo]
      constructor
      · rw [lt_div_iff₀ hDt]; linarith [ht.2]
      · rw [div_lt_iff₀ hDt]; linarith [ht.1]
    have hdu : HasDerivAt u (-(2 * s) / (s - 1 + t) ^ 2) t := by
      have h := ((hasDerivAt_id t).const_sub (s + 1)).div ((hasDerivAt_id t).const_add (s - 1))
        hDt.ne'
      exact h.congr_deriv (by simp only [id]; ring)
    have h := (Real.hasDerivAt_arccos hut.1.ne' hut.2.ne).comp t hdu
    refine (h.congr_deriv ?_).hasDerivWithinAt
    simp only [hf']
    field_simp
  have hinj : InjOn f (Ioo 1 x) := (hmono.mono Ioo_subset_Icc_self).injOn
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj
    (fun φ => (1 - m * Real.sin φ ^ 2) ^ (-(1 / 2) : ℝ))
  rw [himg] at h
  have hfx : 0 ≤ f x := Real.arccos_nonneg _
  rw [DLMF.Elliptic.Real.incEllIntFm, intervalIntegral.integral_of_le hfx,
    integral_Ioc_eq_integral_Ioo, h, intervalIntegral.integral_of_le h1.le,
    integral_Ioc_eq_integral_Ioo, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
  have ht1 : 0 < t - 1 := by linarith [ht.1]
  have hDt := hD t ht.1.le
  have hq : 0 < t ^ 2 + t + 1 := by nlinarith
  have hsq : 0 < √s := Real.sqrt_pos.mpr hs0
  have hsq2 : √s ^ 2 = s := Real.sq_sqrt hs0.le
  have hA : 1 - u t ^ 2 = (2 * √s * √(t - 1) / (s - 1 + t)) ^ 2 := by
    rw [show (2 * √s * √(t - 1) / (s - 1 + t)) ^ 2 = 4 * s * (t - 1) / (s - 1 + t) ^ 2 by
      rw [div_pow, mul_pow, mul_pow, hsq2, Real.sq_sqrt ht1.le]; ring]
    simp only [hu]
    field_simp
    ring
  have hB : 1 - m * (1 - u t ^ 2) = (√(t ^ 2 + t + 1) / (s - 1 + t)) ^ 2 := by
    rw [show (√(t ^ 2 + t + 1) / (s - 1 + t)) ^ 2 = (t ^ 2 + t + 1) / (s - 1 + t) ^ 2 by
      rw [div_pow, Real.sq_sqrt hq.le]]
    simp only [hu, hm]
    field_simp
    linear_combination 4 * t * hs2
  have hsin : Real.sin (f t) ^ 2 = 1 - u t ^ 2 := by
    simp only [hf]
    rw [Real.sin_arccos, Real.sq_sqrt (by rw [hA]; positivity)]
  have hp : 0 < 2 * √s * √(t - 1) / (s - 1 + t) := by
    have := Real.sqrt_pos.mpr ht1; positivity
  rw [smul_eq_mul, hsin, hB, sq_rpow_neg_half (by have := Real.sqrt_pos.mpr hq; positivity)]
  simp only [hf']
  rw [hA, Real.sqrt_sq hp.le, Real.rpow_neg (by norm_num), ← sqrt_sqrt_three, ← hs,
    show t ^ 3 - 1 = (t - 1) * (t ^ 2 + t + 1) by ring, Real.sqrt_mul ht1.le]
  have h3 : 0 < √(t - 1) := Real.sqrt_pos.mpr ht1
  have h4 : 0 < √(t ^ 2 + t + 1) := Real.sqrt_pos.mpr hq
  rw [abs_of_pos (by positivity)]
  field_simp
  rw [hsq2]

/-- Real form of DLMF 19.14.2: `∫ₓ¹ dt/√(1 - t³) = 3^{-1/4} F(φ | m)`. -/
private lemma integral_inv_sqrt_one_sub_cube_real {x : ℝ} (h1 : 1 - √3 ≤ x) (h2 : x < 1) :
    ∫ t in x..1, (√(1 - t ^ 3))⁻¹ =
      (3 : ℝ) ^ (-(1 / 4) : ℝ) * DLMF.Elliptic.Real.incEllIntFm
        (Real.arccos ((√3 - 1 + x) / (√3 + 1 - x))) ((2 + √3) / 4) := by
  set s := √3 with hs
  have hs2 : s ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < s := by positivity
  set m := (2 + s) / 4 with hm
  set u : ℝ → ℝ := fun t => (s - 1 + t) / (s + 1 - t) with hu
  set f : ℝ → ℝ := fun t => Real.arccos (u t) with hf
  have hD : ∀ t, t ≤ 1 → 0 < s + 1 - t := fun t ht => by linarith
  have hu1 : ∀ t, 1 - s ≤ t → t ≤ 1 → u t ∈ Icc (-1) 1 := fun t ht ht' => by
    have := hD t ht'
    simp only [hu, mem_Icc]
    constructor
    · rw [le_div_iff₀ this]; linarith
    · rw [div_le_iff₀ this]; linarith
  have hmonou : StrictMonoOn u (Icc x 1) := by
    intro a ha b hb hab
    have := hD a ha.2; have := hD b hb.2
    simp only [hu]
    rw [div_lt_div_iff₀ (hD a ha.2) (hD b hb.2)]
    nlinarith
  have hanti : StrictAntiOn f (Icc x 1) := by
    intro a ha b hb hab
    exact Real.strictAntiOn_arccos (hu1 a (h1.trans ha.1) ha.2) (hu1 b (h1.trans hb.1) hb.2)
      (hmonou ha hb hab)
  have hcont : ContinuousOn f (Icc x 1) := by
    refine Real.continuous_arccos.comp_continuousOn ?_
    refine ContinuousOn.div (by fun_prop) (by fun_prop) fun t ht => (hD t ht.2).ne'
  have hf1 : f 1 = 0 := by simp [hf, hu, div_self hs0.ne']
  have himg : f '' Ioo x 1 = Ioo 0 (f x) := by
    rw [hcont.image_Ioo_of_strictAntiOn h2.le hanti, hf1]
  set f' : ℝ → ℝ := fun t => -(2 * s / ((s + 1 - t) ^ 2 * √(1 - u t ^ 2))) with hf'
  have hderiv : ∀ t ∈ Ioo x 1, HasDerivWithinAt f (f' t) (Ioo x 1) t := by
    intro t ht
    have hDt := hD t ht.2.le
    have hut : u t ∈ Ioo (-1) 1 := by
      simp only [hu, mem_Ioo]
      constructor
      · rw [lt_div_iff₀ hDt]; linarith [ht.1]
      · rw [div_lt_iff₀ hDt]; linarith [ht.2]
    have hdu : HasDerivAt u (2 * s / (s + 1 - t) ^ 2) t := by
      have h := ((hasDerivAt_id t).const_add (s - 1)).div ((hasDerivAt_id t).const_sub (s + 1))
        hDt.ne'
      exact h.congr_deriv (by simp only [id]; ring)
    have h := (Real.hasDerivAt_arccos hut.1.ne' hut.2.ne).comp t hdu
    refine (h.congr_deriv ?_).hasDerivWithinAt
    simp only [hf']
    field_simp
  have hinj : InjOn f (Ioo x 1) := (hanti.mono Ioo_subset_Icc_self).injOn
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj
    (fun φ => (1 - m * Real.sin φ ^ 2) ^ (-(1 / 2) : ℝ))
  rw [himg] at h
  have hfx : 0 ≤ f x := Real.arccos_nonneg _
  rw [DLMF.Elliptic.Real.incEllIntFm, intervalIntegral.integral_of_le hfx,
    integral_Ioc_eq_integral_Ioo, h, intervalIntegral.integral_of_le h2.le,
    integral_Ioc_eq_integral_Ioo, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
  have ht1 : 0 < 1 - t := by linarith [ht.2]
  have hDt := hD t ht.2.le
  have hq : 0 < t ^ 2 + t + 1 := by nlinarith
  have hsq : 0 < √s := Real.sqrt_pos.mpr hs0
  have hsq2 : √s ^ 2 = s := Real.sq_sqrt hs0.le
  have hA : 1 - u t ^ 2 = (2 * √s * √(1 - t) / (s + 1 - t)) ^ 2 := by
    rw [show (2 * √s * √(1 - t) / (s + 1 - t)) ^ 2 = 4 * s * (1 - t) / (s + 1 - t) ^ 2 by
      rw [div_pow, mul_pow, mul_pow, hsq2, Real.sq_sqrt ht1.le]; ring]
    simp only [hu]
    field_simp
    ring
  have hB : 1 - m * (1 - u t ^ 2) = (√(t ^ 2 + t + 1) / (s + 1 - t)) ^ 2 := by
    rw [show (√(t ^ 2 + t + 1) / (s + 1 - t)) ^ 2 = (t ^ 2 + t + 1) / (s + 1 - t) ^ 2 by
      rw [div_pow, Real.sq_sqrt hq.le]]
    simp only [hu, hm]
    field_simp
    linear_combination 4 * t * hs2
  have hsin : Real.sin (f t) ^ 2 = 1 - u t ^ 2 := by
    simp only [hf]
    rw [Real.sin_arccos, Real.sq_sqrt (by rw [hA]; positivity)]
  have hp : 0 < 2 * √s * √(1 - t) / (s + 1 - t) := by
    have := Real.sqrt_pos.mpr ht1; positivity
  rw [smul_eq_mul, hsin, hB, sq_rpow_neg_half (by have := Real.sqrt_pos.mpr hq; positivity)]
  simp only [hf']
  rw [hA, Real.sqrt_sq hp.le, Real.rpow_neg (by norm_num), ← sqrt_sqrt_three, ← hs,
    show 1 - t ^ 3 = (1 - t) * (t ^ 2 + t + 1) by ring, Real.sqrt_mul ht1.le]
  have h3 : 0 < √(1 - t) := Real.sqrt_pos.mpr ht1
  have h4 : 0 < √(t ^ 2 + t + 1) := Real.sqrt_pos.mpr hq
  rw [abs_neg, abs_of_pos (by positivity)]
  field_simp
  rw [hsq2]

/-- DLMF 19.14.1: `∫₁^x dt/√(t³ - 1) = 3^{-1/4} F(φ, k)`,
`cos φ = (√3 + 1 - x)/(√3 - 1 + x)`, `k² = (2 - √3)/4`, for `1 ≤ x ≤ √3 + 1`. -/
@[dlmf 19.14.E1]
theorem integral_inv_sqrt_cube_sub_one {x : ℝ} (h1 : 1 ≤ x) (h2 : x ≤ Real.sqrt 3 + 1) :
    ((∫ t in (1 : ℝ)..x, (Real.sqrt (t ^ 3 - 1))⁻¹ : ℝ) : ℂ) =
      ((3 : ℝ) ^ (-(1 / 4) : ℝ) : ℝ) *
        incEllIntFk (Real.arccos ((Real.sqrt 3 + 1 - x) / (Real.sqrt 3 - 1 + x)))
          (Real.sqrt ((2 - Real.sqrt 3) / 4)) := by
  have hs : Real.sqrt 3 < 2 := by
    rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hm0 : 0 ≤ (2 - Real.sqrt 3) / 4 := by linarith
  have hk : ((Real.sqrt ((2 - Real.sqrt 3) / 4) : ℝ) : ℂ) ^ 2 =
      (((2 - Real.sqrt 3) / 4 : ℝ) : ℂ) := by
    rw [← ofReal_pow, Real.sq_sqrt hm0]
  rw [incEllIntFk_eq_ofReal hk (by linarith [Real.sqrt_nonneg 3]), ← ofReal_mul]
  congr 1
  rcases h1.lt_or_eq with h1 | rfl
  · exact integral_inv_sqrt_cube_sub_one_real h1 h2
  · simp [DLMF.Elliptic.Real.incEllIntFm]

/-- DLMF 19.14.2: `∫ₓ¹ dt/√(1 - t³) = 3^{-1/4} F(φ, k)`,
`cos φ = (√3 - 1 + x)/(√3 + 1 - x)`, `k² = (2 + √3)/4`, for `1 - √3 ≤ x ≤ 1`. -/
@[dlmf 19.14.E2]
theorem integral_inv_sqrt_one_sub_cube {x : ℝ} (h1 : 1 - Real.sqrt 3 ≤ x) (h2 : x ≤ 1) :
    ((∫ t in x..1, (Real.sqrt (1 - t ^ 3))⁻¹ : ℝ) : ℂ) =
      ((3 : ℝ) ^ (-(1 / 4) : ℝ) : ℝ) *
        incEllIntFk (Real.arccos ((Real.sqrt 3 - 1 + x) / (Real.sqrt 3 + 1 - x)))
          (Real.sqrt ((2 + Real.sqrt 3) / 4)) := by
  have hs : Real.sqrt 3 < 2 := by
    rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hm0 : 0 ≤ (2 + Real.sqrt 3) / 4 := by positivity
  have hk : ((Real.sqrt ((2 + Real.sqrt 3) / 4) : ℝ) : ℂ) ^ 2 =
      (((2 + Real.sqrt 3) / 4 : ℝ) : ℂ) := by
    rw [← ofReal_pow, Real.sq_sqrt hm0]
  rw [incEllIntFk_eq_ofReal hk (by linarith), ← ofReal_mul]
  congr 1
  rcases h2.lt_or_eq with h2 | rfl
  · exact integral_inv_sqrt_one_sub_cube_real h1 h2
  · simp [DLMF.Elliptic.Real.incEllIntFm]

/-- The substitution `φ = 2 arctan t` of (19.14.3):
`(1 - ½ sin²(2 arctan t))^{-1/2} · 2/(1 + t²) = 2/√(1 + t⁴)`. -/
private lemma quartic_subst_integrand (t : ℝ) :
    (1 - 1 / 2 * Real.sin (2 * Real.arctan t) ^ 2) ^ (-(1 / 2) : ℝ) * (2 * (1 / (1 + t ^ 2))) =
      2 * (Real.sqrt (1 + t ^ 4))⁻¹ := by
  have h1 : 0 < 1 + t ^ 2 := by positivity
  have hs : Real.sin (2 * Real.arctan t) = 2 * t / (1 + t ^ 2) := by
    rw [Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan]
    have hq : 0 < Real.sqrt (1 + t ^ 2) := Real.sqrt_pos.mpr h1
    have hq2 : Real.sqrt (1 + t ^ 2) ^ 2 = 1 + t ^ 2 := Real.sq_sqrt h1.le
    calc 2 * (t / Real.sqrt (1 + t ^ 2)) * (1 / Real.sqrt (1 + t ^ 2))
        = 2 * t / Real.sqrt (1 + t ^ 2) ^ 2 := by field_simp
      _ = _ := by rw [hq2]
  have hb : 1 - 1 / 2 * Real.sin (2 * Real.arctan t) ^ 2 = (1 + t ^ 4) / (1 + t ^ 2) ^ 2 := by
    rw [hs]; field_simp; ring
  rw [hb, Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, Real.sqrt_div' _ (by positivity),
    Real.sqrt_sq h1.le]
  have h4 : 0 < Real.sqrt (1 + t ^ 4) := Real.sqrt_pos.mpr (by positivity)
  field_simp

/-- `∫₀^x dt/√(1 + t⁴) = ½ F(2 arctan x | ½)` (real form of 19.14.3, any real `x`). -/
private lemma integral_inv_sqrt_one_add_pow_four_eq_incEllIntFm (x : ℝ) :
    ∫ t in (0 : ℝ)..x, (Real.sqrt (1 + t ^ 4))⁻¹ =
      DLMF.Elliptic.Real.incEllIntFm (2 * Real.arctan x) (1 / 2) / 2 := by
  have hG : Continuous fun φ : ℝ => (1 - 1 / 2 * Real.sin φ ^ 2) ^ (-(1 / 2) : ℝ) :=
    DLMF.Elliptic.continuous_one_sub_mul_sin_sq_rpow (by norm_num) _
  have hsub := intervalIntegral.integral_comp_mul_deriv (a := 0) (b := x)
    (f := fun t => 2 * Real.arctan t) (f' := fun t => 2 * (1 / (1 + t ^ 2)))
    (fun t _ => (Real.hasDerivAt_arctan t).const_mul 2)
    (by
      refine Continuous.continuousOn ?_
      exact continuous_const.mul (continuous_const.div (by fun_prop) fun t => by positivity)) hG
  simp only [Function.comp_def, quartic_subst_integrand, Real.arctan_zero, mul_zero] at hsub
  rw [intervalIntegral.integral_const_mul] at hsub
  unfold DLMF.Elliptic.Real.incEllIntFm
  linarith

/-- DLMF 19.14.3: `∫₀^x dt/√(1 + t⁴) = (sign x / 2) F(φ, k)`, `cos φ = (1 - x²)/(1 + x²)`,
`k² = 1/2`. DLMF assumes `cos φ ≥ 0`, i.e. `|x| ≤ 1`; **stronger than DLMF**: with
`φ = arccos((1 - x²)/(1 + x²)) = 2 arctan |x| ∈ [0, π)`, the formula holds for all real `x`. -/
@[dlmf 19.14.E3]
theorem integral_inv_sqrt_one_add_pow_four (x : ℝ) :
    ((∫ t in (0 : ℝ)..x, (Real.sqrt (1 + t ^ 4))⁻¹ : ℝ) : ℂ) =
      ((((SignType.sign x : ℝ)) / 2 : ℝ) : ℂ) *
        incEllIntFk (Real.arccos ((1 - x ^ 2) / (1 + x ^ 2))) (Real.sqrt (1 / 2)) := by
  have hk : ((Real.sqrt (1 / 2) : ℝ) : ℂ) ^ 2 = ((1 / 2 : ℝ) : ℂ) := by
    rw [← ofReal_pow, Real.sq_sqrt (by norm_num)]
  rw [incEllIntFk_eq_ofReal hk (by norm_num)]
  have harc : ∀ y : ℝ, 0 ≤ y → Real.arccos ((1 - y ^ 2) / (1 + y ^ 2)) = 2 * Real.arctan y := by
    intro y hy
    have h0 : 0 ≤ 2 * Real.arctan y := by have := Real.arctan_nonneg.mpr hy; linarith
    have h1 : 2 * Real.arctan y ≤ π := by have := Real.arctan_lt_pi_div_two y; linarith
    rw [← Real.arccos_cos h0 h1, Real.cos_two_mul, Real.cos_sq_arctan]
    congr 1
    field_simp
    ring
  rcases lt_trichotomy x 0 with h | rfl | h
  · have hneg : ∫ t in (0 : ℝ)..x, (Real.sqrt (1 + t ^ 4))⁻¹ =
        -∫ t in (0 : ℝ)..(-x), (Real.sqrt (1 + t ^ 4))⁻¹ := by
      have := intervalIntegral.integral_comp_neg (a := 0) (b := -x)
        (fun t => (Real.sqrt (1 + t ^ 4))⁻¹)
      simp only [neg_neg, neg_zero, Even.neg_pow (by decide : Even 4)] at this
      rw [intervalIntegral.integral_symm, this]
    rw [hneg, integral_inv_sqrt_one_add_pow_four_eq_incEllIntFm (-x),
      show (1 - x ^ 2) / (1 + x ^ 2) = (1 - (-x) ^ 2) / (1 + (-x) ^ 2) by ring,
      harc (-x) (by linarith), sign_neg h, SignType.coe_neg_one]
    push_cast
    ring
  · simp
  · rw [integral_inv_sqrt_one_add_pow_four_eq_incEllIntFm x, harc x h.le, sign_pos h,
        SignType.coe_one]
    push_cast
    ring

/-! ### Two quadratic factors (19.14.4)–(19.14.10) -/

/-- DLMF 19.14.6 and 19.29.22: `U = (x √((a₁ + b₁y²)(a₂ + b₂y²)) + y √((a₁ + b₁x²)(a₂ +
b₂x²)))/(x² - y²)`, that is `(x² - y²) U = x √(Q₁(y) Q₂(y)) + y √(Q₁(x) Q₂(x))` with
`Q_j(t) = a_j + b_j t²`. -/
@[dlmf 19.29.E22]
def ellRedQuadU (a₁ b₁ a₂ b₂ x y : ℝ) : ℝ :=
  (x * Real.sqrt ((a₁ + b₁ * y ^ 2) * (a₂ + b₂ * y ^ 2)) +
    y * Real.sqrt ((a₁ + b₁ * x ^ 2) * (a₂ + b₂ * x ^ 2))) / (x ^ 2 - y ^ 2)

/-- The hypotheses of DLMF 19.14.4: `0 ≤ y < x`, both quadratics positive on `(y, x)`, and
`α ≤ β ≤ γ` the ordered permutation of `0, a₁b₂, a₂b₁`, not all zero. -/
structure QuadraticProductReductionHyp (a₁ b₁ a₂ b₂ x y α β γ : ℝ) : Prop where
  /-- The lower integration endpoint is nonnegative. -/
  y_nonneg : 0 ≤ y
  /-- The lower integration endpoint is strictly less than the upper endpoint. -/
  y_lt_x : y < x
  /-- Both quadratic factors are strictly positive in the open integration interval. -/
  pos : ∀ t ∈ Ioo y x, 0 < a₁ + b₁ * t ^ 2 ∧ 0 < a₂ + b₂ * t ^ 2
  /-- The three reduction parameters form the multiset `0, a₁b₂, a₂b₁`. -/
  perm : ({α, β, γ} : Multiset ℝ) = {0, a₁ * b₂, a₂ * b₁}
  /-- The smallest reduction parameter is at most the middle parameter. -/
  le₁ : α ≤ β
  /-- The middle reduction parameter is at most the largest parameter. -/
  le₂ : β ≤ γ
  /-- The two cross-coefficient products do not vanish simultaneously. -/
  not_all_zero : ¬ (a₁ * b₂ = 0 ∧ a₂ * b₁ = 0)

/-! ### Limits of `R_F` and the reduction (19.29.19) without integrability -/

/-- Continuity of `R_F` along positive real triples at a nonnegative limit with first entry
possibly zero. -/
theorem tendsto_symEllIntRF_ofReal_of_pos {ι : Type*} {l : Filter ι} {a b c : ι → ℝ}
    {A B C : ℝ} (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B)) (hc : Tendsto c l (𝓝 C))
    (hpos : ∀ᶠ i in l, 0 < a i ∧ 0 < b i ∧ 0 < c i) (hA : 0 ≤ A) (hB : 0 < B) (hC : 0 < C) :
    Tendsto (fun i => symEllIntRF (a i) (b i) (c i)) l (𝓝 (symEllIntRF A B C)) := by
  have hBs : (B : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr hB
  have hCs : (C : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr hC
  have ha' := (continuous_ofReal.tendsto A).comp ha
  have hb' := (continuous_ofReal.tendsto B).comp hb
  have hc' := (continuous_ofReal.tendsto C).comp hc
  have hev : ∀ᶠ i in l, symEllIntRF (a i) (b i) (c i) = Carlson.carlsonRF (a i) (b i) (c i) := by
    filter_upwards [hpos] with i hi
    exact symEllIntRF_eq_carlsonRF (ofReal_mem_slitPlane.mpr hi.1)
      (ofReal_mem_slitPlane.mpr hi.2.1) (ofReal_mem_slitPlane.mpr hi.2.2)
  rcases hA.eq_or_lt with h0 | h0
  · subst h0
    have H := Carlson.tendsto_carlsonRF_zero_of_tendsto_slit hBs hCs
      (by simpa using ha') hb' hc'
      (by filter_upwards [hpos] with i hi; exact ofReal_mem_slitPlane.mpr hi.1)
    rw [ofReal_zero, symEllIntRF_zero_eq_pi_div_two_mul_carlsonRK hBs hCs]
    exact H.congr' (by filter_upwards [hev] with i hi; exact hi.symm)
  · have hAs : (A : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr h0
    have hvec : Tendsto (fun i => (![(a i : ℂ), (b i : ℂ), (c i : ℂ)] : Fin 3 → ℂ)) l
        (𝓝 ![(A : ℂ), (B : ℂ), (C : ℂ)]) := by
      refine tendsto_pi_nhds.2 fun j => ?_
      fin_cases j
      · exact ha'
      · exact hb'
      · exact hc'
    have H := (Carlson.continuousAt_carlsonRF hAs hBs hCs).tendsto.comp hvec
    rw [symEllIntRF_eq_carlsonRF hAs hBs hCs]
    refine H.congr' ?_
    filter_upwards [hev] with i hi
    rw [hi]; rfl

/-- `R_F` along positive real triples at a nonnegative limit with at most one zero entry. -/
theorem tendsto_symEllIntRF_ofReal {ι : Type*} {l : Filter ι} {a b c : ι → ℝ}
    {A B C : ℝ} (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B)) (hc : Tendsto c l (𝓝 C))
    (hpos : ∀ᶠ i in l, 0 < a i ∧ 0 < b i ∧ 0 < c i) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (h2 : (0 < A ∧ 0 < B) ∨ (0 < A ∧ 0 < C) ∨ (0 < B ∧ 0 < C)) :
    Tendsto (fun i => symEllIntRF (a i) (b i) (c i)) l (𝓝 (symEllIntRF A B C)) := by
  rcases h2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have := tendsto_symEllIntRF_ofReal_of_pos hc ha hb
      (by filter_upwards [hpos] with i hi; exact ⟨hi.2.2, hi.1, hi.2.1⟩) hC h1 h2
    simpa only [symEllIntRF_comm_left, symEllIntRF_comm_right] using this
  · have := tendsto_symEllIntRF_ofReal_of_pos hb ha hc
      (by filter_upwards [hpos] with i hi; exact ⟨hi.2.1, hi.1, hi.2.2⟩) hB h1 h2
    simpa only [symEllIntRF_comm_left] using this
  · exact tendsto_symEllIntRF_ofReal_of_pos ha hb hc hpos hA h1 h2

/-- `R_F` blows up along positive real triples whose first two entries tend to `0`. -/
theorem tendsto_symEllIntRF_re_atTop {ι : Type*} {l : Filter ι} {a b c : ι → ℝ} {C : ℝ}
    (ha : Tendsto a l (𝓝 0)) (hb : Tendsto b l (𝓝 0)) (hc : Tendsto c l (𝓝 C))
    (hpos : ∀ᶠ i in l, 0 < a i ∧ 0 < b i ∧ 0 < c i) :
    Tendsto (fun i => (symEllIntRF (a i) (b i) (c i)).re) l atTop := by
  set M : ℝ := |C| + 1 with hM
  have hM0 : 0 < M := by positivity
  have hcM : ∀ᶠ i in l, c i ≤ M :=
    hc.eventually (eventually_le_nhds (by rw [hM]; linarith [le_abs_self C]))
  set e : ι → ℝ := fun i => max (a i) (b i)
  have he : Tendsto e l (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨by simpa using ha.max hb, ?_⟩
    filter_upwards [hpos] with i hi
    exact (lt_max_of_lt_left hi.1).ne'
  have hRC := (tendsto_symEllIntRC_zero hM0).comp he
  refine tendsto_atTop_mono' _ ?_ hRC
  filter_upwards [hpos, hcM] with i hi hci
  have hei : 0 < e i := lt_max_of_lt_left hi.1
  simp only [Function.comp_apply]
  rw [symEllIntRC_eq_symEllIntRF _ (fun h => by have := h.2; rw [ofReal_re] at this; linarith),
    symEllIntRF_comm_left, symEllIntRF_comm_right,
    symEllIntRF_eq_carlsonRF (ofReal_mem_slitPlane.mpr hei) (ofReal_mem_slitPlane.mpr hei)
      (ofReal_mem_slitPlane.mpr hM0),
    symEllIntRF_eq_carlsonRF (ofReal_mem_slitPlane.mpr hi.1) (ofReal_mem_slitPlane.mpr hi.2.1)
      (ofReal_mem_slitPlane.mpr hi.2.2)]
  exact Carlson.carlsonRF_re_antitone hi.1 hi.2.1 hi.2.2 (le_max_left _ _) (le_max_right _ _) hci

/-- `R_F(0, 0, z) = 0` in Lean's totalization for real `z ≥ 0`: the integrand is not
integrable. -/
theorem symEllIntRF_zero_zero_ofReal {z : ℝ} (hz : 0 ≤ z) : symEllIntRF 0 0 z = 0 := by
  rcases hz.eq_or_lt with h | h
  · subst h
    have H := symEllIntRF_scale (l := 4) (by norm_num) 0 0 0
    simp only [mul_zero, ofReal_zero] at H ⊢
    have h4 : ((4 : ℝ) : ℂ) ^ (1 / 2 : ℂ) = 2 := by
      rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow (by norm_num),
        ← Real.sqrt_eq_rpow, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      push_cast; ring
    rw [h4] at H
    linear_combination (2 : ℂ) * H
  · unfold symEllIntRF
    rw [integral_undef (not_integrableOn_symEllIntRF_integrand_zero_zero
      (ofReal_mem_slitPlane.mpr h)), mul_zero]


private lemma two_eq_zero_of_not {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (h : ¬ ((0 < A ∧ 0 < B) ∨ (0 < A ∧ 0 < C) ∨ (0 < B ∧ 0 < C))) :
    (A = 0 ∧ B = 0) ∨ (A = 0 ∧ C = 0) ∨ (B = 0 ∧ C = 0) := by
  rcases hA.eq_or_lt with h1 | h1 <;> rcases hB.eq_or_lt with h2 | h2 <;>
    rcases hC.eq_or_lt with h3 | h3 <;> first
    | exact absurd (by tauto) h
    | (left; exact ⟨h1.symm, h2.symm⟩)
    | (right; left; exact ⟨h1.symm, h3.symm⟩)
    | (right; right; exact ⟨h2.symm, h3.symm⟩)

private lemma quadratic_product_sq_identity {a₁ b₁ a₂ b₂ x y p₁ q₁ p₂ q₂ : ℝ}
    (hxy : x ^ 2 - y ^ 2 ≠ 0)
    (h₁ : p₁ ^ 2 = a₁ + b₁ * x ^ 2) (h₂ : p₂ ^ 2 = a₂ + b₂ * x ^ 2)
    (k₁ : q₁ ^ 2 = a₁ + b₁ * y ^ 2) (k₂ : q₂ ^ 2 = a₂ + b₂ * y ^ 2) :
    ((x * p₁ * q₂ + y * q₁ * p₂) / (x ^ 2 - y ^ 2)) ^ 2 =
      ((x * (q₁ * q₂) + y * (p₁ * p₂)) / (x ^ 2 - y ^ 2)) ^ 2 + a₂ * b₁ := by
  rw [div_pow, div_pow, div_add' _ _ _ (pow_ne_zero 2 hxy), div_left_inj' (pow_ne_zero 2 hxy)]
  linear_combination (x ^ 2 * q₂ ^ 2 - y ^ 2 * p₂ ^ 2) * h₁ -
    (x ^ 2 * q₂ ^ 2 - y ^ 2 * p₂ ^ 2) * k₁ +
    (-(b₁ * (x ^ 2 - y ^ 2)) * y ^ 2) * h₂ + (b₁ * (x ^ 2 - y ^ 2) * x ^ 2) * k₂

/-- Positivity of the three arguments of `R_F` in (19.29.19) for `0 < y < x` and both
quadratics positive on `[y, x]`. -/
theorem ellRedQuadU_args_pos {a₁ b₁ a₂ b₂ x y : ℝ} (hy : 0 < y) (hxy : y < x)
    (hQ : ∀ t ∈ Icc y x, 0 < a₁ + b₁ * t ^ 2 ∧ 0 < a₂ + b₂ * t ^ 2) :
    0 < ellRedQuadU a₁ b₁ a₂ b₂ x y ^ 2 + a₁ * b₂ ∧
      0 < ellRedQuadU a₁ b₁ a₂ b₂ x y ^ 2 + a₂ * b₁ ∧ 0 < ellRedQuadU a₁ b₁ a₂ b₂ x y ^ 2 := by
  have hx0 : 0 < x := hy.trans hxy
  have hd : 0 < x ^ 2 - y ^ 2 := by nlinarith
  obtain ⟨px1, px2⟩ := hQ x ⟨hxy.le, le_rfl⟩
  obtain ⟨py1, py2⟩ := hQ y ⟨le_rfl, hxy.le⟩
  have hU : 0 < ellRedQuadU a₁ b₁ a₂ b₂ x y := by
    unfold ellRedQuadU
    have : 0 < √((a₁ + b₁ * y ^ 2) * (a₂ + b₂ * y ^ 2)) := Real.sqrt_pos.mpr (by positivity)
    positivity
  have hsq : ∀ {c₁ d₁ c₂ d₂ : ℝ}, 0 < c₁ + d₁ * x ^ 2 → 0 < c₂ + d₂ * x ^ 2 →
      0 < c₁ + d₁ * y ^ 2 → 0 < c₂ + d₂ * y ^ 2 →
      0 < ellRedQuadU c₁ d₁ c₂ d₂ x y ^ 2 + c₂ * d₁ := by
    intro c₁ d₁ c₂ d₂ g1 g2 g3 g4
    unfold ellRedQuadU
    rw [Real.sqrt_mul g3.le, Real.sqrt_mul g1.le, ← quadratic_product_sq_identity hd.ne'
      (Real.sq_sqrt g1.le) (Real.sq_sqrt g2.le) (Real.sq_sqrt g3.le) (Real.sq_sqrt g4.le)]
    have := Real.sqrt_pos.mpr g1; have := Real.sqrt_pos.mpr g4
    positivity
  have hB : 0 < ellRedQuadU a₁ b₁ a₂ b₂ x y ^ 2 + a₂ * b₁ := hsq px1 px2 py1 py2
  have hA : 0 < ellRedQuadU a₁ b₁ a₂ b₂ x y ^ 2 + a₁ * b₂ := by
    have := hsq (c₁ := a₂) (d₁ := b₂) (c₂ := a₁) (d₂ := b₁) px2 px1 py2 py1
    have e : ellRedQuadU a₂ b₂ a₁ b₁ x y = ellRedQuadU a₁ b₁ a₂ b₂ x y := by
      unfold ellRedQuadU; rw [mul_comm (a₂ + _), mul_comm (a₂ + b₂ * x ^ 2)]
    rwa [e] at this
  exact ⟨hA, hB, by positivity⟩

/-- DLMF 19.29.19 for `0 < y` and both quadratics positive on `[y, x]`, from Carlson's
Exercise 9.8-3 (`Carlson.integral_quadratic_mul_quadratic`). -/
theorem integral_quadratic_product_eq_symEllIntRF_of_pos {a₁ b₁ a₂ b₂ x y : ℝ} (hy : 0 < y)
    (hxy : y < x) (hQ : ∀ t ∈ Icc y x, 0 < a₁ + b₁ * t ^ 2 ∧ 0 < a₂ + b₂ * t ^ 2) :
    ((∫ t in Ioo y x, 1 / √((a₁ + b₁ * t ^ 2) * (a₂ + b₂ * t ^ 2)) : ℝ) : ℂ) =
      symEllIntRF (ellRedQuadU a₁ b₁ a₂ b₂ x y ^ 2 + a₁ * b₂ : ℝ)
        (ellRedQuadU a₁ b₁ a₂ b₂ x y ^ 2 + a₂ * b₁ : ℝ) (ellRedQuadU a₁ b₁ a₂ b₂ x y ^ 2 : ℝ) := by
  have H := Carlson.integral_quadratic_mul_quadratic (a := b₁) (c := a₁) (α := b₂) (γ := a₂)
    hy hxy (fun t ht => by obtain ⟨h1, h2⟩ := hQ t ht; exact ⟨by linarith, by linarith⟩)
  have e1 : ∀ t : ℝ, (b₁ * t ^ 2 + a₁) * (b₂ * t ^ 2 + a₂) =
      (a₁ + b₁ * t ^ 2) * (a₂ + b₂ * t ^ 2) := fun t => by ring
  simp only [e1] at H
  obtain ⟨hA, hB, hU2⟩ := ellRedQuadU_args_pos hy hxy hQ
  have hint : ∀ t ∈ Ioo y x, 1 / √((a₁ + b₁ * t ^ 2) * (a₂ + b₂ * t ^ 2)) =
      ((a₁ + b₁ * t ^ 2) * (a₂ + b₂ * t ^ 2)) ^ (-1 / 2 : ℝ) := by
    intro t ht
    obtain ⟨q1, q2⟩ := hQ t (Ioo_subset_Icc_self ht)
    rw [Real.sqrt_eq_rpow, show (-1 / 2 : ℝ) = -(1 / 2) by norm_num,
      Real.rpow_neg (by positivity), one_div]
  rw [setIntegral_congr_fun measurableSet_Ioo hint, H]
  rw [symEllIntRF_comm_left, symEllIntRF_comm_right, symEllIntRF_comm_left,
    symEllIntRF_eq_carlsonRF (ofReal_mem_slitPlane.mpr hU2)
      (ofReal_mem_slitPlane.mpr hB) (ofReal_mem_slitPlane.mpr hA)]
  unfold ellRedQuadU
  rw [mul_comm a₂ b₁]


/-- The limit argument behind (19.29.19): if `f ≥ 0` has integrals `R_F(aₙ, bₙ, cₙ)` over an
exhausting sequence `φ n` of `S`, with positive `aₙ, bₙ, cₙ → A, B, C`, then
`∫_S f = R_F(A, B, C)` in Lean's totalization (both sides are `0` when two of `A, B, C`
vanish, and then `f` is not integrable). -/
private lemma integral_eq_symEllIntRF_of_aecover {S : Set ℝ} {φ : ℕ → Set ℝ} {f : ℝ → ℝ}
    (hcov : AECover (volume.restrict S) atTop φ) (hφS : ∀ n, φ n ⊆ S) (hf0 : ∀ t, 0 ≤ f t)
    (hfi : ∀ n, IntegrableOn f (φ n)) {a b c : ℕ → ℝ} {A B C : ℝ}
    (hA : Tendsto a atTop (𝓝 A)) (hB : Tendsto b atTop (𝓝 B)) (hC : Tendsto c atTop (𝓝 C))
    (hargs : ∀ n, 0 < a n ∧ 0 < b n ∧ 0 < c n)
    (hsub : ∀ n, ((∫ t in φ n, f t : ℝ) : ℂ) = symEllIntRF (a n) (b n) (c n)) :
    ((∫ t in S, f t : ℝ) : ℂ) = symEllIntRF A B C := by
  have hA0 : 0 ≤ A := ge_of_tendsto' hA fun n => (hargs n).1.le
  have hB0 : 0 ≤ B := ge_of_tendsto' hB fun n => (hargs n).2.1.le
  have hC0 : 0 ≤ C := ge_of_tendsto' hC fun n => (hargs n).2.2.le
  have hpos : ∀ᶠ n in atTop, 0 < a n ∧ 0 < b n ∧ 0 < c n := Eventually.of_forall hargs
  have hrr : ∀ n, (volume.restrict S).restrict (φ n) = volume.restrict (φ n) := by
    intro n
    rw [Measure.restrict_restrict (hcov.measurableSet n), inter_eq_left.mpr (hφS n)]
  have hre : ∀ n, (symEllIntRF (a n) (b n) (c n)).re = ∫ t in φ n, f t := fun n => by
    rw [← hsub n, ofReal_re]
  by_cases hgood : (0 < A ∧ 0 < B) ∨ (0 < A ∧ 0 < C) ∨ (0 < B ∧ 0 < C)
  · have hRF := tendsto_symEllIntRF_ofReal hA hB hC hpos hA0 hB0 hC0 hgood
    set R := symEllIntRF A B C
    have hI : Tendsto (fun n => ((∫ t in φ n, f t : ℝ) : ℂ)) atTop (𝓝 R) := by
      simp_rw [hsub]; exact hRF
    have hIr : Tendsto (fun n => ∫ t in φ n, f t) atTop (𝓝 R.re) := by
      have := (continuous_re.tendsto _).comp hI
      simpa only [Function.comp_def, ofReal_re] using this
    have hint : Integrable f (volume.restrict S) := by
      refine hcov.integrable_of_integral_norm_bounded (R.re + 1) (fun n => ?_) ?_
      · rw [IntegrableOn, hrr]; exact hfi n
      · filter_upwards [hIr.eventually (eventually_le_nhds (by linarith : R.re < R.re + 1))]
          with n hn
        rw [hrr]
        simpa only [Real.norm_eq_abs, abs_of_nonneg (hf0 _)] using hn
    have hconv := hcov.integral_tendsto_of_countably_generated hint
    simp only [hrr] at hconv
    exact tendsto_nhds_unique ((continuous_ofReal.tendsto _).comp hconv) hI
  · have hnot : ¬ IntegrableOn f S := by
      intro hint
      have hbd : ∀ n, ∫ t in φ n, f t ≤ ∫ t in S, f t := fun n =>
        setIntegral_mono_set hint (ae_of_all _ fun t => hf0 t)
          (Eventually.of_forall (hφS n))
      have htop : Tendsto (fun n => (symEllIntRF (a n) (b n) (c n)).re) atTop atTop := by
        rcases two_eq_zero_of_not hA0 hB0 hC0 hgood with ⟨h1, h2⟩ | ⟨h1, h3⟩ | ⟨h2, h3⟩
        · rw [h1] at hA; rw [h2] at hB
          exact tendsto_symEllIntRF_re_atTop hA hB hC hpos
        · rw [h1] at hA; rw [h3] at hC
          simpa only [symEllIntRF_comm_right] using tendsto_symEllIntRF_re_atTop hA hC hB
            (by filter_upwards [hpos] with n hn; exact ⟨hn.1, hn.2.2, hn.2.1⟩)
        · rw [h2] at hB; rw [h3] at hC
          have := tendsto_symEllIntRF_re_atTop hB hC hA
            (by filter_upwards [hpos] with n hn; exact ⟨hn.2.1, hn.2.2, hn.1⟩)
          simpa only [symEllIntRF_comm_right, symEllIntRF_comm_left] using this
      obtain ⟨n, hn⟩ := (htop.eventually (eventually_gt_atTop (∫ t in S, f t))).exists
      rw [hre n] at hn
      linarith [hbd n]
    rw [integral_undef hnot, ofReal_zero]
    rcases two_eq_zero_of_not hA0 hB0 hC0 hgood with ⟨h1, h2⟩ | ⟨h1, h3⟩ | ⟨h2, h3⟩
    · rw [h1, h2, ofReal_zero, symEllIntRF_zero_zero_ofReal hC0]
    · rw [h1, h3, ofReal_zero, symEllIntRF_comm_right, symEllIntRF_zero_zero_ofReal hB0]
    · rw [h2, h3, ofReal_zero, symEllIntRF_comm_left, symEllIntRF_comm_right,
        symEllIntRF_zero_zero_ofReal hA0]

/-- The integrand `1/√((a₁ + b₁t²)(a₂ + b₂t²))` is nonnegative and integrable on every `Ioo`
whose closure lies in a set where both quadratics are positive. -/
private lemma integrableOn_inv_sqrt_quadratic_product {a₁ b₁ a₂ b₂ u v : ℝ} {S : Set ℝ}
    (hQ : ∀ t ∈ S, 0 < a₁ + b₁ * t ^ 2 ∧ 0 < a₂ + b₂ * t ^ 2) (hS : Icc u v ⊆ S) :
    IntegrableOn (fun t => 1 / √((a₁ + b₁ * t ^ 2) * (a₂ + b₂ * t ^ 2))) (Ioo u v) := by
  refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioo_subset_Icc_self
  refine continuousOn_const.div (Real.continuous_sqrt.comp_continuousOn (by fun_prop)) ?_
  intro t ht
  obtain ⟨q1, q2⟩ := hQ t (hS ht)
  exact (Real.sqrt_pos.mpr (mul_pos q1 q2)).ne'

/-- DLMF 19.29.19 for `0 ≤ y < x` and both quadratics positive on `(y, x)`, **without an
integrability hypothesis**: when the integrand is not integrable two arguments of `R_F` vanish
and both sides are `0` in Lean's totalization. -/
theorem integral_quadratic_product_eq_symEllIntRF {a₁ b₁ a₂ b₂ x y : ℝ} (hy : 0 ≤ y)
    (hxy : y < x) (hQ : ∀ t ∈ Ioo y x, 0 < a₁ + b₁ * t ^ 2 ∧ 0 < a₂ + b₂ * t ^ 2) :
    ((∫ t in Ioo y x, 1 / √((a₁ + b₁ * t ^ 2) * (a₂ + b₂ * t ^ 2)) : ℝ) : ℂ) =
      symEllIntRF (ellRedQuadU a₁ b₁ a₂ b₂ x y ^ 2 + a₁ * b₂ : ℝ)
        (ellRedQuadU a₁ b₁ a₂ b₂ x y ^ 2 + a₂ * b₁ : ℝ) (ellRedQuadU a₁ b₁ a₂ b₂ x y ^ 2 : ℝ) := by
  set d := (x - y) / 2 with hd_def
  have hd : 0 < d := by rw [hd_def]; linarith
  set δ : ℕ → ℝ := fun n => d / ((n : ℝ) + 2) with hδ_def
  have hδpos : ∀ n, 0 < δ n := fun n => by positivity
  have hδd : ∀ n, δ n < d := fun n => by
    rw [hδ_def, div_lt_iff₀ (by positivity)]
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hδ0 : Tendsto δ atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  have hlt : ∀ n, y + δ n < x - δ n := fun n => by have := hδd n; rw [hd_def] at this; linarith
  have hIcc : ∀ n, Icc (y + δ n) (x - δ n) ⊆ Ioo y x := fun n t ht =>
    ⟨by linarith [ht.1, hδpos n], by linarith [ht.2, hδpos n]⟩
  set Un : ℕ → ℝ := fun n => ellRedQuadU a₁ b₁ a₂ b₂ (x - δ n) (y + δ n) with hUn
  have hcU : ContinuousAt (fun s : ℝ => ellRedQuadU a₁ b₁ a₂ b₂ (x - s) (y + s)) 0 := by
    unfold ellRedQuadU
    refine ContinuousAt.div (by fun_prop) (by fun_prop) ?_
    simp only [sub_zero, add_zero]
    nlinarith
  have hU : Tendsto Un atTop (𝓝 (ellRedQuadU a₁ b₁ a₂ b₂ x y)) := by
    have := hcU.tendsto.comp hδ0
    simp only [sub_zero, add_zero] at this
    exact this
  have hcov : AECover (volume.restrict (Ioo y x)) atTop
      (fun n => Ioo (y + δ n) (x - δ n)) := by
    refine ⟨(ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun t ht => ?_),
      fun n => measurableSet_Ioo⟩
    have hm : 0 < min (t - y) (x - t) := lt_min (by linarith [ht.1]) (by linarith [ht.2])
    filter_upwards [hδ0.eventually (gt_mem_nhds hm)] with n hn
    exact ⟨by linarith [min_le_left (t - y) (x - t)], by linarith [min_le_right (t - y) (x - t)]⟩
  exact integral_eq_symEllIntRF_of_aecover hcov
    (fun n => Ioo_subset_Icc_self.trans (hIcc n))
    (fun t => div_nonneg zero_le_one (Real.sqrt_nonneg _))
    (fun n => integrableOn_inv_sqrt_quadratic_product hQ (hIcc n))
    ((hU.pow 2).add_const _) ((hU.pow 2).add_const _) (hU.pow 2)
    (fun n => ellRedQuadU_args_pos (by linarith [hδpos n]) (hlt n) fun t ht => hQ t (hIcc n ht))
    (fun n => integral_quadratic_product_eq_symEllIntRF_of_pos (by linarith [hδpos n]) (hlt n)
      fun t ht => hQ t (hIcc n ht))

/-- Rewriting `U` of (19.29.19) in the variable `1/x`, for the limit `x → ∞`. -/
private lemma quadU_eq_inv_form {x w A B : ℝ} (hx : 0 < x) (hxw : x ^ 2 - w ^ 2 ≠ 0) :
    (x * A + w * B) / (x ^ 2 - w ^ 2) = (x⁻¹ * A + w * (B / x ^ 2)) / (1 - w ^ 2 * x⁻¹ ^ 2) := by
  have h2e : 1 - w ^ 2 * x⁻¹ ^ 2 = (x ^ 2 - w ^ 2) / x ^ 2 := by field_simp
  rw [h2e]
  field_simp

/-- The case `x = ∞` of (19.29.19): for `0 ≤ y`, both quadratics positive on `(y, ∞)` and
`b₁b₂ > 0`, `∫_y^∞ dt/√((a₁ + b₁t²)(a₂ + b₂t²)) = R_F(b₁b₂y² + a₁b₂, b₁b₂y² + a₂b₁, b₁b₂y²)`
(`U → y√(b₁b₂)` as `x → ∞`), without an integrability hypothesis. -/
theorem integral_Ioi_quadratic_product_eq_symEllIntRF {a₁ b₁ a₂ b₂ y : ℝ} (hy : 0 ≤ y)
    (hQ : ∀ t ∈ Ioi y, 0 < a₁ + b₁ * t ^ 2 ∧ 0 < a₂ + b₂ * t ^ 2) (hb : 0 < b₁ * b₂) :
    ((∫ t in Ioi y, 1 / √((a₁ + b₁ * t ^ 2) * (a₂ + b₂ * t ^ 2)) : ℝ) : ℂ) =
      symEllIntRF (b₁ * b₂ * y ^ 2 + a₁ * b₂ : ℝ) (b₁ * b₂ * y ^ 2 + a₂ * b₁ : ℝ)
        (b₁ * b₂ * y ^ 2 : ℝ) := by
  set δ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 2) with hδ_def
  have hδpos : ∀ n, 0 < δ n := fun n => by positivity
  have hδ1 : ∀ n, δ n < 1 := fun n => by
    rw [hδ_def, div_lt_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hδ0 : Tendsto δ atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  set X : ℕ → ℝ := fun n => y + n + 2 with hX_def
  have hXtop : Tendsto X atTop atTop :=
    tendsto_atTop_add_const_right _ 2 (tendsto_atTop_add_const_left _ y tendsto_natCast_atTop_atTop)
  have hlt : ∀ n, y + δ n < X n := fun n => by
    have := hδ1 n; simp only [hX_def]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hX0 : ∀ n, 0 < X n := fun n => by
    simp only [hX_def]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hIcc : ∀ n, Icc (y + δ n) (X n) ⊆ Ioi y := fun n t ht => by
    show y < t; linarith [ht.1, hδpos n]
  set Un : ℕ → ℝ := fun n => ellRedQuadU a₁ b₁ a₂ b₂ (X n) (y + δ n) with hUn
  -- the limit of `U`
  set g : ℝ × ℝ → ℝ := fun p => (p.1 * √((a₁ + b₁ * p.2 ^ 2) * (a₂ + b₂ * p.2 ^ 2)) +
      p.2 * √((a₁ * p.1 ^ 2 + b₁) * (a₂ * p.1 ^ 2 + b₂))) / (1 - p.2 ^ 2 * p.1 ^ 2) with hg
  have hgc : ContinuousAt g (0, y) := by
    refine ContinuousAt.div (by fun_prop) (by fun_prop) ?_
    simp
  have hpair : Tendsto (fun n => ((X n)⁻¹, y + δ n)) atTop (𝓝 ((0 : ℝ), y)) := by
    refine (hXtop.inv_tendsto_atTop).prodMk_nhds ?_
    simpa using hδ0.const_add y
  have hgv : g (0, y) = y * √(b₁ * b₂) := by simp [hg]
  have hUg : ∀ n, Un n = g ((X n)⁻¹, y + δ n) := by
    intro n
    have hXn := hX0 n
    have hQX := hQ (X n) (hIcc n ⟨(hlt n).le, le_rfl⟩)
    have hdiv : (a₁ * (X n)⁻¹ ^ 2 + b₁) * (a₂ * (X n)⁻¹ ^ 2 + b₂) =
        (a₁ + b₁ * X n ^ 2) * (a₂ + b₂ * X n ^ 2) / (X n ^ 2) ^ 2 := by
      field_simp
    have hsq : √((a₁ * (X n)⁻¹ ^ 2 + b₁) * (a₂ * (X n)⁻¹ ^ 2 + b₂)) =
        √((a₁ + b₁ * X n ^ 2) * (a₂ + b₂ * X n ^ 2)) / X n ^ 2 := by
      rw [hdiv, Real.sqrt_div' _ (by positivity), Real.sqrt_sq (by positivity)]
    simp only [hUn, hg, ellRedQuadU, hsq]
    exact quadU_eq_inv_form hXn (by nlinarith [hlt n, hδpos n])
  have hU : Tendsto Un atTop (𝓝 (y * √(b₁ * b₂))) := by
    rw [← hgv]
    exact (hgc.tendsto.comp hpair).congr fun n => (hUg n).symm
  have hL : (y * √(b₁ * b₂)) ^ 2 = b₁ * b₂ * y ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hb.le]; ring
  have hcov : AECover (volume.restrict (Ioi y)) atTop (fun n => Ioo (y + δ n) (X n)) := by
    refine ⟨(ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_),
      fun n => measurableSet_Ioo⟩
    have ht' : 0 < t - y := sub_pos.mpr ht
    filter_upwards [hδ0.eventually (gt_mem_nhds ht'), hXtop.eventually (eventually_gt_atTop t)]
      with n hn hXn
    exact ⟨by linarith, hXn⟩
  have hA := (hU.pow 2).add_const (a₁ * b₂)
  have hB := (hU.pow 2).add_const (a₂ * b₁)
  have hC := hU.pow 2
  rw [hL] at hA hB hC
  exact integral_eq_symEllIntRF_of_aecover hcov
    (fun n => Ioo_subset_Icc_self.trans (hIcc n))
    (fun t => div_nonneg zero_le_one (Real.sqrt_nonneg _))
    (fun n => integrableOn_inv_sqrt_quadratic_product hQ (hIcc n)) hA hB hC
    (fun n => ellRedQuadU_args_pos (by linarith [hδpos n]) (hlt n) fun t ht => hQ t (hIcc n ht))
    (fun n => integral_quadratic_product_eq_symEllIntRF_of_pos (by linarith [hδpos n]) (hlt n)
      fun t ht => hQ t (hIcc n ht))

/-- The six orderings of a three-element multiset equality. -/
private lemma multiset_triple_cases {α β γ p q r : ℝ}
    (h : ({α, β, γ} : Multiset ℝ) = {p, q, r}) :
    (α = p ∧ β = q ∧ γ = r) ∨ (α = p ∧ β = r ∧ γ = q) ∨ (α = q ∧ β = p ∧ γ = r) ∨
      (α = q ∧ β = r ∧ γ = p) ∨ (α = r ∧ β = p ∧ γ = q) ∨ (α = r ∧ β = q ∧ γ = p) := by
  have h' : [α, β, γ].Perm [p, q, r] := by
    rw [Multiset.insert_eq_cons, Multiset.insert_eq_cons, Multiset.insert_eq_cons,
      Multiset.insert_eq_cons] at h
    exact Multiset.coe_eq_coe.mp h
  have hm : α ∈ [p, q, r] := h'.subset (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with hm | hm | hm
  · rw [hm] at h'
    rcases List.perm_pair.mp h'.cons_inv with h2 | h2 <;>
      simp only [List.cons.injEq, and_true] at h2
    · exact Or.inl ⟨hm, h2⟩
    · exact Or.inr (Or.inl ⟨hm, h2⟩)
  · have h3 : [β, γ].Perm [p, r] := by
      rw [hm] at h'; exact (h'.trans (List.Perm.swap q p [r])).cons_inv
    rcases List.perm_pair.mp h3 with h2 | h2 <;> simp only [List.cons.injEq, and_true] at h2
    · exact Or.inr (Or.inr (Or.inl ⟨hm, h2⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hm, h2⟩)))
  · have h3 : [β, γ].Perm [p, q] := by
      rw [hm] at h'
      exact (h'.trans ((List.Perm.cons p (List.Perm.swap r q ([] : List ℝ))).trans
        (List.Perm.swap r p [q]))).cons_inv
    rcases List.perm_pair.mp h3 with h2 | h2 <;> simp only [List.cons.injEq, and_true] at h2
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hm, h2⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hm, h2⟩))))

/-- A function symmetric in its three arguments takes equal values on two triples with the
same multiset of entries. -/
private lemma eq_of_multiset_triple {g : ℝ → ℝ → ℝ → ℂ} (hl : ∀ a b c, g b a c = g a b c)
    (hr : ∀ a b c, g a c b = g a b c) {α β γ p q r : ℝ}
    (h : ({α, β, γ} : Multiset ℝ) = {p, q, r}) : g α β γ = g p q r := by
  have cyc : ∀ a b c, g a b c = g b c a := fun a b c => (hl a b c).symm.trans (hr b c a)
  rcases multiset_triple_cases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
  first
    | rfl
    | exact cyc _ _ _
    | exact (cyc _ _ _).symm
    | exact (hl _ _ _).symm
    | exact (hr _ _ _).symm
    | exact ((hr _ _ _).symm.trans (cyc _ _ _))

/-- `R_F(u + α, u + β, u + γ)` depends only on the multiset `{α, β, γ}`. -/
private lemma symEllIntRF_add_eq_of_multiset {α β γ p q r : ℝ} (u : ℝ)
    (h : ({α, β, γ} : Multiset ℝ) = {p, q, r}) :
    symEllIntRF (u + α : ℝ) (u + β : ℝ) (u + γ : ℝ) =
      symEllIntRF (u + p : ℝ) (u + q : ℝ) (u + r : ℝ) :=
  eq_of_multiset_triple (g := fun a b c => symEllIntRF (u + a : ℝ) (u + b : ℝ) (u + c : ℝ))
    (fun _ _ _ => symEllIntRF_comm_left _ _ _) (fun _ _ _ => symEllIntRF_comm_right _ _ _) h

/-- The conversion of `R_F(V + a₁b₂, V + a₂b₁, V)` to Legendre's form in (19.14.4) and
(19.14.8): with `α ≤ β ≤ γ` the ordered permutation of `0, a₁b₂, a₂b₁`, not all zero, and
nonnegative arguments, it equals `(γ - α)^{-1/2} F(φ, k)`, `sin²φ = (γ - α)/(V + γ)`. -/
private lemma symEllIntRF_eq_incEllIntFk_of_multiset {a₁ b₁ a₂ b₂ V α β γ : ℝ}
    (hperm : ({α, β, γ} : Multiset ℝ) = {0, a₁ * b₂, a₂ * b₁}) (h₁ : α ≤ β) (h₂ : β ≤ γ)
    (hne : ¬ (a₁ * b₂ = 0 ∧ a₂ * b₁ = 0)) (hA0 : 0 ≤ V + a₁ * b₂) (hB0 : 0 ≤ V + a₂ * b₁)
    (hC0 : 0 ≤ V) :
    symEllIntRF (V + a₁ * b₂ : ℝ) (V + a₂ * b₁ : ℝ) (V : ℝ) =
      ((Real.sqrt (γ - α))⁻¹ : ℝ) *
        incEllIntFk (Real.arcsin (Real.sqrt ((γ - α) / (V + γ))))
          (Real.sqrt ((γ - β) / (γ - α))) := by
  have hmem : ∀ w, w ∈ ({α, β, γ} : Multiset ℝ) → 0 ≤ V + w := by
    intro w hw
    rw [hperm] at hw
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · simpa using hC0
    · exact hA0
    · exact hB0
  have hα0 := hmem α (by simp)
  have hβ0 := hmem β (by simp)
  have hγα : α < γ := by
    refine lt_of_le_of_ne (h₁.trans h₂) fun hαγ => hne ?_
    have hβα : β = α := le_antisymm (hαγ ▸ h₂) h₁
    have h0 : (0 : ℝ) ∈ ({α, β, γ} : Multiset ℝ) := by rw [hperm]; simp
    have h1 : a₁ * b₂ ∈ ({α, β, γ} : Multiset ℝ) := by rw [hperm]; simp
    have h2 : a₂ * b₁ ∈ ({α, β, γ} : Multiset ℝ) := by rw [hperm]; simp
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton,
      hβα, ← hαγ, or_self] at h0 h1 h2
    exact ⟨h1.trans h0.symm, h2.trans h0.symm⟩
  have hga : 0 < γ - α := by linarith
  have hUγ : 0 < V + γ := by linarith
  -- the amplitude
  set s := (γ - α) / (V + γ) with hs
  have hs0 : 0 < s := div_pos hga hUγ
  have hs1 : s ≤ 1 := (div_le_one hUγ).mpr (by linarith)
  have hsq0 : 0 < √s := Real.sqrt_pos.mpr hs0
  have hsq1 : √s ≤ 1 := Real.sqrt_le_one.mpr hs1
  set φ := Real.arcsin √s with hφ
  have hsinφ : Real.sin φ = √s := Real.sin_arcsin (by linarith) hsq1
  have hφ0 : 0 < φ := Real.arcsin_pos.mpr hsq0
  have hφ1 : φ ≤ π / 2 := Real.arcsin_le_pi_div_two _
  have hcsc : 1 / Real.sin φ ^ 2 = (V + γ) / (γ - α) := by
    rw [hsinφ, Real.sq_sqrt hs0.le, hs, one_div_div]
  rw [incEllIntFk_ofReal_eq_integral, ← symEllIntRF_csc_sq_eq_integral hφ0 hφ1, hcsc]
  set k2 := (γ - β) / (γ - α) with hk2
  have hk20 : 0 ≤ k2 := div_nonneg (by linarith [h₂]) hga.le
  have hkk : ((√k2 : ℝ) : ℂ) ^ 2 = (k2 : ℂ) := by rw [← ofReal_pow, Real.sq_sqrt hk20]
  rw [hkk]
  set l := 1 / (γ - α) with hl
  have hl0 : 0 < l := by positivity
  have e1 : (((V + γ) / (γ - α) : ℝ) : ℂ) - 1 = (l : ℂ) * ((V + α : ℝ) : ℂ) := by
    rw [← ofReal_one, ← ofReal_sub, ← ofReal_mul]; congr 1; rw [hl]; field_simp [hga.ne']; ring
  have e2 : (((V + γ) / (γ - α) : ℝ) : ℂ) - (k2 : ℂ) =
      (l : ℂ) * ((V + β : ℝ) : ℂ) := by
    rw [← ofReal_sub, ← ofReal_mul]; congr 1; rw [hl, hk2]; field_simp [hga.ne']; ring
  have e3 : ((((V + γ) / (γ - α) : ℝ)) : ℂ) = (l : ℂ) * ((V + γ : ℝ) : ℂ) := by
    rw [← ofReal_mul]; congr 1; rw [hl]; field_simp [hga.ne']
  rw [e1, e2, e3, symEllIntRF_scale hl0]
  have hlsq : ((l : ℂ) ^ (1 / 2 : ℂ))⁻¹ = ((√(γ - α) : ℝ) : ℂ) := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow hl0.le,
      ← Real.sqrt_eq_rpow, hl, Real.sqrt_div' _ hga.le, Real.sqrt_one]
    push_cast
    rw [inv_div, div_one]
  rw [hlsq, ← mul_assoc, ← ofReal_mul, inv_mul_cancel₀ (Real.sqrt_pos.mpr hga).ne', ofReal_one,
    one_mul]
  have := symEllIntRF_add_eq_of_multiset V hperm
  rw [this, add_zero, symEllIntRF_comm_left, symEllIntRF_comm_right]
  exact (symEllIntRF_comm_left _ _ _).symm.trans (symEllIntRF_comm_right _ _ _)

/-- DLMF 19.14.4–19.14.6:
`∫_y^x dt/√((a₁ + b₁t²)(a₂ + b₂t²)) = (γ - α)^{-1/2} F(φ, k)`, `k² = (γ - β)/(γ - α)`,
`sin²φ = (γ - α)/(U² + γ)` with `U` of (19.14.6), `φ ∈ [0, π/2]`. -/
@[dlmf 19.14.E4, dlmf 19.14.E5, dlmf 19.14.E6]
theorem integral_inv_sqrt_two_quadratics {a₁ b₁ a₂ b₂ x y α β γ : ℝ}
    (h : QuadraticProductReductionHyp a₁ b₁ a₂ b₂ x y α β γ) :
    ((∫ t in y..x, (Real.sqrt ((a₁ + b₁ * t ^ 2) * (a₂ + b₂ * t ^ 2)))⁻¹ : ℝ) : ℂ) =
      ((Real.sqrt (γ - α))⁻¹ : ℝ) *
        incEllIntFk (Real.arcsin (Real.sqrt ((γ - α) / (ellRedQuadU a₁ b₁ a₂ b₂ x y ^ 2 + γ))))
          (Real.sqrt ((γ - β) / (γ - α))) := by
  have hxy := h.y_lt_x
  have hy := h.y_nonneg
  rw [intervalIntegral.integral_of_le hxy.le, integral_Ioc_eq_integral_Ioo]
  simp_rw [inv_eq_one_div]
  rw [integral_quadratic_product_eq_symEllIntRF hy hxy h.pos]
  set U := ellRedQuadU a₁ b₁ a₂ b₂ x y with hU
  -- nonnegativity of the arguments
  have hc : ∀ {c d : ℝ}, Continuous fun t : ℝ => c + d * t ^ 2 := by intros; fun_prop
  have endpt : ∀ {c d : ℝ}, (∀ t ∈ Ioo y x, 0 < c + d * t ^ 2) →
      0 ≤ c + d * x ^ 2 ∧ 0 ≤ c + d * y ^ 2 := by
    intro c d hcd
    exact ⟨ge_of_tendsto (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
        (eventually_of_mem (Ioo_mem_nhdsLT hxy) fun t ht => (hcd t ht).le),
      ge_of_tendsto (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
        (eventually_of_mem (Ioo_mem_nhdsGT hxy) fun t ht => (hcd t ht).le)⟩
  obtain ⟨px1, py1⟩ := endpt fun t ht => (h.pos t ht).1
  obtain ⟨px2, py2⟩ := endpt fun t ht => (h.pos t ht).2
  have hd : x ^ 2 - y ^ 2 ≠ 0 := by nlinarith
  have hUe : U = (x * (√(a₁ + b₁ * y ^ 2) * √(a₂ + b₂ * y ^ 2)) +
      y * (√(a₁ + b₁ * x ^ 2) * √(a₂ + b₂ * x ^ 2))) / (x ^ 2 - y ^ 2) := by
    rw [hU, ellRedQuadU, Real.sqrt_mul py1, Real.sqrt_mul px1]
  have hB0 : 0 ≤ U ^ 2 + a₂ * b₁ := by
    rw [hUe, ← quadratic_product_sq_identity hd (Real.sq_sqrt px1) (Real.sq_sqrt px2)
      (Real.sq_sqrt py1) (Real.sq_sqrt py2)]
    positivity
  have hA0 : 0 ≤ U ^ 2 + a₁ * b₂ := by
    have e : U = (x * (√(a₂ + b₂ * y ^ 2) * √(a₁ + b₁ * y ^ 2)) +
        y * (√(a₂ + b₂ * x ^ 2) * √(a₁ + b₁ * x ^ 2))) / (x ^ 2 - y ^ 2) := by
      rw [hUe]; ring
    rw [e, ← quadratic_product_sq_identity hd (Real.sq_sqrt px2) (Real.sq_sqrt px1)
      (Real.sq_sqrt py2) (Real.sq_sqrt py1)]
    positivity
  have hC0 : 0 ≤ U ^ 2 := sq_nonneg U
  rw [one_div]
  exact symEllIntRF_eq_incEllIntFk_of_multiset h.perm h.le₁ h.le₂ h.not_all_zero hA0 hB0 hC0


/-- A function continuous on `[y, x]` and positive on `(y, x)` is nonnegative at `x`. -/
private lemma nonneg_right_of_pos_on_Ioo {f : ℝ → ℝ} (hf : Continuous f) {x y : ℝ} (hyx : y < x)
    (hpos : ∀ t ∈ Ioo y x, 0 < f t) : 0 ≤ f x :=
  ge_of_tendsto (hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (Filter.eventually_of_mem (Ioo_mem_nhdsLT hyx) fun t ht => (hpos t ht).le)

/-- A function continuous on `[y, x]` and positive on `(y, x)` is nonnegative at `y`. -/
private lemma nonneg_left_of_pos_on_Ioo {f : ℝ → ℝ} (hf : Continuous f) {x y : ℝ} (hyx : y < x)
    (hpos : ∀ t ∈ Ioo y x, 0 < f t) : 0 ≤ f y :=
  ge_of_tendsto (hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (Filter.eventually_of_mem (Ioo_mem_nhdsGT hyx) fun t ht => (hpos t ht).le)

/-- The product of the quadratics is nonnegative at both endpoints. -/
private lemma quadratic_product_nonneg {a₁ b₁ a₂ b₂ x y α β γ : ℝ}
    (h : QuadraticProductReductionHyp a₁ b₁ a₂ b₂ x y α β γ) :
    0 ≤ (a₁ + b₁ * x ^ 2) * (a₂ + b₂ * x ^ 2) ∧ 0 ≤ (a₁ + b₁ * y ^ 2) * (a₂ + b₂ * y ^ 2) := by
  have hc : Continuous fun t : ℝ => (a₁ + b₁ * t ^ 2) * (a₂ + b₂ * t ^ 2) := by fun_prop
  have hp : ∀ t ∈ Ioo y x, 0 < (a₁ + b₁ * t ^ 2) * (a₂ + b₂ * t ^ 2) := fun t ht =>
    mul_pos (h.pos t ht).1 (h.pos t ht).2
  exact ⟨nonneg_right_of_pos_on_Ioo hc h.y_lt_x hp, nonneg_left_of_pos_on_Ioo hc h.y_lt_x hp⟩

/-- DLMF 19.14.7 (the case `y = 0` of 19.14.4–19.14.6): `sin²φ = (γ - α)x²/(a₁a₂ + γx²)`. -/
@[dlmf 19.14.E7]
theorem integral_inv_sqrt_two_quadratics_zero {a₁ b₁ a₂ b₂ x α β γ : ℝ}
    (h : QuadraticProductReductionHyp a₁ b₁ a₂ b₂ x 0 α β γ) :
    ((∫ t in (0 : ℝ)..x, (Real.sqrt ((a₁ + b₁ * t ^ 2) * (a₂ + b₂ * t ^ 2)))⁻¹ : ℝ) : ℂ) =
      ((Real.sqrt (γ - α))⁻¹ : ℝ) *
        incEllIntFk (Real.arcsin (Real.sqrt ((γ - α) * x ^ 2 / (a₁ * a₂ + γ * x ^ 2))))
          (Real.sqrt ((γ - β) / (γ - α))) := by
  rw [integral_inv_sqrt_two_quadratics h]
  have hx : 0 < x := h.y_lt_x
  have h0 := (quadratic_product_nonneg h).2
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero] at h0
  have hU : ellRedQuadU a₁ b₁ a₂ b₂ x 0 ^ 2 = a₁ * a₂ / x ^ 2 := by
    unfold ellRedQuadU
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero,
      zero_mul, sub_zero]
    rw [div_pow, mul_pow, Real.sq_sqrt h0]
    field_simp
  congr 4
  rw [hU, show a₁ * a₂ / x ^ 2 + γ = (a₁ * a₂ + γ * x ^ 2) / x ^ 2 by field_simp,
    div_div_eq_mul_div]

/-- DLMF 19.14.8 (the case `x = ∞`): `∫_y^∞ dt/√((a₁ + b₁t²)(a₂ + b₂t²)) = (γ - α)^{-1/2} F(φ, k)`
with `sin²φ = (γ - α)/(b₁b₂y² + γ)`, for `y ≥ 0`, both quadratics positive on `(y, ∞)`,
`b₁b₂ > 0`, and `α ≤ β ≤ γ` as in (19.14.4). -/
@[dlmf 19.14.E8]
theorem integral_inv_sqrt_two_quadratics_infty {a₁ b₁ a₂ b₂ y α β γ : ℝ} (hy : 0 ≤ y)
    (hpos : ∀ t ∈ Ioi y, 0 < a₁ + b₁ * t ^ 2 ∧ 0 < a₂ + b₂ * t ^ 2) (hb : 0 < b₁ * b₂)
    (hperm : ({α, β, γ} : Multiset ℝ) = {0, a₁ * b₂, a₂ * b₁}) (h₁ : α ≤ β) (h₂ : β ≤ γ)
    (hne : ¬ (a₁ * b₂ = 0 ∧ a₂ * b₁ = 0)) :
    ((∫ t in Ioi y, (Real.sqrt ((a₁ + b₁ * t ^ 2) * (a₂ + b₂ * t ^ 2)))⁻¹ : ℝ) : ℂ) =
      ((Real.sqrt (γ - α))⁻¹ : ℝ) *
        incEllIntFk (Real.arcsin (Real.sqrt ((γ - α) / (b₁ * b₂ * y ^ 2 + γ))))
          (Real.sqrt ((γ - β) / (γ - α))) := by
  simp_rw [inv_eq_one_div]
  rw [integral_Ioi_quadratic_product_eq_symEllIntRF hy hpos hb, one_div]
  -- both leading coefficients are positive
  have hlead : ∀ {c d : ℝ}, (∀ t ∈ Ioi y, 0 < c + d * t ^ 2) → 0 ≤ d := by
    intro c d hcd
    by_contra hd
    replace hd := not_le.mp hd
    have ht : y < |c| / (-d) + y + 1 := by
      have : 0 ≤ |c| / (-d) := div_nonneg (abs_nonneg c) (by linarith)
      linarith
    have h1 := hcd _ ht
    have hdiv : -d * (|c| / (-d)) = |c| := by field_simp [hd.ne]
    have hc := le_abs_self c
    have hz : 0 ≤ |c| / (-d) := div_nonneg (abs_nonneg c) (by linarith)
    nlinarith [mul_nonneg (mul_nonneg hz (by linarith : (0 : ℝ) ≤ -d)) hz,
      mul_nonneg (by linarith : (0 : ℝ) ≤ -d) (by linarith : (0 : ℝ) ≤ y + 1),
      mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ -d) hy) hz]
  have hb₁ : 0 < b₁ := lt_of_le_of_ne (hlead fun t ht => (hpos t ht).1) fun h => by
    rw [← h, zero_mul] at hb; exact lt_irrefl _ hb
  have hb₂ : 0 < b₂ := lt_of_le_of_ne (hlead fun t ht => (hpos t ht).2) fun h => by
    rw [← h, mul_zero] at hb; exact lt_irrefl _ hb
  have hsub : Ioo y (y + 1) ⊆ Ioi y := Ioo_subset_Ioi_self
  have hA0 : 0 ≤ b₁ * b₂ * y ^ 2 + a₁ * b₂ := by
    have := nonneg_left_of_pos_on_Ioo (f := fun t => b₁ * b₂ * t ^ 2 + a₁ * b₂) (by fun_prop)
      (lt_add_one y) fun t ht => by
        have := mul_pos hb₂ (hpos t (hsub ht)).1
        linarith
    exact this
  have hB0 : 0 ≤ b₁ * b₂ * y ^ 2 + a₂ * b₁ := by
    have := nonneg_left_of_pos_on_Ioo (f := fun t => b₁ * b₂ * t ^ 2 + a₂ * b₁) (by fun_prop)
      (lt_add_one y) fun t ht => by
        have := mul_pos hb₁ (hpos t (hsub ht)).2
        linarith
    exact this
  exact symEllIntRF_eq_incEllIntFk_of_multiset hperm h₁ h₂ hne hA0 hB0 (by positivity)

/-- DLMF 19.14.9 (the case `a₁ + b₁y² = 0` of 19.14.4–19.14.6):
`sin²φ = (γ - α)(x² - y²)/(γ(x² - y²) - a₁(a₂ + b₂x²))`. -/
@[dlmf 19.14.E9]
theorem integral_inv_sqrt_two_quadratics_left {a₁ b₁ a₂ b₂ x y α β γ : ℝ}
    (h : QuadraticProductReductionHyp a₁ b₁ a₂ b₂ x y α β γ) (hy : a₁ + b₁ * y ^ 2 = 0) :
    ((∫ t in y..x, (Real.sqrt ((a₁ + b₁ * t ^ 2) * (a₂ + b₂ * t ^ 2)))⁻¹ : ℝ) : ℂ) =
      ((Real.sqrt (γ - α))⁻¹ : ℝ) *
        incEllIntFk (Real.arcsin (Real.sqrt ((γ - α) * (x ^ 2 - y ^ 2) /
            (γ * (x ^ 2 - y ^ 2) - a₁ * (a₂ + b₂ * x ^ 2)))))
          (Real.sqrt ((γ - β) / (γ - α))) := by
  rw [integral_inv_sqrt_two_quadratics h]
  have hxy : 0 < x ^ 2 - y ^ 2 := by
    have := h.y_nonneg; have := h.y_lt_x; nlinarith
  have h0 := (quadratic_product_nonneg h).1
  have hU : ellRedQuadU a₁ b₁ a₂ b₂ x y ^ 2 = -a₁ * (a₂ + b₂ * x ^ 2) / (x ^ 2 - y ^ 2) := by
    unfold ellRedQuadU
    rw [hy, zero_mul, Real.sqrt_zero, mul_zero, zero_add, div_pow, mul_pow, Real.sq_sqrt h0]
    have hb : b₁ * y ^ 2 = -a₁ := by linarith
    rw [show (a₁ + b₁ * x ^ 2) = b₁ * (x ^ 2 - y ^ 2) by linarith,
      div_eq_div_iff (pow_ne_zero 2 hxy.ne') hxy.ne']
    linear_combination (x ^ 2 - y ^ 2) ^ 2 * (a₂ + b₂ * x ^ 2) * hb
  congr 4
  rw [hU, show -a₁ * (a₂ + b₂ * x ^ 2) / (x ^ 2 - y ^ 2) + γ =
      (γ * (x ^ 2 - y ^ 2) - a₁ * (a₂ + b₂ * x ^ 2)) / (x ^ 2 - y ^ 2) by field_simp; ring,
    div_div_eq_mul_div]

/-- DLMF 19.14.10 (the case `a₁ + b₁x² = 0` of 19.14.4–19.14.6):
`sin²φ = (γ - α)(y² - x²)/(γ(y² - x²) - a₁(a₂ + b₂y²))`. -/
@[dlmf 19.14.E10]
theorem integral_inv_sqrt_two_quadratics_right {a₁ b₁ a₂ b₂ x y α β γ : ℝ}
    (h : QuadraticProductReductionHyp a₁ b₁ a₂ b₂ x y α β γ) (hx : a₁ + b₁ * x ^ 2 = 0) :
    ((∫ t in y..x, (Real.sqrt ((a₁ + b₁ * t ^ 2) * (a₂ + b₂ * t ^ 2)))⁻¹ : ℝ) : ℂ) =
      ((Real.sqrt (γ - α))⁻¹ : ℝ) *
        incEllIntFk (Real.arcsin (Real.sqrt ((γ - α) * (y ^ 2 - x ^ 2) /
            (γ * (y ^ 2 - x ^ 2) - a₁ * (a₂ + b₂ * y ^ 2)))))
          (Real.sqrt ((γ - β) / (γ - α))) := by
  rw [integral_inv_sqrt_two_quadratics h]
  have hxy : 0 < x ^ 2 - y ^ 2 := by
    have := h.y_nonneg; have := h.y_lt_x; nlinarith
  have hx0 : 0 < x := lt_of_le_of_lt h.y_nonneg h.y_lt_x
  have h0 := (quadratic_product_nonneg h).2
  have hU : ellRedQuadU a₁ b₁ a₂ b₂ x y ^ 2 = a₁ * (a₂ + b₂ * y ^ 2) / (x ^ 2 - y ^ 2) := by
    unfold ellRedQuadU
    rw [hx, zero_mul, Real.sqrt_zero, mul_zero, add_zero, div_pow, mul_pow, Real.sq_sqrt h0]
    have hb : b₁ * x ^ 2 = -a₁ := by linarith
    rw [show (a₁ + b₁ * y ^ 2) = -b₁ * (x ^ 2 - y ^ 2) by linarith,
      div_eq_div_iff (pow_ne_zero 2 hxy.ne') hxy.ne']
    linear_combination (-(x ^ 2 - y ^ 2) ^ 2 * (a₂ + b₂ * y ^ 2)) * hb
  congr 4
  rw [hU, show a₁ * (a₂ + b₂ * y ^ 2) / (x ^ 2 - y ^ 2) + γ =
      (a₁ * (a₂ + b₂ * y ^ 2) + γ * (x ^ 2 - y ^ 2)) / (x ^ 2 - y ^ 2) by field_simp,
    div_div_eq_mul_div, ← neg_div_neg_eq]
  ring_nf

end DLMF.EllipticIntegrals
