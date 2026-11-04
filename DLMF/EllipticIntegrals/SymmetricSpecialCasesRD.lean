/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.EllipticIntegrals.SymmetricSpecialCases

/-!
# Symmetric elliptic integrals: special cases of `R_D` and `R_{-a}` (DLMF §19.20(iv)–(v))

Special values, homogeneity, degenerate cases and the lemniscatic case of `R_D`, and the special
cases of `R_{-a}(𝐛; 𝐳)` with Euler's transformation.

## Main results

* `symmetricEllipticRD_self`, `symmetricEllipticRD_smul`, `symmetricEllipticRD_zero_self`,
  `symmetricEllipticRD_isEquivalent_zero`, `symmetricEllipticRD_self_right`,
  `symmetricEllipticRD_self_left`: special cases of `R_D` (DLMF 19.20.18–19.20.21).
* `lemniscate_second_symmetricEllipticRD`, `symmetricEllipticRD_lemniscatic`,
  `symmetricEllipticRD_lemniscatic_complex`: DLMF 19.20.22, 19.20.23.
* `symmetricEllipticR_zero`, `symmetricEllipticR_neg_natCast`, `symmetricEllipticR_sum`,
  `symmetricEllipticR_euler`: special cases of `R_{-a}` and Euler's transformation (DLMF
  19.20.24–19.20.26).

## Implementation notes

The variables satisfy the constraints of §19.16(i) unless stated otherwise (DLMF 19.20.i.p1);
we state them explicitly. The lemniscatic case (19.20.23) is stated for real positive `x, y` and
in a corrected complex form for `ℜ x, ℜ y > 0`, as in
`DLMF.EllipticIntegrals.SymmetricSpecialCases`. The decimal value in (19.20.22) is excluded as
numerical.

## References

* NIST DLMF §19.20.
-/

@[expose] public noncomputable section

open Complex Set Filter MeasureTheory Asymptotics
open scoped Real Topology

namespace DLMF.EllipticIntegrals

/-! ### §19.20(iv) `R_D` -/

/-- DLMF 19.20.18 (first): `R_D(x, x, x) = x^{-3/2}`. -/
@[dlmf 19.20.E18]
theorem symmetricEllipticRD_self {x : ℂ} (hx : x ∈ slitPlane) : symmetricEllipticRD x x x =
    x ^ (-3 / 2 : ℂ) :=
  symmetricEllipticRJ_self hx

/-- DLMF 19.20.18 (second): `R_D(λx, λy, λz) = λ^{-3/2} R_D(x, y, z)`, `λ > 0`. -/
@[dlmf 19.20.E18]
theorem symmetricEllipticRD_smul {l : ℝ} (hl : 0 < l) {x y z : ℂ} (hx : x ∈ slitPlane)
    (hy : y ∈ slitPlane) (hz : z ∈ slitPlane) :
    symmetricEllipticRD (l * x) (l * y) (l * z) = (l : ℂ) ^ (-3 / 2 : ℂ) *
        symmetricEllipticRD x y z :=
  symmetricEllipticRJ_smul hl hx hy hz hz

/-- DLMF 19.20.18 (third): `R_D(0, y, y) = (3π/4) y^{-3/2}`. -/
@[dlmf 19.20.E18]
theorem symmetricEllipticRD_zero_self {y : ℂ} (hy : y ∈ slitPlane) :
    symmetricEllipticRD 0 y y = (3 * π / 4) * y ^ (-3 / 2 : ℂ) := by
  rw [symmetricEllipticRD_zero_left hy hy]
  have : (![y, y] : Fin 2 → ℂ) = fun _ => y := by funext i; fin_cases i <;> rfl
  rw [this, symmetricEllipticR_const _ _ hy (Complex.Gamma_ne_zero_of_re_pos (by simp; norm_num))]
  congr 2; ring

/-- DLMF 19.20.18 (fourth): `R_D(0, 0, z) = ∞`: the defining integrand is not integrable. -/
@[dlmf 19.20.E18]
theorem not_integrableOn_symmetricEllipticRD_zero_zero {z : ℂ} (hz : z ∈ slitPlane) :
    ¬ IntegrableOn (fun t => (carlsonRootProduct 0 0 z t * ((t : ℂ) + z))⁻¹) (Ioi 0) :=
  not_integrableOn_symmetricEllipticRJ_integrand_zero_zero hz hz

/-- The rescaled integrand `(√(zu + x) √(zu + y) (u + 1)^{3/2})⁻¹` of `√z R_D(x, y, z)`. -/
private noncomputable def symmetricEllipticRDScaledIntegrand (x y z u : ℝ) : ℝ :=
  (√(z * u + x) * √(z * u + y) * (√(u + 1) * (u + 1)))⁻¹

/-- `R_D(x, y, z)` for positive real arguments as a real integral. -/
private lemma symmetricEllipticRD_eq_ofReal_integral {x y z : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hz : 0 < z) :
    symmetricEllipticRD x y z = ((3 / 2 * ∫ t in Ioi (0 : ℝ),
      (√(t + x) * √(t + y) * √(t + z) * (t + z))⁻¹ : ℝ) : ℂ) := by
  have hneg : ¬ IsNegReal (z : ℂ) := fun h => by simp [IsNegReal] at h; linarith
  unfold symmetricEllipticRD symmetricEllipticRJ
  simp only [hneg, ↓reduceIte]
  rw [ofReal_mul, ← integral_complex_ofReal]
  push_cast
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht : (0 : ℝ) < t := ht
  simp only [carlsonRootProduct]
  rw [show (t : ℂ) + x = ((t + x : ℝ) : ℂ) by push_cast; ring,
    show (t : ℂ) + y = ((t + y : ℝ) : ℂ) by push_cast; ring,
    show (t : ℂ) + z = ((t + z : ℝ) : ℂ) by push_cast; ring,
    Carlson.ofReal_cpow_half (by linarith), Carlson.ofReal_cpow_half (by linarith),
    Carlson.ofReal_cpow_half (by linarith)]

/-- `√z ∫₀^∞ (√(t+x) √(t+y) √(t+z) (t+z))⁻¹ dt = ∫₀^∞ symmetricEllipticRDScaledIntegrand x y z u
du`. -/
private lemma sqrt_mul_integral_eq {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    √z * ∫ t in Ioi (0 : ℝ), (√(t + x) * √(t + y) * √(t + z) * (t + z))⁻¹ =
      ∫ u in Ioi (0 : ℝ), symmetricEllipticRDScaledIntegrand x y z u := by
  have h := integral_comp_mul_left_Ioi
    (fun t : ℝ => (√(t + x) * √(t + y) * √(t + z) * (t + z))⁻¹) 0 hz
  rw [mul_zero, smul_eq_mul] at h
  rw [show (∫ t in Ioi (0 : ℝ), (√(t + x) * √(t + y) * √(t + z) * (t + z))⁻¹) =
      z * ∫ u in Ioi (0 : ℝ), (√(z * u + x) * √(z * u + y) * √(z * u + z) * (z * u + z))⁻¹ by
    rw [h]; field_simp, ← mul_assoc, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
  have hu : (0 : ℝ) < u := hu
  simp only [symmetricEllipticRDScaledIntegrand]
  have e : z * u + z = z * (u + 1) := by ring
  rw [e, Real.sqrt_mul hz.le]
  have hs := Real.sqrt_pos.mpr hz
  have h1 := Real.sqrt_pos.mpr (show 0 < u + 1 by linarith)
  have h2 := Real.sqrt_pos.mpr (show 0 < z * u + x by positivity)
  have h3 := Real.sqrt_pos.mpr (show 0 < z * u + y by positivity)
  field_simp

/-- `∫₀^∞ (√(u + 1)(u + 1))⁻¹ du = 2`. -/
private lemma integral_inv_sqrt_mul_add_one :
    ∫ u in Ioi (0 : ℝ), (√(u + 1) * (u + 1))⁻¹ = 2 := by
  have hd : ∀ u ∈ Ioi (0 : ℝ), HasDerivAt (fun u : ℝ => -2 * (√(u + 1))⁻¹)
      ((√(u + 1) * (u + 1))⁻¹) u := by
    intro u hu
    have hu : (0 : ℝ) < u := hu
    have hp : 0 < u + 1 := by linarith
    have hs := Real.sqrt_pos.mpr hp
    have H := (((hasDerivAt_id u).add_const 1).sqrt hp.ne').inv hs.ne'
    convert H.const_mul (-2) using 1
    · rfl
    · simp only [id]
      rw [Real.sq_sqrt hp.le]
      field_simp
  have hint : IntegrableOn (fun u : ℝ => (√(u + 1) * (u + 1))⁻¹) (Ioi 0) := by
    have := integrableOn_add_rpow_Ioi_of_lt (a := -(3 / 2)) (c := 0) (m := 1) (by norm_num)
      (by norm_num)
    refine this.congr_fun (fun u hu => ?_) measurableSet_Ioi
    have hu : (0 : ℝ) < u := hu
    have hp : 0 < u + 1 := by linarith
    show (u + 1) ^ (-(3 / 2) : ℝ) = _
    rw [show (-(3 / 2) : ℝ) = -(1 / 2 + 1) by norm_num, Real.rpow_neg hp.le,
      Real.rpow_add hp, Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hlim : Tendsto (fun u : ℝ => -2 * (√(u + 1))⁻¹) atTop (𝓝 0) := by
    have : Tendsto (fun u : ℝ => √(u + 1)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp (tendsto_atTop_add_const_right _ 1 tendsto_id)
    simpa using this.inv_tendsto_atTop.const_mul (-2)
  have hc : ContinuousWithinAt (fun u : ℝ => -2 * (√(u + 1))⁻¹) (Ici 0) 0 :=
    (((Real.continuous_sqrt.comp (continuous_id.add continuous_const)).continuousAt.inv₀
      (by norm_num)).const_mul _).continuousWithinAt
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hc hd hint hlim]
  simp

/-- `∫₀^∞ symmetricEllipticRDScaledIntegrand x y z u du → 2/(√x √y)` as `z → 0+`. -/
private lemma tendsto_integral_symmetricEllipticRDScaledIntegrand {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) :
    Tendsto (fun z => ∫ u in Ioi (0 : ℝ), symmetricEllipticRDScaledIntegrand x y z u) (𝓝[>] 0)
      (𝓝 (2 / (√x * √y))) := by
  have hsx := Real.sqrt_pos.mpr hx
  have hsy := Real.sqrt_pos.mpr hy
  have hint : IntegrableOn (fun u : ℝ => (√(u + 1) * (u + 1))⁻¹) (Ioi 0) := by
    by_contra h
    have := integral_inv_sqrt_mul_add_one
    rw [integral_undef h] at this
    norm_num at this
  have hval : ∫ u in Ioi (0 : ℝ), (√x * √y)⁻¹ * (√(u + 1) * (u + 1))⁻¹ = 2 / (√x * √y) := by
    rw [integral_const_mul, integral_inv_sqrt_mul_add_one]; ring
  rw [← hval]
  refine tendsto_integral_filter_of_dominated_convergence
    (fun u => (√x * √y)⁻¹ * (√(u + 1) * (u + 1))⁻¹) ?_ ?_ (hint.const_mul _) ?_
  · exact Eventually.of_forall fun z => by
      unfold symmetricEllipticRDScaledIntegrand;
          exact (by fun_prop : Measurable _).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with z hz
    have hz : (0 : ℝ) < z := hz
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu : (0 : ℝ) < u := hu
    have h1 := Real.sqrt_pos.mpr (show 0 < u + 1 by linarith)
    have hX : √x ≤ √(z * u + x) := Real.sqrt_le_sqrt (by nlinarith)
    have hY : √y ≤ √(z * u + y) := Real.sqrt_le_sqrt (by nlinarith)
    unfold symmetricEllipticRDScaledIntegrand
    rw [Real.norm_of_nonneg (by positivity), ← mul_inv]
    gcongr
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu : (0 : ℝ) < u := hu
    have hc : Tendsto (fun z : ℝ => symmetricEllipticRDScaledIntegrand x y z u) (𝓝 0)
        (𝓝 (symmetricEllipticRDScaledIntegrand x y 0 u)) := by
      unfold symmetricEllipticRDScaledIntegrand
      refine ((Continuous.tendsto (by fun_prop) 0).mul tendsto_const_nhds).inv₀ ?_
      have h1 := Real.sqrt_pos.mpr (show 0 < u + 1 by linarith)
      simp only [zero_mul, zero_add]
      positivity
    have e : symmetricEllipticRDScaledIntegrand x y 0 u = (√x * √y)⁻¹ * (√(u + 1) * (u + 1))⁻¹ := by
      simp only [symmetricEllipticRDScaledIntegrand, zero_mul, zero_add, mul_inv]
    rw [← e]
    exact hc.mono_left nhdsWithin_le_nhds

/-- DLMF 19.20.19: `R_D(x, y, z) ∼ 3 x^{-1/2} y^{-1/2} z^{-1/2}` as `z/√(xy) → 0`; stated for
fixed `x, y > 0` and `z → 0+`. -/
@[dlmf 19.20.E19]
theorem symmetricEllipticRD_isEquivalent_zero {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (fun z : ℝ => symmetricEllipticRD x y z) ~[𝓝[>] 0]
      fun z : ℝ => ((3 * x ^ (-1 / 2 : ℝ) * y ^ (-1 / 2 : ℝ) * z ^ (-1 / 2 : ℝ) : ℝ) : ℂ) := by
  have hsx := Real.sqrt_pos.mpr hx
  have hsy := Real.sqrt_pos.mpr hy
  have hneg : ∀ w : ℝ, 0 < w → w ^ (-1 / 2 : ℝ) = (√w)⁻¹ := fun w hw => by
    rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg hw.le, Real.sqrt_eq_rpow]
  refine isEquivalent_of_tendsto_one ?_
  have hT := tendsto_integral_symmetricEllipticRDScaledIntegrand hx hy
  have hR : Tendsto (fun z => ((∫ u in Ioi (0 : ℝ), symmetricEllipticRDScaledIntegrand x y z u) *
      (√x * √y) / 2 : ℝ)) (𝓝[>] 0) (𝓝 1) := by
    have := (hT.mul_const (√x * √y)).div_const 2
    convert this using 2
    field_simp
  refine (Complex.continuous_ofReal.tendsto 1 |>.comp hR).congr' ?_ |>.trans (by simp)
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz : (0 : ℝ) < z := hz
  have hsz := Real.sqrt_pos.mpr hz
  simp only [Function.comp_apply, Pi.div_apply]
  rw [symmetricEllipticRD_eq_ofReal_integral hx hy hz, hneg x hx, hneg y hy, hneg z hz,
    ← sqrt_mul_integral_eq hx hy hz]
  push_cast
  field_simp

/-- DLMF 19.20.20: `R_D(x, y, y) = 3/(2(y - x)) (R_C(x, y) - √x/y)`, `x ≠ y`, `y ≠ 0`
(`x` admissible, `y ∈ ℂ \ (-∞, 0]`). -/
@[dlmf 19.20.E20]
theorem symmetricEllipticRD_self_right {x y : ℂ} (hx : IsCarlsonArgument x) (hy : y ∈ slitPlane)
    (hxy : x ≠ y) :
    symmetricEllipticRD x y y = 3 / (2 * (y - x)) *
        (symmetricEllipticRC x y - x ^ (1 / 2 : ℂ) / y) := by
  rcases hx with hx | rfl
  · exact symmetricEllipticRD_self_right_of_mem_slitPlane hx hy hxy
  · rw [symmetricEllipticRD_zero_self hy, ← symmetricEllipticRF_self_right 0
      (not_isNegReal_of_mem_slitPlane hy),
      symmetricEllipticRF_zero_self hy, zero_cpow (by norm_num : (1 / 2 : ℂ) ≠ 0)]
    have hy0 := slitPlane_ne_zero hy
    rw [show (-3 / 2 : ℂ) = -1 / 2 + (-1) by norm_num, cpow_add _ _ hy0, cpow_neg_one]
    field_simp
    ring

/-- DLMF 19.20.21: `R_D(x, x, z) = 3/(z - x) (R_C(z, x) - 1/√z)`, `x ≠ z`, `xz ≠ 0`
(`x, z ∈ ℂ \ (-∞, 0]`). -/
@[dlmf 19.20.E21]
theorem symmetricEllipticRD_self_left {x z : ℂ} (hx : x ∈ slitPlane) (hz : z ∈ slitPlane)
    (hxz : x ≠ z) :
    symmetricEllipticRD x x z = 3 / (z - x) * (symmetricEllipticRC z x - 1 / z ^ (1 / 2 : ℂ)) :=
  symmetricEllipticRD_self_left_eq_sub_symmetricEllipticRC hx hz hxz

/-- DLMF 19.20.22: the second lemniscate constant
`∫₀¹ t² dt/√(1 - t⁴) = (1/3) R_D(0, 2, 1) = Γ(3/4)²/(2π)^{1/2}` (decimal value excluded). -/
@[dlmf 19.20.E22]
theorem lemniscate_second_symmetricEllipticRD :
    ((∫ t in (0 : ℝ)..1, t ^ 2 / Real.sqrt (1 - t ^ 4) : ℝ) : ℂ) = (1 / 3) *
        symmetricEllipticRD 0 2 1 ∧
      (1 / 3) * symmetricEllipticRD 0 2 1 =
          ((Real.Gamma (3 / 4) ^ 2 / Real.sqrt (2 * π) : ℝ) : ℂ) := by
  refine ⟨integral_sq_div_sqrt_one_sub_pow_four, ?_⟩
  have hP := symmetricEllipticRF_mul_symmetricEllipticRD_lemniscate
  rw [symmetricEllipticRF_zero_one_two] at hP
  have h14 : 0 < Real.Gamma (1 / 4) := Real.Gamma_pos_of_pos (by norm_num)
  have hrefl := Real.Gamma_mul_Gamma_one_sub (1 / 4 : ℝ)
  rw [show (1 : ℝ) - 1 / 4 = 3 / 4 by norm_num, show π * (1 / 4 : ℝ) = π / 4 by ring,
    Real.sin_pi_div_four] at hrefl
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have hsπ : 0 < Real.sqrt (2 * π) := Real.sqrt_pos.mpr (by positivity)
  have hG3 : Real.Gamma (3 / 4) = π * Real.sqrt 2 / Real.Gamma (1 / 4) := by
    have hm : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    rw [eq_div_iff h14.ne', mul_comm, hrefl, div_div_eq_mul_div, div_eq_iff hs2.ne', mul_assoc, hm]
  have hsq : Real.sqrt (2 * π) ^ 2 = 2 * π := Real.sq_sqrt (by positivity)
  have h22 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hA0 : ((Real.Gamma (1 / 4) ^ 2 / (4 * Real.sqrt (2 * π)) : ℝ) : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (by positivity)
  have hD : (1 / 3) * symmetricEllipticRD 0 2 1 =
      (π : ℂ) / 4 / ((Real.Gamma (1 / 4) ^ 2 / (4 * Real.sqrt (2 * π)) : ℝ) : ℂ) := by
    rw [← hP]; field_simp
  rw [hD, hG3]
  have hreal : π / 4 / (Real.Gamma (1 / 4) ^ 2 / (4 * Real.sqrt (2 * π))) =
      (π * Real.sqrt 2 / Real.Gamma (1 / 4)) ^ 2 / Real.sqrt (2 * π) := by
    field_simp
    rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by norm_num)]
  rw [← hreal]
  push_cast
  ring

/-- DLMF 19.20.23 (general lemniscatic case), **domain-restricted** to real `x, y > 0`:
`R_D(x, y, a) = R_{-3/4}(5/4, 1/2; a², xy)`, `a = (x + y)/2`. -/
@[dlmf 19.20.E23 "domain-restricted: real positive x, y; see the complex form for Re x, Re y > 0"]
theorem symmetricEllipticRD_lemniscatic {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    symmetricEllipticRD x y ((x + y) / 2 : ℝ) =
      symmetricEllipticR (3 / 4) ![5 / 4, 1 / 2]
          ![((((x + y) / 2) ^ 2 : ℝ) : ℂ), ((x * y : ℝ) : ℂ)] := by
  have hm : 0 < (x + y) / 2 := by positivity
  rw [symmetricEllipticRD_eq_symmetricEllipticR (ofReal_mem_slitPlane.mpr hx)
    (ofReal_mem_slitPlane.mpr hy) (ofReal_mem_slitPlane.mpr hm)]
  have H := symmetricEllipticR_arithmetic_progression_quadratic_ofReal (a := 3 / 2) hx
      hy (by norm_num)
  norm_num at H
  convert H using 1 <;> norm_num


/-- DLMF 19.20.23, corrected complex form: `R_D(x, y, a) = R_{-3 / 4}(5 / 4, 1/2; a², xy)`,
`a = (x + y)/2`, for complex `x, y` with `ℜ x > 0` and `ℜ y > 0`. **Corrected from the printed DLMF
formula**: DLMF states it under the 19.16(i) constraints only, but it fails there, e.g. at
`x = -1 + i`, `y = -1 + 2i` the two sides differ by a factor `±i` (independent mpmath check,
2026-10-25). -/
@[dlmf 19.20.E23 "corrected: complex x, y with Re x, Re y > 0"]
theorem symmetricEllipticRD_lemniscatic_complex {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) :
    symmetricEllipticRD x y ((x + y) / 2) =
      symmetricEllipticR (3 / 4) ![5 / 4, 1 / 2] ![((x + y) / 2) ^ 2, x * y] := by
  have hm : 0 < ((x + y) / 2).re := by simp only [div_ofNat_re, add_re]; linarith
  rw [symmetricEllipticRD_eq_symmetricEllipticR (Or.inl hx) (Or.inl hy) (Or.inl hm)]
  have H := symmetricEllipticR_arithmetic_progression_quadratic (a := 3 / 2) (by norm_num) hx hy
  norm_num at H
  exact H


/-! ### §19.20(v) `R_{-a}(𝐛; 𝐳)` -/

/-- DLMF 19.20.24 (first): `R_0(𝐛; 𝐳) = 1`, when `Γ(c) ≠ 0`, `c = ∑ bⱼ` (slit-plane nodes). -/
@[dlmf 19.20.E24]
theorem symmetricEllipticR_zero {ι : Type*} [Fintype ι] (b : ι → ℂ) {z : ι → ℂ}
    (hz : z ∈ Carlson.carlsonRSlitDomain) (hb : Gamma (∑ i, b i) ≠ 0) :
    symmetricEllipticR 0 b z = 1 := by
  rw [symmetricEllipticR_of_mem _ _ hz]
  unfold Carlson.carlsonR
  have h := Carlson.regCarlsonR_natCast 0 b hz
  rw [Nat.cast_zero] at h
  rw [neg_zero, h, Carlson.regCarlsonRPolynomial_zero, mul_inv_cancel₀ hb]

/-- DLMF 19.20.24 (second): `R_N(𝐛; 𝐳) = N!/(c)_N T_N(𝐛, 𝐳)`, `N = 0, 1, 2, …`, `c = ∑ bⱼ`
with `0 < re c` (slit-plane nodes; `R_N` is `symmetricEllipticR (-N)`). -/
@[dlmf 19.20.E24]
theorem symmetricEllipticR_neg_natCast {n : ℕ} (N : ℕ) (b : Fin n → ℂ) {z : Fin n → ℂ}
    (hz : z ∈ Carlson.carlsonRSlitDomain) (hc : 0 < (∑ j, b j).re) :
    symmetricEllipticR (-(N : ℂ)) b z =
      (N.factorial : ℂ) / (ascPochhammer ℂ N).eval (∑ j, b j) *
          homogeneousHypergeometricPolynomial N b z := by
  have hcn : ∀ k : ℕ, ∑ j, b j ≠ -k := fun k h => by
    have he := congrArg Complex.re h
    simp only [neg_re, natCast_re] at he
    linarith [Nat.cast_nonneg (α := ℝ) k]
  rw [symmetricEllipticR_of_mem _ _ hz, Carlson.carlsonR, neg_neg,
    Carlson.regCarlsonR_natCast N b hz,
    ← Carlson.carlsonRPolynomialNumerator_div_eq N hcn z,
        carlsonRPolynomialNumerator_eq_factorial_mul_homogeneousHypergeometricPolynomial]
  ring

/-- DLMF 19.20.25: `R_{-c}(𝐛; 𝐳) = ∏ⱼ zⱼ^{-bⱼ}`, `c = ∑ bⱼ`, `Γ(c) ≠ 0`, slit-plane nodes.
From `Carlson.regCarlsonR_neg_sum_sub_nat`. -/
@[dlmf 19.20.E25]
theorem symmetricEllipticR_sum {ι : Type*} [Fintype ι] (b : ι → ℂ) {z : ι → ℂ}
    (hz : z ∈ Carlson.carlsonRSlitDomain) (hb : Gamma (∑ i, b i) ≠ 0) :
    symmetricEllipticR (∑ i, b i) b z = ∏ i, z i ^ (-b i) := by
  rw [symmetricEllipticR_of_mem _ _ hz]
  unfold Carlson.carlsonR
  have h := Carlson.regCarlsonR_neg_sum_sub_nat 0 b hz
  rw [Nat.cast_zero, sub_zero] at h
  rw [h, Carlson.regCarlsonRPolynomial_zero]
  field_simp

/-- DLMF 19.20.26: Euler's transformation `R_{-a}(𝐛; 𝐳) = ∏ⱼ zⱼ^{-bⱼ} R_{-a'}(𝐛; 𝐳⁻¹)`,
`a + a' = c = ∑ bⱼ`, for all complex `a, 𝐛` and slit-plane nodes. From
`Carlson.regCarlsonR_euler`. -/
@[dlmf 19.20.E26]
theorem symmetricEllipticR_euler {ι : Type*} [Fintype ι] (a : ℂ) (b : ι → ℂ) {z : ι → ℂ}
    (hz : z ∈ Carlson.carlsonRSlitDomain) :
    symmetricEllipticR a b z = (∏ i, z i ^ (-b i)) *
        symmetricEllipticR (∑ i, b i - a) b (fun i => (z i)⁻¹) := by
  rw [symmetricEllipticR_of_mem _ _ hz,
      symmetricEllipticR_of_mem _ _ (Carlson.carlsonRSlitDomain_inv hz)]
  unfold Carlson.carlsonR
  rw [Carlson.regCarlsonR_euler _ _ hz, show -(∑ i, b i) - -a = -(∑ i, b i - a) by ring]
  ring

end DLMF.EllipticIntegrals
