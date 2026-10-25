/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Elliptic.JacobiIdentities
public import DLMF.Elliptic.AGM
public import DLMF.Hypergeometric.Elementary

/-!
# The algebraic form of `F`, `arcsn`, and special values (Duverney Ch. 5)

* The substitution `t = sin θ` (by the one-dimensional change of variables for set integrals,
  which handles the integrable singularity at `t = 1`) gives
  `∫₀ˣ dt/√((1-t²)(1-mt²)) = F(arcsin x|m)` for `0 ≤ x ≤ 1`, hence `K = ∫₀¹`. It also gives
  Jacobi's `arcsn = F ∘ arcsin` with `sn ∘ arcsn = id` and
  `arcsn' = ((1-x²)(1-mx²))^{-1/2}` (Duverney Thm 5.9).
* `K(1/2) = Γ(1/4)²/(4√π)`, by Gauss's second summation theorem and the reflection formula.
  With `K = π/(2M)` this gives Gauss's constant `Γ(1/4)² M(1, 1/√2) = 2π^{3/2}`, and with
  Legendre's relation the value of `E(1/2)` (Duverney (5.38), Ex. 5.9).
* `K(-1) = K(1/2)/√2` by homogeneity of the AGM, so the lemniscate integral is
  `∫₀¹ dt/√(1-t⁴) = Γ(1/4)²/(4√(2π))` (Duverney (5.10)–(5.13)).
* The perimeter of an ellipse is `4a E(e²) = 2πa F(-1/2, 1/2; 1; e²)` (Duverney (5.4), (5.6)).
-/

@[expose] public section

open Real Set Filter MeasureTheory
open scoped Topology

noncomputable section

namespace DLMF.Elliptic

/-- `sin` maps `(0, arcsin x)` onto `(0, x)` for `0 ≤ x ≤ 1`. -/
lemma sin_image_Ioo_arcsin {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    sin '' Ioo 0 (arcsin x) = Ioo 0 x := by
  have hb : arcsin x ≤ π / 2 := arcsin_le_pi_div_two x
  ext y
  constructor
  · rintro ⟨θ, ⟨h0, h1⟩, rfl⟩
    refine ⟨sin_pos_of_pos_of_lt_pi h0 (by linarith [pi_pos]), ?_⟩
    have := strictMonoOn_sin ⟨by linarith [pi_pos], by linarith⟩
      ⟨by linarith [arcsin_nonneg.mpr hx0, pi_pos], hb⟩ h1
    rwa [sin_arcsin (by linarith) hx1] at this
  · rintro ⟨h0, h1⟩
    refine ⟨arcsin y, ⟨arcsin_pos.mpr h0, ?_⟩, sin_arcsin (by linarith) (by linarith)⟩
    exact arcsin_lt_arcsin (by linarith) h1 hx1

/-- **The algebraic form of `F`** (Duverney Thm 5.9, DLMF 19.2.4 with `t = sin θ`): for
`0 ≤ x ≤ 1`, `∫₀ˣ dt/√((1-t²)(1-mt²)) = F(arcsin x|m)`. -/
theorem Real.integral_recip_sqrt_eq_incEllIntFm {m : ℝ} (hm : m < 1) {x : ℝ} (hx0 : 0 ≤ x)
    (hx1 : x ≤ 1) :
    ∫ t in (0 : ℝ)..x, 1 / Real.sqrt ((1 - t ^ 2) * (1 - m * t ^ 2)) =
      Real.incEllIntFm (arcsin x) m := by
  have hb0 : 0 ≤ arcsin x := arcsin_nonneg.mpr hx0
  have hb : arcsin x ≤ π / 2 := arcsin_le_pi_div_two x
  have hcv := integral_image_eq_integral_abs_deriv_smul (f := sin) (f' := cos)
    (measurableSet_Ioo (a := (0 : ℝ)) (b := arcsin x))
    (fun θ _ => (hasDerivAt_sin θ).hasDerivWithinAt)
    (injOn_sin.mono fun θ (hθ : θ ∈ Ioo 0 (arcsin x)) =>
      (⟨by linarith [hθ.1, pi_pos], by linarith [hθ.2]⟩ : θ ∈ Icc (-(π / 2)) (π / 2)))
    (fun t => 1 / Real.sqrt ((1 - t ^ 2) * (1 - m * t ^ 2)))
  rw [sin_image_Ioo_arcsin hx0 hx1] at hcv
  rw [intervalIntegral.integral_of_le hx0, integral_Ioc_eq_integral_Ioo, hcv, Real.incEllIntFm,
    intervalIntegral.integral_of_le hb0, integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo fun θ hθ => ?_
  have hc : 0 < cos θ := cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, pi_pos], by linarith [hθ.2]⟩
  have hp := one_sub_mul_sin_sq_pos hm θ
  simp only [smul_eq_mul]
  rw [abs_of_pos hc, show 1 - sin θ ^ 2 = cos θ ^ 2 by rw [← cos_sq_add_sin_sq θ]; ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hc.le, rpow_neg hp.le, ← Real.sqrt_eq_rpow]
  field_simp

/-- `K(m) = ∫₀¹ dt/√((1-t²)(1-mt²))` (DLMF 19.2.8, Duverney (5.8)). -/
@[dlmf 19.2.E8]
theorem Real.compEllIntKm_eq_integral_algebraic {m : ℝ} (hm : m < 1) :
    Real.compEllIntKm m = ∫ t in (0 : ℝ)..1, 1 / Real.sqrt ((1 - t ^ 2) * (1 - m * t ^ 2)) := by
  rw [Real.integral_recip_sqrt_eq_incEllIntFm hm zero_le_one le_rfl, arcsin_one,
      Real.incEllIntFm_pi_div_two]

/-- Jacobi's inverse function `arcsn(x|m) = F(arcsin x|m)` (Duverney (5.56)). -/
@[dlmf 22.15.E4]
def Real.jacobiArcsnm (x m : ℝ) : ℝ := Real.incEllIntFm (arcsin x) m

/-- `sn(arcsn x) = x` for `|x| ≤ 1`. -/
@[dlmf 22.15.E1]
theorem Real.jacobiSnm_jacobiArcsnm {m : ℝ} (hm : m < 1) {x : ℝ} (hx : -1 ≤ x) (hx1 : x ≤ 1) :
    Real.jacobiSnm (Real.jacobiArcsnm x m) m = x := by
  rw [Real.jacobiSnm, Real.jacobiArcsnm, Real.jacobiAmm_incEllIntFm hm, sin_arcsin hx hx1]

/-- `arcsn(sn u) = u` for `|u| ≤ K`. -/
theorem Real.jacobiArcsnm_jacobiSnm {m : ℝ} (hm : m < 1) {u : ℝ} (hu : |u| ≤ Real.compEllIntKm m) :
    Real.jacobiArcsnm (Real.jacobiSnm u m) m = u := by
  have hmono : StrictMono fun u => Real.jacobiAmm u m := by
    simp only [Real.jacobiAmm, hm, ↓reduceDIte]; exact (Real.incEllIntFmOrderIso hm).symm.strictMono
  have h1 : Real.jacobiAmm u m ≤ π / 2 := by
    rw [← Real.jacobiAmm_compEllIntKm hm]; exact hmono.monotone (le_of_abs_le hu)
  have h2 : -(π / 2) ≤ Real.jacobiAmm u m := by
    rw [← Real.jacobiAmm_compEllIntKm hm, ← Real.jacobiAmm_neg hm]
    exact hmono.monotone (neg_le_of_abs_le hu)
  rw [Real.jacobiArcsnm, Real.jacobiSnm, arcsin_sin h2 h1, Real.incEllIntFm_jacobiAmm hm]

/-- `d arcsn/dx = ((1-x²)(1-mx²))^{-1/2}` for `|x| < 1` (Duverney (5.57)). -/
theorem Real.hasDerivAt_jacobiArcsnm {m : ℝ} (hm : m < 1) {x : ℝ} (hx : -1 < x) (hx1 : x < 1) :
    HasDerivAt (fun x => Real.jacobiArcsnm x m)
      (1 / Real.sqrt ((1 - x ^ 2) * (1 - m * x ^ 2))) x := by
  have ha := hasDerivAt_arcsin hx.ne' hx1.ne
  have h := (Real.hasDerivAt_incEllIntFm hm (arcsin x)).comp x ha
  refine h.congr_deriv ?_
  have hp : 0 < 1 - m * x ^ 2 := by
    have := one_sub_mul_sin_sq_pos hm (arcsin x); rwa [sin_arcsin hx.le hx1.le] at this
  have hq : 0 < 1 - x ^ 2 := by nlinarith
  rw [sin_arcsin hx.le hx1.le, rpow_neg hp.le, ← Real.sqrt_eq_rpow, Real.sqrt_mul hq.le]
  field_simp

/-- `K(1/2) = Γ(1/4)²/(4√π)` (Duverney (5.38)), from Gauss's second
summation theorem and the reflection formula. -/
theorem Real.compEllIntKm_one_half :
    Real.compEllIntKm (1 / 2) = Real.Gamma (1 / 4) ^ 2 / (4 * Real.sqrt π) := by
  have hK := Real.compEllIntKm_eq_ordinaryHypergeometric (m := 1 / 2) (by norm_num [abs_of_pos])
  have hc : ∀ k : ℕ, ((1 / 2 : ℂ) + 1 / 2 + 1) / 2 ≠ -(k : ℂ) := by
    intro k h
    rw [show ((1 / 2 : ℂ) + 1 / 2 + 1) / 2 = 1 by norm_num] at h
    have := congrArg Complex.re h; simp at this; linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
  have hg := DLMF.Hypergeometric.gauss_second_summation (a := 1 / 2) (b := 1 / 2) hc
  rw [show ((1 / 2 : ℂ) + 1 / 2 + 1) / 2 = 1 by norm_num, Complex.Gamma_one,
    show ((1 / 2 : ℂ) + 1) / 2 = ((3 / 4 : ℝ) : ℂ) by push_cast; norm_num,
    Complex.Gamma_ofReal] at hg
  rw [show ((1 / 2 : ℝ) : ℂ) = 1 / 2 by push_cast; ring, hg] at hK
  have hK' : Real.compEllIntKm (1 / 2) =
      π / 2 * (Real.sqrt π * 1 / (Real.Gamma (3 / 4) * Real.Gamma (3 / 4))) := by
    exact_mod_cast hK
  have hr := Real.Gamma_mul_Gamma_one_sub (1 / 4)
  rw [show (1 : ℝ) - 1 / 4 = 3 / 4 by norm_num, show π * (1 / 4) = π / 4 by ring,
    sin_pi_div_four] at hr
  have h34 : 0 < Real.Gamma (3 / 4) := Real.Gamma_pos_of_pos (by norm_num)
  have h14 : 0 < Real.Gamma (1 / 4) := Real.Gamma_pos_of_pos (by norm_num)
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hspi : Real.sqrt π ^ 2 = π := Real.sq_sqrt pi_pos.le
  have hs0 : 0 < Real.sqrt π := Real.sqrt_pos.mpr pi_pos
  have hs20 : 0 < Real.sqrt 2 := by positivity
  rw [hK']
  have hG3 : Real.Gamma (3 / 4) = π * Real.sqrt 2 / Real.Gamma (1 / 4) := by
    field_simp at hr ⊢; nlinarith [hr]
  rw [hG3]
  field_simp
  nlinarith [hs2, hspi]

/-- **Gauss's constant** (Duverney (5.38)): `Γ(1/4)² M(1, 1/√2) = 2π^{3/2}`, from
`K(1/2) = π/(2M(1, 1/√2))`. -/
theorem Gamma_one_fourth_sq_mul_agm :
    Real.Gamma (1 / 4) ^ 2 * (NNReal.agm 1 (NNReal.sqrt (1 - 1 / 2 : ℝ).toNNReal) : ℝ) =
      2 * π * Real.sqrt π := by
  have h := Real.compEllIntKm_eq_pi_div_agm (m := 1 / 2) (by norm_num)
  rw [Real.compEllIntKm_one_half] at h
  have hM : 0 < (NNReal.agm 1 (NNReal.sqrt (1 - 1 / 2 : ℝ).toNNReal) : ℝ) := by
    exact_mod_cast NNReal.agm_pos one_pos (NNReal.sqrt_pos.mpr (by norm_num))
  have hs0 : 0 < Real.sqrt π := Real.sqrt_pos.mpr pi_pos
  rw [div_eq_div_iff (by positivity) (by positivity)] at h
  linarith [h]

/-- `E(1/2) = π^{3/2}/Γ(1/4)² + Γ(1/4)²/(8√π)` (Duverney Ex. 5.9), from Legendre's relation at
`m = 1/2`. -/
theorem Real.compEllIntEm_one_half :
    Real.compEllIntEm (1 / 2) = π * Real.sqrt π / Real.Gamma (1 / 4) ^ 2 +
      Real.Gamma (1 / 4) ^ 2 / (8 * Real.sqrt π) := by
  have hL := legendre_relation (m := 1 / 2) (by norm_num) (by norm_num)
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, Real.compEllIntKm_one_half] at hL
  have h14 : 0 < Real.Gamma (1 / 4) := Real.Gamma_pos_of_pos (by norm_num)
  have hs0 : 0 < Real.sqrt π := Real.sqrt_pos.mpr pi_pos
  have hspi : Real.sqrt π ^ 2 = π := Real.sq_sqrt pi_pos.le
  field_simp at hL ⊢
  nlinarith [hL, hspi]

/-- `K(-1) = K(1/2)/√2`, from `K = π/(2M)` and the homogeneity of the AGM. -/
theorem Real.compEllIntKm_neg_one :
    Real.compEllIntKm (-1) = Real.compEllIntKm (1 / 2) / Real.sqrt 2 := by
  rw [Real.compEllIntKm_eq_pi_div_agm (by norm_num), Real.compEllIntKm_eq_pi_div_agm (by norm_num)]
  have h2 : (NNReal.sqrt (1 - (-1) : ℝ).toNNReal) = NNReal.sqrt 2 := by norm_num
  have h12 : (NNReal.sqrt (1 - 1 / 2 : ℝ).toNNReal) = (NNReal.sqrt 2)⁻¹ := by
    rw [show (1 - 1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.toNNReal_inv]
    simp [NNReal.sqrt_inv]
  rw [h2, h12]
  have hs : (NNReal.sqrt 2) ≠ 0 := by positivity
  have hmul : NNReal.agm 1 (NNReal.sqrt 2) =
      NNReal.sqrt 2 * NNReal.agm 1 (NNReal.sqrt 2)⁻¹ := by
    rw [← NNReal.agm_mul_distrib, mul_one, mul_inv_cancel₀ hs, NNReal.agm_comm]
  rw [hmul]
  have hM : 0 < (NNReal.agm 1 (NNReal.sqrt 2)⁻¹ : ℝ) := by
    exact_mod_cast NNReal.agm_pos one_pos (by positivity)
  push_cast
  have hs2 : 0 < Real.sqrt 2 := by positivity
  field_simp

/-- **The lemniscate integral** (Duverney (5.10)–(5.13)): `∫₀¹ dt/√(1-t⁴) = Γ(1/4)²/(4√(2π))`.
The lemniscate `r² = a² cos 2θ` has length `4a` times this integral. -/
theorem integral_recip_sqrt_one_sub_pow_four :
    ∫ t in (0 : ℝ)..1, 1 / Real.sqrt (1 - t ^ 4) =
      Real.Gamma (1 / 4) ^ 2 / (4 * Real.sqrt (2 * π)) := by
  have h := Real.compEllIntKm_eq_integral_algebraic (m := -1) (by norm_num)
  have hcongr : ∫ t in (0 : ℝ)..1, 1 / Real.sqrt (1 - t ^ 4) =
      ∫ t in (0 : ℝ)..1, 1 / Real.sqrt ((1 - t ^ 2) * (1 - (-1) * t ^ 2)) :=
    intervalIntegral.integral_congr fun t _ => by
      simp only [show (1 - t ^ 2) * (1 - (-1) * t ^ 2) = 1 - t ^ 4 by ring]
  rw [hcongr, ← h, Real.compEllIntKm_neg_one, Real.compEllIntKm_one_half,
      Real.sqrt_mul (by norm_num)]
  have hs2 : 0 < Real.sqrt 2 := by positivity
  field_simp

/-- The perimeter of the ellipse `(a sin θ, b cos θ)`, `4 ∫₀^{π/2} √(a² cos²θ + b² sin²θ) dθ`. -/
def ellipsePerimeter (a b : ℝ) : ℝ :=
  4 * ∫ θ in (0 : ℝ)..(π / 2), Real.sqrt (a ^ 2 * cos θ ^ 2 + b ^ 2 * sin θ ^ 2)

/-- The perimeter of an ellipse with semi-axes `a ≥ b > 0` is `4a E(e²)`, `e² = 1 - b²/a²`
(Duverney (5.4)). -/
theorem ellipsePerimeter_eq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ellipsePerimeter a b = 4 * a * Real.compEllIntEm (1 - b ^ 2 / a ^ 2) := by
  have hcongr : ∫ θ in (0 : ℝ)..(π / 2), Real.sqrt (a ^ 2 * cos θ ^ 2 + b ^ 2 * sin θ ^ 2) =
      ∫ θ in (0 : ℝ)..(π / 2), a * (1 - (1 - b ^ 2 / a ^ 2) * sin θ ^ 2) ^ (1 / 2 : ℝ) :=
    intervalIntegral.integral_congr fun θ _ => ?_
  · rw [ellipsePerimeter, Real.compEllIntEm, hcongr, intervalIntegral.integral_const_mul]; ring
  have hpos : 0 ≤ 1 - (1 - b ^ 2 / a ^ 2) * sin θ ^ 2 := by
    have := sin_sq_le_one θ
    have hb' : 0 ≤ b ^ 2 / a ^ 2 := by positivity
    nlinarith [sq_nonneg (sin θ)]
  rw [← Real.sqrt_eq_rpow, show a * Real.sqrt (1 - (1 - b ^ 2 / a ^ 2) * sin θ ^ 2) =
      Real.sqrt (a ^ 2 * (1 - (1 - b ^ 2 / a ^ 2) * sin θ ^ 2)) by
    rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha.le]]
  congr 1
  rw [show a ^ 2 * cos θ ^ 2 = a ^ 2 * (1 - sin θ ^ 2) by rw [← cos_sq_add_sin_sq θ]; ring]
  field_simp
  ring

/-- **The perimeter of an ellipse as a ₂F₁** (Duverney (5.6)): for `0 < b ≤ a`,
`L = 2πa F(-1/2, 1/2; 1; e²)` with `e² = 1 - b²/a²`. -/
theorem ellipsePerimeter_eq_ordinaryHypergeometric {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hba : b ≤ a) :
    (ellipsePerimeter a b : ℂ) =
      2 * π * a * ₂F₁ (-(1 / 2) : ℂ) (1 / 2) 1 ((1 - b ^ 2 / a ^ 2 : ℝ) : ℂ) := by
  have he : |1 - b ^ 2 / a ^ 2| < 1 := by
    have h1 : 0 < b ^ 2 / a ^ 2 := by positivity
    have h2 : b ^ 2 / a ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith
    rw [abs_lt]; constructor <;> linarith
  rw [ellipsePerimeter_eq ha hb, Complex.ofReal_mul, Real.compEllIntEm_eq_ordinaryHypergeometric he]
  push_cast
  ring

end DLMF.Elliptic

end
