/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.EllipticIntegrals.Symmetric
public import Dirichlet.Average.TwoNode
public import Carlson.R.IntegerParameters
public import Carlson.RPolynomial.Coefficients
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import DLMFMathlib.MeasureTheory.Integral.Trigonometric
import DLMFMathlib.Analysis.Integral.DirichletThreeNode
import DLMFMathlib.MeasureTheory.Integral.IntervalSymmetry
import DLMF.EllipticIntegrals.SymmetricRCAddition
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Integral representations of the symmetric elliptic integrals (DLMF §19.23)

Trigonometric, hyperbolic, spherical-average and unit-interval representations of `R_F`,
`R_G`, `R_D` and of the general `R_{-a}(𝐛; 𝐳)`.

## Main definitions

* `CarlsonRightHalfDomain`: the domain of (19.23.6) and (19.23.6_5) (19.23.p3).
* `sphereQuadraticForm`, `directionCosines`: the quadratic form of (19.23.6) and the direction
  cosines of (19.23.9).

## Main results

* `symmetricEllipticRF_zero_eq_integral_trig`, `symmetricEllipticRG_zero_eq_integral_trig`,
  `symmetricEllipticRD_zero_eq_integral_trig`: the complete cases as integrals over `[0, π/2]` of
  powers of `y cos² θ + z sin² θ`, for `ℜ y, ℜ z > 0` (DLMF 19.23.1–19.23.3).
* `symmetricEllipticRF_zero_eq_integral_symmetricEllipticRC`,
  `symmetricEllipticRF_eq_integral_symmetricEllipticRC`: `R_F` as an average of `R_C` (DLMF 19.23.4,
  19.23.5).
* `symmetricEllipticRF_eq_sphere_integral`, `symmetricEllipticRG_eq_sphere_integral`: `R_F` and
  `R_G` as averages over the unit sphere (DLMF 19.23.6, 19.23.6_5).
* `symmetricEllipticR_two_eq_integral_trig`, `symmetricEllipticR_three_eq_integral_sphere`:
  `R_{-a}(𝐛; 𝐳)` for `n = 2` and `n = 3` (DLMF 19.23.8, 19.23.9).
* `symmetricEllipticR_eq_integral_unitInterval`: Euler's integral over `[0, 1]` for general `n`
  (DLMF 19.23.10, stronger than DLMF).

## Implementation notes

All functions are DLMF's (`DLMF.EllipticIntegrals.symmetricEllipticRF` etc.); principal powers are
used throughout, and on the stated domains every base lies in the open right half-plane, so no
branch question arises. The boundary case for the square-root sphere integral uses Mathlib’s
`Complex.continuousAt_cpow_const_of_re_pos`, continuity of compact interval integrals, and
`lean-codes`’ `Carlson.tendsto_carlsonRG_zero`. The three-node formula uses the
stick-breaking identity
`Dirichlet.regDirichletIntegral_fin_three_ofReal` and the quarter-period sine and cosine
substitutions. The two-node trigonometric formula uses `lean-codes`'
`Dirichlet.regCarlsonDirichletAverage_fin_two` and a change of variables by `cos² θ`. The Euler
integral (19.23.10) comes from `lean-codes`' unit-interval representation
`Carlson.regCarlsonR_eq_unitIntervalIntegral` (Carlson 1977, (6.8-6)).

The equation (19.23.7) was moved by DLMF to (19.16.2_5), which is the definition
`DLMF.EllipticIntegrals.symmetricEllipticRG`. The final sentence of the section (19.23.p6) is a
bibliographic pointer.

The averages (19.23.4)–(19.23.5) follow from the integral (19.2.17) of `R_C` by Fubini's theorem
and `∫₀^{π/2} (A cos² θ + B sin² θ)⁻¹ dθ = (π/2) (√A √B)⁻¹` (19.23.8 with `a = 1`); the second
form of (19.23.4) uses the substitution `θ = arctan (sinh t)`.

## References

* NIST DLMF §19.23.
* B. C. Carlson, *Special Functions of Applied Mathematics*, 1977, Exercises 5.9-19, 5.9-20 and
  (6.8-2); formalized in `lean-codes` (`Carlson.*`).
-/

@[expose] public noncomputable section

open Complex Set Filter MeasureTheory
open scoped Real Topology

namespace DLMF.EllipticIntegrals

/-- DLMF 19.23.p3: the domain of (19.23.6) and (19.23.6_5): `x, y, z` have positive real parts,
except that at most one of them may be `0`. -/
def CarlsonRightHalfDomain (x y z : ℂ) : Prop :=
  (0 < x.re ∨ x = 0) ∧ (0 < y.re ∨ y = 0) ∧ (0 < z.re ∨ z = 0) ∧
    (x = 0 → y ≠ 0 ∧ z ≠ 0) ∧ (y = 0 → z ≠ 0)

/-- DLMF 19.23.8 (`n = 2`): `R_{-a}(b₁, b₂; z₁, z₂) = 2/B(b₁, b₂) ∫₀^{π/2}
(z₁ cos² θ + z₂ sin² θ)^{-a} (cos θ)^{2b₁-1} (sin θ)^{2b₂-1} dθ`, for `b₁, b₂ > 0`,
`ℜ z₁, ℜ z₂ > 0`. The exponent `a` is any complex number (`R_{-a}` is Carlson's continuation in
`a`; both sides are entire in `a`). -/
@[dlmf 19.23.E8]
theorem symmetricEllipticR_two_eq_integral_trig (a : ℂ) {b₁ b₂ : ℝ} (hb₁ : 0 < b₁) (hb₂ : 0 < b₂)
    {z₁ z₂ : ℂ} (hz₁ : 0 < z₁.re) (hz₂ : 0 < z₂.re) :
    symmetricEllipticR a ![(b₁ : ℂ), b₂] ![z₁, z₂] = 2 / betaIntegral b₁ b₂ *
      ∫ θ in (0 : ℝ)..(π / 2), (z₁ * (Real.cos θ : ℂ) ^ 2 + z₂ * (Real.sin θ : ℂ) ^ 2) ^ (-a) *
        ((Real.cos θ ^ (2 * b₁ - 1) * Real.sin θ ^ (2 * b₂ - 1) : ℝ) : ℂ) := by
  have hzs : ![z₁, z₂] ∈ Carlson.carlsonRSlitDomain :=
    vec2_mem_carlsonRSlitDomain (Or.inl hz₁) (Or.inl hz₂)
  have hzr : ![z₁, z₂] ∈ Carlson.carlsonRVariableDomain := by
    intro i; fin_cases i <;> assumption
  have hb : ![(b₁ : ℂ), (b₂ : ℂ)] ∈ Complex.mvBetaConvergent := by
    intro i; fin_cases i <;> assumption
  rw [symmetricEllipticR_of_mem _ _ hzs, Carlson.carlsonR,
    Carlson.regCarlsonR_eq_regCarlsonRIntegral _ hb hzr, Carlson.regCarlsonRIntegral,
    Dirichlet.regCarlsonDirichletAverage_fin_two, Dirichlet.regEulerIntegral]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [MeasureTheory.integral_Ioo_eq_integral_cos_sq]
  simp_rw [Complex.real_smul]
  rw [← integral_const_mul]
  rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ π / 2 by positivity),
    integral_Ioc_eq_integral_Ioo, ← integral_const_mul]
  have hB := Complex.betaIntegral_eq_Gamma_mul_div (b₁ : ℂ) (b₂ : ℂ)
      (show 0 < (b₁ : ℂ).re by exact hb₁)
    (show 0 < (b₂ : ℂ).re by exact hb₂)
  rw [hB]
  simp_rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo fun θ hθ => ?_
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hc2 : (1 : ℂ) - (Real.cos θ ^ 2 : ℝ) = ((Real.sin θ ^ 2 : ℝ) : ℂ) := by
    push_cast
    exact_mod_cast (show (1 : ℝ) - Real.cos θ ^ 2 =
        Real.sin θ ^ 2 by nlinarith [Real.sin_sq_add_cos_sq θ])
  rw [hc2]
  have hbase : ((Real.cos θ ^ 2 : ℝ) : ℂ) * z₁ + ((Real.sin θ ^ 2 : ℝ) : ℂ) * z₂ =
      z₁ * (Real.cos θ : ℂ) ^ 2 + z₂ * (Real.sin θ : ℂ) ^ 2 := by push_cast; ring
  rw [hbase]
  have hweight : (2 * Real.sin θ * Real.cos θ : ℝ) *
      (Real.cos θ ^ 2) ^ (b₁ - 1) * (Real.sin θ ^ 2) ^ (b₂ - 1) =
      2 * (Real.cos θ ^ (2 * b₁ - 1) * Real.sin θ ^ (2 * b₂ - 1)) := by
    rw [← Real.rpow_natCast (Real.cos θ) 2, ← Real.rpow_natCast (Real.sin θ) 2,
      ← Real.rpow_mul hc.le, ← Real.rpow_mul hs.le]
    rw [show 2 * b₁ - 1 = 1 + 2 * (b₁ - 1) by ring,
      show 2 * b₂ - 1 = 1 + 2 * (b₂ - 1) by ring,
      Real.rpow_add hc, Real.rpow_add hs, Real.rpow_one, Real.rpow_one]
    ring_nf
  rw [show (b₁ : ℂ) - 1 = ((b₁ - 1 : ℝ) : ℂ) by push_cast; ring,
    show (b₂ : ℂ) - 1 = ((b₂ - 1 : ℝ) : ℂ) by push_cast; ring,
    ← ofReal_cpow (sq_nonneg _) _, ← ofReal_cpow (sq_nonneg _) _]
  have hweightC := congrArg (fun r : ℝ => (r : ℂ)) hweight
  simp only [ofReal_mul, ofReal_ofNat] at hweightC ⊢
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  linear_combination (Gamma ((b₁ : ℂ) + b₂) *
      (z₁ * (Real.cos θ : ℂ) ^ 2 + z₂ * (Real.sin θ : ℂ) ^ 2) ^ (-a) *
    (Gamma (b₁ : ℂ))⁻¹ * (Gamma (b₂ : ℂ))⁻¹) * hweightC

/-! ### Complete integrals (19.23.1)–(19.23.3) -/

/-- DLMF 19.23.1: `R_F(0, y, z) = ∫₀^{π/2} (y cos² θ + z sin² θ)^{-1/2} dθ`, for `ℜ y > 0`,
`ℜ z > 0` (19.23.p1). -/
@[dlmf 19.23.E1]
theorem symmetricEllipticRF_zero_eq_integral_trig {y z : ℂ} (hy : 0 < y.re) (hz : 0 < z.re) :
    symmetricEllipticRF 0 y z = ∫ θ in (0 : ℝ)..(π / 2),
      (y * (Real.cos θ : ℂ) ^ 2 + z * (Real.sin θ : ℂ) ^ 2) ^ (-1 / 2 : ℂ) := by
  have hB : betaIntegral (1 / 2 : ℂ) (1 / 2) = π := by
    rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ (by norm_num) (by norm_num)]
    norm_num [Gamma_one_half_mul_self]
  have H := symmetricEllipticR_two_eq_integral_trig (1 / 2) (b₁ := 1 / 2) (b₂ := 1 / 2)
    (by norm_num) (by norm_num) hy hz
  simp only [ofReal_div, ofReal_one, ofReal_ofNat,
    show 2 * (1 / 2 : ℝ) - 1 = 0 by norm_num, Real.rpow_zero,
    mul_one] at H
  rw [hB] at H
  rw [symmetricEllipticRF_zero_left (Or.inl hy) (Or.inl hz), H]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

/-- DLMF 19.23.2: `R_G(0, y, z) = (1/2) ∫₀^{π/2} (y cos² θ + z sin² θ)^{1/2} dθ`, for `ℜ y > 0`,
`ℜ z > 0` (19.23.p1). -/
@[dlmf 19.23.E2]
theorem symmetricEllipticRG_zero_eq_integral_trig {y z : ℂ} (hy : 0 < y.re) (hz : 0 < z.re) :
    symmetricEllipticRG 0 y z = (1 / 2) * ∫ θ in (0 : ℝ)..(π / 2),
      (y * (Real.cos θ : ℂ) ^ 2 + z * (Real.sin θ : ℂ) ^ 2) ^ (1 / 2 : ℂ) := by
  have hB : betaIntegral (1 / 2 : ℂ) (1 / 2) = π := by
    rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ (by norm_num) (by norm_num)]
    norm_num [Gamma_one_half_mul_self]
  have H := symmetricEllipticR_two_eq_integral_trig (-1 / 2) (b₁ := 1 / 2) (b₂ := 1 / 2)
    (by norm_num) (by norm_num) hy hz
  simp only [ofReal_div, ofReal_one, ofReal_ofNat,
    show 2 * (1 / 2 : ℝ) - 1 = 0 by norm_num, Real.rpow_zero,
    mul_one] at H
  rw [hB] at H
  rw [show -(-1 / 2 : ℂ) = 1 / 2 by ring] at H
  rw [(symmetricEllipticRG_zero_left (Or.inl hy) (Or.inl hz)).1, H]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  ring

/-- DLMF 19.23.3: `R_D(0, y, z) = 3 ∫₀^{π/2} (y cos² θ + z sin² θ)^{-3/2} sin² θ dθ`, for
`ℜ y > 0`, `ℜ z > 0` (19.23.p1). -/
@[dlmf 19.23.E3]
theorem symmetricEllipticRD_zero_eq_integral_trig {y z : ℂ} (hy : 0 < y.re) (hz : 0 < z.re) :
    symmetricEllipticRD 0 y z = 3 * ∫ θ in (0 : ℝ)..(π / 2),
      (y * (Real.cos θ : ℂ) ^ 2 + z * (Real.sin θ : ℂ) ^ 2) ^ (-3 / 2 : ℂ) *
        (Real.sin θ : ℂ) ^ 2 := by
  have hB : betaIntegral (1 / 2 : ℂ) (3 / 2) = π / 2 := by
    rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ (by norm_num) (by norm_num)]
    norm_num
    rw [Carlson.Gamma_three_halves]
    linear_combination (1 / 2 : ℂ) * Gamma_one_half_mul_self
  have H := symmetricEllipticR_two_eq_integral_trig (3 / 2) (b₁ := 1 / 2) (b₂ := 3 / 2)
    (by norm_num) (by norm_num) hy hz
  simp only [ofReal_div, ofReal_one, ofReal_ofNat,
    show 2 * (1 / 2 : ℝ) - 1 = 0 by norm_num,
    show 2 * (3 / 2 : ℝ) - 1 = 2 by norm_num, Real.rpow_zero, Real.rpow_two,
    one_mul, ofReal_pow] at H
  rw [hB] at H
  rw [symmetricEllipticRD_zero_left (Or.inl hy) (Or.inl hz), H]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  simp only [show (-3 / 2 : ℂ) = -(3 / 2) by ring]
  field_simp
  ring

/-! ### `R_F` as an average of `R_C` (19.23.4), (19.23.5) -/

/-- `∫₀^{π/2} (A cos² θ + B sin² θ)⁻¹ dθ = (π/2) (√A √B)⁻¹` for `ℜ A, ℜ B > 0`, from
(19.23.8) with `a = 1`, `b₁ = b₂ = 1/2`. -/
private lemma integral_inv_cos_sq_add_sin_sq {A B : ℂ} (hA : 0 < A.re) (hB : 0 < B.re) :
    ∫ θ in (0 : ℝ)..(π / 2), (A * (Real.cos θ : ℂ) ^ 2 + B * (Real.sin θ : ℂ) ^ 2)⁻¹ =
      (π / 2 : ℂ) * (A ^ (1 / 2 : ℂ) * B ^ (1 / 2 : ℂ))⁻¹ := by
  have hβ : betaIntegral (1 / 2 : ℂ) (1 / 2) = π := by
    rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ (by norm_num) (by norm_num)]
    norm_num [Gamma_one_half_mul_self]
  have H := symmetricEllipticR_two_eq_integral_trig 1 (b₁ := 1 / 2) (b₂ := 1 / 2)
    (by norm_num) (by norm_num) hA hB
  simp only [ofReal_div, ofReal_one, ofReal_ofNat,
    show 2 * (1 / 2 : ℝ) - 1 = 0 by norm_num, Real.rpow_zero, mul_one, ofReal_one] at H
  rw [hβ] at H
  have hz : (![A, B] : Fin 2 → ℂ) ∈ Carlson.carlsonRSlitDomain :=
    vec2_mem_carlsonRSlitDomain (Or.inl hA) (Or.inl hB)
  have hP := Carlson.regCarlsonR_neg_sum_sub_nat 0 (![1 / 2, 1 / 2] : Fin 2 → ℂ) hz
  rw [symmetricEllipticR_of_mem _ _ hz, Carlson.carlsonR] at H
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Fin.prod_univ_two, Carlson.regCarlsonRPolynomial_zero,
    Nat.cast_zero, sub_zero] at hP H
  rw [show -(1 / 2 + 1 / 2 : ℂ) = -1 by norm_num] at hP
  rw [hP] at H
  simp only [cpow_neg_one] at H
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hG : Gamma (1 / 2 + 1 / 2 : ℂ) = 1 := by norm_num
  rw [hG] at H
  simp only [cpow_neg, inv_one, mul_one, one_mul] at H
  rw [mul_inv, H]
  field_simp



/-- The real form of `integral_inv_cos_sq_add_sin_sq`. -/
private lemma integral_inv_cos_sq_add_sin_sq_real {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    ∫ θ in (0 : ℝ)..(π / 2), (A * Real.cos θ ^ 2 + B * Real.sin θ ^ 2)⁻¹ =
      π / 2 * (√A * √B)⁻¹ := by
  have H := integral_inv_cos_sq_add_sin_sq (A := A) (B := B) (by simpa using hA) (by simpa using hB)
  rw [Carlson.ofReal_cpow_half hA.le, Carlson.ofReal_cpow_half hB.le] at H
  apply ofReal_injective
  rw [intervalIntegral.integral_ofReal.symm]
  push_cast at H ⊢
  exact H

/-- The first form of (19.23.4), by Fubini's theorem and (19.23.8) with `a = 1`. -/
private lemma symmetricEllipticRF_zero_eq_integral_symmetricEllipticRC_cos {y z : ℂ} (hy : 0 < y.re)
    (hz : 0 < z.re) :
    symmetricEllipticRF 0 y z =
        (2 / π) * ∫ θ in (0 : ℝ)..(π / 2), symmetricEllipticRC y (z * (Real.cos θ : ℂ) ^ 2) := by
  set m : ℝ := z.re with hm
  set F : ℝ → ℝ → ℂ := fun θ t =>
    (((t : ℂ) + y) ^ (1 / 2 : ℂ) * ((t : ℂ) + z * (Real.cos θ : ℂ) ^ 2))⁻¹ with hF
  have hre : ∀ θ t : ℝ, ((t : ℂ) + z * (Real.cos θ : ℂ) ^ 2).re = t + m * Real.cos θ ^ 2 := by
    intro θ t; simp only [add_re, ofReal_re, ← ofReal_pow, re_mul_ofReal, hm]
  have hRC : ∀ θ, symmetricEllipticRC y (z * (Real.cos θ : ℂ) ^ 2) =
      (1 / 2) * ∫ t in Ioi (0 : ℝ), F θ t := by
    intro θ
    have hn : ¬ IsNegReal (z * (Real.cos θ : ℂ) ^ 2) := fun h => by
      have := hre θ 0; simp only [ofReal_zero, zero_add] at this
      nlinarith [h.2, sq_nonneg (Real.cos θ)]
    simp only [symmetricEllipticRC, hn, ↓reduceIte, F]
  have hys : y ∈ slitPlane := Or.inl hy
  have hy0 : IsCarlsonArgument y := Or.inl hys
  have hmeas : Measurable (Function.uncurry F) := by
    simp only [hF, Function.uncurry_def]; fun_prop
  have hprod : Integrable (Function.uncurry F)
      ((volume.restrict (Ioc (0 : ℝ) (π / 2))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    have hne : ∀ θ t : ℝ, 0 < t → (t : ℂ) + z * (Real.cos θ : ℂ) ^ 2 ≠ 0 := by
      intro θ t ht h
      have := hre θ t
      rw [h, zero_re] at this
      nlinarith [sq_nonneg (Real.cos θ)]
    have hcont : ∀ t : ℝ, 0 < t → Continuous fun θ => F θ t := by
      intro t ht
      simp only [hF, mul_inv]
      exact continuous_const.mul ((by fun_prop : Continuous fun θ : ℝ =>
        (t : ℂ) + z * (Real.cos θ : ℂ) ^ 2).inv₀ fun θ => hne θ t ht)
    set G : ℝ → ℝ → ℝ := fun θ t =>
      ‖((t : ℂ) + y) ^ (1 / 2 : ℂ)‖⁻¹ * ((t + m) * Real.cos θ ^ 2 + t * Real.sin θ ^ 2)⁻¹
      with hG
    have hFG : ∀ θ t : ℝ, 0 < t → ‖F θ t‖ ≤ G θ t := by
      intro θ t ht
      have h0 : ((t : ℂ) + y) ^ (1 / 2 : ℂ) ≠ 0 := ofReal_pos_add_cpow_half_ne_zero ht hy0
      have hpos : 0 < (t + m) * Real.cos θ ^ 2 + t * Real.sin θ ^ 2 := by
        nlinarith [Real.cos_sq_add_sin_sq θ, sq_nonneg (Real.cos θ), sq_nonneg (Real.sin θ)]
      simp only [hF, hG, norm_inv, norm_mul, mul_inv]
      refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (norm_nonneg _))
      apply inv_anti₀ hpos
      refine le_trans (le_of_eq ?_) (re_le_norm _)
      rw [hre]
      nlinarith [Real.cos_sq_add_sin_sq θ]
    have hGint : ∀ t : ℝ, 0 < t → ∫ θ in Ioc 0 (π / 2), G θ t =
        ‖((t : ℂ) + y) ^ (1 / 2 : ℂ)‖⁻¹ * (π / 2 * (√(t + m) * √t)⁻¹) := by
      intro t ht
      simp only [hG]
      rw [MeasureTheory.integral_const_mul, ← intervalIntegral.integral_of_le (by positivity),
        integral_inv_cos_sq_add_sin_sq_real (by linarith) ht]
    rw [integrable_prod_iff' hmeas.aestronglyMeasurable]
    constructor
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact ((hcont t ht).integrableOn_Icc).mono_set Ioc_subset_Icc_self
    · have hms : (m : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr hz
      have hg := (integrableOn_symmetricEllipticRF_integrand (Or.inr rfl) hys
          hms).norm.const_mul (π / 2)
      refine Integrable.mono' hg ?_ ?_
      · exact (hmeas.norm.stronglyMeasurable.integral_prod_left').aestronglyMeasurable
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht0 : 0 < t := ht
        rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
        refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_
          ((ae_restrict_mem measurableSet_Ioc).mono fun θ _ => hFG θ t ht0)).trans
          (le_of_eq ?_)
        · have hc : Continuous fun θ => G θ t := by
            simp only [hG]
            refine continuous_const.mul (Continuous.inv₀ (by fun_prop) fun θ => ?_)
            nlinarith [Real.cos_sq_add_sin_sq θ, sq_nonneg (Real.cos θ),
              sq_nonneg (Real.sin θ)]
          exact (hc.integrableOn_Icc).mono_set Ioc_subset_Icc_self
        · rw [hGint t ht0, add_zero, show (t : ℂ) + (m : ℂ) = ((t + m : ℝ) : ℂ) by push_cast; ring,
            Carlson.ofReal_cpow_half ht0.le, Carlson.ofReal_cpow_half (by linarith),
            norm_inv, norm_mul, norm_mul, norm_real, norm_real, Real.norm_of_nonneg (by positivity),
            Real.norm_of_nonneg (by positivity)]
          ring
  rw [intervalIntegral.integral_congr (g := fun θ => (1 / 2) * ∫ t in Ioi (0 : ℝ), F θ t)
    (fun θ _ => hRC θ), intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ π / 2),
    MeasureTheory.integral_const_mul, integral_integral_swap hprod]
  have hin : ∀ t ∈ Ioi (0 : ℝ), ∫ θ in Ioc 0 (π / 2), F θ t =
      (π / 2 : ℂ) * (carlsonRootProduct 0 y z t)⁻¹ := by
    intro t ht
    have ht0 : 0 < t := ht
    have hA : 0 < ((t : ℂ) + z).re := by simp only [add_re, ofReal_re]; linarith
    have hB : 0 < ((t : ℂ)).re := by simpa using ht0
    have hpt : ∀ θ, F θ t = (((t : ℂ) + y) ^ (1 / 2 : ℂ))⁻¹ *
        (((t : ℂ) + z) * (Real.cos θ : ℂ) ^ 2 + (t : ℂ) * (Real.sin θ : ℂ) ^ 2)⁻¹ := by
      intro θ
      have h1 : (Real.cos θ : ℂ) ^ 2 + (Real.sin θ : ℂ) ^ 2 = 1 := by
        exact_mod_cast Real.cos_sq_add_sin_sq θ
      simp only [hF, mul_inv]
      congr 2
      linear_combination (-(t : ℂ)) * h1
    simp_rw [hpt]
    rw [MeasureTheory.integral_const_mul, ← intervalIntegral.integral_of_le (by positivity),
      integral_inv_cos_sq_add_sin_sq hA hB, carlsonRootProduct, add_zero, mul_inv, mul_inv, mul_inv]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hin, MeasureTheory.integral_const_mul,
      symmetricEllipticRF]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp


/-- `R_C(l a, l b) = l^{-1/2} R_C(a, b)` for real `l > 0` and slit-plane `a, b`. -/
private lemma symmetricEllipticRC_mul_ofReal {l : ℝ} (hl : 0 < l) {a b : ℂ} (ha : a ∈ slitPlane)
    (hb : b ∈ slitPlane) :
    symmetricEllipticRC ((l : ℂ) * a) ((l : ℂ) * b) = (l : ℂ) ^ (-(1 / 2) : ℂ) *
        symmetricEllipticRC a b := by
  have hls : (l : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr hl
  have hmem : ∀ w : ℂ, w ∈ slitPlane → (l : ℂ) * w ∈ slitPlane := fun w hw => by
    rw [mem_slitPlane_iff_arg] at hw ⊢
    rw [arg_real_mul _ hl]
    exact ⟨hw.1, mul_ne_zero (ofReal_ne_zero.mpr hl.ne') hw.2⟩
  have harg : ∀ i, arg (l : ℂ) + arg ((![a, b] : Fin 2 → ℂ) i) ∈ Ioo (-π) π := by
    intro i
    rw [arg_ofReal_of_nonneg hl.le, zero_add]
    have hi : (![a, b] : Fin 2 → ℂ) i ∈ slitPlane := by fin_cases i <;> assumption
    exact ⟨neg_pi_lt_arg _, lt_of_le_of_ne (arg_le_pi _) (mem_slitPlane_iff_arg.mp hi).1⟩
  have H := symmetricEllipticR_mul (1 / 2) ![1 / 2, 1] (vec2_mem_carlsonRSlitDomain ha hb) hls harg
  rw [symmetricEllipticRC_eq_symmetricEllipticR (hmem a ha) (hmem b hb),
      symmetricEllipticRC_eq_symmetricEllipticR ha hb, ← H]
  congr 1
  funext i; fin_cases i <;> rfl


/-- The substitution `θ = arctan (sinh t)` (the Gudermannian) in (19.23.4). -/
private lemma integral_symmetricEllipticRC_cos_eq_integral_cosh {y z : ℂ} (hy : 0 < y.re)
    (hz : 0 < z.re) :
    ∫ θ in (0 : ℝ)..(π / 2), symmetricEllipticRC y (z * (Real.cos θ : ℂ) ^ 2) =
      ∫ t in Ioi (0 : ℝ), symmetricEllipticRC (y * (Real.cosh t : ℂ) ^ 2) z := by
  set g : ℝ → ℝ := fun t => Real.arctan (Real.sinh t) with hg
  set g' : ℝ → ℝ := fun t => (1 + Real.sinh t ^ 2)⁻¹ * Real.cosh t with hg'
  have hderiv : ∀ t ∈ Ioi (0 : ℝ), HasDerivWithinAt g (g' t) (Ioi 0) t := by
    intro t _
    have H := (Real.hasDerivAt_arctan (Real.sinh t)).comp t (Real.hasDerivAt_sinh t)
    simp only [one_div] at H
    exact H.hasDerivWithinAt
  have hinj : InjOn g (Ioi 0) := fun a _ b _ hab =>
    Real.sinh_injective (Real.arctan_injective hab)
  have himg : g '' Ioi 0 = Ioo 0 (π / 2) := by
    ext θ
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨Real.arctan_pos.mpr (Real.sinh_pos_iff.mpr ht), Real.arctan_lt_pi_div_two _⟩
    · intro hθ
      have htan : 0 < Real.tan θ := Real.tan_pos_of_pos_of_lt_pi_div_two hθ.1 hθ.2
      refine ⟨Real.arsinh (Real.tan θ), Real.arsinh_pos_iff.mpr htan, ?_⟩
      simp only [hg, Real.sinh_arsinh]
      exact Real.arctan_tan (by linarith [hθ.1, Real.pi_pos]) hθ.2
  rw [intervalIntegral.integral_of_le (by positivity), integral_Ioc_eq_integral_Ioo, ← himg,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have hch : 0 < Real.cosh t := Real.cosh_pos t
  have hc2 : 1 + Real.sinh t ^ 2 = Real.cosh t ^ 2 := by rw [Real.cosh_sq]; ring
  have hcos : Real.cos (g t) ^ 2 = (Real.cosh t ^ 2)⁻¹ := by
    simp only [hg, Real.cos_arctan, one_div, inv_pow]
    rw [Real.sq_sqrt (by positivity), hc2]
  have hgabs : |g' t| = (Real.cosh t)⁻¹ := by
    simp only [hg', hc2]
    rw [abs_of_pos (by positivity)]
    field_simp
  rw [hgabs, ← ofReal_pow, hcos]
  have hl : 0 < Real.cosh t ^ 2 := by positivity
  have hb : z * (((Real.cosh t ^ 2)⁻¹ : ℝ) : ℂ) ∈ slitPlane := by
    left; rw [re_mul_ofReal]; exact mul_pos hz (inv_pos.mpr hl)
  have H := symmetricEllipticRC_mul_ofReal hl (Or.inl hy) hb
  rw [show ((Real.cosh t ^ 2 : ℝ) : ℂ) * y = y * ((Real.cosh t : ℝ) : ℂ) ^ 2 by push_cast; ring,
    show ((Real.cosh t ^ 2 : ℝ) : ℂ) * (z * (((Real.cosh t ^ 2)⁻¹ : ℝ) : ℂ)) = z by
      rw [mul_left_comm, ← ofReal_mul, mul_inv_cancel₀ hl.ne', ofReal_one, mul_one]] at H
  rw [H, real_smul]
  congr 1
  rw [show (-(1 / 2) : ℂ) = ((-(1 / 2) : ℝ) : ℂ) by push_cast; rfl, ← ofReal_cpow hl.le]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul hch.le]
  norm_num [Real.rpow_neg_one]

/-- DLMF 19.23.4: `R_F(0, y, z) = (2/π) ∫₀^{π/2} R_C(y, z cos² θ) dθ
= (2/π) ∫₀^∞ R_C(y cosh² t, z) dt`, for `ℜ y > 0`, `ℜ z > 0` (DLMF states no domain for this
formula; the notes derive it from (19.23.5) at `x = 0`, whose hypotheses are these). The
integrand of the first integral has an integrable logarithmic singularity at `θ = π/2`. -/
@[dlmf 19.23.E4]
theorem symmetricEllipticRF_zero_eq_integral_symmetricEllipticRC {y z : ℂ} (hy : 0 < y.re)
    (hz : 0 < z.re) :
    symmetricEllipticRF 0 y z =
        (2 / π) * ∫ θ in (0 : ℝ)..(π / 2), symmetricEllipticRC y (z * (Real.cos θ : ℂ) ^ 2) ∧
      symmetricEllipticRF 0 y z =
        (2 / π) * ∫ t in Ioi (0 : ℝ), symmetricEllipticRC (y * (Real.cosh t : ℂ) ^ 2) z := by
  have h1 := symmetricEllipticRF_zero_eq_integral_symmetricEllipticRC_cos hy hz
  exact ⟨h1, h1.trans (by rw [integral_symmetricEllipticRC_cos_eq_integral_cosh hy hz])⟩

/-- DLMF 19.23.5: `R_F(x, y, z) = (2/π) ∫₀^{π/2} R_C(x, y cos² θ + z sin² θ) dθ`, for
`ℜ y > 0`, `ℜ z > 0` and `x ∈ ℂ \ (-∞, 0)` (the domain of `R_C`'s first argument). -/
@[dlmf 19.23.E5]
theorem symmetricEllipticRF_eq_integral_symmetricEllipticRC {x y z : ℂ} (hx : IsCarlsonArgument x)
    (hy : 0 < y.re)
    (hz : 0 < z.re) :
    symmetricEllipticRF x y z = (2 / π) * ∫ θ in (0 : ℝ)..(π / 2),
      symmetricEllipticRC x (y * (Real.cos θ : ℂ) ^ 2 + z * (Real.sin θ : ℂ) ^ 2) := by
  set w : ℝ → ℂ := fun θ => y * (Real.cos θ : ℂ) ^ 2 + z * (Real.sin θ : ℂ) ^ 2 with hwdef
  set m : ℝ := min y.re z.re with hm
  have hm0 : 0 < m := lt_min hy hz
  have hwre : ∀ θ, m ≤ (w θ).re := by
    intro θ
    have h1 : (w θ).re = y.re * Real.cos θ ^ 2 + z.re * Real.sin θ ^ 2 := by
      simp only [hwdef, add_re, ← ofReal_pow, re_mul_ofReal]
    rw [h1]
    nlinarith [min_le_left y.re z.re, min_le_right y.re z.re, Real.sin_sq_add_cos_sq θ,
      sq_nonneg (Real.cos θ), sq_nonneg (Real.sin θ)]
  set F : ℝ → ℝ → ℂ := fun θ t => (((t : ℂ) + x) ^ (1 / 2 : ℂ) * ((t : ℂ) + w θ))⁻¹ with hF
  have hRC : ∀ θ, symmetricEllipticRC x (w θ) = (1 / 2) * ∫ t in Ioi (0 : ℝ), F θ t := by
    intro θ
    have hn : ¬ IsNegReal (w θ) := fun h => by linarith [h.2, hwre θ]
    simp [symmetricEllipticRC, hn, F]
  have key : ∀ θ t, 0 < t → ‖F θ t‖ ≤
      ‖(((t : ℂ) + x) ^ (1 / 2 : ℂ) * ((t : ℂ) + m) ^ (1 / 2 : ℂ) *
        ((t : ℂ) + m) ^ (1 / 2 : ℂ))⁻¹‖ := by
    intro θ t ht
    rw [mul_assoc _ (((t : ℂ) + m) ^ (1 / 2 : ℂ)), cpow_half_mul_cpow_half]
    simp only [hF, norm_inv]
    have h0 : ((t : ℂ) + x) ^ (1 / 2 : ℂ) ≠ 0 := ofReal_pos_add_cpow_half_ne_zero ht hx
    have htm : ‖(t : ℂ) + m‖ = t + m := by
      rw [← ofReal_add, norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    rw [norm_mul, norm_mul]
    apply inv_anti₀ (mul_pos (norm_pos_iff.mpr h0) (by rw [htm]; linarith))
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [htm]
    refine le_trans ?_ (re_le_norm _)
    simp only [add_re, ofReal_re]
    linarith [hwre θ]
  -- integrability on the product
  have hms : ((m : ℂ)) ∈ slitPlane := ofReal_mem_slitPlane.mpr hm0
  have hg := integrableOn_symmetricEllipticRF_integrand hx hms hms
  have hprod : Integrable (Function.uncurry F)
      ((volume.restrict (Ioc (0 : ℝ) (π / 2))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    have H1 := Integrable.mul_prod
      (integrable_const (1 : ℝ) (μ := volume.restrict (Ioc (0 : ℝ) (π / 2)))) hg.norm
    refine H1.mono' ?_ ?_
    · refine Measurable.aestronglyMeasurable ?_
      simp only [hF, hwdef, Function.uncurry_def]
      fun_prop
    · rw [Measure.prod_restrict]
      filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioi)] with p hp
      rw [one_mul]
      exact key p.1 p.2 hp.2
  rw [intervalIntegral.integral_congr (g := fun θ => (1 / 2) * ∫ t in Ioi (0 : ℝ), F θ t)
    (fun θ _ => hRC θ), intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ π / 2)]
  rw [MeasureTheory.integral_const_mul, integral_integral_swap hprod]
  have hin : ∀ t ∈ Ioi (0 : ℝ), ∫ θ in Ioc 0 (π / 2), F θ t =
      (π / 2 : ℂ) * (carlsonRootProduct x y z t)⁻¹ := by
    intro t ht
    have hA : 0 < ((t : ℂ) + y).re := by simp only [add_re, ofReal_re]; linarith [ht.out]
    have hB : 0 < ((t : ℂ) + z).re := by simp only [add_re, ofReal_re]; linarith [ht.out]
    have hpt : ∀ θ, F θ t = (((t : ℂ) + x) ^ (1 / 2 : ℂ))⁻¹ *
        (((t : ℂ) + y) * (Real.cos θ : ℂ) ^ 2 + ((t : ℂ) + z) * (Real.sin θ : ℂ) ^ 2)⁻¹ := by
      intro θ
      have h1 : (Real.cos θ : ℂ) ^ 2 + (Real.sin θ : ℂ) ^ 2 = 1 := by
        exact_mod_cast Real.cos_sq_add_sin_sq θ
      simp only [hF, hwdef, mul_inv]
      congr 2
      linear_combination (-(t : ℂ)) * h1
    simp_rw [hpt]
    rw [MeasureTheory.integral_const_mul, ← intervalIntegral.integral_of_le (by positivity),
      integral_inv_cos_sq_add_sin_sq hA hB, carlsonRootProduct, mul_inv, mul_inv, mul_inv]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hin, MeasureTheory.integral_const_mul,
      symmetricEllipticRF]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp


/-- The direction cosines `(sin θ cos φ, sin θ sin φ, cos θ)` of (19.23.9). -/
def directionCosines (θ φ : ℝ) : Fin 3 → ℝ :=
  ![Real.sin θ * Real.cos φ, Real.sin θ * Real.sin φ, Real.cos θ]

open Dirichlet in
/-- The spherical Dirichlet average with the standard ordering of the direction cosines. -/
private lemma symmetricEllipticR_three_eq_integral_sphere_identity (a : ℂ)
    {b : Fin 3 → ℝ} (hb : ∀ j, 0 < b j) {z : Fin 3 → ℂ} (hz : ∀ j, 0 < (z j).re) :
    symmetricEllipticR a (fun j => (b j : ℂ)) z =
      4 * Gamma (∑ j, (b j : ℂ)) / (∏ j, Gamma (b j : ℂ)) *
        ∫ φ in (0 : ℝ)..(π / 2), ∫ θ in (0 : ℝ)..(π / 2),
          (∑ j, z j * ((directionCosines θ φ j : ℝ) : ℂ) ^ 2) ^ (-a) *
            ((∏ j, directionCosines θ φ j ^ (2 * b j - 1) : ℝ) : ℂ) *
              (Real.sin θ : ℂ) := by
  have hzs : z ∈ Carlson.carlsonRSlitDomain := fun j => Or.inl (hz j)
  have hbC : (fun j => (b j : ℂ)) ∈ mvBetaConvergent := hb
  have hg : ContinuousOn (fun u => carlsonAffineForm z u ^ (-a))
      (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) :=
    (continuous_carlsonAffineForm z).continuousOn.cpow_const
      (fun _ hu => Carlson.carlsonAffineForm_mem_slitPlane hz hu)
  rw [symmetricEllipticR_of_mem _ _ hzs, Carlson.carlsonR,
    Carlson.regCarlsonR_eq_regCarlsonRIntegral _ hbC hz, Carlson.regCarlsonRIntegral,
    regCarlsonDirichletAverage, regDirichletIntegral_fin_three_ofReal hb hg]
  simp only [regEulerIntegral]
  rw [integral_Ioo_eq_integral_cos_sq]
  simp_rw [integral_Ioo_eq_integral_sin_sq, Complex.real_smul]
  rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ π / 2 by positivity)]
  simp_rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ π / 2 by positivity),
    integral_Ioc_eq_integral_Ioo]
  simp_rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro φ hφ
  apply setIntegral_congr_fun measurableSet_Ioo
  intro θ hθ
  dsimp only
  have hφc : 0 < Real.cos φ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hφ.1, Real.pi_pos], hφ.2⟩
  have hφs : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi hφ.1 (by linarith [hφ.2, Real.pi_pos])
  have hθc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hθs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hφcs : (1 : ℂ) - (Real.cos φ ^ 2 : ℝ) = ((Real.sin φ ^ 2 : ℝ) : ℂ) := by
    push_cast
    exact_mod_cast (show (1 : ℝ) - Real.cos φ ^ 2 = Real.sin φ ^ 2 by
      nlinarith [Real.sin_sq_add_cos_sq φ])
  have hθsc : (1 : ℂ) - (Real.sin θ ^ 2 : ℝ) = ((Real.cos θ ^ 2 : ℝ) : ℂ) := by
    push_cast
    exact_mod_cast (show (1 : ℝ) - Real.sin θ ^ 2 = Real.cos θ ^ 2 by
      nlinarith [Real.sin_sq_add_cos_sq θ])
  rw [hφcs, hθsc]
  have hbase : carlsonAffineForm z
      ![Real.cos φ ^ 2 * Real.sin θ ^ 2, (1 - Real.cos φ ^ 2) * Real.sin θ ^ 2,
        1 - Real.sin θ ^ 2] =
      ∑ j, z j * ((directionCosines θ φ j : ℝ) : ℂ) ^ 2 := by
    simp only [carlsonAffineForm, Fin.sum_univ_three, directionCosines,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    simp only [ofReal_mul, ofReal_sub, ofReal_one, ofReal_pow]
    have h1 : 1 - Real.cos φ ^ 2 = Real.sin φ ^ 2 := by nlinarith [Real.sin_sq_add_cos_sq φ]
    have h2 : 1 - Real.sin θ ^ 2 = Real.cos θ ^ 2 := by nlinarith [Real.sin_sq_add_cos_sq θ]
    rw [show (1 : ℂ) - (Real.cos φ : ℂ) ^ 2 = (Real.sin φ : ℂ) ^ 2 by exact_mod_cast h1,
      show (1 : ℂ) - (Real.sin θ : ℂ) ^ 2 = (Real.cos θ : ℂ) ^ 2 by exact_mod_cast h2]
    ring
  rw [hbase]
  simp only [Fin.prod_univ_three, Fin.sum_univ_three, directionCosines,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  have hpow (x β : ℝ) (hx : 0 < x) : x * (x ^ 2) ^ (β - 1) = x ^ (2 * β - 1) := by
    rw [← Real.rpow_natCast x 2, ← Real.rpow_mul hx.le]
    rw [show 2 * β - 1 = 1 + 2 * (β - 1) by ring, Real.rpow_add hx, Real.rpow_one]
    norm_num
  have hC : Real.sin θ ^ (2 * (b 0 + b 1) - 1) =
      Real.sin θ ^ (2 * b 0 - 1) * Real.sin θ ^ (2 * b 1 - 1) * Real.sin θ := by
    rw [show 2 * (b 0 + b 1) - 1 = (2 * b 0 - 1) + (2 * b 1 - 1) + 1 by ring,
      Real.rpow_add hθs, Real.rpow_add hθs, Real.rpow_one]
  have hweight : (2 * Real.sin φ * Real.cos φ) *
      (Real.cos φ ^ 2) ^ (b 0 - 1) * (Real.sin φ ^ 2) ^ (b 1 - 1) *
      (2 * Real.sin θ * Real.cos θ) *
      (Real.sin θ ^ 2) ^ (b 0 + b 1 - 1) * (Real.cos θ ^ 2) ^ (b 2 - 1) =
      4 * ((Real.sin θ * Real.cos φ) ^ (2 * b 0 - 1) *
        (Real.sin θ * Real.sin φ) ^ (2 * b 1 - 1) *
        Real.cos θ ^ (2 * b 2 - 1)) * Real.sin θ := by
    calc
      _ = 4 * (Real.cos φ * (Real.cos φ ^ 2) ^ (b 0 - 1)) *
          (Real.sin φ * (Real.sin φ ^ 2) ^ (b 1 - 1)) *
          (Real.sin θ * (Real.sin θ ^ 2) ^ (b 0 + b 1 - 1)) *
          (Real.cos θ * (Real.cos θ ^ 2) ^ (b 2 - 1)) := by ring
      _ = _ := by
        rw [hpow _ _ hφc, hpow _ _ hφs, hpow _ _ hθs, hpow _ _ hθc, hC,
          Real.mul_rpow hθs.le hφc.le, Real.mul_rpow hθs.le hφs.le]
        ring
  rw [show (b 0 : ℂ) - 1 = ((b 0 - 1 : ℝ) : ℂ) by push_cast; ring,
    show (b 1 : ℂ) - 1 = ((b 1 - 1 : ℝ) : ℂ) by push_cast; ring,
    show (b 0 : ℂ) + b 1 - 1 = ((b 0 + b 1 - 1 : ℝ) : ℂ) by push_cast; ring,
    show (b 2 : ℂ) - 1 = ((b 2 - 1 : ℝ) : ℂ) by push_cast; ring,
    ← ofReal_cpow (sq_nonneg _) _, ← ofReal_cpow (sq_nonneg _) _,
    ← ofReal_cpow (sq_nonneg _) _, ← ofReal_cpow (sq_nonneg _) _]
  have hw := congrArg (fun x : ℝ => (x : ℂ)) hweight
  simp only [ofReal_mul, ofReal_ofNat] at hw ⊢
  have hG0 := Gamma_ne_zero_of_re_pos (show 0 < (b 0 : ℂ).re from hb 0)
  have hG1 := Gamma_ne_zero_of_re_pos (show 0 < (b 1 : ℂ).re from hb 1)
  have hG2 := Gamma_ne_zero_of_re_pos (show 0 < (b 2 : ℂ).re from hb 2)
  have hG01 := Gamma_ne_zero_of_re_pos (show 0 < ((b 0 : ℂ) + b 1).re from add_pos (hb 0) (hb 1))
  set Q : ℂ := (z 0 * ((Real.sin θ : ℂ) * Real.cos φ) ^ 2 +
    z 1 * ((Real.sin θ : ℂ) * Real.sin φ) ^ 2 + z 2 * (Real.cos θ : ℂ) ^ 2) ^ (-a)
  field_simp [hG0, hG1, hG2, hG01]
  simp only [mul_comm (Real.sin θ) (Real.cos φ), mul_comm (Real.sin θ) (Real.sin φ),
    mul_comm (2 : ℝ) (b 0), mul_comm (2 : ℝ) (b 1), mul_comm (2 : ℝ) (b 2)] at hw
  linear_combination Gamma ((b 0 : ℂ) + b 1 + b 2) * Q * hw

/-! ### Averages over the sphere (19.23.6), (19.23.6_5) -/

/-- The quadratic form `x sin² θ cos² φ + y sin² θ sin² φ + z cos² θ` of (19.23.6). -/
def sphereQuadraticForm (x y z : ℂ) (θ φ : ℝ) : ℂ :=
  x * (Real.sin θ : ℂ) ^ 2 * (Real.cos φ : ℂ) ^ 2 + y * (Real.sin θ : ℂ) ^ 2 *
      (Real.sin φ : ℂ) ^ 2 +
    z * (Real.cos θ : ℂ) ^ 2

/-- Reflection symmetry folds the sphere integral into the two quarter periods.
No integrability hypothesis is needed for the totalized integrals. -/
theorem sphere_integral_eq_eight_mul_quarter (f : ℂ → ℂ) (x y z : ℂ) :
    (∫ φ in (0 : ℝ)..(2 * π), ∫ θ in (0 : ℝ)..π,
      f (sphereQuadraticForm x y z θ φ) * (Real.sin θ : ℂ)) =
    8 * ∫ φ in (0 : ℝ)..(π / 2), ∫ θ in (0 : ℝ)..(π / 2),
      f (sphereQuadraticForm x y z θ φ) * (Real.sin θ : ℂ) := by
  have htwo : 2 * (π / 2) = (π : ℝ) := by ring
  have hθ (φ : ℝ) : (∫ θ in (0 : ℝ)..π,
      f (sphereQuadraticForm x y z θ φ) * (Real.sin θ : ℂ)) =
      2 * ∫ θ in (0 : ℝ)..(π / 2),
      f (sphereQuadraticForm x y z θ φ) * (Real.sin θ : ℂ) := by
    have h := intervalIntegral.integral_eq_two_smul_of_reflection
      (fun θ => f (sphereQuadraticForm x y z θ φ) * (Real.sin θ : ℂ))
      (T := π / 2) (by positivity) (fun θ => ?_)
    · simpa only [htwo, Complex.real_smul,
        ofReal_ofNat] using h
    · rw [show 2 * (π / 2) - θ = π - θ by ring]
      simp only [sphereQuadraticForm, Real.sin_pi_sub, Real.cos_pi_sub, ofReal_neg, neg_sq]
  let g : ℝ → ℂ := fun φ => ∫ θ in (0 : ℝ)..π,
    f (sphereQuadraticForm x y z θ φ) * (Real.sin θ : ℂ)
  have hg₁ : ∀ φ, g (2 * π - φ) = g φ := by
    intro φ
    dsimp only [g]
    apply intervalIntegral.integral_congr
    intro θ _
    simp only [sphereQuadraticForm, Real.sin_two_pi_sub, Real.cos_two_pi_sub,
      ofReal_neg, neg_sq]
  have hg₂ : ∀ φ, g (2 * (π / 2) - φ) = g φ := by
    intro φ
    rw [show 2 * (π / 2) - φ = π - φ by ring]
    dsimp only [g]
    apply intervalIntegral.integral_congr
    intro θ _
    simp only [sphereQuadraticForm, Real.sin_pi_sub, Real.cos_pi_sub, ofReal_neg, neg_sq]
  have h₁ := intervalIntegral.integral_eq_two_smul_of_reflection g
    (T := π) Real.pi_pos.le hg₁
  have h₂ := intervalIntegral.integral_eq_two_smul_of_reflection g
    (T := π / 2) (by positivity) hg₂
  simp only [Complex.real_smul, ofReal_ofNat,
    htwo] at h₁ h₂
  rw [h₁, h₂]
  simp only [g]
  simp_rw [hθ]
  rw [intervalIntegral.integral_const_mul]
  ring

/-- The spherical average for three equal Dirichlet parameters `1/2`, with positive real
parts of the nodes and an arbitrary complex exponent. -/
theorem symmetricEllipticR_three_half_eq_sphere_integral (a : ℂ)
    {x y z : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) (hz : 0 < z.re) :
    symmetricEllipticR a (fun _ : Fin 3 => 1 / 2) ![x, y, z] =
      (1 / (4 * π)) * ∫ φ in (0 : ℝ)..(2 * π), ∫ θ in (0 : ℝ)..π,
        sphereQuadraticForm x y z θ φ ^ (-a) * (Real.sin θ : ℂ) := by
  have hb : ∀ _ : Fin 3, (0 : ℝ) < (1 / 2) := fun _ => by norm_num
  have hpos : ∀ i : Fin 3, 0 < (![x, y, z] i).re := by
    intro i; fin_cases i <;> assumption
  have h := symmetricEllipticR_three_eq_integral_sphere_identity a hb hpos
  simp only [show (fun _ : Fin 3 => ((1 / 2 : ℝ) : ℂ)) = fun _ => 1 / 2 by ext; push_cast; rfl,
    show (2 : ℝ) * (1 / 2) - 1 = 0 by norm_num, Real.rpow_zero, Fin.prod_univ_three,
    mul_one, Fin.sum_univ_three] at h
  norm_num only at h
  simp only [ofReal_div, ofReal_one, ofReal_ofNat, mul_one] at h
  have hc : 4 * Gamma (3 / 2 : ℂ) /
      (Gamma (1 / 2 : ℂ) * Gamma (1 / 2) * Gamma (1 / 2)) = 2 / π := by
    rw [Carlson.Gamma_three_halves]
    calc
      _ = 2 / (Gamma (1 / 2 : ℂ) * Gamma (1 / 2)) := by
        field_simp [Gamma_one_half_ne_zero]
        ring
      _ = _ := by rw [Gamma_one_half_mul_self]
  have hbase (θ φ : ℝ) : ∑ j, (![x, y, z] j) * ((directionCosines θ φ j : ℝ) : ℂ) ^ 2 =
      sphereQuadraticForm x y z θ φ := by
    simp only [Fin.sum_univ_three, directionCosines, sphereQuadraticForm,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, ofReal_mul]
    ring
  simp only [Fin.sum_univ_three] at hbase
  simp_rw [hbase] at h
  rw [hc] at h
  rw [h, sphere_integral_eq_eight_mul_quarter (fun w : ℂ => w ^ (-a)) x y z]
  field_simp
  ring

/-- The polar-angle integral is a degenerate elliptic integral when both nodes have
positive real parts. -/
private lemma integral_sin_div_sqrt_quarter_eq_symmetricEllipticRC_of_pos {A z : ℂ}
    (hA : 0 < A.re) (hz : 0 < z.re) :
    (∫ θ in (0 : ℝ)..(π / 2), (Real.sin θ : ℂ) /
      (A * (Real.sin θ : ℂ) ^ 2 + z * (Real.cos θ : ℂ) ^ 2) ^ (1 / 2 : ℂ)) =
      symmetricEllipticRC z A := by
  have h := symmetricEllipticR_two_eq_integral_trig (1 / 2)
    (b₁ := 1 / 2) (b₂ := 1) (by norm_num) (by norm_num) hz hA
  simp only [ofReal_div, ofReal_one, ofReal_ofNat] at h
  rw [← symmetricEllipticRC_eq_symmetricEllipticR (Or.inl hz) (Or.inl hA)] at h
  have hB : betaIntegral (1 / 2 : ℂ) 1 = 2 := by
    rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ (by norm_num) (by norm_num),
      show (1 / 2 : ℂ) + 1 = 3 / 2 by norm_num, Carlson.Gamma_three_halves]
    norm_num only [Gamma_one, mul_one]
    field_simp [Gamma_one_half_ne_zero]
    rw [div_self Gamma_one_half_ne_zero]
  rw [hB] at h
  norm_num only [show (2 : ℝ) * (1 / 2) - 1 = 0 by norm_num,
    show (2 : ℝ) * 1 - 1 = 1 by norm_num, Real.rpow_zero, Real.rpow_one,
    one_mul, Complex.ofReal_one, div_self (by norm_num : (2 : ℂ) ≠ 0)] at h
  rw [h]
  apply intervalIntegral.integral_congr
  intro θ _
  dsimp only
  rw [add_comm (A * (Real.sin θ : ℂ) ^ 2), div_eq_mul_inv,
    inv_cpow_half_eq_cpow_neg_half]
  ring_nf

/-- The polar-angle integral with a zero axial node is a degenerate elliptic integral. -/
private lemma integral_sin_div_sqrt_quarter_eq_symmetricEllipticRC_zero {A : ℂ}
    (hA : 0 < A.re) :
    (∫ θ in (0 : ℝ)..(π / 2), (Real.sin θ : ℂ) /
      (A * (Real.sin θ : ℂ) ^ 2) ^ (1 / 2 : ℂ)) =
      symmetricEllipticRC 0 A := by
  have hroot : A ^ (1 / 2 : ℂ) ≠ 0 :=
    cpow_ne_zero_iff.mpr (Or.inl (slitPlane_ne_zero (Or.inl hA)))
  apply mul_left_cancel₀ hroot
  rw [sqrt_mul_symmetricEllipticRC_zero (Or.inl hA)]
  rw [← intervalIntegral.integral_const_mul]
  have hI : (∫ θ in (0 : ℝ)..(π / 2), A ^ (1 / 2 : ℂ) *
      ((Real.sin θ : ℂ) / (A * (Real.sin θ : ℂ) ^ 2) ^ (1 / 2 : ℂ))) =
      ∫ _θ in (0 : ℝ)..(π / 2), (1 : ℂ) := by
    simp only [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ π / 2 by positivity),
      integral_Ioc_eq_integral_Ioo]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro θ hθ
    dsimp only
    have hs : 0 < Real.sin θ :=
      Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
    rw [mul_comm A ((Real.sin θ : ℂ) ^ 2), ← ofReal_pow,
      TauCeti.ofReal_mul_cpow (sq_nonneg _) A (1 / 2), ofReal_pow,
      TauCeti.ofReal_pow_cpow hs.le]
    norm_num only [show (2 : ℂ) * (1 / 2) = 1 by norm_num, cpow_one]
    field_simp [hroot, ofReal_ne_zero.mpr hs.ne']
    rw [div_self (ofReal_ne_zero.mpr hs.ne')]
  rw [hI]
  simp

/-- The quarter-period average of `R_C`, allowing one vanishing node. -/
theorem integral_symmetricEllipticRC_quarter_eq_symmetricEllipticRF
    {x y z : ℂ} (h : CarlsonRightHalfDomain x y z) :
    (∫ φ in (0 : ℝ)..(π / 2),
      symmetricEllipticRC z (x * (Real.cos φ : ℂ) ^ 2 + y * (Real.sin φ : ℂ) ^ 2)) =
      (π / 2 : ℂ) * symmetricEllipticRF x y z := by
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  by_cases hx : x = 0
  · subst x
    have hy : 0 < y.re := h.2.1.resolve_right (h.2.2.2.1 rfl).1
    have hz : 0 < z.re := h.2.2.1.resolve_right (h.2.2.2.1 rfl).2
    simp only [zero_mul, zero_add]
    have hi := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := π / 2)
      (fun φ => symmetricEllipticRC z (y * (Real.cos φ : ℂ) ^ 2)) (π / 2)
    simp only [sub_self, sub_zero, Real.cos_pi_div_two_sub] at hi
    rw [hi]
    have havg := (symmetricEllipticRF_zero_eq_integral_symmetricEllipticRC hz hy).1
    rw [symmetricEllipticRF_comm_right 0 y z] at havg
    field_simp [hπ] at havg ⊢
    linear_combination -havg
  · have hxpos := h.1.resolve_right hx
    by_cases hy : y = 0
    · subst y
      have hzpos := h.2.2.1.resolve_right (h.2.2.2.2 rfl)
      simp only [zero_mul, add_zero]
      have havg := (symmetricEllipticRF_zero_eq_integral_symmetricEllipticRC hzpos hxpos).1
      rw [← symmetricEllipticRF_comm_left x 0 z, ← symmetricEllipticRF_comm_right 0 x z]
      field_simp [hπ] at havg ⊢
      linear_combination -havg
    · have hypos := h.2.1.resolve_right hy
      have hzarg : IsCarlsonArgument z := h.2.2.1.imp (fun hz => Or.inl hz) id
      have havg := symmetricEllipticRF_eq_integral_symmetricEllipticRC hzarg hxpos hypos
      rw [symmetricEllipticRF_comm_left x z y, symmetricEllipticRF_comm_right x y z] at havg
      field_simp [hπ] at havg ⊢
      linear_combination -havg


/-- DLMF 19.23.6: `4π R_F(x, y, z) = ∫₀^{2π} ∫₀^π sin θ dθ dφ /
(x sin² θ cos² φ + y sin² θ sin² φ + z cos² θ)^{1/2}`, for `x, y, z` with positive real parts,
at most one of them `0` (19.23.p3). -/
@[dlmf 19.23.E6]
theorem symmetricEllipticRF_eq_sphere_integral {x y z : ℂ} (h : CarlsonRightHalfDomain x y z) :
    4 * π * symmetricEllipticRF x y z = ∫ φ in (0 : ℝ)..(2 * π), ∫ θ in (0 : ℝ)..π,
      (Real.sin θ : ℂ) / sphereQuadraticForm x y z θ φ ^ (1 / 2 : ℂ) := by
  have hquarter (φ : ℝ) (hφ : φ ∈ Ioo (0 : ℝ) (π / 2)) :
      (∫ θ in (0 : ℝ)..(π / 2), sphereQuadraticForm x y z θ φ ^ (-1 / 2 : ℂ) *
        (Real.sin θ : ℂ)) =
      symmetricEllipticRC z (x * (Real.cos φ : ℂ) ^ 2 + y * (Real.sin φ : ℂ) ^ 2) := by
    let A := x * (Real.cos φ : ℂ) ^ 2 + y * (Real.sin φ : ℂ) ^ 2
    have hc : 0 < Real.cos φ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hφ.1, Real.pi_pos], hφ.2⟩
    have hs : 0 < Real.sin φ :=
      Real.sin_pos_of_pos_of_lt_pi hφ.1 (by linarith [hφ.2, Real.pi_pos])
    have hA : 0 < A.re := by
      have hre : A.re = x.re * Real.cos φ ^ 2 + y.re * Real.sin φ ^ 2 := by
        simp only [A, add_re, ← ofReal_pow, re_mul_ofReal]
      rw [hre]
      rcases h.1 with hx | hx
      · have hyn : 0 ≤ y.re := h.2.1.elim le_of_lt (fun hy => by simp [hy])
        exact add_pos_of_pos_of_nonneg (mul_pos hx (sq_pos_of_pos hc))
          (mul_nonneg hyn (sq_nonneg _))
      · have hy : 0 < y.re := h.2.1.resolve_right (h.2.2.2.1 hx).1
        simp only [hx, zero_re, zero_mul, zero_add]
        exact mul_pos hy (sq_pos_of_pos hs)
    have hb (θ : ℝ) : sphereQuadraticForm x y z θ φ =
        A * (Real.sin θ : ℂ) ^ 2 + z * (Real.cos θ : ℂ) ^ 2 := by
      dsimp only [sphereQuadraticForm, A]
      ring
    have hconv : (∫ θ in (0 : ℝ)..(π / 2), sphereQuadraticForm x y z θ φ ^ (-1 / 2 : ℂ) *
        (Real.sin θ : ℂ)) = ∫ θ in (0 : ℝ)..(π / 2), (Real.sin θ : ℂ) /
          (A * (Real.sin θ : ℂ) ^ 2 + z * (Real.cos θ : ℂ) ^ 2) ^ (1 / 2 : ℂ) := by
      apply intervalIntegral.integral_congr
      intro θ _
      dsimp only
      rw [hb, div_eq_mul_inv (Real.sin θ : ℂ) _, inv_cpow_half_eq_cpow_neg_half]
      ring
    rw [hconv]
    rcases h.2.2.1 with hz | hz
    · exact integral_sin_div_sqrt_quarter_eq_symmetricEllipticRC_of_pos hA hz
    · subst z
      simp only [zero_mul, add_zero]
      exact integral_sin_div_sqrt_quarter_eq_symmetricEllipticRC_zero hA
  have hI : (∫ φ in (0 : ℝ)..(π / 2), ∫ θ in (0 : ℝ)..(π / 2),
      sphereQuadraticForm x y z θ φ ^ (-1 / 2 : ℂ) * (Real.sin θ : ℂ)) =
      ∫ φ in (0 : ℝ)..(π / 2),
        symmetricEllipticRC z (x * (Real.cos φ : ℂ) ^ 2 + y * (Real.sin φ : ℂ) ^ 2) :=
    intervalIntegral.integral_congr_Ioo_of_le (by positivity) hquarter
  symm
  calc
    _ = ∫ φ in (0 : ℝ)..(2 * π), ∫ θ in (0 : ℝ)..π,
        sphereQuadraticForm x y z θ φ ^ (-1 / 2 : ℂ) * (Real.sin θ : ℂ) := by
      apply intervalIntegral.integral_congr
      intro φ _
      apply intervalIntegral.integral_congr
      intro θ _
      dsimp only
      rw [div_eq_mul_inv, inv_cpow_half_eq_cpow_neg_half]
      ring
    _ = 8 * ∫ φ in (0 : ℝ)..(π / 2), ∫ θ in (0 : ℝ)..(π / 2),
        sphereQuadraticForm x y z θ φ ^ (-1 / 2 : ℂ) * (Real.sin θ : ℂ) :=
      sphere_integral_eq_eight_mul_quarter (fun w => w ^ (-1 / 2 : ℂ)) x y z
    _ = _ := by rw [hI, integral_symmetricEllipticRC_quarter_eq_symmetricEllipticRF h]; ring

/-- The principal square-root sphere integral is continuous on triples in the closed
right half-plane, including vanishing nodes. -/
theorem continuous_sphere_sqrt_integral :
    Continuous (fun v : {w : Fin 3 → ℂ // ∀ j, 0 ≤ (w j).re} =>
      ∫ φ in (0 : ℝ)..(2 * π), ∫ θ in (0 : ℝ)..π,
        sphereQuadraticForm (v.1 0) (v.1 1) (v.1 2) θ φ ^ (1 / 2 : ℂ) *
          (Real.sin θ : ℂ)) := by
  let F : ({w : Fin 3 → ℂ // ∀ j, 0 ≤ (w j).re} × ℝ) → ℝ → ℂ := fun p θ =>
    sphereQuadraticForm (p.1.1 0) (p.1.1 1) (p.1.1 2) θ p.2 ^ (1 / 2 : ℂ) *
      (Real.sin θ : ℂ)
  have hQ : Continuous (fun p : ({w : Fin 3 → ℂ // ∀ j, 0 ≤ (w j).re} × ℝ) × ℝ =>
      sphereQuadraticForm (p.1.1.1 0) (p.1.1.1 1) (p.1.1.1 2) p.2 p.1.2) := by
    have hc (j : Fin 3) : Continuous (fun p :
        ({w : Fin 3 → ℂ // ∀ j, 0 ≤ (w j).re} × ℝ) × ℝ => p.1.1.1 j) :=
      (continuous_apply j).comp
        (continuous_subtype_val.comp (continuous_fst.comp continuous_fst))
    unfold sphereQuadraticForm
    fun_prop
  have hn (p : ({w : Fin 3 → ℂ // ∀ j, 0 ≤ (w j).re} × ℝ) × ℝ) :
      0 ≤ (sphereQuadraticForm (p.1.1.1 0) (p.1.1.1 1) (p.1.1.1 2) p.2 p.1.2).re := by
    simp only [sphereQuadraticForm, add_re, ← ofReal_pow, re_mul_ofReal]
    exact add_nonneg (add_nonneg
      (mul_nonneg (mul_nonneg (p.1.1.2 0) (sq_nonneg _)) (sq_nonneg _))
      (mul_nonneg (mul_nonneg (p.1.1.2 1) (sq_nonneg _)) (sq_nonneg _)))
      (mul_nonneg (p.1.1.2 2) (sq_nonneg _))
  have hr : Continuous (fun p :
      ({w : Fin 3 → ℂ // ∀ j, 0 ≤ (w j).re} × ℝ) × ℝ =>
      sphereQuadraticForm (p.1.1.1 0) (p.1.1.1 1) (p.1.1.1 2) p.2 p.1.2 ^ (1 / 2 : ℂ)) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    exact Filter.Tendsto.comp
      (continuousAt_cpow_const_of_re_pos (Or.inl (hn p))
        (by norm_num : (0 : ℝ) < (1 / 2 : ℂ).re)) (hQ.tendsto p)
  have hf : Continuous F.uncurry :=
    hr.mul (by fun_prop)
  have hinner := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := volume) hf
    (0 : ℝ) π
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume)
    (f := fun v : {w : Fin 3 → ℂ // ∀ j, 0 ≤ (w j).re} => fun φ =>
      ∫ θ in (0 : ℝ)..π, F (v, φ) θ) hinner (0 : ℝ) (2 * π)
/-- The sphere average for `R_G` when all node real parts are positive. -/
private lemma symmetricEllipticRG_eq_sphere_integral_of_pos {x y z : ℂ}
    (hx : 0 < x.re) (hy : 0 < y.re) (hz : 0 < z.re) :
    symmetricEllipticRG x y z = (1 / (4 * π)) * ∫ φ in (0 : ℝ)..(2 * π),
      ∫ θ in (0 : ℝ)..π, sphereQuadraticForm x y z θ φ ^ (1 / 2 : ℂ) *
        (Real.sin θ : ℂ) := by
  rw [symmetricEllipticRG_eq_symmetricEllipticR (Or.inl hx) (Or.inl hy) (Or.inl hz)]
  simpa only [neg_div, neg_neg] using
    symmetricEllipticR_three_half_eq_sphere_integral (-1 / 2) hx hy hz

/-- The third node can tend to zero from the right half-plane. -/
private lemma tendsto_symmetricEllipticRG_zero {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) :
    Tendsto (fun z => symmetricEllipticRG x y z) (𝓝[{z : ℂ | 0 < z.re}] 0)
      (𝓝 (symmetricEllipticRG x y 0)) := by
  have h0 : symmetricEllipticRG x y 0 = (π / 4 : ℂ) * Carlson.carlsonRE x y := by
    rw [← symmetricEllipticRG_comm_right x y 0, symmetricEllipticRG_comm_left 0 x y,
      (symmetricEllipticRG_zero_left (Or.inl hx) (Or.inl hy)).1,
      symmetricEllipticR_of_mem _ _ (vec2_mem_carlsonRSlitDomain (Or.inl hx) (Or.inl hy))]
    unfold Carlson.carlsonRE Carlson.TwoVariable.pair
    norm_num
  rw [h0]
  apply (Carlson.tendsto_carlsonRG_zero hx hy).congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (symmetricEllipticRG_eq_carlsonRG (Or.inl hx) (Or.inl hy) (Or.inl hz)).symm

/-- A convergent path of positive nodes extends the sphere average to its endpoint. -/
private lemma symmetricEllipticRG_eq_sphere_integral_of_path
    {v : ℝ → Fin 3 → ℂ} (hv : Continuous v) (hn : ∀ t j, 0 ≤ (v t j).re)
    (hp : ∀ t : ℝ, 0 < t → ∀ j, 0 < (v t j).re)
    (hlim : Tendsto (fun t => symmetricEllipticRG (v t 0) (v t 1) (v t 2))
      (𝓝[>] (0 : ℝ)) (𝓝 (symmetricEllipticRG (v 0 0) (v 0 1) (v 0 2)))) :
    symmetricEllipticRG (v 0 0) (v 0 1) (v 0 2) =
      (1 / (4 * π)) * ∫ φ in (0 : ℝ)..(2 * π), ∫ θ in (0 : ℝ)..π,
        sphereQuadraticForm (v 0 0) (v 0 1) (v 0 2) θ φ ^ (1 / 2 : ℂ) *
          (Real.sin θ : ℂ) := by
  let w : ℝ → {u : Fin 3 → ℂ // ∀ j, 0 ≤ (u j).re} := fun t => ⟨v t, hn t⟩
  have hw : Continuous w := hv.subtype_mk _
  have hc := (continuous_sphere_sqrt_integral.comp hw).const_mul (1 / (4 * π) : ℂ)
  have ht := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  apply tendsto_nhds_unique hlim
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (symmetricEllipticRG_eq_sphere_integral_of_pos (hp t ht 0) (hp t ht 1) (hp t ht 2)).symm


/-- DLMF 19.23.6_5 (formerly 19.16.3): `R_G(x, y, z) = (1/(4π)) ∫₀^{2π} ∫₀^π
(x sin² θ cos² φ + y sin² θ sin² φ + z cos² θ)^{1/2} sin θ dθ dφ`, for `x, y, z` with positive
real parts, at most one of them `0` (19.23.p3). -/
@[dlmf 19.23.E6_5]
theorem symmetricEllipticRG_eq_sphere_integral {x y z : ℂ} (h : CarlsonRightHalfDomain x y z) :
    symmetricEllipticRG x y z = (1 / (4 * π)) * ∫ φ in (0 : ℝ)..(2 * π), ∫ θ in (0 : ℝ)..π,
      sphereQuadraticForm x y z θ φ ^ (1 / 2 : ℂ) * (Real.sin θ : ℂ) := by
  have hsq : Tendsto (fun t : ℝ => ((t ^ 2 : ℝ) : ℂ)) (𝓝[>] (0 : ℝ))
      (𝓝[{w : ℂ | 0 < w.re}] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hc : Continuous (fun t : ℝ => ((t ^ 2 : ℝ) : ℂ)) := by fun_prop
      simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), ofReal_zero] using
        (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact sq_pos_of_pos ht
  rcases h with ⟨hx, hy, hz, hxy, hyz⟩
  by_cases hx0 : x = 0
  · subst x
    have hypos := hy.resolve_right (hxy rfl).1
    have hzpos := hz.resolve_right (hxy rfl).2
    have H := symmetricEllipticRG_eq_sphere_integral_of_path
      (v := fun t => ![((t ^ 2 : ℝ) : ℂ), y, z]) (by fun_prop)
      (fun t j => by fin_cases j; exact sq_nonneg t; exact hypos.le; exact hzpos.le)
      (fun t ht j => by fin_cases j; exact sq_pos_of_pos ht; exact hypos; exact hzpos) ?_
    · simpa only [Function.comp_def, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, zero_pow (by decide : (2 : ℕ) ≠ 0), ofReal_zero] using H
    · have hl := (tendsto_symmetricEllipticRG_zero hypos hzpos).comp hsq
      simpa only [Function.comp_def, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, zero_pow (by decide : (2 : ℕ) ≠ 0), ofReal_zero,
        symmetricEllipticRG_comm_left, symmetricEllipticRG_comm_right] using hl
  · have hxpos := hx.resolve_right hx0
    by_cases hy0 : y = 0
    · subst y
      have hzpos := hz.resolve_right (hyz rfl)
      have H := symmetricEllipticRG_eq_sphere_integral_of_path
        (v := fun t => ![x, ((t ^ 2 : ℝ) : ℂ), z]) (by fun_prop)
        (fun t j => by fin_cases j; exact hxpos.le; exact sq_nonneg t; exact hzpos.le)
        (fun t ht j => by fin_cases j; exact hxpos; exact sq_pos_of_pos ht; exact hzpos) ?_
      · simpa only [Function.comp_def, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons, zero_pow (by decide : (2 : ℕ) ≠ 0), ofReal_zero]
            using H
      · have hl := (tendsto_symmetricEllipticRG_zero hxpos hzpos).comp hsq
        simpa only [Function.comp_def, Matrix.cons_val_zero, Matrix.cons_val_one,
            Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons, zero_pow (by decide : (2 : ℕ) ≠ 0), ofReal_zero,
          symmetricEllipticRG_comm_right] using hl
    · have hypos := hy.resolve_right hy0
      rcases hz with hz | rfl
      · exact symmetricEllipticRG_eq_sphere_integral_of_pos hxpos hypos hz
      · have H := symmetricEllipticRG_eq_sphere_integral_of_path
          (v := fun t => ![x, y, ((t ^ 2 : ℝ) : ℂ)]) (by fun_prop)
          (fun t j => by fin_cases j; exact hxpos.le; exact hypos.le; exact sq_nonneg t)
          (fun t ht j => by fin_cases j; exact hxpos; exact hypos; exact sq_pos_of_pos ht) ?_
        · simpa only [Function.comp_def, Matrix.cons_val_zero, Matrix.cons_val_one,
            Matrix.cons_val_two,
            Matrix.head_cons, Matrix.tail_cons, zero_pow (by decide : (2 : ℕ) ≠ 0), ofReal_zero]
              using H
        · have hl := (tendsto_symmetricEllipticRG_zero hxpos hypos).comp hsq
          simpa only [Function.comp_def, Matrix.cons_val_zero, Matrix.cons_val_one,
              Matrix.cons_val_two,
            Matrix.head_cons, Matrix.tail_cons, zero_pow (by decide : (2 : ℕ) ≠ 0), ofReal_zero]
              using hl

/-- DLMF 19.23.9 (`n = 3`): with `l₁, l₂, l₃` any permutation `σ` of
`sin θ cos φ, sin θ sin φ, cos θ`,
`R_{-a}(𝐛; 𝐳) = 4 Γ(b₁ + b₂ + b₃)/(Γ(b₁) Γ(b₂) Γ(b₃)) ∫₀^{π/2} ∫₀^{π/2}
(∑ⱼ zⱼ lⱼ²)^{-a} ∏ⱼ lⱼ^{2bⱼ-1} sin θ dθ dφ`, for `bⱼ > 0`, `ℜ zⱼ > 0`; `a` any complex
number. -/
@[dlmf 19.23.E9]
theorem symmetricEllipticR_three_eq_integral_sphere (a : ℂ) {b : Fin 3 → ℝ} (hb : ∀ j, 0 < b j)
    {z : Fin 3 → ℂ} (hz : ∀ j, 0 < (z j).re) (σ : Equiv.Perm (Fin 3)) :
    symmetricEllipticR a (fun j => (b j : ℂ)) z =
      4 * Gamma (∑ j, (b j : ℂ)) / (∏ j, Gamma (b j : ℂ)) *
        ∫ φ in (0 : ℝ)..(π / 2), ∫ θ in (0 : ℝ)..(π / 2),
          (∑ j, z j * ((directionCosines θ φ (σ j) : ℝ) : ℂ) ^ 2) ^ (-a) *
            ((∏ j, directionCosines θ φ (σ j) ^ (2 * b j - 1) : ℝ) : ℂ) *
              (Real.sin θ : ℂ) := by
  have h := symmetricEllipticR_three_eq_integral_sphere_identity a
    (b := b ∘ σ.symm) (z := z ∘ σ.symm) (fun j => hb (σ.symm j))
    (fun j => hz (σ.symm j))
  have hperm := symmetricEllipticR_comp_perm σ.symm a (fun j => (b j : ℂ))
    (z := z) (fun j => Or.inl (hz j))
  simp only [Function.comp_def] at h hperm
  rw [hperm, Equiv.sum_comp σ.symm (fun j => (b j : ℂ)),
    Equiv.prod_comp σ.symm (fun j => Gamma (b j : ℂ))] at h
  have hsum (θ φ : ℝ) :
      (∑ j, z (σ.symm j) * ((directionCosines θ φ j : ℝ) : ℂ) ^ 2) =
        ∑ j, z j * ((directionCosines θ φ (σ j) : ℝ) : ℂ) ^ 2 := by
    simpa only [Equiv.symm_apply_apply] using
      (Equiv.sum_comp σ (fun j => z (σ.symm j) * ((directionCosines θ φ j : ℝ) : ℂ) ^ 2)).symm
  have hprod (θ φ : ℝ) :
      (∏ j, directionCosines θ φ j ^ (2 * b (σ.symm j) - 1)) =
        ∏ j, directionCosines θ φ (σ j) ^ (2 * b j - 1) := by
    simpa only [Equiv.symm_apply_apply] using
      (Equiv.prod_comp σ (fun j => directionCosines θ φ j ^ (2 * b (σ.symm j) - 1))).symm
  simpa only [hsum, hprod] using h

/-- DLMF 19.23.10, **stronger than DLMF**: Euler's integral
`R_{-a}(𝐛; 𝐳) = B(a, a')⁻¹ ∫₀¹ u^{a-1} (1 - u)^{a'-1} ∏ⱼ (1 - u + u zⱼ)^{-bⱼ} du`,
`a + a' = ∑ bⱼ`, `zⱼ ∈ ℂ \ (-∞, 0]`. DLMF assumes `a, a' > 0`; here `a, a'` and `𝐛` are complex
with `ℜ a, ℜ a' > 0`. From `lean-codes`' `Carlson.regCarlsonR_eq_unitIntervalIntegral`. -/
@[dlmf 19.23.E10]
theorem symmetricEllipticR_eq_integral_unitInterval {ι : Type*} [Fintype ι] {a a' : ℂ} {b z : ι → ℂ}
    (ha : 0 < a.re) (ha' : 0 < a'.re) (hsum : a + a' = ∑ i, b i)
    (hz : z ∈ Carlson.carlsonRSlitDomain) :
    symmetricEllipticR a b z = (betaIntegral a a')⁻¹ * ∫ u in (0 : ℝ)..1,
      (u : ℂ) ^ (a - 1) * (1 - u : ℂ) ^ (a' - 1) * ∏ i, ((1 - u : ℂ) + (u : ℂ) * z i) ^ (-b i) := by
  rw [symmetricEllipticR_of_mem _ _ hz]
  unfold Carlson.carlsonR
  have hct : 0 < ((∑ i, b i) + -a).re := by
    rw [← hsum]; simp only [add_re, neg_re]; linarith
  rw [Carlson.regCarlsonR_eq_unitIntervalIntegral (t := -a) (by simpa using ha) hct hz,
    neg_neg, show (∑ i, b i) + -a = a' by rw [← hsum]; ring]
  unfold Carlson.carlsonRUnitIntervalIntegral
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo, ← hsum,
    inv_betaIntegral ha ha']
  ring

end DLMF.EllipticIntegrals
