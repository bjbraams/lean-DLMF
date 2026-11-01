/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.EllipticIntegrals.Symmetric
public import Dirichlet.Average.TwoNode
public import DLMFMathlib.MeasureTheory.Integral.Trigonometric

/-!
# Integral representations of the symmetric elliptic integrals (DLMF §19.23)

Trigonometric, hyperbolic, spherical-average and unit-interval representations of `R_F`,
`R_G`, `R_D` and of the general `R_{-a}(𝐛; 𝐳)`.

## Main definitions

* `CarlsonRightHalfDomain`: the domain of (19.23.6) and (19.23.6_5) (19.23.p3).
* `sphereQuadraticForm`, `directionCosines`: the quadratic form of (19.23.6) and the direction
  cosines of (19.23.9).

## Main results

* `symEllIntRF_zero_eq_integral_trig`, `symEllIntRG_zero_eq_integral_trig`,
  `symEllIntRD_zero_eq_integral_trig`: the complete cases as integrals over `[0, π/2]` of
  powers of `y cos² θ + z sin² θ`, for `ℜ y, ℜ z > 0` (DLMF 19.23.1–19.23.3).
* `symEllIntRF_zero_eq_integral_symEllIntRC`, `symEllIntRF_eq_integral_symEllIntRC`: `R_F` as
  an average of `R_C` (DLMF 19.23.4, 19.23.5).
* `symEllIntRF_eq_sphere_integral`, `symEllIntRG_eq_sphere_integral`: `R_F` and `R_G` as
  averages over the unit sphere (DLMF 19.23.6, 19.23.6_5).
* `symEllIntR_two_eq_integral_trig`, `symEllIntR_three_eq_integral_sphere`: `R_{-a}(𝐛; 𝐳)` for
  `n = 2` and `n = 3` (DLMF 19.23.8, 19.23.9).
* `symEllIntR_eq_integral_unitInterval`: Euler's integral over `[0, 1]` for general `n`
  (DLMF 19.23.10, stronger than DLMF).

## Implementation notes

All functions are DLMF's (`DLMF.EllipticIntegrals.symEllIntRF` etc.); principal powers are used
throughout, and on the stated domains every base lies in the open right half-plane, so no branch
question arises. The two-node trigonometric formula uses `lean-codes`'
`Dirichlet.regCarlsonDirichletAverage_fin_two` and a change of variables by `cos² θ`. The Euler
integral (19.23.10) comes from `lean-codes`' unit-interval representation
`Carlson.regCarlsonR_eq_unitIntervalIntegral` (Carlson 1977, (6.8-6)).

The equation (19.23.7) was moved by DLMF to (19.16.2_5), which is the definition
`DLMF.EllipticIntegrals.symEllIntRG`. The final sentence of the section (19.23.p6) is a
bibliographic pointer.

## References

* NIST DLMF §19.23.
* B. C. Carlson, *Special Functions of Applied Mathematics*, 1977, Exercises 5.9-19, 5.9-20 and
  (6.8-2); formalized in `lean-codes` (`Carlson.*`).
-/

@[expose] public noncomputable section

open Complex Set MeasureTheory
open scoped Real

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
theorem symEllIntR_two_eq_integral_trig (a : ℂ) {b₁ b₂ : ℝ} (hb₁ : 0 < b₁) (hb₂ : 0 < b₂)
    {z₁ z₂ : ℂ} (hz₁ : 0 < z₁.re) (hz₂ : 0 < z₂.re) :
    symEllIntR a ![(b₁ : ℂ), b₂] ![z₁, z₂] = 2 / betaIntegral b₁ b₂ *
      ∫ θ in (0 : ℝ)..(π / 2), (z₁ * (Real.cos θ : ℂ) ^ 2 + z₂ * (Real.sin θ : ℂ) ^ 2) ^ (-a) *
        ((Real.cos θ ^ (2 * b₁ - 1) * Real.sin θ ^ (2 * b₂ - 1) : ℝ) : ℂ) := by
  have hzs : ![z₁, z₂] ∈ Carlson.carlsonRSlitDomain :=
    vec2_mem_carlsonRSlitDomain (Or.inl hz₁) (Or.inl hz₂)
  have hzr : ![z₁, z₂] ∈ Carlson.carlsonRVariableDomain := by
    intro i; fin_cases i <;> assumption
  have hb : ![(b₁ : ℂ), (b₂ : ℂ)] ∈ Complex.mvBetaConvergent := by
    intro i; fin_cases i <;> assumption
  rw [symEllIntR_of_mem _ _ hzs, Carlson.carlsonR,
    Carlson.regCarlsonR_eq_regCarlsonRIntegral _ hb hzr, Carlson.regCarlsonRIntegral,
    Dirichlet.regCarlsonDirichletAverage_fin_two, Dirichlet.regEulerIntegral]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [MeasureTheory.integral_Ioo_eq_integral_cos_sq]
  simp_rw [Complex.real_smul]
  rw [← integral_const_mul]
  rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ π / 2 by positivity),
    integral_Ioc_eq_integral_Ioo, ← integral_const_mul]
  have hB := Complex.betaIntegral_eq_Gamma_mul_div (b₁ : ℂ) (b₂ : ℂ) (show 0 < (b₁ : ℂ).re by exact hb₁)
    (show 0 < (b₂ : ℂ).re by exact hb₂)
  rw [hB]
  simp_rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo fun θ hθ => ?_
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hc2 : (1 : ℂ) - (Real.cos θ ^ 2 : ℝ) = ((Real.sin θ ^ 2 : ℝ) : ℂ) := by
    push_cast
    exact_mod_cast (show (1 : ℝ) - Real.cos θ ^ 2 = Real.sin θ ^ 2 by nlinarith [Real.sin_sq_add_cos_sq θ])
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
    ring
  rw [show (b₁ : ℂ) - 1 = ((b₁ - 1 : ℝ) : ℂ) by push_cast; ring,
    show (b₂ : ℂ) - 1 = ((b₂ - 1 : ℝ) : ℂ) by push_cast; ring,
    ← ofReal_cpow (sq_nonneg _) _, ← ofReal_cpow (sq_nonneg _) _]
  have hweightC := congrArg (fun r : ℝ => (r : ℂ)) hweight
  simp only [ofReal_mul, ofReal_ofNat] at hweightC ⊢
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  linear_combination (Gamma ((b₁ : ℂ) + b₂) * (z₁ * (Real.cos θ : ℂ) ^ 2 + z₂ * (Real.sin θ : ℂ) ^ 2) ^ (-a) *
    (Gamma (b₁ : ℂ))⁻¹ * (Gamma (b₂ : ℂ))⁻¹) * hweightC

/-! ### Complete integrals (19.23.1)–(19.23.3) -/

/-- DLMF 19.23.1: `R_F(0, y, z) = ∫₀^{π/2} (y cos² θ + z sin² θ)^{-1/2} dθ`, for `ℜ y > 0`,
`ℜ z > 0` (19.23.p1). -/
@[dlmf 19.23.E1]
theorem symEllIntRF_zero_eq_integral_trig {y z : ℂ} (hy : 0 < y.re) (hz : 0 < z.re) :
    symEllIntRF 0 y z = ∫ θ in (0 : ℝ)..(π / 2),
      (y * (Real.cos θ : ℂ) ^ 2 + z * (Real.sin θ : ℂ) ^ 2) ^ (-1 / 2 : ℂ) := by
  have hB : betaIntegral (1 / 2 : ℂ) (1 / 2) = π := by
    rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ (by norm_num) (by norm_num)]
    norm_num [Gamma_one_half_mul_self]
  have H := symEllIntR_two_eq_integral_trig (1 / 2) (b₁ := 1 / 2) (b₂ := 1 / 2)
    (by norm_num) (by norm_num) hy hz
  simp only [ofReal_div, ofReal_one, ofReal_ofNat,
    show 2 * (1 / 2 : ℝ) - 1 = 0 by norm_num, Real.rpow_zero,
    mul_one] at H
  rw [hB] at H
  rw [symEllIntRF_zero_left (Or.inl hy) (Or.inl hz), H]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

/-- DLMF 19.23.2: `R_G(0, y, z) = (1/2) ∫₀^{π/2} (y cos² θ + z sin² θ)^{1/2} dθ`, for `ℜ y > 0`,
`ℜ z > 0` (19.23.p1). -/
@[dlmf 19.23.E2]
theorem symEllIntRG_zero_eq_integral_trig {y z : ℂ} (hy : 0 < y.re) (hz : 0 < z.re) :
    symEllIntRG 0 y z = (1 / 2) * ∫ θ in (0 : ℝ)..(π / 2),
      (y * (Real.cos θ : ℂ) ^ 2 + z * (Real.sin θ : ℂ) ^ 2) ^ (1 / 2 : ℂ) := by
  have hB : betaIntegral (1 / 2 : ℂ) (1 / 2) = π := by
    rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ (by norm_num) (by norm_num)]
    norm_num [Gamma_one_half_mul_self]
  have H := symEllIntR_two_eq_integral_trig (-1 / 2) (b₁ := 1 / 2) (b₂ := 1 / 2)
    (by norm_num) (by norm_num) hy hz
  simp only [ofReal_div, ofReal_one, ofReal_ofNat,
    show 2 * (1 / 2 : ℝ) - 1 = 0 by norm_num, Real.rpow_zero,
    mul_one] at H
  rw [hB] at H
  rw [show -(-1 / 2 : ℂ) = 1 / 2 by ring] at H
  rw [(symEllIntRG_zero_left (Or.inl hy) (Or.inl hz)).1, H]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  ring

/-- DLMF 19.23.3: `R_D(0, y, z) = 3 ∫₀^{π/2} (y cos² θ + z sin² θ)^{-3/2} sin² θ dθ`, for
`ℜ y > 0`, `ℜ z > 0` (19.23.p1). -/
@[dlmf 19.23.E3]
theorem symEllIntRD_zero_eq_integral_trig {y z : ℂ} (hy : 0 < y.re) (hz : 0 < z.re) :
    symEllIntRD 0 y z = 3 * ∫ θ in (0 : ℝ)..(π / 2),
      (y * (Real.cos θ : ℂ) ^ 2 + z * (Real.sin θ : ℂ) ^ 2) ^ (-3 / 2 : ℂ) *
        (Real.sin θ : ℂ) ^ 2 := by
  have hB : betaIntegral (1 / 2 : ℂ) (3 / 2) = π / 2 := by
    rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ (by norm_num) (by norm_num)]
    norm_num
    rw [Carlson.Gamma_three_halves]
    linear_combination (1 / 2 : ℂ) * Gamma_one_half_mul_self
  have H := symEllIntR_two_eq_integral_trig (3 / 2) (b₁ := 1 / 2) (b₂ := 3 / 2)
    (by norm_num) (by norm_num) hy hz
  simp only [ofReal_div, ofReal_one, ofReal_ofNat,
    show 2 * (1 / 2 : ℝ) - 1 = 0 by norm_num,
    show 2 * (3 / 2 : ℝ) - 1 = 2 by norm_num, Real.rpow_zero, Real.rpow_two,
    one_mul, ofReal_pow] at H
  rw [hB] at H
  rw [symEllIntRD_zero_left (Or.inl hy) (Or.inl hz), H]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  simp only [show (-3 / 2 : ℂ) = -(3 / 2) by ring]
  field_simp
  ring

/-! ### `R_F` as an average of `R_C` (19.23.4), (19.23.5) -/

/-- DLMF 19.23.4: `R_F(0, y, z) = (2/π) ∫₀^{π/2} R_C(y, z cos² θ) dθ
= (2/π) ∫₀^∞ R_C(y cosh² t, z) dt`, for `ℜ y > 0`, `ℜ z > 0` (DLMF states no domain for this
formula; the notes derive it from (19.23.5) at `x = 0`, whose hypotheses are these). The
integrand of the first integral has an integrable logarithmic singularity at `θ = π/2`. -/
@[dlmf 19.23.E4]
theorem symEllIntRF_zero_eq_integral_symEllIntRC {y z : ℂ} (hy : 0 < y.re) (hz : 0 < z.re) :
    symEllIntRF 0 y z =
        (2 / π) * ∫ θ in (0 : ℝ)..(π / 2), symEllIntRC y (z * (Real.cos θ : ℂ) ^ 2) ∧
      symEllIntRF 0 y z =
        (2 / π) * ∫ t in Ioi (0 : ℝ), symEllIntRC (y * (Real.cosh t : ℂ) ^ 2) z := by
  sorry

/-- DLMF 19.23.5: `R_F(x, y, z) = (2/π) ∫₀^{π/2} R_C(x, y cos² θ + z sin² θ) dθ`, for
`ℜ y > 0`, `ℜ z > 0` and `x ∈ ℂ \ (-∞, 0)` (the domain of `R_C`'s first argument). -/
@[dlmf 19.23.E5]
theorem symEllIntRF_eq_integral_symEllIntRC {x y z : ℂ} (hx : SymEllIntArg x) (hy : 0 < y.re)
    (hz : 0 < z.re) :
    symEllIntRF x y z = (2 / π) * ∫ θ in (0 : ℝ)..(π / 2),
      symEllIntRC x (y * (Real.cos θ : ℂ) ^ 2 + z * (Real.sin θ : ℂ) ^ 2) := by
  sorry

/-! ### Averages over the sphere (19.23.6), (19.23.6_5) -/

/-- The quadratic form `x sin² θ cos² φ + y sin² θ sin² φ + z cos² θ` of (19.23.6). -/
def sphereQuadraticForm (x y z : ℂ) (θ φ : ℝ) : ℂ :=
  x * (Real.sin θ : ℂ) ^ 2 * (Real.cos φ : ℂ) ^ 2 + y * (Real.sin θ : ℂ) ^ 2 *
      (Real.sin φ : ℂ) ^ 2 +
    z * (Real.cos θ : ℂ) ^ 2

/-- DLMF 19.23.6: `4π R_F(x, y, z) = ∫₀^{2π} ∫₀^π sin θ dθ dφ /
(x sin² θ cos² φ + y sin² θ sin² φ + z cos² θ)^{1/2}`, for `x, y, z` with positive real parts,
at most one of them `0` (19.23.p3). -/
@[dlmf 19.23.E6]
theorem symEllIntRF_eq_sphere_integral {x y z : ℂ} (h : CarlsonRightHalfDomain x y z) :
    4 * π * symEllIntRF x y z = ∫ φ in (0 : ℝ)..(2 * π), ∫ θ in (0 : ℝ)..π,
      (Real.sin θ : ℂ) / sphereQuadraticForm x y z θ φ ^ (1 / 2 : ℂ) := by
  sorry

/-- DLMF 19.23.6_5 (formerly 19.16.3): `R_G(x, y, z) = (1/(4π)) ∫₀^{2π} ∫₀^π
(x sin² θ cos² φ + y sin² θ sin² φ + z cos² θ)^{1/2} sin θ dθ dφ`, for `x, y, z` with positive
real parts, at most one of them `0` (19.23.p3). -/
@[dlmf 19.23.E6_5]
theorem symEllIntRG_eq_sphere_integral {x y z : ℂ} (h : CarlsonRightHalfDomain x y z) :
    symEllIntRG x y z = (1 / (4 * π)) * ∫ φ in (0 : ℝ)..(2 * π), ∫ θ in (0 : ℝ)..π,
      sphereQuadraticForm x y z θ φ ^ (1 / 2 : ℂ) * (Real.sin θ : ℂ) := by
  sorry

/-! ### The general `R`-function (19.23.8)–(19.23.10) -/

/-- The direction cosines `(sin θ cos φ, sin θ sin φ, cos θ)` of (19.23.9). -/
def directionCosines (θ φ : ℝ) : Fin 3 → ℝ :=
  ![Real.sin θ * Real.cos φ, Real.sin θ * Real.sin φ, Real.cos θ]

/-- DLMF 19.23.9 (`n = 3`): with `l₁, l₂, l₃` any permutation `σ` of
`sin θ cos φ, sin θ sin φ, cos θ`,
`R_{-a}(𝐛; 𝐳) = 4 Γ(b₁ + b₂ + b₃)/(Γ(b₁) Γ(b₂) Γ(b₃)) ∫₀^{π/2} ∫₀^{π/2}
(∑ⱼ zⱼ lⱼ²)^{-a} ∏ⱼ lⱼ^{2bⱼ-1} sin θ dθ dφ`, for `bⱼ > 0`, `ℜ zⱼ > 0`; `a` any complex
number. -/
@[dlmf 19.23.E9]
theorem symEllIntR_three_eq_integral_sphere (a : ℂ) {b : Fin 3 → ℝ} (hb : ∀ j, 0 < b j)
    {z : Fin 3 → ℂ} (hz : ∀ j, 0 < (z j).re) (σ : Equiv.Perm (Fin 3)) :
    symEllIntR a (fun j => (b j : ℂ)) z =
      4 * Gamma (∑ j, (b j : ℂ)) / ∏ j, Gamma (b j : ℂ) *
        ∫ φ in (0 : ℝ)..(π / 2), ∫ θ in (0 : ℝ)..(π / 2),
          (∑ j, z j * ((directionCosines θ φ (σ j) : ℝ) : ℂ) ^ 2) ^ (-a) *
            ((∏ j, directionCosines θ φ (σ j) ^ (2 * b j - 1) : ℝ) : ℂ) *
              (Real.sin θ : ℂ) := by
  sorry

/-- DLMF 19.23.10, **stronger than DLMF**: Euler's integral
`R_{-a}(𝐛; 𝐳) = B(a, a')⁻¹ ∫₀¹ u^{a-1} (1 - u)^{a'-1} ∏ⱼ (1 - u + u zⱼ)^{-bⱼ} du`,
`a + a' = ∑ bⱼ`, `zⱼ ∈ ℂ \ (-∞, 0]`. DLMF assumes `a, a' > 0`; here `a, a'` and `𝐛` are complex
with `ℜ a, ℜ a' > 0`. From `lean-codes`' `Carlson.regCarlsonR_eq_unitIntervalIntegral`. -/
@[dlmf 19.23.E10]
theorem symEllIntR_eq_integral_unitInterval {ι : Type*} [Fintype ι] {a a' : ℂ} {b z : ι → ℂ}
    (ha : 0 < a.re) (ha' : 0 < a'.re) (hsum : a + a' = ∑ i, b i)
    (hz : z ∈ Carlson.carlsonRSlitDomain) :
    symEllIntR a b z = (betaIntegral a a')⁻¹ * ∫ u in (0 : ℝ)..1,
      (u : ℂ) ^ (a - 1) * (1 - u : ℂ) ^ (a' - 1) * ∏ i, ((1 - u : ℂ) + (u : ℂ) * z i) ^ (-b i) := by
  rw [symEllIntR_of_mem _ _ hz]
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
