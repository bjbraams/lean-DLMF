/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Elliptic.ReductionTables
public import Carlson.Elliptic.Standard
public import DLMF.EllipticIntegrals.Basic.SymmetricProperties
public import DLMF.EllipticIntegrals.SymmetricBounds

/-!
# Symmetric elliptic integrals: Carlson bridges and elementary identities

DLMF's symmetric standard integrals `R_F`, `R_J`, `R_G`, `R_D`, `R_C` and the multivariate
hypergeometric `R`-function `R_{-a}(𝐛; 𝐳)` of §19.16(ii). The standard integrals are defined in
`DLMF.EllipticIntegrals.Basic.Symmetric` by DLMF's own integrals (19.16.1), (19.16.2),
(19.16.2_5), (19.16.5) and (19.2.17); the `R`-function (19.16.8) is defined here, through
Carlson's `R`-function in `lean-codes`. This file relates them to Carlson's functions and
proves the elementary identities of §§19.15–19.16.

## Main definitions

* `symmetricEllipticR`: the multivariate hypergeometric function `R_{-a}(𝐛; 𝐳)` (DLMF 19.16.8).

## Main results

* `symmetricEllipticRF_eq_symmetricEllipticR`, `symmetricEllipticRD_eq_symmetricEllipticR`,
  `symmetricEllipticRJ_eq_symmetricEllipticR`, `symmetricEllipticRG_eq_symmetricEllipticR`,
  `symmetricEllipticRC_eq_symmetricEllipticR`: the integrals as `R`-functions on the slit plane
  (DLMF 19.16.14–19.16.18).
* `symmetricEllipticRF_eq_carlsonRF`, `symmetricEllipticRJ_eq_carlsonR`,
  `symmetricEllipticRG_eq_carlsonRG`, `symmetricEllipticRC_eq_carlsonRC`,
  `symmetricEllipticR_of_mem`: bridges to `lean-codes`.
* `symmetricEllipticR_eq_integral`: the integral representation of `R_{-a}(𝐛; 𝐳)` (DLMF 19.16.9,
  stronger than DLMF).
* `symmetricEllipticRF_zero_left`, `symmetricEllipticRD_zero_left`, `symmetricEllipticRJ_zero_left`,
  `symmetricEllipticRG_zero_left`: the complete cases (DLMF 19.16.20–19.16.23).
* `symmetricEllipticR_comp_perm`: permutation symmetry of the `R`-function (DLMF 19.16.8); the
  symmetry of the standard integrals and DLMF 19.16.5–19.16.7 are in
  `DLMF.EllipticIntegrals.Basic.SymmetricProperties`.
* `symmetricEllipticR_mul`, `symmetricEllipticR_const`: homogeneity and the value at equal arguments
  (DLMF 19.16.11).
* `symmetricEllipticRF_one_one_one`, `symmetricEllipticRJ_one_one_one_one`: the normalizations of
  §19.16(i).
* `two_mul_symmetricEllipticRG`: DLMF 19.21.10 at the level of the defining integrals.
* `symmetricEllipticR_four_eq_integral_sin`, `symmetricEllipticR_cons_zero`,
  `symmetricEllipticR_eq_integral_complete`: DLMF 19.16.12–19.16.13, 19.16.19, 19.16.24.

## Implementation notes

* **Domains.** DLMF §19.16(i): `x, y, z ∈ ℂ \ (-∞, 0]` except that one or more of them may be
  `0` when the integral converges; for `R_F` and `R_J` at most one may vanish, for `R_G` any
  number, for `R_D` the third argument is nonzero; `p ≠ 0`. These are the predicates
  `IsCarlsonArgument` and `CarlsonRFDomain`. Because the definitions are Lean integrals, values
  outside these domains are totalized (a divergent integral is `0`). Square roots are
  principal, so the defining integrands are those of DLMF on the whole complex domain. For
  real negative `p` the Cauchy principal value (`principalValueIoi`) is taken.
* **The `R`-function.** On the product slit plane `symmetricEllipticR a b z` is Carlson's
  `Carlson.carlsonR (-a) b z`; note DLMF's sign convention for the subscript. At the boundary
  (some `z_j = 0`, "without destroying convergence", §19.16(iii)) it is the limit from the slit
  domain.
* **Bridges** to `lean-codes` (`Carlson.carlsonRF`, `Carlson.carlsonRG`,
  `Carlson.TwoVariable.carlsonRC`, `Carlson.carlsonR`) on the slit plane are DLMF's
  (19.16.14)–(19.16.18); the normalizations were checked numerically (mpmath `elliprf`,
  `elliprj`, `elliprg`, `elliprc`; for `p < 0` mpmath's `elliprj` returns a complex number whose
  real part is the principal value used here).
* **§19.15 (prose).** The `R`-function reveals the permutation symmetry hidden in Lauricella's
  `F_D` (19.15.p1). Symmetry of `R_F`, `R_G`, `R_J` in `x, y, z` (`Carlson.carlsonRF_perm`, …,
  and `symmetricEllipticR_comp_perm`) replaces the five Legendre transformations (19.7.2),
  (19.7.4)–(19.7.7), unifies Landen and Gauss transformations (§19.22) and the parameter
  changes of `Π` (19.21.12) (19.15.p2); it permits the elementary-symmetric expansion (19.19.7)
  (19.15.p3) and the reduction theorems of §19.29 (19.15.p4); symmetry in the semiaxes of
  ellipsoids is preserved (19.15.p5). These are commentary; the mathematical content is in the
  cited formulas.

## References

* NIST DLMF §§19.2(iv), 19.15, 19.16.
* B. C. Carlson, *Special Functions of Applied Mathematics*, 1977; formalized in `lean-codes`
  (`Carlson.*`), reused here through bridge theorems.
-/

@[expose] public noncomputable section

open Complex Set Filter MeasureTheory
open scoped Real Topology

namespace DLMF.EllipticIntegrals

/-! ### The multivariate hypergeometric `R`-function -/

/-- DLMF 19.16.8: the multivariate hypergeometric function `R_{-a}(𝐛; 𝐳)` (written
`R(a; 𝐛; 𝐳)` before 1969). On the product slit plane it is Carlson's `R`-function
`Carlson.carlsonR (-a) b z` (all complex `a` and `𝐛`; DLMF's (19.16.9) has real `𝐛` with
`∑ bⱼ > a > 0`, and Carlson's continuation in the parameters is used elsewhere in DLMF, e.g.
`R_{1/2}` in (19.16.17)). When some `zⱼ` lies off the slit plane (DLMF allows `zⱼ = 0`
"without destroying convergence", §19.16(iii)), the value is the limit from the slit domain;
where that limit does not exist the value is junk. -/
@[dlmf 19.16.E8]
def symmetricEllipticR {ι : Type*} [Fintype ι] (a : ℂ) (b z : ι → ℂ) : ℂ := by
  classical
  exact if z ∈ Carlson.carlsonRSlitDomain then Carlson.carlsonR (-a) b z
    else limUnder (𝓝[Carlson.carlsonRSlitDomain] z) (Carlson.carlsonR (-a) b)

/-- Identity under the stated parameter and domain assumptions: `symmetricEllipticR a b z =
Carlson.carlsonR (-a) b z`. -/
theorem symmetricEllipticR_of_mem {ι : Type*} [Fintype ι] (a : ℂ) (b : ι → ℂ) {z : ι → ℂ}
    (hz : z ∈ Carlson.carlsonRSlitDomain) : symmetricEllipticR a b z =
        Carlson.carlsonR (-a) b z := by
  simp [symmetricEllipticR, hz]

/-- Identity under the stated parameter and domain assumptions: `(betaIntegral a a')⁻¹ = Gamma (a
+ a') / (Gamma a * Gamma a')`. -/
theorem inv_betaIntegral {a a' : ℂ} (ha : 0 < a.re) (ha' : 0 < a'.re) :
    (betaIntegral a a')⁻¹ = Gamma (a + a') / (Gamma a * Gamma a') := by
  have h := Complex.Gamma_mul_Gamma_eq_betaIntegral ha ha'
  have h1 : Gamma (a + a') ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  rw [h]; field_simp

/-- Identity under the stated parameter and domain assumptions: `Gamma (5 / 2 : ℂ) = (3 / 2) *
Gamma (3 / 2)`. -/
lemma Gamma_five_halves_eq_mul : Gamma (5 / 2 : ℂ) = (3 / 2) * Gamma (3 / 2) := by
  rw [show (5 / 2 : ℂ) = 3 / 2 + 1 by norm_num, Complex.Gamma_add_one _ (by norm_num)]

/-- Nonvanishing under the stated hypotheses: `Gamma (1 / 2 : ℂ) ≠ 0`. -/
theorem Gamma_one_half_ne_zero : Gamma (1 / 2 : ℂ) ≠ 0 :=
  Complex.Gamma_ne_zero_of_re_pos (by norm_num)

/-- Identity under the stated parameter and domain assumptions: `Gamma (1 / 2 : ℂ) * Gamma (1 / 2)
= π`. -/
lemma Gamma_one_half_mul_self : Gamma (1 / 2 : ℂ) * Gamma (1 / 2) = π := by
  rw [Complex.Gamma_one_half_eq, cpow_half_mul_cpow_half]

/-- DLMF 19.16.9 (first form), **stronger than DLMF**: for complex `a, 𝐛` with `Re a > 0`,
`Re a' > 0`, `a' = -a + ∑ bⱼ` (19.16.10), and nodes in the slit plane,
`R_{-a}(𝐛; 𝐳) = B(a, a')⁻¹ ∫₀^∞ t^{a'-1} ∏ⱼ (t + zⱼ)^{-bⱼ} dt`. DLMF assumes real `bⱼ` and
`∑ bⱼ > a > 0`. From `Carlson.carlsonRPositiveRayIntegral_eq_Gamma_mul_regCarlsonR`. -/
@[dlmf 19.16.E9]
theorem symmetricEllipticR_eq_integral {ι : Type*} [Fintype ι] {a a' : ℂ} {b z : ι → ℂ}
    (ha : 0 < a.re) (ha' : 0 < a'.re) (hsum : a' = -a + ∑ i, b i)
    (hz : z ∈ Carlson.carlsonRSlitDomain) :
    symmetricEllipticR a b z = (betaIntegral a a')⁻¹ *
      ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (a' - 1) * ∏ i, ((t : ℂ) + z i) ^ (-b i) := by
  rw [symmetricEllipticR_of_mem _ _ hz]
  have h := Carlson.carlsonRPositiveRayIntegral_eq_Gamma_mul_regCarlsonR (a := a') (a' := a)
    (b := b) ha' ha (by rw [hsum]; ring) hz
  unfold Carlson.carlsonRPositiveRayIntegral at h
  have hint : (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (a' - 1) * ∏ i, ((t : ℂ) + z i) ^ (-b i)) =
      ∫ s in Ioi (0 : ℝ), (s : ℂ) ^ (a' - 1) * ∏ i, (z i + (s : ℂ)) ^ (-b i) := by
    congr 1; funext t; simp only [add_comm]
  rw [hint, h, inv_betaIntegral ha ha']
  unfold Carlson.carlsonR
  have hS : ∑ i, b i = a + a' := by rw [hsum]; ring
  have h1 : Gamma a ≠ 0 := Complex.Gamma_ne_zero_of_re_pos ha
  have h2 : Gamma a' ≠ 0 := Complex.Gamma_ne_zero_of_re_pos ha'
  rw [hS]; field_simp

/-- DLMF 19.16.10 (the conjugate exponent `a' = -a + ∑ bⱼ`) as used in (19.16.9). -/
@[dlmf 19.16.E10]
def symmetricEllipticRConjugateExponent {ι : Type*} [Fintype ι] (a : ℂ) (b : ι → ℂ) :
    ℂ := -a + ∑ i, b i

/-! ### The named integrals as `R`-functions (19.16.14–19.16.18) -/

/-- Formula under the stated hypotheses: `(![x, y, z] : Fin 3 → ℂ) ∈ Carlson.carlsonRSlitDomain`. -/
theorem vec3_mem_carlsonRSlitDomain {x y z : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) :
    (![x, y, z] : Fin 3 → ℂ) ∈ Carlson.carlsonRSlitDomain := by
  intro i; fin_cases i <;> assumption

/-- Formula under the stated hypotheses: `(![x, y] : Fin 2 → ℂ) ∈ Carlson.carlsonRSlitDomain`. -/
theorem vec2_mem_carlsonRSlitDomain {x y : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) :
    (![x, y] : Fin 2 → ℂ) ∈ Carlson.carlsonRSlitDomain := by
  intro i; fin_cases i <;> assumption

/-- Formula under the stated hypotheses: `(![x, y, z, p] : Fin 4 → ℂ) ∈
Carlson.carlsonRSlitDomain`. -/
theorem vec4_mem_carlsonRSlitDomain {x y z p : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) (hp : p ∈ slitPlane) :
    (![x, y, z, p] : Fin 4 → ℂ) ∈ Carlson.carlsonRSlitDomain := by
  intro i; fin_cases i <;> assumption

/-- DLMF 19.16.14: `R_F(x, y, z) = R_{-1/2}(1/2, 1/2, 1/2; x, y, z)` on the slit plane. -/
@[dlmf 19.16.E14]
theorem symmetricEllipticRF_eq_symmetricEllipticR {x y z : ℂ} (hx : x ∈ slitPlane)
    (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) :
    symmetricEllipticRF x y z = symmetricEllipticR (1 / 2) (fun _ : Fin 3 => 1 / 2) ![x, y, z] := by
  rw [symmetricEllipticR_eq_integral (a' := 1) (by norm_num) (by norm_num)
    (by simp; try norm_num) (vec3_mem_carlsonRSlitDomain hx hy hz),
    inv_betaIntegral (by norm_num) (by norm_num), symmetricEllipticRF]
  simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, sub_self, cpow_zero, one_mul, Gamma_one, mul_one]
  rw [show (1 / 2 : ℂ) + 1 = 3 / 2 by norm_num, Carlson.Gamma_three_halves,
    mul_div_assoc, div_self Gamma_one_half_ne_zero, mul_one]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [carlsonRootProduct, mul_inv, inv_cpow_half_eq_cpow_neg_half, neg_div]

/-- Bridge: on the slit plane DLMF's `R_F` is `Carlson.carlsonRF` of `lean-codes`. -/
theorem symmetricEllipticRF_eq_carlsonRF {x y z : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) : symmetricEllipticRF x y z = Carlson.carlsonRF x y z := by
  rw [symmetricEllipticRF_eq_symmetricEllipticR hx hy hz,
      symmetricEllipticR_of_mem _ _ (vec3_mem_carlsonRSlitDomain hx hy hz),
    Carlson.carlsonRF]
  congr 1; ring

/-- DLMF 19.16.16: `R_J(x, y, z, p) = R_{-3/2}(1/2, 1/2, 1/2, 1; x, y, z, p)` on the slit plane
(`p ∈ slitPlane`: no principal value). -/
@[dlmf 19.16.E16]
theorem symmetricEllipticRJ_eq_symmetricEllipticR {x y z p : ℂ} (hx : x ∈ slitPlane)
    (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) (hp : p ∈ slitPlane) :
    symmetricEllipticRJ x y z p =
        symmetricEllipticR (3 / 2) ![1 / 2, 1 / 2, 1 / 2, 1] ![x, y, z, p] := by
  rw [symmetricEllipticR_eq_integral (a' := 1) (by norm_num) (by norm_num)
    (by simp [Fin.sum_univ_four]; try norm_num) (vec4_mem_carlsonRSlitDomain hx hy hz hp),
    inv_betaIntegral (by norm_num) (by norm_num), symmetricEllipticRJ,
    ite_eq_right (not_isNegReal_of_mem_slitPlane hp)]
  simp only [Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, sub_self, cpow_zero, one_mul,
    Gamma_one, mul_one, cpow_neg_one]
  rw [show (3 / 2 : ℂ) + 1 = 5 / 2 by norm_num, Gamma_five_halves_eq_mul,
    mul_div_assoc, div_self (Complex.Gamma_ne_zero_of_re_pos (by norm_num)), mul_one]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [carlsonRootProduct, mul_inv, inv_cpow_half_eq_cpow_neg_half, neg_div]

/-- Bridge: on the slit plane DLMF's `R_J` is Carlson's `R_{-3/2}(1/2, 1/2, 1/2, 1; …)`. -/
theorem symmetricEllipticRJ_eq_carlsonR {x y z p : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) (hp : p ∈ slitPlane) :
    symmetricEllipticRJ x y z p =
        Carlson.carlsonR (-3 / 2) ![1 / 2, 1 / 2, 1 / 2, 1] ![x, y, z, p] := by
  rw [symmetricEllipticRJ_eq_symmetricEllipticR hx hy hz hp,
      symmetricEllipticR_of_mem _ _ (vec4_mem_carlsonRSlitDomain hx hy hz hp)]
  congr 1; ring

/-- DLMF 19.16.15: `R_D(x, y, z) = R_{-3/2}(1/2, 1/2, 3/2; x, y, z)` on the slit plane. -/
@[dlmf 19.16.E15]
theorem symmetricEllipticRD_eq_symmetricEllipticR {x y z : ℂ} (hx : x ∈ slitPlane)
    (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) :
    symmetricEllipticRD x y z = symmetricEllipticR (3 / 2) ![1 / 2, 1 / 2, 3 / 2] ![x, y, z] := by
  rw [symmetricEllipticR_eq_integral (a' := 1) (by norm_num) (by norm_num)
    (by simp [Fin.sum_univ_three]; try norm_num) (vec3_mem_carlsonRSlitDomain hx hy hz),
    inv_betaIntegral (by norm_num) (by norm_num), symmetricEllipticRD, symmetricEllipticRJ,
    ite_eq_right (not_isNegReal_of_mem_slitPlane hz)]
  simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, sub_self, cpow_zero, one_mul, Gamma_one, mul_one]
  rw [show (3 / 2 : ℂ) + 1 = 5 / 2 by norm_num, Gamma_five_halves_eq_mul,
    mul_div_assoc, div_self (Complex.Gamma_ne_zero_of_re_pos (by norm_num)), mul_one]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [cpow_neg_three_halves_eq (ofReal_add_ne_zero_of_isCarlsonArgument ht (Or.inl hz))]
  simp only [carlsonRootProduct, mul_inv, inv_cpow_half_eq_cpow_neg_half, neg_div]
  ring

/-- DLMF 19.16.18: `R_C(x, y) = R_{-1/2}(1/2, 1; x, y)` on the slit plane. -/
@[dlmf 19.16.E18]
theorem symmetricEllipticRC_eq_symmetricEllipticR {x y : ℂ} (hx : x ∈ slitPlane)
    (hy : y ∈ slitPlane) :
    symmetricEllipticRC x y = symmetricEllipticR (1 / 2) ![1 / 2, 1] ![x, y] := by
  rw [symmetricEllipticR_eq_integral (a' := 1) (by norm_num) (by norm_num)
    (by simp) (vec2_mem_carlsonRSlitDomain hx hy),
    inv_betaIntegral (by norm_num) (by norm_num), symmetricEllipticRC,
    ite_eq_right (not_isNegReal_of_mem_slitPlane hy)]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    sub_self, cpow_zero, one_mul, Gamma_one, mul_one, cpow_neg_one]
  rw [show (1 / 2 : ℂ) + 1 = 3 / 2 by norm_num, Carlson.Gamma_three_halves,
    mul_div_assoc, div_self Gamma_one_half_ne_zero, mul_one]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [mul_inv, inv_cpow_half_eq_cpow_neg_half, neg_div]

/-- Bridge: on the slit plane DLMF's `R_C` is `Carlson.TwoVariable.carlsonRC` of `lean-codes`. -/
theorem symmetricEllipticRC_eq_carlsonRC {x y : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) :
    symmetricEllipticRC x y = Carlson.TwoVariable.carlsonRC x y := by
  rw [symmetricEllipticRC_eq_symmetricEllipticR hx hy,
      symmetricEllipticR_of_mem _ _ (vec2_mem_carlsonRSlitDomain hx hy)]
  unfold Carlson.TwoVariable.carlsonRC Carlson.TwoVariable.pair
  congr 1; ring

/-! ### Zero-variable (complete) cases 19.16.20–19.16.22 -/

/-- DLMF 19.16.20: `R_F(0, y, z) = (π/2) R_{-1/2}(1/2, 1/2; y, z)`, `y, z ∈ ℂ \ (-∞, 0]`. -/
@[dlmf 19.16.E20]
theorem symmetricEllipticRF_zero_left {y z : ℂ} (hy : y ∈ slitPlane) (hz : z ∈ slitPlane) :
    symmetricEllipticRF 0 y z = (π / 2) * symmetricEllipticR (1 / 2) ![1 / 2, 1 / 2] ![y, z] := by
  rw [symmetricEllipticR_eq_integral (a' := 1 / 2) (by norm_num) (by norm_num)
    (by simp) (vec2_mem_carlsonRSlitDomain hy hz),
    inv_betaIntegral (by norm_num) (by norm_num), symmetricEllipticRF]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show (1 / 2 : ℂ) + 1 / 2 = 1 by norm_num, Gamma_one, Gamma_one_half_mul_self,
    show (1 / 2 : ℂ) - 1 = -(1 / 2) by norm_num]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [← mul_assoc, show (π : ℂ) / 2 * (1 / π) = 1 / 2 by field_simp]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [carlsonRootProduct, add_zero, mul_inv, inv_cpow_half_eq_cpow_neg_half, neg_div]
  ring

/-- DLMF 19.16.21: `R_D(0, y, z) = (3π/4) R_{-3/2}(1/2, 3/2; y, z)`, `y, z ∈ ℂ \ (-∞, 0]`. -/
@[dlmf 19.16.E21]
theorem symmetricEllipticRD_zero_left {y z : ℂ} (hy : y ∈ slitPlane) (hz : z ∈ slitPlane) :
    symmetricEllipticRD 0 y z = (3 * π / 4) *
        symmetricEllipticR (3 / 2) ![1 / 2, 3 / 2] ![y, z] := by
  rw [symmetricEllipticR_eq_integral (a' := 1 / 2) (by norm_num) (by norm_num)
    (by simp) (vec2_mem_carlsonRSlitDomain hy hz),
    inv_betaIntegral (by norm_num) (by norm_num), symmetricEllipticRD, symmetricEllipticRJ,
    ite_eq_right (not_isNegReal_of_mem_slitPlane hz)]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show (3 / 2 : ℂ) + 1 / 2 = 2 by norm_num, Carlson.Gamma_two', Carlson.Gamma_three_halves,
    show (1 / 2 : ℂ) - 1 = -(1 / 2) by norm_num, mul_assoc (1 / 2 : ℂ), Gamma_one_half_mul_self]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [← mul_assoc, show 3 * (π : ℂ) / 4 * (1 / (1 / 2 * π)) = 3 / 2 by field_simp; ring]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [cpow_neg_three_halves_eq (ofReal_add_ne_zero_of_isCarlsonArgument ht (Or.inl hz))]
  simp only [carlsonRootProduct, add_zero, mul_inv, inv_cpow_half_eq_cpow_neg_half, neg_div]
  ring

/-- DLMF 19.16.22: `R_J(0, y, z, p) = (3π/4) R_{-3/2}(1/2, 1/2, 1; y, z, p)`,
`y, z, p ∈ ℂ \ (-∞, 0]`. -/
@[dlmf 19.16.E22]
theorem symmetricEllipticRJ_zero_left {y z p : ℂ} (hy : y ∈ slitPlane) (hz : z ∈ slitPlane)
    (hp : p ∈ slitPlane) :
    symmetricEllipticRJ 0 y z p = (3 * π / 4) *
        symmetricEllipticR (3 / 2) ![1 / 2, 1 / 2, 1] ![y, z, p] := by
  rw [symmetricEllipticR_eq_integral (a' := 1 / 2) (by norm_num) (by norm_num)
    (by simp [Fin.sum_univ_three]; try norm_num) (vec3_mem_carlsonRSlitDomain hy hz hp),
    inv_betaIntegral (by norm_num) (by norm_num), symmetricEllipticRJ,
    ite_eq_right (not_isNegReal_of_mem_slitPlane hp)]
  simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, cpow_neg_one]
  rw [show (3 / 2 : ℂ) + 1 / 2 = 2 by norm_num, Carlson.Gamma_two', Carlson.Gamma_three_halves,
    show (1 / 2 : ℂ) - 1 = -(1 / 2) by norm_num, mul_assoc (1 / 2 : ℂ), Gamma_one_half_mul_self]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [← mul_assoc, show 3 * (π : ℂ) / 4 * (1 / (1 / 2 * π)) = 3 / 2 by field_simp; ring]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [carlsonRootProduct, add_zero, mul_inv, inv_cpow_half_eq_cpow_neg_half, neg_div]
  ring

/-! ### Symmetry, homogeneity and normalization -/

/-- DLMF 19.16.8: `R_{-a}(𝐛; 𝐳)` is unchanged when the same permutation is applied to `𝐛` and
`𝐳` (slit-plane nodes). From `Carlson.regCarlsonR_comp_perm`. -/
@[dlmf 19.16.E8]
theorem symmetricEllipticR_comp_perm {ι : Type*} [Fintype ι] (σ : Equiv.Perm ι) (a : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ Carlson.carlsonRSlitDomain) :
    symmetricEllipticR a (b ∘ σ) (z ∘ σ) = symmetricEllipticR a b z := by
  have hz' : z ∘ σ ∈ Carlson.carlsonRSlitDomain := fun i => hz (σ i)
  rw [symmetricEllipticR_of_mem _ _ hz', symmetricEllipticR_of_mem _ _ hz]
  unfold Carlson.carlsonR
  have h1 : (b ∘ σ) ∘ σ.symm = b := by funext i; simp
  have h2 : ∑ i, (b ∘ σ) i = ∑ i, b i := Equiv.sum_comp σ b
  rw [Carlson.regCarlsonR_comp_perm σ _ hz, h1, h2]

/-- DLMF 19.16.11 (first part): homogeneity `R_{-a}(𝐛; λ𝐳) = λ^{-a} R_{-a}(𝐛; 𝐳)`, with the
branch condition made explicit: `λ` and all `zⱼ` in the slit plane and
`ph λ + ph zⱼ ∈ (-π, π)` (DLMF states no condition; for `λ > 0` it is automatic). From
`Carlson.regCarlsonR_mul_of_arg_add`. -/
@[dlmf 19.16.E11]
theorem symmetricEllipticR_mul {ι : Type*} [Fintype ι] (a : ℂ) (b : ι → ℂ) {μ : ℂ} {z : ι → ℂ}
    (hz : z ∈ Carlson.carlsonRSlitDomain) (hμ : μ ∈ slitPlane)
    (harg : ∀ i, arg μ + arg (z i) ∈ Ioo (-Real.pi) Real.pi) :
    symmetricEllipticR a b (fun i => μ * z i) = μ ^ (-a) * symmetricEllipticR a b z := by
  have hz' : (fun i => μ * z i) ∈ Carlson.carlsonRSlitDomain := by
    intro i
    have hμ' := mem_slitPlane_iff_arg.mp hμ
    have hw := mem_slitPlane_iff_arg.mp (hz i)
    rw [mem_slitPlane_iff_arg, arg_mul hμ'.2 hw.2 ⟨(harg i).1, (harg i).2.le⟩]
    exact ⟨(harg i).2.ne, mul_ne_zero hμ'.2 hw.2⟩
  rw [symmetricEllipticR_of_mem _ _ hz', symmetricEllipticR_of_mem _ _ hz]
  unfold Carlson.carlsonR
  rw [Carlson.regCarlsonR_mul_of_arg_add _ b hz hμ harg]
  ring

/-- DLMF 19.16.11 (second part): `R_{-a}(𝐛; x𝟏) = x^{-a}` for `x ∈ ℂ \ (-∞, 0]`, when
`Γ(∑ bⱼ) ≠ 0` (Lean's `Γ` vanishes at its poles; DLMF has `∑ bⱼ > a > 0`). -/
@[dlmf 19.16.E11]
theorem symmetricEllipticR_const {ι : Type*} [Fintype ι] (a : ℂ) (b : ι → ℂ) {x : ℂ}
    (hx : x ∈ slitPlane) (hb : Gamma (∑ i, b i) ≠ 0) :
    symmetricEllipticR a b (fun _ => x) = x ^ (-a) := by
  rw [symmetricEllipticR_of_mem _ _ (fun _ => hx)]
  unfold Carlson.carlsonR
  rw [Carlson.regCarlsonR_const_node _ _ hx]
  field_simp

/-- DLMF 19.16.i.p1: the normalization `R_F(1, 1, 1) = 1`. -/
@[dlmf 19.16.i]
theorem symmetricEllipticRF_one_one_one : symmetricEllipticRF 1 1 1 = 1 := by
  have h1 : (1 : ℂ) ∈ slitPlane := one_mem_slitPlane
  rw [symmetricEllipticRF_eq_carlsonRF h1 h1 h1, Carlson.carlsonRF_self h1, one_cpow]

/-- DLMF 19.16.i.p1: the normalization `R_J(1, 1, 1, 1) = 1`. -/
@[dlmf 19.16.i]
theorem symmetricEllipticRJ_one_one_one_one : symmetricEllipticRJ 1 1 1 1 = 1 := by
  have h1 : (1 : ℂ) ∈ slitPlane := one_mem_slitPlane
  rw [symmetricEllipticRJ_eq_symmetricEllipticR h1 h1 h1 h1]
  have : (![1, 1, 1, 1] : Fin 4 → ℂ) = fun _ => 1 := by funext i; fin_cases i <;> rfl
  have hG : Gamma (∑ i, (![1 / 2, 1 / 2, 1 / 2, 1] : Fin 4 → ℂ) i) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simp [Fin.sum_univ_four]; norm_num)
  rw [this, symmetricEllipticR_const _ _ h1 hG, one_cpow]

/-! ### `R_G` and further representations -/

/-- DLMF 19.21.10 at the level of the defining integrals, **stronger than DLMF** in allowing
`x = 0`: `2R_G(x, y, z) = z R_F(x, y, z) - (1/3)(x - z)(y - z) R_D(x, y, z)
+ x^{1/2} y^{1/2} z^{-1/2}` for admissible `x` and `y, z ∈ ℂ \ (-∞, 0]`. Proved from the exact
antiderivative of `symmetricEllipticRG_integral_identity`. -/
@[dlmf 19.21.E10]
theorem two_mul_symmetricEllipticRG {x y z : ℂ} (hx : IsCarlsonArgument x) (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) :
    2 * symmetricEllipticRG x y z = z * symmetricEllipticRF x y z -
      (1 / 3) * (x - z) * (y - z) * symmetricEllipticRD x y z +
        x ^ (1 / 2 : ℂ) * y ^ (1 / 2 : ℂ) * z ^ (-1 / 2 : ℂ) := by
  have key := symmetricEllipticRG_integral_identity hx hy hz
  rw [symmetricEllipticRD_eq_integral (not_isNegReal_of_mem_slitPlane hz)]
  simp only [symmetricEllipticRG, symmetricEllipticRF, carlsonRootProduct]
  linear_combination (1 / 2 : ℂ) * key

/-- Bridge (slit plane): DLMF's `R_G` integral (19.16.2_5) is `Carlson.carlsonRG`. From
`two_mul_symmetricEllipticRG` and Carlson's Table 9.3-1, row 3 (`lean-codes`). -/
private lemma symmetricEllipticRG_eq_carlsonRG' {x y z : ℂ} (hx : x ∈ slitPlane)
    (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) : symmetricEllipticRG x y z = Carlson.carlsonRG x y z := by
  have h1 := two_mul_symmetricEllipticRG (Or.inl hx) hy hz
  have h2 := Carlson.carlsonR_table_9_3_1_row3 hx hy hz
  rw [symmetricEllipticRF_eq_carlsonRF hx hy hz, symmetricEllipticRD_eq_symmetricEllipticR hx hy hz,
    symmetricEllipticR_of_mem _ _ (vec3_mem_carlsonRSlitDomain hx hy hz), show -(3 / 2 : ℂ) = -3 /
        2 by ring] at h1
  have ex : x * x ^ (-1 / 2 : ℂ) = x ^ (1 / 2 : ℂ) := by
    calc x * x ^ (-1 / 2 : ℂ) = x ^ (1 : ℂ) * x ^ (-1 / 2 : ℂ) := by rw [cpow_one]
      _ = _ := by rw [← cpow_add _ _ (slitPlane_ne_zero hx)]; norm_num
  have ey : y * y ^ (-1 / 2 : ℂ) = y ^ (1 / 2 : ℂ) := by
    calc y * y ^ (-1 / 2 : ℂ) = y ^ (1 : ℂ) * y ^ (-1 / 2 : ℂ) := by rw [cpow_one]
      _ = _ := by rw [← cpow_add _ _ (slitPlane_ne_zero hy)]; norm_num
  have e3 : x * y * (x ^ (-1 / 2 : ℂ) * y ^ (-1 / 2 : ℂ) * z ^ (-1 / 2 : ℂ)) =
      x ^ (1 / 2 : ℂ) * y ^ (1 / 2 : ℂ) * z ^ (-1 / 2 : ℂ) := by
    rw [← ex, ← ey]; ring
  rw [e3] at h2
  linear_combination (1 / 2 : ℂ) * h1 - (1 / 2 : ℂ) * h2

/-- DLMF 19.16.17: `R_G(x, y, z) = R_{1/2}(1/2, 1/2, 1/2; x, y, z)` on the slit plane
(note `a = -1/2` here, outside the integral (19.16.9); the right side is Carlson's
continuation, `lean-codes`' `Carlson.carlsonRG`). -/
@[dlmf 19.16.E17]
theorem symmetricEllipticRG_eq_symmetricEllipticR {x y z : ℂ} (hx : x ∈ slitPlane)
    (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) :
    symmetricEllipticRG x y z =
        symmetricEllipticR (-1 / 2) (fun _ : Fin 3 => 1 / 2) ![x, y, z] := by
  rw [symmetricEllipticRG_eq_carlsonRG' hx hy hz,
      symmetricEllipticR_of_mem _ _ (vec3_mem_carlsonRSlitDomain hx hy hz),
    Carlson.carlsonRG]
  congr 1; ring

/-- Bridge: on the slit plane DLMF's `R_G` is `Carlson.carlsonRG` of `lean-codes`. -/
theorem symmetricEllipticRG_eq_carlsonRG {x y z : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) : symmetricEllipticRG x y z = Carlson.carlsonRG x y z := by
  rw [symmetricEllipticRG_eq_symmetricEllipticR hx hy hz,
      symmetricEllipticR_of_mem _ _ (vec3_mem_carlsonRSlitDomain hx hy hz),
    Carlson.carlsonRG]
  congr 1; ring

/-- The pointwise identity behind (19.16.12): the integrand of (19.16.9) after the substitution
`t = 1/sin² θ - 1/sin² φ`, with `s = sin θ`, `C = cos θ`, `S2 = sin² φ`. -/
private lemma sin_subst_identity {a a' b₁ b₂ b₄ S2 s C k2 α2 : ℝ} (hs : 0 < s) (hC : 0 < C)
    (hsC : C ^ 2 = 1 - s ^ 2) (hsS : s ^ 2 < S2) (hk : 0 < 1 - k2 * s ^ 2)
    (hα : 0 < 1 - α2 * s ^ 2) :
    2 * C / s ^ 3 * ((S2 - s ^ 2) / (s ^ 2 * S2)) ^ (a' - 1) *
        ((1 / s ^ 2 - 1) ^ (-b₁) * (1 / s ^ 2 - k2) ^ (-b₂) *
          (1 / s ^ 2) ^ (-(a + a' - b₁ - b₂ - b₄)) * (1 / s ^ 2 - α2) ^ (-b₄)) =
      2 * S2 ^ (1 - a') * (s ^ (2 * a - 1) * (S2 - s ^ 2) ^ (a' - 1) * C ^ (1 - 2 * b₁) *
        (1 - k2 * s ^ 2) ^ (-b₂) * (1 - α2 * s ^ 2) ^ (-b₄)) := by
  have hS2 : 0 < S2 := by nlinarith
  have hD : 0 < S2 - s ^ 2 := by linarith
  have e1 : 1 / s ^ 2 - 1 = C ^ 2 / s ^ 2 := by rw [hsC]; field_simp
  have e2 : 1 / s ^ 2 - k2 = (1 - k2 * s ^ 2) / s ^ 2 := by field_simp
  have e3 : 1 / s ^ 2 - α2 = (1 - α2 * s ^ 2) / s ^ 2 := by field_simp
  rw [e1, e2, e3]
  generalize S2 - s ^ 2 = D at hD ⊢
  generalize 1 - k2 * s ^ 2 = K at hk ⊢
  generalize 1 - α2 * s ^ 2 = A at hα ⊢
  have hl : 0 < 2 * C / s ^ 3 * (D / (s ^ 2 * S2)) ^ (a' - 1) *
        ((C ^ 2 / s ^ 2) ^ (-b₁) * (K / s ^ 2) ^ (-b₂) *
          (1 / s ^ 2) ^ (-(a + a' - b₁ - b₂ - b₄)) * (A / s ^ 2) ^ (-b₄)) := by positivity
  have hr : 0 < 2 * S2 ^ (1 - a') * (s ^ (2 * a - 1) * D ^ (a' - 1) * C ^ (1 - 2 * b₁) *
        K ^ (-b₂) * A ^ (-b₄)) := by positivity
  rw [← Real.exp_log hl, ← Real.exp_log hr]
  congr 1
  simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow, Real.log_pow,
    Real.log_one]
  push_cast
  ring


/-- DLMF 19.16.12 with 19.16.13: for `n = 4`, `c = csc² φ`, `a, a' > 0`,
`b₃ = a + a' - b₁ - b₂ - b₄`,
`R_{-a}(b₁, …, b₄; c - 1, c - k², c, c - α²) = 2 (sin² φ)^{1-a'} / B(a, a') ∫₀^φ (sin θ)^{2a-1}
(sin² φ - sin² θ)^{a'-1} (cos θ)^{1-2b₁} (1 - k² sin² θ)^{-b₂} (1 - α² sin² θ)^{-b₄} dθ`.
Real parameters; `0 < φ < π/2` and `k² sin² φ < 1`, `α² sin² φ < 1` keep the nodes positive. -/
@[dlmf 19.16.E12, dlmf 19.16.E13]
theorem symmetricEllipticR_four_eq_integral_sin {a a' b₁ b₂ b₄ φ k α : ℝ}
    (ha : 0 < a) (ha' : 0 < a')
    (hφ : 0 < φ) (hφ' : φ < π / 2) (hk : k ^ 2 * Real.sin φ ^ 2 < 1)
    (hα : α ^ 2 * Real.sin φ ^ 2 < 1) :
    let c : ℝ := 1 / Real.sin φ ^ 2
    symmetricEllipticR (a : ℂ) ![(b₁ : ℂ), b₂, a + a' - b₁ - b₂ - b₄, b₄]
        ![((c - 1 : ℝ) : ℂ), ((c - k ^ 2 : ℝ) : ℂ), ((c : ℝ) : ℂ), ((c - α ^ 2 : ℝ) : ℂ)] =
      (betaIntegral a a')⁻¹ * (2 * (Real.sin φ ^ 2) ^ (1 - a') *
        ∫ θ in (0 : ℝ)..φ, Real.sin θ ^ (2 * a - 1) * (Real.sin φ ^ 2 - Real.sin θ ^ 2) ^ (a' - 1) *
          Real.cos θ ^ (1 - 2 * b₁) * (1 - k ^ 2 * Real.sin θ ^ 2) ^ (-b₂) *
          (1 - α ^ 2 * Real.sin θ ^ 2) ^ (-b₄) : ℝ) := by
  intro c
  have hS : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi hφ (by linarith [Real.pi_pos])
  have hS1 : Real.sin φ < 1 := by
    rw [← Real.sin_pi_div_two]
    exact Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) le_rfl hφ'
  have hS2 : 0 < Real.sin φ ^ 2 := by positivity
  have hc1 : 1 < c := by
    simp only [c]; rw [lt_div_iff₀ hS2]; nlinarith
  have hck : k ^ 2 < c := by simp only [c]; rw [lt_div_iff₀ hS2]; linarith
  have hcα : α ^ 2 < c := by simp only [c]; rw [lt_div_iff₀ hS2]; linarith
  have hz : (![((c - 1 : ℝ) : ℂ), ((c - k ^ 2 : ℝ) : ℂ), ((c : ℝ) : ℂ), ((c - α ^ 2 : ℝ) : ℂ)] :
      Fin 4 → ℂ) ∈ Carlson.carlsonRSlitDomain := by
    intro i; fin_cases i <;> simp only [Fin.isValue, Fin.zero_eta,
      Matrix.cons_val_zero, Fin.mk_one, Matrix.cons_val_one] <;>
      exact ofReal_mem_slitPlane.mpr (by linarith)
  rw [symmetricEllipticR_eq_integral (a' := (a' : ℂ)) (by simpa using ha) (by simpa using ha')
    (by simp [Fin.sum_univ_four]; ring) hz]
  congr 1
  set f : ℝ → ℝ := fun θ => 1 / Real.sin θ ^ 2 - c with hf
  set f' : ℝ → ℝ := fun θ => -(2 * Real.cos θ / Real.sin θ ^ 3) with hf'
  have hsinpos : ∀ θ ∈ Ioo 0 φ, 0 < Real.sin θ := fun θ hθ =>
    Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hsinlt : ∀ θ ∈ Ioo 0 φ, Real.sin θ < Real.sin φ := fun θ hθ =>
    Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [hθ.1]) hφ'.le hθ.2
  have hderiv : ∀ θ ∈ Ioo 0 φ, HasDerivWithinAt f (f' θ) (Ioo 0 φ) θ := by
    intro θ hθ
    have h0 := (hsinpos θ hθ).ne'
    have H := (((Real.hasDerivAt_sin θ).pow 2).inv (pow_ne_zero 2 h0)).sub_const c
    refine (H.congr_deriv ?_).hasDerivWithinAt.congr (fun x _ => ?_) ?_
    · simp only [hf', Pi.pow_apply]; field_simp; ring
    · simp only [hf, one_div, Pi.inv_apply, Pi.pow_apply]
    · simp only [hf, one_div, Pi.inv_apply, Pi.pow_apply]
  have hinj : InjOn f (Ioo 0 φ) := by
    intro x hx y hy hxy
    simp only [hf, sub_left_inj, one_div] at hxy
    have hx0 := hsinpos x hx
    have hy0 := hsinpos y hy
    have h2 : Real.sin x ^ 2 = Real.sin y ^ 2 := by
      have := congrArg (·⁻¹) hxy; simpa using this
    have h3 : Real.sin x = Real.sin y := by
      nlinarith [sq_nonneg (Real.sin x - Real.sin y), sq_nonneg (Real.sin x + Real.sin y)]
    exact Real.injOn_sin ⟨by linarith [hx.1], by linarith [hx.2]⟩
      ⟨by linarith [hy.1], by linarith [hy.2]⟩ h3
  have himg : f '' Ioo 0 φ = Ioi 0 := by
    ext t
    constructor
    · rintro ⟨θ, hθ, rfl⟩
      have hs := hsinpos θ hθ
      have hsS := hsinlt θ hθ
      show 0 < 1 / Real.sin θ ^ 2 - c
      simp only [c]
      rw [sub_pos]
      exact one_div_lt_one_div_of_lt (by positivity) (by nlinarith)
    · intro ht
      have ht0 : 0 < t := ht
      have hc0 : 0 < c := by linarith
      set u := 1 / (t + c) with hu
      have hu0 : 0 < u := by positivity
      have huS : u < Real.sin φ ^ 2 := by
        rw [hu, div_lt_iff₀ (by linarith)]
        have : Real.sin φ ^ 2 * c = 1 := by simp only [c]; field_simp
        nlinarith
      have hsq : Real.sqrt u < Real.sin φ := by
        rw [Real.sqrt_lt' hS]; exact huS
      have hsq0 : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu0
      refine ⟨Real.arcsin (Real.sqrt u), ⟨Real.arcsin_pos.mpr hsq0, ?_⟩, ?_⟩
      · have h1 : Real.arcsin (Real.sin φ) = φ :=
          Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith)
        rw [← h1]
        exact Real.arcsin_lt_arcsin (by linarith) hsq (by linarith)
      · show 1 / Real.sin (Real.arcsin (Real.sqrt u)) ^ 2 - c = t
        rw [Real.sin_arcsin (by linarith) (by linarith), Real.sq_sqrt hu0.le, hu]
        field_simp
        ring
  rw [← himg, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj,
    intervalIntegral.integral_of_le hφ.le, integral_Ioc_eq_integral_Ioo, ofReal_mul,
    ← integral_complex_ofReal, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo fun θ hθ => ?_
  have hs := hsinpos θ hθ
  have hsS := hsinlt θ hθ
  have hC : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩
  have hss : Real.sin θ ^ 2 < Real.sin φ ^ 2 := by nlinarith
  have hfθ : f θ = (Real.sin φ ^ 2 - Real.sin θ ^ 2) / (Real.sin θ ^ 2 * Real.sin φ ^ 2) := by
    simp only [hf, c]; field_simp
  have hft : 0 ≤ f θ := by rw [hfθ]; exact div_nonneg (by linarith) (by positivity)
  have hk' : 0 < 1 - k ^ 2 * Real.sin θ ^ 2 := by nlinarith [sq_nonneg k]
  have hα' : 0 < 1 - α ^ 2 * Real.sin θ ^ 2 := by nlinarith [sq_nonneg α]
  have key := sin_subst_identity (a := a) (a' := a') (b₁ := b₁) (b₂ := b₂) (b₄ := b₄)
    (S2 := Real.sin φ ^ 2) hs hC (by rw [Real.cos_sq']) hss hk' hα'
  have habs : |f' θ| = 2 * Real.cos θ / Real.sin θ ^ 3 := by
    simp only [hf', abs_neg]; exact abs_of_pos (by positivity)
  have e1 : (f θ : ℂ) + ((c - 1 : ℝ) : ℂ) = ((1 / Real.sin θ ^ 2 - 1 : ℝ) : ℂ) := by
    simp only [hf]; push_cast; ring
  have e2 : (f θ : ℂ) + ((c - k ^ 2 : ℝ) : ℂ) = ((1 / Real.sin θ ^ 2 - k ^ 2 : ℝ) : ℂ) := by
    simp only [hf]; push_cast; ring
  have e3 : (f θ : ℂ) + ((c : ℝ) : ℂ) = ((1 / Real.sin θ ^ 2 : ℝ) : ℂ) := by
    simp only [hf]; push_cast; ring
  have e4 : (f θ : ℂ) + ((c - α ^ 2 : ℝ) : ℂ) = ((1 / Real.sin θ ^ 2 - α ^ 2 : ℝ) : ℂ) := by
    simp only [hf]; push_cast; ring
  have hs2 : 0 < 1 / Real.sin θ ^ 2 := by positivity
  simp only [Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  rw [e1, e2, e3, e4,
    show -((a : ℂ) + a' - b₁ - b₂ - b₄) = ((-(a + a' - b₁ - b₂ - b₄) : ℝ) : ℂ) by push_cast; ring,
    ← ofReal_neg, ← ofReal_neg, ← ofReal_neg, ← ofReal_one, ← ofReal_sub,
    ← ofReal_cpow hft, ← ofReal_cpow (by linarith), ← ofReal_cpow (by nlinarith),
    ← ofReal_cpow hs2.le, ← ofReal_cpow (by nlinarith), real_smul, habs, hfθ]
  norm_cast
  linear_combination key


/-- DLMF 19.16.19: when one variable is `0` "without destroying convergence",
`R_{-a}(b₁, …, bₙ; 0, z₂, …, zₙ) = B(a, a' - b₁)/B(a, a') · R_{-a}(b₂, …, bₙ; z₂, …, zₙ)`,
for `a + a' > 0`, `a' > b₁`, written with the Beta ratio as the Gamma quotient
`Γ(a' - b₁) Γ(a + a') / (Γ(a') Γ(a + a' - b₁))` (the factor `Γ(a)` cancels, which gives the
meaning for `a ≤ 0`, e.g. `R_G`). Real parameters as in DLMF; the left side is the limit from the
slit domain (`symmetricEllipticR`). We also assume `∑_{j ≥ 2} bⱼ = a + a' - b₁ > 0`, so that the
right side is a genuine (non-totalized) value. -/
@[dlmf 19.16.E19]
theorem symmetricEllipticR_cons_zero {n : ℕ} {a b₁ : ℝ} {b : Fin n → ℝ} {z : Fin n → ℂ}
    (hz : z ∈ Carlson.carlsonRSlitDomain)
    (h₁ : 0 < a + (-a + b₁ + ∑ i, b i)) (h₂ : b₁ < -a + b₁ + ∑ i, b i)
    (h₃ : 0 < ∑ i, b i) :
    let a' : ℝ := -a + b₁ + ∑ i, b i
    symmetricEllipticR (a : ℂ) (Fin.cons (b₁ : ℂ) fun i => (b i : ℂ)) (Fin.cons 0 z) =
      Gamma ((a' - b₁ : ℝ) : ℂ) * Gamma ((a + a' : ℝ) : ℂ) /
          (Gamma (a' : ℂ) * Gamma ((a + a' - b₁ : ℝ) : ℂ)) *
        symmetricEllipticR (a : ℂ) (fun i => (b i : ℂ)) z := by
  sorry

/-- `R_E(y, z) = z R_K(y, z) + (1/2) z (y - z) R_{-3/2}(1/2, 3/2; y, z)` (Carlson's notation,
`lean-codes`), from the contiguous relation `regR2_raise₁` and Table 9.3-2, row 3. -/
private lemma carlsonRE_eq_carlsonRK_add {y z : ℂ} (hy : y ∈ slitPlane) (hz : z ∈ slitPlane) :
    Carlson.carlsonRE y z = z * Carlson.TwoVariable.carlsonRK y z +
      (1 / 2) * z * (y - z) * Carlson.carlsonR (-3 / 2) ![1 / 2, 3 / 2] ![y, z] := by
  have h3 := Carlson.carlsonR_table_9_3_2_row3 hy hz
  have hr := Carlson.regR2_raise₁ hy hz (-1 / 2) (1 / 2) (1 / 2)
  unfold Carlson.carlsonRE Carlson.TwoVariable.carlsonRK Carlson.carlsonR at *
  simp only [Carlson.TwoVariable.pair] at *
  norm_num [Fin.sum_univ_succ] at h3 hr ⊢
  linear_combination (1 / 2 : ℂ) * h3 + (y - z) * hr

/-- DLMF 19.16.23: `R_G(0, y, z) = (π/4) R_{1/2}(1/2, 1/2; y, z) = (π/4) z R_{-1/2}(-1/2, 3/2; y,
z)`, `y, z ∈ ℂ \ (-∞, 0]` (the last `R`-function has `a = a' = 1/2`). -/
@[dlmf 19.16.E23]
theorem symmetricEllipticRG_zero_left {y z : ℂ} (hy : y ∈ slitPlane) (hz : z ∈ slitPlane) :
    symmetricEllipticRG 0 y z = (π / 4) * symmetricEllipticR (-1 / 2) ![1 / 2, 1 / 2] ![y, z] ∧
      symmetricEllipticRG 0 y z = (π / 4) * z *
          symmetricEllipticR (1 / 2) ![-1 / 2, 3 / 2] ![y, z] := by
  have hRE : symmetricEllipticRG 0 y z = (π / 4) * Carlson.carlsonRE y z := by
    have h := two_mul_symmetricEllipticRG (Or.inr rfl) hy hz
    rw [symmetricEllipticRF_zero_left hy hz, symmetricEllipticRD_zero_left hy hz,
      symmetricEllipticR_of_mem _ _ (vec2_mem_carlsonRSlitDomain hy hz),
          symmetricEllipticR_of_mem _ _ (vec2_mem_carlsonRSlitDomain hy hz),
      zero_cpow (by norm_num : (1 / 2 : ℂ) ≠ 0), carlsonRE_eq_carlsonRK_add hy hz] at *
    unfold Carlson.TwoVariable.carlsonRK Carlson.TwoVariable.pair
    rw [show (-(1 / 2) : ℂ) = -1 / 2 by ring, show (-(3 / 2) : ℂ) = -3 / 2 by ring] at h
    linear_combination (1 / 2 : ℂ) * h
  refine ⟨?_, ?_⟩
  · rw [hRE, symmetricEllipticR_of_mem _ _ (vec2_mem_carlsonRSlitDomain hy hz)]
    unfold Carlson.carlsonRE Carlson.TwoVariable.pair
    congr 2; ring
  · have h1 := Carlson.carlsonR_table_9_3_2_row1 hy hz
    rw [hRE, symmetricEllipticR_of_mem _ _ (vec2_mem_carlsonRSlitDomain hy hz), show -(1 / 2 : ℂ) =
        -1 / 2 by ring]
    linear_combination (-(π / 4 : ℂ)) * h1

/-- DLMF 19.16.24: the incomplete integral recovered from the complete one,
`R_{-a}(𝐛; 𝐳) = z₁^{a'-b₁}/B(b₁, a'-b₁) ∫₀^∞ t^{b₁-1} (t + z₁)^{-a'}
R_{-a}(𝐛; 0, t + z₂, …, t + zₙ) dt`, for `a' > b₁`, `a + a' > b₁ > 0`, real parameters and
slit-plane nodes. -/
@[dlmf 19.16.E24]
theorem symmetricEllipticR_eq_integral_complete {n : ℕ} {a b₁ : ℝ} {b : Fin n → ℝ} {z₁ : ℂ}
    {z : Fin n → ℂ} (hz₁ : z₁ ∈ slitPlane) (hz : z ∈ Carlson.carlsonRSlitDomain)
    (h₁ : b₁ < -a + b₁ + ∑ i, b i) (h₂ : b₁ < a + (-a + b₁ + ∑ i, b i)) (h₃ : 0 < b₁) :
    let a' : ℝ := -a + b₁ + ∑ i, b i
    symmetricEllipticR (a : ℂ) (Fin.cons (b₁ : ℂ) fun i => (b i : ℂ)) (Fin.cons z₁ z) =
      z₁ ^ ((a' - b₁ : ℝ) : ℂ) * (betaIntegral b₁ ((a' - b₁ : ℝ) : ℂ))⁻¹ *
        ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ ((b₁ - 1 : ℝ) : ℂ) * ((t : ℂ) + z₁) ^ (-(a' : ℂ)) *
          symmetricEllipticR (a : ℂ) (Fin.cons (b₁ : ℂ) fun i => (b i : ℂ))
            (Fin.cons 0 fun i => (t : ℂ) + z i) := by
  sorry

end DLMF.EllipticIntegrals
