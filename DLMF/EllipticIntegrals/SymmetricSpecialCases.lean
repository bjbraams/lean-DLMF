/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.EllipticIntegrals.SymmetricSeries
public import DLMF.EllipticIntegrals.SymmetricRelations

/-!
# Symmetric elliptic integrals: special cases (DLMF §19.20)

Special values, homogeneity, degenerate cases, limits and principal values of `R_F`, `R_G`,
`R_J`, `R_D` and of `R_{-a}(𝐛; 𝐳)` (§19.20(i)–(v)). As DLMF says (19.20.i.p1), the variables
satisfy the constraints of §19.16(i) unless stated otherwise; we state them explicitly
(slit-plane membership, admissible zeros, real variables where DLMF uses real ones, e.g. for
Cauchy principal values). Homogeneity is stated for real `λ > 0` (for complex `λ` see
`symEllIntR_mul`). "`= ∞`" is formalized as non-integrability of the defining integrand,
"`→ +∞`" as `Tendsto … atTop` of the (real) value.

Decimal values of the lemniscate constants (19.20.2), (19.20.22) are excluded: numerical.

**Domain corrections.** The lemniscatic cases (19.20.3), (19.20.23) are stated for real positive
`x, y`; with complex arguments they fail without a branch condition (numerically, at
`x = -1 + 0.3i`, `y = 2 + i` the two sides differ by a factor `-i`).
-/

@[expose] public noncomputable section

open Complex Set Filter MeasureTheory Asymptotics
open scoped Real Topology

namespace DLMF.EllipticIntegrals

lemma ei19c_smul_mem_slitPlane {l : ℝ} (hl : 0 < l) {x : ℂ} (hx : x ∈ slitPlane) :
    (l : ℂ) * x ∈ slitPlane := by
  rcases mem_slitPlane_iff.mp hx with h | h
  · exact mem_slitPlane_iff.mpr (Or.inl (by simp; positivity))
  · exact mem_slitPlane_iff.mpr (Or.inr (by simp [hl.ne', h]))

lemma ei19c_arg_ofReal_add {l : ℝ} (hl : 0 < l) {x : ℂ} (hx : x ∈ slitPlane) :
    arg (l : ℂ) + arg x ∈ Ioo (-π) π := by
  rw [arg_ofReal_of_nonneg hl.le, zero_add]
  exact ⟨neg_pi_lt_arg _, lt_of_le_of_ne (arg_le_pi _) (mem_slitPlane_iff_arg.mp hx).1⟩

lemma ei19c_symEllIntR_smul {ι : Type*} [Fintype ι] (a : ℂ) (b : ι → ℂ) {l : ℝ} (hl : 0 < l)
    {z : ι → ℂ} (hz : z ∈ Carlson.carlsonRSlitDomain) :
    symEllIntR a b (fun i => (l : ℂ) * z i) = (l : ℂ) ^ (-a) * symEllIntR a b z :=
  symEllIntR_mul a b hz (ofReal_mem_slitPlane.mpr hl) fun i => ei19c_arg_ofReal_add hl (hz i)

/-! ### §19.20(i) `R_F` -/

/-- DLMF 19.20.1 (first): `R_F(x, x, x) = x^{-1/2}`, `x ∈ ℂ \ (-∞, 0]`. -/
@[dlmf 19.20.E1]
theorem symEllIntRF_self {x : ℂ} (hx : x ∈ slitPlane) : symEllIntRF x x x = x ^ (-1 / 2 : ℂ) := by
  rw [symEllIntRF_eq_carlsonRF hx hx hx, Carlson.carlsonRF_self hx]

/-- DLMF 19.20.1 (second): `R_F(λx, λy, λz) = λ^{-1/2} R_F(x, y, z)`, `λ > 0`. -/
@[dlmf 19.20.E1]
theorem symEllIntRF_smul {l : ℝ} (hl : 0 < l) {x y z : ℂ} (hx : x ∈ slitPlane)
    (hy : y ∈ slitPlane) (hz : z ∈ slitPlane) :
    symEllIntRF (l * x) (l * y) (l * z) = (l : ℂ) ^ (-1 / 2 : ℂ) * symEllIntRF x y z := by
  rw [symEllIntRF_eq_symEllIntR (ei19c_smul_mem_slitPlane hl hx) (ei19c_smul_mem_slitPlane hl hy)
    (ei19c_smul_mem_slitPlane hl hz), symEllIntRF_eq_symEllIntR hx hy hz]
  have : (![(l : ℂ) * x, l * y, l * z] : Fin 3 → ℂ) = fun i => (l : ℂ) * ![x, y, z] i := by
    funext i; fin_cases i <;> rfl
  rw [this, ei19c_symEllIntR_smul _ _ hl (ei19c_slit3 hx hy hz)]
  congr 2; ring

/-- DLMF 19.20.1 (third): `R_F(x, y, y) = R_C(x, y)` (for every `x` and `y` not a negative real;
see `symEllIntRC_eq_symEllIntRF`). -/
@[dlmf 19.20.E1]
theorem symEllIntRF_self_right (x : ℂ) {y : ℂ} (hy : ¬ IsNegReal y) :
    symEllIntRF x y y = symEllIntRC x y :=
  (symEllIntRC_eq_symEllIntRF x hy).symm

/-- DLMF 19.20.1 (fourth): `R_F(0, y, y) = (π/2) y^{-1/2}`, `y ∈ ℂ \ (-∞, 0]`. -/
@[dlmf 19.20.E1]
theorem symEllIntRF_zero_self {y : ℂ} (hy : y ∈ slitPlane) :
    symEllIntRF 0 y y = (π / 2) * y ^ (-1 / 2 : ℂ) := by
  rw [symEllIntRF_zero_left hy hy]
  have : (![y, y] : Fin 2 → ℂ) = fun _ => y := by funext i; fin_cases i <;> rfl
  rw [this, symEllIntR_const _ _ hy (Complex.Gamma_ne_zero_of_re_pos (by simp))]
  congr 2; ring

/-- DLMF 19.20.1 (fifth): `R_F(0, 0, z) = ∞`: the defining integrand is not integrable. -/
@[dlmf 19.20.E1]
theorem not_integrableOn_symEllIntRF_zero_zero {z : ℂ} (hz : z ∈ slitPlane) :
    ¬ IntegrableOn (fun t => (symEllIntS 0 0 z t)⁻¹) (Ioi 0) :=
  p19sR1_not_integrableOn_zero_zero' hz

/-- DLMF 19.20.2: the first lemniscate constant
`∫₀¹ dt/√(1 - t⁴) = R_F(0, 1, 2) = Γ(1/4)² / (4 (2π)^{1/2})` (decimal value excluded: numerical). -/
@[dlmf 19.20.E2]
theorem lemniscate_first_symEllIntRF :
    ((∫ t in (0 : ℝ)..1, 1 / Real.sqrt (1 - t ^ 4) : ℝ) : ℂ) = symEllIntRF 0 1 2 ∧
      symEllIntRF 0 1 2 = ((Real.Gamma (1 / 4) ^ 2 / (4 * Real.sqrt (2 * π)) : ℝ) : ℂ) := by
  rw [p19sR1_symEllIntRF_zero_one_two, DLMF.Elliptic.integral_recip_sqrt_one_sub_pow_four]
  exact ⟨rfl, rfl⟩

/-- DLMF 19.20.3 (general lemniscatic case), **domain-restricted** to real `x, y > 0`:
`R_F(x, a, y) = R_{-1/4}(3/4, 1/2; a², xy)`, `a = (x + y)/2`. -/
@[dlmf 19.20.E3 "domain-restricted: real positive x, y; see the complex form for Re x, Re y > 0"]
theorem symEllIntRF_lemniscatic {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    symEllIntRF x ((x + y) / 2 : ℝ) y =
      symEllIntR (1 / 4) ![3 / 4, 1 / 2] ![((((x + y) / 2) ^ 2 : ℝ) : ℂ), ((x * y : ℝ) : ℂ)] := by
  sorry

/-- DLMF 19.20.3, corrected complex form: `R_F(x, a, y) = R_{-1 / 4}(3 / 4, 1/2; a², xy)`, `a = (x + y)/2`, for complex
`x, y` with `ℜ x > 0` and `ℜ y > 0`. **Corrected from the printed DLMF formula**: DLMF states it
under the 19.16(i) constraints only, but it fails there, e.g. at `x = -1 + i`, `y = -1 + 2i` the
two sides differ by a factor `±i` (independent mpmath check, 2026-10-25). -/
@[dlmf 19.20.E3 "corrected: complex x, y with Re x, Re y > 0"]
theorem symEllIntRF_lemniscatic_complex {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) :
    symEllIntRF x ((x + y) / 2) y =
      symEllIntR (1 / 4) ![3 / 4, 1 / 2] ![((x + y) / 2) ^ 2, x * y] := by
  sorry

/-! ### §19.20(ii) `R_G` -/

/-- DLMF 19.20.4 (first): `R_G(x, x, x) = x^{1/2}`. -/
@[dlmf 19.20.E4]
theorem symEllIntRG_self {x : ℂ} (hx : x ∈ slitPlane) : symEllIntRG x x x = x ^ (1 / 2 : ℂ) := by
  rw [symEllIntRG_eq_symEllIntR hx hx hx]
  have : (![x, x, x] : Fin 3 → ℂ) = fun _ => x := by funext i; fin_cases i <;> rfl
  rw [this, symEllIntR_const _ _ hx (Complex.Gamma_ne_zero_of_re_pos (by simp))]
  congr 1; ring

/-- DLMF 19.20.4 (second): `R_G(λx, λy, λz) = λ^{1/2} R_G(x, y, z)`, `λ > 0`. -/
@[dlmf 19.20.E4]
theorem symEllIntRG_smul {l : ℝ} (hl : 0 < l) {x y z : ℂ} (hx : x ∈ slitPlane)
    (hy : y ∈ slitPlane) (hz : z ∈ slitPlane) :
    symEllIntRG (l * x) (l * y) (l * z) = (l : ℂ) ^ (1 / 2 : ℂ) * symEllIntRG x y z := by
  rw [symEllIntRG_eq_symEllIntR (ei19c_smul_mem_slitPlane hl hx) (ei19c_smul_mem_slitPlane hl hy)
    (ei19c_smul_mem_slitPlane hl hz), symEllIntRG_eq_symEllIntR hx hy hz]
  have : (![(l : ℂ) * x, l * y, l * z] : Fin 3 → ℂ) = fun i => (l : ℂ) * ![x, y, z] i := by
    funext i; fin_cases i <;> rfl
  rw [this, ei19c_symEllIntR_smul _ _ hl (ei19c_slit3 hx hy hz)]
  congr 2; ring

/-- `∫₀^∞ dt / ((t + z)^{1/2} (t + z)) = 2 z^{-1/2}` for `z ∈ ℂ \ (-∞, 0]`. -/
lemma p19sR1_integral_inv_cpow_half_mul {z : ℂ} (hz : z ∈ slitPlane) :
    ∫ t in Ioi (0 : ℝ), (((t : ℂ) + z) ^ (1 / 2 : ℂ) * ((t : ℂ) + z))⁻¹ =
      2 * (z ^ (1 / 2 : ℂ))⁻¹ := by
  obtain ⟨c1, hc1, h1⟩ := p19sR1_norm_cpow_half_ge hz
  obtain ⟨c2, hc2, h2⟩ := p19sR1_norm_add_ge hz
  have hz' : ∀ t : ℝ, 0 ≤ t → (t : ℂ) + z ∈ slitPlane := fun t ht => by
    rcases ht.eq_or_lt with rfl | ht
    · simpa using hz
    · exact p19sR1_add_mem_slitPlane ht (Or.inl hz)
  have hint : IntegrableOn (fun t : ℝ => (((t : ℂ) + z) ^ (1 / 2 : ℂ) * ((t : ℂ) + z))⁻¹)
      (Ioi 0) := by
    refine p19sR1_integrableOn_of_le (C := (c1 * c2)⁻¹) ?_ fun t ht => ?_
    · refine ((p19sR1_continuousOn_cpow_half (Or.inl hz)).mul
        (continuous_ofReal.add continuous_const).continuousOn).inv₀ fun t ht => ?_
      exact mul_ne_zero (p19sR1_cpow_half_ne_zero ht (Or.inl hz))
        (slitPlane_ne_zero (p19sR1_add_mem_slitPlane ht (Or.inl hz)))
    · have a1 := h1 t ht.le
      have a2 := h2 t ht.le
      have hs : Real.sqrt t ≤ Real.sqrt (t + 1) := Real.sqrt_le_sqrt (by linarith)
      have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
      rw [norm_inv, norm_mul, ← mul_inv]
      have hp : 0 < ‖((t : ℂ) + z) ^ (1 / 2 : ℂ)‖ * ‖(t : ℂ) + z‖ :=
        mul_pos (lt_of_lt_of_le (by positivity) a1) (lt_of_lt_of_le (by positivity) a2)
      rw [inv_le_inv₀ hp (by positivity)]
      calc c1 * c2 * (Real.sqrt t * (t + 1)) = (c1 * Real.sqrt t) * (c2 * (t + 1)) := by ring
        _ ≤ (c1 * Real.sqrt (t + 1)) * (c2 * (t + 1)) := by gcongr
        _ ≤ _ := mul_le_mul a1 a2 (by positivity) (norm_nonneg _)
  have hderiv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt (fun s : ℝ => -2 * (((s : ℂ) + z) ^ (1 / 2 : ℂ))⁻¹)
      ((((t : ℂ) + z) ^ (1 / 2 : ℂ) * ((t : ℂ) + z))⁻¹) t := by
    intro t ht
    have h := ((p19sR1_hasDerivAt_cpow_half (hz' t (le_of_lt ht))).inv
      (p19sR1_cpow_half_ne_zero ht (Or.inl hz))).const_mul (-2 : ℂ)
    convert h using 1
    have hu0 := p19sR1_cpow_half_ne_zero ht (Or.inl hz)
    have hw0 := slitPlane_ne_zero (p19sR1_add_mem_slitPlane ht (Or.inl hz))
    field_simp
  have hcont : ContinuousWithinAt (fun s : ℝ => -2 * (((s : ℂ) + z) ^ (1 / 2 : ℂ))⁻¹) (Ici 0) 0 :=
    (continuousAt_const.mul ((p19sR1_continuousAt_cpow_half (hz' 0 le_rfl)).inv₀
      (p19sR1_cpow_half_ne_zero_of_mem (hz' 0 le_rfl)))).continuousWithinAt
  have hlim : Tendsto (fun s : ℝ => -2 * (((s : ℂ) + z) ^ (1 / 2 : ℂ))⁻¹) atTop (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun t => 2 * (c1 * Real.sqrt (t + 1))⁻¹) ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with t ht
      have a1 := h1 t ht.le
      rw [norm_mul, norm_inv, norm_neg, Complex.norm_ofNat]
      gcongr
    · have : Tendsto (fun t : ℝ => Real.sqrt (t + 1)) atTop atTop :=
        Real.tendsto_sqrt_atTop.comp (tendsto_atTop_add_const_right _ 1 tendsto_id)
      simpa using ((this.const_mul_atTop hc1).inv_tendsto_atTop).const_mul 2
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim]
  simp

/-- DLMF 19.20.4 (third and fourth): `R_G(0, y, y) = (π/4) y^{1/2}` and
`R_G(0, 0, z) = (1/2) z^{1/2}`, `y, z ∈ ℂ \ (-∞, 0]`. -/
@[dlmf 19.20.E4]
theorem symEllIntRG_zero_self {y z : ℂ} (hy : y ∈ slitPlane) (hz : z ∈ slitPlane) :
    symEllIntRG 0 y y = (π / 4) * y ^ (1 / 2 : ℂ) ∧
      symEllIntRG 0 0 z = (1 / 2) * z ^ (1 / 2 : ℂ) := by
  refine ⟨?_, ?_⟩
  · rw [(symEllIntRG_zero_left hy hy).1]
    have : (![y, y] : Fin 2 → ℂ) = fun _ => y := by funext i; fin_cases i <;> rfl
    rw [this, symEllIntR_const _ _ hy (Complex.Gamma_ne_zero_of_re_pos (by simp))]
    congr 2; ring
  · have hI := p19sR1_integral_inv_cpow_half_mul hz
    have e : ∀ t ∈ Ioi (0 : ℝ), (symEllIntS 0 0 z t)⁻¹ *
        (0 / ((t : ℂ) + 0) + 0 / ((t : ℂ) + 0) + z / ((t : ℂ) + z)) * t =
        z * (((t : ℂ) + z) ^ (1 / 2 : ℂ) * ((t : ℂ) + z))⁻¹ := by
      intro t ht
      have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht)
      simp only [symEllIntS, add_zero, zero_div, zero_add]
      rw [ei19c_cpow_half_sq]
      have hu0 := p19sR1_cpow_half_ne_zero ht (Or.inl hz)
      have hw0 := slitPlane_ne_zero (p19sR1_add_mem_slitPlane ht (Or.inl hz))
      field_simp
    rw [symEllIntRG, setIntegral_congr_fun measurableSet_Ioi e, integral_const_mul, hI]
    have hz0 := p19sR1_cpow_half_ne_zero_of_mem hz
    have hsq := ei19c_cpow_half_sq z
    field_simp
    linear_combination (-4 : ℂ) * hsq

/-- DLMF 19.20.5: `2 R_G(x, y, y) = y R_C(x, y) + √x`, `x` admissible, `y ∈ ℂ \ (-∞, 0]`. -/
@[dlmf 19.20.E5]
theorem two_mul_symEllIntRG_self_right {x y : ℂ} (hx : symEllIntArg x) (hy : y ∈ slitPlane) :
    2 * symEllIntRG x y y = y * symEllIntRC x y + x ^ (1 / 2 : ℂ) := by
  rw [p19sR1_two_mul_symEllIntRG hx hy hy, symEllIntRC_eq_symEllIntRF x
    (ei19c_not_isNegReal_of_mem_slitPlane hy)]
  have hy0 : y ^ (1 / 2 : ℂ) ≠ 0 := p19sR1_cpow_half_ne_zero_of_mem hy
  rw [show (-1 / 2 : ℂ) = -(1 / 2) by ring, cpow_neg]
  field_simp
  ring

/-! ### §19.20(iii) `R_J` -/

/-- DLMF 19.20.6 (first): `R_J(x, x, x, x) = x^{-3/2}`. -/
@[dlmf 19.20.E6]
theorem symEllIntRJ_self {x : ℂ} (hx : x ∈ slitPlane) :
    symEllIntRJ x x x x = x ^ (-3 / 2 : ℂ) := by
  rw [symEllIntRJ_eq_symEllIntR hx hx hx hx]
  have : (![x, x, x, x] : Fin 4 → ℂ) = fun _ => x := by funext i; fin_cases i <;> rfl
  have hG : Gamma (∑ i, (![1 / 2, 1 / 2, 1 / 2, 1] : Fin 4 → ℂ) i) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simp [Fin.sum_univ_four]; norm_num)
  rw [this, symEllIntR_const _ _ hx hG]
  congr 1; ring

/-- DLMF 19.20.6 (second): `R_J(λx, λy, λz, λp) = λ^{-3/2} R_J(x, y, z, p)`, `λ > 0`
(slit-plane variables). -/
@[dlmf 19.20.E6]
theorem symEllIntRJ_smul {l : ℝ} (hl : 0 < l) {x y z p : ℂ} (hx : x ∈ slitPlane)
    (hy : y ∈ slitPlane) (hz : z ∈ slitPlane) (hp : p ∈ slitPlane) :
    symEllIntRJ (l * x) (l * y) (l * z) (l * p) = (l : ℂ) ^ (-3 / 2 : ℂ) * symEllIntRJ x y z p := by
  rw [symEllIntRJ_eq_symEllIntR (ei19c_smul_mem_slitPlane hl hx) (ei19c_smul_mem_slitPlane hl hy)
    (ei19c_smul_mem_slitPlane hl hz) (ei19c_smul_mem_slitPlane hl hp),
    symEllIntRJ_eq_symEllIntR hx hy hz hp]
  have : (![(l : ℂ) * x, l * y, l * z, l * p] : Fin 4 → ℂ) =
      fun i => (l : ℂ) * ![x, y, z, p] i := by
    funext i; fin_cases i <;> rfl
  rw [this, ei19c_symEllIntR_smul _ _ hl (ei19c_slit4 hx hy hz hp)]
  congr 2; ring

/-- DLMF 19.20.6 (third) and 19.20.8 (fourth): `R_J(x, y, z, z) = R_D(x, y, z)` (definitional). -/
@[dlmf 19.20.E6, dlmf 19.20.E8]
theorem symEllIntRJ_self_right (x y z : ℂ) : symEllIntRJ x y z z = symEllIntRD x y z := rfl

/-- DLMF 19.20.6 (fourth): `R_J(0, 0, z, p) = ∞`: the defining integrand is not integrable. -/
@[dlmf 19.20.E6]
theorem not_integrableOn_symEllIntRJ_zero_zero {z p : ℂ} (hz : z ∈ slitPlane)
    (hp : p ∈ slitPlane) :
    ¬ IntegrableOn (fun t => (symEllIntS 0 0 z t * ((t : ℂ) + p))⁻¹) (Ioi 0) :=
  p19sR1_not_integrableOn_zero_zero hz hp

/-- DLMF 19.20.6 (fifth, first equality): `R_J(x, x, x, p) = R_D(p, p, x)`, for `x, p` not
negative reals (stronger than DLMF: no further condition; the integrands agree). -/
@[dlmf 19.20.E6]
theorem symEllIntRJ_self_self_self (p : ℂ) {x : ℂ} (hx : ¬ IsNegReal x) (hp : ¬ IsNegReal p) :
    symEllIntRJ x x x p = symEllIntRD p p x := by
  simp only [symEllIntRD, symEllIntRJ, hx, hp, ↓reduceIte, symEllIntS]
  congr 2; funext t
  rw [mul_assoc (((t : ℂ) + x) ^ (1 / 2 : ℂ)), ei19c_cpow_half_sq,
    ei19c_cpow_half_sq ((t : ℂ) + p)]
  ring

/-- DLMF 19.20.6 (fifth, second equality): `R_J(x, x, x, p) = 3/(x - p) (R_C(x, p) - 1/√x)`,
`x ≠ p`, `xp ≠ 0`; `x ∈ ℂ \ (-∞, 0]`, `p ∈ ℂ \ (-∞, 0]` (principal-value case: see 19.20.8). -/
@[dlmf 19.20.E6]
theorem symEllIntRJ_self_self_self_eq {x p : ℂ} (hx : x ∈ slitPlane) (hp : p ∈ slitPlane)
    (hxp : x ≠ p) :
    symEllIntRJ x x x p = 3 / (x - p) * (symEllIntRC x p - 1 / x ^ (1 / 2 : ℂ)) := by
  rw [symEllIntRJ_self_self_self p (ei19c_not_isNegReal_of_mem_slitPlane hx)
    (ei19c_not_isNegReal_of_mem_slitPlane hp)]
  exact p19sR1_symEllIntRD_self_left hp hx (Ne.symm hxp)

/-- DLMF 19.20.7: `R_J(x, y, z, p) → +∞` as `p → 0±`, for `x, y, z > 0` (for `p < 0` the
principal value). -/
@[dlmf 19.20.E7]
theorem tendsto_symEllIntRJ_zero {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    Tendsto (fun p : ℝ => (symEllIntRJ x y z p).re) (𝓝[≠] 0) atTop := by
  sorry

/-- DLMF 19.20.8 (first): `R_J(0, y, y, p) = 3π / (2(y√p + p√y))`, `p > 0`, `y ∈ ℂ \ (-∞, 0]`. -/
@[dlmf 19.20.E8]
theorem symEllIntRJ_zero_self_self {y : ℂ} (hy : y ∈ slitPlane) {p : ℝ} (hp : 0 < p) :
    symEllIntRJ 0 y y p = 3 * π / (2 * (y * (p : ℂ) ^ (1 / 2 : ℂ) + p * y ^ (1 / 2 : ℂ))) := by
  have hp' : (p : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr hp
  have e : ∀ w : ℂ, w ^ (-1 / 2 : ℂ) = (w ^ (1 / 2 : ℂ))⁻¹ := fun w => by
    rw [show (-1 / 2 : ℂ) = -(1 / 2) by ring, cpow_neg]
  have hRC : ∀ w : ℂ, w ∈ slitPlane → symEllIntRC 0 w = (π / 2) * (w ^ (1 / 2 : ℂ))⁻¹ :=
    fun w hw => by
      rw [← symEllIntRF_self_right 0 (ei19c_not_isNegReal_of_mem_slitPlane hw),
        symEllIntRF_zero_self hw, e]
  have hY0 := p19sR1_cpow_half_ne_zero_of_mem hy
  have hP0 := p19sR1_cpow_half_ne_zero_of_mem hp'
  have hY2 := p19sR1_cpow_half_sq y
  have hP2 := p19sR1_cpow_half_sq (p : ℂ)
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  by_cases hpy : (p : ℂ) = y
  · have hD : symEllIntRD 0 (p : ℂ) p = (3 * π / 4) * (p : ℂ) ^ (-3 / 2 : ℂ) := by
      rw [symEllIntRD_zero_left hp' hp']
      have : (![(p : ℂ), p] : Fin 2 → ℂ) = fun _ => (p : ℂ) := by funext i; fin_cases i <;> rfl
      rw [this, symEllIntR_const _ _ hp' (Complex.Gamma_ne_zero_of_re_pos (by simp; norm_num))]
      congr 2; ring
    rw [← hpy, symEllIntRJ_self_right, hD]
    rw [show (-3 / 2 : ℂ) = -(1 / 2) + (-1) by norm_num, cpow_add _ _ (slitPlane_ne_zero hp'),
      cpow_neg_one, cpow_neg]
    have hp0 : (p : ℂ) ≠ 0 := slitPlane_ne_zero hp'
    field_simp
    ring
  · rw [p19sR1_symEllIntRJ_self_right_eq (Or.inr rfl) hy hp' hpy, hRC y hy, hRC _ hp']
    generalize y ^ (1 / 2 : ℂ) = Y at *
    generalize (p : ℂ) ^ (1 / 2 : ℂ) = P at *
    generalize (p : ℂ) = q at *
    subst hY2 hP2
    have h1 : P - Y ≠ 0 := fun h => hpy (by rw [sub_eq_zero.mp h])
    have h2 : P + Y ≠ 0 := fun h => hpy (by rw [eq_neg_of_add_eq_zero_left h]; ring)
    have h3 : P ^ 2 - Y ^ 2 ≠ 0 := by
      rw [show P ^ 2 - Y ^ 2 = (P - Y) * (P + Y) by ring]; exact mul_ne_zero h1 h2
    have h4 : Y ^ 2 * P + P ^ 2 * Y ≠ 0 := by
      rw [show Y ^ 2 * P + P ^ 2 * Y = Y * P * (P + Y) by ring]
      exact mul_ne_zero (mul_ne_zero hY0 hP0) h2
    rw [eq_div_iff (mul_ne_zero two_ne_zero h4)]
    field_simp
    rw [show P ^ 2 - Y ^ 2 = (P - Y) * (P + Y) by ring]
    field_simp
    ring

/-- DLMF 19.20.8 (second): `R_J(0, y, y, -q) = -3π / (2√y (y + q))`, `q > 0` (Cauchy principal
value), `y > 0`. -/
@[dlmf 19.20.E8]
theorem symEllIntRJ_zero_self_self_neg {y q : ℝ} (hy : 0 < y) (hq : 0 < q) :
    symEllIntRJ 0 y y (-q : ℝ) = -3 * π / (2 * (y : ℂ) ^ (1 / 2 : ℂ) * (y + q)) := by
  sorry

/-- DLMF 19.20.8 (third): `R_J(x, y, y, p) = 3/(p - y) (R_C(x, y) - R_C(x, p))`, `p ≠ y`,
for `x` admissible, `y, p ∈ ℂ \ (-∞, 0]`. -/
@[dlmf 19.20.E8]
theorem symEllIntRJ_self_right_eq {x y p : ℂ} (hx : symEllIntArg x) (hy : y ∈ slitPlane)
    (hp : p ∈ slitPlane) (hpy : p ≠ y) :
    symEllIntRJ x y y p = 3 / (p - y) * (symEllIntRC x y - symEllIntRC x p) :=
  p19sR1_symEllIntRJ_self_right_eq hx hy hp hpy

/-- DLMF 19.20.8 (third), principal-value case: real `x ≥ 0`, `y > 0`, `p < 0`. -/
@[dlmf 19.20.E8]
theorem symEllIntRJ_self_right_eq_of_neg {x y p : ℝ} (hx : 0 ≤ x) (hy : 0 < y) (hp : p < 0) :
    symEllIntRJ x y y p = 3 / ((p : ℂ) - y) * (symEllIntRC x y - symEllIntRC x p) := by
  sorry

/-- DLMF 19.20.9: `R_J(0, y, z, ±√(yz)) = ±3/(2√(yz)) R_F(0, y, z)`, `y, z > 0` (the lower sign
is a Cauchy principal value). -/
@[dlmf 19.20.E9]
theorem symEllIntRJ_zero_sqrt {y z : ℝ} (hy : 0 < y) (hz : 0 < z) :
    symEllIntRJ 0 y z (Real.sqrt (y * z) : ℝ) =
        3 / (2 * Real.sqrt (y * z) : ℝ) * symEllIntRF 0 y z ∧
      symEllIntRJ 0 y z (-Real.sqrt (y * z) : ℝ) =
        -(3 / (2 * Real.sqrt (y * z) : ℝ)) * symEllIntRF 0 y z := by
  sorry

/-- DLMF 19.20.10: `lim_{p→0+} √p R_J(0, y, z, p) = 3π/(2√y√z)` and
`lim_{p→0-} R_J(0, y, z, p) = -R_D(0, y, z) - R_D(0, z, y) = -6/(yz) R_G(0, y, z)`, for
`y, z > 0`. -/
@[dlmf 19.20.E10]
theorem tendsto_symEllIntRJ_zero_left {y z : ℝ} (hy : 0 < y) (hz : 0 < z) :
    Tendsto (fun p : ℝ => (Real.sqrt p : ℂ) * symEllIntRJ 0 y z p) (𝓝[>] 0)
        (𝓝 (3 * π / (2 * Real.sqrt y * Real.sqrt z) : ℝ)) ∧
      Tendsto (fun p : ℝ => symEllIntRJ 0 y z p) (𝓝[<] 0)
        (𝓝 (-symEllIntRD 0 y z - symEllIntRD 0 z y)) ∧
      -symEllIntRD 0 y z - symEllIntRD 0 z y = -6 / ((y : ℂ) * z) * symEllIntRG 0 y z := by
  sorry

/-- DLMF 19.20.11: `R_J(0, y, z, p) = 3/(2p√z) ln(16z/y) - (3/p) R_C(z, p) + O(y ln y)` as
`y → 0+`, for real `p ≠ 0` and `z > 0`. -/
@[dlmf 19.20.E11]
theorem symEllIntRJ_zero_asymptotic {z p : ℝ} (hz : 0 < z) (hp : p ≠ 0) :
    (fun y : ℝ => symEllIntRJ 0 y z p - ((3 / (2 * p * Real.sqrt z) * Real.log (16 * z / y) : ℝ) -
        3 / (p : ℂ) * symEllIntRC z p)) =O[𝓝[>] 0] fun y => ((y * Real.log y : ℝ) : ℂ) := by
  sorry

/-- DLMF 19.20.12: `lim_{p→±∞} p R_J(x, y, z, p) = 3 R_F(x, y, z)` (real `p`; for `p < 0` the
principal value), `x, y, z` in the domain of §19.16(i). -/
@[dlmf 19.20.E12]
theorem tendsto_mul_symEllIntRJ {x y z : ℂ} (h : symEllIntRFDomain x y z) :
    Tendsto (fun p : ℝ => (p : ℂ) * symEllIntRJ x y z p) atTop (𝓝 (3 * symEllIntRF x y z)) ∧
      Tendsto (fun p : ℝ => (p : ℂ) * symEllIntRJ x y z p) atBot (𝓝 (3 * symEllIntRF x y z)) := by
  sorry

/-- DLMF 19.20.13: `2(p - x) R_J(x, y, z, p) = 3 R_F(x, y, z) - 3√x R_C(yz, p²)` for
`p = x ± √((y - x)(z - x))`; real `x ≥ 0`, `y, z > 0` with `(y - x)(z - x) ≥ 0` and `p ≠ 0`
(principal value when `p < 0`; `x, y, z` may be permuted). -/
@[dlmf 19.20.E13]
theorem symEllIntRJ_special_p {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 < y) (hz : 0 < z)
    (hxyz : 0 ≤ (y - x) * (z - x)) {s : ℝ} (hs : s = 1 ∨ s = -1)
    (hp : x + s * Real.sqrt ((y - x) * (z - x)) ≠ 0) :
    let p : ℝ := x + s * Real.sqrt ((y - x) * (z - x))
    2 * ((p : ℂ) - x) * symEllIntRJ x y z p =
      3 * symEllIntRF x y z - 3 * (x : ℂ) ^ (1 / 2 : ℂ) * symEllIntRC (y * z) ((p : ℂ) ^ 2) := by
  sorry

/-- DLMF 19.20.14 with 19.20.15: the Cauchy principal value of `R_J`. For `0 ≤ x < y < z`,
`q > 0` and `p = (z(x + y + q) - xy)/(z + q)`,
`(q + z) R_J(x, y, z, -q) = (p - z) R_J(x, y, z, p) - 3 R_F(x, y, z)
  + 3 (xyz/(xy + pq))^{1/2} R_C(xy + pq, pq)`. -/
@[dlmf 19.20.E14, dlmf 19.20.E15]
theorem symEllIntRJ_principalValue {x y z q : ℝ} (hx : 0 ≤ x) (hxy : x < y) (hyz : y < z)
    (hq : 0 < q) :
    let p : ℝ := (z * (x + y + q) - x * y) / (z + q)
    ((q + z : ℝ) : ℂ) * symEllIntRJ x y z (-q : ℝ) =
      ((p - z : ℝ) : ℂ) * symEllIntRJ x y z p - 3 * symEllIntRF x y z +
        3 * (Real.sqrt (x * y * z / (x * y + p * q)) : ℂ) *
          symEllIntRC (x * y + p * q : ℝ) (p * q : ℝ) := by
  sorry

/-- DLMF 19.20.16: `p = w y + (1 - w) z` with `w = (z - x)/(z + q) ∈ (0, 1)`, so that
`x < y < p < z` (`p` in a hyperbolic region). -/
@[dlmf 19.20.E16]
theorem symEllIntRJ_principalValue_p {x y z q : ℝ} (hx : 0 ≤ x) (hxy : x < y) (hyz : y < z)
    (hq : 0 < q) :
    (z * (x + y + q) - x * y) / (z + q) =
        (z - x) / (z + q) * y + (1 - (z - x) / (z + q)) * z ∧
      0 < (z - x) / (z + q) ∧ (z - x) / (z + q) < 1 := by
  have hzq : 0 < z + q := by linarith
  refine ⟨by field_simp; ring, div_pos (by linarith) hzq, (div_lt_one hzq).mpr (by linarith)⟩

/-- DLMF 19.20.17: the complete case `x = 0` of (19.20.14): for `0 < y < z`, `q > 0`,
`p = z(y + q)/(z + q)`, `(q + z) R_J(0, y, z, -q) = (p - z) R_J(0, y, z, p) - 3 R_F(0, y, z)`. -/
@[dlmf 19.20.E17]
theorem symEllIntRJ_principalValue_complete {y z q : ℝ} (hy : 0 < y) (hyz : y < z) (hq : 0 < q) :
    let p : ℝ := z * (y + q) / (z + q)
    ((q + z : ℝ) : ℂ) * symEllIntRJ 0 y z (-q : ℝ) =
      ((p - z : ℝ) : ℂ) * symEllIntRJ 0 y z p - 3 * symEllIntRF 0 y z := by
  sorry

/-! ### §19.20(iv) `R_D` -/

/-- DLMF 19.20.18 (first): `R_D(x, x, x) = x^{-3/2}`. -/
@[dlmf 19.20.E18]
theorem symEllIntRD_self {x : ℂ} (hx : x ∈ slitPlane) : symEllIntRD x x x = x ^ (-3 / 2 : ℂ) :=
  symEllIntRJ_self hx

/-- DLMF 19.20.18 (second): `R_D(λx, λy, λz) = λ^{-3/2} R_D(x, y, z)`, `λ > 0`. -/
@[dlmf 19.20.E18]
theorem symEllIntRD_smul {l : ℝ} (hl : 0 < l) {x y z : ℂ} (hx : x ∈ slitPlane)
    (hy : y ∈ slitPlane) (hz : z ∈ slitPlane) :
    symEllIntRD (l * x) (l * y) (l * z) = (l : ℂ) ^ (-3 / 2 : ℂ) * symEllIntRD x y z :=
  symEllIntRJ_smul hl hx hy hz hz

/-- DLMF 19.20.18 (third): `R_D(0, y, y) = (3π/4) y^{-3/2}`. -/
@[dlmf 19.20.E18]
theorem symEllIntRD_zero_self {y : ℂ} (hy : y ∈ slitPlane) :
    symEllIntRD 0 y y = (3 * π / 4) * y ^ (-3 / 2 : ℂ) := by
  rw [symEllIntRD_zero_left hy hy]
  have : (![y, y] : Fin 2 → ℂ) = fun _ => y := by funext i; fin_cases i <;> rfl
  rw [this, symEllIntR_const _ _ hy (Complex.Gamma_ne_zero_of_re_pos (by simp; norm_num))]
  congr 2; ring

/-- DLMF 19.20.18 (fourth): `R_D(0, 0, z) = ∞`: the defining integrand is not integrable. -/
@[dlmf 19.20.E18]
theorem not_integrableOn_symEllIntRD_zero_zero {z : ℂ} (hz : z ∈ slitPlane) :
    ¬ IntegrableOn (fun t => (symEllIntS 0 0 z t * ((t : ℂ) + z))⁻¹) (Ioi 0) :=
  p19sR1_not_integrableOn_zero_zero hz hz

/-- DLMF 19.20.19: `R_D(x, y, z) ∼ 3 x^{-1/2} y^{-1/2} z^{-1/2}` as `z/√(xy) → 0`; stated for
fixed `x, y > 0` and `z → 0+`. -/
@[dlmf 19.20.E19]
theorem symEllIntRD_isEquivalent_zero {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (fun z : ℝ => symEllIntRD x y z) ~[𝓝[>] 0]
      fun z : ℝ => ((3 * x ^ (-1 / 2 : ℝ) * y ^ (-1 / 2 : ℝ) * z ^ (-1 / 2 : ℝ) : ℝ) : ℂ) := by
  sorry

/-- DLMF 19.20.20: `R_D(x, y, y) = 3/(2(y - x)) (R_C(x, y) - √x/y)`, `x ≠ y`, `y ≠ 0`
(`x` admissible, `y ∈ ℂ \ (-∞, 0]`). -/
@[dlmf 19.20.E20]
theorem symEllIntRD_self_right {x y : ℂ} (hx : symEllIntArg x) (hy : y ∈ slitPlane)
    (hxy : x ≠ y) :
    symEllIntRD x y y = 3 / (2 * (y - x)) * (symEllIntRC x y - x ^ (1 / 2 : ℂ) / y) := by
  rcases hx with hx | rfl
  · exact p19sR1_symEllIntRD_self_right hx hy hxy
  · rw [symEllIntRD_zero_self hy, ← symEllIntRF_self_right 0
      (ei19c_not_isNegReal_of_mem_slitPlane hy),
      symEllIntRF_zero_self hy, zero_cpow (by norm_num : (1 / 2 : ℂ) ≠ 0)]
    have hy0 := slitPlane_ne_zero hy
    rw [show (-3 / 2 : ℂ) = -1 / 2 + (-1) by norm_num, cpow_add _ _ hy0, cpow_neg_one]
    field_simp
    ring

/-- DLMF 19.20.21: `R_D(x, x, z) = 3/(z - x) (R_C(z, x) - 1/√z)`, `x ≠ z`, `xz ≠ 0`
(`x, z ∈ ℂ \ (-∞, 0]`). -/
@[dlmf 19.20.E21]
theorem symEllIntRD_self_left {x z : ℂ} (hx : x ∈ slitPlane) (hz : z ∈ slitPlane) (hxz : x ≠ z) :
    symEllIntRD x x z = 3 / (z - x) * (symEllIntRC z x - 1 / z ^ (1 / 2 : ℂ)) :=
  p19sR1_symEllIntRD_self_left hx hz hxz

/-- DLMF 19.20.22: the second lemniscate constant
`∫₀¹ t² dt/√(1 - t⁴) = (1/3) R_D(0, 2, 1) = Γ(3/4)²/(2π)^{1/2}` (decimal value excluded). -/
@[dlmf 19.20.E22]
theorem lemniscate_second_symEllIntRD :
    ((∫ t in (0 : ℝ)..1, t ^ 2 / Real.sqrt (1 - t ^ 4) : ℝ) : ℂ) = (1 / 3) * symEllIntRD 0 2 1 ∧
      (1 / 3) * symEllIntRD 0 2 1 = ((Real.Gamma (3 / 4) ^ 2 / Real.sqrt (2 * π) : ℝ) : ℂ) := by
  refine ⟨p19sR1_integral_sq_div_sqrt_eq, ?_⟩
  have hP := p19sR1_lemniscate_product
  rw [p19sR1_symEllIntRF_zero_one_two] at hP
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
  have hD : (1 / 3) * symEllIntRD 0 2 1 =
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
theorem symEllIntRD_lemniscatic {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    symEllIntRD x y ((x + y) / 2 : ℝ) =
      symEllIntR (3 / 4) ![5 / 4, 1 / 2] ![((((x + y) / 2) ^ 2 : ℝ) : ℂ), ((x * y : ℝ) : ℂ)] := by
  sorry

/-- DLMF 19.20.23, corrected complex form: `R_D(x, y, a) = R_{-3 / 4}(5 / 4, 1/2; a², xy)`, `a = (x + y)/2`, for complex
`x, y` with `ℜ x > 0` and `ℜ y > 0`. **Corrected from the printed DLMF formula**: DLMF states it
under the 19.16(i) constraints only, but it fails there, e.g. at `x = -1 + i`, `y = -1 + 2i` the
two sides differ by a factor `±i` (independent mpmath check, 2026-10-25). -/
@[dlmf 19.20.E23 "corrected: complex x, y with Re x, Re y > 0"]
theorem symEllIntRD_lemniscatic_complex {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) :
    symEllIntRD x y ((x + y) / 2) =
      symEllIntR (3 / 4) ![5 / 4, 1 / 2] ![((x + y) / 2) ^ 2, x * y] := by
  sorry

/-! ### §19.20(v) `R_{-a}(𝐛; 𝐳)` -/

/-- DLMF 19.20.24 (first): `R_0(𝐛; 𝐳) = 1`, when `Γ(c) ≠ 0`, `c = ∑ bⱼ` (slit-plane nodes). -/
@[dlmf 19.20.E24]
theorem symEllIntR_zero {ι : Type*} [Fintype ι] (b : ι → ℂ) {z : ι → ℂ}
    (hz : z ∈ Carlson.carlsonRSlitDomain) (hb : Gamma (∑ i, b i) ≠ 0) :
    symEllIntR 0 b z = 1 := by
  rw [symEllIntR_of_mem _ _ hz]
  unfold Carlson.carlsonR
  have h := Carlson.regCarlsonR_natCast 0 b hz
  rw [Nat.cast_zero] at h
  rw [neg_zero, h, Carlson.regCarlsonRPolynomial_zero, mul_inv_cancel₀ hb]

/-- DLMF 19.20.24 (second): `R_N(𝐛; 𝐳) = N!/(c)_N T_N(𝐛, 𝐳)`, `N = 0, 1, 2, …`, `c = ∑ bⱼ`
with `0 < re c` (slit-plane nodes; `R_N` is `symEllIntR (-N)`). -/
@[dlmf 19.20.E24]
theorem symEllIntR_neg_natCast {n : ℕ} (N : ℕ) (b : Fin n → ℂ) {z : Fin n → ℂ}
    (hz : z ∈ Carlson.carlsonRSlitDomain) (hc : 0 < (∑ j, b j).re) :
    symEllIntR (-(N : ℂ)) b z =
      (N.factorial : ℂ) / (ascPochhammer ℂ N).eval (∑ j, b j) * symEllIntT N b z := by
  sorry

/-- DLMF 19.20.25: `R_{-c}(𝐛; 𝐳) = ∏ⱼ zⱼ^{-bⱼ}`, `c = ∑ bⱼ`, `Γ(c) ≠ 0`, slit-plane nodes.
From `Carlson.regCarlsonR_neg_sum_sub_nat`. -/
@[dlmf 19.20.E25]
theorem symEllIntR_sum {ι : Type*} [Fintype ι] (b : ι → ℂ) {z : ι → ℂ}
    (hz : z ∈ Carlson.carlsonRSlitDomain) (hb : Gamma (∑ i, b i) ≠ 0) :
    symEllIntR (∑ i, b i) b z = ∏ i, z i ^ (-b i) := by
  rw [symEllIntR_of_mem _ _ hz]
  unfold Carlson.carlsonR
  have h := Carlson.regCarlsonR_neg_sum_sub_nat 0 b hz
  rw [Nat.cast_zero, sub_zero] at h
  rw [h, Carlson.regCarlsonRPolynomial_zero]
  field_simp

/-- DLMF 19.20.26: Euler's transformation `R_{-a}(𝐛; 𝐳) = ∏ⱼ zⱼ^{-bⱼ} R_{-a'}(𝐛; 𝐳⁻¹)`,
`a + a' = c = ∑ bⱼ`, for all complex `a, 𝐛` and slit-plane nodes. From
`Carlson.regCarlsonR_euler`. -/
@[dlmf 19.20.E26]
theorem symEllIntR_euler {ι : Type*} [Fintype ι] (a : ℂ) (b : ι → ℂ) {z : ι → ℂ}
    (hz : z ∈ Carlson.carlsonRSlitDomain) :
    symEllIntR a b z = (∏ i, z i ^ (-b i)) * symEllIntR (∑ i, b i - a) b (fun i => (z i)⁻¹) := by
  rw [symEllIntR_of_mem _ _ hz, symEllIntR_of_mem _ _ (Carlson.carlsonRSlitDomain_inv hz)]
  unfold Carlson.carlsonR
  rw [Carlson.regCarlsonR_euler _ _ hz, show -(∑ i, b i) - -a = -(∑ i, b i - a) by ring]
  ring

end DLMF.EllipticIntegrals
