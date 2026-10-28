/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.EllipticIntegrals.Connection.CompleteIntegrals

/-!
# Changes of modulus and amplitude in elliptic integrals

Reciprocal and imaginary modulus substitutions for incomplete elliptic integrals on the
specified principal branches.

Source references and common attribution are retained in
`DLMF.EllipticIntegrals.Connection`.
-/

@[expose] public noncomputable section

open Complex Set Filter MeasureTheory

open scoped Real Topology

namespace DLMF.EllipticIntegrals

open DLMF.JacobiElliptic

/-! ### §19.7(ii) Change of modulus and amplitude -/

/-! ### Helpers for 19.7.4 (substitution `θ = arcsin (k sin ψ)`) -/

/-- Identity under the stated parameter and domain assumptions: `(x : ℂ) ^ (-(1 / 2 : ℂ)) =
((Real.sqrt x)⁻¹ : ℝ) ∧ (x : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt x : ℝ)`. -/
lemma p19lR1_ofReal_cpow_half {x : ℝ} (hx : 0 ≤ x) :
    (x : ℂ) ^ (-(1 / 2 : ℂ)) = ((Real.sqrt x)⁻¹ : ℝ) ∧ (x : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt x : ℝ) := by
  constructor
  · rw [show -(1 / 2 : ℂ) = ((-(1 / 2) : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow hx,
      Real.rpow_neg hx, ← Real.sqrt_eq_rpow]
  · rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow hx,
      ← Real.sqrt_eq_rpow]

/-- Estimate under the stated parameter and domain assumptions: `Real.sin x ^ 2 ≤ Real.sin y ^ 2`. -/
lemma p19lR1_sin_sq_le_of_le {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ π / 2) :
    Real.sin x ^ 2 ≤ Real.sin y ^ 2 := by
  have h1 : Real.sin x ≤ Real.sin y :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) hy hxy
  have h0 : 0 ≤ Real.sin x := Real.sin_nonneg_of_nonneg_of_le_pi hx (by linarith [Real.pi_pos])
  nlinarith

/-- `Π` for real data with `α² sin²φ < 1` on `0 ≤ φ ≤ π/2` needs no principal value. -/
lemma p19lR1_Pi_ofReal_of_lt {φ α2 : ℝ} (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ π / 2)
    (hα : α2 * Real.sin φ ^ 2 < 1) (k : ℂ) :
    incEllIntPik φ α2 k = ∫ θ in (0 : ℝ)..φ, ((1 - α2 * (Real.sin θ : ℂ) ^ 2)⁻¹ *
      (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))) := by
  rw [incEllIntPik_eq_segmentIntegral (δ := min 1 (1 - α2 * Real.sin φ ^ 2))
    (lt_min one_pos (by linarith)), ei19a_segmentIntegral_ofReal]
  · simp only [← Complex.ofReal_sin]
  · intro t ht
    have hs := p19lR1_sin_sq_le_of_le (x := t * φ) (y := φ) (by nlinarith [ht.1])
      (by nlinarith [ht.2]) hφ1
    have hs0 := sq_nonneg (Real.sin (t * φ))
    have hre : (1 - (α2 : ℂ) * Complex.sin (t * φ) ^ 2) =
        ((1 - α2 * Real.sin (t * φ) ^ 2 : ℝ) : ℂ) := by
      push_cast; rfl
    rw [hre, Complex.norm_real, Real.norm_eq_abs]
    have hpos : min 1 (1 - α2 * Real.sin φ ^ 2) ≤ 1 - α2 * Real.sin (t * φ) ^ 2 := by
      rcases le_or_gt α2 0 with h | h
      · exact (min_le_left _ _).trans (by nlinarith)
      · exact (min_le_right _ _).trans (by nlinarith)
    exact hpos.trans (le_abs_self _)

/-- The substitution `θ = arcsin (k sin ψ)` on `[0, β]`. -/
lemma p19lR1_arcsin_subst {k β : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (hβ0 : 0 ≤ β) (hβ1 : β ≤ π / 2)
    (g : ℝ → ℂ) :
    ∫ θ in (0 : ℝ)..(Real.arcsin (k * Real.sin β)), g θ =
      ∫ ψ in (0 : ℝ)..β, ((k * Real.cos ψ / Real.sqrt (1 - k ^ 2 * Real.sin ψ ^ 2) : ℝ) : ℂ) *
        g (Real.arcsin (k * Real.sin ψ)) := by
  have hb : ∀ ψ : ℝ, k * Real.sin ψ < 1 := fun ψ => by
    nlinarith [Real.sin_le_one ψ, Real.neg_one_le_sin ψ]
  have hb' : ∀ ψ : ℝ, -1 < k * Real.sin ψ := fun ψ => by
    nlinarith [Real.sin_le_one ψ, Real.neg_one_le_sin ψ]
  have h := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg (a := 0) (b := β) (g := g)
    (f := fun ψ => Real.arcsin (k * Real.sin ψ))
    (f' := fun ψ => k * Real.cos ψ / Real.sqrt (1 - k ^ 2 * Real.sin ψ ^ 2))
    (by fun_prop)
    (fun ψ _ => by
      have := (Real.hasDerivAt_arcsin (hb' ψ).ne' (hb ψ).ne).comp ψ
        ((Real.hasDerivAt_sin ψ).const_mul k)
      refine this.congr_deriv ?_
      rw [mul_pow]; field_simp)
    (fun ψ hψ => by
      rw [min_eq_left hβ0, max_eq_right hβ0] at hψ
      have := Real.cos_nonneg_of_mem_Icc (x := ψ)
        ⟨by linarith [hψ.1, Real.pi_pos], by linarith [hψ.2]⟩
      exact div_nonneg (mul_nonneg hk0.le this) (Real.sqrt_nonneg _))
  simp only [Real.sin_zero, mul_zero, Real.arcsin_zero, real_smul, Function.comp] at h
  exact h.symm

/-- Identity under the stated parameter and domain assumptions: `incEllIntFk φ (1 / k : ℝ) = k *
incEllIntFk β k ∧ incEllIntEk φ (1 / k : ℝ) = (incEllIntEk β k - (1 - k ^ 2 : ℝ) * incEllIntFk
β k) / k ∧ incEllIntPik φ α2 (1 / k : ℝ) = k * incEllIntPik β (k ^ 2 * α2 : ℝ) k`. -/
lemma p19lR1_recip_modulus {k β φ α2 : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ π / 2) (hφ : Real.arcsin (k * Real.sin β) = φ) (hα : α2 * Real.sin φ ^ 2 < 1) :
    incEllIntFk φ (1 / k : ℝ) = k * incEllIntFk β k ∧
      incEllIntEk φ (1 / k : ℝ) = (incEllIntEk β k - (1 - k ^ 2 : ℝ) * incEllIntFk β k) / k ∧
      incEllIntPik φ α2 (1 / k : ℝ) = k * incEllIntPik β (k ^ 2 * α2 : ℝ) k := by
  subst hφ
  have hb : ∀ ψ : ℝ, k * Real.sin ψ ≤ 1 := fun ψ => by
    nlinarith [Real.sin_le_one ψ, Real.neg_one_le_sin ψ]
  have hb' : ∀ ψ : ℝ, -1 ≤ k * Real.sin ψ := fun ψ => by
    nlinarith [Real.sin_le_one ψ, Real.neg_one_le_sin ψ]
  have hsin : ∀ ψ, Real.sin (Real.arcsin (k * Real.sin ψ)) = k * Real.sin ψ :=
    fun ψ => Real.sin_arcsin (hb' ψ) (hb ψ)
  have hk0' : (k : ℂ) ≠ 0 := by exact_mod_cast hk0.ne'
  have hspos : ∀ ψ : ℝ, 0 < 1 - k ^ 2 * Real.sin ψ ^ 2 := fun ψ => by
    nlinarith [Real.sin_sq_le_one ψ, sq_nonneg (Real.sin ψ), mul_pos hk0 hk0]
  set s : ℝ → ℝ := fun ψ => Real.sqrt (1 - k ^ 2 * Real.sin ψ ^ 2) with hs
  have hs0 : ∀ ψ, 0 < s ψ := fun ψ => Real.sqrt_pos.2 (hspos ψ)
  have hs2 : ∀ ψ, s ψ ^ 2 = 1 - k ^ 2 * Real.sin ψ ^ 2 := fun ψ => Real.sq_sqrt (hspos ψ).le
  have hsc : Continuous s := by rw [hs]; fun_prop
  have hΔ : ∀ ψ : ℝ, (1 - (k : ℂ) ^ 2 * (Real.sin ψ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) = ((s ψ)⁻¹ : ℝ) ∧
      (1 - (k : ℂ) ^ 2 * (Real.sin ψ : ℂ) ^ 2) ^ (1 / 2 : ℂ) = (s ψ : ℝ) := by
    intro ψ
    have e : (1 - (k : ℂ) ^ 2 * (Real.sin ψ : ℂ) ^ 2) = ((1 - k ^ 2 * Real.sin ψ ^ 2 : ℝ) : ℂ) := by
      push_cast; ring
    rw [e]; exact p19lR1_ofReal_cpow_half (hspos ψ).le
  -- on `0 < ψ < π/2`, the reciprocal-modulus integrand
  have hcos : ∀ ψ : ℝ, 0 < Real.cos ψ →
      (1 - ((1 / k : ℝ) : ℂ) ^ 2 * (Real.sin (Real.arcsin (k * Real.sin ψ)) : ℂ) ^ 2) ^
        (-(1 / 2 : ℂ)) = ((Real.cos ψ)⁻¹ : ℝ) ∧
      (1 - ((1 / k : ℝ) : ℂ) ^ 2 * (Real.sin (Real.arcsin (k * Real.sin ψ)) : ℂ) ^ 2) ^
        (1 / 2 : ℂ) = (Real.cos ψ : ℝ) := by
    intro ψ hc
    have e : (1 - ((1 / k : ℝ) : ℂ) ^ 2 * (Real.sin (Real.arcsin (k * Real.sin ψ)) : ℂ) ^ 2) =
        ((Real.cos ψ ^ 2 : ℝ) : ℂ) := by
      have er : 1 - (1 / k) ^ 2 * Real.sin (Real.arcsin (k * Real.sin ψ)) ^ 2 = Real.cos ψ ^ 2 := by
        rw [hsin]; field_simp; nlinarith [Real.sin_sq_add_cos_sq ψ]
      rw [← er]; simp only [ofReal_sub, ofReal_one, ofReal_mul, ofReal_pow]
    rw [e, (p19lR1_ofReal_cpow_half (sq_nonneg _)).1, (p19lR1_ofReal_cpow_half (sq_nonneg _)).2,
      Real.sqrt_sq hc.le]
    exact ⟨rfl, rfl⟩
  have hae : ∀ᵐ ψ : ℝ, ψ ∈ uIoc 0 β → 0 < Real.cos ψ := by
    filter_upwards [Measure.ae_ne volume (π / 2)] with ψ hne hψ
    rw [uIoc_of_le hβ0] at hψ
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [hψ.1, Real.pi_pos],
      lt_of_le_of_ne (hψ.2.trans hβ1) hne⟩
  have hφ0 : 0 ≤ Real.arcsin (k * Real.sin β) :=
    Real.arcsin_nonneg.2 (mul_nonneg hk0.le (Real.sin_nonneg_of_nonneg_of_le_pi hβ0
      (by linarith [Real.pi_pos])))
  have hφ1 : Real.arcsin (k * Real.sin β) ≤ π / 2 := Real.arcsin_le_pi_div_two _
  have hsint : IntervalIntegrable (fun ψ => ((s ψ : ℝ) : ℂ)) volume 0 β :=
    (continuous_ofReal.comp hsc).intervalIntegrable _ _
  have hsiint : IntervalIntegrable (fun ψ => (((s ψ)⁻¹ : ℝ) : ℂ)) volume 0 β :=
    (continuous_ofReal.comp (hsc.inv₀ fun ψ => (hs0 ψ).ne')).intervalIntegrable _ _
  refine ⟨?_, ?_, ?_⟩
  · rw [incEllIntFk_ofReal_eq_integral, p19lR1_arcsin_subst hk0 hk1 hβ0 hβ1,
      incEllIntFk_ofReal_eq_integral, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hae] with ψ hψ hmem
    have hc := hψ hmem
    rw [(hcos ψ hc).1, (hΔ ψ).1, ← ofReal_mul, ← ofReal_mul]
    congr 1
    have := (Real.sqrt_pos.2 (hspos ψ)).ne'
    simp only [hs]
    field_simp
  · have hrhs : incEllIntEk β k - (1 - k ^ 2 : ℝ) * incEllIntFk β k =
        ∫ ψ in (0 : ℝ)..β, ((k ^ 2 * Real.cos ψ ^ 2 / s ψ : ℝ) : ℂ) := by
      rw [incEllIntEk_ofReal_eq_integral, incEllIntFk_ofReal_eq_integral]
      simp only [fun ψ => (hΔ ψ).1, fun ψ => (hΔ ψ).2]
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub hsint
        (hsiint.const_mul _)]
      refine intervalIntegral.integral_congr fun ψ _ => ?_
      have h0 := (hs0 ψ).ne'
      have h2 := hs2 ψ
      rw [show ((1 - k ^ 2 : ℝ) : ℂ) * (((s ψ)⁻¹ : ℝ) : ℂ) = (((1 - k ^ 2) * (s ψ)⁻¹ : ℝ) : ℂ) by
        push_cast; ring, ← ofReal_sub]
      congr 1
      rw [Real.cos_sq']
      field_simp
      linear_combination h2
    rw [hrhs, incEllIntEk_ofReal_eq_integral, p19lR1_arcsin_subst hk0 hk1 hβ0 hβ1,
      ← intervalIntegral.integral_div]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hae] with ψ hψ hmem
    have hc := hψ hmem
    rw [(hcos ψ hc).2, ← ofReal_mul, ← ofReal_div]
    congr 1
    have := (Real.sqrt_pos.2 (hspos ψ)).ne'
    simp only [hs]
    field_simp
  · have hαβ : (k ^ 2 * α2) * Real.sin β ^ 2 < 1 := by
      have := hα; rw [hsin] at this; nlinarith
    rw [p19lR1_Pi_ofReal_of_lt hφ0 hφ1 hα, p19lR1_arcsin_subst hk0 hk1 hβ0 hβ1,
      p19lR1_Pi_ofReal_of_lt hβ0 hβ1 hαβ, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hae] with ψ hψ hmem
    have hc := hψ hmem
    rw [(hcos ψ hc).1, (hΔ ψ).1, hsin]
    rw [show (1 - (α2 : ℂ) * ((k * Real.sin ψ : ℝ) : ℂ) ^ 2)⁻¹ =
        (((1 - α2 * (k * Real.sin ψ) ^ 2)⁻¹ : ℝ) : ℂ) by push_cast; ring,
      show (1 - ((k ^ 2 * α2 : ℝ) : ℂ) * (Real.sin ψ : ℂ) ^ 2)⁻¹ =
        (((1 - k ^ 2 * α2 * Real.sin ψ ^ 2)⁻¹ : ℝ) : ℂ) by push_cast; ring]
    simp only [← ofReal_mul]
    congr 1
    have := (Real.sqrt_pos.2 (hspos ψ)).ne'
    simp only [hs]
    field_simp

/-- DLMF 19.7.4 (reciprocal-modulus transformation): for real `0 < k < 1`,
`k₁ = 1/k`, real `0 ≤ φ ≤ π/2` with `sin β = k₁ sin φ ≤ 1` (`β = arcsin(k₁ sin φ)`), and real
`α²` with `α² sin²φ < 1`,
`F(φ, k₁) = kF(β, k)`, `E(φ, k₁) = (E(β, k) - k'²F(β, k))/k`, `Π(φ, α², k₁) = kΠ(β, k²α², k)`. -/
@[dlmf 19.7.E4]
theorem incEllInt_reciprocal_modulus {k φ α2 : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (hφ0 : 0 ≤ φ)
    (hφ1 : φ ≤ π / 2) (hφk : Real.sin φ ≤ k) (hα : α2 * Real.sin φ ^ 2 < 1) :
    let β := Real.arcsin (Real.sin φ / k)
    incEllIntFk φ (1 / k : ℝ) = k * incEllIntFk β k ∧
      incEllIntEk φ (1 / k : ℝ) = (incEllIntEk β k - (1 - k ^ 2 : ℝ) * incEllIntFk β k) / k ∧
      incEllIntPik φ α2 (1 / k : ℝ) = k * incEllIntPik β (k ^ 2 * α2 : ℝ) k := by
  intro β
  have hs0 : 0 ≤ Real.sin φ := Real.sin_nonneg_of_nonneg_of_le_pi hφ0 (by linarith [Real.pi_pos])
  have hu0 : 0 ≤ Real.sin φ / k := div_nonneg hs0 hk0.le
  have hu1 : Real.sin φ / k ≤ 1 := (div_le_one hk0).2 hφk
  have hβ0 : 0 ≤ β := Real.arcsin_nonneg.2 hu0
  have hβ1 : β ≤ π / 2 := Real.arcsin_le_pi_div_two _
  have hφ : Real.arcsin (k * Real.sin β) = φ := by
    rw [Real.sin_arcsin (by linarith) hu1, mul_div_cancel₀ _ hk0.ne',
      Real.arcsin_sin (by linarith [Real.pi_pos]) hφ1]
  exact p19lR1_recip_modulus hk0 hk1 hβ0 hβ1 hφ hα

/-! ### Helpers for 19.7.5–19.7.6 (substitution `tan θ = √(1+k²) tan u`) -/

/-- The amplitude map of 19.7.5, `T(u) = arcsin (√(1+k²) sin u / √(1 + k² sin²u))`. -/
noncomputable def p19lR1_T (k u : ℝ) : ℝ :=
  Real.arcsin (Real.sqrt (1 + k ^ 2) * Real.sin u / Real.sqrt (1 + k ^ 2 * Real.sin u ^ 2))

/-- Estimate under the stated parameter and domain assumptions: `0 < 1 + k ^ 2 * Real.sin u ^ 2`. -/
lemma p19lR1_w_pos (k u : ℝ) : 0 < 1 + k ^ 2 * Real.sin u ^ 2 := by positivity

/-- Estimate under the stated parameter and domain assumptions: `(Real.sqrt (1 + k ^ 2) * Real.sin
u / Real.sqrt (1 + k ^ 2 * Real.sin u ^ 2)) ^ 2 ≤ 1`. -/
lemma p19lR1_T_arg_le (k u : ℝ) :
    (Real.sqrt (1 + k ^ 2) * Real.sin u / Real.sqrt (1 + k ^ 2 * Real.sin u ^ 2)) ^ 2 ≤ 1 := by
  rw [div_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity),
    div_le_one (by positivity)]
  nlinarith [Real.sin_sq_le_one u, sq_nonneg k, sq_nonneg (Real.sin u)]

/-- Identity under the stated parameter and domain assumptions: `Real.sin (p19lR1_T k u) =
Real.sqrt (1 + k ^ 2) * Real.sin u / Real.sqrt (1 + k ^ 2 * Real.sin u ^ 2)`. -/
lemma p19lR1_sin_T (k u : ℝ) :
    Real.sin (p19lR1_T k u) =
      Real.sqrt (1 + k ^ 2) * Real.sin u / Real.sqrt (1 + k ^ 2 * Real.sin u ^ 2) := by
  have h := p19lR1_T_arg_le k u
  rw [p19lR1_T, Real.sin_arcsin (by nlinarith [sq_nonneg (Real.sqrt (1 + k ^ 2) * Real.sin u /
    Real.sqrt (1 + k ^ 2 * Real.sin u ^ 2) + 1)]) (by nlinarith [sq_nonneg (Real.sqrt (1 + k ^ 2) *
    Real.sin u / Real.sqrt (1 + k ^ 2 * Real.sin u ^ 2) - 1)])]

/-- Identity under the stated parameter and domain assumptions: `p19lR1_T k u = Real.arctan
(Real.sqrt (1 + k ^ 2) * Real.tan u)`. -/
lemma p19lR1_T_eq_arctan (k : ℝ) {u : ℝ} (hu : u ∈ Ioo (-(π / 2)) (π / 2)) :
    p19lR1_T k u = Real.arctan (Real.sqrt (1 + k ^ 2) * Real.tan u) := by
  have hc := Real.cos_pos_of_mem_Ioo hu
  have hw := p19lR1_w_pos k u
  rw [Real.arctan_eq_arcsin, p19lR1_T]
  congr 1
  have h1 : 1 + (Real.sqrt (1 + k ^ 2) * Real.tan u) ^ 2 =
      (Real.sqrt (1 + k ^ 2 * Real.sin u ^ 2) / Real.cos u) ^ 2 := by
    rw [mul_pow, div_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hw.le, Real.tan_eq_sin_div_cos]
    field_simp
    nlinarith [Real.sin_sq_add_cos_sq u]
  rw [h1, Real.sqrt_sq (div_nonneg (Real.sqrt_nonneg _) hc.le), Real.tan_eq_sin_div_cos]
  have := (Real.sqrt_pos.2 hw).ne'
  field_simp

/-- At `u`, the function `(p19lR1_T k)` has derivative `(Real.sqrt (1 + k ^ 2) / (1 + k ^ 2 *
Real.sin u ^ 2))`. -/
lemma p19lR1_hasDerivAt_T (k : ℝ) {u : ℝ} (hu : u ∈ Ioo (-(π / 2)) (π / 2)) :
    HasDerivAt (p19lR1_T k) (Real.sqrt (1 + k ^ 2) / (1 + k ^ 2 * Real.sin u ^ 2)) u := by
  have hc := Real.cos_pos_of_mem_Ioo hu
  have h := (Real.hasDerivAt_arctan (Real.sqrt (1 + k ^ 2) * Real.tan u)).comp u
    ((Real.hasDerivAt_tan hc.ne').const_mul (Real.sqrt (1 + k ^ 2)))
  have heq : (fun v => Real.arctan (Real.sqrt (1 + k ^ 2) * Real.tan v)) =ᶠ[𝓝 u] p19lR1_T k := by
    filter_upwards [isOpen_Ioo.mem_nhds hu] with v hv
    exact (p19lR1_T_eq_arctan k hv).symm
  refine (h.congr_of_eventuallyEq heq.symm).congr_deriv ?_
  have hw := p19lR1_w_pos k u
  rw [mul_pow, Real.sq_sqrt (by positivity), Real.tan_eq_sin_div_cos]
  field_simp
  nlinarith [Real.sin_sq_add_cos_sq u]

/-- The function `(p19lR1_T k)` is continuous. -/
lemma p19lR1_continuous_T (k : ℝ) : Continuous (p19lR1_T k) := by
  unfold p19lR1_T
  refine Real.continuous_arcsin.comp ?_
  exact Continuous.div (by fun_prop) (by fun_prop) fun u => (Real.sqrt_pos.2 (p19lR1_w_pos k u)).ne'

/-- Identity under the stated parameter and domain assumptions: `∫ θ in (0 : ℝ)..(p19lR1_T k φ), g
θ = ∫ u in (0 : ℝ)..φ, ((Real.sqrt (1 + k ^ 2) / (1 + k ^ 2 * Real.sin u ^ 2) : ℝ) : ℂ) * g
(p19lR1_T k u)`. -/
lemma p19lR1_T_subst (k : ℝ) {φ : ℝ} (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ π / 2) (g : ℝ → ℂ) :
    ∫ θ in (0 : ℝ)..(p19lR1_T k φ), g θ =
      ∫ u in (0 : ℝ)..φ, ((Real.sqrt (1 + k ^ 2) / (1 + k ^ 2 * Real.sin u ^ 2) : ℝ) : ℂ) *
        g (p19lR1_T k u) := by
  have h := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg (a := 0) (b := φ) (g := g)
    (f := p19lR1_T k) (f' := fun u => Real.sqrt (1 + k ^ 2) / (1 + k ^ 2 * Real.sin u ^ 2))
    (p19lR1_continuous_T k).continuousOn
    (fun u hu => by
      rw [min_eq_left hφ0, max_eq_right hφ0] at hu
      exact p19lR1_hasDerivAt_T k ⟨by linarith [hu.1, Real.pi_pos], by linarith [hu.2]⟩)
    (fun u _ => div_nonneg (Real.sqrt_nonneg _) (p19lR1_w_pos k u).le)
  have h0 : p19lR1_T k 0 = 0 := by simp [p19lR1_T]
  simp only [h0, real_smul, Function.comp] at h
  exact h.symm

/-- The change to an imaginary elliptic modulus transforms both square-root factors on their
principal branches; the positive real square roots fix the signs. -/
lemma p19lR1_imod_pt (k u : ℝ) :
    (1 - (I * k) ^ 2 * (Real.sin u : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) =
        (((Real.sqrt (1 + k ^ 2 * Real.sin u ^ 2))⁻¹ : ℝ) : ℂ) ∧
      (1 - (I * k) ^ 2 * (Real.sin u : ℂ) ^ 2) ^ (1 / 2 : ℂ) =
        ((Real.sqrt (1 + k ^ 2 * Real.sin u ^ 2) : ℝ) : ℂ) ∧
      (1 - ((k / Real.sqrt (1 + k ^ 2) : ℝ) : ℂ) ^ 2 * (Real.sin (p19lR1_T k u) : ℂ) ^ 2) ^
          (-(1 / 2 : ℂ)) = ((Real.sqrt (1 + k ^ 2 * Real.sin u ^ 2) : ℝ) : ℂ) ∧
      (1 - ((k / Real.sqrt (1 + k ^ 2) : ℝ) : ℂ) ^ 2 * (Real.sin (p19lR1_T k u) : ℂ) ^ 2) ^
          (1 / 2 : ℂ) = (((Real.sqrt (1 + k ^ 2 * Real.sin u ^ 2))⁻¹ : ℝ) : ℂ) := by
  have hw := p19lR1_w_pos k u
  have hW := Real.sqrt_pos.2 hw
  have hW2 := Real.sq_sqrt hw.le
  have hc := Real.sqrt_pos.2 (by positivity : (0 : ℝ) < 1 + k ^ 2)
  have hc2 := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 1 + k ^ 2)
  have e1 : (1 - (I * k) ^ 2 * (Real.sin u : ℂ) ^ 2) = ((1 + k ^ 2 * Real.sin u ^ 2 : ℝ) : ℂ) := by
    rw [mul_pow, I_sq]; simp only [ofReal_add, ofReal_one, ofReal_mul, ofReal_pow]; ring
  have er : 1 - (k / Real.sqrt (1 + k ^ 2)) ^ 2 * Real.sin (p19lR1_T k u) ^ 2 =
      (Real.sqrt (1 + k ^ 2 * Real.sin u ^ 2) ^ 2)⁻¹ := by
    rw [p19lR1_sin_T, div_pow, div_pow, mul_pow, hc2, hW2]
    field_simp
    ring
  have e2 : (1 - ((k / Real.sqrt (1 + k ^ 2) : ℝ) : ℂ) ^ 2 * (Real.sin (p19lR1_T k u) : ℂ) ^ 2) =
      (((Real.sqrt (1 + k ^ 2 * Real.sin u ^ 2) ^ 2)⁻¹ : ℝ) : ℂ) := by
    rw [← er]; simp only [ofReal_sub, ofReal_one, ofReal_mul, ofReal_pow]
  rw [e1, e2, (p19lR1_ofReal_cpow_half hw.le).1, (p19lR1_ofReal_cpow_half hw.le).2,
    (p19lR1_inv_sq_cpow hW).1, (p19lR1_inv_sq_cpow hW).2]
  push_cast
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Identity under the stated parameter and domain assumptions: `(1 - α2 * s ^ 2)⁻¹ * W⁻¹ = (1 /
c) / ((α2 + k ^ 2) / (1 + k ^ 2)) * ((k / c) ^ 2 * (c * W⁻¹) + ((1 / c) ^ 2 * α2) * (c * W /
(1 - α2 * s ^ 2)))`. -/
lemma p19lR1_alg_Pi {k α2 c W s : ℝ} (hc : 0 < c) (hW : 0 < W) (hc2 : c ^ 2 = 1 + k ^ 2)
    (hW2 : W ^ 2 = 1 + k ^ 2 * s ^ 2) (hd : 1 - α2 * s ^ 2 ≠ 0) (hαk : α2 + k ^ 2 ≠ 0) :
    (1 - α2 * s ^ 2)⁻¹ * W⁻¹ = (1 / c) / ((α2 + k ^ 2) / (1 + k ^ 2)) *
      ((k / c) ^ 2 * (c * W⁻¹) + ((1 / c) ^ 2 * α2) * (c * W / (1 - α2 * s ^ 2))) := by
  rw [← hc2]
  field_simp
  linear_combination (-(α2)) * hW2

/-- Identity under the stated parameter and domain assumptions: `(1 + k ^ 2) * J - k ^ 2 * sc / Wφ
= (1 / (1 / c)) * (c * J - X)`. -/
lemma p19lR1_alg_E {k c J X Wφ sc : ℝ} (hc2 : c ^ 2 = 1 + k ^ 2) (hc : 0 < c) (hW : 0 < Wφ)
    (hX : X = k ^ 2 * sc / (c * Wφ)) :
    (1 + k ^ 2) * J - k ^ 2 * sc / Wφ = (1 / (1 / c)) * (c * J - X) := by
  rw [hX, ← hc2]; field_simp

/-- Identity under the stated parameter and domain assumptions: `c / a * w = c * w⁻¹`. -/
lemma p19lR1_alg1 {a w : ℝ} (hw : 0 < w) (h : w ^ 2 = a) (c : ℝ) : c / a * w = c * w⁻¹ := by
  rw [← h]; field_simp

/-- Identity under the stated parameter and domain assumptions: `c / a * w⁻¹ = c * (w ^ 3)⁻¹`. -/
lemma p19lR1_alg2 {a w : ℝ} (hw : 0 < w) (h : w ^ 2 = a) (c : ℝ) :
    c / a * w⁻¹ = c * (w ^ 3)⁻¹ := by
  rw [← h]; field_simp

/-- Identity under the stated parameter and domain assumptions: `c / (1 + k ^ 2 * s ^ 2) * ((1 -
(α2 + k ^ 2) / (1 + k ^ 2) * (c * s / W) ^ 2)⁻¹ * W) = c * W / (1 - α2 * s ^ 2)`. -/
lemma p19lR1_alg_P {k α2 c W s : ℝ} (hc2 : c ^ 2 = 1 + k ^ 2) (hW : 0 < W)
    (hW2 : W ^ 2 = 1 + k ^ 2 * s ^ 2) (hd : 1 - α2 * s ^ 2 ≠ 0) :
    c / (1 + k ^ 2 * s ^ 2) * ((1 - (α2 + k ^ 2) / (1 + k ^ 2) * (c * s / W) ^ 2)⁻¹ * W) =
      c * W / (1 - α2 * s ^ 2) := by
  have h1 : 1 - (α2 + k ^ 2) / (1 + k ^ 2) * (c * s / W) ^ 2 = (1 - α2 * s ^ 2) / W ^ 2 := by
    rw [div_pow, mul_pow, hc2]
    have : (1 + k ^ 2) ≠ 0 := by positivity
    field_simp
    rw [hW2]; ring
  rw [h1, ← hW2]
  field_simp

/-- Identity under the stated parameter and domain assumptions: `(k / Real.sqrt (1 + k ^ 2)) ^ 2 *
Real.sin (p19lR1_T k φ) * Real.cos (p19lR1_T k φ) / Real.sqrt (1 - (k / Real.sqrt (1 + k ^ 2))
^ 2 * Real.sin (p19lR1_T k φ) ^ 2) = k ^ 2 * (Real.sin φ * Real.cos φ) / (Real.sqrt (1 + k ^
2) * Real.sqrt (1 + k ^ 2 * Real.sin φ ^ 2))`. -/
lemma p19lR1_imod_X (k : ℝ) {φ : ℝ} (hφ1 : φ ≤ π / 2) (hφ0 : 0 ≤ φ) :
    (k / Real.sqrt (1 + k ^ 2)) ^ 2 * Real.sin (p19lR1_T k φ) * Real.cos (p19lR1_T k φ) /
        Real.sqrt (1 - (k / Real.sqrt (1 + k ^ 2)) ^ 2 * Real.sin (p19lR1_T k φ) ^ 2) =
      k ^ 2 * (Real.sin φ * Real.cos φ) /
        (Real.sqrt (1 + k ^ 2) * Real.sqrt (1 + k ^ 2 * Real.sin φ ^ 2)) := by
  set c := Real.sqrt (1 + k ^ 2) with hc
  set w := Real.sqrt (1 + k ^ 2 * Real.sin φ ^ 2) with hw
  have hc0 : 0 < c := Real.sqrt_pos.2 (by positivity)
  have hc2 : c ^ 2 = 1 + k ^ 2 := Real.sq_sqrt (by positivity)
  have hw0 : 0 < w := Real.sqrt_pos.2 (p19lR1_w_pos k φ)
  have hw2 : w ^ 2 = 1 + k ^ 2 * Real.sin φ ^ 2 := Real.sq_sqrt (p19lR1_w_pos k φ).le
  have hs : Real.sin (p19lR1_T k φ) = c * Real.sin φ / w := p19lR1_sin_T k φ
  have hcφ : 0 ≤ Real.cos φ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hφ1⟩
  have hcos : Real.cos (p19lR1_T k φ) = Real.cos φ / w := by
    have h1 : Real.cos (p19lR1_T k φ) = Real.sqrt (1 - (c * Real.sin φ / w) ^ 2) := by
      rw [p19lR1_T, Real.cos_arcsin]
    have h2 : 1 - (c * Real.sin φ / w) ^ 2 = (Real.cos φ / w) ^ 2 := by
      rw [div_pow, div_pow, mul_pow, hc2]
      field_simp
      rw [hw2]
      nlinarith [Real.sin_sq_add_cos_sq φ]
    rw [h1, h2, Real.sqrt_sq (div_nonneg hcφ hw0.le)]
  have hsq : Real.sqrt (1 - (k / c) ^ 2 * Real.sin (p19lR1_T k φ) ^ 2) = w⁻¹ := by
    have h2 : 1 - (k / c) ^ 2 * Real.sin (p19lR1_T k φ) ^ 2 = (w⁻¹) ^ 2 := by
      rw [hs, div_pow, div_pow, mul_pow, hc2]
      field_simp
      rw [hw2]
      ring
    rw [h2, Real.sqrt_sq (inv_nonneg.2 hw0.le)]
  rw [hsq, hs, hcos]
  field_simp

/-- DLMF 19.7.5–19.7.6 (imaginary-modulus transformation): for real `k`, real
`0 ≤ φ ≤ π/2` and real `α² < 1` with `α² + k² ≠ 0`, with `κ = k/√(1+k²)`, `κ' = 1/√(1+k²)`,
`sin θ = √(1+k²) sin φ/√(1 + k² sin²φ)` and `α₁² = (α² + k²)/(1 + k²)`:
`F(φ, ik) = κ'F(θ, κ)`,
`E(φ, ik) = (1/κ')(E(θ, κ) - κ² sin θ cos θ (1 - κ² sin²θ)^{-1/2})`,
`Π(φ, α², ik) = (κ'/α₁²)(κ²F(θ, κ) + κ'²α²Π(θ, α₁², κ))`. -/
@[dlmf 19.7.E5, dlmf 19.7.E6]
theorem incEllInt_imaginary_modulus {k φ α2 : ℝ} (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ π / 2) (hα : α2 < 1)
    (hαk : α2 + k ^ 2 ≠ 0) :
    let κ := k / Real.sqrt (1 + k ^ 2)
    let κ' := 1 / Real.sqrt (1 + k ^ 2)
    let θ := Real.arcsin (Real.sqrt (1 + k ^ 2) * Real.sin φ /
      Real.sqrt (1 + k ^ 2 * Real.sin φ ^ 2))
    let α12 := (α2 + k ^ 2) / (1 + k ^ 2)
    incEllIntFk φ (I * k) = κ' * incEllIntFk θ κ ∧
      incEllIntEk φ (I * k) = (1 / κ' : ℝ) * (incEllIntEk θ κ -
        (κ ^ 2 * Real.sin θ * Real.cos θ / Real.sqrt (1 - κ ^ 2 * Real.sin θ ^ 2) : ℝ)) ∧
      incEllIntPik φ α2 (I * k) = (κ' / α12 : ℝ) *
        ((κ ^ 2 : ℝ) * incEllIntFk θ κ + (κ' ^ 2 * α2 : ℝ) * incEllIntPik θ α12 κ) := by
  intro κ κ' θ α12
  set c := Real.sqrt (1 + k ^ 2) with hc
  set W : ℝ → ℝ := fun u => Real.sqrt (1 + k ^ 2 * Real.sin u ^ 2) with hW
  have hθ : θ = p19lR1_T k φ := rfl
  have hκ : κ = k / c := rfl
  have hκ' : κ' = 1 / c := rfl
  have hc0 : 0 < c := Real.sqrt_pos.2 (by positivity)
  have hc2 : c ^ 2 = 1 + k ^ 2 := Real.sq_sqrt (by positivity)
  have hW0 : ∀ u, 0 < W u := fun u => Real.sqrt_pos.2 (p19lR1_w_pos k u)
  have hW2 : ∀ u, W u ^ 2 = 1 + k ^ 2 * Real.sin u ^ 2 := fun u => Real.sq_sqrt (p19lR1_w_pos k u).le
  have hpt : ∀ u : ℝ, (1 - (I * k) ^ 2 * (Real.sin u : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) =
        (((W u)⁻¹ : ℝ) : ℂ) ∧
      (1 - (I * k) ^ 2 * (Real.sin u : ℂ) ^ 2) ^ (1 / 2 : ℂ) = ((W u : ℝ) : ℂ) ∧
      (1 - ((κ : ℝ) : ℂ) ^ 2 * (Real.sin (p19lR1_T k u) : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) =
        ((W u : ℝ) : ℂ) ∧
      (1 - ((κ : ℝ) : ℂ) ^ 2 * (Real.sin (p19lR1_T k u) : ℂ) ^ 2) ^ (1 / 2 : ℂ) =
        (((W u)⁻¹ : ℝ) : ℂ) := p19lR1_imod_pt k
  have hsub : ∀ g : ℝ → ℂ, ∫ x in (0 : ℝ)..θ, g x = ∫ u in (0 : ℝ)..φ,
      ((c / (1 + k ^ 2 * Real.sin u ^ 2) : ℝ) : ℂ) * g (p19lR1_T k u) :=
    p19lR1_T_subst k hφ0 hφ1
  have hθ0 : 0 ≤ θ := by
    rw [hθ, p19lR1_T]
    exact Real.arcsin_nonneg.2 (div_nonneg (mul_nonneg hc0.le
      (Real.sin_nonneg_of_nonneg_of_le_pi hφ0 (by linarith [Real.pi_pos]))) (hW0 φ).le)
  have hθ1 : θ ≤ π / 2 := Real.arcsin_le_pi_div_two _
  -- the first kind
  have hF1 : incEllIntFk φ (I * k) = ∫ u in (0 : ℝ)..φ, (((W u)⁻¹ : ℝ) : ℂ) := by
    rw [incEllIntFk_ofReal_eq_integral]
    exact intervalIntegral.integral_congr fun u _ => (hpt u).1
  have hF2 : incEllIntFk θ κ = ∫ u in (0 : ℝ)..φ, ((c * (W u)⁻¹ : ℝ) : ℂ) := by
    rw [incEllIntFk_ofReal_eq_integral, hsub]
    refine intervalIntegral.integral_congr fun u _ => ?_
    rw [(hpt u).2.2.1, ← ofReal_mul]
    exact congrArg ofReal (p19lR1_alg1 (hW0 u) (hW2 u) c)
  refine ⟨?_, ?_, ?_⟩
  · rw [hF1, hF2, intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal,
      intervalIntegral.integral_const_mul, ← ofReal_mul, hκ']
    congr 1
    field_simp
  · have hslit : 1 - (I * (k : ℂ)) ^ 2 ∈ slitPlane := by
      have : (1 - (I * (k : ℂ)) ^ 2) = ((1 + k ^ 2 : ℝ) : ℂ) := by
        rw [mul_pow, I_sq]; push_cast; ring
      rw [this]; exact ofReal_mem_slitPlane.2 (by positivity)
    have hcube := p19lR1_integral_cube hslit φ
    set J := ∫ u in (0 : ℝ)..φ, ((W u ^ 3)⁻¹ : ℝ) with hJ
    have hJ' : (∫ θ in (0 : ℝ)..φ, (1 - (I * (k : ℂ)) ^ 2 * (Real.sin θ : ℂ) ^ 2)⁻¹ *
        (1 - (I * (k : ℂ)) ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))) = (J : ℂ) := by
      rw [hJ, ← intervalIntegral.integral_ofReal]
      refine intervalIntegral.integral_congr fun u _ => ?_
      rw [(hpt u).1]
      have e : (1 - (I * (k : ℂ)) ^ 2 * (Real.sin u : ℂ) ^ 2) = ((W u ^ 2 : ℝ) : ℂ) := by
        rw [hW2 u, mul_pow, I_sq]; simp only [ofReal_add, ofReal_one, ofReal_mul, ofReal_pow]; ring
      rw [e, ← ofReal_inv, ← ofReal_mul]
      congr 1
      have := (hW0 u).ne'
      field_simp
    have hΔφ : p19lR1_Δ (I * k) φ = (W φ : ℂ) := (hpt φ).2.1
    have hEφ : incEllIntEk φ (I * k) =
        (((1 + k ^ 2) * J - k ^ 2 * (Real.sin φ * Real.cos φ) / W φ : ℝ) : ℂ) := by
      have h1k : (1 : ℂ) - (I * k) ^ 2 = ((1 + k ^ 2 : ℝ) : ℂ) := by
        rw [mul_pow, I_sq]; push_cast; ring
      have h1k0 : ((1 + k ^ 2 : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (by positivity : (0 : ℝ) < 1 + k ^ 2).ne'
      have hW0' : (W φ : ℂ) ≠ 0 := by exact_mod_cast (hW0 φ).ne'
      rw [hJ', hΔφ, h1k, eq_div_iff h1k0] at hcube
      rw [mul_pow, I_sq] at hcube
      push_cast at hcube ⊢
      linear_combination -hcube
    have hEθ : incEllIntEk θ κ = ((c * J : ℝ) : ℂ) := by
      rw [incEllIntEk_ofReal_eq_integral, hsub, hJ, ← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_ofReal]
      refine intervalIntegral.integral_congr fun u _ => ?_
      rw [(hpt u).2.2.2, ← ofReal_mul]
      exact congrArg ofReal (p19lR1_alg2 (hW0 u) (hW2 u) c)
    have hX : κ ^ 2 * Real.sin θ * Real.cos θ / Real.sqrt (1 - κ ^ 2 * Real.sin θ ^ 2) =
        k ^ 2 * (Real.sin φ * Real.cos φ) / (c * W φ) := p19lR1_imod_X k hφ1 hφ0
    rw [hEφ, hEθ, hX, hκ']
    have := p19lR1_alg_E (J := J) (X := k ^ 2 * (Real.sin φ * Real.cos φ) / (c * W φ))
      (sc := Real.sin φ * Real.cos φ) hc2 hc0 (hW0 φ) rfl
    rw [this]
    push_cast; ring
  · have hden : ∀ u, 0 < 1 - α2 * Real.sin u ^ 2 := fun u => by
      rcases le_or_gt α2 0 with h | h
      · nlinarith [sq_nonneg (Real.sin u)]
      · nlinarith [Real.sin_sq_le_one u]
    have hα' : α2 * Real.sin φ ^ 2 < 1 := by linarith [hden φ]
    have hα12 : α12 * Real.sin θ ^ 2 < 1 := by
      have h12 : α12 < 1 := by
        show (α2 + k ^ 2) / (1 + k ^ 2) < 1
        rw [div_lt_one (by positivity)]; linarith
      rcases le_or_gt α12 0 with h | h
      · nlinarith [sq_nonneg (Real.sin θ)]
      · nlinarith [Real.sin_sq_le_one θ]
    have hP1 : incEllIntPik φ α2 (I * k) =
        ∫ u in (0 : ℝ)..φ, (((1 - α2 * Real.sin u ^ 2)⁻¹ * (W u)⁻¹ : ℝ) : ℂ) := by
      rw [p19lR1_Pi_ofReal_of_lt hφ0 hφ1 hα']
      refine intervalIntegral.integral_congr fun u _ => ?_
      rw [(hpt u).1, show (1 - (α2 : ℂ) * (Real.sin u : ℂ) ^ 2)⁻¹ =
        (((1 - α2 * Real.sin u ^ 2)⁻¹ : ℝ) : ℂ) by push_cast; ring, ← ofReal_mul]
    have hP2 : incEllIntPik θ α12 κ =
        ∫ u in (0 : ℝ)..φ, ((c * W u / (1 - α2 * Real.sin u ^ 2) : ℝ) : ℂ) := by
      rw [p19lR1_Pi_ofReal_of_lt hθ0 hθ1 hα12, hsub]
      refine intervalIntegral.integral_congr fun u _ => ?_
      have hs : Real.sin (p19lR1_T k u) = c * Real.sin u / W u := p19lR1_sin_T k u
      rw [(hpt u).2.2.1, show (1 - (α12 : ℂ) * (Real.sin (p19lR1_T k u) : ℂ) ^ 2)⁻¹ =
        (((1 - α12 * Real.sin (p19lR1_T k u) ^ 2)⁻¹ : ℝ) : ℂ) by push_cast; ring,
        ← ofReal_mul, ← ofReal_mul, hs]
      exact congrArg ofReal (p19lR1_alg_P hc2 (hW0 u) (hW2 u) (hden u).ne')
    have hBc : Continuous fun u => c * (W u)⁻¹ := by
      refine continuous_const.mul (Continuous.inv₀ ?_ fun u => (hW0 u).ne')
      rw [hW]; fun_prop
    have hCc : Continuous fun u => c * W u / (1 - α2 * Real.sin u ^ 2) := by
      refine Continuous.div (continuous_const.mul ?_) (by fun_prop) fun u => (hden u).ne'
      rw [hW]; fun_prop
    have key : (∫ u in (0 : ℝ)..φ, (1 - α2 * Real.sin u ^ 2)⁻¹ * (W u)⁻¹) =
        κ' / α12 * (κ ^ 2 * (∫ u in (0 : ℝ)..φ, c * (W u)⁻¹) +
          κ' ^ 2 * α2 * ∫ u in (0 : ℝ)..φ, c * W u / (1 - α2 * Real.sin u ^ 2)) := by
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_add ((hBc.intervalIntegrable _ _).const_mul _)
          ((hCc.intervalIntegrable _ _).const_mul _), ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun u _ => ?_
      exact p19lR1_alg_Pi hc0 (hW0 u) hc2 (hW2 u) (hden u).ne' hαk
    rw [hP1, hF2, hP2, intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal,
      intervalIntegral.integral_ofReal, key]
    push_cast; ring

end DLMF.EllipticIntegrals
end
