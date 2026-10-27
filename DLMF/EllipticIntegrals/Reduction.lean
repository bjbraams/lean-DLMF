/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.EllipticIntegrals.Legendre

/-!
# Reduction of general elliptic integrals (DLMF §19.14)

§19.14(i) gives examples of the reduction of elliptic integrals to Legendre's `F(φ, k)`
(`incEllIntFk`, at real arguments). In (19.14.1)–(19.14.3) DLMF assumes the integrand and
`cos φ` nonnegative; with `φ = arccos(…) ∈ [0, π/2]` this is the range of `x` stated in each
theorem (`1 ≤ x ≤ √3 + 1`, `1 - √3 ≤ x ≤ 1`, `|x| ≤ 1`). In (19.14.4)–(19.14.6) the amplitude
`φ ∈ [0, π/2]` is given by `sin²φ` (19.14.5); `α ≤ β ≤ γ` is the ordered permutation of
`0, a₁b₂, a₂b₁` (stated as a multiset equality), not all zero.

The special cases (19.14.7), (19.14.9), (19.14.10) are derived from (19.14.4)–(19.14.6) by
computing `U`; (19.14.8) (`x = ∞`) is the improper integral over `(y, ∞)`.

§19.14(ii) (Legendre's reduction of every elliptic integral to `F`, `E`, `Π` and elementary
functions, and the reduction algorithms of Labahn–Mutrie, Byrd–Friedman and Erdélyi et al.) is
descriptive and is not formalized; the symmetric-integral reduction is §19.29.

## References

* NIST DLMF §19.14.
-/

@[expose] public noncomputable section

open Complex Set
open scoped Real

namespace DLMF.EllipticIntegrals

/-! ### Examples (19.14.1)–(19.14.3) -/

/-- DLMF 19.14.1: `∫₁^x dt/√(t³ - 1) = 3^{-1/4} F(φ, k)`,
`cos φ = (√3 + 1 - x)/(√3 - 1 + x)`, `k² = (2 - √3)/4`, for `1 ≤ x ≤ √3 + 1`. -/
@[dlmf 19.14.E1]
theorem integral_inv_sqrt_cube_sub_one {x : ℝ} (h1 : 1 ≤ x) (h2 : x ≤ Real.sqrt 3 + 1) :
    ((∫ t in (1 : ℝ)..x, (Real.sqrt (t ^ 3 - 1))⁻¹ : ℝ) : ℂ) =
      ((3 : ℝ) ^ (-(1 / 4) : ℝ) : ℝ) *
        incEllIntFk (Real.arccos ((Real.sqrt 3 + 1 - x) / (Real.sqrt 3 - 1 + x)))
          (Real.sqrt ((2 - Real.sqrt 3) / 4)) := by
  sorry

/-- DLMF 19.14.2: `∫ₓ¹ dt/√(1 - t³) = 3^{-1/4} F(φ, k)`,
`cos φ = (√3 - 1 + x)/(√3 + 1 - x)`, `k² = (2 + √3)/4`, for `1 - √3 ≤ x ≤ 1`. -/
@[dlmf 19.14.E2]
theorem integral_inv_sqrt_one_sub_cube {x : ℝ} (h1 : 1 - Real.sqrt 3 ≤ x) (h2 : x ≤ 1) :
    ((∫ t in x..1, (Real.sqrt (1 - t ^ 3))⁻¹ : ℝ) : ℂ) =
      ((3 : ℝ) ^ (-(1 / 4) : ℝ) : ℝ) *
        incEllIntFk (Real.arccos ((Real.sqrt 3 - 1 + x) / (Real.sqrt 3 + 1 - x)))
          (Real.sqrt ((2 + Real.sqrt 3) / 4)) := by
  sorry

/-- The substitution `φ = 2 arctan t` of (19.14.3):
`(1 - ½ sin²(2 arctan t))^{-1/2} · 2/(1 + t²) = 2/√(1 + t⁴)`. -/
lemma ei19b_quartic_integrand (t : ℝ) :
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
lemma ei19b_integral_quartic_nonneg (x : ℝ) :
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
  simp only [Function.comp_def, ei19b_quartic_integrand, Real.arctan_zero, mul_zero] at hsub
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
    rw [hneg, ei19b_integral_quartic_nonneg (-x),
      show (1 - x ^ 2) / (1 + x ^ 2) = (1 - (-x) ^ 2) / (1 + (-x) ^ 2) by ring,
      harc (-x) (by linarith), sign_neg h, SignType.coe_neg_one]
    push_cast
    ring
  · simp
  · rw [ei19b_integral_quartic_nonneg x, harc x h.le, sign_pos h, SignType.coe_one]
    push_cast
    ring

/-! ### Two quadratic factors (19.14.4)–(19.14.10) -/

/-- DLMF 19.14.6: `U = (x √((a₁ + b₁y²)(a₂ + b₂y²)) + y √((a₁ + b₁x²)(a₂ + b₂x²)))/(x² - y²)`. -/
def ei19b_redU (a₁ b₁ a₂ b₂ x y : ℝ) : ℝ :=
  (x * Real.sqrt ((a₁ + b₁ * y ^ 2) * (a₂ + b₂ * y ^ 2)) +
    y * Real.sqrt ((a₁ + b₁ * x ^ 2) * (a₂ + b₂ * x ^ 2))) / (x ^ 2 - y ^ 2)

/-- The hypotheses of DLMF 19.14.4: `0 ≤ y < x`, both quadratics positive on `(y, x)`, and
`α ≤ β ≤ γ` the ordered permutation of `0, a₁b₂, a₂b₁`, not all zero. -/
structure ei19b_RedHyp (a₁ b₁ a₂ b₂ x y α β γ : ℝ) : Prop where
  y_nonneg : 0 ≤ y
  y_lt_x : y < x
  pos : ∀ t ∈ Ioo y x, 0 < a₁ + b₁ * t ^ 2 ∧ 0 < a₂ + b₂ * t ^ 2
  perm : ({α, β, γ} : Multiset ℝ) = {0, a₁ * b₂, a₂ * b₁}
  le₁ : α ≤ β
  le₂ : β ≤ γ
  not_all_zero : ¬ (a₁ * b₂ = 0 ∧ a₂ * b₁ = 0)

/-- DLMF 19.14.4–19.14.6:
`∫_y^x dt/√((a₁ + b₁t²)(a₂ + b₂t²)) = (γ - α)^{-1/2} F(φ, k)`, `k² = (γ - β)/(γ - α)`,
`sin²φ = (γ - α)/(U² + γ)` with `U` of (19.14.6), `φ ∈ [0, π/2]`. -/
@[dlmf 19.14.E4, dlmf 19.14.E5, dlmf 19.14.E6]
theorem integral_inv_sqrt_two_quadratics {a₁ b₁ a₂ b₂ x y α β γ : ℝ}
    (h : ei19b_RedHyp a₁ b₁ a₂ b₂ x y α β γ) :
    ((∫ t in y..x, (Real.sqrt ((a₁ + b₁ * t ^ 2) * (a₂ + b₂ * t ^ 2)))⁻¹ : ℝ) : ℂ) =
      ((Real.sqrt (γ - α))⁻¹ : ℝ) *
        incEllIntFk (Real.arcsin (Real.sqrt ((γ - α) / (ei19b_redU a₁ b₁ a₂ b₂ x y ^ 2 + γ))))
          (Real.sqrt ((γ - β) / (γ - α))) := by
  sorry

/-- A function continuous on `[y, x]` and positive on `(y, x)` is nonnegative at `x`. -/
lemma ei19b_nonneg_right {f : ℝ → ℝ} (hf : Continuous f) {x y : ℝ} (hyx : y < x)
    (hpos : ∀ t ∈ Ioo y x, 0 < f t) : 0 ≤ f x :=
  ge_of_tendsto (hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (Filter.eventually_of_mem (Ioo_mem_nhdsLT hyx) fun t ht => (hpos t ht).le)

/-- A function continuous on `[y, x]` and positive on `(y, x)` is nonnegative at `y`. -/
lemma ei19b_nonneg_left {f : ℝ → ℝ} (hf : Continuous f) {x y : ℝ} (hyx : y < x)
    (hpos : ∀ t ∈ Ioo y x, 0 < f t) : 0 ≤ f y :=
  ge_of_tendsto (hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (Filter.eventually_of_mem (Ioo_mem_nhdsGT hyx) fun t ht => (hpos t ht).le)

/-- The product of the quadratics is nonnegative at both endpoints. -/
lemma ei19b_prod_nonneg {a₁ b₁ a₂ b₂ x y α β γ : ℝ} (h : ei19b_RedHyp a₁ b₁ a₂ b₂ x y α β γ) :
    0 ≤ (a₁ + b₁ * x ^ 2) * (a₂ + b₂ * x ^ 2) ∧ 0 ≤ (a₁ + b₁ * y ^ 2) * (a₂ + b₂ * y ^ 2) := by
  have hc : Continuous fun t : ℝ => (a₁ + b₁ * t ^ 2) * (a₂ + b₂ * t ^ 2) := by fun_prop
  have hp : ∀ t ∈ Ioo y x, 0 < (a₁ + b₁ * t ^ 2) * (a₂ + b₂ * t ^ 2) := fun t ht =>
    mul_pos (h.pos t ht).1 (h.pos t ht).2
  exact ⟨ei19b_nonneg_right hc h.y_lt_x hp, ei19b_nonneg_left hc h.y_lt_x hp⟩

/-- DLMF 19.14.7 (the case `y = 0` of 19.14.4–19.14.6): `sin²φ = (γ - α)x²/(a₁a₂ + γx²)`. -/
@[dlmf 19.14.E7]
theorem integral_inv_sqrt_two_quadratics_zero {a₁ b₁ a₂ b₂ x α β γ : ℝ}
    (h : ei19b_RedHyp a₁ b₁ a₂ b₂ x 0 α β γ) :
    ((∫ t in (0 : ℝ)..x, (Real.sqrt ((a₁ + b₁ * t ^ 2) * (a₂ + b₂ * t ^ 2)))⁻¹ : ℝ) : ℂ) =
      ((Real.sqrt (γ - α))⁻¹ : ℝ) *
        incEllIntFk (Real.arcsin (Real.sqrt ((γ - α) * x ^ 2 / (a₁ * a₂ + γ * x ^ 2))))
          (Real.sqrt ((γ - β) / (γ - α))) := by
  rw [integral_inv_sqrt_two_quadratics h]
  have hx : 0 < x := h.y_lt_x
  have h0 := (ei19b_prod_nonneg h).2
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero] at h0
  have hU : ei19b_redU a₁ b₁ a₂ b₂ x 0 ^ 2 = a₁ * a₂ / x ^ 2 := by
    unfold ei19b_redU
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
  sorry

/-- DLMF 19.14.9 (the case `a₁ + b₁y² = 0` of 19.14.4–19.14.6):
`sin²φ = (γ - α)(x² - y²)/(γ(x² - y²) - a₁(a₂ + b₂x²))`. -/
@[dlmf 19.14.E9]
theorem integral_inv_sqrt_two_quadratics_left {a₁ b₁ a₂ b₂ x y α β γ : ℝ}
    (h : ei19b_RedHyp a₁ b₁ a₂ b₂ x y α β γ) (hy : a₁ + b₁ * y ^ 2 = 0) :
    ((∫ t in y..x, (Real.sqrt ((a₁ + b₁ * t ^ 2) * (a₂ + b₂ * t ^ 2)))⁻¹ : ℝ) : ℂ) =
      ((Real.sqrt (γ - α))⁻¹ : ℝ) *
        incEllIntFk (Real.arcsin (Real.sqrt ((γ - α) * (x ^ 2 - y ^ 2) /
            (γ * (x ^ 2 - y ^ 2) - a₁ * (a₂ + b₂ * x ^ 2)))))
          (Real.sqrt ((γ - β) / (γ - α))) := by
  rw [integral_inv_sqrt_two_quadratics h]
  have hxy : 0 < x ^ 2 - y ^ 2 := by
    have := h.y_nonneg; have := h.y_lt_x; nlinarith
  have h0 := (ei19b_prod_nonneg h).1
  have hU : ei19b_redU a₁ b₁ a₂ b₂ x y ^ 2 = -a₁ * (a₂ + b₂ * x ^ 2) / (x ^ 2 - y ^ 2) := by
    unfold ei19b_redU
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
    (h : ei19b_RedHyp a₁ b₁ a₂ b₂ x y α β γ) (hx : a₁ + b₁ * x ^ 2 = 0) :
    ((∫ t in y..x, (Real.sqrt ((a₁ + b₁ * t ^ 2) * (a₂ + b₂ * t ^ 2)))⁻¹ : ℝ) : ℂ) =
      ((Real.sqrt (γ - α))⁻¹ : ℝ) *
        incEllIntFk (Real.arcsin (Real.sqrt ((γ - α) * (y ^ 2 - x ^ 2) /
            (γ * (y ^ 2 - x ^ 2) - a₁ * (a₂ + b₂ * y ^ 2)))))
          (Real.sqrt ((γ - β) / (γ - α))) := by
  rw [integral_inv_sqrt_two_quadratics h]
  have hxy : 0 < x ^ 2 - y ^ 2 := by
    have := h.y_nonneg; have := h.y_lt_x; nlinarith
  have hx0 : 0 < x := lt_of_le_of_lt h.y_nonneg h.y_lt_x
  have h0 := (ei19b_prod_nonneg h).2
  have hU : ei19b_redU a₁ b₁ a₂ b₂ x y ^ 2 = a₁ * (a₂ + b₂ * y ^ 2) / (x ^ 2 - y ^ 2) := by
    unfold ei19b_redU
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
