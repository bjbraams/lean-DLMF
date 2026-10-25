/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.EllipticIntegrals.LegendreIdentities
public import DLMF.JacobiElliptic.SpecialValues
public import Mathlib.Analysis.SpecialFunctions.Arsinh

/-!
# Special cases of Legendre's integrals and of `R_C` (DLMF §19.6)

Statements of DLMF 19.6.1–19.6.15. DLMF's "`= ∞`" entries are stated as divergence of the norm
(or of the real part, for the real third-kind integrals) along the relevant one-sided limit;
DLMF's `lim_{φ→0} F(φ, k)/φ = 1` etc. are limits along `𝓝[≠] 0`. The third-kind integrals with
real `α² > 1` are Cauchy principal values (DLMF 19.6(i), 19.6(iv)); `c = csc²φ`.
`R_C` is ACQ19C's `symEllIntRC` (DLMF 19.2.17, principal value for `y < 0`).

The inverse Gudermannian of DLMF 19.6.8 is `gd⁻¹(φ) = ∫₀^φ sec t dt` (DLMF 4.23.41;
`DLMF.Elementary.inverseGudermannian`), written out here as that integral, and also as
`arsinh(tan φ)`.
-/

@[expose] public noncomputable section

open Complex Set Filter
open scoped Real Topology

namespace DLMF.EllipticIntegrals

open DLMF.JacobiElliptic

/-! ### §19.6(i) Complete elliptic integrals -/

theorem ei19a_jacobiComodulusk_zero : jacobiComodulusk 0 = 1 := by simp [jacobiComodulusk]

theorem ei19a_jacobiComodulusk_one : jacobiComodulusk 1 = 0 := by simp [jacobiComodulusk]

/-- DLMF 19.6.1: `K(0) = E(0) = K'(1) = E'(1) = π/2`. -/
@[dlmf 19.6.E1]
theorem compEllInt_special_pi_div_two :
    compEllIntKk 0 = π / 2 ∧ compEllIntEk 0 = π / 2 ∧ cCompEllIntKk 1 = π / 2 ∧
      cCompEllIntEk 1 = π / 2 := by
  have hE0 : compEllIntEk 0 = π / 2 := by
    rw [compEllIntEk_eq_integral]; simp
  refine ⟨by simp [compEllIntKk], hE0, ?_, ?_⟩
  · rw [(cCompEllIntKk_of_re_pos (k := 1) (Or.inl (by simp))).1, compEllIntKk_jacobiComodulusk]
    simp [compEllIntKpk]
  · rw [(cCompEllIntKk_of_re_pos (k := 1) (Or.inl (by simp))).2, ei19a_jacobiComodulusk_one, hE0]

/-- DLMF 19.6.1: `E(1) = E'(0) = 1`. -/
@[dlmf 19.6.E1]
theorem compEllInt_special_one : compEllIntEk 1 = 1 ∧ cCompEllIntEk 0 = 1 := by
  have h1 : compEllIntEk 1 = 1 := by
    rw [compEllIntEk_eq_ofReal (m := 1) (by simp) le_rfl, DLMF.Elliptic.Real.compEllIntEm_one,
      ofReal_one]
  refine ⟨h1, ?_⟩
  rw [(cCompEllIntKk_of_re_pos (k := 0) (Or.inr (by simp))).2, ei19a_jacobiComodulusk_zero, h1]

/-- DLMF 19.6.1: `K(1) = ∞`, as `|K(k)| → ∞` for `k → 1-` (from the admitted
`DLMF.JacobiElliptic.tendsto_norm_compEllIntKk_one`). -/
@[dlmf 19.6.E1]
theorem tendsto_norm_compEllIntKk_one' :
    Tendsto (fun k : ℝ => ‖compEllIntKk k‖) (𝓝[<] 1) atTop :=
  tendsto_norm_compEllIntKk_one

/-- DLMF 19.6.1: `K'(0) = ∞`, as `|K'(k)| → ∞` for `k → 0+` (from the admitted
`DLMF.JacobiElliptic.tendsto_norm_compEllIntKpk_zero`). -/
@[dlmf 19.6.E1]
theorem tendsto_norm_cCompEllIntKk_zero :
    Tendsto (fun k : ℝ => ‖cCompEllIntKk k‖) (𝓝[>] 0) atTop := by
  refine tendsto_norm_compEllIntKpk_zero.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with k hk
  rw [(cCompEllIntKk_of_re_pos (k := k) (Or.inl (by simpa using hk))).1,
    compEllIntKk_jacobiComodulusk]

/-- **Admitted.** DLMF 19.6.2: `Π(k², k) = E(k)/k'²` (DLMF: `k² < 1`; here the principal domain
`1 - k² ∈ ℂ \ (-∞, 0]`). -/
@[dlmf 19.6.E2]
theorem compEllIntPik_sq_self {k : ℂ} (hk : 1 - k ^ 2 ∈ slitPlane) :
    compEllIntPik (k ^ 2) k = compEllIntEk k / (1 - k ^ 2) := by
  sorry

/-- **Admitted.** DLMF 19.6.2: `Π(-k, k) = π/(4(1 + k)) + K(k)/2` for real `k` with `k² < 1`. -/
@[dlmf 19.6.E2]
theorem compEllIntPik_neg_self {k : ℝ} (hk : k ^ 2 < 1) :
    compEllIntPik (-k) k = π / (4 * (1 + k)) + compEllIntKk k / 2 := by
  sorry

/-- DLMF 19.6.13 (first relation): `Π(φ, 0, k) = F(φ, k)` for all complex `φ`, `k`. -/
@[dlmf 19.6.E13]
theorem incEllIntPik_zero (φ k : ℂ) : incEllIntPik φ 0 k = incEllIntFk φ k := by
  rw [incEllIntPik_eq_segmentIntegral (δ := 1) one_pos (fun t _ => by simp), incEllIntFk]
  simp

/-- DLMF 19.6.3: `Π(α², 0) = π/(2√(1 - α²))` for real `α² < 1`, and `Π(0, k) = K(k)`. -/
@[dlmf 19.6.E3]
theorem compEllIntPik_special {α2 : ℝ} (hα : α2 < 1) (k : ℂ) :
    compEllIntPik α2 0 = π / (2 * Real.sqrt (1 - α2)) ∧ compEllIntPik 0 k = compEllIntKk k := by
  constructor
  · rw [compEllIntPik, show ((π : ℂ) / 2) = ((π / 2 : ℝ) : ℂ) by push_cast; ring,
      incEllIntPik_eq_ofReal (m := 0) (by simp) zero_le_one hα,
      ← DLMF.Elliptic.Real.compEllIntPim, DLMF.Elliptic.Real.compEllIntPim_param_zero hα]
    push_cast; ring
  · rw [compEllIntPik, incEllIntPik_zero, compEllIntKk_eq_incEllIntFk]

/-- **Admitted.** DLMF 19.6.4: for real `k` with `k² < 1`, `Π(α², k) → +∞` as `α² → 1-`; for real
`α² < 1`, `Π(α², k) → +∞` as `k² → 1-` (`∞ · sign(1 - α²)`; the case `α² > 1` is in 19.6.6). -/
@[dlmf 19.6.E4]
theorem tendsto_compEllIntPik {k α2 : ℝ} (hk : k ^ 2 < 1) (hα : α2 < 1) :
    Tendsto (fun a : ℝ => (compEllIntPik a k).re) (𝓝[<] 1) atTop ∧
      Tendsto (fun k : ℝ => (compEllIntPik α2 k).re) (𝓝[<] 1) atTop := by
  sorry

/-- **Admitted.** DLMF 19.6.5: for real `1 < α²` and real `k` with `k² < 1`, the Cauchy principal
value satisfies `Π(α², k) = K(k) - Π(k²/α², k)`. -/
@[dlmf 19.6.E5]
theorem compEllIntPik_of_one_lt {α2 k : ℝ} (hα : 1 < α2) (hk : k ^ 2 < 1) :
    compEllIntPik α2 k = compEllIntKk k - compEllIntPik (k ^ 2 / α2 : ℝ) k := by
  sorry

/-- **Admitted.** DLMF 19.6.6: for real `1 < α²` (Cauchy principal values), `Π(α², 0) = 0`;
for real `k` with `k² < 1`, `Π(α², k) → K(k) - E(k)/k'²` as `α² → 1+`; and for `1 < α²`,
`Π(α², k) → -∞` as `k² → 1-`. -/
@[dlmf 19.6.E6]
theorem compEllIntPik_of_one_lt_special {α2 k : ℝ} (hα : 1 < α2) (hk : k ^ 2 < 1) :
    compEllIntPik α2 0 = 0 ∧
      Tendsto (fun a : ℝ => compEllIntPik a k) (𝓝[>] 1)
        (𝓝 (compEllIntKk k - compEllIntEk k / (1 - k ^ 2))) ∧
      Tendsto (fun k : ℝ => (compEllIntPik α2 k).re) (𝓝[<] 1) atBot := by
  sorry

/-! ### §19.6(ii) `F(φ, k)` -/

/-- DLMF 19.6.7: `F(0, k) = 0`, `F(φ, 0) = φ` and `F(π/2, k) = K(k)` for all complex `φ`, `k`. -/
@[dlmf 19.6.E7]
theorem incEllIntFk_special (φ k : ℂ) :
    incEllIntFk 0 k = 0 ∧ incEllIntFk φ 0 = φ ∧ incEllIntFk (π / 2) k = compEllIntKk k := by
  refine ⟨by simp [incEllIntFk, ei19a_segmentIntegral], by simp [incEllIntFk,
    ei19a_segmentIntegral], (compEllIntKk_eq_incEllIntFk k).symm⟩

/-- **Admitted.** DLMF 19.6.7: `F(π/2, 1) = ∞`, as `|F(φ, 1)| → ∞` for real `φ → π/2-`; and
`lim_{φ→0} F(φ, k)/φ = 1`. -/
@[dlmf 19.6.E7]
theorem incEllIntFk_limits (k : ℂ) :
    Tendsto (fun φ : ℝ => ‖incEllIntFk φ 1‖) (𝓝[<] (π / 2)) atTop ∧
      Tendsto (fun φ : ℂ => incEllIntFk φ k / φ) (𝓝[≠] 0) (𝓝 1) := by
  sorry

/-- For real `|φ| < π/2`, `F(φ, 1) = ∫₀^φ sec θ dθ = gd⁻¹(φ)` (DLMF 19.6.8, second equality, with
DLMF's definition 4.23.41 of `gd⁻¹`). -/
@[dlmf 19.6.E8]
theorem incEllIntFk_one_eq_integral_sec {φ : ℝ} (hφ : |φ| < π / 2) :
    incEllIntFk φ 1 = ((∫ θ in (0 : ℝ)..φ, (Real.cos θ)⁻¹ : ℝ) : ℂ) := by
  rw [incEllIntFk_eq_ofReal (m := 1) (by simp) le_rfl, DLMF.Elliptic.Real.incEllIntFm]
  congr 1
  refine intervalIntegral.integral_congr fun θ hθ => ?_
  have hθ' : |θ| < π / 2 := by
    rcases le_total 0 φ with h | h
    · rw [uIcc_of_le h] at hθ
      rw [abs_lt] at hφ ⊢; constructor <;> linarith [hθ.1, hθ.2]
    · rw [uIcc_of_ge h] at hθ
      rw [abs_lt] at hφ ⊢; constructor <;> linarith [hθ.1, hθ.2]
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [neg_abs_le θ],
    by linarith [le_abs_self θ]⟩
  rw [one_mul, ← Real.cos_sq', Real.rpow_neg (sq_nonneg _), ← Real.sqrt_eq_rpow,
    Real.sqrt_sq hc.le]

/-- **Admitted.** DLMF 19.6.8: `F(φ, 1) = (sin φ) R_C(1, cos²φ) = gd⁻¹(φ) = arsinh(tan φ)` for
real `|φ| < π/2`. -/
@[dlmf 19.6.E8]
theorem incEllIntFk_one {φ : ℝ} (hφ : |φ| < π / 2) :
    incEllIntFk φ 1 = Real.sin φ * symEllIntRC 1 ((Real.cos φ : ℂ) ^ 2) ∧
      incEllIntFk φ 1 = (Real.arsinh (Real.tan φ) : ℂ) := by
  sorry

/-! ### §19.6(iii) `E(φ, k)` -/

/-- DLMF 19.6.9: `E(0, k) = 0`, `E(φ, 0) = φ`, `E(π/2, k) = E(k)` for all complex `φ`, `k`. -/
@[dlmf 19.6.E9]
theorem incEllIntEk_special (φ k : ℂ) :
    incEllIntEk 0 k = 0 ∧ incEllIntEk φ 0 = φ ∧ incEllIntEk (π / 2) k = compEllIntEk k :=
  ⟨by simp [incEllIntEk, ei19a_segmentIntegral], by simp [incEllIntEk, ei19a_segmentIntegral], rfl⟩

/-- DLMF 19.6.9: `E(φ, 1) = sin φ` for real `|φ| ≤ π/2` (for larger real `φ`, `E(φ, 1)` is
`∫₀^φ |cos θ| dθ ≠ sin φ`: the printed identity holds on DLMF's principal range); in particular
`E(π/2, 1) = 1`. -/
@[dlmf 19.6.E9]
theorem incEllIntEk_one {φ : ℝ} (hφ : |φ| ≤ π / 2) : incEllIntEk φ 1 = Real.sin φ := by
  rw [incEllIntEk_eq_ofReal (m := 1) (by simp) le_rfl, DLMF.Elliptic.Real.incEllIntEm]
  have h : ∀ θ ∈ uIcc (0 : ℝ) φ, (1 - 1 * Real.sin θ ^ 2) ^ (1 / 2 : ℝ) = Real.cos θ := by
    intro θ hθ
    have hθ' : |θ| ≤ π / 2 := by
      rcases le_total 0 φ with h | h
      · rw [uIcc_of_le h] at hθ
        rw [abs_le] at hφ ⊢; constructor <;> linarith [hθ.1, hθ.2]
      · rw [uIcc_of_ge h] at hθ
        rw [abs_le] at hφ ⊢; constructor <;> linarith [hθ.1, hθ.2]
    rw [one_mul, ← Real.cos_sq', ← Real.sqrt_eq_rpow, Real.sqrt_sq (Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [neg_abs_le θ], by linarith [le_abs_self θ]⟩)]
  rw [intervalIntegral.integral_congr h, integral_cos]
  simp

/-- DLMF 19.6.9: `E(π/2, 1) = 1`. -/
@[dlmf 19.6.E9]
theorem incEllIntEk_pi_div_two_one : incEllIntEk (π / 2) 1 = 1 := by
  have h := incEllIntEk_one (φ := π / 2) (by rw [abs_of_pos (by positivity)])
  rw [show ((π : ℂ) / 2) = ((π / 2 : ℝ) : ℂ) by push_cast; ring, h, Real.sin_pi_div_two,
    ofReal_one]

/-- **Admitted.** DLMF 19.6.9 for complex amplitude: `E(φ, 1) = sin φ` when `|Re φ| < π/2`. -/
@[dlmf 19.6.E9]
theorem incEllIntEk_one_complex {φ : ℂ} (hφ : |φ.re| < π / 2) :
    incEllIntEk φ 1 = Complex.sin φ := by
  sorry

/-- **Admitted.** DLMF 19.6.10: `lim_{φ→0} E(φ, k)/φ = 1`. -/
@[dlmf 19.6.E10]
theorem tendsto_incEllIntEk_div (k : ℂ) :
    Tendsto (fun φ : ℂ => incEllIntEk φ k / φ) (𝓝[≠] 0) (𝓝 1) := by
  sorry

/-! ### §19.6(iv) `Π(φ, α², k)` -/

/-- DLMF 19.6.11: `Π(0, α², k) = 0` and `Π(φ, 0, 0) = φ` for all complex `φ`, `α²`, `k`. -/
@[dlmf 19.6.E11]
theorem incEllIntPik_special (φ α2 k : ℂ) : incEllIntPik 0 α2 k = 0 ∧ incEllIntPik φ 0 0 = φ := by
  refine ⟨ei19a_pvSegmentIntegral_zero _ _, ?_⟩
  rw [incEllIntPik_zero, (incEllIntFk_special φ 0).2.1]

/-- **Admitted.** DLMF 19.6.11: `Π(φ, 1, 0) = tan φ` for real `|φ| < π/2`. -/
@[dlmf 19.6.E11]
theorem incEllIntPik_one_zero {φ : ℝ} (hφ : |φ| < π / 2) :
    incEllIntPik φ 1 0 = Real.tan φ := by
  sorry

/-- **Admitted.** DLMF 19.6.12: with `c = csc²φ ≠ α²`, for real `0 < φ < π/2` and real `α²`
(Cauchy principal values when `α² > c`),
`Π(φ, α², 0) = R_C(c - 1, c - α²)`,
`Π(φ, α², 1) = (R_C(c, c - 1) - α² R_C(c, c - α²))/(1 - α²)` (`α² ≠ 1`), and
`Π(φ, 1, 1) = (R_C(c, c - 1) + √c/(c - 1))/2`. -/
@[dlmf 19.6.E12]
theorem incEllIntPik_special_RC {φ α2 : ℝ} (h0 : 0 < φ) (h1 : φ < π / 2)
    (hα : α2 ≠ 1 / Real.sin φ ^ 2) :
    incEllIntPik φ α2 0 =
        symEllIntRC (1 / Real.sin φ ^ 2 - 1 : ℝ) (1 / Real.sin φ ^ 2 - α2 : ℝ) ∧
      (α2 ≠ 1 → incEllIntPik φ α2 1 =
        (symEllIntRC (1 / Real.sin φ ^ 2 : ℝ) (1 / Real.sin φ ^ 2 - 1 : ℝ) -
          α2 * symEllIntRC (1 / Real.sin φ ^ 2 : ℝ) (1 / Real.sin φ ^ 2 - α2 : ℝ)) / (1 - α2)) ∧
      incEllIntPik φ 1 1 = (symEllIntRC (1 / Real.sin φ ^ 2 : ℝ) (1 / Real.sin φ ^ 2 - 1 : ℝ) +
        (Real.sqrt (1 / Real.sin φ ^ 2) / (1 / Real.sin φ ^ 2 - 1) : ℝ)) / 2 := by
  sorry

/-- **Admitted.** DLMF 19.6.13: with `Δ = √(1 - k² sin²φ)`, for real `|φ| < π/2` and `k` in the
principal domain `1 - k² ∈ ℂ \ (-∞, 0]`,
`Π(φ, k², k) = (E(φ, k) - k² sin φ cos φ/Δ)/k'²` and
`Π(φ, 1, k) = F(φ, k) - (E(φ, k) - Δ tan φ)/k'²`. -/
@[dlmf 19.6.E13]
theorem incEllIntPik_special_k {φ : ℝ} (hφ : |φ| < π / 2) {k : ℂ} (hk : 1 - k ^ 2 ∈ slitPlane) :
    incEllIntPik φ (k ^ 2) k = (incEllIntEk φ k - k ^ 2 * Real.sin φ * Real.cos φ /
        (1 - k ^ 2 * (Real.sin φ : ℂ) ^ 2) ^ (1 / 2 : ℂ)) / (1 - k ^ 2) ∧
      incEllIntPik φ 1 k = incEllIntFk φ k - (incEllIntEk φ k -
        (1 - k ^ 2 * (Real.sin φ : ℂ) ^ 2) ^ (1 / 2 : ℂ) * Real.tan φ) / (1 - k ^ 2) := by
  sorry

/-- DLMF 19.6.14: `Π(π/2, α², k) = Π(α², k)`. -/
@[dlmf 19.6.E14]
theorem incEllIntPik_pi_div_two (α2 k : ℂ) : incEllIntPik (π / 2) α2 k = compEllIntPik α2 k := rfl

/-- **Admitted.** DLMF 19.6.14: `lim_{φ→0} Π(φ, α², k)/φ = 1`. -/
@[dlmf 19.6.E14]
theorem tendsto_incEllIntPik_div (α2 k : ℂ) :
    Tendsto (fun φ : ℂ => incEllIntPik φ α2 k / φ) (𝓝[≠] 0) (𝓝 1) := by
  sorry

/-! ### §19.6(v) `R_C(x, y)` -/

/-- **Admitted.** DLMF 19.6.15: `R_C(x, x) = x^{-1/2}` (`x ∈ ℂ \ (-∞, 0]`);
`R_C(λx, λy) = λ^{-1/2} R_C(x, y)` (real `λ > 0`, `x` not a negative real, `y ≠ 0`);
`R_C(0, y) = (π/2) y^{-1/2}` for `|ph y| < π`; and `R_C(0, y) = 0` for `y < 0` (principal
value). -/
@[dlmf 19.6.E15]
theorem symEllIntRC_special :
    (∀ x : ℂ, x ∈ slitPlane → symEllIntRC x x = x ^ (-(1 / 2 : ℂ))) ∧
      (∀ (l : ℝ) (x y : ℂ), 0 < l → symEllIntArg x → y ≠ 0 →
        symEllIntRC (l * x) (l * y) = (l : ℂ) ^ (-(1 / 2 : ℂ)) * symEllIntRC x y) ∧
      (∀ y : ℂ, y ∈ slitPlane → symEllIntRC 0 y = π / 2 * y ^ (-(1 / 2 : ℂ))) ∧
      (∀ y : ℝ, y < 0 → symEllIntRC 0 y = 0) := by
  sorry

/-- **Admitted.** DLMF 19.6.15: `R_C(x, y) → +∞` as `y → 0+` or `y → 0-`, for real `x > 0`. -/
@[dlmf 19.6.E15]
theorem tendsto_symEllIntRC_zero {x : ℝ} (hx : 0 < x) :
    Tendsto (fun y : ℝ => (symEllIntRC x y).re) (𝓝[≠] 0) atTop := by
  sorry

end DLMF.EllipticIntegrals
