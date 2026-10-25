/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.EllipticIntegrals.Legendre
public import DLMF.EllipticIntegrals.Symmetric
public import DLMF.EllipticIntegrals.Inequalities

/-!
# Addition theorems for Legendre's integrals (DLMF §19.11)

The addition theorems are stated for real modulus `k` with `k² < 1` and real amplitudes, the
setting of DLMF's qualifications in §19.11(i). The Legendre integrals are the complex DLMF
integrals `incEllIntFk`, `incEllIntEk`, `incEllIntPik` (and `compEllIntKk`, `compEllIntEk`,
`compEllIntPik`) at real arguments; `R_C` is `symEllIntRC`.

**The amplitude `ψ`.** DLMF defines `ψ` by `sin ψ` (19.11.3) and lists `cos ψ` (19.11.4) as a
further property. For `θ, φ ∈ [0, π/2]` both formulas are needed to fix `ψ ∈ [0, π]` (the sine
alone does not distinguish `ψ` from `π - ψ`); the theorems take `ψ ∈ [0, π]` with both
`sin ψ` and `cos ψ` given, and `addition_sin_sq_add_cos_sq` shows that such a `ψ` exists.
Likewise for the duplication formulas, with (19.11.14) and the first formula of (19.11.15).

**Branches in (19.11.5), (19.11.10), (19.11.16).** DLMF warns that "care has to be taken with
the multivalued functions in (19.11.5)". With DLMF's principal `R_C` (Cauchy principal value
for a negative second argument) the formula (19.11.5) holds numerically (mpmath, 3000 random
samples) exactly when `α² < 1` and `α² (1 - cos θ cos φ cos ψ) < 1`, the region of (19.11.6_5);
it fails outside it. The theorems are stated on this region (with `θ, φ ∈ (0, π/2)`, so that
the cosecants are finite). The duplication formula (19.11.16) is the case `φ = θ`, with the
condition `α² (1 - cos²θ cos ψ) < 1`; (19.11.10) holds for all real `α² < 1`.
In (19.11.6_5) DLMF allows `α² = k²`, where `δ = 0` and the right side is a limit; the theorem
assumes `k² < α²`.

## References

* NIST DLMF §19.11.
-/

@[expose] public noncomputable section

open Complex Set
open scoped Real

namespace DLMF.EllipticIntegrals

open DLMF.JacobiElliptic

/-- `Δ(θ) = √(1 - k² sin²θ)` (DLMF 19.11.3), real. -/
def ei19b_delta (k θ : ℝ) : ℝ := Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2)

/-- The right side of (19.11.3): `sin ψ` for the addition of `θ` and `φ`. -/
def ei19b_addSin (k θ φ : ℝ) : ℝ :=
  (Real.sin θ * Real.cos φ * ei19b_delta k φ + Real.sin φ * Real.cos θ * ei19b_delta k θ) /
    (1 - k ^ 2 * Real.sin θ ^ 2 * Real.sin φ ^ 2)

/-- The right side of the first formula (19.11.4): `cos ψ` for the addition of `θ` and `φ`. -/
def ei19b_addCos (k θ φ : ℝ) : ℝ :=
  (Real.cos θ * Real.cos φ - Real.sin θ * Real.sin φ * ei19b_delta k θ * ei19b_delta k φ) /
    (1 - k ^ 2 * Real.sin θ ^ 2 * Real.sin φ ^ 2)

/-! ### §19.11(i) General formulas -/

/-- DLMF 19.11.3–19.11.4 (consistency): `sin²ψ + cos²ψ = 1` for the expressions (19.11.3) and
(19.11.4), real `k² < 1`, all real `θ, φ`; hence an amplitude `ψ` with these sine and cosine
exists. -/
@[dlmf 19.11.E3, dlmf 19.11.E4]
theorem addition_sin_sq_add_cos_sq {k : ℝ} (hk : k ^ 2 < 1) (θ φ : ℝ) :
    ei19b_addSin k θ φ ^ 2 + ei19b_addCos k θ φ ^ 2 = 1 := by
  set a := Real.sin θ
  set b := Real.cos θ
  set c := Real.sin φ
  set d := Real.cos φ
  set P := ei19b_delta k θ
  set Q := ei19b_delta k φ
  have hP : P ^ 2 = 1 - k ^ 2 * a ^ 2 := Real.sq_sqrt (by nlinarith [Real.sin_sq_le_one θ])
  have hQ : Q ^ 2 = 1 - k ^ 2 * c ^ 2 := Real.sq_sqrt (by nlinarith [Real.sin_sq_le_one φ])
  have hab : a ^ 2 + b ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  have hcd : c ^ 2 + d ^ 2 = 1 := Real.sin_sq_add_cos_sq φ
  have ha1 : a ^ 2 ≤ 1 := Real.sin_sq_le_one θ
  have hc1 : c ^ 2 ≤ 1 := Real.sin_sq_le_one φ
  have hac : a ^ 2 * c ^ 2 ≤ 1 := by
    calc a ^ 2 * c ^ 2 ≤ 1 * 1 := mul_le_mul ha1 hc1 (sq_nonneg c) zero_le_one
      _ = 1 := by ring
  have hD : 1 - k ^ 2 * a ^ 2 * c ^ 2 ≠ 0 := by
    have : k ^ 2 * (a ^ 2 * c ^ 2) ≤ k ^ 2 := by
      calc k ^ 2 * (a ^ 2 * c ^ 2) ≤ k ^ 2 * 1 := mul_le_mul_of_nonneg_left hac (sq_nonneg k)
        _ = k ^ 2 := by ring
    intro h; nlinarith
  unfold ei19b_addSin ei19b_addCos
  rw [div_pow, div_pow, ← add_div, div_eq_one_iff_eq (pow_ne_zero 2 hD)]
  linear_combination (Q ^ 2 * a ^ 2 * c ^ 2 + b ^ 2 * c ^ 2) * hP +
    (-a ^ 4 * c ^ 2 * k ^ 2 + a ^ 2 * c ^ 2 + a ^ 2 * d ^ 2) * hQ +
    (-a ^ 2 * c ^ 2 * k ^ 2 + c ^ 2 + d ^ 2) * hab + (-a ^ 2 * c ^ 2 * k ^ 2 + 1) * hcd

/-- DLMF 19.11.4, second formula: `tan(ψ/2) = ((sin θ) Δ(φ) + (sin φ) Δ(θ))/(cos θ + cos φ)`,
for an amplitude `ψ` with `sin ψ`, `cos ψ` given by (19.11.3), (19.11.4); real `k² < 1`,
`cos θ + cos φ ≠ 0`. -/
@[dlmf 19.11.E4]
theorem addition_tan_half {k θ φ ψ : ℝ} (hk : k ^ 2 < 1) (hs : Real.sin ψ = ei19b_addSin k θ φ)
    (hc : Real.cos ψ = ei19b_addCos k θ φ) (hθφ : Real.cos θ + Real.cos φ ≠ 0) :
    Real.tan (ψ / 2) =
      (Real.sin θ * ei19b_delta k φ + Real.sin φ * ei19b_delta k θ) /
        (Real.cos θ + Real.cos φ) := by
  have htan : Real.tan (ψ / 2) = Real.sin ψ / (1 + Real.cos ψ) := by
    obtain ⟨u, rfl⟩ : ∃ u, ψ = 2 * u := ⟨ψ / 2, by ring⟩
    rw [show 2 * u / 2 = u by ring, Real.sin_two_mul, Real.cos_two_mul, Real.tan_eq_sin_div_cos]
    by_cases hc0 : Real.cos u = 0
    · simp [hc0]
    · field_simp
      ring
  rw [htan, hs, hc]
  unfold ei19b_addSin ei19b_addCos
  set a := Real.sin θ
  set b := Real.cos θ
  set c := Real.sin φ
  set d := Real.cos φ
  set P := ei19b_delta k θ
  set Q := ei19b_delta k φ
  have hP : P ^ 2 = 1 - k ^ 2 * a ^ 2 := Real.sq_sqrt (by nlinarith [Real.sin_sq_le_one θ])
  have hQ : Q ^ 2 = 1 - k ^ 2 * c ^ 2 := Real.sq_sqrt (by nlinarith [Real.sin_sq_le_one φ])
  have hab : a ^ 2 + b ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  have hcd : c ^ 2 + d ^ 2 = 1 := Real.sin_sq_add_cos_sq φ
  have ha1 : a ^ 2 ≤ 1 := Real.sin_sq_le_one θ
  have hc1 : c ^ 2 ≤ 1 := Real.sin_sq_le_one φ
  have hac : a ^ 2 * c ^ 2 ≤ 1 := by
    calc a ^ 2 * c ^ 2 ≤ 1 * 1 := mul_le_mul ha1 hc1 (sq_nonneg c) zero_le_one
      _ = 1 := by ring
  have hD : 1 - k ^ 2 * a ^ 2 * c ^ 2 ≠ 0 := by
    have : k ^ 2 * (a ^ 2 * c ^ 2) ≤ k ^ 2 := by
      calc k ^ 2 * (a ^ 2 * c ^ 2) ≤ k ^ 2 * 1 := mul_le_mul_of_nonneg_left hac (sq_nonneg k)
        _ = k ^ 2 := by ring
    intro h; nlinarith
  rw [show 1 + (b * d - a * c * P * Q) / (1 - k ^ 2 * a ^ 2 * c ^ 2) =
      (1 - k ^ 2 * a ^ 2 * c ^ 2 + (b * d - a * c * P * Q)) / (1 - k ^ 2 * a ^ 2 * c ^ 2) by
    rw [add_div, div_self hD], div_div_div_cancel_right₀ hD]
  by_cases h0 : 1 - k ^ 2 * a ^ 2 * c ^ 2 + (b * d - a * c * P * Q) = 0
  · have key : ((a * Q + c * P) * (b + d)) ^ 2 + (a ^ 2 - c ^ 2) ^ 2 = 0 := by
      linear_combination
        (4 * Q ^ 2 * a ^ 2 * c ^ 2 + b ^ 2 * c ^ 2 + 2 * b * c ^ 2 * d + c ^ 2 * d ^ 2) * hP +
        (-4 * a ^ 4 * c ^ 2 * k ^ 2 + a ^ 2 * b ^ 2 + 2 * a ^ 2 * b * d + 4 * a ^ 2 * c ^ 2 +
          a ^ 2 * d ^ 2) * hQ +
        (2 * P * Q * a * c - 2 * a ^ 2 * c ^ 2 * k ^ 2 + a ^ 2 + c ^ 2) * hab +
        (2 * P * Q * a * c - 2 * a ^ 2 * c ^ 2 * k ^ 2 + a ^ 2 + c ^ 2) * hcd +
        (4 * P * Q * a * c - 4 * a ^ 2 * c ^ 2 * k ^ 2 + 2 * a ^ 2 + 2 * c ^ 2) * h0
    have hsq : ((a * Q + c * P) * (b + d)) ^ 2 = 0 := by
      nlinarith [sq_nonneg ((a * Q + c * P) * (b + d)), sq_nonneg (a ^ 2 - c ^ 2)]
    have hN : a * Q + c * P = 0 := by
      rcases mul_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp hsq) with h | h
      · exact h
      · exact absurd h hθφ
    rw [h0, hN, div_zero, zero_div]
  · rw [div_eq_div_iff h0 hθφ]
    linear_combination (Q * a * c ^ 2) * hP + (P * a ^ 2 * c) * hQ + (P * c) * hab + (Q * a) * hcd

/-- DLMF 19.11.1: `F(θ, k) + F(φ, k) = F(ψ, k)` for real `k² < 1`, `θ, φ ∈ [0, π/2]`, with
`ψ ∈ [0, π]` given by (19.11.3) and (19.11.4). -/
@[dlmf 19.11.E1, dlmf 19.11.E3]
theorem incEllIntFk_add {k θ φ ψ : ℝ} (hk : k ^ 2 < 1) (hθ : θ ∈ Icc 0 (π / 2))
    (hφ : φ ∈ Icc 0 (π / 2)) (hψ : ψ ∈ Icc 0 π) (hs : Real.sin ψ = ei19b_addSin k θ φ)
    (hc : Real.cos ψ = ei19b_addCos k θ φ) :
    incEllIntFk θ k + incEllIntFk φ k = incEllIntFk ψ k := by
  sorry

/-- DLMF 19.11.2: `E(θ, k) + E(φ, k) = E(ψ, k) + k² sin θ sin φ sin ψ`, hypotheses as in
(19.11.1). -/
@[dlmf 19.11.E2, dlmf 19.11.E3]
theorem incEllIntEk_add {k θ φ ψ : ℝ} (hk : k ^ 2 < 1) (hθ : θ ∈ Icc 0 (π / 2))
    (hφ : φ ∈ Icc 0 (π / 2)) (hψ : ψ ∈ Icc 0 π) (hs : Real.sin ψ = ei19b_addSin k θ φ)
    (hc : Real.cos ψ = ei19b_addCos k θ φ) :
    incEllIntEk θ k + incEllIntEk φ k =
      incEllIntEk ψ k + k ^ 2 * Real.sin θ * Real.sin φ * Real.sin ψ := by
  sorry

/-- DLMF 19.11.5–19.11.6: `Π(θ, α², k) + Π(φ, α², k) = Π(ψ, α², k) - α² R_C(γ - δ, γ)` with
`γ = (csc²θ - α²)(csc²φ - α²)(csc²ψ - α²)`, `δ = α²(1 - α²)(α² - k²)`; real `k² < 1`,
`θ, φ ∈ (0, π/2)`, `ψ` as in (19.11.1), on the branch region `α² < 1`,
`α²(1 - cos θ cos φ cos ψ) < 1` (see the module docstring). -/
@[dlmf 19.11.E5, dlmf 19.11.E6]
theorem incEllIntPik_add {k θ φ ψ α2 : ℝ} (hk : k ^ 2 < 1) (hθ : θ ∈ Ioo 0 (π / 2))
    (hφ : φ ∈ Ioo 0 (π / 2)) (hψ : ψ ∈ Icc 0 π) (hs : Real.sin ψ = ei19b_addSin k θ φ)
    (hc : Real.cos ψ = ei19b_addCos k θ φ) (hα : α2 < 1)
    (hαψ : α2 * (1 - Real.cos θ * Real.cos φ * Real.cos ψ) < 1) :
    let γ := (1 / Real.sin θ ^ 2 - α2) * (1 / Real.sin φ ^ 2 - α2) * (1 / Real.sin ψ ^ 2 - α2)
    let δ := α2 * (1 - α2) * (α2 - k ^ 2)
    incEllIntPik θ α2 k + incEllIntPik φ α2 k =
      incEllIntPik ψ α2 k - α2 * symEllIntRC ((γ - δ : ℝ) : ℂ) ((γ : ℝ) : ℂ) := by
  sorry

/-- DLMF 19.11.6_5: for `θ, φ ∈ (0, π/2)`, `ψ` as in (19.11.1), and
`k² < α² < min(1, (1 - cos θ cos φ cos ψ)⁻¹)`,
`R_C(γ - δ, γ) = -δ^{-1/2} arctan(√δ sin θ sin φ sin ψ / (α² - 1 - α² cos θ cos φ cos ψ))`.
(DLMF allows `k² = α²`, where `δ = 0` and the right side is a limit; here `k² < α²`.) -/
@[dlmf 19.11.E6_5]
theorem symEllIntRC_addition_eq_arctan {k θ φ ψ α2 : ℝ} (hk : k ^ 2 < 1)
    (hθ : θ ∈ Ioo 0 (π / 2)) (hφ : φ ∈ Ioo 0 (π / 2)) (hψ : ψ ∈ Icc 0 π)
    (hs : Real.sin ψ = ei19b_addSin k θ φ) (hc : Real.cos ψ = ei19b_addCos k θ φ)
    (hkα : k ^ 2 < α2) (hα : α2 < 1)
    (hαψ : α2 * (1 - Real.cos θ * Real.cos φ * Real.cos ψ) < 1) :
    let γ := (1 / Real.sin θ ^ 2 - α2) * (1 / Real.sin φ ^ 2 - α2) * (1 / Real.sin ψ ^ 2 - α2)
    let δ := α2 * (1 - α2) * (α2 - k ^ 2)
    symEllIntRC ((γ - δ : ℝ) : ℂ) ((γ : ℝ) : ℂ) =
      ((-1 / Real.sqrt δ * Real.arctan (Real.sqrt δ * Real.sin θ * Real.sin φ * Real.sin ψ /
        (α2 - 1 - α2 * Real.cos θ * Real.cos φ * Real.cos ψ)) : ℝ) : ℂ) := by
  sorry

/-! ### §19.11(ii) Case `ψ = π/2` -/

/-- The substitution `θ ↦ π/2 - arctan(k' tan θ)` of (19.11.9) maps `dθ/Δ(θ)` to `-dθ/Δ(θ)`:
`(1 - m sin²(π/2 - arctan(c tan θ)))^{-1/2} · d/dθ(π/2 - arctan(c tan θ)) = -(1 - m sin²θ)^{-1/2}`,
`c = √(1 - m)`, for `cos θ > 0`. -/
theorem ei19b_complement_integrand {m θ : ℝ} (hm : m < 1) (hcos : 0 < Real.cos θ) :
    (1 - m * Real.sin (π / 2 - Real.arctan (Real.sqrt (1 - m) * Real.tan θ)) ^ 2) ^ (-(1 / 2) : ℝ) *
        (-(Real.sqrt (1 - m) * (1 / Real.cos θ ^ 2)) /
          (1 + (Real.sqrt (1 - m) * Real.tan θ) ^ 2)) =
      -(1 - m * Real.sin θ ^ 2) ^ (-(1 / 2) : ℝ) := by
  set c := Real.sqrt (1 - m) with hcdef
  have hc : 0 < c := Real.sqrt_pos.mpr (by linarith)
  have hc2 : c ^ 2 = 1 - m := Real.sq_sqrt (by linarith)
  set D := 1 - m * Real.sin θ ^ 2 with hD
  have hD0 : 0 < D := DLMF.Elliptic.one_sub_mul_sin_sq_pos hm θ
  have hsc := Real.sin_sq_add_cos_sq θ
  have hco : Real.cos θ ≠ 0 := hcos.ne'
  have hx2 : 1 + (c * Real.tan θ) ^ 2 = D / Real.cos θ ^ 2 := by
    have h1 : (c * Real.tan θ) ^ 2 = c ^ 2 * Real.sin θ ^ 2 / Real.cos θ ^ 2 := by
      rw [Real.tan_eq_sin_div_cos]; ring
    rw [h1, hc2, eq_div_iff (pow_ne_zero 2 hco), add_mul, div_mul_cancel₀ _ (pow_ne_zero 2 hco), hD]
    linear_combination hsc
  have hsin : Real.sin (π / 2 - Real.arctan (c * Real.tan θ)) ^ 2 = Real.cos θ ^ 2 / D := by
    rw [Real.sin_pi_div_two_sub, Real.cos_arctan, div_pow, Real.sq_sqrt (by positivity), hx2]
    field_simp
  have hbase : 1 - m * (Real.cos θ ^ 2 / D) = c ^ 2 / D := by
    rw [hc2, eq_div_iff hD0.ne', sub_mul, mul_assoc, div_mul_cancel₀ _ hD0.ne', hD]
    linear_combination (-m) * hsc
  rw [hsin, hbase, ei19b_rpow_neg_half (by positivity), ei19b_rpow_neg_half hD0.le, hx2,
    Real.sqrt_div' _ hD0.le, Real.sqrt_sq hc.le]
  have hsD : 0 < Real.sqrt D := Real.sqrt_pos.mpr hD0
  have hsD2 : Real.sqrt D ^ 2 = D := Real.sq_sqrt hD0.le
  set r := Real.sqrt D with hr
  rw [← hsD2]
  field_simp

/-- Real form of (19.11.7): `F(φ | m) = K(m) - F(π/2 - arctan(√(1-m) tan φ) | m)` for `m < 1`
and `0 ≤ φ < π/2`. -/
theorem ei19b_incEllIntFm_complement {m φ : ℝ} (hm : m < 1) (hφ0 : 0 ≤ φ) (hφ : φ < π / 2) :
    DLMF.Elliptic.Real.incEllIntFm φ m = DLMF.Elliptic.Real.compEllIntKm m -
      DLMF.Elliptic.Real.incEllIntFm (π / 2 - Real.arctan (Real.sqrt (1 - m) * Real.tan φ)) m := by
  set c := Real.sqrt (1 - m) with hcdef
  set G : ℝ → ℝ := fun θ => (1 - m * Real.sin θ ^ 2) ^ (-(1 / 2) : ℝ) with hG
  have hGc : Continuous G := DLMF.Elliptic.continuous_one_sub_mul_sin_sq_rpow hm _
  set f : ℝ → ℝ := fun θ => π / 2 - Real.arctan (c * Real.tan θ) with hf
  set f' : ℝ → ℝ := fun θ => -(c * (1 / Real.cos θ ^ 2)) / (1 + (c * Real.tan θ) ^ 2) with hf'
  have hcos : ∀ θ ∈ uIcc 0 φ, 0 < Real.cos θ := by
    intro θ hθ
    rw [uIcc_of_le hφ0] at hθ
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩
  have hderiv : ∀ θ ∈ uIcc 0 φ, HasDerivAt f (f' θ) θ := by
    intro θ hθ
    have h := (((Real.hasDerivAt_tan (hcos θ hθ).ne').const_mul c).arctan).const_sub (π / 2)
    convert h using 1
    simp only [hf']
    ring
  have hcont' : ContinuousOn f' (uIcc 0 φ) := by
    intro θ hθ
    have hc0 := (hcos θ hθ).ne'
    have htan : ContinuousAt Real.tan θ := Real.continuousAt_tan.mpr hc0
    refine ContinuousAt.continuousWithinAt ?_
    simp only [hf']
    refine ContinuousAt.div ?_ ?_ (by positivity)
    · exact (continuousAt_const.mul (continuousAt_const.div
        (Real.continuous_cos.continuousAt.pow 2) (pow_ne_zero 2 hc0))).neg
    · exact continuousAt_const.add ((continuousAt_const.mul htan).pow 2)
  have hsub := intervalIntegral.integral_comp_mul_deriv hderiv hcont' hGc
  have hpt : ∀ θ ∈ uIcc 0 φ, (G ∘ f) θ * f' θ = -G θ := fun θ hθ =>
    ei19b_complement_integrand hm (hcos θ hθ)
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_neg] at hsub
  have hf0 : f 0 = π / 2 := by simp [hf]
  rw [hf0, ← intervalIntegral.integral_interval_sub_left (hGc.intervalIntegrable 0 (f φ))
    (hGc.intervalIntegrable 0 (π / 2))] at hsub
  unfold DLMF.Elliptic.Real.incEllIntFm DLMF.Elliptic.Real.compEllIntKm
  simp only [hG, hf] at hsub ⊢
  linarith

/-- The substitution of (19.11.9) in the second-kind integrand:
`(1 - m sin²(π/2 - arctan(c tan θ)))^{1/2} · d/dθ(π/2 - arctan(c tan θ)) = -(1 - m) D^{-1/2}/D`,
`D = 1 - m sin²θ`, `c = √(1 - m)`, for `cos θ > 0`. -/
theorem ei19b_complement_integrand_E {m θ : ℝ} (hm : m < 1) (hcos : 0 < Real.cos θ) :
    (1 - m * Real.sin (π / 2 - Real.arctan (Real.sqrt (1 - m) * Real.tan θ)) ^ 2) ^ (1 / 2 : ℝ) *
        (-(Real.sqrt (1 - m) * (1 / Real.cos θ ^ 2)) /
          (1 + (Real.sqrt (1 - m) * Real.tan θ) ^ 2)) =
      -((1 - m) * (Real.sqrt (1 - m * Real.sin θ ^ 2))⁻¹ / (1 - m * Real.sin θ ^ 2)) := by
  set c := Real.sqrt (1 - m) with hcdef
  have hc : 0 < c := Real.sqrt_pos.mpr (by linarith)
  have hc2 : c ^ 2 = 1 - m := Real.sq_sqrt (by linarith)
  set D := 1 - m * Real.sin θ ^ 2 with hD
  have hD0 : 0 < D := DLMF.Elliptic.one_sub_mul_sin_sq_pos hm θ
  have hsc := Real.sin_sq_add_cos_sq θ
  have hco : Real.cos θ ≠ 0 := hcos.ne'
  have hx2 : 1 + (c * Real.tan θ) ^ 2 = D / Real.cos θ ^ 2 := by
    have h1 : (c * Real.tan θ) ^ 2 = c ^ 2 * Real.sin θ ^ 2 / Real.cos θ ^ 2 := by
      rw [Real.tan_eq_sin_div_cos]; ring
    rw [h1, hc2, eq_div_iff (pow_ne_zero 2 hco), add_mul, div_mul_cancel₀ _ (pow_ne_zero 2 hco), hD]
    linear_combination hsc
  have hsin : Real.sin (π / 2 - Real.arctan (c * Real.tan θ)) ^ 2 = Real.cos θ ^ 2 / D := by
    rw [Real.sin_pi_div_two_sub, Real.cos_arctan, div_pow, Real.sq_sqrt (by positivity), hx2]
    field_simp
  have hbase : 1 - m * (Real.cos θ ^ 2 / D) = c ^ 2 / D := by
    rw [hc2, eq_div_iff hD0.ne', sub_mul, mul_assoc, div_mul_cancel₀ _ hD0.ne', hD]
    linear_combination (-m) * hsc
  rw [hsin, hbase, ei19b_rpow_half, hx2, Real.sqrt_div' _ hD0.le, Real.sqrt_sq hc.le, ← hc2]
  have hsD : 0 < Real.sqrt D := Real.sqrt_pos.mpr hD0
  have hsD2 : Real.sqrt D ^ 2 = D := Real.sq_sqrt hD0.le
  set r := Real.sqrt D with hr
  rw [← hsD2]
  field_simp

/-- `d/dθ [m sin θ cos θ / Δ(θ)] = Δ(θ) - (1 - m)/Δ(θ)³`, `Δ = √(1 - m sin²θ)`, `m < 1`. -/
theorem ei19b_hasDerivAt_E_correction {m : ℝ} (hm : m < 1) (θ : ℝ) :
    HasDerivAt (fun θ => m * Real.sin θ * Real.cos θ * (Real.sqrt (1 - m * Real.sin θ ^ 2))⁻¹)
      (Real.sqrt (1 - m * Real.sin θ ^ 2) -
        (1 - m) * (Real.sqrt (1 - m * Real.sin θ ^ 2))⁻¹ / (1 - m * Real.sin θ ^ 2)) θ := by
  have hD0 : 0 < 1 - m * Real.sin θ ^ 2 := DLMF.Elliptic.one_sub_mul_sin_sq_pos hm θ
  have h1 : HasDerivAt (fun θ => 1 - m * Real.sin θ ^ 2)
      (-(m * (2 * Real.sin θ * Real.cos θ))) θ := by
    have := (((Real.hasDerivAt_sin θ).pow 2).const_mul m).const_sub 1
    convert this using 1
    simp
  have h2 := h1.sqrt hD0.ne'
  have hs : 0 < Real.sqrt (1 - m * Real.sin θ ^ 2) := Real.sqrt_pos.mpr hD0
  have h3 := h2.inv hs.ne'
  have h4 : HasDerivAt (fun θ => m * Real.sin θ * Real.cos θ)
      (m * (Real.cos θ ^ 2 - Real.sin θ ^ 2)) θ := by
    have := ((Real.hasDerivAt_sin θ).const_mul m).mul (Real.hasDerivAt_cos θ)
    convert this using 1
    ring
  have h := h4.mul h3
  convert h using 1
  have hsc := Real.sin_sq_add_cos_sq θ
  have hs2 : Real.sqrt (1 - m * Real.sin θ ^ 2) ^ 2 = 1 - m * Real.sin θ ^ 2 := Real.sq_sqrt hD0.le
  set r := Real.sqrt (1 - m * Real.sin θ ^ 2) with hr
  have hc2 : Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 := by linarith
  simp only [Pi.inv_apply]
  rw [← hr, ← hs2]
  field_simp
  rw [hc2]
  ring_nf
  rw [show r ^ 4 = (r ^ 2) ^ 2 by ring, hs2]
  ring

/-- `∫₀^φ (1 - m)/Δ³ = E(φ | m) - m sin φ cos φ/Δ(φ)`, `m < 1`. -/
theorem ei19b_integral_E_correction {m : ℝ} (hm : m < 1) (φ : ℝ) :
    ∫ θ in (0 : ℝ)..φ, (1 - m) * (Real.sqrt (1 - m * Real.sin θ ^ 2))⁻¹ / (1 - m * Real.sin θ ^ 2) =
      DLMF.Elliptic.Real.incEllIntEm φ m -
        m * Real.sin φ * Real.cos φ * (Real.sqrt (1 - m * Real.sin φ ^ 2))⁻¹ := by
  have hpos := DLMF.Elliptic.one_sub_mul_sin_sq_pos hm
  have hc1 : Continuous fun θ : ℝ => Real.sqrt (1 - m * Real.sin θ ^ 2) := by fun_prop
  have hc2 : Continuous fun θ : ℝ =>
      (1 - m) * (Real.sqrt (1 - m * Real.sin θ ^ 2))⁻¹ / (1 - m * Real.sin θ ^ 2) := by
    refine Continuous.div (continuous_const.mul (hc1.inv₀ fun θ =>
      (Real.sqrt_pos.mpr (hpos θ)).ne')) (by fun_prop) fun θ => (hpos θ).ne'
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun θ _ => ei19b_hasDerivAt_E_correction hm θ) ((hc1.sub hc2).intervalIntegrable 0 φ)
  rw [intervalIntegral.integral_sub (hc1.intervalIntegrable 0 φ) (hc2.intervalIntegrable 0 φ)]
    at hftc
  have hE : ∫ θ in (0 : ℝ)..φ, Real.sqrt (1 - m * Real.sin θ ^ 2) =
      DLMF.Elliptic.Real.incEllIntEm φ m := by
    unfold DLMF.Elliptic.Real.incEllIntEm
    exact intervalIntegral.integral_congr fun θ _ => (ei19b_rpow_half _).symm
  simp only [Real.sin_zero, mul_zero, zero_mul, sub_zero] at hftc
  linarith

/-- Real form of (19.11.8): `E(φ | m) = E(m) - E(θ | m) + m sin θ sin φ` with
`θ = π/2 - arctan(√(1-m) tan φ)`, for `m < 1` and `0 ≤ φ < π/2`. -/
theorem ei19b_incEllIntEm_complement {m φ : ℝ} (hm : m < 1) (hφ0 : 0 ≤ φ) (hφ : φ < π / 2) :
    DLMF.Elliptic.Real.incEllIntEm φ m = DLMF.Elliptic.Real.compEllIntEm m -
      DLMF.Elliptic.Real.incEllIntEm (π / 2 - Real.arctan (Real.sqrt (1 - m) * Real.tan φ)) m +
      m * Real.sin (π / 2 - Real.arctan (Real.sqrt (1 - m) * Real.tan φ)) * Real.sin φ := by
  set c := Real.sqrt (1 - m) with hcdef
  set G : ℝ → ℝ := fun θ => (1 - m * Real.sin θ ^ 2) ^ (1 / 2 : ℝ) with hG
  have hGc : Continuous G := DLMF.Elliptic.continuous_one_sub_mul_sin_sq_rpow hm _
  set f : ℝ → ℝ := fun θ => π / 2 - Real.arctan (c * Real.tan θ) with hf
  set f' : ℝ → ℝ := fun θ => -(c * (1 / Real.cos θ ^ 2)) / (1 + (c * Real.tan θ) ^ 2) with hf'
  have hcos : ∀ θ ∈ uIcc 0 φ, 0 < Real.cos θ := by
    intro θ hθ
    rw [uIcc_of_le hφ0] at hθ
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩
  have hderiv : ∀ θ ∈ uIcc 0 φ, HasDerivAt f (f' θ) θ := by
    intro θ hθ
    have h := (((Real.hasDerivAt_tan (hcos θ hθ).ne').const_mul c).arctan).const_sub (π / 2)
    convert h using 1
    simp only [hf']
    ring
  have hcont' : ContinuousOn f' (uIcc 0 φ) := by
    intro θ hθ
    have hc0 := (hcos θ hθ).ne'
    have htan : ContinuousAt Real.tan θ := Real.continuousAt_tan.mpr hc0
    refine ContinuousAt.continuousWithinAt ?_
    simp only [hf']
    refine ContinuousAt.div ?_ ?_ (by positivity)
    · exact (continuousAt_const.mul (continuousAt_const.div
        (Real.continuous_cos.continuousAt.pow 2) (pow_ne_zero 2 hc0))).neg
    · exact continuousAt_const.add ((continuousAt_const.mul htan).pow 2)
  have hsub := intervalIntegral.integral_comp_mul_deriv hderiv hcont' hGc
  have hpt : ∀ θ ∈ uIcc 0 φ, (G ∘ f) θ * f' θ =
      -((1 - m) * (Real.sqrt (1 - m * Real.sin θ ^ 2))⁻¹ / (1 - m * Real.sin θ ^ 2)) :=
    fun θ hθ => ei19b_complement_integrand_E hm (hcos θ hθ)
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_neg,
    ei19b_integral_E_correction hm φ] at hsub
  have hf0 : f 0 = π / 2 := by simp [hf]
  rw [hf0, ← intervalIntegral.integral_interval_sub_left (hGc.intervalIntegrable 0 (f φ))
    (hGc.intervalIntegrable 0 (π / 2))] at hsub
  -- `sin θ₀ = cos φ / Δ(φ)`
  have hcφ : 0 < Real.cos φ := hcos φ (by rw [uIcc_of_le hφ0]; exact ⟨hφ0, le_rfl⟩)
  have hsinθ : Real.sin (f φ) = Real.cos φ * (Real.sqrt (1 - m * Real.sin φ ^ 2))⁻¹ := by
    have hc2 : c ^ 2 = 1 - m := Real.sq_sqrt (by linarith)
    have hsc := Real.sin_sq_add_cos_sq φ
    have hD0 := DLMF.Elliptic.one_sub_mul_sin_sq_pos hm φ
    have hx2 : 1 + (c * Real.tan φ) ^ 2 = (1 - m * Real.sin φ ^ 2) / Real.cos φ ^ 2 := by
      have h1 : (c * Real.tan φ) ^ 2 = c ^ 2 * Real.sin φ ^ 2 / Real.cos φ ^ 2 := by
        rw [Real.tan_eq_sin_div_cos]; ring
      rw [h1, hc2, eq_div_iff (pow_ne_zero 2 hcφ.ne'), add_mul,
        div_mul_cancel₀ _ (pow_ne_zero 2 hcφ.ne')]
      linear_combination hsc
    simp only [hf]
    rw [Real.sin_pi_div_two_sub, Real.cos_arctan, hx2, Real.sqrt_div' _ (by positivity),
      Real.sqrt_sq hcφ.le]
    field_simp
  unfold DLMF.Elliptic.Real.incEllIntEm DLMF.Elliptic.Real.compEllIntEm
  unfold DLMF.Elliptic.Real.incEllIntEm at hsub
  rw [hsinθ]
  simp only [hG, hf] at hsub ⊢
  linarith

/-- DLMF 19.11.7, 19.11.9: `F(φ, k) = K(k) - F(θ, k)` when `tan θ = 1/(k' tan φ)`, for real
`k² < 1` and `θ, φ ∈ (0, π/2)`. -/
@[dlmf 19.11.E7, dlmf 19.11.E9]
theorem incEllIntFk_eq_compEllIntKk_sub {k θ φ : ℝ} (hk : k ^ 2 < 1) (hθ : θ ∈ Ioo 0 (π / 2))
    (hφ : φ ∈ Ioo 0 (π / 2)) (hθφ : Real.tan θ = 1 / (Real.sqrt (1 - k ^ 2) * Real.tan φ)) :
    incEllIntFk φ k = compEllIntKk k - incEllIntFk θ k := by
  have hk' : 0 < Real.sqrt (1 - k ^ 2) := Real.sqrt_pos.mpr (by linarith)
  have htanφ : 0 < Real.tan φ := Real.tan_pos_of_pos_of_lt_pi_div_two hφ.1 hφ.2
  have hθeq : θ = π / 2 - Real.arctan (Real.sqrt (1 - k ^ 2) * Real.tan φ) := by
    rw [← Real.arctan_tan (by linarith [hθ.1, Real.pi_pos]) hθ.2, hθφ, one_div,
      Real.arctan_inv_of_pos (by positivity)]
  have hk2 : ((k : ℂ)) ^ 2 = ((k ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [incEllIntFk_eq_ofReal hk2 hk.le, incEllIntFk_eq_ofReal hk2 hk.le,
    compEllIntKk_eq_ofReal hk2 hk.le, hθeq,
    ei19b_incEllIntFm_complement hk hφ.1.le hφ.2]
  push_cast
  ring

/-- DLMF 19.11.8, 19.11.9: `E(φ, k) = E(k) - E(θ, k) + k² sin θ sin φ` when
`tan θ = 1/(k' tan φ)`, hypotheses as in (19.11.7). -/
@[dlmf 19.11.E8, dlmf 19.11.E9]
theorem incEllIntEk_eq_compEllIntEk_sub {k θ φ : ℝ} (hk : k ^ 2 < 1) (hθ : θ ∈ Ioo 0 (π / 2))
    (hφ : φ ∈ Ioo 0 (π / 2)) (hθφ : Real.tan θ = 1 / (Real.sqrt (1 - k ^ 2) * Real.tan φ)) :
    incEllIntEk φ k = compEllIntEk k - incEllIntEk θ k + k ^ 2 * Real.sin θ * Real.sin φ := by
  have hk' : 0 < Real.sqrt (1 - k ^ 2) := Real.sqrt_pos.mpr (by linarith)
  have htanφ : 0 < Real.tan φ := Real.tan_pos_of_pos_of_lt_pi_div_two hφ.1 hφ.2
  have hθeq : θ = π / 2 - Real.arctan (Real.sqrt (1 - k ^ 2) * Real.tan φ) := by
    rw [← Real.arctan_tan (by linarith [hθ.1, Real.pi_pos]) hθ.2, hθφ, one_div,
      Real.arctan_inv_of_pos (by positivity)]
  have hk2 : ((k : ℂ)) ^ 2 = ((k ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [incEllIntEk_eq_ofReal hk2 hk.le, incEllIntEk_eq_ofReal hk2 hk.le,
    compEllIntEk_eq_ofReal hk2 hk.le, hθeq,
    ei19b_incEllIntEm_complement hk hφ.1.le hφ.2]
  push_cast
  ring

/-- DLMF 19.11.10–19.11.11 (with 19.11.9):
`Π(φ, α², k) = Π(α², k) - Π(θ, α², k) - α² R_C(γ - δ, γ)`,
`γ = (1 - α²)(csc²θ - α²)(csc²φ - α²)`, `δ = α²(1 - α²)(α² - k²)`, for real `k² < 1`,
`α² < 1` and `θ, φ ∈ (0, π/2)` with `tan θ = 1/(k' tan φ)`. -/
@[dlmf 19.11.E10, dlmf 19.11.E11]
theorem incEllIntPik_eq_compEllIntPik_sub {k θ φ α2 : ℝ} (hk : k ^ 2 < 1)
    (hθ : θ ∈ Ioo 0 (π / 2)) (hφ : φ ∈ Ioo 0 (π / 2))
    (hθφ : Real.tan θ = 1 / (Real.sqrt (1 - k ^ 2) * Real.tan φ)) (hα : α2 < 1) :
    let γ := (1 - α2) * (1 / Real.sin θ ^ 2 - α2) * (1 / Real.sin φ ^ 2 - α2)
    let δ := α2 * (1 - α2) * (α2 - k ^ 2)
    incEllIntPik φ α2 k =
      compEllIntPik α2 k - incEllIntPik θ α2 k -
        α2 * symEllIntRC ((γ - δ : ℝ) : ℂ) ((γ : ℝ) : ℂ) := by
  sorry

/-! ### §19.11(iii) Duplication formulas -/

/-- The right side of (19.11.14): `sin ψ` for the duplication of `θ`. -/
def ei19b_dupSin (k θ : ℝ) : ℝ :=
  Real.sin (2 * θ) * ei19b_delta k θ / (1 - k ^ 2 * Real.sin θ ^ 4)

/-- The right side of the first formula (19.11.15): `cos ψ` for the duplication of `θ`. -/
def ei19b_dupCos (k θ : ℝ) : ℝ :=
  (Real.cos (2 * θ) + k ^ 2 * Real.sin θ ^ 4) / (1 - k ^ 2 * Real.sin θ ^ 4)

/-- (19.11.14), (19.11.15) are (19.11.3), (19.11.4) with `φ = θ`. -/
theorem ei19b_dupSin_eq (k θ : ℝ) : ei19b_dupSin k θ = ei19b_addSin k θ θ := by
  unfold ei19b_dupSin ei19b_addSin
  rw [Real.sin_two_mul]
  ring

/-- (19.11.15), first formula, is the first formula of (19.11.4) with `φ = θ`. -/
theorem ei19b_dupCos_eq {k : ℝ} (hk : k ^ 2 < 1) (θ : ℝ) :
    ei19b_dupCos k θ = ei19b_addCos k θ θ := by
  unfold ei19b_dupCos ei19b_addCos
  have hP : ei19b_delta k θ ^ 2 = 1 - k ^ 2 * Real.sin θ ^ 2 :=
    Real.sq_sqrt (by nlinarith [Real.sin_sq_le_one θ])
  rw [Real.cos_two_mul, show Real.sin θ * Real.sin θ * ei19b_delta k θ * ei19b_delta k θ =
    Real.sin θ ^ 2 * ei19b_delta k θ ^ 2 by ring, hP]
  have := Real.sin_sq_add_cos_sq θ
  congr 1
  · nlinarith
  · ring

/-- DLMF 19.11.12: `F(ψ, k) = 2F(θ, k)` for real `k² < 1`, `θ ∈ [0, π/2]`, with `ψ ∈ [0, π]`
given by (19.11.14) and the first formula of (19.11.15). -/
@[dlmf 19.11.E12, dlmf 19.11.E14]
theorem incEllIntFk_duplication {k θ ψ : ℝ} (hk : k ^ 2 < 1) (hθ : θ ∈ Icc 0 (π / 2))
    (hψ : ψ ∈ Icc 0 π) (hs : Real.sin ψ = ei19b_dupSin k θ) (hc : Real.cos ψ = ei19b_dupCos k θ) :
    incEllIntFk ψ k = 2 * incEllIntFk θ k := by
  rw [ei19b_dupSin_eq] at hs
  rw [ei19b_dupCos_eq hk] at hc
  rw [← incEllIntFk_add hk hθ hθ hψ hs hc]
  ring

/-- DLMF 19.11.13: `E(ψ, k) = 2E(θ, k) - k² sin²θ sin ψ`, hypotheses as in (19.11.12). -/
@[dlmf 19.11.E13, dlmf 19.11.E14]
theorem incEllIntEk_duplication {k θ ψ : ℝ} (hk : k ^ 2 < 1) (hθ : θ ∈ Icc 0 (π / 2))
    (hψ : ψ ∈ Icc 0 π) (hs : Real.sin ψ = ei19b_dupSin k θ) (hc : Real.cos ψ = ei19b_dupCos k θ) :
    incEllIntEk ψ k = 2 * incEllIntEk θ k - k ^ 2 * Real.sin θ ^ 2 * Real.sin ψ := by
  rw [ei19b_dupSin_eq] at hs
  rw [ei19b_dupCos_eq hk] at hc
  have h := incEllIntEk_add hk hθ hθ hψ hs hc
  linear_combination -h

/-- DLMF 19.11.15 (remaining formulas): for `ψ ∈ [0, π]` with `sin ψ`, `cos ψ` given by
(19.11.14) and the first formula of (19.11.15), real `k² < 1` and `θ ∈ [0, π/2)`:
`tan(ψ/2) = (tan θ) Δ(θ)`, `sin θ = (sin ψ)/√((1 + cos ψ)(1 + Δ(ψ)))`,
`cos θ = √((cos ψ + Δ(ψ))/(1 + Δ(ψ)))`, `tan θ = tan(ψ/2) √((1 + cos ψ)/(cos ψ + Δ(ψ)))`. -/
@[dlmf 19.11.E15]
theorem duplication_half_angle {k θ ψ : ℝ} (hk : k ^ 2 < 1) (hθ : θ ∈ Ico 0 (π / 2))
    (hψ : ψ ∈ Icc 0 π) (hs : Real.sin ψ = ei19b_dupSin k θ) (hc : Real.cos ψ = ei19b_dupCos k θ) :
    Real.tan (ψ / 2) = Real.tan θ * ei19b_delta k θ ∧
      Real.sin θ = Real.sin ψ / Real.sqrt ((1 + Real.cos ψ) * (1 + ei19b_delta k ψ)) ∧
      Real.cos θ = Real.sqrt ((Real.cos ψ + ei19b_delta k ψ) / (1 + ei19b_delta k ψ)) ∧
      Real.tan θ =
        Real.tan (ψ / 2) * Real.sqrt ((1 + Real.cos ψ) / (Real.cos ψ + ei19b_delta k ψ)) := by
  sorry

/-- DLMF 19.11.16–19.11.17: `Π(ψ, α², k) = 2Π(θ, α², k) + α² R_C(γ - δ, γ)`,
`γ = (csc²θ - α²)²(csc²ψ - α²)`, `δ = α²(1 - α²)(α² - k²)`, for real `k² < 1`,
`θ ∈ (0, π/2)`, `ψ` as in (19.11.12), on the branch region `α² < 1`,
`α²(1 - cos²θ cos ψ) < 1` (see the module docstring). -/
@[dlmf 19.11.E16, dlmf 19.11.E17]
theorem incEllIntPik_duplication {k θ ψ α2 : ℝ} (hk : k ^ 2 < 1) (hθ : θ ∈ Ioo 0 (π / 2))
    (hψ : ψ ∈ Icc 0 π) (hs : Real.sin ψ = ei19b_dupSin k θ) (hc : Real.cos ψ = ei19b_dupCos k θ)
    (hα : α2 < 1) (hαψ : α2 * (1 - Real.cos θ ^ 2 * Real.cos ψ) < 1) :
    let γ := (1 / Real.sin θ ^ 2 - α2) ^ 2 * (1 / Real.sin ψ ^ 2 - α2)
    let δ := α2 * (1 - α2) * (α2 - k ^ 2)
    incEllIntPik ψ α2 k =
      2 * incEllIntPik θ α2 k + α2 * symEllIntRC ((γ - δ : ℝ) : ℂ) ((γ : ℝ) : ℂ) := by
  sorry

end DLMF.EllipticIntegrals
