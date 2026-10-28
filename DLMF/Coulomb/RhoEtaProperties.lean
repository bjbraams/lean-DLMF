/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Coulomb.Defs
public import DLMF.Confluent.CoulombIrregular
public import DLMF.Confluent.Whittaker

/-!
# Coulomb functions `F_ℓ(η,ρ)`, `G_ℓ(η,ρ)`, `H^±_ℓ(η,ρ)`: basic properties
(DLMF §§33.2, 33.4, 33.13)

The functions are those of `DLMF.Coulomb.Basic` (namespace `DLMF.Confluent`): `ℓ ∈ ℕ`, real
`η`, and real `ρ`, with `ρ > 0` wherever DLMF's formulas involve `G_ℓ`, `H^±_ℓ`, `ln ρ` or
division by `ρ`. Derivatives are with respect to `ρ` (`deriv` of the real function, or of the
complex function `ρ ↦ H^±_ℓ(η,ρ)` of a real variable).

Earlier results on these functions are in `DLMF.Confluent.Coulomb` (the Coulomb equation for
the regular solution, 33.2.1, and the lower-sign form of 33.2.4) and
`DLMF.Confluent.CoulombIrregular` (`H^- = conj H^+`, 33.2.11 and the Wronskians 33.2.12).

## Main results

* `coulombF_deriv_deriv`: the Coulomb wave equation 33.2.1 for `F_ℓ`; `coulombG_deriv_deriv`.
* `turningPoint_isRoot`: 33.2.2; `coulomb_indicial`: the indices `ℓ+1`, `-ℓ` at `ρ = 0`.
* `ofReal_coulombF_eq_whittakerM`, `ofReal_coulombF_eq_whittakerM_neg`: 33.2.3.
* `coulombC_pos`, `coulombC_sq_eq_prod`: §33.2(ii) and 33.2.6.
* `coulombHPlus_eq_whittakerW`, `coulombHMinus_eq_whittakerW`: 33.2.7.
* `coulombF_mul_coulombG_sub`: the cross-product 33.2.13.
* `coulombF_recurrence`, `deriv_coulombF_lower`, `deriv_coulombF_upper` and the same for
  `G_ℓ`, `H^±_ℓ`: 33.4.2–33.4.4.
* `coulombC_eq_exp_sigma_mul_Gamma`, `recurrenceR_eq_coulombC_div`: 33.13.1–33.13.2.
-/

@[expose] public section

open Complex Filter Set
open scoped Real Topology Nat ComplexConjugate

noncomputable section

namespace DLMF.Coulomb

open DLMF.Confluent

/-! ### §33.2(i) The Coulomb wave equation -/

/-- **The Coulomb wave equation for `F_ℓ`** (DLMF 33.2.1):
`F_ℓ'' + (1 - 2η/ρ - ℓ(ℓ+1)/ρ²) F_ℓ = 0` for `ρ ≠ 0` (derivatives in `ρ`). -/
@[dlmf 33.2.E1]
theorem coulombF_deriv_deriv (ℓ : ℕ) (η : ℝ) {ρ : ℝ} (hρ : ρ ≠ 0) :
    deriv (deriv (coulombF ℓ η)) ρ +
      (1 - 2 * η / ρ - ℓ * (ℓ + 1) / ρ ^ 2) * coulombF ℓ η ρ = 0 := by
  have hd : deriv (coulombF ℓ η) =
      fun x : ℝ => ((coulombC ℓ η : ℂ) * coulombWaveDeriv ℓ η x).re := by
    funext x
    have h := hasDerivAt_re_comp
      (((hasDerivAt_coulombWave ℓ η (x : ℂ)).comp_ofReal).const_mul (coulombC ℓ η : ℂ))
    exact h.deriv
  have h2 := hasDerivAt_re_comp
    (((hasDerivAt_coulombWaveDeriv ℓ (η : ℂ) (z := (ρ : ℂ)) (by exact_mod_cast hρ)).comp_ofReal
      ).const_mul (coulombC ℓ η : ℂ))
  rw [hd, h2.deriv, coulombF]
  have hc : (2 * (η : ℂ) / ρ + ℓ * (ℓ + 1) / ρ ^ 2 - 1) =
      ((2 * η / ρ + ℓ * (ℓ + 1) / ρ ^ 2 - 1 : ℝ) : ℂ) := by push_cast; ring
  rw [hc, show ∀ c : ℂ, ∀ r : ℝ, c * ((r : ℂ) * coulombWave ℓ η ρ) =
    (r : ℂ) * (c * coulombWave ℓ η ρ) from fun c r => by ring, re_ofReal_mul]
  ring

/-- The indices of the regular singularity `ρ = 0` of DLMF 33.2.1 are `ℓ + 1` and `-ℓ`
(DLMF §33.2(i)): `s(s-1) = ℓ(ℓ+1)` exactly for these `s`. -/
@[dlmf 33.2.i]
theorem coulomb_indicial (ℓ : ℕ) (s : ℂ) :
    s * (s - 1) = ℓ * (ℓ + 1) ↔ s = ℓ + 1 ∨ s = -ℓ := by
  have h : s * (s - 1) - ℓ * (ℓ + 1) = (s - (ℓ + 1)) * (s + ℓ) := by ring
  rw [← sub_eq_zero, h, mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg]

/-- **The outer turning point** (DLMF 33.2.2): `ρ_tp(η,ℓ) = η + (η² + ℓ(ℓ+1))^{1/2}` is the
largest root of `ρ² - 2ηρ - ℓ(ℓ+1) = 0`, the numerator of the coefficient
`1 - 2η/ρ - ℓ(ℓ+1)/ρ²` of DLMF 33.2.1 (the turning points are where `w'' = 0`). -/
@[dlmf 33.2.E2]
theorem turningPoint_isRoot (η : ℝ) (ℓ : ℕ) :
    turningPoint η ℓ ^ 2 - 2 * η * turningPoint η ℓ - ℓ * (ℓ + 1) = 0 ∧
      ∀ ρ : ℝ, ρ ^ 2 - 2 * η * ρ - ℓ * (ℓ + 1) = 0 → ρ ≤ turningPoint η ℓ := by
  have h0 : (0 : ℝ) ≤ η ^ 2 + ℓ * (ℓ + 1) := by positivity
  have hs := Real.sq_sqrt h0
  have hs0 := Real.sqrt_nonneg (η ^ 2 + ℓ * (ℓ + 1))
  refine ⟨?_, fun ρ hρ => ?_⟩
  · rw [turningPoint]; nlinarith
  · rw [turningPoint]
    nlinarith [sq_nonneg (ρ - η - Real.sqrt (η ^ 2 + ℓ * (ℓ + 1)))]

/-- `ρ_tp` is a zero of the coefficient `1 - 2η/ρ - ℓ(ℓ+1)/ρ²` of DLMF 33.2.1 when it is
nonzero. -/
@[dlmf 33.2.E2]
theorem coulomb_coeff_turningPoint (η : ℝ) (ℓ : ℕ) (h : turningPoint η ℓ ≠ 0) :
    1 - 2 * η / turningPoint η ℓ - ℓ * (ℓ + 1) / turningPoint η ℓ ^ 2 = 0 := by
  have h1 := (turningPoint_isRoot η ℓ).1
  field_simp
  linear_combination h1

/-! ### §33.2(ii) The regular solution -/

/-- `Γ(ℓ + 1 + iη) ≠ 0`. -/
theorem c33a_Gamma_ne_zero (ℓ : ℕ) (η : ℝ) : Gamma ((ℓ : ℂ) + 1 + I * η) ≠ 0 := by
  refine Complex.Gamma_ne_zero fun m hm => ?_
  have := congrArg Complex.re hm
  simp at this
  linarith [(Nat.cast_nonneg ℓ : (0 : ℝ) ≤ ℓ), (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

/-- **`C_ℓ(η)` is positive** (DLMF §33.2(ii)). -/
@[dlmf 33.2.ii]
theorem coulombC_pos (ℓ : ℕ) (η : ℝ) : 0 < coulombC ℓ η := by
  rw [coulombC]
  have := norm_pos_iff.mpr (c33a_Gamma_ne_zero ℓ η)
  positivity

/-- **`F_ℓ` via Whittaker's `M`, upper signs** (DLMF 33.2.3):
`F_ℓ(η,ρ) = C_ℓ(η) 2^{-ℓ-1} (-i)^{ℓ+1} M_{iη,ℓ+1/2}(2iρ)`. -/
@[dlmf 33.2.E3]
theorem ofReal_coulombF_eq_whittakerM (ℓ : ℕ) (η ρ : ℝ) :
    (coulombF ℓ η ρ : ℂ) = coulombC ℓ η * ((2 : ℂ) ^ (ℓ + 1))⁻¹ * (-I) ^ (ℓ + 1) *
      whittakerM (I * η) (ℓ + 1 / 2) (2 * I * ρ) := by
  rw [ofReal_coulombF, coulombWave, whittakerM,
    show (ℓ : ℂ) + 1 / 2 + 1 / 2 = ((ℓ + 1 : ℕ) : ℂ) by push_cast; ring, cpow_natCast,
    show (ℓ : ℂ) + 1 / 2 - I * η + 1 / 2 = ℓ + 1 - I * η by ring,
    show 1 + 2 * ((ℓ : ℂ) + 1 / 2) = 2 * ℓ + 2 by ring,
    show -(2 * I * (ρ : ℂ)) / 2 = -I * ρ by ring]
  have h2 : (2 : ℂ) ^ (ℓ + 1) ≠ 0 := pow_ne_zero _ two_ne_zero
  have hI : ((2 : ℂ) ^ (ℓ + 1))⁻¹ * (-I) ^ (ℓ + 1) * (2 * I * ρ) ^ (ℓ + 1) = (ρ : ℂ) ^ (ℓ + 1) := by
    rw [mul_pow, mul_pow, show ((2 : ℂ) ^ (ℓ + 1))⁻¹ * (-I) ^ (ℓ + 1) *
        (2 ^ (ℓ + 1) * I ^ (ℓ + 1) * (ρ : ℂ) ^ (ℓ + 1)) =
        (((2 : ℂ) ^ (ℓ + 1))⁻¹ * 2 ^ (ℓ + 1)) * ((-I) ^ (ℓ + 1) * I ^ (ℓ + 1)) *
          (ρ : ℂ) ^ (ℓ + 1) by ring, inv_mul_cancel₀ h2, ← mul_pow, neg_mul, I_mul_I, neg_neg,
      one_pow, one_mul, one_mul]
  linear_combination (coulombC ℓ η * exp (-I * ρ) *
    kummerM (ℓ + 1 - I * η) (2 * ℓ + 2) (2 * I * ρ)) * hI.symm

/-- **`F_ℓ` via Whittaker's `M`, lower signs** (DLMF 33.2.3):
`F_ℓ(η,ρ) = C_ℓ(η) 2^{-ℓ-1} i^{ℓ+1} M_{-iη,ℓ+1/2}(-2iρ)`. -/
@[dlmf 33.2.E3]
theorem ofReal_coulombF_eq_whittakerM_neg (ℓ : ℕ) (η ρ : ℝ) :
    (coulombF ℓ η ρ : ℂ) = coulombC ℓ η * ((2 : ℂ) ^ (ℓ + 1))⁻¹ * I ^ (ℓ + 1) *
      whittakerM (-(I * η)) (ℓ + 1 / 2) (-(2 * I * ρ)) := by
  rw [ofReal_coulombF, coulombWave_eq_conj_form, whittakerM,
    show (ℓ : ℂ) + 1 / 2 + 1 / 2 = ((ℓ + 1 : ℕ) : ℂ) by push_cast; ring, cpow_natCast,
    show (ℓ : ℂ) + 1 / 2 - -(I * η) + 1 / 2 = ℓ + 1 + I * η by ring,
    show 1 + 2 * ((ℓ : ℂ) + 1 / 2) = 2 * ℓ + 2 by ring,
    show -(-(2 * I * (ρ : ℂ))) / 2 = I * ρ by ring]
  have h2 : (2 : ℂ) ^ (ℓ + 1) ≠ 0 := pow_ne_zero _ two_ne_zero
  have hI : ((2 : ℂ) ^ (ℓ + 1))⁻¹ * I ^ (ℓ + 1) * (-(2 * I * ρ)) ^ (ℓ + 1) =
      (ρ : ℂ) ^ (ℓ + 1) := by
    rw [show -(2 * I * (ρ : ℂ)) = 2 * (-I) * ρ by ring, mul_pow, mul_pow,
      show ((2 : ℂ) ^ (ℓ + 1))⁻¹ * I ^ (ℓ + 1) *
        (2 ^ (ℓ + 1) * (-I) ^ (ℓ + 1) * (ρ : ℂ) ^ (ℓ + 1)) =
        (((2 : ℂ) ^ (ℓ + 1))⁻¹ * 2 ^ (ℓ + 1)) * (I ^ (ℓ + 1) * (-I) ^ (ℓ + 1)) *
          (ρ : ℂ) ^ (ℓ + 1) by ring, inv_mul_cancel₀ h2, ← mul_pow, mul_neg, I_mul_I, neg_neg,
      one_pow, one_mul, one_mul]
  linear_combination (coulombC ℓ η * exp (I * ρ) *
    kummerM (ℓ + 1 + I * η) (2 * ℓ + 2) (-(2 * I * ρ))) * hI.symm

/-- For `η ≠ 0`, `|Γ(1 + iη)|² = πη / sinh(πη)`. -/
theorem c33a_normSq_Gamma_one (η : ℝ) (hη : η ≠ 0) :
    ‖Gamma (1 + I * η)‖ ^ 2 = π * η / Real.sinh (π * η) := by
  have hconj : Gamma (1 - I * η) = conj (Gamma (1 + I * η)) := by
    rw [← Complex.Gamma_conj]; congr 1; simp [Complex.conj_ofReal]; ring
  have hmul : Gamma (1 + I * η) * Gamma (1 - I * η) = ((π * η / Real.sinh (π * η) : ℝ) : ℂ) := by
    have h0 : (I * η : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (by exact_mod_cast hη)
    rw [show (1 : ℂ) + I * η = I * η + 1 by ring, Complex.Gamma_add_one _ h0, mul_assoc,
      Complex.Gamma_mul_Gamma_one_sub, show (π : ℂ) * (I * η) = ((π * η : ℝ) : ℂ) * I by
        push_cast; ring, Complex.sin_mul_I, ← Complex.ofReal_sinh]
    have hs : Real.sinh (π * η) ≠ 0 := by
      rw [Ne, Real.sinh_eq_zero]; exact mul_ne_zero Real.pi_ne_zero hη
    have hs' : ((Real.sinh (π * η) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs
    push_cast
    field_simp
  rw [hconj, Complex.mul_conj, Complex.normSq_eq_norm_sq] at hmul
  exact_mod_cast hmul

/-- `|Γ(ℓ + 1 + iη)|² = |Γ(1 + iη)|² ∏_{k=1}^{ℓ} (η² + k²)`. -/
theorem c33a_normSq_Gamma_succ (ℓ : ℕ) (η : ℝ) :
    ‖Gamma ((ℓ : ℂ) + 1 + I * η)‖ ^ 2 =
      ‖Gamma (1 + I * η)‖ ^ 2 * ∏ k ∈ Finset.Icc 1 ℓ, (η ^ 2 + (k : ℝ) ^ 2) := by
  induction ℓ with
  | zero => simp
  | succ n ih =>
    have hne : (n : ℂ) + 1 + I * η ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this
      linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    rw [show ((n + 1 : ℕ) : ℂ) + 1 + I * η = ((n : ℂ) + 1 + I * η) + 1 by push_cast; ring,
      Complex.Gamma_add_one _ hne, norm_mul, mul_pow, ih, Finset.prod_Icc_succ_top (by omega)]
    have hn : ‖(n : ℂ) + 1 + I * η‖ ^ 2 = η ^ 2 + ((n + 1 : ℕ) : ℝ) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp; ring
    rw [hn]; ring

/-- **The alternative form of `C_ℓ(η)`** (DLMF 33.2.6), squared:
`C_ℓ(η)² = 2^{2ℓ} (2πη/(e^{2πη}-1)) ∏_{k=1}^{ℓ} (η² + k²) / ((2ℓ+1)!)²` for `η ≠ 0`
(at `η = 0` the factor `2πη/(e^{2πη}-1)` is read as its limit `1`, see 33.5.6).
Since `C_ℓ(η) > 0` (`coulombC_pos`) this is 33.2.6. -/
@[dlmf 33.2.E6]
theorem coulombC_sq_eq_prod (ℓ : ℕ) {η : ℝ} (hη : η ≠ 0) :
    coulombC ℓ η ^ 2 = 2 ^ (2 * ℓ) * (2 * π * η / (Real.exp (2 * π * η) - 1) *
      ∏ k ∈ Finset.Icc 1 ℓ, (η ^ 2 + (k : ℝ) ^ 2)) / ((2 * ℓ + 1)! : ℝ) ^ 2 := by
  have hx : π * η ≠ 0 := mul_ne_zero Real.pi_ne_zero hη
  have hs : Real.sinh (π * η) ≠ 0 := by rw [Ne, Real.sinh_eq_zero]; exact hx
  have he : Real.exp (2 * π * η) - 1 ≠ 0 := by
    rw [sub_ne_zero, Ne, Real.exp_eq_one_iff]; intro h; apply hx; linarith
  have hkey : Real.exp (-π * η) * (π * η / Real.sinh (π * η)) =
      2 * π * η / (Real.exp (2 * π * η) - 1) := by
    rw [Real.sinh_eq, show 2 * π * η = π * η + π * η by ring, Real.exp_add,
      show -π * η = -(π * η) by ring, Real.exp_neg]
    have hE := Real.exp_pos (π * η)
    have h2 : Real.exp (π * η) * Real.exp (π * η) - 1 ≠ 0 := by
      rw [← Real.exp_add]; convert he using 2; ring_nf
    field_simp
    ring
  rw [coulombC, div_pow, mul_pow, mul_pow, ← pow_mul, mul_comm ℓ 2, c33a_normSq_Gamma_succ,
    c33a_normSq_Gamma_one η hη, ← Real.exp_nat_mul]
  rw [show ((2 : ℕ) : ℝ) * (-π * η / 2) = -π * η by push_cast; ring, ← hkey]
  ring

/-- **DLMF 33.2.6** in its printed form, for `η ≠ 0`. -/
@[dlmf 33.2.E6]
theorem coulombC_eq_sqrt_prod (ℓ : ℕ) {η : ℝ} (hη : η ≠ 0) :
    coulombC ℓ η = 2 ^ ℓ * Real.sqrt (2 * π * η / (Real.exp (2 * π * η) - 1) *
      ∏ k ∈ Finset.Icc 1 ℓ, (η ^ 2 + (k : ℝ) ^ 2)) / ((2 * ℓ + 1)! : ℝ) := by
  have hC := coulombC_pos ℓ η
  have hsq := coulombC_sq_eq_prod ℓ hη
  have hf : (0 : ℝ) < ((2 * ℓ + 1)! : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hP : 0 ≤ 2 * π * η / (Real.exp (2 * π * η) - 1) *
      ∏ k ∈ Finset.Icc 1 ℓ, (η ^ 2 + (k : ℝ) ^ 2) := by
    have h1 : 0 ≤ 2 * π * η / (Real.exp (2 * π * η) - 1) := by
      rcases lt_or_gt_of_ne hη with h | h
      · apply div_nonneg_of_nonpos
        · nlinarith [Real.pi_pos]
        · linarith [Real.exp_lt_one_iff.mpr (show 2 * π * η < 0 by nlinarith [Real.pi_pos])]
      · apply div_nonneg
        · positivity
        · linarith [Real.one_lt_exp_iff.mpr (show 0 < 2 * π * η by positivity)]
    exact mul_nonneg h1 (Finset.prod_nonneg fun k _ => by positivity)
  rw [eq_div_iff hf.ne', ← Real.sqrt_sq (by positivity : 0 ≤ coulombC ℓ η * (2 * ℓ + 1)!),
    mul_pow, hsq, div_mul_cancel₀ _ (by positivity), pow_mul', Real.sqrt_mul (by positivity),
    Real.sqrt_sq (by positivity)]

/-- **Analyticity of `F_ℓ`** (DLMF §33.2(ii)): `F_ℓ(η,ρ)` is real (by definition here, see
`ofReal_coulombF`) and analytic in `ρ` on `0 < ρ < ∞` and in `η ∈ ℝ`. -/
@[dlmf 33.2.ii]
theorem analytic_coulombF (ℓ : ℕ) :
    (∀ η : ℝ, AnalyticOnNhd ℝ (coulombF ℓ η) (Ioi 0)) ∧
      ∀ ρ : ℝ, 0 < ρ → AnalyticOnNhd ℝ (fun η => coulombF ℓ η ρ) univ := by
  sorry

/-! ### §33.2(iii) The irregular solutions -/

/-- **`H^±_ℓ` via Whittaker's `W`, upper sign** (DLMF 33.2.7):
`H^+_ℓ(η,ρ) = (-i)^ℓ e^{πη/2 + iσ_ℓ(η)} W_{-iη,ℓ+1/2}(-2iρ)`, `ρ > 0`. -/
@[dlmf 33.2.E7]
theorem coulombHPlus_eq_whittakerW (ℓ : ℕ) (η : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    coulombHPlus ℓ η ρ = (-I) ^ ℓ * exp (π * η / 2 + I * coulombSigma ℓ η) *
      whittakerW (-(I * η)) (ℓ + 1 / 2) (-2 * I * ρ) := by
  rw [coulombHPlus_eq ℓ η hρ, whittakerW,
    show (1 : ℂ) / 2 + (ℓ + 1 / 2) = ((ℓ + 1 : ℕ) : ℂ) by push_cast; ring, cpow_natCast,
    show ((ℓ + 1 : ℕ) : ℂ) - -(I * η) = ℓ + 1 + I * η by push_cast; ring,
    show 1 + 2 * ((ℓ : ℂ) + 1 / 2) = 2 * ℓ + 2 by ring,
    show -(-2 * I * (ρ : ℂ)) / 2 = I * ρ by ring, coulombAPlus,
    show I * (coulombSigma ℓ η : ℂ) = coulombSigma ℓ η * I by ring, exp_add, ofReal_exp]
  have hpow : (-I) ^ ℓ * (-2 * I) ^ (ℓ + 1) = (2 : ℂ) ^ (ℓ + 1) * (-1) ^ ℓ * (-I) := by
    have h : (-I) ^ ℓ * (-2 * I) ^ ℓ = (2 : ℂ) ^ ℓ * (-1) ^ ℓ := by
      rw [← mul_pow, ← mul_pow]
      congr 1
      linear_combination 2 * I_sq
    rw [pow_succ, pow_succ]
    linear_combination (-2 * I) * h
  rw [mul_pow (-2 * I)]
  push_cast
  linear_combination (-1 : ℂ) * (exp (coulombSigma ℓ η * I) * exp (π * η / 2) * (ρ : ℂ) ^ (ℓ + 1) *
    exp (I * ρ) * kummerU ((ℓ : ℂ) + 1 + I * η) (2 * ℓ + 2) (-2 * I * ρ)) * hpow

/-- **`H^±_ℓ` via Whittaker's `W`, lower sign** (DLMF 33.2.7):
`H^-_ℓ(η,ρ) = i^ℓ e^{πη/2 - iσ_ℓ(η)} W_{iη,ℓ+1/2}(2iρ)`, `ρ > 0`. -/
@[dlmf 33.2.E7]
theorem coulombHMinus_eq_whittakerW (ℓ : ℕ) (η : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    coulombHMinus ℓ η ρ = I ^ ℓ * exp (π * η / 2 - I * coulombSigma ℓ η) *
      whittakerW (I * η) (ℓ + 1 / 2) (2 * I * ρ) := by
  rw [coulombHMinus_eq ℓ η hρ, whittakerW,
    show (1 : ℂ) / 2 + (ℓ + 1 / 2) = ((ℓ + 1 : ℕ) : ℂ) by push_cast; ring, cpow_natCast,
    show ((ℓ + 1 : ℕ) : ℂ) - I * η = ℓ + 1 - I * η by push_cast; ring,
    show 1 + 2 * ((ℓ : ℂ) + 1 / 2) = 2 * ℓ + 2 by ring,
    show -(2 * I * (ρ : ℂ)) / 2 = -I * ρ by ring, coulombAPlus,
    show (π : ℂ) * η / 2 - I * coulombSigma ℓ η = π * η / 2 + -(coulombSigma ℓ η * I) by ring,
    exp_add]
  simp only [map_mul, map_pow, map_neg, map_one, map_ofNat, conj_I, ← exp_conj, conj_ofReal,
    neg_neg]
  have hpow : I ^ ℓ * (2 * I) ^ (ℓ + 1) = (2 : ℂ) ^ (ℓ + 1) * (-1) ^ ℓ * I := by
    have h : I ^ ℓ * (2 * I) ^ ℓ = (2 : ℂ) ^ ℓ * (-1) ^ ℓ := by
      rw [← mul_pow, ← mul_pow]
      congr 1
      linear_combination 2 * I_sq
    rw [pow_succ, pow_succ]
    linear_combination (2 * I) * h
  rw [mul_pow (2 * I), ofReal_exp, show (coulombSigma ℓ η : ℂ) * -I = -(coulombSigma ℓ η * I) by
    ring]
  push_cast
  linear_combination (-1 : ℂ) * (exp (-(coulombSigma ℓ η * I)) * exp (π * η / 2) *
    (ρ : ℂ) ^ (ℓ + 1) *
    exp (-I * ρ) * kummerU ((ℓ : ℂ) + 1 - I * η) (2 * ℓ + 2) (2 * I * ρ)) * hpow

/-- `0 ≤ x - arctan x ≤ x³` for `x ≥ 0`. -/
lemma q2a_sub_arctan_le_of_nonneg {x : ℝ} (hx : 0 ≤ x) : x - Real.arctan x ≤ x ^ 3 := by
  let g : ℝ → ℝ := fun y => y ^ 3 - y + Real.arctan y
  have hd : ∀ y, HasDerivAt g (3 * y ^ 2 - 1 + 1 / (1 + y ^ 2)) y := by
    intro y
    have := (((hasDerivAt_pow 3 y).sub (hasDerivAt_id y)).add (Real.hasDerivAt_arctan y))
    convert this using 1
    funext z; simp [g]
  have hmono : MonotoneOn g (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun y _ => (hd y).continuousAt.continuousWithinAt)
      (fun y _ => (hd y).differentiableAt.differentiableWithinAt) ?_
    intro y _
    rw [(hd y).deriv]
    have h1 : 0 < 1 + y ^ 2 := by positivity
    have : 1 - 1 / (1 + y ^ 2) = y ^ 2 / (1 + y ^ 2) := by field_simp; ring
    have h2 : y ^ 2 / (1 + y ^ 2) ≤ y ^ 2 := div_le_self (sq_nonneg y) (by nlinarith)
    nlinarith [sq_nonneg y]
  have := hmono (Set.self_mem_Ici) hx hx
  simp only [g, Real.arctan_zero] at this
  linarith

/-- `|x - arctan x| ≤ |x|³`. -/
lemma q2a_abs_sub_arctan_le (x : ℝ) : |x - Real.arctan x| ≤ |x| ^ 3 := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.arctan_le_self hx)), abs_of_nonneg hx]
    exact q2a_sub_arctan_le_of_nonneg hx
  · have h := q2a_sub_arctan_le_of_nonneg (neg_nonneg.mpr hx)
    rw [Real.arctan_neg] at h
    rw [abs_of_nonpos (sub_nonpos.mpr (Real.self_le_arctan hx)), abs_of_nonpos hx]
    linarith

/-- The summable majorant `M³/(n+1)³`. -/
lemma q2a_summable_bound (M : ℝ) :
    Summable (fun n : ℕ => M ^ 3 / ((n : ℝ) + 1) ^ 3) := by
  have h := (summable_nat_add_iff 1).mpr (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 3))
  simpa [div_eq_mul_inv] using h.mul_left (M ^ 3)

/-- `|t - arctan t| ≤ |η|³/(n+1)³` for `t = η/(n+1)`. -/
lemma q2a_term_bound (η : ℝ) (n : ℕ) :
    ‖η / ((n : ℝ) + 1) - Real.arctan (η / ((n : ℝ) + 1))‖ ≤ |η| ^ 3 / ((n : ℝ) + 1) ^ 3 := by
  rw [Real.norm_eq_abs]
  refine (q2a_abs_sub_arctan_le _).trans (le_of_eq ?_)
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1), div_pow]

/-- The series in the Weierstrass form of `phaseShift` converges. -/
lemma q2a_summable_phase (η : ℝ) :
    Summable (fun n : ℕ => η / ((n : ℝ) + 1) - Real.arctan (η / ((n : ℝ) + 1))) :=
  Summable.of_norm_bounded (q2a_summable_bound |η|) (q2a_term_bound η)

/-- The series in the Weierstrass form of `phaseShift` is continuous in `η`. -/
lemma q2a_continuous_phase_tsum :
    Continuous (fun η : ℝ => ∑' n : ℕ, (η / ((n : ℝ) + 1) - Real.arctan (η / ((n : ℝ) + 1)))) := by
  rw [continuous_iff_continuousAt]
  intro x
  set M := |x| + 1
  have hc : ContinuousOn
      (fun η : ℝ => ∑' n : ℕ, (η / ((n : ℝ) + 1) - Real.arctan (η / ((n : ℝ) + 1))))
      (Icc (-M) M) := by
    refine continuousOn_tsum (fun n => by fun_prop) (q2a_summable_bound M) ?_
    intro n η hη
    refine (q2a_term_bound η n).trans ?_
    have : |η| ≤ M := abs_le.mpr ⟨hη.1, hη.2⟩
    gcongr
  refine hc.continuousAt (Icc_mem_nhds ?_ ?_)
  · have := neg_abs_le x; simp only [M]; linarith
  · have := le_abs_self x; simp only [M]; linarith

/-- Polar form `c + iη = |c + iη| e^{i arctan(η/c)}` for `c > 0`. -/
lemma q2a_mul_exp_arctan {c : ℝ} (hc : 0 < c) (η : ℝ) :
    (c : ℂ) + I * η = (‖(c : ℂ) + I * η‖ : ℂ) * exp (I * Real.arctan (η / c)) := by
  have hn : ‖(c : ℂ) + I * η‖ = c * Real.sqrt (1 + (η / c) ^ 2) := by
    rw [show (c : ℂ) + I * η = ⟨c, η⟩ by apply Complex.ext <;> simp,
      Complex.norm_eq_sqrt_sq_add_sq, ← Real.sqrt_sq hc.le, ← Real.sqrt_mul (sq_nonneg c),
      Real.sqrt_sq hc.le]
    congr 1
    field_simp
  have hs : 0 < Real.sqrt (1 + (η / c) ^ 2) := Real.sqrt_pos.mpr (by positivity)
  rw [hn, mul_comm I (Real.arctan (η / c) : ℂ), exp_mul_I, ← ofReal_cos, ← ofReal_sin,
    Real.cos_arctan, Real.sin_arctan]
  apply Complex.ext <;> simp <;> field_simp


/-- Polar form of Euler's sequence `GammaSeq (1+iη) n`. -/
lemma q2a_GammaSeq_eq (η : ℝ) {n : ℕ} (hn : n ≠ 0) :
    GammaSeq (1 + I * η) n =
      (((n : ℝ) * n ! / ∏ j ∈ Finset.range (n + 1), ‖(((j : ℝ) + 1 : ℝ) : ℂ) + I * η‖ : ℝ) : ℂ) *
        exp (I * (η * Real.log n -
          ∑ j ∈ Finset.range (n + 1), Real.arctan (η / ((j : ℝ) + 1)) : ℝ)) := by
  rw [GammaSeq]
  have hp : ∏ j ∈ Finset.range (n + 1), (1 + I * η + (j : ℂ)) =
      ∏ j ∈ Finset.range (n + 1), ((‖(((j : ℝ) + 1 : ℝ) : ℂ) + I * η‖ : ℂ) *
        exp (I * Real.arctan (η / ((j : ℝ) + 1)))) := by
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← q2a_mul_exp_arctan (by positivity : (0 : ℝ) < (j : ℝ) + 1) η]
    push_cast; ring
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hlog : log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (Nat.cast_nonneg n)]; simp
  rw [hp, Finset.prod_mul_distrib, ← exp_sum, cpow_add _ _ hn0, cpow_one,
    cpow_def_of_ne_zero hn0, hlog]
  have hP : (∏ j ∈ Finset.range (n + 1), (‖(((j : ℝ) + 1 : ℝ) : ℂ) + I * η‖ : ℂ)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro j _
    have : (0 : ℝ) < ‖(((j : ℝ) + 1 : ℝ) : ℂ) + I * η‖ := by
      apply norm_pos_iff.mpr
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    exact_mod_cast this.ne'
  have hsub : exp (I * ((η * Real.log n - ∑ j ∈ Finset.range (n + 1),
      Real.arctan (η / ((j : ℝ) + 1)) : ℝ) : ℂ)) =
      exp (Real.log n * (I * η)) / exp (∑ j ∈ Finset.range (n + 1),
        I * Real.arctan (η / ((j : ℝ) + 1))) := by
    rw [← exp_sub]; congr 1
    simp only [ofReal_sub, ofReal_mul, ofReal_sum]
    rw [mul_sub, Finset.mul_sum]; ring_nf
  rw [hsub]
  push_cast
  field_simp

/-- The phases of `GammaSeq (1+iη) n` converge to `phaseShift 0 η`. -/
lemma q2a_tendsto_phase (η : ℝ) :
    Tendsto (fun n : ℕ => η * Real.log n -
      ∑ j ∈ Finset.range (n + 1), Real.arctan (η / ((j : ℝ) + 1))) atTop
      (𝓝 (phaseShift 0 η)) := by
  have hH : Tendsto (fun n : ℕ => (harmonic (n + 1) : ℝ) - Real.log ((n : ℝ) + 1)) atTop
      (𝓝 Real.eulerMascheroniConstant) := by
    have := Real.tendsto_harmonic_sub_log.comp (tendsto_add_atTop_nat 1)
    refine this.congr fun n => ?_
    simp
  have hS := (q2a_summable_phase η).hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have h := ((hH.add Real.tendsto_log_nat_add_one_sub_log).const_mul (-η)).add hS
  rw [phaseShift]
  simp only [Finset.range_zero, Finset.sum_empty, add_zero, add_zero]
  convert h using 1
  · funext n
    simp only [Function.comp_apply, harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast,
      Finset.sum_sub_distrib]
    have hs : ∑ x ∈ Finset.range (n + 1), η / ((x : ℝ) + 1) =
        η * ∑ x ∈ Finset.range (n + 1), ((x + 1 : ℕ) : ℝ)⁻¹ := by
      rw [Finset.mul_sum]; push_cast; simp [div_eq_mul_inv]
    rw [hs]
    ring
  · congr 1; ring

/-- **DLMF 33.2.10 at `ℓ = 0`**: `Γ(1+iη) = |Γ(1+iη)| e^{iσ_0(η)}` with the Weierstrass branch. -/
lemma q2a_Gamma_phase_zero (η : ℝ) :
    Gamma (1 + I * η) = ‖Gamma (1 + I * η)‖ * exp (I * phaseShift 0 η) := by
  have hlim := GammaSeq_tendsto_Gamma (1 + I * η)
  have h2 : Tendsto (fun n : ℕ => (‖GammaSeq (1 + I * η) n‖ : ℂ) *
      exp (I * ((η * Real.log n -
        ∑ j ∈ Finset.range (n + 1), Real.arctan (η / ((j : ℝ) + 1)) : ℝ) : ℂ))) atTop
      (𝓝 ((‖Gamma (1 + I * η)‖ : ℂ) * exp (I * phaseShift 0 η))) := by
    refine ((continuous_ofReal.tendsto _).comp hlim.norm).mul ?_
    exact ((continuous_exp.comp (continuous_const.mul continuous_ofReal)).tendsto _).comp
      (q2a_tendsto_phase η)
  refine tendsto_nhds_unique hlim (h2.congr' ?_)
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hE : ∀ x : ℝ, ‖exp (I * (x : ℂ))‖ = 1 := fun x => by
    rw [mul_comm]; exact norm_exp_ofReal_mul_I x
  rw [q2a_GammaSeq_eq η hn, norm_mul, hE, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]


/-- `σ_{ℓ+1}(η) = σ_ℓ(η) + arctan(η/(ℓ+1))`. -/
lemma q2a_phaseShift_succ (ℓ : ℕ) (η : ℝ) :
    phaseShift (ℓ + 1) η = phaseShift ℓ η + Real.arctan (η / ((ℓ : ℝ) + 1)) := by
  simp only [phaseShift, Finset.sum_range_succ]
  ring

/-- **The phase shift with DLMF's branch** (DLMF 33.2.10): `σ_ℓ(η)` is a phase of
`Γ(ℓ+1+iη)`, i.e. `Γ(ℓ+1+iη) = |Γ(ℓ+1+iη)| e^{iσ_ℓ(η)}`; it vanishes at `η = 0` and is
continuous in `η`. It differs from the principal phase `coulombSigma` by a multiple of `2π`. -/
@[dlmf 33.2.E10]
theorem phaseShift_spec (ℓ : ℕ) :
    (∀ η : ℝ, Gamma ((ℓ : ℂ) + 1 + I * η) =
      ‖Gamma ((ℓ : ℂ) + 1 + I * η)‖ * exp (I * phaseShift ℓ η)) ∧
    phaseShift ℓ 0 = 0 ∧ Continuous (phaseShift ℓ) := by
  refine ⟨fun η => ?_, ?_, ?_⟩
  · induction ℓ with
    | zero => simpa using q2a_Gamma_phase_zero η
    | succ n ih =>
      have hne : (n : ℂ) + 1 + I * η ≠ 0 := by
        intro h; have := congrArg Complex.re h; simp at this
        linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
      have ha := q2a_mul_exp_arctan (by positivity : (0 : ℝ) < (n : ℝ) + 1) η
      rw [ofReal_add, ofReal_natCast, ofReal_one] at ha
      rw [show ((n + 1 : ℕ) : ℂ) + 1 + I * η = ((n : ℂ) + 1 + I * η) + 1 by push_cast; ring,
        Complex.Gamma_add_one _ hne, norm_mul, q2a_phaseShift_succ, ofReal_add, mul_add, exp_add]
      generalize Gamma ((n : ℂ) + 1 + I * η) = g at ih ⊢
      conv_lhs => rw [ha, ih]
      push_cast
      ring
  · simp [phaseShift]
  · unfold phaseShift
    exact ((continuous_const.mul continuous_id).add q2a_continuous_phase_tsum).add
      (by fun_prop)

/-- `e^{iσ_ℓ}` does not depend on the branch: `e^{i phaseShift} = e^{i coulombSigma}`
(DLMF 33.2.10). -/
theorem exp_I_phaseShift (ℓ : ℕ) (η : ℝ) :
    exp (I * phaseShift ℓ η) = exp (I * coulombSigma ℓ η) := by
  have h := (phaseShift_spec ℓ).1 η
  have hg := c33a_Gamma_ne_zero ℓ η
  have hn : (‖Gamma ((ℓ : ℂ) + 1 + I * η)‖ : ℂ) ≠ 0 := by
    exact_mod_cast (norm_pos_iff.mpr hg).ne'
  have h2 := norm_mul_exp_arg_mul_I (Gamma ((ℓ : ℂ) + 1 + I * η))
  rw [coulombSigma]
  apply mul_left_cancel₀ hn
  rw [← h, mul_comm I ((arg (Gamma ((ℓ : ℂ) + 1 + I * η)) : ℝ) : ℂ), h2]

/-- **`H^+_ℓ` and `H^-_ℓ` are complex conjugates** (DLMF §33.2(iii)), `ρ > 0`. -/
@[dlmf 33.2.iii]
theorem coulombHMinus_eq_conj_coulombHPlus (ℓ : ℕ) (η : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    coulombHMinus ℓ η ρ = conj (coulombHPlus ℓ η ρ) :=
  coulombHMinus_eq_conj ℓ η hρ

/-- **Analyticity of the irregular solutions** (DLMF §33.2(iii)): `H^±_ℓ` and `G_ℓ` are
analytic in `ρ` on `0 < ρ < ∞`, and `e^{∓iσ_ℓ(η)} H^±_ℓ(η,ρ)` are analytic in `η ∈ ℝ`. -/
@[dlmf 33.2.iii]
theorem analytic_coulombH (ℓ : ℕ) :
    (∀ η : ℝ, AnalyticOnNhd ℝ (fun ρ : ℝ => coulombHPlus ℓ η ρ) (Ioi 0) ∧
      AnalyticOnNhd ℝ (fun ρ : ℝ => coulombHMinus ℓ η ρ) (Ioi 0) ∧
      AnalyticOnNhd ℝ (coulombG ℓ η) (Ioi 0)) ∧
    ∀ ρ : ℝ, 0 < ρ →
      AnalyticOnNhd ℝ (fun η : ℝ => exp (-(I * phaseShift ℓ η)) * coulombHPlus ℓ η ρ) univ ∧
      AnalyticOnNhd ℝ (fun η : ℝ => exp (I * phaseShift ℓ η) * coulombHMinus ℓ η ρ) univ := by
  sorry

/-! ### §33.4 Recurrence relations and derivatives -/

/-- `R_{ℓ+1}(η) = √((ℓ+1)² + η²)/(ℓ+1)`. -/
theorem c33a_recurrenceR_succ (ℓ : ℕ) (η : ℝ) :
    recurrenceR (ℓ + 1) η = Real.sqrt (((ℓ : ℝ) + 1) ^ 2 + η ^ 2) / (ℓ + 1) := by
  have hl : (0 : ℝ) < (ℓ : ℝ) + 1 := by positivity
  rw [recurrenceR, show 1 + η ^ 2 / ((ℓ + 1 : ℕ) : ℝ) ^ 2 =
      (((ℓ : ℝ) + 1) ^ 2 + η ^ 2) / ((ℓ : ℝ) + 1) ^ 2 by push_cast; field_simp,
    Real.sqrt_div' _ (by positivity), Real.sqrt_sq hl.le]

/-- `R_{ℓ+1}(η) > 0`. -/
theorem c33a_recurrenceR_pos (ℓ : ℕ) (η : ℝ) : 0 < recurrenceR (ℓ + 1) η := by
  rw [c33a_recurrenceR_succ]
  apply div_pos (Real.sqrt_pos.mpr (by positivity)) (by positivity)

/-- `U(a,b,z) + b U(a+1,b+1,z) = z U(a+1,b+2,z)` (from 13.3.9 and 13.3.14). -/
lemma q2a_kummerU_rel1 (a b z : ℂ) (hz : z ≠ 0) :
    kummerU a b z + b * kummerU (a + 1) (b + 1) z - z * kummerU (a + 1) (b + 2) z = 0 := by
  have h1 := kummerU_contiguous_a_b (a + 1) (b + 2) z hz
  have h2 := kummerU_ode_contiguous a b z hz
  rw [show a + 1 + 1 = a + 2 by ring, show b + 2 - 1 = b + 1 by ring] at h1
  linear_combination -(h2 + z * h1)

/-- A contiguous relation between `U(a,b)`, `U(a+1,b+2)`, `U(a+2,b+3)`. -/
lemma q2a_kummerU_rel2 (a b z : ℂ) (hz : z ≠ 0) :
    b * (b + 1) * kummerU (a + 1) (b + 2) z - z * (b - a) * kummerU (a + 1) (b + 2) z -
      b * (a + 1) * z * kummerU (a + 2) (b + 3) z + (b - a) * kummerU a b z = 0 := by
  have h1 := kummerU_contiguous_a_b (a + 1) (b + 2) z hz
  have h3 := kummerU_contiguous_shift_a (a + 2) (b + 2) z hz
  have r1 := q2a_kummerU_rel1 a b z hz
  rw [show a + 1 + 1 = a + 2 by ring, show b + 2 - 1 = b + 1 by ring] at h1
  rw [show b + 2 - (a + 2) = b - a by ring, show a + 2 - 1 = a + 1 by ring,
    show b + 2 + 1 = b + 3 by ring] at h3
  linear_combination b * (a + 1) * h3 + b * (b - a) * h1 + (b - a) * r1

/-- `|ℓ+1+iη| = ((ℓ+1)² + η²)^{1/2}`. -/
lemma q2a_norm_a (ℓ : ℕ) (η : ℝ) :
    ‖(ℓ : ℂ) + 1 + I * η‖ = Real.sqrt (((ℓ : ℝ) + 1) ^ 2 + η ^ 2) := by
  rw [show (ℓ : ℂ) + 1 + I * η = ⟨(ℓ : ℝ) + 1, η⟩ by apply Complex.ext <;> simp,
    Complex.norm_eq_sqrt_sq_add_sq]

/-- `R_{ℓ+1} = |ℓ+1+iη|/(ℓ+1)`. -/
lemma q2a_recurrenceR_cast (ℓ : ℕ) (η : ℝ) :
    (recurrenceR (ℓ + 1) η : ℂ) = ‖(ℓ : ℂ) + 1 + I * η‖ / ((ℓ : ℂ) + 1) := by
  rw [c33a_recurrenceR_succ, q2a_norm_a]; push_cast; ring

/-- `|a| e^{iσ_{ℓ+1}} = a e^{iσ_ℓ}`, `a = ℓ+1+iη`. -/
lemma q2a_exp_sigma_succ (ℓ : ℕ) (η : ℝ) :
    (‖(ℓ : ℂ) + 1 + I * η‖ : ℂ) * exp (coulombSigma (ℓ + 1) η * I) =
      ((ℓ : ℂ) + 1 + I * η) * exp (coulombSigma ℓ η * I) := by
  set a : ℂ := (ℓ : ℂ) + 1 + I * η with ha
  set g := Gamma a with hg
  have hg0 : g ≠ 0 := c33a_Gamma_ne_zero ℓ η
  have hrec : Gamma (((ℓ + 1 : ℕ) : ℂ) + 1 + I * η) = a * g := by
    rw [show ((ℓ + 1 : ℕ) : ℂ) + 1 + I * η = a + 1 by rw [ha]; push_cast; ring,
      Complex.Gamma_add_one]
    intro h
    have := congrArg Complex.re h
    simp [ha] at this
    linarith [(Nat.cast_nonneg ℓ : (0 : ℝ) ≤ ℓ)]
  have h1 := norm_mul_exp_arg_mul_I (Gamma (((ℓ + 1 : ℕ) : ℂ) + 1 + I * η))
  have h0 := norm_mul_exp_arg_mul_I g
  rw [hrec, norm_mul] at h1
  have hn : (‖g‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.mpr hg0).ne'
  apply mul_left_cancel₀ hn
  rw [coulombSigma, coulombSigma, hrec, ← ha, ← hg]
  push_cast at h1
  linear_combination h1 - a * h0

/-- `R_{ℓ+1} A^+_{ℓ+1} = -2a/(ℓ+1) A^+_ℓ`, `a = ℓ+1+iη`. -/
lemma q2a_R_mul_APlus_succ (ℓ : ℕ) (η : ℝ) :
    (recurrenceR (ℓ + 1) η : ℂ) * coulombAPlus (ℓ + 1) η =
      -2 * ((ℓ : ℂ) + 1 + I * η) / ((ℓ : ℂ) + 1) * coulombAPlus ℓ η := by
  have h := q2a_exp_sigma_succ ℓ η
  rw [q2a_recurrenceR_cast, coulombAPlus, coulombAPlus]
  have hl : (ℓ : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero ℓ
  generalize exp (coulombSigma (ℓ + 1) η * I) = E1 at *
  generalize exp (coulombSigma ℓ η * I) = E0 at *
  generalize ((Real.exp (π * η / 2) : ℝ) : ℂ) = X
  generalize (‖(ℓ : ℂ) + 1 + I * η‖ : ℂ) = n at *
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_div_iff hl hl, pow_succ, pow_succ]
  linear_combination (-(2 : ℂ)) * X * 2 ^ (ℓ + 1) * (-1) ^ ℓ * (-I) * ((ℓ : ℂ) + 1) * h

/-- `R_{ℓ+1} A^+_ℓ = -conj(a)/(2(ℓ+1)) A^+_{ℓ+1}`, `a = ℓ+1+iη`. -/
lemma q2a_R_mul_APlus (ℓ : ℕ) (η : ℝ) :
    (recurrenceR (ℓ + 1) η : ℂ) * coulombAPlus ℓ η =
      -((ℓ : ℂ) + 1 - I * η) / (2 * ((ℓ : ℂ) + 1)) * coulombAPlus (ℓ + 1) η := by
  have h := q2a_exp_sigma_succ ℓ η
  have hsq : (‖(ℓ : ℂ) + 1 + I * η‖ : ℂ) ^ 2 = ((ℓ : ℂ) + 1 + I * η) * ((ℓ : ℂ) + 1 - I * η) := by
    rw [← Complex.ofReal_pow, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp; ring_nf; rw [I_sq]; ring
  have h2 : (‖(ℓ : ℂ) + 1 + I * η‖ : ℂ) * exp (coulombSigma ℓ η * I) =
      ((ℓ : ℂ) + 1 - I * η) * exp (coulombSigma (ℓ + 1) η * I) := by
    have hn : (‖(ℓ : ℂ) + 1 + I * η‖ : ℂ) ≠ 0 := by
      have := c33a_Gamma_ne_zero ℓ η
      rw [q2a_norm_a]
      exact_mod_cast (Real.sqrt_pos.mpr (by positivity)).ne'
    apply mul_left_cancel₀ hn
    linear_combination exp (coulombSigma ℓ η * I) * hsq - ((ℓ : ℂ) + 1 - I * η) * h
  rw [q2a_recurrenceR_cast, coulombAPlus, coulombAPlus]
  have hl : (ℓ : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero ℓ
  have hl2 : 2 * ((ℓ : ℂ) + 1) ≠ 0 := mul_ne_zero two_ne_zero hl
  clear h hsq
  generalize exp (coulombSigma (ℓ + 1) η * I) = E1 at *
  generalize exp (coulombSigma ℓ η * I) = E0 at *
  generalize ((Real.exp (π * η / 2) : ℝ) : ℂ) = X
  generalize (‖(ℓ : ℂ) + 1 + I * η‖ : ℂ) = n at *
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_div_iff hl hl2, pow_succ, pow_succ]
  linear_combination (2 : ℂ) * X * 2 ^ (ℓ + 1) * (-1) ^ ℓ * (-I) * ((ℓ : ℂ) + 1) * h2


/-- The derivative of `H^+_ℓ` in terms of Tricomi functions. -/
lemma q2a_hasDerivAt_HPlus (ℓ : ℕ) (η : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    HasDerivAt (fun x : ℝ => coulombHPlus ℓ η x)
      (coulombAPlus ℓ η * exp (I * ρ) * ((ρ : ℂ) ^ ℓ * ((ℓ : ℂ) + 1 + I * ρ) *
          kummerU ((ℓ : ℂ) + 1 + I * η) (2 * ℓ + 2) (-2 * I * ρ) +
        2 * I * ((ℓ : ℂ) + 1 + I * η) * (ρ : ℂ) ^ (ℓ + 1) *
          kummerU ((ℓ : ℂ) + 1 + I * η + 1) (2 * ℓ + 2 + 1) (-2 * I * ρ))) ρ := by
  have hs := neg_two_I_mul_mem_slitPlane hρ
  have hU := hasDerivAt_kummerU ((ℓ : ℂ) + 1 + I * η) (2 * ℓ + 2) hs
  have hlin : HasDerivAt (fun w : ℂ => -2 * I * w) (-2 * I) (ρ : ℂ) := by
    simpa using (hasDerivAt_id (ρ : ℂ)).const_mul (-2 * I)
  have he : HasDerivAt (fun w : ℂ => exp (I * w)) (I * exp (I * ρ)) (ρ : ℂ) := by
    have := ((hasDerivAt_id (ρ : ℂ)).const_mul I).cexp
    exact this.congr_deriv (by simp only [mul_one, id]; ring)
  have h1 := ((((hasDerivAt_pow (ℓ + 1) (ρ : ℂ)).const_mul (coulombAPlus ℓ η)).mul he).mul
    (hU.comp (ρ : ℂ) hlin)).comp_ofReal
  refine (h1.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards [eventually_gt_nhds hρ] with x hx
    rw [coulombHPlus_eq ℓ η hx]
    simp only [Pi.mul_apply, Function.comp_apply]
  · simp only [Pi.mul_apply, Function.comp_apply, Nat.add_sub_cancel]
    push_cast
    ring

/-- **DLMF 33.4.4 for `H^+`**: `(H^+_ℓ)' = S_{ℓ+1} H^+_ℓ - R_{ℓ+1} H^+_{ℓ+1}`, `ρ > 0`. -/
@[dlmf 33.4.E4]
theorem deriv_coulombHPlus_upper (ℓ : ℕ) (η : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    deriv (fun x : ℝ => coulombHPlus ℓ η x) ρ =
      recurrenceS (ℓ + 1) η ρ * coulombHPlus ℓ η ρ -
        recurrenceR (ℓ + 1) η * coulombHPlus (ℓ + 1) η ρ := by
  have hz : (-2 * I * ρ : ℂ) ≠ 0 := slitPlane_ne_zero (neg_two_I_mul_mem_slitPlane hρ)
  have hr := q2a_kummerU_rel1 ((ℓ : ℂ) + 1 + I * η) (2 * ℓ + 2) (-2 * I * ρ) hz
  have hA := q2a_R_mul_APlus_succ ℓ η
  rw [(q2a_hasDerivAt_HPlus ℓ η hρ).deriv, coulombHPlus_eq ℓ η hρ, coulombHPlus_eq (ℓ + 1) η hρ,
    show ((ℓ + 1 : ℕ) : ℂ) + 1 + I * η = (ℓ : ℂ) + 1 + I * η + 1 by push_cast; ring,
    show 2 * ((ℓ + 1 : ℕ) : ℂ) + 2 = 2 * ℓ + 2 + 2 by push_cast; ring, recurrenceS]
  have hρ0 : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  have hl : (ℓ : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero ℓ
  generalize kummerU ((ℓ : ℂ) + 1 + I * η) (2 * ℓ + 2) (-2 * I * ρ) = U0 at *
  generalize kummerU ((ℓ : ℂ) + 1 + I * η + 1) (2 * ℓ + 2 + 1) (-2 * I * ρ) = U1 at *
  generalize kummerU ((ℓ : ℂ) + 1 + I * η + 1) (2 * ℓ + 2 + 2) (-2 * I * ρ) = V at *
  generalize exp (I * ρ) = E at *
  generalize coulombAPlus ℓ η = A0 at *
  generalize coulombAPlus (ℓ + 1) η = A1 at *
  generalize ((recurrenceR (ℓ + 1) η : ℝ) : ℂ) = R at *
  push_cast
  rw [show R * (A1 * (ρ : ℂ) ^ (ℓ + 1 + 1) * E * V) = (R * A1) * (ρ : ℂ) ^ (ℓ + 1 + 1) * E * V by
    ring, hA]
  rw [← sub_eq_zero]
  calc _ = A0 * E * (ρ : ℂ) ^ (ℓ + 1) * (I * ((ℓ : ℂ) + 1 + I * η) / ((ℓ : ℂ) + 1)) *
        (U0 + (2 * ℓ + 2) * U1 - -2 * I * ρ * V) := by
          field_simp
          ring_nf
          simp only [I_sq, I_pow_three]
          ring
    _ = 0 := by rw [hr, mul_zero]


/-- **DLMF 33.4.3 for `H^+`**: `(H^+_{ℓ+1})' = R_{ℓ+1} H^+_ℓ - S_{ℓ+1} H^+_{ℓ+1}`, `ρ > 0`. -/
@[dlmf 33.4.E3]
theorem deriv_coulombHPlus_lower (ℓ : ℕ) (η : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    deriv (fun x : ℝ => coulombHPlus (ℓ + 1) η x) ρ =
      recurrenceR (ℓ + 1) η * coulombHPlus ℓ η ρ -
        recurrenceS (ℓ + 1) η ρ * coulombHPlus (ℓ + 1) η ρ := by
  have hz : (-2 * I * ρ : ℂ) ≠ 0 := slitPlane_ne_zero (neg_two_I_mul_mem_slitPlane hρ)
  have hr := q2a_kummerU_rel2 ((ℓ : ℂ) + 1 + I * η) (2 * ℓ + 2) (-2 * I * ρ) hz
  have hA := q2a_R_mul_APlus ℓ η
  rw [(q2a_hasDerivAt_HPlus (ℓ + 1) η hρ).deriv, coulombHPlus_eq ℓ η hρ,
    coulombHPlus_eq (ℓ + 1) η hρ,
    show ((ℓ + 1 : ℕ) : ℂ) + 1 + I * η + 1 = (ℓ : ℂ) + 1 + I * η + 2 by push_cast; ring,
    show 2 * ((ℓ + 1 : ℕ) : ℂ) + 2 + 1 = 2 * ℓ + 2 + 3 by push_cast; ring,
    show ((ℓ + 1 : ℕ) : ℂ) + 1 + I * η = (ℓ : ℂ) + 1 + I * η + 1 by push_cast; ring,
    show 2 * ((ℓ + 1 : ℕ) : ℂ) + 2 = 2 * ℓ + 2 + 2 by push_cast; ring, recurrenceS]
  have hρ0 : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  have hl : (ℓ : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero ℓ
  generalize kummerU ((ℓ : ℂ) + 1 + I * η) (2 * ℓ + 2) (-2 * I * ρ) = U0 at *
  generalize kummerU ((ℓ : ℂ) + 1 + I * η + 2) (2 * ℓ + 2 + 3) (-2 * I * ρ) = W at *
  generalize kummerU ((ℓ : ℂ) + 1 + I * η + 1) (2 * ℓ + 2 + 2) (-2 * I * ρ) = V at *
  generalize exp (I * ρ) = E at *
  generalize coulombAPlus ℓ η = A0 at *
  generalize coulombAPlus (ℓ + 1) η = A1 at *
  generalize ((recurrenceR (ℓ + 1) η : ℝ) : ℂ) = R at *
  push_cast
  rw [show R * (A0 * (ρ : ℂ) ^ (ℓ + 1) * E * U0) = (R * A0) * (ρ : ℂ) ^ (ℓ + 1) * E * U0 by
    ring, hA]
  rw [← sub_eq_zero]
  calc _ = A1 * E * (ρ : ℂ) ^ (ℓ + 1) / (2 * ℓ + 2) *
        ((2 * ℓ + 2) * (2 * ℓ + 2 + 1) * V - -2 * I * ρ * (2 * ℓ + 2 - ((ℓ : ℂ) + 1 + I * η)) * V -
          (2 * ℓ + 2) * ((ℓ : ℂ) + 1 + I * η + 1) * (-2 * I * ρ) * W +
          (2 * ℓ + 2 - ((ℓ : ℂ) + 1 + I * η)) * U0) := by
          field_simp
          ring_nf
          simp only [I_sq]
          ring
    _ = 0 := by rw [hr, mul_zero]


/-- Real and imaginary parts of a complex linear relation. -/
lemma q2a_re_im_of_eq {g f s r G1 F1 G2 F2 : ℝ}
    (h : (g : ℂ) + I * f = (s : ℂ) * (G1 + I * F1) - (r : ℂ) * (G2 + I * F2)) :
    g = s * G1 - r * G2 ∧ f = s * F1 - r * F2 := by
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp at h1 h2
  exact ⟨by linarith, by linarith⟩

/-- DLMF 33.4.4 for `G_ℓ` and `F_ℓ`. -/
lemma q2a_upper_FG (ℓ : ℕ) (η : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    deriv (coulombG ℓ η) ρ =
      recurrenceS (ℓ + 1) η ρ * coulombG ℓ η ρ - recurrenceR (ℓ + 1) η * coulombG (ℓ + 1) η ρ ∧
    deriv (coulombF ℓ η) ρ =
      recurrenceS (ℓ + 1) η ρ * coulombF ℓ η ρ - recurrenceR (ℓ + 1) η * coulombF (ℓ + 1) η ρ := by
  obtain ⟨g', f', hG, hF, hH, -⟩ := coulomb_wronskian_real_aux ℓ η hρ
  have h := deriv_coulombHPlus_upper ℓ η hρ
  rw [hH.deriv, (coulombH_eq_G_add_I_mul_F ℓ η hρ).1,
    (coulombH_eq_G_add_I_mul_F (ℓ + 1) η hρ).1] at h
  rw [hG.deriv, hF.deriv]
  exact q2a_re_im_of_eq h

/-- DLMF 33.4.3 for `G_{ℓ+1}` and `F_{ℓ+1}`. -/
lemma q2a_lower_FG (ℓ : ℕ) (η : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    deriv (coulombG (ℓ + 1) η) ρ =
      recurrenceR (ℓ + 1) η * coulombG ℓ η ρ - recurrenceS (ℓ + 1) η ρ * coulombG (ℓ + 1) η ρ ∧
    deriv (coulombF (ℓ + 1) η) ρ =
      recurrenceR (ℓ + 1) η * coulombF ℓ η ρ - recurrenceS (ℓ + 1) η ρ * coulombF (ℓ + 1) η ρ := by
  obtain ⟨g', f', hG, hF, hH, -⟩ := coulomb_wronskian_real_aux (ℓ + 1) η hρ
  have h := deriv_coulombHPlus_lower ℓ η hρ
  rw [hH.deriv, (coulombH_eq_G_add_I_mul_F ℓ η hρ).1,
    (coulombH_eq_G_add_I_mul_F (ℓ + 1) η hρ).1] at h
  rw [hG.deriv, hF.deriv]
  exact q2a_re_im_of_eq h

/-- **Derivative of `F_ℓ` in terms of `F_{ℓ-1}`** (DLMF 33.4.3, `X = F`), stated for `ℓ + 1`:
`F_{ℓ+1}' = R_{ℓ+1} F_ℓ - S_{ℓ+1} F_{ℓ+1}`, `ρ > 0`. -/
@[dlmf 33.4.E3]
theorem deriv_coulombF_lower (ℓ : ℕ) (η : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    deriv (coulombF (ℓ + 1) η) ρ =
      recurrenceR (ℓ + 1) η * coulombF ℓ η ρ - recurrenceS (ℓ + 1) η ρ * coulombF (ℓ + 1) η ρ :=
  (q2a_lower_FG ℓ η hρ).2

/-- **Derivative of `F_ℓ` in terms of `F_{ℓ+1}`** (DLMF 33.4.4, `X = F`):
`F_ℓ' = S_{ℓ+1} F_ℓ - R_{ℓ+1} F_{ℓ+1}`, `ℓ ≥ 0`, `ρ > 0`. -/
@[dlmf 33.4.E4]
theorem deriv_coulombF_upper (ℓ : ℕ) (η : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    deriv (coulombF ℓ η) ρ =
      recurrenceS (ℓ + 1) η ρ * coulombF ℓ η ρ - recurrenceR (ℓ + 1) η * coulombF (ℓ + 1) η ρ :=
  (q2a_upper_FG ℓ η hρ).2

/-- **Derivative of `G_ℓ` in terms of `G_{ℓ-1}`** (DLMF 33.4.3, `X = G`), stated for `ℓ + 1`. -/
@[dlmf 33.4.E3]
theorem deriv_coulombG_lower (ℓ : ℕ) (η : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    deriv (coulombG (ℓ + 1) η) ρ =
      recurrenceR (ℓ + 1) η * coulombG ℓ η ρ - recurrenceS (ℓ + 1) η ρ * coulombG (ℓ + 1) η ρ :=
  (q2a_lower_FG ℓ η hρ).1

/-- **Derivative of `G_ℓ` in terms of `G_{ℓ+1}`** (DLMF 33.4.4, `X = G`), `ℓ ≥ 0`. -/
@[dlmf 33.4.E4]
theorem deriv_coulombG_upper (ℓ : ℕ) (η : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    deriv (coulombG ℓ η) ρ =
      recurrenceS (ℓ + 1) η ρ * coulombG ℓ η ρ - recurrenceR (ℓ + 1) η * coulombG (ℓ + 1) η ρ :=
  (q2a_upper_FG ℓ η hρ).1

/-- **The Coulomb wave equation for `G_ℓ`** (DLMF 33.2.1), for `ρ > 0`. -/
@[dlmf 33.2.E1]
theorem coulombG_deriv_deriv (ℓ : ℕ) (η : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    deriv (deriv (coulombG ℓ η)) ρ +
      (1 - 2 * η / ρ - ℓ * (ℓ + 1) / ρ ^ 2) * coulombG ℓ η ρ = 0 := by
  have hev : deriv (coulombG ℓ η) =ᶠ[𝓝 ρ] fun x =>
      recurrenceS (ℓ + 1) η x * coulombG ℓ η x - recurrenceR (ℓ + 1) η * coulombG (ℓ + 1) η x := by
    filter_upwards [eventually_gt_nhds hρ] with x hx
    exact (q2a_upper_FG ℓ η hx).1
  obtain ⟨g0, -, hG0, -, -, -⟩ := coulomb_wronskian_real_aux ℓ η hρ
  obtain ⟨g1, -, hG1, -, -, -⟩ := coulomb_wronskian_real_aux (ℓ + 1) η hρ
  have hS : HasDerivAt (fun x => recurrenceS (ℓ + 1) η x)
      (-(((ℓ + 1 : ℕ) : ℝ) / ρ ^ 2)) ρ := by
    unfold recurrenceS
    have := ((hasDerivAt_inv hρ.ne').const_mul (((ℓ + 1 : ℕ) : ℝ))).add_const
      (η / ((ℓ + 1 : ℕ) : ℝ))
    convert this using 1
    · funext x; simp [div_eq_mul_inv]
    · ring
  have hd := (hS.mul hG0).sub (hG1.const_mul (recurrenceR (ℓ + 1) η))
  rw [hev.deriv_eq, show (fun x => recurrenceS (ℓ + 1) η x * coulombG ℓ η x -
      recurrenceR (ℓ + 1) η * coulombG (ℓ + 1) η x) = ((fun x => recurrenceS (ℓ + 1) η x) *
      coulombG ℓ η - fun y => recurrenceR (ℓ + 1) η * coulombG (ℓ + 1) η y) from rfl, hd.deriv]
  have h0 := (q2a_upper_FG ℓ η hρ).1
  have h1 := (q2a_lower_FG ℓ η hρ).1
  rw [hG0.deriv] at h0
  rw [hG1.deriv] at h1
  rw [h0, h1]
  have hR : recurrenceR (ℓ + 1) η ^ 2 = 1 + η ^ 2 / ((ℓ + 1 : ℕ) : ℝ) ^ 2 := by
    rw [recurrenceR, Real.sq_sqrt (by positivity)]
  have hl : ((ℓ + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [recurrenceS]
  field_simp
  have hR' : ((ℓ + 1 : ℕ) : ℝ) ^ 2 * recurrenceR (ℓ + 1) η ^ 2 = ((ℓ + 1 : ℕ) : ℝ) ^ 2 + η ^ 2 := by
    rw [hR]; field_simp
  push_cast at hR' ⊢
  linear_combination (-(ρ ^ 2) * coulombG ℓ η ρ) * hR'

/-- **The three-term recurrence for `F_ℓ`** (DLMF 33.4.2, `X = F`), stated for `ℓ + 1`:
`R_{ℓ+1} F_ℓ - T_{ℓ+1} F_{ℓ+1} + R_{ℓ+2} F_{ℓ+2} = 0`, `ρ > 0`. -/
@[dlmf 33.4.E2]
theorem coulombF_recurrence (ℓ : ℕ) (η : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    recurrenceR (ℓ + 1) η * coulombF ℓ η ρ - recurrenceT (ℓ + 1) η ρ * coulombF (ℓ + 1) η ρ +
      recurrenceR (ℓ + 2) η * coulombF (ℓ + 2) η ρ = 0 := by
  have h1 := deriv_coulombF_lower ℓ η hρ
  have h2 := deriv_coulombF_upper (ℓ + 1) η hρ
  rw [recurrenceT]
  linear_combination h2 - h1

/-- **The three-term recurrence for `G_ℓ`** (DLMF 33.4.2, `X = G`), stated for `ℓ + 1`. -/
@[dlmf 33.4.E2]
theorem coulombG_recurrence (ℓ : ℕ) (η : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    recurrenceR (ℓ + 1) η * coulombG ℓ η ρ - recurrenceT (ℓ + 1) η ρ * coulombG (ℓ + 1) η ρ +
      recurrenceR (ℓ + 2) η * coulombG (ℓ + 2) η ρ = 0 := by
  have h1 := deriv_coulombG_lower ℓ η hρ
  have h2 := deriv_coulombG_upper (ℓ + 1) η hρ
  rw [recurrenceT]
  linear_combination h2 - h1

/-- For `ρ > 0`, `H⁺_ℓ = G_ℓ + i F_ℓ` has derivative `G_ℓ' + i F_ℓ'`. -/
theorem c33a_hasDerivAt_coulombHPlus (ℓ : ℕ) (η : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    HasDerivAt (fun x : ℝ => coulombHPlus ℓ η x)
      (deriv (coulombG ℓ η) ρ + I * deriv (coulombF ℓ η) ρ) ρ := by
  obtain ⟨g', f', hG, hF, hH, -⟩ := coulomb_wronskian_real_aux ℓ η hρ
  rw [hG.deriv, hF.deriv]
  exact hH

/-- For `ρ > 0`, `H⁻_ℓ = G_ℓ - i F_ℓ` has derivative `G_ℓ' - i F_ℓ'`. -/
lemma c33a_hasDerivAt_coulombHMinus (ℓ : ℕ) (η : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    HasDerivAt (fun x : ℝ => coulombHMinus ℓ η x)
      (deriv (coulombG ℓ η) ρ - I * deriv (coulombF ℓ η) ρ) ρ := by
  obtain ⟨g', f', hG, hF, -, -⟩ := coulomb_wronskian_real_aux ℓ η hρ
  rw [hG.deriv, hF.deriv]
  have h := hG.ofReal_comp.sub (hF.ofReal_comp.const_mul I)
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [eventually_gt_nhds hρ] with x hx
  exact (coulombH_eq_G_add_I_mul_F ℓ η hx).2

/-- **DLMF 33.4.3 for `H^-`**: `(H^-_{ℓ+1})' = R_{ℓ+1} H^-_ℓ - S_{ℓ+1} H^-_{ℓ+1}`, `ρ > 0`. -/
@[dlmf 33.4.E3]
theorem deriv_coulombHMinus_lower (ℓ : ℕ) (η : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    deriv (fun x : ℝ => coulombHMinus (ℓ + 1) η x) ρ =
      recurrenceR (ℓ + 1) η * coulombHMinus ℓ η ρ -
        recurrenceS (ℓ + 1) η ρ * coulombHMinus (ℓ + 1) η ρ := by
  rw [(c33a_hasDerivAt_coulombHMinus (ℓ + 1) η hρ).deriv, deriv_coulombG_lower ℓ η hρ,
    deriv_coulombF_lower ℓ η hρ, (coulombH_eq_G_add_I_mul_F ℓ η hρ).2,
    (coulombH_eq_G_add_I_mul_F (ℓ + 1) η hρ).2]
  push_cast; ring

/-- **DLMF 33.4.4 for `H^-`**: `(H^-_ℓ)' = S_{ℓ+1} H^-_ℓ - R_{ℓ+1} H^-_{ℓ+1}`, `ρ > 0`. -/
@[dlmf 33.4.E4]
theorem deriv_coulombHMinus_upper (ℓ : ℕ) (η : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    deriv (fun x : ℝ => coulombHMinus ℓ η x) ρ =
      recurrenceS (ℓ + 1) η ρ * coulombHMinus ℓ η ρ -
        recurrenceR (ℓ + 1) η * coulombHMinus (ℓ + 1) η ρ := by
  rw [(c33a_hasDerivAt_coulombHMinus ℓ η hρ).deriv, deriv_coulombG_upper ℓ η hρ,
    deriv_coulombF_upper ℓ η hρ, (coulombH_eq_G_add_I_mul_F ℓ η hρ).2,
    (coulombH_eq_G_add_I_mul_F (ℓ + 1) η hρ).2]
  push_cast; ring

/-- **The three-term recurrence for `H^+_ℓ`** (DLMF 33.4.2, `X = H^+`). -/
@[dlmf 33.4.E2]
theorem coulombHPlus_recurrence (ℓ : ℕ) (η : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    recurrenceR (ℓ + 1) η * coulombHPlus ℓ η ρ -
      recurrenceT (ℓ + 1) η ρ * coulombHPlus (ℓ + 1) η ρ +
      recurrenceR (ℓ + 2) η * coulombHPlus (ℓ + 2) η ρ = 0 := by
  have hF := coulombF_recurrence ℓ η hρ
  have hG := coulombG_recurrence ℓ η hρ
  rw [(coulombH_eq_G_add_I_mul_F ℓ η hρ).1, (coulombH_eq_G_add_I_mul_F (ℓ + 1) η hρ).1,
    (coulombH_eq_G_add_I_mul_F (ℓ + 2) η hρ).1]
  have hF' := congrArg (fun r : ℝ => (r : ℂ)) hF
  have hG' := congrArg (fun r : ℝ => (r : ℂ)) hG
  push_cast at hF' hG'
  linear_combination hG' + I * hF'

/-- **The three-term recurrence for `H^-_ℓ`** (DLMF 33.4.2, `X = H^-`). -/
@[dlmf 33.4.E2]
theorem coulombHMinus_recurrence (ℓ : ℕ) (η : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    recurrenceR (ℓ + 1) η * coulombHMinus ℓ η ρ -
      recurrenceT (ℓ + 1) η ρ * coulombHMinus (ℓ + 1) η ρ +
      recurrenceR (ℓ + 2) η * coulombHMinus (ℓ + 2) η ρ = 0 := by
  have hF := coulombF_recurrence ℓ η hρ
  have hG := coulombG_recurrence ℓ η hρ
  rw [(coulombH_eq_G_add_I_mul_F ℓ η hρ).2, (coulombH_eq_G_add_I_mul_F (ℓ + 1) η hρ).2,
    (coulombH_eq_G_add_I_mul_F (ℓ + 2) η hρ).2]
  have hF' := congrArg (fun r : ℝ => (r : ℂ)) hF
  have hG' := congrArg (fun r : ℝ => (r : ℂ)) hG
  push_cast at hF' hG'
  linear_combination hG' - I * hF'

/-! ### §33.2(iv) The cross-product -/

/-- **The cross-product** (DLMF 33.2.13), stated for `ℓ + 1`:
`F_ℓ G_{ℓ+1} - F_{ℓ+1} G_ℓ = (ℓ+1)/((ℓ+1)² + η²)^{1/2}`, `ρ > 0`. -/
@[dlmf 33.2.E13]
theorem coulombF_mul_coulombG_sub (ℓ : ℕ) (η : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    coulombF ℓ η ρ * coulombG (ℓ + 1) η ρ - coulombF (ℓ + 1) η ρ * coulombG ℓ η ρ =
      (ℓ + 1) / Real.sqrt (((ℓ : ℝ) + 1) ^ 2 + η ^ 2) := by
  have hW := coulomb_wronskian (ℓ + 1) η hρ
  rw [deriv_coulombF_lower ℓ η hρ, deriv_coulombG_lower ℓ η hρ] at hW
  have hR := c33a_recurrenceR_pos ℓ η
  have hR' : recurrenceR (ℓ + 1) η *
      (coulombF ℓ η ρ * coulombG (ℓ + 1) η ρ - coulombF (ℓ + 1) η ρ * coulombG ℓ η ρ) = 1 := by
    linear_combination hW
  rw [eq_div_iff (Real.sqrt_pos.mpr (by positivity)).ne']
  rw [c33a_recurrenceR_succ] at hR'
  have hl : (0 : ℝ) < (ℓ : ℝ) + 1 := by positivity
  field_simp at hR'
  linear_combination hR'

/-! ### §33.13 Complex variable and parameters -/

/-- **DLMF 33.13.1** for `ℓ ∈ ℕ`, real `η`:
`C_ℓ(η) = 2^ℓ e^{iσ_ℓ(η) - πη/2} Γ(ℓ+1-iη)/Γ(2ℓ+2)`. This is the form of `C_ℓ` that DLMF uses
for the continuation to complex `ℓ`, `η`. -/
@[dlmf 33.13.E1]
theorem coulombC_eq_exp_sigma_mul_Gamma (ℓ : ℕ) (η : ℝ) :
    (coulombC ℓ η : ℂ) = 2 ^ ℓ * exp (I * coulombSigma ℓ η - π * η / 2) *
      Gamma ((ℓ : ℂ) + 1 - I * η) / Gamma (2 * ℓ + 2) := by
  set g := Gamma ((ℓ : ℂ) + 1 + I * η) with hg
  have hconj : Gamma ((ℓ : ℂ) + 1 - I * η) = conj g := by
    rw [hg, ← Complex.Gamma_conj]
    congr 1
    simp [map_add, map_mul, Complex.conj_ofReal]
    ring
  have hfac : Gamma (2 * (ℓ : ℂ) + 2) = ((2 * ℓ + 1)! : ℂ) := by
    rw [show 2 * (ℓ : ℂ) + 2 = ((2 * ℓ + 1 : ℕ) : ℂ) + 1 by push_cast; ring,
      Complex.Gamma_nat_eq_factorial]
  have hpol : exp (I * coulombSigma ℓ η) * conj g = (‖g‖ : ℂ) := by
    have h := norm_mul_exp_arg_mul_I g
    conv_lhs => rw [← h]
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, coulombSigma, ← hg]
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    rw [mul_left_comm, ← Complex.exp_add]
    simp [mul_comm]
  rw [hconj, hfac, coulombC, sub_eq_add_neg, Complex.exp_add]
  have hf : ((2 * ℓ + 1)! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  push_cast
  rw [← hg]
  have : (2 : ℂ) ^ ℓ * (exp (I * coulombSigma ℓ η) * exp (-(π * η / 2))) * conj g =
      2 ^ ℓ * exp (-(π * η / 2)) * (exp (I * coulombSigma ℓ η) * conj g) := by ring
  rw [this, hpol, show -(π : ℂ) * η / 2 = -(π * η / 2) by ring]

/-- **DLMF 33.13.2** for `ℓ ∈ ℕ`, real `η`, stated for `ℓ + 1`:
`R_{ℓ+1} = (2ℓ+3) C_{ℓ+1}(η)/C_ℓ(η)`. -/
@[dlmf 33.13.E2]
theorem recurrenceR_eq_coulombC_div (ℓ : ℕ) (η : ℝ) :
    recurrenceR (ℓ + 1) η = (2 * ((ℓ + 1 : ℕ) : ℝ) + 1) * coulombC (ℓ + 1) η / coulombC ℓ η := by
  have hC := coulombC_pos ℓ η
  have hg := c33a_Gamma_ne_zero ℓ η
  have hrec : Gamma (((ℓ + 1 : ℕ) : ℂ) + 1 + I * η) =
      ((ℓ : ℂ) + 1 + I * η) * Gamma ((ℓ : ℂ) + 1 + I * η) := by
    rw [show ((ℓ + 1 : ℕ) : ℂ) + 1 + I * η = ((ℓ : ℂ) + 1 + I * η) + 1 by push_cast; ring,
      Complex.Gamma_add_one]
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith [(Nat.cast_nonneg ℓ : (0 : ℝ) ≤ ℓ)]
  have hn : ‖(ℓ : ℂ) + 1 + I * η‖ = Real.sqrt (((ℓ : ℝ) + 1) ^ 2 + η ^ 2) := by
    rw [show (ℓ : ℂ) + 1 + I * η = ⟨(ℓ : ℝ) + 1, η⟩ by apply Complex.ext <;> simp,
      Complex.norm_eq_sqrt_sq_add_sq]
  rw [c33a_recurrenceR_succ, eq_div_iff hC.ne', coulombC, coulombC, hrec, norm_mul, hn]
  have hl : (0 : ℝ) < (ℓ : ℝ) + 1 := by positivity
  rw [show 2 * ((ℓ + 1 : ℕ) : ℝ) + 1 = ((2 * (ℓ + 1) + 1 : ℕ) : ℝ) by push_cast; ring,
    show 2 * (ℓ + 1) + 1 = (2 * ℓ + 2) + 1 by ring, Nat.factorial_succ (2 * ℓ + 2),
    Nat.factorial_succ (2 * ℓ + 1)]
  have hf : ((2 * ℓ + 1)! : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  push_cast
  field_simp
  ring

/-- For `ℓ ∈ ℕ` the complex-parameter function `coulombWaveComplex` is `coulombWave`
(DLMF §33.13). -/
theorem coulombWaveComplex_natCast (ℓ : ℕ) (η ρ : ℂ) :
    coulombWaveComplex ℓ η ρ = coulombWave ℓ η ρ := by
  rw [coulombWaveComplex, coulombWave,
    show (ℓ : ℂ) + 1 = ((ℓ + 1 : ℕ) : ℂ) by push_cast; ring, cpow_natCast]

/-- The first derivative of `coulombWaveComplex` on the slit plane. -/
lemma q2a_hasDerivAt_wc (ℓ η : ℂ) (hb0 : ∀ k : ℕ, 2 * ℓ + 2 ≠ -k) {z : ℂ}
    (hz : z ∈ slitPlane) :
    HasDerivAt (coulombWaveComplex ℓ η)
      ((ℓ + 1) * z ^ (ℓ + 1 - 1) * exp (-I * z) * kummerM (ℓ + 1 - I * η) (2 * ℓ + 2) (2 * I * z)
        - I * z ^ (ℓ + 1) * exp (-I * z) * kummerM (ℓ + 1 - I * η) (2 * ℓ + 2) (2 * I * z)
        + 2 * I * ((ℓ + 1 - I * η) / (2 * ℓ + 2)) * z ^ (ℓ + 1) * exp (-I * z) *
          kummerM (ℓ + 1 - I * η + 1) (2 * ℓ + 2 + 1) (2 * I * z)) z := by
  have hE : HasDerivAt (fun z : ℂ => exp (-I * z)) (-I * exp (-I * z)) z := by
    have := ((hasDerivAt_id z).const_mul (-I)).cexp
    exact this.congr_deriv (by simp only [mul_one, id]; ring)
  have hP : HasDerivAt (fun z : ℂ => z ^ (ℓ + 1)) ((ℓ + 1) * z ^ (ℓ + 1 - 1)) z :=
    (hasDerivAt_id z).cpow_const hz |>.congr_deriv (by simp)
  have h := (hP.mul hE).mul
    (hasDerivAt_kummerM_two_I_mul (α := ℓ + 1 - I * η) hb0 z)
  refine h.congr_deriv ?_
  simp only [Pi.mul_apply]
  ring

/-- **Continuation to complex `ℓ`, `η`, `ρ`** (DLMF §33.13): for complex `ℓ` with
`2ℓ + 2 ∉ {0, -1, -2, …}` and complex `η`, the function
`ρ^{ℓ+1} e^{-iρ} M(ℓ+1-iη, 2ℓ+2, 2iρ)` (principal power) solves the Coulomb wave equation
33.2.1 on the slit plane `ℂ \ (-∞, 0]`; it is the analytic continuation of the regular solution
to noninteger `ℓ` and complex `ρ`, `η`. -/
@[dlmf 33.13]
theorem coulombWaveComplex_ode (ℓ η : ℂ) (hℓ : ∀ k : ℕ, 2 * ℓ + 2 ≠ -k) {ρ : ℂ}
    (hρ : ρ ∈ slitPlane) :
    deriv (deriv (coulombWaveComplex ℓ η)) ρ +
      (1 - 2 * η / ρ - ℓ * (ℓ + 1) / ρ ^ 2) * coulombWaveComplex ℓ η ρ = 0 := by
  set a : ℂ := ℓ + 1 - I * η with ha
  set b : ℂ := 2 * ℓ + 2 with hb
  have hb1 : ∀ k : ℕ, b + 1 ≠ -k := by simpa using DLMF.Hypergeometric.not_neg_nat_add_nat hℓ 1
  have hev : deriv (coulombWaveComplex ℓ η) =ᶠ[𝓝 ρ] fun z =>
      (ℓ + 1) * z ^ (ℓ + 1 - 1) * exp (-I * z) * kummerM a b (2 * I * z)
        - I * z ^ (ℓ + 1) * exp (-I * z) * kummerM a b (2 * I * z)
        + 2 * I * (a / b) * z ^ (ℓ + 1) * exp (-I * z) * kummerM (a + 1) (b + 1) (2 * I * z) := by
    filter_upwards [isOpen_slitPlane.mem_nhds hρ] with z hz
    exact (q2a_hasDerivAt_wc ℓ η hℓ hz).deriv
  rw [hev.deriv_eq]
  have hz0 : ρ ≠ 0 := slitPlane_ne_zero hρ
  have hE : HasDerivAt (fun z : ℂ => exp (-I * z)) (-I * exp (-I * ρ)) ρ := by
    have := ((hasDerivAt_id ρ).const_mul (-I)).cexp
    exact this.congr_deriv (by simp only [mul_one, id]; ring)
  have hP : HasDerivAt (fun z : ℂ => z ^ (ℓ + 1)) ((ℓ + 1) * ρ ^ (ℓ + 1 - 1)) ρ :=
    (hasDerivAt_id ρ).cpow_const hρ |>.congr_deriv (by simp)
  have hP1 : HasDerivAt (fun z : ℂ => z ^ (ℓ + 1 - 1)) ((ℓ + 1 - 1) * ρ ^ (ℓ + 1 - 1 - 1)) ρ :=
    (hasDerivAt_id ρ).cpow_const hρ |>.congr_deriv (by simp)
  have h0 := hasDerivAt_kummerM_two_I_mul (α := a) hℓ ρ
  have h1 := hasDerivAt_kummerM_two_I_mul (α := a + 1) hb1 ρ
  have h := ((((hP1.const_mul (ℓ + 1)).mul hE).mul h0).sub
    (((hP.const_mul I).mul hE).mul h0)).add (((hP.const_mul (2 * I * (a / b))).mul hE).mul h1)
  have h' : HasDerivAt (fun z : ℂ =>
      (ℓ + 1) * z ^ (ℓ + 1 - 1) * exp (-I * z) * kummerM a b (2 * I * z)
        - I * z ^ (ℓ + 1) * exp (-I * z) * kummerM a b (2 * I * z)
        + 2 * I * (a / b) * z ^ (ℓ + 1) * exp (-I * z) * kummerM (a + 1) (b + 1) (2 * I * z))
      _ ρ := h
  rw [h'.deriv]
  have hc := kummerM_ode_contiguous (a := a) (b := b) hℓ (z := 2 * I * ρ)
  have hbne : b ≠ 0 := by simpa using hℓ 0
  have hb1ne : b + 1 ≠ 0 := by simpa using hb1 0
  unfold coulombWaveComplex
  simp only [Pi.mul_apply]
  rw [ show a + 1 + 1 = a + 2 by ring, show b + 1 + 1 = b + 2 by ring]
  simp only [cpow_sub _ _ hz0, cpow_one]
  generalize kummerM a b (2 * I * ρ) = M0 at hc ⊢
  generalize kummerM (a + 1) (b + 1) (2 * I * ρ) = M1 at hc ⊢
  generalize kummerM (a + 2) (b + 2) (2 * I * ρ) = M2 at hc ⊢
  generalize exp (-I * ρ) = E
  generalize ρ ^ (ℓ + 1) = P
  linear_combination (norm := skip) (P / ρ * 2 * I * E * a / (b * (b + 1))) * hc
  rw [ha, hb] at *
  have hl1 : (ℓ : ℂ) + 1 ≠ 0 := fun h => hbne (by linear_combination 2 * h)
  have hl3 : ((ℓ : ℂ) + 1) * 2 + 1 ≠ 0 := fun h => hb1ne (by linear_combination h)
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  ring_nf

end DLMF.Coulomb
