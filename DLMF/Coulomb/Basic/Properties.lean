/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Coulomb.Basic.Functions

/-!
# Coulomb functions: basic properties (DLMF §33.2)

## Main results

* `coulomb_indicial`: the indices `ℓ + 1`, `-ℓ` at the regular singularity `ρ = 0`
  (DLMF §33.2(i)).
* `turningPoint_isRoot`, `coulomb_coeff_turningPoint`: the outer turning point (DLMF 33.2.2).
* `coulombC_pos`: `C_ℓ(η) > 0` (DLMF §33.2(ii)).
* `norm_Gamma_one_add_I_mul_sq`, `norm_Gamma_nat_add_one_add_I_mul_sq`: `|Γ(ℓ+1+iη)|²` as a
  product.
* `coulombC_sq_eq_prod`, `coulombC_eq_sqrt_prod`: the alternative form DLMF 33.2.6.

## Implementation notes

The Coulomb wave equation, the Whittaker forms and the Wronskians of §33.2 use Kummer's and
Whittaker's functions; they are in `DLMF.Coulomb.RhoEtaProperties`, `DLMF.Confluent.Coulomb`
and `DLMF.Confluent.CoulombIrregular`.
-/

@[expose] public section

open Complex
open scoped Real Nat ComplexConjugate

noncomputable section

namespace DLMF.Coulomb

open DLMF.Confluent

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

/-- `Γ(ℓ + 1 + iη) ≠ 0`. -/
theorem Gamma_nat_add_one_add_I_mul_ne_zero (ℓ : ℕ) (η : ℝ) : Gamma ((ℓ : ℂ) + 1 + I * η) ≠ 0 := by
  refine Complex.Gamma_ne_zero fun m hm => ?_
  have := congrArg Complex.re hm
  simp at this
  linarith [(Nat.cast_nonneg ℓ : (0 : ℝ) ≤ ℓ), (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

/-- **`C_ℓ(η)` is positive** (DLMF §33.2(ii)). -/
@[dlmf 33.2.ii]
theorem coulombC_pos (ℓ : ℕ) (η : ℝ) : 0 < coulombC ℓ η := by
  rw [coulombC]
  have := norm_pos_iff.mpr (Gamma_nat_add_one_add_I_mul_ne_zero ℓ η)
  positivity

/-- For `η ≠ 0`, `|Γ(1 + iη)|² = πη / sinh(πη)`. -/
theorem norm_Gamma_one_add_I_mul_sq (η : ℝ) (hη : η ≠ 0) :
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
theorem norm_Gamma_nat_add_one_add_I_mul_sq (ℓ : ℕ) (η : ℝ) :
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
  rw [coulombC, div_pow, mul_pow, mul_pow, ← pow_mul, mul_comm ℓ 2,
      norm_Gamma_nat_add_one_add_I_mul_sq,
    norm_Gamma_one_add_I_mul_sq η hη, ← Real.exp_nat_mul]
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

end DLMF.Coulomb
