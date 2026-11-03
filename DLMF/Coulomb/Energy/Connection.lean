/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Coulomb.Energy.Properties
public import DLMF.Coulomb.RhoEtaProperties
public import Carlson.Elliptic.Addition

/-!
# Coulomb functions `f`, `h`, `s`, `c`: connection formulas

This file expresses `F_ℓ`, `G_ℓ` in terms of `f`, `h` (DLMF 33.16.1–33.16.2), and `f`, `h`, `s`,
`c` in terms of `F_ℓ`, `G_ℓ` for `ε > 0` (33.16.3–33.16.7, 33.16.14–33.16.15) and in terms of
Whittaker functions for `ε < 0` (33.16.8–33.16.13, 33.16.16–33.16.18). We write `τ = ε^{1/2}`
(33.16.3) and `ν = (-ε)^{-1/2}` (33.16.8) inline.

## Main results

* `coulombF_eq_coulombf`, `coulombG_eq_coulombh`: DLMF 33.16.1 and 33.16.2.
* `coulombf_eq_coulombF_pos`, `coulombf_eq_coulombF_pos'`, `coulombh_eq_coulombG_pos`: `ε > 0`,
  `r > 0` (DLMF 33.16.4, 33.16.5).
* `coulombf_eq_coulombF_neg`, `coulombf_eq_coulombF_neg'`, `coulombh_eq_coulombG_neg`: `ε > 0`,
  `r < 0` (DLMF 33.16.6, 33.16.7).
* `coulombs_coulombc_eq_pos`: DLMF 33.16.14.
* `coulombs_coulombc_eq_neg`: DLMF 33.16.15, corrected.
* `coulombf_eq_whittaker_pos`, `coulombh_eq_whittaker_pos`: `ε < 0`, `r > 0`
  (DLMF 33.16.10, 33.16.11).
* `coulombf_eq_whittaker_neg`, `coulombh_eq_whittaker_neg`: `ε < 0`, `r < 0`
  (DLMF 33.16.12, 33.16.13).
* `coulombs_coulombc_eq_whittaker_pos`, `coulombs_coulombc_eq_whittaker_neg`: DLMF 33.16.17 and
  33.16.18, corrected.

## Implementation notes

DLMF 33.16.1–33.16.2, 33.16.4–33.16.7 and 33.16.10–33.16.13 hold as printed. Three formulas are
DLMF errata, checked numerically with mpmath to 30–40 digits; the corrected forms are proved.

* 33.16.15 (`r < 0`, `ε > 0`) is inconsistent with 33.16.6–33.16.7 and the definitions
  33.14.9–33.14.10 of `s`, `c`: with `B = A/(1 - e^{-2π/τ})` these give
  `s = (-1)^{ℓ+1} e^{π/τ} (πτ)^{-1/2} F_ℓ(1/τ,-τr)` and
  `c = (-1)^ℓ e^{-π/τ} (πτ)^{-1/2} G_ℓ(1/τ,-τr)`; DLMF prints them without the factors
  `(-1)^{ℓ+1} e^{π/τ}` and `(-1)^ℓ e^{-π/τ}`.
* 33.16.17: the prefactor `(-1)^ℓ/(2ν^{1/2})` must be `(-1)^ℓ/(2ν)^{1/2}` (DLMF's `s`, `c` are
  too small by the factor `2^{1/2}`), as follows from 33.16.10–33.16.11 with 33.14.9 and
  33.14.12.
* 33.16.18: `K(ν,ℓ)` and `1/K(ν,ℓ)` are interchanged: from 33.16.12–33.16.13,
  `s = (-1)^{ℓ+1} 2^{-1/2} (ν^{3/2} K ξ_ℓ(-ν,r) - sin(πν) cos(πν) (πν^{1/2}K)^{-1} ζ_ℓ(-ν,r))` and
  `c = (-1)^ℓ (π(2ν)^{1/2} K)^{-1} ζ_ℓ(-ν,r)`.
-/

@[expose] public section

open Complex Filter Set
open scoped Real Nat Topology ComplexConjugate

noncomputable section

namespace DLMF.Coulomb

open DLMF.Confluent

/-! ### `F_ℓ` and `G_ℓ` in terms of `f` and `h` -/

/-- For `η ≠ 0`, `κ(1/η², r) = i|η|`. -/
private lemma coulombKappa_one_div_sq {η : ℝ} (hη : η ≠ 0) (r : ℝ) :
    coulombKappa (1 / η ^ 2) r = I * |η| := by
  have hpos : 0 < 1 / η ^ 2 := by positivity
  simp only [coulombKappa, not_lt.mpr hpos.le, ↓reduceIte]
  congr 2
  rw [Real.rpow_neg hpos.le, ← Real.sqrt_eq_rpow, one_div, Real.sqrt_inv, inv_inv,
    Real.sqrt_sq_eq_abs]

/-- At `κ = iη`, the Kummer form of `f(ε,ℓ;r)` at `r = -ηρ` is `(-2η)^{ℓ+1}/(2ℓ+1)!` times the
Kummer form of the Coulomb wave. -/
private lemma coulombfKummer_I_mul (η ρ : ℝ) (hη : η ≠ 0) (ℓ : ℕ) :
    coulombfKummer (I * η) ℓ (-η * ρ) = (-2 * η) ^ (ℓ + 1) * coulombWave ℓ η ρ / (2 * ℓ + 1)! := by
  unfold coulombfKummer coulombWave
  have hη' : (η : ℂ) ≠ 0 := by exact_mod_cast hη
  have h1 : -(((-η * ρ : ℝ)) : ℂ) / (I * η) = -I * ρ := by
    push_cast; field_simp; ring_nf; rw [I_sq]; ring
  have h2 : 2 * (((-η * ρ : ℝ)) : ℂ) / (I * η) = 2 * I * ρ := by
    push_cast; field_simp; ring_nf; rw [I_sq]; ring
  rw [h1, h2]
  push_cast
  ring

/-- **DLMF 33.16.1**: `F_ℓ(η,ρ) = (2ℓ+1)! C_ℓ(η) (-2η)^{-ℓ-1} f(1/η², ℓ; -ηρ)` for `η ≠ 0`
(and all real `ρ`). -/
@[dlmf 33.16.E1]
theorem coulombF_eq_coulombf (ℓ : ℕ) {η : ℝ} (hη : η ≠ 0) (ρ : ℝ) :
    coulombF ℓ η ρ =
      (2 * ℓ + 1)! * coulombC ℓ η / (-2 * η) ^ (ℓ + 1) * coulombf (1 / η ^ 2) ℓ (-η * ρ) := by
  apply Complex.ofReal_injective
  have hε : (1 / η ^ 2 : ℝ) ≠ 0 := by positivity
  push_cast
  rw [ofReal_coulombF, ofReal_coulombf hε, coulombKappa_one_div_sq hη]
  have hK : coulombfKummer (I * (|η| : ℝ)) ℓ (-η * ρ) = coulombfKummer (I * η) ℓ (-η * ρ) := by
    rcases abs_choice η with h | h <;> rw [h]
    push_cast
    rw [mul_neg, coulombfKummer_neg]
  rw [hK, coulombfKummer_I_mul η ρ hη ℓ]
  have h2 : (-(2 * (η : ℂ))) ^ (ℓ + 1) ≠ 0 :=
    pow_ne_zero _ (neg_ne_zero.mpr (mul_ne_zero two_ne_zero (by exact_mod_cast hη)))
  have hf : (((2 * ℓ + 1)! : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  field_simp

/-- Away from `ε = 0` and when `κ` is not real, `h(ε,ℓ;r)` is the real part of 33.14.7. -/
theorem coulombh_eq_re_coulombhFormula_of_im_ne {ε : ℝ} (hε : ε ≠ 0) (ℓ : ℕ) (r : ℝ)
    (him : (coulombKappa ε r).im ≠ 0) :
    coulombh ε ℓ r = (coulombhFormula ε ℓ r).re := by
  unfold coulombh
  split_ifs with h
  · exfalso
    rcases h with h | ⟨m, hm⟩
    · exact hε h
    · have := congrArg Complex.im hm
      simp at this
      exact him (by linarith)
  · rfl


/-- For `η < 0`, `ρ > 0`, the real part of the bracketed form 33.14.7 at `κ = -iη`,
`r = -ηρ` is a real multiple of `G_ℓ(η,ρ)`. -/
private lemma re_coulombhKappa_of_neg (ℓ : ℕ) {η : ℝ} (hη : η < 0) {ρ : ℝ} (hρ : 0 < ρ) (S : ℝ) :
    (coulombhKappa (I * (-η : ℝ)) S ℓ (-η * ρ)).re =
      (-1) ^ ℓ * ‖Gamma (ℓ + 1 + I * η)‖ * Real.exp (-π * η / 2) / (π * η ^ ℓ) *
        coulombG ℓ η ρ := by
  rw [coulombhKappa_I_mul_neg_eq ℓ hη.ne hρ, sub_re, re_ofReal_mul, I_mul_re, ofReal_im,
    neg_zero, sub_zero, coulombG]

/-- For `η > 0`, `ρ > 0`, the real part of the bracketed form 33.14.7 at `κ = iη`,
`r = -ηρ` is a real multiple of `G_ℓ(η,ρ)`. -/
private lemma re_coulombhKappa_of_pos (ℓ : ℕ) {η : ℝ} (hη : 0 < η) {ρ : ℝ} (hρ : 0 < ρ) (S : ℝ) :
    (coulombhKappa (I * (η : ℝ)) S ℓ (-η * ρ)).re =
      (-1) ^ ℓ * ‖Gamma (ℓ + 1 + I * η)‖ * Real.exp (-π * η / 2) / (π * η ^ ℓ) *
        coulombG ℓ η ρ := by
  rw [coulombhKappa_I_mul_eq ℓ hη.ne' hρ, add_re, re_ofReal_mul, I_mul_re, ofReal_im,
    neg_zero, add_zero, coulombHMinus_eq_conj ℓ η hρ, conj_re, coulombG]

/-- **DLMF 33.16.2**: `G_ℓ(η,ρ) = π(-2η)^ℓ / ((2ℓ+1)! C_ℓ(η)) h(1/η², ℓ; -ηρ)` for `η ≠ 0`,
`ρ > 0`. -/
@[dlmf 33.16.E2]
theorem coulombG_eq_coulombh (ℓ : ℕ) {η : ℝ} (hη : η ≠ 0) {ρ : ℝ} (hρ : 0 < ρ) :
    coulombG ℓ η ρ =
      π * (-2 * η) ^ ℓ / ((2 * ℓ + 1)! * coulombC ℓ η) * coulombh (1 / η ^ 2) ℓ (-η * ρ) := by
  have hε : (1 / η ^ 2 : ℝ) ≠ 0 := by positivity
  have hκ := coulombKappa_one_div_sq hη (-η * ρ)
  rw [coulombh_eq_re_coulombhFormula_of_im_ne hε ℓ _ (by rw [hκ]; simpa using hη),
    coulombhFormula, hκ]
  have hX : (-1) ^ ℓ * ‖Gamma (ℓ + 1 + I * η)‖ * Real.exp (-π * η / 2) / (π * η ^ ℓ) *
      (π * (-2 * η) ^ ℓ / ((2 * ℓ + 1)! * coulombC ℓ η)) = 1 := by
    have hN : ‖Gamma (ℓ + 1 + I * η)‖ ≠ 0 :=
      norm_ne_zero_iff.mpr (Gamma_nat_add_one_add_I_mul_ne_zero ℓ η)
    have hf : ((2 * ℓ + 1)! : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have hm1 : ((-1 : ℝ) ^ ℓ) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [coulombC, show (-2 * η) ^ ℓ = (-1) ^ ℓ * 2 ^ ℓ * η ^ ℓ by rw [← mul_pow, ← mul_pow]; ring]
    have := Real.exp_pos (-π * η / 2)
    field_simp
    linear_combination hm1
  rcases hη.lt_or_gt with hneg | hpos
  · rw [abs_of_neg hneg, re_coulombhKappa_of_neg ℓ hneg hρ]
    linear_combination (-coulombG ℓ η ρ) * hX
  · rw [abs_of_pos hpos, re_coulombhKappa_of_pos ℓ hpos hρ]
    linear_combination (-coulombG ℓ η ρ) * hX

/-! ### `ε > 0`: `f`, `h`, `s`, `c` in terms of `F_ℓ` and `G_ℓ` (`τ = ε^{1/2}`) -/

/-- For real `x ≥ 0`, `x^{-1/2} = 1/√x` as complex numbers. -/
private lemma ofReal_cpow_neg_half_eq_inv_sqrt {x : ℝ} (hx : 0 ≤ x) :
    ((x : ℝ) : ℂ) ^ (-(1 / 2) : ℂ) = ((Real.sqrt x)⁻¹ : ℝ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hx, Complex.ofReal_cpow hx]; push_cast; ring_nf

/-- For `ε ≥ 0`, the product `A(ε,ℓ) = ∏ (1 + εk²)` is positive. -/
private lemma coulombAProd_pos {ε : ℝ} (hε : 0 ≤ ε) (ℓ : ℕ) : 0 < coulombAProd ε ℓ :=
  Finset.prod_pos fun k _ => by positivity

/-- For `ε > 0`, `1 - e^{-2π/√ε} > 0`. -/
private lemma one_sub_exp_neg_two_pi_div_sqrt_pos {ε : ℝ} (hε : 0 < ε) : 0 < 1 - Real.exp
    (-(2 * π / Real.sqrt ε)) := by
  have : 0 < 2 * π / Real.sqrt ε := by have := Real.sqrt_pos.mpr hε; positivity
  have := Real.exp_lt_one_iff.mpr (neg_neg_of_pos this)
  linarith

/-- For `ε > 0`, `B(ε,ℓ) = A(ε,ℓ)/(1 - e^{-2π/√ε})` (DLMF 33.14.10). -/
private lemma coulombBFactor_eq_of_pos {ε : ℝ} (hε : 0 < ε) (ℓ : ℕ) :
    coulombBFactor ε ℓ = coulombAProd ε ℓ / (1 - Real.exp (-(2 * π / Real.sqrt ε))) := by
  simp only [coulombBFactor, hε, ↓reduceIte]


/-- `∏_{k=1}^{ℓ} (η² + k²) η^{-2ℓ} = A(1/η², ℓ)`. -/
private lemma prod_Icc_sq_add_sq_mul_eq_coulombAProd (ℓ : ℕ) {η : ℝ} (hη : η ≠ 0) :
    (∏ k ∈ Finset.Icc 1 ℓ, (η ^ 2 + (k : ℝ) ^ 2)) * (1 / η ^ 2) ^ ℓ =
      coulombAProd (1 / η ^ 2) ℓ := by
  induction ℓ with
  | zero => simp [coulombAProd]
  | succ ℓ ih =>
    rw [Finset.prod_Icc_succ_top (by omega), coulombAProd, Finset.prod_range_succ, ← coulombAProd,
      ← ih, pow_succ (1 / η ^ 2) ℓ]
    have h : (η ^ 2 + ((ℓ + 1 : ℕ) : ℝ) ^ 2) * (1 / η ^ 2) =
        1 + 1 / η ^ 2 * ((ℓ + 1 : ℕ) : ℝ) ^ 2 := by
      field_simp
    rw [← h]
    ring

/-- `((2ℓ+1)! C_ℓ(η))² = 2^{2ℓ} (2πη/(e^{2πη}-1)) η^{2ℓ} A(1/η², ℓ)`. -/
private lemma factorial_mul_coulombC_sq (ℓ : ℕ) {η : ℝ} (hη : η ≠ 0) :
    ((2 * ℓ + 1)! * coulombC ℓ η) ^ 2 =
      2 ^ (2 * ℓ) * (2 * π * η / (Real.exp (2 * π * η) - 1)) * (η ^ 2) ^ ℓ *
        coulombAProd (1 / η ^ 2) ℓ := by
  rw [mul_pow, coulombC_sq_eq_prod ℓ hη, ← prod_Icc_sq_add_sq_mul_eq_coulombAProd ℓ hη]
  have hf : ((2 * ℓ + 1)! : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  rw [div_pow, one_pow]
  field_simp

/-- **DLMF 33.16.4**: for `ε > 0`, `τ = ε^{1/2}` (33.16.3) and `r > 0`,
`f(ε,ℓ;r) = ((2/(πτ)) (1 - e^{-2π/τ}) / A(ε,ℓ))^{1/2} F_ℓ(-1/τ, τr)`. This is stronger than DLMF,
which assumes `r > 0`. -/
@[dlmf 33.16.E3, dlmf 33.16.E4]
theorem coulombf_eq_coulombF_pos' {ε : ℝ} (hε : 0 < ε) (ℓ : ℕ) {r : ℝ} :
    coulombf ε ℓ r = Real.sqrt (2 / (π * Real.sqrt ε) *
        (1 - Real.exp (-(2 * π / Real.sqrt ε))) / coulombAProd ε ℓ) *
      coulombF ℓ (-1 / Real.sqrt ε) (Real.sqrt ε * r) := by
  have hτ := Real.sqrt_pos.mpr hε
  set τ := Real.sqrt ε with hτ_def
  have hτ2 : τ ^ 2 = ε := Real.sq_sqrt hε.le
  have hη : (-1 / τ) ≠ 0 := by positivity
  rw [coulombF_eq_coulombf ℓ hη, show -(-1 / τ) * (τ * r) = r by field_simp,
    show 1 / (-1 / τ) ^ 2 = ε by rw [← hτ2]; field_simp]
  have hA := coulombAProd_pos hε.le ℓ
  have hE := one_sub_exp_neg_two_pi_div_sqrt_pos hε
  have hC := coulombC_pos ℓ (-1 / τ)
  have hK := factorial_mul_coulombC_sq ℓ hη
  rw [show 1 / (-1 / τ) ^ 2 = ε by rw [← hτ2]; field_simp,
    show 2 * π * (-1 / τ) = -(2 * π / τ) by ring] at hK
  set K := (2 * ℓ + 1)! * coulombC ℓ (-1 / τ) with hK_def
  have hKpos : 0 < K := by positivity
  have hd : (-2 * (-1 / τ)) ^ (ℓ + 1) = (2 / τ) ^ (ℓ + 1) := by congr 1; ring
  rw [hd]
  suffices h : Real.sqrt (2 / (π * τ) * (1 - Real.exp (-(2 * π / τ))) / coulombAProd ε ℓ) *
      (K / (2 / τ) ^ (ℓ + 1)) = 1 by
    linear_combination (-coulombf ε ℓ r) * h
  rw [← Real.sqrt_sq (by positivity : 0 ≤ K / (2 / τ) ^ (ℓ + 1)), ← Real.sqrt_mul (by positivity),
    div_pow, hK]
  rw [Real.sqrt_eq_one]
  have hE' : Real.exp (-(2 * π / τ)) - 1 ≠ 0 := by linarith
  have hτ0 : τ ≠ 0 := hτ.ne'
  have hA0 : coulombAProd ε ℓ ≠ 0 := hA.ne'
  rw [show ((-1 / τ) ^ 2) ^ ℓ = 1 / τ ^ (2 * ℓ) by
      rw [div_pow, neg_one_sq, one_div_pow, ← pow_mul],
    show ((2 / τ) ^ (ℓ + 1)) ^ 2 = 2 ^ (2 * ℓ) * 4 / (τ ^ (2 * ℓ) * τ ^ 2) by
      rw [← pow_mul, div_pow, ← pow_add, show (ℓ + 1) * 2 = 2 * ℓ + 2 by ring, pow_add]
      norm_num]
  field_simp
  ring

/-- **DLMF 33.16.4**: for `ε > 0`, `τ = ε^{1/2}` (33.16.3) and `r > 0`,
`f(ε,ℓ;r) = ((2/(πτ)) (1 - e^{-2π/τ}) / A(ε,ℓ))^{1/2} F_ℓ(-1/τ, τr)`. -/
@[dlmf 33.16.E3, dlmf 33.16.E4]
theorem coulombf_eq_coulombF_pos {ε : ℝ} (hε : 0 < ε) (ℓ : ℕ) {r : ℝ} (_hr : 0 < r) :
    coulombf ε ℓ r = Real.sqrt (2 / (π * Real.sqrt ε) *
        (1 - Real.exp (-(2 * π / Real.sqrt ε))) / coulombAProd ε ℓ) *
      coulombF ℓ (-1 / Real.sqrt ε) (Real.sqrt ε * r) :=
  coulombf_eq_coulombF_pos' hε ℓ

/-- **DLMF 33.16.5**: for `ε > 0`, `r > 0`,
`h(ε,ℓ;r) = ((2/(πτ)) A(ε,ℓ) / (1 - e^{-2π/τ}))^{1/2} G_ℓ(-1/τ, τr)`. -/
@[dlmf 33.16.E5]
theorem coulombh_eq_coulombG_pos {ε : ℝ} (hε : 0 < ε) (ℓ : ℕ) {r : ℝ} (hr : 0 < r) :
    coulombh ε ℓ r = Real.sqrt (2 / (π * Real.sqrt ε) * coulombAProd ε ℓ /
        (1 - Real.exp (-(2 * π / Real.sqrt ε)))) *
      coulombG ℓ (-1 / Real.sqrt ε) (Real.sqrt ε * r) := by
  have hτ := Real.sqrt_pos.mpr hε
  set τ := Real.sqrt ε with hτ_def
  have hτ2 : τ ^ 2 = ε := Real.sq_sqrt hε.le
  have hη : (-1 / τ) ≠ 0 := by positivity
  rw [coulombG_eq_coulombh ℓ hη (by positivity), show -(-1 / τ) * (τ * r) = r by field_simp,
    show 1 / (-1 / τ) ^ 2 = ε by rw [← hτ2]; field_simp]
  have hA := coulombAProd_pos hε.le ℓ
  have hC := coulombC_pos ℓ (-1 / τ)
  have hK := factorial_mul_coulombC_sq ℓ hη
  rw [show 1 / (-1 / τ) ^ 2 = ε by rw [← hτ2]; field_simp,
    show 2 * π * (-1 / τ) = -(2 * π / τ) by ring] at hK
  set K := (2 * ℓ + 1)! * coulombC ℓ (-1 / τ) with hK_def
  have hKpos : 0 < K := by positivity
  have hd : (-2 * (-1 / τ)) ^ ℓ = (2 / τ) ^ ℓ := by congr 1; ring
  rw [hd]
  have hE : 0 < 1 - Real.exp (-(2 * π / τ)) := by
    have : 0 < 2 * π / τ := by positivity
    have := Real.exp_lt_one_iff.mpr (neg_neg_of_pos this)
    linarith
  suffices h : Real.sqrt (2 / (π * τ) * coulombAProd ε ℓ / (1 - Real.exp (-(2 * π / τ)))) =
      K / (π * (2 / τ) ^ ℓ) by
    rw [h]; field_simp
  rw [← Real.sqrt_sq (by positivity : 0 ≤ K / (π * (2 / τ) ^ ℓ)), div_pow, hK]
  congr 1
  have hE' : Real.exp (-(2 * π / τ)) - 1 ≠ 0 := by linarith
  have hτ0 : τ ≠ 0 := hτ.ne'
  rw [show ((-1 / τ) ^ 2) ^ ℓ = 1 / τ ^ (2 * ℓ) by
      rw [div_pow, neg_one_sq, one_div_pow, ← pow_mul],
    show (π * (2 / τ) ^ ℓ) ^ 2 = π ^ 2 * (2 ^ (2 * ℓ) / τ ^ (2 * ℓ)) by
      rw [mul_pow, ← pow_mul, div_pow, mul_comm ℓ 2]]
  field_simp
  ring

/-- **DLMF 33.16.6**: for `ε > 0`, `r < 0`,
`f(ε,ℓ;r) = (-1)^{ℓ+1} ((2/(πτ)) (e^{2π/τ} - 1) / A(ε,ℓ))^{1/2} F_ℓ(1/τ, -τr)`. This is stronger
than DLMF, which assumes `r < 0`. -/
@[dlmf 33.16.E6]
theorem coulombf_eq_coulombF_neg' {ε : ℝ} (hε : 0 < ε) (ℓ : ℕ) {r : ℝ} :
    coulombf ε ℓ r = (-1) ^ (ℓ + 1) * Real.sqrt (2 / (π * Real.sqrt ε) *
        (Real.exp (2 * π / Real.sqrt ε) - 1) / coulombAProd ε ℓ) *
      coulombF ℓ (1 / Real.sqrt ε) (-(Real.sqrt ε * r)) := by
  have hτ := Real.sqrt_pos.mpr hε
  set τ := Real.sqrt ε with hτ_def
  have hτ2 : τ ^ 2 = ε := Real.sq_sqrt hε.le
  have hη : (1 / τ) ≠ 0 := by positivity
  rw [coulombF_eq_coulombf ℓ hη, show -(1 / τ) * -(τ * r) = r by field_simp,
    show 1 / (1 / τ) ^ 2 = ε by rw [← hτ2]; field_simp]
  have hA := coulombAProd_pos hε.le ℓ
  have hC := coulombC_pos ℓ (1 / τ)
  have hK := factorial_mul_coulombC_sq ℓ hη
  rw [show 1 / (1 / τ) ^ 2 = ε by rw [← hτ2]; field_simp,
    show 2 * π * (1 / τ) = 2 * π / τ by ring] at hK
  set K := (2 * ℓ + 1)! * coulombC ℓ (1 / τ) with hK_def
  have hKpos : 0 < K := by positivity
  have hd : (-2 * (1 / τ)) ^ (ℓ + 1) = (-1) ^ (ℓ + 1) * (2 / τ) ^ (ℓ + 1) := by
    rw [← mul_pow]; congr 1; ring
  rw [hd]
  suffices h : Real.sqrt (2 / (π * τ) * (Real.exp (2 * π / τ) - 1) / coulombAProd ε ℓ) *
      (K / (2 / τ) ^ (ℓ + 1)) = 1 by
    have h1 : ((-1 : ℝ) ^ (ℓ + 1)) ≠ 0 := pow_ne_zero _ (by norm_num)
    symm
    calc _ = Real.sqrt (2 / (π * τ) * (Real.exp (2 * π / τ) - 1) / coulombAProd ε ℓ) *
          (K / (2 / τ) ^ (ℓ + 1)) * coulombf ε ℓ r *
          ((-1 : ℝ) ^ (ℓ + 1) / (-1 : ℝ) ^ (ℓ + 1)) := by ring
      _ = _ := by rw [div_self h1, mul_one, h, one_mul]
  have hD : 0 < Real.exp (2 * π / τ) - 1 := by
    have := Real.one_lt_exp_iff.mpr (show 0 < 2 * π / τ by positivity); linarith
  rw [← Real.sqrt_sq (by positivity : 0 ≤ K / (2 / τ) ^ (ℓ + 1)), ← Real.sqrt_mul (by positivity),
    div_pow, hK]
  rw [Real.sqrt_eq_one]
  have hτ0 : τ ≠ 0 := hτ.ne'
  have hA0 : coulombAProd ε ℓ ≠ 0 := hA.ne'
  rw [show ((1 / τ) ^ 2) ^ ℓ = 1 / τ ^ (2 * ℓ) by
      rw [div_pow, one_pow, one_div_pow, ← pow_mul],
    show ((2 / τ) ^ (ℓ + 1)) ^ 2 = 2 ^ (2 * ℓ) * 4 / (τ ^ (2 * ℓ) * τ ^ 2) by
      rw [← pow_mul, div_pow, ← pow_add, show (ℓ + 1) * 2 = 2 * ℓ + 2 by ring, pow_add]
      norm_num]
  field_simp
  ring

/-- **DLMF 33.16.6**: for `ε > 0`, `r < 0`,
`f(ε,ℓ;r) = (-1)^{ℓ+1} ((2/(πτ)) (e^{2π/τ} - 1) / A(ε,ℓ))^{1/2} F_ℓ(1/τ, -τr)`. -/
@[dlmf 33.16.E6]
theorem coulombf_eq_coulombF_neg {ε : ℝ} (hε : 0 < ε) (ℓ : ℕ) {r : ℝ} (_hr : r < 0) :
    coulombf ε ℓ r = (-1) ^ (ℓ + 1) * Real.sqrt (2 / (π * Real.sqrt ε) *
        (Real.exp (2 * π / Real.sqrt ε) - 1) / coulombAProd ε ℓ) *
      coulombF ℓ (1 / Real.sqrt ε) (-(Real.sqrt ε * r)) :=
  coulombf_eq_coulombF_neg' hε ℓ

/-- **DLMF 33.16.7**: for `ε > 0`, `r < 0`,
`h(ε,ℓ;r) = (-1)^ℓ ((2/(πτ)) A(ε,ℓ) / (e^{2π/τ} - 1))^{1/2} G_ℓ(1/τ, -τr)`. -/
@[dlmf 33.16.E7]
theorem coulombh_eq_coulombG_neg {ε : ℝ} (hε : 0 < ε) (ℓ : ℕ) {r : ℝ} (hr : r < 0) :
    coulombh ε ℓ r = (-1) ^ ℓ * Real.sqrt (2 / (π * Real.sqrt ε) * coulombAProd ε ℓ /
        (Real.exp (2 * π / Real.sqrt ε) - 1)) *
      coulombG ℓ (1 / Real.sqrt ε) (-(Real.sqrt ε * r)) := by
  have hτ := Real.sqrt_pos.mpr hε
  set τ := Real.sqrt ε with hτ_def
  have hτ2 : τ ^ 2 = ε := Real.sq_sqrt hε.le
  have hη : (1 / τ) ≠ 0 := by positivity
  have hρ : 0 < -(τ * r) := by nlinarith
  rw [coulombG_eq_coulombh ℓ hη hρ, show -(1 / τ) * -(τ * r) = r by field_simp,
    show 1 / (1 / τ) ^ 2 = ε by rw [← hτ2]; field_simp]
  have hA := coulombAProd_pos hε.le ℓ
  have hC := coulombC_pos ℓ (1 / τ)
  have hK := factorial_mul_coulombC_sq ℓ hη
  rw [show 1 / (1 / τ) ^ 2 = ε by rw [← hτ2]; field_simp,
    show 2 * π * (1 / τ) = 2 * π / τ by ring] at hK
  set K := (2 * ℓ + 1)! * coulombC ℓ (1 / τ) with hK_def
  have hKpos : 0 < K := by positivity
  have hd : (-2 * (1 / τ)) ^ ℓ = (-1) ^ ℓ * (2 / τ) ^ ℓ := by
    rw [← mul_pow]; congr 1; ring
  rw [hd]
  have hD : 0 < Real.exp (2 * π / τ) - 1 := by
    have := Real.one_lt_exp_iff.mpr (show 0 < 2 * π / τ by positivity); linarith
  suffices h : Real.sqrt (2 / (π * τ) * coulombAProd ε ℓ / (Real.exp (2 * π / τ) - 1)) =
      K / (π * (2 / τ) ^ ℓ) by
    have hm1 : ((-1 : ℝ) ^ ℓ) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [h]; field_simp
    linear_combination (-coulombh ε ℓ r) * hm1
  rw [← Real.sqrt_sq (by positivity : 0 ≤ K / (π * (2 / τ) ^ ℓ)), div_pow, hK]
  congr 1
  have hτ0 : τ ≠ 0 := hτ.ne'
  rw [show ((1 / τ) ^ 2) ^ ℓ = 1 / τ ^ (2 * ℓ) by
      rw [div_pow, one_pow, one_div_pow, ← pow_mul],
    show (π * (2 / τ) ^ ℓ) ^ 2 = π ^ 2 * (2 ^ (2 * ℓ) / τ ^ (2 * ℓ)) by
      rw [mul_pow, ← pow_mul, div_pow, mul_comm ℓ 2]]
  field_simp

/-- **DLMF 33.16.14**: for `ε > 0`, `r > 0`, `s(ε,ℓ;r) = (πτ)^{-1/2} F_ℓ(-1/τ, τr)` and
`c(ε,ℓ;r) = (πτ)^{-1/2} G_ℓ(-1/τ, τr)`. -/
@[dlmf 33.16.E14]
theorem coulombs_coulombc_eq_pos {ε : ℝ} (hε : 0 < ε) (ℓ : ℕ) {r : ℝ} (hr : 0 < r) :
    coulombs ε ℓ r = ((Real.sqrt (π * Real.sqrt ε))⁻¹ *
        coulombF ℓ (-1 / Real.sqrt ε) (Real.sqrt ε * r) : ℝ) ∧
      coulombc ε ℓ r = ((Real.sqrt (π * Real.sqrt ε))⁻¹ *
        coulombG ℓ (-1 / Real.sqrt ε) (Real.sqrt ε * r) : ℝ) := by
  have hA := coulombAProd_pos hε.le ℓ
  have hE := one_sub_exp_neg_two_pi_div_sqrt_pos hε
  have hτ := Real.sqrt_pos.mpr hε
  have hB := coulombBFactor_eq_of_pos hε ℓ
  have hπτ : 0 < π * Real.sqrt ε := by positivity
  constructor
  · rw [coulombs, hB, Carlson.ofReal_cpow_half (by positivity), coulombf_eq_coulombF_pos hε ℓ hr,
      ← Complex.ofReal_mul, ← mul_assoc, ← Real.sqrt_mul (by positivity)]
    congr 3
    rw [← Real.sqrt_inv]
    congr 1
    field_simp
  · rw [coulombc, hB, ofReal_cpow_neg_half_eq_inv_sqrt (by positivity), coulombh_eq_coulombG_pos hε
        ℓ hr,
      ← Complex.ofReal_mul, ← mul_assoc, ← Real.sqrt_inv, ← Real.sqrt_mul (by positivity)]
    congr 3
    rw [← Real.sqrt_inv]
    congr 1
    field_simp

/-- **DLMF 33.16.15, corrected**: for `ε > 0`, `r < 0`,
`s(ε,ℓ;r) = (-1)^{ℓ+1} e^{π/τ} (πτ)^{-1/2} F_ℓ(1/τ, -τr)` and
`c(ε,ℓ;r) = (-1)^ℓ e^{-π/τ} (πτ)^{-1/2} G_ℓ(1/τ, -τr)`. DLMF prints these without the factors
`(-1)^{ℓ+1} e^{π/τ}` and `(-1)^ℓ e^{-π/τ}`, contradicting 33.16.6–33.16.7 and 33.14.9–33.14.10. -/
@[dlmf 33.16.E15]
theorem coulombs_coulombc_eq_neg {ε : ℝ} (hε : 0 < ε) (ℓ : ℕ) {r : ℝ} (hr : r < 0) :
    coulombs ε ℓ r = ((-1) ^ (ℓ + 1) * Real.exp (π / Real.sqrt ε) *
        (Real.sqrt (π * Real.sqrt ε))⁻¹ *
        coulombF ℓ (1 / Real.sqrt ε) (-(Real.sqrt ε * r)) : ℝ) ∧
      coulombc ε ℓ r = ((-1) ^ ℓ * Real.exp (-(π / Real.sqrt ε)) *
        (Real.sqrt (π * Real.sqrt ε))⁻¹ *
        coulombG ℓ (1 / Real.sqrt ε) (-(Real.sqrt ε * r)) : ℝ) := by
  have hA := coulombAProd_pos hε.le ℓ
  have hE := one_sub_exp_neg_two_pi_div_sqrt_pos hε
  have hτ := Real.sqrt_pos.mpr hε
  have hB := coulombBFactor_eq_of_pos hε ℓ
  have hπτ : 0 < π * Real.sqrt ε := by positivity
  have hq := Real.exp_pos (π / Real.sqrt ε)
  have h2 : Real.exp (2 * π / Real.sqrt ε) = Real.exp (π / Real.sqrt ε) ^ 2 := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  have h3 : Real.exp (-(2 * π / Real.sqrt ε)) = (Real.exp (π / Real.sqrt ε) ^ 2)⁻¹ := by
    rw [Real.exp_neg, h2]
  have hD : 0 < Real.exp (2 * π / Real.sqrt ε) - 1 := by
    have : 0 < 2 * π / Real.sqrt ε := by positivity
    have := Real.one_lt_exp_iff.mpr this
    linarith
  constructor
  · rw [coulombs, hB, Carlson.ofReal_cpow_half (by positivity), coulombf_eq_coulombF_neg hε ℓ hr,
      ← Complex.ofReal_mul]
    congr 1
    have key : Real.sqrt (coulombAProd ε ℓ / (1 - Real.exp (-(2 * π / Real.sqrt ε))) / 2) *
        Real.sqrt (2 / (π * Real.sqrt ε) * (Real.exp (2 * π / Real.sqrt ε) - 1) /
          coulombAProd ε ℓ) = Real.exp (π / Real.sqrt ε) * (Real.sqrt (π * Real.sqrt ε))⁻¹ := by
      rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_sq hq.le, ← Real.sqrt_inv,
        ← Real.sqrt_mul (sq_nonneg _)]
      congr 1
      rw [h2, h3]
      have hq2 : Real.exp (π / Real.sqrt ε) ^ 2 - 1 ≠ 0 := by
        rw [← h2]; exact hD.ne'
      have hq1 : 1 - (Real.exp (π / Real.sqrt ε) ^ 2)⁻¹ ≠ 0 := by rw [← h3]; exact hE.ne'
      field_simp
    linear_combination ((-1) ^ (ℓ + 1) * coulombF ℓ (1 / Real.sqrt ε) (-(Real.sqrt ε * r))) * key
  · rw [coulombc, hB, ofReal_cpow_neg_half_eq_inv_sqrt (by positivity), coulombh_eq_coulombG_neg hε
        ℓ hr,
      ← Complex.ofReal_mul]
    congr 1
    have key : (Real.sqrt (2 * (coulombAProd ε ℓ / (1 - Real.exp (-(2 * π / Real.sqrt ε))))))⁻¹ *
        Real.sqrt (2 / (π * Real.sqrt ε) * coulombAProd ε ℓ /
          (Real.exp (2 * π / Real.sqrt ε) - 1)) =
        Real.exp (-(π / Real.sqrt ε)) * (Real.sqrt (π * Real.sqrt ε))⁻¹ := by
      have e1 : Real.exp (-(π / Real.sqrt ε)) = Real.sqrt ((Real.exp (π / Real.sqrt ε) ^ 2)⁻¹) := by
        rw [Real.sqrt_inv, Real.sqrt_sq hq.le, Real.exp_neg]
      have hpos : 0 ≤ (2 * (coulombAProd ε ℓ / (1 - Real.exp (-(2 * π / Real.sqrt ε)))))⁻¹ :=
        (inv_pos.mpr (mul_pos two_pos (div_pos hA hE))).le
      rw [e1, ← Real.sqrt_inv, ← Real.sqrt_inv, ← Real.sqrt_mul hpos,
        ← Real.sqrt_mul (inv_nonneg.mpr (sq_nonneg _))]
      congr 1
      rw [h2, h3]
      have hq2 : Real.exp (π / Real.sqrt ε) ^ 2 - 1 ≠ 0 := by
        rw [← h2]; exact hD.ne'
      have hq1 : 1 - (Real.exp (π / Real.sqrt ε) ^ 2)⁻¹ ≠ 0 := by rw [← h3]; exact hE.ne'
      field_simp
    linear_combination ((-1) ^ ℓ * coulombG ℓ (1 / Real.sqrt ε) (-(Real.sqrt ε * r))) * key

/-! ### `ε < 0`: `f`, `h`, `s`, `c` in terms of Whittaker functions (`ν = (-ε)^{-1/2}`) -/

/-- `ν = (-ε)^{-1/2} > 0` for `ε < 0`. -/
private lemma neg_rpow_neg_half_pos {ε : ℝ} (hε : ε < 0) : 0 < (-ε) ^ (-(1 / 2 : ℝ)) :=
  Real.rpow_pos_of_pos (neg_pos.mpr hε) _

/-- `κ = ν` for `ε < 0`, `r > 0`. -/
private lemma coulombKappa_of_neg_of_pos {ε : ℝ} (hε : ε < 0) {r : ℝ} (hr : 0 < r) :
    coulombKappa ε r = ((-ε) ^ (-(1 / 2 : ℝ)) : ℝ) := by
  simp [coulombKappa, hε, hr]

/-- `κ = -ν` for `ε < 0`, `r ≤ 0`. -/
private lemma coulombKappa_of_neg_of_nonpos {ε : ℝ} (hε : ε < 0) {r : ℝ} (hr : r ≤ 0) :
    coulombKappa ε r = -(((-ε) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
  simp [coulombKappa, hε, not_lt.mpr hr]

/-- `ε = -1/ν²`. -/
private lemma eq_neg_one_div_neg_rpow_neg_half_sq {ε : ℝ} (hε : ε < 0) : ε = -1 /
    ((-ε) ^ (-(1 / 2 : ℝ))) ^ 2 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (neg_pos.mpr hε).le]
  norm_num [Real.rpow_neg_one]

/-- `A(ε,ℓ) ≠ 0` excludes `ν ∈ {1, …, ℓ}`. -/
private lemma neg_rpow_neg_half_sub_ne_neg_nat {ε : ℝ} (hε : ε < 0) {ℓ : ℕ}
    (hA : coulombAProd ε ℓ ≠ 0) (m : ℕ) :
    (((-ε) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) - ℓ ≠ -(m : ℂ) := by
  intro h
  set ν := (-ε) ^ (-(1 / 2 : ℝ))
  have hν := neg_rpow_neg_half_pos hε
  have h' : ν = (ℓ : ℝ) - m := by
    have := congrArg Complex.re h; simp at this; linarith
  have hm : m < ℓ := by
    have : (0 : ℝ) < ℓ - m := h' ▸ hν
    exact_mod_cast (by linarith : (m : ℝ) < ℓ)
  apply hA
  unfold coulombAProd
  apply Finset.prod_eq_zero (i := ℓ - m) (Finset.mem_range.mpr (by omega))
  rw [eq_neg_one_div_neg_rpow_neg_half_sq hε, Nat.cast_sub hm.le, ← h']
  have : ν ≠ 0 := hν.ne'
  field_simp
  ring

/-- `ζ_ℓ(ν,r)` is real when `2r/ν > 0`. -/
private lemma conj_coulombZeta (ℓ : ℕ) {ν r : ℝ} (h : 0 < 2 * r / ν) :
    conj (coulombZeta ℓ ν r) = coulombZeta ℓ ν r := by
  have hs : ((2 * r / ν : ℝ) : ℂ) ∈ slitPlane := Complex.ofReal_mem_slitPlane.mpr h
  unfold coulombZeta
  have e : (2 * r / ν : ℂ) = ((2 * r / ν : ℝ) : ℂ) := by push_cast; ring
  rw [e, map_mul, map_mul, map_pow, ← Complex.exp_conj, conj_kummerU _ _ hs]
  simp [Complex.conj_ofReal, map_sub, map_add, map_mul, map_natCast, map_ofNat]

/-- `e^{nπi} = (-1)^n`. -/
private lemma exp_nat_mul_pi_mul_I (n : ℕ) : exp ((n : ℂ) * π * I) = (-1) ^ n := by
  rw [show (n : ℂ) * π * I = n * (π * I) by ring, Complex.exp_nat_mul, exp_pi_mul_I]

/-- Kummer's connection formula 13.2.41 at a positive real argument `z = x`, in the form used for
`f` (`a = ℓ+1-κ`, `b = 2ℓ+2`). -/
private lemma kummerM_two_mul_add_two_eq_kummerU_connection (ℓ : ℕ) (a : ℂ) {x : ℝ} (hx : 0 < x) :
    kummerM a (2 * ℓ + 2) x = (2 * ℓ + 1)! * (exp (-a * π * I) / Gamma (2 * ℓ + 2 - a) *
      kummerU a (2 * ℓ + 2) x + exp ((2 * ℓ + 2 - a) * π * I) / Gamma a * exp x *
        kummerU (2 * ℓ + 2 - a) (2 * ℓ + 2) (-(x : ℂ))) := by
  have hs : (x : ℂ) ∈ slitPlane := Complex.ofReal_mem_slitPlane.mpr hx
  have h := kummerM_eq_kummerU_connection a (2 * ℓ + 2) hs true
    (by simp [Complex.arg_ofReal_of_nonneg hx.le]) (two_mul_nat_add_two_ne_neg_nat ℓ)
  simp only [↓reduceIte, neg_mul, one_mul] at h
  rw [exp_pi_mul_I, neg_one_mul] at h
  have hG : Gamma (2 * ℓ + 2 : ℂ) = (2 * ℓ + 1)! := by
    rw [show (2 * ℓ + 2 : ℂ) = ((2 * ℓ + 1 : ℕ) : ℂ) + 1 by push_cast; ring,
      Complex.Gamma_nat_eq_factorial]
  rw [hG] at h
  have hf : ((2 * ℓ + 1)! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  rw [div_eq_iff hf] at h
  rw [h]
  ring_nf

/-- `1/Γ(1-x) = sin(πx) Γ(x)/π` when `Γ(x) ≠ 0`. -/
private lemma inv_Gamma_one_sub_real {x : ℝ} (hx : Real.Gamma x ≠ 0) :
    (Real.Gamma (1 - x))⁻¹ = Real.sin (π * x) * Real.Gamma x / π := by
  have h := Real.Gamma_mul_Gamma_one_sub x
  by_cases hs : Real.sin (π * x) = 0
  · rw [hs, div_zero] at h
    rw [hs, (mul_eq_zero.mp h).resolve_left hx]; simp
  · have h2 : Real.Gamma (1 - x) = π / (Real.sin (π * x) * Real.Gamma x) := by
      rw [eq_div_iff (mul_ne_zero hs hx)]
      rw [eq_div_iff hs] at h
      linear_combination h
    rw [h2, inv_div]

/-- `sin(π(ν-ℓ)) = (-1)^ℓ sin(πν)`. -/
private lemma sin_pi_mul_sub_nat (ν : ℝ) (ℓ : ℕ) :
    Real.sin (π * (ν - ℓ)) = (-1) ^ ℓ * Real.sin (π * ν) := by
  rw [mul_sub, Real.sin_sub, mul_comm π (ℓ : ℝ), Real.sin_nat_mul_pi, Real.cos_nat_mul_pi]
  ring

/-- **DLMF 33.16.10**: for `ε < 0`, `ν = (-ε)^{-1/2}` (33.16.8) and `r > 0`, away from
`A(ε,ℓ) = 0` (the poles of `Γ(ν-ℓ)`),
`f(ε,ℓ;r) = (-1)^ℓ ν^{ℓ+1} (-cos(πν) ζ_ℓ(ν,r)/Γ(ℓ+1+ν) + sin(πν) Γ(ν-ℓ) ξ_ℓ(ν,r)/π)`. -/
@[dlmf 33.16.E8, dlmf 33.16.E10]
theorem coulombf_eq_whittaker_pos {ε : ℝ} (hε : ε < 0) (ℓ : ℕ) {r : ℝ} (hr : 0 < r)
    (hA : coulombAProd ε ℓ ≠ 0) :
    let ν := (-ε) ^ (-(1 / 2 : ℝ))
    (coulombf ε ℓ r : ℂ) = (-1) ^ ℓ * (ν : ℂ) ^ (ℓ + 1) *
      (-(Real.cos (π * ν) : ℂ) * coulombZeta ℓ ν r / (Real.Gamma (ℓ + 1 + ν) : ℂ) +
        (Real.sin (π * ν) * Real.Gamma (ν - ℓ) * coulombXi ℓ ν r / π : ℝ)) := by
  intro ν
  have hν : 0 < ν := neg_rpow_neg_half_pos hε
  have hκ : coulombKappa ε r = (ν : ℂ) := coulombKappa_of_neg_of_pos hε hr
  have hνA : ∀ m : ℕ, (ν : ℂ) - ℓ ≠ -(m : ℂ) := neg_rpow_neg_half_sub_ne_neg_nat hε hA
  have hx : 0 < 2 * r / ν := by positivity
  set x := 2 * r / ν with hx_def
  have hζ := conj_coulombZeta ℓ (ν := ν) (r := r) hx
  have hxc : (2 * (r : ℂ) / (ν : ℂ)) = (x : ℂ) := by rw [hx_def]; push_cast; ring
  have hν0 : (ν : ℂ) ≠ 0 := by exact_mod_cast hν.ne'
  have hE : (coulombf ε ℓ r : ℂ) =
      (ν : ℂ) ^ (ℓ + 1) * exp (-((ℓ : ℂ) + 1 - ν) * π * I) / Gamma (ℓ + 1 + ν) *
        coulombZeta ℓ ν r +
      (ν : ℂ) ^ (ℓ + 1) / Gamma (ℓ + 1 - ν) *
        (exp (I * π * (ν : ℂ)) * (exp (-(-(2 * (r : ℂ) / (ν : ℂ))) / 2) *
          (-(2 * (r : ℂ) / (ν : ℂ))) ^ (ℓ + 1) *
          kummerU (ℓ + 1 + (ν : ℂ)) (2 * ℓ + 2) (-(2 * (r : ℂ) / (ν : ℂ))))) := by
    rw [ofReal_coulombf hε.ne, hκ]
    unfold coulombfKummer coulombZeta
    rw [hxc, kummerM_two_mul_add_two_eq_kummerU_connection ℓ _ hx]
    have hr2 : (2 * (r : ℂ)) = (ν : ℂ) * x := by rw [← hxc]; field_simp
    have he1 : exp (-(r : ℂ) / (ν : ℂ)) = exp (-(x : ℂ) / 2) := by
      congr 1; rw [← hxc]; field_simp
    rw [hr2, he1]
    have he3 : exp ((2 * (ℓ : ℂ) + 2 - (ℓ + 1 - (ν : ℂ))) * π * I) =
        (-1) ^ (ℓ + 1) * exp (I * π * (ν : ℂ)) := by
      rw [← exp_nat_mul_pi_mul_I, ← Complex.exp_add]; congr 1; push_cast; ring
    have he2 : exp (-(x : ℂ) / 2) * exp (x : ℂ) = exp (-(-(x : ℂ)) / 2) := by
      rw [← Complex.exp_add]; congr 1; ring
    have hf : ((2 * ℓ + 1)! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    rw [he3, show (2 * (ℓ : ℂ) + 2 - (ℓ + 1 - (ν : ℂ))) = ℓ + 1 + ν by ring,
      mul_pow, neg_pow (x : ℂ), ← he2]
    field_simp
  set W := exp (I * π * (ν : ℂ)) * (exp (-(-(2 * (r : ℂ) / (ν : ℂ))) / 2) *
          (-(2 * (r : ℂ) / (ν : ℂ))) ^ (ℓ + 1) *
          kummerU (ℓ + 1 + (ν : ℂ)) (2 * ℓ + 2) (-(2 * (r : ℂ) / (ν : ℂ))))
    with hW
  have hXi : coulombXi ℓ ν r = W.re := rfl
  set ζ := coulombZeta ℓ ν r with hζdef
  have hζr : ζ = (ζ.re : ℂ) := (Complex.conj_eq_iff_re.mp hζ).symm
  have hWr : W = (W.re : ℂ) + (W.im : ℂ) * I := (Complex.re_add_im W).symm
  set zr := ζ.re
  set wr := W.re
  set wi := W.im
  set c := Real.cos (π * ν)
  set s := Real.sin (π * ν)
  have hexp : exp (-((ℓ : ℂ) + 1 - ν) * π * I) = (-1) ^ (ℓ + 1) * ((c : ℂ) + (s : ℂ) * I) := by
    have h2 : exp (((2 * (ℓ + 1) : ℕ) : ℂ) * π * I) = 1 := by
      rw [exp_nat_mul_pi_mul_I, pow_mul]; simp
    have h3 : exp (((π * ν : ℝ) : ℂ) * I) = (c : ℂ) + (s : ℂ) * I := by
      rw [Complex.exp_mul_I]; simp only [c, s]; push_cast; ring
    rw [show -((ℓ : ℂ) + 1 - ν) * π * I = ((ℓ + 1 : ℕ) : ℂ) * π * I +
        ((π * ν : ℝ) : ℂ) * I - ((2 * (ℓ + 1) : ℕ) : ℂ) * π * I by push_cast; ring,
      Complex.exp_sub, Complex.exp_add, h2, h3, exp_nat_mul_pi_mul_I, div_one]
  have hG1 : Gamma ((ℓ : ℂ) + 1 - ν) = (Real.Gamma (ℓ + 1 - ν) : ℂ) := by
    rw [← Complex.Gamma_ofReal]; push_cast; ring_nf
  have hG2 : Gamma ((ℓ : ℂ) + 1 + ν) = (Real.Gamma (ℓ + 1 + ν) : ℂ) := by
    rw [← Complex.Gamma_ofReal]; push_cast; ring_nf
  have hGr : Real.Gamma (ν - ℓ) ≠ 0 := by
    have := Complex.Gamma_ne_zero hνA
    rw [show (ν : ℂ) - ℓ = ((ν - ℓ : ℝ) : ℂ) by push_cast; ring, Complex.Gamma_ofReal] at this
    exact_mod_cast this
  have hinv : (Real.Gamma (ℓ + 1 - ν))⁻¹ = (-1) ^ ℓ * s * Real.Gamma (ν - ℓ) / π := by
    rw [show (ℓ : ℝ) + 1 - ν = 1 - (ν - ℓ) by ring, inv_Gamma_one_sub_real hGr,
      sin_pi_mul_sub_nat]
  set G1 := Real.Gamma (ℓ + 1 - ν)
  set G2 := Real.Gamma (ℓ + 1 + ν)
  have hE2 : (coulombf ε ℓ r : ℂ) =
      (((-1) ^ (ℓ + 1) * ν ^ (ℓ + 1) * c * zr / G2 + ν ^ (ℓ + 1) * wr * G1⁻¹ : ℝ) : ℂ) +
      (((-1) ^ (ℓ + 1) * ν ^ (ℓ + 1) * s * zr / G2 + ν ^ (ℓ + 1) * wi * G1⁻¹ : ℝ) : ℂ) * I := by
    rw [hE, hexp, hG1, hG2, hζr, hWr]
    push_cast
    ring
  have hP : coulombf ε ℓ r =
      (-1) ^ (ℓ + 1) * ν ^ (ℓ + 1) * c * zr / G2 + ν ^ (ℓ + 1) * wr * G1⁻¹ := by
    have := congrArg Complex.re hE2
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im] at this
    linarith
  rw [hP, hinv, hζr, hXi]
  push_cast
  field_simp
  ring

/-- For `ε < 0`, `r > 0`, `A(ε,ℓ) ≠ 0` and away from the poles of `Γ(ℓ+1-κ)`, the real part of
the formula 33.14.7 is the right-hand side of DLMF 33.16.11. -/
private lemma coulombhFormula_re_eq_whittaker {ε : ℝ} (hε : ε < 0) (ℓ : ℕ) {r : ℝ} (hr : 0 < r)
    (hA : coulombAProd ε ℓ ≠ 0) (hp : ∀ m : ℕ, (ℓ : ℂ) + 1 - coulombKappa ε r ≠ -(m : ℂ)) :
    (coulombhFormula ε ℓ r).re = (-1) ^ ℓ * ((-ε) ^ (-(1 / 2 : ℝ))) ^ (ℓ + 1) *
      coulombAProd ε ℓ * (Real.sin (π * (-ε) ^ (-(1 / 2 : ℝ))) *
        (coulombZeta ℓ ((-ε) ^ (-(1 / 2 : ℝ))) r).re / Real.Gamma (ℓ + 1 + (-ε) ^ (-(1 / 2 : ℝ))) +
        Real.cos (π * (-ε) ^ (-(1 / 2 : ℝ))) * Real.Gamma ((-ε) ^ (-(1 / 2 : ℝ)) - ℓ) *
          coulombXi ℓ ((-ε) ^ (-(1 / 2 : ℝ))) r / π) := by
  set ν := (-ε) ^ (-(1 / 2 : ℝ)) with hνdef
  have hν : 0 < ν := neg_rpow_neg_half_pos hε
  have hκ : coulombKappa ε r = (ν : ℂ) := coulombKappa_of_neg_of_pos hε hr
  have hνA : ∀ m : ℕ, (ν : ℂ) - ℓ ≠ -(m : ℂ) := neg_rpow_neg_half_sub_ne_neg_nat hε hA
  have hx : 0 < 2 * r / ν := by positivity
  set x := 2 * r / ν with hx_def
  have hζ := conj_coulombZeta ℓ (ν := ν) (r := r) hx
  have hxc : (2 * (r : ℂ) / (ν : ℂ)) = (x : ℂ) := by rw [hx_def]; push_cast; ring
  have hν0 : (ν : ℂ) ≠ 0 := by exact_mod_cast hν.ne'
  have hS : coulombSFactor ε r = 2 * Real.cos (π * ν) := by
    simp [coulombSFactor, hε, hr, abs_of_neg hε, hνdef]
  have hpa : ∀ m : ℕ, (ℓ : ℂ) + 1 - ν ≠ -(m : ℂ) := by rw [← hκ]; exact hp
  have hGa : Gamma ((ℓ : ℂ) + 1 - ν) ≠ 0 := Complex.Gamma_ne_zero hpa
  have hGb : Gamma ((ℓ : ℂ) + 1 + ν) ≠ 0 := by
    refine Complex.Gamma_ne_zero fun m h => ?_
    have := congrArg Complex.re h
    simp at this
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m), (Nat.cast_nonneg ℓ : (0 : ℝ) ≤ ℓ)]
  set W := exp (I * π * (ν : ℂ)) * (exp (-(-(2 * (r : ℂ) / (ν : ℂ))) / 2) *
          (-(2 * (r : ℂ) / (ν : ℂ))) ^ (ℓ + 1) *
          kummerU (ℓ + 1 + (ν : ℂ)) (2 * ℓ + 2) (-(2 * (r : ℂ) / (ν : ℂ))))
    with hW
  have hE : coulombhFormula ε ℓ r =
      (Gamma ((ℓ : ℂ) + 1 - ν) * coulombZeta ℓ ν r + (-1) ^ ℓ * (Real.cos (π * ν) : ℂ) *
        (Gamma ((ℓ : ℂ) + 1 - ν) * exp (-((ℓ : ℂ) + 1 - ν) * π * I) * coulombZeta ℓ ν r +
          Gamma ((ℓ : ℂ) + 1 + ν) * W)) / (π * (ν : ℂ) ^ ℓ) := by
    unfold coulombhFormula coulombhKappa
    rw [hκ, hS]
    unfold coulombZeta
    rw [hW, hxc, kummerM_two_mul_add_two_eq_kummerU_connection ℓ _ hx]
    have he3 : exp ((2 * (ℓ : ℂ) + 2 - (ℓ + 1 - (ν : ℂ))) * π * I) =
        (-1) ^ (ℓ + 1) * exp (I * π * (ν : ℂ)) := by
      rw [← exp_nat_mul_pi_mul_I, ← Complex.exp_add]; congr 1; push_cast; ring
    have he2 : exp (-(x : ℂ) / 2) * exp (x : ℂ) = exp (-(-(x : ℂ)) / 2) := by
      rw [← Complex.exp_add]; congr 1; ring
    have hf : ((2 * ℓ + 1)! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    rw [he3, show (2 * (ℓ : ℂ) + 2 - (ℓ + 1 - (ν : ℂ))) = ℓ + 1 + ν by ring,
      neg_pow (x : ℂ), ← he2]
    push_cast
    field_simp
  have hXi : coulombXi ℓ ν r = W.re := rfl
  set ζ := coulombZeta ℓ ν r with hζdef
  have hζr : ζ = (ζ.re : ℂ) := (Complex.conj_eq_iff_re.mp hζ).symm
  have hWr : W = (W.re : ℂ) + (W.im : ℂ) * I := (Complex.re_add_im W).symm
  set zr := ζ.re
  set wr := W.re
  set wi := W.im
  set c := Real.cos (π * ν)
  set s := Real.sin (π * ν)
  have hexp : exp (-((ℓ : ℂ) + 1 - ν) * π * I) = (-1) ^ (ℓ + 1) * ((c : ℂ) + (s : ℂ) * I) := by
    have h2 : exp (((2 * (ℓ + 1) : ℕ) : ℂ) * π * I) = 1 := by
      rw [exp_nat_mul_pi_mul_I, pow_mul]; simp
    have h3 : exp (((π * ν : ℝ) : ℂ) * I) = (c : ℂ) + (s : ℂ) * I := by
      rw [Complex.exp_mul_I]; simp only [c, s]; push_cast; ring
    rw [show -((ℓ : ℂ) + 1 - ν) * π * I = ((ℓ + 1 : ℕ) : ℂ) * π * I +
        ((π * ν : ℝ) : ℂ) * I - ((2 * (ℓ + 1) : ℕ) : ℂ) * π * I by push_cast; ring,
      Complex.exp_sub, Complex.exp_add, h2, h3, exp_nat_mul_pi_mul_I, div_one]
  have hG1 : Gamma ((ℓ : ℂ) + 1 - ν) = (Real.Gamma (ℓ + 1 - ν) : ℂ) := by
    rw [← Complex.Gamma_ofReal]; push_cast; ring_nf
  have hG2 : Gamma ((ℓ : ℂ) + 1 + ν) = (Real.Gamma (ℓ + 1 + ν) : ℂ) := by
    rw [← Complex.Gamma_ofReal]; push_cast; ring_nf
  have hGr : Real.Gamma (ν - ℓ) ≠ 0 := by
    have := Complex.Gamma_ne_zero hνA
    rw [show (ν : ℂ) - ℓ = ((ν - ℓ : ℝ) : ℂ) by push_cast; ring, Complex.Gamma_ofReal] at this
    exact_mod_cast this
  have hinv : (Real.Gamma (ℓ + 1 - ν))⁻¹ = (-1) ^ ℓ * s * Real.Gamma (ν - ℓ) / π := by
    rw [show (ℓ : ℝ) + 1 - ν = 1 - (ν - ℓ) by ring, inv_Gamma_one_sub_real hGr,
      sin_pi_mul_sub_nat]
  set G1 := Real.Gamma (ℓ + 1 - ν)
  set G2 := Real.Gamma (ℓ + 1 + ν)
  have hG1ne : G1 ≠ 0 := by rw [hG1] at hGa; exact_mod_cast hGa
  have hG2ne : G2 ≠ 0 := by rw [hG2] at hGb; exact_mod_cast hGb
  have hm1 : ((-1 : ℝ) ^ ℓ) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  have hE2 : coulombhFormula ε ℓ r =
      (((G1 * zr * (1 - c ^ 2) + (-1) ^ ℓ * c * G2 * wr) / (π * ν ^ ℓ) : ℝ) : ℂ) +
      (((-(G1 * zr * c * s) + (-1) ^ ℓ * c * G2 * wi) / (π * ν ^ ℓ) : ℝ) : ℂ) * I := by
    rw [hE, hexp, hG1, hG2, hζr, hWr]
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hm1c : ((-1 : ℂ) ^ ℓ) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
    push_cast
    field_simp
    linear_combination (-(↑G1 * ↑zr * ↑c * (↑c + ↑s * I))) * hm1c
  have hP : (coulombhFormula ε ℓ r).re =
      (G1 * zr * (1 - c ^ 2) + (-1) ^ ℓ * c * G2 * wr) / (π * ν ^ ℓ) := by
    have := congrArg Complex.re hE2
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im] at this
    linarith
  -- `A = G2 / (Γ(ν-ℓ) ν^{2ℓ+1})`
  have hκ1 : coulombKappa ε 1 = (ν : ℂ) := coulombKappa_of_neg_of_pos hε one_pos
  have hAG := coulombAProd_eq_Gamma hε.ne ℓ 1 (by rw [hκ1]; exact hνA)
  rw [hκ1] at hAG
  have hAr : coulombAProd ε ℓ * Real.Gamma (ν - ℓ) * ν ^ (2 * ℓ + 1) = G2 := by
    have hG3 : Gamma ((ν : ℂ) - ℓ) = (Real.Gamma (ν - ℓ) : ℂ) := by
      rw [← Complex.Gamma_ofReal]; push_cast; ring_nf
    have hG4 : Gamma (1 + (ℓ : ℂ) + ν) = (G2 : ℂ) := by
      rw [← hG2]; ring_nf
    rw [hG3, hG4, zpow_neg, show (2 * (ℓ : ℤ) + 1) = ((2 * ℓ + 1 : ℕ) : ℤ) by push_cast; ring,
      zpow_natCast] at hAG
    have hGrc : (Real.Gamma (ν - ℓ) : ℂ) ≠ 0 := by exact_mod_cast hGr
    have : ((coulombAProd ε ℓ * Real.Gamma (ν - ℓ) * ν ^ (2 * ℓ + 1) : ℝ) : ℂ) = (G2 : ℂ) := by
      push_cast
      rw [hAG]
      field_simp
    exact_mod_cast this
  rw [hP, ← hXi]
  have hs2 : 1 - c ^ 2 = s ^ 2 := by
    have := Real.sin_sq_add_cos_sq (π * ν); simp only [c, s]; linarith
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have hG1s : G1 * s * Real.Gamma (ν - ℓ) = π * (-1) ^ ℓ := by
    have h1 : G1 * ((-1) ^ ℓ * s * Real.Gamma (ν - ℓ) / π) = 1 := by
      rw [← hinv]; exact mul_inv_cancel₀ hG1ne
    rw [mul_div_assoc', div_eq_one_iff_eq hπ] at h1
    linear_combination (-1) ^ ℓ * h1 - G1 * s * Real.Gamma (ν - ℓ) * hm1
  rw [hs2, ← hAr]
  have hνr : ν ≠ 0 := hν.ne'
  field_simp
  linear_combination ν ^ (2 * ℓ + 1) * zr * s * hG1s

/-- Tricomi's function at an integer second parameter is jointly continuous in `a` and `x > 0`
along the negative real axis `z = -x` (principal branch, `ph z = π`). -/
private lemma continuousAt_kummerU_intCast_neg_ofReal (n : ℤ) (a : ℂ) {x : ℝ} (hx : 0 < x) :
    ContinuousAt (fun p : ℂ × ℝ => kummerU p.1 n (-(p.2 : ℂ))) (a, x) := by
  set S : ℂ → ℂ := fun c => sin (π * c) with hS
  have hz : ∀ t : ℝ, 0 < t → -(t : ℂ) ≠ 0 := fun t ht =>
    neg_ne_zero.mpr (ofReal_ne_zero.mpr ht.ne')
  have hev : (fun p : ℂ × ℝ => π * dslope (fun c => tricomiD p.1 c (-(p.2 : ℂ))) n n /
      dslope S n n) =ᶠ[𝓝 (a, x)] fun p => kummerU p.1 n (-(p.2 : ℂ)) := by
    filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds
      (show (a, x) ∈ {p : ℂ × ℝ | 0 < p.2} from hx)] with p hp
    exact (kummerU_eq_dslope p.1 (hz p.2 hp) n (by simp)).symm
  refine ContinuousAt.congr ?_ hev
  have hX : IsOpen (univ ×ˢ Ioi 0 : Set (ℂ × ℝ)) := isOpen_univ.prod isOpen_Ioi
  have hpow : ∀ q : (ℂ × ℝ) × ℂ, 0 < q.1.2 →
      ContinuousAt (fun q : (ℂ × ℝ) × ℂ => (-(q.1.2 : ℂ)) ^ (1 - q.2)) q := by
    intro q hq
    have e : (fun q : (ℂ × ℝ) × ℂ => (q.1.2 : ℂ) ^ (1 - q.2) * exp (π * I * (1 - q.2))) =ᶠ[𝓝 q]
        fun q => (-(q.1.2 : ℂ)) ^ (1 - q.2) := by
      filter_upwards [(isOpen_lt continuous_const (by fun_prop :
        Continuous fun q : (ℂ × ℝ) × ℂ => q.1.2)).mem_nhds
        (show q ∈ {q : (ℂ × ℝ) × ℂ | 0 < q.1.2} from hq)] with q' hq'
      have hq'' : (0 : ℝ) < q'.1.2 := hq'
      have h := ofReal_cpow_of_nonpos (x := -q'.1.2) (by linarith) (1 - q'.2)
      push_cast at h
      rw [h, neg_neg]
    refine ContinuousAt.congr ?_ e
    have hs : ((q.1.2 : ℝ) : ℂ) ∈ slitPlane := Complex.ofReal_mem_slitPlane.mpr hq
    exact (ContinuousAt.cpow (f := fun q : (ℂ × ℝ) × ℂ => ((q.1.2 : ℝ) : ℂ))
      (g := fun q : (ℂ × ℝ) × ℂ => 1 - q.2) (by fun_prop) (by fun_prop) hs).mul (by fun_prop)
  have hcont : ContinuousOn (fun q : (ℂ × ℝ) × ℂ => tricomiD q.1.1 q.2 (-(q.1.2 : ℂ)))
      ((univ ×ˢ Ioi 0) ×ˢ univ) := by
    rintro q ⟨⟨-, hq⟩, -⟩
    have hM := continuous_regularizedConfluent
    have hG := differentiable_one_div_Gamma.continuous
    have h1 : Continuous fun q : (ℂ × ℝ) × ℂ => regularizedHGFun {q.1.1} {q.2} (-(q.1.2 : ℂ)) :=
      hM.comp (f := fun q : (ℂ × ℝ) × ℂ => (q.1.1, q.2, -(q.1.2 : ℂ))) (by fun_prop)
    have h2 : Continuous fun q : (ℂ × ℝ) × ℂ =>
        regularizedHGFun {q.1.1 - q.2 + 1} {2 - q.2} (-(q.1.2 : ℂ)) :=
      hM.comp (f := fun q : (ℂ × ℝ) × ℂ => (q.1.1 - q.2 + 1, 2 - q.2, -(q.1.2 : ℂ)))
        (by fun_prop)
    have h3 : Continuous fun q : (ℂ × ℝ) × ℂ => (Gamma (q.1.1 - q.2 + 1))⁻¹ :=
      (hG.comp (by fun_prop : Continuous fun q : (ℂ × ℝ) × ℂ => q.1.1 - q.2 + 1)).congr
        fun q => by simp
    have h4 : Continuous fun q : (ℂ × ℝ) × ℂ => (Gamma q.1.1)⁻¹ :=
      (hG.comp (by fun_prop : Continuous fun q : (ℂ × ℝ) × ℂ => q.1.1)).congr fun q => by simp
    unfold tricomiD
    exact ((h1.continuousAt.mul h3.continuousAt).sub
      (((hpow q hq).mul h2.continuousAt).mul h4.continuousAt)).continuousWithinAt
  have hnum := continuousOn_dslope_param
    (f := fun p : ℂ × ℝ => fun c => tricomiD p.1 c (-(p.2 : ℂ))) hX hcont
    (fun p hp => differentiable_tricomiD p.1 (hz p.2 hp.2)) n
  have hA : ContinuousAt (fun p : ℂ × ℝ => dslope (fun c => tricomiD p.1 c (-(p.2 : ℂ))) n n)
      (a, x) := by
    have := hnum.continuousAt ((hX.prod isOpen_univ).mem_nhds
      (⟨⟨mem_univ _, hx⟩, mem_univ _⟩ : ((a, x), (n : ℂ)) ∈ (univ ×ˢ Ioi 0) ×ˢ univ))
    exact ContinuousAt.comp (f := fun p : ℂ × ℝ => (p, (n : ℂ))) this (by fun_prop)
  have hSn : dslope S n n ≠ 0 := by
    have hSd' : HasDerivAt S (cos (π * n) * π) n := by
      have := ((hasDerivAt_id (n : ℂ)).const_mul (π : ℂ)).csin
      simpa [hS] using this
    have hS0 : S n = 0 := by
      simp only [hS]
      rw [mul_comm]; exact Complex.sin_int_mul_pi n
    have hcos : cos (π * n) ≠ 0 := by
      intro h
      have := Complex.cos_sq_add_sin_sq (π * (n : ℂ))
      simp only [hS] at hS0
      rw [h, hS0] at this
      norm_num at this
    rw [dslope_same, hSd'.deriv]
    exact mul_ne_zero hcos (ofReal_ne_zero.mpr Real.pi_ne_zero)
  exact (continuousAt_const.mul hA).div continuousAt_const hSn

/-- **DLMF 33.16.11**: for `ε < 0`, `r > 0`, `A(ε,ℓ) ≠ 0`,
`h(ε,ℓ;r) = (-1)^ℓ ν^{ℓ+1} A(ε,ℓ) (sin(πν) ζ_ℓ(ν,r)/Γ(ℓ+1+ν) + cos(πν) Γ(ν-ℓ) ξ_ℓ(ν,r)/π)`. -/
@[dlmf 33.16.E11]
theorem coulombh_eq_whittaker_pos {ε : ℝ} (hε : ε < 0) (ℓ : ℕ) {r : ℝ} (hr : 0 < r)
    (hA : coulombAProd ε ℓ ≠ 0) :
    let ν := (-ε) ^ (-(1 / 2 : ℝ))
    (coulombh ε ℓ r : ℂ) = (-1) ^ ℓ * (ν : ℂ) ^ (ℓ + 1) * coulombAProd ε ℓ *
      ((Real.sin (π * ν) : ℂ) * coulombZeta ℓ ν r / (Real.Gamma (ℓ + 1 + ν) : ℂ) +
        (Real.cos (π * ν) * Real.Gamma (ν - ℓ) * coulombXi ℓ ν r / π : ℝ)) := by
  intro ν
  set νf : ℝ → ℝ := fun e => (-e) ^ (-(1 / 2 : ℝ)) with hνf
  set G : ℝ → ℝ := fun e => (-1) ^ ℓ * (νf e) ^ (ℓ + 1) * coulombAProd e ℓ *
    (Real.sin (π * νf e) * (coulombZeta ℓ (νf e) r).re / Real.Gamma (ℓ + 1 + νf e) +
      Real.cos (π * νf e) * Real.Gamma (νf e - ℓ) * coulombXi ℓ (νf e) r / π) with hG
  have hν : 0 < ν := neg_rpow_neg_half_pos hε
  have hζ := conj_coulombZeta ℓ (ν := ν) (r := r) (by positivity)
  have hζr : coulombZeta ℓ ν r = ((coulombZeta ℓ ν r).re : ℂ) :=
    (Complex.conj_eq_iff_re.mp hζ).symm
  suffices h : coulombh ε ℓ r = G ε by
    rw [h, hζr]
    simp only [hG, hνf]
    push_cast
    ring
  have hκ : ∀ e : ℝ, e < 0 → coulombKappa e r = (νf e : ℂ) := fun e he =>
    coulombKappa_of_neg_of_pos he hr
  by_cases hpole : ∃ m : ℕ, (ℓ : ℂ) + 1 - coulombKappa ε r = -(m : ℂ)
  · obtain ⟨m₀, hm₀⟩ := hpole
    have hpole' : ε = 0 ∨ ∃ m : ℕ, (ℓ : ℂ) + 1 - coulombKappa ε r = -(m : ℂ) := Or.inr ⟨m₀, hm₀⟩
    unfold coulombh
    simp only [hpole', ↓reduceIte]
    have hνc : ContinuousAt νf ε :=
      continuousAt_neg.rpow_const (Or.inl (neg_ne_zero.mpr hε.ne))
    have hAc : ContinuousAt (fun e => coulombAProd e ℓ) ε := by
      unfold coulombAProd
      fun_prop
    have hνpos : 0 < νf ε := hν
    have hνA : ∀ m : ℕ, νf ε - ℓ ≠ -(m : ℝ) := fun m h =>
      neg_rpow_neg_half_sub_ne_neg_nat hε hA m (by exact_mod_cast h)
    -- continuity of the pieces
    have hΓ1 : ContinuousAt (fun e => Real.Gamma (ℓ + 1 + νf e)) ε := by
      refine ContinuousAt.comp (g := Real.Gamma) ?_ (by fun_prop)
      refine (Real.differentiableAt_Gamma fun m h => ?_).continuousAt
      linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m), (Nat.cast_nonneg ℓ : (0 : ℝ) ≤ ℓ)]
    have hΓ1ne : Real.Gamma (ℓ + 1 + νf ε) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
    have hΓ2 : ContinuousAt (fun e => Real.Gamma (νf e - ℓ)) ε :=
      ContinuousAt.comp (g := Real.Gamma) (Real.differentiableAt_Gamma hνA).continuousAt
        (by fun_prop)
    have hνc' : ContinuousAt (fun e => ((νf e : ℝ) : ℂ)) ε :=
      continuous_ofReal.continuousAt.comp hνc
    have hν0 : ((νf ε : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hν.ne'
    have hζc : ContinuousAt (fun e => (coulombZeta ℓ (νf e) r).re) ε := by
      refine continuous_re.continuousAt.comp ?_
      unfold coulombZeta
      have hx : ((2 * r / νf ε : ℝ) : ℂ) ∈ slitPlane :=
        Complex.ofReal_mem_slitPlane.mpr (by positivity)
      have hz : ContinuousAt (fun e => 2 * (r : ℂ) / (νf e : ℂ)) ε :=
        continuousAt_const.div hνc' hν0
      have hU : ContinuousAt (fun e => kummerU ((ℓ : ℂ) + 1 - νf e) (2 * ℓ + 2)
          (2 * (r : ℂ) / (νf e : ℂ))) ε := by
        refine ContinuousAt.comp (g := fun q : ℂ × ℂ × ℂ => kummerU q.1 q.2.1 q.2.2)
          (f := fun e => ((ℓ : ℂ) + 1 - νf e, (2 * ℓ + 2 : ℂ), 2 * (r : ℂ) / (νf e : ℂ))) ?_
          ((continuousAt_const.sub hνc').prodMk (continuousAt_const.prodMk hz))
        refine continuousAt_kummerU _ _ ?_
        convert hx using 1
        push_cast; ring
      exact ((hz.neg.div_const 2).cexp.mul (hz.pow _)).mul hU
    have hξc : ContinuousAt (fun e => coulombXi ℓ (νf e) r) ε := by
      refine continuous_re.continuousAt.comp ?_
      have hz : ContinuousAt (fun e => 2 * (r : ℂ) / (νf e : ℂ)) ε :=
        continuousAt_const.div hνc' hν0
      have hU : ContinuousAt (fun e => kummerU ((ℓ : ℂ) + 1 + νf e) (2 * ℓ + 2)
          (-(2 * (r : ℂ) / (νf e : ℂ)))) ε := by
        have h0 := continuousAt_kummerU_intCast_neg_ofReal (2 * ℓ + 2) ((ℓ : ℂ) + 1 + νf ε)
          (x := 2 * r / νf ε) (by positivity)
        have h1 := ContinuousAt.comp (g := fun p : ℂ × ℝ => kummerU p.1 ((2 * ℓ + 2 : ℤ) : ℂ)
          (-(p.2 : ℂ))) (f := fun e => ((ℓ : ℂ) + 1 + νf e, 2 * r / νf e)) h0
          ((continuousAt_const.add hνc').prodMk (continuousAt_const.div hνc hν.ne'))
        refine h1.congr (Eventually.of_forall fun e => ?_)
        simp only [Function.comp_apply]
        push_cast
        ring_nf
      exact (((continuousAt_const.mul hνc').cexp).mul
        (((hz.neg.neg.div_const 2).cexp.mul (hz.neg.pow _)).mul hU))
    have hGc : ContinuousAt G ε := by
      simp only [hG]
      refine ((continuousAt_const.mul (hνc.pow _)).mul hAc).mul ?_
      have hπν : ContinuousAt (fun e => π * νf e) ε := continuousAt_const.mul hνc
      refine (((Real.continuous_sin.continuousAt.comp hπν).mul hζc).div hΓ1 hΓ1ne).add ?_
      exact (((Real.continuous_cos.continuousAt.comp hπν).mul hΓ2).mul hξc).div_const _
    have hm₀' : νf ε = ℓ + 1 + m₀ := by
      rw [hκ ε hε] at hm₀
      have := congrArg Complex.re hm₀
      simp at this
      linarith
    have hev : ∀ᶠ e in 𝓝[≠] ε, (coulombhFormula e ℓ r).re = G e := by
      have h1 : ∀ᶠ e in 𝓝 ε, e < 0 := eventually_lt_nhds hε
      have h2 : ∀ᶠ e in 𝓝 ε, coulombAProd e ℓ ≠ 0 := hAc.eventually_ne hA
      have h3 : ∀ᶠ e in 𝓝 ε, |νf e - νf ε| < 1 := by
        have := hνc.tendsto
        rw [Metric.tendsto_nhds] at this
        simpa [Real.dist_eq] using this 1 one_pos
      filter_upwards [nhdsWithin_le_nhds (h1.and (h2.and h3)), self_mem_nhdsWithin] with e
        ⟨he, hAe, hνe⟩ hne
      refine coulombhFormula_re_eq_whittaker he ℓ hr hAe fun m hm => hne ?_
      rw [hκ e he] at hm
      have hm' : νf e = ℓ + 1 + m := by
        have := congrArg Complex.re hm
        simp at this
        linarith
      rw [hm', hm₀', abs_lt] at hνe
      have hmm : m = m₀ := by
        have h1 : (m : ℝ) < m₀ + 1 := by linarith
        have h2 : (m₀ : ℝ) < m + 1 := by linarith
        have h1' : m < m₀ + 1 := by exact_mod_cast h1
        have h2' : m₀ < m + 1 := by exact_mod_cast h2
        omega
      have hνeq : νf e = νf ε := by rw [hm', hm₀', hmm]
      rw [eq_neg_one_div_neg_rpow_neg_half_sq he, eq_neg_one_div_neg_rpow_neg_half_sq hε]
      exact congrArg (fun t => -1 / t ^ 2) hνeq
    exact ((hGc.tendsto.mono_left nhdsWithin_le_nhds).congr'
      (hev.mono fun e h => h.symm)).limUnder_eq
  · have hnp : ¬ (ε = 0 ∨ ∃ m : ℕ, (ℓ : ℂ) + 1 - coulombKappa ε r = -(m : ℂ)) := by
      rintro (h | h)
      · exact hε.ne h
      · exact hpole h
    unfold coulombh
    simp only [hnp, ↓reduceIte]
    exact coulombhFormula_re_eq_whittaker hε ℓ hr hA fun m hm => hpole ⟨m, hm⟩

/-- **DLMF 33.16.12**: for `ε < 0`, `r < 0`, `A(ε,ℓ) ≠ 0`,
`f(ε,ℓ;r) = (-1)^ℓ ν^{ℓ+1}/π (-π ξ_ℓ(-ν,r)/Γ(ℓ+1+ν) + sin(πν) cos(πν) Γ(ν-ℓ) ζ_ℓ(-ν,r))`. -/
@[dlmf 33.16.E12]
theorem coulombf_eq_whittaker_neg {ε : ℝ} (hε : ε < 0) (ℓ : ℕ) {r : ℝ} (hr : r < 0)
    (hA : coulombAProd ε ℓ ≠ 0) :
    let ν := (-ε) ^ (-(1 / 2 : ℝ))
    (coulombf ε ℓ r : ℂ) = (-1) ^ ℓ * (ν : ℂ) ^ (ℓ + 1) / π *
      ((-(π * coulombXi ℓ (-ν) r / Real.Gamma (ℓ + 1 + ν)) : ℝ) +
        (Real.sin (π * ν) * Real.cos (π * ν) * Real.Gamma (ν - ℓ) : ℝ) * coulombZeta ℓ (-ν) r) := by
  intro ν
  have hν : 0 < ν := neg_rpow_neg_half_pos hε
  have hκ : coulombKappa ε r = -(ν : ℂ) := coulombKappa_of_neg_of_nonpos hε hr.le
  have hνA : ∀ m : ℕ, (ν : ℂ) - ℓ ≠ -(m : ℂ) := neg_rpow_neg_half_sub_ne_neg_nat hε hA
  have hx : 0 < 2 * r / (-ν) := div_pos_of_neg_of_neg (by linarith) (by linarith)
  set x := 2 * r / (-ν) with hx_def
  have hζ := conj_coulombZeta ℓ (ν := -ν) (r := r) hx
  have hxc : (2 * (r : ℂ) / -(ν : ℂ)) = (x : ℂ) := by rw [hx_def]; push_cast; ring
  have hν0 : (ν : ℂ) ≠ 0 := by exact_mod_cast hν.ne'
  -- the complex form
  have hE : (coulombf ε ℓ r : ℂ) =
      (-(ν : ℂ)) ^ (ℓ + 1) * exp (-((ℓ : ℂ) + 1 + ν) * π * I) / Gamma (ℓ + 1 - ν) *
        coulombZeta ℓ (-ν) r +
      (-(ν : ℂ)) ^ (ℓ + 1) / Gamma (ℓ + 1 + ν) *
        (exp (I * π * ((-ν : ℝ) : ℂ)) * (exp (-(-(2 * (r : ℂ) / ((-ν : ℝ) : ℂ))) / 2) *
          (-(2 * (r : ℂ) / ((-ν : ℝ) : ℂ))) ^ (ℓ + 1) *
          kummerU (ℓ + 1 + ((-ν : ℝ) : ℂ)) (2 * ℓ + 2) (-(2 * (r : ℂ) / ((-ν : ℝ) : ℂ))))) := by
    rw [ofReal_coulombf hε.ne, hκ]
    unfold coulombfKummer coulombZeta
    rw [hxc, kummerM_two_mul_add_two_eq_kummerU_connection ℓ _ hx]
    push_cast
    simp only [hxc]
    have hr2 : (2 * (r : ℂ)) = -(ν : ℂ) * x := by rw [← hxc]; field_simp
    have he1 : exp (-(r : ℂ) / -(ν : ℂ)) = exp (-(x : ℂ) / 2) := by
      congr 1; rw [← hxc]; field_simp
    rw [hr2, he1]
    have he3 : exp ((2 * (ℓ : ℂ) + 2 - (ℓ + 1 - -(ν : ℂ))) * π * I) =
        (-1) ^ (ℓ + 1) * exp (I * π * (-(ν : ℂ))) := by
      rw [← exp_nat_mul_pi_mul_I, ← Complex.exp_add]; congr 1; push_cast; ring
    have he2 : exp (-(x : ℂ) / 2) * exp (x : ℂ) = exp (-(-(x : ℂ)) / 2) := by
      rw [← Complex.exp_add]; congr 1; ring
    have hf : ((2 * ℓ + 1)! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    rw [he3, show (2 * (ℓ : ℂ) + 2 - (ℓ + 1 - -(ν : ℂ))) = ℓ + 1 + -(ν : ℂ) by ring,
      show ((ℓ : ℂ) + 1 + -(ν : ℂ)) = ℓ + 1 - ν by ring,
      show ((ℓ : ℂ) + 1 - -(ν : ℂ)) = ℓ + 1 + ν by ring,
      show (-((ℓ : ℂ) + 1 + ν)) = -(ℓ + 1 + ν) from rfl, mul_pow, neg_pow (x : ℂ), ← he2]
    field_simp
  set W := exp (I * π * ((-ν : ℝ) : ℂ)) * (exp (-(-(2 * (r : ℂ) / ((-ν : ℝ) : ℂ))) / 2) *
          (-(2 * (r : ℂ) / ((-ν : ℝ) : ℂ))) ^ (ℓ + 1) *
          kummerU (ℓ + 1 + ((-ν : ℝ) : ℂ)) (2 * ℓ + 2) (-(2 * (r : ℂ) / ((-ν : ℝ) : ℂ))))
    with hW
  have hXi : coulombXi ℓ (-ν) r = W.re := rfl
  set ζ := coulombZeta ℓ (-ν) r with hζdef
  have hζr : ζ = (ζ.re : ℂ) := (Complex.conj_eq_iff_re.mp hζ).symm
  have hWr : W = (W.re : ℂ) + (W.im : ℂ) * I := (Complex.re_add_im W).symm
  set zr := ζ.re
  set wr := W.re
  set wi := W.im
  set c := Real.cos (π * ν)
  set s := Real.sin (π * ν)
  have hexp : exp (-((ℓ : ℂ) + 1 + ν) * π * I) = (-1) ^ (ℓ + 1) * ((c : ℂ) - (s : ℂ) * I) := by
    have h2 : exp (((2 * (ℓ + 1) : ℕ) : ℂ) * π * I) = 1 := by
      rw [exp_nat_mul_pi_mul_I, pow_mul]; simp
    have h3 : exp (((-(π * ν) : ℝ) : ℂ) * I) = (c : ℂ) - (s : ℂ) * I := by
      rw [Complex.exp_mul_I]; simp only [c, s]; push_cast
      rw [Complex.cos_neg, Complex.sin_neg]; ring
    rw [show -((ℓ : ℂ) + 1 + ν) * π * I = ((ℓ + 1 : ℕ) : ℂ) * π * I +
        ((-(π * ν) : ℝ) : ℂ) * I - ((2 * (ℓ + 1) : ℕ) : ℂ) * π * I by push_cast; ring,
      Complex.exp_sub, Complex.exp_add, h2, h3, exp_nat_mul_pi_mul_I, div_one]
  have hG1 : Gamma ((ℓ : ℂ) + 1 - ν) = (Real.Gamma (ℓ + 1 - ν) : ℂ) := by
    rw [← Complex.Gamma_ofReal]; push_cast; ring_nf
  have hG2 : Gamma ((ℓ : ℂ) + 1 + ν) = (Real.Gamma (ℓ + 1 + ν) : ℂ) := by
    rw [← Complex.Gamma_ofReal]; push_cast; ring_nf
  have hGr : Real.Gamma (ν - ℓ) ≠ 0 := by
    have := Complex.Gamma_ne_zero hνA
    rw [show (ν : ℂ) - ℓ = ((ν - ℓ : ℝ) : ℂ) by push_cast; ring, Complex.Gamma_ofReal] at this
    exact_mod_cast this
  have hinv : (Real.Gamma (ℓ + 1 - ν))⁻¹ = (-1) ^ ℓ * s * Real.Gamma (ν - ℓ) / π := by
    rw [show (ℓ : ℝ) + 1 - ν = 1 - (ν - ℓ) by ring, inv_Gamma_one_sub_real hGr,
      sin_pi_mul_sub_nat]
  set G1 := Real.Gamma (ℓ + 1 - ν)
  set G2 := Real.Gamma (ℓ + 1 + ν)
  have h1 : ((-1 : ℂ) ^ (ℓ + 1)) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  have hE2 : (coulombf ε ℓ r : ℂ) =
      ((ν ^ (ℓ + 1) * c * zr * G1⁻¹ + (-1) ^ (ℓ + 1) * ν ^ (ℓ + 1) * wr / G2 : ℝ) : ℂ) +
      ((-(ν ^ (ℓ + 1) * s * zr * G1⁻¹) + (-1) ^ (ℓ + 1) * ν ^ (ℓ + 1) * wi / G2 : ℝ) : ℂ) *
        I := by
    rw [hE, hexp, hG1, hG2]
    rw [hζr, hWr]
    push_cast
    linear_combination ((ν : ℂ) ^ (ℓ + 1) * ((c : ℂ) - (s : ℂ) * I) * (zr : ℂ) /
      (G1 : ℂ)) * h1
  have hP : coulombf ε ℓ r =
      ν ^ (ℓ + 1) * c * zr * G1⁻¹ + (-1) ^ (ℓ + 1) * ν ^ (ℓ + 1) * wr / G2 := by
    have := congrArg Complex.re hE2
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im] at this
    linarith
  rw [hP, hinv, hζr, hXi]
  push_cast
  field_simp
  ring

/-- **DLMF 33.16.13**: for `ε < 0`, `r < 0`, `A(ε,ℓ) ≠ 0`,
`h(ε,ℓ;r) = (-1)^ℓ ν^{ℓ+1} A(ε,ℓ) Γ(ν-ℓ) ζ_ℓ(-ν,r)/π`. -/
@[dlmf 33.16.E13]
theorem coulombh_eq_whittaker_neg {ε : ℝ} (hε : ε < 0) (ℓ : ℕ) {r : ℝ} (hr : r < 0)
    (hA : coulombAProd ε ℓ ≠ 0) :
    let ν := (-ε) ^ (-(1 / 2 : ℝ))
    (coulombh ε ℓ r : ℂ) = (-1) ^ ℓ * (ν : ℂ) ^ (ℓ + 1) * coulombAProd ε ℓ *
      Real.Gamma (ν - ℓ) * coulombZeta ℓ (-ν) r / π := by
  intro ν
  have hν : 0 < ν := neg_rpow_neg_half_pos hε
  have hκ : coulombKappa ε r = -(ν : ℂ) := coulombKappa_of_neg_of_nonpos hε hr.le
  have hκ1 : coulombKappa ε 1 = (ν : ℂ) := coulombKappa_of_neg_of_pos hε one_pos
  have hνA : ∀ m : ℕ, (ν : ℂ) - ℓ ≠ -(m : ℂ) := neg_rpow_neg_half_sub_ne_neg_nat hε hA
  have hS : coulombSFactor ε r = 0 := by simp [coulombSFactor, hε, not_lt.mpr hr.le]
  have hnp : ¬ (ε = 0 ∨ ∃ m : ℕ, (ℓ : ℂ) + 1 - coulombKappa ε r = -(m : ℂ)) := by
    rintro (h | ⟨m, hm⟩)
    · exact hε.ne h
    · rw [hκ] at hm
      have := congrArg Complex.re hm
      simp at this
      linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m), (Nat.cast_nonneg ℓ : (0 : ℝ) ≤ ℓ)]
  have hζ := conj_coulombZeta ℓ (ν := -ν) (r := r) (by
    rw [div_pos_iff]; right; constructor <;> linarith)
  -- the formula
  have hF : coulombhFormula ε ℓ r = Gamma (ℓ + 1 + ν) / (π * (-(ν : ℂ)) ^ ℓ) *
      coulombZeta ℓ (-ν) r := by
    unfold coulombhFormula coulombhKappa coulombZeta
    rw [hκ, hS]
    push_cast
    ring_nf
  have hG : Gamma (ℓ + 1 + ν) = (Real.Gamma (ℓ + 1 + ν) : ℂ) := by
    rw [← Complex.Gamma_ofReal]; push_cast; ring_nf
  have hreal : conj (coulombhFormula ε ℓ r) = coulombhFormula ε ℓ r := by
    rw [hF, map_mul, hζ, map_div₀, hG, Complex.conj_ofReal, map_mul, map_pow, map_neg,
      Complex.conj_ofReal]
    simp
  have hh : (coulombh ε ℓ r : ℂ) = coulombhFormula ε ℓ r := by
    unfold coulombh
    simp only [hnp, ↓reduceIte]
    exact Complex.conj_eq_iff_re.mp hreal
  rw [hh, hF]
  have hAG := coulombAProd_eq_Gamma hε.ne ℓ 1 (by rw [hκ1]; exact hνA)
  rw [hκ1] at hAG
  rw [hAG, ← Complex.Gamma_ofReal]
  have hG0 : Gamma ((ν : ℂ) - ℓ) ≠ 0 := Complex.Gamma_ne_zero hνA
  have hν0 : (ν : ℂ) ≠ 0 := by exact_mod_cast hν.ne'
  push_cast
  rw [zpow_neg, show (2 * (ℓ : ℤ) + 1) = ((2 * ℓ + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  field_simp
  rw [show (1 : ℂ) + ℓ + ν = ℓ + 1 + ν by ring]
  have h1 : ((-1 : ℂ) ^ ℓ) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  rw [div_eq_iff (pow_ne_zero _ (neg_ne_zero.mpr hν0)), neg_pow]
  linear_combination (-(Gamma (ℓ + 1 + ν) * coulombZeta ℓ (-ν) r * (ν : ℂ) ^ (2 * ℓ + 1))) * h1


/-- **DLMF 33.16.17, corrected**: for `ε < 0`, `r > 0` and `A(ε,ℓ) > 0`, with `K = K(ν,ℓ)`
(33.16.16),
`s(ε,ℓ;r) = (-1)^ℓ (2ν)^{-1/2} (sin(πν) ξ_ℓ(ν,r)/(πK) - cos(πν) ν² K ζ_ℓ(ν,r))` and
`c(ε,ℓ;r) = (-1)^ℓ (2ν)^{-1/2} (cos(πν) ξ_ℓ(ν,r)/(πK) + sin(πν) ν² K ζ_ℓ(ν,r))`.
DLMF prints the prefactor as `(-1)^ℓ/(2ν^{1/2})`, which is too small by `2^{1/2}`. -/
@[dlmf 33.16.E17]
theorem coulombs_coulombc_eq_whittaker_pos {ε : ℝ} (hε : ε < 0) (ℓ : ℕ) {r : ℝ} (hr : 0 < r)
    (hA : 0 < coulombAProd ε ℓ) :
    let ν := (-ε) ^ (-(1 / 2 : ℝ))
    let K := coulombKNorm ν ℓ
    coulombs ε ℓ r = (-1) ^ ℓ / (Real.sqrt (2 * ν) : ℂ) *
        ((Real.sin (π * ν) / (π * K) * coulombXi ℓ ν r : ℝ) -
          (Real.cos (π * ν) * ν ^ 2 * K : ℝ) * coulombZeta ℓ ν r) ∧
      coulombc ε ℓ r = (-1) ^ ℓ / (Real.sqrt (2 * ν) : ℂ) *
        ((Real.cos (π * ν) / (π * K) * coulombXi ℓ ν r : ℝ) +
          (Real.sin (π * ν) * ν ^ 2 * K : ℝ) * coulombZeta ℓ ν r) := by
  intro ν K
  have hν : 0 < ν := neg_rpow_neg_half_pos hε
  have hκ1 : coulombKappa ε 1 = (ν : ℂ) := coulombKappa_of_neg_of_pos hε one_pos
  have hνA := neg_rpow_neg_half_sub_ne_neg_nat hε hA.ne'
  have hAG := coulombAProd_eq_Gamma hε.ne ℓ 1 (by rw [hκ1]; exact hνA)
  rw [hκ1] at hAG
  have hf : (coulombf ε ℓ r : ℂ) = (-1) ^ ℓ * (ν : ℂ) ^ (ℓ + 1) *
      (-(Real.cos (π * ν) : ℂ) * coulombZeta ℓ ν r / (Real.Gamma (ℓ + 1 + ν) : ℂ) +
        (Real.sin (π * ν) * Real.Gamma (ν - ℓ) * coulombXi ℓ ν r / π : ℝ)) :=
    coulombf_eq_whittaker_pos hε ℓ hr hA.ne'
  have hh : (coulombh ε ℓ r : ℂ) = (-1) ^ ℓ * (ν : ℂ) ^ (ℓ + 1) * coulombAProd ε ℓ *
      ((Real.sin (π * ν) : ℂ) * coulombZeta ℓ ν r / (Real.Gamma (ℓ + 1 + ν) : ℂ) +
        (Real.cos (π * ν) * Real.Gamma (ν - ℓ) * coulombXi ℓ ν r / π : ℝ)) :=
    coulombh_eq_whittaker_pos hε ℓ hr hA.ne'
  have hB : coulombBFactor ε ℓ = coulombAProd ε ℓ := by simp [coulombBFactor, not_lt.mpr hε.le]
  have hG1 : Real.Gamma (ℓ + 1 + ν) = Real.Gamma (ν + ℓ + 1) := by ring_nf
  rw [hG1] at hf hh
  have hK : K = (ν ^ 2 * Real.Gamma (ν + ℓ + 1) * Real.Gamma (ν - ℓ)) ^ (-(1 / 2 : ℝ)) := rfl
  set Gp := Real.Gamma (ν + ℓ + 1)
  set Gm := Real.Gamma (ν - ℓ)
  set A := coulombAProd ε ℓ
  have hAr : A = Gp / Gm * (ν ^ (2 * ℓ + 1))⁻¹ := by
    have e1 : Gamma (1 + ℓ + (ν : ℂ)) = (Gp : ℂ) := by
      rw [← Complex.Gamma_ofReal]; push_cast; ring_nf
    have e2 : Gamma ((ν : ℂ) - ℓ) = (Gm : ℂ) := by
      rw [← Complex.Gamma_ofReal]; push_cast; ring_nf
    rw [e1, e2, zpow_neg, show (2 * (ℓ : ℤ) + 1) = ((2 * ℓ + 1 : ℕ) : ℤ) by push_cast; ring,
      zpow_natCast] at hAG
    exact_mod_cast hAG
  have hGp : 0 < Gp := Real.Gamma_pos_of_pos (by positivity)
  have hGm0 : Gm ≠ 0 := by
    intro h0; rw [h0, div_zero, zero_mul] at hAr; exact hA.ne' hAr
  have hGm : 0 < Gm := by
    have : Gm = Gp / (A * ν ^ (2 * ℓ + 1)) := by
      rw [hAr]; field_simp
    rw [this]; positivity
  set t := Real.sqrt ν with ht
  set g := Real.sqrt Gp with hg
  set k := Real.sqrt Gm with hk
  have ht0 : 0 < t := Real.sqrt_pos.mpr hν
  have hg0 : 0 < g := Real.sqrt_pos.mpr hGp
  have hk0 : 0 < k := Real.sqrt_pos.mpr hGm
  have hνt : ν = t ^ 2 := (Real.sq_sqrt hν.le).symm
  have hGpg : Gp = g ^ 2 := (Real.sq_sqrt hGp.le).symm
  have hGmk : Gm = k ^ 2 := (Real.sq_sqrt hGm.le).symm
  have hsA : Real.sqrt A = g / (t ^ (2 * ℓ + 1) * k) := by
    rw [hAr, hνt, hGpg, hGmk, show g ^ 2 / k ^ 2 * ((t ^ 2) ^ (2 * ℓ + 1))⁻¹ =
      (g / (t ^ (2 * ℓ + 1) * k)) ^ 2 by field_simp; ring, Real.sqrt_sq (by positivity)]
  have hK' : K = 1 / (t ^ 2 * g * k) := by
    rw [hK, Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, hνt, hGpg, hGmk,
      show (t ^ 2) ^ 2 * g ^ 2 * k ^ 2 = (t ^ 2 * g * k) ^ 2 by ring,
      Real.sqrt_sq (by positivity), one_div]
  have h2ν : Real.sqrt (2 * ν) = Real.sqrt 2 * t := Real.sqrt_mul (by norm_num) ν
  have h2 : (0 : ℝ) < Real.sqrt 2 := by positivity
  have ct : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
  have cg : (g : ℂ) ≠ 0 := by exact_mod_cast hg0.ne'
  have ck : (k : ℂ) ≠ 0 := by exact_mod_cast hk0.ne'
  have cπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have c2 : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast h2.ne'
  constructor
  · rw [coulombs, hB, Carlson.ofReal_cpow_half (by positivity), hf, Real.sqrt_div' _ (by norm_num),
      hsA, h2ν, hK']
    rw [hνt, hGmk, hGpg]
    push_cast
    field_simp
    ring
  · rw [coulombc, hB, ofReal_cpow_neg_half_eq_inv_sqrt (by positivity), hh, Real.sqrt_mul
        (by norm_num), hsA, h2ν, hK', hAr]
    rw [hνt, hGmk, hGpg]
    push_cast
    field_simp
    ring

/-- **DLMF 33.16.18, corrected**: for `ε < 0`, `r < 0` and `A(ε,ℓ) > 0`,
`s(ε,ℓ;r) = (-1)^{ℓ+1} 2^{-1/2} (ν^{3/2} K ξ_ℓ(-ν,r) - sin(πν) cos(πν) ζ_ℓ(-ν,r)/(π ν^{1/2} K))`
and `c(ε,ℓ;r) = (-1)^ℓ ζ_ℓ(-ν,r) / (π (2ν)^{1/2} K)`. DLMF interchanges `K` and `1/K` in all
three places. -/
@[dlmf 33.16.E18]
theorem coulombs_coulombc_eq_whittaker_neg {ε : ℝ} (hε : ε < 0) (ℓ : ℕ) {r : ℝ} (hr : r < 0)
    (hA : 0 < coulombAProd ε ℓ) :
    let ν := (-ε) ^ (-(1 / 2 : ℝ))
    let K := coulombKNorm ν ℓ
    coulombs ε ℓ r = (-1) ^ (ℓ + 1) / (Real.sqrt 2 : ℂ) *
        ((ν ^ (3 / 2 : ℝ) * K * coulombXi ℓ (-ν) r : ℝ) -
          (Real.sin (π * ν) * Real.cos (π * ν) / (π * Real.sqrt ν * K) : ℝ) *
            coulombZeta ℓ (-ν) r) ∧
      coulombc ε ℓ r = (-1) ^ ℓ / ((π * Real.sqrt (2 * ν) * K : ℝ) : ℂ) *
        coulombZeta ℓ (-ν) r := by
  intro ν K
  have hν : 0 < ν := neg_rpow_neg_half_pos hε
  have hκ1 : coulombKappa ε 1 = (ν : ℂ) := coulombKappa_of_neg_of_pos hε one_pos
  have hνA := neg_rpow_neg_half_sub_ne_neg_nat hε hA.ne'
  have hAG := coulombAProd_eq_Gamma hε.ne ℓ 1 (by rw [hκ1]; exact hνA)
  rw [hκ1] at hAG
  have hf : (coulombf ε ℓ r : ℂ) = (-1) ^ ℓ * (ν : ℂ) ^ (ℓ + 1) / π *
      ((-(π * coulombXi ℓ (-ν) r / Real.Gamma (ℓ + 1 + ν)) : ℝ) +
        (Real.sin (π * ν) * Real.cos (π * ν) * Real.Gamma (ν - ℓ) : ℝ) * coulombZeta ℓ (-ν) r) :=
    coulombf_eq_whittaker_neg hε ℓ hr hA.ne'
  have hh : (coulombh ε ℓ r : ℂ) = (-1) ^ ℓ * (ν : ℂ) ^ (ℓ + 1) * coulombAProd ε ℓ *
      Real.Gamma (ν - ℓ) * coulombZeta ℓ (-ν) r / π :=
    coulombh_eq_whittaker_neg hε ℓ hr hA.ne'
  have hB : coulombBFactor ε ℓ = coulombAProd ε ℓ := by simp [coulombBFactor, not_lt.mpr hε.le]
  have hG1 : Real.Gamma (ℓ + 1 + ν) = Real.Gamma (ν + ℓ + 1) := by ring_nf
  rw [hG1] at hf
  have hK : K = (ν ^ 2 * Real.Gamma (ν + ℓ + 1) * Real.Gamma (ν - ℓ)) ^ (-(1 / 2 : ℝ)) := rfl
  set Gp := Real.Gamma (ν + ℓ + 1)
  set Gm := Real.Gamma (ν - ℓ)
  set A := coulombAProd ε ℓ
  have hAr : A = Gp / Gm * (ν ^ (2 * ℓ + 1))⁻¹ := by
    have e1 : Gamma (1 + ℓ + (ν : ℂ)) = (Gp : ℂ) := by
      rw [← Complex.Gamma_ofReal]; push_cast; ring_nf
    have e2 : Gamma ((ν : ℂ) - ℓ) = (Gm : ℂ) := by
      rw [← Complex.Gamma_ofReal]; push_cast; ring_nf
    rw [e1, e2, zpow_neg, show (2 * (ℓ : ℤ) + 1) = ((2 * ℓ + 1 : ℕ) : ℤ) by push_cast; ring,
      zpow_natCast] at hAG
    exact_mod_cast hAG
  have hGp : 0 < Gp := Real.Gamma_pos_of_pos (by positivity)
  have hGm0 : Gm ≠ 0 := by
    intro h0; rw [h0, div_zero, zero_mul] at hAr; exact hA.ne' hAr
  have hGm : 0 < Gm := by
    have : Gm = Gp / (A * ν ^ (2 * ℓ + 1)) := by
      rw [hAr]; field_simp
    rw [this]; positivity
  set t := Real.sqrt ν with ht
  set g := Real.sqrt Gp with hg
  set k := Real.sqrt Gm with hk
  have ht0 : 0 < t := Real.sqrt_pos.mpr hν
  have hg0 : 0 < g := Real.sqrt_pos.mpr hGp
  have hk0 : 0 < k := Real.sqrt_pos.mpr hGm
  have hνt : ν = t ^ 2 := (Real.sq_sqrt hν.le).symm
  have hGpg : Gp = g ^ 2 := (Real.sq_sqrt hGp.le).symm
  have hGmk : Gm = k ^ 2 := (Real.sq_sqrt hGm.le).symm
  have hsA : Real.sqrt A = g / (t ^ (2 * ℓ + 1) * k) := by
    rw [hAr, hνt, hGpg, hGmk, show g ^ 2 / k ^ 2 * ((t ^ 2) ^ (2 * ℓ + 1))⁻¹ =
      (g / (t ^ (2 * ℓ + 1) * k)) ^ 2 by field_simp; ring, Real.sqrt_sq (by positivity)]
  have hK' : K = 1 / (t ^ 2 * g * k) := by
    rw [hK, Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, hνt, hGpg, hGmk,
      show (t ^ 2) ^ 2 * g ^ 2 * k ^ 2 = (t ^ 2 * g * k) ^ 2 by ring,
      Real.sqrt_sq (by positivity), one_div]
  have h32 : ν ^ (3 / 2 : ℝ) = t ^ 3 := by
    rw [hνt, ← Real.rpow_natCast t 2, ← Real.rpow_mul ht0.le]; norm_num
  have h2ν : Real.sqrt (2 * ν) = Real.sqrt 2 * t := Real.sqrt_mul (by norm_num) ν
  have h2 : (0 : ℝ) < Real.sqrt 2 := by positivity
  have ct : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
  have cg : (g : ℂ) ≠ 0 := by exact_mod_cast hg0.ne'
  have ck : (k : ℂ) ≠ 0 := by exact_mod_cast hk0.ne'
  have cπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have c2 : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast h2.ne'
  constructor
  · rw [coulombs, hB, Carlson.ofReal_cpow_half (by positivity), hf, Real.sqrt_div' _ (by norm_num),
        hsA,
      h32, hK']
    rw [hνt, hGmk, hGpg]
    push_cast
    field_simp
    ring
  · rw [coulombc, hB, ofReal_cpow_neg_half_eq_inv_sqrt (by positivity), hh, Real.sqrt_mul
        (by norm_num), hsA,
      h2ν, hK', hAr]
    rw [hνt, hGmk, hGpg]
    push_cast
    field_simp
    ring

end DLMF.Coulomb
