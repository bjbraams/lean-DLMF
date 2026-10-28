/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Coulomb.Energy.Properties
public import DLMF.Coulomb.RhoEtaProperties

/-!
# Coulomb functions `f`, `h`, `s`, `c`: connection formulas (DLMF §33.16)

`F_ℓ`, `G_ℓ` in terms of `f`, `h` (33.16.1–33.16.2); `f`, `h`, `s`, `c` in terms of `F_ℓ`, `G_ℓ`
for `ε > 0` (33.16.3–33.16.7, 33.16.14–33.16.15) and in terms of Whittaker functions for `ε < 0`
(33.16.8–33.16.13, 33.16.16–33.16.18). We write `τ = ε^{1/2}` (33.16.3) and
`ν = (-ε)^{-1/2}` (33.16.8) inline.

## Source corrections (checked numerically with mpmath, 30–40 digits)

* **33.16.15** (`r < 0`, `ε > 0`) is inconsistent with 33.16.6–33.16.7 and the definitions
  33.14.9–33.14.10 of `s`, `c`: with `B = A/(1 - e^{-2π/τ})` these give
  `s = (-1)^{ℓ+1} e^{π/τ} (πτ)^{-1/2} F_ℓ(1/τ,-τr)` and
  `c = (-1)^ℓ e^{-π/τ} (πτ)^{-1/2} G_ℓ(1/τ,-τr)`; DLMF prints them without the factors
  `(-1)^{ℓ+1} e^{π/τ}` and `(-1)^ℓ e^{-π/τ}`. The corrected forms are acquired.
* **33.16.17**: the prefactor `(-1)^ℓ/(2ν^{1/2})` must be `(-1)^ℓ/(2ν)^{1/2}` (DLMF's `s`, `c` are
  too small by the factor `2^{1/2}`), as follows from 33.16.10–33.16.11 with 33.14.9 and 33.14.12.
* **33.16.18**: `K(ν,ℓ)` and `1/K(ν,ℓ)` are interchanged: from 33.16.12–33.16.13,
  `s = (-1)^{ℓ+1} 2^{-1/2} (ν^{3/2} K ξ_ℓ(-ν,r) - sin(πν) cos(πν) (πν^{1/2}K)^{-1} ζ_ℓ(-ν,r))` and
  `c = (-1)^ℓ (π(2ν)^{1/2} K)^{-1} ζ_ℓ(-ν,r)`.

33.16.1–33.16.2, 33.16.4–33.16.7, 33.16.10–33.16.13 hold as printed.
-/

@[expose] public section

open Complex Filter Set
open scoped Real Nat Topology ComplexConjugate

noncomputable section

namespace DLMF.Coulomb

open DLMF.Confluent

/-! ### `F_ℓ` and `G_ℓ` in terms of `f` and `h` -/

/-- For `η ≠ 0`, `κ(1/η², r) = i|η|`. -/
lemma c33b_kappa_inv_sq {η : ℝ} (hη : η ≠ 0) (r : ℝ) :
    coulombKappa (1 / η ^ 2) r = I * |η| := by
  have hpos : 0 < 1 / η ^ 2 := by positivity
  simp only [coulombKappa, not_lt.mpr hpos.le, ↓reduceIte]
  congr 2
  rw [Real.rpow_neg hpos.le, ← Real.sqrt_eq_rpow, one_div, Real.sqrt_inv, inv_inv,
    Real.sqrt_sq_eq_abs]

/-- At `κ = iη`, the Kummer form of `f(ε,ℓ;r)` at `r = -ηρ` is `(-2η)^{ℓ+1}/(2ℓ+1)!` times the
Kummer form of the Coulomb wave. -/
lemma c33b_coulombfKummer_I (η ρ : ℝ) (hη : η ≠ 0) (ℓ : ℕ) :
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
  rw [ofReal_coulombF, ofReal_coulombf hε, c33b_kappa_inv_sq hη]
  have hK : coulombfKummer (I * (|η| : ℝ)) ℓ (-η * ρ) = coulombfKummer (I * η) ℓ (-η * ρ) := by
    rcases abs_choice η with h | h <;> rw [h]
    push_cast
    rw [mul_neg, coulombfKummer_neg]
  rw [hK, c33b_coulombfKummer_I η ρ hη ℓ]
  have h2 : (-(2 * (η : ℂ))) ^ (ℓ + 1) ≠ 0 :=
    pow_ne_zero _ (neg_ne_zero.mpr (mul_ne_zero two_ne_zero (by exact_mod_cast hη)))
  have hf : (((2 * ℓ + 1)! : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  field_simp

/-- **DLMF 33.16.2**: `G_ℓ(η,ρ) = π(-2η)^ℓ / ((2ℓ+1)! C_ℓ(η)) h(1/η², ℓ; -ηρ)` for `η ≠ 0`,
`ρ > 0`. -/
@[dlmf 33.16.E2]
theorem coulombG_eq_coulombh (ℓ : ℕ) {η : ℝ} (hη : η ≠ 0) {ρ : ℝ} (hρ : 0 < ρ) :
    coulombG ℓ η ρ =
      π * (-2 * η) ^ ℓ / ((2 * ℓ + 1)! * coulombC ℓ η) * coulombh (1 / η ^ 2) ℓ (-η * ρ) := by
  sorry

/-! ### `ε > 0`: `f`, `h`, `s`, `c` in terms of `F_ℓ` and `G_ℓ` (`τ = ε^{1/2}`) -/

/-- For real `x ≥ 0`, `x^{1/2} = √x` as complex numbers. -/
lemma c33b_cpow_half {x : ℝ} (hx : 0 ≤ x) : ((x : ℝ) : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt x : ℂ) := by
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hx]; push_cast; ring_nf

/-- For real `x ≥ 0`, `x^{-1/2} = 1/√x` as complex numbers. -/
lemma c33b_cpow_neg_half {x : ℝ} (hx : 0 ≤ x) :
    ((x : ℝ) : ℂ) ^ (-(1 / 2) : ℂ) = ((Real.sqrt x)⁻¹ : ℝ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hx, Complex.ofReal_cpow hx]; push_cast; ring_nf

/-- For `ε ≥ 0`, the product `A(ε,ℓ) = ∏ (1 + εk²)` is positive. -/
lemma c33b_coulombAProd_pos {ε : ℝ} (hε : 0 ≤ ε) (ℓ : ℕ) : 0 < coulombAProd ε ℓ :=
  Finset.prod_pos fun k _ => by positivity

/-- For `ε > 0`, `1 - e^{-2π/√ε} > 0`. -/
lemma c33b_one_sub_exp_pos {ε : ℝ} (hε : 0 < ε) : 0 < 1 - Real.exp (-(2 * π / Real.sqrt ε)) := by
  have : 0 < 2 * π / Real.sqrt ε := by have := Real.sqrt_pos.mpr hε; positivity
  have := Real.exp_lt_one_iff.mpr (neg_neg_of_pos this)
  linarith

/-- For `ε > 0`, `B(ε,ℓ) = A(ε,ℓ)/(1 - e^{-2π/√ε})` (DLMF 33.14.10). -/
lemma c33b_coulombBFactor_pos {ε : ℝ} (hε : 0 < ε) (ℓ : ℕ) :
    coulombBFactor ε ℓ = coulombAProd ε ℓ / (1 - Real.exp (-(2 * π / Real.sqrt ε))) := by
  simp only [coulombBFactor, hε, ↓reduceIte]


/-- `∏_{k=1}^{ℓ} (η² + k²) η^{-2ℓ} = A(1/η², ℓ)`. -/
lemma q2e_prod_Icc_eq_AProd (ℓ : ℕ) {η : ℝ} (hη : η ≠ 0) :
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
lemma q2e_coulombC_sq (ℓ : ℕ) {η : ℝ} (hη : η ≠ 0) :
    ((2 * ℓ + 1)! * coulombC ℓ η) ^ 2 =
      2 ^ (2 * ℓ) * (2 * π * η / (Real.exp (2 * π * η) - 1)) * (η ^ 2) ^ ℓ *
        coulombAProd (1 / η ^ 2) ℓ := by
  rw [mul_pow, coulombC_sq_eq_prod ℓ hη, ← q2e_prod_Icc_eq_AProd ℓ hη]
  have hf : ((2 * ℓ + 1)! : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  rw [div_pow, one_pow]
  field_simp

/-- **DLMF 33.16.4**: for `ε > 0`, `τ = ε^{1/2}` (33.16.3) and `r > 0`,
`f(ε,ℓ;r) = ((2/(πτ)) (1 - e^{-2π/τ}) / A(ε,ℓ))^{1/2} F_ℓ(-1/τ, τr)`. -/
@[dlmf 33.16.E3, dlmf 33.16.E4]
theorem coulombf_eq_coulombF_pos {ε : ℝ} (hε : 0 < ε) (ℓ : ℕ) {r : ℝ} (hr : 0 < r) :
    coulombf ε ℓ r = Real.sqrt (2 / (π * Real.sqrt ε) *
        (1 - Real.exp (-(2 * π / Real.sqrt ε))) / coulombAProd ε ℓ) *
      coulombF ℓ (-1 / Real.sqrt ε) (Real.sqrt ε * r) := by
  have _ := hr
  have hτ := Real.sqrt_pos.mpr hε
  set τ := Real.sqrt ε with hτ_def
  have hτ2 : τ ^ 2 = ε := Real.sq_sqrt hε.le
  have hη : (-1 / τ) ≠ 0 := by positivity
  rw [coulombF_eq_coulombf ℓ hη, show -(-1 / τ) * (τ * r) = r by field_simp,
    show 1 / (-1 / τ) ^ 2 = ε by rw [← hτ2]; field_simp]
  have hA := c33b_coulombAProd_pos hε.le ℓ
  have hE := c33b_one_sub_exp_pos hε
  have hC := coulombC_pos ℓ (-1 / τ)
  have hK := q2e_coulombC_sq ℓ hη
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

/-- **DLMF 33.16.5**: for `ε > 0`, `r > 0`,
`h(ε,ℓ;r) = ((2/(πτ)) A(ε,ℓ) / (1 - e^{-2π/τ}))^{1/2} G_ℓ(-1/τ, τr)`. -/
@[dlmf 33.16.E5]
theorem coulombh_eq_coulombG_pos {ε : ℝ} (hε : 0 < ε) (ℓ : ℕ) {r : ℝ} (hr : 0 < r) :
    coulombh ε ℓ r = Real.sqrt (2 / (π * Real.sqrt ε) * coulombAProd ε ℓ /
        (1 - Real.exp (-(2 * π / Real.sqrt ε)))) *
      coulombG ℓ (-1 / Real.sqrt ε) (Real.sqrt ε * r) := by
  sorry

/-- **DLMF 33.16.6**: for `ε > 0`, `r < 0`,
`f(ε,ℓ;r) = (-1)^{ℓ+1} ((2/(πτ)) (e^{2π/τ} - 1) / A(ε,ℓ))^{1/2} F_ℓ(1/τ, -τr)`. -/
@[dlmf 33.16.E6]
theorem coulombf_eq_coulombF_neg {ε : ℝ} (hε : 0 < ε) (ℓ : ℕ) {r : ℝ} (hr : r < 0) :
    coulombf ε ℓ r = (-1) ^ (ℓ + 1) * Real.sqrt (2 / (π * Real.sqrt ε) *
        (Real.exp (2 * π / Real.sqrt ε) - 1) / coulombAProd ε ℓ) *
      coulombF ℓ (1 / Real.sqrt ε) (-(Real.sqrt ε * r)) := by
  have _ := hr
  have hτ := Real.sqrt_pos.mpr hε
  set τ := Real.sqrt ε with hτ_def
  have hτ2 : τ ^ 2 = ε := Real.sq_sqrt hε.le
  have hη : (1 / τ) ≠ 0 := by positivity
  rw [coulombF_eq_coulombf ℓ hη, show -(1 / τ) * -(τ * r) = r by field_simp,
    show 1 / (1 / τ) ^ 2 = ε by rw [← hτ2]; field_simp]
  have hA := c33b_coulombAProd_pos hε.le ℓ
  have hC := coulombC_pos ℓ (1 / τ)
  have hK := q2e_coulombC_sq ℓ hη
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

/-- **DLMF 33.16.7**: for `ε > 0`, `r < 0`,
`h(ε,ℓ;r) = (-1)^ℓ ((2/(πτ)) A(ε,ℓ) / (e^{2π/τ} - 1))^{1/2} G_ℓ(1/τ, -τr)`. -/
@[dlmf 33.16.E7]
theorem coulombh_eq_coulombG_neg {ε : ℝ} (hε : 0 < ε) (ℓ : ℕ) {r : ℝ} (hr : r < 0) :
    coulombh ε ℓ r = (-1) ^ ℓ * Real.sqrt (2 / (π * Real.sqrt ε) * coulombAProd ε ℓ /
        (Real.exp (2 * π / Real.sqrt ε) - 1)) *
      coulombG ℓ (1 / Real.sqrt ε) (-(Real.sqrt ε * r)) := by
  sorry

/-- **DLMF 33.16.14**: for `ε > 0`, `r > 0`, `s(ε,ℓ;r) = (πτ)^{-1/2} F_ℓ(-1/τ, τr)` and
`c(ε,ℓ;r) = (πτ)^{-1/2} G_ℓ(-1/τ, τr)`. -/
@[dlmf 33.16.E14]
theorem coulombs_coulombc_eq_pos {ε : ℝ} (hε : 0 < ε) (ℓ : ℕ) {r : ℝ} (hr : 0 < r) :
    coulombs ε ℓ r = ((Real.sqrt (π * Real.sqrt ε))⁻¹ *
        coulombF ℓ (-1 / Real.sqrt ε) (Real.sqrt ε * r) : ℝ) ∧
      coulombc ε ℓ r = ((Real.sqrt (π * Real.sqrt ε))⁻¹ *
        coulombG ℓ (-1 / Real.sqrt ε) (Real.sqrt ε * r) : ℝ) := by
  have hA := c33b_coulombAProd_pos hε.le ℓ
  have hE := c33b_one_sub_exp_pos hε
  have hτ := Real.sqrt_pos.mpr hε
  have hB := c33b_coulombBFactor_pos hε ℓ
  have hπτ : 0 < π * Real.sqrt ε := by positivity
  constructor
  · rw [coulombs, hB, c33b_cpow_half (by positivity), coulombf_eq_coulombF_pos hε ℓ hr,
      ← Complex.ofReal_mul, ← mul_assoc, ← Real.sqrt_mul (by positivity)]
    congr 3
    rw [← Real.sqrt_inv]
    congr 1
    field_simp
  · rw [coulombc, hB, c33b_cpow_neg_half (by positivity), coulombh_eq_coulombG_pos hε ℓ hr,
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
  have hA := c33b_coulombAProd_pos hε.le ℓ
  have hE := c33b_one_sub_exp_pos hε
  have hτ := Real.sqrt_pos.mpr hε
  have hB := c33b_coulombBFactor_pos hε ℓ
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
  · rw [coulombs, hB, c33b_cpow_half (by positivity), coulombf_eq_coulombF_neg hε ℓ hr,
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
  · rw [coulombc, hB, c33b_cpow_neg_half (by positivity), coulombh_eq_coulombG_neg hε ℓ hr,
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
lemma q2e_nu_pos {ε : ℝ} (hε : ε < 0) : 0 < (-ε) ^ (-(1 / 2 : ℝ)) :=
  Real.rpow_pos_of_pos (neg_pos.mpr hε) _

/-- `κ = ν` for `ε < 0`, `r > 0`. -/
lemma q2e_kappa_neg_pos {ε : ℝ} (hε : ε < 0) {r : ℝ} (hr : 0 < r) :
    coulombKappa ε r = ((-ε) ^ (-(1 / 2 : ℝ)) : ℝ) := by
  simp [coulombKappa, hε, hr]

/-- `κ = -ν` for `ε < 0`, `r ≤ 0`. -/
lemma q2e_kappa_neg_neg {ε : ℝ} (hε : ε < 0) {r : ℝ} (hr : r ≤ 0) :
    coulombKappa ε r = -(((-ε) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
  simp [coulombKappa, hε, not_lt.mpr hr]

/-- `ε = -1/ν²`. -/
lemma q2e_eps_eq_nu {ε : ℝ} (hε : ε < 0) : ε = -1 / ((-ε) ^ (-(1 / 2 : ℝ))) ^ 2 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (neg_pos.mpr hε).le]
  norm_num [Real.rpow_neg_one]

/-- `A(ε,ℓ) ≠ 0` excludes `ν ∈ {1, …, ℓ}`. -/
lemma q2e_nu_sub_ne {ε : ℝ} (hε : ε < 0) {ℓ : ℕ} (hA : coulombAProd ε ℓ ≠ 0) (m : ℕ) :
    (((-ε) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) - ℓ ≠ -(m : ℂ) := by
  intro h
  set ν := (-ε) ^ (-(1 / 2 : ℝ))
  have hν := q2e_nu_pos hε
  have h' : ν = (ℓ : ℝ) - m := by
    have := congrArg Complex.re h; simp at this; linarith
  have hm : m < ℓ := by
    have : (0 : ℝ) < ℓ - m := h' ▸ hν
    exact_mod_cast (by linarith : (m : ℝ) < ℓ)
  apply hA
  unfold coulombAProd
  apply Finset.prod_eq_zero (i := ℓ - m) (Finset.mem_range.mpr (by omega))
  rw [q2e_eps_eq_nu hε, Nat.cast_sub hm.le, ← h']
  have : ν ≠ 0 := hν.ne'
  field_simp
  ring

/-- `ζ_ℓ(ν,r)` is real when `2r/ν > 0`. -/
lemma q2e_conj_coulombZeta (ℓ : ℕ) {ν r : ℝ} (h : 0 < 2 * r / ν) :
    conj (coulombZeta ℓ ν r) = coulombZeta ℓ ν r := by
  have hs : ((2 * r / ν : ℝ) : ℂ) ∈ slitPlane := Complex.ofReal_mem_slitPlane.mpr h
  unfold coulombZeta
  have e : (2 * r / ν : ℂ) = ((2 * r / ν : ℝ) : ℂ) := by push_cast; ring
  rw [e, map_mul, map_mul, map_pow, ← Complex.exp_conj, conj_kummerU _ _ hs]
  simp [Complex.conj_ofReal, map_sub, map_add, map_mul, map_natCast, map_ofNat]

/-- `e^{nπi} = (-1)^n`. -/
lemma q2e_exp_nat_pi_I (n : ℕ) : exp ((n : ℂ) * π * I) = (-1) ^ n := by
  rw [show (n : ℂ) * π * I = n * (π * I) by ring, Complex.exp_nat_mul, exp_pi_mul_I]

/-- Kummer's connection formula 13.2.41 at a positive real argument `z = x`, in the form used for
`f` (`a = ℓ+1-κ`, `b = 2ℓ+2`). -/
lemma q2e_kummerM_conn (ℓ : ℕ) (a : ℂ) {x : ℝ} (hx : 0 < x) :
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
lemma q2e_inv_Gamma_one_sub {x : ℝ} (hx : Real.Gamma x ≠ 0) :
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
lemma q2e_sin_sub_nat (ν : ℝ) (ℓ : ℕ) :
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
  have hν : 0 < ν := q2e_nu_pos hε
  have hκ : coulombKappa ε r = (ν : ℂ) := q2e_kappa_neg_pos hε hr
  have hνA : ∀ m : ℕ, (ν : ℂ) - ℓ ≠ -(m : ℂ) := q2e_nu_sub_ne hε hA
  have hx : 0 < 2 * r / ν := by positivity
  set x := 2 * r / ν with hx_def
  have hζ := q2e_conj_coulombZeta ℓ (ν := ν) (r := r) hx
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
    rw [hxc, q2e_kummerM_conn ℓ _ hx]
    have hr2 : (2 * (r : ℂ)) = (ν : ℂ) * x := by rw [← hxc]; field_simp
    have he1 : exp (-(r : ℂ) / (ν : ℂ)) = exp (-(x : ℂ) / 2) := by
      congr 1; rw [← hxc]; field_simp
    rw [hr2, he1]
    have he3 : exp ((2 * (ℓ : ℂ) + 2 - (ℓ + 1 - (ν : ℂ))) * π * I) =
        (-1) ^ (ℓ + 1) * exp (I * π * (ν : ℂ)) := by
      rw [← q2e_exp_nat_pi_I, ← Complex.exp_add]; congr 1; push_cast; ring
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
      rw [q2e_exp_nat_pi_I, pow_mul]; simp
    have h3 : exp (((π * ν : ℝ) : ℂ) * I) = (c : ℂ) + (s : ℂ) * I := by
      rw [Complex.exp_mul_I]; simp only [c, s]; push_cast; ring
    rw [show -((ℓ : ℂ) + 1 - ν) * π * I = ((ℓ + 1 : ℕ) : ℂ) * π * I +
        ((π * ν : ℝ) : ℂ) * I - ((2 * (ℓ + 1) : ℕ) : ℂ) * π * I by push_cast; ring,
      Complex.exp_sub, Complex.exp_add, h2, h3, q2e_exp_nat_pi_I, div_one]
  have hG1 : Gamma ((ℓ : ℂ) + 1 - ν) = (Real.Gamma (ℓ + 1 - ν) : ℂ) := by
    rw [← Complex.Gamma_ofReal]; push_cast; ring_nf
  have hG2 : Gamma ((ℓ : ℂ) + 1 + ν) = (Real.Gamma (ℓ + 1 + ν) : ℂ) := by
    rw [← Complex.Gamma_ofReal]; push_cast; ring_nf
  have hGr : Real.Gamma (ν - ℓ) ≠ 0 := by
    have := Complex.Gamma_ne_zero hνA
    rw [show (ν : ℂ) - ℓ = ((ν - ℓ : ℝ) : ℂ) by push_cast; ring, Complex.Gamma_ofReal] at this
    exact_mod_cast this
  have hinv : (Real.Gamma (ℓ + 1 - ν))⁻¹ = (-1) ^ ℓ * s * Real.Gamma (ν - ℓ) / π := by
    rw [show (ℓ : ℝ) + 1 - ν = 1 - (ν - ℓ) by ring, q2e_inv_Gamma_one_sub hGr,
      q2e_sin_sub_nat]
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

/-- **DLMF 33.16.11**: for `ε < 0`, `r > 0`, `A(ε,ℓ) ≠ 0`,
`h(ε,ℓ;r) = (-1)^ℓ ν^{ℓ+1} A(ε,ℓ) (sin(πν) ζ_ℓ(ν,r)/Γ(ℓ+1+ν) + cos(πν) Γ(ν-ℓ) ξ_ℓ(ν,r)/π)`. -/
@[dlmf 33.16.E11]
theorem coulombh_eq_whittaker_pos {ε : ℝ} (hε : ε < 0) (ℓ : ℕ) {r : ℝ} (hr : 0 < r)
    (hA : coulombAProd ε ℓ ≠ 0) :
    let ν := (-ε) ^ (-(1 / 2 : ℝ))
    (coulombh ε ℓ r : ℂ) = (-1) ^ ℓ * (ν : ℂ) ^ (ℓ + 1) * coulombAProd ε ℓ *
      ((Real.sin (π * ν) : ℂ) * coulombZeta ℓ ν r / (Real.Gamma (ℓ + 1 + ν) : ℂ) +
        (Real.cos (π * ν) * Real.Gamma (ν - ℓ) * coulombXi ℓ ν r / π : ℝ)) := by
  sorry

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
  have hν : 0 < ν := q2e_nu_pos hε
  have hκ : coulombKappa ε r = -(ν : ℂ) := q2e_kappa_neg_neg hε hr.le
  have hνA : ∀ m : ℕ, (ν : ℂ) - ℓ ≠ -(m : ℂ) := q2e_nu_sub_ne hε hA
  have hx : 0 < 2 * r / (-ν) := div_pos_of_neg_of_neg (by linarith) (by linarith)
  set x := 2 * r / (-ν) with hx_def
  have hζ := q2e_conj_coulombZeta ℓ (ν := -ν) (r := r) hx
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
    rw [hxc, q2e_kummerM_conn ℓ _ hx]
    push_cast
    simp only [hxc]
    have hr2 : (2 * (r : ℂ)) = -(ν : ℂ) * x := by rw [← hxc]; field_simp
    have he1 : exp (-(r : ℂ) / -(ν : ℂ)) = exp (-(x : ℂ) / 2) := by
      congr 1; rw [← hxc]; field_simp
    rw [hr2, he1]
    have he3 : exp ((2 * (ℓ : ℂ) + 2 - (ℓ + 1 - -(ν : ℂ))) * π * I) =
        (-1) ^ (ℓ + 1) * exp (I * π * (-(ν : ℂ))) := by
      rw [← q2e_exp_nat_pi_I, ← Complex.exp_add]; congr 1; push_cast; ring
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
      rw [q2e_exp_nat_pi_I, pow_mul]; simp
    have h3 : exp (((-(π * ν) : ℝ) : ℂ) * I) = (c : ℂ) - (s : ℂ) * I := by
      rw [Complex.exp_mul_I]; simp only [c, s]; push_cast
      rw [Complex.cos_neg, Complex.sin_neg]; ring
    rw [show -((ℓ : ℂ) + 1 + ν) * π * I = ((ℓ + 1 : ℕ) : ℂ) * π * I +
        ((-(π * ν) : ℝ) : ℂ) * I - ((2 * (ℓ + 1) : ℕ) : ℂ) * π * I by push_cast; ring,
      Complex.exp_sub, Complex.exp_add, h2, h3, q2e_exp_nat_pi_I, div_one]
  have hG1 : Gamma ((ℓ : ℂ) + 1 - ν) = (Real.Gamma (ℓ + 1 - ν) : ℂ) := by
    rw [← Complex.Gamma_ofReal]; push_cast; ring_nf
  have hG2 : Gamma ((ℓ : ℂ) + 1 + ν) = (Real.Gamma (ℓ + 1 + ν) : ℂ) := by
    rw [← Complex.Gamma_ofReal]; push_cast; ring_nf
  have hGr : Real.Gamma (ν - ℓ) ≠ 0 := by
    have := Complex.Gamma_ne_zero hνA
    rw [show (ν : ℂ) - ℓ = ((ν - ℓ : ℝ) : ℂ) by push_cast; ring, Complex.Gamma_ofReal] at this
    exact_mod_cast this
  have hinv : (Real.Gamma (ℓ + 1 - ν))⁻¹ = (-1) ^ ℓ * s * Real.Gamma (ν - ℓ) / π := by
    rw [show (ℓ : ℝ) + 1 - ν = 1 - (ν - ℓ) by ring, q2e_inv_Gamma_one_sub hGr,
      q2e_sin_sub_nat]
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
  have hν : 0 < ν := q2e_nu_pos hε
  have hκ : coulombKappa ε r = -(ν : ℂ) := q2e_kappa_neg_neg hε hr.le
  have hκ1 : coulombKappa ε 1 = (ν : ℂ) := q2e_kappa_neg_pos hε one_pos
  have hνA : ∀ m : ℕ, (ν : ℂ) - ℓ ≠ -(m : ℂ) := q2e_nu_sub_ne hε hA
  have hS : coulombSFactor ε r = 0 := by simp [coulombSFactor, hε, not_lt.mpr hr.le]
  have hnp : ¬ (ε = 0 ∨ ∃ m : ℕ, (ℓ : ℂ) + 1 - coulombKappa ε r = -(m : ℂ)) := by
    rintro (h | ⟨m, hm⟩)
    · exact hε.ne h
    · rw [hκ] at hm
      have := congrArg Complex.re hm
      simp at this
      linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m), (Nat.cast_nonneg ℓ : (0 : ℝ) ≤ ℓ)]
  have hζ := q2e_conj_coulombZeta ℓ (ν := -ν) (r := r) (by
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
  sorry

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
  have hν : 0 < ν := q2e_nu_pos hε
  have hκ1 : coulombKappa ε 1 = (ν : ℂ) := q2e_kappa_neg_pos hε one_pos
  have hνA := q2e_nu_sub_ne hε hA.ne'
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
  · rw [coulombs, hB, c33b_cpow_half (by positivity), hf, Real.sqrt_div' _ (by norm_num), hsA,
      h32, hK']
    rw [hνt, hGmk, hGpg]
    push_cast
    field_simp
    ring
  · rw [coulombc, hB, c33b_cpow_neg_half (by positivity), hh, Real.sqrt_mul (by norm_num), hsA,
      h2ν, hK', hAr]
    rw [hνt, hGmk, hGpg]
    push_cast
    field_simp
    ring

end DLMF.Coulomb
