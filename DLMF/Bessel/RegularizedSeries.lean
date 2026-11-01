/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bessel.Basic.Equation
public import DLMF.Confluent.KummerProperties
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Analysis.SpecialFunctions.Bessel

/-!
# Half-integer orders and the Kummer connection of Bessel functions (AAR §§4.5–4.6)

The series `J_ν(z) = (z/2)^ν ₀F̃₁(;ν+1;-z²/4)` reduces to elementary functions at half-integer
orders and is a Kummer function times an exponential.

## Main results

* `besselJ_half`, `besselJ_neg_half`: `J_{±1/2}` in elementary form (DLMF 10.16.1).
* `kummerM_eq_exp_mul_regularized0F1`: Kummer's second transformation (AAR (4.1.12)).
* `besselJ_eq_kummerM`: `J_ν` through Kummer's function (DLMF 10.16.5).

## Implementation notes

The calculus of `₀F̃₁` and Bessel's equation are in `DLMF.Bessel.Basic.RegularizedSeries` and
`DLMF.Bessel.Basic.Equation`.
-/
@[expose] public section

open Complex
open scoped Real Nat Topology
open DLMF.Confluent

noncomputable section

namespace DLMF.Bessel

/-- Half-integer Gamma values needed for the elementary Bessel evaluations. -/
theorem Gamma_three_halves : Gamma (3 / 2 : ℂ) = Gamma (1 / 2) / 2 := by
  have h := Gamma_add_one (1 / 2 : ℂ) (by norm_num)
  have heq : (1 / 2 : ℂ) + 1 = 3 / 2 := by ring
  rw [heq] at h
  rw [h]
  ring

/-- Identity under the stated parameter and domain assumptions: `Gamma ((3 / 2 : ℂ) + n) = ((2 * n
+ 1).factorial : ℂ) / (4 ^ n * n.factorial * 2) * Gamma (1 / 2)`. -/
theorem Gamma_nat_add_three_halves (n : ℕ) :
    Gamma ((3 / 2 : ℂ) + n) =
      ((2 * n + 1).factorial : ℂ) / (4 ^ n * n.factorial * 2) * Gamma (1 / 2) := by
  have hfac : ((2 * n + 1).factorial : ℝ) =
      (2 * n + 1).doubleFactorial * (2 ^ n * n.factorial) := by
    have h := Nat.factorial_eq_mul_doubleFactorial (2 * n)
    rw [Nat.doubleFactorial_two_mul] at h
    exact_mod_cast h
  have hreal : Real.Gamma (n + 1 + 1 / 2) =
      (2 * n + 1).factorial / (4 ^ n * n.factorial * 2) * Real.Gamma (1 / 2) := by
    rw [Real.Gamma_nat_add_one_add_half, Real.Gamma_one_half_eq, hfac]
    have h4 : (4 : ℝ) ^ n = 2 ^ n * 2 ^ n := by rw [← mul_pow]; norm_num
    have hf : (n.factorial : ℝ) ≠ 0 := by positivity
    rw [h4, pow_succ]
    field_simp
  have e1 : ((3 / 2 : ℂ) + n) = ((n + 1 + 1 / 2 : ℝ) : ℂ) := by push_cast; ring
  have e2 : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [e1, e2, Complex.Gamma_ofReal, Complex.Gamma_ofReal, hreal]
  push_cast
  ring

/-- Identity under the stated parameter and domain assumptions: `Gamma ((1 / 2 : ℂ) + n) = ((2 *
n).factorial : ℂ) / (4 ^ n * n.factorial) * Gamma (1 / 2)`. -/
theorem Gamma_nat_add_half (n : ℕ) :
    Gamma ((1 / 2 : ℂ) + n) =
      ((2 * n).factorial : ℂ) / (4 ^ n * n.factorial) * Gamma (1 / 2) := by
  have hfac : ((2 * n).factorial : ℝ) = 2 ^ n * n.factorial * (2 * n - 1).doubleFactorial := by
    rcases n with _ | n
    · simp
    · have h := Nat.factorial_eq_mul_doubleFactorial (2 * (n + 1) - 1)
      rw [show 2 * (n + 1) - 1 + 1 = 2 * (n + 1) by omega, Nat.doubleFactorial_two_mul] at h
      exact_mod_cast h
  have hreal : Real.Gamma (n + 1 / 2) =
      (2 * n).factorial / (4 ^ n * n.factorial) * Real.Gamma (1 / 2) := by
    rw [Real.Gamma_nat_add_half, Real.Gamma_one_half_eq, hfac]
    have h4 : (4 : ℝ) ^ n = 2 ^ n * 2 ^ n := by rw [← mul_pow]; norm_num
    have hf : (n.factorial : ℝ) ≠ 0 := by positivity
    rw [h4]
    field_simp
  have e1 : ((1 / 2 : ℂ) + n) = ((n + 1 / 2 : ℝ) : ℂ) := by push_cast; ring
  have e2 : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [e1, e2, Complex.Gamma_ofReal, Complex.Gamma_ofReal, hreal]
  push_cast
  ring

/-- Identity under the stated parameter and domain assumptions: `log (2 : ℂ) = Real.log 2`. -/
theorem log_two : log (2 : ℂ) = Real.log 2 := by
  rw [← ofReal_ofNat 2, ofReal_log (by norm_num)]

/-- Identity under the stated parameter and domain assumptions: `log (π : ℂ) = Real.log π`. -/
theorem log_pi : log (π : ℂ) = Real.log π :=
  (ofReal_log Real.pi_pos.le).symm

/-- Nonvanishing under the stated hypotheses: `(π : ℂ).arg ≠ π`. -/
theorem arg_pi_ne_pi : (π : ℂ).arg ≠ π := by
  rw [arg_ofReal_of_nonneg Real.pi_pos.le]
  exact ne_of_lt Real.pi_pos

/-- Identity under the stated parameter and domain assumptions: `log (z / 2) = log z - log 2`. -/
theorem log_div_ofNat_two {z : ℂ} (hz : z ∈ slitPlane) :
    log (z / 2) = log z - log 2 := by
  have hz0 := slitPlane_ne_zero hz
  have hinv : (2 : ℂ)⁻¹ = ↑((2 : ℝ)⁻¹) := by
    rw [← ofReal_ofNat 2, ← ofReal_inv]
  rw [div_eq_mul_inv, hinv, log_mul_ofReal (2⁻¹) (by norm_num) z hz0, Real.log_inv,
    ofReal_neg, log_two]
  ring

/-- Identity under the stated parameter and domain assumptions: `(z / 2) ^ (1 / 2 : ℂ) = z ^ (1 /
2 : ℂ) / (2 : ℂ) ^ (1 / 2 : ℂ)`. -/
theorem cpow_half_div_two {z : ℂ} (hz : z ∈ slitPlane) :
    (z / 2) ^ (1 / 2 : ℂ) = z ^ (1 / 2 : ℂ) / (2 : ℂ) ^ (1 / 2 : ℂ) := by
  have hz0 := slitPlane_ne_zero hz
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  rw [cpow_def_of_ne_zero (div_ne_zero hz0 h2), log_div_ofNat_two hz, sub_mul, exp_sub,
    ← cpow_def_of_ne_zero hz0, ← cpow_def_of_ne_zero h2]

/-- Identity under the stated parameter and domain assumptions: `(z / 2) ^ (-(1 / 2 : ℂ)) = (2 :
ℂ) ^ (1 / 2 : ℂ) / z ^ (1 / 2 : ℂ)`. -/
theorem cpow_half_recip_div_two {z : ℂ} (hz : z ∈ slitPlane) :
    (z / 2) ^ (-(1 / 2 : ℂ)) = (2 : ℂ) ^ (1 / 2 : ℂ) / z ^ (1 / 2 : ℂ) := by
  rw [cpow_neg, cpow_half_div_two hz, inv_div]

/-- Identity under the stated parameter and domain assumptions: `((2 : ℂ) / π) ^ (1 / 2 : ℂ) = (2
: ℂ) ^ (1 / 2 : ℂ) / (π : ℂ) ^ (1 / 2 : ℂ)`. -/
theorem cpow_half_div_pi :
    ((2 : ℂ) / π) ^ (1 / 2 : ℂ) =
      (2 : ℂ) ^ (1 / 2 : ℂ) / (π : ℂ) ^ (1 / 2 : ℂ) := by
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hlog : log ((2 : ℂ) / π) = log 2 - log π := by
    rw [div_eq_mul_inv, ← ofReal_ofNat 2, log_ofReal_mul (by norm_num) (inv_ne_zero hπ),
      log_inv _ arg_pi_ne_pi, ← log_two, log_pi]
    simp [ofReal_ofNat]
    abel
  rw [cpow_def_of_ne_zero (div_ne_zero h2 hπ), hlog, sub_mul, exp_sub,
    ← cpow_def_of_ne_zero h2, ← cpow_def_of_ne_zero hπ]

/-- Identity under the stated parameter and domain assumptions: `(2 / (π * z)) ^ (1 / 2 : ℂ) = ((2
: ℂ) / π) ^ (1 / 2 : ℂ) / z ^ (1 / 2 : ℂ)`. -/
theorem cpow_half_two_div_pi_z {z : ℂ} (hz : z ∈ slitPlane) :
    (2 / (π * z)) ^ (1 / 2 : ℂ) =
      ((2 : ℂ) / π) ^ (1 / 2 : ℂ) / z ^ (1 / 2 : ℂ) := by
  have hz0 := slitPlane_ne_zero hz
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hpos : 0 < ((2 : ℝ) / π) := by positivity
  have hzinv : log (z⁻¹) = -log z := log_inv z (slitPlane_arg_ne_pi hz)
  have hform : (2 : ℂ) / (π * z) = ↑((2 : ℝ) / π) * z⁻¹ := by
    push_cast
    field [hπ, hz0]
  have hlog : log (2 / (π * z)) = log ((2 : ℂ) / π) - log z := by
    rw [hform, log_ofReal_mul hpos (inv_ne_zero hz0), hzinv, ofReal_log hpos.le,
      ofReal_div, ofReal_ofNat]
    ring
  rw [cpow_def_of_ne_zero (div_ne_zero h2 (mul_ne_zero hπ hz0)), hlog, sub_mul, exp_sub,
    ← cpow_def_of_ne_zero (div_ne_zero h2 hπ), ← cpow_def_of_ne_zero hz0]

/-- Identity under the stated parameter and domain assumptions: `w = w ^ (1 / 2 : ℂ) * w ^ (1 / 2
: ℂ)`. -/
theorem cpow_half_sq {w : ℂ} (hw : w ≠ 0) :
    w = w ^ (1 / 2 : ℂ) * w ^ (1 / 2 : ℂ) := by
  have hadd := cpow_add (x := w) (1 / 2 : ℂ) (1 / 2 : ℂ) hw
  have hsum : (1 / 2 : ℂ) + 1 / 2 = 1 := by ring
  rw [hsum, cpow_one] at hadd
  exact hadd

/-- The algebraic identity connecting the half-integer Bessel prefactors. -/
theorem bessel_half_prefactor {z : ℂ} (hz : z ∈ slitPlane) :
    (z / 2) ^ (1 / 2 : ℂ) * 2 / (z * Gamma (1 / 2 : ℂ)) =
      (2 / (π * z)) ^ (1 / 2 : ℂ) := by
  have hz0 := slitPlane_ne_zero hz
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have h2h : (2 : ℂ) ^ (1 / 2 : ℂ) ≠ 0 :=
    (cpow_ne_zero_iff.mpr (Or.inl h2) : (2 : ℂ) ^ (1 / 2 : ℂ) ≠ 0)
  have hzh : z ^ (1 / 2 : ℂ) ≠ 0 :=
    (cpow_ne_zero_iff.mpr (Or.inl hz0) : z ^ (1 / 2 : ℂ) ≠ 0)
  have hπh : (π : ℂ) ^ (1 / 2 : ℂ) ≠ 0 :=
    (cpow_ne_zero_iff.mpr (Or.inl hπ) : (π : ℂ) ^ (1 / 2 : ℂ) ≠ 0)
  have hzsq := cpow_half_sq hz0
  have h2sq := cpow_half_sq h2
  rw [Gamma_one_half_eq, cpow_half_div_two hz, cpow_half_two_div_pi_z hz, cpow_half_div_pi]
  have hform :
      z ^ (1 / 2 : ℂ) / (2 : ℂ) ^ (1 / 2 : ℂ) * 2 / (z * (π : ℂ) ^ (1 / 2 : ℂ)) =
        z ^ (1 / 2 : ℂ) / (2 : ℂ) ^ (1 / 2 : ℂ) *
          ((2 : ℂ) ^ (1 / 2 : ℂ) * (2 : ℂ) ^ (1 / 2 : ℂ)) /
        (z ^ (1 / 2 : ℂ) * z ^ (1 / 2 : ℂ) * (π : ℂ) ^ (1 / 2 : ℂ)) := by
    rw [← hzsq, ← h2sq]
  have hsimp :
      z ^ (1 / 2 : ℂ) / (2 : ℂ) ^ (1 / 2 : ℂ) *
          ((2 : ℂ) ^ (1 / 2 : ℂ) * (2 : ℂ) ^ (1 / 2 : ℂ)) /
        (z ^ (1 / 2 : ℂ) * z ^ (1 / 2 : ℂ) * (π : ℂ) ^ (1 / 2 : ℂ)) =
        (2 : ℂ) ^ (1 / 2 : ℂ) / (π : ℂ) ^ (1 / 2 : ℂ) / z ^ (1 / 2 : ℂ) := by
    field [h2h, hzh, hπh]
  rw [hform, hsimp]

/-- Identity under the stated parameter and domain assumptions: `regularizedHGFun (∅ : Multiset ℂ)
{3 / 2} (-(z ^ 2 / 4)) = 2 * sin z / (z * Gamma (1 / 2 : ℂ))`. -/
theorem regularized0F1_three_halves_eq_sinc {z : ℂ} (hz : z ≠ 0) :
    regularizedHGFun (∅ : Multiset ℂ) {3 / 2} (-(z ^ 2 / 4)) =
      2 * sin z / (z * Gamma (1 / 2 : ℂ)) := by
  have hg : Gamma (1 / 2 : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  have hs := (hasFPowerSeriesOnBall_regularized0F1 (3 / 2 : ℂ)).hasSum_mul_pow
    (z := -(z ^ 2 / 4)) (by simp)
  have hcoeff (n : ℕ) :
      regularizedHGFunCoeff (∅ : Multiset ℂ) {3 / 2} n * (-(z ^ 2 / 4)) ^ n =
        (2 / Gamma (1 / 2 : ℂ)) *
          ((-1) ^ n * z ^ (2 * n) / (2 * n + 1).factorial) := by
    have hn0 : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    have h2n : ((2 * n + 1).factorial : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (2 * n + 1).factorial_ne_zero
    have h4 : (4 : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
    have h2 : (2 : ℂ) ≠ 0 := by norm_num
    have hG : Gamma ((3 / 2 : ℂ) + n) ≠ 0 := by
      refine Gamma_ne_zero_of_re_pos ?_
      simp
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    rw [regularizedHGFunCoeff_empty, Gamma_nat_add_three_halves]
    have hpow : (-(z ^ 2 / 4)) ^ n = (-1) ^ n * z ^ (2 * n) / (4 : ℂ) ^ n := by
      rw [neg_pow, div_pow, pow_mul, mul_div_assoc]
    rw [hpow]
    field [hn0, h2n, h4, h2, hg, hG]
  simp_rw [hcoeff] at hs
  have hsin0 := (hasSum_sin z).div_const z
  have heq : (fun n : ℕ => ((-1) ^ n * z ^ (2 * n + 1) / (2 * n + 1).factorial) / z) =
      fun n => (-1) ^ n * z ^ (2 * n) / (2 * n + 1).factorial := by
    ext n
    field [hz]
  rw [heq] at hsin0
  have hval : (2 / Gamma (1 / 2 : ℂ)) * (sin z / z) =
      2 * sin z / (z * Gamma (1 / 2 : ℂ)) := by
    field [hz, hg]
  exact hs.unique (hval ▸ hsin0.mul_left (2 / Gamma (1 / 2 : ℂ)))

/-- Identity under the stated parameter and domain assumptions: `regularizedHGFun (∅ : Multiset ℂ)
{1 / 2} (-(z ^ 2 / 4)) = cos z / Gamma (1 / 2 : ℂ)`. -/
theorem regularized0F1_half_eq_cos {z : ℂ} :
    regularizedHGFun (∅ : Multiset ℂ) {1 / 2} (-(z ^ 2 / 4)) =
      cos z / Gamma (1 / 2 : ℂ) := by
  have hg : Gamma (1 / 2 : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  have hs := (hasFPowerSeriesOnBall_regularized0F1 (1 / 2 : ℂ)).hasSum_mul_pow
    (z := -(z ^ 2 / 4)) (by simp)
  have hcoeff (n : ℕ) :
      regularizedHGFunCoeff (∅ : Multiset ℂ) {1 / 2} n * (-(z ^ 2 / 4)) ^ n =
        (1 / Gamma (1 / 2 : ℂ)) * ((-1) ^ n * z ^ (2 * n) / (2 * n).factorial) := by
    have hn0 : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    have h2n : ((2 * n).factorial : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (2 * n).factorial_ne_zero
    have h4 : (4 : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
    have hG : Gamma ((1 / 2 : ℂ) + n) ≠ 0 := by
      refine Gamma_ne_zero_of_re_pos ?_
      simp
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    rw [regularizedHGFunCoeff_empty, Gamma_nat_add_half]
    have hpow : (-(z ^ 2 / 4)) ^ n = (-1) ^ n * z ^ (2 * n) / (4 : ℂ) ^ n := by
      rw [neg_pow, div_pow, pow_mul, mul_div_assoc]
    rw [hpow]
    field [hn0, h2n, h4, hg, hG]
  simp_rw [hcoeff] at hs
  have hval : (1 / Gamma (1 / 2 : ℂ)) * cos z = cos z / Gamma (1 / 2 : ℂ) := by
    field [hg]
  exact hs.unique (hval ▸ (hasSum_cos z).mul_left (1 / Gamma (1 / 2 : ℂ)))

/-- Elementary evaluation `J_{1/2}(z) = √(2/(πz)) sin z` (AAR §4.5). -/
@[dlmf 10.16.E1]
theorem besselJ_half (z : ℂ) (hz : z ∈ slitPlane) :
    besselJ (1 / 2) z = (2 / (π * z)) ^ (1 / 2 : ℂ) * sin z := by
  have hz0 := slitPlane_ne_zero hz
  have hg : Gamma (1 / 2 : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  have hpar : (1 / 2 : ℂ) + 1 = 3 / 2 := by ring
  simp only [besselJ_eq_regularized]
  rw [hpar, regularized0F1_three_halves_eq_sinc hz0, ← bessel_half_prefactor hz]
  field [hz0, hg]

/-- Elementary evaluation `J_{-1/2}(z) = √(2/(πz)) cos z`. -/
@[dlmf 10.16.E1]
theorem besselJ_neg_half (z : ℂ) (hz : z ∈ slitPlane) :
    besselJ (-(1 / 2)) z = (2 / (π * z)) ^ (1 / 2 : ℂ) * cos z := by
  have hz0 := slitPlane_ne_zero hz
  have hg : Gamma (1 / 2 : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have h2h : (2 : ℂ) ^ (1 / 2 : ℂ) ≠ 0 :=
    (cpow_ne_zero_iff.mpr (Or.inl h2) : (2 : ℂ) ^ (1 / 2 : ℂ) ≠ 0)
  have hzh : z ^ (1 / 2 : ℂ) ≠ 0 :=
    (cpow_ne_zero_iff.mpr (Or.inl hz0) : z ^ (1 / 2 : ℂ) ≠ 0)
  have hπh : (π : ℂ) ^ (1 / 2 : ℂ) ≠ 0 :=
    (cpow_ne_zero_iff.mpr (Or.inl hπ) : (π : ℂ) ^ (1 / 2 : ℂ) ≠ 0)
  have hpar : -(1 / 2 : ℂ) + 1 = 1 / 2 := by ring
  simp only [besselJ_eq_regularized]
  rw [hpar, regularized0F1_half_eq_cos, cpow_half_recip_div_two hz, Gamma_one_half_eq,
    cpow_half_two_div_pi_z hz, cpow_half_div_pi]
  field [hz0, hg, h2h, hzh, hπh]

/-- Kummer's second transformation (AAR (4.1.12), p. 191), in regularized `₀F₁` form. -/
theorem kummerM_eq_exp_mul_regularized0F1 {ν : ℂ}
    (hν : ∀ k : ℕ, ν + 1 ≠ -k) (h2ν : ∀ k : ℕ, 2 * ν + 1 ≠ -k) (z : ℂ) :
    kummerM (ν + 1 / 2) (2 * ν + 1) z =
      Gamma (ν + 1) * exp (z / 2) * regularizedHGFun (∅ : Multiset ℂ) {ν + 1} (z ^ 2 / 16) := by
  let F := regularizedHGFun (∅ : Multiset ℂ) {ν + 1}
  let u := fun w : ℂ => w ^ 2 / 16
  let g := fun w : ℂ => Gamma (ν + 1) * exp (w / 2)
  let r := fun w : ℂ => w / 8
  let f := fun w : ℂ => g w * F (u w)
  have hu (w : ℂ) : HasDerivAt u (r w) w := by
    convert! ((hasDerivAt_id w).pow 2).div_const 16 using 1
    simp [r]
    ring
  have hg (w : ℂ) : HasDerivAt g (g w / 2) w := by
    convert! (((hasDerivAt_id w).div_const 2).cexp).const_mul (Gamma (ν + 1)) using 1
    dsimp [g]
    ring
  have hF (w : ℂ) : HasDerivAt F (deriv F w) w :=
    (analyticAt_regularized0F1 (ν + 1) w).differentiableAt.hasDerivAt
  have hF' (w : ℂ) : HasDerivAt (deriv F) (deriv (deriv F) w) w :=
    (analyticAt_regularized0F1 (ν + 1) w).deriv.differentiableAt.hasDerivAt
  have hfirst (w : ℂ) : deriv f w = g w * ((1 / 2) * F (u w) + r w * deriv F (u w)) := by
    change deriv (g * F ∘ u) w = _
    rw [((hg w).mul ((hF (u w)).comp w (hu w))).deriv]
    simp only [Function.comp_apply]
    ring
  have hdeq : deriv f = g * ((fun w => (1 / 2) * (F ∘ u) w) + r * deriv F ∘ u) := funext hfirst
  have hode (w : ℂ) : w * deriv (deriv f) w + (2 * ν + 1 - w) * deriv f w -
      (ν + 1 / 2) * f w = 0 := by
    have hr : HasDerivAt r (1 / 8) w := (hasDerivAt_id w).div_const 8
    have ht := (hg w).mul
      ((((hF (u w)).comp w (hu w)).const_mul (1 / 2)).add
        (hr.mul ((hF' (u w)).comp w (hu w))))
    rw [hdeq, ht.deriv]
    have he := regularized0F1_ode (ν + 1) (u w)
    change u w * deriv (deriv F) (u w) + (ν + 1) * deriv F (u w) - F (u w) = 0 at he
    dsimp only [f, r, Pi.mul_apply, Pi.add_apply, Function.comp_apply]
    linear_combination (norm := (dsimp [u]; ring)) (w * g w / 4) * he
  have hfa (w : ℂ) : AnalyticAt ℂ f w := by
    apply AnalyticAt.mul
    · dsimp [g]
      fun_prop
    · exact (analyticAt_regularized0F1 (ν + 1) _).comp (by dsimp [u]; fun_prop)
  have hs := hasFPowerSeriesOnBall_kummerM (a := ν + 1 / 2) h2ν
  have hma (w : ℂ) : AnalyticAt ℂ (kummerM (ν + 1 / 2) (2 * ν + 1)) w :=
    hs.analyticAt_of_mem (by simp)
  have hmode (w : ℂ) : w * deriv (deriv (kummerM (ν + 1 / 2) (2 * ν + 1))) w +
      (2 * ν + 1 - w) * deriv (kummerM (ν + 1 / 2) (2 * ν + 1)) w -
      (ν + 1 / 2) * kummerM (ν + 1 / 2) (2 * ν + 1) w = 0 := by
    have he := hs.ode_of_recurrence (A := 0) (B := 1) (C := ν + 1 / 2) (D := 2 * ν + 1)
      (fun n => by rw [kummerMCoeff_recurrence h2ν]; ring) (z := w) (by simp)
    simpa using he
  have hzero : f 0 = kummerM (ν + 1 / 2) (2 * ν + 1) 0 := by
    simp [f, g, F, u, Complex.regularizedHGFun_zero, regularizedHGFunCoeff, Gamma_ne_zero hν]
  exact (congrFun (confluent_ode_unique h2ν hfa hma hode hmode hzero) z).symm

/-- Relation of `J_ν` to Kummer's function (AAR §4.5). -/
@[dlmf 10.16.E5]
theorem besselJ_eq_kummerM {ν z : ℂ} (hν : ∀ k : ℕ, ν + 1 ≠ -k)
    (h2ν : ∀ k : ℕ, 2 * ν + 1 ≠ -k) :
    besselJ ν z =
      (z / 2) ^ ν * exp (-I * z) / Gamma (ν + 1) *
        kummerM (ν + 1 / 2) (2 * ν + 1) (2 * I * z) := by
  rw [kummerM_eq_exp_mul_regularized0F1 hν h2ν]
  have hu : (2 * I * z) ^ 2 / 16 = -(z ^ 2 / 4) := by rw [mul_pow, mul_pow, I_sq]; ring
  rw [hu, show (2 * I * z) / 2 = I * z by ring]
  simp only [neg_mul, exp_neg]
  simp only [besselJ_eq_regularized]
  field [Gamma_ne_zero hν, exp_ne_zero (I * z)]

end DLMF.Bessel
