/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module
public import DLMF.EllipticIntegrals.LegendreIdentities
import DLMF.JacobiElliptic.NomeBounds
import DLMF.Theta.Identities
import Mathlib.Tactic

/-!
# Logarithmic bounds for the complementary elliptic ratio

Positive theta-series comparisons bound Jacobi's nome, giving the two-sided logarithmic
bounds for `πK′(k)/(2K(k))` in DLMF 19.9.5. The real theta-constant inversion formula supplies
the relations between the modulus, its complement, and the nome.
-/

open Complex Set Filter Asymptotics
open scoped Real Topology
namespace DLMF.EllipticIntegrals
open DLMF.JacobiElliptic DLMF.Elliptic
/-- DLMF 19.9.5: `ln((1 + √k')²/k) < π K'(k)/(2K(k)) < ln(2(1 + k')/k)` for `0 < k < 1`, with
DLMF's complementary integral `K'(k)` (`complementaryEllipticK`, equal to `K(k')` here). -/
@[dlmf 19.9.E5]
public theorem pi_mul_complementaryEllipticK_div_bounds {k : ℝ}
    (hk0 : 0 < k) (hk1 : k < 1) :
    Real.log ((1 + Real.sqrt (Real.sqrt (1 - k ^ 2))) ^ 2 / k) <
        π * (complementaryEllipticK k).re / (2 * (completeEllipticK k).re) ∧
      π * (complementaryEllipticK k).re / (2 * (completeEllipticK k).re) <
        Real.log (2 * (1 + Real.sqrt (1 - k ^ 2)) / k) := by
  obtain ⟨t, ht, hρ⟩ := exists_jacobiModulusImag_eq hk0 hk1
  obtain ⟨-, -, hτ, -, hcomp, -, hKr, hKpr⟩ := jacobiModulusImag_spec ht
  rw [hρ] at hτ hcomp hKr hKpr
  let q : ℝ := Real.exp (-(π * t))
  let B := jacobiThetaThreeImag t
  let C := jacobiThetaFourImag t
  let P := jacobiThetaTwoReducedQ q
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos, ht])
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (one_le_jacobiThetaThreeImag ht)
  have hC : 0 < C := jacobiThetaFourImag_pos ht
  have he : Real.exp (-(π * t) / 4) ^ 4 = q := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hrel : k ^ 2 * B ^ 4 = q * P ^ 4 := by
    rw [← hρ, jacobiModulusImag, div_pow, div_pow]
    dsimp only [B, P]
    simp only [← pow_mul, Nat.reduceMul]
    rw [div_mul_cancel₀ _ (pow_ne_zero _ hB.ne'),
      jacobiThetaTwoImag_eq_exp_mul_reducedQ ht, mul_pow, he]
  have hkc : (C / B) ^ 2 = Real.sqrt (1 - k ^ 2) := by
    apply ofReal_injective
    rw [jacobiComodulusOfTau, jacobiComodulus,
      jacobiThetaFourTau_zero_I_mul_eq_imag, jacobiThetaThreeTau_zero_I_mul_eq_imag,
      show (1 : ℂ) - (k : ℂ) ^ 2 = ((1 - k ^ 2 : ℝ) : ℂ) by push_cast; ring,
      Carlson.ofReal_cpow_half (by nlinarith)] at hcomp
    simpa only [ofReal_div, ofReal_pow, div_pow] using hcomp
  have hroot : Real.sqrt (Real.sqrt (1 - k ^ 2)) = C / B := by
    rw [← hkc, Real.sqrt_sq (div_pos hC hB).le]
  have hsum : B + C = 2 * Real.jacobiThetaThreeNullQ (q ^ 4) := by
    have hτp : 0 < (I * (t : ℂ)).im := by simpa
    have H1 := DLMF.Theta.jacobiThetaThreeTau_eq_four_mul_tau 0 (I * t) hτp
    have H2 := DLMF.Theta.jacobiThetaFourTau_zero_eq_four_mul_tau hτp
    simp only [mul_zero, jacobiThetaThreeTau_zero_I_mul_eq_imag,
      jacobiThetaFourTau_zero_I_mul_eq_imag] at H1 H2
    have HE : (4 : ℂ) * (I * t) = I * ((4 * t : ℝ) : ℂ) := by push_cast; ring
    rw [HE, jacobiThetaThreeTau_zero_I_mul_eq_imag] at H1 H2
    have H : (B : ℂ) + C = 2 * (jacobiThetaThreeImag (4 * t) : ℂ) := by
      dsimp only [B, C]
      linear_combination H1 + H2
    have heq : Real.exp (-(π * (4 * t))) = q ^ 4 := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [jacobiThetaThreeImag, heq] at H
    exact_mod_cast H
  have hPl : B + C < P := by
    rw [hsum]
    exact two_mul_jacobiThetaThreeNullQ_pow_four_lt_jacobiThetaTwoReducedQ hq0 hq1
  have hPu : P ^ 2 < 2 * (B ^ 2 + C ^ 2) := by
    have H := jacobiThetaTwoReducedQ_lt_two_mul_jacobiThetaThreeNullQ
      (pow_pos hq0 2) (pow_lt_one₀ hq0.le hq1 (by decide : (2 : ℕ) ≠ 0))
    have hT : 0 < Real.jacobiThetaThreeNullQ (q ^ 2) := by
      exact lt_of_lt_of_le zero_lt_one (Real.one_le_jacobiThetaThreeNullQ
        (pow_pos hq0 2) (pow_lt_one₀ hq0.le hq1 (by decide : (2 : ℕ) ≠ 0)))
    have Hm := mul_lt_mul_of_pos_right H (mul_pos zero_lt_two hT)
    have HP := jacobiThetaTwoReducedQ_sq hq0 hq1
    have HT := Real.jacobiThetaThreeNullQ_sq_add_jacobiThetaFourNullQ_sq hq0 hq1
    dsimp only [P, B, C, jacobiThetaThreeImag, jacobiThetaFourImag]
    dsimp only [q] at HP HT Hm
    nlinarith only [HP, HT, Hm]
  let a : ℝ := (1 + Real.sqrt (Real.sqrt (1 - k ^ 2))) ^ 2 / k
  let b : ℝ := 2 * (1 + Real.sqrt (1 - k ^ 2)) / k
  have ha : 0 < a := by dsimp only [a]; positivity
  have hb : 0 < b := by dsimp only [b]; positivity
  have haeq : a = (B + C) ^ 2 / (k * B ^ 2) := by
    dsimp only [a]
    rw [hroot]
    field_simp
  have hbeq : b = 2 * (B ^ 2 + C ^ 2) / (k * B ^ 2) := by
    dsimp only [b]
    rw [← hkc]
    field_simp
  have hqa : q * a ^ 2 < 1 := by
    rw [haeq, div_pow, ← mul_div_assoc]
    apply (div_lt_one (by positivity : (0 : ℝ) < (k * B ^ 2) ^ 2)).mpr
    rw [mul_pow, ← pow_mul]
    have H := pow_lt_pow_left₀ hPl (by positivity : (0 : ℝ) ≤ B + C) (by decide : (4 : ℕ) ≠ 0)
    have HH := mul_lt_mul_of_pos_left H hq0
    rw [← hrel] at HH
    simpa only [← pow_mul, Nat.reduceMul] using HH
  have hqb : 1 < q * b ^ 2 := by
    rw [hbeq, div_pow, ← mul_div_assoc]
    apply (one_lt_div (by positivity : (0 : ℝ) < (k * B ^ 2) ^ 2)).mpr
    rw [mul_pow, ← pow_mul]
    have H := pow_lt_pow_left₀ hPu (sq_nonneg P) (by decide : (2 : ℕ) ≠ 0)
    have HH := mul_lt_mul_of_pos_left H hq0
    rw [← pow_mul, ← hrel] at HH
    simpa only [← pow_mul, Nat.reduceMul] using HH
  have hla := Real.log_lt_log (mul_pos hq0 (pow_pos ha 2)) hqa
  have hlb := Real.log_lt_log zero_lt_one hqb
  rw [Real.log_one, Real.log_mul hq0.ne' (pow_ne_zero 2 ha.ne'), Real.log_pow] at hla
  rw [Real.log_one, Real.log_mul hq0.ne' (pow_ne_zero 2 hb.ne'), Real.log_pow] at hlb
  have hlq : Real.log q = -(π * t) := Real.log_exp _
  rw [hlq] at hla hlb
  have hmid : π * (complementaryEllipticK k).re / (2 * (completeEllipticK k).re) = π * t / 2 := by
    rw [complementaryEllipticK_ofReal hk0, completeEllipticK_ofReal (by nlinarith)]
    simp only [ofReal_re]
    rw [hKr, hKpr]
    field_simp [Real.pi_ne_zero, show jacobiThetaThreeImag t ≠ 0 from hB.ne']
  dsimp only [a, b] at hla hlb
  rw [hmid]
  constructor <;> linarith only [hla, hlb]
end DLMF.EllipticIntegrals
