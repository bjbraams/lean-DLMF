/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module
public import DLMF.EllipticIntegrals.NomeAsymptotics
import DLMF.Theta.Identities
import DLMFMathlib.Analysis.Asymptotics.AsymptoticInversion
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Tactic

/-!
# The fourth-root modulus expansion of the elliptic nome

The variable `λ = (1 - √k′)/(2(1 + √k′))` equals the quotient
`θ₂(0|4τ)/(2θ₃(0|4τ))` for a real modulus `0 < k < 1`. The even-odd decomposition of
theta constants gives sparse power series in the nome. Their remainder bounds and
polynomial reversion give the expansion through degree seventeen.

## Main results

* `jacobiNome_lambda_theta_relation`: `λ` as a quotient of sparse nome series.
* `jacobiNome_isBigO_lambda`: the expansion with remainder `O(λ²¹)` (DLMF 19.5.6–19.5.7).

The theta-constant decomposition uses `DLMF.Theta.jacobiThetaThreeTau_eq_four_mul_tau`.
The estimates use the sparse-series bounds and polynomial remainders of `DLMFMathlib`.
-/

open Complex Set Filter Asymptotics
open scoped Real Topology
namespace DLMF.EllipticIntegrals
open DLMF.JacobiElliptic DLMF.Elliptic
private theorem jacobiThetaTwoTau_four_mul_eq_nome_sum {τ : ℂ} (hτ : 0 < τ.im)
    (hq : ‖cexp (π * I * τ)‖ < 1) :
    jacobiThetaTwoTau 0 (4 * τ) =
      2 * cexp (π * I * τ) * ∑' n : ℕ, cexp (π * I * τ) ^ (4 * n * (n + 1)) := by
  have hs := summable_nat_pow_of_le_exponent hq (fun n => 4 * n * (n + 1))
    (fun n => by nlinarith)
  have h4 : 0 < (4 * τ).im := by simp; linarith
  have H := DLMF.Theta.jacobiThetaTwoTau_hasSum_cos 0 h4
  have he (n : ℕ) : 2 * cexp (π * I * (4 * τ) * ((n : ℂ) + 1 / 2) ^ 2) *
      cos ((2 * n + 1) * 0) = (2 * cexp (π * I * τ)) *
        cexp (π * I * τ) ^ (4 * n * (n + 1)) := by
    simp only [mul_zero, cos_zero, mul_one]
    rw [← Complex.exp_nat_mul]
    conv_rhs => rw [mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  exact (H.congr_fun fun n => (he n).symm).unique (hs.hasSum.mul_left _)
private theorem jacobiThetaThreeTau_four_mul_eq_nome_sum {τ : ℂ} (hτ : 0 < τ.im)
    (hq : ‖cexp (π * I * τ)‖ < 1) :
    jacobiThetaThreeTau 0 (4 * τ) =
      2 * (∑' n : ℕ, cexp (π * I * τ) ^ (4 * n ^ 2)) - 1 := by
  have hs := summable_nat_pow_of_le_exponent hq (fun n => 4 * n ^ 2)
    (fun n => by nlinarith)
  have h4 : 0 < (4 * τ).im := by simp; linarith
  have H := DLMF.Theta.jacobiThetaThreeTau_hasSum_cos 0 h4
  have he (n : ℕ) : 2 * cexp (π * I * (4 * τ) * ((n : ℂ) + 1) ^ 2) *
      cos (2 * ((n : ℂ) + 1) * 0) = 2 * cexp (π * I * τ) ^ (4 * (n + 1) ^ 2) := by
    simp only [mul_zero, cos_zero, mul_one]
    rw [← Complex.exp_nat_mul]
    congr 2
    push_cast
    ring
  have H1 := (H.congr_fun fun n => (he n).symm).tsum_eq
  rw [tsum_mul_left] at H1
  have H2 := hs.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, zero_pow (by decide : (2 : ℕ) ≠ 0),
    mul_zero, pow_zero] at H2
  linear_combination -H1 + 2 * H2
/-- The fourth-root modulus variable `λ` as a quotient of sparse nome series. -/
public theorem jacobiNome_lambda_theta_relation {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1)
    (hq : ‖jacobiNome k‖ < 1) :
    (((1 - Real.sqrt (Real.sqrt (1 - k ^ 2))) /
      (2 * (1 + Real.sqrt (Real.sqrt (1 - k ^ 2)))) : ℝ) : ℂ) =
      jacobiNome k * (∑' n : ℕ, jacobiNome k ^ (4 * n * (n + 1))) /
        (2 * (∑' n : ℕ, jacobiNome k ^ (4 * n ^ 2)) - 1) := by
  obtain ⟨t, ht, hτ, -, hcomp, -⟩ := exists_jacobiTau_eq_I_mul_of_real hk0 hk1
  have hB : 0 < jacobiThetaThreeImag t :=
    lt_of_lt_of_le zero_lt_one (one_le_jacobiThetaThreeImag ht)
  have hC := jacobiThetaFourImag_pos ht
  have hkc : (jacobiThetaFourImag t / jacobiThetaThreeImag t) ^ 2 =
      Real.sqrt (1 - k ^ 2) := by
    apply ofReal_injective
    rw [jacobiComodulusOfTau, jacobiComodulus,
      jacobiThetaFourTau_zero_I_mul_eq_imag, jacobiThetaThreeTau_zero_I_mul_eq_imag,
      show (1 : ℂ) - (k : ℂ) ^ 2 = ((1 - k ^ 2 : ℝ) : ℂ) by push_cast; ring,
      Carlson.ofReal_cpow_half (by nlinarith)] at hcomp
    simpa only [ofReal_div, ofReal_pow, div_pow] using hcomp
  have hroot : Real.sqrt (Real.sqrt (1 - k ^ 2)) =
      jacobiThetaFourImag t / jacobiThetaThreeImag t := by
    rw [← hkc, Real.sqrt_sq (div_pos hC hB).le]
  have hτpos := jacobiTau_im_pos (ofReal_mem_jacobiModulusDomain hk0 hk1)
  have h2 := jacobiThetaTwoTau_four_mul_eq_nome_sum hτpos
    (by simpa only [← jacobiNome_eq_exp_tau] using hq)
  have h3 := jacobiThetaThreeTau_four_mul_eq_nome_sum hτpos
    (by simpa only [← jacobiNome_eq_exp_tau] using hq)
  simp only [← jacobiNome_eq_exp_tau] at h2 h3
  have hsum := DLMF.Theta.jacobiThetaThreeTau_eq_four_mul_tau 0 (jacobiTau k) hτpos
  simp only [mul_zero] at hsum
  have hdiff := DLMF.Theta.jacobiThetaFourTau_zero_eq_four_mul_tau hτpos
  have hBr : jacobiThetaThreeTau 0 (jacobiTau k) = (jacobiThetaThreeImag t : ℂ) := by
    rw [hτ, jacobiThetaThreeTau_zero_I_mul_eq_imag]
  have hCr : jacobiThetaFourTau 0 (jacobiTau k) = (jacobiThetaFourImag t : ℂ) := by
    rw [hτ, jacobiThetaFourTau_zero_I_mul_eq_imag]
  rw [hroot]
  push_cast
  rw [← hBr, ← hCr, hsum, hdiff]
  rw [h2, h3]
  have hn : jacobiThetaThreeTau 0 (jacobiTau k) ≠ 0 :=
    jacobiThetaThreeTau_zero_ne_zero hτpos
  have h4 : 0 < (4 * jacobiTau k).im := by simp; linarith
  have hn4 := jacobiThetaThreeTau_zero_ne_zero h4
  rw [h3] at hn4
  rw [hsum, h2, h3] at hn
  field_simp [hn, hn4]
  ring
end DLMF.EllipticIntegrals

namespace DLMF.EllipticIntegrals
private theorem lambda_forward_remainder :
    (fun q : ℂ => q * (∑' n : ℕ, q ^ (4 * n * (n + 1))) /
        (2 * (∑' n : ℕ, q ^ (4 * n ^ 2)) - 1) -
        (q - 2 * q ^ 5 + 5 * q ^ 9 - 10 * q ^ 13 + 18 * q ^ 17)) =O[𝓝 0]
      fun q => q ^ 21 := by
  let S : ℂ → ℂ := fun q => ∑' n : ℕ, q ^ (4 * n * (n + 1))
  let D : ℂ → ℂ := fun q => 2 * (∑' n : ℕ, q ^ (4 * n ^ 2)) - 1
  let S₀ : ℂ → ℂ := fun q => 1 + q ^ 8
  let D₀ : ℂ → ℂ := fun q => 1 + 2 * q ^ 4 + 2 * q ^ 16
  let P : ℂ → ℂ := fun q => q - 2 * q ^ 5 + 5 * q ^ 9 - 10 * q ^ 13 + 18 * q ^ 17
  have hS : (fun q => S q - S₀ q) =O[𝓝 0] fun q => q ^ 20 := by
    simpa [S, S₀, Finset.sum_range_succ] using
      isBigO_tsum_nat_pow_sub_sum (K := ℂ) (fun n => 4 * n * (n + 1)) 2 20 (by
        intro n; nlinarith)
  have hD : (fun q => D q - D₀ q) =O[𝓝 0] fun q => q ^ 20 := by
    have H := (isBigO_tsum_nat_pow_sub_sum (K := ℂ) (fun n => 4 * n ^ 2) 3 20
      (by intro n; nlinarith)).const_mul_left (2 : ℂ)
    convert H using 1
    funext q
    simp only [D, D₀, Finset.sum_range_succ, Finset.sum_range_zero,
      zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, pow_zero, one_pow, mul_one]
    ring
  have hD1 : Tendsto D (𝓝 0) (𝓝 1) := by
    have H := (isBigO_tsum_nat_pow_sub_sum (K := ℂ) (fun n => 4 * n ^ 2) 1 1
      (by intro n; nlinarith)).trans_tendsto (by simpa using (continuous_pow 1).tendsto (0 : ℂ))
    have H1 : Tendsto (fun q : ℂ => ∑' n : ℕ, q ^ (4 * n ^ 2)) (𝓝 0) (𝓝 1) := by
      simpa [Finset.sum_range_succ] using H.add_const 1
    convert ((tendsto_const_nhds (x := (2 : ℂ))).mul H1).sub_const (1 : ℂ) using 1
    norm_num [D]
  have hP : P =O[𝓝 0] fun q : ℂ => q := by
    have hc : Continuous (fun q : ℂ => 1 - 2 * q ^ 4 + 5 * q ^ 8 - 10 * q ^ 12 +
        18 * q ^ 16) := by fun_prop
    have H := (hc.tendsto 0).isBigO_one ℂ
    convert (isBigO_refl (fun q : ℂ => q) (𝓝 0)).mul H using 1 <;>
      funext q <;> (try dsimp only [P]) <;> ring
  have hpoly : (fun q : ℂ => q * S₀ q - D₀ q * P q) =O[𝓝 0]
      fun q => q ^ 21 := by
    have hc : Continuous (fun q : ℂ => -36 * q ^ 12 + 20 * q ^ 8 - 10 * q ^ 4 - 32) := by
      fun_prop
    have H := (hc.tendsto 0).isBigO_one ℂ
    convert (isBigO_refl (fun q : ℂ => q ^ 21) (𝓝 0)).mul H using 1 <;>
      funext q <;> (try dsimp only [S₀, D₀, P]) <;> ring
  have hnum : (fun q => q * S q - D q * P q) =O[𝓝 0] fun q => q ^ 21 := by
    have H1 : (fun q => q * (S q - S₀ q)) =O[𝓝 0] fun q => q ^ 21 := by
      simpa only [← pow_succ', Nat.reduceAdd] using
        (isBigO_refl (fun q : ℂ => q) (𝓝 0)).mul hS
    have H2 : (fun q => (D q - D₀ q) * P q) =O[𝓝 0] fun q => q ^ 21 := by
      simpa only [← pow_succ, Nat.reduceAdd] using hD.mul hP
    convert (H1.sub H2).add hpoly using 1
    funext q
    ring
  have hinv : (fun q => (D q)⁻¹) =O[𝓝 0] fun _ => (1 : ℂ) :=
    (hD1.inv₀ (by norm_num)).isBigO_one ℂ
  have hn : ∀ᶠ q in 𝓝 (0 : ℂ), D q ≠ 0 :=
    hD1.eventually_ne (by norm_num : (1 : ℂ) ≠ 0)
  apply (hnum.mul hinv).congr'
  · filter_upwards [hn] with q hq
    dsimp only [D] at hq
    dsimp only [S, D, P]
    field_simp [hq]
  · exact Eventually.of_forall fun q => by simp
private theorem lambda_inverse_composition_remainder :
    let P : ℂ → ℂ := fun q => q - 2 * q ^ 5 + 5 * q ^ 9 - 10 * q ^ 13 + 18 * q ^ 17
    (fun q : ℂ => P q + 2 * P q ^ 5 + 15 * P q ^ 9 + 150 * P q ^ 13 +
      1707 * P q ^ 17 - q) =O[𝓝 0] fun q => q ^ 21 := by
  let A : Polynomial ℂ := 1 - 2 * Polynomial.X + 5 * Polynomial.X ^ 2 -
    10 * Polynomial.X ^ 3 + 18 * Polynomial.X ^ 4
  let B : Polynomial ℂ := A + 2 * Polynomial.X * A ^ 5 + 15 * Polynomial.X ^ 2 * A ^ 9 +
    150 * Polynomial.X ^ 3 * A ^ 13 + 1707 * Polynomial.X ^ 4 * A ^ 17 - 1
  have hb : ∀ n < 5, B.coeff n = 0 := by
    intro n hn
    dsimp only [B, A]
    ring_nf
    interval_cases n <;> norm_num [Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.coeff_X_pow, Polynomial.coeff_mul, Polynomial.coeff_one, Polynomial.coeff_X]
  have hq4 : Tendsto (fun q : ℂ => q ^ 4) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_pow 4).tendsto (0 : ℂ)
  have H := AsymptoticInversion.isBigO_eval_of_coeff_eq_zero hq4 hb
  convert (isBigO_refl (fun q : ℂ => q) (𝓝 0)).mul H using 1 <;>
    funext q <;> (try simp only [B, A, Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat,
      Polynomial.eval_one]) <;> ring
end DLMF.EllipticIntegrals

namespace DLMF.EllipticIntegrals
open DLMF.JacobiElliptic
/-- DLMF 19.5.6–19.5.7: with `λ = (1 - √k')/(2(1 + √k'))`,
`q = λ + 2λ⁵ + 15λ⁹ + 150λ¹³ + 1707λ¹⁷ + ⋯` as `k → 0+` (the remainder is `O(λ²¹)`). -/
@[dlmf 19.5.E6, dlmf 19.5.E7]
public theorem jacobiNome_isBigO_lambda :
    let lam : ℝ → ℝ := fun k =>
      (1 - Real.sqrt (Real.sqrt (1 - k ^ 2))) / (2 * (1 + Real.sqrt (Real.sqrt (1 - k ^ 2))))
    (fun k : ℝ => jacobiNome k - ((lam k + 2 * lam k ^ 5 + 15 * lam k ^ 9 + 150 * lam k ^ 13 +
        1707 * lam k ^ 17 : ℝ) : ℂ)) =O[𝓝[>] 0] fun k : ℝ => lam k ^ 21 := by
  let lam : ℝ → ℝ := fun k =>
    (1 - Real.sqrt (Real.sqrt (1 - k ^ 2))) / (2 * (1 + Real.sqrt (Real.sqrt (1 - k ^ 2))))
  let L : ℝ → ℂ := fun k => (lam k : ℂ)
  let q : ℝ → ℂ := fun k => jacobiNome k
  let S : ℂ → ℂ := fun z => ∑' n : ℕ, z ^ (4 * n * (n + 1))
  let D : ℂ → ℂ := fun z => 2 * (∑' n : ℕ, z ^ (4 * n ^ 2)) - 1
  let p : ℝ → ℂ := fun k => q k - 2 * q k ^ 5 + 5 * q k ^ 9 -
    10 * q k ^ 13 + 18 * q k ^ 17
  have hq : Tendsto q (𝓝[>] 0) (𝓝 0) := Real.tendsto_jacobiNome_zero
  have hs : Tendsto S (𝓝 0) (𝓝 1) := tendsto_tsum_nat_pow_zero
    (fun n => 4 * n * (n + 1)) (by norm_num) (by intro n; nlinarith)
  have hd : Tendsto D (𝓝 0) (𝓝 1) := by
    have H := tendsto_tsum_nat_pow_zero (K := ℂ) (fun n => 4 * n ^ 2)
      (by norm_num) (by intro n; nlinarith)
    convert ((tendsto_const_nhds (x := (2 : ℂ))).mul H).sub_const 1 using 1
    norm_num [D]
  have he : ∀ᶠ k in 𝓝[>] (0 : ℝ), L k = q k * S (q k) / D (q k) := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1),
      hq.eventually (Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1))]
      with k hk hkq
    exact jacobiNome_lambda_theta_relation hk.1 hk.2
      (by simpa only [Metric.mem_ball, dist_zero_right] using hkq)
  have hl : Tendsto L (𝓝[>] 0) (𝓝 0) := by
    have H := (hq.mul (hs.comp hq)).div (hd.comp hq) (by norm_num)
    have H0 : Tendsto (fun k => q k * S (q k) / D (q k)) (𝓝[>] 0) (𝓝 0) := by
      simpa only [zero_mul, zero_div, mul_one, Function.comp_def, Pi.div_def] using H
    exact H0.congr' (he.mono fun _ h => h.symm)
  have hnS := (hs.comp hq).eventually_ne (by norm_num : (1 : ℂ) ≠ 0)
  have hnD := (hd.comp hq).eventually_ne (by norm_num : (1 : ℂ) ≠ 0)
  have hb : (fun k => D (q k) / S (q k)) =O[𝓝[>] 0] fun _ => (1 : ℂ) :=
    ((hd.comp hq).div (hs.comp hq) (by norm_num)).isBigO_one ℂ
  have hnome : q =O[𝓝[>] 0] L := by
    apply ((isBigO_refl L (𝓝[>] 0)).mul hb).congr'
    · filter_upwards [he, hnS, hnD] with k hk hkS hkD
      dsimp only [Function.comp_def] at hkS hkD
      rw [hk]
      field_simp [hkS, hkD]
    · exact Eventually.of_forall fun k => by simp
  have hforward : (fun k => L k - p k) =O[𝓝[>] 0] fun k => q k ^ 21 := by
    apply (lambda_forward_remainder.comp_tendsto hq).congr'
    · filter_upwards [he] with k hk
      dsimp only [Function.comp_def]
      rw [hk]
    · exact Eventually.of_forall fun _ => rfl
  have hp : Tendsto p (𝓝[>] 0) (𝓝 0) := by
    have H := (((hq.sub ((tendsto_const_nhds (x := (2 : ℂ))).mul (hq.pow 5))).add
      ((tendsto_const_nhds (x := (5 : ℂ))).mul (hq.pow 9))).sub
      ((tendsto_const_nhds (x := (10 : ℂ))).mul (hq.pow 13))).add
      ((tendsto_const_nhds (x := (18 : ℂ))).mul (hq.pow 17))
    simpa only [zero_pow (by decide : (5 : ℕ) ≠ 0), zero_pow (by decide : (9 : ℕ) ≠ 0),
      zero_pow (by decide : (13 : ℕ) ≠ 0), zero_pow (by decide : (17 : ℕ) ≠ 0),
      mul_zero, sub_zero, add_zero] using H
  let Q : Polynomial ℂ := Polynomial.X + 2 * Polynomial.X ^ 5 + 15 * Polynomial.X ^ 9 +
    150 * Polynomial.X ^ 13 + 1707 * Polynomial.X ^ 17
  have hQ : (fun k => Q.eval (L k) - Q.eval (p k)) =O[𝓝[>] 0]
      fun k => L k - p k := by
    simpa only [Function.comp_def] using
      ((Q.hasStrictDerivAt 0).hasStrictFDerivAt.isBigO_sub.comp_tendsto (hl.prodMk_nhds hp))
  have H : (fun k => q k - Q.eval (L k)) =O[𝓝[>] 0] fun k => q k ^ 21 := by
    convert ((hQ.trans hforward).add
      (lambda_inverse_composition_remainder.comp_tendsto hq)).neg_left using 1
    funext k
    dsimp only [Q, p, Function.comp_def]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_ofNat]
    ring
  have Hfinal := H.trans (hnome.pow 21)
  apply IsBigO.of_norm_right
  simpa only [Q, L, q, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_ofNat, norm_pow, norm_real, ofReal_add,
    ofReal_mul, ofReal_pow, ofReal_ofNat] using Hfinal.norm_right
end DLMF.EllipticIntegrals
