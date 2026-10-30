/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AsymptoticApproximations.Sums.Basic
public import DLMF.Zeta.Riemann
public import DLMFMathlib.RingTheory.Binomial
public import DLMFMathlib.Analysis.Asymptotics.IntegralComparison
public import DLMFMathlib.Analysis.Asymptotics.AsymptoticExpansion
public import Mathlib.Analysis.Analytic.Binomial

/-!
# Power-sum asymptotics from the zeta Euler–Maclaurin formula

The exact formula `DLMF.Zeta.riemannZeta_eq_eulerMaclaurin` supplies the constant
and the finite Bernoulli expansion. Its bounded periodic-Bernoulli integral gives
the asymptotic error without invoking any admitted Hurwitz-zeta asymptotics.
Mathlib's `Complex.ofReal_choose` handles the generalized-binomial coefficient casts.
-/

@[expose] public noncomputable section

open Finset MeasureTheory Set Filter Asymptotics Complex
open scoped Topology Nat

namespace DLMF.AsymptoticApproximations

/-- The legacy zeta binomial coefficient is Mathlib's generalized binomial coefficient. -/
private lemma zeta_binomial_eq_choose (z : ℂ) (n : ℕ) :
    DLMF.Zeta.z25a_gbinom z n = Ring.choose z n :=
  (Ring.choose_eq_descPochhammer_div z n).symm

/-- The even power-sum coefficient agrees with the falling-factorial coefficient
in the zeta Euler–Maclaurin expansion. -/
private lemma powerSum_evenCoeff {α : ℝ} (hα : α ≠ -1) {k : ℕ} (hk : 1 ≤ k) :
    g2b_powSumCoeff α (2 * k) =
      -Ring.choose (-α + 2 * k - 2) (2 * k - 1) * (bernoulli (2 * k) : ℝ) / (2 * k) := by
  have hα1 : α + 1 ≠ 0 := by intro h; apply hα; linarith
  have hk0 : (2 * (k : ℝ)) ≠ 0 := by positivity
  have hrec := Ring.natCast_mul_choose_succ (α + 1) (2 * k - 1)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ 2 * k)] at hrec
  rw [Nat.cast_sub (by omega : 1 ≤ 2 * k)] at hrec
  simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, show α + 1 - 1 = α by ring] at hrec
  rw [g2b_powSumCoeff, Ring.choose_neg_add_even_sub_two α hk]
  field_simp [hα1, hk0]
  linear_combination (bernoulli (2 * k) : ℝ) * hrec

/-- Group the full Bernoulli truncation into its constant, half-endpoint and even
terms; all the remaining odd Bernoulli numbers vanish. -/
private lemma powerSum_partialSum_even {α : ℝ} (hα : α ≠ -1) (m n : ℕ) :
    (∑ j ∈ range (2 * m + 2), g2b_powScale α j n * g2b_powSumCoeff α j) =
      (n : ℝ) ^ (α + 1) / (α + 1) - (n : ℝ) ^ α / 2 +
        ∑ k ∈ Icc 1 m, (n : ℝ) ^ (α + 1 - 2 * k) * g2b_powSumCoeff α (2 * k) := by
  have hα1 : α + 1 ≠ 0 := by intro h; apply hα; linarith
  induction m with
  | zero =>
    norm_num [g2b_powScale, g2b_powSumCoeff, sum_range_succ,
      Ring.choose_zero_right, Ring.choose_one_right]
    field_simp
    ring
  | succ m ih =>
    rw [show 2 * (m + 1) + 2 = (2 * m + 2) + 1 + 1 by ring,
      sum_range_succ, sum_range_succ, ih, sum_Icc_succ_top (by omega : 1 ≤ m + 1)]
    have hodd : g2b_powSumCoeff α (2 * m + 3) = 0 := by
      rw [g2b_powSumCoeff, bernoulli_eq_zero_of_odd ⟨m + 1, by omega⟩ (by omega)]
      simp
    rw [hodd, mul_zero, add_zero]
    rw [show 2 * (m + 1) = 2 * m + 2 by ring]
    simp only [g2b_powScale, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    ring_nf

/-- Rewrite the real-axis periodic-Bernoulli remainder without complex powers. -/
private lemma powerSum_em_integral (α : ℝ) (m n : ℕ) (hn : 1 ≤ n) :
    (∫ t in Ioi (n : ℝ),
      (DLMF.BernoulliEuler.periodicBernoulliB (2 * m + 1) t : ℂ) /
        (t : ℂ) ^ (-(α : ℂ) + 2 * m + 1)) =
      ((∫ t in Ioi (n : ℝ), DLMF.BernoulliEuler.periodicBernoulliB (2 * m + 1) t *
        t ^ (α - 2 * m - 1) : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have ht' : (n : ℝ) < t := ht
  have ht0 : 0 < t := by linarith
  dsimp only
  rw [div_eq_mul_inv, ← Complex.cpow_neg,
    show -(-(α : ℂ) + 2 * m + 1) = ((α - 2 * m - 1 : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow ht0.le, Complex.ofReal_mul]

/-- Each finite zeta correction is the negative of the corresponding real
power-sum Bernoulli term. -/
private lemma powerSum_em_term {α : ℝ} (hα : α ≠ -1) {k : ℕ} (hk : 1 ≤ k)
    (n : ℕ) :
    DLMF.Zeta.z25a_gbinom (-(α : ℂ) + 2 * k - 2) (2 * k - 1) *
        ((bernoulli (2 * k) : ℂ) / (2 * k)) * (n : ℂ) ^ (1 - -(α : ℂ) - 2 * k) =
      -(((n : ℝ) ^ (α + 1 - 2 * k) * g2b_powSumCoeff α (2 * k) : ℝ) : ℂ) := by
  rw [zeta_binomial_eq_choose,
    show -(α : ℂ) + 2 * k - 2 = ((-α + 2 * k - 2 : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_choose,
    show (1 : ℂ) - -(α : ℂ) - 2 * k = ((α + 1 - 2 * k : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_natCast n, ← Complex.ofReal_cpow (Nat.cast_nonneg n), powerSum_evenCoeff hα hk]
  push_cast
  ring

/-- Euler–Maclaurin gives an exact remainder formula for real power sums, with
the zeta value as the constant term. -/
private lemma powerSum_eq_truncation_add_remainder {α : ℝ} (hα : α ≠ -1) {m n : ℕ}
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hmα : α < 2 * m) :
    (∑ j ∈ Ico 1 n, (j : ℝ) ^ α) - (riemannZeta (-(α : ℂ))).re -
        ∑ j ∈ range (2 * m + 2), g2b_powScale α j n * g2b_powSumCoeff α j =
      Ring.choose (-α + 2 * m) (2 * m + 1) *
        ∫ t in Ioi (n : ℝ), DLMF.BernoulliEuler.periodicBernoulliB (2 * m + 1) t *
          t ^ (α - 2 * m - 1) := by
  have hs : -(α : ℂ) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    apply hα
    linarith
  have he := (DLMF.Zeta.riemannZeta_eq_eulerMaclaurin (s := -(α : ℂ)) hm hn
    (by simp; linarith) hs).2
  have hsum : (∑ k ∈ Icc 1 n, 1 / (k : ℂ) ^ (-(α : ℂ))) =
      (((∑ k ∈ Ico 1 n, (k : ℝ) ^ α) + (n : ℝ) ^ α : ℝ) : ℂ) := by
    rw [← Ico_add_one_right_eq_Icc, sum_Ico_succ_top hn, Complex.ofReal_add]
    simp_rw [one_div, Complex.cpow_neg, inv_inv, ← Complex.ofReal_natCast,
      ← Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_sum]
  have hsumEven : (∑ k ∈ Icc 1 m,
      DLMF.Zeta.z25a_gbinom (-(α : ℂ) + 2 * k - 2) (2 * k - 1) *
        ((bernoulli (2 * k) : ℂ) / (2 * k)) * (n : ℂ) ^ (1 - -(α : ℂ) - 2 * k)) =
      -((∑ k ∈ Icc 1 m, (n : ℝ) ^ (α + 1 - 2 * k) * g2b_powSumCoeff α (2 * k) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum, ← sum_neg_distrib]
    apply sum_congr rfl
    intro k hk
    exact powerSum_em_term hα (mem_Icc.mp hk).1 n
  have hfirst : (n : ℂ) ^ (1 - -(α : ℂ)) / (-(α : ℂ) - 1) =
      -(((n : ℝ) ^ (α + 1) / (α + 1) : ℝ) : ℂ) := by
    rw [show (1 : ℂ) - -(α : ℂ) = ((α + 1 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_natCast n, ← Complex.ofReal_cpow (Nat.cast_nonneg n)]
    push_cast
    rw [show -(α : ℂ) - 1 = -((α : ℂ) + 1) by ring, div_neg]
  have hhalf : (1 / 2 : ℂ) * (n : ℂ) ^ (- -(α : ℂ)) =
      (((n : ℝ) ^ α / 2 : ℝ) : ℂ) := by
    rw [neg_neg, ← Complex.ofReal_natCast n, ← Complex.ofReal_cpow (Nat.cast_nonneg n)]
    push_cast
    ring
  have hchoose : DLMF.Zeta.z25a_gbinom (-(α : ℂ) + 2 * m) (2 * m + 1) =
      ((Ring.choose (-α + 2 * m) (2 * m + 1) : ℝ) : ℂ) := by
    rw [zeta_binomial_eq_choose,
      show -(α : ℂ) + 2 * m = ((-α + 2 * m : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_choose]
  rw [hsum, hfirst, hhalf, hsumEven, hchoose, powerSum_em_integral α m n hn] at he
  have hr := congrArg Complex.re he
  simp only [Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.ofReal_re,
    ← Complex.ofReal_mul] at hr
  rw [powerSum_partialSum_even hα]
  linear_combination -hr

/-- Bound the real periodic-Bernoulli tail by integrating its bounded coefficient
against the decaying real power. -/
private lemma powerSum_integral_isBigO {α : ℝ} {m : ℕ} (hmα : α < 2 * m) :
    (fun x : ℝ => ∫ t in Ioi x,
      DLMF.BernoulliEuler.periodicBernoulliB (2 * m + 1) t * t ^ (α - 2 * m - 1)) =O[atTop]
        (fun x : ℝ => x ^ (α - 2 * m)) := by
  obtain ⟨C, hC⟩ := DLMF.Zeta.q25a_periodicBernoulliB_bound (2 * m + 1)
  have h := isBigO_integral_Ioi_bdd_mul_rpow
    (f := fun t => (DLMF.BernoulliEuler.periodicBernoulliB (2 * m + 1) t : ℂ))
    (r := α - 2 * m - 1) (fun t => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hC t)
    (by linarith)
  simp only [← Complex.ofReal_mul, integral_complex_ofReal, Complex.isBigO_ofReal_left] at h
  convert h using 1
  ext x
  congr 1
  ring

/-- The exact zeta remainder gives a power bound for every sufficiently long
even Bernoulli truncation. -/
private lemma powerSum_remainder_isBigO {α : ℝ} (hα : α ≠ -1) {m : ℕ}
    (hm : 1 ≤ m) (hmα : α < 2 * m) :
    (fun n : ℕ => (∑ j ∈ Ico 1 n, (j : ℝ) ^ α) - (riemannZeta (-(α : ℂ))).re -
      ∑ j ∈ range (2 * m + 2), g2b_powScale α j n * g2b_powSumCoeff α j) =O[atTop]
        (g2b_powScale α (2 * m + 1)) := by
  have h := ((powerSum_integral_isBigO hmα).const_mul_left
    (Ring.choose (-α + 2 * m) (2 * m + 1))).comp_tendsto tendsto_natCast_atTop_atTop
  refine h.congr' ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact (powerSum_eq_truncation_add_remainder hα hm hn hmα).symm
  · apply Eventually.of_forall
    intro n
    dsimp [g2b_powScale]
    congr 1
    push_cast
    ring

/-- Later terms of the power-sum scale are bounded by earlier terms at infinity. -/
private lemma powerSum_scale_isBigO (α : ℝ) {N M : ℕ} (hNM : N ≤ M) :
    g2b_powScale α M =O[atTop] g2b_powScale α N := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  simp only [g2b_powScale, Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _), one_mul]
  apply Real.rpow_le_rpow_of_exponent_le hn'
  have hNM' : (N : ℝ) ≤ M := by exact_mod_cast hNM
  linarith

/-- DLMF 2.10.7: for real `α ≠ -1`, as `n → ∞`,
`∑_{j=1}^{n-1} j^α ∼ ζ(-α) + n^{α+1}/(α+1) ∑_{s ≥ 0} (α+1 choose s) B_s n^{-s}`. -/
@[dlmf 2.10.E7]
theorem powerSum_asymptotic {α : ℝ} (hα : α ≠ -1) :
    HasAsymptoticExpansion atTop (g2b_powScale α) (g2b_powSumCoeff α)
      (fun n : ℕ => ∑ j ∈ Ico 1 n, (j : ℝ) ^ α - (riemannZeta (-α)).re) := by
  intro N
  obtain ⟨k, hk⟩ := exists_nat_gt α
  let m := N + k + 1
  have hm : 1 ≤ m := by dsimp [m]; omega
  have hmα : α < 2 * m := by
    dsimp [m]
    push_cast
    linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N), (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hNM : N ≤ 2 * m + 1 := by dsimp [m]; omega
  have hr := (powerSum_remainder_isBigO hα hm hmα).trans (powerSum_scale_isBigO α hNM)
  have htail : (fun n => ∑ j ∈ Ico N (2 * m + 2),
      g2b_powScale α j n * g2b_powSumCoeff α j) =O[atTop] g2b_powScale α N := by
    apply IsBigO.fun_sum
    intro j hj
    exact ((powerSum_scale_isBigO α (mem_Ico.mp hj).1).const_mul_left
      (g2b_powSumCoeff α j)).congr_left fun n => mul_comm _ _
  simp only [smul_eq_mul]
  refine (hr.add htail).congr_left fun n => ?_
  have hsum := sum_range_add_sum_Ico
    (fun j => g2b_powScale α j n * g2b_powSumCoeff α j) (by omega : N ≤ 2 * m + 2)
  rw [← hsum]
  ring

/-- DLMF §2.10(i) (remainder of 2.10.7): truncating 2.10.7 after `s = 2m - 1`, where
`m ≥ (α+1)/2`, leaves a remainder bounded in absolute value by the first neglected term
(`s = 2m`) and of the same sign, for every `n ≥ 1`. -/
@[dlmf 2.10.i]
theorem powerSum_remainder_bound {α : ℝ} (hα : α ≠ -1) {m : ℕ} (hm : 1 ≤ m)
    (hmα : (α + 1) / 2 ≤ m) {n : ℕ} (hn : 1 ≤ n) :
    let R := ∑ j ∈ Ico 1 n, (j : ℝ) ^ α - (riemannZeta (-α)).re -
      ∑ s ∈ range (2 * m), g2b_powScale α s n * g2b_powSumCoeff α s
    0 ≤ R * (g2b_powScale α (2 * m) n * g2b_powSumCoeff α (2 * m)) ∧
      |R| ≤ |g2b_powScale α (2 * m) n * g2b_powSumCoeff α (2 * m)| := by
  sorry

end DLMF.AsymptoticApproximations
