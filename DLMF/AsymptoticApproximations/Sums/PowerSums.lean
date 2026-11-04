/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AsymptoticApproximations.Sums.Basic
public import DLMF.Zeta.Riemann
public import DLMFMathlib.Analysis.Asymptotics.AsymptoticExpansion
public import DLMFMathlib.Analysis.Asymptotics.IntegralComparison
public import DLMFMathlib.RingTheory.Binomial
public import Mathlib.Analysis.Analytic.Binomial

/-!
# Power-sum asymptotics

This file proves the asymptotic expansion of the power sums `∑_{j=1}^{n-1} j^α` (DLMF 2.10.7)
and the remainder bound of DLMF §2.10(i), from the zeta Euler–Maclaurin formula.

## Main results

* `powerSum_asymptotic`: for real `α ≠ -1`, `∑_{j=1}^{n-1} j^α ∼ ζ(-α) + n^{α+1}/(α+1)
  ∑_{s ≥ 0} (α+1 choose s) B_s n^{-s}` (DLMF 2.10.7).
* `powerSum_remainder_bound`: the remainder of 2.10.7 is bounded by the first neglected term
  (DLMF §2.10(i)).

## Implementation notes

The exact formula `DLMF.Zeta.riemannZeta_eq_eulerMaclaurin` supplies the constant and the finite
Bernoulli expansion; its bounded periodic-Bernoulli integral gives the asymptotic error.
Mathlib's `Complex.ofReal_choose` handles the generalized-binomial coefficient casts.
For the remainder bound, the consecutive remainders after `s < 2m` and `s < 2m + 2` are written,
by `DLMF.Zeta.integral_Ioi_periodicBernoulli_div_cpow_recursion`, as integrals of
`B̃_{2k}(t) - B_{2k}` against powers of `t`; these have opposite signs by the Fourier series of
`B_{2k}` (Mathlib's `hasSum_one_div_nat_pow_mul_cos`).
-/

@[expose] public noncomputable section

open Finset MeasureTheory Set Filter Asymptotics Complex
open scoped Topology Nat

namespace DLMF.AsymptoticApproximations

/-- The even power-sum coefficient agrees with the falling-factorial coefficient
in the zeta Euler–Maclaurin expansion. -/
private lemma powerSum_evenCoeff {α : ℝ} (hα : α ≠ -1) {k : ℕ} (hk : 1 ≤ k) :
    powSumCoeff α (2 * k) =
      -Ring.choose (-α + 2 * k - 2) (2 * k - 1) * (bernoulli (2 * k) : ℝ) / (2 * k) := by
  have hα1 : α + 1 ≠ 0 := by intro h; apply hα; linarith
  have hk0 : (2 * (k : ℝ)) ≠ 0 := by positivity
  have hrec := Ring.natCast_mul_choose_succ (α + 1) (2 * k - 1)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ 2 * k)] at hrec
  rw [Nat.cast_sub (by omega : 1 ≤ 2 * k)] at hrec
  simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, show α + 1 - 1 = α by ring] at hrec
  rw [powSumCoeff, Ring.choose_neg_add_even_sub_two α hk]
  field_simp [hα1, hk0]
  linear_combination (bernoulli (2 * k) : ℝ) * hrec

/-- Group the full Bernoulli truncation into its constant, half-endpoint and even
terms; all the remaining odd Bernoulli numbers vanish. -/
private lemma powerSum_partialSum_even {α : ℝ} (hα : α ≠ -1) (m n : ℕ) :
    (∑ j ∈ range (2 * m + 2), powSumScale α j n * powSumCoeff α j) =
      (n : ℝ) ^ (α + 1) / (α + 1) - (n : ℝ) ^ α / 2 +
        ∑ k ∈ Icc 1 m, (n : ℝ) ^ (α + 1 - 2 * k) * powSumCoeff α (2 * k) := by
  have hα1 : α + 1 ≠ 0 := by intro h; apply hα; linarith
  induction m with
  | zero =>
    norm_num [powSumScale, powSumCoeff, sum_range_succ,
      Ring.choose_zero_right, Ring.choose_one_right]
    field_simp
    ring
  | succ m ih =>
    rw [show 2 * (m + 1) + 2 = (2 * m + 2) + 1 + 1 by ring,
      sum_range_succ, sum_range_succ, ih, sum_Icc_succ_top (by omega : 1 ≤ m + 1)]
    have hodd : powSumCoeff α (2 * m + 3) = 0 := by
      rw [powSumCoeff, bernoulli_eq_zero_of_odd ⟨m + 1, by omega⟩ (by omega)]
      simp
    rw [hodd, mul_zero, add_zero]
    rw [show 2 * (m + 1) = 2 * m + 2 by ring]
    simp only [powSumScale, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    ring_nf

/-- Rewrite the real-axis periodic-Bernoulli remainder without complex powers. -/
private lemma powerSum_em_integral (α : ℝ) (m n : ℕ) (hn : 1 ≤ n) :
    (∫ t in Ioi (n : ℝ),
      (periodicBernoulli (2 * m + 1) t : ℂ) /
        (t : ℂ) ^ (-(α : ℂ) + 2 * m + 1)) =
      ((∫ t in Ioi (n : ℝ), periodicBernoulli (2 * m + 1) t *
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
    Ring.choose (-(α : ℂ) + 2 * k - 2) (2 * k - 1) *
        ((bernoulli (2 * k) : ℂ) / (2 * k)) * (n : ℂ) ^ (1 - -(α : ℂ) - 2 * k) =
      -(((n : ℝ) ^ (α + 1 - 2 * k) * powSumCoeff α (2 * k) : ℝ) : ℂ) := by
  rw [show -(α : ℂ) + 2 * k - 2 = ((-α + 2 * k - 2 : ℝ) : ℂ) by push_cast; ring,
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
        ∑ j ∈ range (2 * m + 2), powSumScale α j n * powSumCoeff α j =
      Ring.choose (-α + 2 * m) (2 * m + 1) *
        ∫ t in Ioi (n : ℝ), periodicBernoulli (2 * m + 1) t *
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
      Ring.choose (-(α : ℂ) + 2 * k - 2) (2 * k - 1) *
        ((bernoulli (2 * k) : ℂ) / (2 * k)) * (n : ℂ) ^ (1 - -(α : ℂ) - 2 * k)) =
      -((∑ k ∈ Icc 1 m, (n : ℝ) ^ (α + 1 - 2 * k) * powSumCoeff α (2 * k) : ℝ) : ℂ) := by
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
  have hchoose : Ring.choose (-(α : ℂ) + 2 * m) (2 * m + 1) =
      ((Ring.choose (-α + 2 * m) (2 * m + 1) : ℝ) : ℂ) := by
    rw [show -(α : ℂ) + 2 * m = ((-α + 2 * m : ℝ) : ℂ) by push_cast; ring,
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
      periodicBernoulli (2 * m + 1) t * t ^ (α - 2 * m - 1)) =O[atTop]
        (fun x : ℝ => x ^ (α - 2 * m)) := by
  obtain ⟨C, hC⟩ := DLMF.Zeta.exists_abs_periodicBernoulli_le (2 * m + 1)
  have h := isBigO_integral_Ioi_bdd_mul_rpow
    (f := fun t => (periodicBernoulli (2 * m + 1) t : ℂ))
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
      ∑ j ∈ range (2 * m + 2), powSumScale α j n * powSumCoeff α j) =O[atTop]
        (powSumScale α (2 * m + 1)) := by
  have h := ((powerSum_integral_isBigO hmα).const_mul_left
    (Ring.choose (-α + 2 * m) (2 * m + 1))).comp_tendsto tendsto_natCast_atTop_atTop
  refine h.congr' ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact (powerSum_eq_truncation_add_remainder hα hm hn hmα).symm
  · apply Eventually.of_forall
    intro n
    dsimp [powSumScale]
    congr 1
    push_cast
    ring

/-- Later terms of the power-sum scale are bounded by earlier terms at infinity. -/
private lemma powerSum_scale_isBigO (α : ℝ) {N M : ℕ} (hNM : N ≤ M) :
    powSumScale α M =O[atTop] powSumScale α N := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  simp only [powSumScale, Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _), one_mul]
  apply Real.rpow_le_rpow_of_exponent_le hn'
  have hNM' : (N : ℝ) ≤ M := by exact_mod_cast hNM
  linarith

/-- DLMF 2.10.7: for real `α ≠ -1`, as `n → ∞`,
`∑_{j=1}^{n-1} j^α ∼ ζ(-α) + n^{α+1}/(α+1) ∑_{s ≥ 0} (α+1 choose s) B_s n^{-s}`. -/
@[dlmf 2.10.E7]
theorem powerSum_asymptotic {α : ℝ} (hα : α ≠ -1) :
    HasAsymptoticExpansion atTop (powSumScale α) (powSumCoeff α)
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
      powSumScale α j n * powSumCoeff α j) =O[atTop] powSumScale α N := by
    apply IsBigO.fun_sum
    intro j hj
    exact ((powerSum_scale_isBigO α (mem_Ico.mp hj).1).const_mul_left
      (powSumCoeff α j)).congr_left fun n => mul_comm _ _
  simp only [smul_eq_mul]
  refine (hr.add htail).congr_left fun n => ?_
  have hsum := sum_range_add_sum_Ico
    (fun j => powSumScale α j n * powSumCoeff α j) (by omega : N ≤ 2 * m + 2)
  rw [← hsum]
  ring

open scoped _root_.Real in
/-- `(-1)^{k+1}(B̃_{2k}(x) - B_{2k}) ≤ 0`, from the Fourier series of `B_{2k}`. -/
private lemma neg_one_pow_mul_periodicBernoulli_sub_nonpos {k : ℕ} (hk : 1 ≤ k) (x : ℝ) :
    (-1 : ℝ) ^ (k + 1) * (periodicBernoulli (2 * k) x - bernoulli (2 * k)) ≤ 0 := by
  have hx : Int.fract x ∈ Icc (0 : ℝ) 1 := ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩
  have h1 := hasSum_one_div_nat_pow_mul_cos (by omega : k ≠ 0) hx
  have h0 := hasSum_one_div_nat_pow_mul_cos (by omega : k ≠ 0)
    (x := 0) ⟨le_rfl, zero_le_one⟩
  have hle := hasSum_le (fun n => ?_) (h1.sub h0) hasSum_zero
  · rw [← mul_sub] at hle
    change _ * (bernoulliFun (2 * k) (Int.fract x) - bernoulliFun (2 * k) 0) ≤ 0 at hle
    rw [bernoulliFun_eval_zero] at hle
    have hc : 0 < (2 * π) ^ (2 * k) / 2 / ((2 * k)! : ℝ) := by positivity
    have e : (-1 : ℝ) ^ (k + 1) * (2 * π) ^ (2 * k) / 2 / ((2 * k)! : ℝ) =
        (2 * π) ^ (2 * k) / 2 / ((2 * k)! : ℝ) * (-1) ^ (k + 1) := by ring
    rw [e, mul_assoc] at hle
    exact nonpos_of_mul_nonpos_right (by simpa [periodicBernoulli] using hle) hc
  · simp only [mul_zero, Real.cos_zero]
    rw [← mul_sub]
    refine mul_nonpos_of_nonneg_of_nonpos (by positivity) ?_
    linarith [Real.cos_le_one (2 * π * n * Int.fract x)]

/-- The real form of `DLMF.Zeta.integral_Ioi_periodicBernoulli_div_cpow_recursion`. -/
private lemma integral_Ioi_periodicBernoulli_rpow_recursion {p : ℕ} (hp : 1 ≤ p) {β : ℝ}
    (hβ : β < -1) {a : ℝ} (ha : 0 < a) :
    (p + 1) * ∫ x in Ioi a, periodicBernoulli p x * x ^ β =
      -(periodicBernoulli (p + 1) a * a ^ β) +
        -β * ∫ x in Ioi a, periodicBernoulli (p + 1) x * x ^ (β - 1) := by
  have h := DLMF.Zeta.integral_Ioi_periodicBernoulli_div_cpow_recursion hp
    (w := ((-β : ℝ) : ℂ)) (by simp; linarith) ha
  have hconv : ∀ (q : ℕ) (γ : ℝ), (∫ x in Ioi a,
      (periodicBernoulli q x : ℂ) / (x : ℂ) ^ ((-γ : ℝ) : ℂ)) =
      ((∫ x in Ioi a, periodicBernoulli q x * x ^ γ : ℝ) : ℂ) := by
    intro q γ
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun x (hx : a < x) => ?_
    have hx0 : 0 < x := ha.trans hx
    rw [← Complex.ofReal_cpow hx0.le, Real.rpow_neg hx0.le]
    push_cast
    rw [div_eq_mul_inv, inv_inv]
  rw [hconv, show ((-β : ℝ) : ℂ) + 1 = ((-(β - 1) : ℝ) : ℂ) by push_cast; ring, hconv,
    ← Complex.ofReal_cpow ha.le, Real.rpow_neg ha.le] at h
  apply Complex.ofReal_injective
  push_cast at h ⊢
  rw [h]
  field_simp

/-- `B̃_q x · x^γ` is integrable on `(a, ∞)` for `γ < -1`, `a > 0`. -/
private lemma integrableOn_periodicBernoulli_mul_rpow (q : ℕ) {γ : ℝ} (hγ : γ < -1) {a : ℝ}
    (ha : 0 < a) : IntegrableOn (fun x => periodicBernoulli q x * x ^ γ) (Ioi a) := by
  obtain ⟨C, hC⟩ := DLMF.Zeta.exists_abs_periodicBernoulli_le q
  exact Integrable.bdd_mul (c := C) (integrableOn_Ioi_rpow_of_lt hγ ha)
    (measurable_periodicBernoulli q).aestronglyMeasurable
    (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hC x)

/-- Splitting off the constant term `B_q` of `∫_a^∞ B̃_q(x) x^γ dx`. -/
private lemma integral_periodicBernoulli_mul_rpow_eq (q : ℕ) {γ : ℝ} (hγ : γ < -1) {a : ℝ}
    (ha : 0 < a) :
    ∫ x in Ioi a, periodicBernoulli q x * x ^ γ =
      (∫ x in Ioi a, (periodicBernoulli q x - bernoulli q) * x ^ γ) +
        bernoulli q * (-a ^ (γ + 1) / (γ + 1)) := by
  rw [← integral_Ioi_rpow_of_lt hγ ha, ← integral_const_mul, ← integral_add]
  · refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    ring
  · exact ((integrableOn_periodicBernoulli_mul_rpow q hγ ha).sub
      ((integrableOn_Ioi_rpow_of_lt hγ ha).const_mul _)).congr_fun
      (fun x _ => by simp only [Pi.sub_apply]; ring) measurableSet_Ioi
  · exact (integrableOn_Ioi_rpow_of_lt hγ ha).const_mul _

/-- Sign of `∫_a^∞ (B̃_{2k}(x) - B_{2k}) x^γ dx`. -/
private lemma neg_one_pow_mul_integral_periodicBernoulli_sub_nonpos {k : ℕ} (hk : 1 ≤ k)
    (γ a : ℝ) (ha : 0 < a) :
    (-1 : ℝ) ^ (k + 1) * ∫ x in Ioi a, (periodicBernoulli (2 * k) x - bernoulli (2 * k)) *
      x ^ γ ≤ 0 := by
  rw [← integral_const_mul]
  refine setIntegral_nonpos measurableSet_Ioi fun x (hx : a < x) => ?_
  rw [← mul_assoc]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_one_pow_mul_periodicBernoulli_sub_nonpos hk x)
    (Real.rpow_nonneg (ha.trans hx).le _)

/-- `B̃_q(n) = B_q` at the integers. -/
private lemma periodicBernoulli_natCast_eq_bernoulli (q n : ℕ) :
    periodicBernoulli q n = bernoulli q := by
  simp [periodicBernoulli, bernoulliFun_eval_zero]

/-- The two consecutive remainders `E_m` (after `s < 2m`) and `E_{m+1}` (after `s < 2m + 2`)
of 2.10.7 have opposite signs. -/
private lemma powerSum_remainder_mul_nonpos {α : ℝ} (hα : α ≠ -1) {m : ℕ} (hm : 1 ≤ m)
    (hmα : (α + 1) / 2 ≤ m) {n : ℕ} (hn : 1 ≤ n) :
    ((∑ j ∈ Ico 1 n, (j : ℝ) ^ α) - (riemannZeta (-(α : ℂ))).re -
        ∑ s ∈ range (2 * m), powSumScale α s n * powSumCoeff α s) *
      (Ring.choose (-α + 2 * m) (2 * m + 1) *
        ∫ t in Ioi (n : ℝ), periodicBernoulli (2 * m + 1) t * t ^ (α - 2 * m - 1)) ≤ 0 := by
  have hmα' : α ≤ 2 * m - 1 := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rcases hmα'.lt_or_eq with hlt | heq
  · -- the remainder after `s < 2m + 2`
    have hfull := powerSum_eq_truncation_add_remainder hα hm hn (by linarith)
    rw [show 2 * m + 2 = 2 * m + 1 + 1 by ring, sum_range_succ, sum_range_succ] at hfull
    have hodd : powSumCoeff α (2 * m + 1) = 0 := by
      rw [powSumCoeff, bernoulli_eq_zero_of_odd ⟨m, rfl⟩ (by omega)]
      simp
    have hsc : powSumScale α (2 * m) n = (n : ℝ) ^ (α + 1 - 2 * m) := by
      rw [powSumScale]; push_cast; ring_nf
    rw [hodd, powerSum_evenCoeff hα hm, hsc] at hfull
    -- the recursion for `p = 2m + 1`
    have hr1 := integral_Ioi_periodicBernoulli_rpow_recursion (p := 2 * m + 1) (by omega)
      (β := α - 2 * m - 1) (by linarith) hn0
    rw [integral_periodicBernoulli_mul_rpow_eq (2 * m + 1 + 1) (γ := α - 2 * m - 1 - 1)
      (by linarith) hn0, periodicBernoulli_natCast_eq_bernoulli] at hr1
    have hs1 := neg_one_pow_mul_integral_periodicBernoulli_sub_nonpos (k := m + 1) (by omega)
      (α - 2 * m - 1 - 1) n hn0
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring] at hs1
    set I2 := ∫ x in Ioi (n : ℝ), (periodicBernoulli (2 * m + 1 + 1) x -
      bernoulli (2 * m + 1 + 1)) * x ^ (α - 2 * m - 1 - 1)
    -- the recursion for `p = 2m`
    have hr0 := integral_Ioi_periodicBernoulli_rpow_recursion (p := 2 * m) (by omega)
      (β := α - 2 * m) (by linarith) hn0
    rw [integral_periodicBernoulli_mul_rpow_eq (2 * m) (γ := α - 2 * m) (by linarith) hn0,
      periodicBernoulli_natCast_eq_bernoulli, bernoulli_eq_zero_of_odd ⟨m, rfl⟩ (by omega),
      show α - 2 * m - 1 = α - 2 * (m : ℝ) - 1 by ring] at hr0
    have hs0 := neg_one_pow_mul_integral_periodicBernoulli_sub_nonpos (k := m) hm (α - 2 * m) n
      hn0
    set J := ∫ x in Ioi (n : ℝ), (periodicBernoulli (2 * m) x - bernoulli (2 * m)) *
      x ^ (α - 2 * m)
    -- binomial relations
    have hc1 := Ring.natCast_mul_choose_succ (-α + 2 * m) (2 * m)
    have hc2 := Ring.natCast_mul_choose_succ (-α + 2 * m - 1) (2 * m - 1)
    rw [show 2 * m - 1 + 1 = 2 * m by omega, Nat.cast_sub (by omega),
      show -α + 2 * m - 1 - 1 = -α + 2 * m - 2 by ring] at hc2
    rw [show α - 2 * (m : ℝ) - 1 - 1 + 1 = α - 2 * m - 1 by ring] at hr1
    rw [show α - 2 * (m : ℝ) + 1 = α + 1 - 2 * m by ring] at hr0
    push_cast at hr0 hr1 hc1 hc2 hfull
    set C := Ring.choose (-α + 2 * (m : ℝ)) (2 * m + 1) with hCdef
    set I := ∫ t in Ioi (n : ℝ), periodicBernoulli (2 * m + 1) t * t ^ (α - 2 * (m : ℝ) - 1)
      with hIdef
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    have hw1 : (0 : ℝ) < 2 * m - α - 1 := by linarith
    -- the sign of `I`
    have hI : (-1 : ℝ) ^ m * I ≤ 0 := by
      have hβ : α - 2 * (m : ℝ) - 1 ≠ 0 := by linarith
      have hI2 : (2 * m + 2) * I = -(α - 2 * m - 1) * I2 := by
        field_simp at hr1
        linear_combination hr1
      have e : (-1 : ℝ) ^ m * I = (2 * m + 1 - α) / (2 * m + 2) *
          ((-1) ^ (m + 1 + 1) * I2) := by
        field_simp
        rw [pow_succ, pow_succ]
        linear_combination (-1 : ℝ) ^ m * hI2
      rw [e]
      exact mul_nonpos_of_nonneg_of_nonpos (div_nonneg (by linarith) (by positivity)) hs1
    have hJI : J * I ≤ 0 := by
      rw [pow_succ] at hs0
      rcases neg_one_pow_eq_or ℝ m with h | h <;> rw [h] at hs0 hI <;> nlinarith
    set E := (∑ j ∈ Ico 1 n, (j : ℝ) ^ α) - (riemannZeta (-(α : ℂ))).re -
        ∑ s ∈ range (2 * m), powSumScale α s n * powSumCoeff α s
    set N := (n : ℝ) ^ (α + 1 - 2 * m) with hN
    set b := (bernoulli (2 * m) : ℝ)
    set ch1 := Ring.choose (-α + 2 * (m : ℝ) - 1) (2 * m)
    set ch2 := Ring.choose (-α + 2 * (m : ℝ) - 2) (2 * m - 1)
    have hA : 2 * m * E = 2 * m * (C * I) - N * ch2 * b := by
      field_simp at hfull
      linear_combination hfull
    have hB : (2 * m + 1) * ((2 * m - α - 1) * J + b * N) =
        (2 * m - α - 1) * (2 * m - α) * I := by
      have hne : α + 1 - 2 * (m : ℝ) ≠ 0 := by linarith
      field_simp at hr0
      linear_combination -hr0
    have hE : E * (2 * m - α) = C * (2 * m + 1) * J := by
      have h : 2 * m * (2 * m - α - 1) * (E * (2 * m - α) - C * (2 * m + 1) * J) = 0 := by
        linear_combination (2 * m - α - 1) * (2 * m - α) * hA - 2 * m * C * hB +
          (2 * m - α) * N * b * hc2 + 2 * m * b * N * hc1
      have h0 : 2 * (m : ℝ) * (2 * m - α - 1) ≠ 0 := by positivity
      linear_combination (mul_eq_zero.1 h).resolve_left h0
    have hw : (0 : ℝ) < 2 * m - α := by linarith
    have h2 : C ^ 2 * (2 * m + 1) * (J * I) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hJI
    have h3 : E * (C * I) * (2 * m - α) = C ^ 2 * (2 * m + 1) * (J * I) := by
      linear_combination (C * I) * hE
    nlinarith
  · have hC : Ring.choose (-α + 2 * m) (2 * m + 1) = 0 := by
      rw [heq, show -(2 * (m : ℝ) - 1) + 2 * m = 1 by ring]
      have h := Ring.natCast_mul_choose_succ (1 : ℝ) (2 * m)
      rw [sub_self, show 2 * m = (2 * m - 1) + 1 by omega, Ring.choose_zero_succ,
        mul_zero] at h
      have hne : ((2 * m - 1 + 1 : ℕ) : ℝ) + 1 ≠ 0 := by positivity
      rw [show 2 * m - 1 + 1 = 2 * m by omega] at h hne
      exact (mul_eq_zero.1 h).resolve_left hne
    rw [hC]
    simp
/-- DLMF §2.10(i) (remainder of 2.10.7): truncating 2.10.7 after `s = 2m - 1`, where
`m ≥ (α+1)/2`, leaves a remainder bounded in absolute value by the first neglected term
(`s = 2m`) and of the same sign, for every `n ≥ 1`. -/
@[dlmf 2.10.i]
theorem powerSum_remainder_bound {α : ℝ} (hα : α ≠ -1) {m : ℕ} (hm : 1 ≤ m)
    (hmα : (α + 1) / 2 ≤ m) {n : ℕ} (hn : 1 ≤ n) :
    let R := ∑ j ∈ Ico 1 n, (j : ℝ) ^ α - (riemannZeta (-α)).re -
      ∑ s ∈ range (2 * m), powSumScale α s n * powSumCoeff α s
    0 ≤ R * (powSumScale α (2 * m) n * powSumCoeff α (2 * m)) ∧
      |R| ≤ |powSumScale α (2 * m) n * powSumCoeff α (2 * m)| := by
  intro R
  have hfull := powerSum_eq_truncation_add_remainder hα hm hn (by linarith)
  have hodd : powSumCoeff α (2 * m + 1) = 0 := by
    rw [powSumCoeff, bernoulli_eq_zero_of_odd ⟨m, rfl⟩ (by omega)]
    simp
  rw [show 2 * m + 2 = 2 * m + 1 + 1 by ring, sum_range_succ, sum_range_succ, hodd, mul_zero,
    add_zero] at hfull
  have hmul := powerSum_remainder_mul_nonpos hα hm hmα hn
  set K := Ring.choose (-α + 2 * m) (2 * m + 1) *
    ∫ t in Ioi (n : ℝ), periodicBernoulli (2 * m + 1) t * t ^ (α - 2 * m - 1)
  have hT : powSumScale α (2 * m) n * powSumCoeff α (2 * m) = R - K := by
    simp only [R]; linear_combination -hfull
  have hRK : R * K ≤ 0 := hmul
  rw [hT]
  clear_value R K
  refine ⟨by nlinarith [sq_nonneg R], ?_⟩
  rw [← sq_le_sq]
  nlinarith [sq_nonneg K]

end DLMF.AsymptoticApproximations
