/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Analysis.PSeries

/-!
# Infinite products (DLMF §5.8)

The Weierstrass product 5.8.2 is `one_div_Gamma_eq_tprod` in `Basic.lean`.
Gauss's limit 5.8.1 is Mathlib `GammaSeq_tendsto_Gamma`. The remaining
identities are the modulus product and the general balanced Gamma product.
-/

@[expose] public section

open Complex Filter
open scoped Topology Real

noncomputable section

namespace DLMF.Gamma

/-- `∑ₖ y²/(x+k)²` converges. -/
theorem summable_sq_div_add_sq (x y : ℝ) : Summable fun k : ℕ => y ^ 2 / (x + k) ^ 2 := by
  have hg : Summable fun k : ℕ => 4 * y ^ 2 * (1 / (k : ℝ) ^ 2) :=
    (Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left _
  refine Summable.of_norm_bounded_eventually_nat hg ?_
  filter_upwards [eventually_ge_atTop (⌈2 * |x|⌉₊ + 1)] with k hk
  have hk' : 2 * |x| + 1 ≤ k := by
    have := Nat.le_ceil (2 * |x|)
    have : ((⌈2 * |x|⌉₊ + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast hk
    push_cast at this
    linarith
  have hk0 : (0 : ℝ) < k := by linarith [abs_nonneg x]
  have hxk2 : k / 2 ≤ x + k := by linarith [neg_abs_le x]
  have hxk0 : (0 : ℝ) < x + k := by linarith
  rw [Real.norm_of_nonneg (by positivity), div_le_iff₀ (by positivity : (0 : ℝ) < (x + k) ^ 2)]
  have : (k : ℝ) ^ 2 / 4 ≤ (x + k) ^ 2 := by nlinarith
  field_simp
  nlinarith [sq_nonneg y, mul_le_mul_of_nonneg_left this (sq_nonneg y)]

/-- `∏ₖ (1 + y²/(x+k)²)` converges. -/
theorem multipliable_one_add_sq_div_add_sq (x y : ℝ) :
    Multipliable fun k : ℕ => 1 + y ^ 2 / (x + k) ^ 2 :=
  Real.multipliable_one_add_of_summable (summable_sq_div_add_sq x y)

open Finset in
/-- Both products follow from Gauss's limit `Γ(s) = lim nˢ n!/(s(s+1)⋯(s+n))`: the ratios of
the Gauss sequences are exactly the partial products. -/
@[dlmf 5.8.E3]
theorem Gamma_div_Gamma_add_mul_I_sq {x y : ℝ} (hx : ∀ k : ℕ, (x : ℂ) ≠ -k) :
    ‖(Real.Gamma x : ℂ) / Complex.Gamma (x + I * y)‖ ^ 2 =
      ∏' k : ℕ, (1 + y ^ 2 / (x + k) ^ 2) := by
  have hxk : ∀ k : ℕ, (x : ℂ) + k ≠ 0 := fun k h => hx k (eq_neg_of_add_eq_zero_left h)
  have hxk' : ∀ k : ℕ, (x + k : ℝ) ≠ 0 := fun k h => hxk k (by exact_mod_cast h)
  have hz : ∀ k : ℕ, (x : ℂ) + I * y ≠ -k := by
    intro k h
    have him := congrArg Complex.im h
    have hre := congrArg Complex.re h
    simp at him hre
    exact hx k (by exact_mod_cast hre)
  have hmul := multipliable_one_add_sq_div_add_sq x y
  have hP : Tendsto (fun n : ℕ => ∏ k ∈ range (n + 1), (1 + y ^ 2 / (x + k) ^ 2)) atTop
      (𝓝 (∏' k : ℕ, (1 + y ^ 2 / (x + k) ^ 2))) :=
    hmul.hasProd.tendsto_prod_nat.comp (tendsto_add_atTop_nat 1)
  -- the Gauss sequences
  have hseq : ∀ n : ℕ, 0 < n →
      ‖Complex.GammaSeq x n / Complex.GammaSeq (x + I * y) n‖ ^ 2 =
        ∏ k ∈ range (n + 1), (1 + y ^ 2 / (x + k) ^ 2) := by
    intro n hn
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    have hP1 : ∏ j ∈ range (n + 1), ((x : ℂ) + j) ≠ 0 :=
      prod_ne_zero_iff.mpr fun j _ => hxk j
    have hP2 : ∏ j ∈ range (n + 1), ((x : ℂ) + I * y + j) ≠ 0 :=
      prod_ne_zero_iff.mpr fun j _ => fun h => hz j (eq_neg_of_add_eq_zero_left h)
    have hc1 : (n : ℂ) ^ (x : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hn')
    have hc2 : (n : ℂ) ^ ((x : ℂ) + I * y) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hn')
    have hsplit : Complex.GammaSeq x n / Complex.GammaSeq (x + I * y) n =
        ((n : ℂ) ^ (x : ℂ) / (n : ℂ) ^ ((x : ℂ) + I * y)) *
          (∏ j ∈ range (n + 1), ((x : ℂ) + I * y + j)) / ∏ j ∈ range (n + 1), ((x : ℂ) + j) := by
      simp only [Complex.GammaSeq]
      field_simp
    rw [hsplit, norm_div, norm_mul, norm_div, norm_natCast_cpow_of_pos hn,
      norm_natCast_cpow_of_pos hn]
    have hre : ((x : ℂ) + I * y).re = x := by simp
    rw [hre, Complex.ofReal_re, div_self (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) x).ne',
      one_mul,
      norm_prod, norm_prod, div_pow, ← prod_pow, ← prod_pow, ← prod_div_distrib]
    refine prod_congr rfl fun j _ => ?_
    have h1 : ‖(x : ℂ) + I * y + j‖ ^ 2 = (x + j) ^ 2 + y ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
    have h2 : ‖(x : ℂ) + j‖ ^ 2 = (x + j) ^ 2 := by
      rw [show (x : ℂ) + j = ((x + j : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, sq_abs]
    rw [h1, h2]
    have := hxk' j
    field_simp
  have hlim : Tendsto (fun n : ℕ => ‖Complex.GammaSeq x n / Complex.GammaSeq (x + I * y) n‖ ^ 2)
      atTop (𝓝 (‖Complex.Gamma x / Complex.Gamma (x + I * y)‖ ^ 2)) :=
    (((Complex.GammaSeq_tendsto_Gamma _).div (Complex.GammaSeq_tendsto_Gamma _)
      (Complex.Gamma_ne_zero hz)).norm).pow 2
  rw [← Complex.Gamma_ofReal]
  refine tendsto_nhds_unique hlim (hP.congr' ?_)
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact (hseq n hn).symm

open Finset in
/-- The multipliability in 5.8.5: the `n`-th factor is `exp Lₙ` with `|Lₙ| = O(1/n²)`,
because the balance `∑ aₖ = ∑ bₖ` cancels the terms of order `1/n`. -/
theorem summable_balanced_factor_sub_one {m : ℕ} (a b : Fin m → ℂ)
    (hsum : ∑ k : Fin m, a k = ∑ k : Fin m, b k) :
    Summable fun n : ℕ => ‖(∏ k : Fin m, (a k + n)) / (∏ k : Fin m, (b k + n)) - 1‖ := by
  set A : ℝ := ∑ k : Fin m, (‖a k‖ + ‖b k‖) with hA
  set K : ℝ := ∑ k : Fin m, (‖a k‖ ^ 2 + ‖b k‖ ^ 2) with hK
  have hA0 : 0 ≤ A := sum_nonneg fun k _ => by positivity
  have hK0 : 0 ≤ K := sum_nonneg fun k _ => by positivity
  have hg : Summable fun n : ℕ => 2 * K * (1 / (n : ℝ) ^ 2) :=
    (Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left _
  refine Summable.of_norm_bounded_eventually_nat hg ?_
  filter_upwards [eventually_ge_atTop (⌈2 * A + 2 * K + 1⌉₊)] with n hn
  have hn' : 2 * A + 2 * K + 1 ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have hn0 : (0 : ℝ) < n := by linarith
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
  -- each `w = a/n` satisfies `‖w‖ ≤ 1/2`
  have hsmall : ∀ c : ℂ, ‖c‖ ≤ A → ‖c / n‖ ≤ 1 / 2 := by
    intro c hc
    rw [norm_div, Complex.norm_natCast, div_le_iff₀ hn0]
    linarith
  have haA : ∀ k, ‖a k‖ ≤ A := fun k =>
    (le_add_of_nonneg_right (norm_nonneg _)).trans
      (single_le_sum (f := fun k => ‖a k‖ + ‖b k‖) (fun k _ => by positivity) (mem_univ k))
  have hbA : ∀ k, ‖b k‖ ≤ A := fun k =>
    (le_add_of_nonneg_left (norm_nonneg _)).trans
      (single_le_sum (f := fun k => ‖a k‖ + ‖b k‖) (fun k _ => by positivity) (mem_univ k))
  have hne : ∀ c : ℂ, ‖c‖ ≤ A → 1 + c / n ≠ 0 := by
    intro c hc h
    have := hsmall c hc
    rw [show c / n = -1 by linear_combination h] at this
    norm_num at this
  set L : ℂ := ∑ k : Fin m, ((Complex.log (1 + a k / n) - a k / n) -
    (Complex.log (1 + b k / n) - b k / n)) with hL
  have hfac : (∏ k : Fin m, (a k + n)) / (∏ k : Fin m, (b k + n)) = Complex.exp L := by
    have hsumn : ∑ k : Fin m, (a k / n - b k / n) = 0 := by
      rw [sum_sub_distrib, ← sum_div, ← sum_div, hsum, sub_self]
    have hL' : L = ∑ k : Fin m, (Complex.log (1 + a k / n) - Complex.log (1 + b k / n)) := by
      rw [hL, ← sub_zero (∑ k : Fin m, (Complex.log (1 + a k / n) - Complex.log (1 + b k / n))),
        ← hsumn, ← sum_sub_distrib]
      refine sum_congr rfl fun k _ => ?_
      ring
    rw [hL', Complex.exp_sum, ← prod_div_distrib]
    refine prod_congr rfl fun k _ => ?_
    rw [Complex.exp_sub, Complex.exp_log (hne _ (haA k)), Complex.exp_log (hne _ (hbA k))]
    have hb0 : b k + n ≠ 0 := by
      intro h
      apply hne _ (hbA k)
      rw [show 1 + b k / n = (b k + n) / n by field_simp; ring, h, zero_div]
    have hb0' : (n : ℂ) + b k ≠ 0 := by rwa [add_comm]
    field_simp
    ring
  have hlog : ∀ c : ℂ, ‖c‖ ≤ A → ‖Complex.log (1 + c / n) - c / n‖ ≤ ‖c‖ ^ 2 / n ^ 2 := by
    intro c hc
    have hw := hsmall c hc
    have h := Complex.norm_log_one_add_sub_self_le (by linarith : ‖c / n‖ < 1)
    calc ‖Complex.log (1 + c / n) - c / n‖ ≤ ‖c / n‖ ^ 2 * (1 - ‖c / n‖)⁻¹ / 2 := h
      _ ≤ ‖c / n‖ ^ 2 * 2 / 2 := by
          gcongr
          rw [inv_le_comm₀ (by linarith) two_pos]
          linarith
      _ = ‖c‖ ^ 2 / n ^ 2 := by
          rw [norm_div, Complex.norm_natCast]; ring
  have hLb : ‖L‖ ≤ K / n ^ 2 := by
    calc ‖L‖ ≤ ∑ k : Fin m, ‖(Complex.log (1 + a k / n) - a k / n) -
          (Complex.log (1 + b k / n) - b k / n)‖ := norm_sum_le _ _
      _ ≤ ∑ k : Fin m, (‖a k‖ ^ 2 / n ^ 2 + ‖b k‖ ^ 2 / n ^ 2) := by
          refine sum_le_sum fun k _ => (norm_sub_le _ _).trans ?_
          exact add_le_add (hlog _ (haA k)) (hlog _ (hbA k))
      _ = K / n ^ 2 := by rw [hK, sum_div]; congr 1; funext k; ring
  have hL1 : ‖L‖ ≤ 1 := by
    refine hLb.trans ?_
    rw [div_le_one (by positivity)]
    nlinarith
  rw [hfac, Real.norm_of_nonneg (norm_nonneg _)]
  calc ‖Complex.exp L - 1‖ ≤ 2 * ‖L‖ := Complex.norm_exp_sub_one_le hL1
    _ ≤ 2 * (K / n ^ 2) := by gcongr
    _ = 2 * K * (1 / (n : ℝ) ^ 2) := by ring

open Finset in
/-- DLMF 5.8.5: if `∑ aₖ = ∑ bₖ` and no `bₖ` is a nonpositive integer, then `∏_{n≥0} ∏ₖ (aₖ + n)/(bₖ
+ n) = ∏ₖ Γ(bₖ) / ∏ₖ Γ(aₖ)`. -/
@[dlmf 5.8.E5]
theorem Gamma_balanced_product {m : ℕ} (hm : 0 < m) (a b : Fin m → ℂ)
    (hsum : ∑ k : Fin m, a k = ∑ k : Fin m, b k)
    (hb : ∀ k : Fin m, ∀ n : ℕ, b k ≠ -n) :
    ∏' n : ℕ, (∏ k : Fin m, (a k + n)) / (∏ k : Fin m, (b k + n)) =
      (∏ k : Fin m, Complex.Gamma (b k)) / (∏ k : Fin m, Complex.Gamma (a k)) := by
  set f : ℕ → ℂ := fun n => (∏ k : Fin m, (a k + n)) / (∏ k : Fin m, (b k + n)) with hf
  have hmul : Multipliable f := by
    have := multipliable_one_add_of_summable (summable_balanced_factor_sub_one a b hsum)
    simpa [hf] using this
  by_cases hpole : ∃ k, ∃ n : ℕ, a k = -n
  · -- a pole of some `Γ(aₖ)`: both sides vanish
    obtain ⟨k, n, hkn⟩ := hpole
    have hf0 : f n = 0 := by
      simp only [hf]
      rw [prod_eq_zero (mem_univ k) (by rw [hkn]; ring), zero_div]
    rw [tprod_of_exists_eq_zero ⟨n, hf0⟩, eq_comm, div_eq_zero_iff]
    exact Or.inr (prod_eq_zero (mem_univ k) (by rw [hkn]; exact Complex.Gamma_neg_nat_eq_zero n))
  simp only [not_exists] at hpole
  have hbk : ∀ k (j : ℕ), b k + j ≠ 0 := fun k j h => hb k j (eq_neg_of_add_eq_zero_left h)
  have hak : ∀ k (j : ℕ), a k + j ≠ 0 := fun k j h => hpole k j (eq_neg_of_add_eq_zero_left h)
  -- the Gauss sequences
  have hseq : ∀ N : ℕ, 0 < N → (∏ k : Fin m, Complex.GammaSeq (b k) N) /
      (∏ k : Fin m, Complex.GammaSeq (a k) N) = ∏ n ∈ range (N + 1), f n := by
    intro N hN
    have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    have hpow : ∏ k : Fin m, (N : ℂ) ^ b k = ∏ k : Fin m, (N : ℂ) ^ a k := by
      simp only [Complex.cpow_def_of_ne_zero hN', ← Complex.exp_sum, ← mul_sum, hsum]
    have h1 : ∏ k : Fin m, (N : ℂ) ^ a k ≠ 0 :=
      prod_ne_zero_iff.mpr fun k _ => cpow_ne_zero_iff.mpr (Or.inl hN')
    have h2 : ∏ _k : Fin m, ((N.factorial : ℕ) : ℂ) ≠ 0 :=
      prod_ne_zero_iff.mpr fun k _ => by exact_mod_cast N.factorial_ne_zero
    have h3 : ∏ k : Fin m, ∏ j ∈ range (N + 1), (b k + j) ≠ 0 :=
      prod_ne_zero_iff.mpr fun k _ => prod_ne_zero_iff.mpr fun j _ => hbk k j
    have h4 : ∏ k : Fin m, ∏ j ∈ range (N + 1), (a k + j) ≠ 0 :=
      prod_ne_zero_iff.mpr fun k _ => prod_ne_zero_iff.mpr fun j _ => hak k j
    have e : ∀ c : Fin m → ℂ, ∏ k : Fin m, Complex.GammaSeq (c k) N =
        (∏ k : Fin m, (N : ℂ) ^ c k) * (∏ _k : Fin m, ((N.factorial : ℕ) : ℂ)) /
          ∏ k : Fin m, ∏ j ∈ range (N + 1), (c k + j) := by
      intro c
      simp only [Complex.GammaSeq]
      rw [prod_div_distrib, prod_mul_distrib]
    have e3 : ∏ n ∈ range (N + 1), f n =
        (∏ k : Fin m, ∏ j ∈ range (N + 1), (a k + j)) /
          ∏ k : Fin m, ∏ j ∈ range (N + 1), (b k + j) := by
      simp only [hf]
      rw [prod_div_distrib, prod_comm (s := range (N + 1)) (t := univ)
        (f := fun n k => a k + (n : ℂ)), prod_comm (s := range (N + 1)) (t := univ)
        (f := fun n k => b k + (n : ℂ))]
    rw [e b, e a, e3, hpow]
    field_simp
  have hlim : Tendsto (fun N : ℕ => (∏ k : Fin m, Complex.GammaSeq (b k) N) /
      (∏ k : Fin m, Complex.GammaSeq (a k) N)) atTop
      (𝓝 ((∏ k : Fin m, Complex.Gamma (b k)) / (∏ k : Fin m, Complex.Gamma (a k)))) := by
    refine (tendsto_finsetProd _ fun k _ => Complex.GammaSeq_tendsto_Gamma _).div
      (tendsto_finsetProd _ fun k _ => Complex.GammaSeq_tendsto_Gamma _) ?_
    exact prod_ne_zero_iff.mpr fun k _ => Complex.Gamma_ne_zero (hpole k)
  have hP : Tendsto (fun N : ℕ => ∏ n ∈ range (N + 1), f n) atTop (𝓝 (∏' n, f n)) :=
    hmul.hasProd.tendsto_prod_nat.comp (tendsto_add_atTop_nat 1)
  refine tendsto_nhds_unique hP (hlim.congr' ?_)
  filter_upwards [eventually_gt_atTop 0] with N hN
  exact hseq N hN

end DLMF.Gamma
