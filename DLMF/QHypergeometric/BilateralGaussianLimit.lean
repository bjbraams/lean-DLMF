/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.BilateralWatson
public import DLMF.QHypergeometric.BilateralGaussianTransformation

/-!
# The bilateral Gaussian limit of Watson's transformation

The finite Watson transformation approaches DLMF 17.10.4. Finite-prefix regularity
allows the limit through parameters for which additional infinite-product exclusions
would be false, while the two Gaussian halves have uniform summable majorants.
-/

@[expose] public noncomputable section

open Complex Filter Finset
open scoped Topology
open DLMF.QSeries

namespace DLMF.QHypergeometric.BilateralGaussian

/-- Regularity of `aq` together with `a ≠ 1` includes the zero-th factor at `a`. -/
lemma central_regular {a q : ℂ} (ha1 : a ≠ 1) (haq : ∀ j : ℕ, a * q * q ^ j ≠ 1) :
    ∀ j : ℕ, a * q ^ j ≠ 1 := by
  intro j
  cases j with
  | zero => simpa only [pow_zero, mul_one] using ha1
  | succ j => simpa only [pow_succ, mul_assoc, mul_left_comm, mul_comm] using haq j

/-- A nonzero power of a base in the open unit disk cannot equal one. -/
lemma pow_ne_one {q : ℂ} (hq : ‖q‖ < 1) {j : ℕ} (hj : j ≠ 0) : q ^ j ≠ 1 := by
  intro he
  have H := pow_lt_one₀ (norm_nonneg q) hq hj
  rw [← norm_pow, he, norm_one] at H
  exact lt_irrefl _ H

/-- The forced terminating parameters and the well-poised root pair are bilaterally regular
when the two central q-lattices are excluded. -/
lemma qBilateralRegular_eight {a r c d e f q : ℂ} (hr : r ^ 2 = a)
    (_ha0 : a ≠ 0) (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hA : ∀ j : ℕ, a * q ^ j ≠ 1) (hAi : ∀ j : ℕ, (1 / a) * q ^ j ≠ 1)
    (hB : QBilateralRegular [c, d, e, f]
      [a * q / c, a * q / d, a * q / e, a * q / f] q) (N : ℕ) :
    QBilateralRegular [q ^ (-(N : ℤ)), q * r, -q * r, c, d, e, f, a / q ^ N]
      [q ^ (N + 1), r, -r, a * q / c, a * q / d, a * q / e, a * q / f,
        a * q * q ^ N] q := by
  have ht := pow_ne_zero N hq0
  constructor
  · intro x hx j he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with hx | hx | hx | hx | hx | hx | hx | hx <;> rw [hx] at he
    · apply pow_ne_one hq (by omega : N + 1 + j ≠ 0)
      simpa only [pow_add] using he
    · apply hA (2 * j)
      calc
        a * q ^ (2 * j) = (r * q ^ j) ^ 2 := by rw [mul_pow, hr, ← pow_mul, Nat.mul_comm j 2]
        _ = 1 := by rw [he]; norm_num
    · apply hA (2 * j)
      calc
        a * q ^ (2 * j) = ((-r) * q ^ j) ^ 2 := by
          rw [mul_pow, neg_sq, hr, ← pow_mul, Nat.mul_comm j 2]
        _ = 1 := by rw [he]; norm_num
    · exact hB.1 _ (by simp) j he
    · exact hB.1 _ (by simp) j he
    · exact hB.1 _ (by simp) j he
    · exact hB.1 _ (by simp) j he
    · apply hA (N + j + 1)
      simpa only [pow_add, pow_one, mul_assoc, mul_left_comm, mul_comm] using he
  · intro x hx j he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with hx | hx | hx | hx | hx | hx | hx | hx <;> rw [hx] at he
    · apply pow_ne_one hq (by omega : N + j + 1 ≠ 0)
      have H := congrArg (fun t : ℂ => t * q ^ N) he
      simpa only [zpow_neg, zpow_natCast, inv_mul_cancel₀ ht, pow_add, pow_one,
        mul_assoc, mul_left_comm, mul_comm] using H.symm
    · have hroot : r = q ^ j := by
        rw [pow_succ] at he
        apply mul_left_cancel₀ hq0
        linear_combination he
      apply hAi (2 * j)
      rw [← hr, hroot, ← pow_mul, Nat.mul_comm j 2]
      field_simp
    · have hroot : -r = q ^ j := by
        rw [pow_succ] at he
        apply mul_left_cancel₀ hq0
        linear_combination he
      apply hAi (2 * j)
      have ha : a = q ^ (2 * j) := by
        calc
          a = (-r) ^ 2 := by rw [neg_sq, hr]
          _ = (q ^ j) ^ 2 := by rw [hroot]
          _ = q ^ (2 * j) := by rw [← pow_mul, Nat.mul_comm]
      rw [ha]
      field_simp
    · exact hB.2 _ (by simp) j he
    · exact hB.2 _ (by simp) j he
    · exact hB.2 _ (by simp) j he
    · exact hB.2 _ (by simp) j he
    · apply hAi (N + j + 1)
      have ha : a = q ^ (N + j + 1) := by
        apply (div_eq_iff ht).mp at he
        simpa only [pow_add, pow_one, mul_assoc, mul_left_comm, mul_comm] using he
      rw [ha]
      field_simp

/-- Reciprocal parameter lists exchange the two regularity conditions of a bilateral series.
-/
lemma qBilateralRegular_reciprocal {a b : List ℂ} {q : ℂ} (hq0 : q ≠ 0)
    (ha0 : ∀ x ∈ a, x ≠ 0) (hb0 : ∀ x ∈ b, x ≠ 0) (hB : QBilateralRegular a b q) :
    QBilateralRegular (b.map fun x => q / x) (a.map fun x => q / x) q := by
  refine ⟨FiniteBilateral.qDenominatorRegular_reciprocal ha0 hB.2, ?_⟩
  intro x hx j he
  rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
  apply hB.1 y hy j
  have H := (div_eq_iff (hb0 y hy)).mp he
  apply mul_right_cancel₀ hq0
  rw [pow_succ] at H
  linear_combination -H

/-- The finite positive Gaussian half is summable under its uniform majorant. -/
lemma summable_eightPositiveTerm {a c d e f q : ℂ} (hq : ‖q‖ < 1)
    (haq : qPochhammerInf (a * q) q ≠ 0)
    (hden : QDenominatorRegular [a * q / c, a * q / d, a * q / e, a * q / f] q)
    (N : ℕ) : Summable (fun k => eightPositiveTerm a c d e f q N k) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_eightPositiveTerm_le hq haq hden
  exact Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (hC N)
    ((summable_pow_mul_pow_choose_two (norm_nonneg _) (norm_nonneg q) hq).mul_left C))

/-- The positive Gaussian half is summable by passage to the pointwise limit of the same
uniform Gaussian majorant. -/
lemma summable_gaussianTerm_natCast {a c d e f q : ℂ} (hq : ‖q‖ < 1)
    (haq : qPochhammerInf (a * q) q ≠ 0)
    (hden : QDenominatorRegular [a * q / c, a * q / d, a * q / e, a * q / f] q) :
    Summable (fun k : ℕ => gaussianTerm a c d e f q (k : ℤ)) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_eightPositiveTerm_le hq haq hden
  have hbound (k : ℕ) : ‖gaussianTerm a c d e f q (k : ℤ)‖ ≤
      C * (‖q * a ^ 3 / (c * d * e * f)‖ ^ k * ‖q‖ ^ k.choose 2) := by
    rw [gaussianTerm_natCast_eq]
    exact le_of_tendsto (tendsto_eightPositiveTerm hq a c d e f k).norm
      (Eventually.of_forall fun N => hC N k)
  exact Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound
    ((summable_pow_mul_pow_choose_two (norm_nonneg _) (norm_nonneg q) hq).mul_left C))

/-- Both finite eight-psi-eight tails can be written as positive Gaussian-normalized halves.
-/
lemma qPsi_eight_eq_tsum_halves {a r c d e f q : ℂ} (hr : r ^ 2 = a)
    (ha0 : a ≠ 0) (ha1 : a ≠ 1) (hc0 : c ≠ 0) (hd0 : d ≠ 0)
    (he0 : e ≠ 0) (hf0 : f ≠ 0) (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (haq : qPochhammerInf (a * q) q ≠ 0) (haiq : qPochhammerInf ((1 / a) * q) q ≠ 0)
    (hden : QDenominatorRegular [a * q / c, a * q / d, a * q / e, a * q / f] q)
    (hdeni : QDenominatorRegular [(1 / a) * q / (c / a), (1 / a) * q / (d / a),
      (1 / a) * q / (e / a), (1 / a) * q / (f / a)] q) (N : ℕ)
    (hroot : qPochhammer r q N * qPochhammer (-r) q N ≠ 0)
    (hrooti : qPochhammer (1 / r) q N * qPochhammer (-(1 / r)) q N ≠ 0) :
    BilateralWatson.eightSeries a r c d e f q N =
      (∑' k, eightPositiveTerm a c d e f q N k) +
        (∑' k, eightPositiveTerm (1 / a) (c / a) (d / a) (e / a) (f / a) q N k) - 1 := by
  have hai0 : 1 / a ≠ 0 := one_div_ne_zero ha0
  have hai1 : 1 / a ≠ 1 := by intro h; apply ha1; field_simp at h; exact h.symm
  have hri : (1 / r) ^ 2 = 1 / a := by rw [div_pow, hr, one_pow]
  let F := qPsiTerm [q ^ (-(N : ℤ)), q * r, -q * r, c, d, e, f, a / q ^ N]
    [q ^ (N + 1), r, -r, a * q / c, a * q / d, a * q / e, a * q / f, a * q * q ^ N]
    q (a ^ 2 * q ^ 2 * (q ^ N) ^ 2 / (c * d * e * f))
  have hp (k : ℕ) : F (k : ℤ) = eightPositiveTerm a c d e f q N k :=
    qPsiTerm_natCast_eq_eightPositiveTerm hr ha0 ha1 hc0 hd0 he0 hf0 hq0 N k hroot
  have hn (k : ℕ) : F (-(k : ℤ)) =
      eightPositiveTerm (1 / a) (c / a) (d / a) (e / a) (f / a) q N k := by
    rw [show F (-(k : ℤ)) = _ from
      qPsiTerm_eight_reflect hr ha0 hc0 hd0 he0 hf0 hq0 N k]
    exact qPsiTerm_natCast_eq_eightPositiveTerm hri hai0 hai1 (div_ne_zero hc0 ha0)
      (div_ne_zero hd0 ha0) (div_ne_zero he0 ha0) (div_ne_zero hf0 ha0) hq0 N k hrooti
  have hps : Summable (fun k : ℕ => F (k : ℤ)) :=
    (summable_eightPositiveTerm hq haq hden N).congr (fun k => (hp k).symm)
  have hns : Summable (fun k : ℕ => F (-(k : ℤ))) :=
    (summable_eightPositiveTerm hq haiq hdeni N).congr (fun k => (hn k).symm)
  have hz : F 0 = 1 := by simp [F, qPsiTerm, qPsiExponent, qPochhammerListInt, qPochhammerInt]
  change (∑' k : ℤ, F k) = _
  rw [tsum_int_eq_tsum_natCast_add_tsum_neg_natCast_sub hps hns, hz,
    tsum_congr hp, tsum_congr hn]

/-- The bilateral Gaussian series is the sum of its two positive-index representations. -/
lemma tsum_gaussianTerm_eq_halves {a c d e f q : ℂ} (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (hc0 : c ≠ 0) (hd0 : d ≠ 0) (he0 : e ≠ 0) (hf0 : f ≠ 0)
    (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (haq : qPochhammerInf (a * q) q ≠ 0) (haiq : qPochhammerInf ((1 / a) * q) q ≠ 0)
    (hden : QDenominatorRegular [a * q / c, a * q / d, a * q / e, a * q / f] q)
    (hdeni : QDenominatorRegular [(1 / a) * q / (c / a), (1 / a) * q / (d / a),
      (1 / a) * q / (e / a), (1 / a) * q / (f / a)] q) :
    (∑' k : ℤ, gaussianTerm a c d e f q k) =
      (∑' k : ℕ, gaussianTerm a c d e f q (k : ℤ)) +
        (∑' k : ℕ, gaussianTerm (1 / a) (c / a) (d / a) (e / a) (f / a) q (k : ℤ)) - 1 := by
  have H := gaussianTerm_neg_natCast_eq ha0 ha1 hc0 hd0 he0 hf0 hq0
  have hp := summable_gaussianTerm_natCast hq haq hden
  have hn := (summable_gaussianTerm_natCast hq haiq hdeni).congr (fun k => (H k).symm)
  have hz : gaussianTerm a c d e f q 0 = 1 := by
    simp [gaussianTerm, qPochhammerListInt, qPochhammerInt, sub_ne_zero.mpr (Ne.symm ha1)]
  rw [tsum_int_eq_tsum_natCast_add_tsum_neg_natCast_sub hp hn, hz, tsum_congr H]

/-- The terminating eight-psi-eight converges to its Gaussian bilateral series. -/
lemma tendsto_qPsi_eight {a r c d e f q : ℂ} (hr : r ^ 2 = a)
    (ha0 : a ≠ 0) (ha1 : a ≠ 1) (hc0 : c ≠ 0) (hd0 : d ≠ 0)
    (he0 : e ≠ 0) (hf0 : f ≠ 0) (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (haq : qPochhammerInf (a * q) q ≠ 0) (haiq : qPochhammerInf ((1 / a) * q) q ≠ 0)
    (hden : QDenominatorRegular [a * q / c, a * q / d, a * q / e, a * q / f] q)
    (hdeni : QDenominatorRegular [(1 / a) * q / (c / a), (1 / a) * q / (d / a),
      (1 / a) * q / (e / a), (1 / a) * q / (f / a)] q)
    (hroot : ∀ N, qPochhammer r q N * qPochhammer (-r) q N ≠ 0)
    (hrooti : ∀ N, qPochhammer (1 / r) q N * qPochhammer (-(1 / r)) q N ≠ 0) :
    Tendsto (fun N => BilateralWatson.eightSeries a r c d e f q N) atTop
      (𝓝 (∑' k : ℤ, gaussianTerm a c d e f q k)) := by
  have H := ((tendsto_tsum_eightPositiveTerm hq haq hden).add
    (tendsto_tsum_eightPositiveTerm hq haiq hdeni)).sub_const 1
  simp only [← gaussianTerm_natCast_eq] at H
  rw [← tsum_gaussianTerm_eq_halves ha0 ha1 hc0 hd0 he0 hf0 hq0 hq haq haiq hden hdeni] at H
  apply H.congr'
  exact Eventually.of_forall fun N =>
    (qPsi_eight_eq_tsum_halves hr ha0 ha1 hc0 hd0 he0 hf0 hq0 hq haq haiq hden hdeni N
      (hroot N) (hrooti N)).symm

/-- The finite four-psi-four needs only the finite prefixes inherited from its eight-psi-eight
partner; the remaining moving factors are regular by the annulus assumptions. -/
lemma regularThrough_four_of_eight {a r c d e f w z q : ℂ}
    (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (hz0 : z ≠ 0) (hz : ‖z‖ < 1) (hw : ‖w‖ < 1)
    (N : ℕ) (hreg : FiniteBilateral.RegularThrough
      [q ^ (-(N : ℤ)), q * r, -q * r, c, d, e, f, a / q ^ N]
      [q ^ (N + 1), r, -r, a * q / c, a * q / d, a * q / e, a * q / f,
        a * q * q ^ N] q N) :
    FiniteBilateral.RegularThrough [q ^ (-(N : ℤ)), e, f, w * q ^ N]
      [q ^ (N + 1), a * q / c, a * q / d, SearsLimit.movingParameter z q N] q N := by
  have ht := pow_ne_zero N hq0
  constructor
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with hx | hx | hx | hx <;> rw [hx]
    · exact hreg.1 _ (by simp)
    · exact hreg.1 _ (by simp)
    · exact hreg.1 _ (by simp)
    · exact SearsLimit.qPochhammer_movingParameter_ne_zero hz0 hq0 hq hz N
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with hx | hx | hx | hx <;> rw [hx]
    · exact hreg.2 _ (by simp)
    · exact hreg.2 _ (by simp)
    · exact hreg.2 _ (by simp)
    · rw [mul_div_cancel_right₀ w ht]
      exact qPochhammer_ne_zero_of_factors hq (one_sub_mul_pow_ne_zero_of_norm hw hq) N

/-- A finite product quotient approaches its infinite quotient when the limiting lower product
is regular. -/
lemma tendsto_qProductRatio {q : ℂ} (hq : ‖q‖ < 1) (a : List ℂ) {b : List ℂ}
    (hb : QDenominatorRegular b q) :
    Tendsto (fun N => qProductRatio N a b q) atTop (𝓝 (qProductRatioInf a b q)) := by
  exact (FiniteBilateral.tendsto_qPochhammerList a hq).div
    (FiniteBilateral.tendsto_qPochhammerList b hq)
    (FiniteBilateral.qPochhammerListInf_ne_zero hq hb)

/-- Taking the Gaussian limit of finite Watson gives the annular bilateral transformation
DLMF 17.10.4, using an arbitrary square root of its central parameter. -/
lemma qPsi_two_eq_gaussian {a r c d e f q : ℂ} (hr : r ^ 2 = a)
    (ha0 : a ≠ 0) (ha1 : a ≠ 1) (hc0 : c ≠ 0) (hd0 : d ≠ 0)
    (he0 : e ≠ 0) (hf0 : f ≠ 0) (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hden : QDenominatorRegular [a * q, q / a, a * q / (c * d), a * q / (e * f)] q)
    (hBtwo : QBilateralRegular [e, f] [a * q / c, a * q / d] q)
    (hBfour : QBilateralRegular [c, d, e, f]
      [a * q / c, a * q / d, a * q / e, a * q / f] q)
    (hw : ‖a * q / (c * d)‖ < 1) (hz : ‖a * q / (e * f)‖ < 1) :
    qPsi [e, f] [a * q / c, a * q / d] q (a * q / (e * f)) =
      qProductRatioInf [q / c, q / d, a * q / e, a * q / f]
        [a * q, q / a, a * q / (c * d), a * q / (e * f)] q *
          (∑' k : ℤ, gaussianTerm a c d e f q k) := by
  have hr0 : r ≠ 0 := by intro h; apply ha0; rw [← hr, h]; simp
  have hai0 : 1 / a ≠ 0 := one_div_ne_zero ha0
  have hai1 : 1 / a ≠ 1 := by intro h; apply ha1; field_simp at h; exact h.symm
  have hri : (1 / r) ^ 2 = 1 / a := by rw [div_pow, hr, one_pow]
  have hA := central_regular ha1 (fun j => hden _ (by simp) j)
  have hAi : ∀ j : ℕ, (1 / a) * q ^ j ≠ 1 := by
    apply central_regular hai1
    intro j
    simpa only [one_div, div_eq_mul_inv, mul_one, one_mul, mul_assoc, mul_left_comm, mul_comm] using
      hden (q / a) (by simp) j
  have hBi : QBilateralRegular [c / a, d / a, e / a, f / a]
      [(1 / a) * q / (c / a), (1 / a) * q / (d / a), (1 / a) * q / (e / a),
        (1 / a) * q / (f / a)] q := by
    have H := qBilateralRegular_reciprocal hq0 (by simp [hc0, hd0, he0, hf0])
      (by simp [ha0, hq0, hc0, hd0, he0, hf0]) hBfour
    have hU : ([a * q / c, a * q / d, a * q / e, a * q / f].map fun x => q / x) =
        [c / a, d / a, e / a, f / a] := by
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
      and_intros <;> field_simp
    have hL : ([c, d, e, f].map fun x => q / x) =
        [(1 / a) * q / (c / a), (1 / a) * q / (d / a), (1 / a) * q / (e / a),
          (1 / a) * q / (f / a)] := by
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
      and_intros <;> field_simp
    rwa [hU, hL] at H
  have hB8 (N : ℕ) := qBilateralRegular_eight hr ha0 hq0 hq hA hAi hBfour N
  have hB8i (N : ℕ) := qBilateralRegular_eight hri hai0 hq0 hq hAi
    (by simpa only [one_div_one_div] using hA) hBi N
  have hroot (N : ℕ) : qPochhammer r q N * qPochhammer (-r) q N ≠ 0 := by
    exact mul_ne_zero
      (qPochhammer_ne_zero_of_mem_qDenominatorRegular hq (hB8 N).1 (by simp) N)
      (qPochhammer_ne_zero_of_mem_qDenominatorRegular hq (hB8 N).1 (by simp) N)
  have hrooti (N : ℕ) :
      qPochhammer (1 / r) q N * qPochhammer (-(1 / r)) q N ≠ 0 := by
    exact mul_ne_zero
      (qPochhammer_ne_zero_of_mem_qDenominatorRegular hq (hB8i N).1 (by simp) N)
      (qPochhammer_ne_zero_of_mem_qDenominatorRegular hq (hB8i N).1 (by simp) N)
  have haq : qPochhammerInf (a * q) q ≠ 0 := qPochhammerInf_ne_zero hq
    (fun j => sub_ne_zero.mpr (Ne.symm (hden _ (by simp) j)))
  have haiq : qPochhammerInf ((1 / a) * q) q ≠ 0 := qPochhammerInf_ne_zero hq
    (fun j => sub_ne_zero.mpr (Ne.symm (by
      simpa only [one_div, div_eq_mul_inv, mul_one, one_mul, mul_assoc,
        mul_left_comm, mul_comm] using
        hden (q / a) (by simp) j)))
  have hEight := tendsto_qPsi_eight hr ha0 ha1 hc0 hd0 he0 hf0 hq0 hq haq haiq
    hBfour.1 hBi.1 hroot hrooti
  have hw0 : a * q / (c * d) ≠ 0 := div_ne_zero (mul_ne_zero ha0 hq0) (mul_ne_zero hc0 hd0)
  have hz0 : a * q / (e * f) ≠ 0 := div_ne_zero (mul_ne_zero ha0 hq0) (mul_ne_zero he0 hf0)
  have hbal : (a * q / c) * (a * q / d) =
      e * f * (a * q / (c * d)) * (a * q / (e * f)) := by field_simp
  have hFour := tendsto_qPsi_four he0 hf0 (div_ne_zero (mul_ne_zero ha0 hq0) hc0)
    (div_ne_zero (mul_ne_zero ha0 hq0) hd0) hw0 hz0 hq0 hq hw hz hbal hBtwo
  have hFour' : Tendsto (fun N => BilateralWatson.fourSeries a c d e f q N) atTop
      (𝓝 (qPsi [e, f] [a * q / c, a * q / d] q (a * q / (e * f)))) := by
    convert hFour using 1
    funext N
    unfold BilateralWatson.fourSeries SearsLimit.movingParameter
    congr 2 <;> congr 1 <;> (try simp only [inv_pow]) <;> field_simp
  have hPrefDen : QDenominatorRegular [q / c, q / d, a * q / e, a * q / f] q := by
    intro x hx j
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with hx | hx | hx | hx <;> rw [hx]
    · exact FiniteBilateral.qDenominatorRegular_reciprocal
        (by simp [hc0, hd0, he0, hf0]) hBfour.2 (q / c) (by simp) j
    · exact FiniteBilateral.qDenominatorRegular_reciprocal
        (by simp [hc0, hd0, he0, hf0]) hBfour.2 (q / d) (by simp) j
    · exact hBfour.1 _ (by simp) j
    · exact hBfour.1 _ (by simp) j
  have hFinite (N : ℕ) : BilateralWatson.eightSeries a r c d e f q N =
      qProductRatio N [a * q, q / a, a * q / (c * d), a * q / (e * f)]
        [q / c, q / d, a * q / e, a * q / f] q *
          BilateralWatson.fourSeries a c d e f q N := by
    have hReg := FiniteBilateral.regularThrough_of_qBilateralRegular hq0 hq (hB8 N) N
    have hReg4 := regularThrough_four_of_eight hq0 hq hz0 hz hw N hReg
    have hmove : SearsLimit.movingParameter (a * q / (e * f)) q N = e * f / (a * q ^ N) := by
      unfold SearsLimit.movingParameter
      simp only [inv_pow]
      field_simp
    have hupper : a * q / (c * d) * q ^ N = a * q * q ^ N / (c * d) := by ring
    rw [hmove, hupper] at hReg4
    simpa only [hr] using BilateralWatson.eightSeries_eq_fourSeries hr0 hc0 hd0 he0 hf0
      hq0 hq N (by simpa only [hr] using hPrefDen)
      (by simpa only [hr] using And.intro hReg hReg4)
  have hRhs := (tendsto_qProductRatio hq
    [a * q, q / a, a * q / (c * d), a * q / (e * f)] hPrefDen).mul hFour'
  have hLimit := tendsto_nhds_unique hEight (hRhs.congr' (Eventually.of_forall
    fun N => (hFinite N).symm))
  have hTop := FiniteBilateral.qPochhammerListInf_ne_zero hq hden
  have hBot := FiniteBilateral.qPochhammerListInf_ne_zero hq hPrefDen
  unfold qProductRatioInf at hLimit ⊢
  rw [hLimit]
  field_simp

end DLMF.QHypergeometric.BilateralGaussian
