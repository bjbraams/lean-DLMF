/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.ClausenCommonTermination
public import DLMF.QHypergeometric.ClausenTerminatingLaurent

/-!
# The terminating q-Clausen square identity

The common terminating case follows from finite telescoping recurrences. Termination
in either of the first two parameters follows by Laurent-polynomial continuation from
the geometric sequence `z = ab q^N`. Zero upper products reduce to the q-binomial sum.

The Laurent continuation argument is the one following (2.17) in George Gasper,
*q-Extensions of Clausen's Formula and of the Inequalities Used by de Branges in His
Proof of the Bieberbach, Robertson, and Milin Conjectures*, SIAM J. Math. Anal. 20
(1989), 1019–1034, DOI: 10.1137/0520068. The finite recurrences retain all terminating
zeros and use no division by upper shifted factorials.
-/

@[expose] public noncomputable section

open Complex Finset
open DLMF.QSeries
open DLMF.QHypergeometric.ClausenRecurrence DLMF.QHypergeometric.ClausenLaurentPolynomial

namespace DLMF.QHypergeometric.ClausenSummation

/-- The first series, with the paired and half-base parameters grouped symmetrically. -/
def firstSeries (a b q z : ℂ) : ℂ :=
  qPhi [a, b, a * b * z, a * b / z]
    [a * b * q ^ (1 / 2 : ℂ), -(a * b * q ^ (1 / 2 : ℂ)), -(a * b)] q q

/-- The second series, with the square product grouped symmetrically. -/
def secondSeries (a b q z : ℂ) : ℂ :=
  qPhi [a ^ 2, b ^ 2, a * b, a * b * z, a * b / z]
    [a * b * q ^ (1 / 2 : ℂ), -(a * b * q ^ (1 / 2 : ℂ)), -(a * b), (a * b) ^ 2] q q

/-- Interchanging the first two parameters leaves the first q-Clausen sum unchanged. -/
lemma firstSeries_swap (a b q z : ℂ) : firstSeries a b q z = firstSeries b a q z := by
  unfold firstSeries qPhi
  apply tsum_congr
  intro k
  simp only [qPhiTerm, qPhiExponent, qPochhammerList, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, List.length_cons, List.length_nil, mul_comm b a]
  ring

/-- Interchanging the first two parameters leaves the second q-Clausen sum unchanged. -/
lemma secondSeries_swap (a b q z : ℂ) : secondSeries a b q z = secondSeries b a q z := by
  unfold secondSeries qPhi
  apply tsum_congr
  intro k
  simp only [qPhiTerm, qPhiExponent, qPochhammerList, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, List.length_cons, List.length_nil, mul_comm b a]
  ring

/-- Inverting the Laurent argument interchanges the opposite upper parameters. -/
lemma firstSeries_inv (a b q z : ℂ) : firstSeries a b q z = firstSeries a b q z⁻¹ := by
  unfold firstSeries qPhi
  apply tsum_congr
  intro k
  simp only [qPhiTerm, qPhiExponent, qPochhammerList, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, List.length_cons, List.length_nil, div_eq_mul_inv, inv_inv]
  ring

/-- The second finite Laurent sum is also invariant under inversion of its argument. -/
lemma secondSeries_inv (a b q z : ℂ) : secondSeries a b q z = secondSeries a b q z⁻¹ := by
  unfold secondSeries qPhi
  apply tsum_congr
  intro k
  simp only [qPhiTerm, qPhiExponent, qPochhammerList, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, List.length_cons, List.length_nil, div_eq_mul_inv, inv_inv]
  ring

/-- A prescribed truncation in the first parameter gives the first finite Laurent form. -/
lemma firstSeries_eq_pair_sum {a b q : ℂ} (hq0 : q ≠ 0) (n : ℕ)
    (ha : a = q ^ (-(n : ℤ))) (z : ℂ) :
    firstSeries a b q z = ∑ k ∈ range (n + 1),
      pairCoefficient [a, b]
        [a * b * q ^ (1 / 2 : ℂ), -(a * b * q ^ (1 / 2 : ℂ)), -(a * b)] q k *
          qPochhammer (a * b * z) q k * qPochhammer (a * b / z) q k :=
  qPhi_eq_pair_sum hq0 [a, b] _ (by simp) n (List.mem_cons.mpr (Or.inl ha.symm)) (a * b) z

/-- Squaring the terminating upper parameter doubles the second Laurent truncation. -/
lemma secondSeries_eq_pair_sum {a b q : ℂ} (hq0 : q ≠ 0) (n : ℕ)
    (ha : a = q ^ (-(n : ℤ))) (z : ℂ) :
    secondSeries a b q z = ∑ k ∈ range (2 * n + 1),
      pairCoefficient [a ^ 2, b ^ 2, a * b]
        [a * b * q ^ (1 / 2 : ℂ), -(a * b * q ^ (1 / 2 : ℂ)), -(a * b), (a * b) ^ 2]
        q k * qPochhammer (a * b * z) q k * qPochhammer (a * b / z) q k := by
  have ha2 : a ^ 2 = q ^ (-((2 * n : ℕ) : ℤ)) := by
    rw [ha, ← zpow_natCast _ 2, ← zpow_mul]
    congr 1
    omega
  exact qPhi_eq_pair_sum hq0 [a ^ 2, b ^ 2, a * b] _ (by simp) (2 * n)
    (List.mem_cons.mpr (Or.inl ha2.symm)) (a * b) z

/-- At a geometric Laurent node, both series share the same terminating parameter. -/
lemma square_at_geometric {a b q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hB : ∀ j : ℕ, (a * b) ^ 2 * q ^ j ≠ 1) (hβ : a * b ≠ 0) (N : ℕ) :
    firstSeries a b q (a * b * q ^ N) ^ 2 = secondSeries a b q (a * b * q ^ N) := by
  have he : a * b / (a * b * q ^ N) = q ^ (-(N : ℤ)) := by
    rw [zpow_neg, zpow_natCast]
    rw [div_mul_eq_div_div, div_self hβ, one_div]
  simpa only [firstSeries, secondSeries, he,
    show a * b * (a * b * q ^ N) = (a * b) ^ 2 * q ^ N by ring,
    neg_mul] using qPhi_square_common_termination hq0 hq hB N

/-- Termination in the first parameter follows from polynomial continuation, including zero. -/
theorem square_of_first_terminates {a b q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hB : ∀ j : ℕ, (a * b) ^ 2 * q ^ j ≠ 1) (n : ℕ)
    (ha : a = q ^ (-(n : ℤ))) {z : ℂ} (hz : z ≠ 0) :
    firstSeries a b q z ^ 2 = secondSeries a b q z := by
  by_cases hβ : a * b = 0
  · have ha0 : a ≠ 0 := by rw [ha]; exact zpow_ne_zero _ hq0
    have hb : b = 0 := (mul_eq_zero.mp hβ).resolve_left ha0
    subst b
    simpa only [firstSeries, secondSeries, ha, mul_zero, zero_mul, zero_div, neg_zero,
      zero_pow (by decide : 2 ≠ 0)] using qPhi_square_zero_right hq0 hq n
  · rw [firstSeries_eq_pair_sum hq0 n ha, secondSeries_eq_pair_sum hq0 n ha]
    apply square_eq_of_forall_geometric hβ hq0 hq
    · intro N
      rw [← firstSeries_eq_pair_sum hq0 n ha, ← secondSeries_eq_pair_sum hq0 n ha]
      exact square_at_geometric hq0 hq hB hβ N
    · exact hz

/-- Termination in an opposite upper parameter is the common terminating case. -/
lemma square_of_quotient_terminates {a b q z : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hB : ∀ j : ℕ, (a * b) ^ 2 * q ^ j ≠ 1) (n : ℕ)
    (hn : a * b / z = q ^ (-(n : ℤ))) (hz : z ≠ 0) :
    firstSeries a b q z ^ 2 = secondSeries a b q z := by
  have hp : a * b * z = (a * b) ^ 2 * q ^ n := by
    rw [zpow_neg, zpow_natCast] at hn
    have hqn := pow_ne_zero n hq0
    field_simp at hn
    linear_combination -(a * b) * hn
  simpa only [firstSeries, secondSeries, hp, hn,
    neg_mul] using qPhi_square_common_termination hq0 hq hB n

/-- The terminating q-Clausen square identity with every regular finite exceptional case. -/
theorem square_of_terminating {a b q z : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hB : ∀ j : ℕ, (a * b) ^ 2 * q ^ j ≠ 1)
    (hterm : QTerminating [a, b, a * b * z, a * b / z] q) (hz : z ≠ 0) :
    firstSeries a b q z ^ 2 = secondSeries a b q z := by
  obtain ⟨u, hu, n, hn⟩ := hterm
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl
  · exact square_of_first_terminates hq0 hq hB n hn hz
  · rw [firstSeries_swap, secondSeries_swap]
    exact square_of_first_terminates hq0 hq (by simpa only [mul_comm] using hB) n hn hz
  · rw [firstSeries_inv, secondSeries_inv]
    apply square_of_quotient_terminates hq0 hq hB n _ (inv_ne_zero hz)
    simpa only [div_eq_mul_inv, inv_inv] using hn
  · exact square_of_quotient_terminates hq0 hq hB n hn hz

end DLMF.QHypergeometric.ClausenSummation
