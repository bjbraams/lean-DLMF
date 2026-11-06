/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.ClausenLaurentPolynomial
public import DLMF.QHypergeometric.PfaffSaalschutz
public import DLMF.QHypergeometric.FiniteDifferencePolynomial

/-!
# Finite Laurent forms of the q-Clausen series

Terminating series with opposite upper parameters are finite Laurent polynomials.
The zero paired parameter reduces the series to a terminating q-binomial sum.
-/

@[expose] public noncomputable section

open Complex Finset
open DLMF.QSeries

namespace DLMF.QHypergeometric.ClausenLaurentPolynomial

/-- The coefficient independent of the two opposite upper parameters. -/
def pairCoefficient (A D : List ℂ) (q : ℂ) (k : ℕ) : ℂ :=
  qPochhammerList A q k / (qPochhammerList D q k * qPochhammer q q k) * q ^ k

/-- Termination in an unpaired upper parameter leaves a finite Laurent sum. -/
lemma qPhi_eq_pair_sum {q : ℂ} (hq0 : q ≠ 0) (A D : List ℂ)
    (hlen : A.length + 2 = D.length + 1) (n : ℕ)
    (hmem : q ^ (-(n : ℤ)) ∈ A) (β z : ℂ) :
    qPhi (A ++ [β * z, β / z]) D q q =
      ∑ k ∈ range (n + 1), pairCoefficient A D q k *
        qPochhammer (β * z) q k * qPochhammer (β / z) q k := by
  rw [PfaffSaalschutz.qPhi_eq_sum_of_mem hq0 n (List.mem_append_left _ hmem)]
  apply sum_congr rfl
  intro k hk
  have he : qPhiExponent (A ++ [β * z, β / z]) D = 0 := by
    simp only [qPhiExponent, List.length_append, List.length_cons, List.length_nil]
    omega
  unfold qPhiTerm
  rw [he]
  simp only [qPochhammerList, List.map_append, List.prod_append, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil, zpow_zero, mul_one, pairCoefficient]
  ring

/-- A positive-order terminating q-binomial sum vanishes at the base. -/
lemma terminating_binomial_eq_zero {q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    {n : ℕ} (hn : 0 < n) : qPhi [q ^ (-(n : ℤ))] [] q q = 0 := by
  rw [one_phi_zero_terminating hq0 hq]
  have he : q * q ^ (-(n : ℤ)) = q ^ (-((n - 1 : ℕ) : ℤ)) := by
    conv_lhs => lhs; rw [← zpow_one q]
    rw [← zpow_add₀ hq0]
    congr 1
    omega
  rw [he]
  simpa only [zpow_neg, zpow_natCast] using
    qPochhammer_recip_pow_eq_zero hq0 (show n - 1 < n by omega)

/-- Zero opposite parameters leave the ordinary terminating q-binomial series. -/
lemma qPhi_zero_pair (a q : ℂ) :
    qPhi [a, 0, 0, 0] [0, 0, 0] q q = qPhi [a] [] q q := by
  unfold qPhi
  apply tsum_congr
  intro k
  simp [qPhiTerm, qPhiExponent, qPochhammerList, qPochhammer_zero_param]

/-- The second zero-parameter series has the same binomial reduction. -/
lemma qPhi_zero_pair_square (a q : ℂ) :
    qPhi [a ^ 2, 0, 0, 0, 0] [0, 0, 0, 0] q q = qPhi [a ^ 2] [] q q := by
  unfold qPhi
  apply tsum_congr
  intro k
  simp [qPhiTerm, qPhiExponent, qPochhammerList, qPochhammer_zero_param]

/-- The square identity retains the case where the second upper parameter is zero. -/
lemma qPhi_square_zero_right {q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (n : ℕ) :
    qPhi [q ^ (-(n : ℤ)), 0, 0, 0] [0, 0, 0] q q ^ 2 =
      qPhi [(q ^ (-(n : ℤ))) ^ 2, 0, 0, 0, 0] [0, 0, 0, 0] q q := by
  rw [qPhi_zero_pair, qPhi_zero_pair_square]
  have he : (q ^ (-(n : ℤ))) ^ 2 = q ^ (-((2 * n : ℕ) : ℤ)) := by
    rw [← zpow_natCast _ 2, ← zpow_mul]
    congr 1
    omega
  rw [he]
  by_cases hn : n = 0
  · subst n
    simp only [Nat.cast_zero, neg_zero, zpow_zero, mul_zero]
    have h := one_phi_zero_terminating hq0 hq q 0
    simp only [Nat.cast_zero, neg_zero, zpow_zero, qPochhammer_zero] at h
    simp only [h, one_pow]
  · rw [terminating_binomial_eq_zero hq0 hq (by omega : 0 < n),
      terminating_binomial_eq_zero hq0 hq (by omega : 0 < 2 * n)]
    norm_num

end DLMF.QHypergeometric.ClausenLaurentPolynomial
