/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.Basic.SeriesProperties
public import DLMF.QHypergeometric.DixonFiniteSum

/-!
# Jackson's terminating q-Dixon sum

The product in DLMF 17.7.6 is interpreted after cancellation of removable factors.
The reduced product retains every parameter allowed by the terminating series.
The literal printed quotient is recovered when its denominator is nonzero.
-/

@[expose] public noncomputable section

open Complex
open DLMF.QSeries

namespace DLMF.QHypergeometric

/-- Jackson's terminating q-Dixon sum with removable factors cancelled, stronger than DLMF,
which uses the literal product quotient where its denominator is nonzero. The lower
parameters need only be regular through the final retained term. -/
@[dlmf 17.7.E6 "stronger than DLMF: cancels removable factors in the product quotient"]
theorem q_dixon_terminating' {b c q : ℂ} (hb : b ≠ 0) (hc : c ≠ 0) (hq0 : q ≠ 0)
    (hq : ‖q‖ < 1) (n : ℕ)
    (hd : QDenominatorRegularThrough [q ^ (1 - (2 * n : ℤ)) / b,
      q ^ (1 - (2 * n : ℤ)) / c] q (2 * n)) :
    qPhi [q ^ (-(2 * n : ℤ)), b, c]
      [q ^ (1 - (2 * n : ℤ)) / b, q ^ (1 - (2 * n : ℤ)) / c] q
        (q ^ (2 - (n : ℤ)) / (b * c)) =
      qPochhammerList [q ^ (n + 1), b * c * q ^ n] q n /
        qPochhammerList [b * q ^ n, c * q ^ n] q n := by
  exact DixonFiniteSum.qPhi_eq_cancelled_quotient hb hc hq0 hq n hd

/-- DLMF 17.7.6 in its literal printed quotient form, with its denominator nonzero.
The cancelled form `q_dixon_terminating'` also covers removable zeros of this quotient. -/
@[dlmf 17.7.E6]
theorem q_dixon_terminating {b c q : ℂ} (hb : b ≠ 0) (hc : c ≠ 0) (hq0 : q ≠ 0)
    (hq : ‖q‖ < 1) (n : ℕ)
    (hd : QDenominatorRegularThrough [q ^ (1 - (2 * n : ℤ)) / b,
      q ^ (1 - (2 * n : ℤ)) / c] q (2 * n))
    (hden : qPochhammerList [q, b * c] q n *
      qPochhammerList [b, c] q (2 * n) ≠ 0) :
    qPhi [q ^ (-(2 * n : ℤ)), b, c]
      [q ^ (1 - (2 * n : ℤ)) / b, q ^ (1 - (2 * n : ℤ)) / c] q
        (q ^ (2 - (n : ℤ)) / (b * c)) =
      qPochhammerList [b, c] q n * qPochhammerList [q, b * c] q (2 * n) /
        (qPochhammerList [q, b * c] q n * qPochhammerList [b, c] q (2 * n)) := by
  rw [q_dixon_terminating' hb hc hq0 hq n hd]
  have hsplit (a : ℂ) : qPochhammer a q (2 * n) =
      qPochhammer a q n * qPochhammer (a * q ^ n) q n := by
    rw [two_mul, qPochhammer_add]
  have hbc : qPochhammerList [b, c] q (2 * n) = qPochhammerList [b, c] q n *
      qPochhammerList [b * q ^ n, c * q ^ n] q n := by
    simp only [qPochhammerList, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one]
    rw [hsplit b, hsplit c]
    ring
  have hshift : qPochhammerList [b * q ^ n, c * q ^ n] q n ≠ 0 := by
    have h := right_ne_zero_of_mul hden
    rw [hbc] at h
    exact right_ne_zero_of_mul h
  apply (div_eq_div_iff hshift hden).mpr
  simp only [qPochhammerList, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one]
  rw [hsplit b, hsplit c, hsplit q, hsplit (b * c)]
  simp only [pow_succ, mul_comm q (q ^ n)]
  ring

end DLMF.QHypergeometric
