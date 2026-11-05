/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.Basic.SeriesProperties

/-!
# Exceptional parameters in the terminating q-Dixon quotient

At `q = 1/2`, `b = 3`, `c = 1/3`, `n = 1`, the terminating series in DLMF 17.7.6 is
regular and equals `-9/10`. Its literal product quotient is `0/0`, hence zero under Lean's
field convention. A finite lower-parameter regularity condition alone therefore does not
justify the uncancelled quotient at every parameter. The cancelled quotient agrees with the
regular series at this removable zero.
-/

@[expose] public noncomputable section

open Complex Finset
open DLMF.QSeries

namespace DLMF.QHypergeometric

/-- The lower parameters of the terminating q-Dixon counterexample are regular through the
last term, even though the product parameter `bc` equals one. -/
theorem qDixon_parameters_regular :
    QDenominatorRegularThrough [(2 : ℂ) / 3, 6] (1 / 2) 2 := by
  norm_num [QDenominatorRegularThrough, qPochhammerList, qPochhammer_zero, qPochhammer_succ]

/-- The finite q-Dixon series at these exceptional parameters equals `-9/10`. -/
theorem qPhi_qDixon_exceptional_value :
    qPhi [4, 3, (1 : ℂ) / 3] [2 / 3, 6] (1 / 2) (1 / 2) = -9 / 10 := by
  rw [qPhi, tsum_eq_sum (s := range 3)]
  · norm_num [sum_range_succ, qPhiTerm, qPhiExponent, qPochhammerList,
      qPochhammer_zero, qPochhammer_succ]
  · intro n hn
    have hn2 : 2 < n := by simp only [mem_range, not_lt] at hn; omega
    have H := qPochhammer_recip_pow_eq_zero (q := (1 / 2 : ℂ)) (by norm_num) hn2
    norm_num at H
    simp only [qPhiTerm, qPochhammerList, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, H, zero_mul, zero_div]

/-- The literal quotient in DLMF 17.7.6 disagrees with its regular terminating series when
`q = 1/2`, `b = 3`, `c = 1/3`, `n = 1`. The lower parameters satisfy
`qDixon_parameters_regular`; the extra factor `(bc;q)₁` in the quotient vanishes. -/
theorem qDixon_terminating_quotient_counterexample :
    qPhi [4, 3, (1 : ℂ) / 3] [2 / 3, 6] (1 / 2) (1 / 2) ≠
      qPochhammerList [3, (1 : ℂ) / 3] (1 / 2) 1 *
        qPochhammerList [1 / 2, 3 * ((1 : ℂ) / 3)] (1 / 2) 2 /
        (qPochhammerList [1 / 2, 3 * ((1 : ℂ) / 3)] (1 / 2) 1 *
          qPochhammerList [3, (1 : ℂ) / 3] (1 / 2) 2) := by
  rw [qPhi_qDixon_exceptional_value]
  norm_num [qPochhammerList, qPochhammer_zero, qPochhammer_succ]

/-- At the removable zero `bc=1`, the cancelled q-Dixon quotient agrees with the
regular terminating series. -/
theorem qPhi_qDixon_eq_cancelled_quotient :
    qPhi [4, 3, (1 : ℂ) / 3] [2 / 3, 6] (1 / 2) (1 / 2) =
      qPochhammerList [(1 / 2) ^ 2, (1 / 2 : ℂ)] (1 / 2) 1 /
        qPochhammerList [3 * (1 / 2), ((1 : ℂ) / 3) * (1 / 2)] (1 / 2) 1 := by
  rw [qPhi_qDixon_exceptional_value]
  norm_num [qPochhammerList, qPochhammer_zero, qPochhammer_succ]

end DLMF.QHypergeometric
