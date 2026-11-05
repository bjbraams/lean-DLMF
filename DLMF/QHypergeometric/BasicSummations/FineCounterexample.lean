/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.Basic.SeriesProperties
public import DLMF.QSeries.Heine

/-!
# A counterexample to Fine's first transformation

The printed identity DLMF 17.6.9 fails at the regular parameters
`a = 4`, `b = 3/4`, `q = 1/2`, `z = 0`. Both series terminate, so the failure does not
involve a divergent series or a value assigned at a singular denominator. The transformation
with first-series denominator `(aq²/b;q)ₙ` has the expected value at these parameters.
-/

@[expose] public noncomputable section

open Complex Filter Finset
open DLMF.QSeries
open scoped Topology

namespace DLMF.QHypergeometric

/-- The terminating series `(2; 1/2)ₙ (1/2)ⁿ` has sum `1/2`. -/
private lemma sum_qPochhammer_two :
    (∑' n : ℕ, qPochhammer (2 : ℂ) (1 / 2) n * (1 / 2 : ℂ) ^ n) = 1 / 2 := by
  rw [tsum_eq_sum (s := range 2)]
  · norm_num [sum_range_succ, qPochhammer_zero, qPochhammer_succ]
  · intro n hn
    have hn2 : 1 < n := by simpa using hn
    have H := qPochhammer_recip_pow_eq_zero (q := (1 / 2 : ℂ)) (by norm_num) hn2
    norm_num at H
    rw [H, zero_mul]

/-- The product `(2; 1/2)∞` vanishes because its factor of index one is zero. -/
private lemma infinite_qPochhammer_two : qPochhammerInf (2 : ℂ) (1 / 2) = 0 := by
  rw [qPochhammerInf_mul_qPochhammer (a := 2) (q := (1 / 2 : ℂ)) (by norm_num) 2]
  norm_num [qPochhammer_succ, qPochhammer_zero]

/-- The parameters `a = 4`, `b = 3/4`, `q = 1/2`, `z = 0` satisfy the denominator
regularity conditions of DLMF 17.6.9. -/
theorem fine_first_parameters_regular : QDenominatorRegular
    [(3/4)*(1/2), (4 : ℂ)*0*(1/2)^2/(3/4), (4 : ℂ)*(1/2)/(3/4)] (1/2) := by
  intro t ht n
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · intro h
    exact one_sub_mul_pow_ne_zero_of_norm
      (by norm_num : ‖((3/4 : ℂ)*(1/2))‖ < 1)
      (by norm_num : ‖(1/2 : ℂ)‖ < 1) n (by rw [h]; ring)
  · norm_num
  · intro h
    have hn : (2 : ℂ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
    norm_num [div_pow] at h
    field_simp at h
    have H : (8 : ℂ) = 3 * (2 : ℂ) ^ n := by linear_combination h
    have Hnat : (8 : ℕ) = 3 * 2 ^ n := by exact_mod_cast H
    have hdiv : (3 : ℕ) ∣ 8 := ⟨2 ^ n, Hnat⟩
    norm_num at hdiv

/-- DLMF 17.6.9 fails at `a = 4`, `b = 3/4`, `q = 1/2`, `z = 0`: its left side is
`1`, while the terminating series on its right has sum `1/2` and the full right side is
`1/5`. The denominator parameters are regular, as shown by `fine_first_parameters_regular`. -/
theorem fine_first_transformation_counterexample :
    qPhi [1/2, 4*(1/2)] [(3/4)*(1/2)] (1/2) 0 ≠
      -(1-(3/4 : ℂ))*(4*(1/2)/(3/4))/(1-4*(1/2)/(3/4))*
        (∑' n : ℕ, qPochhammerList [4*(1/2),4*0*(1/2)/(3/4)] (1/2) n*(1/2)^n /
          qPochhammer (4*0*(1/2)^2/(3/4)) (1/2) n) +
      qPochhammerListInf [4*(1/2),4*0*(1/2)/(3/4)] (1/2) /
        qPochhammerInf (4*(1/2)/(3/4)) (1/2)*qPhi [1/2,0] [(3/4)*(1/2)] (1/2) 0 := by
  norm_num [qPochhammerList, qPochhammerListInf, qPochhammer_zero_param,
    infinite_qPochhammer_two, sum_qPochhammer_two]


/-- At the terminating parameters, the first series with denominator `(aq²/b;q)ₙ`
has sum `5/2`. -/
private lemma sum_qPochhammer_two_div_four_thirds :
    (∑' n : ℕ, qPochhammerList [2, 0] (1 / 2) n * (1 / 2) ^ n /
      qPochhammer (4 / 3) (1 / 2) n : ℂ) = 5 / 2 := by
  rw [tsum_eq_sum (s := Finset.range 2)]
  · norm_num [Finset.sum_range_succ, qPochhammerList, qPochhammer_zero, qPochhammer_succ]
  · intro n hn
    have hn2 : 1 < n := by simpa using hn
    have h := qPochhammer_recip_pow_eq_zero (q := (1 / 2 : ℂ)) (by norm_num) hn2
    norm_num at h
    simp only [qPochhammerList, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, h, zero_mul, zero_div]

/-- The first transformation's right side with denominator `(aq²/b;q)ₙ` agrees with
its left side at `q=1/2`, `a=4`, `b=3/4`, `z=0`. -/
theorem fine_first_shifted_denominator_rhs :
    -(1 - (3 / 4 : ℂ)) * (4 * (1 / 2) / (3 / 4)) /
        (1 - 4 * (1 / 2) / (3 / 4)) *
      (∑' n : ℕ, qPochhammerList [2, 0] (1 / 2) n * (1 / 2) ^ n /
        qPochhammer (4 / 3) (1 / 2) n) +
      qPochhammerListInf [2, 0] (1 / 2) / qPochhammerInf (8 / 3) (1 / 2) *
        qPhi [1 / 2, 0] [(3 / 4) * (1 / 2)] (1 / 2) 0 = 1 := by
  rw [sum_qPochhammer_two_div_four_thirds]
  norm_num [qPochhammerListInf, infinite_qPochhammer_two]

end DLMF.QHypergeometric
