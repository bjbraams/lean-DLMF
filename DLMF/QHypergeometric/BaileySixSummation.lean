/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.BaileySixSeries
public import DLMF.QHypergeometric.BaileySixProducts

/-!
# Bailey's six-psi-six sum in cleared form

Rogers' six-phi-five sum evaluates the geometric parameter nodes of the bilateral
kernel. Finite product reversal gives the Bailey product at those nodes, and the
identity theorem extends the equality throughout the convergence disk in `x = 1/e`.
This proves the root-free cleared form underlying DLMF 17.8.7.
-/

@[expose] public noncomputable section

open Complex Filter Finset Set
open scoped Topology
open DLMF.QSeries

namespace DLMF.QHypergeometric.BaileySixSummation

/-- The cleared six-psi-six series equals the Bailey product on its convergence disk. -/
theorem tsum_term_eq_productSide {a b c d q x : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (ha : a ≠ 0) (ha1 : a ≠ 1) (hbcd : b * c * d ≠ 0)
    (hL : QDenominatorRegular [a * q / b, a * q / c, a * q / d] q)
    (hU : ∀ u ∈ [b, c, d], ∀ j : ℕ, u ≠ q ^ (j + 1))
    (hx : ‖x‖ < ‖scale a b c d q‖⁻¹) :
    (∑' n : ℤ, term a b c d q x n) = productSide a b c d q x := by
  apply tsum_term_eq_of_eventually_pow hq0 hq ha hbcd _ hx
  filter_upwards [eventually_node_conditions (b := b) (c := c) (d := d) hq0 hq ha]
    with m hm
  exact (tsum_term_pow_eq_shifted hq0 hq ha ha1 hbcd hL hU m hm.1 hm.2).trans
    (shiftFactor_mul_productSide hq0 hq ha ha1 hbcd hU m hm.1 hm.2)

/-- The quotient of the cleared product is the nine-factor Bailey quotient, with totalized
values preserved at every complex parameter. -/
lemma productSide_div_denominator (a b c d e q : ℂ) :
    productSide a b c d q e⁻¹ / denominator a b c d q e⁻¹ =
      qPochhammerListInf [a * q, a * q / (b * c), a * q / (b * d), a * q / (b * e),
        a * q / (c * d), a * q / (c * e), a * q / (d * e), q, q / a] q /
      qPochhammerListInf [a * q / b, a * q / c, a * q / d, a * q / e,
        q / b, q / c, q / d, q / e, q * a ^ 2 / (b * c * d * e)] q := by
  have he (u : ℂ) : a * q * e⁻¹ / u = a * q / (u * e) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hz : scale a b c d q * e⁻¹ = q * a ^ 2 / (b * c * d * e) := by
    simp only [scale, div_eq_mul_inv, mul_inv_rev]
    ring
  unfold productSide denominator
  rw [he b, he c, he d, hz]
  simp only [← div_eq_mul_inv]

end DLMF.QHypergeometric.BaileySixSummation
