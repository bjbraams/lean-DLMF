/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.Basic
public import DLMF.Bailey

/-!
# Root-free very-well-poised basic series

Andrews, Askey and Roy, *Special Functions*, §12.3, pp. 586–589.
The canonical Bailey numerator `unitD` cancels `(1-a)` before evaluation,
so the series has its intended values at `a = 0` and `a = 1` and is independent
of a chosen square-root sign. Other upper parameters are nonzero when their
complementary quotients `aq/b` are interpreted analytically.
-/

@[expose] public noncomputable section

open Complex

namespace DLMF.QHypergeometric.VeryWellPoised

/-- The root-free very-well-poised coefficient. Five extra upper parameters give `8W7`,
and three give `6W5`. Andrews–Askey–Roy, *Special Functions*, §12.3,
pp. 586–589 (synopsis AAR-12.3–12.4). The apparent `1-a` denominator is canceled. -/
def coefficient (a : ℂ) (b : List ℂ) (q : ℂ) (n : ℕ) : ℂ :=
  DLMF.Bailey.unitD a q n * DLMF.QHypergeometric.qPochhammerList b q n /
    (DLMF.QSeries.qPochhammer q q n *
      DLMF.QHypergeometric.qPochhammerList (b.map fun u => a * q / u) q n)

/-- The defining canceled coefficient formula. -/
theorem coefficient_def (a : ℂ) (b : List ℂ) (q : ℂ) (n : ℕ) :
    coefficient a b q n =
      DLMF.Bailey.unitD a q n * DLMF.QHypergeometric.qPochhammerList b q n /
        (DLMF.QSeries.qPochhammer q q n *
          DLMF.QHypergeometric.qPochhammerList (b.map fun u => a * q / u) q n) := rfl

/-- The constant coefficient is one at every central parameter. -/
@[simp] theorem coefficient_zero (a : ℂ) (b : List ℂ) (q : ℂ) : coefficient a b q 0 = 1 := by
  induction b with
  | nil => simp [coefficient, DLMF.Bailey.unitD, qPochhammerList]
  | cons u b ih =>
    simpa [coefficient, DLMF.Bailey.unitD, qPochhammerList] using ih

/-- The very-well-poised series, with its canonical canceled coefficient convention.
Andrews–Askey–Roy, *Special Functions*, §12.3, synopsis AAR-12.3–12.4.
This totalized sum is used as an analytic value only when the series converges. -/
def value (a : ℂ) (b : List ℂ) (q z : ℂ) : ℂ :=
  ∑' n : ℕ, coefficient a b q n * z ^ n

/-- The defining series of the root-free value. -/
theorem value_def (a : ℂ) (b : List ℂ) (q z : ℂ) :
    value a b q z = ∑' n : ℕ, coefficient a b q n * z ^ n := rfl

/-- At the argument zero the root-free series has value one. -/
@[simp] theorem value_zero (a : ℂ) (b : List ℂ) (q : ℂ) : value a b q 0 = 1 := by
  rw [value, tsum_eq_single 0]
  · simp
  · intro n hn
    simp [zero_pow hn]

/-- The central parameter one has the canceled factor `1+q^n` at positive degree.
Andrews–Askey–Roy, *Special Functions*, §12.3, synopsis AAR-12.3–12.4. -/
theorem coefficient_one {q : ℂ} (hq : ‖q‖ < 1) (b : List ℂ) (n : ℕ) :
    coefficient 1 b q n = if n = 0 then 1 else
      (1 + q ^ n) * DLMF.QHypergeometric.qPochhammerList b q n /
        DLMF.QHypergeometric.qPochhammerList (b.map fun u => q / u) q n := by
  sorry

/-- The root-free coefficient is exactly the paired-square-root basic-series coefficient
where the latter is regular. Andrews–Askey–Roy, *Special Functions*, §12.3,
synopsis AAR-12.3–12.4. Changing the square-root sign just interchanges paired entries. -/
theorem qPhiTerm_eq_coefficient {a q : ℂ} (b : List ℂ) (z : ℂ) (n : ℕ)
    (hregular : n = 0 ∨ (a ≠ 1 ∧
      DLMF.QSeries.qPochhammer (sqrt a) q n *
        DLMF.QSeries.qPochhammer (-sqrt a) q n ≠ 0)) :
    qPhiTerm ([a, q * sqrt a, -q * sqrt a] ++ b)
      ([sqrt a, -sqrt a] ++ b.map (fun u => a * q / u)) q z n =
      coefficient a b q n * z ^ n := by
  sorry

/-- Rogers's nonterminating very-well-poised summation in the canceled convention.
Andrews–Askey–Roy, *Special Functions*, equation (12.3.6), pp. 588–589
(synopsis AAR-12.3–12.4). This includes `a=0,1`; no regularity of either
square-root parameter is required. -/
theorem hasSum_six_phi_five {a b c d q : ℂ} (hqzero : q ≠ 0) (hq : ‖q‖ < 1)
    (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (hlower : QDenominatorRegular [a * q / b, a * q / c, a * q / d] q)
    (hconv : ‖a * q / (b * c * d)‖ < 1) :
    HasSum (fun n : ℕ => coefficient a [b, c, d] q n * (a * q / (b * c * d)) ^ n)
      (DLMF.QHypergeometric.qPochhammerListInf [a * q, a * q / (b * c),
        a * q / (b * d), a * q / (c * d)] q /
        DLMF.QHypergeometric.qPochhammerListInf [a * q / b, a * q / c, a * q / d,
          a * q / (b * c * d)] q) := by
  sorry


/-- Jackson's finite summation with the central removable value retained.
Andrews–Askey–Roy, *Special Functions*, equation (12.3.5), pp. 588–589
(synopsis AAR-12.3–12.4). Only denominators through the terminating index
are excluded. Clearing the final quotient retains its removable specializations. -/
theorem sum_eight_phi_seven_mul_denominator {a b c d e q : ℂ}
    (hqzero : q ≠ 0) (hq : ‖q‖ < 1) (hb : b ≠ 0) (hc : c ≠ 0)
    (hd : d ≠ 0) (he : e ≠ 0) (n : ℕ)
    (hbal : a ^ 2 * q ^ (n + 1) = b * c * d * e)
    (hlower : QDenominatorRegularThrough
      [a * q / b, a * q / c, a * q / d, a * q / e, a * q ^ (n + 1)] q n) :
    (∑ k ∈ Finset.range (n + 1),
      coefficient a [b, c, d, e, q ^ (-(n : ℤ))] q k * q ^ k) *
        qPochhammerList [a * q / b, a * q / c, a * q / d,
          a * q / (b * c * d)] q n =
      qPochhammerList [a * q, a * q / (b * c), a * q / (b * d),
        a * q / (c * d)] q n := by
  sorry

end DLMF.QHypergeometric.VeryWellPoised
