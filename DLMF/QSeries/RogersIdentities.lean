/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QSeries.Basic

/-!
# Finite Rogers sums and the Andrews–Gordon multisum

Andrews, Askey and Roy, *Special Functions*, §§12.1 and 12.4. The finite
bilateral sums use integer indices and nonnegative pentagonal exponents. The
multisum is an ordinary summable family of decreasing finite tuples.
-/

@[expose] public section

open Finset
open scoped Classical

noncomputable section

namespace DLMF.QSeries

/-- The even finite Rogers sum `S₂ₗ` of Andrews–Askey–Roy, *Special Functions*,
§12.1 (synopsis AAR-12.1.1). -/
def finiteRogersEven (q : ℂ) (l : ℕ) : ℂ :=
  ∑ k ∈ Finset.Icc (-(l : ℤ)) (l : ℤ),
    (-1 : ℂ) ^ k * q ^ (k * (3 * k - 1) / 2).toNat /
      (qPochhammer q q ((l : ℤ) + k).toNat *
        qPochhammer q q ((l : ℤ) - k).toNat)

/-- The defining finite bilateral sum. -/
theorem finiteRogersEven_def (q : ℂ) (l : ℕ) :
    finiteRogersEven q l =
      ∑ k ∈ Finset.Icc (-(l : ℤ)) (l : ℤ),
        (-1 : ℂ) ^ k * q ^ (k * (3 * k - 1) / 2).toNat /
          (qPochhammer q q ((l : ℤ) + k).toNat *
            qPochhammer q q ((l : ℤ) - k).toNat) := rfl

/-- The odd finite Rogers sum `S₂ₗ₊₁` of Andrews–Askey–Roy, *Special Functions*,
§12.1 (synopsis AAR-12.1.1). -/
def finiteRogersOdd (q : ℂ) (l : ℕ) : ℂ :=
  ∑ k ∈ Finset.Icc (-(l : ℤ)) ((l : ℤ) + 1),
    (-1 : ℂ) ^ k * q ^ (k * (3 * k - 1) / 2).toNat /
      (qPochhammer q q ((l : ℤ) + 1 - k).toNat *
        qPochhammer q q ((l : ℤ) + k).toNat)

/-- The defining finite bilateral sum. -/
theorem finiteRogersOdd_def (q : ℂ) (l : ℕ) :
    finiteRogersOdd q l =
      ∑ k ∈ Finset.Icc (-(l : ℤ)) ((l : ℤ) + 1),
        (-1 : ℂ) ^ k * q ^ (k * (3 * k - 1) / 2).toNat /
          (qPochhammer q q ((l : ℤ) + 1 - k).toNat *
            qPochhammer q q ((l : ℤ) + k).toNat) := rfl

/-- Both finite Rogers sums have the same shifted-factorial value.
Andrews–Askey–Roy, *Special Functions*, Lemma 12.1.1
(synopsis AAR-12.1.1). -/
theorem finiteRogers_eq_inv_qPochhammer {q : ℂ} (hq : ‖q‖ < 1) (l : ℕ) :
    finiteRogersEven q l = (qPochhammer q q l)⁻¹ ∧
      finiteRogersOdd q l = (qPochhammer q q l)⁻¹ := by
  sorry

/-- The paired first-order recurrences of the finite Rogers sums.
Andrews–Askey–Roy, *Special Functions*, §12.1 (synopsis AAR-12.1.1). -/
theorem finiteRogers_recurrences {q : ℂ} (hq : ‖q‖ < 1) (l : ℕ) :
    finiteRogersEven q l = finiteRogersOdd q l ∧
      finiteRogersOdd q l = (1 - q ^ (l + 1)) * finiteRogersEven q (l + 1) := by
  sorry

/-- The decreasing-tuple summand in the Andrews–Gordon identity, with a final zero
coordinate. Andrews–Askey–Roy, *Special Functions*, §12.4
(synopsis AAR-12.3–12.4). -/
def andrewsGordonTerm (k : ℕ) (q : ℂ) (v : Fin (k + 1) → ℕ) : ℂ :=
  if Antitone v ∧ v (Fin.last k) = 0 then
    q ^ (∑ i : Fin k, v i.castSucc ^ 2) /
      (∏ i : Fin k, qPochhammer q q (v i.castSucc - v i.succ))
  else 0

/-- The explicit tuple summand, including its monotonicity and final-zero restriction. -/
theorem andrewsGordonTerm_def (k : ℕ) (q : ℂ) (v : Fin (k + 1) → ℕ) :
    andrewsGordonTerm k q v =
      if Antitone v ∧ v (Fin.last k) = 0 then
        q ^ (∑ i : Fin k, v i.castSucc ^ 2) /
          (∏ i : Fin k, qPochhammer q q (v i.castSucc - v i.succ))
      else 0 := rfl

/-- The Andrews–Gordon multisum with excluded residues `0, ±(k+1)` modulo `2k+3`.
Andrews–Askey–Roy, *Special Functions*, §12.4, p. 590
(synopsis AAR-12.3–12.4). The quotient is the product over all other positive residues. -/
theorem hasSum_andrewsGordon {k : ℕ} (hk : 1 ≤ k) {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (andrewsGordonTerm k q)
      (qPochhammerInf (q ^ (k + 1)) (q ^ (2 * k + 3)) *
        qPochhammerInf (q ^ (k + 2)) (q ^ (2 * k + 3)) *
        qPochhammerInf (q ^ (2 * k + 3)) (q ^ (2 * k + 3)) /
        qPochhammerInf q q) := by
  sorry

end DLMF.QSeries
