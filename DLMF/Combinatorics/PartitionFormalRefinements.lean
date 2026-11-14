/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Combinatorics.PartitionRefinements
public import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Largest-part refinements and bivariate coefficient identities

Andrews, Askey and Roy, *Special Functions*, Theorems 11.4.3 and 11.4.6,
pp. 560–563, synopsis AAR-11.4.1–11.4.6. Formal identities use polynomial
coefficients for the length marker and finite truncations in the size variable.
-/

@[expose] public noncomputable section

open scoped Classical
open Finset PowerSeries DLMF.QSeries

namespace DLMF.Combinatorics

/-- The exact length/gap/least-part partition count refined by its largest part.
Andrews–Askey–Roy, Theorem 11.4.3, synopsis AAR-11.4.1–11.4.6. The empty partition has largest
part zero, using the multiset supremum convention. -/
def partitionCountExactGapLargest (k l m j n : ℕ) : ℕ :=
  #{p : n.Partition | p.parts.card = m ∧ PartsDifferAtLeast k p ∧
    (∀ a ∈ p.parts, l ≤ a) ∧ p.parts.sup = j}

/-- The finite filtering definition of the largest-part refinement. -/
theorem partitionCountExactGapLargest_def (k l m j n : ℕ) :
    partitionCountExactGapLargest k l m j n =
      #{p : n.Partition | p.parts.card = m ∧ PartsDifferAtLeast k p ∧
        (∀ a ∈ p.parts, l ≤ a) ∧ p.parts.sup = j} := rfl

/-- The largest-part bivariate generating function for fixed unrestricted length.
Andrews–Askey–Roy, Theorem 11.4.3, synopsis AAR-11.4.1–11.4.6. -/
theorem hasSum_partitionCountExactGapLargest_zero {q z : ℂ}
    (hq : ‖q‖ < 1) (hzq : ‖z * q‖ < 1) (m : ℕ) :
    HasSum (fun jn : ℕ × ℕ =>
      (partitionCountExactGapLargest 0 1 m jn.1 jn.2 : ℂ) * z ^ jn.1 * q ^ jn.2)
      ((qPochhammer (z * q) q m)⁻¹) := by
  sorry

/-- The largest-part bivariate generating function for fixed distinct length.
Andrews–Askey–Roy, Theorem 11.4.3, synopsis AAR-11.4.1–11.4.6. -/
theorem hasSum_partitionCountExactGapLargest_one {q z : ℂ}
    (hq : ‖q‖ < 1) (hzq : ‖z * q‖ < 1) (m : ℕ) :
    HasSum (fun jn : ℕ × ℕ =>
      (partitionCountExactGapLargest 1 1 m jn.1 jn.2 : ℂ) * z ^ jn.1 * q ^ jn.2)
      (z ^ m * q ^ (m * (m + 1) / 2) / qPochhammer (z * q) q m) := by
  sorry

/-- Formal length-marked unrestricted partition coefficients.
Andrews–Askey–Roy, Theorem 11.4.6, synopsis AAR-11.4.1–11.4.6. -/
theorem coeff_length_partition_product (n : ℕ) :
    coeff n (∏ j : Fin n, PowerSeries.invOfUnit
      (1 - C (Polynomial.X : Polynomial ℤ) * X ^ (j.val + 1)) 1) =
      ∑ m ∈ range (n + 1), Polynomial.C (partitionCountExactGap 0 1 m n : ℤ) *
        Polynomial.X ^ m := by
  sorry

/-- Formal length-marked distinct partition coefficients.
Andrews–Askey–Roy, Theorem 11.4.6, synopsis AAR-11.4.1–11.4.6. -/
theorem coeff_length_distinct_partition_product (n : ℕ) :
    coeff n (∏ j : Fin n, (1 + C (Polynomial.X : Polynomial ℤ) * X ^ (j.val + 1))) =
      ∑ m ∈ range (n + 1), Polynomial.C (partitionCountExactGap 1 1 m n : ℤ) *
        Polynomial.X ^ m := by
  sorry

/-- Formal bivariate gap-two coefficients, with arbitrary positive least part.
Andrews–Askey–Roy, Theorem 11.4.6, synopsis AAR-11.4.1–11.4.6. -/
theorem coeff_length_gap_two_partition_sum (n : ℕ) {l : ℕ} (hl : 1 ≤ l) :
    coeff n (∑ m ∈ range (n + 1),
      C ((Polynomial.X : Polynomial ℤ) ^ m) * X ^ (l * m + m * (m - 1)) *
        PowerSeries.invOfUnit (∏ j : Fin m, (1 - X ^ (j.val + 1))) 1) =
      ∑ m ∈ range (n + 1), Polynomial.C (partitionCountExactGap 2 l m n : ℤ) *
        Polynomial.X ^ m := by
  sorry

end DLMF.Combinatorics
