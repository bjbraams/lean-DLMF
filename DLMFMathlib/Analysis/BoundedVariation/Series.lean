/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import Mathlib.Analysis.Normed.Group.InfiniteSum
import DLMFMathlib.Analysis.BoundedVariation.Sampling
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
# Variation of infinite sums

* `eVariationOn.tsum_le` bounds the variation of a pointwise summable series.
* `BoundedVariationOn.summable_variation_int_unit` gives summable variations on integer cells.

The proof uses Mathlib's variation composition and summation APIs, with the nonnegative-cell
summability estimate in `DLMFMathlib.Analysis.BoundedVariation.Sampling`.
-/

public noncomputable section
open Set MeasureTheory Filter Topology TopologicalSpace

namespace BoundedVariationOn
variable {E : Type*} [PseudoMetricSpace E] {f : ℝ → E}
/-- The variations of a whole-line bounded-variation function on its integer cells are summable. -/
lemma summable_variation_int_unit (hbv : BoundedVariationOn f univ) :
    Summable (fun n : ℤ => (eVariationOn f (Icc (n : ℝ) (n + 1))).toReal) := by
  apply summable_int_iff_summable_nat_and_neg.mpr
  constructor
  · simpa only [Int.cast_natCast] using
      (hbv.mono (subset_univ (Ici 0))).summable_variation_nat_unit
  · apply (summable_nat_add_iff 1).mp
    have hbvneg : BoundedVariationOn (fun t : ℝ => f (-t)) (Ici 0) :=
      ne_top_of_le_ne_top hbv (eVariationOn.comp_le_of_antitoneOn f (fun t : ℝ => -t)
        (fun _ _ _ _ h => neg_le_neg h) (fun _ _ => mem_univ _))
    have h := hbvneg.summable_variation_nat_unit
    convert h using 1
    funext n
    congr 1
    have he := eVariationOn.comp_eq_of_antitoneOn f (t := Icc (n : ℝ) (n + 1))
      (fun t : ℝ => -t) (fun _ _ _ _ h => neg_le_neg h)
    rw [Set.image_neg_Icc] at he
    convert he.symm using 1 <;> congr 2 <;> push_cast <;> ring
end BoundedVariationOn
namespace eVariationOn
/-- The variation of a pointwise summable series is bounded by the sum of the variations. -/
lemma tsum_le {α ι E : Type*} [LinearOrder α] [NormedAddCommGroup E]
    {F : ι → α → E} {s : Set α} (hs : ∀ x ∈ s, Summable (fun n => F n x)) :
    eVariationOn (fun x => ∑' n, F n x) s ≤ ∑' n, eVariationOn (F n) s := by
  apply iSup_le
  rintro ⟨N, u, hu, hus⟩
  calc
    _ ≤ ∑ i ∈ Finset.range N, ∑' n, edist (F n (u (i + 1))) (F n (u i)) := by
      apply Finset.sum_le_sum
      intro i _
      rw [edist_eq_enorm_sub, ← (hs (u (i + 1)) (hus _)).tsum_sub (hs (u i) (hus _))]
      simpa only [edist_eq_enorm_sub] using
        (enorm_tsum_le_tsum_enorm (f := fun n => F n (u (i + 1)) - F n (u i)))
    _ = ∑' n, ∑ i ∈ Finset.range N, edist (F n (u (i + 1))) (F n (u i)) :=
      (Summable.tsum_finsetSum (fun _ _ => CompleteLattice.summable)).symm
    _ ≤ _ := tsum_le_tsum (fun _ => eVariationOn.sum_le hu hus)
end eVariationOn
