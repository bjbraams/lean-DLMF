/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.Compactness.Compact

/-!
# Combining local integral majorants on a compact set

If a parameterized family admits a nonnegative integrable majorant near each point of a
compact set, finitely many such majorants give a single eventual bound on the whole set.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace MeasureTheory

/-- Local eventual integral bounds combine to a single majorant on a compact set. -/
theorem _root_.IsCompact.exists_integrable_bound_of_locally
    {X E A : Type*} [TopologicalSpace X] [MeasurableSpace X] [NormedAddCommGroup E]
    {μ : Measure X} {l : Filter A} {F : A → X → E} {K : Set X} (hK : IsCompact K)
    (hlocal : ∀ x ∈ K, ∃ U ∈ 𝓝 x, ∃ g : X → ℝ,
      Integrable g μ ∧ (∀ t, 0 ≤ g t) ∧ ∀ᶠ a in l, ∀ t ∈ U, ‖F a t‖ ≤ g t) :
    ∃ g : X → ℝ, Integrable g μ ∧ (∀ t, 0 ≤ g t) ∧
      ∀ᶠ a in l, ∀ t ∈ K, ‖F a t‖ ≤ g t := by
  refine IsCompact.induction_on hK ?_ ?_ ?_ ?_
  · exact ⟨0, integrable_zero _ _ _, fun _ => le_rfl,
      Eventually.of_forall fun _ _ h => False.elim h⟩
  · intro S T hST ⟨g, hg, hg0, hb⟩
    exact ⟨g, hg, hg0, hb.mono fun a ha t ht => ha t (hST ht)⟩
  · intro S T ⟨g, hg, hg0, hb⟩ ⟨h, hh, hh0, hc⟩
    refine ⟨g + h, hg.add hh, fun t => add_nonneg (hg0 t) (hh0 t), ?_⟩
    filter_upwards [hb, hc] with a ha h'a t ht
    rcases ht with ht | ht
    · exact (ha t ht).trans (le_add_of_nonneg_right (hh0 t))
    · exact (h'a t ht).trans (le_add_of_nonneg_left (hg0 t))
  · intro x hx
    obtain ⟨U, hU, g, hg, hg0, hb⟩ := hlocal x hx
    exact ⟨U, nhdsWithin_le_nhds hU, g, hg, hg0, hb⟩

end MeasureTheory
