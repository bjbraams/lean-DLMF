/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Topology.Order.Monotone
public import Mathlib.Order.Filter.IsBounded
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Endpoint divergence of monotone functions

A monotone real function on an open interval whose absolute value is unbounded at
an endpoint tends to the corresponding signed infinity. These forms are useful when
an endpoint condition is expressed as failure of eventual boundedness of the norm.
-/

public section
open Set Filter
open scoped Topology

/-- Unbounded absolute value at the right endpoint forces a monotone function to tend to
positive infinity. -/
theorem MonotoneOn.tendsto_atTop_nhdsLT_of_not_isBoundedUnder_abs
    {a b : ℝ} (hab : a < b) {f : ℝ → ℝ} (hf : MonotoneOn f (Ioo a b))
    (hbound : ¬ IsBoundedUnder (· ≤ ·) (𝓝[<] b) (fun x => |f x|)) :
    Tendsto f (𝓝[<] b) atTop := by
  classical
  let c := (a + b) / 2
  have hc : c ∈ Ioo a b := by dsimp only [c]; constructor <;> linarith
  refine tendsto_atTop.mpr fun M => ?_
  let K := max M (-f c)
  have hfreq : ∃ᶠ x in 𝓝[<] b, K < |f x| := by
    have h : ¬ ∀ᶠ x in 𝓝[<] b, |f x| ≤ K := fun h => hbound ⟨K, h⟩
    simpa only [Filter.Frequently, not_lt] using h
  obtain ⟨x, hx, hxmem⟩ := (hfreq.and_eventually (Ioo_mem_nhdsLT hc.2)).exists
  have hxdom : x ∈ Ioo a b := ⟨hc.1.trans hxmem.1, hxmem.2⟩
  have hlower := hf hc hxdom hxmem.1.le
  have hlarge : M ≤ f x := by
    rcases lt_abs.mp hx with h | h
    · exact (le_max_left M (-f c)).trans h.le
    · have hk : -f c ≤ K := le_max_right _ _
      linarith
  filter_upwards [Ioo_mem_nhdsLT hxmem.2] with y hy
  exact hlarge.trans (hf hxdom ⟨hxdom.1.trans hy.1, hy.2⟩ hy.1.le)

/-- Unbounded absolute value at the left endpoint forces a monotone function to tend to
negative infinity. -/
theorem MonotoneOn.tendsto_atBot_nhdsGT_of_not_isBoundedUnder_abs
    {a b : ℝ} (hab : a < b) {f : ℝ → ℝ} (hf : MonotoneOn f (Ioo a b))
    (hbound : ¬ IsBoundedUnder (· ≤ ·) (𝓝[>] a) (fun x => |f x|)) :
    Tendsto f (𝓝[>] a) atBot := by
  classical
  let c := (a + b) / 2
  have hc : c ∈ Ioo a b := by dsimp only [c]; constructor <;> linarith
  refine tendsto_atBot.mpr fun M => ?_
  let K := max (-M) (f c)
  have hfreq : ∃ᶠ x in 𝓝[>] a, K < |f x| := by
    have h : ¬ ∀ᶠ x in 𝓝[>] a, |f x| ≤ K := fun h => hbound ⟨K, h⟩
    simpa only [Filter.Frequently, not_lt] using h
  obtain ⟨x, hx, hxmem⟩ := (hfreq.and_eventually (Ioo_mem_nhdsGT hc.1)).exists
  have hxdom : x ∈ Ioo a b := ⟨hxmem.1, hxmem.2.trans hc.2⟩
  have hupper := hf hxdom hc hxmem.2.le
  have hsmall : f x ≤ M := by
    rcases lt_abs.mp hx with h | h
    · have hk : f c ≤ K := le_max_right _ _
      linarith
    · have hk : -M ≤ K := le_max_left _ _
      linarith
  filter_upwards [Ioo_mem_nhdsGT hxmem.1] with y hy
  exact (hf ⟨hy.1, hy.2.trans hxdom.2⟩ hxdom hy.2.le).trans hsmall
