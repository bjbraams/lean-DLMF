/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Analysis.Complex.Basic

/-!
# Uniqueness of meromorphic continuation

Agreement on a neighbourhood propagates through a connected domain as agreement on
punctured neighbourhoods. At points where both functions are continuous, their values
also agree. Exceptional totalized values at poles need not agree.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology

namespace MeromorphicOn

/-- Meromorphic functions on a connected complex domain that agree near one point agree
on a punctured neighbourhood of every point of the domain. -/
theorem eventuallyEq_nhdsNE_of_isConnected_of_eventuallyEq {f g : ℂ → ℂ} {U : Set ℂ}
    (hf : MeromorphicOn f U) (hg : MeromorphicOn g U) (hU : IsConnected U)
    {w : ℂ} (hw : w ∈ U) (he : f =ᶠ[𝓝 w] g) {z : ℂ} (hz : z ∈ U) :
    f =ᶠ[𝓝[≠] z] g := by
  have hd : MeromorphicOn (f - g) U := hf.sub hg
  have htop : meromorphicOrderAt (f - g) w = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    filter_upwards [he.filter_mono nhdsWithin_le_nhds] with v hv
    simp only [Pi.sub_apply, Pi.zero_apply, hv, sub_self]
  have hzTop : meromorphicOrderAt (f - g) z = ⊤ := by
    by_contra hne
    have hall := (hd.exists_meromorphicOrderAt_ne_top_iff_forall_mem hU).mp ⟨z, hz, hne⟩
    exact hall w hw htop
  filter_upwards [meromorphicOrderAt_eq_top_iff.mp hzTop] with v hv
  exact sub_eq_zero.mp hv

/-- At a point of continuity, uniqueness of meromorphic continuation gives equality of
the values, without restrictions on exceptional values elsewhere. -/
theorem eq_of_isConnected_of_eventuallyEq {f g : ℂ → ℂ} {U : Set ℂ}
    (hf : MeromorphicOn f U) (hg : MeromorphicOn g U) (hU : IsConnected U)
    {w : ℂ} (hw : w ∈ U) (he : f =ᶠ[𝓝 w] g) {z : ℂ} (hz : z ∈ U)
    (hfc : ContinuousAt f z) (hgc : ContinuousAt g z) : f z = g z := by
  have hne := hf.eventuallyEq_nhdsNE_of_isConnected_of_eventuallyEq hg hU hw he hz
  have hlim := (hfc.tendsto.mono_left (nhdsWithin_le_nhds (s := ({z}ᶜ : Set ℂ)))).congr' hne
  exact tendsto_nhds_unique hlim (hgc.tendsto.mono_left nhdsWithin_le_nhds)

end MeromorphicOn
