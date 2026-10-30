/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Locally uniform parameter limits from continuous extensions

Joint continuity along a parameter slice gives locally uniform convergence to that slice.
Consequently, an already known pointwise limit is locally uniform whenever the family agrees
near the parameter with such a continuous extension.
-/

@[expose] public section

open Filter Set
open scoped Topology

/-- Joint continuity along a parameter slice gives locally uniform convergence to that slice. -/
theorem tendstoLocallyUniformlyOn_of_joint_continuousAt
    {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β] [UniformSpace γ]
    {E : α → β → γ} {a : α} {U : Set β} {p : Filter α} (hp : p ≤ 𝓝 a) (hU : IsOpen U)
    (hc : ∀ z ∈ U, ContinuousAt (fun q : α × β => E q.1 q.2) (a,z)) :
    TendstoLocallyUniformlyOn E (E a) p U := by
  apply hU.tendstoLocallyUniformlyOn_iff_forall_tendsto.mpr
  intro z hz
  have hmono : p ×ˢ 𝓝 z ≤ 𝓝 (a,z) := by
    rw [nhds_prod_eq]
    exact Filter.prod_mono hp le_rfl
  have hmap : Tendsto (fun q : α × β => (a,q.2)) (p ×ˢ 𝓝 z) (𝓝 (a,z)) :=
    tendsto_const_nhds.prodMk_nhds tendsto_snd
  have h₁ := (hc z hz).tendsto.comp hmap
  have h₂ := (hc z hz).tendsto.mono_left hmono
  exact (h₁.prodMk_nhds h₂).mono_right (nhds_le_uniformity _)

/-- A local continuous extension upgrades an identified pointwise limit to locally uniform
 convergence, for any nontrivial parameter filter approaching the extension point. -/
theorem tendstoLocallyUniformlyOn_of_local_extension
    {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β] [UniformSpace γ] [T2Space γ]
    {F E : α → β → γ} {g : β → γ} {a : α} {U : Set β} {p : Filter α} [p.NeBot]
    (hp : p ≤ 𝓝 a) (hU : IsOpen U)
    (hc : ∀ z ∈ U, ContinuousAt (fun q : α × β => E q.1 q.2) (a,z))
    (he : ∀ᶠ m in p, U.EqOn (E m) (F m))
    (hl : ∀ z ∈ U, Tendsto (fun m => F m z) p (𝓝 (g z))) :
    TendstoLocallyUniformlyOn F g p U := by
  have ht := (tendstoLocallyUniformlyOn_of_joint_continuousAt hp hU hc).congr_inseparable
    (he.mono fun m hm z hz => Inseparable.of_eq (hm hz))
  refine ht.congr_right fun z hz => ?_
  exact tendsto_nhds_unique (ht.tendsto_at hz) (hl z hz)
