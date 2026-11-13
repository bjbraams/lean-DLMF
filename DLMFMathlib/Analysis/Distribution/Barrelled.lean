/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Analysis.LocallyConvex.Barrelled
import TauCeti.Analysis.Distribution.TestFunction.Frechet

/-!
# Barrelledness of test-function spaces

A lower-semicontinuous seminorm restricts to a continuous seminorm on every fixed-compact
Fréchet space. Its induced seminorm topology is therefore coarser than the native final
locally convex topology. Thus the seminorm is continuous on the full test-function space.

The proof uses TauCeti's completeness and Baire-space instances for fixed-compact test
functions, together with Mathlib's native final-topology characterization
`TestFunction.topologicalSpace_le_iff`. No countability or finite-dimensionality of the
underlying normed domain is required.

* `TestFunction.instBarrelledSpace`: the test-function space is barrelled.
-/

public section

open Filter Set TopologicalSpace
open scoped Topology Distributions

namespace TestFunction

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Real test functions with values in a Banach space form a barrelled space, for every
regularity order and open domain. -/
instance instBarrelledSpace (Ω : Opens E) (n : ℕ∞) : BarrelledSpace ℝ 𝓓^{n}(Ω, F) := by
  constructor
  intro p hp
  have hstage (K : Compacts E) (hK : (K : Set E) ⊆ Ω) :
      Continuous (p ∘ ofSupportedIn (n := n) hK) := by
    let q := p.comp (ofSupportedInCLM ℝ (n := n) hK).toLinearMap
    have hq : LowerSemicontinuous q := hp.comp (continuous_ofSupportedIn hK)
    exact q.continuous_of_lowerSemicontinuous hq
  let t := p.toSeminormedAddCommGroup.toUniformSpace.toTopologicalSpace
  have hle : topologicalSpace Ω F n ≤ t := by
    let : SeminormedAddCommGroup 𝓓^{n}(Ω, F) := p.toSeminormedAddCommGroup
    let : NormedSpace ℝ 𝓓^{n}(Ω, F) := ⟨fun r x => (map_smul_eq_mul p r x).le⟩
    apply topologicalSpace_le_iff.mpr
    dsimp only [originalTop]
    apply iSup₂_le
    intro K hK
    apply continuous_iff_coinduced_le.mp
    let i : 𝓓^{n}_{K}(E, F) →ₗ[ℝ] 𝓓^{n}(Ω, F) :=
      { toFun := ofSupportedIn hK, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    apply continuous_of_tendsto_nhds_zero i
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hnorm (x : 𝓓^{n}_{K}(E, F)) : ‖i x‖ = p (ofSupportedIn hK x) := rfl
    simpa only [hnorm, Function.comp_def,
      show ofSupportedIn hK (0 : 𝓓^{n}_{K}(E, F)) = 0 from rfl, map_zero] using
        (hstage K hK).tendsto 0
  have hpc : @Continuous 𝓓^{n}(Ω, F) ℝ t inferInstance p := by
    let : SeminormedAddCommGroup 𝓓^{n}(Ω, F) := p.toSeminormedAddCommGroup
    exact continuous_norm
  have ht : t ≤ TopologicalSpace.induced p inferInstance := continuous_iff_le_induced.mp hpc
  exact continuous_iff_le_induced.mpr (hle.trans ht)

end TestFunction


