/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Topology.Algebra.Module.Spaces.CompactConvergenceCLM
public import Mathlib.Analysis.LocallyConvex.Barrelled
import Mathlib.Topology.UniformSpace.Ascoli

/-!
# Sequential compact convergence on barrelled spaces

Pointwise convergence of a sequence of continuous linear maps gives pointwise boundedness.
Mathlib's Banach–Steinhaus theorem makes the family equicontinuous, and its Ascoli theorem
then gives uniform convergence on every compact set.

* `CompactConvergenceCLM.tendsto_atTop_iff_forall_apply`: compact and pointwise convergence
  agree for sequences with barrelled domain and polynormable target.
-/

public section

open Filter Set TopologicalSpace
open scoped Topology

open scoped CompactConvergenceCLM

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [UniformSpace E] [IsUniformAddGroup E]
  [ContinuousSMul 𝕜 E] [BarrelledSpace 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F] [UniformSpace F] [IsUniformAddGroup F]
  [ContinuousSMul 𝕜 F] [PolynormableSpace 𝕜 F]

/-- For sequences of continuous linear maps from a barrelled space to a polynormable space,
compact convergence is equivalent to pointwise convergence. -/
lemma CompactConvergenceCLM.tendsto_atTop_iff_forall_apply
    (T : ℕ → E →L_c[𝕜] F) (T₀ : E →L_c[𝕜] F) :
    Tendsto T atTop (𝓝 T₀) ↔ ∀ φ : E,
      Tendsto (fun n => T n φ) atTop (𝓝 (T₀ φ)) := by
  constructor
  · intro h φ
    exact (continuous_eval_const φ).tendsto T₀ |>.comp h
  · intro h
    let A : ℕ → E →L[𝕜] F := fun n => T n
    have heq : UniformEquicontinuous (fun n φ => T n φ) :=
      PolynormableSpace.banach_steinhaus (𝓕 := A) fun φ =>
        (h φ).isVonNBounded_range 𝕜
    have hu := (EquicontinuousOn.tendsto_uniformOnFun_iff_pi
      (𝔖 := {K : Set E | IsCompact K})
      (fun _ hK => hK) sUnion_isCompact_eq_univ
      (fun K _ => heq.equicontinuous.equicontinuousOn K) atTop (fun φ => T₀ φ)).mpr
        (tendsto_pi_nhds.mpr h)
    exact (UniformConvergenceCLM.isUniformEmbedding_coeFn (RingHom.id 𝕜) F
      {K : Set E | IsCompact K}).isEmbedding.isInducing.tendsto_nhds_iff.mpr hu

