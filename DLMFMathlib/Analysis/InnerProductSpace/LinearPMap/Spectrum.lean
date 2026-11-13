/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Bastiaan J Braams
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.SelfAdjoint
import Mathlib.Topology.MetricSpace.Isometry

/-!
# Scalar shifts and spectra of partial linear maps

Being bounded below is an open condition on the scalar shift. For a self-adjoint partial
linear map, injectivity of a shift implies density of its range, including at real scalars.
The density argument adapts TauCeti's `IsSelfAdjoint.denseRange_smul_sub_of_norm_le`:
a vector orthogonal to the range is an eigenvector of the adjoint at the conjugate scalar.
-/

public section

open Set
open scoped InnerProductSpace

/-- The scalar shifts of a partial linear map that are bounded below form an open set. -/
theorem LinearPMap.isOpen_setOf_exists_pos_mul_norm_le_smul_sub
    {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (A : E →ₗ.[𝕜] E) :
    IsOpen {c : 𝕜 | ∃ K : ℝ, 0 < K ∧
      ∀ x : A.domain, K * ‖(x : E)‖ ≤ ‖c • (x : E) - A x‖} := by
  rw [Metric.isOpen_iff]
  rintro c ⟨K, hK, hb⟩
  refine ⟨K / 2, by positivity, ?_⟩
  intro d hd
  refine ⟨K / 2, by positivity, fun x => ?_⟩
  have hdist : ‖d - c‖ < K / 2 := by simpa only [Metric.mem_ball, dist_eq_norm] using hd
  have htri : ‖c • (x : E) - A x‖ ≤
      ‖d • (x : E) - A x‖ + ‖d - c‖ * ‖(x : E)‖ := by
    calc
      ‖c • (x : E) - A x‖ =
          ‖d • (x : E) - A x - (d - c) • (x : E)‖ := by
        congr 1
        rw [sub_smul]
        abel
      _ ≤ ‖d • (x : E) - A x‖ + ‖(d - c) • (x : E)‖ := norm_sub_le _ _
      _ = _ := by rw [norm_smul]
  have hmul := mul_le_mul_of_nonneg_right hdist.le (norm_nonneg (x : E))
  nlinarith [hb x]
/-- An injective scalar shift of a self-adjoint partial linear map has dense range. -/
theorem IsSelfAdjoint.denseRange_smul_sub_of_injective {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] {A : E →ₗ.[ℂ] E}
    (hA : IsSelfAdjoint A) {c : ℂ}
    (hinj : Function.Injective (fun x : A.domain => c • (x : E) - A x)) :
    DenseRange (fun x : A.domain => c • (x : E) - A x) := by
  by_cases hc : c.im = 0
  · rw [DenseRange, ← A.coe_range_smulSub c]
    refine Submodule.dense_iff_topologicalClosure_eq_top.mpr
      (Submodule.topologicalClosure_eq_top_iff.mpr ((Submodule.eq_bot_iff _).mpr fun y hy => ?_))
    have hortho : ∀ x : A.domain, inner ℂ y (c • (x : E) - A x) = 0 := fun x =>
      (Submodule.mem_orthogonal' _ y).mp hy _
        (LinearMap.mem_range.mpr ⟨x, A.smulSub_apply c x⟩)
    obtain ⟨hy', hAy⟩ :=
      LinearPMap.exists_adjoint_apply_eq_of_inner_smul_sub_eq_zero hA.dense_domain hortho
    obtain ⟨z, hz, hAz⟩ :=
      LinearPMap.exists_of_le (LinearPMap.isSelfAdjoint_def.mp hA).le ⟨y, hy'⟩
    change y = (z : E) at hz
    have heig : A z = c • (z : E) := by
      rw [← hAz, hAy, hz, Complex.conj_eq_iff_im.mpr hc]
    have hz0 : z = 0 := hinj (by simp only [heig, sub_self, Submodule.coe_zero,
      smul_zero, LinearPMap.map_zero])
    rw [hz0, Submodule.coe_zero] at hz
    exact hz
  · exact hA.denseRange_smul_sub hc
