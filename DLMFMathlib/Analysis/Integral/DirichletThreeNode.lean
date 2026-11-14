/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.Transform.Euler
import Dirichlet.Transform.Merge
import Dirichlet.Complex.Aggregation

/-!
# Three-coordinate Dirichlet integrals

The stick-breaking representation of a regularized Dirichlet integral with three positive
real parameters expresses it as two successive weighted Euler integrals.

## Main results

* `Dirichlet.regDirichletIntegral_fin_three_ofReal`: the iterated Euler integral representation
  for an arbitrary continuous complex-valued kernel on the standard simplex.

## Implementation notes

The proof reuses `Dirichlet.regDirichletIntegral_ofReal_eq_merge` and
`Dirichlet.regDirichletIntegral_aggregate` from `lean-codes`; it does not reconstruct the
Dirichlet measure or copy their proofs.
-/

open Complex Set MeasureTheory
namespace Dirichlet

namespace ThreeNodeIntegration

/-- The two surviving coordinate indices after merging coordinates zero and one. -/
private def mergedIndex (j : {i : Fin 3 // i ≠ 1}) : Fin 2 :=
  if (j : Fin 3) = 0 then 0 else 1

/-- Both surviving coordinate indices occur. -/
private lemma surjective_mergedIndex : Function.Surjective mergedIndex := by
  intro j
  fin_cases j
  · exact ⟨⟨0, by decide⟩, rfl⟩
  · exact ⟨⟨2, by decide⟩, rfl⟩

/-- Aggregation along the surviving indices reads the first and last coordinates. -/
private lemma aggregate_mergedIndex {R : Type*} [CommSemiring R]
    (y : {i : Fin 3 // i ≠ 1} → R) :
    stdSimplexAggregate mergedIndex y = ![y ⟨0, by decide⟩, y ⟨2, by decide⟩] := by
  funext j
  fin_cases j
  · simp only [stdSimplexAggregate, FunOnFinite.linearMap_apply_apply]
    have hset : (Finset.univ.filter fun j => mergedIndex j = 0) =
        {⟨0, by decide⟩} := by
      ext j
      obtain ⟨j, hj⟩ := j
      fin_cases j
      · simp [mergedIndex]
      · exact (hj rfl).elim
      · simp [mergedIndex]
    simpa using congrArg (fun s => Finset.sum s y) hset
  · simp only [stdSimplexAggregate, FunOnFinite.linearMap_apply_apply]
    have hset : (Finset.univ.filter fun j => mergedIndex j = 1) =
        {⟨2, by decide⟩} := by
      ext j
      obtain ⟨j, hj⟩ := j
      fin_cases j
      · simp [mergedIndex]
      · exact (hj rfl).elim
      · simp [mergedIndex]
    simpa using congrArg (fun s => Finset.sum s y) hset

end ThreeNodeIntegration

open ThreeNodeIntegration in
/-- A three-coordinate Dirichlet integral is an iterated weighted Euler integral. -/
public theorem regDirichletIntegral_fin_three_ofReal {b : Fin 3 → ℝ}
    (hb : ∀ i, 0 < b i) {g : (Fin 3 → ℝ) → ℂ}
    (hg : ContinuousOn g (Convexity.StdSimplex.coordinateSet ℝ (Fin 3))) :
    regDirichletIntegral (fun i => (b i : ℂ)) g =
      Gamma ((b 0 : ℂ) + b 1) * regEulerIntegral (b 0) (b 1) (fun v =>
        regEulerIntegral ((b 0 : ℂ) + b 1) (b 2)
          (fun s => g ![v * s, (1 - v) * s, 1 - s])) := by
  have hmerge := regDirichletIntegral_ofReal_eq_merge (a := (0 : Fin 3))
    (a' := 1) (by decide) hb hg
  rw [hmerge]
  congr 1
  have hinner (v : Fin 2 → ℝ) (hv : v ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 2)) :
      regDirichletIntegral (mergeParam (0 : Fin 3) 1 (fun i => (b i : ℂ)))
          (fun y => g (mergeMap (by decide : (0 : Fin 3) ≠ 1) v y)) =
      regEulerIntegral ((b 0 : ℂ) + b 1) (b 2)
        (fun s => g ![v 0 * s, v 1 * s, 1 - s]) := by
    let G : (Fin 2 → ℝ) → ℂ := fun u => g ![v 0 * u 0, v 1 * u 0, u 1]
    have hG : ContinuousOn G (Convexity.StdSimplex.coordinateSet ℝ (Fin 2)) := by
      apply hg.comp (by fun_prop)
      intro u hu
      refine ⟨?_, ?_⟩
      · intro i
        fin_cases i
        · exact mul_nonneg (hv.1 0) (hu.1 0)
        · exact mul_nonneg (hv.1 1) (hu.1 0)
        · exact hu.1 1
      · have huv := hv.2
        have huu := hu.2
        simp only [Fin.sum_univ_two] at huv huu
        simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
        linear_combination (u 0) * huv + huu
    have hm : mergeParam (0 : Fin 3) 1 (fun i => (b i : ℂ)) ∈ mvBetaConvergent :=
      mergeParam_ofReal_mem hb
    have hagg := regDirichletIntegral_aggregate surjective_mergedIndex hm hG
    rw [aggregate_mergedIndex] at hagg
    have hpars : ![mergeParam (0 : Fin 3) 1 (fun i => (b i : ℂ)) ⟨0, by decide⟩,
        mergeParam (0 : Fin 3) 1 (fun i => (b i : ℂ)) ⟨2, by decide⟩] =
        ![(b 0 : ℂ) + b 1, b 2] := by simp [mergeParam]
    rw [hpars] at hagg
    have hmapeq : (fun y => G (stdSimplexAggregate mergedIndex y)) =
        fun y => g (mergeMap (by decide : (0 : Fin 3) ≠ 1) v y) := by
      funext y
      rw [aggregate_mergedIndex]
      dsimp only [G]
      congr 1
      funext j
      fin_cases j <;> simp [mergeMap, mergeIndex]
    rw [hmapeq] at hagg
    rw [hagg, ← regDirichletIntegral_fin_two]
    apply regDirichletIntegral_congr
    intro u hu
    have hsum := hu.2
    simp only [Fin.sum_univ_two] at hsum
    have hu1 : u 1 = 1 - u 0 := by linarith [hsum]
    simp only [G, hu1]
  rw [← regDirichletIntegral_fin_two]
  apply regDirichletIntegral_congr
  intro v hv
  dsimp only
  rw [hinner v hv]
  have hsum := hv.2
  simp only [Fin.sum_univ_two] at hsum
  have hv1 : v 1 = 1 - v 0 := by linarith [hsum]
  rw [hv1]
end Dirichlet
