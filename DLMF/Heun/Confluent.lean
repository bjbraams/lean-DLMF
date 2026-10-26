/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Heun.Basic

/-!
# Confluent forms of Heun's equation (DLMF §31.12)

The four standard confluent forms 31.12.1–31.12.4 are defined in DLMF/Heun/Basic.lean
(`IsConfluentHeunSolOn`, `IsDoublyConfluentHeunSolOn`, `IsBiconfluentHeunSolOn` with the sign
corrected in DLMF 1.0.7, `IsTriconfluentHeunSolOn`). This file records the classification of
their singular points stated after each equation: at most regular singular points through the
API of `DLMFMathlib.Analysis.ODE.Singularities`, and the ranks of the irregular singularities
through Poincaré's rank (`HasIrregularRankAtInfinity`, `HasIrregularRankAt`). The rank
statements need the leading coefficient to be nonzero (`ε ≠ 0` for 31.12.1, `δ ≠ 0` at `0` for
31.12.2); for other parameters the singularity is weaker.

The remark that Mathieu, spheroidal and Coulomb spheroidal functions are special cases of
solutions of the confluent Heun equation (31.12.1) is not acquired: it is not attached to
explicit transformations in DLMF.
-/

@[expose] public section

open Filter Asymptotics
open scoped Topology

noncomputable section

namespace DLMF.Heun

/-- DLMF 31.12.1: the confluent Heun equation has at most regular singular points at `z = 0`
and `z = 1`, every other finite point is ordinary, and for `ε ≠ 0` it has an irregular
singularity of rank `1` at `∞`. Coefficients indexed as in `heunODECoeff`. -/
@[dlmf 31.12.E1]
theorem confluentHeun_singularities (q α γ δ ε : ℂ) (hε : ε ≠ 0) :
    let c : Fin 2 → ℂ → ℂ := ![fun z => (α * z - q) / (z * (z - 1)),
      fun z => γ / z + δ / (z - 1) + ε]
    Complex.linearODEAtMostRegularAt c 0 ∧ Complex.linearODEAtMostRegularAt c 1 ∧
    (∀ z : ℂ, z ≠ 0 → z ≠ 1 → Complex.linearODEOrdinaryAt c z) ∧
    HasIrregularRankAtInfinity (fun z => γ / z + δ / (z - 1) + ε)
      (fun z => (α * z - q) / (z * (z - 1))) 1 := by
  sorry

/-- DLMF 31.12.2: the doubly-confluent Heun equation has irregular singularities of rank `1` at
`z = 0` (for `δ ≠ 0`) and at `∞`, and every other finite point is ordinary. -/
@[dlmf 31.12.E2]
theorem doublyConfluentHeun_singularities (q α γ δ : ℂ) (hδ : δ ≠ 0) :
    let c : Fin 2 → ℂ → ℂ := ![fun z => (α * z - q) / z ^ 2, fun z => δ / z ^ 2 + γ / z + 1]
    (∀ z : ℂ, z ≠ 0 → Complex.linearODEOrdinaryAt c z) ∧
    HasIrregularRankAt (fun z => δ / z ^ 2 + γ / z + 1) (fun z => (α * z - q) / z ^ 2) 0 1 ∧
    HasIrregularRankAtInfinity (fun z => δ / z ^ 2 + γ / z + 1)
      (fun z => (α * z - q) / z ^ 2) 1 := by
  sorry

/-- DLMF 31.12.3: the biconfluent Heun equation (sign as corrected in DLMF 1.0.7) has an at
most regular singular point at `z = 0`, every other finite point is ordinary, and it has an
irregular singularity of rank `2` at `∞`. -/
@[dlmf 31.12.E3]
theorem biconfluentHeun_singularities (q α γ δ : ℂ) :
    let c : Fin 2 → ℂ → ℂ := ![fun z => (α * z - q) / z, fun z => -(γ / z + δ + z)]
    Complex.linearODEAtMostRegularAt c 0 ∧
    (∀ z : ℂ, z ≠ 0 → Complex.linearODEOrdinaryAt c z) ∧
    HasIrregularRankAtInfinity (fun z => -(γ / z + δ + z)) (fun z => (α * z - q) / z) 2 := by
  sorry

/-- DLMF 31.12.4: the triconfluent Heun equation has no finite singular points (every finite
point is ordinary). -/
@[dlmf 31.12.E4]
theorem triconfluentHeun_ordinary (q α γ : ℂ) (z : ℂ) :
    Complex.linearODEOrdinaryAt (![fun z => α * z - q, fun z => (γ + z) * z] : Fin 2 → ℂ → ℂ)
      z := by
  intro j
  refine ⟨(![fun z => α * z - q, fun z => (γ + z) * z] : Fin 2 → ℂ → ℂ) j, ?_,
    Filter.EventuallyEq.rfl⟩
  fin_cases j
  · simp only [Fin.zero_eta, Matrix.cons_val_zero]
    fun_prop
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    fun_prop

/-- DLMF 31.12.4: the triconfluent Heun equation has an irregular singularity of rank `3` at
`∞`. -/
@[dlmf 31.12.E4]
theorem triconfluentHeun_rank_infinity (q α γ : ℂ) :
    HasIrregularRankAtInfinity (fun z => (γ + z) * z) (fun z => α * z - q) 3 := by
  have h1 := eventually_cobounded_le_norm (E := ℂ) 1
  refine ⟨by norm_num, ?_, ?_, ?_⟩
  · norm_num
    refine IsBigO.of_bound (‖γ‖ + 1) ?_
    filter_upwards [h1] with z hz
    rw [norm_mul, norm_pow, sq]
    have : ‖γ + z‖ ≤ (‖γ‖ + 1) * ‖z‖ := by
      calc ‖γ + z‖ ≤ ‖γ‖ + ‖z‖ := norm_add_le _ _
        _ ≤ ‖γ‖ * ‖z‖ + ‖z‖ := by nlinarith [norm_nonneg γ]
        _ = _ := by ring
    nlinarith [norm_nonneg z]
  · norm_num
    refine IsBigO.of_bound (‖α‖ + ‖q‖) ?_
    filter_upwards [h1] with z hz
    rw [norm_pow]
    have h4 : ‖z‖ ≤ ‖z‖ ^ 4 := by
      calc ‖z‖ = ‖z‖ ^ 1 := (pow_one _).symm
        _ ≤ ‖z‖ ^ 4 := pow_le_pow_right₀ hz (by norm_num)
    have h4' : 1 ≤ ‖z‖ ^ 4 := one_le_pow₀ hz
    calc ‖α * z - q‖ ≤ ‖α‖ * ‖z‖ + ‖q‖ := by
          rw [← norm_mul]; exact norm_sub_le _ _
      _ ≤ ‖α‖ * ‖z‖ ^ 4 + ‖q‖ * ‖z‖ ^ 4 := by
          gcongr
          · nlinarith [norm_nonneg q]
      _ = _ := by ring
  · rintro ⟨hp, -⟩
    norm_num at hp
    obtain ⟨c, hc⟩ := hp.bound
    have h2 := eventually_cobounded_le_norm (E := ℂ) (max 1 (|c| + ‖γ‖ + 1))
    obtain ⟨z, hz, hz2⟩ := (hc.and h2).exists
    have hz1 : 1 ≤ ‖z‖ := le_trans (le_max_left _ _) hz2
    have hz3 : |c| + ‖γ‖ + 1 ≤ ‖z‖ := le_trans (le_max_right _ _) hz2
    rw [norm_mul] at hz
    have hpos : 0 < ‖z‖ := by linarith
    have : ‖γ + z‖ ≤ c := by
      have := le_of_mul_le_mul_right (a := ‖z‖) (by simpa using hz) hpos
      exact this
    have : ‖z‖ - ‖γ‖ ≤ ‖γ + z‖ := by
      have := norm_sub_norm_le z (-γ)
      simpa [sub_neg_eq_add, add_comm] using this
    linarith [le_abs_self c]

end DLMF.Heun
