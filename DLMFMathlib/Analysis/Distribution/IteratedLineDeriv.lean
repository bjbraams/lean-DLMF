/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Distribution.Distribution
public import TauCeti.Analysis.Distribution.TestFunction.LineDeriv

/-!
# Iterated directional derivatives of test functions and distributions

Directional derivatives commute on smooth test functions. Iterating this fact lets a list
of distributional derivatives act on a test function with one minus sign per derivative.
Both identities allow arbitrary real normed source and target spaces. The commutation
step reuses Tau Ceti's `TestFunction.lineDerivOp_comm`.

## Main results

* `TestFunction.iteratedLineDerivOp_comm`: a directional derivative commutes with any finite
  list of directional derivatives of a test function.
* `Distribution.iteratedLineDerivOp_apply`: moving a list of directional derivatives from a
  distribution to a test function gives one minus sign per derivative.
-/

@[expose] public noncomputable section

open scoped Distributions LineDeriv

namespace TestFunction

/-- A directional derivative commutes with any finite list of directional derivatives of a
smooth test function. -/
lemma iteratedLineDerivOp_comm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : TopologicalSpace.Opens E} {r : ℕ}
    (m : Fin r → E) (v : E) (φ : 𝓓(Ω, F)) :
    ∂^{m} (∂_{v} φ) = ∂_{v} (∂^{m} φ) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [LineDeriv.iteratedLineDerivOp_succ_left, ih, lineDerivOp_comm,
      LineDeriv.iteratedLineDerivOp_succ_left]

end TestFunction

namespace Distribution

/-- Moving a list of directional derivatives from a distribution to a test function gives
one minus sign for each derivative. -/
lemma iteratedLineDerivOp_apply {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : TopologicalSpace.Opens E} {r : ℕ}
    (m : Fin r → E) (T : 𝓓'(Ω, F)) (φ : 𝓓(Ω, ℝ)) :
    (∂^{m} T) φ = (-1 : ℝ) ^ r • T (∂^{m} φ) := by
  induction r generalizing φ with
  | zero => simp
  | succ r ih =>
    rw [LineDeriv.iteratedLineDerivOp_succ_left, lineDerivOp_apply_apply, ih,
      LineDeriv.iteratedLineDerivOp_neg, map_neg, TestFunction.iteratedLineDerivOp_comm,
      LineDeriv.iteratedLineDerivOp_succ_left, pow_succ]
    simp

end Distribution
