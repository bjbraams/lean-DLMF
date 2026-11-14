/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Combinatorics.SimpleGraph.MatchingPolynomial
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Data.Finset.Max

/-!
# The first-internal-edge cancellation involution

Andrews, Askey and Roy, *Special Functions*, Lemmas 6.9.8–6.9.9,
pp. 328–330 (synopsis AAR-6.8.1–6.9.9). A fixed ordering of the labeled edges
selects the first forbidden edge in an ambient matching. Toggling membership
of that edge in the internal matching reverses the sign and is an involution.
-/

@[expose] public noncomputable section

open Finset
open scoped Classical symmDiff

namespace SimpleGraph

variable {V : Type*} [Fintype V] [LinearOrder (Sym2 V)]

/-- Toggle the first ambient edge belonging to the forbidden graph.
Andrews–Askey–Roy, *Special Functions*, Lemmas 6.9.8–6.9.9, pp. 328–330
(synopsis AAR-6.8.1–6.9.9). With no forbidden edge present the matching is fixed. -/
def toggleFirstInternalEdge (G : SimpleGraph V) (M P : Finset (Sym2 V)) : Finset (Sym2 V) :=
  if h : (P ∩ G.edgeFinset).Nonempty then M ∆ {(P ∩ G.edgeFinset).min' h} else M

/-- The first-edge toggle is exactly symmetric difference with the selected edge. -/
theorem toggleFirstInternalEdge_def (G : SimpleGraph V) (M P : Finset (Sym2 V)) :
    toggleFirstInternalEdge G M P =
      if h : (P ∩ G.edgeFinset).Nonempty then M ∆ {(P ∩ G.edgeFinset).min' h} else M := rfl

/-- Applying the same first-edge toggle twice restores the internal edge set. -/
theorem toggleFirstInternalEdge_involutive (G : SimpleGraph V) (P : Finset (Sym2 V)) :
    Function.Involutive (fun M => toggleFirstInternalEdge G M P) := by
  intro M
  by_cases h : (P ∩ G.edgeFinset).Nonempty <;> simp [toggleFirstInternalEdge, h]

/-- On configurations with a forbidden edge, the explicit involution preserves matchings
and reverses the internal-edge sign without fixed points. Andrews–Askey–Roy,
*Special Functions*, Lemmas 6.9.8–6.9.9, pp. 328–330
(synopsis AAR-6.8.1–6.9.9). Perfectness of the ambient matching is unnecessary. -/
theorem toggleFirstInternalEdge_preserves_matching_and_negates_sign
    (G : SimpleGraph V) {M P : Finset (Sym2 V)}
    (hM : M ∈ matchingEdgeFinsets G) (hP : P ∈ matchingEdgeFinsets (⊤ : SimpleGraph V))
    (hsubset : M ⊆ P) (hinternal : (P ∩ G.edgeFinset).Nonempty) :
    toggleFirstInternalEdge G M P ∈ matchingEdgeFinsets G ∧
      toggleFirstInternalEdge G M P ⊆ P ∧ toggleFirstInternalEdge G M P ≠ M ∧
      (-1 : ℤ) ^ (toggleFirstInternalEdge G M P).card = -((-1 : ℤ) ^ M.card) := by
  sorry

end SimpleGraph
