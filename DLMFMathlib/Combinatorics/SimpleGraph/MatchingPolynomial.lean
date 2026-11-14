/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Sum
public import Mathlib.Combinatorics.SimpleGraph.CompleteMultipartite
public import Mathlib.RingTheory.Polynomial.Hermite.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# Matching polynomials and perfect matching counts

The graph interpretation of Hermite polynomials in Andrews, Askey and Roy,
*Special Functions*, §6.9. A matching is a finite set of edges with pairwise
disjoint endpoint sets. Vertices and edges are labeled.
-/

@[expose] public section

open Finset Polynomial
open scoped Classical

noncomputable section

namespace SimpleGraph

variable {V : Type*} [Fintype V]

/-- All edge matchings of a finite labeled graph. Andrews–Askey–Roy,
*Special Functions*, §6.9 (synopsis AAR-6.8.1–6.9.9). -/
def matchingEdgeFinsets (G : SimpleGraph V) : Finset (Finset (Sym2 V)) :=
  G.edgeFinset.powerset.filter fun M =>
    (M : Set (Sym2 V)).Pairwise fun e f => Disjoint e.toFinset f.toFinset

/-- Membership is exactly containment among the edges and pairwise disjointness. -/
theorem mem_matchingEdgeFinsets_iff (G : SimpleGraph V) (M : Finset (Sym2 V)) :
    M ∈ matchingEdgeFinsets G ↔ M ⊆ G.edgeFinset ∧
      (M : Set (Sym2 V)).Pairwise (fun e f => Disjoint e.toFinset f.toFinset) := by
  simp [matchingEdgeFinsets]

/-- The matching polynomial `∑_M (-1)^|M| X^(|V|-2|M|)`.
Andrews–Askey–Roy, *Special Functions*, §6.9 (synopsis AAR-6.8.1–6.9.9). -/
def matchingPolynomial (G : SimpleGraph V) : ℤ[X] :=
  ∑ M ∈ matchingEdgeFinsets G,
    C ((-1 : ℤ) ^ M.card) * X ^ (Fintype.card V - 2 * M.card)

/-- The finite matching expansion. -/
theorem matchingPolynomial_def (G : SimpleGraph V) :
    matchingPolynomial G = ∑ M ∈ matchingEdgeFinsets G,
      C ((-1 : ℤ) ^ M.card) * X ^ (Fintype.card V - 2 * M.card) := rfl

/-- The number of perfect matchings, including one empty matching on no vertices.
Andrews–Askey–Roy, *Special Functions*, §6.9 (synopsis AAR-6.8.1–6.9.9). -/
def perfectMatchingCount (G : SimpleGraph V) : ℕ :=
  ((matchingEdgeFinsets G).filter fun M => M.biUnion Sym2.toFinset = univ).card

/-- The endpoint-covering finite count. -/
theorem perfectMatchingCount_def (G : SimpleGraph V) :
    perfectMatchingCount G =
      ((matchingEdgeFinsets G).filter fun M => M.biUnion Sym2.toFinset = univ).card := rfl

/-- The matching polynomial of the complete graph is the probabilists' Hermite polynomial.
Andrews–Askey–Roy, *Special Functions*, Theorem 6.9.1
(synopsis AAR-6.8.1–6.9.9). -/
theorem matchingPolynomial_top :
    matchingPolynomial (⊤ : SimpleGraph V) = Polynomial.hermite (Fintype.card V) := by
  sorry

/-- Matching polynomials multiply under disjoint union. Andrews–Askey–Roy,
*Special Functions*, Lemma 6.9.7 (synopsis AAR-6.8.1–6.9.9). -/
theorem matchingPolynomial_sum {W : Type*} [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) :
    matchingPolynomial (G.sum H) = matchingPolynomial G * matchingPolynomial H := by
  sorry

/-- Cancellation of internal matching edges counts perfect matchings in the complement.
Andrews–Askey–Roy, *Special Functions*, Lemmas 6.9.8–6.9.9
(synopsis AAR-6.8.1–6.9.9). Odd Gaussian moments are zero and the empty moment is one. -/
theorem perfectMatchingCount_compl_eq_sum (G : SimpleGraph V) :
    (perfectMatchingCount Gᶜ : ℤ) =
      ∑ M ∈ matchingEdgeFinsets G,
        (-1 : ℤ) ^ M.card *
          if Even (Fintype.card V - 2 * M.card) then
            (Nat.doubleFactorial (Fintype.card V - 2 * M.card - 1) : ℤ)
          else 0 := by
  sorry

/-- Perfect matchings of a complete multipartite graph with labeled blocks.
Andrews–Askey–Roy, *Special Functions*, §6.9 (synopsis AAR-6.8.1–6.9.9). -/
def completeMultipartitePerfectMatchingCount {r : ℕ} (blocks : Fin r → ℕ) : ℕ :=
  perfectMatchingCount (completeMultipartiteGraph fun i => Fin (blocks i))

/-- The graph-count definition of multipartite matching numbers. -/
theorem completeMultipartitePerfectMatchingCount_def {r : ℕ} (blocks : Fin r → ℕ) :
    completeMultipartitePerfectMatchingCount blocks =
      perfectMatchingCount (completeMultipartiteGraph fun i => Fin (blocks i)) := rfl

/-- Pairing a fixed vertex in the first block gives the multipartite recurrence.
Andrews–Askey–Roy, *Special Functions*, Lemma 6.9.2
(synopsis AAR-6.8.1–6.9.9). -/
theorem completeMultipartitePerfectMatchingCount_recurrence {r : ℕ}
    (blocks : Fin (r + 1) → ℕ) (hfirst : 0 < blocks 0) :
    completeMultipartitePerfectMatchingCount blocks =
      ∑ j : Fin r, blocks j.succ * completeMultipartitePerfectMatchingCount
        (Function.update (Function.update blocks 0 (blocks 0 - 1)) j.succ
          (blocks j.succ - 1)) := by
  sorry

/-- The bipartite count is a factorial on equal block sizes and zero otherwise.
Andrews–Askey–Roy, *Special Functions*, Theorem 6.9.5
(synopsis AAR-6.8.1–6.9.9). -/
theorem completeMultipartitePerfectMatchingCount_two (m n : ℕ) :
    completeMultipartitePerfectMatchingCount ![m, n] = if m = n then m.factorial else 0 := by
  sorry

/-- The tripartite factorial formula. Andrews–Askey–Roy, *Special Functions*,
Theorem 6.9.6 (synopsis AAR-6.8.1–6.9.9). -/
theorem completeMultipartitePerfectMatchingCount_three (l m n : ℕ) :
    completeMultipartitePerfectMatchingCount ![l, m, n] =
      if Even (l + m + n) ∧ l ≤ m + n ∧ m ≤ l + n ∧ n ≤ l + m then
        l.factorial * m.factorial * n.factorial /
          (((l + m + n) / 2 - l).factorial * ((l + m + n) / 2 - m).factorial *
            ((l + m + n) / 2 - n).factorial)
      else 0 := by
  sorry

end SimpleGraph
