/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Core.Upstream
public import Mathlib.Combinatorics.Derangements.Finite
public import Mathlib.Combinatorics.Enumerative.InclusionExclusion
public import Mathlib.Combinatorics.Enumerative.Partition.Glaisher
public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.Data.Sym.Card
public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.NumberTheory.Real.GoldenRatio
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# DLMF §§26.9–26.18 results already in Mathlib

Checked `dlmf_upstream` pointers (part B of the Chapter 26 acquisition) to Mathlib declarations
that formalize DLMF statements of §§26.9–26.18, instead of duplicate local theorems. Part A's
pointers (§§26.1–26.8) are kept by ACQ26A.
-/

/- §26.10 -/
dlmf_upstream 26.10.E12 Nat.Partition.card_odds_eq_card_distincts
  "exact: Euler's identity #(odds n) = #(distincts n), i.e. p(O,n) = p(D,n)"
dlmf_upstream 26.10.E2 Nat.Partition.hasProd_powerSeriesMk_card_countRestricted
  "partial: formal power series; for m = 2 (countRestricted n 2 = distincts n) the generating \
    function of p(D,n) is the product of (1 + X^i)"
dlmf_upstream 26.10.E5 Nat.Partition.hasProd_powerSeriesMk_card_restricted
  "partial: formal power series version of the generating function of p(∈S,n)"

/- §26.11 -/
dlmf_upstream 26.11.E5 Nat.fib_zero "exact: F_0 = 0"
dlmf_upstream 26.11.E5 Nat.fib_one "exact: F_1 = 1"
dlmf_upstream 26.11.E5 Nat.fib_add_two "exact: F_{n+2} = F_n + F_{n+1}"
dlmf_upstream 26.11.E7 Real.coe_fib_eq
  "exact: Binet's formula F_n = (φ^n - ψ^n)/√5 with φ = (1+√5)/2, ψ = (1-√5)/2"

/- §26.13 -/
dlmf_upstream 26.13.E4 card_derangements_eq_numDerangements
  "exact: d(n) = numDerangements n counts the fixed-point-free permutations"
dlmf_upstream 26.13.E4 numDerangements_sum
  "partial: d(n) = ∑_k (-1)^k (k+1)^{(n-k)} (rising factorial), equivalent to n! ∑ (-1)^j/j!"
dlmf_upstream 26.13 Equiv.Perm.sign_prod_list_swap
  "exact: the sign of a product of l transpositions is (-1)^l (parity of a permutation)"
dlmf_upstream 26.13 Equiv.Perm.swap_induction_on
  "partial: every permutation is a product of transpositions"
dlmf_upstream 26.13 List.formPerm_cons_cons
  "partial: (x, y, …) = (x, y) (y, …), the recursion behind (26.13.5)"

/- §26.15 -/
dlmf_upstream 26.15 Matrix.det_permutation
  "exact: det of the permutation matrix is sign σ"

/- §26.17, Table 26.17.1 (labeled balls/boxes, and the standard models of the unlabeled cases) -/
dlmf_upstream 26.17.T1 Nat.card_fun "exact: k^n maps from n labeled balls to k labeled boxes"
dlmf_upstream 26.17.T1 Fintype.card_embedding_eq
  "exact: k(k-1)⋯(k-n+1) = (k-n+1)_n injective maps"
dlmf_upstream 26.17.T1 Sym.card_sym_eq_multichoose
  "exact for the model Sym (Fin k) n of n unlabeled balls in k labeled boxes: \
    multichoose k n = C(k+n-1, n)"
dlmf_upstream 26.17.T1 Finset.card_powersetCard
  "exact for the model of n unlabeled balls in k labeled boxes, at most one per box: C(k, n)"

/- §26.18 -/
dlmf_upstream 26.18.E1 Finset.inclusion_exclusion_card_inf_compl
  "exact: |⋂ (S i)ᶜ| = ∑_{t ⊆ s} (-1)^{|t|} |⋂_{i ∈ t} S i| in a finite type; the t = ∅ term is |S|"
dlmf_upstream 26.18.E1 Finset.inclusion_exclusion_card_biUnion
  "exact: inclusion-exclusion for the cardinality of a union"
