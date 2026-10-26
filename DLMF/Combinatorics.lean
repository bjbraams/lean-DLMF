/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Combinatorics.Basic
public import DLMF.Combinatorics.Stirling
public import DLMF.Combinatorics.Bell
public import DLMF.Combinatorics.Binomial
public import DLMF.Combinatorics.Catalan
public import DLMF.Combinatorics.Multinomial
public import DLMF.Combinatorics.LatticePaths
public import DLMF.Combinatorics.MathlibCoverage
public import DLMF.Combinatorics.RestrictedPartitions
public import DLMF.Combinatorics.S26aStaircase
public import DLMF.Combinatorics.PartitionIdentities
public import DLMF.Combinatorics.Compositions
public import DLMF.Combinatorics.PlanePartitions
public import DLMF.Combinatorics.Permutations
public import DLMF.Combinatorics.MultisetPermutations
public import DLMF.Combinatorics.CountingTechniques
public import DLMF.Combinatorics.TwelvefoldWay
public import DLMF.Combinatorics.MathlibCoverageB

/-!
# Combinatorial analysis (DLMF Chapter 26)

Binomial and multinomial coefficients, Catalan, Delannoy, Motzkin, Narayana, Schröder, Bell and
Stirling numbers (part A, §§26.1–26.8), and integer partitions, compositions, plane partitions,
permutations, multiset permutations, the twelvefold way and counting techniques (part B,
§§26.9–26.18). The ledger is DLMF26Acquisition.md.
-/
