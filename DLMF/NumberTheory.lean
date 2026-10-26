/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.NumberTheory.Functions
public import DLMF.NumberTheory.T27bHecke
public import DLMF.NumberTheory.DirichletSeries
public import DLMF.NumberTheory.Inversion
public import DLMF.NumberTheory.DivisorSums
public import DLMF.NumberTheory.Characters
public import DLMF.NumberTheory.Asymptotics
public import DLMF.NumberTheory.Primes
public import DLMF.NumberTheory.Additive
public import DLMF.NumberTheory.Partitions
public import DLMF.NumberTheory.MathlibCoverage

/-!
# Functions of number theory (DLMF Chapter 27)

Multiplicative number theory (§§27.2–27.12: arithmetic functions, Dirichlet series, inversion,
divisor sums, Lambert series, characters, periodic functions, asymptotics, primes) and additive
number theory (§§27.13–27.14: sums of squares, Waring's problem, unrestricted partitions),
built on Mathlib's `ArithmeticFunction`, characters and L-series. The ledger is
DLMF27Acquisition.md.
-/
