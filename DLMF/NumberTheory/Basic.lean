/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.NumberTheory.Basic.Characters
public import DLMF.NumberTheory.Basic.Functions
public import DLMF.NumberTheory.Basic.GeneratingFunctions

/-!
# Functions of number theory: foundations (DLMF Chapter 27)

The foundational layer of DLMF Chapter 27. Most arithmetic functions of the chapter are
Mathlib's (`Nat.totient`, `ArithmeticFunction.sigma`, `moebius`, `liouville`, `vonMangoldt`,
`Nat.primeCounting`); the modules imported here define the others and DLMF's predicates.

* `DLMF.NumberTheory.Basic.Functions`: the functions of §27.2 with their defining formulas, and
  DLMF's multiplicative and completely multiplicative functions (27.3.1, 27.3.9).
* `DLMF.NumberTheory.Basic.Characters`: Dirichlet characters in DLMF's form (§27.8), periodic
  functions, Ramanujan sums and Gauss sums (§27.10), with bridges to Mathlib.
* `DLMF.NumberTheory.Basic.GeneratingFunctions`: Lambert series, `r_k(n)` and Jacobi's theta
  series, Euler's product, the discriminant and Ramanujan's `τ`.
-/
