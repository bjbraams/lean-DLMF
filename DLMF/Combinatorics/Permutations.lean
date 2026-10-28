/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Combinatorics.Permutations.CyclesAndExcedances
public import DLMF.Combinatorics.Permutations.EulerianNumbers
public import DLMF.Combinatorics.Permutations.RookPolynomials
public import DLMF.Combinatorics.Permutations.MenageAndFerrers

/-!
# Permutations: cycle, order and matrix notation (DLMF §§26.13–26.15)

`𝔖_n` is `Equiv.Perm (Fin n)`. Positions and values are `0, …, n-1` in Lean against DLMF's
`1, …, n`; all statistics below are invariant under this shift (the major index adds `1` to
each descent position, as DLMF counts positions from `1`).

* Cycle notation: Mathlib's `c[…]` (`Cycle.formPerm`) and `List.formPerm`; the number of cycles
  (fixed points included) is `numCycles σ = σ.partition.parts.card`. The Stirling cycle numbers
  `[n k]` are Mathlib's unsigned `Nat.stirlingFirst n k` (DLMF's `|s(n, k)|`, with the signed
  `signedStirlingFirst` of `DLMF.Combinatorics.Stirling`).
* Order notation: words `w : Fin n → ℕ` with `wordInversions`, `wordDescentSet`,
  `wordMajorIndex`; for permutations `inversionNumber`, `descentNumber`, `majorIndex`. These
  word statistics are reused for multiset permutations (§26.16).
* Eulerian numbers `⟨n k⟩` are `eulerianNumber n k`, the number of `σ ∈ 𝔖_n` with `k` descents.
* Matrix notation: `σ.permMatrix R` (Mathlib) has entry `1` at `(j, σ j)`. Rook numbers
  `r_j(B)` (`rookNumber`), the rook polynomial `R(x, B)` (`rookPolynomial`), hit numbers
  `N_k(B)` (`hitNumber`) and `N(x, B)` (`hitPolynomial`) are over `ℤ[X]`.

Corrections: (26.13.4), second form `d(n) = ⌊(n! + e - 2)/e⌋`, fails at `n = 0`
(`d(0) = 1`, the right side is `0`); it is acquired for `n ≥ 1`.

## References

* NIST DLMF §§26.13–26.15.
-/
