/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Combinatorics.Stirling.DefinitionsAndSeries
public import DLMF.Combinatorics.Stirling.RecurrencesAndIdentities
public import DLMF.Combinatorics.Stirling.AsymptoticsAndCycles

/-!
# Stirling numbers (DLMF §26.8)

DLMF's Stirling numbers of the first kind `s(n, k)` are **signed**: `(-1)^{n-k}` times the
number of permutations of `{1, …, n}` with exactly `k` cycles (DLMF 26.8(i)). Mathlib's
`Nat.stirlingFirst n k` is the unsigned (cycle-counting) number, so the DLMF function is
`signedStirlingFirst n k = (-1)^{n-k} * Nat.stirlingFirst n k : ℤ` (defined here). DLMF's
`S(n, k)` (second kind) is Mathlib's `Nat.stirlingSecond n k` itself; no new definition is
made for it. Both are defined for all `n, k : ℕ` and vanish for `k > n`.

The key bridge is `coeff_descPochhammer`: the falling factorial `x(x-1)⋯(x-n+1)` (Mathlib's
`descPochhammer`) has the coefficients `s(n, k)`. DLMF writes it as the rising factorial
`(x-n+1)_n` (`ascPochhammer` evaluated at `x - n + 1`). The inverse expansion 26.8.10 is
derived from Mathlib's `Nat.pow_eq_sum_stirlingSecond_mul_descFactorial` by polynomial
identity (agreement at every natural number). The lean-codes module
`Pochhammer.PochhammerTransform` has the same expansions in the rising-factorial basis.

**Source corrections (implicit conditions).**
* 26.8.10 (`∑_{k=1}^n S(n,k)(x-k+1)_k = xⁿ`) fails for `n = 0` (empty sum `0 ≠ 1`); it is
  acquired for `1 ≤ n`, with the `k = 0` form valid for all `n` alongside.
* 26.8.29 (`∑_{k=1}^n (-1)^{n-k} s(n,k) = n!`) fails for `n = 0`; acquired for `1 ≤ n`.
* 26.8.31 as printed ("when `f` is analytic for all `x` and the series converges") is false:
  for `f(x) = sin(πx)` at `x = 0`, `k = 1` every `Δⁿf(0) = 0`, so the series converges to
  `0`, but `f'(0) = π`. It is acquired for polynomial `f` (where the series is finite), and
  the counterexample is recorded (`not_forall_stirling_deriv_eq_fwdDiff_series`).
-/
