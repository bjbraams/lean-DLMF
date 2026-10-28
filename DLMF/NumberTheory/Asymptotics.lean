/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.NumberTheory.Asymptotics.DivisorSums
public import DLMF.NumberTheory.Asymptotics.PrimeAndComplexSums

/-!
# Asymptotic formulas: partial sums (DLMF §27.11)

DLMF's `∑_{n≤x}` is the sum over `1 ≤ n ≤ ⌊x⌋` (`Finset.Icc 1 ⌊x⌋₊`) and `∑_{p≤x}` the sum over
the primes `p ≤ ⌊x⌋` (`Nat.primesLE ⌊x⌋₊`). The error terms `O(g(x))` are
`Asymptotics.IsBigO atTop`; DLMF's "for all `x ≥ 1`" (resp. `x ≥ 2`) uniform bounds imply these
and conversely they follow from them when both sides are bounded on compact intervals, which is
the case here. Constants that DLMF only asserts to exist (`A` in 27.11.8, `B` in 27.11.9, `C` in
27.11.12) are existentially quantified. `γ` is `Real.eulerMascheroniConstant`.

Dirichlet's theorem on primes in arithmetic progressions (§27.11 after 27.11.11) is Mathlib's
`Nat.infinite_setOfPred_prime_and_modEq` (`Nat.setOf_prime_and_eq_mod_infinite`).
-/
