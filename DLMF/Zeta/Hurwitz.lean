/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Zeta.Hurwitz.SeriesAndContinuation
public import DLMF.Zeta.Hurwitz.ValuesAndDerivatives

/-!
# The Hurwitz zeta function: definition, Euler–Maclaurin forms, special values, derivatives
(DLMF §25.11(i)–(vi))

## Two Hurwitz zeta functions

* Mathlib's `HurwitzZeta.hurwitzZeta (a : UnitAddCircle) s` is the meromorphic continuation in `s`
  of `∑ (n + a)^{-s}` **for real `0 ≤ a ≤ 1`**; its parameter lives in `ℝ/ℤ`, so it is periodic in
  `a` and agrees with DLMF's `ζ(s, a)` only for `0 < a ≤ 1` (and `hurwitzZeta 0 = ζ(s, 1)`).
* DLMF's `ζ(s, a)` (25.11.1) is defined for complex `a ≠ 0, -1, -2, …` with principal powers. The
  project's definition is `DLMF.Confluent.hurwitzZetaComplex s a`
  (`DLMF/IncompleteGamma/ZerosIntegrals.lean`, made for DLMF 8.15.2), the limit as `N → ∞` of the
  Euler–Maclaurin form `∑_{n<N} (a+n)^{-s} + (a+N)^{1-s}/(s-1) + (a+N)^{-s}/2 + ∑_{k<M} …`
  with `M` large enough for `Re s`. It is reused here, not redefined. Its bridge to Mathlib for
  `0 < a ≤ 1` is `DLMF.Zeta.r25b_hurwitzZetaComplex_mathlib` (a proved form of the admitted
  `DLMF.Confluent.hurwitzZetaComplex_mathlib`).

Convention used below: a DLMF formula whose parameter range is contained in `0 < a ≤ 1` is stated
with Mathlib's `hurwitzZeta` (this is DLMF's function there); a formula for complex `a` or for
unbounded real `a > 0` is stated with `hurwitzZetaComplex`.

The existence of the defining limit (`tendsto_hurwitzZetaComplex`, the content of the continuation
statement in §25.11(i)) is proved in `DLMF.Zeta.R25bHurwitzContinuation` by the one-interval
Euler–Maclaurin formula; the recurrences 25.11.3 and 25.11.4 follow from it.
-/
