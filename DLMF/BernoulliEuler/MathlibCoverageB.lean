/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Core.Upstream
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.NumberTheory.LegendreSymbol.ZModChar
public import Mathlib.NumberTheory.ZetaValues

/-!
# DLMF §§24.11–24.16: results and definitions already in Mathlib

Checked `dlmf_upstream` pointers for the second half of Chapter 24 (the pointers for 24.13.1
and 24.13.2 are in `DLMF.Core.UpstreamElementary` and are not repeated). Mathlib's
`bernoulliFun k x` is DLMF's `B_k(x)` on `ℝ`; its Stirling numbers of the first kind are
unsigned.
-/

/-! ### §24.12 Zeros -/

dlmf_upstream 24.12.i bernoulliFun_eval_half_eq_zero
  "partial: B_{2k+1}(1/2) = 0, one of the zeros 0, 1/2, 1 of B_{2n+1} in [0, 1]"
dlmf_upstream 24.12.i bernoulliFun_endpoints_eq_of_ne_one
  "partial: B_n(1) = B_n(0) for n ≠ 1, so 0 and 1 are zeros of B_{2n}(x) - B_{2n}"

/-! ### §24.15 Related sequences of numbers -/

dlmf_upstream 24.15.iii Nat.stirlingSecond "exact: the Stirling numbers S(n, m) of §26.8(i)"
dlmf_upstream 24.15.iii Nat.stirlingFirst
  "different convention: the unsigned |s(n, m)|; DLMF's s(n, m) = (-1)^{n-m} |s(n, m)|"
dlmf_upstream 24.15.iv Nat.fib "exact: the Fibonacci numbers u_n (u₀ = 0, u₁ = 1)"
dlmf_upstream 24.15.iv Nat.fib_add_two "exact: the Fibonacci recurrence u_{n+1} = u_n + u_{n-1}"

/-! ### §24.16(ii) Character analogs -/

dlmf_upstream 24.16.ii DirichletCharacter.IsPrimitive
  "exact: χ modulo f is primitive when its conductor is f"
dlmf_upstream 24.16.ii DirichletCharacter.conductor "exact: the conductor of χ"
dlmf_upstream 24.16.ii ZMod.χ₄
  "exact: the nontrivial character χ₄ modulo 4 (ℤ-valued; compose with ℤ → ℂ)"
