/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Elliptic.Basic.Amplitude

/-!
# Jacobi's Epsilon and Zeta functions: definitions (DLMF §22.16(ii)–(iii))

Jacobi's Epsilon function `ℰ(x, k)` and Jacobi's Zeta function `Z(x|k)` for real `x` and real
modulus `k` with `k² < 1`.

## Main definitions

* `Real.jacobiEpsilonk`: `ℰ(x, k) = ∫₀ˣ dn²(t, k) dt` (DLMF 22.16.17).
* `Real.jacobiZetaFunctionk`: `Z(x|k) = ℰ(x, k) - (E(k)/K(k)) x` (DLMF 22.16.32).

## Main results

* `Real.jacobiEpsilonk_zero`, `Real.jacobiZetaFunctionk_zero`: `ℰ(0, k) = Z(0|k) = 0`.

## Implementation notes

The integral 22.16.17, valid for all real `x`, is taken as the definition of `ℰ`; the other
representations of DLMF §22.16(ii) are in `DLMF.JacobiElliptic.Related`.
-/

@[expose] public section

open Real DLMF.Elliptic

noncomputable section

namespace DLMF.JacobiElliptic

/-- Jacobi's Epsilon function `ℰ(x, k) = ∫₀ˣ dn²(t, k) dt` for real `x` and real modulus `k`
with `k² < 1` (DLMF 22.16.17, valid for all real `x`; DLMF's 22.16.14 is the equivalent form for
`-K < x < K`). Miller's `JacobiEpsilon`. -/
@[dlmf 22.16.E17]
def Real.jacobiEpsilonk (x k : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, Real.jacobiDnm t (k ^ 2) ^ 2

/-- Jacobi's Zeta function `Z(x|k) = ℰ(x, k) - (E(k)/K(k)) x` for real `x` (DLMF 22.16.32);
Miller's `JacobiZeta`. -/
@[dlmf 22.16.E32]
def Real.jacobiZetaFunctionk (x k : ℝ) : ℝ :=
  Real.jacobiEpsilonk x k - Real.compEllIntEm (k ^ 2) / Real.compEllIntKm (k ^ 2) * x

/-- `ℰ(0, k) = 0`. -/
@[simp]
theorem Real.jacobiEpsilonk_zero (k : ℝ) : Real.jacobiEpsilonk 0 k = 0 := by
  simp [Real.jacobiEpsilonk]

/-- `Z(0|k) = 0`. -/
@[simp]
theorem Real.jacobiZetaFunctionk_zero (k : ℝ) : Real.jacobiZetaFunctionk 0 k = 0 := by
  simp [Real.jacobiZetaFunctionk]

end DLMF.JacobiElliptic
