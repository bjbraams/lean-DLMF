/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Weighted first-order differential operators

`Function.mulDerivMul f` is the operator `z ↦ z (z f(z))'`, and
`Function.oneSubMulDerivMul f` is `z ↦ (1-z) ((1-z) f(z))'`. They are defined over any
nontrivially normed field. Identities involving their iterates require the appropriate
smoothness assumptions; the definitions use Mathlib's totalized derivative.
-/

@[expose] public noncomputable section

namespace Function

/-- The weighted differential operator `f ↦ z (z f)'`. -/
def mulDerivMul {𝕜 : Type*} [NontriviallyNormedField 𝕜] (f : 𝕜 → 𝕜) (z : 𝕜) : 𝕜 :=
  z * deriv (fun w => w * f w) z

/-- The weighted differential operator `f ↦ (1-z) ((1-z) f)'`. -/
def oneSubMulDerivMul {𝕜 : Type*} [NontriviallyNormedField 𝕜] (f : 𝕜 → 𝕜) (z : 𝕜) : 𝕜 :=
  (1 - z) * deriv (fun w => (1 - w) * f w) z

end Function
