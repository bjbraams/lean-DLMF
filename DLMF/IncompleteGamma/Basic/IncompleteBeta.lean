/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Basic.PrincipalBranch

/-!
# The continued incomplete Beta function (DLMF §8.17)

This file defines the incomplete Beta function `B_z(a, b)` and its normalized form
`I_z(a, b)` for complex arguments, through the principal-branch regularized Gauss function
(DLMF 8.17.8). The real functions are `Real.incompleteBeta` and `Real.regularizedIncompleteBeta` in
`DLMF.Statistical.Basic.IncompleteBeta`.

## Main definitions

* `DLMF.Statistical.incompleteBeta`, `DLMF.Statistical.regularizedIncompleteBeta`: the continued
  incomplete Beta function and its normalized form.

## Implementation notes

At parameter poles `incompleteBeta` keeps its totalized values; `regularizedIncompleteBeta`
preserves the removable specialization `a = 0`. The agreement with the real definitions (DLMF
8.17.1–8.17.2) is in `DLMF.IncompleteGamma.Beta`.
-/

@[expose] public noncomputable section
open Complex
namespace DLMF.Statistical

/-- Continued incomplete Beta; at parameter poles the formula keeps its totalized values. -/
def incompleteBeta (a b z : ℂ) : ℂ :=
  if z=1 then Gamma a*Gamma b/Gamma (a+b) else
    Gamma a*z^a*DLMF.Hypergeometric.regularizedGaussHypergeometric a (1-b) (a+1) z

/-- Continued normalized incomplete Beta, preserving the removable a=0 specialization. -/
def regularizedIncompleteBeta (a b z : ℂ) : ℂ :=
  if z=1 then 1 else
    Gamma (a+b)/Gamma b*z^a*DLMF.Hypergeometric.regularizedGaussHypergeometric a (1-b) (a+1) z

end DLMF.Statistical
