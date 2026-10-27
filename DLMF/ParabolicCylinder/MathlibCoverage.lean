/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Core.Upstream
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# DLMF Chapter 12 results already in Mathlib 4.35.0-rc2

The `dlmf_upstream` commands below are checked pointers to Mathlib declarations,
deliberately not duplicate local theorems.
-/

/- DLMF 12.14.22 defines `c_{2r} + i d_{2r} = Γ(2r + 1/2 + ia)/Γ(1/2 + ia)`. The project's
`DLMF.Confluent.pcfWCoeff a r` is the Pochhammer symbol `(1/2 + ia)_{2r}`; Mathlib's
gamma-ratio identity identifies the two, since `Re(1/2 + ia) > 0` for real `a`. -/
dlmf_upstream 12.14.E22 Complex.Gamma_add_nat_div_Gamma_eq
  "partial: the Gamma quotient equals the Pochhammer symbol (z)_n, used with z = 1/2 + ia, n = 2r"
