/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Selberg.Applications
public import DLMF.Selberg.Basic

/-!
# The Selberg integral (AAR Chapter 8)

Mathlib's `SelbergSieve` is unrelated. The `n = 1` case of Selberg is the Beta integral
`Complex.betaIntegral`. The remaining identities of Chapter 8 are recorded below.
-/
