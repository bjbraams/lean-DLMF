/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Bessel.Basic.SecondKind
public import DLMF.Bessel.Modified
public import DLMF.Bessel.Theorems
public import DLMF.Confluent.BasicProperties

/-!
# Bessel functions of the second kind and Hankel functions (DLMF §§10.2–10.6, 10.25–10.29)

This module collects the second-kind Bessel functions with the theorem modules on which the
later Bessel files build.

## Implementation notes

The continuity in the order, the recurrences, derivatives and Wronskians of `Y_ν`, `K_ν` and the
Hankel functions are in `DLMF.Bessel.Basic.SecondKind`; the definitions are in
`DLMF.Bessel.Basic`.
-/
