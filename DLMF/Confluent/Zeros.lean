/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Confluent.Zeros.RealZeros
public import DLMF.Confluent.Zeros.ComplexZeros

/-!
# Zeros (DLMF §§13.9, 13.22)

`p(a,b)` and `n(a,b)` count positive zeros of `M(a,b,x)` and of
`M(a,b,x)` in the left half-plane after Kummer's transformation, respectively.
`T(a,b)` and `P(a,b)` count zeros of `U(a,b,x)` on `(0,∞)`. Bessel-zero
expansions 13.9.8 and 13.22.1 are deferred pending indexed Bessel zeros.
-/
