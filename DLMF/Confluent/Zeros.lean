/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Confluent.Zeros.RealZeros
public import DLMF.Confluent.Zeros.ComplexZeros

/-!
# Zeros of confluent hypergeometric functions

Counts of real zeros and asymptotics of large complex zeros of Kummer's and Tricomi's functions
(DLMF §13.9). The Bessel-zero expansions 13.9.8 and 13.22.1 are not formalized; they need
indexed Bessel zeros.
-/
