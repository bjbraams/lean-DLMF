/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Confluent.BasicProperties.Continuity
public import DLMF.Confluent.BasicProperties.IntegerParametersAndLimits
public import DLMF.Confluent.BasicProperties.Wronskians

/-!
# Kummer `M` and Tricomi `U`: basic properties

Continuity of `U` in its parameters, its values and behaviour at integer parameters and near
the origin, and Wronskians of Kummer's and Tricomi's functions (DLMF §13.2).

Olver's regularized function `𝐌(a,b,z)` is Mathlib's `regularizedHGFun {a} {b}`; complex
powers use the principal branch on the slit plane. The connection formula 13.2.41 and the
Wronskians that follow from it are in `DLMF.Confluent.ConnectionWronskians`.
-/
