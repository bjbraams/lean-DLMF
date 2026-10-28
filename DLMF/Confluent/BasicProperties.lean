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
# Kummer `M` and Tricomi `U`: remaining basic properties (DLMF §13.2)

Olver's regularized function `𝐌(a,b,z)` is Mathlib's `regularizedHGFun {a} {b}`.
The series `kummerM` is entire in `z` at regular denominator parameters; `kummerU`
uses the connection formula 13.2.42 and parameter limits at integer `b`.
The Kummer transformation includes integer parameters by parameter continuity.
The integer-denominator logarithmic expansion and its small-argument consequences follow
from termwise differentiation of the regularized series. Complex powers use the principal branch
on the slit plane. Numerically satisfactory pairs (13.2.24–13.2.26) are recorded as Wronskian
identities on the indicated argument sectors.

The connection formula 13.2.41 is proved for every `b`, in regularized form, as
`regularizedHGFun_eq_kummerU_connection`, from 13.2.42, Kummer's transformation 13.2.39 and the
reflection formula, then by continuity in `b`. The Wronskians 13.2.24, 13.2.25, 13.2.35, 13.2.37
and 13.2.38 that follow from it are in `DLMF.Confluent.ConnectionWronskians`.
-/
