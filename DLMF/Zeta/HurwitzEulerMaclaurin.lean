/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.SeriesProperties
public import DLMF.Zeta.Basic.Hurwitz

/-!
# Euler–Maclaurin continuation of the Hurwitz zeta function

The definition of `DLMF.Zeta.hurwitzZetaComplex` by Euler–Maclaurin continuation, the
existence of the limit, its holomorphy and the bridge to Mathlib's `hurwitzZeta` are in the
foundational module `DLMF.Zeta.Basic.Hurwitz`. This module re-exports it, together with
`DLMF.Hypergeometric.SeriesProperties`, for `DLMF.IncompleteGamma.ZerosIntegrals`.
-/
