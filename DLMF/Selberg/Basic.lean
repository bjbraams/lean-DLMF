/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Selberg.Basic.Integrands
public import DLMF.Selberg.Basic.Parameters

/-!
# The Selberg and Aomoto integrals: definitions (AAR §§8.1–8.4)

This file collects the foundational definitions for Selberg's integral: the integrands, the
unit unitCube and Aomoto's integrals (`DLMF.Selberg.Basic.Integrands`), and the right-hand side of
Selberg's formula with its domain of convergence (`DLMF.Selberg.Basic.Parameters`). The
evaluation is proved in `DLMF.Selberg.IntegrationByParts`, `DLMF.Selberg.DimensionAndParameters`
and `DLMF.Selberg.ContinuationAndAomoto`.
-/
