/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Hypergeometric.Elementary.AlgebraicValues
public import DLMF.Hypergeometric.Elementary.CubicValues

/-!
# Elementary evaluations and special arguments (DLMF §15.4)

All statements in this file are proved; the cubic transformations and boundary limits used
for 15.4.31–15.4.34 are in `SpecialValueTools`.
Existing evaluations are in `Basic`, `DiffEq`, `EulerIntegral`, and `Identities`.
Powers use the principal complex logarithm. Trigonometric substitutions are stated
for real arguments, so their transformed arguments stay in the convergence disk.
Equations with removable quotients (E2, E5, E9, E10, E15, E16) are multiplied
through by their elementary denominators; thus they also hold at the removable points.
The unit-circle evaluations E33–E34 assume absolute convergence and exclude poles
of numerator Gamma factors; DLMF's broader continuation/limit interpretations are
not the totalized series definition in Mathlib.
-/
