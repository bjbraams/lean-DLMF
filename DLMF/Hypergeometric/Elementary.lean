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

This umbrella imports the elementary and algebraic values of `₂F₁`
(`DLMF.Hypergeometric.Elementary.AlgebraicValues`) and its values at cubic and sixth-root
arguments (`DLMF.Hypergeometric.Elementary.CubicValues`). The cubic transformations and boundary
limits used for 15.4.31–15.4.34 are in `DLMF.Hypergeometric.SpecialValueTools`; other
evaluations are in `DLMF.Hypergeometric.DiffEq`, `DLMF.Hypergeometric.EulerIntegral` and
`DLMF.Hypergeometric.Identities`.

Powers use the principal complex logarithm. Trigonometric substitutions are stated for real
arguments, so their transformed arguments stay in the convergence disk. Equations with removable
quotients (15.4.2, 15.4.5, 15.4.9, 15.4.10, 15.4.15, 15.4.16) are multiplied through by their
elementary denominators, so they also hold at the removable points. The unit-circle evaluations
15.4.33–15.4.34 assume absolute convergence and exclude poles of numerator Gamma factors; DLMF's
broader continuation and limit interpretations are not the totalized series of Mathlib.
-/
