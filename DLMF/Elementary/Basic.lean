/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Elementary.Basic.LogExp
public import DLMF.Elementary.Basic.Trigonometric
public import DLMF.Elementary.Basic.InverseTrigonometric
public import DLMF.Elementary.Basic.Gudermannian
public import DLMF.Elementary.Basic.Hyperbolic
public import DLMF.Elementary.Basic.InverseHyperbolic
public import DLMF.Elementary.Basic.LambertW

/-!
# Elementary functions: foundations

The central definitions of DLMF Chapter 4 with their basic properties: the general and closed
logarithms and powers (§4.2), the reciprocal trigonometric functions (§4.14), the principal
inverse trigonometric functions (§4.23), the Gudermannian (§4.23(viii)), and the reciprocal and
principal inverse hyperbolic functions (§§4.28, 4.37).

## Implementation notes

The Lambert W function is defined in `DLMF.Elementary.Basic.LambertW`, from the branch family
constructed in `DLMF.Elementary.Basic.LambertWConstruction`; its expansion coefficients and
asymptotics are in the theorem layer (`DLMF.Elementary.LambertW`).
-/
