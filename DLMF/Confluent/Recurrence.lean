/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Confluent.Recurrence.Contiguous
public import DLMF.Confluent.Recurrence.Derivatives

/-!
# Recurrence relations and derivatives (DLMF §§13.3, 13.15)

Denominator parameters of `kummerM` stay off the nonpositive integers.
Tricomi and Whittaker identities use the principal branch on the slit plane.
The operator `(z d/dz z)` is `Function.mulDerivMul`, matching DLMF 13.3.29.
13.3.15 is already proved as `deriv_kummerM_regular` in
`OrthogonalPolynomials.Differential`; the pointwise form is restated here.
-/
