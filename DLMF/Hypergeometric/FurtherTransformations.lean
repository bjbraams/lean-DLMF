/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Hypergeometric.FurtherTransformations.Quadratic
public import DLMF.Hypergeometric.FurtherTransformations.Cubic

/-!
# Further transformations (DLMF §15.8)

All nonterminating series arguments are restricted to their convergence disks.
Regularized linear transformations retain singular denominator parameters.
Terminating transformations have no disk restriction, but denominator parameters
must still avoid undefined cancellations. E18 is already `gauss_quadratic` and its
inverse `kummer_quadratic`. E12 is `regularized_euler` with `c = a+b-m`.
E29 and E30 are specializations of E21 and of E13/E15, respectively.
Remaining two-term quadratic and logarithmic formulas are in `ConnectionFormulas`.
Formulas that require global continuation are not recorded here.
-/
