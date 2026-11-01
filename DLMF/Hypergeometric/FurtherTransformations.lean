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

This umbrella imports the linear, terminating and quadratic transformations
(`DLMF.Hypergeometric.FurtherTransformations.Quadratic`) and further quadratic and cubic
transformations (`DLMF.Hypergeometric.FurtherTransformations.Cubic`).

All nonterminating series arguments are restricted to their convergence disks. Regularized
linear transformations retain singular denominator parameters. Terminating transformations have
no disk restriction, but denominator parameters must still avoid undefined cancellations.
15.8.18 is `gauss_quadratic` with its inverse `kummer_quadratic`; 15.8.12 is `regularized_euler`
with `c = a+b-m`; 15.8.29 and 15.8.30 are specializations of 15.8.21 and of 15.8.13/15.8.15. The
remaining two-term quadratic and logarithmic formulas are in
`DLMF.Hypergeometric.ConnectionFormulas`. Formulas that require global continuation are not
included.
-/
