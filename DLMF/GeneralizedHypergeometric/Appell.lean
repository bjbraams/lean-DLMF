/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.GeneralizedHypergeometric.Appell.SeriesAndDifferentialEquations
public import DLMF.GeneralizedHypergeometric.Appell.EulerIntegrals
public import DLMF.GeneralizedHypergeometric.Appell.TriangleDirichlet
public import DLMF.GeneralizedHypergeometric.Appell.GermTransformations
public import DLMF.GeneralizedHypergeometric.Appell.HornDifferentialEquations

/-!
# Appell functions and Horn's double series (DLMF §§16.13–16.16)

This umbrella imports the Appell series `F₁`–`F₄` and Horn's `G₂`, `G₃`: their convergence and
differential equations, Euler integral representations, reductions and transformations.

The ordinary double series are totalized outside convergence and at exceptional denominator
parameters, so convergence, differentiation and integral representations state their exact
domains. Euler integrals provide analytic branches beyond the series domains. Transformation
formulas are identities of germs at the origin, transported along compatible analytic
continuations; no divergent totalized series is identified with a continued function. The
connection formula at infinity specifies its continuation explicitly. Two-variable continuation
extends the TauCeti one-variable continuation API. `appellF4` and Bailey's product formula come
from `DLMF.Hypergeometric.AppellF4`.
-/
