/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.GeneralizedHypergeometric.Appell.DefinitionsAndSeries
public import DLMF.GeneralizedHypergeometric.Appell.EulerIntegrals

/-!
# Appell functions and Horn's double series (DLMF §§16.13–16.16)

Acquired 2026-10-24. The ordinary double series are totalized outside convergence and at
exceptional denominator parameters. Convergence, differentiation and integral representations
therefore state their exact domains. Euler integrals provide analytic branches beyond the
series domains. Transformation formulas are identities of germs at the origin, transported
along compatible analytic continuations; no divergent totalized series is silently identified
with a continued function. The infinity connection formula explicitly specifies continuation.

The existing `appF4` and Bailey product theorem are reused. One-variable continuation uses the
pinned TauCeti continuation API; the two-variable definition below is its direct domain extension.
-/
