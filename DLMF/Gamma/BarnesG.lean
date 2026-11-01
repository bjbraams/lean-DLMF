/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Gamma.BarnesG.WeierstrassProduct
public import DLMF.Gamma.BarnesG.BinetAndAsymptotics

/-!
# Barnes G-function (DLMF §5.17)

This umbrella collects the Barnes G-function, defined by the Weierstrass product 5.17.3 for
`G(z+1)`, with its functional equation, integer values, the integral formula for `ln G(x + 1)`,
the Glaisher–Kinkelin constant and the asymptotic expansion of `ln G`.
-/
