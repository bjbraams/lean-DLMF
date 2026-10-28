/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Gamma.Asymptotics.Stirling
public import DLMF.Gamma.Asymptotics.ShiftedStirling
public import DLMF.Gamma.Asymptotics.GammaRatios

/-!
# Asymptotic expansions (DLMF §5.11)

Stirling's formula for `Γ(n+1)` is already `Gamma_nat_succ_isEquivalent_stirlingGamma`
in `Stirling.lean`. Poincaré expansions below are stated along the positive real
axis. Remainder estimates 5.11.10–5.11.11 with `sec(ph z)` are deferred except
for the real-axis form of 5.11.3.
-/
