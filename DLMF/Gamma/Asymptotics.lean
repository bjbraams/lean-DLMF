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
# Asymptotic expansions of the Gamma function (DLMF §5.11)

This umbrella collects Stirling's series for `ln Γ` and `ψ`, the scaled Gamma function and its
coefficients, the shifted Stirling expansion and the expansions of Gamma ratios. The Poincaré
expansions are stated along the positive real axis; Stirling's formula for `Γ(n+1)` is
`Gamma_nat_succ_isEquivalent_stirlingGamma` in `DLMF.Gamma.Stirling`. The remainder estimates
5.11.10–5.11.11 with `sec(ph z)` are not formalized, except the real-axis form of 5.11.3.
-/
