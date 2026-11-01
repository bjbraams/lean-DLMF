/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.ErrorFunctions.BoundsAsymptotics.ContinuedFractions
public import DLMF.ErrorFunctions.BoundsAsymptotics.GaussianRemainders
public import DLMF.ErrorFunctions.BoundsAsymptotics.FresnelRemainders

/-!
# Inequalities, continued fractions and asymptotic remainders (DLMF §§7.8–7.9, 7.12)

This umbrella collects the bounds for the Mills ratio, Dawson's integral and the error function
(§7.8), the continued fractions for `erfc` and the Faddeeva function (§7.9), and the asymptotic
expansions of `erfc` and of the Fresnel auxiliary functions with their remainder integrals and
bounds (§7.12).
-/
