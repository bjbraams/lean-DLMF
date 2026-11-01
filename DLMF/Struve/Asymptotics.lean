/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Struve.Asymptotics.Watson
public import DLMF.Struve.Asymptotics.IntegratedKernels
public import DLMF.Struve.Asymptotics.IntegratedExpansions
public import DLMF.Struve.Asymptotics.LargeOrder
public import DLMF.Struve.Asymptotics.BinomialAndAnger
public import DLMF.Struve.Asymptotics.AngerWeberExpansions
public import DLMF.Struve.Asymptotics.TurningPointEstimates
public import DLMF.Struve.Asymptotics.InnerExpansions
public import DLMF.Struve.Asymptotics.ScaledExpansions

/-!
# Asymptotic expansions of Struve and Anger–Weber functions

This umbrella collects the asymptotic expansions of DLMF §11.6 and §11.11: the large-argument
expansions of `𝐊_ν` and `𝐌_ν` by Watson's lemma, the expansions of the integrated Struve
functions, the large-order expansions, the expansions of the Anger–Weber functions for fixed
and large order, and the turning-point estimates for the scaled expansions.
-/
