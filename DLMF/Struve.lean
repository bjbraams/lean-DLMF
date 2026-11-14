/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Struve.Representations
public import DLMF.Struve.Lommel
public import DLMF.Struve.AngerWeber
public import DLMF.Struve.Asymptotics
public import DLMF.Struve.Computation
public import DLMF.Struve.Coefficients
public import DLMF.Struve.SeriesAndEquations
public import DLMF.Struve.Poisson
public import DLMF.Struve.Properties
public import DLMF.Struve.AsymptoticTools
public import DLMF.Struve.TurningTools
public import DLMF.Struve.BarnesTools
public import DLMF.Struve.LargeOrderTools
public import DLMF.Struve.RelativeBounds

public import DLMF.Struve.Asymptotics.ScorerTransition

/-!
# Struve, Lommel and Anger–Weber functions (DLMF Chapter 11)

This umbrella collects the DLMF Chapter 11 development: the Struve functions `𝐇_ν`, `𝐋_ν`,
`𝐊_ν`, `𝐌_ν` with their series, equations, representations and properties, the Lommel
functions, the Anger and Weber functions, the asymptotic expansions, and the computational
claims of the chapter.
-/
