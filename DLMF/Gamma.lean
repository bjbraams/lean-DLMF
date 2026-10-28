/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Gamma.RatioBounds
public import DLMF.Gamma.Basic
public import DLMF.Gamma.Digamma
public import DLMF.Gamma.Dirichlet
public import DLMF.Gamma.GaussDigamma
public import DLMF.Gamma.IntegralRep
public import DLMF.Gamma.Kummer
public import DLMF.Gamma.Multiplication
public import DLMF.Gamma.Stirling
public import DLMF.Gamma.Pochhammer
public import DLMF.Gamma.SpecialValues
public import DLMF.Gamma.Inequalities
public import DLMF.Gamma.SeriesExpansions
public import DLMF.Gamma.Products
public import DLMF.Gamma.IntegralRepresentations
public import DLMF.Gamma.ComplexBinet
public import DLMF.Gamma.ContinuedFractions
public import DLMF.Gamma.Asymptotics
public import DLMF.Gamma.BetaFunction
public import DLMF.Gamma.Integrals
public import DLMF.Gamma.Polygamma
public import DLMF.Gamma.RationalSeries
public import DLMF.Gamma.PolygammaHurwitz
public import DLMF.Gamma.Multidimensional
public import DLMF.Gamma.BarnesG
public import DLMF.Gamma.QGamma
public import DLMF.Gamma.MathlibCoverage
public import DLMF.Gamma.VerticalBounds
public import DLMF.Gamma.MellinBarnes
public import DLMF.Gamma.RecipGammaDeriv
public import DLMF.Gamma.ShiftedLineBounds
public import DLMF.Gamma.Simplex.PochhammerIdentities

/-!
# The Gamma and Beta functions (AAR Chapter 1; DLMF Chapter 5)

Mathlib supplies Euler's integral, the recurrence, factorial values, reflection,
Legendre duplication, the Beta integral, Gauss's product, and the complex digamma
function. The modules below record AAR Chapter 1 identities and suitable statements
from DLMF §§5.2 and 5.4–5.18 that are absent from Mathlib.

Graphics §5.3, applications §§5.19–5.20, and computation §§5.21–5.24 are excluded.
Each statement taken from the DLMF records its equation number in a `@[dlmf]`
attribute. Many newly acquired statements are admitted and remain proof obligations.

`DLMF.Gamma.RecipGammaDeriv` defines the entire derivatives `(1/Γ)^{(n)}`. Statements in which
digamma occurs only through products with a reciprocal Gamma are given in that form, valid
for all parameters, because Mathlib's digamma takes the value `0` at its poles.
-/
