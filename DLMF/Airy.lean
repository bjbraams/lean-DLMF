/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Airy.Properties
public import DLMF.Airy.Bessel
public import DLMF.Airy.Framework
public import DLMF.Airy.Equation
public import DLMF.Airy.IntegralRepresentations
public import DLMF.Airy.Relations
public import DLMF.Airy.Asymptotics
public import DLMF.Airy.ErrorBoundTools
public import DLMF.Airy.StieltjesForm
public import DLMF.Airy.ModulusTools
public import DLMF.Airy.ModulusPhase
public import DLMF.Airy.Zeros
public import DLMF.Airy.Scorer
public import DLMF.Airy.ScorerAsymptotics
public import DLMF.Airy.IntegralTools
public import DLMF.Airy.Integrals
public import DLMF.Airy.Products
public import DLMF.Airy.Generalized
public import DLMF.Airy.GeneralizedContours
public import DLMF.Airy.GeneralizedFinitePart
public import DLMF.Airy.Incomplete
public import DLMF.Airy.SquareTools

/-!
# Airy functions (DLMF Chapter 9; Beals–Wong §9.9)

Mathlib has no Airy functions. This area defines `Ai` and `Bi` as entire functions through
their Maclaurin series (`DLMF.Airy.Basic`) and develops DLMF §9.2 and §§9.4–9.14: Airy's
equation, Wronskians and connection formulas, the relation to Bessel functions of order `±1/3`,
integral representations, asymptotic expansions with error bounds, modulus and phase, zeros,
Scorer functions, integrals and products of Airy functions, and generalized and incomplete Airy
functions.

Oscillatory integrals are stated as convergence limits, continued Bessel arguments keep
logarithmic coordinates, and asymptotic expansions are stated with explicit finite remainders.
-/
