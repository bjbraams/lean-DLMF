/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.BernoulliEuler.Basic
public import DLMF.BernoulliEuler.GeneratingFunctions
public import DLMF.BernoulliEuler.Properties
public import DLMF.BernoulliEuler.Recurrences
public import DLMF.BernoulliEuler.Explicit
public import DLMF.BernoulliEuler.Integrals
public import DLMF.BernoulliEuler.Series
public import DLMF.BernoulliEuler.Inequalities
public import DLMF.BernoulliEuler.Arithmetic
public import DLMF.BernoulliEuler.MathlibCoverage
public import DLMF.BernoulliEuler.Asymptotics
public import DLMF.BernoulliEuler.Zeros
public import DLMF.BernoulliEuler.IntegralsSums
public import DLMF.BernoulliEuler.RelatedNumbers
public import DLMF.BernoulliEuler.Generalizations
public import DLMF.BernoulliEuler.MathlibCoverageB

/-!
# Bernoulli and Euler polynomials (DLMF Chapter 24)

DLMF's `B_n`, `B_n(x)` are Mathlib's `bernoulli` and `Polynomial.bernoulli`; `E_n`, `E_n(x)`
are `eulerNumber` and `Polynomial.euler` from DLMFMathlib. The modules from `Basic` through
`Arithmetic` cover §§24.1–24.10; those from `Asymptotics` through `Generalizations` cover
§§24.11–24.16.
-/
