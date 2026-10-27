/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Airy.Basic
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
public import DLMF.Airy.Incomplete
public import DLMF.Airy.SquareTools

/-!
# Airy functions (DLMF Chapter 9; Beals–Wong §9.9)

Mathlib has no Airy functions. This area defines `Ai` and `Bi` as entire functions through
their Maclaurin series (`DLMF.Airy.Basic`), proves Airy's equation, the initial values, the
Wronskian, uniqueness of solutions from initial data, the rotation identities with cube roots
of unity and real-valuedness on `ℝ`; and relates them to Bessel functions of order `±1/3` on the
real line, with the leading large-`x` behaviour and positivity on `[0, ∞)` (`DLMF.Airy.Bessel`).

The remaining modules acquire DLMF §§9.2 and 9.4–9.14, including Scorer, generalized and
incomplete Airy functions. The initial acquisition admits all new statements; existing
proofs are preserved. Oscillatory integrals include convergence limits, continued Bessel
arguments retain logarithmic coordinates, and asymptotic expansions use finite remainders.
The equation-by-equation inventory and source-domain qualifications are in
`AiryAcquisition.md` at the project root.
-/
