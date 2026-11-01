/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Lame.Basic.Equations
public import DLMF.Lame.Basic.SpectralData
public import DLMF.Lame.Basic.RecurrenceData
public import DLMF.Lame.Basic.EquationForms

/-!
# Lamé functions: definitions (DLMF §§29.1–29.3, 29.6, 29.9, 29.11)

This entry point collects the definitions for DLMF Chapter 29: Lamé's equation (29.2.1)
`w'' + (h - ν(ν+1) k² sn²(z, k)) w = 0`, `0 < k < 1`, `ν ≥ -1/2`, and its other forms, the
eigenvalues `a^m_ν(k²)`, `b^m_ν(k²)` and eigenfunctions `Ec^m_ν(x, k²)`, `Es^m_ν(x, k²)`, the
three-term recurrences and Fourier coefficients, and the asymptotic coefficients.

Every function takes the modulus `k` (DLMF writes `k²`); argument order is `ν` (subscript),
`m` (superscript), `x`, `k`, as for `ferrersP ν μ x`. Mathlib and TauCeti have no Lamé
functions. `DLMF.Lame.Basic.EquationForms` identifies the algebraic form with Heun's equation
(§29.2(ii)).
-/
