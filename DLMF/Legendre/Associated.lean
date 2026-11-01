/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Legendre.Associated.QuadraticFerrers
public import DLMF.Legendre.Associated.ConjugationAndValues
public import DLMF.Legendre.Associated.Wronskians
public import DLMF.Legendre.Associated.BoundaryAndConnections

/-!
# Associated Legendre functions and Olver normalization

This umbrella module collects the associated Legendre functions `P^μ_ν`, `Q^μ_ν`, Olver's
normalized `𝑸^μ_ν` and the Ferrers functions in their quadratic hypergeometric forms, with
their differential equations, analyticity, conjugation symmetry, Wronskians and connection
formulas (DLMF §§14.2, 14.3, 14.9).
-/
