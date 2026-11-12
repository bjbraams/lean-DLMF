/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Legendre.Integrals.FerrersGreen
public import DLMF.Legendre.Integrals.FerrersDiagonal
public import DLMF.Legendre.Integrals.FerrersTriple
public import DLMF.Legendre.Integrals.ExteriorGreen

/-!
# Definite integrals, orthogonality and primitive formulas

This umbrella imports the definite integrals of Legendre functions (DLMF §14.17): orthogonality
and Green-type integrals of Ferrers functions on `(-1, 1)`, diagonal integrals, and integrals of
associated Legendre functions on `(1, ∞)`, and the Ferrers triple integral (14.17.17).
-/
