/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Legendre.IntegralTools.Orthogonality
public import DLMF.Legendre.IntegralTools.FractionalAndLaplace

/-!
# Tools for Legendre integrals

This umbrella imports the helper results (prefix `legInt_`) behind `DLMF.Legendre.Integrals` and
`DLMF.Legendre.IntegralRepresentations`: the orthogonality moments and iterated primitives of
Ferrers and associated Legendre functions, and the fractional, Laplace-type and Heine integrals
of DLMF §14.12.
-/
