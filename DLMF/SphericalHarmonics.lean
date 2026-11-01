/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.SphericalHarmonics.Basic
public import DLMF.SphericalHarmonics.AdditionTools
public import DLMF.SphericalHarmonics.ZonalTools
public import DLMF.SphericalHarmonics.BesselAddition
public import DLMF.SphericalHarmonics.Theorems

/-!
# Spherical harmonics (AAR Chapter 9)

This area develops homogeneous harmonic polynomials and their orthogonality on the sphere, the
spherical addition theorem, the Funk–Hecke formula, Gegenbauer's addition theorems, the Poisson
kernel of the ball and `SU(2)` (AAR Chapter 9). Mathlib has harmonic functions, the Laplacian,
the planar Poisson kernel and `Matrix.specialUnitaryGroup`, but not these results.
-/
