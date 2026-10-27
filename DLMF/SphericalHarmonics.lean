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

Mathlib has harmonic functions, the Laplacian, the planar Poisson kernel, and
`Matrix.specialUnitaryGroup`. Homogeneous harmonic polynomials, the addition theorem,
Funk–Hecke, and Jacobi polynomials as `SU(2)` matrix coefficients are absent.
-/
