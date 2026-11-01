/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Spheroidal.Spectrum.EntireEigenfunctions
public import DLMF.Spheroidal.Spectrum.ParameterDependence

/-!
# The spectrum of the spheroidal factor equation (DLMF §30.3(i))

This umbrella collects the spectral theory of the equation of the entire factor `g` of
`(1 - z²)^{m/2} g(z)`: entire solutions from the Frobenius series
(`DLMF.Spheroidal.Spectrum.EntireEigenfunctions`) and the dependence on the parameter with the
structure of the spectrum (`DLMF.Spheroidal.Spectrum.ParameterDependence`). This gives the
existence of the eigenvalues `λ^m_n(γ²)` (`DLMF.Spheroidal.exists_spheroidalEigenvalue`).
-/
