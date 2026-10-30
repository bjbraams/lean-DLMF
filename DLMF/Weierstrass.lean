/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Weierstrass.EllipticFunctionsAndInvariants
public import DLMF.Weierstrass.DifferentialEquations
public import DLMF.Weierstrass.SpecialLattices
public import DLMF.Weierstrass.Relations
public import DLMF.Weierstrass.QuarterPeriods
public import DLMF.Weierstrass.Series
public import DLMF.Weierstrass.Addition
public import DLMF.Weierstrass.Integrals
public import DLMF.Weierstrass.Asymptotics
public import DLMF.Weierstrass.ModularFunctions
public import DLMF.Weierstrass.MathlibCoverage

/-!
# Weierstrass elliptic and modular functions (DLMF Chapter 23)

Mathlib has the Weierstrass `℘` function of a `PeriodPair` (full periods), its derivative, the
lattice sums `G n` and the invariants `g₂, g₃`, the differential equation 23.3.10, the Dedekind
eta function and the modular discriminant. This area adds the DLMF half-period parametrization
(`HalfPeriods`: `ω₁, ω₃`, `ω₂ = -ω₁ - ω₃`, `τ = ω₃/ω₁`, `q = e^{iπτ}`), Weierstrass `ζ` and `σ`,
the lattice roots `e_j` and constants `η_j`, functions of given invariants, and the elliptic
modular functions `λ` and `J`.

* `Basic`: §§23.2–23.3(i) (definitions, periodicity, quasi-periodicity, Legendre's relation,
  lattice roots and invariants, functions of given invariants).
* `DifferentialEquations`: §23.3(ii).
* `SpecialLattices`: §23.5 (real, rectangular, lemniscatic, rhombic, equianharmonic lattices).
* `Relations`: §23.6 (theta and Jacobian functions, integrals for rectangular lattices).
* `QuarterPeriods`: §23.7.
* `Series`: §§23.8–23.9 (trigonometric series and products, Laurent series).
* `Addition`: §23.10 (addition theorems, `n`-tuple formulas, homogeneity).
* `Integrals`: §§23.11 and 23.14.
* `Asymptotics`: §§23.12–23.13.
* `ModularFunctions`: §§23.15 and 23.17–23.19.
* `MathlibCoverage`: pointers to the upstream declarations.

Graphics (§§23.4, 23.16), applications (§§23.20–23.21) and computation (§§23.22–23.24) are
excluded; see `DLMF23Acquisition.md`.
-/
