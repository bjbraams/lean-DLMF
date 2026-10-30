/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Basic
public import DLMF.Elementary
public import DLMF.EllipticIntegrals
public import DLMF.GeneralizedHypergeometric
public import DLMF.JacobiElliptic
public import DLMF.ParabolicCylinder
public import DLMF.QHypergeometric
public import DLMF.RiemannTheta
public import DLMF.Struve
public import DLMF.Theta
public import DLMF.Weierstrass

public import DLMF.ErrorFunctions
public import DLMF.ExpIntegrals
public import DLMF.IncompleteGamma

public import DLMF.Airy
public import DLMF.AlgebraicAnalytic
public import DLMF.AsymptoticApproximations
public import DLMF.Bailey
public import DLMF.BernoulliEuler
public import DLMF.Bessel
public import DLMF.CoalescingSaddles
public import DLMF.Combinatorics
public import DLMF.Confluent
public import DLMF.Constants
public import DLMF.Core.UpstreamElementary
public import DLMF.Core.ZeroCounting
public import DLMF.Coulomb
public import DLMF.Elliptic
public import DLMF.Gamma
public import DLMF.Heun
public import DLMF.Hypergeometric
public import DLMF.Lame
public import DLMF.Legendre
public import DLMF.Mathieu
public import DLMF.MatrixArgument
public import DLMF.NumberTheory
public import DLMF.OrthogonalPolynomials
public import DLMF.Painleve
public import DLMF.Partitions
public import DLMF.Polylog
public import DLMF.QSeries
public import DLMF.Selberg
public import DLMF.SphericalHarmonics
public import DLMF.Spheroidal
public import DLMF.Statistical
public import DLMF.WaveEquation
public import DLMF.WignerSymbols
public import DLMF.Zeta

/-!
# Special functions following the NIST Digital Library of Mathematical Functions

This is the complete library entry point, importing the foundational layer and all area
umbrella modules. `DLMF.Basic` provides the smaller view of definitions and elementary
support, without dependencies on DLMF theorem files. Each area umbrella describes its
mathematical scope and upstream coverage; `DEFINITIONS.md` and `DEFINITIONS2.md` catalogue
the DLMF definitions and their Lean counterparts.
-/
