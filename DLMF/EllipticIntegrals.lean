/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.EllipticIntegrals.Addition
public import DLMF.EllipticIntegrals.Asymptotics
public import DLMF.EllipticIntegrals.Connection
public import DLMF.EllipticIntegrals.Derivatives
public import DLMF.EllipticIntegrals.Expansions
public import DLMF.EllipticIntegrals.Inequalities
public import DLMF.EllipticIntegrals.LegendreIdentities
public import DLMF.EllipticIntegrals.Legendre
public import DLMF.EllipticIntegrals.P19sR1Bounds
public import DLMF.EllipticIntegrals.P19sR1Connection
public import DLMF.EllipticIntegrals.P19sR1Legendre
public import DLMF.EllipticIntegrals.Quadratic
public import DLMF.EllipticIntegrals.Reduction
public import DLMF.EllipticIntegrals.Relations
public import DLMF.EllipticIntegrals.SpecialCases
public import DLMF.EllipticIntegrals.SymmetricAddition
public import DLMF.EllipticIntegrals.SymmetricAsymptotics
public import DLMF.EllipticIntegrals.SymmetricConnection
public import DLMF.EllipticIntegrals.SymmetricCoverage
public import DLMF.EllipticIntegrals.SymmetricDerivatives
public import DLMF.EllipticIntegrals.SymmetricInequalities
public import DLMF.EllipticIntegrals.SymmetricIntegrals
public import DLMF.EllipticIntegrals.SymmetricIntegralsOfIntegrals
public import DLMF.EllipticIntegrals.Symmetric
public import DLMF.EllipticIntegrals.SymmetricQuadratic
public import DLMF.EllipticIntegrals.SymmetricReduction
public import DLMF.EllipticIntegrals.SymmetricRelations
public import DLMF.EllipticIntegrals.SymmetricSeries
public import DLMF.EllipticIntegrals.SymmetricSpecialCases

/-!
# Elliptic integrals (DLMF Chapter 19)

Mathlib has no elliptic integrals. This area follows DLMF Chapter 19 for complex arguments:

* Legendre's integrals (§§19.1–19.14): `incEllIntFk`, `incEllIntEk`, `incEllIntDk`,
  `incEllIntPik`, the complete `compEllIntEk`, `compEllIntDk`, `compEllIntPik` (with the existing
  `DLMF.JacobiElliptic.compEllIntKk`, `compEllIntKpk`), the complementary `cCompEllIntKk`,
  `cCompEllIntEk` (19.2.9), and Bulirsch's `bulirschCel`, `bulirschEl1/2/3`, in
  `DLMF.EllipticIntegrals.Legendre`. Bridges go to the real `DLMF.Elliptic.Real.*` integrals and
  to the `lean-codes` Carlson library. Cauchy principal values are `limUnder` of excised
  integrals along the straight path.
* Symmetric integrals (§§19.15–19.29): Carlson's `R_F, R_G, R_J, R_C, R_D, R_K, R_E` and
  `R_{-a}(b; z)`, in `DLMF.EllipticIntegrals.Symmetric`, bridged to the `lean-codes` Carlson
  library.

The real integrals, AGM and Landen theory of the older `DLMF.Elliptic` area remain in place and
carry their own `@[dlmf]` tags.
-/
