/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.EllipticIntegrals.Basic.Symmetric
public import DLMF.EllipticIntegrals.Basic.SymmetricProperties
public import DLMF.EllipticIntegrals.Basic.Complete
public import DLMF.EllipticIntegrals.Basic.Legendre

/-!
# Foundational definitions for elliptic integrals

This entry point exposes Legendre's integrals of complex amplitude and modulus, the
complementary complete integrals and Bulirsch's integrals (DLMF §19.2), and the principal
branches, admissible domains, Cauchy principal values, definitions and elementary symmetries of
the symmetric elliptic integrals (DLMF §§19.15–19.16). The comparison with Carlson's functions
and the theorems about these integrals are collected in the umbrella `DLMF.EllipticIntegrals`.
-/
