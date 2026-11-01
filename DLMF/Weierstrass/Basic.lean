/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Weierstrass.Basic.Periods
public import DLMF.Weierstrass.Basic.Functions
public import DLMF.Weierstrass.Basic.Invariants

/-!
# Weierstrass lattices, `℘`, `ζ` and `σ`: foundations (DLMF §§23.2–23.3(i))

The DLMF half-period data of a lattice and its bridge to Mathlib's `PeriodPair`, the
definitions of the Weierstrass `ζ` and `σ` functions, the lattice roots, constants and
invariants, and the Weierstrass functions of given invariants.
-/
