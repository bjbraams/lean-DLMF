/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Weierstrass.Basic.Periods
public import DLMF.Weierstrass.Basic.Functions
public import DLMF.Weierstrass.Basic.Invariants
public import DLMF.Weierstrass.Basic.LatticesAndSigma
public import DLMF.Weierstrass.Basic.Modular

/-!
# Weierstrass functions and modular functions: foundations (DLMF §§23.2–23.3(i), 23.15)

The DLMF half-period data of a lattice and its bridge to Mathlib's `PeriodPair`, the
definitions of the Weierstrass `ζ` and `σ` functions, the lattice roots, constants and
invariants, and the Weierstrass functions of given invariants; the lattice, convergence, parity,
zeros and poles of `ζ` and `σ` (DLMF §23.2); and the definitions of the elliptic modular
function `λ`, Klein's invariant `J`, the notions of modular function and form, the Dedekind sum
and the eta multiplier (DLMF §§23.15, 23.18).
-/
