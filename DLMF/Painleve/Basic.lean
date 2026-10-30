/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Painleve.Basic.Equations
public import DLMF.Painleve.Basic.HamiltonianAndLax
public import DLMF.Painleve.Basic.BealsWong
public import DLMF.Painleve.Basic.Solutions

/-!
# Painlevé equations in the DLMF normalization: definitions (DLMF Chapter 32)

This file holds the definitions of DLMF Chapter 32 (namespace `DLMF.Painleve`). The older
files of this area (`Basic.BealsWong`, `Backlund`, …) follow Beals–Wong, whose `PII(c)` is
`u'' = 2u³ + xu - c` (`IsPIIOn`); DLMF's `PII` with parameter `α` is the same equation with
`c = -α` (`isPainleveIIOn_iff_isPIIOn` in `DLMF.Painleve.Equations`).

* `IsODE2SolutionOn F w U` (32.2.7): `w'' = F(z, w, w')` on `U`, with genuine
  differentiability of `w` and of `w'` at every point of `U` (so totalized derivatives cannot
  make a nonsolution satisfy the equation). Statements use it on open sets.
* The right-hand sides `painleveIRhs` … `painleveVIRhs` of 32.2.1–32.2.6, as functions of the
  jet `(z, w, w')`, and the predicates `IsPainleveIOn` … `IsPainleveVIOn`. For `PIII`–`PVI` the
  predicate also requires that `U` avoids the points where DLMF divides (`z = 0`, `z = 1`,
  `w = 0`, `w = 1`, `w = z`), so the totalized divisions `x / 0 = 0` never enter.
* `IsPainleveIIIPrimeOn` (32.2.9, DLMF's `P'III`).
* The Hamiltonians of §32.6 and the Hamiltonian system `IsHamiltonianSystemOn` (32.6.1).
* The DLMF Bäcklund maps `painleveIITPlus`, `painleveIITMinus` of 32.7.2.
* The Lax matrices of 32.4.4–32.4.9.
-/
