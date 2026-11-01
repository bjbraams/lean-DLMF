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
public import DLMF.Painleve.Basic.Transformations
public import DLMF.Painleve.Basic.Coalescence

/-!
# Painlevé equations in the DLMF normalization: definitions and basic properties (DLMF Ch. 32)

The foundational entry point for Painlevé equations: the equations and solution predicates
in the DLMF normalization (`Basic.Equations`), Hamiltonians and Lax matrices
(`Basic.HamiltonianAndLax`), Painlevé II in the Beals–Wong normalization (`Basic.BealsWong`),
the definitions for special solutions, reductions and applications (`Basic.Solutions`), the
renormalizations, alternative and symmetric forms of §32.2(ii)–(v) (`Basic.Transformations`) and
the coalescence cascade of §32.2(vi) (`Basic.Coalescence`).
Beals–Wong's `PII(c)` is `u'' = 2u³ + xu - c` (`IsPIIOn`); DLMF's `PII` with parameter `α` is
the same equation with `c = -α` (`isPainleveIIOn_iff_isPIIOn` in `Basic.Transformations`).
-/
