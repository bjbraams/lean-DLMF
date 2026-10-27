/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Elementary.LogExpBasic
public import DLMF.Elementary.LogExpAnalysis
public import DLMF.Elementary.LogExpIntegrals
public import DLMF.Elementary.Generalized
public import DLMF.Elementary.LambertW
public import DLMF.Elementary.Trigonometric
public import DLMF.Elementary.Hyperbolic
public import DLMF.Elementary.Computation
public import DLMF.Elementary.BesselConnections
public import DLMF.Elementary.MathlibCoverage

/-!
# Elementary functions (DLMF Chapter 4)

Logarithms, exponentials and powers; trigonometric and inverse trigonometric
functions; hyperbolic and inverse hyperbolic functions; generalized logarithms,
Lambert W and Wright omega; and exact computational reductions.

`MathlibCoverage` records checked upstream pointers. The other modules acquire
missing definitions and results, including prose and exact algebraic tables.
Graphics, numerical data and application notes are excluded. Branch differences,
source corrections, coverage and remaining admissions are documented in
`DLMF4Acquisition.md`.
-/
