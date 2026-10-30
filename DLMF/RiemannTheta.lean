/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.RiemannTheta.Characteristics
public import DLMF.RiemannTheta.Symmetry
public import DLMF.RiemannTheta.Modular
public import DLMF.RiemannTheta.Products
public import DLMF.RiemannTheta.MathlibCoverage

/-!
# Multidimensional theta functions (DLMF Chapter 21)

* `Basic`: the Siegel upper half-space of Riemann matrices, the Riemann theta function
  `θ(z|Ω)` (21.2.1), its scaled form (21.2.2), theta functions with characteristics
  (21.2.5–21.2.7), absolute and locally uniform convergence with continuity and analyticity in
  each variable (§21.2(i)), the examples 21.2.3–21.2.4 and the Riemann matrices of 21.4.2–21.4.3,
  and the genus-one reduction to the classical theta functions (21.2.8–21.2.12).
* `Symmetry`: parity, periodicity and quasi-periodicity (21.3.1–21.3.6).
* `Modular`: symplectic matrices and modular transformations (21.5.1–21.5.9), with the
  corrected forms of 21.5.4 (theta group) and 21.5.8 (square-root branch).
* `Products`: the Riemann identity and its `h = 4` example, and the addition formula
  (21.6.1–21.6.8).
* `MathlibCoverage`: genus-one and linear-algebra pointers to Mathlib.

The definitions follow DLMF: `θ(z|Ω) = ∑_{n ∈ ℤ^g} exp(2πi(½ n·Ω·n + n·z))`, with the genus
`g` represented by an arbitrary finite index type `ι`.
-/
