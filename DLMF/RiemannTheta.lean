/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.RiemannTheta.Characteristics
public import DLMF.RiemannTheta.CharacteristicParity
public import DLMF.RiemannTheta.HigherOrderAddition
public import DLMF.RiemannTheta.Translations
public import DLMF.RiemannTheta.EllipticQuotients
public import DLMF.RiemannTheta.Uniqueness
public import DLMF.RiemannTheta.Symmetry
public import DLMF.RiemannTheta.Modular
public import DLMF.RiemannTheta.Products
public import DLMF.RiemannTheta.MathlibCoverage

/-!
# Multidimensional theta functions (DLMF Chapter 21)

This umbrella collects the Riemann theta functions of DLMF Chapter 21: the Siegel upper
half-space, the theta function `θ(z|Ω)` with its scaled form and characteristics, convergence
and analyticity (§21.2), symmetry and quasi-periodicity (§21.3), modular transformations
(§21.5) with corrected forms of 21.5.4 and 21.5.8, the Riemann identity and addition formula
(§21.6), and pointers to Mathlib. The genus `g` is represented by an arbitrary finite index
type `ι`. Book-based extensions include higher-order theta sections, the parity and
counts of half-characteristics, second-order addition, rational theta translations
and their Heisenberg commutation relation, and genus-one meromorphic theta quotients.
-/
