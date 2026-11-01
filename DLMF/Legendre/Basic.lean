/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Legendre.Basic.Functions
public import DLMF.Legendre.Basic.Associated
public import DLMF.Legendre.Basic.Harmonics
public import DLMF.Legendre.Basic.Properties

/-!
# Definitions of Legendre and Ferrers functions

This entry point collects the foundational definitions of DLMF Chapter 14: the Legendre
functions `P_ν`, `Q_ν` and the Ferrers function `𝖯^μ_ν` in the hypergeometric normalization of
DLMF §14.3 (`DLMF.Legendre.Basic.Functions`), the associated functions `P^μ_ν`, `Q^μ_ν`, `𝑸^μ_ν`,
`𝖰^μ_ν` and the conical functions (`DLMF.Legendre.Basic.Associated`), and the spherical and
surface harmonics of §14.30 (`DLMF.Legendre.Basic.Harmonics`), together with the value
`P_ν(1) = 1`, the derivatives and Legendre's equations for `P_ν` and `𝖯^μ_ν`
(`DLMF.Legendre.Basic.Properties`).
-/
