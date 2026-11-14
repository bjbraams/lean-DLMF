/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.RiemannTheta.Basic.Definitions
public import DLMF.RiemannTheta.Basic.Convergence
public import DLMF.RiemannTheta.Basic.Characteristics
public import DLMF.RiemannTheta.Basic.Analytic
public import DLMF.RiemannTheta.Basic.Periodicity
public import DLMF.RiemannTheta.Basic.Sections
public import DLMF.RiemannTheta.Basic.HigherOrder
public import DLMF.RiemannTheta.Basic.AlternativeNormalization

/-!
# Foundational Riemann theta functions

This file collects the foundational definitions of the Riemann theta functions
(`DLMF.RiemannTheta.Basic.Definitions`): Riemann matrices and the Siegel upper half-space, the
theta series `θ(z|Ω)`, its scaled form and the theta functions with characteristics; the
convergence and analyticity of the theta series (`DLMF.RiemannTheta.Basic.Convergence`); and the
characteristics and the genus-one reduction (`DLMF.RiemannTheta.Basic.Characteristics`).
The further foundational modules provide joint entire analyticity, symmetry and
quasi-periodicity, spaces of theta sections, Mumford's higher-order theta functions,
and the negative-real-part normalization. The scaled functions and the examples are
in `DLMF.RiemannTheta.Scaled` and `DLMF.RiemannTheta.Characteristics`.
-/
