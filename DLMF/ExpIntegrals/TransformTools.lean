/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.ExpIntegrals.TransformTools.LaplaceAndFourier
public import DLMF.ExpIntegrals.TransformTools.QuadraticMoments

/-!
# Tools for Laplace transforms and integrals of exponential and trigonometric integrals

This umbrella collects the supporting results (prefix `eiTr_`) for DLMF §§6.14–6.15 in
`DLMF.ExpIntegrals.ZerosIntegrals`: elementary Laplace transforms, parametric integral
representations of `E₁`, `Si`, `Ein - Cin` with Fubini swaps, the squared and product integrals of
`E₁`, `Ci`, `Si - π/2`, and the evaluation of the sums of §6.15 through Binet's formulas
(DLMF 5.9.10, 5.9.15).
-/
