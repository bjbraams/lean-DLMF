/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.CoalescingSaddles.DifferentialEquations.Cuspoid
public import DLMF.CoalescingSaddles.DifferentialEquations.HyperbolicUmbilic
public import DLMF.CoalescingSaddles.DifferentialEquations.EllipticUmbilic

/-!
# Differential equations for the canonical integrals

The differential equations of DLMF §36.10 for the canonical integrals: the cuspoid operator
equation, ordinary differential equations and derivative relations (36.10.1–36.10.10), and the
partial differential equations of the elliptic and hyperbolic umbilics (36.10.11–36.10.18).
They follow from differentiation under the integral sign and integration by parts along the
rotated contours on which the canonical integrals are defined.
-/
