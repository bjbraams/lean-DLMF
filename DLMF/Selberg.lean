/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Selberg.Applications
public import DLMF.Selberg.ContinuationAndAomoto

/-!
# The Selberg integral (AAR Chapter 8)

This area proves Selberg's integral and Aomoto's extension on the full domain of convergence
(AAR §§8.1–8.4, DLMF 5.14.4), and collects applications: Siegel's inequality, a nearly poised
`₃F₂(1)` evaluation, the Hasse–Davenport relation and the finite-field Selberg formula
(AAR §§8.5–8.11). Mathlib's `SelbergSieve` is unrelated; the `n = 1` case is the Beta integral
`Complex.betaIntegral`.
-/
