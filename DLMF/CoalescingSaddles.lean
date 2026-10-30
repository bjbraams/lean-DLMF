/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.CoalescingSaddles.Basic
public import DLMF.CoalescingSaddles.CanonicalIntegrals
public import DLMF.CoalescingSaddles.BifurcationSets
public import DLMF.CoalescingSaddles.StokesSets
public import DLMF.CoalescingSaddles.Scaling
public import DLMF.CoalescingSaddles.Basic.AuxiliaryData
public import DLMF.CoalescingSaddles.DifferentialEquations
public import DLMF.CoalescingSaddles.Zeros
public import DLMF.CoalescingSaddles.Series
public import DLMF.CoalescingSaddles.IntegralIdentities
public import DLMF.CoalescingSaddles.Asymptotics

/-! # Integrals with coalescing saddles: DLMF Chapter 36

Potentials of the cuspoid and umbilic catastrophes, the canonical integrals `Ψ_K`, `Ψ^(E)`,
`Ψ^(H)` as absolutely convergent integrals along rotated contours, bifurcation and Stokes sets,
scaling relations, zeros, series, integral identities, differential equations and leading-order
asymptotics. Ledger: `DLMF36Acquisition.md`.
-/
