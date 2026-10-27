/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.AsymptoticApproximations.Basics.Defs
public import DLMF.AsymptoticApproximations.Basics.MathlibCoverage
public import DLMF.AsymptoticApproximations.Basics.OrderSymbols
public import DLMF.AsymptoticApproximations.Basics.Transcendental
public import DLMF.AsymptoticApproximations.Distributional.Defs
public import DLMF.AsymptoticApproximations.Distributional.FractionalIntegrals
public import DLMF.AsymptoticApproximations.Distributional.MathlibCoverage
public import DLMF.AsymptoticApproximations.Distributional.Stieltjes
public import DLMF.AsymptoticApproximations.Integrals.Coalescing
public import DLMF.AsymptoticApproximations.Integrals.Defs
public import DLMF.AsymptoticApproximations.Integrals.Laplace
public import DLMF.AsymptoticApproximations.Integrals.Parts
public import DLMF.AsymptoticApproximations.Integrals.StationaryPhase
public import DLMF.AsymptoticApproximations.Integrals.Watson
public import DLMF.AsymptoticApproximations.Mellin.BesselExample
public import DLMF.AsymptoticApproximations.Mellin.Defs
public import DLMF.AsymptoticApproximations.Mellin.SmallParameter
public import DLMF.AsymptoticApproximations.Mellin.Transforms
public import DLMF.AsymptoticApproximations.ODE.Defs
public import DLMF.AsymptoticApproximations.ODE.Difference
public import DLMF.AsymptoticApproximations.ODE.LiouvilleGreen
public import DLMF.AsymptoticApproximations.ODE.Parameter
public import DLMF.AsymptoticApproximations.ODE.Singularities
public import DLMF.AsymptoticApproximations.Remainders.Defs
public import DLMF.AsymptoticApproximations.Remainders.Stokes
public import DLMF.AsymptoticApproximations.Sums.Darboux
public import DLMF.AsymptoticApproximations.Sums.Defs
public import DLMF.AsymptoticApproximations.Sums.EulerMaclaurin
public import DLMF.AsymptoticApproximations.Sums.MathlibCoverage

/-! # Asymptotic approximations: DLMF Chapter 2

Namespace `DLMF.AsymptoticApproximations`. One subdirectory per group of sections, each with its
own `Defs` file: `Basics` (§§2.1–2.2), `Integrals` (§§2.3–2.4), `Mellin` (§2.5),
`Distributional` (§2.6), `ODE` (§§2.7–2.9), `Sums` (§2.10) and `Remainders` (§2.11).
Ledger: `DLMF2Acquisition.md`.
-/
