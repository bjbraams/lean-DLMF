/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Elliptic.Basic.Integrals
public import DLMF.Elliptic.Basic.Amplitude
public import DLMF.Elliptic.Basic.Theta
public import DLMF.Elliptic.Basic.ThetaPeriodicity
public import DLMF.Elliptic.Basic.Jacobi

/-!
# Elliptic functions: foundational definitions

Real Legendre elliptic integrals, Jacobi's amplitude and the real elliptic functions `sn`, `cn`,
`dn` with their basic properties and the inverse `arcsn`, and the Jacobi theta functions in DLMF
normalization with their series, periodicity and parity.
-/
