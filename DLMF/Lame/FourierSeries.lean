/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Lame.FourierSeries.CoefficientRecurrences
public import DLMF.Lame.FourierSeries.EigenfunctionSeries
public import DLMF.Lame.FourierSeries.ContinuedFractions
public import DLMF.Lame.FourierSeries.CoefficientRatios

/-!
# Lamé functions: Fourier series (DLMF §29.6)

This umbrella module collects the Fourier series of the four Lamé functions in
`φ = π/2 - am(x, k)` (29.2.5), `Ec^{2m}_ν = ½A₀ + ∑ A_{2p} cos 2pφ`,
`Ec^{2m+1}_ν = ∑ A_{2p+1} cos(2p+1)φ`, `Es^{2m+1}_ν = ∑ B_{2p+1} sin(2p+1)φ`,
`Es^{2m+2}_ν = ∑ B_{2p+2} sin(2p+2)φ`, and the same series multiplied by `dn(x, k)`
(coefficients `C`, `D`), with the three-term recurrences, normalizations, positivity conditions,
ratio limits and Parseval sums of DLMF 29.6.1–29.6.60.

The coefficients are defined by the Fourier integrals `Real.lameCosCoeff` and
`Real.lameSinCoeff` of `DLMF.Lame.Basic` (`(4/π)∫₀^{π/2} f cos(jφ) dφ` and
`(4/π)∫₀^{π/2} (f/dn) cos(jφ) dφ`, written as integrals over `x ∈ [0, K]`), so that the
expansions are theorems; the coefficient list is indexed from `0` (`A p = A_{2p}`, `A_{2p+1}`,
`B_{2p+1}` or `B_{2p+2}`). The recurrences use `LameRecurrence` (`A0`, `C0` for `Ec^{2m}`;
`A1`, `C1` for `Ec^{2m+1}`; `B1`, `D1` for `Es^{2m+1}`; `B2`, `D2` for `Es^{2m+2}`), with
`H = 2a - ν(ν+1)k²` (29.6.2, 29.6.17, 29.6.32, 29.6.47). For non-integer `ν` the coefficients
are the minimal solutions of these recurrences, which gives the continued-fraction equation
29.3.10.
-/
