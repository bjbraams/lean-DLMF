/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Lame.FourierSeries.CoefficientRecurrences
public import DLMF.Lame.FourierSeries.EigenfunctionSeries

/-!
# Lamé functions: Fourier series (DLMF §29.6)

DLMF §29.6 expands the four Lamé functions in Fourier series in `φ = π/2 - am(x, k)`
(29.2.5): `Ec^{2m}_ν = ½A₀ + ∑ A_{2p} cos 2pφ`, `Ec^{2m+1}_ν = ∑ A_{2p+1} cos(2p+1)φ`,
`Es^{2m+1}_ν = ∑ B_{2p+1} sin(2p+1)φ`, `Es^{2m+2}_ν = ∑ B_{2p+2} sin(2p+2)φ`, and in the same
series multiplied by `dn(x, k)` (coefficients `C`, `D`). The coefficients are defined here by
the Fourier integrals `Real.lameCosCoeff` and `Real.lameSinCoeff` of `DLMF.Lame.Basic`
(`(4/π)∫₀^{π/2} f cos(jφ) dφ` and `(4/π)∫₀^{π/2} (f/dn) cos(jφ) dφ`, written as integrals over
`x ∈ [0, K]`), so that the expansions 29.6.1, 29.6.8, … are theorems; the coefficient list is
indexed from `0` (`A p = A_{2p}`, `A_{2p+1}`, `B_{2p+1}` or `B_{2p+2}`).

The recurrences use `LameRecurrence` (`A0`, `C0` for `Ec^{2m}`; `A1`, `C1` for `Ec^{2m+1}`;
`B1`, `D1` for `Es^{2m+1}`; `B2`, `D2` for `Es^{2m+2}`), with `H = 2a - ν(ν+1)k²` (29.6.2,
29.6.17, 29.6.32, 29.6.47). The positivity conditions 29.6.6, 29.6.13, 29.6.21 and 29.6.28
(values at `x = K`) are proved from the expansions and `Ec(K) > 0`. The three-term
recurrences (29.6.3–29.6.4 and their analogues) are proved from Lamé's equation for the
coefficients defined as Fourier integrals: Green's identity against the test functions
`cos(jφ(x))`, `sin(jφ(x))` (unweighted) and `dn(x) cos(jφ(x))`, `dn(x) sin(jφ(x))` (weighted),
whose image under the Lamé operator is a combination of three such functions (`p1l_int_unw`,
`p1l_int_w`). The expansions themselves follow from the convergence of the Fourier series of
periodic `C²` functions (`DLMF.Lame.P2lFourier`); the normalizations and the Parseval sums by
termwise integration against `E`, `E dn` and `E dn²` (with `dn² = 1 - k²/2 - (k²/2) cos 2φ`);
the positivity conditions for `B`, `D` by termwise differentiation of the sine series at
`φ = 0` and `Es'(K) < 0`. The ratio limits and the terminating case are admitted.

The prose of §29.6(i) (unique recessive solution of the recurrence for `ν ≠ 2n`; for
`ν = 2n`, `m ≤ n`, the coefficients `A_{2p}` vanish for `p > n`) is acquired as
`Real.lameEck_even_fourierA_eq_zero` (the terminating case).
-/
