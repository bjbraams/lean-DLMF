/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Spheroidal.FerrersSeries.RecurrencesAndConvergence
public import DLMF.Spheroidal.FerrersSeries.RatiosAndSecondKind

/-!
# Expansions of spheroidal functions in series of Ferrers functions (DLMF §30.8)

This umbrella collects the expansions of DLMF §30.8: the expansion 30.8.1 of `𝖯s^m_n` in
Ferrers functions with the coefficients 30.8.2, the recurrence 30.8.4, the normalization
30.8.5–30.8.6 and the ratio asymptotics 30.8.7–30.8.8 (§30.8(i)), and the expansion 30.8.9 of
`𝖰s^m_n` with the recessive and extended coefficients (§30.8(ii)).

Indices: `R = ⌊(n-m)/2⌋`, `N = ⌊(n+m)/2⌋`; sums over `k ≥ -R` are written over `j : ℕ` with
`k = j - R`. The series 30.8.9 reproduces the Wronskian 30.5.4 and the parity 30.5.2 provided
the extended coefficients `a^m_{n,k}`, `-N ≤ k < -R`, are included in `A^m_n`.
-/
