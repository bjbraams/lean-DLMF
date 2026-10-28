/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Spheroidal.FerrersSeries.RecurrencesAndConvergence
public import DLMF.Spheroidal.FerrersSeries.RatiosAndSecondKind

/-!
# Expansions in series of Ferrers functions (DLMF §30.8)

Statement acquisition from NIST DLMF (version 1.2.8), checked 2026-10-26. Admitted statements
are not completed proofs; see `DLMF30Acquisition.md`.

* §30.8(i): the expansion 30.8.1 of `𝖯s^m_n` in Ferrers functions with the coefficients 30.8.2,
  the three-term recurrence 30.8.4 with the coefficients 30.8.3 (`A_{-R} = 0` proved), the
  normalization 30.8.5–30.8.6 and the asymptotic ratios 30.8.7, 30.8.8;
* §30.8(ii): the expansion 30.8.9 of `𝖰s^m_n` with the recessive coefficients `a'^m_{n,k}`
  (30.8.10, 30.8.11) and the extended coefficients `a^m_{n,k}`, `-N ≤ k < -R`.

Indices: `R = ⌊(n-m)/2⌋`, `N = ⌊(n+m)/2⌋`; sums over `k ≥ -R` are written over `j : ℕ` with
`k = j - R`. Numerical checks: the recurrence and normalization were used to compute `𝖯s` and
`𝖰s` (compared with SciPy and with 30.4.1); the series 30.8.9 reproduces the Wronskian 30.5.4
and the parity 30.5.2 to 25 digits, provided the extended coefficients are included in `A^m_n`;
the project's `ferrersQ` agrees with mpmath at the low degrees `-m ≤ ν < m` that occur in 30.8.9.
-/
