/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.BernoulliEuler.Zeros.RealZeros
public import DLMF.BernoulliEuler.Zeros.ZeroLimits
public import DLMF.BernoulliEuler.Zeros.EulerZeros

/-!
# Zeros of Bernoulli and Euler polynomials (DLMF §24.12)

The real zeros of the Bernoulli and Euler polynomials: their enumeration, counts and bounds
(`Zeros.RealZeros`), limiting locations obtained from uniform convergence (`Zeros.ZeroLimits`),
and the Euler zeros and multiple-zero statements (`Zeros.EulerZeros`).

DLMF §24.12(iii) (complex zeros, irreducibility) consists of bibliographic pointers only, and
the numerical tables of zeros are out of scope.

## References

* NIST DLMF §24.12; Brillhart (1969), Dilcher (1988), Delange (1987).
-/
