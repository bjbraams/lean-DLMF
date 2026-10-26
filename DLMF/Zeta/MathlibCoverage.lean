/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Core.Upstream
public import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import Mathlib.NumberTheory.LSeries.HardyZ
public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.LSeries.ZetaZeros

/-!
# DLMF §§25.1–25.10: results already in Mathlib

Checked `dlmf_upstream` pointers for the Riemann zeta function, in addition to those already in
`DLMF.Core.UpstreamElementary` (25.2.1, 25.2(i), 25.2.4, 25.2.11, 25.4.1, 25.4.3, 25.6.1–25.6.3),
which are not repeated. Mathlib's `riemannZeta` is totalized at the pole (`riemannZeta 1` is the
junk value `(γ - log 4π)/2`), which the comments below take into account.

The Riemann hypothesis (DLMF §25.10(i)) is an open conjecture; Mathlib's `RiemannHypothesis` is
the statement as a `Prop`, recorded here as the statement only (no theorem is acquired).
-/

/- §25.2(iv): the Euler product as an unconditional `HasProd`. -/
dlmf_upstream 25.2.E11 riemannZeta_eulerProduct_hasProd "exact: Re s > 1, as HasProd over primes"

/- §25.6: integer arguments. -/
dlmf_upstream 25.6.E4 riemannZeta_neg_two_mul_nat_add_one "exact: ζ(-2(n+1)) = 0 for n ≥ 0"
dlmf_upstream 25.6.E11 deriv_riemannZeta_zero "exact: ζ'(0) = -log(2π)/2"

/- §25.10(i): distribution of the zeros. -/
dlmf_upstream 25.10.i riemannZeta_ne_zero_of_one_le_re
  "partial: ζ(s) ≠ 0 for Re s ≥ 1 (Re s > 1 and the line Re s = 1, Hadamard–de la Vallée Poussin)"
dlmf_upstream 25.10.i riemannZeta_neg_two_mul_nat_add_one "partial: the trivial zeros ζ(-2n) = 0"
dlmf_upstream 25.10.i RiemannHypothesis
  "conjecture: the statement that all nontrivial zeros lie on Re s = 1/2, as a Prop; not a theorem"
dlmf_upstream 25.10.i hardyZ_eq_zero_iff
  "partial: Hardy's Z (= DLMF's Z, see DLMF.Zeta.riemannSiegelZ_eq_hardyZ) vanishes exactly at \
  the zeros of ζ(1/2 + it)"
dlmf_upstream 25.10.i abs_hardyZ "partial: |Z(t)| = |ζ(1/2 + it)|"
dlmf_upstream 25.10.i continuous_hardyZ
  "partial: Z is continuous, so sign changes of Z locate zeros on the critical line"
dlmf_upstream 25.10.E1 hardyZ
  "different convention: Z(t) = Λ(1/2+it)/|Γ_ℝ(1/2+it)|, real-valued by definition; equal to \
  DLMF's e^{iθ(t)} ζ(1/2+it) by DLMF.Zeta.riemannSiegelZ_eq_hardyZ"
