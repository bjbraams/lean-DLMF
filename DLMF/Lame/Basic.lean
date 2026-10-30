/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Lame.Basic.Equations
public import DLMF.Lame.Basic.SpectralData
public import DLMF.Lame.Basic.RecurrenceData

/-!
# Lamé functions: definitions (DLMF §§29.1–29.3, 29.6, 29.9, 29.11)

DLMF Chapter 29 studies Lamé's equation (29.2.1)
`w'' + (h - ν(ν+1) k² sn²(z, k)) w = 0`, `0 < k < 1`, `ν ≥ -1/2`,
its eigenvalues `a^m_ν(k²)`, `b^m_ν(k²)` and eigenfunctions `Ec^m_ν(z, k²)`, `Es^m_ν(z, k²)`.

## Design

* **Equations.** `IsLameSolutionOn h ν k w U` is 29.2.1 over `ℂ` on a set `U` with the
  project's complex `sn(z, k) = DLMF.JacobiElliptic.jacobiSnk z k` (modulus `k`); like
  `DLMF.Painleve.IsPIIOn` it records genuine differentiability of `w` and `w'`, so totalized
  derivatives cannot make a nonsolution satisfy the equation. The other forms of §29.2
  (algebraic 29.2.2, trigonometric 29.2.4, Weierstrass 29.2.9 and 29.2.10) and the Lamé wave
  equation 29.11.1 have their own predicates. `Real.IsLameSolution h ν k w` is 29.2.1 for real
  `x ∈ ℝ` with the real-variable `sn = DLMF.Elliptic.Real.jacobiSnm x (k²)` (parameter
  `m = k²`; it agrees with the complex `sn` for `0 < k < 1`, `jacobiSnk_ofReal`).
* **Eigenvalues.** Table 29.3.2 describes the four eigenvalue families as the four
  Sturm–Liouville problems on `[0, K]` with Neumann (`w' = 0`, "even") or Dirichlet (`w = 0`,
  "odd") conditions at `0` and at `K = K(k)`. `Real.lameEigenvalue ν k odd0 oddK j` is the
  `j`th element (from `0`) of the spectrum of the problem with boundary types `odd0`, `oddK`:
  the unique `h` in the spectrum with exactly `j` spectral points below it
  (`if h : ∃! … then … else 0`; **definition by choice**, the existence and the ordering of
  the spectrum are the admitted theorem `Real.lameEigenvalue_spec` in `DLMF.Lame.Eigenvalues`).
  Then `a^{2m} = (even, even, m)`, `a^{2m+1} = (odd, even, m)`, `b^{2m+1} = (even, odd, m)`,
  `b^{2m+2} = (odd, odd, m)` (`Real.lameAk`, `Real.lameBk`; the superscript of DLMF is the
  natural number argument, `b^0` is not used).
* **Eigenfunctions.** `Real.lameEigenfunction ν k odd0 oddK j` is the unique real eigenfunction
  for that eigenvalue normalized by 29.3.18, `∫₀^K dn(x, k) w(x)² dx = π/4`, with the sign rule
  of §29.3(v) (`w(K) > 0` for `Ec`, `w'(K) < 0` for `Es`); **definition by choice**, existence
  and uniqueness are the admitted theorem `Real.lameEigenfunction_spec`. `Real.lameEck` and
  `Real.lameEsk` are DLMF's `Ec^m_ν(x, k²)` and `Es^m_ν(x, k²)` for real `x`. Lamé functions are
  real-variable functions here: DLMF's eigenvalue problem, normalization, orthogonality,
  Fourier series in `φ = π/2 - am(x, k)` and integral equations are all on the real line.
  The Lamé polynomials (§29.12), which are meromorphic in `z`, are explicit complex functions in
  `DLMF.Lame.Polynomials.Basic`.
* **Parameters.** Every function takes the modulus `k` (DLMF writes `k²`); argument order is
  `ν` (subscript), `m` (superscript), `x`, `k`, as for `ferrersP ν μ x`.
* **Recurrences.** The coefficients `α_p, β_p, γ_p` of the eight three-term recurrences of
  29.3.11–29.3.17 and 29.6.11, 29.6.26, 29.6.41, 29.6.56 are `LameRecurrence.alpha/beta/gamma`;
  the finite continued fractions of 29.3.10 are `lameCFLeft`, `lameCFRight`; the Fourier
  coefficients of 29.6 are defined by the Fourier integrals in `Real.lameCosCoeff`,
  `Real.lameSinCoeff`.

Mathlib and TauCeti have no Lamé functions (checked 2026-10-26).
-/
