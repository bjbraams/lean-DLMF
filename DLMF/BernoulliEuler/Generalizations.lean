/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.BernoulliEuler.Generalizations.HigherOrder
public import DLMF.BernoulliEuler.Generalizations.DegenerateAndCharacter

/-!
# Generalizations of Bernoulli and Euler polynomials (DLMF §24.16)

## Definitions (genuine, by finite formulas)

* `norlundPolynomial n : ℚ[X]`: the Nörlund polynomial `B_n^{(x)}` of 24.16.9 as a polynomial in
  the order `x`. If `g(t) = t/(eᵗ - 1) - 1` (Mathlib's `bernoulliPowerSeries`, minus `1`), then
  `(1 + g)^x = ∑ⱼ (x choose j) gʲ` and only `j ≤ n` contribute to the coefficient of `tⁿ`; so
  `B_n^{(x)} = n! ∑_{j ≤ n} [tⁿ] gʲ · x(x-1)⋯(x-j+1)/j!` (`descPochhammer`). This is the
  formal-power-series meaning of `(t/(eᵗ-1))^x`, the branch equal to `1` at `t = 0`.
* `bernoulliNumberOrder ℓ n = B_n^{(ℓ)}` (24.16.3) and `bernoulliOrder ℓ n : ℚ[X]`, the
  polynomial `B_n^{(ℓ)}(x) = ∑ₖ (n choose k) B_k^{(ℓ)} x^{n-k}` (the coefficient form of
  24.16.1, the factor `e^{xt}` contributing `x^{n-k}/(n-k)!`).
* `eulerNumberOrder ℓ n = E_n^{(ℓ)}` and `eulerOrder ℓ n` for 24.16.2, in the same way from
  `2/(eᵗ + 1) = ∑ Eₙ(0) tⁿ/n!`.
* `bernoulliSecondKind n = bₙ = ∫₀¹ (x choose n) dx` (24.16.5), written through the coefficients
  of `descPochhammer`: `bₙ = (1/n!) ∑ₖ [xᵏ] x(x-1)⋯(x-n+1) / (k+1)`.
* `degenerateBernoulli n : ℚ[X]`, the degenerate Bernoulli number `βₙ(λ)` (24.16.7) as a
  polynomial in `λ`: `((1 + λt)^{1/λ} - 1)/t = ∑ₖ (1-λ)(1-2λ)⋯(1-kλ) tᵏ/(k+1)!` has constant
  term `1`, and `βₙ(λ)/n!` is the `n`-th coefficient of its inverse (`PowerSeries.invOfUnit`).
* `bernoulliChar χ n = B_{n,χ}` (24.16.10) for a Dirichlet character `χ` modulo `f`, defined by
  the classical closed form `B_{n,χ} = f^{n-1} ∑_{a=1}^{f} χ(a) Bₙ(a/f)`; the generating function
  24.16.10 is a theorem. DLMF requires `χ` primitive (with `f` its conductor); the definition and
  the generating function make sense for every `χ` modulo `f ≥ 1`. `bernoulliCharPoly` is
  24.16.11.

## Generating functions and branches

DLMF's generating functions are stated as `HasSum` in `ℂ` for `t ≠ 0` (at `t = 0` the Lean
quotients are totalized). For the Nörlund polynomials of complex order (24.16.9) DLMF's power
`(t/(eᵗ-1))^x` is the branch analytic in `|t| < 2π` and equal to `1` at `0`; the principal power
`cpow` agrees with it only while `t/(eᵗ-1)` has not crossed the negative axis. Numerically the
principal argument stays below `π` for `|t| < 4.8`; we state 24.16.9 for complex `x` and
`0 < ‖t‖ < π`, and for real `x` and real `0 < |t| < 2π` (where `t/(eᵗ-1) > 0`). The degenerate
Bernoulli generating function 24.16.7 ("for sufficiently small `|t|`") is stated for `λ ≠ 0`
eventually in the punctured neighbourhood of `0`, with the principal power `(1 + λt)^{1/λ}`.

## Status

The generating functions 24.16.1, 24.16.2 and 24.16.10 are proved by summing the Cauchy
products of the absolutely convergent series of `t/(eᵗ-1)`, `2/(eᵗ+1)` and `e^{xt}`;
`natDegree_norlundPolynomial` is proved. The formal identity `t β' = β - tβ - β²` for
`β = t/(eᵗ-1)` gives the Nörlund recurrence
`a B_{n+1}^{(a+1)}(x) = (a-n-1) B_{n+1}^{(a)}(x) + (n+1)(x-a) B_n^{(a)}(x)`, hence
`B_n^{(n+1)}(x) = (x-1)⋯(x-n)`; with `∫₀¹ B_n^{(a+1)} = B_n^{(a)}` this proves 24.16.6, and with
the differential equation of `(ln(1+t)/t)^ℓ` it proves 24.16.4. 24.16.5 is proved by integrating
the binomial series `(1+t)^x = ∑ (x choose n) tⁿ` over `0 ≤ x ≤ 1`. 24.16.7 is proved for
`|t| < 1/(4(1+|λ|))` from the binomial series of `(1 + λt)^{1/λ}`, a geometric bound on the
coefficients of the formal inverse and the Cauchy product. The generating function 24.16.9 is
proved from a holomorphic logarithm `L` of `t/(eᵗ-1)` on `|t| < 2π` (a primitive of the
logarithmic derivative): the Taylor coefficients of `e^{xL}` are polynomials in `x` that agree
with `B_n^{(ℓ)}` at `x = ℓ ∈ ℕ`. The identity 24.16.8 is proved for real `0 < λ < 1/4` by writing
`(1+λt)^{1/λ} = eᵘ`, `u = ln(1+λt)/λ`, expanding `t/(eᵘ-1)` with 24.2.1, 24.16.5 and the
Stirling generating function 26.8.8 (`DLMF.Combinatorics.Stirling`), rearranging the absolutely
convergent double series and comparing coefficients with 24.16.7; agreement for infinitely many
`λ` gives the identity in `ℚ[λ]`. The file has no admissions.

## References

* NIST DLMF §24.16; Nörlund (1924), Milne-Thomson (1933), Carlitz (1979), Berndt (1975a).
-/
