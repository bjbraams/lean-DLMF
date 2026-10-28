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

DLMF's `Bₙ(x)` and `Eₙ(x)` on the real line are Mathlib's `bernoulliFun n` and the project's
`eulerFun n` (`DLMFMathlib.NumberTheory.EulerPolynomials`).

## Definitions

* `bernoulliRealZerosGE n`: the real zeros of `Bₙ` in `[1/2, ∞)`, in increasing order and
  counted with multiplicity (they are simple by §24.12(iv)); `bernoulliRealZero n j` is DLMF's
  `x_j^{(n)}` (1-based, `j = 1, 2, …`). Beyond the last zero the totalized value is `0`.
  `bernoulliRealZeroCount n` is DLMF's `R(n)`, the number of real zeros (with multiplicity).
* `eulerRealZerosGE n`, `eulerRealZero n j` (DLMF's `y_j^{(n)}`): the same for `Eₙ`.

## Conventions

* The limits "as `n → ∞` with `m` fixed" for even (odd) `n` are taken along `n = 2k`
  (`n = 2k + 1`), `k → ∞`. The zero `x_{2m}^{(n)}` exists for large `n`, so the totalized value
  does not matter in these limits.
* "No multiple zeros" (§24.12(iv)) is `Polynomial.Separable` over `ℚ`, i.e. no repeated roots in
  an algebraic closure (in particular in `ℂ`). The statement for `Bₙ` is proved for every
  `n ≥ 0` (`B₀ = 1` is a unit), which includes DLMF's `n = 1, 2, …`.
* §24.12(iii) (complex zeros, irreducibility) consists of bibliographic pointers only.
* The numerical tables of zeros referred to elsewhere in the chapter are out of scope.

## Status

The zero counts in `[0, 1]` (§24.12(i)) are proved by Rolle's theorem from the derivative and
shift relations together with the Fourier series of `B₂ₘ` (Mathlib); `R(n) = n` for `n ≤ 5` is
proved from the explicit polynomials. The limits 24.12.4, 24.12.5 and 24.12.8 are proved from the
uniform limits 24.11.5–24.11.6 by a zero-counting (Hurwitz-type) argument, and so is the
corrected 24.12.11. The bounds 24.12.2, 24.12.9, 24.12.10 and the equivalence 24.12.3 are
proved from the Fourier series of `B₂ₖ` and `E₂ₘ₋₁` with explicit tail bounds (sign changes
locate the zero; `n = 2, 4` for 24.12.2 and `n = 5` for 24.12.10, where `y₂` is the double zero
`(1 + √5)/2`, from the explicit polynomials). The count 24.12.6 and the separability statements
of §24.12(iv) remain admitted. 24.12.11 as printed is
false: for odd `n` the limit of `y_{2m}^{(n)}` is `2m - 1/2`, not `m - 1/2`; the corrected
statement `y_m^{(n)} → m - 1/2` is proved (with a proved counterexample to the printed form).

## References

* NIST DLMF §24.12; Brillhart (1969), Dilcher (1988), Delange (1987).
-/
