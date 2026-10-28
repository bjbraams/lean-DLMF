/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Spheroidal.P3lSpectrum.EntireEigenfunctions
public import DLMF.Spheroidal.P3lSpectrum.ParameterDependence

/-!
# The spectrum of the spheroidal factor equation (DLMF §30.3(i))

For `m ∈ ℕ` and real `γ²`, `λ`, consider the equation of the entire factor `g` of
`(1 - z²)^{m/2} g(z)` (DLMF §30.3(i)):

`(1 - z²) g'' - 2(m+1) z g' + (λ - m(m+1) + γ²(1 - z²)) g = 0`.

We prove that the set `p3lSpec m γ²` of real `λ` for which it has a nonzero entire solution is
infinite and meets every half-line `(-∞, x)` in a finite set (`p3lSpec_infinite`,
`p3lSpec_Iio_finite`). This gives the existence of the eigenvalues `λ^m_n(γ²)`
(`DLMF.Spheroidal.exists_spheroidalEigenvalue`).

## Method

* **Frobenius solution at `z = 1`** (exponent `0`): `Y(z) = ∑ f_k (z - 1)^k` with the
  recurrence `2(k+1)(k+m+1) f_{k+1} = (c - k(k+2m+1)) f_k - 2γ² f_{k-1} - γ² f_{k-2}`,
  `c = λ - m(m+1)`, convergent for `|z - 1| < 5/3` (majorants, uniformly for `|c| ≤ K`).
* **Entire solutions force `Y(0) Y'(0) = 0`**: the Wronskian `(1-z²)^{m+1}(g Y' - g' Y)` is
  constant on the disc and vanishes at `z = 1`; applied to `g(z)` and `g(-z)`.
* **Conversely**, if `Y(0) = 0` (`Y'(0) = 0`), `Y` and `∓Y(-z)` agree on the lens between the
  discs about `±1` and glue to a solution on `|z| ≤ 6/5`; its Taylor coefficients at `0` satisfy
  a three-term recurrence and decay geometrically, hence superexponentially
  (`p3l_superexp`), so the solution is entire.
* **Discreteness and lower bound**: `λ ↦ Y(0) Y'(0)` is entire in `λ`; for
  `λ < m(m+1) - |γ²|` it does not vanish (monotonicity of `(1-x²)^{m+1} y y'` on `[0, 1]`).
* **Infinitely many eigenvalues**: by Sturm comparison with `sin(ω s(x))`,
  `s' = (1-x²)^{-m-1}`, the real solution has at least `J` zeros in `(0, 1/2)` for large `λ`;
  the zero count in `[0, 1]` is locally constant in `λ` while `Y(0) ≠ 0`
  (`ODE.sturmDef_ncard_eq_of_isPreconnected`), so `Y(0) = 0` for arbitrarily large `λ`.

Uses the power-series helpers of `DLMF.Hypergeometric.Series` and the Sturm tools of
`DLMFMathlib/Analysis/ODE`. Proof round 3, agent `ls` (prefix `p3l_`).
-/
