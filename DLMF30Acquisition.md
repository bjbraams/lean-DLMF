# DLMF Chapter 30 acquisition: Spheroidal Wave Functions

> Source paths and current layout notes were refreshed on 2026-10-30; generated per-entry
> statuses follow the compiled ledger refresh. Dated acquisition and proof counts
> describe their original batches.

This acquisition covers the definitions, numbered formulas and analytical assertions in prose
of [DLMF Chapter 30](https://dlmf.nist.gov/30), §§30.1–30.12, version 1.2.8, checked on
2026-10-26 (agent ACQ30). The graphics §30.7 and §30.11(ii), the applications §§30.13–30.15 and
the computation sections §§30.16–30.18 are excluded; the pure mathematics of the applications is
listed below. The Lean code is in `DLMF/Spheroidal/` (namespace `DLMF.Spheroidal`, helper prefix
`s30_`).

**Current layout (2026-10-30).**
`DLMF.Spheroidal.Basic` imports only the foundational leaves
`Basic.EquationAndSpectralData` and `Basic.Ferrers`. The former contains equations,
eigenvalues, `𝖯s`, `𝑃s` and coefficient data; the latter contains `a^m_{n,k}`, `A^{±m}_n`,
`𝖰s`, `𝑄s`, `S^{m(j)}_n`, `K^m_n` and Flammer’s functions. It uses the canonical
`DLMF.Legendre.Basic` definitions of the Ferrers functions. Existence and API theorems
formerly beside those definitions are in `FerrersProperties`, outside the foundation.
The subsequent developments are
[Equation](DLMF/Spheroidal/Equation.lean) (§§30.2, 30.3(i), 30.12),
[Eigenvalues](DLMF/Spheroidal/Eigenvalues.lean) (§§30.3, 30.9),
[Angular](DLMF/Spheroidal/Angular.lean) (§§30.1, 30.4–30.6),
[FerrersSeries](DLMF/Spheroidal/FerrersSeries.lean) (§30.8) and
[Radial](DLMF/Spheroidal/Radial.lean) (§30.11).
These theorem files import the required Legendre, Bessel and spheroidal theorem APIs
explicitly. Neither Mathlib nor TauCeti has spheroidal functions, so there is no
`MathlibCoverage` module.

**Status after proof round 1 (2026-10-26).** Direct admissions in DLMF/Spheroidal fell from 56 to 41. Proved: the transformations 30.2.2 and 30.2.4, the γ = 0 spectrum, parity, recurrence and orthogonality of 𝖯s (30.4), the recurrence 30.8.4 and 30.11.1. Many results are proved only from the flagged existence theorems; see REVIEW.md, "Proof round 1 for Chapters 28–31 (2026-10-26)".

**Status after proof round 2 (2026-10-26).** Direct admissions in DLMF/Spheroidal fell from 41 to 35. Proved: the Ferrers expansion 30.8.1, the recurrence 30.8.4, the normalization 30.8.5, the ratio estimates 30.8.7 and 30.8.8 (the latter corrected by γ² ≠ 0 after a proved counterexample at γ² = 0; the errata report (reports/DLMFErrata.tex) (b)) and 30.5.3. Most remain proved from the admitted spheroidal eigenvalue existence (singular Sturm–Liouville theory). See REVIEW.md, "Proof round 2 for Chapters 28–31 (2026-10-26)".

**Counts.** §§30.1–30.12 (without the graphics) have 67 numbered equations (30.1: 2, 30.2: 4,
30.3: 12, 30.4: 9, 30.5: 4, 30.6: 5, 30.8: 11, 30.9: 6, 30.11: 12, 30.12: 2; §30.7 and §30.10
have none). In scope: all 67. Covered: all 67. In addition 9 prose IDs carry tags (30.2.i,
30.2.iii, 30.3.i, 30.3.ii, 30.4.i, 30.4.ii, 30.4.iv, 30.8.ii, 30.9.ii). 76 DLMF IDs are tagged on
135 declarations: 50 definitions, 9 proved theorems, 20 theorems proved from admissions and 56
direct admissions. Two further definitions are untagged (`spheroidalPsFactor`,
`spheroidalCutPlane`), as are the proved helper lemmas `spheroidalEigenvalue_spec`,
`spheroidalPsFactor_spec`, `spheroidalQs_spec`, `spheroidalQsC_spec`,
`spheroidalCoeffPrime_spec` (from the existence theorems), `spheroidalPs_zero` and
`hasDerivAt_spheroidalPs_zero`. Excluded numbered equations: 38 (application: 30.13: 16,
30.14: 9, 30.15: 13) and 9 (computation: 30.16); §30.7 (21 figures), §30.11(ii) (4 figures)
graphics; §30.17 tables (numerical); §30.18 software.

Module admissions (`grep -cE 'by sorry|:= sorry|^\s*(·\s*)?sorry\s*$|exact sorry'`):

- [Basic](DLMF/Spheroidal/Basic.lean): 0 admissions. The flagged existence theorems for `λ^m_n` and `𝖯s`.
- [FerrersProperties](DLMF/Spheroidal/FerrersProperties.lean): 3 admissions. The flagged existence theorems for `a'`, `𝖰s`, `𝑄s`.
- [Equation](DLMF/Spheroidal/Equation.lean): 2 admissions.
- [Eigenvalues](DLMF/Spheroidal/Eigenvalues.lean): 11 admissions.
- [Angular](DLMF/Spheroidal/Angular.lean): 8 admissions.
- [FerrersSeries](DLMF/Spheroidal/FerrersSeries.lean): 0 admissions.
- [Radial](DLMF/Spheroidal/Radial.lean): 8 admissions.

## Domains, conventions and design notes

- `γ²` is a real parameter `γ2 : ℝ` (DLMF §30.1); `m ≤ n` naturals. Argument order: degree
  before order, as for the project's `ferrersP ν μ x`, then DLMF's arguments: `λ^m_n(γ²)` is
  `spheroidalEigenvalue n m γ2`, `𝖯s^m_n(x, γ²)` is `spheroidalPs n m x γ2`, `S^{m(j)}_n(z, γ)` is
  `spheroidalRadial j n m z γ`. The radial functions take complex `z`, `γ`; the coefficients are
  evaluated at `(γ^2).re` and the theorems assume `(γ^2).im = 0`.
- The equation 30.2.1 is a predicate with genuine differentiability in divergence form:
  `(1-z²) w'` has derivative `-(λ + γ²(1-z²) - μ²/(1-z²)) w` (complex, `IsSpheroidalSolutionOn`
  on a set `U`; real on `(-1, 1)` for real-valued `f`, `IsSpheroidalSolutionReal`).
- **Eigenvalues (definition by choice, flagged).** Following DLMF §30.3(i), `𝖯s^m_n` has the form
  `(1-x²)^{m/2} g(x)` with `g` entire; `w = (1-z²)^{m/2} g` solves 30.2.1 (`μ = m`) iff
  `(1-z²)g'' - 2(m+1)zg' + (λ - m(m+1) + γ²(1-z²))g = 0` (`IsSpheroidalFactor`; its power-series
  recurrence is 30.4.5 with 30.3.6). `spheroidalSpectrum m γ2` is the set of real `λ` with a
  nonzero entire solution, and `λ^m_n(γ²)` is the element of the spectrum with exactly `n - m`
  smaller elements (encard), junk `0` otherwise. Existence is the admitted
  `exists_spheroidalEigenvalue` (Sturm–Liouville theory); the ordering 30.3.1 is proved from it;
  the zero count `n - m` of §30.4(ii) and the value `n(n+1)` at `γ = 0` (30.3.3) are admitted
  theorems. This duplicates in spirit the Mathieu area's `nthLeast` (ACQ28A, written
  concurrently); the two could share a helper later.
- **`𝖯s` (definition by choice, flagged).** `spheroidalPsFactor n m γ2` is the entire `g` with the
  eigenvalue `λ^m_n(γ²)`, real on `ℝ`, normalized by 30.4.1 and with the sign of `g(0)` (`n - m`
  even) or `g'(0)` (`n - m` odd) of §30.4(i); existence and uniqueness are admitted
  (`existsUnique_isSpheroidalPsFactor`, simplicity of the eigenvalues). Then
  `𝖯s = (1-x²)^{m/2} Re g(x)` and `𝑃s(z) = (-1)^m (z-1)^{m/2} (z+1)^{m/2} g(z)` with principal
  powers (30.6.1): real on `(1, ∞)` and analytic on `ℂ ∖ (-∞, 1]` (both proved from the
  existence theorem), with the boundary values 30.6.4 and the Legendre limit `P^m_n(z)` (30.6.2).
  This form was checked numerically against the Legendre series `∑(-1)^k a_k P^m_{n+2k}(z)`.
- **`a^m_{n,k}`.** For `k ≥ -R` (`R = ⌊(n-m)/2⌋`) the integral 30.8.2 with the project's
  `ferrersP`; for `-N ≤ k < -R` (`N = ⌊(n+m)/2⌋`) the forward recursion of §30.8(ii)
  (`spheroidalFwd`: `f_{-N-1} = 0`, `f_{-N} = 1`), scaled to match `a^m_{n,-R}`; `0` below `-N`.
  DLMF says `𝖰s` does not exist when `f_{-R} = 0`; the theorems on `𝖰s`, `𝑄s` and 30.11.9 carry
  the hypothesis `spheroidalFwd … ≠ 0`. The sum `A^m_n = ∑_{2k ≥ -m-n} (-1)^k a^m_{n,k}` of 30.11.4
  includes the extended coefficients; this reading was confirmed numerically: the Wronskian
  30.5.4 of `𝖯s` with the series 30.8.9 matches only with them (e.g. `n = 3, m = 1, γ² = 4`:
  `13.39975` with, `12.99865` without). `a'^m_{n,k}` (30.8.9–30.8.10) is defined by choice as the
  recessive solution normalized by 30.8.10 (existence admitted).
- **`𝖰s` (definition by characterization, flagged).** DLMF gives no closed definition in §30.5;
  `spheroidalQs` is the solution of 30.2.1 on `(-1, 1)` with the parity 30.5.2 and the Wronskian
  30.5.4 (unique: a second one differs by a multiple of `𝖯s`, which has the opposite parity),
  extended by `0`. 30.5.2 and 30.5.4 are thus proved from the existence theorem, and the
  Meixner–Schäfke series 30.8.9 is the substantive (admitted) theorem.
- **`𝑄s` (definition by characterization, flagged).** The solution on `ℂ ∖ (-∞, 1]` whose
  boundary values from above on `(-1, 1)` are those of 30.6.5 (upper signs); existence and
  uniqueness admitted; the lower signs and the reality on `(1, ∞)` are admitted theorems.
- **`ψ^{(1)}_k` (flagged).** For `j = 1` the entire `j_k` (`DLMF.sphericalJ` of `DLMF.Core`) is
  used: 30.11.3 allows every `z ≠ 0` for `j = 1`, while the literal principal-branch formula
  30.11.1 changes sign on `(-∞, 0]`. The formula is the admitted `spheroidalPsi_one_eq` off the
  cut. For `j = 2, 3, 4` the formula with principal `(π/(2z))^{1/2}` and
  `𝒞^{(2), (3), (4)} = Y, J + iY, J - iY` (project's `besselY`, Mathlib's `besselJ`). The project
  had no `y_n`, `h_n`; they are not defined separately.
- Series are stated with `HasSum` (Ferrers series over `j ∈ ℕ`, `k = j - R`), asymptotics with
  `IsBigO` and the project's `HasAsymptoticExpansion` (30.9: powers `γ^{-i}` at `+∞`, the six
  printed coefficients as `spheroidalProlateBeta`, `spheroidalOblateC`, further coefficients
  existentially quantified); continued fractions (30.3.5) with `DLMF.cfTail` and
  `DLMF.HasContinuedFraction`, with the nondegeneracy hypotheses that DLMF leaves implicit.
  `ℓ_{2k}` (30.3.8) is the `k`-th Taylor coefficient of `γ² ↦ λ^m_n(γ²)` at `0`.
- **Import organization.** `ferrersP`, `ferrersQ`, `associatedP` and `associatedQ` now live
  in `DLMF.Legendre.Basic.Functions`, exported through `DLMF.Legendre.Basic`.
  `DLMF.Spheroidal.Basic.Ferrers` uses that definition layer; Legendre theorem dependencies
  belong to `FerrersProperties`, `Angular` and the other spheroidal theorem files.

Source corrections and checks (scripts and outputs in the agent's scratch directory, mpmath at
20–80 digits, SciPy `pro_cv`, `obl_cv`, `pro_rad1`, `pro_rad2` for cross-checks):

- **30.11.6** (erratum, `j = 1, 2`): the error term `O(z⁻² e^{|ℑz|})` is correct only for
  `γ ≤ 1`; the correct term is `O(z⁻² e^{|ℑ(γz)|})`. For `n = m = 0`, `γ = 2`, `z = iy`:
  `|S^{0(1)}_0(iy, 2) - ψ^{(1)}_0(2iy)| y² e^{-y} = 3.9·10³, 8.7·10⁷, 4.2·10¹⁶` at
  `y = 10, 20, 40`, whereas `|S - ψ| y² e^{-2y} = 0.1771, 0.1785, 0.1791` (similarly for `n = 1`).
  Acquired in the corrected form for real `γ > 0`. The `j = 3, 4` form checked for real `z`.
- 30.3.5 (stated with added hypotheses): the equivalence needs nondegeneracy (nonzero finite
  continuant on the left; nonzero expansion coefficient of index `p` for the convergence of the
  right side); stated as two implications.
- 30.5.4/30.11.4: the nonvanishing `A^m_n A^{-m}_n ≠ 0` is stated under the existence hypothesis
  of §30.8(ii).
- Checked numerically and found correct: 30.3.1, 30.3.2 (`n ≤ 160`), 30.3.4 (grid
  `|γ²| ≤ 400`, `m ≤ 4`), 30.3.5 with 30.3.6 and with 30.3.7, 30.3.9–30.3.12 (high-precision
  polynomial fits, nine `(n, m)` including `n = 0, 1`), 30.4.1 with 30.8.5, 30.4.3, the zero count
  of §30.4(ii), 30.5.2, 30.5.4 (seven cases), 30.8.7, 30.8.8, 30.8.9–30.8.11 (Wronskian, parity,
  ODE residual `≤ 10⁻²⁷`), 30.9.1–30.9.6 (scaled remainders stable between `γ = 50` and `100` for
  seven `(n, m)`), 30.11.3 (SciPy), 30.11.6 (`j = 3`), 30.11.7, 30.11.8 with 30.11.10–30.11.11,
  30.11.9 (four cases), 30.11.12, 30.6.1 and 30.6.4 (form of `𝑃s`), and the project's
  `ferrersQ` at the degrees `-m ≤ ν < m` occurring in 30.8.9 (against mpmath).

## Numbered formulas and prose items

## [§30.1 Special Notation](https://dlmf.nist.gov/30.1)

- [30.1.E1](https://dlmf.nist.gov/30.1.E1): [`DLMF.Spheroidal.flammerS1`](DLMF/Spheroidal/Basic/Ferrers.lean#L218) (definition); [`DLMF.Spheroidal.flammerS2`](DLMF/Spheroidal/Basic/Ferrers.lean#L223) (definition). Flammer's `S^{(1)}_{mn}`, `S^{(2)}_{mn}` as functions of `γ²`.
- [30.1.E2](https://dlmf.nist.gov/30.1.E2): [`DLMF.Spheroidal.flammerD`](DLMF/Spheroidal/Basic/Ferrers.lean#L209) (definition); [`DLMF.Spheroidal.flammerS1_zero`](DLMF/Spheroidal/Angular.lean#L1421) (proved); [`DLMF.Spheroidal.flammerS1_deriv_zero`](DLMF/Spheroidal/Angular.lean#L1434) (proved). `d_{mn}` defined by 30.1.2; both normalizations proved from the sign convention of §30.4(i).

## [§30.2 Differential Equations](https://dlmf.nist.gov/30.2)

- [30.2.i](https://dlmf.nist.gov/30.2.i): [`DLMF.Spheroidal.spheroidal_indicial_exponents`](DLMF/Spheroidal/Equation.lean#L154) (proved); [`DLMF.Spheroidal.spheroidal_irregular_infinity`](DLMF/Spheroidal/Equation.lean#L169) (admitted). Exponents `±μ/2` at `z = 1` (indicial polynomial, proved); irregular singularity of rank 1 at `∞` stated as existence of solutions `∼ e^{±iγz}/z` (admitted).
- [30.2.iii](https://dlmf.nist.gov/30.2.iii): [`DLMF.Spheroidal.isSpheroidalSolutionReal_ferrersP`](DLMF/Spheroidal/Equation.lean#L289) (proved); [`DLMF.Spheroidal.spheroidalLiouville_coeff_mathieu`](DLMF/Spheroidal/Equation.lean#L306) (proved); [`DLMF.Spheroidal.IsSpheroidalLiouvilleSolution.mathieu`](DLMF/Spheroidal/Equation.lean#L316) (proved); [`DLMF.Spheroidal.isSpheroidalZetaSolution_sphericalJ`](DLMF/Spheroidal/Equation.lean#L329) (proved). `γ = 0`: `𝖯^m_n` solves 30.2.1 (admitted); `μ² = 1/4`: Mathieu equation with `a = λ + 1/4 + γ²/2`, `q = γ²/4` (proved); `γ = 0` in 30.2.4: `j_n` (`DLMF.sphericalJ`) solves it (admitted).
- [30.2.E1](https://dlmf.nist.gov/30.2.E1): [`DLMF.Spheroidal.IsSpheroidalSolutionOn`](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L80) (definition); [`DLMF.Spheroidal.IsSpheroidalSolutionReal`](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L92) (definition). Divergence form with genuine differentiability, complex (`IsSpheroidalSolutionOn`, open `U` avoiding `±1`) and real on `(-1, 1)` (`IsSpheroidalSolutionReal`).
- [30.2.E2](https://dlmf.nist.gov/30.2.E2): [`DLMF.Spheroidal.IsSpheroidalLiouvilleSolution`](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L103) (definition); [`DLMF.Spheroidal.isSpheroidalLiouvilleSolution_of_isSpheroidalSolutionOn`](DLMF/Spheroidal/Equation.lean#L183) (proved). Predicate for 30.2.2; the transformation under 30.2.3 (`g(t) = (sin t)^{1/2} w(cos t)`) admitted.
- [30.2.E3](https://dlmf.nist.gov/30.2.E3): [`DLMF.Spheroidal.isSpheroidalLiouvilleSolution_of_isSpheroidalSolutionOn`](DLMF/Spheroidal/Equation.lean#L183) (proved). With 30.2.2.
- [30.2.E4](https://dlmf.nist.gov/30.2.E4): [`DLMF.Spheroidal.IsSpheroidalZetaSolution`](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L114) (definition); [`DLMF.Spheroidal.isSpheroidalZetaSolution_of_isSpheroidalSolutionOn`](DLMF/Spheroidal/Equation.lean#L243) (proved). `ζ = γz`, `γ ≠ 0`, image set `γU`.

## [§30.3 Eigenvalues](https://dlmf.nist.gov/30.3)

- [30.3.i](https://dlmf.nist.gov/30.3.i): [`DLMF.Spheroidal.IsSpheroidalFactor`](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L151) (definition); [`DLMF.Spheroidal.spheroidalSpectrum`](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L163) (definition); [`DLMF.Spheroidal.spheroidalEigenvalue`](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L169) (definition); [`DLMF.Spheroidal.exists_spheroidalEigenvalue`](DLMF/Spheroidal/Existence.lean#L60) (proved); [`DLMF.Spheroidal.isSpheroidalSolutionReal_iff_isSpheroidalFactor`](DLMF/Spheroidal/Equation.lean#L390) (proved); [`DLMF.Spheroidal.exists_bounded_iff_mem_spheroidalSpectrum`](DLMF/Spheroidal/Equation.lean#L481) (admitted). Design choice (flagged): spectrum = real `λ` with a nonzero entire solution of the factor equation; `λ^m_n` = element with `n - m` smaller elements; existence admitted; equivalence with bounded solutions admitted.
- [30.3.ii](https://dlmf.nist.gov/30.3.ii): [`DLMF.Spheroidal.analyticAt_spheroidalEigenvalue`](DLMF/Spheroidal/Eigenvalues.lean#L75) (admitted). Real-analyticity in `γ²`.
- [30.3.E1](https://dlmf.nist.gov/30.3.E1): [`DLMF.Spheroidal.spheroidalEigenvalue_lt_succ`](DLMF/Spheroidal/Eigenvalues.lean#L53) (proved); [`DLMF.Spheroidal.spheroidalEigenvalue_lt`](DLMF/Spheroidal/Eigenvalues.lean#L64) (proved). Proved from the existence theorem.
- [30.3.E2](https://dlmf.nist.gov/30.3.E2): [`DLMF.Spheroidal.spheroidalEigenvalue_isBigO_atTop`](DLMF/Spheroidal/Eigenvalues.lean#L82) (admitted). `IsBigO atTop` with `n⁻²`; checked numerically (`n ≤ 160`).
- [30.3.E3](https://dlmf.nist.gov/30.3.E3): [`DLMF.Spheroidal.spheroidalEigenvalue_zero`](DLMF/Spheroidal/Eigenvalues.lean#L89) (proved).
- [30.3.E4](https://dlmf.nist.gov/30.3.E4): [`DLMF.Spheroidal.spheroidalEigenvalue_deriv_bounds`](DLMF/Spheroidal/Eigenvalues.lean#L95) (admitted). `HasDerivAt` with `-1 < d < 0`; checked numerically on a grid `|γ²| ≤ 400`, `m ≤ 4`.
- [30.3.E5](https://dlmf.nist.gov/30.3.E5): [`DLMF.Spheroidal.spheroidal_cf_of_eigenvalue`](DLMF/Spheroidal/Eigenvalues.lean#L103) (admitted); [`DLMF.Spheroidal.spheroidal_eigenvalue_of_cf`](DLMF/Spheroidal/Eigenvalues.lean#L136) (admitted). Continuants `DLMF.cfTail`/`HasContinuedFraction`; two directions with nondegeneracy hypotheses added (nonzero finite continuant; nonzero expansion coefficient of index `p`); `alt` selects 30.3.6 or 30.3.7.
- [30.3.E6](https://dlmf.nist.gov/30.3.E6): [`DLMF.Spheroidal.spheroidalCFAlpha`](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L226) (definition); [`DLMF.Spheroidal.spheroidalCFBeta`](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L230) (definition); [`DLMF.Spheroidal.spheroidalCFGamma`](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L234) (definition); [`DLMF.Spheroidal.spheroidal_cf_of_eigenvalue`](DLMF/Spheroidal/Eigenvalues.lean#L103) (admitted); [`DLMF.Spheroidal.spheroidal_eigenvalue_of_cf`](DLMF/Spheroidal/Eigenvalues.lean#L136) (admitted). Coefficient definitions; checked numerically (truncated tridiagonal eigenproblems).
- [30.3.E7](https://dlmf.nist.gov/30.3.E7): [`DLMF.Spheroidal.spheroidalCFAlphaAlt`](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L238) (definition); [`DLMF.Spheroidal.spheroidalCFBetaAlt`](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L244) (definition); [`DLMF.Spheroidal.spheroidalCFGammaAlt`](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L250) (definition); [`DLMF.Spheroidal.spheroidal_cf_of_eigenvalue`](DLMF/Spheroidal/Eigenvalues.lean#L103) (admitted); [`DLMF.Spheroidal.spheroidal_eigenvalue_of_cf`](DLMF/Spheroidal/Eigenvalues.lean#L136) (admitted). Coefficient definitions; checked numerically.
- [30.3.E8](https://dlmf.nist.gov/30.3.E8): [`DLMF.Spheroidal.spheroidalEll`](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L296) (definition); [`DLMF.Spheroidal.hasSum_spheroidalEll`](DLMF/Spheroidal/Eigenvalues.lean#L158) (proved from admissions). `ℓ_{2k}` = Taylor coefficients of `γ² ↦ λ^m_n(γ²)` at `0`; positive radius asserted.
- [30.3.E9](https://dlmf.nist.gov/30.3.E9): [`DLMF.Spheroidal.spheroidalEll_zero`](DLMF/Spheroidal/Eigenvalues.lean#L180) (proved); [`DLMF.Spheroidal.spheroidalEll_one`](DLMF/Spheroidal/Eigenvalues.lean#L185) (admitted); [`DLMF.Spheroidal.spheroidalEll_two`](DLMF/Spheroidal/Eigenvalues.lean#L192) (admitted). `ℓ_0` proved from 30.3.3; `ℓ_2`, `ℓ_4` admitted; all checked by high-precision fits for nine `(n, m)`.
- [30.3.E10](https://dlmf.nist.gov/30.3.E10): [`DLMF.Spheroidal.spheroidalEll_three`](DLMF/Spheroidal/Eigenvalues.lean#L206) (admitted). Checked numerically.
- [30.3.E11](https://dlmf.nist.gov/30.3.E11): [`DLMF.Spheroidal.spheroidalEll_four`](DLMF/Spheroidal/Eigenvalues.lean#L218) (admitted). Checked numerically.
- [30.3.E12](https://dlmf.nist.gov/30.3.E12): [`DLMF.Spheroidal.spheroidalEllA`](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L302) (definition); [`DLMF.Spheroidal.spheroidalEllB`](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L312) (definition); [`DLMF.Spheroidal.spheroidalEllC`](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L324) (definition); [`DLMF.Spheroidal.spheroidalEllD`](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L334) (definition); [`DLMF.Spheroidal.spheroidalEll_four`](DLMF/Spheroidal/Eigenvalues.lean#L218) (admitted). Auxiliary `A, B, C, D` as definitions.

## [§30.4 Functions of the First Kind](https://dlmf.nist.gov/30.4)

- [30.4.i](https://dlmf.nist.gov/30.4.i): [`DLMF.Spheroidal.existsUnique_isSpheroidalPsFactor`](DLMF/Spheroidal/Existence.lean#L81) (proved); [`DLMF.Spheroidal.spheroidalPs`](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L203) (definition); [`DLMF.Spheroidal.spheroidalPs_zero_sign`](DLMF/Spheroidal/Angular.lean#L222) (proved); [`DLMF.Spheroidal.spheroidalPs_deriv_zero_sign`](DLMF/Spheroidal/Angular.lean#L229) (proved); [`DLMF.Spheroidal.isSpheroidalSolutionReal_spheroidalPs`](DLMF/Spheroidal/Angular.lean#L253) (proved). Normalization and sign of `𝖯s(0)` / `𝖯s'(0)`; design choice (flagged): `𝖯s = (1-x²)^{m/2} g`, `g` chosen entire, real, normalized; existence/uniqueness admitted.
- [30.4.ii](https://dlmf.nist.gov/30.4.ii): [`DLMF.Spheroidal.ncard_zeros_spheroidalPs`](DLMF/Spheroidal/Angular.lean#L629) (admitted). `ncard` of the zero set in `(-1, 1)` is `n - m`.
- [30.4.iv](https://dlmf.nist.gov/30.4.iv): [`DLMF.Spheroidal.tendstoUniformlyOn_spheroidalExpansion_sub_ferrers`](DLMF/Spheroidal/Angular.lean#L831) (admitted). Equiconvergence with the Ferrers expansion, uniformly on `[-1, 1]`.
- [30.4.E1](https://dlmf.nist.gov/30.4.E1): [`DLMF.Spheroidal.IsSpheroidalPsFactor`](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L179) (definition); [`DLMF.Spheroidal.integral_spheroidalPs_sq`](DLMF/Spheroidal/Angular.lean#L237) (proved). Proved from the existence theorem.
- [30.4.E2](https://dlmf.nist.gov/30.4.E2): [`DLMF.Spheroidal.spheroidalPs_gamma_zero`](DLMF/Spheroidal/Angular.lean#L603) (proved).
- [30.4.E3](https://dlmf.nist.gov/30.4.E3): [`DLMF.Spheroidal.spheroidalPs_neg`](DLMF/Spheroidal/Angular.lean#L616) (proved).
- [30.4.E4](https://dlmf.nist.gov/30.4.E4): [`DLMF.Spheroidal.hasSum_spheroidalPs`](DLMF/Spheroidal/Angular.lean#L637) (proved). Proved (Taylor series of the entire factor), for all real `x` (stronger than DLMF; meaningful on `[-1, 1]`).
- [30.4.E5](https://dlmf.nist.gov/30.4.E5): [`DLMF.Spheroidal.spheroidalPs_coeff_recurrence`](DLMF/Spheroidal/Angular.lean#L658) (proved). With the parity vanishing.
- [30.4.E6](https://dlmf.nist.gov/30.4.E6): [`DLMF.Spheroidal.integral_spheroidalPs_mul`](DLMF/Spheroidal/Angular.lean#L758) (proved); [`DLMF.Spheroidal.integral_spheroidalPs_mul_eq`](DLMF/Spheroidal/Angular.lean#L809) (proved). `k ≠ n` admitted; the Kronecker form proved from it and 30.4.1.
- [30.4.E7](https://dlmf.nist.gov/30.4.E7): [`DLMF.Spheroidal.tendsto_spheroidalExpansion_L2`](DLMF/Spheroidal/Angular.lean#L819) (admitted). `MemLp f 2` on `(-1, 1)`; `L²` convergence of partial sums (30.4.9).
- [30.4.E8](https://dlmf.nist.gov/30.4.E8): [`DLMF.Spheroidal.spheroidalExpansionCoeff`](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L217) (definition).
- [30.4.E9](https://dlmf.nist.gov/30.4.E9): [`DLMF.Spheroidal.tendsto_spheroidalExpansion_L2`](DLMF/Spheroidal/Angular.lean#L819) (admitted).

## [§30.5 Functions of the Second Kind](https://dlmf.nist.gov/30.5)

- [30.5.E1](https://dlmf.nist.gov/30.5.E1): [`DLMF.Spheroidal.IsSpheroidalQs`](DLMF/Spheroidal/Basic/Ferrers.lean#L133) (definition); [`DLMF.Spheroidal.spheroidalQs`](DLMF/Spheroidal/Basic/Ferrers.lean#L150) (definition); [`DLMF.Spheroidal.exists_isSpheroidalQs`](DLMF/Spheroidal/FerrersProperties.lean#L38) (admitted); [`DLMF.Spheroidal.isSpheroidalSolutionReal_spheroidalQs`](DLMF/Spheroidal/Angular.lean#L847) (proved from admissions). Design choice (flagged): `𝖰s` characterized by 30.2.1, the parity 30.5.2 and the Wronskian 30.5.4 (unique), existence admitted under nonvanishing of the forward recursion (DLMF: otherwise `𝖰s` does not exist).
- [30.5.E2](https://dlmf.nist.gov/30.5.E2): [`DLMF.Spheroidal.spheroidalQs_neg`](DLMF/Spheroidal/Angular.lean#L856) (proved from admissions). Proved from the characterization.
- [30.5.E3](https://dlmf.nist.gov/30.5.E3): [`DLMF.Spheroidal.spheroidalQs_gamma_zero`](DLMF/Spheroidal/Angular.lean#L1109) (proved).
- [30.5.E4](https://dlmf.nist.gov/30.5.E4): [`DLMF.Spheroidal.wronskian_spheroidalPs_spheroidalQs`](DLMF/Spheroidal/Angular.lean#L1172) (proved from admissions); [`DLMF.Spheroidal.spheroidalA_mul_spheroidalANeg_ne_zero`](DLMF/Spheroidal/Angular.lean#L1184) (admitted). Wronskian proved from the characterization; `A^m_n A^{-m}_n ≠ 0` admitted. Checked numerically against the series 30.8.9 (7 cases, 25 digits); the extended coefficients `-N ≤ k < -R` are needed in `A^m_n`.

## [§30.6 Functions of Complex Argument](https://dlmf.nist.gov/30.6)

- [30.6.E1](https://dlmf.nist.gov/30.6.E1): [`DLMF.Spheroidal.spheroidalPsC`](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L210) (definition); [`DLMF.Spheroidal.IsSpheroidalQsC`](DLMF/Spheroidal/Basic/Ferrers.lean#L160) (definition); [`DLMF.Spheroidal.spheroidalQsC`](DLMF/Spheroidal/Basic/Ferrers.lean#L173) (definition); [`DLMF.Spheroidal.existsUnique_isSpheroidalQsC`](DLMF/Spheroidal/FerrersProperties.lean#L47) (admitted); [`DLMF.Spheroidal.differentiableOn_spheroidalPsC`](DLMF/Spheroidal/Angular.lean#L1193) (proved); [`DLMF.Spheroidal.spheroidalPsC_im_eq_zero`](DLMF/Spheroidal/Angular.lean#L1211) (proved); [`DLMF.Spheroidal.isSpheroidalSolutionOn_spheroidalPsC`](DLMF/Spheroidal/Angular.lean#L1227) (proved); [`DLMF.Spheroidal.isSpheroidalSolutionOn_spheroidalQsC`](DLMF/Spheroidal/Angular.lean#L1265) (proved from admissions); [`DLMF.Spheroidal.spheroidalQsC_im_eq_zero`](DLMF/Spheroidal/Angular.lean#L1274) (admitted). `𝑃s = (-1)^m (z-1)^{m/2}(z+1)^{m/2} g(z)` (definition; analyticity and reality on `(1, ∞)` proved; checked against the Legendre series `∑(-1)^k a_k P^m_{n+2k}(z)`); `𝑄s` by its upper boundary values 30.6.5 (flagged choice).
- [30.6.E2](https://dlmf.nist.gov/30.6.E2): [`DLMF.Spheroidal.spheroidalPsC_gamma_zero`](DLMF/Spheroidal/Angular.lean#L1281) (admitted). `associatedP`, `associatedQ` of DLMF/Legendre/Associated.lean.
- [30.6.E3](https://dlmf.nist.gov/30.6.E3): [`DLMF.Spheroidal.wronskian_spheroidalPsC_spheroidalQsC`](DLMF/Spheroidal/Angular.lean#L1288) (admitted).
- [30.6.E4](https://dlmf.nist.gov/30.6.E4): [`DLMF.Spheroidal.tendsto_spheroidalPsC_boundary`](DLMF/Spheroidal/Angular.lean#L1349) (proved).
- [30.6.E5](https://dlmf.nist.gov/30.6.E5): [`DLMF.Spheroidal.tendsto_spheroidalQsC_boundary_upper`](DLMF/Spheroidal/Angular.lean#L1398) (proved from admissions); [`DLMF.Spheroidal.tendsto_spheroidalQsC_boundary_lower`](DLMF/Spheroidal/Angular.lean#L1409) (admitted). Upper signs proved from the characterization; lower signs admitted.

## [§30.8 Expansions in Series of Ferrers Functions](https://dlmf.nist.gov/30.8)

- [30.8.ii](https://dlmf.nist.gov/30.8.ii): [`DLMF.Spheroidal.spheroidalFwd`](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L275) (definition); [`DLMF.Spheroidal.exists_isSpheroidalCoeffPrime`](DLMF/Spheroidal/FerrersProperties.lean#L30) (admitted); [`DLMF.Spheroidal.spheroidalCoeff_of_lt`](DLMF/Spheroidal/FerrersSeries/RatiosAndSecondKind.lean#L542) (proved). Forward solution and extended coefficients (definitions); unfolding lemma proved; existence of `a'` admitted.
- [30.8.E1](https://dlmf.nist.gov/30.8.E1): [`DLMF.Spheroidal.hasSum_spheroidalPs_ferrers`](DLMF/Spheroidal/FerrersSeries/RecurrencesAndConvergence.lean#L902) (proved). Sum over `k = j - R`, `j ∈ ℕ`.
- [30.8.E2](https://dlmf.nist.gov/30.8.E2): [`DLMF.Spheroidal.spheroidalCoeffMain`](DLMF/Spheroidal/Basic/Ferrers.lean#L60) (definition); [`DLMF.Spheroidal.spheroidalCoeff`](DLMF/Spheroidal/Basic/Ferrers.lean#L69) (definition); [`DLMF.Spheroidal.spheroidalCoeff_of_le`](DLMF/Spheroidal/FerrersSeries/RecurrencesAndConvergence.lean#L30) (proved). Definition via the project's `ferrersP`; unfolding lemma proved.
- [30.8.E3](https://dlmf.nist.gov/30.8.E3): [`DLMF.Spheroidal.spheroidalRecA`](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L255) (definition); [`DLMF.Spheroidal.spheroidalRecB`](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L261) (definition); [`DLMF.Spheroidal.spheroidalRecC`](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L269) (definition).
- [30.8.E4](https://dlmf.nist.gov/30.8.E4): [`DLMF.Spheroidal.spheroidalRecA_neg_R`](DLMF/Spheroidal/FerrersSeries/RecurrencesAndConvergence.lean#L42) (proved); [`DLMF.Spheroidal.spheroidalCoeff_recurrence`](DLMF/Spheroidal/FerrersSeries/RatiosAndSecondKind.lean#L559) (proved); [`DLMF.Spheroidal.spheroidalCoeff_recurrence_of_le`](DLMF/Spheroidal/FerrersSeries/RecurrencesAndConvergence.lean#L417) (proved). All `k ∈ ℤ` (with the extension) and `k ≥ -R`; `A_{-R} = 0` proved.
- [30.8.E5](https://dlmf.nist.gov/30.8.E5): [`DLMF.Spheroidal.hasSum_spheroidalCoeff_normalization`](DLMF/Spheroidal/FerrersSeries/RecurrencesAndConvergence.lean#L997) (proved). Checked against 30.4.1.
- [30.8.E6](https://dlmf.nist.gov/30.8.E6): [`DLMF.Spheroidal.spheroidalCoeffNeg`](DLMF/Spheroidal/Basic/Ferrers.lean#L81) (definition); [`DLMF.Spheroidal.spheroidalCoeffNeg_of_le`](DLMF/Spheroidal/FerrersSeries/RecurrencesAndConvergence.lean#L512) (proved).
- [30.8.E7](https://dlmf.nist.gov/30.8.E7): [`DLMF.Spheroidal.spheroidalCoeff_ratio_isBigO`](DLMF/Spheroidal/FerrersSeries/RatiosAndSecondKind.lean#L240) (proved). `IsBigO` with `k⁻¹`.
- [30.8.E8](https://dlmf.nist.gov/30.8.E8): [`DLMF.Spheroidal.spheroidalCoeff_ratio_isBigO_four`](DLMF/Spheroidal/FerrersSeries/RatiosAndSecondKind.lean#L453) (proved). `IsBigO` with `k⁻⁴`; checked numerically.
- [30.8.E9](https://dlmf.nist.gov/30.8.E9): [`DLMF.Spheroidal.spheroidalCoeffPrime`](DLMF/Spheroidal/Basic/Ferrers.lean#L126) (definition); [`DLMF.Spheroidal.spheroidalQs_eq_ferrers_series`](DLMF/Spheroidal/FerrersSeries/RatiosAndSecondKind.lean#L521) (admitted). Two `HasSum`s; checked numerically (Wronskian, parity, ODE residual).
- [30.8.E10](https://dlmf.nist.gov/30.8.E10): [`DLMF.Spheroidal.IsSpheroidalCoeffPrime`](DLMF/Spheroidal/Basic/Ferrers.lean#L99) (definition); [`DLMF.Spheroidal.spheroidalQs_eq_ferrers_series`](DLMF/Spheroidal/FerrersSeries/RatiosAndSecondKind.lean#L521) (admitted).
- [30.8.E11](https://dlmf.nist.gov/30.8.E11): [`DLMF.Spheroidal.spheroidalCPrime`](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L288) (definition); [`DLMF.Spheroidal.spheroidalQs_eq_ferrers_series`](DLMF/Spheroidal/FerrersSeries/RatiosAndSecondKind.lean#L521) (admitted).

## [§30.9 Asymptotic Approximations and Expansions](https://dlmf.nist.gov/30.9)

- [30.9.ii](https://dlmf.nist.gov/30.9.ii): [`DLMF.Spheroidal.spheroidalOblateQ`](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L362) (definition). `q = n + 1` or `n`.
- [30.9.E1](https://dlmf.nist.gov/30.9.E1): [`DLMF.Spheroidal.spheroidalEigenvalue_prolate_asymptotic`](DLMF/Spheroidal/Eigenvalues.lean#L227) (admitted). `HasAsymptoticExpansion atTop` in powers `γ^{-i}` of `λ + γ² - γq`, first six coefficients given; checked numerically (`γ = 50, 100`, seven `(n, m)`).
- [30.9.E2](https://dlmf.nist.gov/30.9.E2): [`DLMF.Spheroidal.spheroidalProlateBeta`](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L343) (definition); [`DLMF.Spheroidal.spheroidalEigenvalue_prolate_asymptotic`](DLMF/Spheroidal/Eigenvalues.lean#L227) (admitted).
- [30.9.E3](https://dlmf.nist.gov/30.9.E3): [`DLMF.Spheroidal.spheroidalEigenvalue_prolate_asymptotic`](DLMF/Spheroidal/Eigenvalues.lean#L227) (admitted).
- [30.9.E4](https://dlmf.nist.gov/30.9.E4): [`DLMF.Spheroidal.spheroidalEigenvalue_oblate_asymptotic`](DLMF/Spheroidal/Eigenvalues.lean#L237) (admitted). In `κ = |γ|`, `γ² = -κ²`; checked numerically.
- [30.9.E5](https://dlmf.nist.gov/30.9.E5): [`DLMF.Spheroidal.spheroidalOblateC`](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L367) (definition); [`DLMF.Spheroidal.spheroidalEigenvalue_oblate_asymptotic`](DLMF/Spheroidal/Eigenvalues.lean#L237) (admitted).
- [30.9.E6](https://dlmf.nist.gov/30.9.E6): [`DLMF.Spheroidal.spheroidalEigenvalue_oblate_asymptotic`](DLMF/Spheroidal/Eigenvalues.lean#L237) (admitted).

## [§30.11 Radial Spheroidal Wave Functions](https://dlmf.nist.gov/30.11)

- [30.11.E1](https://dlmf.nist.gov/30.11.E1): [`DLMF.Spheroidal.spheroidalPsi`](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L400) (definition); [`DLMF.Spheroidal.spheroidalPsi_one_eq`](DLMF/Spheroidal/Radial.lean#L47) (proved). `ψ^{(1)}_k := j_k` (entire, `DLMF.sphericalJ`); principal-branch formula off `(-∞, 0]` admitted (flagged choice: the literal formula changes sign on the negative axis).
- [30.11.E2](https://dlmf.nist.gov/30.11.E2): [`DLMF.Spheroidal.spheroidalCylinder`](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L388) (definition); [`DLMF.Spheroidal.spheroidalPsi_three_four`](DLMF/Spheroidal/Radial.lean#L90) (proved). `ψ^{(3),(4)} = ψ^{(1)} ± iψ^{(2)}` proved from 30.11.1.
- [30.11.E3](https://dlmf.nist.gov/30.11.E3): [`DLMF.Spheroidal.spheroidalRadial`](DLMF/Spheroidal/Basic/Ferrers.lean#L182) (definition); [`DLMF.Spheroidal.summable_spheroidalRadial_series`](DLMF/Spheroidal/Radial.lean#L101) (admitted); [`DLMF.Spheroidal.isSpheroidalSolutionOn_spheroidalRadial`](DLMF/Spheroidal/Radial.lean#L112) (admitted). Definition (`γ²` evaluated as `(γ^2).re`); convergence and ODE admitted; checked against SciPy `pro_rad1`, `pro_rad2`.
- [30.11.E4](https://dlmf.nist.gov/30.11.E4): [`DLMF.Spheroidal.spheroidalA`](DLMF/Spheroidal/Basic/Ferrers.lean#L91) (definition); [`DLMF.Spheroidal.spheroidalANeg`](DLMF/Spheroidal/Basic/Ferrers.lean#L95) (definition); [`DLMF.Spheroidal.spheroidalA_mul_spheroidalANeg_ne_zero`](DLMF/Spheroidal/Angular.lean#L1184) (admitted). Definitions; nonvanishing admitted.
- [30.11.E5](https://dlmf.nist.gov/30.11.E5): [`DLMF.Spheroidal.spheroidalRadial_three_four`](DLMF/Spheroidal/Radial.lean#L124) (proved from admissions). Proved from the convergence theorem and 30.11.1.
- [30.11.E6](https://dlmf.nist.gov/30.11.E6): [`DLMF.Spheroidal.spheroidalRadial_isBigO_one_two`](DLMF/Spheroidal/Radial.lean#L160) (admitted); [`DLMF.Spheroidal.spheroidalRadial_isBigO_three_four`](DLMF/Spheroidal/Radial.lean#L170) (admitted). Corrected (`e^{|ℑ(γz)|}` for `j = 1, 2`), real `γ > 0`, sector filter `DLMF.sector (π - δ)`; see corrections.
- [30.11.E7](https://dlmf.nist.gov/30.11.E7): [`DLMF.Spheroidal.wronskian_spheroidalRadial`](DLMF/Spheroidal/Radial.lean#L181) (admitted). Checked numerically.
- [30.11.E8](https://dlmf.nist.gov/30.11.E8): [`DLMF.Spheroidal.spheroidalRadial_one_eq`](DLMF/Spheroidal/Radial.lean#L194) (admitted). Checked numerically with `K` from 30.11.10–30.11.11.
- [30.11.E9](https://dlmf.nist.gov/30.11.E9): [`DLMF.Spheroidal.spheroidalRadial_two_eq`](DLMF/Spheroidal/Radial.lean#L202) (admitted). Checked numerically (`𝑄s` from the Legendre series analogue of 30.8.9 for `z > 1`, four cases, 11 digits).
- [30.11.E10](https://dlmf.nist.gov/30.11.E10): [`DLMF.Spheroidal.spheroidalK`](DLMF/Spheroidal/Basic/Ferrers.lean#L192) (definition); [`DLMF.Spheroidal.spheroidalRadial_one_eq`](DLMF/Spheroidal/Radial.lean#L194) (admitted).
- [30.11.E11](https://dlmf.nist.gov/30.11.E11): [`DLMF.Spheroidal.spheroidalK`](DLMF/Spheroidal/Basic/Ferrers.lean#L192) (definition); [`DLMF.Spheroidal.spheroidalRadial_one_eq`](DLMF/Spheroidal/Radial.lean#L194) (admitted).
- [30.11.E12](https://dlmf.nist.gov/30.11.E12): [`DLMF.Spheroidal.spheroidalRadial_one_integral`](DLMF/Spheroidal/Radial.lean#L217) (admitted). Checked numerically.

## [§30.12 Generalized and Coulomb Spheroidal Functions](https://dlmf.nist.gov/30.12)

- [30.12.E1](https://dlmf.nist.gov/30.12.E1): [`DLMF.Spheroidal.IsGenSpheroidalSolutionOn`](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L127) (definition); [`DLMF.Spheroidal.isGenSpheroidalSolutionOn_zero_iff`](DLMF/Spheroidal/Equation.lean#L492) (proved). Predicate; reduction at `α = 0` proved.
- [30.12.E2](https://dlmf.nist.gov/30.12.E2): [`DLMF.Spheroidal.IsSpheroidalSolutionOn₂`](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L138) (definition); [`DLMF.Spheroidal.isSpheroidalSolutionOn₂_zero_iff`](DLMF/Spheroidal/Equation.lean#L503) (proved). Predicate; reduction at `α = 0` proved.

## Prose, informal and excluded items

- [§30.1](https://dlmf.nist.gov/30.1): notation (`x ∈ (-1, 1)`, real `γ²`, the names of the
  main functions) recorded above; the notations of Flammer and Abramowitz–Stegun
  (`λ_{mn}(γ) = λ^m_n(γ²) + γ²`, `R^{(j)}_{mn}(γ, z) = S^{m(j)}_n(z, γ)`) are notation only.
- §30.2(i): the remark on prolate (`γ² > 0`) and oblate (`γ² < 0`) coordinates and §30.4(i)
  paragraph 2 (names "prolate/oblate angular spheroidal wave function") are terminology.
- §30.5 paragraph 2, §30.6 (further properties, complex parameters), §30.9(i) paragraphs 3–4,
  §30.9(ii) paragraphs 3–4, §30.9(iii) (large `n`, large `m`, `x → ±1`, complex `γ²`),
  §30.11(iii) paragraph 2, §30.11(vi) paragraph 2 and §30.12 (theory and computation of
  30.12.1, 30.12.2): bibliographic pointers; not acquired.
- [§30.7](https://dlmf.nist.gov/30.7) Graphics (Figures 30.7.1–30.7.21) and §30.11(ii)
  (Figures 30.11.1–30.11.4): excluded: graphics.
- [§30.10](https://dlmf.nist.gov/30.10) Series and Integrals: references only (integral
  equations, product formulas, addition theorem, expansions in products of spherical Bessel
  functions); no formulas, not acquired.
- [§30.13](https://dlmf.nist.gov/30.13) Wave Equation in Prolate Spheroidal Coordinates
  (30.13.E1–E16): excluded: application. Mathematical content: prolate spheroidal coordinates
  30.13.1–30.13.2 and their metric coefficients 30.13.3–30.13.5, the Laplacian 30.13.6;
  separation of variables of the Helmholtz equation 30.13.7 into 30.13.8–30.13.11 (30.13.9 and
  30.13.10 are 30.2.1, 30.13.11 is `w₃'' + μ²w₃ = 0`); single-valuedness and boundedness force
  `μ = m`, `w₃ = a cos mφ + b sin mφ` (30.13.12), `w₂ = a𝖯s^m_n + b𝖰s^m_n` (30.13.13),
  `w₁ = aS^{m(1)}_n + bS^{m(2)}_n` (30.13.14), and the product is a `C²` solution in all space when
  `b₁ = b₂ = 0`; the interior Dirichlet problem for a prolate ellipsoid `ξ = ξ₀` has the
  eigenvalues `c²κ² = γ²` with `S^{m(1)}_n(ξ₀, γ) = 0` (30.13.15), and between two ellipsoids
  the condition 30.13.16.
- [§30.14](https://dlmf.nist.gov/30.14) Wave Equation in Oblate Spheroidal Coordinates
  (30.14.E1–E9): excluded: application. The same programme for oblate coordinates
  `x = c√((ξ²+1)(1-η²)) cos φ`, … (30.14.1–30.14.6), separated equations with `γ² = -κ²c²`
  (30.14.7–30.14.8: `ξ ↦ iξ` in 30.2.1), and the Dirichlet condition `S^{m(1)}_n(iξ₀, γ) = 0`
  (30.14.9).
- [§30.15](https://dlmf.nist.gov/30.15) Signal Analysis (30.15.E1–E13): excluded:
  application. Mathematical content (prolate spheroidal wave functions of Slepian–Pollak): for
  `τ, σ > 0`, `γ = τσ`, the scaled functions `φ_n(t) = √((2n+1)/(2τ)) √Λ_n 𝖯s^0_n(t/τ, γ²)` with
  `Λ_n = (2γ/π)(K^0_n(γ) A^0_n(γ²))²` (30.15.1–30.15.2) are the eigenfunctions of the
  sinc-kernel integral equation `∫_{-τ}^{τ} sin σ(t-s)/(π(t-s)) φ_n(s) ds = Λ_n φ_n(t)` (30.15.3);
  their Fourier transforms 30.15.4–30.15.6 (band-limitedness); the double orthogonality
  `∫_{-τ}^{τ} φ_kφ_n = Λ_nδ_{kn}`, `∫_ℝ φ_kφ_n = δ_{kn}` (30.15.7–30.15.8), completeness in the
  `σ`-band-limited functions and in `L²(-τ, τ)`; the energy-concentration extremal problem
  30.15.9–30.15.13 with `arccos √B + arccos √α = arccos √Λ_0`. These are candidates for a later
  decision.
- [§30.16](https://dlmf.nist.gov/30.16) Methods of Computation (30.16.E1–E9): excluded:
  computation (truncated matrix eigenproblems for `λ^m_n` with error bounds 30.16.1–30.16.6,
  normalization of truncated coefficient vectors 30.16.7–30.16.9; the underlying recurrences
  30.3.5 and 30.8.4 are acquired).
- [§30.17](https://dlmf.nist.gov/30.17) Tables: excluded: numerical.
  [§30.18](https://dlmf.nist.gov/30.18) Software: excluded: software.

## Validation

- All seven modules build with `lake build DLMF.Spheroidal.<Module>` and each passes
  `lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false` with only `sorry` warnings.
  There are no axioms, no `native_decide`, no `sorry` in definitions or helper lemmas (the
  helpers are `private` with prefix `s30_`); the five admitted theorems in the definitions files
  are the flagged existence theorems. Lines are at most 100 characters.
- `#print axioms` over all 92 theorems: the 10 proved without admissions depend on
  `[propext, Classical.choice, Quot.sound]` (`spheroidal_indicial_exponents`,
  `spheroidalLiouville_coeff_mathieu`, `IsSpheroidalLiouvilleSolution.mathieu`,
  `isGenSpheroidalSolutionOn_zero_iff`, `isSpheroidalSolutionOn₂_zero_iff`,
  `spheroidalRecA_neg_R`, `spheroidalCoeff_of_le`, `spheroidalCoeffNeg_of_le`,
  `spheroidalCoeff_of_lt`, `spheroidalPs_zero`); the others also on `sorryAx`.
- Theorems proved from admissions (20 tagged): the ordering 30.3.1, `ℓ_0` (from 30.3.3), the
  sign conventions and the normalization 30.4.1, 30.4.4, the orthogonality relation with
  Kronecker delta, the facts about `𝖯s` and `𝑃s` that follow from the existence theorem
  (analyticity, reality, ODE), 30.5.1–30.5.2, 30.5.4, 30.6.1 for `𝑄s`, the upper signs of
  30.6.5, the two normalizations of 30.1.2, `ψ^{(3), (4)} = ψ^{(1)} ± iψ^{(2)}` and the
  connection formulas 30.11.5.
- DLMF.lean, the area umbrella `DLMF/Spheroidal.lean`, README, the lakefile and the other
  ledgers were not touched (the coordinator writes the umbrella).
