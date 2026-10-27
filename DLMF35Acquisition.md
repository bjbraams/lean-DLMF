# DLMF Chapter 35 acquisition: Functions of Matrix Argument

This acquisition covers the definitions, numbered formulas and analytical assertions in prose
of [DLMF Chapter 35](https://dlmf.nist.gov/35), version 1.2.8, checked on 2026-10-26, by one
agent (agent ma, helper prefix `m35_`). The Lean code is in `DLMF/MatrixArgument/` (namespace
`DLMF.MatrixArgument`). The modules, in import order, are
[Basic](DLMF/MatrixArgument/Basic.lean) (all definitions; imports Mathlib and Tau Ceti only),
[GammaBeta](DLMF/MatrixArgument/GammaBeta.lean) (§§35.2–35.3; imports `Basic` and
`TauCeti.Analysis.SpecialFunctions.MultivariateGamma.Basic`),
[Zonal](DLMF/MatrixArgument/Zonal.lean) (§35.4; imports `Basic`),
[Generalized](DLMF/MatrixArgument/Generalized.lean) (§35.8; imports `Zonal`),
[Bessel](DLMF/MatrixArgument/Bessel.lean) (§35.5; imports `Generalized`),
[Confluent](DLMF/MatrixArgument/Confluent.lean) (§35.6; imports `Generalized`),
[Gaussian](DLMF/MatrixArgument/Gaussian.lean) (§35.7; imports `Generalized`) and
[MathlibCoverage](DLMF/MatrixArgument/MathlibCoverage.lean) (upstream pointers to Tau Ceti;
imports `DLMF.Core.Upstream` and `TauCeti.Analysis.SpecialFunctions.MultivariateGamma.Integral`).
No module imports a theorem file of another area.

**Counts.** §§35.2–35.8 have 62 numbered equations (35.2: 3, 35.3: 8, 35.4: 9, 35.5: 8,
35.6: 10, 35.7: 11, 35.8: 13); §35.1 is notation only; §§35.9–35.12 have no numbered equations
and are excluded (35.9: application; 35.10–35.12: computation). In scope: 62. Covered: 59 by
project declarations; 35.7.E4 (a limit that leaves the convergence region of the series) and
35.7.E10–E11 (displays of functions whose asymptotics are only cited) are recorded as not
formalized. In addition 6 prose IDs (35.1, 35.2, 35.4.i, 35.4.ii, 35.7.iii, 35.8.i) carry tags.
65 DLMF IDs are tagged by 84 `@[dlmf]` attributes. The modules contain 39 definitions (35 in
`Basic`, among them one instance; 4 instances in `Zonal`) and 81 theorems: 34 proved (of
which 5 private `m35_` helpers and 12 untagged API lemmas) and 47 admitted; no proved theorem
depends on an admission. There are 4 upstream pointers (Tau Ceti).

Module admissions (`grep -cE 'by sorry|:= sorry|^\s*(·\s*)?sorry\s*$|exact sorry'`) and
declarations:

- [Basic](DLMF/MatrixArgument/Basic.lean): 0 admissions; 35 definitions.
- [GammaBeta](DLMF/MatrixArgument/GammaBeta.lean): 7 admissions; 11 theorems: 4 proved,
  7 admitted.
- [Zonal](DLMF/MatrixArgument/Zonal.lean): 5 admissions; 4 instances, 18 theorems:
  13 proved, 5 admitted.
- [Generalized](DLMF/MatrixArgument/Generalized.lean): 13 admissions; 26 theorems:
  13 proved, 13 admitted.
- [Bessel](DLMF/MatrixArgument/Bessel.lean): 6 admissions; 7 theorems: 1 proved, 6 admitted.
- [Confluent](DLMF/MatrixArgument/Confluent.lean): 8 admissions; 10 theorems: 2 proved,
  8 admitted.
- [Gaussian](DLMF/MatrixArgument/Gaussian.lean): 8 admissions; 9 theorems: 1 proved,
  8 admitted.
- [MathlibCoverage](DLMF/MatrixArgument/MathlibCoverage.lean): 0 admissions; 4 pointers.

## Design

- **Matrices, `𝓢`, `Ω` and `dX`.** Matrices are `Matrix (Fin m) (Fin m) ℝ`. The space `𝓢` of
  real symmetric matrices is Tau Ceti's `selfAdjoint.submodule ℝ (Matrix (Fin m) (Fin m) ℝ)`
  (`SymMatrix m`), and DLMF's `dX = ∏_{j≤k} dx_{j,k}` is Tau Ceti's
  `TauCeti.symmetricLebesgue m`, the push-forward of Lebesgue measure on the upper-triangular
  coordinates; with it Tau Ceti proves 35.3.1 for real `a`, which confirms the normalization.
  `Ω` is `posDefCone m` (Mathlib's `Matrix.PosDef`), `S < X < T` is `matrixInterval S T`,
  `etr`, `leadingMinor` (`|(X)_j|`) and `matrixSpectralNorm` (operator norm on Euclidean space)
  are the remaining notations of 35.1.
- **Haar measure.** `O(m)` is Mathlib's `Matrix.orthogonalGroup (Fin m) ℝ`, a topological
  group (Mathlib); the project proves it compact (`instCompactSpaceOrthogonalGroup`) and takes
  `dH = orthogonalHaar m := Measure.haarMeasure ⊤`, a probability measure. Right invariance
  (`isMulRightInvariant_orthogonalHaar`) is proved from uniqueness of Haar measure.
- **Partitions.** DLMF's partitions are vectors `(k₁, …, k_m)`; they are nonincreasing
  `κ : Fin m → ℕ`, and `partitions m k` is the `Finset` of those of weight `k`. Mathlib's
  `Nat.Partition` (multisets of positive parts) and `YoungDiagram` were not used: the vector
  form is what 35.4.1–35.4.3 index by, and sums over `partitions m k` are finite sums.
- **Zonal polynomials (honest definition).** DLMF *defines* `Z_κ` by 35.4.2 and 35.4.3 (an
  integral over `O(m)` of products of principal minors), and so does the project:
  `zonalPolynomial κ T = zonalPolynomialAtOne κ * ∫_{O(m)} ∏_{j=1}^{m} |(HTHᵀ)_j|^{k_j-k_{j+1}} dH`
  (the factor `j = m` is DLMF's `|T|^{k_m}`; the literal form is `zonalPolynomial_eq_dlmf`).
  No Jack polynomials or choice are needed. The normalization was checked numerically for
  `m = 2` against `∑_{|κ|=k} Z_κ(T) = (tr T)^k` (35.4.6) for `k ≤ 5`. Proved: 35.4.2, the DLMF
  form 35.4.3, 35.4.4, 35.4.5, homogeneity `Z_κ(cT) = c^{|κ|} Z_κ(T)`, and `Z_{(k)}(t) = t^k`
  for `m = 1`. Polynomiality in the eigenvalues (35.4(ii)), 35.4.6–35.4.9 are admitted.
- **Products of matrices as arguments.** DLMF's `Z_κ` and the functions of matrix argument
  live on `𝓢`; at a product such as `TX` (`X ∈ Ω`) DLMF means the function of the eigenvalues
  of `TX`. The formula for `Z_κ` is not a class function on nonsymmetric matrices, so the
  statements use the symmetric matrix `X^{1/2} T X^{1/2}` (`CFC.sqrt X * T * CFC.sqrt X`),
  which has the same eigenvalues (35.4.7, 35.4.9, 35.5.4, 35.5.5, 35.5.7, 35.6.5, 35.8.13).
- **Multivariate gamma and beta.** `multivariateGamma m a` is the product formula 35.3.4 over
  `ℂ` (the meromorphic continuation of 35.3.1, needed because 35.5.1 and others use `Γ_m` at
  arbitrary arguments); it agrees with Tau Ceti's real `TauCeti.multivariateGamma`
  (`multivariateGamma_ofReal`, proved). `multivariateGammaVec` is 35.3.5 and
  `multivariateBeta` is 35.3.7; the integrals 35.3.1–35.3.3, 35.3.8 are theorems (admitted for
  complex parameters). `[a]_κ` is `partitionalShiftedFactorial a κ` over any field;
  `[a]_κ = Γ_m(a+κ)/Γ_m(a)` (35.4.1) is proved.
- **Hypergeometric functions.** `hypergeometricPFQ a b T` is 35.8.1 as the Lean `tsum` over `k`
  of the finite sums over `partitions m k` (with `a : Fin p → ℂ`, `b : Fin q → ℂ`); `hyp1F1`,
  `hyp2F1`, `hyp0F1`, `hyp1F0`, `hyp0F0`, `hyp3F2` are its special cases, `besselA` is 35.5.2
  (with `A_ν(0) = 1/Γ_m(ν+(m+1)/2)`), and `besselB`, `kummerPsi` are the integrals 35.5.3,
  35.6.2. DLMF's regularity condition `-b + (j+1)/2 ∉ ℕ` (`1 ≤ j ≤ m`) on a denominator
  parameter is stated as `multivariateGamma m b ≠ 0` (equivalent), and implies `[b]_κ ≠ 0`
  (`partitionalShiftedFactorial_ne_zero`). For `m = 1` the series is the classical one
  (`hypergeometricPFQ_fin_one`, `hyp1F1_fin_one`), and `hyp2F1` is Mathlib's
  `ordinaryHypergeometric` (`hyp2F1_fin_one`), all proved.
- **Integrals.** Every integral identity is stated with `HasIntegralOn s f I` (integrability on
  `s` for `dX` together with the value), so the convention that a non-integrable function has
  integral `0` never enters. Limits are `Filter.Tendsto` along real parameters `→ +∞`.
- **Domains.** The series definition of `₂F₁`, `₃F₂` reaches `‖T‖ < 1` and `T = I` (where it
  converges); identities whose arguments leave that region are stated where they stay in it
  (35.7.3: `0 ≤ t₁, t₂ < 1`; Pfaff forms of 35.7.6: `0 < T < I/2`; 35.8.12–35.8.13: the
  parameter ranges where both series converge), and 35.7.4 is not formalized.
- **Reuse.** Tau Ceti: `symmetricLebesgue`, `multivariateGamma` and its cone integral
  (pointers), `selfAdjoint.submodule`; Mathlib: `Matrix.PosDef`, `Matrix.orthogonalGroup`,
  `Measure.haarMeasure`, `CFC.sqrt` on matrices, `ascPochhammer`, `Complex.Gamma`,
  `ordinaryHypergeometric`. The project's scalar Kummer and Gauss functions are not needed: the
  `m = 1` reductions are to the classical series and to Mathlib's `ordinaryHypergeometric`.

## Source corrections (suspected DLMF errata)

All were checked before acquisition; `m = 2` checks use the zonal polynomials computed from
35.4.2–35.4.3 (`Z_κ(diag(t₁,t₂)) = Z_κ(I)(t₁t₂)^{k₂} ⟨(t₁cos²θ + t₂sin²θ)^{k₁-k₂}⟩_θ`).

- **35.2.2** (inversion formula): with DLMF's `d𝐙 = ∏_{j≤k} dz_{j,k}` the constant must be
  `2^{m(m-1)/2} (2πi)^{-m(m+1)/2}`: the pairing `tr(VX) = ∑ v_{jj}x_{jj} + 2∑_{j<k} v_{jk}x_{jk}`
  doubles the off-diagonal frequencies. Check: for `φ(X) = exp(-½ tr X²)` on `𝓢`,
  `∫_𝓢 φ̂(V) dV = (2π)^m π^{m(m-1)/2} = (2π)^{m(m+1)/2} / 2^{m(m-1)/2}`. Acquired corrected;
  identical for `m = 1`.
- **35.7.8** (reflection formula): the condition `½(j+1) - a ∈ ℕ` for some `j = 1, …, m` must
  be restricted to `j = 1` (`a ∈ {0, -1, …}`). For `m = 2`, `b = 0.4`, `c = 2.7`,
  `T = diag(0.3, 0.65)`: `a = 1/2` gives `1.08962` against `-3.74181`, `a = -1/2` gives
  `0.92364` against `0.24711`; `a = -2` agrees to 30 digits.
- **35.8(i), first paragraph** (termination): `-a_j + (k+1)/2 ∈ ℕ` gives termination only for
  `k = 1`; for `k ≥ 2` the partitions `(n, 0, …, 0)` still contribute (`m = 2`, `a = 1/2`:
  `[1/2]_{(n,0)} = (1/2)_n`, and `₁F₀(1/2; T) = |I - T|^{-1/2}` is not a polynomial).
- **35.8.6** (Pfaff–Saalschütz): the printed right-hand side is the reciprocal of the correct
  value. `m = 1`, `a = (-3, 0.7, 0.45)`, `b₁ = 4.2`: `₃F₂ = 1.0503775`, printed `0.9520387`,
  reciprocal `1.0503775` (the classical 16.4.3); `m = 2`: `1.1193706` against printed
  `0.8933592 = 1/1.1193706`.
- **35.8.7** (Thomae): the upper parameter `b₂ - a₂` must be `b₂ - a₁`, and `Γ(c)`, `Γ(c + a₃)`
  must be `Γ_m(c)`, `Γ_m(c + a₃)`. `m = 1` (`a = (0.6, 0.7, 0.3)`, `b = (2.2, 3.1)`):
  `1.0220067` = corrected, printed parameters give `0.8434897`; `m = 2` terminating cases agree
  with the corrected form to 25 digits (e.g. `0.0844907`), the printed form gives `-0.2199`.
- **35.8.13** (Euler integral): the factor is `B_m(b₁ - a₁, a₁)`, not `1/B_m(b₁ - a₁, a₁)`
  (compare 35.6.4). `m = 1`, `p = q = 0`, `a₁ = 0.7`, `b₁ = 2.1`, `t = 0.8`: integral
  `1.4715874` = `B · ₁F₁`, printed `₁F₁/B = 1.2149568`.

## Numbered formulas and prose items

## [§35.1 Special Notation](https://dlmf.nist.gov/35.1)

- [35.1](https://dlmf.nist.gov/35.1): notation; [`DLMF.MatrixArgument.posDefCone`](DLMF/MatrixArgument/Basic.lean#L85) (definition); [`DLMF.MatrixArgument.orthogonalHaar`](DLMF/MatrixArgument/Basic.lean#L136) (definition); upstream `TauCeti.symmetricLebesgue` (the measure `dX`). The other notations are `SymMatrix`, `matrixInterval`, `etr`, `leadingMinor`, `matrixSpectralNorm` (see "Design"). 35.1.p5 (alternative notations of Herz, Faraut–Korányi, Terras): no statement.

## [§35.2 Laplace Transform](https://dlmf.nist.gov/35.2)

- [35.2](https://dlmf.nist.gov/35.2): [`DLMF.MatrixArgument.laplaceTransform_integrableOn_analyticOnNhd`](DLMF/MatrixArgument/GammaBeta.lean#L117) (admitted). Paragraph 35.2.Px1.p2 (absolute convergence for ℜ𝐙 > X₀ and holomorphy in the entries `z_{j,k}`); measurability of `f` added.
- [35.2.E1](https://dlmf.nist.gov/35.2.E1): [`DLMF.MatrixArgument.laplaceTransform`](DLMF/MatrixArgument/Basic.lean#L311) (definition)
- [35.2.E2](https://dlmf.nist.gov/35.2.E2): [`DLMF.MatrixArgument.laplaceTransform_inversion`](DLMF/MatrixArgument/GammaBeta.lean#L136) (admitted). **Corrected**: DLMF omits the factor `2^{m(m-1)/2}` (Fourier inversion on `𝓢` with `tr(VX)` doubling the off-diagonal frequencies; checked with a Gaussian). Continuity of `f` added; DLMF's limit hypothesis as `U → ∞` dropped (not needed).
- [35.2.E3](https://dlmf.nist.gov/35.2.E3): [`DLMF.MatrixArgument.matrixConvolution`](DLMF/MatrixArgument/Basic.lean#L320) (definition); [`DLMF.MatrixArgument.laplaceTransform_matrixConvolution`](DLMF/MatrixArgument/GammaBeta.lean#L167) (proved). The convolution theorem of 35.2.Px3.p1.

## [§35.3 Multivariate Gamma and Beta Functions](https://dlmf.nist.gov/35.3)

- [35.3.E1](https://dlmf.nist.gov/35.3.E1): [`DLMF.MatrixArgument.multivariateGamma_eq_integral`](DLMF/MatrixArgument/GammaBeta.lean#L582) (proved); upstream `TauCeti.integral_posDef_multivariateGamma`; upstream `TauCeti.integrableOn_posDef_det_rpow_mul_exp_neg_trace`. Complex `a` admitted; the real case is upstream in Tau Ceti (pointers in [MathlibCoverage](DLMF/MatrixArgument/MathlibCoverage.lean)).
- [35.3.E2](https://dlmf.nist.gov/35.3.E2): [`DLMF.MatrixArgument.multivariateGammaVec_eq_integral`](DLMF/MatrixArgument/GammaBeta.lean#L611) (proved). Zero-based indices; the factor `|X|^{s_m-(m+1)/2}` is the `j = m` factor with `s_{m+1} := (m+1)/2`.
- [35.3.E3](https://dlmf.nist.gov/35.3.E3): [`DLMF.MatrixArgument.multivariateBeta_eq_integral`](DLMF/MatrixArgument/GammaBeta.lean#L1372) (proved)
- [35.3.E4](https://dlmf.nist.gov/35.3.E4): [`DLMF.MatrixArgument.multivariateGamma`](DLMF/MatrixArgument/Basic.lean#L168) (definition); [`DLMF.MatrixArgument.multivariateGamma_ofReal`](DLMF/MatrixArgument/GammaBeta.lean#L564) (proved); [`DLMF.MatrixArgument.multivariateGamma_one`](DLMF/MatrixArgument/GammaBeta.lean#L577) (proved); upstream `TauCeti.multivariateGamma_def`. Definition by the product formula (the meromorphic continuation of 35.3.1); agrees with Tau Ceti's real `TauCeti.multivariateGamma`.
- [35.3.E5](https://dlmf.nist.gov/35.3.E5): [`DLMF.MatrixArgument.multivariateGammaVec`](DLMF/MatrixArgument/Basic.lean#L177) (definition). Definition by the product formula (continuation of 35.3.2).
- [35.3.E6](https://dlmf.nist.gov/35.3.E6): [`DLMF.MatrixArgument.multivariateGammaVec_const`](DLMF/MatrixArgument/GammaBeta.lean#L1395) (proved)
- [35.3.E7](https://dlmf.nist.gov/35.3.E7): [`DLMF.MatrixArgument.multivariateBeta`](DLMF/MatrixArgument/Basic.lean#L185) (definition); [`DLMF.MatrixArgument.multivariateBeta_one`](DLMF/MatrixArgument/GammaBeta.lean#L1400) (proved). Definition `B_m(a,b) = Γ_m(a)Γ_m(b)/Γ_m(a+b)`; the integral 35.3.3 is a theorem.
- [35.3.E8](https://dlmf.nist.gov/35.3.E8): [`DLMF.MatrixArgument.multivariateBeta_eq_integral_posDefCone`](DLMF/MatrixArgument/GammaBeta.lean#L1406) (proved)

## [§35.4 Partitions and Zonal Polynomials](https://dlmf.nist.gov/35.4)

- [35.4.i](https://dlmf.nist.gov/35.4.i): [`DLMF.MatrixArgument.partitions`](DLMF/MatrixArgument/Basic.lean#L144) (definition). Partitions are nonincreasing `κ : Fin m → ℕ` (DLMF's vectors with at most `m` parts); `partitionLength` is `ℓ(κ)`, `|κ|` is `∑ j, κ j`.
- [35.4.E1](https://dlmf.nist.gov/35.4.E1): [`DLMF.MatrixArgument.partitionalShiftedFactorial`](DLMF/MatrixArgument/Basic.lean#L160) (definition); [`DLMF.MatrixArgument.multivariateGammaVec_add_div`](DLMF/MatrixArgument/Zonal.lean#L111) (proved). First equality proved under `Γ_m(a) ≠ 0`; the second is the definition.
- [35.4.E2](https://dlmf.nist.gov/35.4.E2): [`DLMF.MatrixArgument.zonalPolynomialAtOne`](DLMF/MatrixArgument/Basic.lean#L193) (definition); [`DLMF.MatrixArgument.zonalPolynomial_one`](DLMF/MatrixArgument/Zonal.lean#L134) (proved)
- [35.4.E3](https://dlmf.nist.gov/35.4.E3): [`DLMF.MatrixArgument.zonalPolynomial`](DLMF/MatrixArgument/Basic.lean#L206) (definition); [`DLMF.MatrixArgument.zonalPolynomial_eq_dlmf`](DLMF/MatrixArgument/Zonal.lean#L152) (proved). Definition by DLMF's formula itself (Haar integral over `O(m)`), with the factor `|T|^{k_m}` written as the `j = m` factor; the literal DLMF form is `zonalPolynomial_eq_dlmf`.
- [35.4.E4](https://dlmf.nist.gov/35.4.E4): [`DLMF.MatrixArgument.zonalPolynomial_zero`](DLMF/MatrixArgument/Zonal.lean#L188) (proved). Proved for every `κ`.
- [35.4.E5](https://dlmf.nist.gov/35.4.E5): [`DLMF.MatrixArgument.zonalPolynomial_conj`](DLMF/MatrixArgument/Zonal.lean#L227) (proved)
- [35.4.E6](https://dlmf.nist.gov/35.4.E6): [`DLMF.MatrixArgument.sum_zonalPolynomial`](DLMF/MatrixArgument/Zonal.lean#L569) (admitted)
- [35.4.E7](https://dlmf.nist.gov/35.4.E7): [`DLMF.MatrixArgument.integral_zonalPolynomial_conj`](DLMF/MatrixArgument/Zonal.lean#L576) (admitted). `S ∈ Ω`, `T ∈ 𝓢`; `Z_κ(SHTH⁻¹)` is written `Z_κ(S^{1/2}HTHᵀS^{1/2})` (same eigenvalues).
- [35.4.E8](https://dlmf.nist.gov/35.4.E8): [`DLMF.MatrixArgument.hasIntegralOn_zonalPolynomial_laplace`](DLMF/MatrixArgument/Zonal.lean#L702) (proved)
- [35.4.E9](https://dlmf.nist.gov/35.4.E9): [`DLMF.MatrixArgument.hasIntegralOn_zonalPolynomial_beta`](DLMF/MatrixArgument/Zonal.lean#L805) (admitted). `Z_κ(TX)` written `Z_κ(X^{1/2}TX^{1/2})`.
- [35.4.ii](https://dlmf.nist.gov/35.4.ii): [`DLMF.MatrixArgument.zonalPolynomial_exists_symmetric`](DLMF/MatrixArgument/Zonal.lean#L555) (proved). The prose after 35.4.5 ("therefore `Z_κ(T)` is a symmetric polynomial in the eigenvalues"), with homogeneity of degree `|κ|`. Untagged proved companions: `zonalPolynomial_smul` (`Z_κ(cT) = c^{|κ|}Z_κ(T)`), `zonalPolynomial_neg`, `zonalPolynomial_fin_one` (`m = 1`: `Z_{(k)}(t) = t^k`).

## [§35.5 Bessel Functions of Matrix Argument](https://dlmf.nist.gov/35.5)

- [35.5.E1](https://dlmf.nist.gov/35.5.E1): [`DLMF.MatrixArgument.besselA_zero`](DLMF/MatrixArgument/Bessel.lean#L33) (proved). Proved from 35.8.4 and 35.8.8.
- [35.5.E2](https://dlmf.nist.gov/35.5.E2): [`DLMF.MatrixArgument.besselA`](DLMF/MatrixArgument/Basic.lean#L262) (definition). Definition, with `A_ν(0) = 1/Γ_m(ν+(m+1)/2)` built in.
- [35.5.E3](https://dlmf.nist.gov/35.5.E3): [`DLMF.MatrixArgument.besselB`](DLMF/MatrixArgument/Basic.lean#L271) (definition); [`DLMF.MatrixArgument.integrableOn_besselB`](DLMF/MatrixArgument/Bessel.lean#L59) (proved). Definition by the integral; absolute convergence stated as `integrableOn_besselB`.
- [35.5.E4](https://dlmf.nist.gov/35.5.E4): [`DLMF.MatrixArgument.hasIntegralOn_besselA_laplace`](DLMF/MatrixArgument/Bessel.lean#L110) (admitted). `A_ν(SX)` written `A_ν(X^{1/2}SX^{1/2})`.
- [35.5.E5](https://dlmf.nist.gov/35.5.E5): [`DLMF.MatrixArgument.hasIntegralOn_besselA_convolution`](DLMF/MatrixArgument/Bessel.lean#L120) (admitted). Products sandwiched by `X^{1/2}`, `(T-X)^{1/2}`, `T^{1/2}`.
- [35.5.E6](https://dlmf.nist.gov/35.5.E6): [`DLMF.MatrixArgument.besselB_neg`](DLMF/MatrixArgument/Bessel.lean#L134) (proved)
- [35.5.E7](https://dlmf.nist.gov/35.5.E7): [`DLMF.MatrixArgument.hasIntegralOn_besselA_mul_besselB`](DLMF/MatrixArgument/Bessel.lean#L233) (admitted). Products sandwiched by `X^{1/2}`.
- [35.5.E8](https://dlmf.nist.gov/35.5.E8): [`DLMF.MatrixArgument.integral_etr_orthogonal`](DLMF/MatrixArgument/Bessel.lean#L246) (admitted)
- [35.5.iii](https://dlmf.nist.gov/35.5.iii): No statement (references only).

## [§35.6 Confluent Hypergeometric Functions of Matrix Argument](https://dlmf.nist.gov/35.6)

- [35.6.E1](https://dlmf.nist.gov/35.6.E1): [`DLMF.MatrixArgument.hyp1F1`](DLMF/MatrixArgument/Basic.lean#L243) (definition); [`DLMF.MatrixArgument.hyp1F1_eq_tsum`](DLMF/MatrixArgument/Confluent.lean#L31) (proved). Definition as `pFq` with `p = q = 1`; the series form is proved. Untagged: `hyp1F1_fin_one` (`m = 1`, Kummer's series).
- [35.6.E2](https://dlmf.nist.gov/35.6.E2): [`DLMF.MatrixArgument.kummerPsi`](DLMF/MatrixArgument/Basic.lean#L281) (definition); [`DLMF.MatrixArgument.integrableOn_kummerPsi`](DLMF/MatrixArgument/Confluent.lean#L46) (proved). Definition by the integral; absolute convergence stated as `integrableOn_kummerPsi`.
- [35.6.E3](https://dlmf.nist.gov/35.6.E3): [`DLMF.MatrixArgument.laguerreL`](DLMF/MatrixArgument/Basic.lean#L293) (definition)
- [35.6.E4](https://dlmf.nist.gov/35.6.E4): [`DLMF.MatrixArgument.hasIntegralOn_hyp1F1`](DLMF/MatrixArgument/Confluent.lean#L157) (admitted). Stated as `∫ … = B_m(a, b-a) ₁F₁(a; b; T)` with integrability.
- [35.6.E5](https://dlmf.nist.gov/35.6.E5): [`DLMF.MatrixArgument.hasIntegralOn_hyp1F1_laplace`](DLMF/MatrixArgument/Confluent.lean#L170) (admitted). `₁F₁(SX)` written `₁F₁(X^{1/2}SX^{1/2})`; `S ∈ 𝓢`, `T ∈ Ω` made explicit.
- [35.6.E6](https://dlmf.nist.gov/35.6.E6): [`DLMF.MatrixArgument.hasIntegralOn_hyp1F1_convolution`](DLMF/MatrixArgument/Confluent.lean#L182) (admitted)
- [35.6.E7](https://dlmf.nist.gov/35.6.E7): [`DLMF.MatrixArgument.hyp1F1_kummer`](DLMF/MatrixArgument/Confluent.lean#L196) (admitted)
- [35.6.E8](https://dlmf.nist.gov/35.6.E8): [`DLMF.MatrixArgument.hasIntegralOn_kummerPsi_mellin`](DLMF/MatrixArgument/Confluent.lean#L208) (proved)
- [35.6.E9](https://dlmf.nist.gov/35.6.E9): [`DLMF.MatrixArgument.tendsto_hyp1F1_besselA`](DLMF/MatrixArgument/Confluent.lean#L358) (admitted). Real `a → +∞`; `Γ_m(ν+(m+1)/2) ≠ 0` made explicit.
- [35.6.E10](https://dlmf.nist.gov/35.6.E10): [`DLMF.MatrixArgument.tendsto_kummerPsi_besselB`](DLMF/MatrixArgument/Confluent.lean#L368) (admitted). Real `a → +∞`, `T ∈ Ω`.
- [35.6.iv](https://dlmf.nist.gov/35.6.iv): No statement (references only).

## [§35.7 Gaussian Hypergeometric Function of Matrix Argument](https://dlmf.nist.gov/35.7)

- [35.7.E1](https://dlmf.nist.gov/35.7.E1): [`DLMF.MatrixArgument.hyp2F1`](DLMF/MatrixArgument/Basic.lean#L249) (definition); [`DLMF.MatrixArgument.hyp2F1_eq_tsum`](DLMF/MatrixArgument/Gaussian.lean#L39) (proved). Definition as `pFq` with `p = 2`, `q = 1`; the series form is proved; convergence for `‖T‖ < 1` is the §35.8(i) statement `hypergeometricPFQ_summable_of_eq_succ`. Untagged: `hyp2F1_fin_one` (`m = 1`: Mathlib's `ordinaryHypergeometric`).
- [35.7.E2](https://dlmf.nist.gov/35.7.E2): [`DLMF.MatrixArgument.jacobiP`](DLMF/MatrixArgument/Basic.lean#L301) (definition)
- [35.7.E3](https://dlmf.nist.gov/35.7.E3): [`DLMF.MatrixArgument.hyp2F1_diagonal_two`](DLMF/MatrixArgument/Gaussian.lean#L47) (admitted). Restricted to `0 ≤ t₁, t₂ < 1` (so that the classical `₂F₁` series converges at `t₁ + t₂ - t₁t₂`).
- [35.7.E4](https://dlmf.nist.gov/35.7.E4): Not formalized: the argument `I - cT⁻¹` leaves `‖T‖ < 1` as `c → ∞`, and the analytic continuation of `₂F₁` of matrix argument is not defined (checked numerically for `m = 1`).
- [35.7.E5](https://dlmf.nist.gov/35.7.E5): [`DLMF.MatrixArgument.hasIntegralOn_hyp2F1`](DLMF/MatrixArgument/Gaussian.lean#L63) (admitted). Stated as `∫ … = B_m(a, c-a) ₂F₁(a, b; c; T)` with integrability.
- [35.7.E6](https://dlmf.nist.gov/35.7.E6): [`DLMF.MatrixArgument.hyp2F1_euler`](DLMF/MatrixArgument/Gaussian.lean#L77) (admitted); [`DLMF.MatrixArgument.hyp2F1_pfaff`](DLMF/MatrixArgument/Gaussian.lean#L85) (admitted). First equality on `0 < T < I`; the two Pfaff forms on `0 < T < I/2`, where `‖T(I-T)⁻¹‖ < 1`.
- [35.7.E7](https://dlmf.nist.gov/35.7.E7): [`DLMF.MatrixArgument.hyp2F1_one`](DLMF/MatrixArgument/Gaussian.lean#L96) (admitted)
- [35.7.E8](https://dlmf.nist.gov/35.7.E8): [`DLMF.MatrixArgument.hyp2F1_reflection`](DLMF/MatrixArgument/Gaussian.lean#L106) (admitted). **Corrected**: the condition `½(j+1) - a ∈ ℕ` for some `j` must be `a ∈ {0, -1, -2, …}` (`j = 1`); fails for `m = 2`, `a = ±1/2`.
- [35.7.E9](https://dlmf.nist.gov/35.7.E9): [`DLMF.MatrixArgument.gaussPDEOperator`](DLMF/MatrixArgument/Basic.lean#L333) (definition); [`DLMF.MatrixArgument.hyp2F1_gaussPDE`](DLMF/MatrixArgument/Gaussian.lean#L121) (admitted). `gaussPDEOperator` is the operator minus `abF`; the theorem gives real analyticity on `|t_k| < 1` and the equations at distinct `t_k`.
- [35.7.E10](https://dlmf.nist.gov/35.7.E10): Not formalized: the display names the functions whose uniform asymptotics (Butler and Wood 2002) DLMF cites but does not state.
- [35.7.E11](https://dlmf.nist.gov/35.7.E11): Not formalized: as 35.7.E10.
- [35.7.iii](https://dlmf.nist.gov/35.7.iii): [`DLMF.MatrixArgument.eq_hyp2F1_of_gaussPDE`](DLMF/MatrixArgument/Gaussian.lean#L133) (admitted). The uniqueness statement of 35.7.iii.p1 (conditions (a)–(c)); 35.7.iii.p2 (systems for `₀F₁`, `₁F₁` by confluence) is a remark without a separate statement.
- [35.7.iv](https://dlmf.nist.gov/35.7.iv): No statement (references only).

## [§35.8 Generalized Hypergeometric Functions of Matrix Argument](https://dlmf.nist.gov/35.8)

- [35.8.i](https://dlmf.nist.gov/35.8.i): [`DLMF.MatrixArgument.hypergeometricPFQ_eq_sum_of_neg_nat`](DLMF/MatrixArgument/Generalized.lean#L106) (proved); [`DLMF.MatrixArgument.hypergeometricPFQ_summable_of_le`](DLMF/MatrixArgument/Generalized.lean#L139) (admitted); [`DLMF.MatrixArgument.hypergeometricPFQ_summable_of_eq_succ`](DLMF/MatrixArgument/Generalized.lean#L153) (admitted); [`DLMF.MatrixArgument.not_summable_hypergeometricPFQ_of_eq_succ`](DLMF/MatrixArgument/Generalized.lean#L165) (admitted); [`DLMF.MatrixArgument.not_summable_hypergeometricPFQ_of_lt`](DLMF/MatrixArgument/Generalized.lean#L176) (admitted). Paragraphs 35.8.Px1.p1–p4. **Corrected** p1: termination only when some `a_j` is a nonpositive integer (DLMF: `-a_j + (k+1)/2 ∈ ℕ` for some `k ≤ m`; false for `k ≥ 2`, e.g. `m = 2`, `a = 1/2`). Divergence (p3, p4) is stated for the absolute series, with non-termination as hypothesis.
- [35.8.E1](https://dlmf.nist.gov/35.8.E1): [`DLMF.MatrixArgument.hypergeometricPFQ`](DLMF/MatrixArgument/Basic.lean#L221) (definition)
- [35.8.E2](https://dlmf.nist.gov/35.8.E2): [`DLMF.MatrixArgument.hyp0F0_eq_etr`](DLMF/MatrixArgument/Generalized.lean#L214) (admitted)
- [35.8.E3](https://dlmf.nist.gov/35.8.E3): [`DLMF.MatrixArgument.hyp2F1_self_right`](DLMF/MatrixArgument/Generalized.lean#L220) (proved); [`DLMF.MatrixArgument.hyp1F0_eq_det_cpow`](DLMF/MatrixArgument/Generalized.lean#L234) (admitted). First equality proved (`Γ_m(b) ≠ 0`); second admitted (`0 < T < I`).
- [35.8.E4](https://dlmf.nist.gov/35.8.E4): [`DLMF.MatrixArgument.besselA_eq_hyp0F1`](DLMF/MatrixArgument/Generalized.lean#L240) (proved)
- [35.8.E5](https://dlmf.nist.gov/35.8.E5): [`DLMF.MatrixArgument.hyp3F2_one_kummer`](DLMF/MatrixArgument/Generalized.lean#L258) (admitted). Added hypotheses: `ℜ(b₂ - a₃) > (m-1)/2` (convergence of the right side) and regularity of the denominators.
- [35.8.E6](https://dlmf.nist.gov/35.8.E6): [`DLMF.MatrixArgument.hyp3F2_one_saalschutz`](DLMF/MatrixArgument/Generalized.lean#L274) (admitted). **Corrected**: DLMF prints the reciprocal of the right-hand side (already wrong for `m = 1`, cf. 16.4.3).
- [35.8.E7](https://dlmf.nist.gov/35.8.E7): [`DLMF.MatrixArgument.hyp3F2_one_thomae`](DLMF/MatrixArgument/Generalized.lean#L294) (admitted). **Corrected**: upper parameter `b₂ - a₁` (DLMF: `b₂ - a₂`) and `Γ_m(c)`, `Γ_m(c + a₃)` (DLMF: `Γ(c)`, `Γ(c + a₃)`); added `ℜa₁ > (m-1)/2` (convergence of the right side).
- [35.8.E8](https://dlmf.nist.gov/35.8.E8): [`DLMF.MatrixArgument.hypergeometricPFQ_zero`](DLMF/MatrixArgument/Generalized.lean#L188) (proved)
- [35.8.E9](https://dlmf.nist.gov/35.8.E9): [`DLMF.MatrixArgument.tendsto_hypergeometricPFQ_snoc`](DLMF/MatrixArgument/Generalized.lean#L317) (admitted). Real `γ → +∞`, `p ≤ q`.
- [35.8.E10](https://dlmf.nist.gov/35.8.E10): [`DLMF.MatrixArgument.tendsto_hypergeometricPFQ_snoc_denom`](DLMF/MatrixArgument/Generalized.lean#L327) (admitted). Real `γ → +∞`; `p ≤ q`, or `p = q + 1` with `‖T‖ < 1`.
- [35.8.E11](https://dlmf.nist.gov/35.8.E11): [`DLMF.MatrixArgument.hypergeometricPFQ_conj`](DLMF/MatrixArgument/Generalized.lean#L203) (proved)
- [35.8.E12](https://dlmf.nist.gov/35.8.E12): [`DLMF.MatrixArgument.hasIntegralOn_hypergeometricPFQ_laplace`](DLMF/MatrixArgument/Generalized.lean#L338) (admitted). Restricted to `p < q`, or `p = q` with `T > I` (where both series converge).
- [35.8.E13](https://dlmf.nist.gov/35.8.E13): [`DLMF.MatrixArgument.hasIntegralOn_hypergeometricPFQ_euler`](DLMF/MatrixArgument/Generalized.lean#L354) (admitted). **Corrected**: the factor is `B_m(b₁ - a₁, a₁)`, not its reciprocal. `pFq(TX)` written `pFq(X^{1/2}TX^{1/2})`; `p ≤ q`, or `p = q + 1` with `‖T‖ < 1`.
- [35.8.v](https://dlmf.nist.gov/35.8.v): No statement (references only: Mellin–Barnes integrals of Ding et al. 1996, Faraut and Korányi 1994).

## [§§35.9–35.12](https://dlmf.nist.gov/35.9) and other prose, informal and excluded items

- 35.1.p5 (alternative notations of other authors) and the reference-only subsections
  35.4.i.p4, 35.5.iii, 35.6.iv, 35.7.iv, 35.8.v: no statement.
- 35.7.iii.p2 (remark that the system of 35.7.9 can be used for asymptotics and computation):
  no statement.
- [§35.9 Applications](https://dlmf.nist.gov/35.9): excluded: application (densities of
  random-matrix distributions in multivariate statistics expressed by `pFq` with `p ≤ 2`,
  `q ≤ 1`, and uses of 35.4.7, 35.5.3, 35.5.8; no new formulas).
- [§35.10 Methods of Computation](https://dlmf.nist.gov/35.10): excluded: computation (summing
  35.8.1 by recursion on partitions, quadrature, the Koev–Edelman algorithm).
- [§35.11 Tables](https://dlmf.nist.gov/35.11): excluded: numerical.
- [§35.12 Software](https://dlmf.nist.gov/35.12): excluded: software.

## Validation

- The seven modules build with `lake build DLMF.MatrixArgument.<Module>` and each passes
  `lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false` without errors (`Basic`
  without admissions). There are no axioms, no `native_decide`, and no `sorry` in definitions
  or helper declarations (prefix `m35_`). No line exceeds 100 characters.
- `#print axioms` for the proved theorems `multivariateGamma_ofReal`,
  `multivariateGammaVec_add_div`, `zonalPolynomial_one`, `zonalPolynomial_eq_dlmf`,
  `zonalPolynomial_zero`, `zonalPolynomial_conj`, `zonalPolynomial_smul`,
  `zonalPolynomial_fin_one`, `hypergeometricPFQ_zero`, `hypergeometricPFQ_conj`,
  `hypergeometricPFQ_eq_sum_of_neg_nat`, `hyp2F1_self_right`, `besselA_eq_hyp0F1`,
  `besselA_zero`, `hyp2F1_fin_one`, `hyp1F1_fin_one`, `hyp2F1_eq_tsum`,
  `isMulRightInvariant_orthogonalHaar` shows only `propext`, `Classical.choice` and
  `Quot.sound`.
- Numerical checks (mpmath, scipy, numpy; scripts kept outside the repository): for `m = 2`
  with exact zonal polynomials, 35.4.6 (`k ≤ 5`), 35.6.7, 35.7.3, 35.7.6 (all three forms),
  35.7.7 (terminating and non-terminating), 35.7.8, 35.8.2, 35.8.3, 35.8.5, and the corrected
  35.8.6, 35.8.7; by Monte Carlo over Wishart samples (`m = 2`) 35.4.8 and 35.5.4; for `m = 1` against mpmath (Bessel `J`, `K`, Kummer `M`,
  Tricomi `U`, `₂F₁`, quadrature) 35.5.5, 35.5.7, 35.6.5, 35.6.6, 35.6.8, 35.6.9, 35.6.10,
  35.7.4 and the corrected 35.8.13.
- DLMF.lean, the umbrella `DLMF/MatrixArgument.lean`, the lakefile and the other ledgers are
  unchanged.
