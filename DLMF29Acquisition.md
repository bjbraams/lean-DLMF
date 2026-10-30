# DLMF Chapter 29 acquisition: Lamé Functions

> Source paths and current layout notes were refreshed on 2026-10-30; generated per-entry
> statuses follow the compiled ledger refresh. Dated acquisition and proof counts
> describe their original batches.

This acquisition covers the definitions, numbered formulas and analytical assertions in prose
of [DLMF Chapter 29](https://dlmf.nist.gov/29), §§29.1–29.17, version 1.2.8, checked on
2026-10-26 (agent ACQ29). The graphics sections §29.4 and §29.13 are excluded; the
applications §§29.18–29.19 are excluded: application, and §§29.20–29.22 excluded:
computation. The Lean code is in `DLMF/Lame/` (namespace `DLMF.Lame`, helper prefix `l29_`);
the modules, in import order, are
[Basic](DLMF/Lame/Basic.lean) (definitions for §§29.2–29.3, 29.6, 29.7, 29.9, 29.11),
[Polynomials/Basic](DLMF/Lame/Polynomials/Basic.lean) (definitions for §§29.12, 29.14, 29.15),
[Eigenvalues](DLMF/Lame/Eigenvalues.lean) (§§29.3, 29.9),
[DifferentialEquations](DLMF/Lame/DifferentialEquations.lean) (§§29.2, 29.10, 29.11),
[FourierSeries](DLMF/Lame/FourierSeries.lean) (§29.6),
[SpecialCases](DLMF/Lame/SpecialCases.lean) (§29.5),
[Asymptotics](DLMF/Lame/Asymptotics.lean) (§29.7),
[IntegralEquations](DLMF/Lame/IntegralEquations.lean) (§29.8),
[Polynomials/Series](DLMF/Lame/Polynomials/Series.lean) (§§29.12, 29.15),
[Polynomials/Orthogonality](DLMF/Lame/Polynomials/Orthogonality.lean) (§29.14) and
[OtherSolutions](DLMF/Lame/OtherSolutions.lean) (§29.17).

**Current layout (2026-10-30).**
`DLMF.Lame.Basic` exports `Basic.Equations`, `Basic.SpectralData` and
`Basic.RecurrenceData`. These leaves use the canonical Jacobi, Weierstrass and real-amplitude
foundations. The polynomial definitions are in `DLMF.Lame.Polynomials.Basic` and require
Mathlib's matrix characteristic-polynomial API. The theorem modules listed above import
existence, elliptic-function, Heun, Mathieu and Legendre results explicitly as needed;
`SpecialCases`, for example, uses `DLMF.Elliptic.Jacobi` and
`DLMF.Mathieu.SpectralExistence`. Neither Mathlib nor TauCeti has Lamé functions, so there
are no upstream Lamé pointers.

**Status after proof round 1 (2026-10-26).** Direct admissions in DLMF/Lame fell from 128 to 104. Proved: all sixteen Fourier-coefficient recurrences of 29.6, Table 29.12.1, the algebraic and imaginary-period forms (29.2.2–3, 29.10.4) and the classification of singular points. Many results are proved only from the flagged existence theorems; see REVIEW.md, "Proof round 1 for Chapters 28–31 (2026-10-26)".

**Status after proof round 2 (2026-10-26).** Direct admissions in DLMF/Lame fell from 104 to 44. Proved: the Lamé eigenvalue and eigenfunction existence `Real.lameEigenvalue_spec`/`lameEigenfunction_spec` (separated Sturm–Liouville theory), so the eigenvalues, eigenfunctions, normalization 29.3.18 and parities are fully proved; the zero counts (Table 29.3.2) and the interlacing 29.3.1–4; all Fourier expansions, normalizations, Parseval sums and positivity results of 29.6 except the ratio limits; the k = 0 results 29.5.1–3; the imaginary-axis form 29.10.1–3; the Lamé polynomials: distinct real eigenvalues 29.15.3, the polynomial form of Table 29.12.1, that they solve Lamé's equation, their identification with Ec/Es 29.12.1–8 and the eigenvalue identifications of the 29.15.7 family, and the orthogonality 29.14.1–11. See REVIEW.md, "Proof round 2 for Chapters 28–31 (2026-10-26)".

**Counts.** §§29.2–29.17 have 208 numbered items; §29.1 is notation only and §§29.4, 29.13
are graphics (no numbered formulas). Excluded: the ten equations 29.18.E1–29.18.E10
(application). In scope: 198 numbered items (195 equations and the tables 29.3.T1, 29.3.T2,
29.12.T1); all 198 are covered. In addition 14 prose IDs (29.2.i, 29.2.ii, 29.3.i, 29.3.iii,
29.3.iv, 29.3.v, 29.6.i, 29.7.i, 29.9, 29.10, 29.11, 29.12.i, 29.12.iii, 29.15.ii) carry tags.
212 DLMF IDs are tagged on 198 declarations: 39 definitions, 14 proved, 17 proved from
admissions and 128 admitted. The eleven modules hold 236 declarations in all: 61 definitions
(36 in Basic, 25 in Polynomials/Basic, counting structures and inductives), 27 proved, 20
proved from admissions and 128 admitted (`sorry` count per file: Basic 0, Polynomials/Basic 0,
Eigenvalues 21, DifferentialEquations 8, FourierSeries 49, SpecialCases 13, Asymptotics 3,
IntegralEquations 5, Polynomials/Series 24, Polynomials/Orthogonality 4, OtherSolutions 1).

## Domains, conventions and source corrections

- **Modulus.** DLMF writes `k²` as the second argument (`Ec^m_ν(z, k²)`, `a^m_ν(k²)`); the
  Lean functions take the modulus `k` itself (`Real.lameEck ν m x k`, `Real.lameAk ν m k`).
  `K = Real.compEllIntKm (k ^ 2)`, `K' = Real.compEllIntKm (1 - k ^ 2)`; the complex `sn` is
  `DLMF.JacobiElliptic.jacobiSnk z k` and the real one `Real.jacobiSnm x (k ^ 2)` (they agree,
  `jacobiSnk_ofReal`). DLMF assumes `0 < k < 1`, `ν ≥ -1/2`; every theorem carries these
  hypotheses where needed, while the predicates are stated for all parameters.
- **Lamé functions of §29.3 are real-variable functions.** The eigenvalue problems of
  §29.3(i) are boundary problems on `[0, K]` with the parity conditions of Table 29.3.1
  (`Real.LameBoundary`). `Real.lameEigenvalue` is defined by choice as the `j`th eigenvalue if
  it exists uniquely (junk `0` otherwise), and `Real.lameEigenfunction` as a chosen eigenfunction
  normalized by 29.3.18 with the sign rule of §29.3(v). Existence, simplicity and uniqueness are
  the two flagged admitted existence theorems `Real.lameEigenvalue_spec` and
  `Real.lameEigenfunction_spec` (regular Sturm–Liouville theory); everything about `lameEck`,
  `lameEsk` "proved from admissions" depends only on these two (and, where noted, on the
  admitted Fourier and orthogonality statements). `a^m_ν = Real.lameAk ν m k` and
  `b^m_ν = Real.lameBk ν m k` are the eigenvalues of the matching parity class.
- **Fourier coefficients (§29.6).** The coefficients `A_p, B_p, C_p, D_p` are the Fourier
  integrals `Real.lameCosCoeff`/`Real.lameSinCoeff` (weighted by `dn` for the `C`, `D` series)
  of the Lamé functions in `φ = π/2 - am(x, k)`; the recurrences 29.6.3–29.6.4 etc. are theorems
  about these integrals with the coefficients `α_p, β_p, γ_p` of `LameRecurrence` (tagged
  29.3.11–29.3.17 and 29.6.11, 29.6.26, 29.6.41, 29.6.56).
- **29.3.10** (continued fractions) is stated for non-integer `ν` with nonvanishing partial
  denominators; for integer `ν` the terminating case is a separate statement (29.3.iii).
- **§29.2(ii) Heun form.** DLMF identifies 29.2.10 with Heun's equation 31.2.1; the proved
  statement is the equivalent identification of the algebraic form 29.2.2 (`a = k⁻²`,
  `q = -hk⁻²/4`, `α = -ν/2`, `β = (ν+1)/2`, `γ = δ = ε = ½`).
- **29.8 kernel (convention correction).** DLMF writes the Ferrers function `𝖯_ν`, but the
  argument `y = dn(z, k) dn(z₁, k)/k'` of 29.8.6 ranges over `[k', 1/k']`, which straddles `1`,
  and `x` of 29.8.1 is likewise not confined to `[-1, 1]`. The function meant is
  `F(-ν, ν+1; 1; (1 - x)/2)`, i.e. the Legendre function `P_ν` (equal to `𝖯_ν` on `(-1, 1)`);
  the Lean statements use `DLMF.Legendre.legendreP ν`. With this reading 29.8.2, 29.8.5 and
  29.8.7–29.8.9 were confirmed numerically (ratios `1 ± 10⁻¹²`, `ν = 2.7`, `k = 0.6`). This is
  a notational imprecision rather than an erratum and has not been added to the errata report (reports/DLMFErrata.tex).
- **Lamé polynomials (§§29.12–29.15).** The eight types are defined directly by their
  Chebyshev series 29.15.43–29.15.50 (`lamePolyEk t n m z k`, complex `z`), with the
  coefficients of the finite tridiagonal eigenvalue problem 29.15.2 (eigenvalue `H_m` the `m`th
  sorted root of the characteristic polynomial, eigenvector by forward recursion, normalized by
  29.15.5/10/…/40 and the sign rules 29.15.6/11/…/41). No choice is involved. The identification
  with `Ec`, `Es` (29.12.1–29.12.8) and of `½(H_m + ν(ν+1)k²)` with the eigenvalues (29.15.7,
  …, 29.15.42) are admitted; the finite Fourier series 29.15.1, 29.15.8, …, 29.15.38 are
  proved. The inner product 29.14.2 has no conjugation, as in DLMF.
- **29.12.9.** The branches of `ξ^ρ(ξ - 1)^σ(ξ - k⁻²)^τ` are avoided by stating the
  equivalent polynomial form `sn^a cn^b dn^c P(sn²)` of Table 29.12.1.
- **29.17.1.** The base point `iK'` is a pole of `E`; the integral is taken along the segment
  from `iK'` and the statement is local on an open set avoiding zeros of `E`.
- **No DLMF errata were found.** Numerically checked (scripts in the agent scratchpad,
  mpmath): matrix eigenvalues of all eight recurrences against ODE shooting with the boundary
  and parity assignments; the interlacing 29.3.1–29.3.6; 29.3.5, 29.3.7, 29.3.8 for `ν = 3, 4`;
  `τ₀–τ₃` of 29.7 (remainder times `κ³ → -τ₃`); all eight polynomial types solve 29.2.1 with
  `h = ½(H + ν(ν+1)k²)`, satisfy the normalization `π/4` and the sign rules, and have `m` zeros
  in `(0, K)`; 29.6.15, 29.3.18, 29.6.7; the equilibrium 29.12.13; the orthogonality 29.14;
  the identity `k'² sn²(i(z - K - iK'), k') = 1 - k² sn²(z, k)` behind 29.10; the limits
  29.5.4–29.5.6; the Mathieu limit of the eigenvalues (`h → a_m(θ) + 2θ`, 29.5.7); 29.8.

## Numbered formulas and prose items

## [§29.2 Differential Equations](https://dlmf.nist.gov/29.2)

- [29.2.i](https://dlmf.nist.gov/29.2.i): [`DLMF.Lame.lame_regularSingularAt`](DLMF/Lame/DifferentialEquations.lean#L109) (proved); [`DLMF.Lame.lame_ordinaryAt`](DLMF/Lame/DifferentialEquations.lean#L178) (proved).
- [29.2.ii](https://dlmf.nist.gov/29.2.ii): [`DLMF.Lame.isLameAlgebraicSolutionOn_iff_isHeunSolOn`](DLMF/Lame/DifferentialEquations.lean#L395) (proved). DLMF identifies 29.2.10 with Heun’s equation; the proved bridge is stated for the equivalent algebraic form 29.2.2 (Heun parameters `a = k⁻²`, `q = -h/4 · k⁻²`, `α = -ν/2`, `β = (ν+1)/2`, `γ = δ = ε = ½`).
- [29.2.E1](https://dlmf.nist.gov/29.2.E1): [`DLMF.Lame.IsLameSolutionOn`](DLMF/Lame/Basic/Equations.lean#L26) (definition); [`DLMF.Lame.Real.IsLameSolution`](DLMF/Lame/Basic/Equations.lean#L82) (definition). `IsLameSolutionOn` is the complex equation on an open set (all complex parameters); `Real.IsLameSolution` the real form used for the eigenvalue problems.
- [29.2.E2](https://dlmf.nist.gov/29.2.E2): [`DLMF.Lame.IsLameAlgebraicSolutionOn`](DLMF/Lame/Basic/Equations.lean#L38) (definition); [`DLMF.Lame.isLameSolutionOn_comp_sn_sq`](DLMF/Lame/DifferentialEquations.lean#L203) (proved). Algebraic form as a predicate; the transfer to 29.2.1 via `ξ = sn²` is admitted.
- [29.2.E3](https://dlmf.nist.gov/29.2.E3): [`DLMF.Lame.isLameSolutionOn_comp_sn_sq`](DLMF/Lame/DifferentialEquations.lean#L203) (proved).
- [29.2.E4](https://dlmf.nist.gov/29.2.E4): [`DLMF.Lame.Real.IsLameTrigSolution`](DLMF/Lame/Basic/Equations.lean#L93) (definition); [`DLMF.Lame.Real.isLameSolution_comp_lamePhi`](DLMF/Lame/DifferentialEquations.lean#L264) (proved). Trigonometric form; the transfer `W ↦ W ∘ φ` to 29.2.1 is proved.
- [29.2.E5](https://dlmf.nist.gov/29.2.E5): [`DLMF.Lame.Real.lamePhi`](DLMF/Lame/Basic/Equations.lean#L106) (definition); [`DLMF.Lame.Real.isLameSolution_comp_lamePhi`](DLMF/Lame/DifferentialEquations.lean#L264) (proved).
- [29.2.E6](https://dlmf.nist.gov/29.2.E6): [`DLMF.Lame.isLameWeierstrassSolutionOn_of_isLameSolutionOn`](DLMF/Lame/DifferentialEquations.lean#L296) (proved).
- [29.2.E7](https://dlmf.nist.gov/29.2.E7): [`DLMF.Lame.isLameWeierstrassSolutionOn_of_isLameSolutionOn`](DLMF/Lame/DifferentialEquations.lean#L296) (proved).
- [29.2.E8](https://dlmf.nist.gov/29.2.E8): [`DLMF.Lame.isLameWeierstrassSolutionOn_of_isLameSolutionOn`](DLMF/Lame/DifferentialEquations.lean#L296) (proved).
- [29.2.E9](https://dlmf.nist.gov/29.2.E9): [`DLMF.Lame.IsLameWeierstrassSolutionOn`](DLMF/Lame/Basic/Equations.lean#L49) (definition); [`DLMF.Lame.isLameWeierstrassSolutionOn_of_isLameSolutionOn`](DLMF/Lame/DifferentialEquations.lean#L296) (proved). Weierstrass form with `℘(z; g₂, g₃)` of `DLMF.Weierstrass`; transfer admitted.
- [29.2.E10](https://dlmf.nist.gov/29.2.E10): [`DLMF.Lame.IsLameWeierstrassAlgebraicSolutionOn`](DLMF/Lame/Basic/Equations.lean#L60) (definition); [`DLMF.Lame.isLameWeierstrassSolutionOn_comp_wp`](DLMF/Lame/DifferentialEquations.lean#L313) (proved).
- [29.2.E11](https://dlmf.nist.gov/29.2.E11): [`DLMF.Lame.isLameWeierstrassSolutionOn_comp_wp`](DLMF/Lame/DifferentialEquations.lean#L313) (proved).
- [29.2.E12](https://dlmf.nist.gov/29.2.E12): [`DLMF.Lame.isLameWeierstrassSolutionOn_of_isLameSolutionOn`](DLMF/Lame/DifferentialEquations.lean#L296) (proved).

## [§29.3 Definitions and Basic Properties](https://dlmf.nist.gov/29.3)

- [29.3.i](https://dlmf.nist.gov/29.3.i): [`DLMF.Lame.Real.lameAk`](DLMF/Lame/Basic/SpectralData.lean#L52) (definition); [`DLMF.Lame.Real.lameBk`](DLMF/Lame/Basic/SpectralData.lean#L57) (definition); [`DLMF.Lame.Real.lameEigenvalue_spec`](DLMF/Lame/Eigenvalues.lean#L95) (proved). Eigenvalues by choice: `lameEigenvalue` is the `j`th eigenvalue of the boundary problem with the parity conditions of Table 29.3.1 if it exists uniquely (existence and simplicity: the flagged admitted theorem `lameEigenvalue_spec`, regular Sturm–Liouville theory).
- [29.3.iii](https://dlmf.nist.gov/29.3.iii): [`DLMF.Lame.Real.lameCF_A1`](DLMF/Lame/Eigenvalues.lean#L990) (admitted); [`DLMF.Lame.Real.lameCF_B1`](DLMF/Lame/Eigenvalues.lean#L1001) (admitted); [`DLMF.Lame.Real.lameCF_B2`](DLMF/Lame/Eigenvalues.lean#L1012) (admitted); [`DLMF.Lame.Real.lameCF_A0_terminating`](DLMF/Lame/Eigenvalues.lean#L1023) (admitted).
- [29.3.iv](https://dlmf.nist.gov/29.3.iv): [`DLMF.Lame.Real.lameEck`](DLMF/Lame/Basic/SpectralData.lean#L81) (definition); [`DLMF.Lame.Real.lameEsk`](DLMF/Lame/Basic/SpectralData.lean#L87) (definition); [`DLMF.Lame.Real.lameEck_isLameEigenfunction`](DLMF/Lame/Eigenvalues.lean#L359) (proved); [`DLMF.Lame.Real.lameEsk_isLameEigenfunction`](DLMF/Lame/Eigenvalues.lean#L368) (proved); [`DLMF.Lame.Real.lameEck_zeros_Ioo`](DLMF/Lame/Eigenvalues.lean#L826) (proved); [`DLMF.Lame.Real.lameEsk_zeros_Ioo`](DLMF/Lame/Eigenvalues.lean#L834) (proved); [`DLMF.Lame.Real.lameEck_zeros_Ico`](DLMF/Lame/Eigenvalues.lean#L843) (proved); [`DLMF.Lame.Real.lameEsk_zeros_Ico`](DLMF/Lame/Eigenvalues.lean#L869) (proved). `lameEck`/`lameEsk` are chosen normalized eigenfunctions (existence and uniqueness: flagged admitted `lameEigenfunction_spec`).
- [29.3.v](https://dlmf.nist.gov/29.3.v): [`DLMF.Lame.Real.lameEigenfunction_spec`](DLMF/Lame/Eigenvalues.lean#L158) (proved); [`DLMF.Lame.Real.lameEck_K_pos`](DLMF/Lame/Eigenvalues.lean#L392) (proved); [`DLMF.Lame.Real.lameEsk_deriv_K_neg`](DLMF/Lame/Eigenvalues.lean#L400) (proved).
- [29.3.E1](https://dlmf.nist.gov/29.3.E1): [`DLMF.Lame.Real.lameAk_lt_lameAk_succ`](DLMF/Lame/Eigenvalues.lean#L899) (proved).
- [29.3.E2](https://dlmf.nist.gov/29.3.E2): [`DLMF.Lame.Real.lameAk_lt_lameBk_succ`](DLMF/Lame/Eigenvalues.lean#L914) (proved).
- [29.3.E3](https://dlmf.nist.gov/29.3.E3): [`DLMF.Lame.Real.lameBk_lt_lameBk_succ`](DLMF/Lame/Eigenvalues.lean#L923) (proved).
- [29.3.E4](https://dlmf.nist.gov/29.3.E4): [`DLMF.Lame.Real.lameBk_lt_lameAk_succ`](DLMF/Lame/Eigenvalues.lean#L938) (proved).
- [29.3.E5](https://dlmf.nist.gov/29.3.E5): [`DLMF.Lame.Real.lameAk_eq_lameBk`](DLMF/Lame/Eigenvalues.lean#L946) (admitted).
- [29.3.E6](https://dlmf.nist.gov/29.3.E6): [`DLMF.Lame.Real.lameAk_sub_lameBk_mul_pos`](DLMF/Lame/Eigenvalues.lean#L952) (admitted).
- [29.3.E7](https://dlmf.nist.gov/29.3.E7): [`DLMF.Lame.Real.lameAk_add_lameAk_comodulus`](DLMF/Lame/Eigenvalues.lean#L960) (admitted). `a^m_n(k²) + a^{n-m}_n(k'²) = n(n+1)` for integer `n` and `m ≤ n` (modulus argument `k'`); checked numerically.
- [29.3.E8](https://dlmf.nist.gov/29.3.E8): [`DLMF.Lame.Real.lameBk_add_lameBk_comodulus`](DLMF/Lame/Eigenvalues.lean#L967) (admitted). As 29.3.E7 for `b`; checked numerically.
- [29.3.E9](https://dlmf.nist.gov/29.3.E9): [`DLMF.Lame.Real.lameCF_A0`](DLMF/Lame/Eigenvalues.lean#L977) (admitted).
- [29.3.E10](https://dlmf.nist.gov/29.3.E10): [`DLMF.Lame.lameCFLeft`](DLMF/Lame/Basic/RecurrenceData.lean#L93) (definition); [`DLMF.Lame.lameCFRight`](DLMF/Lame/Basic/RecurrenceData.lean#L100) (definition); [`DLMF.Lame.Real.lameCF_A0`](DLMF/Lame/Eigenvalues.lean#L977) (admitted); [`DLMF.Lame.Real.lameCF_A1`](DLMF/Lame/Eigenvalues.lean#L990) (admitted); [`DLMF.Lame.Real.lameCF_B1`](DLMF/Lame/Eigenvalues.lean#L1001) (admitted); [`DLMF.Lame.Real.lameCF_B2`](DLMF/Lame/Eigenvalues.lean#L1012) (admitted). Stated for non-integer `ν` (for integer `ν` the left-hand side can terminate, see the terminating case under 29.3.iii) and with nonvanishing partial denominators.
- [29.3.E11](https://dlmf.nist.gov/29.3.E11): [`DLMF.Lame.LameRecurrence.alpha`](DLMF/Lame/Basic/RecurrenceData.lean#L34) (definition).
- [29.3.E12](https://dlmf.nist.gov/29.3.E12): [`DLMF.Lame.LameRecurrence.beta`](DLMF/Lame/Basic/RecurrenceData.lean#L50) (definition); [`DLMF.Lame.LameRecurrence.gamma`](DLMF/Lame/Basic/RecurrenceData.lean#L68) (definition).
- [29.3.E13](https://dlmf.nist.gov/29.3.E13): [`DLMF.Lame.LameRecurrence.beta`](DLMF/Lame/Basic/RecurrenceData.lean#L50) (definition).
- [29.3.E14](https://dlmf.nist.gov/29.3.E14): [`DLMF.Lame.LameRecurrence.alpha`](DLMF/Lame/Basic/RecurrenceData.lean#L34) (definition); [`DLMF.Lame.LameRecurrence.gamma`](DLMF/Lame/Basic/RecurrenceData.lean#L68) (definition).
- [29.3.E15](https://dlmf.nist.gov/29.3.E15): [`DLMF.Lame.LameRecurrence.beta`](DLMF/Lame/Basic/RecurrenceData.lean#L50) (definition).
- [29.3.E16](https://dlmf.nist.gov/29.3.E16): [`DLMF.Lame.LameRecurrence.alpha`](DLMF/Lame/Basic/RecurrenceData.lean#L34) (definition); [`DLMF.Lame.LameRecurrence.gamma`](DLMF/Lame/Basic/RecurrenceData.lean#L68) (definition).
- [29.3.E17](https://dlmf.nist.gov/29.3.E17): [`DLMF.Lame.LameRecurrence.alpha`](DLMF/Lame/Basic/RecurrenceData.lean#L34) (definition); [`DLMF.Lame.LameRecurrence.beta`](DLMF/Lame/Basic/RecurrenceData.lean#L50) (definition); [`DLMF.Lame.LameRecurrence.gamma`](DLMF/Lame/Basic/RecurrenceData.lean#L68) (definition).
- [29.3.E18](https://dlmf.nist.gov/29.3.E18): [`DLMF.Lame.Real.lameEck_normalization`](DLMF/Lame/Eigenvalues.lean#L376) (proved); [`DLMF.Lame.Real.lameEsk_normalization`](DLMF/Lame/Eigenvalues.lean#L384) (proved).
- [29.3.E19](https://dlmf.nist.gov/29.3.E19): [`DLMF.Lame.Real.lameEck_even_orthogonal`](DLMF/Lame/Eigenvalues.lean#L1049) (proved); [`DLMF.Lame.Real.lameEck_odd_orthogonal`](DLMF/Lame/Eigenvalues.lean#L1058) (proved); [`DLMF.Lame.Real.lameEsk_odd_orthogonal`](DLMF/Lame/Eigenvalues.lean#L1067) (proved); [`DLMF.Lame.Real.lameEsk_even_orthogonal`](DLMF/Lame/Eigenvalues.lean#L1076) (proved). The general orthogonality on `(0, K)` (Green’s identity, `l29_integral_mul_eq_zero`) is proved; the four parity cases follow from the admitted existence theorems.
- [29.3.T1](https://dlmf.nist.gov/29.3.T1): [`DLMF.Lame.Real.lameEck_parity`](DLMF/Lame/Eigenvalues.lean#L458) (proved); [`DLMF.Lame.Real.lameEsk_parity`](DLMF/Lame/Eigenvalues.lean#L480) (proved). Parity of `Ec`, `Es` at `0` and `K` proved from the boundary conditions by ODE uniqueness (`l29_reflect`), given the admitted existence theorems.
- [29.3.T2](https://dlmf.nist.gov/29.3.T2): [`DLMF.Lame.Real.lameEck_parity`](DLMF/Lame/Eigenvalues.lean#L458) (proved); [`DLMF.Lame.Real.lameEsk_parity`](DLMF/Lame/Eigenvalues.lean#L480) (proved).

## [§29.5 Special Cases and Limiting Forms](https://dlmf.nist.gov/29.5)

- [29.5.E1](https://dlmf.nist.gov/29.5.E1): [`DLMF.Lame.Real.lameAk_zero`](DLMF/Lame/SpecialCases.lean#L485) (proved); [`DLMF.Lame.Real.lameBk_zero`](DLMF/Lame/SpecialCases.lean#L492) (proved).
- [29.5.E2](https://dlmf.nist.gov/29.5.E2): [`DLMF.Lame.Real.lameEck_zero_zero`](DLMF/Lame/SpecialCases.lean#L505) (proved).
- [29.5.E3](https://dlmf.nist.gov/29.5.E3): [`DLMF.Lame.Real.lameEck_modulus_zero`](DLMF/Lame/SpecialCases.lean#L514) (proved); [`DLMF.Lame.Real.lameEsk_modulus_zero`](DLMF/Lame/SpecialCases.lean#L525) (proved).
- [29.5.E4](https://dlmf.nist.gov/29.5.E4): [`DLMF.Lame.Real.tendsto_lameAk_one`](DLMF/Lame/SpecialCases.lean#L539) (admitted); [`DLMF.Lame.Real.tendsto_lameBk_one`](DLMF/Lame/SpecialCases.lean#L545) (admitted).
- [29.5.E5](https://dlmf.nist.gov/29.5.E5): [`DLMF.Lame.Real.tendsto_lameEck_div_one`](DLMF/Lame/SpecialCases.lean#L552) (admitted); [`DLMF.Lame.Real.tendsto_lameEsk_div_one`](DLMF/Lame/SpecialCases.lean#L563) (admitted).
- [29.5.E6](https://dlmf.nist.gov/29.5.E6): [`DLMF.Lame.Real.tendsto_lameEck_div_deriv_one`](DLMF/Lame/SpecialCases.lean#L573) (admitted); [`DLMF.Lame.Real.tendsto_lameEsk_div_deriv_one`](DLMF/Lame/SpecialCases.lean#L585) (admitted).
- [29.5.E7](https://dlmf.nist.gov/29.5.E7): [`DLMF.Lame.Real.tendsto_lameEck_mathieuCe`](DLMF/Lame/SpecialCases.lean#L597) (admitted); [`DLMF.Lame.Real.tendsto_lameEsk_mathieuSe`](DLMF/Lame/SpecialCases.lean#L608) (admitted).

## [§29.6 Fourier Series](https://dlmf.nist.gov/29.6)

- [29.6.i](https://dlmf.nist.gov/29.6.i): [`DLMF.Lame.Real.lameEck_even_fourierA_eq_zero`](DLMF/Lame/FourierSeries/EigenfunctionSeries.lean#L988) (admitted). For `ν = 2n` the coefficients `A_{2p}`, `p > n`, of `Ec^{2m}_{2n}` vanish (terminating series); admitted.
- [29.6.E1](https://dlmf.nist.gov/29.6.E1): [`DLMF.Lame.Real.lameEck_even_hasSum_fourierA`](DLMF/Lame/FourierSeries/CoefficientRecurrences.lean#L696) (proved).
- [29.6.E2](https://dlmf.nist.gov/29.6.E2): [`DLMF.Lame.Real.lameEck_even_fourierA_rec_zero`](DLMF/Lame/FourierSeries/CoefficientRecurrences.lean#L713) (proved).
- [29.6.E3](https://dlmf.nist.gov/29.6.E3): [`DLMF.Lame.Real.lameEck_even_fourierA_rec_zero`](DLMF/Lame/FourierSeries/CoefficientRecurrences.lean#L713) (proved).
- [29.6.E4](https://dlmf.nist.gov/29.6.E4): [`DLMF.Lame.Real.lameEck_even_fourierA_rec`](DLMF/Lame/FourierSeries/CoefficientRecurrences.lean#L734) (proved).
- [29.6.E5](https://dlmf.nist.gov/29.6.E5): [`DLMF.Lame.Real.lameEck_even_fourierA_normalization`](DLMF/Lame/FourierSeries/CoefficientRecurrences.lean#L763) (proved).
- [29.6.E6](https://dlmf.nist.gov/29.6.E6): [`DLMF.Lame.Real.lameEck_even_fourierA_pos`](DLMF/Lame/FourierSeries/CoefficientRecurrences.lean#L790) (proved).
- [29.6.E7](https://dlmf.nist.gov/29.6.E7): [`DLMF.Lame.Real.lameEck_even_fourierA_ratio`](DLMF/Lame/FourierSeries/CoefficientRecurrences.lean#L803) (admitted).
- [29.6.E8](https://dlmf.nist.gov/29.6.E8): [`DLMF.Lame.Real.lameEck_even_hasSum_fourierC`](DLMF/Lame/FourierSeries/CoefficientRecurrences.lean#L814) (proved).
- [29.6.E9](https://dlmf.nist.gov/29.6.E9): [`DLMF.Lame.Real.lameEck_even_fourierC_rec_zero`](DLMF/Lame/FourierSeries/CoefficientRecurrences.lean#L832) (proved).
- [29.6.E10](https://dlmf.nist.gov/29.6.E10): [`DLMF.Lame.Real.lameEck_even_fourierC_rec`](DLMF/Lame/FourierSeries/CoefficientRecurrences.lean#L852) (proved).
- [29.6.E11](https://dlmf.nist.gov/29.6.E11): [`DLMF.Lame.LameRecurrence.alpha`](DLMF/Lame/Basic/RecurrenceData.lean#L34) (definition); [`DLMF.Lame.LameRecurrence.beta`](DLMF/Lame/Basic/RecurrenceData.lean#L50) (definition); [`DLMF.Lame.LameRecurrence.gamma`](DLMF/Lame/Basic/RecurrenceData.lean#L68) (definition).
- [29.6.E12](https://dlmf.nist.gov/29.6.E12): [`DLMF.Lame.Real.lameEck_even_fourierC_normalization`](DLMF/Lame/FourierSeries/CoefficientRecurrences.lean#L880) (proved).
- [29.6.E13](https://dlmf.nist.gov/29.6.E13): [`DLMF.Lame.Real.lameEck_even_fourierC_pos`](DLMF/Lame/FourierSeries/CoefficientRecurrences.lean#L931) (proved).
- [29.6.E14](https://dlmf.nist.gov/29.6.E14): [`DLMF.Lame.Real.lameEck_even_fourierC_ratio`](DLMF/Lame/FourierSeries/CoefficientRecurrences.lean#L950) (admitted).
- [29.6.E15](https://dlmf.nist.gov/29.6.E15): [`DLMF.Lame.Real.lameEck_even_fourier_parseval`](DLMF/Lame/FourierSeries/EigenfunctionSeries.lean#L32) (proved).
- [29.6.E16](https://dlmf.nist.gov/29.6.E16): [`DLMF.Lame.Real.lameEck_odd_hasSum_fourierA`](DLMF/Lame/FourierSeries/EigenfunctionSeries.lean#L56) (proved).
- [29.6.E17](https://dlmf.nist.gov/29.6.E17): [`DLMF.Lame.Real.lameEck_odd_fourierA_rec_zero`](DLMF/Lame/FourierSeries/EigenfunctionSeries.lean#L73) (proved).
- [29.6.E18](https://dlmf.nist.gov/29.6.E18): [`DLMF.Lame.Real.lameEck_odd_fourierA_rec_zero`](DLMF/Lame/FourierSeries/EigenfunctionSeries.lean#L73) (proved).
- [29.6.E19](https://dlmf.nist.gov/29.6.E19): [`DLMF.Lame.Real.lameEck_odd_fourierA_rec`](DLMF/Lame/FourierSeries/EigenfunctionSeries.lean#L94) (proved).
- [29.6.E20](https://dlmf.nist.gov/29.6.E20): [`DLMF.Lame.Real.lameEck_odd_fourierA_normalization`](DLMF/Lame/FourierSeries/EigenfunctionSeries.lean#L123) (proved).
- [29.6.E21](https://dlmf.nist.gov/29.6.E21): [`DLMF.Lame.Real.lameEck_odd_fourierA_pos`](DLMF/Lame/FourierSeries/EigenfunctionSeries.lean#L150) (proved).
- [29.6.E22](https://dlmf.nist.gov/29.6.E22): [`DLMF.Lame.Real.lameEck_odd_fourierA_ratio`](DLMF/Lame/FourierSeries/EigenfunctionSeries.lean#L163) (admitted).
- [29.6.E23](https://dlmf.nist.gov/29.6.E23): [`DLMF.Lame.Real.lameEck_odd_hasSum_fourierC`](DLMF/Lame/FourierSeries/EigenfunctionSeries.lean#L174) (proved).
- [29.6.E24](https://dlmf.nist.gov/29.6.E24): [`DLMF.Lame.Real.lameEck_odd_fourierC_rec_zero`](DLMF/Lame/FourierSeries/EigenfunctionSeries.lean#L193) (proved).
- [29.6.E25](https://dlmf.nist.gov/29.6.E25): [`DLMF.Lame.Real.lameEck_odd_fourierC_rec`](DLMF/Lame/FourierSeries/EigenfunctionSeries.lean#L213) (proved).
- [29.6.E26](https://dlmf.nist.gov/29.6.E26): [`DLMF.Lame.LameRecurrence.alpha`](DLMF/Lame/Basic/RecurrenceData.lean#L34) (definition); [`DLMF.Lame.LameRecurrence.beta`](DLMF/Lame/Basic/RecurrenceData.lean#L50) (definition); [`DLMF.Lame.LameRecurrence.gamma`](DLMF/Lame/Basic/RecurrenceData.lean#L68) (definition).
- [29.6.E27](https://dlmf.nist.gov/29.6.E27): [`DLMF.Lame.Real.lameEck_odd_fourierC_normalization`](DLMF/Lame/FourierSeries/EigenfunctionSeries.lean#L241) (proved).
- [29.6.E28](https://dlmf.nist.gov/29.6.E28): [`DLMF.Lame.Real.lameEck_odd_fourierC_pos`](DLMF/Lame/FourierSeries/EigenfunctionSeries.lean#L289) (proved).
- [29.6.E29](https://dlmf.nist.gov/29.6.E29): [`DLMF.Lame.Real.lameEck_odd_fourierC_ratio`](DLMF/Lame/FourierSeries/EigenfunctionSeries.lean#L308) (admitted).
- [29.6.E30](https://dlmf.nist.gov/29.6.E30): [`DLMF.Lame.Real.lameEck_odd_fourier_parseval`](DLMF/Lame/FourierSeries/EigenfunctionSeries.lean#L319) (proved).
- [29.6.E31](https://dlmf.nist.gov/29.6.E31): [`DLMF.Lame.Real.lameEsk_odd_hasSum_fourierB`](DLMF/Lame/FourierSeries/EigenfunctionSeries.lean#L343) (proved).
- [29.6.E32](https://dlmf.nist.gov/29.6.E32): [`DLMF.Lame.Real.lameEsk_odd_fourierB_rec_zero`](DLMF/Lame/FourierSeries/EigenfunctionSeries.lean#L360) (proved).
- [29.6.E33](https://dlmf.nist.gov/29.6.E33): [`DLMF.Lame.Real.lameEsk_odd_fourierB_rec_zero`](DLMF/Lame/FourierSeries/EigenfunctionSeries.lean#L360) (proved).
- [29.6.E34](https://dlmf.nist.gov/29.6.E34): [`DLMF.Lame.Real.lameEsk_odd_fourierB_rec`](DLMF/Lame/FourierSeries/EigenfunctionSeries.lean#L381) (proved).
- [29.6.E35](https://dlmf.nist.gov/29.6.E35): [`DLMF.Lame.Real.lameEsk_odd_fourierB_normalization`](DLMF/Lame/FourierSeries/EigenfunctionSeries.lean#L410) (proved).
- [29.6.E36](https://dlmf.nist.gov/29.6.E36): [`DLMF.Lame.Real.lameEsk_odd_fourierB_pos`](DLMF/Lame/FourierSeries/EigenfunctionSeries.lean#L437) (proved).
- [29.6.E37](https://dlmf.nist.gov/29.6.E37): [`DLMF.Lame.Real.lameEsk_odd_fourierB_ratio`](DLMF/Lame/FourierSeries/EigenfunctionSeries.lean#L464) (admitted).
- [29.6.E38](https://dlmf.nist.gov/29.6.E38): [`DLMF.Lame.Real.lameEsk_odd_hasSum_fourierD`](DLMF/Lame/FourierSeries/EigenfunctionSeries.lean#L475) (proved).
- [29.6.E39](https://dlmf.nist.gov/29.6.E39): [`DLMF.Lame.Real.lameEsk_odd_fourierD_rec_zero`](DLMF/Lame/FourierSeries/EigenfunctionSeries.lean#L494) (proved).
- [29.6.E40](https://dlmf.nist.gov/29.6.E40): [`DLMF.Lame.Real.lameEsk_odd_fourierD_rec`](DLMF/Lame/FourierSeries/EigenfunctionSeries.lean#L514) (proved).
- [29.6.E41](https://dlmf.nist.gov/29.6.E41): [`DLMF.Lame.LameRecurrence.alpha`](DLMF/Lame/Basic/RecurrenceData.lean#L34) (definition); [`DLMF.Lame.LameRecurrence.beta`](DLMF/Lame/Basic/RecurrenceData.lean#L50) (definition); [`DLMF.Lame.LameRecurrence.gamma`](DLMF/Lame/Basic/RecurrenceData.lean#L68) (definition).
- [29.6.E42](https://dlmf.nist.gov/29.6.E42): [`DLMF.Lame.Real.lameEsk_odd_fourierD_normalization`](DLMF/Lame/FourierSeries/EigenfunctionSeries.lean#L542) (proved).
- [29.6.E43](https://dlmf.nist.gov/29.6.E43): [`DLMF.Lame.Real.lameEsk_odd_fourierD_pos`](DLMF/Lame/FourierSeries/EigenfunctionSeries.lean#L590) (proved).
- [29.6.E44](https://dlmf.nist.gov/29.6.E44): [`DLMF.Lame.Real.lameEsk_odd_fourierD_ratio`](DLMF/Lame/FourierSeries/EigenfunctionSeries.lean#L617) (admitted).
- [29.6.E45](https://dlmf.nist.gov/29.6.E45): [`DLMF.Lame.Real.lameEsk_odd_fourier_parseval`](DLMF/Lame/FourierSeries/EigenfunctionSeries.lean#L628) (proved).
- [29.6.E46](https://dlmf.nist.gov/29.6.E46): [`DLMF.Lame.Real.lameEsk_even_hasSum_fourierB`](DLMF/Lame/FourierSeries/EigenfunctionSeries.lean#L652) (proved).
- [29.6.E47](https://dlmf.nist.gov/29.6.E47): [`DLMF.Lame.Real.lameEsk_even_fourierB_rec_zero`](DLMF/Lame/FourierSeries/EigenfunctionSeries.lean#L672) (proved).
- [29.6.E48](https://dlmf.nist.gov/29.6.E48): [`DLMF.Lame.Real.lameEsk_even_fourierB_rec_zero`](DLMF/Lame/FourierSeries/EigenfunctionSeries.lean#L672) (proved).
- [29.6.E49](https://dlmf.nist.gov/29.6.E49): [`DLMF.Lame.Real.lameEsk_even_fourierB_rec`](DLMF/Lame/FourierSeries/EigenfunctionSeries.lean#L693) (proved).
- [29.6.E50](https://dlmf.nist.gov/29.6.E50): [`DLMF.Lame.Real.lameEsk_even_fourierB_normalization`](DLMF/Lame/FourierSeries/EigenfunctionSeries.lean#L722) (proved).
- [29.6.E51](https://dlmf.nist.gov/29.6.E51): [`DLMF.Lame.Real.lameEsk_even_fourierB_pos`](DLMF/Lame/FourierSeries/EigenfunctionSeries.lean#L753) (proved).
- [29.6.E52](https://dlmf.nist.gov/29.6.E52): [`DLMF.Lame.Real.lameEsk_even_fourierB_ratio`](DLMF/Lame/FourierSeries/EigenfunctionSeries.lean#L784) (admitted).
- [29.6.E53](https://dlmf.nist.gov/29.6.E53): [`DLMF.Lame.Real.lameEsk_even_hasSum_fourierD`](DLMF/Lame/FourierSeries/EigenfunctionSeries.lean#L795) (proved).
- [29.6.E54](https://dlmf.nist.gov/29.6.E54): [`DLMF.Lame.Real.lameEsk_even_fourierD_rec_zero`](DLMF/Lame/FourierSeries/EigenfunctionSeries.lean#L817) (proved).
- [29.6.E55](https://dlmf.nist.gov/29.6.E55): [`DLMF.Lame.Real.lameEsk_even_fourierD_rec`](DLMF/Lame/FourierSeries/EigenfunctionSeries.lean#L837) (proved).
- [29.6.E56](https://dlmf.nist.gov/29.6.E56): [`DLMF.Lame.LameRecurrence.alpha`](DLMF/Lame/Basic/RecurrenceData.lean#L34) (definition); [`DLMF.Lame.LameRecurrence.beta`](DLMF/Lame/Basic/RecurrenceData.lean#L50) (definition); [`DLMF.Lame.LameRecurrence.gamma`](DLMF/Lame/Basic/RecurrenceData.lean#L68) (definition).
- [29.6.E57](https://dlmf.nist.gov/29.6.E57): [`DLMF.Lame.Real.lameEsk_even_fourierD_normalization`](DLMF/Lame/FourierSeries/EigenfunctionSeries.lean#L865) (proved).
- [29.6.E58](https://dlmf.nist.gov/29.6.E58): [`DLMF.Lame.Real.lameEsk_even_fourierD_pos`](DLMF/Lame/FourierSeries/EigenfunctionSeries.lean#L918) (proved).
- [29.6.E59](https://dlmf.nist.gov/29.6.E59): [`DLMF.Lame.Real.lameEsk_even_fourierD_ratio`](DLMF/Lame/FourierSeries/EigenfunctionSeries.lean#L949) (admitted).
- [29.6.E60](https://dlmf.nist.gov/29.6.E60): [`DLMF.Lame.Real.lameEsk_even_fourier_parseval`](DLMF/Lame/FourierSeries/EigenfunctionSeries.lean#L960) (proved).

## [§29.7 Asymptotic Expansions](https://dlmf.nist.gov/29.7)

- [29.7.i](https://dlmf.nist.gov/29.7.i): [`DLMF.Lame.Real.lameBk_asymptotic`](DLMF/Lame/Asymptotics.lean#L54) (admitted).
- [29.7.E1](https://dlmf.nist.gov/29.7.E1): [`DLMF.Lame.Real.lameAk_asymptotic`](DLMF/Lame/Asymptotics.lean#L34) (admitted). Poincaré expansion stated with an arbitrary coefficient sequence whose first five terms are 29.7.3–29.7.8.
- [29.7.E2](https://dlmf.nist.gov/29.7.E2): [`DLMF.Lame.lameKappa`](DLMF/Lame/Basic/RecurrenceData.lean#L134) (definition).
- [29.7.E3](https://dlmf.nist.gov/29.7.E3): [`DLMF.Lame.lameTau0`](DLMF/Lame/Basic/RecurrenceData.lean#L138) (definition).
- [29.7.E4](https://dlmf.nist.gov/29.7.E4): [`DLMF.Lame.lameTau1`](DLMF/Lame/Basic/RecurrenceData.lean#L142) (definition).
- [29.7.E5](https://dlmf.nist.gov/29.7.E5): [`DLMF.Lame.Real.lameBk_sub_lameAk_isBigO`](DLMF/Lame/Asymptotics.lean#L46) (admitted).
- [29.7.E6](https://dlmf.nist.gov/29.7.E6): [`DLMF.Lame.lameTau2`](DLMF/Lame/Basic/RecurrenceData.lean#L146) (definition).
- [29.7.E7](https://dlmf.nist.gov/29.7.E7): [`DLMF.Lame.lameTau3`](DLMF/Lame/Basic/RecurrenceData.lean#L150) (definition).
- [29.7.E8](https://dlmf.nist.gov/29.7.E8): [`DLMF.Lame.lameTau4`](DLMF/Lame/Basic/RecurrenceData.lean#L157) (definition).

## [§29.8 Integral Equations](https://dlmf.nist.gov/29.8)

- [29.8.E1](https://dlmf.nist.gov/29.8.E1): [`DLMF.Lame.Real.lame_integral_equation`](DLMF/Lame/IntegralEquations.lean#L40) (admitted).
- [29.8.E2](https://dlmf.nist.gov/29.8.E2): [`DLMF.Lame.Real.lame_integral_equation`](DLMF/Lame/IntegralEquations.lean#L40) (admitted). Kernel `P_ν = DLMF.Legendre.legendreP ν` instead of the Ferrers function (see conventions).
- [29.8.E3](https://dlmf.nist.gov/29.8.E3): [`DLMF.Lame.Real.lame_integral_equation`](DLMF/Lame/IntegralEquations.lean#L40) (admitted).
- [29.8.E4](https://dlmf.nist.gov/29.8.E4): [`DLMF.Lame.Real.lame_integral_equation`](DLMF/Lame/IntegralEquations.lean#L40) (admitted).
- [29.8.E5](https://dlmf.nist.gov/29.8.E5): [`DLMF.Lame.Real.lameEck_even_integral_equation`](DLMF/Lame/IntegralEquations.lean#L65) (admitted).
- [29.8.E6](https://dlmf.nist.gov/29.8.E6): [`DLMF.Lame.Real.lameEck_even_integral_equation`](DLMF/Lame/IntegralEquations.lean#L65) (admitted).
- [29.8.E7](https://dlmf.nist.gov/29.8.E7): [`DLMF.Lame.Real.lameEck_odd_integral_equation`](DLMF/Lame/IntegralEquations.lean#L83) (admitted).
- [29.8.E8](https://dlmf.nist.gov/29.8.E8): [`DLMF.Lame.Real.lameEsk_odd_integral_equation`](DLMF/Lame/IntegralEquations.lean#L102) (admitted).
- [29.8.E9](https://dlmf.nist.gov/29.8.E9): [`DLMF.Lame.Real.lameEsk_even_integral_equation`](DLMF/Lame/IntegralEquations.lean#L122) (admitted).

## [§29.9 Stability](https://dlmf.nist.gov/29.9)

- [29.9](https://dlmf.nist.gov/29.9): [`DLMF.Lame.Real.IsLameStable`](DLMF/Lame/Basic/RecurrenceData.lean#L126) (definition); [`DLMF.Lame.Real.not_isLameStable_iff`](DLMF/Lame/Eigenvalues.lean#L1089) (admitted); [`DLMF.Lame.Real.not_isLameStable_iff_nat`](DLMF/Lame/Eigenvalues.lean#L1098) (admitted). `IsLameStable`: all real solutions bounded on ℝ. Instability iff `h ≤ a^0_ν` or `h` between `a^m_ν` and `b^m_ν` (non-integer `ν`), resp. `h ∈ [b^m_n, a^m_n]` (integer `ν = n`); admitted.

## [§29.10 Lamé Functions with Imaginary Periods](https://dlmf.nist.gov/29.10)

- [29.10](https://dlmf.nist.gov/29.10): [`DLMF.Lame.Real.lame_imaginary_periods`](DLMF/Lame/DifferentialEquations.lean#L687) (proved). Imaginary periods of the functions 29.10.4 proved from the admitted transformation 29.10.1–29.10.3 and the real periods of Table 29.3.2.
- [29.10.E1](https://dlmf.nist.gov/29.10.E1): [`DLMF.Lame.isLameSolutionOn_imaginary`](DLMF/Lame/DifferentialEquations.lean#L527) (proved).
- [29.10.E2](https://dlmf.nist.gov/29.10.E2): [`DLMF.Lame.isLameSolutionOn_imaginary`](DLMF/Lame/DifferentialEquations.lean#L527) (proved).
- [29.10.E3](https://dlmf.nist.gov/29.10.E3): [`DLMF.Lame.isLameSolutionOn_imaginary`](DLMF/Lame/DifferentialEquations.lean#L527) (proved).
- [29.10.E4](https://dlmf.nist.gov/29.10.E4): [`DLMF.Lame.Real.lameEck_imaginary_solution`](DLMF/Lame/DifferentialEquations.lean#L658) (proved); [`DLMF.Lame.Real.lameEsk_imaginary_solution`](DLMF/Lame/DifferentialEquations.lean#L674) (proved).

## [§29.11 Lamé Wave Equation](https://dlmf.nist.gov/29.11)

- [29.11](https://dlmf.nist.gov/29.11): [`DLMF.Lame.isLameWaveSolutionOn_zero_iff`](DLMF/Lame/DifferentialEquations.lean#L713) (proved). For `ω = 0` the wave equation is 29.2.1 (proved).
- [29.11.E1](https://dlmf.nist.gov/29.11.E1): [`DLMF.Lame.IsLameWaveSolutionOn`](DLMF/Lame/Basic/Equations.lean#L72) (definition).

## [§29.12 Definitions](https://dlmf.nist.gov/29.12)

- [29.12.i](https://dlmf.nist.gov/29.12.i): [`DLMF.Lame.lamePolyEk_polynomial_form`](DLMF/Lame/Polynomials/P2pBase.lean#L655) (proved); [`DLMF.Lame.lamePolyEk_zeros`](DLMF/Lame/Polynomials/Series.lean#L612) (proved).
- [29.12.iii](https://dlmf.nist.gov/29.12.iii): [`DLMF.Lame.lamePolyEk_zeros_equilibrium`](DLMF/Lame/Polynomials/Series.lean#L666) (admitted).
- [29.12.E1](https://dlmf.nist.gov/29.12.E1): [`DLMF.Lame.Real.lameUEk_eq`](DLMF/Lame/Polynomials/Series.lean#L104) (proved). For real `x`; the Lamé polynomial is defined by its Chebyshev series (29.15.43–29.15.50).
- [29.12.E2](https://dlmf.nist.gov/29.12.E2): [`DLMF.Lame.Real.lameSEk_eq`](DLMF/Lame/Polynomials/Series.lean#L168) (proved). For real `x`; the Lamé polynomial is defined by its Chebyshev series (29.15.43–29.15.50).
- [29.12.E3](https://dlmf.nist.gov/29.12.E3): [`DLMF.Lame.Real.lameCEk_eq`](DLMF/Lame/Polynomials/Series.lean#L228) (proved). For real `x`; the Lamé polynomial is defined by its Chebyshev series (29.15.43–29.15.50).
- [29.12.E4](https://dlmf.nist.gov/29.12.E4): [`DLMF.Lame.Real.lameDEk_eq`](DLMF/Lame/Polynomials/Series.lean#L291) (proved). For real `x`; the Lamé polynomial is defined by its Chebyshev series (29.15.43–29.15.50).
- [29.12.E5](https://dlmf.nist.gov/29.12.E5): [`DLMF.Lame.Real.lameSCEk_eq`](DLMF/Lame/Polynomials/Series.lean#L366) (proved). For real `x`; the Lamé polynomial is defined by its Chebyshev series (29.15.43–29.15.50).
- [29.12.E6](https://dlmf.nist.gov/29.12.E6): [`DLMF.Lame.Real.lameSDEk_eq`](DLMF/Lame/Polynomials/Series.lean#L428) (proved). For real `x`; the Lamé polynomial is defined by its Chebyshev series (29.15.43–29.15.50).
- [29.12.E7](https://dlmf.nist.gov/29.12.E7): [`DLMF.Lame.Real.lameCDEk_eq`](DLMF/Lame/Polynomials/Series.lean#L493) (proved). For real `x`; the Lamé polynomial is defined by its Chebyshev series (29.15.43–29.15.50).
- [29.12.E8](https://dlmf.nist.gov/29.12.E8): [`DLMF.Lame.Real.lameSCDEk_eq`](DLMF/Lame/Polynomials/Series.lean#L561) (proved). For real `x`; the Lamé polynomial is defined by its Chebyshev series (29.15.43–29.15.50).
- [29.12.E9](https://dlmf.nist.gov/29.12.E9): [`DLMF.Lame.lamePolyEk_algebraic_form`](DLMF/Lame/Polynomials/Series.lean#L625) (proved). Algebraic form stated with the polynomial form of Table 29.12.1 (avoiding branches of `(ξ - 1)^σ`), plus the location and simplicity of the zeros of `P`.
- [29.12.E10](https://dlmf.nist.gov/29.12.E10): [`DLMF.Lame.lamePolyEk_algebraic_form`](DLMF/Lame/Polynomials/Series.lean#L625) (proved).
- [29.12.E11](https://dlmf.nist.gov/29.12.E11): [`DLMF.Lame.lamePolyEk_zeros_maximize`](DLMF/Lame/Polynomials/Series.lean#L643) (admitted).
- [29.12.E12](https://dlmf.nist.gov/29.12.E12): [`DLMF.Lame.lamePolyEk_zeros_maximize`](DLMF/Lame/Polynomials/Series.lean#L643) (admitted).
- [29.12.E13](https://dlmf.nist.gov/29.12.E13): [`DLMF.Lame.lamePolyEk_zeros_equilibrium`](DLMF/Lame/Polynomials/Series.lean#L666) (admitted).
- [29.12.T1](https://dlmf.nist.gov/29.12.T1): [`DLMF.Lame.lamePolyEk_polynomial_form`](DLMF/Lame/Polynomials/P2pBase.lean#L655) (proved); [`DLMF.Lame.lamePolyEk_periods`](DLMF/Lame/Polynomials/P2pBase.lean#L672) (proved); [`DLMF.Lame.lamePolyEk_parities`](DLMF/Lame/Polynomials/P2pBase.lean#L708) (proved). Polynomial form, real and imaginary periods and the three parities, all eight types in three theorems; admitted. The eigenvalue column is 29.15.E7 etc.

## [§29.14 Orthogonality](https://dlmf.nist.gov/29.14)

- [29.14.E1](https://dlmf.nist.gov/29.14.E1): [`DLMF.Lame.lameProduct`](DLMF/Lame/Polynomials/Basic.lean#L230) (definition); [`DLMF.Lame.lameProduct_orthogonal`](DLMF/Lame/Polynomials/Orthogonality.lean#L45) (proved); [`DLMF.Lame.lameProduct_complete`](DLMF/Lame/Polynomials/Orthogonality.lean#L66) (admitted).
- [29.14.E2](https://dlmf.nist.gov/29.14.E2): [`DLMF.Lame.lameInner`](DLMF/Lame/Polynomials/Basic.lean#L224) (definition); [`DLMF.Lame.lameProduct_orthogonal`](DLMF/Lame/Polynomials/Orthogonality.lean#L45) (proved); [`DLMF.Lame.lameProduct_complete`](DLMF/Lame/Polynomials/Orthogonality.lean#L66) (admitted). No complex conjugation, as in DLMF.
- [29.14.E3](https://dlmf.nist.gov/29.14.E3): [`DLMF.Lame.lameOrthWeight`](DLMF/Lame/Polynomials/Basic.lean#L218) (definition); [`DLMF.Lame.lameProduct_orthogonal`](DLMF/Lame/Polynomials/Orthogonality.lean#L45) (proved).
- [29.14.E4](https://dlmf.nist.gov/29.14.E4): [`DLMF.Lame.lameProduct`](DLMF/Lame/Polynomials/Basic.lean#L230) (definition); [`DLMF.Lame.lameProduct_orthogonal`](DLMF/Lame/Polynomials/Orthogonality.lean#L45) (proved); [`DLMF.Lame.lameProduct_complete`](DLMF/Lame/Polynomials/Orthogonality.lean#L66) (admitted).
- [29.14.E5](https://dlmf.nist.gov/29.14.E5): [`DLMF.Lame.lameProduct`](DLMF/Lame/Polynomials/Basic.lean#L230) (definition); [`DLMF.Lame.lameProduct_orthogonal`](DLMF/Lame/Polynomials/Orthogonality.lean#L45) (proved); [`DLMF.Lame.lameProduct_complete`](DLMF/Lame/Polynomials/Orthogonality.lean#L66) (admitted).
- [29.14.E6](https://dlmf.nist.gov/29.14.E6): [`DLMF.Lame.lameProduct`](DLMF/Lame/Polynomials/Basic.lean#L230) (definition); [`DLMF.Lame.lameProduct_orthogonal`](DLMF/Lame/Polynomials/Orthogonality.lean#L45) (proved); [`DLMF.Lame.lameProduct_complete`](DLMF/Lame/Polynomials/Orthogonality.lean#L66) (admitted).
- [29.14.E7](https://dlmf.nist.gov/29.14.E7): [`DLMF.Lame.lameProduct`](DLMF/Lame/Polynomials/Basic.lean#L230) (definition); [`DLMF.Lame.lameProduct_orthogonal`](DLMF/Lame/Polynomials/Orthogonality.lean#L45) (proved); [`DLMF.Lame.lameProduct_complete`](DLMF/Lame/Polynomials/Orthogonality.lean#L66) (admitted).
- [29.14.E8](https://dlmf.nist.gov/29.14.E8): [`DLMF.Lame.lameProduct`](DLMF/Lame/Polynomials/Basic.lean#L230) (definition); [`DLMF.Lame.lameProduct_orthogonal`](DLMF/Lame/Polynomials/Orthogonality.lean#L45) (proved); [`DLMF.Lame.lameProduct_complete`](DLMF/Lame/Polynomials/Orthogonality.lean#L66) (admitted).
- [29.14.E9](https://dlmf.nist.gov/29.14.E9): [`DLMF.Lame.lameProduct`](DLMF/Lame/Polynomials/Basic.lean#L230) (definition); [`DLMF.Lame.lameProduct_orthogonal`](DLMF/Lame/Polynomials/Orthogonality.lean#L45) (proved); [`DLMF.Lame.lameProduct_complete`](DLMF/Lame/Polynomials/Orthogonality.lean#L66) (admitted).
- [29.14.E10](https://dlmf.nist.gov/29.14.E10): [`DLMF.Lame.lameProduct`](DLMF/Lame/Polynomials/Basic.lean#L230) (definition); [`DLMF.Lame.lameProduct_orthogonal`](DLMF/Lame/Polynomials/Orthogonality.lean#L45) (proved); [`DLMF.Lame.lameProduct_complete`](DLMF/Lame/Polynomials/Orthogonality.lean#L66) (admitted).
- [29.14.E11](https://dlmf.nist.gov/29.14.E11): [`DLMF.Lame.lameInner`](DLMF/Lame/Polynomials/Basic.lean#L224) (definition); [`DLMF.Lame.lameProduct_orthogonal_all`](DLMF/Lame/Polynomials/Orthogonality.lean#L81) (proved); [`DLMF.Lame.lameProduct_complete_all`](DLMF/Lame/Polynomials/Orthogonality.lean#L131) (admitted).

## [§29.15 Fourier Series and Chebyshev Series](https://dlmf.nist.gov/29.15)

- [29.15.ii](https://dlmf.nist.gov/29.15.ii): [`DLMF.Lame.l29_sn_eq_cos`](DLMF/Lame/Polynomials/Series.lean#L57) (proved); [`DLMF.Lame.l29_T_cos`](DLMF/Lame/Polynomials/Series.lean#L68) (proved); [`DLMF.Lame.l29_U_cos`](DLMF/Lame/Polynomials/Series.lean#L76) (proved). `cos(jθ) = T_j(cos θ)`, `sin((j+1)θ) = sin θ U_j(cos θ)` and `sn = cos φ` (proved).
- [29.15.E1](https://dlmf.nist.gov/29.15.E1): [`DLMF.Lame.Real.lameUEk_fourier`](DLMF/Lame/Polynomials/Series.lean#L88) (proved). Proved from the Chebyshev series 29.15.43–29.15.50 and §29.15(ii).
- [29.15.E2](https://dlmf.nist.gov/29.15.E2): [`DLMF.Lame.lameMatrix`](DLMF/Lame/Polynomials/Basic.lean#L127) (definition). `lameMatrix r ν k n` for each of the eight recurrences.
- [29.15.E3](https://dlmf.nist.gov/29.15.E3): [`DLMF.Lame.lamePolyH_strictMono`](DLMF/Lame/Polynomials/P2pBase.lean#L218) (proved). Stated as `n + 1` simple roots of the characteristic polynomial and strict increase of `lamePolyH`.
- [29.15.E4](https://dlmf.nist.gov/29.15.E4): [`DLMF.Lame.lamePolyCoeff`](DLMF/Lame/Polynomials/Basic.lean#L160) (definition).
- [29.15.E5](https://dlmf.nist.gov/29.15.E5): [`DLMF.Lame.LamePolyType.normForm`](DLMF/Lame/Polynomials/Basic.lean#L73) (definition).
- [29.15.E6](https://dlmf.nist.gov/29.15.E6): [`DLMF.Lame.LamePolyType.signForm`](DLMF/Lame/Polynomials/Basic.lean#L89) (definition).
- [29.15.E7](https://dlmf.nist.gov/29.15.E7): [`DLMF.Lame.Real.lameAk_eq_lamePolyH_uE`](DLMF/Lame/Polynomials/Series.lean#L139) (proved). Admitted (identifies the matrix eigenvalue with the eigenvalue of §29.3).
- [29.15.E8](https://dlmf.nist.gov/29.15.E8): [`DLMF.Lame.Real.lameSEk_fourier`](DLMF/Lame/Polynomials/Series.lean#L153) (proved). Proved from the Chebyshev series 29.15.43–29.15.50 and §29.15(ii).
- [29.15.E9](https://dlmf.nist.gov/29.15.E9): [`DLMF.Lame.lamePolyCoeff`](DLMF/Lame/Polynomials/Basic.lean#L160) (definition).
- [29.15.E10](https://dlmf.nist.gov/29.15.E10): [`DLMF.Lame.LamePolyType.normForm`](DLMF/Lame/Polynomials/Basic.lean#L73) (definition).
- [29.15.E11](https://dlmf.nist.gov/29.15.E11): [`DLMF.Lame.LamePolyType.signForm`](DLMF/Lame/Polynomials/Basic.lean#L89) (definition).
- [29.15.E12](https://dlmf.nist.gov/29.15.E12): [`DLMF.Lame.Real.lameAk_eq_lamePolyH_sE`](DLMF/Lame/Polynomials/Series.lean#L196) (proved). Admitted (identifies the matrix eigenvalue with the eigenvalue of §29.3).
- [29.15.E13](https://dlmf.nist.gov/29.15.E13): [`DLMF.Lame.Real.lameCEk_fourier`](DLMF/Lame/Polynomials/Series.lean#L210) (proved). Proved from the Chebyshev series 29.15.43–29.15.50 and §29.15(ii).
- [29.15.E14](https://dlmf.nist.gov/29.15.E14): [`DLMF.Lame.lamePolyCoeff`](DLMF/Lame/Polynomials/Basic.lean#L160) (definition).
- [29.15.E15](https://dlmf.nist.gov/29.15.E15): [`DLMF.Lame.LamePolyType.normForm`](DLMF/Lame/Polynomials/Basic.lean#L73) (definition).
- [29.15.E16](https://dlmf.nist.gov/29.15.E16): [`DLMF.Lame.LamePolyType.signForm`](DLMF/Lame/Polynomials/Basic.lean#L89) (definition).
- [29.15.E17](https://dlmf.nist.gov/29.15.E17): [`DLMF.Lame.Real.lameBk_eq_lamePolyH_cE`](DLMF/Lame/Polynomials/Series.lean#L259) (proved). Admitted (identifies the matrix eigenvalue with the eigenvalue of §29.3).
- [29.15.E18](https://dlmf.nist.gov/29.15.E18): [`DLMF.Lame.Real.lameDEk_fourier`](DLMF/Lame/Polynomials/Series.lean#L273) (proved). Proved from the Chebyshev series 29.15.43–29.15.50 and §29.15(ii).
- [29.15.E19](https://dlmf.nist.gov/29.15.E19): [`DLMF.Lame.lamePolyCoeff`](DLMF/Lame/Polynomials/Basic.lean#L160) (definition).
- [29.15.E20](https://dlmf.nist.gov/29.15.E20): [`DLMF.Lame.LamePolyType.normForm`](DLMF/Lame/Polynomials/Basic.lean#L73) (definition).
- [29.15.E21](https://dlmf.nist.gov/29.15.E21): [`DLMF.Lame.LamePolyType.signForm`](DLMF/Lame/Polynomials/Basic.lean#L89) (definition).
- [29.15.E22](https://dlmf.nist.gov/29.15.E22): [`DLMF.Lame.Real.lameAk_eq_lamePolyH_dE`](DLMF/Lame/Polynomials/Series.lean#L334) (proved). Admitted (identifies the matrix eigenvalue with the eigenvalue of §29.3).
- [29.15.E23](https://dlmf.nist.gov/29.15.E23): [`DLMF.Lame.Real.lameSCEk_fourier`](DLMF/Lame/Polynomials/Series.lean#L348) (proved). Proved from the Chebyshev series 29.15.43–29.15.50 and §29.15(ii).
- [29.15.E24](https://dlmf.nist.gov/29.15.E24): [`DLMF.Lame.lamePolyCoeff`](DLMF/Lame/Polynomials/Basic.lean#L160) (definition).
- [29.15.E25](https://dlmf.nist.gov/29.15.E25): [`DLMF.Lame.LamePolyType.normForm`](DLMF/Lame/Polynomials/Basic.lean#L73) (definition).
- [29.15.E26](https://dlmf.nist.gov/29.15.E26): [`DLMF.Lame.LamePolyType.signForm`](DLMF/Lame/Polynomials/Basic.lean#L89) (definition).
- [29.15.E27](https://dlmf.nist.gov/29.15.E27): [`DLMF.Lame.Real.lameBk_eq_lamePolyH_scE`](DLMF/Lame/Polynomials/Series.lean#L397) (proved). Admitted (identifies the matrix eigenvalue with the eigenvalue of §29.3).
- [29.15.E28](https://dlmf.nist.gov/29.15.E28): [`DLMF.Lame.Real.lameSDEk_fourier`](DLMF/Lame/Polynomials/Series.lean#L411) (proved). Proved from the Chebyshev series 29.15.43–29.15.50 and §29.15(ii).
- [29.15.E29](https://dlmf.nist.gov/29.15.E29): [`DLMF.Lame.lamePolyCoeff`](DLMF/Lame/Polynomials/Basic.lean#L160) (definition).
- [29.15.E30](https://dlmf.nist.gov/29.15.E30): [`DLMF.Lame.LamePolyType.normForm`](DLMF/Lame/Polynomials/Basic.lean#L73) (definition).
- [29.15.E31](https://dlmf.nist.gov/29.15.E31): [`DLMF.Lame.LamePolyType.signForm`](DLMF/Lame/Polynomials/Basic.lean#L89) (definition).
- [29.15.E32](https://dlmf.nist.gov/29.15.E32): [`DLMF.Lame.Real.lameAk_eq_lamePolyH_sdE`](DLMF/Lame/Polynomials/Series.lean#L461) (proved). Admitted (identifies the matrix eigenvalue with the eigenvalue of §29.3).
- [29.15.E33](https://dlmf.nist.gov/29.15.E33): [`DLMF.Lame.Real.lameCDEk_fourier`](DLMF/Lame/Polynomials/Series.lean#L475) (proved). Proved from the Chebyshev series 29.15.43–29.15.50 and §29.15(ii).
- [29.15.E34](https://dlmf.nist.gov/29.15.E34): [`DLMF.Lame.lamePolyCoeff`](DLMF/Lame/Polynomials/Basic.lean#L160) (definition).
- [29.15.E35](https://dlmf.nist.gov/29.15.E35): [`DLMF.Lame.LamePolyType.normForm`](DLMF/Lame/Polynomials/Basic.lean#L73) (definition).
- [29.15.E36](https://dlmf.nist.gov/29.15.E36): [`DLMF.Lame.LamePolyType.signForm`](DLMF/Lame/Polynomials/Basic.lean#L89) (definition).
- [29.15.E37](https://dlmf.nist.gov/29.15.E37): [`DLMF.Lame.Real.lameBk_eq_lamePolyH_cdE`](DLMF/Lame/Polynomials/Series.lean#L529) (proved). Admitted (identifies the matrix eigenvalue with the eigenvalue of §29.3).
- [29.15.E38](https://dlmf.nist.gov/29.15.E38): [`DLMF.Lame.Real.lameSCDEk_fourier`](DLMF/Lame/Polynomials/Series.lean#L543) (proved). Proved from the Chebyshev series 29.15.43–29.15.50 and §29.15(ii).
- [29.15.E39](https://dlmf.nist.gov/29.15.E39): [`DLMF.Lame.lamePolyCoeff`](DLMF/Lame/Polynomials/Basic.lean#L160) (definition).
- [29.15.E40](https://dlmf.nist.gov/29.15.E40): [`DLMF.Lame.LamePolyType.normForm`](DLMF/Lame/Polynomials/Basic.lean#L73) (definition).
- [29.15.E41](https://dlmf.nist.gov/29.15.E41): [`DLMF.Lame.LamePolyType.signForm`](DLMF/Lame/Polynomials/Basic.lean#L89) (definition).
- [29.15.E42](https://dlmf.nist.gov/29.15.E42): [`DLMF.Lame.Real.lameBk_eq_lamePolyH_scdE`](DLMF/Lame/Polynomials/Series.lean#L598) (proved). Admitted (identifies the matrix eigenvalue with the eigenvalue of §29.3).
- [29.15.E43](https://dlmf.nist.gov/29.15.E43): [`DLMF.Lame.lameUEk`](DLMF/Lame/Polynomials/Basic.lean#L182) (definition).
- [29.15.E44](https://dlmf.nist.gov/29.15.E44): [`DLMF.Lame.lameSEk`](DLMF/Lame/Polynomials/Basic.lean#L186) (definition).
- [29.15.E45](https://dlmf.nist.gov/29.15.E45): [`DLMF.Lame.lameCEk`](DLMF/Lame/Polynomials/Basic.lean#L190) (definition).
- [29.15.E46](https://dlmf.nist.gov/29.15.E46): [`DLMF.Lame.lameDEk`](DLMF/Lame/Polynomials/Basic.lean#L194) (definition).
- [29.15.E47](https://dlmf.nist.gov/29.15.E47): [`DLMF.Lame.lameSCEk`](DLMF/Lame/Polynomials/Basic.lean#L198) (definition).
- [29.15.E48](https://dlmf.nist.gov/29.15.E48): [`DLMF.Lame.lameSDEk`](DLMF/Lame/Polynomials/Basic.lean#L202) (definition).
- [29.15.E49](https://dlmf.nist.gov/29.15.E49): [`DLMF.Lame.lameCDEk`](DLMF/Lame/Polynomials/Basic.lean#L206) (definition).
- [29.15.E50](https://dlmf.nist.gov/29.15.E50): [`DLMF.Lame.lameSCDEk`](DLMF/Lame/Polynomials/Basic.lean#L211) (definition).

## [§29.17 Other Solutions](https://dlmf.nist.gov/29.17)

- [29.17.E1](https://dlmf.nist.gov/29.17.E1): [`DLMF.Lame.lamePolyEk_second_solution`](DLMF/Lame/OtherSolutions.lean#L36) (admitted). Path from `iK'` (a pole of `E`) along the segment, local statement on an open set; the Wronskian `E F' - E' F = 1` is included.
## Prose, informal and excluded items

- [§29.1](https://dlmf.nist.gov/29.1) Special Notation: notation and conventions only (recorded
  above). The relations 29.1.Ex1–29.1.Ex10 to Jansen's functions `L^{(m)}_{cν}`, `L^{(m)}_{sν}`
  and Ince's interchange of `a^{2m+1}_ν` and `b^{2m+1}_ν` concern other notations; not
  acquired.
- 29.2(i) remark that 29.2.1 has no other singularities and the description of the forms in
  §29.2(ii): covered by the tagged theorems.
- [§29.4](https://dlmf.nist.gov/29.4) and [§29.13](https://dlmf.nist.gov/29.13) Graphics:
  excluded: graphical.
- [§29.7(ii)](https://dlmf.nist.gov/29.7.ii) Müller's asymptotic expansions of the Lamé
  functions: formal expansions described without precise statement; not acquired.
- [§29.16](https://dlmf.nist.gov/29.16) Asymptotic Expansions of Lamé polynomials: references
  only (Hargrave and Sleeman 1977); not acquired.
- [§29.17(ii)](https://dlmf.nist.gov/29.17.ii) algebraic Lamé functions and
  [§29.17(iii)](https://dlmf.nist.gov/29.17.iii) Lamé–Wangerin functions: descriptive with
  references; not acquired.
- [§29.18](https://dlmf.nist.gov/29.18) Mathematical Applications: excluded: application. Its
  pure-mathematics content: 29.18.1–29.18.7 separate the wave equation in sphero-conal
  coordinates into the spherical Bessel equation 29.18.5 and two Lamé equations 29.18.6–29.18.7;
  29.18.8–29.18.10 separate it in ellipsoidal coordinates into three Lamé wave equations
  (29.11.1); §29.18(iii), (iv) are references only.
- [§29.19](https://dlmf.nist.gov/29.19) Physical Applications: excluded: application.
- [§29.20](https://dlmf.nist.gov/29.20) Methods of Computation,
  [§29.21](https://dlmf.nist.gov/29.21) Tables and [§29.22](https://dlmf.nist.gov/29.22)
  Software: excluded: computation.
- Bibliographic paragraphs (Arscott, Erdélyi et al., Ince, Jansen, …) are not acquired.

## Validation

- All eleven modules build with `lake build DLMF.Lame.<Module>` and each passes
  `lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false` with only `sorry` warnings.
  Lines are at most 100 characters and `git diff --check` is clean.
- There are no axioms and no `native_decide`; definitions (Basic, Polynomials/Basic) and helper
  declarations (prefix `l29_`) contain no `sorry`. The only admissions besides acquired DLMF
  statements are the two flagged existence theorems `Real.lameEigenvalue_spec` and
  `Real.lameEigenfunction_spec`.
- `#print axioms` over all 236 declarations shows only `propext`, `Classical.choice`,
  `Quot.sound` and (for the 148 admitted or dependent theorems) `sorryAx`; for example
  `Real.isLameSolution_comp_lamePhi`, `isLameAlgebraicSolutionOn_iff_isHeunSolOn`,
  `isLameWaveSolutionOn_zero_iff`, `Real.IsLameEigenfunction.parity`, `l29_reflect`,
  `l29_integral_mul_eq_zero`, `Real.lameUEk_fourier` and `Real.lameSCDEk_fourier` depend on
  `[propext, Classical.choice, Quot.sound]`.
- DLMF.lean, the area umbrella `DLMF/Lame.lean`, the lakefile and the other ledgers are
  unchanged; the coordinator adds the eleven modules to the umbrella.
