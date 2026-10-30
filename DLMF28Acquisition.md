# DLMF Chapter 28 acquisition: Mathieu Functions and Hill's Equation

> Source paths and current layout notes were refreshed on 2026-10-30; generated per-entry
> statuses follow the compiled ledger refresh. Dated acquisition and proof counts
> describe their original batches.

This acquisition covers the definitions, numbered formulas and analytical assertions in prose
of [DLMF Chapter 28](https://dlmf.nist.gov/28), version 1.2.8, checked on 2026-10-26. It was
done by three concurrent agents, and this ledger has three parts:

**Status after proof round 1 (2026-10-26).** Direct admissions in DLMF/Mathieu fell from 314 to 203. Proved: the Mathieu existence theorem (entire solutions of linear ODEs with entire coefficients), Hill's global existence and §28.29(ii) Floquet theory, Fourier series and recurrences 28.4.1–20, the integral equations 28.10.1–8, Floquet and q = 0 results of §28.2, all of 28.5.3–7 (including the corrected 28.5.6), absolute convergence of the me_ν series 28.14.1, Ince-equation characterizations and several modified-function relations. 28.2.33 gained the hypothesis n ≠ 0 after a proved counterexample. Many results are proved only from the flagged existence theorems; see REVIEW.md, "Proof round 1 for Chapters 28–31 (2026-10-26)".

**Status after proof round 2 (2026-10-26).** Direct admissions in DLMF/Mathieu fell from 203 to 173. Proved: the eigenvalue existence theorems `mathieuSpecA_exists`/`mathieuSpecB_exists` behind a_n(q), b_n(q) (periodic Sturm–Liouville theory), so everything that rested only on them is now fully proved; Ince's theorem (§28.5(i)) and Floquet uniqueness (§28.2(iv)); joint entireness of w_I, w_II and the singularities of the algebraic form (§28.2(i)–(iii)); 28.2.18–20; the zero counts `mathieu_zeros_count` and the imaginary-axis zeros (§28.9) by a general Sturm oscillation theorem; the −q relations 28.2.34–37; locally uniform convergence §28.4(i); the stability chart §28.17; Hill's growth bound §28.29(iii); the radial series 28.24.1–5 with locally uniform convergence; the reality §28.20(iii) and the equation for the modified functions; and the connection formulas 28.22.1–4. 28.12.7 is proved under the extra hypothesis of distinct eigenvalues (separate theorem). See REVIEW.md, "Proof round 2 for Chapters 28–31 (2026-10-26)".

- Part A (agent ACQ28A): §§28.1–28.11, Mathieu functions of integer order. Lean code in
  `DLMF/Mathieu/` (namespace `DLMF.Mathieu`, helper prefix `m28a_`).
- Part B (agent ACQ28B): §§28.12–28.19 and §§28.29–28.31, Mathieu functions of noninteger
  order and Hill's equation (appended below by ACQ28B).
- Part C (agent ACQ28C): §§28.20–28.28, modified Mathieu functions (appended below by ACQ28C).

Excluded for the whole chapter: the graphics sections [§28.3](https://dlmf.nist.gov/28.3),
[§28.13](https://dlmf.nist.gov/28.13) and [§28.21](https://dlmf.nist.gov/28.21) (excluded:
graphics); the applications sections [§28.32](https://dlmf.nist.gov/28.32) and
[§28.33](https://dlmf.nist.gov/28.33) (excluded: application; their mathematical content is
listed in the exclusions of part A below); the computation, tables and software sections
[§28.34](https://dlmf.nist.gov/28.34)–[§28.36](https://dlmf.nist.gov/28.36) (excluded:
computation).

# Part A: §§28.1–28.11 (ACQ28A)

**Current layout (2026-10-30).**
`DLMF.Mathieu.Basic` is the foundational umbrella for `Basic.EquationAndSolutions`,
`Basic.Spectral`, `Basic.Functions` and `Basic.ContinuedFractions`. They retain the Mathieu
equation, `w_I`, `w_II`, Floquet notions, eigenvalues `a_n`, `b_n`, eigenfunctions `ce_n`,
`se_n`, second solutions `fe_n`, `ge_n` and Fourier coefficients. The existence proofs are
in `FundamentalSolutions` and `SpectralExistence`; `Properties` collects the separate basic
solution, Floquet, spectral and eigenfunction theorem files.
The subsequent theorem developments are
[FourierSeries](DLMF/Mathieu/FourierSeries.lean) (§28.4),
[SecondSolutions](DLMF/Mathieu/SecondSolutions.lean) (§28.5),
[SmallQ](DLMF/Mathieu/SmallQ.lean) (§28.6),
[Continuation](DLMF/Mathieu/Continuation.lean) (§28.7),
[LargeQ](DLMF/Mathieu/LargeQ.lean) (§28.8),
[Zeros](DLMF/Mathieu/Zeros.lean) (§28.9),
[IntegralEquations](DLMF/Mathieu/IntegralEquations.lean) (§28.10) and
[Expansions](DLMF/Mathieu/Expansions.lean) (§28.11).
They import the theorem APIs they use explicitly; for example `SmallQ` uses
`SpectralExistence`, the small-q coefficient developments, `Basic.ContinuedFractions` and
`DLMF.EllipticIntegrals.Legendre`. Mathlib supplies `Complex.besselJ` and
`Polynomial.hermite`, but has no Mathieu functions, so there is no MathlibCoverage file.

**Counts.** §§28.2–28.11 have 137 numbered items (134 equations and the tables 28.2.T1,
28.2.T2, 28.6.T1); §28.1 is notation only and §28.3 is graphics. In scope: 136 (28.6.T1, the
radii of convergence of the small-q series, is excluded: numerical). Covered: all 136. In
addition 11 prose IDs (28.2.i–28.2.v, 28.4.i, 28.4.iii, 28.5.i, 28.6.ii, 28.7, 28.9) carry
tags. 147 DLMF IDs are tagged on 220 declarations: 20 definitions, 42 proved theorems and 158
admitted theorems. The modules hold 270 declarations in all (31 definitions); the untagged ones
are definitions and proved helpers.

Module admissions (`grep -cE 'by sorry|:= sorry|^\s*(·\s*)?sorry\s*$|exact sorry'`) and tagged
declarations:

- [Basic](DLMF/Mathieu/Basic.lean): 3 admissions (the flagged existence theorems). 25 tagged: 20 definitions, 2 proved, 3 admitted.
- [ContinuedFractions](DLMF/Mathieu/Basic/ContinuedFractions.lean): 0 admissions. 2 untagged definitions.
- [Properties](DLMF/Mathieu/Properties.lean): 0 admissions. 71 tagged: 35 proved, 36 admitted.
- [FourierSeries](DLMF/Mathieu/FourierSeries.lean): 9 admissions. 36 tagged: 36 admitted.
- [SecondSolutions](DLMF/Mathieu/SecondSolutions.lean): 1 admissions. 20 tagged: 5 proved, 15 admitted.
- [SmallQ](DLMF/Mathieu/SmallQ.lean): 9 admissions. 31 tagged: 31 admitted.
- [Continuation](DLMF/Mathieu/Continuation.lean): 7 admissions. 7 tagged: 7 admitted.
- [LargeQ](DLMF/Mathieu/LargeQ.lean): 5 admissions. 5 tagged: 5 admitted.
- [Zeros](DLMF/Mathieu/Zeros.lean): 7 admissions. 9 tagged: 9 admitted.
- [IntegralEquations](DLMF/Mathieu/IntegralEquations.lean): 2 admissions. 10 tagged: 10 admitted.
- [Expansions](DLMF/Mathieu/Expansions.lean): 6 admissions. 6 tagged: 6 admitted.

## Design decisions (definitions by choice)

- The Mathieu equation 28.2.1 is the predicate `IsMathieuSolution a q w` (complex `a`, `q`,
  `w : ℂ → ℂ` differentiable with `w'' + (a − 2q cos 2z) w = 0`). Uniqueness from initial data
  (`IsMathieuSolution.eq_of_initial`) is proved from the project's power-series ODE uniqueness.
- `mathieuWI`, `mathieuWII` (28.2.5) are defined by choice from the admitted existence theorem
  `exists_isMathieuSolution` (28.2(ii)), as `if h : ∃ … then h.choose else 0`; uniqueness
  makes the choice irrelevant, and `mathieuWI_spec`, `mathieuWII_spec` are proved.
- The eigenvalues `mathieuA n q`, `mathieuB n q` are defined for real `q` only. The sets
  `mathieuSpecA q`, `mathieuSpecB q` are the real `a` admitting a solution of the parity and
  period type of Table 28.2.1; `mathieuA n q` is the `⌊n/2⌋`-th least element of the
  appropriate set (`nthLeast`, the element with exactly `k` smaller elements), so that
  `a_0 < a_2 < …` and `a_1 < a_3 < …` are separate ordered spectra. Existence of the ordered
  spectra is the admitted `mathieuSpecA_exists`, `mathieuSpecB_exists` (28.2(v)); the
  interlacing 28.2.25 is an admitted theorem. `mathieuB 0 q = 0` is a junk value (`b_0` is not
  defined in DLMF), and so is `mathieuSe 0`.
- `mathieuCe n z q`, `mathieuSe n z q` (argument order of DLMF) are the solutions with
  eigenvalue `a_n(q)`, resp. `b_n(q)`, normalized by 28.2.30 and the sign conditions
  `ce_n(0, q) > 0`, `se_n'(0, q) > 0`. For real `q` these are equivalent to DLMF's continuity
  convention in `q` (verified numerically against scipy). They are built from `w_I`, `w_II`
  with the factors `mathieuCeZero`, `mathieuSeDerivZero` = `√(π / ∫₀^{2π} |w|²)`.
- The second solutions `mathieuFe`, `mathieuGe` (28.5) are normalized by 28.5.5 as
  `fe_n'(0) > 0`, `ge_n(0) > 0`. The case `n = 0`, `q = 0` is the special value
  `fe_0(z, 0) = z` (28.5.7); 28.5.5 makes `fe_0'(0, q) ≈ 2/|q|` blow up as `q → 0`, so `fe_0`
  is discontinuous at `q = 0` (DLMF's 28.5.7 is a separate convention). `mathieuFeC`,
  `mathieuGeS`, `mathieuFeF`, `mathieuGeG` are the constants of 28.5.3–28.5.4
  (`C_0(0) = √2` by convention).
- The Fourier coefficients `mathieuFourierA n m q`, `mathieuFourierB n m q` (28.4) are defined
  as Fourier integrals of `ce_n`, `se_n`; the series 28.4.1–28.4.4 are admitted `HasSum`
  statements with locally uniform convergence.
- No definition of `ν̂` is made: the characteristic exponent is handled by the predicate
  `IsMathieuCharExp` (28.2.16) and the principal branch `DLMF.Elementary.arccosPrincipal`.
- The continued fractions of 28.6.16–28.6.19 are `mathieuCFTail` (a finite `foldr`) and
  `mathieuCFHead`; the statements take the limit of the truncations.
- Asymptotic statements (28.6 small-q series, 28.4.21–27, 28.8) are stated with
  `Asymptotics.IsBigO` or with explicit error functions `ε` bounded by the stated order;
  28.6.20 (radius of convergence) is stated via analytic extension on balls.

## Source corrections and notes

- **28.6.12, 28.6.13** (no erratum): the `q⁶` coefficients have denominator 92935987200000,
  which is what DLMF prints (as `9293 59872 00000`); the acquisition agent first misread the
  digit grouping. Checks: the coefficient is ≈ 7.256·10⁻⁸ (tridiagonal eigenvalue fit),
  `a_6 − b_6 = q⁶/7372800 + …` as in 28.6.15, and `(a_6 + b_6)/2` agrees with 28.6.14.
- **28.5.6**, second relation (erratum or sign convention): with DLMF's own normalization
  28.5.5 the relation is `C_{2m+1}(−q) = −S_{2m+1}(q)`. Numerically `C_1(−1) = −0.95506`,
  `S_1(1) = 0.95506`, `C_3(−1) = −0.0051465`, `S_3(1) = 0.0051465`; it also follows
  analytically from 28.2.35 and the sign rule. The corrected form is acquired.
- **28.6.16**: valid for `n ≥ 1`; for `n = 0` the leading term carries a factor 2 (both forms
  are acquired).
- Numerically verified before acquisition (scripts with tridiagonal eigenproblems and ODE
  integration): the sign conventions, 28.2.34, 28.4.21–28.4.27, 28.6.1–28.6.15 (including
  28.6.12, 28.6.13), 28.6.16–28.6.19, 28.7.1–28.7.4, 28.8.1–28.8.2, the Sips and
  Goldstein expansions 28.8.3–28.8.12, 28.10.1–28.10.10.

## Numbered formulas and prose items

## [§28.2 Definitions and Basic Properties](https://dlmf.nist.gov/28.2)

- [28.2.i](https://dlmf.nist.gov/28.2.i): [`DLMF.Mathieu.mathieu_algebraic_form_singularities`](DLMF/Mathieu/Properties/BasicSolutions.lean#L144) (proved).
- [28.2.ii](https://dlmf.nist.gov/28.2.ii): [`DLMF.Mathieu.exists_isMathieuSolution`](DLMF/Mathieu/FundamentalSolutions.lean#L92) (proved); [`DLMF.Mathieu.mathieuWI_neg`](DLMF/Mathieu/Properties/BasicSolutions.lean#L367) (proved); [`DLMF.Mathieu.mathieuWII_neg`](DLMF/Mathieu/Properties/BasicSolutions.lean#L375) (proved); [`DLMF.Mathieu.differentiable_mathieuWI_mathieuWII`](DLMF/Mathieu/Properties/BasicSolutions.lean#L624) (proved).
- [28.2.iii](https://dlmf.nist.gov/28.2.iii): [`DLMF.Mathieu.exists_entire_mathieuWI_pi`](DLMF/Mathieu/Properties/Floquet.lean#L180) (proved); [`DLMF.Mathieu.isMathieuCharExp_iff`](DLMF/Mathieu/Properties/Floquet.lean#L201) (proved); [`DLMF.Mathieu.re_arccosPrincipal_mathieuWI_div_pi_mem`](DLMF/Mathieu/Properties/Floquet.lean#L276) (proved); [`DLMF.Mathieu.isMathieuCharExp_double_iff`](DLMF/Mathieu/Properties/Floquet.lean#L283) (proved).
- [28.2.iv](https://dlmf.nist.gov/28.2.iv): [`DLMF.Mathieu.IsMathieuSolution.isFloquet_or`](DLMF/Mathieu/Properties/Floquet.lean#L309) (proved); [`DLMF.Mathieu.IsFloquetSolution.unique`](DLMF/Mathieu/Properties/Floquet.lean#L726) (proved).
- [28.2.v](https://dlmf.nist.gov/28.2.v): [`DLMF.Mathieu.mathieuSpecA_exists`](DLMF/Mathieu/SpectralExistence.lean#L233) (proved); [`DLMF.Mathieu.mathieuSpecB_exists`](DLMF/Mathieu/SpectralExistence.lean#L246) (proved); [`DLMF.Mathieu.charExp_set_infinite_discrete`](DLMF/Mathieu/Properties/Spectra.lean#L29) (admitted); [`DLMF.Mathieu.mathieuA_lt_mathieuA_add_two`](DLMF/Mathieu/Properties/Spectra.lean#L294) (proved); [`DLMF.Mathieu.mathieuB_lt_mathieuB_add_two`](DLMF/Mathieu/Properties/Spectra.lean#L303) (proved).
- [28.2.E1](https://dlmf.nist.gov/28.2.E1): [`DLMF.Mathieu.IsMathieuSolution`](DLMF/Mathieu/Basic/EquationAndSolutions.lean#L42) (definition).
- [28.2.E2](https://dlmf.nist.gov/28.2.E2): [`DLMF.Mathieu.algebraic_form_sin_sq`](DLMF/Mathieu/Properties/BasicSolutions.lean#L33) (proved).
- [28.2.E3](https://dlmf.nist.gov/28.2.E3): [`DLMF.Mathieu.algebraic_form_cos`](DLMF/Mathieu/Properties/BasicSolutions.lean#L75) (proved).
- [28.2.E4](https://dlmf.nist.gov/28.2.E4): [`DLMF.Mathieu.IsMathieuSolution.comp_neg`](DLMF/Mathieu/Properties/BasicSolutions.lean#L292) (proved); [`DLMF.Mathieu.IsMathieuSolution.comp_add_pi`](DLMF/Mathieu/Properties/BasicSolutions.lean#L299) (proved); [`DLMF.Mathieu.IsMathieuSolution.comp_sub_pi`](DLMF/Mathieu/Properties/BasicSolutions.lean#L308) (proved); [`DLMF.Mathieu.IsMathieuSolution.comp_add_half_pi`](DLMF/Mathieu/Properties/BasicSolutions.lean#L317) (proved); [`DLMF.Mathieu.IsMathieuSolution.comp_sub_half_pi`](DLMF/Mathieu/Properties/BasicSolutions.lean#L326) (proved).
- [28.2.E5](https://dlmf.nist.gov/28.2.E5): [`DLMF.Mathieu.mathieuWI`](DLMF/Mathieu/Basic/EquationAndSolutions.lean#L52) (definition); [`DLMF.Mathieu.mathieuWII`](DLMF/Mathieu/Basic/EquationAndSolutions.lean#L59) (definition); [`DLMF.Mathieu.mathieuWI_spec`](DLMF/Mathieu/FundamentalSolutions.lean#L104) (proved); [`DLMF.Mathieu.mathieuWII_spec`](DLMF/Mathieu/FundamentalSolutions.lean#L113) (proved).
- [28.2.E6](https://dlmf.nist.gov/28.2.E6): [`DLMF.Mathieu.mathieuWI_wronskian`](DLMF/Mathieu/Properties/BasicSolutions.lean#L400) (proved).
- [28.2.E7](https://dlmf.nist.gov/28.2.E7): [`DLMF.Mathieu.mathieuWI_add_pi`](DLMF/Mathieu/Properties/BasicSolutions.lean#L517) (proved); [`DLMF.Mathieu.mathieuWI_sub_pi`](DLMF/Mathieu/Properties/BasicSolutions.lean#L525) (proved).
- [28.2.E8](https://dlmf.nist.gov/28.2.E8): [`DLMF.Mathieu.mathieuWII_add_pi`](DLMF/Mathieu/Properties/BasicSolutions.lean#L533) (proved); [`DLMF.Mathieu.mathieuWII_sub_pi`](DLMF/Mathieu/Properties/BasicSolutions.lean#L541) (proved).
- [28.2.E9](https://dlmf.nist.gov/28.2.E9): [`DLMF.Mathieu.mathieuWI_pi_eq_deriv_mathieuWII_pi`](DLMF/Mathieu/Properties/BasicSolutions.lean#L485) (proved).
- [28.2.E10](https://dlmf.nist.gov/28.2.E10): [`DLMF.Mathieu.mathieuWI_pi_sub_one`](DLMF/Mathieu/Properties/BasicSolutions.lean#L490) (proved).
- [28.2.E11](https://dlmf.nist.gov/28.2.E11): [`DLMF.Mathieu.mathieuWI_pi_add_one`](DLMF/Mathieu/Properties/BasicSolutions.lean#L495) (proved).
- [28.2.E12](https://dlmf.nist.gov/28.2.E12): [`DLMF.Mathieu.deriv_mathieuWI_pi`](DLMF/Mathieu/Properties/BasicSolutions.lean#L500) (proved).
- [28.2.E13](https://dlmf.nist.gov/28.2.E13): [`DLMF.Mathieu.mathieuWII_pi`](DLMF/Mathieu/Properties/BasicSolutions.lean#L511) (proved).
- [28.2.E14](https://dlmf.nist.gov/28.2.E14): [`DLMF.Mathieu.IsFloquetSolution`](DLMF/Mathieu/Basic/EquationAndSolutions.lean#L81) (definition); [`DLMF.Mathieu.exists_isFloquetSolution_iff`](DLMF/Mathieu/Properties/Floquet.lean#L29) (proved).
- [28.2.E15](https://dlmf.nist.gov/28.2.E15): [`DLMF.Mathieu.mathieuMonodromy`](DLMF/Mathieu/Basic/EquationAndSolutions.lean#L67) (definition); [`DLMF.Mathieu.exists_isFloquetSolution_iff`](DLMF/Mathieu/Properties/Floquet.lean#L29) (proved).
- [28.2.E16](https://dlmf.nist.gov/28.2.E16): [`DLMF.Mathieu.IsMathieuCharExp`](DLMF/Mathieu/Basic/EquationAndSolutions.lean#L73) (definition); [`DLMF.Mathieu.exists_isFloquetSolution_iff_charExp`](DLMF/Mathieu/Properties/Floquet.lean#L85) (proved); [`DLMF.Mathieu.mathieuWI_pi_neg_q`](DLMF/Mathieu/Properties/Floquet.lean#L117) (proved).
- [28.2.E17](https://dlmf.nist.gov/28.2.E17): [`DLMF.Mathieu.IsMathieuSolution.add_pi_add_sub_pi`](DLMF/Mathieu/Properties/Floquet.lean#L296) (proved).
- [28.2.E18](https://dlmf.nist.gov/28.2.E18): [`DLMF.Mathieu.IsFloquetSolution.exists_fourier`](DLMF/Mathieu/Properties/Floquet.lean#L868) (proved).
- [28.2.E19](https://dlmf.nist.gov/28.2.E19): [`DLMF.Mathieu.IsFloquetSolution.exists_fourier`](DLMF/Mathieu/Properties/Floquet.lean#L868) (proved).
- [28.2.E20](https://dlmf.nist.gov/28.2.E20): [`DLMF.Mathieu.isFloquetSolution_of_recurrence`](DLMF/Mathieu/Properties/Floquet.lean#L1031) (proved).
- [28.2.E21](https://dlmf.nist.gov/28.2.E21): [`DLMF.Mathieu.deriv_mathieuWI_half_pi_mathieuA_even`](DLMF/Mathieu/Properties/Spectra.lean#L38) (proved); [`DLMF.Mathieu.mathieuWI_half_pi_mathieuA_odd`](DLMF/Mathieu/Properties/Spectra.lean#L45) (proved).
- [28.2.E22](https://dlmf.nist.gov/28.2.E22): [`DLMF.Mathieu.deriv_mathieuWII_half_pi_mathieuB_odd`](DLMF/Mathieu/Properties/Spectra.lean#L52) (proved); [`DLMF.Mathieu.mathieuWII_half_pi_mathieuB_even`](DLMF/Mathieu/Properties/Spectra.lean#L59) (proved).
- [28.2.E23](https://dlmf.nist.gov/28.2.E23): [`DLMF.Mathieu.mathieuA_zero`](DLMF/Mathieu/Properties/Spectra.lean#L587) (proved).
- [28.2.E24](https://dlmf.nist.gov/28.2.E24): [`DLMF.Mathieu.mathieuB_zero`](DLMF/Mathieu/Properties/Spectra.lean#L596) (proved).
- [28.2.E25](https://dlmf.nist.gov/28.2.E25): [`DLMF.Mathieu.mathieu_eigenvalues_interlace_pos`](DLMF/Mathieu/Properties/Spectra.lean#L609) (admitted); [`DLMF.Mathieu.mathieu_eigenvalues_interlace_neg`](DLMF/Mathieu/Properties/Spectra.lean#L616) (admitted).
- [28.2.E26](https://dlmf.nist.gov/28.2.E26): [`DLMF.Mathieu.mathieuA_even_neg`](DLMF/Mathieu/Properties/Spectra.lean#L626) (proved).
- [28.2.E27](https://dlmf.nist.gov/28.2.E27): [`DLMF.Mathieu.mathieuA_odd_neg`](DLMF/Mathieu/Properties/Spectra.lean#L634) (proved).
- [28.2.E28](https://dlmf.nist.gov/28.2.E28): [`DLMF.Mathieu.mathieuB_even_neg`](DLMF/Mathieu/Properties/Spectra.lean#L644) (proved).
- [28.2.E29](https://dlmf.nist.gov/28.2.E29): [`DLMF.Mathieu.mathieuCe_zero_zero`](DLMF/Mathieu/Properties/Eigenfunctions.lean#L359) (proved); [`DLMF.Mathieu.mathieuCe_q_zero`](DLMF/Mathieu/Properties/Eigenfunctions.lean#L371) (proved); [`DLMF.Mathieu.mathieuSe_q_zero`](DLMF/Mathieu/Properties/Eigenfunctions.lean#L379) (proved).
- [28.2.E30](https://dlmf.nist.gov/28.2.E30): [`DLMF.Mathieu.integral_mathieuCe_sq`](DLMF/Mathieu/Properties/Eigenfunctions.lean#L391) (proved); [`DLMF.Mathieu.integral_mathieuSe_sq`](DLMF/Mathieu/Properties/Eigenfunctions.lean#L399) (proved).
- [28.2.E31](https://dlmf.nist.gov/28.2.E31): [`DLMF.Mathieu.integral_mathieuCe_mul_mathieuCe`](DLMF/Mathieu/Properties/Eigenfunctions.lean#L406) (proved).
- [28.2.E32](https://dlmf.nist.gov/28.2.E32): [`DLMF.Mathieu.integral_mathieuSe_mul_mathieuSe`](DLMF/Mathieu/Properties/Eigenfunctions.lean#L414) (proved).
- [28.2.E33](https://dlmf.nist.gov/28.2.E33): [`DLMF.Mathieu.integral_mathieuCe_mul_mathieuSe`](DLMF/Mathieu/Properties/Eigenfunctions.lean#L444) (proved).
- [28.2.E34](https://dlmf.nist.gov/28.2.E34): [`DLMF.Mathieu.mathieuCe_even_neg_q`](DLMF/Mathieu/Properties/Eigenfunctions.lean#L503) (proved).
- [28.2.E35](https://dlmf.nist.gov/28.2.E35): [`DLMF.Mathieu.mathieuCe_odd_neg_q`](DLMF/Mathieu/Properties/Eigenfunctions.lean#L526) (proved).
- [28.2.E36](https://dlmf.nist.gov/28.2.E36): [`DLMF.Mathieu.mathieuSe_odd_neg_q`](DLMF/Mathieu/Properties/Eigenfunctions.lean#L551) (proved).
- [28.2.E37](https://dlmf.nist.gov/28.2.E37): [`DLMF.Mathieu.mathieuSe_even_neg_q`](DLMF/Mathieu/Properties/Eigenfunctions.lean#L580) (proved).
- [28.2.E38](https://dlmf.nist.gov/28.2.E38): [`DLMF.Mathieu.mathieuCe_div_mathieuCe_zero`](DLMF/Mathieu/Properties/Eigenfunctions.lean#L70) (proved).
- [28.2.E39](https://dlmf.nist.gov/28.2.E39): [`DLMF.Mathieu.mathieuSe_div_deriv_mathieuSe_zero`](DLMF/Mathieu/Properties/Eigenfunctions.lean#L78) (proved).
- [28.2.T1](https://dlmf.nist.gov/28.2.T1): [`DLMF.Mathieu.mathieuSpecA`](DLMF/Mathieu/Basic/Spectral.lean#L29) (definition); [`DLMF.Mathieu.mathieuSpecB`](DLMF/Mathieu/Basic/Spectral.lean#L36) (definition); [`DLMF.Mathieu.mathieuA`](DLMF/Mathieu/Basic/Spectral.lean#L43) (definition); [`DLMF.Mathieu.mathieuB`](DLMF/Mathieu/Basic/Spectral.lean#L50) (definition); [`DLMF.Mathieu.exists_solution_neumann_iff`](DLMF/Mathieu/Properties/Spectra.lean#L121) (proved); [`DLMF.Mathieu.exists_solution_neumann_dirichlet_iff`](DLMF/Mathieu/Properties/Spectra.lean#L167) (proved); [`DLMF.Mathieu.exists_solution_dirichlet_neumann_iff`](DLMF/Mathieu/Properties/Spectra.lean#L199) (proved); [`DLMF.Mathieu.exists_solution_dirichlet_iff`](DLMF/Mathieu/Properties/Spectra.lean#L245) (proved).
- [28.2.T2](https://dlmf.nist.gov/28.2.T2): [`DLMF.Mathieu.mathieuCe`](DLMF/Mathieu/Basic/Functions.lean#L33) (definition); [`DLMF.Mathieu.mathieuSe`](DLMF/Mathieu/Basic/Functions.lean#L41) (definition); [`DLMF.Mathieu.mathieuCe_neg`](DLMF/Mathieu/Properties/Eigenfunctions.lean#L131) (proved); [`DLMF.Mathieu.mathieuSe_neg`](DLMF/Mathieu/Properties/Eigenfunctions.lean#L136) (proved); [`DLMF.Mathieu.mathieuCe_even_add_pi`](DLMF/Mathieu/Properties/Eigenfunctions.lean#L141) (proved); [`DLMF.Mathieu.mathieuCe_odd_add_pi`](DLMF/Mathieu/Properties/Eigenfunctions.lean#L148) (proved); [`DLMF.Mathieu.mathieuSe_odd_add_pi`](DLMF/Mathieu/Properties/Eigenfunctions.lean#L155) (proved); [`DLMF.Mathieu.mathieuSe_even_add_pi`](DLMF/Mathieu/Properties/Eigenfunctions.lean#L162) (proved).

## [§28.4 Fourier Series](https://dlmf.nist.gov/28.4)

- [28.4.i](https://dlmf.nist.gov/28.4.i): [`DLMF.Mathieu.mathieu_fourier_locallyUniform`](DLMF/Mathieu/FourierSeries.lean#L484) (proved).
- [28.4.iii](https://dlmf.nist.gov/28.4.iii): [`DLMF.Mathieu.mathieuFourier_sign`](DLMF/Mathieu/FourierSeries.lean#L685) (proved).
- [28.4.E1](https://dlmf.nist.gov/28.4.E1): [`DLMF.Mathieu.mathieuFourierA`](DLMF/Mathieu/Basic/Functions.lean#L118) (definition); [`DLMF.Mathieu.hasSum_mathieuCe_even`](DLMF/Mathieu/FourierSeries.lean#L327) (proved).
- [28.4.E2](https://dlmf.nist.gov/28.4.E2): [`DLMF.Mathieu.hasSum_mathieuCe_odd`](DLMF/Mathieu/FourierSeries.lean#L341) (proved).
- [28.4.E3](https://dlmf.nist.gov/28.4.E3): [`DLMF.Mathieu.mathieuFourierB`](DLMF/Mathieu/Basic/Functions.lean#L126) (definition); [`DLMF.Mathieu.hasSum_mathieuSe_odd`](DLMF/Mathieu/FourierSeries.lean#L355) (proved).
- [28.4.E4](https://dlmf.nist.gov/28.4.E4): [`DLMF.Mathieu.hasSum_mathieuSe_even`](DLMF/Mathieu/FourierSeries.lean#L369) (proved).
- [28.4.E5](https://dlmf.nist.gov/28.4.E5): [`DLMF.Mathieu.mathieuFourierA_even_rec_zero`](DLMF/Mathieu/FourierSeries.lean#L512) (proved); [`DLMF.Mathieu.mathieuFourierA_even_rec_one`](DLMF/Mathieu/FourierSeries.lean#L524) (proved); [`DLMF.Mathieu.mathieuFourierA_even_rec`](DLMF/Mathieu/FourierSeries.lean#L535) (proved).
- [28.4.E6](https://dlmf.nist.gov/28.4.E6): [`DLMF.Mathieu.mathieuFourierA_odd_rec_zero`](DLMF/Mathieu/FourierSeries.lean#L550) (proved); [`DLMF.Mathieu.mathieuFourierA_odd_rec`](DLMF/Mathieu/FourierSeries.lean#L560) (proved).
- [28.4.E7](https://dlmf.nist.gov/28.4.E7): [`DLMF.Mathieu.mathieuFourierB_odd_rec_zero`](DLMF/Mathieu/FourierSeries.lean#L577) (proved); [`DLMF.Mathieu.mathieuFourierB_odd_rec`](DLMF/Mathieu/FourierSeries.lean#L587) (proved).
- [28.4.E8](https://dlmf.nist.gov/28.4.E8): [`DLMF.Mathieu.mathieuFourierB_even_rec_zero`](DLMF/Mathieu/FourierSeries.lean#L603) (proved); [`DLMF.Mathieu.mathieuFourierB_even_rec`](DLMF/Mathieu/FourierSeries.lean#L613) (proved).
- [28.4.E9](https://dlmf.nist.gov/28.4.E9): [`DLMF.Mathieu.hasSum_mathieuFourierA_even_sq`](DLMF/Mathieu/FourierSeries.lean#L631) (proved).
- [28.4.E10](https://dlmf.nist.gov/28.4.E10): [`DLMF.Mathieu.hasSum_mathieuFourierA_odd_sq`](DLMF/Mathieu/FourierSeries.lean#L644) (proved).
- [28.4.E11](https://dlmf.nist.gov/28.4.E11): [`DLMF.Mathieu.hasSum_mathieuFourierB_odd_sq`](DLMF/Mathieu/FourierSeries.lean#L657) (proved).
- [28.4.E12](https://dlmf.nist.gov/28.4.E12): [`DLMF.Mathieu.hasSum_mathieuFourierB_even_sq`](DLMF/Mathieu/FourierSeries.lean#L670) (proved).
- [28.4.E13](https://dlmf.nist.gov/28.4.E13): [`DLMF.Mathieu.mathieuFourierA_even_q_zero`](DLMF/Mathieu/FourierSeries.lean#L705) (proved).
- [28.4.E14](https://dlmf.nist.gov/28.4.E14): [`DLMF.Mathieu.mathieuFourierA_odd_q_zero`](DLMF/Mathieu/FourierSeries.lean#L736) (proved).
- [28.4.E15](https://dlmf.nist.gov/28.4.E15): [`DLMF.Mathieu.mathieuFourierB_odd_q_zero`](DLMF/Mathieu/FourierSeries.lean#L745) (proved).
- [28.4.E16](https://dlmf.nist.gov/28.4.E16): [`DLMF.Mathieu.mathieuFourierB_even_q_zero`](DLMF/Mathieu/FourierSeries.lean#L754) (proved).
- [28.4.E17](https://dlmf.nist.gov/28.4.E17): [`DLMF.Mathieu.mathieuFourierA_even_neg_q`](DLMF/Mathieu/FourierSeries.lean#L765) (proved).
- [28.4.E18](https://dlmf.nist.gov/28.4.E18): [`DLMF.Mathieu.mathieuFourierB_even_neg_q`](DLMF/Mathieu/FourierSeries.lean#L784) (proved).
- [28.4.E19](https://dlmf.nist.gov/28.4.E19): [`DLMF.Mathieu.mathieuFourierA_odd_neg_q`](DLMF/Mathieu/FourierSeries.lean#L804) (proved).
- [28.4.E20](https://dlmf.nist.gov/28.4.E20): [`DLMF.Mathieu.mathieuFourierB_odd_neg_q`](DLMF/Mathieu/FourierSeries.lean#L823) (proved).
- [28.4.E21](https://dlmf.nist.gov/28.4.E21): [`DLMF.Mathieu.mathieuFourierA_zero_small_q`](DLMF/Mathieu/FourierSeries.lean#L844) (admitted).
- [28.4.E22](https://dlmf.nist.gov/28.4.E22): [`DLMF.Mathieu.mathieuFourierA_up_small_q`](DLMF/Mathieu/FourierSeries.lean#L853) (admitted); [`DLMF.Mathieu.mathieuFourierB_up_small_q`](DLMF/Mathieu/FourierSeries.lean#L863) (admitted).
- [28.4.E23](https://dlmf.nist.gov/28.4.E23): [`DLMF.Mathieu.mathieuFourierA_down_small_q`](DLMF/Mathieu/FourierSeries.lean#L873) (admitted); [`DLMF.Mathieu.mathieuFourierB_down_small_q`](DLMF/Mathieu/FourierSeries.lean#L883) (admitted).
- [28.4.E24](https://dlmf.nist.gov/28.4.E24): [`DLMF.Mathieu.mathieuFourierA_even_large_m`](DLMF/Mathieu/FourierSeries.lean#L895) (admitted).
- [28.4.E25](https://dlmf.nist.gov/28.4.E25): [`DLMF.Mathieu.mathieuFourierA_odd_large_m`](DLMF/Mathieu/FourierSeries.lean#L905) (admitted).
- [28.4.E26](https://dlmf.nist.gov/28.4.E26): [`DLMF.Mathieu.mathieuFourierB_odd_large_m`](DLMF/Mathieu/FourierSeries.lean#L916) (admitted).
- [28.4.E27](https://dlmf.nist.gov/28.4.E27): [`DLMF.Mathieu.mathieuFourierB_even_large_m`](DLMF/Mathieu/FourierSeries.lean#L927) (admitted).

## [§28.5 Second Solutions fe_n, ge_n](https://dlmf.nist.gov/28.5)

- [28.5.i](https://dlmf.nist.gov/28.5.i): [`DLMF.Mathieu.mathieu_ince`](DLMF/Mathieu/SecondSolutions.lean#L308) (proved); [`DLMF.Mathieu.mathieuFeC_ne_zero`](DLMF/Mathieu/SecondSolutions.lean#L816) (proved); [`DLMF.Mathieu.mathieuGeS_ne_zero`](DLMF/Mathieu/SecondSolutions.lean#L889) (proved); [`DLMF.Mathieu.mathieuFeF_unique`](DLMF/Mathieu/SecondSolutions.lean#L989) (proved); [`DLMF.Mathieu.mathieuGeG_unique`](DLMF/Mathieu/SecondSolutions.lean#L1021) (proved); [`DLMF.Mathieu.mathieuFeC_mathieuGeS_tendsto`](DLMF/Mathieu/SecondSolutions.lean#L1071) (admitted); [`DLMF.Mathieu.mathieu_secular_unbounded`](DLMF/Mathieu/SecondSolutions.lean#L1264) (proved).
- [28.5.E1](https://dlmf.nist.gov/28.5.E1): [`DLMF.Mathieu.mathieuFe`](DLMF/Mathieu/Basic/Functions.lean#L77) (definition); [`DLMF.Mathieu.mathieuFeC`](DLMF/Mathieu/Basic/Functions.lean#L91) (definition); [`DLMF.Mathieu.mathieuFe_eq`](DLMF/Mathieu/SecondSolutions.lean#L324) (proved).
- [28.5.E2](https://dlmf.nist.gov/28.5.E2): [`DLMF.Mathieu.mathieuGe`](DLMF/Mathieu/Basic/Functions.lean#L84) (definition); [`DLMF.Mathieu.mathieuGeS`](DLMF/Mathieu/Basic/Functions.lean#L98) (definition); [`DLMF.Mathieu.mathieuGe_eq`](DLMF/Mathieu/SecondSolutions.lean#L331) (proved).
- [28.5.E3](https://dlmf.nist.gov/28.5.E3): [`DLMF.Mathieu.mathieuFeF`](DLMF/Mathieu/Basic/Functions.lean#L104) (definition); [`DLMF.Mathieu.mathieuFeF_periodicity`](DLMF/Mathieu/SecondSolutions.lean#L961) (proved).
- [28.5.E4](https://dlmf.nist.gov/28.5.E4): [`DLMF.Mathieu.mathieuGeG`](DLMF/Mathieu/Basic/Functions.lean#L110) (definition); [`DLMF.Mathieu.mathieuGeG_periodicity`](DLMF/Mathieu/SecondSolutions.lean#L975) (proved).
- [28.5.E5](https://dlmf.nist.gov/28.5.E5): [`DLMF.Mathieu.mathieuFe_mathieuGe_normalization`](DLMF/Mathieu/SecondSolutions.lean#L1062) (proved).
- [28.5.E6](https://dlmf.nist.gov/28.5.E6): [`DLMF.Mathieu.mathieuFeC_even_neg`](DLMF/Mathieu/SecondSolutions.lean#L1083) (proved); [`DLMF.Mathieu.mathieuFeC_odd_neg`](DLMF/Mathieu/SecondSolutions.lean#L1132) (proved); [`DLMF.Mathieu.mathieuGeS_even_neg`](DLMF/Mathieu/SecondSolutions.lean#L1182) (proved). The second relation is acquired corrected as `C_{2m+1}(−q) = −S_{2m+1}(q)` (see source corrections).
- [28.5.E7](https://dlmf.nist.gov/28.5.E7): [`DLMF.Mathieu.mathieuFe_zero_zero`](DLMF/Mathieu/SecondSolutions.lean#L1228) (proved); [`DLMF.Mathieu.mathieuFe_q_zero`](DLMF/Mathieu/SecondSolutions.lean#L1233) (proved); [`DLMF.Mathieu.mathieuGe_q_zero`](DLMF/Mathieu/SecondSolutions.lean#L1250) (proved).
- [28.5.E8](https://dlmf.nist.gov/28.5.E8): [`DLMF.Mathieu.mathieuCe_mathieuFe_wronskian`](DLMF/Mathieu/SecondSolutions.lean#L1357) (proved).
- [28.5.E9](https://dlmf.nist.gov/28.5.E9): [`DLMF.Mathieu.mathieuSe_mathieuGe_wronskian`](DLMF/Mathieu/SecondSolutions.lean#L1372) (proved).

## [§28.6 Expansions for Small q](https://dlmf.nist.gov/28.6)

- [28.6.ii](https://dlmf.nist.gov/28.6.ii): [`DLMF.Mathieu.mathieuSe_small_q`](DLMF/Mathieu/SmallQ.lean#L1348) (proved); [`DLMF.Mathieu.mathieuCe_radius_eq`](DLMF/Mathieu/SmallQ.lean#L1364) (admitted); [`DLMF.Mathieu.mathieuSe_radius_eq`](DLMF/Mathieu/SmallQ.lean#L1375) (admitted).
- [28.6.E1](https://dlmf.nist.gov/28.6.E1): [`DLMF.Mathieu.mathieuA_zero_small_q`](DLMF/Mathieu/SmallQ.lean#L58) (proved).
- [28.6.E2](https://dlmf.nist.gov/28.6.E2): [`DLMF.Mathieu.mathieuA_one_small_q`](DLMF/Mathieu/SmallQ.lean#L138) (proved).
- [28.6.E3](https://dlmf.nist.gov/28.6.E3): [`DLMF.Mathieu.mathieuB_one_small_q`](DLMF/Mathieu/SmallQ.lean#L230) (proved).
- [28.6.E4](https://dlmf.nist.gov/28.6.E4): [`DLMF.Mathieu.mathieuA_two_small_q`](DLMF/Mathieu/SmallQ.lean#L322) (proved).
- [28.6.E5](https://dlmf.nist.gov/28.6.E5): [`DLMF.Mathieu.mathieuB_two_small_q`](DLMF/Mathieu/SmallQ.lean#L417) (proved).
- [28.6.E6](https://dlmf.nist.gov/28.6.E6): [`DLMF.Mathieu.mathieuA_three_small_q`](DLMF/Mathieu/SmallQ.lean#L501) (proved).
- [28.6.E7](https://dlmf.nist.gov/28.6.E7): [`DLMF.Mathieu.mathieuB_three_small_q`](DLMF/Mathieu/SmallQ.lean#L589) (proved).
- [28.6.E8](https://dlmf.nist.gov/28.6.E8): [`DLMF.Mathieu.mathieuA_four_small_q`](DLMF/Mathieu/SmallQ.lean#L677) (proved).
- [28.6.E9](https://dlmf.nist.gov/28.6.E9): [`DLMF.Mathieu.mathieuB_four_small_q`](DLMF/Mathieu/SmallQ.lean#L757) (proved).
- [28.6.E10](https://dlmf.nist.gov/28.6.E10): [`DLMF.Mathieu.mathieuA_five_small_q`](DLMF/Mathieu/SmallQ.lean#L831) (proved).
- [28.6.E11](https://dlmf.nist.gov/28.6.E11): [`DLMF.Mathieu.mathieuB_five_small_q`](DLMF/Mathieu/SmallQ.lean#L912) (proved).
- [28.6.E12](https://dlmf.nist.gov/28.6.E12): [`DLMF.Mathieu.mathieuA_six_small_q`](DLMF/Mathieu/SmallQ.lean#L993) (proved).
- [28.6.E13](https://dlmf.nist.gov/28.6.E13): [`DLMF.Mathieu.mathieuB_six_small_q`](DLMF/Mathieu/SmallQ.lean#L1082) (proved).
- [28.6.E14](https://dlmf.nist.gov/28.6.E14): [`DLMF.Mathieu.mathieuA_small_q`](DLMF/Mathieu/SmallQ.lean#L1165) (proved); [`DLMF.Mathieu.mathieuB_small_q`](DLMF/Mathieu/SmallQ.lean#L1181) (proved).
- [28.6.E15](https://dlmf.nist.gov/28.6.E15): [`DLMF.Mathieu.mathieuA_sub_mathieuB_small_q`](DLMF/Mathieu/SmallQ.lean#L1196) (admitted).
- [28.6.E16](https://dlmf.nist.gov/28.6.E16): [`DLMF.Mathieu.mathieuA_even_contFrac`](DLMF/Mathieu/SmallQ.lean#L1206) (admitted); [`DLMF.Mathieu.mathieuA_zero_contFrac`](DLMF/Mathieu/SmallQ.lean#L1219) (admitted). Stated for `n ≥ 1`; for `n = 0` a separate version carries the factor 2.
- [28.6.E17](https://dlmf.nist.gov/28.6.E17): [`DLMF.Mathieu.mathieuA_odd_contFrac`](DLMF/Mathieu/SmallQ.lean#L1227) (admitted).
- [28.6.E18](https://dlmf.nist.gov/28.6.E18): [`DLMF.Mathieu.mathieuB_odd_contFrac`](DLMF/Mathieu/SmallQ.lean#L1240) (admitted).
- [28.6.E19](https://dlmf.nist.gov/28.6.E19): [`DLMF.Mathieu.mathieuB_even_contFrac`](DLMF/Mathieu/SmallQ.lean#L1253) (admitted).
- [28.6.E20](https://dlmf.nist.gov/28.6.E20): [`DLMF.Mathieu.mathieu_radius_liminf`](DLMF/Mathieu/SmallQ.lean#L1265) (admitted).
- [28.6.E21](https://dlmf.nist.gov/28.6.E21): [`DLMF.Mathieu.mathieuCe_zero_small_q`](DLMF/Mathieu/SmallQ.lean#L1283) (proved).
- [28.6.E22](https://dlmf.nist.gov/28.6.E22): [`DLMF.Mathieu.mathieuCe_one_small_q`](DLMF/Mathieu/SmallQ.lean#L1293) (proved).
- [28.6.E23](https://dlmf.nist.gov/28.6.E23): [`DLMF.Mathieu.mathieuSe_one_small_q`](DLMF/Mathieu/SmallQ.lean#L1303) (proved).
- [28.6.E24](https://dlmf.nist.gov/28.6.E24): [`DLMF.Mathieu.mathieuCe_two_small_q`](DLMF/Mathieu/SmallQ.lean#L1313) (proved).
- [28.6.E25](https://dlmf.nist.gov/28.6.E25): [`DLMF.Mathieu.mathieuSe_two_small_q`](DLMF/Mathieu/SmallQ.lean#L1323) (proved).
- [28.6.E26](https://dlmf.nist.gov/28.6.E26): [`DLMF.Mathieu.mathieuCe_small_q`](DLMF/Mathieu/SmallQ.lean#L1332) (proved).

## [§28.7 Analytic Continuation of Eigenvalues](https://dlmf.nist.gov/28.7)

- [28.7](https://dlmf.nist.gov/28.7): [`DLMF.Mathieu.mathieu_exceptional_values`](DLMF/Mathieu/Continuation.lean#L34) (admitted); [`DLMF.Mathieu.mathieuA_mathieuB_analytic`](DLMF/Mathieu/Continuation.lean#L51) (admitted); [`DLMF.Mathieu.mathieu_eigenEquation_irreducible`](DLMF/Mathieu/Continuation.lean#L62) (admitted).
- [28.7.E1](https://dlmf.nist.gov/28.7.E1): [`DLMF.Mathieu.hasSum_mathieuA_even_sub`](DLMF/Mathieu/Continuation.lean#L74) (admitted).
- [28.7.E2](https://dlmf.nist.gov/28.7.E2): [`DLMF.Mathieu.hasSum_mathieuA_odd_sub`](DLMF/Mathieu/Continuation.lean#L80) (admitted).
- [28.7.E3](https://dlmf.nist.gov/28.7.E3): [`DLMF.Mathieu.hasSum_mathieuB_odd_sub`](DLMF/Mathieu/Continuation.lean#L86) (admitted).
- [28.7.E4](https://dlmf.nist.gov/28.7.E4): [`DLMF.Mathieu.hasSum_mathieuB_even_sub`](DLMF/Mathieu/Continuation.lean#L92) (admitted).

## [§28.8 Asymptotic Expansions for Large q](https://dlmf.nist.gov/28.8)

- [28.8.E1](https://dlmf.nist.gov/28.8.E1): [`DLMF.Mathieu.mathieuA_large_q`](DLMF/Mathieu/LargeQ.lean#L41) (admitted); [`DLMF.Mathieu.mathieuB_large_q`](DLMF/Mathieu/LargeQ.lean#L57) (admitted).
- [28.8.E2](https://dlmf.nist.gov/28.8.E2): [`DLMF.Mathieu.mathieuB_sub_mathieuA_large_q`](DLMF/Mathieu/LargeQ.lean#L70) (admitted).
- [28.8.E3](https://dlmf.nist.gov/28.8.E3): [`DLMF.Mathieu.mathieu_sips`](DLMF/Mathieu/LargeQ.lean#L83) (admitted).
- [28.8.E4](https://dlmf.nist.gov/28.8.E4): [`DLMF.Mathieu.mathieu_sips`](DLMF/Mathieu/LargeQ.lean#L83) (admitted).
- [28.8.E5](https://dlmf.nist.gov/28.8.E5): [`DLMF.Mathieu.mathieu_sips`](DLMF/Mathieu/LargeQ.lean#L83) (admitted).
- [28.8.E6](https://dlmf.nist.gov/28.8.E6): [`DLMF.Mathieu.mathieu_sips`](DLMF/Mathieu/LargeQ.lean#L83) (admitted).
- [28.8.E7](https://dlmf.nist.gov/28.8.E7): [`DLMF.Mathieu.mathieu_sips`](DLMF/Mathieu/LargeQ.lean#L83) (admitted).
- [28.8.E8](https://dlmf.nist.gov/28.8.E8): [`DLMF.Mathieu.mathieu_goldstein`](DLMF/Mathieu/LargeQ.lean#L120) (admitted).
- [28.8.E9](https://dlmf.nist.gov/28.8.E9): [`DLMF.Mathieu.mathieu_goldstein`](DLMF/Mathieu/LargeQ.lean#L120) (admitted).
- [28.8.E10](https://dlmf.nist.gov/28.8.E10): [`DLMF.Mathieu.mathieu_goldstein`](DLMF/Mathieu/LargeQ.lean#L120) (admitted).
- [28.8.E11](https://dlmf.nist.gov/28.8.E11): [`DLMF.Mathieu.mathieu_goldstein`](DLMF/Mathieu/LargeQ.lean#L120) (admitted).
- [28.8.E12](https://dlmf.nist.gov/28.8.E12): [`DLMF.Mathieu.mathieu_goldstein`](DLMF/Mathieu/LargeQ.lean#L120) (admitted).

## [§28.9 Zeros](https://dlmf.nist.gov/28.9)

- [28.9](https://dlmf.nist.gov/28.9): [`DLMF.Mathieu.mathieu_zeros_count`](DLMF/Mathieu/Zeros.lean#L34) (proved); [`DLMF.Mathieu.mathieuCe_even_zeros_continuous`](DLMF/Mathieu/Zeros.lean#L60) (admitted); [`DLMF.Mathieu.mathieuSe_odd_zeros_continuous`](DLMF/Mathieu/Zeros.lean#L68) (admitted); [`DLMF.Mathieu.mathieuCe_odd_zeros_continuous`](DLMF/Mathieu/Zeros.lean#L75) (admitted); [`DLMF.Mathieu.mathieuSe_even_zeros_continuous`](DLMF/Mathieu/Zeros.lean#L82) (admitted); [`DLMF.Mathieu.mathieu_zeros_large_q_even`](DLMF/Mathieu/Zeros.lean#L89) (admitted); [`DLMF.Mathieu.mathieu_zeros_large_q_odd`](DLMF/Mathieu/Zeros.lean#L101) (admitted); [`DLMF.Mathieu.mathieu_imaginary_zeros`](DLMF/Mathieu/Zeros.lean#L169) (proved); [`DLMF.Mathieu.mathieu_zeros_strip`](DLMF/Mathieu/Zeros.lean#L193) (admitted).

## [§28.10 Integral Equations](https://dlmf.nist.gov/28.10)

- [28.10.E1](https://dlmf.nist.gov/28.10.E1): [`DLMF.Mathieu.integral_cos_mathieuCe_even`](DLMF/Mathieu/IntegralEquations.lean#L435) (proved).
- [28.10.E2](https://dlmf.nist.gov/28.10.E2): [`DLMF.Mathieu.integral_cosh_mathieuCe_even`](DLMF/Mathieu/IntegralEquations.lean#L556) (proved).
- [28.10.E3](https://dlmf.nist.gov/28.10.E3): [`DLMF.Mathieu.integral_sin_mathieuCe_odd`](DLMF/Mathieu/IntegralEquations.lean#L637) (proved).
- [28.10.E4](https://dlmf.nist.gov/28.10.E4): [`DLMF.Mathieu.integral_cos_cosh_mathieuCe_odd`](DLMF/Mathieu/IntegralEquations.lean#L700) (proved).
- [28.10.E5](https://dlmf.nist.gov/28.10.E5): [`DLMF.Mathieu.integral_sinh_mathieuSe_odd`](DLMF/Mathieu/IntegralEquations.lean#L769) (proved).
- [28.10.E6](https://dlmf.nist.gov/28.10.E6): [`DLMF.Mathieu.integral_sin_cos_mathieuSe_odd`](DLMF/Mathieu/IntegralEquations.lean#L834) (proved).
- [28.10.E7](https://dlmf.nist.gov/28.10.E7): [`DLMF.Mathieu.integral_sin_sin_mathieuSe_even`](DLMF/Mathieu/IntegralEquations.lean#L905) (proved).
- [28.10.E8](https://dlmf.nist.gov/28.10.E8): [`DLMF.Mathieu.integral_cos_sinh_mathieuSe_even`](DLMF/Mathieu/IntegralEquations.lean#L980) (proved).
- [28.10.E9](https://dlmf.nist.gov/28.10.E9): [`DLMF.Mathieu.integral_besselJ_mathieuCe_even`](DLMF/Mathieu/IntegralEquations.lean#L1054) (admitted).
- [28.10.E10](https://dlmf.nist.gov/28.10.E10): [`DLMF.Mathieu.integral_besselJ_mathieuCe`](DLMF/Mathieu/IntegralEquations.lean#L1064) (admitted).

## [§28.11 Expansions in Series of Mathieu Functions](https://dlmf.nist.gov/28.11)

- [28.11.E1](https://dlmf.nist.gov/28.11.E1): [`DLMF.Mathieu.hasSum_mathieu_expansion`](DLMF/Mathieu/Expansions.lean#L27) (admitted).
- [28.11.E2](https://dlmf.nist.gov/28.11.E2): [`DLMF.Mathieu.hasSum_mathieu_expansion`](DLMF/Mathieu/Expansions.lean#L27) (admitted).
- [28.11.E3](https://dlmf.nist.gov/28.11.E3): [`DLMF.Mathieu.hasSum_one_mathieuCe`](DLMF/Mathieu/Expansions.lean#L45) (admitted).
- [28.11.E4](https://dlmf.nist.gov/28.11.E4): [`DLMF.Mathieu.hasSum_cos_even_mathieuCe`](DLMF/Mathieu/Expansions.lean#L51) (admitted).
- [28.11.E5](https://dlmf.nist.gov/28.11.E5): [`DLMF.Mathieu.hasSum_cos_odd_mathieuCe`](DLMF/Mathieu/Expansions.lean#L58) (admitted).
- [28.11.E6](https://dlmf.nist.gov/28.11.E6): [`DLMF.Mathieu.hasSum_sin_odd_mathieuSe`](DLMF/Mathieu/Expansions.lean#L65) (admitted).
- [28.11.E7](https://dlmf.nist.gov/28.11.E7): [`DLMF.Mathieu.hasSum_sin_even_mathieuSe`](DLMF/Mathieu/Expansions.lean#L72) (admitted).

## Prose, informal and excluded items (part A)

- [§28.1](https://dlmf.nist.gov/28.1) Special Notation: notation only; the conventions are
  recorded above.
- [§28.3](https://dlmf.nist.gov/28.3) Graphics: excluded: graphics.
- [28.6.T1](https://dlmf.nist.gov/28.6.T1) (radii of convergence `ρ_n` of the small-q
  series) and the decimal values of the radii in §28.6(ii): excluded: numerical. The exact
  statements of §28.6(ii) (the radii of the series for `a_n` and `b_n`) are acquired.
- §28.6(ii): the conjectured monotonicity of the radii is a conjecture; not acquired.
- §28.7: the decimal values of the branch points (`q_0 = ±1.4688i`, …) are excluded:
  numerical; the exact statements are acquired under ID 28.7.
- §28.8(iv) (uniform approximations by Barrett, Dunster): informal description with references;
  not acquired.
- §28.9: the qualitative correspondence of the large-q zeros with the zeros of `J_m` is
  imprecise; not acquired. The exact zero statements are acquired under ID 28.9.
- §28.10(iii): bibliographic; not acquired.
- [§28.32](https://dlmf.nist.gov/28.32) Mathematical Applications (excluded: application).
  Mathematical content: 28.32.1–28.32.5, separation of the two-dimensional wave equation in
  elliptical coordinates into Mathieu's equation 28.2.1 and the modified equation 28.20.1;
  28.32.6–28.32.8, an integral relation between solutions of the two equations via a kernel
  satisfying the separated PDE (the source of the integral equations of §28.10); §28.32(ii),
  separation of the Helmholtz equation in paraboloidal coordinates into the Whittaker–Hill
  equation 28.31.1.
- [§28.33](https://dlmf.nist.gov/28.33) Physical Applications (excluded: application).
  Mathematical content: 28.33.1–28.33.4, the elliptical-membrane boundary-value problem for
  the wave equation, with eigenfrequencies determined by zeros of modified Mathieu functions;
  §28.33(iii), stability of initial-value problems for 28.2.1 and Hill's equation (stability
  regions bounded by the eigenvalue curves `a_n(q)`, `b_n(q)`).
- [§28.34](https://dlmf.nist.gov/28.34)–[§28.36](https://dlmf.nist.gov/28.36) Methods of
  Computation, Tables, Software: excluded: computation.
- Figures in §§28.2–28.11 and bibliographic paragraphs are not acquired.

## Validation (part A)

- All eleven modules build together with `lake build DLMF.Mathieu.<Module>` with 0 errors and
  only `sorry` warnings, and each passes
  `lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false`. Lines are at most 100
  characters. There are no axioms, no `native_decide` and no `sorry` in definitions or helper
  declarations (prefix `m28a_`); the only admissions outside acquired DLMF statements are the
  three flagged existence theorems in `Basic`.
- `#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound` for, e.g.,
  `IsMathieuSolution.eq_of_initial`, `algebraic_form_sin_sq`, `algebraic_form_cos`,
  `IsMathieuSolution.comp_add_half_pi`, `isMathieuCharExp_iff`, `isMathieuCharExp_double_iff`,
  `nthLeast_eq_of`, `mathieuFe_zero_zero`, `mathieuFe_eq`,
  `IsMathieuSolution.wronskian_eq`. Theorems about `w_I`, `w_II`, `ce_n`, `se_n` proved in
  Lean (e.g. `mathieuWI_pi_eq_deriv_mathieuWII_pi`, `IsMathieuSolution.isFloquet_or`) also
  show `sorryAx` through the admitted existence theorem `exists_isMathieuSolution`.
- DLMF.lean, the area umbrella, the lakefile and the other ledgers are unchanged (the
  coordinator adds the umbrella).

# Part B: §§28.12–28.19 and §§28.29–28.31 (ACQ28B)

Part B (agent ACQ28B, 2026-10-26) covers §§28.12–28.19, Mathieu functions of noninteger order,
and §§28.29–28.31, Hill's equation; the gap §§28.20–28.28 (modified Mathieu functions) is part
C, below. The Lean code is in `DLMF/Mathieu/Noninteger/` and `DLMF/Mathieu/Hill/` (namespace
`DLMF.Mathieu`, helper prefix `m28b_`); the modules, in import order, are
[Noninteger/Basic](DLMF/Mathieu/Noninteger/Basic.lean) (imports `DLMF.Mathieu.Basic`),
[Noninteger/Properties](DLMF/Mathieu/Noninteger/Properties.lean) (§28.12),
[Noninteger/Fourier](DLMF/Mathieu/Noninteger/Fourier.lean) (§28.14),
[Noninteger/Expansions](DLMF/Mathieu/Noninteger/Expansions.lean) (§§28.15–28.17, 28.19),
[Hill/Basic](DLMF/Mathieu/Hill/Basic.lean) (Mathlib only),
[Hill/Floquet](DLMF/Mathieu/Hill/Floquet.lean) (§28.29; uses Hill/Basic and the global, parameter-dependent and spectral ODE APIs in
`DLMFMathlib.Analysis.ODE`),
[Hill/Eigenfunctions](DLMF/Mathieu/Hill/Eigenfunctions.lean) (§28.30) and
[Hill/Ince](DLMF/Mathieu/Hill/Ince.lean) (§28.31; uses Hill/Basic, `DLMF.Mathieu.SpectralExistence` and
`DLMF.Mathieu.Noninteger.Properties`). Nothing is upstream (Mathlib and TauCeti have no Mathieu, Hill or Ince
functions), so there is no `dlmf_upstream` file for part B.

**Counts (part B).** The in-scope sections have 83 numbered equations (§28.12: 15, §28.14: 10,
§28.15: 3, §28.16: 1, §28.19: 4, §28.29: 22, §28.30: 4, §28.31: 24); §28.17 has prose only and
§28.18 only refers to §28.28. Excluded: §28.13 (Figures 28.13.1–28.13.5) and Figure 28.17.1
(graphics); no numerical items occur. Covered: all 83 numbered equations, plus 10 prose IDs
(28.12.i, 28.12.ii, 28.12.iii, 28.17, 28.29.i, 28.29.ii, 28.29.iii, 28.30.i, 28.31.ii,
28.31.iii); 93 DLMF IDs are tagged on 113 declarations: 22 definitions, 24 proved theorems,
9 theorems proved from admissions and 58 direct admissions (`grep -c sorry`: Noninteger/Basic 0,
Properties 8, Fourier 3, Expansions 10, Hill/Basic 0, Floquet 19, Eigenfunctions 2, Ince 16).
The untagged helpers (unfolding lemmas, `m28b_` transport lemmas, closure lemmas of Hill
solutions) are all proved.

## Part B: design, domains and source corrections

- **`λ_ν(q)`, `me_ν`, `c^ν_{2m}` (definitions by choice).** DLMF defines `λ_ν(q)` "by analytic
  continuation" from `λ_ν(0) = ν²` and fixes the sign of the Fourier coefficients "by
  continuity" from `c^ν_0(0) = 1`. `IsMeCoeffSeq ν q a c` says that `c : ℤ → ℂ` is an
  absolutely summable solution of the recurrence 28.14.4 normalized by 28.14.5
  (`∑ c² = 1`, equivalent to 28.12.5). A continuation path (`IsMathieuLambdaPath`) is a pair
  `(Λ, c)` continuous on `[0, 1]` with `Λ 0 = ν²`, `c 0 0 = 1` and `IsMeCoeffSeq ν (t q) (Λ t)
  (c t)` for every `t`: continuation along the straight segment `[0, q]`.
  `MathieuNormalSegment ν q` says that such a path exists and its endpoint is unique; the
  endpoint is `(λ_ν(q), c^ν(q))`, else the junk value `(0, 0)`. `mathieuMe ν z q` is the
  Fourier series 28.14.1 with these coefficients. This hypothesis replaces DLMF's "q a normal
  value" (it is normality along the whole segment, stronger than pointwise normality); for
  real `ν ∉ ℤ` and real `q` it holds (`mathieuNormalSegment_real`, admitted), and at `q = 0`
  it is proved.
- For integer `ν = m`, DLMF's completions 28.12.3 and 28.12.11 are used, with ACQ28A's
  `mathieuA`, `mathieuB`, `mathieuCe`, `mathieuSe`, which exist for real `q` only; for
  integer `ν` and nonreal `q`, `mathieuLambda` and `mathieuMe` are junk `0`. For integer `ν`
  the coefficients `mathieuMeCoeff` are the Fourier coefficients `π⁻¹ ∫₀^π me_ν e^{-i(ν+2m)x}`.
  `mathieuCeNu`, `mathieuSeNu` are 28.12.12–28.12.13 for every `ν` (used for `ν ∉ ℤ`).
- **Restriction `ν ∉ ℤ`.** All of §28.12(ii)–(iii) and §28.14 is stated for `ν ∉ ℤ`, as DLMF's
  §28.12 restricts `ν̂ ≠ 0, 1`. Several formulas are false for integer `ν` with DLMF's own
  completion (28.12.2: `λ_1(-q) = a_1(-q) = b_1(q) ≠ λ_1(q)`; 28.12.8: `me_{-n} = -√2 i se_n ≠
  √2 ce_n(-z)`), so this is a domain statement, not a correction.
- **Proved from the definitions:** the `q = 0` values 28.12.1, 28.12.4, 28.14.9 (a continuous
  path in the countable set `{(ν + 2m)²}` is constant, `Set.Countable.isTotallyDisconnected`);
  the symmetries 28.12.2, 28.12.8, 28.12.9, 28.12.10, 28.12.14, 28.12.15, 28.14.7, 28.14.8 by
  transporting continuation paths along the involutions `c_m ↦ c_{-m}`, `c_m ↦ (-1)^m c_m`,
  and complex conjugation (`m28b_data_transport`); 28.12.6; 28.14.4–28.14.5; reality of
  `ce_ν`, `se_ν`; convergence of 28.14.1 on the real axis.
- **Stronger than DLMF, 28.12.10.** DLMF warns that 28.12.10 fails across cuts on the real
  `q`-axis for special complex `ν`; with the straight-segment continuation it holds for all
  `ν ∉ ℤ` and all `q` (proved).
- Expansions printed with finitely many terms and "⋯" (28.15.1, 28.15.3, 28.16.1) are stated as
  `O`-bounds of the remainder after the printed terms (`O(q⁸)`, `O(q³)`, `O(h⁻⁶)`); 28.14.6 as
  `c_{2m}/c_{2m∓2} + q/(4m²) = O(m⁻³)`; 28.14.10 as `c_{2m} - (leading term) c_0 = O(q^{m+2})`.
  The continued fractions of 28.15.2 are limits of their approximants (`mathieuContFrac`).
- **Hill's equation.** Real variable, `Q : ℝ → ℂ` continuous, `π`-periodic, mean zero
  (`IsHillPotential`; DLMF's "minimum period π" is not required); this covers DLMF's real
  continuous and strip-analytic cases on the real axis. `IsHillSolution` records genuine
  derivatives. Uniqueness of solutions is proved (DLMFMathlib `ODE.eq_of_linear_ode`); global
  existence is the flagged admitted theorem `hill_exists_solution` (DLMFMathlib has existence
  on compact intervals only). `hillWI`, `hillWII` are definitions by choice; 28.29.4–28.29.5
  and the symmetric-case parities are proved from the existence theorem.
- **`λ_n`, `μ_n` (definition by counting).** `hillPeriodicEigenvalue Q n` and
  `hillAntiperiodicEigenvalue Q n` (real `Q`) are `inf {t | N(t) ≥ n + 1}` resp. `≥ n`, where
  `N(t)` counts the real `λ ≤ t` with nontrivial solutions of multiplier `+1` (resp. `-1`),
  each with the dimension of its solution space; this is DLMF's listing with multiplicity
  (`λ_{2m-1} = λ_{2m}` at coexistence). DLMF's "a solution of period `2π` iff `λ = μ_n`" means
  antiperiodic solutions; stated so. `λ̂_m` (28.30) merges them in the order 28.29.18, and the
  eigenfunctions of 28.30 are any orthonormal family (`IsHillEigenfunctionFamily`; DLMF's
  `w_m` are such a choice). "`f''` square integrable" (28.30) is formalized as `f'` absolutely
  continuous with derivative in `L²(0, 2π)`.
- **Ince polynomials (definitions by choice).** For real `ξ` and natural `p`, `inceA p m ξ`
  (`a_p^m(ξ)`) is the unique real `η` for which Ince's equation has a nontrivial cosine Ince
  polynomial solution (frequencies `k ≤ p`, `k ≡ p mod 2`, real coefficients) with exactly `m`
  zeros in `[0, π)` — DLMF's ordering by zeros; `inceC p m z ξ` is the unique such polynomial
  normalized by 28.31.12 with `C_p^m(0, ξ) > 0`. `inceB`, `inceS` likewise (zero at `0`
  counted, `S_p^m'(0, ξ) > 0`). Inadmissible indices give junk `0`. The Fourier-series
  solutions 28.31.4–28.31.9 (DLMF: "formal") are stated for coefficients with
  `∑ ‖A_k‖ (k+1)² e^{kR} < ∞` for all `R` (`IsEntireFourierCoeff`), as an equivalence between
  the equation and the recurrences. The reduction 28.31.2 is proved for all complex parameters
  with `ξ² = -4k²c²` (DLMF: `k² < 0`); 28.31.18 is proved from it. In 28.31.22–28.31.24 the
  `u`-integral runs along `u₀ + it`, `t ≥ 0`, with DLMF's `u₀ = 0` (`ξ > 0`) or `½π`
  (`ξ < 0`); the constant factor `i` of `du` is dropped.

Source corrections and checks (scripts in the agent's scratch directory `acq28b/py`):

- **§28.31(iii), Asymptotic Behavior, second paragraph (erratum).** DLMF: for `ξ > 0`,
  `hc_p^m(z, -ξ)`, `hs_p^m(z, -ξ)` behave as multiples of `exp(¼ξ cos 2z)(cos z)^{-p-2}` as
  `z → ½π ± i∞`, the other periodic solutions as multiples of `exp(-¼ξ cos 2z)(cos z)^p`. By
  28.31.19–28.31.20 (`z ↦ ½π - z` maps `cos 2z ↦ -cos 2z`, `cos z ↦ sin z`) and the first
  paragraph, the factors are `exp(¼ξ cos 2z)(sin z)^p` and `exp(-¼ξ cos 2z)(sin z)^{-p-2}`.
  Numerically (`ξ = 0.8`, `p = 2, 3, 4`, all `m`, `z = ½π + iy`, `y = 2, 3, 4`) the ratio
  `hc_p^m(z, -ξ)/(exp(¼ξ cos 2z)(sin z)^p)` converges (`-0.416, -0.472, -0.480` for
  `hc_2^0`), while the ratio with DLMF's factor grows like `e^{(2p+2)y}` (`-1.0·10³, -4.8·10⁵,
  -2.0·10⁸`). The corrected form is acquired (`paraboloidal_asymptotic_neg`).
- Checked numerically and found correct: 28.14.6, 28.14.10, 28.15.1 (error `≈ 4·10⁻¹³` at
  `q = 0.05`), the three printed orders of 28.15.3, 28.16.1 (`ν = 0.3, 0.5, 1.5, 2.4`,
  `h = 10, 20`, remainder ratio `≈ 2⁶`), the asymptotic constant `N/(4m)²` of 28.29.20–28.29.21
  against Mathieu's `a_n ≈ n² + q²/(2(n² - 1))`, 28.31.13, 28.31.19, 28.31.20 (finite
  eigenproblems, `p ≤ 6`, `ξ = 0.8`) and the first paragraph of the asymptotic behaviour;
  28.31.3 and the recurrences 28.31.6–28.31.9 were verified symbolically (sympy).

## Numbered formulas and prose items (part B)


## [§28.12 Definitions and Basic Properties](https://dlmf.nist.gov/28.12)

- [28.12.i](https://dlmf.nist.gov/28.12.i): [`DLMF.Mathieu.mathieuLambda`](DLMF/Mathieu/Noninteger/Basic.lean#L119) (definition); [`DLMF.Mathieu.isMathieuCharExp_mathieuLambda`](DLMF/Mathieu/Noninteger/Properties.lean#L922) (proved); [`DLMF.Mathieu.isMathieuCharExp_iff_exists_mathieuLambda`](DLMF/Mathieu/Noninteger/Properties.lean#L241) (admitted); [`DLMF.Mathieu.mathieuNormalSegment_real`](DLMF/Mathieu/Noninteger/Properties.lean#L250) (admitted); [`DLMF.Mathieu.not_continuousAt_mathieuLambda`](DLMF/Mathieu/Noninteger/Properties.lean#L257) (admitted). `mathieuLambda` (λ_ν(q)): straight-segment continuation from ν² (design note); characterization by 28.2.16, the set of roots `{λ_{ν+2n}}`, reality/normality for real ν, q, discontinuity at integers.
- [28.12.ii](https://dlmf.nist.gov/28.12.ii): [`DLMF.Mathieu.mathieuMe`](DLMF/Mathieu/Noninteger/Basic.lean#L130) (definition); [`DLMF.Mathieu.isFloquetSolution_mathieuMe`](DLMF/Mathieu/Noninteger/Properties.lean#L750) (proved). `mathieuMe` (me_ν): Fourier series with the continued coefficients; Floquet property admitted.
- [28.12.iii](https://dlmf.nist.gov/28.12.iii): [`DLMF.Mathieu.mathieuCeNu_mathieuSeNu_real`](DLMF/Mathieu/Noninteger/Properties.lean#L983) (proved); [`DLMF.Mathieu.mathieu_periodic_of_rational`](DLMF/Mathieu/Noninteger/Properties.lean#L1030) (proved). Reality of ce_ν, se_ν for real ν, q, x (proved from 28.12.10); periodicity 2mπ for rational ν = s/m ∉ ℤ (admitted).
- [28.12.E1](https://dlmf.nist.gov/28.12.E1): [`DLMF.Mathieu.mathieuLambda_zero`](DLMF/Mathieu/Noninteger/Properties.lean#L235) (proved). For ν ∉ ℤ; proved from the definition (the continuation at q = 0 is constant).
- [28.12.E2](https://dlmf.nist.gov/28.12.E2): [`DLMF.Mathieu.mathieuLambda_neg_q_and_neg_nu`](DLMF/Mathieu/Noninteger/Properties.lean#L348) (proved). For ν ∉ ℤ (false for integer ν with 28.12.3: λ₁(-q) = b₁(q)); proved by transporting continuation paths.
- [28.12.E3](https://dlmf.nist.gov/28.12.E3): [`DLMF.Mathieu.mathieuLambda_intCast_eq`](DLMF/Mathieu/Noninteger/Properties.lean#L356) (proved). Integer order, real q (definition completion via `mathieuLambdaInt`).
- [28.12.E4](https://dlmf.nist.gov/28.12.E4): [`DLMF.Mathieu.mathieuMe_zero`](DLMF/Mathieu/Noninteger/Properties.lean#L691) (proved). ν ∉ ℤ.
- [28.12.E5](https://dlmf.nist.gov/28.12.E5): [`DLMF.Mathieu.integral_mathieuMe_mul_neg`](DLMF/Mathieu/Noninteger/Properties.lean#L700) (proved). ν ∉ ℤ, q normal along the segment.
- [28.12.E6](https://dlmf.nist.gov/28.12.E6): [`DLMF.Mathieu.mathieuMe_add_pi`](DLMF/Mathieu/Noninteger/Properties.lean#L715) (proved). ν ∉ ℤ, all q.
- [28.12.E7](https://dlmf.nist.gov/28.12.E7): [`DLMF.Mathieu.integral_mathieuMe_orthogonal`](DLMF/Mathieu/Noninteger/Properties.lean#L728) (admitted). ν ∉ ℤ, q normal for ν + 2m and ν + 2n.
- [28.12.E8](https://dlmf.nist.gov/28.12.E8): [`DLMF.Mathieu.mathieuMe_neg_nu`](DLMF/Mathieu/Noninteger/Properties.lean#L738) (proved). ν ∉ ℤ; proved (reindexing m ↦ -m).
- [28.12.E9](https://dlmf.nist.gov/28.12.E9): [`DLMF.Mathieu.mathieuMe_neg_q`](DLMF/Mathieu/Noninteger/Properties.lean#L931) (proved). ν ∉ ℤ; proved from 28.14.8.
- [28.12.E10](https://dlmf.nist.gov/28.12.E10): [`DLMF.Mathieu.conj_mathieuMe`](DLMF/Mathieu/Noninteger/Properties.lean#L946) (proved). Stronger than DLMF: with the straight-segment continuation valid for every q (DLMF excepts cuts on the real q-axis for special complex ν).
- [28.12.E11](https://dlmf.nist.gov/28.12.E11): [`DLMF.Mathieu.mathieuMe_natCast`](DLMF/Mathieu/Noninteger/Properties.lean#L961) (proved); [`DLMF.Mathieu.mathieuMe_neg_natCast`](DLMF/Mathieu/Noninteger/Properties.lean#L970) (proved). Integer order, real q (definition completion via `mathieuMeInt`).
- [28.12.E12](https://dlmf.nist.gov/28.12.E12): [`DLMF.Mathieu.mathieuCeNu`](DLMF/Mathieu/Noninteger/Basic.lean#L151) (definition). Definition for every ν; used for ν ∉ ℤ.
- [28.12.E13](https://dlmf.nist.gov/28.12.E13): [`DLMF.Mathieu.mathieuSeNu`](DLMF/Mathieu/Noninteger/Basic.lean#L157) (definition). Definition for every ν; used for ν ∉ ℤ.
- [28.12.E14](https://dlmf.nist.gov/28.12.E14): [`DLMF.Mathieu.mathieuCeNu_neg`](DLMF/Mathieu/Noninteger/Properties.lean#L1071) (proved). ν ∉ ℤ.
- [28.12.E15](https://dlmf.nist.gov/28.12.E15): [`DLMF.Mathieu.mathieuSeNu_neg`](DLMF/Mathieu/Noninteger/Properties.lean#L1079) (proved). ν ∉ ℤ.

## [§28.13 Graphics](https://dlmf.nist.gov/28.13)

- §28.13 (Figures 28.13.1–28.13.5): excluded: graphics.

## [§28.14 Fourier Series](https://dlmf.nist.gov/28.14)

- [28.14.E1](https://dlmf.nist.gov/28.14.E1): [`DLMF.Mathieu.mathieuMeCoeff`](DLMF/Mathieu/Noninteger/Basic.lean#L140) (definition); [`DLMF.Mathieu.hasSum_mathieuMe`](DLMF/Mathieu/Noninteger/Fourier.lean#L36) (proved); [`DLMF.Mathieu.hasSum_mathieuMe_ofReal`](DLMF/Mathieu/Noninteger/Fourier.lean#L67) (proved). `mathieuMeCoeff ν q m` = c^ν_{2m}(q); absolute and locally uniform convergence on ℂ admitted; the real-axis case is proved (ℓ¹ coefficients by construction).
- [28.14.E2](https://dlmf.nist.gov/28.14.E2): [`DLMF.Mathieu.hasSum_mathieuCeNu`](DLMF/Mathieu/Noninteger/Fourier.lean#L104) (proved). From 28.14.1.
- [28.14.E3](https://dlmf.nist.gov/28.14.E3): [`DLMF.Mathieu.hasSum_mathieuSeNu`](DLMF/Mathieu/Noninteger/Fourier.lean#L117) (proved). From 28.14.1.
- [28.14.E4](https://dlmf.nist.gov/28.14.E4): [`DLMF.Mathieu.mathieuMeCoeff_recurrence`](DLMF/Mathieu/Noninteger/Fourier.lean#L130) (proved). From the definition (q normal along the segment).
- [28.14.E5](https://dlmf.nist.gov/28.14.E5): [`DLMF.Mathieu.hasSum_mathieuMeCoeff_sq`](DLMF/Mathieu/Noninteger/Fourier.lean#L141) (proved). From the definition.
- [28.14.E6](https://dlmf.nist.gov/28.14.E6): [`DLMF.Mathieu.mathieuMeCoeff_ratio`](DLMF/Mathieu/Noninteger/Fourier.lean#L315) (proved). Stated as c_{2m}/c_{2m∓2} + q/(4m²) = O(m⁻³), m → ±∞, q ≠ 0.
- [28.14.E7](https://dlmf.nist.gov/28.14.E7): [`DLMF.Mathieu.mathieuMeCoeff_neg`](DLMF/Mathieu/Noninteger/Fourier.lean#L349) (proved). ν ∉ ℤ.
- [28.14.E8](https://dlmf.nist.gov/28.14.E8): [`DLMF.Mathieu.mathieuMeCoeff_neg_q`](DLMF/Mathieu/Noninteger/Fourier.lean#L358) (proved). ν ∉ ℤ.
- [28.14.E9](https://dlmf.nist.gov/28.14.E9): [`DLMF.Mathieu.mathieuMeCoeff_zero`](DLMF/Mathieu/Noninteger/Fourier.lean#L365) (proved). ν ∉ ℤ.
- [28.14.E10](https://dlmf.nist.gov/28.14.E10): [`DLMF.Mathieu.mathieuMeCoeff_isBigO_zero`](DLMF/Mathieu/Noninteger/Fourier.lean#L373) (admitted). c_{2m} - (leading term) c_0 = O(q^{m+2}), q → 0 in ℂ, m ≥ 1 (equivalent to DLMF since c_0 → 1). Checked numerically.

## [§28.15 Expansions for Small 𝑞](https://dlmf.nist.gov/28.15)

- [28.15.E1](https://dlmf.nist.gov/28.15.E1): [`DLMF.Mathieu.mathieuLambda_isBigO_zero`](DLMF/Mathieu/Noninteger/Expansions.lean#L39) (admitted). Remainder O(q⁸) as q → 0 in ℂ, ν ∉ ℤ. Checked numerically (ν = 0.3, 1.7, 2.5, q = 0.05: error ~ 4·10⁻¹³).
- [28.15.E2](https://dlmf.nist.gov/28.15.E2): [`DLMF.Mathieu.mathieuLambda_contFrac`](DLMF/Mathieu/Noninteger/Expansions.lean#L51) (admitted). Continued fractions as limits of the approximants `mathieuContFrac`; DLMF's remark "higher coefficients can be found by equating powers" is not a separate statement.
- [28.15.E3](https://dlmf.nist.gov/28.15.E3): [`DLMF.Mathieu.mathieuMe_isBigO_zero`](DLMF/Mathieu/Noninteger/Expansions.lean#L65) (admitted). Remainder O(q³) for fixed z. Coefficients checked numerically.

## [§28.16 Asymptotic Expansions for Large 𝑞](https://dlmf.nist.gov/28.16)

- [28.16.E1](https://dlmf.nist.gov/28.16.E1): [`DLMF.Mathieu.mathieuLambda_isBigO_atTop`](DLMF/Mathieu/Noninteger/Expansions.lean#L82) (admitted). Remainder after the printed terms O(h⁻⁶), h → +∞, real ν ∈ (m, m+1). Checked numerically.

## [§28.17 Stability as 𝑥 → ±∞](https://dlmf.nist.gov/28.17)

- [28.17](https://dlmf.nist.gov/28.17): [`DLMF.Mathieu.IsMathieuStable`](DLMF/Mathieu/Noninteger/Basic.lean#L205) (definition); [`DLMF.Mathieu.isMathieuStable_q_zero`](DLMF/Mathieu/Noninteger/Expansions.lean#L100) (proved); [`DLMF.Mathieu.isMathieuStable_mathieuLambda`](DLMF/Mathieu/Noninteger/Expansions.lean#L204) (proved from admissions); [`DLMF.Mathieu.not_isMathieuStable_of_im_ne_zero`](DLMF/Mathieu/Noninteger/Expansions.lean#L330) (proved); [`DLMF.Mathieu.mathieuMe_tendsto_or`](DLMF/Mathieu/Noninteger/Expansions.lean#L260) (proved); [`DLMF.Mathieu.isOpen_mathieuStable_and_frontier`](DLMF/Mathieu/Noninteger/Expansions.lean#L538) (proved). `IsMathieuStable` (definition, ¶1); stable pairs for q = 0, a > 0 (proved) and for real ν ∉ ℤ (¶2); instability for ℑν ≠ 0 and unboundedness of all nontrivial solutions, behaviour of me_ν(±x) (¶3); openness of the real stability region and its boundary on the characteristic curves (¶4). Figure 28.17.1 excluded: graphics.

## [§28.18 Integrals and Integral Equations](https://dlmf.nist.gov/28.18)

- §28.18 consists of a pointer to §28.28 (part C); no statements.

## [§28.19 Expansions in Series of me_{ν+2n} Functions](https://dlmf.nist.gov/28.19)

- [28.19.E1](https://dlmf.nist.gov/28.19.E1): [`DLMF.Mathieu.hasSum_mathieuMe_expansion`](DLMF/Mathieu/Noninteger/Expansions.lean#L610) (admitted). Hypotheses: ν ∉ ℤ, q normal for every ν + 2n, f analytic on a strip a < ℑz < b.
- [28.19.E2](https://dlmf.nist.gov/28.19.E2): [`DLMF.Mathieu.hasSum_mathieuMe_expansion`](DLMF/Mathieu/Noninteger/Expansions.lean#L610) (admitted).
- [28.19.E3](https://dlmf.nist.gov/28.19.E3): [`DLMF.Mathieu.hasSum_mathieuMe_expansion`](DLMF/Mathieu/Noninteger/Expansions.lean#L610) (admitted).
- [28.19.E4](https://dlmf.nist.gov/28.19.E4): [`DLMF.Mathieu.hasSum_exp_mathieuMe`](DLMF/Mathieu/Noninteger/Expansions.lean#L630) (admitted).

## [§28.29 Definitions and Basic Properties (Hill's Equation)](https://dlmf.nist.gov/28.29)

- [28.29.i](https://dlmf.nist.gov/28.29.i): [`DLMF.Mathieu.IsHillPotential`](DLMF/Mathieu/Hill/Basic.lean#L95) (definition); [`DLMF.Mathieu.isHillPotential_mathieu`](DLMF/Mathieu/Hill/Floquet.lean#L50) (proved). Mathieu's equation as Hill's equation (proved: Q = -2q cos 2x satisfies 28.29.2–28.29.3); hypotheses on Q.
- [28.29.ii](https://dlmf.nist.gov/28.29.ii): [`DLMF.Mathieu.hill_exists_solution`](DLMF/Mathieu/Hill/Floquet.lean#L71) (proved); [`DLMF.Mathieu.hillWI_spec`](DLMF/Mathieu/Hill/Floquet.lean#L101) (proved); [`DLMF.Mathieu.hillWII_spec`](DLMF/Mathieu/Hill/Floquet.lean#L112) (proved); [`DLMF.Mathieu.differentiable_hillDiscriminant`](DLMF/Mathieu/Hill/Floquet.lean#L485) (proved); [`DLMF.Mathieu.exists_hillFloquet_fundamental_pair`](DLMF/Mathieu/Hill/Floquet.lean#L520) (proved); [`DLMF.Mathieu.hill_all_periodic_of_minimal_period`](DLMF/Mathieu/Hill/Floquet.lean#L658) (proved); [`DLMF.Mathieu.IsHillSolution.floquet_or`](DLMF/Mathieu/Hill/Floquet.lean#L770) (proved); [`DLMF.Mathieu.hillWI_neg_of_even`](DLMF/Mathieu/Hill/Floquet.lean#L804) (proved); [`DLMF.Mathieu.hillWII_neg_of_even`](DLMF/Mathieu/Hill/Floquet.lean#L822) (proved). Existence (flagged, admitted) and uniqueness (proved) of solutions, basic solutions w_I, w_II (definitions by choice), entire discriminant, fundamental pair, period nπ, Floquet-or-shift, symmetric case (w_I even, w_II odd: proved from existence).
- [28.29.iii](https://dlmf.nist.gov/28.29.iii): [`DLMF.Mathieu.differentiable_hillDiscriminant`](DLMF/Mathieu/Hill/Floquet.lean#L485) (proved); [`DLMF.Mathieu.hillDiscriminant_order_half`](DLMF/Mathieu/Hill/Floquet.lean#L961) (proved); [`DLMF.Mathieu.infinite_hillDiscriminant_eq`](DLMF/Mathieu/Hill/Floquet.lean#L1051) (admitted); [`DLMF.Mathieu.hillPeriodicEigenvalue_spec`](DLMF/Mathieu/Hill/Floquet.lean#L1060) (admitted); [`DLMF.Mathieu.hillAntiperiodicEigenvalue_spec`](DLMF/Mathieu/Hill/Floquet.lean#L1073) (admitted). Real Q: Δ entire of order exactly ½; infinitely many roots of Δ = 2cos πν; the eigenvalue sequences.
- [28.29.E1](https://dlmf.nist.gov/28.29.E1): [`DLMF.Mathieu.IsHillSolution`](DLMF/Mathieu/Hill/Basic.lean#L86) (definition). Real variable, Q : ℝ → ℂ continuous (covers DLMF's two cases on the real axis).
- [28.29.E2](https://dlmf.nist.gov/28.29.E2): [`DLMF.Mathieu.IsHillPotential`](DLMF/Mathieu/Hill/Basic.lean#L95) (definition). Field of `IsHillPotential`.
- [28.29.E3](https://dlmf.nist.gov/28.29.E3): [`DLMF.Mathieu.IsHillPotential`](DLMF/Mathieu/Hill/Basic.lean#L95) (definition). Field of `IsHillPotential`; DLMF's "π is the minimum period" is not required.
- [28.29.E4](https://dlmf.nist.gov/28.29.E4): [`DLMF.Mathieu.hillWI_add_pi`](DLMF/Mathieu/Hill/Floquet.lean#L151) (proved). Proved from the flagged existence theorem.
- [28.29.E5](https://dlmf.nist.gov/28.29.E5): [`DLMF.Mathieu.hillWII_add_pi`](DLMF/Mathieu/Hill/Floquet.lean#L165) (proved). Proved from the flagged existence theorem.
- [28.29.E6](https://dlmf.nist.gov/28.29.E6): [`DLMF.Mathieu.exists_hillCharExp`](DLMF/Mathieu/Hill/Floquet.lean#L424) (proved). Proved: a characteristic exponent with -1 < ℜν ≤ 1 exists for every λ.
- [28.29.E7](https://dlmf.nist.gov/28.29.E7): [`DLMF.Mathieu.IsHillFloquetSolution`](DLMF/Mathieu/Hill/Basic.lean#L135) (definition); [`DLMF.Mathieu.exists_hillFloquet_iff_det`](DLMF/Mathieu/Hill/Floquet.lean#L445) (proved). `IsHillFloquetSolution` (definition); Floquet's theorem admitted. Stated for every ν (DLMF normalizes 28.29.6).
- [28.29.E8](https://dlmf.nist.gov/28.29.E8): [`DLMF.Mathieu.hillMonodromy`](DLMF/Mathieu/Hill/Basic.lean#L128) (definition); [`DLMF.Mathieu.exists_hillFloquet_iff_det`](DLMF/Mathieu/Hill/Floquet.lean#L445) (proved). `hillMonodromy` (definition).
- [28.29.E9](https://dlmf.nist.gov/28.29.E9): [`DLMF.Mathieu.exists_hillFloquet_iff_discriminant`](DLMF/Mathieu/Hill/Floquet.lean#L462) (proved). Stated for every ν.
- [28.29.E10](https://dlmf.nist.gov/28.29.E10): [`DLMF.Mathieu.IsHillFloquetSolution.exists_periodic`](DLMF/Mathieu/Hill/Floquet.lean#L508) (proved). Proved.
- [28.29.E11](https://dlmf.nist.gov/28.29.E11): [`DLMF.Mathieu.exists_hill_periodic_of_discriminant`](DLMF/Mathieu/Hill/Floquet.lean#L581) (proved). Stated for all solutions (c = 0 for multiples of P), with s = (-1)^ν = ±1.
- [28.29.E12](https://dlmf.nist.gov/28.29.E12): [`DLMF.Mathieu.hill_coexistence_iff`](DLMF/Mathieu/Hill/Floquet.lean#L630) (proved). Coexistence ↔ monodromy = ±I.
- [28.29.E13](https://dlmf.nist.gov/28.29.E13): [`DLMF.Mathieu.IsHillSolution.add_pi_add_sub_pi`](DLMF/Mathieu/Hill/Floquet.lean#L759) (proved).
- [28.29.E14](https://dlmf.nist.gov/28.29.E14): [`DLMF.Mathieu.hillDiscriminant_of_even`](DLMF/Mathieu/Hill/Floquet.lean#L844) (proved). Q even: Δ(λ) = 2 w_I(π, λ).
- [28.29.E15](https://dlmf.nist.gov/28.29.E15): [`DLMF.Mathieu.hillDiscriminant`](DLMF/Mathieu/Hill/Basic.lean#L121) (definition). `hillDiscriminant` (definition, for all Q).
- [28.29.E16](https://dlmf.nist.gov/28.29.E16): [`DLMF.Mathieu.hillPeriodicEigenvalue`](DLMF/Mathieu/Hill/Basic.lean#L190) (definition); [`DLMF.Mathieu.hillPeriodicEigenvalue_spec`](DLMF/Mathieu/Hill/Floquet.lean#L1060) (admitted). `hillPeriodicEigenvalue` (definition by counting with multiplicity = dim of the periodic solution space); characterization admitted.
- [28.29.E17](https://dlmf.nist.gov/28.29.E17): [`DLMF.Mathieu.hillAntiperiodicEigenvalue`](DLMF/Mathieu/Hill/Basic.lean#L198) (definition); [`DLMF.Mathieu.hillAntiperiodicEigenvalue_spec`](DLMF/Mathieu/Hill/Floquet.lean#L1073) (admitted). `hillAntiperiodicEigenvalue` (μ_n, n ≥ 1); DLMF's "solution of period 2π" means antiperiodic (w(z+π) = -w(z)).
- [28.29.E18](https://dlmf.nist.gov/28.29.E18): [`DLMF.Mathieu.hill_eigenvalue_interlacing`](DLMF/Mathieu/Hill/Floquet.lean#L1088) (admitted).
- [28.29.E19](https://dlmf.nist.gov/28.29.E19): [`DLMF.Mathieu.hillMeanSquare`](DLMF/Mathieu/Hill/Basic.lean#L225) (definition); [`DLMF.Mathieu.hillAntiperiodicEigenvalue_asymptotic`](DLMF/Mathieu/Hill/Floquet.lean#L1099) (admitted). `hillMeanSquare` N.
- [28.29.E20](https://dlmf.nist.gov/28.29.E20): [`DLMF.Mathieu.hillAntiperiodicEigenvalue_asymptotic`](DLMF/Mathieu/Hill/Floquet.lean#L1099) (admitted). Q ∈ C².
- [28.29.E21](https://dlmf.nist.gov/28.29.E21): [`DLMF.Mathieu.hillPeriodicEigenvalue_asymptotic`](DLMF/Mathieu/Hill/Floquet.lean#L1111) (admitted). Q ∈ C².
- [28.29.E22](https://dlmf.nist.gov/28.29.E22): [`DLMF.Mathieu.hill_gap_asymptotic`](DLMF/Mathieu/Hill/Floquet.lean#L1123) (admitted). Q ∈ C^k (Hochstadt).

## [§28.30 Expansions in Series of Eigenfunctions](https://dlmf.nist.gov/28.30)

- [28.30.i](https://dlmf.nist.gov/28.30.i): [`DLMF.Mathieu.hillEigenvalueHat`](DLMF/Mathieu/Hill/Basic.lean#L206) (definition); [`DLMF.Mathieu.IsHillEigenfunctionFamily`](DLMF/Mathieu/Hill/Basic.lean#L215) (definition); [`DLMF.Mathieu.exists_hill_eigenfunctions`](DLMF/Mathieu/Hill/Eigenfunctions.lean#L38) (admitted). `hillEigenvalueHat` (λ̂_m, merged natural order), `IsHillEigenfunctionFamily` (definition: orthonormal real 2π-periodic eigenfunctions; a choice in DLMF).
- [28.30.E1](https://dlmf.nist.gov/28.30.E1): [`DLMF.Mathieu.exists_hill_eigenfunctions`](DLMF/Mathieu/Hill/Eigenfunctions.lean#L38) (admitted). Existence of an eigenfunction family admitted.
- [28.30.E2](https://dlmf.nist.gov/28.30.E2): [`DLMF.Mathieu.exists_hill_eigenfunctions`](DLMF/Mathieu/Hill/Eigenfunctions.lean#L38) (admitted).
- [28.30.E3](https://dlmf.nist.gov/28.30.E3): [`DLMF.Mathieu.hasSum_hill_eigenfunction_expansion`](DLMF/Mathieu/Hill/Eigenfunctions.lean#L46) (admitted). For every eigenfunction family; "f square integrable" as f' absolutely continuous with derivative in L²(0, 2π).
- [28.30.E4](https://dlmf.nist.gov/28.30.E4): [`DLMF.Mathieu.hasSum_hill_eigenfunction_expansion`](DLMF/Mathieu/Hill/Eigenfunctions.lean#L46) (admitted).

## [§28.31 Equations of Whittaker–Hill and Ince](https://dlmf.nist.gov/28.31)

- [28.31.ii](https://dlmf.nist.gov/28.31.ii): [`DLMF.Mathieu.inceC_spec`](DLMF/Mathieu/Hill/Ince.lean#L722) (admitted); [`DLMF.Mathieu.inceS_spec`](DLMF/Mathieu/Hill/Ince.lean#L740) (admitted). Ince polynomials exist for nonnegative integer p, eigenvalues real, distinct, ordered by zeros (`inceC_spec`, `inceS_spec`).
- [28.31.iii](https://dlmf.nist.gov/28.31.iii): [`DLMF.Mathieu.paraboloidal_asymptotic_pos`](DLMF/Mathieu/Hill/Ince.lean#L984) (admitted); [`DLMF.Mathieu.paraboloidal_asymptotic_neg`](DLMF/Mathieu/Hill/Ince.lean#L1016) (admitted). Asymptotic behaviour for ξ > 0 (z = iy → ±i∞) and, **corrected**, for -ξ (z = ½π + iy): factors exp(¼ξ cos 2z)(sin z)^p and exp(-¼ξ cos 2z)(sin z)^{-p-2} instead of DLMF's (cos z)^{-p-2} and (cos z)^p; "other periodic solutions" taken as even or odd periodic solutions not proportional to hc, hs.
- [28.31.E1](https://dlmf.nist.gov/28.31.E1): [`DLMF.Mathieu.IsWhittakerHillSolution`](DLMF/Mathieu/Hill/Basic.lean#L232) (definition). `IsWhittakerHillSolution` (definition, entire W, complex parameters).
- [28.31.E2](https://dlmf.nist.gov/28.31.E2): [`DLMF.Mathieu.isWhittakerHillSolution_iff_isInceSolution`](DLMF/Mathieu/Hill/Ince.lean#L74) (proved). Proved, for all complex parameters with ξ² = -4k²c² (DLMF: k² < 0).
- [28.31.E3](https://dlmf.nist.gov/28.31.E3): [`DLMF.Mathieu.IsInceSolution`](DLMF/Mathieu/Hill/Basic.lean#L240) (definition). `IsInceSolution` (definition).
- [28.31.E4](https://dlmf.nist.gov/28.31.E4): [`DLMF.Mathieu.isInceSolution_cos_even_iff`](DLMF/Mathieu/Hill/Ince.lean#L362) (proved); [`DLMF.Mathieu.isInceSolution_cos_odd_iff`](DLMF/Mathieu/Hill/Ince.lean#L468) (proved). Fourier-series solutions with `IsEntireFourierCoeff` coefficients: solution ↔ recurrences (DLMF: "formal" solutions).
- [28.31.E5](https://dlmf.nist.gov/28.31.E5): [`DLMF.Mathieu.isInceSolution_sin_odd_iff`](DLMF/Mathieu/Hill/Ince.lean#L543) (proved); [`DLMF.Mathieu.isInceSolution_sin_even_iff`](DLMF/Mathieu/Hill/Ince.lean#L623) (proved).
- [28.31.E6](https://dlmf.nist.gov/28.31.E6): [`DLMF.Mathieu.isInceSolution_cos_even_iff`](DLMF/Mathieu/Hill/Ince.lean#L362) (proved).
- [28.31.E7](https://dlmf.nist.gov/28.31.E7): [`DLMF.Mathieu.isInceSolution_cos_odd_iff`](DLMF/Mathieu/Hill/Ince.lean#L468) (proved).
- [28.31.E8](https://dlmf.nist.gov/28.31.E8): [`DLMF.Mathieu.isInceSolution_sin_odd_iff`](DLMF/Mathieu/Hill/Ince.lean#L543) (proved).
- [28.31.E9](https://dlmf.nist.gov/28.31.E9): [`DLMF.Mathieu.isInceSolution_sin_even_iff`](DLMF/Mathieu/Hill/Ince.lean#L623) (proved).
- [28.31.E10](https://dlmf.nist.gov/28.31.E10): [`DLMF.Mathieu.inceC`](DLMF/Mathieu/Hill/Basic.lean#L283) (definition); [`DLMF.Mathieu.inceC_spec`](DLMF/Mathieu/Hill/Ince.lean#L722) (admitted). `inceC` (C_p^m): definition by choice (unique normalized cosine Ince polynomial for η = a_p^m(ξ), `inceA` chosen by zero count, real ξ).
- [28.31.E11](https://dlmf.nist.gov/28.31.E11): [`DLMF.Mathieu.inceS`](DLMF/Mathieu/Hill/Basic.lean#L293) (definition); [`DLMF.Mathieu.inceS_spec`](DLMF/Mathieu/Hill/Ince.lean#L740) (admitted). `inceS` (S_p^m), `inceB`: as for C.
- [28.31.E12](https://dlmf.nist.gov/28.31.E12): [`DLMF.Mathieu.inceC_spec`](DLMF/Mathieu/Hill/Ince.lean#L722) (admitted); [`DLMF.Mathieu.inceS_spec`](DLMF/Mathieu/Hill/Ince.lean#L740) (admitted).
- [28.31.E13](https://dlmf.nist.gov/28.31.E13): [`DLMF.Mathieu.ince_tendsto_xi_zero`](DLMF/Mathieu/Hill/Ince.lean#L759) (admitted).
- [28.31.E14](https://dlmf.nist.gov/28.31.E14): [`DLMF.Mathieu.ince_tendsto_mathieu`](DLMF/Mathieu/Hill/Ince.lean#L771) (admitted). Along sequences p_j → ∞, ξ_j → 0, p_j ξ_j → 2q (real q), using ce_m, se_m of DLMF.Mathieu.Basic.
- [28.31.E15](https://dlmf.nist.gov/28.31.E15): [`DLMF.Mathieu.ince_tendsto_mathieu`](DLMF/Mathieu/Hill/Ince.lean#L771) (admitted).
- [28.31.E16](https://dlmf.nist.gov/28.31.E16): [`DLMF.Mathieu.paraboloidalHc`](DLMF/Mathieu/Hill/Basic.lean#L302) (definition). `paraboloidalHc` (definition).
- [28.31.E17](https://dlmf.nist.gov/28.31.E17): [`DLMF.Mathieu.paraboloidalHs`](DLMF/Mathieu/Hill/Basic.lean#L308) (definition). `paraboloidalHs` (definition).
- [28.31.E18](https://dlmf.nist.gov/28.31.E18): [`DLMF.Mathieu.paraboloidal_isWhittakerHillSolution`](DLMF/Mathieu/Hill/Ince.lean#L786) (proved from admissions). As the Whittaker–Hill equation with k = iξ/2, c = 1; proved from 28.31.2 and the admitted Ince-polynomial specifications.
- [28.31.E19](https://dlmf.nist.gov/28.31.E19): [`DLMF.Mathieu.paraboloidalHc_neg_xi`](DLMF/Mathieu/Hill/Ince.lean#L813) (admitted). Checked numerically (p ≤ 6, ξ = 0.8).
- [28.31.E20](https://dlmf.nist.gov/28.31.E20): [`DLMF.Mathieu.paraboloidalHs_neg_xi`](DLMF/Mathieu/Hill/Ince.lean#L824) (admitted). Checked numerically.
- [28.31.E21](https://dlmf.nist.gov/28.31.E21): [`DLMF.Mathieu.integral_paraboloidal_orthogonal`](DLMF/Mathieu/Hill/Ince.lean#L901) (proved from admissions).
- [28.31.E22](https://dlmf.nist.gov/28.31.E22): [`DLMF.Mathieu.paraboloidalHc_double_orthogonal`](DLMF/Mathieu/Hill/Ince.lean#L943) (admitted). u-integral along u₀ + it, t ≥ 0 (u₀ = 0 for ξ > 0, ½π for ξ < 0, as DLMF); the factor i of du dropped.
- [28.31.E23](https://dlmf.nist.gov/28.31.E23): [`DLMF.Mathieu.paraboloidalHs_double_orthogonal`](DLMF/Mathieu/Hill/Ince.lean#L959) (admitted).
- [28.31.E24](https://dlmf.nist.gov/28.31.E24): [`DLMF.Mathieu.paraboloidalHc_Hs_double_orthogonal`](DLMF/Mathieu/Hill/Ince.lean#L972) (admitted).

## Prose, informal and excluded items (part B)

- Not acquired (informal or pointers): the remark of §28.31(i) on Arscott's treatment, §28.30(ii)
  (pointer to Schäfke and Meixner et al.), the last paragraph of §28.29(iii) (pointer), the
  remark on infinite determinants in §28.29, the remarks in §28.12 that `ce_ν`, `se_ν` at
  integer `ν` are not limiting values, and the sentence of §28.15 that higher coefficients are
  found by equating powers of `q`.
- Excluded: graphics (§28.13, Figure 28.17.1). The mathematical content of the applications
  sections is listed in part A.

## Validation (part B)

- The eight modules build with `lake build DLMF.Mathieu.Noninteger.Expansions
  DLMF.Mathieu.Hill.Ince DLMF.Mathieu.Hill.Eigenfunctions` with 0 errors and only `sorry`
  warnings; each passes `lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false`; a
  scratch file importing all part A theorem modules together with the part B modules
  elaborates without name clashes. Lines are at most 100 characters. No axioms, no
  `native_decide`, no `sorry` in definitions or helpers (prefix `m28b_`); the one flagged
  admitted foundation is `hill_exists_solution` (global existence for Hill's equation).
- `#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound` for 60 sorry-free
  theorems, e.g. `mathieuLambda_zero`, `mathieuLambda_neg_q_and_neg_nu`, `mathieuMe_neg_q`,
  `conj_mathieuMe`, `isHillPotential_mathieu`, `exists_hillCharExp`,
  `isWhittakerHillSolution_iff_isInceSolution`, `isMathieuStable_q_zero`. The nine
  "proved from admissions" theorems depend on `hasSum_mathieuMe`, `hill_exists_solution` or
  `inceC_spec`/`inceS_spec`.
- DLMF.lean, the area umbrella, `DLMF/Mathieu/Basic.lean`, the lakefile and the other ledgers
  are unchanged (the coordinator adds the umbrella imports).

# Part C: modified Mathieu functions, §§28.20–28.28 (agent ACQ28C)

This part covers [§§28.20–28.28](https://dlmf.nist.gov/28.20) (DLMF version 1.2.8, checked on
2026-10-26). §28.21 (graphics) is excluded. The Lean code is in `DLMF/Mathieu/Modified/`
(namespace `DLMF.Mathieu`, helper prefix `m28c_`). The modules, in import order, are
[Basic](DLMF/Mathieu/Modified/Basic.lean) (the foundational umbrella for
`Basic.Functions`, `Basic.AsymptoticData` and `Basic.IntegralKernels`),
[BesselSeries](DLMF/Mathieu/Modified/BesselSeries.lean) (§§28.23–28.24; also imports
`DLMF.Bessel.Modified` and `DLMF.Bessel.SecondKind`),
[Properties](DLMF/Mathieu/Modified/Properties.lean) (§28.20; also imports
`DLMF.Mathieu.Noninteger.Properties`),
[Connection](DLMF/Mathieu/Modified/Connection.lean) (§28.22),
[Asymptotics](DLMF/Mathieu/Modified/Asymptotics.lean) (§§28.25–28.26; also imports
`DLMFMathlib.Analysis.Asymptotics.AsymptoticExpansion`) and
[Integrals](DLMF/Mathieu/Modified/Integrals.lean) (§28.28; imports `Connection`).

**Counts.** §§28.20–28.28 have 124 numbered equations: 25 in §28.20, 14 in §28.22, 13 in §28.23,
13 in §28.24, 5 in §28.25, 5 in §28.26 and 49 in §28.28. §28.21 has figures only and §28.27
has no formulas. All 124 equations are in scope and covered. Three prose IDs carry tags as
well: 28.20.iii (the definition and characterization of `M^{(j)}_ν`), 28.26.i (Goldstein's
expansions of `Fs_m`, `Gs_m`) and 28.28.i (absolute convergence). 127 DLMF IDs are tagged on
164 declarations: 45 definitions, 12 proved theorems, 9 theorems proved from admissions and
98 direct admissions. Excluded: §28.21 (graphics). Pointers only, not acquired: 28.26.ii,
§28.27 and §28.28(v).

Module admissions (`grep -cE 'by sorry|:= sorry|^\s*(·\s*)?sorry\s*$|exact sorry'`) and
tagged declarations:

- [Basic](DLMF/Mathieu/Modified/Basic.lean): 0 admissions. 45 tagged: 45 definitions.
- [BesselSeries](DLMF/Mathieu/Modified/BesselSeries.lean): 12 admissions. 28 tagged: 1 proved, 27 admitted.
- [Properties](DLMF/Mathieu/Modified/Properties.lean): 6 admissions. 28 tagged: 4 proved, 7 proved from admissions, 17 admitted.
- [Connection](DLMF/Mathieu/Modified/Connection.lean): 0 admissions. 8 tagged: 8 admitted.
- [Asymptotics](DLMF/Mathieu/Modified/Asymptotics.lean): 5 admissions. 10 tagged: 3 proved, 2 proved from admissions, 5 admitted.
- [Integrals](DLMF/Mathieu/Modified/Integrals.lean): 37 admissions. 45 tagged: 4 proved, 41 admitted.

## Part C: design notes

- **Modified Mathieu functions** (28.20.3–28.20.7). `modMathieuCe`, `modMathieuSe` and
  `modMathieuMe` take complex `ν`, `z`, `q`. They use ACQ28B's `mathieuCeNu`, `mathieuSeNu`
  and `mathieuMe` for noninteger `ν`, and ACQ28A's `mathieuCe`, `mathieuSe` (real `q`) when
  `ν` is a natural number and `q` is real. `modMathieuFe` and `modMathieuGe` (integer `n`, real
  `q`) come from ACQ28A's `mathieuFe`, `mathieuGe`. The upper signs of DLMF are used. The
  integer cases are proved to agree with ACQ28A's functions (`modMathieuCe_natCast`,
  `modMathieuSe_natCast`).
- **`M^{(j)}_ν`** (§28.20(iii)). DLMF characterizes these functions by their asymptotics.
  They are *defined* here by the cross-product series 28.24.1,
  `M^{(j)}_ν(z, h) = (c^ν_{2n})⁻¹ ∑_ℓ (-1)^ℓ c^ν_{2ℓ} J_{ℓ-n}(h e^{-z}) 𝒞^{(j)}_{ν+n+ℓ}(h e^z)`,
  normalized at an index `n = modMathieuIndex ν h` with `c^ν_{2n} ≠ 0`, chosen by
  `Classical.choose` (`modMathieuM`). The value does not depend on `n`; this was checked
  numerically and is part of the admitted 28.24.1. The Bessel functions are continued
  analytically in `z` (`besselJExp`, `besselYExp`: `(h/2)^μ e^{μz} ₀F̃₁(μ+1; -(he^z)²/4)` and
  its limit at integer order), so `M^{(j)}_ν` is entire in `z`, and powers of `h` are
  principal. The characterization of §28.20(iii) (the equation, the asymptotics 28.20.9–12,
  uniqueness and reality) is stated as theorems. 28.20.13–14 are proved from the definition
  (given summability). Integer `ν` requires the index choice: `c^{-2}_0 = 0`, for example.
- **Radial functions** `Mc^{(j)}_n`, `Ms^{(j)}_n` (28.20.15–16) and `Ie`, `Io`, `Ke`, `Ko`
  (28.20.17–20) are defined from `modMathieuM` as DLMF does. Statements about them with ACQ28A's
  integer-order functions need real `h`, because those functions take real `q`.
- **Bessel series** (28.23). `mathieuCyl j μ w` is the principal `𝒞^{(j)}_μ(w)`, and
  `mathieuCylExp` is its continuation in `z` for `w = h e^z`. In 28.23.2–5 the argument
  `2h cosh z` (or `2h sinh z`) is `h e^{z'}` with `z' = z + log(1 ± e^{-2z})` (`mathieuCylCosh`,
  `mathieuCylSinh`). This is the continuation that DLMF's convergence statements need.
- **Asymptotics** (28.25). The coefficients `D^±_m` (`modMathieuAsympD`) are defined by the
  recurrence 28.25.3, which is proved in field form. 28.25.1 is stated as
  `HasAsymptoticExpansion` (from `DLMFMathlib`) along `Re z → +∞` in the sectors 28.25.4–5.
- **Goldstein** (28.26). `Fc_m`, `Gc_m`, `Fs_m`, `Gs_m` are *defined* by solving 28.26.1–2 for
  them, so that 28.26.1–2 hold by construction (`radialMathieuMc_three_eq_goldstein` and
  `radialMathieuMs_three_eq_goldstein`, proved from 28.20.13). The content of 28.26.4–5 and of
  28.26(i) is then the `O(h^{-4})` approximation (admitted), stated for `Re z > 0`,
  `|Im z| < π/2`, uniformly as `h → ∞` (principal `arctan` and powers).
- **Integrals** (28.28). The paths `𝓛_1`, `𝓛_3`, `𝓛_4` of 28.28.6 are realized as specific
  polygonal paths with vertical rays (`mathieuPathIntegral`). DLMF says only that `η₁`, `η₂`
  are real constants. In fact the rays must lie in the valleys of `e^{2ihw}`, so the theorems
  carry `MathieuPathValley z α η₁ η₂`, an explicit condition in terms of
  `arg(cosh(z ± iα) ± i)`. 28.28.10 becomes the hypotheses
  `0 < Im(h(cosh z ± 1))`. The functions `R(z, t)` and `φ(z, t)` of 28.28.18–19 are defined
  by explicit logarithms that are analytic for `Re z > 0`. Their defining identities are
  proved (`mathieuKernelR_sq`, `mathieuKernelR_zero`, `exp_two_I_mathieuKernelPhi`,
  `mathieuKernelPhi_zero`). 28.28.21 uses the `4/π ∫₀^{π/2}` form. Nonvanishing hypotheses
  are added where DLMF divides by a cross-product value at `0` (28.28.27, 28, 33, 38, 43, 46,
  49), and those equations state the second equality, the first being the definition of the
  constant. The principal value 28.28.34 is a limit over `{t ∈ (0, 2π] : ε < |sin t|}`.
- **Branch restrictions.** 28.24.10–13 (with `K`) are restricted to `|Im z| < π`, and
  28.26.4–5 to `|Im z| < π/2`, where the principal functions used here are the continuations
  that DLMF means.

## Part C: corrections to DLMF

1. **28.23.2–28.23.5**: DLMF says the expansions are valid for all `z` when `j = 1`. For
   noninteger `ν` this is false. The ratio of consecutive terms tends to `1/cosh² z` (resp.
   `1/sinh² z`), so the series diverge when `|cosh z| < 1` (resp. `|sinh z| < 1`). Example:
   `ν = 0.3`, `h = 1.2`, `z = 0.2 + 1.2i`, where partial sums of 28.23.2 grow to `~10⁵` at
   `L = 10` and `~10¹²` at `L = 20`. 28.23.4 diverges at `z = 0.3` and at `z = 0.7 + 0.2i`. The
   theorems assume `|cosh z| > 1` (resp. `|sinh z| > 1`) for every `j`. Only for integer `ν`,
   where the series terminate on one side or reduce to 28.23.6–13, does the `j = 1` case
   hold for all `z`.
2. **28.28.11**: the factor `e^{iνπ}` must be `e^{iνπ/2}`. Take `h = 1.2`, `z = 1 + i` and
   divide the integral by `½πi ce_ν(0, h²) M^{(3)}_ν(z, h)`. The ratio is `e^{0.15πi}` for
   `ν = 0.3`, `e^{πi/4}` for `ν = 0.5` and `i` for `ν = 1`, each to `10⁻¹²`. These values
   rule out `e^{iνπ}`. The neighbouring formulas 28.28.12–14 have the factors `e^{iνπ/2}`,
   `i^m`, `i^{m+1}`, which is consistent with the correction.
3. **28.28.16**: the overall sign is wrong. The correct right side is
   `+π A^{2n}_0 / (2 ce_{2n}(π/2)) · (ce_{2n}(y) ∓ 2 fe_{2n}(y)/(π C_{2n}))`. Direct
   integration with `h = 1.2`, `n = 0, 1` and `y = 0.6, 2.0` gives `0.11236`, `-0.05205`,
   `1.10503`, `-1.41558`. The corrected right side gives `0.11239`, `-0.05204`, `1.10489`,
   `-1.41562`, and the differences are the truncation error of the integration. The corrected
   form also follows from the corrected 28.28.11 at `z = iy`. 28.28.15 follows the same way
   and is correct as printed. The coordinator's independent verifier also found that the lower
   sign belongs to `−π ≤ y ≤ 0`, not to `π ≤ y ≤ 2π` as printed (the left side is even in `y`,
   `fe_{2n}` is odd; at `y = −0.3` the lower sign gives `0.4211` against `0.4207`, at
   `y = π + 0.3` the printed range gives `±2.05` against `−0.4207`); the statement uses the
   corrected range.

## Part C: prose, informal and excluded items

- §28.21 (graphics): excluded, graphics.
- 28.20.E8 (`h = √q > 0`) is notation, recorded on `modMathieuM_three_isBigO`.
- The remark after 28.22.13, that `M^{(1)}_ν(0, h)` is best computed from 28.24.1 with an index
  of maximal `|c^ν_{2n}|`, is computational advice. It is not acquired.
- 28.26(ii) (uniform approximations) points to §28.8(iv) and to Naylor. It is not acquired.
- §28.27 (addition theorems) points to Meixner, Schäfke and Wolf (1980, §2.4) and has no
  formulas. It is not acquired.
- §28.28(v) (compendia) points to the literature. It is not acquired.

## Part C: numbered formulas and prose items

## [§28.20 Definitions and Basic Properties](https://dlmf.nist.gov/28.20)

- [28.20.iii](https://dlmf.nist.gov/28.20.iii): [`DLMF.Mathieu.modMathieuM`](DLMF/Mathieu/Modified/Basic/Functions.lean#L143) (definition); [`DLMF.Mathieu.isModMathieuSolution_modMathieuM`](DLMF/Mathieu/Modified/Properties.lean#L162) (proved); [`DLMF.Mathieu.eq_modMathieuM_three_of_isBigO`](DLMF/Mathieu/Modified/Properties.lean#L206) (admitted); [`DLMF.Mathieu.eq_modMathieuM_four_of_isBigO`](DLMF/Mathieu/Modified/Properties.lean#L217) (admitted); [`DLMF.Mathieu.modMathieuM_one_two_real`](DLMF/Mathieu/Modified/Properties.lean#L372) (proved). The modified Mathieu functions; `M^{(j)}_ν(·, h)` solves the modified Mathieu equation 28.20.1 with `q = h²`, `a = λ_ν(h²)` ), `j = 1, 2, 3, 4`, `h ≠ 0`, admissible `(ν, h)`.
- [28.20.E1](https://dlmf.nist.gov/28.20.E1): [`DLMF.Mathieu.IsModMathieuSolution`](DLMF/Mathieu/Modified/Basic/Functions.lean#L24) (definition); [`DLMF.Mathieu.IsMathieuSolution.isModMathieuSolution_comp`](DLMF/Mathieu/Modified/Properties.lean#L33) (proved). The modified Mathieu equation; If `w` solves Mathieu's equation 28.2.1 then `z ↦ w(cz)` with `c² = -1` (`c = ±i`) solves the modified Mathieu equation 28.20.1.
- [28.20.E2](https://dlmf.nist.gov/28.20.E2): [`DLMF.Mathieu.isModMathieuSolution_comp_cosh`](DLMF/Mathieu/Modified/Properties.lean#L61) (proved). The algebraic form.
- [28.20.E3](https://dlmf.nist.gov/28.20.E3): [`DLMF.Mathieu.modMathieuCe`](DLMF/Mathieu/Modified/Basic/Functions.lean#L35) (definition); [`DLMF.Mathieu.modMathieuCe_natCast`](DLMF/Mathieu/Modified/Properties.lean#L91) (proved); [`DLMF.Mathieu.isModMathieuSolution_modMathieuCe`](DLMF/Mathieu/Modified/Properties.lean#L109) (proved). The modified Mathieu function; `Ce_n(z, q) = ce_n(iz, q)` for `n ∈ ℕ` and real `q` .
- [28.20.E4](https://dlmf.nist.gov/28.20.E4): [`DLMF.Mathieu.modMathieuSe`](DLMF/Mathieu/Modified/Basic/Functions.lean#L44) (definition); [`DLMF.Mathieu.modMathieuSe_natCast`](DLMF/Mathieu/Modified/Properties.lean#L100) (proved); [`DLMF.Mathieu.isModMathieuSolution_modMathieuSe`](DLMF/Mathieu/Modified/Properties.lean#L116) (proved). The modified Mathieu function; `Se_n(z, q) = -i se_n(iz, q)` for `n ≥ 1` and real `q` .
- [28.20.E5](https://dlmf.nist.gov/28.20.E5): [`DLMF.Mathieu.modMathieuMe`](DLMF/Mathieu/Modified/Basic/Functions.lean#L53) (definition); [`DLMF.Mathieu.isModMathieuSolution_modMathieuMe`](DLMF/Mathieu/Modified/Properties.lean#L131) (proved). The modified Mathieu function; `Me_ν(·, q)` solves the modified Mathieu equation with `a = λ_ν(q)` , `ν ∉ ℤ`, `q` normal along `[0, q]`.
- [28.20.E6](https://dlmf.nist.gov/28.20.E6): [`DLMF.Mathieu.modMathieuFe`](DLMF/Mathieu/Modified/Basic/Functions.lean#L58) (definition); [`DLMF.Mathieu.isModMathieuSolution_modMathieuFe`](DLMF/Mathieu/Modified/Properties.lean#L139) (proved). The modified Mathieu function; `Fe_n(·, q)` solves the modified Mathieu equation with `a = a_n(q)` , `(n, q) ≠ (0, 0)`.
- [28.20.E7](https://dlmf.nist.gov/28.20.E7): [`DLMF.Mathieu.modMathieuGe`](DLMF/Mathieu/Modified/Basic/Functions.lean#L64) (definition); [`DLMF.Mathieu.isModMathieuSolution_modMathieuGe`](DLMF/Mathieu/Modified/Properties.lean#L154) (proved). The modified Mathieu function; `Ge_n(·, q)` solves the modified Mathieu equation with `a = b_n(q)` .
- [28.20.E8](https://dlmf.nist.gov/28.20.E8): [`DLMF.Mathieu.modMathieuM_three_isBigO`](DLMF/Mathieu/Modified/Properties.lean#L170) (admitted). Asymptotics of `M^{(3)}_ν`. Notation h = √q > 0, recorded on the first theorem that uses it.
- [28.20.E9](https://dlmf.nist.gov/28.20.E9): [`DLMF.Mathieu.modMathieuM_three_isBigO`](DLMF/Mathieu/Modified/Properties.lean#L170) (admitted). Asymptotics of `M^{(3)}_ν`.
- [28.20.E10](https://dlmf.nist.gov/28.20.E10): [`DLMF.Mathieu.modMathieuM_four_isBigO`](DLMF/Mathieu/Modified/Properties.lean#L180) (admitted). Asymptotics of `M^{(4)}_ν`.
- [28.20.E11](https://dlmf.nist.gov/28.20.E11): [`DLMF.Mathieu.modMathieuM_one_isBigO`](DLMF/Mathieu/Modified/Properties.lean#L188) (admitted). Asymptotics of `M^{(1)}_ν`.
- [28.20.E12](https://dlmf.nist.gov/28.20.E12): [`DLMF.Mathieu.modMathieuM_two_isBigO`](DLMF/Mathieu/Modified/Properties.lean#L197) (admitted). Asymptotics of `M^{(2)}_ν`.
- [28.20.E13](https://dlmf.nist.gov/28.20.E13): [`DLMF.Mathieu.modMathieuM_three`](DLMF/Mathieu/Modified/Properties.lean#L391) (proved). `M^{(3)}_ν = M^{(1)}_ν + i M^{(2)}_ν` , `h ≠ 0`, admissible `(ν, h)`.
- [28.20.E14](https://dlmf.nist.gov/28.20.E14): [`DLMF.Mathieu.modMathieuM_four`](DLMF/Mathieu/Modified/Properties.lean#L401) (proved). `M^{(4)}_ν = M^{(1)}_ν - i M^{(2)}_ν` , `h ≠ 0`, admissible `(ν, h)`.
- [28.20.E15](https://dlmf.nist.gov/28.20.E15): [`DLMF.Mathieu.radialMathieuMc`](DLMF/Mathieu/Modified/Basic/Functions.lean#L155) (definition). The radial Mathieu function.
- [28.20.E16](https://dlmf.nist.gov/28.20.E16): [`DLMF.Mathieu.radialMathieuMs`](DLMF/Mathieu/Modified/Basic/Functions.lean#L161) (definition). The radial Mathieu function.
- [28.20.E17](https://dlmf.nist.gov/28.20.E17): [`DLMF.Mathieu.modMathieuIe`](DLMF/Mathieu/Modified/Basic/Functions.lean#L169) (definition). `Ie_n(z, h) = i^{-n} Mc^{(1)}_n(z, ih)` .
- [28.20.E18](https://dlmf.nist.gov/28.20.E18): [`DLMF.Mathieu.modMathieuIo`](DLMF/Mathieu/Modified/Basic/Functions.lean#L174) (definition). `Io_n(z, h) = i^{-n} Ms^{(1)}_n(z, ih)` .
- [28.20.E19](https://dlmf.nist.gov/28.20.E19): [`DLMF.Mathieu.modMathieuKe`](DLMF/Mathieu/Modified/Basic/Functions.lean#L179) (definition). `Ke_n(z, h)`.
- [28.20.E20](https://dlmf.nist.gov/28.20.E20): [`DLMF.Mathieu.modMathieuKo`](DLMF/Mathieu/Modified/Basic/Functions.lean#L186) (definition). `Ko_n(z, h)`.
- [28.20.E21](https://dlmf.nist.gov/28.20.E21): [`DLMF.Mathieu.modMathieuM_wronskian_two`](DLMF/Mathieu/Modified/Properties.lean#L413) (proved from admissions); [`DLMF.Mathieu.modMathieuM_wronskian_three`](DLMF/Mathieu/Modified/Properties.lean#L448) (proved from admissions). Wronskians.
- [28.20.E22](https://dlmf.nist.gov/28.20.E22): [`DLMF.Mathieu.modMathieuM_add_pi_div_two`](DLMF/Mathieu/Modified/Properties.lean#L509) (proved from admissions). Shift by `±πi/2`.
- [28.20.E23](https://dlmf.nist.gov/28.20.E23): [`DLMF.Mathieu.radialMathieu_add_pi_div_two_even`](DLMF/Mathieu/Modified/Properties.lean#L815) (proved). Shift by `±πi/2`.
- [28.20.E24](https://dlmf.nist.gov/28.20.E24): [`DLMF.Mathieu.radialMathieu_add_pi_div_two_odd`](DLMF/Mathieu/Modified/Properties.lean#L840) (proved). Shift by `±πi/2`.
- [28.20.E25](https://dlmf.nist.gov/28.20.E25): [`DLMF.Mathieu.modMathieuM_one_add_int_mul_pi_I`](DLMF/Mathieu/Modified/Properties.lean#L879) (proved); [`DLMF.Mathieu.modMathieuM_two_add_int_mul_pi_I`](DLMF/Mathieu/Modified/Properties.lean#L964) (proved from admissions); [`DLMF.Mathieu.modMathieuM_three_add_int_mul_pi_I`](DLMF/Mathieu/Modified/Properties.lean#L981) (proved from admissions); [`DLMF.Mathieu.modMathieuM_four_add_int_mul_pi_I`](DLMF/Mathieu/Modified/Properties.lean#L1008) (proved from admissions). Shift by `sπi`.

## [§28.21 Graphics](https://dlmf.nist.gov/28.21)

- 28.21: excluded: graphics (figures of modified Mathieu functions).

## [§28.22 Connection Formulas](https://dlmf.nist.gov/28.22)

- [28.22.E1](https://dlmf.nist.gov/28.22.E1): [`DLMF.Mathieu.radialMathieuMc_one_eq`](DLMF/Mathieu/Modified/Connection.lean#L28) (proved). Connection formula.
- [28.22.E2](https://dlmf.nist.gov/28.22.E2): [`DLMF.Mathieu.radialMathieuMs_one_eq`](DLMF/Mathieu/Modified/Connection.lean#L36) (proved). Connection formula.
- [28.22.E3](https://dlmf.nist.gov/28.22.E3): [`DLMF.Mathieu.radialMathieuMc_two_eq`](DLMF/Mathieu/Modified/Connection.lean#L45) (proved). Connection formula.
- [28.22.E4](https://dlmf.nist.gov/28.22.E4): [`DLMF.Mathieu.radialMathieuMs_two_eq`](DLMF/Mathieu/Modified/Connection.lean#L55) (proved). Connection formula.
- [28.22.E5](https://dlmf.nist.gov/28.22.E5): [`DLMF.Mathieu.mathieuJoinGe`](DLMF/Mathieu/Modified/Basic/Functions.lean#L221) (definition). The joining factor.
- [28.22.E6](https://dlmf.nist.gov/28.22.E6): [`DLMF.Mathieu.mathieuJoinGe`](DLMF/Mathieu/Modified/Basic/Functions.lean#L221) (definition). The joining factor.
- [28.22.E7](https://dlmf.nist.gov/28.22.E7): [`DLMF.Mathieu.mathieuJoinGo`](DLMF/Mathieu/Modified/Basic/Functions.lean#L233) (definition). The joining factor.
- [28.22.E8](https://dlmf.nist.gov/28.22.E8): [`DLMF.Mathieu.mathieuJoinGo`](DLMF/Mathieu/Modified/Basic/Functions.lean#L233) (definition). The joining factor.
- [28.22.E9](https://dlmf.nist.gov/28.22.E9): [`DLMF.Mathieu.mathieuJoinFe`](DLMF/Mathieu/Modified/Basic/Functions.lean#L245) (definition). The joining factor.
- [28.22.E10](https://dlmf.nist.gov/28.22.E10): [`DLMF.Mathieu.mathieuJoinFo`](DLMF/Mathieu/Modified/Basic/Functions.lean#L250) (definition). The joining factor.
- [28.22.E11](https://dlmf.nist.gov/28.22.E11): [`DLMF.Mathieu.radialMathieu_two_zero`](DLMF/Mathieu/Modified/Connection.lean#L82) (proved from admissions). Values at `z = 0`.
- [28.22.E12](https://dlmf.nist.gov/28.22.E12): [`DLMF.Mathieu.mathieuFe_ge_zero_eq_joinG`](DLMF/Mathieu/Modified/Connection.lean#L164) (proved from admissions). Initial values of the second solutions.
- [28.22.E13](https://dlmf.nist.gov/28.22.E13): [`DLMF.Mathieu.modMathieuM_one_eq_modMathieuMe`](DLMF/Mathieu/Modified/Connection.lean#L318) (proved from admissions). Noninteger order.
- [28.22.E14](https://dlmf.nist.gov/28.22.E14): [`DLMF.Mathieu.modMathieuM_two_eq`](DLMF/Mathieu/Modified/Connection.lean#L387) (proved from admissions). Noninteger order.

## [§28.23 Expansions in Series of Bessel Functions](https://dlmf.nist.gov/28.23)

- [28.23.E1](https://dlmf.nist.gov/28.23.E1): [`DLMF.Mathieu.mathieuCylExp`](DLMF/Mathieu/Modified/Basic/Functions.lean#L87) (definition); [`DLMF.Mathieu.mathieuCyl`](DLMF/Mathieu/Modified/Basic/Functions.lean#L99) (definition); [`DLMF.Mathieu.mathieuCyl_three_four`](DLMF/Mathieu/Modified/BesselSeries.lean#L49) (proved); [`DLMF.Mathieu.mathieuCylExp_eq_mathieuCyl`](DLMF/Mathieu/Modified/BesselSeries.lean#L138) (proved). The cylinder functions; The principal-branch cylinder functions `𝒞^{(j)}_μ(w)` of DLMF 28.23.1 (`J_μ`, `Y_μ`, `H^{(1)}_μ`, `H^{(2)}_μ` at `w`, with `DLMF.Bessel.besselY`); junk `0` for.
- [28.23.E2](https://dlmf.nist.gov/28.23.E2): [`DLMF.Mathieu.hasSum_modMathieuM_cosh`](DLMF/Mathieu/Modified/BesselSeries.lean#L150) (admitted). Expansion in Bessel functions. **Corrected domain**: DLMF says valid for all z when j = 1; true only for |cosh z| > 1 (see Corrections).
- [28.23.E3](https://dlmf.nist.gov/28.23.E3): [`DLMF.Mathieu.hasSum_modMathieuM_cosh_deriv`](DLMF/Mathieu/Modified/BesselSeries.lean#L164) (admitted). Expansion in Bessel functions. **Corrected domain** (|cosh z| > 1; see Corrections).
- [28.23.E4](https://dlmf.nist.gov/28.23.E4): [`DLMF.Mathieu.hasSum_modMathieuM_sinh`](DLMF/Mathieu/Modified/BesselSeries.lean#L176) (admitted). Expansion in Bessel functions. **Corrected domain** (|sinh z| > 1; see Corrections).
- [28.23.E5](https://dlmf.nist.gov/28.23.E5): [`DLMF.Mathieu.hasSum_modMathieuM_sinh_deriv`](DLMF/Mathieu/Modified/BesselSeries.lean#L188) (admitted). Expansion in Bessel functions. **Corrected domain** (|sinh z| > 1; see Corrections).
- [28.23.E6](https://dlmf.nist.gov/28.23.E6): [`DLMF.Mathieu.hasSum_radialMathieuMc_even_cosh`](DLMF/Mathieu/Modified/BesselSeries.lean#L200) (admitted). Integer-order expansion.
- [28.23.E7](https://dlmf.nist.gov/28.23.E7): [`DLMF.Mathieu.hasSum_radialMathieuMc_even_sinh`](DLMF/Mathieu/Modified/BesselSeries.lean#L213) (admitted). Integer-order expansion.
- [28.23.E8](https://dlmf.nist.gov/28.23.E8): [`DLMF.Mathieu.hasSum_radialMathieuMc_odd_cosh`](DLMF/Mathieu/Modified/BesselSeries.lean#L223) (admitted). Integer-order expansion.
- [28.23.E9](https://dlmf.nist.gov/28.23.E9): [`DLMF.Mathieu.hasSum_radialMathieuMc_odd_sinh`](DLMF/Mathieu/Modified/BesselSeries.lean#L235) (admitted). Integer-order expansion.
- [28.23.E10](https://dlmf.nist.gov/28.23.E10): [`DLMF.Mathieu.hasSum_radialMathieuMs_odd_cosh`](DLMF/Mathieu/Modified/BesselSeries.lean#L248) (admitted). Integer-order expansion.
- [28.23.E11](https://dlmf.nist.gov/28.23.E11): [`DLMF.Mathieu.hasSum_radialMathieuMs_odd_sinh`](DLMF/Mathieu/Modified/BesselSeries.lean#L261) (admitted). Integer-order expansion.
- [28.23.E12](https://dlmf.nist.gov/28.23.E12): [`DLMF.Mathieu.hasSum_radialMathieuMs_even_cosh`](DLMF/Mathieu/Modified/BesselSeries.lean#L273) (admitted). Integer-order expansion.
- [28.23.E13](https://dlmf.nist.gov/28.23.E13): [`DLMF.Mathieu.hasSum_radialMathieuMs_even_sinh`](DLMF/Mathieu/Modified/BesselSeries.lean#L286) (admitted). Integer-order expansion.
- [28.23](https://dlmf.nist.gov/28.23): [`DLMF.Mathieu.hasSum_radialMathieuMc_even_cosh`](DLMF/Mathieu/Modified/BesselSeries.lean#L200) (admitted); [`DLMF.Mathieu.hasSum_radialMathieuMc_even_sinh`](DLMF/Mathieu/Modified/BesselSeries.lean#L213) (admitted); [`DLMF.Mathieu.hasSum_radialMathieuMc_odd_cosh`](DLMF/Mathieu/Modified/BesselSeries.lean#L223) (admitted); [`DLMF.Mathieu.hasSum_radialMathieuMc_odd_sinh`](DLMF/Mathieu/Modified/BesselSeries.lean#L235) (admitted); [`DLMF.Mathieu.hasSum_radialMathieuMs_even_cosh`](DLMF/Mathieu/Modified/BesselSeries.lean#L273) (admitted); [`DLMF.Mathieu.hasSum_radialMathieuMs_even_sinh`](DLMF/Mathieu/Modified/BesselSeries.lean#L286) (admitted); [`DLMF.Mathieu.hasSum_radialMathieuMs_odd_cosh`](DLMF/Mathieu/Modified/BesselSeries.lean#L248) (admitted); [`DLMF.Mathieu.hasSum_radialMathieuMs_odd_sinh`](DLMF/Mathieu/Modified/BesselSeries.lean#L261) (admitted).

## [§28.24 Expansions in Series of Cross-Products of Bessel Functions or Modified Bessel Functions](https://dlmf.nist.gov/28.24)

- [28.24.E1](https://dlmf.nist.gov/28.24.E1): [`DLMF.Mathieu.hasSum_modMathieuTerm`](DLMF/Mathieu/Modified/BesselSeries.lean#L301) (proved). Cross-product expansion.
- [28.24.E2](https://dlmf.nist.gov/28.24.E2): [`DLMF.Mathieu.hasSum_radialMathieuMc_even_cross`](DLMF/Mathieu/Modified/BesselSeries.lean#L328) (proved). Cross-product expansion.
- [28.24.E3](https://dlmf.nist.gov/28.24.E3): [`DLMF.Mathieu.hasSum_radialMathieuMc_odd_cross`](DLMF/Mathieu/Modified/BesselSeries.lean#L342) (proved). Cross-product expansion.
- [28.24.E4](https://dlmf.nist.gov/28.24.E4): [`DLMF.Mathieu.hasSum_radialMathieuMs_odd_cross`](DLMF/Mathieu/Modified/BesselSeries.lean#L356) (proved). Cross-product expansion.
- [28.24.E5](https://dlmf.nist.gov/28.24.E5): [`DLMF.Mathieu.hasSum_radialMathieuMs_even_cross`](DLMF/Mathieu/Modified/BesselSeries.lean#L370) (proved). Cross-product expansion.
- [28.24.E6](https://dlmf.nist.gov/28.24.E6): [`DLMF.Mathieu.hasSum_modMathieuIe_even`](DLMF/Mathieu/Modified/BesselSeries.lean#L385) (proved). Modified-Bessel cross-product expansion.
- [28.24.E7](https://dlmf.nist.gov/28.24.E7): [`DLMF.Mathieu.hasSum_modMathieuIo_even`](DLMF/Mathieu/Modified/BesselSeries.lean#L402) (proved). Modified-Bessel cross-product expansion.
- [28.24.E8](https://dlmf.nist.gov/28.24.E8): [`DLMF.Mathieu.hasSum_modMathieuIe_odd`](DLMF/Mathieu/Modified/BesselSeries.lean#L419) (proved). Modified-Bessel cross-product expansion.
- [28.24.E9](https://dlmf.nist.gov/28.24.E9): [`DLMF.Mathieu.hasSum_modMathieuIo_odd`](DLMF/Mathieu/Modified/BesselSeries.lean#L437) (proved). Modified-Bessel cross-product expansion.
- [28.24.E10](https://dlmf.nist.gov/28.24.E10): [`DLMF.Mathieu.hasSum_modMathieuKe_even`](DLMF/Mathieu/Modified/BesselSeries.lean#L454) (proved). Modified-Bessel cross-product expansion. Restricted to |Im z| < π (principal K).
- [28.24.E11](https://dlmf.nist.gov/28.24.E11): [`DLMF.Mathieu.hasSum_modMathieuKo_even`](DLMF/Mathieu/Modified/BesselSeries.lean#L471) (proved). Modified-Bessel cross-product expansion. Restricted to |Im z| < π (principal K).
- [28.24.E12](https://dlmf.nist.gov/28.24.E12): [`DLMF.Mathieu.hasSum_modMathieuKe_odd`](DLMF/Mathieu/Modified/BesselSeries.lean#L489) (proved). Modified-Bessel cross-product expansion. Restricted to |Im z| < π (principal K).
- [28.24.E13](https://dlmf.nist.gov/28.24.E13): [`DLMF.Mathieu.hasSum_modMathieuKo_odd`](DLMF/Mathieu/Modified/BesselSeries.lean#L507) (proved). Modified-Bessel cross-product expansion. Restricted to |Im z| < π (principal K).
- [28.24](https://dlmf.nist.gov/28.24): [`DLMF.Mathieu.modMathieuTerm_locally_uniform`](DLMF/Mathieu/Modified/BesselSeries.lean#L313) (proved).

## [§28.25 Asymptotic Expansions for Large ℜz](https://dlmf.nist.gov/28.25)

- [28.25.E1](https://dlmf.nist.gov/28.25.E1): [`DLMF.Mathieu.modMathieuM_three_hasAsymptoticExpansion`](DLMF/Mathieu/Modified/Asymptotics.lean#L60) (admitted); [`DLMF.Mathieu.modMathieuM_four_hasAsymptoticExpansion`](DLMF/Mathieu/Modified/Asymptotics.lean#L73) (admitted). Asymptotic expansion of `M^{(3)}_ν`; Asymptotic expansion of `M^{(4)}_ν`.
- [28.25.E2](https://dlmf.nist.gov/28.25.E2): [`DLMF.Mathieu.modMathieuAsympD`](DLMF/Mathieu/Modified/Basic/AsymptoticData.lean#L33) (definition); [`DLMF.Mathieu.modMathieuAsympD_zero`](DLMF/Mathieu/Modified/Asymptotics.lean#L34) (proved); [`DLMF.Mathieu.modMathieuAsympD_recurrence`](DLMF/Mathieu/Modified/Asymptotics.lean#L38) (proved); [`DLMF.Mathieu.modMathieuAsympDPair_fst`](DLMF/Mathieu/Modified/Asymptotics.lean#L52) (proved). The coefficients `D^±_m` of DLMF 28.25.1, defined by 28.25.2 (`D_{-1} = 0`, `D_0 = 1`) and the recurrence 28.25.3; `σ = 1` gives `D^+_m` (for `M^{(3)}_ν`); `D^±_{0} = 1` .
- [28.25.E3](https://dlmf.nist.gov/28.25.E3): [`DLMF.Mathieu.modMathieuAsympD`](DLMF/Mathieu/Modified/Basic/AsymptoticData.lean#L33) (definition); [`DLMF.Mathieu.modMathieuAsympD_recurrence`](DLMF/Mathieu/Modified/Asymptotics.lean#L38) (proved). The coefficients `D^±_m` of DLMF 28.25.1, defined by 28.25.2 (`D_{-1} = 0`, `D_0 = 1`) and the recurrence 28.25.3; `σ = 1` gives `D^+_m` (for `M^{(3)}_ν`); The recurrence 28.25.3 for `m ≥ 0`, with `D_{-1} = 0`.
- [28.25.E4](https://dlmf.nist.gov/28.25.E4): [`DLMF.Mathieu.modMathieuM_three_hasAsymptoticExpansion`](DLMF/Mathieu/Modified/Asymptotics.lean#L60) (admitted). Asymptotic expansion of `M^{(3)}_ν`.
- [28.25.E5](https://dlmf.nist.gov/28.25.E5): [`DLMF.Mathieu.modMathieuM_four_hasAsymptoticExpansion`](DLMF/Mathieu/Modified/Asymptotics.lean#L73) (admitted). Asymptotic expansion of `M^{(4)}_ν`.

## [§28.26 Asymptotic Approximations for Large q](https://dlmf.nist.gov/28.26)

- [28.26.i](https://dlmf.nist.gov/28.26.i): [`DLMF.Mathieu.goldsteinFs_Gs_isBigO`](DLMF/Mathieu/Modified/Asymptotics.lean#L168) (admitted). Goldstein's expansions of `Fs_m`, `Gs_m`.
- [28.26.E1](https://dlmf.nist.gov/28.26.E1): [`DLMF.Mathieu.goldsteinFc`](DLMF/Mathieu/Modified/Basic/AsymptoticData.lean#L59) (definition); [`DLMF.Mathieu.goldsteinGc`](DLMF/Mathieu/Modified/Basic/AsymptoticData.lean#L67) (definition); [`DLMF.Mathieu.radialMathieuMc_three_eq_goldstein`](DLMF/Mathieu/Modified/Asymptotics.lean#L87) (proved). Goldstein's `Fc_m(z, h)`, defined with `Gc_m` so that 28.26.1 holds; Goldstein's `Gc_m(z, h) = (π h cosh z)^{1/2} (sin φ Mc^{(1)}_m - cos φ Mc^{(2)}_m)`; with `Fc_m` it gives.
- [28.26.E2](https://dlmf.nist.gov/28.26.E2): [`DLMF.Mathieu.goldsteinFs`](DLMF/Mathieu/Modified/Basic/AsymptoticData.lean#L75) (definition); [`DLMF.Mathieu.goldsteinGs`](DLMF/Mathieu/Modified/Basic/AsymptoticData.lean#L84) (definition); [`DLMF.Mathieu.radialMathieuMs_three_eq_goldstein`](DLMF/Mathieu/Modified/Asymptotics.lean#L118) (proved). Goldstein's `Fs_m(z, h) = (π h cosh z)^{1/2} (sin φ Ms^{(1)}_{m+1} - cos φ Ms^{(2)}_{m+1})`; with `Gs_m` it gives; Goldstein's `Gs_m(z, h) = -(π h cosh z)^{1/2} (cos φ Ms^{(1)}_{m+1} + sin φ Ms^{(2)}_{m+1})` .
- [28.26.E3](https://dlmf.nist.gov/28.26.E3): [`DLMF.Mathieu.goldsteinPhase`](DLMF/Mathieu/Modified/Basic/AsymptoticData.lean#L53) (definition). The phase `φ = 2h sinh z - (m + 1/2) arctan(sinh z)` of DLMF 28.26.3 (principal complex `arctan`, which is analytic for `Re z > 0`, `|Im z| < π/2`).
- [28.26.E4](https://dlmf.nist.gov/28.26.E4): [`DLMF.Mathieu.goldsteinFc_isBigO`](DLMF/Mathieu/Modified/Asymptotics.lean#L150) (admitted). Goldstein's expansion of `Fc_m`.
- [28.26.E5](https://dlmf.nist.gov/28.26.E5): [`DLMF.Mathieu.goldsteinGc_isBigO`](DLMF/Mathieu/Modified/Asymptotics.lean#L160) (admitted). Goldstein's expansion of `Gc_m`.
- 28.26.ii: pointer only (uniform approximations: §28.8(iv) and Naylor (1984, 1987, 1989)). Not acquired.

## [§28.27 Addition Theorems](https://dlmf.nist.gov/28.27)

- 28.27: no statements (prose pointer to Meixner, Schäfke and Wolf, 1980, §2.4). Not acquired.

## [§28.28 Integrals, Integral Representations, and Integral Equations](https://dlmf.nist.gov/28.28)

- [28.28.i](https://dlmf.nist.gov/28.28.i): [`DLMF.Mathieu.integrableOn_exp_cosh_modMathieu`](DLMF/Mathieu/Modified/Integrals.lean#L214) (admitted). Absolute convergence.
- [28.28.E1](https://dlmf.nist.gov/28.28.E1): [`DLMF.Mathieu.mathieuKernelW`](DLMF/Mathieu/Modified/Basic/IntegralKernels.lean#L23) (definition). `w = cosh z cos t cos α + sinh z sin t sin α` .
- [28.28.E2](https://dlmf.nist.gov/28.28.E2): [`DLMF.Mathieu.integral_exp_mathieuCe`](DLMF/Mathieu/Modified/Integrals.lean#L55) (proved). Integral equation.
- [28.28.E3](https://dlmf.nist.gov/28.28.E3): [`DLMF.Mathieu.integral_exp_mathieuSe`](DLMF/Mathieu/Modified/Integrals.lean#L65) (proved). Integral equation.
- [28.28.E4](https://dlmf.nist.gov/28.28.E4): [`DLMF.Mathieu.integral_dw_exp_mathieuCe`](DLMF/Mathieu/Modified/Integrals.lean#L98) (proved). Integral equation.
- [28.28.E5](https://dlmf.nist.gov/28.28.E5): [`DLMF.Mathieu.integral_dw_exp_mathieuSe`](DLMF/Mathieu/Modified/Integrals.lean#L112) (proved). Integral equation.
- [28.28.E6](https://dlmf.nist.gov/28.28.E6): [`DLMF.Mathieu.mathieuPathIntegral`](DLMF/Mathieu/Modified/Basic/IntegralKernels.lean#L28) (definition); [`DLMF.Mathieu.pathIntegral_exp_mathieuMe`](DLMF/Mathieu/Modified/Integrals.lean#L126) (admitted). The integral along the path `𝓛_j` of DLMF 28.28.6, realized as a polygonal path with vertical rays; Integral representation along `𝓛_j`.
- [28.28.E7](https://dlmf.nist.gov/28.28.E7): [`DLMF.Mathieu.pathIntegral_exp_mathieuMe`](DLMF/Mathieu/Modified/Integrals.lean#L126) (admitted). Integral representation along `𝓛_j`.
- [28.28.E8](https://dlmf.nist.gov/28.28.E8): [`DLMF.Mathieu.pathIntegral_dw_exp_mathieuMe`](DLMF/Mathieu/Modified/Integrals.lean#L138) (admitted). Integral representation along `𝓛_j`.
- [28.28.E9](https://dlmf.nist.gov/28.28.E9): [`DLMF.Mathieu.pathIntegral_one_exp_mathieuMe`](DLMF/Mathieu/Modified/Integrals.lean#L151) (admitted). Integral representation along `𝓛_1`.
- [28.28.E10](https://dlmf.nist.gov/28.28.E10): [`DLMF.Mathieu.integral_exp_cosh_modMathieuCe`](DLMF/Mathieu/Modified/Integrals.lean#L163) (admitted); [`DLMF.Mathieu.integral_exp_cosh_modMathieuSe`](DLMF/Mathieu/Modified/Integrals.lean#L177) (admitted); [`DLMF.Mathieu.integral_exp_cosh_modMathieuFe`](DLMF/Mathieu/Modified/Integrals.lean#L190) (admitted); [`DLMF.Mathieu.integral_exp_cosh_modMathieuGe`](DLMF/Mathieu/Modified/Integrals.lean#L203) (admitted). Laplace-type integral.
- [28.28.E11](https://dlmf.nist.gov/28.28.E11): [`DLMF.Mathieu.integral_exp_cosh_modMathieuCe`](DLMF/Mathieu/Modified/Integrals.lean#L163) (admitted). Laplace-type integral. **Corrected**: factor e^{iνπ/2}, not e^{iνπ} (see Corrections).
- [28.28.E12](https://dlmf.nist.gov/28.28.E12): [`DLMF.Mathieu.integral_exp_cosh_modMathieuSe`](DLMF/Mathieu/Modified/Integrals.lean#L177) (admitted). Laplace-type integral.
- [28.28.E13](https://dlmf.nist.gov/28.28.E13): [`DLMF.Mathieu.integral_exp_cosh_modMathieuFe`](DLMF/Mathieu/Modified/Integrals.lean#L190) (admitted). Laplace-type integral.
- [28.28.E14](https://dlmf.nist.gov/28.28.E14): [`DLMF.Mathieu.integral_exp_cosh_modMathieuGe`](DLMF/Mathieu/Modified/Integrals.lean#L203) (admitted). Laplace-type integral.
- [28.28.E15](https://dlmf.nist.gov/28.28.E15): [`DLMF.Mathieu.integral_cos_cosh_modMathieuCe`](DLMF/Mathieu/Modified/Integrals.lean#L227) (admitted). Cosine transform.
- [28.28.E16](https://dlmf.nist.gov/28.28.E16): [`DLMF.Mathieu.integral_sin_cosh_modMathieuCe`](DLMF/Mathieu/Modified/Integrals.lean#L237) (admitted). Sine transform. **Corrected**: overall sign of the right-hand side and the range of the lower sign (see Corrections).
- [28.28.E17](https://dlmf.nist.gov/28.28.E17): [`DLMF.Mathieu.integral_cyl_mathieuMe`](DLMF/Mathieu/Modified/Integrals.lean#L352) (admitted). Integral of a product with a Bessel function.
- [28.28.E18](https://dlmf.nist.gov/28.28.E18): [`DLMF.Mathieu.mathieuKernelR`](DLMF/Mathieu/Modified/Basic/IntegralKernels.lean#L50) (definition); [`DLMF.Mathieu.mathieuKernelR_sq`](DLMF/Mathieu/Modified/Integrals.lean#L265) (proved); [`DLMF.Mathieu.mathieuKernelR_zero`](DLMF/Mathieu/Modified/Integrals.lean#L298) (proved). `R(z, t)` of DLMF 28.28.18; `R(z, t)² = ½(cosh 2z + cos 2t)` , `Re z > 0`, real `t`.
- [28.28.E19](https://dlmf.nist.gov/28.28.E19): [`DLMF.Mathieu.mathieuKernelPhi`](DLMF/Mathieu/Modified/Basic/IntegralKernels.lean#L56) (definition); [`DLMF.Mathieu.exp_two_I_mathieuKernelPhi`](DLMF/Mathieu/Modified/Integrals.lean#L312) (proved); [`DLMF.Mathieu.mathieuKernelPhi_zero`](DLMF/Mathieu/Modified/Integrals.lean#L347) (proved). `φ(z, t)` of DLMF 28.28.19; `e^{2iφ} = cosh(z + it) / cosh(z - it)` , `Re z > 0`, real `t`.
- [28.28.E20](https://dlmf.nist.gov/28.28.E20): [`DLMF.Mathieu.integral_cyl_mathieuCe_even`](DLMF/Mathieu/Modified/Integrals.lean#L364) (admitted). Integer order.
- [28.28.E21](https://dlmf.nist.gov/28.28.E21): [`DLMF.Mathieu.integral_cyl_mathieuCe_odd`](DLMF/Mathieu/Modified/Integrals.lean#L376) (admitted). Integer order.
- [28.28.E22](https://dlmf.nist.gov/28.28.E22): [`DLMF.Mathieu.integral_cyl_mathieuSe_odd`](DLMF/Mathieu/Modified/Integrals.lean#L388) (admitted). Integer order.
- [28.28.E23](https://dlmf.nist.gov/28.28.E23): [`DLMF.Mathieu.integral_cyl_mathieuSe_even`](DLMF/Mathieu/Modified/Integrals.lean#L400) (admitted). Integer order.
- [28.28.E24](https://dlmf.nist.gov/28.28.E24): [`DLMF.Mathieu.modMathieuD0`](DLMF/Mathieu/Modified/Basic/IntegralKernels.lean#L71) (definition); [`DLMF.Mathieu.modMathieuD1`](DLMF/Mathieu/Modified/Basic/IntegralKernels.lean#L76) (definition). `D_0(ν, μ, z) = M^{(3)}_ν(z) M^{(4)}_μ(z) - M^{(4)}_ν(z) M^{(3)}_μ(z)` ; `D_1(ν, μ, z) = M^{(3)'}_ν(z) M^{(4)}_μ(z) - M^{(4)'}_ν(z) M^{(3)}_μ(z)` .
- [28.28.E25](https://dlmf.nist.gov/28.28.E25): [`DLMF.Mathieu.integral_cos_mathieuMe_mul`](DLMF/Mathieu/Modified/Integrals.lean#L417) (admitted). DLMF 28.28.25.
- [28.28.E26](https://dlmf.nist.gov/28.28.E26): [`DLMF.Mathieu.integral_sin_mathieuMe_mul`](DLMF/Mathieu/Modified/Integrals.lean#L428) (admitted). DLMF 28.28.26.
- [28.28.E27](https://dlmf.nist.gov/28.28.E27): [`DLMF.Mathieu.mathieuAlpha0`](DLMF/Mathieu/Modified/Basic/IntegralKernels.lean#L82) (definition); [`DLMF.Mathieu.mathieuAlpha0_eq`](DLMF/Mathieu/Modified/Integrals.lean#L439) (admitted). `α^{(0)}_{ν,m} = (2π)⁻¹ ∫₀^{2π} cos t me_ν(t, h²) me_{-ν-2m-1}(t, h²) dt` ; DLMF 28.28.27 (second equality), `D_0(ν, ν+2m+1, 0) ≠ 0`.
- [28.28.E28](https://dlmf.nist.gov/28.28.E28): [`DLMF.Mathieu.mathieuAlpha1`](DLMF/Mathieu/Modified/Basic/IntegralKernels.lean#L89) (definition); [`DLMF.Mathieu.mathieuAlpha1_eq`](DLMF/Mathieu/Modified/Integrals.lean#L448) (admitted). `α^{(1)}_{ν,m} = (2π)⁻¹ ∫₀^{2π} sin t me_ν(t, h²) me_{-ν-2m-1}(t, h²) dt` ; DLMF 28.28.28 (second equality), `D_1(ν, ν+2m+1, 0) ≠ 0`.
- [28.28.E29](https://dlmf.nist.gov/28.28.E29): [`DLMF.Mathieu.integral_sin_deriv_mathieuMe_mul`](DLMF/Mathieu/Modified/Integrals.lean#L458) (admitted). DLMF 28.28.29.
- [28.28.E30](https://dlmf.nist.gov/28.28.E30): [`DLMF.Mathieu.integral_cos_deriv_mathieuMe_mul`](DLMF/Mathieu/Modified/Integrals.lean#L470) (admitted). DLMF 28.28.30.
- [28.28.E31](https://dlmf.nist.gov/28.28.E31): [`DLMF.Mathieu.integral_cos_sin_mathieuMe_mul`](DLMF/Mathieu/Modified/Integrals.lean#L482) (admitted). DLMF 28.28.31.
- [28.28.E32](https://dlmf.nist.gov/28.28.E32): [`DLMF.Mathieu.integral_deriv_mathieuMe_mul`](DLMF/Mathieu/Modified/Integrals.lean#L493) (admitted). DLMF 28.28.32.
- [28.28.E33](https://dlmf.nist.gov/28.28.E33): [`DLMF.Mathieu.mathieuGammaInt`](DLMF/Mathieu/Modified/Basic/IntegralKernels.lean#L96) (definition); [`DLMF.Mathieu.mathieuGammaInt_eq`](DLMF/Mathieu/Modified/Integrals.lean#L505) (admitted). `γ_{ν,m} = (2π)⁻¹ ∫₀^{2π} me'_ν(t, h²) me_{-ν-2m}(t, h²) dt` ; DLMF 28.28.33 (second equality), `D_1(ν, ν+2m, 0) ≠ 0`.
- [28.28.E34](https://dlmf.nist.gov/28.28.E34): [`DLMF.Mathieu.pv_integral_deriv_mathieuMe_div_sin`](DLMF/Mathieu/Modified/Integrals.lean#L515) (admitted). DLMF 28.28.34 (Cauchy principal value at the zeros `0, π, 2π` of `sin t`; the integrand is `2π`-periodic, so the excluded set `{|sin t| ≤ ε}` is symmetric about.
- [28.28.E35](https://dlmf.nist.gov/28.28.E35): [`DLMF.Mathieu.radialMathieuDs0`](DLMF/Mathieu/Modified/Basic/IntegralKernels.lean#L103) (definition); [`DLMF.Mathieu.radialMathieuDs1`](DLMF/Mathieu/Modified/Basic/IntegralKernels.lean#L109) (definition); [`DLMF.Mathieu.radialMathieuDs2`](DLMF/Mathieu/Modified/Basic/IntegralKernels.lean#L115) (definition). `Ds_0(n, m, z) = Ms^{(3)}_n Ms^{(4)}_m - Ms^{(4)}_n Ms^{(3)}_m` ; `Ds_1(n, m, z) = Ms^{(3)'}_n Ms^{(4)}_m - Ms^{(4)'}_n Ms^{(3)}_m` .
- [28.28.E36](https://dlmf.nist.gov/28.28.E36): [`DLMF.Mathieu.integral_cos_mathieuSe_mul`](DLMF/Mathieu/Modified/Integrals.lean#L533) (admitted). DLMF 28.28.36, `m, n ≥ 1`, `m - n = 2p + 1`.
- [28.28.E37](https://dlmf.nist.gov/28.28.E37): [`DLMF.Mathieu.integral_sin_deriv_mathieuSe_mul`](DLMF/Mathieu/Modified/Integrals.lean#L544) (admitted). DLMF 28.28.37, `m, n ≥ 1`, `m - n = 2p + 1`.
- [28.28.E38](https://dlmf.nist.gov/28.28.E38): [`DLMF.Mathieu.mathieuAlphaHatS`](DLMF/Mathieu/Modified/Basic/IntegralKernels.lean#L145) (definition); [`DLMF.Mathieu.mathieuAlphaHatS_eq`](DLMF/Mathieu/Modified/Integrals.lean#L555) (admitted). `α̂^{(s)}_{n,m} = (2π)⁻¹ ∫₀^{2π} cos t se_n(t, h²) se_m(t, h²) dt` , real `h`; DLMF 28.28.38 (second equality), `m, n ≥ 1`, `m - n = 2p + 1`, `Ds_2(n, m, 0) ≠ 0`.
- [28.28.E39](https://dlmf.nist.gov/28.28.E39): [`DLMF.Mathieu.radialMathieuDc0`](DLMF/Mathieu/Modified/Basic/IntegralKernels.lean#L121) (definition); [`DLMF.Mathieu.radialMathieuDc1`](DLMF/Mathieu/Modified/Basic/IntegralKernels.lean#L127) (definition). `Dc_0(n, m, z) = Mc^{(3)}_n Mc^{(4)}_m - Mc^{(4)}_n Mc^{(3)}_m` ; `Dc_1(n, m, z) = Mc^{(3)'}_n Mc^{(4)}_m - Mc^{(4)'}_n Mc^{(3)}_m` .
- [28.28.E40](https://dlmf.nist.gov/28.28.E40): [`DLMF.Mathieu.radialMathieuDsc0`](DLMF/Mathieu/Modified/Basic/IntegralKernels.lean#L133) (definition); [`DLMF.Mathieu.radialMathieuDsc1`](DLMF/Mathieu/Modified/Basic/IntegralKernels.lean#L139) (definition). `Dsc_0(n, m, z) = Ms^{(3)}_n Mc^{(4)}_m - Ms^{(4)}_n Mc^{(3)}_m` ; `Dsc_1(n, m, z) = Ms^{(3)'}_n Mc^{(4)}_m - Ms^{(4)'}_n Mc^{(3)}_m` .
- [28.28.E41](https://dlmf.nist.gov/28.28.E41): [`DLMF.Mathieu.integral_sin_mathieuSe_mul_mathieuCe`](DLMF/Mathieu/Modified/Integrals.lean#L565) (admitted). DLMF 28.28.41, `m ≥ 0`, `n ≥ 1`, `m - n = 2p + 1`.
- [28.28.E42](https://dlmf.nist.gov/28.28.E42): [`DLMF.Mathieu.integral_cos_deriv_mathieuSe_mul_mathieuCe`](DLMF/Mathieu/Modified/Integrals.lean#L576) (admitted). DLMF 28.28.42, `m ≥ 0`, `n ≥ 1`, `m - n = 2p + 1`.
- [28.28.E43](https://dlmf.nist.gov/28.28.E43): [`DLMF.Mathieu.mathieuBetaHat`](DLMF/Mathieu/Modified/Basic/IntegralKernels.lean#L152) (definition); [`DLMF.Mathieu.mathieuBetaHat_eq`](DLMF/Mathieu/Modified/Integrals.lean#L587) (admitted). `β̂_{n,m} = (2π)⁻¹ ∫₀^{2π} sin t se_n(t, h²) ce_m(t, h²) dt` , real `h`; DLMF 28.28.43 (second equality), `m ≥ 0`, `n ≥ 1`, `m - n = 2p + 1`, `Dsc_1(n, m, 0) ≠ 0`.
- [28.28.E44](https://dlmf.nist.gov/28.28.E44): [`DLMF.Mathieu.integral_sin_two_mathieuSe_mul_mathieuCe`](DLMF/Mathieu/Modified/Integrals.lean#L597) (admitted). DLMF 28.28.44, `m ≥ 0`, `n ≥ 1`, `n - m = 2p`.
- [28.28.E45](https://dlmf.nist.gov/28.28.E45): [`DLMF.Mathieu.integral_deriv_mathieuSe_mul_mathieuCe`](DLMF/Mathieu/Modified/Integrals.lean#L607) (admitted). DLMF 28.28.45, `m ≥ 0`, `n ≥ 1`, `n - m = 2p`.
- [28.28.E46](https://dlmf.nist.gov/28.28.E46): [`DLMF.Mathieu.mathieuGammaHat`](DLMF/Mathieu/Modified/Basic/IntegralKernels.lean#L159) (definition); [`DLMF.Mathieu.mathieuGammaHat_eq`](DLMF/Mathieu/Modified/Integrals.lean#L618) (admitted). `γ̂_{n,m} = (2π)⁻¹ ∫₀^{2π} se'_n(t, h²) ce_m(t, h²) dt` , real `h`; DLMF 28.28.46 (second equality), `m ≥ 0`, `n ≥ 1`, `n - m = 2p`, `Dsc_1(n, m, 0) ≠ 0`.
- [28.28.E47](https://dlmf.nist.gov/28.28.E47): [`DLMF.Mathieu.integral_cos_mathieuCe_mul`](DLMF/Mathieu/Modified/Integrals.lean#L628) (admitted). DLMF 28.28.47, `m, n ≥ 0`, `m - n = 2p + 1`.
- [28.28.E48](https://dlmf.nist.gov/28.28.E48): [`DLMF.Mathieu.integral_sin_deriv_mathieuCe_mul`](DLMF/Mathieu/Modified/Integrals.lean#L639) (admitted). DLMF 28.28.48, `m, n ≥ 0`, `m - n = 2p + 1`.
- [28.28.E49](https://dlmf.nist.gov/28.28.E49): [`DLMF.Mathieu.mathieuAlphaHatC`](DLMF/Mathieu/Modified/Basic/IntegralKernels.lean#L166) (definition); [`DLMF.Mathieu.mathieuAlphaHatC_eq`](DLMF/Mathieu/Modified/Integrals.lean#L650) (admitted). `α̂^{(c)}_{n,m} = (2π)⁻¹ ∫₀^{2π} cos t ce_n(t, h²) ce_m(t, h²) dt` , real `h`; DLMF 28.28.49 (second equality), `m, n ≥ 0`, `m - n = 2p + 1`, `Dc_0(n, m, 0) ≠ 0`.

## Part C: validation

- All six modules build with `lake build DLMF.Mathieu.Modified.Integrals
  DLMF.Mathieu.Modified.Asymptotics`. Each file was also checked with
  `lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false`. There are no warnings other
  than `declaration uses 'sorry'`, and no line is longer than 100 characters.
- `#print axioms` shows only `propext`, `Classical.choice` and `Quot.sound` for the 12 proved
  theorems, for example `modMathieuM_one_add_int_mul_pi_I` (28.20.25, first line), `IsMathieuSolution.isModMathieuSolution_comp`,
  `modMathieuAsympD_recurrence`, `mathieuKernelR_sq` and `exp_two_I_mathieuKernelPhi`. The 9
  theorems proved from admissions also depend on `sorryAx`. For
  `isModMathieuSolution_modMathieuCe` the admission comes from ACQ28A's
  `isMathieuSolution_mathieuCe`, and for `modMathieuM_three` from 28.24.1.
- Numerical checks used independent Python/mpmath eigen-solvers for `a_n`, `b_n`, `λ_ν` and the
  Fourier coefficients (`h = 1.2`, `ν = 0.3`, small `m`, `n`):
  - the independence of 28.24.1 from `n`;
  - the reproduction of 28.23.6–13 and 28.24.2–5 by the general definition for integer `ν`;
  - 28.23.2–3 for `|cosh z| > 1`;
  - 28.20.21–24;
  - 28.22.1–4 and 28.22.9–14;
  - 28.25.1 with the recurrence for `D^±_m`;
  - 28.26.4–5 together with `Fs_m`, `Gs_m`;
  - 28.24.6–13;
  - 28.28.2–5, 7–9 (two parameter sets, rays in the valleys), 12–15, 17, 20–23 and 25–49.
