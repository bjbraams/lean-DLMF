# DLMF Chapter 18 acquisition

Reviewed 2026-09-16 against [NIST DLMF Chapter 18](https://dlmf.nist.gov/18), version 1.2.7 (2026-06-15), and the installed Mathlib 4.34.0 sources. The current toolchain and pinned Mathlib revision are listed in the [README](../../README.md#dependencies-and-upstream-reuse); this acquisition inventory was not re-reviewed in full against those newer sources.

## Scope and status

All sections 18.1–18.37 except graphics (§18.4) were visited. Applications (§§18.38–18.39) and computation (§§18.40–18.42) are excluded. This acquisition covers a broad selection of results with explicit statements and usable definitions. It is **not a complete transcription of every formula**: remaining items are recorded below, including suitable formulas still requiring further transcription or infrastructure.

The acquisition introduced **329 theorem declarations** and **65 definitions** in 15 new Lean modules, initially with **327 new `sorry`s**. Subsequent proof work has removed most of those admissions; on 2026-10-17 the orthogonal-polynomial directory contains **69 `sorry`s** (64 acquired here and five pre-existing). See the [first proof progress report](../../PROOF_PROGRESS_ORTHOGONAL_2026-09-16.md) and [second proof progress report](../../PROOF_PROGRESS_ORTHOGONAL_2026-09-16_2.md) for the completed proofs and validation. `laguerreExtended_eq` and `associated_zero` were already proved at acquisition. The checklist and module snapshot below record acquisition history; elaboration alone does not establish the truth of an admitted statement.

As of 2026-10-24 there are **26 explicit source admissions** in this directory.
The latest round proves Meixner–Pollaczek, q-Hahn, little-q-Jacobi and
Stieltjes–Wigert orthogonality; `Hahn.lean` has no remaining admissions and
`QFamilies.lean` has six. See the
[parallel proof round](../../REVIEW.md#parallel-admission-removal-and-reuse-round-2026-10-24)
for proofs, reused results and validation. The old counts and inline line numbers
below remain a dated acquisition snapshot.

[MathlibCoverage.lean](MathlibCoverage.lean) contains **48 commented upstream statement entries**, each with its DLMF tag. No active duplicate Mathlib theorem is introduced there. CrossRefAttribute cannot attach documentation to an imported declaration, so the tags on upstream excerpts remain inside comments. Existing local matches have live `@[dlmf …]` attributes.

Existing theorem statements and assumptions were preserved. The chapter aggregate imports every new module; the existing `qGegenbauer` definition is tagged in [QSeries/Identities.lean](../QSeries/Identities.lean).

## Conventions and parameter restrictions

- Existing `jacobiPolynomialP`, `ultrasphericalPolynomial`, and `laguerrePolynomialL` use hypergeometric quotients. At singular lower parameters these are not polynomial continuation in the parameters. New statements therefore specify regular parameter ranges. `laguerreExtended` gives the finite polynomial continuation where negative integral parameters are needed, and its agreement with `laguerrePolynomialL` is proved on the regular domain.
- Terminating ordinary and basic hypergeometric definitions use explicit finite cutoffs. Finite families carry degree and lattice bounds; positive-weight statements state their positivity and convergence ranges.
- Mathlib `hermite` is the probabilists’ family; `hermitePolynomialH` is the physicists’ family. Mathlib shifted Legendre uses `P_n(1-2x)`. Existing `qGegenbauer` and definitions named `Laurent` use the Laurent variable, with polynomial argument `(z+z⁻¹)/2`.
- New nonterminating Gauss formulas stay in their series convergence domains. Positive real arguments are used for several power/Bessel identities to make branch choices explicit. No unimplemented analytic continuation or principal-value integral is silently represented by an ordinary sum or integral.
- A tag on a definition, a restricted theorem, or one table row records that correspondence only. It does not claim a proof, all parameter regimes, or every equality in a multi-part display.

## Source corrections

1. [DLMF 18.2.11_1](https://dlmf.nist.gov/18.2.E11_1) has the wrong sign. Telescoping 18.2.11 gives the **negative** next-to-leading/leading coefficient ratio. See `sum_recurrenceDiagonal` in [GeneralIdentities.lean](GeneralIdentities.lean).
2. [DLMF 18.12.17](https://dlmf.nist.gov/18.12.E17) prints `|z| < 1`, but the series requires `|z| < 1/2`. At `x=0`, the even coefficients are `(-1)^k (2k)!/(k!)²`, giving radius `1/2`. See `hermitePolynomialH_half_factorial_generating_function` in [Series.lean](Series.lean).
3. [DLMF 18.17.41](https://dlmf.nist.gov/18.17.E41) has an incorrect power of `a` and denominator-parameter shifts. For `n=0`, the printed answer is `Γ(z)/a²` instead of `Γ(z)/a^z`. The corrected denominator parameters are `(1-z-n)/2` and `(2-z-n)/2`. `hermite_mellin_laplace_transform` in [Integrals.lean](Integrals.lean) uses a finite coefficient sum to avoid removable singularities.

These are checks of the displayed DLMF statements, documented beside the corresponding Lean declarations. They are not claims about errors in AAR. The corrected telescoping theorem is now proved; the other two correction theorems remain admitted. The finite Racah/dual-Hahn weight and norm displays in §18.25, in particular 18.25.14, are deferred pending a normalization check; no correction to that display is asserted here.

## Acquired declarations by module

| Module | Theorems acquired | Definitions acquired | `sorry`s on 2026-10-17 |
| --- | ---: | ---: | ---: |
| [Associated.lean](Associated.lean) | 22 | 14 | 5 |
| [BoundsZeros.lean](BoundsZeros.lean) | 25 | 1 | 11 |
| [ContinuedFractions.lean](ContinuedFractions.lean) | 5 | 1 | 0 |
| [Differential.lean](Differential.lean) | 34 | 0 | 0 |
| [Explicit.lean](Explicit.lean) | 35 | 3 | 0 |
| [GeneralIdentities.lean](GeneralIdentities.lean) | 16 | 10 | 3 |
| [Hahn.lean](Hahn.lean) | 36 | 9 | 3 |
| [Integrals.lean](Integrals.lean) | 54 | 0 | 10 |
| [Limits.lean](Limits.lean) | 14 | 0 | 4 |
| [MathlibCoverage.lean](MathlibCoverage.lean) | 0 | 0 | 0 |
| [Multivariate.lean](Multivariate.lean) | 4 | 2 | 3 |
| [QFamilies.lean](QFamilies.lean) | 19 | 16 | 9 |
| [Series.lean](Series.lean) | 40 | 0 | 9 |
| [UnitCircle.lean](UnitCircle.lean) | 10 | 5 | 3 |
| [Wilson.lean](Wilson.lean) | 15 | 4 | 4 |

The last column was refreshed on 2026-10-17 from the build's `sorry` warnings (69 in this
directory, including five in the pre-existing `General.lean` and `Topics.lean`). Modules added
after the acquisition: [ClassicalInstances.lean](ClassicalInstances.lean) (classical families as
`IsOrthogonalPolynomials` instances, zeros in the support, Gauss quadrature, completeness),
[SoninePolyaApplications.lean](SoninePolyaApplications.lean),
[JacobiDiscriminant.lean](JacobiDiscriminant.lean), [Legendre.lean](Legendre.lean),
[GegenbauerSeries.lean](GegenbauerSeries.lean), [ChebyshevExpansion.lean](ChebyshevExpansion.lean),
[LaguerreSeries.lean](LaguerreSeries.lean) and [BinomialSeries.lean](BinomialSeries.lean); none
of them contains an admission.

## Section review

The counts below concern numbered equations and tables appearing on each source page. “Tagged” means a matching tag exists in local code or a Mathlib comment, not that the entire display is formalized. Untagged entries remain explicitly listed in the inventory.

| Section | Tagged / numbered displays | Coverage and remaining work |
| --- | ---: | --- |
| [18.1](https://dlmf.nist.gov/18.1) | 1 / 3 | Notation and rescaled Chebyshev polynomials. The two older normalization conventions are not new polynomial families. |
| [18.2](https://dlmf.nist.gov/18.2) | 24 / 60 | General measures, kernels, moments, recurrence coefficients, zeros, and L² expansions. Separate matrix formulations, quadratic changes of measure, continued-fraction convergence, and Sheffer classification are not transcribed. |
| [18.3](https://dlmf.nist.gov/18.3) | 2 / 3 | Classical orthogonality and norms, including finite Chebyshev orthogonality. Table tags identify specific rows; they do not assert that every normalization in the table has a separate declaration. |
| [18.5](https://dlmf.nist.gov/18.5) | 24 / 26 | Explicit sums, hypergeometric definitions, Rodrigues formulas, and low-degree values. Fibonacci specialization and inverse-variable Rodrigues formula are not transcribed; some alternate hypergeometric forms are represented only by their finite sums. |
| [18.6](https://dlmf.nist.gov/18.6) | 6 / 6 | Special values, reflection identities, and monomial limits. Selected table entries appear as local statements or Mathlib comments. |
| [18.7](https://dlmf.nist.gov/18.7) | 23 / 26 | Family relations, quadratic transformations, and limits. The inverse Gegenbauer/Jacobi scaling is represented by the forward relation. Shifted T and U are changes of variable, not new definitions here. |
| [18.8](https://dlmf.nist.gov/18.8) | 1 / 1 | The six classical differential equations. Transformed differential equations in the table are not separately transcribed. |
| [18.9](https://dlmf.nist.gov/18.9) | 28 / 33 | Recurrences, contiguous relations, and derivatives. Algebraically rearranged coefficient conventions and the three-term derivative expansion are not separately transcribed. |
| [18.10](https://dlmf.nist.gov/18.10) | 9 / 11 | Dirichlet, Laplace, double-integral, and Bessel representations. The general contour formula and its contour table need a separate branch/contour specification. |
| [18.11](https://dlmf.nist.gov/18.11) | 5 / 8 | Laguerre/confluent representation and Mehler–Heine limits. Ferrers, Tricomi, Whittaker, and parabolic-cylinder representations await the corresponding function definitions. |
| [18.12](https://dlmf.nist.gov/18.12) | 19 / 19 | Every numbered equation has a tagged local statement or existing statement. Some multi-equality displays have only one form formalized. Nonterminating hypergeometric arguments are restricted to the convergence disk. |
| [18.13](https://dlmf.nist.gov/18.13) | 5 / 5 | All five denominator continued fractions, using Mathlib GenContFract. These are finite convergent-denominator identities. |
| [18.14](https://dlmf.nist.gov/18.14) | 17 / 28 | Global bounds, Turán inequalities, and positive sums. Bounds for ordered local extrema and their auxiliary parameter inequalities are not separately transcribed. |
| [18.15](https://dlmf.nist.gov/18.15) | 1 / 29 | Leading Jacobi Darboux asymptotic. Full uniform expansions, higher coefficients, remainders, and turning-point formulas require further asymptotic infrastructure. |
| [18.16](https://dlmf.nist.gov/18.16) | 6 / 21 | Existence of classical zeros, Laguerre bounds, and discriminants. Indexed Bessel/Airy-zero comparisons and asymptotics await canonical indexed zero definitions. |
| [18.17](https://dlmf.nist.gov/18.17) | 37 / 56 | Norms, weighted integrals, fractional integrals, transforms, convolutions, and a triple Hermite integral. Remaining transforms are not separately transcribed. Principal-value formulas need an actual principal-value definition; second-kind/parabolic-cylinder formulas need those functions. |
| [18.18](https://dlmf.nist.gov/18.18) | 26 / 40 | Generating sums, additions, connections, linearization, and Mehler formula. General pointwise expansion theorems need their convergence hypotheses formalized. Several auxiliary normalizations and bilateral kernels are not separately transcribed. |
| [18.19](https://dlmf.nist.gov/18.19) | 5 / 11 | Hahn-class weights and orthogonality in standard positive ranges. Complete norm tables and all alternate admissible parameter ranges are not separately transcribed. |
| [18.20](https://dlmf.nist.gov/18.20) | 6 / 11 | The six Hahn-class families are defined by terminating sums. The first four numbered equations are notation for those families, not additional identities. |
| [18.21](https://dlmf.nist.gov/18.21) | 10 / 13 | Ten family limits. Continuous-Hahn limits to Jacobi, Meixner–Pollaczek, and Hermite remain untranscribed. |
| [18.22](https://dlmf.nist.gov/18.22) | 12 / 32 | Difference equations and first differences. Full recurrence coefficient tables, weighted raising operators, and Rodrigues formulas at finite lattice boundaries remain untranscribed. |
| [18.23](https://dlmf.nist.gov/18.23) | 5 / 7 | Five generating functions. The two finite Hahn/Krawtchouk generating-polynomial formulas are not separately transcribed. |
| [18.24](https://dlmf.nist.gov/18.24) | 0 / 0 | Literature survey; no numbered equations or explicit expansion supplied by the source. |
| [18.25](https://dlmf.nist.gov/18.25) | 2 / 17 | Wilson and continuous-dual-Hahn weights and orthogonality. Finite Racah/dual-Hahn norm and weight regimes require a separate normalization audit before transcription. |
| [18.26](https://dlmf.nist.gov/18.26) | 13 / 23 | Wilson-class finite definitions, dualities, limits, differences, and generating functions. Some parameter-degeneration and central-difference identities remain untranscribed. |
| [18.27](https://dlmf.nist.gov/18.27) | 18 / 41 | Principal q-Hahn families, selected orthogonality and q→1 limits. Further weight regimes, norms, generating functions, and alternative transformations remain untranscribed. |
| [18.28](https://dlmf.nist.gov/18.28) | 14 / 40 | Askey–Wilson, q-Racah, Al-Salam–Chihara, continuous q-Hermite, and existing q-ultraspherical definitions; selected identities and limits. Continuous q-Jacobi and reciprocal-q regimes need additional definitions; other normalizations and degenerations remain untranscribed. |
| [18.29](https://dlmf.nist.gov/18.29) | 2 / 2 | Combined leading Askey–Wilson asymptotic and its coefficient. The source gives other asymptotics only by literature reference. |
| [18.30](https://dlmf.nist.gov/18.30) | 7 / 31 | General associated recurrence and Laguerre, Hermite, and Meixner–Pollaczek specializations. Associated Jacobi and explicit weights involving Tricomi/parabolic-cylinder functions or continued Gauss values remain deferred. |
| [18.31](https://dlmf.nist.gov/18.31) | 0 / 0 | Bernstein–Szegő weights are described in prose and the explicit construction is delegated by DLMF to a book reference; no new theorem transcribed. |
| [18.32](https://dlmf.nist.gov/18.32) | 1 / 2 | Freud weights, including the α=0 case. Remaining content is a literature survey. |
| [18.33](https://dlmf.nist.gov/18.33) | 13 / 32 | Unit-circle orthogonality, reversed polynomials, Szegő recurrences, norm ratios, Verblunsky existence/uniqueness, and Szegő–Askey families. Full line/circle transformations and the logarithmic Szegő theorem need further measure-decomposition and normalization work. |
| [18.34](https://dlmf.nist.gov/18.34) | 9 / 12 | Bessel polynomials, reverse form, ODE, orthogonality, and Morse functions. The inverse-variable ODE and special-function representations are not separately transcribed. |
| [18.35](https://dlmf.nist.gov/18.35) | 10 / 23 | Pollaczek recurrence, continuous weight/orthogonality, and associated Meixner–Pollaczek formulas. Discrete-mass regimes and weights involving boundary values of Gauss functions remain deferred. |
| [18.36](https://dlmf.nist.gov/18.36) | 7 / 10 | Exceptional Laguerre and Hermite definitions, identities, and orthogonality. The remaining Darboux seed and differential-operator constructions are not separately transcribed. |
| [18.37](https://dlmf.nist.gov/18.37) | 6 / 8 | Disk and triangle polynomials and orthogonality. Specializations are covered by definitions where noted; general root-system, matrix-valued, Sobolev, and multiple orthogonal polynomials are literature topics without the needed structures here. |

## Equation and table inventory

Every numbered equation and table extracted from the visited source pages is listed here. A dash means **no exact tag match**, not a claim that the formula is false or irrelevant. Consult the section review before starting the remaining transcription. Section-level prose tags follow the numbered entries. Declaration names link to their module; the line number is supplied for navigation.

### §18.1

| DLMF | Local declaration or Mathlib record |
| --- | --- |
| [18.1.E1](https://dlmf.nist.gov/18.1.E1) | — Not separately tagged; see section review. |
| [18.1.E2](https://dlmf.nist.gov/18.1.E2) | — Not separately tagged; see section review. |
| [18.1.E3](https://dlmf.nist.gov/18.1.E3) | [Polynomial.Chebyshev.C_eq_two_mul_T_comp_half_mul_X](../OrthogonalPolynomials/MathlibCoverage.lean) (line 25; Mathlib comment); [Polynomial.Chebyshev.S_eq_U_comp_half_mul_X](../OrthogonalPolynomials/MathlibCoverage.lean) (line 32; Mathlib comment) |

### §18.2

| DLMF | Local declaration or Mathlib record |
| --- | --- |
| [18.2.E1](https://dlmf.nist.gov/18.2.E1) | — Not separately tagged; see section review. |
| [18.2.E1_5](https://dlmf.nist.gov/18.2.E1_5) | — Not separately tagged; see section review. |
| [18.2.E2](https://dlmf.nist.gov/18.2.E2) | — Not separately tagged; see section review. |
| [18.2.E3](https://dlmf.nist.gov/18.2.E3) | — Not separately tagged; see section review. |
| [18.2.E4](https://dlmf.nist.gov/18.2.E4) | — Not separately tagged; see section review. |
| [18.2.E4_5](https://dlmf.nist.gov/18.2.E4_5) | [IsOrthogonalPolynomials](../OrthogonalPolynomials/General.lean) (line 44; local) |
| [18.2.E5](https://dlmf.nist.gov/18.2.E5) | [squaredNorm](../OrthogonalPolynomials/GeneralIdentities.lean) (line 33; local) |
| [18.2.E5_5](https://dlmf.nist.gov/18.2.E5_5) | [integral_product](../OrthogonalPolynomials/GeneralIdentities.lean) (line 54; local) |
| [18.2.E6](https://dlmf.nist.gov/18.2.E6) | [firstWeightedSquaredNorm](../OrthogonalPolynomials/GeneralIdentities.lean) (line 416; local) |
| [18.2.E7](https://dlmf.nist.gov/18.2.E7) | — Not separately tagged; see section review. |
| [18.2.E8](https://dlmf.nist.gov/18.2.E8) | — Not separately tagged; see section review. |
| [18.2.E9](https://dlmf.nist.gov/18.2.E9) | — Not separately tagged; see section review. |
| [18.2.E9_5](https://dlmf.nist.gov/18.2.E9_5) | — Not separately tagged; see section review. |
| [18.2.E10](https://dlmf.nist.gov/18.2.E10) | [three_term_recurrence](../OrthogonalPolynomials/General.lean) (line 229; local) |
| [18.2.E11](https://dlmf.nist.gov/18.2.E11) | [recurrenceDiagonal](../OrthogonalPolynomials/GeneralIdentities.lean) (line 49; local); [recurrenceDiagonal_eq_integral](../OrthogonalPolynomials/GeneralIdentities.lean) (line 62; local) |
| [18.2.E11_1](https://dlmf.nist.gov/18.2.E11_1) | [sum_recurrenceDiagonal](../OrthogonalPolynomials/GeneralIdentities.lean) (line 74; local) |
| [18.2.E11_2](https://dlmf.nist.gov/18.2.E11_2) | — Not separately tagged; see section review. |
| [18.2.E11_3](https://dlmf.nist.gov/18.2.E11_3) | — Not separately tagged; see section review. |
| [18.2.E11_4](https://dlmf.nist.gov/18.2.E11_4) | [monic_squaredNorm_ratio](../OrthogonalPolynomials/GeneralIdentities.lean) (line 228; local) |
| [18.2.E11_5](https://dlmf.nist.gov/18.2.E11_5) | — Not separately tagged; see section review. |
| [18.2.E11_6](https://dlmf.nist.gov/18.2.E11_6) | — Not separately tagged; see section review. |
| [18.2.E11_7](https://dlmf.nist.gov/18.2.E11_7) | — Not separately tagged; see section review. |
| [18.2.E11_8](https://dlmf.nist.gov/18.2.E11_8) | — Not separately tagged; see section review. |
| [18.2.E11_9](https://dlmf.nist.gov/18.2.E11_9) | — Not separately tagged; see section review. |
| [18.2.E12](https://dlmf.nist.gov/18.2.E12) | [christoffel_darboux](../OrthogonalPolynomials/General.lean) (line 640; local); [christoffelDarbouxKernel](../OrthogonalPolynomials/GeneralIdentities.lean) (line 37; local) |
| [18.2.E12_5](https://dlmf.nist.gov/18.2.E12_5) | [kernel_reproduces](../OrthogonalPolynomials/GeneralIdentities.lean) (line 129; local); [kernel_annihilates](../OrthogonalPolynomials/GeneralIdentities.lean) (line 441; local) |
| [18.2.E13](https://dlmf.nist.gov/18.2.E13) | [christoffel_darboux_diagonal](../OrthogonalPolynomials/GeneralIdentities.lean) (line 144; local) |
| [18.2.E14](https://dlmf.nist.gov/18.2.E14) | — Not separately tagged; see section review. |
| [18.2.E15](https://dlmf.nist.gov/18.2.E15) | [kernel_polynomials_orthogonal](../OrthogonalPolynomials/GeneralIdentities.lean) (line 450; local) |
| [18.2.E16](https://dlmf.nist.gov/18.2.E16) | [kernel_difference](../OrthogonalPolynomials/GeneralIdentities.lean) (line 177; local) |
| [18.2.E17](https://dlmf.nist.gov/18.2.E17) | — Not separately tagged; see section review. |
| [18.2.E18](https://dlmf.nist.gov/18.2.E18) | — Not separately tagged; see section review. |
| [18.2.E19](https://dlmf.nist.gov/18.2.E19) | — Not separately tagged; see section review. |
| [18.2.E20](https://dlmf.nist.gov/18.2.E20) | [rootDiscriminant](../OrthogonalPolynomials/BoundsZeros.lean) (line 656; local) |
| [18.2.E21](https://dlmf.nist.gov/18.2.E21) | [symmetric_measure_parity](../OrthogonalPolynomials/GeneralIdentities.lean) (line 364; local) |
| [18.2.E22](https://dlmf.nist.gov/18.2.E22) | — Not separately tagged; see section review. |
| [18.2.E23](https://dlmf.nist.gov/18.2.E23) | — Not separately tagged; see section review. |
| [18.2.E24](https://dlmf.nist.gov/18.2.E24) | — Not separately tagged; see section review. |
| [18.2.E25](https://dlmf.nist.gov/18.2.E25) | [compact_support_L2_expansion](../OrthogonalPolynomials/GeneralIdentities.lean) (line 548; local) |
| [18.2.E26](https://dlmf.nist.gov/18.2.E26) | [moment](../OrthogonalPolynomials/GeneralIdentities.lean) (line 41; local) |
| [18.2.E27](https://dlmf.nist.gov/18.2.E27) | [hankelDeterminant](../OrthogonalPolynomials/GeneralIdentities.lean) (line 44; local); [hankelDeterminant_pos](../OrthogonalPolynomials/GeneralIdentities.lean) (line 184; local) |
| [18.2.E28](https://dlmf.nist.gov/18.2.E28) | [shiftedHankelDeterminant](../OrthogonalPolynomials/GeneralIdentities.lean) (line 420; local) |
| [18.2.E29](https://dlmf.nist.gov/18.2.E29) | [monic_moment_determinant](../OrthogonalPolynomials/GeneralIdentities.lean) (line 527; local) |
| [18.2.E30](https://dlmf.nist.gov/18.2.E30) | [monic_diagonal_moment_determinant](../OrthogonalPolynomials/GeneralIdentities.lean) (line 534; local); [monic_offdiagonal_moment_determinant](../OrthogonalPolynomials/GeneralIdentities.lean) (line 541; local) |
| [18.2.E31](https://dlmf.nist.gov/18.2.E31) | — Not separately tagged; see section review. |
| [18.2.E32](https://dlmf.nist.gov/18.2.E32) | — Not separately tagged; see section review. |
| [18.2.E33](https://dlmf.nist.gov/18.2.E33) | — Not separately tagged; see section review. |
| [18.2.E34](https://dlmf.nist.gov/18.2.E34) | — Not separately tagged; see section review. |
| [18.2.E35](https://dlmf.nist.gov/18.2.E35) | — Not separately tagged; see section review. |
| [18.2.E36](https://dlmf.nist.gov/18.2.E36) | — Not separately tagged; see section review. |
| [18.2.E37](https://dlmf.nist.gov/18.2.E37) | — Not separately tagged; see section review. |
| [18.2.E38](https://dlmf.nist.gov/18.2.E38) | — Not separately tagged; see section review. |
| [18.2.E39](https://dlmf.nist.gov/18.2.E39) | [IsSzegoWeight](../OrthogonalPolynomials/GeneralIdentities.lean) (line 431; local) |
| [18.2.E40](https://dlmf.nist.gov/18.2.E40) | [IsNevaiClass](../OrthogonalPolynomials/GeneralIdentities.lean) (line 437; local) |
| [18.2.E41](https://dlmf.nist.gov/18.2.E41) | [poissonKernel](../OrthogonalPolynomials/GeneralIdentities.lean) (line 425; local) |
| [18.2.E42](https://dlmf.nist.gov/18.2.E42) | — Not separately tagged; see section review. |
| [18.2.E43](https://dlmf.nist.gov/18.2.E43) | — Not separately tagged; see section review. |
| [18.2.E44](https://dlmf.nist.gov/18.2.E44) | — Not separately tagged; see section review. |
| [18.2.E45](https://dlmf.nist.gov/18.2.E45) | — Not separately tagged; see section review. |
| [18.2.E46](https://dlmf.nist.gov/18.2.E46) | — Not separately tagged; see section review. |
| [18.2.iv](https://dlmf.nist.gov/18.2.iv) | [favard](../OrthogonalPolynomials/General.lean) (line 266; local) |
| [18.2.x](https://dlmf.nist.gov/18.2.x) | [gauss_quadrature](../OrthogonalPolynomials/General.lean) (line 280; local) |
| [18.2.vi](https://dlmf.nist.gov/18.2.vi) | [orthogonal_polynomials_roots](../OrthogonalPolynomials/General.lean) (line 498; local); [zeros_interlace](../OrthogonalPolynomials/GeneralIdentities.lean) (line 240; local) |
| [18.2.viii](https://dlmf.nist.gov/18.2.viii) | [orthogonal_polynomials_parseval](../OrthogonalPolynomials/General.lean) (line 716; local) |

### §18.3

| DLMF | Local declaration or Mathlib record |
| --- | --- |
| [18.3.E1](https://dlmf.nist.gov/18.3.E1) | [chebyshevT_discrete_orthogonality](../OrthogonalPolynomials/Explicit.lean) (line 420; local) |
| [18.3.E2](https://dlmf.nist.gov/18.3.E2) | — Not separately tagged; see section review. |
| [18.3.T1](https://dlmf.nist.gov/18.3.T1) | [laguerrePolynomialL_orthogonal](../OrthogonalPolynomials/Classical.lean) (line 299; local); [jacobiPolynomialP_orthogonal](../OrthogonalPolynomials/Classical.lean) (line 647; local); [integral_eval_U_mul_of_ne](../OrthogonalPolynomials/General.lean) (line 821; local); [integral_eval_U_mul_self](../OrthogonalPolynomials/General.lean) (line 871; local); [jacobi_norm](../OrthogonalPolynomials/Integrals.lean) (line 394; local); [laguerrePolynomialL_norm](../OrthogonalPolynomials/Integrals.lean) (line 427; local); [hermitePolynomialH_orthogonality](../OrthogonalPolynomials/Integrals.lean) (line 464; local); [hermite_orthogonality](../OrthogonalPolynomials/Integrals.lean) (line 495; local); [legendre_orthogonality](../OrthogonalPolynomials/Integrals.lean) (line 502; local); [ultrasphericalPolynomial_orthogonality](../OrthogonalPolynomials/Integrals.lean) (line 670; local); [Polynomial.Chebyshev.leadingCoeff_T](../OrthogonalPolynomials/MathlibCoverage.lean) (line 39; Mathlib comment); [Polynomial.Chebyshev.leadingCoeff_U_natCast](../OrthogonalPolynomials/MathlibCoverage.lean) (line 46; Mathlib comment); [Polynomial.Chebyshev.integral_eval_T_real_mul_eval_T_real_measureT_of_ne](../OrthogonalPolynomials/MathlibCoverage.lean) (line 242; Mathlib comment); [Polynomial.Chebyshev.integral_eval_T_real_mul_self_measureT_zero](../OrthogonalPolynomials/MathlibCoverage.lean) (line 249; Mathlib comment); [Polynomial.Chebyshev.integral_T_real_mul_self_measureT_of_ne_zero](../OrthogonalPolynomials/MathlibCoverage.lean) (line 256; Mathlib comment); [Polynomial.degree_hermite](../OrthogonalPolynomials/MathlibCoverage.lean) (line 263; Mathlib comment); [Polynomial.hermite_monic](../OrthogonalPolynomials/MathlibCoverage.lean) (line 269; Mathlib comment); [Polynomial.leadingCoeff_hermite](../OrthogonalPolynomials/MathlibCoverage.lean) (line 275; Mathlib comment) |

### §18.5

| DLMF | Local declaration or Mathlib record |
| --- | --- |
| [18.5.E1](https://dlmf.nist.gov/18.5.E1) | [Polynomial.Chebyshev.T_real_cos](../OrthogonalPolynomials/MathlibCoverage.lean) (line 174; Mathlib comment); [Polynomial.Chebyshev.T_complex_cos](../OrthogonalPolynomials/MathlibCoverage.lean) (line 180; Mathlib comment) |
| [18.5.E2](https://dlmf.nist.gov/18.5.E2) | [Polynomial.Chebyshev.U_real_cos](../OrthogonalPolynomials/MathlibCoverage.lean) (line 186; Mathlib comment); [Polynomial.Chebyshev.U_complex_cos](../OrthogonalPolynomials/MathlibCoverage.lean) (line 192; Mathlib comment) |
| [18.5.E3](https://dlmf.nist.gov/18.5.E3) | [chebyshevV_cos](../OrthogonalPolynomials/Differential.lean) (line 975; local) |
| [18.5.E4](https://dlmf.nist.gov/18.5.E4) | [chebyshevW_cos](../OrthogonalPolynomials/Differential.lean) (line 1086; local) |
| [18.5.E4_5](https://dlmf.nist.gov/18.5.E4_5) | — Not separately tagged; see section review. |
| [18.5.E5](https://dlmf.nist.gov/18.5.E5) | [jacobi_rodrigues](../OrthogonalPolynomials/Integrals.lean) (line 758; local); [laguerrePolynomialL_rodrigues](../OrthogonalPolynomials/Integrals.lean) (line 784; local) |
| [18.5.E6](https://dlmf.nist.gov/18.5.E6) | — Not separately tagged; see section review. |
| [18.5.E7](https://dlmf.nist.gov/18.5.E7) | [jacobiPolynomialP](../OrthogonalPolynomials/Classical.lean) (line 482; local); [jacobi_finite_sum](../OrthogonalPolynomials/Explicit.lean) (line 65; local); [Polynomial.coeff_shiftedLegendre](../OrthogonalPolynomials/MathlibCoverage.lean) (line 322; Mathlib comment) |
| [18.5.E8](https://dlmf.nist.gov/18.5.E8) | [jacobi_binomial_sum](../OrthogonalPolynomials/Explicit.lean) (line 154; local) |
| [18.5.E9](https://dlmf.nist.gov/18.5.E9) | [ultrasphericalPolynomial](../OrthogonalPolynomials/Classical.lean) (line 699; local) |
| [18.5.E10](https://dlmf.nist.gov/18.5.E10) | [ultrasphericalPolynomial_finite_sum](../OrthogonalPolynomials/GegenbauerSeries.lean) (line 362; local) |
| [18.5.E11](https://dlmf.nist.gov/18.5.E11) | [ultrasphericalPolynomial_cos_sum](../OrthogonalPolynomials/GegenbauerSeries.lean) (line 111; local) |
| [18.5.E11_1](https://dlmf.nist.gov/18.5.E11_1) | [chebyshevT_finite_sum](../OrthogonalPolynomials/Explicit.lean) (line 508; local) |
| [18.5.E11_2](https://dlmf.nist.gov/18.5.E11_2) | [chebyshevT_hypergeometric](../OrthogonalPolynomials/Differential.lean) (line 890; local) |
| [18.5.E11_3](https://dlmf.nist.gov/18.5.E11_3) | [chebyshevU_finite_sum](../OrthogonalPolynomials/Explicit.lean) (line 488; local) |
| [18.5.E11_4](https://dlmf.nist.gov/18.5.E11_4) | [ultrasphericalPolynomial_param_one_eq](../OrthogonalPolynomials/Classical.lean) (line 708; local) |
| [18.5.E12](https://dlmf.nist.gov/18.5.E12) | [laguerrePolynomialL](../OrthogonalPolynomials/Classical.lean) (line 206; local); [laguerrePolynomialL_eq_sum](../OrthogonalPolynomials/Classical.lean) (line 335; local); [laguerreExtended](../OrthogonalPolynomials/Explicit.lean) (line 41; local); [laguerreExtended_eq](../OrthogonalPolynomials/Explicit.lean) (line 46; local) |
| [18.5.E13](https://dlmf.nist.gov/18.5.E13) | [hermitePolynomialH_finite_sum](../OrthogonalPolynomials/Explicit.lean) (line 235; local) |
| [18.5.E14](https://dlmf.nist.gov/18.5.E14) | [Polynomial.Chebyshev.T_zero](../OrthogonalPolynomials/MathlibCoverage.lean) (line 53; Mathlib comment); [Polynomial.Chebyshev.T_one](../OrthogonalPolynomials/MathlibCoverage.lean) (line 59; Mathlib comment); [Polynomial.Chebyshev.T_two](../OrthogonalPolynomials/MathlibCoverage.lean) (line 65; Mathlib comment) |
| [18.5.E15](https://dlmf.nist.gov/18.5.E15) | [Polynomial.Chebyshev.U_zero](../OrthogonalPolynomials/MathlibCoverage.lean) (line 71; Mathlib comment); [Polynomial.Chebyshev.U_one](../OrthogonalPolynomials/MathlibCoverage.lean) (line 77; Mathlib comment); [Polynomial.Chebyshev.U_two](../OrthogonalPolynomials/MathlibCoverage.lean) (line 83; Mathlib comment) |
| [18.5.E16](https://dlmf.nist.gov/18.5.E16) | [legendrePolynomialP_zero](../OrthogonalPolynomials/Classical.lean) (line 495; local); [legendrePolynomialP_one](../OrthogonalPolynomials/Topics.lean) (line 214; local) |
| [18.5.E17](https://dlmf.nist.gov/18.5.E17) | [laguerrePolynomialL_zero](../OrthogonalPolynomials/Classical.lean) (line 210; local) |
| [18.5.E17_5](https://dlmf.nist.gov/18.5.E17_5) | [laguerrePolynomialL_zero](../OrthogonalPolynomials/Classical.lean) (line 210; local) |
| [18.5.E18](https://dlmf.nist.gov/18.5.E18) | [hermitePolynomialH_zero](../OrthogonalPolynomials/Classical.lean) (line 48; local); [hermitePolynomialH_one](../OrthogonalPolynomials/Classical.lean) (line 56; local); [hermitePolynomialH_two](../OrthogonalPolynomials/Classical.lean) (line 60; local) |
| [18.5.E19](https://dlmf.nist.gov/18.5.E19) | [Polynomial.hermite_zero](../OrthogonalPolynomials/MathlibCoverage.lean) (line 281; Mathlib comment); [Polynomial.hermite_one](../OrthogonalPolynomials/MathlibCoverage.lean) (line 287; Mathlib comment); [Polynomial.coeff_hermite](../OrthogonalPolynomials/MathlibCoverage.lean) (line 293; Mathlib comment) |
| [18.5.T1](https://dlmf.nist.gov/18.5.T1) | [deriv_gaussian_eq_hermitePolynomialH](../OrthogonalPolynomials/Classical.lean) (line 118; local); [Polynomial.deriv_gaussian_eq_hermite_mul_gaussian](../OrthogonalPolynomials/MathlibCoverage.lean) (line 307; Mathlib comment); [Polynomial.hermite_eq_deriv_gaussian](../OrthogonalPolynomials/MathlibCoverage.lean) (line 315; Mathlib comment) |

### §18.6

| DLMF | Local declaration or Mathlib record |
| --- | --- |
| [18.6.E1](https://dlmf.nist.gov/18.6.E1) | [laguerrePolynomialL_at_zero](../OrthogonalPolynomials/Explicit.lean) (line 246; local) |
| [18.6.E2](https://dlmf.nist.gov/18.6.E2) | [jacobi_limit_alpha](../OrthogonalPolynomials/Limits.lean) (line 74; local) |
| [18.6.E3](https://dlmf.nist.gov/18.6.E3) | [jacobi_limit_beta](../OrthogonalPolynomials/Limits.lean) (line 109; local) |
| [18.6.E4](https://dlmf.nist.gov/18.6.E4) | [ultrasphericalPolynomial_limit_monomial](../OrthogonalPolynomials/Limits.lean) (line 131; local) |
| [18.6.E5](https://dlmf.nist.gov/18.6.E5) | [laguerrePolynomialL_limit_monomial](../OrthogonalPolynomials/Limits.lean) (line 169; local) |
| [18.6.T1](https://dlmf.nist.gov/18.6.T1) | [jacobi_reflection](../OrthogonalPolynomials/Differential.lean) (line 707; local); [jacobi_at_one](../OrthogonalPolynomials/Explicit.lean) (line 251; local); [jacobi_symmetric_even_at_zero](../OrthogonalPolynomials/Differential.lean) (line 772; local); [ultrasphericalPolynomial_reflection](../OrthogonalPolynomials/Differential.lean) (line 729; local); [ultrasphericalPolynomial_at_one](../OrthogonalPolynomials/Explicit.lean) (line 266; local); [ultrasphericalPolynomial_even_at_zero](../OrthogonalPolynomials/Differential.lean) (line 754; local); [hermitePolynomialH_reflection](../OrthogonalPolynomials/Explicit.lean) (line 271; local); [hermitePolynomialH_even_at_zero](../OrthogonalPolynomials/Explicit.lean) (line 289; local); [chebyshevV_reflection](../OrthogonalPolynomials/Differential.lean) (line 1171; local); [chebyshevW_reflection](../OrthogonalPolynomials/Differential.lean) (line 1219; local); [chebyshevV_at_one](../OrthogonalPolynomials/Explicit.lean) (line 314; local); [chebyshevW_at_one](../OrthogonalPolynomials/Explicit.lean) (line 318; local); [Polynomial.Chebyshev.T_eval_one](../OrthogonalPolynomials/MathlibCoverage.lean) (line 89; Mathlib comment); [Polynomial.Chebyshev.T_eval_neg_one](../OrthogonalPolynomials/MathlibCoverage.lean) (line 95; Mathlib comment); [Polynomial.Chebyshev.T_eval_neg](../OrthogonalPolynomials/MathlibCoverage.lean) (line 101; Mathlib comment); [Polynomial.Chebyshev.U_eval_one](../OrthogonalPolynomials/MathlibCoverage.lean) (line 107; Mathlib comment); [Polynomial.Chebyshev.U_eval_neg_one](../OrthogonalPolynomials/MathlibCoverage.lean) (line 113; Mathlib comment); [Polynomial.Chebyshev.U_eval_neg](../OrthogonalPolynomials/MathlibCoverage.lean) (line 119; Mathlib comment); [Polynomial.Chebyshev.abs_eval_T_real_eq_one_iff](../OrthogonalPolynomials/MathlibCoverage.lean) (line 228; Mathlib comment); [Polynomial.coeff_hermite_of_odd_add](../OrthogonalPolynomials/MathlibCoverage.lean) (line 301; Mathlib comment); [Polynomial.shiftedLegendre_eval_symm](../OrthogonalPolynomials/MathlibCoverage.lean) (line 329; Mathlib comment) |

### §18.7

| DLMF | Local declaration or Mathlib record |
| --- | --- |
| [18.7.E1](https://dlmf.nist.gov/18.7.E1) | [ultrasphericalPolynomial_eq_jacobiPolynomialP](../OrthogonalPolynomials/Classical.lean) (line 910; local) |
| [18.7.E2](https://dlmf.nist.gov/18.7.E2) | — Not separately tagged; see section review. |
| [18.7.E3](https://dlmf.nist.gov/18.7.E3) | [chebyshevT_eq_jacobi](../OrthogonalPolynomials/Differential.lean) (line 907; local) |
| [18.7.E4](https://dlmf.nist.gov/18.7.E4) | [eval_U_eq_ultrasphericalPolynomial](../OrthogonalPolynomials/Classical.lean) (line 879; local) |
| [18.7.E5](https://dlmf.nist.gov/18.7.E5) | [chebyshevV](../OrthogonalPolynomials/Explicit.lean) (line 56; local) |
| [18.7.E6](https://dlmf.nist.gov/18.7.E6) | [chebyshevW](../OrthogonalPolynomials/Explicit.lean) (line 61; local) |
| [18.7.E7](https://dlmf.nist.gov/18.7.E7) | — Not separately tagged; see section review. |
| [18.7.E8](https://dlmf.nist.gov/18.7.E8) | — Not separately tagged; see section review. |
| [18.7.E9](https://dlmf.nist.gov/18.7.E9) | [legendrePolynomialP](../OrthogonalPolynomials/Classical.lean) (line 491; local); [legendre_eq_ultrasphericalPolynomial](../OrthogonalPolynomials/Explicit.lean) (line 323; local); [legendrePolynomialP_eq_normalized_ultrasphericalPolynomial](../OrthogonalPolynomials/Topics.lean) (line 207; local) |
| [18.7.E10](https://dlmf.nist.gov/18.7.E10) | [aeval_shiftedLegendre_eq_legendrePolynomialP](../OrthogonalPolynomials/Classical.lean) (line 518; local) |
| [18.7.E11](https://dlmf.nist.gov/18.7.E11) | [aeval_hermitePolynomialH_eq_hermite](../OrthogonalPolynomials/Classical.lean) (line 92; local) |
| [18.7.E12](https://dlmf.nist.gov/18.7.E12) | [aeval_hermitePolynomialH_eq_hermite](../OrthogonalPolynomials/Classical.lean) (line 92; local) |
| [18.7.E13](https://dlmf.nist.gov/18.7.E13) | [jacobi_quadratic_even](../OrthogonalPolynomials/GegenbauerSeries.lean) (line 494; local) |
| [18.7.E14](https://dlmf.nist.gov/18.7.E14) | [jacobi_quadratic_odd](../OrthogonalPolynomials/GegenbauerSeries.lean) (line 539; local) |
| [18.7.E15](https://dlmf.nist.gov/18.7.E15) | [ultrasphericalPolynomial_quadratic_even](../OrthogonalPolynomials/GegenbauerSeries.lean) (line 383; local) |
| [18.7.E16](https://dlmf.nist.gov/18.7.E16) | [ultrasphericalPolynomial_quadratic_odd](../OrthogonalPolynomials/GegenbauerSeries.lean) (line 418; local) |
| [18.7.E17](https://dlmf.nist.gov/18.7.E17) | [chebyshevU_quadratic](../OrthogonalPolynomials/Differential.lean) (line 1140; local) |
| [18.7.E18](https://dlmf.nist.gov/18.7.E18) | [chebyshevT_quadratic](../OrthogonalPolynomials/Differential.lean) (line 1108; local) |
| [18.7.E19](https://dlmf.nist.gov/18.7.E19) | [hermitePolynomialH_even_eq_laguerrePolynomialL](../OrthogonalPolynomials/Explicit.lean) (line 350; local) |
| [18.7.E20](https://dlmf.nist.gov/18.7.E20) | [hermitePolynomialH_odd_eq_laguerrePolynomialL](../OrthogonalPolynomials/Explicit.lean) (line 367; local) |
| [18.7.E21](https://dlmf.nist.gov/18.7.E21) | [jacobi_limit_laguerrePolynomialL](../OrthogonalPolynomials/Limits.lean) (line 196; local) |
| [18.7.E22](https://dlmf.nist.gov/18.7.E22) | [jacobi_limit_laguerrePolynomialL_reflected](../OrthogonalPolynomials/Limits.lean) (line 222; local) |
| [18.7.E23](https://dlmf.nist.gov/18.7.E23) | [jacobi_limit_hermite](../OrthogonalPolynomials/Limits.lean) (line 231; local) |
| [18.7.E24](https://dlmf.nist.gov/18.7.E24) | [ultrasphericalPolynomial_limit_hermite](../OrthogonalPolynomials/Limits.lean) (line 293; local) |
| [18.7.E25](https://dlmf.nist.gov/18.7.E25) | [ultrasphericalPolynomial_limit_chebyshev](../OrthogonalPolynomials/Limits.lean) (line 344; local) |
| [18.7.E26](https://dlmf.nist.gov/18.7.E26) | [laguerrePolynomialL_limit_hermite](../OrthogonalPolynomials/Limits.lean) (line 434; local) |

### §18.8

| DLMF | Local declaration or Mathlib record |
| --- | --- |
| [18.8.T1](https://dlmf.nist.gov/18.8.T1) | [jacobi_differential_equation](../OrthogonalPolynomials/Differential.lean) (line 92; local); [ultrasphericalPolynomial_differential_equation](../OrthogonalPolynomials/Differential.lean) (line 107; local); [legendre_differential_equation](../OrthogonalPolynomials/Differential.lean) (line 122; local); [laguerrePolynomialL_differential_equation](../OrthogonalPolynomials/Differential.lean) (line 131; local); [hermitePolynomialH_differential_equation](../OrthogonalPolynomials/Differential.lean) (line 147; local); [hermite_differential_equation](../OrthogonalPolynomials/Differential.lean) (line 158; local); [Polynomial.Chebyshev.one_sub_X_sq_mul_derivative_derivative_T_eq_poly_in_T](../OrthogonalPolynomials/MathlibCoverage.lean) (line 153; Mathlib comment); [Polynomial.Chebyshev.one_sub_X_sq_mul_derivative_derivative_U_eq_poly_in_U](../OrthogonalPolynomials/MathlibCoverage.lean) (line 160; Mathlib comment) |

### §18.9

| DLMF | Local declaration or Mathlib record |
| --- | --- |
| [18.9.E1](https://dlmf.nist.gov/18.9.E1) | — Not separately tagged; see section review. |
| [18.9.E2](https://dlmf.nist.gov/18.9.E2) | [jacobi_recurrence](../OrthogonalPolynomials/Differential.lean) (line 242; local) |
| [18.9.E2_1](https://dlmf.nist.gov/18.9.E2_1) | — Not separately tagged; see section review. |
| [18.9.E2_2](https://dlmf.nist.gov/18.9.E2_2) | — Not separately tagged; see section review. |
| [18.9.E3](https://dlmf.nist.gov/18.9.E3) | [jacobi_contiguous_sub](../OrthogonalPolynomials/Differential.lean) (line 387; local) |
| [18.9.E4](https://dlmf.nist.gov/18.9.E4) | [jacobi_contiguous_add](../OrthogonalPolynomials/Differential.lean) (line 410; local) |
| [18.9.E5](https://dlmf.nist.gov/18.9.E5) | [jacobi_raise_beta](../OrthogonalPolynomials/Differential.lean) (line 440; local) |
| [18.9.E6](https://dlmf.nist.gov/18.9.E6) | [jacobi_raise_degree_beta](../OrthogonalPolynomials/Differential.lean) (line 470; local) |
| [18.9.E7](https://dlmf.nist.gov/18.9.E7) | [ultrasphericalPolynomial_raise_parameter](../OrthogonalPolynomials/Differential.lean) (line 511; local) |
| [18.9.E8](https://dlmf.nist.gov/18.9.E8) | [ultrasphericalPolynomial_raise_parameter_sq](../OrthogonalPolynomials/Differential.lean) (line 582; local) |
| [18.9.E9](https://dlmf.nist.gov/18.9.E9) | [Polynomial.Chebyshev.U_eq_two_mul_T_add_U](../OrthogonalPolynomials/MathlibCoverage.lean) (line 141; Mathlib comment) |
| [18.9.E10](https://dlmf.nist.gov/18.9.E10) | [Polynomial.Chebyshev.one_sub_X_sq_mul_U_eq_pol_in_T](../OrthogonalPolynomials/MathlibCoverage.lean) (line 344; Mathlib comment) |
| [18.9.E11](https://dlmf.nist.gov/18.9.E11) | [chebyshevV_contiguous](../OrthogonalPolynomials/Differential.lean) (line 917; local) |
| [18.9.E12](https://dlmf.nist.gov/18.9.E12) | [chebyshevV_mul_one_add](../OrthogonalPolynomials/Differential.lean) (line 946; local) |
| [18.9.E13](https://dlmf.nist.gov/18.9.E13) | [laguerrePolynomialL_raise_parameter](../OrthogonalPolynomials/Differential.lean) (line 1229; local) |
| [18.9.E14](https://dlmf.nist.gov/18.9.E14) | [laguerrePolynomialL_mul_argument](../OrthogonalPolynomials/Differential.lean) (line 1249; local) |
| [18.9.E15](https://dlmf.nist.gov/18.9.E15) | [jacobi_derivative](../OrthogonalPolynomials/Differential.lean) (line 1286; local) |
| [18.9.E16](https://dlmf.nist.gov/18.9.E16) | [jacobi_weighted_derivative](../OrthogonalPolynomials/Differential.lean) (line 1669; local) |
| [18.9.E17](https://dlmf.nist.gov/18.9.E17) | [jacobi_lowering_derivative](../OrthogonalPolynomials/Differential.lean) (line 1318; local) |
| [18.9.E18](https://dlmf.nist.gov/18.9.E18) | [jacobi_raising_derivative](../OrthogonalPolynomials/Differential.lean) (line 1373; local) |
| [18.9.E18_5](https://dlmf.nist.gov/18.9.E18_5) | — Not separately tagged; see section review. |
| [18.9.E19](https://dlmf.nist.gov/18.9.E19) | [ultrasphericalPolynomial_derivative](../OrthogonalPolynomials/Differential.lean) (line 1427; local) |
| [18.9.E20](https://dlmf.nist.gov/18.9.E20) | [ultrasphericalPolynomial_weighted_derivative](../OrthogonalPolynomials/Differential.lean) (line 1706; local) |
| [18.9.E21](https://dlmf.nist.gov/18.9.E21) | [Polynomial.Chebyshev.T_derivative_eq_U](../OrthogonalPolynomials/MathlibCoverage.lean) (line 147; Mathlib comment) |
| [18.9.E22](https://dlmf.nist.gov/18.9.E22) | [chebyshevU_weighted_derivative](../OrthogonalPolynomials/Differential.lean) (line 1744; local) |
| [18.9.E23](https://dlmf.nist.gov/18.9.E23) | [laguerrePolynomialL_derivative](../OrthogonalPolynomials/Differential.lean) (line 1478; local) |
| [18.9.E24](https://dlmf.nist.gov/18.9.E24) | [laguerrePolynomialL_weighted_derivative](../OrthogonalPolynomials/Differential.lean) (line 1810; local) |
| [18.9.E25](https://dlmf.nist.gov/18.9.E25) | [hermitePolynomialH_derivative](../OrthogonalPolynomials/Classical.lean) (line 65; local) |
| [18.9.E26](https://dlmf.nist.gov/18.9.E26) | [hermitePolynomialH_weighted_derivative](../OrthogonalPolynomials/Differential.lean) (line 1495; local) |
| [18.9.E27](https://dlmf.nist.gov/18.9.E27) | [hermite_derivative](../OrthogonalPolynomials/Differential.lean) (line 35; local) |
| [18.9.E28](https://dlmf.nist.gov/18.9.E28) | [hermite_weighted_derivative](../OrthogonalPolynomials/Differential.lean) (line 1505; local) |
| [18.9.T1](https://dlmf.nist.gov/18.9.T1) | [ultrasphericalPolynomial_recurrence](../OrthogonalPolynomials/Differential.lean) (line 303; local); [laguerrePolynomialL_recurrence](../OrthogonalPolynomials/Differential.lean) (line 356; local); [hermitePolynomialH_recurrence](../OrthogonalPolynomials/Differential.lean) (line 377; local); [hermite_recurrence](../OrthogonalPolynomials/Differential.lean) (line 382; local); [ultrasphericalPolynomial_normalized_recurrence](../OrthogonalPolynomials/Topics.lean) (line 105; local); [legendrePolynomialP_recurrence](../OrthogonalPolynomials/Topics.lean) (line 220; local); [Polynomial.Chebyshev.T_add_two](../OrthogonalPolynomials/MathlibCoverage.lean) (line 125; Mathlib comment); [Polynomial.Chebyshev.U_add_two](../OrthogonalPolynomials/MathlibCoverage.lean) (line 133; Mathlib comment) |
| [18.9.T2](https://dlmf.nist.gov/18.9.T2) | — Not separately tagged; see section review. |

### §18.10

| DLMF | Local declaration or Mathlib record |
| --- | --- |
| [18.10.E1](https://dlmf.nist.gov/18.10.E1) | [ultrasphericalPolynomial_dirichlet_integral](../OrthogonalPolynomials/Integrals.lean) (line 3580; local) |
| [18.10.E2](https://dlmf.nist.gov/18.10.E2) | [legendre_dirichlet_mehler](../OrthogonalPolynomials/Integrals.lean) (line 877; local) |
| [18.10.E3](https://dlmf.nist.gov/18.10.E3) | [jacobi_double_laplace_integral](../OrthogonalPolynomials/Integrals.lean) (line 3590; local) |
| [18.10.E4](https://dlmf.nist.gov/18.10.E4) | [ultrasphericalPolynomial_laplace_integral](../OrthogonalPolynomials/Integrals.lean) (line 998; local) |
| [18.10.E5](https://dlmf.nist.gov/18.10.E5) | [legendre_laplace_integral](../OrthogonalPolynomials/Integrals.lean) (line 1133; local) |
| [18.10.E6](https://dlmf.nist.gov/18.10.E6) | [laguerrePolynomialL_double_laplace_integral](../OrthogonalPolynomials/Integrals.lean) (line 3602; local) |
| [18.10.E7](https://dlmf.nist.gov/18.10.E7) | [hermitePolynomialH_laplace_integral](../OrthogonalPolynomials/Integrals.lean) (line 1329; local) |
| [18.10.E8](https://dlmf.nist.gov/18.10.E8) | — Not separately tagged; see section review. |
| [18.10.E9](https://dlmf.nist.gov/18.10.E9) | [laguerrePolynomialL_bessel_integral](../OrthogonalPolynomials/Integrals.lean) (line 3611; local) |
| [18.10.E10](https://dlmf.nist.gov/18.10.E10) | [hermitePolynomialH_fourier_integral](../OrthogonalPolynomials/Integrals.lean) (line 1477; local) |
| [18.10.T1](https://dlmf.nist.gov/18.10.T1) | — Not separately tagged; see section review. |

### §18.11

| DLMF | Local declaration or Mathlib record |
| --- | --- |
| [18.11.E1](https://dlmf.nist.gov/18.11.E1) | — Not separately tagged; see section review. |
| [18.11.E2](https://dlmf.nist.gov/18.11.E2) | [laguerrePolynomialL_eq_sum_coeff](../OrthogonalPolynomials/Classical.lean) (line 215; local) |
| [18.11.E3](https://dlmf.nist.gov/18.11.E3) | — Not separately tagged; see section review. |
| [18.11.E4](https://dlmf.nist.gov/18.11.E4) | — Not separately tagged; see section review. |
| [18.11.E5](https://dlmf.nist.gov/18.11.E5) | [jacobi_mehler_heine](../OrthogonalPolynomials/Limits.lean) (line 512; local) |
| [18.11.E6](https://dlmf.nist.gov/18.11.E6) | [laguerrePolynomialL_mehler_heine](../OrthogonalPolynomials/Limits.lean) (line 519; local) |
| [18.11.E7](https://dlmf.nist.gov/18.11.E7) | [hermite_even_mehler_heine](../OrthogonalPolynomials/Limits.lean) (line 525; local) |
| [18.11.E8](https://dlmf.nist.gov/18.11.E8) | [hermite_odd_mehler_heine](../OrthogonalPolynomials/Limits.lean) (line 532; local) |

### §18.12

| DLMF | Local declaration or Mathlib record |
| --- | --- |
| [18.12.E1](https://dlmf.nist.gov/18.12.E1) | [jacobi_generating_function](../OrthogonalPolynomials/Series.lean) (line 139; local) |
| [18.12.E2](https://dlmf.nist.gov/18.12.E2) | [jacobi_regularized_generating_function](../OrthogonalPolynomials/Series.lean) (line 1057; local) |
| [18.12.E2_5](https://dlmf.nist.gov/18.12.E2_5) | [jacobi_brafman_generating_function](../OrthogonalPolynomials/Series.lean) (line 1109; local) |
| [18.12.E3](https://dlmf.nist.gov/18.12.E3) | [jacobi_weighted_generating_function](../OrthogonalPolynomials/Series.lean) (line 1120; local) |
| [18.12.E3_5](https://dlmf.nist.gov/18.12.E3_5) | [jacobi_adjacent_generating_function](../OrthogonalPolynomials/Series.lean) (line 1129; local) |
| [18.12.E4](https://dlmf.nist.gov/18.12.E4) | [ultrasphericalPolynomial_generating_function](../OrthogonalPolynomials/Series.lean) (line 148; local) |
| [18.12.E5](https://dlmf.nist.gov/18.12.E5) | [ultrasphericalPolynomial_weighted_generating_function](../OrthogonalPolynomials/Series.lean) (line 158; local) |
| [18.12.E6](https://dlmf.nist.gov/18.12.E6) | [ultrasphericalPolynomial_bessel_generating_function](../OrthogonalPolynomials/Legendre.lean) (line 807; local) |
| [18.12.E7](https://dlmf.nist.gov/18.12.E7) | [chebyshevT_poisson_generating_function](../OrthogonalPolynomials/Series.lean) (line 1136; local) |
| [18.12.E8](https://dlmf.nist.gov/18.12.E8) | [chebyshevT_generating_function](../OrthogonalPolynomials/Series.lean) (line 244; local) |
| [18.12.E9](https://dlmf.nist.gov/18.12.E9) | [chebyshevT_log_generating_function](../OrthogonalPolynomials/Series.lean) (line 271; local) |
| [18.12.E10](https://dlmf.nist.gov/18.12.E10) | [chebyshevU_generating_function](../OrthogonalPolynomials/Series.lean) (line 311; local) |
| [18.12.E11](https://dlmf.nist.gov/18.12.E11) | [legendre_generating_function](../OrthogonalPolynomials/Series.lean) (line 332; local) |
| [18.12.E12](https://dlmf.nist.gov/18.12.E12) | [legendre_exponential_generating_function](../OrthogonalPolynomials/Legendre.lean) (line 716; local) |
| [18.12.E13](https://dlmf.nist.gov/18.12.E13) | [laguerrePolynomialL_generating_function](../OrthogonalPolynomials/Classical.lean) (line 420; local) |
| [18.12.E14](https://dlmf.nist.gov/18.12.E14) | [laguerrePolynomialL_bessel_generating_function](../OrthogonalPolynomials/Series.lean) (line 1160; local) |
| [18.12.E15](https://dlmf.nist.gov/18.12.E15) | [hermitePolynomialH_generating_function](../OrthogonalPolynomials/Classical.lean) (line 197; local) |
| [18.12.E16](https://dlmf.nist.gov/18.12.E16) | [hermite_generating_function](../OrthogonalPolynomials/Series.lean) (line 339; local) |
| [18.12.E17](https://dlmf.nist.gov/18.12.E17) | [hermitePolynomialH_half_factorial_generating_function](../OrthogonalPolynomials/Series.lean) (line 1245; local) |

### §18.13

| DLMF | Local declaration or Mathlib record |
| --- | --- |
| [18.13.E1](https://dlmf.nist.gov/18.13.E1) | [chebyshevT_continued_fraction](../OrthogonalPolynomials/ContinuedFractions.lean) (line 53; local) |
| [18.13.E2](https://dlmf.nist.gov/18.13.E2) | [chebyshevU_continued_fraction](../OrthogonalPolynomials/ContinuedFractions.lean) (line 68; local) |
| [18.13.E3](https://dlmf.nist.gov/18.13.E3) | [legendre_continued_fraction](../OrthogonalPolynomials/ContinuedFractions.lean) (line 81; local) |
| [18.13.E4](https://dlmf.nist.gov/18.13.E4) | [laguerrePolynomialL_continued_fraction](../OrthogonalPolynomials/ContinuedFractions.lean) (line 98; local) |
| [18.13.E5](https://dlmf.nist.gov/18.13.E5) | [hermitePolynomialH_continued_fraction](../OrthogonalPolynomials/ContinuedFractions.lean) (line 123; local) |

### §18.14

| DLMF | Local declaration or Mathlib record |
| --- | --- |
| [18.14.E1](https://dlmf.nist.gov/18.14.E1) | [jacobi_bound_at_one](../OrthogonalPolynomials/BoundsZeros.lean) (line 67; local) |
| [18.14.E2](https://dlmf.nist.gov/18.14.E2) | [jacobi_bound_at_neg_one](../OrthogonalPolynomials/BoundsZeros.lean) (line 117; local) |
| [18.14.E3](https://dlmf.nist.gov/18.14.E3) | [jacobi_bernstein_bound](../OrthogonalPolynomials/BoundsZeros.lean) (line 125; local) |
| [18.14.E3_5](https://dlmf.nist.gov/18.14.E3_5) | [jacobi_weighted_bound](../OrthogonalPolynomials/BoundsZeros.lean) (line 452; local) |
| [18.14.E4](https://dlmf.nist.gov/18.14.E4) | [ultrasphericalPolynomial_bound_at_one](../OrthogonalPolynomials/BoundsZeros.lean) (line 143; local) |
| [18.14.E5](https://dlmf.nist.gov/18.14.E5) | [ultrasphericalPolynomial_even_bound](../OrthogonalPolynomials/BoundsZeros.lean) (line 209; local) |
| [18.14.E6](https://dlmf.nist.gov/18.14.E6) | [ultrasphericalPolynomial_odd_bound](../OrthogonalPolynomials/BoundsZeros.lean) (line 249; local) |
| [18.14.E7](https://dlmf.nist.gov/18.14.E7) | [ultrasphericalPolynomial_bernstein_bound](../OrthogonalPolynomials/BoundsZeros.lean) (line 338; local) |
| [18.14.E8](https://dlmf.nist.gov/18.14.E8) | [laguerrePolynomialL_bound](../OrthogonalPolynomials/BoundsZeros.lean) (line 345; local) |
| [18.14.E9](https://dlmf.nist.gov/18.14.E9) | [hermitePolynomialH_bound](../OrthogonalPolynomials/BoundsZeros.lean) (line 350; local) |
| [18.14.E10](https://dlmf.nist.gov/18.14.E10) | [turan_legendre](../OrthogonalPolynomials/Topics.lean) (line 230; local) |
| [18.14.E11](https://dlmf.nist.gov/18.14.E11) | [jacobi_turan](../OrthogonalPolynomials/BoundsZeros.lean) (line 355; local); [turan_ultrasphericalPolynomial](../OrthogonalPolynomials/Topics.lean) (line 159; local) |
| [18.14.E12](https://dlmf.nist.gov/18.14.E12) | [laguerrePolynomialL_turan](../OrthogonalPolynomials/BoundsZeros.lean) (line 362; local) |
| [18.14.E13](https://dlmf.nist.gov/18.14.E13) | [hermitePolynomialH_turan](../OrthogonalPolynomials/BoundsZeros.lean) (line 368; local) |
| [18.14.E14](https://dlmf.nist.gov/18.14.E14) | — Not separately tagged; see section review. |
| [18.14.E15](https://dlmf.nist.gov/18.14.E15) | — Not separately tagged; see section review. |
| [18.14.E16](https://dlmf.nist.gov/18.14.E16) | — Not separately tagged; see section review. |
| [18.14.E17](https://dlmf.nist.gov/18.14.E17) | — Not separately tagged; see section review. |
| [18.14.E18](https://dlmf.nist.gov/18.14.E18) | — Not separately tagged; see section review. |
| [18.14.E19](https://dlmf.nist.gov/18.14.E19) | — Not separately tagged; see section review. |
| [18.14.E20](https://dlmf.nist.gov/18.14.E20) | — Not separately tagged; see section review. |
| [18.14.E21](https://dlmf.nist.gov/18.14.E21) | — Not separately tagged; see section review. |
| [18.14.E22](https://dlmf.nist.gov/18.14.E22) | — Not separately tagged; see section review. |
| [18.14.E23](https://dlmf.nist.gov/18.14.E23) | — Not separately tagged; see section review. |
| [18.14.E24](https://dlmf.nist.gov/18.14.E24) | — Not separately tagged; see section review. |
| [18.14.E25](https://dlmf.nist.gov/18.14.E25) | [jacobi_positive_weighted_sum](../OrthogonalPolynomials/BoundsZeros.lean) (line 404; local) |
| [18.14.E26](https://dlmf.nist.gov/18.14.E26) | [jacobi_positive_sum](../OrthogonalPolynomials/BoundsZeros.lean) (line 411; local) |
| [18.14.E27](https://dlmf.nist.gov/18.14.E27) | [laguerrePolynomialL_positive_weighted_sum](../OrthogonalPolynomials/BoundsZeros.lean) (line 417; local) |
| [18.14.i](https://dlmf.nist.gov/18.14.i) | [Polynomial.Chebyshev.abs_eval_T_real_le_one](../OrthogonalPolynomials/MathlibCoverage.lean) (line 235; Mathlib comment) |

### §18.15

| DLMF | Local declaration or Mathlib record |
| --- | --- |
| [18.15.E1](https://dlmf.nist.gov/18.15.E1) | — Not separately tagged; see section review. |
| [18.15.E2](https://dlmf.nist.gov/18.15.E2) | — Not separately tagged; see section review. |
| [18.15.E3](https://dlmf.nist.gov/18.15.E3) | — Not separately tagged; see section review. |
| [18.15.E4](https://dlmf.nist.gov/18.15.E4) | — Not separately tagged; see section review. |
| [18.15.E4_5](https://dlmf.nist.gov/18.15.E4_5) | [jacobi_darboux_asymptotic](../OrthogonalPolynomials/BoundsZeros.lean) (line 443; local) |
| [18.15.E5](https://dlmf.nist.gov/18.15.E5) | — Not separately tagged; see section review. |
| [18.15.E6](https://dlmf.nist.gov/18.15.E6) | — Not separately tagged; see section review. |
| [18.15.E7](https://dlmf.nist.gov/18.15.E7) | — Not separately tagged; see section review. |
| [18.15.E8](https://dlmf.nist.gov/18.15.E8) | — Not separately tagged; see section review. |
| [18.15.E9](https://dlmf.nist.gov/18.15.E9) | — Not separately tagged; see section review. |
| [18.15.E10](https://dlmf.nist.gov/18.15.E10) | — Not separately tagged; see section review. |
| [18.15.E11](https://dlmf.nist.gov/18.15.E11) | — Not separately tagged; see section review. |
| [18.15.E12](https://dlmf.nist.gov/18.15.E12) | — Not separately tagged; see section review. |
| [18.15.E13](https://dlmf.nist.gov/18.15.E13) | — Not separately tagged; see section review. |
| [18.15.E14](https://dlmf.nist.gov/18.15.E14) | — Not separately tagged; see section review. |
| [18.15.E15](https://dlmf.nist.gov/18.15.E15) | — Not separately tagged; see section review. |
| [18.15.E16](https://dlmf.nist.gov/18.15.E16) | — Not separately tagged; see section review. |
| [18.15.E17](https://dlmf.nist.gov/18.15.E17) | — Not separately tagged; see section review. |
| [18.15.E18](https://dlmf.nist.gov/18.15.E18) | — Not separately tagged; see section review. |
| [18.15.E19](https://dlmf.nist.gov/18.15.E19) | — Not separately tagged; see section review. |
| [18.15.E20](https://dlmf.nist.gov/18.15.E20) | — Not separately tagged; see section review. |
| [18.15.E21](https://dlmf.nist.gov/18.15.E21) | — Not separately tagged; see section review. |
| [18.15.E22](https://dlmf.nist.gov/18.15.E22) | — Not separately tagged; see section review. |
| [18.15.E23](https://dlmf.nist.gov/18.15.E23) | — Not separately tagged; see section review. |
| [18.15.E24](https://dlmf.nist.gov/18.15.E24) | — Not separately tagged; see section review. |
| [18.15.E25](https://dlmf.nist.gov/18.15.E25) | — Not separately tagged; see section review. |
| [18.15.E26](https://dlmf.nist.gov/18.15.E26) | — Not separately tagged; see section review. |
| [18.15.E27](https://dlmf.nist.gov/18.15.E27) | — Not separately tagged; see section review. |
| [18.15.E28](https://dlmf.nist.gov/18.15.E28) | — Not separately tagged; see section review. |

### §18.16

| DLMF | Local declaration or Mathlib record |
| --- | --- |
| [18.16.E1](https://dlmf.nist.gov/18.16.E1) | — Not separately tagged; see section review. |
| [18.16.E2](https://dlmf.nist.gov/18.16.E2) | — Not separately tagged; see section review. |
| [18.16.E3](https://dlmf.nist.gov/18.16.E3) | — Not separately tagged; see section review. |
| [18.16.E4](https://dlmf.nist.gov/18.16.E4) | — Not separately tagged; see section review. |
| [18.16.E5](https://dlmf.nist.gov/18.16.E5) | — Not separately tagged; see section review. |
| [18.16.E6](https://dlmf.nist.gov/18.16.E6) | — Not separately tagged; see section review. |
| [18.16.E7](https://dlmf.nist.gov/18.16.E7) | — Not separately tagged; see section review. |
| [18.16.E8](https://dlmf.nist.gov/18.16.E8) | — Not separately tagged; see section review. |
| [18.16.E9](https://dlmf.nist.gov/18.16.E9) | — Not separately tagged; see section review. |
| [18.16.E10](https://dlmf.nist.gov/18.16.E10) | — Not separately tagged; see section review. |
| [18.16.E11](https://dlmf.nist.gov/18.16.E11) | — Not separately tagged; see section review. |
| [18.16.E12](https://dlmf.nist.gov/18.16.E12) | [laguerrePolynomialL_zero_lower_bound](../OrthogonalPolynomials/BoundsZeros.lean) (line 640; local) |
| [18.16.E13](https://dlmf.nist.gov/18.16.E13) | [laguerrePolynomialL_zero_upper_bound](../OrthogonalPolynomials/BoundsZeros.lean) (line 647; local) |
| [18.16.E14](https://dlmf.nist.gov/18.16.E14) | — Not separately tagged; see section review. |
| [18.16.E15](https://dlmf.nist.gov/18.16.E15) | — Not separately tagged; see section review. |
| [18.16.E16](https://dlmf.nist.gov/18.16.E16) | [hermitePolynomialH_zeros](../OrthogonalPolynomials/BoundsZeros.lean) (line 437; local) |
| [18.16.E17](https://dlmf.nist.gov/18.16.E17) | — Not separately tagged; see section review. |
| [18.16.E18](https://dlmf.nist.gov/18.16.E18) | — Not separately tagged; see section review. |
| [18.16.E19](https://dlmf.nist.gov/18.16.E19) | [jacobi_discriminant](../OrthogonalPolynomials/BoundsZeros.lean) (line 705; local) |
| [18.16.E20](https://dlmf.nist.gov/18.16.E20) | [laguerrePolynomialL_discriminant](../OrthogonalPolynomials/BoundsZeros.lean) (line 1064; local) |
| [18.16.E21](https://dlmf.nist.gov/18.16.E21) | [hermitePolynomialH_discriminant](../OrthogonalPolynomials/BoundsZeros.lean) (line 1312; local) |
| [18.16.i](https://dlmf.nist.gov/18.16.i) | [jacobi_zeros](../OrthogonalPolynomials/BoundsZeros.lean) (line 425; local) |
| [18.16.iv](https://dlmf.nist.gov/18.16.iv) | [laguerrePolynomialL_zeros](../OrthogonalPolynomials/BoundsZeros.lean) (line 431; local) |
| [18.16.iii](https://dlmf.nist.gov/18.16.iii) | [Polynomial.Chebyshev.roots_T_real](../OrthogonalPolynomials/MathlibCoverage.lean) (line 198; Mathlib comment); [Polynomial.Chebyshev.roots_U_real](../OrthogonalPolynomials/MathlibCoverage.lean) (line 206; Mathlib comment); [Polynomial.Chebyshev.rootMultiplicity_T_real](../OrthogonalPolynomials/MathlibCoverage.lean) (line 214; Mathlib comment); [Polynomial.Chebyshev.rootMultiplicity_U_real](../OrthogonalPolynomials/MathlibCoverage.lean) (line 221; Mathlib comment) |

### §18.17

| DLMF | Local declaration or Mathlib record |
| --- | --- |
| [18.17.E1](https://dlmf.nist.gov/18.17.E1) | [jacobi_weighted_integral](../OrthogonalPolynomials/Integrals.lean) (line 2548; local) |
| [18.17.E2](https://dlmf.nist.gov/18.17.E2) | [laguerrePolynomialL_unweighted_convolution](../OrthogonalPolynomials/Integrals.lean) (line 2594; local) |
| [18.17.E3](https://dlmf.nist.gov/18.17.E3) | [hermitePolynomialH_integral](../OrthogonalPolynomials/Integrals.lean) (line 1517; local) |
| [18.17.E4](https://dlmf.nist.gov/18.17.E4) | [hermitePolynomialH_weighted_integral](../OrthogonalPolynomials/Integrals.lean) (line 1534; local) |
| [18.17.E5](https://dlmf.nist.gov/18.17.E5) | [ultrasphericalPolynomial_product_integral](../OrthogonalPolynomials/Integrals.lean) (line 2686; local) |
| [18.17.E6](https://dlmf.nist.gov/18.17.E6) | [legendre_product_integral](../OrthogonalPolynomials/Integrals.lean) (line 1555; local) |
| [18.17.E7](https://dlmf.nist.gov/18.17.E7) | — Not separately tagged; see section review. |
| [18.17.E8](https://dlmf.nist.gov/18.17.E8) | — Not separately tagged; see section review. |
| [18.17.E9](https://dlmf.nist.gov/18.17.E9) | [jacobi_fractional_integral](../OrthogonalPolynomials/Integrals.lean) (line 2696; local) |
| [18.17.E10](https://dlmf.nist.gov/18.17.E10) | — Not separately tagged; see section review. |
| [18.17.E11](https://dlmf.nist.gov/18.17.E11) | — Not separately tagged; see section review. |
| [18.17.E12](https://dlmf.nist.gov/18.17.E12) | — Not separately tagged; see section review. |
| [18.17.E13](https://dlmf.nist.gov/18.17.E13) | — Not separately tagged; see section review. |
| [18.17.E14](https://dlmf.nist.gov/18.17.E14) | [laguerrePolynomialL_fractional_integral](../OrthogonalPolynomials/Integrals.lean) (line 1576; local) |
| [18.17.E15](https://dlmf.nist.gov/18.17.E15) | [laguerrePolynomialL_fractional_tail_integral](../OrthogonalPolynomials/Integrals.lean) (line 1647; local) |
| [18.17.E16](https://dlmf.nist.gov/18.17.E16) | [jacobi_fourier_transform](../OrthogonalPolynomials/Integrals.lean) (line 3618; local) |
| [18.17.E16_5](https://dlmf.nist.gov/18.17.E16_5) | [ultrasphericalPolynomial_fourier_transform](../OrthogonalPolynomials/Integrals.lean) (line 2973; local) |
| [18.17.E17](https://dlmf.nist.gov/18.17.E17) | [ultrasphericalPolynomial_even_cosine_transform](../OrthogonalPolynomials/Integrals.lean) (line 3704; local) |
| [18.17.E18](https://dlmf.nist.gov/18.17.E18) | [ultrasphericalPolynomial_odd_sine_transform](../OrthogonalPolynomials/Integrals.lean) (line 3725; local) |
| [18.17.E19](https://dlmf.nist.gov/18.17.E19) | [legendre_fourier_transform](../OrthogonalPolynomials/Integrals.lean) (line 3748; local) |
| [18.17.E20](https://dlmf.nist.gov/18.17.E20) | — Not separately tagged; see section review. |
| [18.17.E21](https://dlmf.nist.gov/18.17.E21) | [legendre_bessel_square_integral](../OrthogonalPolynomials/Integrals.lean) (line 3082; local) |
| [18.17.E21_1](https://dlmf.nist.gov/18.17.E21_1) | — Not separately tagged; see section review. |
| [18.17.E21_2](https://dlmf.nist.gov/18.17.E21_2) | [hermitePolynomialH_fourier_transform](../OrthogonalPolynomials/Integrals.lean) (line 1709; local) |
| [18.17.E21_3](https://dlmf.nist.gov/18.17.E21_3) | [hermitePolynomialH_fourier_eigenfunction](../OrthogonalPolynomials/Integrals.lean) (line 1806; local) |
| [18.17.E22](https://dlmf.nist.gov/18.17.E22) | [hermite_fourier_eigenfunction](../OrthogonalPolynomials/Integrals.lean) (line 3088; local) |
| [18.17.E23](https://dlmf.nist.gov/18.17.E23) | [hermite_even_cosine_transform](../OrthogonalPolynomials/Integrals.lean) (line 3246; local) |
| [18.17.E24](https://dlmf.nist.gov/18.17.E24) | — Not separately tagged; see section review. |
| [18.17.E25](https://dlmf.nist.gov/18.17.E25) | [hermite_product_cosine_transform](../OrthogonalPolynomials/Integrals.lean) (line 3388; local) |
| [18.17.E26](https://dlmf.nist.gov/18.17.E26) | [hermite_product_sine_transform](../OrthogonalPolynomials/Integrals.lean) (line 3466; local) |
| [18.17.E27](https://dlmf.nist.gov/18.17.E27) | [hermite_odd_sine_transform](../OrthogonalPolynomials/Integrals.lean) (line 3273; local) |
| [18.17.E28](https://dlmf.nist.gov/18.17.E28) | — Not separately tagged; see section review. |
| [18.17.E28_5](https://dlmf.nist.gov/18.17.E28_5) | [laguerrePolynomialL_fourier_transform](../OrthogonalPolynomials/Integrals.lean) (line 1926; local) |
| [18.17.E29](https://dlmf.nist.gov/18.17.E29) | — Not separately tagged; see section review. |
| [18.17.E30](https://dlmf.nist.gov/18.17.E30) | — Not separately tagged; see section review. |
| [18.17.E31](https://dlmf.nist.gov/18.17.E31) | — Not separately tagged; see section review. |
| [18.17.E32](https://dlmf.nist.gov/18.17.E32) | — Not separately tagged; see section review. |
| [18.17.E33](https://dlmf.nist.gov/18.17.E33) | [jacobi_laplace_transform](../OrthogonalPolynomials/Integrals.lean) (line 3544; local) |
| [18.17.E34](https://dlmf.nist.gov/18.17.E34) | [laguerrePolynomialL_laplace_transform](../OrthogonalPolynomials/Integrals.lean) (line 3776; local) |
| [18.17.E34_5](https://dlmf.nist.gov/18.17.E34_5) | [laguerrePolynomialL_product_laplace_transform](../OrthogonalPolynomials/Integrals.lean) (line 3554; local) |
| [18.17.E35](https://dlmf.nist.gov/18.17.E35) | [hermitePolynomialH_laplace_transform](../OrthogonalPolynomials/Integrals.lean) (line 1937; local) |
| [18.17.E36](https://dlmf.nist.gov/18.17.E36) | [jacobi_mellin_transform](../OrthogonalPolynomials/Integrals.lean) (line 1980; local) |
| [18.17.E37](https://dlmf.nist.gov/18.17.E37) | [ultrasphericalPolynomial_mellin_transform](../OrthogonalPolynomials/Integrals.lean) (line 4019; local) |
| [18.17.E38](https://dlmf.nist.gov/18.17.E38) | [legendre_even_mellin_transform](../OrthogonalPolynomials/Integrals.lean) (line 2121; local) |
| [18.17.E39](https://dlmf.nist.gov/18.17.E39) | [legendre_odd_mellin_transform](../OrthogonalPolynomials/Integrals.lean) (line 2170; local) |
| [18.17.E40](https://dlmf.nist.gov/18.17.E40) | [laguerrePolynomialL_mellin_laplace_transform](../OrthogonalPolynomials/Integrals.lean) (line 4032; local) |
| [18.17.E41](https://dlmf.nist.gov/18.17.E41) | [hermite_mellin_laplace_transform](../OrthogonalPolynomials/Integrals.lean) (line 3569; local) |
| [18.17.E41_5](https://dlmf.nist.gov/18.17.E41_5) | — Not separately tagged; see section review. |
| [18.17.E42](https://dlmf.nist.gov/18.17.E42) | — Not separately tagged; see section review. |
| [18.17.E43](https://dlmf.nist.gov/18.17.E43) | — Not separately tagged; see section review. |
| [18.17.E44](https://dlmf.nist.gov/18.17.E44) | [legendre_singular_integral](../OrthogonalPolynomials/Integrals.lean) (line 2227; local) |
| [18.17.E45](https://dlmf.nist.gov/18.17.E45) | — Not separately tagged; see section review. |
| [18.17.E46](https://dlmf.nist.gov/18.17.E46) | — Not separately tagged; see section review. |
| [18.17.E47](https://dlmf.nist.gov/18.17.E47) | [laguerrePolynomialL_convolution](../OrthogonalPolynomials/Integrals.lean) (line 2293; local) |
| [18.17.E48](https://dlmf.nist.gov/18.17.E48) | [hermitePolynomialH_convolution](../OrthogonalPolynomials/Integrals.lean) (line 2380; local) |
| [18.17.E49](https://dlmf.nist.gov/18.17.E49) | [hermitePolynomialH_triple_integral](../OrthogonalPolynomials/Integrals.lean) (line 2495; local) |

### §18.18

| DLMF | Local declaration or Mathlib record |
| --- | --- |
| [18.18.E1](https://dlmf.nist.gov/18.18.E1) | — Not separately tagged; see section review. |
| [18.18.E2](https://dlmf.nist.gov/18.18.E2) | — Not separately tagged; see section review. |
| [18.18.E3](https://dlmf.nist.gov/18.18.E3) | — Not separately tagged; see section review. |
| [18.18.E4](https://dlmf.nist.gov/18.18.E4) | — Not separately tagged; see section review. |
| [18.18.E5](https://dlmf.nist.gov/18.18.E5) | — Not separately tagged; see section review. |
| [18.18.E6](https://dlmf.nist.gov/18.18.E6) | — Not separately tagged; see section review. |
| [18.18.E7](https://dlmf.nist.gov/18.18.E7) | — Not separately tagged; see section review. |
| [18.18.E8](https://dlmf.nist.gov/18.18.E8) | — Not separately tagged; see section review. |
| [18.18.E9](https://dlmf.nist.gov/18.18.E9) | [legendre_addition](../OrthogonalPolynomials/Series.lean) (line 816; local) |
| [18.18.E10](https://dlmf.nist.gov/18.18.E10) | [laguerrePolynomialL_addition](../OrthogonalPolynomials/Series.lean) (line 527; local) |
| [18.18.E11](https://dlmf.nist.gov/18.18.E11) | [hermitePolynomialH_addition](../OrthogonalPolynomials/Series.lean) (line 549; local) |
| [18.18.E12](https://dlmf.nist.gov/18.18.E12) | [laguerrePolynomialL_multiplication](../OrthogonalPolynomials/Series.lean) (line 595; local) |
| [18.18.E13](https://dlmf.nist.gov/18.18.E13) | [hermitePolynomialH_multiplication](../OrthogonalPolynomials/Series.lean) (line 626; local) |
| [18.18.E14](https://dlmf.nist.gov/18.18.E14) | — Not separately tagged; see section review. |
| [18.18.E15](https://dlmf.nist.gov/18.18.E15) | — Not separately tagged; see section review. |
| [18.18.E16](https://dlmf.nist.gov/18.18.E16) | [ultrasphericalPolynomial_connection](../OrthogonalPolynomials/Series.lean) (line 651; local) |
| [18.18.E17](https://dlmf.nist.gov/18.18.E17) | [monomial_ultrasphericalPolynomial_expansion](../OrthogonalPolynomials/Series.lean) (line 659; local) |
| [18.18.E18](https://dlmf.nist.gov/18.18.E18) | [laguerrePolynomialL_connection](../OrthogonalPolynomials/Series.lean) (line 666; local) |
| [18.18.E19](https://dlmf.nist.gov/18.18.E19) | [monomial_laguerrePolynomialL_expansion](../OrthogonalPolynomials/Series.lean) (line 690; local) |
| [18.18.E20](https://dlmf.nist.gov/18.18.E20) | [monomial_hermitePolynomialH_expansion](../OrthogonalPolynomials/Series.lean) (line 730; local) |
| [18.18.E21](https://dlmf.nist.gov/18.18.E21) | [Polynomial.Chebyshev.T_mul_T](../OrthogonalPolynomials/MathlibCoverage.lean) (line 168; Mathlib comment) |
| [18.18.E22](https://dlmf.nist.gov/18.18.E22) | [ultrasphericalPolynomial_linearization](../OrthogonalPolynomials/Series.lean) (line 826; local) |
| [18.18.E23](https://dlmf.nist.gov/18.18.E23) | [hermitePolynomialH_linearization](../OrthogonalPolynomials/Series.lean) (line 758; local) |
| [18.18.E24](https://dlmf.nist.gov/18.18.E24) | — Not separately tagged; see section review. |
| [18.18.E25](https://dlmf.nist.gov/18.18.E25) | — Not separately tagged; see section review. |
| [18.18.E26](https://dlmf.nist.gov/18.18.E26) | — Not separately tagged; see section review. |
| [18.18.E27](https://dlmf.nist.gov/18.18.E27) | — Not separately tagged; see section review. |
| [18.18.E28](https://dlmf.nist.gov/18.18.E28) | [mehler_formula](../OrthogonalPolynomials/Series.lean) (line 808; local) |
| [18.18.E29](https://dlmf.nist.gov/18.18.E29) | [ultrasphericalPolynomial_convolution](../OrthogonalPolynomials/Series.lean) (line 837; local) |
| [18.18.E30](https://dlmf.nist.gov/18.18.E30) | [ultrasphericalPolynomial_geometric_convolution](../OrthogonalPolynomials/Series.lean) (line 850; local) |
| [18.18.E31](https://dlmf.nist.gov/18.18.E31) | [chebyshev_geometric_sum](../OrthogonalPolynomials/Series.lean) (line 873; local) |
| [18.18.E32](https://dlmf.nist.gov/18.18.E32) | [chebyshevT_even_sum](../OrthogonalPolynomials/Series.lean) (line 894; local) |
| [18.18.E33](https://dlmf.nist.gov/18.18.E33) | [chebyshevT_odd_sum](../OrthogonalPolynomials/Series.lean) (line 912; local) |
| [18.18.E34](https://dlmf.nist.gov/18.18.E34) | [chebyshevU_even_sum](../OrthogonalPolynomials/Series.lean) (line 925; local) |
| [18.18.E35](https://dlmf.nist.gov/18.18.E35) | [chebyshevU_odd_sum](../OrthogonalPolynomials/Series.lean) (line 943; local) |
| [18.18.E36](https://dlmf.nist.gov/18.18.E36) | [legendre_convolution](../OrthogonalPolynomials/Series.lean) (line 967; local) |
| [18.18.E37](https://dlmf.nist.gov/18.18.E37) | [laguerrePolynomialL_sum](../OrthogonalPolynomials/Series.lean) (line 975; local) |
| [18.18.E38](https://dlmf.nist.gov/18.18.E38) | [laguerrePolynomialL_addition](../OrthogonalPolynomials/Series.lean) (line 527; local) |
| [18.18.E39](https://dlmf.nist.gov/18.18.E39) | [hermitePolynomialH_addition](../OrthogonalPolynomials/Series.lean) (line 549; local) |
| [18.18.E40](https://dlmf.nist.gov/18.18.E40) | [hermitePolynomialH_even_convolution](../OrthogonalPolynomials/Series.lean) (line 1010; local) |
| [18.18.i](https://dlmf.nist.gov/18.18.i) | [jacobiPolynomialP_complete](../OrthogonalPolynomials/ClassicalInstances.lean) (line 748; local) |
| [18.18.iv](https://dlmf.nist.gov/18.18.iv) | [jacobiPolynomialP_connection](../OrthogonalPolynomials/Topics.lean) (line 31; local) |

### §18.19

| DLMF | Local declaration or Mathlib record |
| --- | --- |
| [18.19.E1](https://dlmf.nist.gov/18.19.E1) | — Not separately tagged; see section review. |
| [18.19.E2](https://dlmf.nist.gov/18.19.E2) | [continuousHahnWeight](../OrthogonalPolynomials/Hahn.lean) (line 141; local) |
| [18.19.E3](https://dlmf.nist.gov/18.19.E3) | — Not separately tagged; see section review. |
| [18.19.E4](https://dlmf.nist.gov/18.19.E4) | [continuousHahn_orthogonal](../OrthogonalPolynomials/Hahn.lean) (line 149; local) |
| [18.19.E5](https://dlmf.nist.gov/18.19.E5) | — Not separately tagged; see section review. |
| [18.19.E6](https://dlmf.nist.gov/18.19.E6) | — Not separately tagged; see section review. |
| [18.19.E7](https://dlmf.nist.gov/18.19.E7) | [meixnerPollaczekWeight](../OrthogonalPolynomials/Hahn.lean) (line 145; local) |
| [18.19.E8](https://dlmf.nist.gov/18.19.E8) | — Not separately tagged; see section review. |
| [18.19.E9](https://dlmf.nist.gov/18.19.E9) | [meixnerPollaczek_orthogonality](../OrthogonalPolynomials/Hahn.lean) (line 155; local) |
| [18.19.T1](https://dlmf.nist.gov/18.19.T1) | [hahn_orthogonal](../OrthogonalPolynomials/Hahn.lean) (line 2153; local); [krawtchouk_orthogonality](../OrthogonalPolynomials/Hahn.lean) (line 2033; local); [meixner_orthogonality](../OrthogonalPolynomials/Hahn.lean) (line 1999; local); [charlier_orthogonality](../OrthogonalPolynomials/Hahn.lean) (line 1993; local); [hahn_weight_sum](../OrthogonalPolynomials/Hahn.lean) (line 2245; local) |
| [18.19.T2](https://dlmf.nist.gov/18.19.T2) | — Not separately tagged; see section review. |

### §18.20

| DLMF | Local declaration or Mathlib record |
| --- | --- |
| [18.20.E1](https://dlmf.nist.gov/18.20.E1) | — Not separately tagged; see section review. |
| [18.20.E2](https://dlmf.nist.gov/18.20.E2) | — Not separately tagged; see section review. |
| [18.20.E3](https://dlmf.nist.gov/18.20.E3) | — Not separately tagged; see section review. |
| [18.20.E4](https://dlmf.nist.gov/18.20.E4) | — Not separately tagged; see section review. |
| [18.20.E5](https://dlmf.nist.gov/18.20.E5) | [hahn](../OrthogonalPolynomials/Hahn.lean) (line 113; local) |
| [18.20.E6](https://dlmf.nist.gov/18.20.E6) | [krawtchouk](../OrthogonalPolynomials/Hahn.lean) (line 117; local) |
| [18.20.E7](https://dlmf.nist.gov/18.20.E7) | [meixner](../OrthogonalPolynomials/Hahn.lean) (line 121; local) |
| [18.20.E8](https://dlmf.nist.gov/18.20.E8) | [charlier](../OrthogonalPolynomials/Hahn.lean) (line 125; local) |
| [18.20.E9](https://dlmf.nist.gov/18.20.E9) | [continuousHahn](../OrthogonalPolynomials/Hahn.lean) (line 131; local) |
| [18.20.E10](https://dlmf.nist.gov/18.20.E10) | [meixnerPollaczek](../OrthogonalPolynomials/Hahn.lean) (line 136; local) |
| [18.20.T1](https://dlmf.nist.gov/18.20.T1) | — Not separately tagged; see section review. |

### §18.21

| DLMF | Local declaration or Mathlib record |
| --- | --- |
| [18.21.E1](https://dlmf.nist.gov/18.21.E1) | — Not separately tagged; see section review. |
| [18.21.E2](https://dlmf.nist.gov/18.21.E2) | [krawtchouk_duality](../OrthogonalPolynomials/Hahn.lean) (line 194; local); [meixner_duality](../OrthogonalPolynomials/Hahn.lean) (line 199; local); [charlier_duality](../OrthogonalPolynomials/Hahn.lean) (line 203; local) |
| [18.21.E3](https://dlmf.nist.gov/18.21.E3) | [hahn_limit_krawtchouk](../OrthogonalPolynomials/Hahn.lean) (line 916; local) |
| [18.21.E4](https://dlmf.nist.gov/18.21.E4) | [hahn_limit_meixner](../OrthogonalPolynomials/Hahn.lean) (line 1122; local) |
| [18.21.E5](https://dlmf.nist.gov/18.21.E5) | [hahn_limit_jacobi](../OrthogonalPolynomials/Hahn.lean) (line 944; local) |
| [18.21.E6](https://dlmf.nist.gov/18.21.E6) | [krawtchouk_limit_charlier](../OrthogonalPolynomials/Hahn.lean) (line 979; local) |
| [18.21.E7](https://dlmf.nist.gov/18.21.E7) | [meixner_limit_charlier](../OrthogonalPolynomials/Hahn.lean) (line 1000; local) |
| [18.21.E8](https://dlmf.nist.gov/18.21.E8) | [meixner_limit_laguerrePolynomialL](../OrthogonalPolynomials/Hahn.lean) (line 1158; local) |
| [18.21.E9](https://dlmf.nist.gov/18.21.E9) | [charlier_limit_hermite](../OrthogonalPolynomials/Hahn.lean) (line 1067; local) |
| [18.21.E10](https://dlmf.nist.gov/18.21.E10) | — Not separately tagged; see section review. |
| [18.21.E11](https://dlmf.nist.gov/18.21.E11) | — Not separately tagged; see section review. |
| [18.21.E12](https://dlmf.nist.gov/18.21.E12) | [meixnerPollaczek_limit_laguerrePolynomialL](../OrthogonalPolynomials/Hahn.lean) (line 1202; local) |
| [18.21.E13](https://dlmf.nist.gov/18.21.E13) | [meixnerPollaczek_limit_hermite](../OrthogonalPolynomials/Hahn.lean) (line 1251; local) |

### §18.22

| DLMF | Local declaration or Mathlib record |
| --- | --- |
| [18.22.E1](https://dlmf.nist.gov/18.22.E1) | — Not separately tagged; see section review. |
| [18.22.E2](https://dlmf.nist.gov/18.22.E2) | [meixner_recurrence](../OrthogonalPolynomials/Hahn.lean) (line 1840; local); [krawtchouk_recurrence](../OrthogonalPolynomials/Hahn.lean) (line 2210; local); [hahn_recurrence](../OrthogonalPolynomials/Hahn.lean) (line 2356; local) |
| [18.22.E3](https://dlmf.nist.gov/18.22.E3) | — Not separately tagged; see section review. |
| [18.22.E4](https://dlmf.nist.gov/18.22.E4) | — Not separately tagged; see section review. |
| [18.22.E5](https://dlmf.nist.gov/18.22.E5) | — Not separately tagged; see section review. |
| [18.22.E6](https://dlmf.nist.gov/18.22.E6) | — Not separately tagged; see section review. |
| [18.22.E7](https://dlmf.nist.gov/18.22.E7) | — Not separately tagged; see section review. |
| [18.22.E8](https://dlmf.nist.gov/18.22.E8) | [meixnerPollaczek_recurrence](../OrthogonalPolynomials/Hahn.lean) (line 578; local) |
| [18.22.E9](https://dlmf.nist.gov/18.22.E9) | — Not separately tagged; see section review. |
| [18.22.E10](https://dlmf.nist.gov/18.22.E10) | [hahn_difference_equation](../OrthogonalPolynomials/Hahn.lean) (line 207; local) |
| [18.22.E11](https://dlmf.nist.gov/18.22.E11) | — Not separately tagged; see section review. |
| [18.22.E12](https://dlmf.nist.gov/18.22.E12) | — Not separately tagged; see section review. |
| [18.22.E13](https://dlmf.nist.gov/18.22.E13) | — Not separately tagged; see section review. |
| [18.22.E14](https://dlmf.nist.gov/18.22.E14) | [continuousHahn_difference_equation](../OrthogonalPolynomials/Hahn.lean) (line 1297; local) |
| [18.22.E15](https://dlmf.nist.gov/18.22.E15) | — Not separately tagged; see section review. |
| [18.22.E16](https://dlmf.nist.gov/18.22.E16) | — Not separately tagged; see section review. |
| [18.22.E17](https://dlmf.nist.gov/18.22.E17) | [meixnerPollaczek_difference_equation](../OrthogonalPolynomials/Hahn.lean) (line 1379; local) |
| [18.22.E18](https://dlmf.nist.gov/18.22.E18) | — Not separately tagged; see section review. |
| [18.22.E19](https://dlmf.nist.gov/18.22.E19) | [hahn_forward_difference](../OrthogonalPolynomials/Hahn.lean) (line 491; local) |
| [18.22.E20](https://dlmf.nist.gov/18.22.E20) | — Not separately tagged; see section review. |
| [18.22.E21](https://dlmf.nist.gov/18.22.E21) | [krawtchouk_forward_difference](../OrthogonalPolynomials/Hahn.lean) (line 513; local) |
| [18.22.E22](https://dlmf.nist.gov/18.22.E22) | — Not separately tagged; see section review. |
| [18.22.E23](https://dlmf.nist.gov/18.22.E23) | [meixner_forward_difference](../OrthogonalPolynomials/Hahn.lean) (line 526; local) |
| [18.22.E24](https://dlmf.nist.gov/18.22.E24) | — Not separately tagged; see section review. |
| [18.22.E25](https://dlmf.nist.gov/18.22.E25) | [charlier_forward_difference](../OrthogonalPolynomials/Hahn.lean) (line 542; local) |
| [18.22.E26](https://dlmf.nist.gov/18.22.E26) | — Not separately tagged; see section review. |
| [18.22.E27](https://dlmf.nist.gov/18.22.E27) | [continuousHahn_central_difference](../OrthogonalPolynomials/Hahn.lean) (line 1447; local) |
| [18.22.E28](https://dlmf.nist.gov/18.22.E28) | — Not separately tagged; see section review. |
| [18.22.E29](https://dlmf.nist.gov/18.22.E29) | [meixnerPollaczek_central_difference](../OrthogonalPolynomials/Hahn.lean) (line 639; local) |
| [18.22.E30](https://dlmf.nist.gov/18.22.E30) | — Not separately tagged; see section review. |
| [18.22.T1](https://dlmf.nist.gov/18.22.T1) | — Not separately tagged; see section review. |
| [18.22.T2](https://dlmf.nist.gov/18.22.T2) | [krawtchouk_difference_equation](../OrthogonalPolynomials/Hahn.lean) (line 362; local); [meixner_difference_equation](../OrthogonalPolynomials/Hahn.lean) (line 377; local); [charlier_difference_equation](../OrthogonalPolynomials/Hahn.lean) (line 552; local) |

### §18.23

| DLMF | Local declaration or Mathlib record |
| --- | --- |
| [18.23.E1](https://dlmf.nist.gov/18.23.E1) | — Not separately tagged; see section review. |
| [18.23.E2](https://dlmf.nist.gov/18.23.E2) | — Not separately tagged; see section review. |
| [18.23.E3](https://dlmf.nist.gov/18.23.E3) | [krawtchouk_generating_function](../OrthogonalPolynomials/Hahn.lean) (line 702; local) |
| [18.23.E4](https://dlmf.nist.gov/18.23.E4) | [meixner_generating_function](../OrthogonalPolynomials/Hahn.lean) (line 757; local) |
| [18.23.E5](https://dlmf.nist.gov/18.23.E5) | [charlier_generating_function](../OrthogonalPolynomials/Hahn.lean) (line 821; local) |
| [18.23.E6](https://dlmf.nist.gov/18.23.E6) | [continuousHahn_generating_function](../OrthogonalPolynomials/Hahn.lean) (line 1484; local) |
| [18.23.E7](https://dlmf.nist.gov/18.23.E7) | [meixnerPollaczek_generating_function](../OrthogonalPolynomials/Hahn.lean) (line 851; local) |

### §18.24

| DLMF | Local declaration or Mathlib record |
| --- | --- |
| — | No numbered display; see section review. |

### §18.25

| DLMF | Local declaration or Mathlib record |
| --- | --- |
| [18.25.E1](https://dlmf.nist.gov/18.25.E1) | — Not separately tagged; see section review. |
| [18.25.E2](https://dlmf.nist.gov/18.25.E2) | [wilson_orthogonal](../OrthogonalPolynomials/Wilson.lean) (line 168; local) |
| [18.25.E3](https://dlmf.nist.gov/18.25.E3) | — Not separately tagged; see section review. |
| [18.25.E4](https://dlmf.nist.gov/18.25.E4) | — Not separately tagged; see section review. |
| [18.25.E5](https://dlmf.nist.gov/18.25.E5) | — Not separately tagged; see section review. |
| [18.25.E6](https://dlmf.nist.gov/18.25.E6) | — Not separately tagged; see section review. |
| [18.25.E7](https://dlmf.nist.gov/18.25.E7) | — Not separately tagged; see section review. |
| [18.25.E8](https://dlmf.nist.gov/18.25.E8) | [continuousDualHahn_orthogonality](../OrthogonalPolynomials/Wilson.lean) (line 174; local) |
| [18.25.E9](https://dlmf.nist.gov/18.25.E9) | — Not separately tagged; see section review. |
| [18.25.E10](https://dlmf.nist.gov/18.25.E10) | — Not separately tagged; see section review. |
| [18.25.E11](https://dlmf.nist.gov/18.25.E11) | — Not separately tagged; see section review. |
| [18.25.E12](https://dlmf.nist.gov/18.25.E12) | — Not separately tagged; see section review. |
| [18.25.E13](https://dlmf.nist.gov/18.25.E13) | — Not separately tagged; see section review. |
| [18.25.E14](https://dlmf.nist.gov/18.25.E14) | — Not separately tagged; see section review. |
| [18.25.E15](https://dlmf.nist.gov/18.25.E15) | — Not separately tagged; see section review. |
| [18.25.T1](https://dlmf.nist.gov/18.25.T1) | — Not separately tagged; see section review. |
| [18.25.T2](https://dlmf.nist.gov/18.25.T2) | — Not separately tagged; see section review. |

### §18.26

| DLMF | Local declaration or Mathlib record |
| --- | --- |
| [18.26.E1](https://dlmf.nist.gov/18.26.E1) | [wilson](../OrthogonalPolynomials/Wilson.lean) (line 36; local); [wilson_hypergeometric](../OrthogonalPolynomials/Wilson.lean) (line 89; local) |
| [18.26.E2](https://dlmf.nist.gov/18.26.E2) | [continuousDualHahn](../OrthogonalPolynomials/Wilson.lean) (line 44; local); [continuousDualHahn_hypergeometric](../OrthogonalPolynomials/Wilson.lean) (line 101; local) |
| [18.26.E3](https://dlmf.nist.gov/18.26.E3) | [racah](../OrthogonalPolynomials/Wilson.lean) (line 51; local); [racah_hypergeometric](../OrthogonalPolynomials/Wilson.lean) (line 113; local) |
| [18.26.E4](https://dlmf.nist.gov/18.26.E4) | [dualHahn](../OrthogonalPolynomials/Wilson.lean) (line 57; local); [dualHahn_hypergeometric](../OrthogonalPolynomials/Wilson.lean) (line 127; local) |
| [18.26.E4_1](https://dlmf.nist.gov/18.26.E4_1) | [dualHahn_hahn_duality](../OrthogonalPolynomials/Wilson.lean) (line 141; local) |
| [18.26.E4_2](https://dlmf.nist.gov/18.26.E4_2) | [racah_duality](../OrthogonalPolynomials/Wilson.lean) (line 153; local) |
| [18.26.E5](https://dlmf.nist.gov/18.26.E5) | [wilson_limit_continuousDualHahn](../OrthogonalPolynomials/Wilson.lean) (line 198; local) |
| [18.26.E6](https://dlmf.nist.gov/18.26.E6) | — Not separately tagged; see section review. |
| [18.26.E7](https://dlmf.nist.gov/18.26.E7) | — Not separately tagged; see section review. |
| [18.26.E8](https://dlmf.nist.gov/18.26.E8) | — Not separately tagged; see section review. |
| [18.26.E9](https://dlmf.nist.gov/18.26.E9) | [racah_limit_dualHahn](../OrthogonalPolynomials/Wilson.lean) (line 224; local) |
| [18.26.E10](https://dlmf.nist.gov/18.26.E10) | [racah_limit_hahn](../OrthogonalPolynomials/Wilson.lean) (line 241; local) |
| [18.26.E11](https://dlmf.nist.gov/18.26.E11) | — Not separately tagged; see section review. |
| [18.26.E12](https://dlmf.nist.gov/18.26.E12) | — Not separately tagged; see section review. |
| [18.26.E13](https://dlmf.nist.gov/18.26.E13) | — Not separately tagged; see section review. |
| [18.26.E14](https://dlmf.nist.gov/18.26.E14) | [wilson_central_difference](../OrthogonalPolynomials/Wilson.lean) (line 281; local) |
| [18.26.E15](https://dlmf.nist.gov/18.26.E15) | [continuousDualHahn_central_difference](../OrthogonalPolynomials/Wilson.lean) (line 330; local) |
| [18.26.E16](https://dlmf.nist.gov/18.26.E16) | — Not separately tagged; see section review. |
| [18.26.E17](https://dlmf.nist.gov/18.26.E17) | — Not separately tagged; see section review. |
| [18.26.E18](https://dlmf.nist.gov/18.26.E18) | [wilson_generating_function](../OrthogonalPolynomials/Wilson.lean) (line 374; local) |
| [18.26.E19](https://dlmf.nist.gov/18.26.E19) | [continuousDualHahn_generating_function](../OrthogonalPolynomials/Wilson.lean) (line 382; local) |
| [18.26.E20](https://dlmf.nist.gov/18.26.E20) | — Not separately tagged; see section review. |
| [18.26.E21](https://dlmf.nist.gov/18.26.E21) | — Not separately tagged; see section review. |

### §18.27

| DLMF | Local declaration or Mathlib record |
| --- | --- |
| [18.27.E1](https://dlmf.nist.gov/18.27.E1) | — Not separately tagged; see section review. |
| [18.27.E2](https://dlmf.nist.gov/18.27.E2) | — Not separately tagged; see section review. |
| [18.27.E3](https://dlmf.nist.gov/18.27.E3) | [qHahn](../OrthogonalPolynomials/QFamilies.lean) (line 46; local) |
| [18.27.E4](https://dlmf.nist.gov/18.27.E4) | [qHahn_orthogonal](../OrthogonalPolynomials/QFamilies.lean) (line 114; local) |
| [18.27.E4_1](https://dlmf.nist.gov/18.27.E4_1) | — Not separately tagged; see section review. |
| [18.27.E4_2](https://dlmf.nist.gov/18.27.E4_2) | [qHahn_limit_hahn](../OrthogonalPolynomials/QFamilies.lean) (line 438; local) |
| [18.27.E5](https://dlmf.nist.gov/18.27.E5) | [bigQJacobi](../OrthogonalPolynomials/QFamilies.lean) (line 50; local) |
| [18.27.E6](https://dlmf.nist.gov/18.27.E6) | — Not separately tagged; see section review. |
| [18.27.E6_5](https://dlmf.nist.gov/18.27.E6_5) | — Not separately tagged; see section review. |
| [18.27.E7](https://dlmf.nist.gov/18.27.E7) | — Not separately tagged; see section review. |
| [18.27.E8](https://dlmf.nist.gov/18.27.E8) | — Not separately tagged; see section review. |
| [18.27.E9](https://dlmf.nist.gov/18.27.E9) | — Not separately tagged; see section review. |
| [18.27.E9_5](https://dlmf.nist.gov/18.27.E9_5) | — Not separately tagged; see section review. |
| [18.27.E10](https://dlmf.nist.gov/18.27.E10) | — Not separately tagged; see section review. |
| [18.27.E11](https://dlmf.nist.gov/18.27.E11) | — Not separately tagged; see section review. |
| [18.27.E12](https://dlmf.nist.gov/18.27.E12) | — Not separately tagged; see section review. |
| [18.27.E12_5](https://dlmf.nist.gov/18.27.E12_5) | — Not separately tagged; see section review. |
| [18.27.E13](https://dlmf.nist.gov/18.27.E13) | [littleQJacobi](../OrthogonalPolynomials/QFamilies.lean) (line 54; local) |
| [18.27.E14](https://dlmf.nist.gov/18.27.E14) | [littleQJacobi_orthogonal](../OrthogonalPolynomials/QFamilies.lean) (line 124; local) |
| [18.27.E14_1](https://dlmf.nist.gov/18.27.E14_1) | — Not separately tagged; see section review. |
| [18.27.E14_2](https://dlmf.nist.gov/18.27.E14_2) | — Not separately tagged; see section review. |
| [18.27.E14_3](https://dlmf.nist.gov/18.27.E14_3) | — Not separately tagged; see section review. |
| [18.27.E14_4](https://dlmf.nist.gov/18.27.E14_4) | [littleQJacobi_limit_jacobi](../OrthogonalPolynomials/QFamilies.lean) (line 485; local) |
| [18.27.E14_5](https://dlmf.nist.gov/18.27.E14_5) | [littleQLaguerre](../OrthogonalPolynomials/QFamilies.lean) (line 58; local) |
| [18.27.E14_6](https://dlmf.nist.gov/18.27.E14_6) | [littleQLaguerre_limit_laguerrePolynomialL](../OrthogonalPolynomials/QFamilies.lean) (line 529; local) |
| [18.27.E15](https://dlmf.nist.gov/18.27.E15) | [qLaguerre](../OrthogonalPolynomials/QFamilies.lean) (line 61; local) |
| [18.27.E16](https://dlmf.nist.gov/18.27.E16) | [qLaguerre_orthogonal](../OrthogonalPolynomials/QFamilies.lean) (line 132; local) |
| [18.27.E17](https://dlmf.nist.gov/18.27.E17) | — Not separately tagged; see section review. |
| [18.27.E17_1](https://dlmf.nist.gov/18.27.E17_1) | — Not separately tagged; see section review. |
| [18.27.E17_2](https://dlmf.nist.gov/18.27.E17_2) | — Not separately tagged; see section review. |
| [18.27.E17_3](https://dlmf.nist.gov/18.27.E17_3) | [qLaguerre_limit_laguerrePolynomialL](../OrthogonalPolynomials/QFamilies.lean) (line 571; local) |
| [18.27.E18](https://dlmf.nist.gov/18.27.E18) | [stieltjesWigert](../OrthogonalPolynomials/QFamilies.lean) (line 66; local) |
| [18.27.E19](https://dlmf.nist.gov/18.27.E19) | — Not separately tagged; see section review. |
| [18.27.E20](https://dlmf.nist.gov/18.27.E20) | [stieltjesWigert_orthogonal](../OrthogonalPolynomials/QFamilies.lean) (line 138; local) |
| [18.27.E20_5](https://dlmf.nist.gov/18.27.E20_5) | — Not separately tagged; see section review. |
| [18.27.E21](https://dlmf.nist.gov/18.27.E21) | [discreteQHermiteI](../OrthogonalPolynomials/QFamilies.lean) (line 71; local) |
| [18.27.E22](https://dlmf.nist.gov/18.27.E22) | — Not separately tagged; see section review. |
| [18.27.E23](https://dlmf.nist.gov/18.27.E23) | [discreteQHermiteII](../OrthogonalPolynomials/QFamilies.lean) (line 77; local) |
| [18.27.E24](https://dlmf.nist.gov/18.27.E24) | — Not separately tagged; see section review. |
| [18.27.E25](https://dlmf.nist.gov/18.27.E25) | [discreteQHermiteI_limit_hermite](../OrthogonalPolynomials/QFamilies.lean) (line 738; local) |
| [18.27.E26](https://dlmf.nist.gov/18.27.E26) | [discreteQHermiteII_limit_hermite](../OrthogonalPolynomials/QFamilies.lean) (line 781; local) |

### §18.28

| DLMF | Local declaration or Mathlib record |
| --- | --- |
| [18.28.E1](https://dlmf.nist.gov/18.28.E1) | [askeyWilson](../OrthogonalPolynomials/QFamilies.lean) (line 85; local) |
| [18.28.E1_5](https://dlmf.nist.gov/18.28.E1_5) | [askeyWilsonLaurent](../OrthogonalPolynomials/QFamilies.lean) (line 93; local); [askeyWilson_laurent_representation](../OrthogonalPolynomials/QFamilies.lean) (line 167; local) |
| [18.28.E2](https://dlmf.nist.gov/18.28.E2) | [askeyWilson_orthogonal](../OrthogonalPolynomials/QFamilies.lean) (line 189; local) |
| [18.28.E3](https://dlmf.nist.gov/18.28.E3) | — Not separately tagged; see section review. |
| [18.28.E4](https://dlmf.nist.gov/18.28.E4) | — Not separately tagged; see section review. |
| [18.28.E5](https://dlmf.nist.gov/18.28.E5) | — Not separately tagged; see section review. |
| [18.28.E6](https://dlmf.nist.gov/18.28.E6) | — Not separately tagged; see section review. |
| [18.28.E6_1](https://dlmf.nist.gov/18.28.E6_1) | [askeyWilson_difference_equation](../OrthogonalPolynomials/QFamilies.lean) (line 831; local) |
| [18.28.E6_2](https://dlmf.nist.gov/18.28.E6_2) | [askeyWilsonDifferenceCoefficient](../OrthogonalPolynomials/QFamilies.lean) (line 827; local) |
| [18.28.E6_3](https://dlmf.nist.gov/18.28.E6_3) | — Not separately tagged; see section review. |
| [18.28.E6_4](https://dlmf.nist.gov/18.28.E6_4) | — Not separately tagged; see section review. |
| [18.28.E6_5](https://dlmf.nist.gov/18.28.E6_5) | — Not separately tagged; see section review. |
| [18.28.E7](https://dlmf.nist.gov/18.28.E7) | [alSalamChihara](../OrthogonalPolynomials/QFamilies.lean) (line 98; local) |
| [18.28.E8](https://dlmf.nist.gov/18.28.E8) | — Not separately tagged; see section review. |
| [18.28.E9](https://dlmf.nist.gov/18.28.E9) | — Not separately tagged; see section review. |
| [18.28.E10](https://dlmf.nist.gov/18.28.E10) | — Not separately tagged; see section review. |
| [18.28.E11](https://dlmf.nist.gov/18.28.E11) | — Not separately tagged; see section review. |
| [18.28.E12](https://dlmf.nist.gov/18.28.E12) | — Not separately tagged; see section review. |
| [18.28.E13](https://dlmf.nist.gov/18.28.E13) | [qGegenbauer](../QSeries/Identities.lean) (line 458; local) |
| [18.28.E14](https://dlmf.nist.gov/18.28.E14) | — Not separately tagged; see section review. |
| [18.28.E15](https://dlmf.nist.gov/18.28.E15) | [qGegenbauer_orthogonal](../OrthogonalPolynomials/QFamilies.lean) (line 199; local) |
| [18.28.E16](https://dlmf.nist.gov/18.28.E16) | [continuousQHermiteLaurent](../OrthogonalPolynomials/QFamilies.lean) (line 102; local) |
| [18.28.E17](https://dlmf.nist.gov/18.28.E17) | [continuousQHermite_orthogonality](../OrthogonalPolynomials/QFamilies.lean) (line 205; local) |
| [18.28.E18](https://dlmf.nist.gov/18.28.E18) | — Not separately tagged; see section review. |
| [18.28.E19](https://dlmf.nist.gov/18.28.E19) | [qRacah](../OrthogonalPolynomials/QFamilies.lean) (line 106; local) |
| [18.28.E20](https://dlmf.nist.gov/18.28.E20) | — Not separately tagged; see section review. |
| [18.28.E21](https://dlmf.nist.gov/18.28.E21) | — Not separately tagged; see section review. |
| [18.28.E22](https://dlmf.nist.gov/18.28.E22) | — Not separately tagged; see section review. |
| [18.28.E23](https://dlmf.nist.gov/18.28.E23) | [qRacah_duality](../OrthogonalPolynomials/QFamilies.lean) (line 250; local) |
| [18.28.E24](https://dlmf.nist.gov/18.28.E24) | — Not separately tagged; see section review. |
| [18.28.E25](https://dlmf.nist.gov/18.28.E25) | — Not separately tagged; see section review. |
| [18.28.E26](https://dlmf.nist.gov/18.28.E26) | — Not separately tagged; see section review. |
| [18.28.E27](https://dlmf.nist.gov/18.28.E27) | — Not separately tagged; see section review. |
| [18.28.E28](https://dlmf.nist.gov/18.28.E28) | — Not separately tagged; see section review. |
| [18.28.E29](https://dlmf.nist.gov/18.28.E29) | [askeyWilson_limit_wilson](../OrthogonalPolynomials/QFamilies.lean) (line 635; local) |
| [18.28.E30](https://dlmf.nist.gov/18.28.E30) | — Not separately tagged; see section review. |
| [18.28.E31](https://dlmf.nist.gov/18.28.E31) | [qGegenbauer_limit_ultrasphericalPolynomial](../OrthogonalPolynomials/QFamilies.lean) (line 693; local) |
| [18.28.E32](https://dlmf.nist.gov/18.28.E32) | — Not separately tagged; see section review. |
| [18.28.E33](https://dlmf.nist.gov/18.28.E33) | — Not separately tagged; see section review. |
| [18.28.E34](https://dlmf.nist.gov/18.28.E34) | — Not separately tagged; see section review. |

### §18.29

| DLMF | Local declaration or Mathlib record |
| --- | --- |
| [18.29.E1](https://dlmf.nist.gov/18.29.E1) | [askeyWilson_asymptotic](../OrthogonalPolynomials/QFamilies.lean) (line 848; local) |
| [18.29.E2](https://dlmf.nist.gov/18.29.E2) | [askeyWilsonAsymptoticCoefficient](../OrthogonalPolynomials/QFamilies.lean) (line 843; local) |

### §18.30

| DLMF | Local declaration or Mathlib record |
| --- | --- |
| [18.30.E1](https://dlmf.nist.gov/18.30.E1) | — Not separately tagged; see section review. |
| [18.30.E2](https://dlmf.nist.gov/18.30.E2) | [associated_zero](../OrthogonalPolynomials/Associated.lean) (line 94; local) |
| [18.30.E3](https://dlmf.nist.gov/18.30.E3) | [associated](../OrthogonalPolynomials/Associated.lean) (line 37; local) |
| [18.30.E4](https://dlmf.nist.gov/18.30.E4) | — Not separately tagged; see section review. |
| [18.30.E5](https://dlmf.nist.gov/18.30.E5) | — Not separately tagged; see section review. |
| [18.30.E6](https://dlmf.nist.gov/18.30.E6) | — Not separately tagged; see section review. |
| [18.30.E7](https://dlmf.nist.gov/18.30.E7) | — Not separately tagged; see section review. |
| [18.30.E8](https://dlmf.nist.gov/18.30.E8) | — Not separately tagged; see section review. |
| [18.30.E9](https://dlmf.nist.gov/18.30.E9) | [associatedLaguerre](../OrthogonalPolynomials/Associated.lean) (line 44; local) |
| [18.30.E10](https://dlmf.nist.gov/18.30.E10) | — Not separately tagged; see section review. |
| [18.30.E11](https://dlmf.nist.gov/18.30.E11) | — Not separately tagged; see section review. |
| [18.30.E12](https://dlmf.nist.gov/18.30.E12) | — Not separately tagged; see section review. |
| [18.30.E13](https://dlmf.nist.gov/18.30.E13) | [associatedHermite](../OrthogonalPolynomials/Associated.lean) (line 49; local) |
| [18.30.E14](https://dlmf.nist.gov/18.30.E14) | — Not separately tagged; see section review. |
| [18.30.E15](https://dlmf.nist.gov/18.30.E15) | — Not separately tagged; see section review. |
| [18.30.E16](https://dlmf.nist.gov/18.30.E16) | [associatedMeixnerPollaczek](../OrthogonalPolynomials/Associated.lean) (line 53; local) |
| [18.30.E17](https://dlmf.nist.gov/18.30.E17) | — Not separately tagged; see section review. |
| [18.30.E18](https://dlmf.nist.gov/18.30.E18) | — Not separately tagged; see section review. |
| [18.30.E19](https://dlmf.nist.gov/18.30.E19) | [associatedPollaczek_limit_laguerrePolynomialL](../OrthogonalPolynomials/Associated.lean) (line 98; local) |
| [18.30.E20](https://dlmf.nist.gov/18.30.E20) | [associatedPollaczek_limit_hermite](../OrthogonalPolynomials/Associated.lean) (line 156; local) |
| [18.30.E21](https://dlmf.nist.gov/18.30.E21) | — Not separately tagged; see section review. |
| [18.30.E22](https://dlmf.nist.gov/18.30.E22) | — Not separately tagged; see section review. |
| [18.30.E23](https://dlmf.nist.gov/18.30.E23) | — Not separately tagged; see section review. |
| [18.30.E24](https://dlmf.nist.gov/18.30.E24) | — Not separately tagged; see section review. |
| [18.30.E25](https://dlmf.nist.gov/18.30.E25) | — Not separately tagged; see section review. |
| [18.30.E26](https://dlmf.nist.gov/18.30.E26) | — Not separately tagged; see section review. |
| [18.30.E27](https://dlmf.nist.gov/18.30.E27) | — Not separately tagged; see section review. |
| [18.30.E28](https://dlmf.nist.gov/18.30.E28) | — Not separately tagged; see section review. |
| [18.30.E29](https://dlmf.nist.gov/18.30.E29) | — Not separately tagged; see section review. |
| [18.30.E30](https://dlmf.nist.gov/18.30.E30) | — Not separately tagged; see section review. |
| [18.30.E31](https://dlmf.nist.gov/18.30.E31) | — Not separately tagged; see section review. |

### §18.31

| DLMF | Local declaration or Mathlib record |
| --- | --- |
| — | No numbered display; see section review. |

### §18.32

| DLMF | Local declaration or Mathlib record |
| --- | --- |
| [18.32.E1](https://dlmf.nist.gov/18.32.E1) | — Not separately tagged; see section review. |
| [18.32.E2](https://dlmf.nist.gov/18.32.E2) | [freudWeight](../OrthogonalPolynomials/Associated.lean) (line 74; local) |

### §18.33

| DLMF | Local declaration or Mathlib record |
| --- | --- |
| [18.33.E1](https://dlmf.nist.gov/18.33.E1) | — Not separately tagged; see section review. |
| [18.33.E2](https://dlmf.nist.gov/18.33.E2) | — Not separately tagged; see section review. |
| [18.33.E3](https://dlmf.nist.gov/18.33.E3) | — Not separately tagged; see section review. |
| [18.33.E4](https://dlmf.nist.gov/18.33.E4) | — Not separately tagged; see section review. |
| [18.33.E5](https://dlmf.nist.gov/18.33.E5) | — Not separately tagged; see section review. |
| [18.33.E6](https://dlmf.nist.gov/18.33.E6) | — Not separately tagged; see section review. |
| [18.33.E7](https://dlmf.nist.gov/18.33.E7) | — Not separately tagged; see section review. |
| [18.33.E8](https://dlmf.nist.gov/18.33.E8) | — Not separately tagged; see section review. |
| [18.33.E9](https://dlmf.nist.gov/18.33.E9) | — Not separately tagged; see section review. |
| [18.33.E10](https://dlmf.nist.gov/18.33.E10) | — Not separately tagged; see section review. |
| [18.33.E11](https://dlmf.nist.gov/18.33.E11) | — Not separately tagged; see section review. |
| [18.33.E12](https://dlmf.nist.gov/18.33.E12) | — Not separately tagged; see section review. |
| [18.33.E13](https://dlmf.nist.gov/18.33.E13) | [szegoAskey](../OrthogonalPolynomials/UnitCircle.lean) (line 51; local) |
| [18.33.E14](https://dlmf.nist.gov/18.33.E14) | [szegoAskey_orthogonal](../OrthogonalPolynomials/UnitCircle.lean) (line 496; local) |
| [18.33.E15](https://dlmf.nist.gov/18.33.E15) | [szegoAskeyQ](../OrthogonalPolynomials/UnitCircle.lean) (line 56; local) |
| [18.33.E16](https://dlmf.nist.gov/18.33.E16) | [szegoAskeyQ_orthogonal](../OrthogonalPolynomials/UnitCircle.lean) (line 502; local) |
| [18.33.E17](https://dlmf.nist.gov/18.33.E17) | [IsUnitCircleOP](../OrthogonalPolynomials/UnitCircle.lean) (line 40; local) |
| [18.33.E18](https://dlmf.nist.gov/18.33.E18) | — Not separately tagged; see section review. |
| [18.33.E19](https://dlmf.nist.gov/18.33.E19) | — Not separately tagged; see section review. |
| [18.33.E20](https://dlmf.nist.gov/18.33.E20) | — Not separately tagged; see section review. |
| [18.33.E21](https://dlmf.nist.gov/18.33.E21) | — Not separately tagged; see section review. |
| [18.33.E22](https://dlmf.nist.gov/18.33.E22) | [reflectedPolynomial](../OrthogonalPolynomials/UnitCircle.lean) (line 34; local) |
| [18.33.E23](https://dlmf.nist.gov/18.33.E23) | [szego_recurrence](../OrthogonalPolynomials/UnitCircle.lean) (line 424; local) |
| [18.33.E24](https://dlmf.nist.gov/18.33.E24) | [szego_reflected_recurrence](../OrthogonalPolynomials/UnitCircle.lean) (line 430; local) |
| [18.33.E25](https://dlmf.nist.gov/18.33.E25) | [verblunskyCoefficient](../OrthogonalPolynomials/UnitCircle.lean) (line 48; local); [verblunskyCoefficient_norm_lt_one](../OrthogonalPolynomials/UnitCircle.lean) (line 439; local) |
| [18.33.E26](https://dlmf.nist.gov/18.33.E26) | [unitCircle_norm_ratio](../OrthogonalPolynomials/UnitCircle.lean) (line 453; local) |
| [18.33.E27](https://dlmf.nist.gov/18.33.E27) | [inverse_szego_recurrence](../OrthogonalPolynomials/UnitCircle.lean) (line 459; local) |
| [18.33.E28](https://dlmf.nist.gov/18.33.E28) | [inverse_reflected_szego_recurrence](../OrthogonalPolynomials/UnitCircle.lean) (line 469; local) |
| [18.33.E29](https://dlmf.nist.gov/18.33.E29) | — Not separately tagged; see section review. |
| [18.33.E30](https://dlmf.nist.gov/18.33.E30) | [unitCircle_three_term_recurrence](../OrthogonalPolynomials/UnitCircle.lean) (line 479; local) |
| [18.33.E31](https://dlmf.nist.gov/18.33.E31) | — Not separately tagged; see section review. |
| [18.33.E32](https://dlmf.nist.gov/18.33.E32) | — Not separately tagged; see section review. |
| [18.33.vi](https://dlmf.nist.gov/18.33.vi) | [verblunsky_theorem](../OrthogonalPolynomials/UnitCircle.lean) (line 491; local) |

### §18.34

| DLMF | Local declaration or Mathlib record |
| --- | --- |
| [18.34.E1](https://dlmf.nist.gov/18.34.E1) | [besselPolynomial](../OrthogonalPolynomials/Associated.lean) (line 64; local); [besselPolynomial_eq_laguerrePolynomialL](../OrthogonalPolynomials/Associated.lean) (line 218; local) |
| [18.34.E2](https://dlmf.nist.gov/18.34.E2) | [reverseBesselPolynomial](../OrthogonalPolynomials/Associated.lean) (line 69; local); [reverseBesselPolynomial_eq](../OrthogonalPolynomials/Associated.lean) (line 243; local) |
| [18.34.E3](https://dlmf.nist.gov/18.34.E3) | — Not separately tagged; see section review. |
| [18.34.E4](https://dlmf.nist.gov/18.34.E4) | [besselPolynomial_recurrence](../OrthogonalPolynomials/Associated.lean) (line 329; local) |
| [18.34.E5](https://dlmf.nist.gov/18.34.E5) | — Not separately tagged; see section review. |
| [18.34.E5_5](https://dlmf.nist.gov/18.34.E5_5) | [besselPolynomial_finite_orthogonality](../OrthogonalPolynomials/Associated.lean) (line 427; local) |
| [18.34.E6](https://dlmf.nist.gov/18.34.E6) | — Not separately tagged; see section review. |
| [18.34.E7](https://dlmf.nist.gov/18.34.E7) | [besselPolynomial_differential_equation](../OrthogonalPolynomials/Associated.lean) (line 369; local) |
| [18.34.E7_1](https://dlmf.nist.gov/18.34.E7_1) | [morsePolynomialFunction](../OrthogonalPolynomials/Associated.lean) (line 779; local) |
| [18.34.E7_2](https://dlmf.nist.gov/18.34.E7_2) | [morsePolynomialFunction_ode](../OrthogonalPolynomials/Associated.lean) (line 796; local) |
| [18.34.E7_3](https://dlmf.nist.gov/18.34.E7_3) | [morsePolynomialFunction_orthogonality](../OrthogonalPolynomials/Associated.lean) (line 886; local) |
| [18.34.E8](https://dlmf.nist.gov/18.34.E8) | [jacobi_limit_besselPolynomial](../OrthogonalPolynomials/Associated.lean) (line 435; local) |

### §18.35

| DLMF | Local declaration or Mathlib record |
| --- | --- |
| [18.35.E0_5](https://dlmf.nist.gov/18.35.E0_5) | — Not separately tagged; see section review. |
| [18.35.E1](https://dlmf.nist.gov/18.35.E1) | — Not separately tagged; see section review. |
| [18.35.E2](https://dlmf.nist.gov/18.35.E2) | [pollaczek](../OrthogonalPolynomials/Associated.lean) (line 59; local) |
| [18.35.E2_1](https://dlmf.nist.gov/18.35.E2_1) | — Not separately tagged; see section review. |
| [18.35.E2_2](https://dlmf.nist.gov/18.35.E2_2) | — Not separately tagged; see section review. |
| [18.35.E2_3](https://dlmf.nist.gov/18.35.E2_3) | — Not separately tagged; see section review. |
| [18.35.E2_4](https://dlmf.nist.gov/18.35.E2_4) | — Not separately tagged; see section review. |
| [18.35.E2_5](https://dlmf.nist.gov/18.35.E2_5) | [pollaczek_reflection](../OrthogonalPolynomials/Associated.lean) (line 472; local) |
| [18.35.E3](https://dlmf.nist.gov/18.35.E3) | [pollaczekTau](../OrthogonalPolynomials/Associated.lean) (line 762; local) |
| [18.35.E4](https://dlmf.nist.gov/18.35.E4) | [pollaczek_finite_sum](../OrthogonalPolynomials/Associated.lean) (line 530; local) |
| [18.35.E4_5](https://dlmf.nist.gov/18.35.E4_5) | — Not separately tagged; see section review. |
| [18.35.E5](https://dlmf.nist.gov/18.35.E5) | [pollaczek_orthogonality](../OrthogonalPolynomials/Associated.lean) (line 771; local) |
| [18.35.E6](https://dlmf.nist.gov/18.35.E6) | [pollaczekAngularWeight](../OrthogonalPolynomials/Associated.lean) (line 766; local) |
| [18.35.E6_1](https://dlmf.nist.gov/18.35.E6_1) | — Not separately tagged; see section review. |
| [18.35.E6_2](https://dlmf.nist.gov/18.35.E6_2) | — Not separately tagged; see section review. |
| [18.35.E6_3](https://dlmf.nist.gov/18.35.E6_3) | — Not separately tagged; see section review. |
| [18.35.E6_4](https://dlmf.nist.gov/18.35.E6_4) | — Not separately tagged; see section review. |
| [18.35.E6_5](https://dlmf.nist.gov/18.35.E6_5) | — Not separately tagged; see section review. |
| [18.35.E6_6](https://dlmf.nist.gov/18.35.E6_6) | — Not separately tagged; see section review. |
| [18.35.E7](https://dlmf.nist.gov/18.35.E7) | [pollaczek_generating_function](../OrthogonalPolynomials/Associated.lean) (line 550; local) |
| [18.35.E8](https://dlmf.nist.gov/18.35.E8) | [pollaczek_eq_ultrasphericalPolynomial](../OrthogonalPolynomials/Associated.lean) (line 570; local) |
| [18.35.E9](https://dlmf.nist.gov/18.35.E9) | [pollaczek_eq_meixnerPollaczek](../OrthogonalPolynomials/Associated.lean) (line 588; local) |
| [18.35.E10](https://dlmf.nist.gov/18.35.E10) | [pollaczek_eq_associatedMeixnerPollaczek](../OrthogonalPolynomials/Associated.lean) (line 608; local) |

### §18.36

| DLMF | Local declaration or Mathlib record |
| --- | --- |
| [18.36.E1](https://dlmf.nist.gov/18.36.E1) | — Not separately tagged; see section review. |
| [18.36.E2](https://dlmf.nist.gov/18.36.E2) | [laguerrePolynomialL_negative_integer_parameter](../OrthogonalPolynomials/Associated.lean) (line 622; local) |
| [18.36.E3](https://dlmf.nist.gov/18.36.E3) | [exceptionalLaguerreWeight](../OrthogonalPolynomials/Associated.lean) (line 83; local) |
| [18.36.E4](https://dlmf.nist.gov/18.36.E4) | — Not separately tagged; see section review. |
| [18.36.E5](https://dlmf.nist.gov/18.36.E5) | [exceptionalLaguerre](../OrthogonalPolynomials/Associated.lean) (line 79; local) |
| [18.36.E6](https://dlmf.nist.gov/18.36.E6) | [exceptionalLaguerre_orthogonality](../OrthogonalPolynomials/Associated.lean) (line 688; local) |
| [18.36.E7](https://dlmf.nist.gov/18.36.E7) | [exceptionalLaguerre_differential_equation](../OrthogonalPolynomials/Associated.lean) (line 694; local) |
| [18.36.E8](https://dlmf.nist.gov/18.36.E8) | — Not separately tagged; see section review. |
| [18.36.E9](https://dlmf.nist.gov/18.36.E9) | [exceptionalHermite](../OrthogonalPolynomials/Associated.lean) (line 87; local) |
| [18.36.E10](https://dlmf.nist.gov/18.36.E10) | [exceptionalHermite_orthonormal](../OrthogonalPolynomials/Associated.lean) (line 755; local) |

### §18.37

| DLMF | Local declaration or Mathlib record |
| --- | --- |
| [18.37.E1](https://dlmf.nist.gov/18.37.E1) | [diskPolynomial_polar](../OrthogonalPolynomials/Multivariate.lean) (line 45; local) |
| [18.37.E2](https://dlmf.nist.gov/18.37.E2) | [diskPolynomial_orthogonal](../OrthogonalPolynomials/Multivariate.lean) (line 91; local) |
| [18.37.E3](https://dlmf.nist.gov/18.37.E3) | — Not separately tagged; see section review. |
| [18.37.E4](https://dlmf.nist.gov/18.37.E4) | — Not separately tagged; see section review. |
| [18.37.E5](https://dlmf.nist.gov/18.37.E5) | [diskPolynomial_at_one](../OrthogonalPolynomials/Multivariate.lean) (line 53; local) |
| [18.37.E6](https://dlmf.nist.gov/18.37.E6) | [diskPolynomial](../OrthogonalPolynomials/Multivariate.lean) (line 32; local) |
| [18.37.E7](https://dlmf.nist.gov/18.37.E7) | [trianglePolynomial](../OrthogonalPolynomials/Multivariate.lean) (line 40; local) |
| [18.37.E8](https://dlmf.nist.gov/18.37.E8) | [trianglePolynomial_orthogonal](../OrthogonalPolynomials/Multivariate.lean) (line 98; local) |

## New declaration checklist

All names below are in namespace `DLMF.OrthogonalPolynomials`. This checklist identifies every new proof obligation, including proofs completed in subsequent work.

| Module | Declaration | Status |
| --- | --- | --- |
| [Associated.lean](Associated.lean) | `associated` | definition |
| [Associated.lean](Associated.lean) | `associatedLaguerre` | definition |
| [Associated.lean](Associated.lean) | `associatedHermite` | definition |
| [Associated.lean](Associated.lean) | `associatedMeixnerPollaczek` | definition |
| [Associated.lean](Associated.lean) | `pollaczek` | definition |
| [Associated.lean](Associated.lean) | `besselPolynomial` | definition |
| [Associated.lean](Associated.lean) | `reverseBesselPolynomial` | definition |
| [Associated.lean](Associated.lean) | `freudWeight` | definition |
| [Associated.lean](Associated.lean) | `exceptionalLaguerre` | definition |
| [Associated.lean](Associated.lean) | `exceptionalLaguerreWeight` | definition |
| [Associated.lean](Associated.lean) | `exceptionalHermite` | definition |
| [Associated.lean](Associated.lean) | `associated_zero` | proved |
| [Associated.lean](Associated.lean) | `associatedPollaczek_limit_laguerrePolynomialL` | proved |
| [Associated.lean](Associated.lean) | `associatedPollaczek_limit_hermite` | proved |
| [Associated.lean](Associated.lean) | `besselPolynomial_eq_laguerrePolynomialL` | proved |
| [Associated.lean](Associated.lean) | `reverseBesselPolynomial_eq` | proved |
| [Associated.lean](Associated.lean) | `besselPolynomial_recurrence` | proved |
| [Associated.lean](Associated.lean) | `besselPolynomial_differential_equation` | proved |
| [Associated.lean](Associated.lean) | `besselPolynomial_finite_orthogonality` | `sorry` |
| [Associated.lean](Associated.lean) | `jacobi_limit_besselPolynomial` | proved |
| [Associated.lean](Associated.lean) | `pollaczek_reflection` | proved |
| [Associated.lean](Associated.lean) | `pollaczek_finite_sum` | proved |
| [Associated.lean](Associated.lean) | `pollaczek_generating_function` | proved |
| [Associated.lean](Associated.lean) | `pollaczek_eq_ultrasphericalPolynomial` | proved |
| [Associated.lean](Associated.lean) | `pollaczek_eq_meixnerPollaczek` | proved |
| [Associated.lean](Associated.lean) | `pollaczek_eq_associatedMeixnerPollaczek` | proved |
| [Associated.lean](Associated.lean) | `laguerrePolynomialL_negative_integer_parameter` | proved |
| [Associated.lean](Associated.lean) | `exceptionalLaguerre_orthogonality` | `sorry` |
| [Associated.lean](Associated.lean) | `exceptionalLaguerre_differential_equation` | proved |
| [Associated.lean](Associated.lean) | `exceptionalHermite_orthonormal` | `sorry` |
| [Associated.lean](Associated.lean) | `pollaczekTau` | definition |
| [Associated.lean](Associated.lean) | `pollaczekAngularWeight` | definition |
| [Associated.lean](Associated.lean) | `pollaczek_orthogonality` | `sorry` |
| [Associated.lean](Associated.lean) | `morsePolynomialFunction` | definition |
| [Associated.lean](Associated.lean) | `morsePolynomialFunction_ode` | proved |
| [Associated.lean](Associated.lean) | `morsePolynomialFunction_orthogonality` | `sorry` |
| [BoundsZeros.lean](BoundsZeros.lean) | `jacobi_bound_at_one` | proved |
| [BoundsZeros.lean](BoundsZeros.lean) | `jacobi_bound_at_neg_one` | proved |
| [BoundsZeros.lean](BoundsZeros.lean) | `jacobi_bernstein_bound` | `sorry` |
| [BoundsZeros.lean](BoundsZeros.lean) | `ultrasphericalPolynomial_bound_at_one` | proved |
| [BoundsZeros.lean](BoundsZeros.lean) | `ultrasphericalPolynomial_even_bound` | proved |
| [BoundsZeros.lean](BoundsZeros.lean) | `ultrasphericalPolynomial_odd_bound` | proved |
| [BoundsZeros.lean](BoundsZeros.lean) | `ultrasphericalPolynomial_bernstein_bound` | `sorry` |
| [BoundsZeros.lean](BoundsZeros.lean) | `laguerrePolynomialL_bound` | `sorry` |
| [BoundsZeros.lean](BoundsZeros.lean) | `hermitePolynomialH_bound` | `sorry` |
| [BoundsZeros.lean](BoundsZeros.lean) | `jacobi_turan` | `sorry` |
| [BoundsZeros.lean](BoundsZeros.lean) | `laguerrePolynomialL_turan` | `sorry` |
| [BoundsZeros.lean](BoundsZeros.lean) | `hermitePolynomialH_turan` | proved |
| [BoundsZeros.lean](BoundsZeros.lean) | `jacobi_positive_weighted_sum` | `sorry` |
| [BoundsZeros.lean](BoundsZeros.lean) | `jacobi_positive_sum` | `sorry` |
| [BoundsZeros.lean](BoundsZeros.lean) | `laguerrePolynomialL_positive_weighted_sum` | `sorry` |
| [BoundsZeros.lean](BoundsZeros.lean) | `jacobi_zeros` | proved |
| [BoundsZeros.lean](BoundsZeros.lean) | `laguerrePolynomialL_zeros` | proved |
| [BoundsZeros.lean](BoundsZeros.lean) | `hermitePolynomialH_zeros` | proved |
| [BoundsZeros.lean](BoundsZeros.lean) | `jacobi_darboux_asymptotic` | `sorry` |
| [BoundsZeros.lean](BoundsZeros.lean) | `jacobi_weighted_bound` | `sorry` |
| [BoundsZeros.lean](BoundsZeros.lean) | `laguerrePolynomialL_zero_lower_bound` | proved |
| [BoundsZeros.lean](BoundsZeros.lean) | `laguerrePolynomialL_zero_upper_bound` | proved |
| [BoundsZeros.lean](BoundsZeros.lean) | `rootDiscriminant` | definition |
| [BoundsZeros.lean](BoundsZeros.lean) | `jacobi_discriminant` | proved |
| [BoundsZeros.lean](BoundsZeros.lean) | `laguerrePolynomialL_discriminant` | proved |
| [BoundsZeros.lean](BoundsZeros.lean) | `hermitePolynomialH_discriminant` | proved |
| [ContinuedFractions.lean](ContinuedFractions.lean) | `polynomialFraction` | definition |
| [ContinuedFractions.lean](ContinuedFractions.lean) | `chebyshevT_continued_fraction` | proved |
| [ContinuedFractions.lean](ContinuedFractions.lean) | `chebyshevU_continued_fraction` | proved |
| [ContinuedFractions.lean](ContinuedFractions.lean) | `legendre_continued_fraction` | proved |
| [ContinuedFractions.lean](ContinuedFractions.lean) | `laguerrePolynomialL_continued_fraction` | proved |
| [ContinuedFractions.lean](ContinuedFractions.lean) | `hermitePolynomialH_continued_fraction` | proved |
| [Differential.lean](Differential.lean) | `jacobi_differential_equation` | proved |
| [Differential.lean](Differential.lean) | `ultrasphericalPolynomial_differential_equation` | proved |
| [Differential.lean](Differential.lean) | `legendre_differential_equation` | proved |
| [Differential.lean](Differential.lean) | `laguerrePolynomialL_differential_equation` | proved |
| [Differential.lean](Differential.lean) | `hermitePolynomialH_differential_equation` | proved |
| [Differential.lean](Differential.lean) | `hermite_differential_equation` | proved |
| [Differential.lean](Differential.lean) | `jacobi_recurrence` | proved |
| [Differential.lean](Differential.lean) | `ultrasphericalPolynomial_recurrence` | proved |
| [Differential.lean](Differential.lean) | `laguerrePolynomialL_recurrence` | proved |
| [Differential.lean](Differential.lean) | `hermitePolynomialH_recurrence` | proved |
| [Differential.lean](Differential.lean) | `hermite_recurrence` | proved |
| [Differential.lean](Differential.lean) | `jacobi_contiguous_sub` | proved |
| [Differential.lean](Differential.lean) | `jacobi_contiguous_add` | proved |
| [Differential.lean](Differential.lean) | `jacobi_raise_beta` | proved |
| [Differential.lean](Differential.lean) | `jacobi_raise_degree_beta` | proved |
| [Differential.lean](Differential.lean) | `ultrasphericalPolynomial_raise_parameter` | proved |
| [Differential.lean](Differential.lean) | `ultrasphericalPolynomial_raise_parameter_sq` | proved |
| [Differential.lean](Differential.lean) | `chebyshevV_contiguous` | proved |
| [Differential.lean](Differential.lean) | `chebyshevV_mul_one_add` | proved |
| [Differential.lean](Differential.lean) | `laguerrePolynomialL_raise_parameter` | proved |
| [Differential.lean](Differential.lean) | `laguerrePolynomialL_mul_argument` | proved |
| [Differential.lean](Differential.lean) | `jacobi_derivative` | proved |
| [Differential.lean](Differential.lean) | `jacobi_lowering_derivative` | proved |
| [Differential.lean](Differential.lean) | `jacobi_raising_derivative` | proved |
| [Differential.lean](Differential.lean) | `ultrasphericalPolynomial_derivative` | proved |
| [Differential.lean](Differential.lean) | `laguerrePolynomialL_derivative` | proved |
| [Classical.lean](Classical.lean) | `hermitePolynomialH_derivative` | proved |
| [Differential.lean](Differential.lean) | `hermite_derivative` | proved |
| [Differential.lean](Differential.lean) | `hermitePolynomialH_weighted_derivative` | proved |
| [Differential.lean](Differential.lean) | `hermite_weighted_derivative` | proved |
| [Differential.lean](Differential.lean) | `jacobi_weighted_derivative` | proved |
| [Differential.lean](Differential.lean) | `ultrasphericalPolynomial_weighted_derivative` | proved |
| [Differential.lean](Differential.lean) | `chebyshevU_weighted_derivative` | proved |
| [Differential.lean](Differential.lean) | `laguerrePolynomialL_weighted_derivative` | proved |
| [Explicit.lean](Explicit.lean) | `laguerreExtended` | definition |
| [Explicit.lean](Explicit.lean) | `laguerreExtended_eq` | proved |
| [Explicit.lean](Explicit.lean) | `chebyshevV` | definition |
| [Explicit.lean](Explicit.lean) | `chebyshevW` | definition |
| [Differential.lean](Differential.lean) | `chebyshevV_cos` | proved |
| [Differential.lean](Differential.lean) | `chebyshevW_cos` | proved |
| [Explicit.lean](Explicit.lean) | `jacobi_finite_sum` | proved |
| [Explicit.lean](Explicit.lean) | `jacobi_binomial_sum` | proved |
| [Differential.lean](Differential.lean) | `chebyshevT_hypergeometric` | proved |
| [Explicit.lean](Explicit.lean) | `hermitePolynomialH_finite_sum` | proved |
| [Explicit.lean](Explicit.lean) | `laguerrePolynomialL_at_zero` | proved |
| [Differential.lean](Differential.lean) | `jacobi_reflection` | proved |
| [Explicit.lean](Explicit.lean) | `jacobi_at_one` | proved |
| [Differential.lean](Differential.lean) | `jacobi_symmetric_even_at_zero` | proved |
| [Differential.lean](Differential.lean) | `ultrasphericalPolynomial_reflection` | proved |
| [Explicit.lean](Explicit.lean) | `ultrasphericalPolynomial_at_one` | proved |
| [Differential.lean](Differential.lean) | `ultrasphericalPolynomial_even_at_zero` | proved |
| [Explicit.lean](Explicit.lean) | `hermitePolynomialH_reflection` | proved |
| [Explicit.lean](Explicit.lean) | `hermitePolynomialH_even_at_zero` | proved |
| [Differential.lean](Differential.lean) | `chebyshevV_reflection` | proved |
| [Differential.lean](Differential.lean) | `chebyshevW_reflection` | proved |
| [Explicit.lean](Explicit.lean) | `chebyshevV_at_one` | proved |
| [Explicit.lean](Explicit.lean) | `chebyshevW_at_one` | proved |
| [Differential.lean](Differential.lean) | `chebyshevT_eq_jacobi` | proved |
| [Explicit.lean](Explicit.lean) | `legendre_eq_ultrasphericalPolynomial` | proved |
| [GegenbauerSeries.lean](GegenbauerSeries.lean) | `jacobi_quadratic_even` | proved |
| [GegenbauerSeries.lean](GegenbauerSeries.lean) | `jacobi_quadratic_odd` | proved |
| [GegenbauerSeries.lean](GegenbauerSeries.lean) | `ultrasphericalPolynomial_quadratic_even` | proved |
| [GegenbauerSeries.lean](GegenbauerSeries.lean) | `ultrasphericalPolynomial_quadratic_odd` | proved |
| [Differential.lean](Differential.lean) | `chebyshevU_quadratic` | proved |
| [Differential.lean](Differential.lean) | `chebyshevT_quadratic` | proved |
| [Explicit.lean](Explicit.lean) | `hermitePolynomialH_even_eq_laguerrePolynomialL` | proved |
| [Explicit.lean](Explicit.lean) | `hermitePolynomialH_odd_eq_laguerrePolynomialL` | proved |
| [Explicit.lean](Explicit.lean) | `chebyshevT_discrete_orthogonality` | proved |
| [Explicit.lean](Explicit.lean) | `chebyshevT_finite_sum` | proved |
| [Explicit.lean](Explicit.lean) | `chebyshevU_finite_sum` | proved |
| [GeneralIdentities.lean](GeneralIdentities.lean) | `squaredNorm` | definition |
| [GeneralIdentities.lean](GeneralIdentities.lean) | `christoffelDarbouxKernel` | definition |
| [GeneralIdentities.lean](GeneralIdentities.lean) | `moment` | definition |
| [GeneralIdentities.lean](GeneralIdentities.lean) | `hankelDeterminant` | definition |
| [GeneralIdentities.lean](GeneralIdentities.lean) | `recurrenceDiagonal` | definition |
| [GeneralIdentities.lean](GeneralIdentities.lean) | `integral_product` | proved |
| [GeneralIdentities.lean](GeneralIdentities.lean) | `recurrenceDiagonal_eq_integral` | proved |
| [GeneralIdentities.lean](GeneralIdentities.lean) | `sum_recurrenceDiagonal` | proved |
| [GeneralIdentities.lean](GeneralIdentities.lean) | `kernel_reproduces` | proved |
| [GeneralIdentities.lean](GeneralIdentities.lean) | `christoffel_darboux_diagonal` | proved |
| [GeneralIdentities.lean](GeneralIdentities.lean) | `kernel_difference` | proved |
| [GeneralIdentities.lean](GeneralIdentities.lean) | `hankelDeterminant_pos` | proved |
| [GeneralIdentities.lean](GeneralIdentities.lean) | `monic_squaredNorm_ratio` | proved |
| [GeneralIdentities.lean](GeneralIdentities.lean) | `zeros_interlace` | proved |
| [GeneralIdentities.lean](GeneralIdentities.lean) | `symmetric_measure_parity` | proved |
| [GeneralIdentities.lean](GeneralIdentities.lean) | `firstWeightedSquaredNorm` | definition |
| [GeneralIdentities.lean](GeneralIdentities.lean) | `shiftedHankelDeterminant` | definition |
| [GeneralIdentities.lean](GeneralIdentities.lean) | `poissonKernel` | definition |
| [GeneralIdentities.lean](GeneralIdentities.lean) | `IsSzegoWeight` | definition |
| [GeneralIdentities.lean](GeneralIdentities.lean) | `IsNevaiClass` | definition |
| [GeneralIdentities.lean](GeneralIdentities.lean) | `kernel_annihilates` | proved |
| [GeneralIdentities.lean](GeneralIdentities.lean) | `kernel_polynomials_orthogonal` | proved |
| [GeneralIdentities.lean](GeneralIdentities.lean) | `monic_moment_determinant` | `sorry` |
| [GeneralIdentities.lean](GeneralIdentities.lean) | `monic_diagonal_moment_determinant` | `sorry` |
| [GeneralIdentities.lean](GeneralIdentities.lean) | `monic_offdiagonal_moment_determinant` | `sorry` |
| [GeneralIdentities.lean](GeneralIdentities.lean) | `compact_support_L2_expansion` | proved |
| [Hahn.lean](Hahn.lean) | `terminatingHypergeometric` | definition |
| [Hahn.lean](Hahn.lean) | `hahn` | definition |
| [Hahn.lean](Hahn.lean) | `krawtchouk` | definition |
| [Hahn.lean](Hahn.lean) | `meixner` | definition |
| [Hahn.lean](Hahn.lean) | `charlier` | definition |
| [Hahn.lean](Hahn.lean) | `continuousHahn` | definition |
| [Hahn.lean](Hahn.lean) | `meixnerPollaczek` | definition |
| [Hahn.lean](Hahn.lean) | `continuousHahnWeight` | definition |
| [Hahn.lean](Hahn.lean) | `meixnerPollaczekWeight` | definition |
| [Hahn.lean](Hahn.lean) | `hahn_orthogonal` | proved |
| [Hahn.lean](Hahn.lean) | `krawtchouk_orthogonality` | proved |
| [Hahn.lean](Hahn.lean) | `meixner_orthogonality` | proved |
| [Hahn.lean](Hahn.lean) | `charlier_orthogonality` | proved |
| [Hahn.lean](Hahn.lean) | `continuousHahn_orthogonal` | `sorry` |
| [Hahn.lean](Hahn.lean) | `meixnerPollaczek_orthogonality` | `sorry` |
| [Hahn.lean](Hahn.lean) | `krawtchouk_duality` | proved |
| [Hahn.lean](Hahn.lean) | `meixner_duality` | proved |
| [Hahn.lean](Hahn.lean) | `charlier_duality` | proved |
| [Hahn.lean](Hahn.lean) | `hahn_difference_equation` | proved |
| [Hahn.lean](Hahn.lean) | `krawtchouk_difference_equation` | proved |
| [Hahn.lean](Hahn.lean) | `meixner_difference_equation` | proved |
| [Hahn.lean](Hahn.lean) | `charlier_difference_equation` | proved |
| [Hahn.lean](Hahn.lean) | `hahn_forward_difference` | proved |
| [Hahn.lean](Hahn.lean) | `krawtchouk_forward_difference` | proved |
| [Hahn.lean](Hahn.lean) | `meixner_forward_difference` | proved |
| [Hahn.lean](Hahn.lean) | `charlier_forward_difference` | proved |
| [Hahn.lean](Hahn.lean) | `meixnerPollaczek_recurrence` | proved |
| [Hahn.lean](Hahn.lean) | `meixnerPollaczek_central_difference` | proved |
| [Hahn.lean](Hahn.lean) | `krawtchouk_generating_function` | proved |
| [Hahn.lean](Hahn.lean) | `meixner_generating_function` | proved |
| [Hahn.lean](Hahn.lean) | `charlier_generating_function` | proved |
| [Hahn.lean](Hahn.lean) | `meixnerPollaczek_generating_function` | proved |
| [Hahn.lean](Hahn.lean) | `hahn_limit_krawtchouk` | proved |
| [Hahn.lean](Hahn.lean) | `hahn_limit_jacobi` | proved |
| [Hahn.lean](Hahn.lean) | `krawtchouk_limit_charlier` | proved |
| [Hahn.lean](Hahn.lean) | `meixner_limit_charlier` | proved |
| [Hahn.lean](Hahn.lean) | `charlier_limit_hermite` | proved |
| [Hahn.lean](Hahn.lean) | `hahn_limit_meixner` | proved |
| [Hahn.lean](Hahn.lean) | `meixner_limit_laguerrePolynomialL` | proved |
| [Hahn.lean](Hahn.lean) | `meixnerPollaczek_limit_laguerrePolynomialL` | proved |
| [Hahn.lean](Hahn.lean) | `meixnerPollaczek_limit_hermite` | proved |
| [Hahn.lean](Hahn.lean) | `continuousHahn_difference_equation` | proved |
| [Hahn.lean](Hahn.lean) | `meixnerPollaczek_difference_equation` | proved |
| [Hahn.lean](Hahn.lean) | `continuousHahn_central_difference` | proved |
| [Hahn.lean](Hahn.lean) | `continuousHahn_generating_function` | `sorry` |
| [Hahn.lean](Hahn.lean) | `meixner_recurrence` | proved |
| [Hahn.lean](Hahn.lean) | `krawtchouk_recurrence` | proved |
| [Hahn.lean](Hahn.lean) | `hahn_weight_sum` | proved |
| [Hahn.lean](Hahn.lean) | `hahn_recurrence` | proved |
| [Integrals.lean](Integrals.lean) | `jacobi_norm` | proved |
| [Integrals.lean](Integrals.lean) | `laguerrePolynomialL_norm` | proved |
| [Integrals.lean](Integrals.lean) | `hermitePolynomialH_orthogonality` | proved |
| [Integrals.lean](Integrals.lean) | `hermite_orthogonality` | proved |
| [Integrals.lean](Integrals.lean) | `legendre_orthogonality` | proved |
| [Integrals.lean](Integrals.lean) | `ultrasphericalPolynomial_orthogonality` | proved |
| [Integrals.lean](Integrals.lean) | `jacobi_rodrigues` | proved |
| [Integrals.lean](Integrals.lean) | `laguerrePolynomialL_rodrigues` | proved |
| [Integrals.lean](Integrals.lean) | `legendre_dirichlet_mehler` | `sorry` |
| [Integrals.lean](Integrals.lean) | `ultrasphericalPolynomial_laplace_integral` | proved |
| [Integrals.lean](Integrals.lean) | `legendre_laplace_integral` | proved |
| [Integrals.lean](Integrals.lean) | `hermitePolynomialH_laplace_integral` | proved |
| [Integrals.lean](Integrals.lean) | `hermitePolynomialH_fourier_integral` | proved |
| [Integrals.lean](Integrals.lean) | `hermitePolynomialH_integral` | proved |
| [Integrals.lean](Integrals.lean) | `hermitePolynomialH_weighted_integral` | proved |
| [Integrals.lean](Integrals.lean) | `legendre_product_integral` | `sorry` |
| [Integrals.lean](Integrals.lean) | `laguerrePolynomialL_fractional_integral` | proved |
| [Integrals.lean](Integrals.lean) | `laguerrePolynomialL_fractional_tail_integral` | proved |
| [Integrals.lean](Integrals.lean) | `hermitePolynomialH_fourier_transform` | proved |
| [Integrals.lean](Integrals.lean) | `hermitePolynomialH_fourier_eigenfunction` | proved |
| [Integrals.lean](Integrals.lean) | `laguerrePolynomialL_fourier_transform` | proved |
| [Integrals.lean](Integrals.lean) | `hermitePolynomialH_laplace_transform` | proved |
| [Integrals.lean](Integrals.lean) | `jacobi_mellin_transform` | proved |
| [Integrals.lean](Integrals.lean) | `legendre_even_mellin_transform` | proved |
| [Integrals.lean](Integrals.lean) | `legendre_odd_mellin_transform` | proved |
| [Integrals.lean](Integrals.lean) | `legendre_singular_integral` | `sorry` |
| [Integrals.lean](Integrals.lean) | `laguerrePolynomialL_convolution` | proved |
| [Integrals.lean](Integrals.lean) | `hermitePolynomialH_convolution` | proved |
| [Integrals.lean](Integrals.lean) | `hermitePolynomialH_triple_integral` | proved |
| [Integrals.lean](Integrals.lean) | `jacobi_weighted_integral` | proved |
| [Integrals.lean](Integrals.lean) | `laguerrePolynomialL_unweighted_convolution` | proved |
| [Integrals.lean](Integrals.lean) | `ultrasphericalPolynomial_product_integral` | `sorry` |
| [Integrals.lean](Integrals.lean) | `jacobi_fractional_integral` | proved |
| [Integrals.lean](Integrals.lean) | `ultrasphericalPolynomial_fourier_transform` | proved |
| [Integrals.lean](Integrals.lean) | `legendre_bessel_square_integral` | `sorry` |
| [Integrals.lean](Integrals.lean) | `hermite_fourier_eigenfunction` | proved |
| [Integrals.lean](Integrals.lean) | `hermite_even_cosine_transform` | proved |
| [Integrals.lean](Integrals.lean) | `hermite_odd_sine_transform` | proved |
| [Integrals.lean](Integrals.lean) | `hermite_product_cosine_transform` | proved |
| [Integrals.lean](Integrals.lean) | `hermite_product_sine_transform` | proved |
| [Integrals.lean](Integrals.lean) | `jacobi_laplace_transform` | proved |
| [Integrals.lean](Integrals.lean) | `laguerrePolynomialL_product_laplace_transform` | `sorry` |
| [Integrals.lean](Integrals.lean) | `hermite_mellin_laplace_transform` | proved |
| [Integrals.lean](Integrals.lean) | `ultrasphericalPolynomial_dirichlet_integral` | `sorry` |
| [Integrals.lean](Integrals.lean) | `jacobi_double_laplace_integral` | `sorry` |
| [Integrals.lean](Integrals.lean) | `laguerrePolynomialL_double_laplace_integral` | `sorry` |
| [Integrals.lean](Integrals.lean) | `laguerrePolynomialL_bessel_integral` | `sorry` |
| [Integrals.lean](Integrals.lean) | `jacobi_fourier_transform` | proved |
| [Integrals.lean](Integrals.lean) | `ultrasphericalPolynomial_even_cosine_transform` | proved |
| [Integrals.lean](Integrals.lean) | `ultrasphericalPolynomial_odd_sine_transform` | proved |
| [Integrals.lean](Integrals.lean) | `legendre_fourier_transform` | proved |
| [Integrals.lean](Integrals.lean) | `laguerrePolynomialL_laplace_transform` | proved |
| [Integrals.lean](Integrals.lean) | `ultrasphericalPolynomial_mellin_transform` | proved |
| [Integrals.lean](Integrals.lean) | `laguerrePolynomialL_mellin_laplace_transform` | proved |
| [Limits.lean](Limits.lean) | `jacobi_limit_alpha` | proved |
| [Limits.lean](Limits.lean) | `jacobi_limit_beta` | proved |
| [Limits.lean](Limits.lean) | `ultrasphericalPolynomial_limit_monomial` | proved |
| [Limits.lean](Limits.lean) | `laguerrePolynomialL_limit_monomial` | proved |
| [Limits.lean](Limits.lean) | `jacobi_limit_laguerrePolynomialL` | proved |
| [Limits.lean](Limits.lean) | `jacobi_limit_laguerrePolynomialL_reflected` | proved |
| [Limits.lean](Limits.lean) | `jacobi_limit_hermite` | proved |
| [Limits.lean](Limits.lean) | `ultrasphericalPolynomial_limit_hermite` | proved |
| [Limits.lean](Limits.lean) | `ultrasphericalPolynomial_limit_chebyshev` | proved |
| [Limits.lean](Limits.lean) | `laguerrePolynomialL_limit_hermite` | proved |
| [Limits.lean](Limits.lean) | `jacobi_mehler_heine` | `sorry` |
| [Limits.lean](Limits.lean) | `laguerrePolynomialL_mehler_heine` | `sorry` |
| [Limits.lean](Limits.lean) | `hermite_even_mehler_heine` | `sorry` |
| [Limits.lean](Limits.lean) | `hermite_odd_mehler_heine` | `sorry` |
| [Multivariate.lean](Multivariate.lean) | `diskPolynomial` | definition |
| [Multivariate.lean](Multivariate.lean) | `trianglePolynomial` | definition |
| [Multivariate.lean](Multivariate.lean) | `diskPolynomial_polar` | `sorry` |
| [Multivariate.lean](Multivariate.lean) | `diskPolynomial_at_one` | proved |
| [Multivariate.lean](Multivariate.lean) | `diskPolynomial_orthogonal` | `sorry` |
| [Multivariate.lean](Multivariate.lean) | `trianglePolynomial_orthogonal` | `sorry` |
| [QFamilies.lean](QFamilies.lean) | `terminatingBasicHypergeometric` | definition |
| [QFamilies.lean](QFamilies.lean) | `qHahn` | definition |
| [QFamilies.lean](QFamilies.lean) | `bigQJacobi` | definition |
| [QFamilies.lean](QFamilies.lean) | `littleQJacobi` | definition |
| [QFamilies.lean](QFamilies.lean) | `littleQLaguerre` | definition |
| [QFamilies.lean](QFamilies.lean) | `qLaguerre` | definition |
| [QFamilies.lean](QFamilies.lean) | `stieltjesWigert` | definition |
| [QFamilies.lean](QFamilies.lean) | `discreteQHermiteI` | definition |
| [QFamilies.lean](QFamilies.lean) | `discreteQHermiteII` | definition |
| [QFamilies.lean](QFamilies.lean) | `askeyWilson` | definition |
| [QFamilies.lean](QFamilies.lean) | `askeyWilsonLaurent` | definition |
| [QFamilies.lean](QFamilies.lean) | `alSalamChihara` | definition |
| [QFamilies.lean](QFamilies.lean) | `continuousQHermiteLaurent` | definition |
| [QFamilies.lean](QFamilies.lean) | `qRacah` | definition |
| [QFamilies.lean](QFamilies.lean) | `qHahn_orthogonal` | `sorry` |
| [QFamilies.lean](QFamilies.lean) | `littleQJacobi_orthogonal` | `sorry` |
| [QFamilies.lean](QFamilies.lean) | `qLaguerre_orthogonal` | `sorry` |
| [QFamilies.lean](QFamilies.lean) | `stieltjesWigert_orthogonal` | `sorry` |
| [QFamilies.lean](QFamilies.lean) | `askeyWilson_laurent_representation` | proved |
| [QFamilies.lean](QFamilies.lean) | `askeyWilson_orthogonal` | `sorry` |
| [QFamilies.lean](QFamilies.lean) | `qGegenbauer_orthogonal` | `sorry` |
| [QFamilies.lean](QFamilies.lean) | `continuousQHermite_orthogonality` | `sorry` |
| [QFamilies.lean](QFamilies.lean) | `qRacah_duality` | proved |
| [QFamilies.lean](QFamilies.lean) | `qHahn_limit_hahn` | proved |
| [QFamilies.lean](QFamilies.lean) | `littleQJacobi_limit_jacobi` | proved |
| [QFamilies.lean](QFamilies.lean) | `littleQLaguerre_limit_laguerrePolynomialL` | proved |
| [QFamilies.lean](QFamilies.lean) | `qLaguerre_limit_laguerrePolynomialL` | proved |
| [QFamilies.lean](QFamilies.lean) | `askeyWilson_limit_wilson` | proved |
| [QFamilies.lean](QFamilies.lean) | `qGegenbauer_limit_ultrasphericalPolynomial` | proved |
| [QFamilies.lean](QFamilies.lean) | `discreteQHermiteI_limit_hermite` | proved |
| [QFamilies.lean](QFamilies.lean) | `discreteQHermiteII_limit_hermite` | proved |
| [QFamilies.lean](QFamilies.lean) | `askeyWilsonDifferenceCoefficient` | definition |
| [QFamilies.lean](QFamilies.lean) | `askeyWilson_difference_equation` | `sorry` |
| [QFamilies.lean](QFamilies.lean) | `askeyWilsonAsymptoticCoefficient` | definition |
| [QFamilies.lean](QFamilies.lean) | `askeyWilson_asymptotic` | `sorry` |
| [Series.lean](Series.lean) | `jacobi_generating_function` | `sorry` |
| [Series.lean](Series.lean) | `ultrasphericalPolynomial_generating_function` | proved |
| [Series.lean](Series.lean) | `ultrasphericalPolynomial_weighted_generating_function` | proved |
| [Series.lean](Series.lean) | `chebyshevT_generating_function` | proved |
| [Series.lean](Series.lean) | `chebyshevT_log_generating_function` | proved |
| [Series.lean](Series.lean) | `chebyshevU_generating_function` | proved |
| [Series.lean](Series.lean) | `legendre_generating_function` | proved |
| [Legendre.lean](Legendre.lean) | `legendre_exponential_generating_function` | proved |
| [Series.lean](Series.lean) | `hermite_generating_function` | proved |
| [Series.lean](Series.lean) | `laguerrePolynomialL_addition` | proved |
| [Series.lean](Series.lean) | `hermitePolynomialH_addition` | proved |
| [Series.lean](Series.lean) | `laguerrePolynomialL_multiplication` | proved |
| [Series.lean](Series.lean) | `hermitePolynomialH_multiplication` | proved |
| [Series.lean](Series.lean) | `ultrasphericalPolynomial_connection` | `sorry` |
| [Series.lean](Series.lean) | `monomial_ultrasphericalPolynomial_expansion` | `sorry` |
| [Series.lean](Series.lean) | `laguerrePolynomialL_connection` | proved |
| [Series.lean](Series.lean) | `monomial_laguerrePolynomialL_expansion` | proved |
| [Series.lean](Series.lean) | `monomial_hermitePolynomialH_expansion` | proved |
| [Series.lean](Series.lean) | `hermitePolynomialH_linearization` | proved |
| [Series.lean](Series.lean) | `mehler_formula` | `sorry` |
| [Series.lean](Series.lean) | `legendre_addition` | `sorry` |
| [Series.lean](Series.lean) | `ultrasphericalPolynomial_linearization` | `sorry` |
| [GegenbauerSeries.lean](GegenbauerSeries.lean) | `ultrasphericalPolynomial_finite_sum` | proved |
| [GegenbauerSeries.lean](GegenbauerSeries.lean) | `ultrasphericalPolynomial_cos_sum` | proved |
| [Series.lean](Series.lean) | `ultrasphericalPolynomial_convolution` | proved |
| [Series.lean](Series.lean) | `ultrasphericalPolynomial_geometric_convolution` | proved |
| [Series.lean](Series.lean) | `chebyshev_geometric_sum` | proved |
| [Series.lean](Series.lean) | `chebyshevT_even_sum` | proved |
| [Series.lean](Series.lean) | `chebyshevT_odd_sum` | proved |
| [Series.lean](Series.lean) | `chebyshevU_even_sum` | proved |
| [Series.lean](Series.lean) | `chebyshevU_odd_sum` | proved |
| [Series.lean](Series.lean) | `legendre_convolution` | proved |
| [Series.lean](Series.lean) | `laguerrePolynomialL_sum` | proved |
| [Series.lean](Series.lean) | `hermitePolynomialH_even_convolution` | proved |
| [Series.lean](Series.lean) | `jacobi_regularized_generating_function` | proved |
| [Series.lean](Series.lean) | `jacobi_brafman_generating_function` | `sorry` |
| [Series.lean](Series.lean) | `jacobi_weighted_generating_function` | `sorry` |
| [Series.lean](Series.lean) | `jacobi_adjacent_generating_function` | `sorry` |
| [Legendre.lean](Legendre.lean) | `ultrasphericalPolynomial_bessel_generating_function` | proved |
| [Series.lean](Series.lean) | `chebyshevT_poisson_generating_function` | proved |
| [Series.lean](Series.lean) | `laguerrePolynomialL_bessel_generating_function` | proved |
| [Series.lean](Series.lean) | `hermitePolynomialH_half_factorial_generating_function` | proved |
| [UnitCircle.lean](UnitCircle.lean) | `reflectedPolynomial` | definition |
| [UnitCircle.lean](UnitCircle.lean) | `IsUnitCircleOP` | definition |
| [UnitCircle.lean](UnitCircle.lean) | `verblunskyCoefficient` | definition |
| [UnitCircle.lean](UnitCircle.lean) | `szegoAskey` | definition |
| [UnitCircle.lean](UnitCircle.lean) | `szegoAskeyQ` | definition |
| [UnitCircle.lean](UnitCircle.lean) | `szego_recurrence` | proved |
| [UnitCircle.lean](UnitCircle.lean) | `szego_reflected_recurrence` | proved |
| [UnitCircle.lean](UnitCircle.lean) | `verblunskyCoefficient_norm_lt_one` | proved |
| [UnitCircle.lean](UnitCircle.lean) | `unitCircle_norm_ratio` | proved |
| [UnitCircle.lean](UnitCircle.lean) | `inverse_szego_recurrence` | proved |
| [UnitCircle.lean](UnitCircle.lean) | `inverse_reflected_szego_recurrence` | proved |
| [UnitCircle.lean](UnitCircle.lean) | `unitCircle_three_term_recurrence` | proved |
| [UnitCircle.lean](UnitCircle.lean) | `verblunsky_theorem` | `sorry` |
| [UnitCircle.lean](UnitCircle.lean) | `szegoAskey_orthogonal` | `sorry` |
| [UnitCircle.lean](UnitCircle.lean) | `szegoAskeyQ_orthogonal` | `sorry` |
| [Wilson.lean](Wilson.lean) | `wilson` | definition |
| [Wilson.lean](Wilson.lean) | `continuousDualHahn` | definition |
| [Wilson.lean](Wilson.lean) | `racah` | definition |
| [Wilson.lean](Wilson.lean) | `dualHahn` | definition |
| [Wilson.lean](Wilson.lean) | `wilson_hypergeometric` | proved |
| [Wilson.lean](Wilson.lean) | `continuousDualHahn_hypergeometric` | proved |
| [Wilson.lean](Wilson.lean) | `racah_hypergeometric` | proved |
| [Wilson.lean](Wilson.lean) | `dualHahn_hypergeometric` | proved |
| [Wilson.lean](Wilson.lean) | `dualHahn_hahn_duality` | proved |
| [Wilson.lean](Wilson.lean) | `racah_duality` | proved |
| [Wilson.lean](Wilson.lean) | `wilson_orthogonal` | `sorry` |
| [Wilson.lean](Wilson.lean) | `continuousDualHahn_orthogonality` | `sorry` |
| [Wilson.lean](Wilson.lean) | `wilson_limit_continuousDualHahn` | proved |
| [Wilson.lean](Wilson.lean) | `racah_limit_dualHahn` | proved |
| [Wilson.lean](Wilson.lean) | `racah_limit_hahn` | proved |
| [Wilson.lean](Wilson.lean) | `wilson_central_difference` | proved |
| [Wilson.lean](Wilson.lean) | `continuousDualHahn_central_difference` | proved |
| [Wilson.lean](Wilson.lean) | `wilson_generating_function` | `sorry` |
| [Wilson.lean](Wilson.lean) | `continuousDualHahn_generating_function` | `sorry` |

## Pre-existing admissions retained

- `favard` in `General.lean` (`orthogonal_polynomials_parseval` has since been proved).
- `jacobiPolynomialP_connection`, `vietoris_inequality`, `ultrasphericalPolynomial_cesaro_nonneg`, and `irrational_riemannZeta_three` in `Topics.lean`.

## Acquisition validation (before subsequent proof work)

- `lake build > /tmp/DLMF-build.log 2>&1`: passed, 3788 jobs.
- `lake env lean f.lean`: passed for all 20 changed Lean files (the 18 files in this directory, the chapter aggregate, and `DLMF/QSeries/Identities.lean`). Expected admission warnings remain.
- `git diff --check`: passed. Since these working files are untracked, a separate trailing-whitespace scan was also run on all changed Lean files; it passed.
- `rg -n '\bsorry\b' AAR --glob '*.lean'`: 334 admissions in the orthogonal-polynomial directory and 482 across `AAR`; the new modules account for 327.
- Snapshot comparisons confirm that `General.lean`, `Classical.lean`, `Topics.lean`, and `QSeries/Identities.lean` retain their original statements and proofs, with only attributes/whitespace differing. The aggregate changes are imports and documentation.
- All 329 new theorems have DLMF attributes. No axioms or proof escape mechanisms were added. `Scratch.lean` is absent, and the original `.lake` symlink is unchanged.

Direct-check logs and the complete admission listing are in `/tmp/aar-dlmf18/`; the source/declaration inventory above is retained in the project.
