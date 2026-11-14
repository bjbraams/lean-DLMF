# LaoLaksh Chapter1 acquisition ledger

All **19** entries and their distinct subclaims are audited in lookup order Mathlib,
TauCeti, DLMF. Pins: Mathlib `1b1ccf4b088b32fa3f23f2de1127433254a81e1e`, TauCeti
`396c3bd971e9722aa8656231760e710fe641d8cf`, Lean `v4.36.0-rc2`. The source synopsis,
pins and existing definition bodies are unchanged. “Existing” does not imply proved;
the transitive Lean axiom audit below distinguishes proofs, admissions and dependence on
admissions. Newly admitted statements remain in the theorem layer; defining APIs are proved.

## RL-1.01 — Rising factorial and gamma bridge (1.4, 1.16–1.17, pp. 1-1, 1-4).

Mathlib `Complex.Gamma_add_nat_div_Gamma_eq` gives the exact all-nonpole Gamma quotient; no
unnecessary positive-real-part restriction is used. The project's canonical
`DLMF.Hypergeometric.pochhammer`, `DLMF.Hypergeometric.pochhammer_zero`,
`DLMF.Hypergeometric.pochhammer_succ`, `DLMF.Hypergeometric.pochhammer_neg_coe_nat`, and
`DLMF.Hypergeometric.pochhammer_neg_nat_eq_zero` give all elementary identities and finite
termination. The descending-factorial quotient for k<=N follows from its factorial formula, while
the Pochhammer identity remains polynomial even at exceptional parameters. Existing
`Complex.Gamma_nat_eq_factorial` gives Gamma(n+1)=n!.

Checked named coverage: 7 declarations; 0 depend on admissions.

## RL-1.02 — Generalized and Gauss series (1.5–1.9, pp. 1-2–1-3).

Canonical `DLMF.Hypergeometric.pochhammerProduct`,
`DLMF.Hypergeometric.generalizedHypergeometricCoeff`,
`DLMF.Hypergeometric.generalizedHypergeometricSeries`,
`DLMF.Hypergeometric.generalizedHypergeometric`, and
`DLMF.Hypergeometric.generalizedHypergeometric_hasSum_disk` give the series with its convergence
domain and principal continuation distinguished. Upper/lower lists are multisets, so permutation
invariance is definitional. `DLMF.Hypergeometric.generalizedHypergeometricTruncated` is the actual
retained finite sum and permits lower exceptions after termination;
`DLMF.Hypergeometric.generalizedHypergeometric_eq_finite` identifies it with the regular-parameter
function. Ordinary Gauss uses `ordinaryHypergeometric` on the series disk, and
`Gamma(c)*regularizedGaussHypergeometric` for its continued principal function. A totalized
divergent series is never identified with its continuation outside the disk.

Checked named coverage: 8 declarations; 0 depend on admissions.

## RL-1.03 — Convergence (1.23–1.25, pp. 1-5–1-6).

Existing `DLMF.Hypergeometric.generalizedHypergeometric_radius_one`,
`DLMF.Hypergeometric.generalizedHypergeometric_radius_zero`,
`DLMF.Hypergeometric.generalizedHypergeometric_hasSum_entire`,
`DLMF.Hypergeometric.generalizedHypergeometric_unit_absolute_iff`,
`DLMF.Hypergeometric.generalizedHypergeometric_unit_conditional`, and
`DLMF.Hypergeometric.generalizedHypergeometric_one_converges_iff` give every radius, absolute
endpoint and conditional unit-circle claim. Specialize to upper multiset {a,b}, lower {c} for
Gauss. Their nontermination and regular-lower predicates are necessary and retained. Conditional
convergence is `DLMF.Hypergeometric.HypergeometricSeriesConvergesTo`, a limit of natural finite
partial sums; it is not the unconditional HasSum predicate.

Checked named coverage: 7 declarations; 0 depend on admissions.

## RL-1.04 — Finite Horner evaluation (1.10–1.13, pp. 1-3–1-4).

TauCeti `TauCeti.Polynomial.eval₂_ofCoeffList_reverse` is the exact generic finite Horner
evaluator. The ratio form is its elementary backward-induction adapter: assuming c0=1 and
c(k+1)=r(k)c(k), multiply Hk=1+r(k)zH(k+1) by c(k). Starting with c(N)H(N)=c(N), backward
induction gives c(k)H(k)=sum_{j=k}^N c(j)z^(j-k), hence the source identity at k=0. No division by
c(k) is needed, so vanishing intermediate coefficients are allowed. For Gauss, the defining
consecutive-coefficient recurrence supplies r(k) under precisely the finite nonzero denominator
conditions through the retained degree; lower exceptions after termination do not invalidate this
finite computation.

Checked named coverage: 1 declarations; 0 depend on admissions.

## RL-1.05 — Chu–Vandermonde and Gauss sum (1.15, 1.18, pp. 1-4–1-6).

Existing `DLMF.Hypergeometric.sum_pochhammer_mul_neg_nat_div` gives Chu-Vandermonde with exactly
the finite denominator hypothesis: every (c)_k is nonzero for k<=N, with no global exclusion of
later lower poles. `DLMF.Hypergeometric.generalizedHypergeometricTruncated` supplies the
finite-function convention. Existing `DLMF.Hypergeometric.gauss_summation` gives Gauss on c
outside nonpositive integers and Re(c-a-b)>0. Its denominator Gamma factors are totalized
reciprocals, which correctly retain zeros at their poles; no extra regularity of c-a,c-b is
imposed. `DLMF.Hypergeometric.hasSum_regularizedGauss_one` additionally states the entire
regularized version, including exceptional c. These were already acquired; no new finite-parameter
exclusion is introduced.

Checked named coverage: 4 declarations; 1 depend on admissions.

## RL-1.06 — Euler beta and hypergeometric integrals (1.19–1.28, pp. 1-5–1-6).

Mathlib `Complex.betaIntegral`, `Complex.betaIntegral_convergent`, and
`Complex.Gamma_mul_Gamma_eq_betaIntegral` give the full complex beta integral. Gamma(s+t) is
nonzero because Re(s+t)>0, so its division yields exactly B(u,v). The full-principal-domain Euler
representation is existing
`DLMF.Hypergeometric.regularizedGaussHypergeometric_eq_regularizedGaussHypergeometricIntegral`,
together with `DLMF.Hypergeometric.regularizedGaussHypergeometricIntegral`,
`DLMF.Hypergeometric.eulerKernel`, and `DLMF.Hypergeometric.intervalIntegrable_eulerKernel`.
Multiplying by Gamma(c) and the beta identity gives the source ordinary normalization. This covers
every complex a and z in the complement of [1,infinity) under Re c>Re b>0; the older
ordinaryHypergeometric_eq_integral only states the unit-disk form.

Checked named coverage: 7 declarations; 0 depend on admissions.

## RL-1.07 — Gauss differential equation (1.29, pp. 1-6–1-7).

Existing `DLMF.Hypergeometric.ordinaryHypergeometric_ode` gives the Gauss equation on its initial
series disk. Existing `DLMF.Hypergeometric.regularizedGaussHypergeometric_ode`, multiplied by
Gamma(c), gives the entire principal cut domain; the canonical regularized continuation retains
parameter exceptions separately. `DLMF.Hypergeometric.eq_ordinaryHypergeometric_of_gaussOperator`
gives the unique analytic-at-zero solution normalized by value one for regular c. At zero the
equation determines the derivative through c*y'(0)=ab, so a second free initial datum is not
inserted into this singular initial-value normalization.

Checked named coverage: 3 declarations; 0 depend on admissions.

## RL-1.08 — Regular singularity and Frobenius recurrence (1.35–1.48, pp. 1-7–1-9).

Existing `Complex.LinearODEAtMostRegularAt` gives precisely the two weighted analytic extensions
for n=2; `Complex.LinearODERegularSingularAt` additionally excludes ordinary points. The source
describes the at-most-regular criterion, so this distinction is retained. Canonical
`DLMF.AsymptoticApproximations.indicialPoly` and `DLMF.AsymptoticApproximations.frobeniusCoeff`
give the indicial polynomial and recurrence. Generic
`PowerSeries.indicial_eq_zero_of_formal_frobenius` and `PowerSeries.coeff_formal_frobenius` give
the exact algebraic coefficient identities without nonresonance assumptions. Existing
`DLMF.AsymptoticApproximations.summable_frobeniusCoeff_of_nonresonant`,
`DLMF.AsymptoticApproximations.analyticOnNhd_frobeniusAnalyticFactor`, and
`DLMF.AsymptoticApproximations.frobeniusAnalyticFactor_exp_log_isLinearODE2SolutionOn` give
convergence and a genuine local solution for any specified analytic logarithm branch, under
exactly the shifted-indicial nonzero conditions. Existing
`DLMF.Hypergeometric.riemannNormalOperator_gauss` identifies the complete exponent pairs
(0,1-c),(0,c-a-b),(a,b); substituting them into the indicial quadratic gives those roots directly,
and `DLMF.Hypergeometric.gauss_fuchs_relation` verifies their sum.

Checked named coverage: 11 declarations; 5 depend on admissions.

## RL-1.09 — Nonresonant bases (1.58–1.80, pp. 1-10–1-13).

Existing `DLMF.Hypergeometric.zeroSecond`, `DLMF.Hypergeometric.oneFirst`,
`DLMF.Hypergeometric.oneSecond`, `DLMF.Hypergeometric.infinityFirst`,
`DLMF.Hypergeometric.zero_second_ode`, `DLMF.Hypergeometric.one_first_ode`,
`DLMF.Hypergeometric.one_second_ode`, and `DLMF.Hypergeometric.infinity_first_ode` give exactly
the source six local solutions. `DLMF.Hypergeometric.zero_wronskian` and
`DLMF.Hypergeometric.one_wronskian` cover the full corresponding complex slit disks; their
nonresonance assumptions make both power factors and the coefficient nonzero. New
`DLMF.Hypergeometric.infinity_wronskian_slit` fills the remaining genuine domain gap: the full
slit exterior |z|>1 replaces the earlier Re z>1 Wronskian restriction. Nonintegral a-b makes it
nonzero. Proved `DLMF.AlgebraicAnalytic.isFundamentalPair_of_wronskian_ne_zero` then gives every
complex analytic solution as a constant linear combination; evaluating value and derivative at one
point makes those constants unique by the nonzero determinant. Other coherent local logarithms
multiply the two powers by nonzero constants, preserving the basis. Real-interval-only
solution-space results are not used as full complex-germ coverage.

Checked named coverage: 12 declarations; 1 depend on admissions.

## RL-1.10 — Euler/Pfaff transformations (1.30–1.32, pp. 1-6–1-7).

Existing `DLMF.Hypergeometric.regularizedGaussHypergeometric_euler` and
`DLMF.Hypergeometric.regularizedGaussHypergeometric_pfaff` in ArgumentContinuation give the
complete principal cut-plane transformations for all complex parameters. Existing
`DLMF.Hypergeometric.regularizedGaussHypergeometric_symm` gives the second Pfaff form by swapping
a,b. Multiply by Gamma(c) on regular c to recover the book ordinary normalization. Their
cut-domain hypothesis includes every real z<1 and the fractional-linear transformed argument
remains in the same cut domain. The earlier Euler-integral/unit-disk transformation lemmas alone
have stronger hypotheses and were not used as full source coverage.

Checked named coverage: 3 declarations; 0 depend on admissions.

## RL-1.11 — Confluence (1.88–1.94, pp. 1-15–1-16).

Existing `DLMF.Confluent.kummerM`, `DLMF.Confluent.hasSum_kummerM`,
`DLMF.Confluent.analyticOnNhd_kummerM`, and `DLMF.Confluent.kummerM_ode` give the entire Kummer
series and equation. Shared acquisition
`DLMF.Confluent.tendstoLocallyUniformly_ordinaryHypergeometric_add_div_atTop`, with d=0, is
exactly Gauss-to-Kummer convergence locally uniformly in the complex argument. Fixed complex
shifts of the large parameter are additionally allowed. Pointwise convergence of coefficients is
not treated as a convergence proof for the functions.

Checked named coverage: 5 declarations; 1 depend on admissions.

## RL-1.12 — Bell's labelled Theorem, parts 1–2 (pp. 1-17–1-18).

Existing `DLMF.OrthogonalPolynomials.legendrePolynomialP` and `DLMF.Legendre.legendreP_nat` give
the terminating Gauss Legendre polynomial. Existing `DLMF.Legendre.iteratedDeriv_legendreP`,
specialized to nu=n and natural m<=n, gives the derivative as (-1/2)^m(-n)_m(n+1)_m times the
regularized Gauss function at lower m+1. Convert (-n)_m and (n+1)_m by the finite factorial
formulas and use Gamma(m+1)=m! to obtain exactly the coefficient (n+m)!/((n-m)!2^m m!) and upper
parameters m-n,m+n+1. Multiplying by the positive (1-x^2)^(m/2) is the source sign-free associated
polynomial. `DLMF.Legendre.ferrersP_nat` or `DLMF.Legendre.ferrersP_nat_order_rodrigues`
identifies it with (-1)^m times the canonical Condon-Shortley Ferrers function on (-1,1); that
phase is not silently dropped. This is an elementary exact derivative specialization, not an
additional admission.

Checked named coverage: 5 declarations; 0 depend on admissions.

## RL-1.13 — Bell's Theorem, part 3 (p. 1-17).

Existing proved `DLMF.Bessel.besselJ_eq_kummerM` is already the complete complex-argument
representation without a nonzero-z or slit-plane restriction. Natural orders satisfy both
denominator regularity hypotheses, Gamma(n+1)=n!, and the principal natural power is the ordinary
integer power. It therefore covers every real x, including zero and negative x. The canonical
regularized Bessel series supplies the source normalization; no duplicate real Bessel definition
is introduced.

Checked named coverage: 1 declarations; 0 depend on admissions.

## RL-1.14 — Bell's Theorem, part 4 (p. 1-17).

Existing proved `DLMF.Confluent.hermitePolynomialHEval_even_mul` and
`DLMF.Confluent.hermitePolynomialHEval_odd_mul` in Relations are precisely the even and odd Kummer
identities after multiplying by n!. Both already hold for every complex x, including x=0, and
division only by nonzero n! yields the source formulas. The later kummerM_hermite_odd lemma
divides by x and is therefore a less suitable pointer. The physicists normalization is canonical
`DLMF.OrthogonalPolynomials.hermitePolynomialH`, with its derivative recurrence and Gaussian
Rodrigues API; it is distinct from probabilists' Hermite.

Checked named coverage: 3 declarations; 0 depend on admissions.

## RL-1.15 — Bell's Theorem, part 5 (p. 1-17).

The canonical `DLMF.OrthogonalPolynomials.laguerrePolynomialL` is definitionally (alpha+1)_n/n!
times M(-n,alpha+1,x), exactly the corrected associated formula on alpha>-1. Set alpha=0 and use
`DLMF.Hypergeometric.pochhammer_nat_one` to cancel n! for the ordinary Laguerre form. The
exceptional-parameter polynomial continuation is separately
`DLMF.OrthogonalPolynomials.laguerreExtended`, with its regular-parameter bridge; it is not needed
to weaken the source's alpha>-1 condition. No mistaken associated lower parameter 1 is retained.

Checked named coverage: 3 declarations; 0 depend on admissions.

## RL-1.16 — Bell's Theorem, part 6 (p. 1-17).

Existing `DLMF.OrthogonalPolynomials.chebyshevT_hypergeometric` is the exact terminating T
formula. Existing `DLMF.OrthogonalPolynomials.eval_U_eq_ultrasphericalPolynomial` and
`DLMF.OrthogonalPolynomials.ultrasphericalPolynomial_param_one_eq` give the corrected U prefactor
n+1 and lower parameter 3/2. Mathlib `Polynomial.Chebyshev.T_real_cos` and
`Polynomial.Chebyshev.U_real_cos` give both trigonometric normalizations for every real angle,
including sine-zero endpoints in the multiplied U identity. Thus the printed nonstandard
second-kind formula is not formalized.

Checked named coverage: 5 declarations; 0 depend on admissions.

## RL-1.17 — Bell's Theorem, parts 7–8 (p. 1-18).

Canonical `DLMF.OrthogonalPolynomials.ultrasphericalPolynomial` and
`DLMF.OrthogonalPolynomials.jacobiPolynomialP` are exactly the two corrected hypergeometric
definitions. The source real parameter ranges ensure every ordinary lower denominator is regular;
the explicitly excluded lambda=0 is retained in the source convention. The Pochhammer prefactors,
argument (1-x)/2 and Jacobi upper parameter n+alpha+beta+1 match the source as corrected in the
synopsis. No nonstandard Jacobi prefactor or argument is copied from the printed error.

Checked named coverage: 2 declarations; 0 depend on admissions.

## RL-1.18 — Elementary degenerations and limits (1.108–1.124, pp. 1-20–1-23).

Existing `DLMF.Confluent.kummerM_self` gives M(a,a,z)=exp z on regular a. Existing
`DLMF.Hypergeometric.sum_pochhammer_neg_nat_div_factorial_mul_pow`, with the canonical terminating
coefficient formula, gives F(-n,b;b,z)=(1-z)^n under regular b, or nonzero (b)_k for every k<=n.
Existing `DLMF.Hypergeometric.mul_regularizedGaussHypergeometric_one_one_two` gives the full real
x>-1 logarithm after z=-x; Gamma(2)=1. Existing
`DLMF.Hypergeometric.arcsin_eq_ordinaryHypergeometric` gives the stated arcsine domain, and
`DLMF.Hypergeometric.arctan_eq_regularizedGaussHypergeometric` gives all real x. The exponential
limit follows by the existing local uniform Gauss-to-Kummer theorem with c=a and kummerM_self. The
two large-equal-upper-parameter limits follow from
`DLMF.Confluent.tendstoLocallyUniformly_ordinaryHypergeometric_sqrt_div_atTop` with t=A^2, scales
both one and argument -x^2/4; `DLMF.Bessel.regularized0F1_half_eq_cos` and
`DLMF.Bessel.regularized0F1_three_halves_eq_sinc` identify the limits after Gamma normalization.
For sine, x=0 is checked separately rather than dividing by zero. No equality outside a
defining-series disk is justified by its totalized sum.

Checked named coverage: 8 declarations; 3 depend on admissions.

## RL-1.19 — Function-to-equation substitution (1.125–1.128, pp. 1-24–1-25).

Existing proved `DLMF.OrthogonalPolynomials.legendre_differential_equation` and
`DLMF.OrthogonalPolynomials.laguerrePolynomialL_differential_equation` at alpha=0 are exactly the
two substituted equations for every complex argument. Their proofs already perform the
Gauss/Kummer substitutions and the chain rule. The broad final programme about deriving all
special-function differential equations is excluded: source conjectural programme, not a theorem.
No unsupported universal equation-reduction assertion is admitted.

Checked named coverage: 2 declarations; 0 depend on admissions.

## Validation

All 19 entries are mapped. The transitive `#print axioms` audit checked **96** distinct
declarations; **11** depend on admissions. The **1** new modules
owned by this supplement contain **1** public declarations, including
**1** directly admitted targets. Definitions and their
defining equations have no admissions. Every new module has passed a direct strict Lean check
with `autoImplicit=false` and `relaxedAutoImplicit=false`; modules are registered in their
area umbrellas. Repository-wide build and import integration are coordinated with the other
book acquisitions and reported separately.

The per-entry declaration locations and proof statuses are retained in
[reports/BookAcquisition-LaoLaksh-Chapter1.tsv](reports/BookAcquisition-LaoLaksh-Chapter1.tsv). No additional
source erratum requiring user approval was identified in this supplement.

## Checked declaration index

- [Complex.Gamma_add_nat_div_Gamma_eq](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean#L481) — proved, no admission.
- [Complex.Gamma_mul_Gamma_eq_betaIntegral](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean#L124) — proved, no admission.
- [Complex.Gamma_nat_eq_factorial](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean#L325) — proved, no admission.
- [Complex.LinearODEAtMostRegularAt](DLMFMathlib/Analysis/ODE/Singularities.lean#L55) — definition, no admission.
- [Complex.LinearODERegularSingularAt](DLMFMathlib/Analysis/ODE/Singularities.lean#L60) — definition, no admission.
- [Complex.betaIntegral](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean#L60) — definition, no admission.
- [Complex.betaIntegral_convergent](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean#L78) — proved, no admission.
- [DLMF.AlgebraicAnalytic.isFundamentalPair_of_wronskian_ne_zero](DLMF/AlgebraicAnalytic/ODE/SecondOrder.lean#L244) — proved, no admission.
- [DLMF.AsymptoticApproximations.analyticOnNhd_frobeniusAnalyticFactor](DLMF/AsymptoticApproximations/ODE/Frobenius.lean#L65) — direct admission.
- [DLMF.AsymptoticApproximations.frobeniusAnalyticFactor_exp_log_isLinearODE2SolutionOn](DLMF/AsymptoticApproximations/ODE/Frobenius.lean#L93) — direct admission.
- [DLMF.AsymptoticApproximations.frobeniusCoeff](DLMF/AsymptoticApproximations/ODE/Basic.lean#L85) — definition, no admission.
- [DLMF.AsymptoticApproximations.indicialPoly](DLMF/AsymptoticApproximations/ODE/Basic.lean#L78) — definition, no admission.
- [DLMF.AsymptoticApproximations.summable_frobeniusCoeff_of_nonresonant](DLMF/AsymptoticApproximations/ODE/Frobenius.lean#L52) — direct admission.
- [DLMF.Bessel.besselJ_eq_kummerM](DLMF/Bessel/RegularizedSeries.lean#L366) — proved, no admission.
- [DLMF.Bessel.regularized0F1_half_eq_cos](DLMF/Bessel/RegularizedSeries.lean#L248) — proved, no admission.
- [DLMF.Bessel.regularized0F1_three_halves_eq_sinc](DLMF/Bessel/RegularizedSeries.lean#L209) — proved, no admission.
- [DLMF.Confluent.analyticOnNhd_kummerM](DLMF/Confluent/Basic/KummerProperties.lean#L139) — proved, no admission.
- [DLMF.Confluent.hasSum_kummerM](DLMF/Confluent/Basic/KummerContiguous.lean#L50) — proved, no admission.
- [DLMF.Confluent.hermitePolynomialHEval_even_mul](DLMF/Confluent/Relations.lean#L674) — proved, no admission.
- [DLMF.Confluent.hermitePolynomialHEval_odd_mul](DLMF/Confluent/Relations.lean#L719) — proved, no admission.
- [DLMF.Confluent.kummerM](DLMF/Confluent/Basic/KummerM.lean#L47) — definition, no admission.
- [DLMF.Confluent.kummerM_ode](DLMF/Confluent/Basic/KummerProperties.lean#L160) — proved, no admission.
- [DLMF.Confluent.kummerM_self](DLMF/Confluent/Basic/KummerProperties.lean#L57) — proved, no admission.
- [DLMF.Confluent.tendstoLocallyUniformly_ordinaryHypergeometric_add_div_atTop](DLMF/Confluent/ConfluenceUniform.lean#L29) — direct admission.
- [DLMF.Confluent.tendstoLocallyUniformly_ordinaryHypergeometric_sqrt_div_atTop](DLMF/Confluent/ConfluenceUniform.lean#L39) — direct admission.
- [DLMF.Hypergeometric.HypergeometricSeriesConvergesTo](DLMF/GeneralizedHypergeometric/Basic/ParametersAndSeries.lean#L70) — definition, no admission.
- [DLMF.Hypergeometric.arcsin_eq_ordinaryHypergeometric](DLMF/Hypergeometric/DiffEq.lean#L143) — proved, no admission.
- [DLMF.Hypergeometric.arctan_eq_regularizedGaussHypergeometric](DLMF/GeneralizedHypergeometric/BookSeries.lean#L49) — direct admission.
- [DLMF.Hypergeometric.eq_ordinaryHypergeometric_of_gaussOperator](DLMF/Hypergeometric/FurtherTransformations/Quadratic.lean#L362) — proved, no admission.
- [DLMF.Hypergeometric.eulerKernel](DLMF/Hypergeometric/Basic/PrincipalBranch.lean#L127) — definition, no admission.
- [DLMF.Hypergeometric.gauss_fuchs_relation](DLMF/Hypergeometric/Riemann.lean#L69) — proved, no admission.
- [DLMF.Hypergeometric.gauss_summation](DLMF/Hypergeometric/EulerIntegral.lean#L78) — proved, no admission.
- [DLMF.Hypergeometric.generalizedHypergeometric](DLMF/GeneralizedHypergeometric/Basic/PrincipalContinuation.lean#L56) — definition, no admission.
- [DLMF.Hypergeometric.generalizedHypergeometricCoeff](DLMF/GeneralizedHypergeometric/Basic/ParametersAndSeries.lean#L51) — definition, no admission.
- [DLMF.Hypergeometric.generalizedHypergeometricSeries](DLMF/GeneralizedHypergeometric/Basic/ParametersAndSeries.lean#L61) — definition, no admission.
- [DLMF.Hypergeometric.generalizedHypergeometricTruncated](DLMF/GeneralizedHypergeometric/Basic/ParametersAndSeries.lean#L65) — definition, no admission.
- [DLMF.Hypergeometric.generalizedHypergeometric_eq_finite](DLMF/GeneralizedHypergeometric/Basic/SeriesProperties.lean#L210) — proved, no admission.
- [DLMF.Hypergeometric.generalizedHypergeometric_hasSum_disk](DLMF/GeneralizedHypergeometric/Basic/SeriesProperties.lean#L146) — proved, no admission.
- [DLMF.Hypergeometric.generalizedHypergeometric_hasSum_entire](DLMF/GeneralizedHypergeometric/AnalyticProperties.lean#L74) — proved, no admission.
- [DLMF.Hypergeometric.generalizedHypergeometric_one_converges_iff](DLMF/GeneralizedHypergeometric/AnalyticProperties.lean#L942) — proved, no admission.
- [DLMF.Hypergeometric.generalizedHypergeometric_radius_one](DLMF/GeneralizedHypergeometric/AnalyticProperties.lean#L102) — proved, no admission.
- [DLMF.Hypergeometric.generalizedHypergeometric_radius_zero](DLMF/GeneralizedHypergeometric/AnalyticProperties.lean#L1036) — proved, no admission.
- [DLMF.Hypergeometric.generalizedHypergeometric_unit_absolute_iff](DLMF/GeneralizedHypergeometric/AnalyticProperties.lean#L299) — proved, no admission.
- [DLMF.Hypergeometric.generalizedHypergeometric_unit_conditional](DLMF/GeneralizedHypergeometric/AnalyticProperties.lean#L892) — proved, no admission.
- [DLMF.Hypergeometric.hasSum_regularizedGauss_one](DLMF/Hypergeometric/Boundary.lean#L58) — proved, no admission.
- [DLMF.Hypergeometric.infinityFirst](DLMF/Hypergeometric/Basic/GaussEquation.lean#L159) — definition, no admission.
- [DLMF.Hypergeometric.infinity_first_ode](DLMF/Hypergeometric/Basic/GaussEquation.lean#L359) — proved, no admission.
- [DLMF.Hypergeometric.infinity_wronskian_slit](DLMF/Hypergeometric/Solutions/InfinityWronskian.lean#L28) — direct admission.
- [DLMF.Hypergeometric.intervalIntegrable_eulerKernel](DLMF/Hypergeometric/Basic/CutPlane.lean#L201) — proved, no admission.
- [DLMF.Hypergeometric.mul_regularizedGaussHypergeometric_one_one_two](DLMF/GeneralizedHypergeometric/BookSeries.lean#L42) — direct admission.
- [DLMF.Hypergeometric.oneFirst](DLMF/Hypergeometric/Basic/GaussEquation.lean#L149) — definition, no admission.
- [DLMF.Hypergeometric.oneSecond](DLMF/Hypergeometric/Basic/GaussEquation.lean#L154) — definition, no admission.
- [DLMF.Hypergeometric.one_first_ode](DLMF/Hypergeometric/Basic/GaussEquation.lean#L266) — proved, no admission.
- [DLMF.Hypergeometric.one_second_ode](DLMF/Hypergeometric/Basic/GaussEquation.lean#L301) — proved, no admission.
- [DLMF.Hypergeometric.one_wronskian](DLMF/Hypergeometric/Basic/GaussEquation.lean#L494) — proved, no admission.
- [DLMF.Hypergeometric.ordinaryHypergeometric_ode](DLMF/Hypergeometric/Basic/GaussEquation.lean#L121) — proved, no admission.
- [DLMF.Hypergeometric.pochhammer](DLMF/Hypergeometric/Basic/Pochhammer.lean#L39) — definition, no admission.
- [DLMF.Hypergeometric.pochhammerProduct](DLMF/GeneralizedHypergeometric/Basic/ParametersAndSeries.lean#L44) — definition, no admission.
- [DLMF.Hypergeometric.pochhammer_nat_one](DLMF/Hypergeometric/Basic/Pochhammer.lean#L56) — proved, no admission.
- [DLMF.Hypergeometric.pochhammer_neg_coe_nat](DLMF/Hypergeometric/Basic/Pochhammer.lean#L141) — proved, no admission.
- [DLMF.Hypergeometric.pochhammer_neg_nat_eq_zero](DLMF/Hypergeometric/Basic/Pochhammer.lean#L158) — proved, no admission.
- [DLMF.Hypergeometric.pochhammer_succ](DLMF/Hypergeometric/Basic/Pochhammer.lean#L52) — proved, no admission.
- [DLMF.Hypergeometric.pochhammer_zero](DLMF/Hypergeometric/Basic/Pochhammer.lean#L44) — proved, no admission.
- [DLMF.Hypergeometric.regularizedGaussHypergeometricIntegral](DLMF/Hypergeometric/Basic/PrincipalBranch.lean#L137) — definition, no admission.
- [DLMF.Hypergeometric.regularizedGaussHypergeometric_eq_regularizedGaussHypergeometricIntegral](DLMF/Hypergeometric/Basic/CutPlane.lean#L457) — proved, no admission.
- [DLMF.Hypergeometric.regularizedGaussHypergeometric_euler](DLMF/Hypergeometric/ArgumentContinuation.lean#L231) — proved, no admission.
- [DLMF.Hypergeometric.regularizedGaussHypergeometric_ode](DLMF/Hypergeometric/Basic/CutPlane.lean#L536) — proved, no admission.
- [DLMF.Hypergeometric.regularizedGaussHypergeometric_pfaff](DLMF/Hypergeometric/ArgumentContinuation.lean#L266) — proved, no admission.
- [DLMF.Hypergeometric.regularizedGaussHypergeometric_symm](DLMF/Hypergeometric/Basic/CutPlane.lean#L475) — proved, no admission.
- [DLMF.Hypergeometric.riemannNormalOperator_gauss](DLMF/Hypergeometric/Riemann.lean#L74) — proved, no admission.
- [DLMF.Hypergeometric.sum_pochhammer_mul_neg_nat_div](DLMF/Hypergeometric/TerminatingSummations.lean#L27) — direct admission.
- [DLMF.Hypergeometric.sum_pochhammer_neg_nat_div_factorial_mul_pow](DLMF/Hypergeometric/Basic/Pochhammer.lean#L147) — proved, no admission.
- [DLMF.Hypergeometric.zeroSecond](DLMF/Hypergeometric/Basic/GaussEquation.lean#L144) — definition, no admission.
- [DLMF.Hypergeometric.zero_second_ode](DLMF/Hypergeometric/Basic/GaussEquation.lean#L227) — proved, no admission.
- [DLMF.Hypergeometric.zero_wronskian](DLMF/Hypergeometric/Basic/GaussEquation.lean#L397) — proved, no admission.
- [DLMF.Legendre.ferrersP_nat](DLMF/Legendre/Ferrers.lean#L37) — proved, no admission.
- [DLMF.Legendre.ferrersP_nat_order_rodrigues](DLMF/Legendre/IntegerTheory.lean#L147) — proved, no admission.
- [DLMF.Legendre.iteratedDeriv_legendreP](DLMF/Legendre/Recurrences.lean#L78) — proved, no admission.
- [DLMF.Legendre.legendreP_nat](DLMF/Legendre/FirstKindProperties.lean#L38) — proved, no admission.
- [DLMF.OrthogonalPolynomials.chebyshevT_hypergeometric](DLMF/OrthogonalPolynomials/Differential/ClassicalEquations.lean#L1017) — proved, no admission.
- [DLMF.OrthogonalPolynomials.eval_U_eq_ultrasphericalPolynomial](DLMF/OrthogonalPolynomials/Basic/Classical.lean#L433) — proved, no admission.
- [DLMF.OrthogonalPolynomials.hermitePolynomialH](DLMF/OrthogonalPolynomials/Basic/Definitions.lean#L56) — definition, no admission.
- [DLMF.OrthogonalPolynomials.jacobiPolynomialP](DLMF/OrthogonalPolynomials/Basic/Definitions.lean#L71) — definition, no admission.
- [DLMF.OrthogonalPolynomials.laguerreExtended](DLMF/OrthogonalPolynomials/Basic/Definitions.lean#L103) — definition, no admission.
- [DLMF.OrthogonalPolynomials.laguerrePolynomialL](DLMF/OrthogonalPolynomials/Basic/Definitions.lean#L64) — definition, no admission.
- [DLMF.OrthogonalPolynomials.laguerrePolynomialL_differential_equation](DLMF/OrthogonalPolynomials/Differential/ClassicalEquations.lean#L179) — proved, no admission.
- [DLMF.OrthogonalPolynomials.legendrePolynomialP](DLMF/OrthogonalPolynomials/Basic/Definitions.lean#L76) — definition, no admission.
- [DLMF.OrthogonalPolynomials.legendre_differential_equation](DLMF/OrthogonalPolynomials/Differential/ClassicalEquations.lean#L167) — proved, no admission.
- [DLMF.OrthogonalPolynomials.ultrasphericalPolynomial](DLMF/OrthogonalPolynomials/Basic/Definitions.lean#L83) — definition, no admission.
- [DLMF.OrthogonalPolynomials.ultrasphericalPolynomial_param_one_eq](DLMF/OrthogonalPolynomials/Basic/Classical.lean#L267) — proved, no admission.
- [Polynomial.Chebyshev.T_real_cos](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/Chebyshev/Basic.lean#L149) — proved, no admission.
- [Polynomial.Chebyshev.U_real_cos](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/Chebyshev/Basic.lean#L154) — proved, no admission.
- [PowerSeries.coeff_formal_frobenius](DLMFMathlib/Analysis/ODE/FormalSeries.lean#L49) — direct admission.
- [PowerSeries.indicial_eq_zero_of_formal_frobenius](DLMFMathlib/Analysis/ODE/FormalSeries.lean#L38) — direct admission.
- [TauCeti.Polynomial.eval₂_ofCoeffList_reverse](.lake/packages/TauCeti/TauCeti/Algebra/Polynomial/Coeff/List.lean#L79) — proved, no admission.
- [ordinaryHypergeometric](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/OrdinaryHypergeometric.lean#L81) — definition, no admission.

## Checked all-argument Hermite derivations

Both divisions use only the nonzero factorial n!, so zero arguments are included.

```lean
import DLMF.Confluent.Relations
open Complex DLMF.Confluent DLMF.OrthogonalPolynomials
example (n : ℕ) (z : ℂ) :
    hermitePolynomialHEval (2*n) z =
      ((-1 : ℂ)^n * (2*n).factorial * kummerM (-(n : ℂ)) (1/2) (z^2)) /
        (n.factorial : ℂ) := by
  apply (eq_div_iff (Nat.cast_ne_zero.mpr n.factorial_ne_zero)).2
  exact hermitePolynomialHEval_even_mul n z
example (n : ℕ) (z : ℂ) :
    hermitePolynomialHEval (2*n+1) z =
      ((-1 : ℂ)^n * (2*n+1).factorial * (2*z) * kummerM (-(n : ℂ)) (3/2) (z^2)) /
        (n.factorial : ℂ) := by
  apply (eq_div_iff (Nat.cast_ne_zero.mpr n.factorial_ne_zero)).2
  exact hermitePolynomialHEval_odd_mul n z
```
