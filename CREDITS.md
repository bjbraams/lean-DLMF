# Credits and related upstream work

The project formalizes material from Andrews, Askey and Roy, *Special Functions*
(1999), and the NIST Digital Library of Mathematical Functions, using Mathlib.
Existing module copyright and authorship notices remain authoritative.

## `ToMathlib` layer, now `DLMFMathlib` (2026-10-15)

`ToMathlib/Analysis/Integral/Laplace.lean` comes from the companion project `lean-codes`
(an unmodified copy until 2026-10-25; since then imported from the `LeanCodes` dependency). The Euler polynomials build on the Mathlib
contributors' `Polynomial.bernoulli` API and follow its recursive style; Euler–Maclaurin uses
`bernoulliFun` and its derivative from `Mathlib.NumberTheory.ZetaValues`, and both summation
formulas use Mathlib's interval integration by parts. Watson's lemma uses the Gamma integral
`Real.integral_rpow_mul_exp_neg_mul_Ioi` and `isLittleO_rpow_exp_pos_mul_atTop`. The proof
routes follow Temme, *Special Functions*, §§1.1–1.2 and Theorem 2.4.

## Carlson's theorem from lean-codes (2026-10-16)

`ToMathlib/Analysis/Complex/Carlson.lean` comes from the companion project `lean-codes` (an
unmodified copy until 2026-10-25; since then imported from the `LeanCodes` dependency). Its proof of Carlson's theorem follows Titchmarsh,
*The Theory of Functions*, §5.81, and rests on Mathlib's Phragmén–Lindelöf principle
(`PhragmenLindelof.eq_zero_on_right_half_plane_of_superexponential_decay`) and removable
singularities.

## Gamma pass from Temme (2026-10-15)

The proof routes for the Binet formulas, Prym's and the Cauchy–Saalschütz
representations, and Stirling's series with remainder follow N. M. Temme,
*Special Functions: An Introduction to the Classical Functions of Mathematical
Physics* (Wiley, 1996), §§3.2, 3.4 and 3.6. The `coth` partial fractions use the
Mathlib contributors' `cot_series_rep'` in
`Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent`; the zeta values use
`hasSum_zeta_nat` in `Mathlib.NumberTheory.ZetaValues`; Stirling's constant uses the
project's `tendsto_Gamma_nat_div_stirlingGamma`, built on Mathlib's `Stirling`.
No upstream theorem is admitted or copied.

## Legendre and Chebyshev pass from Temme (2026-10-15)

The proof routes follow Temme, *Special Functions*, §§6.8–6.9. The Chebyshev convergence theorem
uses Mathlib's `has_pointwise_sum_fourier_series_of_summable` and `fourierCoeff_eq_intervalIntegral`
(`Mathlib.Analysis.Fourier.AddCircle`), the Chebyshev measure and
`integral_measureT_eq_integral_cos` (`Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev`),
and the coefficient decay uses `Complex.integral_boundary_rect_eq_zero_of_differentiableOn`. The
Laplace–Heine formula uses `integral_gaussian_complex_Ioi` and
`Complex.tendsto_one_add_pow_exp_of_tendsto`. Example 6.3 uses the project's
`chebyshevT_generating_function`.

## Orthogonal-polynomial integrals and complex-sector asymptotics (2026-10-15)

The ray rotation in `DLMFMathlib/Analysis/Complex/RotateRay.lean` applies the Mathlib contributors'
`Complex.integral_boundary_rect_eq_zero_of_differentiableOn` in logarithmic coordinates. The sector
form of Watson's lemma follows Temme, *Special Functions*, §2.4. Its Gamma integral starts from
Mathlib's `Complex.Gamma_eq_integral` and extends by `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`.
The Gegenbauer Laplace integral uses the project's `DLMF.Gamma.beta_sin_cos` for its
normalization. The Legendre exponential generating function exchanges sum and integral with
Mathlib's `intervalIntegral.hasSum_integral_of_dominated_convergence` and identifies `J₀` through
the project's `hasFPowerSeriesOnBall_regularized0F1`.

## Duverney pass (2026-10-16)

Targets and proof routes follow D. Duverney, *An Introduction to Hypergeometric Functions*
(Birkhäuser, 2024). Upstream reuse:

* Mathlib:
  * Abel's limit theorem (`Real.tendsto_tsum_powerSeries_nhdsWithin_lt`) and
    `Antitone.tendsto_alternating_series_of_tendsto_zero`.
  * Zeta and Hurwitz: `riemannZeta_two_mul_nat`, `hasSum_hurwitzZeta_of_one_lt_re`,
    `HurwitzZeta.expZeta`.
  * `cot_series_rep'`, `hasSum_one_div_nat_pow_mul_sin`, and the Bernoulli-polynomial API.
  * `Real.goldenRatio`, and `NNReal.agm` with its lemmas.
  * The regularized `ₚF_q` series API (`regularizedHGFun`, `ofScalars_series_injective`).
  * Tannery's theorem (`tendsto_tsum_of_dominated_convergence`).
  * Integration: `intervalIntegral.hasSum_integral_of_dominated_convergence`,
    `integral_tsum_of_summable_integral_norm`, `integral_image_eq_integral_abs_deriv_smul`.
  * Derivatives and series: `Complex.hasSum_deriv_of_summable_norm`,
    `tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm`, `Finset.sum_antidiagonal_choose_succ_mul`.
* Project: Polygamma, Digamma and `deriv_recip_Gamma_neg_nat`; the `₂F₁` contiguous, Euler and
  quadratic transformations; `q_binomial_theorem` and `heine_transformation`; the Jacobi/AGM API;
  and the Bessel order-continuity and Wronskian lemmas.
* The `linear_combination` multipliers for the Jacobi addition formulas and Clausen's formula were
  found with sympy Gröbner reduction.

## Gap pass, Temme Chapters 8, 9, 11, 12 (2026-10-16)

Legendre: Neumann's integral uses Mathlib's `HasDerivAt.clog_real` and the project's
`legendre_orthogonality` and `legendrePolyP_recurrence`. The integer Wronskian uses
`IsOpen.is_const_of_deriv_eq_zero`. Bessel zeros (Sturm comparison after Watson §15.6) use
`strictMonoOn_of_deriv_pos`, `IsClosed.csInf_mem` and `intermediate_value_Icc'`. The continued fraction for
`Γ(a,x)` uses Mathlib's `GenContFract` recurrences (`nums_recurrence`, `dens_recurrence`) and
`MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul`. The elliptic additions use Mathlib's
`NNReal.agm` lemmas, `tsum_mul_tsum_of_summable_norm` and `Equiv.tsum_eq` for the theta doubling
identities, and `HasDerivAt.arctan`.

## Separation of the wave equation (2026-10-16)

The coordinate systems and separated equations follow Temme, *Special Functions*, Chapter 10.
The Cartesian computations use the project's regularized `₀F₁` contiguous relation and derivative
lemmas from `DLMF/Bessel/Basic.lean`. The Fourier–Bessel normalization uses Mathlib's
`intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le` and `squeeze_zero_norm'`. The hypergeometric
form of the incomplete Beta function uses the project's Euler integral
`ordinaryHypergeometric_eq_integral` and Mathlib's `intervalIntegral.integral_comp_mul_left`.

## Legendre, statistical and elliptic functions from Temme (2026-10-16)

The proof routes follow N. M. Temme, *Special Functions* (Wiley, 1996), Chapters 8, 11 and 12,
and the DLMF, Chapters 8, 14, 19, 20 and 22. The Legendre functions are built on the project's
cut-plane continuation `regularizedGaussHG` and its contiguous relations, Gauss's second summation and
quadratic transformations, Pfaff's transformation, and Mathlib's `binomialSeries` /
`ordinaryHypergeometric` API. The statistical functions bridge to and reuse TauCeti's
`regularizedGamma`, `lowerIncGamma_eq_integral`, `regularizedIncompleteBeta` and
`sum_Icc_choose_mul_pow_eq_regularizedIncompleteBeta`, and Mathlib's `Complex.betaIntegral` API,
`integral_cpow` and `MeasureTheory.integral_tsum_of_summable_integral_norm`. The elliptic functions
use Mathlib's `NNReal.agm` and `agmSequences` lemmas, `jacobiTheta₂` with its functional equation,
change of variables `integral_image_eq_integral_abs_deriv_smul`, differentiation under the integral
sign, `HasDerivAt.of_local_left_inverse` and `StrictMono.orderIsoOfSurjective`.

## Bessel pass from Temme (2026-10-16)

The proof routes follow N. M. Temme, *Special Functions* (Wiley, 1996), Chapter 9, and the
DLMF, Chapter 10. The project uses Weiyi Wang's `Complex.besselJ`
(`Mathlib.Analysis.SpecialFunctions.Bessel`) as its `J_ν`, with its parity, analyticity,
integer-order analyticity and value at `0`; entireness of the core series uses the Mathlib
contributors' `analyticAt_regularizedHGFun_zero`. The integer-order limits use Mathlib's `dslope`
and the project's parameter-continuity lemmas from `DLMF/Confluent/BasicProperties.lean`. Bessel's
integral uses `intervalIntegral.hasSum_integral_of_dominated_convergence`,
`integral_exp_mul_complex` and `intervalIntegral.integral_comp_sub_left`. The `K_ν` integral uses
`MeasureTheory.integral_comp_mul_left_Ioi` and `integral_add_left_eq_self`. Hankel's expansions
rest on the project's sector Watson lemma and Tricomi expansion. The zero theorems use
`intermediate_value_Icc'` and Rolle's theorem `exists_hasDerivAt_eq_zero`, and Lommel's integral
uses `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le` and
`IntervalIntegrable.mono_fun'` with `intervalIntegral.intervalIntegrable_rpow'`.

## Mellin–Barnes and loop integrals (2026-10-16)

The Mellin–Barnes integrals rest on the Mathlib contributors' Mellin inversion theorem
`mellinInv_mellin_eq` (`Mathlib.Analysis.MellinInversion`), Mathlib's Gamma integral
(`Complex.GammaIntegral`, `Complex.Gamma_eq_integral`), Fubini (`integral_integral_swap`,
`Integrable.mul_prod`), differentiation under the integral
(`hasDerivAt_integral_of_dominated_loc_of_deriv_le`) and the Cauchy estimate
`Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`. The vertical bounds for `Γ` use the project's
product formula DLMF 5.8.3 and modulus formulas 5.4.3–5.4.4. The generalized hypergeometric
equation is stated for the Mathlib contributors' `Complex.regularizedHGFun`
(`Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric`). The loop integral uses
`Complex.integral_boundary_rect_eq_zero_of_differentiableOn` in logarithmic coordinates.

## Connection formula 13.2.41 (2026-10-16)

The proof uses the Mathlib contributors' reflection formula `Complex.Gamma_mul_Gamma_one_sub`,
`Complex.differentiable_one_div_Gamma` for continuity of `1/Γ`, and `Complex.continuousAt_arg`.
It also uses the project's continuity of `𝐌` and `U` in their parameters.

## Confluent pass from Temme (2026-10-15)

The proof routes for the asymptotic expansions of the confluent functions and their special
cases follow N. M. Temme, *Special Functions* (Wiley, 1996), §§7.1–7.3. The binomial series
uses Mathlib's `Complex.one_add_cpow_hasFPowerSeriesAt_zero` and
`HasFPowerSeriesAt.isBigO_sub_partialSum_pow`. The regularized contiguous relations are the
project's existing ones in `DLMF.Confluent.Continuation`. The incomplete Gamma bridge reuses
TauCeti's `TauCeti.ofReal_lowerIncompleteGamma_eq_partialGamma`
(`TauCeti.Analysis.SpecialFunctions.IncompleteGamma`), and `Si(x) → π/2` is TauCeti's
`TauCeti.Contour.tendsto_integral_sinc_atTop`
(`TauCeti.Analysis.Contour.WorkedExamples.HalfDisc.SineIntegral`). Euler's constant enters
`E₁` through the project's `DLMF.Gamma.eulerMascheroni_eq_integral_recip_one_add`.

## Further local proofs (2026-10-08)

The Whittaker M denominator-pole limit and the `q`-Gegenbauer classical limit
reuse the project's proved regularized Kummer continuity/pole formulas and finite
`q`-Pochhammer and Gegenbauer coefficient identities. The two Laguerre fractional
integrals reuse its Kummer parameter integral, Laguerre addition, and moments.
Their adapters use the Mathlib contributors' Gamma/Pochhammer relation in
`Mathlib.Analysis.SpecialFunctions.Gamma.Basic`, affine interval substitution,
and measure-preserving translation. No new upstream theorem is admitted or copied;
the compiled axiom audit verifies all four proofs and their two supporting lemmas.

## Next priority proofs (2026-10-08)

The Rodrigues proofs reuse the project's weighted Jacobi and Laguerre derivative
identities and the Mathlib contributors' iterated derivative and scalar-restriction
APIs in `Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas`. Legendre norms reuse local
Jacobi orthogonality and Legendre recurrence. The unweighted Laguerre convolution
uses local Laguerre derivative identities and Mathlib's interval integration by parts.
The Jacobi fractional integral reuses the proved regularized Gauss fractional integral;
the power moment helper scales Mathlib's Beta integral.

The regularized Kummer Laplace self-transform uses Mathlib's
`hasSum_integral_of_summable_integral_norm`, the project's regularized Gauss
summability and binomial series, and its proved complex Gamma moments. The closed
Whittaker M transform reuses that self-transform with Mathlib's principal-logarithm
API. Tricomi kernel convergence uses Mathlib's Gamma integrability and a finite
binomial majorant; its shifted-parameter case reuses local Kummer transformation and
Gamma moments. The compiled audit checks all seven completed admissions and five
supporting lemmas without admitted dependencies.

## Open priority continuation (2026-10-08)

The weighted Laguerre convolution uses the Mathlib contributors' Beta integral,
Gamma/Pochhammer relation, polynomial coefficient formulas for `(X + 1)^n`, and
additive-homomorphism finite-sum API. Jacobi norms use the project's weighted
Jacobi derivative with Mathlib's endpoint power continuity and interval FTC;
Gegenbauer orthogonality then uses the proved symmetric Jacobi family and
Mathlib's Gamma duplication formula. The underlying upstream modules are
`Mathlib.Analysis.SpecialFunctions.Gamma.Beta`,
`Mathlib.Algebra.Polynomial.Coeff`, `Mathlib.Algebra.Polynomial.Monic`, and
`Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus`.

The general Kummer transform in its absolute series region uses Mathlib's
summable-integral-norm exchange and the project's regularized Gauss summability,
cut-plane comparison, and complex Gamma moments. The finite shifted Tricomi
Laplace family uses the project's proved shifted Tricomi sum with Mathlib's
binomial expansion and Gamma integrability. The existing Kummer self-transform
and Tricomi shift-one proofs now specialize these broader lemmas. No new upstream
admission is used; the compiled audit checks all three closed admissions, their
supporting lemmas, and the refactored special cases.

## Full half-plane Kummer transform (2026-10-08)

The Kummer ray bound uses the Mathlib contributors' reciprocal Gamma recurrence
in `Mathlib.Analysis.SpecialFunctions.Gamma.Beta`, interval-integral norm bounds,
and FTC. Parameter lowering extends the project's proved Euler representation
to arbitrary complex parameters. Finite Gamma majorants justify holomorphic
Laplace dependence using `hasDerivAt_integral_of_dominated_loc_of_deriv_le` from
`Mathlib.Analysis.Calculus.ParametricIntegral`. Analytic uniqueness extends the
project's series-region transform to the full half-plane, retaining the Gauss
cut-plane continuation and singular denominator parameters.

Tricomi integral parameter continuity uses Mathlib's `continuousAt_of_dominated`
from `Mathlib.MeasureTheory.Integral.Bochner.Basic`, the proved kernel
integrability, and the project's continued `U` parameter continuity. This also
provides a proved reduction of the general representation to noninteger second
parameters; that initial identification remains open. The compiled audit checks
the completed Kummer transform and all eight new public supporting proofs without
any dependency on admitted results. No new TauCeti result is adopted in this pass.

## Tricomi and Whittaker Laplace representations (2026-10-08)

The Gauss confluence proof uses the Mathlib contributors' dominated convergence
theorem for series. Tricomi's integral limit uses their real Bernoulli inequality
from `Mathlib.Analysis.Convex.SpecificFunctions.Basic`, complex exponential
approximation, and dominated convergence for integrals. Its majorant is integrable
by the **Tau Ceti contributors'**
`integrableOn_rpow_mul_one_add_rpow` in
[TauCeti.Analysis.SpecialFunctions.Beta](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/Analysis/SpecialFunctions/Beta.lean).
The affected module header and point of use also credit this reuse.

The connection limit reuses the project's proved Gauss connection formula and
Gamma-ratio asymptotic. Mathlib's dominated differentiation and analytic
uniqueness extend the argument region; the project's proved parameter continuity
then supplies integer second parameters. Whittaker W uses Mathlib's affine
integral substitution and principal complex powers. The compiled axiom audit
checks both completed representations, the public supporting lemmas, the shifted
special cases, and the Gauss, Gamma, and TauCeti foundations without admitted
dependencies.

## Tricomi Mellin transform (2026-10-08)

The proof reuses the project's proved Tricomi Laplace representation and complex
Gamma and Beta integrals. Absolute convergence uses the Mathlib contributors'
`Real.integral_rpow_mul_exp_neg_mul_Ioi` and Gamma integrability, together with
the **Tau Ceti contributors'** `integrableOn_rpow_mul_one_add_rpow` from
[TauCeti.Analysis.SpecialFunctions.Beta](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/Analysis/SpecialFunctions/Beta.lean).
Mathlib's `integrable_prod_iff'` and `integral_integral_swap` in
`Mathlib.MeasureTheory.Integral.Prod` justify the integral exchange. The affected
module header and helper docstring credit the reuse. The compiled axiom audit
checks the transform, its new absolute-integrability theorem, and all three
special-function integral foundations without admitted dependencies.

## TauCeti

TauCeti is available as a dependency, pinned since 2026-10-26 at revision
`a049b4264d2cf4dbf4720796f844a3a3764914a5` (jointly with lean-codes, lean-CA, lean-LCS and
lean-SCV, which share the package checkout). Older entries cite the revision they used. The source headers of the modules below
credit **The Tau Ceti contributors**, under the Apache 2.0 license.

The [reuse review and implementation](TauCetiReview.md) records six adopted uses.
Three existing proofs now call TauCeti, new bridges connect the real restrictions
of the complex error functions, and three admissions (two Hermite Fourier
identities and compact-support Parseval) have been replaced by checked proofs.
The affected module headers also credit the imported work.

- [Hermite orthogonality](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/Analysis/SpecialFunctions/Hermite/Orthogonality.lean):
  `integral_hermite_mul_hermite_mul_gaussian`, now used for the project's
  probabilists’ Hermite orthogonality proof.
- [Polynomial Gaussian integrability](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/Probability/Distributions/Gaussian/PolynomialMemLp.lean):
  `integrable_eval_mul_exp_neg_sq`, now used for the matching project helper.
- [Beta integrals](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/Analysis/SpecialFunctions/Beta.lean):
  `integral_rpow_mul_one_sub_rpow`, now used for the project's real beta integral.
- [Error function](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/Analysis/SpecialFunctions/Erf.lean):
  the real `erf` and `erfc` APIs, identified with the project's complex functions on real inputs.
- [Hermite Fourier transform](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/Analysis/SpecialFunctions/Hermite/Function/Fourier/Basic.lean):
  `fourier_twoPiHermiteFunction` supplies the upstream eigenfunction theorem for
  the now-proved `hermitePolyH_fourier_eigenfunction` and `hermite_fourier_eigenfunction`.
  Local adapters account for the Fourier phase, dilation and polynomial normalization.
- [Polynomial completeness](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/Analysis/InnerProductSpace/PolynomialCompleteness.lean)
  and [weighted orthogonal bases](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/Analysis/InnerProductSpace/WeightedOrthogonalBasis.lean):
  the completeness and basis construction used to prove
  `orthogonal_polynomials_parseval` and `compact_support_L2_expansion`, followed
  by Mathlib’s Hilbert-basis Parseval and expansion identities.

- [Hermite parity](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/RingTheory/Polynomial/Hermite/Derivative.lean):
  `Polynomial.hermite_aeval_neg`, and the Gaussian integrability
  `integrable_aeval_mul_gaussian` from the Hermite orthogonality module above. Both are
  used for the now-proved `hermite_even_cosine_transform` and `hermite_odd_sine_transform`
  in [Integrals.lean](DLMF/OrthogonalPolynomials/Integrals.lean). The product cosine
  and sine transforms reuse these single-polynomial transforms and Gaussian
  integrability. The Hermite convolution uses the polynomial Gaussian integrability
  adaptation listed above.

Related real incomplete-gamma, Dirichlet and multivariate-Gamma developments are
not replacements for the project's general complex statements. Adoption should retain
attribution in the affected module headers and at the point of use.

## Dirichlet simplex integrals ported from lean-codes (2026-10-16)

The Dirichlet simplex integrals were first ported from the companion project `lean-codes`
(same author) into `DLMF/Gamma/Simplex/`. Since lean-codes became a Lake dependency
(2026-10-25) the ports have been removed (2026-10-28) and the project imports the lean-codes
modules `StdSimplexMeasure/*`, `Pochhammer/*` and `Dirichlet/Beta/Complex/*` directly.
DLMF 5.14.1–5.14.2 (`dirichlet_simplex`,
`dirichlet_simplex_full`) are derived from `mvBetaIntegralOne_eq_mvBeta` and
`mvBetaIntegral_eq_mvBeta`. The Glaisher–Kinkelin closed form 5.17.7 differentiates the Mathlib
contributors' `riemannZeta_one_sub` and uses `Complex.hasDerivAt_Gamma_nat`
(`Mathlib.NumberTheory.Harmonic.GammaDeriv`).

## Beals–Wong additions (2026-10-18)

Beals and Wong, *Special Functions and Orthogonal Polynomials*, second edition
(Cambridge, 2016), supplies the mathematical targets: the indexed Hermite and
Jacobi zero estimates in §§5.3 and 5.5, discrete Rodrigues and addition formulas
in §§6.2–6.5, and Bessel transforms in §9.8. The supplied PDF's filename says
2015; its copyright page gives 2016 as the publication year.

[DiscreteAddition.lean](DLMF/OrthogonalPolynomials/DiscreteAddition.lean) uses
the Mathlib contributors' formal exponential series and the existing local
Chu–Vandermonde and terminating-sum APIs.
[DiscreteRodrigues.lean](DLMF/OrthogonalPolynomials/DiscreteRodrigues.lean) uses
Mathlib's `fwdDiff` and the local Charlier difference equation. The indexed
zero proofs reuse the local Sturm comparison, Hermite–Laguerre identities,
and classical root enumerations, with Mathlib's trigonometric calculus.
[IntegralTransforms.lean](DLMF/Bessel/IntegralTransforms.lean) reuses the
proved local regularized Kummer integral, full Kummer Laplace transform,
and Bessel–Kummer identity; Mathlib's change-of-variables and complex-power
APIs handle the Gaussian substitution and scaling. The module headers and
proofs identify these sources of reuse.


The refinement batch uses the same Beals–Wong source for strict Jacobi angle
bounds and the Meixner, Krawtchouk, and Hahn Rodrigues formulas. The Jacobi proof
reuses the existing local Sturm comparison theorem. The discrete proofs use the
Mathlib contributors' binomial expansion of iterated `fwdDiff`, factorial identities,
and the local terminating-sum and Hahn difference APIs. The complex Gaussian
transform adapts the regularized `₀F₁` summation argument using the existing complex
Gamma integral. The new [LaplaceTransform.lean](DLMF/Bessel/LaplaceTransform.lean)
uses the proved Kummer Laplace theorem, the local quadratic Gauss transformation
and regularized contiguous relations, and Mathlib's analytic identity principle.
The parameter-lowering argument retains exceptional orders without cancellation
of singular Gamma factors.

## Painlevé II (2026-10-18)

Beals and Wong, second edition, Chapter 15, supplies the Painlevé II
normalization, pole analysis, rational and Airy constructions, Bäcklund
transformations, compatible linear system, energy identity, and quotient
equations formalized in [DLMF/Painleve.lean](DLMF/Painleve.lean). The Airy scale
corrects the substitution on page 407: it must satisfy `k³ = -1/2`.

The local real existence and uniqueness proofs reuse the Mathlib contributors'
Picard–Lindelöf, continuously differentiable vector-field existence, and locally
Lipschitz ODE uniqueness results in `Mathlib.Analysis.ODE.ExistUnique`.
The pole analysis uses Mathlib's `Meromorphic.Order`, including derivative
orders and analytic factorization. The rational construction uses Mathlib's
polynomial evaluation, differentiation, and root APIs. The Airy construction
reuses the proved local [Airy API](DLMF/Airy/Basic.lean), with Mathlib's analytic
and meromorphic calculus. The Lax derivative uses Mathlib's matrix normed-space
and product-derivative APIs. The new proofs do not adopt any TauCeti Painlevé
removability theorem, which concerns a different subject.


## First admission-priority batch (2026-10-18)

The Laguerre and Hermite Mehler–Heine limits reuse the local regularized confluent
large-parameter limit, Gamma-ratio asymptotics, and regularized Bessel/trigonometric
identities. The Laguerre–Bessel integral reuses the local regularized Bessel integral
and Kummer transformation. Its uniform bound uses the proved Hermite-product cosine
transform and Laguerre connection coefficients, with the Tau Ceti contributors’
Gaussian polynomial integrability theorem.

The moment determinant identities in
[GeneralIdentities.lean](DLMF/OrthogonalPolynomials/GeneralIdentities.lean) use the
Mathlib contributors’ `Matrix.det_updateCol_sum` and the Tau Ceti contributors’
`Matrix.det_eq_mul_det_submatrix_castSucc_of_col` from
`TauCeti.LinearAlgebra.Matrix.CornerMinor`, together with the local orthogonal
polynomial basis and integral APIs. The disk-polynomial polar identity uses the
local finite Jacobi sum and reflection formula and Mathlib’s factorial and
Pochhammer identities.

The ball Poisson representation in
[Theorems.lean](DLMF/SphericalHarmonics/Theorems.lean) uses the Tau Ceti contributors’
`Analysis.PDE.PoissonIntegral.Ball` and `Analysis.InnerProductSpace.Laplacian.Comparison`.
The continuous extension argument is adapted from their unit-ball Dirichlet proof;
the final identification uses their Dirichlet uniqueness theorem. The `SU(2)`
double cover uses their `LinearAlgebra.CliffordAlgebra.Spin.Real.Three`,
`Spin.Real.Basic`, and
`LinearAlgebra.QuadraticForm.SpecialOrthogonal.WeightedSumSquares`, including
`realSpinThreeEquivSpecialUnitary`, positive-definite Spin surjectivity,
`mem_ker_spinToSpecialOrthogonal_iff`, and the matrix coordinate equivalence.

The Whittaker transform corrections retain the DLMF 13.23 source formulas while
expressing regularized Whittaker `M` through Mathlib’s regularized confluent
hypergeometric function, rather than division of a totalized ordinary series at a
Gamma pole. The regularization bridge is proved; the five corrected transforms
remain admitted.


## Finite identities and connection coefficients (2026-10-18)

The finite Kummer–Bessel expansions in
[Relations.lean](DLMF/Confluent/Relations.lean) follow DLMF 13.6.11₁–13.6.11₂.
The proofs use the existing local regularized Kummer contiguous relations and
entire dependence on the parameters, together with the Mathlib contributors’
reciprocal-Gamma recurrence, Pascal/binomial identities and complex identity
principle. Expressing the finite sum through regularized `₀F₁` permits the Kummer
transformation without changing a principal-power branch at a negated argument.

The Kummer and Whittaker product identities in
[ProductsAddition.lean](DLMF/Confluent/ProductsAddition.lean), DLMF 13.12.1 and
13.25.1, use the existing local derivative and contiguous APIs. Mathlib’s theorem
that an entire function with zero derivative is constant supplies the final
Kummer identity; the Whittaker formula follows by the existing Kummer
transformation and principal-power calculus.

The Jacobi connection formula is AAR Lemma 7.1.1. The Gegenbauer monomial,
connection and linearization formulas follow DLMF 18.18.17, 18.18.16 and 18.18.22.
Their implementations in [Topics.lean](DLMF/OrthogonalPolynomials/Topics.lean) and
[Series.lean](DLMF/OrthogonalPolynomials/Series.lean) use the local finite Jacobi
and Gegenbauer series, Gegenbauer recurrence and Pochhammer convolution, with
Mathlib’s finite-sum, binomial, factorial and polynomial APIs. The finite
Pochhammer inversion is proved by telescoping, with a separate regular head
term so that the Jacobi case `α + β = -1` remains included. The linearization
proof verifies the interior and endpoint coefficient recurrences and then uses
induction on the smaller polynomial degree.


## Six generating-function, integral and orthogonality proofs (2026-10-19)

The adjacent Jacobi generating function follows DLMF 18.12.3_5. The Laguerre
product Laplace transform is DLMF 18.17.34_5; the Jacobi and Laguerre double
Laplace integrals are 18.10.3 and 18.10.6. Finite Bessel-polynomial and Morse
orthogonality are DLMF 18.34.5_5 and 18.34.7_3, in the normalizations already
acquired in the project.

The new proofs use the Mathlib contributors' Gamma/Pochhammer and Gaussian
moment results, finite polynomial induction, shifted summation, and real
change-of-variables APIs. In particular, `integral_comp_rpow_Ioi` and its
integrability counterpart justify reciprocal moments, the one-dimensional
Jacobian theorem handles the square-substituted Beta moments, and
`integral_comp_exp` transports Bessel orthogonality to the Morse functions.
These uses are identified in the changed module headers and at their points of
use. The proofs also reuse the project's proved Jacobi parameter-raising and
binomial formulas, Gegenbauer generating function and angular Laplace
representation, Laguerre multiplication formula and orthogonality, and finite
Pochhammer Vandermonde identity. No new TauCeti source was copied or adapted in
this batch.


## Jacobi endpoint limit and multivariate orthogonality (2026-10-19)

Jacobi Mehler–Heine in [Limits.lean](DLMF/OrthogonalPolynomials/Limits.lean)
follows DLMF 18.11.5. The proof uses the Mathlib contributors' Tannery theorem
(`tendsto_tsum_of_dominated_convergence`), descending-factorial bound
(`Nat.descFactorial_le_pow`) and continuous sinc function. The project's proved
Gamma-ratio limit and regularized Bessel series give the normalization. A new
terminating-series bound handles both numerator parameters varying with degree.

Disk and triangle orthogonality in
[Multivariate.lean](DLMF/OrthogonalPolynomials/Multivariate.lean) follow DLMF
18.37.2 and 18.37.8. Their proofs use Mathlib's polar-coordinate integral formula,
Jacobian change-of-variables formulas, separated-product integral formula and
complex exponential integral. These are applied to the project's proved disk
polar representation and one-variable Jacobi orthogonality. No TauCeti source
was copied or adapted in this batch.


## Hahn/Wilson generating functions and Legendre identities (2026-10-19)

The continuous Hahn, Wilson and continuous dual Hahn generating functions follow
DLMF 18.23.6, 18.26.18 and 18.26.19. Their coefficient proofs use the project's
proved Chu–Vandermonde, Euler convolution and Pfaff–Saalschütz identities.
[FiniteConvolution.lean](DLMF/Hypergeometric/FiniteConvolution.lean) supplies the
finite `3F2` and balanced `4F3` transformations. Mathlib's absolutely summable
Cauchy-product API, `hasSum_sum_range_mul_of_summable_norm`, then identifies the
convergent series. The previously exposed OP convolution helper is retained as
an adapter to the earlier shared helper.

Legendre addition and its product and singular integrals are DLMF 18.18.9,
18.17.6 and 18.17.44. The new
[addition kernel](DLMF/OrthogonalPolynomials/LegendreAddition.lean) uses the local
Jacobi derivative/ladder identities and the Mathlib contributors' analytic
identity principle, derivative, finite-sum and trigonometric APIs. The product
integral integrates the resulting finite cosine sum using Mathlib's
`integral_cos_mul_complex`. The
[singular-integral proof](DLMF/OrthogonalPolynomials/LegendreSingular.lean) uses
Mathlib's `dslope` continuity and interval-integral congruence and fundamental
theorem of calculus APIs to justify the split at the diagonal. No TauCeti
source was copied or adapted in this batch.


## Confluent additions, boundary Mellin transforms and Mehler (2026-10-19)

The eight first-parameter Kummer and Whittaker addition formulas in
[ProductsAddition.lean](DLMF/Confluent/ProductsAddition.lean) follow DLMF 13.13.3,
13.13.5, 13.13.9, 13.13.11, 13.26.3, 13.26.6, 13.26.9 and 13.26.12.
[MobiusTaylor.lean](DLMF/Confluent/MobiusTaylor.lean) uses Mathlib's
`Complex.taylorSeries_eq_on_ball'`, local differentiation of equal functions,
and principal complex-power calculus with the project's proved contiguous
relations. The zero-preserving coefficient recurrence avoids dividing by
numerator parameters.

The Mellin transforms in [Integrals.lean](DLMF/Confluent/Integrals.lean) follow
DLMF 13.10.5 and 13.23.3. The new
[regularized boundary summation](DLMF/Hypergeometric/Boundary.lean) uses the
project's proved Gauss summation and reciprocal Gamma recurrence. The Gamma-moment
majorant reuses the local proved Gamma-ratio asymptotics and Mathlib's summable
integral-norm theorem, real Gamma integral and finite-prefix series API.

[Mehler.lean](DLMF/OrthogonalPolynomials/Mehler.lean), DLMF 18.18.28, uses the
Mathlib contributors' complex Taylor theorem, analyticity of derivatives and
uniqueness of formal multilinear series. The Hermite polynomial recurrence
identifies the coefficients. Existing scalar-series helpers were extracted from
`Series` into [ScalarSeries.lean](DLMF/OrthogonalPolynomials/ScalarSeries.lean)
without changing their statements or proofs.

The natural-shift Gamma-ratio estimate in
[RatioBounds.lean](DLMF/Gamma/RatioBounds.lean) uses Mathlib's Gamma recurrence,
complex norm-square and real-power APIs and the project's finite Pochhammer
recurrence. It does not use the admitted general ratio inequality. No TauCeti
source was copied or adapted in this batch.


## Tricomi Laplace transforms and continuous Hahn orthogonality (2026-10-19)

The Tricomi and Whittaker transforms in
[Integrals.lean](DLMF/Confluent/Integrals.lean) follow DLMF 13.10.7 and 13.23.4.
[EulerHalfLine.lean](DLMF/Hypergeometric/EulerHalfLine.lean) uses the Mathlib
contributors' `integral_image_eq_integral_abs_deriv_smul` and
`integrableOn_image_iff_integrableOn_abs_deriv_smul` to transfer the project's
continued Euler Gauss integral to the positive half-line. The double integral in
[TricomiLaplace.lean](DLMF/Confluent/TricomiLaplace.lean) uses Mathlib's Fubini and
integrability-of-iterated-integrals APIs, the Gamma integral and principal-power
calculus. The local proved Tricomi and regularized Gauss contiguous relations
extend both the transform and its integrability to unrestricted first parameter.
The existing continued Pfaff transformation supplies the stated argument.

Continuous Hahn orthogonality in [Hahn.lean](DLMF/OrthogonalPolynomials/Hahn.lean)
follows DLMF 18.19.4. [HahnMoments.lean](DLMF/OrthogonalPolynomials/HahnMoments.lean)
uses the project's proved Barnes four-Gamma lemma, vertical Gamma bound,
Pfaff–Saalschutz theorem and finite Pochhammer reflection/Vandermonde formulas.
Mathlib's finite-sum integral and absolute-integrability APIs justify every
exchange. No TauCeti source was copied or adapted in this batch.


## Integer-parameter Tricomi expansion and logarithmic remainders (2026-10-19)

The integer-denominator expansion and the small-argument estimates at second
parameters one, two and zero in
[BasicProperties.lean](DLMF/Confluent/BasicProperties.lean) follow DLMF 13.2.9,
13.2.19, 13.2.17 and 13.2.21. The existing parameter-limit definition and
Kummer transformation retain the principal complex branches.

[ParameterDerivatives.lean](DLMF/Confluent/ParameterDerivatives.lean) adapts the
project's proved Gauss parameter-differentiation argument in
[ConnectionFormulas.lean](DLMF/Hypergeometric/ConnectionFormulas.lean), using the
confluent majorant from [Regularized.lean](DLMF/Confluent/Regularized.lean).
It reuses Mathlib's `hasSum_deriv_of_summable_norm` and the local proved
reciprocal-Gamma and Pochhammer derivative formulas, including reciprocal-Gamma
zeros. [LogSeries.lean](DLMF/Confluent/LogSeries.lean) uses Mathlib's scalar
formal power series, convergence radius and analyticity APIs. The remainder
proofs use Mathlib's derivative-to-Big-O and complex logarithm norm estimates;
exceptional first parameters use the project's exact polynomial formulas.
No TauCeti source was copied or adapted in this batch.


## Airy theory acquisition and first proofs (2026-10-19)

The new [Airy modules](DLMF/Airy.lean) acquire NIST DLMF
[§9.2](https://dlmf.nist.gov/9.2) and
[§§9.4–9.14](https://dlmf.nist.gov/9.4), including the Scorer, Swanson–Headley,
Olver, Smirnov, Reid and incomplete-function conventions cited there.
[AiryAcquisition.md](AiryAcquisition.md) maps every numbered equation and
records the qualification of Reid's positive-parameter ray integrals.
The many admitted statements are source acquisitions, not completed proofs.

The first 36 proofs extend the project's proved Airy series, initial-value,
Wronskian and rotation theory. They use the Mathlib contributors' complex
calculus, derivative-of-quotient, Gamma reflection, finite Pochhammer,
regularized ₀F₁ differentiability, finite sum and algebra APIs. The general
solution uses the project's proved uniqueness theorem; product Wronskians and
antiderivatives reduce to its Airy ODE and initial Wronskian. No TauCeti source
was copied or adapted in this batch.


## DLMF Chapters 6–8 acquisition (2026-10-19)

The source of the expanded [exponential integrals](DLMF/ExpIntegrals.lean),
[error/Dawson/Fresnel functions](DLMF/ErrorFunctions.lean) and
[incomplete Gamma and related functions](DLMF/IncompleteGamma.lean) is NIST DLMF
[Chapter 6](https://dlmf.nist.gov/6), [Chapter 7](https://dlmf.nist.gov/7) and
[Chapter 8](https://dlmf.nist.gov/8), version 1.2.8. Graphs and application notes
are excluded. [DLMF678Acquisition.md](DLMF678Acquisition.md) records individual
equations, named normalizations, source qualifications and the proved
continued-fraction counterexample. Most acquired theorems remain admitted.

[MathlibCoverage.lean](DLMF/Core/MathlibCoverage.lean) points to the Mathlib
contributors' complete Beta/Gamma identity, partial Gamma integral and
recurrence, and Gaussian integrals. No local duplicate of the complete Beta
identity is added. The continued-fraction helper calls Mathlib's
`GenContFract.nextConts`, adding termination and argument conventions.

The first 19 proofs reuse Mathlib's Gamma/power, square-root, polynomial and
finite-sum APIs, the project's proved incomplete Beta symmetry and power
specialization, and its existing E1/U definitions and bridge. The inverse
erf/erfc proofs reuse TauCeti's `Real.erfInv` and `Real.erf_erfInv`, via the
existing complex-to-real erf bridge. These root `Real` declarations are in
TauCeti's source, not Mathlib. No TauCeti proof source was copied or adapted.


## DLMF Chapters 11, 12 and 14 acquisition (2026-10-19)

The expanded [Struve](DLMF/Struve.lean), [parabolic-cylinder](DLMF/ParabolicCylinder.lean)
and [Legendre](DLMF/Legendre.lean) theory follows NIST DLMF version 1.2.8:
[Chapter 11](https://dlmf.nist.gov/11), R. B. Paris;
[Chapter 12](https://dlmf.nist.gov/12), N. M. Temme;
and [Chapter 14](https://dlmf.nist.gov/14), T. M. Dunster.
Graphs and application notes are excluded. The
[acquisition ledger](DLMF111214Acquisition.md) records equations, prose,
normalizations, domain restrictions and two formally checked source discrepancies.
Most acquired theorems remain admitted.

The Mathlib contributors supply `Complex.besselJ`, Gamma and digamma, inverse
hyperbolic functions, Chebyshev and probabilists' Hermite polynomials, complex
calculus, analytic uniqueness, ordered convergence and finite-sum APIs.
DLMF 14.7.13 points to `Polynomial.factorial_mul_shiftedLegendre_eq` with the
existing local normalization bridge; the Gamma ratio in 12.14.22 points to
`Complex.Gamma_add_nat_div_Gamma_eq`. Neither upstream result is reproved here.

The 25 first proofs extend the project's already proved cylinder, error-function,
hypergeometric continuation and polynomial theory. The existing cylinder core's
TauCeti Hermite derivative dependency is retained. No TauCeti proof source was
copied or adapted in this batch. The two counterexample files use accepted proofs
without reliance on the newly admitted statements.


## DLMF seven-track proof batch (2026-10-19)

The [100 admission removals](REVIEW.md#seven-track-admission-removal-2026-10-19)
reuse the proved project Kummer/Tricomi, continued Gauss, incomplete Gamma/Beta,
parabolic-cylinder and orthogonal-polynomial APIs. The complete statement sources
remain the DLMF Chapter 6–8 and 11/12/14 acquisition ledgers cited above.

The Mathlib contributors supply complex primitive existence
`Differentiable.isExactOn_univ`, interval FTC
`intervalIntegral.integral_eq_sub_of_hasDerivAt`, real exponential-series
summability `Real.summable_pow_div_factorial`, and locally uniform holomorphic
convergence `differentiableOn_tsum_of_summable_norm`. These are the inputs to the
new Mathlib-only segment-primitive and sparse-factorial-series adapters.
Mathlib's `Complex.regularizedHGFun`,
`Complex.radius_regularizedHGFunSeries_eq_top` and
`Complex.analyticAt_regularizedHGFun_of_card_le` supply the Struve and small-Lommel
argument theory; Gamma identities and reciprocal-Gamma differentiability retain
exceptional parameters. The E1–Ein proof uses the project's previously proved
termwise regularized Kummer parameter derivative and integer-parameter Tricomi
connection numerator. The existing cylinder core retains its TauCeti Hermite
calculus dependency. No TauCeti proof source was copied or adapted in this batch,
and no exact DLMF result already covered by Mathlib was reproved locally.


## DLMF four-priority proof follow-up (2026-10-20)

The [69 admission removals](REVIEW.md#four-priority-admission-removal-2026-10-20)
reuse the project's proved regularized Gauss, Kummer/Tricomi, cylinder, Gamma,
Beta and Hermite APIs. The DLMF equation sources remain those recorded in the
Chapter 6–8 and 11/12/14 acquisition ledgers.

The Mathlib contributors supply complex analytic uniqueness and the implication
from complex differentiability to analyticity, `Complex.differentiableOn_dslope`,
the two one-sided principal-log limits on the negative real axis, interval FTC,
reciprocal-Gamma recurrence and the factorial/binomial and series-reindexing APIs.
The two general entire-function adapters added to SegmentPrimitive import Mathlib
only. Their uses preserve the original totalized integral values at the origin.

TauCeti's `continuous_regularizedIncompleteBeta`, through the existing project
normalization bridge in `DLMF.Statistical.IncompleteBeta`, supplies the incomplete-
Beta endpoint limit. The existing cylinder/Hermite and Tricomi integral cores
retain their previously documented TauCeti dependencies. No TauCeti source was
copied or adapted, and no exact DLMF result already in Mathlib was reproved here.


## Struve and Lommel forcing batch (2026-10-20)

The [15 admission removals](REVIEW.md#struve-and-lommel-forcing-2026-10-20)
use the DLMF statements and normalizations already recorded in the acquisition
ledgers. Mathlib's `Complex.regularizedHGFun` and its power-series radius and
analyticity theorems supply the underlying entire series. Reciprocal-Gamma
recurrence and the project's proved generalized coefficient recurrence give the
exact inhomogeneous second-order equation, without cancelling Gamma factors at
exceptional orders.

The ordinary solution formulas reuse
`DLMF.Bessel.eq_besselJ_besselY_of_ode`, whose accepted proof includes integer orders.
Mathlib's analytic and iterated-derivative calculus supplies linearity and local
congruence of the Bessel operator; the existing principal-power derivative fixes
the branch in the quadratic substitution. The Fresnel norm proofs use the
project's real/complex bridges and Mathlib's complex norm and real trigonometric
identities. No dependency was added, no TauCeti source was copied or adapted, and
no exact DLMF theorem already proved in Mathlib was reproved here.


## Four-track identity batch (2026-10-20)

The [58 admission removals](REVIEW.md#four-track-identity-proofs-2026-10-20)
use the DLMF statements and normalizations already acquired in this project.
The regularized Struve and Fresnel reductions use Mathlib's
`Complex.regularizedHGFun`, its coefficient definition, convergence radius and
power-series APIs, together with Gamma recurrence and the existing Bessel and
hypergeometric cores. The I/K basis theorem adapts the project's proved J/Y
Abel/Wronskian argument to the already proved modified Bessel Wronskian.

Mathlib's `Complex.hasSum_taylorSeries_of_entire` supplies the repeated-erfc
Taylor sum. The coefficient evaluation uses the project's proved
`pcfU_iterated_deriv_10` and `pcfU_zero`; it does not cancel a Gamma factor at
an exceptional parameter. The Fresnel primitive adapter uses
`Complex.hasSum_cos`, `Complex.hasSum_sin`,
`intervalIntegral.hasSum_integral_of_dominated_convergence`,
`intervalIntegral.integral_ofReal` and `integral_pow`. The logarithmic Gamma
half-order continuation uses the real fundamental theorem of calculus through
the existing straight-segment primitive adapter, and the proved complex erf
and Kummer identities. The Dawson transfer reuses the project's
`Real.dawsonF_eq_kummerM` through its established real/complex normalization
bridge and Mathlib's entire-function uniqueness theorem.

The associated-P/Ferrers-P recurrences reuse the project's regularized Gauss
contiguous relations; the Olver-Q equation uses their proved differential
equation and Mathlib's analytic chain and product rules. No dependency was
added, no TauCeti source was copied or adapted, and no exact DLMF theorem already
proved in Mathlib was reproved here. All 58 completed statements and 34 new
proved helpers were checked for absence of admitted dependencies.


## Finite Struve sums and Ferrers foundations (2026-10-20)

The [11 admission removals](REVIEW.md#finite-struve-sums-and-ferrers-foundations-2026-10-20)
retain the acquired DLMF normalizations and branch conventions. The finite
Struve identities reuse the project's Bessel and Struve derivative ladders,
Mathlib's factorial recurrences, finite-sum differentiation and complex powers.
The P order recurrences reuse proved regularized Gauss contiguous identities.

The regularized quadratic connection reuses the project's proved ordinary
quadratic formula and
`DLMF.Hypergeometric.analyticOnNhd_regularizedGaussHGFun_comp`, with the proved
`Complex.eq_of_differentiable_of_eqOn_pos_reals` adapter. Mathlib's
`Complex.differentiable_one_div_Gamma`, `Complex.Gamma_mul_Gamma_one_sub` and
positive-real logarithm identities supply the normalization and exceptional
parameter extension. The Ferrers-Q equation reuses the proved regularized
Gauss equation and Mathlib's complex derivative rules and real restrictions.

The lower-Gamma parameter proof uses the project's
`analyticAt_regularizedConfluent_comp` and Mathlib's reciprocal-Gamma
analyticity. Logarithmic monodromy uses
`Complex.exp_int_mul_two_pi_mul_I`. The lower trigonometric bridge uses the
proved `scIncGamma_hasSum_alternating`, the previously established factorial
decay bound and Mathlib's `HasSum.even_add_odd`.

No dependency was added and no TauCeti source was copied or adapted. Existing
Mathlib theorems are used through normalization adapters rather than restated
as newly acquired project results. All 11 completed statements and 16 new
proved helpers were checked for absence of admitted dependencies.

## Project-wide tier-A proof batch (2026-10-20)

These proofs use the project's own proved cores together with Mathlib's integral,
calculus, series, polynomial and complex-power APIs. They use the following pinned
TauCeti theorems by name, through imports; no TauCeti source was copied or adapted:

- `TauCeti.regularizedIncompleteBeta` and its `_def_of_mem_Icc`, `_symm`,
  `_eq_one_of_one_le` and `continuous_regularizedIncompleteBeta` lemmas, together with
  `TauCeti.integral_rpow_mul_one_sub_rpow` and
  `TauCeti.intervalIntegrable_rpow_mul_one_sub_rpow`. These give the incomplete-Beta
  quadratic substitution (8.17.22) and the related limits.
- `TauCeti.lowerIncompleteGamma` and `TauCeti.continuous_lowerIncompleteGamma`, for the
  zero limit of the upper-Gamma power bounds.
- `TauCeti.Real.erfc`, `erfc_def`, `hasDerivAt_erfc`, `tendsto_erf_atTop` and
  `tendsto_erfc_atTop`, for the Mills-ratio and horizontal erfc integrals.

The general interval-integral differentiation rule used for the Anger and Weber
functions is a short local proof from Mathlib's
`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`. It does not
reuse the Selberg module's parametric-integral lemma.

## Shared-helper round (2026-10-20)

`DLMFMathlib/Analysis/Complex/ParametricHolomorphy.lean` is new project work built from
Mathlib's one-variable Cauchy integral formula and its dominated-convergence and
`fderiv` APIs. It includes a continuous form of Osgood's lemma. No code was copied from
other projects. The joint parameter holomorphy of the continued Gauss function, the
Struve Poisson integrals and the remaining helpers of this round reuse the project's
proved cores together with Mathlib. No new TauCeti theorem was adopted beyond those
listed for the tier-A batch.

## Blocker round (2026-10-20)

The new files `DLMF/Bessel/KIntegralRep.lean`, `YIntegralRep.lean`, `YSchlafli.lean`,
`Schlafli.lean`, `ProductIntegral.lean`, `NeumannSeries.lean`,
`DLMFMathlib/Analysis/ODE/PowerSeriesUniqueness.lean` and
`DLMFMathlib/Analysis/Asymptotics/WatsonRotated.lean` are new project work built on Mathlib
and the project's existing cores. No code was copied from other projects. From TauCeti,
`TauCeti.Contour.tendsto_integral_sinc_atTop` (the Dirichlet integral, from
`TauCeti.Analysis.Contour.WorkedExamples.HalfDisc.SineIntegral`) is used in the proof of
`struveH_integral_one_div_sq`. The WZ certificates for the two terminating identities in
`NeumannSeries.lean` were found with sympy; the identities themselves are proved in Lean.

## DLMF 13.11.3 (2026-10-21)

The branch-free form `regularizedHGFun_eq_besselExpansion` and the corrected Bessel form
`regularizedHGFun_besselJ_series` in `DLMF/Confluent/Series.lean` are original work. They use
Mathlib's formal power series derivative (`PowerSeries.derivative`) and
`PowerSeries.exp_mul_exp_eq_exp_add`, and the project's Neumann-series coefficient bounds
(`exists_norm_regularized0F1Coeff_le`, `exists_norm_recip_Gamma_add_nat_le`,
`norm_poch_le_factorial_mul_exp`). The telescoping certificate was found by hand after a sympy
ansatz.

## Reciprocal-Gamma strengthening (2026-10-21)

`DLMF/Gamma/RecipGammaDeriv.lean`, `DLMF/Hypergeometric/LogConnectionsRecipGamma.lean` and the
`_recipGamma` theorems in the Confluent and Legendre files are original project work. They use
Mathlib's `differentiable_one_div_Gamma`, `one_div_Gamma_eq_self_mul_one_div_Gamma_add_one`,
`Complex.digamma` and `iteratedDeriv`. No code was copied from other projects.

## Infrastructure round (2026-10-21)

The new files `DLMFMathlib/Analysis/Asymptotics/AsymptoticInversion.lean`,
`DLMFMathlib/Analysis/Integral/Improper.lean`, the five `ToMathlib/Analysis/ODE/LiouvilleGreen*.lean`
files, `DLMF/ParabolicCylinder/SectorAsymptotics.lean`, `DLMF/ParabolicCylinder/UniformLG.lean`,
`DLMF/Legendre/IntegralTools.lean` and the scripts `scripts/DumpDLMF.lean` and
`scripts/dlmf_ledgers.py` are original project work. No code was copied from other projects.
The mathematical sources are F. W. J. Olver, *Asymptotics and Special Functions*, Chapters 6,
10 and 11 (Liouville–Green error bounds), and DLMF §§11.5, 11.7, 12.9, 12.10, 14.6, 14.12 and
14.17. They use Mathlib's formal substitution and compositional inverse of power series
(`PowerSeries.subst`, `PowerSeries.substInvOfIsUnit`), `HasFPowerSeriesAt`, interval and
improper integrals, and the `@[dlmf]` cross-reference attribute
(`Mathlib/Tactic/CrossRefAttribute.lean`, by Damiano Testa), whose environment extension the
dump script reads. The rotated-contour results reuse the project's
`DLMFMathlib/Analysis/Asymptotics/WatsonRotated.lean`.

## Upstream pointers (2026-10-21)

The `dlmf_upstream` pointers record, without reproving them, results of Mathlib (172 pointers,
among them the Gamma, Beta, digamma, Bernoulli, zeta, Hurwitz zeta, Chebyshev, Hermite,
hypergeometric-series, AGM and Jacobi theta developments) and of TauCeti (6 pointers: real
`erf`/`erfc`, the regularized incomplete Gamma and Beta functions, and the Beta integral in
`TauCeti/Analysis/SpecialFunctions`). Ownership of those results stays with their libraries.

## Round 6 (2026-10-21)

The new files `DLMFMathlib/Analysis/ODE/LiouvilleGreenFinite.lean`,
`DLMFMathlib/Analysis/Complex/StarPrimitive.lean`, `DLMF/Confluent/KummerDecay.lean`,
`DLMF/IncompleteGamma/RealIntegrals.lean`, `DLMF/Legendre/BoundaryAsymptotics.lean`,
`DLMF/ParabolicCylinder/UniformLG2.lean` and `DLMF/Struve/AsymptoticTools.lean`, and the proofs
added in this round, are original project work. No code was copied from other projects. The
mathematical sources are DLMF Chapters 6, 8, 9, 11–15, F. W. J. Olver, *Asymptotics and Special
Functions* (Liouville–Green theory from a finite endpoint), and N. M. Temme, *Asymptotic
Methods for Integrals*. The proofs build on Mathlib's interval and improper integration, Cauchy
integral and identity-theorem APIs, and on the project's earlier ToMathlib layers (Watson's lemma on
rotated rays, parametric holomorphy, asymptotic power series).

## Round 7 (2026-10-21)

The new ToMathlib files `Analysis/Complex/ZeroLocalization.lean`,
`Topology/Order/ZeroEnumeration.lean`, `Analysis/ContinuedFraction/Convergence.lean`,
`Analysis/Asymptotics/StationaryPhase.lean` and `Analysis/Complex/BarnesResidue.lean`, the new DLMF
tool files and the proofs of this round are original project work, with these uses of other
work:

- The Rouché theorem, argument principle and zero-count tools of TauCeti
  (`TauCeti.Analysis.Complex.Conformal`, `TauCeti.Analysis.Complex.ZeroCount`) are used in
  `DLMF/ErrorFunctions/ZeroTools.lean`; the helper `erfZ_count_eq_single` there is adapted from a
  private TauCeti lemma (`count_eq_single`), as credited in the module header.
- The primitive argument in `DLMFMathlib/Analysis/Complex/BarnesResidue.lean` follows the approach
  of TauCeti's Perron formula development (`TauCeti/.../Perron/Basic`), as noted in its docstring.
- The continued-fraction theory builds on Mathlib's generalized continued fractions
  (`Mathlib/Algebra/ContinuedFractions`).

The mathematical sources are DLMF Chapters 6–9 and 11–15, the classical Pincherle theorem on
continued fractions and minimal solutions, and F. W. J. Olver, *Asymptotics and Special
Functions*.

## Round 8 (2026-10-21)

The new ToMathlib files `Analysis/Calculus/DoubleZeroSqrt.lean`,
`Analysis/Complex/MellinBarnesSeries.lean`, `Analysis/Integral/PrincipalValue.lean`,
`Analysis/ODE/SturmCount.lean` and `Analysis/ODE/SturmDeformation.lean`, the new DLMF tool files
`Airy/ErrorBoundTools.lean`, `Bessel/SphericalSeriesTools.lean` and
`SphericalHarmonics/AdditionTools.lean`, and the proofs of this round are original project work,
with these uses of other work:

- `harmonicHomogeneous_orthogonal` (`DLMF/SphericalHarmonics/Basic.lean`) uses TauCeti's polar
  decomposition `TauCeti.integral_eq_integral_Ioi_integral_toSphere`
  (`TauCeti.MeasureTheory.Constructions.HaarToSphere`); its private helper `hhOrth_eval_smul` is
  adapted from TauCeti's `MvPolynomial.IsHomogeneous.eval₂_const_mul`
  (`TauCeti/RingTheory/MvPolynomial/Homogeneous.lean`), as credited in the module header and the
  docstring. It also uses Mathlib's line-derivative integration by parts and Euler identity for
  homogeneous polynomials.
- `MellinBarnesSeries.lean` builds on the project's `BarnesResidue.lean` (round 7).
- `SturmCount.lean` builds on the project's `SturmComparison.lean` (Beals–Wong, Theorems 3.3.3,
  3.3.4 and 3.3.6).

The mathematical sources are DLMF Chapters 6–14 and 18, F. W. J. Olver, *Asymptotics and Special
Functions*, and G. E. Andrews, R. Askey and R. Roy, *Special Functions* (§9.8 for the Gegenbauer
addition theorem).

## Round 9 (2026-10-22)

The new ToMathlib files `Analysis/Asymptotics/StieltjesRemainder.lean` and
`Analysis/Calculus/InverseSeries.lean`, the new DLMF files `Airy/StieltjesForm.lean`,
`Bessel/KMellin.lean`, `Bessel/SphericalProductTools.lean`, `Gamma/ShiftedLineBounds.lean`,
`Legendre/ZeroTools.lean` and `SphericalHarmonics/ZonalTools.lean`, and the proofs of this round are
original project work, with these uses of other work:

- `SphericalHarmonics/ZonalTools.lean` uses TauCeti's Poisson integral on the ball
  (`TauCeti.Analysis.Complex.PoissonIntegral.Ball`, `poissonKernelBall_reproduces`) and its Laplacian
  API (`laplacian_eq_sum_fderiv_fderiv_apply`).
- The Mellin inversion step for 7.7.13–14 uses Mathlib's `mellinInv_mellin_eq`; Stirling-type
  inputs use Mathlib's `Real.GammaSeq_tendsto_Gamma` and the project's Binet integral.

The mathematical sources are DLMF Chapters 6–12, 14 and 18, F. W. J. Olver, *Asymptotics and
Special Functions*, G. Nemes (2017) on the Airy error bounds (as cited in DLMF 9.7(iv)), and
G. E. Andrews, R. Askey and R. Roy, *Special Functions* (§§9.6–9.7 for the addition theorem and
Funk–Hecke).

## Round 10 (2026-10-22)

The new ToMathlib file `Analysis/Complex/LagrangeBurmann.lean`, the new DLMF files
`Confluent/ZeroTools.lean`, `Legendre/ZeroCounts.lean`, `Legendre/AdditionTools.lean`,
`Hypergeometric/AppellF4.lean` and `SphericalHarmonics/BesselAddition.lean`, and the proofs of this
round are original project work. They use Mathlib's Cauchy integral formula for derivatives,
circle integrals and `HasFPowerSeriesOnBall.exchange_radius`, Mathlib's maximum modulus principle
(for the Hurwitz-type step in the Saff–Varga argument), and Carlson's theorem from
`ToMathlib/Analysis/Complex/Carlson.lean` (maintained in `../lean-codes`).

The mathematical sources are DLMF Chapters 9, 10, 13, 14, 16 and 18, G. E. Andrews, R. Askey and
R. Roy, *Special Functions* (§4.16, Saff–Varga parabolic regions; §9.6), W. N. Bailey's product
formula for Appell's F4, and L. Brafman's generating function for Jacobi polynomials.

## Round 11 (2026-10-22)

The new ToMathlib file `Analysis/SpecificLimits/Pincherle.lean`, the new DLMF files
`Core/ZeroCounting.lean`, `ErrorFunctions/ZeroClassification.lean`,
`ExpIntegrals/TransformTools.lean`, `IncompleteGamma/BoundTools.lean`,
`Legendre/QAdditionTools.lean`, `Legendre/FourierTools.lean` and `Struve/BarnesTools.lean`, and the
proofs of this round are original project work. They use TauCeti's Rouché theorem
(`TauCeti.Analysis.Complex.Conformal.Rouche`) and its incomplete-gamma API
(`TauCeti.Analysis.SpecialFunctions.IncompleteGamma`: `lowerIncompleteGamma`,
`regularizedGamma`), and Mathlib's Abel limit theorem, Stirling-type Gamma bounds and dominated
convergence.

The mathematical sources are DLMF Chapters 6, 7, 8, 11, 13 and 14; H. Alzer's bounds for the
incomplete gamma function (DLMF 8.10.11); Pincherle's theorem on minimal solutions and continued
fractions; and Tannery's theorem.

## Round 12 (2026-10-22)

The new ToMathlib file `Analysis/Asymptotics/LaplaceSaddle.lean`, the new DLMF files
`Hypergeometric/SpecialValueTools.lean` and `OrthogonalPolynomials/InequalityTools.lean`, and the
proofs of this round are original project work. They use Mathlib's Stirling formula, change of
variables and dominated convergence, and the project's Watson lemma, inverse-series and
Barnes-lemma results.

The mathematical sources are DLMF Chapters 8, 9, 13, 14, 15 and 18; L. Lorch's inequality for
ultraspherical polynomials (18.14.7); Kershaw-type Gamma-ratio bounds; the cubic transformations
and special values of Gessel–Stanton and Karlsson cited by DLMF §15.4; Erdélyi's product
integral (15.6.9); and N. M. Temme, *Special Functions* (Laplace and saddle-point methods for
§8.11).

## Round 13 (2026-10-22)

The new DLMF files `Airy/SquareTools.lean`, `Hypergeometric/CubicTools.lean`,
`ParabolicCylinder/ContourTools.lean` and `Struve/LargeOrderTools.lean`, and the proofs of this
round are original project work. They use Mathlib's Gronwall inequality, Cauchy's theorem for
rectangles, circle integrals, the Beta integral and dominated differentiation, TauCeti's real
error function, and the project's Watson lemma, saddle substitution and Barnes residue results.

The mathematical sources are DLMF Chapters 8, 9, 11, 12, 13, 14 and 15; Goursat's cubic
transformations of the hypergeometric function; and the representation of Ai² as an integral of Ai
(Reid; DLMF §9.11 context).

## Duplication review (2026-10-22)

The shared scalar-series helpers in `DLMFMathlib/Analysis/Complex/ScalarSeries.lean` consolidate
the existing project proofs using the Mathlib contributors'
`FormalMultilinearSeries.ofScalars_series_injective`,
`HasFPowerSeriesAt.eq_formalMultilinearSeries`, and
`hasSum_sum_range_mul_of_summable_norm`. The regularized Gauss boundary limit now combines
the project's `hasSum_regularizedGauss_one` with Mathlib's
`Complex.tendsto_tsum_powerSeries_nhdsWithin_lt`.

Both spherical-harmonic scaling helpers now import and apply the Tau Ceti contributors'
`MvPolynomial.IsHomogeneous.eval₂_const_mul` directly, from
`TauCeti.RingTheory.MvPolynomial.Homogeneous`, instead of repeating its proof.
The Poisson reproduction theorem reuses `zonal_poisson`, whose original Tau Ceti attribution
is retained. Gamma and Selberg integral holomorphy reuse the existing general
`Complex.differentiableOn_integral_of_locally_dominated` in `ToMathlib`.

## Parallel proof and reuse round (2026-10-24)

The lower incomplete-Gamma multiplication formula uses Mathlib's
`Complex.hasSum_taylorSeries_of_entire` and the project's existing regularized
confluent-hypergeometric derivatives. The associated Legendre degree derivative
reuses the existing regularized Gauss parameter-derivative series, generalized
from a real argument to its complex convergence disk.

The Stieltjes–Wigert orthogonality proof uses the Tau Ceti contributors'
`TauCeti.Probability.Distributions.LogNormal.Basic`, specifically
`integrable_pow_logNormalMeasure`, `integral_pow_logNormalMeasure`, and
`logNormalMeasure_eq_withDensity`, together with the project's finite q-binomial
identity. The little-q-Jacobi proof reuses the project's `QOrthogonalityTools`
moment and finite-sum lemmas. The q-Hahn proof reuses `DiscreteOrtho` finite
self-adjointness after proving the coefficient recurrence and Pearson balance.

The Goodwin–Staton proof reuses the project's Faddeeva Cauchy integral and
exponential-integral horizontal representation. Its passage to the positive
real axis uses Mathlib's dominated convergence theorem.

The incomplete-Gamma local inverse uses Mathlib's analytic inverse-function
theorem (`Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic`). Its global
inverse-series convergence uses `Complex.hasSum_taylorSeries_on_ball`; this last
result and the printed inverse-series coefficients still depend on the admitted
global inverse specification.

`DLMFMathlib/Analysis/ODE/SymmetricSquare.lean` generalizes the existing Airy
product calculation using Mathlib's derivative rules. It is original project
work and has no dependency on special-function modules.

The Meixner–Pollaczek moment proof reuses the project's two-Gamma Mellin–Barnes
integral and holomorphy estimates, the reverse Pochhammer basis from
`OrthogonalPolynomials/HahnMoments.lean`, and terminating Chu–Vandermonde. The
parabolic-cylinder product proof uses Mathlib's change-of-variables theorem for
the beta-integral initial value, the project's Gamma duplication/reflection formulas,
and the shared third-order uniqueness argument.

## Priority proof implementation (2026-10-24)

The global incomplete-Gamma inverse uses the Tau Ceti contributors'
`IsCoveringMapOn.of_isLocalHomeomorph_of_isCompact_preimage` from
`TauCeti.Topology.Covering.Proper`, with Mathlib's covering-space lifting theorem
in `Mathlib.Topology.Homotopy.Lifting` and contractibility of convex sets. This
closes the global inverse specification left open in the preceding round and
removes the inherited admissions from the Alpha-series convergence and printed
coefficients.

The shared complex Chebyshev-series module generalizes the project's previous
real proof using Mathlib's Fourier reconstruction and rectangular contour
integral. Compact cylinder expansions and the real Chebyshev API reuse it.
The shared parameterized Taylor-coefficient module extracts the existing
hypergeometric coefficient proof and uses Mathlib's circle-integral Cauchy
formula and differentiation under an interval integral.

Whipple's terminating transformation follows from the project's proved Watson
q-transformation by a finite `q → 1` limit. The Askey–Wilson difference equation
uses the existing q-Pochhammer finite basis. Fixed-argument incomplete-Beta
asymptotics reuse the regularized hypergeometric coefficient and Gamma APIs.
Inverse-erf's convergent series reuses the existing TauCeti real inverse and
Mathlib's analytic inverse/Taylor theory. The real Bi′ bound uses the proved
Airy differential equation, Gamma initial values, and a polynomial envelope.

## DLMF Chapters 4, 16 and 17 acquisition and Elementary proofs (2026-10-24)

The new chapter modules follow the NIST DLMF, version 1.2.8. Their acquisition
ledgers record exact formulas, analytical prose, exclusions, parameter domains,
branch conventions and source corrections. Existing project results retain their
original proofs and now carry the additional DLMF references where appropriate.

The Elementary catalog points directly to Mathlib's complex logarithm, exponential,
power, trigonometric and hyperbolic APIs, inverse-function calculus, exact values,
series, products and integrals. It also adopts the Tau Ceti contributors' inverse
hyperbolic and orthogonality APIs from `Analysis.SpecialFunctions.Artanh`,
`Analysis.SpecialFunctions.Hyperbolic` and
`Analysis.SpecialFunctions.Trigonometric.Orthogonality`. The new proofs use those
APIs and Mathlib's interval fundamental theorem, argument bounds and derivative
uniqueness; they preserve the acquired theorem statements. The exact positive-root
Bessel correspondence reuses the project's proved half-integer Bessel formula.

Generalized hypergeometric functions reuse Mathlib's regularized series and radii,
the Tau Ceti contributors' regularized contiguous identity, and the project's
classical identities. Their continuation interfaces use the Tau Ceti contributors'
`Analysis.Complex.Conformal.Continuation.Basic`. Residue expressions use
`TauCeti.Analysis.Contour.Residue.Basic`, authored by Chris Birkbeck, retaining
its AINTLIB attribution. Meijer contour and logarithmic-sheet statements are new
acquisitions, with their proof obligations explicit.

The q-hypergeometric development reuses the project's q-Pochhammer, q-binomial,
Heine, q-Gamma, Jackson calculus and Bailey APIs. Checked upstream coverage also
uses Mathlib's complex Dedekind-eta transformation and ordinary binomial theorem.
Analytic continuation uses TauCeti's path-continuation API directly. The corrected
Karlsson and bibasic sums are checked against Gasper–Rahman's *Basic Hypergeometric
Series*, Eq 1.9.7, and Gasper's 1995 q-series lectures, Eq 4.1.23; exact rational
counterexamples to the printed DLMF versions are proved in Lean. The constant-term
correction in 17.14.E3 follows by expanding its displayed Jacobi numerator.

`DLMFMathlib/Analysis/ODE/Singularities.lean` and
`DLMFMathlib/Analysis/Complex/SeparatingContour.lean` supply general predicates using
Mathlib only. They have no admissions and no special-function dependency.

## Second parallel Chapter 4/16/17 proof round (2026-10-24)

The 92 Elementary proofs reuse Mathlib's principal logarithm and power calculus,
trig/hyperbolic inverse identities, exact values, limits and exponential estimates.
The ODE formulas use Mathlib's constancy theorem for zero derivatives on connected
open sets and ordinary derivative/product rules. Hyperbolic branch calculus reuses
the project's now-proved principal inverse-sine API through rotation, preserving
all cut and sign conditions.

The Chapter 16 coefficient and radius proofs use Moritz Doll's
`Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric` and Mathlib's Gamma,
polynomial and scalar-series APIs. Private finite-product normalization/ratio
lemmas are adapted with their 2026 Moritz Doll copyright and explicit attribution
in the module header and at use; the positive-degree divergence extension is local
work. The 0F1 adapter directly applies the Tau Ceti contributors' regularized
contiguous identity. The guarded principal-function definition has an explicit
old-definition equivalence under the retained continuation-existence admission.

The 28 q-series proofs reuse the project's QSeries shifted-factorial, Gaussian,
q-binomial and Jackson APIs and Mathlib's product limits and ratio-test series
convergence. The new generic qPhi summability proof preserves DLMF's integer phase
and its full convergence domains. No copied TauCeti proof or new axiom is introduced.

## Third parallel Chapter 4/16/17 proof round (2026-10-24)

`DLMFMathlib/Analysis/SpecialFunctions/Complex/LogBoundary.lean` adapts Michael
Stoll's 2023 Mathlib integral-remainder proof of `Complex.norm_log_sub_logTaylor_le`.
A compact-path inverse bound replaces its open-disk geometric bound. The source
retains his copyright and authorship. The six DLMF adapters use natural partial
sums, finite odd-term grouping and Mathlib's principal exponential-strip identities.

The complex binomial adapter directly reuses Mathlib's
`Complex.one_add_cpow_hasFPowerSeriesOnBall_zero`, generalized binomial and
Pochhammer-polynomial APIs. Logarithm-sheet derivatives use
`iteratedDeriv_succ_log`; full complex-power derivatives use local derivative
congruence on the slit plane. The elementary limits, inequalities, primitives and
improper integral reuse Mathlib's power/log asymptotics, exponential remainder,
derivative rules and improper fundamental theorem. Complete trig/hyperbolic fibers
use Mathlib's sine/cosine equality and period APIs. Branch-set corrections use
explicit logarithm lifts and paired sinh/cosh identities, with no parameter loss.

Chapter 16 finite inversions reuse the proved local `poch_one_sub_sub_mul` and
`poch_ne_zero_of_le`, plus Mathlib's
`Nat.descFactorial_eq_factorial_mul_choose`. The integer-index Gamma bridge
extends `Complex.Gamma_add_nat_div_Gamma_eq`, handling shifted poles explicitly.
Odd Dixon follows from finite inversion; normalized bilateral Dougall reuses the
proved local `dougall_bilateral` and Mathlib's Gamma reflection formula without
strengthening lower-parameter exclusions. The raising operator uses Mathlib's
`iteratedDeriv_fun_mul`, `iteratedDeriv_fun_id` and analytic germ APIs. Nominal
order uses `Polynomial.natDegree_multiset_prod_of_monic` and `monic_X_add_C`,
including empty parameter multisets. No external proof body was copied.

The qPhi power-series/Taylor API directly uses Mathlib's
`FormalMultilinearSeries.ofScalars`, `le_radius_of_tendsto`, scalar-series
uniqueness and change-of-origin analyticity. Moving the proved `zero_phi_zero`
adapter from BasicSummations into Basic preserves its declaration and 17.5.E1
tag while avoiding an import cycle. The q-elementary expansions reuse the proved
Heine/Euler q-series, `HasSum.even_add_odd` and injective subsequences; explicit
q=0 cases preserve all original domains.

The Gaussian bridges reuse the proved QSeries finite q-binomial formula, local
q-Pochhammer reversal, the exact integer triangular identity and Mathlib's integer
power laws. No nonzero upper Pochhammer factor is canceled. Product continuation
applies analytic composition/division to the proved entire q-Pochhammer product,
then uses the pure Tau Ceti contributors' `ContinuesInside` germ adapter. Series
values are identified with the product on the convergent disk/germ only. No
TauCeti proof source was copied, and no new axiom or dependency was introduced.

## Fourth parallel Chapter 4/16/17 proof round (2026-10-24)

Hyperbolic real antiderivatives and derivatives use TauCeti's
`TauCeti.Analysis.SpecialFunctions.Artanh` (`Real.hasDerivAt_artanh`). The scaled
Dirichlet integral uses TauCeti's `TauCeti.Contour.tendsto_integral_sin_mul_div_atTop`
(`TauCeti.Analysis.Contour.WorkedExamples.HalfDisc.SineIntegral`). The two Chapter 16
Barnes residue theorems use `TauCeti.Contour.residue_eq_of_eventuallyEq_zpow_smul`.
Appell double-series analyticity uses `TauCeti.Analysis.Complex.CauchyIntegralPolydisc`,
and `appell_continuation_unique` adapts the one-variable TauCeti arguments
`IsAnalyticContinuationAlong.eventuallyEq` and `eventually_eventuallyEq_iff_of_analyticAt`
to two variables, with inline attribution.

Within the project, the Lambert W Maclaurin series reuse the Lagrange–Bürmann theorem of
`DLMFMathlib/Analysis/Complex/LagrangeBurmann.lean` (`lagB_hasSum_iteratedDeriv`,
`lagB_hasSum_of_differentiableOn`). The new `DLMFMathlib/Analysis/Complex/TrigR4SeriesExtension.lean`
adapts the coefficient-uniqueness argument of the local `scalarSeries_unique_ball`.
The 0F1 product formula uses Chu–Vandermonde; the logarithm integrals
`integral_log_div_one_sub/add` reuse the local `DLMF.Polylog.Real.dilog_one` and
`dilog_neg_one`. Chapter 17 summations reuse the project's QSeries Heine transformation
and the Bailey-lemma API (`DLMF.Bailey.bailey_relation`, `watsonR`,
`bailey_limit_relation`); two private limit helpers in `BaileyPairs.lean` copy private
helpers of `DLMF/QSeries/Bailey.lean`. No other external proof body was copied.

## Chapters 20–23 acquisition (2026-10-25)

The theta chapter builds on Mathlib's `jacobiTheta₂` and `jacobiTheta` APIs
(`Mathlib/NumberTheory/ModularForms/JacobiTheta/*`: quasi-periodicity, parity,
differentiability, the functional equation) and the project's Jacobi triple product
(`DLMF/QSeries`). The Riemann theta chapter uses Mathlib's `Matrix.PosDef`, `Matrix.J`
and `Matrix.symplecticGroup`. The Weierstrass chapter is stated on Mathlib's `PeriodPair`
with its `weierstrassP`, `derivWeierstrassP`, `G`, `g₂`, `g₃` and differential equation
(`Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.lean`), and the modular-function
section uses Mathlib's `ModularForm.eta` and `ModularForm.discriminant`. No external proof
body was copied.

## lean-codes as a Lake dependency (2026-10-25)

With the user's approval, the companion project lean-codes (Bastiaan J Braams; package
`LeanCodes`, path `../lean-codes`) is a Lake dependency. Its two former mirrors
(`ToMathlib/Analysis/Integral/Laplace.lean`, `ToMathlib/Analysis/Complex/Carlson.lean`) are
imported from it, and the Chapter 19 acquisition builds on its Carlson library: the
R-function, `carlsonRF`, `carlsonRG`, `carlsonRC`, Legendre-form bridges, duplication,
Landen/AGM, quartic reduction and asymptotics, formalized from B. C. Carlson, *Special
Functions of Applied Mathematics* (1977). Its proofs are used through imports, not copied.

## Proof round 1 for Chapters 19–23 (2026-10-25)

Chapter 19 proofs reuse the lean-codes Carlson library (Bastiaan J Braams, after B. C. Carlson)
through imports: `Carlson.hasSum_agmA_zero`, `Carlson.carlsonRE_eq_agm`,
`Carlson.TwoVariable.carlsonRK_sq_eq_inv_agm` (AGM forms of E and K), `Carlson.R.Homogeneity`,
`Carlson.R.BinomialSeries` and `Carlson.RPolynomial.Generating` (19.19.2),
`Carlson.Elliptic.ReductionTables`, `Carlson.TwoVariable.GaussHypergeometric`,
`Carlson.TwoVariable.R.ElementaryValues` and the Landen modules. Chapter 23 uses Mathlib's
`PeriodPair.derivWeierstrassP_sq`, the Dedekind eta API and the level-one graded ring for the
discriminant; Chapter 20 uses Mathlib's `logDeriv_tprod_eq_tsum`, the Eisenstein-series summability
lemmas (`EisensteinSeries.summable_one_div_norm_rpow`, `r_mul_max_le`) and
`hasSum_mellin_pi_mul`; the Chapter 22 real bridges use `Mathlib.Analysis.ODE.ExistUnique`. The
polynomial certificates in the p = 3 cyclic identities of `DLMF/JacobiElliptic/Cyclic.lean` were
computed with the Singular computer-algebra system and are checked by Lean's `linear_combination`.
No external proof body was copied.

## Chapters 24–27 acquisition and proof round 1 (2026-10-25)

The Chapter 24–27 areas build on Mathlib's Bernoulli, zeta, L-series, arithmetic-function,
character, combinatorics and partition libraries (recorded with `dlmf_upstream` pointers); the
proofs use, among others, Mathlib's `Bernoulli.vonStaudt_clausen` (24.10.1), `LSeries_iteratedDeriv`,
`hasSum_mellin`, the Hurwitz-zeta functional equations, `Real.one_add_rpow_hasFPowerSeriesOnBall_zero`
(the Catalan generating function), `DomMulAct.stabilizer_card` (multiset permutations) and Korselt's
criterion `Nat.IsCarmichael`. From the companion project lean-codes (Bastiaan J Braams),
`Pochhammer.PochhammerTransform` (`coeff_ascPochhammer`) is imported in
`DLMF/BernoulliEuler/RelatedNumbers.lean` (24.15.8) and `DLMF/Combinatorics/MathlibCoverage.lean`.
From TauCeti, `TauCeti.Combinatorics.Enumerative.Partition.Conjugate` (conjugate partitions) is
imported in `DLMF/Combinatorics/RestrictedPartitions.lean` (26.9). The coefficients of the
generating-function certificates for 24.14.8–10 were found with sympy and are checked by Lean's
`linear_combination`. No external proof body was copied.

## Proof round 2 for Chapters 24–27 (2026-10-25)

The round-2 proofs use, among others, Mathlib's `Equiv.Perm.decomposeFin'` (the Eulerian insertion
recurrence 26.14.8), `Ring.descPochhammer_smeval_add` (Vandermonde for falling factorials, 26.8.19),
the pentagonal number theorem in `Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries`
(26.10.7, 27.14.6), the harmonic-number bounds of `Mathlib.NumberTheory.Harmonic.Bounds` and the
zeta values of `Mathlib.NumberTheory.ZetaValues` (27.11.4, 27.11.6–7), the trigonometric series of
`Mathlib.Analysis.SpecialFunctions.Trigonometric.Series` (24.11.5–6) and the binomial series of
`Mathlib.Analysis.Analytic.Binomial` (24.16.5–7). No external proof body was copied.

## Proof round 3 for Chapters 24–27 (2026-10-26)

From TauCeti, `TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Bialternant`
(`TauCeti.diagramSchurPoly_mul_alternant`, the Jacobi bialternant formula) is imported in
`DLMF/Combinatorics/PlanePartitions.lean` for MacMahon's box formula (26.12.4, 26.12.21), and
`TauCeti.GroupTheory.Perm.SwapFactors` (`Equiv.Perm.isLeast_card_sub_orbitCount`) in
`DLMF/Combinatorics/Permutations.lean` for the minimal transposition factorization (§26.13). The
round also uses Mathlib's `Chebyshev.psi_le_const_mul_self` (Mertens 27.11.8, 27.11.10), Euler's
sine product `EulerSineProd` (25.8.8), `Complex.hasSum_taylorSeries_on_ball` and the Tannery theorem
(25.2.4, 24.16.9), and `DifferentiableOn.isExactOn_ball` (the logarithm in 24.16.9). The
Rogers–Ramanujan partition identities 26.10.13–14 are derived from the project's own
`DLMF.Bailey.rogers_ramanujan_first` and `rogers_ramanujan_second`. No external proof body was copied.

## Ramanujan's τ and the prime number theorem (2026-10-26)

Ramanujan's τ (DLMF/NumberTheory/Partitions.lean, with the general Hecke recursion helpers in
DLMF/NumberTheory/T27bHecke.lean): multiplicativity (§27.14(vi)), 27.14.19 and the congruence
τ(n) ≡ σ₁₁(n) (mod 691) (27.14.20) use TauCeti's
`TauCeti.ModularForms.LevelOne.DiscriminantEigenform`
(`TauCeti.ModularForm.discriminant_qExpansion_coeff_mul`,
`TauCeti.ModularForm.discriminant_qExpansion_coeff_prime_pow_add_two`) and Mathlib's
`CuspForm.exists_smul_discriminant_of_weight_eq_twelve` (E₁₂ − E₆² = cΔ, from
`Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula`),
`ModularFormClass.qExpansion_coeff_unique`, `ModularForm.discriminant_qExpansion_coeff_one`,
`EisensteinSeries.E_qExpansion_coeff`, `ModularForm.qExpansion_pow`, `qExpansion_smul` and
`qExpansion_sub`.

The prime number theorem (DLMFMathlib/NumberTheory/T27aPrimeNumberTheorem.lean; 27.2.3, 27.2.4,
27.12.1 and primes in arithmetic progressions, §27.11) specializes TauCeti's prime ideal theorem
and natural-density Chebotarev theorem to ℚ:
`TauCeti.NumberTheory.ArithmeticDirichletSeries.Prime.PrimeIdealTheorem`
(`TauCeti.primeIdealTheorem`, `TauCeti.primeCount_univ_isEquivalent_div_log`,
`TauCeti.primeCount_eq_card`, `TauCeti.primeTheta_apply`, `TauCeti.primesLE`,
`TauCeti.mem_normLE`, `Rat.HeightOneSpectrum.absNorm_asIdeal`,
`Rat.HeightOneSpectrum.exists_absNorm_eq`) and
`TauCeti.NumberTheory.Chebotarev.PrimeCounting.PrimesCongruent`
(`NumberField.Chebotarev.tendsto_primeCount_primesCongruent`), with Mathlib's
`Rat.HeightOneSpectrum.primesEquiv`, `natGenerator`, `prime_natGenerator` and
`Chebyshev.isBigO_psi_sub_theta_sqrt` (ψ(x) ~ x from θ(x) ~ x). No external proof body was copied.
