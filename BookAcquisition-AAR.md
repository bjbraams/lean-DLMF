# Andrews–Askey–Roy acquisition audit

The approved follow-up has corrected this book’s SYNOPSIS and ERRATA records.
The acquisition evidence below is retained as a historical audit; references to
unchanged synopsis text or blocked defective variants describe that snapshot.
Current per-item dispositions are in BookAcquisition-RevisionNotes.md.

Source: *Special Functions* (1999); stable entry identifiers refer to
[SYNOPSIS-AAR.md](SYNOPSIS-AAR.md). The synopsis is unchanged.

The grouped audit covers all 85 synopsis entry groups, including the numbered Theorem
census and their valid mathematical subclaims. “Present” distinguishes checked proofs
from existing admissions. Restricted existing results are paired with the fuller newly
acquired targets where required. New admitted statements are acquisition targets, never
completed proofs. Confirmed false source/synopsis variants are explicitly deferred below;
the synopsis and existing tagged theorem statements are unchanged.

Pinned search order: Mathlib, TauCeti, then DLMF. Dependencies remain unchanged.

## Entry ledger

### AAR-1.1.1–1.1.5: gamma and beta

- Mathlib: `Complex.GammaSeq_tendsto_Gamma`, `Gamma_add_one`, `Gamma_one`,
  `Gamma_eq_integral`, `Gamma_ne_zero`, `differentiable_one_div_Gamma`,
  `betaIntegral`, `betaIntegral_eq_Gamma_mul_div`; `Real.tendsto_harmonic_sub_log`.
- Pinned TauCeti `Gamma/Order.lean`: `Complex.tendsto_add_natCast_mul_Gamma`,
  `meromorphicOrderAt_Gamma_neg_nat`, `analyticOrderAt_inv_Gamma_neg_nat` (proved).
- Existing proved `DLMF.Gamma.one_div_Gamma_eq_tprod`,
  `multipliable_weierstrassGammaTerm`, `tendsto_weierstrassGamma_prod`.
- Newly admitted local uniform refinements: `DLMF.Gamma.tendstoLocallyUniformlyOn_GammaSeq`,
  `tendstoLocallyUniformly_weierstrassGamma_prod` (`ProductsUniform.lean`).
- Beta symmetry: proved Mathlib `Complex.betaIntegral_symm`. The half-line formula
  is proved `Complex.integral_cpow_div_one_add_cpow` in
  `DLMFMathlib/Analysis/SpecialFunctions/Gamma/BetaHalfLine.lean`, including integrability
  `Complex.integrableOn_cpow_div_one_add_cpow`. The two explicit unit-shift quotients
  follow by the checked gamma-quotient/`Complex.Gamma_add_one` adapter in
  `/tmp/AAR-small-derivations-audit.lean` (positive real parts).

### AAR-1.2.1–1.2.7: reflection, Bernoulli numbers and digamma (pp. 9–14)

- Mathlib `Complex.Gamma_mul_Gamma_one_sub`, `Complex.tendsto_euler_sin_prod`,
  `Complex.cot_series_rep`; Bernoulli definitions/generating function:
  `bernoulli`, `Polynomial.bernoulli`, `Polynomial.bernoulli_generating_function`,
  `bernoulli_eq_zero_of_odd`; log-convexity `Real.convexOn_log_Gamma`.
- Existing proved `DLMF.Gamma.deriv_Gamma_one`, `digamma_eq_cDigammaSeries`,
  `polygamma_eq_tsum`, `digamma_rat`; upstream `Complex.digamma_one`,
  `digamma_apply_add_one`.
- The full even-zeta identity is proved Mathlib `hasSum_zeta_nat`. Strict log-gamma
  convexity is proved `DLMF.Gamma.strictConvexOn_log_Gamma`. Both pass axiom audit.
- Newly admitted `Complex.hasSum_one_div_add_intCast_sq`,
  `tendstoLocallyUniformly_euler_sin_prod`, `tendstoLocallyUniformlyOn_cot_series`,
  `tendstoLocallyUniformlyOn_one_div_add_intCast_sq` in
  `DLMFMathlib/Analysis/SpecialFunctions/Trigonometric/LatticeExpansions.lean`
  retain local uniformity and the full pole complement.

### AAR-1.3.1–1.3.4: Hurwitz and Riemann zeta (pp. 15–18)

- Mathlib `riemannZeta`, `zeta_eq_tsum_one_div_nat_cpow`, `riemannZeta_residue_one`,
  `riemannZeta_one_sub`, `completedRiemannZeta_one_sub`.
- Existing proved `DLMF.Zeta.hurwitzZetaComplex_neg_nat` and
  `deriv_hurwitzZetaComplex_zero` (`Hurwitz/ValuesAndDerivatives.lean`).
- Exact Hurwitz shifts: `hurwitzZetaComplex_eq_add_one`, `hurwitzZetaComplex_eq_add_nat`;
  holomorphy/residue: `differentiableAt_hurwitzZetaComplex`,
  `hurwitzZetaComplex_residue_one` in `Hurwitz/SeriesAndContinuation.lean`.
  Mathlib `riemannZeta_zero` and `riemannZeta_neg_two_mul_nat_add_one` give the zero and
  negative-even values directly. Mathlib `deriv_riemannZeta_zero` gives the exact
  derivative at zero directly, without a Hurwitz normalization adapter.

### AAR-1.4.1–1.4.5: Stirling expansion (pp. 18–22)

- Existing proved real/ray statements: `DLMF.Gamma.tendsto_Gamma_div_stirling`,
  `Gamma_ratio_power`, `norm_Gamma_imag_large` and the coefficient API in `Asymptotics/`.
- New shared Temme acquisitions `DLMF.Gamma.logGamma_stirling_sector`,
  `scaledGamma_sector_expansion`, `inv_scaledGamma_sector_expansion`,
  `gammaStirlingCoeff_recurrence` in `SectorExpansions.lean` retain full closed sectors.
- Exact periodic-Bernoulli remainder and signed first-omitted-term bound: shared new
  admitted `logGammaStieltjesRemainder_eq_integral`,
  `norm_logGammaStieltjesRemainder_le`, `logGammaStieltjesRemainder_sign_and_norm_lt`.
  The exact periodic-B-only form, with its combined elementary terms and explicit
  integrability, is newly admitted `logGamma_eq_sum_sub_periodicBernoulli_integral`
  in `Gamma/PeriodicStirlingRemainder.lean`.
- Newly admitted `tendstoUniformlyOn_norm_Gamma_vertical_div` in
  `Gamma/VerticalStripAsymptotics.lean` gives the exact leading constant and uniformity
  in the real part on any compact interval, simultaneously as `t→+∞` and `t→−∞`.
  The complex phase expansion is obtained directly from the full sector logarithmic
  expansion; no magnitude-only theorem is used as a phase identity.

### AAR-1.5.1–1.5.2: multiplication (pp. 22–25)

- Duplication: Mathlib `Complex.Gamma_mul_Gamma_add_half`.
- General multiplication: existing proved `DLMF.Gamma.Gamma_prod_add_div`,
  `Gamma_mul_nat`; rational product: `DLMF.Gamma.Real.prod_Gamma_div`
  (`Gamma/Multiplication.lean`).

### AAR-1.6.1–1.7.1: logarithmic integral and Fourier formulas (pp. 26–31)

- Newly admitted in `Gamma/IntegralRepresentations/JointComplex.lean`, namespace
  `DLMF.Gamma`: `digamma_integral_algebraic`, `digamma_integral_exponential`,
  `logGamma_integral_malmsten`, `logGamma_integral_binet_exponential`,
  `logGamma_integral_binet_arctan`. Each includes integrability of the combined
  integrand; the logarithm is canonical `TauCeti.logGamma`.
- Existing proved positive-real Binet cases: `DLMF.Gamma.log_Gamma_binet_exp`,
  `log_Gamma_binet_arctan`.
- Newly admitted full Kummer Fourier formula:
  `DLMF.Gamma.Real.tendsto_sum_log_Gamma_sine` (`KummerFourier.lean`). Ordered partial
  sums, not unconditional `HasSum`, retain conditional convergence.

### AAR-1.8.1–1.8.6: Dirichlet integrals (pp. 32–34)

- Theorem 1.8.1 and 1.8.6: existing proved `DLMF.Gamma.dirichlet_simplex` and
  `dirichlet_simplex_full` (coordinate measure, not hypersurface area).
- Corollaries 1.8.2–1.8.4: new admissions `DLMF.Gamma.integral_power_simplex`,
  `volume_ellipsoid` in `Gamma/Multidimensional/Liouville.lean`.
- Theorem 1.8.5 and its measurable extension: new admissions `integral_liouville`,
  `integral_liouville_of_integrable` in the same module. Positive coordinate scales,
  power exponents and real parts are explicit; the shell requires positive dimension.

### AAR-1.9.3–1.9.4: characterizations (pp. 34–36)

- Bohr–Mollerup: Mathlib `Real.eq_Gamma_of_log_convex` (proved).
- Theorem1.9.4: newly admitted `DLMF.Gamma.Real.eq_Gamma_of_tendsto_ratio` in
  `Gamma/Characterizations.lean` retains positivity, normalization, functional equation
  and every positive-real translation ratio.

### AAR-1.10.1–1.10.11: characters and Gauss/Jacobi sums (pp. 36–43)

- Theorem 1.10.1 / Corollary 1.10.2: new admitted `Complex.character_real_eq_exp`,
  `character_pos_eq_cpow` (`DLMFMathlib/Analysis/SpecialFunctions/Exp/Characters.lean`).
  The trivial character is included and positive-ray continuity is explicit.
- Gauss/Jacobi definitions are Mathlib `gaussSum`, `jacobiSum`, with the required
  zero extension through `MulChar`, including the trivial character.
- Theorem 1.10.7: Mathlib `jacobiSum_one_nontrivial`, `jacobiSum_one_one`,
  `jacobiSum_nontrivial_inv`, `jacobiSum_eq_gaussSum_mul_gaussSum_div_gaussSum` (proved).
- Gauss shift: Mathlib `gaussSum_mulShift_eq`; norm: pinned proved `TauCeti.norm_gaussSum`.
  The explicit Jacobi norm adapter `norm_jacobiSum` is proved in
  `DLMFMathlib/NumberTheory/JacobiSum/Norm.lean` from Mathlib's quotient formula
  and the three pinned TauCeti Gauss norms. The book's nontrivial additive character
  is primitive over a field by Mathlib `AddChar.IsPrimitive.of_ne_one`.
- Corollary 1.10.10: Mathlib `Nat.Prime.sq_add_sq` (proved).
- Theorem 1.10.11: new `multipleJacobiSum` with proved defining sum and admitted
  `multipleJacobiSum_eq_prod_gaussSum_div` in `DLMFMathlib/NumberTheory/JacobiSum/Multiple.lean`.
- DFT double transform: Mathlib `ZMod.dft_dft` (proved), with sign convention adapter.
  Character orthogonality follows from Mathlib `MulChar.sum_eq_zero_of_ne_one`
  and `sum_one_eq_card_units`, applied to the quotient character. The explicit finite
  Parseval target `ZMod.sum_dft_mul_conj_dft` is newly admitted in
  `DLMFMathlib/Analysis/Fourier/FiniteParseval.lean`; `sum_norm_dft_sq` is its corollary
  and therefore depends on that admission. Frequency reflection reconciles the signs.

### AAR-1.11–1.12: probability and the p-adic gamma function (pp. 43–46)

- New foundational `DLMF.Gamma.padicGammaInteger`, `padicGamma`, with proved
  defining equations (`Gamma/Basic/PadicGamma.lean`). The extension uses the canonical
  `PadicInt.appr` sequence, not an unspecified chosen interpolation.
- Seven new admissions (`Gamma/PadicGamma.lean`): `tendsto_padicGammaInteger_appr`,
  `padicGamma_natCast`, `continuous_padicGamma`, `isUnit_padicGamma`,
  `padicGamma_add_one`, `padicGamma_congr`, `eq_padicGamma_of_continuous`.
- Exact proved pinned TauCeti order-statistic laws:
  `TauCeti.Probability.map_orderStatistic_pi_uniformMeasure` and
  `hasLaw_orderStatistic_iid_uniformMeasure`, in
  `Probability/Distributions/OrderStatistic/Basic.lean`. Both pass axiom audit.
  The index is zero-based: beta shapes are `k+1,n-k`. The factorial density is a
  checked simplification of `ProbabilityTheory.betaPDFReal` using
  `Real.Gamma_nat_eq_factorial`; `/tmp/AAR-order-statistic-audit.lean` checks this.
  `ProbabilityTheory.isProbabilityMeasureBeta` supplies total mass one.

### AAR-2.1.1–2.1.5: series, convergence and singular behavior (pp. 61–65)

- Canonical series and continuation: `DLMF.Hypergeometric.generalizedHypergeometric`,
  `regularizedHGFun`, and the principal Gauss APIs.
- Existing proved convergence classification in `GeneralizedHypergeometric/AnalyticProperties`:
  `generalizedHypergeometric_entire`, `generalizedHypergeometric_radius_one`,
  `generalizedHypergeometric_radius_zero`, `generalizedHypergeometric_unit_absolute_iff`,
  `generalizedHypergeometric_unit_conditional`, `generalizedHypergeometric_unit_diverges`,
  `generalizedHypergeometric_one_converges_iff` (namespace `DLMF.Hypergeometric`).
- Power endpoint limit is existing proved
  `DLMF.Hypergeometric.tendsto_ordinaryHypergeometric_nhdsWithin_one`
  (`Continuation.lean`). Zero-excess logarithm is shared newly admitted
  `tendsto_regularizedGaussHypergeometric_div_log_left_one` (`EndpointLogarithm.lean`).
- Full principal-cut higher derivatives are proved
  `iteratedDeriv_regularizedGaussHypergeometric` (`Basic/CutPlane.lean`), with no
  exceptional lower-parameter exclusion in this regularized normalization.
- Newly admitted partial-sum asymptotics:
  `tendsto_sum_gaussHypergeometricCoeff_div_cpow` and
  `tendsto_sum_gaussHypergeometricCoeff_div_log` (`EndpointPartialSums.lean`).
  Both retain terminating upper parameters as zero normalized limits.

### AAR-2.2.1–2.2.7: beta integrals and elementary transformations (pp. 65–72)

- Existing proved principal transformations:
  `DLMF.Hypergeometric.pfaff_transformation_of_ne_neg_nat`,
  `euler_transformation_of_ne_neg_nat` (`Continuation.lean`).
- Existing proved beta transform `DLMF.Hypergeometric.fractional_integral`
  (`IntegralRepresentations.lean`), on its stated convergence disk.
- New finite-only denominator forms, shared with Duverney:
  `DLMF.Hypergeometric.sum_pochhammer_mul_neg_nat_div`,
  `pfaff_saalschutz_of_finite_regular` (`TerminatingSummations.lean`, admitted).
- Euler integral on the full cut is proved
  `regularizedGaussHypergeometric_eq_regularizedGaussHypergeometricIntegral` in
  `Basic/CutPlane.lean`; boundary Gauss value is proved
  `tendsto_regularizedGaussHypergeometric_left_one` in `Boundary.lean`.
  Newly admitted `regularizedGaussHypergeometric_eq_beta_integral` in
  `PrincipalBetaTransform.lean` extends the fractional beta transform to the full
  principal cut plane, including explicit integrability of its weighted integrand.

### AAR-2.3.1–2.3.3: Riemann equation and connection coefficients (pp. 73–84)

- Papperitz operator and local solution-space definitions:
  `DLMF.Hypergeometric.riemannOperator`, `riemannSolutions`, `riemannNormalOperator`.
  Existing proved `gauss_fuchs_relation`, `riemannNormalOperator_gauss`,
  `riemann_hypergeometric_solution`, `riemann_gauge_shift`, `riemann_mobius_covariance`.
- Connection at one: existing proved `zero_first_connection_one`,
  `zero_second_connection_one`, `one_first_connection_zero`, `one_second_connection_zero`
  in `Hypergeometric/Solutions/Connections.lean`, initially on the common lens.
- Logarithmic exceptional connections are already in `ConnectionFormulas.lean`.
- Shared new `Complex.exists_partial_fractions_of_linearODEAtMostRegularAtInfinity`
  gives the rational Fuchsian classification, and its infinity conditions encode Fuchs's relation.
- Exact coefficient uniqueness is shared newly admitted
  `Complex.eq_papperitz_coefficients_of_regularSingular` in
  `DLMFMathlib/Analysis/ODE/FuchsianClassification.lean`; expanding its three finite
  sums gives precisely the existing `riemannOperator` coefficients.
- Shared newly admitted `regularizedGaussHypergeometric_connection_inv`,
  `regularizedGaussHypergeometric_connection_one_sub`, their quotient formulas and
  parameter limits in `PrincipalConnections.lean` cover the whole common principal
  domains. `RiemannSolutionSpaces.lean` gives actual linear maps and bijections for
  Möbius, gauge, and cross-ratio/Gauss transformations.
- The terminating reflected specialization is newly admitted
  `terminating_gauss_one_sub_of_finite_regular` in `FiniteBalancedTransformations.lean`.

### AAR-2.4.1–2.4.6: Barnes representations and finite sums (pp. 85–94)

- Theorem 2.4.1: existing proved `DLMF.Hypergeometric.barnes_integral` is initially
  negative real −1<x<0; existing admitted `generalizedHypergeometric_barnes_vertical`
  and `generalizedHypergeometric_barnes_right` cover the general contour/principal sector.
  Shared new `regularizedGaussHypergeometric_eq_barnesContour`,
  `isIntegrable_barnesIntegrand`, `tendstoLocallyUniformlyOn_barnesContour` in
  `Hypergeometric/BarnesContours.lean` give the regularized full-cut function on
  actual deformed contours, without an artificial lower-parameter exclusion.
- Theorem2.4.2: existing proved `DLMF.Gamma.mellin_barnes_four`; shared newly admitted
  `barnes_first_lemma_contour` and `isIntegrable_barnes_first` in `Gamma/BarnesContours.lean`
  give the actual deformed-contour extension of Barnes's first lemma.
- Theorem 2.4.3: new admitted `DLMF.Gamma.barnes_second_lemma` in `BarnesSummations.lean`
  asserts integrability and the exact value on every separating vertical line.
  New admitted `barnes_second_lemma_contour` in `Gamma/Integrals/BarnesDeformations.lean`
  gives every finite pole-separating deformation with vertical tails.
- Theorems2.4.4–5: new admitted
  `generalizedHypergeometric_threeFTwo_two_term` and
  `generalizedHypergeometric_threeFTwo_balanced_two_term` in
  `GeneralizedHypergeometric/TwoTermConnections.lean` give the literal two-term formula
  and its balanced Gauss specialization. These are the displayed nonresonant formulas;
  resonant gamma-factor parameter limits remain a separate continuation adapter.
- Theorem 2.4.6: new admitted `DLMF.Hypergeometric.bailey_finite_sum_reciprocity`
  in `FiniteReciprocity.lean`, with finite denominator regularity and retained-term cutoffs.

### AAR-2.5: contiguous relations and Jacobi definition (pp. 94–102)

- Existing proved `DLMF.Hypergeometric.contiguous_a` and regularized contiguous
  relations in `Hypergeometric/Continuation.lean` (initial disks).
- Regular Jacobi definition: `DLMF.OrthogonalPolynomials.jacobiPolynomialP`.
- Polynomial continuation at every parameter: new `jacobiExtended`, with proved
  unfolding/degree-zero API; bridge `jacobiExtended_eq_jacobiPolynomialP` proved
  for `-1 < Re α`. Shared newly admitted
  `jacobiExtended_eq_jacobiPolynomialP_of_not_neg_nat` (`JacobiContinuation.lean`)
  covers all ordinary regular parameters. Full principal contiguous relations are
  already proved `regularizedGaussHypergeometric_contiguous_a`, `_c`, `_shift_b`,
  `_ab`, `_a_b_pred`, `_a_c_succ`, `_a_pred_c_succ`, `_a_succ_c_pred`, `_c_three`,
  `_diagonal` in `ArgumentContinuation.lean`, with no exceptional parameter exclusions.

### AAR-2.6.1–2.6.3: dilogarithms (pp. 102–107)

- Canonical definitions are `DLMF.Zeta.polylog`; elementary identities and the
  root-of-unity multiplication formula are existing proved in `Zeta/Polylog/Properties.lean`.
  Golden-ratio values and the corrected negative-golden-ratio dilogarithm are shared
  acquisitions indexed precisely in `BookAcquisition-Duverney.md`, module
  `DLMF/Polylog/BookIdentities.lean`, namespace `DLMF.Polylog`.
- New admitted `DLMF.Zeta.polylog_natCast_eq_generalizedHypergeometric` in
  `Zeta/Polylog/HypergeometricSeries.lean` gives every nonnegative integer order on
  the full complex disk. It includes the `Li₂=z·3F2(1,1,1;2,2;z)` bridge; the
  peer real-cut bridge is not incorrectly counted as full complex-disk coverage.

### AAR-2.7–2.8.2: binomial sums and bilateral summation (pp. 107–111)

- Existing proved `DLMF.Hypergeometric.dougall_bilateral`
  (`Hypergeometric/Identities/Whipple.lean`), with summability/normalization helpers in
  `Identities/Dougall.lean`.
- Bounded Carlson uniqueness is in canonical lean-codes Carlson imports; exact adapter
  is an instance of `Complex.eqOn_zero_of_natCast_eq_zero` at exponential type zero.
  The binomial-square identity is exact proved Mathlib `Nat.sum_range_choose_sq`.
  Newly admitted generalized-binomial finite differences are
  `Ring.sum_neg_one_pow_mul_choose_mul_choose_add_natCast` in
  `DLMFMathlib/Combinatorics/BinomialDifferences.lean`, over any commutative binomial
  ring, including the zero case when the difference order exceeds the degree.

### AAR-2.9.1: fractional integration (pp. 111–114)

- Existing fractional-integral definitions:
  `DLMF.AlgebraicAnalytic.riemannLiouvilleIntegralFrom`, `riemannLiouvilleIntegralUpper`;
  proved monomial/semigroup API `fractionalIntegral_cpow`,
  `fractionalIntegral_fractionalIntegral`.
- Newly admitted Rao/AAR Erdélyi product integral:
  `DLMF.Hypergeometric.BetaTransform.erdelyi_first`
  (`GeneralizedHypergeometric/BetaTransforms.lean`),
  on its specified initial disk.
- Full L¹ almost-everywhere semigroup and the left/right dual pairing on arbitrary
  finite endpoints are newly admitted
  `ae_riemannLiouvilleIntegralFrom_riemannLiouvilleIntegralFrom` and
  `integral_riemannLiouvilleIntegralFrom_mul_eq` in `Summability/FubiniFractional.lean`.
  The dual pairing assumes the actual joint absolute triangular kernel and concludes
  integrability of both products. Fractional derivatives are the existing canonical
  integer derivatives of the complementary-order integrals.
- Full principal-cut Erdélyi is newly admitted
  `regularizedGaussHypergeometric_eq_erdelyi_product_integral` in
  `Hypergeometric/PrincipalBetaTransform.lean`; regularization cancels all beta/Gamma
  prefactors, and both transformed arguments use the coherent principal cuts.

### AAR-3.1.1–3.1.3: quadratic transformations (pp. 125–131)

- Existing branch-sensitive formulas:
  `DLMF.Hypergeometric.quadratic_connection_well_poised`,
  `quadratic_connection_half_sum` (`QuadraticConnections.lean`).
- The exact source germs (3.1.1) and (3.1.3) are newly admitted
  `eventuallyEq_quadratic_well_poised` and `eventuallyEq_quadratic_double_lower`
  in `ClassicalQuadraticGerms.lean`. Compatible continuation preserves these germ
  identities by the analytic identity principle; no disconnected principal-branch
  identity is asserted. Earlier connection formulas above are complementary.
- Shared new `regularizedGaussHypergeometric_neg_one_kummer` gives the full principal
  continuation. `tendsto_sum_gaussHypergeometricCoeff_neg_one_kummer` gives ordinary
  natural-order boundary convergence for Re(b)<1, including the conditional strip;
  both are in `KummerBoundary.lean` and admitted. Its reciprocal-Gamma form cancels
  the apparent singular Gamma quotient. The older proved `kummer_theorem` covers
  only Re(b)<1/2 and imposes another upper-parameter exclusion.
- The even polynomial consequence at every continued complex parameter is newly admitted
  `jacobiExtended_quadratic_even` in `ClassicalCoefficientIdentities.lean`; the ratio
  `(α+1)₂ₙ/(α+1)ₙ` is canceled before exceptional specialization.

### AAR-3.2.3–3.2.11: AGM and Legendre relations (pp. 132–139)

- AGM sequences and quadratic convergence: existing proved
  `DLMF.EllipticIntegrals.agmSeq_succ`, `tendsto_agmSeq`, `agmSeqC_succ`;
  Mathlib `NNReal.agm` supplies symmetry, homogeneity and step invariance.
- Theorem 3.2.3: existing proved `DLMF.EllipticIntegrals.inv_agm_eq_integral` and
  `completeEllipticK_eq_pi_div_agm`.
- Theorem 3.2.7: existing proved `legendre_relation_ofReal`; complex version
  `legendre_relation_complex` keeps the slit-plane branches.
- Theorem 3.2.8: new admitted `DLMF.Hypergeometric.elliott_relation` in `Elliott.lean`.
  The synopsis formula is mistranscribed: printed p.138/Chapter03 PDF p.15 uses
  `F(A,C−1)F(1−A,c+1/2) + F(A,C)F(−A,c+1/2) − F(A,C)F(1−A,c+1/2)`.
  At a=b=c=0 this is the Legendre relation. The synopsis instead gives
  `KK′+EE′−EK′`, which is not constant. The source-correct statement was acquired;
  the synopsis was left unchanged for review.
- Lemmas 3.2.9–10: existing `completeEllipticE_eq_agm` gives the evaluated series;
  new admitted `agm_squareRoot_integral_step`, `pi_eq_agm_correction_series`, and
  `strictMono_tendsto_agm_pi_approximants` in
  `EllipticIntegrals/ArithmeticGeometricMeanPi.lean` give the literal step, exact pi
  correction series and all finite positive-denominator monotone approximants.
- Lemma3.2.6: newly admitted `exists_solutionWronskian_eq_cpow` in
  `Hypergeometric/Solutions/AbelWronskian.lean` gives the constant-power formula for
  arbitrary Gauss solution pairs on a connected principal branch domain, without
  a nonresonance hypothesis or an independence assumption.

### AAR-3.3.3: balanced transformations (pp. 140–143)

- Existing proved `DLMF.Hypergeometric.generalizedHypergeometric_balanced_4F3_transformation`,
  `generalizedHypergeometricTruncated_sheppard`,
  `generalizedHypergeometric_3F2_unit_transformation` (`UnitArgument.lean`, `Thomae.lean`).
- Full finite-only Whipple and Sheppard forms are newly admitted
  `balanced_fourFThree_of_finite_regular` and `sheppard_of_finite_regular` in
  `FiniteBalancedTransformations.lean`. The former also covers Rao–Lakshminarayanan
  (6.76) by parameter permutation and the balancing identity. Thomae nonterminating
  forms use the existing convergent-series statements with their actual excess conditions.

### AAR-3.4.1–3.5.5: well-poised summations (pp. 143–150)

- Existing proved in `DLMF.Hypergeometric`: `dixon_sum`, `whipple_7F6`,
  `generalizedHypergeometric_watson_sum`, `generalizedHypergeometric_whipple_3F2_sum`,
  `gauss_second_summation`, `bailey_summation`.
- Existing admitted: `generalizedHypergeometric_dougall_5F4_sum`,
  `generalizedHypergeometric_whipple_nonterminating_left`,
  `generalizedHypergeometric_whipple_general`.
- New admitted targets in `Hypergeometric/WellPoisedSummations.lean`:
  `bailey_terminating_fiveFFour` (3.4.2), `sum_veryWellPoised_fiveFFour` (3.4.3),
  `sum_veryWellPoised_dougall` (3.5.1), `hasSum_veryWellPoised_dougall` (3.5.2),
  `tendsto_sum_veryWellPoised_minus_one` (3.5.3),
  `tendsto_sum_veryWellPoised_minus_one_threeFTwo` (3.4.6).
  The actual `VeryWellPoised.coefficient` cancels the artificial a/2 singularity first;
  it has proved defining/zero API. Conditional minus-one sums are ordered limits.
  Finite denominator exclusions stop at the terminating degree.
- The canceled central-parameter Whipple3.4.4 form is newly admitted
  `sum_veryWellPoised_whipple` in the same module, retaining `a=0` and denominator
  poles strictly after termination. Resonant final quotient parameters have the
  source's meromorphic-limit interpretation, not a falsely totalized divergent quotient.

### AAR-3.6.1–3.8.2: Barnes integrals and Wilson polynomials (pp. 150–160)

- Theorems 3.6.1 and 3.6.3: new admitted `DLMF.Gamma.barnes_very_well_poised_seven`,
  `barnes_balanced_nine`, with actual Gamma-block kernels and separating vertical lines.
- Theorems 3.6.2 and 3.8.2: new admitted `DLMF.OrthogonalPolynomials.wilson_integral_mul`
  gives the full positive-real-axis norm. Degree zero is Wilson's beta integral.
- Definition 3.8.1: existing canonical `wilson`; new admitted `wilson_parameter_permutation`
  gives every parameter permutation on the finite regular domain.
- New admitted `wilson_normalized_recurrence` in `WilsonRecurrences.lean` gives
  the literal A_n,C_n coefficients, cleared so no artificial sum-parameter exclusion
  is imposed. New admitted `barnes_very_well_poised_seven_contour` and
  `barnes_balanced_nine_contour` in `Gamma/Integrals/BarnesDeformations.lean` extend
  the corresponding Gamma evaluations to every actual separating contour, canceling
  the ratio Γ(1+a/2+s)/Γ(a/2+s) before evaluating its removable points.
  The full complex norm is newly admitted `wilson_integral_mul_contour` in
  `OrthogonalPolynomials/WilsonContourNorms.lean`, with explicit
  `wilsonBarnesIntegrand` and proved defining API. Degree zero gives exactly the
  deformed-contour Wilson integral, including its factor two normalization.

### AAR-3.9.1: quadratic pullback of Riemann equations (pp. 160–163)

- New admitted `DLMF.Hypergeometric.riemannNormalOperator_quadratic_iff`
  in `RiemannQuadratic.lean` gives the exact pointwise equivalence of local solution
  equations under x=(2u−1)^2, with doubled infinity exponents and repeated finite pairs.
- New proved `analyticAt_riemannQuadratic_coefficients` establishes that u=1/2 is ordinary.
- An explicit equivalence of function spaces using arbitrary chosen inverse branches
  is now explicit in newly admitted
  `exists_linearMap_bijOn_riemannNormalSolutions_quadratic` with a chosen analytic
  square-root branch. `exists_analytic_quadratic_pullback` gives the analytic solution
  extension through `u=1/2`, rather than merely coefficient analyticity there.

### AAR-3.10–3.12: Gosper, WZ and Pfaff methods (pp. 163–176)

- Bailey (3.11.7): new admitted `DLMF.Hypergeometric.bailey_terminating_fourFThree`;
  its displayed second-order recurrence is `bailey_pochhammer_ratio_recurrence`
  in `FiniteReciprocity.lean`.
- Finite WZ telescoping is elementary finite summation (`Finset.sum_range_sub`);
  the generic multi-shift versions are now newly admitted
  `Finset.sum_finsum_eq_zero_of_telescoping_certificate` and
  `sum_eq_zero_of_tendsto_telescoping_certificate` in
  `DLMFMathlib/Algebra/BigOperators/CreativeTelescoping.lean`. Finite support and ordered
  convergence with boundary limits are stated separately. Gosper equivalence is newly
  admitted `Polynomial.exists_gosper_rational_iff_polynomial` in
  `DLMFMathlib/RingTheory/Polynomial/Gosper.lean`.
- Pfaff's Vandermonde recurrence is the proved
  `vandermonde_pochhammer_ratio_recurrence` in `FiniteReciprocity.lean`, combined with
  `sum_pochhammer_mul_neg_nat_div` (existing admitted finite evaluation). Its hypotheses
  concern the retained denominator and the displayed `a/b`, not later denominator poles.

### AAR-4.1–4.4: Kummer, Tricomi and Whittaker functions (pp. 188–199)

- Existing canonical definitions: `DLMF.Confluent.kummerM`, `kummerU`,
  `whittakerM`, `whittakerW`, with logarithmic-surface variants in the foundational API.
- Integral formula: existing proved `kummerM_eq_euler_integral`; U's half-line integral
  is `kummerU_laplace`. Whittaker bridges `kummerM_eq_whittakerM`,
  `kummerU_eq_whittakerW`; symmetry `whittakerW_even_mu` (proved).
- Asymptotic targets: existing proved `hasAsymptoticExpansion_kummerU`,
  `hasAsymptoticExpansion_kummerU_sector`,
  `hasAsymptoticExpansion_regularizedConfluent`,
  `hasAsymptoticExpansion_regularizedConfluent_sector_of_re_pos`.
- Shared new `hasAsymptoticExpansion_regularizedConfluent_sector` in
  `Confluent/Asymptotics/LogarithmicSector.lean` removes extraneous fixed-parameter
  restrictions; Kummer transformation gives the left-half-plane algebraic expansion.
  `hasAsymptoticExpansion_kummerUContinuedOnLog` retains the full
  `|Im w|≤3π/2−δ` logarithmic surface, with `kummerUContinuedOnLog_eq_principal`
  and `tendsto_kummerUContinuedOnLog` giving principal agreement and integer-c limits.
- Theorem4.2.1 is shared new `regularizedHGFun_eq_kummerBarnesContour` in
  `Confluent/BarnesContours.lean`, with actual separating contour and integrability.
- Gaussian/error normalizations: existing proved `kummerM_erf`, `kummerU_erfc`,
  `kummerM_hermite_even`, `kummerM_hermite_odd`, `kummerU_hermite`,
  `kummerU_laguerrePolynomialL` in `Confluent/Relations.lean`. Kummer second
  Frobenius expression follows from the existing principal transformation/ODE API.

### AAR-4.5–4.10: Bessel definitions and core API (pp. 199–216)

- Mathlib `Complex.besselJ` is canonical. Local J/I/Y/K definitions, differential
  equations, recurrences and Wronskians are in `Bessel/Basic/`.
- Existing proved `DLMF.Bessel.besselJ_generating_function`,
  `hasSum_besselJ_jacobiAnger`, `besselJ_int_eq_integral_exp`,
  `besselJ_int_eq_integral_cos`, `besselJ_eq_poisson_integral`,
  `besselY_eq_schlafli`; the generating and integral conventions agree.
- Large-order normalization: existing proved `besselJ_isEquivalent_large_order`;
  large-argument statements are collected in `Bessel/Asymptotics`.
- Exact differential and order-recurrence pointers: proved `besselJ_ode`,
  `besselY_ode_all`, `besselJ_add_sub`, `besselY_add_sub`, `two_deriv_besselJ`,
  `hasDerivAt_besselY`, `hankelH1_add_sub`, `hankelH2_add_sub`,
  `hasDerivAt_hankelH1`, `hasDerivAt_hankelH2`. Weighted derivatives follow from
  the product rule and these exact recurrences; J interfaces are proved
  `hasDerivAt_cpow_mul_besselJ'`, `hasDerivAt_cpow_neg_mul_besselJ'`.
  `continuousAt_besselY` and `besselY_eq_dslope` encode all integer-order limits.
- Half-integer J values: proved `besselJ_half`, `besselJ_neg_half`.
  Neumann/Graf/Gegenbauer additions: proved `hasSum_besselJ_add`,
  `hasSum_besselJ_graf`, `besselJ_addition` (the latter in
  `SphericalHarmonics/BesselAddition.lean`). The generating/Poisson complex domains
  are shared new `tendstoLocallyUniformlyOn_sum_besselJ_generating` and
  `besselJ_eq_poisson_exponential`, indexed by the Temme9 acquisition.
- Shared new `isBigO_besselJOnLog_remainder`, `isBigO_besselYOnLog_remainder`,
  and `hasAsymptoticExpansion_hankelH1OnLog` / `hankelH2OnLog` in
  `Bessel/LogarithmicAsymptotics.lean` give the exact full complex-sector
  remainder scale and lifted Hankel branches. `largeArgumentCoefficient_succ`
  and its zero value identify the displayed finite-product coefficients.

### AAR-4.11.1–4.11.8: Bessel integrals and Jacobi limit (pp. 216–222)

- Theorem 4.11.3: existing proved `DLMF.Bessel.besselJ_laplace_integrable`,
  `besselJ_laplace_integral` give the regularized Gauss form without artificial
  exclusion of a negative-integer Bessel order.
- Theorem 4.11.7: existing proved `besselJ_gaussian_integral_complex`,
  `besselJ_gaussian_integral` and Kummer-M variants. Corollary 4.11.8:
  existing proved `sonine_integral`.
- Theorem 4.11.6: new admissions
  `DLMF.OrthogonalPolynomials.jacobiExtended_mehler_heine_uniform_cos`,
  `jacobiExtended_mehler_heine_uniform_quadratic` cover every real α,β, locally
  uniformly on the complex plane. The limit is Mathlib's entire regularized ₀F₁.
- Two angular Sonine integrals, the two elementary Laplace corollaries and the
  Mellin-product integral are now acquired by newly admitted
  `besselJ_sonine_angular`, `besselJ_mul_besselJ_sonine_angular`,
  `besselJ_complex_laplace_integral`, `integral_exp_mul_besselJ_div`, and
  `integral_besselJ_mul_besselJ_cpow` in `Bessel/BookIntegralTransforms.lean`.
  Complex-frequency Laplace convergence and principal branches are explicit; each
  transform includes absolute integrability. The elementary positive real-frequency
  Laplace corollary follows by scaling the shared root
  `integral_exp_mul_besselJ_eq_cpow` rather than adding a duplicate admission.

### AAR-4.12–4.13: modified functions and Nicholson integral (pp. 222–225)

- Modified I/K definitions and branch identities are canonical in `Bessel/Basic/`;
  half-line K representations are proved in `KIntegralRep.lean`, `KIntegrals.lean`.
- Nicholson: existing admitted `DLMF.Bessel.nicholson_integral` in `Modified.lean`.
- Basic exact pointers: proved `besselI_ode`, `besselK_ode_all`,
  `besselK_neg`, `wronskian_besselK_besselI` (reverse Wronskian gives the book sign).
  Shared new `hasAsymptoticExpansion_besselIOnLog` and
  `hasAsymptoticExpansion_besselKOnLog` give every displayed coefficient and include
  the positive real axis; only I coefficients alternate. The K cosh integral is
  proved `besselK_eq_integral_cosh` in `KIntegralRep.lean`.

### AAR-4.14.1–4.16.4: zeros, comparison and zero-free regions (pp. 225–234)

- Existing proved zero results include `DLMF.Bessel.besselJ_zeros_simple`,
  `besselJ_first_positive_zero_strictMono`, `exists_strictMono_besselJ_positive_zeros`,
  `besselJ_exists_zero_Ioo`, `besselJ_pi_lt_sub`,
  `existsUnique_besselJ_succ_zero_between`, `existsUnique_besselJ_zero_between`.
- Dini API: existing targets `im_eq_zero_of_diniNormalized_eq_zero`,
  `deriv_diniNormalized_ne_zero`, `existsUnique_diniZero_between_besselJ_zeros`,
  `integral_besselJ_mul_eq_zero_of_diniZeros`,
  `integral_norm_besselJ_sq_of_diniZero` in `DiniZeros.lean`.
- Saff–Varga parabola: existing proved `DLMF.Confluent.kummerM_ne_zero_of_mem_parabolicRegion`.
- Theorem4.14.1: newly admitted `tendsto_degree_mul_jacobi_zero_angle` in
  `OrthogonalPolynomials/JacobiBesselZeroLimit.lean` gives every fixed zero index for
  α,β>-1. `Bessel/CanonicalProduct.lean` adds admitted `hasProd_normalized_besselJ`
  with a complete strictly increasing positive-zero sequence; normalization makes
  the product an entire identity at every complex argument. Reality for ν>-1 is
  existing admitted `im_eq_zero_of_normalized_besselJ_eq_zero` in `DiniZeros.lean`;
  the complete unbounded sequence is shared admitted `exists_strictMono_besselJ_positive_zeros`.
- Theorem4.14.2 and Theorem4.15.1: new admitted
  `ODE.abs_solution_lt_of_potential_lt`, `arch_and_zero_forwardDifferences_pos`,
  `zero_offset_forwardDifferences_pos` in `DLMFMathlib/Analysis/ODE/ArchDifferences.lean`.
  Its exact finite-interval forms `finite_arch_and_zero_forwardDifferences_pos` and
  `finite_zero_offset_forwardDifferences_pos` require only n+2 / n+1 retained zeros
  and allow a closed interval, rather than assuming an infinite sequence inside it.
  They retain matching nonzero initial data, consecutive-zero indexing and existence
  of the highest amplitude derivative only in the interior, without extra continuity.
- Corollary4.15.2: newly admitted `cylinder_arch_and_zero_forwardDifferences_pos`,
  `cylinder_zero_offset_forwardDifferences_pos` and
  `cylinder_consecutive_zero_gaps_strictMono_or_strictAnti` in
  `Bessel/CylinderZeroDifferences.lean`, for arbitrary nontrivial real cylinder solutions.
- Theorem4.16.1: newly admitted `Complex.recurrence_ne_zero_of_mem_parabolicRegion`
  in `DLMFMathlib/Analysis/Complex/ParabolicRecurrence.lean` is the full general
  three-term recurrence. Corollaries4.16.2–4 use existing proved
  `DLMF.Confluent.SaffVarga.hurwitz`, `partialSums`, `params` and
  `kummerM_ne_zero_of_mem_parabolicRegion`. The Dini targets above are related
  Temme coverage, rather than substitutes for the AAR zero-difference theorems.

### AAR-5.1: Chebyshev prototypes (pp. 240–244)

- Definitions, values, recurrence, cosine/sine realization, zeros and extrema: Mathlib
  `Polynomial.Chebyshev.T`, `U`, `T_add_two`, `U_add_two`, `T_real_cos`,
  `U_real_cos`, `roots_T_real`, `roots_U_real` and `abs_eval_T_real_eq_one_iff`.
  The exact generating functions are proved DLMF `chebyshevT_generating_function`
  and `chebyshevU_generating_function` in `Series/ClassicalGenerating.lean`.
- Orthogonality of `T`: Mathlib `Polynomial.Chebyshev.measureT`; that of `U`:
  DLMF `DLMF.OrthogonalPolynomials.integral_eval_U_mul_of_ne` and
  `integral_eval_U_mul_self` (existing proved, `General.lean`).
- Minimax and its unique equality case are Mathlib
  `Polynomial.Chebyshev.leadingCoeff_le_of_forall_abs_le_one` and
  `coeff_eq_iff_of_forall_abs_le_one` in `Trigonometric/Chebyshev/Extremal.lean`.
  Normalize the monic polynomial by its uniform bound; these state precisely the
  sharp leading-coefficient inequality and equality polynomial `T_n`.
  The T norms are `integral_eval_T_real_mul_eval_T_real_measureT_of_ne`,
  `integral_eval_T_real_mul_self_measureT_zero`, `integral_T_real_mul_self_measureT_of_ne_zero`.

### AAR-5.2.2–5.2.6: recurrence and Christoffel–Darboux (pp. 244–248)

- Orthogonal sequence, degrees, positive norms: existing proved definition
  `DLMF.OrthogonalPolynomials.IsOrthogonalPolynomials` (`Basic/General.lean`).
- Three-term recurrence and coefficients: existing proved
  `DLMF.OrthogonalPolynomials.three_term_recurrence`,
  `recurrenceDiagonal_eq_integral`, `monic_squaredNorm_ratio`.
- Christoffel–Darboux and diagonal identity: existing proved
  `DLMF.OrthogonalPolynomials.christoffel_darboux` and `christoffel_darboux_diagonal`.
- Favard converse: existing admitted `DLMF.OrthogonalPolynomials.favard`.
- The exact nonmonic recurrence coefficients are shared newly admitted
  `three_term_recurrence_explicit` in `GeneralRecurrenceCoefficients.lean`.
  Strict diagonal positivity and the telescoping norm product are newly proved
  `christoffelDarbouxKernel_diag_pos`, `squaredNorm_eq_mul_prod_ratio` in
  `NormProducts.lean`; the existing `monic_squaredNorm_ratio` identifies each ratio
  with the source monic recurrence coefficient.

### AAR-5.3.2–5.4.4: quadrature and zeros (pp. 248–256)

- Exactness and existence of positive weights: existing proved
  `DLMF.OrthogonalPolynomials.gauss_quadrature` (`General.lean`).
- Distinct zeros and strict interlacing: existing proved `orthogonal_polynomials_roots`
  and `zeros_interlace` in namespace `DLMF.OrthogonalPolynomials`.
- Canonical cardinal-polynomial weights: new definition `gaussWeight`, with proved
  `gaussWeight_def`, in `QuadratureAndKernels.lean`.
- Squared-cardinal-norm identity and positivity: newly admitted
  `gaussWeight_eq_integral_sq`; continuous quadrature convergence: newly admitted
  `tendsto_gauss_quadrature`; half-open Markov–Stieltjes bounds: newly admitted
  `markov_stieltjes_inequalities` (same namespace and module).
- New admitted `exists_zero_between_consecutive_orthogonal_polynomial_zeros` in
  `MeasureConstruction.lean` gives nonadjacent-degree separation (5.4.3). New admitted
  `strict_markov_stieltjes_inequalities` in `QuadratureError.lean` gives the strict
  atom-free, positive-on-every-subinterval refinement. The support-interior theorem
  `eval_eq_zero_mem_interior_convexHull_support` also covers the exact root location.

### AAR-5.5.2–5.5.6: continued fractions and Cauchy transforms (pp. 256–259)

- Continued-fraction convergent recurrence and determinant: Mathlib `GenContFract`
  continuants API, with its precise first/second-kind normalization identified by
  the newly admitted `polynomialFraction_jacobi_continuants` below.
- Second-kind polynomial: new `DLMF.OrthogonalPolynomials.secondKindPolynomial`
  integrates coefficients of `P /ₘ (X - C t)`. Proved unfolding:
  `secondKindPolynomial_def`. This preserves the polynomial diagonal value at atoms.
- Newly admitted in `QuadratureAndKernels.lean`: `eval_secondKindPolynomial`,
  `secondKindPolynomial_recurrence`, `secondKindPolynomial_div_eq_sum`, and
  `tendstoLocallyUniformlyOn_secondKindPolynomial_div` (Markov's theorem off `[a,b]`).
- Proved elementary API `secondKindPolynomial_C` and `secondKindPolynomial_X_sub_C`
  gives the exact initial values. Newly admitted `polynomialFraction_jacobi_continuants`
  in `SecondKindContinuedFraction.lean` identifies both actual Mathlib numerator and
  denominator continuants with the second/first-kind polynomials, including index zero.
  Convergents are therefore the quotient by Mathlib's continuant definition.
  Convergence above is explicitly locally uniform, not merely pointwise.

### AAR-5.6.2–5.6.5: reproducing kernels (pp. 259–263)

- Reproducing kernel: existing proved `DLMF.OrthogonalPolynomials.kernel_reproduces`.
- Christoffel modification: existing proved `kernel_polynomials_orthogonal`, with
  absolute weight `|y-x|`, equivalent on a one-sided support to the positive book weight.
- Christoffel weights: newly admitted `gaussWeight_inv_eq_kernel`.
- Sharp evaluation inequality, attainment and the two real equality cases: newly
  admitted `kernel_evaluation_extremum`. New declarations are in
  `DLMF.OrthogonalPolynomials.QuadratureAndKernels`.

### AAR-5.7.1–5.7.6: least squares and completeness (pp. 263–266)

- Compact-support Parseval and L² convergence: existing proved
  `DLMF.OrthogonalPolynomials.orthogonal_polynomials_parseval` (`General.lean`) and
  `compact_support_L2_expansion` (`GeneralIdentities.lean`).
- Full weighted-polynomial least squares, the Pythagorean error identity and equality
  precisely at the projection polynomial are shared newly admitted
  `polynomial_projection_leastSquares` in `LeastSquaresProjection.lean`.
  The zero-coefficient almost-everywhere consequence is the zero limit in proved
  `compact_support_L2_expansion`; full exponential-decay completeness is the exact
  `MeasureTheory.MemLp.ae_eq_zero_of_moments_mul_eq_zero_of_exponential_decay` below.
- Density/completeness input is pinned TauCeti
  `TauCeti.orthogonal_span_range_bareNormalizedLp_eq_bot`
  (`Analysis/InnerProductSpace/PolynomialCompleteness.lean`).

### AAR-5.8.1–5.8.2: moments, walks and Jacobi fractions (pp. 266–269)

- New finite Jacobi matrix `DLMF.OrthogonalPolynomials.jacobiTruncation`, with proved
  `jacobiTruncation_apply`; newly admitted `moment_eq_jacobiTruncation_pow`.
- New formal continued fraction `jacobiMomentFraction`, with proved zero and successor
  equations; newly admitted `coeff_jacobiMomentFraction_eq_moment` gives coefficient
  stabilization, so no analytic convergence assumption is introduced.
- These declarations are in `SpectralMoments.lean`. The general finite-graph resolvent
  and vertex-deletion determinant are newly admitted
  `Matrix.mul_powerSeriesResolvent` and `powerSeriesResolvent_diagonal_mul_det` in
  `DLMFMathlib/LinearAlgebra/Matrix/PowerSeriesResolvent.lean`. The actual power series
  has proved coefficient API `Matrix.coeff_powerSeriesResolvent`; the determinant
  quotient is cleared, so it holds over every commutative coefficient ring.

### AAR-6.1–6.2: Hermite and Laguerre definitions and API (pp. 278–293)

- Canonical `hermitePolynomialH`, `laguerrePolynomialL`, `laguerreExtended`,
  `jacobiPolynomialP`, `ultrasphericalPolynomial`, Chebyshev families are in
  `OrthogonalPolynomials/Basic/` (proved unfolding and elementary API).
- Existing proved `deriv_gaussian_eq_hermitePolynomialH`,
  `hasSum_hermitePolynomialH_generating_function`,
  `hasSum_laguerreExtended_generating_function`, `laguerrePolynomialL_orthogonal`,
  `jacobiPolynomialP_orthogonal`; classical differential equations and recurrence
  statements are in `Basic/Classical.lean` and `Recurrences/`.
- The all-parameter Jacobi polynomial is newly defined `jacobiExtended`, with proved
  regular-domain bridge and new admitted endpoints/reflection/cleared recurrence.
- Exact source norms: existing proved `hermitePolynomialH_orthogonality` and
  `laguerrePolynomialL_norm` in `Integrals/AngularRepresentations.lean`; off-diagonal
  Laguerre orthogonality is `laguerrePolynomialL_orthogonal`. The connection identity
  at all complex parameters is proved `laguerrePolynomialL_connection` in
  `Series/JacobiParameterSeries.lean` and uses `laguerreExtended` on both sides.
  `laguerrePolynomialL_fractional_integral` is the displayed β-kernel convolution.
- Theorem6.2.1: new admitted `tendsto_mixed_laguerre_expansion` in
  `LaguerreDualSeries.lean` gives the corrected low/high mixed coefficients and actual
  weighted-L² seminorm convergence, retaining both source Hilbert-space assumptions.
- Theorem6.2.2: new explicit `laguerreFractionalLeftPartial` and
  `laguerreFractionalRightPartial`, with proved defining equations, apply the printed
  fractional operations to actual finite partial sums. New admitted
  `laguerre_dual_series_coefficients` concludes the exact dual coefficient formula
  from pointwise convergence of those operations and the source's explicit integrable
  majorants on each side of the splitting point.

### AAR-6.3.1–6.4.3: determinants, Rodrigues and generating functions (pp. 293–306)

- Existing proved moment/Hankel tools:
  `DLMF.OrthogonalPolynomials.monic_moment_determinant`, `hankelDeterminant_pos`.
- Classical Jacobi Rodrigues/norm/ODE/generating APIs already exist in `Classical`,
  `Differential`, `Series/ClassicalGenerating`; general two-family Gram determinant
  construction is newly defined `MeasureTheory.biorthogonalDeterminant`, with proved
  unfolding and newly admitted `integral_mul_biorthogonalDeterminant_eq_zero` in
  `DLMFMathlib/LinearAlgebra/BiorthogonalDeterminant.lean`. This includes distinct
  row/column families and arbitrary measures, requiring exactly product integrability.
- Existing proved `DLMF.AlgebraicAnalytic.lagrange_burmann`; classical limits
  `DLMF.OrthogonalPolynomials.jacobi_limit_laguerrePolynomialL`,
  `ultrasphericalPolynomial_limit_hermite` (restricted parameters retained).
- New all-parameter Jacobi admissions in `PolynomialContinuation.lean`:
  `jacobiExtended_one`, `jacobiExtended_neg_one`, `jacobiExtended_neg`,
  `iteratedDeriv_jacobiExtended_self`, `jacobiExtended_recurrence`.
  Shared `JacobiContinuation.lean` additionally has the full complex-parameter ODE,
  Rodrigues formula, entire-local and real-interval full-disk generating functions.
  Newly admitted `eq_jacobiExtended_of_orthogonal_and_endpoint` in
  `ClassicalCoefficientIdentities.lean` gives exactly the converse uniqueness in
  Theorem6.4.3. The moment determinant and positive Hankel determinant above identify
  the construction's leading coefficient; no new special-function determinant is required.

### AAR-6.5.1–6.6.2: completeness and asymptotics (pp. 306–313)

- Theorem6.5.1: new admitted `MeasureTheory.Integrable.ae_eq_of_fourier_eq` and its
  zero corollary in `DLMFMathlib/Analysis/Fourier/L1Uniqueness.lean`. Continuity-only
  inversion is not incorrectly counted as an a.e. theorem for arbitrary L¹ functions.
- Theorem6.5.2: new admitted
  `MeasureTheory.MemLp.ae_eq_zero_of_moments_mul_eq_zero_of_exponential_decay`
  in `DLMFMathlib/Analysis/InnerProductSpace/MomentCompleteness.lean` retains a signed
  or complex nonzero-a.e. L² multiplier and the unweighted L² domain of `f`. Positive
  `withDensity` completeness alone would not cover that multiplier scope.
- Theorem 6.5.3: existing proved `DLMF.OrthogonalPolynomials.laguerrePolynomialL_complete`,
  `hermitePolynomialH_complete`; general Parseval/partial-sum convergence is supplied
  by pinned `TauCeti.hilbertBasisOfWeightedMeasure` with
  `TauCeti.orthogonal_span_range_bareNormalizedLp_eq_bot` and Mathlib
  `HilbertBasis.hasSum_repr`, `HilbertBasis.hasSum_inner_mul_inner`. The normalization
  is explicitly the polynomial divided by the square root of its squared norm.
- Theorem 6.6.1: new admitted `Complex.isLittleO_coeff_sub_of_continuousOn_closedBall`
  in `DLMFMathlib/Analysis/Complex/CoefficientAsymptotics.lean`.
- Uniform Jacobi refinement: new admitted `jacobiExtended_darboux_uniform` in `Darboux.lean`
  gives the full O(n^(-3/2)) error for every real α,β and compact interior angle interval.
  Existing admitted `jacobi_darboux_asymptotic` only gives a pointwise little-o equivalent.
- Theorem6.6.2: new admitted `exists_density_of_summable_recurrence_perturbation`
  in `SummableRecurrencePerturbation.lean` gives the continuous positive interior density,
  countable pure point exterior measure, endpoint masses and almost-everywhere limsup.

### AAR-6.7.1–6.7.4: fractional and Laplace polynomial integrals (pp. 313–316)

- Theorem 6.7.1: existing proved `DLMF.OrthogonalPolynomials.legendre_dirichlet_mehler`
  (`Integrals/AngularRepresentations.lean`); the second integral is newly admitted
  `legendrePolynomialP_eq_complementary_mehler` in `LegendreIntegralRepresentations.lean`.
- Theorem 6.7.2: existing `jacobi_fractional_integral` and `jacobi_weighted_integral`
  (`Integrals/ConvolutionsAndFourier.lean`), with the source normalization converted by P_n(1).
  Newly admitted `jacobiExtended_fractional_integral_weighted` and
  `jacobiExtended_fractional_integral_weighted_left` in `JacobiFractionalTransforms.lean`
  give the second right/left formulas, including complex-parameter endpoint regularity
  and weighted integrability. Reflection gives the first left formula from the proved
  first right formula and `jacobiExtended_neg`.
- Corollary 6.7.3: existing proved `jacobi_double_laplace_integral` gives the general
  double Laplace representation. The exact single angular transform with the whole
  `ν>λ>-1/2` range, including either zero-parameter normalized Chebyshev case, is
  newly admitted `ultrasphericalPolynomial_normalized_fractional_angular` in
  `JacobiFractionalTransforms.lean`.
- Theorem 6.7.4: existing proved `ultrasphericalPolynomial_laplace_integral`
  (`Integrals/GegenbauerAndLegendre.lean`).

### AAR-6.8.1–6.9.9: linearization and matchings (pp. 316–330)

- Hermite linearization: existing proved `hermitePolynomialH_linearization` in
  `Series/JacobiParameterSeries.lean` is exactly 6.8.1 with coefficients
  2^k k! choose(m,k)choose(n,k). Gegenbauer linearization:
  `ultrasphericalPolynomial_linearization` in the same file is the displayed coefficient
  factorization term for term for λ>0. Hermite triple integral is existing proved
  `hermitePolynomialH_triple_integral` in `Integrals/LaguerreAndHermite.lean`.
- Legendre triple integral: existing proved
  `DLMF.WignerSymbols.LegendreProducts.triple_integral`, together with the explicit
  zero-projection `wigner3j` formula, gives the factorial/triangle expression.
  `LegendreProducts.zero_projection_square` is the proved exact factorial expression
  in triangle-gap indices, while `wigner3j_zero_zero_zero_of_odd` and the triad-zero
  rule give the other cases. Chebyshev removable limits are proved
  `ultrasphericalPolynomial_limit_chebyshev` (`Limits.lean`), with its scaled
  `(n+λ)/λ` normalization explicit.
- Canonical new `SimpleGraph.matchingEdgeFinsets`, `matchingPolynomial`,
  `perfectMatchingCount`, `completeMultipartitePerfectMatchingCount` with proved
  membership/unfolding APIs in `DLMFMathlib/Combinatorics/SimpleGraph/MatchingPolynomial.lean`.
- Theorem 6.9.1 / Lemma 6.9.7: new admissions `matchingPolynomial_top`, `matchingPolynomial_sum`.
- Lemma 6.9.2 / Theorems 6.9.5–6: new admissions
  `completeMultipartitePerfectMatchingCount_recurrence`,
  `completeMultipartitePerfectMatchingCount_two`, `completeMultipartitePerfectMatchingCount_three`.
- Theorem 6.9.4: new admissions `DLMF.OrthogonalPolynomials.integral_prod_hermite_eq_matchingCount`,
  `integral_prod_hermitePolynomialH_eq_matchingCount` in `MatchingIntegrals.lean`.
- Lemmas 6.9.8–9: new admitted `SimpleGraph.perfectMatchingCount_compl_eq_sum`
  gives the complete sign-cancellation identity, including odd and empty Gaussian moments.
  The explicit involution and Gaussian recurrence proof are not separately acquired yet.

- The actual first-internal-edge involution is now defined in
  `DLMFMathlib/Combinatorics/SimpleGraph/MatchingInvolution.lean` as
  `SimpleGraph.toggleFirstInternalEdge`, with proved unfolding and involutivity.
  `toggleFirstInternalEdge_preserves_matching_and_negates_sign` is the admitted
  no-fixed-point matching-preservation/sign-reversal target.

### AAR-6.10–6.11: continuous Hahn families and q-ultraspherical extension (pp. 330–339)

- Existing canonical `continuousDualHahn`, `continuousHahn`, `wilson`.
- Existing admitted `continuousDualHahn_orthogonality` gives the full dual-Hahn norm;
  existing proved `wilson_limit_continuousDualHahn` gives the Wilson limit.
- New admitted `continuousHahn_integral_mul` (`WilsonHahnNorms.lean`) gives the full Hahn
  norm, canceling its exceptional n=0,A=1 denominator before specialization.
- Existing `continuousHahn_difference_equation` is the full imaginary-step equation.
  New admitted `wilson_imaginary_step_equation`, `continuousDualHahn_imaginary_step_equation`,
  `wilson_normalized_recurrence`, `continuousDualHahn_normalized_recurrence`,
  `continuousHahn_normalized_recurrence` in `WilsonRecurrences.lean` give all remaining
  equations, with rational coefficient poles cleared before specialization.
- Rogers families: new `qGegenbauer_recurrence`, `hasSum_qGegenbauer_generating`;
  existing proved `qGegenbauer_limit_ultrasphericalPolynomial` retains the classical limit.
  Full q-Rogers norm is recorded under AAR10.11.

### AAR-6-exercises-51–52: Hardy and Roosenraad theorems (pp. 352–354)

- New `OrthogonalPolynomials/HermiteUncertainty.lean` defines
  `generalizedHermiteFunction`, `generalizedHermiteLp`, `roosenraadTransform`
  by explicit Laguerre formulas, a canonical L² lift, and the actual L² spectral sum.
- New admissions `memLp_generalizedHermiteFunction`, `orthonormal_generalizedHermiteLp`,
  `exists_unitary_roosenraadTransform`, `roosenraadTransform_eq_integral` acquire
  the basis, its unitary extension and Bessel integral kernel.
- The two named uncertainty theorems are new admissions
  `exists_finite_hermite_expansion_of_gaussian_bounds`,
  `exists_finite_generalizedHermite_expansion_of_gaussian_bounds`.
- The transform convention is `exp(ixt)/sqrt(2π)` and the spectral phase is i^j;
  function-representative equalities are almost everywhere.

### AAR-7.1.1–7.1.4': Jacobi connection coefficients (pp. 356–363)

- Lemma 7.1.1: new `DLMF.OrthogonalPolynomials.jacobiConnectionCoefficient` with proved
  integral unfolding and admitted `jacobiExtended_connection` covers all continued numerator
  parameters and positive real Jacobi-weight basis parameters.
- Theorems 7.1.2–3: new admissions `jacobiExtended_equal_first_connection`,
  `jacobiExtended_equal_second_connection` in `ConnectionCoefficients.lean`.
  The removable α+β+1 factor is canceled, including α+β+1=0.
- Theorems 7.1.4/4′: existing proved `ultrasphericalPolynomial_connection`
  (`Series/JacobiParameterSeries.lean`) gives the exact finite Gegenbauer formula,
  swapping its parameter names to match the book. Jacobi conversion uses the canonical bridge.
  Their nonnegativity for λ≥μ>0 is now the proved explicit scalar inequality
  `gegenbauer_connectionCoefficient_nonneg` in `ClassicalCoefficientIdentities.lean`;
  its real Pochhammer polynomials coerce to the complex factors in that connection formula.

### AAR-7.2.1–7.2.7: coefficient and Laguerre positivity (pp. 363–371)

- Newly admitted in `DLMF.OrthogonalPolynomials.Real` (`PositivityCriteria.lean`):
  `sum_binomial_triple_nonneg`, `laguerreTripleIntegral_three_nonneg`,
  `laguerreTripleIntegral_three_pos`, `integral_damped_laguerre_mul_pos`,
  `exists_measure_moments_of_laguerre_kernel_nonneg`,
  `laguerreTripleIntegral_two_nonneg` (sharp threshold/equality included),
  `integral_laguerre_scaled_triple_nonneg`. Auxiliary `laguerreTripleIntegral` has
  a proved defining equation. Sarmanov retains absolute local uniform convergence.
- Newly admitted MacMahon master theorem:
  `MvPowerSeries.coeff_det_inv_eq_coeff_prod_linear_forms`
  (`DLMFMathlib/Combinatorics/MacMahon.lean`).
- Corollary7.2.4: newly admitted `integral_damped_laguerre_mul_function_pos` in the
  same namespace/file gives every strict coefficient for a nonzero weighted-L² function
  with nonnegative original coefficients, using the gamma-weight measure.

### AAR-7.3.1–7.3.6: Vietoris inequalities and trigonometric zeros (pp. 371–381)

- New Mathlib-style `Real.vietorisCoefficient` with proved defining formula.
- Propositions 7.3.1–3: new admissions `Real.tendsto_sum_vietoris`,
  `centralBinom_lt_four_pow_div_sqrt_pi_mul`, `sqrt_sin_sub_le_vietoris_sums`.
- Theorems 7.3.4–5: new admissions `vietoris_sums_pos`,
  `trig_sums_pos_of_vietoris_coefficients` (both sine and cosine).
- Theorem 7.3.6 baseline: new admission `exists_trig_zeros_of_antitone_coefficients`
  gives every simple zero and the Szegő intervals, with the corrected sine index.
- Convexity-refined zero intervals: new admitted
  `Real.exists_trig_zeros_of_convex_coefficients` (degree at least two).
- Blocked mathematical review: the strict upper bound in the Vietoris-refined
  (7.3.29) fails at n=1, λ₀=2, λ₁=1. The polynomial 2cos θ+1 has root
  θ=2π/3, equal to kπ/(n+1/2), while (2k−1)λ_{k−1}≥2kλ_k>0 holds.
  Printed p.381/Chapter07 PDF p.27 confirms both the weak coefficient inequality
  and strict zero inequality. The unverified refinement target was removed;
  neither the synopsis nor the book errata file was changed.
  Degree n=2 also has equality: λ=(1,1/2,(3−√5)/8) gives a zero at 4π/5,
  equal to kπ/(n+1/2) for k=2; both required coefficient inequalities hold.
- All are in `DLMFMathlib/Analysis/SpecialFunctions/Trigonometric/Vietoris.lean`;
  the infinite series use ordered limits, not unconditional `HasSum`.

### AAR-7.4.1–7.6.4: positive polynomial sums (pp. 381–391)

- Newly admitted in `DLMF.OrthogonalPolynomials.Real`:
  `sum_normalized_gegenbauer_pos`, `sum_jacobi_zero_second_parameter_pos`,
  `sum_normalized_jacobi_pos_of_parameter_lt`, `gegenbauer_cesaro_kernel_nonneg`
  (`PositivityCriteria.lean`).
- Corollary 7.6.4: existing admitted
  `DLMF.OrthogonalPolynomials.ultrasphericalPolynomial_cesaro_nonneg`.
- Turán infinite sine-transform positivity and the generating-coefficient lemma
  remain to acquire.

### AAR-7.7.1–7.7.5: Apéry–Beukers irrationality (pp. 391–395)

- Theorem 7.7.2: existing admitted `DLMF.OrthogonalPolynomials.irrational_riemannZeta_three`.
- New admissions in `OrthogonalPolynomials/Beukers.lean`:
  `integral_beukers_kernel_diagonal`, `integral_beukers_kernel_off_diagonal`,
  `integral_beukers_eq_triple`, `beukers_quotient_le`,
  `exists_integer_linear_form_beukers`, `exists_integer_linear_form_zeta_three_geometric`.
  These state the actual double/triple integrals, exact integer linear forms and bounds.
- `Nat.lcmUpto` is reused, not redefined. Its eventual bound by3^n is new proved `Nat.eventually_lcmUpto_lt_three_pow`,
  with the general `eventually_lcmUpto_lt_pow` in `DLMFMathlib/NumberTheory/LcmGrowth.lean`.
  Both have clean axiom audits, derived from PNT and log(lcm) with no all-n prime assumption.

### AAR-8.1.1–8.3.3: Selberg and Aomoto integrals (pp. 402–410)

- Existing proved `DLMF.Selberg.selberg_integral`, `selberg_integral_one`,
  `aomoto_integral`; Mehta full domain: `DLMF.Gamma.selberg_hermite`.
- Existing `DLMF.Gamma.selberg_laguerrePolynomialL` requires positive coupling;
  newly admitted `DLMF.Selberg.laguerre_selberg_moment` gives the full domain,
  canceling the coupling quotient before the `n=1` exceptional specialization.
- New admissions in `IntegralExtensions.lean`: `selberg_elementary_symmetric_moment`,
  `selberg_mixed_moment`, `simplex_selberg_moment` (corrected missing factor included).
- New admitted `selberg_mixed_moment_canceled` in the same module includes every
  convergent parameter. It cancels the first j+k−n overlap factors against the last
  j+k−n denominator factors before evaluation, so no removable-value exclusion remains.

### AAR-8.4.1–8.4.4: Anderson's interlacing integral (pp. 411–415)

- New admissions `DLMF.Selberg.dixon_anderson_integral`, `interlacing_partial_fractions`
  (`IntegralExtensions.lean`). New explicit `interlacingResidue` has proved defining API;
  new admissions `interlacingResidue_pos_sum`,
  `existsUnique_interlacing_roots_of_residues`, `interlacingResidue_jacobian` in
  `Selberg/InterlacingCoordinates.lean` acquire the actual residue formula, inverse
  simplex map, derivative and absolute Vandermonde Jacobian.
- Three new polynomiality criteria in namespace `Complex`:
  `exists_polynomial_of_integer_values_of_type_lt_log_two`,
  `exists_polynomial_of_integer_derivatives_of_type_lt_gelfond`,
  `exists_polynomial_of_integer_derivatives_of_type_lt_selberg`
  (`DLMFMathlib/Analysis/Complex/IntegerValues.lean`, admitted).

### AAR-8.5.1–8.5.5: equilibrium and root discriminants (pp. 415–419)

- Root discriminants already proved: `DLMF.OrthogonalPolynomials.jacobiPolynomialP_prod_sq_sub`
  (`JacobiDiscriminant.lean`), `laguerrePolynomialL_discriminant` and
  `hermitePolynomialH_discriminant` (`BoundsZeros/Discriminants.lean`). These are root
  products; no leading-coefficient discriminant factor is lost.
- New `DLMF.Selberg.jacobiElectrostaticProduct` with proved unfolding and newly admitted
  `jacobiElectrostaticProduct_maximizes_iff`, `jacobiElectrostaticProduct_sq_maximum`,
  `laguerreElectrostaticProduct_maximizes_iff`, and
  `hermiteElectrostaticProduct_maximizes_iff` in `EquilibriumAndTrace.lean`.
- Parameter monotonicity: new admitted
  `jacobiExtended_shifted_zero_lt_of_first_parameter_lt` and
  `jacobiExtended_shifted_zero_lt_of_second_parameter_lt` in
  `OrthogonalPolynomials/JacobiParameterZeros.lean` compare every increasingly ordered
  shifted zero, with the directions for `P_n(1-2x)` explicit.

### AAR-8.6.1–8.6.7: Siegel and trace inequalities (pp. 419–425)

- Arithmetic–geometric mean and its equality condition: Mathlib
  `Real.geom_mean_le_arith_mean_weighted` and
  `geom_mean_eq_arith_mean_weighted_iff_of_pos`. Equal positive weights `1/n`
  specialize the latter to equality precisely when all entries coincide.
- Siegel refinement: existing admitted `DLMF.Selberg.siegel_inequality`; the two-point
  equality `siegel_inequality_two` is existing proved.
- Newly admitted in `DLMF.Selberg.EquilibriumAndTrace`: `existsUnique_siegelParameter`,
  `discriminant_le_mean_pow` (Schur), `eventually_trace_gt_siegelConstant` (squarefree
  monic integer polynomial form), and `trace_gt_three_halves` (irreducible form with
  the linear and quadratic exceptions explicit).
- Lemma8.6.3: newly admitted `existsUnique_laguerre_discriminant_parameter` and
  `siegelDiscriminant_le_laguerre_maximum` in `Selberg/ConstrainedDiscriminant.lean`
  give the unique parameter, exact upper bound and all Laguerre-zero equality cases.

### AAR-8.7.1–8.9.1: circle equilibrium and constant terms (pp. 425–430)

- Circle energy: newly admitted `DLMF.Selberg.prod_unitCircle_dist_le` and
  `prod_unitCircle_dist_eq_iff` give the product inequality and rotated-regular-polygon
  equality cases. The product also handles collisions; taking logarithms requires
  distinct points, unlike Lean's totalized `log 0`.
- The first nearly-poised sum: existing proved `DLMF.Selberg.nearly_poised_3F2`.
- The other four nearly-poised finite sums are newly admitted
  `nearly_poised_threeFTwo_second`, `third`, `fourth`, `fifth` in
  `Selberg/NearlyPoisedSummations.lean`. All denominator exclusions concern only
  the finite sum, and removable factors on the right are canceled.
- AAR8.9.1(a) is a false source formula, discussed under Additional source review below.

- Actual finite Laurent constant-term acquisitions: newly admitted
  `AddMonoidAlgebra.coeff_zero_dyson` and `coeff_zero_morris` in
  `DLMFMathlib/Combinatorics/DysonMorris.lean`. The exponent group is
  `Fin n →₀ ℤ`, and coefficients may lie in any characteristic-zero field.
  Empty dimension and zero exponents are retained. These do compute the constant
  term, unlike the pre-existing factorial-quotient arithmetic lemma.

### AAR-8.10.4–8.11.2: Hasse–Davenport and finite-field Selberg (pp. 430–439)

- Hasse–Davenport: existing admitted `DLMF.Selberg.hasse_davenport`, allowing trivial
  multiplicative character and requiring a nontrivial additive character.
- Finite-field Selberg: existing admitted `selberg_finite_field` includes a generating
  character, odd field, every finite regularity condition and the correct discriminant factor.
- Norm/trace: Mathlib `FiniteField.algebraMap_trace_eq_sum_pow`,
  `algebraMap_norm_eq_prod_pow`, `algebraMap_norm_eq_pow_sum`;
  pinned `TauCeti.FiniteField.map_minpoly_eq_prod_orbit` supplies the conjugate-root product.
- Signed norm/trace identities are proved upstream
  `Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly` and
  `Algebra.PowerBasis.trace_gen_eq_nextCoeff_minpoly` (Mathlib `RingTheory/Norm/Basic`
  and `RingTheory/Trace/Basic`), applied to the power basis of the degree-m generator.
- Newly admitted `Polynomial.exists_prod_monic_irreducibles_degree_dvd` and
  `sum_resultant_mulChar_eq_zero` in
  `DLMFMathlib/NumberTheory/FiniteField/ResultantCharacter.lean` give the irreducible
  product and Lemma8.11.1 coefficient cutoff. The modulus is nonconstant; each positive
  irreducible multiplicity is nonzero modulo q−1, as required for the primitive character.
- New `DLMF.Selberg.finiteFieldSelbergSum` has proved defining API; newly admitted
  `finiteFieldSelbergSum_succ` in `FiniteFieldRecurrence.lean` gives the induction
  recurrence with every exponent regularity condition.

### AAR-9.1–9.5: harmonic decomposition and dimension (pp. 445–454)

- Homogeneous harmonic polynomials: pinned TauCeti `MvPolynomial.laplacian`,
  `normSq`, `harmonicSubmodule`; restriction `MvPolynomial.harmonicSphereRestriction`.
- Fischer direct decomposition: pinned proved
  `MvPolynomial.disjoint_ker_laplacian_map_mulLeft_normSq` and
  `harmonicSubmodule_sup_map_mulLeft_normSq`; iterated decomposition:
  `homogeneousSubmodule_eq_iSup_map_mulLeft_normSq_pow`.
- Dimensions: pinned proved `MvPolynomial.finrank_harmonicSubmodule_add_two`;
  three-dimensional closed formula existing proved
  `DLMF.SphericalHarmonics.harmonicHomogeneousDim_three`.
- Orthogonality: existing proved `DLMF.SphericalHarmonics.harmonicHomogeneous_orthogonal`.
- Full arbitrary-function polar Laplacian and orthogonal covariance are newly admitted
  `InnerProductSpace.laplacian_eq_polar` and `laplacian_comp_linearIsometryEquiv` in
  `DLMFMathlib/Analysis/InnerProductSpace/PolarLaplacian.lean`. Surface polynomial
  eigenvalues are newly admitted `spherical_laplacian_eigenvalue` in
  `SphericalHarmonics/HarmonicDecomposition.lean`. Algebraic rotation invariance is
  proved pinned `MvPolynomial.laplacian_linearSubst_of_mul_transpose_eq_one` and
  `linearSubst_mem_harmonicSubmodule`.

### AAR-9.6.1–9.8.1: zonal and addition formulas (pp. 454–463)

- Existing proved dimension-three `DLMF.SphericalHarmonics.spherical_addition`,
  `funk_hecke`; continuous-parameter `ultrasphericalPolynomial_addition` for `λ > 1/2`.
- New admissions in `HarmonicDecomposition.lean`: `exists_zonal_generator`,
  `exists_unisolvent_sphere_points`, `spherical_addition_dimension`, `funk_hecke_dimension`.
- Probability-normalized Y_l^m are sqrt(4π) times canonical
  `DLMF.Legendre.sphericalHarmonic`; its defining associated-Legendre formula,
  `sphericalHarmonic_negative_order` and proved `sphericalHarmonic_orthonormal`
  (`Legendre/Harmonics.lean`) give the exact phases and normalization.
- Newly admitted `DLMF.SphericalHarmonics.ultrasphericalPolynomial_addition_of_pos`
  in `GegenbauerContinuation.lean` cancels all addition coefficients into Jacobi form
  and covers every λ>0, including λ=1/2. Newly admitted
  `tendsto_ultrasphericalPolynomial_div_at_one_zero` gives the dimension-two
  Chebyshev/cosine interpretation, retaining the normalized polynomial limit.

### AAR-9.9.1: Poisson extension (pp. 463–464)

- Pinned proved `TauCeti.harmonicOnNhd_ballPoissonIntegral`,
  `tendsto_ballPoissonIntegral`, `eqOn_ballPoissonIntegral_of_harmonicOnNhd`
  give harmonicity, continuous boundary values and uniqueness for real data.
  Applying to real and imaginary parts gives the complex result.
- Existing proved `DLMF.SphericalHarmonics.ballPoissonIntegral_reproduces`,
  `poissonKernelBall_reproduces`, `poissonKernelBall_eq_area_mul` connect conventions.
  The area factor converts `Measure.toSphere` to the book's probability measure.
- New admitted `DLMF.SphericalHarmonics.tendstoUniformlyOn_poissonKernel_gegenbauer`
  in `PoissonSeries.lean` gives joint uniform convergence for |r|≤R<1 and all
  angular arguments in [-1,1].

### AAR-9.10.2–9.10.6: Fourier–Bessel reduction (pp. 464–466)

- New admitted targets in `SphericalHarmonics/FourierBessel.lean`:
  `DLMF.SphericalHarmonics.integral_sphere_exp_mul_harmonic` (9.10.2),
  `fourierInv_radial_mul_surface_harmonic` (9.10.3),
  `integral_homogeneous_harmonic_fourierInv` (9.10.4, Schwartz-test equality),
  `fourierInv_radial_mul_solid_harmonic` (9.10.5),
  `fourierInv_gaussian_mul_harmonic` (9.10.6).
- The positive Fourier sign is Mathlib's inverse Fourier convention. Surface measure
  is unnormalized; no extra ω_n denominator is inserted. The zero harmonic case is
  elementary; the radial theorems assume nonzero P to recover radial integrability.
- All six new Fourier–Bessel targets now explicitly take arbitrary complex-coefficient
  `MvPolynomial.harmonicSubmodule` elements. The sphere transform is stated with the
  entire normalized 0F1 kernel, including every complex frequency and zero. The new
  `fourierInv_radial_mul_surface_harmonic_zero` gives the exact zero-frequency value;
  its continuous interpretation follows from L¹ Fourier continuity.

### AAR-9.11–9.16: compact groups, SU(2), Jacobi matrix entries (pp. 466–478)

- Compact averaging/unitarization: pinned proved `ContRepresentation.isUnitarizable`
  (`TauCeti.RepresentationTheory.Compact.Unitarizable`). Complete reducibility:
  `Representation.isSemisimpleRepresentation_of_continuous` (`Compact.Semisimple`).
- Schur matrix-entry orthogonality: pinned proved
  `ContRepresentation.schur_orthogonality_basis` and `schur_orthogonality`
  (`Compact.SchurOrthogonality`).
- SU(2) irreducibles/classification: pinned proved
  `TauCeti.SU2.isIrreducible_symPower`, `existsUnique_nonempty_equiv_symPower`.
- Character formula and Weyl integration: pinned proved
  `TauCeti.SU2.character_symPower_torusExp_eq_sin_div_sin`, `weyl_integration_formula`.
- Double cover: existing proved `DLMF.SphericalHarmonics.realSpinThreeEquivSpecialUnitary_negOne`
  and pinned proved `TauCeti.SU2.toSO3_surjective`, `toSO3_eq_one_iff`, `ker_toSO3`
  in `RepresentationTheory/SU2/Adjoint.lean` give the exact canonical cover and kernel.
- New canonical `suTwoPolynomialMatrix` has proved finite-sum API; newly admitted
  `suTwoPolynomialMatrix_mul`, `_one`, `_conjTranspose_mul`, `_rotation`, `_neg_one`
  and `exists_equiv_suTwoPolynomialMatrix` in `CompactGroupRepresentations.lean`
  give the exact monomial representation, unitary normalization and Jacobi entries.
- New `suTwoEulerMatrix` has proved defining API; new admitted `suTwoEulerMatrix_mem`
  and `integral_haarProb_suTwo_eq_euler_integral` in `EulerHaar.lean` give the source
  phases, Euler ranges and probability density sinθ/(16π²).
- New admissions `exists_representation_soThree_comp_toSO3_iff_even` and
  `exists_equiv_symPower_harmonicSubmodule` give parity descent and the complex
  degree-k harmonic-polynomial model of Sym^(2k). No generic representation
  structure is duplicated.

### AAR-10.1–10.2.4: q-calculus and the q-binomial theorem (pp. 481–493)

- Canonical q-products, negative indices, q-derivative, Jackson integral and Gaussian
  coefficients are `DLMF.QSeries` Basic declarations, with proved elementary APIs.
- Theorem10.2.1: existing proved `q_binomial_theorem`; Corollary10.2.2:
  `tsum_div_qPochhammer`, q-exponential and finite q-binomial identities.
- New admitted `jacksonIntegral_integration_by_parts`, `tendsto_jacksonIntegral_one`
  in `QSeries/ClassicalLimitsAndParts.lean` retain the source's endpoint summability.
- Lemma10.2.3: new admitted `Real.antitoneOn_exp_sub_div_one_sub_exp`
  (`DLMFMathlib/Analysis/SpecialFunctions/Exp/RatioMonotonicity.lean`), corrected exponent sign.
- Theorem10.2.4: new admitted `tendstoUniformlyOn_qPochhammerInf_ratio`,
  `tendstoLocallyUniformlyOn_qPochhammerInf_ratio` give both uniform domains.
- Q-derivative powers/limits are also covered by new shared `qDeriv_cpow_real`,
  `tendsto_qDeriv_of_hasDerivAt_real`. Product zero multiplicities and exact local-uniform
  q-product convergence are now acquired in `QSeries/ProductConvergence.lean`:
  `tendstoLocallyUniformly_qPochhammer`, `analyticOnNhd_qPochhammerInf`,
  `analyticOrderAt_qPochhammerInf` (new admissions). Every zero is simple; q=0
  retains precisely the factor 1−a.

### AAR-10.3.1–10.3.5: q-gamma and q-beta (pp. 493–496)

- Definition and shifts: canonical `DLMF.QSeries.qGamma`, `qGamma_one`, `qGamma_add_one`.
- Theorem 10.3.1: existing proved `DLMF.QSeries.q_beta_integral`.
- Theorem 10.3.3 / Corollary 10.3.4: existing proved `DLMF.Gamma.qGamma_mono_left`,
  `qGamma_mono_right`, `qGamma_two`, `tendsto_qGamma_one`. New admitted
  `qGamma_mono_of_two_lt` in `Gamma/QGammaExtensions.lean` acquires the missing
  x>2 base comparison and strict upper bound by Gamma.
- New admissions in `Gamma/QGammaExtensions.lean`: `qGamma_pos_logConvex`,
  `eq_qGamma_of_logConvex`, `qGamma_multiplication` (10.3.5),
  `differentiable_inv_qGamma`, `inv_qGamma_eq_zero_iff`.
  The zero lattice includes every 2πik/log q translate, not only nonpositive integers.

### AAR-10.4.1–10.6.1: triple product, bilateral sum and sums of squares (pp. 496–508)

- Triple product: existing proved `DLMF.QSeries.jacobi_triple_product`.
  Pentagonal/cube consequences: `DLMF.NumberTheory.eulerReciprocal_pentagonal`,
  `DLMF.Theta.hasSum_eulerFunction_pow_three`; Gauss triangular identity:
  `DLMF.Combinatorics.hasSum_pow_triangular_mul_eulerFunction`.
- Ramanujan 1psi1: existing proved `DLMF.QSeries.ramanujan_1psi1_of_regular` and
  `ramanujan_1psi1`, preserving bilateral denominator regularity.
- Two/four squares: existing proved `DLMF.NumberTheory.sumSquaresCount_two`,
  `sumSquaresCount_four` (odd/even formula equivalent to the divisor sum).
- x²+2y²: new `sumSquareTwiceSquareCount` with proved defining count and admitted
  `finite_sumSquareTwiceSquare_representations`, `sumSquareTwiceSquareCount_zero`,
  `sumSquareTwiceSquareCount_eq_divisor_classes` in `BinaryQuadraticCounts.lean`.
- Local uniformity is newly admitted
  `DLMF.QSeries.tendstoLocallyUniformlyOn_jacobi_triple_product` in
  `ProductConvergence.lean`. The exact source divisor display is newly admitted
  `DLMF.NumberTheory.sumSquaresCount_four_eq_sum_divisors_not_dvd_four` in
  `BinaryQuadraticCounts.lean`, with positive n and signed ordered representations.

### AAR-10.7.1–10.7.2: theta and Jacobi elliptic functions (pp. 508–513)

- All four canonical theta functions and q/τ bridges are in `DLMF.Theta.Basic`.
  Products: `jacobiThetaOneTau_hasProd`, `jacobiThetaOneTau_hasProd_sin` and companion APIs.
- Proposition10.7.1: existing proved `jacobiThetaOneDerivNullTau_eq_mul`;
  fourth-power identity: `jacobiThetaNull_fourth_power`.
- Canonical elliptic theta quotients are `DLMF.JacobiElliptic` Basic functions.
  Existing proved derivative theorems `hasDerivAt_jacobiSn`, `hasDerivAt_jacobiCn`,
  `hasDerivAt_jacobiDn` preserve the modulus-domain/pole exclusions.
- Theorem10.7.2: existing proved `jacobiSn_hasSum_fourier`, `jacobiCn_hasSum_fourier`,
  `jacobiDn_hasSum_fourier`; their strip hypotheses match after v=πu/(2K).
- Individual zero/quasiperiod and nome/K relation adapters still require exact mapping;
  no replacement theta definitions are introduced.

### AAR-10.8.1–10.8.2: Askey–Wilson and Rahman beta integrals (pp. 513–520)

- New `DLMF.QHypergeometric.pairedShiftedFactorial` and proved defining lemma
  retain complex paired products, including complex bases.
- New admitted `askey_wilson_integral` (10.8.1), `nassrallah_rahman_integral` (10.8.2)
  in `QHypergeometric/ContinuousBetaIntegrals.lean` include Bochner integrability.
  Rahman's A/a_i is explicitly the product of the other four parameters, including a_i=0.

- The explicit q-to-one integral scaling is newly admitted
  `tendsto_askeyWilson_integral_wilson` in `QHypergeometric/WilsonIntegralLimit.lean`.
  Its factor `(q;q)_∞^6(1−q)^(5−2Σa_j)` is explicit and the limit is the actual
  paired-Gamma Wilson half-line integral for fixed positive shape parameters.

### AAR-10.9.1–10.10.3: basic hypergeometric transformations (pp. 520–527)

- Existing proved `DLMF.QSeries.q_gauss_summation`, `heine_transformation`,
  `heine_transformation_two`, `heine_transformation_three`.
- Existing `DLMF.QHypergeometric.qPhi3_sears_first`, `qPhi3_sears_second`,
  terminating first/second/third/fourth, `qPhi4_balanced_transformations` in `Transformations.lean`
  supply the terminating/analytic transformations with explicit denominator conditions.
- Q-Chu and q-Pfaff–Saalschütz have canonical finite forms, including shared finite-only
  q-parameter refinements from the Duverney acquisition.
- Exact equation matching: 10.9.1 is proved `heine_first`, 10.9.2 is
  `q_gauss_summation`, 10.9.3 is `q_bailey_daum`; 10.10.1 is `heine_third` in
  `BasicSummations/Heine.lean`, which needs only the two argument-disk inequalities
  and actual regular lower parameter, unlike the older QSeries third-transformation wrapper.
- Finite 10.10.2 is the proved cleared `searsSum_transformation_first`;
  the two displayed finite 10.10.3 formulas are `phiSum_three_two_second` and
  `searsSum_three_two_fourth`, after swapping their b,c to the source a,b order.
  These low-level declarations in `SearsTransformation.lean` require nonzero lower
  q-Pochhammers only through n; their `q*q⁻¹^n` equals `q^(1−n)`.
  The bridges `qPhi_four_three_eq_searsSum`, `qPhi_three_two_eq_phiSum` and
  `qPhi_three_two_eq_searsSum` identify the displayed canonical finite series exactly.
- The two infinite 10.10.3 formulas are proved `qPhi3_sears_first` and
  `qPhi3_sears_second` (interchange a,b in the latter), with both argument-norm
  restrictions and all printed product denominators retained. Thus no global lower
  lattice restriction is imposed on the finite source transformations.

### AAR-10.11.1: Rogers polynomials and continuous q-Hermite (pp. 527–532)

- Theorem 10.11.1: new admitted `DLMF.OrthogonalPolynomials.qGegenbauer_integral_mul`
  gives the full norm, including equal degrees, and paired-product continuation for complex q,β.
- Existing definitions `DLMF.QSeries.qGegenbauer`, `continuousQHermiteLaurent` are reused;
  their argument is exp(iθ), corresponding to polynomial variable cos θ.
- New admissions in `QFamilies/RogersAndHermite.lean`: `qGegenbauer_recurrence`,
  `hasSum_qGegenbauer_generating`, `continuousQHermiteLaurent_recurrence`,
  `hasSum_continuousQHermiteLaurent_generating`, `continuousQHermiteLaurent_mul`,
  `hasSum_continuousQHermiteLaurent_poisson`.
- Existing proved `continuousQHermite_orthogonality` gives its full norm.
  The initial values are newly proved in the foundational layer:
  `DLMF.QSeries.qGegenbauer_zero`, `qGegenbauer_one`, and
  `DLMF.OrthogonalPolynomials.continuousQHermiteLaurent_zero`,
  `continuousQHermiteLaurent_one`. Their definitions and normalizations are unchanged.

### AAR-10.12.1–10.12.8: Mellin interpolation and modularity (pp. 532–542)

- Theorem10.12.1, contour independence and local series: existing proved dependency
  `Complex.RamanujanClass.hasSum_mellinInv`, `mellinInv_eq_mellinInv`,
  `Complex.ramanujan_master_theorem` in lean-codes `RamanujanMaster.lean`, already imported by DLMF.
- Corollary10.12.2: existing `DLMF.QHypergeometric.mellinQBeta_integral`,
  `mellinQBetaValue_eq`, `tendsto_mellinQBetaValue` retain the removable integer limits.
- Corollary10.12.3: generic Carlson uniqueness is proved as
  `Complex.eqOn_zero_of_natCast_eq_zero`; the exact Ramanujan half-plane
  specialization is newly admitted `Complex.RamanujanClass.eq_zero_of_natCast_eq_zero`
  in `DLMFMathlib/Analysis/SpecialFunctions/RamanujanUniqueness.lean`.
- Lemma10.12.4 holomorphy: existing proved `DLMF.AlgebraicAnalytic.differentiableOn_mellin`;
  new admitted uniqueness `MeasureTheory.ae_eq_zero_of_mellin_vertical_eq_zero`.
- Theorem10.12.5: newly admitted
  `Real.integral_rpow_neg_half_mul_exp_neg_mul_sub_div` in
  `DLMFMathlib/Analysis/SpecialFunctions/Integrals/ReciprocalExponential.lean`
  retains `a>0,b≥0`, including the zero endpoint, and asserts absolute integrability.
- Theorem10.12.6: existing proved `DLMF.Theta.jacobiThetaThreeTau_neg_inv` / Mathlib theta S-law.
- Theorem10.12.7: Mathlib `completedRiemannZeta_one_sub` (proved).
- Theorem10.12.8: pinned proved `TauCeti.ModularForm.eta_add_one`, `eta_smul`,
  `etaMultiplier_S` retain the phase multiplier, not just the magnitude.

### AAR-11.1.1–11.3.1: partition definitions and Omega elimination (pp. 553–559)

- Mathlib `Nat.Partition`, `restricted`, `countRestricted` supply the canonical partition
  type and restriction families. General Glaisher: proved
  `Nat.Partition.card_restricted_eq_card_countRestricted`; Euler is `card_odds_eq_card_distincts`.
- Unrestricted formal products: Mathlib `hasProd_powerSeriesMk_card_restricted`.
  New `DLMF.Combinatorics.partitionCountMultiplicityIn` with proved defining count;
  new admissions `hasProd_partitionCountMultiplicityIn`,
  `hasProd_partitionCountMultiplicityIn_formal` cover arbitrary allowed-part sets.
- New canonical formal Omega: `LaurentPolynomial.nonnegativeCoefficientSum`,
  `MvPowerSeries.omegaNonnegative`, with proved coefficient API in
  `DLMFMathlib/Combinatorics/PartitionAnalysis.lean`.
- Lemmas 11.2.1–3 / Proposition 11.3.1: new admissions
  `omegaNonnegative_geometric_two`, `omegaNonnegative_geometric_two_shift`,
  `omegaNonnegative_geometric_many`, `omegaNonnegative_geometric_three`,
  `omegaNonnegative_geometric_three_square` (namespace `MvPowerSeries`).
- Theorem 11.2.2: existing proved `DLMF.Combinatorics.hasSum_partitionCountAtMostParts`.
- Triangle example: new `trianglePartitionCount` with proved defining finite count and
  admitted `hasSum_trianglePartitionCount` in `Combinatorics/PartitionRefinements.lean`.

### AAR-11.4.1–11.4.6: refined generating functions (pp. 559–563)

- New `DLMF.Combinatorics.partitionCountExactGap` with proved defining count.
- Theorems 11.4.1–2: new admitted `hasSum_partitionCountExactGap`,
  `partitionCountExactGap_formal` include all lengths, minimum gaps and positive least parts.
- Theorem 11.4.3: existing proved `hasSum_distinct_largest`,
  `hasSum_partitionCountBoxed_two`; the full fixed-length/fixed-largest double
  refinements are newly admitted `hasSum_partitionCountExactGapLargest_zero`
  and `hasSum_partitionCountExactGapLargest_one` in `PartitionFormalRefinements.lean`.
- Theorem 11.4.4: existing proved `hasSum_partitionCountBoxed`,
  `hasSum_partitionCountAtMostDistinctBoxed`. Corollary 11.4.5: `sum_qBinom_triangle_eq_prod`.
- Theorem 11.4.6: existing proved `DLMF.NumberTheory.hasSum_partitionFunction`,
  plus new admissions `hasSum_partitionCountExactGap_zero_bivariate`,
  `hasSum_partitionCountExactGap_one_bivariate`, `hasSum_partitionCountExactGap_two_bivariate`.
  Coefficientwise formal bivariate identities are newly admitted
  `coeff_length_partition_product`, `coeff_length_distinct_partition_product`,
  `coeff_length_gap_two_partition_sum` in `PartitionFormalRefinements.lean`.
  They live in `PowerSeries (Polynomial ℤ)`, with finite factors sufficient for
  each requested q coefficient and the length recorded by the polynomial variable.

### AAR-11.5.1–11.7: conjugation, Rogers–Ramanujan and congruences (pp. 563–573)

- Conjugation: Mathlib `Nat.Partition.conjugate`, `conjugate_conjugate`;
  existing proved `DLMF.Combinatorics.card_parts_conjugate`,
  `partitionCountAtMostParts_eq_card_parts_le`. The exact boxed symmetry is newly
  proved `partitionCountBoxed_comm` in `RestrictedPartitions.lean`.
- Durfee and self-conjugacy: new admitted `hasSum_durfee_square`,
  `nonempty_equiv_selfConjugate_distinct_odd` in `PartitionRefinements.lean`.
- Rogers–Ramanujan products: existing proved `DLMF.Bailey.rogers_ramanujan_first`,
  `rogers_ramanujan_second`; partition forms `DLMF.Combinatorics.partitionCountDiff_two_eq`,
  `partitionCountDiffTwoNoOne_eq` are proved.
- Congruences modulo 5/7: existing proved
  `DLMF.NumberTheory.RamanujanCongruences.five_dvd_card_partition`, `seven_dvd_card_partition`.
- Modulo 11: new admitted `DLMF.NumberTheory.eleven_dvd_card_partition`.
- Five-dissection: existing proved `hasSum_partitionFunction_five`.
  Seven-dissection: new admitted `hasSum_partitionFunction_seven`,
  `partitionPowerSeries_seven_dissection` in `NumberTheory/PartitionDissections.lean`.
  The explicit diagonal-hook bijection is newly admitted
  `exists_equiv_selfConjugate_distinct_odd_diagonalHooks`, using actual
  `diagonalHookLengths` with proved membership API. Formal Durfee is
  `hasSum_durfee_square_formal`, both in `PartitionDiagrams.lean`.
  The exact cleared five-dissection is newly admitted `partitionPowerSeries_five_dissection`
  in `NumberTheory/PartitionDissections.lean`.

### AAR-12.1.1: finite Rogers identities (pp. 577–582)

- New explicit definitions `DLMF.QSeries.finiteRogersEven`, `finiteRogersOdd`,
  with proved defining sums and no negative natural exponents.
- New admissions `finiteRogers_eq_inv_qPochhammer`, `finiteRogers_recurrences`
  acquire Lemma 12.1.1 and both recurrence identities.
- Infinite Rogers–Ramanujan products already proved in `DLMF.Bailey.rogers_ramanujan_first`,
  `rogers_ramanujan_second`; the exact bilateral numerator forms are newly admitted
  `hasSum_rogersRamanujan_first_bilateral`, `hasSum_rogersRamanujan_second_bilateral`
  in `QSeries/RogersBilateral.lean`, with integer exponents and the zero-base value retained.

### AAR-12.2.1–12.2.3: Bailey transform and chain (pp. 582–586)

- Existing proved `DLMF.Bailey.IsBaileyPair`, `bailey_lemma`, `bailey_relation`,
  `unit_pair`, `bailey_limit_relation`, `sum_unit_bailey`.
- Existing `DLMF.QHypergeometric.general_bailey_transform`, `IsBaileyChain`,
  `limiting_bailey_transform`, `rogersBaileyAlpha`, `rogersBaileyBeta`,
  `isBaileyPair_rogersBailey` supply the general transform and chain.
- Lemma12.2.2 is exactly proved `general_bailey_transform`: its `Summable` on
  ℕ×ℕ with a triangular indicator is the source absolute double-sum/Fubini condition.
  Theorem12.2.3 is proved `DLMF.Bailey.bailey_relation` at each finite n, so only
  denominators through the retained indices are excluded. `bailey_lemma` packages
  these relations over all n without introducing an analytic summability assumption.
- The exact weak-form Lemma12.2.1 hypothesis is newly acquired as admitted
  `limiting_bailey_transform_of_summable_double` in `BaileyAbsoluteConvergence.lean`.
  It concludes both separate summabilities, which the older limiting wrapper assumes.
  The unit-pair cancellation uses canonical `DLMF.Bailey.unitD`; the a=1 removable
  specialization is retained by `VeryWellPoised.coefficient` below.

### AAR-12.3–12.4: Watson, Jackson and multiseries (pp. 586–590)

- Existing proved Watson: `DLMF.Bailey.watson_transformation` and
  `watson_transformation_rational`.
- Existing Jackson: `DLMF.QHypergeometric.jackson_eight_phi_seven`;
  limiting very-well-poised sums are in `HigherSummations.lean`.
- New `DLMF.QSeries.andrewsGordonTerm` is the explicit decreasing-tuple summand;
  new admitted `hasSum_andrewsGordon` is the full §12.4 multisum and product,
  with residues 0,±(k+1) excluded modulo 2k+3.
- New root-free `DLMF.QHypergeometric.VeryWellPoised.coefficient` and `value`
  in `QHypergeometric/VeryWellPoised.lean` reuse canonical Bailey `unitD`, with proved
  defining/constant/zero-argument API. New admitted `coefficient_one`,
  `qPhiTerm_eq_coefficient`, `hasSum_six_phi_five`, and
  `sum_eight_phi_seven_mul_denominator` retain the central `a=1` cancellation.
  The finite Jackson statement excludes denominators only through its final index
  and clears its final product quotient. Other inverted upper parameters are nonzero.

### AAR-A.1.1–A.1.6

- Existing proved `DLMF.AlgebraicAnalytic.infiniteProductConverges_iff_log`,
  `infiniteProductConverges_norm_iff`, `prod_mtest`, `prod_mtest_log`,
  `differentiableOn_of_tendstoUniformlyOn_prod` acquire the convergence and holomorphic-limit claims.
- Mathlib's `Multipliable`/`HasProd` APIs distinguish zero finite factors from nonzero tails.
- Full arbitrary-factor multiplicities are newly admitted
  `Complex.analyticOnNhd_product_zero_order` in
  `DLMFMathlib/Analysis/Analytic/InfiniteProduct.lean`, assuming analytic factors, a
  locally uniform product limit and absolute product convergence at each point.
  Pinned `analyticOrderAt_tprod_weierstrassFactorOne` covers only the genus-one special case.

### AAR-B.1.1–B.1.6: Abel and Cesàro summation (pp. 599–602)

- Existing proved `DLMF.AlgebraicAnalytic.hasAbelSum_of_tendsto`,
  `hasCesaroSum_of_tendsto`, `tendsto_cauchyProduct`.
- New admissions `Complex.tendstoUniformlyOn_partial_powerSeries_of_tendsto_sum`,
  `tendsto_tsum_powerSeries_of_tendsto_cesaro` (`DLMFMathlib/Analysis/Summability/Cesaro`).
- Existing proved Poisson/Fejér API in `DLMF.AlgebraicAnalytic`:
  `hasSum_abelPoissonKernel`, `integral_abelPoissonKernel`, `integral_fejerKernel`,
  `tendsto_abelMean`, `tendsto_fourierCesaroMean`, `tendstoUniformly_abelMean`,
  `tendstoUniformly_fourierCesaroMean` (`Summability/FourierSeries.lean`).
- Continuous periodic approximation is newly proved
  `DLMF.AlgebraicAnalytic.exists_uniform_fourierCesaroMean_sub_lt`
  in `Summability/FourierSeries.lean`, directly from uniform Fejér convergence.
  Endpoint compatibility is retained; unconditional sums do not replace ordered limits.

### AAR-B.2–B.3: higher means and fractional integrals (pp. 602–605)

- Existing canonical `DLMF.AlgebraicAnalytic.cesaroMeanOfOrder`,
  `HasCesaroSumOfOrder`, `HasCesaroIntegral`, `HasAbelIntegral`.
- New order inclusion `Complex.tendsto_cesaro_order_of_lt`
  (`DLMFMathlib/Analysis/Summability/Cesaro.lean`, admitted).
- Existing proved fractional monomial API as in AAR-2.9.1. Newly admitted
  `DLMF.AlgebraicAnalytic.fractionalIntegral_fractionalIntegral_of_integrable` and
  `ae_hasDerivAt_fractionalIntegral_half_twice` in `Summability/FubiniFractional.lean`
  give the full absolute-Fubini semigroup and a.e. local-L¹ Abel half-inversion.
  The book §B.3 introduces the noninteger integral summability definitions but does
  not assert a separate Cesàro-to-Abel integral theorem; no extra acquisition is inferred.

### AAR-B-exercises-9–10: Dirichlet and Hardy–Littlewood (pp. 608–609)

- Existing admitted `DLMF.AlgebraicAnalytic.tendsto_cesaro_of_abel_mean`
  is the Hardy–Littlewood theorem, with equivalent denominator `N+1`.
- Mathlib `DirichletCharacter.LFunction_apply_one_ne_zero`
  (`NumberTheory/LSeries/Nonvanishing.lean`) gives nonvanishing for every nonprincipal
  complex character. Its `DirichletCharacter.zetaMul_nonneg` gives the nonnegative
  divisor coefficients for quadratic characters; a real character has square one.
  Exact natural-order boundary identification is proved in pinned TauCeti as
  `DirichletCharacter.tendsto_sum_Icc_div_LFunction_one` in
  `LSeries/BoundaryConvergence/DirichletEulerProduct.lean`, for every nonprincipal
  complex character. This is a cutoff limit, and does not assert absolute summability.

### AAR-C.1.1–C.2.2: definition, uniqueness and algebra (pp. 611–614)

- Existing definition `DLMF.AsymptoticApproximations.HasPoincareExpansion`.
- Existing proved `hasPoincareExpansion_iff_tendsto`, `HasPoincareExpansion.unique`,
  `add`, `mul`, `inv` (`Basics/OrderSymbols.lean`); smaller-sector holomorphic
  differentiation `HasPoincareExpansion.deriv` (`Basics/Calculus.lean`).
- The strict erfc remainder and fixed-argument divergence are newly admitted
  `DLMF.Confluent.Real.erfc_asymptotic_remainder_strict` and
  `tendsto_erfc_asymptotic_term_norm` in `ErrorFunctions/AsymptoticStrictBounds.lean`.
  Reciprocal coefficient recurrence is proved Mathlib `PowerSeries.coeff_inv`, paired
  with proved `Asymptotics.HasAsymptoticPowerSeries.recip`; both pass axiom audit.
  Tail integration is proved `Asymptotics.HasAsymptoticExpansion.integral_Ioi_inv_pow`
  (`IntegralPowerSeries.lean`), also axiom-audited. The explicit damped oscillatory
  counterexample is newly acquired in
  `DLMFMathlib/Analysis/Asymptotics/NonDifferentiableExpansion.lean`: its derivative
  formula is proved, its null expansion and failure of a null derivative are admitted.

### AAR-C.3.1–C.4: Watson and gamma ratios (pp. 614–616)

- Full complex/fractional endpoint powers and uniform closed-subsector Watson
  expansion are shared newly admitted `Asymptotics.LiftedWatson.hasAsymptoticExpansion_transform`
  in `DLMFMathlib/Analysis/Asymptotics/LiftedWatson.lean`, with actual ray transforms
  and explicit endpoint expansion/exponential-growth predicate `IsKernel`.
  The fixed-ray half-plane versions are `Asymptotics.watson_lemma_sector_conditional`
  in `WatsonConditional.lean`; real positive order is its specialization.
- Existing proved real-axis `DLMF.Gamma.Gamma_ratio_expansion`, `stirlingRatioG_recurrence`
  (`Gamma/Asymptotics/ShiftedStirling.lean`). Shared new admitted
  `Gamma_ratio_sector_expansion` in `Gamma/SectorExpansions.lean` supplies the full
  closed-sector quotient expansion with the canonical Bernoulli-polynomial coefficients;
  `Gamma_ratio_centered_sector_expansion` supplies its centered version.

### AAR-D.2.1–D.3.2: summation and applications (pp. 617–623)

- TheoremD.2.1: existing proved `sum_range_succ_eq_integral_add` in
  `DLMFMathlib/Analysis/EulerMaclaurin.lean`, including canonical `periodicBernoulli`.
  Newly admitted `sum_Ioc_eq_integral_add_bernoulli` and
  `norm_sum_Ioc_sub_integral_sub_bernoulli_le` in
  `DLMFMathlib/Analysis/EulerMaclaurin/IntegerInterval.lean` give arbitrary integer
  endpoints, the precise periodic-Bernoulli supremum norm, and only local C^s
  assumptions with canonical within-derivatives at the endpoints.
- TheoremD.3.1: new admitted `DLMF.Zeta.exists_riemannZeta_log_bounds_near_one`
  in `Zeta/NearOneBounds.lean` gives both uniform bounds and the moving left boundary.
- TheoremD.3.2: shared admitted `DLMF.Gamma.logGammaStieltjesRemainder_eq_integral`
  on the principal slit plane; newly admitted
  `logGamma_eq_sum_sub_periodicBernoulli_integral` in `PeriodicStirlingRemainder.lean`
  is the exact printed periodic-B-only expression, including integrability.

### AAR-D.4.1: bounded-variation Poisson summation (pp. 623–627)

- The proved local integral input is
  `Real.tendsto_integral_mul_sin_div_of_boundedVariationOn` in
  `DLMFMathlib/Analysis/Fourier/DirichletJordan.lean`; the actual full Poisson
  spatial sum and symmetric Fourier sum are the newly admitted target below.
- New admitted `Real.tendsto_sum_Icc_fourier_of_boundedVariationOn_dominated`
  in `DLMFMathlib/Analysis/Fourier/PoissonBoundedVariation.lean` gives the full jump-average,
  absolute spatial convergence and symmetric Fourier limit under the stated envelope.
- Gaussian specialization follows from exact proved Mathlib
  `Complex.tsum_exp_neg_quadratic`, with arbitrary complex linear parameter and
  positive real part of the quadratic parameter. Substituting the linear parameter
  `−s*x`, multiplying by `exp(−π*s*x²)` and completing both squares gives the
  displayed shifted identity. The upstream theorem passed transitive axiom audit.

### AAR-D-exercise-6: Lipschitz summation (p. 627)

- New admitted `Complex.lipschitz_summation` in
  `DLMFMathlib/Analysis/SpecialFunctions/Gamma/LipschitzSummation.lean` asserts absolute
  convergence of both sides and the exact bilateral-to-unilateral identity.
  The hypotheses are Re x>0, 0<a<1, Re s>1, with right-half-plane powers.

### AAR-E.1–E.4.1

- Existing proved analytic inversion: `DLMF.AlgebraicAnalytic.lagrange_inversion`,
  `lagrange_burmann`; formal extraction `PowerSeries.coeff_lagrangeBurmann_basis`,
  `coeff_subst_inverse_coordinate` (`DLMFMathlib/RingTheory/PowerSeries/LagrangeBurmann`).
- Existing analytic quotient `Complex.hasSum_lagrangeBurmann_quotient` is partial.
- Formal residue substitution is already proved by pinned TauCeti
  `TauCeti.LaurentSeries.coeff_neg_one_substAlgHom_mul_derivative`
  (`RingTheory/LaurentSeries/Substitution/Basic.lean`), with coordinate order one.
- Newly admitted in `DLMFMathlib/RingTheory/PowerSeries/LagrangeIdentities.lean`:
  `PowerSeries.existsUnique_eq_X_mul_subst`,
  `natCast_mul_coeff_subst_of_eq_X_mul_subst`, `coeff_lambert_binomial`,
  `coeff_lambert_binomial_div`, `sum_lambert_binomial_convolution`,
  `coeff_mul_eq_of_binomial_weighted_subst`. These cover the full formal statements
  over every characteristic-zero field, with removable convolution factors canceled.

### AAR-F.1–F.3: ordinary points, indicial equation and resonance

- Existing proved `DLMF.AlgebraicAnalytic.exists_isLinearODE2SolutionOn`,
  `isLinearODE2SolutionOn_unique` give the local analytic ordinary-point theory.
  The regular-singular targets `DLMF.AsymptoticApproximations.frobenius_solutions`
  and `frobenius_log_solution` are existing admissions, with the convergence radius
  and nonresonant/repeated-root scopes stated explicitly.
- New shared ODE targets in `DLMFMathlib/Analysis/ODE/EulerEquation.lean`:
  `Complex.euler_equation_cpow`, `euler_equation_cpow_mul_log`, `wronskian_cpow`,
  `wronskian_cpow_mul_log`, `exists_euler_solution_eq_cpow_linear_combination`,
  `exists_euler_solution_eq_cpow_log_linear_combination`,
  `hasDerivAt_exp_const_div_sub`, `linearODEIrregularAt_first_order_inverse_square`.
  The sign of the irregular exponential is +c/(z−a).
- New formal recurrences in `DLMFMathlib/Analysis/ODE/FormalSeries.lean`:
  `PowerSeries.coeff_ordinary_second_order`, `indicial_eq_zero_of_formal_frobenius`,
  `coeff_formal_frobenius` (admitted, general characteristic-zero field).
- New admitted `frobenius_obstruction_eq_zero_iff` in
  `AsymptoticApproximations/ODE/FrobeniusResonance.lean` gives exactly the finite
  resonance obstruction and a convergent normalized smaller-root analytic factor iff
  that obstruction vanishes. It states the solution on every punctured subdomain
  with an analytic logarithm, so it retains arbitrary chosen branches.
  Repeated-root logarithmic necessity is included in existing admitted
  `frobenius_log_solution` through its `c=1` conclusion; the nonresonant pair and
  positive radius are in `frobenius_solutions` and `FrobeniusMajorants`.
  These source convergence targets remain admissions, rather than completed proofs.

## Additional source review

- AAR8.9.1(a), printed p.429/Chapter08 PDF29: the printed denominator (α)_{2k}
  is false. At α=β=1,k=1 the finite 3F2 sum is 1/3 whereas the printed RHS is 1.
  Existing proved `DLMF.Selberg.nearly_poised_3F2` has (α+1)_{2k}, yielding 1/3.
  The source/synopsis assertion is blocked pending review; no false theorem was admitted.
  The source and synopsis files are unchanged.
- Other four cases of 8.9.1 are newly admitted as `DLMF.Selberg.nearly_poised_threeFTwo_second`,
  `nearly_poised_threeFTwo_third`, `nearly_poised_threeFTwo_fourth`,
  `nearly_poised_threeFTwo_fifth` in `NearlyPoisedSummations.lean`. Removable factors are
  canceled and only finite lower-factorial regularity is imposed.
