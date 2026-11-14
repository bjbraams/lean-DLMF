# Temme Chapter11 acquisition ledger

All **21** entries and their distinct subclaims are audited in lookup order Mathlib,
TauCeti, DLMF. Pins: Mathlib `1b1ccf4b088b32fa3f23f2de1127433254a81e1e`, TauCeti
`396c3bd971e9722aa8656231760e710fe641d8cf`, Lean `v4.36.0-rc2`. The source synopsis,
pins and existing definition bodies are unchanged. “Existing” does not imply proved;
the transitive Lean axiom audit below distinguishes proofs, admissions and dependence on
admissions. Newly admitted statements remain in the theorem layer; defining APIs are proved.

## TEM-11-01 — Normal, plasma and Dawson functions (11.1), pp. 275–276.

Existing TauCeti `TauCeti.Probability.cdf_gaussianReal_zero_one` and
`TauCeti.Probability.hasDerivAt_cdf_gaussianReal` give the normal CDF and density. Rewrite
`1+erf(x/√2)=erfc(-x/√2)` with the existing error-function parity/complement API and
`DLMF.Confluent.erf_ofReal`. Existing `DLMF.Confluent.faddeevaW`,
`DLMF.Confluent.faddeevaW_cauchy_integral`, `DLMF.Confluent.faddeevaW_entire`,
`DLMF.Confluent.faddeevaW_negative`, `DLMF.Confluent.hasDerivAt_faddeevaW` cover the plasma
function, integral domain Im z>0, continuation, reflection and ODE. Existing
`DLMF.Confluent.dawsonF`, `DLMF.Confluent.dawsonF_negative`, `DLMF.Confluent.dawsonF_entire`,
`DLMF.Confluent.hasDerivAt_dawsonF_complex`, `DLMF.Confluent.dawsonF_faddeeva` cover every Dawson
subclaim, including the oriented segment primitive and the exact decomposition.

Checked named coverage: 13 declarations; 0 depend on admissions.

## TEM-11-02 — Incomplete gamma definitions and entire regularization (11.2)–(11.5), pp. 277–278.

Existing `DLMF.Confluent.lowerIncompleteGamma_segment_integral`,
`DLMF.Confluent.upperIncompleteGamma_parameter_entire`, `DLMF.Confluent.regularizedGamma_eq`,
`DLMF.Confluent.regularizedIncompleteGammaQ_eq`, and
`DLMF.Confluent.regularizedGamma_add_regularizedIncompleteGammaQ'` cover both incomplete functions
and P+Q=1 with their actual complex branches. Existing `DLMF.Statistical.tricomiIncompleteGamma`,
`DLMF.Confluent.tricomiIncompleteGamma_hasSum_exponential`,
`DLMF.Confluent.tricomiIncompleteGamma_joint_entire`,
`DLMF.Statistical.tricomiIncompleteGamma_neg_nat` give the entire two-variable gamma-star
function, its exponential series and every exceptional negative-integer value. Existing
`DLMF.Confluent.lowerIncompleteGamma_parameter_residue` records the lower function's meromorphic
poles; it is not treated as jointly entire.

Checked named coverage: 10 declarations; 0 depend on admissions.

## TEM-11-03 — Values, recurrences and probability interpretation (11.6)–(11.8), pp. 278–279.

Existing `DLMF.Confluent.regularizedIncompleteGammaQ_nat_succ_expPartialSum`,
`DLMF.Confluent.regularizedGamma_nat_succ_expPartialSum`,
`DLMF.Confluent.upperIncompleteGamma_add_one`, `DLMF.Statistical.lowerIncompleteGamma_add_one`,
`DLMF.Confluent.regularizedGamma_add_one`, `DLMF.Confluent.regularizedIncompleteGammaQ_add_one`
give the finite values and all shape recurrences. `DLMF.Confluent.regularizedGamma_ofReal` and
`DLMF.Confluent.regularizedIncompleteGammaQ_ofReal` bridge to TauCeti; its
`TauCeti.regularizedGamma_pos`, `TauCeti.regularizedGamma_lt_one` then give both strict bounds.
The gamma density and chi-square interpretation are existing
`TauCeti.Probability.cdf_gammaMeasure_eq`, `TauCeti.Probability.cdf_chiSquaredMeasure_eq`, with
the density in their underlying Gamma measure API. Integer-shape finite tails identify the Poisson
probabilities by the finite mass sum, not by a new measure definition.

Checked named coverage: 12 declarations; 0 depend on admissions.

## TEM-11-04 — Series and large-argument remainder (11.9)–(11.12), pp. 279–280.

Existing `DLMF.Statistical.lowerIncompleteGamma_eq_tsum` and
`DLMF.Confluent.tricomiIncompleteGamma_hasSum_exponential` give both convergent lower-gamma series
after multiplication by the explicit power and Gamma factor. Existing
`DLMF.Confluent.IncompleteGammaRealIntegrals.upperIncompleteGamma_expansion` is the exact finite
integration-by-parts identity for every N≥0. Newly acquired
`DLMF.Confluent.norm_upperIncompleteGamma_le_of_lt_argument` and
`DLMF.Confluent.norm_upperIncompleteGamma_remainder_le` in ParameterRemainderBounds cover
precisely z>max(0,a-N), including cases outside the older a-1≤N bound. Existing
`DLMF.Confluent.upperIncompleteGamma_log_asymptotic` is the full logarithmic-cover sector
expansion |arg z|≤3π/2-δ; restricting to the principal cut would lose part of this domain.

Checked named coverage: 6 declarations; 2 depend on admissions.

## TEM-11-05 — Legendre continued fraction (11.18)–(11.19), pp. 281–282.

Existing `DLMF.Statistical.gammaIncCFNum`, `DLMF.Statistical.gammaIncCFDen`,
`DLMF.Statistical.gammaIncContFract` in Statistical/ContinuedFraction supply the alternating
numerator and denominator convention on positive reals. Existing
`DLMF.Confluent.upperIncompleteGamma_continuedFraction_complex` in BoundsFractions covers the full
principal cut and every complex shape, with the project continuant-based
`DLMF.Core.HasContinuedFraction` interpretation. Rescaling alternate continuants converts its
normalized denominators to z,1,z,1 without changing B/A; terminating numerators freeze the finite
continuant. Intermediate zero denominators are not treated as infinite-tail values.

Checked named coverage: 5 declarations; 1 depend on admissions.

## TEM-11-06 — Gamma inversion contours (11.20), pp. 282–283.

New `DLMF.Confluent.gammaInversionKernel`, its proved defining equation,
`DLMF.Confluent.integrable_gammaInversionKernel`,
`DLMF.Confluent.regularizedGamma_eq_vertical_integral`, and
`DLMF.Confluent.regularizedIncompleteGammaQ_eq_vertical_integral` in GammaInversion. The upward
vertical tangent is included by cancellation of i against 2πi; the branch is principal on Re s>-1.
Both lines are absolutely integrable for a>0, so their integrals also equal the source's symmetric
truncation limits. Their opposite signs and the existing complementary relation retain the
residue-one contour shift.

Checked named coverage: 4 declarations; 3 depend on admissions.

## TEM-11-07 — Uniform gamma transition (11.21)–(11.24), pp. 283–286, Exercise 11.4.

New `DLMF.Confluent.Real.gammaTransitionEta` and `DLMF.Confluent.Real.gammaTransitionInverse` have
explicit signed-coordinate and inverse-choice definitions with proved defining APIs.
`DLMF.Confluent.Real.gammaTransitionEta_strictMonoOn_bijOn`,
`DLMF.Confluent.Real.gammaTransitionInverse_spec`, `DLMF.Confluent.gammaUniformEtaOnLog_ofReal`,
`DLMF.Confluent.Real.analyticAt_gammaTransitionInverse_zero`,
`DLMF.Confluent.Real.gammaTransitionInverse_zero_hasDerivAt` give the increasing onto map, actual
positive inverse, complex-branch bridge and central analytic normalization. Existing
`DLMF.Confluent.gammaUniformC`, `DLMF.Confluent.gammaUniformC_first`,
`DLMF.Confluent.gammaUniformS_uniform_expansion` give C0 and the entire uniform expansion. Its
logarithmic complex filter already includes every real eta, with unbounded positive lambda. New
`DLMF.Confluent.gammaUniformC_real_coordinate_succ` explicitly translates the full recursion to
eta, with reciprocal-Gamma Stirling coefficient (-1)^n gammaStirlingCoeff n.
`DLMF.Confluent.analyticAt_gammaUniformC_real_coordinate_zero` retains all removable coefficient
singularities. P is exactly 1-Q by the existing complementary theorem.

Checked named coverage: 12 declarations; 8 depend on admissions.

## TEM-11-08 — Stable gamma scaling, (11.26)–(11.28), pp. 286–288.

New exact `DLMF.Confluent.gamma_density_scaled_identity` in ParameterRemainderBounds states the
complete stable scaling, with the existing canonical `DLMF.Confluent.gammaScaled` and μ=(x-a)/a.
The power series of log(1+μ)-μ follows by removing the linear term from Mathlib
`Real.hasSum_pow_div_log_of_abs_lt_one` at -μ. Its nonpositivity is the existing
`Real.log_le_sub_one_of_pos` at 1+μ. Positivity of a,x gives μ>-1 algebraically. No numerical
error estimate is asserted.

Checked named coverage: 4 declarations; 1 depend on admissions.

## TEM-11-09 — Incomplete beta definitions, symmetry and series (11.29)–(11.34), pp. 288–289.

Existing `DLMF.Statistical.Real.incompleteBeta`,
`DLMF.Statistical.Real.regularizedIncompleteBeta`, their zero/one and symmetry APIs,
`DLMF.Statistical.Real.regularizedIncompleteBeta_ofReal`, and
`DLMF.Statistical.regularizedIncompleteBeta_ofReal` give the interval definition and bridge to
TauCeti's increasing beta CDF. Existing
`DLMF.Statistical.Real.incompleteBeta_eq_ordinaryHypergeometric`,
`DLMF.Statistical.incompleteBeta_hypergeometric_euler`,
`DLMF.Statistical.incompleteBeta_hypergeometric_pfaff` give all three displayed hypergeometric
forms, divided by the same nonzero beta normalization. The disk restriction belongs to the literal
Pfaff-transformed infinite series, not its continued function; x<1/2 is exactly |x/(x-1)|<1 on
0<x<1.

Checked named coverage: 7 declarations; 0 depend on admissions.

## TEM-11-10 — Beta recurrences (11.36)–(11.41), pp. 289–290.

Existing `DLMF.Statistical.Real.regularizedIncompleteBeta_add_one_left`,
`DLMF.Statistical.Real.regularizedIncompleteBeta_add_one_right`,
`DLMF.Statistical.regularizedIncompleteBeta_neighbors`,
`DLMF.Statistical.regularizedIncompleteBeta_neighbors_down`, and
`DLMF.Statistical.regularizedIncompleteBeta_contiguous_12` through the related real contiguous
family cover the two shifts, weighted neighbor identity, downward relation and the eliminated
second-order recurrence. Applying symmetry swaps p,q and x,1-x for the complementary recurrence.
Downward shifts are used under p,q>1 as in the synopsis.

Checked named coverage: 5 declarations; 0 depend on admissions.

## TEM-11-11 — Beta continued fraction (11.35), p. 289.

Existing `DLMF.Statistical.incompleteBeta_continuedFraction` in BetaContinuedFraction and the
coefficient definitions in FractionTools provide the exact continued fraction with continuant
limits. The ordinary positive p,q and 0<x<1 source domain is included; the endpoint x=0 is
additionally valid. The alternative tail follows from the existing beta symmetry. This is a
convergence result for actual continuants, not an equality to a nested totalized expression.

Checked named coverage: 1 declarations; 0 depend on admissions.

## TEM-11-12 — Beta contour (11.42), pp. 290–291.

Existing `DLMF.Statistical.regularizedIncompleteBeta_mellinBarnes` and
`DLMF.Confluent.IncompleteBetaBarnes.integral_vertical` state both the exact upward contour and
absolute integrability for 0<x<c<1 and p,q>0. Principal powers are positive on (0,1); the i from
dt is already included in the real vertical parametrization. The complementary relation comes from
the existing beta symmetry, equivalently the residue at the crossed pole.

Checked named coverage: 2 declarations; 0 depend on admissions.

## TEM-11-13 — Beta limit with fixed second parameter (11.43)–(11.44), pp. 291–292.

Existing `DLMF.Statistical.Real.betaXi`, `DLMF.Statistical.Real.betaGeneratingKernel`,
`DLMF.Statistical.Real.betaGeneratingCoeff`, `DLMF.Statistical.betaAuxF`,
`DLMF.Statistical.betaAuxF_initial`, `DLMF.Statistical.betaAuxF_recurrence` give f, its actual
Taylor coefficients, F0,F1 and the complete moment recurrence. Existing
`DLMF.Confluent.IncompleteBetaUniform.normalizedIncompleteBeta_eq_laplace_integral` gives the
exact transformed integral. Existing
`DLMF.Confluent.IncompleteBetaUniform.exists_norm_iteratedDeriv_betaGeneratingKernel_le` proves
the finiteness needed for every positive-order M_N. New
`DLMF.Statistical.norm_betaAuxF_le_pochhammer` retains the exact (q)_N p^(-q-N) bound. New
`DLMF.Statistical.betaEndpointApproximation`, its proved defining/zero API,
`DLMF.Statistical.norm_regularizedIncompleteBeta_sub_endpointApproximation_le`, and
`DLMF.Statistical.exists_betaEndpointApproximation_uniform_remainder` state the precise
derivative-based error and full closed-interval absolute O(p^-N), with the actual limiting value
at x=0.

Checked named coverage: 12 declarations; 3 depend on admissions.

## TEM-11-14 — Symmetric large-parameter beta transition (11.45)–(11.46), pp. 292–294.

Existing `DLMF.Statistical.Real.betaCenter`, `DLMF.Statistical.Real.betaEta`,
`DLMF.Statistical.betaSymmetricC`, `DLMF.Statistical.betaSymmetricC_first`,
`DLMF.Statistical.betaSymmetricC_at_zero`, `DLMF.Statistical.betaSymmetricC_analytic`,
`DLMF.Statistical.incompleteBeta_symmetric_uniform_expansion` provide the transition and full
uniform remainder for s in [δ,1-δ]. New `DLMF.Statistical.betaSymmetricPhase`,
`DLMF.Statistical.betaSymmetricSaddleInverse`, `DLMF.Statistical.betaSymmetricSaddleAmplitude`,
`DLMF.Statistical.betaSymmetricSaddleCoefficient` are the actual normalized inverse germ,
pole-subtracted amplitude and Taylor algorithm. Their defining equations are proved.
`DLMF.Statistical.betaSymmetricSaddleInverse_spec`,
`DLMF.Statistical.analyticAt_betaSymmetricSaddleAmplitude`,
`DLMF.Statistical.betaSymmetricSaddleCoefficient_eq` connect this algorithm, including the
removable transition, to the canonical asymptotic coefficients. The explicit (-1)^n bridge retains
the canonical DLMF coefficient convention; no uniformity at s=0 or1 is claimed.

Checked named coverage: 14 declarations; 7 depend on admissions.

## TEM-11-15 — General beta-to-gamma saddle reduction (11.47)–(11.58), pp. 295–297.

New BetaGammaSaddle contains the full contour construction and algorithm.
`DLMF.Statistical.Real.betaGammaPhaseConstant`, `DLMF.Statistical.betaGammaBetaPhase`,
`DLMF.Statistical.betaGammaGammaPhase`, `DLMF.Statistical.betaGammaLocalInverse`,
`DLMF.Statistical.betaGammaHankelPoint`, `DLMF.Statistical.IsBetaGammaContinuation`,
`DLMF.Statistical.betaGammaContinuation` fix the principal phases, decreasing saddle branch,
explicit upward Hankel deformation and its normalized analytic continuation. Every definition has
a proved defining/API lemma. `DLMF.Statistical.betaGammaLocalInverse_spec`,
`DLMF.Statistical.exists_isBetaGammaContinuation`, `DLMF.Statistical.betaGammaContinuation_spec`,
`DLMF.Statistical.betaGammaContinuation_ofReal`,
`DLMF.Statistical.Real.betaZeta_strictAntiOn_bijOn`,
`DLMF.Statistical.Real.hasDerivAt_betaZeta_saddle`, `DLMF.Statistical.Real.hasDerivAt_betaZeta`
give the actual real coordinate map and full derivatives. `DLMF.Statistical.betaGammaAmplitude`
fills the apparent pole by its punctured limit, and `DLMF.Statistical.betaGammaContourCoefficient`
is h^(n)(μ)/n!, not a placeholder. `DLMF.Statistical.betaGammaMomentCoefficient` is the explicit
falling-factorial sum; `DLMF.Statistical.betaGammaMomentCoefficient_initial`,
`DLMF.Statistical.betaGammaMomentCoefficient_recurrence`,
`DLMF.Statistical.betaGammaMomentCoefficient_two` give the complete recursion and corrected Φ2=-q.
`DLMF.Statistical.integral_betaGammaContour_monomial` evaluates each moment exactly.
`DLMF.Statistical.integrableOn_betaGammaContour_taylor_remainder`,
`DLMF.Statistical.regularizedIncompleteBeta_eq_gamma_sub_finite_contour`,
`DLMF.Statistical.norm_regularizedIncompleteBeta_sub_gamma_sum_le_contour` retain the exact finite
remainder and its absolute contour-norm bound for every positive p,q. No claim that p^-n alone is
an asymptotic scale for variable q is inserted.

Checked named coverage: 24 declarations; 12 depend on admissions.

## TEM-11-16 — Noncentral gamma / Marcum definitions (11.61)–(11.63), pp. 298–299.

Existing `DLMF.Statistical.marcumP`, `DLMF.Statistical.marcumQ`,
`DLMF.Statistical.summable_marcumP_term`, `DLMF.Statistical.summable_marcumQ_term`,
`DLMF.Statistical.marcumP_add_marcumQ`, `DLMF.Statistical.marcumP_nonneg`,
`DLMF.Statistical.marcumP_le_one`, `DLMF.Statistical.marcumP_zero_left`,
`DLMF.Statistical.marcumQ_eq_integral` cover the Poisson mixtures and upper Bessel integral. New
proved `DLMF.Statistical.marcumQ_nonneg`, `DLMF.Statistical.marcumQ_le_one`,
`DLMF.Statistical.marcumQ_zero_left` complete the real probability API without changing
definitions. New `DLMF.Statistical.integrableOn_marcumBesselDensity` and
`DLMF.Statistical.marcumP_eq_integral` provide absolute integrability and the lower integral. New
`DLMF.Statistical.Real.cdf_noncentralChiSquaredMeasure_eq_marcumP` is the direct bridge from
TauCeti's existing distribution and CDF; it keeps ν>0 and nonnegative noncentrality.

Checked named coverage: 15 declarations; 2 depend on admissions.

## TEM-11-17 — Marcum recurrences and contours (11.64)–(11.69), pp. 299–301.

Existing proved `DLMF.Statistical.marcumQ_add_one` and `DLMF.Statistical.marcumQ_recurrence` have
exactly the source parameter ranges and normalizations. New
`DLMF.Statistical.marcumVerticalKernel`, its defining identity,
`DLMF.Statistical.integrable_marcumVerticalKernel`,
`DLMF.Statistical.marcumQ_eq_vertical_integral`, `DLMF.Statistical.marcumP_eq_vertical_integral`
cover both upward inversion contours. The complex powers are principal and positive on the
positive axis; the crossed pole and the negative lower-tail sign are retained.

Checked named coverage: 6 declarations; 3 depend on admissions.

## TEM-11-18 — Fixed-order Marcum transition (11.66)–(11.80), pp. 300–303.

New MarcumFixedOrder gives explicit `DLMF.Statistical.Real.marcumXi`,
`DLMF.Statistical.Real.marcumRho`, `DLMF.Statistical.Real.marcumSigma`,
`DLMF.Statistical.marcumBesselTail`, `DLMF.Statistical.Real.marcumTransitionMoment`,
`DLMF.Statistical.marcumBesselCoefficient`, with proved defining equations. The coefficient is
(-1)^n times the canonical Hankel coefficient, preserving its existing normalization.
`DLMF.Statistical.integrableOn_marcumBesselTail_kernel`,
`DLMF.Statistical.not_integrableOn_marcumBesselTail_kernel_zero`,
`DLMF.Statistical.marcumQ_eq_besselTail`, `DLMF.Statistical.marcumP_eq_besselTail`,
`DLMF.Statistical.tendsto_marcumQ_besselTail_diagonal`,
`DLMF.Statistical.tendsto_marcumP_besselTail_diagonal` distinguish the divergent individual
zero-damping integrals from the finite combinations.
`DLMF.Statistical.marcumBesselCoefficient_zero`, `DLMF.Statistical.marcumBesselCoefficient_succ`,
`DLMF.Statistical.Real.marcumTransitionMoment_eq_upperIncompleteGamma`,
`DLMF.Statistical.Real.marcumTransitionMoment_succ`,
`DLMF.Statistical.Real.marcumTransitionMoment_zero` give the full coefficient/moment algorithm.
`DLMF.Statistical.norm_marcumBesselTail_sub_sum_le`,
`DLMF.Statistical.exists_marcumBesselTail_uniform_remainder` give the pointwise-bound transport
and uniform-in-positive-damping complete expansion.
`DLMF.Statistical.marcumQ_besselTail_leading_term` identifies its displayed Gaussian leading term
exactly.

Checked named coverage: 20 declarations; 13 depend on admissions.

## TEM-11-19 — Variable-order Marcum transition (11.81)–(11.83), pp. 303–305.

New MarcumVariableOrder defines the actual principal `DLMF.Statistical.marcumSaddlePhase`,
normalized `DLMF.Statistical.marcumSaddleInverse`, signed
`DLMF.Statistical.Real.marcumPoleCoordinate`, pole-subtracted
`DLMF.Statistical.marcumSaddleAmplitude`, derivative-based
`DLMF.Statistical.marcumSaddleCoefficient`, and genuine endpoint
`DLMF.Statistical.Real.marcumQZeroOrder`, each with a proved defining lemma.
`DLMF.Statistical.marcumSaddleInverse_spec`, `DLMF.Statistical.Real.marcumPoleCoordinate_sq`,
`DLMF.Statistical.analyticAt_marcumSaddleAmplitude`,
`DLMF.Statistical.im_marcumSaddleCoefficient_even`,
`DLMF.Statistical.Real.tendsto_marcumQ_zero_order`,
`DLMF.Statistical.Real.marcumPoleCoordinate_eq_zero_iff` give every normalization and
removable/endpoint claim, including y=x+μ.
`DLMF.Statistical.exists_marcumQ_variable_order_uniform_remainder` states the entire N-term
estimate uniformly in μ≥0 and |logρ|≤B with explicit constants and Gaussian factor. The zero-order
value uses the one-sided limit rather than evaluating a totalized central shape-zero mixture.

Checked named coverage: 13 declarations; 7 depend on admissions.

## TEM-11-20 — Von Mises distribution and convergent expansion (11.85)–(11.89), pp. 308–309.

Shared with root's acquisition: `DLMF.Statistical.Real.vonMisesCDF` and its defining API in
Basic/VonMises, `DLMF.Statistical.Real.vonMisesCDF_neg`,
`DLMF.Statistical.Real.hasSum_vonMisesCDF_fourier`,
`DLMF.Statistical.Real.vonMisesGaussianMoment`,
`DLMF.Statistical.Real.hasSum_vonMisesGaussianMoment`,
`DLMF.Statistical.Real.vonMisesGaussianMoment_eq_lowerIncompleteGamma`,
`DLMF.Statistical.Real.vonMisesCDF_gaussian_uniform`, and
`DLMF.Statistical.Real.vonMisesCDF_erfc_uniform` in VonMises cover the full convergent
Fourier/Gaussian expansions, endpoints, oriented signs, finite-order uniform bound and Gaussian
leading limit. These files are owned by root and were not edited by the chapter11 audit.

Checked named coverage: 8 declarations; 6 depend on admissions.

## TEM-11-21 — Error-function and gamma monodromy, Exercises 11.1–11.3, pp. 310–311.

New `DLMF.Confluent.Real.integrableOn_erfc_gammaTail_kernel` and
`DLMF.Confluent.erfc_eq_gammaTail_integral` in ErrorFunctions/Integrals/GammaTail give the exact
shifted-gamma Laplace formula and its absolute convergence. Existing
`DLMF.Confluent.erfc_sector_asymptotic`, `DLMF.Confluent.erfc_remainder_bound`,
`DLMF.Confluent.erfc_remainder_sign` give the complete sector expansion and the positive-real
first-omitted-term sign/bound. Existing `DLMF.Confluent.upperIncompleteGammaOnLog_monodromy`,
`DLMF.Confluent.upperIncompleteGammaOnLog_monodromy_limit` retain the logarithmic covering,
whole-expression parameter limit at the nonpositive integers, and all other integral parameters
directly.

Checked named coverage: 7 declarations; 2 depend on admissions.

## Validation

All 21 entries are mapped. The transitive `#print axioms` audit checked **250** distinct
declarations; **79** depend on admissions. The **13** new modules
owned by this supplement contain **147** public declarations, including
**64** directly admitted targets. Definitions and their
defining equations have no admissions. Every new module has passed a direct strict Lean check
with `autoImplicit=false` and `relaxedAutoImplicit=false`; modules are registered in their
area umbrellas. Repository-wide build and import integration are coordinated with the other
book acquisitions and reported separately.

The per-entry declaration locations and proof statuses are retained in
[reports/BookAcquisition-Temme-Chapter11.tsv](reports/BookAcquisition-Temme-Chapter11.tsv). No additional
source erratum or user approval question was identified in this supplement.

## Related Chapter 13 acquisition

TEM-13-06, beta half: `DLMF.Statistical.Real.regularizedIncompleteBeta_add_nat_isEquivalent`,
`DLMF.Statistical.Real.tendsto_regularizedIncompleteBeta_add_nat_ratio`, and
`DLMF.Statistical.Real.tendsto_regularizedIncompleteBeta_add_nat_zero` state the full equivalent,
ratio limit and minimality against the constant solution. These admitted targets are included
in this supplement's declaration index; the repeated-erfc half belongs to the shared root audit.

## Checked declaration index

- [Complex.IsAnalyticSaddleMap](DLMFMathlib/Analysis/Analytic/QuadraticInverse.lean#L30) — definition, no admission.
- [Complex.IsAnalyticSaddleMap.eventuallyEq](DLMFMathlib/Analysis/Analytic/QuadraticInverse.lean#L79) — direct admission.
- [Complex.analyticSaddleMap](DLMFMathlib/Analysis/Analytic/QuadraticInverse.lean#L59) — definition, no admission.
- [Complex.analyticSaddleMap_def](DLMFMathlib/Analysis/Analytic/QuadraticInverse.lean#L63) — proved, no admission.
- [Complex.analyticSaddleMap_spec](DLMFMathlib/Analysis/Analytic/QuadraticInverse.lean#L69) — depends on admission.
- [Complex.exists_isAnalyticSaddleMap](DLMFMathlib/Analysis/Analytic/QuadraticInverse.lean#L49) — direct admission.
- [Complex.isAnalyticSaddleMap_iff](DLMFMathlib/Analysis/Analytic/QuadraticInverse.lean#L37) — proved, no admission.
- [Complex.quadraticInverse](DLMFMathlib/Analysis/Analytic/QuadraticInverse.lean#L88) — definition, no admission.
- [Complex.quadraticInverse_def](DLMFMathlib/Analysis/Analytic/QuadraticInverse.lean#L92) — proved, no admission.
- [DLMF.Confluent.IncompleteBetaBarnes.integral_vertical](DLMF/IncompleteGamma/BetaBarnes.lean#L169) — proved, no admission.
- [DLMF.Confluent.IncompleteBetaUniform.exists_norm_iteratedDeriv_betaGeneratingKernel_le](DLMF/IncompleteGamma/BetaEndpointBounds.lean#L282) — proved, no admission.
- [DLMF.Confluent.IncompleteBetaUniform.normalizedIncompleteBeta_eq_laplace_integral](DLMF/IncompleteGamma/BetaEndpointBounds.lean#L348) — proved, no admission.
- [DLMF.Confluent.IncompleteGammaRealIntegrals.upperIncompleteGamma_expansion](DLMF/IncompleteGamma/RealIntegrals.lean#L220) — proved, no admission.
- [DLMF.Confluent.Real.analyticAt_gammaTransitionInverse_zero](DLMF/IncompleteGamma/GammaTransitionCoordinates.lean#L70) — direct admission.
- [DLMF.Confluent.Real.gammaTransitionEta](DLMF/IncompleteGamma/GammaTransitionCoordinates.lean#L28) — definition, no admission.
- [DLMF.Confluent.Real.gammaTransitionEta_def](DLMF/IncompleteGamma/GammaTransitionCoordinates.lean#L37) — proved, no admission.
- [DLMF.Confluent.Real.gammaTransitionEta_strictMonoOn_bijOn](DLMF/IncompleteGamma/GammaTransitionCoordinates.lean#L49) — direct admission.
- [DLMF.Confluent.Real.gammaTransitionInverse](DLMF/IncompleteGamma/GammaTransitionCoordinates.lean#L33) — definition, no admission.
- [DLMF.Confluent.Real.gammaTransitionInverse_def](DLMF/IncompleteGamma/GammaTransitionCoordinates.lean#L43) — proved, no admission.
- [DLMF.Confluent.Real.gammaTransitionInverse_spec](DLMF/IncompleteGamma/GammaTransitionCoordinates.lean#L56) — depends on admission.
- [DLMF.Confluent.Real.gammaTransitionInverse_zero_hasDerivAt](DLMF/IncompleteGamma/GammaTransitionCoordinates.lean#L76) — direct admission.
- [DLMF.Confluent.Real.integrableOn_erfc_gammaTail_kernel](DLMF/ErrorFunctions/Integrals/GammaTail.lean#L29) — direct admission.
- [DLMF.Confluent.analyticAt_gammaUniformC_real_coordinate_zero](DLMF/IncompleteGamma/GammaTransitionCoordinates.lean#L92) — direct admission.
- [DLMF.Confluent.dawsonF](DLMF/ErrorFunctions/Basic/Functions.lean#L56) — definition, no admission.
- [DLMF.Confluent.dawsonF_entire](DLMF/ErrorFunctions/Basic/Properties.lean#L169) — proved, no admission.
- [DLMF.Confluent.dawsonF_faddeeva](DLMF/ErrorFunctions/Relations.lean#L171) — proved, no admission.
- [DLMF.Confluent.dawsonF_negative](DLMF/ErrorFunctions/Relations.lean#L77) — proved, no admission.
- [DLMF.Confluent.erf_ofReal](DLMF/ErrorFunctions/Basic/Properties.lean#L66) — proved, no admission.
- [DLMF.Confluent.erfc_eq_gammaTail_integral](DLMF/ErrorFunctions/Integrals/GammaTail.lean#L36) — direct admission.
- [DLMF.Confluent.erfc_remainder_bound](DLMF/ErrorFunctions/BoundsAsymptotics/GaussianRemainders.lean#L588) — proved, no admission.
- [DLMF.Confluent.erfc_remainder_sign](DLMF/ErrorFunctions/BoundsAsymptotics/GaussianRemainders.lean#L813) — proved, no admission.
- [DLMF.Confluent.erfc_sector_asymptotic](DLMF/ErrorFunctions/BoundsAsymptotics/GaussianRemainders.lean#L371) — proved, no admission.
- [DLMF.Confluent.faddeevaW](DLMF/ErrorFunctions/Basic/Functions.lean#L51) — definition, no admission.
- [DLMF.Confluent.faddeevaW_cauchy_integral](DLMF/ErrorFunctions/Integrals/GaussianAndCauchy.lean#L461) — proved, no admission.
- [DLMF.Confluent.faddeevaW_entire](DLMF/ErrorFunctions/Basic/Properties.lean#L163) — proved, no admission.
- [DLMF.Confluent.faddeevaW_negative](DLMF/ErrorFunctions/Relations.lean#L70) — proved, no admission.
- [DLMF.Confluent.gammaInversionKernel](DLMF/IncompleteGamma/GammaInversion.lean#L27) — definition, no admission.
- [DLMF.Confluent.gammaInversionKernel_def](DLMF/IncompleteGamma/GammaInversion.lean#L32) — proved, no admission.
- [DLMF.Confluent.gammaScaled](DLMF/IncompleteGamma/UniformAsymptotics.lean#L81) — definition, no admission.
- [DLMF.Confluent.gammaUniformC](DLMF/IncompleteGamma/UniformAsymptotics.lean#L498) — definition, no admission.
- [DLMF.Confluent.gammaUniformC_first](DLMF/IncompleteGamma/UniformAsymptotics.lean#L636) — proved, no admission.
- [DLMF.Confluent.gammaUniformC_real_coordinate_succ](DLMF/IncompleteGamma/GammaTransitionCoordinates.lean#L82) — direct admission.
- [DLMF.Confluent.gammaUniformEtaOnLog_ofReal](DLMF/IncompleteGamma/GammaTransitionCoordinates.lean#L64) — direct admission.
- [DLMF.Confluent.gammaUniformS_uniform_expansion](DLMF/IncompleteGamma/UniformAsymptotics.lean#L715) — direct admission.
- [DLMF.Confluent.gamma_density_scaled_identity](DLMF/IncompleteGamma/ParameterRemainderBounds.lean#L46) — direct admission.
- [DLMF.Confluent.hasDerivAt_dawsonF_complex](DLMF/ErrorFunctions/Basic/Properties.lean#L153) — proved, no admission.
- [DLMF.Confluent.hasDerivAt_faddeevaW](DLMF/ErrorFunctions/Relations.lean#L411) — proved, no admission.
- [DLMF.Confluent.integrable_gammaInversionKernel](DLMF/IncompleteGamma/GammaInversion.lean#L38) — direct admission.
- [DLMF.Confluent.lowerIncompleteGamma_parameter_residue](DLMF/IncompleteGamma/ContinuedProperties.lean#L317) — proved, no admission.
- [DLMF.Confluent.lowerIncompleteGamma_segment_integral](DLMF/IncompleteGamma/ContinuedProperties.lean#L127) — proved, no admission.
- [DLMF.Confluent.norm_upperIncompleteGamma_le_of_lt_argument](DLMF/IncompleteGamma/ParameterRemainderBounds.lean#L28) — direct admission.
- [DLMF.Confluent.norm_upperIncompleteGamma_remainder_le](DLMF/IncompleteGamma/ParameterRemainderBounds.lean#L35) — direct admission.
- [DLMF.Confluent.regularizedGamma_add_one](DLMF/IncompleteGamma/Regularized.lean#L124) — proved, no admission.
- [DLMF.Confluent.regularizedGamma_add_regularizedIncompleteGammaQ'](DLMF/IncompleteGamma/Regularized.lean#L60) — proved, no admission.
- [DLMF.Confluent.regularizedGamma_eq](DLMF/IncompleteGamma/Regularized.lean#L49) — proved, no admission.
- [DLMF.Confluent.regularizedGamma_eq_vertical_integral](DLMF/IncompleteGamma/GammaInversion.lean#L45) — direct admission.
- [DLMF.Confluent.regularizedGamma_nat_succ_expPartialSum](DLMF/IncompleteGamma/SpecialValues.lean#L129) — proved, no admission.
- [DLMF.Confluent.regularizedGamma_ofReal](DLMF/IncompleteGamma/Regularized.lean#L158) — proved, no admission.
- [DLMF.Confluent.regularizedIncompleteGammaQ_add_one](DLMF/IncompleteGamma/Regularized.lean#L112) — proved, no admission.
- [DLMF.Confluent.regularizedIncompleteGammaQ_eq](DLMF/IncompleteGamma/Regularized.lean#L91) — proved, no admission.
- [DLMF.Confluent.regularizedIncompleteGammaQ_eq_vertical_integral](DLMF/IncompleteGamma/GammaInversion.lean#L53) — direct admission.
- [DLMF.Confluent.regularizedIncompleteGammaQ_nat_succ_expPartialSum](DLMF/IncompleteGamma/SpecialValues.lean#L137) — proved, no admission.
- [DLMF.Confluent.regularizedIncompleteGammaQ_ofReal](DLMF/IncompleteGamma/Regularized.lean#L168) — proved, no admission.
- [DLMF.Confluent.tricomiIncompleteGamma_hasSum_exponential](DLMF/IncompleteGamma/ContinuedProperties.lean#L51) — proved, no admission.
- [DLMF.Confluent.tricomiIncompleteGamma_joint_entire](DLMF/IncompleteGamma/ContinuedProperties.lean#L158) — proved, no admission.
- [DLMF.Confluent.upperIncompleteGammaOnLog_monodromy](DLMF/IncompleteGamma/ContinuedProperties.lean#L486) — proved, no admission.
- [DLMF.Confluent.upperIncompleteGammaOnLog_monodromy_limit](DLMF/IncompleteGamma/ContinuedProperties.lean#L500) — proved, no admission.
- [DLMF.Confluent.upperIncompleteGamma_add_one](DLMF/Confluent/IncompleteGamma.lean#L197) — proved, no admission.
- [DLMF.Confluent.upperIncompleteGamma_continuedFraction_complex](DLMF/IncompleteGamma/BoundsFractions.lean#L107) — direct admission.
- [DLMF.Confluent.upperIncompleteGamma_log_asymptotic](DLMF/IncompleteGamma/Asymptotics/LargeArgument.lean#L67) — proved, no admission.
- [DLMF.Confluent.upperIncompleteGamma_parameter_entire](DLMF/IncompleteGamma/ContinuedProperties.lean#L276) — proved, no admission.
- [DLMF.Core.HasContinuedFraction](DLMF/Core/Basic.lean#L206) — definition, no admission.
- [DLMF.Statistical.IsBetaGammaContinuation](DLMF/IncompleteGamma/BetaGammaSaddle.lean#L52) — definition, no admission.
- [DLMF.Statistical.Real.betaCenter](DLMF/IncompleteGamma/BetaAsymptotics.lean#L62) — definition, no admission.
- [DLMF.Statistical.Real.betaEta](DLMF/IncompleteGamma/BetaAsymptotics.lean#L67) — definition, no admission.
- [DLMF.Statistical.Real.betaGammaPhaseConstant](DLMF/IncompleteGamma/BetaGammaSaddle.lean#L29) — definition, no admission.
- [DLMF.Statistical.Real.betaGammaPhaseConstant_def](DLMF/IncompleteGamma/BetaGammaSaddle.lean#L98) — proved, no admission.
- [DLMF.Statistical.Real.betaGeneratingCoeff](DLMF/IncompleteGamma/BetaEndpointData.lean#L266) — definition, no admission.
- [DLMF.Statistical.Real.betaGeneratingKernel](DLMF/IncompleteGamma/BetaEndpointData.lean#L261) — definition, no admission.
- [DLMF.Statistical.Real.betaXi](DLMF/IncompleteGamma/BetaEndpointData.lean#L257) — definition, no admission.
- [DLMF.Statistical.Real.betaZeta_strictAntiOn_bijOn](DLMF/IncompleteGamma/BetaGammaSaddle.lean#L194) — direct admission.
- [DLMF.Statistical.Real.cdf_noncentralChiSquaredMeasure_eq_marcumP](DLMF/Statistical/MarcumProbability.lean#L52) — proved, no admission.
- [DLMF.Statistical.Real.hasDerivAt_betaZeta](DLMF/IncompleteGamma/BetaGammaSaddle.lean#L207) — direct admission.
- [DLMF.Statistical.Real.hasDerivAt_betaZeta_saddle](DLMF/IncompleteGamma/BetaGammaSaddle.lean#L201) — direct admission.
- [DLMF.Statistical.Real.hasSum_vonMisesCDF_fourier](DLMF/Statistical/VonMises.lean#L40) — direct admission.
- [DLMF.Statistical.Real.hasSum_vonMisesGaussianMoment](DLMF/Statistical/VonMises.lean#L48) — direct admission.
- [DLMF.Statistical.Real.incompleteBeta](DLMF/Statistical/Basic/IncompleteBeta.lean#L59) — definition, no admission.
- [DLMF.Statistical.Real.incompleteBeta_eq_ordinaryHypergeometric](DLMF/Statistical/IncompleteBeta.lean#L37) — proved, no admission.
- [DLMF.Statistical.Real.integrableOn_marcumTransitionMoment_kernel](DLMF/Statistical/MarcumFixedOrder.lean#L143) — direct admission.
- [DLMF.Statistical.Real.marcumPoleCoordinate](DLMF/Statistical/MarcumVariableOrder.lean#L41) — definition, no admission.
- [DLMF.Statistical.Real.marcumPoleCoordinate_def](DLMF/Statistical/MarcumVariableOrder.lean#L78) — proved, no admission.
- [DLMF.Statistical.Real.marcumPoleCoordinate_eq_zero_iff](DLMF/Statistical/MarcumVariableOrder.lean#L141) — direct admission.
- [DLMF.Statistical.Real.marcumPoleCoordinate_sq](DLMF/Statistical/MarcumVariableOrder.lean#L116) — direct admission.
- [DLMF.Statistical.Real.marcumQZeroOrder](DLMF/Statistical/MarcumVariableOrder.lean#L62) — definition, no admission.
- [DLMF.Statistical.Real.marcumQZeroOrder_def](DLMF/Statistical/MarcumVariableOrder.lean#L100) — proved, no admission.
- [DLMF.Statistical.Real.marcumRho](DLMF/Statistical/MarcumFixedOrder.lean#L32) — definition, no admission.
- [DLMF.Statistical.Real.marcumRho_def](DLMF/Statistical/MarcumFixedOrder.lean#L43) — proved, no admission.
- [DLMF.Statistical.Real.marcumSigma](DLMF/Statistical/MarcumFixedOrder.lean#L35) — definition, no admission.
- [DLMF.Statistical.Real.marcumSigma_def](DLMF/Statistical/MarcumFixedOrder.lean#L47) — proved, no admission.
- [DLMF.Statistical.Real.marcumTransitionMoment](DLMF/Statistical/MarcumFixedOrder.lean#L61) — definition, no admission.
- [DLMF.Statistical.Real.marcumTransitionMoment_def](DLMF/Statistical/MarcumFixedOrder.lean#L65) — proved, no admission.
- [DLMF.Statistical.Real.marcumTransitionMoment_eq_upperIncompleteGamma](DLMF/Statistical/MarcumFixedOrder.lean#L150) — direct admission.
- [DLMF.Statistical.Real.marcumTransitionMoment_succ](DLMF/Statistical/MarcumFixedOrder.lean#L158) — direct admission.
- [DLMF.Statistical.Real.marcumTransitionMoment_zero](DLMF/Statistical/MarcumFixedOrder.lean#L166) — direct admission.
- [DLMF.Statistical.Real.marcumXi](DLMF/Statistical/MarcumFixedOrder.lean#L29) — definition, no admission.
- [DLMF.Statistical.Real.marcumXi_def](DLMF/Statistical/MarcumFixedOrder.lean#L39) — proved, no admission.
- [DLMF.Statistical.Real.regularizedIncompleteBeta](DLMF/Statistical/Basic/IncompleteBeta.lean#L64) — definition, no admission.
- [DLMF.Statistical.Real.regularizedIncompleteBeta_add_nat_isEquivalent](DLMF/IncompleteGamma/BetaOrderMinimality.lean#L27) — direct admission.
- [DLMF.Statistical.Real.regularizedIncompleteBeta_add_one_left](DLMF/Statistical/Basic/IncompleteBeta.lean#L214) — proved, no admission.
- [DLMF.Statistical.Real.regularizedIncompleteBeta_add_one_right](DLMF/Statistical/Basic/IncompleteBeta.lean#L241) — proved, no admission.
- [DLMF.Statistical.Real.regularizedIncompleteBeta_ofReal](DLMF/Statistical/Basic/IncompleteBeta.lean#L277) — proved, no admission.
- [DLMF.Statistical.Real.tendsto_marcumQ_zero_order](DLMF/Statistical/MarcumVariableOrder.lean#L136) — direct admission.
- [DLMF.Statistical.Real.tendsto_regularizedIncompleteBeta_add_nat_ratio](DLMF/IncompleteGamma/BetaOrderMinimality.lean#L36) — direct admission.
- [DLMF.Statistical.Real.tendsto_regularizedIncompleteBeta_add_nat_zero](DLMF/IncompleteGamma/BetaOrderMinimality.lean#L44) — direct admission.
- [DLMF.Statistical.Real.vonMisesCDF](DLMF/Statistical/Basic/VonMises.lean#L25) — definition, no admission.
- [DLMF.Statistical.Real.vonMisesCDF_erfc_uniform](DLMF/Statistical/VonMises.lean#L77) — direct admission.
- [DLMF.Statistical.Real.vonMisesCDF_gaussian_uniform](DLMF/Statistical/VonMises.lean#L68) — direct admission.
- [DLMF.Statistical.Real.vonMisesCDF_neg](DLMF/Statistical/VonMises.lean#L35) — direct admission.
- [DLMF.Statistical.Real.vonMisesGaussianMoment](DLMF/Statistical/VonMises.lean#L26) — definition, no admission.
- [DLMF.Statistical.Real.vonMisesGaussianMoment_eq_lowerIncompleteGamma](DLMF/Statistical/VonMises.lean#L58) — direct admission.
- [DLMF.Statistical.analyticAt_betaGammaAmplitude](DLMF/IncompleteGamma/BetaGammaSaddle.lean#L216) — direct admission.
- [DLMF.Statistical.analyticAt_betaSymmetricSaddleAmplitude](DLMF/IncompleteGamma/BetaSymmetricSaddle.lean#L85) — direct admission.
- [DLMF.Statistical.analyticAt_marcumSaddleAmplitude](DLMF/Statistical/MarcumVariableOrder.lean#L124) — direct admission.
- [DLMF.Statistical.betaAuxF](DLMF/IncompleteGamma/BetaEndpointData.lean#L270) — definition, no admission.
- [DLMF.Statistical.betaAuxF_initial](DLMF/IncompleteGamma/BetaEndpointData.lean#L417) — proved, no admission.
- [DLMF.Statistical.betaAuxF_recurrence](DLMF/IncompleteGamma/BetaEndpointData.lean#L359) — proved, no admission.
- [DLMF.Statistical.betaEndpointApproximation](DLMF/IncompleteGamma/BetaEndpointError.lean#L27) — definition, no admission.
- [DLMF.Statistical.betaEndpointApproximation_def](DLMF/IncompleteGamma/BetaEndpointError.lean#L33) — proved, no admission.
- [DLMF.Statistical.betaEndpointApproximation_zero](DLMF/IncompleteGamma/BetaEndpointError.lean#L40) — proved, no admission.
- [DLMF.Statistical.betaGammaAmplitude](DLMF/IncompleteGamma/BetaGammaSaddle.lean#L69) — definition, no admission.
- [DLMF.Statistical.betaGammaAmplitude_def](DLMF/IncompleteGamma/BetaGammaSaddle.lean#L135) — proved, no admission.
- [DLMF.Statistical.betaGammaBetaPhase](DLMF/IncompleteGamma/BetaGammaSaddle.lean#L33) — definition, no admission.
- [DLMF.Statistical.betaGammaBetaPhase_def](DLMF/IncompleteGamma/BetaGammaSaddle.lean#L102) — proved, no admission.
- [DLMF.Statistical.betaGammaContinuation](DLMF/IncompleteGamma/BetaGammaSaddle.lean#L64) — definition, no admission.
- [DLMF.Statistical.betaGammaContinuation_def](DLMF/IncompleteGamma/BetaGammaSaddle.lean#L131) — proved, no admission.
- [DLMF.Statistical.betaGammaContinuation_ofReal](DLMF/IncompleteGamma/BetaGammaSaddle.lean#L188) — direct admission.
- [DLMF.Statistical.betaGammaContinuation_spec](DLMF/IncompleteGamma/BetaGammaSaddle.lean#L182) — depends on admission.
- [DLMF.Statistical.betaGammaContourCoefficient](DLMF/IncompleteGamma/BetaGammaSaddle.lean#L77) — definition, no admission.
- [DLMF.Statistical.betaGammaContourCoefficient_def](DLMF/IncompleteGamma/BetaGammaSaddle.lean#L143) — proved, no admission.
- [DLMF.Statistical.betaGammaContourKernel](DLMF/IncompleteGamma/BetaGammaSaddle.lean#L88) — definition, no admission.
- [DLMF.Statistical.betaGammaContourKernel_def](DLMF/IncompleteGamma/BetaGammaSaddle.lean#L154) — proved, no admission.
- [DLMF.Statistical.betaGammaContourPrefactor](DLMF/IncompleteGamma/BetaGammaSaddle.lean#L93) — definition, no admission.
- [DLMF.Statistical.betaGammaContourPrefactor_def](DLMF/IncompleteGamma/BetaGammaSaddle.lean#L161) — proved, no admission.
- [DLMF.Statistical.betaGammaGammaPhase](DLMF/IncompleteGamma/BetaGammaSaddle.lean#L36) — definition, no admission.
- [DLMF.Statistical.betaGammaGammaPhase_def](DLMF/IncompleteGamma/BetaGammaSaddle.lean#L106) — proved, no admission.
- [DLMF.Statistical.betaGammaHankelPoint](DLMF/IncompleteGamma/BetaGammaSaddle.lean#L46) — definition, no admission.
- [DLMF.Statistical.betaGammaHankelPoint_def](DLMF/IncompleteGamma/BetaGammaSaddle.lean#L116) — proved, no admission.
- [DLMF.Statistical.betaGammaLocalInverse](DLMF/IncompleteGamma/BetaGammaSaddle.lean#L40) — definition, no admission.
- [DLMF.Statistical.betaGammaLocalInverse_def](DLMF/IncompleteGamma/BetaGammaSaddle.lean#L110) — proved, no admission.
- [DLMF.Statistical.betaGammaLocalInverse_spec](DLMF/IncompleteGamma/BetaGammaSaddle.lean#L168) — direct admission.
- [DLMF.Statistical.betaGammaMomentCoefficient](DLMF/IncompleteGamma/BetaGammaSaddle.lean#L82) — definition, no admission.
- [DLMF.Statistical.betaGammaMomentCoefficient_def](DLMF/IncompleteGamma/BetaGammaSaddle.lean#L148) — proved, no admission.
- [DLMF.Statistical.betaGammaMomentCoefficient_initial](DLMF/IncompleteGamma/BetaGammaSaddle.lean#L222) — proved, no admission.
- [DLMF.Statistical.betaGammaMomentCoefficient_recurrence](DLMF/IncompleteGamma/BetaGammaSaddle.lean#L228) — direct admission.
- [DLMF.Statistical.betaGammaMomentCoefficient_two](DLMF/IncompleteGamma/BetaGammaSaddle.lean#L235) — proved, no admission.
- [DLMF.Statistical.betaSymmetricC](DLMF/IncompleteGamma/BetaAsymptotics.lean#L218) — definition, no admission.
- [DLMF.Statistical.betaSymmetricC_analytic](DLMF/IncompleteGamma/BetaAsymptotics.lean#L240) — direct admission.
- [DLMF.Statistical.betaSymmetricC_at_zero](DLMF/IncompleteGamma/BetaAsymptotics.lean#L235) — direct admission.
- [DLMF.Statistical.betaSymmetricC_first](DLMF/IncompleteGamma/BetaAsymptotics.lean#L228) — direct admission.
- [DLMF.Statistical.betaSymmetricPhase](DLMF/IncompleteGamma/BetaSymmetricSaddle.lean#L29) — definition, no admission.
- [DLMF.Statistical.betaSymmetricPhase_def](DLMF/IncompleteGamma/BetaSymmetricSaddle.lean#L52) — proved, no admission.
- [DLMF.Statistical.betaSymmetricSaddleAmplitude](DLMF/IncompleteGamma/BetaSymmetricSaddle.lean#L39) — definition, no admission.
- [DLMF.Statistical.betaSymmetricSaddleAmplitude_def](DLMF/IncompleteGamma/BetaSymmetricSaddle.lean#L62) — proved, no admission.
- [DLMF.Statistical.betaSymmetricSaddleCoefficient](DLMF/IncompleteGamma/BetaSymmetricSaddle.lean#L47) — definition, no admission.
- [DLMF.Statistical.betaSymmetricSaddleCoefficient_def](DLMF/IncompleteGamma/BetaSymmetricSaddle.lean#L70) — proved, no admission.
- [DLMF.Statistical.betaSymmetricSaddleCoefficient_eq](DLMF/IncompleteGamma/BetaSymmetricSaddle.lean#L93) — direct admission.
- [DLMF.Statistical.betaSymmetricSaddleInverse](DLMF/IncompleteGamma/BetaSymmetricSaddle.lean#L34) — definition, no admission.
- [DLMF.Statistical.betaSymmetricSaddleInverse_def](DLMF/IncompleteGamma/BetaSymmetricSaddle.lean#L57) — proved, no admission.
- [DLMF.Statistical.betaSymmetricSaddleInverse_spec](DLMF/IncompleteGamma/BetaSymmetricSaddle.lean#L78) — direct admission.
- [DLMF.Statistical.exists_betaEndpointApproximation_uniform_remainder](DLMF/IncompleteGamma/BetaEndpointError.lean#L68) — direct admission.
- [DLMF.Statistical.exists_isBetaGammaContinuation](DLMF/IncompleteGamma/BetaGammaSaddle.lean#L176) — direct admission.
- [DLMF.Statistical.exists_marcumBesselTail_uniform_remainder](DLMF/Statistical/MarcumFixedOrder.lean#L188) — direct admission.
- [DLMF.Statistical.exists_marcumQ_variable_order_uniform_remainder](DLMF/Statistical/MarcumVariableOrder.lean#L150) — direct admission.
- [DLMF.Statistical.gammaIncCFDen](DLMF/Statistical/ContinuedFraction.lean#L473) — definition, no admission.
- [DLMF.Statistical.gammaIncCFNum](DLMF/Statistical/ContinuedFraction.lean#L468) — definition, no admission.
- [DLMF.Statistical.gammaIncContFract](DLMF/Statistical/ContinuedFraction.lean#L477) — definition, no admission.
- [DLMF.Statistical.im_marcumSaddleCoefficient_even](DLMF/Statistical/MarcumVariableOrder.lean#L130) — direct admission.
- [DLMF.Statistical.incompleteBeta_continuedFraction](DLMF/IncompleteGamma/Beta.lean#L789) — proved, no admission.
- [DLMF.Statistical.incompleteBeta_hypergeometric_euler](DLMF/IncompleteGamma/Beta.lean#L211) — proved, no admission.
- [DLMF.Statistical.incompleteBeta_hypergeometric_pfaff](DLMF/IncompleteGamma/Beta.lean#L232) — proved, no admission.
- [DLMF.Statistical.incompleteBeta_symmetric_uniform_expansion](DLMF/IncompleteGamma/BetaAsymptotics.lean#L247) — direct admission.
- [DLMF.Statistical.integrableOn_betaGammaContour_monomial](DLMF/IncompleteGamma/BetaGammaSaddle.lean#L242) — direct admission.
- [DLMF.Statistical.integrableOn_betaGammaContour_taylor_remainder](DLMF/IncompleteGamma/BetaGammaSaddle.lean#L260) — direct admission.
- [DLMF.Statistical.integrableOn_marcumBesselDensity](DLMF/Statistical/MarcumProbability.lean#L64) — direct admission.
- [DLMF.Statistical.integrableOn_marcumBesselTail_kernel](DLMF/Statistical/MarcumFixedOrder.lean#L81) — direct admission.
- [DLMF.Statistical.integrable_marcumVerticalKernel](DLMF/Statistical/MarcumContours.lean#L40) — direct admission.
- [DLMF.Statistical.integral_betaGammaContour_monomial](DLMF/IncompleteGamma/BetaGammaSaddle.lean#L250) — direct admission.
- [DLMF.Statistical.isBetaGammaContinuation_iff](DLMF/IncompleteGamma/BetaGammaSaddle.lean#L120) — proved, no admission.
- [DLMF.Statistical.lowerIncompleteGamma_add_one](DLMF/Statistical/IncompleteGamma.lean#L44) — proved, no admission.
- [DLMF.Statistical.lowerIncompleteGamma_eq_tsum](DLMF/Statistical/IncompleteGamma.lean#L61) — proved, no admission.
- [DLMF.Statistical.marcumBesselCoefficient](DLMF/Statistical/MarcumFixedOrder.lean#L71) — definition, no admission.
- [DLMF.Statistical.marcumBesselCoefficient_def](DLMF/Statistical/MarcumFixedOrder.lean#L75) — proved, no admission.
- [DLMF.Statistical.marcumBesselCoefficient_succ](DLMF/Statistical/MarcumFixedOrder.lean#L135) — direct admission.
- [DLMF.Statistical.marcumBesselCoefficient_zero](DLMF/Statistical/MarcumFixedOrder.lean#L131) — proved, no admission.
- [DLMF.Statistical.marcumBesselTail](DLMF/Statistical/MarcumFixedOrder.lean#L52) — definition, no admission.
- [DLMF.Statistical.marcumBesselTail_def](DLMF/Statistical/MarcumFixedOrder.lean#L56) — proved, no admission.
- [DLMF.Statistical.marcumP](DLMF/Statistical/MarcumQ.lean#L63) — definition, no admission.
- [DLMF.Statistical.marcumP_add_marcumQ](DLMF/Statistical/MarcumQ.lean#L87) — proved, no admission.
- [DLMF.Statistical.marcumP_eq_besselTail](DLMF/Statistical/MarcumFixedOrder.lean#L103) — direct admission.
- [DLMF.Statistical.marcumP_eq_integral](DLMF/Statistical/MarcumProbability.lean#L72) — direct admission.
- [DLMF.Statistical.marcumP_eq_vertical_integral](DLMF/Statistical/MarcumContours.lean#L55) — direct admission.
- [DLMF.Statistical.marcumP_le_one](DLMF/Statistical/MarcumQ.lean#L99) — proved, no admission.
- [DLMF.Statistical.marcumP_nonneg](DLMF/Statistical/MarcumQ.lean#L94) — proved, no admission.
- [DLMF.Statistical.marcumP_zero_left](DLMF/Statistical/MarcumQ.lean#L106) — proved, no admission.
- [DLMF.Statistical.marcumQ](DLMF/Statistical/MarcumQ.lean#L67) — definition, no admission.
- [DLMF.Statistical.marcumQ_add_one](DLMF/Statistical/MarcumQ.lean#L140) — proved, no admission.
- [DLMF.Statistical.marcumQ_besselTail_leading_term](DLMF/Statistical/MarcumFixedOrder.lean#L197) — direct admission.
- [DLMF.Statistical.marcumQ_eq_besselTail](DLMF/Statistical/MarcumFixedOrder.lean#L95) — direct admission.
- [DLMF.Statistical.marcumQ_eq_integral](DLMF/Statistical/MarcumQ.lean#L283) — proved, no admission.
- [DLMF.Statistical.marcumQ_eq_vertical_integral](DLMF/Statistical/MarcumContours.lean#L47) — direct admission.
- [DLMF.Statistical.marcumQ_le_one](DLMF/Statistical/MarcumProbability.lean#L36) — proved, no admission.
- [DLMF.Statistical.marcumQ_nonneg](DLMF/Statistical/MarcumProbability.lean#L28) — proved, no admission.
- [DLMF.Statistical.marcumQ_recurrence](DLMF/Statistical/MarcumQ.lean#L189) — proved, no admission.
- [DLMF.Statistical.marcumQ_zero_left](DLMF/Statistical/MarcumProbability.lean#L44) — proved, no admission.
- [DLMF.Statistical.marcumSaddleAmplitude](DLMF/Statistical/MarcumVariableOrder.lean#L49) — definition, no admission.
- [DLMF.Statistical.marcumSaddleAmplitude_def](DLMF/Statistical/MarcumVariableOrder.lean#L87) — proved, no admission.
- [DLMF.Statistical.marcumSaddleCoefficient](DLMF/Statistical/MarcumVariableOrder.lean#L56) — definition, no admission.
- [DLMF.Statistical.marcumSaddleCoefficient_def](DLMF/Statistical/MarcumVariableOrder.lean#L95) — proved, no admission.
- [DLMF.Statistical.marcumSaddleInverse](DLMF/Statistical/MarcumVariableOrder.lean#L34) — definition, no admission.
- [DLMF.Statistical.marcumSaddleInverse_def](DLMF/Statistical/MarcumVariableOrder.lean#L71) — proved, no admission.
- [DLMF.Statistical.marcumSaddleInverse_spec](DLMF/Statistical/MarcumVariableOrder.lean#L106) — direct admission.
- [DLMF.Statistical.marcumSaddlePhase](DLMF/Statistical/MarcumVariableOrder.lean#L30) — definition, no admission.
- [DLMF.Statistical.marcumSaddlePhase_def](DLMF/Statistical/MarcumVariableOrder.lean#L67) — proved, no admission.
- [DLMF.Statistical.marcumVerticalKernel](DLMF/Statistical/MarcumContours.lean#L28) — definition, no admission.
- [DLMF.Statistical.marcumVerticalKernel_def](DLMF/Statistical/MarcumContours.lean#L33) — proved, no admission.
- [DLMF.Statistical.norm_betaAuxF_le_pochhammer](DLMF/IncompleteGamma/BetaEndpointError.lean#L46) — direct admission.
- [DLMF.Statistical.norm_marcumBesselTail_sub_sum_le](DLMF/Statistical/MarcumFixedOrder.lean#L174) — direct admission.
- [DLMF.Statistical.norm_regularizedIncompleteBeta_sub_endpointApproximation_le](DLMF/IncompleteGamma/BetaEndpointError.lean#L56) — direct admission.
- [DLMF.Statistical.norm_regularizedIncompleteBeta_sub_gamma_sum_le_contour](DLMF/IncompleteGamma/BetaGammaSaddle.lean#L285) — direct admission.
- [DLMF.Statistical.not_integrableOn_marcumBesselTail_kernel_zero](DLMF/Statistical/MarcumFixedOrder.lean#L89) — direct admission.
- [DLMF.Statistical.regularizedIncompleteBeta_contiguous_12](DLMF/IncompleteGamma/Beta.lean#L466) — proved, no admission.
- [DLMF.Statistical.regularizedIncompleteBeta_eq_gamma_sub_finite_contour](DLMF/IncompleteGamma/BetaGammaSaddle.lean#L269) — direct admission.
- [DLMF.Statistical.regularizedIncompleteBeta_mellinBarnes](DLMF/IncompleteGamma/Beta.lean#L254) — proved, no admission.
- [DLMF.Statistical.regularizedIncompleteBeta_neighbors](DLMF/IncompleteGamma/Beta.lean#L368) — proved, no admission.
- [DLMF.Statistical.regularizedIncompleteBeta_neighbors_down](DLMF/IncompleteGamma/Beta.lean#L411) — proved, no admission.
- [DLMF.Statistical.regularizedIncompleteBeta_ofReal](DLMF/IncompleteGamma/Beta.lean#L86) — proved, no admission.
- [DLMF.Statistical.summable_marcumP_term](DLMF/Statistical/MarcumQ.lean#L71) — proved, no admission.
- [DLMF.Statistical.summable_marcumQ_term](DLMF/Statistical/MarcumQ.lean#L81) — proved, no admission.
- [DLMF.Statistical.tendsto_marcumP_besselTail_diagonal](DLMF/Statistical/MarcumFixedOrder.lean#L122) — direct admission.
- [DLMF.Statistical.tendsto_marcumQ_besselTail_diagonal](DLMF/Statistical/MarcumFixedOrder.lean#L112) — direct admission.
- [DLMF.Statistical.tricomiIncompleteGamma](DLMF/Statistical/Basic/IncompleteGamma.lean#L34) — definition, no admission.
- [DLMF.Statistical.tricomiIncompleteGamma_neg_nat](DLMF/Statistical/IncompleteGamma.lean#L138) — proved, no admission.
- [Real.hasSum_pow_div_log_of_abs_lt_one](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Log/Deriv.lean#L352) — proved, no admission.
- [Real.log_le_sub_one_of_pos](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean#L307) — proved, no admission.
- [TauCeti.Probability.cdf_chiSquaredMeasure_eq](.lake/packages/TauCeti/TauCeti/Probability/Distributions/ChiSquared/Basic.lean#L320) — proved, no admission.
- [TauCeti.Probability.cdf_gammaMeasure_eq](.lake/packages/TauCeti/TauCeti/Probability/Distributions/Gamma/Cdf.lean#L101) — proved, no admission.
- [TauCeti.Probability.cdf_gaussianReal_zero_one](.lake/packages/TauCeti/TauCeti/Probability/Distributions/Gaussian/Cdf.lean#L150) — proved, no admission.
- [TauCeti.Probability.hasDerivAt_cdf_gaussianReal](.lake/packages/TauCeti/TauCeti/Probability/Distributions/Gaussian/Cdf.lean#L228) — proved, no admission.
- [TauCeti.regularizedGamma_lt_one](.lake/packages/TauCeti/TauCeti/Analysis/SpecialFunctions/IncompleteGamma/Basic.lean#L507) — proved, no admission.
- [TauCeti.regularizedGamma_pos](.lake/packages/TauCeti/TauCeti/Analysis/SpecialFunctions/IncompleteGamma/Basic.lean#L502) — proved, no admission.
