# Temme Chapters7 8 acquisition ledger

All **20** entries and their distinct subclaims are audited in lookup order Mathlib,
TauCeti, DLMF. Pins: Mathlib `1b1ccf4b088b32fa3f23f2de1127433254a81e1e`, TauCeti
`396c3bd971e9722aa8656231760e710fe641d8cf`, Lean `v4.36.0-rc2`. The source synopsis,
pins and existing definition bodies are unchanged. “Existing” does not imply proved;
the transitive Lean axiom audit below distinguishes proofs, admissions and dependence on
admissions. Newly admitted statements remain in the theorem layer; defining APIs are proved.

## TEM-07-01 — Kummer series, confluence and equation (7.1)–(7.6), pp. 172–173.

Existing `DLMF.Confluent.kummerM`, `DLMF.Confluent.hasSum_kummerM`,
`DLMF.Confluent.analyticOnNhd_kummerM`, `DLMF.Confluent.kummerM_ode`, and
`DLMF.Confluent.kummerM_kummer_transform` give the literal series, entire argument, equation and
transformation at every regular lower parameter. `DLMF.Confluent.wronskian_kummerM_pair` covers
the shifted second solution and its independence for nonintegral c. Existing
`DLMF.Confluent.kummerM_eq_mul_regularizedHGFun` and
`DLMF.Confluent.analyticOnNhd_regularizedConfluent_comp` cover the whole regularized parameter
continuation. Shared new
`DLMF.Confluent.tendstoLocallyUniformly_ordinaryHypergeometric_add_div_atTop`, with d=0, gives the
actual locally uniform confluence on bounded argument sets. The earlier pointwise confluence
statement alone was insufficient. The shared Kristensson acquisition owns that module; no
duplicate confluence target is retained.

Checked named coverage: 9 declarations; 1 depend on admissions.

## TEM-07-02 — Kummer integral and derivatives (7.7)–(7.9), pp. 173–174.

Existing `DLMF.Confluent.regularized_euler_integral`, multiplied by Gamma(c), and
`DLMF.Confluent.kummerM_eq_mul_regularizedHGFun` give the full complex Euler integral on Re c>Re
a>0. Existing `DLMF.Confluent.iteratedDeriv_kummerM` gives every derivative with the precise
Pochhammer ratio. New `DLMF.Confluent.hasAsymptoticExpansion_regularizedConfluent_sector` and the
canonical `DLMF.Confluent.kummerCoeff` give every order of the dominant expansion for all fixed
complex a,c, without the extra real-part restrictions of the older Euler-integral proof.
Multiplication by Gamma(c) recovers ordinary M on its regular parameter set. The reciprocal-Gamma
leading coefficient may vanish: the assertion is an asymptotic expansion, not equivalence to zero.

Checked named coverage: 5 declarations; 1 depend on admissions.

## TEM-07-03 — Tricomi function and its connection formula (7.12)–(7.15), pp. 175–176.

Existing `DLMF.Confluent.kummerU_laplace_integrable`, `DLMF.Confluent.kummerU_laplace`,
`DLMF.Confluent.kummerU_eq_connection`, and `DLMF.Confluent.tendsto_kummerUConnection` give the
actual absolutely convergent integral, connection formula and whole-expression integer-parameter
limit. `DLMF.Confluent.differentiableOn_kummerU` supplies principal-cut regularity. The equation
follows by substituting `DLMF.Confluent.iteratedDeriv_kummerU`, `DLMF.Confluent.deriv_kummerU` and
`DLMF.Confluent.kummerU_ode_contiguous`; this exact derivation was checked in the Duverney ledger.
`DLMF.Confluent.kummerU_kummer_transform_all` gives the coherent-power transformation for every
second parameter, and `DLMF.Confluent.kummerU_zero_arg` gives the zero value for Re c<1, even
without the initial Re a>0 restriction. New `DLMF.Confluent.kummerUContinuedOnLog`, its proved
defining and nonintegral/integral APIs, `DLMF.Confluent.tendsto_kummerUContinuedOnLog`,
`DLMF.Confluent.kummerUContinuedOnLog_eq_principal`, and
`DLMF.Confluent.analyticAt_kummerUContinuedOnLog` retain joint continuation in both complex
parameters and every logarithmic sheet. The pre-existing raw connection expression is preserved
unchanged.

Checked named coverage: 14 declarations; 3 depend on admissions.

## TEM-07-04 — Tricomi asymptotics and logarithmic case (7.13), pp. 175–177.

New `DLMF.Confluent.hasAsymptoticExpansion_kummerUContinuedOnLog` gives every fixed complex a,c
and the full lifted sector |arg z|<3pi/2, including integer c. Its actual coefficient family is
`DLMF.Confluent.tricomiCoeff`. Existing `DLMF.Confluent.kummerU_nat_log`, at n=0, is exactly the
displayed c=1 logarithmic series; `DLMF.Confluent.tricomiLogSeries`,
`DLMF.Confluent.summable_tricomiLogSeries`, `DLMF.Confluent.tricomi_log_series_split` retain
convergence and all finite-power singular parts for c=n+1. Existing
`DLMF.Confluent.kummerU_nat_log_recipGamma` and
`DLMF.Confluent.tricomi_log_series_split_recipGamma` give the reciprocal-Gamma version through
exceptional first parameters. Negative integral second parameters follow by
`DLMF.Confluent.kummerU_kummer_transform_all`; no finite singular sum is dropped.

Checked named coverage: 9 declarations; 1 depend on admissions.

## TEM-07-05 — Whittaker normalization (7.17)–(7.18), p. 178.

Existing `DLMF.Confluent.whittakerM`, `DLMF.Confluent.whittakerW`,
`DLMF.Confluent.whittakerW_eq_kummerU`, `DLMF.Confluent.whittakerM_ode`,
`DLMF.Confluent.whittakerW_ode`, and `DLMF.Confluent.whittakerW_even_mu` give the exact
normalization, both equations and order reflection. Ordinary Whittaker M keeps the regular
lower-parameter hypothesis; regularized Whittaker M is a separate function and is not silently
substituted. The new full logarithmic Whittaker lift belongs to the shared Olver acquisition and
uses the all-parameter Tricomi lift above.

Checked named coverage: 6 declarations; 0 depend on admissions.

## TEM-07-06 — Coulomb normalization (7.19), pp. 178–179.

New foundational `DLMF.Coulomb.Real.coulombNormalization`, `DLMF.Coulomb.Real.coulombSigma`,
`DLMF.Coulomb.Real.coulombTheta`, `DLMF.Coulomb.Real.coulombF`,
`DLMF.Coulomb.Real.coulombIncoming`, and `DLMF.Coulomb.Real.coulombG` retain every real angular
momentum ell>=0; all defining equations, positivity of normalization, and the natural-order phase
bridge are proved. They reuse the canonical unnormalized complex-order wave. New theorem-layer
`DLMF.Coulomb.Real.coulombF_of_normalized_complex_wave`,
`DLMF.Coulomb.Real.coulombG_eq_tricomi_combination`, `DLMF.Coulomb.Real.coulombF_natCast`,
`DLMF.Coulomb.Real.coulombG_natCast`, `DLMF.Coulomb.Real.analyticOnNhd_coulombF_coulombG`,
`DLMF.Coulomb.Real.coulombF_coulombG_ode`, `DLMF.Coulomb.Real.isBigO_coulombF_sub_sin`, and
`DLMF.Coulomb.Real.isBigO_coulombG_sub_cos` give reality, compatibility, equations and both
additive errors on rho>0. The source A equals normalization times rho^(ell+1) exp(-i rho), since
(2rho)^(ell+1)/2=2^ell rho^(ell+1). Natural-order-only legacy Coulomb results do not cover this
real-parameter source.

Checked named coverage: 14 declarations; 8 depend on admissions.

## TEM-07-07 — Parabolic cylinder solutions (7.20)–(7.22), p. 179.

Existing `DLMF.Confluent.parabolicCylinderEven`, `DLMF.Confluent.parabolicCylinderOdd`,
`DLMF.Confluent.parabolicCylinderU`, `DLMF.Confluent.parabolicCylinderV`,
`DLMF.Confluent.parabolicCylinderD` and their entire-function API give the source definitions with
Gamma reciprocals. `DLMF.Confluent.isWeberSolution_parabolicCylinderEven`,
`DLMF.Confluent.isWeberSolution_parabolicCylinderOdd`,
`DLMF.Confluent.parabolicCylinderEven_zero`, `DLMF.Confluent.parabolicCylinderEvenDeriv_zero`,
`DLMF.Confluent.parabolicCylinderOdd_zero`, `DLMF.Confluent.parabolicCylinderOddDeriv_zero`, and
`DLMF.Confluent.IsWeberSolution.wronskian_eq` give the basis equation and Wronskian one. Existing
`DLMF.Confluent.parabolicCylinderV_eq`, `DLMF.Confluent.parabolicCylinderV_entire_order`,
`DLMF.Confluent.parabolicCylinderV_wronskian`, and `DLMF.Confluent.parabolicCylinderD_nat` give
the V connection, removable parameter limits, U/V Wronskian and Hermite specialization. The
source's U_pc is the parabolic cylinder function, never the identically named Tricomi U.

Checked named coverage: 16 declarations; 0 depend on admissions.

## TEM-07-08 — Error functions (7.23), p. 180.

Existing `DLMF.Confluent.erf`, `DLMF.Confluent.erfc`,
`DLMF.Confluent.erf_complex_segment_integral`, `DLMF.Confluent.differentiable_erf_complex`,
`DLMF.Confluent.erf_negative`, `DLMF.Confluent.hasDerivAt_erf_complex`, and the derivative of
`DLMF.Confluent.erfc` obtained by differentiating 1-erf give the oriented primitive, entire/odd
behavior and both derivatives. `DLMF.Confluent.erf_ofReal`, `DLMF.Confluent.erfc_ofReal` bridge to
TauCeti, and existing `DLMF.Confluent.erfc_horizontal_integral` gives the full improper Gaussian
tail after translating the radius. Existing `DLMF.Confluent.kummerM_erf`, with its explicit
nonzero-argument cancellation and the separate zero value, gives the exact Kummer specialization.

Checked named coverage: 10 declarations; 0 depend on admissions.

## TEM-07-09 — Exponential, sine and cosine integrals (7.24)–(7.25), pp. 180–182.

Existing `DLMF.Confluent.expIntegralE`, `DLMF.Confluent.expIntegralE_laplace_complex`,
`DLMF.Confluent.expIntegralE_stieltjes`, `DLMF.Confluent.expIntegralE_eq_exp_mul_kummerU`,
`DLMF.Confluent.expIntegralE_add_one`, and `DLMF.Confluent.hasDerivAt_expIntegralE` cover
arbitrary complex order, both full complex integral domains, incomplete-gamma and Tricomi bridges,
recurrence and derivative. Existing `DLMF.Confluent.expIntegralE_nat_hasSum` at n=1 gives the
entire convergent E1 logarithmic series on the principal cut.
`DLMF.Confluent.Real.expIntegralEi_principalValue` retains the symmetric pole principal value.
Existing `DLMF.Confluent.sinIntegral_entire`, `DLMF.Confluent.sinIntegral_segment_integral`,
`DLMF.Confluent.cosIntegralCin_entire`, `DLMF.Confluent.cosIntegralCin_segment_integral` and the
defining `DLMF.Confluent.cosIntegral` give Si and Ci with the logarithmic term retained.
`DLMF.Confluent.cosIntegral_horizontal_integral`, specialized to positive real argument, is the
ordered improper Ci tail; `DLMF.Confluent.tendsto_sinIntegralTail_add_ofReal`, with z=0 and
Si=pi/2+tail, gives the exact Si limit. Conditional tails are not represented as Bochner integrals
over the whole ray.

Checked named coverage: 15 declarations; 0 depend on admissions.

## TEM-07-10 — Gibbs limit, pp. 181–183.

The shared root acquisition `DLMF.Confluent.Real.squareWaveFourierSum`,
`DLMF.Confluent.Real.squareWaveFourierSum_sinIntegral_uniform`,
`DLMF.Confluent.Real.tendsto_squareWaveFourierSum_scaled`,
`DLMF.Confluent.Real.squareWaveFourierSum_le_first_peak`, and
`DLMF.Confluent.Real.one_lt_gibbs_peak` gives the actual odd-harmonic partial sum, the uniform
remainder on [0,pi-epsilon], fixed rescaled limits, and the exact first overshoot with strict
inequality. All declarations in that module are included in the checked index below. The decimal
approximation is excluded: numerical. No extra admission is introduced here.

Checked named coverage: 5 declarations; 4 depend on admissions.

## TEM-07-11 — Fresnel normalization, tails and Cornu geometry (7.26), pp. 182–185.

Existing `DLMF.Confluent.fresnelC_entire`, `DLMF.Confluent.fresnelS_entire`,
`DLMF.Confluent.fresnel_negative`, `DLMF.Confluent.Real.tendsto_fresnelC_atTop`,
`DLMF.Confluent.Real.tendsto_fresnelS_atTop`, and
`DLMF.Confluent.hasAsymptoticExpansion_fresnelAuxiliaryG_add_I_mul_fresnelAuxiliaryF` cover the
analytic part after the exact change of scale z=sqrt(pi/2)x. The shared root module
ErrorFunctions/CornuCurve defines the scaled curve and proves or states
`DLMF.Confluent.Real.cornuCurve_def`, `DLMF.Confluent.Real.norm_deriv_cornuCurve`,
`DLMF.Confluent.Real.integral_norm_deriv_cornuCurve`, and
`DLMF.Confluent.Real.curvature_cornuCurve`; these give arc length sqrt(2/pi)t and curvature
sqrt(2pi)t. Multiplying arc length by pi gives curvature algebraically. Existing
`DLMF.Confluent.fresnelC`, `DLMF.Confluent.fresnelS` use the DLMF parameter, so the source scale
is never silently identified with it.

Checked named coverage: 12 declarations; 3 depend on admissions.

## TEM-07-12 — Incomplete gamma and polynomial specializations, pp. 185–186.

Existing `DLMF.Confluent.kummerM_lowerIncompleteGamma` and
`DLMF.Confluent.kummerM_kummer_transform` give both lower-gamma identities on the initial Re a>0
domain; `DLMF.Confluent.upperIncompleteGamma_eq_cpow_mul_kummerU` and
`DLMF.Confluent.kummerU_kummer_transform_all` give the upper-gamma identity. The first and second
components of `DLMF.Confluent.kummerU_laguerrePolynomialL`, together with
`DLMF.Confluent.kummerU_neg_nat`, give the regular-denominator M specialization. New proved
`DLMF.Confluent.kummerU_eq_laguerreExtended` gives the U specialization for every complex alpha.
It uses the existing canonical `DLMF.OrthogonalPolynomials.laguerreExtended`;
`DLMF.OrthogonalPolynomials.laguerreExtended_eq` is the bridge to ordinary laguerrePolynomialL on
regular parameters. The totalized ordinary quotient is not the source polynomial at exceptional
parameters.

Checked named coverage: 9 declarations; 0 depend on admissions.

## TEM-08-01 — Ordinary first and second kind (8.4)–(8.8), pp. 194–196.

Existing `DLMF.Legendre.legendreP`, `DLMF.Legendre.legendreQ`, `DLMF.Legendre.legendreP_ode`,
`DLMF.Legendre.legendreQ_ode`, `DLMF.Legendre.legendreP_one`,
`DLMF.Legendre.legendreP_neg_sub_one`, and `DLMF.Legendre.legendreP_nat` give the exact
regularized definitions, equations, value one, degree reflection and polynomial specialization.
Existing `DLMF.Legendre.analyticAt_legendreQ` and the Gamma-prefactor/entire Olver-Q definition
give the meromorphic parameter interpretation and whole regularized denominator.
`DLMF.Legendre.associated_wronskian_11` at mu=0, with the ordinary-to-associated bridges and Gamma
quotient cancellation under LegendreQRegular, and the forward derivative identities
`DLMF.Legendre.associatedP_recurrence_4`, `DLMF.Legendre.associatedQ_recurrence_4` give the full
complex-degree Wronskian: multiply W by 1-z^2, substitute both derivatives, then cancel
(nu+1)Gamma(nu+1)/Gamma(nu+2)=1. A natural-degree-only Wronskian would not cover the synopsis.

Checked named coverage: 11 declarations; 0 depend on admissions.

## TEM-08-02 — Cut values and connection identities (8.9)–(8.14), pp. 196–198.

Existing `DLMF.Legendre.associated_connection_12` at mu=0 gives the degree-reflection connection:
multiply by Gamma(nu+1)Gamma(-nu) and apply Gamma reflection to obtain pi cot(pi nu)P.
`DLMF.Legendre.olverQ_boundary_aux` at mu=0 gives both signs of the boundary limit, with
`DLMF.Legendre.associatedP_boundary_upper`, the ordinary bridges and Gamma cancellation giving the
stated P term. `DLMF.Legendre.ferrersQ_boundary_average` gives the exact cut average, not an
interchange of analytic Q with Ferrers Q. Existing `DLMF.Legendre.ferrers_connection_10` at mu=0
gives the cosine/sine formula, while `DLMF.Legendre.continuousAt_ferrersQ_degree` retains
integral-degree limiting values wherever finite.

Checked named coverage: 6 declarations; 0 depend on admissions.

## TEM-08-03 — Zero-centred and logarithmic series (8.15)–(8.23), pp. 198–200.

New `DLMF.Legendre.legendreP_eq_even_add_odd_hypergeometric` states the zero-centered pair with
entire reciprocal-Gamma coefficients for every complex nu. Existing
`DLMF.Legendre.legendreP_zero_arg` gives A and new `DLMF.Legendre.deriv_legendreP_zero` gives B
without real-degree restrictions. New `DLMF.Legendre.hasSum_legendreP_logarithmic_endpoint` states
the full logarithmic expansion for nonintegral complex nu and the entire slit disk |1+z|<2.
Restricting a pre-existing hypergeometric connection formula to the overlap of two unit disks
would have lost part of the source domain.

Checked named coverage: 4 declarations; 3 depend on admissions.

## TEM-08-04 — Integral-degree second kind (8.24)–(8.33), pp. 200–202.

Existing `DLMF.Legendre.legendreQ_zero`, `DLMF.Legendre.legendreQ_one`,
`DLMF.Legendre.legendreQ_recurrence`, and `DLMF.Legendre.legendreQ_nat` give Q0,Q1,the undivided
recurrence and Qn=Pn Q0-W. The actual polynomial remainder is `DLMF.Legendre.legendreQPoly`; new
`DLMF.Legendre.legendreQPoly_eval_eq_convolution` and
`DLMF.Legendre.legendreQPoly_eval_eq_legendre_sum` give both complete finite sums. New
`DLMF.Legendre.intervalIntegrable_neumann_kernel`,
`DLMF.Legendre.legendreQ_nat_eq_neumann_integral`, and
`DLMF.Legendre.tendsto_neumann_principalValue_ferrersQ` cover the full complex complement of
[-1,1] and the actual symmetric deleted-interval limit. They retain the branch normalized at
positive infinity. The old z-1 slit-plane integral alone covered a smaller domain.

Checked named coverage: 10 declarations; 5 depend on admissions.

## TEM-08-05 — Integral representations (8.34)–(8.42), pp. 202–209.

Existing `DLMF.Legendre.legendreP_laplace` gives all complex nu and z>=1, stronger than the source
z>1. Existing `DLMF.Legendre.olverQ_real_integral` at mu=0 and Re nu>-1, multiplied by
Gamma(nu+1), gives precisely the cosh integral for Q; sqrt(pi)/Gamma(1/2)=1 cancels the prefactor.
Existing `DLMF.Legendre.ferrersP_mehler_dirichlet` at mu=0 and `DLMF.Legendre.ferrersP_zero` give
the Mehler-Dirichlet P integral for all complex degrees. Positive-real square roots and powers are
retained. The factor sqrt(2)/pi times (cos t-cos theta)^(-1/2) equals the source 2/pi times (2cos
t-2cos theta)^(-1/2).

Checked named coverage: 4 declarations; 0 depend on admissions.

## TEM-08-06 — Degree and derivative recurrences, Exercise 8.3, p. 214.

Existing `DLMF.Legendre.legendreP_recurrence` and `DLMF.Legendre.legendreP_deriv_recurrence` give
the degree and backward derivative identities; subtracting the degree recurrence gives the forward
derivative identity without dividing by nu. Existing `DLMF.Legendre.associatedQ_recurrence_3`,
`DLMF.Legendre.associatedQ_recurrence_5`, and `DLMF.Legendre.associatedQ_recurrence_4` at mu=0,
with the ordinary bridge and Gamma recurrence, give the matching Q identities. The regular
parameter predicate retains all finite meromorphic values; zero degree factors are never canceled
to manufacture exceptional values.

Checked named coverage: 5 declarations; 0 depend on admissions.

## TEM-08-07 — Associated equation and normalization, §8.7, pp. 209–213.

Existing `DLMF.Legendre.associatedP`, `DLMF.Legendre.olverQ`, `DLMF.Legendre.associatedQ`,
`DLMF.Legendre.legendreBranchPower`, and `DLMF.Legendre.ferrersP` are the exact normalized
principal-branch definitions, including the whole regularized hypergeometric expression at
integral order. Their basic ODE API gives the associated equation, including
`DLMF.Legendre.ferrersP_ode`. Existing `DLMF.Legendre.ferrersP_nat` gives the derivative identity
for every complex degree and natural order on the open interval; `DLMF.Legendre.ferrersPNat`
provides the canonical continuous polynomial endpoint extension at natural degree. The branch
power uses Log(z+1)+Log(z-1), never a fresh principal square root of z^2-1.

Checked named coverage: 8 declarations; 0 depend on admissions.

## TEM-08-08 — Associated polynomial orthogonality and addition, pp. 212–218.

Existing `DLMF.Legendre.ferrersP_negative_integer_order` at nu=n and m<=n, followed by
Gamma_nat_eq_factorial, gives the factorial relation. Existing
`DLMF.Legendre.ferrers_orthogonality_6` gives both off-diagonal zero and diagonal
2(n+m)!/((2n+1)(n-m)!). For the full addition domain, use the proved
`DLMF.OrthogonalPolynomials.LegendreAddition.legendre_eq_kernel`,
`DLMF.OrthogonalPolynomials.LegendreAddition.kernel`,
`DLMF.OrthogonalPolynomials.LegendreAddition.coeff`,
`DLMF.OrthogonalPolynomials.LegendreAddition.weight`, and
`DLMF.OrthogonalPolynomials.LegendreAddition.jet`. Substitute x=cos theta,y=cos theta',s=sin
theta,t=sin theta'; sin^2=1-cos^2 proves both algebraic hypotheses. On [0,pi], sqrt(1-cos^2)=sin,
so `DLMF.Legendre.ferrersPNat` turns each coefficient into the two Ferrers values; the product of
the two (-1)^m factors is one. `DLMF.Legendre.ferrersPNat_eq` gives the interior bridge and the
polynomial definition covers endpoints. This is the entire displayed finite addition theorem; the
older narrower theta+theta'<pi theorem is not used for the full domain.

Checked named coverage: 9 declarations; 0 depend on admissions.

## Validation

All 20 entries are mapped. The transitive `#print axioms` audit checked **186** distinct
declarations; **29** depend on admissions. The **7** new modules
owned by this supplement contain **40** public declarations, including
**21** directly admitted targets. Definitions and their
defining equations have no admissions. Every new module has passed a direct strict Lean check
with `autoImplicit=false` and `relaxedAutoImplicit=false`; modules are registered in their
area umbrellas. Repository-wide build and import integration are coordinated with the other
book acquisitions and reported separately.

The per-entry declaration locations and proof statuses are retained in
[reports/BookAcquisition-Temme-Chapters7-8.tsv](reports/BookAcquisition-Temme-Chapters7-8.tsv). No additional
source erratum or user approval question was identified in this supplement.

## Checked declaration index

- [DLMF.Confluent.IsWeberSolution.wronskian_eq](DLMF/ParabolicCylinder/Basic/WeberEquation.lean#L223) — proved, no admission.
- [DLMF.Confluent.Real.cornuCurve_def](DLMF/ErrorFunctions/CornuCurve.lean#L31) — proved, no admission.
- [DLMF.Confluent.Real.curvature_cornuCurve](DLMF/ErrorFunctions/CornuCurve.lean#L47) — direct admission.
- [DLMF.Confluent.Real.expIntegralEi_principalValue](DLMF/ExpIntegrals/AnalyticProperties.lean#L191) — proved, no admission.
- [DLMF.Confluent.Real.integral_norm_deriv_cornuCurve](DLMF/ErrorFunctions/CornuCurve.lean#L40) — direct admission.
- [DLMF.Confluent.Real.norm_deriv_cornuCurve](DLMF/ErrorFunctions/CornuCurve.lean#L35) — direct admission.
- [DLMF.Confluent.Real.one_lt_gibbs_peak](DLMF/ExpIntegrals/GibbsLimit.lean#L57) — direct admission.
- [DLMF.Confluent.Real.squareWaveFourierSum](DLMF/ExpIntegrals/GibbsLimit.lean#L25) — definition, no admission.
- [DLMF.Confluent.Real.squareWaveFourierSum_le_first_peak](DLMF/ExpIntegrals/GibbsLimit.lean#L50) — direct admission.
- [DLMF.Confluent.Real.squareWaveFourierSum_sinIntegral_uniform](DLMF/ExpIntegrals/GibbsLimit.lean#L34) — direct admission.
- [DLMF.Confluent.Real.tendsto_fresnelC_atTop](DLMF/Confluent/ErrorFunctions.lean#L116) — proved, no admission.
- [DLMF.Confluent.Real.tendsto_fresnelS_atTop](DLMF/Confluent/ErrorFunctions.lean#L134) — proved, no admission.
- [DLMF.Confluent.Real.tendsto_squareWaveFourierSum_scaled](DLMF/ExpIntegrals/GibbsLimit.lean#L43) — direct admission.
- [DLMF.Confluent.analyticAt_kummerUContinuedOnLog](DLMF/Confluent/Asymptotics/LogarithmicSector.lean#L54) — direct admission.
- [DLMF.Confluent.analyticOnNhd_kummerM](DLMF/Confluent/Basic/KummerProperties.lean#L139) — proved, no admission.
- [DLMF.Confluent.analyticOnNhd_regularizedConfluent_comp](DLMF/Confluent/Regularized.lean#L112) — proved, no admission.
- [DLMF.Confluent.cosIntegral](DLMF/ExpIntegrals/Basic/Functions.lean#L58) — definition, no admission.
- [DLMF.Confluent.cosIntegralCin_entire](DLMF/ExpIntegrals/Basic/Properties.lean#L93) — proved, no admission.
- [DLMF.Confluent.cosIntegralCin_segment_integral](DLMF/ExpIntegrals/Basic/Properties.lean#L266) — proved, no admission.
- [DLMF.Confluent.cosIntegral_horizontal_integral](DLMF/ExpIntegrals/AnalyticProperties.lean#L828) — proved, no admission.
- [DLMF.Confluent.deriv_kummerU](DLMF/Confluent/Recurrence/Derivatives.lean#L143) — proved, no admission.
- [DLMF.Confluent.differentiableOn_kummerU](DLMF/Confluent/BasicProperties/Wronskians.lean#L185) — proved, no admission.
- [DLMF.Confluent.differentiable_erf_complex](DLMF/ErrorFunctions/Basic/Properties.lean#L90) — proved, no admission.
- [DLMF.Confluent.erf](DLMF/Confluent/Basic/ErrorFunctions.lean#L50) — definition, no admission.
- [DLMF.Confluent.erf_complex_segment_integral](DLMF/ErrorFunctions/Basic/Properties.lean#L245) — proved, no admission.
- [DLMF.Confluent.erf_negative](DLMF/ErrorFunctions/Relations.lean#L56) — proved, no admission.
- [DLMF.Confluent.erf_ofReal](DLMF/ErrorFunctions/Basic/Properties.lean#L66) — proved, no admission.
- [DLMF.Confluent.erfc](DLMF/Confluent/Basic/ErrorFunctions.lean#L54) — definition, no admission.
- [DLMF.Confluent.erfc_horizontal_integral](DLMF/ErrorFunctions/AnalyticProperties.lean#L142) — proved, no admission.
- [DLMF.Confluent.erfc_ofReal](DLMF/ErrorFunctions/Basic/Properties.lean#L76) — proved, no admission.
- [DLMF.Confluent.expIntegralE](DLMF/Confluent/Basic/ExponentialIntegrals.lean#L42) — definition, no admission.
- [DLMF.Confluent.expIntegralE_add_one](DLMF/Confluent/ExpIntegral.lean#L79) — proved, no admission.
- [DLMF.Confluent.expIntegralE_eq_exp_mul_kummerU](DLMF/Confluent/ExpIntegral.lean#L55) — proved, no admission.
- [DLMF.Confluent.expIntegralE_laplace_complex](DLMF/IncompleteGamma/ExponentialIntegral.lean#L88) — proved, no admission.
- [DLMF.Confluent.expIntegralE_nat_hasSum](DLMF/IncompleteGamma/ExponentialIntegral.lean#L236) — proved, no admission.
- [DLMF.Confluent.expIntegralE_stieltjes](DLMF/IncompleteGamma/ExponentialIntegral.lean#L109) — proved, no admission.
- [DLMF.Confluent.fresnelC](DLMF/ErrorFunctions/Basic/Functions.lean#L61) — definition, no admission.
- [DLMF.Confluent.fresnelC_entire](DLMF/ErrorFunctions/Basic/Properties.lean#L174) — proved, no admission.
- [DLMF.Confluent.fresnelS](DLMF/ErrorFunctions/Basic/Functions.lean#L66) — definition, no admission.
- [DLMF.Confluent.fresnelS_entire](DLMF/ErrorFunctions/Basic/Properties.lean#L179) — proved, no admission.
- [DLMF.Confluent.fresnel_negative](DLMF/ErrorFunctions/Relations.lean#L84) — proved, no admission.
- [DLMF.Confluent.hasAsymptoticExpansion_fresnelAuxiliaryG_add_I_mul_fresnelAuxiliaryF](DLMF/Confluent/FresnelAsymptotics.lean#L106) — proved, no admission.
- [DLMF.Confluent.hasAsymptoticExpansion_kummerUContinuedOnLog](DLMF/Confluent/Asymptotics/LogarithmicSector.lean#L62) — direct admission.
- [DLMF.Confluent.hasAsymptoticExpansion_regularizedConfluent_sector](DLMF/Confluent/Asymptotics/LogarithmicSector.lean#L31) — direct admission.
- [DLMF.Confluent.hasDerivAt_erf_complex](DLMF/ErrorFunctions/Basic/Properties.lean#L80) — proved, no admission.
- [DLMF.Confluent.hasDerivAt_expIntegralE](DLMF/Confluent/ExpIntegral.lean#L93) — proved, no admission.
- [DLMF.Confluent.hasSum_kummerM](DLMF/Confluent/Basic/KummerContiguous.lean#L50) — proved, no admission.
- [DLMF.Confluent.isWeberSolution_parabolicCylinderEven](DLMF/ParabolicCylinder/Basic/WeberEquation.lean#L207) — proved, no admission.
- [DLMF.Confluent.isWeberSolution_parabolicCylinderOdd](DLMF/ParabolicCylinder/Basic/WeberEquation.lean#L213) — proved, no admission.
- [DLMF.Confluent.iteratedDeriv_kummerM](DLMF/Confluent/Recurrence/Contiguous.lean#L515) — proved, no admission.
- [DLMF.Confluent.iteratedDeriv_kummerU](DLMF/Confluent/Recurrence/Derivatives.lean#L184) — proved, no admission.
- [DLMF.Confluent.kummerCoeff](DLMF/Confluent/Asymptotics/LargeArgument.lean#L444) — definition, no admission.
- [DLMF.Confluent.kummerM](DLMF/Confluent/Basic/KummerM.lean#L47) — definition, no admission.
- [DLMF.Confluent.kummerM_eq_mul_regularizedHGFun](DLMF/Confluent/Basic/KummerProperties.lean#L104) — proved, no admission.
- [DLMF.Confluent.kummerM_erf](DLMF/Confluent/Relations.lean#L166) — proved, no admission.
- [DLMF.Confluent.kummerM_kummer_transform](DLMF/Confluent/Basic/KummerProperties.lean#L230) — proved, no admission.
- [DLMF.Confluent.kummerM_lowerIncompleteGamma](DLMF/Confluent/Relations.lean#L133) — proved, no admission.
- [DLMF.Confluent.kummerM_ode](DLMF/Confluent/Basic/KummerProperties.lean#L160) — proved, no admission.
- [DLMF.Confluent.kummerUContinuedOnLog](DLMF/Confluent/Basic/TricomiLogarithmic.lean#L31) — definition, no admission.
- [DLMF.Confluent.kummerUContinuedOnLog_def](DLMF/Confluent/Basic/TricomiLogarithmic.lean#L36) — proved, no admission.
- [DLMF.Confluent.kummerUContinuedOnLog_eq_principal](DLMF/Confluent/Asymptotics/LogarithmicSector.lean#L47) — direct admission.
- [DLMF.Confluent.kummerUContinuedOnLog_int](DLMF/Confluent/Basic/TricomiLogarithmic.lean#L47) — proved, no admission.
- [DLMF.Confluent.kummerUContinuedOnLog_of_not_int](DLMF/Confluent/Basic/TricomiLogarithmic.lean#L42) — proved, no admission.
- [DLMF.Confluent.kummerU_eq_connection](DLMF/Confluent/Basic/Tricomi.lean#L70) — proved, no admission.
- [DLMF.Confluent.kummerU_eq_laguerreExtended](DLMF/Confluent/LaguerreContinuation.lean#L29) — proved, no admission.
- [DLMF.Confluent.kummerU_kummer_transform_all](DLMF/Confluent/BasicProperties/Continuity.lean#L577) — proved, no admission.
- [DLMF.Confluent.kummerU_laguerrePolynomialL](DLMF/Confluent/Relations.lean#L841) — proved, no admission.
- [DLMF.Confluent.kummerU_laplace](DLMF/Confluent/IntegralRepresentations/EulerAndBessel.lean#L694) — proved, no admission.
- [DLMF.Confluent.kummerU_laplace_integrable](DLMF/Confluent/IntegralRepresentations/EulerAndBessel.lean#L309) — proved, no admission.
- [DLMF.Confluent.kummerU_nat_log](DLMF/Confluent/BasicProperties/IntegerParametersAndLimits.lean#L112) — proved, no admission.
- [DLMF.Confluent.kummerU_nat_log_recipGamma](DLMF/Confluent/BasicProperties/IntegerParametersAndLimits.lean#L132) — proved, no admission.
- [DLMF.Confluent.kummerU_neg_nat](DLMF/Confluent/BasicProperties/Continuity.lean#L652) — proved, no admission.
- [DLMF.Confluent.kummerU_ode_contiguous](DLMF/Confluent/Recurrence/Contiguous.lean#L501) — proved, no admission.
- [DLMF.Confluent.kummerU_zero_arg](DLMF/Confluent/BasicProperties/IntegerParametersAndLimits.lean#L835) — proved, no admission.
- [DLMF.Confluent.parabolicCylinderD](DLMF/ParabolicCylinder/Basic/Functions.lean#L88) — definition, no admission.
- [DLMF.Confluent.parabolicCylinderD_nat](DLMF/ParabolicCylinder/Basic/WeberEquation.lean#L403) — proved, no admission.
- [DLMF.Confluent.parabolicCylinderEven](DLMF/ParabolicCylinder/Basic/Functions.lean#L50) — definition, no admission.
- [DLMF.Confluent.parabolicCylinderEvenDeriv_zero](DLMF/ParabolicCylinder/Basic/WeberEquation.lean#L194) — proved, no admission.
- [DLMF.Confluent.parabolicCylinderEven_zero](DLMF/ParabolicCylinder/Basic/WeberEquation.lean#L190) — proved, no admission.
- [DLMF.Confluent.parabolicCylinderOdd](DLMF/ParabolicCylinder/Basic/Functions.lean#L55) — definition, no admission.
- [DLMF.Confluent.parabolicCylinderOddDeriv_zero](DLMF/ParabolicCylinder/Basic/WeberEquation.lean#L202) — proved, no admission.
- [DLMF.Confluent.parabolicCylinderOdd_zero](DLMF/ParabolicCylinder/Basic/WeberEquation.lean#L198) — proved, no admission.
- [DLMF.Confluent.parabolicCylinderU](DLMF/ParabolicCylinder/Basic/Functions.lean#L73) — definition, no admission.
- [DLMF.Confluent.parabolicCylinderV](DLMF/ParabolicCylinder/Basic/Functions.lean#L109) — definition, no admission.
- [DLMF.Confluent.parabolicCylinderV_entire_order](DLMF/ParabolicCylinder/ElementaryProperties.lean#L181) — proved, no admission.
- [DLMF.Confluent.parabolicCylinderV_eq](DLMF/Confluent/ParabolicCylinder/WronskiansAndConnections.lean#L201) — proved, no admission.
- [DLMF.Confluent.parabolicCylinderV_wronskian](DLMF/ParabolicCylinder/Basic/Wronskians.lean#L455) — proved, no admission.
- [DLMF.Confluent.regularized_euler_integral](DLMF/Confluent/IntegralRepresentations/EulerAndBessel.lean#L70) — proved, no admission.
- [DLMF.Confluent.sinIntegral_entire](DLMF/ExpIntegrals/Basic/Properties.lean#L84) — proved, no admission.
- [DLMF.Confluent.sinIntegral_segment_integral](DLMF/ExpIntegrals/Basic/Properties.lean#L246) — proved, no admission.
- [DLMF.Confluent.summable_tricomiLogSeries](DLMF/Confluent/LogSeries.lean#L59) — proved, no admission.
- [DLMF.Confluent.tendstoLocallyUniformly_ordinaryHypergeometric_add_div_atTop](DLMF/Confluent/ConfluenceUniform.lean#L29) — direct admission.
- [DLMF.Confluent.tendsto_kummerUConnection](DLMF/Confluent/BasicProperties/Continuity.lean#L210) — proved, no admission.
- [DLMF.Confluent.tendsto_kummerUContinuedOnLog](DLMF/Confluent/Asymptotics/LogarithmicSector.lean#L40) — direct admission.
- [DLMF.Confluent.tendsto_sinIntegralTail_add_ofReal](DLMF/ExpIntegrals/AnalyticProperties.lean#L750) — proved, no admission.
- [DLMF.Confluent.tricomiCoeff](DLMF/Confluent/Asymptotics/LargeArgument.lean#L66) — definition, no admission.
- [DLMF.Confluent.tricomiLogSeries](DLMF/Confluent/LogSeries.lean#L55) — definition, no admission.
- [DLMF.Confluent.tricomi_log_series_split](DLMF/Confluent/LogSeries.lean#L96) — proved, no admission.
- [DLMF.Confluent.tricomi_log_series_split_recipGamma](DLMF/Confluent/LogSeries.lean#L171) — proved, no admission.
- [DLMF.Confluent.upperIncompleteGamma_eq_cpow_mul_kummerU](DLMF/Confluent/IncompleteGamma.lean#L56) — proved, no admission.
- [DLMF.Confluent.whittakerM](DLMF/Confluent/Basic/Whittaker.lean#L51) — definition, no admission.
- [DLMF.Confluent.whittakerM_ode](DLMF/Confluent/Basic/Whittaker.lean#L103) — proved, no admission.
- [DLMF.Confluent.whittakerW](DLMF/Confluent/Basic/Whittaker.lean#L70) — definition, no admission.
- [DLMF.Confluent.whittakerW_eq_kummerU](DLMF/Confluent/Basic/Whittaker.lean#L231) — proved, no admission.
- [DLMF.Confluent.whittakerW_even_mu](DLMF/Confluent/Whittaker.lean#L437) — proved, no admission.
- [DLMF.Confluent.whittakerW_ode](DLMF/Confluent/Basic/Whittaker.lean#L199) — proved, no admission.
- [DLMF.Confluent.wronskian_kummerM_pair](DLMF/Confluent/BasicProperties/Wronskians.lean#L323) — proved, no admission.
- [DLMF.Coulomb.Real.analyticOnNhd_coulombF_coulombG](DLMF/Coulomb/RealOrder.lean#L56) — direct admission.
- [DLMF.Coulomb.Real.coulombF](DLMF/Coulomb/Basic/RealOrder.lean#L43) — definition, no admission.
- [DLMF.Coulomb.Real.coulombF_coulombG_ode](DLMF/Coulomb/RealOrder.lean#L63) — direct admission.
- [DLMF.Coulomb.Real.coulombF_def](DLMF/Coulomb/Basic/RealOrder.lean#L72) — proved, no admission.
- [DLMF.Coulomb.Real.coulombF_natCast](DLMF/Coulomb/RealOrder.lean#L44) — direct admission.
- [DLMF.Coulomb.Real.coulombF_of_normalized_complex_wave](DLMF/Coulomb/RealOrder.lean#L29) — direct admission.
- [DLMF.Coulomb.Real.coulombG](DLMF/Coulomb/Basic/RealOrder.lean#L55) — definition, no admission.
- [DLMF.Coulomb.Real.coulombG_def](DLMF/Coulomb/Basic/RealOrder.lean#L84) — proved, no admission.
- [DLMF.Coulomb.Real.coulombG_eq_tricomi_combination](DLMF/Coulomb/RealOrder.lean#L37) — direct admission.
- [DLMF.Coulomb.Real.coulombG_natCast](DLMF/Coulomb/RealOrder.lean#L50) — direct admission.
- [DLMF.Coulomb.Real.coulombIncoming](DLMF/Coulomb/Basic/RealOrder.lean#L48) — definition, no admission.
- [DLMF.Coulomb.Real.coulombIncoming_def](DLMF/Coulomb/Basic/RealOrder.lean#L77) — proved, no admission.
- [DLMF.Coulomb.Real.coulombNormalization](DLMF/Coulomb/Basic/RealOrder.lean#L28) — definition, no admission.
- [DLMF.Coulomb.Real.coulombNormalization_def](DLMF/Coulomb/Basic/RealOrder.lean#L58) — proved, no admission.
- [DLMF.Coulomb.Real.coulombNormalization_pos](DLMF/Coulomb/Basic/RealOrder.lean#L88) — proved, no admission.
- [DLMF.Coulomb.Real.coulombSigma](DLMF/Coulomb/Basic/RealOrder.lean#L34) — definition, no admission.
- [DLMF.Coulomb.Real.coulombSigma_def](DLMF/Coulomb/Basic/RealOrder.lean#L63) — proved, no admission.
- [DLMF.Coulomb.Real.coulombSigma_natCast](DLMF/Coulomb/Basic/RealOrder.lean#L102) — proved, no admission.
- [DLMF.Coulomb.Real.coulombTheta](DLMF/Coulomb/Basic/RealOrder.lean#L38) — definition, no admission.
- [DLMF.Coulomb.Real.coulombTheta_def](DLMF/Coulomb/Basic/RealOrder.lean#L67) — proved, no admission.
- [DLMF.Coulomb.Real.isBigO_coulombF_sub_sin](DLMF/Coulomb/RealOrder.lean#L72) — direct admission.
- [DLMF.Coulomb.Real.isBigO_coulombG_sub_cos](DLMF/Coulomb/RealOrder.lean#L79) — direct admission.
- [DLMF.Legendre.analyticAt_legendreQ](DLMF/Legendre/Basic/Properties.lean#L389) — proved, no admission.
- [DLMF.Legendre.associatedP](DLMF/Legendre/Basic/Associated.lean#L49) — definition, no admission.
- [DLMF.Legendre.associatedP_boundary_upper](DLMF/Legendre/Continuation/LogarithmicBranches.lean#L135) — proved, no admission.
- [DLMF.Legendre.associatedP_recurrence_4](DLMF/Legendre/AssociatedRecurrences.lean#L754) — proved, no admission.
- [DLMF.Legendre.associatedQ](DLMF/Legendre/Basic/Associated.lean#L61) — definition, no admission.
- [DLMF.Legendre.associatedQ_recurrence_3](DLMF/Legendre/AssociatedRecurrences.lean#L819) — proved, no admission.
- [DLMF.Legendre.associatedQ_recurrence_4](DLMF/Legendre/AssociatedRecurrences.lean#L991) — proved, no admission.
- [DLMF.Legendre.associatedQ_recurrence_5](DLMF/Legendre/AssociatedRecurrences.lean#L1031) — proved, no admission.
- [DLMF.Legendre.associated_connection_12](DLMF/Legendre/Connections.lean#L392) — proved, no admission.
- [DLMF.Legendre.associated_wronskian_11](DLMF/Legendre/AssociatedRecurrences.lean#L1082) — proved, no admission.
- [DLMF.Legendre.continuousAt_ferrersQ_degree](DLMF/Legendre/AssociatedRecurrences.lean#L353) — proved, no admission.
- [DLMF.Legendre.deriv_legendreP_zero](DLMF/Legendre/OrdinaryLocalSeries.lean#L40) — direct admission.
- [DLMF.Legendre.ferrersP](DLMF/Legendre/Basic/Functions.lean#L40) — definition, no admission.
- [DLMF.Legendre.ferrersPNat](DLMF/Legendre/Basic/Harmonics.lean#L40) — definition, no admission.
- [DLMF.Legendre.ferrersPNat_eq](DLMF/Legendre/Harmonics.lean#L58) — proved, no admission.
- [DLMF.Legendre.ferrersP_mehler_dirichlet](DLMF/Legendre/IntegralRepresentations/Ferrers.lean#L175) — proved, no admission.
- [DLMF.Legendre.ferrersP_nat](DLMF/Legendre/Ferrers.lean#L37) — proved, no admission.
- [DLMF.Legendre.ferrersP_negative_integer_order](DLMF/Legendre/Connections.lean#L302) — proved, no admission.
- [DLMF.Legendre.ferrersP_ode](DLMF/Legendre/Basic/Properties.lean#L170) — proved, no admission.
- [DLMF.Legendre.ferrersP_zero](DLMF/Legendre/Basic/Properties.lean#L128) — proved, no admission.
- [DLMF.Legendre.ferrersQ_boundary_average](DLMF/Legendre/Continuation/LogarithmicBranches.lean#L702) — proved, no admission.
- [DLMF.Legendre.ferrers_connection_10](DLMF/Legendre/Connections.lean#L274) — proved, no admission.
- [DLMF.Legendre.ferrers_orthogonality_6](DLMF/Legendre/Integrals/FerrersGreen.lean#L75) — proved, no admission.
- [DLMF.Legendre.hasSum_legendreP_logarithmic_endpoint](DLMF/Legendre/OrdinaryLocalSeries.lean#L48) — direct admission.
- [DLMF.Legendre.intervalIntegrable_neumann_kernel](DLMF/Legendre/IntegerSecondKind.lean#L46) — direct admission.
- [DLMF.Legendre.legendreBranchPower](DLMF/Legendre/Basic/Associated.lean#L42) — definition, no admission.
- [DLMF.Legendre.legendreP](DLMF/Legendre/Basic/Functions.lean#L35) — definition, no admission.
- [DLMF.Legendre.legendreP_deriv_recurrence](DLMF/Legendre/Recurrences.lean#L60) — proved, no admission.
- [DLMF.Legendre.legendreP_eq_even_add_odd_hypergeometric](DLMF/Legendre/OrdinaryLocalSeries.lean#L30) — direct admission.
- [DLMF.Legendre.legendreP_laplace](DLMF/Legendre/Laplace.lean#L233) — proved, no admission.
- [DLMF.Legendre.legendreP_nat](DLMF/Legendre/FirstKindProperties.lean#L38) — proved, no admission.
- [DLMF.Legendre.legendreP_neg_sub_one](DLMF/Legendre/Basic/Properties.lean#L65) — proved, no admission.
- [DLMF.Legendre.legendreP_ode](DLMF/Legendre/Basic/Properties.lean#L116) — proved, no admission.
- [DLMF.Legendre.legendreP_one](DLMF/Legendre/Basic/Properties.lean#L56) — proved, no admission.
- [DLMF.Legendre.legendreP_recurrence](DLMF/Legendre/Recurrences.lean#L41) — proved, no admission.
- [DLMF.Legendre.legendreP_zero_arg](DLMF/Legendre/Recurrences.lean#L101) — proved, no admission.
- [DLMF.Legendre.legendreQ](DLMF/Legendre/Basic/Functions.lean#L48) — definition, no admission.
- [DLMF.Legendre.legendreQPoly](DLMF/Legendre/Integer.lean#L235) — definition, no admission.
- [DLMF.Legendre.legendreQPoly_eval_eq_convolution](DLMF/Legendre/IntegerSecondKind.lean#L29) — direct admission.
- [DLMF.Legendre.legendreQPoly_eval_eq_legendre_sum](DLMF/Legendre/IntegerSecondKind.lean#L37) — direct admission.
- [DLMF.Legendre.legendreQ_nat](DLMF/Legendre/Integer.lean#L250) — proved, no admission.
- [DLMF.Legendre.legendreQ_nat_eq_neumann_integral](DLMF/Legendre/IntegerSecondKind.lean#L55) — direct admission.
- [DLMF.Legendre.legendreQ_ode](DLMF/Legendre/Basic/Properties.lean#L306) — proved, no admission.
- [DLMF.Legendre.legendreQ_one](DLMF/Legendre/Integer.lean#L204) — proved, no admission.
- [DLMF.Legendre.legendreQ_recurrence](DLMF/Legendre/Integer.lean#L143) — proved, no admission.
- [DLMF.Legendre.legendreQ_zero](DLMF/Legendre/SecondKind.lean#L39) — proved, no admission.
- [DLMF.Legendre.olverQ](DLMF/Legendre/Basic/Associated.lean#L54) — definition, no admission.
- [DLMF.Legendre.olverQ_boundary_aux](DLMF/Legendre/Continuation/LogarithmicBranches.lean#L377) — proved, no admission.
- [DLMF.Legendre.olverQ_real_integral](DLMF/Legendre/IntegralRepresentations/Ferrers.lean#L337) — proved, no admission.
- [DLMF.Legendre.tendsto_neumann_principalValue_ferrersQ](DLMF/Legendre/IntegerSecondKind.lean#L64) — direct admission.
- [DLMF.OrthogonalPolynomials.LegendreAddition.coeff](DLMF/OrthogonalPolynomials/LegendreAddition.lean#L221) — definition, no admission.
- [DLMF.OrthogonalPolynomials.LegendreAddition.jet](DLMF/OrthogonalPolynomials/LegendreAddition.lean#L46) — definition, no admission.
- [DLMF.OrthogonalPolynomials.LegendreAddition.kernel](DLMF/OrthogonalPolynomials/LegendreAddition.lean#L480) — definition, no admission.
- [DLMF.OrthogonalPolynomials.LegendreAddition.legendre_eq_kernel](DLMF/OrthogonalPolynomials/LegendreAddition.lean#L533) — proved, no admission.
- [DLMF.OrthogonalPolynomials.LegendreAddition.weight](DLMF/OrthogonalPolynomials/LegendreAddition.lean#L219) — definition, no admission.
- [DLMF.OrthogonalPolynomials.laguerreExtended](DLMF/OrthogonalPolynomials/Basic/Definitions.lean#L103) — definition, no admission.
- [DLMF.OrthogonalPolynomials.laguerreExtended_eq](DLMF/OrthogonalPolynomials/Basic/Classical.lean#L478) — proved, no admission.

## Checked addition coefficient derivation

This algebraic adapter checks the factorial-weighted Ferrers coefficient in the full
addition kernel, including the polynomial endpoint values. The sine substitutions stated
in TEM-08-08 then impose the two kernel hypotheses.

```lean
import DLMF.OrthogonalPolynomials.LegendreAddition
import DLMF.Legendre.Basic.Harmonics
open Complex DLMF.Legendre DLMF.OrthogonalPolynomials
open DLMF.OrthogonalPolynomials.LegendreAddition
example (n k : ℕ) (x y : ℝ) :
    coeff n k x y (Real.sqrt (1-x^2)) (Real.sqrt (1-y^2)) =
      weight n k * ferrersPNat n k x * ferrersPNat n k y := by
  unfold coeff ferrersPNat jet
  have hs : ((-1 : ℂ) ^ k) * (-1) ^ k = 1 := by rw [← mul_pow]; simp
  rw [mul_pow]
  linear_combination
    -(weight n k * (Real.sqrt (1-x^2) : ℂ)^k * (Real.sqrt (1-y^2) : ℂ)^k *
      iteratedDeriv k (legendrePolynomialP n) (x : ℂ) *
      iteratedDeriv k (legendrePolynomialP n) (y : ℂ)) * hs
```
