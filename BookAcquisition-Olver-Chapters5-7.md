# Olver Chapters 5–7 acquisition ledger

All **66** entries and their distinct subclaims are audited in lookup order Mathlib,
TauCeti, DLMF. Pins: Mathlib `1b1ccf4b088b32fa3f23f2de1127433254a81e1e`, TauCeti
`396c3bd971e9722aa8656231760e710fe641d8cf`, Lean `v4.36.0-rc2`. The source synopsis,
pins and existing definition bodies are unchanged. “Existing” does not imply proved;
the transitive Lean axiom audit below distinguishes proofs, admissions and dependence on
admissions. Newly admitted statements remain in the theorem layer; defining APIs are proved.

## O-5.01 — real initial-value existence (Theorem 1.1, pp. 139–141).

New `ODE.existsUnique_secondOrder_continuous_interval` gives arbitrary open ordinary real
intervals, continuous complex coefficients and forcing, every initial jet, uniqueness and
compact-uniform Picard iteration; `ODE.secondOrderPicardIterate` is the actual two-component
iteration with proved zero/successor equations. Unbounded intervals and overlap compatibility are
retained by uniqueness. No analytic coefficient assumption replaces continuity.

Checked named coverage: 2 declarations; 1 depend on admissions.

## O-5.02 — equivalent fundamental-pair tests (Theorem 1.2, pp. 141–142).

New `ODE.fundamentalPair_iff_linearIndependent_iff_wronskian` is exactly the three
fundamental-pair tests; `ODE.wronskian_eq_exp_integral_continuous` gives the Abel factor from
every interior reference point. New `ODE.reduction_of_order_continuous` supplies the actual two
nested primitives and Wronskian for continuous complex coefficients on a zero-free first-solution
subinterval, including its initial derivative normalization. The three tests require a nonempty
interval, supplied by the interior reference.

Checked named coverage: 3 declarations; 3 depend on admissions.

## O-5.03 — real parameter dependence (Theorem 2.1, pp. 143–144).

Existing `ODE.continuousOn_parametric_linear_ode` covers joint continuity of the solution jet
under continuous coefficient and initial-data families on a compact real rectangle.
`ODE.differentiable_parametric_linear_ode` gives the parameter derivative and differentiated
inhomogeneous system under the stated continuous parameter derivatives, hence w, its first two
argument derivatives and their parameter derivatives. No analyticity in the real variable is
assumed.

Checked named coverage: 2 declarations; 2 depend on admissions.

## O-5.04 — holomorphic parameter with real argument (Theorem 2.2, p. 144).

Existing `ODE.differentiable_complex_parametric_linear_ode` gives holomorphic parameter dependence
with merely continuous real argument coefficients and holomorphic initial data. Its vector-system
realization (value, first derivative), followed by the ODE for the second derivative, covers all
three displayed solution jet components.

Checked named coverage: 1 declarations; 1 depend on admissions.

## O-5.05 — complex initial-value theorem (Theorem 3.1, pp. 145–146).

Existing `DLMF.AlgebraicAnalytic.exists_isLinearODE2SolutionOn` and
`DLMF.AlgebraicAnalytic.isLinearODE2SolutionOn_unique` supply simply-connected-domain analytic IVP
existence and uniqueness. New `Complex.existsUnique_linearSecondOrderContinuation` supplies actual
compatible solution germs along every continuous path in any ordinary domain;
`Complex.IsLinearSecondOrderContinuation.isAnalyticContinuationAlong` is a proved bridge to the
canonical TauCeti continuation predicate. Path independence is supplied only under the monodromy
hypothesis, never silently on a multiply connected domain.

Checked named coverage: 4 declarations; 1 depend on admissions.

## O-5.06 — holomorphic parameters and complex argument (Theorem 3.2, pp. 146–147).

New `Complex.exists_linearSecondOrderContinuation_param_analytic` covers jointly continuous,
separately holomorphic coefficient families, holomorphic initial jets, arbitrary fixed continuous
paths, and parameter analyticity of the carried value and first two argument derivatives. Existing
`DLMF.AlgebraicAnalytic.isLinearODE2SolutionOn_param_analytic` supplies the corresponding
single-valued branch-domain statement. The path is actual data, not an unspecified universal-cover
placeholder.

Checked named coverage: 2 declarations; 2 depend on admissions.

## O-5.07 — Taylor recursion (§3.2, p. 146).

Existing `PowerSeries.coeff_ordinary_second_order` is the exact finite convolution Taylor
recurrence. `ODE.linearOdeTaylorCoeff` is the recursively computed coefficient family, and
`ODE.exists_ball_solution_linear_ode` gives analytic solutions throughout any coefficient ball.
Expanding that analytic solution at its center and applying the coefficient recurrence gives the
source radius lower bound, including every smaller ball up to the nearest coefficient singularity.

Checked named coverage: 3 declarations; 1 depend on admissions.

## O-5.08 — singularity rank and Frobenius (Theorem 4.1, pp. 148–151).

Canonical ordinary, regular-singular and rank predicates are `Complex.LinearODEOrdinaryAt`,
`Complex.LinearODERegularSingularAt`, and `DLMF.AsymptoticApproximations.HasSingularityRank`.
Existing `DLMF.AsymptoticApproximations.indicialPoly`,
`DLMF.AsymptoticApproximations.frobeniusCoeff`,
`DLMF.AsymptoticApproximations.summable_frobeniusCoeff_of_nonresonant`,
`DLMF.AsymptoticApproximations.analyticOnNhd_frobeniusAnalyticFactor`, and
`DLMF.AsymptoticApproximations.frobeniusAnalyticFactor_isLinearODE2SolutionOn` acquire the exact
single-root recursion and whole coefficient-disc convergence.
`DLMF.AsymptoticApproximations.frobenius_solutions` gives the two-root nonresonant basis. The
exact shifted-indicial exclusions, rather than a stronger unnecessary noninteger condition on
unrelated parameters, are retained.

Checked named coverage: 9 declarations; 4 depend on admissions.

## O-5.09 — resonance (§5, pp. 151–153).

Existing `DLMF.AsymptoticApproximations.frobenius_log_solution` gives both repeated and distinct
resonant roots, convergent analytic factors, the possible zero logarithmic coefficient, and the
repeated-root nonzero normalization. New `Complex.exists_resonant_primitive` gives the exact
analytic regular primitive, finite principal part, logarithm coefficient and its equality to the
contour residue. For the reduction quotient z^(-N-1)k(z), this coefficient is k^(N)(0)/N!;
multiplication by the first Frobenius solution and `Complex.reduction_of_order_of_primitives`
gives the source residue computation, including N=0.

Checked named coverage: 3 declarations; 3 depend on admissions.

## O-5.10 — infinity and recessive solutions (§§6–7, pp. 153–155).

Existing `DLMF.AlgebraicAnalytic.isLinearODE2SolutionOn_inv` gives exactly 2/t-p(1/t)/t^2 and
q(1/t)/t^4. New `ODE.IsRecessiveAt` is the general solution-space/filter predicate, retaining
eventual nonvanishing of independent comparison solutions so totalized division cannot fake
recession at common zeros. `ODE.IsRecessiveAt.exists_smul_eq` states uniqueness up to nonzero
scale for a nontrivial approach filter. `ODE.IsNumericallySatisfactoryPair` includes the span,
independence, and recessive member at every indicated endpoint where one exists. All defining iff
APIs are proved; the endpoint domain is explicit.

Checked named coverage: 4 declarations; 1 depend on admissions.

## O-5.11 — three-singularity classification (Theorem 8.1, pp. 156–158).

New generic `Complex.eq_papperitz_coefficients_of_regularSingular` classifies the
three-marked-point regular-singular equation with the Fuchs exponent sum, including ordinary
marked points. `DLMF.Hypergeometric.coefficients_eq_gauss_of_regularSingular` is the normalized
Gauss classification. Existing Riemann coefficients/operator and
`DLMF.Hypergeometric.riemann_hypergeometric_solution_exp_log` give the actual Mobius change and
locally chosen nonvanishing analytic-log power gauge, rather than a single-valued power on an
unspecified domain. The coefficients and exponent pairs determine the equation, and fixed-path
continuation is the O-5.05 construction.

Checked named coverage: 3 declarations; 3 depend on admissions.

## O-5.12 — regularized Gauss function (§9.1, Theorem 9.1, pp. 159–160).

Canonical `DLMF.Hypergeometric.regularizedGaussHypergeometric` has the reciprocal-Gamma series and
the principal cut-plane continuation. Existing
`DLMF.Hypergeometric.differentiableOn_regularizedGaussHypergeometric_joint`,
`DLMF.Hypergeometric.differentiable_regularizedGaussHypergeometric_params`, and
`DLMF.Hypergeometric.analyticOnNhd_regularizedGaussHypergeometric_comp` give the full joint
parameter/argument analytic scope on the principal branch.
`DLMF.Hypergeometric.genContinued_parameter_entire` retains every chosen continued branch.
`DLMF.Hypergeometric.regularizedGaussHypergeometric_neg_nat` gives the exact c=-m shifted
regularized formula; the all-c equation and ordinary/regularized bridge retain reciprocal-Gamma
zeros.

Checked named coverage: 6 declarations; 1 depend on admissions.

## O-5.13 — Euler and Gauss formulas (§9.4–9.5, pp. 160–161).

Existing
`DLMF.Hypergeometric.regularizedGaussHypergeometric_eq_regularizedGaussHypergeometricIntegral`
gives the exact principal Euler integral for Re(c)>Re(b)>0, with no artificial argument
restriction to the unit disc. `DLMF.Hypergeometric.hasSum_regularizedGauss_one` gives the
regularized Gauss value for Re(c-a-b)>0 without excluding c, c-a or c-b at Gamma poles;
denominator Gamma factors are reciprocal zeros. These cover the normalization differences from
ordinary F directly.

Checked named coverage: 2 declarations; 0 depend on admissions.

## O-5.14 — derivative, Euler and Pfaff transformations (§§9–10, pp. 162–165).

Existing `DLMF.Hypergeometric.iteratedDeriv_regularizedGaussHypergeometric`,
`DLMF.Hypergeometric.regularizedGaussHypergeometric_euler`,
`DLMF.Hypergeometric.regularizedGaussHypergeometric_pfaff`, and
`DLMF.Hypergeometric.regularizedGaussHypergeometric_contiguous_c` give the derivative, Euler,
Pfaff and exact lower-parameter contiguous relation on compatible principal cuts for all
parameters. Integer c is not dropped merely because the ordinary series notation would be
inadmissible.

Checked named coverage: 4 declarations; 0 depend on admissions.

## O-5.15 — local bases and connections (§10, pp. 163–168).

The zero pair is the actual regularized Gauss function and z^(1-c) times its shifted regularized
counterpart. New `DLMF.Hypergeometric.wronskian_regularizedGauss_zero_pair` gives exactly
sin(pi*c)/pi*z^(-c)*(1-z)^(c-a-b-1); c nonintegral makes the pair independent by the
fundamental-pair theorem. Resonant bases use O-5.09.
`DLMF.Hypergeometric.regularizedGaussHypergeometric_connection_inv`,
`DLMF.Hypergeometric.regularizedGaussHypergeometric_eq_connection_inv`,
`DLMF.Hypergeometric.tendsto_connection_inv`, and their
`DLMF.Hypergeometric.regularizedGaussHypergeometric_connection_one_sub`,
`DLMF.Hypergeometric.regularizedGaussHypergeometric_eq_connection_one_sub`,
`DLMF.Hypergeometric.tendsto_connection_one_sub` counterparts provide both principal connection
formulas and the limits of the entire combined right sides. Gamma reflection converts their
normalized sums into the synopsis ordinary transformed F forms when the exponent difference is
noninteger; those differences guarantee the transformed lower parameters are admissible.
Individual divergent Gamma factors are never separately assigned finite limits.

Checked named coverage: 7 declarations; 7 depend on admissions.

## O-5.16 — generalized hypergeometric equation (§11, pp. 168–169).

Canonical generalized coefficient series and Euler-operator equation are
`DLMF.Hypergeometric.generalizedHypergeometricCoeff` and
`DLMF.Hypergeometric.generalizedHypergeometric_theta_ode`. Exact analytic/radius cases are
`DLMF.Hypergeometric.generalizedHypergeometric_entire`,
`DLMF.Hypergeometric.generalizedHypergeometric_radius_one`,
`DLMF.Hypergeometric.generalizedHypergeometric_radius_zero`, and
`DLMF.Hypergeometric.generalizedHypergeometric_diverges_nonzero`, with nontermination/lower
regularity retained. `DLMF.Hypergeometric.generalizedHypergeometric_terminating_entire` covers
terminating exceptions. New `DLMF.Hypergeometric.generalizedHypergeometricTruncated_theta_ode`
admits lower exceptional parameters occurring only beyond the finite degree: it requires
denominator Pochhammer products nonzero only through that degree. The uncancelled Euler product
has order max(p,q+1); coefficient cancellation is not hidden.

Checked named coverage: 8 declarations; 1 depend on admissions.

## O-5.17 — Clausen square (Exercise 11.1, p. 169).

Existing `DLMF.Hypergeometric.clausen_formula` gives the exact square identity on the defining
disc; `DLMF.Hypergeometric.generalizedHypergeometric_clausen_principal` gives compatible principal
continuation. Lower regularity is ordinary-series regularity, with exceptional termination treated
separately. New `ODE.product_symmetricSquare_equation` gives the full arbitrary p/q third-order
symmetric-square equation, including the 3p, 2p^2+pprime+4q, and 4pq+2qprime coefficients, over a
general nontrivially normed field.

Checked named coverage: 3 declarations; 1 depend on admissions.

## O-5.18 — associated Legendre normalizations (§12, pp. 169–171).

Canonical `DLMF.Legendre.associatedP`, `DLMF.Legendre.olverQ`, `DLMF.Legendre.associatedQ` and
`DLMF.Legendre.legendreBranchPower` preserve the source normalizations. Their definitions give the
two regularized hypergeometric expressions and the Hobson Gamma conversion on its regular locus.
`DLMF.Legendre.associatedP_reflect_degree` gives degree reflection and
`DLMF.Legendre.associated_connection_14` gives normalized-Q order symmetry.
`DLMF.Legendre.associatedP_entire_degree`, `DLMF.Legendre.associatedP_entire_order`,
`DLMF.Legendre.olverQ_entire_degree`, and `DLMF.Legendre.olverQ_entire_order` retain the entire
parameter dependence. The branch power uses log(z-1)+log(z+1), not principal sqrt(z^2-1) on the
left half-plane; whole-expression limits retain exceptional parameters.

Checked named coverage: 10 declarations; 0 depend on admissions.

## O-5.19 — endpoint forms and satisfactory pair (Theorem 12.1, pp. 171–174).

Existing `DLMF.Legendre.associated_wronskian_8` is exactly
W(P^(-mu),OlverQ^mu)=-1/(Gamma(nu+mu+1)*(z^2-1)). New
`DLMF.Legendre.tendsto_associatedP_neg_order_scaled_one`,
`DLMF.Legendre.tendsto_olverQ_scaled_cobounded`, and
`DLMF.Legendre.tendsto_olverQ_zero_order_div_log_one` give all three full complex cut-plane
endpoint coefficients, retaining zero reciprocal-Gamma coefficients as scaled limits rather than
false equivalences to zero. New `DLMF.Legendre.isNumericallySatisfactoryPair_associatedP_olverQ`
gives the exact right-half-plane complex parameter range and both endpoint approaches with the
general endpoint-basis predicate. Its solution-space span is full by the nonzero Wronskian and
connected-domain uniqueness.

Checked named coverage: 5 declarations; 4 depend on admissions.

## O-5.20 — Legendre P loops (Theorem 13.1, pp. 174–175).

New `DLMF.Legendre.SchlafliPBasedLoop` specifies the actual finite positive loop, its two
normalized logarithmic lifts, and its infinite real legs.
`DLMF.Legendre.nonempty_schlafliPBasedLoop` supplies the contour. Both source expressions are
actual finite-loop-plus-tail integrals: `DLMF.Legendre.schlafliPFirstExpression` and
`DLMF.Legendre.schlafliPSecondExpression`. `DLMF.Legendre.integrableOn_schlafliPFirstTail` and
`DLMF.Legendre.integrableOn_schlafliPSecondTail` retain their different source ranges.
`DLMF.Legendre.associatedP_eq_schlafliPFirstExpression` and
`DLMF.Legendre.associatedP_eq_schlafliPSecondExpression` give their exact factors, and
`DLMF.Legendre.tendsto_schlafliPFirstExpression` /
`DLMF.Legendre.tendsto_schlafliPSecondExpression` give whole-expression degree-pole limits. The
factor exp(-2*pi*i*mu)-1 comes from the two real legs. The displayed z=1 endpoint is acquired by
limit, not by evaluating a totalized logarithm at zero.

Checked named coverage: 10 declarations; 7 depend on admissions.

## O-5.21 — Legendre Q loop (Theorem 13.2, pp. 177–178).

New `DLMF.Legendre.SchlafliQOppositeLobes` specifies the positive right loop followed by the
negative left loop, with all three carried logarithms normalized at the interior real base point.
`DLMF.Legendre.nonempty_schlafliQOppositeLobes` supplies this actual contour.
`DLMF.Legendre.schlafliQExpression` is the whole e^(-nu*pi*i)*Gamma(-nu)/(2^(nu+2)*pi*i) times
branch-power and continued integral. `DLMF.Legendre.olverQ_eq_schlafliQExpression` identifies it
with normalized Olver Q and `DLMF.Legendre.tendsto_schlafliQExpression` acquires all
nonnegative-integral-degree removable limits. This is the arbitrary-order formula with Olver
orientation, not only a zero-order related contour.

Checked named coverage: 5 declarations; 3 depend on admissions.

## O-5.22 — Legendre recurrences (§13.3, pp. 176–177).

Existing `DLMF.Legendre.associatedP_recurrence_6` is the order-mu+2 identity,
`DLMF.Legendre.associatedP_recurrence_7` is the mixed order/degree identity with the normalized
square root, and `DLMF.Legendre.associatedP_recurrence_3` is the degree-nu+2 identity.
`DLMF.Legendre.associatedP_recurrence_4` and `DLMF.Legendre.associatedP_recurrence_5` supply the
derivative recurrences. These are parameter identities of the canonical entire P family on the
retained branch; no noninteger-order restriction is silently added.

Checked named coverage: 5 declarations; 0 depend on admissions.

## O-5.23 — integer degree/order (§14, pp. 179–183).

Existing `DLMF.Legendre.associatedP_nat_order_rodrigues`,
`DLMF.Legendre.associatedP_order_gt_degree`, and
`DLMF.Legendre.associatedP_negative_integer_order` give the integer derivative formula, vanishing
above degree, and negative-order factor. At degree n and m<=n, Gamma natural values reduce that
factor to (n-m)!/(n+m)!; the positive branch has no Ferrers (-1)^m factor.
`DLMF.Legendre.legendreQ_nat_eq_neumann_integral` gives the full complex Neumann cut, and
`DLMF.Legendre.legendreQPoly_eval_eq_convolution` /
`DLMF.Legendre.legendreQPoly_eval_eq_legendre_sum` give both actual finite W polynomial sums in
the canonical logarithmic Q decomposition. The exact logarithmic decomposition is
`DLMF.Legendre.legendreQ_nat` together with `DLMF.Legendre.legendreQ_zero` on its canonical cut;
the integer Neumann target also supplies the extension across the remaining left real ray.

Checked named coverage: 8 declarations; 3 depend on admissions.

## O-5.24 — addition theorem (Theorem 14.1, p. 183).

New `DLMF.Legendre.legendrePolynomialP_addition_sqrt_pair` is fully proved: it gives the exact
factorial-weighted finite addition polynomial for every complex argument, angle and arbitrary
paired square roots satisfying r_i^2=z_i^2-1. It is derived from the existing
`DLMF.OrthogonalPolynomials.LegendreAddition.legendre_eq_kernel`, with imaginary-rotated square
roots. Substitution of `DLMF.Legendre.associatedP_nat_order_rodrigues` gives the displayed
associated P normalization. No artificial slit restriction remains on this polynomial identity.

Checked named coverage: 3 declarations; 0 depend on admissions.

## O-5.25 — trigonometric integral (Lemma 14.1, p. 184).

New `Real.integral_inv_affine_cos_sin` gives strict positivity, interval integrability and the
exact 2*pi/sqrt(a^2-b^2-c^2) integral for every real starting angle under precisely
a>sqrt(b^2+c^2). It includes b=c=0 and fixes the positive square root.

Checked named coverage: 1 declarations; 1 depend on admissions.

## O-5.26 — Ferrers functions (§15, pp. 185–189).

Canonical `DLMF.Legendre.ferrersP` and `DLMF.Legendre.ferrersQ` give the real-interval regularized
normalizations, with the latter via integer-order parameter limits. Existing
`DLMF.Legendre.ferrersP_nat_order_rodrigues` and `DLMF.Legendre.ferrersP_negative_integer_order`
retain the Condon--Shortley (-1)^m sign. `DLMF.Legendre.ferrers_orthogonality_6` gives the degree
Kronecker-delta integral and `DLMF.Legendre.ferrers_orthogonality_8` gives the 1/(1-x^2) weighted
order integral, including the stated diagonal specialization.
`DLMF.Legendre.ferrers_connection_10` is exactly the reflection identity with cos(pi*(nu+mu)) and
-2/pi*sin(pi*(nu+mu))*Q. The traditional-Q Gamma-pole locus is retained, not confused with the
entire normalized complex Q.

Checked named coverage: 7 declarations; 0 depend on admissions.

## O-5.27 — Ferrers values and parity series (§15.2, pp. 187–188).

Existing `DLMF.Legendre.ferrersP_zero_1`, `DLMF.Legendre.ferrersP_zero_2`,
`DLMF.Legendre.ferrersQ_zero_3`, and `DLMF.Legendre.ferrersQ_zero_4` give exactly the four
displayed initial values and derivative values. `DLMF.Legendre.ferrersP_even_odd` /
`DLMF.Legendre.ferrersQ_even_odd` and `DLMF.Legendre.ferrersP_eqOn_even_odd` /
`DLMF.Legendre.ferrersQ_eqOn_even_odd` give the full normalized x^2 Gauss parity formulas. The
source derivative at zero is the coefficient of x after multiplying by the even (1-x^2)^(mu/2)
factor. `DLMF.Legendre.LegendreQRegular` excludes genuine numerator-Gamma poles for traditional Q;
reciprocal denominator-Gamma zeros are retained.

Checked named coverage: 9 declarations; 0 depend on admissions.

## O-6.01 — Liouville transform (Theorem 1.1, pp. 190–191).

Existing `DLMF.AlgebraicAnalytic.liouville_transformation` supplies the complex analytic
transformation. New `Real.iteratedDeriv_liouville_inverse` gives the full merely C3 real
inverse-coordinate formula, with the explicit Schwarzian and the amplitude |xprime|^(-1/2),
including orientation reversal. `Real.schwarzian_quotient_comp` gives the real C3 Schwarzian chain
rule. Substituting xprime=1/sqrt(f) gives exactly the source psi and W=f^(1/4)w; an
orientation-dependent square-root constant does not change the equation.

Checked named coverage: 3 declarations; 2 depend on admissions.

## O-6.02 — error-control function (§2.1, (2.01), p. 193).

New `LiouvilleGreen.RealInterval.Data.density` is precisely A*Asecond-g/sqrt(f), A=f^(-1/4), for
only C2 positive real f and continuous complex g. Its phase satisfies phaseprime=sqrt(f);
`LiouvilleGreen.RealInterval.Data.variation` is the actual absolute-density integral from any
extended-real reference, with all defining APIs proved. Thus adding a constant to a control
primitive changes no bound. Existing `Complex.IsComplexLiouvilleGreenData` gives the corresponding
analytic chosen-branch amplitude, phase and control primitive, with exactly the source derivative.

Checked named coverage: 3 declarations; 0 depend on admissions.

## O-6.03 — exponential LG bounds (Theorem 2.1, pp. 193–196).

New `LiouvilleGreen.RealInterval.Data.exists_exponential` gives both exponential solutions on any
extended-real ordinary interval, complex continuous g, the exact constants |epsilon| and
|epsilonprime|/(2*u*sqrt(f)), the actual zero endpoint limits, and real-valued solutions for real
g. Set u=1 for the displayed source formula; left and right reference choices are explicit. Only
integrability from the selected endpoint to each interior point is assumed. Existing real Volterra
proofs remain available, but no analytic regularity is substituted for the source C2 regularity.

Checked named coverage: 1 declarations; 1 depend on admissions.

## O-6.04 — oscillatory LG bounds (Theorem 2.2, p. 196).

New `LiouvilleGreen.RealInterval.Data.exists_oscillatory_pair` gives both signs, any
finite/interior/improper reference in the interval closure, only C2 positive f and continuous
complex g, the exact exp(V/u)-1 bounds on both errors and normalized derivatives, and both zero
endpoint limits. It also gives a named conjugate choice when g is real. Interior references use
the actual two-sided approach filter and two-sided reference segment. Set u=1 for Theorem2.2.

Checked named coverage: 1 declarations; 1 depend on admissions.

## O-6.05 — endpoint behavior and connection multiplier (Theorem 3.1, §3.3–3.5, pp. 198–200).

New `LiouvilleGreen.RealInterval.Data.tendsto_exponential_error_opposite` states the finite
opposite-end error limit and vanishing normalized derivative under total density integrability and
phase divergence, for the full weak real regularity. Existing
`LiouvilleGreen.Interval.eqOn_of_recessive_ratio`,
`LiouvilleGreen.Interval.eqOn_of_recessive_ratio_left`,
`LiouvilleGreen.Interval.exists_dominant_of_recessive`, and
`LiouvilleGreen.Interval.exists_dominant_of_recessive_left` give recessive uniqueness and the
complementary dominant construction in their real settings. The general solution-space uniqueness
is `ODE.IsRecessiveAt.exists_smul_eq`; adding a recessive multiple leaves the dominant
normalization unchanged, so no false dominant uniqueness is asserted.

Checked named coverage: 6 declarations; 2 depend on admissions.

## O-6.06 — convergence of the error integral (§4, pp. 200–202).

New `LiouvilleGreen.integrable_errorDensity_of_power_at_zero` and
`LiouvilleGreen.integrable_errorDensity_of_power_atTop` give both explicit differentiated-power
sufficient conditions, actual density integrability, and quantitative density/tail orders. The
phrase twice differentiable asymptotic relation is implemented by first and second derivative
order bounds, as the source pp200--201 specifies. New
`LiouvilleGreen.integrable_errorDensity_inverseSquare_split` gives exact cancellation of the -1/4
inverse-square error and local integrability of the remaining O(1/t) perturbation. Existing
`Complex.euler_equation_cpow` identifies the resulting powers 1/2 plus/minus sqrt(q0+1/4) with the
distinct indicial roots; for q0<-1/4 use the oscillatory sign with f=abs(q0+1/4)/t^2. The repeated
root is O-5.09, not an invalid exponential equivalence.

Checked named coverage: 4 declarations; 4 depend on admissions.

## O-6.07 — uniform large parameter (§5, pp. 203–206).

New `LiouvilleGreen.RealInterval.Data.exists_exponential` and
`LiouvilleGreen.RealInterval.Data.exists_oscillatory_pair` include every u>0 with exactly the
source derivative normalizers and variations V/(2u) or V/u. The new fully proved
`Real.exp_div_sub_one_le_two_div` and `Real.norm_le_inv_parameter_of_exp_control` turn bounded
total variation into a uniform O(1/u) bound on any index set, including an unbounded interval. The
fully proved `Real.eventually_norm_lt_of_exp_control` gives uniform relative o(1) from V(u)/u
tending to zero, so parameter-dependent f/g are retained by instantiation. Existing fully proved
`Complex.liouvilleGreen_doublePole_parameter_shift` gives the exact constant shift setting the
remaining double-pole numerator to -1/4; choosing its positive real square root is the displayed
effective parameter when that radicand is positive.

Checked named coverage: 6 declarations; 2 depend on admissions.

## O-6.08 — parabolic cylinder example (§6, pp. 206–208).

New `DLMF.Confluent.PositiveCylinderError.leadingFactor` uses the exact source
2^((u-1)/4)*u^(-(u+1)/4)*exp(u/4)*(1+t^2)^(-1/4)*exp(-u*pcfXiBar(t));
`DLMF.Confluent.PositiveCylinderError.error` is the actual canonical cylinder ratio.
`DLMF.Confluent.PositiveCylinderError.amplitude_mul_secondDeriv` gives the explicit
(3t^2-2)/(4*(1+t^2)^(5/2)) density.
`DLMF.Confluent.PositiveCylinderError.integrable_density_and_variation` computes the full-line
absolute integral as 4/3*sqrt(2/5)-1/6 and bounds its tail by 3/(8*t^2) for t>=1.
`DLMF.Confluent.PositiveCylinderError.norm_error_le` gives both computable error components;
`DLMF.Confluent.PositiveCylinderError.error_uniform_parameter_and_tail` gives the entire-real-line
uniform O(1/u) and fixed-u O(t^-2) conclusions.

Checked named coverage: 6 declarations; 4 depend on admissions.

## O-6.09 — integrable singular-potential extension (Theorem 7.1, pp. 209–210).

New `Real.sineMajorant` is the actual compact-interval supremum, with proved defining API;
`Real.sineMajorant_eq` supplies its sin(x)/1 piecewise value. `ODE.SingularSinePotential.control`
is the actual weighted G integral. `ODE.SingularSinePotential.exists_solution` retains a
continuous complex potential on the punctured interval, finite weighted integrals at zero, a
C1-through-zero normalized solution, the actual sine-kernel Volterra equation and sharp
sine-majorant error. `ODE.SingularSinePotential.exists_scattering_family` gives for real g=O(1/x)
near zero with an integrable tail the actual scattering amplitude/phase and uniform O(log(u)/u)
error and corrections. It fixes w(0)=0 and wprime(0)=u, rather than hiding an arbitrary amplitude
in the result.

Checked named coverage: 5 declarations; 3 depend on admissions.

## O-6.10 — zero localization (§8, pp. 211–214).

New `Real.exists_zero_sin_add_error` gives the exact arcsine phase bracket and its pi*eta/2 bound,
including zero error and a singleton bracket. `Real.existsUnique_zero_sin_add_error` gives the
source derivative criterion eta<1/sqrt(2), with within derivatives at bracket endpoints.
`Real.exists_sin_error_zero_sequence` gives exactly one zero per sufficiently late half-period
cell, every sufficiently large zero, and phase z_n=n*pi-delta+o(1). Applying these in the actual
phase coordinate, or in u times the phase coordinate, retains the phase integer and gives the
uniform parameter version from O-6.07; it is not merely an infinite-zero subsequence assertion.

Checked named coverage: 3 declarations; 3 depend on admissions.

## O-6.11 — inverse-coordinate sensitivity (Lemma 8.1, p. 214).

New `Real.exp_mul_le_of_abs_logDeriv_le` gives both stronger exponential two-sided bounds and the
exact rational corollary under K*abs(s-t)<1, for every pair of points in the interval, using only
continuous X and within-interval C1 derivatives. Positivity of X and nonnegativity of K are
explicit. This is the source inverse-coordinate sensitivity lemma, not a one-point derivative
heuristic.

Checked named coverage: 1 declarations; 1 depend on admissions.

## O-6.12 — parameter derivative of an oscillatory error (Theorem 9.1, p. 216).

New `LiouvilleGreen.CompactInterval.Data.exists_oscillatory_parameter_family` gives the actual
endpoint-normalized complex oscillatory IVP family, jointly C1 error, both usual LG bounds, and
the exact parameter derivative majorant `LiouvilleGreen.CompactInterval.Data.parameterBound`.
`LiouvilleGreen.CompactInterval.Data.integratedVariation` is the source I=integral sqrt(f)*V,
increasing on the interval, so its total variation is I itself. All real coefficient derivatives
at the finite endpoints are within the closed interval; only C2 f and continuous real g are
required. The minus family is obtained by conjugacy. The first parameter derivative estimate is
therefore acquired explicitly, not inferred from mere differentiability.

Checked named coverage: 3 declarations; 1 depend on admissions.

## O-6.13 — eigenvalue asymptotic (§9, pp. 214–217).

New `LiouvilleGreen.CompactInterval.Data.exists_dirichlet_frequency_sequence` fixes the action as
the actual integral sqrt(f), gives the real normalized Dirichlet IVP, simple characteristic roots,
all sufficiently large positive frequencies indexed by the phase integer with u_n=n*pi/c+O(1/n),
and uniform eigenfunction sine errors.
`LiouvilleGreen.CompactInterval.Data.existsUnique_dirichlet_frequency_of_threshold` retains a
computable finite half-period-cell threshold. With A=exp(V/u)-1 and B the O-6.12 majorant, it
requires A<1 and (c*A+B)/sqrt(1-A^2)<c. These factors come from differentiating the exponential
phase and arcsine correction. The synopsis instruction merely to use B<c omits them; this
correction is recorded in BookAcquisition-RevisionNotes.md, with source (9.14)--(9.15) evidence.
The original synopsis is unchanged.

Checked named coverage: 2 declarations; 2 depend on admissions.

## O-6.14 — general Volterra setup (§10.2, p. 218).

New `ODE.WeightedVolterra.Data` is the full source kernel with two path derivatives, actual zero
diagonal, positive source Pj/Q weights, forcing J, all three coefficient functions, actual
kappa/kappa0/kappa1 bounds and arc-length-weighted integrability. Its extended-real parameter
endpoints allow finite and improper oriented paths; finitely many coefficient/corner exceptions
are explicit. `ODE.WeightedVolterra.Data.variation`, `ODE.WeightedVolterra.Data.transform`, and
`ODE.WeightedVolterra.Data.iterate` are actual functions with proved defining equations. No
universal kernel estimate is assumed without its source weights.

Checked named coverage: 4 declarations; 0 depend on admissions.

## O-6.15 — Volterra existence and error (Theorem 10.1, pp. 219–220).

New `ODE.WeightedVolterra.Data.existsUnique_isSolution` gives the full kernel/derivative-coupled
Volterra construction, compact-uniform convergence of its actual iterates, the two source A*exp(B)
bounds and both normalized endpoint limits. `ODE.WeightedVolterra.Data.norm_iterate_succ_sub_le`
gives exactly kappa*Phi*(kappa0*Psi0+kappa1*Psi1)^n/n! for both iterate components. The solution
predicate includes the actual integral equation, derivative along the oriented path, and local
second regularity away from the explicit exceptional set. Uniqueness is on the path interval, so
arbitrary values outside it are not falsely fixed.

Checked named coverage: 2 declarations; 2 depend on admissions.

## O-6.16 — sharper self-forcing estimate (Theorem 10.2, p. 220).

New `ODE.WeightedVolterra.Data.norm_isSolution_le_selfForcingBound` covers the completely general
source kernel when phi=psi0 and psi1=0. `ODE.WeightedVolterra.selfForcingBound` is the actual
piecewise (kappa/kappa0)*(exp(kappa0*Phi)-1), with its exact kappa0=0 value kappa*Phi;
`ODE.WeightedVolterra.tendsto_selfForcingBound_zero` gives the continuous limiting interpretation.
For arbitrary fundamental pairs, existing `Complex.complexGreen_error_integral_and_bound` and
`Complex.exists_complexGreen_error_endpoint` retain the explicit kernel, its derivative, P0/P1/k,
actual oriented integrals, both bounds and endpoint normalization. New
`Complex.complexGreen_derivative_coupling_error` extends that specialization to differing
first-derivative coefficients and arbitrary finite initial errors.

Checked named coverage: 6 declarations; 5 depend on admissions.

## O-6.17 — complex LG (Theorem 11.1, p. 222).

Existing `Complex.IsComplexLiouvilleGreenData`, `Complex.exists_complexLiouvilleGreenData`,
`Complex.exists_complexLiouvilleGreen_finite_reference`, and
`Complex.exists_complexLiouvilleGreen_endpoint_reference` give actual chosen-branch analytic LG
solutions and progressive finite/infinite path bounds on a simply connected branch domain. New
`Complex.IsLiouvilleGreenContinuation` represents actual compatible analytic
fourth-root/phase/control germs along any path, using the canonical TauCeti continuation
predicate. `Complex.exists_liouvilleGreenContinuation`,
`Complex.exists_liouvilleGreenContinuation_error`, and
`Complex.exists_liouvilleGreenContinuation_endpoint_error` give the finite/improper progressive
estimates on these continued branches in a multiply connected original domain. The control
variation follows the carried germs, and the actual monotonicity of the carried phase is a
hypothesis; no global single-valued square root or unmodelled cover is substituted.

Checked named coverage: 8 declarations; 6 depend on admissions.

## O-6.18 — complex endpoint multiplier (Theorem 12.1, pp. 223–224).

Existing `Complex.exists_complexLiouvilleGreen_connection_multiplier` gives exactly the two
oppositely normalized solutions, equality of their opposite-end relative-error limits, vanishing
normalized derivatives and the (exp(total variation/abs(u))-1)/2 bound. The branch domain is
explicit, and its progressive path retains the actual common initial tail. The equality is a
Wronskian connection equality, not equality of the two solutions. Continued branch transfer is the
actual germ construction of O-6.17.

Checked named coverage: 1 declarations; 1 depend on admissions.

## O-6.19 — variation along a line (Lemma 13.1, p. 225).

New `Complex.eVariationOn_exp_neg_mul_lift_line` gives the actual full doubly infinite line
variation 2*chi(alpha)*d^(-alpha), with `Complex.powerVariationConstant` the displayed Gamma
quotient and a continuous logarithmic lift of the line. `Complex.progressivePowerVariationCosts`
is the actual cost set of finite progressive right-half-plane paths to a positive R plus its
R^(-alpha) ray tail. `Complex.csInf_progressivePowerVariationCosts` proves nonemptiness,
boundedness, exact infimum abs(z)^(-alpha), and epsilon-approximation. It does not misstate an
infimum as a finite-path minimum.

Checked named coverage: 4 declarations; 2 depend on admissions.

## O-7.01 — rank-one formal solutions (§§1–2, pp. 229–232).

Existing `DLMF.AsymptoticApproximations.IsRankOneAtInfinity`,
`DLMF.AsymptoticApproximations.rankOneExponent`, and `DLMF.AsymptoticApproximations.rankOneCoeff`
are the actual distinct-root Laurent data, exact mu, and normalized finite coefficient recursion.
New `DLMF.AsymptoticApproximations.RankOne.rankOneCoeff_formal_operator_eq_and_unique` identifies
these with the unique constant-one formal solution of the fully conjugated operator. Its
coefficient extraction is actual finite arithmetic via
`DLMF.AsymptoticApproximations.RankOneForcing.operatorCoefficient`, not evaluation of a divergent
series. The denominator pc0+2*lambda is explicitly nonzero.

Checked named coverage: 5 declarations; 1 depend on admissions.

## O-7.02 — canonical solutions (Theorem 2.1, pp. 232–234).

New `DLMF.AsymptoticApproximations.RankOne.exists_unique_differentiated_solutions` uses literal
exp(lambda*z)*z^mu, with no extra constant from the sector-orienting log(lambda2-lambda1). It
gives actual analytic logarithmic-plane solutions, both all-orders expansions, first two
differentiated remainder estimates, and uniqueness on the whole stated sectors. Restricting the
widened sectors gives the source canonical pi-half-angle sectors and all closed subsectors.
Existing `DLMF.AsymptoticApproximations.rankOne_exists_unique_solutions` uses a different constant
power normalization, which is related by the explicit constant exp(-mu*log(lambda2-lambda1)); it
is not silently treated as the literal source normalization.

Checked named coverage: 2 declarations; 2 depend on admissions.

## O-7.03 — enlarged sectors (Theorem 2.2, p. 235).

New `DLMF.AsymptoticApproximations.RankOne.canonicalSector` retains the actual unwrapped first and
second sectors of opening 3*pi-2*delta on one common logarithmic plane.
`DLMF.AsymptoticApproximations.RankOne.exists_unique_differentiated_solutions` includes both
function expansions and differentiated remainders there. No boundary ray at the full 3*pi opening
is included. The derivative remainder uses exp(j*w) times the Nth scale, so it remains meaningful
when a characteristic root is zero and its formal leading derivative vanishes.

Checked named coverage: 2 declarations; 1 depend on admissions.

## O-7.04 — analytic parameter dependence (Theorem 3.1, pp. 236–237).

New `DLMF.AsymptoticApproximations.RankOne.ParameterData` fixes distinct characteristic roots and
leading coefficients, holomorphic parameter Laurent coefficients and actual convergent common
geometric majorants on every compact parameter set.
`DLMF.AsymptoticApproximations.RankOne.ParameterData.analyticOnNhd_exponent_coeff` gives
holomorphic mu and every finite recursive coefficient.
`DLMF.AsymptoticApproximations.RankOne.ParameterData.exists_analytic_canonical_family` gives
locally joint analytic canonical solutions on the full lifted exterior, analytic first two
argument derivatives and locally uniform differentiated asymptotic remainders with the actual
varying exponent and any holomorphic initial multiplier, including its zeros. This is
normalization at infinity, not only finite-IVP parameter dependence.

Checked named coverage: 3 declarations; 2 depend on admissions.

## O-7.05 — coincident characteristic roots (§4, pp. 237–238).

Existing `DLMF.AsymptoticApproximations.fabry_transformation` is the exact change
W(t)=exp(pc0*t^2/2)*w(t^2), with both actual transformed coefficients and the necessary t nonzero
hypothesis. `DLMF.AsymptoticApproximations.fabry_coefficients` gives their convergent even
inverse-power Laurent expansions and the characteristic dichotomy. Since t maps to t^2, choosing a
logarithmic branch amounts to t=exp(w/2); this is the actual ramified cover, without independently
principalizing a square root. If qc1=pc0*pc1/2 the transformed equation has regular-singular
infinity; otherwise its characteristic roots are plus/minus sqrt(2*pc0*pc1-4*qc1). Substitution of
the existing rank-one recursion then gives the source half-power formal expansion; convergence of
that formal expansion is not claimed.

Checked named coverage: 2 declarations; 0 depend on admissions.

## O-7.06 — cylinder functions and normalization (§§5–6, pp. 238–244).

Canonical `DLMF.Bessel.besselYOnLog`, `DLMF.Bessel.hankelH1OnLog`, and `DLMF.Bessel.hankelH2OnLog`
retain the removable integer-order normalization. New `DLMF.Bessel.analyticOnNhd_cylinderOnLog`,
`DLMF.Bessel.cylinderOnLog_recurrences`, and `DLMF.Bessel.cylinderOnLog_ode` give joint entire
order/log-coordinate dependence, both recurrence/derivative identities for J/Y/H1/H2, and the
actual lifted differential equation. Existing `DLMF.Bessel.wronskian_besselJ_besselY` and
`DLMF.Bessel.wronskian_hankelH1_hankelH2` give 2/(pi*z) and -4*i/(pi*z) on a branch; analytic
continuation gives every carried branch. No nonintegral-order restriction remains.

Checked named coverage: 8 declarations; 3 depend on admissions.

## O-7.07 — Hankel expansions (§5, pp. 239–241).

Existing `DLMF.Bessel.largeArgumentCoefficient` is the exact product a_k;
`DLMF.Bessel.hasAsymptoticExpansion_hankelH1OnLog` and
`DLMF.Bessel.hasAsymptoticExpansion_hankelH2OnLog` give both full 3*pi lifted sectors.
`DLMF.Bessel.isBigO_besselJOnLog_remainder` / `DLMF.Bessel.isBigO_besselYOnLog_remainder` retain
both exponential absolute remainder scales, including near trigonometric zeros. New
`DLMF.Bessel.isBigO_hankelOnLog_derivative_remainder` gives the first derivative expansion with
the actual `DLMF.Bessel.hankelOnLogPartialSum`. Principal bridges are the existing OnLog/log
lemmas; no argument is independently reduced modulo 2*pi.

Checked named coverage: 7 declarations; 5 depend on admissions.

## O-7.08 — zeros and their simplicity (Theorem 6.1, pp. 244–245).

Existing `DLMF.Bessel.deriv_ne_zero_of_bessel_solution_eq_zero` and
`DLMF.Bessel.iteratedDeriv_two_ne_zero_of_bessel_solution_deriv_eq_zero` state the generic
analytic-solution zero and derivative-zero simplicity assertions on a connected open branch
domain. Nontriviality and exclusion of the origin are explicit; derivative simplicity excludes
precisely z^2=nu^2. These are already general in complex order and therefore cover the source
real-order assertions without duplicate targets.

Checked named coverage: 2 declarations; 2 depend on admissions.

## O-7.09 — reality and exclusion near the origin (Theorem 6.2 and Lemma 6.1, pp. 245–246).

Existing `DLMF.Bessel.im_eq_zero_of_besselJ_eq_zero` gives reality of nonzero J zeros for real
nu>-1; `Complex.besselJ_neg_int` reduces nu=-1 to nu=1.
`DLMF.Bessel.im_eq_zero_of_diniNormalized_eq_zero`, with the zero Robin coefficient, gives
derivative reality for nu>=0 after its normalized derivative bridge.
`DLMF.Bessel.existsUnique_imaginary_deriv_besselJ_zero` gives exactly the imaginary pair for
-1<nu<0. `DLMF.Bessel.exists_uniform_besselJ_ne_zero` and
`DLMF.Bessel.exists_uniform_deriv_besselJ_ne_zero` give the source uniform-in-order neighborhoods,
including all positive orders above the chosen margin. A leading reciprocal-Gamma zero at a
negative integer is not used as a false nonvanishing argument.

Checked named coverage: 6 declarations; 5 depend on admissions.

## O-7.10 — parameterized zeros (Theorems 6.3–6.4, p. 246).

Existing `DLMF.Bessel.exists_positive_besselJ_zero_family` gives complete increasing positive-zero
enumerations, C1 dependence and strict order monotonicity throughout nu>-1.
`DLMF.Bessel.exists_positive_deriv_besselJ_zero_family` gives derivative-zero C1 dependence on
nu>0 and the first-zero bound >nu. `DLMF.Bessel.besselJ_deriv_positive_zeros_interlace` gives the
exact complete indexed chain. These enumerate every positive zero, so a shifted subsequence cannot
satisfy the source indexing.

Checked named coverage: 3 declarations; 3 depend on admissions.

## O-7.11 — McMahon expansion of large zeros (§6, pp. 246–248).

New `DLMF.Bessel.hankelCosineSeries`, `DLMF.Bessel.hankelSineSeries`,
`DLMF.Bessel.besselZeroPhaseSeries`, and `DLMF.Bessel.besselZeroCorrectionSeries` give the actual
formal tangent/phase reversion algorithm. `DLMF.Bessel.coeff_besselZeroCorrectionSeries_le_three`
gives exactly both displayed corrections and the zero even coefficients through degree three.
`DLMF.Bessel.Real.hasAsymptoticPowerSeries_besselJ_positive_zeros` gives the full all-orders
correction for complete J indexing, nu>-1.
`DLMF.Bessel.Real.hasAsymptoticPowerSeries_besselY_positive_zeros` gives the full Y correction and
complete indexing for nu>-1/2, the connected component continued from nu=1/2 used in the source
pp248--249. At nu=-1/2 a zero reaches zero and the complete-positive enumeration shifts; unchanged
indexing is not extended across that event. Existing finite McMahon targets are special cases.

Checked named coverage: 7 declarations; 3 depend on admissions.

## O-7.12 — separation of cylinder zeros (Theorems 7.1–7.2, pp. 248–249).

Existing `DLMF.Bessel.existsUnique_cylinder_zero_between` gives arbitrary independent real
cylinder-function interlacing. `DLMF.Bessel.exists_positive_besselY_zero_family` gives complete C1
and order-increasing Y zeros for nu>-1/2; `DLMF.Bessel.besselY_besselJ_positive_zeros_interlace`
gives their exact indexed chain. Upstream `TauCeti.argumentPrinciple_windingNumber` gives the
meromorphic argument principle as the winding-number weighted sum of zero/pole orders;
`TauCeti.argumentPrinciple_windingNumber_of_analyticOnNhd` is its analytic specialization. For a
positive simple contour, inside winding is one and outside zero, so this is exactly
change-of-argument/(2*pi)=number of zeros minus poles with multiplicity.

Checked named coverage: 5 declarations; 3 depend on admissions.

## O-7.13 — modified cylinder functions (§8, pp. 250–253).

Canonical lifted I/K functions have the removable integer-order definitions. New
`DLMF.Bessel.besselIOnLog_eq_besselJOnLog`, `DLMF.Bessel.modifiedCylinderOnLog_recurrences`, and
`DLMF.Bessel.cylinderOnLog_ode` give the exact correlated rotation, shifts/derivatives and
modified equation. Existing `DLMF.Bessel.besselK_neg`, `DLMF.Bessel.wronskian_besselK_besselI`,
and `DLMF.Bessel.besselK_eq_integral_cosh` give symmetry, 1/z Wronskian and the all-complex-order
integral for Re(z)>0. Existing `DLMF.Bessel.hasAsymptoticExpansion_besselKOnLog` and
`DLMF.Bessel.hasAsymptoticExpansion_besselIOnLog` give the full required lifted sectors. New
`DLMF.Bessel.besselIOnLog_eq_besselKOnLog_connection`, `DLMF.Bessel.besselKOnLog_add_int_mul_pi`,
and `DLMF.Bessel.isBigO_besselIOnLog_two_exponentials` give the exact upper/lower continued
connection, integer-order-safe Chebyshev sine quotient, and full two-exponential I remainder.
Principal reevaluation after a half-turn is not substituted for continuation.

Checked named coverage: 11 declarations; 8 depend on admissions.

## O-7.14 — modified monotonicity and zeros (Theorems 8.1–8.2, pp. 251–252).

Existing `DLMF.Bessel.besselI_ofReal_pos` and `DLMF.Bessel.besselK_ofReal_pos` give positivity.
`DLMF.Bessel.Real.strictMonoOn_re_besselI`, `DLMF.Bessel.Real.strictAntiOn_re_besselK`,
`DLMF.Bessel.Real.strictAntiOn_re_besselI_order`, and
`DLMF.Bessel.Real.strictMonoOn_re_besselK_order` give both argument and order monotonicities.
`DLMF.Bessel.besselK_ne_zero_of_nonneg_re` retains the closed half-plane, including nonzero
imaginary-axis boundary. `DLMF.Bessel.besselK_isEquivalent_cpow_nhds_zero` and
`DLMF.Bessel.besselK_zero_isEquivalent_neg_log_nhds_zero` give both cut-sector small-argument
forms. Their order and branch restrictions match the source; real-only positivity is not used to
imply complex nonvanishing.

Checked named coverage: 9 declarations; 7 depend on admissions.

## O-7.15 — confluent hypergeometric functions (§9, pp. 254–258).

Canonical `DLMF.Confluent.kummerM` is ordinary M and Mathlib `Complex.regularizedHGFun` is the
distinct reciprocal-Gamma regularization. Existing `DLMF.Confluent.hasFPowerSeriesOnBall_kummerM`,
`DLMF.Confluent.kummerM_ode`, `DLMF.Confluent.kummerM_eq_euler_integral`,
`DLMF.Confluent.kummerM_kummer_transform`, and `DLMF.Confluent.kummerU_kummer_transform_all` give
the series, equation, Euler integral and transformations on their exact domains. New
`DLMF.Confluent.differentiable_regularizedKummer_parameters_argument` gives full joint entire
dependence in (a,c,z), including exceptional c. Existing
`DLMF.Confluent.wronskian_regularizedHGFun` gives precisely sin(pi*c)/pi*exp(z)*z^(-c) for the
regularized local pair; no ordinary Gamma factor is lost.

Checked named coverage: 9 declarations; 1 depend on admissions.

## O-7.16 — Tricomi solution and exact connections (§9, pp. 255–258).

Existing `DLMF.Confluent.kummerU_laplace`, `DLMF.Confluent.kummerU_eq_connection`, and the
canonical integer-parameter limiting definition give the normalized Tricomi integral and entire
parameter limits. `DLMF.Confluent.regularizedHGFun_eq_kummerU_connection` has upper sign=false
(positive displayed phases, rotated argument through the lower half-plane) and lower sign=true
(reversed phases and rotated argument through the upper half-plane). New
`DLMF.Confluent.regularizedConfluent_eq_tricomi_continued` continues both exact identities on the
entire logarithmic plane with the correlated w plus/minus pi*i shift. Existing
`DLMF.Confluent.wronskian_regularizedHGFun_kummerU_all` gives W(Mtilde,U)=-exp(z)*z^(-c)/Gamma(a);
swapping the Wronskian gives exactly the source W(U,Mtilde) with positive sign. All
reciprocal-Gamma zeros are retained.

Checked named coverage: 5 declarations; 1 depend on admissions.

## O-7.17 — confluent asymptotics and specializations (§§9–10, pp. 257–262).

Existing full `DLMF.Confluent.kummerUContinuedOnLog` and
`DLMF.Confluent.hasAsymptoticExpansion_kummerUContinuedOnLog` acquire the entire 3*pi-minus-margin
wound Tricomi sector, with integer second parameter defined by a whole limit. New
`DLMF.Confluent.isBigO_regularizedConfluentOnLog_two_exponentials` gives both upper/lower lifted M
expansions of opening 2*pi-minus-margin with both absolute scales, including vanishing
reciprocal-Gamma coefficients. Exact reductions are `DLMF.Confluent.kummerU_besselK`, the defining
equation of `DLMF.Confluent.upperIncompleteGamma`, the fully proved
`DLMF.Confluent.kummerU_eq_laguerreExtended`, and new
`DLMF.Confluent.parabolicCylinderU_eq_kummerUContinuedOnLog` with its actual correlated 2*w-log(2)
argument. Existing `DLMF.Confluent.whittakerWContinuedOnLog` and
`DLMF.Confluent.hasAsymptoticExpansion_whittakerWContinuedOnLog` retain the whole wound Whittaker
sector; canonical Whittaker definitions/equations preserve ordinary versus regularized M and its
exceptional lower parameters. Large-parameter LG follows by applying O-6.07 only after verifying
the displayed Whittaker coefficient is zero-free on the selected progressive domain.

Checked named coverage: 9 declarations; 4 depend on admissions.

## O-7.18 — computable residual error (Theorem 12.1, pp. 265–270).

New `DLMF.AsymptoticApproximations.RankOneComparison.shift`,
`DLMF.AsymptoticApproximations.RankOneComparison.comparisonFunction`,
`DLMF.AsymptoticApproximations.RankOneComparison.coefficientP`,
`DLMF.AsymptoticApproximations.RankOneComparison.coefficientQ`,
`DLMF.AsymptoticApproximations.RankOneComparison.truncation`, and
`DLMF.AsymptoticApproximations.RankOneComparison.residual` are the exact computable source
expressions, with proved defining APIs.
`DLMF.AsymptoticApproximations.RankOneComparison.comparison_pair_equations` gives the actual
nowhere-zero Wronskian (lambda2-lambda1)*exp(-pc0*z-pc1*Log(z)), P0=-Wprime/W, and both comparison
equations outside the shift circle on any actual analytic logarithm branch. New
`Complex.complexGreen_derivative_coupling_error` gives the complete derivative-coupled residual
Green equation, derivative equation, arbitrary finite initial errors and explicit A/B absolute
bounds. `Complex.exists_complexGreen_derivative_coupling_endpoint` gives the actual absolutely
convergent initial-tail correction with both zero normalized endpoint errors and the same bounds.
The broader progressive kernel weighting is `ODE.WeightedVolterra.Data.existsUnique_isSolution`;
choose phi=-R_N, psi0=-(q-Q0), psi1=-(p-P0). Thus nonconvergent coefficient asymptotics are
allowed whenever those actual kernel variations converge; no unknown O constant replaces the
displayed computation.

Checked named coverage: 10 declarations; 4 depend on admissions.

## O-7.19 — inhomogeneous formal series (Theorem 14.1, pp. 274–276).

New `DLMF.AsymptoticApproximations.RankOneForcing.coefficient` is the actual forced Laurent
recursion with a0=r0/q0. `DLMF.AsymptoticApproximations.RankOneForcing.operatorCoefficient`
explicitly extracts every coefficient of the conjugated differential operator by finite sums.
`DLMF.AsymptoticApproximations.RankOneForcing.coefficient_operator_eq_and_unique` gives formal
correctness and uniqueness under q0 nonzero.
`DLMF.AsymptoticApproximations.RankOneForcing.exists_finite_sectorial_expansion` gives an actual
analytic inhomogeneous logarithmic-plane solution with every prescribed finite truncation and its
O(exp((alpha-N)*w)) remainder on the simultaneous root/difference progressive sectors. All four
constant logarithms are supplied with their actual exponential values, allowing arbitrary
compatible unwrapped phases. The solution may depend on N and the sector, exactly as the source
requires; it is not falsely promoted to a global all-orders particular solution.

Checked named coverage: 4 declarations; 2 depend on admissions.

## O-7.20 — Struve functions (§15, pp. 276–278).

Canonical `DLMF.Struve.struveH` is the reciprocal-Gamma series and `DLMF.Struve.struveK` is H-Y,
distinct from modified Bessel K. Existing `DLMF.Struve.struveH_ode`,
`DLMF.Struve.struveH_eq_poisson`, and `DLMF.Struve.struveK_laplace` give the inhomogeneous
equation, sin-Poisson integral and exact Laplace kernel. The K Laplace target is already valid for
every complex order and Re(z)>0; no unnecessary Re(nu)>-1/2 restriction is added there.
`DLMF.Struve.struveK_asymptotic_rotSector` and `DLMF.Struve.struveK_asymptotic` give the full
coefficient series with both rotated and combined |arg(z)|<pi sectors, and the existing
signed-remainder bound controls the first omitted term on the stated real range. These are exact
source normalizations, not only a generic Watson lemma.

Checked named coverage: 7 declarations; 0 depend on admissions.

## Validation

All 66 entries are mapped. The transitive `#print axioms` audit checked **382** distinct
declarations; **144** depend on admissions. The **32** new modules
owned by this supplement contain **203** public declarations, including
**83** directly admitted targets. Definitions and their
defining equations have no admissions. Every new module has passed a direct strict Lean check
with `autoImplicit=false` and `relaxedAutoImplicit=false`; modules are registered in their
area umbrellas. Repository-wide build and import integration are coordinated with the other
book acquisitions and reported separately.

The per-entry declaration locations and proof statuses are retained in
[reports/BookAcquisition-Olver-Chapters5-7.tsv](reports/BookAcquisition-Olver-Chapters5-7.tsv).
Source statement qualifications are recorded in
[BookAcquisition-RevisionNotes.md](BookAcquisition-RevisionNotes.md); the SYNOPSIS file is unchanged.

## Checked declaration index

- [Complex.IsComplexLiouvilleGreenData](DLMFMathlib/Analysis/ODE/ComplexLiouvilleGreen.lean#L36) — definition, no admission.
- [Complex.IsLinearSecondOrderContinuation](DLMFMathlib/Analysis/ODE/LinearODEContinuation.lean#L33) — definition, no admission.
- [Complex.IsLinearSecondOrderContinuation.isAnalyticContinuationAlong](DLMFMathlib/Analysis/ODE/LinearODEContinuation.lean#L53) — proved, no admission.
- [Complex.IsLiouvilleGreenContinuation](DLMFMathlib/Analysis/ODE/LiouvilleGreenContinuation.lean#L31) — definition, no admission.
- [Complex.LinearODEOrdinaryAt](DLMFMathlib/Analysis/ODE/Singularities.lean#L51) — definition, no admission.
- [Complex.LinearODERegularSingularAt](DLMFMathlib/Analysis/ODE/Singularities.lean#L60) — definition, no admission.
- [Complex.besselJ_neg_int](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Bessel.lean#L84) — proved, no admission.
- [Complex.complexGreen_derivative_coupling_error](DLMFMathlib/Analysis/ODE/ComplexGreenDerivativeCoupling.lean#L29) — direct admission.
- [Complex.complexGreen_error_integral_and_bound](DLMFMathlib/Analysis/ODE/ComplexGreenEquation.lean#L33) — direct admission.
- [Complex.csInf_progressivePowerVariationCosts](DLMFMathlib/Analysis/Complex/PowerVariation.lean#L73) — direct admission.
- [Complex.eVariationOn_exp_neg_mul_lift_line](DLMFMathlib/Analysis/Complex/PowerVariation.lean#L43) — direct admission.
- [Complex.eq_papperitz_coefficients_of_regularSingular](DLMFMathlib/Analysis/ODE/FuchsianClassification.lean#L191) — direct admission.
- [Complex.euler_equation_cpow](DLMFMathlib/Analysis/ODE/EulerEquation.lean#L34) — direct admission.
- [Complex.existsUnique_linearSecondOrderContinuation](DLMFMathlib/Analysis/ODE/LinearODEContinuation.lean#L65) — direct admission.
- [Complex.exists_complexGreen_derivative_coupling_endpoint](DLMFMathlib/Analysis/ODE/ComplexGreenDerivativeCoupling.lean#L60) — direct admission.
- [Complex.exists_complexGreen_error_endpoint](DLMFMathlib/Analysis/ODE/ComplexGreenEquation.lean#L66) — direct admission.
- [Complex.exists_complexLiouvilleGreenData](DLMFMathlib/Analysis/ODE/ComplexLiouvilleGreen.lean#L75) — direct admission.
- [Complex.exists_complexLiouvilleGreen_connection_multiplier](DLMFMathlib/Analysis/ODE/ComplexLiouvilleGreen.lean#L140) — direct admission.
- [Complex.exists_complexLiouvilleGreen_endpoint_reference](DLMFMathlib/Analysis/ODE/ComplexLiouvilleGreen.lean#L108) — direct admission.
- [Complex.exists_complexLiouvilleGreen_finite_reference](DLMFMathlib/Analysis/ODE/ComplexLiouvilleGreen.lean#L87) — direct admission.
- [Complex.exists_linearSecondOrderContinuation_param_analytic](DLMFMathlib/Analysis/ODE/LinearODEContinuation.lean#L79) — direct admission.
- [Complex.exists_liouvilleGreenContinuation](DLMFMathlib/Analysis/ODE/LiouvilleGreenContinuation.lean#L56) — direct admission.
- [Complex.exists_liouvilleGreenContinuation_endpoint_error](DLMFMathlib/Analysis/ODE/LiouvilleGreenContinuation.lean#L94) — direct admission.
- [Complex.exists_liouvilleGreenContinuation_error](DLMFMathlib/Analysis/ODE/LiouvilleGreenContinuation.lean#L70) — direct admission.
- [Complex.exists_resonant_primitive](DLMFMathlib/Analysis/Complex/ResonantPrimitive.lean#L35) — direct admission.
- [Complex.isLinearSecondOrderContinuation_iff](DLMFMathlib/Analysis/ODE/LinearODEContinuation.lean#L42) — proved, no admission.
- [Complex.isLiouvilleGreenContinuation_iff](DLMFMathlib/Analysis/ODE/LiouvilleGreenContinuation.lean#L42) — proved, no admission.
- [Complex.liouvilleGreen_doublePole_parameter_shift](DLMFMathlib/Analysis/ODE/LiouvilleGreenSingularCoefficients.lean#L115) — proved, no admission.
- [Complex.mem_progressivePowerVariationCosts_iff](DLMFMathlib/Analysis/Complex/PowerVariation.lean#L61) — proved, no admission.
- [Complex.powerVariationConstant](DLMFMathlib/Analysis/Complex/PowerVariation.lean#L32) — definition, no admission.
- [Complex.powerVariationConstant_def](DLMFMathlib/Analysis/Complex/PowerVariation.lean#L36) — proved, no admission.
- [Complex.progressivePowerVariationCosts](DLMFMathlib/Analysis/Complex/PowerVariation.lean#L53) — definition, no admission.
- [Complex.reduction_of_order_of_primitives](DLMFMathlib/Analysis/ODE/ReductionOfOrder.lean#L32) — direct admission.
- [Complex.regularizedHGFun](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/RegularizedHypergeometric.lean#L192) — definition, no admission.
- [DLMF.AlgebraicAnalytic.exists_isLinearODE2SolutionOn](DLMF/AlgebraicAnalytic/ODE/SecondOrder.lean#L171) — proved, no admission.
- [DLMF.AlgebraicAnalytic.isLinearODE2SolutionOn_inv](DLMF/AlgebraicAnalytic/ODE/Transformations.lean#L61) — proved, no admission.
- [DLMF.AlgebraicAnalytic.isLinearODE2SolutionOn_param_analytic](DLMF/AlgebraicAnalytic/ODE/SecondOrder.lean#L414) — direct admission.
- [DLMF.AlgebraicAnalytic.isLinearODE2SolutionOn_unique](DLMF/AlgebraicAnalytic/ODE/SecondOrder.lean#L219) — proved, no admission.
- [DLMF.AlgebraicAnalytic.liouville_transformation](DLMF/AlgebraicAnalytic/ODE/Transformations.lean#L182) — proved, no admission.
- [DLMF.AsymptoticApproximations.HasSingularityRank](DLMF/AsymptoticApproximations/ODE/Basic.lean#L95) — definition, no admission.
- [DLMF.AsymptoticApproximations.IsRankOneAtInfinity](DLMF/AsymptoticApproximations/ODE/Basic.lean#L240) — definition, no admission.
- [DLMF.AsymptoticApproximations.RankOne.ParameterData](DLMF/AsymptoticApproximations/ODE/RankOneParameterDependence.lean#L67) — definition, no admission.
- [DLMF.AsymptoticApproximations.RankOne.ParameterData.analyticOnNhd_exponent_coeff](DLMF/AsymptoticApproximations/ODE/RankOneParameterDependence.lean#L95) — direct admission.
- [DLMF.AsymptoticApproximations.RankOne.ParameterData.exists_analytic_canonical_family](DLMF/AsymptoticApproximations/ODE/RankOneParameterDependence.lean#L108) — direct admission.
- [DLMF.AsymptoticApproximations.RankOne.canonicalSector](DLMF/AsymptoticApproximations/ODE/RankOneParameterDependence.lean#L29) — definition, no admission.
- [DLMF.AsymptoticApproximations.RankOne.canonicalSector_def](DLMF/AsymptoticApproximations/ODE/RankOneParameterDependence.lean#L34) — proved, no admission.
- [DLMF.AsymptoticApproximations.RankOne.exists_unique_differentiated_solutions](DLMF/AsymptoticApproximations/ODE/RankOneParameterDependence.lean#L44) — direct admission.
- [DLMF.AsymptoticApproximations.RankOne.rankOneCoeff_formal_operator_eq_and_unique](DLMF/AsymptoticApproximations/ODE/RankOneFormalOperator.lean#L26) — direct admission.
- [DLMF.AsymptoticApproximations.RankOneComparison.coefficientP](DLMF/AsymptoticApproximations/ODE/RankOneComparison.lean#L48) — definition, no admission.
- [DLMF.AsymptoticApproximations.RankOneComparison.coefficientP_def](DLMF/AsymptoticApproximations/ODE/RankOneComparison.lean#L51) — proved, no admission.
- [DLMF.AsymptoticApproximations.RankOneComparison.coefficientQ](DLMF/AsymptoticApproximations/ODE/RankOneComparison.lean#L55) — definition, no admission.
- [DLMF.AsymptoticApproximations.RankOneComparison.coefficientQ_def](DLMF/AsymptoticApproximations/ODE/RankOneComparison.lean#L61) — proved, no admission.
- [DLMF.AsymptoticApproximations.RankOneComparison.comparisonFunction](DLMF/AsymptoticApproximations/ODE/RankOneComparison.lean#L39) — definition, no admission.
- [DLMF.AsymptoticApproximations.RankOneComparison.comparisonFunction_def](DLMF/AsymptoticApproximations/ODE/RankOneComparison.lean#L43) — proved, no admission.
- [DLMF.AsymptoticApproximations.RankOneComparison.comparison_pair_equations](DLMF/AsymptoticApproximations/ODE/RankOneComparison.lean#L89) — direct admission.
- [DLMF.AsymptoticApproximations.RankOneComparison.residual](DLMF/AsymptoticApproximations/ODE/RankOneComparison.lean#L78) — definition, no admission.
- [DLMF.AsymptoticApproximations.RankOneComparison.residual_def](DLMF/AsymptoticApproximations/ODE/RankOneComparison.lean#L82) — proved, no admission.
- [DLMF.AsymptoticApproximations.RankOneComparison.shift](DLMF/AsymptoticApproximations/ODE/RankOneComparison.lean#L30) — definition, no admission.
- [DLMF.AsymptoticApproximations.RankOneComparison.shift_def](DLMF/AsymptoticApproximations/ODE/RankOneComparison.lean#L34) — proved, no admission.
- [DLMF.AsymptoticApproximations.RankOneComparison.truncation](DLMF/AsymptoticApproximations/ODE/RankOneComparison.lean#L68) — definition, no admission.
- [DLMF.AsymptoticApproximations.RankOneComparison.truncation_def](DLMF/AsymptoticApproximations/ODE/RankOneComparison.lean#L73) — proved, no admission.
- [DLMF.AsymptoticApproximations.RankOneForcing.coefficient](DLMF/AsymptoticApproximations/ODE/RankOneForcing.lean#L27) — definition, no admission.
- [DLMF.AsymptoticApproximations.RankOneForcing.coefficient_operator_eq_and_unique](DLMF/AsymptoticApproximations/ODE/RankOneForcing.lean#L72) — direct admission.
- [DLMF.AsymptoticApproximations.RankOneForcing.coefficient_succ](DLMF/AsymptoticApproximations/ODE/RankOneForcing.lean#L45) — proved, no admission.
- [DLMF.AsymptoticApproximations.RankOneForcing.coefficient_zero](DLMF/AsymptoticApproximations/ODE/RankOneForcing.lean#L39) — proved, no admission.
- [DLMF.AsymptoticApproximations.RankOneForcing.exists_finite_sectorial_expansion](DLMF/AsymptoticApproximations/ODE/RankOneForcing.lean#L82) — direct admission.
- [DLMF.AsymptoticApproximations.RankOneForcing.operatorCoefficient](DLMF/AsymptoticApproximations/ODE/RankOneForcing.lean#L57) — definition, no admission.
- [DLMF.AsymptoticApproximations.RankOneForcing.operatorCoefficient_def](DLMF/AsymptoticApproximations/ODE/RankOneForcing.lean#L63) — proved, no admission.
- [DLMF.AsymptoticApproximations.analyticOnNhd_frobeniusAnalyticFactor](DLMF/AsymptoticApproximations/ODE/Frobenius.lean#L65) — direct admission.
- [DLMF.AsymptoticApproximations.fabry_coefficients](DLMF/AsymptoticApproximations/ODE/Singularities.lean#L310) — proved, no admission.
- [DLMF.AsymptoticApproximations.fabry_transformation](DLMF/AsymptoticApproximations/ODE/Singularities.lean#L262) — proved, no admission.
- [DLMF.AsymptoticApproximations.frobeniusAnalyticFactor_isLinearODE2SolutionOn](DLMF/AsymptoticApproximations/ODE/Frobenius.lean#L78) — direct admission.
- [DLMF.AsymptoticApproximations.frobeniusCoeff](DLMF/AsymptoticApproximations/ODE/Basic.lean#L85) — definition, no admission.
- [DLMF.AsymptoticApproximations.frobenius_log_solution](DLMF/AsymptoticApproximations/ODE/Singularities.lean#L134) — direct admission.
- [DLMF.AsymptoticApproximations.frobenius_solutions](DLMF/AsymptoticApproximations/ODE/Singularities.lean#L112) — direct admission.
- [DLMF.AsymptoticApproximations.indicialPoly](DLMF/AsymptoticApproximations/ODE/Basic.lean#L78) — definition, no admission.
- [DLMF.AsymptoticApproximations.rankOneCoeff](DLMF/AsymptoticApproximations/ODE/Basic.lean#L112) — definition, no admission.
- [DLMF.AsymptoticApproximations.rankOneExponent](DLMF/AsymptoticApproximations/ODE/Basic.lean#L104) — definition, no admission.
- [DLMF.AsymptoticApproximations.rankOne_exists_unique_solutions](DLMF/AsymptoticApproximations/ODE/Singularities.lean#L184) — direct admission.
- [DLMF.AsymptoticApproximations.summable_frobeniusCoeff_of_nonresonant](DLMF/AsymptoticApproximations/ODE/Frobenius.lean#L52) — direct admission.
- [DLMF.Bessel.Real.hasAsymptoticPowerSeries_besselJ_positive_zeros](DLMF/Bessel/CompleteZeroExpansions.lean#L94) — direct admission.
- [DLMF.Bessel.Real.hasAsymptoticPowerSeries_besselY_positive_zeros](DLMF/Bessel/CompleteZeroExpansions.lean#L106) — direct admission.
- [DLMF.Bessel.Real.strictAntiOn_re_besselI_order](DLMF/Bessel/CylinderMagnitude.lean#L44) — direct admission.
- [DLMF.Bessel.Real.strictAntiOn_re_besselK](DLMF/Bessel/CylinderMagnitude.lean#L38) — direct admission.
- [DLMF.Bessel.Real.strictMonoOn_re_besselI](DLMF/Bessel/CylinderMagnitude.lean#L32) — direct admission.
- [DLMF.Bessel.Real.strictMonoOn_re_besselK_order](DLMF/Bessel/CylinderMagnitude.lean#L50) — direct admission.
- [DLMF.Bessel.analyticOnNhd_cylinderOnLog](DLMF/Bessel/LogarithmicMonodromy.lean#L31) — direct admission.
- [DLMF.Bessel.besselFirstKindOnLog_add_int_mul_pi](DLMF/Bessel/LogarithmicMonodromy.lean#L78) — direct admission.
- [DLMF.Bessel.besselIOnLog_eq_besselJOnLog](DLMF/Bessel/LogarithmicMonodromy.lean#L72) — direct admission.
- [DLMF.Bessel.besselIOnLog_eq_besselKOnLog_connection](DLMF/Bessel/LogarithmicMonodromy.lean#L104) — direct admission.
- [DLMF.Bessel.besselI_ofReal_pos](DLMF/Bessel/Elementary.lean#L338) — proved, no admission.
- [DLMF.Bessel.besselJ_deriv_positive_zeros_interlace](DLMF/Bessel/OrderAndZeroProperties.lean#L80) — direct admission.
- [DLMF.Bessel.besselKOnLog_add_int_mul_pi](DLMF/Bessel/LogarithmicMonodromy.lean#L96) — direct admission.
- [DLMF.Bessel.besselK_eq_integral_cosh](DLMF/Bessel/KIntegralRep.lean#L707) — proved, no admission.
- [DLMF.Bessel.besselK_isEquivalent_cpow_nhds_zero](DLMF/Bessel/CylinderMagnitude.lean#L62) — direct admission.
- [DLMF.Bessel.besselK_ne_zero_of_nonneg_re](DLMF/Bessel/CylinderMagnitude.lean#L56) — direct admission.
- [DLMF.Bessel.besselK_neg](DLMF/Bessel/Basic/SecondKind.lean#L913) — proved, no admission.
- [DLMF.Bessel.besselK_ofReal_pos](DLMF/Bessel/Elementary.lean#L416) — proved, no admission.
- [DLMF.Bessel.besselK_zero_isEquivalent_neg_log_nhds_zero](DLMF/Bessel/CylinderMagnitude.lean#L69) — direct admission.
- [DLMF.Bessel.besselYOnLog](DLMF/Bessel/Basic.lean#L93) — definition, no admission.
- [DLMF.Bessel.besselYOnLog_add_int_mul_pi](DLMF/Bessel/LogarithmicMonodromy.lean#L86) — direct admission.
- [DLMF.Bessel.besselY_besselJ_positive_zeros_interlace](DLMF/Bessel/OrderAndZeroProperties.lean#L111) — direct admission.
- [DLMF.Bessel.besselZeroCorrectionSeries](DLMF/Bessel/CompleteZeroExpansions.lean#L56) — definition, no admission.
- [DLMF.Bessel.besselZeroCorrectionSeries_def](DLMF/Bessel/CompleteZeroExpansions.lean#L78) — proved, no admission.
- [DLMF.Bessel.besselZeroPhaseSeries](DLMF/Bessel/CompleteZeroExpansions.lean#L46) — definition, no admission.
- [DLMF.Bessel.besselZeroPhaseSeries_def](DLMF/Bessel/CompleteZeroExpansions.lean#L69) — proved, no admission.
- [DLMF.Bessel.coeff_besselZeroCorrectionSeries_le_three](DLMF/Bessel/CompleteZeroExpansions.lean#L83) — direct admission.
- [DLMF.Bessel.cylinderOnLog_ode](DLMF/Bessel/LogarithmicMonodromy.lean#L62) — direct admission.
- [DLMF.Bessel.cylinderOnLog_recurrences](DLMF/Bessel/LogarithmicMonodromy.lean#L40) — direct admission.
- [DLMF.Bessel.deriv_ne_zero_of_bessel_solution_eq_zero](DLMF/Bessel/PositiveZeroSequence.lean#L29) — direct admission.
- [DLMF.Bessel.existsUnique_cylinder_zero_between](DLMF/Bessel/OrderAndZeroProperties.lean#L90) — direct admission.
- [DLMF.Bessel.existsUnique_imaginary_deriv_besselJ_zero](DLMF/Bessel/OrderAndZeroProperties.lean#L46) — direct admission.
- [DLMF.Bessel.exists_positive_besselJ_zero_family](DLMF/Bessel/OrderAndZeroProperties.lean#L57) — direct admission.
- [DLMF.Bessel.exists_positive_besselY_zero_family](DLMF/Bessel/OrderAndZeroProperties.lean#L100) — direct admission.
- [DLMF.Bessel.exists_positive_deriv_besselJ_zero_family](DLMF/Bessel/OrderAndZeroProperties.lean#L69) — direct admission.
- [DLMF.Bessel.exists_uniform_besselJ_ne_zero](DLMF/Bessel/OrderAndZeroProperties.lean#L31) — direct admission.
- [DLMF.Bessel.exists_uniform_deriv_besselJ_ne_zero](DLMF/Bessel/OrderAndZeroProperties.lean#L38) — direct admission.
- [DLMF.Bessel.hankelCosineSeries](DLMF/Bessel/CompleteZeroExpansions.lean#L33) — definition, no admission.
- [DLMF.Bessel.hankelCosineSeries_def](DLMF/Bessel/CompleteZeroExpansions.lean#L59) — proved, no admission.
- [DLMF.Bessel.hankelH1OnLog](DLMF/Bessel/Basic.lean#L110) — definition, no admission.
- [DLMF.Bessel.hankelH2OnLog](DLMF/Bessel/Basic.lean#L113) — definition, no admission.
- [DLMF.Bessel.hankelOnLogPartialSum](DLMF/Bessel/LogarithmicDerivativeExpansions.lean#L28) — definition, no admission.
- [DLMF.Bessel.hankelOnLogPartialSum_def](DLMF/Bessel/LogarithmicDerivativeExpansions.lean#L34) — proved, no admission.
- [DLMF.Bessel.hankelSineSeries](DLMF/Bessel/CompleteZeroExpansions.lean#L39) — definition, no admission.
- [DLMF.Bessel.hankelSineSeries_def](DLMF/Bessel/CompleteZeroExpansions.lean#L64) — proved, no admission.
- [DLMF.Bessel.hasAsymptoticExpansion_besselIOnLog](DLMF/Bessel/LogarithmicAsymptotics.lean#L82) — direct admission.
- [DLMF.Bessel.hasAsymptoticExpansion_besselKOnLog](DLMF/Bessel/LogarithmicAsymptotics.lean#L74) — direct admission.
- [DLMF.Bessel.hasAsymptoticExpansion_hankelH1OnLog](DLMF/Bessel/LogarithmicAsymptotics.lean#L92) — direct admission.
- [DLMF.Bessel.hasAsymptoticExpansion_hankelH2OnLog](DLMF/Bessel/LogarithmicAsymptotics.lean#L105) — direct admission.
- [DLMF.Bessel.im_eq_zero_of_besselJ_eq_zero](DLMF/Bessel/DiniZeros.lean#L52) — direct admission.
- [DLMF.Bessel.im_eq_zero_of_diniNormalized_eq_zero](DLMF/Bessel/DiniZeros.lean#L58) — direct admission.
- [DLMF.Bessel.isBigO_besselIOnLog_two_exponentials](DLMF/Bessel/LogarithmicMonodromy.lean#L115) — direct admission.
- [DLMF.Bessel.isBigO_besselJOnLog_remainder](DLMF/Bessel/LogarithmicAsymptotics.lean#L118) — direct admission.
- [DLMF.Bessel.isBigO_besselYOnLog_remainder](DLMF/Bessel/LogarithmicAsymptotics.lean#L129) — direct admission.
- [DLMF.Bessel.isBigO_hankelOnLog_derivative_remainder](DLMF/Bessel/LogarithmicDerivativeExpansions.lean#L44) — direct admission.
- [DLMF.Bessel.iteratedDeriv_two_ne_zero_of_bessel_solution_deriv_eq_zero](DLMF/Bessel/PositiveZeroSequence.lean#L40) — direct admission.
- [DLMF.Bessel.largeArgumentCoefficient](DLMF/Bessel/LogarithmicAsymptotics.lean#L27) — definition, no admission.
- [DLMF.Bessel.modifiedCylinderOnLog_recurrences](DLMF/Bessel/LogarithmicMonodromy.lean#L49) — direct admission.
- [DLMF.Bessel.wronskian_besselJ_besselY](DLMF/Bessel/Basic/SecondKind.lean#L524) — proved, no admission.
- [DLMF.Bessel.wronskian_besselK_besselI](DLMF/Bessel/Basic/SecondKind.lean#L905) — proved, no admission.
- [DLMF.Bessel.wronskian_hankelH1_hankelH2](DLMF/Bessel/Basic/SecondKind.lean#L550) — proved, no admission.
- [DLMF.Confluent.PositiveCylinderError.amplitude_mul_secondDeriv](DLMF/ParabolicCylinder/PositiveParameterError.lean#L61) — direct admission.
- [DLMF.Confluent.PositiveCylinderError.density](DLMF/ParabolicCylinder/PositiveParameterError.lean#L46) — definition, no admission.
- [DLMF.Confluent.PositiveCylinderError.density_def](DLMF/ParabolicCylinder/PositiveParameterError.lean#L49) — proved, no admission.
- [DLMF.Confluent.PositiveCylinderError.error](DLMF/ParabolicCylinder/PositiveParameterError.lean#L37) — definition, no admission.
- [DLMF.Confluent.PositiveCylinderError.error_def](DLMF/ParabolicCylinder/PositiveParameterError.lean#L41) — proved, no admission.
- [DLMF.Confluent.PositiveCylinderError.error_uniform_parameter_and_tail](DLMF/ParabolicCylinder/PositiveParameterError.lean#L84) — direct admission.
- [DLMF.Confluent.PositiveCylinderError.integrable_density_and_variation](DLMF/ParabolicCylinder/PositiveParameterError.lean#L68) — direct admission.
- [DLMF.Confluent.PositiveCylinderError.leadingFactor](DLMF/ParabolicCylinder/PositiveParameterError.lean#L27) — definition, no admission.
- [DLMF.Confluent.PositiveCylinderError.leadingFactor_def](DLMF/ParabolicCylinder/PositiveParameterError.lean#L32) — proved, no admission.
- [DLMF.Confluent.PositiveCylinderError.norm_error_le](DLMF/ParabolicCylinder/PositiveParameterError.lean#L76) — direct admission.
- [DLMF.Confluent.PositiveCylinderError.tailVariation](DLMF/ParabolicCylinder/PositiveParameterError.lean#L53) — definition, no admission.
- [DLMF.Confluent.PositiveCylinderError.tailVariation_def](DLMF/ParabolicCylinder/PositiveParameterError.lean#L56) — proved, no admission.
- [DLMF.Confluent.differentiable_regularizedKummer_parameters_argument](DLMF/Confluent/JointRegularizedParameters.lean#L24) — direct admission.
- [DLMF.Confluent.hasAsymptoticExpansion_kummerUContinuedOnLog](DLMF/Confluent/Asymptotics/LogarithmicSector.lean#L62) — direct admission.
- [DLMF.Confluent.hasAsymptoticExpansion_whittakerWContinuedOnLog](DLMF/Confluent/Asymptotics/WhittakerLogarithmic.lean#L45) — direct admission.
- [DLMF.Confluent.hasFPowerSeriesOnBall_kummerM](DLMF/Confluent/Basic/KummerProperties.lean#L115) — proved, no admission.
- [DLMF.Confluent.isBigO_regularizedConfluentOnLog_two_exponentials](DLMF/Confluent/Asymptotics/LogarithmicTwoExponentials.lean#L43) — direct admission.
- [DLMF.Confluent.kummerM](DLMF/Confluent/Basic/KummerM.lean#L47) — definition, no admission.
- [DLMF.Confluent.kummerM_eq_euler_integral](DLMF/Confluent/KummerProperties.lean#L199) — proved, no admission.
- [DLMF.Confluent.kummerM_kummer_transform](DLMF/Confluent/Basic/KummerProperties.lean#L230) — proved, no admission.
- [DLMF.Confluent.kummerM_ode](DLMF/Confluent/Basic/KummerProperties.lean#L160) — proved, no admission.
- [DLMF.Confluent.kummerUContinuedOnLog](DLMF/Confluent/Basic/TricomiLogarithmic.lean#L31) — definition, no admission.
- [DLMF.Confluent.kummerU_besselK](DLMF/Confluent/Relations.lean#L326) — proved, no admission.
- [DLMF.Confluent.kummerU_eq_connection](DLMF/Confluent/Basic/Tricomi.lean#L70) — proved, no admission.
- [DLMF.Confluent.kummerU_eq_laguerreExtended](DLMF/Confluent/LaguerreContinuation.lean#L29) — proved, no admission.
- [DLMF.Confluent.kummerU_kummer_transform_all](DLMF/Confluent/BasicProperties/Continuity.lean#L577) — proved, no admission.
- [DLMF.Confluent.kummerU_laplace](DLMF/Confluent/IntegralRepresentations/EulerAndBessel.lean#L694) — proved, no admission.
- [DLMF.Confluent.parabolicCylinderU_eq_kummerUContinuedOnLog](DLMF/Confluent/ParabolicCylinder/LogarithmicRelation.lean#L30) — direct admission.
- [DLMF.Confluent.regularizedConfluent_eq_tricomi_continued](DLMF/Confluent/Asymptotics/LogarithmicTwoExponentials.lean#L32) — direct admission.
- [DLMF.Confluent.regularizedHGFun_eq_kummerU_connection](DLMF/Confluent/BasicProperties/Wronskians.lean#L586) — proved, no admission.
- [DLMF.Confluent.upperIncompleteGamma](DLMF/Confluent/Basic/IncompleteGamma.lean#L35) — definition, no admission.
- [DLMF.Confluent.whittakerWContinuedOnLog](DLMF/Confluent/Basic/WhittakerLogarithmic.lean#L30) — definition, no admission.
- [DLMF.Confluent.wronskian_regularizedHGFun](DLMF/Confluent/BasicProperties/Wronskians.lean#L336) — proved, no admission.
- [DLMF.Confluent.wronskian_regularizedHGFun_kummerU_all](DLMF/Confluent/BasicProperties/Wronskians.lean#L376) — proved, no admission.
- [DLMF.Hypergeometric.analyticOnNhd_regularizedGaussHypergeometric_comp](DLMF/Hypergeometric/ParameterHolomorphy.lean#L418) — proved, no admission.
- [DLMF.Hypergeometric.clausen_formula](DLMF/Hypergeometric/Clausen.lean#L198) — proved, no admission.
- [DLMF.Hypergeometric.coefficients_eq_gauss_of_regularSingular](DLMF/Hypergeometric/RiemannClassification.lean#L33) — direct admission.
- [DLMF.Hypergeometric.differentiableOn_regularizedGaussHypergeometric_joint](DLMF/Hypergeometric/ParameterHolomorphy.lean#L363) — proved, no admission.
- [DLMF.Hypergeometric.differentiable_regularizedGaussHypergeometric_params](DLMF/Hypergeometric/ParameterHolomorphy.lean#L400) — proved, no admission.
- [DLMF.Hypergeometric.genContinued_parameter_entire](DLMF/GeneralizedHypergeometric/AnalyticProperties.lean#L1098) — direct admission.
- [DLMF.Hypergeometric.generalizedHypergeometricCoeff](DLMF/GeneralizedHypergeometric/Basic/ParametersAndSeries.lean#L51) — definition, no admission.
- [DLMF.Hypergeometric.generalizedHypergeometricTruncated_theta_ode](DLMF/GeneralizedHypergeometric/TerminatingDifferentialEquation.lean#L25) — direct admission.
- [DLMF.Hypergeometric.generalizedHypergeometric_clausen_principal](DLMF/GeneralizedHypergeometric/Transformations.lean#L528) — proved, no admission.
- [DLMF.Hypergeometric.generalizedHypergeometric_diverges_nonzero](DLMF/GeneralizedHypergeometric/AnalyticProperties.lean#L1057) — proved, no admission.
- [DLMF.Hypergeometric.generalizedHypergeometric_entire](DLMF/GeneralizedHypergeometric/AnalyticProperties.lean#L66) — proved, no admission.
- [DLMF.Hypergeometric.generalizedHypergeometric_radius_one](DLMF/GeneralizedHypergeometric/AnalyticProperties.lean#L102) — proved, no admission.
- [DLMF.Hypergeometric.generalizedHypergeometric_radius_zero](DLMF/GeneralizedHypergeometric/AnalyticProperties.lean#L1036) — proved, no admission.
- [DLMF.Hypergeometric.generalizedHypergeometric_terminating_entire](DLMF/GeneralizedHypergeometric/AnalyticProperties.lean#L92) — proved, no admission.
- [DLMF.Hypergeometric.generalizedHypergeometric_theta_ode](DLMF/GeneralizedHypergeometric/DifferentialEquations.lean#L407) — proved, no admission.
- [DLMF.Hypergeometric.hasSum_regularizedGauss_one](DLMF/Hypergeometric/Boundary.lean#L58) — proved, no admission.
- [DLMF.Hypergeometric.iteratedDeriv_regularizedGaussHypergeometric](DLMF/Hypergeometric/Basic/CutPlane.lean#L501) — proved, no admission.
- [DLMF.Hypergeometric.regularizedGaussHypergeometric](DLMF/Hypergeometric/Basic/PrincipalBranch.lean#L166) — definition, no admission.
- [DLMF.Hypergeometric.regularizedGaussHypergeometric_connection_inv](DLMF/Hypergeometric/PrincipalConnections.lean#L71) — direct admission.
- [DLMF.Hypergeometric.regularizedGaussHypergeometric_connection_one_sub](DLMF/Hypergeometric/PrincipalConnections.lean#L100) — direct admission.
- [DLMF.Hypergeometric.regularizedGaussHypergeometric_contiguous_c](DLMF/Hypergeometric/ArgumentContinuation.lean#L47) — proved, no admission.
- [DLMF.Hypergeometric.regularizedGaussHypergeometric_eq_connection_inv](DLMF/Hypergeometric/PrincipalConnections.lean#L83) — direct admission.
- [DLMF.Hypergeometric.regularizedGaussHypergeometric_eq_connection_one_sub](DLMF/Hypergeometric/PrincipalConnections.lean#L112) — direct admission.
- [DLMF.Hypergeometric.regularizedGaussHypergeometric_eq_regularizedGaussHypergeometricIntegral](DLMF/Hypergeometric/Basic/CutPlane.lean#L457) — proved, no admission.
- [DLMF.Hypergeometric.regularizedGaussHypergeometric_euler](DLMF/Hypergeometric/ArgumentContinuation.lean#L231) — proved, no admission.
- [DLMF.Hypergeometric.regularizedGaussHypergeometric_neg_nat](DLMF/Hypergeometric/Basic/CutPlane.lean#L567) — proved, no admission.
- [DLMF.Hypergeometric.regularizedGaussHypergeometric_pfaff](DLMF/Hypergeometric/ArgumentContinuation.lean#L266) — proved, no admission.
- [DLMF.Hypergeometric.riemann_hypergeometric_solution_exp_log](DLMF/Hypergeometric/RiemannLogarithmicSolutions.lean#L29) — direct admission.
- [DLMF.Hypergeometric.tendsto_connection_inv](DLMF/Hypergeometric/PrincipalConnections.lean#L92) — direct admission.
- [DLMF.Hypergeometric.tendsto_connection_one_sub](DLMF/Hypergeometric/PrincipalConnections.lean#L122) — direct admission.
- [DLMF.Hypergeometric.wronskian_regularizedGauss_zero_pair](DLMF/Hypergeometric/RegularizedLocalWronskian.lean#L31) — direct admission.
- [DLMF.Legendre.LegendreQRegular](DLMF/Legendre/Basic/Associated.lean#L66) — definition, no admission.
- [DLMF.Legendre.SchlafliPBasedLoop](DLMF/Legendre/AssociatedSchlafliContours.lean#L32) — definition, no admission.
- [DLMF.Legendre.SchlafliQOppositeLobes](DLMF/Legendre/AssociatedSchlafliContours.lean#L177) — definition, no admission.
- [DLMF.Legendre.associatedP](DLMF/Legendre/Basic/Associated.lean#L49) — definition, no admission.
- [DLMF.Legendre.associatedP_entire_degree](DLMF/Legendre/Associated/ConjugationAndValues.lean#L175) — proved, no admission.
- [DLMF.Legendre.associatedP_entire_order](DLMF/Legendre/Associated/ConjugationAndValues.lean#L185) — proved, no admission.
- [DLMF.Legendre.associatedP_eq_schlafliPFirstExpression](DLMF/Legendre/AssociatedSchlafliContours.lean#L146) — direct admission.
- [DLMF.Legendre.associatedP_eq_schlafliPSecondExpression](DLMF/Legendre/AssociatedSchlafliContours.lean#L153) — direct admission.
- [DLMF.Legendre.associatedP_nat_order_rodrigues](DLMF/Legendre/IntegerTheory.lean#L181) — proved, no admission.
- [DLMF.Legendre.associatedP_negative_integer_order](DLMF/Legendre/Connections.lean#L944) — proved, no admission.
- [DLMF.Legendre.associatedP_order_gt_degree](DLMF/Legendre/IntegerTheory.lean#L233) — proved, no admission.
- [DLMF.Legendre.associatedP_recurrence_3](DLMF/Legendre/AssociatedRecurrences.lean#L716) — proved, no admission.
- [DLMF.Legendre.associatedP_recurrence_4](DLMF/Legendre/AssociatedRecurrences.lean#L754) — proved, no admission.
- [DLMF.Legendre.associatedP_recurrence_5](DLMF/Legendre/AssociatedRecurrences.lean#L731) — proved, no admission.
- [DLMF.Legendre.associatedP_recurrence_6](DLMF/Legendre/AssociatedRecurrences.lean#L682) — proved, no admission.
- [DLMF.Legendre.associatedP_recurrence_7](DLMF/Legendre/AssociatedRecurrences.lean#L700) — proved, no admission.
- [DLMF.Legendre.associatedP_reflect_degree](DLMF/Legendre/Associated/BoundaryAndConnections.lean#L457) — proved, no admission.
- [DLMF.Legendre.associatedQ](DLMF/Legendre/Basic/Associated.lean#L61) — definition, no admission.
- [DLMF.Legendre.associated_connection_14](DLMF/Legendre/Connections.lean#L370) — proved, no admission.
- [DLMF.Legendre.associated_wronskian_8](DLMF/Legendre/Associated/BoundaryAndConnections.lean#L597) — proved, no admission.
- [DLMF.Legendre.ferrersP](DLMF/Legendre/Basic/Functions.lean#L40) — definition, no admission.
- [DLMF.Legendre.ferrersP_eqOn_even_odd](DLMF/Legendre/Associated/Wronskians.lean#L265) — proved, no admission.
- [DLMF.Legendre.ferrersP_even_odd](DLMF/Legendre/Associated/QuadraticFerrers.lean#L452) — proved, no admission.
- [DLMF.Legendre.ferrersP_nat_order_rodrigues](DLMF/Legendre/IntegerTheory.lean#L147) — proved, no admission.
- [DLMF.Legendre.ferrersP_negative_integer_order](DLMF/Legendre/Connections.lean#L302) — proved, no admission.
- [DLMF.Legendre.ferrersP_zero_1](DLMF/Legendre/SpecialValues.lean#L58) — proved, no admission.
- [DLMF.Legendre.ferrersP_zero_2](DLMF/Legendre/SpecialValues.lean#L82) — proved, no admission.
- [DLMF.Legendre.ferrersQ](DLMF/Legendre/Basic/Associated.lean#L86) — definition, no admission.
- [DLMF.Legendre.ferrersQ_eqOn_even_odd](DLMF/Legendre/Associated/Wronskians.lean#L286) — proved, no admission.
- [DLMF.Legendre.ferrersQ_even_odd](DLMF/Legendre/Associated/QuadraticFerrers.lean#L467) — proved, no admission.
- [DLMF.Legendre.ferrersQ_zero_3](DLMF/Legendre/SpecialValues.lean#L109) — proved, no admission.
- [DLMF.Legendre.ferrersQ_zero_4](DLMF/Legendre/SpecialValues.lean#L127) — proved, no admission.
- [DLMF.Legendre.ferrers_connection_10](DLMF/Legendre/Connections.lean#L274) — proved, no admission.
- [DLMF.Legendre.ferrers_orthogonality_6](DLMF/Legendre/Integrals/FerrersGreen.lean#L75) — proved, no admission.
- [DLMF.Legendre.ferrers_orthogonality_8](DLMF/Legendre/Integrals/FerrersGreen.lean#L128) — proved, no admission.
- [DLMF.Legendre.integrableOn_schlafliPFirstTail](DLMF/Legendre/AssociatedSchlafliContours.lean#L133) — direct admission.
- [DLMF.Legendre.integrableOn_schlafliPSecondTail](DLMF/Legendre/AssociatedSchlafliContours.lean#L139) — direct admission.
- [DLMF.Legendre.isNumericallySatisfactoryPair_associatedP_olverQ](DLMF/Legendre/EndpointPair.lean#L54) — direct admission.
- [DLMF.Legendre.legendreBranchPower](DLMF/Legendre/Basic/Associated.lean#L42) — definition, no admission.
- [DLMF.Legendre.legendrePolynomialP_addition_sqrt_pair](DLMF/Legendre/PolynomialAddition.lean#L30) — proved, no admission.
- [DLMF.Legendre.legendreQPoly_eval_eq_convolution](DLMF/Legendre/IntegerSecondKind.lean#L29) — direct admission.
- [DLMF.Legendre.legendreQPoly_eval_eq_legendre_sum](DLMF/Legendre/IntegerSecondKind.lean#L37) — direct admission.
- [DLMF.Legendre.legendreQ_nat](DLMF/Legendre/Integer.lean#L250) — proved, no admission.
- [DLMF.Legendre.legendreQ_nat_eq_neumann_integral](DLMF/Legendre/IntegerSecondKind.lean#L55) — direct admission.
- [DLMF.Legendre.legendreQ_zero](DLMF/Legendre/SecondKind.lean#L39) — proved, no admission.
- [DLMF.Legendre.nonempty_schlafliPBasedLoop](DLMF/Legendre/AssociatedSchlafliContours.lean#L52) — direct admission.
- [DLMF.Legendre.nonempty_schlafliQOppositeLobes](DLMF/Legendre/AssociatedSchlafliContours.lean#L205) — direct admission.
- [DLMF.Legendre.olverQ](DLMF/Legendre/Basic/Associated.lean#L54) — definition, no admission.
- [DLMF.Legendre.olverQ_entire_degree](DLMF/Legendre/Associated/ConjugationAndValues.lean#L319) — proved, no admission.
- [DLMF.Legendre.olverQ_entire_order](DLMF/Legendre/Associated/ConjugationAndValues.lean#L337) — proved, no admission.
- [DLMF.Legendre.olverQ_eq_schlafliQExpression](DLMF/Legendre/AssociatedSchlafliContours.lean#L228) — direct admission.
- [DLMF.Legendre.schlafliPFirstExpression](DLMF/Legendre/AssociatedSchlafliContours.lean#L83) — definition, no admission.
- [DLMF.Legendre.schlafliPFirstExpression_def](DLMF/Legendre/AssociatedSchlafliContours.lean#L120) — proved, no admission.
- [DLMF.Legendre.schlafliPFirstLoopIntegral](DLMF/Legendre/AssociatedSchlafliContours.lean#L68) — definition, no admission.
- [DLMF.Legendre.schlafliPFirstLoopIntegral_def](DLMF/Legendre/AssociatedSchlafliContours.lean#L104) — proved, no admission.
- [DLMF.Legendre.schlafliPFirstTail](DLMF/Legendre/AssociatedSchlafliContours.lean#L57) — definition, no admission.
- [DLMF.Legendre.schlafliPFirstTail_def](DLMF/Legendre/AssociatedSchlafliContours.lean#L94) — proved, no admission.
- [DLMF.Legendre.schlafliPSecondExpression](DLMF/Legendre/AssociatedSchlafliContours.lean#L89) — definition, no admission.
- [DLMF.Legendre.schlafliPSecondExpression_def](DLMF/Legendre/AssociatedSchlafliContours.lean#L126) — proved, no admission.
- [DLMF.Legendre.schlafliPSecondLoopIntegral](DLMF/Legendre/AssociatedSchlafliContours.lean#L75) — definition, no admission.
- [DLMF.Legendre.schlafliPSecondLoopIntegral_def](DLMF/Legendre/AssociatedSchlafliContours.lean#L112) — proved, no admission.
- [DLMF.Legendre.schlafliPSecondTail](DLMF/Legendre/AssociatedSchlafliContours.lean#L62) — definition, no admission.
- [DLMF.Legendre.schlafliPSecondTail_def](DLMF/Legendre/AssociatedSchlafliContours.lean#L99) — proved, no admission.
- [DLMF.Legendre.schlafliQExpression](DLMF/Legendre/AssociatedSchlafliContours.lean#L211) — definition, no admission.
- [DLMF.Legendre.schlafliQExpression_def](DLMF/Legendre/AssociatedSchlafliContours.lean#L218) — proved, no admission.
- [DLMF.Legendre.tendsto_associatedP_neg_order_scaled_one](DLMF/Legendre/EndpointPair.lean#L29) — direct admission.
- [DLMF.Legendre.tendsto_olverQ_scaled_cobounded](DLMF/Legendre/EndpointPair.lean#L37) — direct admission.
- [DLMF.Legendre.tendsto_olverQ_zero_order_div_log_one](DLMF/Legendre/EndpointPair.lean#L45) — direct admission.
- [DLMF.Legendre.tendsto_schlafliPFirstExpression](DLMF/Legendre/AssociatedSchlafliContours.lean#L160) — direct admission.
- [DLMF.Legendre.tendsto_schlafliPSecondExpression](DLMF/Legendre/AssociatedSchlafliContours.lean#L168) — direct admission.
- [DLMF.Legendre.tendsto_schlafliQExpression](DLMF/Legendre/AssociatedSchlafliContours.lean#L235) — direct admission.
- [DLMF.OrthogonalPolynomials.LegendreAddition.legendre_eq_kernel](DLMF/OrthogonalPolynomials/LegendreAddition.lean#L533) — proved, no admission.
- [DLMF.Struve.struveH](DLMF/Struve/Basic/Functions.lean#L56) — definition, no admission.
- [DLMF.Struve.struveH_eq_poisson](DLMF/Struve/Poisson.lean#L202) — proved, no admission.
- [DLMF.Struve.struveH_ode](DLMF/Struve/SeriesAndEquations.lean#L522) — proved, no admission.
- [DLMF.Struve.struveK](DLMF/Struve/Basic/Functions.lean#L83) — definition, no admission.
- [DLMF.Struve.struveK_asymptotic](DLMF/Struve/Asymptotics/Watson.lean#L888) — proved, no admission.
- [DLMF.Struve.struveK_asymptotic_rotSector](DLMF/Struve/Asymptotics/Watson.lean#L532) — proved, no admission.
- [DLMF.Struve.struveK_laplace](DLMF/Struve/Representations/PoissonAndBarnesLoop.lean#L86) — proved, no admission.
- [LiouvilleGreen.CompactInterval.Data](DLMFMathlib/Analysis/ODE/LiouvilleGreenParameterBounds.lean#L31) — definition, no admission.
- [LiouvilleGreen.CompactInterval.Data.amplitude](DLMFMathlib/Analysis/ODE/LiouvilleGreenParameterBounds.lean#L44) — definition, no admission.
- [LiouvilleGreen.CompactInterval.Data.amplitude_def](DLMFMathlib/Analysis/ODE/LiouvilleGreenParameterBounds.lean#L47) — proved, no admission.
- [LiouvilleGreen.CompactInterval.Data.density](DLMFMathlib/Analysis/ODE/LiouvilleGreenParameterBounds.lean#L58) — definition, no admission.
- [LiouvilleGreen.CompactInterval.Data.density_def](DLMFMathlib/Analysis/ODE/LiouvilleGreenParameterBounds.lean#L63) — proved, no admission.
- [LiouvilleGreen.CompactInterval.Data.existsUnique_dirichlet_frequency_of_threshold](DLMFMathlib/Analysis/ODE/LiouvilleGreenParameterBounds.lean#L139) — direct admission.
- [LiouvilleGreen.CompactInterval.Data.exists_dirichlet_frequency_sequence](DLMFMathlib/Analysis/ODE/LiouvilleGreenParameterBounds.lean#L118) — direct admission.
- [LiouvilleGreen.CompactInterval.Data.exists_oscillatory_parameter_family](DLMFMathlib/Analysis/ODE/LiouvilleGreenParameterBounds.lean#L98) — direct admission.
- [LiouvilleGreen.CompactInterval.Data.integratedVariation](DLMFMathlib/Analysis/ODE/LiouvilleGreenParameterBounds.lean#L75) — definition, no admission.
- [LiouvilleGreen.CompactInterval.Data.integratedVariation_def](DLMFMathlib/Analysis/ODE/LiouvilleGreenParameterBounds.lean#L79) — proved, no admission.
- [LiouvilleGreen.CompactInterval.Data.parameterBound](DLMFMathlib/Analysis/ODE/LiouvilleGreenParameterBounds.lean#L84) — definition, no admission.
- [LiouvilleGreen.CompactInterval.Data.parameterBound_def](DLMFMathlib/Analysis/ODE/LiouvilleGreenParameterBounds.lean#L89) — proved, no admission.
- [LiouvilleGreen.CompactInterval.Data.phase](DLMFMathlib/Analysis/ODE/LiouvilleGreenParameterBounds.lean#L51) — definition, no admission.
- [LiouvilleGreen.CompactInterval.Data.phase_def](DLMFMathlib/Analysis/ODE/LiouvilleGreenParameterBounds.lean#L54) — proved, no admission.
- [LiouvilleGreen.CompactInterval.Data.variation](DLMFMathlib/Analysis/ODE/LiouvilleGreenParameterBounds.lean#L68) — definition, no admission.
- [LiouvilleGreen.CompactInterval.Data.variation_def](DLMFMathlib/Analysis/ODE/LiouvilleGreenParameterBounds.lean#L71) — proved, no admission.
- [LiouvilleGreen.Interval.eqOn_of_recessive_ratio](DLMFMathlib/Analysis/ODE/LiouvilleGreenEndpoint.lean#L28) — proved, no admission.
- [LiouvilleGreen.Interval.eqOn_of_recessive_ratio_left](DLMFMathlib/Analysis/ODE/LiouvilleGreenEndpoint.lean#L141) — proved, no admission.
- [LiouvilleGreen.Interval.exists_dominant_of_recessive](DLMFMathlib/Analysis/ODE/LiouvilleGreenDominant.lean#L28) — proved, no admission.
- [LiouvilleGreen.Interval.exists_dominant_of_recessive_left](DLMFMathlib/Analysis/ODE/LiouvilleGreenDominant.lean#L133) — proved, no admission.
- [LiouvilleGreen.RealInterval.Data](DLMFMathlib/Analysis/ODE/LiouvilleGreenGeneralInterval.lean#L31) — definition, no admission.
- [LiouvilleGreen.RealInterval.Data.amplitude](DLMFMathlib/Analysis/ODE/LiouvilleGreenGeneralInterval.lean#L47) — definition, no admission.
- [LiouvilleGreen.RealInterval.Data.amplitude_def](DLMFMathlib/Analysis/ODE/LiouvilleGreenGeneralInterval.lean#L50) — proved, no admission.
- [LiouvilleGreen.RealInterval.Data.approach](DLMFMathlib/Analysis/ODE/LiouvilleGreenGeneralInterval.lean#L84) — definition, no admission.
- [LiouvilleGreen.RealInterval.Data.approach_def](DLMFMathlib/Analysis/ODE/LiouvilleGreenGeneralInterval.lean#L88) — proved, no admission.
- [LiouvilleGreen.RealInterval.Data.density](DLMFMathlib/Analysis/ODE/LiouvilleGreenGeneralInterval.lean#L55) — definition, no admission.
- [LiouvilleGreen.RealInterval.Data.density_def](DLMFMathlib/Analysis/ODE/LiouvilleGreenGeneralInterval.lean#L60) — proved, no admission.
- [LiouvilleGreen.RealInterval.Data.exists_exponential](DLMFMathlib/Analysis/ODE/LiouvilleGreenGeneralInterval.lean#L95) — direct admission.
- [LiouvilleGreen.RealInterval.Data.exists_oscillatory_pair](DLMFMathlib/Analysis/ODE/LiouvilleGreenGeneralInterval.lean#L117) — direct admission.
- [LiouvilleGreen.RealInterval.Data.mem_referenceSegment_iff](DLMFMathlib/Analysis/ODE/LiouvilleGreenGeneralInterval.lean#L70) — proved, no admission.
- [LiouvilleGreen.RealInterval.Data.referenceSegment](DLMFMathlib/Analysis/ODE/LiouvilleGreenGeneralInterval.lean#L65) — definition, no admission.
- [LiouvilleGreen.RealInterval.Data.tendsto_exponential_error_opposite](DLMFMathlib/Analysis/ODE/LiouvilleGreenGeneralInterval.lean#L144) — direct admission.
- [LiouvilleGreen.RealInterval.Data.variation](DLMFMathlib/Analysis/ODE/LiouvilleGreenGeneralInterval.lean#L75) — definition, no admission.
- [LiouvilleGreen.RealInterval.Data.variation_def](DLMFMathlib/Analysis/ODE/LiouvilleGreenGeneralInterval.lean#L79) — proved, no admission.
- [LiouvilleGreen.integrable_errorDensity_inverseSquare_split](DLMFMathlib/Analysis/ODE/LiouvilleGreenPowerEndpoints.lean#L73) — direct admission.
- [LiouvilleGreen.integrable_errorDensity_of_power_atTop](DLMFMathlib/Analysis/ODE/LiouvilleGreenPowerEndpoints.lean#L51) — direct admission.
- [LiouvilleGreen.integrable_errorDensity_of_power_at_zero](DLMFMathlib/Analysis/ODE/LiouvilleGreenPowerEndpoints.lean#L30) — direct admission.
- [ODE.IsNumericallySatisfactoryPair](DLMFMathlib/Analysis/ODE/EndpointBasis.lean#L55) — definition, no admission.
- [ODE.IsRecessiveAt](DLMFMathlib/Analysis/ODE/EndpointBasis.lean#L33) — definition, no admission.
- [ODE.IsRecessiveAt.exists_smul_eq](DLMFMathlib/Analysis/ODE/EndpointBasis.lean#L46) — direct admission.
- [ODE.SingularSinePotential.control](DLMFMathlib/Analysis/ODE/SingularSinePotential.lean#L48) — definition, no admission.
- [ODE.SingularSinePotential.control_def](DLMFMathlib/Analysis/ODE/SingularSinePotential.lean#L52) — proved, no admission.
- [ODE.SingularSinePotential.exists_scattering_family](DLMFMathlib/Analysis/ODE/SingularSinePotential.lean#L79) — direct admission.
- [ODE.SingularSinePotential.exists_solution](DLMFMathlib/Analysis/ODE/SingularSinePotential.lean#L58) — direct admission.
- [ODE.WeightedVolterra.Data](DLMFMathlib/Analysis/ODE/GeneralWeightedVolterra.lean#L49) — definition, no admission.
- [ODE.WeightedVolterra.Data.IsSolution](DLMFMathlib/Analysis/ODE/GeneralWeightedVolterra.lean#L140) — definition, no admission.
- [ODE.WeightedVolterra.Data.existsUnique_isSolution](DLMFMathlib/Analysis/ODE/GeneralWeightedVolterra.lean#L179) — direct admission.
- [ODE.WeightedVolterra.Data.isSolution_iff](DLMFMathlib/Analysis/ODE/GeneralWeightedVolterra.lean#L152) — proved, no admission.
- [ODE.WeightedVolterra.Data.iterate](DLMFMathlib/Analysis/ODE/GeneralWeightedVolterra.lean#L127) — definition, no admission.
- [ODE.WeightedVolterra.Data.iterate_succ](DLMFMathlib/Analysis/ODE/GeneralWeightedVolterra.lean#L135) — proved, no admission.
- [ODE.WeightedVolterra.Data.iterate_zero](DLMFMathlib/Analysis/ODE/GeneralWeightedVolterra.lean#L132) — proved, no admission.
- [ODE.WeightedVolterra.Data.norm_isSolution_le_selfForcingBound](DLMFMathlib/Analysis/ODE/GeneralWeightedVolterra.lean#L217) — direct admission.
- [ODE.WeightedVolterra.Data.norm_iterate_succ_sub_le](DLMFMathlib/Analysis/ODE/GeneralWeightedVolterra.lean#L165) — direct admission.
- [ODE.WeightedVolterra.Data.transform](DLMFMathlib/Analysis/ODE/GeneralWeightedVolterra.lean#L106) — definition, no admission.
- [ODE.WeightedVolterra.Data.transform_def](DLMFMathlib/Analysis/ODE/GeneralWeightedVolterra.lean#L115) — proved, no admission.
- [ODE.WeightedVolterra.Data.variation](DLMFMathlib/Analysis/ODE/GeneralWeightedVolterra.lean#L98) — definition, no admission.
- [ODE.WeightedVolterra.Data.variation_def](DLMFMathlib/Analysis/ODE/GeneralWeightedVolterra.lean#L102) — proved, no admission.
- [ODE.WeightedVolterra.initialSegment](DLMFMathlib/Analysis/ODE/GeneralWeightedVolterra.lean#L37) — definition, no admission.
- [ODE.WeightedVolterra.interval](DLMFMathlib/Analysis/ODE/GeneralWeightedVolterra.lean#L34) — definition, no admission.
- [ODE.WeightedVolterra.mem_initialSegment_iff](DLMFMathlib/Analysis/ODE/GeneralWeightedVolterra.lean#L44) — proved, no admission.
- [ODE.WeightedVolterra.mem_interval_iff](DLMFMathlib/Analysis/ODE/GeneralWeightedVolterra.lean#L40) — proved, no admission.
- [ODE.WeightedVolterra.selfForcingBound](DLMFMathlib/Analysis/ODE/GeneralWeightedVolterra.lean#L197) — definition, no admission.
- [ODE.WeightedVolterra.selfForcingBound_def](DLMFMathlib/Analysis/ODE/GeneralWeightedVolterra.lean#L201) — proved, no admission.
- [ODE.WeightedVolterra.selfForcingBound_zero](DLMFMathlib/Analysis/ODE/GeneralWeightedVolterra.lean#L205) — proved, no admission.
- [ODE.WeightedVolterra.tendsto_selfForcingBound_zero](DLMFMathlib/Analysis/ODE/GeneralWeightedVolterra.lean#L210) — direct admission.
- [ODE.continuousOn_parametric_linear_ode](DLMFMathlib/Analysis/ODE/ParameterDependence.lean#L31) — direct admission.
- [ODE.differentiable_complex_parametric_linear_ode](DLMFMathlib/Analysis/ODE/ParameterDependence.lean#L86) — direct admission.
- [ODE.differentiable_parametric_linear_ode](DLMFMathlib/Analysis/ODE/ParameterDependence.lean#L50) — direct admission.
- [ODE.existsUnique_secondOrder_continuous_interval](DLMFMathlib/Analysis/ODE/ContinuousSecondOrder.lean#L54) — direct admission.
- [ODE.exists_ball_solution_linear_ode](DLMFMathlib/Analysis/ODE/BallLinear.lean#L176) — proved, no admission.
- [ODE.fundamentalPair_iff_linearIndependent_iff_wronskian](DLMFMathlib/Analysis/ODE/ContinuousSecondOrder.lean#L84) — direct admission.
- [ODE.isNumericallySatisfactoryPair_iff](DLMFMathlib/Analysis/ODE/EndpointBasis.lean#L62) — proved, no admission.
- [ODE.isRecessiveAt_iff](DLMFMathlib/Analysis/ODE/EndpointBasis.lean#L39) — proved, no admission.
- [ODE.linearOdeTaylorCoeff](DLMFMathlib/Analysis/ODE/EntireLinear.lean#L47) — definition, no admission.
- [ODE.product_symmetricSquare_equation](DLMFMathlib/Analysis/ODE/SymmetricSquareGeneral.lean#L29) — direct admission.
- [ODE.reduction_of_order_continuous](DLMFMathlib/Analysis/ODE/ContinuousSecondOrder.lean#L102) — direct admission.
- [ODE.secondOrderPicardIterate](DLMFMathlib/Analysis/ODE/ContinuousSecondOrder.lean#L31) — definition, no admission.
- [ODE.secondOrderPicardIterate_succ](DLMFMathlib/Analysis/ODE/ContinuousSecondOrder.lean#L44) — proved, no admission.
- [ODE.secondOrderPicardIterate_zero](DLMFMathlib/Analysis/ODE/ContinuousSecondOrder.lean#L40) — proved, no admission.
- [ODE.wronskian_cyclic_sum](DLMFMathlib/Analysis/ODE/SymmetricSquareGeneral.lean#L45) — proved, no admission.
- [ODE.wronskian_eq_exp_integral_continuous](DLMFMathlib/Analysis/ODE/ContinuousSecondOrder.lean#L72) — direct admission.
- [PowerSeries.coeff_ordinary_second_order](DLMFMathlib/Analysis/ODE/FormalSeries.lean#L26) — direct admission.
- [Real.eventually_norm_lt_of_exp_control](DLMFMathlib/Analysis/Asymptotics/ExponentialMajorant.lean#L62) — proved, no admission.
- [Real.existsUnique_zero_sin_add_error](DLMFMathlib/Analysis/ODE/SineErrorZeros.lean#L42) — direct admission.
- [Real.exists_sin_error_zero_sequence](DLMFMathlib/Analysis/ODE/SineErrorZeros.lean#L56) — direct admission.
- [Real.exists_zero_sin_add_error](DLMFMathlib/Analysis/ODE/SineErrorZeros.lean#L31) — direct admission.
- [Real.exp_div_sub_one_le_two_div](DLMFMathlib/Analysis/Asymptotics/ExponentialMajorant.lean#L30) — proved, no admission.
- [Real.exp_mul_le_of_abs_logDeriv_le](DLMFMathlib/Analysis/ODE/RealChangeOfVariables.lean#L59) — direct admission.
- [Real.integral_inv_affine_cos_sin](DLMFMathlib/Analysis/Integral/TrigonometricReciprocal.lean#L26) — direct admission.
- [Real.iteratedDeriv_liouville_inverse](DLMFMathlib/Analysis/ODE/RealChangeOfVariables.lean#L45) — direct admission.
- [Real.norm_le_inv_parameter_of_exp_control](DLMFMathlib/Analysis/Asymptotics/ExponentialMajorant.lean#L43) — proved, no admission.
- [Real.schwarzian_quotient_comp](DLMFMathlib/Analysis/ODE/RealChangeOfVariables.lean#L30) — direct admission.
- [Real.sineMajorant](DLMFMathlib/Analysis/ODE/SingularSinePotential.lean#L30) — definition, no admission.
- [Real.sineMajorant_def](DLMFMathlib/Analysis/ODE/SingularSinePotential.lean#L33) — proved, no admission.
- [Real.sineMajorant_eq](DLMFMathlib/Analysis/ODE/SingularSinePotential.lean#L38) — direct admission.
- [TauCeti.argumentPrinciple_windingNumber](.lake/packages/TauCeti/TauCeti/Analysis/Complex/Conformal/ArgumentPrinciple.lean#L87) — proved, no admission.
- [TauCeti.argumentPrinciple_windingNumber_of_analyticOnNhd](.lake/packages/TauCeti/TauCeti/Analysis/Complex/Conformal/ArgumentPrinciple.lean#L114) — proved, no admission.
