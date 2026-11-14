# Kristensson statement acquisition ledger

The approved follow-up has corrected this book’s SYNOPSIS and ERRATA records.
The acquisition evidence below is retained as a historical audit; references to
unchanged synopsis text or blocked defective variants describe that snapshot.
Current per-item dispositions are in BookAcquisition-RevisionNotes.md.

This is a working, exhaustive entry inventory for `SYNOPSIS-Kristensson.md`. An existing statement may itself be admitted; membership is distinguished from proof completion. Each entry records checked matches and explicitly lists remaining distinct subclaims. An entry with a pending comparison is not certified as covered.

## K-1.01 — Helmholtz equation and separation.

New EuclideanSpace.orthogonalLaplacian with proved defining formula; laplacian_comp_eq_orthogonalLaplacian identifies it with Mathlib's Cartesian Laplacian for an orthogonal chart, and orthogonalLaplacian_prod gives the full variable-metric product-separation identity. orthogonalLaplacian_prod_const_metric is its constant-metric special case. The Helmholtz equation is Laplacian.laplacian u+k²u=0, using the upstream Laplacian directly. The final conditional separation remark is substitution into this product identity.

## K-2.01 — ODE and normal form (§2.1.1, (2.1)–(2.2)).

Existing operator: `DLMF.AlgebraicAnalytic.IsLinearODE2SolutionOn`; first-derivative elimination: `DLMF.AlgebraicAnalytic.isLinearODE2SolutionOn_elim_first`. The primitive `P` is explicit in the hypotheses; no global primitive on a nonsimply connected domain is inferred.

## K-2.02 — change of independent variable (Theorem 2.1(a), p. 4).

Existing change-of-variable formula: `DLMF.AlgebraicAnalytic.isLinearODE2SolutionOn_comp_eta_iff`; also `DLMF.Heun.isLinearODE2On_comp`. The nonzero derivative and domain image assumptions must be retained.

## K-2.03 — nonvanishing gauge (Theorem 2.1(b), p. 4).

Existing nonvanishing gauge formula: `DLMF.Heun.isLinearODE2On_gauge_mul`. Its supplied logarithmic derivative and derivative satisfy exactly the displayed coefficient relations.

## K-2.04 — ordinary and singular points (Definitions 2.1, 2.4–2.5, pp. 4,12,24).

Existing definitions: `Complex.LinearODEOrdinaryAt`, `Complex.LinearODEAtMostRegularAt`, `Complex.LinearODERegularSingularAt`, `Complex.LinearODEIrregularAt`, and their infinity variants in `DLMFMathlib.Analysis.ODE.Singularities`. Coefficient vector is `![q,p]`. Reciprocal transformation: `DLMF.AlgebraicAnalytic.isLinearODE2SolutionOn_inv`. Regular singular explicitly excludes ordinary; weighted analytic extension is the at-most-regular predicate.

## K-2.05 — Wronskian and linear dependence (Definition 2.2, Lemmas 2.1–2.2, pp. 5–6).

Existing canonical ODE.wronskian and DLMF.AlgebraicAnalytic.wronskianN / wronskianN_two; hasDerivAt_wronskian_of_isLinearODE2SolutionOn, wronskian_eq_mul_exp and isFundamentalPair_tfae cover the ordinary-equation statements. New Complex.wronskian_eq_zero_iff_linearCombination_eq_zero and wronskian_eventuallyEq_zero_iff_linearCombination_eventuallyEq_zero in DLMFMathlib.Analysis.Meromorphic.Wronskian give the arbitrary analytic/meromorphic criterion without a common ODE. Punctured germs retain correctness at totalized poles and removable points.

## K-2.06 — Picard construction (Theorem 2.2, Lemmas 2.3–2.6, pp. 7–9).

Ordinary analytic existence/uniqueness: DLMF.AlgebraicAnalytic.exists_isLinearODE2SolutionOn and isLinearODE2SolutionOn_unique. Constructive Complex.PicardSeries.term/solution have proved defining/initial APIs; norm_term_le, analyticOnNhd_term, deriv_term_add_one, deriv_deriv_term_add_one, tendstoUniformlyOn_sum_range_term and solution_properties give exactly the factorial majorant, derivative identities, closed-disc uniform convergence and summed ODE/initial values. Mathlib TendstoUniformlyOn.tendstoLocallyUniformlyOn immediately supplies the local uniform convergence on that analytic disc, and restriction to smaller discs gives its open-domain formulation.

## K-2.07 — fundamental solutions and reduction of order (§2.3.1, pp. 10–11).

Existing normalized fundamental pair: DLMF.AlgebraicAnalytic.exists_isFundamentalPair and isFundamentalPair_of_initial. New Complex.reduction_of_order_of_primitives gives u*G with F'=p, G'=exp(-F)/u², its ODE and exact Wronskian exp(-F). exists_reduction_of_order supplies those normalized analytic primitives on a simply connected zero-free solution domain. These are all in DLMFMathlib.Analysis.ODE.ReductionOfOrder.

## K-2.08 — indicial polynomial and Frobenius recursion (§2.4.1, (2.9)–(2.15), pp. 12–15).

Existing canonical indicial polynomial and recursion: DLMF.AsymptoticApproximations.indicialPoly / frobeniusCoeff, with j=n-m reindexing. Convergent nonresonant solutions are frobenius_solutions; repeated/resonant root solutions are frobenius_log_solution. New PowerSeries.indicial_eq_zero_of_formal_frobenius and coeff_formal_frobenius in DLMFMathlib.Analysis.ODE.FormalSeries state the exact formal residual coefficient equations without assuming analytic convergence.

## K-2.09 — indicial roots (Lemma 2.7, p. 15).

New proved algebra: `Complex.frobenius_indicial_shift` in `DLMFMathlib.Analysis.ODE.FrobeniusMajorants`. The sum/product root relations are the coefficient comparison of the monic quadratic; the shifted factorization is checked by Lean.

## K-2.10 — coefficient majorants (Lemmas 2.8–2.9, pp. 15–17).

New targets: `Complex.norm_frobenius_coefficient_le`, `Complex.exists_norm_frobenius_coefficient_le`, and `Complex.summable_frobenius_of_geometric_majorant`. These separately cover the two coefficient bounds and their absolute-convergence consequence.

## K-2.11 — convergent Frobenius solutions (Theorem 2.3, pp. 18–20).

New DLMF.AsymptoticApproximations.frobeniusAnalyticFactor uses canonical frobeniusCoeff, with proved defining/center API. summable_frobeniusCoeff_of_nonresonant and analyticOnNhd_frobeniusAnalyticFactor give convergence and analyticity on the full coefficient disc under only I(alpha+n)!=0 for n>=1. frobeniusAnalyticFactor_isLinearODE2SolutionOn and frobeniusAnalyticFactor_exp_log_isLinearODE2SolutionOn give both the principal slit and any supplied analytic logarithm branch. Largest-root and non-positive-integer-difference specializations follow from the indicial factorization frobenius_indicial_shift. Existing frobenius_solutions / frobenius_log_solution retain the two-root basis and resonant logarithm statements.

## K-2.12 — resonant local basis (Theorem 2.4, p. 23).

Existing admitted local basis targets: `DLMF.AsymptoticApproximations.frobenius_solutions` and `frobenius_log_solution`. The latter normalizes the repeated-root logarithmic coefficient to one and does not assert it nonzero for distinct resonant roots.

## K-2.13 — infinity exponents (§2.5, pp. 24–25).

Existing reciprocal-coordinate classification: `Complex.linearODEReciprocalCoeff`, `Complex.LinearODEAtMostRegularAtInfinity`. The convention z^(-α) is a coordinate convention, and follows directly from t=1/z on a correlated logarithmic branch.

## K-3.01 — Fuchsian equation (§3.1, pp. 29–31).

New canonical Complex.LinearODEFuchsian (all finite points and infinity at most regular) has proved iff, constructor and finite/infinity projections in FuchsianClassification. The rational coefficient representation is exists_partial_fractions_of_linearODEAtMostRegularAtInfinity with explicit analytic complement and finite weighted germs. Polynomial.simplePoleNumerator is the common-denominator simple-residue numerator; no second Fuchsian definition is introduced locally in DLMF.

## K-3.02 — infinity regular singular (Theorem 3.1, p. 32).

New Complex.exists_analytic_weighted_partial_fractions_at gives both finite indicial coefficient values. exists_analytic_reciprocal_partial_fractions gives the infinity product and exponent sum, and fuchs_relation_of_infinity_indicial proves their algebraic relation. Polynomial.simplePoleNumerator, sum_div_sub_eq_eval_simplePoleNumerator_div_prod, natDegree_simplePoleNumerator_le_of_sum_eq_zero and coeff_simplePoleNumerator_sub_two_of_sum_eq_zero give exactly R/psi, degree<=n-2 and coefficient of z^(n-2). Synopsis revision: that coefficient is not necessarily the leading coefficient if degree drops; example a=(0,1,2), f=(1,-2,1) gives R=2 but sum(a*f)=0. SYNOPSIS unchanged; root notified for RevisionNotes.

## K-3.03 — infinity ordinary (Theorem 3.2, pp. 34–35).

New Complex.linearODEOrdinaryAtInfinity_partial_fractions_iff gives exactly the four moment constraints. linearODEOrdinaryAtInfinity_partial_fractions_iff_isBigO gives the equivalent p=2/z+O(z^-2),q=O(z^-4) for these rational germs, in every direction at infinity. Analyticity of the rational germs is retained for the converse.

## K-3.04 — Fuchs relation (Comment 3.1, p. 36).

New proved `Complex.fuchs_relation_of_infinity_indicial`, with n finite points and the infinity pair. Inserting an ordinary marked point adds exponents 0,1 and increases the point count by one, preserving the relation by arithmetic.

## K-3.05 — displacement of exponents, repaired target (Theorem 3.3, pp. 36–37).

Existing DLMF.Heun.isLinearODE2On_gauge_mul gives the exact transformed coefficients; new Complex.linearODEAtMostRegularAt_gauge_partial_fractions gives the corrected at-most-regular preservation. Proved Complex.indicial_gauge_shift identifies the transformed indicial polynomial as I(r+rho), so finite roots shift by -rho. At infinity use rho=-sum local gauge exponents, giving the opposite sum shift. The false stronger strict-singularity-preservation claim is not admitted.

## K-3.06 — accessory parameters (§§3.1–3.3).

New LinearMap.weightedMomentPair is the genuine finite residue moment map f -> (sum f,sum a*f), with proved evaluation and kernel iff. weightedMomentPair_surjective and finrank_ker_weightedMomentPair give rank two and dimension card-2 whenever two marked points differ. exists_weightedMomentPair_eq and weightedMomentPair_eq_iff_sub_mem_ker identify every inhomogeneous fiber as a translate of that kernel. The two constraints therefore leave exactly the source's accessory freedom.

## K-4.01 — no everywhere ordinary scalar equation (§4.1, p. 43).

New target `Complex.not_linearODEOrdinaryAt_everywhere_and_infinity`.

## K-4.02 — one singularity (§4.1, pp. 43–44).

New Complex.eq_zero_of_entire_linearODEAtMostRegularAtInfinity gives p=q=0 for the infinity-only case. For a single finite marked point, linearODEOrdinaryAtInfinity_partial_fractions_iff forces p=2/(z-a),q=0. Their bases are explicitly (1,z), W=1, and (1,1/(z-a)), W=-1/(z-a)^2, respectively. The existing isFundamentalPair_of_wronskian_ne_zero / isFundamentalPair_tfae then gives exactly Az+B and A/(z-a)+B on any connected ordinary domain; this is a simple substitution into the existing fundamental-pair theorem.

## K-4.03 — two singularities (§4.2.1, p. 45).

Complex.euler_equation_cpow/euler_equation_cpow_mul_log and their Wronskians/basis theorems give the principal branches. New euler_equation_exp_log, euler_equation_exp_log_mul_log, wronskian_exp_log, wronskian_exp_log_mul_log, existsUnique_euler_solution_exp_log_linear_combination and existsUnique_euler_solution_exp_log_mul_log_linear_combination give every supplied analytic logarithm branch on a connected open domain, including uniqueness of constants. Under reciprocal coordinates z=1/t, exp(alpha*Log z) becomes exp(-alpha*Log t) on correlated lifts, giving infinity exponents -alpha,-beta.

## K-4.04 — two finite singularities (§4.2.2, (4.1), pp. 46–47).

Existing DLMF.AlgebraicAnalytic.isLinearODE2SolutionOn_comp_eta_iff gives the pullback coefficient identity. New Complex.mobius_euler_equation_exp_log gives the explicit chosen-log power solution; exists_mobius_euler_linear_combination and exists_mobius_euler_log_linear_combination give the complete distinct/repeated-root bases on connected branch domains. linearODEOrdinaryAtInfinity_mobius_euler states ordinary infinity. The selected analytic logarithm is supplied rather than silently imposing an unrelated principal cut.

## K-4.05 — coalescence (§4.2.3, pp. 47–48).

New Complex.tendstoLocallyUniformlyOn_coalescing_euler_coefficients gives both scaled limits; fixed exponents are k=0. inverse_exponential_equation supplies the two exact solutions, wronskian_inverse_exponentials gives W=2*i*k/(z-a)^2 and exists_inverse_exponential_linear_combination gives the full fundamental-pair classification for k!=0. linearODEIrregularAt_inverse_fourth_power gives strict irregularity. All statements are in DLMFMathlib.Analysis.ODE.EulerEquation.

## K-4.06 — Gauss normal form (§4.3.1, (4.3), pp. 49–50).

DLMF.Hypergeometric.coefficients_eq_gauss_of_regularSingular classifies normalized 0,1,infinity coefficient germs, and Complex.eq_papperitz_coefficients_of_regularSingular gives the general finite triple. New exists_linearMap_bijOn_riemannSolutions_gauss supplies the actual complex-linear bijection on arbitrary open branch domains using the explicit cross-ratio and power gauge, with A=alpha1+beta1+gamma1, B=alpha1+beta1+gamma2, C=1+alpha1-alpha2. Zero extension outside the domains makes the solution-space bijection injective; no unnecessary nonresonance assumption is imposed.

## K-4.07 — derivative raises all parameters (Lemma 4.1, p. 50).

Existing general derivative equation `DLMF.Hypergeometric.gaussOperator_iteratedDeriv` specializes at derivative order one to the raised Gauss parameters.

## K-4.08 — Papperitz representation (§4.3.2, (4.4), pp. 50–51).

New Complex.eq_papperitz_coefficients_of_regularSingular states the complete uniqueness classification from three finite marked exponent pairs and ordinary infinity, including the derived exponent-sum relation. Its cyclic Fin3 formula is exactly the zeroth-order coefficient of the existing DLMF.Hypergeometric.riemannOperator, with p fixed by the same residues. Analytic complement hypotheses exclude arbitrary totalized point spikes away from the marked points.

## K-4.09 — Möbius covariance (Theorem 4.1, pp. 52–55).

Existing riemann_mobius_covariance supplies the pointwise coefficient/operator identity. New DLMF.Hypergeometric.exists_linearMap_bijOn_riemannSolutions_mobius packages the complex-linear bijection of supported solution sets on arbitrary open domains; exists_linearMap_bijOn_riemannNormalSolutions_gauge supplies the exponent gauge, and exists_linearMap_bijOn_riemannSolutions_gauss gives the normalized reduction. The matrix determinant need only be nonzero.

## K-4.10 — four singularities (§4.4, (4.10)–(4.11), pp. 56–58).

Canonical Heun definitions/exponents already exist. New DLMF.Heun.existsUnique_heun_coefficients_of_regularSingular identifies arbitrary normalized three-finite/one-infinite Fuchsian germs with canonical heunCoeffP / heunCoeffR, derives the balance relation and gives the unique accessory value for each fixed equation. Generic LinearMap.finrank_ker_weightedMomentPair on three marked points gives the one-dimensional residue freedom. General four-point Mobius/gauge covariance remains existing Heun transformation API.

## K-5.01 — normalized series (Theorem 5.1, pp. 63–65).

Mathlib ordinaryHypergeometric/ordinaryHypergeometricSeries, ordinaryHypergeometricSeries_radius_eq_one and ordinaryHypergeometric_radius_top_of_neg_nat₁ and ordinaryHypergeometric_radius_top_of_neg_nat₂ supply series/radius. Local hasFPowerSeriesOnBall_ordinaryHypergeometric plus Mathlib HasFPowerSeriesOnBall.tendstoLocallyUniformlyOn gives the precise local uniform convergence. gaussHypergeometricCoeff_recurrence, ordinaryHypergeometric_ode and eq_ordinaryHypergeometric_of_gaussOperator give recurrence/ODE/uniqueness. conditional_convergence_on_circle and divergence_on_circle give the nonabsolute unit-circle cases; generalizedHypergeometric_unit_absolute_iff and summable_norm_generalizedHypergeometricCoeff_iff specialize to upper multiset{a,b},lower{c}. ordinaryHypergeometric_eq_sum_neg_nat is the explicit terminating polynomial: its coefficient at N is (-1)^N*(b)_N/(c)_N, so degree=N exactly when (b)_N is nonzero; if it vanishes the finite product shows earlier upper termination. This is a direct finite-product calculation, including N=0.

## K-5.02 — derivative and elementary special cases (§§5.2–5.3, pp. 66–68).

Existing derivatives: `DLMF.Hypergeometric.iteratedDeriv_regularizedGaussHypergeometric`, with Gamma normalization to ordinary admissible F; zero upper parameter `ordinaryHypergeometric_zero_left`; binomial specialization `ordinaryHypergeometric_eq_one_sub_neg_cpow`; logarithmic specialization `log_one_add_eq_ordinaryHypergeometric` after substituting -z. Continued-domain versions use the project principal Gauss function, not the totalized series outside its disc.

## K-5.03 — symmetry and Euler transformation (§§5.2,5.4–5.5).

Existing `DLMF.Hypergeometric.ordinaryHypergeometric_symm` and principal-continuation Euler transformation `regularized_euler`. Recover ordinary normalization under admissible c by multiplying Γ(c).

## K-5.04 — lower-parameter recurrence, repaired target (Lemma 5.1, p. 69).

Existing exact corrected relation: `DLMF.Hypergeometric.regularizedGaussHypergeometric_contiguous_c_three`. Multiplication by Γ(c) and Γ(c)=(c-1)Γ(c-1), Γ(c+1)=cΓ(c), followed by division by c-1, gives the displayed formula including its factor z. No false printed equation is introduced.

## K-5.05 — contiguous relation (Lemma 5.2, p. 71).

Existing `DLMF.Hypergeometric.regularizedGaussHypergeometric_contiguous_a_pred_c_succ`. Multiplying by cΓ(c) converts exactly to the ordinary displayed identity.

## K-5.06 — Kummer's 24 local solutions (Theorem 5.2, pp. 73–76).

New DLMF.Hypergeometric.KummerPermutations formalizes the exact finite algorithm: exponents is the three exponent pairs; coordinate selects the six normalized maps according to a Perm(Fin3); parameters constructs A,B,C from the two Bool exponent choices; gauge and solution are actual functions. gaussOperator_solution supplies the equation on each explicit common branch domain, card_indices proves the symbolic count24, and solution_eq_ordinary gives the exact ordinary normalization only for C regular and norm(Tz)<1. Existing zero_second_representations, one_first_representations, one_second_representations, kummer_five_representations and kummer_six_representations identify the classical alternative families. Exceptional C values do not imply equality of independent finite totalizations: the canonical regularized family still solves the equation, while appropriate logarithmic bases are supplied by the general Frobenius targets K2.12; coherent parameter limits are given by PrincipalConnections. New KummerSeedForms gives the literal six normalized source seeds and all four Euler/Pfaff forms, including the negative-axis infinity normalization excluded by the generic gauge domain. Its proved fourForms_eq_first/expression_eq_first and card_indices, plus analyticOnNhd_and_gaussOperator_expression, identify the actual classical 24 functions on their principal seed domains.

## K-5.07 — Euler integral (Theorem 5.3, p. 77).

Existing DLMF.Hypergeometric.regularizedGaussHypergeometric_eq_regularizedGaussHypergeometricIntegral gives the full principal cut-plane Euler integral under Re b>0 and Re(c-b)>0. Its definition regularizedGaussHypergeometricIntegral is exactly the displayed integral divided by Gamma(b)Gamma(c-b); multiplying by Gamma(c) recovers the ordinary book normalization. intervalIntegrable_eulerKernel records absolute convergence. The unit-disc bridge is ordinaryHypergeometric_eq_Gamma_mul_regularizedGaussHypergeometric.

## K-5.08 — unit-argument value (Corollary 5.1, p. 78).

Existing exact DLMF.Hypergeometric.gauss_summation assumes precisely admissible c and Re(c-a-b)>0, with the Gamma denominator interpreted by totalized reciprocal Gamma factors. The endpoint series realization is ordinaryHypergeometric_one_eq_tsum.

## K-5.09 — transformed Euler integral (Corollary 5.2, p. 79).

New DLMF.Hypergeometric.integrableOn_transformedEulerKernel and regularizedGaussHypergeometric_eq_integral_Ioi_one give the exact 1-to-infinity kernel with exponents a-c,c-b-1,-a on the entire principal cut plane, including its absolute convergence. Multiplication by Gamma(c) gives the book normalization. This differs from the existing 0-to-infinity integral_Ioi kernel.

## K-5.10 — Pfaff transformation (Lemma 5.3, p. 79).

Existing DLMF.Hypergeometric.regularizedGaussHypergeometric_pfaff in ArgumentContinuation gives exactly the principal cut-plane identity for all parameters, including exceptional lower parameters in the regularized normalization. For admissible c, multiplication by Gamma(c) gives the ordinary identity; the transformed argument z/(z-1) stays in cutPlane by div_sub_one_mem_cutPlane.

## K-5.11 — Barnes representation (Theorem 5.4, pp. 80–84).

New Complex.BarnesContour records an actual finite piecewise-C1 deformation with upward vertical tails, pole avoidance and relative winding indices; nonempty_barnesContour supplies existence for disjoint opposite pole families. New DLMF.Hypergeometric.regularizedGaussHypergeometric_eq_barnesContour gives the complete representation, isIntegrable_barnesIntegrand gives absolute convergence, and tendstoLocallyUniformlyOn_barnesContour gives locally uniform truncation on the full stated cut. Coincident same-side upper poles are permitted, so no unnecessary noninteger a-b restriction is imposed.

## K-5.12 — Barnes convergence and residues (Lemmas 5.4–5.5, pp. 80–84).

New DLMF.Hypergeometric.exists_norm_barnesIntegrand_vertical_le states the explicit uniform polynomial/exponential vertical-tail bound, retaining norm(z)^sigma. isIntegrable_barnesIntegrand and tendstoLocallyUniformlyOn_barnesContour give absolute and local uniform convergence. hasSum_barnesContour_right_residues separately gives the right-closing Gamma-coefficient residue series for norm(z)<1. The individual Gamma(-s) residue follows from Mathlib Complex.tendsto_add_natCast_mul_Gamma under s↦-s, producing (-1)^(n+1)/n!.

## K-5.13 — binomial Barnes integral (Corollary 5.3, p. 84).

New DLMF.Gamma.Gamma_mul_one_sub_cpow_neg_barnesContour states the arbitrary finite-deformation binomial Barnes representation, with exact Gamma(a) and 1/(2pi i) normalization. isIntegrable_barnes_binomial separately gives absolute convergence on the full negative-argument slit cut.

## K-5.14 — connection at infinity (Theorem 5.5, pp. 84–86).

New DLMF.Hypergeometric.regularizedGaussHypergeometric_connection_inv is the full principal-cut formula with its sine factor cleared. regularizedGaussHypergeometric_eq_connection_inv divides it at noninteger a-b, yielding exactly the two book Gamma coefficients after reflection. The argument domain is -z in slitPlane; both z and 1/z then have their proper principal continuations. tendsto_connection_inv independently states the removable limit of the combined expression at every parameter, including integer upper differences; separate divergent summands are not assigned finite values.

## K-5.15 — Barnes first lemma (Lemma 5.6, pp. 86–88).

New DLMF.Gamma.barnes_first_lemma_contour gives exactly the four-Gamma quotient for every Complex.BarnesContour separating the two left and two right pole families. isIntegrable_barnes_first supplies absolute convergence. The contour existence theorem allows arbitrary admissible parameter real parts, beyond the straight-line separating-strip case.

## K-5.16 — connection between zero and one (§5.6.1, pp. 89–90).

New DLMF.Hypergeometric.regularizedGaussHypergeometric_connection_one_sub gives the cleared principal formula on z,1-z in cutPlane, exactly the plane cut along (-infinity,0] and [1,infinity). regularizedGaussHypergeometric_eq_connection_one_sub gives its nonresonant quotient, and tendsto_connection_one_sub separately acquires the whole-expression removable parameter limits at resonances. Multiplication by Gamma(c) gives the ordinary book normalization at admissible c.

## K-5.17 — quadratic change (§5.7, pp. 91–92).

Existing DLMF.Hypergeometric.gauss_quadratic in FurtherTransformations.Quadratic is exactly the displayed near-zero quadratic identity, with the component conditions norm(z)<1,norm(4z(1-z))<1,Re z<1/2. These all hold on a neighborhood of zero. Continuing the two germs along compatible lifted quadratic branches preserves the identity by uniqueness of analytic continuation; no independent principal-branch assertion outside that common domain is made.

## K-5.18 — quadratic transformation (Lemma 5.7, p. 92).

Existing DLMF.Hypergeometric.quadratic_half_sum in FurtherTransformations.Cubic is the exact source formula after substituting u=(1-z)/2. Then 1-2u=z and 4u(u-1)/(1-2u)^2=1-z^(-2), with the same lower parameter (a+b+1)/2. Its norm and right-half-plane restrictions hold on a neighborhood of z=1, fixing z^(-a)=1 there. Analytic continuation preserves this equality only along compatible common branches. The differently named quadratic_reciprocal_sqrt is not used for this entry.

## K-5.19 — Jacobi polynomial definition (§5.8.1, pp. 93–95).

Canonical jacobiExtended is the genuine finite-binomial polynomial continuation for all complex alpha,beta. New DLMF.OrthogonalPolynomials.jacobiExtended_eq_jacobiPolynomialP_of_not_neg_nat gives the full admissible-alpha bridge, not merely Re alpha>-1. Existing jacobiExtended_one, jacobiExtended_neg_one, jacobiExtended_neg and iteratedDeriv_jacobiExtended_self give endpoints, reflection and the leading coefficient multiplied by n!, including vanishing degree at degenerate parameters.

## K-5.20 — Jacobi equation (§5.8.1).

Existing admissible-range equation DLMF.OrthogonalPolynomials.jacobi_differential_equation; new all-parameter jacobiExtended_differential_equation in JacobiContinuation retains the polynomial continuation at exceptional α.

## K-5.21 — generating function (§5.8.2, pp. 96–98).

Existing jacobi_generating_function has Re α,Re β>-1 and real|x|≤1. New exists_hasSum_jacobiExtended_generating handles arbitrary complex α,β,x near t=0; hasSum_jacobiExtended_generating handles all complex parameters and real|x|≤1 throughout|t|<1. Principal branches are normalized at t=0.

## K-5.22 — Rodrigues formula (§5.8.3, (5.25), p. 98).

Existing real admissible Rodrigues formula jacobi_rodrigues; new jacobiExtended_rodrigues covers arbitrary complex parameters for real -1<x<1 with positive-base principal powers and real-variable complex-valued derivatives.

## K-5.23 — orthogonality (Lemma 5.8, pp. 99–100).

Existing DLMF.OrthogonalPolynomials.jacobiPolynomialP_orthogonal gives off-diagonal orthogonality. jacobi_norm_all supplies a denominator regular at degree zero; n=0 is integral_jacobi_weight. For n≥1, jacobi_norm gives the displayed Gamma quotient. The polynomial-continuation bridge agrees on real α,β>-1, so no new normalization is needed.

## K-5.24 — Schläfli integral (Lemma 5.9, p. 101).

New DLMF.OrthogonalPolynomials.jacobiExtended_schlafli_circle gives the positive-circle formula. jacobiExtended_schlafli_contour gives the arbitrary positively oriented simple contour with its filled interior in a branch domain, using analytic logarithms of (1-t)/(1-x) and (1+t)/(1+x) normalized to zero at x. This retains all complex parameters and makes the contour-power correlations explicit.

## K-5.25 — three-term recurrence (Lemma 5.10, p. 103).

Existing jacobi_recurrence and new all-parameter jacobiExtended_recurrence give the cleared identity with n,n+1,n+2, specializing by n→n-1 at n>=1. Canonical jacobiExtended_zero supplies P0=1; new jacobiExtended_degree_one supplies P1=(alpha-beta+(alpha+beta+2)x)/2 at every complex parameter pair. The normalized recurrence with degree-zero removable factors cancelled is mul_jacobiExtended.

## K-5.26 — multiplication matrix ((5.29), p. 104).

New DLMF.OrthogonalPolynomials.JacobiMultiplication.upper/diagonal/lower are the actual rational coefficients with degree-zero removable factors cancelled: A0=2/(alpha+beta+2), B0=(beta-alpha)/(alpha+beta+2), C0=0. mul_jacobiExtended gives the normalized multiplication recurrence with exactly its genuine nonzero denominator assumptions. integral_mul_jacobiExtended_mul_jacobiExtended gives the full weighted tridiagonal matrix at every pair of natural degrees, including zero; jacobi_norm_all supplies each diagonal moment's Gamma value.

## K-6.01 — first-kind normalization ((6.1)–(6.3), pp. 107–108).

Canonical legendreP is the regularized Gauss expression with lower parameter1, hence agrees with the ordinary definition. Existing ODE/value/reflection APIs and legendreP_eq_cpow_mul give the source normalizations. New differentiable_legendreP_degree is proved from the existing joint parameter holomorphy and shows entire degree dependence at every fixed principal-cut argument. Integer degree is the existing legendrePolynomialP normalization; legendrePolynomialP_eq_eval identifies Mathlib's polynomial explicitly.

## K-6.02 — second-kind normalization ((6.4), p. 108).

Canonical Hobson associatedQ nu0 equals Gamma(nu+1)*olverQ nu0. New hasAsymptoticExpansion_associatedQ_zero_order gives the full principal exterior expansion, including vanishing initial reciprocal-Gamma coefficients. associatedQ_zero_order_isEquivalent gives the displayed leading equivalent only when nu+3/2 is not a nonpositive integer and LegendreQRegular holds; otherwise a zero leading coefficient does not give an equivalent. analyticAt_associatedQ_degree, tendsto_associatedQ_degree and meromorphicAt_associatedQ_degree retain regular and pole degree behavior. Existing IsLegendreTransport/legendreTransport_exists/legendreTransport_unique in Continuation.LogarithmicBranches give specified-path continuation off +/-1; no global single-valued continuation on the segment complement is asserted. Qualification: at nu=-3/2 the displayed leading coefficient is zero while Q is nonzero; use the full expansion. Parent records this in RevisionNotes.

## K-6.03 — first Schläfli contour (Theorem 6.1, p. 110).

New DLMF.Legendre.legendreP_schlafli_contour states the full complex-cut branch formula using a positive simple contour enclosing1,z and continuous normalized logarithmic lifts. The curve/interior remains in the branch domain cut at(-∞,-1]. All complex ν are allowed.

## K-6.04 — second Schläfli contour (Theorem 6.2, pp. 112–115).

New associatedQ_zero_order_schlafli_contour gives the figure-eight orientation, lobe order and normalized logarithmic lifts; associatedQ_zero_order_eq_intervalIntegral gives the collapsed integral for Re nu>-1. New tendsto_associatedQ_degree gives continuity at nonnegative integer degrees. Combining that limit with the contour identity in a punctured neighborhood (where sin(pi nu) is nonzero) gives precisely the removable contour quotient. Negative integer degrees are genuine Hobson poles, not removable: tendsto_add_one_mul_associatedQ_degree_neg_one records residue1 at nu=-1. The synopsis's unqualified integer wording is flagged for RevisionNotes, and is not formalized as a false finite limit.

## K-6.05 — real/complex integral combination (Example 6.1, (6.5), pp. 115–118).

New associatedQ_zero_order_eq_mixed_integrals gives the real formula and tail convergence. associatedQ_zero_order_eq_mixed_integrals_complex extends it to z-1 in slitPlane with principal correlated complex roots sqrt(z-cos t),sqrt(z+cosh t), separately stating finite-interval and infinite-tail absolute convergence. It specializes to the source's positive real square roots when z>1.

## K-6.06 — associated equation (§6.3, pp. 119–120).

Existing associated equation and derivative bridges: `DLMF.Legendre.associatedP_nat_order_derivative`, `olverQ_nat_order_derivative`, and `associatedQ_nat_order_derivative`. Real-interval book convention differs by (-1)^m from Ferrers convention; no identification across that sign is assumed.

## K-6.07 — associated Gauss expression ((6.7), p. 120).

Existing associatedP_nat_order_derivative and iteratedDeriv_legendreP give the formula at every complex degree with the canonical correlated branch power. Their prefactor (-1/2)^m*(-nu)_m*(nu+1)_m equals (nu-m+1)_(2m)/2^m by pochhammer_reflect and the finite-product splitting identity. The lower parameter m+1 contributes Gamma(m+1)=m!, so the source's Gamma quotient is interpreted as this polynomial product even at its exceptional degrees. No uncancelled totalized Gamma ratio is introduced.

## K-6.08 — toroidal separation (Example 6.2, pp. 120–121).

Canonical toroidalCoordinates is reused by toroidalCoordinateChart, a structural Euclidean-space bridge. New DLMF.Legendre.inner_fderiv_toroidalCoordinateChart gives all metric coefficients, laplacian_toroidalCoordinateChart gives the Cartesian pullback, and laplace_toroidal_product gives exactly the square-root-prefactored separated harmonic product. associatedP_cosh_differential_equation and olverQ_cosh_differential_equation identify the two associated-Legendre radial functions at cosh(eta); substituting nu=n-1/2 gives nu(nu+1)=n^2-1/4. For integer angular frequencies, periodicity follows from exp(z+2pi*i*k)=exp(z), Mathlib Complex.exp_int_mul_two_pi_mul_I and Complex.exp_add, applied to the two exponential angular solutions; real sine/cosine forms are their linear combinations.

## K-7.01 — first confluence (§7.1, (7.1), pp. 123–125).

Existing DLMF.Confluent.tendsto_ordinaryHypergeometric_add_div_atTop and new tendstoLocallyUniformly_ordinaryHypergeometric_add_div_atTop give the confluence; hasFPowerSeriesOnBall_kummerM / analyticOnNhd_kummerM / kummerM_ode give the normalized entire-in-z solution. New kummer_linearODEAtMostRegularAt_zero, kummer_linearODEOrdinaryAt_zero_iff, kummer_linearODERegularSingularAt_zero and kummer_linearODEIrregularAtInfinity supply exact singularity classification, including the removable a=c=0 case. Its indicial polynomial is r(r-1)+c*r=r(r+c-1), so the origin exponents 0,1-c are a direct algebraic substitution.

## K-7.02 — second local solution ((7.2), pp. 124–125).

Existing DLMF.Confluent.wronskian_kummer_pair gives exactly (1-c)*exp(z)*z^(-c) for the ordinary M pair at noninteger c. The second equation follows by differentiating z^(1-c)*M(a-c+1,2-c,z) twice and substituting kummerM_ode at shifted parameters; the extra terms cancel algebraically. The nonzero Wronskian and DLMF.AlgebraicAnalytic.isFundamentalPair_of_wronskian_ne_zero give the complete solution basis on any connected open branch domain. This uses an explicit product/chain-rule derivation, not a new undefined second function.

## K-7.03 — Kummer transformation and derivatives (Problems 7.1–7.3, p. 138).

Existing DLMF.Confluent.kummerM_kummer_transform and iteratedDeriv_kummerM, with the canonical entire series for admissible c. These are exactly the transformation and all derivative orders.

## K-7.04 — Bessel bridge ((7.4)–(7.5), pp. 125–126).

DLMF.Bessel.besselJ_eq_kummerM gives the stated Kummer bridge at admissible lower parameters. Canonical Complex.besselJ_def / local besselJ_eq_regularized give Jnu(z)=(z/2)^nu times entire regularized0F1(-z^2/4). Dividing by the nonzero power on the slit plane and taking z→0 therefore gives 1/Gamma(nu+1) by continuity at zero, including zero reciprocal-Gamma values. At nu=-n, Mathlib Complex.besselJ_neg_int gives (-1)^n Jn, so its actual nonzero first term has order n, not the invalid generic negative power with zero leading factor. Both cases use the canonical reciprocal-Gamma series.

## K-7.05 — Kummer beta integral (Theorem 7.1, p. 126).

Existing `DLMF.Confluent.kummerM_eq_euler_integral`.

## K-7.06 — Poisson Bessel integrals (Example 7.1, pp. 126–127).

Existing DLMF.Bessel.besselJ_eq_poisson_integral is the source [-1,1] formula for all real arguments and complex order Re nu>-1/2. Root's new besselJ_eq_poisson_exponential extends it to the full principal slit plane. Substituting t=cos(theta), theta in[0,pi], transforms (1-t^2)^(nu-1/2)*dt into sin(theta)^(2nu)*dtheta, with positive real bases in the open interval. Reflection t→-t interchanges the signs in the Fourier exponential, so both printed sign conventions give the same integral.

## K-7.07 — Barnes Kummer integral (Theorem 7.2, p. 127).

New DLMF.Confluent.regularizedHGFun_eq_kummerBarnesContour gives the arbitrary finite-deformation Barnes integral on Re z<0; multiplying by Gamma(c) gives the book normalization. isIntegrable_kummerBarnesIntegrand states absolute convergence, exists_norm_kummerBarnesIntegrand_vertical_le gives the uniform sectorial tail bound and tendstoLocallyUniformlyOn_kummerBarnesContour gives local uniform convergence. Complex.BarnesContour separates -a-n from n and therefore excludes precisely the forbidden opposite pole coincidences.

## K-7.08 — Laguerre definition and Jacobi limit ((7.8)–(7.9), p. 130).

Canonical all-parameter laguerreExtended and jacobiExtended are the genuine finite polynomial continuations. New DLMF.OrthogonalPolynomials.tendstoLocallyUniformly_jacobiExtended_laguerreExtended gives the full complex compact-uniform confluence; tendsto_iteratedDeriv_jacobiExtended_laguerreExtended gives every coefficient through derivatives at zero. Existing laguerreExtended_eq and jacobiExtended_eq_jacobiPolynomialP_of_not_neg_nat identify the ordinary hypergeometric normalizations when admissible. The old pointwise theorem remains an ordinary-normalization statement at exceptional parameters and is not confused with polynomial continuation.

## K-7.09 — Laguerre identities (pp. 130–132).

New DLMF.OrthogonalPolynomials.laguerreExtended_rodrigues holds for all complex alpha on the principal slit, hence on x>0; laguerreExtended_differential_equation, deriv_laguerreExtended, laguerreExtended_recurrence and iteratedDeriv_laguerreExtended_self supply the all-parameter polynomial API. Existing hasSum_laguerreExtended_generating_function gives the generating series, and laguerrePolynomialL_orthogonal together with laguerreExtended_eq gives orthogonality for real alpha>-1. No artificial orthogonality condition is imposed on Rodrigues or the algebraic identities.

## K-7.10 — Hermite definition (§7.1.4, p. 132).

Existing DLMF.OrthogonalPolynomials.hermitePolynomialH_even_eq_laguerrePolynomialL and hermitePolynomialH_odd_eq_laguerrePolynomialL exactly give the physicists' even/odd normalization. Canonical Hermite definition has H0=1,H1=2X.

## K-7.11 — second confluence ((7.10)–(7.11), pp. 132–133).

New DLMF.Confluent.tendstoLocallyUniformly_ordinaryHypergeometric_sqrt_div_atTop gives the second confluence. Mathlib regularizedHGFun ∅{c} times Gamma(c) is the unregularized limit series. Existing DLMF.Bessel.regularized0F1_ode and analyticAt_regularized0F1 give its equation and entireness. New limitFunction_linearODERegularSingularAt_zero / limitFunction_linearODEIrregularAtInfinity give strict classification. limitFunction_second_solution and wronskian_limitFunction_pair give the gauged second solution, its noninteger independence and all-parameter regularized Wronskian. Its analytic-factor equation is regularized0F1_ode at 2-c, a direct substitution retaining the corrected function name.

## K-7.12 — Barnes limit function (Theorem 7.3, pp. 134–135).

New DLMF.Hypergeometric.integrable_limitFunction_barnes, limitFunction_eq_barnes_integral and tendstoLocallyUniformlyOn_limitFunction_barnes give exact Theorem7.3 vertical-line range, absolute convergence, representation and compact-uniform convergence on negative real arguments. No false open-sector absolute-convergence claim is added.

## K-7.13 — Bessel limit-series bridge ((7.13), pp. 136–137).

Mathlib Complex.besselJ uses the reciprocal-Gamma0F1 series directly, so its defining expansion covers all integer exceptional orders. The ordinary0F1/Gamma form follows for admissible ν+1. New limitFunction_eq_barnes_integral specializes at c=ν+1,z=-x²/4 and multiplies by(x/2)^ν/Γ(ν+1), giving the stated Barnes representation with the same sigma condition. This is a direct substitution and cancellation, with x>0 fixing powers.

## K-7.14 — generalized series (§7.4, (7.14), p. 138).

Canonical generalizedHypergeometricCoeff/generalizedHypergeometricSeries and generalizedHypergeometricTruncated give the exact ordinary list coefficient series. GeneralizedHypergeometric.AnalyticProperties provides generalizedHypergeometric_entire and generalizedHypergeometric_hasSum_entire for p<=q (the latter requires LowerParametersRegular); generalizedHypergeometric_radius_one and generalizedHypergeometric_radius_zero give the two other nonterminating regimes. generalizedHypergeometric_terminating_entire and generalizedHypergeometricCoeff_summable_of_terminates cover termination. Finite lists map to multisets preserving multiplicity; finite products are exactly the multiset product definitions. At z=0 all nonconstant terms vanish, including the radius-zero regime.

## K-7.15 — Whittaker gauge (Problem 7.4, pp. 138–139).

Existing DLMF.Confluent.whittakerM and whittakerM_ode give the exact gauge and Whittaker equation. ordinary and regularizedWhittakerM are separate canonical definitions, with regularizedWhittakerM_eq_div_Gamma bridge; ordinary lower-parameter restrictions are retained.

## K-8.01 — equation and symmetries ((8.1)–(8.2), pp. 141–143).

Existing general Heun operator/solutions with q=ab h and transformations `heun_fHomotopic_zero`, `heun_fHomotopic_one`, `heun_fHomotopic_a`, `heun_homography_div`, `heun_homography_mobius`. Degeneration at A=h=1: `DLMF.Heun.heunLocal_one_eq_hypergeometric`. Remaining general permutation-isomorphism packaging is shared with K-4.10.

## K-8.02 — power-series recursion ((8.3)–(8.5), pp. 143–144).

Existing `DLMF.Heun.heunLocalCoeff`, `heunLocalCoeff_rec_zero`, `heunLocalCoeff_rec`, `heunLocal_second_isHeunSolutionOn`, `eventuallyEq_heunLocal_of_analyticAt`. Substitute q=ab h and e=a+b+1-c-d; the displayed coefficients match after expanding heunRecurrenceQ.

## K-8.03 — local existence and convergence (Theorem 8.1, p. 145).

Existing hasFPowerSeriesOnBall_heunLocal / hasSum_heunLocal give the interior normalized solution. New summable_heunLocalCoeff_of_norm_le_one gives absolute unit-boundary convergence under Re d<1. radius_heunLocalCoeff_of_minimal gives exact larger radius abs(A) under the actual minimal ratio limit; summable_heunLocalCoeff_of_minimal_of_norm_le gives its absolute boundary convergence under Re epsilon<1. All new statements are in DLMF.Heun.SeriesBoundary; the larger radius is not asserted for a generic coefficient sequence.

## K-8.04 — generic and minimal coefficient roots ((8.6)–(8.7), pp. 144–146).

New tendsto_heunRecurrenceQ_add_div_R / tendsto_neg_heunRecurrenceP_div_R identify the exact normalized coefficient limits. exists_heunLocalCoeff_ratio_limit gives characteristic ratio 1 or A^-1 and eventual nonzero denominators for a nonterminating normalized sequence when abs(A)>1. Generic Complex.SecondOrderRecurrence.exists_fundamental_pair and tendsto_continuant_ratio_iff_minimal supply the minimality/Pincherle machinery; radius_heunLocalCoeff_of_minimal identifies its larger convergence radius. The exact tridiagonal continuant representation is eq_continuant_mul_initial after the explicit normalization.

## K-8.05 — polynomial criterion (§8.3, p. 146).

New DLMF.Heun.heunLocalCoeff_terminates_iff gives the full exact-degree criterion, and exists_heunPolynomial_iff identifies a genuine normalized polynomial ODE solution. charpoly_heunPolyMatrix_eval_eq gives the exact undivided determinant/next-coefficient identity; charpoly_heunPolyMatrix_isRoot_iff gives the determinant criterion. heunLocalCoeff_two_eq_zero_iff_accessory_quadratic states the exact N=1 accessory equation, without excluding h=0,1,A. Its nonzero alpha*beta hypothesis is necessary to cancel that factor and follows from the exact-degree-one leading coefficient requirement.

## K-8.06 — Jacobi basis for Heun (§8.4, (8.8)–(8.11), pp. 147–148).

New coefficients and exact action targets in `DLMF.Heun.JacobiExpansion`: `upperCoefficient`, `diagonalCoefficient`, `lowerCoefficient`, three derivative coefficients, `mul_basis`, `mul_deriv_basis`; all defining formulas have proved interface lemmas. n=0 is separately normalized.

## K-8.07 — polynomial asymptotics (Lemma 8.1, pp. 148–151).

New DLMF.Heun.JacobiExpansion.basis_ratio_asymptotic gives the exact two-term ratio and eventual nonzero denominator; basis_ratio_asymptotic_uniform gives the same O(n^-2) bound with one constant and threshold on any compact set off the focal segment. Complex.Joukowski.norm_outerInverse_gt_one proves the strict modulus condition. The recurrence denominators and admissible c remain explicit.

## K-8.08 — expansion-coefficient recursion (Lemma 8.2, pp. 151–153).

New `recurrenceDenominator`, `recurrenceFirstCoefficient`, `recurrenceSecondCoefficient`, their proved defining lemmas, `isHeunSolutionOn_iff_recurrence`, `recurrenceFirstCoefficient_zero`, `recurrence_coefficients_asymptotic` in `DLMF.Heun.JacobiExpansion`.

## K-8.09 — two ratio limits (Lemma 8.3, pp. 153–156).

New `DLMF.Heun.JacobiExpansion.coefficient_ratio_asymptotic`; root reciprocal and modulus are represented using `Complex.Joukowski.outerInverse` and its modulus theorem.

## K-8.10 — elliptic convergence domain (Theorem 8.2, pp. 156–158).

New `DLMF.Heun.JacobiExpansion.summable_of_ratio_lt`, `not_summable_of_ratio_gt`, `norm_term_ratio_boundary`, `summable_boundary`. Elliptic locus is `Complex.Joukowski.norm_outerInverse_eq_iff` and `norm_outerInverse_lt_iff`. Terminating sequences converge as finite sums, separately from ratio hypotheses.

## K-8.11 — singly confluent equation (§8.5, (8.17)–(8.18), pp. 158–159).

New DLMF.Heun.tendstoLocallyUniformlyOn_heun_coefficients_sqrt gives both precise coefficient limits, retaining q=ab h and balance-determined e. isLinearODE2On_comp_sq_of_confluentHeun gives the displayed square pullback using the existing canonical IsConfluentHeunSolutionOn with ε=0. It preserves the sign of -4K(h-t²)/(1-t²) and assumes nonsingular pullback points.

## K-8.12 — Lamé, spheroidal and Mathieu equations (§8.6, pp. 159–161).

Exact Lame-Heun bridge: DLMF.Lame.isLameAlgebraicSolutionOn_iff_isHeunSolutionOn, nu=-2a,k^2=A^-1. New EuclideanSpace.prolateSpheroidalCoordinates, prolateSpheroidalCoordinates_cosh_cos, inner_fderiv_prolateSpheroidalCoordinates and laplacian_prolateSpheroidalCoordinates acquire the source chart, its hyperbolic form, metric and Cartesian Laplacian. DLMF.WaveEquation.helmholtz_prolate_product gives the precise angular/radial Helmholtz separation with the prolate spectral signs. Existing DLMF.Spheroidal.Real.isSpheroidalSolution_iff_isSpheroidalFactor gives the gauge, and new DLMF.Heun.isLinearODE2On_spheroidalFactor_of_confluentHeun gives the cancelled source coefficient pullback even at chi=0. Existing isSpheroidalLiouvilleSolution_of_isSpheroidalSolutionOn, spheroidalLiouville_coeff_mathieu and IsSpheroidalLiouvilleSolution.mathieu give the exact mu^2=1/4 Mathieu reduction and parameters.

## K-A.01 — Gamma definition and continuation ((A.1)–(A.3), pp. 163–164).

Mathlib: Complex.Gamma_eq_integral, Gamma_add_one, Gamma_nat_eq_factorial, Gamma_eq_zero_iff, differentiable_one_div_Gamma, tendsto_add_natCast_mul_Gamma. Pinned TauCeti: Complex.meromorphicOrderAt_Gamma_neg_nat and meromorphicOrderAt_Gamma_of_ne_neg_nat in TauCeti.Analysis.SpecialFunctions.Gamma.Order identify exactly the simple poles and no meromorphic zeros. Reciprocal Gamma is entire, with zeros exactly at nonpositive integers by Gamma_eq_zero_iff; its simple-zero order follows by negating the meromorphic order of the inverse. Gamma is totalized to zero at its poles; these germ/order statements retain the mathematical meaning.

## K-A.02 — reflection and duplication ((A.4)–(A.5), pp. 164–165).

Mathlib Complex.Gamma_mul_Gamma_one_sub is the totalized reflection identity, Gamma_mul_Gamma_add_half is duplication, and Gamma_one_half_eq is the exact half value. Solving duplication algebraically gives the displayed Gamma(2z) normalization away from poles; the direct totalized Mathlib identity retains its globally valid domain.

## K-A.03 — log-Gamma and Binet remainder ((A.6), p. 166).

Pinned TauCeti.logGamma provides the analytic log-Gamma branch and logGamma_ofReal; TauCeti.isBigO_logGamma_sub_stirling gives the sectorial O(1/|z|) remainder. New DLMF.Gamma.logGamma_stirling_remainder_eq_integral states the exact Binet logarithmic-kernel integral and absolute convergence for Re z>0. No boundedness near zero is asserted.

## K-A.04 — sine away from its zeros (Lemma A.1, Corollary A.1, pp. 166–168).

New Complex.exists_norm_sin_pi_mul_bounds_of_dist_int and exists_norm_sin_pi_mul_add_bounds_of_dist_int in DLMFMathlib.Analysis.Complex.GlobalLogSineBounds, with positive lower constants, ordered constants and both lattice exclusions explicit.

## K-A.05 — logarithm difference (Lemma A.2, pp. 169–170).

New Complex.exists_abs_re_mul_log_sub_log_le in DLMFMathlib.Analysis.Complex.GlobalLogSineBounds; principal logarithms and the two excluded discs are explicit. The imaginary-part jump is not claimed bounded.

## K-A.06 — global Gamma magnitude (Lemma A.3, pp. 170–172).

New DLMF.Gamma.exists_norm_Gamma_stirling_global_bounds, with the exact principal-argument scale and exclusion of every Gamma-pole disc.

## K-A.07 — shifted Gamma (Corollary A.2, p. 172).

New DLMF.Gamma.exists_norm_Gamma_add_stirling_global_bounds, retaining the original-variable logarithm/argument and the shifted pole exclusions.

## K-A.08 — Gamma-ratio bound (Lemma A.4, pp. 172–173).

New DLMF.Gamma.exists_norm_Gamma_add_div_Gamma_global_bounds. This is a global two-sided magnitude comparison, distinct from a sectorial asymptotic expansion.

## K-A.09 — rising factorial ((A.9)–(A.12), pp. 173–174).

Mathlib Polynomial.ascPochhammer and local DLMF.Hypergeometric.pochhammer with pochhammer_zero, pochhammer_succ, pochhammer_succ_left, pochhammer_neg_coe_nat and pochhammer_reflect give the finite-product identities. Mathlib Complex.Gamma_add_nat_div_Gamma_eq is the admissible natural-index Gamma quotient. Canonical DLMF.Hypergeometric.pochhammerOfInt defines negative indices by reciprocal rising products; proved pochhammerOfInt_eq_Gamma_div supplies the integer-index Gamma quotient, including shifted poles under Lean totalization. No duplicate integer-index family is introduced.

## K-A.10 — rising-factorial asymptotic (Lemma A.5, p. 174).

Parent new DLMF.Gamma.Gamma_ratio_sector_expansion gives the full shifted Gamma quotient with G0=1 and G1=(a-b)(a+b-1)/2. Substitute a=alpha,b=1 and z=n, then multiply by Gamma(alpha)^-1 using Complex.Gamma_add_nat_div_Gamma_eq. This gives exactly (alpha)_n/n! = n^(alpha-1)/Gamma(alpha)*(1+alpha*(alpha-1)/(2n)+O(n^-2)). For alpha=-m the Pochhammer numerator terminates for n>m and reciprocal Gamma is zero, so treat that case by the exact finite-product zero statement rather than cancellation of a Gamma pole.

## K-A.11 — digamma (§A.4, p. 175).

Canonical Mathlib Complex.digamma is the logarithmic derivative. Complex.digamma_apply_add_one is the exact complex recurrence away from nonpositive integers. Local DLMF.Gamma.digamma_eq_cDigammaSeries/hasSum_cDigammaTerm give the partial-fraction series and summableLocallyUniformlyOn_cDigammaTerm gives its local uniform convergence on notNegNat. Real integer values are DLMF.Gamma.Real.digamma_nat_add_one and digamma_one.

## K-A.12 — generalized binomial (§A.5, (A.14)–(A.15), p. 175).

Mathlib Ring.choose is the generalized falling-factorial coefficient. Ring.descPochhammer_eq_factorial_smul_choose and Polynomial.descPochhammer_eq_ascPochhammer give exactly choose(alpha,n)=(-1)^n*(-alpha)_n/n! by evaluation and division by the nonzero factorial. Existing DLMF.Hypergeometric.hasSum_pochhammer_div_factorial with exponent -alpha and argument -z is the binomial series. Complex.Gamma_add_nat_div_Gamma_eq gives the regular-parameter Gamma quotient.

## K-A.13 — beta (§A.6, (A.16)–(A.17), p. 176).

Mathlib Complex.betaIntegral_eq_Gamma_mul_div (Re x,Re y>0) is exactly the beta integral/Gamma quotient. Reflection t↦1-t gives symmetry, and the quotient supplies meromorphic continuation. No duplicate beta definition is needed.

## K-A.14 — Euler constant (§A.7, (A.18), pp. 176–177).

Mathlib Real.eulerMascheroniSeq/eulerMascheroniSeq' are exactly the lower/upper source sequences. strictMono_eulerMascheroniSeq and strictAnti_eulerMascheroniSeq' give monotonicity; tendsto_eulerMascheroniSeq, tendsto_eulerMascheroniSeq', tendsto_harmonic_sub_log_add_one and tendsto_harmonic_sub_log identify their common limit. eulerMascheroniSeq_lt_eulerMascheroniConstant and eulerMascheroniConstant_lt_eulerMascheroniSeq' give the strict bounds for every natural n.

## K-B.01 — second-order sequence.

New `Complex.SecondOrderRecurrence.existsUnique_solution`, `existsUnique_linear_combination`, and proved `casoratian_add_one`. Free initialization and fixed x1=A0*x0 are explicitly distinguished.

## K-B.02 — continuant determinant (Lemma B.1, pp. 179–181).

New `Complex.SecondOrderRecurrence.continuantMatrix`, `continuant`, proved formulas and values `continuant_zero`, `continuant_one`, recurrence target `continuant_add_two`, and `eq_continuant_mul_initial`.

## K-B.03 — remove the leading coefficient (Lemma B.2, p. 181).

New `Complex.SecondOrderRecurrence.div_prod_recurrence`. Initial y0=x0 is an empty-product identity and y1=y0 uses the explicitly imposed original initialization.

## K-B.04 — Poincaré–Perron basis (Theorem B.1, pp. 182–183).

New `Complex.SecondOrderRecurrence.exists_fundamental_pair` states both ratio limits, eventual nonvanishing, nonzero Casoratian, and minimal/dominant ratio tending to zero.

## K-B.05 — generic versus minimal (Theorem B.2, pp. 183–184).

New `Complex.SecondOrderRecurrence.existsUnique_linear_combination`, `tendsto_ratio_linear_combination` and the final minimality limit in `exists_fundamental_pair`. The zero sequence is not forced into a nonzero quotient-limit assertion.

## K-B.06 — Pincherle, repaired target (Theorem B.3, pp. 184–185).

New corrected `Complex.SecondOrderRecurrence.tendsto_continuant_ratio_iff_minimal`; ordinary intermediate denominators are replaced by continuants, with eventual nonzero final denominators for finite convergence. Headed normalization is then the scalar equality L=-A0.

## K-B.07 — summably small coefficient defect (Lemma B.3, pp. 185–189).

New `Complex.SecondOrderRecurrence.exists_limit_of_summable_defect`: limit, quantitative error and summable consecutive differences. Boundedness follows immediately from convergence.

## K-B.08 — product normalization, repaired target (Lemma B.4, pp. 189–191).

New proved Complex.SecondOrderRecurrence.mul_prod_recurrence and mul_prod_initial give the product normalization, and normalized_coefficient_sum supplies the exact c1,c2 formulas. The inverse is the pointwise identity x_n=y_n/product_(j<n)f_j, obtained by division by the nonzero finite product. Since f_n=1+c1/n+c2/n^2 tends to one, its factors are eventually nonzero; restrict to that tail before inversion. This is a finite algebraic derivation, not an assertion that early factors cannot vanish.

## K-B.09 — power asymptotic (Theorem B.4, p. 191).

New `Complex.SecondOrderRecurrence.exists_power_asymptotic`, retaining the source nonzero-limit exclusion.

## K-B.10 — quotient expansion (Corollary B.1, p. 193).

New `Complex.SecondOrderRecurrence.ratio_power_asymptotic`.

## K-B.11 — integral comparison (Lemma B.5, p. 193).

Mathlib AntitoneOn.integral_le_sum_Ico and AntitoneOn.sum_le_integral_Ico in Analysis.SumIntegralComparisons; adding the omitted endpoint gives the Icc version and its lower/upper endpoint bounds. This is a finite-sum reindexing, not a missing analytic theorem.

## K-B.12 — zeta tail (Lemma B.6, pp. 194–195).

DLMF.AsymptoticApproximations.powerSum_asymptotic at alpha=-lambda has scale0 n^(1-lambda) and coefficient0=1/(1-lambda); truncating after it leaves O(n^(-lambda)). Its exact constant is Re(riemannZeta(lambda)). For lambda>1, Mathlib zeta_eq_tsum_one_div_nat_add_one_cpow identifies that value with the convergent real positive zeta series (take real parts). The sum to n-1 differs from the source sum to n by n^(-lambda), which is absorbed into the stated remainder.

## K-B.13 — harmonic asymptotic (Lemma B.7, pp. 195–197).

Existing DLMF.AsymptoticApproximations.harmonic_asymptotic expands H_(n-1)-log n-γ with leading -1/(2n); adding 1/n gives the synopsis +1/(2n) and truncating before order2 gives O(n^-2). The exact remainder theorem harmonic_remainder_bound is stronger.

## K-B.14 — weighted geometric convolution (Lemma B.8, pp. 197–199).

Complex.SecondOrderRecurrence.weighted_geometric_convolution gives the stronger O(1/n) error, hence the stated limit. New weighted_geometric_convolution_succ separately records the exact finite-sum recurrence for n>=1, and eventually_norm_weighted_geometric_multiplier_le gives an eventual contraction factor r with c<r<1.

## K-C.01 — rational decomposition.

Mathlib Polynomial.mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse and quo_add_sum_rem_mul_pow_inverse_unique give the algebraic factorwise decomposition. New Polynomial.eval_div_eval_eq_quotient_add_partialFractions transfers it to actual complex rational functions with an arbitrary nonzero leading constant, exact derivative coefficients and canonical polynomial quotient. existsUnique_partialFractionCoefficients gives uniqueness in the natural dependent finite coefficient family. tendsto_eval_mod_div_eval_cobounded states that the proper remainder vanishes in every complex direction at infinity, including a constant denominator.

## K-C.02 — coefficients of principal parts.

New Polynomial.partialFractionCofactor is the actual denominator with the selected root factor removed, retaining the leading scalar. partialFractionCoefficient is exactly D^(m_i-j-1)(p/cofactor)(a_i)/(m_i-j-1)! for denominator power j+1. Its defining/evaluation/top-coefficient APIs are proved. analyticAt_div_partialFractionCofactor supplies the cancelled germ's analyticity, and eval_div_eval_eq_quotient_add_partialFractions identifies these Taylor derivatives with every principal-part coefficient.

## K-D.01 — complex circle equation ((D.1)–(D.2), p. 203).

New Complex.norm_sub_eq_radius_iff is the conjugate circle equation including radius zero. For the converse substitute center c=-beta and radius sqrt(norm(beta)^2-gamma) into that same equivalence, use alpha=star(beta), real gamma and Real.sq_sqrt of the assumed nonnegative radicand. This is a direct algebraic substitution; no additional circle definition or theorem is needed. Radius zero gives precisely the singleton center.

## K-D.02 — Apollonius circles ((D.3), p. 204).

New Complex.norm_sub_eq_mul_norm_sub_iff gives the exact center and radius for k!=1; norm_sub_eq_norm_sub_iff_re gives the perpendicular bisector for k=1. If c=(a-k²b)/(1-k²), r=k*norm(a-b)/abs(1-k²), direct subtraction and norm multiplication give norm(a-c)=k*r and norm(b-c)=r/k. With a!=b,k>0,k!=1 one has r>0, so the stated interior-focus conclusions follow immediately for k<1 and k>1, respectively.

## K-D.03 — elliptic level set (Lemma D.1, pp. 205–208).

New Complex.Joukowski.outerInverse and its proved defining API, norm_outerInverse_gt_one, norm_add_norm_sub_one, norm_outerInverse_eq_iff and norm_outerInverse_lt_iff give the exact off-segment locus and interior comparison. New focalRatio is the actual continuous extension L-sqrt(L²-1), L=norm(z)+norm(z-1), with proved continuous_focalRatio and focus values. focalRatio_eq_inv_norm_outerInverse identifies the original rho; focalRatio_eq_one_iff / focalRatio_pos_and_le_one / focalRatio_gt_iff include the whole segment in the ellipse interior.

## K-D.04 — Joukowski parametrization (pp. 157–158, Appendix D).

New `Complex.Joukowski.ellipseParametrization`, proved formula, `ellipseParametrization_coordinates`, `exists_ellipseParametrization_iff`. The stated semiaxes and focal locations follow directly from these formulas.
