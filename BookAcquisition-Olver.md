# Olver statement acquisition ledger

The approved follow-up has corrected this book’s SYNOPSIS and ERRATA records.
The acquisition evidence below is retained as a historical audit; references to
unchanged synopsis text or blocked defective variants describe that snapshot.
Current per-item dispositions are in BookAcquisition-RevisionNotes.md.

This working inventory includes every stable entry of `SYNOPSIS-Olver.md`. Existing statements may be admitted. A related weaker result is recorded as partial coverage; it does not certify a source theorem. Explicit outstanding subclaims are retained until acquired.

## O-1.01 — integration-by-parts example (§1, pp. 1–4).

Acquired finite identities and strict bounds in `Real.integral_exp_neg_mul_cos_eq_sum_add`, `Real.integral_exp_neg_mul_div_one_add_remainder`, and fixed-argument divergence `Real.tendsto_factorial_div_pow_atTop` (all new admitted, `DLMFMathlib.Analysis.Asymptotics.ElementaryLaplaceRemainders`). Exact cosine transform is proved upstream `TauCeti.integral_Ioi_exp_neg_mul_mul_cos`, frequency 1, with its accompanying absolute-integrability API. Existing divergent asymptotic prototype remains `DLMF.AsymptoticApproximations.hasAsymptoticExpansion_laplace_inv_one_add`.

## O-1.02 — order calculus (§§2–3, pp. 4–8).

Order calculus is the proved Mathlib `Asymptotics.IsBigO`, `IsLittleO`, `IsEquivalent` API. New proved complex-power comparisons `Complex.isLittleO_ofReal_cpow_exp_atTop` and `Complex.isLittleO_log_ofReal_cpow_atTop` reduce by `Complex.norm_cpow_eq_rpow_re_of_pos` to upstream root-level `isLittleO_rpow_exp_atTop` / `isLittleO_log_rpow_atTop`. Explicit exponentiation counterexample `Real.isEquivalent_add_one_and_not_exp` is newly admitted in `PowerGrowthCounterexamples`; the pair is x+1,x.

## O-1.03 — convergent-series tails (Theorem 3.1, p. 7).

Closed-disc coefficient and tail bounds acquired as `Complex.exists_coeff_bound_and_norm_tsum_tail_le` (new admitted, `DLMFMathlib.Analysis.Complex.UniformPowerSeriesTail`), for arbitrary complex Banach-valued coefficients and intermediate radius. Existing local-asymptotic corollary is `DLMF.AsymptoticApproximations.tsum_tail_isBigO_pow`.

## O-1.04 — integration of equivalents (§4.1, (4.01)–(4.02), pp. 8–9).

Existing equivalent-integral statements: `DLMF.AsymptoticApproximations.integral_Ioi_isEquivalent_of_isEquivalent_cpow`, `exists_tendsto_intervalIntegral_of_isEquivalent_cpow`, `intervalIntegral_isEquivalent_log`, `intervalIntegral_isEquivalent_cpow`. Explicit local-L1 O/o power and logarithm primitives, tail integrability and little-oh power tail acquired as `Asymptotics.IsBigO.intervalIntegral_rpow`, `.intervalIntegral_log`, `.integrableOn_Ioi_of_rpow`, and `Asymptotics.IsLittleO.intervalIntegral_rpow`, `.intervalIntegral_log`, `.integral_Ioi_rpow` (six new admitted, `IntegralMajorants`). Existing proved `Asymptotics.IsBigO.integral_Ioi_rpow` supplies the Big-O tail. The excluded complex boundary is not asserted.

## O-1.05 — monotone differentiation (Theorem 4.1, p. 9).

New target `Asymptotics.deriv_isEquivalent_rpow_of_monotone` in DLMFMathlib.Analysis.Asymptotics.MonotoneDerivative.

## O-1.06 — holomorphic differentiation (Theorem 4.2, pp. 9–10).

Existing proved first-derivative `DLMF.AsymptoticApproximations.ritt_isBigO`, `ritt_isLittleO`. Arbitrary derivative order and explicit Cauchy constants acquired in `Complex.norm_iteratedDeriv_le_of_sector_bound`, `Complex.isBigO_iteratedDeriv_of_sector`, `Complex.isLittleO_iteratedDeriv_of_sector` (new admitted, `HigherSectorDerivatives`), with strictly interior angular margins.

## O-1.07 — real inverse asymptotic (Theorem 5.1, p. 13).

Existing `DLMF.AsymptoticApproximations.existsUnique_root_of_isEquivalent` and `root_isEquivalent`; new quantitative full-real-exponent inverse error `Real.existsUnique_root_and_error_le_of_isEquivalent` (admitted, `RealInverseError`).

## O-1.08 — analytic inverse on nested sectors (Theorem 6.1, pp. 14–16).

Acquired `Complex.exists_analytic_inverse_of_isEquivalent_sector` (new admitted, `SectorInverse`): common radii, unique root in intermediate closed sector, analytic inverse on smaller closed sector and uniform inverse equivalence. All three sectors lie on the specified rotated single sheet.

## O-1.09 — Poincaré expansion (§7.1, p. 16).

Existing canonical `DLMF.AsymptoticApproximations.HasPoincareExpansion` and `HasUniformPoincareExpansion`, underlying `Asymptotics.HasAsymptoticExpansion`. Prefactors are division/scaling and must be eventually nonzero.

## O-1.10 — coefficient recovery and uniqueness (Theorem 7.1 and its corollaries, p. 17).

Coefficient recovery at **every** order is already precisely the proved tagged `DLMF.AsymptoticApproximations.hasPoincareExpansion_iff_tendsto` (Basics/OrderSymbols, not merely its first-coefficient special case). Coefficient uniqueness is `Asymptotics.HasAsymptoticExpansion.unique` with a nondegenerate scale. The lower bound for a remainder constant is the checked one-line `le_of_tendsto h.norm hb` applied to that coefficient-recovery limit and the eventual normalized remainder bound; this derivation was Lean-checked in /tmp/Olver-bound-check.lean. Exponentially small nonuniqueness is `DLMF.AsymptoticApproximations.cexp_neg_isLittleO_one_sector`.

## O-1.11 — full-neighborhood convergence (Theorem 7.2, pp. 18–19).

Acquired `Complex.hasSum_laurent_of_hasAsymptoticPowerSeries` (new admitted, `ExteriorLaurentAsymptotics`), including arbitrary integer leading power, equality everywhere on the entire original exterior disk, and local normal convergence there.

## O-1.12 — divergent sector expansion (Theorem 7.3, p. 19).

Acquired `Complex.angle_lt_pi_and_not_meromorphicAt_inv_of_divergent_expansion` (new admitted, `ExteriorLaurentAsymptotics`). The theorem explicitly assumes holomorphy on the full deleted neighborhood of infinity, as the source does, and an everywhere-divergent coefficient series. The half-angle is strictly below pi; non-meromorphy after inversion records the essential singularity.

## O-1.13 — algebra of asymptotic series (§8, pp. 19–22).

Existing `Asymptotics.HasAsymptoticPowerSeries.add`, `mul`, `recip`, `comp`, `analytic_comp` and principal-branch `cpow` / `log` supply algebra and analytic composition. Explicit named coefficient recurrences acquired using canonical Mathlib `PowerSeries.logOf`: `PowerSeries.natCast_mul_coeff_logOf` and `PowerSeries.coeff_inv_eq_sum_Icc` (new admitted, `LogarithmicRecurrence`). Reciprocal recurrence is the finite-Icc indexing of proved upstream `PowerSeries.coeff_inv`.

## O-1.14 — integration, differentiation and inversion (§8.2–8.4, pp. 20–22).

Integrated logarithm and integration constant acquired in `Asymptotics.HasAsymptoticExpansion.exists_intervalIntegral_inv_pow` (new admitted, `PrimitiveExpansion`), with local integrability and all-order integrated remainder. Existing holomorphic differentiation `DLMF.AsymptoticApproximations.HasPoincareExpansion.deriv`, inverse theorem `lagrange_reversion_of_isEquivalent`, and canonical `Asymptotics.mcMahonSeries_spec` give inversion. Fourth coefficient added as `Asymptotics.mcMahonSeries_coeff_three` (new admitted, `McMahonCoefficients`). **Synopsis revision required:** printed p.21 has forward ζ=z+sum a_n/z^n and inverse z=ζ−sum b_n/ζ^n. Synopsis changes both signs while retaining b2=a0*a1+a2; false for a0=a1=1,a2=0, whose stated minus-forward inverse has b2=−1. New target uses source-correct signs; SYNOPSIS left unchanged.

## O-1.15 — prescribed asymptotic sums (§9, pp. 22–24).

Existing real-ray and principal closed-sector Borel–Ritt targets are supplemented by `Asymptotics.exists_hasAsymptoticExpansion_inv_pow_region` and `Asymptotics.exists_analytic_cutoff_sum_log_sector` (new admitted, `PrescribedSeries`). The latter states the explicit analytic cutoff summands, local normal convergence, analyticity and all-order expansion on any bounded logarithmic argument strip, including widths above 2pi; zero coefficients are omitted.

## O-1.16 — general scales and uniform expansions (§10, pp. 24–26).

Canonical general scale and expansion definitions/API are `Asymptotics.IsAsymptoticScale`, `HasAsymptoticExpansion`, `.unique`; generalized and uniform definitions are `DLMF.AsymptoticApproximations.HasGeneralizedAsymptoticExpansion` and `HasUniformPoincareExpansion` in Basics/Basic. Multiplication acquired as `Asymptotics.HasAsymptoticExpansion.mul_of_compatible_scale` (new admitted, `CompatibleProductScale`), explicitly requiring phi0=1 and multiplicative scale compatibility, rather than asserting arbitrary-scale multiplication.

## O-1.17 — variation (§11, pp. 27–29).

Mathlib eVariationOn is the canonical supremum over ordered finite partitions. Exact APIs: eVariationOn.sum_le / eVariationOn_eq_strictMonoOn, eVariationOn.Icc_add_Icc, eVariationOn.edist_le, MonotoneOn.eVariationOn_eq, BoundedVariationOn.exists_tendsto_left / exists_tendsto_right / exists_tendsto_atTop. TauCeti.eVariationOn_eq_lintegral_enorm_derivWithin (Analysis/Calculus/MetricVariation) supplies the C1 integral formula, including complex values; apply it to f composed with each C1 path piece and use interval additivity for the piecewise path formula. No new duplicate variation definition is required.

## O-2.01 — analytic parameter integrals (Theorem 1.1, pp. 31–32).

Exact source scope is acquired by `Complex.differentiableOn_and_tendstoLocallyUniformlyOn_integral_iteratedDeriv` (new admitted, DLMFMathlib.Analysis.Complex.ImproperParameterIntegral, also Temme Theorem2.3). It accepts arbitrary cutoff filters approaching finite/infinite endpoints, joint continuity, parameter holomorphy and local uniform convergence; it concludes holomorphy and local uniform convergence of every derivative integral, without imposing absolute domination.

## O-2.02 — Gamma and Euler limit (§1.1–1.3, pp. 31–34).

Proved Mathlib `Complex.Gamma_eq_integral`, `Gamma_add_one`, `Gamma_nat_eq_factorial`, `GammaSeq_tendsto_Gamma`, `Gamma_ne_zero` and `Gamma_eq_zero_iff` give Euler integral, recurrence, factorial, Euler limit and no genuine zeros off poles. Pinned TauCeti Gamma/Order proves `Complex.tendsto_add_natCast_mul_Gamma`, `meromorphicOrderAt_Gamma_neg_nat`, `meromorphicOrderAt_Gamma_of_ne_neg_nat`, giving all residues/simple poles. `Meromorphic.Gamma` is proved in Mathlib.Analysis.Meromorphic.Complex. Mathlib Gamma is totalized to zero at its genuine poles; this is not a meromorphic zero.

## O-2.03 — Euler constant and product (Lemma 1.1, §1.4, p. 34).

Real.strictAnti_eulerMascheroniSeq', Real.tendsto_eulerMascheroniSeq', Real.one_half_lt_eulerMascheroniConstant and Real.eulerMascheroniConstant_lt_two_thirds in Mathlib NumberTheory/Harmonic/EulerMascheroni give the decreasing harmonic/log sequence and 0<gamma<1. Existing DLMF.Gamma.one_div_Gamma_eq_tprod and new AAR DLMF.Gamma.tendstoLocallyUniformly_weierstrassGamma_prod give the exact Weierstrass product and locally uniform convergence. Complex.differentiable_one_div_Gamma and Complex.Gamma_eq_zero_iff give entireness and its precise zero set, since Lean totalizes Gamma to zero at poles and reciprocation preserves that zero set.

## O-2.04 — reflection, duplication and beta (§1.5–1.6, pp. 35–37).

Proved Mathlib `Complex.Gamma_mul_Gamma_one_sub`, `Gamma_mul_Gamma_add_half`, `Gamma_one_half_eq`, and `betaIntegral_eq_Gamma_mul_div` cover reflection, duplication and complex beta integral on Re p,Re q>0. Pole exclusions are retained for pointwise Gamma products; continuation identities are interpreted meromorphically rather than by multiplying junk pole values.

## O-2.05 — Hankel reciprocal Gamma (§1.7, pp. 37–38).

Exact all-parameter fixed-positive-radius formula is `DLMF.Gamma.inv_Gamma_eq_hankel_fixed_radius` (new admitted, HankelAndPrymConvergence, also TEM-03-04). Both correlated negative-cut banks, the counterclockwise circular arc, and absolute convergence are explicit. Entire parameter dependence follows from equality to Mathlib differentiable reciprocal Gamma; a local uniform integral proof is an optional proof route, not a missing mathematical statement.

## O-2.06 — digamma (§2, pp. 39–40).

Proved Mathlib `Complex.digamma_def`, `digamma_apply_add_one`, `digamma_one_sub`, `digamma_two_mul` cover definition and functional identities. Local series/uniform derivatives: `DLMF.Gamma.digamma_eq_cDigammaSeries`, `summableLocallyUniformlyOn_cDigammaTerm`, `polygamma_eq_tsum`, `summableLocallyUniformlyOn_iteratedDerivWithin_cDigammaTerm`. Real strict monotonicity is `DLMF.Gamma.digamma_strictMonoOn`; the unique minimum is now the fully proved `DLMF.Gamma.Real.existsUnique_isMinOn_Gamma_Ioi`, combining upstream existence with strict logarithmic convexity. Newly proved `DLMF.Gamma.meromorphicAt_digamma` uses upstream `Meromorphic.Gamma.logDeriv`; new admitted `tendsto_mul_digamma_neg_nat` states each residue -1 (Gamma.DigammaPoles).


## O-2.07 — exponential integrals (§3.1–3.2, pp. 40–41).

Canonical definitions `DLMF.Confluent.expIntE1`, `expIntegralEin`, `Real.expIntegralEi`, `Real.logIntegralLi`. Entire Ein and segment primitive: `expIntegralEin_entire`, `expIntegralEin_segment_integral`; relation/series: `expIntE1_eq_Ein_complex`, `expIntE1_hasSum`. Principal-value Ei: `Real.expIntegralEi_principalValue` and `Real.expIntegralEi_negative`. Exact boundary signs are `expIntE1_negative_boundary` (Continuation), using an explicit epsilon=±1 approach, giving -Ei(x)−epsilon*i*pi. Logarithmic integral definition and `Real.logIntegralLi_principalValue` / `LogIntegralPrincipalValue.logIntegralLi_eq` give the correlated real PV branches.

## O-2.08 — Dirichlet integral and sine/cosine integrals (Lemma 3.1, §§3.3–3.4, pp. 41–43).

Canonical `DLMF.Confluent.sinIntegral`, `cosIntegralCin`, `sinIntegralTail`, `cosIntegral` give exactly Si,Cin,si,Ci. Entire and segment integral APIs are Basic/Properties. `expIntegralEin_mul_I`, Si odd and Cin even give both displayed Ein identities by addition/subtraction at ±z. Correlated E1 identities are `sinIntegral_eq_E1`, `cosIntegral_eq_E1` for Re z>0. Tail formulas `sinIntegralTail_horizontal_integral`, `cosIntegral_horizontal_integral` restrict to the real improper tails. Exact **proved upstream Dirichlet cutoff limit** is `TauCeti.Contour.tendsto_integral_sin_div_atTop` (or `tendsto_integral_sinc_atTop`) in TauCeti.Analysis.Contour.WorkedExamples.HalfDisc.SineIntegral. No totalized Lebesgue integral replaces the conditional tail.

## O-2.09 — generalized exponential integral (Exercise 3.5–3.6, p. 43).

Canonical `DLMF.Confluent.expIntegralE`; existing `expIntegralE_laplace_complex`, Gamma bridge/recurrence and `hasDerivAt_expIntegralE` in IncompleteGamma.ExponentialIntegral cover definition, incomplete Gamma, recurrence and derivative. Full principal-cut Stieltjes target newly acquired as `expIntegralE_eq_stieltjes_integral_slitPlane` (new admitted, IncompleteGamma.StieltjesExponentialIntegral), for arbitrary complex order Re p>0 with absolute convergence. Setting p=n≥1 and Mathlib Gamma factorial gives precisely the source integer formula.

## O-2.10 — erf, Dawson and Fresnel (§4, pp. 43–44).

Canonical `DLMF.Confluent.erf`, `erfc`, `dawsonF`, `fresnelC`, `fresnelS` have the source normalizations. `erf_complex_segment_integral`, `hasSum_erf_complex`, and `hasDerivAt_erf_complex` give the entire Gaussian primitive and power series. `dawsonF_entire` and `hasDerivAt_dawsonF_complex` give D-prime=1−2zD with the actual defining Gaussian primitive. `fresnelC_entire`, `fresnelS_entire`, `hasDerivAt_fresnelC_complex`, `hasDerivAt_fresnelS_complex` give the normalized entire Fresnel integrals. Exact correlated phase is `fresnel_signed_erf` with epsilon=1 and `fresnelZetaComplex`=(sqrt(pi)/2)*(1−i)*z. Exact real cutoff limits are `DLMF.Confluent.Real.tendsto_fresnelC_atTop` and `tendsto_fresnelS_atTop` (Confluent/ErrorFunctions).

## O-2.11 — incomplete Gamma (§5, p. 45).

Canonical lower/upper incomplete Gamma, `tricomiIncompleteGamma`; `lowerIncompleteGamma_segment_integral`, `upperIncompleteGamma_horizontal_integral` give the defining integrals on the cut; sum/Gamma identity and defining regularized-confluent series give the expansion. Full chosen-log continuation: `lowerIncompleteGammaOnLog_monodromy`, `upperIncompleteGammaOnLog_monodromy`, `upperIncompleteGammaOnLog_monodromy_limit` explicitly include the exceptional-parameter limit. `tricomiIncompleteGamma_joint_entire` gives exactly the entire normalized two-variable function. Erf square relation is recorded in ErrorFunctions/IncompleteGamma with its correlated phase (precise pointer being checked).

## O-2.12 — orthogonal polynomial construction (Theorem 6.1, p. 46).

Intrinsic existence with all moments and infinite essential support: `DLMF.OrthogonalPolynomials.existsUnique_orthonormal_polynomials` (new admitted, MeasureConstruction). The exact prescribed nonzero-leading-coefficient normalization is now `existsUnique_orthogonal_polynomials_leadingCoeff` (new admitted, PrescribedLeadingCoefficients), applying equally to positive interval weights via their withDensity restricted measure. Lower-degree orthogonality is the proved `IsOrthogonalPolynomials.integral_mul_eq_zero_of_degree_lt`; monic normalization is kappa_n=1, and orthonormal signs follow by normalization of each positive squared norm.

## O-2.13 — recurrence and zeros (Theorems 6.2–6.3, p. 47).

Recurrence: `DLMF.OrthogonalPolynomials.three_term_recurrence`, `three_term_recurrence_explicit`; monic norm ratio `monic_squaredNorm_ratio` and `IsOrthogonalPolynomials.integral_eval_sq_pos`. Distinct complete real zeros: `orthogonal_polynomials_roots`, `IsOrthogonalPolynomials.exists_strictMono_roots`. **Open-interval localization is already proved**, by `IsOrthogonalPolynomials.lt_of_mem_roots` and `.mem_roots_lt` (ClassicalInstances), assuming a<x<b almost everywhere under the weight measure. No new localization admission is needed.

## O-2.14 — Christoffel–Darboux (Exercise 6.3, p. 48).

Existing Christoffel–Darboux and diagonal formulas: `DLMF.OrthogonalPolynomials.christoffel_darboux`, `christoffel_darboux_diagonal`, with exact leading-coefficient/squared-norm normalization; `kernel_reproduces` gives projection on polynomials. General weighted-L2 minimization, exact Pythagorean identity and equality iff identical polynomial now acquired as `polynomial_projection_leastSquares` (new admitted, LeastSquaresProjection), for arbitrary positive measure supporting a full orthogonal family and arbitrary MemLp f 2.

## O-2.15 — classical polynomial definitions (§7, (7.06)–(7.09), pp. 48–49).

Canonical Legendre, Jacobi, Laguerre, Hermite definitions retained. Exceptional-parameter polynomial continuations are `jacobiExtended`, `laguerreExtended`; finite complex binomial sums define their entire parameter dependence directly. Exact all-complex Rodrigues formulas: `jacobiExtended_rodrigues` (JacobiContinuation) and `laguerreExtended_rodrigues` (new admitted, LaguerreContinuation), with specified slit/interior branches. Legendre/Hermite Rodrigues and all four orthogonality relations already exist; no alpha>-1 restriction is used for continued Laguerre Rodrigues.

## O-2.16 — classical norms and ODEs (§7, pp. 49–52).

Norms: `DLMF.OrthogonalPolynomials.legendre_orthogonality` (m=n), `hermitePolynomialH_orthogonality` (m=n), `laguerrePolynomialL_norm`, `jacobi_norm_all` (degree zero/removable case) and `jacobi_norm` (positive degree). All-parameter ODEs: `legendre_differential_equation`, `jacobiExtended_differential_equation`, `laguerreExtended_differential_equation`, `hermitePolynomialH_differential_equation`; LaguerreContinuation explicitly supplies arbitrary complex alpha.

## O-2.17 — classical generating and recurrence identities (§7.3–7.4 and exercises, pp. 50–52).

Exact existing generating/recurrence identities: `DLMF.OrthogonalPolynomials.legendre_generating_function`, `legendrePolynomialP_recurrence`; `hasSum_hermitePolynomialH_generating_function`, `hermitePolynomialH_recurrence`; `hasSum_laguerreExtended_generating_function` for all complex alpha, `laguerreExtended_recurrence`. Hermite derivative is already the proved polynomial API `hermitePolynomialH_derivative` (Basic/Classical), with coefficient 2(n+1). All-complex Laguerre derivative is `deriv_laguerreExtended` (new admitted, LaguerreContinuation). Even/odd bridges are `hermitePolynomialH_even_eq_laguerrePolynomialL`, `hermitePolynomialH_odd_eq_laguerrePolynomialL` (Explicit).

## O-2.18 — Legendre integral and bounds ((7.19), Exercise 7.9, pp. 51–52).

Complete source now acquired: `DLMF.OrthogonalPolynomials.legendrePolynomialP_eq_circleIntegral` (new admitted, LegendreComplexLaplace) states the exact Rodrigues–Cauchy factor on any positive circle about arbitrary complex z. Same module `legendrePolynomialP_eq_laplace_integral_complex` permits either square root s^2=z^2−1, and `norm_legendrePolynomialP_cosh_le` gives exp(n*abs alpha). Existing proved real angular representation / unit bound remain `legendre_laplace_integral`, `norm_legendrePolynomialP_le_one`.

## O-2.19 — Airy integral (§8, pp. 53–55).

Exact defining integrals `DLMF.Airy.airyAi_cos_integral` (ordinary oscillatory limit) and `airyAi_contour_integral` (rays −pi/3 to +pi/3, factor1/(2*pi*i)) are in IntegralRepresentations. Proved entire/ODE/initial/rotation APIs are `differentiable_airyAi`, `airyAi_ode`, `airyAi_zero`, `airyAiDeriv_zero`, `airyAi_add_omega` (Basic/Properties); `hasSum_airyAi_maclaurin` is the entire actual series. Exact normalized Taylor recurrence, including c2=0, is newly `airyAi_maclaurin_coefficient_recurrence` (admitted, MaclaurinRecurrence), with c_n=iteratedDeriv(n,Ai,0)/n!.

## O-2.20 — sum/integral interchange (Theorem 8.1, p. 54).

Exact proved Mathlib APIs: `MeasureTheory.integral_tsum`, `hasSum_integral_of_summable_integral_norm`, `integral_tsum_of_summable_integral_norm` in MeasureTheory/Integral/DominatedConvergence. Their hypotheses are actual integrability and summability of absolute integrals; continuous locally uniformly summing terms with the source finite absolute sum satisfy them. Apply to the measure restricted to the open interval (with finite/infinite endpoints), then `intervalIntegral_tendsto_integral_Ioi` or the two-sided cutoff theorem converts the absolutely integrable result to ordinary improper limits. Exact signatures were Lean-checked in /tmp/Olver-upstream-check.lean; no duplicate admission is needed.

## O-2.21 — Bessel series and differential equation (§9, pp. 55–58).

Canonical proved Mathlib `Complex.besselJ`, `besselJ_int_neg`, `besselJ_neg_int` give the function and integer parity. Existing proved `DLMF.Bessel.besselJ_eq_regularized`, `hasSum_regularized0F1`, and Bessel equation APIs give the reciprocal-Gamma series and ODE; `differentiable_besselJ_order` (Basic/SecondKind) is exactly entire order dependence at every nonzero z. Full continued half-turn monodromy is shared new `besselFirstKindOnLog_add_int_mul_pi`; joint analyticity on the logarithmic covering is `analyticOnNhd_cylinderOnLog` (admitted, LogarithmicMonodromy). Integer trigonometric integral is in Bessel.Elementary.

## O-2.22 — Bessel generating and recurrences ((9.06), (9.14)–(9.15), pp. 56–59).

Generating identity `DLMF.Bessel.hasSum_besselJ_generating_function`; old compact-annulus local uniformity `tendstoLocallyUniformlyOn_sum_besselJ_generating`. Joint absolute normal convergence now `summableLocallyUniformlyOn_besselJ_generating`; arbitrary-order actual Hankel-bank/circle formula now `besselJOnLog_eq_hankel` (new admitted, HankelAndNormalConvergence), with explicit chosen-log argument and fixed positive circle radius. Recurrences already `besselJ_add_sub`, `two_deriv_besselJ`; zero forms retain clearing factors.

## O-2.23 — Bessel addition and Poisson integral (Exercises 9.2,9.5–9.6, p. 59).

Exact proved addition `DLMF.Bessel.hasSum_besselJ_add`; shared joint absolute local uniformity `summableLocallyUniformly_besselJ_add` (new admitted). The square consequence is now fully proved as `hasSum_besselJ_int_sq` and `hasSum_besselJ_nat_succ_sq` (HankelAndNormalConvergence), using general proved `HasSum.nat_succ_of_even` (DLMFMathlib.Topology.Algebra.InfiniteSum.EvenInt); the one-sided sum is (1−J0(z)^2)/2. Arbitrary-complex Poisson integral is shared `besselJ_eq_poisson_exponential`, principal slit, Re nu>−1/2; sharp nonzero-complex-z real-order magnitude including nu=−1/2 is newly `norm_besselJ_le_exp_abs_im` (admitted).

## O-2.24 — modified Bessel (§10, pp. 60–61).

Canonical reciprocal-Gamma series/ODE `DLMF.Bessel.besselI_ode`, derivative `hasDerivAt_besselI`, recurrence `besselI_sub_add`, generating `hasSum_besselI_generating_function`. Exact phase/rotation `besselI_eq_besselJ` is in Basic/Equation, z!=0 and arg z<=pi/2; logarithmic monodromy transports all other sectors. Compact-annulus local uniformity is `tendstoLocallyUniformlyOn_sum_besselI_generating`; joint absolute normal convergence now `summableLocallyUniformlyOn_besselI_generating` (new admitted, HankelAndNormalConvergence).

## O-2.25 — zeta (§11, pp. 61–64).

Proved upstream Mathlib `riemannZeta_residue_one` is exactly punctured limit (s−1)zeta(s)→1; `differentiableAt_riemannZeta` gives holomorphy off 1. `riemannZeta_one_sub` is the exact displayed cosine/Gamma functional equation, with pole exclusions for pointwise evaluation; its meromorphic interpretation removes apparent poles, not junk-value pointwise substitutions. Defining Dirichlet/Mellin representations, `riemannZeta_eulerProduct_hasProd`, `riemannZeta_neg_two_mul_nat_add_one`, `riemannZeta_zero`, `riemannZeta_ne_zero_of_one_le_re` give all other claims and are precisely recorded in Core/UpstreamElementary and Zeta/MathlibCoverage.

## O-3.01 — repeated integration by parts (§§1–2, pp. 66–70).

Exact finite endpoint identity `intervalIntegral.integral_exp_neg_mul_eq_sum_add` and ordinary half-line limit `tendsto_integral_exp_neg_mul_of_derivatives` are newly admitted in LaplaceFiniteRemainder. Finite upper endpoint contributions are explicit. The generic exponential integration-by-parts theorem `intervalIntegral.integral_cexp_mul_eq_sum_add` is already proved. Existing `DLMF.AsymptoticApproximations.laplace_derivatives_exp_bound` and `laplace_error_bound` give the exponential-derivative bound; the new generic exact bound `Asymptotics.integrableOn_and_norm_integral_exp_mul_le_gamma` with rho=1 gives M/(x^N*(x−sigma)) directly.

## O-3.02 — Watson's lemma (Theorem 3.1, pp. 71–72).

Existing DLMF.AsymptoticApproximations.watson_lemma requires an absolutely integrable damped tail; new Asymptotics.watson_lemma_conditional now covers ordinary conditional tails and finitely many improper interior points via MeasureTheory.IsImproperLaplacePrimitive. Its complex lambda with positive real part includes the book's real case. Finite endpoints follow by zero-extension beyond that endpoint, keeping a finite exceptional endpoint in the primitive data.

## O-3.03 — Riemann–Lebesgue (Theorem 4.1, pp. 73–74).

Mathlib Riemann–Lebesgue gives the finite absolutely integrable cutoff limit. The full ordinary-improper assembly is newly acquired as `Complex.tendsto_zero_of_uniform_improper_fourier_cutoffs` (admitted, Fourier.ImproperRiemannLebesgue): arbitrary cutoff filter, finite simultaneous interval excisions, uniform convergence for all sufficiently large absolute frequencies, and limit zero at both positive and negative infinity. No absolute full-tail assumption is added.

## O-3.04 — Fourier endpoint expansions (§5, pp. 74–76).

Source low regularity is now explicit in `Asymptotics.fourier_endpoint_expansion_of_integrable_highestDerivative` and `exists_fourier_halfLine_expansion_of_integrable_highestDerivative` (new admitted, FourierEndpointIntegrableDerivative). The highest derivative is integrable and continuous off finitely many exceptions; lower derivatives have continuous interiors and finite endpoint limits. The finite theorem includes exact integral remainder and little-oh estimate; the half-line theorem preserves ordinary conditional cutoff limits and imposes explicit vanishing upper-endpoint contributions.

## O-3.05 — endpoint Laplace principle (Theorem 7.1, pp. 80–83).

The weak leading theorem is newly `Asymptotics.tendsto_rpow_mul_integral_exp_of_endpoint_equivalents` (admitted, EndpointLaplaceSeries): only p~P*t^mu, differentiated phase equivalent and q~Q*t^(lambda−1), with positive mu,lambda,P, actual local regularity, separated distant phase and one absolutely integrable damped tail. A measurable domain containing a right neighborhood and contained in the positive half-line includes finite/infinite endpoints and improper distant pieces. Translation and multiplication by exp(-x*p(a)) restore the source endpoint normalization.

## O-3.06 — interior minimum (§7.1, p. 80).

Full weak local/tail scope and several isolated equal-level minima are acquired as `Asymptotics.tendsto_sqrt_mul_integral_exp_of_finite_minima` (new admitted, LaplaceMinimum). It uses local quadratic equivalents, amplitude continuity and one absolute damped-tail integral; each minimum contributes q(t_i)*sqrt(2*pi/c_i). The earlier outstanding pointer `isBigO_integral_exp_mul_phase_of_maximum` is an **oscillatory** theorem and was not reused as a Laplace theorem. Different higher phase levels are exponentially negligible by `integrableOn_and_norm_integral_exp_le_of_phase_gap`.

## O-3.07 — full endpoint Laplace expansion (Theorem 8.1, pp. 85–87).

Formal coefficient identification is already fully proved `PowerSeries.coeff_weightedDensity_subst_inverse` (LaplaceCoefficients), for arbitrary complex lambda and chosen logarithm. Full real endpoint integral expansion with arbitrary complex Re lambda>0 is newly `Asymptotics.hasAsymptoticExpansion_integral_exp_of_endpoint_series` (admitted, EndpointLaplaceSeries). It uses actual differentiated phase/amplitude expansions, positive leading phase coefficient, finite/infinite measurable domain and absolute separated tails; coefficients are exactly (1/mu)*coeff_s(Q*logarithmicPower(P,log P0,−(s+lambda)/mu))*Gamma((s+lambda)/mu). No extra convergence of the formal input series is required.

## O-3.08 — Stirling from a Laplace minimum (§8.3, pp. 87–89).

Canonical `DLMF.Gamma.stirlingG`; full complex-sector expansion `scaledGamma_sector_expansion`, plus `gammaStirlingCoeff_eq_stirlingG`, `stirlingG_series_eq_exp` and `gammaStirlingCoeff_recurrence` (SectorExpansions, shared acquisition) supply all orders and the exact formal exponential Bernoulli identity. First four coefficients 1,1/12,1/288,−139/51840 were Lean-checked directly by norm_num unfolding the finite recurrence and Bernoulli numbers (/tmp/Olver-stirling-small.lean).

## O-3.09 — explicit Watson/Laplace remainder majorants (§9, pp. 89–92).

New exact global Gamma majorant `Asymptotics.integrableOn_and_norm_integral_exp_mul_le_gamma`, local bound plus explicit tail `norm_integral_exp_mul_le_gamma_add_tail`, and separated exponential phase-gap estimate `integrableOn_and_norm_integral_exp_le_of_phase_gap` (admitted, LaplaceAbsoluteMajorants). Set rho=(N+Re lambda)/mu to obtain the source general-complex-lambda bound. The amplitude is arbitrary real Banach-valued; local/tail pieces are genuine absolutely defined integrals.

## O-3.10 — nonstationary phase (§11.3, pp. 97–98).

Direct nonlinear-phase theorem under a finite piecewise C2 phase / C1 amplitude partition is newly `Asymptotics.isLittleO_nonstationaryPhase_sub_endpoint_terms` (admitted, NonstationaryPhaseEndpoints). Phase is globally C1 on the finite interval and has no derivative zero; all internal partition boundary terms cancel by continuity. Both outer endpoint terms and little-oh inverse-frequency remainder are explicit.

## O-3.11 — oscillatory Gamma moment (Lemma 12.1, p. 98).

Exact ordinary Gamma moment acquired as `Asymptotics.tendsto_integral_rpow_mul_exp_I` (new admitted, SingularFourierRemainders), with 0<alpha<1 and x>0. This specifies the actual cutoff limit exp(i*pi*alpha/2)*Gamma(alpha)*x^(−alpha), not merely existence of a conditional integral or a totalized Bochner value.

## O-3.12 — tail estimate (Lemma 12.2, p. 99).

Acquired `Asymptotics.exists_power_fourier_tail_bound` (new admitted, SingularFourierRemainders). It permits every real alpha<1, including negative alpha, any K>0, ordinary cutoff convergence uniformly for x>=X>0, and explicit bound 2*K^(alpha−1)/x.

## O-3.13 — singular Fourier remainder (Lemma 12.3, pp. 99–100).

Both `Asymptotics.exists_fourier_remainder_isLittleO` and `exists_fourier_remainder_isBigO` are newly admitted (SingularFourierRemainders). They retain finite exceptional points, local differentiated o/O power hypotheses, bounded variation on each distant tail and vanishing amplitude at infinity; the actual improper transforms converge uniformly for x>=X>0 and have the stated o/O x^(−alpha) size.

## O-3.14 — stationary endpoint (Theorem 13.1, pp. 100–102).

New exact weak leading theorem `Asymptotics.exists_stationaryEndpoint_leading_limit` (admitted, StationaryEndpointLeading) accepts an arbitrary EReal right endpoint, monotone phase, finite exceptional points, two differentiated phase equivalents, one differentiated amplitude equivalent, and bounded variation of q/p-prime on every distant tail. If the far phase is infinite, q/p-prime must tend to zero. It concludes ordinary cutoff existence and the exact scaled Gamma-phase leading limit. Cases mu=1 or lambda=1 use limits to zero for vanishing differentiated leading coefficients.

## O-3.15 — endpoint terms when the singularity is weak (Theorem 13.2, p. 102).

After the actual monotone phase substitution, new `Asymptotics.isLittleO_fourier_sub_endpoint_terms` and `exists_fourier_halfLine_sub_endpoint_isLittleO` (admitted, SingularFourierRemainders) give respectively finite phase endpoint and infinite phase endpoint formulas. Continuous bounded-variation amplitude plus C1 away from finitely many points is retained; arbitrary BV alone would not imply a vanishing Fourier–Stieltjes remainder. The half-line integral is an ordinary uniform cutoff limit. When endpoint coefficients vanish the result is a remainder bound, not an asserted equivalent.

## O-3.16 — full stationary-phase expansion (§14, pp. 103–104).

Acquired `Asymptotics.hasAsymptoticExpansion_stationaryPhase_morse` and `isBigO_stationaryPhase_morse_sub_sums` (new admitted, MorseStationaryPhase). The full coefficients use the actual amplitude q(h(u))*h-prime(u) of an orientation-preserving smooth Morse coordinate, with (i*sigma)^k/(2^k*k!) and even derivatives. The compact-support theorem gives the entire expansion; the finite-interval theorem explicitly adds both nonstationary endpoint series through sufficient order, rather than discarding them.

## O-4.01 — Laplace continuation and derivative expansion (Theorem 1.1, pp. 106–109).

Full logarithmic-cover continuation is supplied by shared new `Asymptotics.LiftedWatson.IsKernel`, `.transform`, `.exists_analyticOnNhd_transform`, `.exists_transform_ofReal`, `.hasAsymptoticExpansion_transform`. This allows independent exponential rates on every proper closed kernel subsector, asymmetric angles, and the full lifted union −alpha2−pi/2<arg z<−alpha1+pi/2. For q analytic at zero, its actual Taylor expansion gives mu=lambda=1 with coefficients q^(n)(0)/n!, so multiplication by Gamma(n+1)=n! yields precisely the derivative coefficients. Separate exponential bounds on derivatives are stronger than the kernel hypotheses; no common rate is required.

## O-4.02 — incomplete-Gamma large argument (§2, pp. 109–112).

Full logarithmic sector `DLMF.Confluent.upperIncompleteGamma_log_asymptotic` (IncompleteGamma/Asymptotics/LargeArgument) gives logSector(3*pi/2−delta), all complex a, using canonical falling-factorial `incGammaAsymptoticCoeff`. Exact all-parameter/all-sheet finite remainder now newly `upperIncompleteGammaOnLog_eq_sum_add_shift` (admitted, LaplaceTailMajorant): remainder (−1)^N*(1−a)_N*Gamma(a−N,z), with no artificial nonpole exclusions. Its decreasing-ray absolute bounds follow from the exact Gamma and incomplete-Gamma majorants; the logarithmic sheet remains fixed.

## O-4.03 — Laplace convergence half-plane (Theorem 3.1, p. 112).

New MeasureTheory.IsImproperLaplacePrimitive, exists_improperLaplace_of_re_lt, laplaceConvergenceAbscissa, exists_improperLaplace_of_abscissa_lt and laplaceConvergenceAbscissa_le_laplaceAbscissa in ConditionalLaplace retain ordinary conditional convergence with finite exceptional points. The canonical absolute abscissa is MeasureTheory.laplaceAbscissa from LaplaceDomain. improperLaplace_exp_mul_sin_exp_iff and integrableOn_exp_mul_sin_exp_iff exhibit distinct abscissae 0 and 1 for q(t)=exp(t)*sin(exp(t)).

## O-4.04 — complex Watson lemma (Theorem 3.2, p. 113).

New Asymptotics.watson_lemma_sector_conditional in WatsonConditional supplies the full proper-right-sector expansion, complex lambda with Re lambda>0, mu>0, finite exceptional points and ordinary conditional tails. Its real-axis version watson_lemma_conditional also covers O-3.02.

## O-4.05 — rotated Watson lemma (Theorem 3.3, pp. 114–115).

Shared `Asymptotics.LiftedWatson.IsKernel` explicitly requires uniform zero-endpoint expansion and subsector exponential growth on the logarithmic strip, not analyticity at the origin. `.exists_analyticOnNhd_transform` / `.hasAsymptoticExpansion_transform` give the full rotated continued proper sectors and fixed powers. This covers power-singular endpoints and arbitrary bounded argument ranges, including on the logarithmic covering.

## O-4.06 — complex Airy asymptotic (§4, pp. 116–118).

Proved `DLMF.Airy.airyAi_poincare` (Asymptotics/RotatedBi) gives |arg z|<=pi−delta for every 0<delta<pi, every truncation N. Canonical `airyU` and `airyU_recurrence` (LaplaceSectors) give the full source coefficients; cancel 6k+3=3*(2k+1) in its displayed recurrence to obtain (6k+1)*(6k+5)/(72*(k+1)). Negative-axis complete two-contribution expansion and derivative are `airyAi_oscillatory_expansion`, `airyAiDeriv_oscillatory_expansion` (OscillatoryForms).

## O-4.07 — ratio of Gamma functions (§5.1–5.2, pp. 118–120).

Full arbitrary complex a,b closed-sector expansion is `DLMF.Gamma.Gamma_ratio_sector_expansion`; formal Bernoulli-polynomial exponential identity is `stirlingRatioG_series_eq_exp` (shared SectorExpansions). Exact proved recursion is `DLMF.Gamma.ShiftedStirling.stirlingRatioG_recurrence`, with `stirlingShiftCoeff` spelling its logarithmic coefficients. No Re(b−a)>0 restriction remains. G1=(a−b)*(a+b−1)/2 was Lean-checked directly by norm_num and ring from `stirlingRatioG` and the Bernoulli polynomial definition (/tmp/Olver-stirling-small.lean).

## O-4.08 — Watson for loops (Theorem 5.1, pp. 120–121).

New Complex.hankelLaplaceTransform in WatsonHankel defines the lower/upper logarithmic-plane jump plus a fixed positive-radius circle. Asymptotics.watson_lemma_hankel gives the reciprocal-Gamma expansion for arbitrary complex lambda, mu>0, preserving all correlated branches and the ordinary conditional jump tail. No Re lambda>0 restriction, no spurious pole exclusions and no principal-value replacement are imposed.

## O-4.09 — contour endpoint Laplace theorem (Theorem 6.1, pp. 121–125).

Existing admitted tagged `DLMF.AsymptoticApproximations.laplace_method_contour` (Integrals/Laplace) has the complete source domain: actual path tangent and continuous lifted argument, convergent local phase/amplitude expansions, arbitrary complex Re lambda>0, mu>0, closed parameter sector width<pi, absolute uniform tail, positive separated phase, and chosen log leading coefficient satisfying the outgoing-angle branch inequality. Coefficients are the actual finite `laplaceCoeff`; the existing formal density extraction theorem identifies them with the source formal-power expression.

## O-4.10 — simple saddle theorem (Theorem 7.1, pp. 125–127).

Existing admitted tagged `DLMF.AsymptoticApproximations.saddle_point` (Integrals/Laplace) already gives all orders uniformly on a closed parameter sector of width<pi, with actual contour, simple saddle, separated positive endpoint gaps, absolute uniform tails and chosen square-root phase tied to the outgoing tangent. It sums exactly 2*Gamma(k+1/2)*laplaceCoeff(...,2k). The local analytic normal coordinate is independently `Complex.exists_isAnalyticSaddleMap`; it is not treated as a contour deformation argument.

## O-4.11 — saddle coefficients (§7.3, p. 127).

Existing proved `DLMF.AsymptoticApproximations.saddle_coeff_zero`, `saddle_coeff_two` give undivided coefficients, including q(t0)=0. The exact normalized displayed A1 is now the **proved** `saddle_coefficient_normalized` (Integrals/SaddleCoefficients), using b2/(2*b0), q(t0)!=0, p-doubleprime!=0 and exp(L0)=p-doubleprime/2. The proof is checked finite field algebra; it does not depend on an admitted saddle expansion.

## O-4.12 — Darboux-type Legendre and Bessel examples (§§8–9, pp. 127–134).

Exact compact-uniform Legendre normalization newly `DLMF.OrthogonalPolynomials.legendrePolynomialP_darboux_leading_uniform` (admitted, LegendreDarbouxLeading), with absolute O(n^(−3/2)) error. Full ordinary J exponential Debye expansion newly `DLMF.Bessel.exists_uniform_besselJ_sech_debye_remainder` (admitted, RealDebyeExpansion), uniform on compact positive alpha intervals with canonical U_k(coth alpha). Shared `exists_norm_besselJ_transition_sub_airy_le` at shift0 and `airyAi_zero` give the exact coalescence constant 2^(1/3)/(3^(2/3)*Gamma(2/3)), with stronger absolute O(nu^(−1)) error.

## O-4.13 — steepest paths and remainder (§10, pp. 135–137).

Arbitrary finite critical multiplicity is now acquired in `Complex.exists_analytic_critical_normalForm` and `exists_critical_level_arcs` (new admitted, CriticalPointNormalForm): actual local analytic inverse, tangent normalization and complete 2m rays with adjacent pi/m directions. Exact full-ray Gamma bound / local-plus-tail bound and uniform separated-gap exponential estimate are `Asymptotics.integrableOn_and_norm_integral_exp_mul_le_gamma`, `norm_integral_exp_mul_le_gamma_add_tail`, `integrableOn_and_norm_integral_exp_le_of_phase_gap`. Finite omitted-ray tails are explicitly incomplete Gamma via `DLMF.Confluent.integral_Ioi_exp_neg_mul_rpow_eq_upperIncompleteGamma` and `norm_integral_Ioi_le_upperIncompleteGamma` (new admitted, IncompleteGamma.LaplaceTailMajorant). Substitute decay rate Re(z*exp(i*beta))−sigma; the contour tangent has unit norm, with its branch/orientation retained in the actual ray parametrization.

## O-5.01 — real initial-value existence (Theorem 1.1, pp. 139–141).

New `ODE.existsUnique_secondOrder_continuous_interval` gives arbitrary open ordinary real intervals, continuous complex coefficients and forcing, every initial jet, uniqueness and compact-uniform Picard iteration; `ODE.secondOrderPicardIterate` is the actual two-component iteration with proved zero/successor equations. Unbounded intervals and overlap compatibility are retained by uniqueness. No analytic coefficient assumption replaces continuity.

## O-5.02 — equivalent fundamental-pair tests (Theorem 1.2, pp. 141–142).

New `ODE.fundamentalPair_iff_linearIndependent_iff_wronskian` is exactly the three fundamental-pair tests; `ODE.wronskian_eq_exp_integral_continuous` gives the Abel factor from every interior reference point. New `ODE.reduction_of_order_continuous` supplies the actual two nested primitives and Wronskian for continuous complex coefficients on a zero-free first-solution subinterval, including its initial derivative normalization. The three tests require a nonempty interval, supplied by the interior reference.

## O-5.03 — real parameter dependence (Theorem 2.1, pp. 143–144).

Existing `ODE.continuousOn_parametric_linear_ode` covers joint continuity of the solution jet under continuous coefficient and initial-data families on a compact real rectangle. `ODE.differentiable_parametric_linear_ode` gives the parameter derivative and differentiated inhomogeneous system under the stated continuous parameter derivatives, hence w, its first two argument derivatives and their parameter derivatives. No analyticity in the real variable is assumed.

## O-5.04 — holomorphic parameter with real argument (Theorem 2.2, p. 144).

Existing `ODE.differentiable_complex_parametric_linear_ode` gives holomorphic parameter dependence with merely continuous real argument coefficients and holomorphic initial data. Its vector-system realization (value, first derivative), followed by the ODE for the second derivative, covers all three displayed solution jet components.

## O-5.05 — complex initial-value theorem (Theorem 3.1, pp. 145–146).

Existing `DLMF.AlgebraicAnalytic.exists_isLinearODE2SolutionOn` and `DLMF.AlgebraicAnalytic.isLinearODE2SolutionOn_unique` supply simply-connected-domain analytic IVP existence and uniqueness. New `Complex.existsUnique_linearSecondOrderContinuation` supplies actual compatible solution germs along every continuous path in any ordinary domain; `Complex.IsLinearSecondOrderContinuation.isAnalyticContinuationAlong` is a proved bridge to the canonical TauCeti continuation predicate. Path independence is supplied only under the monodromy hypothesis, never silently on a multiply connected domain.

## O-5.06 — holomorphic parameters and complex argument (Theorem 3.2, pp. 146–147).

New `Complex.exists_linearSecondOrderContinuation_param_analytic` covers jointly continuous, separately holomorphic coefficient families, holomorphic initial jets, arbitrary fixed continuous paths, and parameter analyticity of the carried value and first two argument derivatives. Existing `DLMF.AlgebraicAnalytic.isLinearODE2SolutionOn_param_analytic` supplies the corresponding single-valued branch-domain statement. The path is actual data, not an unspecified universal-cover placeholder.

## O-5.07 — Taylor recursion (§3.2, p. 146).

Existing `PowerSeries.coeff_ordinary_second_order` is the exact finite convolution Taylor recurrence. `ODE.linearOdeTaylorCoeff` is the recursively computed coefficient family, and `ODE.exists_ball_solution_linear_ode` gives analytic solutions throughout any coefficient ball. Expanding that analytic solution at its center and applying the coefficient recurrence gives the source radius lower bound, including every smaller ball up to the nearest coefficient singularity.

## O-5.08 — singularity rank and Frobenius (Theorem 4.1, pp. 148–151).

Canonical ordinary, regular-singular and rank predicates are `Complex.LinearODEOrdinaryAt`, `Complex.LinearODERegularSingularAt`, and `DLMF.AsymptoticApproximations.HasSingularityRank`. Existing `DLMF.AsymptoticApproximations.indicialPoly`, `DLMF.AsymptoticApproximations.frobeniusCoeff`, `DLMF.AsymptoticApproximations.summable_frobeniusCoeff_of_nonresonant`, `DLMF.AsymptoticApproximations.analyticOnNhd_frobeniusAnalyticFactor`, and `DLMF.AsymptoticApproximations.frobeniusAnalyticFactor_isLinearODE2SolutionOn` acquire the exact single-root recursion and whole coefficient-disc convergence. `DLMF.AsymptoticApproximations.frobenius_solutions` gives the two-root nonresonant basis. The exact shifted-indicial exclusions, rather than a stronger unnecessary noninteger condition on unrelated parameters, are retained.

## O-5.09 — resonance (§5, pp. 151–153).

Existing `DLMF.AsymptoticApproximations.frobenius_log_solution` gives both repeated and distinct resonant roots, convergent analytic factors, the possible zero logarithmic coefficient, and the repeated-root nonzero normalization. New `Complex.exists_resonant_primitive` gives the exact analytic regular primitive, finite principal part, logarithm coefficient and its equality to the contour residue. For the reduction quotient z^(-N-1)k(z), this coefficient is k^(N)(0)/N!; multiplication by the first Frobenius solution and `Complex.reduction_of_order_of_primitives` gives the source residue computation, including N=0.

## O-5.10 — infinity and recessive solutions (§§6–7, pp. 153–155).

Existing `DLMF.AlgebraicAnalytic.isLinearODE2SolutionOn_inv` gives exactly 2/t-p(1/t)/t^2 and q(1/t)/t^4. New `ODE.IsRecessiveAt` is the general solution-space/filter predicate, retaining eventual nonvanishing of independent comparison solutions so totalized division cannot fake recession at common zeros. `ODE.IsRecessiveAt.exists_smul_eq` states uniqueness up to nonzero scale for a nontrivial approach filter. `ODE.IsNumericallySatisfactoryPair` includes the span, independence, and recessive member at every indicated endpoint where one exists. All defining iff APIs are proved; the endpoint domain is explicit.

## O-5.11 — three-singularity classification (Theorem 8.1, pp. 156–158).

New generic `Complex.eq_papperitz_coefficients_of_regularSingular` classifies the three-marked-point regular-singular equation with the Fuchs exponent sum, including ordinary marked points. `DLMF.Hypergeometric.coefficients_eq_gauss_of_regularSingular` is the normalized Gauss classification. Existing Riemann coefficients/operator and `DLMF.Hypergeometric.riemann_hypergeometric_solution_exp_log` give the actual Mobius change and locally chosen nonvanishing analytic-log power gauge, rather than a single-valued power on an unspecified domain. The coefficients and exponent pairs determine the equation, and fixed-path continuation is the O-5.05 construction.

## O-5.12 — regularized Gauss function (§9.1, Theorem 9.1, pp. 159–160).

Canonical `DLMF.Hypergeometric.regularizedGaussHypergeometric` has the reciprocal-Gamma series and the principal cut-plane continuation. Existing `DLMF.Hypergeometric.differentiableOn_regularizedGaussHypergeometric_joint`, `DLMF.Hypergeometric.differentiable_regularizedGaussHypergeometric_params`, and `DLMF.Hypergeometric.analyticOnNhd_regularizedGaussHypergeometric_comp` give the full joint parameter/argument analytic scope on the principal branch. `DLMF.Hypergeometric.genContinued_parameter_entire` retains every chosen continued branch. `DLMF.Hypergeometric.regularizedGaussHypergeometric_neg_nat` gives the exact c=-m shifted regularized formula; the all-c equation and ordinary/regularized bridge retain reciprocal-Gamma zeros.

## O-5.13 — Euler and Gauss formulas (§9.4–9.5, pp. 160–161).

Existing `DLMF.Hypergeometric.regularizedGaussHypergeometric_eq_regularizedGaussHypergeometricIntegral` gives the exact principal Euler integral for Re(c)>Re(b)>0, with no artificial argument restriction to the unit disc. `DLMF.Hypergeometric.hasSum_regularizedGauss_one` gives the regularized Gauss value for Re(c-a-b)>0 without excluding c, c-a or c-b at Gamma poles; denominator Gamma factors are reciprocal zeros. These cover the normalization differences from ordinary F directly.

## O-5.14 — derivative, Euler and Pfaff transformations (§§9–10, pp. 162–165).

Existing `DLMF.Hypergeometric.iteratedDeriv_regularizedGaussHypergeometric`, `DLMF.Hypergeometric.regularizedGaussHypergeometric_euler`, `DLMF.Hypergeometric.regularizedGaussHypergeometric_pfaff`, and `DLMF.Hypergeometric.regularizedGaussHypergeometric_contiguous_c` give the derivative, Euler, Pfaff and exact lower-parameter contiguous relation on compatible principal cuts for all parameters. Integer c is not dropped merely because the ordinary series notation would be inadmissible.

## O-5.15 — local bases and connections (§10, pp. 163–168).

The zero pair is the actual regularized Gauss function and z^(1-c) times its shifted regularized counterpart. New `DLMF.Hypergeometric.wronskian_regularizedGauss_zero_pair` gives exactly sin(pi*c)/pi*z^(-c)*(1-z)^(c-a-b-1); c nonintegral makes the pair independent by the fundamental-pair theorem. Resonant bases use O-5.09. `DLMF.Hypergeometric.regularizedGaussHypergeometric_connection_inv`, `DLMF.Hypergeometric.regularizedGaussHypergeometric_eq_connection_inv`, `DLMF.Hypergeometric.tendsto_connection_inv`, and their `DLMF.Hypergeometric.regularizedGaussHypergeometric_connection_one_sub`, `DLMF.Hypergeometric.regularizedGaussHypergeometric_eq_connection_one_sub`, `DLMF.Hypergeometric.tendsto_connection_one_sub` counterparts provide both principal connection formulas and the limits of the entire combined right sides. Gamma reflection converts their normalized sums into the synopsis ordinary transformed F forms when the exponent difference is noninteger; those differences guarantee the transformed lower parameters are admissible. Individual divergent Gamma factors are never separately assigned finite limits.

## O-5.16 — generalized hypergeometric equation (§11, pp. 168–169).

Canonical generalized coefficient series and Euler-operator equation are `DLMF.Hypergeometric.generalizedHypergeometricCoeff` and `DLMF.Hypergeometric.generalizedHypergeometric_theta_ode`. Exact analytic/radius cases are `DLMF.Hypergeometric.generalizedHypergeometric_entire`, `DLMF.Hypergeometric.generalizedHypergeometric_radius_one`, `DLMF.Hypergeometric.generalizedHypergeometric_radius_zero`, and `DLMF.Hypergeometric.generalizedHypergeometric_diverges_nonzero`, with nontermination/lower regularity retained. `DLMF.Hypergeometric.generalizedHypergeometric_terminating_entire` covers terminating exceptions. New `DLMF.Hypergeometric.generalizedHypergeometricTruncated_theta_ode` admits lower exceptional parameters occurring only beyond the finite degree: it requires denominator Pochhammer products nonzero only through that degree. The uncancelled Euler product has order max(p,q+1); coefficient cancellation is not hidden.

## O-5.17 — Clausen square (Exercise 11.1, p. 169).

Existing `DLMF.Hypergeometric.clausen_formula` gives the exact square identity on the defining disc; `DLMF.Hypergeometric.generalizedHypergeometric_clausen_principal` gives compatible principal continuation. Lower regularity is ordinary-series regularity, with exceptional termination treated separately. New `ODE.product_symmetricSquare_equation` gives the full arbitrary p/q third-order symmetric-square equation, including the 3p, 2p^2+pprime+4q, and 4pq+2qprime coefficients, over a general nontrivially normed field.

## O-5.18 — associated Legendre normalizations (§12, pp. 169–171).

Canonical `DLMF.Legendre.associatedP`, `DLMF.Legendre.olverQ`, `DLMF.Legendre.associatedQ` and `DLMF.Legendre.legendreBranchPower` preserve the source normalizations. Their definitions give the two regularized hypergeometric expressions and the Hobson Gamma conversion on its regular locus. `DLMF.Legendre.associatedP_reflect_degree` gives degree reflection and `DLMF.Legendre.associated_connection_14` gives normalized-Q order symmetry. `DLMF.Legendre.associatedP_entire_degree`, `DLMF.Legendre.associatedP_entire_order`, `DLMF.Legendre.olverQ_entire_degree`, and `DLMF.Legendre.olverQ_entire_order` retain the entire parameter dependence. The branch power uses log(z-1)+log(z+1), not principal sqrt(z^2-1) on the left half-plane; whole-expression limits retain exceptional parameters.

## O-5.19 — endpoint forms and satisfactory pair (Theorem 12.1, pp. 171–174).

Existing `DLMF.Legendre.associated_wronskian_8` is exactly W(P^(-mu),OlverQ^mu)=-1/(Gamma(nu+mu+1)*(z^2-1)). New `DLMF.Legendre.tendsto_associatedP_neg_order_scaled_one`, `DLMF.Legendre.tendsto_olverQ_scaled_cobounded`, and `DLMF.Legendre.tendsto_olverQ_zero_order_div_log_one` give all three full complex cut-plane endpoint coefficients, retaining zero reciprocal-Gamma coefficients as scaled limits rather than false equivalences to zero. New `DLMF.Legendre.isNumericallySatisfactoryPair_associatedP_olverQ` gives the exact right-half-plane complex parameter range and both endpoint approaches with the general endpoint-basis predicate. Its solution-space span is full by the nonzero Wronskian and connected-domain uniqueness.

## O-5.20 — Legendre P loops (Theorem 13.1, pp. 174–175).

New `DLMF.Legendre.SchlafliPBasedLoop` specifies the actual finite positive loop, its two normalized logarithmic lifts, and its infinite real legs. `DLMF.Legendre.nonempty_schlafliPBasedLoop` supplies the contour. Both source expressions are actual finite-loop-plus-tail integrals: `DLMF.Legendre.schlafliPFirstExpression` and `DLMF.Legendre.schlafliPSecondExpression`. `DLMF.Legendre.integrableOn_schlafliPFirstTail` and `DLMF.Legendre.integrableOn_schlafliPSecondTail` retain their different source ranges. `DLMF.Legendre.associatedP_eq_schlafliPFirstExpression` and `DLMF.Legendre.associatedP_eq_schlafliPSecondExpression` give their exact factors, and `DLMF.Legendre.tendsto_schlafliPFirstExpression` / `DLMF.Legendre.tendsto_schlafliPSecondExpression` give whole-expression degree-pole limits. The factor exp(-2*pi*i*mu)-1 comes from the two real legs. The displayed z=1 endpoint is acquired by limit, not by evaluating a totalized logarithm at zero.

## O-5.21 — Legendre Q loop (Theorem 13.2, pp. 177–178).

New `DLMF.Legendre.SchlafliQOppositeLobes` specifies the positive right loop followed by the negative left loop, with all three carried logarithms normalized at the interior real base point. `DLMF.Legendre.nonempty_schlafliQOppositeLobes` supplies this actual contour. `DLMF.Legendre.schlafliQExpression` is the whole e^(-nu*pi*i)*Gamma(-nu)/(2^(nu+2)*pi*i) times branch-power and continued integral. `DLMF.Legendre.olverQ_eq_schlafliQExpression` identifies it with normalized Olver Q and `DLMF.Legendre.tendsto_schlafliQExpression` acquires all nonnegative-integral-degree removable limits. This is the arbitrary-order formula with Olver orientation, not only a zero-order related contour.

## O-5.22 — Legendre recurrences (§13.3, pp. 176–177).

Existing `DLMF.Legendre.associatedP_recurrence_6` is the order-mu+2 identity, `DLMF.Legendre.associatedP_recurrence_7` is the mixed order/degree identity with the normalized square root, and `DLMF.Legendre.associatedP_recurrence_3` is the degree-nu+2 identity. `DLMF.Legendre.associatedP_recurrence_4` and `DLMF.Legendre.associatedP_recurrence_5` supply the derivative recurrences. These are parameter identities of the canonical entire P family on the retained branch; no noninteger-order restriction is silently added.

## O-5.23 — integer degree/order (§14, pp. 179–183).

Existing `DLMF.Legendre.associatedP_nat_order_rodrigues`, `DLMF.Legendre.associatedP_order_gt_degree`, and `DLMF.Legendre.associatedP_negative_integer_order` give the integer derivative formula, vanishing above degree, and negative-order factor. At degree n and m<=n, Gamma natural values reduce that factor to (n-m)!/(n+m)!; the positive branch has no Ferrers (-1)^m factor. `DLMF.Legendre.legendreQ_nat_eq_neumann_integral` gives the full complex Neumann cut, and `DLMF.Legendre.legendreQPoly_eval_eq_convolution` / `DLMF.Legendre.legendreQPoly_eval_eq_legendre_sum` give both actual finite W polynomial sums in the canonical logarithmic Q decomposition. The exact logarithmic decomposition is `DLMF.Legendre.legendreQ_nat` together with `DLMF.Legendre.legendreQ_zero` on its canonical cut; the integer Neumann target also supplies the extension across the remaining left real ray.

## O-5.24 — addition theorem (Theorem 14.1, p. 183).

New `DLMF.Legendre.legendrePolynomialP_addition_sqrt_pair` is fully proved: it gives the exact factorial-weighted finite addition polynomial for every complex argument, angle and arbitrary paired square roots satisfying r_i^2=z_i^2-1. It is derived from the existing `DLMF.OrthogonalPolynomials.LegendreAddition.legendre_eq_kernel`, with imaginary-rotated square roots. Substitution of `DLMF.Legendre.associatedP_nat_order_rodrigues` gives the displayed associated P normalization. No artificial slit restriction remains on this polynomial identity.

## O-5.25 — trigonometric integral (Lemma 14.1, p. 184).

New `Real.integral_inv_affine_cos_sin` gives strict positivity, interval integrability and the exact 2*pi/sqrt(a^2-b^2-c^2) integral for every real starting angle under precisely a>sqrt(b^2+c^2). It includes b=c=0 and fixes the positive square root.

## O-5.26 — Ferrers functions (§15, pp. 185–189).

Canonical `DLMF.Legendre.ferrersP` and `DLMF.Legendre.ferrersQ` give the real-interval regularized normalizations, with the latter via integer-order parameter limits. Existing `DLMF.Legendre.ferrersP_nat_order_rodrigues` and `DLMF.Legendre.ferrersP_negative_integer_order` retain the Condon--Shortley (-1)^m sign. `DLMF.Legendre.ferrers_orthogonality_6` gives the degree Kronecker-delta integral and `DLMF.Legendre.ferrers_orthogonality_8` gives the 1/(1-x^2) weighted order integral, including the stated diagonal specialization. `DLMF.Legendre.ferrers_connection_10` is exactly the reflection identity with cos(pi*(nu+mu)) and -2/pi*sin(pi*(nu+mu))*Q. The traditional-Q Gamma-pole locus is retained, not confused with the entire normalized complex Q.

## O-5.27 — Ferrers values and parity series (§15.2, pp. 187–188).

Existing `DLMF.Legendre.ferrersP_zero_1`, `DLMF.Legendre.ferrersP_zero_2`, `DLMF.Legendre.ferrersQ_zero_3`, and `DLMF.Legendre.ferrersQ_zero_4` give exactly the four displayed initial values and derivative values. `DLMF.Legendre.ferrersP_even_odd` / `DLMF.Legendre.ferrersQ_even_odd` and `DLMF.Legendre.ferrersP_eqOn_even_odd` / `DLMF.Legendre.ferrersQ_eqOn_even_odd` give the full normalized x^2 Gauss parity formulas. The source derivative at zero is the coefficient of x after multiplying by the even (1-x^2)^(mu/2) factor. `DLMF.Legendre.LegendreQRegular` excludes genuine numerator-Gamma poles for traditional Q; reciprocal denominator-Gamma zeros are retained.

## O-6.01 — Liouville transform (Theorem 1.1, pp. 190–191).

Existing `DLMF.AlgebraicAnalytic.liouville_transformation` supplies the complex analytic transformation. New `Real.iteratedDeriv_liouville_inverse` gives the full merely C3 real inverse-coordinate formula, with the explicit Schwarzian and the amplitude |xprime|^(-1/2), including orientation reversal. `Real.schwarzian_quotient_comp` gives the real C3 Schwarzian chain rule. Substituting xprime=1/sqrt(f) gives exactly the source psi and W=f^(1/4)w; an orientation-dependent square-root constant does not change the equation.

## O-6.02 — error-control function (§2.1, (2.01), p. 193).

New `LiouvilleGreen.RealInterval.Data.density` is precisely A*Asecond-g/sqrt(f), A=f^(-1/4), for only C2 positive real f and continuous complex g. Its phase satisfies phaseprime=sqrt(f); `LiouvilleGreen.RealInterval.Data.variation` is the actual absolute-density integral from any extended-real reference, with all defining APIs proved. Thus adding a constant to a control primitive changes no bound. Existing `Complex.IsComplexLiouvilleGreenData` gives the corresponding analytic chosen-branch amplitude, phase and control primitive, with exactly the source derivative.

## O-6.03 — exponential LG bounds (Theorem 2.1, pp. 193–196).

New `LiouvilleGreen.RealInterval.Data.exists_exponential` gives both exponential solutions on any extended-real ordinary interval, complex continuous g, the exact constants |epsilon| and |epsilonprime|/(2*u*sqrt(f)), the actual zero endpoint limits, and real-valued solutions for real g. Set u=1 for the displayed source formula; left and right reference choices are explicit. Only integrability from the selected endpoint to each interior point is assumed. Existing real Volterra proofs remain available, but no analytic regularity is substituted for the source C2 regularity.

## O-6.04 — oscillatory LG bounds (Theorem 2.2, p. 196).

New `LiouvilleGreen.RealInterval.Data.exists_oscillatory_pair` gives both signs, any finite/interior/improper reference in the interval closure, only C2 positive f and continuous complex g, the exact exp(V/u)-1 bounds on both errors and normalized derivatives, and both zero endpoint limits. It also gives a named conjugate choice when g is real. Interior references use the actual two-sided approach filter and two-sided reference segment. Set u=1 for Theorem2.2.

## O-6.05 — endpoint behavior and connection multiplier (Theorem 3.1, §3.3–3.5, pp. 198–200).

New `LiouvilleGreen.RealInterval.Data.tendsto_exponential_error_opposite` states the finite opposite-end error limit and vanishing normalized derivative under total density integrability and phase divergence, for the full weak real regularity. Existing `LiouvilleGreen.Interval.eqOn_of_recessive_ratio`, `LiouvilleGreen.Interval.eqOn_of_recessive_ratio_left`, `LiouvilleGreen.Interval.exists_dominant_of_recessive`, and `LiouvilleGreen.Interval.exists_dominant_of_recessive_left` give recessive uniqueness and the complementary dominant construction in their real settings. The general solution-space uniqueness is `ODE.IsRecessiveAt.exists_smul_eq`; adding a recessive multiple leaves the dominant normalization unchanged, so no false dominant uniqueness is asserted.

## O-6.06 — convergence of the error integral (§4, pp. 200–202).

New `LiouvilleGreen.integrable_errorDensity_of_power_at_zero` and `LiouvilleGreen.integrable_errorDensity_of_power_atTop` give both explicit differentiated-power sufficient conditions, actual density integrability, and quantitative density/tail orders. The phrase twice differentiable asymptotic relation is implemented by first and second derivative order bounds, as the source pp200--201 specifies. New `LiouvilleGreen.integrable_errorDensity_inverseSquare_split` gives exact cancellation of the -1/4 inverse-square error and local integrability of the remaining O(1/t) perturbation. Existing `Complex.euler_equation_cpow` identifies the resulting powers 1/2 plus/minus sqrt(q0+1/4) with the distinct indicial roots; for q0<-1/4 use the oscillatory sign with f=abs(q0+1/4)/t^2. The repeated root is O-5.09, not an invalid exponential equivalence.

## O-6.07 — uniform large parameter (§5, pp. 203–206).

New `LiouvilleGreen.RealInterval.Data.exists_exponential` and `LiouvilleGreen.RealInterval.Data.exists_oscillatory_pair` include every u>0 with exactly the source derivative normalizers and variations V/(2u) or V/u. The new fully proved `Real.exp_div_sub_one_le_two_div` and `Real.norm_le_inv_parameter_of_exp_control` turn bounded total variation into a uniform O(1/u) bound on any index set, including an unbounded interval. The fully proved `Real.eventually_norm_lt_of_exp_control` gives uniform relative o(1) from V(u)/u tending to zero, so parameter-dependent f/g are retained by instantiation. Existing fully proved `Complex.liouvilleGreen_doublePole_parameter_shift` gives the exact constant shift setting the remaining double-pole numerator to -1/4; choosing its positive real square root is the displayed effective parameter when that radicand is positive.

## O-6.08 — parabolic cylinder example (§6, pp. 206–208).

New `DLMF.Confluent.PositiveCylinderError.leadingFactor` uses the exact source 2^((u-1)/4)*u^(-(u+1)/4)*exp(u/4)*(1+t^2)^(-1/4)*exp(-u*pcfXiBar(t)); `DLMF.Confluent.PositiveCylinderError.error` is the actual canonical cylinder ratio. `DLMF.Confluent.PositiveCylinderError.amplitude_mul_secondDeriv` gives the explicit (3t^2-2)/(4*(1+t^2)^(5/2)) density. `DLMF.Confluent.PositiveCylinderError.integrable_density_and_variation` computes the full-line absolute integral as 4/3*sqrt(2/5)-1/6 and bounds its tail by 3/(8*t^2) for t>=1. `DLMF.Confluent.PositiveCylinderError.norm_error_le` gives both computable error components; `DLMF.Confluent.PositiveCylinderError.error_uniform_parameter_and_tail` gives the entire-real-line uniform O(1/u) and fixed-u O(t^-2) conclusions.

## O-6.09 — integrable singular-potential extension (Theorem 7.1, pp. 209–210).

New `Real.sineMajorant` is the actual compact-interval supremum, with proved defining API; `Real.sineMajorant_eq` supplies its sin(x)/1 piecewise value. `ODE.SingularSinePotential.control` is the actual weighted G integral. `ODE.SingularSinePotential.exists_solution` retains a continuous complex potential on the punctured interval, finite weighted integrals at zero, a C1-through-zero normalized solution, the actual sine-kernel Volterra equation and sharp sine-majorant error. `ODE.SingularSinePotential.exists_scattering_family` gives for real g=O(1/x) near zero with an integrable tail the actual scattering amplitude/phase and uniform O(log(u)/u) error and corrections. It fixes w(0)=0 and wprime(0)=u, rather than hiding an arbitrary amplitude in the result.

## O-6.10 — zero localization (§8, pp. 211–214).

New `Real.exists_zero_sin_add_error` gives the exact arcsine phase bracket and its pi*eta/2 bound, including zero error and a singleton bracket. `Real.existsUnique_zero_sin_add_error` gives the source derivative criterion eta<1/sqrt(2), with within derivatives at bracket endpoints. `Real.exists_sin_error_zero_sequence` gives exactly one zero per sufficiently late half-period cell, every sufficiently large zero, and phase z_n=n*pi-delta+o(1). Applying these in the actual phase coordinate, or in u times the phase coordinate, retains the phase integer and gives the uniform parameter version from O-6.07; it is not merely an infinite-zero subsequence assertion.

## O-6.11 — inverse-coordinate sensitivity (Lemma 8.1, p. 214).

New `Real.exp_mul_le_of_abs_logDeriv_le` gives both stronger exponential two-sided bounds and the exact rational corollary under K*abs(s-t)<1, for every pair of points in the interval, using only continuous X and within-interval C1 derivatives. Positivity of X and nonnegativity of K are explicit. This is the source inverse-coordinate sensitivity lemma, not a one-point derivative heuristic.

## O-6.12 — parameter derivative of an oscillatory error (Theorem 9.1, p. 216).

New `LiouvilleGreen.CompactInterval.Data.exists_oscillatory_parameter_family` gives the actual endpoint-normalized complex oscillatory IVP family, jointly C1 error, both usual LG bounds, and the exact parameter derivative majorant `LiouvilleGreen.CompactInterval.Data.parameterBound`. `LiouvilleGreen.CompactInterval.Data.integratedVariation` is the source I=integral sqrt(f)*V, increasing on the interval, so its total variation is I itself. All real coefficient derivatives at the finite endpoints are within the closed interval; only C2 f and continuous real g are required. The minus family is obtained by conjugacy. The first parameter derivative estimate is therefore acquired explicitly, not inferred from mere differentiability.

## O-6.13 — eigenvalue asymptotic (§9, pp. 214–217).

New `LiouvilleGreen.CompactInterval.Data.exists_dirichlet_frequency_sequence` fixes the action as the actual integral sqrt(f), gives the real normalized Dirichlet IVP, simple characteristic roots, all sufficiently large positive frequencies indexed by the phase integer with u_n=n*pi/c+O(1/n), and uniform eigenfunction sine errors. `LiouvilleGreen.CompactInterval.Data.existsUnique_dirichlet_frequency_of_threshold` retains a computable finite half-period-cell threshold. With A=exp(V/u)-1 and B the O-6.12 majorant, it requires A<1 and (c*A+B)/sqrt(1-A^2)<c. These factors come from differentiating the exponential phase and arcsine correction. The synopsis instruction merely to use B<c omits them; this correction is recorded in BookAcquisition-RevisionNotes.md, with source (9.14)--(9.15) evidence. The original synopsis is unchanged.

## O-6.14 — general Volterra setup (§10.2, p. 218).

New `ODE.WeightedVolterra.Data` is the full source kernel with two path derivatives, actual zero diagonal, positive source Pj/Q weights, forcing J, all three coefficient functions, actual kappa/kappa0/kappa1 bounds and arc-length-weighted integrability. Its extended-real parameter endpoints allow finite and improper oriented paths; finitely many coefficient/corner exceptions are explicit. `ODE.WeightedVolterra.Data.variation`, `ODE.WeightedVolterra.Data.transform`, and `ODE.WeightedVolterra.Data.iterate` are actual functions with proved defining equations. No universal kernel estimate is assumed without its source weights.

## O-6.15 — Volterra existence and error (Theorem 10.1, pp. 219–220).

New `ODE.WeightedVolterra.Data.existsUnique_isSolution` gives the full kernel/derivative-coupled Volterra construction, compact-uniform convergence of its actual iterates, the two source A*exp(B) bounds and both normalized endpoint limits. `ODE.WeightedVolterra.Data.norm_iterate_succ_sub_le` gives exactly kappa*Phi*(kappa0*Psi0+kappa1*Psi1)^n/n! for both iterate components. The solution predicate includes the actual integral equation, derivative along the oriented path, and local second regularity away from the explicit exceptional set. Uniqueness is on the path interval, so arbitrary values outside it are not falsely fixed.

## O-6.16 — sharper self-forcing estimate (Theorem 10.2, p. 220).

New `ODE.WeightedVolterra.Data.norm_isSolution_le_selfForcingBound` covers the completely general source kernel when phi=psi0 and psi1=0. `ODE.WeightedVolterra.selfForcingBound` is the actual piecewise (kappa/kappa0)*(exp(kappa0*Phi)-1), with its exact kappa0=0 value kappa*Phi; `ODE.WeightedVolterra.tendsto_selfForcingBound_zero` gives the continuous limiting interpretation. For arbitrary fundamental pairs, existing `Complex.complexGreen_error_integral_and_bound` and `Complex.exists_complexGreen_error_endpoint` retain the explicit kernel, its derivative, P0/P1/k, actual oriented integrals, both bounds and endpoint normalization. New `Complex.complexGreen_derivative_coupling_error` extends that specialization to differing first-derivative coefficients and arbitrary finite initial errors.

## O-6.17 — complex LG (Theorem 11.1, p. 222).

Existing `Complex.IsComplexLiouvilleGreenData`, `Complex.exists_complexLiouvilleGreenData`, `Complex.exists_complexLiouvilleGreen_finite_reference`, and `Complex.exists_complexLiouvilleGreen_endpoint_reference` give actual chosen-branch analytic LG solutions and progressive finite/infinite path bounds on a simply connected branch domain. New `Complex.IsLiouvilleGreenContinuation` represents actual compatible analytic fourth-root/phase/control germs along any path, using the canonical TauCeti continuation predicate. `Complex.exists_liouvilleGreenContinuation`, `Complex.exists_liouvilleGreenContinuation_error`, and `Complex.exists_liouvilleGreenContinuation_endpoint_error` give the finite/improper progressive estimates on these continued branches in a multiply connected original domain. The control variation follows the carried germs, and the actual monotonicity of the carried phase is a hypothesis; no global single-valued square root or unmodelled cover is substituted.

## O-6.18 — complex endpoint multiplier (Theorem 12.1, pp. 223–224).

Existing `Complex.exists_complexLiouvilleGreen_connection_multiplier` gives exactly the two oppositely normalized solutions, equality of their opposite-end relative-error limits, vanishing normalized derivatives and the (exp(total variation/abs(u))-1)/2 bound. The branch domain is explicit, and its progressive path retains the actual common initial tail. The equality is a Wronskian connection equality, not equality of the two solutions. Continued branch transfer is the actual germ construction of O-6.17.

## O-6.19 — variation along a line (Lemma 13.1, p. 225).

New `Complex.eVariationOn_exp_neg_mul_lift_line` gives the actual full doubly infinite line variation 2*chi(alpha)*d^(-alpha), with `Complex.powerVariationConstant` the displayed Gamma quotient and a continuous logarithmic lift of the line. `Complex.progressivePowerVariationCosts` is the actual cost set of finite progressive right-half-plane paths to a positive R plus its R^(-alpha) ray tail. `Complex.csInf_progressivePowerVariationCosts` proves nonemptiness, boundedness, exact infimum abs(z)^(-alpha), and epsilon-approximation. It does not misstate an infimum as a finite-path minimum.

## O-7.01 — rank-one formal solutions (§§1–2, pp. 229–232).

Existing `DLMF.AsymptoticApproximations.IsRankOneAtInfinity`, `DLMF.AsymptoticApproximations.rankOneExponent`, and `DLMF.AsymptoticApproximations.rankOneCoeff` are the actual distinct-root Laurent data, exact mu, and normalized finite coefficient recursion. New `DLMF.AsymptoticApproximations.RankOne.rankOneCoeff_formal_operator_eq_and_unique` identifies these with the unique constant-one formal solution of the fully conjugated operator. Its coefficient extraction is actual finite arithmetic via `DLMF.AsymptoticApproximations.RankOneForcing.operatorCoefficient`, not evaluation of a divergent series. The denominator pc0+2*lambda is explicitly nonzero.

## O-7.02 — canonical solutions (Theorem 2.1, pp. 232–234).

New `DLMF.AsymptoticApproximations.RankOne.exists_unique_differentiated_solutions` uses literal exp(lambda*z)*z^mu, with no extra constant from the sector-orienting log(lambda2-lambda1). It gives actual analytic logarithmic-plane solutions, both all-orders expansions, first two differentiated remainder estimates, and uniqueness on the whole stated sectors. Restricting the widened sectors gives the source canonical pi-half-angle sectors and all closed subsectors. Existing `DLMF.AsymptoticApproximations.rankOne_exists_unique_solutions` uses a different constant power normalization, which is related by the explicit constant exp(-mu*log(lambda2-lambda1)); it is not silently treated as the literal source normalization.

## O-7.03 — enlarged sectors (Theorem 2.2, p. 235).

New `DLMF.AsymptoticApproximations.RankOne.canonicalSector` retains the actual unwrapped first and second sectors of opening 3*pi-2*delta on one common logarithmic plane. `DLMF.AsymptoticApproximations.RankOne.exists_unique_differentiated_solutions` includes both function expansions and differentiated remainders there. No boundary ray at the full 3*pi opening is included. The derivative remainder uses exp(j*w) times the Nth scale, so it remains meaningful when a characteristic root is zero and its formal leading derivative vanishes.

## O-7.04 — analytic parameter dependence (Theorem 3.1, pp. 236–237).

New `DLMF.AsymptoticApproximations.RankOne.ParameterData` fixes distinct characteristic roots and leading coefficients, holomorphic parameter Laurent coefficients and actual convergent common geometric majorants on every compact parameter set. `DLMF.AsymptoticApproximations.RankOne.ParameterData.analyticOnNhd_exponent_coeff` gives holomorphic mu and every finite recursive coefficient. `DLMF.AsymptoticApproximations.RankOne.ParameterData.exists_analytic_canonical_family` gives locally joint analytic canonical solutions on the full lifted exterior, analytic first two argument derivatives and locally uniform differentiated asymptotic remainders with the actual varying exponent and any holomorphic initial multiplier, including its zeros. This is normalization at infinity, not only finite-IVP parameter dependence.

## O-7.05 — coincident characteristic roots (§4, pp. 237–238).

Existing `DLMF.AsymptoticApproximations.fabry_transformation` is the exact change W(t)=exp(pc0*t^2/2)*w(t^2), with both actual transformed coefficients and the necessary t nonzero hypothesis. `DLMF.AsymptoticApproximations.fabry_coefficients` gives their convergent even inverse-power Laurent expansions and the characteristic dichotomy. Since t maps to t^2, choosing a logarithmic branch amounts to t=exp(w/2); this is the actual ramified cover, without independently principalizing a square root. If qc1=pc0*pc1/2 the transformed equation has regular-singular infinity; otherwise its characteristic roots are plus/minus sqrt(2*pc0*pc1-4*qc1). Substitution of the existing rank-one recursion then gives the source half-power formal expansion; convergence of that formal expansion is not claimed.

## O-7.06 — cylinder functions and normalization (§§5–6, pp. 238–244).

Canonical `DLMF.Bessel.besselYOnLog`, `DLMF.Bessel.hankelH1OnLog`, and `DLMF.Bessel.hankelH2OnLog` retain the removable integer-order normalization. New `DLMF.Bessel.analyticOnNhd_cylinderOnLog`, `DLMF.Bessel.cylinderOnLog_recurrences`, and `DLMF.Bessel.cylinderOnLog_ode` give joint entire order/log-coordinate dependence, both recurrence/derivative identities for J/Y/H1/H2, and the actual lifted differential equation. Existing `DLMF.Bessel.wronskian_besselJ_besselY` and `DLMF.Bessel.wronskian_hankelH1_hankelH2` give 2/(pi*z) and -4*i/(pi*z) on a branch; analytic continuation gives every carried branch. No nonintegral-order restriction remains.

## O-7.07 — Hankel expansions (§5, pp. 239–241).

Existing `DLMF.Bessel.largeArgumentCoefficient` is the exact product a_k; `DLMF.Bessel.hasAsymptoticExpansion_hankelH1OnLog` and `DLMF.Bessel.hasAsymptoticExpansion_hankelH2OnLog` give both full 3*pi lifted sectors. `DLMF.Bessel.isBigO_besselJOnLog_remainder` / `DLMF.Bessel.isBigO_besselYOnLog_remainder` retain both exponential absolute remainder scales, including near trigonometric zeros. New `DLMF.Bessel.isBigO_hankelOnLog_derivative_remainder` gives the first derivative expansion with the actual `DLMF.Bessel.hankelOnLogPartialSum`. Principal bridges are the existing OnLog/log lemmas; no argument is independently reduced modulo 2*pi.

## O-7.08 — zeros and their simplicity (Theorem 6.1, pp. 244–245).

Existing `DLMF.Bessel.deriv_ne_zero_of_bessel_solution_eq_zero` and `DLMF.Bessel.iteratedDeriv_two_ne_zero_of_bessel_solution_deriv_eq_zero` state the generic analytic-solution zero and derivative-zero simplicity assertions on a connected open branch domain. Nontriviality and exclusion of the origin are explicit; derivative simplicity excludes precisely z^2=nu^2. These are already general in complex order and therefore cover the source real-order assertions without duplicate targets.

## O-7.09 — reality and exclusion near the origin (Theorem 6.2 and Lemma 6.1, pp. 245–246).

Existing `DLMF.Bessel.im_eq_zero_of_besselJ_eq_zero` gives reality of nonzero J zeros for real nu>-1; `Complex.besselJ_neg_int` reduces nu=-1 to nu=1. `DLMF.Bessel.im_eq_zero_of_diniNormalized_eq_zero`, with the zero Robin coefficient, gives derivative reality for nu>=0 after its normalized derivative bridge. `DLMF.Bessel.existsUnique_imaginary_deriv_besselJ_zero` gives exactly the imaginary pair for -1<nu<0. `DLMF.Bessel.exists_uniform_besselJ_ne_zero` and `DLMF.Bessel.exists_uniform_deriv_besselJ_ne_zero` give the source uniform-in-order neighborhoods, including all positive orders above the chosen margin. A leading reciprocal-Gamma zero at a negative integer is not used as a false nonvanishing argument.

## O-7.10 — parameterized zeros (Theorems 6.3–6.4, p. 246).

Existing `DLMF.Bessel.exists_positive_besselJ_zero_family` gives complete increasing positive-zero enumerations, C1 dependence and strict order monotonicity throughout nu>-1. `DLMF.Bessel.exists_positive_deriv_besselJ_zero_family` gives derivative-zero C1 dependence on nu>0 and the first-zero bound >nu. `DLMF.Bessel.besselJ_deriv_positive_zeros_interlace` gives the exact complete indexed chain. These enumerate every positive zero, so a shifted subsequence cannot satisfy the source indexing.

## O-7.11 — McMahon expansion of large zeros (§6, pp. 246–248).

New `DLMF.Bessel.hankelCosineSeries`, `DLMF.Bessel.hankelSineSeries`, `DLMF.Bessel.besselZeroPhaseSeries`, and `DLMF.Bessel.besselZeroCorrectionSeries` give the actual formal tangent/phase reversion algorithm. `DLMF.Bessel.coeff_besselZeroCorrectionSeries_le_three` gives exactly both displayed corrections and the zero even coefficients through degree three. `DLMF.Bessel.Real.hasAsymptoticPowerSeries_besselJ_positive_zeros` gives the full all-orders correction for complete J indexing, nu>-1. `DLMF.Bessel.Real.hasAsymptoticPowerSeries_besselY_positive_zeros` gives the full Y correction and complete indexing for nu>-1/2, the connected component continued from nu=1/2 used in the source pp248--249. At nu=-1/2 a zero reaches zero and the complete-positive enumeration shifts; unchanged indexing is not extended across that event. Existing finite McMahon targets are special cases.

## O-7.12 — separation of cylinder zeros (Theorems 7.1–7.2, pp. 248–249).

Existing `DLMF.Bessel.existsUnique_cylinder_zero_between` gives arbitrary independent real cylinder-function interlacing. `DLMF.Bessel.exists_positive_besselY_zero_family` gives complete C1 and order-increasing Y zeros for nu>-1/2; `DLMF.Bessel.besselY_besselJ_positive_zeros_interlace` gives their exact indexed chain. Upstream `TauCeti.argumentPrinciple_windingNumber` gives the meromorphic argument principle as the winding-number weighted sum of zero/pole orders; `TauCeti.argumentPrinciple_windingNumber_of_analyticOnNhd` is its analytic specialization. For a positive simple contour, inside winding is one and outside zero, so this is exactly change-of-argument/(2*pi)=number of zeros minus poles with multiplicity.

## O-7.13 — modified cylinder functions (§8, pp. 250–253).

Canonical lifted I/K functions have the removable integer-order definitions. New `DLMF.Bessel.besselIOnLog_eq_besselJOnLog`, `DLMF.Bessel.modifiedCylinderOnLog_recurrences`, and `DLMF.Bessel.cylinderOnLog_ode` give the exact correlated rotation, shifts/derivatives and modified equation. Existing `DLMF.Bessel.besselK_neg`, `DLMF.Bessel.wronskian_besselK_besselI`, and `DLMF.Bessel.besselK_eq_integral_cosh` give symmetry, 1/z Wronskian and the all-complex-order integral for Re(z)>0. Existing `DLMF.Bessel.hasAsymptoticExpansion_besselKOnLog` and `DLMF.Bessel.hasAsymptoticExpansion_besselIOnLog` give the full required lifted sectors. New `DLMF.Bessel.besselIOnLog_eq_besselKOnLog_connection`, `DLMF.Bessel.besselKOnLog_add_int_mul_pi`, and `DLMF.Bessel.isBigO_besselIOnLog_two_exponentials` give the exact upper/lower continued connection, integer-order-safe Chebyshev sine quotient, and full two-exponential I remainder. Principal reevaluation after a half-turn is not substituted for continuation.

## O-7.14 — modified monotonicity and zeros (Theorems 8.1–8.2, pp. 251–252).

Existing `DLMF.Bessel.besselI_ofReal_pos` and `DLMF.Bessel.besselK_ofReal_pos` give positivity. `DLMF.Bessel.Real.strictMonoOn_re_besselI`, `DLMF.Bessel.Real.strictAntiOn_re_besselK`, `DLMF.Bessel.Real.strictAntiOn_re_besselI_order`, and `DLMF.Bessel.Real.strictMonoOn_re_besselK_order` give both argument and order monotonicities. `DLMF.Bessel.besselK_ne_zero_of_nonneg_re` retains the closed half-plane, including nonzero imaginary-axis boundary. `DLMF.Bessel.besselK_isEquivalent_cpow_nhds_zero` and `DLMF.Bessel.besselK_zero_isEquivalent_neg_log_nhds_zero` give both cut-sector small-argument forms. Their order and branch restrictions match the source; real-only positivity is not used to imply complex nonvanishing.

## O-7.15 — confluent hypergeometric functions (§9, pp. 254–258).

Canonical `DLMF.Confluent.kummerM` is ordinary M and Mathlib `Complex.regularizedHGFun` is the distinct reciprocal-Gamma regularization. Existing `DLMF.Confluent.hasFPowerSeriesOnBall_kummerM`, `DLMF.Confluent.kummerM_ode`, `DLMF.Confluent.kummerM_eq_euler_integral`, `DLMF.Confluent.kummerM_kummer_transform`, and `DLMF.Confluent.kummerU_kummer_transform_all` give the series, equation, Euler integral and transformations on their exact domains. New `DLMF.Confluent.differentiable_regularizedKummer_parameters_argument` gives full joint entire dependence in (a,c,z), including exceptional c. Existing `DLMF.Confluent.wronskian_regularizedHGFun` gives precisely sin(pi*c)/pi*exp(z)*z^(-c) for the regularized local pair; no ordinary Gamma factor is lost.

## O-7.16 — Tricomi solution and exact connections (§9, pp. 255–258).

Existing `DLMF.Confluent.kummerU_laplace`, `DLMF.Confluent.kummerU_eq_connection`, and the canonical integer-parameter limiting definition give the normalized Tricomi integral and entire parameter limits. `DLMF.Confluent.regularizedHGFun_eq_kummerU_connection` has upper sign=false (positive displayed phases, rotated argument through the lower half-plane) and lower sign=true (reversed phases and rotated argument through the upper half-plane). New `DLMF.Confluent.regularizedConfluent_eq_tricomi_continued` continues both exact identities on the entire logarithmic plane with the correlated w plus/minus pi*i shift. Existing `DLMF.Confluent.wronskian_regularizedHGFun_kummerU_all` gives W(Mtilde,U)=-exp(z)*z^(-c)/Gamma(a); swapping the Wronskian gives exactly the source W(U,Mtilde) with positive sign. All reciprocal-Gamma zeros are retained.

## O-7.17 — confluent asymptotics and specializations (§§9–10, pp. 257–262).

Existing full `DLMF.Confluent.kummerUContinuedOnLog` and `DLMF.Confluent.hasAsymptoticExpansion_kummerUContinuedOnLog` acquire the entire 3*pi-minus-margin wound Tricomi sector, with integer second parameter defined by a whole limit. New `DLMF.Confluent.isBigO_regularizedConfluentOnLog_two_exponentials` gives both upper/lower lifted M expansions of opening 2*pi-minus-margin with both absolute scales, including vanishing reciprocal-Gamma coefficients. Exact reductions are `DLMF.Confluent.kummerU_besselK`, the defining equation of `DLMF.Confluent.upperIncompleteGamma`, the fully proved `DLMF.Confluent.kummerU_eq_laguerreExtended`, and new `DLMF.Confluent.parabolicCylinderU_eq_kummerUContinuedOnLog` with its actual correlated 2*w-log(2) argument. Existing `DLMF.Confluent.whittakerWContinuedOnLog` and `DLMF.Confluent.hasAsymptoticExpansion_whittakerWContinuedOnLog` retain the whole wound Whittaker sector; canonical Whittaker definitions/equations preserve ordinary versus regularized M and its exceptional lower parameters. Large-parameter LG follows by applying O-6.07 only after verifying the displayed Whittaker coefficient is zero-free on the selected progressive domain.

## O-7.18 — computable residual error (Theorem 12.1, pp. 265–270).

New `DLMF.AsymptoticApproximations.RankOneComparison.shift`, `DLMF.AsymptoticApproximations.RankOneComparison.comparisonFunction`, `DLMF.AsymptoticApproximations.RankOneComparison.coefficientP`, `DLMF.AsymptoticApproximations.RankOneComparison.coefficientQ`, `DLMF.AsymptoticApproximations.RankOneComparison.truncation`, and `DLMF.AsymptoticApproximations.RankOneComparison.residual` are the exact computable source expressions, with proved defining APIs. `DLMF.AsymptoticApproximations.RankOneComparison.comparison_pair_equations` gives the actual nowhere-zero Wronskian (lambda2-lambda1)*exp(-pc0*z-pc1*Log(z)), P0=-Wprime/W, and both comparison equations outside the shift circle on any actual analytic logarithm branch. New `Complex.complexGreen_derivative_coupling_error` gives the complete derivative-coupled residual Green equation, derivative equation, arbitrary finite initial errors and explicit A/B absolute bounds. `Complex.exists_complexGreen_derivative_coupling_endpoint` gives the actual absolutely convergent initial-tail correction with both zero normalized endpoint errors and the same bounds. The broader progressive kernel weighting is `ODE.WeightedVolterra.Data.existsUnique_isSolution`; choose phi=-R_N, psi0=-(q-Q0), psi1=-(p-P0). Thus nonconvergent coefficient asymptotics are allowed whenever those actual kernel variations converge; no unknown O constant replaces the displayed computation.

## O-7.19 — inhomogeneous formal series (Theorem 14.1, pp. 274–276).

New `DLMF.AsymptoticApproximations.RankOneForcing.coefficient` is the actual forced Laurent recursion with a0=r0/q0. `DLMF.AsymptoticApproximations.RankOneForcing.operatorCoefficient` explicitly extracts every coefficient of the conjugated differential operator by finite sums. `DLMF.AsymptoticApproximations.RankOneForcing.coefficient_operator_eq_and_unique` gives formal correctness and uniqueness under q0 nonzero. `DLMF.AsymptoticApproximations.RankOneForcing.exists_finite_sectorial_expansion` gives an actual analytic inhomogeneous logarithmic-plane solution with every prescribed finite truncation and its O(exp((alpha-N)*w)) remainder on the simultaneous root/difference progressive sectors. All four constant logarithms are supplied with their actual exponential values, allowing arbitrary compatible unwrapped phases. The solution may depend on N and the sector, exactly as the source requires; it is not falsely promoted to a global all-orders particular solution.

## O-7.20 — Struve functions (§15, pp. 276–278).

Canonical `DLMF.Struve.struveH` is the reciprocal-Gamma series and `DLMF.Struve.struveK` is H-Y, distinct from modified Bessel K. Existing `DLMF.Struve.struveH_ode`, `DLMF.Struve.struveH_eq_poisson`, and `DLMF.Struve.struveK_laplace` give the inhomogeneous equation, sin-Poisson integral and exact Laplace kernel. The K Laplace target is already valid for every complex order and Re(z)>0; no unnecessary Re(nu)>-1/2 restriction is added there. `DLMF.Struve.struveK_asymptotic_rotSector` and `DLMF.Struve.struveK_asymptotic` give the full coefficient series with both rotated and combined |arg(z)|<pi sectors, and the existing signed-remainder bound controls the first omitted term on the stated real range. These are exact source normalizations, not only a generic Watson lemma.

## O-8.01 — Bernoulli system (§1, pp. 279–284).

Canonical Mathlib `bernoulli` / `Polynomial.bernoulli` and DLMF `bernoulliPolyB` retain the B1=-1/2 convention. Existing `hasSum_bernoulliPolyB_mul_pow_div`, `hasDerivAt_bernoulliPolyB`, `bernoulliPolyB_one_sub`, `bernoulliPolyB_eq_sum`, `bernoulliPolyB_zero_one`, `bernoulli_two_mul_add_one_eq_zero_and_sign` and `bernoulliPolyB_mul` cover generating functions, derivative, reflection, finite expansion, endpoints, odd vanishing and multiplication. `integral_bernoulliFun_add_one n 0`, simplified by n>0, gives the zero integral. Exact upstream Fourier pointers are `hasSum_one_div_nat_pow_mul_cos`, `hasSum_one_div_nat_pow_mul_sin` and `hasSum_one_div_pow_mul_fourier_mul_bernoulliFun` (recorded in Core.UpstreamElementary). `tendsto_sum_sin_div_eq_bernoulliFun_one` gives the natural-order B1 sine series only for 0<x<1; translation gives its noninteger periodic version. No false pointwise claim at integer discontinuities is used.

## O-8.02 — Bernoulli zeros and bounds (Theorem 1.1, p. 283).

Existing `DLMF.BernoulliEuler.bernoulliFun_even_sub_zeros_Icc` and `bernoulliFun_odd_zeros_Icc` give the exact zero sets. `abs_bernoulliFun_two_mul_lt` supplies the strict interior bound; at either endpoint the endpoint value is B_(2s), extending it weakly to [0,1]. `abs_bernoulliFun_two_mul_sub_le` is the sharp difference bound, and `bernoulliPolyB_half` is the midpoint value. These cover every valid subclaim; no extra target is needed.

## O-8.03 — Euler–Maclaurin with integral remainder (§2, pp. 284–287).

New [DLMFMathlib/Analysis/EulerMaclaurin/AbsolutelyContinuous.lean](DLMFMathlib/Analysis/EulerMaclaurin/AbsolutelyContinuous.lean) gives `Real.EulerMaclaurin.sum_Ico_eq_integral_add_evenRemainder` with C^(2m-1) closed-interval data, absolute continuity of its last derivative and L1 final derivative. The explicit remainder uses the same periodic Bernoulli difference. `abs_evenRemainder_le_integral`, `sign_and_abs_evenRemainder_le_endpoint` and `abs_evenRemainder_le_endpoint_of_two_even_signs` give the sharp factor, sign and factor-one refinement, including a.e. highest derivatives. `tendsto_sum_sub_integral_sub_endpoint_terms` records the improper constant as the convergent remainder integral. These targets are admitted; the older global C^(2m) theorem is a proved special case.

## O-8.04 — power sums and harmonic numbers (§§2–3, pp. 285–292).

Existing `powerSum_asymptotic` / `powerSum_remainder_bound` give the complete sum-to-n-1 expansion. Mathlib Faulhaber supplies exact finite termination at nonnegative integral powers. `harmonic_asymptotic` / `harmonic_remainder_bound` use H_(n-1); `harmonic_succ` and n-1+1=n for n>0 add precisely 1/n, changing -1/(2n) to +1/(2n) while retaining all higher terms and the same remainder. `jLogJSum_eq`, `jLogJRemainder_bound` and `Gamma.glaisherKinkelin_eq_zeta_neg_one` give the hyperfactorial-logarithm expansion and C=1/12-zeta'(-1). The synopsis has the opposite sign on its higher Bernoulli terms: the existing `sumMulLogTerm` is source-correct with a preceding minus. This synopsis revision is deferred and documented, rather than asserting the false plus-sign variant.

## O-8.05 — Abel–Plana and the Bernoulli moment (Lemma 3.1, pp. 289–292).

New [DLMFMathlib/Analysis/Complex/FiniteAbelPlana.lean](DLMFMathlib/Analysis/Complex/FiniteAbelPlana.lean), `Complex.sum_Icc_sub_endpoints_eq_integral_add_vertical_limit`, retains holomorphy only inside the strip, continuity on its boundary, the uniform o(exp(2pi|y|)) growth and an explicitly convergent ordinary vertical integral at both zero and infinity. No boundary derivative or absolute vertical convergence is imposed. Real symmetry turns each conjugate difference into 2i times its imaginary part, giving the printed real formula by linearity. `bernoulli_two_mul_eq_integral_exp_sub_one` with u=2pi*y gives the moment (-1)^(m-1)B_(2m)/(4m).

## O-8.06 — Stirling logarithm and Stieltjes bound (§4, pp. 293–295).

New DLMF.Gamma.logGammaStieltjesRemainder with proved defining residual; integrableOn_logGammaStieltjesRemainder and logGammaStieltjesRemainder_eq_integral give the exact periodic-Bernoulli remainder. norm_logGammaStieltjesRemainder_le gives the explicit sec(arg/2)^(2m) bound, and logGammaStieltjesRemainder_sign_and_norm_lt gives strict signed first-omitted-term control for positive real z. Parent SectorExpansions logGamma_stirling_sector / scaledGamma_sector_expansion and gammaStirlingCoeff_recurrence cover the full sector expansions and coefficient exponentiation. AAR JointComplex.logGamma_integral_binet_arctan gives Binet's alternative complex integral.

## O-8.07 — summation by parts and oscillatory sums (§5, pp. 295–299).

The finite identity is existing `DLMF.AsymptoticApproximations.sum_by_parts`. New [DLMFMathlib/Analysis/Asymptotics/OscillatoryPowerSums.lean](DLMFMathlib/Analysis/Asymptotics/OscillatoryPowerSums.lean) defines `Complex.OscillatoryPowerSum.coefficient` by the actual triangular recurrence, with proved zero/successor equations, and states its coefficientwise formal functional equation. `constant` is a specified renormalized partial-sum limit, with existence in `tendsto_sub_tail`. `isBigO_sub_constant_sub_tail` uses that same constant at every order. `tendsto_partialSum` gives its natural Dirichlet value for alpha<0. No totalized sum is assigned to a divergent series.

## O-8.08 — Barnes representation (§6, pp. 299–302).

`Complex.BarnesContour` and the Gauss BarnesContours API give finite deformations, absolute and locally uniform tails, full principal-cut regularized normalization and right residues. New [DLMF/Hypergeometric/BarnesLeftResidues.lean](DLMF/Hypergeometric/BarnesLeftResidues.lean) specifies the actual normalized residue of every left pole by a small circle, both complete exterior residue series, and their local uniform convergence. `regularizedGaussHypergeometric_eq_connectionNumerator_deriv` gives every integral-upper-difference value as the derivative of the combined sine-cleared numerator. Differentiating (-z)^(-b) supplies the logarithm; neither singular family is totalized before taking this derivative. Existing `tendsto_connection_inv` supplies the corresponding whole-family removable limit.

## O-8.09 — alternating quadratic sum (§7, pp. 302–304).

New DLMF.Bessel.tendsto_alternatingQuadraticSum_eq_macdonald states the symmetric ordinary limit for Re alpha>0,Re z>0 with exactly the source K-series constants and continued principal powers. summableLocallyUniformlyOn_norm_alternatingQuadratic_macdonald gives absolute local uniform convergence in both parameters. isBigO_alternatingQuadratic_macdonald_tail gives the next exponential tail scale on every proper closed right subsector after each fixed finite truncation. The left sum is not incorrectly replaced by an absolutely convergent tsum when Re alpha<=1/2.

## O-8.10 — polylogarithm near its boundary (§7, pp. 304–306).

Existing `DLMF.Zeta.PolylogLogarithmic.hasSum_regularized` is precisely the convergent logarithmic expansion with s=-alpha, on the principal slitOne branch and norm(log z)<2pi. New [DLMF/Zeta/Polylog/OrderAndRemovableLog.lean](DLMF/Zeta/Polylog/OrderAndRemovableLog.lean) gives entire order analyticity for every fixed slitOne argument and the combined Gamma-plus-zeta parameter limit at positive integral s. The explicit integer expansion for m>=2 is the existing `LerchLogarithmic.hasSum_lerchPhi_log_nat_of_re_pos` at a=1, using `polylog_eq_mul_lerchPhi_of_mem_slitOne`, `hurwitzZetaComplex_one` and `Complex.digamma_nat_add_one`; m=1 is -log(1-z). No continuation across the chosen principal cut is claimed.

## O-8.11 — factorial-power entire function (§8, pp. 307–309).

New Complex.summableLocallyUniformly_factorial_rpow and analyticOnNhd_tsum_factorial_rpow give the entire power-series function in z=x^p; Real.summable_factorial_rpow gives the positive-x series. Real.isBigO_tsum_factorial_rpow gives exactly the first correction and relative O(x^-2) for 0<p<=4. For nonintegral p, entireness is in the series variable z, not in x through its branch point.

## O-8.12 — Darboux transfer (§9, pp. 309–310).

Existing `DLMF.AsymptoticApproximations` Darboux transfer and Darboux derivative modules. Exact Laurent annulus and L1 radial boundary passage still to compare.

## O-8.13 — Legendre Darboux coefficients and its convergence warning (§10, pp. 311–314).

New [DLMF/AsymptoticApproximations/Sums/LegendreDarbouxComplete.lean](DLMF/AsymptoticApproximations/Sums/LegendreDarbouxComplete.lean) gives every explicit binomial/phase term, the sharp finite-truncation O(n^(-m-3/2)) remainder after inclusive indices 0..m, and `hasSum_term` showing that the convergent complete generalized series sums to twice P_n on pi/6<theta<5pi/6. Thus it directly formalizes the convergence/non-equality warning. Source p312 uses m+1 terms, while the synopsis incorrectly says first m terms with that error; the source-correct inclusive target is acquired and the synopsis discrepancy recorded separately. Existing Darboux and LegendreDarboux cover the generating function and leading comparison.

## O-8.14 — Laplace inversion (Theorem 11.1, pp. 315–316).

The existing `laplace_inversion` already admits the line c=sigma but assumes differentiability on the whole positive axis. New [DLMFMathlib/Analysis/Integral/LaplaceBoundaryInversion.lean](DLMFMathlib/Analysis/Integral/LaplaceBoundaryInversion.lean), `Complex.tendsto_laplace_vertical_integral_of_one_sided_derivatives`, requires only absolute integrability after the exponential weight and finite one-sided derivative traces at the inversion point. It averages the two traces and includes c=sigma. Function.update encodes the one-sided trace without forcing the original point value to agree with either side. The outer symmetric integral is not asserted to converge absolutely.

## O-8.15 — Haar transfer and Volterra example (§11, pp. 316–320).

New [DLMFMathlib/Analysis/Fourier/UniformImproperTransfer.lean](DLMFMathlib/Analysis/Fourier/UniformImproperTransfer.lean) gives the boundary C^m Haar theorem from separate positive/negative uniformly convergent ordinary Fourier tails of every derivative. It does not assume analytic extension across the contour. Applying it to (F-G)(r+i*y) and multiplying by exp(r*t)/(2pi) yields the source transfer after its assumed contour deformation; pole/branch contributions are exactly the separately assumed residue/Hankel contributions. New [DLMF/Gamma/Volterra.lean](DLMF/Gamma/Volterra.lean) defines the actual V(a,t), states absolute convergence, the transform p^(-a)/log p for p>1 including a=0, and its all-orders inverse-log expansion after subtracting the exponential residue.

## O-9.01 — logarithmic Watson lemma (Theorem 1.1, pp. 323–324).

New [DLMFMathlib/Analysis/Asymptotics/WatsonLogarithmicOrdinary.lean](DLMFMathlib/Analysis/Asymptotics/WatsonLogarithmicOrdinary.lean), `Complex.isBigO_laplace_log_pow_sub_sum_of_tendsto`, covers every natural logarithm power, ramified exponents, all finite remainder orders and the exact finite binomial combination of Gamma derivatives. Its hypotheses retain the ordinary improper limit for every sufficiently large Laplace parameter, rather than imposing absolute integrability on a conditionally convergent source integral. Existing WatsonLog/WatsonComplexLog supply the proved first-log absolute-convergence specializations.

## O-9.02 — fractional logarithmic weight (Theorem 1.2, p. 324).

New [DLMFMathlib/Analysis/Asymptotics/FractionalLogWatson.lean](DLMFMathlib/Analysis/Asymptotics/FractionalLogWatson.lean) defines `Real.FractionalLogWatson.moment`, states its absolute convergence and strict positivity, the sharper finite moment expansion for locally integrable Banach-valued amplitudes, and the all-orders inverse-logarithm expansion using Ring.choose(beta,j), signs and Gamma derivatives. The two expansion scales remain distinct.

## O-9.03 — perturbed Laplace endpoint (Theorem 2.1, pp. 326–328).

New Asymptotics.isBigO_perturbed_laplace_endpoint in PerturbedLaplace retains all exponents and the exact minimum error exponent, complex amplitude/perturbation, continuous data and phase-derivative estimates on the finite interval. isBigO_perturbed_laplace_endpoint_of_nonpos removes alpha<1 under a nonpositive real perturbation, as in the source. Independent tails remain the responsibility of each application.

## O-9.04 — Bell-number saddle (§3, pp. 329–331).

Existing `DLMF.Combinatorics.existsUnique_mul_log_eq` proves the unique exact saddle; the older bell_isBigO has a weaker relative error. New [DLMF/Combinatorics/BellSaddle.lean](DLMF/Combinatorics/BellSaddle.lean) chooses that exact saddle with a proved value_spec, fixes a_n=exp(1)*Nat.bell(n)/n!, states the sharp relative O(1/N) coefficient estimate and gives an explicit first-inverse-log substitution whose putative main term has unbounded ratio to the correct one. Thus the warning is an actual counterexample, rather than an unsupported claim that saddle substitution is always valid.

## O-9.05 — Faxén function and critical perturbation (Theorem 4.1, pp. 332–333).

New DLMF.AsymptoticApproximations.faxenIntegral is the genuine positive-axis integral with positive-real powers; faxenIntegral_def is proved. integrableOn_faxenIntegral, analyticOnNhd_faxenIntegral and hasSum_faxenIntegral give absolute convergence, entireness and the Gamma-coefficient Taylor expansion for 0<=Re a<1,Re b>0. faxenIntegral_half_half and faxenIntegral_third_third give exactly the erf/Scorer Hi specializations. New generic Asymptotics.isBigO_critical_perturbed_laplace_endpoint supplies the critical scaling and full explicit minimum error exponent; the leading Faxen integral may vanish, so the error is absolute after division by the common prefactor.

## O-9.06 — transition-scale examples (§5, pp. 334–336).

New [DLMF/ParabolicCylinder/TransitionScale.lean](DLMF/ParabolicCylinder/TransitionScale.lean) states the fixed-real-a canonical U(n+1/2,a) formula with its exact Gamma normalization and relative O(n^(-1/2)) error. New [DLMF/Bessel/TransitionScale.lean](DLMF/Bessel/TransitionScale.lean) states the complex-compact uniform Bessel/Airy transition with absolute C/nu error, without dividing by Ai, so Airy zeros are included.

## O-9.07 — general kernel lemma (Lemma 6.1, p. 337).

Existing `DLMF.AsymptoticApproximations.watson_lemma_kernel` exactly gives the source ramified exponents (s+lambda)/mu, local integrability, positive stretched-exponential bounds for the kernel, exponential amplitude growth and the complete coefficient expansion in Mellin moments. Its N=0 remainder estimate supplies the general-kernel lemma. New `Complex.isBigO_integral_log_singular_kernel_sub_sum` in LogSingularKernel permits the logarithmic singularity needed for K0, while retaining the same power-order error.

## O-9.08 — Airy and Macdonald kernels (§6, pp. 337–339).

`DLMF.Airy.airyAi_mellin` and `DLMF.Bessel.besselK_mellin` give the exact complex Mellin moments. The kernel consequence follows from watson_lemma_kernel (Airy) and the new LogSingularKernel theorem (K0); their positive-real moments are substituted directly. For the explicit Airy leading estimate take exponents 1 and 1+delta, use `airyAi_positive_integral` for 1/3, and retain the source exponential growth in v^(3/2). The stretched-exponential kernel bound follows from the existing Airy asymptotic envelope on the tail and continuity on a compact initial interval. No globally bounded-kernel claim is made for the singular K0.

## O-9.09 — Nicholson integral (Theorem 7.1, pp. 340–342).

Existing new CylinderMagnitude targets give the complex-order/right-half-plane Nicholson integral, absolute and joint locally uniform convergence, all strict real monotonicity cases and the half-order equality. The remaining algebraic evenness is now proved in foundational `DLMF.Bessel.besselJ_sq_add_besselY_sq_neg_order` in Basic.SecondKind, by the exact J/Y reflection rotation and cos^2+sin^2=1. It holds for every complex order on the principal slit plane, hence includes the stated real positive-ray case.

## O-9.10 — oscillatory Airy kernel (§8, pp. 342–344).

Confirmed synopsis revision: source p343 (8.02) has A_n(v)=O(v^(-n/2-1/4)), not the false exponent printed in the synopsis. Correct-source new definitions and targets: `DLMF.Airy.oscillatoryTail`, `hasIntegralAtTop_oscillatoryTail`, `isBigO_oscillatoryTail`, `oscillatoryTail_zero_arg`, `hasIntegralAtTop_airyAi_neg_mul`, `airyAi_neg_kernel_expansion`. The full source derivative-growth condition v^((2s-3-delta_s)/4) is retained. SYNOPSIS is unchanged; see RevisionNotes.

## O-9.11 — Bleistein endpoint transformation (§9, pp. 344–346).

Existing bleistein_quadratic / bleisteinW API gives the exact increasing quadratic substitution and amplitude formula. New [DLMF/AsymptoticApproximations/Integrals/BleisteinMoments.lean](DLMF/AsymptoticApproximations/Integrals/BleisteinMoments.lean), `bleisteinF_eq_sum_parabolicCylinderU`, evaluates every centered polynomial moment as an explicit finite combination of Gamma factors and canonical U(lambda+k-1/2,-y). Scaling w by sqrt(x) gives the printed moments. Taylor-at-alpha coefficients are iteratedDeriv(s) of the transformed amplitude divided by s!, by the existing analytic Taylor API. Finite endpoint to infinite-moment replacement remains conditional on its separately stated remainder and tail bounds, as in the source.

## O-9.12 — rigorous endpoint coalescence example (§10, pp. 346–351).

New [DLMF/AsymptoticApproximations/Integrals/CosineEndpoint.lean](DLMF/AsymptoticApproximations/Integrals/CosineEndpoint.lean) defines the actual two-branch monotone inverse of the cosine phase, transformed upper endpoint, inverse-Jacobian coefficients and centered Gaussian moments. Targets specify exact endpoint and phase identities, a convergent inverse-Jacobian Taylor germ, all three printed coefficients, moment evaluation through bleisteinF and the complete parameter-uniform finite error including a=0. Endpoint derivatives are taken within the physical interval to avoid a false derivative claim for the totalized inverse outside its range.

## O-9.13 — Chester–Friedman–Ursell reduction (§11, pp. 351–352).

New [DLMFMathlib/Analysis/Complex/AnalyticCubicCoordinates.lean](DLMFMathlib/Analysis/Complex/AnalyticCubicCoordinates.lean) gives a parameter-analytic cubic normal form at an order-three critical point, a locally nonzero inverse-coordinate derivative, the normalization of that derivative and analytic transformed amplitudes across coalescence. `cubic_saddle_values` proves both exact mean/difference identities algebraically. Existing cfu_airy_form gives the Airy contour reduction; new ShiftedScorerMoment.integral_exp_cubic_eq_scorerHi gives the exact Scorer endpoint contour and its scaling. No global uniform contour-deformation theorem is inferred from this local normal form alone.

## O-9.14 — Anger–Scorer uniform expansion (§§12–13, pp. 352–360).

New [DLMF/Struve/Asymptotics/ScorerTransition.lean](DLMF/Struve/Asymptotics/ScorerTransition.lean) uses the canonical angerA, defines its actual cubic inverse and derivative-based reversion coefficients, and states exact inverse identities, their convergent local series and continuity through a=0. New [DLMF/Airy/Scorer/ShiftedMoments.lean](DLMF/Airy/Scorer/ShiftedMoments.lean) defines Qi_s, absolute convergence, the canonical Hi/Hi' bridges, integration-by-parts recurrence and positivity of even moments. exists_uniform_remainder_le is the complete all-a>=0,nu>0 even-N weighted error estimate, with the exact source majorant; no odd moment is used as a positive error denominator.

## O-10.01 — Liouville classification (§1, pp. 362–363).

Existing liouville_caseI/II/III and bessel_approximating_equation give the supplied-coordinate equations. New Complex.liouville_normal_equation in ComplexLiouvilleTransformation gives the exact analytic amplitude/phase residual and displayed psi. TurningPointCoordinates.exists_analytic_simpleZero_liouville_coordinate and exists_analytic_simplePole_liouville_coordinate give normalized analytic coordinates with nonzero derivatives and analytic inverses; exists_analytic_liouville_coordinate_amplitude supplies the compatible amplitude branch. The simple-pole perturbation theorem retains its double pole rather than treating it as removable. Real simple-zero coordinates and inverses are actual weighted-integral definitions in ODE.RealTurningPoint.

## O-10.02 — coefficient algorithms (§2, pp. 364–366).

Complex.IsComplexLiouvilleGreenCoefficientSequence gives the exact linear A-recursion, and exists_complexLiouvilleGreenCoefficientSequence realizes arbitrary integration constants. New deriv_liouvilleGreenPartialSum gives the exact finite derivative identity with B0=1,Bs=As+A_(s-1)' and the explicit last derivative term. The exponential coefficients are the actual coefficients of Mathlib PowerSeries.logOf(PowerSeries.mk A). analyticOnNhd_liouvilleGreen_logarithmic_coefficient and liouvilleGreen_logarithmic_coefficient_recurrence give analyticity, E0=0,E1'=psi/2 and the full quadratic E differential recurrence. Mathlib PowerSeries.subst_exp_log and substitution associativity reconstruct the selected A-series formally from that logarithm when A0=1; no convergence is assumed and no free unmatched exponential constants are introduced.

## O-10.03 — finite-truncation theorem (Theorem 3.1, pp. 366–367).

New Complex.IsComplexLiouvilleGreenCoefficientSequence has proved API and existence with arbitrary integration constants. liouvilleGreenPartialSum is the genuine finite exponential sum, with proved definition/empty-sum API and exact residual target liouvilleGreenPartialSum_residual. exists_complexLiouvilleGreen_expansion_finite_reference gives exact initial matching and both source variation bounds on any progressive path; exists_complexLiouvilleGreen_expansion_endpoint_reference permits a prescribed recessive infinity tail and finite initial variations. Replacing u by -u gives the minus branch. The actual solution may depend on N, as the source allows.

## O-10.04 — convergence at a pole (Theorem 4.1, p. 369).

New Complex.IsOriginalVariableLiouvilleGreenCoefficientSequence is the exact original-variable recurrence, with proved interface and a phase-pullback target. In LiouvilleGreenSingularCoefficients, boundedVariationOn_liouvilleGreenCoefficient_at_higherPole gives every radial variation and finite limit under the strict higher-pole order condition; exists_analytic_extension_liouvilleGreenCoefficient_at_doublePole gives analytic extension in the exceptional -1/4 case. liouvilleGreen_doublePole_parameter_shift proves the parameter renormalization algebra. boundedVariationOn_liouvilleGreenCoefficient_at_infinity and exists_analytic_extension_liouvilleGreenCoefficient_at_infinity give both infinity cases. As the source p369 explicitly requires, the leading powers are terms of convergent Laurent expansions; a pointwise ray equivalent alone is not used to justify derivatives.

## O-10.05 — uniform bounded coefficients (Theorem 5.1, pp. 370–371).

New Complex.exists_uniform_liouvilleGreen_coefficient_bounds states the full parameter-uniform theorem: analytic coefficient sequences, one fixed interior ball buffer, uniform weighted psi bound, bounded reference values and explicitly supplied joining paths with bounded weighted arc length imply uniform bounds for A_s and derivative decay 1/(1+norm(xi)^(1+p)) for every s. The constants are independent of both parameter and phase point. Along any infinite tail with finite weighted arc length, the derivative bound immediately makes each coefficient variation integrable, proving the stated convergence consequence.

## O-10.06 — one solution with all orders (§6, pp. 371–373).

Complex.exists_allOrders_complexLiouvilleGreen_finite_reference constructs one analytic exact solution per parameter with every order simultaneously, uniformly on progressive joining paths under Theorem5.1. The finite initial data are chosen, not asserted unique. New exists_allOrders_complexLiouvilleGreen_endpoint_reference gives one recessively normalized exact solution at infinity with all orders outside the solution quantifier and the exact common variation majorant. Positive-index coefficient constants vanish on the prescribed tail. The uniform variations follow from the weighted coefficient theorem; no inference from unrelated finite-N solutions is made.

## O-10.07 — Debye polynomials and modified Bessel functions (§7, pp. 374–378).

DLMF.Bessel.Debye.polynomialU/polynomialV are genuine rational polynomial recursions with proved APIs; coefficientU_succ, polynomialU_one/two and natDegree_polynomialU give the source recursion, first values and degree. exists_uniform_besselI_debye_remainder, exists_uniform_besselK_debye_remainder and both derivative variants give every truncation uniformly on unbounded proper right subsectors. New DebyeContinuation defines the actual lifted phase, gamma originFactor, normalized I/K, coefficientSum and remainder; norm_remainder_I_le/K_le give exact U_n variation bounds along progressive paths and match canonical endpoint normalizations. normalizedFunction_I_cleared is proved and retains the finite-origin multiplier at small orders where division can fail; the large-order expansions are unaffected. See RevisionNotes for the p377 normalization caveat.

## O-10.08 — continuation domains (§8, pp. 378–382).

New Debye.liftDomain and phaseOnLog explicitly describe the logarithmic cover cut at the outer imaginary rays, with turning points removed. norm_remainder_I_le/K_le acquire the continuation estimates using monotonicity of Re(nu*eta), allowing complex orders with positive real part and the canonically normalized origin/infinity tails. Canonical all-integer half-turn formulas, including removable integer-order sine ratios, are DLMF.Bessel.besselFirstKindOnLog_add_int_mul_pi, besselKOnLog_add_int_mul_pi and besselIOnLog_eq_besselKOnLog_connection in LogarithmicMonodromy; its Chebyshev-U integer coefficient encodes the parameter limits. The cleared K relation follows by linear elimination of these two adjacent half-turn identities. These targets retain actual branch normalization rather than using fixed-order large-argument estimates.

## O-10.09 — general parameter-dependent coefficients (Theorem 9.1, pp. 382–386).

New Complex.IsAffineLiouvilleGreenCoefficientSequence and exists_affineLiouvilleGreenCoefficientSequence acquire the exact A recursion and arbitrary integration constants. affineLiouvilleGreenRemainder and affineLiouvilleGreenPartialSum are actual finite functions with proved APIs. liouvilleGreen_comparison_pair gives the exact comparison coefficient and Wronskian -2. affineLiouvilleGreenPartialSum_residual gives the distinct A_N'/T_N' residual. exists_affineLiouvilleGreen_finite_reference and exists_affineLiouvilleGreen_endpoint_reference give the exact three-variation lambda/mu bounds for finite and prescribed recessive infinite references, retaining the tail lower bound and all joining-path conditions. The exact Green residual equation is Complex.complexGreen_error_integral_and_bound instantiated with that comparison pair, R=the explicit truncation residual and T=Q-Q0=H'. This is a direct specialization with every kernel and weight specified.

## O-10.10 — inhomogeneous expansions (§10, pp. 386–388).

Complex.inhomogeneousExpansionCoefficient/PartialSum give the actual G recursion and sum with proved APIs; analyticOnNhd_inhomogeneousExpansionCoefficient is proved. inhomogeneousExpansionPartialSum_residual gives the exact residual, and inhomogeneousExpansionError_equation gives the signed two-reference primitive error. New InhomogeneousGreenBounds defines the actual two-tail path integrals with their derivatives. norm_inhomogeneousTwoTailError_le_of_integrable supplies the uniform L1 estimate 2CM/(c*norm(u)^(2N+1)); norm_inhomogeneousTwoTailError_le_of_exponential retains the decay rate and supplies 2CM/(c*a*norm(u)^(2N+2)). Uniform progressive LG complementary-product/Wronskian bounds instantiate C,c,a. Thus both stated asymptotic orders are explicit quantitative targets.

## O-10.11 — forced modified Bessel example (§11, pp. 388–390).

New DLMF.Bessel.forcedModifiedBesselCoefficient is the actual rational differential recursion, with proved zero/successor APIs. exists_polynomial_forcedModifiedBesselCoefficient gives denominator (1+z^2)^(3s+1), hence poles only at +/-i. forcedModifiedBesselPartialSum_residual gives the exact source residual with its sign. forcedModifiedBesselParticular is a single actual I/K ray-integral solution independent of N; integrable_forcedModifiedBesselParticular and forcedModifiedBesselParticular_equation state its endpoint convergence and forced equation. exists_uniform_forcedModifiedBesselParticular_remainder supplies every inverse-even-power truncation uniformly on unbounded proper right subsectors, with an explicit argument-growth weight and positive-real order threshold.

## O-11.01 — Airy normalization and real properties (§1, pp. 392–394).

Canonical Airy.Basic supplies airyAi/airyBi, hasDerivAt_airyAi/airyBi, both defining ODEs, airyAi_zero/airyAiDeriv_zero/airyBi_zero/airyBiDeriv_zero and wronskian_airyAi_airyBi. Real.airyAi_pos/airyBi_pos give positive-axis signs; new RealOrderProperties proves airyAiDeriv_neg_of_nonneg, airyBiDeriv_pos_of_nonneg and all four strict positive-axis monotonicities (six admission-free proofs from the established APIs). BesselRepresentations.airyAi_eq_besselK_complex, airyBi_eq_besselI_complex, airyAi_neg_eq_besselJ_complex and airyBi_neg_eq_besselJ_complex, with their derivative siblings, give all displayed fractional-order identities. airyAi_poincare/airyAiDeriv_poincare/airyBi_poincare/airyBiDeriv_poincare and the four oscillatory_expansion targets give the full expansions; airyAi_real_error and airyAiDeriv_real_error give the first-omitted-term bounds and signs.

## O-11.02 — real Airy envelopes (§2, pp. 394–397).

New DLMF.AsymptoticApproximations.Real.AiryEnvelope reuses canonical airyEnvCrit and defines actual weight E, modulus M, derivativeModulus N, normalized phase/derivativePhase and the three supremum constants errorConstant/aiErrorConstant/biErrorConstant. Defining APIs and weight branch simplifications are proved. transition_properties, weight_properties, modulus_properties, phase_representations, phase_properties and modulus_envelope acquire the crossing, continuity, positivity, monotonicity, four sine/cosine identities and bridge to existing envelopeAi/envelopeBi. modulus_isEquivalent and derivativeModulus_isEquivalent give both real infinities; weight_isEquivalent gives the exact positive-infinity exponential. errorConstant_bounds separately asserts bounded defining ranges, positivity and all three supremum inequalities. No numerical approximations are introduced.

## O-11.03 — turning-point regularity (Lemma 3.1, p. 399).

New ODE.RealTurningPoint.ratio/coordinate/scale/amplitude/perturbation are actual removable weighted-integral definitions with proved defining APIs. values_at_turningPoint, regularity, coordinate_integrals, inverse_properties, continuousOn_perturbation, perturbation_eq_away and transformed_equation acquire all source normalization, C2/C3 extension, positivity, inverse smoothness, retained continuous psi and exact transformation assertions. Complex local analytic coordinates are in TurningPointCoordinates as well.

## O-11.04 — real Airy approximation (Theorem 3.1, pp. 399–400).

New DLMF.AsymptoticApproximations.Real.airyPerturbationControl is the actual weighted control primitive, with proved defining/base APIs. exists_airy_perturbation_interval states the full canonical W-equation theorem with EReal endpoints, continuous complex-valued psi and integrable norm(psi)/sqrt(abs(zeta)). It asserts finite total control variation, both Ai/Bi-type exact solutions, normalized function/derivative limits at the prescribed finite or infinite ends, and all four exact E/M/N/Lambda variation bounds. The original w=h^(-1/4)W coordinate form follows by the existing Liouville CaseII transformation. Uniform bounded control variation gives the stated normalized O(1/u) consequence using exp(c/u)-1<=constant/u for u>=1.

## O-11.05 — real Airy zeros and monotone envelopes (Lemma 5.1, pp. 403–405).

All four *_infinite_real_zeros, *_spec and *_enumeration targets give the complete negative zero sequences. New real_zero_interlacing_below_transition and real_derivative_zero_interlacing_below_transition give both exact chains with c. On x<=c the weighted moduli coincide with canonical airyModulus/airyDerivModulus by AiryEnvelope.weight_of_le and their defining sums. airy_weighted_modulus_monotone gives strict increase of its positive reciprocal; airy_weighted_derivModulus_monotone gives N/abs(x)^(1/4); airy_modulus_deriv_monotone, airy_modulus_monotone and airy_modulus_product_monotone give the remaining three. airy_phase_monotone/airy_derivPhase_monotone and airy_phase_deriv_monotone/airy_derivPhase_deriv_monotone give the phases and absolute derivative monotonicities on their negative branches; deriv_airyPhase/deriv_airyDerivPhase give the exact derivatives. At c those derivative formulas refer to the left branch, not the totalized derivative of a phase flattened on the other side. airy_zero_common_asymptotic_coefficients has exactly cT1=5/48,cU1=-7/48 and the common all-order reversion/value families. airyZeroArgument1/3 with index n-1 is exactly t_n/s_n, so the four printed corrections follow by truncating that common expansion.

## O-11.06 — zeros of the perturbed equation (§6, pp. 405–408).

Real.airy_perturbation_zeros_and_displacement gives both one-half thresholds, both zero-free regions, uniqueness in every complete comparison bracket and the exact pi^2/3 displacement estimates with monotone source variation controls. Existing real Airy perturbation existence supplies the normalized solutions. New admission-free LipschitzOnWith.norm_sub_le_of_mul_sub_le transfers a bound for u^(2/3)*zeta-a_n through any L-Lipschitz inverse with the exact factor L/u^(2/3); applying it to sigma=O(1/u) gives O(u^-5/3). Its constants are unchanged for an external zero index, so the same argument gives all-index uniformity exactly when the inverse Lipschitz bound and total control variation are uniform. LipschitzOnWith.isBigO_sub_comp proves the corresponding filter formulation. New Bessel.Real.isBigO_besselJ_fixed_zero_turningPoint gives the displayed fixed-index consequence with all powers of two.

## O-11.07 — smooth weighted integration (Lemma 7.1, p. 410).

New MeasureTheory.weightedRayPrimitive is the actual Banach-valued integral integral0..1 t^alpha smul h(t smul x), for alpha>-1. Defining API is proved. intervalIntegrable_weightedRayPrimitive states absolute convergence; weightedRayPrimitive_zero gives h(0)/(alpha+1); contDiffOn_weightedRayPrimitive and iteratedDeriv_weightedRayPrimitive give every Cn derivative formula through zero. weightedRayPrimitive_differential_equation and contDiffOn_weightedRayPrimitive_succ give the extra derivative away zero for merely Cn data. analyticOnNhd_weightedRayPrimitive gives the complex analytic version on open star-shaped domains. Taking alpha=-1/2 gives exactly the source value2h(0), weights t^(k-1/2) and identity2xI'+I=2h.

## O-11.08 — higher Airy coefficients and real error (Theorem 7.1, pp. 409–412).

New ODE.IsTurningPointCoefficientSequence gives the differential A/B recurrences, the removable B(0) equation (proved), and its weighted-ray primitive identity. Real smooth and simply connected complex analytic coefficient-existence targets supply arbitrary A integration constants. turningPointPartialSum is the actual compound sum with proved defining API and an exact residual theorem. New Real.exists_airy_compound_expansion gives Ai/Bi-type solutions, four exact function/derivative variation bounds and opposite-endpoint normalizations. Real.exists_bounded_airy_coefficients_and_finite_variation supplies the differentiated-tail sufficient condition, bounded A, B decay and weighted B variation. These are acquired theorem targets, mostly admitted, rather than claims of completed proofs.

## O-11.09 — complex Airy solutions and zeros (§8, pp. 413–416).

airyAi_add_omega and airyBi_eq_airyAi_omega give both exact connections. airyAi_poincare/airyAiDeriv_poincare and the rotated expansion targets give the three recessive sectors on their stated branches. airyAi_complex_zeros_real/airyAiDeriv_complex_zeros_real give reality; airyBi_complex_zeros_sector/airyBiDeriv_complex_zeros_sector, their infinite_complex_zeros and complete enumeration targets give both nonreal families. airy_zero_common_asymptotic_coefficients uses the very same cT/cU for real and complex zeros. airyComplexZeroArgument is exactly airyZeroArgument+(3i/4)*log2, so its upper Bi argument is the printed 3pi(4n-1)/8+(3i/4)log2. exists_airy_zero_parametrizations gives the exact e^(pi*i/3)*T identity at that shifted argument; its T is a common zero parametrization, not an unsupported analytic-continuation assertion about an arbitrary interpolating function.

## O-11.10 — complex turning-point theorem (Theorem 9.1, pp. 417–418).

New Airy.ComplexEnvelope defines the actual three rotated solutions/derivatives, principal rotated weights, moduli and both supremum constants, with proved defining APIs and weight positivity. Its properties, sector inequalities, rotation/conjugation, Wronskian and constant-bound targets give the source envelope infrastructure. New exists_complex_airy_expansion_finite_reference and exists_complex_airy_expansion_endpoint_reference in ComplexAiryExpansion give analytic exact solutions, branch-normalized square-root progressive paths, full coefficient residual construction, both exact envelope and derivative bounds with the sector-dependent k, and endpoint normalizations. Paths avoid zero until the evaluation endpoint to exclude an artificial root-sheet change through the turning point.

## O-11.11 — coefficient bounds at infinity (Theorem 9.2, p. 419).

New ODE.exists_uniform_turningPoint_coefficient_bounds acquires all six parameter-uniform A/B bounds with the exact nonuniform boundary clearance, weighted paths, reference-value bounds and psi decay. exists_uniform_turningPoint_coefficient_variation_paths chooses modified paths and square-root lifts with uniformly finite variation of sqrt(z)*B_n. The unrestricted assertion for every weighted-length-bounded path is qualified in BookAcquisition-RevisionNotes: repeated shrinking loops near zero require path control or replacement. No confirmed book erratum is inferred from that qualification.

## O-11.12 — uniform large-order Bessel expansion (§10, pp. 419–426).

New Bessel.TurningPoint defines an actual weighted-integral actionRatio, coordinate, removable prefactor, amplitude and nonsingular perturbation using the inverse coordinate. coordinate_properties gives analyticity, inverse, exact two real action formulas, derivative/nonzero normalization and removable value at one. perturbation_coordinate_eq gives the displayed rational psi. airyComparison/cylinder/approximation are actual four-branch expressions. exists_uniform_cylinder_turningPoint_coefficients gives the common all-orders normalized A/B family, J/Y and separately recessive H1/H2 expansions plus uniform proper-sector function/derivative remainders; its majorants retain both Airy value and derivative at zeros. TurningPoint.exists_uniform_zero_coordinate_coefficients gives the all-index implicit J/Y zero expansions with first coefficient -B0, and the fixed-index first three J-zero terms are explicit. Derivative-zero inversion requires reciprocal-Airy-zero weights and is not mislabeled analytic at zero.

## O-11.13 — displaced Airy argument (§11, pp. 426–429).

New ODE.turningPointDisplacement is the actual half-weight primitive, with analytic/removable normalizing equation. coefficientDerivative and shiftedTurningPointResiduals are explicit PowerSeries expressions after substituting the shifted Airy argument and eliminating C''. exists_shiftedTurningPoint_formal_coefficients supplies analytic A/B arrays with arbitrary prescribed A integration constants, A0=1 and both residuals zero coefficientwise. The weighted primitive determines every B_s through zero; the second residual then integrates A_(s+1). No uniform remainder theorem is asserted beyond the source's formal construction.

## O-11.14 — forced Airy coefficients and Scorer functions (§12, pp. 429–432).

New ODE.IsForcedTurningPointCoefficientSequence gives exact analytic A/B/G differential and divisibility recurrences with A0=omega(0). A_succ_zero proves the recursively selected constants; exists_forcedTurningPointCoefficientSequence supplies analytic coefficients and G0=-dslope(omega,0). forcedTurningPointPartialSum is the actual Wi compound expression and forcedTurningPointPartialSum_residual gives the exact next-order residual. Existing scorerGi_exp_cos_integral, scorerHi_exp_integral, scorerGi_ode/scorerHi_ode, scorerGi_add_scorerHi, scorerHi_rotated_ode and the Scorer.ExpansionsAndZeros sector expansions cover the special-function statements with forcing signs -1/pi and +1/pi respectively. Scaling Wi=pi*Hi, or Wi=-pi*Gi, gives the normalized forcing1 used by the generic target.

## O-12.01 — real Bessel envelopes (§1, pp. 435–438; Lemma 4.1, pp. 443–444).

New DLMF.AsymptoticApproximations.Real.BesselEnvelope reuses canonical besselEnvCrit and defines actual E/M/unwrapped phase, with proved defining APIs and branch values. transition_properties gives the first positive crossing and its position before the first zeros; strictMonoOn_transition gives order monotonicity. continuousOn_weight_modulus, weight_properties, weight_le_succ and modulus_pos give joint continuity, positive weight bounds, argument antitonicity and order-step comparison. phase_representations, phase_properties and isBigO_phase_sub_linear give the exact normalized phase identities/derivative/asymptotic. modulus_envelope identifies M/E and ME with canonical envelopeJ/envelopeY. Existing Bessel zero-enumeration/interlacing APIs provide Xnu<y1<j1 after the crossing inequalities.

## O-12.02 — simple-pole transformation (§2, pp. 438–440).

New Complex.exists_analytic_simplePole_liouville_coordinate and amplitude/perturbation targets in TurningPointCoordinates give the analytic action coordinate and inverse, compatible amplitude and exact retained double-pole coefficient, allowing c=4 for the source normalization. Real.exists_analytic_simplePole_liouville_coordinate and exists_analytic_simplePole_liouville_data give the increasing real analytic coordinate/inverse, positive amplitude and analytic remaining perturbation. Existing liouville_caseIII supplies the algebra once the factor-four normalization is substituted.

## O-12.03 — Bessel coefficient recursion (§2, pp. 439–440).

New ODE.IsSimplePoleCoefficientSequence in SimplePoleCoefficients gives both exact differential recurrences, including zero. B_zero is proved; B_eq_weightedRayPrimitive is the source integral formula without a free B constant. exists_simplePoleCoefficientSequence_real/complex realize arbitrary prescribed A_n(0) with smooth/analytic coefficients. simplePolePartialSum is an actual finite compound sum with proved interface; simplePolePartialSum_residual gives its exact remainder in terms of B_n and B_n'. The canonical I/K or J/Y consecutive-order derivative identities instantiate the comparison pair and signs. No undefined coefficient family is assumed.

## O-12.04 — positive-variable error (Theorem 3.1, pp. 441–442).

New RealBesselExpansion defines the actual positive I/K comparison pairs and the exact supremum modifiedConstant. constants_properties gives finiteness/continuity and lambda1>=1. exists_positive_bessel_compound_expansion gives both exact compound solutions and all four source function/modified-derivative bounds, including EReal infinite endpoints under finite weighted B variations. The fixed truncation need not define the same solution at different orders; the separate all-orders theorem handles that issue.

## O-12.05 — negative-variable error (Theorem 4.1, pp. 444–445).

BesselComparison.negativePair gives the actual J/Y expressions with the negative consecutive-order sign. oscillatoryConstant and oscillatoryErrorConstant define lambda2/3/4; constants_properties gives finiteness/continuity. exists_negative_bessel_compound_expansion gives both exact solutions, the full explicit E/M exponential variation bounds, and derivative bounds by negativeDerivativeMajorant. ordinaryGreenKernel is the actual square-root J/Y kernel with Wronskian -1/pi; negativeErrorMajorant and negativeDerivativeMajorant are explicit known-integrand bounds with no unknown error under the integral. Infinite reference ends remain allowed under the stated finite variations.

## O-12.06 — uniformity and tails (§5, pp. 447–448).

New ODE.exists_jointly_continuous_simplePole_coefficients gives joint order/variable continuity for every variable derivative under canonical zero A constants. simplePoleDerivativeCoefficient/Companion are actual derivative-series arrays with proved APIs; exists_simplePole_coefficient_tail_limits gives all coefficient limits and finite weighted variation from the differentiated tail condition at either real infinity. New Real.exists_allOrders_real_bessel_comparison chooses one exact solution before every truncation and gives all four compound expansions uniformly on compact order intervals under uniform variations. exists_uniform_nonnegative_order_bessel_comparison gives the separate leading positive-variable result for all nonnegative orders under the source weighted L1 hypothesis. No unbounded-order oscillatory estimate is claimed.

## O-12.07 — radial scattering error (Theorem 6.1, pp. 449–451).

New Real.radialScatteringControl, totalRadialScatteringControl and bornPhaseShift are actual weighted integrals with proved APIs. IsRadialScatteringSolution specifies origin continuity, the radial ODE and the exact recessive ratio limit. exists_radialScatteringSolution gives the source exponential M/E error. exists_radialScattering_phase gives nonzero amplitude, principal phase, both infinity sinusoidal limits and the explicit linear phase bound under exp(G)-1<=1. isBigO_radialScattering_phase_sub_born gives the quadratic-in-total-control Born error. The sharper intermediate arcsin inequality can be derived from the same complex-amplitude geometry; the synopsis itself displays only the acquired linear bound.

## O-12.08 — perturbed Bessel zeros (§7, pp. 451–453).

New Real.exists_simplePole_solutions_with_uniform_zero_bounds gives both exact real comparison solutions, the first J zero-free region, unique zeros in every complete J/Y bracket and all-index argument error C/u. Its coordinate error explicitly retains C*(j/u^3+u^-4), including the analogous Y bound and the first Y bracket with endpoint0. isBigO_whittakerM_fixed_positive_zero gives the fixed-index Whittaker application with the exact preceding-zero count; it does not falsely assert infinitely many positive Whittaker zeros for every fixed kappa.

## O-12.09 — complex Bessel weights (§8, pp. 453–457).

New BesselComplexEnvelope.comparisonRegion/weightSquared/weight/modulus are actual strip-disc suprema and weighted Bessel norms, with proved defining APIs. weight_properties, modulus_properties, exists_uniform_sector_weight_equivalent and exists_uniform_halfPlane_modulus_bounds acquire finite suprema, correct zero-weight limit, continuity on the appropriate domains, the explicit exponential upper bound, proper-sector equivalent and both closed-half-plane growth directions uniformly in bounded order. The order-zero modulus is unbounded at0, so no finite continuous modulus extension there is asserted. Exact all-integer monodromy with removable parameter limits is in Bessel.LogarithmicMonodromy.

## O-12.10 — complex simple-pole theorem (Theorem 9.1, pp. 458–460).

ComplexBesselComparison defines the actual lifted I/K comparison and companion, Green kernel, finite partialSum and adaptive envelope. comparison_and_partialSum_equations gives the exact Wronskian -exp(w)/2 and finite residual in w=log(zeta). exists_complex_simplePole_I_expansion constructs the origin-normalized lifted solution; exists_complex_simplePole_K_expansion gives finite-reference exact matching and exact Green/differentiated-Green integrals. Both have the complete adaptive variation function bound and the explicit derivativeMajorant, whose integrand contains no unknown error. exists_complex_simplePole_K_endpoint_expansion gives a prescribed recessive infinite reference and all later paths retaining its tail germ. IsSimplePoleCoefficientSequence supplies the analytic removable coefficients; solutions remain on the punctured logarithmic cover, with no false analyticity-through-zero claim.

## O-12.11 — relaxed progressive paths (§10, pp. 460–462).

New BesselComplexEnvelope.radiusWeightRatio/kernelConstant are actual suprema describing the fixed radius-ratio cost. radiusWeightRatio_properties gives finite local bounds, original ratio1 and divergence as the allowed ratio tends to infinity. Both complex simple-pole existence targets allow the relaxed ordered radius condition while retaining the real-action monotonicity. Their I/K OnLog comparisons and canonical exact monodromy encode sheet continuation; the K solution retains its chosen reference value on the cover, so changing reference sheets is not asserted to preserve that solution.

## O-12.12 — coefficients at infinity (Theorem 11.1, pp. 462–463).

New ODE.exists_uniform_simplePole_coefficient_bounds gives all six parameter-uniform bounds with square-root boundary clearance, the inner disc and weighted paths, and rho1=min(rho,1/2). The order is allowed to vary over a bounded interval. The source p463 has B_s'' decay exponent2+rho1; this exact stronger source exponent is acquired, while the weaker synopsis exponent1+rho1 is left unchanged.

## O-12.13 — Legendre functions of large degree (§§12–13, pp. 463–474).

New Legendre.SimplePole.perturbation has the actual meromorphic expression and exact removable value -(m^2-1/4)/12. IsCoefficientSequence fixes all integration constants by A_(s+1)(0)=2m B_s(0), and exists_coefficientSequence gives analytic coefficients on each simply connected domain avoiding the nonzero pi*i action poles. approximationP/Q are actual source sums. exists_exterior_expansion_errors gives exact P^{-m} and cleared Q^m identities, Q's finite-truncation multiplier and all function/derivative variation bounds; P uses the signed-order -m arrays with I_m,I_(m-1), and its own B^{-m} variations. exists_ferrersP_expansion_error gives the full J compound formula/error. exists_uniform_coefficient_variation_bound gives uniform bounded signed orders and separation from the next pole. principal_cosh_normal_equation gives the complex normal action ODE; analytic continuation along nonsingular paths and the generic complex simple-pole targets provide the continuation framework. Existing ferrersQ_large_degree_uniform supplies the source's leading Ferrers Q statement (the book p468 itself gives leading Q here). Signed-array normalization is qualified in RevisionNotes; zero constants apply to the unrearranged positive-order P array, not directly to A^{-m}.

## O-12.14 — Heine and Neumann expansions (Exercises 13.1–13.2, p. 473).

Existing legendre_heine_series/legendre_heine_uniform are proved for z1-1 in slitPlane. New legendre_heine_uniform_full_exterior extends the uniform result to the full integer-Q branch outside the focal segment, including the negative real exterior. New ellipsePath is the positively oriented affine Joukowski path, and analyticLegendreCoefficient is the exact (n+1/2) interval integral, both with proved interfaces. analyticLegendreCoefficient_eq_contour gives the source contour coefficient, and tendstoUniformlyOn_analyticLegendre_expansion gives the complete analytic Neumann series uniformly on every smaller closed ellipse, including the focal segment.

## O-12.15 — separated canonical equations (Theorem 14.1, pp. 475–476).

New Complex.exists_monomial_of_separated_scaling in SeparatedScaling gives the full meromorphic potential classification for an open parameter family and nonconstant analytic nonzero scale, retaining the normalization alpha of P''/P. Its conclusion is f=a*z^m,h=b*z^m+c/z^2, m!=-2 and alpha*omega^(m+2)=a*u^2+b. monomial_scaled_solution gives the converse exact differential substitution with no quotient at zeros of P. Rescaling the fixed canonical argument absorbs nonzero alpha and yields the source scale branch. The exceptional Euler class is explicitly covered by euler_equation_exp_log/cpow, their repeated-root log variants and complete-basis theorems in EulerEquation; it is not forced into the monomial-scaling classification.

## O-12.16 — other transition orders (§14, pp. 476–479).

New Complex.exists_analytic_power_liouville_coordinate acquires analytic coordinates, removable ratios and inverses for m>=-1. exists_analytic_power_liouville_coordinate_of_zero_residue gives higher poles with the necessary resonant square-root residue exclusion; the synopsis's unrestricted even-higher-pole claim is false (m=-4,F=1+z) and excluded with source evidence in RevisionNotes. compound_comparison_residual is the exact P*A+P'*B differential identity. New ODE.IsPowerTransitionCoefficientSequence gives both explicit formal coefficient recurrences; exists_higherPole_powerTransition_coefficients and exists_higherZero_powerTransition_coefficients realize the two permitted source families with their analytic divisibility. power_liouville_simplePole_residual gives the exact reduction of the higher-zero family to CaseIII; higher poles satisfy the acquired elementary LG pole criteria. The source's informal generic/nonatypical terminology is represented by these explicit permitted families and coefficient constraints, not by inventing an unquantified universal classification of all second-order equations.

## O-13.01 — monodromy and circuit exponents (§2, pp. 480–482).

New DLMFMathlib.Analysis.ODE.CircuitMonodromy uses the actual logarithmic universal cover and pulled-back equation, constructs a normalized fundamental pair, its integer-circuit GL representation, basis conjugacy, and the Cayley–Hamilton second-circuit identity for every solution. Its regular-singular diagonalization and resonant triangularization retain both counted indicial roots. Matrix.JordanTwo states the explicit invertible order-two Jordan alternatives for arbitrary algebraically closed fields, applicable also at irregular singularities. Mathlib Complex.exp_ne_zero, Complex.exp_log and Complex.exp_eq_exp_iff_exists_int supply the nonzero eigenvalue logarithms and their integer ambiguity; no relation to a sectorial formal exponent is imposed. Generalized eigenspace and nilpotent Jordan-chain prerequisites were found in Mathlib and TauCeti, but not this explicit circuit API. Most new analytic targets remain admitted.

## O-13.02 — simple-pole monodromy (§4, pp. 483–486).

New AsymptoticApproximations.Connections.SimplePole defines the actual Bessel-normalized Frobenius coefficients, logarithmic-cover recessive solution, I/K comparisons, relative errors, and the coefficient from the actual circuit matrix. recessive_add_circuit is fully proved directly from exponential periodicity. The lifted ODE, dominant circuit, and exact two-bank Y-zero error quotient are acquired, with independent-solution and nonzero-denominator hypotheses. norm_monodromyCoefficient_div_pi_mul_I_sub_one_le explicitly retains numerator and denominator errors; its general normed-field quotient estimate is proved in RelativeErrorQuotient. The adaptive-envelope error/variation targets are ComplexBesselExpansion.exists_complex_simplePole_I_expansion and exists_complex_simplePole_K_expansion, with a genuinely infinity-selected K solution in ComplexBesselEndpoint. Thus small error supplies denominator nonvanishing rather than silently cancelling it.

## O-13.03 — parameterized pole connections and Legendre example (§§5–6, pp. 487–491).

New ODE.SimplePoleScaling gives the exact residual under zeta=u²*x, the actual scaled perturbation psi(zeta/u²)/u², and a local inverse-coordinate parameterization of the intrinsic cut with tangent -1/(4*u²*F(z0)). Connections.SimplePoleParameter gives the actual dilated Frobenius solution and its exact u/residue-logarithm normalization multiplier. ComplexBesselEndpoint constructs the progressive-infinity-selected K solution with vanishing relative value/derivative errors and explicit kernel/variation bounds; together with the two-bank quotient in SimplePole this yields the pi*i*(1+O(u^-1)) coefficient when the computed variations are bounded. The Legendre normalization comparison is explicit in Legendre.SimplePoleExpansion (canonical signed-order coefficient arrays and Gamma normalizers); its exact continuation is already Continuation.Monodromy/ContinuityAndConnections. The source’s finite normalizer and branch choices are retained. These targets are predominantly admitted, not proofs inferred from normal-form substitution alone.

## O-13.04 — real Gans–Jeffreys connection (§7, pp. 491–494).

New Connections.GansJeffreys constructs the same right-recessive solution with amplitude-two left oscillation and a separately normalized left cosine solution with the corresponding right growing coefficient. All are actual classical solutions of the canonical real Airy-coordinate equation; its control is the integral of abs(psi)/sqrt(abs(x)). The statement includes a computable envelope constant, exponential variation bound, and the large-u O(u^-1) specialization. TurningPointCoordinates.transformed_equation transfers back to the source f,g on an interval with divergent endpoint actions. Complex.exists_amplitude_phase_error supplies the sharp amplitude/arcsine phase extraction. No cosine solution is selected by a growing asymptotic alone.

## O-13.05 — two-turning-point quantization (§8, pp. 494–497).

New ODE.TwoTurningPoints defines the actual signed potential, both endpoint actions, positive barrier action, and computed half-line Airy controls. IsProblem contains coefficient regularity, positivity, action divergence and integrability hypotheses, not desired connection outcomes. exists_recessive_pair supplies both canonically normalized endpoint solutions and the exact Wronskian matching criterion. IsTwoEndRecessive is small relative to the growing comparison at each end, so it does not incorrectly require pointwise decay for arbitrary admissible tails. exists_quantization_bound gives the fixed-potential half-integer action law with O(1/n) error for the actual two-end boundary problem; no first global eigenvalue is assigned to n.

## O-13.06 — confining bound states (§9, pp. 497–501).

New ODE.ConfiningQuantization retains all four differentiated power-tail conditions at each infinity. It acquires the two unique large-energy turning roots, their asymptotic locations, actual two-end vanishing bound states and their L2 characterization, an unbounded simple large-parameter enumeration, and computed integrable Airy controls with O(1/u) total size. exists_action_quantization_bound follows printed p.500’s additive O(1/u), which cannot be silently replaced by the synopsis O(1/n) for a varying potential. That stronger rate is deferred in BookAcquisition-RevisionNotes.md; the source-correct targets are otherwise acquired.

## O-13.07 — barrier scattering (§10, pp. 501–503).

New ODE.TwoTurningPoints.IsScatteringState specifies actual classical solutions, unit outgoing amplitude, and both value and Liouville-normalized derivative limits. exists_scattering_family constructs those states and the transmitted exp(-2*u*L) probability with relative O(1/u), plus the reflected probability. flux_identity gives the exact real-potential relation abs(A)^2-abs(B)^2=1 and T+R=1; the exponentially accurate R=1-T follows from that identity and the transmission estimate, rather than subtracting independent algebraic errors. The geometric hypotheses are actual actions and control variations. These are admitted theorem targets.

## O-13.08 — principal curves and canonical solutions (§11, pp. 503–506).

New `Complex.SimpleTurningPoint.principalRay` and `Complex.SimpleTurningPoint.exists_three_principal_arcs` give the actual local analytic inverse coordinate and all three outgoing quadratic-differential arcs, whose tangent directions differ by 2*pi/3. `Complex.SimpleTurningPoint.principal_trajectories_no_crossing` gives global absence of self-crossings, equality of intersecting maximal trajectories and the lack of regular interior endpoints. `Complex.SimpleTurningPoint.exists_three_principal_branch_domains` constructs the actual three maximal cuts, simply connected branch domains, adjacent principal components, canonical root/phase/control primitives and cyclic amplitude normalization from analytic f with one simple zero. It allows extra principal components elsewhere, as p504 states. New `Complex.ThreeReferenceLiouvilleGreen.Data` supplies only actual branch/reference/progressive-path geometry, with normalized multipliers and common prescribed tails. `Complex.ThreeReferenceLiouvilleGreen.Data.exists_canonical_network` derives actual global analytic endpoint-selected solutions, full accessible-point bounds, pairwise endpoint limits, their symmetry and the sharp half-exponential variation bound. The endpoint errors are conclusions, not structure fields.

## O-13.09 — fundamental three-solution connection (§11, pp. 505–506).

New `Complex.ThreeReferenceLiouvilleGreen.Data.exists_canonical_network` gives the exact cyclic connection with coefficients (1+delta23), exp(-2*pi*i/3)*(1+delta31), exp(2*pi*i/3)*(1+delta12). `Complex.ThreeReferenceLiouvilleGreen.Data.relativeError` and `Complex.ThreeReferenceLiouvilleGreen.Data.IsCanonicalFamily` are actual solution/normalization predicates with proved defining APIs; `Complex.ThreeReferenceLiouvilleGreen.Data.IsCanonicalFamily.connection_limits` derives the same identity and delta limits for any such actual family. New `Complex.ThreeReferenceLiouvilleGreen.Data.normalized_coefficient_endpoint_symmetry` gives the actual limits of the original-variable higher coefficient recursion, normalized to vanish at each reference. `Complex.ThreeReferenceLiouvilleGreen.Data.exists_positive_parameter_connection_expansions` gives fixed-geometry uniform O(1/u) connection errors and all higher endpoint coefficient expansions, with pair symmetry and actual control variations divided by u. The elementary algebraic basis `ODE.wronskian_cyclic_sum` is fully proved for arbitrary normed-commutative-ring-valued functions; the analytic normalization and endpoint identification remain admitted targets.

## O-13.10 — vanishing endpoint errors (Theorem 13.1, pp. 508–510).

New `Complex.PowerSectorLiouvilleGreen.Data` retains analytic complex-power equivalents on an actual annular sector, the canonical root/phase/control and the source positive exponents. `Complex.PowerSectorLiouvilleGreen.Data.control_deriv_isBigO` derives the differentiated control decay z^(-1-min(alpha,beta)) on every closed interior subsector. `Complex.PowerSectorLiouvilleGreen.AdjacentRayDirections` is the explicit unwrapped principal-domain inequality, whose boundaries are alpha*theta+arg(k)/2=pi/2+n*pi. `Complex.PowerSectorLiouvilleGreen.Data.exists_escaping_progressive_joins` constructs actual eventually progressive straight tails and joins escaping every compact set, with total control variation tending to zero. `Complex.PowerSectorLiouvilleGreen.Data.tendsto_error_adjacent_zero` concludes exact vanishing of the actual canonical relative error and normalized derivative at the adjacent reference. Its hypotheses are the actual ODE, coefficient branch and first-end normalization; neither a zero delta nor the desired endpoint bound is assumed. The Airy special case follows by f=z, g=0 and its exact rotated Airy normalization.

## O-13.11 — complex proof of real connections (§14, pp. 510–513).

New `Complex.ThreeReferenceLiouvilleGreen.IsRealGeometry` records the actual Schwarz-symmetric coefficient domain, conjugate reference paths and the positive/negative real-axis canonical branch normalizations. `Complex.ThreeReferenceLiouvilleGreen.real_connection_of_canonical_family` takes only the actual canonical ODE family and the source stated cross-reference/negative-infinity vanishing conditions; it derives the real amplitude-two identity, actual endpoint constant with its sharp variation bound, the negative-infinity connection asymptotic, and separate constant/local amplitude-phase bounds. `Complex.ThreeReferenceLiouvilleGreen.cosine_connection_of_canonical_family` fixes the source real cosine solution as Re(exp(-pi*i/6)*W2), with its exact growing-side error, negative-side phase and endpoint asymptotic. The amplitude/phase inequality itself reuses `Complex.exists_amplitude_phase_error`, including abs(p)<=abs(epsilon) and abs(q)<=arcsin(abs(epsilon))<=pi*abs(epsilon)/2. Source vanishing/path hypotheses are retained; Schwarz symmetry is not used to invent a zero connection correction.

## O-13.12 — exact scattering coefficients and Weber tests (§15, pp. 513–516).

New `Complex.ThreeReferenceScattering.scattering_probabilities_of_canonical_family` derives the actual unit-transmitted `ODE.TwoTurningPoints.IsScatteringState` from the canonical network, actual coefficient comparison waves, global classical ODE, and the source required cross-reference and real-infinity vanishing errors. `Complex.ThreeReferenceScattering.rightRelativeError` is the actual upper-cut transmitted-wave relative error with the common scale and unit phase retained. The theorem derives delta2/delta3 as actual endpoint limits, their strict variation bounds, the nonzero incoming denominator, both exact quotients T=exp(-2*u*L)/abs(1+delta3)^2 and R=abs(1+delta2)^2/abs(1+delta3)^2, and exact flux R+T=1. No probability or connection coefficient is assumed as input. The two exact tests reuse root `DLMF.Confluent.WeberScattering.transmission_and_reflection`, `DLMF.Confluent.WeberScattering.outgoingRight_flux`, `DLMF.Confluent.WeberScattering.outgoingRight_eq_incoming_add_reflected`, and `DLMF.Confluent.WeberScattering.isBoundState_iff_odd_square`: their waves and Wronskian coefficients are actual cylinder functions, not definitions equal to the desired logistic formulas. Progressive geometry remains the actual Data joins and the supplied vanishing errors; O-13.10 supplies sufficient exact-vanishing conditions.

## O-14.01 — limits of asymptotic information (§§1–2, pp. 519–522).

New DLMFMathlib.Analysis.Asymptotics.ExactRemainders defines the actual omitted-term quotient convergingFactor and proves its exact remainder identity under nonvanishing. IsLeastTermIndex is separately a minimum-size predicate on terms. flatExample takes any prescribed finite-point value while its flatExample_self and isLittleO_flatExample are fully proved. exists_analytic_expansion_error_gt_of_decreasing_terms is an explicit analytic counterexample with a full geometric inverse-power expansion, strictly decreasing positive terms and arbitrarily large next-term-relative finite error. No optimum-remainder claim is inferred from the least term.

## O-14.02 — exponential-integral exact remainder (§3, pp. 523–526).

New DLMF.ExpIntegrals.ConvergingFactors defines the canonical exp(z)*expIntegralE(1,z) remainder quotient and states the coherent full-slit rotated integral and exact first-order differential equation. Its actual polynomial coefficient sequence uses the finite derivativeResolvent inverse of c-D, with both printed initial polynomials and uniqueness. exists_uniform_growing_index_remainder_le is the full bounded-complex-zeta/proper-sector n-growing error, not a fixed-index expansion. The generic polynomial resolvent extends Mathlib sumIDeriv from the unweighted c=1 case.

## O-14.03 — the negative cut and the Ei multiplier (§4, pp. 527–530).

New DLMF.ExpIntegrals.EiConvergingFactors retains the exact upper-bank i*pi*exp(-x) term, defines the real Ei quotient, states the ordinary principal-value integral and exact differential/adjacent-index equations. It reuses Gamma.Real.gammaSaddleInverse for the signed Gaussian coordinate, defines the pole-subtracted analytic amplitude and actual formal-exponential reciprocal-Stirling normalization. The finite even-Gaussian convolution is the effective all-order coefficient algorithm. coefficient_zero is zeta-1/3; polynomiality and the full uniform growing-index error are explicit targets. The odd pole is removed before its whole-line Gaussian integral.

## O-14.04 — confluent converging factor (§5, pp. 531–536).

New DLMF.Confluent.ConvergingFactors defines the U(a,a+b+1,z) omitted-term quotient, its exact beta-Taylor integral and source second-order differential equation. The actual coefficient algorithm inverts (1-D)(1+q-D) and recursively includes both n^(-1) and n^(-2) perturbing polynomial operators, so every coefficient is a specified polynomial. The two printed initial values and full complex-zeta/sector uniform growing-index estimate are separate targets. a>0 and b outside the nonnegative integers are retained; no converging factor is inferred by dividing a terminating zero term.

## O-14.05 — Euler transformation (Theorem 6.1, pp. 537–539).

Existing EulerTransformation gives the finite transform, composition/inverse, forward differences and common exterior germ. New DLMFMathlib.Analysis.Asymptotics.EulerConditional supplies equality whenever both natural-order translated inverse-power series converge, with its HasSum corollary, and the full ordinary Banach-valued alternating Euler transformation. Its Abel-parameter formula retains the coherent rational substitution r/(2-r) before taking the boundary limit. Existing holomorphic identity-theorem APIs give continuation from the common exterior germ on a connected continuation domain.

## O-14.06 — Euler transformation of asymptotic series (Theorem 7.1, p. 540).

New Asymptotics.HasAsymptoticExpansion.eulerCoefficientTransform gives the full transformed expansion on any filter with norm(z) tending to infinity, retaining every truncation order and imposing no convergence of the coefficient series.

## O-14.07 — certified transformed remainder (§7, pp. 541–543).

New DLMF.ExpIntegrals.EulerRemainders defines the actual first transformed terms/residual, exact finite factorial/Gamma sum and finite denominator expansion. firstError_sign_and_abs_le gives the even-index sign and factor-two bound. The second transformation is explicitly the t=3 denominator expansion; firstError_eq_sum_secondTerm_add_error and secondError_sign_and_abs_le give the exact iterated residual and factor-four bound for two independently even truncation indices. The signs are asserted for the integral remainders, not guessed from term decrease.

## O-14.08 — Aitken acceleration (Exercise 7.3, p. 543).

New Asymptotics.aitkenTransform with proved defining quotient, HasAsymptoticExpansion.aitkenTransform and aitkenTransform_of_eq_zero state the two exact fixed-index error orders n+3 and n+2. Both theorems assert eventual nonvanishing of the denominator; they do not assert convergence as the truncation index varies.