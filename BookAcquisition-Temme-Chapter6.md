# Temme Chapter 6 acquisition audit

This companion audit covers every group TEM-06-01 through TEM-06-16 of
[SYNOPSIS-Temme.md](SYNOPSIS-Temme.md). The source is Temme, *Special Functions*,
Chapter 6, pp. 133–164. The synopsis is unchanged. Search order is pinned Mathlib,
pinned TauCeti, then DLMF. Existing admissions and new admissions are acquisition
coverage, never evidence of a completed proof.

All unqualified local names below belong to `DLMF.OrthogonalPolynomials`.
The auxiliary definitions retain the unnormalized polynomial convention; setting
`squaredNorm μ p n = 1` gives the book's orthonormal formulas.

## TEM-06-01: existence, uniqueness, finite expansion and moment vanishing

- New admitted `existsUnique_orthonormal_polynomials` in `MeasureConstruction.lean`
  requires integrability of every monomial and positive mass outside every finite
  set. Its conclusion is uniqueness of the whole sequence, with orthogonality,
  unit squared norms and positive leading coefficients. It includes measures
  without densities, as required by the synopsis.
- Existing `IsOrthogonalPolynomials.expansion` in `Basic/General.lean` gives the
  exact finite polynomial expansion. `IsOrthogonalPolynomials.integral_mul` gives
  its coefficients as integrals divided by squared norms. Under unit norms these
  are precisely the inner products in the source.
- Existing `IsOrthogonalPolynomials.integral_mul_eq_zero_of_degree_lt`, applied to
  `Polynomial.X ^ j`, gives every stated vanishing monomial moment.

## TEM-06-02: recurrence coefficients and Favard

- Existing `three_term_recurrence` in `Basic/General.lean` gives the three-term
  structure; `recurrenceDiagonal_eq_integral` in `Basic/NormsAndKernels.lean`
  identifies the diagonal coefficient.
- New admitted `orthonormal_polynomials_recurrence` in `MeasureConstruction.lean`
  gives both the initial step and the subsequent recurrences with all leading
  coefficient ratios and the integral diagonal coefficient explicit. Positivity
  of the leading coefficients makes both outer recurrence coefficients positive;
  the previous-polynomial coefficient is exactly `a_n/a_(n-1)`.
- The converse is existing admitted `favard` in `General.lean`. Its conclusion is
  a positive measure, with no unwarranted assertion that the measure has a density.
- The more general nonmonic, non-unit-norm formula is newly admitted
  `three_term_recurrence_explicit` in `GeneralRecurrenceCoefficients.lean`
  (shared Duverney acquisition).

## TEM-06-03: Christoffel–Darboux and reproduction

- Existing `christoffel_darboux` in `Basic/General.lean` is the off-diagonal formula,
  with squared norms retained.
- Existing `christoffel_darboux_diagonal` in `Basic/NormsAndKernels.lean` is the
  derivative diagonal formula, and `kernel_reproduces` in that file gives exact
  reproduction on the space of polynomials of the specified degree.
- `christoffelDarbouxKernel` is the canonical norm-divided finite sum. Unit norms
  give the source kernel directly, without a new definition.

## TEM-06-04: all roots, support location and strict interlacing

- Existing `orthogonal_polynomials_roots` in `General.lean` states that the real
  root multiset has cardinality `n` and is duplicate-free. Its `natDegree = n`
  hypothesis is already part of `IsOrthogonalPolynomials`.
- Existing `zeros_interlace` in `GeneralIdentities.lean` gives increasing arrays
  of all roots of both adjacent degrees and both strict interlacing inequalities.
- New admitted `eval_eq_zero_mem_interior_convexHull_support` in
  `MeasureConstruction.lean` places every root in the interior of the convex hull
  of the actual measure support. The existence of the whole orthogonal sequence
  excludes finite-support degeneracy. The positive-density interval case follows
  by identifying this convex hull.

## TEM-06-05: Gaussian weights, exactness and exact remainder

- Canonical `gaussWeight μ x i` in `QuadratureAndKernels.lean` is the integral of
  `Lagrange.basis`. No division at a root is used to define the Lagrange polynomial.
- Existing `gauss_quadrature` in `General.lean` gives positive exact weights.
  New admitted `integral_eq_sum_gaussWeight` in `QuadratureError.lean` specifies
  that these are the canonical Lagrange-integral weights for every polynomial
  of degree less than `2n`.
- New admitted `gaussWeight_eq_integral_sq` in `QuadratureAndKernels.lean` gives
  the squared-Lagrange expression and strict positivity. New admitted
  `gaussWeight_inv_eq_kernel` gives the inverse-kernel expression.
- New admitted `gaussWeight_eq_derivative_quotient` in `QuadratureError.lean`
  gives the consecutive-polynomial derivative quotient, with its squared norm
  retained. Under unit norms it is exactly the displayed source formula.
- New admitted `exists_gauss_quadrature_error_eq_iteratedDeriv` in that file gives
  a point strictly between the endpoints and the exact derivative remainder.
  The measure is supported on the compact interval and positive on every open
  subinterval; the source's positive weight satisfies these assumptions.

## TEM-06-06: Jacobi definitions, degree, values, equation, derivatives and norm

- Canonical `jacobiPolynomialP` in `Basic/Classical.lean` is the terminating
  hypergeometric expression, for the source's `α, β > -1`. The new polynomial
  continuation `jacobiExtended` in `Basic/PolynomialContinuation.lean` has a
  proved bridge `jacobiExtended_eq_jacobiPolynomialP` on this domain.
- Existing `jacobiPolyPR_natDegree` in `ClassicalInstances.lean` gives the exact
  polynomial degree. `jacobiPolynomialP_one` gives the value at one;
  `jacobi_reflection` in `Differential/ClassicalEquations.lean` gives parity with
  the two parameters interchanged.
- Existing `jacobi_rodrigues` in `Integrals/AngularRepresentations.lean` is the
  stated real-interval Rodrigues formula. Existing `jacobi_differential_equation`
  and `jacobi_derivative` in the differential modules are the equation and
  lowering derivative formula.
- Existing `jacobiPolynomialP_orthogonal` in `Classical.lean` gives orthogonality.
  Existing `jacobi_norm_all` in `Integrals/AngularRepresentations.lean` treats
  the zero degree separately by the beta value, so `α + β + 1 = 0` causes no
  artificial zero or singularity. Positive degrees give the displayed gamma norm.
- Shared newly admitted `JacobiContinuation.lean` extends the equation,
  Rodrigues and generating formulas to all continued complex parameters. These
  extensions are additional coverage, not needed to weaken the source domain.

## TEM-06-07: Jacobi recurrence and seeds

- Existing `jacobi_recurrence` in `Differential/ClassicalEquations.lean` gives the
  recurrence on the regular domain. New admitted `jacobiExtended_recurrence` in
  `PolynomialContinuation.lean` is the fully cleared recurrence for all complex
  parameters, including values at which division by a recurrence factor is invalid.
- Existing `jacobiPolynomialP_zero` and `jacobiPolynomialP_one_eq` give both seeds.
  The latter is in `Differential/ClassicalEquations.lean`. No degenerate degree-zero
  recurrence is used in place of the degree-one seed.

## TEM-06-08: Gegenbauer and Legendre

- Canonical `ultrasphericalPolynomial` and the proved
  `ultrasphericalPolynomial_eq_jacobiPolynomialP` are in `Basic/Classical.lean`.
- Existing `ultrasphericalPolynomial_generating_function` in
  `Series/ClassicalGenerating.lean` covers the whole `Re λ > -1/2` range.
  Existing differential equation and recurrence have the same full range.
- Shared new admitted `ultrasphericalPolynomial_norm_of_nonzero` in
  `GegenbauerNorm.lean` gives the full `λ > -1/2, λ ≠ 0` norm. The older
  `ultrasphericalPolynomial_norm` alone requires `λ > 0` and is only partial.
  Orthogonality in the remaining negative-λ range follows from the canonical
  Jacobi bridge and `jacobiPolynomialP_orthogonal` with `α = β = λ - 1/2`.
- Existing `legendre_eq_ultrasphericalPolynomial` identifies `λ = 1/2`;
  `legendrePolynomialP` is definitionally Jacobi with zero parameters.
  Existing `legendre_orthogonality` in `Integrals/AngularRepresentations.lean`
  gives both the Kronecker orthogonality and its exact `2/(2n+1)` norm.

## TEM-06-09: Chebyshev

- Use Mathlib's `Polynomial.Chebyshev.T` and `.U` directly. Its `T_real_cos` and
  `U_real_cos` give the trigonometric definitions, including the undivided sine
  identity, which remains valid at the endpoints.
- Mathlib `T_zero`, `T_one`, `U_zero`, `U_one`, `T_add_two` and `U_add_two` give
  all four seeds and both polynomial recurrences over a general commutative ring.
- Mathlib `integral_eval_T_real_mul_eval_T_real_measureT`,
  `integral_eval_T_real_mul_self_measureT_zero` and
  `integral_T_real_mul_self_measureT_of_ne_zero` give the first-kind weighted
  orthogonality and both norm cases. `Polynomial.Chebyshev.integral_measureT`
  identifies the measure as `dx/sqrt(1-x²)`.
- Existing DLMF `integral_eval_U_mul_of_ne` and `integral_eval_U_mul_self` in
  `General.lean` give the second-kind orthogonality and norm `π/2`.
- Mathlib `one_sub_X_sq_mul_derivative_derivative_T_eq_poly_in_T` and its `U`
  version give exactly both differential equations as polynomial identities.

## TEM-06-10: Laguerre

- Canonical `laguerrePolynomialL` is the source's terminating Kummer expression;
  `laguerrePolynomialL_eq_sum_coeff` and `laguerreExtended_eq` in
  `Basic/Classical.lean` give the finite continued polynomial.
- Existing `laguerrePolynomialL_rodrigues` in `Integrals/AngularRepresentations.lean`,
  `laguerrePolynomialL_differential_equation`, `laguerrePolynomialL_recurrence`
  and `laguerrePolynomialL_derivative` in the differential modules give every
  listed identity for `α > -1`.
- Existing `laguerrePolynomialL_orthogonal` and `laguerrePolynomialL_norm` give
  orthogonality and the gamma norm. Existing
  `hasSum_laguerreExtended_generating_function` in `Classical.lean`, followed by
  `laguerreExtended_eq`, gives the complete generating function for `|t| < 1`.

## TEM-06-11: Hermite

- Canonical physicists' `hermitePolynomialH` is in `Basic/Classical.lean`.
  Existing `deriv_gaussian_eq_hermitePolynomialH` supplies Rodrigues, and
  `hermite_finite_sum` in `Series/ClassicalGenerating.lean` is the exact finite sum.
- Existing `hasSum_hermitePolynomialH_generating_function` in `Classical.lean`
  gives the entire generating series. `hermitePolynomialH_derivative`,
  `hermitePolynomialH_recurrence` and `hermitePolynomialH_differential_equation`
  give the derivative, recurrence and differential equation.
- Existing `hermitePolynomialH_orthogonality` in
  `Integrals/AngularRepresentations.lean` includes the exact `sqrt π * 2^n * n!`
  norm. `hermitePolynomialH_zero` and `hermitePolynomialH_one` give the seeds;
  differentiating the constant seed gives its zero derivative separately.

## TEM-06-12: Legendre integrals and bounds

- New admitted `legendrePolynomialP_eq_integral_pow` in
  `LegendreIntegralRepresentations.lean` gives the full complex Laplace integral
  for either square root, with no restriction to real `z` or one selected branch.
- Existing `legendre_dirichlet_mehler` in `Integrals/AngularRepresentations.lean`
  is the first integral. New admitted
  `legendrePolynomialP_eq_complementary_mehler` gives the second integral.
- Existing `norm_legendrePolynomialP_le_one` in `Legendre.lean` gives the closed
  interval bound. `norm_legendrePolynomialP_cos_le` gives the sharper displayed
  bound with `x = cos θ`; substituting `θ = arccos x` and
  `sin(arccos x) = sqrt(1-x²)` yields the synopsis version. This last algebraic
  real-variable adapter has not been separately installed as a theorem.

## TEM-06-13: Stieltjes, convergence and Hilb

- Shared new admissions `legendrePolynomialP_stieltjes_uniform`,
  `hasSum_legendreStieltjesTerm`, and `legendrePolynomialP_hilb_uniform` in
  `LegendreSeries.lean` give, respectively, every finite asymptotic order on each
  compact interior angle interval, the convergent series under `2 sin θ > 1`,
  and the endpoint-uniform Hilb error. `Real.legendreHilbAmplitude` supplies the
  limiting factor one at zero.

## TEM-06-14: least squares, exact error and Bessel

- Shared new admitted `legendre_partialSum_unique_leastSquares` in
  `LegendreSeries.lean` gives the full complex `L²` minimization and equality
  exactly when the competitor polynomial equals the partial-sum polynomial.
- Shared new admissions `integral_norm_sub_sum_legendrePolynomialP_sq_of_memLp`
  and `summable_legendreCoeff_sq_of_memLp` give the exact error, summability and
  Bessel bound. These are not restricted to continuous functions.

## TEM-06-15: pointwise convergence and derivative coefficient formula

- Shared new admitted `tendsto_sum_legendreCoeff_of_one_sided_bound` in
  `LegendreSeries.lean` gives the half-sum of the supplied one-sided values under
  integrability and local first-order one-sided error bounds. The source's finite
  one-sided derivatives imply these bounds; continuity points use both values `f x`.
- Shared new admitted `legendreCoeff_eq_integral_derivative` gives the coefficient
  after repeated integration by parts, using a supplied continuous chain of
  within-interval derivatives. A `C^n` function supplies this chain.

## TEM-06-16: plane waves and Chebyshev expansions

- Shared new admitted `tendstoUniformlyOn_legendre_plane_wave` in
  `LegendreSeries.lean` uses the canonical entire spherical Bessel function, so
  negative `a` and `a = 0` retain the intended continuation.
- Existing canonical `chebyshevCoeff`, `chebyshevCoeff_eq_integral_measureT` and
  `fourierCoeff_chebyshevCircleFun` in `ChebyshevExpansion.lean` give the exact
  coefficient normalization and the Fourier bridge. Existing
  `hasSum_chebyshevCoeff_mul_T` covers continuous functions with absolutely
  summable coefficients.
- New admitted `tendsto_sum_chebyshevCoeff_of_boundedVariationOn` in
  `ChebyshevUniformSeries.lean` supplies the usual Dirichlet–Jordan pointwise
  Fourier criterion, including jumps and the half-sum of their one-sided values.
- New admitted `tendstoUniformlyOn_chebyshevT_recip_add` in that file strengthens
  the existing pointwise reciprocal expansion to the required full closed-interval
  uniform convergence for every real `a > 1`.

## Validation status

The newly added Chapter 6 modules are registered in the orthogonal-polynomial
umbrella. Direct strict Lean checks have passed for the new measure construction,
quadrature error, Legendre integral and Chebyshev uniform/convergence statements.
Full and targeted module builds are integrated with the shared acquisition build.
A strict local existing-declaration axiom audit at
`/tmp/AAR-Temme6-existing-audit.lean` checked 56 declarations: all were accepted,
with only `propext`, `Classical.choice` and `Quot.sound` among their axiom
dependencies, and no `sorryAx`. Thus the existing declarations listed there
are proved; newly acquired admissions remain explicitly distinguished above.
No source definition, tagged theorem statement or synopsis entry was changed.
