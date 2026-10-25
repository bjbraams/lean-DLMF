# Beals and Wong coverage inventory

Review and implementation date: 18 October 2026.

Beals and Wong still offers substantial material beyond the current union of
Mathlib, pinned TauCeti, and lean-DLMF. The largest missing developments are
orthogonal-polynomial approximation and moment theory, distributions of zeros,
Riemann–Hilbert asymptotics, Meijer G-functions, complex elliptic-function
theory beyond the existing foundations, and global Painlevé II theory.

## Scope and interpretation

The source is the second edition of *Special Functions and Orthogonal
Polynomials*, Cambridge Studies in Advanced Mathematics 153, in
[the supplied PDF](References/BealsWong2015SpecialFunctionsOrthogonalPolynomials2ndEd-CambridgeStudiesAM153.pdf).
Its copyright page says **first published 2016**, although the filename and
some project comments say 2015. Page references below are printed book pages;
add 14 to obtain the PDF viewer page number.

The comparison uses:

- Mathlib `5e0c4e5239cb0a2d86d68a884bf52cfd963fce22`.
- TauCeti `a780c7ad6beb23f60a17351a492d177878020ad5`.
- The current lean-DLMF working tree, including its modified and untracked Lean
  files. The underlying AAR commit is `53aca5cf2947648287e2a45e0d1740dd1db5572c`.

These are the initial inventory revisions. The later shared upgrade to Lean
`v4.36.0-rc1`, Mathlib `911003dd6dea`, and TauCeti `5cdecf40e99d` is recorded
in [REVIEW.md](REVIEW.md); the initial negative findings retain their original
revision basis. The dependency checkouts were clean at initial review time. This
is a chapter-by-chapter inventory of mathematical topics and theorem families,
including selected substantive exercise formulas, rather than a certification
of every exercise or every differently normalized formula.

Status words have the following meanings:

- **Absent:** no corresponding definition or theorem was located in the three
  source trees. General tools from which a result could be developed do not
  themselves count as the book's result.
- **Partial:** related theory exists, but a specified domain, parameter range,
  conclusion, or substantial part of the development is missing.
- **Admitted:** a corresponding local statement exists with `sorry`; this is
  already included as a statement, but is not established mathematics.
- **Present:** source declarations with proofs cover the indicated material.
  The implementation batch below was built and axiom-audited; the initial
  review did not repeat that audit for every pre-existing proof.

Negative findings come from both topic/name searches and examination of the
nearby APIs and statements. They mean “no matching result located at these
revisions,” not a claim about later upstream versions. Existing coverage
Markdown files contain historical counts and some superseded descriptions;
the current Lean sources take precedence here.

## Chapters 1 and 2 Orientation and gamma beta zeta

Most of the concrete function theory here is already represented. Mathlib has
Gamma, beta, reflection, duplication, Bohr–Mollerup, and zeta foundations;
[DLMF/Gamma](DLMF/Gamma.lean),
[DLMF/Selberg](DLMF/Selberg.lean), and the incomplete-gamma modules provide much
more. These chapters are not large new acquisition areas.

- **Absent — Wielandt's characterization of Gamma**, Theorem 2.4.1, pp. 24–25.
  The precise missing theorem identifies a holomorphic function on `Re z > 0`
  satisfying `G(z+1) = z G(z)`, `G(1) = 1`, and boundedness on
  `1 ≤ Re z ≤ 2`, with Gamma. Mathlib's
  [BohrMollerup.lean](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gamma/BohrMollerup.lean)
  covers the other characterization, Theorem 2.4.2. The project's Gamma
  bounds and complex-analysis tools are useful prerequisites for Wielandt.
- **Partial — characterization by simple coefficient recursion**, §1.3 and
  §12.2. The project proves that its hypergeometric functions solve their
  equations and has coefficient uniqueness results, but does not classify
  all differential operators whose power-series equations reduce to the
  book's two-term coefficient recursion. See the Chapter 12 entry.

## Chapter 3 Second order differential equations

The recent
[SturmComparison](DLMFMathlib/Analysis/ODE/SturmComparison.lean),
[SoninePolya](DLMFMathlib/Analysis/ODE/SoninePolya.lean), and
[Volterra](DLMFMathlib/Analysis/ODE/Volterra.lean) modules cover substantial parts
of §§3.3 and 3.5. Generic existence and uniqueness tools are already upstream.
The missing pieces concern the structure and classification of equations.

- **Absent — general gauge and Liouville transformations with weighted
  symmetry**, §3.1, Propositions 3.1.1–3.1.4, pp. 47–49. This includes the
  criterion `q w = (p w)'` for formal symmetry, existence and uniqueness up
  to scale of the symmetrizing weight, gauge changes to a chosen weight, and
  the unitary reduction to a Schrödinger equation. Individual transformations
  are proved inside several special-function modules; a general theorem
  with these conclusions is missing.
- **Partial — general second-order solution-space and Green-kernel API**,
  §§3.2–3.3, pp. 49–55. The book packages the two-dimensional homogeneous
  solution space, Wronskian independence, and the inhomogeneous Green
  integral for arbitrary continuous coefficients on an interval. The local
  weighted Wronskian and oscillator Volterra formulas cover useful special
  cases. A corresponding general scalar second-order interface was not
  located; the upstream Picard–Lindelöf foundations should be reused.
- **Absent — classification of symmetric polynomial eigenfunction systems**,
  §3.4, Theorem 3.4.1, pp. 55–60. The converse classification leading to
  Hermite, Laguerre, and Jacobi is missing. Having these families, their
  ODEs, and their orthogonality does not prove this classification.

The applications in §3.6 are partly covered by
[WaveEquation/Helmholtz.lean](DLMF/WaveEquation/Helmholtz.lean). Consequently,
separation of variables and the occurrence of Bessel/Legendre equations
should not be inventoried as wholly absent.

## Chapter 4 Orthogonal polynomials on an interval

[General.lean](DLMF/OrthogonalPolynomials/General.lean) and
[GeneralIdentities.lean](DLMF/OrthogonalPolynomials/GeneralIdentities.lean)
already provide the three-term recurrence, Gauss quadrature, real roots in
the support, interlacing, Christoffel–Darboux, positive Hankel determinants,
and compact-support expansion results. TauCeti supplies important
completeness and moment-determinacy ingredients.

- **Absent — Padé approximation to a Stieltjes transform**, §4.2,
  pp. 78–81. Missing are the general numerator polynomials, the
  orthogonal-polynomial denominator characterization, the order of matching
  at infinity, exact remainder identities, and the resulting approximation
  bounds and convergence results. Mathlib already defines the Cauchy/Stieltjes
  transform as a specialization of
  [resolventTransform](.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/ResolventTransform.lean)
  and proves off-support analyticity. That transform is not itself a gap.
- **Absent — the general Padé and Jacobi continued-fraction correspondence**,
  §4.3, pp. 81–84. The missing theorem connects the recurrence of an arbitrary
  orthogonal system to convergents of its Stieltjes transform. The five
  concrete finite identities in
  [ContinuedFractions.lean](DLMF/OrthogonalPolynomials/ContinuedFractions.lean)
  do not supply this analytic correspondence or convergence.
- **Admitted — Favard's existence theorem**, §4.5, Theorem 4.5.1,
  pp. 86–88. `favard` in `General.lean` already states existence of an
  orthogonality measure from a positive recurrence. It needs a proof, rather
  than another acquired statement.
- **Absent — Carleman's recurrence-coefficient uniqueness criterion**,
  Theorem 4.5.2, pp. 88–89: divergence of the book's `∑ 1/a_n` implies
  uniqueness of the orthonormalizing measure. Preserve the book's
  normalization when translating those coefficients. TauCeti already proves
  determinacy from exponential moments and on compact support in
  [Probability/Moments](.lake/packages/TauCeti/TauCeti/Probability/Moments/Determinacy.lean).
  Those results cover important cases but not this recurrence criterion.
- **Absent — the general Erdős–Turán zero-distribution theorem**, §4.6,
  Theorem 4.6.1, pp. 89–90. For a positive almost-everywhere weight on
  `(-1,1)`, the normalized zero-counting measures tend to the arcsine law.
  Root location and interlacing do not imply this conclusion by themselves.
- **Admitted — moment determinant formulas**, §4.1 and related formulas in
  §4.5. `monic_moment_determinant`, `monic_diagonal_moment_determinant`, and
  `monic_offdiagonal_moment_determinant` in `GeneralIdentities.lean` remain
  admitted. Positivity of the Hankel determinant is already proved.

The broader Hamburger moment problem discussed in §4.5 is a natural
extension, but should not be mistaken for a separate full theorem proved
in this book. The concrete book targets are Favard and the stated uniqueness
criterion.

## Chapter 5 Classical orthogonal polynomials

Definitions, classical ODEs, Rodrigues formulas, many generating functions,
orthogonality, completeness, and basic zero theorems have extensive coverage.
In particular,
[ClassicalInstances.lean](DLMF/OrthogonalPolynomials/ClassicalInstances.lean)
now proves completeness for Hermite, Laguerre, Jacobi, and Gegenbauer, so
the book's basic completeness theorem should not be counted as missing.

- **Present — indexed Hermite and Jacobi zero estimates**,
  Theorems 5.3.2 and 5.5.1, pp. 107 and 114.
  [HermiteZeroBounds.lean](DLMF/OrthogonalPolynomials/HermiteZeroBounds.lean)
  now proves both strict indexed bounds for the positive zeros of even
  and odd Hermite polynomials, including their complete enumeration.
  [JacobiZeroBounds.lean](DLMF/OrthogonalPolynomials/JacobiZeroBounds.lean)
  proves the indexed angle bounds when `α², β² ≤ 1/4`, and both strict
  inequalities when at least one squared parameter is less than `1/4`. Laguerre extremal zero bounds are proved in
  [BoundsZeros.lean](DLMF/OrthogonalPolynomials/BoundsZeros.lean).
- **Absent — the classical limiting zero distributions**, §5.7,
  Theorems 5.7.1–5.7.3, pp. 120–123. These are the Jacobi arcsine law,
  the rescaled Laguerre law with density
  `(2/π) √((1-x)/x)` on `(0,1)`, and the rescaled Hermite semicircle law
  with density `(2/π) √(1-x²)` on `(-1,1)`. No zero-counting-measure
  convergence theorem for these families was located.
- **Absent — Stieltjes electrostatic characterization of the zeros**,
  Theorems 5.7.5–5.7.7, pp. 123–124. Missing are existence and uniqueness
  of the maximizing weighted Vandermonde configuration for Jacobi,
  Laguerre, and Hermite weights, and identification with the polynomial
  zeros. The proved discriminant formulas in `BoundsZeros.lean` and
  [JacobiDiscriminant.lean](DLMF/OrthogonalPolynomials/JacobiDiscriminant.lean)
  are related but do not assert this optimization theorem. A header mention
  of electrostatics in `Selberg/Applications.lean` is not an implementation.
- **Absent — pointwise expansion theorems**, §5.8,
  Theorems 5.8.1, 5.8.4, 5.8.5, pp. 124–130. Missing is convergence of
  Hermite, Laguerre, and Jacobi orthogonal expansions to `f(x)` under the
  book's local bounded-difference-quotient condition and weighted `L²`
  assumptions. Existing completeness, Parseval, and `L²` convergence do
  not establish pointwise convergence.
- **Partial — the general functions of the second kind**, §5.9,
  Theorems 5.9.1–5.9.2, pp. 130–133. The missing development constructs
  Cauchy transforms of the classical weighted polynomials and identifies
  the transformed differential equation and solutions uniformly across
  the three families. The degree-integer Legendre Q Neumann integral is
  already proved in [Legendre/Neumann.lean](DLMF/Legendre/Neumann.lean).
- **Admitted — Mehler's formula**, (5.3.17), p. 106:
  `mehler_formula` in
  [Series.lean](DLMF/OrthogonalPolynomials/Series.lean).
- **Admitted — the Jacobi Darboux formula**, (5.5.12), p. 114, also
  derived in §13.3: `jacobi_darboux_asymptotic` in `BoundsZeros.lean`.
  This existing statement is at fixed real angle; the book also discusses
  more general matching and approximation statements in Chapters 7 and 13.

Hermite fixed-argument asymptotics, (5.3.20), and Fejér's Laguerre formula,
(5.4.12), are already covered by
[HermiteFixedX.lean](DLMF/OrthogonalPolynomials/HermiteFixedX.lean) and
[LargeASharp.lean](DLMF/Confluent/LargeASharp.lean).

## Chapter 6 Semi classical orthogonal polynomials

[Hahn.lean](DLMF/OrthogonalPolynomials/Hahn.lean),
[Wilson.lean](DLMF/OrthogonalPolynomials/Wilson.lean), and
[Limits.lean](DLMF/OrthogonalPolynomials/Limits.lean) already represent the
families and much of the algebra in this chapter. The recently proved
Charlier, Krawtchouk, Meixner, and Hahn orthogonality must be retained in
the coverage assessment.

- **Absent — the general classification of discrete polynomial
  eigenfunctions**, §6.1, especially Theorem 6.1.3, pp. 141–146. Missing is
  the converse theorem identifying the four discrete classical families
  from symmetry and the second-order difference-operator hypotheses.
- **Present / partial — discrete Rodrigues theory**, §6.2, pp. 146–149.
  [DiscreteRodrigues.lean](DLMF/OrthogonalPolynomials/DiscreteRodrigues.lean)
  proves Charlier, Meixner, and Krawtchouk formulas, with their shifted
  weights identified by Pochhammer factors. Meixner allows `Re β > 0`
  and nonzero complex `c`; the more general finite nonvanishing form also
  yields Krawtchouk for `n ≤ N` and `p ≠ 0, 1`. The order-zero Krawtchouk
  weight is identified with the binomial weight.
  [HahnRodrigues.lean](DLMF/OrthogonalPolynomials/HahnRodrigues.lean) proves
  Hahn's formula and shifted-weight identity for `n ≤ N` and
  `Re α, Re β > -1`. All formulas hold for every integer argument with
  zero extension outside the support, retaining the endpoint terms.
  Hahn's alternative real regime `α, β < -N` and an abstract shifted-weight
  theorem with its general norm computation are not included.
- **Partial — generating functions beyond discrete support arguments**,
  §§6.3–6.5. `charlier_generating_function` and
  `meixner_generating_function` already prove (6.3.6) and (6.5.7) for
  natural-number argument, and `krawtchouk_generating_function` proves
  the finite generating identity on its discrete support. The book also
  treats the polynomial variable more generally. Extending these
  identities requires the appropriate convergence domains and branches.
- **Present — discrete addition formulas**, (6.3.10)–(6.3.11), (6.4.12),
  and (6.5.11), for Charlier, Krawtchouk, and Meixner, now proved in
  [DiscreteAddition.lean](DLMF/OrthogonalPolynomials/DiscreteAddition.lean).
  The four identities use the existing normalizations and complex
  polynomial arguments. The Krawtchouk formula assumes `n ≤ N`; Meixner
  assumes `0 < Re β`. Formal power series supply the coefficient algebra
  without asserting a larger analytic generating-function domain.
- **Absent — discrete large-degree asymptotics and limiting zero behavior**,
  §§6.3–6.6, including the Charlier and Meixner formulas placing zeros
  near integers, and the Krawtchouk/Hahn formulas discussed there. Existing
  fixed-degree parameter limits in the Askey scheme are different limits.
- **Admitted — parts of the neoclassical orthogonality theory**, §6.7,
  pp. 162–168. `continuousHahn_orthogonal` and
  `meixnerPollaczek_orthogonality` in `Hahn.lean`, and the continuous dual
  Hahn/Wilson orthogonality statements in `Wilson.lean`, need proofs.
  The functions, many difference equations, and transformations already exist.

## Chapter 7 Two methods for orthogonal polynomial asymptotics

This is one of the largest substantive gaps. Fixed-argument Hermite and
Laguerre estimates do not cover the rescaled arguments used here.

- **Absent — asymptotics off the interval of zeros**, §7.1,
  Theorems 7.1.1–7.1.3, pp. 173–175. Missing are the complex off-support
  approximations for the rescaled Hermite and Laguerre polynomials and
  monic Jacobi polynomials, with their specified branches and error terms.
- **Partial — matching from recurrence relations and bulk asymptotics**,
  §7.2, Theorems 7.2.1–7.2.3, pp. 175–178. The Jacobi oscillation has a
  related admitted real-angle statement. The book's complex-neighborhood
  matching framework and the Laguerre `L_n(4nx)` and Hermite
  `H_n(√(2n+1)x)` bulk regimes are missing.
- **Absent — the matrix Riemann–Hilbert formulation of orthogonal
  polynomials**, §7.3, pp. 178–179: the polynomial/Cauchy-transform matrix,
  its triangular jump, normalization at infinity, and characterization.
- **Absent — the Hermite Riemann–Hilbert asymptotic analysis**, §§7.4–7.6,
  pp. 179–196. Missing are the successive matrix transformations, contour
  deformation, model solutions and error analysis, and Theorem 7.6.1's
  rescaled Hermite expansion. No matching framework was located upstream.

## Chapter 8 Confluent hypergeometric functions

This chapter has broad existing coverage in
[DLMF/Confluent](DLMF/Confluent.lean): Kummer and Tricomi functions,
integer-parameter continuation, contiguous relations, special cases,
Whittaker functions, and parabolic cylinder functions. Integer denominator
parameters should not be listed as entirely unsupported: the continuation
and logarithmic-series machinery already exists.

- **Partial — completion of the book's parameter-asymptotic range**,
  §§8.1–8.2, pp. 201–207, and §13.2. `LargeA.lean` and `LargeASharp.lean`
  cover large negative real `a` for regularized M with all real `c`, and
  U for noninteger real `c`, at fixed positive real argument. The U
  asymptotic at integer `c` still needs a corresponding theorem; one cannot
  remove that exclusion merely by citing continuity at each fixed parameter.
- **Partial — remaining parabolic-cylinder results**, §8.6,
  pp. 212–216, and §13.1. The U/V definitions, initial values, Wronskians,
  recurrences, Hermite specialization, and the large-positive-argument U
  expansion are present in
  [ParabolicCylinder.lean](DLMF/Confluent/ParabolicCylinder.lean).
  The complementary V large-argument asymptotic and the general
  noninteger-degree parameter-asymptotic treatment go beyond the current
  explicit results. The fixed-integer-degree Hermite estimates are present.

## Chapter 9 Cylinder and Airy functions

Mathlib provides `Complex.besselJ`. The project provides the other cylinder
functions, recurrences, Wronskians, many integrals, fixed-order asymptotics,
some large-order limits, and extensive zero theory. In particular,
infinitely many cylinder zeros, spacing relative to π, J/J-successor
interlacing, and reality of J zeros are already represented in
[SturmZeros.lean](DLMF/Bessel/SturmZeros.lean).

- **Partial — the derivative-zero part of Theorem 9.2.5**, p. 231.
  Reality of J zeros for real order `ν > -1` is present; the corresponding
  book theorem about zeros of J prime needs its own result: reality for
  `ν ≥ 0`, and the pair of imaginary zeros when `-1 < ν < 0`.
  First-positive-zero monotonicity is
  already in [Zeros.lean](DLMF/Bessel/Zeros.lean).
- **Absent — Graf's general addition theorem**, (9.6.3), p. 241.
  The proved `hasSum_besselJ_add` is Neumann's addition theorem for an
  additive argument; it does not supply Graf's arbitrary-order geometric
  addition formula with its phases and convergence domain.
- **Proved — Gegenbauer's Bessel addition theorem**, (9.6.4), p. 241:
  `besselJ_addition` in [BesselAddition.lean](DLMF/SphericalHarmonics/BesselAddition.lean) (moved from DLMF/Bessel/Theorems.lean on 2026-10-22; proved).
- **Absent — the Hankel transform and its inversion**, §9.7,
  pp. 241–243. Missing are the Bessel-kernel transform, its identification
  with a Fourier angular mode in polar coordinates, and its involution
  theorem under precise integrability/continuity assumptions. Fourier
  inversion itself is upstream. Finite Fourier–Bessel coefficient
  identities in [Lommel.lean](DLMF/Bessel/Lommel.lean) are already covered,
  but are not Hankel inversion.
- **Present — direct Bessel integral-transform interfaces**, §9.8,
  pp. 243–245.
  [IntegralTransforms.lean](DLMF/Bessel/IntegralTransforms.lean) proves
  the general Gaussian-weight integral (9.8.3) with complex scale `s`
  satisfying `Re s > 0`, positive real frequency, complex powers/orders,
  and `Re(μ + ν) > 0`. Both regularized and ordinary Kummer forms are
  supplied; the regularized form retains exceptional orders.
  [LaplaceTransform.lean](DLMF/Bessel/LaplaceTransform.lean) proves the
  conventional quadratic Gauss form of the Laplace–Bessel integral,
  with argument `-w²/s²`, throughout `Re s > 0`. Its regularized version
  retains every complex order under the stated sufficient condition
  `Re(μ + ν) > 0`, and absolute convergence is proved separately.
  The proof uses Kummer's Laplace theorem, quadratic transformation and
  continuation in `s`, then regularized contiguous relations to lower
  the denominator without dividing by singular Gamma factors. The earlier
  Kummer representation remains available with its explicit exclusions.
  Sonine's single-Bessel Gaussian integral, Poisson integrals, and Lommel
  orthogonality also have local proofs.
- **Partial — Airy integral and asymptotic theory**, §9.9,
  pp. 245–248. [DLMF/Airy](DLMF/Airy.lean) already defines Ai and Bi,
  proves their ODE and initial values, Wronskian, rotation identities,
  Bessel relations on the real axis, positivity, and leading positive-axis
  asymptotics. Missing book targets are the improper oscillatory and
  contour representations (9.9.8)–(9.9.10), and the fuller asymptotic
  expansion following (9.9.13). The oscillatory integral must use an
  appropriate improper-limit formulation rather than silently interpreting
  a non-absolutely-integrable function as a Bochner integral.

## Chapter 10 Hypergeometric functions

Most of the named topics already have extensive local statements and proofs:
fundamental solutions, linear relations, integer-parameter logarithmic
solutions, contiguous identities, quadratic transformations, integrals,
and special values. In particular,
[Solutions.lean](DLMF/Hypergeometric/Solutions.lean),
[ConnectionFormulas.lean](DLMF/Hypergeometric/ConnectionFormulas.lean), and
[ArgumentContinuation.lean](DLMF/Hypergeometric/ArgumentContinuation.lean)
cover much more than just the defining series.

- **Partial — full branch and contour scope of the book's solution theory**,
  §§10.1–10.3 and §10.6, pp. 255–273. Several solution and connection
  theorems are formulated on overlapping convergence disks or a chosen cut
  plane. A complete theory transporting bases and their branch phases
  around the singularities is not present. The main new infrastructure
  would be continuation along paths and monodromy, rather than another
  definition of `₂F₁`.

This chapter is a smaller acquisition opportunity than Chapters 4, 7, 12,
14, or 15. Any further formula acquisition should compare exact parameter
exceptions and branches with the existing statements first. In particular,
an old coverage file's “continuation missing” note is not evidence that
the current project lacks cut-plane continuation.

## Chapter 11 Spherical functions

[SphericalHarmonics](DLMF/SphericalHarmonics.lean) and
[Legendre](DLMF/Legendre.lean) provide a starting point, but do not yet give
the full chapter.

- **Partial — harmonic-polynomial decomposition and spherical harmonic
  bases**, §11.1, pp. 280–286. The project defines harmonic homogeneous
  polynomials and a numerical dimension expression. It does not establish
  the full dimension/decomposition theorem, construct the book's normalized
  basis `Y_n^m`, or prove its completeness on the sphere, Theorems
  11.1.2–11.1.3. A numerical formula definition is not the dimension theorem.
  Generic upstream harmonic-function tools do not supply this basis.
- **Admitted — orthogonality and addition results already stated**:
  `harmonicHomogeneous_orthogonal` in
  [Basic.lean](DLMF/SphericalHarmonics/Basic.lean), and `spherical_addition`
  in [Theorems.lean](DLMF/SphericalHarmonics/Theorems.lean), have admissions.
  The existing `legendre_addition` in `OrthogonalPolynomials/Series.lean`
  is admitted as well. These are proof tasks rather than absent statements.
- **Partial — associated Legendre functions and their relations**,
  §§11.3–11.6, pp. 289–301. General P/Q of degree ν, several recurrences,
  integer-degree Q, the Neumann integral, and Ferrers P are present.
  General associated second-kind functions, a full associated P/Q basis
  with branch-dependent connections, and the corresponding integral
  representations are missing. Polynomial associated Legendre results
  do not cover arbitrary complex degree and order.
- **Absent — Legendre asymptotic formulas**, §11.4 and §13.4,
  pp. 293–296 and 340–342. In particular, the Hobson–Darboux–Laplace
  large-degree associated P/Q estimates (13.4.4)–(13.4.5) were not found
  as local theorems. The existing Laplace integral is a prerequisite.

## Chapter 12 Generalized hypergeometric and Meijer G functions

Mathlib already defines generalized regularized hypergeometric series, and
[Generalized.lean](DLMF/Hypergeometric/Generalized.lean),
[GeneralizedCalculus.lean](DLMF/Hypergeometric/GeneralizedCalculus.lean), and
[GeneralizedIntegral.lean](DLMF/Hypergeometric/GeneralizedIntegral.lean)
provide local ODE, differentiation, coefficient-uniqueness, and integral
results. Thus generalized hypergeometric functions themselves are present.

- **Absent — classification of operators by two-term coefficient
  recursion**, §12.2, pp. 308–310. Missing is the converse leading from
  a general differential operator to `Q(θ) - x P(θ)`, and then to the
  generalized hypergeometric operator. The local coefficient-uniqueness
  theorem starts with an already specified hypergeometric operator.
- **Absent — general fundamental bases and connection theory for
  generalized equations**, Propositions 12.2.1–12.2.2 and Theorems
  12.2.3–12.2.4, pp. 310–312. This includes shifted-parameter bases at
  zero and infinity, independence under nonresonance conditions, and the
  higher-order connection/asymptotic statements. The extensive `₂F₁`
  solution API does not prove these for arbitrary order.
- **Absent — Meijer G definitions and elementary calculus**, §12.3,
  pp. 312–319. Missing are `G_{p,q}^{m,n}`, its Mellin–Barnes kernel,
  parameter conventions, ODE, shifts and inversion symmetries, and
  identifications of classical functions as G-functions.
- **Absent — G-function integral transforms and convolution rules**,
  especially Theorem 12.3.3, pp. 317–319. The book's calculus for
  integrals of products of G-functions has no corresponding API.
- **Absent — admissible G contours and convergence theory**, §12.4,
  pp. 319–322: pole separation, vertical and loop contours, parameter
  inequalities, and independence of allowed contour choices.
- **Absent — G-function residue expansions and asymptotics**, §12.5,
  Theorems 12.5.1–12.5.3, pp. 322–325.
- **Absent — the Mellin transform of a G-function**, §12.6,
  Theorem 12.6.1, pp. 325–326. **Mellin transformation and inversion
  themselves are present** in Mathlib's
  [MellinTransform.lean](.lake/packages/mathlib/Mathlib/Analysis/MellinTransform.lean)
  and [MellinInversion.lean](.lake/packages/mathlib/Mathlib/Analysis/MellinInversion.lean).
  Local Barnes-integral results are further useful prerequisites, but do
  not amount to a general G-function development.

## Chapter 13 Asymptotic methods

This chapter overlaps several entries above. It should not be counted as
an additional independent collection of missing theorems in every case.

- **Present in substantial part — oscillator/Volterra estimates**,
  §13.1, and their Hermite application, through `Volterra.lean` and
  `HermiteFixedX.lean`.
- **Present in substantial part — negative-parameter Kummer/Bessel
  approximation with rates**, §13.2, including (13.2.8), through
  `LargeA.lean` and `LargeASharp.lean`. The integer-c U extension remains
  the specific omission recorded under Chapter 8.
- **Partial or admitted — hypergeometric and Jacobi approximations**,
  §13.3, pp. 338–340. The fixed-angle Jacobi Darboux result is admitted;
  the more general perturbed-Bessel approximation and its uniform
  estimates require additional statements and proofs.
- **Absent — the Legendre applications**, §13.4, as recorded under
  Chapter 11. The project's general
  [Laplace.lean](ToMathlib/Analysis/Integral/Laplace.lean) and Watson
  lemmas already provide asymptotic integration tools.
- **Absent — a reusable complex steepest-descent and real stationary-phase
  theorem**, §13.5, pp. 342–345. The book illustrates contour deformation
  with Laguerre polynomials and gives the stationary-phase leading term
  at a nondegenerate critical point. Existing real Laplace asymptotics,
  sectorial Watson theory, and Gaussian/Fresnel evaluations are useful
  ingredients, but do not supply these general oscillatory theorems.

## Chapter 14 Elliptic functions

The real theory is substantial:
[Complete.lean](DLMF/Elliptic/Complete.lean),
[AGM.lean](DLMF/Elliptic/AGM.lean),
[Jacobi.lean](DLMF/Elliptic/Jacobi.lean),
[JacobiIdentities.lean](DLMF/Elliptic/JacobiIdentities.lean), and
[ThirdKind.lean](DLMF/Elliptic/ThirdKind.lean) include real elliptic
integrals, the AGM relation, Landen transformations, real Jacobi functions,
derivatives, addition, and real periods. The missing part is primarily
complex function theory and its connections.

- **Absent — general elliptic-function structure and reduction of elliptic
  integrals**, §§14.1–14.2, pp. 359–366. Missing are the book's general
  reductions for rational/algebraic integrands and the structural
  zero/pole/residue arguments on a period parallelogram. Existing real
  special integral evaluations are narrower.
- **Partial — complex Jacobi functions**, §14.3, pp. 366–371. Missing are
  complex meromorphic sn/cn/dn, their imaginary periods, poles and
  residues, and imaginary/complementary-modulus transformations. The
  project definitions are explicitly `Real.jacobiSnm`, `Real.jacobiCnm`,
  and `Real.jacobiDnm`; real addition and periodicity are already covered.
- **Partial — theta construction and representation of elliptic functions**,
  §§14.4–14.5, pp. 371–380. Theta series and some transformations are
  upstream, the local four-theta wrappers are present, and the Jacobi
  triple product is proved in
  [QSeries/Identities.lean](DLMF/QSeries/Identities.lean). Missing targets
  include the full zero/divisor characterization on a fundamental
  parallelogram, general representation by theta quotients, and the
  sn/cn/dn theta-quotient identities with the corresponding complex
  periods. The theta heat equation and Jacobi's Z-function/integration
  formulas are further book statements not located in the checked APIs.
  `ThetaAGM.lean` already relates K to a theta null value on the real-q
  domain; that relation is not wholly absent.
- **Partial — Weierstrass theory**, §14.6, pp. 380–383. Mathlib's
  [Weierstrass.lean](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.lean)
  already supplies a period lattice, ℘ and its derivative, parity,
  periodicity, meromorphicity, pole order, invariants, and
  `derivWeierstrassP_sq`, the equation `(℘')² = 4℘³ - g₂℘ - g₃`.
  Missing book targets are the two-argument ℘ addition theorem,
  Weierstrass ζ and σ, their quasi-periods and
  integration formulas, representation of elliptic functions by ℘/℘′
  or ζ/σ, and the corresponding links to Jacobi/theta functions.

## Chapter 15 Painlevé transcendents

**Partial, with a proved local and explicit-solution development.**
[DLMF/Painleve.lean](DLMF/Painleve.lean) now imports eight modules in the
book's convention `u'' = 2u³ + xu - c`. No matching nonlinear-equation
development was located in Mathlib or pinned TauCeti. TauCeti's theorems
named “Painlevé removability” concern complex-analysis gluing.

The book concentrates on Painlevé II. The following parts are implemented:

- Local real existence for arbitrary initial value and first derivative,
  and uniqueness of solution germs, using Mathlib's ODE theory.
- Conditional pole analysis from §15.3: a meromorphic solution's poles are
  simple, with residue `+1` or `-1`. Meromorphicity at the point is assumed.
- Rational solutions for every integer parameter: the existence direction
  of Theorem 15.3.1. An explicit polynomial-pair recurrence has a proved
  nonzero denominator at every step and solves PII on that denominator's
  full regular set. Its first two nonzero members match page 407.
- The Bäcklund reflection, its involution property, the shifts `c → c ± 1`,
  and their inverse identities on open sets where the denominators do not
  vanish, §15.4.
- The Riccati/Airy seed at `c = 1/2` and an explicit rational jet recurrence
  for every half-integer parameter, Proposition 15.4.6. The functions are
  meromorphic on the plane; each has a proved nonempty open solution
  domain. The scale satisfies `k³ = -1/2`, correcting the printed
  substitution on page 407, which does not solve the scaled Airy equation.
- The Lax matrix compatibility identity, its equivalence to PII at nonzero
  spectral parameter, and the actual matrix derivative along a solution.
  Trace and spectral-reflection identities are included.
- The energy derivative and the converse from the two quotient equations
  (15.3.10)–(15.3.11) to PII off the denominator's zeros.

The remaining book targets include:

- The general Painlevé method and derivation of PII from singularity
  constraints, §§15.1–15.2, pp. 392–399.
- Complex analytic local existence, the convergent Laurent family with
  its free coefficient, the necessity and uniqueness directions of the
  rational classification, and the rational pole counts, §15.3,
  pp. 399–402. No arbitrary-solution entire tau-pair existence is claimed.
- Construction of sectorial fundamental solutions, Stokes/monodromy data,
  and isomonodromy, §§15.5–15.6, pp. 408–415.
- The inverse problem and meromorphic continuation/Painlevé-property
  proof for PII, §15.7, pp. 415–419.
- The real PII(0) Airy boundary conditions and oscillatory asymptotics,
  together with the connection constants in Theorems 15.8.1–15.8.2,
  §15.8, pp. 419–424.

The explicit meromorphic families and conditional pole restrictions do not
establish global meromorphic continuation for arbitrary initial data or
the real connection formulas.

## Appendices

Most of Appendices A and B is foundational material already available:
holomorphic/meromorphic functions, Cauchy theory, residues, Fourier
transformation and inversion, Riemann–Lebesgue, approximation, and Mellin
transformation/inversion. Two additional targets stand out.

- **Absent — the prescribed-zero entire-function existence theorem used
  from Weierstrass factorization**, Appendix A.5, p. 434, and its
  consequence that a plane-meromorphic function is a quotient of entire
  functions. No matching global theorem was located. Mathlib's
  `CanonicalDecomposition.lean` treats finite decompositions on compact
  sets/disks, which is a different result.
- **Absent — the Sokhotski–Plemelj boundary formula for Cauchy/Stieltjes
  transforms**, Appendix A.6, pp. 435–436. The resolvent transform and
  TauCeti's holomorphic Stieltjes extension provide related theory, but
  the book's two boundary values and jump relation were not located.
  This is a prerequisite for the Chapter 4 and Chapter 7 developments.

Appendix B.2's polynomial-completeness argument is substantially covered by
TauCeti's polynomial completeness API and the local classical instances.
Appendix B.5 should not lead to duplicate Mellin inversion infrastructure.

## Suggested order of work

The project targets special functions themselves. General theory in this
inventory is background or a potential prerequisite: develop it only when
a chosen special-function identity, estimate, or construction needs it.
In particular, the general moment problem, operator classification, and
Riemann–Hilbert framework are not independent project objectives.

The implementation batches have tested the initial readiness assessment
with completed Lean proofs. Remaining targets are stated explicitly below.

1. **Implemented:** the four Charlier, Krawtchouk, and Meixner addition
   identities; all four classical discrete Rodrigues formulas in the
   parameter ranges above; strict indexed Hermite bounds; and the indexed
   Jacobi angle bounds with their strict refinement. These use existing
   terminating sums, polynomial representations, difference equations,
   sorted roots, ODEs, and Sturm comparison. Analytic generating functions
   at general complex arguments still need convergence and branch work
   beyond the current discrete-support statements.
2. **Implemented:** Gaussian-weight Bessel integrals for every complex
   scale of positive real part, and the conventional continued-Gauss
   Laplace–Bessel formula throughout `Re s > 0`, with no order exclusions
   in the regularized forms. The absolute-convergence and parameter
   conditions are recorded above.
3. **Feasible with additional local analytic lemmas:** Wielandt's Gamma
   characterization. Gamma recurrence, bounds, holomorphy, removable
   singularities, and Liouville-type tools exist. The bounded-strip
   argument and any holomorphic extension used in the proof still need
   to be formalized. This is a specific Gamma theorem, not an immediate
   application of an existing uniqueness theorem.
4. **Require more analytic preparation:** the Airy oscillatory/contour
   integrals and Graf's arbitrary-order addition theorem. Airy/Bessel
   definitions and many identities are available, but the needed
   convergence, tail estimates, contour arguments, and branch-dependent
   summation bounds are not packaged for these results. Integer-order
   Graf addition has a nearer route through the existing Bessel Fourier
   integral and generating function. These targets should not all be
   described as equally small.
5. **Larger special-function follow-ups:** Hankel inversion; Mehler and
   Jacobi Darboux; continuous Hahn, Meixner–Pollaczek, Wilson, and
   continuous dual Hahn orthogonality; Meijer G-functions; complex
   Jacobi/Weierstrass ζ/σ; and the remaining Painlevé II classification,
   continuation, and connection theorems. Choose a concrete theorem or
   function family first and add only its required supporting machinery.
   Hankel inversion in particular needs the weighted integrability and
   polar Fourier-transform correspondence, even though Fourier inversion
   itself is already available.

## Review validation

The PDF contents, chapter passages and named results were compared with
current Lean declarations, not just filenames or old coverage summaries.
The searches explicitly distinguished Stieltjes transforms from
Fourier–Stieltjes transforms, Painlevé equations from removability, Mellin
inversion from G-functions, finite Fourier–Bessel formulas from Hankel
inversion, and real Jacobi functions from complex elliptic functions.

The initial inventory was a documentation-only review. The first
implementation added five Lean modules, imported them through the two area
umbrellas, and generalized a Meixner coefficient lemma without changing its
existing public wrapper. It introduced eleven main proved results and no
admissions. Dependency pins, build configuration, branches, and existing
theorem assumptions were preserved.

Validation: `lake build` succeeded (4271 jobs); direct `lake env lean` checks
were run for every changed Lean file and `Main.lean`. The axiom audit of
the eleven main results and both Meixner coefficient lemmas reports only
`propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
Whitespace and relative documentation links were checked. The existing
continuous Hahn, Meixner–Pollaczek, and generating-function admissions in
`Hahn.lean` remain; no proof of those is claimed here.

The refinement batch adds `HahnRodrigues.lean` and `LaplaceTransform.lean`,
completes the strict Jacobi bounds, the Meixner/Krawtchouk/Hahn Rodrigues
formulas, complex Gaussian scales, and the conventional Laplace–Bessel
formula without exceptional-order exclusions. All earlier public statements
are preserved. The existing Kummer argument-domain lemma was exposed for
reuse, with its proof unchanged. See [REVIEW.md](REVIEW.md) for the final
build, direct-file checks, and twenty-declaration axiom audit.

The Painlevé batch adds eight modules and their umbrella. Chapter 15 above
separates the proved local, Bäcklund, rational, Airy, pole, Lax, and quotient
results from the remaining classification and global theory. Its validation
and the page 407 scaling correction are recorded in [REVIEW.md](REVIEW.md).
